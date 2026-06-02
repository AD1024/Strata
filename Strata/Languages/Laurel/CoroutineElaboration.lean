module

public import Strata.Languages.Laurel.Resolution
import Strata.Util.Tactics

public section

namespace Strata.Laurel

/-- Collect every `var name: T` declaration in `expr` as a `Parameter`.
    Each `.Declare` already carries a full `Parameter`, so the type is
    available with no separate lookup. Disjoint-scope shadowing
    produces multiple `Parameter`s with the same `text` but distinct
    `uniqueId`s — the caller relies on `uniqueId` for keying. -/
private def collectVarDeclsExpr (expr : StmtExprMd) : List Parameter :=
  match _h : expr.val with
  -- Bare declaration `var x: T` (no initializer).
  | .Var (.Declare param) => [param]
  -- Initialized declaration `var x: T := e` parses to an `Assign` whose
  -- target is a `.Declare`. Harvest that target *and* recurse into the
  -- RHS (which may itself contain declarations, e.g. block expressions).
  | .Assign targets value =>
    let declared := targets.filterMap fun t =>
      match t.val with
      | .Declare param => some param
      | _ => none
    declared ++ collectVarDeclsExpr value
  | .Block stmts _ =>
    stmts.attach.flatMap (fun ⟨s, _⟩ => collectVarDeclsExpr s)
  | .IfThenElse c t e =>
    collectVarDeclsExpr c ++ collectVarDeclsExpr t
      ++ (match e with | some eb => collectVarDeclsExpr eb | none => [])
  | .While c _ _ body => collectVarDeclsExpr c ++ collectVarDeclsExpr body
  | _ => []
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try term_by_mem)
  all_goals (cases expr; simp_all; omega)

/-- Collect every local `var` declaration in a coroutine's body. Empty list
    for non-coroutine procedures and for bodyless / external procedures. -/
def collectVarDecl (p : Procedure) : List Parameter :=
  if p.kind == .Regular then [] else
  match p.body with
  | .Opaque _ (some impl) _ => collectVarDeclsExpr impl
  | _ => []  -- abstract / external: nothing to walk

/-- A `FieldNaming` maps each promoted local's resolved `uniqueId` to the
    `Identifier` used for its generated field. Built once per coroutine so
    the field *declaration* (in `coroutineToComposite`) and every field
    *access* (in `rewriteStmtExpr`) agree on the name by construction.

    Two design goals collide here, and `FieldNaming` reconciles them:

      * **Resolution requires distinct `text`.** Composite fields are
        registered by `composite.fieldText` (see `resolveTypeDefinition`),
        so two promoted locals that share a `text` (legal under Laurel's
        scope-based shadowing — `var x` in disjoint `if`/`else` branches)
        would collide and the re-`resolve` after this pass would emit a
        spurious "duplicate field" error.

      * **Diagnostics should show the user's name.** We therefore mangle
        *only on collision*: a name unique within the coroutine keeps its
        `text` verbatim, so the overwhelmingly common case produces clean
        field names and clean error messages. Genuinely-shadowed names get
        a `$<uniqueId>` suffix. -/
abbrev FieldNaming := Std.HashMap Nat Identifier

/-- Compute the field-naming map for a coroutine. Collects every promoted
    parameter (inputs, body locals, `yields`), then for each distinct
    `uniqueId` picks a field name: the verbatim `text` if that `text` is
    unique across the promoted set, else `text$uniqueId`.

    `resumes` bindings are deliberately *not* promoted: the resumed value
    is a per-call argument, lowered to a parameter of the generated
    `resume` procedure (see `populateCoroutineComposite`), not coroutine
    state. So a `resumes (y: U)` binding never becomes a `self#` field. -/
private def fieldNaming (proc : Procedure) : FieldNaming :=
  let promoted : List Parameter :=
    proc.inputs ++ collectVarDecl proc ++ proc.yields
  -- First pass: count how many promoted params share each `text`.
  let textCounts : Std.HashMap String Nat :=
    promoted.foldl (fun m p =>
      m.insert p.name.text ((m.getD p.name.text 0) + 1)) ∅
  -- Second pass: assign a collision-safe field `Identifier` per uniqueId.
  promoted.foldl (fun m p =>
    match p.name.uniqueId with
    | none => m  -- unresolved; skip (defensive — shouldn't happen post-resolve)
    | some uid =>
      let collides := (textCounts.getD p.name.text 0) > 1
      let fieldText := if collides then s!"{p.name.text}${uid}" else p.name.text
      -- Preserve the source location on the field-name identifier so
      -- diagnostics that surface the field still point at the original
      -- declaration site.
      m.insert uid { p.name with text := fieldText }) ∅

/-- Build a mutable `Field` from a parameter, using the collision-safe name
    chosen by `fieldNaming`. Falls back to the verbatim name if (defensively)
    the parameter is missing from the map. -/
private def paramToField (naming : FieldNaming) (p : Parameter) : Field :=
  let fieldName :=
    match p.name.uniqueId with
    | some uid => naming.getD uid p.name
    | none => p.name
  { name := fieldName, isMutable := true, type := p.type }

/-- Build the state-machine composite for a coroutine.

    Layout (every field mutable so `moveNext` can write):
      `var $pc: int`                  — state index (0 = entry)
      `var <input>: <T>`              — one per `proc.inputs`
      `var <local>: <T>`              — one per body-collected local
      `var <yield>: <T>`              — one per `proc.yields`

    `resumes` bindings are *not* fields: the resumed value is a per-call
    argument threaded as a parameter of the generated `resume` procedure,
    not coroutine state.

    Heap-snapshot bookkeeping is *not* a field here either. The Stage-3
    rely/guarantee VC introduces per-segment snapshots locally
    against the heap value threaded by `HeapParameterization`.

    The composite is named `<proc>State` (e.g. `producer` ⇒
    `producerState`). Promoted-local field names come from `fieldNaming`,
    which mangles only on genuine `text` collision (Laurel allows
    scope-based shadowing), so the common no-shadowing case keeps the
    user's names verbatim for readable diagnostics. The control field is
    `$pc` — `$`-prefixed so it can never collide with a user local. -/
private def coroutineToComposite (naming : FieldNaming) (proc : Procedure) : CompositeType :=
  let pcField : Field :=
    { name := "$pc", isMutable := true, type := { val := .TInt, source := none } }
  let inputFields  := proc.inputs.map (paramToField naming)
  let localFields  := (collectVarDecl proc).map (paramToField naming)
  let yieldFields  := proc.yields.map  (paramToField naming)
  { name := { proc.name with text := proc.name.text ++ "State" },
    extending := [],
    fields := pcField :: inputFields ++ localFields ++ yieldFields,
    instanceProcedures := [] }

/-- Build a `self#name` field-read expression, inheriting `src` from the
    original local-reference node so a failed obligation still points at
    the user's source. -/
private def selfFieldRead (fieldName : Identifier) (src : Option FileRange) : StmtExprMd :=
  let selfNode : StmtExprMd := { val := .This, source := src }
  { val := .Var (.Field selfNode fieldName), source := src }

/-- Build a `self#name` field-write target, inheriting `src` from the
    original assignment-target node. -/
private def selfFieldTarget (fieldName : Identifier) (src : Option FileRange) : AstNode Variable :=
  let selfNode : StmtExprMd := { val := .This, source := src }
  { val := .Field selfNode fieldName, source := src }

/-- Resolve a referenced `Identifier` to its generated field name, or
    `none` if it is not a promoted local. The returned identifier carries
    the *field* name (collision-mangled where needed); callers attach the
    *reference site's* source location, not the declaration's. -/
private def promotedFieldName (naming : FieldNaming) (id : Identifier) : Option Identifier :=
  match id.uniqueId with
  | some uid => naming[uid]?
  | none => none

/-- Rewrite a single statement-or-expression: every reference to a
    promoted name becomes `self#name`. Standalone bare `var` declarations
    (no initializer) are returned unchanged here; the `Block` walker
    is responsible for dropping them. -/
private def rewriteStmtExpr (naming : FieldNaming) (expr : StmtExprMd) : StmtExprMd :=
  let src := expr.source
  match _h : expr.val with
  -- Reads of a promoted local become field reads of self. The rewritten
  -- access inherits `src` (the *reference site*), so a failed obligation
  -- localizes to where the user read the variable, not where it was
  -- declared.
  | .Var (.Local id) =>
    match promotedFieldName naming id with
    | some fieldName => selfFieldRead fieldName src
    | none => expr
  -- Standalone bare `var name: T` declaration: leave for the Block
  -- walker to drop. Returning unchanged is safe — the result of
  -- `rewriteStmtExpr` on this case is only ever consumed by Block.
  | .Var (.Declare _) => expr
  -- Assignment is the interesting case: `var x: T := e` rewrites to
  -- `self#x := rewrite(e)`; `x := e` (where `x` is promoted) likewise.
  | .Assign targets value =>
    let value' := rewriteStmtExpr naming value
    let targets' := targets.attach.map fun ⟨t, _⟩ =>
      let ⟨tv, ts⟩ := t
      match tv with
      | .Local id =>
        match promotedFieldName naming id with
        | some fieldName => selfFieldTarget fieldName ts
        | none => t
      | .Declare ⟨name, _⟩ =>
        match promotedFieldName naming name with
        | some fieldName => selfFieldTarget fieldName ts
        | none => t
      | .Field target field =>
        { val := .Field (rewriteStmtExpr naming target) field, source := ts }
    { val := .Assign targets' value', source := src }
  -- Structural: recurse into each child.
  | .Block stmts label =>
    -- Drop bare `var name: T` standalone statements (no initializer);
    -- the field already exists on the composite. Other statements
    -- recurse via `rewriteStmtExpr`.
    let stmts' := stmts.attach.filterMap fun ⟨s, _⟩ =>
      match s.val with
      | .Var (.Declare _) => none
      | _ => some (rewriteStmtExpr naming s)
    { val := .Block stmts' label, source := src }
  | .IfThenElse cond t e =>
    { val := .IfThenElse (rewriteStmtExpr naming cond) (rewriteStmtExpr naming t)
        (e.attach.map fun ⟨eb, _⟩ => rewriteStmtExpr naming eb), source := src }
  | .While cond invs dec body =>
    { val := .While
        (rewriteStmtExpr naming cond)
        (invs.attach.map fun ⟨i, _⟩ => rewriteStmtExpr naming i)
        (dec.attach.map fun ⟨d, _⟩ => rewriteStmtExpr naming d)
        (rewriteStmtExpr naming body),
      source := src }
  | .Return v =>
    { val := .Return (v.attach.map fun ⟨e, _⟩ => rewriteStmtExpr naming e),
      source := src }
  | .Resume target v =>
    { val := .Resume (rewriteStmtExpr naming target)
        (v.attach.map fun ⟨e, _⟩ => rewriteStmtExpr naming e),
      source := src }
  | .PureFieldUpdate target field newValue =>
    { val := .PureFieldUpdate (rewriteStmtExpr naming target) field
        (rewriteStmtExpr naming newValue), source := src }
  | .StaticCall callee args =>
    { val := .StaticCall callee
        (args.attach.map fun ⟨a, _⟩ => rewriteStmtExpr naming a),
      source := src }
  | .PrimitiveOp op args =>
    { val := .PrimitiveOp op
        (args.attach.map fun ⟨a, _⟩ => rewriteStmtExpr naming a),
      source := src }
  | .ReferenceEquals lhs rhs =>
    { val := .ReferenceEquals (rewriteStmtExpr naming lhs) (rewriteStmtExpr naming rhs),
      source := src }
  | .AsType t ty =>
    { val := .AsType (rewriteStmtExpr naming t) ty, source := src }
  | .IsType t ty =>
    { val := .IsType (rewriteStmtExpr naming t) ty, source := src }
  | .InstanceCall target callee args =>
    { val := .InstanceCall (rewriteStmtExpr naming target) callee
        (args.attach.map fun ⟨a, _⟩ => rewriteStmtExpr naming a),
      source := src }
  | .Quantifier mode param trigger body =>
    -- Quantifier-bound names shadow promoted names; the body is
    -- still rewritten. Quantifier params introduce their own scope
    -- but they are not in `naming` (only inputs / locals / channel
    -- bindings are), and they have distinct `uniqueId`s after
    -- resolution, so `promotedFieldName` returns `none` for them.
    { val := .Quantifier mode param
        (trigger.attach.map fun ⟨tr, _⟩ => rewriteStmtExpr naming tr)
        (rewriteStmtExpr naming body),
      source := src }
  | .Var (.Field target field) =>
    { val := .Var (.Field (rewriteStmtExpr naming target) field), source := src }
  | .Assigned name =>
    { val := .Assigned (rewriteStmtExpr naming name), source := src }
  | .Old v => { val := .Old (rewriteStmtExpr naming v), source := src }
  | .Fresh v => { val := .Fresh (rewriteStmtExpr naming v), source := src }
  | .Assert cond =>
    { val := .Assert
        { cond with condition := rewriteStmtExpr naming cond.condition },
      source := src }
  | .Assume c => { val := .Assume (rewriteStmtExpr naming c), source := src }
  | .ProveBy v p =>
    { val := .ProveBy (rewriteStmtExpr naming v) (rewriteStmtExpr naming p), source := src }
  | .ContractOf ty f =>
    { val := .ContractOf ty (rewriteStmtExpr naming f), source := src }
  -- Leaves: unchanged.
  | .Exit _ | .Yield | .LiteralInt _ | .LiteralBool _ | .LiteralString _
  | .LiteralDecimal _ | .New _ | .This | .Abstract | .All | .Hole .. => expr
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals (cases expr; simp_all; omega)

/-- Promote every coroutine-body local to a `self#field` access.
    Pure rewrite — does not generate the composite or the `moveNext`
    body, only the body the dispatcher will eventually wrap. The
    `naming` argument must be the same `fieldNaming proc` used to build
    the composite, so accesses and declarations agree on field names. -/
private def promoteLocalsInBody (naming : FieldNaming) (body : StmtExprMd) : StmtExprMd :=
  rewriteStmtExpr naming body

/-! ## State-machine linearization (`MoveNext`)

The coroutine body is compiled into a dispatch loop over the `$pc`
control field:

```
while (true) {
  if      ($pc == 1) { <state 1> }
  else if ($pc == 2) { <state 2> }
  ...
  else { return }                 -- $pc == END (= 0)
}
```

Each generated *state block* ends in one of two terminators:

* **suspend** — `$pc := k; return` — control returns to the caller and
  the coroutine resumes at state `k` on the next `resume`.
* **transition** — `$pc := k` followed by falling through the `if`-chain;
  the enclosing `while (true)` re-dispatches to state `k`. Control-flow
  joins (loop back-edges, branch merges) are realized this way, so no
  `goto`/`exit` is needed.

`linearize stmt next` emits the blocks for `stmt` and returns the state
id at which executing `stmt` *begins*; on completion `stmt` transitions
to the caller-supplied continuation `next`. Continuations thread in, so
sequencing composes right-to-left. -/

/-- A reserved state id meaning "the coroutine has run to completion".
    The dispatcher's `else` arm (no matching `$pc`) returns. -/
private def endState : Nat := 0

/-- Build an integer-literal expression node. -/
private def intLit (n : Int) : StmtExprMd :=
  { val := .LiteralInt n, source := none }

/-- `self#$pc` read. -/
private def pcRead : StmtExprMd := selfFieldRead "$pc" none

/-- `self#$pc := k` as a statement. -/
private def pcAssign (k : Nat) : StmtExprMd :=
  { val := .Assign [selfFieldTarget "$pc" none] (intLit (Int.ofNat k)), source := none }

/-- A bare `return` (no value) — the suspend half of a yield. -/
private def bareReturn : StmtExprMd := { val := .Return none, source := none }

/-- `lhs == rhs` over integers. -/
private def eqInt (lhs rhs : StmtExprMd) : StmtExprMd :=
  { val := .PrimitiveOp .Eq [lhs, rhs], source := none }

/-- Wrap a list of statements as a `Block` with no label. -/
private def block (stmts : List StmtExprMd) : StmtExprMd :=
  { val := .Block stmts none, source := none }

/-- Does this subtree contain a `yield` (in statement or expression
    position)? Determines whether `linearize` keeps the subtree as a
    single straight-line state or must split it across `$pc` values. -/
private def containsYield (expr : StmtExprMd) : Bool :=
  match _h : expr.val with
  | .Yield => true
  | .Block stmts _ => stmts.attach.any (fun ⟨s, _⟩ => containsYield s)
  | .IfThenElse c t e =>
    containsYield c || containsYield t
      || (match e with | some eb => containsYield eb | none => false)
  | .While c invs dec body =>
    containsYield c
      || invs.attach.any (fun ⟨i, _⟩ => containsYield i)
      || (match dec with | some d => containsYield d | none => false)
      || containsYield body
  | .Assign _ value => containsYield value
  | .Return v => match v with | some e => containsYield e | none => false
  | .Resume target v =>
    containsYield target || (match v with | some e => containsYield e | none => false)
  | .PureFieldUpdate target _ newValue => containsYield target || containsYield newValue
  | .StaticCall _ args => args.attach.any (fun ⟨a, _⟩ => containsYield a)
  | .PrimitiveOp _ args => args.attach.any (fun ⟨a, _⟩ => containsYield a)
  | .ReferenceEquals l r => containsYield l || containsYield r
  | .AsType t _ => containsYield t
  | .IsType t _ => containsYield t
  | .InstanceCall target _ args =>
    containsYield target || args.attach.any (fun ⟨a, _⟩ => containsYield a)
  | .Quantifier _ _ trigger body =>
    (match trigger with | some t => containsYield t | none => false) || containsYield body
  | .Var (.Field target _) => containsYield target
  | .Assigned n => containsYield n
  | .Old v => containsYield v
  | .Fresh v => containsYield v
  | .Assert cond => containsYield cond.condition
  | .Assume c => containsYield c
  | .ProveBy v p => containsYield v || containsYield p
  | .ContractOf _ f => containsYield f
  | .Var (.Local _) | .Var (.Declare _)
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _
  | .LiteralDecimal _ | .New _ | .This | .Abstract | .All | .Hole .. => false
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals (cases expr; simp_all; omega)

/-- Linearization state: the accumulated `(stateId, body)` arms and a
    fresh-id counter. State ids start at 1 (`endState = 0` is reserved). -/
private structure LinState where
  /-- Emitted state arms, keyed by id. Order is not significant — the
      dispatcher sorts/chains them. -/
  arms : Array (Nat × StmtExprMd) := #[]
  /-- Next fresh state id to hand out. -/
  nextId : Nat := 1

private abbrev LinM := StateM LinState

/-- Allocate a fresh state id. -/
private def freshState : LinM Nat := do
  let s ← get
  modify (fun s => { s with nextId := s.nextId + 1 })
  return s.nextId

/-- Record a state arm: "when `$pc == id`, run `body`". -/
private def emitState (id : Nat) (body : StmtExprMd) : LinM Unit :=
  modify fun s => { s with arms := s.arms.push (id, body) }

/-- Linearize a statement into state arms.

    `linearize naming stmt next` emits the arms needed to run `stmt` and
    returns the state id at which `stmt` *begins*. On completion `stmt`
    transitions to `next` (the caller-supplied continuation).

    Structural recursion on `stmt.val`:

    * **yield-free subtree** — kept whole as one straight-line state that
      ends with a transition to `next`. This is the fast path: ordinary
      code never fragments into one state per statement.
    * **`Block`** — threaded right-to-left: the last statement's
      continuation is `next`, each earlier statement's continuation is
      the entry of the next.
    * **`IfThenElse c t e`** — `c` is yield-free here;
       branch entries are linearized with continuation
      `next`, and a dispatching state evaluates `c` and jumps to the
      chosen branch entry.
    * **`While c body`** — a head state asserts the invariants then
      evaluates `c`: true enters the linearized body, false transitions
      to `next`. The body's continuation is a `bodyEnd` state that
      re-asserts the invariants before looping back to the head, so the
      back-edge carries the inductive "body preserves invariant" check.
    * **`Yield`** — suspends: the entry state sets `$pc := next; return`.
      Resumption re-dispatches to `next`.
    * **`x := yield`** (`.Assign [x] yield`) — value-receiving suspend.
      Splits into two states: a *suspend* state (`$pc := resume; return`)
      and a *resume* state that binds the resume argument into `x`
      (`x := <resumeParam>; $pc := next`). `resumeParam` is the parameter
      of the generated `resume` procedure that carries the value passed
      at the call site via `resume(co, v)` — it is per-call data, not
      coroutine state, so it is read as a plain local. -/
private partial def linearize (naming : FieldNaming) (resumeParam : Option Identifier)
    (stmt : StmtExprMd) (next : Nat) : LinM Nat := do
  -- Fast path: a subtree with no yield is one atomic state.
  if !containsYield stmt then
    let id ← freshState
    emitState id (block [stmt, pcAssign next])
    return id
  match stmt.val with
  | .Block stmts _ =>
    -- Thread continuations right-to-left. Empty block ≡ no-op → next.
    let mut entry := next
    for s in stmts.reverse do
      entry ← linearize naming resumeParam s entry
    return entry
  | .Assign targets value =>
    match value.val with
    | .Yield =>
      -- `x := yield`: suspend, then on resume bind the resume argument
      -- into the target(s). Two states: suspend (return to caller) and
      -- resume (rebind, then continue to `next`).
      let resumeId ← freshState
      let suspendId ← freshState
      emitState suspendId (block [pcAssign resumeId, bareReturn])
      let rebind : List StmtExprMd := match resumeParam with
        | some rp =>
          -- `x := <resumeParam>`. The resume value is a local parameter
          -- of `resume`, so it is read with `.Var (.Local rp)`. Source
          -- is the original assignment's, so a failed obligation points
          -- back at `x := yield`.
          [{ val := .Assign targets { val := .Var (.Local rp), source := stmt.source },
             source := stmt.source }]
        | none =>
          -- No `resumes` binding declared, so there is no value to bind;
          -- the target keeps its prior value. (Resolution should require
          -- a `resumes` clause when the body uses `x := yield`.)
          []
      emitState resumeId (block (rebind ++ [pcAssign next]))
      return suspendId
    | _ =>
      -- RHS contains a yield but is not exactly `yield` (e.g.
      -- `x := f(yield)`). Yields nested in subexpressions are not a
      -- supported surface form; keep as one state so elaboration stays
      -- total. Such positions should be rejected at resolution.
      let id ← freshState
      emitState id (block [stmt, pcAssign next])
      return id
  | .IfThenElse c t e =>
    let thenEntry ← linearize naming resumeParam t next
    let elseEntry ← match e with
      | some eb => linearize naming resumeParam eb next
      | none => pure next
    let id ← freshState
    emitState id
      { val := .IfThenElse c (pcAssign thenEntry) (some (pcAssign elseEntry)),
        source := stmt.source }
    return id
  | .While c invs _dec body =>
    -- The structured `While` dissolves into the dispatch loop, but its
    -- invariants survive as explicit `assert`s at three distinct states,
    -- so a failure localizes to the right place:
    --
    --   * head       — asserts the invariants, then tests `c`. Reached
    --                  on loop entry and on every back-edge, this is the
    --                  "invariant holds at the top of the loop" check.
    --   * bodyEnd    — the body's continuation: asserts the invariants
    --                  before transitioning to the loop exit. A failure
    --                  here means *the body broke the invariant*, pointing
    --                  at the body rather than the head.
    --   * loop exit  — the `c`-false path out of the head; reached when
    --                  the loop terminates. (No separate assert: control
    --                  arrives straight from the head's assert with `¬c`,
    --                  so post-loop states already have `invariants ∧ ¬c`.)
    --
    -- The back-edge runs body → bodyEnd (asserts) → head (asserts): the
    -- bodyEnd assert is the inductive "body preserves the invariant"
    -- check; the head assert restates it at the loop top. Both are kept
    -- for precise localization.
    --
    -- Invariants are already local-promoted (rewriteStmtExpr recurses
    -- into `While` invariants before linearization), so they reference
    -- `self#…` fields. `decreases` is dropped — termination is a separate
    -- Stage-3 obligation against `$pc`, not expressible as an inline
    -- assert.
    let asserts : List StmtExprMd := invs.map fun i =>
      { val := .Assert { condition := i, summary := none }, source := i.source }
    let head ← freshState
    let bodyEnd ← freshState
    -- Body's continuation is `bodyEnd` (assert, then back to `head`), so
    -- the back-edge passes through the body-preservation check.
    let bodyEntry ← linearize naming resumeParam body bodyEnd
    emitState bodyEnd (block (asserts ++ [pcAssign head]))
    -- Head: assert invariants, then branch — true → body, false → exit.
    emitState head
      (block (asserts ++
        [{ val := .IfThenElse c (pcAssign bodyEntry) (some (pcAssign next)),
           source := stmt.source }]))
    return head
  | .Yield =>
    -- Suspend: stamp the resume target and return to the caller.
    let id ← freshState
    emitState id (block [pcAssign next, bareReturn])
    return id
  | _ =>
    -- Any other yield-containing expression (e.g. `z := yield` after
    -- promotion, or a yield nested in a call argument) is handled by
    -- the fast path's negation only if yield-free; reaching here means
    -- a yield in an unsupported position. Emit a straight-line state
    -- that transitions to `next` so elaboration stays total; Stage-2
    -- TODO: lower expression-position yields explicitly.
    let id ← freshState
    emitState id (block [stmt, pcAssign next])
    return id

/-- Assemble the dispatch loop from emitted state arms. Produces:

    ```
    while (true) {
      if      ($pc == id₁) { <arm₁> }
      else if ($pc == id₂) { <arm₂> }
      ...
      else { return }                  -- no matching state ⇒ done
    }
    ```

    Built as a right-fold over the arms so the innermost `else` is the
    terminal `return`. Arm order is cosmetic — every arm self-identifies
    by its `$pc` guard, so the chain is correct under any permutation. -/
private def buildDispatchLoop (arms : Array (Nat × StmtExprMd)) : StmtExprMd :=
  let terminal : StmtExprMd := bareReturn
  let chain : StmtExprMd := arms.foldr (init := terminal) fun (id, body) acc =>
    { val := .IfThenElse (eqInt pcRead (intLit (Int.ofNat id))) body (some acc),
      source := none }
  { val := .While { val := .LiteralBool true, source := none } [] none chain,
    source := none }

/-- Linearize a body and return both the assembled dispatch loop and the
    *entry state id* — the `$pc` value at which a freshly-constructed
    coroutine begins. The constructor initializes `$pc` to this id.

    The body's top-level continuation is `endState` (= 0), which has no
    arm in the dispatcher, so running off the end lands in the `else`
    branch and returns — "done". `endState` and the entry id are always
    distinct (entry is a fresh id ≥ 1), so there is no collision between
    "freshly constructed" and "done". -/
private def linearizeBody (naming : FieldNaming) (resumeParam : Option Identifier)
    (body : StmtExprMd) : StmtExprMd × Nat :=
  let (entry, finalState) := (linearize naming resumeParam body endState).run {}
  (buildDispatchLoop finalState.arms, entry)

/-- Guard a halt postcondition with `$pc == END`. The plain `ensures Q`
    of a coroutine fires only when the coroutine has run to completion,
    so on `resume` it becomes `($pc == END) ==> Q` — vacuously true while
    the coroutine is still suspended mid-body, and `Q` only when done.
    Applied to plain `ensures`, *not* to `guarantees` (which fires at
    every yield, unguarded). -/
private def guardWithEnd (c : Condition) : Condition :=
  let guard := eqInt pcRead (intLit (Int.ofNat endState))
  let guarded : StmtExprMd :=
    { val := .PrimitiveOp .Implies [guard, c.condition], source := c.condition.source }
  { c with condition := guarded }

/-- Add the `resume` instance procedure to a coroutine's state composite.
    The resume body is the linearized state machine over the coroutine's
    promoted body, dispatched on `self#$pc`. `proc` supplies that body;
    `composite` supplies the field layout the body's `self#…` accesses
    refer to; `naming` keeps the two in agreement.

    The generated `resume` is an `opaque`, side-effecting instance
    procedure. Outgoing values flow through `self`'s `yields` fields; the
    *incoming* resumed value is `resume`'s input parameter(s), taken
    verbatim from the coroutine's `resumes` bindings. `x := yield` reads
    that parameter on re-entry (see `linearize`).

    Contracts (all clause expressions rewritten through `naming`, so
    references to inputs / promoted locals / `yields` become `self#…`):

      * `relies R`     → `resume` **precondition** — assumed on every
                         resume (the scheduler may have run other
                         coroutines since I last ran).
      * `guarantees G` → `resume` **postcondition**, unguarded — I
                         re-establish it at every yield, i.e. every time
                         `resume` returns.
      * `ensures Q` (halt) → `resume` **postcondition guarded by
                         `$pc == END`** — `($pc == END) ==> Q` — only
                         asserted when the coroutine has run off the end,
                         vacuous while still suspended.
      * `requires` (construction) → belongs on the *constructor* (see below) -/
private def populateCoroutineComposite (naming : FieldNaming) (proc : Procedure)
    (composite : CompositeType) : CompositeType :=
  match proc.body with
  | .Opaque haltPosts (some impl) _ =>
    let promoted := rewriteStmtExpr naming impl
    -- The resumed value is `resume`'s parameter. Laurel's surface allows
    -- a list, but the canonical `resumes (y: U)` has one binding; we read
    -- the first as the `x := yield` target. (Multi-resume is a Stage-2
    -- surface restriction.)
    let resumeParam : Option Identifier := proc.resumes.head?.map (·.name)
    let (dispatchBody, _entry) := linearizeBody naming resumeParam promoted
    -- Rewrite every contract expression so it refers to the generated
    -- composite fields, matching the rewritten body.
    let rewriteCond (c : Condition) : Condition :=
      c.mapCondition (rewriteStmtExpr naming)
    let relies'     := proc.relies.map rewriteCond
    let guarantees' := proc.guarantees.map rewriteCond
    -- Halt `ensures` lives in the `Opaque` body's postconditions; guard
    -- each with `$pc == END` so it only fires at completion.
    let haltEnsures := haltPosts.map (guardWithEnd ∘ rewriteCond)
    -- `resume` postconditions = per-yield guarantees (unguarded) ++
    -- END-guarded halt ensures.
    let resumePosts := guarantees' ++ haltEnsures
    let resumeProc : Procedure :=
      { kind := .Regular
        name := { proc.name with text := "resume" }
        inputs := proc.resumes
        outputs := []
        -- `relies` is the per-resume precondition.
        preconditions := relies'
        relies := []
        guarantees := []
        yields := []
        resumes := []
        decreases := none
        isFunctional := false
        invokeOn := none
        -- Postconditions on the Opaque body: guarantees + guarded halt.
        body := .Opaque resumePosts (some dispatchBody) [] }
    { composite with instanceProcedures := resumeProc :: composite.instanceProcedures }
  | _ => composite

/-- The entry state id for a coroutine body — the `$pc` value the
    constructor must initialize. Mirrors the `linearizeBody` allocation
    so the constructor and the dispatcher agree. -/
private def coroutineEntryState (naming : FieldNaming) (proc : Procedure) : Nat :=
  match proc.body with
  | .Opaque _ (some impl) _ =>
    let promoted := rewriteStmtExpr naming impl
    let resumeParam : Option Identifier := proc.resumes.head?.map (·.name)
    (linearizeBody naming resumeParam promoted).2
  | _ => endState

/-- Generate the spawn constructor for a coroutine: a static procedure
    that allocates and initializes a fresh state composite.

    ```
    procedure <coro>(p₁: T₁, …) returns ($co: <coro>State)
      requires <plain requires, verbatim>      -- construction precondition
      opaque
      ensures $co#$pc == 0                      -- starts at the entry hop
      ensures $co#p₁ == p₁  …                   -- inputs copied into fields
    {
      $co := new <coro>State;
      $co#$pc := 0;
      $co#p₁ := p₁; …
    }
    ```

    The coroutine's plain `requires` is the *construction* precondition;
    it references the coroutine parameters, which are this constructor's
    own parameters, so it transfers **verbatim** — no `self#` rewrite
    (unlike `relies`/`guarantees`/`ensures`, whose subjects are promoted
    coroutine state).

    The `ensures` are essential for soundness of the downstream dispatch:
    without `$co#$pc == 0`, a caller could not establish that the first
    `resume` enters at the body's start; without the input-copy
    postconditions, the promoted `self#pₖ` reads would be havoced.

    The constructor is named after the coroutine itself, so a spawn call
    `coro(args)` resolves here once call-site rewriting (separate change)
    fixes the *type annotation* `co: coro` → `co: <coro>State`. -/
private def coroutineConstructor (naming : FieldNaming) (proc : Procedure)
    (composite : CompositeType) (entry : Nat) : Procedure :=
  let compositeTy : HighTypeMd := { val := .UserDefined composite.name, source := none }
  let coName : Identifier := { text := "$co", uniqueId := none, source := none }
  let coRead : StmtExprMd := { val := .Var (.Local coName), source := none }
  let fieldRead (f : Identifier) : StmtExprMd :=
    { val := .Var (.Field coRead f), source := none }
  let fieldTarget (f : Identifier) : AstNode Variable :=
    { val := .Field coRead f, source := none }
  let paramRead (p : Parameter) : StmtExprMd :=
    { val := .Var (.Local p.name), source := none }
  -- Body: allocate, set `$pc := entry`, copy each input into its field.
  let allocStmt : StmtExprMd :=
    { val := .Assign [{ val := .Local coName, source := none }]
        { val := .New composite.name, source := none }, source := none }
  let pcInit : StmtExprMd :=
    { val := .Assign [fieldTarget "$pc"] (intLit (Int.ofNat entry)), source := none }
  let inputInits : List StmtExprMd := proc.inputs.map fun p =>
    { val := .Assign [fieldTarget (paramToField naming p).name] (paramRead p), source := none }
  let ctorBody := block ([allocStmt, pcInit] ++ inputInits)
  -- Postconditions: starting pc and the input-copy relation.
  let pcEnsures : Condition :=
    { condition := eqInt (fieldRead "$pc") (intLit (Int.ofNat entry)), summary := none }
  let inputEnsures : List Condition := proc.inputs.map fun p =>
    { condition := eqInt (fieldRead (paramToField naming p).name) (paramRead p), summary := none }
  { kind := .Regular
    name := proc.name
    inputs := proc.inputs
    outputs := [{ name := coName, type := compositeTy }]
    -- Plain `requires` transfers verbatim — its subjects are the inputs,
    -- which are this constructor's parameters.
    preconditions := proc.preconditions
    relies := []
    guarantees := []
    yields := []
    resumes := []
    decreases := none
    isFunctional := false
    invokeOn := none
    body := .Opaque (pcEnsures :: inputEnsures) (some ctorBody) [] }

/-- Phase A entry point: replace every coroutine procedure with a state
    composite carrying a `resume` instance procedure.

    Per coroutine procedure:
      * `fieldNaming` fixes collision-safe field names, shared by the
        composite declaration and the promoted-local body rewrite;
      * `coroutineToComposite` builds the `$pc` + inputs + locals +
        channel-binding field layout;
      * `populateCoroutineComposite` adds the `resume` instance
        procedure (the linearized state machine over the promoted body).
    The coroutine procedure is dropped from `staticProcedures` (it is now
    a type, not a callable); the generated composite is appended to
    `types`. The spawn constructor (a static procedure named after the
    coroutine) replaces the dropped coroutine in `staticProcedures`, so a
    `coro(args)` call still resolves to a callable. Regular procedures
    pass through untouched.

    TODO — call-site rewrite (separate change): a spawn `var co: coro :=
    coro(args)` resolves its *call* to the new constructor automatically
    (same name), but the *type annotation* `co: coro` still names the
    removed coroutine type — it must be rewritten to `co: <coro>State`.
    Likewise `resume(co[, v])` must become an instance call `co.resume(v)`.
    Until that lands, `rejectCoroutines` (earlier in the pipeline)
    guarantees any program containing a coroutine halts with a diagnostic
    before Core, so the dangling references are never re-resolved into
    final output. -/
def elaborateCoroutines (_ : SemanticModel) (p : Program) : Program :=
  let (coroutines, regulars) := p.staticProcedures.partition Procedure.is_coroutine
  -- Each coroutine yields a state composite (with `resume`) and a spawn
  -- constructor (a static procedure that allocates + initializes it).
  let generatedTypes : List TypeDefinition := coroutines.map fun proc =>
    let naming := fieldNaming proc
    let shell := coroutineToComposite naming proc
    .Composite (populateCoroutineComposite naming proc shell)
  let generatedCtors : List Procedure := coroutines.map fun proc =>
    let naming := fieldNaming proc
    let entry := coroutineEntryState naming proc
    coroutineConstructor naming proc (coroutineToComposite naming proc) entry
  { p with
    staticProcedures := regulars ++ generatedCtors,
    types := p.types ++ generatedTypes }


end Strata.Laurel
end
