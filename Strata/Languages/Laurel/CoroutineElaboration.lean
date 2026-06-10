module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.MapStmtExpr
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
  { name := { fieldName with uniqueId := none }, isMutable := true, type := p.type }

/-- Build the state-machine composite for a coroutine.

    Layout (every field mutable so `moveNext` can write):
      `var $pc: int`                  — state index (0 = entry)
      `var <input>: <T>`              — one per `proc.inputs`
      `var <local>: <T>`              — one per body-collected local
      `var <yield>: <T>`              — one per `proc.yields`

    `resumes` bindings are *not* fields: the resumed value is a per-call
    argument threaded as a parameter of the generated `resume` procedure,
    not coroutine state.

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
  { name := { proc.name with text := proc.name.text ++ "State", uniqueId := none },
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
  | .HasNext target =>
    { val := .HasNext (rewriteStmtExpr naming target), source := src }
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
  | .HasNext target => containsYield target
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
private def linearize (naming : FieldNaming) (resumeParam : Option Identifier)
    (stmt : StmtExprMd) (next : Nat) : LinM Nat := do
  -- Fast path: a subtree with no yield is one atomic state.
  if !containsYield stmt then
    let id ← freshState
    emitState id (block [stmt, pcAssign next])
    return id
  match _h: stmt.val with
  | .Block stmts _ =>
    -- Thread continuations right-to-left: the last statement's
    -- continuation is `next`, each earlier statement's continuation is
    -- the entry of the one after it. Empty block ≡ no-op → next.
    -- `foldrM` over `.attach` carries the `s ∈ stmts` membership proof
    -- the termination checker needs, and threads the accumulator exactly
    -- as `for s in stmts.reverse` did — so state-id order is unchanged.
    stmts.attach.foldrM (init := next) fun ⟨s, _⟩ cont =>
      linearize naming resumeParam s cont
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
    let elseEntry ← match _he : e with
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
    -- obligation against `$pc`, not expressible as an inline assert.
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
    -- that transitions to `next` so elaboration stays total; lowering
    -- expression-position yields explicitly is a TODO.
    let id ← freshState
    emitState id (block [stmt, pcAssign next])
    return id
  termination_by sizeOf stmt
  decreasing_by
    all_goals (have := AstNode.sizeOf_val_lt stmt)
    all_goals (simp_all; try term_by_mem)
    all_goals (cases stmt; simp_all; omega)


/-! ### State coalescing

Linearization emits one arm per structural node, so a run of statements
with no yield between them spreads across several arms linked by pure
`$pc := k` transitions. At runtime the dispatcher already collapses these
(a transition falls through and re-dispatches), but the *generated* code
is fat. The coalescing pass merges a yield-to-yield fragment back into a
single arm.

A merge fires when arm A **tail-transitions** to B — A's body is a block
whose last statement is `$pc := B` with no intervening `return` — and B
has exactly one predecessor (only one `$pc := B` site exists anywhere)
and B is neither the entry nor the end. Then B's body is spliced in place
of A's trailing transition and B's arm is deleted. Flattening B's block
into A lets chains compress to a fixpoint. Merging never crosses a
suspend (`... ; return`), since a suspend arm's last statement is the
`return`, not a `$pc :=` — that is exactly the yield boundary we keep. -/

/-- Target of a `$pc := k` statement, if `s` is precisely that. -/
private def pcAssignTarget? (s : StmtExprMd) : Option Nat :=
  match s.val with
  | .Assign [t] v =>
    match t.val, v.val with
    | .Field _ f, .LiteralInt k => if f.text == "$pc" && k ≥ 0 then some k.toNat else none
    | _, _ => none
  | _ => none

/-- All `$pc := k` targets mentioned anywhere in a generated arm body
    (straight transitions and the two arms of a dispatch conditional).
    `.attach` on the block's statements gives the termination checker a
    membership proof for each recursive call, exactly as in
    `collectVarDeclsExpr` / `containsYield`. -/
private def pcTargets (s : StmtExprMd) : List Nat :=
  match _h : s.val with
  | .Assign _ _ => (pcAssignTarget? s).toList
  | .Block stmts _ => stmts.attach.flatMap (fun ⟨st, _⟩ => pcTargets st)
  | .IfThenElse _ t e => pcTargets t ++ (match e with | some eb => pcTargets eb | none => [])
  | _ => []
  termination_by sizeOf s
  decreasing_by
    all_goals (try have := AstNode.sizeOf_val_lt s)
    all_goals (try term_by_mem)
    all_goals (cases s; simp_all; omega)


/-- If `body` is a block whose last statement is `$pc := k` (a tail
    transition, no trailing `return`), return `k`. Suspend arms end in
    `return` and conditional arms end in an `if`, so both return `none`. -/
private def tailTransition? (body : StmtExprMd) : Option Nat :=
  match body.val with
  | .Block stmts _ => stmts.getLast?.bind pcAssignTarget?
  | _ => none

/-- Splice `bbody` in place of `abody`'s trailing `$pc :=` statement.
    `bbody`'s statements are flattened in (rather than nested as a
    sub-block) so the result's last statement is `bbody`'s last —
    keeping the merged arm eligible for further coalescing. -/
private def spliceTail (abody bbody : StmtExprMd) : StmtExprMd :=
  match abody.val with
  | .Block astmts lbl =>
    let bstmts := match bbody.val with
      | .Block bs _ => bs
      | _ => [bbody]
    { val := .Block (astmts.dropLast ++ bstmts) lbl, source := abody.source }
  | _ => abody  -- not a block ⇒ not a tail-transition arm; unreachable

/-- Fixpoint merge of tail-transition arms into their unique-predecessor
    targets. Each step removes one arm, so the recursion terminates. -/
private def coalesceArms (entry : Nat) (arms : Array (Nat × StmtExprMd))
    : Array (Nat × StmtExprMd) :=
  let go (m : Std.HashMap Nat StmtExprMd) : Std.HashMap Nat StmtExprMd := Id.run do
    let mut m := m
    repeat
      -- Predecessor counts: how many `$pc := k` sites reference each k.
      let counts : Std.HashMap Nat Nat :=
        m.fold (fun acc _ body =>
          (pcTargets body).foldl (fun acc k => acc.insert k ((acc.getD k 0) + 1)) acc) ∅
      -- Find an arm A whose tail transitions to a mergeable B.
      let cand := m.toList.findSome? fun (a, body) =>
        match tailTransition? body with
        | some b =>
          if b != entry && b != endState && counts.getD b 0 == 1 && m.contains b
          then some (a, b) else none
        | none => none
      match cand with
      | none => break
      | some (a, b) =>
        let abody := m.getD a (block [])
        let bbody := m.getD b (block [])
        m := (m.erase b).insert a (spliceTail abody bbody)
    return m
  let m := arms.foldl (fun m (id, b) => m.insert id b) (∅ : Std.HashMap Nat StmtExprMd)
  (go m).toList.toArray

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
  -- Coalesce yield-to-yield fragments before assembling the dispatcher,
  -- so a run of pure transitions collapses into a single arm.
  let coalesced := coalesceArms entry finalState.arms
  (buildDispatchLoop coalesced, entry)

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
    -- the first as the `x := yield` target.
    let resumeParam : Option Identifier := proc.resumes.head?.map (·.name)
    let (dispatchBody, _entry) := linearizeBody naming resumeParam promoted
    -- Rewrite every contract expression so it refers to the generated
    -- composite fields, matching the rewritten body.
    let rewriteCond (c : Condition) : Condition :=
      c.mapCondition (rewriteStmtExpr naming)
    let relies'     := proc.relies.map rewriteCond
    let guarantees' := proc.guarantees.map rewriteCond
    -- A resumed coroutine must not already be done: `$pc != END`. This
    -- rules out resuming a coroutine that has run off its end (which
    -- would otherwise fall straight to the dispatcher's `else`/return
    -- with no work). It is a precondition of every `resume` call.
    let notDone : Condition :=
      { condition :=
          { val := .PrimitiveOp .Neq [pcRead, intLit (Int.ofNat endState)], source := none },
        summary := none }
    -- Halt `ensures` lives in the `Opaque` body's postconditions; guard
    -- each with `$pc == END` so it only fires at completion.
    let haltEnsures := haltPosts.map (guardWithEnd ∘ rewriteCond)
    -- `resume` postconditions = per-yield guarantees (unguarded) ++
    -- END-guarded halt ensures.
    let resumePosts := guarantees' ++ haltEnsures
    -- The body and contracts emit `.This`/`this#…`. After
    -- `LiftInstanceProcedures` lifts this method to a static procedure,
    -- `this` no longer resolves; declare an explicit `self : <c>State`
    -- input (the convention `LiftInstanceProcedures` already supports
    -- for hand-written instance methods) and rewrite every `.This` to
    -- `.Var (.Local self)`.
    let selfName : Identifier := { text := "self", uniqueId := none, source := none }
    let selfType : HighTypeMd := { val := .UserDefined composite.name, source := none }
    let selfParam : Parameter := { name := selfName, type := selfType }
    let thisToSelf : StmtExprMd → StmtExprMd := mapStmtExpr fun e =>
      match e.val with
      | .This => { e with val := .Var (.Local selfName) }
      | _ => e
    let dispatchBody' := thisToSelf dispatchBody
    let resumePosts' := resumePosts.map (·.mapCondition thisToSelf)
    let preconds' := (notDone :: relies').map (·.mapCondition thisToSelf)
    -- Copy each `yields (x: T)` binding from `self#<x>` into the output
    -- parameter `x` immediately before every `return` in the dispatch
    -- body, so callers receive the most-recently-yielded values.
    let selfRead : StmtExprMd := { val := .Var (.Local selfName), source := none }
    let yieldCopies : List StmtExprMd := proc.yields.map fun p =>
      let fieldName := (paramToField naming p).name
      let fieldRead : StmtExprMd :=
        { val := .Var (.Field selfRead { fieldName with uniqueId := none }), source := none }
      let outTarget : AstNode Variable :=
        { val := .Local { p.name with uniqueId := none }, source := none }
      { val := .Assign [outTarget] fieldRead, source := none }
    let copyBeforeReturn (e : StmtExprMd) : StmtExprMd :=
      match e.val with
      | .Return none => block (yieldCopies ++ [e])
      | _ => e
    let dispatchBody'' :=
      if proc.yields.isEmpty then dispatchBody'
      else mapStmtExpr copyBeforeReturn dispatchBody'
    let yieldOutputs : List Parameter := proc.yields.map fun p =>
      { p with name := { p.name with uniqueId := none } }
    let resumeProc : Procedure :=
      { kind := .Regular
        name := { proc.name with text := "resume", uniqueId := none }
        inputs := selfParam :: proc.resumes
        outputs := yieldOutputs
        preconditions := preconds'
        relies := []
        guarantees := []
        yields := []
        resumes := []
        decreases := none
        isFunctional := false
        invokeOn := none
        body := .Opaque resumePosts' (some dispatchBody'') [] }
    -- `has_next(co)` returns true iff the coroutine has not yet run to
    -- completion (its `$pc` field has not reached the END state). The
    -- generated method is a pure observer; the user-side syntax
    -- `has_next(co)` is rewritten to `co#has_next()` by the caller pass.
    let hasNextOut : Identifier := { text := "result", uniqueId := none, source := none }
    let hasNextOutParam : Parameter :=
      { name := hasNextOut, type := { val := .TBool, source := none } }
    let pcReadSelf : StmtExprMd :=
      { val := .Var (.Field selfRead { text := "$pc", uniqueId := none, source := none }),
        source := none }
    let pcNeqEnd : StmtExprMd :=
      { val := .PrimitiveOp .Neq [pcReadSelf, intLit (Int.ofNat endState)], source := none }
    let hasNextProc : Procedure :=
      { kind := .Regular
        name := { proc.name with text := "has_next", uniqueId := none }
        inputs := [selfParam]
        outputs := [hasNextOutParam]
        preconditions := []
        relies := []
        guarantees := []
        yields := []
        resumes := []
        decreases := none
        isFunctional := true
        invokeOn := none
        body := .Transparent pcNeqEnd }
    { composite with
      instanceProcedures := resumeProc :: hasNextProc :: composite.instanceProcedures }
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
    name := { proc.name with uniqueId := none }
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

/-! ## Caller-side rewrite

For each elaborated coroutine `c`, retarget every caller:
  * type annotations `co: c` → `co: <c>State`
  * `resume(co[, v])` → `InstanceCall co #"resume" [v?]`
  (`co#resume([v])` in concrete syntax)

The pipeline re-resolves after this pass, so generated identifiers
have `uniqueId := none`. -/

private abbrev CoroutineSet := Std.HashSet String

private def stateTypeName (id : Identifier) : Identifier :=
  { id with text := id.text ++ "State", uniqueId := none }

/-- Rewrite a `HighTypeMd`: every `UserDefined ref` naming a coroutine
    in `coros` becomes `<ref>State`. Recurses into structural type
    formers. -/
private def rewriteCallerType (coros : CoroutineSet) (ty : HighTypeMd) : HighTypeMd :=
  let val' := match _h : ty.val with
    | .UserDefined ref =>
      if coros.contains ref.text then .UserDefined (stateTypeName ref) else ty.val
    | .TTypedField vt => .TTypedField (rewriteCallerType coros vt)
    | .TSet et => .TSet (rewriteCallerType coros et)
    | .TMap kt vt => .TMap (rewriteCallerType coros kt) (rewriteCallerType coros vt)
    | .Applied base args =>
      .Applied (rewriteCallerType coros base) (args.attach.map fun ⟨a, _⟩ => rewriteCallerType coros a)
    | .Pure base => .Pure (rewriteCallerType coros base)
    | .Intersection tys =>
      .Intersection (tys.attach.map fun ⟨t, _⟩ => rewriteCallerType coros t)
    | .MultiValuedExpr tys =>
      .MultiValuedExpr (tys.attach.map fun ⟨t, _⟩ => rewriteCallerType coros t)
    | other => other
  { ty with val := val' }
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt ty)
  all_goals (try term_by_mem)
  all_goals (cases ty; simp_all; omega)

private def rewriteCallerParameter (coros : CoroutineSet) (p : Parameter) : Parameter :=
  { p with type := rewriteCallerType coros p.type }

/-- Rewrite a single node. Composes with `mapStmtExprM`'s bottom-up
    traversal, so child `StmtExprMd` nodes are already rewritten when
    this fires; the cases below patch only the *type* and `Resume`
    positions that the generic traversal does not enter. -/
private def rewriteCallerNode (coros : CoroutineSet) (e : StmtExprMd) : StmtExprMd :=
  match e.val with
  | .Resume target value =>
    let resumeName : Identifier := { text := "resume", uniqueId := none, source := e.source }
    { e with val := .InstanceCall target resumeName value.toList }
  | .HasNext target =>
    let methodName : Identifier := { text := "has_next", uniqueId := none, source := e.source }
    { e with val := .InstanceCall target methodName [] }
  | .New ref =>
    if coros.contains ref.text then { e with val := .New (stateTypeName ref) } else e
  | .AsType target ty =>
    { e with val := .AsType target (rewriteCallerType coros ty) }
  | .IsType target ty =>
    { e with val := .IsType target (rewriteCallerType coros ty) }
  | .Var (.Declare param) =>
    { e with val := .Var (.Declare (rewriteCallerParameter coros param)) }
  | .Quantifier mode param trigger body =>
    { e with val := .Quantifier mode (rewriteCallerParameter coros param) trigger body }
  | .Assign targets value =>
    let targets' := targets.map fun t => match t.val with
      | .Declare param => { t with val := .Declare (rewriteCallerParameter coros param) }
      | _ => t
    { e with val := .Assign targets' value }
  | .Hole det (some ty) =>
    { e with val := .Hole det (some (rewriteCallerType coros ty)) }
  | _ => e

private def rewriteCallerProcedure (coros : CoroutineSet) (proc : Procedure) : Procedure :=
  let f := mapStmtExpr (rewriteCallerNode coros)
  let proc : Procedure := mapProcedureBodiesM (m := Id) f proc
  { proc with
    inputs := proc.inputs.map (rewriteCallerParameter coros)
    outputs := proc.outputs.map (rewriteCallerParameter coros)
    preconditions := proc.preconditions.map (·.mapCondition f)
    relies := proc.relies.map (·.mapCondition f)
    guarantees := proc.guarantees.map (·.mapCondition f)
    decreases := proc.decreases.map f
    invokeOn := proc.invokeOn.map f }

private def rewriteCallerTypeDef (coros : CoroutineSet) (td : TypeDefinition) : TypeDefinition :=
  let f := mapStmtExpr (rewriteCallerNode coros)
  match td with
  | .Composite ct =>
    .Composite { ct with
      fields := ct.fields.map fun fld => { fld with type := rewriteCallerType coros fld.type }
      instanceProcedures := ct.instanceProcedures.map (rewriteCallerProcedure coros) }
  | .Constrained ct =>
    .Constrained { ct with
      base := rewriteCallerType coros ct.base
      constraint := f ct.constraint
      witness := f ct.witness }
  | .Datatype dt =>
    .Datatype { dt with
      constructors := dt.constructors.map fun ctor =>
        { ctor with args := ctor.args.map (rewriteCallerParameter coros) } }
  | .Alias ta =>
    .Alias { ta with target := rewriteCallerType coros ta.target }

private def rewriteCallerProgram (coros : CoroutineSet) (p : Program) : Program :=
  if coros.isEmpty then p else
  let f := mapStmtExpr (rewriteCallerNode coros)
  { p with
    staticProcedures := p.staticProcedures.map (rewriteCallerProcedure coros)
    staticFields := p.staticFields.map fun fld =>
      { fld with type := rewriteCallerType coros fld.type }
    types := p.types.map (rewriteCallerTypeDef coros)
    constants := p.constants.map fun c =>
      { c with type := rewriteCallerType coros c.type, initializer := c.initializer.map f } }

/-- Each coroutine `c` is replaced by:
      * a state composite `<c>State` (built by `coroutineToComposite`)
        carrying a `resume` instance procedure
        (`populateCoroutineComposite`);
      * a spawn constructor — a static procedure named `c` that
        allocates the composite and initializes `$pc`
        (`coroutineConstructor`).
    The coroutine procedure is dropped; callers are retargeted by
    `rewriteCallerProgram` (type annotations `co: c` → `co: <c>State`,
    `resume(co[, v])` → `co#resume([v])`). Once `LiftInstanceProcedures`
    runs, `co#resume(...)` folds into a static call to
    `<c>State$resume`. Regular procedures pass through unchanged except
    for the caller rewrite. -/
def elaborateCoroutines (_ : SemanticModel) (p : Program) : Program :=
  let (coroutines, regulars) := p.staticProcedures.partition Procedure.is_coroutine
  let generatedTypes : List TypeDefinition := coroutines.map fun proc =>
    let naming := fieldNaming proc
    let shell := coroutineToComposite naming proc
    .Composite (populateCoroutineComposite naming proc shell)
  let generatedCtors : List Procedure := coroutines.map fun proc =>
    let naming := fieldNaming proc
    let entry := coroutineEntryState naming proc
    coroutineConstructor naming proc (coroutineToComposite naming proc) entry
  let coros : CoroutineSet :=
    coroutines.foldl (fun s c => s.insert c.name.text) ∅
  let elaborated : Program :=
    { p with
      staticProcedures := regulars ++ generatedCtors,
      types := p.types ++ generatedTypes }
  rewriteCallerProgram coros elaborated


end Strata.Laurel
end
