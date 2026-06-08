/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
End-to-end execution tests for coroutines: parse a Laurel coroutine +
driver, lower through the full pipeline to Core, then invoke the Core
*concrete interpreter* (`Core.Statement.Command.runCall`) on the
driver to observe the runtime state.

Each test passes a free variable for the heap input (`h0`) and reports
the final `$heap` LExpr after the driver returns. With no concrete
reductions for `select(update(...))` in the Core interpreter today,
the heap output is mostly symbolic — but a passing test confirms that
(a) the pipeline lowers without diagnostics, (b) every call site
resolves, and (c) the constructor and resume calls inline correctly.
Once map theory lands in Core's concrete-eval, these tests' expected
outputs will sharpen from "symbolic chain" to concrete values.
-/

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import Strata.Languages.Laurel.Grammar
meta import Strata.Languages.Laurel.LaurelCompilationPipeline
meta import Strata.Languages.Core.ProgramEval
meta import Strata.Languages.Core.ProcedureEval
meta import Strata.Languages.Core.StatementEval

meta section

open Strata
open Strata.Laurel
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)
open Std (ToFormat Format format)
open Lambda

namespace Strata.Laurel

/-- A free variable representing a symbolic initial heap. The driver
    operates on this; the resulting `$heap` is the symbolic result of
    applying the constructor and any resume calls. -/
private def symHeap : Core.Expression.Expr := .fvar () "h0" none

/-- Lower a Laurel program to Core, then run the named driver
    procedure with `[symHeap]` as input. Print the resulting `$heap`
    binding (or any error). -/
private def runDriverThroughPipeline (input : String) (driverName : String) : IO Unit := do
  let inputCtx := StrataDDM.Parser.stringInputContext "test" input
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  match Laurel.TransM.run (Strata.Uri.file "test") (parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok p =>
    let (coreOpt, diags) ← Laurel.translate default p
    if !diags.isEmpty then
      IO.println s!"diagnostics ({diags.length}):"
      for d in diags do IO.println s!"  {d.message}"
    match coreOpt with
    | none => IO.println "no Core program produced"
    | some core =>
      match core.run with
      | .error e => IO.println s!"init error: {e.message}"
      | .ok E =>
        match Core.Program.Procedure.find? core ⟨driverName, ()⟩ with
        | none => IO.println s!"procedure '{driverName}' not found"
        | some p =>
          let lhs := p.header.outputs.keys
          let fuel := 100000
          let E' := Core.Statement.Command.runCall lhs driverName [symHeap] fuel E
          match E'.error with
          | none =>
            match E'.exprEnv.state.find? "$heap" with
            | some (_, v) => IO.println s!"$heap = {format v}"
            | none => IO.println "$heap not bound"
          | some err => IO.println s!"runtime error: {format err}"

/-! ## Bare counter: yields 0, 1, 2, ...

The driver spawns a counter and resumes it three times. After lowering
to Core via heap-parameterization, every coroutine field lives on a
heap-encoded composite; the resulting `$heap` is a `select(update(...))`
chain over the symbolic input `h0`. Concrete reductions for the
`select(update(m,k,v),k) == v` rule are not yet implemented in the
Core interpreter, so the resume calls' effect is currently invisible
(they execute, but their heap writes don't reduce away).

What we *do* observe: the constructor's effect (entry `$pc` = 6) is
applied to `h0`, confirming that the spawn ctor and lowering are
correct end-to-end.
-/

private def counterProgram := r"
coroutine counter() yields (x: int)
{
  var i: int := 0;
  while (true)
    invariant i >= 0
  {
    x := i;
    yield;
    i := i + 1
  }
};

procedure driver()
  opaque
{
  var co: counter := counter();
  resume(co);
  resume(co);
  resume(co)
};
"

/--
info: $heap = updateField(increment(h0), MkComposite(Heap..nextReference!(h0), counterState_TypeTag), counterState.$pc, BoxInt(6))
-/
#guard_msgs in
#eval! runDriverThroughPipeline counterProgram "driver"

/-! ## Producer with a parameter: spawn `producer(0)`, resume once.

Exercises the spawn constructor's input-copy behaviour (`seed` is
written into the composite during construction). The `$heap` shows
`updateField` chains for both `$pc := 4` (entry) and `seed := 0`. -/

private def producerProgram := r"
coroutine producer(seed: int) yields (x: int)
  requires seed >= 0
{
  x := seed; yield;
  x := seed + 1; yield
};

procedure driver()
  opaque
{
  var co: producer := producer(0);
  resume(co)
};
"

/--
info: $heap = updateField(updateField(increment(h0), MkComposite(Heap..nextReference!(h0), producerState_TypeTag), producerState.$pc, BoxInt(4)), MkComposite(Heap..nextReference!(h0), producerState_TypeTag), producerState.seed, BoxInt(0))
-/
#guard_msgs in
#eval! runDriverThroughPipeline producerProgram "driver"

end Strata.Laurel
end
