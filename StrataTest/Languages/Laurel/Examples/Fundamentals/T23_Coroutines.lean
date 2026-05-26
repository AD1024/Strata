/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Stage 1 tests for coroutine syntax: parse + resolution + the pipeline's
"not yet verified" rejection.

Coroutines, yield, resume, and rely/guarantee clauses parse and resolve
cleanly. The pipeline's `rejectCoroutines` pass surfaces a single
targeted diagnostic per coroutine declaration. Real verification (Phase A
elaboration → Phase B Core lowering) is Stage 2/3 work.

The intended user-facing model:
  coroutine coro(x: int) { ... yield ... };
  // the coroutine name `coro` doubles as a constructor:
  var co := coro(1);
  // resume drives it forward:
  resume(co);
At Stage 1 this all parses and resolves; semantics arrive in Stage 2 when
Phase A elaboration replaces `coroutine coro` with a generated composite
type plus a `Coro.resume` procedure, and rewrites `coro(1)` into
`new Coro(1)` with an init block.
-/

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples
meta import Strata.DDM.Elab
meta import Strata.DDM.BuiltinDialects.Init
meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
meta import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
meta import Strata.Languages.Laurel.Resolution

meta section

open StrataTest.Util
open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Run only parsing + resolution and return diagnostics (no SMT verification).
    Mirrors the helper in DuplicateNameTests so we can assert that the new
    constructs *parse and resolve* without firing the rejectCoroutines
    pipeline pass. -/
private def processResolution (input : Lean.Parser.InputContext) : IO (Array Diagnostic) := do
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input
  let uri := Strata.Uri.file input.fileName
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let files := Map.insert Map.empty uri input.fileMap
    return result.errors.toList.map (fun dm => dm.toDiagnostic files) |>.toArray

/-! ## Smallest coroutine: empty body, no spec.

Asserts that the new top-level `coroutine` keyword reaches the AST and
resolves without complaint. -/

def emptyCoroutine := r"
coroutine empty()
{
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "EmptyCoroutine" emptyCoroutine 14 processResolution

/-! ## Counter coroutine with a single yield.

Smoke test for `yield` (no value) inside a `while` body. -/

def counterCoroutine := r"
coroutine counter()
{
  var i: int := 0;
  while (i < 3)
    invariant i >= 0
  {
    i := i + 1;
    yield
  }
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "CounterCoroutine" counterCoroutine 14 processResolution

/-! ## Yielding a value via the `yields` binding.

Values flow out via the `yields x: T` clause. Each yield site assigns to
`x` first, then suspends with a bare `yield`. -/

def yieldValueProgram := r"
coroutine emit() yields (x: int)
{
  x := 1; yield;
  x := 2; yield;
  x := 3; yield
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "YieldValue" yieldValueProgram 14 processResolution

/-! ## Abstract (bodyless) coroutine with requires / ensures / modifies.

Exercises the full `coroutineSpec` block. The abstract form leaves the
implementation to a future override or treats it as a primitive. The
keywords `requires` and `ensures` are reused; their temporal semantics
inside a coroutine are per-resume / per-yield, kind-determined. -/

def abstractCoroutine := r"
composite Counter {
  var value: int
}

coroutine ticker(c: Counter)
  requires c#value >= old(c#value)
  ensures c#value == old(c#value) + 1
  modifies c;
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "AbstractCoroutine" abstractCoroutine 14 processResolution

/-! ## Calling a coroutine spawns an instance; `resume` drives it.

The coroutine name doubles as a constructor (Python-style:
`co = generator(args)`), and `resume(co)` advances it. The result of
`resume(co)` in statement position is dropped. -/

def spawnAndResumeStmt := r"
coroutine producer(seed: int) yields (x: int)
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

#guard_msgs (drop info, error) in
#eval testInputWithOffset "SpawnAndResumeStmt" spawnAndResumeStmt 14 processResolution

/-! ## `resume` in expression position binds the yielded value.

`x := resume(co)` exercises the expression-position arm. The result type
is `Unknown` at Stage 1 (LaurelTypes deliberately defers it to Stage 2);
this test only checks that the construct parses and resolves. -/

def resumeBindsResult := r"
coroutine producer(seed: int) yields (x: int)
{
  x := seed; yield
};

procedure driver(): int
  opaque
{
  var co: producer := producer(0);
  var z: int := 0;
  z := resume(co);
  return z
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ResumeBindsResult" resumeBindsResult 14 processResolution

/-! ## `resume(co, v)` sends a value into the coroutine.

Two-argument resume; the value `v` will, post-Stage-2, become the result
of the coroutine's most recent `yield` (Python `gen.send(v)` semantics). -/

def resumeWithSend := r"
coroutine echo() yields (x: int) resumes (y: int)
  requires y >= 0
{
  x := 0; yield
};

procedure driver()
  opaque
{
  var co: echo := echo();
  resume(co, 42)
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ResumeWithSend" resumeWithSend 14 processResolution

/-! ## Coroutine consumes the value sent by `resume(co, v)`.

The dual of `ResumeWithSend`: from the *coroutine's* side, the
expression form `z := yield` binds the resumed value `v` (per Python
`gen.send(v)` semantics) to a body-local name. The `resumes (y: U)`
clause names the value spec-side; the body sees it only through the
expression yield. -/

def coroutineConsumesResumed := r"
coroutine echo() yields (x: int) resumes (y: int)
  requires y >= 0
{
  var z: int := 0;
  z := yield;
  x := z + 1;
  yield
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "CoroutineConsumesResumed" coroutineConsumesResumed 14 processResolution

/-! ## `return e` is rejected inside a coroutine.

The only legal forms in a coroutine body are bare `return` (terminator)
and `x := e; yield` (value yield via the `yields` binding). `return e`
inside a coroutine resolves to a clear error. -/

def returnWithValueInCoroutine := r"
coroutine bad() yields (x: int)
{
  return 42
//^^^^^^^^^ error: return with a value is not allowed in a coroutine
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "ReturnWithValueInCoroutine" returnWithValueInCoroutine 14 processResolution

/-! ## Bare `return` is the legal coroutine terminator.

Bare `return` (no value) is the iterator shutdown form: the coroutine
transitions to Done and is no longer resumable. The motivating case is
early termination from inside a loop or conditional branch, which can't
be expressed cleanly via falloff. -/

def bareReturnInCoroutine := r"
coroutine countTo(limit: int) yields (x: int)
{
  var i: int := 0;
  while (i < limit)
    invariant i >= 0
  {
    if i > 100 then {
      return    // early termination from inside a nested branch
    };
    x := i;
    yield;
    i := i + 1
  }
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "BareReturnInCoroutine" bareReturnInCoroutine 14 processResolution

/-! ## Pipeline rejection: each coroutine triggers exactly one diagnostic.

Runs the full Laurel pipeline. `rejectCoroutines` is the first stage; the
program flows through unchanged after the diagnostic, so later passes
don't add noise. The annotation matches a substring of the full message
("coroutine 'empty' is parsed but not yet verified ..."). -/

def coroutineRejected := r"
coroutine empty()
//        ^^^^^ error: parsed but not yet verified
{
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "CoroutineRejected" coroutineRejected 14 processLaurelFile

end Strata.Laurel
