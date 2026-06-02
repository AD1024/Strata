/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Sanity checks for Phase A coroutine elaboration: parse + resolve a
coroutine, run `elaborateCoroutines`, and pretty-print the resulting
program (state composite + `resume` method + spawn constructor).

These are `#eval` smoke tests — they exercise the transformation end to
end and pin the generated shape, so regressions in field naming, the
dispatch loop, contract placement, or constructor generation surface as
diff noise rather than silent miscompiles.
-/

meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import Strata.Languages.Laurel.Grammar
meta import Strata.Languages.Laurel.CoroutineElaboration
meta import Strata.Languages.Laurel.Resolution

meta section

open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Parse, resolve, and run Phase A coroutine elaboration. -/
def parseAndElaborate (input : String) : IO Program := do
  let inputCtx := StrataDDM.Parser.stringInputContext "test" input
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    pure (elaborateCoroutines result.model result.program)

/-- Print every type definition and static procedure of a program. -/
def printProgram (p : Program) : IO Unit := do
  for ty in p.types do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format ty)))
  for proc in p.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Empty coroutine: just the state composite + trivial resume + ctor. -/

def emptyCoroutine := r"
coroutine empty()
{
};
"

/--
info: composite emptyState { var $pc: intprocedure resume()
  requires this#$pc != 0
  opaque
while(true) if this#$pc == 1 then { {  }; this#$pc := 0 } else return {  }; }
procedure empty()
  returns ($co: emptyState)
  opaque
  ensures $co#$pc == 1
{ $co := new emptyState; $co#$pc := 1 };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate emptyCoroutine)

/-! ## Counter: a single yield inside a while loop (the canonical
state-split case — exercises loop head/body-end invariant asserts and
the dispatch loop). -/

def counterCoroutine := r"
coroutine counter() yields (x: int)
{
  var i: int := 0;
  while (i < 3)
    invariant i >= 0
  {
    x := i;
    yield;
    i := i + 1
  }
};
"

/--
info: composite counterState { var $pc: int var i: int var x: intprocedure resume()
  requires this#$pc != 0
  opaque
while(true) if this#$pc == 1 then { assert this#i >= 0; if this#i < 3 then this#$pc := 5 else this#$pc := 0 } else if this#$pc == 3 then { this#i := this#i + 1; assert this#i >= 0; this#$pc := 1 } else if this#$pc == 5 then { this#x := this#i; this#$pc := 3; return {  } } else if this#$pc == 6 then { this#i := 0; this#$pc := 1 } else return {  }; }
procedure counter()
  returns ($co: counterState)
  opaque
  ensures $co#$pc == 6
{ $co := new counterState; $co#$pc := 6 };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate counterCoroutine)

/-! ## Producer with input + construction precondition: checks the spawn
constructor carries `requires` verbatim and copies the input into a field. -/

def producerCoroutine := r"
coroutine producer(seed: int) yields (x: int)
  requires seed >= 0
{
  x := seed; yield;
  x := seed + 1; yield
};
"

/--
info: composite producerState { var $pc: int var seed: int var x: intprocedure resume()
  requires this#$pc != 0
  opaque
while(true) if this#$pc == 2 then { this#x := this#seed + 1; this#$pc := 0; return {  } } else if this#$pc == 4 then { this#x := this#seed; this#$pc := 2; return {  } } else return {  }; }
procedure producer(seed: int)
  returns ($co: producerState)
  requires seed >= 0
  opaque
  ensures $co#$pc == 4
  ensures $co#seed == seed
{ $co := new producerState; $co#$pc := 4; $co#seed := seed };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate producerCoroutine)

/-! ## Channel + rely/guarantee: checks relies → resume precondition,
guarantees → resume postcondition (unguarded). -/

def echoCoroutine := r"
coroutine echo() yields (x: int) resumes (y: int)
  relies y >= 0
  guarantees x >= 0
{
  x := 0; yield
};
"

/--
info: composite echoState { var $pc: int var x: intprocedure resume(y: int)
  requires this#$pc != 0
  requires y >= 0
  opaque
  ensures this#x >= 0
while(true) if this#$pc == 2 then { this#x := 0; this#$pc := 0; return {  } } else return {  }; }
procedure echo()
  returns ($co: echoState)
  opaque
  ensures $co#$pc == 2
{ $co := new echoState; $co#$pc := 2 };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate echoCoroutine)

/-! ## Bidirectional channel: the coroutine yields a value *out* via the
`yields` binding and receives a value *in* via `z := yield`, binding it to
a body-local that it then uses. This is the full duplex case — values flow
both directions across a single suspension.

  * `x := <expr>; ...; z := yield` — `x` is the outgoing value (a field),
    `z := yield` suspends and, on resume, binds the *incoming* value (the
    `v` from a driver's `resume(co, v)`) into the local `z`.
  * The incoming value is `resume`'s parameter `y` (from `resumes (y: int)`),
    read as a plain local — it is per-call data, not coroutine state.
  * `z` *is* promoted (it's a body local that lives across the yield), so
    the rebind writes `this#z := y`. -/

def duplexCoroutine := r"
coroutine adder() yields (out: int) resumes (inp: int)
{
  var total: int := 0;
  out := total;
  var z: int := yield;
  total := total + z;
  out := total;
  yield
};
"

/--
info: composite adderState { var $pc: int var total: int var z: int var out: intprocedure resume(inp: int)
  requires this#$pc != 0
  opaque
while(true) if this#$pc == 4 then { this#z := inp; this#total := this#total + this#z; this#out := this#total; this#$pc := 0; return {  } } else if this#$pc == 7 then { this#total := 0; this#out := this#total; this#$pc := 4; return {  } } else return {  }; }
procedure adder()
  returns ($co: adderState)
  opaque
  ensures $co#$pc == 7
{ $co := new adderState; $co#$pc := 7 };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate duplexCoroutine)

/-! ## Combined control flow: a `while` loop whose body contains an
`if`/`else`, with a `yield` in each branch. Exercises the interaction of
the loop-split (head / bodyEnd / back-edge) with the branch-split
(dispatch state → per-branch entry → merge), and confirms both branches'
yields produce distinct suspend states that re-converge at the loop's
bodyEnd. -/

def branchingLoop := r"
coroutine sieve(limit: int) yields (out: int)
{
  var i: int := 0;
  while (i < limit)
    invariant i >= 0
  {
    if i % 2 == 0 then {
      out := i;
      yield
    } else {
      out := 0 - i;
      yield
    };
    i := i + 1
  }
};
"

/--
info: composite sieveState { var $pc: int var limit: int var i: int var out: intprocedure resume()
  requires this#$pc != 0
  opaque
while(true) if this#$pc == 1 then { assert this#i >= 0; if this#i < this#limit then this#$pc := 8 else this#$pc := 0 } else if this#$pc == 3 then { this#i := this#i + 1; assert this#i >= 0; this#$pc := 1 } else if this#$pc == 5 then { this#out := this#i; this#$pc := 3; return {  } } else if this#$pc == 7 then { this#out := 0 - this#i; this#$pc := 3; return {  } } else if this#$pc == 8 then if this#i % 2 == 0 then this#$pc := 5 else this#$pc := 7 else if this#$pc == 9 then { this#i := 0; this#$pc := 1 } else return {  }; }
procedure sieve(limit: int)
  returns ($co: sieveState)
  opaque
  ensures $co#$pc == 9
  ensures $co#limit == limit
{ $co := new sieveState; $co#$pc := 9; $co#limit := limit };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate branchingLoop)

/-! ## Stress: nested loops, each with its own yield. The inner loop's
back-edge must not be confused with the outer's; the inner exit must
flow to the outer body's continuation. -/

def nestedLoops := r"
coroutine grid(rows: int, cols: int) yields (cell: int)
{
  var r: int := 0;
  while (r < rows)
    invariant r >= 0
  {
    var c: int := 0;
    while (c < cols)
      invariant c >= 0
    {
      cell := r * cols + c;
      yield;
      c := c + 1
    };
    r := r + 1
  }
};
"

/--
info: composite gridState { var $pc: int var rows: int var cols: int var r: int var c: int var cell: intprocedure resume()
  requires this#$pc != 0
  opaque
while(true) if this#$pc == 1 then { assert this#r >= 0; if this#r < this#rows then this#$pc := 9 else this#$pc := 0 } else if this#$pc == 3 then { this#r := this#r + 1; assert this#r >= 0; this#$pc := 1 } else if this#$pc == 4 then { assert this#c >= 0; if this#c < this#cols then this#$pc := 8 else this#$pc := 3 } else if this#$pc == 6 then { this#c := this#c + 1; assert this#c >= 0; this#$pc := 4 } else if this#$pc == 8 then { this#cell := this#r * this#cols + this#c; this#$pc := 6; return {  } } else if this#$pc == 9 then { this#c := 0; this#$pc := 4 } else if this#$pc == 10 then { this#r := 0; this#$pc := 1 } else return {  }; }
procedure grid(rows: int, cols: int)
  returns ($co: gridState)
  opaque
  ensures $co#$pc == 10
  ensures $co#rows == rows
  ensures $co#cols == cols
{ $co := new gridState; $co#$pc := 10; $co#rows := rows; $co#cols := cols };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate nestedLoops)

/-! ## Stress: nested conditionals with a yield only in the innermost
then-branch (asymmetric — the else paths fall through with no yield).
Exercises branch-merge where some branches are pure transitions. -/

def nestedIf := r"
coroutine classify(x: int) yields (tag: int)
{
  if x > 0 then {
    if x > 10 then {
      tag := 2;
      yield
    } else {
      tag := 1
    }
  } else {
    tag := 0
  };
  tag := 0 - 1;
  yield
};
"

/--
info: composite classifyState { var $pc: int var x: int var tag: intprocedure resume()
  requires this#$pc != 0
  opaque
while(true) if this#$pc == 2 then { this#tag := 0 - 1; this#$pc := 0; return {  } } else if this#$pc == 4 then { this#tag := 2; this#$pc := 2; return {  } } else if this#$pc == 5 then { { this#tag := 1 }; this#$pc := 2 } else if this#$pc == 6 then if this#x > 10 then this#$pc := 4 else this#$pc := 5 else if this#$pc == 7 then { { this#tag := 0 }; this#$pc := 2 } else if this#$pc == 8 then if this#x > 0 then this#$pc := 6 else this#$pc := 7 else return {  }; }
procedure classify(x: int)
  returns ($co: classifyState)
  opaque
  ensures $co#$pc == 8
  ensures $co#x == x
{ $co := new classifyState; $co#$pc := 8; $co#x := x };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate nestedIf)

/-! ## Stress: a yield-free inner loop nested inside a yielding outer
loop. The inner loop has no yield, so it must stay a single coalesced
state (an ordinary `while`), not fragment into dispatch arms. -/

def yieldFreeInner := r"
coroutine summer(n: int) yields (running: int)
{
  var total: int := 0;
  var i: int := 0;
  while (i < n)
    invariant i >= 0
  {
    var j: int := 0;
    while (j < i)
      invariant j >= 0
    {
      total := total + j;
      j := j + 1
    };
    running := total;
    yield;
    i := i + 1
  }
};
"

/--
info: composite summerState { var $pc: int var n: int var total: int var i: int var j: int var running: intprocedure resume()
  requires this#$pc != 0
  opaque
while(true) if this#$pc == 1 then { assert this#i >= 0; if this#i < this#n then this#$pc := 7 else this#$pc := 0 } else if this#$pc == 3 then { this#i := this#i + 1; assert this#i >= 0; this#$pc := 1 } else if this#$pc == 7 then { this#j := 0; while(this#j < this#i)
  invariant this#j >= 0 { this#total := this#total + this#j; this#j := this#j + 1 }; this#running := this#total; this#$pc := 3; return {  } } else if this#$pc == 9 then { this#total := 0; this#i := 0; this#$pc := 1 } else return {  }; }
procedure summer(n: int)
  returns ($co: summerState)
  opaque
  ensures $co#$pc == 9
  ensures $co#n == n
{ $co := new summerState; $co#$pc := 9; $co#n := n };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate yieldFreeInner)

/-! ## Stress: two yields in sequence inside one if-branch, plus a
trailing yield after the if. Exercises a chain of suspends within a
single branch and re-convergence. -/

def multiYieldBranch := r"
coroutine pulse(flag: bool) yields (beat: int)
{
  if flag then {
    beat := 1;
    yield;
    beat := 2;
    yield
  } else {
    beat := 0
  };
  beat := 9;
  yield
};
"

/--
info: composite pulseState { var $pc: int var flag: bool var beat: intprocedure resume()
  requires this#$pc != 0
  opaque
while(true) if this#$pc == 2 then { this#beat := 9; this#$pc := 0; return {  } } else if this#$pc == 4 then { this#beat := 2; this#$pc := 2; return {  } } else if this#$pc == 6 then { this#beat := 1; this#$pc := 4; return {  } } else if this#$pc == 7 then { { this#beat := 0 }; this#$pc := 2 } else if this#$pc == 8 then if this#flag then this#$pc := 6 else this#$pc := 7 else return {  }; }
procedure pulse(flag: bool)
  returns ($co: pulseState)
  opaque
  ensures $co#$pc == 8
  ensures $co#flag == flag
{ $co := new pulseState; $co#$pc := 8; $co#flag := flag };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate multiYieldBranch)

end Strata.Laurel
end
