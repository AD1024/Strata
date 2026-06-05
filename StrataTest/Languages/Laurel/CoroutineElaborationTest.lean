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
info: composite emptyState { var $pc: intprocedure resume(self: emptyState)
  requires self#$pc != 0
  opaque
while(true) if self#$pc == 1 then { {  }; self#$pc := 0 } else return {  }; }
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
info: composite counterState { var $pc: int var i: int var x: intprocedure resume(self: counterState)
  requires self#$pc != 0
  opaque
while(true) if self#$pc == 1 then { assert self#i >= 0; if self#i < 3 then self#$pc := 5 else self#$pc := 0 } else if self#$pc == 3 then { self#i := self#i + 1; assert self#i >= 0; self#$pc := 1 } else if self#$pc == 5 then { self#x := self#i; self#$pc := 3; return {  } } else if self#$pc == 6 then { self#i := 0; self#$pc := 1 } else return {  }; }
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
info: composite producerState { var $pc: int var seed: int var x: intprocedure resume(self: producerState)
  requires self#$pc != 0
  opaque
while(true) if self#$pc == 2 then { self#x := self#seed + 1; self#$pc := 0; return {  } } else if self#$pc == 4 then { self#x := self#seed; self#$pc := 2; return {  } } else return {  }; }
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
info: composite echoState { var $pc: int var x: intprocedure resume(self: echoState, y: int)
  requires self#$pc != 0
  requires y >= 0
  opaque
  ensures self#x >= 0
while(true) if self#$pc == 2 then { self#x := 0; self#$pc := 0; return {  } } else return {  }; }
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
    the rebind writes `self#z := y`. -/

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
info: composite adderState { var $pc: int var total: int var z: int var out: intprocedure resume(self: adderState, inp: int)
  requires self#$pc != 0
  opaque
while(true) if self#$pc == 4 then { self#z := inp; self#total := self#total + self#z; self#out := self#total; self#$pc := 0; return {  } } else if self#$pc == 7 then { self#total := 0; self#out := self#total; self#$pc := 4; return {  } } else return {  }; }
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
info: composite sieveState { var $pc: int var limit: int var i: int var out: intprocedure resume(self: sieveState)
  requires self#$pc != 0
  opaque
while(true) if self#$pc == 1 then { assert self#i >= 0; if self#i < self#limit then self#$pc := 8 else self#$pc := 0 } else if self#$pc == 3 then { self#i := self#i + 1; assert self#i >= 0; self#$pc := 1 } else if self#$pc == 5 then { self#out := self#i; self#$pc := 3; return {  } } else if self#$pc == 7 then { self#out := 0 - self#i; self#$pc := 3; return {  } } else if self#$pc == 8 then if self#i % 2 == 0 then self#$pc := 5 else self#$pc := 7 else if self#$pc == 9 then { self#i := 0; self#$pc := 1 } else return {  }; }
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
info: composite gridState { var $pc: int var rows: int var cols: int var r: int var c: int var cell: intprocedure resume(self: gridState)
  requires self#$pc != 0
  opaque
while(true) if self#$pc == 1 then { assert self#r >= 0; if self#r < self#rows then self#$pc := 9 else self#$pc := 0 } else if self#$pc == 3 then { self#r := self#r + 1; assert self#r >= 0; self#$pc := 1 } else if self#$pc == 4 then { assert self#c >= 0; if self#c < self#cols then self#$pc := 8 else self#$pc := 3 } else if self#$pc == 6 then { self#c := self#c + 1; assert self#c >= 0; self#$pc := 4 } else if self#$pc == 8 then { self#cell := self#r * self#cols + self#c; self#$pc := 6; return {  } } else if self#$pc == 9 then { self#c := 0; self#$pc := 4 } else if self#$pc == 10 then { self#r := 0; self#$pc := 1 } else return {  }; }
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
info: composite classifyState { var $pc: int var x: int var tag: intprocedure resume(self: classifyState)
  requires self#$pc != 0
  opaque
while(true) if self#$pc == 2 then { self#tag := 0 - 1; self#$pc := 0; return {  } } else if self#$pc == 4 then { self#tag := 2; self#$pc := 2; return {  } } else if self#$pc == 5 then { { self#tag := 1 }; self#$pc := 2 } else if self#$pc == 6 then if self#x > 10 then self#$pc := 4 else self#$pc := 5 else if self#$pc == 7 then { { self#tag := 0 }; self#$pc := 2 } else if self#$pc == 8 then if self#x > 0 then self#$pc := 6 else self#$pc := 7 else return {  }; }
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
info: composite summerState { var $pc: int var n: int var total: int var i: int var j: int var running: intprocedure resume(self: summerState)
  requires self#$pc != 0
  opaque
while(true) if self#$pc == 1 then { assert self#i >= 0; if self#i < self#n then self#$pc := 7 else self#$pc := 0 } else if self#$pc == 3 then { self#i := self#i + 1; assert self#i >= 0; self#$pc := 1 } else if self#$pc == 7 then { self#j := 0; while(self#j < self#i)
  invariant self#j >= 0 { self#total := self#total + self#j; self#j := self#j + 1 }; self#running := self#total; self#$pc := 3; return {  } } else if self#$pc == 9 then { self#total := 0; self#i := 0; self#$pc := 1 } else return {  }; }
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
info: composite pulseState { var $pc: int var flag: bool var beat: intprocedure resume(self: pulseState)
  requires self#$pc != 0
  opaque
while(true) if self#$pc == 2 then { self#beat := 9; self#$pc := 0; return {  } } else if self#$pc == 4 then { self#beat := 2; self#$pc := 2; return {  } } else if self#$pc == 6 then { self#beat := 1; self#$pc := 4; return {  } } else if self#$pc == 7 then { { self#beat := 0 }; self#$pc := 2 } else if self#$pc == 8 then if self#flag then self#$pc := 6 else self#$pc := 7 else return {  }; }
procedure pulse(flag: bool)
  returns ($co: pulseState)
  opaque
  ensures $co#$pc == 8
  ensures $co#flag == flag
{ $co := new pulseState; $co#$pc := 8; $co#flag := flag };
-/
#guard_msgs in
#eval! do printProgram (← parseAndElaborate multiYieldBranch)

/-! ## Caller-side rewrite: `co: c` → `co: cState`, `resume(co[, v])` →
`co#resume([v])` (an `InstanceCall`). -/

def printProcsNamed (p : Program) (name : String) : IO Unit := do
  for proc in p.staticProcedures do
    if proc.name.text == name then
      IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ### Spawn + statement-position `resume(co)`. -/

def spawnAndResume := r"
coroutine producer(seed: int) yields (x: int)
{
  x := seed; yield
};

procedure driver()
  opaque
{
  var co: producer := producer(0);
  resume(co)
};
"

/--
info: procedure driver()
  opaque
{ var co: producerState := producer(0); co#resume() };
-/
#guard_msgs in
#eval! do printProcsNamed (← parseAndElaborate spawnAndResume) "driver"

/-! ### Expression-position `z := resume(co)` and statement-position
`resume(co, v)` with a send value. -/

def resumeWithSendDriver := r"
coroutine echo() yields (x: int) resumes (y: int)
  requires y >= 0
{
  x := 0; yield
};

procedure driver(): int
  opaque
{
  var co: echo := echo();
  var z: int := 0;
  z := resume(co);
  resume(co, 42);
  return z
};
"

/--
info: procedure driver(): int
  opaque
{ var co: echoState := echo(); var z: int := 0; z := co#resume(); co#resume(42); return z };
-/
#guard_msgs in
#eval! do printProcsNamed (← parseAndElaborate resumeWithSendDriver) "driver"

end Strata.Laurel
end
