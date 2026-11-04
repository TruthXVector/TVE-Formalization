/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import TVE.Complexity.CookLevinBridge

/-!
# Inductive Boolean Circuit to 3-SAT Tseitin Compiler Bridge

Replaces the scalar `3 * G` clause-count definition with an executable
inductive boolean circuit compiler:
1. Defines inductive fan-in-2 boolean logic gates (`GateOp`,
   `CircuitGate`), literals (`Literal`), and 3-SAT clauses (`Clause3`).
2. Implements the executable Tseitin reduction `compileTseitin` and
   proves by structural induction on `gates : List CircuitGate` that
   `(compileTseitin gates).length = 3 * gates.length`.
3. Proves boolean soundness and completeness: a variable assignment
   satisfies the compiled 3-SAT formula if and only if every gate
   output matches its boolean gate operation.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

public section

namespace TVE

/-- Fan-in-2 boolean logic gate operations (including universal NAND). -/
inductive GateOp where
  | andOp  : GateOp
  | orOp   : GateOp
  | nandOp : GateOp

/-- A single fan-in-2 logic gate with input wires `in1, in2` and output `outVar`. -/
structure CircuitGate where
  op     : GateOp
  in1    : ℕ
  in2    : ℕ
  outVar : ℕ

/-- A boolean literal `(varIdx, isPos)` in a 3-SAT clause. -/
structure Literal where
  varIdx : ℕ
  isPos  : Bool

/-- A 3-SAT clause consisting of exactly three boolean literals. -/
structure Clause3 where
  lit1 : Literal
  lit2 : Literal
  lit3 : Literal

/-- Evaluates a single boolean literal under a wire assignment `assign : ℕ → Bool`. -/
@[expose]
def evalLiteral (l : Literal) (assign : ℕ → Bool) : Bool :=
  match l.isPos with
  | true  => assign l.varIdx
  | false => !(assign l.varIdx)

/-- Evaluates a 3-SAT disjunction `l1 ∨ l2 ∨ l3` under `assign`. -/
@[expose]
def evalClause3 (c : Clause3) (assign : ℕ → Bool) : Bool :=
  evalLiteral c.lit1 assign ||
  evalLiteral c.lit2 assign ||
  evalLiteral c.lit3 assign

/-- Evaluates a conjunction of 3-SAT clauses under `assign`. -/
@[expose]
def evalClauseList : List Clause3 → (ℕ → Bool) → Bool
  | [], _ => true
  | c :: cs, assign => evalClause3 c assign && evalClauseList cs assign

/-- Evaluates whether a single gate's output wire equals its boolean gate function. -/
@[expose]
def evalGateSpec (g : CircuitGate) (assign : ℕ → Bool) : Bool :=
  match g.op with
  | GateOp.andOp  => assign g.outVar == (assign g.in1 && assign g.in2)
  | GateOp.orOp   => assign g.outVar == (assign g.in1 || assign g.in2)
  | GateOp.nandOp => assign g.outVar == !(assign g.in1 && assign g.in2)

/-- Evaluates whether all gates in a circuit satisfy their boolean gate equations. -/
@[expose]
def evalCircuitSpec : List CircuitGate → (ℕ → Bool) → Bool
  | [], _ => true
  | g :: gs, assign => evalGateSpec g assign && evalCircuitSpec gs assign

/--
Compiles a single fan-in-2 logic gate `g` into its exact 3-clause Tseitin
3-SAT representation.
-/
@[expose]
def gateToClauses (g : CircuitGate) : List Clause3 :=
  match g.op with
  | GateOp.andOp =>
    [ { lit1 := ⟨g.in1, false⟩, lit2 := ⟨g.in2, false⟩, lit3 := ⟨g.outVar, true⟩ },
      { lit1 := ⟨g.in1, true⟩,  lit2 := ⟨g.in1, true⟩,  lit3 := ⟨g.outVar, false⟩ },
      { lit1 := ⟨g.in2, true⟩,  lit2 := ⟨g.in2, true⟩,  lit3 := ⟨g.outVar, false⟩ } ]
  | GateOp.orOp =>
    [ { lit1 := ⟨g.in1, true⟩,  lit2 := ⟨g.in2, true⟩,  lit3 := ⟨g.outVar, false⟩ },
      { lit1 := ⟨g.in1, false⟩, lit2 := ⟨g.in1, false⟩, lit3 := ⟨g.outVar, true⟩ },
      { lit1 := ⟨g.in2, false⟩, lit2 := ⟨g.in2, false⟩, lit3 := ⟨g.outVar, true⟩ } ]
  | GateOp.nandOp =>
    [ { lit1 := ⟨g.in1, false⟩, lit2 := ⟨g.in2, false⟩, lit3 := ⟨g.outVar, false⟩ },
      { lit1 := ⟨g.in1, true⟩,  lit2 := ⟨g.in1, true⟩,  lit3 := ⟨g.outVar, true⟩ },
      { lit1 := ⟨g.in2, true⟩,  lit2 := ⟨g.in2, true⟩,  lit3 := ⟨g.outVar, true⟩ } ]

/--
Executable Tseitin circuit-to-3SAT compiler mapping a list of logic gates
to its 3-SAT CNF tableau.
-/
@[expose]
def compileTseitin : List CircuitGate → List Clause3
  | [] => []
  | g :: rest => gateToClauses g ++ compileTseitin rest

/-- Lemma: Every individual gate compiles to exactly 3 clauses. -/
theorem gateToClauses_length (g : CircuitGate) :
    (gateToClauses g).length = 3 := by
  rcases g with ⟨op, in1, in2, outVar⟩
  cases op <;> rfl

/--
Theorem (Structural Induction Proof of the \(3G\) Tseitin Clause Count):
For any boolean circuit `gates : List CircuitGate`, the compiled 3-SAT
tableau contains exactly `3 * gates.length` clauses.
-/
theorem compileTseitin_length (gates : List CircuitGate) :
    (compileTseitin gates).length = 3 * gates.length := by
  induction gates with
  | nil => rfl
  | cons g rest ih =>
    dsimp [compileTseitin]
    rw [List.length_append, gateToClauses_length g, ih]
    ring

/-- Lemma: Evaluation of concatenated 3-SAT clause lists distributes over `&&`. -/
theorem evalClauseList_append (L1 L2 : List Clause3) (assign : ℕ → Bool) :
    evalClauseList (L1 ++ L2) assign =
      (evalClauseList L1 assign && evalClauseList L2 assign) := by
  induction L1 with
  | nil => rfl
  | cons c rest ih =>
    dsimp [evalClauseList]
    rw [ih]
    cases (evalClause3 c assign) <;>
      cases (evalClauseList rest assign) <;>
      cases (evalClauseList L2 assign) <;> rfl

/--
Theorem (Single-Gate Tseitin Truth-Table Equisatisfiability):
For every gate `g : CircuitGate` and wire assignment `assign : ℕ → Bool`,
the 3 emitted Tseitin clauses evaluate to `true` if and only if the gate
output wire matches the boolean gate operation.
-/
theorem gate_clauses_iff_gate_spec (g : CircuitGate) (assign : ℕ → Bool) :
    evalClauseList (gateToClauses g) assign = evalGateSpec g assign := by
  rcases g with ⟨op, in1, in2, outVar⟩
  cases op <;>
    dsimp [gateToClauses, evalClauseList, evalClause3, evalLiteral, evalGateSpec] <;>
    cases (assign in1) <;> cases (assign in2) <;> cases (assign outVar) <;> rfl

/--
Theorem (Global Inductive Soundness & Completeness of the Tseitin Compiler):
For any boolean circuit `gates : List CircuitGate` and wire assignment
`assign : ℕ → Bool`, the compiled 3-SAT tableau `compileTseitin gates`
evaluates to `true` if and only if every gate in `gates` satisfies its
boolean truth table.
-/
theorem compileTseitin_sound_and_complete
    (gates : List CircuitGate) (assign : ℕ → Bool) :
    evalClauseList (compileTseitin gates) assign =
      evalCircuitSpec gates assign := by
  induction gates with
  | nil => rfl
  | cons g rest ih =>
    dsimp [compileTseitin, evalCircuitSpec]
    rw [evalClauseList_append, gate_clauses_iff_gate_spec, ih]

/--
Theorem (Bridge from Inductive Compiler Length to `tseitinClauseCount`):
The cast real length `((compileTseitin gates).length : ℝ)` of the compiled
3-SAT tableau identically matches `tseitinClauseCount (gates.length : ℝ)`.
-/
theorem inductive_compiler_matches_tseitinClauseCount
    (gates : List CircuitGate) :
    ((compileTseitin gates).length : ℝ) =
      tseitinClauseCount (gates.length : ℝ) := by
  rw [compileTseitin_length]
  dsimp [tseitinClauseCount]
  push_cast
  ring

#print axioms gateToClauses_length
#print axioms compileTseitin_length
#print axioms gate_clauses_iff_gate_spec
#print axioms compileTseitin_sound_and_complete
#print axioms inductive_compiler_matches_tseitinClauseCount

end TVE
