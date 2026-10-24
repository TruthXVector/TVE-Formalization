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
public import Mathlib.Tactic.NormNum

/-!
# Cantor Space and Rule 30 Transfer Operator

Embeds the discrete {0, 1} cellular automaton into the continuous real field.
By mapping boolean states to spin states {1, -1}, Rule 30 becomes a non-linear
transfer operator U on a subset of the infinite-dimensional space ℝ^ℤ.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE.Rule30

/-- The state of the entire 1D lattice mapped into the continuous real field. -/
@[expose]
def LatticeState := ℤ → ℝ

/-- A state is valid if every cell strictly takes spin values +1 (False) or -1 (True). -/
@[expose]
def isSpinState (s : LatticeState) : Prop :=
  ∀ x : ℤ, s x = 1 ∨ s x = -1

/-- Algebraic translation of XOR (Addition mod 2). -/
@[expose]
def spinXOR (a b : ℝ) : ℝ := a * b

/-- Algebraic translation of OR.
    Using the isomorphic mapping: False = 1, True = -1. -/
@[expose]
noncomputable def spinOR (a b : ℝ) : ℝ := (-1 + a + b + a * b) / 2

/-- Theorem: The algebraic OR operator is strictly closed on the spin set {1, -1}. -/
theorem spinOR_closed (a b : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    spinOR a b = 1 ∨ spinOR a b = -1 := by
  dsimp [spinOR]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rw [ha, hb]; left; norm_num
  · rw [ha, hb]; right; norm_num
  · rw [ha, hb]; right; norm_num
  · rw [ha, hb]; right; norm_num

/-- The continuous Transfer Operator U for Rule 30. -/
@[expose]
noncomputable def U (s : LatticeState) : LatticeState :=
  fun x => s (x - 1) * spinOR (s x) (s (x + 1))

/-- Theorem: The continuous Transfer Operator U perfectly preserves the discrete spin Cantor space.
    Proves that evolving the system algebraically never breaks the {1, -1} physical constraint. -/
theorem U_preserves_spin (s : LatticeState) (hs : isSpinState s) :
    isSpinState (U s) := by
  intro x
  dsimp [U]
  have hl := hs (x - 1)
  have hr := spinOR_closed (s x) (s (x + 1)) (hs x) (hs (x + 1))
  cases hl with
  | inl h1 =>
    rw [h1]
    cases hr with
    | inl h2 =>
      rw [h2]
      left
      norm_num
    | inr h2 =>
      rw [h2]
      right
      norm_num
  | inr h1 =>
    rw [h1]
    cases hr with
    | inl h2 =>
      rw [h2]
      right
      norm_num
    | inr h2 =>
      rw [h2]
      left
      norm_num

#print axioms spinOR_closed
#print axioms U_preserves_spin

end TVE.Rule30
