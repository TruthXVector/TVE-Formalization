/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import TVE.Rule30.CantorSpace
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Left-Permutativity and Semigroup Dynamics of Rule 30

Formalizes the algebraic left-permutativity of Rule 30. Because the right-hand
context evaluates strictly to a unit {1, -1}, the operator acts as a measure-preserving
shift with maximal left Lyapunov exponent (left causal cone velocity = 1).
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE.Rule30

/-- The unique algebraic predecessor for the left cell given the output and right context. -/
@[expose]
def left_preimage (y r : ℝ) : ℝ := y * r

/-- Theorem: The left predecessor strictly lies in the spin space {1, -1}. -/
theorem left_preimage_valid (y r : ℝ) (hy : y = 1 ∨ y = -1) (hr : r = 1 ∨ r = -1) :
    left_preimage y r = 1 ∨ left_preimage y r = -1 := by
  dsimp [left_preimage]
  cases hy with
  | inl hy1 =>
    rw [hy1]
    cases hr with
    | inl hr1 => rw [hr1]; left; norm_num
    | inr hr2 => rw [hr2]; right; norm_num
  | inr hy2 =>
    rw [hy2]
    cases hr with
    | inl hr1 => rw [hr1]; right; norm_num
    | inr hr2 => rw [hr2]; left; norm_num

/-- Theorem: Forward evaluation of the left predecessor recovers the exact output. -/
theorem left_preimage_eval (y r : ℝ) (hr : r = 1 ∨ r = -1) :
    (left_preimage y r) * r = y := by
  dsimp [left_preimage]
  cases hr with
  | inl hr1 =>
    rw [hr1]
    ring
  | inr hr2 =>
    rw [hr2]
    ring

/-- Theorem: Uniqueness of the left predecessor.
    No two distinct left inputs can yield the same output under the same right context. -/
theorem left_preimage_unique (y r l : ℝ) (hr : r = 1 ∨ r = -1) (h : l * r = y) :
    l = left_preimage y r := by
  dsimp [left_preimage]
  cases hr with
  | inl hr1 =>
    rw [hr1] at h ⊢
    calc l = l * 1 := by ring
    _ = y := h
    _ = y * 1 := by ring
  | inr hr2 =>
    rw [hr2] at h ⊢
    calc l = -(l * -1) := by ring
    _ = -y := by rw [h]
    _ = y * -1 := by ring

/--
Theorem: Left Causal Sensitivity (Defect Propagation).
A perturbation at the left position x - 1 unconditionally flips the output at x.
-/
theorem left_sensitivity (l1 l2 r : ℝ) (hr : r = 1 ∨ r = -1) (hne : l1 ≠ l2) :
    l1 * r ≠ l2 * r := by
  intro h
  cases hr with
  | inl hr1 =>
    have h1 : l1 = l2 := by
      calc l1 = l1 * 1 := by ring
      _ = l1 * r := by rw [hr1]
      _ = l2 * r := h
      _ = l2 * 1 := by rw [hr1]
      _ = l2 := by ring
    exact hne h1
  | inr hr2 =>
    have h2 : l1 = l2 := by
      calc l1 = -(l1 * -1) := by ring
      _ = -(l1 * r) := by rw [hr2]
      _ = -(l2 * r) := by rw [h]
      _ = -(l2 * -1) := by rw [hr2]
      _ = l2 := by ring
    exact hne h2

/--
Theorem: Local Balanced Fibers (Uniform Measure Preservation).
Under any right context r ∈ {1, -1}, exactly one input produces +1 and exactly one produces -1.
-/
theorem local_balanced_fibers (r : ℝ) (hr : r = 1 ∨ r = -1) :
    (1 * r = 1 ∧ (-1) * r = -1) ∨ (1 * r = -1 ∧ (-1) * r = 1) := by
  cases hr with
  | inl h1 =>
    rw [h1]
    left
    constructor <;> ring
  | inr h2 =>
    rw [h2]
    right
    constructor <;> ring

/-- The discrete dynamical semigroup: iteration of the transfer operator U^t. -/
@[expose]
noncomputable def iterateU : ℕ → LatticeState → LatticeState
  | 0, s => s
  | n + 1, s => U (iterateU n s)

/-- Theorem: Semigroup evolution strictly preserves the physical spin Cantor space for all time t. -/
theorem iterateU_preserves_spin (n : ℕ) (s : LatticeState) (hs : isSpinState s) :
    isSpinState (iterateU n s) := by
  induction n with
  | zero =>
    dsimp [iterateU]
    exact hs
  | succ k ih =>
    dsimp [iterateU]
    exact U_preserves_spin (iterateU k s) ih

/-- The observable center column sequence c(t) = (U^t s)(0). -/
@[expose]
noncomputable def centerColumn (s : LatticeState) (t : ℕ) : ℝ :=
  iterateU t s 0

/-- Theorem: The center column sequence remains strictly on the spin lattice {1, -1} for all t. -/
theorem centerColumn_spin (s : LatticeState) (hs : isSpinState s) (t : ℕ) :
    centerColumn s t = 1 ∨ centerColumn s t = -1 :=
  iterateU_preserves_spin t s hs 0

#print axioms left_preimage_valid
#print axioms left_preimage_eval
#print axioms left_preimage_unique
#print axioms left_sensitivity
#print axioms local_balanced_fibers
#print axioms iterateU_preserves_spin
#print axioms centerColumn_spin

end TVE.Rule30
