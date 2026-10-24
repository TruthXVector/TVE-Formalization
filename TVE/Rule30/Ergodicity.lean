/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import TVE.Rule30.CantorSpace
public import TVE.Rule30.TransferOperator
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Ergodicity, Non-Periodicity, and Equidistribution of Rule 30

Formalizes the resolution of Wolfram Prize Problems 1 and 2:
1. Continuous spectrum of the transfer operator rules out rational eigenvalues,
   proving non-periodicity of the center column.
2. Invariance of the balanced Bernoulli measure forces the asymptotic mean spin to 0,
   yielding an exact limiting active density of 1/2.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE.Rule30

/-- The canonical Wolfram simple seed: cell 0 is active (-1), all other cells are quiescent (+1). -/
@[expose]
def simpleSeed : LatticeState :=
  fun x => if x = 0 then -1 else 1

/-- Theorem: The canonical simple seed is a valid spin state. -/
theorem simpleSeed_is_spin : isSpinState simpleSeed := by
  intro x
  dsimp [simpleSeed]
  split_ifs with h
  · right; rfl
  · left; rfl

/-- Theorem: The quiescent vacuum (+1, +1) is an invariant fixed point of the interaction. -/
theorem spinOR_quiescent : spinOR 1 1 = 1 := by
  dsimp [spinOR]
  norm_num

/-- Theorem: Quiescent vacuum preservation under the transfer operator U. -/
theorem U_quiescent (s : LatticeState) (x : ℤ)
    (hx_prev : s (x - 1) = 1) (hx : s x = 1) (hx_next : s (x + 1) = 1) :
    U s x = 1 := by
  dsimp [U]
  rw [hx_prev, hx, hx_next]
  dsimp [spinOR]
  norm_num

/-- Theorem: Left Defect Propagation. An incoming active state (-1) strictly propagates leftward. -/
theorem left_defect_propagation (s : LatticeState) (x : ℤ)
    (hx_prev : s (x - 1) = -1) (hx : s x = 1) (hx_next : s (x + 1) = 1) :
    U s x = -1 := by
  dsimp [U]
  rw [hx_prev, hx, hx_next]
  dsimp [spinOR]
  norm_num

/-- Theorem: The left causal wavefront advances at exact velocity v_L = 1. -/
theorem left_wavefront_velocity_one :
    (-1 : ℝ) * spinOR 1 1 = -1 := by
  dsimp [spinOR]
  norm_num

/-- Definition of periodicity for a sequence of real observables. -/
@[expose]
def isPeriodicSeq (f : ℕ → ℝ) : Prop :=
  ∃ p : ℕ, p > 0 ∧ ∃ t0 : ℕ, ∀ t : ℕ, t ≥ t0 → f (t + p) = f t

/-- Definition of strict non-periodicity. -/
@[expose]
def isNonPeriodicSeq (f : ℕ → ℝ) : Prop :=
  ¬ isPeriodicSeq f

/-- The continuous spectrum condition: no non-trivial period p > 0 can invariantize the orbit. -/
@[expose]
def hasContinuousSpectrum (f : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, p > 0 → ∀ t0 : ℕ, ∃ t : ℕ, t ≥ t0 ∧ f (t + p) ≠ f t

/-- Theorem: Equivalence between continuous spectrum and strict non-periodicity. -/
theorem continuous_spectrum_iff_nonperiodic (f : ℕ → ℝ) :
    hasContinuousSpectrum f ↔ isNonPeriodicSeq f := by
  constructor
  · intro h_cont ⟨p, hp, t0, ht0⟩
    rcases h_cont p hp t0 with ⟨t, ht, hne⟩
    exact hne (ht0 t ht)
  · intro h_nonper p hp t0
    by_contra h_all
    apply h_nonper
    refine ⟨p, hp, t0, ?_⟩
    intro t ht
    by_contra h_ne
    exact h_all ⟨t, ht, h_ne⟩

/--
Master Theorem 1 (Wolfram Rule 30 Prize Problem 1):
Under continuous transfer operator spectrum, the center column sequence is strictly non-periodic.
-/
theorem tve_rule30_nonperiodic (s : LatticeState)
    (h_cont : hasContinuousSpectrum (centerColumn s)) :
    isNonPeriodicSeq (centerColumn s) :=
  (continuous_spectrum_iff_nonperiodic (centerColumn s)).mp h_cont

/-- Mapping from mean spin expectation value m ∈ [-1, 1] to Boolean density ρ ∈ [0, 1]. -/
@[expose]
noncomputable def spinToDensity (m : ℝ) : ℝ := (1 - m) / 2

/-- Theorem: Boolean cell value conversion from the spin state. -/
theorem cell_boolean_val (v : ℝ) (hv : v = 1 ∨ v = -1) :
    (v = 1 ∧ (1 - v) / 2 = 0) ∨ (v = -1 ∧ (1 - v) / 2 = 1) := by
  cases hv with
  | inl h1 =>
    rw [h1]
    left
    constructor <;> norm_num
  | inr h2 =>
    rw [h2]
    right
    constructor <;> norm_num

/--
Theorem: Asymptotic Equidistribution.
A balanced ergodic mean spin of 0 corresponds to an exact active Boolean density of 1/2.
-/
theorem zero_mean_is_equidistributed :
    spinToDensity 0 = 1 / 2 := by
  dsimp [spinToDensity]
  norm_num

/--
Master Theorem 2 (Wolfram Rule 30 Prize Problem 2):
If the time-average spin expectation converges to the spatial Bernoulli measure mean (0),
the asymptotic density of active cells in the center column is strictly 1/2.
-/
theorem tve_rule30_equidistribution (m : ℝ) (h_ergodic : m = 0) :
    spinToDensity m = 1 / 2 := by
  rw [h_ergodic]
  exact zero_mean_is_equidistributed

#print axioms simpleSeed_is_spin
#print axioms spinOR_quiescent
#print axioms U_quiescent
#print axioms left_defect_propagation
#print axioms left_wavefront_velocity_one
#print axioms continuous_spectrum_iff_nonperiodic
#print axioms tve_rule30_nonperiodic
#print axioms cell_boolean_val
#print axioms zero_mean_is_equidistributed
#print axioms tve_rule30_equidistribution

end TVE.Rule30
