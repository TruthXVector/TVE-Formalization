/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import TVE.Complexity.TopologicalFrustration

/-!
# Lumer-Phillips Contraction and Kramers Search Inversion Duality

Formalizes the duality between forward verification contraction
\(D_{\mathrm{fwd}}(\gamma, r) = e^{-\gamma r}\) and backward witness search
inversion \(S_{\mathrm{search}}(\gamma, r) = e^{+\gamma r}\) across frustrated
cycle rank \(r\). Proves the exact reciprocal identity
\(D_{\mathrm{fwd}} \cdot S_{\mathrm{search}} = 1\) and the strict separation
\(0 < D_{\mathrm{fwd}} < 1 < S_{\mathrm{search}}\) for all \(\gamma, r > 0\).
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/--
Forward verification dissipative contraction factor across cycle rank \(r\):
\(D_{\mathrm{fwd}}(\gamma, r) = e^{-\gamma r}\).
-/
@[expose]
noncomputable def forwardContraction (gamma r : ℝ) : ℝ :=
  Real.exp (-gamma * r)

/--
Backward Kramers witness search multiplier across cycle rank \(r\):
\(S_{\mathrm{search}}(\gamma, r) = e^{+\gamma r}\).
-/
@[expose]
noncomputable def backwardSearchMultiplier (gamma r : ℝ) : ℝ :=
  Real.exp (gamma * r)

/--
Theorem: Exact Semigroup Reciprocal Duality Identity.
The product of the forward verification contraction and backward search
expansion is identically \(1\) for all \(\gamma, r \in \mathbb{R}\).
-/
theorem semigroup_reciprocal_duality (gamma r : ℝ) :
    forwardContraction gamma r * backwardSearchMultiplier gamma r = 1 := by
  dsimp [forwardContraction, backwardSearchMultiplier]
  rw [← Real.exp_add]
  have h_cancel : -gamma * r + gamma * r = 0 := by ring
  rw [h_cancel, Real.exp_zero]

/--
Theorem: Strict Contraction of Forward Verification on Frustrated Graphs.
For \(\gamma > 0\) and cycle rank \(r > 0\), \(0 < D_{\mathrm{fwd}}(\gamma, r) < 1\).
-/
theorem forward_contraction_strict_bounds (gamma r : ℝ)
    (h_gamma : gamma > 0) (hr : r > 0) :
    0 < forwardContraction gamma r ∧ forwardContraction gamma r < 1 := by
  dsimp [forwardContraction]
  refine ⟨Real.exp_pos (-gamma * r), ?_⟩
  rw [Real.exp_lt_one_iff]
  have h_prod : 0 < gamma * r := mul_pos h_gamma hr
  linarith

/--
Theorem: Strict Expansion of Backward Witness Search.
For \(\gamma > 0\) and cycle rank \(r > 0\), \(1 < S_{\mathrm{search}}(\gamma, r)\).
-/
theorem backward_search_strictly_expansive (gamma r : ℝ)
    (h_gamma : gamma > 0) (hr : r > 0) :
    1 < backwardSearchMultiplier gamma r := by
  have h_fwd := forward_contraction_strict_bounds gamma r h_gamma hr
  have h_rec := semigroup_reciprocal_duality gamma r
  by_contra h_not
  have h_le : backwardSearchMultiplier gamma r ≤ 1 := by linarith
  have h_mul : forwardContraction gamma r * backwardSearchMultiplier gamma r ≤
      forwardContraction gamma r * 1 :=
    mul_le_mul_of_nonneg_left h_le (le_of_lt h_fwd.1)
  linarith

/--
Theorem: Forward-vs-Backward Semigroup Separation Sandwich.
For all \(\gamma > 0\) and \(r > 0\):
\(0 < D_{\mathrm{fwd}}(\gamma, r) < 1 < S_{\mathrm{search}}(\gamma, r)\).
-/
theorem forward_contraction_vs_search_expansion (gamma r : ℝ)
    (h_gamma : gamma > 0) (hr : r > 0) :
    0 < forwardContraction gamma r ∧
    forwardContraction gamma r < 1 ∧
    1 < backwardSearchMultiplier gamma r := by
  have h_fwd := forward_contraction_strict_bounds gamma r h_gamma hr
  have h_bwd := backward_search_strictly_expansive gamma r h_gamma hr
  exact ⟨h_fwd.1, h_fwd.2, h_bwd⟩

/--
Theorem: Monotonicity of Search Complexity Under ETH Core Compression.
If syntactic preprocessing compresses a graph to an effective frustrated cycle
rank \(0 < r_{\mathrm{eff}} \le r_{\mathrm{raw}}\), the compressed search
multiplier remains strictly expansive (\(1 < S_{\mathrm{search}}(\gamma, r_{\mathrm{eff}})\))
and bounded above by the raw multiplier.
-/
theorem eth_compression_preserves_search_barrier
    (gamma r_eff r_raw : ℝ)
    (h_gamma : gamma > 0) (hr_eff : r_eff > 0) (h_comp : r_eff ≤ r_raw) :
    1 < backwardSearchMultiplier gamma r_eff ∧
    backwardSearchMultiplier gamma r_eff ≤ backwardSearchMultiplier gamma r_raw ∧
    forwardContraction gamma r_raw ≤ forwardContraction gamma r_eff := by
  have h_exp_eff := backward_search_strictly_expansive gamma r_eff h_gamma hr_eff
  have h_diff_nonneg : 0 ≤ gamma * (r_raw - r_eff) := by
    have h_sub : 0 ≤ r_raw - r_eff := by linarith
    exact mul_nonneg (le_of_lt h_gamma) h_sub
  have h_exp_diff_le_one : Real.exp (-gamma * (r_raw - r_eff)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have h_bwd_raw_pos : 0 ≤ backwardSearchMultiplier gamma r_raw := by
    dsimp [backwardSearchMultiplier]
    exact le_of_lt (Real.exp_pos _)
  have h_fwd_eff_pos : 0 ≤ forwardContraction gamma r_eff := by
    dsimp [forwardContraction]
    exact le_of_lt (Real.exp_pos _)
  refine ⟨h_exp_eff, ?_, ?_⟩
  · have h_mul : Real.exp (-gamma * (r_raw - r_eff)) * backwardSearchMultiplier gamma r_raw ≤
        1 * backwardSearchMultiplier gamma r_raw :=
      mul_le_mul_of_nonneg_right h_exp_diff_le_one h_bwd_raw_pos
    have h_id : Real.exp (-gamma * (r_raw - r_eff)) * backwardSearchMultiplier gamma r_raw =
        backwardSearchMultiplier gamma r_eff := by
      dsimp [backwardSearchMultiplier]
      rw [← Real.exp_add]
      congr 1
      ring
    linarith
  · have h_mul : Real.exp (-gamma * (r_raw - r_eff)) * forwardContraction gamma r_eff ≤
        1 * forwardContraction gamma r_eff :=
      mul_le_mul_of_nonneg_right h_exp_diff_le_one h_fwd_eff_pos
    have h_id : Real.exp (-gamma * (r_raw - r_eff)) * forwardContraction gamma r_eff =
        forwardContraction gamma r_raw := by
      dsimp [forwardContraction]
      rw [← Real.exp_add]
      congr 1
      ring
    linarith

#print axioms semigroup_reciprocal_duality
#print axioms forward_contraction_strict_bounds
#print axioms backward_search_strictly_expansive
#print axioms forward_contraction_vs_search_expansion
#print axioms eth_compression_preserves_search_barrier

end TVE
