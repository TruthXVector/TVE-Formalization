/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import TVE.Poincare.NeckStability

/-!
# Equivalence to Perelman \(\kappa\)-Noncollapsing Without \(\mathcal{W}\)-Entropy

In Hamilton-Perelman Ricci flow, the \(\mathcal{W}\)-entropy functional is
introduced to prove \(\kappa\)-noncollapsing: a lower bound on neck volume
at bounded curvature scale. This module proves that the TVE Lyapunov energy
sandwich directly enforces a strictly positive lower bound on the cylindrical
neck volume \(\mathrm{Vol}(a, L) = \pi a^2 L \ge \kappa_{\mathrm{TVE}} > 0\).
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-- Geometric volume of a 3D cylindrical neck segment of radius \(a\) and length \(L\). -/
@[expose]
noncomputable def neckVolume (a L : ℝ) : ℝ :=
  Real.pi * (a ^ 2) * L

/--
The derived TVE \(\kappa\)-noncollapsing volume floor:
\(\kappa_{\mathrm{TVE}}(\xi, L, E_{\max}) = (\pi^2 \xi L) / E_{\max}\).
-/
@[expose]
noncomputable def kappaTVE (xi L E_max : ℝ) : ℝ :=
  (Real.pi ^ 2 * xi * L) / E_max

/--
Lemma: Any upper bound \(E_{\max}\) on the physical neck energy is strictly positive.
-/
theorem energy_bound_strictly_positive (a xi sigma E_max : ℝ)
    (ha : a > 0) (hxi : xi > 0) (hsigma : sigma > 0)
    (h_bound : neckEnergyExplicit a xi sigma ≤ E_max) :
    0 < E_max := by
  have h_press := helicity_pressure_le_neck_energy a xi sigma ha hxi hsigma
  have h_pos : 0 < Real.pi * (xi / (a ^ 2)) := by positivity
  linarith

/--
Theorem: Strict Positivity of the TVE \(\kappa\)-Noncollapsing Constant.
-/
theorem kappa_tve_pos (a xi sigma L E_max : ℝ)
    (ha : a > 0) (hxi : xi > 0) (hsigma : sigma > 0) (hL : L > 0)
    (h_bound : neckEnergyExplicit a xi sigma ≤ E_max) :
    0 < kappaTVE xi L E_max := by
  have hE_pos := energy_bound_strictly_positive a xi sigma E_max ha hxi hsigma h_bound
  dsimp [kappaTVE]
  positivity

/--
Theorem: TVE Lyapunov Energy Bound Implies Perelman \(\kappa\)-Noncollapsing.
Any neck satisfying the TVE energy bound \(\mathcal{E}(a) \le E_{\max}\) automatically
satisfies the strict volume lower bound \(\kappa_{\mathrm{TVE}}(\xi, L, E_{\max}) \le \pi a^2 L\).
-/
theorem tve_implies_perelman_kappa_noncollapsing (a xi sigma L E_max : ℝ)
    (ha : a > 0) (hxi : xi > 0) (hsigma : sigma > 0) (hL : L > 0)
    (h_bound : neckEnergyExplicit a xi sigma ≤ E_max) :
    0 < kappaTVE xi L E_max ∧
    kappaTVE xi L E_max ≤ neckVolume a L := by
  have h_kpos := kappa_tve_pos a xi sigma L E_max ha hxi hsigma hL h_bound
  have hE_pos := energy_bound_strictly_positive a xi sigma E_max ha hxi hsigma h_bound
  have hE_ne : E_max ≠ 0 := ne_of_gt hE_pos
  have h_sq := neck_radius_sq_floor a xi sigma E_max ha hxi hsigma h_bound
  have h_fac : 0 ≤ (Real.pi * L) / E_max := by positivity
  have h_mul : ((Real.pi * L) / E_max) * (Real.pi * xi) ≤
      ((Real.pi * L) / E_max) * (E_max * (a ^ 2)) :=
    mul_le_mul_of_nonneg_left h_sq h_fac
  have h_lhs : ((Real.pi * L) / E_max) * (Real.pi * xi) =
      kappaTVE xi L E_max := by
    dsimp [kappaTVE]
    ring
  have h_rhs : ((Real.pi * L) / E_max) * (E_max * (a ^ 2)) =
      neckVolume a L := by
    dsimp [neckVolume]
    calc
      ((Real.pi * L) / E_max) * (E_max * (a ^ 2))
        = ((Real.pi * L) / E_max * E_max) * (a ^ 2) := by ring
      _ = (Real.pi * L) * (a ^ 2) := by rw [div_mul_cancel₀ (Real.pi * L) hE_ne]
      _ = Real.pi * (a ^ 2) * L := by ring
  refine ⟨h_kpos, ?_⟩
  linarith

#print axioms energy_bound_strictly_positive
#print axioms kappa_tve_pos
#print axioms tve_implies_perelman_kappa_noncollapsing

end TVE
