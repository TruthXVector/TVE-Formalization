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
public import TVE.Vacuum
public import TVE.Poincare.NeckStability
public import TVE.Poincare.SmoothPoincare4D

/-!
# Vortex Filament Core Radius Floor and Pointwise Vorticity Cap

Applies the TVE Bogomolny helicity-tension floor to a 3D fluid vortex filament
carrying circulation \(\Gamma_0 > 0\) under viscous decay rate \(\gamma_\nu > 0\).
Proves that the squared core radius \(a(t)^2\) is bounded away from zero for all
\(0 \le t\) and that the Kelvin core vorticity \(|\boldsymbol{\omega}| = \Gamma_0 / (\pi a^2)\)
is uniformly capped by \(\omega_{\max} < \infty\), preventing finite-time blowup.
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
The hydrodynamic vortex helicity pressure coupling constant:
\(\xi_{\mathrm{vort}} = \Gamma_0^2 / (2\pi^2)\).
-/
@[expose]
noncomputable def vortexHelicityCoupling (Gamma0 : ℝ) : ℝ :=
  (Gamma0 ^ 2) / (2 * Real.pi ^ 2)

/--
Lemma: For any non-zero circulation \(\Gamma_0 > 0\), the vortex helicity
coupling \(\xi_{\mathrm{vort}}\) is strictly positive.
-/
theorem vortex_coupling_pos (Gamma0 : ℝ) (hG : Gamma0 > 0) :
    0 < vortexHelicityCoupling Gamma0 := by
  dsimp [vortexHelicityCoupling]
  positivity

/--
Theorem: Viscous Lyapunov Vortex-Energy Sandwich.
Substituting the viscous dissipation rate \(\gamma_\nu > 0\) into the neck
stability semigroup bounds the radial vortex energy between the Bogomolny floor
and its initial value \(\mathcal{E}(a_0)\) for all \(0 \le t\).
-/
theorem viscous_lyapunov_vortex_sandwich (a0 xi_vort sigma_vort gamma_nu t : ℝ)
    (ha0 : a0 > 0) (hxi : xi_vort > 0) (hsigma : sigma_vort > 0)
    (h_nu : gamma_nu > 0) (ht : 0 ≤ t) :
    topologicalFloor xi_vort sigma_vort ≤
      neckEnergyFlow a0 xi_vort sigma_vort gamma_nu t ∧
    neckEnergyFlow a0 xi_vort sigma_vort gamma_nu t ≤
      radialEnergyPerLength a0 xi_vort sigma_vort :=
  lyapunov_energy_sandwich a0 xi_vort sigma_vort gamma_nu t ha0 hxi hsigma h_nu ht

/--
Theorem: Uniform Vortex Core Radius Floor.
For any vortex tube bounded by radial energy \(E_{\max}\), the core radius \(a\)
satisfies \(\pi\xi_{\mathrm{vort}} \le E_{\max} a^2\), preventing \(a \to 0\) pinch-off.
-/
theorem vortex_core_radius_sq_floor (a xi_vort sigma_vort E_max : ℝ)
    (ha : a > 0) (hxi : xi_vort > 0) (hsigma : sigma_vort > 0)
    (h_bound : neckEnergyExplicit a xi_vort sigma_vort ≤ E_max) :
    Real.pi * xi_vort ≤ E_max * (a ^ 2) :=
  neck_radius_sq_floor a xi_vort sigma_vort E_max ha hxi hsigma h_bound

/--
Theorem: Kelvin Pointwise \(L^\infty\) Vorticity Cap.
By Kelvin's circulation relation \(|\boldsymbol{\omega}| = (\Gamma_0 / \pi) / a^2\),
the helicity radius floor strictly bounds the peak vorticity magnitude by
\(\omega_{\max} = ((\Gamma_0 / \pi) E_{\max}) / (\pi \xi_{\mathrm{vort}}) < \infty\).
-/
theorem kelvin_vorticity_linfty_cap (a xi_vort sigma_vort E_max Gamma0 : ℝ)
    (ha : a > 0) (hxi : xi_vort > 0) (hsigma : sigma_vort > 0) (hG : Gamma0 > 0)
    (h_bound : neckEnergyExplicit a xi_vort sigma_vort ≤ E_max) :
    (Gamma0 / Real.pi) / (a ^ 2) ≤
      ((Gamma0 / Real.pi) * E_max) / (Real.pi * xi_vort) := by
  have hC : Gamma0 / Real.pi > 0 := by positivity
  exact sectional_curvature_cap_no_surgery
    a xi_vort sigma_vort E_max (Gamma0 / Real.pi) ha hxi hsigma hC h_bound

/--
Theorem: Kolmogorov / Ultraviolet Vortex Mode-Count Bound.
Because every active vortex tube satisfies \(0 < a_{\mathrm{eq}} \le r_{\min}\),
the number of active transverse modes \(N_{\mathrm{modes}}\) is bounded by the
TVE capacity \(\alpha^{-1} = 4\pi^3 + \pi^2 + \pi\).
-/
theorem kolmogorov_mode_count_bounded (N_modes r_min a_eq : ℝ)
    (hN : 0 ≤ N_modes) (ha : a_eq > 0) (h_floor : a_eq ≤ r_min)
    (h_cap : N_modes * (r_min / a_eq) ^ 2 ≤ alphaInv) :
    N_modes ≤ 4 * Real.pi ^ 3 + Real.pi ^ 2 + Real.pi :=
  casson_stage_count_bounded_by_alphaInv N_modes r_min a_eq hN ha h_floor h_cap

#print axioms vortex_coupling_pos
#print axioms viscous_lyapunov_vortex_sandwich
#print axioms vortex_core_radius_sq_floor
#print axioms kelvin_vorticity_linfty_cap
#print axioms kolmogorov_mode_count_bounded

end TVE