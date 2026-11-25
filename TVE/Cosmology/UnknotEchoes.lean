/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Horizonless Unknot Black Hole Echoes & Helical Polarization Spectrum

Formalizes dynamical collapse and echo observables of a horizonless TVE unknot
throat with polarizable vacuum index \(K(r) = e^{u(r)}\) and Beltrami core,
aligned with `TVE.Cosmology.BlackHoleUnknot`:
1. Exact logarithmic optical-potential linearization \(\nabla K / K = \nabla u\).
2. Tortoise hyperbolic-cosine bounce potential \(U_{\mathrm{eff}}(r_*)\),
   global minimum at \(r_{*,\mathrm{eq}} = r_s \ln\epsilon_{\mathrm{TVE}}\),
   and exact first/second derivatives proving cutoff independence of the
   throat breathing frequency \(\Omega_{\mathrm{breath}} = c^3 / (\sqrt{2} G M)\).
3. Cutoff-independent \(30\,M_\odot\) breathing frequency bracket
   \(f_{\mathrm{breath}} \in (761, 762)\,\mathrm{Hz}\) and Woltjer-Taylor
   over-barrier escape (\(\tilde{\Omega}_{\mathrm{breath}} = 1/\sqrt{2} > 0.3737\)).
4. Native exponential-PV echo timing vs. Planck-wall models: aligned with
   `BlackHoleUnknot`'s \(I_{\mathrm{echo}} \in (8.331, 8.332)\), a \(30\,M_\odot\)
   remnant produces echoes at \((1.231, 1.232)\,\mathrm{ms}\) vs.
   \((54.0, 54.2)\,\mathrm{ms}\) for Planck walls (more than \(40\times\) earlier).
5. Mass-independent Beltrami Berry polarization rotation
   \(\Delta\psi_{\mathrm{bounce}} = \pi(1 - 1/\sqrt{2}) \in (52.7^\circ, 52.8^\circ)\)
   per echo bounce.
6. Exact unitarity \(|R_{\mathrm{unknot},\pm}(\omega)| = 1\) of the soft-wall
   Bessel-Gamma reflection matrix and \(-3\,\mathrm{dB}\) geometric echo decay.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE.Cosmology

/-! ## 1. Logarithmic Optical Potential Linearization (\(u = \ln K\)) -/

/-- Exact chain-rule linearization of the polarizable vacuum stiffness gradient:
    for \(K(x) = e^{u(x)}\), \(\frac{K'(x)}{K(x)} = u'(x)\). -/
theorem optical_potential_log_linearization
    (u : ℝ → ℝ) (x u' : ℝ) (hu : HasDerivAt u u' x) :
    HasDerivAt (fun t => Real.exp (u t)) (Real.exp (u x) * u') x ∧
      (Real.exp (u x) * u') / Real.exp (u x) = u' := by
  have h_exp : HasDerivAt (fun t => Real.exp (u t)) (Real.exp (u x) * u') x :=
    hu.exp
  have h_pos : Real.exp (u x) ≠ 0 := ne_of_gt (Real.exp_pos (u x))
  refine ⟨h_exp, ?_⟩
  rw [mul_comm, mul_div_cancel_right₀ u' h_pos]

/-! ## 2. Tortoise Cosh Bounce Potential & Cutoff-Independent Breathing Mode -/

/-- Effective tortoise-coordinate potential of the unknot throat balancing
    gravitational redshift (\(e^{+y}\)) and Bohm cutoff stiffness (\(e^{-y}\)):
    \(U_{\mathrm{eff}}(r_*) = U_0 \cosh((r_* - r_{*,\mathrm{eq}})/r_s)\). -/
noncomputable def tortoiseCoshPotential (U0 r_eq r_s r_star : ℝ) : ℝ :=
  (U0 / 2) * (Real.exp ((r_star - r_eq) / r_s) +
              Real.exp (-((r_star - r_eq) / r_s)))

/-- Exact first derivative of the tortoise bounce potential. -/
noncomputable def tortoiseCoshDeriv (U0 r_eq r_s r_star : ℝ) : ℝ :=
  (U0 / (2 * r_s)) * (Real.exp ((r_star - r_eq) / r_s) -
                      Real.exp (-((r_star - r_eq) / r_s)))

/-- Exact second derivative of the tortoise bounce potential. -/
noncomputable def tortoiseCoshSecondDeriv (U0 r_eq r_s r_star : ℝ) : ℝ :=
  (U0 / (2 * r_s ^ 2)) * (Real.exp ((r_star - r_eq) / r_s) +
                          Real.exp (-((r_star - r_eq) / r_s)))

/-- Theorem: At the equilibrium bounce radius \(r_* = r_{*,\mathrm{eq}}\), the
    potential attains its global lower bound \(U_{\mathrm{eff}}(r_*) \ge U_0\). -/
theorem tortoiseCoshPotential_min_at_eq
    (U0 r_eq r_s r_star : ℝ) (hU0 : 0 ≤ U0) :
    U0 ≤ tortoiseCoshPotential U0 r_eq r_s r_star := by
  dsimp [tortoiseCoshPotential]
  set y := (r_star - r_eq) / r_s
  have h_pos : 0 < Real.exp y := Real.exp_pos y
  have h_ne : Real.exp y ≠ 0 := ne_of_gt h_pos
  have h_inv : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [h_inv]
  have h_sq : 0 ≤ (Real.exp y - 1) ^ 2 := sq_nonneg (Real.exp y - 1)
  have h_sum_ge : 2 ≤ Real.exp y + (Real.exp y)⁻¹ := by
    have h_mul : 2 * Real.exp y ≤ (Real.exp y + (Real.exp y)⁻¹) * Real.exp y := by
      have h_id :
          (Real.exp y + (Real.exp y)⁻¹) * Real.exp y =
            Real.exp y * Real.exp y + 1 := by
        rw [add_mul, inv_mul_cancel₀ h_ne]
      rw [h_id]
      have h_exp : (Real.exp y - 1) ^ 2 =
          Real.exp y * Real.exp y - 2 * Real.exp y + 1 := by ring
      linarith
    exact le_of_mul_le_mul_right h_mul h_pos
  have h_half : 0 ≤ U0 / 2 := by linarith
  have h_scaled := mul_le_mul_of_nonneg_left h_sum_ge h_half
  linarith

theorem tortoiseCoshPotential_at_eq (U0 r_eq r_s : ℝ) :
    tortoiseCoshPotential U0 r_eq r_s r_eq = U0 := by
  dsimp [tortoiseCoshPotential]
  simp only [sub_self, zero_div, neg_zero, Real.exp_zero]
  ring

/-- Theorem: Exact first derivative of `tortoiseCoshPotential`. -/
theorem hasDerivAt_tortoiseCoshPotential (U0 r_eq r_s r_star : ℝ) :
    HasDerivAt (tortoiseCoshPotential U0 r_eq r_s)
      (tortoiseCoshDeriv U0 r_eq r_s r_star) r_star := by
  have h_lin : HasDerivAt (fun r => (r - r_eq) / r_s) (1 / r_s) r_star :=
    ((hasDerivAt_id r_star).sub_const r_eq).div_const r_s
  have h_e1 :
      HasDerivAt (fun r => Real.exp ((r - r_eq) / r_s))
        (Real.exp ((r_star - r_eq) / r_s) * (1 / r_s)) r_star :=
    h_lin.exp
  have h_e2 :
      HasDerivAt (fun r => Real.exp (-((r - r_eq) / r_s)))
        (Real.exp (-((r_star - r_eq) / r_s)) * (-(1 / r_s))) r_star :=
    h_lin.neg.exp
  have h_full := (h_e1.add h_e2).const_mul (U0 / 2)
  refine h_full.congr_deriv ?_
  dsimp [tortoiseCoshDeriv]
  ring

/-- Theorem: Exact second derivative of `tortoiseCoshPotential`. -/
theorem hasDerivAt_tortoiseCoshDeriv (U0 r_eq r_s r_star : ℝ) :
    HasDerivAt (tortoiseCoshDeriv U0 r_eq r_s)
      (tortoiseCoshSecondDeriv U0 r_eq r_s r_star) r_star := by
  have h_lin : HasDerivAt (fun r => (r - r_eq) / r_s) (1 / r_s) r_star :=
    ((hasDerivAt_id r_star).sub_const r_eq).div_const r_s
  have h_e1 :
      HasDerivAt (fun r => Real.exp ((r - r_eq) / r_s))
        (Real.exp ((r_star - r_eq) / r_s) * (1 / r_s)) r_star :=
    h_lin.exp
  have h_e2 :
      HasDerivAt (fun r => Real.exp (-((r - r_eq) / r_s)))
        (Real.exp (-((r_star - r_eq) / r_s)) * (-(1 / r_s))) r_star :=
    h_lin.neg.exp
  have h_full := (h_e1.sub h_e2).const_mul (U0 / (2 * r_s))
  refine h_full.congr_deriv ?_
  dsimp [tortoiseCoshSecondDeriv]
  ring

/-- Stationary bounce point and cutoff-independent curvature
    \(U_{\mathrm{eff}}'(r_{*,\mathrm{eq}}) = 0\),
    \(U_{\mathrm{eff}}''(r_{*,\mathrm{eq}}) = U_0 / r_s^2\). -/
theorem tortoiseCosh_equilibrium_derivatives (U0 r_eq r_s : ℝ) :
    tortoiseCoshDeriv U0 r_eq r_s r_eq = 0 ∧
      tortoiseCoshSecondDeriv U0 r_eq r_s r_eq = U0 / r_s ^ 2 := by
  constructor
  · dsimp [tortoiseCoshDeriv]
    simp only [sub_self, zero_div, neg_zero, Real.exp_zero, sub_self, mul_zero]
  · dsimp [tortoiseCoshSecondDeriv]
    simp only [sub_self, zero_div, neg_zero, Real.exp_zero]
    ring

/-- Cutoff-independent asymptotic throat breathing angular frequency:
    \(\Omega_{\mathrm{breath}} = \sqrt{c^2 U''(r_{*,\mathrm{eq}}) / (U_0 / 2)}
    = \frac{\sqrt{2}\,c}{r_s} = \frac{c^3}{\sqrt{2}\,G M}\). -/
noncomputable def breathingOmega (c G M : ℝ) : ℝ :=
  c ^ 3 / (Real.sqrt 2 * G * M)

theorem breathingOmega_cutoff_independent
    (U0 c G M ε_TVE : ℝ)
    (hU0 : 0 < U0) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) :
    let r_s := 2 * G * M / c ^ 2
    let r_eq := r_s * Real.log ε_TVE
    Real.sqrt (c ^ 2 * tortoiseCoshSecondDeriv U0 r_eq r_s r_eq / (U0 / 2)) =
      breathingOmega c G M := by
  intro r_s r_eq
  have h_curv := (tortoiseCosh_equilibrium_derivatives U0 r_eq r_s).2
  rw [h_curv]
  have hU0_ne : U0 ≠ 0 := ne_of_gt hU0
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hG_ne : G ≠ 0 := ne_of_gt hG
  have hM_ne : M ≠ 0 := ne_of_gt hM
  have h_sq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have h_alg :
      c ^ 2 * (U0 / r_s ^ 2) / (U0 / 2) = (breathingOmega c G M) ^ 2 := by
    dsimp [breathingOmega, r_s]
    have h_lhs_simp :
        c ^ 2 * (U0 / (2 * G * M / c ^ 2) ^ 2) / (U0 / 2) =
          c ^ 6 / (2 * G ^ 2 * M ^ 2) := by
      field_simp [hU0_ne, hc_ne, hG_ne, hM_ne]
    have h_rhs_simp :
        (c ^ 3 / (Real.sqrt 2 * G * M)) ^ 2 = c ^ 6 / (2 * G ^ 2 * M ^ 2) := by
      rw [div_pow]
      have h_den : (Real.sqrt 2 * G * M) ^ 2 = 2 * G ^ 2 * M ^ 2 := by
        calc
          (Real.sqrt 2 * G * M) ^ 2 = Real.sqrt 2 ^ 2 * G ^ 2 * M ^ 2 := by ring
          _ = 2 * G ^ 2 * M ^ 2 := by rw [h_sq2]
      rw [h_den]
      ring
    rw [h_lhs_simp, h_rhs_simp]
  rw [h_alg]
  have h_nonneg : 0 ≤ breathingOmega c G M := by
    dsimp [breathingOmega]
    positivity
  exact Real.sqrt_sq h_nonneg

/-! ## 3. Quantitative \(30\,M_\odot\) Breathing Frequency & Over-Barrier Escape -/

/-- Exact rational bracket on \(\sqrt{2} \in (1.4142, 1.4143)\). -/
theorem sqrt_two_bounds :
    (14142 : ℝ) / 10000 < Real.sqrt 2 ∧ Real.sqrt 2 < (14143 : ℝ) / 10000 := by
  have h_lo_sq : ((14142 : ℝ) / 10000) ^ 2 < 2 := by norm_num
  have h_hi_sq : (2 : ℝ) < ((14143 : ℝ) / 10000) ^ 2 := by norm_num
  constructor
  · have h1 := Real.sqrt_lt_sqrt (by positivity) h_lo_sq
    rwa [Real.sqrt_sq (by positivity)] at h1
  · have h2 := Real.sqrt_lt_sqrt (by positivity) h_hi_sq
    rwa [Real.sqrt_sq (by positivity)] at h2

/-- Positive-product monotonicity helper. -/
theorem mul_lt_mul_pos_bounds {a b c d : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hab : a < b) (hcd : c < d) :
    a * c < b * d := by
  have hb : 0 < b := by linarith
  have h1 : 0 < b * (d - c) := mul_pos hb (by linarith)
  have h2 : 0 < (b - a) * c := mul_pos (by linarith) hc
  have h_id : b * d - a * c = b * (d - c) + (b - a) * c := by ring
  linarith

/-- Throat breathing frequency \(f_{\mathrm{breath}} = \frac{1}{2\pi\sqrt{2}\,t_g}\)
    for gravitational time scale \(t_g = G M / c^3\). -/
noncomputable def breathingFreqHz (t_g : ℝ) : ℝ :=
  1 / (2 * Real.pi * Real.sqrt 2 * t_g)

/-- Theorem: For a \(30\,M_\odot\) LIGO remnant (\(t_g \in (147.7, 147.8)\,\mu\mathrm{s}\)),
    the cutoff-independent breathing mode lies strictly inside \((761, 762)\,\mathrm{Hz}\). -/
theorem breathing_30Msun_freq_bracket
    (t_g : ℝ)
    (ht_lo : (1477 : ℝ) / 10000000 < t_g)
    (ht_hi : t_g < (1478 : ℝ) / 10000000)
    (hpi_lo : (31415 : ℝ) / 10000 < Real.pi)
    (hpi_hi : Real.pi < (31416 : ℝ) / 10000) :
    (761 : ℝ) < breathingFreqHz t_g ∧ breathingFreqHz t_g < 762 := by
  rcases sqrt_two_bounds with ⟨hs_lo, hs_hi⟩
  have h_t_pos : 0 < t_g := by linarith
  have h_s_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by positivity)
  have h_den_pos : 0 < 2 * Real.pi * Real.sqrt 2 * t_g := by
    have hpi := Real.pi_pos
    positivity
  have h_p1_lo :
      ((31415 : ℝ) / 10000) * ((14142 : ℝ) / 10000) < Real.pi * Real.sqrt 2 :=
    mul_lt_mul_pos_bounds (by positivity) (by positivity) hpi_lo hs_lo
  have h_p2_lo :
      ((31415 : ℝ) / 10000) * ((14142 : ℝ) / 10000) * ((1477 : ℝ) / 10000000) <
        Real.pi * Real.sqrt 2 * t_g :=
    mul_lt_mul_pos_bounds (by positivity) (by positivity) h_p1_lo ht_lo
  have h_p1_hi :
      Real.pi * Real.sqrt 2 < ((31416 : ℝ) / 10000) * ((14143 : ℝ) / 10000) :=
    mul_lt_mul_pos_bounds (by linarith) h_s_pos hpi_hi hs_hi
  have h_p2_hi :
      Real.pi * Real.sqrt 2 * t_g <
        ((31416 : ℝ) / 10000) * ((14143 : ℝ) / 10000) * ((1478 : ℝ) / 10000000) :=
    mul_lt_mul_pos_bounds (by positivity) h_t_pos h_p1_hi ht_hi
  have h_num_lo :
      761 * (2 * (((31416 : ℝ) / 10000) * ((14143 : ℝ) / 10000) *
        ((1478 : ℝ) / 10000000))) < 1 := by norm_num
  have h_num_hi :
      1 < 762 * (2 * (((31415 : ℝ) / 10000) * ((14142 : ℝ) / 10000) *
        ((1477 : ℝ) / 10000000))) := by norm_num
  dsimp [breathingFreqHz]
  constructor
  · rw [lt_div_iff₀ h_den_pos]
    linarith
  · rw [div_lt_iff₀ h_den_pos]
    linarith

/-- Theorem (Woltjer-Taylor Over-Barrier Escape):
    The dimensionless breathing frequency \(\tilde{\Omega}_{\mathrm{breath}} = 1/\sqrt{2}\)
    exceeds the \(l = 2\) Regge-Wheeler photon-sphere barrier peak \(0.3737\),
    driving rapid relaxation of Echo \(k = 1\) into stationary echoes \(k \ge 3\). -/
theorem breathing_above_regge_wheeler_barrier :
    (3737 : ℝ) / 10000 < 1 / Real.sqrt 2 := by
  have h_s_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by positivity)
  rw [lt_div_iff₀ h_s_pos]
  rcases sqrt_two_bounds with ⟨_, hs_hi⟩
  linarith

/-! ## 4. Native Exponential-PV Echo Timing vs. Planck-Wall Models -/

/-- Native TVE exponential-PV echo delay \(\Delta t_{\mathrm{PV}} = t_g I_{\mathrm{echo}}\),
    where `BlackHoleUnknot` certifies \(I_{\mathrm{echo}} = 2 \int_{1/2}^1 (e^{2u}/u^2)\,du
    \in (8.331, 8.332)\) with zero Planck-length free parameters. -/
def pvEchoDelay (t_g I_echo : ℝ) : ℝ :=
  t_g * I_echo

/-- Planck-wall benchmark delay \(\Delta t_{\mathrm{Planck}} = 4 t_g \ln(r_s / \ell_P)\). -/
noncomputable def planckEchoDelay (t_g r_s l_P : ℝ) : ℝ :=
  4 * t_g * Real.log (r_s / l_P)

/-- Planck-wall delay in milliseconds given \(t_g\) in ms and \(L_P = \ln(r_s / \ell_P)\). -/
def planckEchoDelayMs (t_g_ms L_P : ℝ) : ℝ :=
  4 * t_g_ms * L_P

/-- Theorem: Whenever the compact exponential-PV optical cavity integral satisfies
    \(I_{\mathrm{echo}} < 4 \ln(r_s / \ell_P)\), TVE echoes arrive strictly earlier
    than Planck-wall echoes. -/
theorem pv_echo_strictly_earlier_than_planck
    (t_g I_echo r_s l_P : ℝ)
    (ht : 0 < t_g) (h_lt : I_echo < 4 * Real.log (r_s / l_P)) :
    pvEchoDelay t_g I_echo < planckEchoDelay t_g r_s l_P := by
  dsimp [pvEchoDelay, planckEchoDelay]
  have h_mul := mul_lt_mul_of_pos_left h_lt ht
  linarith

/--
Quantitative \(30\,M_\odot\) Echo Timing Separation (`BlackHoleUnknot` Alignment):
For \(t_g \in (0.147764, 0.147766)\,\mathrm{ms}\):
- Native exponential-PV cavity (\(I_{\mathrm{echo}} \in (8.331, 8.332)\)):
  \(\Delta t_{\mathrm{PV}} \in (1.231, 1.232)\,\mathrm{ms}\)
- Planck-wall benchmark (\(L_P \in (91.45, 91.55)\)):
  \(\Delta t_{\mathrm{Planck}} \in (54.0, 54.2)\,\mathrm{ms}\)
TVE echoes arrive strictly more than \(40\times\) earlier than Planck-wall templates.
-/
theorem echo_30Msun_pv_vs_planck_brackets
    (t_g_ms I_echo L_P : ℝ)
    (ht_lo : (147764 : ℝ) / 1000000 < t_g_ms)
    (ht_hi : t_g_ms < (147766 : ℝ) / 1000000)
    (hI_lo : (8331 : ℝ) / 1000 < I_echo)
    (hI_hi : I_echo < (8332 : ℝ) / 1000)
    (hP_lo : (9145 : ℝ) / 100 < L_P)
    (hP_hi : L_P < (9155 : ℝ) / 100) :
    ((1231 : ℝ) / 1000 < pvEchoDelay t_g_ms I_echo ∧
      pvEchoDelay t_g_ms I_echo < (1232 : ℝ) / 1000) ∧
    ((540 : ℝ) / 10 < planckEchoDelayMs t_g_ms L_P ∧
      planckEchoDelayMs t_g_ms L_P < (542 : ℝ) / 10) ∧
    40 * pvEchoDelay t_g_ms I_echo < planckEchoDelayMs t_g_ms L_P := by
  have ht_pos : 0 < t_g_ms := by linarith
  have hI_pos : 0 < I_echo := by linarith
  have hP_pos : 0 < L_P := by linarith
  have h_pv_lo :=
    mul_lt_mul_pos_bounds (by positivity) (by positivity) ht_lo hI_lo
  have h_pv_hi := mul_lt_mul_pos_bounds ht_pos hI_pos ht_hi hI_hi
  have h_p_lo :=
    mul_lt_mul_pos_bounds (by positivity) (by positivity) ht_lo hP_lo
  have h_p_hi := mul_lt_mul_pos_bounds ht_pos hP_pos ht_hi hP_hi
  dsimp [pvEchoDelay, planckEchoDelayMs]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩

/-! ## 5. Mass-Independent Beltrami Berry Polarization Rotation (\(52.72^\circ\)) -/

/-- Rytov-Vladimirskii-Berry geometric polarization rotation per bounce through
    a \((1,1)\) virial-equipartition Beltrami unknot throat (\(\cos\theta_0 = 1/\sqrt{2}\)). -/
noncomputable def beltramiBounceRotationRad : ℝ :=
  Real.pi * (1 - 1 / Real.sqrt 2)

/-- Equivalent bounce polarization rotation in degrees: \(180(1 - 1/\sqrt{2})\). -/
noncomputable def beltramiBounceRotationDeg : ℝ :=
  180 * (1 - 1 / Real.sqrt 2)

/-- Cumulative polarization rotation after \(k\) throat reflections. -/
noncomputable def echoPolarizationAngle (k : ℕ) : ℝ :=
  (k : ℝ) * beltramiBounceRotationRad

/-- Theorem: Successive echoes step linearly in polarization angle by
    \(\Delta\psi_{\mathrm{bounce}}\), completely independent of black hole mass \(M\). -/
theorem echoPolarizationAngle_step (k : ℕ) :
    echoPolarizationAngle (k + 1) - echoPolarizationAngle k =
      beltramiBounceRotationRad := by
  dsimp [echoPolarizationAngle]
  push_cast
  ring

/-- Theorem: The mass-independent per-bounce polarization rotation lies strictly
    inside \((52.7^\circ, 52.8^\circ)\). -/
theorem beltramiBounceRotationDeg_bracket :
    (527 : ℝ) / 10 < beltramiBounceRotationDeg ∧
      beltramiBounceRotationDeg < (528 : ℝ) / 10 := by
  rcases sqrt_two_bounds with ⟨hs_lo, hs_hi⟩
  have h_s_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by positivity)
  have h_inv_lo : (10000 : ℝ) / 14143 < 1 / Real.sqrt 2 := by
    rw [div_lt_div_iff₀ (by positivity) h_s_pos]
    linarith
  have h_inv_hi : 1 / Real.sqrt 2 < (10000 : ℝ) / 14142 := by
    rw [div_lt_div_iff₀ h_s_pos (by positivity)]
    linarith
  dsimp [beltramiBounceRotationDeg]
  constructor <;> linarith

/-! ## 6. Unitary Bessel-Gamma Soft-Wall Reflection & \(-3\,\mathrm{dB}\) Echo Decay -/

/-- Closed-form soft-wall Bessel-Gamma inner reflection amplitude for circular
    polarization modes (\(\pm\)):
    \(R_{\mathrm{unknot},\pm}(\omega) = -\frac{\Gamma(1 + i\nu)}{\Gamma(1 - i\nu)}
    e^{\pm i \Delta\psi_{\mathrm{bounce}}}\), with \(\nu = 4 G M \omega / c^3\). -/
noncomputable def unknotReflection (ν Δψ : ℝ) : ℂ :=
  -(Complex.Gamma (1 + Complex.I * (ν : ℂ)) /
    Complex.Gamma (1 - Complex.I * (ν : ℂ))) *
    Complex.exp ((Δψ : ℂ) * Complex.I)

/-- Theorem: The soft-wall Bessel-Gamma unknot core is strictly unitary
    (\(\|R_{\mathrm{unknot},\pm}(\omega)\| = 1\)) at every real frequency \(\nu\). -/
theorem unknotReflection_unitary (ν Δψ : ℝ) :
    ‖unknotReflection ν Δψ‖ = 1 := by
  dsimp [unknotReflection]
  set s : ℂ := 1 + Complex.I * (ν : ℂ)
  have h_re : 0 < s.re := by
    simp [s, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  have h_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h_re
  have h_norm_ne : ‖Complex.Gamma s‖ ≠ 0 := norm_ne_zero_iff.mpr h_ne
  have h_conj_arg : 1 - Complex.I * (ν : ℂ) = starRingEnd ℂ s := by
    simp [s, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, sub_eq_add_neg]
  have h_gamma_conj :
      Complex.Gamma (1 - Complex.I * (ν : ℂ)) =
        starRingEnd ℂ (Complex.Gamma s) := by
    rw [h_conj_arg]
    exact Complex.Gamma_conj s
  rw [norm_mul, norm_neg, norm_div, h_gamma_conj, Complex.norm_conj,
      div_self h_norm_ne, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Theorem: Combining unitary core reflection (\(\|R_{\mathrm{unknot}}\| = 1\))
    with the 50/50 Regge-Wheeler photon-sphere split (\(|R_{\mathrm{ph}}| = 1/\sqrt{2}\))
    yields an exact \(-3\,\mathrm{dB}\) (\(1/2\)) power decay per echo bounce. -/
theorem echo_power_half_per_bounce (ν Δψ : ℝ) :
    (‖unknotReflection ν Δψ‖ * (1 / Real.sqrt 2)) ^ 2 = (1 : ℝ) / 2 := by
  rw [unknotReflection_unitary, one_mul, div_pow, one_pow,
      Real.sq_sqrt (by positivity)]

#print axioms optical_potential_log_linearization
#print axioms tortoiseCoshPotential_min_at_eq
#print axioms hasDerivAt_tortoiseCoshPotential
#print axioms hasDerivAt_tortoiseCoshDeriv
#print axioms tortoiseCosh_equilibrium_derivatives
#print axioms breathingOmega_cutoff_independent
#print axioms breathing_30Msun_freq_bracket
#print axioms breathing_above_regge_wheeler_barrier
#print axioms pv_echo_strictly_earlier_than_planck
#print axioms echo_30Msun_pv_vs_planck_brackets
#print axioms echoPolarizationAngle_step
#print axioms beltramiBounceRotationDeg_bracket
#print axioms unknotReflection_unitary
#print axioms echo_power_half_per_bounce

end TVE.Cosmology
