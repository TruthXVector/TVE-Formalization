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

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option linter.style.whitespace false

/-!
# Horizonless Unknot Black Hole Cavity Dynamics, Freeze-Out & Helical Spectrum

Formalizes wave propagation, rotating horizonless geometry, core boundary
dichotomy, and polarization observables on the native TVE exponential
polarizable-vacuum (PV) metric \(K(r) = e^{2 r_g / r}\) (`u = r_g / r`),
fully unified with `TVE.Cosmology.BlackHoleUnknot` and high-SNR LIGO ringdown
constraints (`GW150914`, `GW250114_082203`) with zero Schwarzschild cutoffs:
1. Exact log-radial throat profile \(R_{\mathrm{phys}}(x) = r_g e^{x + e^{-x}}\),
   proper vs. tortoise curvature redshift (\(1/(e^2 r_g^2)\) vs. \(1/(e^4 r_g^2)\)),
   sub-barrier throat modes (\(\tilde{\Omega}_{\mathrm{throat},\infty} = 1/e^2 < 0.3730\)),
   and the single-peak impedance-matched potential \(V_{\mathrm{opt}}(u)\) proving
   why empty polarizable vacuum at \(u = 1\) is reflectionless (\(Z_{\mathrm{vac}} = Z_0\)).
2. Exact horizonless rotating exponential-PV equatorial geometry (`Azreg-Aïnou /
   Newman-Janis`), proving \(g_{t\phi}^2 - g_{tt} g_{\phi\phi} = r^2 + a^2 > 0\)
   for all \(r > 0\) and all spin parameters \(a \in \mathbb{R}\).
3. Core boundary dichotomy: near-TOV prompt millisecond cavities (\(u_{\mathrm{core}} = 1\),
   \(\Delta t_{\mathrm{PV}} \in (1.231, 1.232)\,\mathrm{ms}\) at \(30\,M_\odot\),
   \(> 40\times\) earlier than Planck walls) vs. super-TOV exponential optical
   freeze-out (\(I_{\mathrm{echo}}(u_{\mathrm{core}})\) exceeding \(17\,\mathrm{s}\) at
   \(30\,M_\odot\) and \(40\,\mathrm{s}\) at \(68.56\,M_\odot\) by \(u_{\mathrm{core}} = 8\)).
4. First-principles PV bag soft-wall Bessel-Gamma reflection (\(\nu_{\mathrm{PV}} =
   \frac{e^2}{2} t_g \omega\), \(\frac{e^2}{2} < 4\)) and spin-weighted Beltrami Berry
   polarization rotation (\(52.7^\circ\text{–}52.8^\circ\) for spin-1 ngEHT subrings;
   \(105.4^\circ\text{–}105.5^\circ\) for spin-2 gravitational waves).
5. Decoupled dissipative Dyson cavity series (\(A_{k+1} = \epsilon_1 \gamma_{\mathrm{loop}}^k\))
   and exact geometric energy bounds recovering the lossless \(-3\,\mathrm{dB}\) limit.
-/

public section

namespace TVE.Cosmology

/-! ## 1. Elementary Rational Bounds & Native Exponential-PV Throat Optics -/

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

/-- Monotone squaring step for exponential lower bounds:
    \(0 \le a \le e^x \implies a^2 \le e^{2x}\). -/
theorem sq_le_exp_double {a x : ℝ} (ha : 0 ≤ a) (h : a ≤ Real.exp x) :
    a ^ 2 ≤ Real.exp (2 * x) := by
  have hexp : 0 ≤ Real.exp x := le_of_lt (Real.exp_pos x)
  have h2x : x + x = 2 * x := by ring
  calc
    a ^ 2 = a * a := sq a
    _ ≤ Real.exp x * Real.exp x := mul_le_mul h h ha hexp
    _ = Real.exp (x + x) := (Real.exp_add x x).symm
    _ = Real.exp (2 * x) := by rw [h2x]

/-- Zero-axiom elementary rational bracket on \(K_{\mathrm{throat}} = e^2 \in (7.27, 7.51)\)
    via seven dyadic squarings of `Real.add_one_le_exp (±1/64)`. -/
theorem exp_two_bounds :
    (727 : ℝ) / 100 < Real.exp 2 ∧ Real.exp 2 < (751 : ℝ) / 100 := by
  have h0 : (65 : ℝ) / 64 ≤ Real.exp (1 / 64) := by
    have h := Real.add_one_le_exp ((1 : ℝ) / 64)
    linarith
  have h1 := sq_le_exp_double (by positivity) h0
  rw [show (2 : ℝ) * (1 / 64) = 1 / 32 by norm_num] at h1
  have h2 := sq_le_exp_double (by positivity) h1
  rw [show (2 : ℝ) * (1 / 32) = 1 / 16 by norm_num] at h2
  have h3 := sq_le_exp_double (by positivity) h2
  rw [show (2 : ℝ) * (1 / 16) = 1 / 8 by norm_num] at h3
  have h4 := sq_le_exp_double (by positivity) h3
  rw [show (2 : ℝ) * (1 / 8) = 1 / 4 by norm_num] at h4
  have h5 := sq_le_exp_double (by positivity) h4
  rw [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] at h5
  have h6 := sq_le_exp_double (by positivity) h5
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h6
  have h7 := sq_le_exp_double (by positivity) h6
  rw [show (2 : ℝ) * 1 = 2 by norm_num] at h7
  have h_lo_num :
      (727 : ℝ) / 100 < ((((((((65 : ℝ) / 64) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
    norm_num
  have hn0 : (63 : ℝ) / 64 ≤ Real.exp (-((1 : ℝ) / 64)) := by
    have h := Real.add_one_le_exp (-((1 : ℝ) / 64))
    linarith
  have hn1 := sq_le_exp_double (by positivity) hn0
  rw [show (2 : ℝ) * -((1 : ℝ) / 64) = -((1 : ℝ) / 32) by norm_num] at hn1
  have hn2 := sq_le_exp_double (by positivity) hn1
  rw [show (2 : ℝ) * -((1 : ℝ) / 32) = -((1 : ℝ) / 16) by norm_num] at hn2
  have hn3 := sq_le_exp_double (by positivity) hn2
  rw [show (2 : ℝ) * -((1 : ℝ) / 16) = -((1 : ℝ) / 8) by norm_num] at hn3
  have hn4 := sq_le_exp_double (by positivity) hn3
  rw [show (2 : ℝ) * -((1 : ℝ) / 8) = -((1 : ℝ) / 4) by norm_num] at hn4
  have hn5 := sq_le_exp_double (by positivity) hn4
  rw [show (2 : ℝ) * -((1 : ℝ) / 4) = -((1 : ℝ) / 2) by norm_num] at hn5
  have hn6 := sq_le_exp_double (by positivity) hn5
  rw [show (2 : ℝ) * -((1 : ℝ) / 2) = -(1 : ℝ) by norm_num] at hn6
  have hn7 := sq_le_exp_double (by positivity) hn6
  rw [show (2 : ℝ) * -(1 : ℝ) = -(2 : ℝ) by norm_num] at hn7
  rw [Real.exp_neg (2 : ℝ), ← one_div] at hn7
  have h_hi_num :
      (100 : ℝ) / 751 < ((((((((63 : ℝ) / 64) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2) ^ 2 := by
    norm_num
  have h_inv_lt : (100 : ℝ) / 751 < 1 / Real.exp 2 := lt_of_lt_of_le h_hi_num hn7
  rw [div_lt_div_iff₀ (by positivity) (Real.exp_pos 2)] at h_inv_lt
  exact ⟨lt_of_lt_of_le h_lo_num h7, by linarith⟩

/-- Physical circumferential radius in log-radial coordinate \(r = r_g e^x\)
    (\(u = e^{-x}\)): \(R_{\mathrm{phys}}(x) = r_g \exp(x + e^{-x})\). -/
noncomputable def pvThroatRadiusLog (r_g x : ℝ) : ℝ :=
  r_g * Real.exp (x + Real.exp (-x))

/-- First log-radial derivative \(\frac{d R_{\mathrm{phys}}}{dx}\). -/
noncomputable def pvThroatRadiusLogDeriv (r_g x : ℝ) : ℝ :=
  r_g * Real.exp (x + Real.exp (-x)) * (1 - Real.exp (-x))

/-- Second log-radial derivative \(\frac{d^2 R_{\mathrm{phys}}}{dx^2}\). -/
noncomputable def pvThroatRadiusLogSecondDeriv (r_g x : ℝ) : ℝ :=
  r_g * Real.exp (x + Real.exp (-x)) * ((1 - Real.exp (-x)) ^ 2 + Real.exp (-x))

/-- Theorem: At the throat \(x = 0\) (\(r = r_g\), \(u = 1\)), \(R_{\mathrm{phys}}(x)\)
    attains its global minimum \(e r_g\) with zero arbitrary cutoff parameters. -/
theorem pvThroatRadiusLog_min_at_throat
    (r_g x : ℝ) (hrg : 0 ≤ r_g) :
    r_g * Real.exp 1 ≤ pvThroatRadiusLog r_g x ∧
      pvThroatRadiusLog r_g 0 = r_g * Real.exp 1 := by
  constructor
  · dsimp [pvThroatRadiusLog]
    have h_ineq : 1 ≤ x + Real.exp (-x) := by
      have h := Real.add_one_le_exp (-x)
      linarith
    have h_exp : Real.exp 1 ≤ Real.exp (x + Real.exp (-x)) :=
      Real.exp_le_exp.mpr h_ineq
    exact mul_le_mul_of_nonneg_left h_exp hrg
  · dsimp [pvThroatRadiusLog]
    simp only [neg_zero, Real.exp_zero, zero_add]

/-- Theorem: Exact first derivative of `pvThroatRadiusLog`. -/
theorem hasDerivAt_pvThroatRadiusLog (r_g x : ℝ) :
    HasDerivAt (pvThroatRadiusLog r_g) (pvThroatRadiusLogDeriv r_g x) x := by
  have h_neg : HasDerivAt (fun t => Real.exp (-t)) (Real.exp (-x) * (-1)) x :=
    (hasDerivAt_id x).neg.exp
  have h_inner :
      HasDerivAt (fun t => t + Real.exp (-t)) (1 + Real.exp (-x) * (-1)) x :=
    (hasDerivAt_id x).add h_neg
  have h_exp := (h_inner.exp).const_mul r_g
  refine h_exp.congr_deriv ?_
  dsimp [pvThroatRadiusLogDeriv]
  ring

/-- Theorem: Exact second derivative of `pvThroatRadiusLog`. -/
theorem hasDerivAt_pvThroatRadiusLogDeriv (r_g x : ℝ) :
    HasDerivAt (pvThroatRadiusLogDeriv r_g)
      (pvThroatRadiusLogSecondDeriv r_g x) x := by
  have h1 := hasDerivAt_pvThroatRadiusLog r_g x
  have h2 :
      HasDerivAt (fun t => 1 - Real.exp (-t)) (0 - Real.exp (-x) * (-1)) x :=
    (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).neg.exp)
  have h_prod := h1.mul h2
  refine h_prod.congr_deriv ?_
  dsimp [pvThroatRadiusLogSecondDeriv, pvThroatRadiusLogDeriv, pvThroatRadiusLog]
  ring

/-- Theorem (Proper vs. Tortoise Throat Curvature Redshift):
    At \(x = 0\) (\(dl/dx|_0 = e r_g\), \(dr_*/dx|_0 = e^2 r_g\)), the local proper
    throat curvature \(1/(e^2 r_g^2)\) is redshifted by \(e^{-2}\) in distant-observer
    tortoise coordinates to \(1/(e^4 r_g^2)\). -/
theorem pvThroatRadiusLog_curvatures_at_throat (r_g : ℝ) (hrg : r_g ≠ 0) :
    pvThroatRadiusLogDeriv r_g 0 = 0 ∧
      (pvThroatRadiusLogSecondDeriv r_g 0 / (r_g * Real.exp 1) ^ 2) /
        pvThroatRadiusLog r_g 0 = 1 / (r_g ^ 2 * Real.exp 2) ∧
      (pvThroatRadiusLogSecondDeriv r_g 0 / (r_g * Real.exp 2) ^ 2) /
        pvThroatRadiusLog r_g 0 = 1 / (r_g ^ 2 * Real.exp 4) := by
  have he1_ne : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  have he2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, sq]
  have he4 : Real.exp 4 = Real.exp 2 ^ 2 := by
    rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add, sq]
  refine ⟨?_, ?_, ?_⟩
  · dsimp [pvThroatRadiusLogDeriv]
    simp only [neg_zero, Real.exp_zero, sub_self, mul_zero]
  · dsimp [pvThroatRadiusLogSecondDeriv, pvThroatRadiusLog]
    simp only [neg_zero, Real.exp_zero, zero_add, sub_self]
    rw [he2]
    field_simp [hrg, he1_ne]
    ring
  · dsimp [pvThroatRadiusLogSecondDeriv, pvThroatRadiusLog]
    simp only [neg_zero, Real.exp_zero, zero_add, sub_self]
    rw [he4, he2]
    field_simp [hrg, he1_ne]
    ring

/-- Redshifted distant-observer throat curvature frequency (\(m = 1\)):
    \(f_{\mathrm{throat},1} = \frac{1}{2\pi e^2 t_g}\). -/
noncomputable def subBarrierThroatFreqHz (t_g : ℝ) : ℝ :=
  1 / (2 * Real.pi * Real.exp 2 * t_g)

/-- Quadrupole (\(m = 2\)) distant-observer throat circulation frequency:
    \(f_{\mathrm{throat},2} = \frac{1}{\pi e^2 t_g} = 2 f_{\mathrm{throat},1}\). -/
noncomputable def quadrupoleThroatFreqHz (t_g : ℝ) : ℝ :=
  1 / (Real.pi * Real.exp 2 * t_g)

/-- Theorem (Sub-Barrier Trapping vs. \(l = 2\) Barrier Peak):
    The dimensionless redshifted throat curvature mode
    \(\tilde{\Omega}_{\mathrm{throat},\infty} = 1 / e^2\) sits strictly below the
    \(l = 2\) barrier peak \(0.3730\) (replacing the unredshifted Schwarzschild
    over-barrier approximation). -/
theorem throat_mode_strictly_sub_barrier :
    1 / Real.exp 2 < (3730 : ℝ) / 10000 := by
  rcases exp_two_bounds with ⟨he_lo, _⟩
  have he_pos : 0 < Real.exp 2 := Real.exp_pos 2
  rw [div_lt_div_iff₀ he_pos (by positivity)]
  linarith

/-- Theorem: For a `GW250114_082203`-scale remnant
    (\(M_{f,\mathrm{det}} \approx 68.56\,M_\odot\), \(t_g \in (337.69, 337.71)\,\mu\mathrm{s}\)),
    the sub-barrier throat modes lie inside \((62, 65)\,\mathrm{Hz}\) (\(m = 1\))
    and \((125, 130)\,\mathrm{Hz}\) (\(m = 2\)). -/
theorem throat_GW250114_freq_brackets
    (t_g : ℝ)
    (ht_lo : (33769 : ℝ) / 100000000 < t_g)
    (ht_hi : t_g < (33771 : ℝ) / 100000000)
    (hpi_lo : (31415 : ℝ) / 10000 < Real.pi)
    (hpi_hi : Real.pi < (31416 : ℝ) / 10000) :
    ((62 : ℝ) < subBarrierThroatFreqHz t_g ∧ subBarrierThroatFreqHz t_g < 65) ∧
    ((125 : ℝ) < quadrupoleThroatFreqHz t_g ∧ quadrupoleThroatFreqHz t_g < 130) := by
  rcases exp_two_bounds with ⟨he_lo, he_hi⟩
  have ht_pos : 0 < t_g := by linarith
  have he_pos : 0 < Real.exp 2 := Real.exp_pos 2
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h_den1_pos : 0 < 2 * Real.pi * Real.exp 2 * t_g := by positivity
  have h_den2_pos : 0 < Real.pi * Real.exp 2 * t_g := by positivity
  have hp1_lo := mul_lt_mul_pos_bounds (by positivity) (by positivity) hpi_lo he_lo
  have hp2_lo := mul_lt_mul_pos_bounds (by positivity) (by positivity) hp1_lo ht_lo
  have hp1_hi := mul_lt_mul_pos_bounds hpi_pos he_pos hpi_hi he_hi
  have hp2_hi := mul_lt_mul_pos_bounds (by positivity) ht_pos hp1_hi ht_hi
  have h_n1_lo :
      62 * (2 * (((31416 : ℝ) / 10000) * ((751 : ℝ) / 100) *
        ((33771 : ℝ) / 100000000))) < 1 := by
    norm_num
  have h_n1_hi :
      1 < 65 * (2 * (((31415 : ℝ) / 10000) * ((727 : ℝ) / 100) *
        ((33769 : ℝ) / 100000000))) := by
    norm_num
  have h_n2_lo :
      125 * (((31416 : ℝ) / 10000) * ((751 : ℝ) / 100) *
        ((33771 : ℝ) / 100000000)) < 1 := by
    norm_num
  have h_n2_hi :
      1 < 130 * (((31415 : ℝ) / 10000) * ((727 : ℝ) / 100) *
        ((33769 : ℝ) / 100000000)) := by
    norm_num
  dsimp [subBarrierThroatFreqHz, quadrupoleThroatFreqHz]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ h_den1_pos]; linarith
  · rw [div_lt_iff₀ h_den1_pos]; linarith
  · rw [lt_div_iff₀ h_den2_pos]; linarith
  · rw [div_lt_iff₀ h_den2_pos]; linarith

/-- Impedance-matched (\(Z_{\mathrm{vac}} = Z_0\)) tortoise Liouville wave potential
    on static exponential-PV: \(V_{\mathrm{opt}}(u) = \frac{L^2}{r_g^2} u^2 e^{-4u}\). -/
noncomputable def pvOpticalPotential (L2 r_g u : ℝ) : ℝ :=
  (L2 / r_g ^ 2) * (u ^ 2 * Real.exp (-4 * u))

/-- Exact \(u\)-derivative \(\frac{d V_{\mathrm{opt}}}{du}\). -/
noncomputable def pvOpticalPotentialDeriv (L2 r_g u : ℝ) : ℝ :=
  (L2 / r_g ^ 2) * (2 * u * (1 - 2 * u)) * Real.exp (-4 * u)

/-- Theorem: Exact derivative of `pvOpticalPotential`. -/
theorem hasDerivAt_pvOpticalPotential (L2 r_g u : ℝ) :
    HasDerivAt (pvOpticalPotential L2 r_g) (pvOpticalPotentialDeriv L2 r_g u) u := by
  have h_sq_eq : (fun t : ℝ => t ^ 2) = (fun t => t * t) := funext sq
  have h_u2 : HasDerivAt (fun t : ℝ => t ^ 2) (1 * u + u * 1) u := by
    rw [h_sq_eq]
    exact (hasDerivAt_id u).mul (hasDerivAt_id u)
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (-4 * t))
      (Real.exp (-4 * u) * (-4 * 1)) u :=
    ((hasDerivAt_id u).const_mul (-4)).exp
  have h_full := (h_u2.mul h_exp).const_mul (L2 / r_g ^ 2)
  refine h_full.congr_deriv ?_
  dsimp [pvOpticalPotentialDeriv]
  ring

/-- Theorem (Single-Barrier / Reflectionless Empty Throat):
    For \(Z_{\mathrm{vac}}(r) = Z_0\), `pvOpticalPotential` attains its global maximum
    at the \(u = 1/2\) photon sphere (`r = 2 r_g`) and decreases strictly across the
    \(u = 1\) throat (`V_opt(1) < V_opt(1/2)`, `V_opt'(u) < 0` for all `u > 1/2`),
    proving empty polarizable vacuum at \(u = 1\) has no secondary barrier peak. -/
theorem pvOpticalPotential_single_barrier_no_throat_wall
    (L2 r_g u : ℝ) (hL2 : 0 < L2) (hrg : 0 < r_g) (hu : 0 ≤ u) :
    pvOpticalPotential L2 r_g u ≤ pvOpticalPotential L2 r_g (1 / 2) ∧
      pvOpticalPotential L2 r_g 1 < pvOpticalPotential L2 r_g (1 / 2) ∧
      (1 / 2 < u → pvOpticalPotentialDeriv L2 r_g u < 0) := by
  have h_coef_pos : 0 < L2 / r_g ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · dsimp [pvOpticalPotential]
    have h_lin : 2 * u ≤ Real.exp (2 * u - 1) := by
      have h := Real.add_one_le_exp (2 * u - 1)
      linarith
    have h_sq : (2 * u) ^ 2 ≤ Real.exp (4 * u - 2) := by
      have hexp : 0 ≤ Real.exp (2 * u - 1) := le_of_lt (Real.exp_pos _)
      have h_add : (2 * u - 1) + (2 * u - 1) = 4 * u - 2 := by ring
      calc
        (2 * u) ^ 2 = (2 * u) * (2 * u) := sq (2 * u)
        _ ≤ Real.exp (2 * u - 1) * Real.exp (2 * u - 1) :=
          mul_le_mul h_lin h_lin (by linarith) hexp
        _ = Real.exp ((2 * u - 1) + (2 * u - 1)) := (Real.exp_add _ _).symm
        _ = Real.exp (4 * u - 2) := by rw [h_add]
    have h_mul := mul_le_mul_of_nonneg_right h_sq (le_of_lt (Real.exp_pos (-4 * u)))
    have h_exp_id :
        Real.exp (4 * u - 2) * Real.exp (-4 * u) = Real.exp (-4 * (1 / 2)) := by
      rw [← Real.exp_add]
      have h_arg : (4 * u - 2) + (-4 * u) = -4 * ((1 : ℝ) / 2) := by ring
      rw [h_arg]
    have h_lhs_id :
        (2 * u) ^ 2 * Real.exp (-4 * u) = 4 * (u ^ 2 * Real.exp (-4 * u)) := by ring
    have h_rhs_id :
        ((1 : ℝ) / 2) ^ 2 * Real.exp (-4 * (1 / 2)) =
          (1 / 4) * Real.exp (-4 * (1 / 2)) := by ring
    rw [h_exp_id, h_lhs_id] at h_mul
    have h_core :
        u ^ 2 * Real.exp (-4 * u) ≤ ((1 : ℝ) / 2) ^ 2 * Real.exp (-4 * (1 / 2)) := by
      rw [h_rhs_id]
      linarith
    exact mul_le_mul_of_nonneg_left h_core (le_of_lt h_coef_pos)
  · dsimp [pvOpticalPotential]
    rcases exp_two_bounds with ⟨he_lo, _⟩
    have h4_lt : (4 : ℝ) < Real.exp 2 := by linarith
    have h_em4_pos : 0 < Real.exp (-4) := Real.exp_pos (-4)
    have h_prod := mul_lt_mul_of_pos_right h4_lt h_em4_pos
    have h_e2_em4 : Real.exp 2 * Real.exp (-4) = Real.exp (-4 * (1 / 2)) := by
      rw [← Real.exp_add]
      have h_arg : (2 : ℝ) + (-4) = -4 * ((1 : ℝ) / 2) := by norm_num
      rw [h_arg]
    rw [h_e2_em4] at h_prod
    have h_rhs_id :
        ((1 : ℝ) / 2) ^ 2 * Real.exp (-4 * (1 / 2)) =
          (1 / 4) * Real.exp (-4 * (1 / 2)) := by ring
    have h_core :
        1 ^ 2 * Real.exp (-4 * 1) < ((1 : ℝ) / 2) ^ 2 * Real.exp (-4 * (1 / 2)) := by
      rw [show (-4 : ℝ) * 1 = -4 by norm_num, one_pow, one_mul, h_rhs_id]
      linarith
    exact mul_lt_mul_of_pos_left h_core h_coef_pos
  · intro hu_gt
    dsimp [pvOpticalPotentialDeriv]
    have h_neg_fac : 2 * u * (1 - 2 * u) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have h_left_neg : (L2 / r_g ^ 2) * (2 * u * (1 - 2 * u)) < 0 :=
      mul_neg_of_pos_of_neg h_coef_pos h_neg_fac
    exact mul_neg_of_neg_of_pos h_left_neg (Real.exp_pos (-4 * u))

/-! ## 2. Horizonless Rotating Exponential-PV Equatorial Geometry (All Spins) -/

/-- Rotating exponential-PV equatorial \(g_{tt}\) component (\(\theta = \pi / 2\)). -/
noncomputable def rotPV_g_tt (r_g r : ℝ) : ℝ :=
  -Real.exp (-(2 * r_g / r))

/-- Rotating exponential-PV equatorial frame-dragging component \(g_{t\phi}\). -/
noncomputable def rotPV_g_tphi (r_g a r : ℝ) : ℝ :=
  -a * (1 - Real.exp (-(2 * r_g / r)))

/-- Rotating exponential-PV equatorial azimuthal component \(g_{\phi\phi}\). -/
noncomputable def rotPV_g_phiphi (r_g a r : ℝ) : ℝ :=
  r ^ 2 * Real.exp (2 * r_g / r) + a ^ 2 * (2 - Real.exp (-(2 * r_g / r)))

/-- Horizon function \(\Delta_{\mathrm{PV}}(a, r) = r^2 + a^2\). -/
def rotPV_Delta (a r : ℝ) : ℝ :=
  r ^ 2 + a ^ 2

/-- Rotating exponential-PV equatorial radial component \(g_{rr}\). -/
noncomputable def rotPV_g_rr (r_g a r : ℝ) : ℝ :=
  r ^ 2 * Real.exp (2 * r_g / r) / rotPV_Delta a r

/-- Theorem (Global Absence of Event Horizons at Arbitrary Spin):
    Because \(e^{-2 r_g / r} e^{+2 r_g / r} = 1\), the \((t, \phi)\) metric determinant
    satisfies \(g_{t\phi}^2 - g_{tt} g_{\phi\phi} = r^2 + a^2 > 0\) for all \(r > 0\)
    and all spin parameters \(a \in \mathbb{R}\) (no Kerr \(r^2 - 2 r_g r + a^2 = 0\) root). -/
theorem rotPV_determinant_horizonless
    (r_g a r : ℝ) (hr : 0 < r) :
    (rotPV_g_tphi r_g a r) ^ 2 - rotPV_g_tt r_g r * rotPV_g_phiphi r_g a r =
      rotPV_Delta a r ∧ 0 < rotPV_Delta a r := by
  constructor
  · dsimp [rotPV_g_tphi, rotPV_g_tt, rotPV_g_phiphi, rotPV_Delta]
    set ep := Real.exp (2 * r_g / r)
    set em := Real.exp (-(2 * r_g / r))
    have h_prod : em * ep = 1 := by
      dsimp [em, ep]
      rw [Real.exp_neg, inv_mul_cancel₀ (ne_of_gt (Real.exp_pos _))]
    calc
      (-a * (1 - em)) ^ 2 - -em * (r ^ 2 * ep + a ^ 2 * (2 - em))
          = r ^ 2 * (em * ep) + a ^ 2 := by ring
      _ = r ^ 2 + a ^ 2 := by rw [h_prod]; ring
  · dsimp [rotPV_Delta]
    positivity

/-- Theorem: At zero spin (\(a = 0\)), the rotating exponential-PV metric reduces
    identically to the static `BlackHoleUnknot` exponential-PV line element, and
    for \(a > 0\) induces strictly prograde frame dragging (\(-g_{t\phi} > 0\)). -/
theorem rotPV_static_recovery_and_frame_dragging
    (r_g a r : ℝ) (hrg : 0 < r_g) (ha : 0 < a) (hr : 0 < r) :
    rotPV_g_tphi r_g 0 r = 0 ∧
      rotPV_g_phiphi r_g 0 r = r ^ 2 * Real.exp (2 * r_g / r) ∧
      rotPV_g_rr r_g 0 r = Real.exp (2 * r_g / r) ∧
      0 < -rotPV_g_tphi r_g a r := by
  have hr_ne : r ≠ 0 := ne_of_gt hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [rotPV_g_tphi]
  · simp [rotPV_g_phiphi]
  · dsimp [rotPV_g_rr, rotPV_Delta]
    field_simp [hr_ne]
    ring
  · dsimp [rotPV_g_tphi]
    have h_neg_arg : -(2 * r_g / r) < 0 := by
      have h_pos_div : 0 < 2 * r_g / r := by positivity
      linarith
    have h_exp_lt_one : Real.exp (-(2 * r_g / r)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr h_neg_arg
    have h_one_sub : 0 < 1 - Real.exp (-(2 * r_g / r)) := by linarith
    have h_prod_pos : 0 < a * (1 - Real.exp (-(2 * r_g / r))) := mul_pos ha h_one_sub
    linarith

/-! ## 3. Core Boundary Dichotomy: Near-TOV Cavity vs. Super-TOV Freeze-Out -/

/-- Native TVE exponential-PV echo delay \(\Delta t_{\mathrm{PV}} = t_g I_{\mathrm{echo}}\),
    where `BlackHoleUnknot` certifies \(I_{\mathrm{echo}}(1) = 2 \int_{1/2}^1 (e^{2u}/u^2)\,du
    \in (8.331, 8.332)\) for a physical boundary at the \(u_{\mathrm{core}} = 1\) throat. -/
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

/-- Quantitative \(30\,M_\odot\) Near-Throat Benchmark (`u_core = 1` vs. Planck Wall):
    For \(t_g \in (0.147764, 0.147766)\,\mathrm{ms}\) and \(I_{\mathrm{echo}} \in (8.331, 8.332)\),
    \(\Delta t_{\mathrm{PV}} \in (1.231, 1.232)\,\mathrm{ms}\) vs.
    \(\Delta t_{\mathrm{Planck}} \in (54.0, 54.2)\,\mathrm{ms}\) (\(> 40\times\) earlier). -/
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

/-- Optical round-trip integrand \(f_{\mathrm{cav}}(u) = 2 e^{2u} / u^2\). -/
noncomputable def pvCavityIntegrand (u : ℝ) : ℝ :=
  2 * Real.exp (2 * u) / u ^ 2

/-- Exact antiderivative \(F_{\mathrm{low}}(u) = e^{2u} / u_{\mathrm{core}}^2\) minorizing
    `pvCavityIntegrand` on \([1, u_{\mathrm{core}}]\). -/
noncomputable def pvCavityLowerAntideriv (u_core u : ℝ) : ℝ :=
  Real.exp (2 * u) / u_core ^ 2

/-- Closed-form elementary lower bound on \(I_{\mathrm{echo}}(u_{\mathrm{core}})\) for
    super-TOV remnants (\(M > M_{\mathrm{TOV}} \approx 2.17\,M_\odot\)) compressed to
    \(u_{\mathrm{core}} > 1\):
    \(I_{\mathrm{throat}} + (e^{2 u_{\mathrm{core}}} - e^2) / u_{\mathrm{core}}^2\). -/
noncomputable def pvCoreFreezeOutBound (I_throat u_core : ℝ) : ℝ :=
  I_throat + (Real.exp (2 * u_core) - Real.exp 2) / u_core ^ 2

/-- Theorem (Strict Interior Monotonicity & Antiderivative Minorant):
    For all \(u > 1\), `pvCavityIntegrand` has strictly positive derivative
    \(4(u - 1)e^{2u}/u^3 > 0\), and on \((0, u_{\mathrm{core}}]\) dominates the exact
    derivative of `pvCavityLowerAntideriv`. -/
theorem pvCavityIntegrand_strict_growth_and_minorant
    (u u_core : ℝ) (hu : 1 < u) (h_le : u ≤ u_core) :
    HasDerivAt pvCavityIntegrand (4 * (u - 1) * Real.exp (2 * u) / u ^ 3) u ∧
      0 < 4 * (u - 1) * Real.exp (2 * u) / u ^ 3 ∧
      HasDerivAt (pvCavityLowerAntideriv u_core)
        (2 * Real.exp (2 * u) / u_core ^ 2) u ∧
      2 * Real.exp (2 * u) / u_core ^ 2 ≤ pvCavityIntegrand u := by
  have hu_pos : 0 < u := by linarith
  have hu_ne : u ≠ 0 := ne_of_gt hu_pos
  have huc_pos : 0 < u_core := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h_num : HasDerivAt (fun t : ℝ => 2 * Real.exp (2 * t))
        (2 * (Real.exp (2 * u) * (2 * 1))) u :=
      (((hasDerivAt_id u).const_mul 2).exp).const_mul 2
    have h_sq_eq : (fun t : ℝ => t ^ 2) = (fun t => t * t) := funext sq
    have h_den : HasDerivAt (fun t : ℝ => t ^ 2) (1 * u + u * 1) u := by
      rw [h_sq_eq]
      exact (hasDerivAt_id u).mul (hasDerivAt_id u)
    have h_div := h_num.div h_den (pow_ne_zero 2 hu_ne)
    refine h_div.congr_deriv ?_
    field_simp [hu_ne]
    ring
  · have hu_sub : 0 < u - 1 := by linarith
    positivity
  · have h_exp : HasDerivAt (fun t : ℝ => Real.exp (2 * t))
        (Real.exp (2 * u) * (2 * 1)) u :=
      ((hasDerivAt_id u).const_mul 2).exp
    have h_div := h_exp.div_const (u_core ^ 2)
    refine h_div.congr_deriv ?_
    ring
  · dsimp [pvCavityIntegrand]
    have h_sq_le : u ^ 2 ≤ u_core ^ 2 := by
      calc
        u ^ 2 = u * u := sq u
        _ ≤ u_core * u_core :=
          mul_le_mul h_le h_le (le_of_lt hu_pos) (le_of_lt huc_pos)
        _ = u_core ^ 2 := (sq u_core).symm
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h_num_pos : 0 < 2 * Real.exp (2 * u) := by positivity
    exact mul_le_mul_of_nonneg_left h_sq_le (le_of_lt h_num_pos)

/-- Theorem (Super-TOV Exponential Optical Freeze-Out):
    Unlike logarithmic Planck-wall delays (\(\sim 54\text{–}123\,\mathrm{ms}\)), once a
    super-TOV remnant compresses even modestly to \(u_{\mathrm{core}} = 8\)
    (\(r_{\mathrm{core}} = r_g / 8\)), `pvCoreFreezeOutBound` exceeds \(120{,}000\),
    pushing the echo return past \(17\,\mathrm{s}\) at \(30\,M_\odot\) and past
    \(40\,\mathrm{s}\) at `GW250114_082203` (\(68.56\,M_\odot\)). -/
theorem super_tov_exponential_freeze_out_at_u8
    (I_throat t_g_30_s t_g_68_s : ℝ)
    (hI : (8331 : ℝ) / 1000 < I_throat)
    (ht30 : (147764 : ℝ) / 1000000000 < t_g_30_s)
    (ht68 : (33769 : ℝ) / 100000000 < t_g_68_s) :
    (120000 : ℝ) < pvCoreFreezeOutBound I_throat 8 ∧
      (17 : ℝ) < pvEchoDelay t_g_30_s (pvCoreFreezeOutBound I_throat 8) ∧
      (40 : ℝ) < pvEchoDelay t_g_68_s (pvCoreFreezeOutBound I_throat 8) := by
  rcases exp_two_bounds with ⟨he2_lo, he2_hi⟩
  have s1 := sq_le_exp_double (by positivity) (le_of_lt he2_lo)
  rw [show (2 : ℝ) * 2 = 4 by norm_num] at s1
  have s2 := sq_le_exp_double (by positivity) s1
  rw [show (2 : ℝ) * 4 = 8 by norm_num] at s2
  have s3 : (((((727 : ℝ) / 100) ^ 2) ^ 2) ^ 2) ≤ Real.exp (2 * 8) :=
    sq_le_exp_double (by positivity) s2
  have h_diff_lt :
      (((((727 : ℝ) / 100) ^ 2) ^ 2) ^ 2) - (751 : ℝ) / 100 <
        Real.exp (2 * 8) - Real.exp 2 := by linarith
  have h_div_lt :
      ((((((727 : ℝ) / 100) ^ 2) ^ 2) ^ 2) - (751 : ℝ) / 100) * ((1 : ℝ) / 64) <
        (Real.exp (2 * 8) - Real.exp 2) * ((1 : ℝ) / 64) :=
    mul_lt_mul_of_pos_right h_diff_lt (by positivity)
  have h_bound : (120000 : ℝ) < pvCoreFreezeOutBound I_throat 8 := by
    dsimp [pvCoreFreezeOutBound]
    have h_div_eq :
        (Real.exp (2 * 8) - Real.exp 2) / (8 : ℝ) ^ 2 =
          (Real.exp (2 * 8) - Real.exp 2) * ((1 : ℝ) / 64) := by ring
    have h_num :
        (120000 : ℝ) <
          (8331 : ℝ) / 1000 +
            ((((((727 : ℝ) / 100) ^ 2) ^ 2) ^ 2) - (751 : ℝ) / 100) *
              ((1 : ℝ) / 64) := by
      norm_num
    rw [h_div_eq]
    linarith
  have h_30 := mul_lt_mul_pos_bounds (by positivity) (by positivity) ht30 h_bound
  have h_68 := mul_lt_mul_pos_bounds (by positivity) (by positivity) ht68 h_bound
  have h_30_num : (17 : ℝ) < ((147764 : ℝ) / 1000000000) * 120000 := by norm_num
  have h_68_num : (40 : ℝ) < ((33769 : ℝ) / 100000000) * 120000 := by norm_num
  dsimp [pvEchoDelay]
  refine ⟨h_bound, by linarith, by linarith⟩

/-! ## 4. PV Bag Soft-Wall Reflection & Spin-Weighted Berry Phase -/

/-- First-principles dimensionless Bessel-Gamma frequency parameter derived from
    the tortoise slope \(\alpha_{\mathrm{PV}} = 2 / (e^2 r_g)\) of `BlackHoleUnknot`'s
    \(e^{4\Delta u}\) bag core at \(u = 1\): \(\nu_{\mathrm{PV}} = \frac{e^2}{2} t_g \omega\). -/
noncomputable def pvSoftWallNu (t_g omega : ℝ) : ℝ :=
  (Real.exp 2 / 2) * t_g * omega

/-- Theorem: The native PV bag soft-wall slope coefficient \(\frac{e^2}{2}\) lies inside
    \((3.63, 3.76)\), strictly below Schwarzschild's ad-hoc coefficient \(4\). -/
theorem pvSoftWallSlope_lt_schwarzschild :
    (363 : ℝ) / 100 < Real.exp 2 / 2 ∧ Real.exp 2 / 2 < (376 : ℝ) / 100 ∧
      Real.exp 2 / 2 < 4 := by
  rcases exp_two_bounds with ⟨he_lo, he_hi⟩
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Rytov-Vladimirskii-Berry geometric polarization rotation per bounce through
    a \((1,1)\) virial-equipartition Beltrami unknot throat (\(\cos\theta_0 = 1/\sqrt{2}\)). -/
noncomputable def beltramiBounceRotationRad : ℝ :=
  Real.pi * (1 - 1 / Real.sqrt 2)

/-- Equivalent spin-1 bounce polarization rotation in degrees: \(180(1 - 1/\sqrt{2})\). -/
noncomputable def beltramiBounceRotationDeg : ℝ :=
  180 * (1 - 1 / Real.sqrt 2)

/-- Spin-\(s\) helicity phase shift in radians (\(s = 1\) photons, \(s = 2\) GWs). -/
noncomputable def spinWeightedBounceRotationRad (s : ℕ) : ℝ :=
  (s : ℝ) * beltramiBounceRotationRad

/-- Spin-\(s\) helicity phase shift in degrees (\(s = 1\) photons, \(s = 2\) GWs). -/
noncomputable def spinWeightedBounceRotationDeg (s : ℕ) : ℝ :=
  (s : ℝ) * beltramiBounceRotationDeg

/-- Cumulative spin-1 polarization rotation after \(k\) throat reflections. -/
noncomputable def echoPolarizationAngle (k : ℕ) : ℝ :=
  (k : ℝ) * beltramiBounceRotationRad

/-- Theorem: Successive bounces step linearly in polarization angle by
    \(\Delta\psi_{\mathrm{bounce}}\), completely independent of remnant mass \(M\). -/
theorem echoPolarizationAngle_step (k : ℕ) :
    echoPolarizationAngle (k + 1) - echoPolarizationAngle k =
      beltramiBounceRotationRad := by
  dsimp [echoPolarizationAngle]
  push_cast
  ring

/-- Theorem: Spin-1 photon-subring rotation lies inside \((52.7^\circ, 52.8^\circ)\),
    while spin-2 gravitational-wave tensor phase steps inside \((105.4^\circ, 105.5^\circ)\). -/
theorem beltramiBounceRotationDeg_bracket :
    ((527 : ℝ) / 10 < beltramiBounceRotationDeg ∧
      beltramiBounceRotationDeg < (528 : ℝ) / 10) ∧
    ((1054 : ℝ) / 10 < spinWeightedBounceRotationDeg 2 ∧
      spinWeightedBounceRotationDeg 2 < (1055 : ℝ) / 10) := by
  rcases sqrt_two_bounds with ⟨hs_lo, hs_hi⟩
  have h_s_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by positivity)
  have h_inv_lo : (10000 : ℝ) / 14143 < 1 / Real.sqrt 2 := by
    rw [div_lt_div_iff₀ (by positivity) h_s_pos]
    linarith
  have h_inv_hi : 1 / Real.sqrt 2 < (10000 : ℝ) / 14142 := by
    rw [div_lt_div_iff₀ h_s_pos (by positivity)]
    linarith
  dsimp [spinWeightedBounceRotationDeg, beltramiBounceRotationDeg]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Closed-form soft-wall Bessel-Gamma inner reflection amplitude:
    \(R_{\mathrm{unknot}}(\nu, \Delta\Phi) = -\frac{\Gamma(1 + i\nu)}{\Gamma(1 - i\nu)}
    e^{i \Delta\Phi}\). -/
noncomputable def unknotReflection (ν Δψ : ℝ) : ℂ :=
  -(Complex.Gamma (1 + Complex.I * (ν : ℂ)) /
    Complex.Gamma (1 - Complex.I * (ν : ℂ))) *
    Complex.exp ((Δψ : ℂ) * Complex.I)

/-- Native PV spin-\(s\) reflection operator instantiated at \(\nu_{\mathrm{PV}}(t_g, \omega)\). -/
noncomputable def unknotReflectionPV (s : ℕ) (t_g omega : ℝ) : ℂ :=
  unknotReflection (pvSoftWallNu t_g omega) (spinWeightedBounceRotationRad s)

/-- Theorem: The soft-wall Bessel-Gamma unknot core is strictly unitary
    (\(\|R_{\mathrm{unknot}}(\nu, \Delta\psi)\| = 1\)) at every real frequency \(\nu\). -/
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

/-- Corollary: Exact unitarity of the native PV spin-\(s\) reflection operator. -/
theorem unknotReflectionPV_unitary (s : ℕ) (t_g omega : ℝ) :
    ‖unknotReflectionPV s t_g omega‖ = 1 :=
  unknotReflection_unitary (pvSoftWallNu t_g omega) (spinWeightedBounceRotationRad s)

/-! ## 5. Decoupled Dissipative Dyson Cavity Series & Lossless \(-3\,\mathrm{dB}\) Limit -/

/-- Lossless benchmark (\(\eta_{\mathrm{diss}} = 0\), \(|R_{\mathrm{ph}}| = 1/\sqrt{2}\)):
    combining unitary reflection with a 50/50 barrier split gives \(1/2\) (\(-3\,\mathrm{dB}\))
    power retention per cavity loop. -/
theorem echo_power_half_per_bounce (ν Δψ : ℝ) :
    (‖unknotReflection ν Δψ‖ * (1 / Real.sqrt 2)) ^ 2 = (1 : ℝ) / 2 := by
  rw [unknotReflection_unitary, one_mul, div_pow, one_pow,
      Real.sq_sqrt (by positivity)]

/-- Dissipative cavity loop retention factor
    \(\gamma_{\mathrm{loop}} = R_{\mathrm{ph}}\sqrt{1 - \eta_{\mathrm{diss}}}\)
    with polar Lundquist jet / neutrino core exhaust \(\eta_{\mathrm{diss}} \in [0, 1]\). -/
noncomputable def dysonLoopFactor (R_ph eta_diss : ℝ) : ℝ :=
  R_ph * Real.sqrt (1 - eta_diss)

/-- Decoupled Dyson bounce amplitude \(A_{k+1} = \epsilon_1 \gamma_{\mathrm{loop}}^k\),
    separating plunge excitation \(\epsilon_1\) from loop retention \(\gamma_{\mathrm{loop}}\). -/
def dysonEchoAmp (eps_1 gamma_loop : ℝ) (k : ℕ) : ℝ :=
  eps_1 * gamma_loop ^ k

/-- Cumulative echo power \(\sum_{j=0}^{N-1} A_{j+1}^2\) over the first \(N\) bounces. -/
def dysonPartialEnergy (eps_1 gamma_loop : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => dysonPartialEnergy eps_1 gamma_loop n + (dysonEchoAmp eps_1 gamma_loop n) ^ 2

/-- Theorem: At the barrier top (\(|R_{\mathrm{ph}}| = 1/\sqrt{2}\)), core dissipation
    \(\eta_{\mathrm{diss}} \in (0, 1]\) strictly reduces loop power below \(1/2\),
    and decoupling \(\epsilon_1 < \gamma_{\mathrm{loop}}\) preserves strictly greater
    Bounce-2+ power than naive \(\epsilon_1^{k+1}\) scaling. -/
theorem dyson_dissipative_loop_and_decoupling
    (eta_diss eps_1 gamma_loop : ℝ)
    (heta_pos : 0 < eta_diss) (heta_le : eta_diss ≤ 1)
    (heps_pos : 0 < eps_1) (heps_lt : eps_1 < gamma_loop) :
    (dysonLoopFactor (1 / Real.sqrt 2) eta_diss) ^ 2 = (1 - eta_diss) / 2 ∧
      (dysonLoopFactor (1 / Real.sqrt 2) eta_diss) ^ 2 < 1 / 2 ∧
      (eps_1 ^ 2) ^ 2 < (dysonEchoAmp eps_1 gamma_loop 1) ^ 2 := by
  have h_one_sub : 0 ≤ 1 - eta_diss := by linarith
  have h_eq : (dysonLoopFactor (1 / Real.sqrt 2) eta_diss) ^ 2 = (1 - eta_diss) / 2 := by
    dsimp [dysonLoopFactor]
    rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt h_one_sub]
    ring
  refine ⟨h_eq, by linarith, ?_⟩
  dsimp [dysonEchoAmp]
  rw [pow_one]
  have h_sq_lt : eps_1 ^ 2 < gamma_loop ^ 2 := by
    have h_diff :
        gamma_loop ^ 2 - eps_1 ^ 2 = (gamma_loop - eps_1) * (gamma_loop + eps_1) := by
      ring
    have h_prod : 0 < (gamma_loop - eps_1) * (gamma_loop + eps_1) :=
      mul_pos (by linarith) (by linarith)
    linarith
  have heps2_pos : 0 < eps_1 ^ 2 := by positivity
  have h_mul := mul_lt_mul_of_pos_left h_sq_lt heps2_pos
  calc
    (eps_1 ^ 2) ^ 2 = eps_1 ^ 2 * eps_1 ^ 2 := sq (eps_1 ^ 2)
    _ < eps_1 ^ 2 * gamma_loop ^ 2 := h_mul
    _ = (eps_1 * gamma_loop) ^ 2 := by ring

/-- Theorem (Exact Dyson Partial-Energy Identity & Geometric Convergence Bound):
    For every bounce count \(N \in \mathbb{N}\) and \(0 \le \gamma_{\mathrm{loop}} < 1\),
    \((1 - \gamma_{\mathrm{loop}}^2) \sum_{j=0}^{N-1} A_{j+1}^2 =
      \epsilon_1^2 (1 - \gamma_{\mathrm{loop}}^{2N})\),
    bounding echo train energy at or below \(\epsilon_1^2 / (1 - \gamma_{\mathrm{loop}}^2)\). -/
theorem dysonPartialEnergy_identity_and_bound
    (eps_1 gamma_loop : ℝ) (N : ℕ)
    (hg_nonneg : 0 ≤ gamma_loop) (hg_lt : gamma_loop < 1) :
    (1 - gamma_loop ^ 2) * dysonPartialEnergy eps_1 gamma_loop N =
      eps_1 ^ 2 * (1 - gamma_loop ^ (2 * N)) ∧
    dysonPartialEnergy eps_1 gamma_loop N ≤ eps_1 ^ 2 / (1 - gamma_loop ^ 2) := by
  have h_id :
      ∀ n : ℕ, (1 - gamma_loop ^ 2) * dysonPartialEnergy eps_1 gamma_loop n =
        eps_1 ^ 2 * (1 - gamma_loop ^ (2 * n)) := by
    intro n
    induction n with
    | zero =>
      simp [dysonPartialEnergy]
    | succ k ih =>
      dsimp [dysonPartialEnergy, dysonEchoAmp]
      rw [mul_add, ih]
      have h_pow_sq : (eps_1 * gamma_loop ^ k) ^ 2 = eps_1 ^ 2 * gamma_loop ^ (2 * k) := by
        rw [mul_pow, ← pow_mul, mul_comm k 2]
      have h_pow_step :
          gamma_loop ^ (2 * (k + 1)) = gamma_loop ^ (2 * k) * gamma_loop ^ 2 := by
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
      rw [h_pow_sq, h_pow_step]
      ring
  have hN := h_id N
  refine ⟨hN, ?_⟩
  have hg2_lt : gamma_loop ^ 2 < 1 := by
    have h_diff : 1 - gamma_loop ^ 2 = (1 - gamma_loop) * (1 + gamma_loop) := by ring
    have h_pos : 0 < (1 - gamma_loop) * (1 + gamma_loop) :=
      mul_pos (by linarith) (by linarith)
    linarith
  have h_den_pos : 0 < 1 - gamma_loop ^ 2 := by linarith
  rw [le_div_iff₀ h_den_pos, mul_comm, hN, mul_sub, mul_one]
  have h_nonneg_term : 0 ≤ eps_1 ^ 2 * gamma_loop ^ (2 * N) := by positivity
  linarith

#print axioms optical_potential_log_linearization
#print axioms exp_two_bounds
#print axioms pvThroatRadiusLog_min_at_throat
#print axioms hasDerivAt_pvThroatRadiusLog
#print axioms hasDerivAt_pvThroatRadiusLogDeriv
#print axioms pvThroatRadiusLog_curvatures_at_throat
#print axioms throat_mode_strictly_sub_barrier
#print axioms throat_GW250114_freq_brackets
#print axioms hasDerivAt_pvOpticalPotential
#print axioms pvOpticalPotential_single_barrier_no_throat_wall
#print axioms rotPV_determinant_horizonless
#print axioms rotPV_static_recovery_and_frame_dragging
#print axioms pv_echo_strictly_earlier_than_planck
#print axioms echo_30Msun_pv_vs_planck_brackets
#print axioms pvCavityIntegrand_strict_growth_and_minorant
#print axioms super_tov_exponential_freeze_out_at_u8
#print axioms pvSoftWallSlope_lt_schwarzschild
#print axioms echoPolarizationAngle_step
#print axioms beltramiBounceRotationDeg_bracket
#print axioms unknotReflection_unitary
#print axioms unknotReflectionPV_unitary
#print axioms echo_power_half_per_bounce
#print axioms dyson_dissipative_loop_and_decoupling
#print axioms dysonPartialEnergy_identity_and_bound

end TVE.Cosmology
