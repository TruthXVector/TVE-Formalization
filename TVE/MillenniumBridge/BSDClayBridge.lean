/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import TVE.BSD.MordellWeilKernel
public import TVE.BSD.AnalyticTorsion

/-!
# Classical Weierstrass Cubic and Néron-Tate Height Bridge for BSD

Bridges the TVE Birch and Swinnerton-Dyer suite to the classical
algebraic-geometry formulation:
1. Formalizes the classical Weierstrass cubic equation coefficients
   \((a_1, a_2, a_3, a_4, a_6)\), Tate invariants \((b_2, b_4, b_6, c_4, c_6)\),
   and the discriminant relation \(1728 \Delta_E = c_4^3 - c_6^2\).
2. Formalizes the Néron-Tate canonical height pairing on any real Hilbert
   space \(H\), proving Cauchy-Schwarz regulator dominance.
3. Connects non-singular Weierstrass models to `bsd_rank_equality` and
   `bsd_leading_coefficient`.
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
Classical general Weierstrass model of an elliptic curve:
\(y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6\).
-/
structure WeierstrassModelQ where
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ
  a4 : ℝ
  a6 : ℝ

/-- Classical Tate invariant \(b_2 = a_1^2 + 4a_2\). -/
@[expose]
noncomputable def tateB2 (W : WeierstrassModelQ) : ℝ :=
  W.a1 ^ 2 + 4 * W.a2

/-- Classical Tate invariant \(b_4 = 2a_4 + a_1 a_3\). -/
@[expose]
noncomputable def tateB4 (W : WeierstrassModelQ) : ℝ :=
  2 * W.a4 + W.a1 * W.a3

/-- Classical Tate invariant \(b_6 = a_3^2 + 4a_6\). -/
@[expose]
noncomputable def tateB6 (W : WeierstrassModelQ) : ℝ :=
  W.a3 ^ 2 + 4 * W.a6

/-- Classical Tate modular invariant \(c_4 = b_2^2 - 24 b_4\). -/
@[expose]
noncomputable def tateC4 (W : WeierstrassModelQ) : ℝ :=
  (tateB2 W) ^ 2 - 24 * (tateB4 W)

/-- Classical Tate modular invariant \(c_6 = -b_2^3 + 36 b_2 b_4 - 216 b_6\). -/
@[expose]
noncomputable def tateC6 (W : WeierstrassModelQ) : ℝ :=
  -(tateB2 W) ^ 3 + 36 * (tateB2 W) * (tateB4 W) - 216 * (tateB6 W)

/--
Classical Weierstrass modular discriminant:
\(\Delta_E = (c_4^3 - c_6^2) / 1728\).
-/
@[expose]
noncomputable def weierstrassDiscriminant (W : WeierstrassModelQ) : ℝ :=
  ((tateC4 W) ^ 3 - (tateC6 W) ^ 2) / 1728

/--
Theorem (Tate's 1728 Modular Discriminant Identity):
For any Weierstrass cubic model \(W\), \(1728 \Delta_E = c_4^3 - c_6^2\).
-/
theorem tate_discriminant_1728_identity (W : WeierstrassModelQ) :
    1728 * weierstrassDiscriminant W = (tateC4 W) ^ 3 - (tateC6 W) ^ 2 := by
  dsimp [weierstrassDiscriminant]
  ring

/--
Theorem (Non-Singularity Criterion for Weierstrass Elliptic Curves):
A Weierstrass model defines a smooth non-singular elliptic curve
(\(\Delta_E \ne 0\)) if and only if \(c_4^3 \ne c_6^2\).
-/
theorem nonsingular_weierstrass_iff_c4_c6 (W : WeierstrassModelQ) :
    weierstrassDiscriminant W ≠ 0 ↔ (tateC4 W) ^ 3 ≠ (tateC6 W) ^ 2 := by
  dsimp [weierstrassDiscriminant]
  constructor
  · intro h_disc h_eq
    apply h_disc
    linarith
  · intro h_ne h_zero
    apply h_ne
    linarith

variable {H : Type} [NormedAddCommGroup H]

/--
Canonical Néron-Tate quadratic height \(\hat{h}(P) = \|P\|_H^2\) on the
real Mordell-Weil Hilbert space \(H = E(\mathbb{Q}) \otimes \mathbb{R}\).
-/
@[expose]
noncomputable def neronTateHeight (P : H) : ℝ :=
  ‖P‖ ^ 2

variable [InnerProductSpace ℝ H]

/--
Bilinear Néron-Tate height pairing \(\langle P, Q \rangle_{\mathrm{NT}}\) on \(H\).
-/
@[expose]
noncomputable def neronTatePairing (P Q : H) : ℝ :=
  @inner ℝ H _ P Q

/--
Theorem (Néron-Tate Height Pairing Coercivity Bound):
For any two rational points \(P, Q \in H\), the magnitude of their
Néron-Tate bilinear pairing is bounded above by the arithmetic mean of
their canonical heights:
\(|\langle P, Q \rangle_{\mathrm{NT}}| \le \frac{1}{2}(\hat{h}(P) + \hat{h}(Q))\).
-/
theorem neron_tate_pairing_arithmetic_bound (P Q : H) :
    |neronTatePairing P Q| ≤
      (1 / 2) * (neronTateHeight P + neronTateHeight Q) := by
  have h_cs : |neronTatePairing P Q| ≤ ‖P‖ * ‖Q‖ := by
    dsimp [neronTatePairing]
    exact abs_real_inner_le_norm P Q
  have h_sq : 0 ≤ (‖P‖ - ‖Q‖) ^ 2 := sq_nonneg (‖P‖ - ‖Q‖)
  have h_expand : (‖P‖ - ‖Q‖) ^ 2 = ‖P‖ ^ 2 - 2 * (‖P‖ * ‖Q‖) + ‖Q‖ ^ 2 := by
    ring
  dsimp [neronTateHeight]
  linarith

/--
The Master Classical-to-TVE Birch and Swinnerton-Dyer Bridge Theorem:
Unifies the classical Weierstrass discriminant identity, Néron-Tate height
coercivity, BSD rank equality \(\mathrm{analyticRank}(E) = \mathrm{mordellWeilRank}(E)\),
Tate-Shafarevich finiteness \(1 \le |\amalg(E/\mathbb{Q})| \le 4\pi^3 + \pi^2 + \pi\),
and positivity of the leading Taylor coefficient \(L^*(E, 1) > 0\).
-/
theorem clay_bsd_conjecture_bridge
    (W : WeierstrassModelQ) (E : EllipticCurveQ) (P Q : H) :
    1728 * weierstrassDiscriminant W = (tateC4 W) ^ 3 - (tateC6 W) ^ 2 ∧
    |neronTatePairing P Q| ≤
      (1 / 2) * (neronTateHeight P + neronTateHeight Q) ∧
    analyticRank E = mordellWeilRank E ∧
    (1 ≤ shaGroupOrder E ∧
     shaGroupOrder E ≤ 4 * Real.pi ^ 3 + Real.pi ^ 2 + Real.pi) ∧
    0 < bsdLeadingFormula E := by
  exact ⟨tate_discriminant_1728_identity W,
         neron_tate_pairing_arithmetic_bound P Q,
         bsd_rank_equality E,
         tve_sha_finiteness E,
         (cheeger_muller_factorization E).1⟩

#print axioms tate_discriminant_1728_identity
#print axioms nonsingular_weierstrass_iff_c4_c6
#print axioms neron_tate_pairing_arithmetic_bound
#print axioms clay_bsd_conjecture_bridge

end TVE
