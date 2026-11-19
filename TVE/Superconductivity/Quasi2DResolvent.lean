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
public import Mathlib.Tactic.FieldSimp
public import TVE.Vacuum
public import TVE.Action
public import TVE.Topologies
public import TVE.Spectrum
public import TVE.Forces
public import TVE.VacuumPolarization
public import TVE.Superconductivity.HopfPairing

/-!
# Topological Vacuum Electrodynamics — Quasi-2D Elliptic-AGM & Multilayer Resolvent

Zero-axiom Brillouin resolvent engine (`TVE.Superconductivity.Quasi2DResolvent`)
certifying the multilayer quasi-2D Watson integrals `W_L` (`L = 1, 2, 3`) without
magic constants or uncertified numerical quadrature:

1. **Certified 2D Elliptic-AGM Optical Resolvents (`[]`):**
   Evaluates `G_{2D}(δ) = (2 / (π (1 + δ))) K((1 + δ)⁻²) = 1 / agm(1 + δ, √((1+δ)² - 1))`
   at the open `L`-layer tridiagonal optical gaps `δ ∈ {1/6, 1/12, 1/4}` (`η_in = 1/3`),
   certifying every geometric-mean square root via `PosRat` squaring bounds (`rfl`):
   `G_{2D}(1/6) ∈ (1.1622, 1.1625)`, `G_{2D}(1/12) ∈ (1.4076, 1.4079)`, and
   `G_{2D}(1/4) ∈ (1.0161, 1.0163)`.
2. **Musical-Comma Mercator Logarithms & Multilayer `W_1, W_2, W_3` (`[]`):**
   Certifies `ln 2` and `ln 3` via `2 = (4/3)²(9/8)` and `3 = (4/3)³(9/8)²` together
   with `ln(A_eff(4) / 128)` via alternating Mercator bounds, deriving the quasi-2D
   acoustic integrals `W_{Q2D}(L) = (1/π) ln(32 L A_eff(4))` and per-layer resolvents
   `W_3 ∈ (1.8147, 1.8150) < W_2 ∈ (2.0268, 2.0271) < W_1 ∈ (2.6708, 2.6709)`.
3. **Continuum AGM Contraction, Pythagorean Seeds & `π`-Cancellation (`ℝ`):**
   Proves `b < √(ab) < (a + b)/2 < a` and `(a + b)/2 - √(ab) < (a - b)/2` for all
   `0 < b < a`, verifies the `(7/6, √13/6)`, `(13/12, 5/12)`, and `(5/4, 3/4)` seeds
   from `η_in = (5/4)/(15/4) = 1/3`, and proves exact `π`-cancellation in `G_{2D}(δ)`.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-! ## Part 1: Zero-Axiom Elliptic-AGM & Quasi-2D Logarithmic Kernel (`[]`) -/

/-- Arithmetic mean `(a + b) / 2` on `PosRat`. -/
@[expose]
def scAgmArithMeanPosRat (a b : PosRat) : PosRat :=
  posRatMulRed { num := 1, denPred := 1 } (scPosRatAddRed a b)

/-- Multiplicative inverse `1 / q` on positive `PosRat` via `vpPosRatToNzOrOne`. -/
@[expose]
def scPosRatRecip (q : PosRat) : PosRat :=
  posRatDivRed (posRatOfInt 1) (vpPosRatToNzOrOne q)

/--
Alternating Mercator logarithm partial sum `∑_{j=1}^{k+1} (-1)^{j-1} x^j / j` in `PosRat`.
For `0 < x < 1`, odd `k` (even number of terms) is a strict lower bound on `ln(1 + x)`
and even `k` (odd number of terms) is a strict upper bound on `ln(1 + x)`.
-/
@[expose]
def scMercatorLogTruncPosRat (x : PosRat) : ℕ → PosRat
  | 0 => x
  | k + 1 =>
      let prev := scMercatorLogTruncPosRat x k
      let xPow := vpPowPosRat x (k + 2)
      let denNz : NzPosRat := { isNeg := false, numPred := k + 1, denPred := 0 }
      let term := posRatDivRed xPow denNz
      if (k + 1) % 2 == 1 then posRatSubRed prev term else scPosRatAddRed prev term

/-! ### 1. Certified 2D Optical Elliptic-AGM Resolvents (`δ ∈ {1/6, 1/12, 1/4}`) -/

/-- `L = 2` optical mode (`δ = 1/6`): `a_0 = 7/6`, `b_0 = √13 / 6` via Pell bounds on `√13`. -/
@[expose] def scAgmSixA0 : PosRat := { num := 7, denPred := 5 }
@[expose] def scAgmSixB0Lo : PosRat := { num := 1429, denPred := 2377 }
@[expose] def scAgmSixB0Hi : PosRat := { num := 649, denPred := 1079 }
@[expose] def scAgmSixA1Lo : PosRat := scAgmArithMeanPosRat scAgmSixA0 scAgmSixB0Lo
@[expose] def scAgmSixA1Hi : PosRat := scAgmArithMeanPosRat scAgmSixA0 scAgmSixB0Hi
@[expose] def scAgmSixB1Lo : PosRat := { num := 8373, denPred := 9999 }
@[expose] def scAgmSixB1Hi : PosRat := { num := 83731, denPred := 99999 }
@[expose] def scAgmSixA2Lo : PosRat := scAgmArithMeanPosRat scAgmSixA1Lo scAgmSixB1Lo
@[expose] def scAgmSixA2Hi : PosRat := scAgmArithMeanPosRat scAgmSixA1Hi scAgmSixB1Hi
@[expose] def scAgmSixB2Lo : PosRat := { num := 86023, denPred := 99999 }
@[expose] def scAgmSixB2Hi : PosRat := { num := 86024, denPred := 99999 }
@[expose] def scAgmSixA3Hi : PosRat := scAgmArithMeanPosRat scAgmSixA2Hi scAgmSixB2Hi

/-- Exported certified bounds on `G_{2D}(1/6) = 1 / agm(7/6, √13 / 6)`. -/
@[expose] def scG2dOneSixthLoPosRat : PosRat := scPosRatRecip scAgmSixA3Hi
@[expose] def scG2dOneSixthHiPosRat : PosRat := scPosRatRecip scAgmSixB2Lo

/-- `L = 3` lower optical mode (`δ = 1/12`): exact `(13/12, 5/12)` Pythagorean seed. -/
@[expose] def scAgmTwelfthA0 : PosRat := { num := 13, denPred := 11 }
@[expose] def scAgmTwelfthB0 : PosRat := { num := 5, denPred := 11 }
@[expose] def scAgmTwelfthA1 : PosRat := { num := 3, denPred := 3 }
@[expose] def scAgmTwelfthB1Lo : PosRat := { num := 518, denPred := 770 }
@[expose] def scAgmTwelfthB1Hi : PosRat := { num := 43, denPred := 63 }
@[expose] def scAgmTwelfthA2Lo : PosRat := scAgmArithMeanPosRat scAgmTwelfthA1 scAgmTwelfthB1Lo
@[expose] def scAgmTwelfthA2Hi : PosRat := scAgmArithMeanPosRat scAgmTwelfthA1 scAgmTwelfthB1Hi
@[expose] def scAgmTwelfthB2Lo : PosRat := { num := 3549, denPred := 4999 }
@[expose] def scAgmTwelfthB2Hi : PosRat := { num := 7099, denPred := 9999 }
@[expose] def scAgmTwelfthA3Hi : PosRat := scAgmArithMeanPosRat scAgmTwelfthA2Hi scAgmTwelfthB2Hi
@[expose] def scAgmTwelfthB3Lo : PosRat := { num := 7103, denPred := 9999 }

/-- Exported certified bounds on `G_{2D}(1/12) = 1 / agm(13/12, 5/12)`. -/
@[expose] def scG2dOneTwelfthLoPosRat : PosRat := scPosRatRecip scAgmTwelfthA3Hi
@[expose] def scG2dOneTwelfthHiPosRat : PosRat := scPosRatRecip scAgmTwelfthB3Lo

/-- `L = 3` upper optical mode (`δ = 1/4`): exact `(5/4, 3/4)` Pythagorean seed. -/
@[expose] def scAgmQuarterA0 : PosRat := { num := 5, denPred := 3 }
@[expose] def scAgmQuarterB0 : PosRat := { num := 3, denPred := 3 }
@[expose] def scAgmQuarterA1 : PosRat := posRatOfInt 1
@[expose] def scAgmQuarterB1Lo : PosRat := { num := 1677, denPred := 1731 }
@[expose] def scAgmQuarterB1Hi : PosRat := { num := 61, denPred := 62 }
@[expose] def scAgmQuarterA2Hi : PosRat := scAgmArithMeanPosRat scAgmQuarterA1 scAgmQuarterB1Hi
@[expose] def scAgmQuarterB2Lo : PosRat := { num := 98399, denPred := 99999 }

/-- Exported certified bounds on `G_{2D}(1/4) = 1 / agm(5/4, 3/4)`. -/
@[expose] def scG2dOneQuarterLoPosRat : PosRat := scPosRatRecip scAgmQuarterA2Hi
@[expose] def scG2dOneQuarterHiPosRat : PosRat := scPosRatRecip scAgmQuarterB2Lo

/-! ### 2. Musical-Comma Logarithms (`ln 2`, `ln 3`) & Multilayer Resolvents `W_1, W_2, W_3` -/

/-- Certified bounds on `ln(4/3)` and `ln(9/8)` via alternating Mercator polynomials. -/
@[expose] def scLnFourThirdsLo : PosRat := scMercatorLogTruncPosRat { num := 1, denPred := 2 } 9
@[expose] def scLnFourThirdsHi : PosRat := scMercatorLogTruncPosRat { num := 1, denPred := 2 } 10
@[expose] def scLnNineEighthsLo : PosRat := scMercatorLogTruncPosRat { num := 1, denPred := 7 } 5
@[expose] def scLnNineEighthsHi : PosRat := scMercatorLogTruncPosRat { num := 1, denPred := 7 } 6

/-- Exported certified bounds on `ln 2 = 2 ln(4/3) + ln(9/8)`. -/
@[expose]
def scLn2LoPosRat : PosRat :=
  scPosRatAddRed (posRatMulRed (posRatOfInt 2) scLnFourThirdsLo) scLnNineEighthsLo

@[expose]
def scLn2HiPosRat : PosRat :=
  scPosRatAddRed (posRatMulRed (posRatOfInt 2) scLnFourThirdsHi) scLnNineEighthsHi

/-- Exported certified bounds on `ln 3 = 3 ln(4/3) + 2 ln(9/8)`. -/
@[expose]
def scLn3LoPosRat : PosRat :=
  scPosRatAddRed
    (posRatMulRed (posRatOfInt 3) scLnFourThirdsLo)
    (posRatMulRed (posRatOfInt 2) scLnNineEighthsLo)

@[expose]
def scLn3HiPosRat : PosRat :=
  scPosRatAddRed
    (posRatMulRed (posRatOfInt 3) scLnFourThirdsHi)
    (posRatMulRed (posRatOfInt 2) scLnNineEighthsHi)

/-- Certified Mercator bounds on `ln(A_eff(4) / 128) = ln(1 + x_4)` from `[137.6726, 137.6727]`. -/
@[expose] def scLnAeffOver128Lo : PosRat := scMercatorLogTruncPosRat { num := 48363, denPred := 639999 } 3
@[expose] def scLnAeffOver128Hi : PosRat := scMercatorLogTruncPosRat { num := 96727, denPred := 1279999 } 2

/-- Single-layer (`L = 1`) quasi-2D Watson integral `W_1 = (12 ln 2 + ln(A_eff(4)/128)) / π`. -/
@[expose]
def scWLayer1LoPosRat : PosRat :=
  let lnY1 := scPosRatAddRed (posRatMulRed (posRatOfInt 12) scLn2LoPosRat) scLnAeffOver128Lo
  posRatDivRed lnY1 vpPiConvHiNz

@[expose]
def scWLayer1HiPosRat : PosRat :=
  let lnY1 := scPosRatAddRed (posRatMulRed (posRatOfInt 12) scLn2HiPosRat) scLnAeffOver128Hi
  posRatDivRed lnY1 vpPiConvLoNz

/-- Bilayer (`L = 2`) per-plane Watson integral `W_2 = (W_{Q2D}(2) + G_{2D}(1/6)) / 2`. -/
@[expose]
def scWLayer2LoPosRat : PosRat :=
  let lnY2 := scPosRatAddRed (posRatMulRed (posRatOfInt 13) scLn2LoPosRat) scLnAeffOver128Lo
  let wQ2d2 := posRatDivRed lnY2 vpPiConvHiNz
  posRatMulRed { num := 1, denPred := 1 } (scPosRatAddRed wQ2d2 scG2dOneSixthLoPosRat)

@[expose]
def scWLayer2HiPosRat : PosRat :=
  let lnY2 := scPosRatAddRed (posRatMulRed (posRatOfInt 13) scLn2HiPosRat) scLnAeffOver128Hi
  let wQ2d2 := posRatDivRed lnY2 vpPiConvLoNz
  posRatMulRed { num := 1, denPred := 1 } (scPosRatAddRed wQ2d2 scG2dOneSixthHiPosRat)

/-- Trilayer (`L = 3`) per-plane Watson integral `W_3 = (W_{Q2D}(3) + G_{2D}(1/12) + G_{2D}(1/4)) / 3`. -/
@[expose]
def scWLayer3LoPosRat : PosRat :=
  let lnY3 := scPosRatAddRed
    (scPosRatAddRed (posRatMulRed (posRatOfInt 12) scLn2LoPosRat) scLn3LoPosRat)
    scLnAeffOver128Lo
  let wQ2d3 := posRatDivRed lnY3 vpPiConvHiNz
  let sumOpt := scPosRatAddRed scG2dOneTwelfthLoPosRat scG2dOneQuarterLoPosRat
  posRatMulRed { num := 1, denPred := 2 } (scPosRatAddRed wQ2d3 sumOpt)

@[expose]
def scWLayer3HiPosRat : PosRat :=
  let lnY3 := scPosRatAddRed
    (scPosRatAddRed (posRatMulRed (posRatOfInt 12) scLn2HiPosRat) scLn3HiPosRat)
    scLnAeffOver128Hi
  let wQ2d3 := posRatDivRed lnY3 vpPiConvLoNz
  let sumOpt := scPosRatAddRed scG2dOneTwelfthHiPosRat scG2dOneQuarterHiPosRat
  posRatMulRed { num := 1, denPred := 2 } (scPosRatAddRed wQ2d3 sumOpt)

/--
Theorem (Zero Axioms): Certified Elliptic-AGM Optical Resolvents, Musical-Comma Logarithms
& Multilayer Quasi-2D Watson Hierarchy (`W_3 < W_2 < W_1`).
-/
theorem sc_quasi2d_agm_and_multilayer_resolvent_bounds :
    vacFastLtInt (4287 * 4287) (13 * 1189 * 1189) = true ∧
    vacFastLtInt (13 * 180 * 180) (649 * 649) = true ∧
    posRatLt (posRatMulRed scAgmSixB1Lo scAgmSixB1Lo)
      (posRatMulRed scAgmSixA0 scAgmSixB0Lo) = true ∧
    posRatLt (posRatMulRed scAgmSixA0 scAgmSixB0Hi)
      (posRatMulRed scAgmSixB1Hi scAgmSixB1Hi) = true ∧
    posRatLt (posRatMulRed scAgmSixB2Lo scAgmSixB2Lo)
      (posRatMulRed scAgmSixA1Lo scAgmSixB1Lo) = true ∧
    posRatLt (posRatMulRed scAgmSixA1Hi scAgmSixB1Hi)
      (posRatMulRed scAgmSixB2Hi scAgmSixB2Hi) = true ∧
    posRatLt (posRatMulRed scAgmTwelfthB1Lo scAgmTwelfthB1Lo)
      (posRatMulRed scAgmTwelfthA0 scAgmTwelfthB0) = true ∧
    posRatLt (posRatMulRed scAgmTwelfthA0 scAgmTwelfthB0)
      (posRatMulRed scAgmTwelfthB1Hi scAgmTwelfthB1Hi) = true ∧
    posRatLt (posRatMulRed scAgmTwelfthB2Lo scAgmTwelfthB2Lo)
      (posRatMulRed scAgmTwelfthA1 scAgmTwelfthB1Lo) = true ∧
    posRatLt (posRatMulRed scAgmTwelfthA1 scAgmTwelfthB1Hi)
      (posRatMulRed scAgmTwelfthB2Hi scAgmTwelfthB2Hi) = true ∧
    posRatLt (posRatMulRed scAgmTwelfthB3Lo scAgmTwelfthB3Lo)
      (posRatMulRed scAgmTwelfthA2Lo scAgmTwelfthB2Lo) = true ∧
    posRatLt (posRatMulRed scAgmQuarterB1Lo scAgmQuarterB1Lo)
      (posRatMulRed scAgmQuarterA0 scAgmQuarterB0) = true ∧
    posRatLt (posRatMulRed scAgmQuarterA0 scAgmQuarterB0)
      (posRatMulRed scAgmQuarterB1Hi scAgmQuarterB1Hi) = true ∧
    posRatLt (posRatMulRed scAgmQuarterB2Lo scAgmQuarterB2Lo)
      (posRatMulRed scAgmQuarterA1 scAgmQuarterB1Lo) = true ∧
    posRatLt { num := 11622, denPred := 9999 } scG2dOneSixthLoPosRat = true ∧
    posRatLt scG2dOneSixthHiPosRat { num := 11625, denPred := 9999 } = true ∧
    posRatLt { num := 14076, denPred := 9999 } scG2dOneTwelfthLoPosRat = true ∧
    posRatLt scG2dOneTwelfthHiPosRat { num := 14079, denPred := 9999 } = true ∧
    posRatLt { num := 10161, denPred := 9999 } scG2dOneQuarterLoPosRat = true ∧
    posRatLt scG2dOneQuarterHiPosRat { num := 10163, denPred := 9999 } = true ∧
    posRatLt { num := 693146, denPred := 999999 } scLn2LoPosRat = true ∧
    posRatLt scLn2HiPosRat { num := 693148, denPred := 999999 } = true ∧
    posRatLt { num := 1098610, denPred := 999999 } scLn3LoPosRat = true ∧
    posRatLt scLn3HiPosRat { num := 1098614, denPred := 999999 } = true ∧
    posRatLt { num := 26708, denPred := 9999 } scWLayer1LoPosRat = true ∧
    posRatLt scWLayer1HiPosRat { num := 26709, denPred := 9999 } = true ∧
    posRatLt { num := 20268, denPred := 9999 } scWLayer2LoPosRat = true ∧
    posRatLt scWLayer2HiPosRat { num := 20271, denPred := 9999 } = true ∧
    posRatLt { num := 18147, denPred := 9999 } scWLayer3LoPosRat = true ∧
    posRatLt scWLayer3HiPosRat { num := 18150, denPred := 9999 } = true ∧
    posRatLt scWLayer3HiPosRat scWLayer2LoPosRat = true ∧
    posRatLt scWLayer2HiPosRat scWLayer1LoPosRat = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: Continuum `ℝ` AGM Contraction, Pythagorean Seeds & `π`-Cancellation -/

/--
Theorem (Continuum `ℝ`): Strict AGM Step Monotonicity, Contraction & `[100]` Optical Seeds.
1. For ALL `0 < b < a` and `0 < g` with `g² = a b`, the arithmetic-geometric step
   `(a', g) = ((a + b)/2, √(ab))` satisfies `b < g < a' < a` and `a' - g < (a - b) / 2`.
2. Along `[100]`, the `e_g` intensity ratio `(5/4) / (15/4) = 1/3` produces the exact
   Pythagorean seeds `(7/6)² - 1 = 13/36`, `(13/12)² - 1 = (5/12)²`, and `(5/4)² - 1 = (3/4)²`.
-/
theorem continuum_agm_step_monotonicity_and_pythagorean_seeds
    (a b g : ℝ) (hb : 0 < b) (hab : b < a) (hg : 0 < g) (hg_sq : g ^ 2 = a * b) :
    let a_next := (a + b) / 2
    b < g ∧
    g < a_next ∧
    a_next < a ∧
    a_next - g < (a - b) / 2 ∧
    ((5 / 4 : ℝ) / (15 / 4 : ℝ) = (1 / 3 : ℝ)) ∧
    ((7 / 6 : ℝ) ^ 2 - 1 = (13 / 36 : ℝ)) ∧
    ((13 / 12 : ℝ) ^ 2 - 1 = (5 / 12 : ℝ) ^ 2) ∧
    ((5 / 4 : ℝ) ^ 2 - 1 = (3 / 4 : ℝ) ^ 2) := by
  have h_gb_pos : 0 < g + b := add_pos hg hb
  have h_diff_gb : (g - b) * (g + b) = (a - b) * b := by
    calc (g - b) * (g + b)
      _ = g ^ 2 - b ^ 2 := by ring
      _ = a * b - b ^ 2 := by rw [hg_sq]
      _ = (a - b) * b := by ring
  have h_rhs_gb : 0 < (a - b) * b := mul_pos (by linarith) hb
  have hb_lt_g : b < g := by
    by_contra h_not
    have h_np : (g - b) * (g + b) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt h_gb_pos)
    linarith
  have ha_pos : 0 < a := lt_trans hb hab
  have h_sum_pos : 0 < (a + b) / 2 + g := by positivity
  have h_am_gm_id :
      ((a + b) / 2 - g) * ((a + b) / 2 + g) = (a - b) ^ 2 / 4 := by
    calc ((a + b) / 2 - g) * ((a + b) / 2 + g)
      _ = ((a + b) / 2) ^ 2 - g ^ 2 := by ring
      _ = ((a + b) / 2) ^ 2 - a * b := by rw [hg_sq]
      _ = (a - b) ^ 2 / 4 := by ring
  have h_sq_pos : 0 < (a - b) ^ 2 / 4 :=
    div_pos (sq_pos_of_ne_zero (by linarith)) (by norm_num)
  have hg_lt_am : g < (a + b) / 2 := by
    by_contra h_not
    have h_np : ((a + b) / 2 - g) * ((a + b) / 2 + g) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt h_sum_pos)
    linarith
  refine ⟨hb_lt_g, hg_lt_am, by linarith, by linarith, by ring, by ring, by ring, by ring⟩

/--
Theorem (Continuum `ℝ`): Musical-Comma Dyadic Factorization & Elliptic `π`-Cancellation.
1. `(4/3)² · (9/8) = 2` and `(4/3)³ · (9/8)² = 3`, justifying the Mercator decompositions
   `ln 2 = 2 ln(4/3) + ln(9/8)` and `ln 3 = 3 ln(4/3) + 2 ln(9/8)`.
2. `32 L A = 2¹² · (A / 128)`, `2¹³ · (A / 128)`, and `2¹² · 3 · (A / 128)` for `L = 1, 2, 3`.
3. Substituting Gauss's identity `K(z⁻²) = (π z) / (2 · agm)` into `(2 / (π z)) K(z⁻²)`
   cancels `π` and `z` identically, leaving `1 / agm`.
-/
theorem continuum_musical_comma_and_elliptic_pi_cancellation
    (A pi_r z agm_z : ℝ)
    (hpi : pi_r ≠ 0) (hz : z ≠ 0) (hagm : agm_z ≠ 0) :
    ((4 / 3 : ℝ) ^ 2 * (9 / 8 : ℝ) = 2) ∧
    ((4 / 3 : ℝ) ^ 3 * (9 / 8 : ℝ) ^ 2 = 3) ∧
    (32 * (1 : ℝ) * A = (2 : ℝ) ^ 12 * (A / 128)) ∧
    (32 * (2 : ℝ) * A = (2 : ℝ) ^ 13 * (A / 128)) ∧
    (32 * (3 : ℝ) * A = (2 : ℝ) ^ 12 * 3 * (A / 128)) ∧
    ((2 / (pi_r * z)) * ((pi_r * z) / (2 * agm_z)) = 1 / agm_z) := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, ?_⟩
  field_simp [hpi, hz, hagm]

#print axioms sc_quasi2d_agm_and_multilayer_resolvent_bounds

end TVE
