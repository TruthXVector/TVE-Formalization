/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import TVE.Vacuum
public import TVE.Action
public import TVE.Topologies
public import TVE.Spectrum

/-!
# Topological Vacuum Electrodynamics — Confinement and Electroweak Shares

Constructive zero-axiom and continuum `ℝ` formalization of TVE forces:
1. **Reconciled Bag & Linear-Tension Confinement (`PosRat`):** Proves radial
   pressure balance and strict Derrick-Bogomolny energy optimality in sound
   positive-denominator `PosRat` arithmetic (`a = radiusPred + 1 ≥ 1`), reconciling
   vacuum bag pressure `P_bag` (`a_eq⁴ = ξ / P_bag`) with 1D linear string tension
   `σ = P_bag a_eq²` (`a_eq² = ξ / σ`, matching `minorRadiusFromTension`).
2. **Subtracted-Proton Electroweak VEV Factorization:** Propagates the Seifert-subtracted
   proton mass `m_p = (94 / 7) α⁻¹ m_e` into `v = 2 m_p cos θ_C / α - (4 / 5) σ_s / α`,
   proving `35 (v / m_e) = 924 A² - 3290 A = 14 A (66 A - 235)` and its `7`-canceled
   reduction `v / m_e = (2 / 5) A (66 A - 235)` both symbolically over `ℕ` and over `ℝ`.
3. **Continued-Fraction `PosRat` Boson Hierarchy:** Verifies the exact Weinberg `W / Z`
   identity and interval-disjoint strict ordering `m_p < m_W < m_Z < v` across the
   continued-fraction `[333/106, 355/113]` bracket in pure-`Nat` GMP `PosRat` arithmetic.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-! ## Part 1: Zero-Axiom `PosRat` Confinement & Electroweak Kernel -/

/--
Sound division-by-zero-free radial confinement state (`radius = radiusPred + 1 ≥ 1`,
`eqRadius = eqRadiusPred + 1 ≥ 1`), distinguishing cross-sectional vacuum bag pressure
`pBag` (`J/m³`, `a_eq⁴ = ξ / P_bag`) from reduced 1D linear string tension
`σ_lin = P_bag * a_eq²` (`J/m`, `a_eq² = ξ / σ_lin`).
-/
structure ConfinementStatePos where
  xi : ℕ
  pBag : ℕ
  radiusPred : ℕ
  eqRadiusPred : ℕ

/-- Equilibrium `PosRat` confinement state (`ξ = 16, P_bag = 1, a = 2, a_eq = 2, σ_lin = 4`). -/
@[expose]
def canonicalConfinementPos : ConfinementStatePos :=
  { xi := 16, pBag := 1, radiusPred := 1, eqRadiusPred := 1 }

/-- Compressed neck state (`a = 1 < a_eq = 2`) where outward helicity pressure dominates. -/
@[expose]
def compressedConfinementPos : ConfinementStatePos :=
  { xi := 16, pBag := 1, radiusPred := 0, eqRadiusPred := 1 }

/-- Stretched tube state (`a = 3 > a_eq = 2`) where inward tension dominates. -/
@[expose]
def stretchedConfinementPos : ConfinementStatePos :=
  { xi := 16, pBag := 1, radiusPred := 2, eqRadiusPred := 1 }

/-- Reduced 1D linear string tension `σ_lin = P_bag * a_eq²` associated to `s : ConfinementStatePos`. -/
@[expose]
def frcLinearTensionNat (s : ConfinementStatePos) : ℕ :=
  let aEq := s.eqRadiusPred + 1
  s.pBag * (aEq * aEq)

/-- Outward magnetic helicity pressure `P_mag = ξ / a⁴` in sound `PosRat` (`den = a⁴ ≥ 1`). -/
@[expose]
def frcHelicityPressurePosRat (s : ConfinementStatePos) : PosRat :=
  helicityPressurePosRat s.xi s.radiusPred

/-- Inward linear-tension stress `P_lin = σ_lin / a²` in sound `PosRat` (`den = a² ≥ 1`). -/
@[expose]
def frcLinearTensionStressPosRat (s : ConfinementStatePos) : PosRat :=
  linearTensionPressurePosRat (frcLinearTensionNat s) s.radiusPred

/-- Constant vacuum bag pressure `P_bag / 1` in sound `PosRat`. -/
@[expose]
def frcBagPressurePosRat (s : ConfinementStatePos) : PosRat :=
  posRatOfInt (Int.ofNat s.pBag)

/-- Radial cross-sectional tube energy `(ξ + P_bag a⁴) / a²` in sound `PosRat` (`den = a² ≥ 1`). -/
@[expose]
def frcRadialEnergyPosRat (s : ConfinementStatePos) : PosRat :=
  radialTubeEnergyPosRat s.xi s.pBag s.radiusPred

/-- Cleared linear-tension force residual `ξ - σ_lin a²` (vanishing iff `a² = ξ / σ_lin`). -/
@[expose]
def linearTensionForceResidual (xi sigmaLin a : ℤ) : ℤ :=
  xi - sigmaLin * a * a

/-! ### Legacy `ConfinementState` & `ExactRat` Shims (Preserved for Compatibility) -/

/-- Legacy integer state for radial flux-tube helicity confinement. -/
structure ConfinementState where
  xi : ℤ
  sigma : ℤ
  radius : ℤ

/-- Equilibrium tube state (`a_eq = 2` with `ξ = 16, P_bag = 1`). -/
@[expose]
def canonicalConfinement : ConfinementState :=
  { xi := 16, sigma := 1, radius := 2 }

/-- Compressed neck state (`a = 1 < a_eq`). -/
@[expose]
def compressedConfinement : ConfinementState :=
  { xi := 16, sigma := 1, radius := 1 }

/-- Stretched tube state (`a = 3 > a_eq`). -/
@[expose]
def stretchedConfinement : ConfinementState :=
  { xi := 16, sigma := 1, radius := 3 }

/-- Outward dynamic helicity pressure `P = ξ / a⁴` in integer arithmetic. -/
@[expose]
def helicityPressureInt (s : ConfinementState) : ℤ :=
  s.xi / (s.radius * s.radius * s.radius * s.radius)

/-- Legacy `ExactRat` outward helicity pressure `P = ξ / a⁴`. -/
@[expose]
def frcPressureExact (s : ConfinementState) : ExactRat :=
  { num := s.xi, den := s.radius * s.radius * s.radius * s.radius }

/-- Legacy `ExactRat` inward bag pressure `P_bag / 1`. -/
@[expose]
def frcTensionExact (s : ConfinementState) : ExactRat :=
  { num := s.sigma, den := 1 }

/-- Cleared-denominator bag radial force residual `ξ - P_bag a⁴`. -/
@[expose]
def netRadialForceResidual (s : ConfinementState) : ℤ :=
  s.xi - s.sigma * s.radius * s.radius * s.radius * s.radius

/-- Radial tube energy density `(ξ + P_bag a⁴) / a²` in integer arithmetic. -/
@[expose]
def radialEnergyPerAreaInt (s : ConfinementState) : ℤ :=
  (s.xi + s.sigma * s.radius * s.radius * s.radius * s.radius) /
    (s.radius * s.radius)

/-- Legacy `ExactRat` radial tube energy `(ξ + P_bag a⁴) / a²`. -/
@[expose]
def frcEnergyExact (s : ConfinementState) : ExactRat :=
  { num := s.xi + s.sigma * s.radius * s.radius * s.radius * s.radius,
    den := s.radius * s.radius }

/-! ### Subtracted-Proton Electroweak Polynomials & Pure-`Nat` GMP `PosRat` Operators -/

/--
Cleared-denominator electroweak VEV core polynomial `924 A² - 3290 A = 14 A (66 A - 235)`
obtained from `35 (v / m_e)` using the strange-subtracted proton mass `m_p = (94 / 7) A m_e`:
`35 [ 2 A ((94 / 7) A) (1 - 7 / (2A)) - (4 / 5) A ((4 / 7) A) ] = 5 (188 A² - 658 A) - 16 A² = 924 A² - 3290 A`.
-/
@[expose]
def ewCorePolyInt (A : ℤ) : ℤ :=
  924 * A * A - 3290 * A

/-- `7`-canceled electroweak VEV numerator `2 A (66 A - 235)` over reduced denominator `5`. -/
@[expose]
def ewReducedPolyInt (A : ℤ) : ℤ :=
  2 * A * (66 * A - 235)

/-- Subtracted proton rest mass `(94 / 7) A m_e` scaled to common electroweak denominator `1050 A m_e` (`150 × 94 A² = 14100 A²`). -/
@[expose]
def protonScaledEW (A : ℤ) : ℤ :=
  14100 * A * A

/-- Electroweak VEV `v` scaled to common denominator `1050 A m_e` (`30 A (924 A² - 3290 A)`). -/
@[expose]
def vevScaledEW (A : ℤ) : ℤ :=
  30 * A * ewCorePolyInt A

/-- Charged `W` boson mass `m_W` scaled to common denominator `1050 A m_e`. -/
@[expose]
def mWScaledEW (A : ℤ) : ℤ :=
  10 * ewCorePolyInt A * (A - 3)

/-- Neutral `Z` boson mass `m_Z` scaled to common denominator `1050 A m_e`. -/
@[expose]
def mZScaledEW (A : ℤ) : ℤ :=
  11 * ewCorePolyInt A * (A + 1)

/-- Cabibbo cosine `cos θ_C = 1 - (7 / 2) α` in pure-`Nat` GMP `PosRat`. -/
@[expose]
def cosThetaCPosRat (A_rat : PosRat) : PosRat :=
  posRatSubRed (posRatOfInt 1)
    (posRatDivRed { num := 7, denPred := 1 } (specPosRatToNz A_rat))

/--
Dimensionless electroweak VEV `v / m_e = 2 A (m_p / m_e) cos θ_C - (4 / 5) A (σ_s / m_e)`
in pure-`Nat` GMP `PosRat`, directly composing `protonOverMePosRat`, `cosThetaCPosRat`,
and `strangeOverMePosRat` with zero hand-cancellation.
-/
@[expose]
def vevOverMePosRat (A_rat : PosRat) : PosRat :=
  let protonTerm :=
    posRatMulRed (posRatMulRed (posRatOfInt 2) A_rat)
      (posRatMulRed (protonOverMePosRat A_rat) (cosThetaCPosRat A_rat))
  let strangeTerm :=
    posRatMulRed { num := 4, denPred := 4 }
      (posRatMulRed A_rat (strangeOverMePosRat A_rat))
  posRatSubRed protonTerm strangeTerm

/-- Reduced polynomial form `(2 / 5) A (66 A - 235)` of `v / m_e` in pure-`Nat` GMP `PosRat`. -/
@[expose]
def vevReducedPolyPosRat (A_rat : PosRat) : PosRat :=
  let inner := posRatSubRed (posRatMulRed (posRatOfInt 66) A_rat) (posRatOfInt 235)
  posRatMulRed { num := 2, denPred := 4 } (posRatMulRed A_rat inner)

/--
Dimensionless `W` boson mass `m_W / m_e = (v / (3 m_e))(1 - 3 α)` in pure-`Nat` GMP `PosRat`,
directly composing `vevOverMePosRat`.
-/
@[expose]
def mWOverMePosRat (A_rat : PosRat) : PosRat :=
  let oneMinus3Alpha :=
    posRatSubRed (posRatOfInt 1)
      (posRatDivRed (posRatOfInt 3) (specPosRatToNz A_rat))
  posRatMulRed (posRatMulRed { num := 1, denPred := 2 } (vevOverMePosRat A_rat)) oneMinus3Alpha

/--
Dimensionless `Z` boson mass `m_Z / m_e = (1/2)(4/5 + 2/3)((v / m_e) / 2)(1 + α)` in pure-`Nat`
GMP `PosRat`, directly composing `vevOverMePosRat` and the `(4/5, 2/3)` winding shares.
-/
@[expose]
def mZOverMePosRat (A_rat : PosRat) : PosRat :=
  let shareMean :=
    posRatMulRed { num := 1, denPred := 1 }
      (posRatAddRed { num := 4, denPred := 4 } { num := 2, denPred := 2 })
  let halfVev := posRatMulRed { num := 1, denPred := 1 } (vevOverMePosRat A_rat)
  let onePlusAlpha :=
    posRatAddRed (posRatOfInt 1)
      (posRatDivRed (posRatOfInt 1) (specPosRatToNz A_rat))
  posRatMulRed shareMean (posRatMulRed halfVev onePlusAlpha)

/-- Legacy `ExactRat` Cabibbo cosine retained for staged compatibility. -/
@[expose]
def frcCosThetaCExact (A : ℤ) : ExactRat :=
  { num := 2 * A - 7, den := 2 * A }

/-- Legacy `ExactRat` electroweak VEV `v / m_e = (924 A² - 3290 A) / 35`. -/
@[expose]
def frcVevOverMeExact (A : ℤ) : ExactRat :=
  { num := ewCorePolyInt A, den := 35 }

/-- Legacy `ExactRat` `W` mass `m_W / m_e`. -/
@[expose]
def frcMWOverMeExact (A : ℤ) : ExactRat :=
  { num := ewCorePolyInt A * (A - 3), den := 105 * A }

/-- Legacy `ExactRat` `Z` mass `m_Z / m_e`. -/
@[expose]
def frcMZOverMeExact (A : ℤ) : ExactRat :=
  { num := 11 * ewCorePolyInt A * (A + 1), den := 1050 * A }

/--
Theorem (Zero Axioms): Division-by-Zero-Free `PosRat` Confinement & Reconciled Linear Tension.
Proves in sound `PosRat` arithmetic (`a = radiusPred + 1 ≥ 1`) that:
1. At equilibrium (`a = 2, ξ = 16, P_bag = 1, σ_lin = 4`), `P_mag = 16/16 = 1`, `P_lin = 4/4 = 1`,
   `netRadialForceResidual = 0` (`a⁴ = ξ / P_bag`), and `linearTensionForceResidual 16 4 2 = 0` (`a² = ξ / σ_lin`).
2. Under compression (`a = 1`), `1 < 4 < 16` (`P_bag < P_lin < P_mag`) prevents core collapse.
3. Under stretching (`a = 3`), `0 < 16/81 < 4/9 < 1` (`0 < P_mag < P_lin < P_bag`).
4. Equilibrium energy (`8`) is strictly below both compressed (`17`) and stretched (`97/9`) states.
-/
theorem bogomolny_confinement_pressure_balance :
    frcHelicityPressurePosRat canonicalConfinementPos = frcBagPressurePosRat canonicalConfinementPos ∧
    frcLinearTensionStressPosRat canonicalConfinementPos = frcBagPressurePosRat canonicalConfinementPos ∧
    netRadialForceResidual canonicalConfinement = 0 ∧
    linearTensionForceResidual 16 4 2 = 0 ∧
    posRatLt (frcBagPressurePosRat compressedConfinementPos)
      (frcLinearTensionStressPosRat compressedConfinementPos) = true ∧
    posRatLt (frcLinearTensionStressPosRat compressedConfinementPos)
      (frcHelicityPressurePosRat compressedConfinementPos) = true ∧
    frcHelicityPressurePosRat stretchedConfinementPos = { num := 16, denPred := 80 } ∧
    posRatLt (posRatOfInt 0) (frcHelicityPressurePosRat stretchedConfinementPos) = true ∧
    posRatLt (frcHelicityPressurePosRat stretchedConfinementPos)
      (frcLinearTensionStressPosRat stretchedConfinementPos) = true ∧
    posRatLt (frcLinearTensionStressPosRat stretchedConfinementPos)
      (frcBagPressurePosRat stretchedConfinementPos) = true ∧
    frcRadialEnergyPosRat stretchedConfinementPos = { num := 97, denPred := 8 } ∧
    posRatLt (frcRadialEnergyPosRat canonicalConfinementPos)
      (frcRadialEnergyPosRat compressedConfinementPos) = true ∧
    posRatLt (frcRadialEnergyPosRat canonicalConfinementPos)
      (frcRadialEnergyPosRat stretchedConfinementPos) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): Universal Symbolic Bogomolny Radial Optimality over `ℕ`.
-/
theorem universal_bogomolny_radial_minimum_nat (b k : ℕ) :
    b * b + (b + (k + 1)) * (b + (k + 1)) =
      (b * b + b * b) + (((k + 1) * b) + ((b * (k + 1)) + ((k + 1) * (k + 1)))) ∧
    vacIsPosNat (((k + 1) * b) + ((b * (k + 1)) + ((k + 1) * (k + 1)))) = true :=
  ⟨Eq.trans
      (congrArg (Nat.add (b * b)) (vac_add_sq b (k + 1)))
      (vac_add_assoc (b * b) (b * b)
        (((k + 1) * b) + ((b * (k + 1)) + ((k + 1) * (k + 1))))).symm,
   rfl⟩

/--
Theorem (Zero Axioms): Positive-Denominator `PosRat` Derivation of Cabibbo & Electroweak Shares.
-/
theorem steiner_electroweak_and_cabibbo_shares :
    posRatReduce { num := sphereKernelTrace trefoilEquilibriumSheet, denPred := 1 } =
      { num := 7, denPred := 1 } ∧
    posRatReduce { num := 2 * trefoilEquilibriumSheet.aspectNum, denPred := 4 } =
      { num := 4, denPred := 4 } ∧
    sheetAspectPosRat trefoilEquilibriumSheetPos = { num := 2, denPred := 2 } ∧
    posRatMulRed { num := 1, denPred := 1 }
      (posRatAddRed { num := 4, denPred := 4 } (sheetAspectPosRat trefoilEquilibriumSheetPos)) =
      { num := 11, denPred := 14 } ∧
    protonTrefoilTubeInt.writhe = 3 ∧
    posRatReduce { num := sphereKernelTrace trefoilEquilibriumSheet, denPred := 8 } =
      { num := 7, denPred := 8 } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): Universal Symbolic Factorization of the Subtracted-Proton VEV Polynomial.
Proves universally for ALL `A D : ℕ` using pure kernel induction (`Vacuum.lean`) that:
1. `924 * (A * A) = (14 * A) * (66 * A)` and `3290 * A = (14 * A) * 235` (`14A(66A - 235)`).
2. Whenever `D + 235 = 66 * A`, `(14 * A) * D + 3290 * A = 924 * (A * A)`.
3. Canceling the prime `7` against `35 = 5 × 7` gives `5 * ((14 * A) * D) = 35 * ((2 * A) * D)`.
-/
theorem universal_ew_vev_polynomial_factorization_nat (A D : ℕ) :
    924 * (A * A) = (14 * A) * (66 * A) ∧
    3290 * A = (14 * A) * 235 ∧
    (D + 235 = 66 * A → (14 * A) * D + 3290 * A = 924 * (A * A)) ∧
    5 * ((14 * A) * D) = 35 * ((2 * A) * D) :=
  have h_quad : 924 * (A * A) = (14 * A) * (66 * A) :=
    (vac_mul_four_swap 14 A 66 A).symm
  have h_lin : 3290 * A = (14 * A) * 235 :=
    Eq.trans (vac_mul_assoc 14 235 A)
      (Eq.trans (congrArg (Nat.mul 14) (vac_mul_comm 235 A))
        (vac_mul_assoc 14 A 235).symm)
  have h_dist : D + 235 = 66 * A → (14 * A) * D + 3290 * A = 924 * (A * A) :=
    fun hD =>
      Eq.trans (congrArg (Nat.add ((14 * A) * D)) h_lin)
        (Eq.trans (vac_mul_add (14 * A) D 235).symm
          (Eq.trans (congrArg (Nat.mul (14 * A)) hD) h_quad.symm))
  have h_70A : 5 * (14 * A) = 35 * (2 * A) :=
    Eq.trans (vac_mul_assoc 5 14 A).symm (vac_mul_assoc 35 2 A)
  have h_canc7 : 5 * ((14 * A) * D) = 35 * ((2 * A) * D) :=
    Eq.trans (vac_mul_assoc 5 (14 * A) D).symm
      (Eq.trans (congrArg (fun t => t * D) h_70A)
        (vac_mul_assoc 35 (2 * A) D))
  ⟨h_quad, h_lin, h_dist, h_canc7⟩

/--
Theorem (Zero Axioms): Exact Weinberg `W / Z` Identity & Interval-Disjoint `PosRat` Hierarchy
Across the Continued-Fraction Bracket `[333/106, 355/113]`.
Proves in pure-`Nat` GMP `PosRat` arithmetic with zero `π = 3` or `A = 137` approximations that:
1. Direct operator composition `vevOverMePosRat` equals `vevReducedPolyPosRat` (`(2/5)A(66A - 235)`)
   at both `A_L = α⁻¹(333/106)` and `A_U = α⁻¹(355/113)`.
2. The exact Weinberg identity `11 (1 + α) m_W = 10 (1 - 3 α) m_Z` holds in `PosRat` at `A_L` and `A_U`,
   as well as symbolically at `alphaInvPoly 3 = 120` and `137`.
3. Across `[333/106, 355/113]`, `m_p(A_U) < m_W(A_L)`, `m_W(A_U) < m_Z(A_L)`, and `m_Z(A_U) < v(A_L)`.
-/
theorem electroweak_vev_and_boson_hierarchy :
    let A_L := alphaInvPosRat piConvergent3PosRat
    let A_U := alphaInvPosRat piZuChongzhiPosRat
    let onePlusAlpha_U :=
      posRatAddRed (posRatOfInt 1) (posRatDivRed (posRatOfInt 1) (specPosRatToNz A_U))
    let oneMinus3Alpha_U :=
      posRatSubRed (posRatOfInt 1) (posRatDivRed (posRatOfInt 3) (specPosRatToNz A_U))
    vevOverMePosRat A_L = vevReducedPolyPosRat A_L ∧
    vevOverMePosRat A_U = vevReducedPolyPosRat A_U ∧
    posRatMulRed (posRatOfInt 11) (posRatMulRed onePlusAlpha_U (mWOverMePosRat A_U)) =
      posRatMulRed (posRatOfInt 10) (posRatMulRed oneMinus3Alpha_U (mZOverMePosRat A_U)) ∧
    mWScaledEW (alphaInvPoly 3) * (11 * (alphaInvPoly 3 + 1)) =
      mZScaledEW (alphaInvPoly 3) * (10 * (alphaInvPoly 3 - 3)) ∧
    posRatLt (protonOverMePosRat A_U) (mWOverMePosRat A_L) = true ∧
    posRatLt (mWOverMePosRat A_U) (mZOverMePosRat A_L) = true ∧
    posRatLt (mZOverMePosRat A_U) (vevOverMePosRat A_L) = true ∧
    isStrictlyLighterInt (protonScaledEW 137) (mWScaledEW 137) = true ∧
    isStrictlyLighterInt (mWScaledEW 137) (mZScaledEW 137) = true ∧
    isStrictlyLighterInt (mZScaledEW 137) (vevScaledEW 137) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: Continuum Confinement, VEV Reduction & Weinberg Mass-Ratio Layer -/

/-- Dynamic pressure scaling under the helicity constraint: \(P = \xi / a^4\) (normalized to unit baseline). -/
@[expose]
noncomputable def confinementPressure (a : ℝ) : ℝ :=
  stringTension / (a ^ 4)

/--
Equilibrium minor radius recovered from reduced 1D Nambu-Goto linear string tension \(\sigma\)
(\(\text{J}/\text{m}\), where \(\sigma = P_{\mathrm{bag}} a_{\mathrm{eq}}^2\) relates linear tension to
the cross-sectional vacuum bag pressure \(P_{\mathrm{bag}}\) of `BeltramiConfinement.lean`):
balancing \(P_{\mathrm{mag}} = \xi / a_{\mathrm{eq}}^4\) against \(\sigma / a_{\mathrm{eq}}^2\) gives \(a_{\mathrm{eq}} = \sqrt{\xi / \sigma}\).
-/
@[expose]
noncomputable def minorRadiusFromTension (ξ σ : ℝ) : ℝ :=
  Real.sqrt (ξ / σ)

/-- Cabibbo cosine from the mode count: \(\cos\theta_C = 1 - (7/2)\alpha\). -/
@[expose]
noncomputable def cosThetaC : ℝ := 1 - (7 / 2) * alpha

/-- Electroweak vacuum expectation value read from the strange-subtracted proton mass and strange subtraction:
    \(v = \frac{2m_p\cos\theta_C}{\alpha} - \frac{4}{5}\frac{\sigma_s}{\alpha}\). -/
@[expose]
noncomputable def v : ℝ :=
  (2 * protonMass * cosThetaC) / alpha - (4 / 5) * (strangeSubtraction / alpha)

/-- W mass as the charged winding share on the trefoil:
    \(m_W = \frac{v}{3}(1 - 3\alpha)\). -/
@[expose]
noncomputable def m_W : ℝ :=
  (v / 3) * (1 - 3 * alpha)

/-- Z mass as the neutral mean of the poloidal and charged shares:
    \(m_Z = \frac{1}{2}(\frac{4}{5} + \frac{2}{3})\frac{v}{2}(1 + \alpha)\). -/
@[expose]
noncomputable def m_Z : ℝ :=
  (1 / 2) * (4 / 5 + 2 / 3) * (v / 2) * (1 + alpha)

/-- The winding count \(\sqrt{7/9}\) appearing in the electroweak relations. -/
@[expose]
noncomputable def windingCount : ℝ := Real.sqrt (7 / 9)

/--
Theorem (Exact Continuum Reduction of the Subtracted-Proton Electroweak VEV):
Proves directly over `ℝ` that substituting `protonMass = (94 / 7) α⁻¹ m_e`,
`cosThetaC = 1 - (7 / 2) α`, and `strangeSubtraction = (4 / 7) α⁻¹ m_e` into `v`
yields both `(924 α⁻² - 3290 α⁻¹) / 35 = 14 α⁻¹ (66 α⁻¹ - 235) / 35` and the
`7`-canceled identity `v = 2 α⁻¹ (66 α⁻¹ - 235) / 5`.
-/
theorem continuum_vev_polynomial_reduction :
    v = (14 * alphaInv * (66 * alphaInv - 235)) / 35 ∧
    v = (2 * alphaInv * (66 * alphaInv - 235)) / 5 := by
  have hA_pos : 0 < alphaInv := by
    dsimp [alphaInv, torusBulkCapacity, torusBoundaryCapacity, torusCutCapacity]
    have h_pi : 0 < Real.pi := Real.pi_pos
    positivity
  have hA_ne : alphaInv ≠ 0 := ne_of_gt hA_pos
  have ha_pos : 0 < (1 : ℝ) / alphaInv := one_div_pos.mpr hA_pos
  have ha_ne : (1 : ℝ) / alphaInv ≠ 0 := ne_of_gt ha_pos
  have h_inv_mul : alphaInv * ((1 : ℝ) / alphaInv) = 1 := by
    rw [mul_comm]
    exact div_mul_cancel₀ 1 hA_ne
  have h_div_alpha : ∀ x : ℝ, x / alpha = x * alphaInv := by
    intro x
    dsimp [alpha]
    calc x / (1 / alphaInv)
      _ = (x * 1) / (1 / alphaInv) := by ring
      _ = (x * (alphaInv * (1 / alphaInv))) / (1 / alphaInv) := by rw [h_inv_mul]
      _ = ((x * alphaInv) * (1 / alphaInv)) / (1 / alphaInv) := by ring
      _ = x * alphaInv := mul_div_cancel_right₀ (x * alphaInv) ha_ne
  have h_mp : protonMass = (94 / 7) * alphaInv := by
    rw [protonMass_and_neutron_split_identities.1]
    dsimp [m_e]
    ring
  have h_ss : strangeSubtraction = (4 / 7) * alphaInv := by
    dsimp [strangeSubtraction, m_e]
    ring
  have h_cos_mul : cosThetaC * alphaInv = alphaInv - 7 / 2 := by
    dsimp [cosThetaC, alpha]
    calc (1 - (7 / 2) * (1 / alphaInv)) * alphaInv
      _ = alphaInv - (7 / 2) * (alphaInv * (1 / alphaInv)) := by ring
      _ = alphaInv - (7 / 2) * 1 := by rw [h_inv_mul]
      _ = alphaInv - 7 / 2 := by ring
  have h35 : v = (14 * alphaInv * (66 * alphaInv - 235)) / 35 := by
    dsimp [v]
    rw [h_div_alpha (2 * protonMass * cosThetaC), h_div_alpha strangeSubtraction, h_mp, h_ss]
    calc 2 * ((94 / 7) * alphaInv) * cosThetaC * alphaInv -
           (4 / 5) * ((4 / 7) * alphaInv * alphaInv)
      _ = (188 / 7) * alphaInv * (cosThetaC * alphaInv) - (16 / 35) * alphaInv ^ 2 := by ring
      _ = (188 / 7) * alphaInv * (alphaInv - 7 / 2) - (16 / 35) * alphaInv ^ 2 := by
          rw [h_cos_mul]
      _ = (14 * alphaInv * (66 * alphaInv - 235)) / 35 := by ring
  refine ⟨h35, ?_⟩
  rw [h35]
  ring

/--
Theorem (Continuum Confinement Pressure Regimes & Exact Weinberg Boson Identity):
-/
theorem continuum_confinement_and_weinberg_relations
    (a_comp a_str ξ σ : ℝ)
    (hc_pos : 0 < a_comp) (hc_lt : a_comp < 1)
    (hs_gt : 1 < a_str) (hξ : 0 ≤ ξ) (hσ : 0 < σ) :
    stringTension < confinementPressure a_comp ∧
    confinementPressure 1 = stringTension ∧
    confinementPressure a_str < stringTension ∧
    (minorRadiusFromTension ξ σ) ^ 2 * σ = ξ ∧
    11 * (1 + alpha) * m_W = 10 * (1 - 3 * alpha) * m_Z := by
  have hc4_pos : 0 < a_comp ^ 4 := pow_pos hc_pos 4
  have hc_diff : 0 < 1 - a_comp := by linarith
  have hc_sum : 0 < 1 + a_comp + a_comp ^ 2 + a_comp ^ 3 := by positivity
  have hc4_lt : a_comp ^ 4 < 1 := by
    have h_f := mul_pos hc_diff hc_sum
    linarith [show (1 - a_comp) * (1 + a_comp + a_comp ^ 2 + a_comp ^ 3) =
                1 - a_comp ^ 4 by ring]
  have hc_press : stringTension < confinementPressure a_comp := by
    dsimp [confinementPressure, stringTension]
    have h_inv_pos : 0 < 1 / (a_comp ^ 4) := by positivity
    have h_mul := mul_lt_mul_of_pos_right hc4_lt h_inv_pos
    have h_canc : (a_comp ^ 4) * (1 / (a_comp ^ 4)) = 1 := by
      rw [one_div]
      exact mul_inv_cancel₀ (ne_of_gt hc4_pos)
    linarith
  have h_eq1 : confinementPressure 1 = stringTension := by
    dsimp [confinementPressure, stringTension]; norm_num
  have hs_pos : 0 < a_str := lt_trans zero_lt_one hs_gt
  have hs4_pos : 0 < a_str ^ 4 := pow_pos hs_pos 4
  have hs_diff : 0 < a_str - 1 := by linarith
  have hs_sum : 0 < 1 + a_str + a_str ^ 2 + a_str ^ 3 := by positivity
  have hs4_gt : 1 < a_str ^ 4 := by
    have h_f := mul_pos hs_diff hs_sum
    linarith [show (a_str - 1) * (1 + a_str + a_str ^ 2 + a_str ^ 3) =
                a_str ^ 4 - 1 by ring]
  have hs_press : confinementPressure a_str < stringTension := by
    dsimp [confinementPressure, stringTension]
    have h_inv_pos : 0 < 1 / (a_str ^ 4) := by positivity
    have h_mul := mul_lt_mul_of_pos_right hs4_gt h_inv_pos
    have h_canc : (a_str ^ 4) * (1 / (a_str ^ 4)) = 1 := by
      rw [one_div]
      exact mul_inv_cancel₀ (ne_of_gt hs4_pos)
    linarith
  have h_rad : (minorRadiusFromTension ξ σ) ^ 2 * σ = ξ := by
    dsimp [minorRadiusFromTension]
    rw [Real.sq_sqrt (div_nonneg hξ (le_of_lt hσ))]
    exact div_mul_cancel₀ ξ (ne_of_gt hσ)
  have h_weinberg : 11 * (1 + alpha) * m_W = 10 * (1 - 3 * alpha) * m_Z := by
    dsimp [m_W, m_Z]; ring
  exact ⟨hc_press, h_eq1, hs_press, h_rad, h_weinberg⟩

#print axioms bogomolny_confinement_pressure_balance
#print axioms universal_bogomolny_radial_minimum_nat
#print axioms steiner_electroweak_and_cabibbo_shares
#print axioms universal_ew_vev_polynomial_factorization_nat
#print axioms electroweak_vev_and_boson_hierarchy

end TVE
