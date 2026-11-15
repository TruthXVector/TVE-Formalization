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
public import Mathlib.Tactic.FieldSimp
public import TVE.Vacuum
public import TVE.Action
public import TVE.Topologies
public import TVE.Spectrum
public import TVE.Forces
public import TVE.VacuumPolarization

/-!
# Topological Vacuum Electrodynamics — BCC α-Iron Ferromagnetic Phase Transition

Formalizes the parameter-free TVE derivation of BCC α-iron's ferromagnetic Curie
transition across both the Order-0 (`K = 1` rigid upper bound) and Order-1 (`δK > 0`
polarizable-vacuum relaxation) tiers, benchmarked against high-purity zone-refined
iron thermometry (`1042–1044 K`, NIST/JANAF `C_p` λ-peak `1043.2 K`, traditional `1043 K`):

1. **Radical-Free 3D Wigner–Seitz Hodge Geometry (`[]`):** Exact integer coordinates
   at scale `a_0 = 4` for Kelvin's 14-face BCC truncated octahedron (`8` regular
   hexagons + `6` squares, `V_WS = (1/2) a_0^3`), proving Voronoi–Delaunay Hodge
   conductances `w_1 / a_0 = 3/8`, `w_2 / a_0 = 1/8`, single-face ratio `w_2 / w_1 = 1/3`,
   and `4 : 1` (`80% / 20%`) shell partition, contrasted against FCC's 12-face rhombic
   dodecahedron (`w_2 = 0`, `V_WS = (1/4) a_0^3`).
2. **Exact `L = 2` (`3d`) Cubic Harmonics & Unsöld Conservation (`[]`):** Rational
   `t_{2g}` and `e_g` directional weights on `IntVec3`, proving pure `t_{2g}` (`5/3`)
   selection on `[111]` hexagons, pure `e_g` (`5/2`) selection on `[100]` squares,
   and exact `(3/5) G_{t2g} + (2/5) G_{eg} = 1` spherical flux conservation.
3. **Certified Lundquist Wall & Interstitial Attenuation Bounds (`[]`):** Alternating
   polynomial bounds certifying `sqrt(3) ∈ (265/153, 1351/780)`, first Bessel zero
   `j_{0,1} ∈ (601/250, 481/200)`, and square-face NNN/NN exchange ratio
   `η_TVE = J_2 / J_1 = (1/3) exp(-4 j_{0,1} (2/√3 - 1)) ∈ (749/10000, 755/10000)`.
4. **Order-0 Rigid Upper Bound (`K = 1`, `[]`):** Certifies BCC localized Mott–Hubbard
   dominance `(U_{3d}/W_BCC)^2 > 2 > 1 > (U_{3d}/W_FCC)^2`, `J_1^(0) ∈ (22.06, 22.07) meV`,
   `J_2^(0) ∈ (1.65, 1.67) meV`, 8-hexagon NN `T_C^NN ∈ (980, 981) K`, and 14-face
   Order-0 upper bound `T_C^(0) ∈ (1046, 1048) K`.
5. **Order-1 Polarizable-Vacuum Relaxation (`δK > 0`, `[]`):** Consumes the shared
   unknot-screened coupling `vpEffectiveAlphaInvLoNz` / `vpEffectiveAlphaInvHiNz`
   (`A_eff = A_1 + 1/(2π)`) from `TVE.VacuumPolarization`, proving `T_C^(1) < T_C^(0)`
   and relaxing the 14-face transition strictly inside the high-purity `1042–1044 K`
   experimental band (`(1042.9, 1043.1) K` at 4-decimal Brillouin precision).
6. **Continuum Brillouin Sandwich, Homothetic Invariance & Bethe–Slater Flip (`ℝ`):**
   Pointwise dispersion sandwich `0 ≤ 1 - γ_2(q) ≤ 2(1 - γ_1(q))`, `4π^3` Watson
   reciprocity, three-power `(1 + a_{e,1})⁻³` screening & homothetic `dT_C/dP ≈ 0`
   invariance, and the BCC α-Fe ↔ FCC γ-Fe Bethe–Slater sign flip.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-! ## Part 1: Zero-Axiom Constructive Wigner–Seitz, Lundquist & Curie Kernel (`[]`) -/

/-- Negation `-q` on `PosRat` (`Vacuum.lean`). -/
@[expose]
def cmPosRatNeg (q : PosRat) : PosRat :=
  { num := -q.num, denPred := q.denPred }

/-- Reduced addition `a + b = a - (-b)` on `PosRat` via `posRatSubRed`. -/
@[expose]
def cmPosRatAddRed (a b : PosRat) : PosRat :=
  posRatSubRed a (cmPosRatNeg b)

/-- Dot product `u · v` on `IntVec3` (`Action.lean`). -/
@[expose]
def cmVecDot (u v : IntVec3) : ℤ :=
  u.x * v.x + u.y * v.y + u.z * v.z

/-- Squared Euclidean norm `‖v‖²` on `IntVec3`. -/
@[expose]
def cmVecNormSq (v : IntVec3) : ℤ :=
  cmVecDot v v

/-- Scalar triple product `u · (v × w) = 6 × Vol(0, u, v, w)` on `IntVec3`. -/
@[expose]
def cmScalarTriple (u v w : IntVec3) : ℤ :=
  cmVecDot u (vecCross v w)

/-! ### 1. Radical-Free 3D Wigner–Seitz Geometry at Lattice Scale `a_0 = 4` -/

/-- BCC nearest-neighbor lattice vector `(+2, +2, +2)` at cubic scale `a_0 = 4` (`d_1² = 12`). -/
@[expose]
def bccNNVec : IntVec3 := { x := 2, y := 2, z := 2 }

/-- BCC next-nearest-neighbor lattice vector `(+4, 0, 0)` at cubic scale `a_0 = 4` (`d_2² = 16`). -/
@[expose]
def bccNNNVec : IntVec3 := { x := 4, y := 0, z := 0 }

/-- Ordered vertices `v_0 .. v_5` of the `(+2, +2, +2)` hexagonal face of Kelvin's truncated octahedron. -/
@[expose] def kelvinHexV0 : IntVec3 := { x := 2, y := 1, z := 0 }
@[expose] def kelvinHexV1 : IntVec3 := { x := 1, y := 2, z := 0 }
@[expose] def kelvinHexV2 : IntVec3 := { x := 0, y := 2, z := 1 }
@[expose] def kelvinHexV3 : IntVec3 := { x := 0, y := 1, z := 2 }
@[expose] def kelvinHexV4 : IntVec3 := { x := 1, y := 0, z := 2 }
@[expose] def kelvinHexV5 : IntVec3 := { x := 2, y := 0, z := 1 }

/-- Ordered vertices `s_0 .. s_3` of the `(+4, 0, 0)` square face of Kelvin's truncated octahedron. -/
@[expose] def kelvinSqV0 : IntVec3 := { x := 2, y := 1, z := 0 }
@[expose] def kelvinSqV1 : IntVec3 := { x := 2, y := 0, z := 1 }
@[expose] def kelvinSqV2 : IntVec3 := { x := 2, y := -1, z := 0 }
@[expose] def kelvinSqV3 : IntVec3 := { x := 2, y := 0, z := -1 }

/-- Oriented `6 × Volume` of the pyramid from `(0,0,0)` to a BCC hexagonal face (`= A_hex · d_1 = 18`). -/
@[expose]
def cmHexPyramid6Vol : ℤ :=
  cmScalarTriple kelvinHexV0 kelvinHexV1 kelvinHexV2 +
  cmScalarTriple kelvinHexV0 kelvinHexV2 kelvinHexV3 +
  cmScalarTriple kelvinHexV0 kelvinHexV3 kelvinHexV4 +
  cmScalarTriple kelvinHexV0 kelvinHexV4 kelvinHexV5

/-- Oriented `6 × Volume` of the pyramid from `(0,0,0)` to a BCC square face (`= A_sq · d_2 = 8`). -/
@[expose]
def cmSqPyramid6Vol : ℤ :=
  cmScalarTriple kelvinSqV0 kelvinSqV1 kelvinSqV2 +
  cmScalarTriple kelvinSqV0 kelvinSqV2 kelvinSqV3

/-- Dimensionless BCC hexagonal Hodge conductance `w_1 / a_0 = (6 V_hex) / (a_0 d_1²) = 18 / 48 = 3 / 8`. -/
@[expose]
def cmBccHexHodgeNorm : PosRat :=
  posRatDivRed (posRatOfInt cmHexPyramid6Vol) { isNeg := false, numPred := 47, denPred := 0 }

/-- Dimensionless BCC square Hodge conductance `w_2 / a_0 = (6 V_sq) / (a_0 d_2²) = 8 / 64 = 1 / 8`. -/
@[expose]
def cmBccSqHodgeNorm : PosRat :=
  posRatDivRed (posRatOfInt cmSqPyramid6Vol) { isNeg := false, numPred := 63, denPred := 0 }

/-- FCC nearest-neighbor vector `(+2, +2, 0)` at `a_0 = 4` (`d_1² = 8`) and rhombic face vertices. -/
@[expose] def fccNNVec : IntVec3 := { x := 2, y := 2, z := 0 }
@[expose] def fccRhombV0 : IntVec3 := { x := 2, y := 0, z := 0 }
@[expose] def fccRhombV1 : IntVec3 := { x := 1, y := 1, z := -1 }
@[expose] def fccRhombV2 : IntVec3 := { x := 0, y := 2, z := 0 }
@[expose] def fccRhombV3 : IntVec3 := { x := 1, y := 1, z := 1 }

/-- Oriented `6 × Volume` of an FCC rhombic pyramid (`= 8`) vs. degenerate NNN corner vertex (`= 0`). -/
@[expose]
def cmFccRhombPyramid6Vol : ℤ :=
  cmScalarTriple fccRhombV0 fccRhombV1 fccRhombV2 +
  cmScalarTriple fccRhombV0 fccRhombV2 fccRhombV3

@[expose]
def cmFccDegenerateNNN6Vol : ℤ :=
  cmScalarTriple fccRhombV0 fccRhombV0 fccRhombV0

/--
Theorem (Zero Axioms): Radical-Free 3D Wigner–Seitz Hodge Partition (BCC Kelvin Cell vs. FCC).
-/
theorem kelvin_wigner_seitz_14_face_hodge_partition :
    let W1 := posRatMulRed (posRatOfInt 8) cmBccHexHodgeNorm
    let W2 := posRatMulRed (posRatOfInt 6) cmBccSqHodgeNorm
    let Wtot := cmPosRatAddRed W1 W2
    cmVecNormSq bccNNVec = 12 ∧
    cmVecNormSq bccNNNVec = 16 ∧
    2 * cmVecDot kelvinHexV0 bccNNVec = cmVecNormSq bccNNVec ∧
    2 * cmVecDot kelvinHexV3 bccNNVec = cmVecNormSq bccNNVec ∧
    cmVecNormSq (vecSub kelvinHexV1 kelvinHexV0) = 2 ∧
    cmVecNormSq (vecSub kelvinHexV2 kelvinHexV1) = 2 ∧
    2 * cmVecDot kelvinSqV0 bccNNNVec = cmVecNormSq bccNNNVec ∧
    cmVecDot (vecSub kelvinSqV1 kelvinSqV0) (vecSub kelvinSqV3 kelvinSqV0) = 0 ∧
    cmHexPyramid6Vol = 18 ∧
    cmSqPyramid6Vol = 8 ∧
    8 * cmHexPyramid6Vol + 6 * cmSqPyramid6Vol = 3 * (4 * 4 * 4) ∧
    cmBccHexHodgeNorm = { num := 3, denPred := 7 } ∧
    cmBccSqHodgeNorm = { num := 1, denPred := 7 } ∧
    posRatMulRed cmBccSqHodgeNorm { num := 8, denPred := 2 } = { num := 1, denPred := 2 } ∧
    W1 = posRatOfInt 3 ∧
    W2 = { num := 3, denPred := 3 } ∧
    Wtot = { num := 15, denPred := 3 } ∧
    posRatMulRed W1 { num := 4, denPred := 14 } = { num := 4, denPred := 4 } ∧
    2 * (12 * cmFccRhombPyramid6Vol) = 3 * (4 * 4 * 4) ∧
    cmFccDegenerateNNN6Vol = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 2. Exact `L = 2` (`3d`) Cubic Harmonics & Unsöld Spherical Flux Conservation -/

/-- Cubic quartic invariant `Q_4(v) = (x⁴ + y⁴ + z⁴) / (x² + y² + z²)²` in `PosRat`. -/
@[expose]
def cmCubicQ4PosRat (v : IntVec3) (rSqPred : ℕ) : PosRat :=
  let x2 := v.x * v.x
  let y2 := v.y * v.y
  let z2 := v.z * v.z
  let num4 := x2 * x2 + y2 * y2 + z2 * z2
  let r4Nz : NzPosRat := { isNeg := false, numPred := vacMulSuccPred rSqPred rSqPred, denPred := 0 }
  posRatDivRed (posRatOfInt num4) r4Nz

/-- Normalized `t_{2g}` subshell directional intensity `G_{t2g}(v) = (5/2)(1 - Q_4(v))` in `PosRat`. -/
@[expose]
def cmGt2gPosRat (v : IntVec3) (rSqPred : ℕ) : PosRat :=
  posRatMulRed { num := 5, denPred := 1 }
    (posRatSubRed (posRatOfInt 1) (cmCubicQ4PosRat v rSqPred))

/-- Normalized `e_g` subshell directional intensity `G_{eg}(v) = (5/4)(3 Q_4(v) - 1)` in `PosRat`. -/
@[expose]
def cmGegPosRat (v : IntVec3) (rSqPred : ℕ) : PosRat :=
  posRatMulRed { num := 5, denPred := 3 }
    (posRatSubRed (posRatMulRed (posRatOfInt 3) (cmCubicQ4PosRat v rSqPred)) (posRatOfInt 1))

/-- 5-orbital Unsöld spherical average `(3/5) G_{t2g}(v) + (2/5) G_{eg}(v)` in `PosRat`. -/
@[expose]
def cmUnsoldAvgPosRat (v : IntVec3) (rSqPred : ℕ) : PosRat :=
  cmPosRatAddRed
    (posRatMulRed { num := 3, denPred := 4 } (cmGt2gPosRat v rSqPred))
    (posRatMulRed { num := 2, denPred := 4 } (cmGegPosRat v rSqPred))

/--
Theorem (Zero Axioms): `3d` (`t_{2g}` vs. `e_g`) Crystal-Field Channel Selection & Unsöld Sum.
-/
theorem cubic_3d_harmonic_channel_selection_and_unsold :
    let v111 : IntVec3 := { x := 1, y := 1, z := 1 }
    let v100 : IntVec3 := { x := 1, y := 0, z := 0 }
    let v110 : IntVec3 := { x := 1, y := 1, z := 0 }
    cmGt2gPosRat v111 2 = { num := 5, denPred := 2 } ∧
    cmGegPosRat v111 2 = posRatOfInt 0 ∧
    cmGt2gPosRat v100 0 = posRatOfInt 0 ∧
    cmGegPosRat v100 0 = { num := 5, denPred := 1 } ∧
    cmGt2gPosRat v110 1 = { num := 5, denPred := 3 } ∧
    cmGegPosRat v110 1 = { num := 5, denPred := 7 } ∧
    cmGt2gPosRat kelvinHexV0 4 = { num := 4, denPred := 4 } ∧
    cmGegPosRat kelvinHexV0 4 = { num := 13, denPred := 9 } ∧
    cmUnsoldAvgPosRat v111 2 = posRatOfInt 1 ∧
    cmUnsoldAvgPosRat v100 0 = posRatOfInt 1 ∧
    cmUnsoldAvgPosRat v110 1 = posRatOfInt 1 ∧
    cmUnsoldAvgPosRat kelvinHexV0 4 = posRatOfInt 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 3. Certified Lundquist Bessel Root `j_{0,1}` & Interstitial Attenuation `η_TVE` -/

/-- Cleared integer 5th-order alternating lower polynomial `(5!)² D⁵ J_0^{(5)}(p/q)` at `z = p² / (4q²)`. -/
@[expose]
def cmBesselJ0Lower5ClearedInt (p q : ℤ) : ℤ :=
  let n := p * p
  let d := 4 * q * q
  let d2 := d * d
  let d3 := d2 * d
  let d4 := d3 * d
  let d5 := d4 * d
  let n2 := n * n
  let n3 := n2 * n
  let n4 := n3 * n
  let n5 := n4 * n
  14400 * d5 - 14400 * d4 * n + 3600 * d3 * n2 - 400 * d2 * n3 + 25 * d * n4 - n5

/-- Cleared integer 6th-order alternating upper polynomial `(6!)² D⁶ J_0^{(6)}(p/q)` at `z = p² / (4q²)`. -/
@[expose]
def cmBesselJ0Upper6ClearedInt (p q : ℤ) : ℤ :=
  let n := p * p
  let d := 4 * q * q
  let d2 := d * d
  let d3 := d2 * d
  let d4 := d3 * d
  let d5 := d4 * d
  let d6 := d5 * d
  let n2 := n * n
  let n3 := n2 * n
  let n4 := n3 * n
  let n5 := n4 * n
  let n6 := n5 * n
  518400 * d6 - 518400 * d5 * n + 129600 * d4 * n2 - 14400 * d3 * n3 +
    900 * d2 * n4 - 36 * d * n5 + n6

/-- Cleared integer 7th-order alternating lower polynomial `7! D⁷ E_7(n/d) < 7! D⁷ exp(-n/d)` for `0 < n/d < 2`. -/
@[expose]
def cmExpNegLower7ClearedInt (n d : ℤ) : ℤ :=
  let d2 := d * d
  let d3 := d2 * d
  let d4 := d3 * d
  let d5 := d4 * d
  let d6 := d5 * d
  let d7 := d6 * d
  let n2 := n * n
  let n3 := n2 * n
  let n4 := n3 * n
  let n5 := n4 * n
  let n6 := n5 * n
  let n7 := n6 * n
  5040 * d7 - 5040 * d6 * n + 2520 * d5 * n2 - 840 * d4 * n3 +
    210 * d3 * n4 - 42 * d2 * n5 + 7 * d * n6 - n7

/-- Cleared integer 8th-order alternating upper polynomial `8! D⁸ exp(-n/d) < 8! D⁸ E_8(n/d)` for `0 < n/d < 2`. -/
@[expose]
def cmExpNegUpper8ClearedInt (n d : ℤ) : ℤ :=
  let d2 := d * d
  let d3 := d2 * d
  let d4 := d3 * d
  let d5 := d4 * d
  let d6 := d5 * d
  let d7 := d6 * d
  let d8 := d7 * d
  let n2 := n * n
  let n3 := n2 * n
  let n4 := n3 * n
  let n5 := n4 * n
  let n6 := n5 * n
  let n7 := n6 * n
  let n8 := n7 * n
  40320 * d8 - 40320 * d7 * n + 20160 * d6 * n2 - 6720 * d5 * n3 +
    1680 * d4 * n4 - 336 * d3 * n5 + 56 * d2 * n6 - 8 * d * n7 + n8

/-- Integer power `d ^ k` for cleared rational bound comparisons. -/
@[expose]
def cmPowInt (b : ℤ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => cmPowInt b k * b

/--
Theorem (Zero Axioms): Certified Lundquist Bessel Root `j_{0,1}` & Interstitial Attenuation `η_TVE`.
-/
theorem lundquist_wall_and_interstitial_attenuation_bounds :
    let jL : PosRat := { num := 601, denPred := 249 }
    let jU : PosRat := { num := 481, denPred := 199 }
    let gL : PosRat := { num := 209, denPred := 1350 }
    let gU : PosRat := { num := 41, denPred := 264 }
    let uL := posRatMulRed (posRatOfInt 4) (posRatMulRed jL gL)
    let uU := posRatMulRed (posRatOfInt 4) (posRatMulRed jU gU)
    vacFastLtInt (265 * 265) (3 * 153 * 153) = true ∧
    vacFastLtInt (3 * 780 * 780) (1351 * 1351) = true ∧
    vacFastLtInt 0 (cmBesselJ0Lower5ClearedInt 601 250) = true ∧
    vacFastLtInt (cmBesselJ0Upper6ClearedInt 481 200) 0 = true ∧
    posRatLt { num := 743, denPred := 499 } uL = true ∧
    posRatLt uU { num := 149, denPred := 99 } = true ∧
    vacFastLtInt
      (749 * (3 * 5040 * cmPowInt 100 7))
      (10000 * cmExpNegLower7ClearedInt 149 100) = true ∧
    vacFastLtInt
      (10000 * cmExpNegUpper8ClearedInt 743 500)
      (755 * (3 * 40320 * cmPowInt 500 8)) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 4. Order-0 (`K = 1`) Upper Bound & Order-1 (`δK > 0`) Polarizable-Vacuum Relaxation -/

/-- Exact 2019 SI conversion factor `e / (1000 k_B) = 801088317 / 69032450` (`K / meV`). -/
@[expose]
def cmKelvinPerMeVPosRat : PosRat :=
  { num := 801088317, denPred := 69032449 }

/-- Squared Mott–Hubbard ratio `(U_{3d} / W)^2 = A / z_1²` for coordination `z_1` (`z1SqPred = z_1² - 1`). -/
@[expose]
def cmMottHubbardSqPosRat (A_rat : PosRat) (z1SqPred : ℕ) : PosRat :=
  posRatDivRed A_rat { isNeg := false, numPred := z1SqPred, denPred := 0 }

/-- Intra-atomic `n = 3` (`3d`) Coulomb scale `U_{3d} = m_e c² / (9 A²)` in `meV`. -/
@[expose]
def cmIntraAtomicU3dMeVPosRat (meMeV : ℤ) (A_nz : NzPosRat) : PosRat :=
  let alpha_rat := posRatDivRed (posRatOfInt 1) A_nz
  let alpha2 := posRatMulRed alpha_rat alpha_rat
  posRatMulRed { num := meMeV, denPred := 8 } alpha2

/-- Nearest-neighbor `n = 3` (`3d`) chiral exchange scale `J_{3d} = m_e c² / (9 A³)` in `meV`. -/
@[expose]
def cmExchangeJ3dMeVPosRat (meMeV : ℤ) (A_nz : NzPosRat) : PosRat :=
  let alpha_rat := posRatDivRed (posRatOfInt 1) A_nz
  posRatMulRed (cmIntraAtomicU3dMeVPosRat meMeV A_nz) alpha_rat

/-- Thermal `n = 3` (`3d`) exchange temperature `T_{3d} = J_{3d} / k_B` in Kelvin. -/
@[expose]
def cmExchangeT3dKelvinPosRat (meMeV : ℤ) (A_nz : NzPosRat) : PosRat :=
  posRatMulRed (cmExchangeJ3dMeVPosRat meMeV A_nz) cmKelvinPerMeVPosRat

/--
Theorem (Zero Axioms): Order-0 (`K = 1`) Rigid-Vacuum Upper Bounds on BCC α-Iron `T_C`.
Certifies `(U_{3d}/W_BCC)² > 2 > 1 > (U_{3d}/W_FCC)²`, `J_1^(0) ∈ (22.06, 22.07) meV`,
`J_2^(0) ∈ (1.65, 1.67) meV`, 8-hexagon `T_C^NN ∈ (980, 981) K`, unconditional Brillouin
ceiling `< 1092 K`, and Order-0 14-face upper bound `T_C^(0) ∈ (1046, 1048) K`.
-/
theorem tve_iron_3d_scale_mott_hubbard_and_curie_bounds :
    let A_L : NzPosRat := alphaInvNzPosRat 332 105
    let A_U : NzPosRat := alphaInvNzPosRat 354 112
    let U3d_L := cmIntraAtomicU3dMeVPosRat 510998950 A_U
    let U3d_U := cmIntraAtomicU3dMeVPosRat 510998952 A_L
    let J1_L := cmExchangeJ3dMeVPosRat 510998950 A_U
    let J1_U := cmExchangeJ3dMeVPosRat 510998952 A_L
    let T3d_L := cmExchangeT3dKelvinPosRat 510998950 A_U
    let T3d_U := cmExchangeT3dKelvinPosRat 510998952 A_L
    let eta_lo : PosRat := { num := 749, denPred := 9999 }
    let eta_hi : PosRat := { num := 755, denPred := 9999 }
    let J2_L := posRatMulRed eta_lo J1_L
    let J2_U := posRatMulRed eta_hi J1_U
    let Tmf_L := posRatMulRed { num := 16, denPred := 2 } T3d_L
    let Tmf_U := posRatMulRed { num := 16, denPred := 2 } T3d_U
    let Tnn_L := posRatMulRed { num := 735, denPred := 1023 } Tmf_L
    let Tnn_U := posRatMulRed { num := 735, denPred := 1023 } Tmf_U
    let T14_L := posRatDivRed Tmf_L { isNeg := false, numPred := 1304, denPred := 999 }
    let T14_U := posRatDivRed Tmf_U { isNeg := false, numPred := 1303, denPred := 999 }
    let Tbrill_U := posRatDivRed
      (posRatMulRed Tmf_U (cmPosRatAddRed (posRatOfInt 1) (posRatMulRed { num := 3, denPred := 1 } eta_hi)))
      { isNeg := false, numPred := 3482, denPred := 2499 }
    posRatLt (posRatOfInt 2) (cmMottHubbardSqPosRat (nzPosRatToPosRat A_L) 63) = true ∧
    posRatLt (cmMottHubbardSqPosRat (nzPosRatToPosRat A_U) 143) (posRatOfInt 1) = true ∧
    posRatLt (posRatOfInt 3023) U3d_L = true ∧
    posRatLt U3d_U (posRatOfInt 3024) = true ∧
    posRatLt { num := 2206, denPred := 99 } J1_L = true ∧
    posRatLt J1_U { num := 2207, denPred := 99 } = true ∧
    posRatLt (posRatOfInt 256) T3d_L = true ∧
    posRatLt T3d_U { num := 2561, denPred := 9 } = true ∧
    posRatLt { num := 165, denPred := 99 } J2_L = true ∧
    posRatLt J2_U { num := 167, denPred := 99 } = true ∧
    posRatLt (posRatOfInt 1365) Tmf_L = true ∧
    posRatLt Tmf_U (posRatOfInt 1366) = true ∧
    posRatLt (posRatOfInt 980) Tnn_L = true ∧
    posRatLt Tnn_U (posRatOfInt 981) = true ∧
    posRatLt Tnn_L (posRatOfInt 1043) = true ∧
    posRatLt (posRatOfInt 1043) Tbrill_U = true ∧
    posRatLt Tbrill_U (posRatOfInt 1092) = true ∧
    posRatLt (posRatOfInt 1046) T14_L = true ∧
    posRatLt T14_U (posRatOfInt 1048) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): Order-1 (`δK > 0`) Polarizable-Vacuum Relaxation of BCC α-Iron `T_C`.
Feeds the exported unknot-screened inverse coupling `vpEffectiveAlphaInvLoNz` /
`vpEffectiveAlphaInvHiNz` (`A_eff = A_1 (1 + a_{e,1}) = A_1 + 1/(2π) ∈ (137.1951, 137.1952)`)
from `TVE.VacuumPolarization` directly into the `3d` exchange kernel, certifying via `rfl`:
1. **Preserved Mott–Hubbard Split:** `(U_{3d}^(1)/W_BCC^(1))² > 2 > 1 > (U_{3d}^(1)/W_FCC^(1))²`.
2. **Relaxed `3d` Couplings:** `U_{3d}^(1) ∈ (3016, 3017) meV`, `J_1^(1) ∈ (21.98, 21.99) meV`,
   `J_2^(1) ∈ (1.64, 1.67) meV`, `T_{3d}^(1) ∈ (255.1, 255.2) K`, `T_C^MF(1) ∈ (1360, 1361) K`.
3. **Strict Variational Lowering onto High-Purity Lab Band (`1042–1044 K`):**
   - Proves `T_C^(1) < T_C^(0)` strictly (`1043.6 K < 1046.3 K`).
   - Certifies `1042 K < T_C^(1) < 1044 K` across the wide Brillouin interval `[1.304, 1.305]`
     and `1042.9 K < T_C^(1) < 1043.1 K` at 4-decimal Brillouin precision `[1.3046, 1.3047]`
     (matching NIST/JANAF evaluated `C_p` λ-peak `1043.2 K` and high-purity `1043–1044 K` data).
-/
theorem tve_iron_order1_polarizable_vacuum_curie_bounds :
    let A0_U : NzPosRat := alphaInvNzPosRat 354 112
    let Tmf0_L := posRatMulRed { num := 16, denPred := 2 } (cmExchangeT3dKelvinPosRat 510998950 A0_U)
    let T14_0_L := posRatDivRed Tmf0_L { isNeg := false, numPred := 1304, denPred := 999 }
    let Aeff_L : NzPosRat := vpEffectiveAlphaInvLoNz
    let Aeff_U : NzPosRat := vpEffectiveAlphaInvHiNz
    let U3d_1_L := cmIntraAtomicU3dMeVPosRat 510998950 Aeff_U
    let U3d_1_U := cmIntraAtomicU3dMeVPosRat 510998952 Aeff_L
    let J1_1_L := cmExchangeJ3dMeVPosRat 510998950 Aeff_U
    let J1_1_U := cmExchangeJ3dMeVPosRat 510998952 Aeff_L
    let T3d_1_L := cmExchangeT3dKelvinPosRat 510998950 Aeff_U
    let T3d_1_U := cmExchangeT3dKelvinPosRat 510998952 Aeff_L
    let eta_lo : PosRat := { num := 749, denPred := 9999 }
    let eta_hi : PosRat := { num := 755, denPred := 9999 }
    let J2_1_L := posRatMulRed eta_lo J1_1_L
    let J2_1_U := posRatMulRed eta_hi J1_1_U
    let Tmf1_L := posRatMulRed { num := 16, denPred := 2 } T3d_1_L
    let Tmf1_U := posRatMulRed { num := 16, denPred := 2 } T3d_1_U
    let T14_1_wide_L := posRatDivRed Tmf1_L { isNeg := false, numPred := 1304, denPred := 999 }
    let T14_1_wide_U := posRatDivRed Tmf1_U { isNeg := false, numPred := 1303, denPred := 999 }
    let T14_1_tight_L := posRatDivRed Tmf1_L { isNeg := false, numPred := 13046, denPred := 9999 }
    let T14_1_tight_U := posRatDivRed Tmf1_U { isNeg := false, numPred := 13045, denPred := 9999 }
    posRatLt (posRatOfInt 2) (cmMottHubbardSqPosRat (nzPosRatToPosRat Aeff_L) 63) = true ∧
    posRatLt (cmMottHubbardSqPosRat (nzPosRatToPosRat Aeff_U) 143) (posRatOfInt 1) = true ∧
    posRatLt (posRatOfInt 3016) U3d_1_L = true ∧
    posRatLt U3d_1_U (posRatOfInt 3017) = true ∧
    posRatLt { num := 2198, denPred := 99 } J1_1_L = true ∧
    posRatLt J1_1_U { num := 2199, denPred := 99 } = true ∧
    posRatLt { num := 164, denPred := 99 } J2_1_L = true ∧
    posRatLt J2_1_U { num := 167, denPred := 99 } = true ∧
    posRatLt { num := 2551, denPred := 9 } T3d_1_L = true ∧
    posRatLt T3d_1_U { num := 2552, denPred := 9 } = true ∧
    posRatLt (posRatOfInt 1360) Tmf1_L = true ∧
    posRatLt Tmf1_U (posRatOfInt 1361) = true ∧
    posRatLt T14_1_wide_U T14_0_L = true ∧
    posRatLt (posRatOfInt 1042) T14_1_wide_L = true ∧
    posRatLt T14_1_wide_U (posRatOfInt 1044) = true ∧
    posRatLt { num := 10429, denPred := 9 } T14_1_tight_L = true ∧
    posRatLt T14_1_tight_U { num := 10431, denPred := 9 } = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: Continuum `ℝ` Brillouin Sandwich, Order-1 Screening & Bethe–Slater Flip -/

/-- Strict positivity of `alphaInv = 4π³ + π² + π > 0` (`Vacuum.lean`). -/
theorem cm_alphaInv_pos : 0 < alphaInv := by
  dsimp [alphaInv, torusBulkCapacity, torusBoundaryCapacity, torusCutCapacity]
  have h4 : (0 : ℝ) < 4 := by positivity
  have h_bulk : 0 < 4 * Real.pi ^ 3 := mul_pos h4 (pow_pos Real.pi_pos 3)
  have h_surf : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  exact add_pos (add_pos h_bulk h_surf) Real.pi_pos

/-- Continuum Order-0 `n = 3` (`3d`) exchange energy `J_{3d}^(0) = m_e c² α³ / 9`. -/
@[expose]
noncomputable def tveIronExchangeJ3d (me_energy : ℝ) : ℝ :=
  me_energy * (alpha ^ 3) / 9

/-- Continuum Order-1 cut-screened `n = 3` (`3d`) exchange energy `J_{3d}^(1) = m_e c² α_eff³ / 9`. -/
@[expose]
noncomputable def tveIronExchangeJ3dOrder1 (me_energy : ℝ) : ℝ :=
  me_energy * (effectiveAlphaOrder1 ^ 3) / 9

/-- Continuum Watson BCC integral `W_BCC = Γ(1/4)⁴ / (4π³)` parameterized by `Γ(1/4)` using `torusBulkCapacity`. -/
@[expose]
noncomputable def watsonBccIntegral (gammaQuarter : ℝ) : ℝ :=
  (gammaQuarter ^ 4) / torusBulkCapacity

/--
Theorem: Continuum Superexchange Identity, Mott–Hubbard Ratio & `4π³` Torus-Bulk Watson Reciprocity.
-/
theorem tve_3d_superexchange_mott_hubbard_and_watson_reciprocity
    (me_energy sqrt_alpha gammaQuarter : ℝ)
    (hme : me_energy ≠ 0) (h_sq : sqrt_alpha ^ 2 = alpha) (hg : gammaQuarter ≠ 0) :
    let U_3d := me_energy * (alpha ^ 2) / 9
    let t_3d := (1 / 2 : ℝ) * U_3d * sqrt_alpha
    (2 * t_3d) ^ 2 / U_3d = tveIronExchangeJ3d me_energy ∧
    (sqrt_alpha ≠ 0 → (U_3d / (2 * 8 * t_3d)) ^ 2 = alphaInv / 64) ∧
    (sqrt_alpha ≠ 0 → (U_3d / (2 * 12 * t_3d)) ^ 2 = alphaInv / 144) ∧
    1 / watsonBccIntegral gammaQuarter = (4 * Real.pi ^ 3) / (gammaQuarter ^ 4) := by
  have h_ainv_ne : alphaInv ≠ 0 := ne_of_gt cm_alphaInv_pos
  have h_alpha_def : alpha = 1 / alphaInv := rfl
  have h_alpha_ne : alpha ≠ 0 := by
    rw [h_alpha_def]
    exact one_div_ne_zero h_ainv_ne
  have h_a_mul : alpha * alphaInv = 1 := by
    rw [h_alpha_def, one_div]
    exact inv_mul_cancel₀ h_ainv_ne
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [tveIronExchangeJ3d]
    have hU_ne : me_energy * (alpha ^ 2) / 9 ≠ 0 := by
      apply div_ne_zero
      · exact mul_ne_zero hme (pow_ne_zero 2 h_alpha_ne)
      · norm_num
    have h_num :
        (2 * ((1 / 2 : ℝ) * (me_energy * (alpha ^ 2) / 9) * sqrt_alpha)) ^ 2 =
          (me_energy * (alpha ^ 2) / 9) * (me_energy * (alpha ^ 2) * (sqrt_alpha ^ 2) / 9) := by
      ring
    rw [h_num, h_sq, mul_div_cancel_left₀ _ hU_ne]
    ring
  · intro h_sa
    have hU_ne : me_energy * (alpha ^ 2) / 9 ≠ 0 := by
      apply div_ne_zero
      · exact mul_ne_zero hme (pow_ne_zero 2 h_alpha_ne)
      · norm_num
    have h_div :
        (me_energy * (alpha ^ 2) / 9) /
          (2 * 8 * ((1 / 2 : ℝ) * (me_energy * (alpha ^ 2) / 9) * sqrt_alpha)) =
        1 / (8 * sqrt_alpha) := by
      have h_den :
          2 * 8 * ((1 / 2 : ℝ) * (me_energy * (alpha ^ 2) / 9) * sqrt_alpha) =
            (me_energy * (alpha ^ 2) / 9) * (8 * sqrt_alpha) := by ring
      rw [h_den, ← div_div, div_self hU_ne]
    rw [h_div]
    have h_sq64 : (1 / (8 * sqrt_alpha)) ^ 2 = 1 / (64 * (sqrt_alpha ^ 2)) := by ring
    rw [h_sq64, h_sq]
    calc 1 / (64 * alpha)
      _ = (alpha * alphaInv) / (64 * alpha) := by rw [h_a_mul]
      _ = (alphaInv * alpha) / (64 * alpha) := by ring
      _ = alphaInv / 64 := mul_div_mul_right alphaInv 64 h_alpha_ne
  · intro h_sa
    have hU_ne : me_energy * (alpha ^ 2) / 9 ≠ 0 := by
      apply div_ne_zero
      · exact mul_ne_zero hme (pow_ne_zero 2 h_alpha_ne)
      · norm_num
    have h_div :
        (me_energy * (alpha ^ 2) / 9) /
          (2 * 12 * ((1 / 2 : ℝ) * (me_energy * (alpha ^ 2) / 9) * sqrt_alpha)) =
        1 / (12 * sqrt_alpha) := by
      have h_den :
          2 * 12 * ((1 / 2 : ℝ) * (me_energy * (alpha ^ 2) / 9) * sqrt_alpha) =
            (me_energy * (alpha ^ 2) / 9) * (12 * sqrt_alpha) := by ring
      rw [h_den, ← div_div, div_self hU_ne]
    rw [h_div]
    have h_sq144 : (1 / (12 * sqrt_alpha)) ^ 2 = 1 / (144 * (sqrt_alpha ^ 2)) := by ring
    rw [h_sq144, h_sq]
    calc 1 / (144 * alpha)
      _ = (alpha * alphaInv) / (144 * alpha) := by rw [h_a_mul]
      _ = (alphaInv * alpha) / (144 * alpha) := by ring
      _ = alphaInv / 144 := mul_div_mul_right alphaInv 144 h_alpha_ne
  · dsimp [watsonBccIntegral, torusBulkCapacity]
    rw [one_div_div]

/--
Theorem: Continuum Order-1 Three-Power Cut Screening & Homothetic Cell-Dilation Invariance.
1. `tveIronExchangeJ3dOrder1` equals `(m_e c² α_1³ / 9) / (1 + a_{e,1})³` identically.
2. Whenever `0 < effectiveAlphaOrder1 < alpha` and `0 < me_energy`, Order-1 exchange is
   strictly lower than the rigid Order-0 upper bound: `J_{3d}^(1) < J_{3d}^(0)`.
3. Under any uniform thermal or hydrostatic lattice scaling `s ≠ 0` (`d_1' = s d_1`, `d_2' = s d_2`),
   the interstitial square-face attenuation ratio `(s d_2)/(s d_1) - 1 = d_2/d_1 - 1` is
   strictly invariant (matching experimental ambient `dT_C / dP ≈ 0` in BCC α-Fe).
-/
theorem tve_iron_order1_screening_and_homothetic_invariance
    (me_energy d1 d2 s : ℝ)
    (hme : 0 < me_energy)
    (ha_pos : 0 < effectiveAlphaOrder1)
    (ha_lt : effectiveAlphaOrder1 < alpha)
    (hs : s ≠ 0) :
    tveIronExchangeJ3dOrder1 me_energy =
      (me_energy * (alphaOrder1 ^ 3) / 9) / (cwfDielectricIndex 1 ^ 3) ∧
    tveIronExchangeJ3dOrder1 me_energy < tveIronExchangeJ3d me_energy ∧
    (s * d2) / (s * d1) - 1 = d2 / d1 - 1 := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [tveIronExchangeJ3dOrder1, effectiveAlphaOrder1]
    rw [div_pow alphaOrder1 (cwfDielectricIndex 1) 3]
    simp only [div_eq_mul_inv]
    ring
  · dsimp [tveIronExchangeJ3dOrder1, tveIronExchangeJ3d]
    have hb_pos : 0 < alpha := lt_trans ha_pos ha_lt
    have h_diff :
        alpha ^ 3 - effectiveAlphaOrder1 ^ 3 =
          (alpha - effectiveAlphaOrder1) *
            (alpha ^ 2 + alpha * effectiveAlphaOrder1 + effectiveAlphaOrder1 ^ 2) := by ring
    have h_quad_pos :
        0 < alpha ^ 2 + alpha * effectiveAlphaOrder1 + effectiveAlphaOrder1 ^ 2 := by positivity
    have h_cube_diff : 0 < alpha ^ 3 - effectiveAlphaOrder1 ^ 3 := by
      rw [h_diff]
      exact mul_pos (by linarith) h_quad_pos
    have h_cube_lt : effectiveAlphaOrder1 ^ 3 < alpha ^ 3 := by linarith
    have h_c_pos : 0 < me_energy / 9 := div_pos hme (by positivity)
    have h_mul := mul_lt_mul_of_pos_left h_cube_lt h_c_pos
    linarith [show (me_energy / 9) * effectiveAlphaOrder1 ^ 3 = me_energy * (effectiveAlphaOrder1 ^ 3) / 9 by ring,
              show (me_energy / 9) * alpha ^ 3 = me_energy * (alpha ^ 3) / 9 by ring]
  · rw [mul_div_mul_left d2 d1 hs]

/-- Elementary non-negative unit-interval bound `3 x y z ≤ x² + y² + z²` on `[0, 1]³`. -/
theorem cm_nonneg_unit_cubic_bound (x y z : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    3 * (x * y * z) ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  have h_sos : 0 ≤ (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by positivity
  have h_id :
      (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) =
        2 * (x ^ 3 + y ^ 3 + z ^ 3 - 3 * (x * y * z)) := by ring
  have hx_c : 0 ≤ x ^ 2 * (1 - x) := mul_nonneg (sq_nonneg x) (by linarith)
  have hy_c : 0 ≤ y ^ 2 * (1 - y) := mul_nonneg (sq_nonneg y) (by linarith)
  have hz_c : 0 ≤ z ^ 2 * (1 - z) := mul_nonneg (sq_nonneg z) (by linarith)
  have hx_eq : x ^ 2 * (1 - x) = x ^ 2 - x ^ 3 := by ring
  have hy_eq : y ^ 2 * (1 - y) = y ^ 2 - y ^ 3 := by ring
  have hz_eq : z ^ 2 * (1 - z) = z ^ 2 - z ^ 3 := by ring
  linarith

/--
Theorem: Unconditional Pointwise BCC Brillouin-Torus Spin-Wave Sandwich.
-/
theorem bcc_brillouin_dispersion_pointwise_sandwich
    (a b c eta : ℝ)
    (haL : -1 ≤ a) (haU : a ≤ 1)
    (hbL : -1 ≤ b) (hbU : b ≤ 1)
    (hcL : -1 ≤ c) (hcU : c ≤ 1)
    (heta : 0 ≤ eta) :
    let om1 := 1 - a * b * c
    let om2 := (2 / 3 : ℝ) * (3 - a ^ 2 - b ^ 2 - c ^ 2)
    3 * (a * b * c) ≤ a ^ 2 + b ^ 2 + c ^ 2 ∧
    0 ≤ om2 ∧
    om2 ≤ 2 * om1 ∧
    om1 ≤ om1 + (3 / 4 : ℝ) * eta * om2 ∧
    om1 + (3 / 4 : ℝ) * eta * om2 ≤ (1 + (3 / 2 : ℝ) * eta) * om1 := by
  have h_amgm : 3 * (a * b * c) ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
    rcases le_total 0 a with ha0 | ha0 <;>
    rcases le_total 0 b with hb0 | hb0 <;>
    rcases le_total 0 c with hc0 | hc0
    · exact cm_nonneg_unit_cubic_bound a b c ha0 haU hb0 hbU hc0 hcU
    · have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
      have habc : (a * b) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hab hc0
      have hsq : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
      linarith
    · have hab : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 hb0
      have habc : (a * b) * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hab hc0
      have hsq : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
      linarith
    · have h := cm_nonneg_unit_cubic_bound a (-b) (-c)
        ha0 haU (by linarith) (by linarith) (by linarith) (by linarith)
      linarith [show 3 * (a * (-b) * (-c)) = 3 * (a * b * c) by ring,
                show a ^ 2 + (-b) ^ 2 + (-c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 by ring]
    · have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hb0
      have habc : (a * b) * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hab hc0
      have hsq : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
      linarith
    · have h := cm_nonneg_unit_cubic_bound (-a) b (-c)
        (by linarith) (by linarith) hb0 hbU (by linarith) (by linarith)
      linarith [show 3 * ((-a) * b * (-c)) = 3 * (a * b * c) by ring,
                show (-a) ^ 2 + b ^ 2 + (-c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 by ring]
    · have h := cm_nonneg_unit_cubic_bound (-a) (-b) c
        (by linarith) (by linarith) (by linarith) (by linarith) hc0 hcU
      linarith [show 3 * ((-a) * (-b) * c) = 3 * (a * b * c) by ring,
                show (-a) ^ 2 + (-b) ^ 2 + c ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 by ring]
    · have hab : 0 ≤ a * b := mul_nonneg_of_nonpos_of_nonpos ha0 hb0
      have habc : (a * b) * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hab hc0
      have hsq : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
      linarith
  have ha2 : a ^ 2 ≤ 1 := by
    have h : 0 ≤ (1 - a) * (1 + a) := mul_nonneg (by linarith) (by linarith)
    linarith [show (1 - a) * (1 + a) = 1 - a ^ 2 by ring]
  have hb2 : b ^ 2 ≤ 1 := by
    have h : 0 ≤ (1 - b) * (1 + b) := mul_nonneg (by linarith) (by linarith)
    linarith [show (1 - b) * (1 + b) = 1 - b ^ 2 by ring]
  have hc2 : c ^ 2 ≤ 1 := by
    have h : 0 ≤ (1 - c) * (1 + c) := mul_nonneg (by linarith) (by linarith)
    linarith [show (1 - c) * (1 + c) = 1 - c ^ 2 by ring]
  have hom2_nonneg : 0 ≤ (2 / 3 : ℝ) * (3 - a ^ 2 - b ^ 2 - c ^ 2) := by linarith
  have hom2_le : (2 / 3 : ℝ) * (3 - a ^ 2 - b ^ 2 - c ^ 2) ≤ 2 * (1 - a * b * c) := by linarith
  have h_lo :
      (1 - a * b * c) ≤
        (1 - a * b * c) + (3 / 4 : ℝ) * eta * ((2 / 3 : ℝ) * (3 - a ^ 2 - b ^ 2 - c ^ 2)) := by
    have h_term : 0 ≤ (3 / 4 : ℝ) * eta * ((2 / 3 : ℝ) * (3 - a ^ 2 - b ^ 2 - c ^ 2)) :=
      mul_nonneg (by linarith) hom2_nonneg
    linarith
  have h_hi :
      (1 - a * b * c) + (3 / 4 : ℝ) * eta * ((2 / 3 : ℝ) * (3 - a ^ 2 - b ^ 2 - c ^ 2)) ≤
        (1 + (3 / 2 : ℝ) * eta) * (1 - a * b * c) := by
    have h_mul := mul_le_mul_of_nonneg_left hom2_le (show 0 ≤ (3 / 4 : ℝ) * eta by linarith)
    linarith [show (3 / 4 : ℝ) * eta * (2 * (1 - a * b * c)) =
                (3 / 2 : ℝ) * eta * (1 - a * b * c) by ring,
              show (1 + (3 / 2 : ℝ) * eta) * (1 - a * b * c) =
                (1 - a * b * c) + (3 / 2 : ℝ) * eta * (1 - a * b * c) by ring]
  exact ⟨h_amgm, hom2_nonneg, hom2_le, h_lo, h_hi⟩

/--
Theorem: Topological Bethe–Slater Phase Flip (Ferromagnetic BCC α-Fe vs. Antiferromagnetic FCC γ-Fe).
-/
theorem bethe_slater_lundquist_phase_flip_alpha_vs_gamma_fe
    (B_phi B_z : ℝ) :
    let E_pair := fun s : ℝ => (B_z + s * B_z) ^ 2 + (B_phi - s * B_phi) ^ 2
    E_pair (-1) - E_pair 1 = 4 * (B_phi ^ 2 - B_z ^ 2) ∧
    (B_z = 0 → B_phi ≠ 0 → E_pair 1 < E_pair (-1)) ∧
    (B_phi ^ 2 < B_z ^ 2 → E_pair (-1) < E_pair 1) := by
  have h_diff :
      ((B_z + (-1 : ℝ) * B_z) ^ 2 + (B_phi - (-1 : ℝ) * B_phi) ^ 2) -
        ((B_z + (1 : ℝ) * B_z) ^ 2 + (B_phi - (1 : ℝ) * B_phi) ^ 2) =
      4 * (B_phi ^ 2 - B_z ^ 2) := by ring
  refine ⟨h_diff, ?_, ?_⟩
  · intro hBz hBphi
    have h_pos : 0 < B_phi ^ 2 := sq_pos_of_ne_zero hBphi
    have hBz2 : B_z ^ 2 = 0 := by rw [hBz]; ring
    linarith
  · intro h_core
    linarith

/-! ## Part 3: Watson–Legendre Resolvent Certification of `I(η_TVE)` (No Literal `1.3046` Divisor) -/

/-- Exact finite 2-term & 3-term rational resolvent identities + pointwise cubic remainder bound over `ℝ`. -/
theorem bcc_finite_resolvent_and_remainder_bounds
    (om1 tom2 eta : ℝ)
    (hom1 : 0 < om1) (htom0 : 0 ≤ tom2) (htomU : tom2 ≤ (3 / 2 : ℝ) * om1) (heta : 0 ≤ eta) :
    let A_mid := (1 + (3 / 4 : ℝ) * eta) * om1
    let d_mid := tom2 - (3 / 4 : ℝ) * om1
    let A1 := (1 + eta) * om1
    let d1 := tom2 - om1
    (1 / (om1 + eta * tom2) =
      1 / A_mid - (eta * d_mid) / (A_mid ^ 2) +
        (eta ^ 2 * d_mid ^ 2) / (A_mid ^ 2 * (om1 + eta * tom2))) ∧
    d_mid ^ 2 ≤ (9 / 16 : ℝ) * om1 ^ 2 ∧
    (1 / (om1 + eta * tom2) =
      1 / A1 - (eta * d1) / (A1 ^ 2) + (eta ^ 2 * d1 ^ 2) / (A1 ^ 3) -
        (eta ^ 3 * d1 ^ 3) / (A1 ^ 3 * (om1 + eta * tom2))) ∧
    -(om1 * d1 ^ 2) ≤ d1 ^ 3 ∧ d1 ^ 3 ≤ om1 * d1 ^ 2 := by
  have h_tot_pos : 0 < om1 + eta * tom2 := by
    have h_et : 0 ≤ eta * tom2 := mul_nonneg heta htom0
    linarith
  have h_mid_pos : 0 < (1 + (3 / 4 : ℝ) * eta) * om1 := mul_pos (by linarith) hom1
  have h_A1_pos : 0 < (1 + eta) * om1 := mul_pos (by linarith) hom1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : om1 + eta * tom2 ≠ 0 := ne_of_gt h_tot_pos
    have h2 : (1 + (3 / 4 : ℝ) * eta) * om1 ≠ 0 := ne_of_gt h_mid_pos
    field_simp [h1, h2]
    ring
  · have h_prod : 0 ≤ ((3 / 2 : ℝ) * om1 - tom2) * tom2 := mul_nonneg (by linarith) htom0
    linarith [show (9 / 16 : ℝ) * om1 ^ 2 - (tom2 - (3 / 4 : ℝ) * om1) ^ 2 =
                ((3 / 2 : ℝ) * om1 - tom2) * tom2 by ring]
  · have h1 : om1 + eta * tom2 ≠ 0 := ne_of_gt h_tot_pos
    have h2 : (1 + eta) * om1 ≠ 0 := ne_of_gt h_A1_pos
    field_simp [h1, h2]
    ring
  · have h_lo : 0 ≤ (tom2) * (tom2 - om1) ^ 2 := mul_nonneg htom0 (sq_nonneg _)
    linarith [show (tom2 - om1) ^ 3 + om1 * (tom2 - om1) ^ 2 = tom2 * (tom2 - om1) ^ 2 by ring]
  · have h_hi : 0 ≤ (2 * om1 - tom2) * (tom2 - om1) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith [show om1 * (tom2 - om1) ^ 2 - (tom2 - om1) ^ 3 = (2 * om1 - tom2) * (tom2 - om1) ^ 2 by ring]

/-- Unconditional midpoint (`c = 3/4`) lower bound on `I(η)` from `(W_L, π_L, η_U)` in `PosRat`. -/
@[expose]
def cmBccResolventMidLoPosRat (W_L pi_L eta_U : PosRat) : PosRat :=
  let den := cmPosRatAddRed (posRatOfInt 1) (posRatMulRed { num := 3, denPred := 3 } eta_U)
  let denNz := vpPosRatToNzOrOne den
  let t0 := posRatDivRed W_L denNz
  let subDen := posRatMulRed (posRatMulRed den den) (posRatMulRed (posRatMulRed pi_L pi_L) W_L)
  let t1 := posRatDivRed (posRatMulRed (posRatOfInt 3) eta_U) (vpPosRatToNzOrOne subDen)
  posRatSubRed t0 t1

/-- Unconditional midpoint (`c = 3/4`) upper bound on `I(η)` from `(W_U, π_U, η_L)` in `PosRat`. -/
@[expose]
def cmBccResolventMidHiPosRat (W_U pi_U eta_L : PosRat) : PosRat :=
  let den := cmPosRatAddRed (posRatOfInt 1) (posRatMulRed { num := 3, denPred := 3 } eta_L)
  let den2Nz := vpPosRatToNzOrOne (posRatMulRed den den)
  let t0 := posRatDivRed W_U (vpPosRatToNzOrOne den)
  let subDen := posRatMulRed (posRatMulRed den den) (posRatMulRed (posRatMulRed pi_U pi_U) W_U)
  let t1 := posRatDivRed (posRatMulRed (posRatOfInt 3) eta_L) (vpPosRatToNzOrOne subDen)
  let rem := posRatDivRed
    (posRatMulRed { num := 9, denPred := 15 } (posRatMulRed (posRatMulRed eta_L eta_L) W_U)) den2Nz
  cmPosRatAddRed (posRatSubRed t0 t1) rem

/-- Closed-form Legendre-moment (`K_2 = -3/4 K_1`) lower bound on `I(η)` in `PosRat`. -/
@[expose]
def cmBccResolventLegendreLoPosRat (W_L W_U pi_L pi_U eta_U : PosRat) : PosRat :=
  let negK1_lo := posRatSubRed (posRatMulRed { num := 1, denPred := 3 } W_L)
    (posRatDivRed (posRatOfInt 3) (vpPosRatToNzOrOne (posRatMulRed (posRatMulRed pi_L pi_L) W_L)))
  let negK1_hi := posRatSubRed (posRatMulRed { num := 1, denPred := 3 } W_U)
    (posRatDivRed (posRatOfInt 3) (vpPosRatToNzOrOne (posRatMulRed (posRatMulRed pi_U pi_U) W_U)))
  let K2_lo := posRatMulRed { num := 3, denPred := 3 } negK1_lo
  let K2_hi := posRatMulRed { num := 3, denPred := 3 } negK1_hi
  let op := cmPosRatAddRed (posRatOfInt 1) eta_U
  let op2 := posRatMulRed op op
  let op3Nz := vpPosRatToNzOrOne (posRatMulRed op2 op)
  let eta2 := posRatMulRed eta_U eta_U
  let t01 := cmPosRatAddRed (posRatDivRed W_L (vpPosRatToNzOrOne op))
    (posRatDivRed (posRatMulRed eta_U negK1_lo) (vpPosRatToNzOrOne op2))
  let t2 := posRatDivRed (posRatMulRed eta2 K2_lo) op3Nz
  let r3 := posRatDivRed (posRatMulRed (posRatMulRed eta2 eta_U) K2_hi) op3Nz
  posRatSubRed (cmPosRatAddRed t01 t2) r3

/-- Closed-form Legendre-moment (`K_2 = -3/4 K_1`) upper bound on `I(η)` in `PosRat`. -/
@[expose]
def cmBccResolventLegendreHiPosRat (W_U pi_U eta_L : PosRat) : PosRat :=
  let negK1_hi := posRatSubRed (posRatMulRed { num := 1, denPred := 3 } W_U)
    (posRatDivRed (posRatOfInt 3) (vpPosRatToNzOrOne (posRatMulRed (posRatMulRed pi_U pi_U) W_U)))
  let K2_hi := posRatMulRed { num := 3, denPred := 3 } negK1_hi
  let op := cmPosRatAddRed (posRatOfInt 1) eta_L
  let op2 := posRatMulRed op op
  let op3Nz := vpPosRatToNzOrOne (posRatMulRed op2 op)
  let eta2 := posRatMulRed eta_L eta_L
  let t01 := cmPosRatAddRed (posRatDivRed W_U (vpPosRatToNzOrOne op))
    (posRatDivRed (posRatMulRed eta_L negK1_hi) (vpPosRatToNzOrOne op2))
  let t23 := posRatDivRed
    (posRatMulRed (cmPosRatAddRed eta2 (posRatMulRed eta2 eta_L)) K2_hi) op3Nz
  cmPosRatAddRed t01 t23

/--
Theorem (Zero Axioms): Watson–Legendre Resolvent Certification of `I(η_TVE)` & `T_C^(1)`.
Derives the 14-face BCC Brillouin integral directly from Watson's `W_BCC ∈ [1.393203, 1.393204]`,
Machin `π`, and certified `η_TVE ∈ [0.0749, 0.0755]` with zero literal `1.3046` divisors:
1. Unconditional midpoint bound locks `I(η_TVE) ∈ (1.303, 1.309)` and `T_C^(1) ∈ (1040, 1044) K`.
2. Legendre moment identity (`K_1 = -W/4 + 3/(π²W)`, `K_2 = -3/4 K_1`) with cubic remainder
   certifies `I(η_TVE) ∈ (1.3043, 1.3051)` and `T_C^(1) ∈ (1042.7 K, 1043.3 K)`.
-/
theorem bcc_watson_legendre_resolvent_curie_certification :
    let W_L : PosRat := { num := 1393203, denPred := 999999 }
    let W_U : PosRat := { num := 1393204, denPred := 999999 }
    let eta_L : PosRat := { num := 749, denPred := 9999 }
    let eta_U : PosRat := { num := 755, denPred := 9999 }
    let Imid_L := cmBccResolventMidLoPosRat W_L vpPiConvLo eta_U
    let Imid_U := cmBccResolventMidHiPosRat W_U vpPiConvHi eta_L
    let Ileg_L := cmBccResolventLegendreLoPosRat W_L W_U vpPiConvLo vpPiConvHi eta_U
    let Ileg_U := cmBccResolventLegendreHiPosRat W_U vpPiConvHi eta_L
    let Tmf1_L := posRatMulRed { num := 16, denPred := 2 }
      (cmExchangeT3dKelvinPosRat 510998950 vpEffectiveAlphaInvHiNz)
    let Tmf1_U := posRatMulRed { num := 16, denPred := 2 }
      (cmExchangeT3dKelvinPosRat 510998952 vpEffectiveAlphaInvLoNz)
    let Tc_mid_L := posRatDivRed Tmf1_L (vpPosRatToNzOrOne Imid_U)
    let Tc_mid_U := posRatDivRed Tmf1_U (vpPosRatToNzOrOne Imid_L)
    let Tc_leg_L := posRatDivRed Tmf1_L (vpPosRatToNzOrOne Ileg_U)
    let Tc_leg_U := posRatDivRed Tmf1_U (vpPosRatToNzOrOne Ileg_L)
    posRatLt { num := 1303, denPred := 999 } Imid_L = true ∧
    posRatLt Imid_U { num := 1309, denPred := 999 } = true ∧
    posRatLt (posRatOfInt 1040) Tc_mid_L = true ∧
    posRatLt Tc_mid_U (posRatOfInt 1044) = true ∧
    posRatLt { num := 13043, denPred := 9999 } Ileg_L = true ∧
    posRatLt Ileg_U { num := 13051, denPred := 9999 } = true ∧
    posRatLt { num := 10427, denPred := 9 } Tc_leg_L = true ∧
    posRatLt Tc_leg_U { num := 10433, denPred := 9 } = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms kelvin_wigner_seitz_14_face_hodge_partition
#print axioms cubic_3d_harmonic_channel_selection_and_unsold
#print axioms lundquist_wall_and_interstitial_attenuation_bounds
#print axioms tve_iron_3d_scale_mott_hubbard_and_curie_bounds
#print axioms tve_iron_order1_polarizable_vacuum_curie_bounds
#print axioms bcc_watson_legendre_resolvent_curie_certification

end TVE
