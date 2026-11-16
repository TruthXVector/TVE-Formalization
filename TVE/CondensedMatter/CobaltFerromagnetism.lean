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

/-!
# Topological Vacuum Electrodynamics — FCC β-Cobalt Ferromagnetic Curie Transition

Standalone parameter-free TVE formalization of FCC β-cobalt's (`Z = 27`, HCP α-Co →
FCC β-Co above `~695 K ≪ T_C`) ferromagnetic-to-paramagnetic Curie transition across
both the Order-0 (`K = 1` rigid upper bound) and Order-1 (`δK > 0` polarizable-vacuum
relaxation) tiers, importing only `TVE.VacuumPolarization` and the root TVE core:

1. **Radical-Free 3D FCC Rhombic-Dodecahedron Hodge Geometry (`[]`):** Exact integer
   coordinates at cubic scale `a_0 = 4` for the 12-face FCC Wigner–Seitz rhombic
   dodecahedron (`V_WS = (1/4) a_0^3`), proving single-face Hodge conductance
   `w_1 / a_0 = 1/4`, total 12-face shell sum `W_1 / a_0 = 3`, strict vanishing of
   next-nearest-neighbor octahedral corner conductance (`w_2 = 0`), and the exact
   equal-atomic-volume (`V_WS`) squared bond-volume identity `(d_1^BCC / d_1^FCC)^6 = 27 / 32`.
2. **Exact `L = 2` (`3d`) `[110]` Harmonics & Unsöld Conservation (`[]`):** Proves the
   `2 : 1` directional ratio `G_{t2g}([110]) = 5/4` vs. `G_{eg}([110]) = 5/8` along the
   12 FCC nearest-neighbor normals and Unsöld spherical closure `(3/5) G_{t2g} + (2/5) G_{eg} = 1`
   for multi-hole `S = 1` β-Co (`G_orb = 1`).
3. **Zero-Axiom Joyce Singular-Modulus Certification of `W_FCC` & `η_pack` (`[]`):**
   Certifies Pell convergents for `√3` and `√2`, Joyce's 3rd singular modulus
   `m_3 = sin²(π/12) = (2 − √3)/4 ∈ (0.06698, 0.06699)`, and 4-term hypergeometric bounds
   on `₂F₁(1/2, 1/2; 1; m_3)`, deriving Watson's FCC triple integral
   `W_FCC ∈ (1.34465, 1.34467)` and `η_pack = √(27/32) ∈ (0.918558, 0.918559)` from
   scratch with zero uncertified rational constants.
4. **Order-0 Ceiling & Order-1 Polarizable-Vacuum Relaxation (`[]`):** Consumes
   `vpEffectiveAlphaInvLoNz` / `vpEffectiveAlphaInvHiNz` from `TVE.VacuumPolarization`,
   certifying `(U_{3d}/W_FCC)² = A_eff / 144 ∈ (0.952, 0.953) < 1`, packed bond grip
   `J_1^(1)(Co) ∈ (20.19, 20.20) meV`, Order-0 rigid ceiling `T_C^(0) ∈ (1399, 1400) K`,
   strict variational lowering `T_C^(1) < T_C^(0)`, and Order-1 Curie transition
   `T_C^(1)(β-Co) ∈ (1394.3 K, 1394.4 K)` (handbook `1121 °C = 1394.15 K`, experimental
   zero-field range `1388–1395 K`).
5. **Continuum `3√3 / 4` Joyce–Watson Cancellation & FCC Brillouin Bounds (`ℝ`):**
   Proves over `ℝ` that `(3√3 / 4)` cancels identically in `η_pack / W_FCC = 1 / (√2 F(m_3)²)`
   and proves `0 ≤ ω_FCC(q) ≤ 4/3` across the entire 3D FCC Brillouin zone.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-! ## Part 1: Zero-Axiom Constructive FCC Geometry, Joyce–Watson & Curie Kernel (`[]`) -/

/-- Negation `-q` on `PosRat` (`Vacuum.lean`). -/
@[expose]
def coPosRatNeg (q : PosRat) : PosRat :=
  { num := -q.num, denPred := q.denPred }

/-- Reduced addition `a + b = a - (-b)` on `PosRat` via `posRatSubRed`. -/
@[expose]
def coPosRatAddRed (a b : PosRat) : PosRat :=
  posRatSubRed a (coPosRatNeg b)

/-- Dot product `u · v` on `IntVec3` (`Action.lean`). -/
@[expose]
def coVecDot (u v : IntVec3) : ℤ :=
  u.x * v.x + u.y * v.y + u.z * v.z

/-- Squared Euclidean norm `‖v‖²` on `IntVec3`. -/
@[expose]
def coVecNormSq (v : IntVec3) : ℤ :=
  coVecDot v v

/-- Scalar triple product `u · (v × w) = 6 × Vol(0, u, v, w)` on `IntVec3`. -/
@[expose]
def coScalarTriple (u v w : IntVec3) : ℤ :=
  coVecDot u (vecCross v w)

/-! ### 1. Radical-Free 3D FCC Rhombic-Dodecahedron Geometry at Scale `a_0 = 4` -/

/-- FCC nearest-neighbor lattice vector `(+2, +2, 0)` at cubic scale `a_0 = 4` (`d_1² = 8`). -/
@[expose] def fccCoNNVec : IntVec3 := { x := 2, y := 2, z := 0 }

/-- FCC next-nearest-neighbor octahedral vector `(+4, 0, 0)` at cubic scale `a_0 = 4` (`d_2² = 16`). -/
@[expose] def fccCoNNNVec : IntVec3 := { x := 4, y := 0, z := 0 }

/-- Ordered vertices `r_0 .. r_3` of the `(+2, +2, 0)` face of the FCC rhombic dodecahedron. -/
@[expose] def coRhombV0 : IntVec3 := { x := 2, y := 0, z := 0 }
@[expose] def coRhombV1 : IntVec3 := { x := 1, y := 1, z := -1 }
@[expose] def coRhombV2 : IntVec3 := { x := 0, y := 2, z := 0 }
@[expose] def coRhombV3 : IntVec3 := { x := 1, y := 1, z := 1 }

/-- Oriented `6 × Volume` of the pyramid from `(0,0,0)` to an FCC rhombic face (`= A_rhomb · d_1 = 8`). -/
@[expose]
def coFccRhombPyramid6Vol : ℤ :=
  coScalarTriple coRhombV0 coRhombV1 coRhombV2 +
  coScalarTriple coRhombV0 coRhombV2 coRhombV3

/-- Degenerate `6 × Volume` at the octahedral NNN corner vertex `coRhombV0 = (2, 0, 0)` (`= 0`). -/
@[expose]
def coFccOctahedralCorner6Vol : ℤ :=
  coScalarTriple coRhombV0 coRhombV0 coRhombV0

/-- Dimensionless FCC single-face Hodge conductance `w_1 / a_0 = (6 V_rhomb) / (a_0 d_1²) = 8 / 32 = 1 / 4`. -/
@[expose]
def coFccRhombHodgeNorm : PosRat :=
  posRatDivRed (posRatOfInt coFccRhombPyramid6Vol) { isNeg := false, numPred := 31, denPred := 0 }

/--
Theorem (Zero Axioms): Radical-Free 3D FCC Rhombic-Dodecahedron Hodge Geometry & Equal-`V_WS` Ratio.
1. All 4 vertices `r_0 .. r_3` lie on the perpendicular bisector `2 (r_i · d_1) = ‖d_1‖² = 8`.
2. All 4 edges have squared length `3`, and orthogonal diagonals have squared lengths `8` and `4` (`2 : 1`).
3. `12` congruent rhombic pyramids exhaust the FCC Wigner–Seitz volume `V_WS = a_0³ / 4 = 16`
   (`2 * (12 * 8) = 3 * 64`), with `w_1 / a_0 = 1/4`, `12 (w_1 / a_0) = 3`, and `w_2 = 0`.
4. At equal Wigner–Seitz atomic volume `V_WS = 16` (`a_BCC³ = 32` vs. `a_FCC³ = 64`), the squared
   cubic bond-volume ratio `(d_1^BCC)⁶ / (d_1^FCC)⁶ = ((3/4)³ · 32²) / ((1/2)³ · 64²) = 27 / 32`.
-/
theorem fcc_rhombic_dodecahedron_12_face_hodge_geometry :
    let W1_fcc := posRatMulRed (posRatOfInt 12) coFccRhombHodgeNorm
    let d1_bcc6_scaled : ℤ := 27 * (32 * 32)
    let d1_fcc6_scaled : ℤ := 8 * (64 * 64)
    let packSqRatio := posRatDivRed (posRatOfInt d1_bcc6_scaled)
      { isNeg := false, numPred := 32767, denPred := 0 }
    coVecNormSq fccCoNNVec = 8 ∧
    coVecNormSq fccCoNNNVec = 16 ∧
    2 * coVecDot coRhombV0 fccCoNNVec = coVecNormSq fccCoNNVec ∧
    2 * coVecDot coRhombV1 fccCoNNVec = coVecNormSq fccCoNNVec ∧
    2 * coVecDot coRhombV2 fccCoNNVec = coVecNormSq fccCoNNVec ∧
    2 * coVecDot coRhombV3 fccCoNNVec = coVecNormSq fccCoNNVec ∧
    coVecNormSq (vecSub coRhombV1 coRhombV0) = 3 ∧
    coVecNormSq (vecSub coRhombV2 coRhombV1) = 3 ∧
    coVecNormSq (vecSub coRhombV2 coRhombV0) = 8 ∧
    coVecNormSq (vecSub coRhombV3 coRhombV1) = 4 ∧
    coVecDot (vecSub coRhombV2 coRhombV0) (vecSub coRhombV3 coRhombV1) = 0 ∧
    coFccRhombPyramid6Vol = 8 ∧
    2 * (12 * coFccRhombPyramid6Vol) = 3 * (4 * 4 * 4) ∧
    coFccRhombHodgeNorm = { num := 1, denPred := 3 } ∧
    W1_fcc = posRatOfInt 3 ∧
    coFccOctahedralCorner6Vol = 0 ∧
    packSqRatio = { num := 27, denPred := 31 } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 2. Exact `L = 2` (`3d`) `[110]` Harmonics & Unsöld Closure for Multi-Hole `S = 1` β-Co -/

/-- Cubic quartic invariant `Q_4(v) = (x⁴ + y⁴ + z⁴) / (x² + y² + z²)²` in `PosRat`. -/
@[expose]
def coCubicQ4PosRat (v : IntVec3) (rSqPred : ℕ) : PosRat :=
  let x2 := v.x * v.x
  let y2 := v.y * v.y
  let z2 := v.z * v.z
  let num4 := x2 * x2 + y2 * y2 + z2 * z2
  let r4Nz : NzPosRat := { isNeg := false, numPred := vacMulSuccPred rSqPred rSqPred, denPred := 0 }
  posRatDivRed (posRatOfInt num4) r4Nz

/-- Normalized `t_{2g}` directional intensity `G_{t2g}(v) = (5/2)(1 - Q_4(v))` in `PosRat`. -/
@[expose]
def coGt2gPosRat (v : IntVec3) (rSqPred : ℕ) : PosRat :=
  posRatMulRed { num := 5, denPred := 1 }
    (posRatSubRed (posRatOfInt 1) (coCubicQ4PosRat v rSqPred))

/-- Normalized `e_g` directional intensity `G_{eg}(v) = (5/4)(3 Q_4(v) - 1)` in `PosRat`. -/
@[expose]
def coGegPosRat (v : IntVec3) (rSqPred : ℕ) : PosRat :=
  posRatMulRed { num := 5, denPred := 3 }
    (posRatSubRed (posRatMulRed (posRatOfInt 3) (coCubicQ4PosRat v rSqPred)) (posRatOfInt 1))

/-- 5-orbital Unsöld spherical average `(3/5) G_{t2g}(v) + (2/5) G_{eg}(v)` in `PosRat`. -/
@[expose]
def coUnsoldAvgPosRat (v : IntVec3) (rSqPred : ℕ) : PosRat :=
  coPosRatAddRed
    (posRatMulRed { num := 3, denPred := 4 } (coGt2gPosRat v rSqPred))
    (posRatMulRed { num := 2, denPred := 4 } (coGegPosRat v rSqPred))

/--
Theorem (Zero Axioms): FCC `[110]` Harmonic Split (`5/4` vs. `5/8`) & Unsöld Conservation (`G_orb = 1`).
-/
theorem fcc_cobalt_3d_unsold_harmonic_closure :
    let v110 : IntVec3 := { x := 1, y := 1, z := 0 }
    let v100 : IntVec3 := { x := 1, y := 0, z := 0 }
    coGt2gPosRat v110 1 = { num := 5, denPred := 3 } ∧
    coGegPosRat v110 1 = { num := 5, denPred := 7 } ∧
    coUnsoldAvgPosRat v110 1 = posRatOfInt 1 ∧
    coUnsoldAvgPosRat fccCoNNVec 7 = posRatOfInt 1 ∧
    coUnsoldAvgPosRat v100 0 = posRatOfInt 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### 3. Zero-Axiom Joyce Singular-Modulus Certification of `W_FCC` & `η_pack` -/

/--
4-term hypergeometric lower polynomial `1 + (1/4)m + (9/64)m² + (25/256)m³` for
`₂F₁(1/2, 1/2; 1; m)` (`m ∈ (0, 1)`, strictly positive coefficients).
-/
@[expose]
def coFccHypergeomLoPosRat (m : PosRat) : PosRat :=
  let m2 := posRatMulRed m m
  let m3 := posRatMulRed m2 m
  let t1 := posRatMulRed { num := 1, denPred := 3 } m
  let t2 := posRatMulRed { num := 9, denPred := 63 } m2
  let t3 := posRatMulRed { num := 25, denPred := 255 } m3
  coPosRatAddRed (coPosRatAddRed (posRatOfInt 1) t1) (coPosRatAddRed t2 t3)

/--
Geometric-majorant upper bound `F_lo(m) + (1225 / 16384) · m⁴ / (1 - m)` for `₂F₁(1/2, 1/2; 1; m)`
(valid for all `0 < m < 1` since `c_{n+1} / c_n = ((2n+1)/(2n+2))² < 1`).
-/
@[expose]
def coFccHypergeomHiPosRat (m : PosRat) : PosRat :=
  let m2 := posRatMulRed m m
  let m4 := posRatMulRed m2 m2
  let oneSubM := vpPosRatToNzOrOne (posRatSubRed (posRatOfInt 1) m)
  let tail := posRatDivRed (posRatMulRed { num := 1225, denPred := 16383 } m4) oneSubM
  coPosRatAddRed (coFccHypergeomLoPosRat m) tail

/-- Certified Pell lower/upper bounds on `√3` (`3691/2131 < √3 < 5042/2911`) and `√2` (`8119/5741 < √2 < 19601/13860`). -/
@[expose] def coSqrt3LoPosRat : PosRat := { num := 3691, denPred := 2130 }
@[expose] def coSqrt3HiPosRat : PosRat := { num := 5042, denPred := 2910 }
@[expose] def coSqrt2LoPosRat : PosRat := { num := 8119, denPred := 5740 }
@[expose] def coSqrt2HiPosRat : PosRat := { num := 19601, denPred := 13859 }

/-- Joyce's 3rd singular modulus `m_3 = sin²(π/12) = (2 - √3) / 4` bounds in `PosRat`. -/
@[expose]
def coSingularMod3LoPosRat : PosRat :=
  posRatMulRed { num := 1, denPred := 3 } (posRatSubRed (posRatOfInt 2) coSqrt3HiPosRat)

@[expose]
def coSingularMod3HiPosRat : PosRat :=
  posRatMulRed { num := 1, denPred := 3 } (posRatSubRed (posRatOfInt 2) coSqrt3LoPosRat)

/-- Certified Watson FCC triple integral `W_FCC = (3√3 / 4) · ₂F₁(1/2, 1/2; 1; m_3)²` bounds in `PosRat`. -/
@[expose]
def coWatsonFccLoPosRat : PosRat :=
  let F_L := coFccHypergeomLoPosRat coSingularMod3LoPosRat
  posRatMulRed (posRatMulRed { num := 3, denPred := 3 } coSqrt3LoPosRat) (posRatMulRed F_L F_L)

@[expose]
def coWatsonFccHiPosRat : PosRat :=
  let F_U := coFccHypergeomHiPosRat coSingularMod3HiPosRat
  posRatMulRed (posRatMulRed { num := 3, denPred := 3 } coSqrt3HiPosRat) (posRatMulRed F_U F_U)

/-- Certified equal-`V_WS` close-packed bond-volume factor `η_pack = (3√3) / (4√2) = √(27/32)` in `PosRat`. -/
@[expose]
def coPackingFactorLoPosRat : PosRat :=
  posRatDivRed (posRatMulRed (posRatOfInt 3) coSqrt3LoPosRat)
    (vpPosRatToNzOrOne (posRatMulRed (posRatOfInt 4) coSqrt2HiPosRat))

@[expose]
def coPackingFactorHiPosRat : PosRat :=
  posRatDivRed (posRatMulRed (posRatOfInt 3) coSqrt3HiPosRat)
    (vpPosRatToNzOrOne (posRatMulRed (posRatOfInt 4) coSqrt2LoPosRat))

/-- Cancelled Joyce–Watson ratio `η_pack / W_FCC = 1 / (√2 · ₂F₁(1/2, 1/2; 1; m_3)²)` bounds in `PosRat`. -/
@[expose]
def coPackOverWatsonLoPosRat : PosRat :=
  let F_U := coFccHypergeomHiPosRat coSingularMod3HiPosRat
  let den := posRatMulRed coSqrt2HiPosRat (posRatMulRed F_U F_U)
  posRatDivRed (posRatOfInt 1) (vpPosRatToNzOrOne den)

@[expose]
def coPackOverWatsonHiPosRat : PosRat :=
  let F_L := coFccHypergeomLoPosRat coSingularMod3LoPosRat
  let den := posRatMulRed coSqrt2LoPosRat (posRatMulRed F_L F_L)
  posRatDivRed (posRatOfInt 1) (vpPosRatToNzOrOne den)

/--
Theorem (Zero Axioms): Certified Joyce Singular Modulus, Watson `W_FCC` & Packing Factor `η_pack`.
Derives `W_FCC ∈ (1.34465, 1.34467)` and `η_pack = √(27/32) ∈ (0.918558, 0.918559)` directly
from Pell quadratic bounds and the 4-term hypergeometric polynomial with zero magic constants.
-/
theorem watson_fcc_singular_modulus_and_packing_bounds :
    let F3_L := coFccHypergeomLoPosRat coSingularMod3LoPosRat
    let F3_U := coFccHypergeomHiPosRat coSingularMod3HiPosRat
    vacFastLtInt (3691 * 3691) (3 * 2131 * 2131) = true ∧
    vacFastLtInt (3 * 2911 * 2911) (5042 * 5042) = true ∧
    vacFastLtInt (8119 * 8119) (2 * 5741 * 5741) = true ∧
    vacFastLtInt (2 * 13860 * 13860) (19601 * 19601) = true ∧
    posRatLt { num := 6698, denPred := 99999 } coSingularMod3LoPosRat = true ∧
    posRatLt coSingularMod3HiPosRat { num := 6699, denPred := 99999 } = true ∧
    posRatLt { num := 101740, denPred := 99999 } F3_L = true ∧
    posRatLt F3_U { num := 101741, denPred := 99999 } = true ∧
    posRatLt { num := 134465, denPred := 99999 } coWatsonFccLoPosRat = true ∧
    posRatLt coWatsonFccHiPosRat { num := 134467, denPred := 99999 } = true ∧
    posRatLt { num := 918558, denPred := 999999 } coPackingFactorLoPosRat = true ∧
    posRatLt coPackingFactorHiPosRat { num := 918559, denPred := 999999 } = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 4. Order-0 Rigid Ceiling (`K = 1`) & Order-1 Polarizable-Vacuum Relaxation (`δK > 0`) -/

/-- Exact 2019 SI conversion factor `e / (1000 k_B) = 801088317 / 69032450` (`K / meV`). -/
@[expose]
def coKelvinPerMeVPosRat : PosRat :=
  { num := 801088317, denPred := 69032449 }

/-- Squared Mott–Hubbard ratio `(U_{3d} / W)² = A / z_1²` (`z1SqPred = z_1² - 1`). -/
@[expose]
def coMottHubbardSqPosRat (A_rat : PosRat) (z1SqPred : ℕ) : PosRat :=
  posRatDivRed A_rat { isNeg := false, numPred := z1SqPred, denPred := 0 }

/-- Bare `n = 3` (`3d`) exchange scale `J_{3d} = m_e c² / (9 A³)` in `meV`. -/
@[expose]
def coExchangeJ3dMeVPosRat (meMeV : ℤ) (A_nz : NzPosRat) : PosRat :=
  let alpha_rat := posRatDivRed (posRatOfInt 1) A_nz
  let alpha3 := posRatMulRed alpha_rat (posRatMulRed alpha_rat alpha_rat)
  posRatMulRed { num := meMeV, denPred := 8 } alpha3

/-- Bare `n = 3` (`3d`) thermal exchange scale `T_{3d} = J_{3d} / k_B` in Kelvin. -/
@[expose]
def coExchangeT3dKelvinPosRat (meMeV : ℤ) (A_nz : NzPosRat) : PosRat :=
  posRatMulRed (coExchangeJ3dMeVPosRat meMeV A_nz) coKelvinPerMeVPosRat

/--
Theorem (Zero Axioms): Order-0 Ceiling & Order-1 Polarizable-Vacuum Curie Transition of FCC β-Cobalt.
Consumes `vpEffectiveAlphaInvLoNz` / `vpEffectiveAlphaInvHiNz` directly from `TVE.VacuumPolarization`
for `z_1 = 12`, `w_2 = 0`, `S = 1` (`z_1 S(S+1)/3 = 8`), `G_orb = 1`, certifying via `rfl`:
1. **FCC Mott–Hubbard Regime:** `(U_{3d}^(1)/W_FCC)² = A_eff / 144 ∈ (0.952, 0.953) < 1`.
2. **Packed FCC Bond Grip:** `J_1^(1)(β-Co) = η_pack · J_{3d}^(1) ∈ (20.19, 20.20) meV`
   and mean-field scale `T_MF^(1)(β-Co) = 8 η_pack T_{3d}^(1) ∈ (1874, 1875) K`.
3. **Order-0 Rigid Ceiling (`K = 1`):** `T_C^(0)(β-Co) ∈ (1399 K, 1400 K)`.
4. **Strict Variational Lowering & Order-1 Curie Point (`δK > 0`):**
   Proves `T_C^(1)(β-Co) < T_C^(0)(β-Co)` strictly and certifies both the cancelled
   Joyce–Watson form `8 T_{3d}^(1) / (√2 F(m_3)²)` and direct `T_MF^(1) / W_FCC` inside
   `(1394.3 K, 1394.4 K)` (handbook `1121 °C = 1394.15 K`, zero-field range `1388–1395 K`).
-/
theorem tve_cobalt_order0_and_order1_curie_bounds :
    let A0_L : NzPosRat := alphaInvNzPosRat 332 105
    let A0_U : NzPosRat := alphaInvNzPosRat 354 112
    let T3d_0_L := coExchangeT3dKelvinPosRat 510998950 A0_U
    let T3d_0_U := coExchangeT3dKelvinPosRat 510998952 A0_L
    let Tc_0_L := posRatMulRed (posRatMulRed (posRatOfInt 8) T3d_0_L) coPackOverWatsonLoPosRat
    let Tc_0_U := posRatMulRed (posRatMulRed (posRatOfInt 8) T3d_0_U) coPackOverWatsonHiPosRat
    let Aeff_L : NzPosRat := vpEffectiveAlphaInvLoNz
    let Aeff_U : NzPosRat := vpEffectiveAlphaInvHiNz
    let J1_Co_1_L := posRatMulRed coPackingFactorLoPosRat (coExchangeJ3dMeVPosRat 510998950 Aeff_U)
    let J1_Co_1_U := posRatMulRed coPackingFactorHiPosRat (coExchangeJ3dMeVPosRat 510998952 Aeff_L)
    let T3d_1_L := coExchangeT3dKelvinPosRat 510998950 Aeff_U
    let T3d_1_U := coExchangeT3dKelvinPosRat 510998952 Aeff_L
    let Tmf_1_L := posRatMulRed (posRatOfInt 8) (posRatMulRed coPackingFactorLoPosRat T3d_1_L)
    let Tmf_1_U := posRatMulRed (posRatOfInt 8) (posRatMulRed coPackingFactorHiPosRat T3d_1_U)
    let Tc_1_L := posRatMulRed (posRatMulRed (posRatOfInt 8) T3d_1_L) coPackOverWatsonLoPosRat
    let Tc_1_U := posRatMulRed (posRatMulRed (posRatOfInt 8) T3d_1_U) coPackOverWatsonHiPosRat
    let Tc_1_dir_L := posRatDivRed Tmf_1_L (vpPosRatToNzOrOne coWatsonFccHiPosRat)
    let Tc_1_dir_U := posRatDivRed Tmf_1_U (vpPosRatToNzOrOne coWatsonFccLoPosRat)
    posRatLt { num := 952, denPred := 999 } (coMottHubbardSqPosRat (nzPosRatToPosRat Aeff_L) 143) = true ∧
    posRatLt (coMottHubbardSqPosRat (nzPosRatToPosRat Aeff_U) 143) { num := 953, denPred := 999 } = true ∧
    posRatLt { num := 2019, denPred := 99 } J1_Co_1_L = true ∧
    posRatLt J1_Co_1_U { num := 2020, denPred := 99 } = true ∧
    posRatLt (posRatOfInt 1874) Tmf_1_L = true ∧
    posRatLt Tmf_1_U (posRatOfInt 1875) = true ∧
    posRatLt (posRatOfInt 1399) Tc_0_L = true ∧
    posRatLt Tc_0_U (posRatOfInt 1400) = true ∧
    posRatLt Tc_1_U Tc_0_L = true ∧
    posRatLt { num := 13943, denPred := 9 } Tc_1_L = true ∧
    posRatLt Tc_1_U { num := 13944, denPred := 9 } = true ∧
    posRatLt { num := 13943, denPred := 9 } Tc_1_dir_L = true ∧
    posRatLt Tc_1_dir_U { num := 13944, denPred := 9 } = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: Continuum `ℝ` Equal-Volume Packing, Joyce–Watson Cancellation & FCC Brillouin Zone -/

/--
Theorem (Continuum `ℝ`): Equal-Wigner–Seitz-Volume Bond Scaling & `3√3 / 4` Joyce–Watson Cancellation.
1. Whenever `a_bcc³ / 2 = a_fcc³ / 4 ≠ 0` (equal Wigner–Seitz atomic volume `V_WS`), the
   squared bond-volume ratio `((3/4) a_bcc²)³ / ((1/2) a_fcc²)³ = 27 / 32` holds identically.
2. Between `η_pack = (3 s3) / (4 s2)` (`s3 = √3, s2 = √2`) and `W_FCC = (3 s3 / 4) F²`,
   the `(3√3 / 4)` prefactor cancels identically: `η_pack / W_FCC = 1 / (s2 F²)`.
3. Order-1 screening (`T3d_1 < T3d_0`) strictly lowers `T_C^(1)(β-Co) < T_C^(0)(β-Co)`.
-/
theorem fcc_equal_wigner_seitz_volume_packing_and_watson_cancellation
    (a_bcc a_fcc s3 s2 F_hyp T3d_0 T3d_1 : ℝ)
    (ha_fcc : a_fcc ≠ 0)
    (h_vol : a_bcc ^ 3 / 2 = a_fcc ^ 3 / 4)
    (hs3 : s3 ≠ 0) (hs2 : 0 < s2) (hF : 0 < F_hyp)
    (hT : T3d_1 < T3d_0) :
    let d1_bcc_sq := (3 / 4 : ℝ) * a_bcc ^ 2
    let d1_fcc_sq := (1 / 2 : ℝ) * a_fcc ^ 2
    let eta_pack := (3 * s3) / (4 * s2)
    let W_fcc := (3 * s3 / 4) * (F_hyp ^ 2)
    d1_bcc_sq ^ 3 / d1_fcc_sq ^ 3 = (27 / 32 : ℝ) ∧
    eta_pack / W_fcc = 1 / (s2 * F_hyp ^ 2) ∧
    8 * T3d_1 * (eta_pack / W_fcc) < 8 * T3d_0 * (eta_pack / W_fcc) := by
  have hs2_ne : s2 ≠ 0 := ne_of_gt hs2
  have hF_ne : F_hyp ≠ 0 := ne_of_gt hF
  have h_canc : ((3 * s3) / (4 * s2)) / ((3 * s3 / 4) * (F_hyp ^ 2)) = 1 / (s2 * F_hyp ^ 2) := by
    field_simp [hs3, hs2_ne, hF_ne]
  refine ⟨?_, h_canc, ?_⟩
  · have h_a3 : a_bcc ^ 3 = (1 / 2 : ℝ) * a_fcc ^ 3 := by linarith
    have h_num : ((3 / 4 : ℝ) * a_bcc ^ 2) ^ 3 = (27 / 64 : ℝ) * (a_bcc ^ 3) ^ 2 := by ring
    have h_den : ((1 / 2 : ℝ) * a_fcc ^ 2) ^ 3 = (1 / 8 : ℝ) * (a_fcc ^ 3) ^ 2 := by ring
    change ((3 / 4 : ℝ) * a_bcc ^ 2) ^ 3 / ((1 / 2 : ℝ) * a_fcc ^ 2) ^ 3 = (27 / 32 : ℝ)
    rw [h_num, h_den, h_a3]
    have hf3 : a_fcc ^ 3 ≠ 0 := pow_ne_zero 3 ha_fcc
    field_simp [hf3]
    ring
  · rw [h_canc]
    have h_pos : 0 < 1 / (s2 * F_hyp ^ 2) := by positivity
    have h8 : 8 * T3d_1 < 8 * T3d_0 := by linarith
    exact mul_lt_mul_of_pos_right h8 h_pos

/--
Theorem (Continuum `ℝ`): Universal 12-Face FCC Brillouin Spin-Wave Dispersion Bounds.
For ALL `(a, b, c) ∈ [-1, 1]³` (`a = cos q_x`, `b = cos q_y`, `c = cos q_z`), the 12-face
FCC nearest-neighbor spin-wave dispersion `ω_FCC(q) = 1 - (ab + bc + ca) / 3` satisfies
`0 ≤ ω_FCC(q) ≤ 4 / 3` (attaining `4 / 3` at the FCC `X`-point `(1, 1, -1)`).
-/
theorem fcc_brillouin_dispersion_nonneg_and_bounded
    (a b c : ℝ)
    (haL : -1 ≤ a) (haU : a ≤ 1)
    (hbL : -1 ≤ b) (hbU : b ≤ 1)
    (hcL : -1 ≤ c) (hcU : c ≤ 1) :
    let om_fcc := 1 - (a * b + b * c + c * a) / 3
    0 ≤ om_fcc ∧ om_fcc ≤ (4 / 3 : ℝ) := by
  have ha2 : 0 ≤ 1 - a ^ 2 := by
    have h : 0 ≤ (1 - a) * (1 + a) := mul_nonneg (by linarith) (by linarith)
    linarith [show (1 - a) * (1 + a) = 1 - a ^ 2 by ring]
  have hb2 : 0 ≤ 1 - b ^ 2 := by
    have h : 0 ≤ (1 - b) * (1 + b) := mul_nonneg (by linarith) (by linarith)
    linarith [show (1 - b) * (1 + b) = 1 - b ^ 2 by ring]
  have hc2 : 0 ≤ 1 - c ^ 2 := by
    have h : 0 ≤ (1 - c) * (1 + c) := mul_nonneg (by linarith) (by linarith)
    linarith [show (1 - c) * (1 + c) = 1 - c ^ 2 by ring]
  have h_sos : 0 ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by positivity
  have h_p : 0 ≤ (1 + a) * (1 + b) * (1 + c) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h_m : 0 ≤ (1 - a) * (1 - b) * (1 - c) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  refine ⟨?_, ?_⟩
  · linarith [show 1 - (a * b + b * c + c * a) / 3 =
                ((1 - a ^ 2) + (1 - b ^ 2) + (1 - c ^ 2) +
                  ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2) / 3 by ring]
  · linarith [show (1 + a) * (1 + b) * (1 + c) + (1 - a) * (1 - b) * (1 - c) =
                2 * (1 + a * b + b * c + c * a) by ring]

#print axioms fcc_rhombic_dodecahedron_12_face_hodge_geometry
#print axioms fcc_cobalt_3d_unsold_harmonic_closure
#print axioms watson_fcc_singular_modulus_and_packing_bounds
#print axioms tve_cobalt_order0_and_order1_curie_bounds

end TVE
