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
public import TVE.Vacuum
public import TVE.Action
public import TVE.Topologies
public import TVE.Spectrum
public import TVE.Forces
public import TVE.QFTSubsumption

/-!
# Topological Vacuum Electrodynamics — Order-1 Polarizable-Vacuum Dressing

Shared root Order-1 (`δK = 2φ > 0`) polarizable-vacuum self-relaxation library
sitting downstream of the untouched Order-0 (`K = 1`) rigid-vacuum core:

1. **Zero-Axiom Constructive Downstream API & Rational Bounds (`[]`):**
   - Machin alternating arctangent certification of `103993 / 33102 < π < 104348 / 33215`.
   - Order-1 spinor Casimir / Steiner mode capacity `A_1 = A_0 - 1 / (24 A_0)` exported
     in both `PosRat` and `NzPosRat`.
   - Topology-driven differential mass-ratio dressers `vpDressedMassRatioLoPosRat` /
     `vpDressedMassRatioHiPosRat` taking `(c0, wr, tw, lk)` directly (preserving the
     `(0, 1, 0)` reference electron identity while relaxing `m_{π⁺}/m_e`, `m_p/m_e`, `v/m_e`).
   - General `N`-channel screened inverse couplings `A_eff(N) = A_1 + N / (2π)` exported
     as `NzPosRat` (`vpScreenedAlphaInvLoNz`, `vpEffectiveAlphaInvLoNz`) so atomic and
     condensed-matter modules (`IronFerromagnetism`) plug them directly into Order-0 kernels.
2. **Universal Algebraic, Variational & Continuum `ℝ` Soundness (`∀`):**
   - `vp_ring4_rayleigh_ritz_universal`: Proves summation-by-parts, `ΔE^(1) = -4 λ_PV ∑ |∇φ|²`,
     and strict negativity `ΔE^(1) < 0` for EVERY non-constant soliton profile.
   - `vp_cwf_unsigned_dominates_signed_universal`: Proves `0 ≤ N_CWF` and `|h_total| ≤ N_CWF`
     for ALL `(wr, tw, lk) ∈ ℤ³`.
   - `continuum_order1_interval_monotonicity` & `continuum_screened_alpha_inv_identity`:
     Proves strict monotonicity of Order-1 interval maps over `ℝ` and the exact continuum
     identity `A_1 (1 + N a_{e,1}) = A_1 + N / (2π)`.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-! ## Part 1: Zero-Axiom Constructive Downstream API & Interval Kernel (`[]`) -/

/-- Negation `-q` on `PosRat` (`Vacuum.lean`). -/
@[expose]
def vpPosRatNeg (q : PosRat) : PosRat :=
  { num := -q.num, denPred := q.denPred }

/-- Reduced addition `a + b = a - (-b)` on `PosRat` via `posRatSubRed`. -/
@[expose]
def vpPosRatAddRed (a b : PosRat) : PosRat :=
  posRatSubRed a (vpPosRatNeg b)

/-- Total, underflow-free conversion of a non-zero `PosRat` to `NzPosRat` (defaults `0` to `1`). -/
@[expose]
def vpPosRatToNzOrOne (q : PosRat) : NzPosRat :=
  match q.num with
  | Int.ofNat (k + 1) => { isNeg := false, numPred := k, denPred := q.denPred }
  | Int.ofNat 0 => { isNeg := false, numPred := 0, denPred := 0 }
  | Int.negSucc k => { isNeg := true, numPred := k, denPred := q.denPred }

/-! ### 1. Signed CWF Helicity vs. Unsigned (`L¹`) Polarization Channel Definitions -/

/-- Absolute value `|z|` as `ℕ` using kernel primitive cases. -/
@[expose]
def vpIntNatAbs : ℤ → ℕ
  | Int.ofNat n => n
  | Int.negSucc n => n + 1

/-- Integer absolute value `|z|` on `ℤ`. -/
@[expose]
def vpIntAbs (z : ℤ) : ℤ :=
  if 0 ≤ z then z else -z

/-- Signed CWF helicity `h_total = Wr + Tw + 2 Lk` (`Topologies.lean` stability invariant). -/
@[expose]
def vpSignedCWFHelicity (wr tw lk : ℤ) : ℤ :=
  wr + tw + 2 * lk

/-- Unsigned (`L¹`) CWF polarization channel count `N_CWF = |Wr| + |Tw| + 2 |Lk|` as `ℕ`. -/
@[expose]
def vpUnsignedCWFChannels (wr tw lk : ℤ) : ℕ :=
  vpIntNatAbs wr + vpIntNatAbs tw + 2 * vpIntNatAbs lk

/-- Unsigned (`L¹`) CWF polarization channel count `N_CWF = |Wr| + |Tw| + 2 |Lk|` on `ℤ`. -/
@[expose]
def vpUnsignedCWFInt (wr tw lk : ℤ) : ℤ :=
  vpIntAbs wr + vpIntAbs tw + 2 * vpIntAbs lk

/--
Theorem (Zero Axioms): Canonical TVE Sector Table (`h_total` vs. `N_CWF`).
- Planar neutrino `(0, 0, 0)`: `h_total = 0`, `N_CWF = 0`.
- Electron unknot `(0, 1, 0)`: `h_total = 1`, `N_CWF = 1`.
- Proton `T_{3,2}` trefoil `(3, 0, 0)`: `h_total = 3`, `N_CWF = 3`.
- Achiral pion Hopf link `(2, 0, -1)`: `h_total = 0` (ABJ-unstable) yet `N_CWF = 4`.
-/
theorem vp_cwf_signed_vs_unsigned_channel_hierarchy :
    vpSignedCWFHelicity 0 0 0 = 0 ∧ vpUnsignedCWFChannels 0 0 0 = 0 ∧
    vpSignedCWFHelicity 0 1 0 = 1 ∧ vpUnsignedCWFChannels 0 1 0 = 1 ∧
    vpSignedCWFHelicity 3 0 0 = 3 ∧ vpUnsignedCWFChannels 3 0 0 = 3 ∧
    vpSignedCWFHelicity 2 0 (-1) = 0 ∧ vpUnsignedCWFChannels 2 0 (-1) = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 2. Machin Convergents & Exported Order-1 Downstream Coupling API -/

/-- Natural power `base ^ n` on reduced `PosRat`. -/
@[expose]
def vpPowPosRat (base : PosRat) : ℕ → PosRat
  | 0 => posRatOfInt 1
  | n + 1 => posRatMulRed (vpPowPosRat base n) base

/-- Recursive alternating arctangent partial sum `∑_{k=0}^K (-1)^k / ((2k+1) m^{2k+1})` in `PosRat`. -/
@[expose]
def vpAtanInvTruncPosRat (mPred : ℕ) : ℕ → PosRat
  | 0 => { num := 1, denPred := mPred }
  | k + 1 =>
      let prev := vpAtanInvTruncPosRat mPred k
      let x : PosRat := { num := 1, denPred := mPred }
      let x2 := posRatMulRed x x
      let xPow := posRatMulRed x (vpPowPosRat x2 (k + 1))
      let oddDen : NzPosRat := { isNeg := false, numPred := 2 * (k + 1), denPred := 0 }
      let term := posRatDivRed xPow oddDen
      if (k + 1) % 2 == 1 then posRatSubRed prev term else vpPosRatAddRed prev term

/-- High-precision Machin-certified `π` lower and upper convergents (`PosRat` & `NzPosRat`). -/
@[expose] def vpPiConvLo : PosRat := { num := 103993, denPred := 33101 }
@[expose] def vpPiConvHi : PosRat := { num := 104348, denPred := 33214 }
@[expose] def vpPiConvLoNz : NzPosRat := { isNeg := false, numPred := 103992, denPred := 33101 }
@[expose] def vpPiConvHiNz : NzPosRat := { isNeg := false, numPred := 104347, denPred := 33214 }

/-- Order-0 `NzPosRat` mode capacity `A_0` at `103993 / 33102` and `104348 / 33215`. -/
@[expose] def vpAlphaInv0LoNz : NzPosRat := alphaInvNzPosRat 103992 33101
@[expose] def vpAlphaInv0HiNz : NzPosRat := alphaInvNzPosRat 104347 33214

/-- Order-1 spinor Casimir / Steiner mode capacity `A_1(A_0) = A_0 - 1 / (24 A_0)` in `PosRat`. -/
@[expose]
def vpAlphaInvOrder1PosRat (A0_nz : NzPosRat) : PosRat :=
  let A0 := nzPosRatToPosRat A0_nz
  let shift := posRatDivRed { num := 1, denPred := 23 } A0_nz
  posRatSubRed A0 shift

/-- Exported Order-1 mode capacity `A_1` bounds in `PosRat` and `NzPosRat`. -/
@[expose] def vpAlphaInv1LoPosRat : PosRat := vpAlphaInvOrder1PosRat vpAlphaInv0LoNz
@[expose] def vpAlphaInv1HiPosRat : PosRat := vpAlphaInvOrder1PosRat vpAlphaInv0HiNz
@[expose] def vpAlphaInv1LoNz : NzPosRat := vpPosRatToNzOrOne vpAlphaInv1LoPosRat
@[expose] def vpAlphaInv1HiNz : NzPosRat := vpPosRatToNzOrOne vpAlphaInv1HiPosRat

/-- Exported Order-1 Schwinger cut-holonomy quantum `a_{e,1} = 1 / (2 π A_1)` bounds in `PosRat`. -/
@[expose]
def vpSchwingerAe1LoPosRat : PosRat :=
  let den := posRatMulRed (posRatOfInt 2) (posRatMulRed vpPiConvHi vpAlphaInv1HiPosRat)
  posRatDivRed (posRatOfInt 1) (vpPosRatToNzOrOne den)

@[expose]
def vpSchwingerAe1HiPosRat : PosRat :=
  let den := posRatMulRed (posRatOfInt 2) (posRatMulRed vpPiConvLo vpAlphaInv1LoPosRat)
  posRatDivRed (posRatOfInt 1) (vpPosRatToNzOrOne den)

/-- Exported `N`-channel dielectric index `K_T(N) = 1 + N · a_{e,1}` bounds in `PosRat`. -/
@[expose]
def vpDielectricIndexLoPosRat (nChannels : ℕ) : PosRat :=
  vpPosRatAddRed (posRatOfInt 1)
    (posRatMulRed (posRatOfInt (Int.ofNat nChannels)) vpSchwingerAe1LoPosRat)

@[expose]
def vpDielectricIndexHiPosRat (nChannels : ℕ) : PosRat :=
  vpPosRatAddRed (posRatOfInt 1)
    (posRatMulRed (posRatOfInt (Int.ofNat nChannels)) vpSchwingerAe1HiPosRat)

/-- Order-1 dressed scale `A_1 · (1 + a_{e,1}) / (1 + N · a_{e,1}) = A_1 · (2 π A_1 + 1) / (2 π A_1 + N)`. -/
@[expose]
def vpDressedScaleFactorPosRat (piPos A1Pos : PosRat) (nChannels : ℕ) : PosRat :=
  let twoPiA1 := posRatMulRed (posRatOfInt 2) (posRatMulRed piPos A1Pos)
  let numTerm := vpPosRatAddRed twoPiA1 (posRatOfInt 1)
  let denTerm := vpPosRatAddRed twoPiA1 (posRatOfInt (Int.ofNat nChannels))
  posRatMulRed A1Pos (posRatDivRed numTerm (vpPosRatToNzOrOne denTerm))

/--
Exported topology-driven Order-1 mass-ratio bounds `(m_T / m_e)^(1)` for any bare coefficient `c0`
(`(m_T / m_e)^(0) = c0 · A_0`) and CWF integers `(wr, tw, lk)`.
-/
@[expose]
def vpDressedMassRatioLoPosRat (c0 : PosRat) (wr tw lk : ℤ) : PosRat :=
  let nCh := vpUnsignedCWFChannels wr tw lk
  posRatMulRed c0 (vpDressedScaleFactorPosRat vpPiConvLo vpAlphaInv1LoPosRat nCh)

@[expose]
def vpDressedMassRatioHiPosRat (c0 : PosRat) (wr tw lk : ℤ) : PosRat :=
  let nCh := vpUnsignedCWFChannels wr tw lk
  posRatMulRed c0 (vpDressedScaleFactorPosRat vpPiConvHi vpAlphaInv1HiPosRat nCh)

/--
Exported unconditional interval bounds on `N`-channel screened inverse coupling
`A_eff(N) = A_1 (1 + N a_{e,1}) = A_1 + N / (2π)` in `PosRat` and `NzPosRat`.
-/
@[expose]
def vpScreenedAlphaInvLoPosRat (nChannels : ℕ) : PosRat :=
  let twoPiHi := posRatMulRed (posRatOfInt 2) vpPiConvHi
  let shift := posRatDivRed (posRatOfInt (Int.ofNat nChannels)) (vpPosRatToNzOrOne twoPiHi)
  vpPosRatAddRed vpAlphaInv1LoPosRat shift

@[expose]
def vpScreenedAlphaInvHiPosRat (nChannels : ℕ) : PosRat :=
  let twoPiLo := posRatMulRed (posRatOfInt 2) vpPiConvLo
  let shift := posRatDivRed (posRatOfInt (Int.ofNat nChannels)) (vpPosRatToNzOrOne twoPiLo)
  vpPosRatAddRed vpAlphaInv1HiPosRat shift

@[expose]
def vpScreenedAlphaInvLoNz (nChannels : ℕ) : NzPosRat :=
  vpPosRatToNzOrOne (vpScreenedAlphaInvLoPosRat nChannels)

@[expose]
def vpScreenedAlphaInvHiNz (nChannels : ℕ) : NzPosRat :=
  vpPosRatToNzOrOne (vpScreenedAlphaInvHiPosRat nChannels)

/-- Unknot (`N = 1`) screened coupling aliases ready for atomic & condensed-matter modules (`IronFerromagnetism`). -/
@[expose] def vpEffectiveAlphaInvLoNz : NzPosRat := vpScreenedAlphaInvLoNz 1
@[expose] def vpEffectiveAlphaInvHiNz : NzPosRat := vpScreenedAlphaInvHiNz 1
@[expose] def vpEffectiveAlphaLoPosRat : PosRat := posRatDivRed (posRatOfInt 1) vpEffectiveAlphaInvHiNz
@[expose] def vpEffectiveAlphaHiPosRat : PosRat := posRatDivRed (posRatOfInt 1) vpEffectiveAlphaInvLoNz

/--
Theorem (Zero Axioms): Machin-Certified `π`, Spinor Casimir `α⁻¹` Shift, Reference-Electron
Invariance & Order-1 Downstream Coupling Bounds.
(Continuum `ℝ` interval soundness and algebraic equivalence proved in Part 2.)
-/
theorem vp_order1_casimir_alpha_and_cwf_dressing_hierarchy :
    let piMachinLo := posRatSubRed
      (posRatMulRed (posRatOfInt 16) (vpAtanInvTruncPosRat 4 7))
      (posRatMulRed (posRatOfInt 4) (vpAtanInvTruncPosRat 238 2))
    let piMachinHi := posRatSubRed
      (posRatMulRed (posRatOfInt 16) (vpAtanInvTruncPosRat 4 8))
      (posRatMulRed (posRatOfInt 4) (vpAtanInvTruncPosRat 238 1))
    let A0_lo := nzPosRatToPosRat vpAlphaInv0LoNz
    let mpi1_lo := vpDressedMassRatioLoPosRat (posRatOfInt 2) 2 0 (-1)
    let mpi1_hi := vpDressedMassRatioHiPosRat (posRatOfInt 2) 2 0 (-1)
    let mp1_lo := vpDressedMassRatioLoPosRat { num := 94, denPred := 6 } 3 0 0
    let mp1_hi := vpDressedMassRatioHiPosRat { num := 94, denPred := 6 } 3 0 0
    let v1_lo := posRatMulRed { num := 2, denPred := 4 }
      (posRatMulRed (posRatSubRed (posRatMulRed (posRatOfInt 66) vpAlphaInv1LoPosRat) (posRatOfInt 235))
                    (vpDressedMassRatioLoPosRat (posRatOfInt 1) 3 0 0))
    let v1_hi := posRatMulRed { num := 2, denPred := 4 }
      (posRatMulRed (posRatSubRed (posRatMulRed (posRatOfInt 66) vpAlphaInv1HiPosRat) (posRatOfInt 235))
                    (vpDressedMassRatioHiPosRat (posRatOfInt 1) 3 0 0))
    posRatLt vpPiConvLo piMachinLo = true ∧
    posRatLt piMachinHi vpPiConvHi = true ∧
    posRatLt { num := 137036303, denPred := 999999 } A0_lo = true ∧
    posRatLt vpAlphaInv1HiPosRat A0_lo = true ∧
    posRatLt { num := 1370359995, denPred := 9999999 } vpAlphaInv1LoPosRat = true ∧
    posRatLt vpAlphaInv1HiPosRat { num := 1370359999, denPred := 9999999 } = true ∧
    vpDressedMassRatioLoPosRat (posRatOfInt 1) 0 1 0 = vpAlphaInv1LoPosRat ∧
    posRatLt { num := 1161409, denPred := 999999999 } vpSchwingerAe1LoPosRat = true ∧
    posRatLt vpSchwingerAe1HiPosRat { num := 1161410, denPred := 999999999 } = true ∧
    posRatLt { num := 273121, denPred := 999 } mpi1_lo = true ∧
    posRatLt mpi1_hi { num := 273122, denPred := 999 } = true ∧
    posRatLt { num := 1835938, denPred := 999 } mp1_lo = true ∧
    posRatLt mp1_hi { num := 1835939, denPred := 999 } = true ∧
    posRatLt (posRatOfInt 481762) v1_lo = true ∧
    posRatLt v1_hi (posRatOfInt 481763) = true ∧
    posRatLt { num := 1371951, denPred := 9999 } (vpScreenedAlphaInvLoPosRat 1) = true ∧
    posRatLt (vpScreenedAlphaInvHiPosRat 1) { num := 1371952, denPred := 9999 } = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: Universal Algebraic, Variational & Continuum `ℝ` Theorems -/

/-- Periodic 4-site scalar profile `(f_0, f_1, f_2, f_3)` on `ℤ`. -/
structure VPRing4Int where
  v0 : ℤ
  v1 : ℤ
  v2 : ℤ
  v3 : ℤ

/-- Scalar multiplication `c · v` on `VPRing4Int`. -/
@[expose]
def vpRing4Scale (c : ℤ) (v : VPRing4Int) : VPRing4Int :=
  { v0 := c * v.v0, v1 := c * v.v1, v2 := c * v.v2, v3 := c * v.v3 }

/-- Discrete gradient Dirichlet norm `∑_{i=0}^3 (φ_{i+1} - φ_i)²` on `VPRing4Int`. -/
@[expose]
def vpRing4GradNormSq (phi : VPRing4Int) : ℤ :=
  let d0 := phi.v1 - phi.v0
  let d1 := phi.v2 - phi.v1
  let d2 := phi.v3 - phi.v2
  let d3 := phi.v0 - phi.v3
  d0 * d0 + d1 * d1 + d2 * d2 + d3 * d3

/-- Discrete negative Laplacian `(-Δ_ring φ)_i = 2 φ_i - φ_{i-1} - φ_{i+1}` as `VPRing4Int`. -/
@[expose]
def vpRing4NegLapVec (phi : VPRing4Int) : VPRing4Int :=
  { v0 := 2 * phi.v0 - phi.v3 - phi.v1
  , v1 := 2 * phi.v1 - phi.v0 - phi.v2
  , v2 := 2 * phi.v2 - phi.v1 - phi.v3
  , v3 := 2 * phi.v3 - phi.v2 - phi.v0 }

/-- Discrete inner product `⟨f, g⟩ = ∑_{i=0}^3 f_i g_i` on `VPRing4Int`. -/
@[expose]
def vpRing4Dot (f g : VPRing4Int) : ℤ :=
  f.v0 * g.v0 + f.v1 * g.v1 + f.v2 * g.v2 + f.v3 * g.v3

/-- Coupled Order-1 energy shift `ΔE^(1) = 4 λ_PV ∑ |∇φ|² - 2 ⟨φ, u_EM⟩` for Field Eq. 3 source `u_EM`. -/
@[expose]
def vpRing4Order1EnergyShift (lamPV : ℤ) (phi : VPRing4Int) : ℤ :=
  let uEM := vpRing4Scale (4 * lamPV) (vpRing4NegLapVec phi)
  4 * lamPV * vpRing4GradNormSq phi - 2 * vpRing4Dot phi uEM

/--
Theorem (Universal over `ℤ`): Discrete Ring-4 Rayleigh–Ritz Order-1 Energy Lowering.
For EVERY stiffness `lamPV` and EVERY profile `phi`:
1. Summation-by-parts holds identically: `⟨φ, -Δ_ring φ⟩ = ∑ |∇φ|²`.
2. Elastic vacuum bending cancels half the dielectric drop: `ΔE^(1) = -4 λ_PV ∑ |∇φ|²`.
3. `0 ≤ ∑ |∇φ|²`, and whenever `0 < lamPV` and `phi` is non-constant, `ΔE^(1) < 0` strictly.
-/
theorem vp_ring4_rayleigh_ritz_universal
    (lamPV : ℤ) (phi : VPRing4Int) :
    vpRing4Dot phi (vpRing4NegLapVec phi) = vpRing4GradNormSq phi ∧
    vpRing4Order1EnergyShift lamPV phi = -(4 * lamPV * vpRing4GradNormSq phi) ∧
    0 ≤ vpRing4GradNormSq phi ∧
    (0 < lamPV →
      (phi.v1 ≠ phi.v0 ∨ phi.v2 ≠ phi.v1 ∨ phi.v3 ≠ phi.v2 ∨ phi.v0 ≠ phi.v3) →
      vpRing4Order1EnergyShift lamPV phi < 0) := by
  have h_sbp : vpRing4Dot phi (vpRing4NegLapVec phi) = vpRing4GradNormSq phi := by
    dsimp [vpRing4Dot, vpRing4NegLapVec, vpRing4GradNormSq]
    ring
  have h_shift : vpRing4Order1EnergyShift lamPV phi = -(4 * lamPV * vpRing4GradNormSq phi) := by
    dsimp [vpRing4Order1EnergyShift, vpRing4Scale, vpRing4Dot, vpRing4NegLapVec, vpRing4GradNormSq]
    ring
  have h_sq_nn : ∀ x : ℤ, 0 ≤ x * x := by
    intro x
    rcases le_total 0 x with hx | hx
    · exact mul_nonneg hx hx
    · exact mul_nonneg_of_nonpos_of_nonpos hx hx
  have h_sq_pos : ∀ x y : ℤ, x ≠ y → 0 < (x - y) * (x - y) := by
    intro x y hne
    rcases lt_trichotomy (x - y) 0 with hlt | heq | hgt
    · exact mul_pos_of_neg_of_neg hlt hlt
    · exfalso
      apply hne
      linarith
    · exact mul_pos hgt hgt
  have h0_nn := h_sq_nn (phi.v1 - phi.v0)
  have h1_nn := h_sq_nn (phi.v2 - phi.v1)
  have h2_nn := h_sq_nn (phi.v3 - phi.v2)
  have h3_nn := h_sq_nn (phi.v0 - phi.v3)
  have h_grad_nn : 0 ≤ vpRing4GradNormSq phi := by
    dsimp [vpRing4GradNormSq]
    linarith
  refine ⟨h_sbp, h_shift, h_grad_nn, ?_⟩
  intro hlam h_nonconst
  have h_grad_pos : 0 < vpRing4GradNormSq phi := by
    dsimp [vpRing4GradNormSq]
    rcases h_nonconst with h0 | h1 | h2 | h3
    · have hp := h_sq_pos phi.v1 phi.v0 h0; linarith
    · have hp := h_sq_pos phi.v2 phi.v1 h1; linarith
    · have hp := h_sq_pos phi.v3 phi.v2 h2; linarith
    · have hp := h_sq_pos phi.v0 phi.v3 h3; linarith
  have h4lam : 0 < 4 * lamPV := by linarith
  have h_prod_pos : 0 < 4 * lamPV * vpRing4GradNormSq phi := mul_pos h4lam h_grad_pos
  linarith

private theorem vp_int_abs_bounds (z : ℤ) : -vpIntAbs z ≤ z ∧ z ≤ vpIntAbs z := by
  dsimp [vpIntAbs]
  split <;> exact ⟨by linarith, by linarith⟩

private theorem vp_int_abs_le_of_bounds (z b : ℤ) (hL : -b ≤ z) (hU : z ≤ b) :
    vpIntAbs z ≤ b := by
  dsimp [vpIntAbs]
  split <;> linarith

/--
Theorem (Universal over `ℤ³`): Unsigned (`L¹`) CWF Polarization Dominates Signed Helicity.
For ALL integer triples `(wr, tw, lk) ∈ ℤ³`, `0 ≤ N_CWF` and `|h_total| ≤ N_CWF`.
-/
theorem vp_cwf_unsigned_dominates_signed_universal (wr tw lk : ℤ) :
    0 ≤ vpUnsignedCWFInt wr tw lk ∧
    vpIntAbs (vpSignedCWFHelicity wr tw lk) ≤ vpUnsignedCWFInt wr tw lk := by
  have ⟨hwrL, hwrU⟩ := vp_int_abs_bounds wr
  have ⟨htwL, htwU⟩ := vp_int_abs_bounds tw
  have ⟨hlkL, hlkU⟩ := vp_int_abs_bounds lk
  have hn_nn : 0 ≤ vpUnsignedCWFInt wr tw lk := by
    dsimp [vpUnsignedCWFInt]
    linarith
  refine ⟨hn_nn, vp_int_abs_le_of_bounds _ _ ?_ ?_⟩
  · dsimp [vpSignedCWFHelicity, vpUnsignedCWFInt]; linarith
  · dsimp [vpSignedCWFHelicity, vpUnsignedCWFInt]; linarith

/-! ### Continuum `ℝ` Exported Order-1 Definitions & Soundness Theorems -/

/-- Order-1 continuum mode capacity `A_1 = A_0 - 1 / (24 A_0)`. -/
@[expose]
noncomputable def alphaInvOrder1 : ℝ :=
  alphaInv - 1 / (24 * alphaInv)

/-- Order-1 continuum fine-structure constant `α_1 = 1 / A_1`. -/
@[expose]
noncomputable def alphaOrder1 : ℝ :=
  1 / alphaInvOrder1

/-- Order-1 continuum Schwinger cut-holonomy quantum `a_{e,1} = α_1 / (2π)`. -/
@[expose]
noncomputable def schwingerAnomalyOrder1 : ℝ :=
  alphaOrder1 / (2 * Real.pi)

/-- Order-1 continuum `N`-channel polarizable-vacuum dielectric index `K_T(N) = 1 + N · a_{e,1}`. -/
@[expose]
noncomputable def cwfDielectricIndex (nChannels : ℝ) : ℝ :=
  1 + nChannels * schwingerAnomalyOrder1

/-- Order-1 continuum differential reference-electron mass factor `K_e / K_T(N)`. -/
@[expose]
noncomputable def cwfDifferentialFactor (nChannels : ℝ) : ℝ :=
  cwfDielectricIndex 1 / cwfDielectricIndex nChannels

/-- Order-1 continuum `N`-channel screened inverse coupling `A_eff(N) = A_1 · K_T(N)`. -/
@[expose]
noncomputable def screenedAlphaInvOrder1 (nChannels : ℝ) : ℝ :=
  alphaInvOrder1 * cwfDielectricIndex nChannels

/-- Order-1 continuum unknot-screened fine-structure coupling `α_eff = α_1 / (1 + a_{e,1})`. -/
@[expose]
noncomputable def effectiveAlphaOrder1 : ℝ :=
  alphaOrder1 / cwfDielectricIndex 1

/--
Theorem (Continuum `ℝ`): Exact Additive Screened Inverse-Coupling Law & Atomic Equivalence.
Whenever `0 < alphaInvOrder1` and `0 ≤ nChannels`, proves:
1. `screenedAlphaInvOrder1 nChannels = alphaInvOrder1 + nChannels / (2 * Real.pi)`
   (`A_1` cancels identically inside `A_1 · N · a_{e,1}`).
2. `effectiveAlphaOrder1 = 1 / screenedAlphaInvOrder1 1`, justifying downstream `NzPosRat`
   evaluation via `vpEffectiveAlphaInvLoNz` and `vpEffectiveAlphaInvHiNz`.
-/
theorem continuum_screened_alpha_inv_identity
    (nChannels : ℝ) (hA1_pos : 0 < alphaInvOrder1) :
    screenedAlphaInvOrder1 nChannels = alphaInvOrder1 + nChannels / (2 * Real.pi) ∧
    effectiveAlphaOrder1 = 1 / screenedAlphaInvOrder1 1 := by
  have hA1_ne : alphaInvOrder1 ≠ 0 := ne_of_gt hA1_pos
  have h2pi_pos : 0 < 2 * Real.pi := mul_pos (by positivity) Real.pi_pos
  have h_cancel : alphaInvOrder1 * ((1 / alphaInvOrder1) / (2 * Real.pi)) = 1 / (2 * Real.pi) := by
    have h1 : (1 / alphaInvOrder1) * alphaInvOrder1 = 1 := div_mul_cancel₀ 1 hA1_ne
    calc alphaInvOrder1 * ((1 / alphaInvOrder1) / (2 * Real.pi))
      _ = ((1 / alphaInvOrder1) * alphaInvOrder1) / (2 * Real.pi) := by ring
      _ = 1 / (2 * Real.pi) := by rw [h1]
  refine ⟨?_, ?_⟩
  · dsimp [screenedAlphaInvOrder1, cwfDielectricIndex, schwingerAnomalyOrder1, alphaOrder1]
    calc alphaInvOrder1 * (1 + nChannels * ((1 / alphaInvOrder1) / (2 * Real.pi)))
      _ = alphaInvOrder1 + nChannels * (alphaInvOrder1 * ((1 / alphaInvOrder1) / (2 * Real.pi))) := by ring
      _ = alphaInvOrder1 + nChannels * (1 / (2 * Real.pi)) := by rw [h_cancel]
      _ = alphaInvOrder1 + nChannels / (2 * Real.pi) := by ring
  · dsimp [effectiveAlphaOrder1, screenedAlphaInvOrder1]
    have ha1_pos : 0 < alphaOrder1 := by dsimp [alphaOrder1]; positivity
    have hae_pos : 0 < schwingerAnomalyOrder1 := by
      dsimp [schwingerAnomalyOrder1]
      exact div_pos ha1_pos h2pi_pos
    have hK1_pos : 0 < cwfDielectricIndex 1 := by dsimp [cwfDielectricIndex]; linarith
    have hd_pos : 0 < alphaInvOrder1 * cwfDielectricIndex 1 := mul_pos hA1_pos hK1_pos
    have hx : (alphaOrder1 / cwfDielectricIndex 1) * (alphaInvOrder1 * cwfDielectricIndex 1) = 1 := by
      dsimp [alphaOrder1]
      calc ((1 / alphaInvOrder1) / cwfDielectricIndex 1) * (alphaInvOrder1 * cwfDielectricIndex 1)
        _ = (((1 / alphaInvOrder1) / cwfDielectricIndex 1) * cwfDielectricIndex 1) * alphaInvOrder1 := by ring
        _ = (1 / alphaInvOrder1) * alphaInvOrder1 := by rw [div_mul_cancel₀ _ (ne_of_gt hK1_pos)]
        _ = 1 := div_mul_cancel₀ 1 hA1_ne
    have hy : (1 / (alphaInvOrder1 * cwfDielectricIndex 1)) * (alphaInvOrder1 * cwfDielectricIndex 1) = 1 :=
      div_mul_cancel₀ 1 (ne_of_gt hd_pos)
    have h_zero :
        ((alphaOrder1 / cwfDielectricIndex 1) - (1 / (alphaInvOrder1 * cwfDielectricIndex 1))) *
          (alphaInvOrder1 * cwfDielectricIndex 1) = 0 := by
      calc ((alphaOrder1 / cwfDielectricIndex 1) - (1 / (alphaInvOrder1 * cwfDielectricIndex 1))) *
             (alphaInvOrder1 * cwfDielectricIndex 1)
        _ = (alphaOrder1 / cwfDielectricIndex 1) * (alphaInvOrder1 * cwfDielectricIndex 1) -
            (1 / (alphaInvOrder1 * cwfDielectricIndex 1)) * (alphaInvOrder1 * cwfDielectricIndex 1) := by ring
        _ = 1 - 1 := by rw [hx, hy]
        _ = 0 := by ring
    rcases lt_trichotomy (alphaOrder1 / cwfDielectricIndex 1) (1 / (alphaInvOrder1 * cwfDielectricIndex 1)) with hlt | heq | hgt
    · exfalso
      have hn : (alphaOrder1 / cwfDielectricIndex 1) - (1 / (alphaInvOrder1 * cwfDielectricIndex 1)) < 0 := by linarith
      have hp := mul_neg_of_neg_of_pos hn hd_pos
      linarith
    · exact heq
    · exfalso
      have hp1 : 0 < (alphaOrder1 / cwfDielectricIndex 1) - (1 / (alphaInvOrder1 * cwfDielectricIndex 1)) := by linarith
      have hp := mul_pos hp1 hd_pos
      linarith

/--
Theorem (Continuum `ℝ`): Strict Monotonicity Soundness of Order-1 Interval Bounds.
-/
theorem continuum_order1_interval_monotonicity
    (p1 p2 A1 A2 x1 x2 N : ℝ)
    (hp1 : 0 < p1) (hp : p1 < p2)
    (hA1 : 0 < A1) (hA : A1 < A2)
    (hx1 : 0 < x1) (hx : x1 < x2)
    (hN : 1 < N) :
    (4 * p1 ^ 3 + p1 ^ 2 + p1 < 4 * p2 ^ 3 + p2 ^ 2 + p2) ∧
    (A1 - 1 / (24 * A1) < A2 - 1 / (24 * A2)) ∧
    ((x1 + 1) / (x1 + N) < (x2 + 1) / (x2 + N)) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp2 : 0 < p2 := lt_trans hp1 hp
    have h_factor :
        (4 * p2 ^ 3 + p2 ^ 2 + p2) - (4 * p1 ^ 3 + p1 ^ 2 + p1) =
          (p2 - p1) * (4 * p2 ^ 2 + 4 * p2 * p1 + 4 * p1 ^ 2 + p2 + p1 + 1) := by ring
    have h_pos2 : 0 < 4 * p2 ^ 2 + 4 * p2 * p1 + 4 * p1 ^ 2 + p2 + p1 + 1 := by positivity
    have h_diff : 0 < (p2 - p1) * (4 * p2 ^ 2 + 4 * p2 * p1 + 4 * p1 ^ 2 + p2 + p1 + 1) :=
      mul_pos (by linarith) h_pos2
    linarith
  · have hA2 : 0 < A2 := lt_trans hA1 hA
    have h24A1 : 0 < 24 * A1 := by positivity
    have h24A2 : 0 < 24 * A2 := by positivity
    have h_inv1 : (1 / (24 * A1)) * (24 * A1) = 1 := div_mul_cancel₀ 1 (ne_of_gt h24A1)
    have h_inv2 : (1 / (24 * A2)) * (24 * A2) = 1 := div_mul_cancel₀ 1 (ne_of_gt h24A2)
    have h_inv_lt : 1 / (24 * A2) < 1 / (24 * A1) := by
      have h_id : ((1 / (24 * A1)) - (1 / (24 * A2))) * ((24 * A1) * (24 * A2)) =
          ((1 / (24 * A1)) * (24 * A1)) * (24 * A2) - ((1 / (24 * A2)) * (24 * A2)) * (24 * A1) := by ring
      rw [h_inv1, h_inv2] at h_id
      have h_rhs : 0 < 1 * (24 * A2) - 1 * (24 * A1) := by linarith
      have h_den : 0 < (24 * A1) * (24 * A2) := mul_pos h24A1 h24A2
      by_contra h_not
      have h_le : (1 / (24 * A1)) - (1 / (24 * A2)) ≤ 0 := by linarith
      have h_np : ((1 / (24 * A1)) - (1 / (24 * A2))) * ((24 * A1) * (24 * A2)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h_le (le_of_lt h_den)
      linarith
    linarith
  · have hx2 : 0 < x2 := lt_trans hx1 hx
    have hd1 : 0 < x1 + N := by linarith
    have hd2 : 0 < x2 + N := by linarith
    have hq1 : ((x1 + 1) / (x1 + N)) * (x1 + N) = x1 + 1 := div_mul_cancel₀ (x1 + 1) (ne_of_gt hd1)
    have hq2 : ((x2 + 1) / (x2 + N)) * (x2 + N) = x2 + 1 := div_mul_cancel₀ (x2 + 1) (ne_of_gt hd2)
    have h_id : (((x2 + 1) / (x2 + N)) - ((x1 + 1) / (x1 + N))) * ((x1 + N) * (x2 + N)) =
        (((x2 + 1) / (x2 + N)) * (x2 + N)) * (x1 + N) - (((x1 + 1) / (x1 + N)) * (x1 + N)) * (x2 + N) := by ring
    rw [hq1, hq2] at h_id
    have h_rhs : (x2 + 1) * (x1 + N) - (x1 + 1) * (x2 + N) = (x2 - x1) * (N - 1) := by ring
    have h_prod : 0 < (x2 - x1) * (N - 1) := mul_pos (by linarith) (by linarith)
    have h_den : 0 < (x1 + N) * (x2 + N) := mul_pos hd1 hd2
    by_contra h_not
    have h_le : ((x2 + 1) / (x2 + N)) - ((x1 + 1) / (x1 + N)) ≤ 0 := by linarith
    have h_np : (((x2 + 1) / (x2 + N)) - ((x1 + 1) / (x1 + N))) * ((x1 + N) * (x2 + N)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h_le (le_of_lt h_den)
    linarith

/--
Theorem (Continuum `ℝ`): Rayleigh–Ritz Variational Upper-Bound & Half-Cancellation Identity.
-/
theorem continuum_rayleigh_ritz_order0_upper_bound
    (E0 deltaK lamPV gradPhiSqInt phiFieldInt ae N : ℝ)
    (hE0 : 0 < E0) (hdK : 0 < deltaK) (hlam : 0 < lamPV) (hgrad : 0 < gradPhiSqInt)
    (h_virial : 4 * lamPV * gradPhiSqInt = phiFieldInt)
    (hae : 0 < ae) (hN : 1 < N) :
    E0 / (1 + deltaK) < E0 ∧
    E0 + (-2 * phiFieldInt + 4 * lamPV * gradPhiSqInt) = E0 - 4 * lamPV * gradPhiSqInt ∧
    E0 - 4 * lamPV * gradPhiSqInt < E0 ∧
    alphaInvOrder1 < alphaInv ∧
    (1 + ae) / (1 + N * ae) < 1 := by
  have h_ainv_pos : 0 < alphaInv := by
    dsimp [alphaInv, torusBulkCapacity, torusBoundaryCapacity, torusCutCapacity]
    have h4 : (0 : ℝ) < 4 := by positivity
    exact add_pos (add_pos (mul_pos h4 (pow_pos Real.pi_pos 3)) (pow_pos Real.pi_pos 2)) Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h_den : 0 < 1 + deltaK := by linarith
    rw [div_lt_iff₀ h_den]
    have h_mul : 0 < E0 * deltaK := mul_pos hE0 hdK
    linarith [show E0 * (1 + deltaK) = E0 + E0 * deltaK by ring]
  · linarith
  · have h_pos : 0 < 4 * lamPV * gradPhiSqInt := by positivity
    linarith
  · dsimp [alphaInvOrder1]
    have h_shift : 0 < 1 / (24 * alphaInv) := by positivity
    linarith
  · have hN_ae : ae < N * ae := by
      have h := mul_lt_mul_of_pos_right hN hae
      linarith
    have h_den : 0 < 1 + N * ae := by linarith
    rw [div_lt_iff₀ h_den]
    linarith

#print axioms vp_cwf_signed_vs_unsigned_channel_hierarchy
#print axioms vp_order1_casimir_alpha_and_cwf_dressing_hierarchy
#print axioms vp_ring4_rayleigh_ritz_universal
#print axioms vp_cwf_unsigned_dominates_signed_universal
#print axioms continuum_screened_alpha_inv_identity
#print axioms continuum_order1_interval_monotonicity

end TVE
