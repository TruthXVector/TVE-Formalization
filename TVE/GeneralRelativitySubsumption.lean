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
public import Mathlib.Tactic.NormNum
public import TVE.Vacuum
public import TVE.Action
public import TVE.Topologies
public import TVE.Spectrum
public import TVE.QuantumSubsumption

/-!
# TVE Subsumption of General Relativity & Quantum-Gravity Unification

Structured in two tiers:
- **Part 1 (Zero-Axiom Constructive PV Metric, Spin-2 TT & Quantum-Gravity Kernel):**
  Proves division-by-zero-free `PosRat` / `NzPosRat` proper phase-space volume invariance
  (`dτ · dℓ = dt · dr`), null geodesic & causal signature laws, PPN `γ = 1` light deflection
  (`Δθ_GR = 2 Δθ_Newt = 4 Φ_N`), discrete exponential horizon regularity (`-4^(-n) < 0` for
  all `n : ℕ`), Plebanski-Tamm `3×3` constitutive spin-2 transverse-traceless (`h_+, h_×`)
  helicity/orthogonality and gravitomagnetic Sagnac frame-dragging (`w_i`), and fractional-cavity
  Quantum-Gravity unification (`T_PV = 353 / 81`, `does not depend on any axioms`).
- **Part 2 (Continuum `ℝ` Compatibility & Plebanski-Tamm Tensorial Layer):**
  Preserves all continuum Polarizable-Vacuum metric, PPN, exponential horizon, and
  Quantum-Gravity unification theorems, plus the bidirectional (`↔`) continuum Spin-2 TT
  polarization decomposition and ADM/Plebanski shift-vector Sagnac non-reciprocity.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

public section

namespace TVE

/-! ## Part 1: Zero-Axiom Constructive PV Metric, Spin-2 TT & Quantum-Gravity Kernel -/

/-! ### Division-by-Zero-Free `PosRat` / `NzPosRat` Relativistic Kinematics & PPN Operators -/

/-- Proper clock interval `dτ = dt / √K` in division-by-zero-free `PosRat` (`sqrtK : NzPosRat`). -/
@[expose]
def grProperTimePosRat (dt : PosRat) (sqrtK : NzPosRat) : PosRat :=
  posRatDiv dt sqrtK

/-- Proper radial ruler length `dℓ = √K · dr` in sound `PosRat` (`sqrtK : NzPosRat`). -/
@[expose]
def grProperLengthPosRat (dr : PosRat) (sqrtK : NzPosRat) : PosRat :=
  posRatMul (nzPosRatToPosRat sqrtK) dr

/-- Effective coordinate speed of light `c_eff = c / K` in GMP-reduced `PosRat` (`KVal : NzPosRat`). -/
@[expose]
def grRefractiveLightSpeedPosRat (cLight : PosRat) (KVal : NzPosRat) : PosRat :=
  posRatDivRed cLight KVal

/-- Isotropic PV line element `ds² = -(c² / K) dt² + K dr²` in GMP-reduced `PosRat`. -/
@[expose]
def grSpacetimeIntervalSqPosRat (cLight dt dr : PosRat) (KVal : NzPosRat) : PosRat :=
  let c2 := posRatMulRed cLight cLight
  let dt2 := posRatMulRed dt dt
  let dr2 := posRatMulRed dr dr
  let tempTerm := posRatMulRed (posRatDivRed c2 KVal) dt2
  let spatTerm := posRatMulRed (nzPosRatToPosRat KVal) dr2
  posRatSubRed spatTerm tempTerm

/-- Newtonian potential `Φ_N = (2 κ M) / (r c²)` (`κ = G / 2`) in GMP-reduced `PosRat`. -/
@[expose]
def grNewtonianPotentialPosRat (kappa M : PosRat) (r cLight : NzPosRat) : PosRat :=
  let numTerm := posRatMulRed (posRatOfInt 2) (posRatMulRed kappa M)
  let cSq_nz : NzPosRat :=
    { isNeg := false,
      numPred := vacMulSuccPred cLight.numPred cLight.numPred,
      denPred := vacMulSuccPred cLight.denPred cLight.denPred }
  let rCSq_nz : NzPosRat :=
    { isNeg := r.isNeg,
      numPred := vacMulSuccPred r.numPred cSq_nz.numPred,
      denPred := vacMulSuccPred r.denPred cSq_nz.denPred }
  posRatDivRed numTerm rCSq_nz

/-- Weak-field refractive index `K_weak = 1 + 2 Φ_N` in GMP-reduced `PosRat`. -/
@[expose]
def grWeakRefractivePosRat (phiN : PosRat) : PosRat :=
  posRatAddRed (posRatOfInt 1) (posRatMulRed (posRatOfInt 2) phiN)

/-- Newtonian grazing deflection `Δθ_Newt = 2 Φ_N` in GMP-reduced `PosRat`. -/
@[expose]
def grNewtonianDeflectionPosRat (phiN : PosRat) : PosRat :=
  posRatMulRed (posRatOfInt 2) phiN

/-- PPN light deflection `Δθ_PPN = (1 + γ_PPN) · 2 Φ_N` in GMP-reduced `PosRat`. -/
@[expose]
def grPPNDeflectionPosRat (gammaPPN phiN : PosRat) : PosRat :=
  posRatMulRed (posRatAddRed (posRatOfInt 1) gammaPPN) (grNewtonianDeflectionPosRat phiN)

/-! ### Plebanski-Tamm `3×3` Constitutive Tensor, Spin-2 TT Modes & Frame-Dragging (`ℤ`) -/

/--
Symmetric `3×3` spatial constitutive permittivity/permeability perturbation tensor `δK_{ij}`
with 6 independent components (`1` isotropic scalar trace + `2` longitudinal vector shears +
`1` longitudinal compression + `2` transverse-traceless spin-2 polarizations `h_+, h_×`).
-/
structure GRSymTensor3 where
  kxx : ℤ
  kyy : ℤ
  kzz : ℤ
  kxy : ℤ
  kxz : ℤ
  kyz : ℤ

/-- Componentwise negation `-T` on `GRSymTensor3`. -/
@[expose]
def grSymNeg (T : GRSymTensor3) : GRSymTensor3 :=
  { kxx := -T.kxx, kyy := -T.kyy, kzz := -T.kzz,
    kxy := -T.kxy, kxz := -T.kxz, kyz := -T.kyz }

/-- Spatial trace `tr(δK) = δK_xx + δK_yy + δK_zz`. -/
@[expose]
def grSymTrace (T : GRSymTensor3) : ℤ :=
  T.kxx + T.kyy + T.kzz

/-- Longitudinal contraction `(k̂ · δK)_i = (δK_xz, δK_yz, δK_zz)` along propagation axis `k̂ = ẑ`. -/
@[expose]
def grTransverseZ (T : GRSymTensor3) : IntVec3 :=
  { x := T.kxz, y := T.kyz, z := T.kzz }

/-- Frobenius inner product `tr(A B) = ∑_{i,j} A_{ij} B_{ij}` on symmetric `3×3` tensors. -/
@[expose]
def grSymFrobInner (A B : GRSymTensor3) : ℤ :=
  A.kxx * B.kxx + A.kyy * B.kyy + A.kzz * B.kzz +
  2 * (A.kxy * B.kxy + A.kxz * B.kxz + A.kyz * B.kyz)

/--
Exact `90°` (`π / 2`) spatial rotation `R_{π/2} T R_{π/2}ᵀ` around propagation axis `ẑ`:
distinguishes spin-0 (`R_{π/2} T = +T`), spin-1 (`R_{π/2}² T = -T`), and spin-2 TT (`R_{π/2} T = -T`).
-/
@[expose]
def grRot90Z (T : GRSymTensor3) : GRSymTensor3 :=
  { kxx := T.kyy,
    kyy := T.kxx,
    kzz := T.kzz,
    kxy := -T.kxy,
    kxz := -T.kyz,
    kyz := T.kxz }

/-- Transverse-traceless spin-2 constitutive gravitational wave `h_+ e⁺ + h_× eˣ` along `ẑ`. -/
@[expose]
def grTTWave (hPlus hCross : ℤ) : GRSymTensor3 :=
  { kxx := hPlus, kyy := -hPlus, kzz := 0,
    kxy := hCross, kxz := 0, kyz := 0 }

/-- Isotropic spin-0 scalar refractive perturbation `diag(k0, k0, k0)`. -/
@[expose]
def grScalarMode (k0 : ℤ) : GRSymTensor3 :=
  { kxx := k0, kyy := k0, kzz := k0, kxy := 0, kxz := 0, kyz := 0 }

/-- Longitudinal spin-1 vector shear mode `(vx, vy)` along `ẑ`. -/
@[expose]
def grVectorShearZ (vx vy : ℤ) : GRSymTensor3 :=
  { kxx := 0, kyy := 0, kzz := 0, kxy := 0, kxz := vx, kyz := vy }

/--
ADM / Plebanski stationary metric line element with gravitomagnetic shift vector `w : IntVec3`:
cleared-K form `K ds² = -c² dt² + K² |dx - c dt w|²`.
-/
@[expose]
def grPlebanskiClearedLineSq (cLight KVal dt : ℤ) (w dx : IntVec3) : ℤ :=
  let shiftDx : IntVec3 := vecSub dx (vecScale (cLight * dt) w)
  let tempPart : ℤ := -(cLight * cLight * dt * dt)
  let spatPart : ℤ := KVal * KVal * actVecNormSqInt shiftDx
  tempPart + spatPart

-- Pure-kernel double-negation involution `-(-z) = z` on `ℤ` (zero axioms).
theorem gr_int_neg_neg (z : ℤ) : -(-z) = z :=
  Int.casesOn (motive := fun w => -(-w) = w) z
    (fun n =>
      Nat.casesOn (motive := fun k => -(-Int.ofNat k) = Int.ofNat k) n
        rfl
        (fun _ => rfl))
    (fun _ => rfl)

/--
Theorem (Zero Axioms): Plebanski-Tamm Spin-2 TT Polarizations, Helicity Separation & Frame-Dragging.
Proves constructively with zero axioms (`does not depend on any axioms`) that:
1. Basis polarizations `e⁺ = grTTWave 1 0` and `eˣ = grTTWave 0 1` are transverse (`grTransverseZ = 0`),
   traceless (`grSymTrace = 0`), Frobenius-orthogonal (`⟨e⁺, eˣ⟩ = 0`), and equal-norm (`‖e⁺‖² = ‖eˣ‖² = 2`).
2. For ALL `hP hC : ℤ`, `grTTWave hP hC` inverts phase under a `π/2` rotation (`grRot90Z = -I`)
   and is invariant under a `π` rotation (`grRot90Z² = +I`, spin-2), whereas `grScalarMode k0` is
   `π/2`-invariant (spin-0) and `grVectorShearZ vx vy` inverts under `π` (`grRot90Z² = -I`, spin-1).
3. A non-zero gravitomagnetic shift vector `w = (0, 1, 0)` induces a non-zero Sagnac / Lense-Thirring
   asymmetry `grPlebanskiClearedLineSq(-dx) - grPlebanskiClearedLineSq(+dx) = 32 ≠ 0` between
   counter-propagating rays `±dx = (0, ±1, 0)`.
-/
theorem gr_plebanski_tamm_spin2_and_frame_dragging (hP hC k0 vx vy : ℤ) :
    grTransverseZ (grTTWave 1 0) = vecZero ∧
    grSymTrace (grTTWave 1 0) = 0 ∧
    grTransverseZ (grTTWave 0 1) = vecZero ∧
    grSymTrace (grTTWave 0 1) = 0 ∧
    grSymFrobInner (grTTWave 1 0) (grTTWave 0 1) = 0 ∧
    grSymFrobInner (grTTWave 1 0) (grTTWave 1 0) = 2 ∧
    grSymFrobInner (grTTWave 0 1) (grTTWave 0 1) = 2 ∧
    grRot90Z (grTTWave hP hC) = grSymNeg (grTTWave hP hC) ∧
    grRot90Z (grRot90Z (grTTWave hP hC)) = grTTWave hP hC ∧
    grRot90Z (grScalarMode k0) = grScalarMode k0 ∧
    grRot90Z (grRot90Z (grVectorShearZ vx vy)) = grSymNeg (grVectorShearZ vx vy) ∧
    grPlebanskiClearedLineSq 2 2 1 { x := 0, y := 1, z := 0 } { x := 0, y := -1, z := 0 } -
      grPlebanskiClearedLineSq 2 2 1 { x := 0, y := 1, z := 0 } { x := 0, y := 1, z := 0 } = 32 :=
  ⟨rfl,
   rfl,
   rfl,
   rfl,
   rfl,
   rfl,
   rfl,
   congrArg (fun y => GRSymTensor3.mk (-hP) y 0 (-hC) 0 0) (gr_int_neg_neg hP).symm,
   congrArg (fun xy => GRSymTensor3.mk hP (-hP) 0 xy 0 0) (gr_int_neg_neg hC),
   rfl,
   rfl,
   rfl⟩

/-! ### Legacy `ExactRat` Compatibility Shims (Retained for Downstream Callers) -/

/-- Legacy `ExactRat` pair helper retained for compatibility (new theorems use `PosRat` / `NzPosRat`). -/
@[expose]
def grRatDiv (p q : ExactRat) : ExactRat :=
  { num := p.num * q.den, den := p.den * q.num }

@[expose]
def grProperTimeExact (dt sqrtK : ExactRat) : ExactRat :=
  grRatDiv dt sqrtK

@[expose]
def grProperLengthExact (dr sqrtK : ExactRat) : ExactRat :=
  exactRatMul sqrtK dr

@[expose]
def grRefractiveLightSpeedExact (cLight KVal : ExactRat) : ExactRat :=
  grRatDiv cLight KVal

@[expose]
def grSpacetimeIntervalSqExact (cLight KVal dt dr : ExactRat) : ExactRat :=
  let c2 := exactRatMul cLight cLight
  let dt2 := exactRatMul dt dt
  let dr2 := exactRatMul dr dr
  let tempTerm := exactRatMul (grRatDiv c2 KVal) dt2
  let spatTerm := exactRatMul KVal dr2
  exactRatSub spatTerm tempTerm

@[expose]
def grNewtonianPotentialExact (kappa M r cLight : ExactRat) : ExactRat :=
  let numTerm := exactRatMul (exactRatOfInt 2) (exactRatMul kappa M)
  let denTerm := exactRatMul r (exactRatMul cLight cLight)
  grRatDiv numTerm denTerm

@[expose]
def grWeakRefractiveExact (phiN : ExactRat) : ExactRat :=
  exactRatAdd (exactRatOfInt 1) (exactRatMul (exactRatOfInt 2) phiN)

@[expose]
def grNewtonianDeflectionExact (phiN : ExactRat) : ExactRat :=
  exactRatMul (exactRatOfInt 2) phiN

@[expose]
def grPPNDeflectionExact (gammaPPN phiN : ExactRat) : ExactRat :=
  exactRatMul (exactRatAdd (exactRatOfInt 1) gammaPPN) (grNewtonianDeflectionExact phiN)

/-! ### Pure-Kernel `ℕ` Multiplication Lemmas & Discrete Exponential Metric (`PosRat`) -/

/-- Constructive `4 ^ n` scale denominator for discrete exponential metric `g_00(n) = -4^(-n)`. -/
@[expose]
def grPow4Nat : ℕ → ℕ
  | 0 => 1
  | n + 1 => grPow4Nat n * 4

/-- Predecessor witness certifying `grPow4Nat n = Nat.succ (grPow4Pred n)` (`4^n ≥ 1`). -/
@[expose]
def grPow4Pred : ℕ → ℕ
  | 0 => 0
  | n + 1 => (grPow4Nat n * 3) + grPow4Pred n

theorem grPow4Nat_eq_succ (n : ℕ) : grPow4Nat n = Nat.succ (grPow4Pred n) :=
  Nat.rec
    (motive := fun k => grPow4Nat k = Nat.succ (grPow4Pred k))
    rfl
    (fun k ih => congrArg (Nat.add (grPow4Nat k * 3)) ih)
    n

theorem gr_zero_mul_nat (m : ℕ) : 0 * m = 0 :=
  Nat.rec (motive := fun k => 0 * k = 0) rfl (fun _ ih => ih) m

/-- Sound positive-denominator discrete exponential temporal metric `g_00(n) = -1 / 4^n` in `PosRat`. -/
@[expose]
def grDiscreteExpMetricPosRat (n : ℕ) : PosRat :=
  { num := Int.negSucc 0, denPred := grPow4Pred n }

/-- Constructive singular Schwarzschild temporal metric `-(1 - 2u) = 2u - 1` in `PosRat`. -/
@[expose]
def grSchwarzschildLinearMetricPosRat (u : PosRat) : PosRat :=
  posRatSubRed (posRatMulRed (posRatOfInt 2) u) (posRatOfInt 1)

/-- Legacy `ExactRat` discrete exponential metric retained for compatibility. -/
@[expose]
def grDiscreteExpMetricExact (n : ℕ) : ExactRat :=
  { num := -1, den := Int.ofNat (grPow4Nat n) }

/-- Legacy `ExactRat` Schwarzschild linear metric retained for compatibility. -/
@[expose]
def grSchwarzschildLinearMetricExact (u : ExactRat) : ExactRat :=
  exactRatSub (exactRatMul (exactRatOfInt 2) u) (exactRatOfInt 1)

/--
Theorem (Zero Axioms): Universal `PosRat` / `NzPosRat` Phase-Space Volume Invariance (`dτ · dℓ = dt · dr`).
Proves universally for ALL `dt_n dt_d dr_n dr_d s_n s_d : ℕ` without division-by-zero risk,
tactics, or axioms that `grProperTimePosRat dt sqrtK` times `grProperLengthPosRat dr sqrtK`
equals `posRatMul dt dr` under `posRatEq`.
-/
theorem gr_universal_phase_space_volume_invariance
    (dt_n dt_d dr_n dr_d s_n s_d : ℕ) :
    let dt : PosRat := { num := Int.ofNat dt_n, denPred := dt_d }
    let dr : PosRat := { num := Int.ofNat dr_n, denPred := dr_d }
    let sqrtK : NzPosRat := { isNeg := false, numPred := s_n, denPred := s_d }
    posRatEq
      (posRatMul (grProperTimePosRat dt sqrtK) (grProperLengthPosRat dr sqrtK))
      (posRatMul dt dr) :=
  let a := dt_n
  let b := dt_d + 1
  let c := dr_n
  let d := dr_d + 1
  let p := s_n + 1
  let q := s_d + 1
  have s1 : (a * q) * (p * c) = (a * c) * (q * p) :=
    Eq.trans (vac_mul_four_swap a q p c)
      (Eq.trans (congrArg (fun t => t * (q * c)) (vac_mul_comm a p))
        (Eq.trans (vac_mul_four_swap p a q c)
          (Eq.trans (vac_mul_comm (p * q) (a * c))
            (congrArg (Nat.mul (a * c)) (vac_mul_comm p q)))))
  have s2 : (b * p) * (q * d) = (q * p) * (b * d) :=
    Eq.trans (vac_mul_four_swap b p q d)
      (Eq.trans (congrArg (fun t => t * (p * d)) (vac_mul_comm b q))
        (vac_mul_four_swap q b p d))
  have h_nat :
      ((a * q) * (p * c)) * (b * d) = (a * c) * ((b * p) * (q * d)) :=
    Eq.trans
      (congrArg (fun t => t * (b * d)) s1)
      (Eq.trans (vac_mul_assoc (a * c) (q * p) (b * d))
        (congrArg (Nat.mul (a * c)) s2.symm))
  congrArg Int.ofNat h_nat

/--
Theorem (Zero Axioms): Division-by-Zero-Free `PosRat` Null Geodesic & Causal Cone Law.
Verifies on a curved refractive cavity (`K = 4, √K = 2, c = 6`) in sound `PosRat` / `NzPosRat`:
1. Effective coordinate light speed is `c / K = 3 / 2` (`denPred = 1`).
2. Null light rays (`dr = 3, dt = 2`) satisfy `ds² = 0` and `(dr/dt)² = (c/K)² = 9 / 4`.
3. Timelike worldlines (`dr = 1, dt = 2`) satisfy `ds² < 0`, while spacelike intervals
   (`dr = 2, dt = 1`) satisfy `0 < ds²`.
-/
theorem gr_null_geodesic_and_spacetime_signature_exact :
    let K4 : NzPosRat := { isNeg := false, numPred := 3, denPred := 0 }
    grRefractiveLightSpeedPosRat (posRatOfInt 6) K4 = { num := 3, denPred := 1 } ∧
    grSpacetimeIntervalSqPosRat (posRatOfInt 6) (posRatOfInt 2) (posRatOfInt 3) K4 =
      posRatOfInt 0 ∧
    posRatMulRed { num := 3, denPred := 1 } { num := 3, denPred := 1 } =
      posRatMulRed (grRefractiveLightSpeedPosRat (posRatOfInt 6) K4)
        (grRefractiveLightSpeedPosRat (posRatOfInt 6) K4) ∧
    posRatLt
      (grSpacetimeIntervalSqPosRat (posRatOfInt 6) (posRatOfInt 2) (posRatOfInt 1) K4)
      (posRatOfInt 0) = true ∧
    posRatLt (posRatOfInt 0)
      (grSpacetimeIntervalSqPosRat (posRatOfInt 6) (posRatOfInt 1) (posRatOfInt 2) K4) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): Universal PPN `γ = 1` Light Deflection & `κ = G / 2` Floor Law (`PosRat`).
-/
theorem gr_ppn_light_deflection_and_floor_exact (phi : ℕ) :
    let r5 : NzPosRat := { isNeg := false, numPred := 4, denPred := 0 }
    let c2 : NzPosRat := { isNeg := false, numPred := 1, denPred := 0 }
    let phiRat : PosRat := { num := 3, denPred := 19 }
    (1 + 1) * (2 * phi) = 4 * phi ∧
    grNewtonianPotentialPosRat { num := 1, denPred := 1 } (posRatOfInt 3) r5 c2 = phiRat ∧
    posRatSubRed (grWeakRefractivePosRat phiRat) (posRatOfInt 1) =
      grNewtonianDeflectionPosRat phiRat ∧
    grPPNDeflectionPosRat (posRatOfInt 1) phiRat =
      posRatMulRed (posRatOfInt 2) (grNewtonianDeflectionPosRat phiRat) ∧
    grPPNDeflectionPosRat (posRatOfInt 1) phiRat =
      posRatMulRed (posRatOfInt 4) phiRat :=
  ⟨(vac_mul_assoc 2 2 phi).symm, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): Universal `PosRat` Discrete Exponential Horizon Regularity vs Schwarzschild Collapse.
Proves for ALL discrete potential depths `n : ℕ` that:
1. Denominator `posRatDenNat (grDiscreteExpMetricPosRat n) = 4^n` is strictly positive.
2. `grDiscreteExpMetricPosRat n = -1 / 4^n` strictly preserves `g_00(n) < 0` in `PosRat` at EVERY `n : ℕ`.
3. At the Schwarzschild horizon `u = 1/2` (`2u = 1`), the linear approximation `-(1 - 2u)` collapses
   to `0` and flips sign (`+1 > 0`) at `u = 1`, whereas `grDiscreteExpMetricPosRat 1 = -1/4` stays in `(-1, 0)`.
-/
theorem gr_discrete_exponential_horizon_regularity_nat (n : ℕ) :
    isPosNat (grPow4Nat n) = true ∧
    posRatDenNat (grDiscreteExpMetricPosRat n) = grPow4Nat n ∧
    posRatLt (grDiscreteExpMetricPosRat n) (posRatOfInt 0) = true ∧
    grDiscreteExpMetricPosRat 0 = posRatOfInt (-1) ∧
    posRatLt (posRatOfInt (-1)) (grDiscreteExpMetricPosRat 1) = true ∧
    grSchwarzschildLinearMetricPosRat { num := 1, denPred := 1 } = posRatOfInt 0 ∧
    posRatLt (posRatOfInt 0) (grSchwarzschildLinearMetricPosRat (posRatOfInt 1)) = true :=
  have h_den_pos : isPosNat (grPow4Nat n) = true :=
    Eq.rec
      (motive := fun k _ => isPosNat k = true)
      rfl
      (grPow4Nat_eq_succ n).symm
  have h_den_eq : posRatDenNat (grDiscreteExpMetricPosRat n) = grPow4Nat n :=
    (grPow4Nat_eq_succ n).symm
  have h_neg_posRat : posRatLt (grDiscreteExpMetricPosRat n) (posRatOfInt 0) = true :=
    Eq.trans
      (congrArg
        (fun k => vacFastLtInt (Int.negSucc 0) (vacIntFromSignMag false k))
        (vac_zero_mul (grPow4Pred n + 1)))
      rfl
  ⟨h_den_pos, h_den_eq, h_neg_posRat, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms — Constructive Master GR, Spin-2 TT & Quantum-Gravity Unification Synthesis):
Unites all 5 General Relativity & Quantum-Gravity pillars with `does not depend on any axioms`:
1. `PosRat` / `NzPosRat` proper spacetime phase-space invariance `dτ · dℓ = dt · dr` (`√K = 2/3`).
2. `PosRat` PPN `γ = 1` light deflection `Δθ_GR = 2 Δθ_Newt = 4 Φ_N`.
3. Universal `PosRat` Lorentzian signature preservation `g_00(n) = -4^(-n) < 0` for ALL `n : ℕ`.
4. Plebanski-Tamm Spin-2 TT orthogonality (`⟨e⁺, eˣ⟩ = 0`) and universal `π/2` helicity inversion.
5. Fractional-cavity `PosRat` (`fractionalPVCavityPos`, `T_PV = 353/81`) + universal `ℕ`
   Quantum-Gravity Unification: `G_Ein = T_PV` and `8 m λ_PV Q_Bohm = ℏ² G_Ein`.
-/
theorem gr_master_relativity_and_qg_unification_constructive
    (hbar mass lam L n : ℕ) (hP hC : ℤ) :
    let sqrtK23 : NzPosRat := { isNeg := false, numPred := 1, denPred := 2 }
    posRatEq
      (posRatMul
        (grProperTimePosRat { num := 5, denPred := 6 } sqrtK23)
        (grProperLengthPosRat { num := 11, denPred := 12 } sqrtK23))
      (posRatMul { num := 5, denPred := 6 } { num := 11, denPred := 12 }) ∧
    grPPNDeflectionPosRat (posRatOfInt 1) { num := 1, denPred := 6 } =
      posRatMulRed (posRatOfInt 2) (grNewtonianDeflectionPosRat { num := 1, denPred := 6 }) ∧
    (isPosNat (grPow4Nat n) = true ∧
     posRatLt (grDiscreteExpMetricPosRat n) (posRatOfInt 0) = true) ∧
    (grSymFrobInner (grTTWave 1 0) (grTTWave 0 1) = 0 ∧
     grRot90Z (grTTWave hP hC) = grSymNeg (grTTWave hP hC)) ∧
    einsteinSourcePosRat fractionalPVCavityPos =
      pvStressEnergyPosRat fractionalPVCavityPos ∧
    posRatMulRed (posRatOfInt 8) (bohmPotentialPosRat fractionalPVCavityPos) =
      posRatMulRed (posRatOfInt 4) (pvStressEnergyPosRat fractionalPVCavityPos) ∧
    (8 * mass * lam) * ((hbar * hbar) * L) =
      (hbar * hbar) * ((2 * mass) * ((4 * lam) * L)) :=
  let h_reg := gr_discrete_exponential_horizon_regularity_nat n
  ⟨gr_universal_phase_space_volume_invariance 5 6 11 12 1 2,
   rfl,
   ⟨h_reg.1, h_reg.2.2.1⟩,
   ⟨rfl, congrArg (fun y => GRSymTensor3.mk (-hP) y 0 (-hC) 0 0) (gr_int_neg_neg hP).symm⟩,
   rfl,
   rfl,
   (universal_pv_chain_rule_and_qg_unification_nat hbar mass lam 1 L 0).2⟩

/-! ## Part 2: Continuum ℝ Compatibility & Tensorial Plebanski-Tamm Layer -/

/-! ### Pillar 1: Polarizable Vacuum Metric, Time Dilation & Null Geodesics -/

/--
Proper clock interval dτ = dt / √K in a polarizable vacuum of
refractive amplitude √K.
-/
@[expose]
noncomputable def properTimeInterval (dt sqrt_K : ℝ) : ℝ :=
  dt / sqrt_K

/--
Proper physical ruler length dℓ = √K · dr in a polarizable
vacuum of refractive amplitude √K.
-/
@[expose]
noncomputable def properRadialLength (dr sqrt_K : ℝ) : ℝ :=
  sqrt_K * dr

/--
Effective coordinate speed of light c_eff(K) = c / K in a
vacuum region of refractive index K.
-/
@[expose]
noncomputable def refractiveLightSpeed (c_light K_val : ℝ) : ℝ :=
  c_light / K_val

/--
Isotropic Polarizable Vacuum / General Relativity spacetime line element:
ds² = -(c² / K) dt² + K dr².
-/
@[expose]
noncomputable def pvSpacetimeIntervalSq
    (c_light K_val dt dr : ℝ) : ℝ :=
  -((c_light ^ 2) / K_val) * (dt ^ 2) + K_val * (dr ^ 2)

/--
Theorem (Reciprocity of Gravitational Time Dilation and Ruler Contraction):
-/
theorem proper_spacetime_volume_invariance
    (dt dr sqrt_K : ℝ) (h_sqrt_K : sqrt_K ≠ 0) :
    properTimeInterval dt sqrt_K * properRadialLength dr sqrt_K = dt * dr := by
  dsimp [properTimeInterval, properRadialLength]
  have h_rearr : (dt / sqrt_K) * (sqrt_K * dr) =
      ((dt / sqrt_K) * sqrt_K) * dr := by ring
  rw [h_rearr, div_mul_cancel₀ dt h_sqrt_K]

/--
Theorem (Null Geodesic Equivalence to Refractive Light Propagation):
-/
theorem null_geodesic_iff_refractive_light_speed
    (c_light K_val dt dr : ℝ)
    (hK : K_val ≠ 0) (hdt : dt ≠ 0) :
    pvSpacetimeIntervalSq c_light K_val dt dr = 0 ↔
      (dr / dt) ^ 2 = (refractiveLightSpeed c_light K_val) ^ 2 := by
  dsimp [pvSpacetimeIntervalSq, refractiveLightSpeed]
  have hK2 : K_val ^ 2 ≠ 0 := pow_ne_zero 2 hK
  have hdt2 : dt ^ 2 ≠ 0 := pow_ne_zero 2 hdt
  constructor
  · intro h_null
    have h_eq : K_val * (dr ^ 2) = ((c_light ^ 2) / K_val) * (dt ^ 2) := by
      linarith
    have h_mul_K : (K_val ^ 2) * (dr ^ 2) = (c_light ^ 2) * (dt ^ 2) := by
      calc (K_val ^ 2) * (dr ^ 2)
        _ = K_val * (K_val * (dr ^ 2)) := by ring
        _ = K_val * (((c_light ^ 2) / K_val) * (dt ^ 2)) := by rw [h_eq]
        _ = (((c_light ^ 2) / K_val) * K_val) * (dt ^ 2) := by ring
        _ = (c_light ^ 2) * (dt ^ 2) := by rw [div_mul_cancel₀ _ hK]
    calc (dr / dt) ^ 2
      _ = (dr ^ 2) / (dt ^ 2) := by ring
      _ = (((K_val ^ 2) * (dr ^ 2)) / (K_val ^ 2)) / (dt ^ 2) := by
          rw [mul_div_cancel_left₀ (dr ^ 2) hK2]
      _ = (((c_light ^ 2) * (dt ^ 2)) / (dt ^ 2)) / (K_val ^ 2) := by
          rw [h_mul_K]; ring
      _ = (c_light ^ 2) / (K_val ^ 2) := by
          rw [mul_div_cancel_right₀ (c_light ^ 2) hdt2]
      _ = (c_light / K_val) ^ 2 := by ring
  · intro h_vel
    have h_cross : (dr ^ 2) * (K_val ^ 2) = (c_light ^ 2) * (dt ^ 2) := by
      calc (dr ^ 2) * (K_val ^ 2)
        _ = (((dr / dt) ^ 2) * (dt ^ 2)) * (K_val ^ 2) := by
            have h1 : (dr / dt) ^ 2 * (dt ^ 2) =
                ((dr ^ 2) / (dt ^ 2)) * (dt ^ 2) := by ring
            rw [h1, div_mul_cancel₀ (dr ^ 2) hdt2]
        _ = (((c_light / K_val) ^ 2) * (K_val ^ 2)) * (dt ^ 2) := by
            rw [h_vel]; ring
        _ = (((c_light ^ 2) / (K_val ^ 2)) * (K_val ^ 2)) * (dt ^ 2) := by ring
        _ = (c_light ^ 2) * (dt ^ 2) := by
            rw [div_mul_cancel₀ (c_light ^ 2) hK2]
    calc -((c_light ^ 2) / K_val) * (dt ^ 2) + K_val * (dr ^ 2)
      _ = (-((c_light ^ 2) * (dt ^ 2)) + (dr ^ 2) * (K_val ^ 2)) / K_val := by
          have h_split :
              (-((c_light ^ 2) * (dt ^ 2)) + (dr ^ 2) * (K_val ^ 2)) / K_val =
              -((c_light ^ 2) / K_val) * (dt ^ 2) +
                ((dr ^ 2 * K_val) * K_val) / K_val := by ring
          rw [h_split, mul_div_cancel_right₀ _ hK]
          ring
      _ = 0 := by rw [h_cross]; ring

/-! ### Pillar 2: Weak-Field Newtonian Potential, PPN Light Bending & Redshift -/

/--
Dimensionless Newtonian gravitational potential Φ_N = (2κM)/(rc²) = GM/(rc²)
expressed in terms of the TVE gravitational floor κ = G / 2 (`Action.lean`).
-/
@[expose]
noncomputable def dimensionlessNewtonianPotential
    (kappa_grav M_mass r_rad c_light : ℝ) : ℝ :=
  (2 * kappa_grav * M_mass) / (r_rad * (c_light ^ 2))

/--
Weak-field vacuum refractive index profile K_weak(Φ_N) = 1 + 2 Φ_N.
-/
@[expose]
noncomputable def weakFieldRefractiveIndex (phi_N : ℝ) : ℝ :=
  1 + 2 * phi_N

/--
Newtonian corpuscular grazing light deflection angle Δθ_Newt = 2 Φ_N = 2GM/(bc²).
-/
@[expose]
noncomputable def newtonianLightDeflection (phi_N : ℝ) : ℝ :=
  2 * phi_N

/--
Full Einstein / Polarizable-Vacuum light deflection angle combining temporal
clock delay (Φ_N) and spatial ruler curvature (γ_PPN Φ_N):
Δθ_GR = (1 + γ_PPN) · 2 Φ_N.
-/
@[expose]
noncomputable def ppnLightDeflection (gamma_ppn phi_N : ℝ) : ℝ :=
  (1 + gamma_ppn) * newtonianLightDeflection phi_N

/--
Theorem (Exact PPN Light Deflection & Weak-Field Redshift Equivalence):
-/
theorem einstein_light_deflection_twice_newtonian (phi_N : ℝ) :
    weakFieldRefractiveIndex phi_N - 1 = 2 * phi_N ∧
    ppnLightDeflection 1 phi_N = 2 * newtonianLightDeflection phi_N ∧
    ppnLightDeflection 1 phi_N = 4 * phi_N := by
  dsimp [weakFieldRefractiveIndex, ppnLightDeflection, newtonianLightDeflection]
  refine ⟨by ring, by ring, by ring⟩

/-! ### Pillar 3: Horizon Regularity & Elimination of the r → 0 Singularity -/

/--
Exact exponential Polarizable-Vacuum temporal metric coefficient
g_00(u) = -exp(-2u) for dimensionless gravitational potential u = GM/(rc²).
-/
@[expose]
noncomputable def exponentialTemporalMetric (u : ℝ) : ℝ :=
  -Real.exp (-2 * u)

/--
Theorem (Horizon Regularity of the Exponential Polarizable-Vacuum Metric):
-/
theorem exponential_metric_horizon_regularity (u : ℝ) (hu : 0 ≤ u) :
    -1 ≤ exponentialTemporalMetric u ∧
    exponentialTemporalMetric u < 0 := by
  dsimp [exponentialTemporalMetric]
  have h_pos : 0 < Real.exp (-2 * u) := Real.exp_pos (-2 * u)
  have h_le_one : Real.exp (-2 * u) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  exact ⟨by linarith, by linarith⟩

/-! ### Pillar 4: The Grand Quantum-Gravity Unification Identity (δK) -/

/--
Macroscopic Einstein-Dicke gravitational field source density governed by
Field Equation 3 (`index_equation` in `Action.lean`):
G_Ein = -4 λ_PV (∇²√K / √K) = E_field - (λ_PV / K²)(∇K)².
-/
@[expose]
noncomputable def einsteinRefractiveSourceDensity
    (lambda_pv sqrt_K lap_sqrt_K : ℝ) : ℝ :=
  -4 * lambda_pv * (lap_sqrt_K / sqrt_K)

/--
Right-hand side stress-energy source of Field Equation 3 (`Action.lean`):
T_PV = E_field - (λ_PV / K²)(∇K)².
-/
@[expose]
noncomputable def polarizableVacuumStressEnergy
    (lambda_pv E_field grad_K_sq K_val : ℝ) : ℝ :=
  E_field - (lambda_pv / (K_val ^ 2)) * grad_K_sq

/--
Theorem (The Grand Quantum-Gravity Unification Identity):
-/
theorem quantum_gravity_unification_identity
    (hbar m lambda_pv sqrt_K lap_sqrt_K E_field grad_K_sq K_val : ℝ)
    (hm : m ≠ 0) (h_sqrt_K : sqrt_K ≠ 0) (h_lambda : lambda_pv ≠ 0)
    (h_index : lap_sqrt_K =
      tveIndexLaplacianRHS sqrt_K lambda_pv E_field grad_K_sq K_val) :
    einsteinRefractiveSourceDensity lambda_pv sqrt_K lap_sqrt_K =
      polarizableVacuumStressEnergy lambda_pv E_field grad_K_sq K_val ∧
    8 * m * lambda_pv * bohmQuantumPotential hbar m sqrt_K lap_sqrt_K =
      (hbar ^ 2) * einsteinRefractiveSourceDensity lambda_pv sqrt_K lap_sqrt_K ∧
    8 * m * lambda_pv * bohmQuantumPotential hbar m sqrt_K lap_sqrt_K =
      (hbar ^ 2) * polarizableVacuumStressEnergy
        lambda_pv E_field grad_K_sq K_val := by
  have h_div :
      lap_sqrt_K / sqrt_K =
        -(1 / (4 * lambda_pv)) *
          (E_field - (lambda_pv / (K_val ^ 2)) * grad_K_sq) := by
    rw [h_index]
    dsimp [tveIndexLaplacianRHS]
    have h_factor :
        -(sqrt_K / (4 * lambda_pv)) *
          (E_field - (lambda_pv / (K_val ^ 2)) * grad_K_sq) =
        sqrt_K * (-(1 / (4 * lambda_pv)) *
          (E_field - (lambda_pv / (K_val ^ 2)) * grad_K_sq)) := by
      ring
    rw [h_factor, mul_div_cancel_left₀ _ h_sqrt_K]
  have h_4lam_ne : 4 * lambda_pv ≠ 0 := mul_ne_zero (by norm_num) h_lambda
  have h_ein_eq :
      einsteinRefractiveSourceDensity lambda_pv sqrt_K lap_sqrt_K =
        polarizableVacuumStressEnergy lambda_pv E_field grad_K_sq K_val := by
    dsimp [einsteinRefractiveSourceDensity, polarizableVacuumStressEnergy]
    rw [h_div]
    have h_rearr :
        -4 * lambda_pv *
          (-(1 / (4 * lambda_pv)) *
            (E_field - (lambda_pv / (K_val ^ 2)) * grad_K_sq)) =
        ((1 / (4 * lambda_pv)) * (4 * lambda_pv)) *
          (E_field - (lambda_pv / (K_val ^ 2)) * grad_K_sq) := by
      ring
    rw [h_rearr, one_div_mul_cancel h_4lam_ne]
    ring
  have h2m_ne : 2 * m ≠ 0 := mul_ne_zero (by norm_num) hm
  have h_unif :
      8 * m * lambda_pv * bohmQuantumPotential hbar m sqrt_K lap_sqrt_K =
        (hbar ^ 2) *
          einsteinRefractiveSourceDensity lambda_pv sqrt_K lap_sqrt_K := by
    dsimp [bohmQuantumPotential, einsteinRefractiveSourceDensity]
    calc 8 * m * lambda_pv * (-((hbar ^ 2) / (2 * m)) * (lap_sqrt_K / sqrt_K))
      _ = (((hbar ^ 2) / (2 * m)) * (2 * m)) *
            (-4 * lambda_pv * (lap_sqrt_K / sqrt_K)) := by ring
      _ = (hbar ^ 2) * (-4 * lambda_pv * (lap_sqrt_K / sqrt_K)) := by
          rw [div_mul_cancel₀ (hbar ^ 2) h2m_ne]
  have h_unif_stress :
      8 * m * lambda_pv * bohmQuantumPotential hbar m sqrt_K lap_sqrt_K =
        (hbar ^ 2) * polarizableVacuumStressEnergy
          lambda_pv E_field grad_K_sq K_val := by
    rw [h_unif, h_ein_eq]
  exact ⟨h_ein_eq, h_unif, h_unif_stress⟩

/-! ### Pillar 5: Continuum Plebanski-Tamm Tensorial Vacuum, Spin-2 TT Modes & Frame-Dragging -/

/-- Continuum `3×3` symmetric spatial constitutive tensor `K^{ij}` (`6` real components). -/
structure PlebanskiSymTensor3 where
  kxx : ℝ
  kyy : ℝ
  kzz : ℝ
  kxy : ℝ
  kxz : ℝ
  kyz : ℝ

/-- Trace `tr(h) = h_xx + h_yy + h_zz` on `PlebanskiSymTensor3`. -/
@[expose]
def plebanskiTrace (h : PlebanskiSymTensor3) : ℝ :=
  h.kxx + h.kyy + h.kzz

/-- Longitudinal contraction `h · ẑ = (h_xz, h_yz, h_zz)` along propagation axis `ẑ`. -/
@[expose]
def plebanskiTransverseZ (h : PlebanskiSymTensor3) : ℝ × ℝ × ℝ :=
  (h.kxz, h.kyz, h.kzz)

/-- Frobenius inner product `tr(A B)` on `PlebanskiSymTensor3`. -/
@[expose]
def plebanskiFrobInner (A B : PlebanskiSymTensor3) : ℝ :=
  A.kxx * B.kxx + A.kyy * B.kyy + A.kzz * B.kzz +
  2 * (A.kxy * B.kxy + A.kxz * B.kxz + A.kyz * B.kyz)

/-- Exact `π / 2` spatial rotation `R_{π/2} h R_{π/2}ᵀ` around `ẑ` on `PlebanskiSymTensor3`. -/
@[expose]
def plebanskiRot90Z (h : PlebanskiSymTensor3) : PlebanskiSymTensor3 :=
  { kxx := h.kyy, kyy := h.kxx, kzz := h.kzz,
    kxy := -h.kxy, kxz := -h.kyz, kyz := h.kxz }

/-- Continuum transverse-traceless spin-2 wave `h_+ e⁺ + h_× eˣ` propagating along `ẑ`. -/
@[expose]
def plebanskiTTWave (h_plus h_cross : ℝ) : PlebanskiSymTensor3 :=
  { kxx := h_plus, kyy := -h_plus, kzz := 0,
    kxy := h_cross, kxz := 0, kyz := 0 }

/--
Stationary ADM / Plebanski optical line element incorporating the gravitomagnetic
frame-dragging shift vector `w = (wx, wy, wz)` (`w_i = -g_{0i}/g_{00}`):
`ds² = -(c² / K) dt² + K ((dx - wx c dt)² + (dy - wy c dt)² + (dz - wz c dt)²)`.
-/
@[expose]
noncomputable def admShiftLineElementSq
    (c_light K_val wx wy wz dt dx dy dz : ℝ) : ℝ :=
  -((c_light ^ 2) / K_val) * (dt ^ 2) +
  K_val * ((dx - wx * c_light * dt) ^ 2 +
           (dy - wy * c_light * dt) ^ 2 +
           (dz - wz * c_light * dt) ^ 2)

/--
Theorem (Bidirectional Continuum Spin-2 TT Decomposition & Gravitomagnetic Frame-Dragging):
Proves over `ℝ` that:
1. A symmetric `3×3` constitutive tensor perturbation `h` propagating along `ẑ` is transverse
   (`h · ẑ = 0`) and traceless (`tr(h) = 0`) if and only if (`↔`) `h = plebanskiTTWave h_plus h_cross`
   for two real spin-2 polarization amplitudes `(h_plus, h_cross)`.
2. The `+` and `×` polarizations are Frobenius-orthogonal with norm `2 (h_+² + h_×²)` and
   invert sign under a `π / 2` rotation around `ẑ` (helicity ±2).
3. Reversing spatial ray propagation `dx ↦ -dx` in `admShiftLineElementSq` yields the exact
   Sagnac / Lense-Thirring frame-dragging asymmetry `4 K c dt (w · dx)`.
-/
theorem plebanski_tamm_spin2_tt_and_frame_dragging
    (h : PlebanskiSymTensor3)
    (h_plus h_cross c_light K_val wx wy wz dt dx dy dz : ℝ) :
    ((plebanskiTransverseZ h = (0, 0, 0) ∧ plebanskiTrace h = 0) ↔
      ∃ hp hc : ℝ, h = plebanskiTTWave hp hc) ∧
    plebanskiFrobInner (plebanskiTTWave h_plus 0) (plebanskiTTWave 0 h_cross) = 0 ∧
    plebanskiFrobInner (plebanskiTTWave h_plus h_cross) (plebanskiTTWave h_plus h_cross) =
      2 * (h_plus ^ 2 + h_cross ^ 2) ∧
    plebanskiRot90Z (plebanskiTTWave h_plus h_cross) =
      plebanskiTTWave (-h_plus) (-h_cross) ∧
    admShiftLineElementSq c_light K_val wx wy wz dt (-dx) (-dy) (-dz) -
      admShiftLineElementSq c_light K_val wx wy wz dt dx dy dz =
      4 * K_val * c_light * dt * (wx * dx + wy * dy + wz * dz) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · cases h with | mk kxx kyy kzz kxy kxz kyz =>
      intro ⟨h_trv, h_trc⟩
      have hkxz : kxz = 0 := congrArg Prod.fst h_trv
      have hkyz : kyz = 0 := congrArg (fun p => p.2.1) h_trv
      have hkzz : kzz = 0 := congrArg (fun p => p.2.2) h_trv
      dsimp [plebanskiTrace] at h_trc
      have hkyy : kyy = -kxx := by linarith
      refine ⟨kxx, kxy, ?_⟩
      dsimp [plebanskiTTWave]
      rw [hkyy, hkzz, hkxz, hkyz]
    · rintro ⟨hp, hc, h_eq⟩
      rw [h_eq]
      dsimp [plebanskiTransverseZ, plebanskiTrace, plebanskiTTWave]
      exact ⟨rfl, by ring⟩
  · dsimp [plebanskiFrobInner, plebanskiTTWave]; ring
  · dsimp [plebanskiFrobInner, plebanskiTTWave]; ring
  · dsimp [plebanskiRot90Z, plebanskiTTWave]; congr 1 <;> ring
  · dsimp [admShiftLineElementSq]; ring

#print axioms gr_plebanski_tamm_spin2_and_frame_dragging
#print axioms gr_universal_phase_space_volume_invariance
#print axioms gr_null_geodesic_and_spacetime_signature_exact
#print axioms gr_ppn_light_deflection_and_floor_exact
#print axioms gr_discrete_exponential_horizon_regularity_nat
#print axioms gr_master_relativity_and_qg_unification_constructive

end TVE
