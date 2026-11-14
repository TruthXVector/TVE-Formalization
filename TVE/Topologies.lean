/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import TVE.Vacuum
public import TVE.Action

/-!
# Topological Vacuum Electrodynamics — Flux-Tube Topologies

Constructive zero-axiom formalization of quantized torus-knot and link
topologies, positive-denominator `PosRat` aspect ratios, Seifert genus,
Calugareanu-White-Fuller magnetic helicity superselection, winding-to-Steiner
trace duality, and reconciled bag-pressure (`a⁴ = ξ / P_bag`) vs. linear-tension
(`a² = ξ / σ`) radial confinement bounds, paired with the locked real-valued
`FluxTube` interface for downstream modules.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-! ## Part 1: Zero-Axiom Constructive Knot & Link Topology Kernel -/

/--
Constructive integer representation of a closed Beltrami flux-tube topology
on the TVE vacuum sheet, carrying strictly positive aspect denominator
`aspectDenPred + 1 ≥ 1` for division-by-zero-free `PosRat` invariants.
-/
structure TopologicalTube where
  /-- Toroidal winding number \(p\) around the major cycle. -/
  toroidalWinding : ℤ
  /-- Poloidal winding number \(q\) around the minor core. -/
  poloidalWinding : ℤ
  /-- Numerator \(p_U\) of the equilibrium aspect ratio \(U = R / a\). -/
  aspectNum : ℤ
  /-- Denominator \(q_U\) of the equilibrium aspect ratio \(U = R / a\). -/
  aspectDen : ℤ
  /-- Predecessor `q_U - 1` guaranteeing strictly positive denominator `aspectDenPred + 1 ≥ 1`. -/
  aspectDenPred : ℕ
  /-- 3D self-linking / crossing writhe \(\mathrm{Wr}\). -/
  writhe : ℤ
  /-- Internal ribbon twist \(\mathrm{Tw}\). -/
  twist : ℤ
  /-- Pairwise component linking contribution \(2\,\mathrm{Lk}\). -/
  linkingSum : ℤ
  /-- Radial Beltrami Bessel-wall generation index \(n\). -/
  radialWallIndex : ℕ
  /-- Number of closed flux-tube components. -/
  componentCount : ℕ

/-- Integer aspect ratio \(U = p_U / q_U\) for integer-ratio topologies. -/
@[expose]
def aspectRatioInt (t : TopologicalTube) : ℤ :=
  t.aspectNum / t.aspectDen

/-- Sound positive-denominator rational aspect ratio \(U = p_U / (q_{\mathrm{pred}} + 1)\) in `PosRat`. -/
@[expose]
def aspectRatioPosRat (t : TopologicalTube) : PosRat :=
  { num := t.aspectNum, denPred := t.aspectDenPred }

/-- Legacy `ExactRat` aspect ratio retained for staged downstream compatibility. -/
@[expose]
def aspectRatioExact (t : TopologicalTube) : ExactRat :=
  { num := t.aspectNum, den := t.aspectDen }

/--
Calugareanu-White-Fuller quantized total magnetic helicity:
\(h_{\mathrm{total}} = \mathrm{Wr} + \mathrm{Tw} + 2\,\mathrm{Lk}\).
-/
@[expose]
def totalHelicityInt (t : TopologicalTube) : ℤ :=
  t.writhe + t.twist + t.linkingSum

/-- Twice the Seifert surface genus \(2g = (p - 1)(q - 1)\) of a \((p, q)\) torus knot. -/
@[expose]
def seifertDoubleGenus (t : TopologicalTube) : ℤ :=
  (t.toroidalWinding - 1) * (t.poloidalWinding - 1)

/-- Seifert surface genus \(g = (p - 1)(q - 1) / 2\) of a \((p, q)\) torus knot. -/
@[expose]
def seifertGenusInt (t : TopologicalTube) : ℤ :=
  seifertDoubleGenus t / 2

/-- Sound positive-denominator Seifert genus \((p - 1)(q - 1) / 2\) in `PosRat` (`den = 2 ≥ 1`). -/
@[expose]
def seifertGenusPosRat (t : TopologicalTube) : PosRat :=
  posRatReduce { num := seifertDoubleGenus t, denPred := 1 }

/-- Legacy `ExactRat` Seifert genus retained for staged downstream compatibility. -/
@[expose]
def seifertGenusExact (t : TopologicalTube) : ExactRat :=
  { num := seifertDoubleGenus t, den := 2 }

/-- Primary torus-knot braid crossing invariant \(p(q - 1)\). -/
@[expose]
def torusCrossingPrimary (t : TopologicalTube) : ℤ :=
  t.toroidalWinding * (t.poloidalWinding - 1)

/-- Dual poloidal braid crossing invariant \(q(p - 1)\). -/
@[expose]
def torusCrossingDual (t : TopologicalTube) : ℤ :=
  t.poloidalWinding * (t.toroidalWinding - 1)

/-- 1D filament tangent winding norm \(I_{\mathrm{fil}} = p^2 + q^2\). -/
@[expose]
def filamentNormInt (t : TopologicalTube) : ℤ :=
  t.toroidalWinding * t.toroidalWinding +
  t.poloidalWinding * t.poloidalWinding

/-- 2D surface helicity measure \(I_{\mathrm{surf}} = 2pq\). -/
@[expose]
def surfaceMeasureInt (t : TopologicalTube) : ℤ :=
  2 * t.toroidalWinding * t.poloidalWinding

/-- Winding anisotropy defect \(I_{\mathrm{fil}} - I_{\mathrm{surf}}\). -/
@[expose]
def windingAnisotropyInt (t : TopologicalTube) : ℤ :=
  filamentNormInt t - surfaceMeasureInt t

/-- Projects a `TopologicalTube` onto its helicity `ZPFSheet` (`Vacuum.lean`). -/
@[expose]
def helicitySheetOf (t : TopologicalTube) : ZPFSheet :=
  { aspectNum := t.aspectNum,
    aspectDen := t.aspectDen,
    helicity := totalHelicityInt t }

/-- Projects a `TopologicalTube` onto its writhe `ZPFSheet` (`Vacuum.lean`). -/
@[expose]
def writheSheetOf (t : TopologicalTube) : ZPFSheet :=
  { aspectNum := t.aspectNum,
    aspectDen := t.aspectDen,
    helicity := t.writhe }

/--
Outward magnetic helicity pressure \(P_{\mathrm{mag}} = \xi / a^4\) in sound `PosRat`
for strictly positive minor radius `a = aPred + 1 ≥ 1`.
-/
@[expose]
def helicityPressurePosRat (xi aPred : ℕ) : PosRat :=
  let a := aPred + 1
  let a4 := a * a * a * a
  posRatFromSignMagReduced false xi (a4 - 1)

/--
Inward cross-sectional linear-tension stress \(P_{\mathrm{lin}} = \sigma / a^2\) in sound `PosRat`
for reduced 1D string tension \(\sigma = P_{\mathrm{bag}} a_{\mathrm{eq}}^2\) (`a = aPred + 1 ≥ 1`),
reconciling \(P_{\mathrm{mag}} = P_{\mathrm{bag}} \iff a_{\mathrm{eq}}^4 = \xi / P_{\mathrm{bag}}\)
with \(P_{\mathrm{mag}} = \sigma / a_{\mathrm{eq}}^2 \iff a_{\mathrm{eq}}^2 = \xi / \sigma\).
-/
@[expose]
def linearTensionPressurePosRat (sigmaLin aPred : ℕ) : PosRat :=
  let a := aPred + 1
  let a2 := a * a
  posRatFromSignMagReduced false sigmaLin (a2 - 1)

/--
Radial cross-sectional tube energy \((\xi + P_{\mathrm{bag}} a^4) / a^2\) in sound `PosRat`
for strictly positive minor radius `a = aPred + 1 ≥ 1`.
-/
@[expose]
def radialTubeEnergyPosRat (xi pBag aPred : ℕ) : PosRat :=
  let a := aPred + 1
  let a2 := a * a
  let a4 := a2 * a2
  posRatFromSignMagReduced false (xi + pBag * a4) (a2 - 1)

/-- Legacy `ExactRat` outward helicity pressure retained for compatibility. -/
@[expose]
def helicityPressureExact (xi a : ℤ) : ExactRat :=
  { num := xi, den := a * a * a * a }

/-- Legacy `ExactRat` radial tube energy retained for compatibility. -/
@[expose]
def radialTubeEnergyExact (xi sigma a : ℤ) : ExactRat :=
  { num := xi + sigma * a * a * a * a, den := a * a }

/-- Constructive lepton radial wall family (\(n\)-th Bessel wall on the \((1,1)\) unknot). -/
@[expose]
def radialWallTubeInt (n : ℕ) : TopologicalTube :=
  { toroidalWinding := 1,
    poloidalWinding := 1,
    aspectNum := 2,
    aspectDen := 1,
    aspectDenPred := 0,
    writhe := 0,
    twist := 1,
    linkingSum := 0,
    radialWallIndex := n,
    componentCount := 1 }

/-- Ground-state electron unknot (\(n = 1, U = 2, h = 1\)). -/
@[expose]
def electronTubeInt : TopologicalTube := radialWallTubeInt 1

/-- Muon topology as the second radial wall (\(n = 2\)). -/
@[expose]
def muonTubeInt : TopologicalTube := radialWallTubeInt 2

/-- Tau topology as the third radial wall (\(n = 3\)). -/
@[expose]
def tauTubeInt : TopologicalTube := radialWallTubeInt 3

/-- Relaxed \(T_{3,2}\) proton trefoil (\(p = 3, q = 2, U_{\mathrm{eq}} = 2/3, \mathrm{Wr} = 3\)). -/
@[expose]
def protonTrefoilTubeInt : TopologicalTube :=
  { toroidalWinding := 3,
    poloidalWinding := 2,
    aspectNum := 2,
    aspectDen := 3,
    aspectDenPred := 2,
    writhe := 3,
    twist := -2,
    linkingSum := 0,
    radialWallIndex := 1,
    componentCount := 1 }

/-- Pion Hopf link (2-component link with \(\mathrm{Wr} = 2\) and zero net global helicity). -/
@[expose]
def pionHopfTubeInt : TopologicalTube :=
  { toroidalWinding := 1,
    poloidalWinding := 1,
    aspectNum := 1,
    aspectDen := 1,
    aspectDenPred := 0,
    writhe := 2,
    twist := 0,
    linkingSum := -2,
    radialWallIndex := 1,
    componentCount := 2 }

/-- Planar neutrino loop shed at topological rupture (\(\mathrm{Wr} = 0, h = 0\)). -/
@[expose]
def neutrinoLoopTubeInt : TopologicalTube :=
  { toroidalWinding := 1,
    poloidalWinding := 0,
    aspectNum := 1,
    aspectDen := 1,
    aspectDenPred := 0,
    writhe := 0,
    twist := 0,
    linkingSum := 0,
    radialWallIndex := 1,
    componentCount := 1 }

/-- Kernel-level proposition `n = 0` (`True` at `0`, `False` at `n + 1`). -/
@[expose]
def topIsZeroNatProp (n : ℕ) : Prop :=
  Nat.casesOn (motive := fun _ => Prop) n True (fun _ => False)

/-- Pure kernel discriminator proving `(0 : ℕ) ≠ 1` with zero axioms. -/
theorem top_zero_ne_one_nat (h : (0 : ℕ) = 1) : False :=
  Eq.mp (congrArg topIsZeroNatProp h) trivial

/--
Theorem (Zero Axioms): Ground-State Electron Unknot Topological Invariants.
Proves by pure kernel reduction (`rfl`) with positive-denominator `PosRat` and
zero-remainder certificates that `electronTubeInt` has exact aspect ratio `2 / 1`,
unit magnetic helicity `1`, Seifert genus `0`, isotropic Hopf winding, and projects
onto `unknotSheet`.
-/
theorem electron_unknot_constructive_invariants :
    aspectRatioInt electronTubeInt = 2 ∧
    electronTubeInt.aspectDen * aspectRatioInt electronTubeInt =
      electronTubeInt.aspectNum ∧
    aspectRatioPosRat electronTubeInt = posRatOfInt 2 ∧
    seifertGenusPosRat electronTubeInt = posRatOfInt 0 ∧
    exactRatEq (aspectRatioExact electronTubeInt) { num := 2, den := 1 } ∧
    totalHelicityInt electronTubeInt = 1 ∧
    seifertGenusInt electronTubeInt = 0 ∧
    2 * seifertGenusInt electronTubeInt = seifertDoubleGenus electronTubeInt ∧
    windingAnisotropyInt electronTubeInt = 0 ∧
    helicitySheetOf electronTubeInt = unknotSheet :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): Lepton Generation Radial-Wall Hierarchy.
Proves for every wall index `n : ℕ` that `radialWallTubeInt n` preserves exact
`PosRat` aspect ratio `2 / 1` and unit helicity `1`, recovering electron, muon, and tau.
-/
theorem lepton_radial_wall_hierarchy (n : ℕ) :
    (radialWallTubeInt n).radialWallIndex = n ∧
    aspectRatioInt (radialWallTubeInt n) = 2 ∧
    aspectRatioPosRat (radialWallTubeInt n) = posRatOfInt 2 ∧
    exactRatEq (aspectRatioExact (radialWallTubeInt n)) { num := 2, den := 1 } ∧
    totalHelicityInt (radialWallTubeInt n) = 1 ∧
    radialWallTubeInt 1 = electronTubeInt ∧
    radialWallTubeInt 2 = muonTubeInt ∧
    radialWallTubeInt 3 = tauTubeInt :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): Proton \(T_{3,2}\) Trefoil Knot & Exact `PosRat` Invariants.
Proves by pure kernel reduction (`rfl`) that `protonTrefoilTubeInt` has exact
`PosRat` aspect ratio `2 / 3` (`denPred = 2`), writhe `3`, unit net helicity `1`,
exact `PosRat` Seifert genus `1 / 1`, and braid crossings `(3, 4)` summing to `7`.
-/
theorem proton_trefoil_constructive_invariants :
    aspectRatioPosRat protonTrefoilTubeInt = { num := 2, denPred := 2 } ∧
    seifertGenusPosRat protonTrefoilTubeInt = posRatOfInt 1 ∧
    exactRatEq (aspectRatioExact protonTrefoilTubeInt) { num := 2, den := 3 } ∧
    protonTrefoilTubeInt.writhe = 3 ∧
    totalHelicityInt protonTrefoilTubeInt = 1 ∧
    seifertGenusInt protonTrefoilTubeInt = 1 ∧
    2 * seifertGenusInt protonTrefoilTubeInt =
      seifertDoubleGenus protonTrefoilTubeInt ∧
    torusCrossingPrimary protonTrefoilTubeInt = 3 ∧
    torusCrossingDual protonTrefoilTubeInt = 4 ∧
    torusCrossingPrimary protonTrefoilTubeInt +
      torusCrossingDual protonTrefoilTubeInt =
      sphereKernelTrace trefoilEquilibriumSheet ∧
    writheSheetOf protonTrefoilTubeInt = trefoilEquilibriumSheet :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): Unknot-Trefoil Winding & Steiner-Trace Duality.
Proves that the \((3,2)\) trefoil winding invariants \((I_{\mathrm{fil}}, I_{\mathrm{surf}}) = (13, 12)\)
match the 3D sphere-kernel trace and 2D surface stiffness weight of `unknotSheet` in `Vacuum.lean`,
with unit chiral knot anisotropy \(I_{\mathrm{fil}} - I_{\mathrm{surf}} = 1\).
-/
theorem unknot_trefoil_winding_trace_duality :
    filamentNormInt protonTrefoilTubeInt = 13 ∧
    surfaceMeasureInt protonTrefoilTubeInt = 12 ∧
    filamentNormInt protonTrefoilTubeInt = sphereKernelTrace unknotSheet ∧
    surfaceMeasureInt protonTrefoilTubeInt = surfaceStiffnessWeight unknotSheet ∧
    windingAnisotropyInt protonTrefoilTubeInt = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): Global Helicity Neutrality of the Pion Hopf Link and Neutrino Loop.
-/
theorem meson_and_neutrino_helicity_neutrality :
    pionHopfTubeInt.componentCount = 2 ∧
    pionHopfTubeInt.writhe = 2 ∧
    totalHelicityInt pionHopfTubeInt = 0 ∧
    neutrinoLoopTubeInt.writhe = 0 ∧
    totalHelicityInt neutrinoLoopTubeInt = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms — Topological Helicity Superselection & `PosRat` Confinement):
Proves with division-by-zero-free `PosRat` arithmetic (`a = aPred + 1 ≥ 1`) that:
1. Universal Superselection: Any knotted/twisted tube with `totalHelicityInt t1 ≠ 0` cannot
   undergo a helicity-conserving transition into a trivial `totalHelicityInt t2 = 0` sector.
2. Lepton & Baryon Stability: `electronTubeInt` and `protonTrefoilTubeInt` are topologically
   distinct from `neutrinoLoopTubeInt` and `pionHopfTubeInt`.
3. Reconciled Bag & Linear-Tension Confinement (`ξ = 16, P_bag = 1, σ = P_bag a_eq² = 4`):
   - Stretched (`a = 3`, `aPred = 2`): `0 < 16/81 < 4/9 < 1`.
   - Equilibrium (`a = 2`, `aPred = 1`): `P_mag = 16/16 = 1 = P_bag = 4/4 = σ/a_eq²`.
   - Compressed (`a = 1`, `aPred = 0`): `1 < 4/1 < 16/1`.
   - Radial energy achieves its strict minimum at `a = 2` (`8 < 17` and `8 < 97/9`).
-/
theorem helicity_confinement :
    (∀ t1 t2 : TopologicalTube,
      totalHelicityInt t1 ≠ 0 →
      totalHelicityInt t2 = 0 →
      totalHelicityInt t1 ≠ totalHelicityInt t2 ∧ t1 ≠ t2) ∧
    totalHelicityInt electronTubeInt ≠ 0 ∧
    totalHelicityInt protonTrefoilTubeInt ≠ 0 ∧
    electronTubeInt ≠ neutrinoLoopTubeInt ∧
    protonTrefoilTubeInt ≠ neutrinoLoopTubeInt ∧
    protonTrefoilTubeInt ≠ pionHopfTubeInt ∧
    helicityPressurePosRat 16 2 = { num := 16, denPred := 80 } ∧
    posRatLt (posRatOfInt 0) (helicityPressurePosRat 16 2) = true ∧
    posRatLt (helicityPressurePosRat 16 2) (linearTensionPressurePosRat 4 2) = true ∧
    posRatLt (linearTensionPressurePosRat 4 2) (posRatOfInt 1) = true ∧
    helicityPressurePosRat 16 1 = posRatOfInt 1 ∧
    linearTensionPressurePosRat 4 1 = posRatOfInt 1 ∧
    posRatLt (posRatOfInt 1) (linearTensionPressurePosRat 4 0) = true ∧
    posRatLt (linearTensionPressurePosRat 4 0) (helicityPressurePosRat 16 0) = true ∧
    posRatLt (radialTubeEnergyPosRat 16 1 1) (radialTubeEnergyPosRat 16 1 0) = true ∧
    posRatLt (radialTubeEnergyPosRat 16 1 1) (radialTubeEnergyPosRat 16 1 2) = true :=
  ⟨fun t1 t2 h_nz h_z =>
    ⟨fun h_eq_h => h_nz (Eq.trans h_eq_h h_z),
     fun h_eq_t => h_nz (Eq.trans (congrArg totalHelicityInt h_eq_t) h_z)⟩,
   fun h => top_zero_ne_one_nat (congrArg Int.toNat h).symm,
   fun h => top_zero_ne_one_nat (congrArg Int.toNat h).symm,
   fun h => top_zero_ne_one_nat (congrArg (fun t => (totalHelicityInt t).toNat) h).symm,
   fun h => top_zero_ne_one_nat (congrArg (fun t => (totalHelicityInt t).toNat) h).symm,
   fun h => top_zero_ne_one_nat (congrArg (fun t => (totalHelicityInt t).toNat) h).symm,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: Downstream Real-Valued Compatibility Layer (Interface-Locked) -/

/-- A formal representation of a Miller-Turner force-free flux tube configuration. -/
structure FluxTube where
  majorRadius : ℝ
  tubeMinorRadius : ℝ
  writhe : ℤ
  magneticHelicity : ℝ
  radialWallIndex : ℕ

/-- Aspect ratio \(U = R / a\). -/
@[expose]
noncomputable def aspectRatio (t : FluxTube) : ℝ :=
  t.majorRadius / t.tubeMinorRadius

/-- The ground-state electron unknot (\(n=1\), \(U=2\)). -/
@[expose]
noncomputable def electronUnknot (a : ℝ) : FluxTube :=
  { majorRadius := 2 * a,
    tubeMinorRadius := a,
    writhe := 0,
    magneticHelicity := 1,
    radialWallIndex := 1 }

/-- Theorem: The electron baseline rigorously yields an aspect ratio of 2. -/
theorem electron_aspect_ratio (a : ℝ) (ha : a ≠ 0) :
    aspectRatio (electronUnknot a) = 2 := by
  dsimp [aspectRatio, electronUnknot]
  exact mul_div_cancel_right₀ 2 ha

/-- Higher radial walls of the same unknot topology. -/
@[expose]
noncomputable def radialWall (n : ℕ) (a : ℝ) : FluxTube :=
  { majorRadius := 2 * a,
    tubeMinorRadius := a,
    writhe := 0,
    magneticHelicity := 1,
    radialWallIndex := n }

/-- Muon is defined strictly as the second radial wall (\(n=2\)). -/
@[expose]
noncomputable def muon (a : ℝ) : FluxTube := radialWall 2 a

theorem muon_is_second_wall (a : ℝ) : radialWall 2 a = muon a := rfl

/-- Tau is defined strictly as the third radial wall (\(n=3\)). -/
@[expose]
noncomputable def tau (a : ℝ) : FluxTube := radialWall 3 a

theorem tau_is_third_wall (a : ℝ) : radialWall 3 a = tau a := rfl

/-- The proton as the \(T_{3,2}\) trefoil. -/
@[expose]
noncomputable def protonTrefoil (a R : ℝ) : FluxTube :=
  { majorRadius := R,
    tubeMinorRadius := a,
    writhe := 3,
    magneticHelicity := 1,
    radialWallIndex := 1 }

/-- Theorem: The writhe of the proton trefoil evaluates exactly to 3. -/
theorem trefoil_writhe_eq (a R : ℝ) : (protonTrefoil a R).writhe = 3 := rfl

/-- The pion as the Hopf link (modeled as a composite topology). -/
@[expose]
noncomputable def pionHopfLink (a R : ℝ) : FluxTube :=
  { majorRadius := R,
    tubeMinorRadius := a,
    writhe := 2,
    magneticHelicity := 0,
    radialWallIndex := 1 }

/-- The neutrino as the planar loop shed at rupture. -/
@[expose]
noncomputable def neutrinoPlanarLoop (a R : ℝ) : FluxTube :=
  { majorRadius := R,
    tubeMinorRadius := a,
    writhe := 0,
    magneticHelicity := 0,
    radialWallIndex := 1 }

#print axioms electron_unknot_constructive_invariants
#print axioms lepton_radial_wall_hierarchy
#print axioms proton_trefoil_constructive_invariants
#print axioms unknot_trefoil_winding_trace_duality
#print axioms meson_and_neutrino_helicity_neutrality
#print axioms helicity_confinement

end TVE
