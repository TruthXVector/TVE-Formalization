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
public import TVE.CondensedMatter.CobaltFerromagnetism
public import TVE.Superconductivity.HopfPairing
public import TVE.Superconductivity.Quasi2DResolvent

/-!
# Topological Vacuum Electrodynamics — Unconventional Cuprate, Pnictide & Nickelate Domes

Parameter-free `T_c` certifications (`TVE.Superconductivity.UnconventionalDomes`) across
layered `3d` Mott-superexchange families, importing `HopfPairing`, `Quasi2DResolvent`,
and `CobaltFerromagnetism`:

1. **Multilayer Cuprate `T_c(L)` Peak at `L = 3` & `L = 4` Turnover (`[]`):**
   Evaluates `T_c(L) = T_{3d}(4) / W_L` across `L = 1, 2, 3`, certifying
   `T_c(1) ∈ (94.5, 94.6) K` (Hg-1201 `~94–97 K`), `T_c(2) ∈ (124.5, 124.6) K`
   (Hg-1212 `~127 K`), `T_c^outer(3) ∈ (134.5, 134.6) K` and 3-plane mean
   `(129.9, 130.0) K` (Hg-1223 `~133–135 K`), Jensen-trace `L = 4` underdoping
   turnover `T_c^scr(4) < 122 K < T_c(3)` alongside 4th-derivative Steiner vanishing,
   and the 3D close-packed pressure ceiling `T_c^pack ∈ (172.4, 172.6) K`
   (bounding compressed Hg-1223 `~164 K`).
2. **Tetrahedral Iron Pnictides (`4/9`) & Bilayer Nickelates (`2/3`) (`[]`):**
   Applies the Cauchy–Schwarz `[111]` `t_{2g}`-to-`e_g` crystal-field ratio `4 / 9`
   to certify `T_c^pnic(1) ∈ (42.0, 42.1) K` (pressed La-1111 `~43 K`) and optimal
   `T_c^pnic(2) ∈ (55.3, 55.4) K` (Sm-1111 `~55–56 K`), and applies the `2 / 3`
   octahedral `d_{3z²-r²}` share to certify pressurized bilayer `La₃Ni₂O₇` inside
   `(83.0, 83.1) K` (observed `~80–83 K`).
3. **Continuum Multilayer Ordering, `L = 4` Radical Cancellation & Phase Flip (`ℝ`):**
   Proves strict `T_c` ordering from `W_3 < W_2 < W_1`, exact `√2`-cancellation in
   the `L = 4` optical trace `((2 - √2) + 2 + (2 + √2)) / 36 = 1 / 6`, and the
   Bethe–Slater ferromagnetic-to-singlet crossover.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-! ## Part 1: Zero-Axiom Cuprate, Pnictide & Nickelate `T_c` Kernel (`[]`) -/

/--
`L = 4` convex Jensen lower bound on `W_4`:
Because the 3 non-zero tridiagonal eigenvalues `(2 - √2, 2, 2 + √2)` have exact mean
gap `((2 - √2) + 2 + (2 + √2)) / (3 × 12) = 1 / 6` and `G_{2D}(δ)` is strictly convex,
`G_{2D}(δ_2) + G_{2D}(δ_3) + G_{2D}(δ_4) > 3 G_{2D}(1/6)`, certifying a radical-free
lower bound on `W_4` (`ln(32 · 4 · A_eff(4)) = 14 ln 2 + ln(A_eff(4)/128)`).
-/
@[expose]
def scWLayer4JensenLoPosRat : PosRat :=
  let lnY4 := scPosRatAddRed (posRatMulRed (posRatOfInt 14) scLn2LoPosRat) scLnAeffOver128Lo
  let wQ2d4 := posRatDivRed lnY4 vpPiConvHiNz
  let threeG16 := posRatMulRed (posRatOfInt 3) scG2dOneSixthLoPosRat
  posRatMulRed { num := 1, denPred := 3 } (scPosRatAddRed wQ2d4 threeG16)

/--
Theorem (Zero Axioms): Parameter-Free Unconventional `T_c` Hierarchy Across Cuprates
(`L = 1, 2, 3, 4` + 3D Pressure Ceiling), Iron Pnictides (`4/9`), and Bilayer `La₃Ni₂O₇` (`2/3`).
-/
theorem sc_unconventional_cuprate_pnictide_nickelate_domes :
    let T3d_4_L := scExchangeT3dKelvinPosRat 510998950 scAlphaInv4HiNz
    let T3d_4_U := scExchangeT3dKelvinPosRat 510998952 scAlphaInv4LoNz
    let Tc_cuprate_1_L := posRatDivRed T3d_4_L (vpPosRatToNzOrOne scWLayer1HiPosRat)
    let Tc_cuprate_1_U := posRatDivRed T3d_4_U (vpPosRatToNzOrOne scWLayer1LoPosRat)
    let Tc_cuprate_2_L := posRatDivRed T3d_4_L (vpPosRatToNzOrOne scWLayer2HiPosRat)
    let Tc_cuprate_2_U := posRatDivRed T3d_4_U (vpPosRatToNzOrOne scWLayer2LoPosRat)
    let Tc_cuprate_3_ideal_L := posRatDivRed T3d_4_L (vpPosRatToNzOrOne scWLayer3HiPosRat)
    let Tc_cuprate_3_ideal_U := posRatDivRed T3d_4_U (vpPosRatToNzOrOne scWLayer3LoPosRat)
    let D_out := scPreslandTallonDomePosRat { num := 18, denPred := 99 }
    let D_3avg : PosRat := { num := 113, denPred := 120 }
    let Tc_cuprate_3_out_L := posRatMulRed D_out Tc_cuprate_3_ideal_L
    let Tc_cuprate_3_out_U := posRatMulRed D_out Tc_cuprate_3_ideal_U
    let Tc_cuprate_3_avg_L := posRatMulRed D_3avg Tc_cuprate_3_ideal_L
    let Tc_cuprate_3_avg_U := posRatMulRed D_3avg Tc_cuprate_3_ideal_U
    let D_4layer := scPreslandTallonDomePosRat { num := 21, denPred := 99 }
    let Tc_cuprate_4_ideal_U := posRatDivRed T3d_4_U (vpPosRatToNzOrOne scWLayer4JensenLoPosRat)
    let Tc_cuprate_4_scr_U := posRatMulRed D_4layer Tc_cuprate_4_ideal_U
    let Tc_3d_packed_L := posRatMulRed T3d_4_L coPackOverWatsonLoPosRat
    let Tc_3d_packed_U := posRatMulRed T3d_4_U coPackOverWatsonHiPosRat
    let Tc_3d_unpacked_L := posRatDivRed T3d_4_L (vpPosRatToNzOrOne coWatsonFccHiPosRat)
    let Tc_3d_unpacked_U := posRatDivRed T3d_4_U (vpPosRatToNzOrOne coWatsonFccLoPosRat)
    let pnic_ratio : PosRat := { num := 4, denPred := 8 }
    let ni2o7_share : PosRat := { num := 2, denPred := 2 }
    let Tc_pnic_1_L := posRatMulRed pnic_ratio Tc_cuprate_1_L
    let Tc_pnic_1_U := posRatMulRed pnic_ratio Tc_cuprate_1_U
    let Tc_pnic_2_L := posRatMulRed pnic_ratio Tc_cuprate_2_L
    let Tc_pnic_2_U := posRatMulRed pnic_ratio Tc_cuprate_2_U
    let Tc_ni2o7_L := posRatMulRed ni2o7_share Tc_cuprate_2_L
    let Tc_ni2o7_U := posRatMulRed ni2o7_share Tc_cuprate_2_U
    posRatLt { num := 945, denPred := 9 } Tc_cuprate_1_L = true ∧
    posRatLt Tc_cuprate_1_U { num := 946, denPred := 9 } = true ∧
    posRatLt { num := 1245, denPred := 9 } Tc_cuprate_2_L = true ∧
    posRatLt Tc_cuprate_2_U { num := 1246, denPred := 9 } = true ∧
    posRatLt { num := 1391, denPred := 9 } Tc_cuprate_3_ideal_L = true ∧
    posRatLt Tc_cuprate_3_ideal_U { num := 1392, denPred := 9 } = true ∧
    posRatLt { num := 1345, denPred := 9 } Tc_cuprate_3_out_L = true ∧
    posRatLt Tc_cuprate_3_out_U { num := 1346, denPred := 9 } = true ∧
    posRatLt { num := 1299, denPred := 9 } Tc_cuprate_3_avg_L = true ∧
    posRatLt Tc_cuprate_3_avg_U (posRatOfInt 130) = true ∧
    D_4layer = { num := 96, denPred := 120 } ∧
    posRatLt Tc_cuprate_4_scr_U (posRatOfInt 122) = true ∧
    posRatLt Tc_cuprate_4_scr_U Tc_cuprate_3_avg_L = true ∧
    specSteinerFourthDerivWeight unknotSheet = 0 ∧
    posRatLt { num := 1724, denPred := 9 } Tc_3d_packed_L = true ∧
    posRatLt Tc_3d_packed_U { num := 1726, denPred := 9 } = true ∧
    posRatLt { num := 1877, denPred := 9 } Tc_3d_unpacked_L = true ∧
    posRatLt Tc_3d_unpacked_U { num := 1879, denPred := 9 } = true ∧
    posRatLt (posRatOfInt 42) Tc_pnic_1_L = true ∧
    posRatLt Tc_pnic_1_U { num := 421, denPred := 9 } = true ∧
    posRatLt { num := 553, denPred := 9 } Tc_pnic_2_L = true ∧
    posRatLt Tc_pnic_2_U { num := 554, denPred := 9 } = true ∧
    posRatLt (posRatOfInt 83) Tc_ni2o7_L = true ∧
    posRatLt Tc_ni2o7_U { num := 831, denPred := 9 } = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: Continuum `ℝ` Multilayer Monotonicity, `L = 4` Trace & Crossover Laws -/

private theorem sc_div_strict_anti
    (T w_small w_big : ℝ)
    (hT : 0 < T) (hs : 0 < w_small) (hlt : w_small < w_big) :
    T / w_big < T / w_small := by
  have hb : 0 < w_big := lt_trans hs hlt
  have hq1 : (T / w_small) * w_small = T := div_mul_cancel₀ T (ne_of_gt hs)
  have hq2 : (T / w_big) * w_big = T := div_mul_cancel₀ T (ne_of_gt hb)
  have h_id :
      ((T / w_small) - (T / w_big)) * (w_small * w_big) =
        ((T / w_small) * w_small) * w_big - ((T / w_big) * w_big) * w_small := by
    ring
  rw [hq1, hq2] at h_id
  have h_rhs : 0 < T * w_big - T * w_small := by
    have hp : 0 < T * (w_big - w_small) := mul_pos hT (by linarith)
    linarith [show T * w_big - T * w_small = T * (w_big - w_small) by ring]
  have h_den : 0 < w_small * w_big := mul_pos hs hb
  by_contra h_not
  have h_np : ((T / w_small) - (T / w_big)) * (w_small * w_big) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt h_den)
  linarith

/--
Theorem (Continuum `ℝ`): Multilayer Phase-Stiffening Ordering & `L = 4` Radical Cancellation.
1. Whenever `0 < T3d_4` and `0 < W3 < W2 < W1`, `T3d_4 / W1 < T3d_4 / W2 < T3d_4 / W3`.
2. On the `L = 4` open tridiagonal block (`λ ∈ {2 - s2, 2, 2 + s2}`), `s2 = √2` cancels
   identically in the mean optical gap `((2 - s2)/12 + 2/12 + (2 + s2)/12) / 3 = 1 / 6`.
3. Under `p_ave = 0.16` two-shell charge imbalance `(p_out, p_in) = (0.21, 0.11)`, both
   shells evaluate identically to `96 / 121` on the Presland–Tallon dome.
-/
theorem continuum_multilayer_phase_stiffening_and_l4_jensen_trace
    (T3d_4 W1 W2 W3 s2 : ℝ)
    (hT : 0 < T3d_4) (hW3 : 0 < W3) (h32 : W3 < W2) (h21 : W2 < W1) :
    let hW2 : 0 < W2 := lt_trans hW3 h32
    T3d_4 / W1 < T3d_4 / W2 ∧
    T3d_4 / W2 < T3d_4 / W3 ∧
    (((2 - s2) / 12 + (2 : ℝ) / 12 + (2 + s2) / 12) / 3 = (1 / 6 : ℝ)) ∧
    ((21 / 100 : ℝ) + (11 / 100 : ℝ)) / 2 = (4 / 25 : ℝ) ∧
    1 - (10000 / 121 : ℝ) * ((21 / 100 : ℝ) - (4 / 25 : ℝ)) ^ 2 = (96 / 121 : ℝ) ∧
    1 - (10000 / 121 : ℝ) * ((11 / 100 : ℝ) - (4 / 25 : ℝ)) ^ 2 = (96 / 121 : ℝ) := by
  have hW2 : 0 < W2 := lt_trans hW3 h32
  exact ⟨sc_div_strict_anti T3d_4 W2 W1 hT hW2 h21,
         sc_div_strict_anti T3d_4 W3 W2 hT hW3 h32,
         by ring, by ring, by ring, by ring⟩

/--
Theorem (Continuum `ℝ`): Bethe–Slater Singlet Crossover & Crystal-Field Family Ordering.
1. Core-axial overlap dominance (`B_phi² < B_z²`) makes the antiparallel `s = -1` Hopf
   singlet strictly lower in energy than the `s = +1` ferromagnetic state.
2. For any `0 < Tc_bilayer`, the tetrahedral `[111]` pnictide (`4/9`), octahedral apical
   bilayer nickelate (`2/3`), and planar `[100]` bilayer cuprate (`1`) satisfy the strict
   hierarchy `(4 / 9) Tc_bilayer < (2 / 3) Tc_bilayer < Tc_bilayer`.
-/
theorem continuum_bethe_slater_pnictide_nickelate_crossover
    (B_phi B_z Tc_bilayer : ℝ)
    (h_core : B_phi ^ 2 < B_z ^ 2) (hTc : 0 < Tc_bilayer) :
    let E_pair := fun s : ℝ => (B_z + s * B_z) ^ 2 + (B_phi - s * B_phi) ^ 2
    E_pair (-1) < E_pair 1 ∧
    (4 / 9 : ℝ) * Tc_bilayer < (2 / 3 : ℝ) * Tc_bilayer ∧
    (2 / 3 : ℝ) * Tc_bilayer < Tc_bilayer := by
  have h_bs :
      ((B_z + (-1 : ℝ) * B_z) ^ 2 + (B_phi - (-1 : ℝ) * B_phi) ^ 2) -
        ((B_z + (1 : ℝ) * B_z) ^ 2 + (B_phi - (1 : ℝ) * B_phi) ^ 2) =
      4 * (B_phi ^ 2 - B_z ^ 2) := by
    ring
  refine ⟨by linarith, by linarith, by linarith⟩

#print axioms sc_unconventional_cuprate_pnictide_nickelate_domes

end TVE
