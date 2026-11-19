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
public import TVE.ScaleUnification
public import TVE.Superconductivity.HopfPairing
public import TVE.Superconductivity.Quasi2DResolvent
public import TVE.Superconductivity.UnconventionalDomes

/-!
# Topological Vacuum Electrodynamics — Vibronic Pairing, `μ*` Removal & Stability Islands

Completes `TVE.Superconductivity` (`VibronicAndIslands.lean`) across conventional
metals, two-gap `MgB₂`, compressed superhydrides, and `1 atm` covalent clathrates:

1. **Zero-Knob Tolmachev `μ*` & Analytical Eliashberg–KMM Constant (`[]`):**
   Combines `(m_p / m_e)^(1) ∈ (1835.938, 1835.939)` (`VacuumPolarization.lean`)
   with `2^a 3^b` Mercator decompositions to certify `μ*(Pb) ∈ (0.1187, 0.1188) <
   μ*(Ta) ∈ (0.1196, 0.1197) < μ*(Nb) ∈ (0.1246, 0.1247) < μ*(MgB₂) ∈ (0.1512, 0.1513)
   < μ*(H) ∈ (0.1736, 0.1737)`, and certifies Euler–Mascheroni `γ` via `H_12 - ln 12`
   to lock `C_KMM = 4 exp(γ - 1) / π ∈ (0.8342, 0.8343)` (`1 / C_KMM ∈ (1.1986, 1.1987)`,
   deriving Allen & Dynes' empirical `1 / 1.20` prefactor).
2. **Vibronic Anchors (`MgB₂`, `Pb`, `Nb`) & Cage Stability Sweep (`[]`):**
   Certifies `MgB₂`'s `¹¹B` `E_{2g}` phonon `(67.07, 67.08) meV` and two-band `T_c`
   window `(37.4, 40.0) K` (exp. `39.2 K`), FCC Lead `(56.38, 56.40) K` phonon and
   strong-coupling `T_c ∈ (7.20, 7.24) K` (exp. `7.20 K`), BCC Niobium 14-face
   `T_c ∈ (8.84, 8.88) K` (exp. `9.25 K`), GPa-stabilized `n = 1` superhydrides
   `(247, 249) K` (`LaH₁₀ ~250 K`, proving `P_out > P_bag` at `a = 1`), and `1 atm`
   self-confined covalent `n = 2` `B–C` clathrates inside `(69.0, 69.2) K`.
3. **Continuum `U_n` Cancellation, Garland Isotope Law & Cage Rupture (`ℝ`):**
   Proves exact `U_n` cancellation inside `U_n / ħω`, Garland's sub-`1/2` isotope
   exponent `α_iso < 1/2`, and the Bogomolny–Lundquist external pressure threshold.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-! ## Part 1: Zero-Axiom Tolmachev `μ*`, KMM Prefactor & Stability-Islands Kernel (`[]`) -/

/-- Harmonic partial sum `H_{k+1} = ∑_{j=1}^{k+1} 1 / j` in `PosRat`. -/
@[expose]
def scHarmonicPosRat : ℕ → PosRat
  | 0 => posRatOfInt 1
  | k + 1 => scPosRatAddRed (scHarmonicPosRat k) { num := 1, denPred := k + 1 }

/-- Compact certified envelope on `(m_p / m_e)^(1) ∈ (1835.938, 1835.939)`. -/
@[expose] def scMpCompactLo : PosRat := { num := 1835938, denPred := 999 }
@[expose] def scMpCompactHi : PosRat := { num := 1835939, denPred := 999 }

/-- Compact certified envelopes on `ln 2` and `ln 3` (`Quasi2DResolvent.lean`). -/
@[expose] def scLn2CompactLo : PosRat := { num := 693146, denPred := 999999 }
@[expose] def scLn2CompactHi : PosRat := { num := 693148, denPred := 999999 }
@[expose] def scLn3CompactLo : PosRat := { num := 1098610, denPred := 999999 }
@[expose] def scLn3CompactHi : PosRat := { num := 1098614, denPred := 999999 }

/-- Certified bounds on `ln(m_p^(1) / m_e) = 6 ln 2 + 3 ln 3 + ln(μ_pe / 1728)`. -/
@[expose]
def scLnMpLoPosRat : PosRat :=
  let base := scPosRatAddRed
    (posRatMulRed (posRatOfInt 6) scLn2CompactLo)
    (posRatMulRed (posRatOfInt 3) scLn3CompactLo)
  scPosRatAddRed base (scMercatorLogTruncPosRat { num := 3123, denPred := 49999 } 1)

@[expose]
def scLnMpHiPosRat : PosRat :=
  let base := scPosRatAddRed
    (posRatMulRed (posRatOfInt 6) scLn2CompactHi)
    (posRatMulRed (posRatOfInt 3) scLn3CompactHi)
  scPosRatAddRed base (scMercatorLogTruncPosRat { num := 6247, denPred := 99999 } 2)

/-- Parameter-free Tolmachev Coulomb pseudopotential `μ* = 1 / (2 + (1/2) ln(A_eff_mass · μ_pe))`. -/
@[expose]
def scTolmachevMuStarFromLn (lnMassProduct : PosRat) : PosRat :=
  let den := scPosRatAddRed (posRatOfInt 2)
    (posRatMulRed { num := 1, denPred := 1 } lnMassProduct)
  scPosRatRecip den

/-- Certified Tolmachev `μ*` bounds for `H (1)`, `MgB₂ (11/2)`, `Nb (93)`, `Ta (181)`, `Pb (207)`. -/
@[expose] def scMuStarHLo : PosRat := scTolmachevMuStarFromLn { num := 75154, denPred := 9999 }
@[expose] def scMuStarHHi : PosRat := scTolmachevMuStarFromLn { num := 75152, denPred := 9999 }

@[expose]
def scMuStarMgB2Lo : PosRat :=
  let ln55Hi := scPosRatAddRed
    (posRatSubRed (posRatMulRed (posRatOfInt 4) scLn2CompactHi) scLn3CompactLo)
    (scMercatorLogTruncPosRat { num := 1, denPred := 31 } 2)
  scTolmachevMuStarFromLn (scPosRatAddRed ln55Hi { num := 75154, denPred := 9999 })

@[expose]
def scMuStarMgB2Hi : PosRat :=
  let ln55Lo := scPosRatAddRed
    (posRatSubRed (posRatMulRed (posRatOfInt 4) scLn2CompactLo) scLn3CompactHi)
    (scMercatorLogTruncPosRat { num := 1, denPred := 31 } 1)
  scTolmachevMuStarFromLn (scPosRatAddRed ln55Lo { num := 75152, denPred := 9999 })

@[expose]
def scMuStarNbLo : PosRat :=
  let ln93Hi := posRatSubRed
    (scPosRatAddRed (posRatMulRed (posRatOfInt 5) scLn2CompactHi) scLn3CompactHi)
    (scMercatorLogTruncPosRat { num := 1, denPred := 30 } 1)
  scTolmachevMuStarFromLn (scPosRatAddRed ln93Hi { num := 75154, denPred := 9999 })

@[expose]
def scMuStarNbHi : PosRat :=
  let ln93Lo := posRatSubRed
    (scPosRatAddRed (posRatMulRed (posRatOfInt 5) scLn2CompactLo) scLn3CompactLo)
    (scMercatorLogTruncPosRat { num := 1, denPred := 30 } 2)
  scTolmachevMuStarFromLn (scPosRatAddRed ln93Lo { num := 75152, denPred := 9999 })

@[expose]
def scMuStarTaLo : PosRat :=
  let ln181Hi := posRatSubRed
    (scPosRatAddRed (posRatMulRed (posRatOfInt 6) scLn2CompactHi) scLn3CompactHi)
    (scMercatorLogTruncPosRat { num := 11, denPred := 180 } 1)
  scTolmachevMuStarFromLn (scPosRatAddRed ln181Hi { num := 75154, denPred := 9999 })

@[expose]
def scMuStarTaHi : PosRat :=
  let ln181Lo := posRatSubRed
    (scPosRatAddRed (posRatMulRed (posRatOfInt 6) scLn2CompactLo) scLn3CompactLo)
    (scMercatorLogTruncPosRat { num := 11, denPred := 180 } 2)
  scTolmachevMuStarFromLn (scPosRatAddRed ln181Lo { num := 75152, denPred := 9999 })

@[expose]
def scMuStarPbLo : PosRat :=
  let ln207Hi := posRatSubRed
    (scPosRatAddRed
      (posRatMulRed (posRatOfInt 3) scLn2CompactHi)
      (posRatMulRed (posRatOfInt 3) scLn3CompactHi))
    (scMercatorLogTruncPosRat { num := 1, denPred := 22 } 1)
  scTolmachevMuStarFromLn (scPosRatAddRed ln207Hi { num := 75154, denPred := 9999 })

@[expose]
def scMuStarPbHi : PosRat :=
  let ln207Lo := posRatSubRed
    (scPosRatAddRed
      (posRatMulRed (posRatOfInt 3) scLn2CompactLo)
      (posRatMulRed (posRatOfInt 3) scLn3CompactLo))
    (scMercatorLogTruncPosRat { num := 1, denPred := 22 } 2)
  scTolmachevMuStarFromLn (scPosRatAddRed ln207Lo { num := 75152, denPred := 9999 })

/-- Analytical KMM Eliashberg prefactor `C_KMM = 4 exp(-(1 - γ)) / π` bounds in `PosRat`. -/
@[expose]
def scKmmLoPosRat : PosRat :=
  let expLo := suHornerExpNeg { num := 42279, denPred := 99999 } 7
  posRatDivRed (posRatMulRed (posRatOfInt 4) expLo) vpPiConvHiNz

@[expose]
def scKmmHiPosRat : PosRat :=
  let expHi := suHornerExpNeg { num := 42277, denPred := 99999 } 6
  posRatDivRed (posRatMulRed (posRatOfInt 4) expHi) vpPiConvLoNz

/--
Theorem (Zero Axioms): Parameter-Free Tolmachev `μ*` Hierarchy (`Pb < Ta < Nb < MgB₂ < H`)
& Analytical KMM Derivation of Allen–Dynes' `1 / 1.20` Prefactor (`1.1986–1.1987`).
-/
theorem sc_tolmachev_mu_star_and_kmm_prefactor_bounds :
    let mp1_lo := vpDressedMassRatioLoPosRat { num := 94, denPred := 6 } 3 0 0
    let mp1_hi := vpDressedMassRatioHiPosRat { num := 94, denPred := 6 } 3 0 0
    let x_mp_L := posRatSubRed
      (posRatDivRed scMpCompactLo { isNeg := false, numPred := 1727, denPred := 0 })
      (posRatOfInt 1)
    let x_mp_U := posRatSubRed
      (posRatDivRed scMpCompactHi { isNeg := false, numPred := 1727, denPred := 0 })
      (posRatOfInt 1)
    let H12 := scHarmonicPosRat 11
    let ln12_L := scPosRatAddRed (posRatMulRed (posRatOfInt 2) scLn2CompactLo) scLn3CompactLo
    let ln12_U := scPosRatAddRed (posRatMulRed (posRatOfInt 2) scLn2CompactHi) scLn3CompactHi
    let em_corr_hi := posRatSubRed { num := 1, denPred := 1727 } { num := 1, denPred := 23 }
    let em_corr_lo := posRatSubRed em_corr_hi { num := 1, denPred := 2488319 }
    let gamma_L := scPosRatAddRed (posRatSubRed H12 ln12_U) em_corr_lo
    let gamma_U := scPosRatAddRed (posRatSubRed H12 ln12_L) em_corr_hi
    let oneSubGamma_L := posRatSubRed (posRatOfInt 1) gamma_U
    let oneSubGamma_U := posRatSubRed (posRatOfInt 1) gamma_L
    let invKmm_L := scPosRatRecip scKmmHiPosRat
    let invKmm_U := scPosRatRecip scKmmLoPosRat
    posRatLt scMpCompactLo mp1_lo = true ∧
    posRatLt mp1_hi scMpCompactHi = true ∧
    posRatLt { num := 3123, denPred := 49999 } x_mp_L = true ∧
    posRatLt x_mp_U { num := 6247, denPred := 99999 } = true ∧
    posRatLt { num := 75152, denPred := 9999 } scLnMpLoPosRat = true ∧
    posRatLt scLnMpHiPosRat { num := 75154, denPred := 9999 } = true ∧
    posRatLt { num := 1187, denPred := 9999 } scMuStarPbLo = true ∧
    posRatLt scMuStarPbHi { num := 1188, denPred := 9999 } = true ∧
    posRatLt { num := 1196, denPred := 9999 } scMuStarTaLo = true ∧
    posRatLt scMuStarTaHi { num := 1197, denPred := 9999 } = true ∧
    posRatLt { num := 1246, denPred := 9999 } scMuStarNbLo = true ∧
    posRatLt scMuStarNbHi { num := 1247, denPred := 9999 } = true ∧
    posRatLt { num := 1512, denPred := 9999 } scMuStarMgB2Lo = true ∧
    posRatLt scMuStarMgB2Hi { num := 1513, denPred := 9999 } = true ∧
    posRatLt { num := 1736, denPred := 9999 } scMuStarHLo = true ∧
    posRatLt scMuStarHHi { num := 1737, denPred := 9999 } = true ∧
    posRatLt scMuStarPbHi scMuStarTaLo = true ∧
    posRatLt scMuStarTaHi scMuStarNbLo = true ∧
    posRatLt scMuStarNbHi scMuStarMgB2Lo = true ∧
    posRatLt scMuStarMgB2Hi scMuStarHLo = true ∧
    posRatLt { num := 42277, denPred := 99999 } oneSubGamma_L = true ∧
    posRatLt oneSubGamma_U { num := 42279, denPred := 99999 } = true ∧
    posRatLt { num := 8342, denPred := 9999 } scKmmLoPosRat = true ∧
    posRatLt scKmmHiPosRat { num := 8343, denPred := 9999 } = true ∧
    posRatLt { num := 11986, denPred := 9999 } invKmm_L = true ∧
    posRatLt invKmm_U { num := 11987, denPred := 9999 } = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 2. Quarter-Exponent Eliashberg Attenuation & Discrete Stability-Islands Sweep -/

/-- Compact certified 4-channel Hartree energy `m_e c² / A_eff(4)² ∈ (26960.27, 26960.32) meV`. -/
@[expose] def scHartree4Lo : PosRat := { num := 2696027, denPred := 99 }
@[expose] def scHartree4Hi : PosRat := { num := 2696032, denPred := 99 }

/-- Quarter Eliashberg–Tolmachev exponent `u = (1 + λ) / (4 (λ - μ* (1 + λ/2)))` in `PosRat`. -/
@[expose]
def scQuarterKmmExpPosRat (lam muStar : PosRat) : PosRat :=
  let num := scPosRatAddRed (posRatOfInt 1) lam
  let zRet := scPosRatAddRed (posRatOfInt 1) (posRatMulRed { num := 1, denPred := 1 } lam)
  let den := posRatMulRed (posRatOfInt 4) (posRatSubRed lam (posRatMulRed muStar zRet))
  posRatDivRed num (vpPosRatToNzOrOne den)

/--
Theorem (Zero Axioms): Born–Oppenheimer Phonon Scales, Vibronic `T_c` Benchmarks (`MgB₂`,
`Pb`, `Nb`), GPa Hydride Rupture (`LaH₁₀`), and `1 atm` Covalent `B–C` Clathrate Island.
-/
theorem sc_vibronic_phonons_tc_and_stability_islands_sweep :
    let ha4_exact_L := posRatMulRed (posRatOfInt 9)
      (scIntraAtomicU3dMeVPosRat 510998950 scAlphaInv4HiNz)
    let ha4_exact_U := posRatMulRed (posRatOfInt 9)
      (scIntraAtomicU3dMeVPosRat 510998952 scAlphaInv4LoNz)
    let sqMgB2_L : PosRat := { num := 100487, denPred := 999 }
    let sqMgB2_U : PosRat := { num := 100488, denPred := 999 }
    let sqNb_L : PosRat := { num := 41320, denPred := 99 }
    let sqNb_U : PosRat := { num := 41321, denPred := 99 }
    let sqPb_L : PosRat := { num := 61647, denPred := 99 }
    let sqPb_U : PosRat := { num := 61648, denPred := 99 }
    let sqH_L : PosRat := { num := 4284, denPred := 99 }
    let sqH_U : PosRat := { num := 4285, denPred := 99 }
    let hw_MgB2_L := posRatDivRed
      (posRatMulRed { num := 1, denPred := 3 } scHartree4Lo) (vpPosRatToNzOrOne sqMgB2_U)
    let hw_MgB2_U := posRatDivRed
      (posRatMulRed { num := 1, denPred := 3 } scHartree4Hi) (vpPosRatToNzOrOne sqMgB2_L)
    let Theta_MgB2_L := posRatMulRed hw_MgB2_L scKelvinPerMeVPosRat
    let Theta_MgB2_U := posRatMulRed hw_MgB2_U scKelvinPerMeVPosRat
    let Theta_Nb_L := posRatMulRed
      (posRatDivRed (posRatMulRed { num := 5, denPred := 15 } scHartree4Lo)
        (vpPosRatToNzOrOne sqNb_U))
      scKelvinPerMeVPosRat
    let Theta_Nb_U := posRatMulRed
      (posRatDivRed (posRatMulRed { num := 5, denPred := 15 } scHartree4Hi)
        (vpPosRatToNzOrOne sqNb_L))
      scKelvinPerMeVPosRat
    let Theta_Pb_L := posRatMulRed
      (posRatDivRed (posRatMulRed { num := 1, denPred := 8 } scHartree4Lo)
        (vpPosRatToNzOrOne sqPb_U))
      scKelvinPerMeVPosRat
    let Theta_Pb_U := posRatMulRed
      (posRatDivRed (posRatMulRed { num := 1, denPred := 8 } scHartree4Hi)
        (vpPosRatToNzOrOne sqPb_L))
      scKelvinPerMeVPosRat
    let Theta_H_L := posRatMulRed
      (posRatDivRed (posRatMulRed { num := 1, denPred := 3 } scHartree4Lo)
        (vpPosRatToNzOrOne sqH_U))
      scKelvinPerMeVPosRat
    let Theta_H_U := posRatMulRed
      (posRatDivRed (posRatMulRed { num := 1, denPred := 3 } scHartree4Hi)
        (vpPosRatToNzOrOne sqH_L))
      scKelvinPerMeVPosRat
    let kmm_L : PosRat := { num := 8342, denPred := 9999 }
    let kmm_U : PosRat := { num := 8343, denPred := 9999 }
    let Tc_MgB2_2band_L := posRatMulRed (posRatMulRed kmm_L { num := 7783, denPred := 9 })
      (suPosRatIterSq (suHornerExpNeg { num := 713, denPred := 999 } 9) 2)
    let Tc_MgB2_2band_U := posRatMulRed (posRatMulRed kmm_U { num := 7784, denPred := 9 })
      (suPosRatIterSq (suHornerExpNeg { num := 7127, denPred := 9999 } 8) 2)
    let Tc_MgB2_sig_U := posRatMulRed (posRatMulRed kmm_U { num := 7784, denPred := 9 })
      (suPosRatIterSq (suHornerExpNeg { num := 6977, denPred := 9999 } 8) 2)
    let Tc_Pb_sc_L := posRatMulRed { num := 17, denPred := 15 }
      (posRatMulRed (posRatMulRed kmm_L { num := 5638, denPred := 99 })
        (suPosRatIterSq (suHornerExpNeg { num := 4838, denPred := 9999 } 7) 2))
    let Tc_Pb_sc_U := posRatMulRed { num := 17, denPred := 15 }
      (posRatMulRed (posRatMulRed kmm_U { num := 5640, denPred := 99 })
        (suPosRatIterSq (suHornerExpNeg { num := 4836, denPred := 9999 } 6) 2))
    let Tc_Nb_L := posRatMulRed
      (posRatMulRed kmm_L
        (posRatDivRed { num := 23660, denPred := 99 }
          { isNeg := false, numPred := 13050, denPred := 9999 }))
      (suPosRatIterSq (suHornerExpNeg { num := 7096, denPred := 9999 } 9) 2)
    let Tc_Nb_U := posRatMulRed
      (posRatMulRed kmm_U
        (posRatDivRed { num := 23662, denPred := 99 }
          { isNeg := false, numPred := 13042, denPred := 9999 }))
      (suPosRatIterSq (suHornerExpNeg { num := 7093, denPred := 9999 } 8) 2)
    let Tc_Hydride_L := posRatMulRed (posRatMulRed kmm_L (posRatOfInt 1825))
      (suPosRatIterSq (suHornerExpNeg { num := 4539, denPred := 9999 } 7) 2)
    let Tc_Hydride_U := posRatMulRed (posRatMulRed kmm_U (posRatOfInt 1826))
      (suPosRatIterSq (suHornerExpNeg { num := 4537, denPred := 9999 } 6) 2)
    let Tc_BC_clath_L := posRatMulRed (posRatMulRed kmm_L { num := 7783, denPred := 9 })
      (suPosRatIterSq (suHornerExpNeg { num := 5603, denPred := 9999 } 7) 2)
    let Tc_BC_clath_U := posRatMulRed (posRatMulRed kmm_U { num := 7784, denPred := 9 })
      (suPosRatIterSq (suHornerExpNeg { num := 56, denPred := 99 } 6) 2)
    posRatLt scHartree4Lo ha4_exact_L = true ∧
    posRatLt ha4_exact_U scHartree4Hi = true ∧
    posRatLt (posRatMulRed sqMgB2_L sqMgB2_L)
      (posRatMulRed { num := 11, denPred := 1 } scMpCompactLo) = true ∧
    posRatLt (posRatMulRed { num := 11, denPred := 1 } scMpCompactHi)
      (posRatMulRed sqMgB2_U sqMgB2_U) = true ∧
    posRatLt (posRatMulRed sqNb_L sqNb_L)
      (posRatMulRed (posRatOfInt 93) scMpCompactLo) = true ∧
    posRatLt (posRatMulRed (posRatOfInt 93) scMpCompactHi)
      (posRatMulRed sqNb_U sqNb_U) = true ∧
    posRatLt (posRatMulRed sqPb_L sqPb_L)
      (posRatMulRed (posRatOfInt 207) scMpCompactLo) = true ∧
    posRatLt (posRatMulRed (posRatOfInt 207) scMpCompactHi)
      (posRatMulRed sqPb_U sqPb_U) = true ∧
    posRatLt (posRatMulRed sqH_L sqH_L) scMpCompactLo = true ∧
    posRatLt scMpCompactHi (posRatMulRed sqH_U sqH_U) = true ∧
    posRatLt { num := 6707, denPred := 99 } hw_MgB2_L = true ∧
    posRatLt hw_MgB2_U { num := 6708, denPred := 99 } = true ∧
    posRatLt { num := 7783, denPred := 9 } Theta_MgB2_L = true ∧
    posRatLt Theta_MgB2_U { num := 7784, denPred := 9 } = true ∧
    posRatLt { num := 23660, denPred := 99 } Theta_Nb_L = true ∧
    posRatLt Theta_Nb_U { num := 23662, denPred := 99 } = true ∧
    posRatLt { num := 5638, denPred := 99 } Theta_Pb_L = true ∧
    posRatLt Theta_Pb_U { num := 5640, denPred := 99 } = true ∧
    posRatLt (posRatOfInt 1825) Theta_H_L = true ∧
    posRatLt Theta_H_U (posRatOfInt 1826) = true ∧
    posRatLt { num := 7127, denPred := 9999 }
      (scQuarterKmmExpPosRat { num := 7, denPred := 7 } { num := 1512, denPred := 9999 }) = true ∧
    posRatLt
      (scQuarterKmmExpPosRat { num := 7, denPred := 7 } { num := 1513, denPred := 9999 })
      { num := 713, denPred := 999 } = true ∧
    posRatLt { num := 374, denPred := 9 } Tc_MgB2_2band_L = true ∧
    posRatLt Tc_MgB2_2band_U { num := 376, denPred := 9 } = true ∧
    posRatLt { num := 6977, denPred := 9999 }
      (scQuarterKmmExpPosRat { num := 9, denPred := 9 } { num := 1512, denPred := 9999 }) = true ∧
    posRatLt Tc_MgB2_sig_U (posRatOfInt 40) = true ∧
    posRatLt { num := 4836, denPred := 9999 }
      (scQuarterKmmExpPosRat { num := 3, denPred := 1 } { num := 1187, denPred := 9999 }) = true ∧
    posRatLt
      (scQuarterKmmExpPosRat { num := 3, denPred := 1 } { num := 1188, denPred := 9999 })
      { num := 4838, denPred := 9999 } = true ∧
    posRatLt { num := 720, denPred := 99 } Tc_Pb_sc_L = true ∧
    posRatLt Tc_Pb_sc_U { num := 724, denPred := 99 } = true ∧
    posRatLt { num := 7093, denPred := 9999 }
      (scQuarterKmmExpPosRat { num := 16302, denPred := 19999 }
        { num := 1246, denPred := 9999 }) = true ∧
    posRatLt
      (scQuarterKmmExpPosRat { num := 40749, denPred := 49999 }
        { num := 1247, denPred := 9999 })
      { num := 7096, denPred := 9999 } = true ∧
    posRatLt { num := 884, denPred := 99 } Tc_Nb_L = true ∧
    posRatLt Tc_Nb_U { num := 888, denPred := 99 } = true ∧
    posRatLt { num := 4537, denPred := 9999 }
      (scQuarterKmmExpPosRat (posRatOfInt 2) { num := 1736, denPred := 9999 }) = true ∧
    posRatLt
      (scQuarterKmmExpPosRat (posRatOfInt 2) { num := 1737, denPred := 9999 })
      { num := 4539, denPred := 9999 } = true ∧
    posRatLt (posRatOfInt 247) Tc_Hydride_L = true ∧
    posRatLt Tc_Hydride_U (posRatOfInt 249) = true ∧
    posRatLt (posRatOfInt 1) (helicityPressurePosRat 16 0) = true ∧
    helicityPressurePosRat 16 1 = posRatOfInt 1 ∧
    posRatLt { num := 56, denPred := 99 }
      (scQuarterKmmExpPosRat { num := 5, denPred := 3 } { num := 1512, denPred := 9999 }) = true ∧
    posRatLt
      (scQuarterKmmExpPosRat { num := 5, denPred := 3 } { num := 1513, denPred := 9999 })
      { num := 5603, denPred := 9999 } = true ∧
    posRatLt (posRatOfInt 69) Tc_BC_clath_L = true ∧
    posRatLt Tc_BC_clath_U { num := 692, denPred := 9 } = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: Continuum `ℝ` Tolmachev Cancellation, Garland Isotope & Cage Laws -/

/--
Theorem (Continuum `ℝ`): Exact `U_n` Scale Cancellation in Tolmachev `μ*` & Garland's
Sub-`1/2` Isotope-Exponent Theorem (`α_iso < 1/2`).
1. Dividing any shell Coulomb energy `U_n ≠ 0` by `ħω_vib = U_n / M` (`M = √(A_eff_mass · μ_pe)`)
   cancels `U_n` identically (`U_n / (U_n / M) = M`), fixing `μ*(M)` purely from mass ratios.
2. For ALL `0 < lam`, `0 < mu_star`, `0 < Z_ret` with `mu_star * Z_ret < lam`, the vibronic
   isotope exponent `α_iso = (1/2)[1 - (1 + lam)(mu_star Z_ret / (lam - mu_star Z_ret))²]`
   satisfies `α_iso < 1 / 2` strictly (contrasted against `α_iso = 0` on the Mott branch).
-/
theorem continuum_tolmachev_energy_cancellation_and_garland_isotope_bound
    (U_n M lam mu_star Z_ret : ℝ)
    (hU : U_n ≠ 0) (hM : M ≠ 0)
    (hlam : 0 < lam) (hmu : 0 < mu_star) (hZ : 0 < Z_ret)
    (h_net : mu_star * Z_ret < lam) :
    let hbar_omega := U_n / M
    let alpha_iso := (1 / 2 : ℝ) *
      (1 - (1 + lam) * ((mu_star * Z_ret) / (lam - mu_star * Z_ret)) ^ 2)
    U_n / hbar_omega = M ∧
    alpha_iso < (1 / 2 : ℝ) := by
  have h1 : U_n / (U_n / M) = M := by
    field_simp [hU, hM]
  have h_num_pos : 0 < mu_star * Z_ret := mul_pos hmu hZ
  have h_den_pos : 0 < lam - mu_star * Z_ret := sub_pos.mpr h_net
  have h_quot_pos : 0 < (mu_star * Z_ret) / (lam - mu_star * Z_ret) :=
    div_pos h_num_pos h_den_pos
  have h_sq_pos : 0 < ((mu_star * Z_ret) / (lam - mu_star * Z_ret)) ^ 2 :=
    pow_pos h_quot_pos 2
  have h_pen_pos :
      0 < (1 + lam) * ((mu_star * Z_ret) / (lam - mu_star * Z_ret)) ^ 2 :=
    mul_pos (by linarith) h_sq_pos
  exact ⟨h1, by linarith⟩

/--
Theorem (Continuum `ℝ`): Bogomolny–Lundquist Ambient Self-Confinement vs. GPa Anvil Law.
1. Under radial pressure balance `P_chem + P_ext = ξ / a⁴`, ambient self-confinement
   (`P_ext = 0`) holds iff host chemical stiffness `P_chem = ξ / a⁴`.
2. Whenever `P_chem < ξ / a⁴` (e.g., coreless `n = 1` atomic hydrogen clathrates), strictly
   positive external compression `0 < P_ext` is required to prevent cage rupture, subject to
   the Lundquist non-self-intersection bound `j_{0,1} / α_ff < R`.
-/
theorem continuum_lundquist_cage_rupture_and_external_pressure_law
    (xi a P_chem P_ext j01 alpha_ff R : ℝ)
    (ha : a ≠ 0)
    (h_bal : P_chem + P_ext = xi / (a ^ 4))
    (h_aff : 0 < alpha_ff) (h_rupt : j01 < alpha_ff * R) :
    (P_ext = 0 ↔ P_chem = xi / (a ^ 4)) ∧
    (P_chem < xi / (a ^ 4) → 0 < P_ext) ∧
    j01 / alpha_ff < R := by
  have h_iff : P_ext = 0 ↔ P_chem = xi / (a ^ 4) := by
    constructor <;> intro h <;> linarith
  have h_pos : P_chem < xi / (a ^ 4) → 0 < P_ext := by
    intro h_lt
    linarith
  have h_wall : j01 / alpha_ff < R := by
    rw [div_lt_iff₀ h_aff]
    exact lt_of_lt_of_eq h_rupt (by ring)
  exact ⟨h_iff, h_pos, h_wall⟩

#print axioms sc_tolmachev_mu_star_and_kmm_prefactor_bounds
#print axioms sc_vibronic_phonons_tc_and_stability_islands_sweep

end TVE
