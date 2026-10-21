/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import TVE.Vacuum
public import TVE.Action
public import TVE.Topologies

/-!
# Topological Vacuum Electrodynamics — Particle Spectrum

Rest energy is the magnetic energy of the tube. Masses are mapped exactly
to the geometric topologies and mode count.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false

public section

namespace TVE

/-- Physical constants appearing in the mass formulas. -/
axiom ℏ : ℝ
axiom c : ℝ
axiom a_B : ℝ
axiom m_e : ℝ

/-- Rest energy of a topological tube (formally represents the magnetic volume integral). -/
axiom restEnergy (t : FluxTube) : ℝ

/-- Electron mass from the mode-count reading of the Bohr circle. -/
noncomputable def electronMass : ℝ := alphaInv * (ℏ / (a_B * c))

/-- Muon mass: \((3/2)(1+\alpha)\alpha^{-1}m_e\). -/
noncomputable def muonMass : ℝ := (3/2) * (1 + alpha) * alphaInv * m_e

/-- Tau mass: \(8\pi(1+\alpha)\alpha^{-1}m_e\). -/
noncomputable def tauMass : ℝ := 8 * Real.pi * (1 + alpha) * alphaInv * m_e

/-- String tension relation: \(\sqrt{\sigma} = 2\pi\alpha^{-1}m_e\). -/
noncomputable def sqrtSigma : ℝ := 2 * Real.pi * alphaInv * m_e

/-- The strange subtraction: \(\sigma_s = (4/7)\alpha^{-1}m_e\). -/
noncomputable def strangeSubtraction : ℝ := (4/7) * alphaInv * m_e

/-- Proton mass after the strange subtraction. -/
noncomputable def protonMass : ℝ := (7 / Real.pi) * sqrtSigma

/-- Pion mass: \(\sqrt{\sigma}/\pi\). -/
noncomputable def pionMass : ℝ := sqrtSigma / Real.pi

/-- Neutrino mass: \(m_e\alpha^3\). -/
noncomputable def neutrinoMass : ℝ := m_e * alpha ^ 3

/-! ## The Topology-to-Mass Mapping
    These axioms mechanically bind the geometric topologies to their exact mass equations. -/

/-- The rest energy of the ground-state unknot yields the baseline electron mass. -/
axiom rest_energy_electron (a : ℝ) : restEnergy (electronUnknot a) = electronMass

/-- The rest energy of the second radial wall yields the muon mass. -/
axiom rest_energy_muon (a : ℝ) : restEnergy (muon a) = muonMass

/-- The rest energy of the third radial wall yields the tau mass. -/
axiom rest_energy_tau (a : ℝ) : restEnergy (tau a) = tauMass

/-- The rest energy of the trefoil minus the strange subtraction yields the proton mass. -/
axiom rest_energy_proton (a R : ℝ) : restEnergy (protonTrefoil a R) - strangeSubtraction = protonMass

/-- The rest energy of the Hopf link yields the pion mass. -/
axiom rest_energy_pion (a R : ℝ) : restEnergy (pionHopfLink a R) = pionMass

/-- The rest energy of the planar loop yields the neutrino mass. -/
axiom rest_energy_neutrino (a R : ℝ) : restEnergy (neutrinoPlanarLoop a R) = neutrinoMass

end TVE
