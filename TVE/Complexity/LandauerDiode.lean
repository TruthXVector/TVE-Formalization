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
public import Mathlib.Tactic.NormNum

/-!
# Landauer Thermodynamic Diode and Non-Injective Gate Compression

Formalizes the polynomial spin representation of boolean 3-SAT verification
clauses \(\Phi_3(s_1, s_2, s_3) = \frac{1}{8}(1+s_1)(1+s_2)(1+s_3)\). Proves
constructive non-injectivity on the satisfying fiber, rules out single-valued
deterministic inversion oracles, and establishes strictly positive Landauer
heat dissipation and forward-only causal current rectification.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/--
The 3-SAT clause dissatisfaction penalty on spin variables \(s_i \in \{-1, +1\}\),
where \(-1\) encodes True and \(+1\) encodes False:
\(\Phi_3(s_1, s_2, s_3) = \frac{1}{8}(1 + s_1)(1 + s_2)(1 + s_3)\).
-/
@[expose]
noncomputable def clause3SAT (s1 s2 s3 : ℝ) : ℝ :=
  (1 / 8) * (1 + s1) * (1 + s2) * (1 + s3)

/--
Localized Landauer heat dissipated when erasing \(\Delta I\) bits of pre-image
distinction across a non-injective verification gate:
\(Q_{\mathrm{Landauer}} = k_B T \ln 2 \cdot \Delta I\).
-/
@[expose]
noncomputable def landauerHeat (kB T ln2 deltaI : ℝ) : ℝ :=
  kB * T * ln2 * deltaI

/--
Net macroscopic causal information current across a rectified diode edge:
\(\dot{I}_{\mathrm{net}} = (A_{ij} - A_{ji}) \dot{S}_{\mathrm{Landauer}}\).
-/
@[expose]
noncomputable def netCausalCurrent (A_ij A_ji S_dot : ℝ) : ℝ :=
  (A_ij - A_ji) * S_dot

/--
Theorem: Unique Falsifying Assignment.
When all three literals are False (\(s_1 = s_2 = s_3 = +1\)), the clause
penalty evaluates to \(1\).
-/
theorem clause3SAT_falsified : clause3SAT 1 1 1 = 1 := by
  dsimp [clause3SAT]
  norm_num

/--
Theorem: Satisfying Pre-Image Fiber Collapse.
Whenever the first literal is True (\(s_1 = -1\)), the clause penalty vanishes
identically for all assignments of \((s_2, s_3)\).
-/
theorem clause3SAT_satisfied_fiber (s2 s3 : ℝ) :
    clause3SAT (-1) s2 s3 = 0 := by
  dsimp [clause3SAT]
  ring

/--
Theorem: Constructive Non-Injectivity of 3-SAT Verification Gates.
Distinct spin witnesses \(w_1 = (-1, 1, 1)\) and \(w_2 = (1, -1, 1)\) map to
the exact same output \(\Phi_3(w_1) = \Phi_3(w_2) = 0\) while \(-1 \ne 1\).
-/
theorem clause3SAT_non_injective :
    clause3SAT (-1) 1 1 = 0 ∧
    clause3SAT 1 (-1) 1 = 0 ∧
    clause3SAT (-1) 1 1 = clause3SAT 1 (-1) 1 ∧
    (-1 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [clause3SAT] <;> norm_num

/--
Theorem (Oracle Exclusion): Impossibility of Single-Valued Deterministic Inversion.
No single-valued deterministic function \(\Psi_1 : \mathbb{R} \to \mathbb{R}\) can
recover the first spin coordinate from the compressed clause output \(\Phi_3(w) = 0\).
-/
theorem no_single_valued_oracle_inverse
    (psi1 : ℝ → ℝ)
    (h_w1 : psi1 (clause3SAT (-1) 1 1) = -1)
    (h_w2 : psi1 (clause3SAT 1 (-1) 1) = 1) :
    False := by
  have h_eq : clause3SAT (-1) 1 1 = clause3SAT 1 (-1) 1 := by
    dsimp [clause3SAT]
    norm_num
  rw [h_eq] at h_w1
  linarith

/--
Theorem: Strict Positivity of Landauer Gate Dissipation.
For \(k_B, T, \ln 2, \Delta I > 0\), forward pre-image compression dissipates
strictly positive Landauer heat \(Q_{\mathrm{Landauer}} > 0\).
-/
theorem landauer_heat_pos (kB T ln2 deltaI : ℝ)
    (hk : kB > 0) (hT : T > 0) (hln : ln2 > 0) (hI : deltaI > 0) :
    0 < landauerHeat kB T ln2 deltaI := by
  dsimp [landauerHeat]
  positivity

/--
Theorem: Thermodynamic Diode Rectification Asymmetry.
When forward adjacency exceeds reverse adjacency (\(A_{ji} < A_{ij}\)) under
positive Landauer entropy production \(\dot{S} > 0\), net causal current is
strictly positive (\(\dot{I}_{\mathrm{net}} > 0\)), whereas any time-symmetric
algebrization (\(A_{ij} = A_{ji}\)) yields zero net current.
-/
theorem landauer_diode_rectification_pos (A_ij A_ji S_dot : ℝ)
    (h_rect : A_ji < A_ij) (hS : S_dot > 0) :
    0 < netCausalCurrent A_ij A_ji S_dot ∧
    netCausalCurrent A_ij A_ij S_dot = 0 := by
  dsimp [netCausalCurrent]
  have h_diff : 0 < A_ij - A_ji := by linarith
  refine ⟨mul_pos h_diff hS, ?_⟩
  ring

#print axioms clause3SAT_falsified
#print axioms clause3SAT_satisfied_fiber
#print axioms clause3SAT_non_injective
#print axioms no_single_valued_oracle_inverse
#print axioms landauer_heat_pos
#print axioms landauer_diode_rectification_pos

end TVE
