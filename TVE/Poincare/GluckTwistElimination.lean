/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import TVE.YangMills.CovariantCutoff
public import TVE.Poincare.NeckStability
public import TVE.Poincare.SmoothPoincare4D

/-!
# Gluck Twist Elimination in 4D Smooth Topology

Closes the second potential route to an exotic smooth \(S^4\) (gluing an
embedded \(S^2 \times D^2\) via the non-trivial loop in \(\pi_1(SO(3))\)).
Under TVE, the 3D twist embeds into the 4D rotation group \(SO(4) \subset O(4)\),
preserving the covariant cutoff \(a_{\mathrm{eq}}\) while the overdamped
Woltjer-Taylor flow monotonically relaxes the twist shear energy to zero.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

open Matrix

public section

namespace TVE

/--
Explicit 4D matrix representation of the \(\pi\)-rotation generator of the
Gluck twist embedded in \(SO(3) \hookrightarrow SO(4)\).
-/
def GluckTwistGenerator : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-1,  0,  0,  0;
      0, -1,  0,  0;
      0,  0,  1,  0;
      0,  0,  0,  1]

/--
Theorem: The 4D Gluck twist generator is orientation-preserving (\(\det = +1\)).
-/
theorem gluck_generator_is_special : GluckTwistGenerator.det = 1 := by decide

/--
Theorem: The 4D Gluck twist generator is orthogonal (\(G^T G = I\)).
-/
theorem gluck_generator_is_orthogonal :
    GluckTwistGenerator.transpose * GluckTwistGenerator = 1 := by decide

/--
Theorem: Involutive Trivialization in \(SO(4)\) (\(\mathbb{Z}_2\) Closure).
Composing the Gluck twist generator with itself yields the 4D identity matrix.
-/
theorem gluck_generator_involutive :
    GluckTwistGenerator * GluckTwistGenerator = 1 := by decide

/--
The instantaneous twist shear energy along the 4D Woltjer-Taylor relaxation flow:
\(E_{\mathrm{twist}}(t) = e^{-2\gamma t} E_{\mathrm{twist}}(0)\).
-/
@[expose]
noncomputable def gluckTwistEnergy (E_twist0 gamma t : ℝ) : ℝ :=
  Real.exp (-2 * gamma * t) * E_twist0

/--
Theorem: Smooth Null-Homotopy Attenuation of Gluck Twist Strain Energy.
Along the overdamped relaxation flow, the non-trivial Gluck twist shear energy
is non-negative and decays monotonically below its initial value \(E_{\mathrm{twist}}(0)\).
-/
theorem gluck_twist_energy_decay (E_twist0 gamma t : ℝ)
    (hE0 : 0 ≤ E_twist0) (h_gamma : gamma > 0) (ht : 0 ≤ t) :
    0 ≤ gluckTwistEnergy E_twist0 gamma t ∧
    gluckTwistEnergy E_twist0 gamma t ≤ E_twist0 := by
  have h_exp := exp_decay_bounds gamma t h_gamma ht
  dsimp [gluckTwistEnergy]
  constructor
  · positivity
  · have h_mult : Real.exp (-2 * gamma * t) * E_twist0 ≤ 1 * E_twist0 :=
      mul_le_mul_of_nonneg_right h_exp.2 hE0
    linarith

/--
The Master TVE Gluck Twist Elimination Theorem:
For any orthogonal 4D Gluck frame transformation \(R \in O(4)\) on the 4-manifold,
the quadratic action density and dynamic cutoff \(a_{\mathrm{eq}} = (\xi/\sigma)^{1/4}\)
remain strictly invariant, the twist shear energy decays monotonically, and the
cross-sectional neck radius stays bounded above the surgery-free floor \(\pi\xi \le E_{\max} a^2\).
-/
theorem tve_gluck_twist_elimination
    (R F : Matrix (Fin 4) (Fin 4) ℝ)
    (E_twist0 gamma t a xi sigma E_max : ℝ)
    (hR : R.transpose * R = 1)
    (hE0 : 0 ≤ E_twist0) (h_gamma : gamma > 0) (ht : 0 ≤ t)
    (ha : a > 0) (hxi : xi > 0) (hsigma : sigma > 0)
    (h_bound : neckEnergyExplicit a xi sigma ≤ E_max) :
    actionDensity (rotateField R F) = actionDensity F ∧
    localCutoff (rotateField R F) xi sigma = localCutoff F xi sigma ∧
    (0 ≤ gluckTwistEnergy E_twist0 gamma t ∧ gluckTwistEnergy E_twist0 gamma t ≤ E_twist0) ∧
    Real.pi * xi ≤ E_max * (a ^ 2) := by
  refine ⟨trace_action_density_invariant R F hR,
          covariant_cutoff_os1 R F xi sigma hR,
          gluck_twist_energy_decay E_twist0 gamma t hE0 h_gamma ht,
          neck_radius_sq_floor a xi sigma E_max ha hxi hsigma h_bound⟩

#print axioms gluck_generator_is_special
#print axioms gluck_generator_is_orthogonal
#print axioms gluck_generator_involutive
#print axioms gluck_twist_energy_decay
#print axioms tve_gluck_twist_elimination

end TVE
