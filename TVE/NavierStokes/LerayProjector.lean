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
public import TVE.NavierStokes.BeltramiDepletion
public import TVE.NavierStokes.CrossHelicityMHD

/-!
# Leray-Helmholtz Projector, Pressure Reconstruction, and Beltrami Split

Formalizes the classical Fourier-space Leray solenoidal projector
\(\mathbb{P}_{\mathbf{k}}(\mathbf{v})\) and the complementary longitudinal
pressure-gradient projector \(\mathbb{Q}_{\mathbf{k}}(\mathbf{v})\). Proves
exact pressure annihilation, Pythagorean norm stability, curl commutation,
and the universal Lagrange-Beltrami identity
\(\|\boldsymbol{\omega} \times \mathbf{u}\|^2 = \|\mathbf{u}\|^2 \|\boldsymbol{\omega}_\perp\|^2\)
for every unrestricted vector field in \(\mathbb{R}^3\).
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
The longitudinal Helmholtz-Hodge projector reconstructing the pressure gradient
mode from any vector \(\mathbf{v}\) at wavevector \(\mathbf{k}\):
\(\mathbb{Q}_{\mathbf{k}}(\mathbf{v}) = \frac{\mathbf{k} \cdot \mathbf{v}}{\|\mathbf{k}\|^2}\mathbf{k}\).
-/
@[expose]
noncomputable def pressureProjector3 (k v : Vec3) : Vec3 :=
  smul3 (dot3 k v / normSq3 k) k

/--
The solenoidal Leray projector onto the divergence-free subspace at wavevector \(\mathbf{k}\):
\(\mathbb{P}_{\mathbf{k}}(\mathbf{v}) = \mathbf{v} - \mathbb{Q}_{\mathbf{k}}(\mathbf{v})\).
-/
@[expose]
noncomputable def lerayProjector3 (k v : Vec3) : Vec3 :=
  sub3 v (pressureProjector3 k v)

/--
Universal pointwise Gram-Schmidt Beltrami alignment coefficient for any
unrestricted velocity \(\mathbf{u}\) and vorticity \(\boldsymbol{\omega}\):
\(\alpha(\mathbf{u}, \boldsymbol{\omega}) = \frac{\mathbf{u} \cdot \boldsymbol{\omega}}{\|\mathbf{u}\|^2}\).
-/
@[expose]
noncomputable def beltramiAlpha (u omega : Vec3) : ℝ :=
  dot3 u omega / normSq3 u

/--
Universal transverse non-Beltrami vorticity component for any unrestricted
field pair \((\mathbf{u}, \boldsymbol{\omega})\):
\(\boldsymbol{\omega}_\perp = \boldsymbol{\omega} - \alpha(\mathbf{u}, \boldsymbol{\omega})\mathbf{u}\).
-/
@[expose]
noncomputable def beltramiPerp (u omega : Vec3) : Vec3 :=
  lerayProjector3 u omega

/-- Lemma: Squared Euclidean norm is non-negative for all \(\mathbf{w} \in \mathbb{R}^3\). -/
theorem normSq3_nonneg (w : Vec3) : 0 ≤ normSq3 w := by
  dsimp [normSq3]
  positivity

/-- Lemma: Polarization expansion of \(\|\mathbf{p} + \mathbf{q}\|^2\) in \(\mathbb{R}^3\). -/
theorem normSq3_add (p q : Vec3) :
    normSq3 (add3 p q) = normSq3 p + normSq3 q + 2 * dot3 p q := by
  dsimp [normSq3, add3, dot3]
  ring

/--
Theorem: Exact Helmholtz-Hodge Vector Reconstruction.
Every vector \(\mathbf{v} \in \mathbb{R}^3\) decomposes identically into its
solenoidal Leray projection and longitudinal pressure projection:
\(\mathbb{P}_{\mathbf{k}}(\mathbf{v}) + \mathbb{Q}_{\mathbf{k}}(\mathbf{v}) = \mathbf{v}\).
-/
theorem helmholtz_hodge_reconstruction (k v : Vec3) :
    add3 (lerayProjector3 k v) (pressureProjector3 k v) = v := by
  ext <;> dsimp [add3, lerayProjector3, pressureProjector3, sub3, smul3] <;> ring

/--
Theorem: Zero-Mode Galilean Vanishing.
At the zero mode \(\mathbf{v} = \mathbf{0}\), both the Leray velocity projection
and the reconstructed pressure gradient vanish identically.
-/
theorem zero_mode_galilean_vanishing (k : Vec3) :
    lerayProjector3 k zero3 = zero3 ∧ pressureProjector3 k zero3 = zero3 := by
  have h_dot : dot3 k zero3 = 0 := by dsimp [dot3, zero3]; ring
  have h_p : pressureProjector3 k zero3 = zero3 := by
    dsimp only [pressureProjector3]
    rw [h_dot, zero_div]
    ext <;> dsimp [smul3, zero3] <;> ring
  refine ⟨?_, h_p⟩
  change sub3 zero3 (pressureProjector3 k zero3) = zero3
  rw [h_p]
  ext <;> dsimp [sub3, zero3] <;> ring

/--
Theorem: Exact Annihilation of Pressure Gradients by the Leray Projector.
For any non-zero wavevector (\(\|\mathbf{k}\|^2 > 0\)) and scalar \(c \in \mathbb{R}\),
\(\mathbb{P}_{\mathbf{k}}(c\mathbf{k}) = \mathbf{0}\).
-/
theorem leray_annihilates_pressure_gradient (k : Vec3) (c : ℝ)
    (hk : normSq3 k > 0) :
    lerayProjector3 k (smul3 c k) = zero3 := by
  have hk_ne : normSq3 k ≠ 0 := ne_of_gt hk
  have h_dot : dot3 k (smul3 c k) = c * normSq3 k := by
    dsimp [dot3, smul3, normSq3]
    ring
  have h_coeff : dot3 k (smul3 c k) / normSq3 k = c := by
    rw [h_dot]
    exact mul_div_cancel_right₀ c hk_ne
  dsimp [lerayProjector3, pressureProjector3]
  rw [h_coeff]
  ext <;> dsimp [sub3, smul3, zero3] <;> ring

/--
Theorem: Divergence-Free (Solenoidal) Image of the Leray Projector.
For any \(\|\mathbf{k}\|^2 > 0\), \(\mathbf{k} \cdot \mathbb{P}_{\mathbf{k}}(\mathbf{v}) = 0\).
-/
theorem leray_image_divergence_free (k v : Vec3) (hk : normSq3 k > 0) :
    dot3 k (lerayProjector3 k v) = 0 := by
  have hk_ne : normSq3 k ≠ 0 := ne_of_gt hk
  have h_expand : dot3 k (lerayProjector3 k v) =
      dot3 k v - (dot3 k v / normSq3 k) * normSq3 k := by
    dsimp [lerayProjector3, pressureProjector3, sub3, smul3, dot3, normSq3]
    ring
  rw [h_expand, div_mul_cancel₀ (dot3 k v) hk_ne, sub_self]

/--
Theorem: Exact Orthogonality of the Solenoidal and Pressure Projections.
\(\mathbb{P}_{\mathbf{k}}(\mathbf{v}) \cdot \mathbb{Q}_{\mathbf{k}}(\mathbf{v}) = 0\).
-/
theorem leray_orthogonal_pressure (k v : Vec3) (hk : normSq3 k > 0) :
    dot3 (lerayProjector3 k v) (pressureProjector3 k v) = 0 := by
  have h_div := leray_image_divergence_free k v hk
  have h_factor : dot3 (lerayProjector3 k v) (pressureProjector3 k v) =
      (dot3 k v / normSq3 k) * dot3 k (lerayProjector3 k v) := by
    dsimp [pressureProjector3, smul3, dot3]
    ring
  rw [h_factor, h_div, mul_zero]

/--
Theorem: Idempotence of the Leray Projector (\(\mathbb{P}_{\mathbf{k}}^2 = \mathbb{P}_{\mathbf{k}}\)).
-/
theorem leray_idempotent (k v : Vec3) (hk : normSq3 k > 0) :
    lerayProjector3 k (lerayProjector3 k v) = lerayProjector3 k v := by
  have h_div := leray_image_divergence_free k v hk
  have h_p : pressureProjector3 k (lerayProjector3 k v) = zero3 := by
    dsimp only [pressureProjector3]
    rw [h_div, zero_div]
    ext <;> dsimp [smul3, zero3] <;> ring
  change sub3 (lerayProjector3 k v) (pressureProjector3 k (lerayProjector3 k v)) =
    lerayProjector3 k v
  rw [h_p]
  ext <;> dsimp [sub3, zero3] <;> ring

/--
Theorem: Self-Adjointness of the Leray Projector.
\(\mathbb{P}_{\mathbf{k}}(\mathbf{u}) \cdot \mathbf{v} = \mathbf{u} \cdot \mathbb{P}_{\mathbf{k}}(\mathbf{v})\).
-/
theorem leray_self_adjoint (k u v : Vec3) :
    dot3 (lerayProjector3 k u) v = dot3 u (lerayProjector3 k v) := by
  dsimp [lerayProjector3, pressureProjector3, sub3, smul3, dot3]
  ring

/--
Theorem: Pythagorean Norm Decomposition and Contractivity of Pressure Elimination.
\(\|\mathbb{P}_{\mathbf{k}}(\mathbf{v})\|^2 + \|\mathbb{Q}_{\mathbf{k}}(\mathbf{v})\|^2 = \|\mathbf{v}\|^2\),
guaranteeing both \(\|\mathbb{P}_{\mathbf{k}}(\mathbf{v})\|^2 \le \|\mathbf{v}\|^2\) and
pressure stability \(\|\mathbb{Q}_{\mathbf{k}}(\mathbf{v})\|^2 \le \|\mathbf{v}\|^2\).
-/
theorem leray_pythagorean_decomposition (k v : Vec3) (hk : normSq3 k > 0) :
    normSq3 (lerayProjector3 k v) + normSq3 (pressureProjector3 k v) = normSq3 v ∧
    normSq3 (lerayProjector3 k v) ≤ normSq3 v ∧
    normSq3 (pressureProjector3 k v) ≤ normSq3 v := by
  have h_rec := helmholtz_hodge_reconstruction k v
  have h_orth := leray_orthogonal_pressure k v hk
  have h_add := normSq3_add (lerayProjector3 k v) (pressureProjector3 k v)
  rw [h_rec, h_orth] at h_add
  have hP_pos := normSq3_nonneg (lerayProjector3 k v)
  have hQ_pos := normSq3_nonneg (pressureProjector3 k v)
  refine ⟨by linarith, by linarith, by linarith⟩

/--
Theorem: Equivalence of the Leray-Projected Momentum Equation and the Vorticity Equation.
Taking the Fourier curl (\(\mathbf{k} \times \cdot\)) commutes with the Leray projector:
\(\mathbf{k} \times \mathbb{P}_{\mathbf{k}}(\mathbf{L}) = \mathbf{k} \times \mathbf{L}\).
-/
theorem curl_leray_commutes (k L : Vec3) :
    cross3 k (lerayProjector3 k L) = cross3 k L := by
  ext <;> dsimp [cross3, lerayProjector3, pressureProjector3, sub3, smul3] <;> ring

/--
Theorem: Lagrange's 3D Vector Identity (Universal Helicity Depletion of the Lamb Vector).
For every unrestricted pair of vectors \(\mathbf{u}, \boldsymbol{\omega} \in \mathbb{R}^3\),
\(\|\boldsymbol{\omega} \times \mathbf{u}\|^2 + (\mathbf{u} \cdot \boldsymbol{\omega})^2
= \|\mathbf{u}\|^2 \|\boldsymbol{\omega}\|^2\).
-/
theorem lagrange_vector_identity (u omega : Vec3) :
    normSq3 (cross3 omega u) + (dot3 u omega) ^ 2 = normSq3 u * normSq3 omega := by
  dsimp [normSq3, cross3, dot3]
  ring

/--
Theorem: Universal Unrestricted Beltrami Decomposition and Lamb Norm Identity.
Every unrestricted vector field pair \((\mathbf{u}, \boldsymbol{\omega})\) with
\(\|\mathbf{u}\|^2 > 0\) decomposes identically as
\(\boldsymbol{\omega} = \alpha(\mathbf{u}, \boldsymbol{\omega})\mathbf{u} + \boldsymbol{\omega}_\perp\)
with \(\mathbf{u} \cdot \boldsymbol{\omega}_\perp = 0\) and exact Lamb norm
\(\|\boldsymbol{\omega} \times \mathbf{u}\|^2 = \|\mathbf{u}\|^2 \|\boldsymbol{\omega}_\perp\|^2\).
-/
theorem universal_beltrami_orthogonal_split (u omega : Vec3) (hu : normSq3 u > 0) :
    add3 (smul3 (beltramiAlpha u omega) u) (beltramiPerp u omega) = omega ∧
    dot3 u (beltramiPerp u omega) = 0 ∧
    normSq3 (cross3 omega u) = normSq3 u * normSq3 (beltramiPerp u omega) := by
  have h_rec : add3 (smul3 (beltramiAlpha u omega) u) (beltramiPerp u omega) = omega := by
    ext <;> dsimp [add3, smul3, beltramiAlpha, beltramiPerp,
                   lerayProjector3, pressureProjector3, sub3] <;> ring
  have h_orth : dot3 u (beltramiPerp u omega) = 0 :=
    leray_image_divergence_free u omega hu
  have h_depl : cross3 omega u = cross3 (beltramiPerp u omega) u := by
    calc
      cross3 omega u
        = cross3 (add3 (smul3 (beltramiAlpha u omega) u) (beltramiPerp u omega)) u := by
            rw [h_rec]
      _ = cross3 (beltramiPerp u omega) u :=
            beltrami_depletion_identity (beltramiAlpha u omega) u (beltramiPerp u omega)
  have h_lagr := lagrange_vector_identity u (beltramiPerp u omega)
  rw [h_orth, ← h_depl] at h_lagr
  refine ⟨h_rec, h_orth, by linarith⟩

#print axioms helmholtz_hodge_reconstruction
#print axioms zero_mode_galilean_vanishing
#print axioms leray_annihilates_pressure_gradient
#print axioms leray_image_divergence_free
#print axioms leray_orthogonal_pressure
#print axioms leray_idempotent
#print axioms leray_self_adjoint
#print axioms leray_pythagorean_decomposition
#print axioms curl_leray_commutes
#print axioms lagrange_vector_identity
#print axioms universal_beltrami_orthogonal_split

end TVE
