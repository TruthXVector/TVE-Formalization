/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Beltrami Depletion of Nonlinearity in 3D Navier-Stokes

Formalizes the 3D Lamb vector \(\mathbf{L} = \boldsymbol{\omega} \times \mathbf{u}\)
governing the convective nonlinearity of incompressible fluid flow. Proves that
decomposing vorticity into its force-free Beltrami core \(\alpha\mathbf{u}\) and
transverse shear \(\boldsymbol{\omega}_\perp\) identically annihilates the core
self-stretching term: \((\alpha\mathbf{u} + \boldsymbol{\omega}_\perp) \times \mathbf{u}
= \boldsymbol{\omega}_\perp \times \mathbf{u}\).
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-- A three-dimensional Euclidean vector in \(\mathbb{R}^3\). -/
@[ext]
structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

/-- The zero vector in \(\mathbb{R}^3\). -/
@[expose]
def zero3 : Vec3 := ⟨0, 0, 0⟩

/-- Vector addition in \(\mathbb{R}^3\). -/
@[expose]
noncomputable def add3 (u v : Vec3) : Vec3 :=
  ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

/-- Scalar multiplication in \(\mathbb{R}^3\). -/
@[expose]
noncomputable def smul3 (c : ℝ) (u : Vec3) : Vec3 :=
  ⟨c * u.x, c * u.y, c * u.z⟩

/-- Euclidean dot product \(\mathbf{u} \cdot \mathbf{v}\) in \(\mathbb{R}^3\). -/
@[expose]
noncomputable def dot3 (u v : Vec3) : ℝ :=
  u.x * v.x + u.y * v.y + u.z * v.z

/--
The 3D cross product \(\boldsymbol{\omega} \times \mathbf{u}\) (the Lamb vector
governing convective vortex stretching).
-/
@[expose]
noncomputable def cross3 (omega u : Vec3) : Vec3 :=
  ⟨omega.y * u.z - omega.z * u.y,
   omega.z * u.x - omega.x * u.z,
   omega.x * u.y - omega.y * u.x⟩

/--
Theorem: Self-Cross Cancellation.
Any vector is strictly cross-orthogonal to itself (\(\mathbf{u} \times \mathbf{u} = \mathbf{0}\)).
-/
theorem self_cross3_zero (u : Vec3) : cross3 u u = zero3 := by
  ext <;> dsimp [cross3, zero3] <;> ring

/--
Theorem: Vanishing of the Lamb Vector on the Beltrami Core.
When vorticity aligns with velocity (\(\boldsymbol{\omega} = \alpha\mathbf{u}\)),
the convective Lamb vector vanishes identically.
-/
theorem beltrami_lamb_vanishes (alpha : ℝ) (u : Vec3) :
    cross3 (smul3 alpha u) u = zero3 := by
  ext <;> dsimp [cross3, smul3, zero3] <;> ring

/--
Theorem: Beltrami Depletion of Nonlinearity.
Under the decomposition \(\boldsymbol{\omega} = \alpha\mathbf{u} + \boldsymbol{\omega}_\perp\),
the Beltrami core drops out of the Lamb vector identically, leaving only the
transverse residual \(\boldsymbol{\omega}_\perp \times \mathbf{u}\).
-/
theorem beltrami_depletion_identity (alpha : ℝ) (u omega_perp : Vec3) :
    cross3 (add3 (smul3 alpha u) omega_perp) u = cross3 omega_perp u := by
  ext <;> dsimp [cross3, add3, smul3] <;> ring

/--
Theorem: Lamb Vector Orthogonality to Velocity (Convective Energy Conservation).
\((\boldsymbol{\omega} \times \mathbf{u}) \cdot \mathbf{u} = 0\).
-/
theorem lamb_orthogonal_velocity (omega u : Vec3) :
    dot3 (cross3 omega u) u = 0 := by
  dsimp [dot3, cross3]
  ring

/--
Theorem: Lamb Vector Orthogonality to Vorticity (Convective Helicity Conservation).
\((\boldsymbol{\omega} \times \mathbf{u}) \cdot \boldsymbol{\omega} = 0\).
-/
theorem lamb_orthogonal_vorticity (omega u : Vec3) :
    dot3 (cross3 omega u) omega = 0 := by
  dsimp [dot3, cross3]
  ring

#print axioms self_cross3_zero
#print axioms beltrami_lamb_vanishes
#print axioms beltrami_depletion_identity
#print axioms lamb_orthogonal_velocity
#print axioms lamb_orthogonal_vorticity

end TVE