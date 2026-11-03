/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import TVE.NavierStokes.BeltramiDepletion
public import TVE.NavierStokes.CrossHelicityMHD
public import TVE.NavierStokes.LerayProjector
public import TVE.NavierStokes.ClassicalLerayHopfBridge

/-!
# Pointwise Fréchet Jacobian and Hessian Vector Calculus Bridge

Formalizes the spatial differential operators of the classical 3D
Navier-Stokes equations from the \(3 \times 3\) Fréchet Jacobian matrix
\(J_u\) and symmetric second-derivative Hessian matrices. Proves the
convective-to-Lamb identity, Schwarz curl-of-gradient vanishing
\(\nabla\times(\nabla p) = \mathbf{0}\), divergence-of-curl vanishing
\(\nabla\cdot(\nabla\times\mathbf{u}) = 0\), and the Pressure-Strain-Vorticity
Poisson identity \(\mathrm{Tr}(J_u^2) = |S|^2 - \frac{1}{2}|\boldsymbol{\omega}|^2\).
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
Symmetry of a \(3 \times 3\) second-derivative Hessian matrix (Schwarz's theorem:
\(\partial_i \partial_j f = \partial_j \partial_i f\)).
-/
@[expose]
def isSymmetricHessian3 (H : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  H 0 1 = H 1 0 ∧ H 0 2 = H 2 0 ∧ H 1 2 = H 2 1

/--
Divergence \(\nabla \cdot \mathbf{u} = \mathrm{Tr}(J_u)\) extracted from the
\(3 \times 3\) velocity Jacobian matrix \(J_{ij} = \partial_j u_i\).
-/
@[expose]
noncomputable def divFromJacobian (J : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  J 0 0 + J 1 1 + J 2 2

/--
Vorticity \(\boldsymbol{\omega} = \nabla \times \mathbf{u}\) extracted as the
axial vector of the skew-symmetric part of the \(3 \times 3\) Jacobian matrix \(J_u\).
-/
@[expose]
noncomputable def curlFromJacobian (J : Matrix (Fin 3) (Fin 3) ℝ) : Vec3 :=
  ⟨J 2 1 - J 1 2,
   J 0 2 - J 2 0,
   J 1 0 - J 0 1⟩

/--
Classical directional convective acceleration \((\mathbf{u} \cdot \nabla)\mathbf{u} = J_u \mathbf{u}\).
-/
@[expose]
noncomputable def convectiveDerivative3 (u : Vec3) (J : Matrix (Fin 3) (Fin 3) ℝ) : Vec3 :=
  ⟨u.x * J 0 0 + u.y * J 0 1 + u.z * J 0 2,
   u.x * J 1 0 + u.y * J 1 1 + u.z * J 1 2,
   u.x * J 2 0 + u.y * J 2 1 + u.z * J 2 2⟩

/--
Dynamic kinetic-energy gradient \(\frac{1}{2}\nabla|\mathbf{u}|^2 = J_u^T \mathbf{u}\).
-/
@[expose]
noncomputable def halfGradNormSq3 (u : Vec3) (J : Matrix (Fin 3) (Fin 3) ℝ) : Vec3 :=
  ⟨u.x * J 0 0 + u.y * J 1 0 + u.z * J 2 0,
   u.x * J 0 1 + u.y * J 1 1 + u.z * J 2 1,
   u.x * J 0 2 + u.y * J 1 2 + u.z * J 2 2⟩

/--
Divergence of the curl \(\nabla \cdot (\nabla \times \mathbf{u})\) evaluated from
the three component Hessian matrices \(H_x, H_y, H_z\) of \(\mathbf{u}\).
-/
@[expose]
noncomputable def divOfCurlFromHessians (Hx Hy Hz : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (Hz 0 1 - Hz 1 0) + (Hx 1 2 - Hx 2 1) + (Hy 2 0 - Hy 0 2)

/--
Trace of the squared velocity gradient \(\mathrm{Tr}(J_u^2) = \sum_{i,j} J_{ij} J_{ji}\)
(the classical source term of the pressure Poisson equation \(-\Delta p = \mathrm{Tr}(J_u^2)\)).
-/
@[expose]
noncomputable def jacobianSqTrace3 (J : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  J 0 0 ^ 2 + J 1 1 ^ 2 + J 2 2 ^ 2 +
    2 * (J 0 1 * J 1 0 + J 0 2 * J 2 0 + J 1 2 * J 2 1)

/--
Frobenius norm squared \(\|S(J_u)\|_F^2 = \sum_{i,j} \bigl(\frac{1}{2}(J_{ij} + J_{ji})\bigr)^2\)
of the symmetric strain-rate tensor \(S = \frac{1}{2}(J_u + J_u^T)\).
-/
@[expose]
noncomputable def strainFrobeniusSq3 (J : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  J 0 0 ^ 2 + J 1 1 ^ 2 + J 2 2 ^ 2 +
    2 * (((J 0 1 + J 1 0) / 2) ^ 2 +
         ((J 0 2 + J 2 0) / 2) ^ 2 +
         ((J 1 2 + J 2 1) / 2) ^ 2)

/--
Lemma: Any matrix equal to its transpose satisfies `isSymmetricHessian3`.
-/
theorem transpose_eq_implies_symmetric_hessian (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.transpose = H) : isSymmetricHessian3 H := by
  have h01 : H.transpose 1 0 = H 1 0 := by rw [hH]
  have h02 : H.transpose 2 0 = H 2 0 := by rw [hH]
  have h12 : H.transpose 2 1 = H 2 1 := by rw [hH]
  exact ⟨h01, h02, h12⟩

/--
Theorem (Schwarz Curl-of-Gradient Vanishing):
For any pressure field \(p\) whose Hessian matrix \(H_p\) is symmetric
(\(\partial_i \partial_j p = \partial_j \partial_i p\)), taking the curl of the
pressure gradient vanishes identically: \(\nabla \times (\nabla p) = \mathbf{0}\).
-/
theorem schwarz_curl_grad_vanishes (H_p : Matrix (Fin 3) (Fin 3) ℝ)
    (h_symm : isSymmetricHessian3 H_p) :
    curlFromJacobian H_p = zero3 := by
  rcases h_symm with ⟨h01, h02, h12⟩
  ext <;> dsimp [curlFromJacobian, zero3] <;> linarith

/--
Theorem (Schwarz Divergence-of-Curl Vanishing):
For any smooth velocity field \(\mathbf{u}\) with symmetric component Hessians
\(H_x, H_y, H_z\), the vorticity is identically divergence-free:
\(\nabla \cdot (\nabla \times \mathbf{u}) = 0\).
-/
theorem schwarz_div_curl_vanishes (Hx Hy Hz : Matrix (Fin 3) (Fin 3) ℝ)
    (hx : isSymmetricHessian3 Hx)
    (hy : isSymmetricHessian3 Hy)
    (hz : isSymmetricHessian3 Hz) :
    divOfCurlFromHessians Hx Hy Hz = 0 := by
  rcases hx with ⟨_, _, hx12⟩
  rcases hy with ⟨_, hy02, _⟩
  rcases hz with ⟨hz01, _, _⟩
  dsimp [divOfCurlFromHessians]
  linarith

/--
Theorem (Exact Pointwise Convective-to-Lamb Decomposition):
For every velocity vector \(\mathbf{u} \in \mathbb{R}^3\) and every \(3 \times 3\)
Jacobian matrix \(J_u\), the convective derivative decomposes identically into
the rotational Lamb vector plus the kinetic energy gradient:
\((\mathbf{u}\cdot\nabla)\mathbf{u} = (\nabla\times\mathbf{u})\times\mathbf{u} + \frac{1}{2}\nabla|\mathbf{u}|^2\).
-/
theorem convective_lamb_bernoulli_identity (u : Vec3) (J : Matrix (Fin 3) (Fin 3) ℝ) :
    convectiveDerivative3 u J =
      add3 (cross3 (curlFromJacobian J) u) (halfGradNormSq3 u J) := by
  ext <;> dsimp [convectiveDerivative3, add3, cross3,
                 curlFromJacobian, halfGradNormSq3] <;> ring

/--
Theorem (Pointwise Vanishing of Rotational Lamb Work):
Taking the inner product of the convective acceleration with \(\mathbf{u}\)
annihilates the rotational Lamb vector identically at every point \(x \in \mathbb{R}^3\):
\(((\mathbf{u}\cdot\nabla)\mathbf{u}) \cdot \mathbf{u} = (\frac{1}{2}\nabla|\mathbf{u}|^2) \cdot \mathbf{u}\).
-/
theorem convective_work_reduces_to_bernoulli (u : Vec3) (J : Matrix (Fin 3) (Fin 3) ℝ) :
    dot3 (convectiveDerivative3 u J) u = dot3 (halfGradNormSq3 u J) u := by
  dsimp [convectiveDerivative3, halfGradNormSq3, dot3]
  ring

/--
Theorem (Exact Pressure-Strain-Vorticity Poisson Trace Identity):
For every \(3 \times 3\) velocity Jacobian matrix \(J_u\), the pressure Poisson
source \(\mathrm{Tr}(J_u^2)\) equals the Frobenius norm squared of the symmetric
strain tensor minus half the squared vorticity norm:
\(\mathrm{Tr}(J_u^2) = \|S(J_u)\|_F^2 - \frac{1}{2}\|\nabla \times \mathbf{u}\|^2\).
-/
theorem pressure_poisson_jacobian_trace_identity (J : Matrix (Fin 3) (Fin 3) ℝ) :
    jacobianSqTrace3 J =
      pressurePoissonSource (strainFrobeniusSq3 J) (normSq3 (curlFromJacobian J)) := by
  dsimp [jacobianSqTrace3, pressurePoissonSource, strainFrobeniusSq3,
         normSq3, curlFromJacobian]
  ring

#print axioms transpose_eq_implies_symmetric_hessian
#print axioms schwarz_curl_grad_vanishes
#print axioms schwarz_div_curl_vanishes
#print axioms convective_lamb_bernoulli_identity
#print axioms convective_work_reduces_to_bernoulli
#print axioms pressure_poisson_jacobian_trace_identity

end TVE
