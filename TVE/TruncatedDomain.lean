/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Truncated Modular Surface and Absorbing Boundary

Constructs the geometric domain \(Y_a\) by truncating the modular surface at the
unknot minor-radius cutoff \(y = a\). Formalizes the 1D Sommerfeld outgoing
radiation condition at the Archimedean geometric regulator.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false

public section

namespace TVE

open UpperHalfPlane

/-- The truncated upper half-plane bounded by the unknot minor radius `a`. -/
def TruncatedUpperHalfPlane (a : ℝ) :=
  { z : UpperHalfPlane // (z : ℂ).im ≤ a }

/-- The logarithmic cusp coordinate \(r = \ln y\). -/
noncomputable def cuspCoordinate (y : ℝ) : ℝ :=
  Real.log y

/-- The fundamental domain of the modular group \(\operatorname{SL}(2, \mathbb{Z})\). -/
axiom ModularFundamentalDomain : Set UpperHalfPlane

/-- The geometric domain \(Y_a\) used for the Lax-Phillips truncation. -/
def Y_a_domain (a : ℝ) :=
  { z : TruncatedUpperHalfPlane a // z.val ∈ ModularFundamentalDomain }

/--
The absorbing (outgoing) boundary condition at the truncation height \(r = \ln a\).
Strictly imposes the one-way Landauer exhaust of the TVE waveguide:
\(\partial_t v + \partial_r v = 0\)
-/
def isAbsorbingBoundary (v : ℝ → ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ t, (deriv (fun t' => v (cuspCoordinate a) t') t) +
       (deriv (fun r' => v r' t) (cuspCoordinate a)) = 0

end TVE
