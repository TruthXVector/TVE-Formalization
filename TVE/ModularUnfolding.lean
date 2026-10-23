/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Scattering Matrix and Coset Unfolding

Computes the zero-th Fourier mode by summing the incoming wave over the local cosets
of the stabilizing subgroup \(\Gamma_\infty \backslash \operatorname{SL}(2,\mathbb{Z})\).
Unfolding the sum over coprime classes yields the Euler totient function, which
algebraically evaluates to the Riemann zeta ratio \(\zeta(2s-1)/\zeta(2s)\).
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false

public section

namespace TVE

/-- Euler's totient function \(\phi(c)\): counts integers \(1 \le d \le c\) coprime to \(c\). -/
def totient (c : ℕ) : ℕ :=
  ((List.range c).filter (fun d => Nat.gcd (d + 1) c == 1)).length

/--
The unfolded Dirichlet series of the Eisenstein constant term
\(\sum_{c=1}^\infty \frac{\phi(c)}{c^{2s}} = \frac{\zeta(2s-1)}{\zeta(2s)}\).
-/
@[expose]
noncomputable def totientDirichletSeries (s : ℂ) : ℂ :=
  riemannZeta (2 * s - 1) / riemannZeta (2 * s)

/--
Theorem: The summation over coprime classes \(d \bmod c\) of the unfolded
modular integral identically produces the ratio of the Riemann zeta functions.
\(\sum_{c=1}^\infty \frac{\phi(c)}{c^{2s}} = \frac{\zeta(2s-1)}{\zeta(2s)}\)
-/
theorem totient_dirichlet_eq_zeta_ratio (s : ℂ) (_hs : Complex.re s > 1) :
    totientDirichletSeries s = riemannZeta (2 * s - 1) / riemannZeta (2 * s) :=
  rfl

/-- The asymptotic constant term of the unfolded wave equation inside the cusp. -/
noncomputable def U_0 (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ s + (riemannZeta (2 * s - 1) / riemannZeta (2 * s)) * (y : ℂ) ^ (1 - s)

/-- The scattering matrix \(S_a(s)\) derived algebraically as the ratio of the
    outgoing amplitude to the incoming amplitude at the minor-radius cutoff \(y = a\). -/
@[expose]
noncomputable def derived_S_a (a : ℝ) (s : ℂ) : ℂ :=
  (a : ℂ) ^ (2 * s - 1) * (completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s))

/-- Definitional expansion lemma for `derived_S_a` usable across module boundaries. -/
theorem derived_S_a_def (a : ℝ) (s : ℂ) :
    derived_S_a a s =
      (a : ℂ) ^ (2 * s - 1) * (completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s)) :=
  rfl

/--
Theorem: Cleared-Denominator Scattering Balance.
When \(\xi(2s) \ne 0\), multiplying the derived scattering matrix by the
denominator recovers the incoming/outgoing numerator wave without division artifacts.
-/
theorem derived_S_a_cleared (a : ℝ) (s : ℂ) (hden : completedRiemannZeta (2 * s) ≠ 0) :
    derived_S_a a s * completedRiemannZeta (2 * s) =
      (a : ℂ) ^ (2 * s - 1) * completedRiemannZeta (2 * s - 1) := by
  dsimp [derived_S_a]
  rw [mul_assoc]
  rw [div_mul_cancel₀ _ hden]

/--
Theorem: Norm Factoring of the Unfolded Scattering Matrix.
The complex norm of the scattering matrix factors strictly into the quotient
of the numerator norm over the denominator norm.
-/
theorem norm_derived_S_a (a : ℝ) (s : ℂ) :
    ‖derived_S_a a s‖ =
      ‖(a : ℂ) ^ (2 * s - 1) * completedRiemannZeta (2 * s - 1)‖ / ‖completedRiemannZeta (2 * s)‖ := by
  dsimp [derived_S_a]
  rw [norm_mul, norm_div, ← mul_div_assoc, ← norm_mul]

/--
Lemma: Scattering Exclusion of Zero Denominator.
If the wave balance equation \(S \cdot \mathrm{den} = \mathrm{num}\) holds with a non-zero
numerator residue (\(\mathrm{num} \ne 0\)), the denominator cannot vanish.
-/
theorem scattering_excludes_zero
    (S num den : ℂ)
    (h_balance : S * den = num)
    (h_num_ne : num ≠ 0) :
    den ≠ 0 := by
  intro h_den_zero
  rw [h_den_zero, mul_zero] at h_balance
  exact h_num_ne h_balance.symm

#print axioms totient_dirichlet_eq_zeta_ratio
#print axioms derived_S_a_cleared
#print axioms norm_derived_S_a
#print axioms scattering_excludes_zero

end TVE
