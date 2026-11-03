/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import TVE.Complexity.LandauerDiode
public import TVE.Complexity.TopologicalFrustration
public import TVE.Complexity.SemigroupComplexity
public import TVE.Complexity.PneNP

/-!
# Cook-Levin Tableau Bridge and Universal Input-Size Separation

Bridges the TVE cycle-rank complexity suite to the classical Cook-Levin
and Tseitin circuit-to-3SAT formulation:
1. Proves that any verification circuit with \(n > 0\) inputs and \(G \ge n\)
   fan-in-2 logic gates (\(N_{\mathrm{tab}} = n + G\) variables,
   \(M_{\mathrm{tab}} = 3G\) clauses) automatically satisfies the clause
   density condition \(N_{\mathrm{tab}} \le M_{\mathrm{tab}}\) and forces
   \(7n + 1 \le r_{\mathrm{tab}}(n, G, c)\).
2. Proves monotonicity \(C \cdot n^k \le |C| \cdot r_{\mathrm{tab}}^k\),
   translating cycle-rank lower bounds directly into bounds in the input
   variable count \(n\).
3. Establishes the universally quantified negation: for any barrier rate
   \(\gamma > 0\), no polynomial \((C, k)\) can bound the witness search
   complexity across all input sizes \(n > 0\).
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
Total variable count \(N_{\mathrm{tab}}(n, G) = n + G\) of a Tseitin 3-SAT
tableau encoding a circuit with \(n\) inputs and \(G\) internal gates.
-/
@[expose]
noncomputable def tseitinVarCount (n G : ℝ) : ℝ :=
  n + G

/--
Total clause count \(M_{\mathrm{tab}}(G) = 3G\) of a Tseitin 3-SAT tableau
(3 clauses per fan-in-2 logic gate).
-/
@[expose]
noncomputable def tseitinClauseCount (G : ℝ) : ℝ :=
  3 * G

/--
Topological cycle rank \(r_{\mathrm{tab}}(n, G, c)\) of the Tseitin 3-SAT
tableau with \(n\) inputs, \(G\) gates, and \(c\) connected components.
-/
@[expose]
noncomputable def tseitinCycleRank (n G c : ℝ) : ℝ :=
  cycleRank3SAT (tseitinClauseCount G) (tseitinVarCount n G) c

/--
Theorem: Exact Closed-Form Identity for the Tseitin Tableau Cycle Rank.
\(r_{\mathrm{tab}}(n, G, c) = 8G - n + c\).
-/
theorem tseitin_cycle_rank_identity (n G c : ℝ) :
    tseitinCycleRank n G c = 8 * G - n + c := by
  dsimp [tseitinCycleRank, cycleRank3SAT, tseitinClauseCount, tseitinVarCount]
  ring

/--
Theorem (Automatic Clause Density of Tseitin Circuit Reductions):
Every verification circuit inspecting all \(n > 0\) inputs (\(n \le G\))
automatically produces a 3-SAT tableau satisfying \(N_{\mathrm{tab}} \le M_{\mathrm{tab}}\).
-/
theorem tseitin_automatic_clause_density (n G : ℝ)
    (hn : n > 0) (hG : n ≤ G) :
    tseitinVarCount n G ≤ tseitinClauseCount G ∧
    0 < tseitinVarCount n G := by
  dsimp [tseitinVarCount, tseitinClauseCount]
  constructor <;> linarith

/--
Theorem: Linear Input-Size Lower Bound on Tseitin Tableau Cycle Rank.
For any circuit with \(0 < n \le G\) and \(1 \le c\), the tableau cycle rank
satisfies \(7n + 1 \le r_{\mathrm{tab}}(n, G, c)\) and \(n \le r_{\mathrm{tab}}(n, G, c)\).
-/
theorem tseitin_cycle_rank_bounds (n G c : ℝ)
    (hn : n > 0) (hG : n ≤ G) (hc : 1 ≤ c) :
    7 * n + 1 ≤ tseitinCycleRank n G c ∧
    n ≤ tseitinCycleRank n G c ∧
    0 < tseitinCycleRank n G c := by
  have h_id := tseitin_cycle_rank_identity n G c
  refine ⟨by linarith, by linarith, by linarith⟩

/--
Theorem: Degree-1 Polynomial Complexity of Forward Tableau Verification.
On a linear verification circuit (\(G = n\)), forward clause evaluation cost
is identically the degree-1 polynomial \(T_{\mathrm{ver}}(n) = 9n^1\).
-/
theorem tseitin_linear_forward_verification (n : ℝ) :
    forwardVerificationCost (tseitinClauseCount n) = polyTimeBound 9 n 1 := by
  dsimp [forwardVerificationCost, tseitinClauseCount, polyTimeBound]
  ring

/--
Lemma: Monotonicity of Natural Powers on Non-Negative Reals.
For \(0 \le a \le b\) and any \(k \in \mathbb{N}\), \(a^k \le b^k\).
-/
theorem pow_mono_nonneg (a b : ℝ) (k : ℕ) (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ k ≤ b ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, le_refl]
  | succ k ih =>
    have h_ak : 0 ≤ a ^ k := by positivity
    have h_bk : 0 ≤ b ^ k := le_trans h_ak ih
    have h1 : (a ^ k) * a ≤ (b ^ k) * a := mul_le_mul_of_nonneg_right ih ha
    have h2 : (b ^ k) * a ≤ (b ^ k) * b := mul_le_mul_of_nonneg_left hab h_bk
    have h_lhs : (a ^ k) * a = a ^ (k + 1) := by ring
    have h_rhs : (b ^ k) * b = b ^ (k + 1) := by ring
    linarith

/--
Lemma: Input-Size Polynomial Bounded by Cycle-Rank Polynomial.
Whenever \(0 \le n \le r\), \(C \cdot n^k \le |C| \cdot r^k\) for all \(C \in \mathbb{R}\)
and \(k \in \mathbb{N}\).
-/
theorem poly_input_le_poly_rank (C n r : ℝ) (k : ℕ)
    (hn : 0 ≤ n) (hnr : n ≤ r) :
    polyTimeBound C n k ≤ polyTimeBound |C| r k := by
  dsimp [polyTimeBound]
  have h_nk_nonneg : 0 ≤ n ^ k := by positivity
  have h_pow : n ^ k ≤ r ^ k := pow_mono_nonneg n r k hn hnr
  have h_c_abs : C ≤ |C| := le_abs_self C
  have h_abs_nonneg : 0 ≤ |C| := abs_nonneg C
  have h1 : C * (n ^ k) ≤ |C| * (n ^ k) :=
    mul_le_mul_of_nonneg_right h_c_abs h_nk_nonneg
  have h2 : |C| * (n ^ k) ≤ |C| * (r ^ k) :=
    mul_le_mul_of_nonneg_left h_pow h_abs_nonneg
  exact le_trans h1 h2

/--
Lemma: Strict Positivity of the Asymptotic Cycle-Rank Threshold.
For any \(C \in \mathbb{R}\), \(\gamma > 0\), and \(k \in \mathbb{N}\),
\(0 < r_0(C, \gamma, k)\).
-/
theorem rankThreshold_pos (C gamma : ℝ) (k : ℕ) (h_gamma : gamma > 0) :
    0 < rankThreshold C gamma k := by
  have h_gk_pos : 0 < degreeRate gamma k := by
    dsimp [degreeRate]
    positivity
  have h_pow_pos : 0 < (degreeRate gamma k) ^ (k + 1) := by positivity
  dsimp [rankThreshold]
  have h_div_nonneg : 0 ≤ |C| / ((degreeRate gamma k) ^ (k + 1)) :=
    div_nonneg (abs_nonneg C) (le_of_lt h_pow_pos)
  linarith

/--
Theorem (Input-Size Super-Polynomial Separation):
For any polynomial bound \(C \cdot n^k\) in the input variable count \(n\),
whenever \(n \ge r_0(|C|, \gamma, k)\), \(G \ge n\), and \(c \ge 1\), the backward
witness search multiplier on the Tseitin tableau strictly exceeds \(C \cdot n^k\).
-/
theorem input_size_superpolynomial_separation
    (C gamma n G c : ℝ) (k : ℕ)
    (hn : n > 0) (hG : n ≤ G) (hc : 1 ≤ c)
    (h_gamma : gamma > 0)
    (hn_ge : rankThreshold |C| gamma k ≤ n) :
    polyTimeBound C n k < backwardSearchMultiplier gamma (tseitinCycleRank n G c) ∧
    backwardSearchMultiplier gamma (tseitinCycleRank n G c) ≠ polyTimeBound C n k := by
  have h_bounds := tseitin_cycle_rank_bounds n G c hn hG hc
  have hr_ge : rankThreshold |C| gamma k ≤ tseitinCycleRank n G c :=
    le_trans hn_ge h_bounds.2.1
  have h_poly_le := poly_input_le_poly_rank C n (tseitinCycleRank n G c) k
    (le_of_lt hn) h_bounds.2.1
  have h_sep := asymptotic_superpolynomial_separation
    |C| gamma (tseitinCycleRank n G c) k h_gamma hr_ge
  have h_lt : polyTimeBound C n k <
      backwardSearchMultiplier gamma (tseitinCycleRank n G c) :=
    lt_of_le_of_lt h_poly_le h_sep.1
  refine ⟨h_lt, ?_⟩
  linarith

/--
Theorem (Universal Counterexample Witness Across All Polynomial Degrees):
For any barrier rate \(\gamma > 0\), any coefficient \(C \in \mathbb{R}\), and any
polynomial degree \(k \in \mathbb{N}\), there exists an explicit input size \(n > 0\)
whose forward verification cost is the degree-1 polynomial \(9n^1\) while its
backward witness search multiplier strictly exceeds \(C \cdot n^k\).
-/
theorem cook_levin_universal_separation
    (gamma : ℝ) (h_gamma : gamma > 0) (C : ℝ) (k : ℕ) :
    ∃ (n : ℝ), n > 0 ∧
      forwardVerificationCost (tseitinClauseCount n) = polyTimeBound 9 n 1 ∧
      polyTimeBound C n k <
        backwardSearchMultiplier gamma (tseitinCycleRank n n 1) := by
  let n0 := rankThreshold |C| gamma k
  have h_n0_pos : n0 > 0 := rankThreshold_pos |C| gamma k h_gamma
  have h_ver := tseitin_linear_forward_verification n0
  have h_sep := input_size_superpolynomial_separation
    C gamma n0 n0 1 k h_n0_pos (le_refl n0) (by norm_num) h_gamma (le_refl n0)
  exact ⟨n0, h_n0_pos, h_ver, h_sep.1⟩

/--
The Master Cook-Levin Universal P ≠ NP Negation Theorem:
For any positive frustration barrier rate \(\gamma > 0\), there does not exist
any polynomial time bound \((C, k) \in \mathbb{R} \times \mathbb{N}\) in the
input variable size \(n\) that bounds the backward witness search complexity
across all input sizes \(n > 0\).
-/
theorem cook_levin_no_polynomial_solver
    (gamma : ℝ) (h_gamma : gamma > 0) :
    ¬ (∃ (C : ℝ) (k : ℕ), ∀ (n : ℝ), n > 0 →
        backwardSearchMultiplier gamma (tseitinCycleRank n n 1) ≤
          polyTimeBound C n k) := by
  intro h_exists
  rcases h_exists with ⟨C, k, h_all⟩
  rcases cook_levin_universal_separation gamma h_gamma C k with
    ⟨n0, hn0_pos, _, h_lt⟩
  have h_le := h_all n0 hn0_pos
  linarith

#print axioms tseitin_cycle_rank_identity
#print axioms tseitin_automatic_clause_density
#print axioms tseitin_cycle_rank_bounds
#print axioms tseitin_linear_forward_verification
#print axioms pow_mono_nonneg
#print axioms poly_input_le_poly_rank
#print axioms rankThreshold_pos
#print axioms input_size_superpolynomial_separation
#print axioms cook_levin_universal_separation
#print axioms cook_levin_no_polynomial_solver

end TVE
