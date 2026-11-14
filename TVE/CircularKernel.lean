/-
Copyright (c) 2026 Truth Vector. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Truth Vector
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import TVE.Vacuum
public import TVE.Topologies

/-!
# Circular Kernel Calculus, 1D–4D Folding, Trefoil Reductions & Determinant Classification

Unifies the constructive zero-axiom Gaussian/polynomial/Diophantine circular-kernel
core with the continuum 1D–4D Steiner-jet, Sophie Germain, trefoil, denominator-inflation
sandwich classification (`ν ≤ 2 + σ`), and `Real.pi` Flint Hills isolation theorems:
- **Part 1 (Zero-Axiom Constructive Kernel):** Exact `GaussianInt` pole hierarchy,
  universal Gaussian-integer norm floor, `ExactRat` Dalzell `22/7` & TVE division,
  universal `Nat.rec` discrete determinant-sandwich collapse (`q^m < q^(m+d+1)`),
  constructive Diophantine dyadic repulsion, `U = 2h` midpoint parity factorization,
  `113 = 7² + 8²` norm, 4D Sophie Germain convolution, and 4D symplectic action balance.
- **Part 2 (Continuum ℝ / ℂ Pillars 1–6):** Preserves all original signatures and adds
  the unconditional `ν ≤ 2 + σ` denominator-inflation classification, unconditional
  `Real.pi` dyadic isolation + `ν < 5/2` spike damping threshold, 2D/4D folding, and
  log-free 3D/4D sphere-kernel trefoil/unknot reductions.
-/

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

public section

namespace TVE

/-! ## Part 1: Zero-Axiom Constructive Gaussian, Polynomial & Diophantine Kernel -/

/-- Constructive Gaussian integer `z = re + im · i ∈ ℤ[i]`. -/
structure GaussianInt where
  re : ℤ
  im : ℤ

/-- Addition in `ℤ[i]`. -/
@[expose]
def gaussAdd (a b : GaussianInt) : GaussianInt :=
  { re := a.re + b.re, im := a.im + b.im }

/-- Subtraction in `ℤ[i]`. -/
@[expose]
def gaussSub (a b : GaussianInt) : GaussianInt :=
  { re := a.re - b.re, im := a.im - b.im }

/-- Multiplication in `ℤ[i]` using pure `Int` operations. -/
@[expose]
def gaussMul (a b : GaussianInt) : GaussianInt :=
  { re := a.re * b.re - a.im * b.im,
    im := a.re * b.im + a.im * b.re }

/-- Scalar integer multiplication on `ℤ[i]`. -/
@[expose]
def gaussScale (c : ℤ) (z : GaussianInt) : GaussianInt :=
  { re := c * z.re, im := c * z.im }

/-- Squared modulus `|z|² = re² + im²` in `ℤ[i]`. -/
@[expose]
def gaussNormSq (z : GaussianInt) : ℤ :=
  z.re * z.re + z.im * z.im

/-- Exact 4th power `z⁴ = (z · z) · (z · z)` in `ℤ[i]` without `HPow`. -/
@[expose]
def gaussPow4 (z : GaussianInt) : GaussianInt :=
  let z2 := gaussMul z z
  gaussMul z2 z2

/-- Returns `true` iff `n = 0` via `Nat.casesOn`. -/
@[expose]
def ckIsZeroNat (n : ℕ) : Bool :=
  Nat.casesOn (motive := fun _ => Bool) n true (fun _ => false)

/-- Returns `true` iff `n ≥ 1` via `Nat.casesOn`. -/
@[expose]
def ckIsPosNat (n : ℕ) : Bool :=
  Nat.casesOn (motive := fun _ => Bool) n false (fun _ => true)

/-- Executable zero-axiom test `z = 0` on `ℤ`. -/
@[expose]
def ckIsZeroInt (z : ℤ) : Bool :=
  ckIsZeroNat z.toNat && ckIsZeroNat (-z).toNat

/-- Executable zero-axiom test `z > 0` on `ℤ`. -/
@[expose]
def ckIsPosInt (z : ℤ) : Bool :=
  ckIsPosNat z.toNat

/-- O(1) executable non-negativity test `0 ≤ z` on `ℤ` via `Int.casesOn`. -/
@[expose]
def ckIsNonNegInt (z : ℤ) : Bool :=
  Int.casesOn (motive := fun _ => Bool) z (fun _ => true) (fun _ => false)

/-- O(1) truncation-free strict ordering `p < q` on `ExactRat` (for `den > 0`). -/
@[expose]
def ckRatLt (p q : ExactRat) : Bool :=
  Int.casesOn (motive := fun _ => Bool) (p.num * q.den - q.num * p.den)
    (fun _ => false) (fun _ => true)

/-- Executable zero-axiom test `z = 0 + 0i` on `GaussianInt`. -/
@[expose]
def gaussIsZero (z : GaussianInt) : Bool :=
  ckIsZeroInt z.re && ckIsZeroInt z.im

/-- Evaluates the folded quartic polynomial `z⁴ + 6z² + 25` in `ℤ[i]`. -/
@[expose]
def evalFoldedDenom4Gauss (z : GaussianInt) : GaussianInt :=
  let z2 := gaussMul z z
  let z4 := gaussMul z2 z2
  gaussAdd (gaussAdd z4 (gaussScale 6 z2)) { re := 25, im := 0 }

/--
Theorem (Zero Axioms): 1D–4D Gaussian Pole & Steiner Derivative Residue Hierarchy.
-/
theorem gaussian_pole_and_residue_hierarchy :
    gaussMul { re := 0, im := 1 } { re := 1, im := -1 } = { re := 1, im := 1 } ∧
    gaussPow4 { re := 1, im := 1 } = { re := -4, im := 0 } ∧
    gaussNormSq { re := 1, im := 2 } = 5 ∧
    gaussMul { re := 1, im := 2 } { re := 1, im := 2 } = { re := -3, im := 4 } ∧
    evalFoldedDenom4Gauss { re := 1, im := 2 } = { re := 0, im := 0 } ∧
    gaussPow4 (gaussSub { re := 1, im := 0 } { re := -3, im := 4 }) =
      { re := -1024, im := 0 } ∧
    gaussNormSq { re := -11, im := 2 } = 125 ∧
    gaussNormSq { re := -3, im := 2 } = 13 ∧
    gaussNormSq { re := -4, im := 1 } = 17 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): Universal Gaussian-Integer Lattice Floor (`z = 0 ∨ |z|² ≥ 1`).
-/
theorem universal_gaussian_integer_norm_floor (z : GaussianInt) :
    (gaussIsZero z || ckIsPosInt (gaussNormSq z)) = true :=
  GaussianInt.casesOn
    (motive := fun w => (gaussIsZero w || ckIsPosInt (gaussNormSq w)) = true)
    z
    (fun a b =>
      Int.casesOn
        (motive := fun x =>
          (gaussIsZero { re := x, im := b } ||
            ckIsPosInt (gaussNormSq { re := x, im := b })) = true)
        a
        (fun na =>
          Nat.casesOn
            (motive := fun k =>
              (gaussIsZero { re := Int.ofNat k, im := b } ||
                ckIsPosInt (gaussNormSq { re := Int.ofNat k, im := b })) = true)
            na
            (Int.casesOn
              (motive := fun y =>
                (gaussIsZero { re := Int.ofNat 0, im := y } ||
                  ckIsPosInt (gaussNormSq { re := Int.ofNat 0, im := y })) = true)
              b
              (fun nb =>
                Nat.casesOn
                  (motive := fun m =>
                    (gaussIsZero { re := Int.ofNat 0, im := Int.ofNat m } ||
                      ckIsPosInt (gaussNormSq { re := Int.ofNat 0, im := Int.ofNat m })) = true)
                  nb rfl (fun _ => rfl))
              (fun _ => rfl))
            (fun ma =>
              Int.casesOn
                (motive := fun y =>
                  (gaussIsZero { re := Int.ofNat (Nat.succ ma), im := y } ||
                    ckIsPosInt (gaussNormSq { re := Int.ofNat (Nat.succ ma), im := y })) = true)
                b
                (fun nb =>
                  Nat.casesOn
                    (motive := fun m =>
                      (gaussIsZero { re := Int.ofNat (Nat.succ ma), im := Int.ofNat m } ||
                        ckIsPosInt
                          (gaussNormSq { re := Int.ofNat (Nat.succ ma), im := Int.ofNat m })) = true)
                    nb rfl (fun _ => rfl))
                (fun _ => rfl)))
        (fun ma =>
          Int.casesOn
            (motive := fun y =>
              (gaussIsZero { re := Int.negSucc ma, im := y } ||
                ckIsPosInt (gaussNormSq { re := Int.negSucc ma, im := y })) = true)
            b
            (fun nb =>
              Nat.casesOn
                (motive := fun m =>
                  (gaussIsZero { re := Int.negSucc ma, im := Int.ofNat m } ||
                    ckIsPosInt (gaussNormSq { re := Int.negSucc ma, im := Int.ofNat m })) = true)
                nb rfl (fun _ => rfl))
            (fun _ => rfl)))

/-- Exact Cauchy coefficient product `(c₆x⁶ + c₅x⁵ + c₄x⁴ + c₃x³ + c₂x² + c₁x + c₀)(x² + 1)` in `ℤ[x]`. -/
@[expose]
def polyMulDeg6CircleInt (c6 c5 c4 c3 c2 c1 c0 : ℤ) :
    ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ :=
  (c6, c5, c4 + c6, c3 + c5, c2 + c4, c1 + c3, c0 + c2, c1, c0)

/-- Exact Cauchy coefficient product `(a₂w² + a₁w + a₀)(b₂w² + b₁w + b₀)` in `ℤ[w]`. -/
@[expose]
def polyMulQuadInt (a2 a1 a0 b2 b1 b0 : ℤ) : ℤ × ℤ × ℤ × ℤ × ℤ :=
  (a2 * b2,
   a2 * b1 + a1 * b2,
   a2 * b0 + a1 * b1 + a0 * b2,
   a1 * b0 + a0 * b1,
   a0 * b0)

/-- Exact Cauchy coefficient product `(a₁w + a₀)(b₂w² + b₁w + b₀)` in `ℤ[w]`. -/
@[expose]
def polyMulLinQuadInt (a1 a0 b2 b1 b0 : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (a1 * b2,
   a1 * b1 + a0 * b2,
   a1 * b0 + a0 * b1,
   a0 * b0)

/-- Truncation-free `ExactRat` evaluation of `∫₀¹ Q₄(x) dx = 1/7 - 2/3 + 1 - 4/3 + 4`. -/
@[expose]
def dalzellAntiderivOneExact : ExactRat :=
  exactRatAdd
    (exactRatSub
      (exactRatAdd
        (exactRatSub { num := 1, den := 7 } { num := 2, den := 3 })
        { num := 1, den := 1 })
      { num := 4, den := 3 })
    { num := 4, den := 1 }

/--
Theorem (Zero Axioms): Exact Polynomial Division & `ExactRat` Convergents (`22/7` and `3`).
Proves by pure kernel reduction (`rfl`) without `ℝ` quotients that:
1. `(x⁶ - 4x⁵ + 5x⁴ - 4x² + 4)(x² + 1) - 4 = x⁸ - 4x⁷ + 6x⁶ - 4x⁵ + x⁴ = x⁴(1 - x)⁴`.
2. `dalzellAntiderivOneExact` equals `22 / 7` in `ExactRat`.
3. `(4x + 1)(x² + 1) - (3x + 1) = 4x³ + x² + x`, with `[0, 1]` quotient integral `3 / 1`.
-/
theorem dalzell_and_tve_division_exact :
    (let (d8, d7, d6, d5, d4, d3, d2, d1, d0) :=
       polyMulDeg6CircleInt 1 (-4) 5 0 (-4) 0 4
     (d8, d7, d6, d5, d4, d3, d2, d1, d0 - 4)) =
      (1, -4, 6, -4, 1, 0, 0, 0, 0) ∧
    exactRatEq dalzellAntiderivOneExact { num := 22, den := 7 } ∧
    (let (t3, t2, t1, t0) := polyMulLinQuadInt 4 1 1 0 1
     (t3, t2, t1 - 3, t0 - 1)) = (4, 1, 1, 0) ∧
    exactRatEq (exactRatAdd { num := 2, den := 1 } { num := 1, den := 1 })
      { num := 3, den := 1 } :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Constructive Zero-Axiom Determinant Sandwich & Diophantine Repulsion -/

/-- Constructive natural exponentiation `b ^ k` via primitive recursion. -/
@[expose]
def ckPowNat (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => ckPowNat b k * b

/-- Predecessor witness certifying `1 ≤ (q0 + 2) ^ k` for every `q0 k : ℕ`. -/
@[expose]
def ckPowPred (q0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (ckPowNat (q0 + 2) k * (q0 + 1)) + ckPowPred q0 k

/-- Strict positive gap predecessor `(q0 + 2)^(m + d + 1) - (q0 + 2)^m - 1`. -/
@[expose]
def ckGapPred (q0 m : ℕ) : ℕ → ℕ
  | 0 => (ckPowNat (q0 + 2) m * q0) + ckPowPred q0 m
  | d + 1 =>
    Nat.succ (ckGapPred q0 m d) +
      ((ckPowNat (q0 + 2) (m + (d + 1)) * q0) + ckPowPred q0 (m + (d + 1)))

/-- Kernel proposition `n ≠ 0` (`False` at `0`, `True` at `n + 1`). -/
@[expose]
def ckNonZeroNatProp (n : ℕ) : Prop :=
  Nat.casesOn (motive := fun _ => Prop) n False (fun _ => True)

theorem ckPowNat_eq_succ (q0 k : ℕ) :
    ckPowNat (q0 + 2) k = Nat.succ (ckPowPred q0 k) :=
  Nat.rec
    (motive := fun n => ckPowNat (q0 + 2) n = Nat.succ (ckPowPred q0 n))
    rfl
    (fun n ih =>
      congrArg (Nat.add (ckPowNat (q0 + 2) n * (q0 + 1))) ih)
    k

theorem ckPowNat_step_gap (q0 k : ℕ) :
    ckPowNat (q0 + 2) (k + 1) =
      ckPowNat (q0 + 2) k +
        Nat.succ ((ckPowNat (q0 + 2) k * q0) + ckPowPred q0 k) :=
  let P := ckPowNat (q0 + 2) k
  Eq.trans
    (vac_add_comm (P * (q0 + 1)) P)
    (congrArg (Nat.add P)
      (congrArg (Nat.add (P * q0)) (ckPowNat_eq_succ q0 k)))

theorem ck_add_succ_ne_self (a g : ℕ) : a + Nat.succ g = a → False :=
  Nat.rec
    (motive := fun x => x + Nat.succ g = x → False)
    (fun h0 =>
      let hs : Nat.succ g = 0 := Eq.trans (vac_zero_add (Nat.succ g)).symm h0
      Eq.mp (congrArg ckNonZeroNatProp hs) trivial)
    (fun x ih hx =>
      let hp : Nat.succ x + g = x := congrArg Nat.pred hx
      ih (Eq.trans (vac_succ_add x g).symm hp))
    a

/--
Theorem (Zero Axioms): Universal Discrete Determinant Sandwich Collapse over `ℕ`.
Proves for ALL integer bases `q = q0 + 2 ≥ 2`, ALL cleared floor exponents `m`,
ALL positive exponent excesses `d + 1 ≥ 1` (`n = m + (d + 1)`), and ALL `D u v : ℕ`:
1. `q^(m + d + 1) = q^m + (ckGapPred + 1)` (`q^m < q^n` constructively).
2. No cleared determinant `D` can simultaneously satisfy `q^n + u = D` (`q^n ≤ D`)
   and `D + v = q^m` (`D ≤ q^m`).
-/
theorem discrete_determinant_sandwich_collapse_nat
    (q0 m d D u v : ℕ) :
    ckPowNat (q0 + 2) (m + (d + 1)) =
      ckPowNat (q0 + 2) m + Nat.succ (ckGapPred q0 m d) ∧
    (ckPowNat (q0 + 2) (m + (d + 1)) + u = D →
     D + v = ckPowNat (q0 + 2) m → False) :=
  let h_mono :
      ckPowNat (q0 + 2) (m + (d + 1)) =
        ckPowNat (q0 + 2) m + Nat.succ (ckGapPred q0 m d) :=
    Nat.rec
      (motive := fun n =>
        ckPowNat (q0 + 2) (m + (n + 1)) =
          ckPowNat (q0 + 2) m + Nat.succ (ckGapPred q0 m n))
      (ckPowNat_step_gap q0 m)
      (fun n ih =>
        let k := m + (n + 1)
        let Ek := (ckPowNat (q0 + 2) k * q0) + ckPowPred q0 k
        Eq.trans (ckPowNat_step_gap q0 k)
          (Eq.trans
            (congrArg (fun t => t + Nat.succ Ek) ih)
            (vac_add_assoc (ckPowNat (q0 + 2) m)
              (Nat.succ (ckGapPred q0 m n)) (Nat.succ Ek))))
      d
  ⟨h_mono,
   fun h_fl h_cl =>
    let M := ckPowNat (q0 + 2) m
    let G := ckGapPred q0 m d
    let e1 : (M + Nat.succ G) + u = D :=
      Eq.trans (congrArg (fun t => t + u) h_mono.symm) h_fl
    let e2 : ((M + Nat.succ G) + u) + v = M :=
      Eq.trans (congrArg (fun t => t + v) e1) h_cl
    let s1 := vac_add_assoc M (Nat.succ G) u
    let s2 := vac_add_assoc M (Nat.succ G + u) v
    let s3 := vac_succ_add G u
    let s4 := vac_succ_add (G + u) v
    let s34 : (Nat.succ G + u) + v = Nat.succ ((G + u) + v) :=
      Eq.trans (congrArg (fun t => t + v) s3) s4
    let lhs_eq : ((M + Nat.succ G) + u) + v = M + Nat.succ ((G + u) + v) :=
      Eq.trans (congrArg (fun t => t + v) s1)
        (Eq.trans s2 (congrArg (Nat.add M) s34))
    ck_add_succ_ne_self M ((G + u) + v) (Eq.trans lhs_eq.symm e2)⟩

theorem ck_int_sq_nonneg (z : ℤ) : ckIsNonNegInt (z * z) = true :=
  Int.casesOn (motive := fun w => ckIsNonNegInt (w * w) = true) z
    (fun _ => rfl)
    (fun _ => rfl)

/--
Theorem (Zero Axioms): Constructive Diophantine Parallelogram Law & Dyadic `[1, 8]` Witness.
Proves with zero axioms that:
1. For ALL integer error terms `e1 e2 : ℤ`, `2(e₁² + e₂²) - (e₁ - e₂)² = (e₁ + e₂)² ≥ 0`.
2. In dyadic block `Q_blk = 8` (`8⁴ = 4096`) around `355 / 113`, `22 / 7` and `25 / 8`
   have unit cross-difference `22*8 - 25*7 = 1`, `22 / 7` lies inside `< 1 / 4`, and
   `25 / 8` is strictly repelled outside `> 1 / 4`.
-/
theorem universal_diophantine_dyadic_repulsion_int (e1 e2 : ℤ) :
    ckIsNonNegInt ((e1 + e2) * (e1 + e2)) = true ∧
    (22 : ℤ) * 8 - 25 * 7 = 1 ∧
    ckRatLt { num := 4096, den := 625681 } { num := 1, den := 4 } = true ∧
    ckRatLt { num := 1, den := 4 } { num := 921600, den := 817216 } = true :=
  ⟨ck_int_sq_nonneg (e1 + e2), rfl, rfl, rfl⟩

/-- Scaled Steiner polynomial `8 P(U, h; x) = 16 U x³ + 4 U x² + 8 h x`. -/
@[expose]
def steinerScaled8Int (U h x : ℤ) : ℤ :=
  16 * U * x * x * x + 4 * U * x * x + 8 * h * x

/-- Midpoint-folded Steiner polynomial `8 P(U, h; (1 + y)/2)` decomposed into even + odd parts. -/
@[expose]
def midpointSteiner8Int (U h y : ℤ) : ℤ :=
  ((3 * U + 4 * h) + 7 * U * y * y) +
  2 * y * ((4 * U + 2 * h) + U * y * y)

/-- Odd-parity factorization defect `(4U + 2h) - 5U = 2h - U` relative to `(5 + y²)`. -/
@[expose]
def midpointOddFactorDefectInt (U h : ℤ) : ℤ :=
  (4 * U + 2 * h) - 5 * U

/--
Theorem (Zero Axioms): Bidirectional Midpoint Folding, `U = 2h` Factorization & `113` Norm.
-/
theorem midpoint_folding_and_113_norm_int :
    midpointOddFactorDefectInt 2 1 = 0 ∧
    steinerScaled8Int 2 1 0 = midpointSteiner8Int 2 1 (-1) ∧
    steinerScaled8Int 2 1 1 = midpointSteiner8Int 2 1 1 ∧
    steinerScaled8Int 2 1 2 = midpointSteiner8Int 2 1 3 ∧
    steinerScaled8Int 2 1 3 = midpointSteiner8Int 2 1 5 ∧
    7 * 7 + 8 * 8 = 113 ∧
    64 * (10 + 1) / 2 = 352 ∧
    352 + 3 = 355 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Coefficient-level parity reflection `u ↦ -u` on `a₂u² + a₁u + a₀`. -/
@[expose]
def polyParityFlipQuadInt (a2 a1 a0 : ℤ) : ℤ × ℤ × ℤ :=
  (a2, -a1, a0)

/-- Parity-twin radial quartic factors `D₄(u) = u² - 8u + 32` and `Q_4D(u) = u² + 8u + 32`. -/
@[expose]
def parityTwinMinusInt (u : ℤ) : ℤ := u * u - 8 * u + 32

@[expose]
def parityTwinPlusInt (u : ℤ) : ℤ := u * u + 8 * u + 32

/--
Theorem (Zero Axioms): 4D Sophie Germain Polynomial Identity & Level `(1,1)` / `(1,2)` Phase-Locks.
-/
theorem sophie_germain_4d_and_phase_lock_int :
    polyMulQuadInt 1 (-10) 41 1 6 25 = (1, -4, 6, -4, 1025) ∧
    polyParityFlipQuadInt 1 (-8) 32 = (1, 8, 32) ∧
    parityTwinMinusInt (-1) = parityTwinPlusInt 1 ∧
    parityTwinMinusInt (-2) = parityTwinPlusInt 2 ∧
    parityTwinMinusInt (-3) = parityTwinPlusInt 3 ∧
    polyMulQuadInt 1 (-8) 32 1 8 32 = (1, 0, 0, 0, 1024) ∧
    (let (c3, c2, c1, c0) := polyMulLinQuadInt 1 (-16) 1 6 25
     (c3, c2, c1 + 80, c0 + 400)) = (1, -10, 9, 0) ∧
    (let (d4, d3, d2, d1, d0) := polyMulQuadInt 1 3 (-64) 1 6 25
     (d4, d3, d2, d1 + 320, d0 + 1600)) = (1, 9, -21, 11, 0) ∧
    1 + 5 - 320 = -314 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Theorem (Zero Axioms): 4D Symplectic Action Fixed Point & Higher-Sphere Boundary Jumps.
-/
theorem higher_sphere_and_symplectic_action_int :
    (3 * (2 : ℤ), (2 : ℤ), 3 * (1 : ℤ)) = (6, 2, 3) ∧
    3 * (2 * (1 : ℤ) - 2) = 0 ∧
    (let (q4, q3, q2, q1, q0) := polyMulQuadInt 18 (-2) (-11) 1 0 1
     (q4, q3, q2, q1, q0 + 11)) = (18, -2, 7, -2, 0) ∧
    -(11 + 2) + 2 * 2 = -9 ∧
    -(3 + 2) + 2 * 2 = -1 ∧
    ((3 + 5 - 24) - (-24 * 4)) / 16 = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 2: Continuum ℝ / ℂ Circular-Kernel Pillars (1D → 4D + Trefoil) -/

/-! ### Pillar 1: Topological Derivation of `P'(x) = 12x² + 2x + 1` and Weight `24` -/

/--
Parametric Steiner-Minkowski torus phase-space polynomial in terms of the
flux-tube aspect ratio `U = R / a` and magnetic helicity quantum `h`:
`P(U, h; x) = (2U)x³ + (U/2)x² + hx`.
-/
@[expose]
noncomputable def tveSteinerTubePoly (U h x : ℝ) : ℝ :=
  (2 * U) * (x ^ 3) + (U / 2) * (x ^ 2) + h * x

/--
First radial derivative (boundary flux Jacobian) of `tveSteinerTubePoly`:
`P'(U, h; x) = (6U)x² + Ux + h`.
-/
@[expose]
noncomputable def tveSteinerFirstDeriv (U h x : ℝ) : ℝ :=
  (6 * U) * (x ^ 2) + U * x + h

/--
Second radial derivative (mean curvature stiffness) of `tveSteinerTubePoly`:
`P''(U, h; x) = (12U)x + U`.
-/
@[expose]
noncomputable def tveSteinerSecondDeriv (U h x : ℝ) : ℝ :=
  (12 * U) * x + U

/--
Third radial derivative (topological bulk weight) of `tveSteinerTubePoly`:
`P'''(U, h; x) = 12U`.
-/
@[expose]
noncomputable def tveSteinerThirdDeriv (U : ℝ) : ℝ :=
  12 * U

/--
Theorem (Topological Derivation of the TVE Polynomial & Its Derivative Jet):
-/
theorem tve_steiner_polynomial_from_unknot
    (a x eps : ℝ) (ha : a ≠ 0) :
    tveSteinerTubePoly (aspectRatio (electronUnknot a)) 1 Real.pi = alphaInv ∧
    tveSteinerTubePoly (aspectRatio (electronUnknot a)) 1 (x + eps) -
      tveSteinerTubePoly (aspectRatio (electronUnknot a)) 1 x =
      (tveSteinerFirstDeriv (aspectRatio (electronUnknot a)) 1 x) * eps +
      (tveSteinerSecondDeriv (aspectRatio (electronUnknot a)) 1 x / 2) * (eps ^ 2) +
      (tveSteinerThirdDeriv (aspectRatio (electronUnknot a)) / 6) * (eps ^ 3) ∧
    tveSteinerFirstDeriv (aspectRatio (electronUnknot a)) 1 x =
      12 * (x ^ 2) + 2 * x + 1 ∧
    tveSteinerSecondDeriv (aspectRatio (electronUnknot a)) 1 x =
      24 * x + 2 ∧
    tveSteinerThirdDeriv (aspectRatio (electronUnknot a)) = 24 := by
  dsimp [tveSteinerTubePoly, tveSteinerFirstDeriv,
         tveSteinerSecondDeriv, tveSteinerThirdDeriv]
  rw [electron_aspect_ratio a ha, alphaInv_val]
  refine ⟨by ring, by ring, by ring, by ring, by ring⟩

/-! ### Pillar 2: Dalzell & TVE Circular Kernel `1 / (1 + x²)` Decomposition -/

/--
Polynomial quotient `Q₄(x) = x⁶ - 4x⁵ + 5x⁴ - 4x² + 4` obtained by dividing
the boundary-vanishing Dalzell wave packet `x⁴(1 - x)⁴` by `1 + x²`.
-/
@[expose]
def dalzellQuotient4 (x : ℝ) : ℝ :=
  x ^ 6 - 4 * (x ^ 5) + 5 * (x ^ 4) - 4 * (x ^ 2) + 4

/--
Exact polynomial antiderivative `∫ Q₄(x) dx` of `dalzellQuotient4`.
-/
@[expose]
noncomputable def dalzellAntideriv4 (x : ℝ) : ℝ :=
  (x ^ 7) / 7 - (2 * (x ^ 6)) / 3 + (x ^ 5) - (4 * (x ^ 3)) / 3 + 4 * x

/--
Exact polynomial antiderivative `∫ (4x + 1) dx = 2x² + x` of the TVE
circular-kernel quotient `4x + 1`.
-/
@[expose]
def tveQuotientAntideriv (x : ℝ) : ℝ :=
  2 * (x ^ 2) + x

/--
Theorem (Dalzell `22/7` & TVE Torus Polynomial Circular Kernel Identities):
-/
theorem dalzell_and_tve_circular_kernel_identities (x : ℝ) :
    (x ^ 4 * ((1 - x) ^ 4)) / (1 + x ^ 2) =
      dalzellQuotient4 x - 4 / (1 + x ^ 2) ∧
    dalzellAntideriv4 1 - dalzellAntideriv4 0 = 22 / 7 ∧
    (4 * (x ^ 3) + x ^ 2 + x) / (1 + x ^ 2) =
      (4 * x + 1) - (3 * x) / (1 + x ^ 2) - 1 / (1 + x ^ 2) ∧
    tveQuotientAntideriv 1 - tveQuotientAntideriv 0 = 3 := by
  have h_denom : 1 + x ^ 2 ≠ 0 := by positivity
  have h_dalz_poly :
      x ^ 4 * ((1 - x) ^ 4) =
        (dalzellQuotient4 x) * (1 + x ^ 2) - 4 := by
    dsimp [dalzellQuotient4]
    ring
  have h_dalz_div :
      (x ^ 4 * ((1 - x) ^ 4)) / (1 + x ^ 2) =
        dalzellQuotient4 x - 4 / (1 + x ^ 2) := by
    calc (x ^ 4 * ((1 - x) ^ 4)) / (1 + x ^ 2)
      _ = ((dalzellQuotient4 x) * (1 + x ^ 2) - 4) / (1 + x ^ 2) := by
          rw [h_dalz_poly]
      _ = ((dalzellQuotient4 x) * (1 + x ^ 2)) / (1 + x ^ 2) -
            4 / (1 + x ^ 2) := by ring
      _ = dalzellQuotient4 x - 4 / (1 + x ^ 2) := by
          rw [mul_div_cancel_right₀ _ h_denom]
  have h_tve_poly :
      4 * (x ^ 3) + x ^ 2 + x =
        (4 * x + 1) * (1 + x ^ 2) - 3 * x - 1 := by
    ring
  have h_tve_div :
      (4 * (x ^ 3) + x ^ 2 + x) / (1 + x ^ 2) =
        (4 * x + 1) - (3 * x) / (1 + x ^ 2) - 1 / (1 + x ^ 2) := by
    calc (4 * (x ^ 3) + x ^ 2 + x) / (1 + x ^ 2)
      _ = ((4 * x + 1) * (1 + x ^ 2) - 3 * x - 1) / (1 + x ^ 2) := by
          rw [h_tve_poly]
      _ = ((4 * x + 1) * (1 + x ^ 2)) / (1 + x ^ 2) -
            (3 * x) / (1 + x ^ 2) - 1 / (1 + x ^ 2) := by ring
      _ = (4 * x + 1) - (3 * x) / (1 + x ^ 2) - 1 / (1 + x ^ 2) := by
          rw [mul_div_cancel_right₀ _ h_denom]
  refine ⟨h_dalz_div, ?_, h_tve_div, ?_⟩
  · dsimp [dalzellAntideriv4]
    norm_num
  · dsimp [tveQuotientAntideriv]
    norm_num

/--
Theorem (Gaussian-Integer Kernel Periodicity `(i(1 - i))⁴ = (1 + i)⁴ = -4`):
-/
theorem gaussian_unit_fourth_power_eq_neg_four :
    Complex.I * (1 - Complex.I) = 1 + Complex.I ∧
    (Complex.I * (1 - Complex.I)) ^ 4 = (-4 : ℂ) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h_base : Complex.I * (1 - Complex.I) = 1 + Complex.I := by
    calc Complex.I * (1 - Complex.I)
      _ = Complex.I - Complex.I ^ 2 := by ring
      _ = Complex.I - (-1) := by rw [hI]
      _ = 1 + Complex.I := by ring
  refine ⟨h_base, ?_⟩
  rw [h_base]
  calc (1 + Complex.I) ^ 4
    _ = ((1 + Complex.I) ^ 2) ^ 2 := by ring
    _ = (1 + 2 * Complex.I + Complex.I ^ 2) ^ 2 := by ring
    _ = (1 + 2 * Complex.I + (-1)) ^ 2 := by rw [hI]
    _ = 4 * (Complex.I ^ 2) := by ring
    _ = 4 * (-1) := by rw [hI]
    _ = (-4 : ℂ) := by ring

/-! ### Pillar 3: Gaussian-Integer Floor & Exact `ν ≤ 2 + σ` Denominator-Inflation Classification -/

/--
Theorem (Gaussian-Integer Lattice Floor `|α|² ≥ 1` & Arithmetic Lower Bound `L`):
-/
theorem gaussian_integer_norm_floor
    (a b : ℤ) (delta_denom : ℝ)
    (h_nz : a ≠ 0 ∨ b ≠ 0) (h_delta : 0 < delta_denom) :
    1 ≤ a ^ 2 + b ^ 2 ∧
    1 / (delta_denom ^ 2) ≤
      ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (delta_denom ^ 2) := by
  have h_int : 1 ≤ a ^ 2 + b ^ 2 := by
    rcases h_nz with ha | hb
    · have hb_sq : 0 ≤ b ^ 2 := sq_nonneg b
      have ha_cases : a ≤ -1 ∨ 1 ≤ a := by omega
      rcases ha_cases with h_neg | h_pos
      · have h1 : a + 1 ≤ 0 := by omega
        have h2 : a - 1 ≤ 0 := by omega
        have h_mul : 0 ≤ (a + 1) * (a - 1) :=
          mul_nonneg_of_nonpos_of_nonpos h1 h2
        have h_id : (a + 1) * (a - 1) = a ^ 2 - 1 := by ring
        linarith
      · have h1 : 0 ≤ a - 1 := by omega
        have h2 : 0 ≤ a + 1 := by omega
        have h_mul : 0 ≤ (a - 1) * (a + 1) := mul_nonneg h1 h2
        have h_id : (a - 1) * (a + 1) = a ^ 2 - 1 := by ring
        linarith
    · have ha_sq : 0 ≤ a ^ 2 := sq_nonneg a
      have hb_cases : b ≤ -1 ∨ 1 ≤ b := by omega
      rcases hb_cases with h_neg | h_pos
      · have h1 : b + 1 ≤ 0 := by omega
        have h2 : b - 1 ≤ 0 := by omega
        have h_mul : 0 ≤ (b + 1) * (b - 1) :=
          mul_nonneg_of_nonpos_of_nonpos h1 h2
        have h_id : (b + 1) * (b - 1) = b ^ 2 - 1 := by ring
        linarith
      · have h1 : 0 ≤ b - 1 := by omega
        have h2 : 0 ≤ b + 1 := by omega
        have h_mul : 0 ≤ (b - 1) * (b + 1) := mul_nonneg h1 h2
        have h_id : (b - 1) * (b + 1) = b ^ 2 - 1 := by ring
        linarith
  have h_real : ((1 : ℤ) : ℝ) ≤ ((a ^ 2 + b ^ 2 : ℤ) : ℝ) :=
    Int.cast_le.mpr h_int
  push_cast at h_real
  have h_inv_nonneg : 0 ≤ 1 / (delta_denom ^ 2) := by positivity
  have h_div := mul_le_mul_of_nonneg_right h_real h_inv_nonneg
  have h_lhs : 1 * (1 / (delta_denom ^ 2)) = 1 / (delta_denom ^ 2) := by ring
  have h_rhs :
      ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) * (1 / (delta_denom ^ 2)) =
        ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) / (delta_denom ^ 2) := by ring
  exact ⟨h_int, by linarith⟩

/--
Uninflated (`σ = 0`) arithmetic floor `L(K, log_q) = exp(-2 K log_q) = q^(-2K)`
of an LCM-free 2D topological `(p, q) ∈ ℤ²` lattice.
-/
@[expose]
noncomputable def arithmeticDeterminantFloor (K_jet log_q : ℝ) : ℝ :=
  Real.exp (-2 * K_jet * log_q)

/--
Denominator-inflated arithmetic floor `L_σ(K, log_q) = exp(-(2 + σ) K log_q)`
accounting for rational antiderivative LCM inflation rate `σ ≥ 0`.
-/
@[expose]
noncomputable def inflatedDeterminantFloor (sigma_inf K_jet log_q : ℝ) : ℝ :=
  Real.exp (-(2 + sigma_inf) * K_jet * log_q)

/--
Analytic ceiling `U(ν, K, log_q) = exp(-ν K log_q) = q^(-νK)` produced by
Taylor jet cancellation of order `K` at approximation exponent `ν`.
-/
@[expose]
noncomputable def analyticDeterminantCeiling (nu K_jet log_q : ℝ) : ℝ :=
  Real.exp (-nu * K_jet * log_q)

/--
Theorem (Unconditional `ν ≤ 2 + σ` Denominator-Inflation Sandwich Classification):
Classifies the exact boundary between classical Padé/Dalzell LCM inflation (`σ > 0`,
yielding `ν ≤ 2 + σ`) and LCM-free topological winding lattices (`σ = 0`, yielding `ν ≤ 2`):
1. At `σ = 0`, `inflatedDeterminantFloor 0` coincides identically with `arithmeticDeterminantFloor`.
2. For all `K_jet > 0` and `log_q > 0`, `U(ν) < L_σ` holds if and only if `2 + σ < ν`.
3. Whenever `2 + σ < ν`, no determinant `D_abs` can satisfy `L_σ ≤ D_abs ≤ U(ν)`.
-/
theorem determinant_sandwich_inflation_classification
    (nu sigma_inf K_jet log_q D_abs : ℝ)
    (hK : 0 < K_jet) (hq : 0 < log_q) :
    inflatedDeterminantFloor 0 K_jet log_q =
      arithmeticDeterminantFloor K_jet log_q ∧
    (analyticDeterminantCeiling nu K_jet log_q <
       inflatedDeterminantFloor sigma_inf K_jet log_q ↔
     2 + sigma_inf < nu) ∧
    (2 + sigma_inf < nu →
     ¬ (inflatedDeterminantFloor sigma_inf K_jet log_q ≤ D_abs ∧
        D_abs ≤ analyticDeterminantCeiling nu K_jet log_q)) := by
  have h_zero_sigma :
      inflatedDeterminantFloor 0 K_jet log_q =
        arithmeticDeterminantFloor K_jet log_q := by
    dsimp [inflatedDeterminantFloor, arithmeticDeterminantFloor]
    congr 1
    ring
  have h_iff :
      analyticDeterminantCeiling nu K_jet log_q <
        inflatedDeterminantFloor sigma_inf K_jet log_q ↔
      2 + sigma_inf < nu := by
    dsimp [analyticDeterminantCeiling, inflatedDeterminantFloor]
    constructor
    · intro h_lt
      rcases lt_or_ge (2 + sigma_inf) nu with h_ok | h_ge
      · exact h_ok
      · have h_diff_nonpos : nu - (2 + sigma_inf) ≤ 0 := by linarith
        have hKq_nonneg : 0 ≤ K_jet * log_q := by positivity
        have h_prod_nonpos :
            (nu - (2 + sigma_inf)) * (K_jet * log_q) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h_diff_nonpos hKq_nonneg
        have h_arg_nonpos :
            (nu - (2 + sigma_inf)) * K_jet * log_q ≤ 0 := by linarith
        have h_exp_le :
            Real.exp ((nu - (2 + sigma_inf)) * K_jet * log_q) ≤ 1 :=
          Real.exp_le_one_iff.mpr h_arg_nonpos
        have h_u_pos : 0 < Real.exp (-nu * K_jet * log_q) :=
          Real.exp_pos (-nu * K_jet * log_q)
        have h_mul :=
          mul_le_mul_of_nonneg_right h_exp_le (le_of_lt h_u_pos)
        rw [← Real.exp_add, one_mul] at h_mul
        have h_arg_eq :
            (nu - (2 + sigma_inf)) * K_jet * log_q + (-nu * K_jet * log_q) =
              -(2 + sigma_inf) * K_jet * log_q := by ring
        rw [h_arg_eq] at h_mul
        linarith
    · intro h_gt
      have h_diff_pos : 0 < nu - (2 + sigma_inf) := by linarith
      have h_prod_pos : 0 < (nu - (2 + sigma_inf)) * K_jet * log_q := by positivity
      have h_not_le : ¬ ((nu - (2 + sigma_inf)) * K_jet * log_q ≤ 0) := by linarith
      have h_not_exp_le :
          ¬ (Real.exp ((nu - (2 + sigma_inf)) * K_jet * log_q) ≤ 1) :=
        mt Real.exp_le_one_iff.mp h_not_le
      have h_exp_gt_one :
          1 < Real.exp ((nu - (2 + sigma_inf)) * K_jet * log_q) :=
        not_le.mp h_not_exp_le
      have h_u_pos : 0 < Real.exp (-nu * K_jet * log_q) :=
        Real.exp_pos (-nu * K_jet * log_q)
      have h_mul := mul_lt_mul_of_pos_right h_exp_gt_one h_u_pos
      rw [← Real.exp_add, one_mul] at h_mul
      have h_arg_eq :
          (nu - (2 + sigma_inf)) * K_jet * log_q + (-nu * K_jet * log_q) =
            -(2 + sigma_inf) * K_jet * log_q := by ring
      rw [h_arg_eq] at h_mul
      exact h_mul
  refine ⟨h_zero_sigma, h_iff, ?_⟩
  intro h_nu_gt ⟨h_fl, h_cl⟩
  have h_lt := h_iff.mpr h_nu_gt
  linarith

/--
Corollary (`σ = 0` LCM-Free Limit, Preserving Legacy Signature):
-/
theorem determinant_sandwich_exponent_two_collapse
    (nu K_jet log_q D_abs : ℝ)
    (h_nu : 2 < nu) (hK : 0 < K_jet) (hq : 0 < log_q) :
    analyticDeterminantCeiling nu K_jet log_q <
      arithmeticDeterminantFloor K_jet log_q ∧
    ¬ (arithmeticDeterminantFloor K_jet log_q ≤ D_abs ∧
       D_abs ≤ analyticDeterminantCeiling nu K_jet log_q) := by
  have h_cls := determinant_sandwich_inflation_classification nu 0 K_jet log_q D_abs hK hq
  have h_gt : 2 + (0 : ℝ) < nu := by linarith
  have h_lt := h_cls.2.1.mpr h_gt
  have h_no := h_cls.2.2 h_gt
  rw [h_cls.1] at h_lt h_no
  exact ⟨h_lt, h_no⟩

/-! ### Pillar 4: Diophantine Dyadic Repulsion & Unconditional `Real.pi` Flint Hills Isolation -/

/--
Theorem (Diophantine Fraction Repulsion Across Dyadic Denominator Blocks):
-/
theorem diophantine_dyadic_repulsion
    (p1 q1 p2 q2 Q_blk pi_val : ℝ) (cross_int : ℤ)
    (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hq1_le : q1 ≤ Q_blk) (hq2_le : q2 ≤ Q_blk)
    (h_cross_ne : cross_int ≠ 0)
    (h_cross_eq : (cross_int : ℝ) = p1 * q2 - p2 * q1) :
    1 ≤ ((p1 / q1 - p2 / q2) * (q1 * q2)) ^ 2 ∧
    ¬ (((p1 / q1 - pi_val) ^ 2) * (Q_blk ^ 4) < 1 / 4 ∧
       ((p2 / q2 - pi_val) ^ 2) * (Q_blk ^ 4) < 1 / 4) := by
  have hq1_ne : q1 ≠ 0 := ne_of_gt hq1
  have hq2_ne : q2 ≠ 0 := ne_of_gt hq2
  have h_norm := (gaussian_integer_norm_floor cross_int 0 1
    (Or.inl h_cross_ne) (by norm_num)).2
  have h_cross_sq : 1 ≤ (p1 * q2 - p2 * q1) ^ 2 := by
    rw [h_cross_eq] at h_norm
    linarith
  have h_frac_id :
      (p1 / q1 - p2 / q2) * (q1 * q2) = p1 * q2 - p2 * q1 := by
    have h1 :
        (p1 / q1 - p2 / q2) * (q1 * q2) =
          ((p1 / q1) * q1) * q2 - ((p2 / q2) * q2) * q1 := by ring
    rw [h1, div_mul_cancel₀ p1 hq1_ne, div_mul_cancel₀ p2 hq2_ne]
  have h_sep_ge_one : 1 ≤ ((p1 / q1 - p2 / q2) * (q1 * q2)) ^ 2 := by
    rw [h_frac_id]
    exact h_cross_sq
  refine ⟨h_sep_ge_one, ?_⟩
  rintro ⟨h_close1, h_close2⟩
  have h_prod_le : q1 * q2 ≤ Q_blk ^ 2 := by
    have h_m1 : q1 * q2 ≤ Q_blk * q2 :=
      mul_le_mul_of_nonneg_right hq1_le (le_of_lt hq2)
    have h_m2 : Q_blk * q2 ≤ Q_blk * Q_blk :=
      mul_le_mul_of_nonneg_left hq2_le (le_trans (le_of_lt hq1) hq1_le)
    linarith [show Q_blk * Q_blk = Q_blk ^ 2 by ring]
  have h_prod_nonneg : 0 ≤ q1 * q2 := by positivity
  have h_sq_le : (q1 * q2) ^ 2 ≤ Q_blk ^ 4 := by
    have h_sum_nonneg : 0 ≤ Q_blk ^ 2 + q1 * q2 := by positivity
    have h_diff_nonneg : 0 ≤ Q_blk ^ 2 - q1 * q2 := by linarith
    have h_f := mul_nonneg h_sum_nonneg h_diff_nonneg
    linarith [show (Q_blk ^ 2 + q1 * q2) * (Q_blk ^ 2 - q1 * q2) =
                Q_blk ^ 4 - (q1 * q2) ^ 2 by ring]
  have h_diff_sq_nonneg : 0 ≤ (p1 / q1 - p2 / q2) ^ 2 :=
    sq_nonneg (p1 / q1 - p2 / q2)
  have h_scale_le :
      ((p1 / q1 - p2 / q2) * (q1 * q2)) ^ 2 ≤
        ((p1 / q1 - p2 / q2) ^ 2) * (Q_blk ^ 4) := by
    have h_mul := mul_le_mul_of_nonneg_left h_sq_le h_diff_sq_nonneg
    linarith [show ((p1 / q1 - p2 / q2) * (q1 * q2)) ^ 2 =
                ((p1 / q1 - p2 / q2) ^ 2) * ((q1 * q2) ^ 2) by ring]
  have h_parallelogram :
      0 ≤ ((p1 / q1 - pi_val) + (p2 / q2 - pi_val)) ^ 2 :=
    sq_nonneg ((p1 / q1 - pi_val) + (p2 / q2 - pi_val))
  have h_tri_sq :
      (p1 / q1 - p2 / q2) ^ 2 ≤
        2 * ((p1 / q1 - pi_val) ^ 2 + (p2 / q2 - pi_val) ^ 2) := by
    linarith [show ((p1 / q1 - pi_val) + (p2 / q2 - pi_val)) ^ 2 =
                2 * ((p1 / q1 - pi_val) ^ 2 + (p2 / q2 - pi_val) ^ 2) -
                  (p1 / q1 - p2 / q2) ^ 2 by ring]
  have hQ4_nonneg : 0 ≤ Q_blk ^ 4 := by positivity
  have h_tri_scaled := mul_le_mul_of_nonneg_right h_tri_sq hQ4_nonneg
  linarith

/--
Theorem (Unconditional `Real.pi` Dyadic Spike Isolation & `ν < 5 / 2` Damping Threshold):
1. Instantiates `diophantine_dyadic_repulsion` directly at `Real.pi` (no free target variable):
   at most ONE distinct fraction `p / q` in `0 < q ≤ Q_blk` can enter `(p/q - π)² Q_blk⁴ < 1/4`.
2. Proves unconditionally for any `log_Q > 0` that the single remaining dyadic resonant spike
   `exp((2ν - 5) log_Q) = Q^(2ν - 5)` is strictly damped (`1 < Q^(5 - 2ν)` and `Q^(2ν - 5) < 1`)
   whenever `ν < 5 / 2`.
-/
theorem flint_hills_real_pi_dyadic_isolation_and_spike_threshold
    (p1 q1 p2 q2 Q_blk nu log_Q : ℝ) (cross_int : ℤ)
    (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hq1_le : q1 ≤ Q_blk) (hq2_le : q2 ≤ Q_blk)
    (h_cross_ne : cross_int ≠ 0)
    (h_cross_eq : (cross_int : ℝ) = p1 * q2 - p2 * q1)
    (hQ : 0 < log_Q) :
    ¬ (((p1 / q1 - Real.pi) ^ 2) * (Q_blk ^ 4) < 1 / 4 ∧
       ((p2 / q2 - Real.pi) ^ 2) * (Q_blk ^ 4) < 1 / 4) ∧
    (1 < Real.exp ((5 - 2 * nu) * log_Q) ↔ nu < 5 / 2) ∧
    (nu < 5 / 2 → Real.exp ((2 * nu - 5) * log_Q) < 1) := by
  have h_iso :=
    (diophantine_dyadic_repulsion p1 q1 p2 q2 Q_blk Real.pi cross_int
      hq1 hq2 hq1_le hq2_le h_cross_ne h_cross_eq).2
  have h_iff : 1 < Real.exp ((5 - 2 * nu) * log_Q) ↔ nu < 5 / 2 := by
    constructor
    · intro h_gt
      have h_not_exp : ¬ (Real.exp ((5 - 2 * nu) * log_Q) ≤ 1) := not_le.mpr h_gt
      have h_not_arg : ¬ ((5 - 2 * nu) * log_Q ≤ 0) :=
        mt Real.exp_le_one_iff.mpr h_not_exp
      rcases lt_or_ge nu (5 / 2) with h_lt | h_ge
      · exact h_lt
      · have h_nonpos : 5 - 2 * nu ≤ 0 := by linarith
        have h_prod_nonpos : (5 - 2 * nu) * log_Q ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h_nonpos (le_of_lt hQ)
        exact False.elim (h_not_arg h_prod_nonpos)
    · intro h_lt
      have h_diff_pos : 0 < 5 - 2 * nu := by linarith
      have h_prod_pos : 0 < (5 - 2 * nu) * log_Q := mul_pos h_diff_pos hQ
      have h_not_arg : ¬ ((5 - 2 * nu) * log_Q ≤ 0) := by linarith
      have h_not_exp : ¬ (Real.exp ((5 - 2 * nu) * log_Q) ≤ 1) :=
        mt Real.exp_le_one_iff.mp h_not_arg
      exact not_le.mp h_not_exp
  refine ⟨h_iso, h_iff, ?_⟩
  intro h_lt
  have h_gt := h_iff.mpr h_lt
  have he_pos : 0 < Real.exp ((2 * nu - 5) * log_Q) :=
    Real.exp_pos ((2 * nu - 5) * log_Q)
  have h_mul := mul_lt_mul_of_pos_right h_gt he_pos
  rw [← Real.exp_add, one_mul] at h_mul
  have h_zero_arg : (5 - 2 * nu) * log_Q + (2 * nu - 5) * log_Q = 0 := by ring
  rw [h_zero_arg] at h_mul
  have h_exp0_le : Real.exp 0 ≤ 1 := Real.exp_le_one_iff.mpr (le_refl 0)
  linarith

/-! ### Pillar 5: Bidirectional Midpoint Folding, 4D Sophie Germain Duality & `-1/12` Inflection -/

/-- Bidirectionally folded quartic denominator `D₄(y) = y⁴ + 6y² + 25 = (y² + 3)² + 16`. -/
@[expose]
def foldedKernelDenom4 (y : ℝ) : ℝ :=
  y ^ 4 + 6 * (y ^ 2) + 25

/-- 4D Sophie Germain parity-twin quotient `Q_4D(y) = y⁴ - 10y² + 41 = (y² - 5)² + 16`. -/
@[expose]
def sophieGermainQuot4 (y : ℝ) : ℝ :=
  y ^ 4 - 10 * (y ^ 2) + 41

/--
Theorem (Bidirectional Parity Folding, `113/4` Midpoint Norm, 4D Sophie Germain Division
& Universal `-1/12` Casimir Surface Elimination):
-/
theorem bidirectional_folding_and_sophie_germain_4d
    (a U h y z : ℝ) (ha : a ≠ 0) :
    tveSteinerTubePoly U h ((1 + y) / 2) =
      ((3 * U + 4 * h) + 7 * U * (y ^ 2)) / 8 +
        (y * ((4 * U + 2 * h) + U * (y ^ 2))) / 4 ∧
    tveSteinerTubePoly (aspectRatio (electronUnknot a)) 1 ((1 + y) / 2) =
      ((5 + 7 * (y ^ 2)) + 2 * y * (5 + y ^ 2)) / 4 ∧
    foldedKernelDenom4 y = (y ^ 2 + 3) ^ 2 + 16 ∧
    ((1 - y ^ 2) ^ 2 - 8 * (1 - y ^ 2) + 32) = foldedKernelDenom4 y ∧
    ((1 - y ^ 2) ^ 2 + 8 * (1 - y ^ 2) + 32) = sophieGermainQuot4 y ∧
    ((1 / 2 : ℝ) + 3) ^ 2 + 16 = 113 / 4 ∧
    ((1 - y ^ 2) ^ 4) / (foldedKernelDenom4 y) =
      sophieGermainQuot4 y - 1024 / (foldedKernelDenom4 y) ∧
    tveSteinerTubePoly (aspectRatio (electronUnknot a)) 1 (z - 1 / 12) =
      4 * (z ^ 3) + (11 / 12) * z - 17 / 216 ∧
    tveSteinerSecondDeriv U h (-1 / 12) = 0 := by
  have h_d4 : foldedKernelDenom4 y ≠ 0 := by
    dsimp [foldedKernelDenom4]
    positivity
  have h_sg_poly :
      (1 - y ^ 2) ^ 4 =
        (sophieGermainQuot4 y) * (foldedKernelDenom4 y) - 1024 := by
    dsimp [sophieGermainQuot4, foldedKernelDenom4]
    ring
  have h_sg_div :
      ((1 - y ^ 2) ^ 4) / (foldedKernelDenom4 y) =
        sophieGermainQuot4 y - 1024 / (foldedKernelDenom4 y) := by
    calc ((1 - y ^ 2) ^ 4) / (foldedKernelDenom4 y)
      _ = ((sophieGermainQuot4 y) * (foldedKernelDenom4 y) - 1024) /
            (foldedKernelDenom4 y) := by rw [h_sg_poly]
      _ = ((sophieGermainQuot4 y) * (foldedKernelDenom4 y)) /
            (foldedKernelDenom4 y) - 1024 / (foldedKernelDenom4 y) := by ring
      _ = sophieGermainQuot4 y - 1024 / (foldedKernelDenom4 y) := by
          rw [mul_div_cancel_right₀ _ h_d4]
  refine ⟨?_, ?_, ?_, ?_, ?_, by norm_num, h_sg_div, ?_, ?_⟩
  · dsimp [tveSteinerTubePoly]
    ring
  · dsimp [tveSteinerTubePoly]
    rw [electron_aspect_ratio a ha]
    ring
  · dsimp [foldedKernelDenom4]
    ring
  · dsimp [foldedKernelDenom4]
    ring
  · dsimp [sophieGermainQuot4]
    ring
  · dsimp [tveSteinerTubePoly]
    rw [electron_aspect_ratio a ha]
    ring
  · dsimp [tveSteinerSecondDeriv]
    ring

/-! ### Pillar 6: Log-Free 3D Sphere & 4D Hopf Derivative Reductions on Unknot & `(3,2)` Trefoil -/

/-- Rational antiderivative piece `R₁(2, 1; x) = -(11x + 2) / (2(1 + x²))` for the 3D unknot jet. -/
@[expose]
noncomputable def unknotSphereRat1 (x : ℝ) : ℝ :=
  -(11 * x + 2) / (2 * (1 + x ^ 2))

/-- Exact derivative `R₁'(2, 1; x)` of `unknotSphereRat1`. -/
@[expose]
noncomputable def unknotSphereRat1Deriv (x : ℝ) : ℝ :=
  ((11 * (x ^ 2) + 4 * x - 11) / 2) / ((1 + x ^ 2) ^ 2)

/-- Rational antiderivative piece `R₁(2/3, 3; x) = -(3x + 2) / (6(1 + x²))` for the relaxed trefoil. -/
@[expose]
noncomputable def trefoilSphereRat1 (x : ℝ) : ℝ :=
  -(3 * x + 2) / (6 * (1 + x ^ 2))

/-- Exact derivative `R₁'(2/3, 3; x)` of `trefoilSphereRat1`. -/
@[expose]
noncomputable def trefoilSphereRat1Deriv (x : ℝ) : ℝ :=
  ((3 * (x ^ 2) + 4 * x - 3) / 6) / ((1 + x ^ 2) ^ 2)

/-- Rational antiderivative piece `R₂(2; x) = (3x³ + 5x - 24) / (4(1 + x²)²)` for the 4D Hopf unknot jet. -/
@[expose]
noncomputable def unknotHopfRat2 (x : ℝ) : ℝ :=
  (3 * (x ^ 3) + 5 * x - 24) / (4 * ((1 + x ^ 2) ^ 2))

/-- Exact derivative `R₂'(2; x)` of `unknotHopfRat2`. -/
@[expose]
noncomputable def unknotHopfRat2Deriv (x : ℝ) : ℝ :=
  ((-3 * (x ^ 4) - 6 * (x ^ 2) + 96 * x + 5) / 4) / ((1 + x ^ 2) ^ 3)

/--
Theorem (3D Sphere & 4D Hopf Derivative Reductions + Trefoil Zero-Drift Identity):
-/
theorem higher_sphere_and_trefoil_circular_reductions (x : ℝ) :
    tveSteinerFirstDeriv 2 1 x / ((1 + x ^ 2) ^ 2) =
      unknotSphereRat1Deriv x + (13 / 2) / (1 + x ^ 2) ∧
    unknotSphereRat1 1 - unknotSphereRat1 0 = -9 / 4 ∧
    tveSteinerFirstDeriv (2 / 3) 3 x / ((1 + x ^ 2) ^ 2) =
      trefoilSphereRat1Deriv x + (7 / 2) / (1 + x ^ 2) ∧
    trefoilSphereRat1 1 - trefoilSphereRat1 0 = -1 / 12 ∧
    tveSteinerSecondDeriv 2 1 x / ((1 + x ^ 2) ^ 3) =
      unknotHopfRat2Deriv x + (3 / 4) / (1 + x ^ 2) ∧
    unknotHopfRat2 1 - unknotHopfRat2 0 = 5 ∧
    tveSteinerTubePoly (3 / 2) 3 x / (1 + x ^ 2) =
      (3 / 4) * (4 * x + 1) - (3 / 4) / (1 + x ^ 2) := by
  have h1 : 1 + x ^ 2 ≠ 0 := by positivity
  have h2 : (1 + x ^ 2) ^ 2 ≠ 0 := by positivity
  have h_pole_u1 :
      ((13 / 2 : ℝ) * (1 + x ^ 2)) / ((1 + x ^ 2) ^ 2) =
        (13 / 2) / (1 + x ^ 2) := by
    rw [pow_two (1 + x ^ 2)]
    exact mul_div_mul_right (13 / 2 : ℝ) (1 + x ^ 2) h1
  have h_u1_num :
      tveSteinerFirstDeriv 2 1 x =
        (11 * (x ^ 2) + 4 * x - 11) / 2 + (13 / 2) * (1 + x ^ 2) := by
    dsimp [tveSteinerFirstDeriv]
    ring
  have h_u1 :
      tveSteinerFirstDeriv 2 1 x / ((1 + x ^ 2) ^ 2) =
        unknotSphereRat1Deriv x + (13 / 2) / (1 + x ^ 2) := by
    calc tveSteinerFirstDeriv 2 1 x / ((1 + x ^ 2) ^ 2)
      _ = ((11 * (x ^ 2) + 4 * x - 11) / 2 + (13 / 2) * (1 + x ^ 2)) /
            ((1 + x ^ 2) ^ 2) := by rw [h_u1_num]
      _ = unknotSphereRat1Deriv x +
            ((13 / 2 : ℝ) * (1 + x ^ 2)) / ((1 + x ^ 2) ^ 2) := by
          dsimp [unknotSphereRat1Deriv]
          ring
      _ = unknotSphereRat1Deriv x + (13 / 2) / (1 + x ^ 2) := by
          rw [h_pole_u1]
  have h_pole_t1 :
      ((7 / 2 : ℝ) * (1 + x ^ 2)) / ((1 + x ^ 2) ^ 2) =
        (7 / 2) / (1 + x ^ 2) := by
    rw [pow_two (1 + x ^ 2)]
    exact mul_div_mul_right (7 / 2 : ℝ) (1 + x ^ 2) h1
  have h_t1_num :
      tveSteinerFirstDeriv (2 / 3) 3 x =
        (3 * (x ^ 2) + 4 * x - 3) / 6 + (7 / 2) * (1 + x ^ 2) := by
    dsimp [tveSteinerFirstDeriv]
    ring
  have h_t1 :
      tveSteinerFirstDeriv (2 / 3) 3 x / ((1 + x ^ 2) ^ 2) =
        trefoilSphereRat1Deriv x + (7 / 2) / (1 + x ^ 2) := by
    calc tveSteinerFirstDeriv (2 / 3) 3 x / ((1 + x ^ 2) ^ 2)
      _ = ((3 * (x ^ 2) + 4 * x - 3) / 6 + (7 / 2) * (1 + x ^ 2)) /
            ((1 + x ^ 2) ^ 2) := by rw [h_t1_num]
      _ = trefoilSphereRat1Deriv x +
            ((7 / 2 : ℝ) * (1 + x ^ 2)) / ((1 + x ^ 2) ^ 2) := by
          dsimp [trefoilSphereRat1Deriv]
          ring
      _ = trefoilSphereRat1Deriv x + (7 / 2) / (1 + x ^ 2) := by
          rw [h_pole_t1]
  have h_pole_u2 :
      ((3 / 4 : ℝ) * ((1 + x ^ 2) ^ 2)) / ((1 + x ^ 2) ^ 3) =
        (3 / 4) / (1 + x ^ 2) := by
    have h_p3 : (1 + x ^ 2) ^ 3 = (1 + x ^ 2) * ((1 + x ^ 2) ^ 2) := by ring
    rw [h_p3]
    exact mul_div_mul_right (3 / 4 : ℝ) (1 + x ^ 2) h2
  have h_u2_num :
      tveSteinerSecondDeriv 2 1 x =
        (-3 * (x ^ 4) - 6 * (x ^ 2) + 96 * x + 5) / 4 +
          (3 / 4) * ((1 + x ^ 2) ^ 2) := by
    dsimp [tveSteinerSecondDeriv]
    ring
  have h_u2 :
      tveSteinerSecondDeriv 2 1 x / ((1 + x ^ 2) ^ 3) =
        unknotHopfRat2Deriv x + (3 / 4) / (1 + x ^ 2) := by
    calc tveSteinerSecondDeriv 2 1 x / ((1 + x ^ 2) ^ 3)
      _ = ((-3 * (x ^ 4) - 6 * (x ^ 2) + 96 * x + 5) / 4 +
            (3 / 4) * ((1 + x ^ 2) ^ 2)) / ((1 + x ^ 2) ^ 3) := by
          rw [h_u2_num]
      _ = unknotHopfRat2Deriv x +
            ((3 / 4 : ℝ) * ((1 + x ^ 2) ^ 2)) / ((1 + x ^ 2) ^ 3) := by
          dsimp [unknotHopfRat2Deriv]
          ring
      _ = unknotHopfRat2Deriv x + (3 / 4) / (1 + x ^ 2) := by
          rw [h_pole_u2]
  have h_tf_num :
      tveSteinerTubePoly (3 / 2) 3 x =
        ((3 / 4) * (4 * x + 1)) * (1 + x ^ 2) - 3 / 4 := by
    dsimp [tveSteinerTubePoly]
    ring
  have h_tf :
      tveSteinerTubePoly (3 / 2) 3 x / (1 + x ^ 2) =
        (3 / 4) * (4 * x + 1) - (3 / 4) / (1 + x ^ 2) := by
    calc tveSteinerTubePoly (3 / 2) 3 x / (1 + x ^ 2)
      _ = (((3 / 4) * (4 * x + 1)) * (1 + x ^ 2) - 3 / 4) / (1 + x ^ 2) := by
          rw [h_tf_num]
      _ = (((3 / 4) * (4 * x + 1)) * (1 + x ^ 2)) / (1 + x ^ 2) -
            (3 / 4) / (1 + x ^ 2) := by ring
      _ = (3 / 4) * (4 * x + 1) - (3 / 4) / (1 + x ^ 2) := by
          rw [mul_div_cancel_right₀ _ h1]
  refine ⟨h_u1, ?_, h_t1, ?_, h_u2, ?_, h_tf⟩
  · dsimp [unknotSphereRat1]; norm_num
  · dsimp [trefoilSphereRat1]; norm_num
  · dsimp [unknotHopfRat2]; norm_num

#print axioms gaussian_pole_and_residue_hierarchy
#print axioms universal_gaussian_integer_norm_floor
#print axioms dalzell_and_tve_division_exact
#print axioms discrete_determinant_sandwich_collapse_nat
#print axioms universal_diophantine_dyadic_repulsion_int
#print axioms midpoint_folding_and_113_norm_int
#print axioms sophie_germain_4d_and_phase_lock_int
#print axioms higher_sphere_and_symplectic_action_int

end TVE
