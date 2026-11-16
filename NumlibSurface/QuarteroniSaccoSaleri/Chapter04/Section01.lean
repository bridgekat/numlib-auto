/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.Analysis.Matrix.SpectralNorm
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.Stationary.Basic

/-!
# Quarteroni, Sacco and Saleri, Section 4.1: On the convergence of iterative methods

This module formalizes Section 4.1 of [quarteroni2000numerical], on the linear iterative methods
(4.2)
$$x^{(k+1)} = B x^{(k)} + f, \qquad k \ge 0,$$
for the solution of a linear system $Ax = b$ with $A \in \mathbb{R}^{n \times n}$. The method is
consistent (Definition 4.1) if the solution $x = A^{-1} b$ is a fixed point, $x = Bx + f$. For a
consistent method the error $e^{(k)} = x^{(k)} - x$ satisfies $e^{(k)} = B^k e^{(0)}$ (4.4), and
Theorem 4.1 shows that the iterates converge to $x$ for every $x^{(0)}$ if and only if the spectral
radius satisfies $\rho(B) < 1$. Example 4.1 shows that consistency alone does not give convergence.
Definition 4.2 introduces the convergence factor $\|B^m\|$, the average convergence factor
$\|B^m\|^{1/m}$ and the average convergence rate $R_m(B) = -\frac{1}{m} \log \|B^m\|$, and (4.5)
identifies the asymptotic convergence rate $R(B) = \lim_{k \to \infty} R_k(B) = -\log \rho(B)$.

The proofs specialize the backbone modules `Numlib.Stationary.Basic` (the affine iteration
$x \mapsto Gx + f$ on a normed space, its error propagation, and the convergence factors and rates),
`Numlib.LinearAlgebra.Matrix.Complexify` (the spectral radius `Matrix.complexSpectralRadius` of a
real matrix and the equivalence $B^k \to 0 \iff \rho(B) < 1$) and
`Numlib.Analysis.Matrix.SpectralNorm` (the spectral norm of a symmetric matrix).

## Main definitions

* Equation (4.2), `QuarteroniSaccoSaleri.Chapter04.affineStep`: one step $x \mapsto Bx + f$ of the
  linear iterative method.
* Definition 4.1, `QuarteroniSaccoSaleri.Chapter04.definition_4_1`: the method is consistent with
  $Ax = b$ if $A^{-1} b = B A^{-1} b + f$.
* Definition 4.2, `QuarteroniSaccoSaleri.Chapter04.definition_4_2_factor`: the convergence factor
  $\|B^m\|_2$ after $m$ steps.
* Definition 4.2, `QuarteroniSaccoSaleri.Chapter04.definition_4_2_averageFactor`: the average
  convergence factor $\|B^m\|_2^{1/m}$ after $m$ steps.
* Definition 4.2, `QuarteroniSaccoSaleri.Chapter04.definition_4_2_rate`: the average convergence
  rate $R_m(B) = -\frac{1}{m} \log \|B^m\|_2$ after $m$ steps.
* Equation (4.5), `QuarteroniSaccoSaleri.Chapter04.asymptoticConvergenceRate`: the asymptotic
  convergence rate $R(B) = -\log \rho(B)$.

## Main results

* Equation (4.2), `QuarteroniSaccoSaleri.Chapter04.toLp_affineStep`: the step is the backbone step
  `Stationary.step` in `EuclideanSpace ℝ (Fin n)`.
* Equation (4.2), `QuarteroniSaccoSaleri.Chapter04.toLp_affineStep_iterate`: the same for the
  iterates.
* Definition 4.1, `QuarteroniSaccoSaleri.Chapter04.definition_4_1_iff`: the method is consistent if
  and only if $f = (I - B) A^{-1} b$.
* Example 4.1, `QuarteroniSaccoSaleri.Chapter04.example_4_1_consistent`: the method
  $x^{(k+1)} = -x^{(k)} + b$ is consistent with $2Ix = b$.
* Example 4.1, `QuarteroniSaccoSaleri.Chapter04.example_4_1_iterate`: from $x^{(0)} = 0$ its
  iterates alternate between $0$ and $b$.
* Example 4.1, `QuarteroniSaccoSaleri.Chapter04.example_4_1_not_tendsto`: for $b \neq 0$ these
  iterates do not converge.
* Example 4.1, `QuarteroniSaccoSaleri.Chapter04.example_4_1_tendsto`: from $x^{(0)} = b/2$ the
  iterates are constant.
* Equation (4.4), `QuarteroniSaccoSaleri.Chapter04.equation_4_4`: for a consistent method,
  $e^{(k)} = B^k e^{(0)}$.
* Theorem 4.1, `QuarteroniSaccoSaleri.Chapter04.complexSpectralRadius_lt_one_of_forall_tendsto`: if
  the iterates converge to one limit from every start, then $\rho(B) < 1$.
* Theorem 4.1, `QuarteroniSaccoSaleri.Chapter04.theorem_4_1`: a consistent method converges for
  every $x^{(0)}$ if and only if $\rho(B) < 1$.
* Theorem 4.1, `QuarteroniSaccoSaleri.Chapter04.tendsto_of_algebraNorm_lt_one`: $\|B\| < 1$ in a
  matrix norm is sufficient for convergence.
* Definition 4.2, `QuarteroniSaccoSaleri.Chapter04.definition_4_2_eq`: the three quantities agree
  with the backbone definitions.
* Equation (4.5), `QuarteroniSaccoSaleri.Chapter04.equation_4_5`: $R_k(B) \to -\log \rho(B)$ if
  $\rho(B) \neq 0$.
* Equation (4.5), `QuarteroniSaccoSaleri.Chapter04.equation_4_5_factor`:
  $\|B^m\|_2^{1/m} \to \rho(B)$.
* Equation (4.5), `QuarteroniSaccoSaleri.Chapter04.equation_4_5_symm`: for symmetric $B$,
  $R_m(B) = -\log \rho(B)$ for every $m \ge 1$.
* Exercise 4.1, `QuarteroniSaccoSaleri.Chapter04.exercise_4_1`: a matrix with $\rho(B) < 1$ whose
  average convergence factor after one step exceeds $1$.

## Conventions

* The method (4.2) on $\mathbb{R}^n$ is `QuarteroniSaccoSaleri.Chapter04.affineStep B f` on
  `Fin n → ℝ`. The iterate `(affineStep B f)^[k] x⁽⁰⁾` is the iterate $x^{(k)}$.
* The solution of the system $Ax = b$ of (3.2) is written `A⁻¹ *ᵥ b`. Mathlib's inverse of a
  singular matrix is $0$. The book's standing assumption that $A$ is nonsingular is therefore a
  hypothesis of the statements that need it, and it is omitted from the statements that are true
  without it.
* Matrix norms are the spectral norm $\|\cdot\|_2$ (Mathlib's scoped `Matrix.Norms.L2Operator`). The
  spectral radius of a real matrix is `Matrix.complexSpectralRadius`, with values in `ℝ≥0∞`, and its
  real value is `.toReal`.
* Exercise 4.k is Exercise k of Chapter 4.

## Implementation notes

* Under `WithLp.toLp 2`, the method (4.2) is the backbone `Stationary.step` of the operator
  `Matrix.toEuclideanCLM B` on `EuclideanSpace ℝ (Fin n)`
  (`QuarteroniSaccoSaleri.Chapter04.toLp_affineStep` and
  `QuarteroniSaccoSaleri.Chapter04.toLp_affineStep_iterate`). Every backbone statement is
  transported in this way.
* The spectral radius of a matrix with a single real eigenvalue, used in Exercise 4.1, is
  `Matrix.complexSpectralRadius_eq_of_forall_mem_spectrum_iff`.

## Deviations from the source

* **Equation (4.4) and Theorem 4.1** (generalization). The statements do not assume that $A$ is
  nonsingular. For a singular $A$, $A^{-1} = 0$ in Lean, consistency reads $f = 0$, and the
  statements remain true. See `QuarteroniSaccoSaleri.Chapter04.equation_4_4` and
  `QuarteroniSaccoSaleri.Chapter04.theorem_4_1`.
* **Definition 4.2** (reading). The book allows any matrix norm. The definitions use the spectral
  norm. See `QuarteroniSaccoSaleri.Chapter04.definition_4_2_factor`.
* **Equation (4.5)** (reading). The limit is stated for $\rho(B) \neq 0$. For a nilpotent $B$ the
  book's rate is $+\infty$, and the formal rates $R_k(B)$ are $0$. See
  `QuarteroniSaccoSaleri.Chapter04.equation_4_5`.

## Not formalized

* **Remark 4.1**, on the order, the stationarity and the linearity of a general iterative method. It
  is a classification.
-/

open Filter Finset Matrix Topology WithLp
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter04

variable {n : ℕ}

/-! ### The linear iterative method (4.2) -/

/-- **Equation (4.2)** of [quarteroni2000numerical]. Let $B \in \mathbb{R}^{n \times n}$ be the
iteration matrix and let $f \in \mathbb{R}^n$ be the vector obtained from the right-hand side.
One step of the **linear iterative method** is
$$x \mapsto Bx + f,$$
so that the method is $x^{(k+1)} = B x^{(k)} + f$.

The iterate $x^{(k)}$ from $x^{(0)}$ is `(affineStep B f)^[k] x⁽⁰⁾`. This is the backbone
`Stationary.step` of the operator `Matrix.toEuclideanCLM B`, read on plain functions; see
`QuarteroniSaccoSaleri.Chapter04.toLp_affineStep`. -/
def affineStep (B : Matrix (Fin n) (Fin n) ℝ) (f x : Fin n → ℝ) : Fin n → ℝ := B *ᵥ x + f

/-- **Equation (4.2)** of [quarteroni2000numerical], the backbone form. Let
$B \in \mathbb{R}^{n \times n}$ and $f, x \in \mathbb{R}^n$. Under `WithLp.toLp 2`, the step
$Bx + f$ is the backbone step `Stationary.step` of the operator `Matrix.toEuclideanCLM B` on
`EuclideanSpace ℝ (Fin n)`. Through this identity the theory of `Numlib.Stationary.Basic`
applies to the method of the book. -/
theorem toLp_affineStep (B : Matrix (Fin n) (Fin n) ℝ) (f x : Fin n → ℝ) :
    (toLp 2 (affineStep B f x) : EuclideanSpace ℝ (Fin n)) =
      Stationary.step (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f) (toLp 2 x) := rfl

/-- **Equation (4.2)** of [quarteroni2000numerical], the backbone form of the iterates. Under
`WithLp.toLp 2`, the iterate $x^{(k)}$ of (4.2) from $x^{(0)}$ is the iterate of index $k$ of
the backbone step `Stationary.step` of `Matrix.toEuclideanCLM B`. -/
theorem toLp_affineStep_iterate (B : Matrix (Fin n) (Fin n) ℝ) (f x₀ : Fin n → ℝ) (k : ℕ) :
    (toLp 2 ((affineStep B f)^[k] x₀) : EuclideanSpace ℝ (Fin n)) =
      (Stationary.step (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f))^[k] (toLp 2 x₀) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

/-! ### Definition 4.1 and Example 4.1 -/

/-- **Definition 4.1** of [quarteroni2000numerical]. Let $A, B \in \mathbb{R}^{n \times n}$ and
$b, f \in \mathbb{R}^n$. The iterative method (4.2) is **consistent** with the system $Ax = b$
if the solution $x = A^{-1} b$ is a fixed point of the step:
$$A^{-1} b = B A^{-1} b + f.$$

The definition is meaningful for a nonsingular $A$, the standing assumption of Section 3.2. For
a singular $A$, Lean's $A^{-1}$ is $0$. The "equivalently, $f = (I - B) A^{-1} b$" of the book
is `QuarteroniSaccoSaleri.Chapter04.definition_4_1_iff`. -/
def definition_4_1 (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → ℝ) : Prop :=
  A⁻¹ *ᵥ b = B *ᵥ (A⁻¹ *ᵥ b) + f

/-- **Definition 4.1** of [quarteroni2000numerical], "equivalently". Let
$A, B \in \mathbb{R}^{n \times n}$ and $b, f \in \mathbb{R}^n$. The method (4.2) is consistent
with $Ax = b$ if and only if
$$f = (I - B) A^{-1} b.$$
This is a rearrangement, and it holds for every $A$. -/
theorem definition_4_1_iff (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) :
    definition_4_1 A b B f ↔ f = (1 - B) *ᵥ (A⁻¹ *ᵥ b) := by
  rw [definition_4_1, sub_mulVec, one_mulVec]
  exact ⟨fun h => eq_sub_of_add_eq' h.symm, fun h => (add_eq_of_eq_sub' h).symm⟩

/-- If the method (4.2) is consistent with $Ax = b$, then under `WithLp.toLp 2` the solution
$A^{-1} b$ is a fixed point of the backbone step: $B A^{-1} b + f = A^{-1} b$ in
`EuclideanSpace ℝ (Fin n)`. This is the form of the fixed-point hypothesis that the theorems of
`Numlib.Stationary.Basic` take. -/
theorem toLp_fixed_of_consistent {A B : Matrix (Fin n) (Fin n) ℝ} {b f : Fin n → ℝ}
    (hc : definition_4_1 A b B f) :
    toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B (toLp 2 (A⁻¹ *ᵥ b)) + toLp 2 f =
      (toLp 2 (A⁻¹ *ᵥ b) : EuclideanSpace ℝ (Fin n)) := by
  rw [toEuclideanCLM_toLp, ← toLp_add, ← hc]

/-- $(2I)^{-1} b = b/2$, the solution of the system of Example 4.1. -/
private theorem inv_two_smul_one_mulVec (b : Fin n → ℝ) :
    ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ *ᵥ b = (1 / 2 : ℝ) • b := by
  have h : ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = (1 / 2 : ℝ) • 1 := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, one_mul]
    norm_num
  rw [h, smul_mulVec, one_mulVec]

/-- **Example 4.1** of [quarteroni2000numerical], consistency. For every $b \in \mathbb{R}^n$, the
method $x^{(k+1)} = -x^{(k)} + b$, that is, $B = -I$ and $f = b$, is consistent with the system
$2I x = b$: its solution $b/2$ satisfies $b/2 = -b/2 + b$. -/
theorem example_4_1_consistent (b : Fin n → ℝ) :
    definition_4_1 ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) b (-1) b := by
  rw [definition_4_1, inv_two_smul_one_mulVec, neg_mulVec, one_mulVec]
  module

/-- **Example 4.1** of [quarteroni2000numerical], the iterates from $x^{(0)} = 0$. For every
$b \in \mathbb{R}^n$ and every $k$, the method $x^{(k+1)} = -x^{(k)} + b$ started at
$x^{(0)} = 0$ gives
$$x^{(2k)} = 0, \qquad x^{(2k+1)} = b.$$
-/
theorem example_4_1_iterate (b : Fin n → ℝ) (k : ℕ) :
    (affineStep (-1) b)^[2 * k] 0 = 0 ∧ (affineStep (-1) b)^[2 * k + 1] 0 = b := by
  have h1 : ∀ x, affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b x = -x + b := fun x => by
    rw [affineStep, neg_mulVec, one_mulVec]
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have h2 : (affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b)^[2 * (k + 1)] 0 = 0 := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply', ih1, h1]
      abel
    refine ⟨h2, ?_⟩
    rw [Function.iterate_succ_apply', h2, h1]
    abel

/-- **Example 4.1** of [quarteroni2000numerical], non-convergence. Let $b \in \mathbb{R}^n$ with
$b \neq 0$. The sequence $x^{(k)}$ of the method $x^{(k+1)} = -x^{(k)} + b$ started at
$x^{(0)} = 0$ has no limit, because its even terms are $0$ and its odd terms are $b$. So
consistency alone does not give convergence. -/
theorem example_4_1_not_tendsto {b : Fin n → ℝ} (hb : b ≠ 0) :
    ¬ ∃ x, Tendsto (fun k => (affineStep (-1) b)^[k] 0) atTop (𝓝 x) := by
  rintro ⟨x, hx⟩
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k two_pos) tendsto_id
  have h3 : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_succ _) h2
  have heven : Tendsto (fun k => (affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b)^[2 * k] 0) atTop
      (𝓝 x) :=
    hx.comp h2
  have hodd : Tendsto (fun k => (affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b)^[2 * k + 1] 0) atTop
      (𝓝 x) :=
    hx.comp h3
  simp only [fun k => (example_4_1_iterate b k).1] at heven
  simp only [fun k => (example_4_1_iterate b k).2] at hodd
  exact hb ((tendsto_nhds_unique hodd tendsto_const_nhds).symm.trans
    (tendsto_nhds_unique heven tendsto_const_nhds))

/-- **Example 4.1** of [quarteroni2000numerical], convergence from $x^{(0)} = b/2$. For every
$b \in \mathbb{R}^n$, the method $x^{(k+1)} = -x^{(k)} + b$ started at the solution
$x^{(0)} = b/2$ is stationary: $x^{(k)} = b/2$ for all $k$, and so the sequence converges to
$b/2$. -/
theorem example_4_1_tendsto (b : Fin n → ℝ) :
    (∀ k, (affineStep (-1) b)^[k] ((1 / 2 : ℝ) • b) = (1 / 2 : ℝ) • b) ∧
      Tendsto (fun k => (affineStep (-1) b)^[k] ((1 / 2 : ℝ) • b)) atTop (𝓝 ((1 / 2 : ℝ) • b)) := by
  have hfix : affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b ((1 / 2 : ℝ) • b) = (1 / 2 : ℝ) • b := by
    rw [affineStep, neg_mulVec, one_mulVec]
    module
  have h : ∀ k, (affineStep (-1 : Matrix (Fin n) (Fin n) ℝ) b)^[k] ((1 / 2 : ℝ) • b)
      = (1 / 2 : ℝ) • b := fun k => Function.iterate_fixed hfix k
  refine ⟨h, ?_⟩
  simp only [h]
  exact tendsto_const_nhds

/-! ### Theorem 4.1 -/

/-- **Equation (4.4)** of [quarteroni2000numerical]. Let $A, B \in \mathbb{R}^{n \times n}$ and
$b, f \in \mathbb{R}^n$, and let the method (4.2) be consistent with $Ax = b$. Then for every
$x^{(0)} \in \mathbb{R}^n$ and every $k$, the error $e^{(k)} = x^{(k)} - A^{-1} b$ satisfies
$$e^{(k)} = B^k e^{(0)}.$$
This follows from the recursion $e^{(k+1)} = B e^{(k)}$.

**Generalization.** The book assumes that $A$ is nonsingular. The statement holds without this
hypothesis: for a singular $A$, $A^{-1} = 0$ in Lean, consistency reads $f = 0$, and the
identity is still true.

The proof specializes `Stationary.step_iterate_sub`, transported along
`QuarteroniSaccoSaleri.Chapter04.toLp_affineStep_iterate`. -/
theorem equation_4_4 {A B : Matrix (Fin n) (Fin n) ℝ} {b f : Fin n → ℝ}
    (hc : definition_4_1 A b B f) (x₀ : Fin n → ℝ) (k : ℕ) :
    (affineStep B f)^[k] x₀ - A⁻¹ *ᵥ b = (B ^ k) *ᵥ (x₀ - A⁻¹ *ᵥ b) := by
  have h := Stationary.step_iterate_sub (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) (toLp 2 f)
    (toLp_fixed_of_consistent hc) (toLp 2 x₀) k
  rw [← toLp_affineStep_iterate, ← map_pow, ← toLp_sub, ← toLp_sub, toEuclideanCLM_toLp] at h
  exact toLp_injective 2 h

/-- **Section 4.1** of [quarteroni2000numerical], the difference of two iterations. Let
$B \in \mathbb{R}^{n \times n}$ and $f, x^{(0)}, y^{(0)} \in \mathbb{R}^n$, and let $x^{(k)}$
and $y^{(k)}$ be the iterates of (4.2) from $x^{(0)}$ and from $y^{(0)}$. Then for every $k$
$$x^{(k)} - y^{(k)} = B^k (x^{(0)} - y^{(0)}).$$
No fixed point is needed. This identity is the reason why convergence for every $x^{(0)}$ forces
$B^k \to 0$, whatever the limit is.

The proof takes the difference of two instances of the closed form
`Stationary.step_iterate_eq_pow_add_sum`. -/
theorem affineStep_iterate_sub_iterate (B : Matrix (Fin n) (Fin n) ℝ) (f x₀ y₀ : Fin n → ℝ)
    (k : ℕ) :
    (affineStep B f)^[k] x₀ - (affineStep B f)^[k] y₀ = (B ^ k) *ᵥ (x₀ - y₀) := by
  have hx := Stationary.step_iterate_eq_pow_add_sum (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B)
    (toLp 2 f) (toLp 2 x₀) k
  have hy := Stationary.step_iterate_eq_pow_add_sum (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B)
    (toLp 2 f) (toLp 2 y₀) k
  rw [← toLp_affineStep_iterate] at hx hy
  have h := congrArg₂ (· - ·) hx hy
  simp only [add_sub_add_right_eq_sub, ← map_pow, ← toLp_sub, toEuclideanCLM_toLp, ← mulVec_sub]
    at h
  exact toLp_injective 2 h

/-- **Theorem 4.1** of [quarteroni2000numerical], the necessity of $\rho(B) < 1$. Let
$B \in \mathbb{R}^{n \times n}$ and $f, x \in \mathbb{R}^n$. If the iterates of (4.2) converge
to $x$ from every $x^{(0)} \in \mathbb{R}^n$, then $\rho(B) < 1$. No consistency is needed for
this direction.

The reason is that the differences $x^{(k)} - y^{(k)} = B^k (x^{(0)} - y^{(0)})$ of two
iterations tend to $0$, so that $B^k v \to 0$ for every $v$, and Theorem 1.5 gives
$\rho(B) < 1$. -/
theorem complexSpectralRadius_lt_one_of_forall_tendsto {B : Matrix (Fin n) (Fin n) ℝ}
    {f x : Fin n → ℝ} (h : ∀ x₀, Tendsto (fun k => (affineStep B f)^[k] x₀) atTop (𝓝 x)) :
    complexSpectralRadius B < 1 := by
  rw [← tendsto_pow_iff_complexSpectralRadius_lt_one,
    tendsto_zero_iff_forall_mulVec_tendsto_zero]
  intro v
  have hv := (h v).sub (h 0)
  rw [sub_self] at hv
  simpa only [affineStep_iterate_sub_iterate, sub_zero] using hv

/-- **Theorem 4.1** of [quarteroni2000numerical]. Let $A, B \in \mathbb{R}^{n \times n}$ and
$b, f \in \mathbb{R}^n$, and let the method (4.2) be consistent with $Ax = b$. Then the sequence
$x^{(k)}$ converges to the solution $x = A^{-1} b$ for every choice of
$x^{(0)} \in \mathbb{R}^n$ if and only if $\rho(B) < 1$.

**Generalization.** The book assumes that $A$ is nonsingular. The statement holds without this
hypothesis: for a singular $A$, $A^{-1} = 0$ in Lean, consistency reads $f = 0$, and the
equivalence is still true.

By (4.4) the errors are $B^k e^{(0)}$, and $B^k v \to 0$ for every $v$ if and only if
$B^k \to 0$, if and only if $\rho(B) < 1$ (Theorem 1.5,
`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`). The book proves the converse with an
eigenvector for an eigenvalue of modulus greater than $1$, and it does not treat the case
$\rho(B) = 1$. The equivalence of Theorem 1.5 covers both cases
(`QuarteroniSaccoSaleri.Chapter04.complexSpectralRadius_lt_one_of_forall_tendsto`). -/
theorem theorem_4_1 {A B : Matrix (Fin n) (Fin n) ℝ} {b f : Fin n → ℝ}
    (hc : definition_4_1 A b B f) :
    (∀ x₀, Tendsto (fun k => (affineStep B f)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b))) ↔
      complexSpectralRadius B < 1 := by
  refine ⟨complexSpectralRadius_lt_one_of_forall_tendsto, fun h x₀ => ?_⟩
  rw [← tendsto_pow_iff_complexSpectralRadius_lt_one,
    tendsto_zero_iff_forall_mulVec_tendsto_zero] at h
  rw [← tendsto_sub_nhds_zero_iff]
  simpa only [equation_4_4 hc] using h (x₀ - A⁻¹ *ᵥ b)

/-- **Section 4.1** of [quarteroni2000numerical], the remark after Theorem 4.1. Let
$A, B \in \mathbb{R}^{n \times n}$ and $b, f \in \mathbb{R}^n$, and let the method (4.2) be
consistent with $Ax = b$. Let $N$ be a matrix norm on $\mathbb{R}^{n \times n}$ with $N(B) < 1$.
Then for every $x^{(0)} \in \mathbb{R}^n$ the iterates $x^{(k)}$ converge to $A^{-1} b$. So
$\|B\| < 1$ in some matrix norm is a sufficient condition for convergence.

A matrix norm is an algebra norm, that is, a submultiplicative norm
(`AlgebraNorm ℝ (Matrix (Fin n) (Fin n) ℝ)`). By (1.23) and Theorem 1.5 the powers of $B$ tend
to $0$ (`Matrix.tendsto_pow_of_algebraNorm_lt_one`), so $\rho(B) < 1$ and Theorem 4.1 applies. -/
theorem tendsto_of_algebraNorm_lt_one {A B : Matrix (Fin n) (Fin n) ℝ} {b f : Fin n → ℝ}
    (hc : definition_4_1 A b B f) (N : AlgebraNorm ℝ (Matrix (Fin n) (Fin n) ℝ)) (hN : N B < 1)
    (x₀ : Fin n → ℝ) :
    Tendsto (fun k => (affineStep B f)^[k] x₀) atTop (𝓝 (A⁻¹ *ᵥ b)) :=
  (theorem_4_1 hc).2
    ((tendsto_pow_iff_complexSpectralRadius_lt_one B).1 (tendsto_pow_of_algebraNorm_lt_one N hN))
    x₀

/-! ### Definition 4.2 and the asymptotic convergence rate (4.5) -/

section ConvergenceFactor

open scoped Matrix.Norms.L2Operator

/-- **Definition 4.2** of [quarteroni2000numerical], the convergence factor. Let
$B \in \mathbb{R}^{n \times n}$ and $m \in \mathbb{N}$. The **convergence factor after $m$
steps** of the iteration with matrix $B$ is $\|B^m\|_2$, in the spectral norm. It bounds the
reduction of the error over $m$ steps: $\|e^{(m)}\| \le \|B^m\| \|e^{(0)}\|$ (Section 4.6).

**Reading.** The book allows any matrix norm. The definition fixes the spectral norm. -/
noncomputable def definition_4_2_factor (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : ℝ := ‖B ^ m‖

/-- **Definition 4.2** of [quarteroni2000numerical], the average convergence factor. Let
$B \in \mathbb{R}^{n \times n}$ and $m \in \mathbb{N}$. The **average convergence factor after
$m$ steps** is $\|B^m\|_2^{1/m}$.

At $m = 0$ the exponent $1/m$ is $0$ in Lean, so the value is $1$. -/
noncomputable def definition_4_2_averageFactor (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : ℝ :=
  ‖B ^ m‖ ^ (1 / m : ℝ)

/-- **Definition 4.2** of [quarteroni2000numerical], the average convergence rate. Let
$B \in \mathbb{R}^{n \times n}$ and $m \in \mathbb{N}$. The **average convergence rate after $m$
steps** is
$$R_m(B) = -\frac{1}{m} \log \|B^m\|_2.$$

In Lean, $1/0 = 0$ and $\log 0 = 0$. So $R_0(B) = 0$, and $R_m(B) = 0$ when $B^m = 0$. -/
noncomputable def definition_4_2_rate (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) : ℝ :=
  -(1 / m : ℝ) * Real.log ‖B ^ m‖

/-- **Definition 4.2** of [quarteroni2000numerical], the backbone form. For
$B \in \mathbb{R}^{n \times n}$ and $m \in \mathbb{N}$, the convergence factor, the average
convergence factor and the average convergence rate after $m$ steps are the backbone
`Stationary.convergenceFactor`, `Stationary.averageConvergenceFactor` and
`Stationary.averageConvergenceRate` of the operator `Matrix.toEuclideanCLM B`. The operator norm
of this operator is the spectral norm of $B$ (`Matrix.l2_opNorm_toEuclideanCLM`). -/
theorem definition_4_2_eq (B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    definition_4_2_factor B m =
        Stationary.convergenceFactor (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) m ∧
      definition_4_2_averageFactor B m =
        Stationary.averageConvergenceFactor (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) m ∧
      definition_4_2_rate B m =
        Stationary.averageConvergenceRate (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) B) m := by
  simp only [definition_4_2_factor, definition_4_2_averageFactor, definition_4_2_rate,
    Stationary.convergenceFactor, Stationary.averageConvergenceFactor,
    Stationary.averageConvergenceRate, ← map_pow, l2_opNorm_toEuclideanCLM]
  exact ⟨trivial, trivial, trivial⟩

/-- **Equation (4.5)** of [quarteroni2000numerical], definition. For
$B \in \mathbb{R}^{n \times n}$, the **asymptotic convergence rate** is
$$R(B) = -\log \rho(B).$$
It is the limit of the average convergence rates $R_k(B)$; see
`QuarteroniSaccoSaleri.Chapter04.equation_4_5`. At $\rho(B) = 0$ the value is $0$ in Lean,
because $\log 0 = 0$. -/
noncomputable def asymptoticConvergenceRate (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -Real.log (complexSpectralRadius B).toReal

/-- **Equation (4.5)** of [quarteroni2000numerical]. Let $B \in \mathbb{R}^{n \times n}$ with
$\rho(B) \neq 0$. Then
$$R(B) = \lim_{k \to \infty} R_k(B) = -\log \rho(B),$$
"where Property 1.13 has been accounted for".

**Reading.** The book does not exclude $\rho(B) = 0$. For a nilpotent $B$ the book's rate is
$+\infty$, while the formal rates $R_k(B)$ are $0$ for large $k$. The statement therefore
assumes $\rho(B) \neq 0$.

The proof composes Gelfand's formula $\|B^k\|^{1/k} \to \rho(B)$ with the logarithm
(`Matrix.tendsto_averageConvergenceRate`). -/
theorem equation_4_5 {B : Matrix (Fin n) (Fin n) ℝ} (hρ : complexSpectralRadius B ≠ 0) :
    Tendsto (definition_4_2_rate B) atTop (𝓝 (asymptoticConvergenceRate B)) :=
  tendsto_averageConvergenceRate B hρ

/-- **Equation (4.5)** of [quarteroni2000numerical], the closing remark. For every
$B \in \mathbb{R}^{n \times n}$, the average convergence factors converge to the spectral
radius:
$$\lim_{m \to \infty} \|B^m\|_2^{1/m} = \rho(B).$$
So $\rho(B)$ is the **asymptotic convergence factor**.

This is Property 1.14; the proof specializes `Matrix.tendsto_pow_rpow_complexSpectralRadius`. -/
theorem equation_4_5_factor (B : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (definition_4_2_averageFactor B) atTop (𝓝 (complexSpectralRadius B).toReal) :=
  tendsto_pow_rpow_complexSpectralRadius B

/-- **Equation (4.5)** of [quarteroni2000numerical], the symmetric case. Let
$B \in \mathbb{R}^{n \times n}$ be symmetric and let $m \ge 1$. Then
$$R_m(B) = -\frac{1}{m} \log \|B^m\|_2 = -\log \rho(B),$$
because $\|B^m\|_2 = \|B\|_2^m = \rho(B)^m$.

The statement has no condition on $\rho(B)$. If $\rho(B) = 0$, then $B = 0$, and both sides are
$0$ because $\log 0 = 0$ in Lean. The proof specializes `Matrix.IsHermitian.l2_opNorm_pow` and
`Matrix.l2_opNorm_eq_complexSpectralRadius_of_isHermitian`. -/
theorem equation_4_5_symm {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.IsSymm) {m : ℕ} (hm : m ≠ 0) :
    definition_4_2_rate B m = asymptoticConvergenceRate B := by
  have hB' : B.IsHermitian := isHermitian_iff_isSymm.mpr hB
  rw [definition_4_2_rate, asymptoticConvergenceRate, hB'.l2_opNorm_pow hm,
    l2_opNorm_eq_complexSpectralRadius_of_isHermitian hB', Real.log_pow]
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  field_simp

/-- A complex number $\mu$ is in the spectrum of the complexification of a real $2 \times 2$ matrix
$B$ if and only if $\mu^2 - \operatorname{tr}(B) \mu + \det B = 0$. -/
private theorem mem_spectrum_complexify_fin_two (B : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℂ) :
    μ ∈ spectrum ℂ (complexify B) ↔ μ ^ 2 - B.trace * μ + B.det = 0 := by
  rw [mem_spectrum_complexify_iff, charpoly_fin_two, Polynomial.IsRoot.def]
  simp

/-- **Exercise 4.1** of [quarteroni2000numerical], cited after Definition 4.2 for the non-monotone
behaviour of $\|B^m\|$. Let $0 < a < 1$ and
$$B = \begin{bmatrix} a & 4 \\ 0 & a \end{bmatrix}.$$
Then $\rho(B) = a < 1$, while the average convergence factor after one step exceeds $1$:
$\|B\|_2 > 1$.

The characteristic polynomial of $B$ is $(\lambda - a)^2$, and $\|B\|_2 \ge |b_{12}| = 4$. -/
theorem exercise_4_1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    complexSpectralRadius (!![a, 4; 0, a] : Matrix (Fin 2) (Fin 2) ℝ) = ENNReal.ofReal a ∧
      complexSpectralRadius (!![a, 4; 0, a] : Matrix (Fin 2) (Fin 2) ℝ) < 1 ∧
      1 < definition_4_2_averageFactor (!![a, 4; 0, a] : Matrix (Fin 2) (Fin 2) ℝ) 1 := by
  set B : Matrix (Fin 2) (Fin 2) ℝ := !![a, 4; 0, a] with hB
  have hspec : ∀ μ : ℂ, μ ∈ spectrum ℂ (complexify B) ↔ μ = a := by
    intro μ
    rw [mem_spectrum_complexify_fin_two]
    simp only [hB, trace_fin_two_of, det_fin_two_of, mul_zero, sub_zero]
    push_cast
    constructor
    · intro h
      have h' : (μ - a) ^ 2 = 0 := by linear_combination h
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h')
    · rintro rfl
      ring
  have hρ : complexSpectralRadius B = ENNReal.ofReal a := by
    rw [complexSpectralRadius_eq_of_forall_mem_spectrum_iff hspec, abs_of_pos ha0]
  refine ⟨hρ, by rw [hρ]; exact ENNReal.ofReal_lt_one.mpr ha1, ?_⟩
  rw [definition_4_2_averageFactor, pow_one, Nat.cast_one, div_one, Real.rpow_one]
  have h4 : ‖B 0 1‖ ≤ ‖B‖ := norm_entry_le_l2_opNorm B 0 1
  have hB01 : ‖B 0 1‖ = 4 := by simp [hB]
  linarith

end ConvergenceFactor

end QuarteroniSaccoSaleri.Chapter04
