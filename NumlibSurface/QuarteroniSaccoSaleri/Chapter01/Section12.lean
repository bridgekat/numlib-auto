/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.MMatrix
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section10

/-!
# Quarteroni, Sacco and Saleri, Section 1.12: Positive Definite, Diagonally Dominant and M-matrices

This module formalizes Section 1.12 of [quarteroni2000numerical]. The book's positive definiteness
(Definition 1.22) does not assume symmetry. A matrix $A \in \mathbb{C}^{n \times n}$ is positive
definite in $\mathbb{C}^n$ if the number $(Ax, x) = x^H A x$ is real and positive for every
$x \neq 0$, and a matrix $A \in \mathbb{R}^{n \times n}$ is positive definite in $\mathbb{R}^n$ if
$(Ax, x) = x^T A x > 0$ for every $x \neq 0$. Property 1.17 identifies the complex notion with
Mathlib's `Matrix.PosDef` (Hermitian with positive form), and the real notion is coercivity of the
operator $x \mapsto Ax$ on Euclidean space. The module then states the symmetric and skew-symmetric
parts of a matrix, the characterizations of symmetric positive definite matrices (Property 1.18),
the energy norm (1.28), diagonal dominance (Definition 1.24), and M-matrices with the discrete
maximum principle (Definition 1.25, Properties 1.19 and 1.20).

The proofs specialize Mathlib's `Matrix.PosDef` API and the backbone modules
`Numlib.LinearAlgebra.Matrix.Cholesky` (Sylvester's criterion, the factorization $A = H^T H$, the
bounds on the entries), `Numlib.Analysis.InnerProductSpace.Energy` (the energy norm),
`Numlib.LinearAlgebra.Matrix.DiagDominant` (diagonal dominance) and
`Numlib.LinearAlgebra.Matrix.MMatrix` (M-matrices).

## Main definitions

* Definition 1.22, `QuarteroniSaccoSaleri.Chapter01.IsPositiveDefinite`: $(Ax, x)$ is real and
  positive for every nonzero $x \in \mathbb{C}^n$.
* Definition 1.22, `QuarteroniSaccoSaleri.Chapter01.IsPositiveSemidefinite`: $(Ax, x)$ is real and
  nonnegative for every nonzero $x \in \mathbb{C}^n$.
* Definition 1.22, `QuarteroniSaccoSaleri.Chapter01.IsPositiveDefiniteReal`: $(Ax, x) > 0$ for every
  nonzero $x \in \mathbb{R}^n$.
* Definition 1.22, `QuarteroniSaccoSaleri.Chapter01.IsPositiveSemidefiniteReal`: $(Ax, x) \ge 0$ for
  every nonzero $x \in \mathbb{R}^n$.
* Definition 1.22, `QuarteroniSaccoSaleri.Chapter01.definition_1_22`: positive definiteness in
  $\mathbb{R}^n$ is coercivity, positive definiteness in $\mathbb{C}^n$ is positivity of $x^H A x$
  in the order of $\mathbb{C}$, and the complex notion implies the real one.
* Example 1.8, `QuarteroniSaccoSaleri.Chapter01.example_1_8_matrix`: the nonsymmetric matrix (1.27).
* Definition 1.23, `QuarteroniSaccoSaleri.Chapter01.definition_1_23`: the symmetric part
  $A_S = \frac{1}{2}(A + A^T)$ and the skew-symmetric part $A_{SS} = \frac{1}{2}(A - A^T)$, with
  $A = A_S + A_{SS}$.
* Definition 1.24, `QuarteroniSaccoSaleri.Chapter01.definition_1_24`: diagonal dominance by rows and
  by columns, weak and strict.
* Definition 1.25, `QuarteroniSaccoSaleri.Chapter01.definition_1_25`: an M-matrix is a nonsingular
  matrix with nonpositive off-diagonal entries and an entrywise nonnegative inverse.

## Main results

* Example 1.8, `QuarteroniSaccoSaleri.Chapter01.example_1_8`: the matrix (1.27) is positive definite
  in $\mathbb{R}^2$ for every $\alpha$, but for $\alpha \neq -1$ it is neither symmetric nor
  positive definite in $\mathbb{C}^2$.
* Property 1.15, `QuarteroniSaccoSaleri.Chapter01.property_1_15`: a real matrix is positive definite
  in $\mathbb{R}^n$ if and only if its symmetric part is.
* Property 1.16, `QuarteroniSaccoSaleri.Chapter01.property_1_16`: if $(Ax, x)$ is real for every
  $x \in \mathbb{C}^n$, then $A$ is Hermitian (symmetric if $A$ is real).
* Property 1.17, `QuarteroniSaccoSaleri.Chapter01.property_1_17`: positive definiteness in
  $\mathbb{C}^n$ is the same as being Hermitian with positive eigenvalues, and it implies
  nonsingularity.
* Property 1.18(1), `QuarteroniSaccoSaleri.Chapter01.property_1_18_quadratic`: a symmetric real
  matrix is positive definite if and only if $x^T A x > 0$ for every nonzero real $x$.
* Property 1.18(2), `QuarteroniSaccoSaleri.Chapter01.property_1_18_eigenvalues`: a symmetric real
  matrix is positive definite if and only if every principal submatrix has positive eigenvalues.
* Property 1.18(3), `QuarteroniSaccoSaleri.Chapter01.property_1_18_minors`: Sylvester's criterion,
  positivity of the leading principal minors.
* Property 1.18(4), `QuarteroniSaccoSaleri.Chapter01.property_1_18_factor`: a real matrix is
  positive definite if and only if $A = H^T H$ with $H$ nonsingular.
* Section 1.12, `QuarteroniSaccoSaleri.Chapter01.posDef_diag_pos`: a positive definite matrix has
  positive diagonal entries, and $|a_{ij}| \le \max(a_{ii}, a_{jj})$.
* Equation (1.28), `QuarteroniSaccoSaleri.Chapter01.equation_1_28`: the square root $A^{1/2}$ and
  the energy norm $\|x\|_A = \|A^{1/2} x\|_2 = (Ax, x)^{1/2}$.
* Section 1.12, `QuarteroniSaccoSaleri.Chapter01.posDef_of_isStrictDiagDominant`: a symmetric
  strictly diagonally dominant matrix with positive diagonal is positive definite.
* Section 1.12, `QuarteroniSaccoSaleri.Chapter01.discreteMaximumPrinciple`: if $A$ is an M-matrix
  and $Ax \le 0$, then $x \le 0$.
* Property 1.19, `QuarteroniSaccoSaleri.Chapter01.property_1_19`: a matrix with nonpositive
  off-diagonal entries is an M-matrix if and only if $Aw > 0$ for some $w > 0$.
* Property 1.20, `QuarteroniSaccoSaleri.Chapter01.property_1_20`: a strictly diagonally dominant
  matrix with nonpositive off-diagonal entries and positive diagonal is an M-matrix.

## Conventions

* For complex vectors, the book's $(Ax, x)$ is `star x ⬝ᵥ (A *ᵥ x)`. For real vectors, it is
  `x ⬝ᵥ (A *ᵥ x)`. The scalar product is linear in its first argument, as fixed in Section 1.10.
* "Positive definite" without qualification is Mathlib's `Matrix.PosDef`. For a real matrix it means
  symmetric with $x^T A x > 0$ for $x \neq 0$.
* Inequalities between vectors are entrywise.

## Implementation notes

* The square root $A^{1/2}$ is Mathlib's `CFC.sqrt` for the Loewner order on matrices, which is
  Mathlib's scoped `MatrixOrder`. This scope is opened for
  `QuarteroniSaccoSaleri.Chapter01.equation_1_28` only.

## Deviations from the source

* **Definition 1.22 and Example 1.8** (reading). The definitions of positivity use the book's
  quadratic forms. The companion theorem adds equivalent and related formulations. The real
  positive definiteness in Example 1.8 is proved for all parameters, including $\alpha = -1$.
* **Property 1.16** (generalization). The complex characterization adds the converse.
* **Property 1.18(4)** (generalization). The source assumes $A$ symmetric. The equivalence holds
  without this hypothesis. See `QuarteroniSaccoSaleri.Chapter01.property_1_18_factor`.
* **After Property 1.18 and Equation (1.28)** (reading). The combined entrywise result assumes
  symmetric positive definiteness, although positivity on the diagonal holds without symmetry.
  The uniqueness clause for the square root quantifies over symmetric positive definite roots.
-/

open Finset Matrix
open scoped ComplexOrder

namespace QuarteroniSaccoSaleri.Chapter01

variable {n : ℕ}

/-! ### Definition 1.22 -/

/-- **Definition 1.22** of [quarteroni2000numerical], in $\mathbb{C}^n$. A matrix
$A \in \mathbb{C}^{n \times n}$ is **positive definite in $\mathbb{C}^n$** if for every
$x \in \mathbb{C}^n$ with $x \neq 0$ the number $(Ax, x) = x^H A x$ is real and positive.

No symmetry is assumed. Property 1.17 shows that such a matrix is Hermitian. The number
$(Ax, x)$ is `star x ⬝ᵥ (A *ᵥ x)`, and "real and positive" is stated as a zero imaginary part
and a positive real part. -/
def IsPositiveDefinite (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x : Fin n → ℂ, x ≠ 0 → (star x ⬝ᵥ (A *ᵥ x)).im = 0 ∧ 0 < (star x ⬝ᵥ (A *ᵥ x)).re

/-- **Definition 1.22** of [quarteroni2000numerical], semidefinite case in $\mathbb{C}^n$. A matrix
$A \in \mathbb{C}^{n \times n}$ is **positive semidefinite in $\mathbb{C}^n$** if for every
$x \in \mathbb{C}^n$ with $x \neq 0$ the number $(Ax, x) = x^H A x$ is real and nonnegative. -/
def IsPositiveSemidefinite (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x : Fin n → ℂ, x ≠ 0 → (star x ⬝ᵥ (A *ᵥ x)).im = 0 ∧ 0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re

/-- **Definition 1.22** of [quarteroni2000numerical], in $\mathbb{R}^n$. A matrix
$A \in \mathbb{R}^{n \times n}$ is **positive definite in $\mathbb{R}^n$** if
$(Ax, x) = x^T A x > 0$ for every $x \in \mathbb{R}^n$ with $x \neq 0$.

No symmetry is assumed. Example 1.8 gives a nonsymmetric matrix that is positive definite in
$\mathbb{R}^2$. -/
def IsPositiveDefiniteReal (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)

/-- **Definition 1.22** of [quarteroni2000numerical], semidefinite case in $\mathbb{R}^n$. A matrix
$A \in \mathbb{R}^{n \times n}$ is **positive semidefinite in $\mathbb{R}^n$** if
$(Ax, x) = x^T A x \ge 0$ for every $x \in \mathbb{R}^n$ with $x \neq 0$. -/
def IsPositiveSemidefiniteReal (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 ≤ x ⬝ᵥ (A *ᵥ x)

/-- **Definition 1.22** of [quarteroni2000numerical], three reformulations. Let
$A \in \mathbb{R}^{n \times n}$ and $B \in \mathbb{C}^{n \times n}$. Then $A$ is positive
definite in $\mathbb{R}^n$ if and only if the operator $x \mapsto Ax$ on Euclidean space
$\mathbb{R}^n$ is coercive. The matrix $B$ is positive definite in $\mathbb{C}^n$ if and only if
$0 < x^H B x$ for every $x \neq 0$ in the order of $\mathbb{C}$, where $0 < z$ means that $z$ is
real and positive. Finally, if $A$, viewed as a complex matrix, is positive definite in
$\mathbb{C}^n$, then $A$ is positive definite in $\mathbb{R}^n$.

The converse of the last statement fails, by Example 1.8. The operator is
`Matrix.toEuclideanLin A` and coercivity is the backbone's `LinearMap.IsCoercive`, which in
finite dimension is positivity of the form by `LinearMap.isCoercive_iff_forall_pos`. The order
of $\mathbb{C}$ is Mathlib's `ComplexOrder`, and $A$ viewed as a complex matrix is
`Matrix.complexify A`.

**Reading.** The numbered definition gives the quadratic-form conditions directly. Their
expressions using coercivity and the complex order, and the implication from complex to real
positivity, are additional reformulations and consequences. -/
theorem definition_1_22 (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (IsPositiveDefiniteReal A ↔ (toEuclideanLin A).IsCoercive) ∧
      (IsPositiveDefinite B ↔ ∀ x : Fin n → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (B *ᵥ x)) ∧
      (IsPositiveDefinite (complexify A) → IsPositiveDefiniteReal A) := by
  refine ⟨?_, ?_, fun h x hx => ?_⟩
  · rw [LinearMap.isCoercive_iff_forall_pos]
    constructor
    · intro h x hx
      have := h (WithLp.ofLp x) (fun h0 => hx ((WithLp.ofLp_eq_zero 2).1 h0))
      rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin, star_trivial]
      simpa using this
    · intro h x hx
      have := h (WithLp.toLp 2 x) (fun h0 => hx ((WithLp.toLp_eq_zero 2).1 h0))
      rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin, star_trivial] at this
      simpa using this
  · refine forall_congr' fun x => imp_congr_right fun _ => ?_
    rw [Complex.lt_def]
    simp only [Complex.zero_re, Complex.zero_im]
    exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩
  · have hz : (fun i => (x i : ℂ)) ≠ 0 := fun h0 =>
      hx (funext fun i => by simpa using congrFun h0 i)
    have := (h _ hz).2
    rw [re_star_dotProduct_complexify_mulVec] at this
    simpa using this

/-- **Example 1.8** of [quarteroni2000numerical], the matrix (1.27). For $\alpha \in \mathbb{R}$,
this is the matrix
$$A = \begin{bmatrix} 2 & \alpha \\ -2 - \alpha & 2 \end{bmatrix}.$$
-/
def example_1_8_matrix (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![2, α; -2 - α, 2]

/-- **Example 1.8** of [quarteroni2000numerical]. Let $\alpha \in \mathbb{R}$ and let $A$ be the
matrix (1.27). For every $x \in \mathbb{R}^2$,
$$(Ax, x) = 2 (x_1^2 + x_2^2 - x_1 x_2),$$
and $A$ is positive definite in $\mathbb{R}^2$. If $\alpha \neq -1$, then $A$ is not symmetric.
For $x = (1, i) \in \mathbb{C}^2$ the imaginary part of $(Ax, x)$ is $2\alpha + 2$, and if
$\alpha \neq -1$, then $A$ is not positive definite in $\mathbb{C}^2$. Thus a matrix that is
positive definite in $\mathbb{R}^n$ need not be symmetric, and need not be positive definite in
$\mathbb{C}^n$.

The full value at $x = (1, i)$ is $(Ax, x) = 4 + (2\alpha + 2) i$. The components $x_1, x_2$ are
`x 0` and `x 1`, and $A$ acts on complex vectors through `Matrix.complexify`.

**Generalization.** The book treats only $\alpha \ne -1$. The quadratic identity and real positive
definiteness also hold at $\alpha = -1$. The failures of symmetry and complex positive
definiteness retain the restriction. -/
theorem example_1_8 (α : ℝ) :
    (∀ x : Fin 2 → ℝ,
        x ⬝ᵥ (example_1_8_matrix α *ᵥ x) = 2 * (x 0 ^ 2 + x 1 ^ 2 - x 0 * x 1)) ∧
      IsPositiveDefiniteReal (example_1_8_matrix α) ∧
      (α ≠ -1 → ¬ (example_1_8_matrix α).IsSymm) ∧
      (star ![1, Complex.I] ⬝ᵥ (complexify (example_1_8_matrix α) *ᵥ ![1, Complex.I])).im =
        2 * α + 2 ∧
      (α ≠ -1 → ¬ IsPositiveDefinite (complexify (example_1_8_matrix α))) := by
  have hq : ∀ x : Fin 2 → ℝ,
      x ⬝ᵥ (example_1_8_matrix α *ᵥ x) = 2 * (x 0 ^ 2 + x 1 ^ 2 - x 0 * x 1) := fun x => by
    simp [example_1_8_matrix, dotProduct, mulVec, Fin.sum_univ_two]
    ring
  have him : (star ![1, Complex.I] ⬝ᵥ
      (complexify (example_1_8_matrix α) *ᵥ ![1, Complex.I])).im = 2 * α + 2 := by
    rw [im_star_dotProduct_complexify_mulVec]
    simp [example_1_8_matrix, dotProduct, mulVec, Fin.sum_univ_two]
    ring
  refine ⟨hq, fun x hx => ?_, fun hα hS => hα ?_, him, fun hα h => ?_⟩
  · rw [hq]
    have h0 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
    have : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      rcases h0 with h0 | h0 <;> positivity
    nlinarith [sq_nonneg (x 0 - x 1)]
  · have := hS.apply 0 1
    simp [example_1_8_matrix] at this
    linarith
  · have hne : ![(1 : ℂ), Complex.I] ≠ 0 := fun h0 => by
      have := congrFun h0 0
      simp at this
    have := (h _ hne).1
    rw [him] at this
    exact hα (by linarith)

/-! ### Definition 1.23 and Properties 1.15–1.17 -/

/-- **Definition 1.23** of [quarteroni2000numerical]. The **symmetric part** of
$A \in \mathbb{R}^{n \times n}$ is $A_S = \frac{1}{2}(A + A^T)$, its **skew-symmetric part** is
$A_{SS} = \frac{1}{2}(A - A^T)$, and $A = A_S + A_{SS}$. For $B \in \mathbb{C}^{n \times n}$ the
same holds with $B^H$ in place of $A^T$.

The two parts are Mathlib's `selfAdjointPart ℝ A` and `skewAdjointPart ℝ A` on the star module
of real matrices, in which `star A` is $A^T$. The theorem identifies them with the formulas of
the book. The decomposition is `StarModule.selfAdjointPart_add_skewAdjointPart`. The complex
matrices form a star module over $\mathbb{R}$ with the conjugate transpose as star. -/
theorem definition_1_23 (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (selfAdjointPart ℝ A : Matrix (Fin n) (Fin n) ℝ) = (1 / 2 : ℝ) • (A + Aᵀ) ∧
      (skewAdjointPart ℝ A : Matrix (Fin n) (Fin n) ℝ) = (1 / 2 : ℝ) • (A - Aᵀ) ∧
      (selfAdjointPart ℝ A : Matrix (Fin n) (Fin n) ℝ) + skewAdjointPart ℝ A = A ∧
      (selfAdjointPart ℝ B : Matrix (Fin n) (Fin n) ℂ) = (1 / 2 : ℝ) • (B + Bᴴ) ∧
      (skewAdjointPart ℝ B : Matrix (Fin n) (Fin n) ℂ) = (1 / 2 : ℝ) • (B - Bᴴ) ∧
      (selfAdjointPart ℝ B : Matrix (Fin n) (Fin n) ℂ) + skewAdjointPart ℝ B = B := by
  refine ⟨?_, ?_, StarModule.selfAdjointPart_add_skewAdjointPart ℝ A, ?_, ?_,
    StarModule.selfAdjointPart_add_skewAdjointPart ℝ B⟩ <;>
    simp only [selfAdjointPart_apply_coe, skewAdjointPart_apply_coe, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, invOf_eq_inv, one_div]

/-- **Property 1.15** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$. For every
$x \in \mathbb{R}^n$, $x^T A_{SS} x = 0$ and $x^T A x = x^T A_S x$. Hence $A$ is positive
definite in $\mathbb{R}^n$ if and only if its symmetric part $A_S$ is positive definite in
$\mathbb{R}^n$. For the matrix (1.27) of Example 1.8 and every $\alpha \in \mathbb{R}$, the
symmetric part is
$$\begin{bmatrix} 2 & -1 \\ -1 & 2 \end{bmatrix}.$$

The quadratic form of a skew-symmetric matrix vanishes, which gives the first identity. The
parts are written as `(1 / 2 : ℝ) • (A + Aᵀ)` and `(1 / 2 : ℝ) • (A - Aᵀ)`. The parameter
$\alpha$ is used only in the last clause, the book's instance. -/
theorem property_1_15 (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    (∀ x : Fin n → ℝ, x ⬝ᵥ (((1 / 2 : ℝ) • (A - Aᵀ)) *ᵥ x) = 0) ∧
      (∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (((1 / 2 : ℝ) • (A + Aᵀ)) *ᵥ x)) ∧
      (IsPositiveDefiniteReal A ↔ IsPositiveDefiniteReal ((1 / 2 : ℝ) • (A + Aᵀ))) ∧
      (1 / 2 : ℝ) • (example_1_8_matrix α + (example_1_8_matrix α)ᵀ) = !![2, -1; -1, 2] := by
  have hT : ∀ x : Fin n → ℝ, x ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := fun x => by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hS : ∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (((1 / 2 : ℝ) • (A + Aᵀ)) *ᵥ x) := fun x => by
    rw [smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add, hT, smul_eq_mul]
    ring
  refine ⟨fun x => ?_, hS, ?_, ?_⟩
  · rw [smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, hT, sub_self, smul_zero]
  · exact ⟨fun h x hx => (hS x).symm ▸ h x hx, fun h x hx => (hS x) ▸ h x hx⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [example_1_8_matrix] <;> ring

/-- **Property 1.16** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$. Then
$(Ax, x)$ is real for every $x \in \mathbb{C}^n$ if and only if $A$ is Hermitian. Let
$B \in \mathbb{R}^{n \times n}$. If $(Bx, x)$ is real for every $x \in \mathbb{C}^n$, then $B$
is symmetric.

The forward direction of the first clause is Mathlib's
`LinearMap.isSymmetric_iff_inner_map_self_real` for the Euclidean operator, and the converse
direction is `Matrix.IsHermitian.im_star_dotProduct_mulVec_self`. In the second clause, $B$ acts
on complex vectors through `Matrix.complexify`.

**Generalization.** The book gives the implication from a real-valued quadratic form to a
Hermitian matrix. The complex clause adds the converse. In the real clause, as in the book,
the form is tested on complex vectors. -/
theorem property_1_16 (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℝ) :
    ((∀ x : Fin n → ℂ, (star x ⬝ᵥ (A *ᵥ x)).im = 0) ↔ A.IsHermitian) ∧
      ((∀ x : Fin n → ℂ, (star x ⬝ᵥ (complexify B *ᵥ x)).im = 0) → B.IsSymm) := by
  have key : ∀ (A : Matrix (Fin n) (Fin n) ℂ),
      (∀ x : Fin n → ℂ, (star x ⬝ᵥ (A *ᵥ x)).im = 0) → A.IsHermitian := fun A h => by
    rw [← isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
    intro v
    have hv : inner ℂ (toEuclideanLin A v) v =
        star (star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)) := by
      rw [← inner_conj_symm, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin,
        dotProduct_comm]
      rfl
    rw [hv, Complex.star_def, Complex.conj_conj]
    exact (Complex.conj_eq_iff_im.2 (h _)).symm
  refine ⟨⟨key A, fun hA x => by simpa using hA.im_star_dotProduct_mulVec_self x⟩, fun h => ?_⟩
  exact isHermitian_iff_isSymm.1 ((isHermitian_complexify_iff _).1 (key _ h))

/-- **Property 1.17** of [quarteroni2000numerical]. A matrix $A \in \mathbb{C}^{n \times n}$ is
positive definite in $\mathbb{C}^n$ if and only if it is Hermitian with $x^H A x > 0$ for every
$x \neq 0$, which is Mathlib's `Matrix.PosDef`. A Hermitian matrix has this property if and only
if all its eigenvalues are positive. A matrix that is positive definite in $\mathbb{C}^n$ is
nonsingular.

The first equivalence uses `Matrix.posDef_iff_dotProduct_mulVec`, with Property 1.16 for the
Hermitian symmetry. The second is `Matrix.IsHermitian.posDef_iff_eigenvalues_pos`, and
nonsingularity is `Matrix.PosDef.isUnit`. -/
theorem property_1_17 (A : Matrix (Fin n) (Fin n) ℂ) :
    (IsPositiveDefinite A ↔ A.PosDef) ∧
      (A.PosDef ↔ ∃ hA : A.IsHermitian, ∀ i, 0 < hA.eigenvalues i) ∧
      (IsPositiveDefinite A → IsUnit A) := by
  have h1 : IsPositiveDefinite A ↔ A.PosDef := by
    rw [posDef_iff_dotProduct_mulVec, (definition_1_22 0 A).2.1]
    constructor
    · intro h
      refine ⟨(property_1_16 A 0).1.1 fun x => ?_, fun x hx => h x hx⟩
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · exact ((Complex.lt_def.1 (h x hx)).2).symm
    · exact fun h x hx => h.2 hx
  exact ⟨h1, ⟨fun h => ⟨h.1, h.eigenvalues_pos⟩, fun ⟨hA, h⟩ => hA.posDef_iff_eigenvalues_pos.2 h⟩,
    fun h => (h1.1 h).isUnit⟩

/-! ### Property 1.18 -/

/-- **Property 1.18(1)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric. Then $A$ is positive definite if and only if $(Ax, x) > 0$ for every nonzero
$x \in \mathbb{R}^n$, that is, if and only if $A$ is positive definite in $\mathbb{R}^n$.

"Positive definite" on the left is Mathlib's `Matrix.PosDef`, which is positive definiteness in
$\mathbb{C}^n$ by Property 1.17. The proof is `Matrix.posDef_iff_dotProduct_mulVec`, where
`star` is the identity over $\mathbb{R}$. -/
theorem property_1_18_quadratic {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.PosDef ↔ IsPositiveDefiniteReal A := by
  rw [posDef_iff_dotProduct_mulVec, isHermitian_iff_isSymm]
  simp only [star_trivial]
  exact ⟨fun h x hx => h.2 hx, fun h => ⟨hA, fun x hx => h x hx⟩⟩

/-- **Property 1.18(2)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric. Then $A$ is positive definite if and only if, for every set of indices
$s \subseteq \{1, \dots, n\}$, all eigenvalues of the principal submatrix $A(s, s)$ are
positive.

The principal submatrix is `A.submatrix Subtype.val Subtype.val`, indexed by the elements of
$s$; for $s = \emptyset$ the condition is empty. The proof is the backbone's
`Matrix.posDef_iff_forall_principalSubmatrix_eigenvalues_pos`. -/
theorem property_1_18_eigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.PosDef ↔ ∀ (s : Finset (Fin n)) (i : s),
      0 < ((isHermitian_iff_isSymm.2 hA).submatrix (Subtype.val : s → Fin n)).eigenvalues i :=
  posDef_iff_forall_principalSubmatrix_eigenvalues_pos (isHermitian_iff_isSymm.2 hA)

/-- **Property 1.18(3)** of [quarteroni2000numerical] (Sylvester's criterion). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric. Then $A$ is positive definite if and only if its
leading principal minors $d_k = \det A(1{:}k, 1{:}k)$, $k = 1, \dots, n$, are all positive.

Indices start at $0$, so for `k : Fin n` the matrix `A.leadingPrincipalSubmatrix k` is the
leading principal submatrix of order $k + 1$. The proof is the backbone's
`Matrix.posDef_iff_forall_det_leadingPrincipalSubmatrix_pos`. -/
theorem property_1_18_minors {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.PosDef ↔ ∀ k : Fin n, 0 < (A.leadingPrincipalSubmatrix k).det :=
  posDef_iff_forall_det_leadingPrincipalSubmatrix_pos (isHermitian_iff_isSymm.2 hA)

/-- **Property 1.18(4)** of [quarteroni2000numerical]. A matrix $A \in \mathbb{R}^{n \times n}$ is
positive definite if and only if $A = H^T H$ for some nonsingular
$H \in \mathbb{R}^{n \times n}$.

**Generalization.** The source assumes that $A$ is symmetric. Neither direction needs this
hypothesis: $H^T H$ is symmetric, and a positive definite matrix (`Matrix.PosDef`) is symmetric
by definition.

The proof is the backbone's `Matrix.posDef_iff_exists_isUnit_conjTranspose_mul_self`. -/
theorem property_1_18_factor (A : Matrix (Fin n) (Fin n) ℝ) :
    A.PosDef ↔ ∃ H : Matrix (Fin n) (Fin n) ℝ, IsUnit H ∧ A = Hᵀ * H := by
  rw [posDef_iff_exists_isUnit_conjTranspose_mul_self]
  simp only [conjTranspose_eq_transpose_of_trivial, eq_comm]

/-- **Section 1.12** of [quarteroni2000numerical], remarks after Property 1.18. Let
$A \in \mathbb{R}^{n \times n}$ be positive definite. Then every diagonal entry is positive,
$a_{ii} = e_i^T A e_i > 0$, and
$$|a_{ij}| \le \max(a_{ii}, a_{jj}) \quad \text{for all } i, j,$$
so an entry of largest modulus lies on the diagonal. These are necessary conditions for positive
definiteness.

The first part is Mathlib's `Matrix.PosDef.diag_pos`, and the second is the backbone's
`Matrix.PosDef.norm_apply_le_max_re_diag`.

**Reading.** The source's positive-diagonal argument applies to every real positive definite
matrix. The combined declaration assumes symmetric positive definiteness and gives a pointwise
bound on the entries, which implies the claim about the entry of largest modulus. -/
theorem posDef_diag_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    (∀ i, 0 < A i i) ∧ ∀ i j, |A i j| ≤ max (A i i) (A j j) :=
  ⟨fun _ => hA.diag_pos, fun i j => by simpa using hA.norm_apply_le_max_re_diag i j⟩

open scoped MatrixOrder in
/-- **Equation (1.28)** of [quarteroni2000numerical], the energy norm. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite. Then $A^{1/2}$ is the only
positive definite matrix $X$ with $X^2 = A$. For every $x \in \mathbb{R}^n$,
$$\|x\|_A = \|A^{1/2} x\|_2 = (Ax, x)^{1/2},$$
and $\|x\|_A$ is the norm of $x$ in the energy space of $A$, so it is a vector norm, the
**energy norm**. The **energy scalar product** satisfies $(x, y)_A = (Ax, y)$ for all
$x, y \in \mathbb{R}^n$.

The matrix $A^{1/2}$ is Mathlib's `CFC.sqrt A` in the Loewner order, and its uniqueness is
`CFC.sqrt_eq_iff`. The energy norm is the backbone's `energyNorm (toEuclideanLin A) x`, and the
energy scalar product is `energyInner (toEuclideanLin A) x y`. The energy space is `WithEnergy`
of `Numlib.Analysis.InnerProductSpace.Energy`, built from
`Matrix.posDef_iff_isSymmetricCoercive`, and `WithEnergy.equiv` maps $x$ to its copy there.

**Reading.** Uniqueness of the positive square root is stated using `Matrix.PosDef`, so the
competing square roots in the equivalence are required to be symmetric. The energy norm and
inner-product formulas use the same symmetric positive definite $A$ as the source. -/
theorem equation_1_28 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    (∀ X : Matrix (Fin n) (Fin n) ℝ, X.PosDef ∧ X ^ 2 = A ↔ X = CFC.sqrt A) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        energyNorm (toEuclideanLin A) x = ‖toEuclideanLin (CFC.sqrt A) x‖ ∧
          energyNorm (toEuclideanLin A) x = √(inner ℝ x (toEuclideanLin A x))) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        ‖WithEnergy.equiv (toEuclideanLin A) ((posDef_iff_isSymmetricCoercive A).1 hA) x‖ =
          energyNorm (toEuclideanLin A) x) ∧
      ∀ x y : EuclideanSpace ℝ (Fin n),
        energyInner (toEuclideanLin A) x y = inner ℝ y (toEuclideanLin A x) := by
  have hA0 : 0 ≤ A := nonneg_iff_posSemidef.2 hA.posSemidef
  have hsq : CFC.sqrt A ^ 2 = A := CFC.sq_sqrt A hA0
  have hS : (CFC.sqrt A).PosSemidef := nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)
  refine ⟨fun X => ⟨fun ⟨hX, hX2⟩ => ?_, fun hX => ?_⟩, fun x => ⟨?_, ?_⟩,
    fun x => WithEnergy.norm_equiv _ _ x, fun x y => real_inner_comm _ _⟩
  · exact ((CFC.sqrt_eq_iff A X hA0 (nonneg_iff_posSemidef.2 hX.posSemidef)).2
      (by rw [← sq, hX2])).symm
  · subst hX
    refine ⟨hS.posDef_iff_isUnit.2 ?_, hsq⟩
    have : IsUnit (CFC.sqrt A ^ 2) := by rw [hsq]; exact hA.isUnit
    exact (isUnit_pow_iff two_ne_zero).1 this
  · rw [energyNorm, norm_eq_sqrt_real_inner, RCLike.re_to_real, ← hS.1.eq,
      toEuclideanLin_conjTranspose_inner_left, ← toEuclideanLin_mul_apply, hS.1.eq, ← sq, hsq,
      real_inner_comm]
  · rw [energyNorm, RCLike.re_to_real, real_inner_comm]

/-! ### Definition 1.24: diagonal dominance -/

/-- **Definition 1.24** of [quarteroni2000numerical]. A matrix $A \in \mathbb{R}^{n \times n}$ is
**diagonally dominant by rows** if $|a_{ii}| \ge \sum_{j \neq i} |a_{ij}|$ for every $i$, and
**diagonally dominant by columns** if $|a_{ii}| \ge \sum_{j \neq i} |a_{ji}|$ for every $i$. It
is **strictly diagonally dominant** by rows or by columns if the inequalities are strict.

The theorem states that the backbone's `Matrix.IsDiagDominant`, `Matrix.IsColDiagDominant`,
`Matrix.IsStrictDiagDominant` and `Matrix.IsStrictColDiagDominant` of
`Numlib.LinearAlgebra.Matrix.DiagDominant` are these four conditions. -/
theorem definition_1_24 (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.IsDiagDominant ↔ ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ |A i i|) ∧
      (A.IsColDiagDominant ↔ ∀ i, ∑ j ∈ univ.erase i, |A j i| ≤ |A i i|) ∧
      (A.IsStrictDiagDominant ↔ ∀ i, ∑ j ∈ univ.erase i, |A i j| < |A i i|) ∧
      (A.IsStrictColDiagDominant ↔ ∀ i, ∑ j ∈ univ.erase i, |A j i| < |A i i|) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- **Section 1.12** of [quarteroni2000numerical], after Definition 1.24. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and strictly diagonally dominant by rows, with
$a_{ii} > 0$ for every $i$. Then $A$ is positive definite.

The proof is the backbone's `Matrix.IsStrictDiagDominant.posDef`, which uses Gershgorin's
theorem. -/
theorem posDef_of_isStrictDiagDominant {A : Matrix (Fin n) (Fin n) ℝ} (hS : A.IsSymm)
    (hd : A.IsStrictDiagDominant) (hpos : ∀ i, 0 < A i i) : A.PosDef :=
  hd.posDef (isHermitian_iff_isSymm.2 hS) fun i => by simpa using hpos i

/-! ### Definition 1.25: M-matrices -/

/-- **Definition 1.25** of [quarteroni2000numerical]. A matrix $A \in \mathbb{R}^{n \times n}$ is an
**M-matrix** if it is nonsingular, $a_{ij} \le 0$ for $i \neq j$, and all entries of $A^{-1}$
are nonnegative.

The theorem states that the backbone's `Matrix.IsMMatrix` is this condition. Its three fields
are the three conditions, and the third is `Matrix.EntrywiseNonneg` of the inverse. -/
theorem definition_1_25 (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsMMatrix ↔ IsUnit A ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧ ∀ i j, 0 ≤ A⁻¹ i j :=
  ⟨fun h => ⟨h.isUnit, h.offDiag_nonpos, fun i j => h.inv_entrywiseNonneg.apply i j⟩,
    fun ⟨hu, hoff, hinv⟩ => ⟨hoff, hu, entrywiseNonneg_iff.2 hinv⟩⟩

/-- **Section 1.12** of [quarteroni2000numerical], the discrete maximum principle. Let
$A \in \mathbb{R}^{n \times n}$ be an M-matrix and let $x \in \mathbb{R}^n$. If $Ax \le 0$, then
$x \le 0$, where the inequalities are componentwise.

The proof is the backbone's `Matrix.IsMMatrix.nonpos_of_mulVec_nonpos`: $x = A^{-1}(Ax)$ and
$A^{-1} \ge 0$. -/
theorem discreteMaximumPrinciple {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix)
    {x : Fin n → ℝ} (hx : A *ᵥ x ≤ 0) : x ≤ 0 :=
  hA.nonpos_of_mulVec_nonpos hx

/-- **Property 1.19** of [quarteroni2000numerical] (M-criterion). Let
$A \in \mathbb{R}^{n \times n}$ satisfy $a_{ij} \le 0$ for $i \neq j$. Then $A$ is an M-matrix
if and only if there is a vector $w \in \mathbb{R}^n$ with $w > 0$ and $Aw > 0$, componentwise.

The proof is the backbone's `Matrix.isMMatrix_iff_exists_pos_mulVec_pos`. -/
theorem property_1_19 {A : Matrix (Fin n) (Fin n) ℝ} (hoff : ∀ i j, i ≠ j → A i j ≤ 0) :
    A.IsMMatrix ↔ ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∀ i, 0 < (A *ᵥ w) i :=
  isMMatrix_iff_exists_pos_mulVec_pos hoff

/-- **Property 1.20** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be strictly
diagonally dominant by rows, with $a_{ij} \le 0$ for $i \neq j$ and $a_{ii} > 0$ for every $i$.
Then $A$ is an M-matrix.

Under these hypotheses every row sum of $A$ is positive, so this is Property 1.19 with
$w = (1, \dots, 1)$. The proof is the backbone's `Matrix.IsStrictDiagDominant.isMMatrix`. -/
theorem property_1_20 {A : Matrix (Fin n) (Fin n) ℝ} (hd : A.IsStrictDiagDominant)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hpos : ∀ i, 0 < A i i) : A.IsMMatrix :=
  hd.isMMatrix hpos hoff

end QuarteroniSaccoSaleri.Chapter01
