/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg

/-!
# Saad: Conventions of the library

This module holds the notation and the small lemmas that the whole surface library for
[saad2003iterative] shares. The book writes a vector of $\mathbb{R}^n$ or $\mathbb{C}^n$, a matrix
product $Ax$, and an inner product $(x, y) = \sum_i x_i \bar{y}_i$. The library has two Lean
pictures of these objects: the Euclidean space `EuclideanSpace 𝕜 (Fin n)`, where the inner product
and the norm live, and the plain function type `Fin n → 𝕜`, where componentwise statements live. The
lemmas here translate between the two pictures, define the extreme eigenvalues $\lambda_{\min}(H)$
and $\lambda_{\max}(H)$ of a Hermitian matrix, and prove the quadratic-form bounds $\lambda_{\min}
\|x\|^2 \le (Hx, x) \le \lambda_{\max} \|x\|^2$.

## Main definitions

* `SaadSparse.lambdaMin`: the smallest eigenvalue $\lambda_{\min}(H)$ of a Hermitian matrix $H$.
* `SaadSparse.lambdaMax`: the largest eigenvalue $\lambda_{\max}(H)$ of a Hermitian matrix $H$.

## Main results

* `SaadSparse.real_inner_toEuclideanLin`: for real $A$, the inner product $(Au, u)$ is the dot
  product of the coordinate vectors of $Au$ and $u$.
* `SaadSparse.lambdaMin_le_lambdaMax`: $\lambda_{\min}(H) \le \lambda_{\max}(H)$.
* `SaadSparse.isSymmetricBoundedBy_toEuclideanLin`: $\lambda_{\min}(H) \|x\|^2 \le (Hx, x) \le
  \lambda_{\max}(H) \|x\|^2$ for every $x$.
* `SaadSparse.norm_complexify_mulVec`: complexification does not change the Euclidean norm of $Ax$.
* `SaadSparse.max_zero_eq_half` and `SaadSparse.min_zero_eq_half`: the positive part
  $(z)^+ = (z + |z|)/2$ and the negative part $(z)^- = (z - |z|)/2$ of the book are $\max(z, 0)$ and
  $\min(z, 0)$.

## Notation

* `A ⬝ x`: the product $Ax$ of the book, that is `Matrix.toEuclideanLin A x` on
  `EuclideanSpace 𝕜 (Fin n)`. It is the only notation that the library introduces. It is scoped to
  the namespace `SaadSparse`, and a module that uses it writes `open scoped SaadSparse`. It is
  different from Mathlib's `x ⬝ᵥ y` (`Matrix.dotProduct`) and `A *ᵥ x` (`Matrix.mulVec`), which act
  on the plain function type.

## Conventions

* A vector of $\mathbb{R}^n$ or $\mathbb{C}^n$ is an element of `EuclideanSpace 𝕜 (Fin n)`, and a
  matrix is a `Matrix (Fin n) (Fin n) 𝕜`.
* Componentwise statements use the plain function type `Fin n → 𝕜` with `A *ᵥ x` and `x ⬝ᵥ y`. The
  two pictures are related by `WithLp.toLp 2` and `WithLp.ofLp`, through
  `Matrix.ofLp_toEuclideanLin` and `Matrix.toEuclideanLin_toLp` of
  `Numlib.Analysis.Matrix.ToEuclideanLin`.
* The inner product $(x, y) = \sum_i x_i \bar{y}_i$ of the book is Mathlib's `inner 𝕜 y x`.
  Mathlib's inner product is conjugate-linear in the first argument, and the book's in the second.
  Over $\mathbb{R}$ the two agree.
* For a Hermitian matrix $H$, $\lambda_{\min}(H)$ and $\lambda_{\max}(H)$ are `SaadSparse.lambdaMin`
  and `SaadSparse.lambdaMax`, the extreme values of `Matrix.IsHermitian.eigenvalues`.
* A real matrix is viewed as a complex matrix through `Matrix.complexify`, and the spectral radius
  $\rho(A)$ is `Matrix.complexSpectralRadius A`.

## Deviations from the source

* **Scope.** The common Hermitian estimate gives the inequalities from the extremal Rayleigh
  quotient formulas. See `SaadSparse.isSymmetricBoundedBy_toEuclideanLin`.
-/

namespace SaadSparse

open Matrix Finset

/-- The product $Ax$ of the book: `A ⬝ x` is `Matrix.toEuclideanLin A x`, the matrix $A$ acting on a
vector of `EuclideanSpace 𝕜 (Fin n)`. -/
scoped notation:75 A " ⬝ " x => Matrix.toEuclideanLin A x

section Glue

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- Let $A \in \mathbb{R}^{n \times n}$ and $u \in \mathbb{R}^n$. The inner product $(Au, u)$ of the
book, written `inner ℝ u (A ⬝ u)`, equals the dot product $(Au) \cdot u$ of the coordinate
vectors, `(A *ᵥ u) ⬝ᵥ u`. -/
theorem real_inner_toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u (A ⬝ u) = (A *ᵥ WithLp.ofLp u) ⬝ᵥ WithLp.ofLp u := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Let $A \in \mathbb{R}^{n \times n}$ and $x, y \in \mathbb{R}^n$. The inner product $(Ax, y)$ of
the book, written `inner ℝ y (A ⬝ x)`, equals the dot product $(Ax) \cdot y$ of the coordinate
vectors, `(A *ᵥ x) ⬝ᵥ y`. -/
theorem real_inner_toEuclideanLin' (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ y (A ⬝ x) = (A *ᵥ WithLp.ofLp x) ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Let $A \in \mathbb{R}^{n \times n}$ and $u \in \mathbb{R}^n$. The inner product $(Au, u)$, in
Mathlib's order of arguments `inner ℝ (A ⬝ u) u`, equals the dot product $(Au) \cdot u$ of the
coordinate vectors. -/
theorem real_inner_apply_self (A : Matrix (Fin n) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (A ⬝ u) u = (A *ᵥ WithLp.ofLp u) ⬝ᵥ WithLp.ofLp u := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp

/-- Let $A \in \mathbb{R}^{n \times n}$ and $x, y \in \mathbb{R}^n$. The inner product $(Ax, y)$, in
Mathlib's order of arguments `inner ℝ (A ⬝ x) y`, equals the dot product $y \cdot (Ax)$ of the
coordinate vectors. -/
theorem real_inner_apply (A : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (A ⬝ x) y = WithLp.ofLp y ⬝ᵥ (A *ᵥ WithLp.ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

omit [RCLike 𝕜] in
/-- The map `WithLp.toLp 2` from `Fin n → 𝕜` to `EuclideanSpace 𝕜 (Fin n)` is injective. Therefore
an identity between vectors can be moved from one picture to the other. -/
theorem toLp_injective : Function.Injective (WithLp.toLp 2 : (Fin n → 𝕜) → EuclideanSpace 𝕜 _) :=
  fun _ _ h => congrArg WithLp.ofLp h

/-- For $x \in \mathbb{R}^n$, the squared Euclidean norm is the dot product of the coordinate vector
with itself: $\|x\|^2 = x \cdot x$. -/
theorem real_norm_sq_eq_dotProduct (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

end Glue

section Eigenvalues

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The **smallest eigenvalue** $\lambda_{\min}(H)$ of a Hermitian matrix
$H \in \mathbb{K}^{n \times n}$ with $n \ge 1$: the minimum of the eigenvalues
`Matrix.IsHermitian.eigenvalues` of $H$. -/
noncomputable def lambdaMin [NeZero n] {H : Matrix (Fin n) (Fin n) 𝕜} (hH : H.IsHermitian) : ℝ :=
  univ.inf' univ_nonempty hH.eigenvalues

/-- The **largest eigenvalue** $\lambda_{\max}(H)$ of a Hermitian matrix
$H \in \mathbb{K}^{n \times n}$ with $n \ge 1$: the maximum of the eigenvalues
`Matrix.IsHermitian.eigenvalues` of $H$. -/
noncomputable def lambdaMax [NeZero n] {H : Matrix (Fin n) (Fin n) 𝕜} (hH : H.IsHermitian) : ℝ :=
  univ.sup' univ_nonempty hH.eigenvalues

variable [NeZero n] {H : Matrix (Fin n) (Fin n) 𝕜} (hH : H.IsHermitian)

include hH in
/-- Let $H \in \mathbb{K}^{n \times n}$ be Hermitian, with $n \ge 1$. Then every eigenvalue
$\lambda_i$ of $H$ satisfies $\lambda_{\min}(H) \le \lambda_i$. -/
theorem lambdaMin_le_eigenvalues (i : Fin n) : lambdaMin hH ≤ hH.eigenvalues i :=
  inf'_le _ (mem_univ i)

include hH in
/-- Let $H \in \mathbb{K}^{n \times n}$ be Hermitian, with $n \ge 1$. Then every eigenvalue
$\lambda_i$ of $H$ satisfies $\lambda_i \le \lambda_{\max}(H)$. -/
theorem eigenvalues_le_lambdaMax (i : Fin n) : hH.eigenvalues i ≤ lambdaMax hH :=
  le_sup' _ (mem_univ i)

include hH in
/-- Let $H \in \mathbb{K}^{n \times n}$ be Hermitian, with $n \ge 1$. Then
$\lambda_{\min}(H) \le \lambda_{\max}(H)$.

The interval $[\lambda_{\min}, \lambda_{\max}]$ that carries the quadratic-form bounds of
Section 1.9.2 of [saad2003iterative] is therefore nonempty. The hypothesis $n \ge 1$ is
necessary, because there must be an eigenvalue between the two numbers. -/
theorem lambdaMin_le_lambdaMax : lambdaMin hH ≤ lambdaMax hH :=
  (lambdaMin_le_eigenvalues hH ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩).trans
    (eigenvalues_le_lambdaMax hH _)

include hH in
/-- Let $H \in \mathbb{K}^{n \times n}$ be Hermitian, with $n \ge 1$. Then the operator
$x \mapsto Hx$ on $\mathbb{K}^n$ is symmetric, and for every $x \in \mathbb{K}^n$
$$\lambda_{\min}(H) \|x\|^2 \le \operatorname{Re} (Hx, x) \le \lambda_{\max}(H) \|x\|^2.$$

The two halves are the extremal characterizations (1.38) and (1.40) of Section 1.9.2 of
[saad2003iterative], with the denominator $(x, x)$ cleared. The statement is
`LinearMap.IsSymmetricBoundedBy` for `Matrix.toEuclideanLin H`, the form of a spectral
hypothesis that the backbone takes.

**Reading.** The theorem gives the two quadratic-form bounds, after clearing the denominators,
including at the zero vector. The original displays identify the extrema of the Rayleigh quotient
and hence include attainment.
-/
theorem isSymmetricBoundedBy_toEuclideanLin :
    (toEuclideanLin H).IsSymmetricBoundedBy (lambdaMin hH) (lambdaMax hH) :=
  hH.isSymmetricBoundedBy_toEuclideanLin fun i =>
    ⟨lambdaMin_le_eigenvalues hH i, eigenvalues_le_lambdaMax hH i⟩

end Eigenvalues

section Complexify

variable {n : ℕ}

/-- Let $A \in \mathbb{R}^{n \times n}$ and $x \in \mathbb{R}^n$. The Euclidean norm of $Ax$ does
not change when $A$ and $x$ are viewed as a complex matrix and a complex vector:
$\|A_{\mathbb{C}} x_{\mathbb{C}}\|_2 = \|Ax\|_2$, where $A_{\mathbb{C}}$ is
`Matrix.complexify A`. -/
theorem norm_complexify_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ‖(WithLp.toLp 2 (complexify A *ᵥ fun i => (x i : ℂ)) : EuclideanSpace ℂ (Fin n))‖ =
      ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ (Fin n))‖ := by
  have h : (complexify A *ᵥ fun i => (x i : ℂ)) = fun i => ((A *ᵥ x) i : ℂ) := by
    funext i
    simp [mulVec, dotProduct, complexify]
  rw [h, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp

end Complexify

section PositiveNegativePart

/-!
### The positive and negative parts of the book

The book writes $(z)^+ = (z + |z|)/2$ and $(z)^- = (z - |z|)/2$ for the positive and negative parts
of a real number $z$, in the upwind schemes of Section 2.2.3 and again in the finite volume fluxes
of Section 2.5. The negative part of the book is *nonpositive*. Mathlib's `negPart` is different: it
is $\max(-z, 0)$.
-/

/-- For $z \in \mathbb{R}$, the positive part $(z)^+ = (z + |z|)/2$ of the book is $\max(z, 0)$. -/
theorem max_zero_eq_half (z : ℝ) : max z 0 = (z + |z|) / 2 := by
  rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> [rw [max_eq_left]; rw [max_eq_right]] <;>
    linarith

/-- For $z \in \mathbb{R}$, the negative part $(z)^- = (z - |z|)/2$ of the book is $\min(z, 0)$. -/
theorem min_zero_eq_half (z : ℝ) : min z 0 = (z - |z|) / 2 := by
  rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> [rw [min_eq_right]; rw [min_eq_left]] <;>
    linarith

end PositiveNegativePart

end SaadSparse
