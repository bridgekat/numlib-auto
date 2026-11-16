/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Hermitian`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Matrix.ToEuclideanLin

/-!
# The Hermitian part of a matrix

Every square complex matrix $A$ splits as $A = H + iS$ with $$H = \frac{A + A^H}{2}, \qquad S =
\frac{A - A^H}{2i},$$ both Hermitian. The matrix $H$ is the **Hermitian part** of $A$, and
$iS = (A - A^H)/2$ is its skew-Hermitian part. This decomposition is the one of
[quarteroni2000numerical] Theorem 5.1 (the eigenvalue bounds of Hirsch and Bendixson, which put the
spectrum of $A$ in the rectangle spanned by the extreme eigenvalues of $H$ and of $S$), and of
[saad2003iterative] §1.11, equation (1.49).

The quadratic form of $A$ sees only its Hermitian part: $\operatorname{Re}(x^H A x) = x^H H x$. So a
matrix whose Hermitian part is positive definite, the unsymmetric "positive definite" of
[golub2013matrix] §4.2, is nonsingular. The module also proves that the Hermitian part commutes with
congruence and that $\|H\|_2 \le \|A\|_2$.

## Main definitions

* `Matrix.hermitianPart`: $H = (A + A^H)/2$, over any `RCLike` field.
* `Matrix.skewHermitianPart`: $S = (A - A^H)/(2i)$, over $\mathbb{C}$, as in [saad2003iterative].

## Main results

* `Matrix.hermitianPart_isHermitian`, `Matrix.skewHermitianPart_isHermitian`: $H$ and $S$ are
  Hermitian.
* `Matrix.eq_hermitianPart_add_I_smul_skewHermitianPart`: $A = H + iS$.
* `Matrix.skewHermitianPart_eq_hermitianPart`: $S$ is the Hermitian part of $-iA$, which reduces
  every statement about $S$ to one about $H$.
* `Matrix.re_inner_hermitianPart`: $\operatorname{Re} \langle Hx, x \rangle = \operatorname{Re}
  \langle Ax, x \rangle$; `Matrix.dotProduct_mulVec_hermitianPart` and
  `Matrix.mulVec_dotProduct_eq_hermitianPart` are the same identity for a real matrix and the dot
  product.
* `Matrix.star_dotProduct_hermitianPart_mulVec`: $x^H H x = \operatorname{Re}(x^H A x)$.
* `Matrix.posDef_hermitianPart_iff_forall_dotProduct_mulVec_pos`: $H$ is positive definite if and
  only if $\operatorname{Re}(x^H A x) > 0$ for all $x \ne 0$.
* `Matrix.isUnit_of_posDef_hermitianPart`, `Matrix.isUnit_of_posDef_add_transpose`: a matrix with
  positive definite Hermitian part is nonsingular; for a real $P$, the condition is that $P + P^T$
  is positive definite.
* `Matrix.IsHermitian.hermitianPart_eq`, `Matrix.hermitianPart_eq_smul_add_transpose`: the Hermitian
  part of a Hermitian matrix is the matrix, and over $\mathbb{R}$ it is $(P + P^T)/2$.
* `Matrix.hermitianPart_conjTranspose_mul_mul`: $\operatorname{herm}(X^H A X) = X^H
  \operatorname{herm}(A) X$.
* `Matrix.l2_opNorm_hermitianPart_le`: $\|H\|_2 \le \|A\|_2$ ([golub2013matrix] §4.2.2).

## Implementation notes

* The operator form is the unbundled $\frac12 (A + A^\dagger)$ of
  `ContinuousLinearMap.re_inner_hermitianPart_apply` and
  `ContinuousLinearMap.isCoerciveWith_iff_hermitianPart` in
  `Numlib.Analysis.InnerProductSpace.Coercive`. `Matrix.re_inner_hermitianPart` is that identity
  read through `Matrix.toEuclideanLin`.
* `Matrix.skewHermitianPart` is defined for complex matrices only. Over a general `RCLike` field
  the imaginary unit can be $0$, and then the division by $2i$ has no meaning.
-/

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*}

/-- The **Hermitian part** of a square matrix $A$ over $\mathbb{K}$ is $$H = \frac{A + A^H}{2}.$$
-/
noncomputable def hermitianPart (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (2⁻¹ : 𝕜) • (A + Aᴴ)

/-- For a square complex matrix $A$, the matrix $$S = \frac{A - A^H}{2i},$$ so that $A = H + iS$
with $H$ the Hermitian part of $A$. The matrix $iS = (A - A^H)/2$ is the skew-Hermitian part of
$A$, and $S$ itself is Hermitian.

Over $\mathbb{R}$ the division by $2i$ has no meaning, so this is defined over $\mathbb{C}$
only. -/
noncomputable def skewHermitianPart (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 * Complex.I)⁻¹ • (A - Aᴴ)

/-- The entries of the Hermitian part: $h_{ij} = (a_{ij} + \overline{a_{ji}})/2$. -/
@[simp]
theorem hermitianPart_apply (A : Matrix n n 𝕜) (i j : n) :
    hermitianPart A i j = (2⁻¹ : 𝕜) * (A i j + starRingEnd 𝕜 (A j i)) := rfl

/-- The entries of $S = (A - A^H)/(2i)$: $s_{ij} = (a_{ij} - \overline{a_{ji}})/(2i)$. -/
@[simp]
theorem skewHermitianPart_apply (A : Matrix n n ℂ) (i j : n) :
    skewHermitianPart A i j = (2 * Complex.I)⁻¹ * (A i j - starRingEnd ℂ (A j i)) := rfl

/-- The Hermitian part of a square matrix is Hermitian. -/
theorem hermitianPart_isHermitian (A : Matrix n n 𝕜) : (hermitianPart A).IsHermitian := by
  change ((2⁻¹ : 𝕜) • (A + Aᴴ))ᴴ = (2⁻¹ : 𝕜) • (A + Aᴴ)
  rw [conjTranspose_smul, show star (2⁻¹ : 𝕜) = 2⁻¹ by simp, conjTranspose_add,
    conjTranspose_conjTranspose, add_comm Aᴴ A]

/-- For a square complex matrix $A$, the matrix $S = (A - A^H)/(2i)$ is the Hermitian part of $-iA$.
-/
theorem skewHermitianPart_eq_hermitianPart (A : Matrix n n ℂ) :
    skewHermitianPart A = hermitianPart ((-Complex.I) • A) := by
  ext i j
  simp only [skewHermitianPart_apply, hermitianPart_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    map_neg, Complex.conj_I, neg_neg]
  rw [mul_inv, Complex.inv_I]
  ring

/-- For a square complex matrix $A$, the matrix $S = (A - A^H)/(2i)$ is Hermitian. -/
theorem skewHermitianPart_isHermitian (A : Matrix n n ℂ) : (skewHermitianPart A).IsHermitian := by
  rw [skewHermitianPart_eq_hermitianPart]
  exact hermitianPart_isHermitian _

/-- For a square complex matrix $A$, the matrix $iS = (A - A^H)/2$ is the skew-Hermitian part of
$A$. -/
theorem I_smul_skewHermitianPart (A : Matrix n n ℂ) :
    Complex.I • skewHermitianPart A = (2⁻¹ : ℂ) • (A - Aᴴ) := by
  rw [skewHermitianPart, smul_smul]
  congr 1
  rw [mul_inv, ← mul_assoc, mul_comm Complex.I (2⁻¹ : ℂ), mul_assoc,
    mul_inv_cancel₀ Complex.I_ne_zero, mul_one]

/-- **The Hermitian decomposition.** Every square complex matrix satisfies $A = H + iS$, with
$H = (A + A^H)/2$ and $S = (A - A^H)/(2i)$. -/
theorem eq_hermitianPart_add_I_smul_skewHermitianPart (A : Matrix n n ℂ) :
    A = hermitianPart A + Complex.I • skewHermitianPart A := by
  rw [I_smul_skewHermitianPart, hermitianPart, ← smul_add,
    show A + Aᴴ + (A - Aᴴ) = (2 : ℂ) • A by module, smul_smul,
    inv_mul_cancel₀ (two_ne_zero' ℂ), one_smul]

/-- The Hermitian part of a Hermitian matrix is the matrix itself. -/
theorem IsHermitian.hermitianPart_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    hermitianPart A = A := by
  rw [hermitianPart, hA.eq, ← two_smul 𝕜 A, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- For a real square matrix $P$, the Hermitian part is the symmetric part $(P + P^T)/2$. -/
theorem hermitianPart_eq_smul_add_transpose (P : Matrix n n ℝ) :
    hermitianPart P = (2⁻¹ : ℝ) • (P + Pᵀ) := by
  rw [hermitianPart, conjTranspose_eq_transpose_of_trivial]

variable [Fintype n]

variable [DecidableEq n]

/-- Let $A \in \mathbb{K}^{n \times n}$ and $x \in \mathbb{K}^n$. The real part of the quadratic
form of $A$ equals that of its Hermitian part $H$: $$\operatorname{Re} \langle Hx, x \rangle =
\operatorname{Re} \langle Ax, x \rangle.$$

This is the matrix form of `ContinuousLinearMap.re_inner_hermitianPart_apply`, through
`Matrix.toEuclideanLin`. -/
theorem re_inner_hermitianPart (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    RCLike.re (inner 𝕜 (toEuclideanLin (hermitianPart A) x) x)
      = RCLike.re (inner 𝕜 (toEuclideanLin A x) x) := by
  have hH : toEuclideanLin (hermitianPart A) =
      (2⁻¹ : 𝕜) • (toEuclideanLin A + LinearMap.adjoint (toEuclideanLin A)) := by
    rw [hermitianPart, map_smul, map_add, toEuclideanLin_conjTranspose_eq_adjoint]
  have hadj : inner 𝕜 (LinearMap.adjoint (toEuclideanLin A) x) x
      = starRingEnd 𝕜 (inner 𝕜 (toEuclideanLin A x) x) := by
    rw [LinearMap.adjoint_inner_left, inner_conj_symm]
  have key : inner 𝕜 (toEuclideanLin (hermitianPart A) x) x
      = (2⁻¹ : 𝕜) * (inner 𝕜 (toEuclideanLin A x) x
        + starRingEnd 𝕜 (inner 𝕜 (toEuclideanLin A x) x)) := by
    rw [hH]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, inner_smul_left, inner_add_left, hadj,
      map_inv₀, RCLike.conj_ofNat]
  rw [key, RCLike.add_conj, ← mul_assoc, show (2⁻¹ : 𝕜) * 2 = 1 by norm_num, one_mul,
    RCLike.ofReal_re]

/-! ### Congruence, definiteness and the spectral norm -/

omit [DecidableEq n] in
/-- Let $A$ be a square matrix on $n$ and $X$ a matrix with rows indexed by $n$. The Hermitian part
of the congruence $X^H A X$ is the congruence of the Hermitian part: $$\operatorname{herm}(X^H A
X) = X^H \operatorname{herm}(A)\, X.$$
-/
theorem hermitianPart_conjTranspose_mul_mul {k : Type*} (X : Matrix n k 𝕜)
    (A : Matrix n n 𝕜) : hermitianPart (Xᴴ * A * X) = Xᴴ * hermitianPart A * X := by
  simp only [hermitianPart, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]


omit [DecidableEq n] in
/-- Let $A \in \mathbb{K}^{n \times n}$ with Hermitian part $H$. For every $x \in \mathbb{K}^n$,
$$x^H H x = \operatorname{Re}(x^H A x).$$
-/
theorem star_dotProduct_hermitianPart_mulVec (A : Matrix n n 𝕜) (x : n → 𝕜) :
    star x ⬝ᵥ (hermitianPart A *ᵥ x) = (RCLike.re (star x ⬝ᵥ (A *ᵥ x)) : 𝕜) := by
  have h : starRingEnd 𝕜 (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (Aᴴ *ᵥ x) := by
    rw [starRingEnd_apply, star_dotProduct, star_star, star_mulVec, ← dotProduct_mulVec]
  rw [hermitianPart, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, ← h,
    RCLike.add_conj, smul_eq_mul, ← mul_assoc, show (2⁻¹ : 𝕜) * 2 = 1 by norm_num, one_mul]

omit [DecidableEq n] in
/-- For a real square matrix $M$ with symmetric part $H$ and a real vector $x$, $x^T H x = x^T M x$.
This is the real case of `Matrix.star_dotProduct_hermitianPart_mulVec`. -/
theorem dotProduct_mulVec_hermitianPart (M : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (hermitianPart M *ᵥ x) = x ⬝ᵥ (M *ᵥ x) := by
  simpa using star_dotProduct_hermitianPart_mulVec M x

omit [DecidableEq n] in
/-- For a real square matrix $A$ with symmetric part $H$ and a real vector $u$,
$(Au) \cdot u = (Hu) \cdot u$. This is `Matrix.dotProduct_mulVec_hermitianPart` with the dot
product in the other order. -/
theorem mulVec_dotProduct_eq_hermitianPart (A : Matrix n n ℝ) (u : n → ℝ) :
    (A *ᵥ u) ⬝ᵥ u = (hermitianPart A *ᵥ u) ⬝ᵥ u := by
  rw [dotProduct_comm, ← dotProduct_mulVec_hermitianPart, dotProduct_comm]

omit [DecidableEq n] in
/-- Let $A \in \mathbb{K}^{n \times n}$. The Hermitian part of $A$ is positive definite if and only
if $$\operatorname{Re}(x^H A x) > 0 \quad \text{for all } x \ne 0.$$ Over $\mathbb{R}$ the
condition is $x^T A x > 0$ for all $x \ne 0$, the "positive definite" of [golub2013matrix] §4.2
for unsymmetric matrices. -/
theorem posDef_hermitianPart_iff_forall_dotProduct_mulVec_pos (A : Matrix n n 𝕜) :
    (hermitianPart A).PosDef ↔ ∀ x : n → 𝕜, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x)) := by
  rw [posDef_iff_dotProduct_mulVec]
  simp only [hermitianPart_isHermitian, true_and, star_dotProduct_hermitianPart_mulVec,
    RCLike.ofReal_pos]

omit [DecidableEq n] in
/-- If the Hermitian part of $A$ is positive definite, then $\operatorname{Re}(x^H A x) > 0$ for
every $x \ne 0$. This is the "positive definite" of [golub2013matrix] §4.2 for unsymmetric
matrices. -/
theorem re_dotProduct_mulVec_pos_of_posDef_hermitianPart {A : Matrix n n 𝕜}
    (hA : (hermitianPart A).PosDef) {x : n → 𝕜} (hx : x ≠ 0) :
    0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x)) := by
  have := hA.dotProduct_mulVec_pos hx
  rwa [star_dotProduct_hermitianPart_mulVec, RCLike.ofReal_pos] at this

/-- A square matrix whose Hermitian part is positive definite is nonsingular.

Over $\mathbb{R}$ this is `Matrix.isUnit_of_posDef_add_transpose`, where $P + P^T$ is twice the
Hermitian part of $P$. -/
theorem isUnit_of_posDef_hermitianPart {A : Matrix n n 𝕜}
    (hA : (hermitianPart A).PosDef) : IsUnit A := by
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  by_contra hne
  have h := re_dotProduct_mulVec_pos_of_posDef_hermitianPart hA (sub_ne_zero.2 hne)
  rw [mulVec_sub, hxy, sub_self, dotProduct_zero, map_zero] at h
  exact lt_irrefl _ h

/-- A real square matrix $P$ with $P + P^T$ positive definite is nonsingular. This is the real case
of `Matrix.isUnit_of_posDef_hermitianPart`, since the Hermitian part of $P$ is $(P + P^T)/2$. -/
theorem isUnit_of_posDef_add_transpose {P : Matrix n n ℝ} (hP : (P + Pᵀ).PosDef) : IsUnit P :=
  isUnit_of_posDef_hermitianPart <| by
    rw [hermitianPart_eq_smul_add_transpose]
    exact hP.smul (by norm_num)

omit [Fintype n] [DecidableEq n] in
/-- The Hermitian part commutes with taking a principal submatrix: for $e : m \to n$, the Hermitian
part of $(a_{e(i) e(j)})$ is the submatrix of the Hermitian part of $A$ with rows and columns
$e$. -/
theorem hermitianPart_submatrix {m : Type*} (A : Matrix n n 𝕜) (e : m → n) :
    hermitianPart (A.submatrix e e) = (hermitianPart A).submatrix e e := by
  ext i j
  simp

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm of the Hermitian part is at most that of the matrix: $$\left\| \frac{A +
A^H}{2} \right\|_2 \le \frac{\|A\|_2 + \|A^H\|_2}{2} = \|A\|_2.$$ This is [golub2013matrix]
§4.2.2. -/
theorem l2_opNorm_hermitianPart_le (A : Matrix n n 𝕜) :
    ‖hermitianPart A‖ ≤ ‖A‖ := by
  rw [hermitianPart, norm_smul, norm_inv, RCLike.norm_ofNat]
  calc 2⁻¹ * ‖A + Aᴴ‖ ≤ 2⁻¹ * (‖A‖ + ‖Aᴴ‖) := by gcongr; exact norm_add_le _ _
    _ = ‖A‖ := by rw [l2_opNorm_conjTranspose]; ring

end Matrix
