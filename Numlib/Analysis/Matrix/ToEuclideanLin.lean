/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv

/-!
# Matrices as operators on Euclidean space

A matrix $A \in \mathbb{K}^{m \times n}$, $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, acts as a
linear operator $x \mapsto A x$ from the Euclidean space $\mathbb{K}^n$ to $\mathbb{K}^m$; in Lean
this operator is `Matrix.toEuclideanLin A`. This file collects the facts that move a statement
between the matrix and the operator. Matrix multiplication is composition, powers and polynomials of
a square matrix are those of its operator, and the conjugate transpose is the adjoint: $\langle A^H
y, x \rangle = \langle y, A x \rangle$. The eigenvalues of a square matrix are those of its
operator, and the algebraic multiplicity of an eigenvalue is the dimension of the generalized
eigenspace. The spectral norm of a square matrix is the operator norm of its operator.

The file also treats matrices with orthonormal columns. The range of a matrix is the span of its
columns, $Q^H Q = I$ holds if and only if the columns of $Q$ are orthonormal, and such a $Q$ acts as
a linear isometry. A unitary matrix preserves the Euclidean norm and inner product, and the two
column blocks of a unitary matrix span orthogonal complements. Further sections treat the inverse of
a matrix, the shift $A + r I$, the rank-one matrix $u v^T$, and real matrices as operators on
$\mathbb{C}^n$.

## Main definitions

* `Matrix.unitaryLinearIsometryEquiv`: a unitary matrix $U$ as a linear isometry equivalence of
  $\mathbb{K}^n$.
* `Matrix.toEuclideanLinearIsometry`: a matrix $V$ with $V^H V = I$ as a linear isometry.
* `Matrix.toEuclideanLinearIsometryEquiv`: a matrix $V$ with $V^H V = I$ and $V V^H = I$ as a linear
  isometry equivalence.
* `Matrix.toEuclideanComplex`: a real vector as a vector of $\mathbb{C}^n$.

## Main results

* `Matrix.toEuclideanLin_mul`: the operator of $A B$ is the composition of the operators of $A$ and
  $B$.
* `Matrix.toEuclideanLin_aeval`: the operator of $p(A)$ is $p$ of the operator of $A$, for a
  polynomial $p$.
* `Matrix.finrank_maxGenEigenspace_toEuclideanLin`: the algebraic multiplicity of an eigenvalue is
  the dimension of its generalized eigenspace.
* `Matrix.toEuclideanLin_conjTranspose_inner_left`: $\langle A^H y, x \rangle = \langle y, A x
  \rangle$.
* `Matrix.hasEigenvalue_toEuclideanLin_iff`: the eigenvalues of the operator are the points of the
  spectrum of the matrix.
* `Matrix.IsHermitian.isSymmetricBoundedBy_toEuclideanLin`: a Hermitian matrix whose eigenvalues lie
  in $[\lambda_{\min}, \lambda_{\max}]$ has its quadratic form between $\lambda_{\min} \|x\|^2$ and
  $\lambda_{\max} \|x\|^2$.
* `Matrix.range_toEuclideanLin_eq_span_col`: the range of a matrix is the span of its columns.
* `Matrix.conjTranspose_mul_self_eq_one_iff_orthonormal`: $Q^H Q = I$ if and only if the columns of
  $Q$ are orthonormal.
* `Matrix.range_eq_orthogonal_of_fromCols`: the two column blocks of a unitary matrix span
  orthogonal complements.
* `Matrix.l2_opNorm_eq_norm_toEuclideanLin`: the spectral norm of a square matrix is the operator
  norm of its operator.
* `Matrix.norm_toLp_mulVec_of_mem_unitaryGroup`: a unitary matrix preserves the Euclidean norm.
* `Matrix.range_mul_eq_map_of_mul_conjTranspose_eq_one`: a unitary $V$ maps the range of $M$
  isometrically onto the range of $V M$.
* `Matrix.toEuclideanCLM_nonsing_inv`: the operator of $A^{-1}$ is the inverse of the operator of an
  invertible $A$.
* `Matrix.toEuclideanCLM_add_smul_one`: the operator of $A + r I$ is the operator of $A$ plus $r$
  times the identity.
* `Matrix.PosDef.isSymmetricCoercive_toEuclideanCLM_complexify`: a real positive definite matrix
  acts on $\mathbb{C}^n$ as a symmetric coercive operator.

## Notation

* $\langle x, y \rangle$: the Euclidean inner product, conjugate-linear in the first argument, as in
  Mathlib.
* $A^H$: the conjugate transpose `Aᴴ`. Over $\mathbb{R}$ it is the transpose $A^T$.
* $\operatorname{ran} A$: the range `LinearMap.range (Matrix.toEuclideanLin A)`.

## Implementation notes

* A vector of $\mathbb{K}^n$ is a term of `EuclideanSpace 𝕜 n`, and `WithLp.toLp 2` and
  `WithLp.ofLp` pass between it and a function `n → 𝕜`. The identities `Matrix.ofLp_toEuclideanLin`
  and `Matrix.toEuclideanLin_toLp` hold by definition, and they are stated so that `rw` can pass
  between the operator and `Matrix.mulVec`.
* Everything that makes sense for a rectangular matrix is stated for one, with arbitrary finite
  index types.
* The equivalence of symmetric matrices and symmetric operators is Mathlib's
  `Matrix.isSymmetric_toEuclideanLin_iff`. Its direction for a real symmetric matrix is
  `Matrix.IsSymm.isSymmetric_toEuclideanLin`. The equivalence of positive definite matrices and
  symmetric coercive operators is `Matrix.posDef_iff_isSymmetricCoercive`. The reading of a Krylov
  subspace of `Matrix.toEuclideanLin A` as a span of columns is
  `Matrix.krylov_subspace_toEuclideanLin` in `Numlib.Krylov.ToEuclideanLin`, because this module
  cannot depend on the Krylov theory.
* Mathlib's matrix inverse $A^{-1}$ is $0$ for a singular $A$, and the operator algebra has the
  inverse `Ring.inverse`, which is also $0$ at a non-invertible element. The two agree under
  `Matrix.toEuclideanCLM` for an invertible $A$, and the results on inverses assume that $A$ is
  invertible.
* `Matrix.toEuclideanCLM_injective` states injectivity for the coercion that applications use,
  because `StarAlgEquiv.injective` is stated for the underlying ring equivalence and leaves a goal
  phrased in `toRingEquiv`.
-/

/-- The real inner product of two coordinate vectors $u, v \in \mathbb{R}^\iota$ is their dot
product: $\langle u, v \rangle = u \cdot v$.

This is Mathlib's `EuclideanSpace.inner_toLp_toLp` with the trivial conjugation removed and the
factors in this order. -/
theorem EuclideanSpace.inner_toLp_toLp_real {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ ι) (WithLp.toLp 2 v) = u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The identity matrix acts as the identity operator: the operator of
$I \in \mathbb{K}^{n \times n}$ is the identity of $\mathbb{K}^n$. -/
@[simp]
theorem toEuclideanLin_one : toEuclideanLin (1 : Matrix n n 𝕜) = LinearMap.id :=
  toLpLin_one 2

/-- Matrix multiplication is composition of operators. Let $A \in \mathbb{K}^{m \times n}$ and
$B \in \mathbb{K}^{n \times o}$. Then the operator of $A B$ is the operator of $A$ composed with
the operator of $B$.

On square matrices this makes `Matrix.toEuclideanLin` a morphism of algebras. -/
theorem toEuclideanLin_mul {m o : Type*} [Fintype o] [DecidableEq o] (A : Matrix m n 𝕜)
    (B : Matrix n o 𝕜) : toEuclideanLin (A * B) = toEuclideanLin A ∘ₗ toEuclideanLin B :=
  toLpLin_mul_same 2 A B

/-- Let $A \in \mathbb{K}^{m \times n}$, $B \in \mathbb{K}^{n \times o}$ and $x \in \mathbb{K}^o$.
Then $(A B) x = A (B x)$, where each matrix acts as its operator.

This is the applied form of `Matrix.toEuclideanLin_mul`. -/
theorem toEuclideanLin_mul_apply {m o : Type*} [Fintype o] [DecidableEq o] (A : Matrix m n 𝕜)
    (B : Matrix n o 𝕜) (x : EuclideanSpace 𝕜 o) :
    toEuclideanLin (A * B) x = toEuclideanLin A (toEuclideanLin B x) := by
  rw [toEuclideanLin_mul, LinearMap.comp_apply]

/-- Powers of a matrix act as powers of its operator. Let $A \in \mathbb{K}^{n \times n}$ and let
$k$ be a natural number. Then the operator of $A^k$ is the $k$-th power of the operator of $A$.

This lets a Krylov subspace of a matrix be read as a Krylov subspace of
`Matrix.toEuclideanLin A`. -/
theorem toEuclideanLin_pow (A : Matrix n n 𝕜) (k : ℕ) :
    toEuclideanLin (A ^ k) = toEuclideanLin A ^ k :=
  toLpLin_pow 2 A k

/-- Let $A \in \mathbb{K}^{n \times n}$ and let $p$ be a polynomial over $\mathbb{K}$. Then the
operator of the matrix $p(A)$ is $p(T)$, where $T$ is the operator of $A$.

The polynomial evaluation is `Polynomial.aeval`. -/
theorem toEuclideanLin_aeval (A : Matrix n n 𝕜) (p : Polynomial 𝕜) :
    toEuclideanLin (Polynomial.aeval A p) = Polynomial.aeval (toEuclideanLin A) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def, map_smul, toEuclideanLin_pow]

/-- The algebraic multiplicity of an eigenvalue is the dimension of its generalized eigenspace. Let
$A \in \mathbb{K}^{n \times n}$ and $\mu \in \mathbb{K}$. Then the multiplicity of $\mu$ as a
root of the characteristic polynomial of $A$ is the dimension of the generalized eigenspace
$\bigcup_k \ker (T - \mu I)^k$ of the operator $T$ of $A$.

The generalized eigenspace is `Module.End.maxGenEigenspace`. The proof is Mathlib's
`LinearMap.finrank_maxGenEigenspace_eq`, read through `Matrix.charpoly_toLin`. -/
theorem finrank_maxGenEigenspace_toEuclideanLin (A : Matrix n n 𝕜) (μ : 𝕜) :
    Module.finrank 𝕜 (Module.End.maxGenEigenspace (toEuclideanLin A) μ) =
      A.charpoly.rootMultiplicity μ := by
  rw [LinearMap.finrank_maxGenEigenspace_eq, toEuclideanLin_eq_toLin_orthonormal, charpoly_toLin]

/-- The conjugate transpose moves across the inner product as the adjoint does. Let
$A \in \mathbb{K}^{m \times n}$, $x \in \mathbb{K}^n$ and $y \in \mathbb{K}^m$. Then
$$\langle A^H y, x \rangle = \langle y, A x \rangle.$$

The proof is `LinearMap.adjoint_inner_left`. -/
theorem toEuclideanLin_conjTranspose_inner_left {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    inner 𝕜 (toEuclideanLin Aᴴ y) x = inner 𝕜 y (toEuclideanLin A x) := by
  rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

/-- The conjugate transpose moves across the inner product as the adjoint does. Let
$A \in \mathbb{K}^{m \times n}$, $x \in \mathbb{K}^n$ and $y \in \mathbb{K}^m$. Then
$$\langle x, A^H y \rangle = \langle A x, y \rangle.$$

The proof is `LinearMap.adjoint_inner_right`. -/
theorem toEuclideanLin_conjTranspose_inner_right {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    inner 𝕜 x (toEuclideanLin Aᴴ y) = inner 𝕜 (toEuclideanLin A x) y := by
  rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

/-- The quadratic form of a congruence. Let $A \in \mathbb{K}^{m \times m}$,
$X \in \mathbb{K}^{m \times n}$ and $y \in \mathbb{K}^n$. Then
$$\langle X^H A X y, y \rangle = \langle A (X y), X y \rangle.$$
-/
theorem inner_toEuclideanLin_conjTranspose_mul_mul_apply {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m 𝕜) (X : Matrix m n 𝕜) (y : EuclideanSpace 𝕜 n) :
    inner 𝕜 (toEuclideanLin (Xᴴ * A * X) y) y =
      inner 𝕜 (toEuclideanLin A (toEuclideanLin X y)) (toEuclideanLin X y) := by
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_left]

/-- Over a field with trivial conjugation, such as $\mathbb{R}$, the adjoint of the operator of
$A \in \mathbb{K}^{m \times n}$ is the operator of $A^T$.

This is `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` with $A^H = A^T$. -/
theorem toEuclideanLin_transpose_eq_adjoint [TrivialStar 𝕜] {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m n 𝕜) :
    toEuclideanLin Aᵀ = LinearMap.adjoint (toEuclideanLin A) := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_eq_adjoint]

/-- Over a field with trivial conjugation, for $A \in \mathbb{K}^{m \times n}$, $x \in \mathbb{K}^n$
and $y \in \mathbb{K}^m$, $\langle A^T y, x \rangle = \langle y, A x \rangle$. This is the real
form of `Matrix.toEuclideanLin_conjTranspose_inner_left`. -/
theorem toEuclideanLin_transpose_inner_left [TrivialStar 𝕜] {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    inner 𝕜 (toEuclideanLin Aᵀ y) x = inner 𝕜 y (toEuclideanLin A x) := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_inner_left]

/-- Over a field with trivial conjugation, for $A \in \mathbb{K}^{m \times n}$, $x \in \mathbb{K}^n$
and $y \in \mathbb{K}^m$, $\langle x, A^T y \rangle = \langle A x, y \rangle$. This is the real
form of `Matrix.toEuclideanLin_conjTranspose_inner_right`. -/
theorem toEuclideanLin_transpose_inner_right [TrivialStar 𝕜] {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    inner 𝕜 x (toEuclideanLin Aᵀ y) = inner 𝕜 (toEuclideanLin A x) y := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_inner_right]

/-- Let $\mathbb{K}$ have trivial conjugation, as $\mathbb{R}$ does, and let
$A \in \mathbb{K}^{n \times n}$ be symmetric, $A^T = A$. Then the operator of $A$ is symmetric:
$\langle A x, y \rangle = \langle x, A y \rangle$ for all $x, y$.

This is the direction of Mathlib's `Matrix.isSymmetric_toEuclideanLin_iff` that a real statement
needs, with the step from symmetric to Hermitian (`Matrix.isHermitian_iff_isSymm`) already
taken. -/
theorem IsSymm.isSymmetric_toEuclideanLin [TrivialStar 𝕜] {A : Matrix n n 𝕜} (hA : A.IsSymm) :
    (toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr (isHermitian_iff_isSymm.mpr hA)

/-- The eigenvalues of the operator are the eigenvalues of the matrix. Let
$A \in \mathbb{K}^{n \times n}$ and $\mu \in \mathbb{K}$. Then $\mu$ is an eigenvalue of the
operator of $A$ if and only if $\mu$ is in the spectrum of $A$. -/
theorem hasEigenvalue_toEuclideanLin_iff (A : Matrix n n 𝕜) (μ : 𝕜) :
    Module.End.HasEigenvalue (toEuclideanLin A) μ ↔ μ ∈ spectrum 𝕜 A := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, spectrum_toLpLin]

/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian and let $\mu \in \mathbb{K}$. Then $\mu$ is an
eigenvalue of the operator of $A$ if and only if $\mu = \lambda_i$ for some $i$, where
$(\lambda_i)$ are Mathlib's eigenvalues `Matrix.IsHermitian.eigenvalues` of $A$. -/
theorem IsHermitian.hasEigenvalue_toEuclideanLin_iff {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (μ : 𝕜) : Module.End.HasEigenvalue (toEuclideanLin A) μ ↔ ∃ i, (hA.eigenvalues i : 𝕜) = μ := by
  rw [Matrix.hasEigenvalue_toEuclideanLin_iff, hA.spectrum_eq_image_range]
  simp [eq_comm]

/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian, and let
$\lambda_{\min}, \lambda_{\max} \in \mathbb{R}$ be such that every eigenvalue of $A$ lies in
$[\lambda_{\min}, \lambda_{\max}]$. Then the operator of $A$ is symmetric and
$$\lambda_{\min} \|x\|^2 \le \operatorname{Re} \langle A x, x \rangle \le \lambda_{\max}
  \|x\|^2$$
for all $x \in \mathbb{K}^n$.

The conclusion is `LinearMap.IsSymmetricBoundedBy`, and the eigenvalues are
`Matrix.IsHermitian.eigenvalues`. -/
theorem IsHermitian.isSymmetricBoundedBy_toEuclideanLin {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (h : ∀ i, hA.eigenvalues i ∈ Set.Icc lmin lmax) :
    (toEuclideanLin A).IsSymmetricBoundedBy lmin lmax := by
  refine (LinearMap.IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue
    (isSymmetric_toEuclideanLin_iff.mpr hA) lmin lmax).mpr fun μ hμ => ?_
  obtain ⟨i, rfl⟩ := (hA.hasEigenvalue_toEuclideanLin_iff μ).mp hμ
  simpa using h i

section Coordinates

/-! ### Coordinates

`Matrix.toEuclideanLin A` is `Matrix.mulVec` transported along `WithLp.toLp 2` / `WithLp.ofLp`, for
a rectangular `A` as well as a square one. The identifications are definitional, and are stated so
that `rw` and `simp only` can pass between the operator picture and the coordinate one in either
direction. -/

variable {m : Type*}

/-- In coordinates, the operator of $A \in \mathbb{K}^{m \times n}$ is matrix-vector multiplication:
the coordinate vector of $A x$ is `A *ᵥ WithLp.ofLp x`. -/
theorem ofLp_toEuclideanLin (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    WithLp.ofLp (toEuclideanLin A x) = A *ᵥ WithLp.ofLp x := rfl

/-- In coordinates, the operator of $A \in \mathbb{K}^{m \times n}$ is matrix-vector multiplication:
the operator applied to the vector with coordinates $v$ is the vector with coordinates `A *ᵥ v`. -/
theorem toEuclideanLin_toLp (A : Matrix m n 𝕜) (v : n → 𝕜) :
    toEuclideanLin A (WithLp.toLp 2 v) = WithLp.toLp 2 (A *ᵥ v) := rfl

/-- The operator of $A \in \mathbb{K}^{m \times n}$ applied to $x$ is the vector with coordinates
`A *ᵥ WithLp.ofLp x`. -/
theorem toEuclideanLin_apply (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    toEuclideanLin A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

omit [Fintype n] [DecidableEq n] in
/-- Let $V \in \mathbb{K}^{n \times m}$ have columns $v_1, \dots, v_m$, and let
$y \in \mathbb{K}^m$. Then
$$V y = \sum_j y_j v_j.$$

This passes between a matrix-vector product $V y$ and the linear combination $\sum_j y_j v_j$ of
the columns of $V$. -/
theorem toEuclideanLin_apply_eq_sum [Fintype m] [DecidableEq m] (V : Matrix n m 𝕜) (y : m → 𝕜) :
    toEuclideanLin V (WithLp.toLp 2 y) =
      ∑ j, y j • (WithLp.toLp 2 (Vᵀ j) : EuclideanSpace 𝕜 n) := by
  ext i
  simp [toLpLin_apply, mulVec, dotProduct, mul_comm]

end Coordinates

/-- Let $A \in \mathbb{R}^{n \times n}$ and $x \in \mathbb{R}^n$. Then Mathlib's quadratic form
$x \cdot A x$ (`Matrix.toQuadraticForm'`) is $\operatorname{Re} \langle A x, x \rangle$ for the
operator of $A$. -/
theorem toQuadraticForm'_ofLp (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    Matrix.toQuadraticForm' A (WithLp.ofLp x) = RCLike.re (inner ℝ (toEuclideanLin A x) x) := by
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply, toLinearMap₂'_apply',
    RCLike.re_to_real, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin, star_trivial]

section Columns

/-! ### Ranges and orthonormality of columns -/

variable {m : Type*}

omit [Fintype n] [DecidableEq n] in
/-- The range of a matrix $M \in \mathbb{K}^{n \times m}$ is the span of its columns. -/
theorem range_toEuclideanLin_eq_span_col [Fintype m] [DecidableEq m] (M : Matrix n m 𝕜) :
    LinearMap.range (toEuclideanLin M) =
      Submodule.span 𝕜 (Set.range fun j => WithLp.toLp 2 (M.col j)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx := toEuclideanLin_apply_eq_sum M (WithLp.ofLp x)
    simp only [WithLp.toLp_ofLp] at hx
    rw [hx]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨WithLp.toLp 2 (Pi.single j 1), by rw [toEuclideanLin_toLp, mulVec_single_one]⟩

omit [Fintype n] [DecidableEq n] in
/-- Let $m$ be nonempty and let $x \in \mathbb{K}^n$. The range of the matrix whose columns all
equal $x$ is the line $\mathbb{K} x$.

The matrix is `Matrix.replicateCol m x`. -/
theorem range_toEuclideanLin_replicateCol [Fintype m] [DecidableEq m] [Nonempty m] (x : n → 𝕜) :
    LinearMap.range (toEuclideanLin (replicateCol m x)) = 𝕜 ∙ WithLp.toLp 2 x := by
  rw [range_toEuclideanLin_eq_span_col]
  have h : (fun j : m => WithLp.toLp 2 ((replicateCol m x).col j)) = fun _ => WithLp.toLp 2 x :=
    rfl
  rw [h, Set.range_const]

omit [DecidableEq n] in
/-- Let $Q \in \mathbb{K}^{n \times m}$. Then $Q^H Q = I$ if and only if the columns of $Q$ are
orthonormal in $\mathbb{K}^n$. -/
theorem conjTranspose_mul_self_eq_one_iff_orthonormal [DecidableEq m] {Q : Matrix n m 𝕜} :
    Qᴴ * Q = 1 ↔ Orthonormal 𝕜 fun j => WithLp.toLp 2 (Q.col j) := by
  rw [orthonormal_iff_ite, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.one_apply, Matrix.mul_apply]
  rfl

omit [DecidableEq n] in
/-- Let $Q \in \mathbb{K}^{n \times m}$ and $r \in \mathbb{K}^n$. Then $Q^H r = 0$ if and only if
$r$ is orthogonal to every column of $Q$. -/
theorem conjTranspose_mulVec_eq_zero_iff {Q : Matrix n m 𝕜} {r : n → 𝕜} :
    Qᴴ *ᵥ r = 0 ↔ ∀ j, inner 𝕜 (WithLp.toLp 2 (Q.col j)) (WithLp.toLp 2 r) = 0 := by
  rw [funext_iff]
  refine forall_congr' fun j => ?_
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rfl

/-- The two column blocks of a unitary matrix span orthogonal complements. Let
$Q_\alpha \in \mathbb{K}^{n \times r}$ and $Q_\beta \in \mathbb{K}^{n \times s}$, and suppose
that $Q = [Q_\alpha \; Q_\beta]$ satisfies $Q^H Q = I$ and $Q Q^H = I$. Then
$$\operatorname{ran} Q_\beta = (\operatorname{ran} Q_\alpha)^\perp.$$
-/
theorem range_eq_orthogonal_of_fromCols {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s]
    [DecidableEq s] {Qα : Matrix n r 𝕜} {Qβ : Matrix n s 𝕜}
    (hQ : (fromCols Qα Qβ)ᴴ * fromCols Qα Qβ = 1)
    (hQ' : fromCols Qα Qβ * (fromCols Qα Qβ)ᴴ = 1) :
    LinearMap.range (toEuclideanLin Qβ) = (LinearMap.range (toEuclideanLin Qα))ᗮ := by
  have hαβ : Qαᴴ * Qβ = 0 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
      ← fromBlocks_one] at hQ
    exact (fromBlocks_inj.1 hQ).2.1
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows] at hQ'
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨z, rfl⟩
    rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← toEuclideanLin_mul_apply, hαβ, map_zero, LinearMap.zero_apply, inner_zero_right]
  · intro x hx
    have h0 : toEuclideanLin Qαᴴ x = 0 := by
      rw [toEuclideanLin_conjTranspose_eq_adjoint]
      refine ext_inner_left 𝕜 fun z => ?_
      rw [LinearMap.adjoint_inner_right, inner_zero_right]
      exact (Submodule.mem_orthogonal _ _).1 hx _ ⟨z, rfl⟩
    refine ⟨toEuclideanLin Qβᴴ x, ?_⟩
    have h := congrArg (fun M => toEuclideanLin M x) hQ'
    simp only [map_add, LinearMap.add_apply, toEuclideanLin_mul_apply, h0, map_zero, zero_add,
      toLpLin_one, LinearMap.id_apply] at h
    exact h

/-- Complementary column selections of a unitary matrix span orthogonal complements. Let
$V \in \mathbb{K}^{n \times n}$ be unitary, and let $f : r \to n$ and $g : s \to n$ be such that
the map on $r \sqcup s$ given by $f$ and $g$ is a bijection onto the column indices. Then
$$\operatorname{ran} V(:, g) = (\operatorname{ran} V(:, f))^\perp,$$
where the $i$-th column of $V(:, f)$ is the column $f(i)$ of $V$.

This is [golub2013matrix], §2.1.5, after Theorem 2.1.1. The column selection $V(:, f)$ is
`V.submatrix id f`, and the bijection is `Sum.elim f g`. The two selections side by side are $V$
with its columns permuted, so the result follows from `Matrix.range_eq_orthogonal_of_fromCols`. -/
theorem range_submatrix_eq_orthogonal {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s]
    [DecidableEq s] {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) {f : r → n} {g : s → n}
    (hfg : Function.Bijective (Sum.elim f g)) :
    LinearMap.range (toEuclideanLin (V.submatrix id g))
      = (LinearMap.range (toEuclideanLin (V.submatrix id f)))ᗮ := by
  have hW : fromCols (V.submatrix id f) (V.submatrix id g)
      = V.submatrix id (Equiv.ofBijective _ hfg) := by
    ext i (j | j) <;> rfl
  refine range_eq_orthogonal_of_fromCols ?_ ?_ <;> rw [hW]
  · rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hV, submatrix_one_equiv]
  · rw [conjTranspose_submatrix, submatrix_mul_equiv, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff.1 hV, submatrix_id_id]

end Columns

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm of $A \in \mathbb{K}^{n \times n}$ is the operator norm of its operator on
$\mathbb{K}^n$.

The spectral norm is the norm of the scoped instance `Matrix.Norms.L2Operator`. -/
theorem l2_opNorm_eq_norm_toEuclideanLin (A : Matrix n n 𝕜) :
    ‖A‖ = ‖LinearMap.toContinuousLinearMap (toEuclideanLin A)‖ :=
  l2_opNorm_def A

section Unitary

variable {U : Matrix n n 𝕜}

/-- A unitary matrix $U \in \mathbb{K}^{n \times n}$ gives a unitary element
`Matrix.toEuclideanCLM U` of the algebra of continuous linear operators on $\mathbb{K}^n$. -/
theorem toEuclideanCLM_mem_unitary (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) U ∈
      unitary (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) :=
  Unitary.map_mem _ hU

/-- A unitary matrix $U \in \mathbb{K}^{n \times n}$ is an isometry: $\|U x\| = \|x\|$ for all
$x \in \mathbb{K}^n$, with $U$ acting through `Matrix.toEuclideanCLM`. -/
theorem norm_toEuclideanCLM_apply_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (x : EuclideanSpace 𝕜 n) : ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) U x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (toEuclideanCLM_mem_unitary hU) x

/-- A unitary matrix preserves the Euclidean norm. Let $U \in \mathbb{K}^{n \times n}$ be unitary
and let $v \in \mathbb{K}^n$. Then
$$\|U v\|_2 = \|v\|_2.$$

The proof transports $U$ along the star algebra equivalence `Matrix.toEuclideanCLM` and uses
that a unitary continuous linear operator on a Hilbert space preserves the norm
(`ContinuousLinearMap.norm_map_of_mem_unitary`). -/
theorem norm_toLp_mulVec_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup n 𝕜) (v : n → 𝕜) :
    ‖(WithLp.toLp 2 (U *ᵥ v) : EuclideanSpace 𝕜 n)‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 n)‖ := by
  rw [← toEuclideanCLM_toLp U v]
  exact norm_toEuclideanCLM_apply_of_mem_unitaryGroup hU _

/-- A unitary matrix preserves the Euclidean inner product. Let $U \in \mathbb{K}^{n \times n}$ be
unitary and let $v, w \in \mathbb{K}^n$. Then
$$\langle U v, U w \rangle = \langle v, w \rangle.$$
-/
theorem inner_toLp_mulVec_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup n 𝕜) (v w : n → 𝕜) :
    inner 𝕜 (WithLp.toLp 2 (U *ᵥ v) : EuclideanSpace 𝕜 n)
        (WithLp.toLp 2 (U *ᵥ w) : EuclideanSpace 𝕜 n) =
      inner 𝕜 (WithLp.toLp 2 v : EuclideanSpace 𝕜 n) (WithLp.toLp 2 w : EuclideanSpace 𝕜 n) := by
  rw [← toEuclideanCLM_toLp U v, ← toEuclideanCLM_toLp U w]
  exact ContinuousLinearMap.inner_map_map_of_mem_unitary (toEuclideanCLM_mem_unitary hU) _ _

/-- A unitary matrix acts as an isometry. Let $U \in \mathbb{K}^{n \times n}$ be unitary. Then
$\|U x\| = \|x\|$ for all $x \in \mathbb{K}^n$, with $U$ acting through `Matrix.toEuclideanLin`. -/
theorem norm_toEuclideanLin_apply_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (x : EuclideanSpace 𝕜 n) : ‖toEuclideanLin U x‖ = ‖x‖ := by
  rw [toEuclideanLin_apply, norm_toLp_mulVec_of_mem_unitaryGroup hU]

/-- A unitary matrix $U \in \mathbb{K}^{n \times n}$ is invertible. Its inverse is $U^H$. -/
theorem isUnit_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup n 𝕜) : IsUnit U :=
  ⟨⟨U, star U, mem_unitaryGroup_iff.mp hU, mem_unitaryGroup_iff'.mp hU⟩, rfl⟩

/-- A unitary similarity does not change the spectrum. Let $U \in \mathbb{K}^{n \times n}$ be
unitary and let $A \in \mathbb{K}^{n \times n}$. Then $U^H A U$ and $A$ have the same spectrum. -/
theorem spectrum_conjTranspose_mul_mul {A : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    spectrum 𝕜 (Uᴴ * A * U) = spectrum 𝕜 A := by
  have hu : IsUnit U := isUnit_of_mem_unitaryGroup hU
  have hinv : U⁻¹ = Uᴴ :=
    inv_eq_left_inv (conjTranspose_mul_self_of_mem_unitaryGroup hU)
  have h := spectrum.units_conjugate' (R := 𝕜) (a := A) (u := hu.unit)
  rwa [coe_units_inv, IsUnit.unit_spec, hinv] at h

/-- A unitary matrix $U \in \mathbb{K}^{n \times n}$ as a linear isometry equivalence of
$\mathbb{K}^n$. It acts as $U$, and its inverse acts as $U^H$.

The two actions are `Matrix.unitaryLinearIsometryEquiv_apply` and
`Matrix.unitaryLinearIsometryEquiv_symm_apply`. -/
noncomputable def unitaryLinearIsometryEquiv (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    EuclideanSpace 𝕜 n ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 n :=
  Unitary.linearIsometryEquiv ⟨toEuclideanCLM (n := n) (𝕜 := 𝕜) U, toEuclideanCLM_mem_unitary hU⟩

/-- The isometry `Matrix.unitaryLinearIsometryEquiv` of a unitary matrix $U$ acts as $U$: it sends
$x$ to $U x$. -/
theorem unitaryLinearIsometryEquiv_apply (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (x : EuclideanSpace 𝕜 n) : unitaryLinearIsometryEquiv hU x = toEuclideanLin U x := rfl

/-- The inverse of the isometry `Matrix.unitaryLinearIsometryEquiv` of a unitary matrix $U$ acts as
$U^H$: it sends $x$ to $U^H x$. -/
theorem unitaryLinearIsometryEquiv_symm_apply (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (x : EuclideanSpace 𝕜 n) : (unitaryLinearIsometryEquiv hU).symm x = toEuclideanLin Uᴴ x := by
  change (star (toEuclideanCLM (n := n) (𝕜 := 𝕜) U)) x = _
  rw [← map_star, star_eq_conjTranspose]
  rfl

end Unitary

section Isometry

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A matrix $V \in \mathbb{K}^{n \times m}$ with orthonormal columns, $V^H V = I$, as a linear
isometry from $\mathbb{K}^m$ to $\mathbb{K}^n$. It acts as $V$. -/
noncomputable def toEuclideanLinearIsometry {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1) :
    EuclideanSpace 𝕜 m →ₗᵢ[𝕜] EuclideanSpace 𝕜 n where
  toLinearMap := toEuclideanLin V
  norm_map' y := by
    have h : inner 𝕜 (toEuclideanLin V y) (toEuclideanLin V y) = inner 𝕜 y y := by
      rw [← toEuclideanLin_conjTranspose_inner_left, ← Matrix.toEuclideanLin_mul_apply, hV,
        toEuclideanLin_one, LinearMap.id_apply]
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← inner_self_eq_norm_sq (𝕜 := 𝕜),
      ← inner_self_eq_norm_sq (𝕜 := 𝕜), h]

/-- The isometry `Matrix.toEuclideanLinearIsometry` of a matrix $V$ with $V^H V = I$ acts as $V$: it
sends $y$ to $V y$. -/
@[simp]
theorem toEuclideanLinearIsometry_apply {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1)
    (y : EuclideanSpace 𝕜 m) : toEuclideanLinearIsometry hV y = toEuclideanLin V y := rfl

/-- A matrix $V \in \mathbb{K}^{n \times m}$ with $V^H V = I$ and $V V^H = I$, as a linear isometry
equivalence from $\mathbb{K}^m$ onto $\mathbb{K}^n$. It acts as $V$.

Such a $V$ is a unitary matrix whose rows and columns are indexed by different types. -/
noncomputable def toEuclideanLinearIsometryEquiv {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1)
    (hV' : V * Vᴴ = 1) : EuclideanSpace 𝕜 m ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 n :=
  LinearIsometryEquiv.ofSurjective (toEuclideanLinearIsometry hV) fun y =>
    ⟨toEuclideanLin Vᴴ y, by
      rw [toEuclideanLinearIsometry_apply, ← toEuclideanLin_mul_apply, hV', toEuclideanLin_one,
        LinearMap.id_apply]⟩

/-- The isometry equivalence `Matrix.toEuclideanLinearIsometryEquiv` of a matrix $V$ with
$V^H V = I$ and $V V^H = I$ acts as $V$: it sends $y$ to $V y$. -/
@[simp]
theorem toEuclideanLinearIsometryEquiv_apply {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1)
    (hV' : V * Vᴴ = 1) (y : EuclideanSpace 𝕜 m) :
    toEuclideanLinearIsometryEquiv hV hV' y = toEuclideanLin V y := rfl

/-- Column spaces under a unitary change of coordinates. Let $V \in \mathbb{K}^{n \times m}$ satisfy
$V^H V = I$ and $V V^H = I$, and let $M \in \mathbb{K}^{m \times k}$. Then
$\operatorname{ran}(V M)$ is the image of $\operatorname{ran} M$ under the isometry equivalence
of $V$.

Therefore the metric quantities of column spaces, such as gaps, angles and distances, do not
change under $M \mapsto V M$. The isometry equivalence is
`Matrix.toEuclideanLinearIsometryEquiv`. -/
theorem range_mul_eq_map_of_mul_conjTranspose_eq_one {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1)
    (hV' : V * Vᴴ = 1) {k : Type*} [Fintype k] [DecidableEq k] (M : Matrix m k 𝕜) :
    LinearMap.range (toEuclideanLin (V * M)) =
      (LinearMap.range (toEuclideanLin M)).map
        ((toEuclideanLinearIsometryEquiv hV hV').toLinearEquiv :
          EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 n) := by
  rw [toEuclideanLin_mul, LinearMap.range_comp]
  rfl

omit [DecidableEq n] in
/-- Let $V \in \mathbb{K}^{n \times m}$ satisfy $V^H V = I$. Then $\operatorname{ran} V$ has
dimension $m$, the number of columns. -/
theorem finrank_range_of_conjTranspose_mul_self_eq_one {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1) :
    Module.finrank 𝕜 (LinearMap.range (toEuclideanLin V)) = Fintype.card m := by
  classical
  rw [LinearMap.finrank_range_of_inj (f := toEuclideanLin V)
    (toEuclideanLinearIsometry hV).injective, finrank_euclideanSpace]

end Isometry

section Applied

/-! ### The applied forms of the linear-equivalence laws

`Matrix.toEuclideanLin` is a linear equivalence, so `map_zero`, `map_neg`, `map_sub` and `map_smul`
apply to it; each of the lemmas below is one of those followed by the pointwise definition of the
corresponding operation on linear maps, in the form in which a proof about a vector wants it. -/

variable {m : Type*}

/-- The zero matrix of size $m \times n$ sends every vector $v \in \mathbb{K}^n$ to $0$. -/
theorem toEuclideanLin_zero_apply (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (0 : Matrix m n 𝕜) v = 0 := by
  rw [map_zero]; rfl

/-- Let $A \in \mathbb{K}^{m \times n}$ and $v \in \mathbb{K}^n$. Then $(-A) v = -(A v)$. -/
theorem toEuclideanLin_neg_apply (A : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (-A) v = -toEuclideanLin A v := by
  rw [map_neg]; rfl

/-- Let $A, B \in \mathbb{K}^{m \times n}$ and $v \in \mathbb{K}^n$. Then $(A - B) v = A v - B v$.
-/
theorem toEuclideanLin_sub_apply (A B : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (A - B) v = toEuclideanLin A v - toEuclideanLin B v := by
  rw [map_sub]; rfl

/-- Let $r \in \mathbb{K}$, $A \in \mathbb{K}^{m \times n}$ and $v \in \mathbb{K}^n$. Then
$(r A) v = r (A v)$. -/
theorem toEuclideanLin_smul_apply (r : 𝕜) (A : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (r • A) v = r • toEuclideanLin A v := by
  rw [map_smul]; rfl

end Applied

/-- The identity matrix fixes every vector: $I v = v$ for $v \in \mathbb{K}^n$. This is the applied
form of `Matrix.toEuclideanLin_one`. -/
theorem toEuclideanLin_one_apply (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (1 : Matrix n n 𝕜) v = v := by
  rw [toEuclideanLin_one]; rfl

/-- Two matrices $A, B \in \mathbb{K}^{n \times n}$ that act as the same continuous linear operator
on $\mathbb{K}^n$ are equal: `Matrix.toEuclideanCLM` is injective.

This is the injectivity of a star algebra equivalence, stated for the coercion that applications
use. `StarAlgEquiv.injective` is stated for the underlying ring equivalence instead, and a goal
closed by it is phrased in `toRingEquiv`. -/
theorem toEuclideanCLM_injective :
    Function.Injective (toEuclideanCLM (n := n) (𝕜 := 𝕜)) :=
  EmbeddingLike.injective' _

section Inverse

/-! ### Inversion

Mathlib's `Matrix.inv` is a junk-valued inverse, defined for every square matrix and equal to `0`
on a singular one, whereas the operator algebra `EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n` has
the junk-valued `Ring.inverse` of a monoid. The two agree under `Matrix.toEuclideanCLM` on
invertible matrices, which is all that is ever needed; on singular ones both sides are `0` for
`Matrix.inv` and `Ring.inverse` alike, but the operator side does not know that its argument came
from a matrix, so the hypothesis stays. -/

/-- Let $A \in \mathbb{K}^{n \times n}$ be invertible. Then the operator of `Ring.inverse A` is
`Ring.inverse` of the operator of $A$, which is its inverse operator.

A star algebra equivalence carries `Ring.inverse` to `Ring.inverse`, and the operator is
`Matrix.toEuclideanCLM A`. -/
theorem toEuclideanCLM_ringInverse {A : Matrix n n 𝕜} (hA : IsUnit A) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (Ring.inverse A)
      = Ring.inverse (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := by
  have hu : IsUnit (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := hA.map _
  refine hu.mul_left_cancel ?_
  rw [← map_mul, Ring.mul_inverse_cancel _ hA, map_one, Ring.mul_inverse_cancel _ hu]

/-- The operator of the inverse is the inverse operator. Let $A \in \mathbb{K}^{n \times n}$ be
invertible. Then the operator of $A^{-1}$ is the inverse of the operator of $A$.

On the left, $A^{-1}$ is Mathlib's matrix inverse, which is $0$ for a singular matrix. On the
right, the inverse is `Ring.inverse` in the algebra of continuous linear operators. The
operators are `Matrix.toEuclideanCLM`. -/
theorem toEuclideanCLM_nonsing_inv {A : Matrix n n 𝕜} (hA : IsUnit A) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) A⁻¹
      = Ring.inverse (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := by
  rw [nonsing_inv_eq_ringInverse, toEuclideanCLM_ringInverse hA]

/-- Let $M \in \mathbb{K}^{n \times n}$ be invertible. Then the operator of $M$ is invertible, and
its inverse `Ring.inverse` is the operator of $M^{-1}$.

This is the form of `Matrix.toEuclideanCLM_nonsing_inv` for linear maps, with the operators
`Matrix.toEuclideanLin`. -/
theorem ringInverse_toEuclideanLin {M : Matrix n n 𝕜} (hM : IsUnit M) :
    IsUnit (toEuclideanLin M) ∧ Ring.inverse (toEuclideanLin M) = toEuclideanLin M⁻¹ := by
  have hdet := (isUnit_iff_isUnit_det M).mp hM
  let u : (Module.End 𝕜 (EuclideanSpace 𝕜 n))ˣ :=
    ⟨toEuclideanLin M, toEuclideanLin M⁻¹,
      by rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, mul_nonsing_inv M hdet,
        toEuclideanLin_one, Module.End.one_eq_id],
      by rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, nonsing_inv_mul M hdet,
        toEuclideanLin_one, Module.End.one_eq_id]⟩
  exact ⟨⟨u, rfl⟩, Ring.inverse_unit u⟩

/-- Let $A \in \mathbb{K}^{n \times n}$ be invertible and let $z \in \mathbb{K}^n$. Then
$A (A^{-1} z) = z$.

This is the applied form of `Matrix.mul_nonsing_inv`. -/
theorem toEuclideanLin_mul_nonsing_inv_apply {A : Matrix n n 𝕜} (hA : IsUnit A)
    (z : EuclideanSpace 𝕜 n) : toEuclideanLin A (toEuclideanLin A⁻¹ z) = z := by
  rw [← toEuclideanLin_mul_apply, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA),
    toEuclideanLin_one_apply]

/-- Let $A \in \mathbb{K}^{n \times n}$ be invertible and let $z \in \mathbb{K}^n$. Then
$A^{-1} (A z) = z$.

This is the applied form of `Matrix.nonsing_inv_mul`. -/
theorem toEuclideanLin_nonsing_inv_mul_apply {A : Matrix n n 𝕜} (hA : IsUnit A)
    (z : EuclideanSpace 𝕜 n) : toEuclideanLin A⁻¹ (toEuclideanLin A z) = z := by
  rw [← toEuclideanLin_mul_apply, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA),
    toEuclideanLin_one_apply]

/-- An invertible matrix $S \in \mathbb{K}^{n \times n}$ acts surjectively: its range is
$\mathbb{K}^n$. -/
theorem range_toEuclideanLin_eq_top_of_isUnit {S : Matrix n n 𝕜} (hS : IsUnit S) :
    LinearMap.range (toEuclideanLin S) = ⊤ :=
  LinearMap.range_eq_top.2 fun z => ⟨_, toEuclideanLin_mul_nonsing_inv_apply hS z⟩

end Inverse

section Shift

/-!
### Shifts by a multiple of the identity

The shift $A + r I$ is the form of a resolvent, of a regularized system and of the half-steps of an
alternating-direction iteration. Its image under `Matrix.toEuclideanCLM` is the corresponding shift
of the operator.
-/

/-- Let $A \in \mathbb{K}^{n \times n}$ and $r \in \mathbb{K}$. Then the operator of $A + r I$ is
$T + r \cdot 1$, where $T$ is the operator of $A$.

The operators are `Matrix.toEuclideanCLM`. -/
theorem toEuclideanCLM_add_smul_one (A : Matrix n n 𝕜) (r : 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (A + r • 1)
      = toEuclideanCLM (n := n) (𝕜 := 𝕜) A + r • 1 := by
  rw [map_add, map_smul, map_one]

/-- Let $A \in \mathbb{K}^{n \times n}$ and $r \in \mathbb{K}$. Then the operator of $A - r I$ is
$T - r \cdot 1$, where $T$ is the operator of $A$.

The operators are `Matrix.toEuclideanCLM`. -/
theorem toEuclideanCLM_sub_smul_one (A : Matrix n n 𝕜) (r : 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (A - r • 1)
      = toEuclideanCLM (n := n) (𝕜 := 𝕜) A - r • 1 := by
  rw [map_sub, map_smul, map_one]

/-- Let $A \in \mathbb{K}^{n \times n}$ and $r \in \mathbb{K}$ be such that $A + r I$ is invertible.
Then the shifted operator $T + r \cdot 1$ is invertible, where $T$ is the operator of $A$.

The operator is `Matrix.toEuclideanCLM A`. -/
theorem isUnit_toEuclideanCLM_add_smul_one {A : Matrix n n 𝕜} {r : 𝕜}
    (hA : IsUnit (A + r • (1 : Matrix n n 𝕜))) :
    IsUnit (toEuclideanCLM (n := n) (𝕜 := 𝕜) A + r • 1) := by
  have h := hA.map (toEuclideanCLM (n := n) (𝕜 := 𝕜))
  rwa [toEuclideanCLM_add_smul_one] at h

end Shift

section RankOne

open WithLp

/-- Let $u, v \in \mathbb{R}^n$. Then the outer product $u v^T$ acts on $\mathbb{R}^n$ as the
rank-one operator $w \mapsto \langle v, w \rangle u$.

The outer product is `Matrix.vecMulVec u v`, and the rank-one operator is
`InnerProductSpace.rankOne`. -/
theorem toEuclideanCLM_vecMulVec (u v : n → ℝ) :
    toEuclideanCLM (𝕜 := ℝ) (vecMulVec u v)
      = InnerProductSpace.rankOne ℝ (toLp 2 u) (toLp 2 v) := by
  ext w i
  simp [ofLp_toEuclideanCLM, InnerProductSpace.rankOne_apply,
    EuclideanSpace.inner_eq_star_dotProduct, vecMulVec_mulVec, dotProduct_comm, mul_comm]

end RankOne

section Complexify

/-! ### Real matrices as operators on `EuclideanSpace ℂ n`

A real matrix reaches the complex Hilbert-space theory (self-adjointness, coercivity, the
spectral radius) through `Matrix.complexify` and `Matrix.toEuclideanCLM`; a real vector is read in
`EuclideanSpace ℂ n` through `Matrix.toEuclideanComplex`. -/

/-- A real vector $e \in \mathbb{R}^n$ as the vector of $\mathbb{C}^n$ with the same coordinates. -/
def toEuclideanComplex (e : n → ℝ) : EuclideanSpace ℂ n := WithLp.toLp 2 fun i => (e i : ℂ)

omit [Fintype n] [DecidableEq n] in
/-- A real vector $e$ is zero if and only if its image in $\mathbb{C}^n$ under
`Matrix.toEuclideanComplex` is zero. -/
theorem toEuclideanComplex_eq_zero_iff {e : n → ℝ} : toEuclideanComplex e = 0 ↔ e = 0 := by
  constructor
  · intro h
    ext i
    have := congrFun (congrArg WithLp.ofLp h) i
    simpa [toEuclideanComplex] using this
  · rintro rfl
    ext i
    simp [toEuclideanComplex]

/-- Let $A \in \mathbb{R}^{n \times n}$ and $e \in \mathbb{R}^n$. Then the operator of $A$, viewed
as a complex matrix, sends the image of $e$ in $\mathbb{C}^n$ to the image of $A e$.

The complex matrix is `Matrix.complexify A`, its operator is `Matrix.toEuclideanCLM`, and the
image of a real vector is `Matrix.toEuclideanComplex`. -/
theorem toEuclideanCLM_complexify_toEuclideanComplex (A : Matrix n n ℝ) (e : n → ℝ) :
    toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) (toEuclideanComplex e)
      = toEuclideanComplex (A *ᵥ e) := by
  rw [toEuclideanComplex, toEuclideanCLM_toLp, complexify_mulVec_ofReal]
  rfl

/-- Let $A \in \mathbb{R}^{n \times n}$ and $e \in \mathbb{R}^n$. Then the quadratic form of $A$
viewed as a complex matrix, at the image of $e$ in $\mathbb{C}^n$, has real part
$(A e) \cdot e$.

The complex matrix is `Matrix.complexify A`, and the image of a real vector is
`Matrix.toEuclideanComplex`. -/
theorem re_inner_toEuclideanCLM_complexify_toEuclideanComplex (A : Matrix n n ℝ) (e : n → ℝ) :
    RCLike.re (inner ℂ (toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) (toEuclideanComplex e))
      (toEuclideanComplex e)) = (A *ᵥ e) ⬝ᵥ e := by
  rw [toEuclideanCLM_complexify_toEuclideanComplex, toEuclideanComplex, toEuclideanComplex,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

/-- Let $X \in \mathbb{R}^{n \times n}$ be symmetric. Then $X$, viewed as a complex matrix, acts on
$\mathbb{C}^n$ as a symmetric operator.

The complex matrix is `Matrix.complexify X`, and its operator is `Matrix.toEuclideanCLM`. -/
theorem IsHermitian.isSymmetric_toEuclideanCLM_complexify {X : Matrix n n ℝ}
    (hX : X.IsHermitian) :
    ((toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify X) :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin]
  exact isSymmetric_toEuclideanLin_iff.mpr ((isHermitian_complexify_iff X).mpr hX)

/-- Let $X \in \mathbb{R}^{n \times n}$ be positive definite. Then $X$, viewed as a complex matrix,
acts on $\mathbb{C}^n$ as a symmetric coercive operator: it is symmetric and $\operatorname{Re}
\langle X z, z \rangle \ge c \|z\|^2$ for some $c > 0$ and all $z$.

The complex matrix is `Matrix.complexify X`, its operator is `Matrix.toEuclideanCLM`, and the
conclusion is `LinearMap.IsSymmetricCoercive`. -/
theorem PosDef.isSymmetricCoercive_toEuclideanCLM_complexify {X : Matrix n n ℝ}
    (hX : X.PosDef) :
    ((toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify X) :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetricCoercive := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin]
  exact (posDef_iff_isSymmetricCoercive _).mp (posDef_complexify_iff.mpr hX)

/-- Let $A \in \mathbb{R}^{n \times n}$. Then the real spectrum of the operator of $A$ on
$\mathbb{C}^n$ is the real spectrum of $A$: a real number $\lambda$ is in one if and only if it
is in the other.

The operator is `Matrix.toEuclideanCLM (Matrix.complexify A)`, and the real spectrum is
`spectrum ℝ`. -/
theorem spectrum_real_toEuclideanCLM_complexify (A : Matrix n n ℝ) :
    spectrum ℝ (toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A)) = spectrum ℝ A := by
  ext t
  rw [← spectrum.algebraMap_mem_iff ℂ, AlgEquiv.spectrum_eq (toEuclideanCLM (n := n) (𝕜 := ℂ)),
    Complex.coe_algebraMap, ofReal_mem_spectrum_complexify_iff]

end Complexify

end Matrix
