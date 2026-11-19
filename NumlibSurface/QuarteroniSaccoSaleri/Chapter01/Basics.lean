/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Swap
import Numlib.LinearAlgebra.Matrix.BlockDiagonal
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Quarteroni, Sacco and Saleri, Sections 1.1–1.6: Vector spaces and matrices

This module formalizes §1.1–1.6 of [quarteroni2000numerical]. These sections recall the linear
algebra that the rest of the book uses: linear independence, bases and dimension of a vector space;
the inverse of a square matrix; matrices as linear maps; operations on block-partitioned matrices;
the determinant and the Laplace rule; the rank and the kernel of a matrix; and the special shapes of
matrices (block diagonal, triangular, trapezoidal, banded, tridiagonal and Hessenberg). Almost every
numbered item of these sections is a structure of Mathlib, and the declarations here restate the
book's items in the book's notation.

The proofs use Mathlib and the backbone modules `Numlib.LinearAlgebra.Matrix.Rank` (the rank as the
maximal order of a nonvanishing minor), `Numlib.LinearAlgebra.Matrix.BlockDiagonal`,
`Numlib.LinearAlgebra.Matrix.Band` and `Numlib.LinearAlgebra.Matrix.Hessenberg` (banded, tridiagonal
and Hessenberg shapes), and `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`.

## Main definitions

* Definition 1.1: a vector space over a field $K$ is Mathlib's `Module K V`; it has no declaration
  here.
* Definition 1.2: a subspace, the span of a family and the direct sum are Mathlib's `Submodule`,
  `Submodule.span`, and `IsCompl` or `DirectSum.IsInternal`; they have no declaration here.
* Definition 1.3, `QuarteroniSaccoSaleri.Chapter01.definition_1_3`: linear independence of a family
  of vectors, and the components of a vector with respect to a basis.
* Definition 1.4: a submatrix is Mathlib's `Matrix.submatrix` along strictly monotone maps of the
  indices; it has no declaration here.
* Definition 1.5: a block-partitioned and a block diagonal matrix are Mathlib's `Matrix.fromBlocks`
  and `Matrix.blockDiagonal'`; they have no declaration here.
* Definition 1.6, `QuarteroniSaccoSaleri.Chapter01.definition_1_6`: an invertible matrix and its
  inverse.
* Definitions 1.7 and 1.8: the transpose and the conjugate transpose are Mathlib's
  `Matrix.transpose` and `Matrix.conjTranspose`; they have no declaration here.
* Definition 1.9: symmetric, skew-symmetric ($A^T = -A$) and orthogonal matrices are Mathlib's
  `Matrix.IsSymm`, the equation `Aᵀ = -A`, and `Matrix.orthogonalGroup`; they have no declaration
  here.
* Definition 1.10: Hermitian, unitary and normal matrices are Mathlib's `Matrix.IsHermitian`,
  `Matrix.unitaryGroup` and `IsStarNormal`; they have no declaration here.
* Definition 1.11: a linear map is Mathlib's `LinearMap`; it has no declaration here.
* Example 1.4, `QuarteroniSaccoSaleri.Chapter01.example_1_4_matrix`: the rotation matrix
  $G(\theta)$.
* Definition 1.12, `QuarteroniSaccoSaleri.Chapter01.definition_1_12`: the rank as the maximal order
  of a nonvanishing minor, stated as a theorem about Mathlib's `Matrix.rank`.

## Main results

* Definition 1.3, `QuarteroniSaccoSaleri.Chapter01.definition_1_3`: the characterization of linear
  independence by the vanishing of the coefficients, and the decomposition of a vector in a basis.
* Property 1.1, `QuarteroniSaccoSaleri.Chapter01.property_1_1`: if $V$ has a basis of $n$ vectors,
  then $\dim V = n$, every linearly independent family has at most $n$ elements, and every basis has
  $n$ elements.
* Example 1.3, `QuarteroniSaccoSaleri.Chapter01.example_1_3`: the space of $n$-vectors has dimension
  $n$, with the unit vectors as a basis.
* Definition 1.6, `QuarteroniSaccoSaleri.Chapter01.definition_1_6`: the inverse of an invertible
  matrix is invertible, and $(AB)^{-1} = B^{-1} A^{-1}$.
* Property 1.2, `QuarteroniSaccoSaleri.Chapter01.property_1_2`: a square matrix is invertible if and
  only if its columns are linearly independent.
* Equation (1.2), `QuarteroniSaccoSaleri.Chapter01.permMatrix_mem_orthogonalGroup`: the elementary
  permutation matrix exchanges two rows, and permutation matrices and their products are orthogonal.
* Property 1.3, `QuarteroniSaccoSaleri.Chapter01.property_1_3`: linear maps
  $\mathbb{C}^n \to \mathbb{C}^m$ correspond to matrices in $\mathbb{C}^{m \times n}$.
* Example 1.4, `QuarteroniSaccoSaleri.Chapter01.example_1_4`: $G(\theta)$ is orthogonal with
  determinant $1$, and it is the rotation by the angle $-\theta$.
* Property 1.4, `QuarteroniSaccoSaleri.Chapter01.property_1_4`: scalar multiplication,
  transposition, addition and multiplication of block-partitioned matrices act block by block.
* Equation (1.4), `QuarteroniSaccoSaleri.Chapter01.equation_1_4`: the Laplace rule for the
  determinant, and the cofactor formula for the inverse.
* §1.5, `QuarteroniSaccoSaleri.Chapter01.rank_transpose`: the rank is the dimension of the range,
  and $\operatorname{rank} A = \operatorname{rank} A^T$.
* §1.5, `QuarteroniSaccoSaleri.Chapter01.rank_add_finrank_ker`:
  $\operatorname{rank} A + \dim \ker A = n$.
* Example 1.5, `QuarteroniSaccoSaleri.Chapter01.example_1_5`: the rank and the kernel dimensions of
  one $2 \times 3$ matrix.
* §1.5, `QuarteroniSaccoSaleri.Chapter01.nonsingular_tfae`: six equivalent forms of nonsingularity.
* §1.6.1, `QuarteroniSaccoSaleri.Chapter01.det_blockDiagonal'`: the determinant of a block diagonal
  matrix is the product of the determinants of the blocks.
* §1.6.2, `QuarteroniSaccoSaleri.Chapter01.det_of_isTriangular`: the determinant of a triangular
  matrix is the product of its diagonal entries.
* §1.6.2, `QuarteroniSaccoSaleri.Chapter01.isTriangular_inv_mul`: inverses and products of lower
  (upper) triangular matrices are lower (upper) triangular.
* §1.6.2, `QuarteroniSaccoSaleri.Chapter01.isUpperTrapezoidal_mul`: products of upper (lower)
  trapezoidal matrices are upper (lower) trapezoidal.
* §1.6.2, `QuarteroniSaccoSaleri.Chapter01.isUnitTriangular_mul`: products of unit lower (upper)
  triangular matrices are unit lower (upper) triangular.
* §1.6.3, `QuarteroniSaccoSaleri.Chapter01.hasBandwidth_iff_shape`: the diagonal, triangular,
  tridiagonal, bidiagonal and Hessenberg shapes in terms of the lower and upper bands.
* §1.6.3, `QuarteroniSaccoSaleri.Chapter01.isTridiagonal_tridiag`: the matrices
  $\mathrm{tridiag}_n(b, d, c)$ and $\mathrm{tridiag}_n(\beta, \delta, \gamma)$ are tridiagonal.

## Conventions

* Indices are 0-based. A vector $x \in \mathbb{R}^n$ is `x : Fin n → ℝ`, and the product $Ax$ is
  `A *ᵥ x`.

## Implementation notes

* The elementary matrices of §1.3 are Mathlib's `Equiv.Perm.permMatrix`, `Matrix.swap` and
  `Matrix.transvection`. The trace and the determinant of §1.4, with their listed properties, are
  Mathlib's `Matrix.trace`, `Matrix.det_apply`, `Matrix.det_transpose`, `Matrix.det_mul`,
  `Matrix.det_nonsing_inv`, `Matrix.det_conjTranspose`, `Matrix.det_smul`,
  `Matrix.det_zero_of_row_eq`, `Matrix.det_permute`, `Matrix.det_diagonal`,
  `Matrix.isUnit_iff_isUnit_det`, `Matrix.inv_diagonal` and `Matrix.det_of_mem_unitary`. The range
  and the kernel of §1.5 are `LinearMap.range` and `LinearMap.ker` of `Matrix.mulVecLin`. These
  items have no declaration here.
* The bandwidth predicates of the backbone, `Matrix.HasLowerBandwidth` and
  `Matrix.HasUpperBandwidth` in `Numlib.LinearAlgebra.Matrix.Band`, are defined for square matrices
  over a linearly ordered index type. This is where the book uses them. The rectangular trapezoidal
  shapes of §1.6.2 are stated directly by the vanishing of entries.

## Deviations from the source

* **Example 1.3** (generalization). The dimension and coordinate basis statements hold over any
  field. See `QuarteroniSaccoSaleri.Chapter01.example_1_3`.
* **Definition 1.4** (typo). The book calls the selected rows and columns of a submatrix
  "contiguous"; only increasing indices are meant. Mathlib's `Matrix.submatrix` along strictly
  monotone maps is used.
* **Example 1.4** (correction). The book calls $G(\theta)$ the counterclockwise rotation by
  $\theta$; as printed, $G(\theta)$ is the rotation by $-\theta$. See
  `QuarteroniSaccoSaleri.Chapter01.example_1_4`.
* **Property 1.4** (reading and correction). Lean gives the two-by-two block case. For the
  product only the inner block sizes have to match, and the block columns come from the right
  factor. See `QuarteroniSaccoSaleri.Chapter01.property_1_4`.
* **The inverse formula after (1.4)** (generalization). The formula also holds at a singular matrix
  with Mathlib's total inverse. See `QuarteroniSaccoSaleri.Chapter01.equation_1_4`.
* **Definition 1.12** (reading). The order-zero minor gives rank zero when all positive-order
  minors vanish. See `QuarteroniSaccoSaleri.Chapter01.definition_1_12`.
* **Section 1.6.2, triangular inverses and products** (reading). The inverse clauses assume
  invertibility explicitly. See `QuarteroniSaccoSaleri.Chapter01.isTriangular_inv_mul`.
* **Section 1.6.2, trapezoidal products** (generalization). The product property also holds for
  lower trapezoidal factors. See `QuarteroniSaccoSaleri.Chapter01.isUpperTrapezoidal_mul`.
* **Section 1.6.3, banded matrices** (reading). The bandwidth predicates and shape equivalences are
  stated for square matrices. The text interchanges the upper and lower trapezoidal labels in
  its band discussion. Lean uses the entrywise definitions from §1.6.2. See
  `QuarteroniSaccoSaleri.Chapter01.hasBandwidth_iff_shape`.

## Not formalized

* **Examples 1.1 and 1.2.** They are prose.
* **Example 1.3, the function-space clause.** The space $C^p([a, b])$ is infinite-dimensional.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter01

/-! ### §1.1 Vector spaces -/

section VectorSpaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Definition 1.3** of [quarteroni2000numerical]. Let $V$ be a vector space over a field $K$. A
system $v_1, \dots, v_m$ of vectors of $V$ is **linearly independent** if and only if
$\alpha_1 v_1 + \dots + \alpha_m v_m = 0$ implies $\alpha_1 = \dots = \alpha_m = 0$. If
$b_1, \dots, b_n$ is a basis of $V$ and $u \in V$, then $u = \sum_i u_i b_i$, where the
**components** $u_i$ of $u$ with respect to the basis are the coefficients of its decomposition.

Linear independence is Mathlib's `LinearIndependent`, and a basis is `Module.Basis`: a linearly
independent system of generators. The component $u_i$ is `b.repr u i`. The proof uses
`Fintype.linearIndependent_iff`. -/
theorem definition_1_3 {m n : ℕ} (v : Fin m → V) (b : Module.Basis (Fin n) K V) (u : V) :
    (LinearIndependent K v ↔ ∀ α : Fin m → K, ∑ i, α i • v i = 0 → ∀ i, α i = 0) ∧
      ∑ i, b.repr u i • b i = u :=
  ⟨Fintype.linearIndependent_iff, b.sum_repr u⟩

/-- **Property 1.1** of [quarteroni2000numerical]. Let $V$ be a vector space over a field $K$ with a
basis of $n$ vectors. Then the **dimension** $\dim V$ is $n$, every linearly independent finite
system of vectors of $V$ has at most $n$ elements, and every other finite basis of $V$ has $n$
elements.

The dimension is Mathlib's `Module.finrank`. -/
theorem property_1_1 {n : ℕ} (b : Module.Basis (Fin n) K V) :
    Module.finrank K V = n ∧
      (∀ {ι : Type*} [Fintype ι] {v : ι → V}, LinearIndependent K v → Fintype.card ι ≤ n) ∧
      ∀ {ι : Type*} [Fintype ι], Module.Basis ι K V → Fintype.card ι = n := by
  have hfin : Module.Finite K V := Module.Finite.of_basis b
  have hn : Module.finrank K V = n := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  refine ⟨hn, fun hv => hn ▸ hv.fintype_card_le_finrank, fun b' => ?_⟩
  rw [← hn, Module.finrank_eq_card_basis b']

end VectorSpaces

/-- **Example 1.3** of [quarteroni2000numerical]. Let $\mathbb{K}$ be a field. The space
$\mathbb{K}^n$ has dimension $n$, and its usual basis is the system of unit vectors
$e_1, \dots, e_n$ with $(e_i)_j = \delta_{ij}$.

**Generalization.** The book gives the dimension for real and complex scalars and the coordinate
basis for real scalars. The same coordinate vectors give the basis and the dimension over any
field.

The usual basis is Mathlib's `Pi.basisFun`. -/
theorem example_1_3 (𝕜 : Type*) [Field 𝕜] (n : ℕ) :
    Module.finrank 𝕜 (Fin n → 𝕜) = n ∧
      ∀ i j : Fin n, Pi.basisFun 𝕜 (Fin n) i j = if i = j then 1 else 0 :=
  ⟨Module.finrank_fin_fun 𝕜, fun i j => by simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]⟩

/-! ### §1.3 Operations with matrices, the inverse -/

section Inverse

variable {𝕜 : Type*} [Field 𝕜] {n : ℕ}

/-- **Definition 1.6** of [quarteroni2000numerical]. Let $A$ and $B$ be square matrices of order $n$
over a field. The matrix $A$ is **invertible** (or regular, or nonsingular) if and only if there
is a matrix $B$ with $AB = BA = I$; then $B$ is the inverse $A^{-1}$. If $A$ is invertible, then
$A A^{-1} = A^{-1} A = I$, $A^{-1}$ is invertible, and $(A^{-1})^{-1} = A$. If $A$ and $B$ are
invertible, then $AB$ is invertible and $(AB)^{-1} = B^{-1} A^{-1}$.

Invertibility is Mathlib's `IsUnit A`, and the inverse is Mathlib's `A⁻¹`. -/
theorem definition_1_6 (A B : Matrix (Fin n) (Fin n) 𝕜) :
    ((∃ B, A * B = 1 ∧ B * A = 1) ↔ IsUnit A) ∧
      (IsUnit A → A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 ∧ IsUnit A⁻¹ ∧ A⁻¹⁻¹ = A) ∧
      (IsUnit A → IsUnit B → IsUnit (A * B) ∧ (A * B)⁻¹ = B⁻¹ * A⁻¹) := by
  refine ⟨isUnit_iff_exists.symm, fun hA => ?_, fun hA hB => ⟨hA.mul hB, Matrix.mul_inv_rev A B⟩⟩
  have hd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  exact ⟨mul_nonsing_inv A hd, nonsing_inv_mul A hd, isUnit_nonsing_inv_iff.2 hA,
    nonsing_inv_nonsing_inv A hd⟩

/-- **Property 1.2** of [quarteroni2000numerical]. A square matrix over a field is invertible if and
only if its column vectors are linearly independent.

The proof is Mathlib's `Matrix.linearIndependent_cols_iff_isUnit`. -/
theorem property_1_2 (A : Matrix (Fin n) (Fin n) 𝕜) :
    IsUnit A ↔ LinearIndependent 𝕜 A.col :=
  linearIndependent_col_iff_isUnit.symm

end Inverse

/-- **Equation (1.2)** of [quarteroni2000numerical], and the remark after Definition 1.9. Let
$\sigma$ and $\tau$ be permutations of $\{1, \dots, n\}$, with permutation matrices $P_\sigma$
and $P_\tau$. Then $P_\sigma$ is orthogonal, $P_\sigma^{-1} = P_\sigma^T$, and the product
$P_\sigma P_\tau$ is orthogonal. For indices $i$ and $j$, the elementary permutation matrix
$P^{(i,j)}$ of (1.2) is the permutation matrix of the transposition of $i$ and $j$, and for
every real matrix $A$ of order $n$ the product $P^{(i,j)} A$ is $A$ with the rows $i$ and $j$
exchanged: row $i$ of $P^{(i,j)} A$ is row $j$ of $A$, row $j$ is row $i$ of $A$, and every
other row is the row of $A$.

The matrix $P_\sigma$ is `σ.permMatrix ℝ`. The elementary matrix of the transposition of $i$ and
$j$ is `Matrix.swap ℝ i j`. Orthogonality is membership in `Matrix.orthogonalGroup`. -/
theorem permMatrix_mem_orthogonalGroup {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    σ.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
      (σ.permMatrix ℝ)⁻¹ = (σ.permMatrix ℝ)ᵀ ∧
      σ.permMatrix ℝ * τ.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
      ∀ (i j : Fin n) (A : Matrix (Fin n) (Fin n) ℝ),
        Matrix.swap ℝ i j = (Equiv.swap i j).permMatrix ℝ ∧
          (Matrix.swap ℝ i j * A) i = A j ∧ (Matrix.swap ℝ i j * A) j = A i ∧
          ∀ k, k ≠ i → k ≠ j → (Matrix.swap ℝ i j * A) k = A k := by
  have hmem : ∀ σ : Equiv.Perm (Fin n), σ.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    intro σ
    rw [mem_orthogonalGroup_iff (Fin n) ℝ, transpose_permMatrix, ← permMatrix_mul, inv_mul_cancel,
      permMatrix_one]
  refine ⟨hmem σ, ?_, (Matrix.orthogonalGroup (Fin n) ℝ).mul_mem (hmem σ) (hmem τ),
    fun i j A => ⟨rfl, ?_, ?_, fun k hki hkj => ?_⟩⟩
  · exact inv_eq_right_inv ((mem_orthogonalGroup_iff (Fin n) ℝ).1 (hmem σ))
  · ext a; exact swap_mul_apply_left i j a A
  · ext a; exact swap_mul_apply_right i j a A
  · ext a; exact swap_mul_of_ne hki hkj A

/-! ### §1.3.2 Matrices and linear mappings -/

/-- **Property 1.3** of [quarteroni2000numerical], with (1.3). For every linear map
$f : \mathbb{C}^n \to \mathbb{C}^m$ there is a unique matrix $A_f \in \mathbb{C}^{m \times n}$
such that $f(x) = A_f x$ for all $x \in \mathbb{C}^n$. Conversely, for every
$A \in \mathbb{C}^{m \times n}$ the map $x \mapsto Ax$ is linear.

The map $x \mapsto Ax$ is `Matrix.mulVecLin A`, and the matrix $A_f$ is `LinearMap.toMatrix' f`. -/
theorem property_1_3 {m n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)) (A : Matrix (Fin m) (Fin n) ℂ) :
    (∃! A : Matrix (Fin m) (Fin n) ℂ, ∀ x, f x = A *ᵥ x) ∧ IsLinearMap ℂ fun x => A *ᵥ x := by
  refine ⟨⟨LinearMap.toMatrix' f, fun x => (LinearMap.toMatrix'_mulVec f x).symm, fun B hB => ?_⟩,
    A.mulVecLin.isLinear⟩
  have h : Matrix.toLin' B = f := LinearMap.ext fun x => by rw [Matrix.toLin'_apply, hB x]
  rw [← h, LinearMap.toMatrix'_toLin']

/-- **Example 1.4** of [quarteroni2000numerical], the rotation matrix. For $\theta \in \mathbb{R}$,
$$G(\theta) = \begin{bmatrix} \cos\theta & \sin\theta \\ -\sin\theta & \cos\theta
  \end{bmatrix}.$$
-/
noncomputable def example_1_4_matrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

/-- **Example 1.4** of [quarteroni2000numerical]. Let $\theta, x_1, x_2 \in \mathbb{R}$. The matrix
$G(\theta)$ is orthogonal with $\det G(\theta) = 1$, and
$$G(\theta) \begin{bmatrix} x_1 \\ x_2 \end{bmatrix} = \begin{bmatrix} x_1 \cos\theta + x_2
  \sin\theta \\ -x_1 \sin\theta + x_2 \cos\theta \end{bmatrix}.$$
If $\mathbb{R}^2$ is identified with $\mathbb{C}$ by $(y_1, y_2) \mapsto y_1 + i y_2$, this
image is $e^{-i\theta} (x_1 + i x_2)$. So $G(\theta)$ is the rotation by the angle $-\theta$.

**Correction.** The book calls $G(\theta)$ the counterclockwise rotation by the angle $\theta$.
As printed, $G(\theta)$ is the clockwise rotation by $\theta$. The counterclockwise rotation by
$\theta$ is the transpose $\begin{bmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta
\end{bmatrix}$.

The matrix $G(\theta)$ is `QuarteroniSaccoSaleri.Chapter01.example_1_4_matrix θ`. -/
theorem example_1_4 (θ x₁ x₂ : ℝ) :
    example_1_4_matrix θ ∈ Matrix.orthogonalGroup (Fin 2) ℝ ∧ (example_1_4_matrix θ).det = 1 ∧
      example_1_4_matrix θ *ᵥ ![x₁, x₂] =
        ![x₁ * Real.cos θ + x₂ * Real.sin θ, -x₁ * Real.sin θ + x₂ * Real.cos θ] ∧
      ((⟨x₁ * Real.cos θ + x₂ * Real.sin θ, -x₁ * Real.sin θ + x₂ * Real.cos θ⟩ : ℂ) =
        Complex.exp (-(θ : ℂ) * Complex.I) * ⟨x₁, x₂⟩) := by
  have hsc := Real.sin_sq_add_cos_sq θ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_orthogonalGroup_iff (Fin 2) ℝ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [example_1_4_matrix, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
  · rw [example_1_4_matrix, det_fin_two_of]
    nlinarith
  · ext i
    fin_cases i <;> simp [example_1_4_matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  · have h : -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
      Real.sin_neg]
    apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;> ring

/-! ### §1.3.3 Operations with block-partitioned matrices -/

/-- **Property 1.4** of [quarteroni2000numerical]. Operations on block-partitioned complex matrices
are performed block by block. Let
$$A = \begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix}, \quad A' =
  \begin{bmatrix} A'_{11} & A'_{12} \\ A'_{21} & A'_{22} \end{bmatrix}, \quad B =
  \begin{bmatrix} B_{11} & B_{12} \\ B_{21} & B_{22} \end{bmatrix},$$
where $A_{ij}, A'_{ij} \in \mathbb{C}^{k_i \times l_j}$ and
$B_{ij} \in \mathbb{C}^{l_i \times m_j}$, and let $c \in \mathbb{C}$. Then: (1) $cA$ has the
blocks $c A_{ij}$, and $A^T$ has the blocks $(A^T)_{ij} = A_{ji}^T$; (2) $A + A'$ has the blocks
$A_{ij} + A'_{ij}$; (3) $AB$ has the blocks $C_{ij} = \sum_s A_{is} B_{sj}$.

**Reading.** The book states the property for a general $k \times l$ partition. Here it is in
$2 \times 2$ block form `Matrix.fromBlocks`, to which the general partition reduces by
induction.

**Correction.** For (3) the printed condition $k_i=n_i$ equates outer block sizes that need
not agree. The product needs matching inner blocks and its block columns follow the right
factor, with $C_{kn}$ in the lower-right corner of the general display. -/
theorem property_1_4 {k₁ k₂ l₁ l₂ m₁ m₂ : ℕ} (c : ℂ)
    (A₁₁ : Matrix (Fin k₁) (Fin l₁) ℂ) (A₁₂ : Matrix (Fin k₁) (Fin l₂) ℂ)
    (A₂₁ : Matrix (Fin k₂) (Fin l₁) ℂ) (A₂₂ : Matrix (Fin k₂) (Fin l₂) ℂ)
    (A'₁₁ : Matrix (Fin k₁) (Fin l₁) ℂ) (A'₁₂ : Matrix (Fin k₁) (Fin l₂) ℂ)
    (A'₂₁ : Matrix (Fin k₂) (Fin l₁) ℂ) (A'₂₂ : Matrix (Fin k₂) (Fin l₂) ℂ)
    (B₁₁ : Matrix (Fin l₁) (Fin m₁) ℂ) (B₁₂ : Matrix (Fin l₁) (Fin m₂) ℂ)
    (B₂₁ : Matrix (Fin l₂) (Fin m₁) ℂ) (B₂₂ : Matrix (Fin l₂) (Fin m₂) ℂ) :
    c • fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ = fromBlocks (c • A₁₁) (c • A₁₂) (c • A₂₁) (c • A₂₂) ∧
      (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)ᵀ = fromBlocks A₁₁ᵀ A₂₁ᵀ A₁₂ᵀ A₂₂ᵀ ∧
      fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ + fromBlocks A'₁₁ A'₁₂ A'₂₁ A'₂₂ =
        fromBlocks (A₁₁ + A'₁₁) (A₁₂ + A'₁₂) (A₂₁ + A'₂₁) (A₂₂ + A'₂₂) ∧
      fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ * fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ =
        fromBlocks (A₁₁ * B₁₁ + A₁₂ * B₂₁) (A₁₁ * B₁₂ + A₁₂ * B₂₂)
          (A₂₁ * B₁₁ + A₂₂ * B₂₁) (A₂₁ * B₁₂ + A₂₂ * B₂₂) :=
  ⟨fromBlocks_smul c A₁₁ A₁₂ A₂₁ A₂₂, fromBlocks_transpose A₁₁ A₁₂ A₂₁ A₂₂,
    fromBlocks_add A₁₁ A₁₂ A₂₁ A₂₂ A'₁₁ A'₁₂ A'₂₁ A'₂₂,
    fromBlocks_multiply A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂⟩

/-! ### §1.4 Trace and determinant -/

/-- **Equation (1.4)** of [quarteroni2000numerical] (the Laplace rule), and the cofactor formula for
the inverse. Let $A$ be a square matrix of order $n + 1$ over a field, and let $i$ be a row
index. For a matrix $A_0 = [a_{11}]$ of order $1$, $\det A_0 = a_{11}$. For $A$,
$$\det A = \sum_j \Delta_{ij} a_{ij}, \qquad \Delta_{ij} = (-1)^{i+j} \det A_{ij},$$
where $A_{ij}$ is the matrix obtained from $A$ by deleting row $i$ and column $j$. Moreover,
$A^{-1} = (\det A)^{-1} C$, where $C$ is the adjugate of $A$, the matrix with the entries
$c_{ji} = \Delta_{ij}$.

**Generalization.** The book states the adjugate formula for invertible matrices. It holds for
singular matrices as well because Mathlib's matrix inverse and the inverse of the determinant
both give zero in that case.

The adjugate is `Matrix.adjugate`. The proof uses `Matrix.det_succ_row`, `Matrix.inv_def` and
`Matrix.adjugate_fin_succ_eq_det_submatrix`. -/
theorem equation_1_4 {𝕜 : Type*} [Field 𝕜] {n : ℕ} (A₀ : Matrix (Fin 1) (Fin 1) 𝕜)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) (i : Fin (n + 1)) :
    A₀.det = A₀ 0 0 ∧
      A.det = ∑ j : Fin (n + 1),
        (-1) ^ (i + j : ℕ) * (A.submatrix i.succAbove j.succAbove).det * A i j ∧
      A⁻¹ = A.det⁻¹ • A.adjugate ∧
      ∀ i j : Fin (n + 1),
        A.adjugate j i = (-1) ^ (i + j : ℕ) * (A.submatrix i.succAbove j.succAbove).det := by
  refine ⟨det_fin_one A₀, ?_, ?_, fun i j => adjugate_fin_succ_eq_det_submatrix A j i⟩
  · rw [det_succ_row A i]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [Matrix.inv_def, Ring.inverse_eq_inv']

/-! ### §1.5 Rank and kernel -/

section Rank

open scoped ComplexOrder

variable {𝕜 : Type*} [Field 𝕜] {m n : ℕ}

/-- **Definition 1.12** of [quarteroni2000numerical]. Let $A \in \mathbb{K}^{m \times n}$ over a
field $\mathbb{K}$. The **rank** of $A$ is the maximum order of the nonvanishing determinants
extracted from $A$, that is, the largest $k$ such that the square submatrix of $A$ along some
$k$ distinct rows and some $k$ distinct columns has nonzero determinant. Moreover, $A$ has
**full rank**, $\operatorname{rank} A = \min(m, n)$, if and only if some determinant of order
$\min(m, n)$ extracted from $A$ does not vanish.

**Reading.** The book describes extracted determinants of positive order. The theorem includes
the order-zero minor, whose determinant is $1$. This specifies rank zero when all positive-order
minors vanish and also covers matrices with an empty dimension.

The statement is a theorem about Mathlib's `Matrix.rank`, the dimension of the range of $A$. The
proof specializes the backbone theorem `Matrix.rank_eq_sup_card_det_submatrix_ne_zero`. The rows
and the columns of a submatrix are given by injective maps from `Fin k`. -/
theorem definition_1_12 (A : Matrix (Fin m) (Fin n) 𝕜) :
    A.rank = sSup {k | ∃ (r : Fin k ↪ Fin m) (c : Fin k ↪ Fin n), (A.submatrix r c).det ≠ 0} ∧
      (A.rank = min m n ↔
        ∃ (r : Fin (min m n) ↪ Fin m) (c : Fin (min m n) ↪ Fin n), (A.submatrix r c).det ≠ 0) := by
  refine ⟨rank_eq_sup_card_det_submatrix_ne_zero A, fun hk => ?_, fun ⟨r, c, h⟩ => ?_⟩
  · obtain ⟨r, c, h⟩ := exists_det_submatrix_ne_zero A
    have hdet : (A.submatrix (r ∘ Fin.cast hk.symm) (c ∘ Fin.cast hk.symm)).det ≠ 0 := by
      rw [← submatrix_submatrix]
      exact (det_submatrix_equiv_self (finCongr hk.symm) (A.submatrix r c)).symm ▸ h
    exact ⟨⟨_, (injective_of_det_submatrix_ne_zero_left A h).comp (Fin.cast_injective _)⟩,
      ⟨_, (injective_of_det_submatrix_ne_zero_right A h).comp (Fin.cast_injective _)⟩, hdet⟩
  · refine le_antisymm (le_min ?_ ?_) (card_le_rank_of_det_submatrix_ne_zero A h)
    · simpa using rank_le_card_height A
    · simpa using rank_le_card_width A

/-- **Equation (1.5)** of [quarteroni2000numerical], and the first relation of §1.5. Let
$A \in \mathbb{R}^{m \times n}$ and $B \in \mathbb{C}^{m \times n}$. The range of $A$ is
$\operatorname{range}(A) = \{y : y = Ax \text{ for some } x\}$, and the rank of $A$ is the
dimension of $\operatorname{range}(A)$. Moreover, $\operatorname{rank} A^T = \operatorname{rank}
A$ (row rank equals column rank), and $\operatorname{rank} B^H = \operatorname{rank} B$.

The range is `LinearMap.range A.mulVecLin`. -/
theorem rank_transpose (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) (Fin n) ℂ) :
    A.rank = Module.finrank ℝ (LinearMap.range A.mulVecLin) ∧
      (∀ y, y ∈ LinearMap.range A.mulVecLin ↔ ∃ x, A *ᵥ x = y) ∧
      Aᵀ.rank = A.rank ∧ Bᴴ.rank = B.rank :=
  ⟨rfl, fun _ => LinearMap.mem_range, Matrix.rank_transpose A, Matrix.rank_conjTranspose B⟩

/-- **Section 1.5** of [quarteroni2000numerical], the second relation. Let
$A \in \mathbb{R}^{m \times n}$. The kernel of $A$ is $\ker(A) = \{x : Ax = 0\}$, and
$$\operatorname{rank} A + \dim \ker A = n.$$
For a nonsingular square matrix $B$ of order $n$, $\operatorname{rank} B = n$ and
$\dim \ker B = 0$.

The kernel is `LinearMap.ker A.mulVecLin`. The proof uses Mathlib's
`LinearMap.finrank_range_add_finrank_ker`; the square case is the backbone theorem
`Matrix.rank_add_finrank_ker_mulVecLin`. -/
theorem rank_add_finrank_ker (A : Matrix (Fin m) (Fin n) ℝ) :
    (∀ x, x ∈ LinearMap.ker A.mulVecLin ↔ A *ᵥ x = 0) ∧
      A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = n ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, IsUnit B →
        B.rank = n ∧ Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 0 := by
  refine ⟨fun x => LinearMap.mem_ker, ?_, fun B hB => ?_⟩
  · have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rwa [Module.finrank_fin_fun] at h
  · have hr : B.rank = n := by rw [rank_of_isUnit B hB, Fintype.card_fin]
    have h := rank_add_finrank_ker_mulVecLin B
    rw [Fintype.card_fin, hr] at h
    exact ⟨hr, by omega⟩

/-- **Example 1.5** of [quarteroni2000numerical]. For
$$A = \begin{bmatrix} 1 & 1 & 0 \\ 1 & -1 & 1 \end{bmatrix} \in \mathbb{R}^{2 \times 3},$$
$\operatorname{rank} A = 2$, $\dim \ker A = 1$ and $\dim \ker A^T = 0$.

The leading $2 \times 2$ minor is $-2 \neq 0$, so the rank is $2$, and the two relations of §1.5
give the dimensions of the kernels. -/
theorem example_1_5 :
    (!![1, 1, 0; 1, -1, 1] : Matrix (Fin 2) (Fin 3) ℝ).rank = 2 ∧
      Module.finrank ℝ (LinearMap.ker (!![1, 1, 0; 1, -1, 1] : Matrix (Fin 2) (Fin 3) ℝ).mulVecLin)
        = 1 ∧
      Module.finrank ℝ
        (LinearMap.ker (!![1, 1, 0; 1, -1, 1] : Matrix (Fin 2) (Fin 3) ℝ)ᵀ.mulVecLin) = 0 := by
  set A : Matrix (Fin 2) (Fin 3) ℝ := !![1, 1, 0; 1, -1, 1] with hA
  have hminor : (A.submatrix id (Fin.castLE (by norm_num : 2 ≤ 3))).det ≠ 0 := by
    rw [det_fin_two]
    simp [hA, Fin.castLE]
    norm_num
  have hrank : A.rank = 2 :=
    le_antisymm (by simpa using rank_le_card_height A)
      (card_le_rank_of_det_submatrix_ne_zero A hminor)
  have h1 := (rank_add_finrank_ker A).2.1
  have h2 := (rank_add_finrank_ker Aᵀ).2.1
  rw [Matrix.rank_transpose] at h2
  refine ⟨hrank, ?_, ?_⟩ <;> omega

/-- **Section 1.5** of [quarteroni2000numerical], the equivalent forms of nonsingularity, with the
condition on the eigenvalues from §1.7. For $A \in \mathbb{C}^{n \times n}$ the following are
equivalent: (1) $A$ is nonsingular; (2) $\det A \neq 0$; (3) $\ker A = \{0\}$; (4)
$\operatorname{rank} A = n$; (5) the rows of $A$ are linearly independent and the columns of $A$
are linearly independent; (6) $0$ is not an eigenvalue of $A$.

Nonsingularity is `IsUnit A`. Condition (6) says that $0$ is not in `spectrum ℂ A`. -/
theorem nonsingular_tfae (A : Matrix (Fin n) (Fin n) ℂ) :
    List.TFAE [IsUnit A, A.det ≠ 0, LinearMap.ker A.mulVecLin = ⊥, A.rank = n,
      LinearIndependent ℂ A.row ∧ LinearIndependent ℂ A.col, (0 : ℂ) ∉ spectrum ℂ A] := by
  tfae_have 1 ↔ 2 := by rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  tfae_have 1 ↔ 3 := by
    rw [LinearMap.ker_eq_bot, coe_mulVecLin, mulVec_injective_iff_isUnit]
  tfae_have 1 → 4 := fun h => by rw [rank_of_isUnit A h, Fintype.card_fin]
  tfae_have 4 → 3 := fun h => by
    have hk := rank_add_finrank_ker_mulVecLin A
    rw [Fintype.card_fin, h] at hk
    exact Submodule.finrank_eq_zero.1 (by omega)
  tfae_have 1 ↔ 5 := by
    rw [linearIndependent_row_iff_isUnit, linearIndependent_col_iff_isUnit, and_self]
  tfae_have 1 ↔ 6 := by rw [spectrum.zero_notMem_iff]
  tfae_finish

end Rank

/-! ### §1.6 Special matrices -/

section Special

variable {𝕜 : Type*} [Field 𝕜] {n : ℕ}

/-- **Section 1.6.1** of [quarteroni2000numerical]. Let $D = \operatorname{diag}(D_1, \dots, D_k)$
be a block diagonal matrix over a field, whose diagonal blocks $D_i$ are square matrices of
possibly different orders. Then
$$\det D = \prod_{i=1}^k \det D_i.$$

The matrix $D$ is Mathlib's `Matrix.blockDiagonal' D`. The proof is the backbone theorem
`Matrix.det_blockDiagonal'`. -/
theorem det_blockDiagonal' {k : ℕ} {sz : Fin k → ℕ}
    (D : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) 𝕜) :
    (blockDiagonal' D).det = ∏ i, (D i).det :=
  Matrix.det_blockDiagonal' D

/-- **Section 1.6.2** of [quarteroni2000numerical], the first statement. A square matrix $L$ over a
field is **lower triangular** if and only if $l_{ij} = 0$ for $i < j$, and a square matrix $U$
is **upper triangular** if and only if $u_{ij} = 0$ for $i > j$. The determinant of a lower or
an upper triangular matrix is the product of its diagonal entries.

The two shapes are Mathlib's `Matrix.IsLowerTriangular` and `Matrix.IsUpperTriangular`. -/
theorem det_of_isTriangular (L U : Matrix (Fin n) (Fin n) 𝕜) :
    (L.IsLowerTriangular ↔ ∀ i j, i < j → L i j = 0) ∧
      (U.IsUpperTriangular ↔ ∀ i j, j < i → U i j = 0) ∧
      (L.IsLowerTriangular → L.det = ∏ i, L i i) ∧
      (U.IsUpperTriangular → U.det = ∏ i, U i i) :=
  ⟨Iff.rfl, Iff.rfl, det_of_isLowerTriangular L, fun hU => det_of_isUpperTriangular hU⟩

/-- **Section 1.6.2** of [quarteroni2000numerical], the second and the third statements. Let
$L, L', U, U'$ be square matrices of order $n$ over a field. If $L$ is lower triangular and
invertible, then $L^{-1}$ is lower triangular; if $U$ is upper triangular and invertible, then
$U^{-1}$ is upper triangular. If $L$ and $L'$ are lower triangular, then $LL'$ is lower
triangular; if $U$ and $U'$ are upper triangular, then $UU'$ is upper triangular.

**Reading.** The source refers to the inverse of a triangular matrix without spelling out the
invertibility assumption. The declaration requires invertibility for the inverse clauses so
they describe the ordinary matrix inverse.

The proof uses Mathlib's `Matrix.blockTriangular_inv_of_blockTriangular` and
`Matrix.BlockTriangular.mul`. -/
theorem isTriangular_inv_mul (L L' U U' : Matrix (Fin n) (Fin n) 𝕜) :
    (L.IsLowerTriangular → IsUnit L → L⁻¹.IsLowerTriangular) ∧
      (U.IsUpperTriangular → IsUnit U → U⁻¹.IsUpperTriangular) ∧
      (L.IsLowerTriangular → L'.IsLowerTriangular → (L * L').IsLowerTriangular) ∧
      (U.IsUpperTriangular → U'.IsUpperTriangular → (U * U').IsUpperTriangular) := by
  refine ⟨fun hL hu => ?_, fun hU hu => ?_, fun hL hL' => hL.mul hL', fun hU hU' => hU.mul hU'⟩
  · have := hu.invertible
    exact blockTriangular_inv_of_blockTriangular hL
  · have := hu.invertible
    exact blockTriangular_inv_of_blockTriangular hU

/-- **Section 1.6.2** of [quarteroni2000numerical], the third statement for trapezoidal matrices. A
matrix $A \in \mathbb{K}^{m \times p}$ is **upper trapezoidal** if $a_{ij} = 0$ for $i > j$, and
**lower trapezoidal** if $a_{ij} = 0$ for $i < j$. Let $A \in \mathbb{K}^{m \times p}$ and
$B \in \mathbb{K}^{p \times q}$ over a field $\mathbb{K}$. If $A$ and $B$ are upper trapezoidal,
then $AB$ is upper trapezoidal. If $A$ and $B$ are lower trapezoidal, then $AB$ is lower
trapezoidal.

**Generalization.** The book pairs the product of upper trapezoidal matrices with that of lower
triangular matrices. The lower statement also holds for rectangular factors because any
nonzero term contributing to $(AB)_{ij}$ must have an intermediate index $k$ with $i \ge k \ge j$.

The two shapes are stated directly by the vanishing of the entries, without a named predicate. -/
theorem isUpperTrapezoidal_mul {m p q : ℕ} (A : Matrix (Fin m) (Fin p) 𝕜)
    (B : Matrix (Fin p) (Fin q) 𝕜) :
    ((∀ (i : Fin m) (j : Fin p), (j : ℕ) < i → A i j = 0) →
        (∀ (i : Fin p) (j : Fin q), (j : ℕ) < i → B i j = 0) →
        ∀ (i : Fin m) (j : Fin q), (j : ℕ) < i → (A * B) i j = 0) ∧
      ((∀ (i : Fin m) (j : Fin p), (i : ℕ) < j → A i j = 0) →
        (∀ (i : Fin p) (j : Fin q), (i : ℕ) < j → B i j = 0) →
        ∀ (i : Fin m) (j : Fin q), (i : ℕ) < j → (A * B) i j = 0) :=
  ⟨fun hA hB _ _ hij =>
      Matrix.mul_apply_eq_zero_of_lt (b := Fin.val) (c := Fin.val) (d := Fin.val) hA hB hij,
    fun hA hB _ _ hij =>
      Matrix.mul_apply_eq_zero_of_lt (b := fun i : Fin m => OrderDual.toDual i.val)
      (c := fun k : Fin p => OrderDual.toDual k.val) (d := fun j : Fin q => OrderDual.toDual j.val)
      (fun i k h => hA i k h) (fun k j h => hB k j h) hij⟩

/-- **Section 1.6.2** of [quarteroni2000numerical], the last statement. A square matrix $L$ over a
field is **unit lower triangular** if and only if it is lower triangular with diagonal entries
$l_{ii} = 1$. The product of two unit lower triangular matrices is unit lower triangular, and
the product of two unit upper triangular matrices is unit upper triangular.

Unit lower triangularity is the backbone predicate `Matrix.IsUnitLowerTriangular`. A matrix $U$
is unit upper triangular when $U^T$ is unit lower triangular. The proof uses the backbone
theorem `Matrix.IsUnitLowerTriangular.mul`. -/
theorem isUnitTriangular_mul (L L' U U' : Matrix (Fin n) (Fin n) 𝕜) :
    (L.IsUnitLowerTriangular ↔ L.IsLowerTriangular ∧ ∀ i, L i i = 1) ∧
      (L.IsUnitLowerTriangular → L'.IsUnitLowerTriangular → (L * L').IsUnitLowerTriangular) ∧
      (Uᵀ.IsUnitLowerTriangular → U'ᵀ.IsUnitLowerTriangular →
        (U * U')ᵀ.IsUnitLowerTriangular) := by
  refine ⟨⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩, fun h h' => h.mul h', fun h h' => ?_⟩
  rw [transpose_mul]
  exact h'.mul h

/-- **Section 1.6.3** of [quarteroni2000numerical], banded matrices. Let $A$ be a square matrix of
order $n$ over a field, and let $p, q \ge 0$. The matrix $A$ has **lower band** $p$ if and only
if $a_{ij} = 0$ for $i > j + p$, and **upper band** $q$ if and only if $a_{ij} = 0$ for
$j > i + q$. The named shapes are characterized by the bands as follows:

* $A$ is diagonal if and only if it has lower band $0$ and upper band $0$;
* $A$ is lower triangular if and only if it has upper band $0$, and upper triangular if and only
  if it has lower band $0$;
* $A$ is tridiagonal if and only if it has lower band $1$ and upper band $1$;
* $A$ is upper bidiagonal if and only if it has lower band $0$ and upper band $1$, and lower
  bidiagonal if and only if it has lower band $1$ and upper band $0$;
* $A$ is upper Hessenberg if and only if it has lower band $1$, and $A^T$ is upper Hessenberg
  (that is, $A$ is lower Hessenberg) if and only if $A$ has upper band $1$.

Every matrix of order $n$ has lower band $n - 1$ and upper band $n - 1$.

**Reading.** The book defines the two bands for rectangular real or complex matrices. This
declaration states the shape equivalences for square matrices over a field, the domain of the
backbone bandwidth predicates.
The book reverses the trapezoidal labels in §1.6.3. The upper shape has lower band zero and
the lower shape has upper band zero, by the entrywise definitions in §1.6.2.

The bands are the backbone predicates `Matrix.HasLowerBandwidth` and `Matrix.HasUpperBandwidth`
of `Numlib.LinearAlgebra.Matrix.Band`, read on `Fin n` through
`Matrix.hasLowerBandwidth_iff_fin`. The shapes are `Matrix.IsDiag`, `Matrix.IsLowerTriangular`,
`Matrix.IsUpperTriangular`, and the backbone predicates `Matrix.IsTridiagonal`,
`Matrix.IsUpperBidiagonal`, `Matrix.IsLowerBidiagonal` and `Matrix.IsUpperHessenberg`. The last
clause is the book's remark that the trapezoidal and the Hessenberg shapes have the bands
$p = m - 1$ and $q = n - 1$. -/
theorem hasBandwidth_iff_shape (A : Matrix (Fin n) (Fin n) 𝕜) (p q : ℕ) :
    (A.HasLowerBandwidth p ↔ ∀ i j : Fin n, (j : ℕ) + p < i → A i j = 0) ∧
      (A.HasUpperBandwidth q ↔ ∀ i j : Fin n, (i : ℕ) + q < j → A i j = 0) ∧
      (A.IsDiag ↔ A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth 0) ∧
      (A.IsLowerTriangular ↔ A.HasUpperBandwidth 0) ∧
      (A.IsUpperTriangular ↔ A.HasLowerBandwidth 0) ∧
      (A.IsTridiagonal ↔ A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth 1) ∧
      (A.IsUpperBidiagonal ↔ A.HasLowerBandwidth 0 ∧ A.HasUpperBandwidth 1) ∧
      (A.IsLowerBidiagonal ↔ A.HasLowerBandwidth 1 ∧ A.HasUpperBandwidth 0) ∧
      (A.IsUpperHessenberg ↔ A.HasLowerBandwidth 1) ∧
      (Aᵀ.IsUpperHessenberg ↔ A.HasUpperBandwidth 1) ∧
      A.HasLowerBandwidth (n - 1) ∧ A.HasUpperBandwidth (n - 1) := by
  refine ⟨hasLowerBandwidth_iff_fin, hasUpperBandwidth_iff_fin, isDiag_iff_hasBandwidth_zero,
    hasUpperBandwidth_zero_iff.symm, hasLowerBandwidth_zero_iff.symm,
    isTridiagonal_iff_hasBandwidth_one, ⟨IsUpperBidiagonal.hasBandwidth, fun h => ?_⟩,
    ⟨IsLowerBidiagonal.hasBandwidth, fun h => ?_⟩, isUpperHessenberg_iff_hasLowerBandwidth_one,
    ?_, ?_, ?_⟩
  · intro i j hij
    rcases hij with hij | hij
    · exact hasLowerBandwidth_zero_iff.1 h.1 hij
    · exact (isTridiagonal_iff_hasBandwidth_one.2 ⟨h.1.mono zero_le_one, h.2⟩) i j (Or.inr hij)
  · intro i j hij
    rcases hij with hij | hij
    · exact hasUpperBandwidth_zero_iff.1 h.2 hij
    · exact (isTridiagonal_iff_hasBandwidth_one.2 ⟨h.1, h.2.mono zero_le_one⟩) i j (Or.inl hij)
  · rw [isUpperHessenberg_iff_hasLowerBandwidth_one, ← hasLowerBandwidth_transpose_iff]
  · simpa using hasLowerBandwidth_card_sub_one (A := A)
  · simpa using hasUpperBandwidth_card_sub_one (A := A)

end Special

/-- **Section 1.6.3** of [quarteroni2000numerical], the matrices $\mathrm{tridiag}_n(b, d, c)$ and
$\mathrm{tridiag}_n(\beta, \delta, \gamma)$. Let $b, c \in \mathbb{R}^N$,
$d \in \mathbb{R}^{N+1}$ and $\beta, \delta, \gamma \in \mathbb{R}$. The tridiagonal matrix
$T = \mathrm{tridiag}_{N+1}(b, d, c)$ of order $N + 1$ has the entries $t_{ii} = d_i$,
$t_{i+1,i} = b_i$ and $t_{i,i+1} = c_i$ (with 0-based indices), and it is tridiagonal. The
matrix $\mathrm{tridiag}_{N+1}(\beta, \delta, \gamma)$ with constant bands is
$\mathrm{tridiag}_{N+1}(b, d, c)$ for the constant vectors $b = (\beta, \dots, \beta)$,
$d = (\delta, \dots, \delta)$ and $c = (\gamma, \dots, \gamma)$, and it is tridiagonal.

The first matrix is the backbone's `Matrix.tridiagonalOf b d c`, and the second is the
backbone's `Matrix.tridiagonalToeplitz (N + 1) β δ γ` of
`Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz`. -/
theorem isTridiagonal_tridiag {N : ℕ} (b : Fin N → ℝ) (d : Fin (N + 1) → ℝ) (c : Fin N → ℝ)
    (β δ γ : ℝ) :
    (∀ i, tridiagonalOf b d c i i = d i) ∧
      (∀ i : Fin N, tridiagonalOf b d c i.succ i.castSucc = b i) ∧
      (∀ i : Fin N, tridiagonalOf b d c i.castSucc i.succ = c i) ∧
      (tridiagonalOf b d c).IsTridiagonal ∧
      tridiagonalToeplitz (N + 1) β δ γ = tridiagonalOf (fun _ => β) (fun _ => δ) (fun _ => γ) ∧
      (tridiagonalToeplitz (N + 1) β δ γ).IsTridiagonal :=
  ⟨tridiagonalOf_apply_self b d c, tridiagonalOf_apply_succ_castSucc b d c,
    tridiagonalOf_apply_castSucc_succ b d c, isTridiagonal_tridiagonalOf b d c,
    tridiagonalToeplitz_eq_tridiagonalOf N β δ γ,
    (tridiagonalToeplitz_eq_tridiagonalOf N β δ γ).symm ▸ isTridiagonal_tridiagonalOf _ _ _⟩

end QuarteroniSaccoSaleri.Chapter01
