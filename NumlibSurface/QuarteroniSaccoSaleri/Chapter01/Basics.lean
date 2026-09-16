import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Swap
import Numlib.LinearAlgebra.Matrix.BlockDiagonal
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz

/-!
# Quarteroni–Sacco–Saleri §1.1–1.6: vector spaces, matrices, determinants, rank, special shapes

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §1.1–1.6. These sections recall the linear algebra the rest of the
book cites, and almost every numbered item is one of Mathlib's own structures, restated here in
the book's notation.

## What carries no declaration

The numbered items that *are* Mathlib definitions: Definition 1.1 (`Module K V`), 1.2
(`Submodule`, `Submodule.span`, the direct sum `IsCompl`/`DirectSum.IsInternal`), 1.4
(`Matrix.submatrix` along strictly monotone maps — the book's "contiguous" is a slip, only
increasing is meant), 1.5 (`Matrix.fromBlocks`, `Matrix.blockDiagonal'`), 1.7
(`Matrix.transpose`), 1.8 (`Matrix.conjTranspose`), 1.9 (`Matrix.IsSymm`, `Aᵀ = -A`,
`Matrix.orthogonalGroup`), 1.10 (`Matrix.IsHermitian`, `Matrix.unitaryGroup`, `IsStarNormal`),
1.11 (`LinearMap`); the elementary matrices of §1.3 (`Equiv.Perm.permMatrix`, `Matrix.swap`,
`Matrix.transvection`); the trace and determinant of §1.4 with their listed properties
(`Matrix.trace`, `Matrix.det_apply`, `Matrix.det_transpose`, `Matrix.det_mul`,
`Matrix.det_nonsing_inv`, `Matrix.det_conjTranspose`, `Matrix.det_smul`,
`Matrix.det_zero_of_row_eq`, `Matrix.det_permute`, `Matrix.det_diagonal`,
`Matrix.isUnit_iff_isUnit_det`, `Matrix.inv_diagonal`, `Matrix.det_of_mem_unitary`); the range
and kernel of §1.5 (`LinearMap.range`, `LinearMap.ker` of `Matrix.mulVecLin`). Examples 1.1 and
1.2 are prose.

## What does

* `definition_1_3`, `property_1_1`, `example_1_3` — linear independence, bases and dimension.
* `definition_1_6`, `property_1_2` — invertibility and its characterization by the columns.
* `permMatrix_mem_orthogonalGroup` — the elementary permutation matrices (1.2) and the remark
  after Definition 1.9 that permutation matrices are orthogonal.
* `property_1_3`, `example_1_4` — matrices as linear maps; the rotation matrix, with the sign
  erratum recorded (`G(θ)` as printed is the rotation by `-θ`).
* `property_1_4` — block operations, in the `2 × 2` block form to which the general partition
  reduces.
* `equation_1_4` — the Laplace rule and the cofactor formula for the inverse.
* `definition_1_12` — the rank as the maximal order of a nonvanishing minor, a theorem against
  Mathlib's `Matrix.rank`.
* `rank_transpose`, `rank_add_finrank_ker`, `example_1_5` — the two relations of §1.5 and the
  worked example.
* `nonsingular_tfae` — the five equivalent forms of nonsingularity, with "no null eigenvalue"
  from §1.7.
* `det_blockDiagonal'`, `det_of_isTriangular`, `isTriangular_inv_mul`, `isUpperTrapezoidal_mul`,
  `isUnitTriangular_mul` — §1.6.1–1.6.2.
* `hasBandwidth_iff_shape`, `isTridiagonal_tridiag` — the banded vocabulary of §1.6.3 as
  instances of the backbone's `Matrix.HasLowerBandwidth`/`Matrix.HasUpperBandwidth`.

## Conventions

Indices are `0`-based (`Fin n`). The book's `ℝⁿ` is `Fin n → ℝ` and `A x` is `A *ᵥ x`. The
backbone's bandwidth predicates are for square matrices over a linearly ordered index type
(`Numlib/LinearAlgebra/Matrix/Hessenberg`), which is where the book uses them; the rectangular
trapezoidal shapes of §1.6.2 are stated directly.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter01

/-! ### §1.1 Vector spaces -/

section VectorSpaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Definition 1.3.** A system `v₁, …, vₘ` of vectors is *linearly independent* when
`α₁ v₁ + ⋯ + αₘ vₘ = 0` forces `α₁ = ⋯ = αₘ = 0` (Mathlib's `LinearIndependent`, through
`Fintype.linearIndependent_iff`); a *basis* is a linearly independent system of generators
(`Module.Basis`), and the *components* of `u` with respect to the basis `b` are the coefficients
`b.repr u i` of its decomposition `u = ∑ i, (b.repr u i) • b i`. -/
theorem definition_1_3 {m n : ℕ} (v : Fin m → V) (b : Module.Basis (Fin n) K V) (u : V) :
    (LinearIndependent K v ↔ ∀ α : Fin m → K, ∑ i, α i • v i = 0 → ∀ i, α i = 0) ∧
      ∑ i, b.repr u i • b i = u :=
  ⟨Fintype.linearIndependent_iff, b.sum_repr u⟩

/-- **Property 1.1.** If `V` admits a basis of `n` vectors, then every linearly independent
system of vectors of `V` has at most `n` elements and any other basis of `V` has `n` elements;
the number `n = dim V` is the *dimension* of `V` (Mathlib's `Module.finrank`). -/
theorem property_1_1 {n : ℕ} (b : Module.Basis (Fin n) K V) :
    Module.finrank K V = n ∧
      (∀ {ι : Type*} [Fintype ι] {v : ι → V}, LinearIndependent K v → Fintype.card ι ≤ n) ∧
      ∀ {ι : Type*} [Fintype ι], Module.Basis ι K V → Fintype.card ι = n := by
  have hfin : Module.Finite K V := Module.Finite.of_basis b
  have hn : Module.finrank K V = n := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  refine ⟨hn, fun hv => hn ▸ hv.fintype_card_le_finrank, fun b' => ?_⟩
  rw [← hn, Module.finrank_eq_card_basis b']

end VectorSpaces

/-- **Example 1.3.** `ℝⁿ` and `ℂⁿ` have dimension `n`, and the usual basis is the set of unit
vectors `e₁, …, eₙ` with `(eᵢ)ⱼ = δᵢⱼ` (`Pi.basisFun`). The book's other clause, that
`C^p([a, b])` is infinite-dimensional, is not restated. -/
theorem example_1_3 (𝕜 : Type*) [Field 𝕜] (n : ℕ) :
    Module.finrank 𝕜 (Fin n → 𝕜) = n ∧
      ∀ i j : Fin n, Pi.basisFun 𝕜 (Fin n) i j = if i = j then 1 else 0 :=
  ⟨Module.finrank_fin_fun 𝕜, fun i j => by simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]⟩

/-! ### §1.3 Operations with matrices, the inverse -/

section Inverse

variable {𝕜 : Type*} [Field 𝕜] {n : ℕ}

/-- **Definition 1.6.** A square matrix `A` is *invertible* (regular, nonsingular) when there is
a `B` with `A B = B A = I` (Mathlib's `IsUnit A`); `B` is the inverse `A⁻¹`. If `A` is invertible
its inverse is invertible with `(A⁻¹)⁻¹ = A`, and if `A` and `B` are invertible so is `A B`, with
`(A B)⁻¹ = B⁻¹ A⁻¹`. -/
theorem definition_1_6 (A B : Matrix (Fin n) (Fin n) 𝕜) :
    ((∃ B, A * B = 1 ∧ B * A = 1) ↔ IsUnit A) ∧
      (IsUnit A → A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 ∧ IsUnit A⁻¹ ∧ A⁻¹⁻¹ = A) ∧
      (IsUnit A → IsUnit B → IsUnit (A * B) ∧ (A * B)⁻¹ = B⁻¹ * A⁻¹) := by
  refine ⟨isUnit_iff_exists.symm, fun hA => ?_, fun hA hB => ⟨hA.mul hB, Matrix.mul_inv_rev A B⟩⟩
  have hd : IsUnit A.det := (isUnit_iff_isUnit_det A).1 hA
  exact ⟨mul_nonsing_inv A hd, nonsing_inv_mul A hd, isUnit_nonsing_inv_iff.2 hA,
    nonsing_inv_nonsing_inv A hd⟩

/-- **Property 1.2.** A square matrix is invertible iff its column vectors are linearly
independent (`Matrix.linearIndependent_cols_iff_isUnit`). -/
theorem property_1_2 (A : Matrix (Fin n) (Fin n) 𝕜) :
    IsUnit A ↔ LinearIndependent 𝕜 A.col :=
  linearIndependent_cols_iff_isUnit.symm

end Inverse

/-- **§1.3, (1.2), and the remark after Definition 1.9.** The elementary permutation matrix
`P^{(i,j)}` of (1.2) is `Matrix.swap ℝ i j = (Equiv.swap i j).permMatrix ℝ`, and
pre-multiplying by it exchanges the rows `i` and `j`; the permutation matrices `σ.permMatrix ℝ`
are orthogonal, `P⁻¹ = Pᵀ`, and so is every product of them (the orthogonal group is closed
under multiplication). -/
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

/-- **Property 1.3, (1.3).** For every linear map `f : ℂⁿ → ℂᵐ` there is a unique matrix
`A_f ∈ ℂ^{m×n}` with `f x = A_f x` for all `x` (namely `LinearMap.toMatrix' f`); conversely, for
every `A ∈ ℂ^{m×n}` the map `x ↦ A x` is linear (`Matrix.mulVecLin A`). -/
theorem property_1_3 {m n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ)) (A : Matrix (Fin m) (Fin n) ℂ) :
    (∃! A : Matrix (Fin m) (Fin n) ℂ, ∀ x, f x = A *ᵥ x) ∧ IsLinearMap ℂ fun x => A *ᵥ x := by
  refine ⟨⟨LinearMap.toMatrix' f, fun x => (LinearMap.toMatrix'_mulVec f x).symm, fun B hB => ?_⟩,
    A.mulVecLin.isLinear⟩
  have h : Matrix.toLin' B = f := LinearMap.ext fun x => by rw [Matrix.toLin'_apply, hB x]
  rw [← h, LinearMap.toMatrix'_toLin']

/-- The matrix `G(θ) = [[cos θ, sin θ], [-sin θ, cos θ]]` of Example 1.4. -/
noncomputable def example_1_4_matrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

/-- **Example 1.4.** The rotation matrix `G(θ)` is orthogonal with determinant `1`, and it maps
`(x₁, x₂)` to `(x₁ cos θ + x₂ sin θ, -x₁ sin θ + x₂ cos θ)`, which under `ℝ² ≃ ℂ` is the point
`x₁ + i x₂` multiplied by `exp(-iθ)`: the rotation by the angle `-θ`. Book erratum: the text
calls `G(θ)` the *counterclockwise* rotation by `θ`; as printed it is the clockwise one (the
counterclockwise matrix is `[[c, -s], [s, c]]`, the transpose). -/
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

/-- **Property 1.4.** Operations on block-partitioned matrices are performed block by block, in
the `2 × 2` block form (`Matrix.fromBlocks`) to which the general `k × l` partition reduces by
induction: (1) `λ A` and `Aᵀ` blockwise, (2) `A + B` blockwise when the partitions agree, and
(3) `A B` with the blocks `C_ij = ∑_s A_is B_sj` when the column partition of `A` is the row
partition of `B`. -/
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

/-- **(1.4), the Laplace rule, and the cofactor formula for the inverse.** For a matrix of
order `1`, `det A = a₁₁`; for order `n + 1 > 1` and any row `i`,
`det A = ∑ⱼ Δᵢⱼ aᵢⱼ` with the cofactors `Δᵢⱼ = (-1)^{i+j} det Aᵢⱼ`, `Aᵢⱼ` the matrix obtained by
deleting row `i` and column `j` (`Matrix.det_succ_row`); and `A⁻¹ = (det A)⁻¹ C` with
`C` the matrix of entries `Δⱼᵢ`, that is `C = adjugate A` (`Matrix.inv_def`,
`Matrix.adjugate_fin_succ_eq_det_submatrix`). Mathlib's `A⁻¹` is `0` for a singular `A`, so the
last identity holds without the invertibility hypothesis. -/
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

/-- **Definition 1.12.** The *rank* of `A ∈ 𝕜^{m×n}` is the maximum order of the nonvanishing
determinants extracted from `A` — the determinants of the square submatrices along `k` distinct
rows and `k` distinct columns — and it agrees with Mathlib's `Matrix.rank`, the dimension of
the range (backbone `Matrix.rank_eq_sup_card_det_submatrix_ne_zero`). `A` has *full rank*,
`rank A = min m n`, exactly when some determinant of order `min m n` does not vanish. -/
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

/-- **§1.5, (1.5) and relation 1.** The rank of `A` is the dimension of its range
`range(A) = {y : y = A x}`; `rank A = rank Aᵀ` ("row rank equals column rank"), and
`rank A = rank Aᴴ` for a complex matrix. -/
theorem rank_transpose (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin m) (Fin n) ℂ) :
    A.rank = Module.finrank ℝ (LinearMap.range A.mulVecLin) ∧
      (∀ y, y ∈ LinearMap.range A.mulVecLin ↔ ∃ x, A *ᵥ x = y) ∧
      Aᵀ.rank = A.rank ∧ Bᴴ.rank = B.rank :=
  ⟨rfl, fun _ => LinearMap.mem_range, Matrix.rank_transpose A, Matrix.rank_conjTranspose B⟩

/-- **§1.5, relation 2.** The kernel `ker(A) = {x : A x = 0}` satisfies
`rank A + dim ker A = n` for `A ∈ ℝ^{m×n}` (Mathlib's `LinearMap.finrank_range_add_finrank_ker`;
the square case is the backbone's `Matrix.rank_add_finrank_ker_mulVecLin`); for a nonsingular
square `A`, `rank A = n` and `dim ker A = 0`. -/
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

/-- **Example 1.5.** For `A = [[1, 1, 0], [1, -1, 1]]`, `rank A = 2`, `dim ker A = 1` and
`dim ker Aᵀ = 0`: the leading `2 × 2` minor is `-2 ≠ 0`, so the rank is `2`, and the two
rank–nullity relations give the kernel dimensions. -/
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

/-- **§1.5, the equivalent forms of nonsingularity** (with "no null eigenvalue" from §1.7). For
`A ∈ ℂ^{n×n}` the following are equivalent: (1) `A` is nonsingular; (2) `det A ≠ 0`;
(3) `ker A = {0}`; (4) `rank A = n`; (5) `A` has linearly independent rows and columns;
(6) `0` is not an eigenvalue of `A`. -/
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
    rw [linearIndependent_rows_iff_isUnit, linearIndependent_cols_iff_isUnit, and_self]
  tfae_have 1 ↔ 6 := by rw [spectrum.zero_notMem_iff]
  tfae_finish

end Rank

/-! ### §1.6 Special matrices -/

section Special

variable {𝕜 : Type*} [Field 𝕜] {n : ℕ}

/-- **§1.6.1.** The determinant of a block diagonal matrix `D = diag(D₁, …, Dₖ)`, whose
diagonal blocks `Dᵢ` are square matrices of possibly different sizes, is the product of the
determinants of the blocks (backbone `Matrix.det_blockDiagonal'`). -/
theorem det_blockDiagonal' {k : ℕ} {sz : Fin k → ℕ}
    (D : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) 𝕜) :
    (blockDiagonal' D).det = ∏ i, (D i).det :=
  Matrix.det_blockDiagonal' D

/-- **§1.6.2, first bullet.** A lower triangular matrix `L` has `lᵢⱼ = 0` for `i < j`
(`Matrix.IsLowerTriangular`), an upper triangular `U` has `uᵢⱼ = 0` for `i > j`
(`Matrix.IsUpperTriangular`), and the determinant of a triangular matrix is the product of its
diagonal entries. -/
theorem det_of_isTriangular (L U : Matrix (Fin n) (Fin n) 𝕜) :
    (L.IsLowerTriangular ↔ ∀ i j, i < j → L i j = 0) ∧
      (U.IsUpperTriangular ↔ ∀ i j, j < i → U i j = 0) ∧
      (L.IsLowerTriangular → L.det = ∏ i, L i i) ∧
      (U.IsUpperTriangular → U.det = ∏ i, U i i) :=
  ⟨Iff.rfl, Iff.rfl, det_of_isLowerTriangular L, fun hU => det_of_isUpperTriangular hU⟩

/-- **§1.6.2, second and third bullets.** The inverse of an invertible lower (respectively,
upper) triangular matrix is lower (upper) triangular
(`Matrix.blockTriangular_inv_of_blockTriangular`), and the product of two lower (upper)
triangular matrices is lower (upper) triangular (`Matrix.BlockTriangular.mul`). -/
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

/-- **§1.6.2, third bullet, the trapezoidal case.** An `m × n` matrix is *upper trapezoidal* when
`aᵢⱼ = 0` for `i > j` and *lower trapezoidal* when `aᵢⱼ = 0` for `i < j`; the product of two
upper (lower) trapezoidal matrices is upper (lower) trapezoidal. -/
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

/-- **§1.6.2, last bullet.** A *unit* triangular matrix is a triangular matrix with diagonal
entries `1` (`Matrix.IsUnitLowerTriangular`, and its transpose for the upper shape); the product
of two unit lower (upper) triangular matrices is unit lower (upper) triangular (backbone
`Matrix.IsUnitLowerTriangular.mul`). -/
theorem isUnitTriangular_mul (L L' U U' : Matrix (Fin n) (Fin n) 𝕜) :
    (L.IsUnitLowerTriangular ↔ L.IsLowerTriangular ∧ ∀ i, L i i = 1) ∧
      (L.IsUnitLowerTriangular → L'.IsUnitLowerTriangular → (L * L').IsUnitLowerTriangular) ∧
      (Uᵀ.IsUnitLowerTriangular → U'ᵀ.IsUnitLowerTriangular →
        (U * U')ᵀ.IsUnitLowerTriangular) := by
  refine ⟨⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩, fun h h' => h.mul h', fun h h' => ?_⟩
  rw [transpose_mul]
  exact h'.mul h

/-- **§1.6.3, banded matrices.** A square matrix `A` has *lower band* `p` when `aᵢⱼ = 0` for
`i > j + p` and *upper band* `q` when `aᵢⱼ = 0` for `j > i + q` (the backbone's
`Matrix.HasLowerBandwidth`/`Matrix.HasUpperBandwidth` of `Numlib/LinearAlgebra/Matrix/Hessenberg`,
through `Matrix.hasLowerBandwidth_iff_fin`); the named shapes are: diagonal `(p, q) = (0, 0)`;
lower triangular `q = 0` and upper triangular `p = 0`; tridiagonal `(1, 1)`; upper bidiagonal
`(0, 1)` and lower bidiagonal `(1, 0)`; upper Hessenberg `p = 1` and lower Hessenberg (the
transpose of an upper Hessenberg matrix) `q = 1`. Every matrix of order `n` has both bands
`n - 1`, which is the book's `p = m - 1`, `q = n - 1` for the trapezoidal and Hessenberg shapes. -/
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
  · rw [isUpperHessenberg_iff_hasLowerBandwidth_one, hasUpperBandwidth_iff_transpose]
  · simpa using hasLowerBandwidth_card_sub_one (A := A)
  · simpa using hasUpperBandwidth_card_sub_one (A := A)

end Special

/-- **§1.6.3, `tridiagₙ(b, d, c)` and `tridiagₙ(β, δ, γ)`.** The tridiagonal matrix with the
vectors `b`, `d`, `c` on the lower, principal and upper diagonals is the backbone's
`Matrix.tridiagonalOf b d c`, the constant-coefficient one `Matrix.tridiagonalToeplitz n β δ γ`
(`Numlib/LinearAlgebra/Matrix/TridiagonalToeplitz`), the latter the former with constant bands;
both are tridiagonal. -/
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
