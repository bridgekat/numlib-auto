import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Numlib.Analysis.InnerProductSpace.PrincipalAngles
import Numlib.Eigen.InvariantSubspace
import Numlib.LinearAlgebra.Matrix.LeastSquares

/-!
# Singular-value inequalities for matrices

The matrix corollaries of the coordinate-free singular-value theory of
`Numlib/Analysis/InnerProductSpace/SingularValues` (Weyl's inequality, interlacing, the
stacked-isometry identity, the spectrum of the Hermitian dilation) and of the eigenvalue
inequalities of `Numlib/Eigen/MinMax` (Ky Fan, Hoffman–Wielandt, the trace inequality), in the
vocabulary of `Numlib/LinearAlgebra/Matrix/SVD` (`Matrix.sortedSingularValues`, `Matrix.IsSVD`,
`Matrix.svdTruncation`) and with the norms of `Numlib/Analysis/Matrix/OperatorNorm`.

## Main results

* `Matrix.hermitianDilation`: the Jordan–Wielandt matrix `[0 Aᴴ; A 0]`, with its operator
  (`Matrix.toEuclideanLin_hermitianDilation`) and its spectrum
  `Matrix.IsHermitian.eigenvalues₀_hermitianDilation`:
  `σ_0, …, σ_{p-1}, 0, …, 0, -σ_{p-1}, …, -σ_0`.
* `Matrix.abs_sortedSingularValues_add_sub_le`: **Weyl's perturbation bound**
  `|σ_i(A + B) − σ_i(A)| ≤ ‖B‖₂`, and its Frobenius form.
* `Matrix.sum_sq_sortedSingularValues_sub_le`: **Mirsky's inequality**
  `∑ (σ_k(A + E) - σ_k(A))² ≤ ‖E‖_F²`, Hoffman–Wielandt for the dilations.
* **Eckart–Young**: `Matrix.sortedSingularValues_le_l2_opNorm_sub_of_rank_le` and
  `Matrix.isLeast_l2_opNorm_sub_of_rank_le` in the `2`-norm,
  `Matrix.sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le` and
  `Matrix.isLeast_frobenius_norm_sub_of_rank_le` in the Frobenius norm, with the norms of the
  truncation residual `Matrix.l2_opNorm_sub_svdTruncation` and
  `Matrix.frobenius_norm_sub_svdTruncation`.
* `Matrix.isGreatest_frobenius_norm_sq_conjTranspose_mul`: **Ky Fan's maximum principle** in the
  form `max_{Qᴴ Q = 1} ‖Qᴴ A‖_F² = σ_0² + ⋯ + σ_{r-1}²`.
* `Matrix.norm_trace_mul_le_sum_sortedSingularValues_mul`: **von Neumann's trace inequality**.
* `Matrix.sortedSingularValues_submatrix_le`: deleting rows or columns does not increase any
  singular value, with the block forms `Matrix.sortedSingularValues_fromCols_left_le` (and
  `_right_le`, `Matrix.sortedSingularValues_fromRows_left_le`, `_right_le`).
* `Matrix.isStarProjection_mul_pinv`, `Matrix.isStarProjection_pinv_mul`: `A A⁺` and `A⁺ A` are
  orthogonal projectors, so they and their complements have spectral norm at most one.
* `Matrix.frobenius_norm_pinv_sub_le`: **Wedin's bound**
  `‖B⁺ - A⁺‖_F ≤ 2 ‖B - A‖_F max(‖A⁺‖₂², ‖B⁺‖₂²)` with no rank hypothesis, from the three-term
  decomposition `Matrix.pinv_sub_pinv_eq` ([golub2013matrix] §5.5.3).
* `Matrix.exists_singularSubspacePair_perturbation`: **the perturbation of a singular subspace
  pair** (Stewart, Wedin), with Wedin's condition for non-square trailing blocks, by Stewart's
  quadratic-equation lemma for the coupled Sylvester operator of the pair.

## Implementation notes

Matrices are indexed by arbitrary `Fintype`s wherever the statement allows it; only the statements
that mention an SVD (`Matrix.IsSVD` and `Matrix.svdTruncation` are `Fin`-indexed) are stated for
`Fin` shapes, and the others reach an SVD by reindexing
(`Matrix.sortedSingularValues_submatrix_equiv`).
The dilation `Matrix.hermitianDilation A` puts the domain factor first, as its operator
`LinearMap.hermitianDilation` does, so that its matrix is the operator conjugated by the isometry
`PiLp.sumPiLpEquivProdLpPiLp` and the two have the same characteristic polynomial. Mirsky's
inequality and von Neumann's inequality are then the Hoffman–Wielandt inequality and the trace
inequality for two symmetric operators, applied to dilations: the sorted spectrum of a dilation
is the singular values followed by their negatives, and the reflected pairing of such spectra
counts every product of singular values twice (`sum_range_sub_reflect_mul_sub_reflect`).

## References

* [golub2013matrix] G. H. Golub and C. F. Van Loan, *Matrix Computations*, 4th ed., §2.4, §2.5,
  §5.3, §5.5, §6.4, §7.3, §7.9, §8.1, §8.6, §12.5.
-/

open Module

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Submatrices and reindexing -/

section Submatrix

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l] [DecidableEq n]
  [DecidableEq k]

/-- Extension by zero along an injection, as a linear isometry of Euclidean spaces. -/
private noncomputable def extendByZeroIsometry (e : k ↪ n) :
    EuclideanSpace 𝕜 k →ₗᵢ[𝕜] EuclideanSpace 𝕜 n where
  toLinearMap := (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).symm.toLinearMap ∘ₗ
    Function.ExtendByZero.linearMap 𝕜 e ∘ₗ (WithLp.linearEquiv 2 𝕜 (k → 𝕜)).toLinearMap
  norm_map' x := PiLp.norm_toLp_extend 2 e.injective (WithLp.ofLp x)

/-- Deleting columns: the selected columns act as `A` composed with the isometric extension by
zero, and restricting the domain along an isometry can only decrease singular values
(`LinearMap.singularValues_comp_linearIsometry_le`). -/
private theorem sortedSingularValues_submatrix_id_le (A : Matrix m n 𝕜) {g : k → n}
    (hg : Function.Injective g) (i : ℕ) :
    (A.submatrix id g).sortedSingularValues i ≤ A.sortedSingularValues i := by
  have h : toEuclideanLin (A.submatrix id g) =
      toEuclideanLin A ∘ₗ (extendByZeroIsometry (𝕜 := 𝕜) ⟨g, hg⟩).toLinearMap := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, toEuclideanLin_apply, toEuclideanLin_apply,
      submatrix_mulVec_eq_comp_mulVec_extend A id hg, Function.comp_id]
    rfl
  change (toEuclideanLin (A.submatrix id g)).singularValues i ≤ _
  rw [h]
  exact (toEuclideanLin A).singularValues_comp_linearIsometry_le _ i

/-- Deleting rows: dropping coordinates of `A x` does not increase its norm. -/
private theorem sortedSingularValues_submatrix_id_right_le (A : Matrix m n 𝕜) {f : l → m}
    (hf : Function.Injective f) (i : ℕ) :
    (A.submatrix f id).sortedSingularValues i ≤ A.sortedSingularValues i :=
  LinearMap.singularValues_le_of_forall_norm_le _ (fun x => by
    rw [toEuclideanLin_apply, toEuclideanLin_apply]
    exact PiLp.norm_toLp_comp_le 2 hf (A *ᵥ WithLp.ofLp x)) i

/-- **Deleting rows and columns does not increase any singular value** ([golub2013matrix]
Corollary 2.4.5 iterated, and Corollary 8.6.3): for injective row and column selections `f`, `g`,
`σ_i(A.submatrix f g) ≤ σ_i(A)`, the singular-value form of `Matrix.l2_opNorm_submatrix_le` and
`Matrix.frobenius_norm_submatrix_le`. -/
theorem sortedSingularValues_submatrix_le (A : Matrix m n 𝕜) {f : l → m}
    (hf : Function.Injective f) {g : k → n} (hg : Function.Injective g) (i : ℕ) :
    (A.submatrix f g).sortedSingularValues i ≤ A.sortedSingularValues i :=
  calc (A.submatrix f g).sortedSingularValues i
      = ((A.submatrix f id).submatrix id g).sortedSingularValues i := rfl
    _ ≤ (A.submatrix f id).sortedSingularValues i := sortedSingularValues_submatrix_id_le _ hg i
    _ ≤ A.sortedSingularValues i := sortedSingularValues_submatrix_id_right_le _ hf i

/-- **Reindexing does not change the singular values**: for equivalences `e : l ≃ m`,
`f : k ≃ n`, `σ(A.submatrix e f) = σ(A)`. Both directions are deletions of no rows and
columns. -/
theorem sortedSingularValues_submatrix_equiv (A : Matrix m n 𝕜) (e : l ≃ m) (f : k ≃ n) :
    (A.submatrix e f).sortedSingularValues = A.sortedSingularValues := by
  funext i
  refine le_antisymm (sortedSingularValues_submatrix_le A e.injective f.injective i) ?_
  have h := sortedSingularValues_submatrix_le (A.submatrix e f) e.symm.injective
    f.symm.injective i
  rwa [submatrix_submatrix, e.self_comp_symm, f.self_comp_symm, submatrix_id_id] at h

end Submatrix

/-! ### Elementary facts about sorted singular values -/

section Basic

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Sorted singular values vanish from `min (card m) (card n)` on: there are at most that many
nonzero ones (`Matrix.sortedSingularValues_eq_zero_iff_rank_le`). -/
theorem sortedSingularValues_eq_zero_of_min_le (A : Matrix m n 𝕜) {k : ℕ}
    (hk : min (Fintype.card m) (Fintype.card n) ≤ k) : A.sortedSingularValues k = 0 :=
  (A.sortedSingularValues_eq_zero_iff_rank_le k).2
    ((le_min A.rank_le_card_height A.rank_le_card_width).trans hk)

/-- **A matrix and its conjugate transpose have the same singular values**
(`LinearMap.singularValues_adjoint`). -/
@[simp]
theorem sortedSingularValues_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) :
    Aᴴ.sortedSingularValues = A.sortedSingularValues := by
  funext i
  change (toEuclideanLin Aᴴ).singularValues i = (toEuclideanLin A).singularValues i
  rw [toEuclideanLin_conjTranspose, LinearMap.singularValues_adjoint]

/-- Scaling by `c` scales the stretch on a max–min subspace by `‖c‖`. -/
private theorem mul_sortedSingularValues_le_smul (c : 𝕜) (A : Matrix m n 𝕜) (i : ℕ) :
    ‖c‖ * A.sortedSingularValues i ≤ (c • A).sortedSingularValues i := by
  rcases (A.sortedSingularValues_nonneg i).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact sortedSingularValues_nonneg _ i
  have hk := (toEuclideanLin A).lt_finrank_of_singularValues_pos hpos
  obtain ⟨S, hS, h⟩ := ((toEuclideanLin A).isGreatest_singularValues hk).1
  refine (toEuclideanLin (c • A)).le_singularValues_of_mul_norm_le hS.ge fun x hx => ?_
  rw [map_smul, LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x hx) (norm_nonneg c)

/-- Singular values are absolutely homogeneous: `σ_i(c A) = ‖c‖ σ_i(A)`. -/
theorem sortedSingularValues_smul (c : 𝕜) (A : Matrix m n 𝕜) (i : ℕ) :
    (c • A).sortedSingularValues i = ‖c‖ * A.sortedSingularValues i := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, norm_zero, zero_mul]
    change (toEuclideanLin (0 : Matrix m n 𝕜)).singularValues i = 0
    rw [map_zero, LinearMap.singularValues_zero]
    rfl
  refine le_antisymm ?_ (mul_sortedSingularValues_le_smul c A i)
  have h := mul_sortedSingularValues_le_smul c⁻¹ (c • A) i
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at h
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  calc (c • A).sortedSingularValues i
      = ‖c‖ * (‖c‖⁻¹ * (c • A).sortedSingularValues i) := by field_simp
    _ ≤ ‖c‖ * A.sortedSingularValues i := mul_le_mul_of_nonneg_left h hc'.le

/-- **Weyl's inequality for sorted singular values** ([golub2013matrix] Corollary 2.4.4 and
Theorem 8.6.2's `σ_{i+j}(A + B) ≤ σ_i(A) + σ_j(B)`), the matrix form of
`LinearMap.singularValues_add_le`. -/
theorem sortedSingularValues_add_le (A B : Matrix m n 𝕜) (i j : ℕ) :
    (A + B).sortedSingularValues (i + j) ≤ A.sortedSingularValues i + B.sortedSingularValues j := by
  change (toEuclideanLin (A + B)).singularValues (i + j) ≤ _
  rw [show toEuclideanLin (A + B) = toEuclideanLin A + toEuclideanLin B from map_add _ _ _]
  exact LinearMap.singularValues_add_le _ _ i j

open scoped Matrix.Norms.Frobenius in
/-- **The squared Frobenius norm is the sum of the squared sorted singular values**
([golub2013matrix] (2.4.7)): `‖A‖_F² = ∑_{i < card n} σ_i(A)²`, the column-indexed
`Matrix.frobenius_norm_sq_eq_sum_sq_colSingularValues` read through the relabelling
`Matrix.exists_equiv_colSingularValues_eq_sortedSingularValues`. -/
theorem frobenius_norm_sq_eq_sum_sq_sortedSingularValues (A : Matrix m n 𝕜) :
    ‖A‖ ^ 2 = ∑ i ∈ Finset.range (Fintype.card n), A.sortedSingularValues i ^ 2 := by
  obtain ⟨e, he⟩ := A.exists_equiv_colSingularValues_eq_sortedSingularValues
  rw [frobenius_norm_sq_eq_sum_sq_colSingularValues, ← e.sum_comp,
    ← Fin.sum_univ_eq_sum_range (fun i => A.sortedSingularValues i ^ 2)]
  exact Finset.sum_congr rfl fun k _ => by rw [he]

/-- **Weyl's perturbation bound** ([golub2013matrix] Corollary 8.6.2):
`|σ_i(A + B) − σ_i(A)| ≤ σ_0(B) = ‖B‖₂`, from `Matrix.sortedSingularValues_add_le` in both
directions. -/
theorem abs_sortedSingularValues_add_sub_le (A B : Matrix m n 𝕜) (i : ℕ) :
    |(A + B).sortedSingularValues i - A.sortedSingularValues i| ≤ B.sortedSingularValues 0 := by
  have h1 := sortedSingularValues_add_le A B i 0
  have h2 := sortedSingularValues_add_le (A + B) (-B) i 0
  rw [add_zero] at h1
  rw [add_neg_cancel_right, add_zero] at h2
  have hneg : (-B).sortedSingularValues 0 = B.sortedSingularValues 0 := by
    rw [← neg_one_smul 𝕜 B, sortedSingularValues_smul, norm_neg, norm_one, one_mul]
  rw [hneg] at h2
  rw [abs_le]
  constructor <;> linarith

open scoped Matrix.Norms.Frobenius in
/-- The largest singular value is at most the Frobenius norm, `σ_0(A) = ‖A‖₂ ≤ ‖A‖_F`. -/
theorem sortedSingularValues_zero_le_frobenius_norm (A : Matrix m n 𝕜) :
    A.sortedSingularValues 0 ≤ ‖A‖ := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · rw [A.sortedSingularValues_eq_zero_of_min_le (by omega)]
    exact norm_nonneg _
  · refine (pow_le_pow_iff_left₀ (A.sortedSingularValues_nonneg 0) (norm_nonneg _)
      two_ne_zero).1 ?_
    rw [frobenius_norm_sq_eq_sum_sq_sortedSingularValues]
    exact Finset.single_le_sum (f := fun i => A.sortedSingularValues i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_range.2 hpos)

open scoped Matrix.Norms.Frobenius in
/-- **Weyl's perturbation bound in the Frobenius norm**: `|σ_i(A + B) − σ_i(A)| ≤ ‖B‖_F`. -/
theorem abs_sortedSingularValues_add_sub_le_frobenius_norm (A B : Matrix m n 𝕜) (i : ℕ) :
    |(A + B).sortedSingularValues i - A.sortedSingularValues i| ≤ ‖B‖ :=
  (abs_sortedSingularValues_add_sub_le A B i).trans (sortedSingularValues_zero_le_frobenius_norm B)

end Basic

/-! ### The Hermitian dilation -/

section Dilation

variable {m n : Type*}

/-- **The Hermitian dilation** (Jordan–Wielandt matrix) of `A : Matrix m n α`: the square block
matrix `[0 Aᴴ; A 0]` on `n ⊕ m`, domain block first. It is the matrix `S₃ = [0 Aᵀ; A 0]` of
[golub2013matrix] §8.6.1 and `Ã` of (8.6.4); the book's `[0 A; Aᴴ 0]` of (10.4.16) and §9.4.3 is
`hermitianDilation Aᴴ`. Its operator is `LinearMap.hermitianDilation`
(`Matrix.toEuclideanLin_hermitianDilation`), and its spectrum is `±` the singular values of `A`
padded by zeros (`Matrix.IsHermitian.eigenvalues₀_hermitianDilation`). -/
def hermitianDilation {α : Type*} [Zero α] [Star α] (A : Matrix m n α) :
    Matrix (n ⊕ m) (n ⊕ m) α :=
  fromBlocks 0 Aᴴ A 0

/-- The Hermitian dilation is Hermitian. -/
theorem isHermitian_hermitianDilation {α : Type*} [AddMonoid α] [StarAddMonoid α]
    (A : Matrix m n α) : (hermitianDilation A).IsHermitian :=
  isHermitian_zero.fromBlocks (conjTranspose_conjTranspose A) isHermitian_zero

/-- The Hermitian dilation is additive. -/
theorem hermitianDilation_add {α : Type*} [AddMonoid α] [StarAddMonoid α] (A B : Matrix m n α) :
    hermitianDilation (A + B) = hermitianDilation A + hermitianDilation B := by
  simp only [hermitianDilation, fromBlocks_add, conjTranspose_add, add_zero]

open scoped Matrix.Norms.Frobenius in
/-- The dilation carries each entry of `A` twice: `‖hermitianDilation A‖_F² = 2 ‖A‖_F²`. -/
theorem frobenius_norm_hermitianDilation_sq [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    ‖hermitianDilation A‖ ^ 2 = 2 * ‖A‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq]
  simp only [hermitianDilation, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, zero_apply, norm_zero, conjTranspose_apply,
    norm_star, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    zero_add, add_zero]
  rw [Finset.sum_comm]
  ring

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **The matrix of the Jordan–Wielandt operator**: `toEuclideanLin (hermitianDilation A)` is the
operator `LinearMap.hermitianDilation (toEuclideanLin A) (toEuclideanLin Aᴴ)` on
`WithLp 2 (EuclideanSpace 𝕜 n × EuclideanSpace 𝕜 m)`, conjugated by the isometry
`PiLp.sumPiLpEquivProdLpPiLp` that splits a vector on `n ⊕ m` into its two blocks. -/
theorem toEuclideanLin_hermitianDilation (A : Matrix m n 𝕜) :
    toEuclideanLin (hermitianDilation A) =
      (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := 𝕜) 2 fun _ : n ⊕ m => 𝕜).symm.toLinearEquiv.toLinearMap
        ∘ₗ LinearMap.hermitianDilation (toEuclideanLin A) (toEuclideanLin Aᴴ) ∘ₗ
          (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := 𝕜) 2 fun _ : n ⊕ m => 𝕜).toLinearEquiv.toLinearMap
      := by
  refine LinearMap.ext fun x => ?_
  ext i
  rcases i with j | j <;>
    simp [toEuclideanLin_apply, hermitianDilation, mulVec, dotProduct, Fintype.sum_sum_type] <;>
    rfl

/-- **The spectrum of the Hermitian dilation** ([golub2013matrix] (8.6.3)): the sorted eigenvalues
of `hermitianDilation A` (of size `N = card n + card m`) are `λ_i = σ_i - σ_{N-1-i}`, that is
`σ_0, …, σ_{p-1}`, then `N - 2p` zeros, then `-σ_{p-1}, …, -σ_0`, where `p = min (card m) (card n)`
(at most one of the two terms is nonzero). The operator statement
`LinearMap.eigenvalues_hermitianDilation`, transported along the isometry of
`Matrix.toEuclideanLin_hermitianDilation`, which preserves the characteristic polynomial. -/
theorem IsHermitian.eigenvalues₀_hermitianDilation {A : Matrix m n 𝕜}
    (hA : (hermitianDilation A).IsHermitian) (i : Fin (Fintype.card (n ⊕ m))) :
    hA.eigenvalues₀ i =
      A.sortedSingularValues i - A.sortedSingularValues (Fintype.card (n ⊕ m) - 1 - i) := by
  have hN : finrank 𝕜 (WithLp 2 (EuclideanSpace 𝕜 n × EuclideanSpace 𝕜 m)) =
      Fintype.card (n ⊕ m) := by
    rw [(WithLp.linearEquiv 2 𝕜 (EuclideanSpace 𝕜 n × EuclideanSpace 𝕜 m)).finrank_eq,
      Module.finrank_prod, finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_sum]
  have hcp : (toEuclideanLin (hermitianDilation A)).charpoly =
      (LinearMap.hermitianDilation (toEuclideanLin A)
        (LinearMap.adjoint (toEuclideanLin A))).charpoly := by
    rw [← (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := 𝕜) 2
        fun _ : n ⊕ m => 𝕜).toLinearEquiv.symm.charpoly_conj, LinearEquiv.symm_conj_apply,
      toEuclideanLin_hermitianDilation, toEuclideanLin_conjTranspose]
    rfl
  have heq := (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff
    (isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace
    (toEuclideanLin A).isSymmetric_hermitianDilation_adjoint hN).2 hcp
  rw [IsHermitian.eigenvalues₀, heq]
  exact (toEuclideanLin A).eigenvalues_hermitianDilation hN i

end Dilation

/-- **The reflected pairing**: if `a` and `b` vanish from `p` on and `2 p ≤ N`, then
`∑_{k < N} (a_k - a_{N-1-k}) (b_k - b_{N-1-k}) = 2 ∑_{k < p} a_k b_k`, the two halves of each
factor never being nonzero together. This is how the spectra of two dilations pair up. -/
private theorem sum_range_sub_reflect_mul_sub_reflect {N p : ℕ} (hp : 2 * p ≤ N) {a b : ℕ → ℝ}
    (ha : ∀ k, p ≤ k → a k = 0) (hb : ∀ k, p ≤ k → b k = 0) :
    ∑ k ∈ Finset.range N, (a k - a (N - 1 - k)) * (b k - b (N - 1 - k)) =
      2 * ∑ k ∈ Finset.range p, a k * b k := by
  have hexp : ∀ k ∈ Finset.range N, (a k - a (N - 1 - k)) * (b k - b (N - 1 - k)) =
      a k * b k + a (N - 1 - k) * b (N - 1 - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rcases lt_or_ge k p with h | h
    · rw [ha (N - 1 - k) (by omega), hb (N - 1 - k) (by omega)]
      ring
    · rw [ha k h, hb k h]
      ring
  have hrefl := Finset.sum_range_reflect (fun k => a k * b k) N
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, hrefl]
  have hsplit : ∑ k ∈ Finset.range N, a k * b k = ∑ k ∈ Finset.range p, a k * b k := by
    refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k _ hk => ?_).symm
    rw [Finset.mem_range, not_lt] at hk
    rw [ha k hk, zero_mul]
  rw [hsplit]
  ring

/-- The size of a dilation is at least twice the number of singular values. -/
private theorem two_mul_min_le_card_sum {m n : Type*} [Fintype m] [Fintype n] :
    2 * min (Fintype.card m) (Fintype.card n) ≤ Fintype.card (n ⊕ m) := by
  rw [Fintype.card_sum]
  omega

/-! ### Mirsky's inequality and the Eckart–Young lower bounds -/

section Mirsky

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius in
/-- **Mirsky's inequality**, the Wielandt–Hoffman theorem for singular values ([golub2013matrix]
Theorem 8.6.4): `∑_{k < min(m, n)} (σ_k(A + E) - σ_k(A))² ≤ ‖E‖_F²`. The Hoffman–Wielandt
inequality `Matrix.IsHermitian.hoffman_wielandt` for the dilations of `A + E` and `A`, whose sorted
eigenvalue differences are `±(σ_k(A + E) - σ_k(A))` and zeros
(`Matrix.IsHermitian.eigenvalues₀_hermitianDilation`), counts the left side twice and the right
side as `‖hermitianDilation E‖_F² = 2 ‖E‖_F²`. -/
theorem sum_sq_sortedSingularValues_sub_le (A E : Matrix m n 𝕜) :
    ∑ k ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      ((A + E).sortedSingularValues k - A.sortedSingularValues k) ^ 2 ≤ ‖E‖ ^ 2 := by
  classical
  set p := min (Fintype.card m) (Fintype.card n) with hp
  set d : ℕ → ℝ := fun k => (A + E).sortedSingularValues k - A.sortedSingularValues k with hd
  have hd0 : ∀ k, p ≤ k → d k = 0 := fun k hk => by
    simp only [hd, sortedSingularValues_eq_zero_of_min_le _ hk, sub_self]
  have hHW := (isHermitian_hermitianDilation (A + E)).hoffman_wielandt
    (isHermitian_hermitianDilation A)
  have hF : ‖hermitianDilation (A + E) - hermitianDilation A‖ ^ 2 = 2 * ‖E‖ ^ 2 := by
    rw [hermitianDilation_add, add_sub_cancel_left, frobenius_norm_hermitianDilation_sq]
  have hL : ∑ k, ((isHermitian_hermitianDilation (A + E)).eigenvalues₀ k -
      (isHermitian_hermitianDilation A).eigenvalues₀ k) ^ 2 =
        2 * ∑ k ∈ Finset.range p, d k * d k := by
    have h := sum_range_sub_reflect_mul_sub_reflect (two_mul_min_le_card_sum (m := m) (n := n))
      hd0 hd0
    rw [Finset.sum_range] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [IsHermitian.eigenvalues₀_hermitianDilation, IsHermitian.eigenvalues₀_hermitianDilation]
    simp only [hd]
    ring
  have hsum : ∑ k ∈ Finset.range p, d k * d k = ∑ k ∈ Finset.range p,
      ((A + E).sortedSingularValues k - A.sortedSingularValues k) ^ 2 :=
    Finset.sum_congr rfl fun k _ => by simp only [hd]; ring
  have := hHW.trans_eq hF
  rw [hL, hsum] at this
  linarith

/-! ### The Eckart–Young theorem -/

open scoped Matrix.Norms.L2Operator in
/-- **The lower half of the Eckart–Young theorem in the `2`-norm** ([golub2013matrix] proof of
Theorem 2.4.8): if `rank B ≤ k` then `σ_k(A) ≤ ‖A - B‖₂`. Weyl's inequality for `A = (A - B) + B`
gives `σ_k(A) ≤ σ_0(A - B) + σ_k(B)`, with `σ_0(A - B) = ‖A - B‖₂` and `σ_k(B) = 0`; the book's
kernel-intersection argument is the proof of Weyl's inequality. -/
theorem sortedSingularValues_le_l2_opNorm_sub_of_rank_le {A B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : A.sortedSingularValues k ≤ ‖A - B‖ := by
  have h := sortedSingularValues_add_le (A - B) B 0 k
  rw [zero_add, sub_add_cancel, (B.sortedSingularValues_eq_zero_iff_rank_le k).2 hB, add_zero,
    sortedSingularValues_zero_eq_l2_opNorm] at h
  exact h

open scoped Matrix.Norms.Frobenius in
/-- **The lower half of the Eckart–Young–Mirsky theorem in the Frobenius norm** ([golub2013matrix]
§2.4, the remark after Theorem 2.4.8, used in Theorem 6.3.1): if `rank Ĉ ≤ r` then
`∑_{r ≤ i < min(m, n)} σ_i(C)² ≤ ‖C - Ĉ‖_F²`. Mirsky's inequality for `Ĉ` and `C - Ĉ`, whose
terms `σ_i(Ĉ)` vanish for `i ≥ r`, the terms `i < r` being dropped. -/
theorem sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le {C Ĉ : Matrix m n 𝕜}
    {r : ℕ} (h : Ĉ.rank ≤ r) :
    ∑ i ∈ Finset.Ico r (min (Fintype.card m) (Fintype.card n)), C.sortedSingularValues i ^ 2 ≤
      ‖C - Ĉ‖ ^ 2 := by
  have hM := sum_sq_sortedSingularValues_sub_le Ĉ (C - Ĉ)
  rw [add_sub_cancel] at hM
  refine le_trans ?_ hM
  calc ∑ i ∈ Finset.Ico r (min (Fintype.card m) (Fintype.card n)), C.sortedSingularValues i ^ 2
      = ∑ i ∈ Finset.Ico r (min (Fintype.card m) (Fintype.card n)),
          (C.sortedSingularValues i - Ĉ.sortedSingularValues i) ^ 2 :=
        Finset.sum_congr rfl fun i hi => by
          rw [(Ĉ.sortedSingularValues_eq_zero_iff_rank_le i).2
            (h.trans (Finset.mem_Ico.1 hi).1), sub_zero]
    _ ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
          (C.sortedSingularValues i - Ĉ.sortedSingularValues i) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_subset_Ico_left (Nat.zero_le r)

end Mirsky

section Truncation

variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜} {σ : ℕ → ℝ}
  {V : Matrix (Fin n) (Fin n) 𝕜}

/-- **A truncated SVD has rank at most `k`**, whatever the factors: `U Σ_k Vᴴ` has at most `k`
nonzero diagonal entries in its middle factor (`Matrix.rank_svdTruncation` is the equality for
`k ≤ rank A`). -/
theorem rank_svdTruncation_le (U : Matrix (Fin m) (Fin m) 𝕜) (σ : ℕ → ℝ)
    (V : Matrix (Fin n) (Fin n) 𝕜) (k : ℕ) : (svdTruncation U σ V k).rank ≤ k := by
  classical
  refine (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans ?_)
  rw [rank_rectDiagonal]
  have hlt : ∀ j : {j : Fin n // (j : ℕ) < m ∧
      (if (j : ℕ) < k then ((σ j : ℝ) : 𝕜) else 0) ≠ 0}, (j.1 : ℕ) < k := fun j => by
    by_contra hjk
    exact j.2.2 (by rw [ite_eq_right hjk])
  refine (Fintype.card_le_of_injective (fun j => (⟨j.1, hlt j⟩ : Fin k)) fun a b hab => ?_).trans_eq
    (Fintype.card_fin k)
  exact Subtype.ext (Fin.ext (Fin.mk.inj_iff.1 hab))

/-- **The residual of a truncated SVD**: `A - A_k = U Σ' Vᴴ` with `Σ'` the diagonal of the
trailing singular values `σ_i`, `i ≥ k`. -/
theorem IsSVD.sub_svdTruncation (h : IsSVD A U σ V) (k : ℕ) :
    A - svdTruncation U σ V k =
      U * (rectDiagonal (fun i => if i < k then 0 else ((σ i : ℝ) : 𝕜)) :
        Matrix (Fin m) (Fin n) 𝕜) * star V := by
  conv_lhs => rw [h.eq_mul_mul_star]
  rw [svdTruncation, ← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  ext i j
  simp only [sub_apply, rectDiagonal_apply]
  split_ifs <;> simp

open scoped Matrix.Norms.L2Operator in
/-- **The `2`-norm of a truncation residual** ([golub2013matrix] proof of Theorem 2.4.8, first
paragraph): `‖A - A_k‖₂ = σ_k(A)`, by unitary invariance and `Matrix.l2_opNorm_rectDiagonal`, the
largest trailing singular value being `σ_k` (or `0 = σ_k` when `k ≥ min m n`). -/
theorem l2_opNorm_sub_svdTruncation (h : IsSVD A U σ V) (k : ℕ) :
    ‖A - svdTruncation U σ V k‖ = A.sortedSingularValues k := by
  rw [h.sub_svdTruncation, l2_opNorm_unitary_mul_mul_unitary h.mem_unitaryGroup_left _
    (Unitary.star_mem h.mem_unitaryGroup_right), l2_opNorm_rectDiagonal]
  apply le_antisymm
  · refine Real.iSup_le (fun i => ?_) (A.sortedSingularValues_nonneg k)
    have hi := i.isLt
    split_ifs with hik
    · rw [norm_zero]
      exact A.sortedSingularValues_nonneg k
    · rw [RCLike.norm_ofReal, abs_of_nonneg (h.nonneg i),
        ← h.singularValues_eq (i := k) (by omega) (by omega)]
      exact h.antitone (not_lt.1 hik)
  · rcases lt_or_ge k (min m n) with hk | hk
    · refine le_trans ?_ (le_ciSup (Set.finite_range _).bddAbove ⟨k, hk⟩)
      dsimp only
      rw [ite_eq_right (lt_irrefl k), RCLike.norm_ofReal, abs_of_nonneg (h.nonneg k),
        h.singularValues_eq (by omega) (by omega)]
    · rw [sortedSingularValues_eq_zero_of_min_le A (by simpa using hk)]
      exact Real.iSup_nonneg fun i => norm_nonneg _

open scoped Matrix.Norms.Frobenius in
/-- The squared Frobenius norm of a rectangular diagonal matrix is the sum of the squared moduli of
its visible diagonal entries. -/
theorem frobenius_norm_rectDiagonal_sq (d : ℕ → 𝕜) :
    ‖(rectDiagonal d : Matrix (Fin m) (Fin n) 𝕜)‖ ^ 2 =
      ∑ i ∈ Finset.range (min m n), ‖d i‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq]
  have hrow : ∀ i : Fin m, ∑ j : Fin n, ‖(rectDiagonal d : Matrix (Fin m) (Fin n) 𝕜) i j‖ ^ 2 =
      if (i : ℕ) < n then ‖d i‖ ^ 2 else 0 := by
    intro i
    simp only [rectDiagonal_apply]
    split_ifs with hi
    · rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp
      · intro j _ hj
        rw [ite_eq_right (fun h => hj (Fin.ext h.symm)), norm_zero, zero_pow two_ne_zero]
      · simp
    · refine Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right (fun (h : (i : ℕ) = j) => hi (h ▸ j.isLt)), norm_zero,
        zero_pow two_ne_zero]
  rw [Finset.sum_congr rfl fun i _ => hrow i,
    Fin.sum_univ_eq_sum_range (fun i => if i < n then ‖d i‖ ^ 2 else 0) m, ← Finset.sum_filter]
  congr 1
  ext i
  simp [lt_min_iff]

open scoped Matrix.Norms.Frobenius in
/-- **The Frobenius norm of a truncation residual** ([golub2013matrix] §2.4.2):
`‖A - A_k‖_F = √(σ_k² + ⋯ + σ_{p-1}²)`, `p = min m n`, by unitary invariance and
`Matrix.frobenius_norm_rectDiagonal_sq`. -/
theorem frobenius_norm_sub_svdTruncation (h : IsSVD A U σ V) (k : ℕ) :
    ‖A - svdTruncation U σ V k‖ =
      √(∑ i ∈ Finset.Ico k (min m n), A.sortedSingularValues i ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), h.sub_svdTruncation, frobenius_norm_unitary_mul_mul_unitary
    h.mem_unitaryGroup_left _ (Unitary.star_mem h.mem_unitaryGroup_right),
    frobenius_norm_rectDiagonal_sq]
  congr 1
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (min k (min m n)))
    (min_le_right k (min m n))]
  have h1 : ∀ i ∈ Finset.Ico 0 (min k (min m n)),
      ‖(if i < k then (0 : 𝕜) else ((σ i : ℝ) : 𝕜))‖ ^ 2 = 0 := fun i hi => by
    rw [ite_eq_left (lt_of_lt_of_le (Finset.mem_Ico.1 hi).2 (min_le_left _ _)), norm_zero,
      zero_pow two_ne_zero]
  rw [Finset.sum_eq_zero h1, zero_add]
  rcases le_total k (min m n) with hk | hk
  · rw [min_eq_left hk]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hki, him⟩ := Finset.mem_Ico.1 hi
    rw [ite_eq_right (not_lt.2 hki), RCLike.norm_ofReal, sq_abs,
      h.singularValues_eq (by omega) (by omega)]
  · rw [min_eq_right hk, Finset.Ico_self, Finset.Ico_eq_empty_of_le hk]
    simp

end Truncation

section EckartYoungIsLeast

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Subtracting a matrix read back from `Fin` indices. -/
private theorem sub_submatrix_equivFin (A : Matrix m n 𝕜)
    (B : Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) 𝕜) :
    A - B.submatrix (Fintype.equivFin m) (Fintype.equivFin n) =
      (A.submatrix (Fintype.equivFin m).symm (Fintype.equivFin n).symm - B).submatrix
        (Fintype.equivFin m) (Fintype.equivFin n) := by
  ext i j
  simp

omit [DecidableEq n] in
/-- The attainment step of both Eckart–Young theorems: an SVD of `A` read on `Fin` indices, and the
truncation `B` of rank at most `k` read back, with `A - B` the reindexed truncation residual. -/
private theorem exists_rank_le_eq_svdTruncation_submatrix (A : Matrix m n 𝕜) (k : ℕ) :
    ∃ (U : Matrix (Fin (Fintype.card m)) (Fin (Fintype.card m)) 𝕜) (σ : ℕ → ℝ)
      (V : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) 𝕜),
      IsSVD (A.submatrix (Fintype.equivFin m).symm (Fintype.equivFin n).symm) U σ V ∧
      ∃ B : Matrix m n 𝕜, B.rank ≤ k ∧ A - B =
        (A.submatrix (Fintype.equivFin m).symm (Fintype.equivFin n).symm -
          svdTruncation U σ V k).submatrix (Fintype.equivFin m) (Fintype.equivFin n) := by
  obtain ⟨U, σ, V, h⟩ :=
    exists_isSVD (A.submatrix (Fintype.equivFin m).symm (Fintype.equivFin n).symm)
  refine ⟨U, σ, V, h, (svdTruncation U σ V k).submatrix (Fintype.equivFin m)
    (Fintype.equivFin n), ?_, sub_submatrix_equivFin A _⟩
  rw [rank_submatrix]
  exact rank_svdTruncation_le U σ V k

open scoped Matrix.Norms.L2Operator in
/-- **The Eckart–Young theorem in the `2`-norm** ([golub2013matrix] Theorem 2.4.8): the distance
from `A` to the matrices of rank at most `k` is `σ_k(A)`, attained at the truncation of any SVD
(for the book's `rank B = k` form, the truncation of an SVD at `k ≤ rank A` has rank exactly `k`,
`Matrix.rank_svdTruncation`). At `k = min m n - 1` it says that `σ_min` is the distance to the
rank-deficient matrices. -/
theorem isLeast_l2_opNorm_sub_of_rank_le (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast ((fun B => ‖A - B‖) '' {B | B.rank ≤ k}) (A.sortedSingularValues k) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨U, σ, V, h, B, hB, hAB⟩ := exists_rank_le_eq_svdTruncation_submatrix A k
    refine ⟨B, hB, ?_⟩
    dsimp only
    rw [hAB, l2_opNorm_submatrix_equiv, l2_opNorm_sub_svdTruncation h,
      sortedSingularValues_submatrix_equiv]
  · rintro _ ⟨B, hB, rfl⟩
    exact sortedSingularValues_le_l2_opNorm_sub_of_rank_le hB

open scoped Matrix.Norms.Frobenius in
/-- **The Eckart–Young–Mirsky theorem in the Frobenius norm** ([golub2013matrix] §2.4.2, the
remark after Theorem 2.4.8, stated there without proof): the distance from `A` to the matrices of
rank at most `k` is `√(σ_k² + ⋯ + σ_{p-1}²)`, `p = min(m, n)`, attained at the truncation of any
SVD. Lower bound `Matrix.sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le`. -/
theorem isLeast_frobenius_norm_sub_of_rank_le (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast ((fun B => ‖A - B‖) '' {B | B.rank ≤ k})
      √(∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)),
        A.sortedSingularValues i ^ 2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨U, σ, V, h, B, hB, hAB⟩ := exists_rank_le_eq_svdTruncation_submatrix A k
    refine ⟨B, hB, ?_⟩
    dsimp only
    rw [hAB, frobenius_norm_submatrix_equiv, frobenius_norm_sub_svdTruncation h,
      sortedSingularValues_submatrix_equiv]
  · rintro _ ⟨B, hB, rfl⟩
    change _ ≤ ‖A - B‖
    rw [← Real.sqrt_sq (norm_nonneg (A - B))]
    exact Real.sqrt_le_sqrt (sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le hB)

end EckartYoungIsLeast

/-! ### Ky Fan's maximum principle and von Neumann's trace inequality -/

section KyFan

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Frobenius in
/-- **Ky Fan's maximum principle, SVD form** ([golub2013matrix] (12.5.3) and the sentence after
it): over the matrices `Q` with `r ≤ card m` orthonormal columns, the largest value of
`‖Qᴴ A‖_F²` is `σ_0² + ⋯ + σ_{r-1}²`, attained at the leading left singular vectors. With
`T = toEuclideanLin Aᴴ`, `‖Qᴴ A‖_F² = ‖Aᴴ Q‖_F² = ∑_j re ⟪T† T q_j, q_j⟫` over the columns `q_j` of
`Q`, and Ky Fan's principle for the symmetric `T† T`
(`LinearMap.IsSymmetric.sum_re_inner_le_sum_eigenvalues`), whose eigenvalues are the `σ_i²`,
bounds the sum, with equality at its leading eigenvectors. -/
theorem isGreatest_frobenius_norm_sq_conjTranspose_mul (A : Matrix m n 𝕜) {r : ℕ}
    (hr : r ≤ Fintype.card m) :
    IsGreatest ((fun Q : Matrix m (Fin r) 𝕜 => ‖Qᴴ * A‖ ^ 2) '' {Q | Qᴴ * Q = 1})
      (∑ i ∈ Finset.range r, A.sortedSingularValues i ^ 2) := by
  classical
  set T : EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 n := toEuclideanLin Aᴴ with hT
  have hn : finrank 𝕜 (EuclideanSpace 𝕜 m) = Fintype.card m := finrank_euclideanSpace
  have hS := T.isSymmetric_adjoint_comp_self
  have heig : ∀ i : Fin (Fintype.card m), hS.eigenvalues hn i = A.sortedSingularValues i ^ 2 := by
    intro i
    rw [← T.sq_singularValues_fin hn i]
    exact congrArg (· ^ 2) (congrFun (sortedSingularValues_conjTranspose A) i)
  have hsum : ∑ i : Fin r, hS.eigenvalues hn (Fin.castLE hr i) =
      ∑ i ∈ Finset.range r, A.sortedSingularValues i ^ 2 := by
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun i _ => heig _
  have hobj : ∀ Q : Matrix m (Fin r) 𝕜, ‖Qᴴ * A‖ ^ 2 =
      ∑ j, RCLike.re (inner 𝕜 ((LinearMap.adjoint T ∘ₗ T) (WithLp.toLp 2 (Qᵀ j)))
        (WithLp.toLp 2 (Qᵀ j))) := by
    intro Q
    rw [← frobenius_norm_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
      frobenius_norm_sq_eq_sum_norm_sq_col]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
    rfl
  refine ⟨?_, ?_⟩
  · set v := hS.eigenvectorBasis hn
    set Q : Matrix m (Fin r) 𝕜 := of fun a j => WithLp.ofLp (v (Fin.castLE hr j)) a with hQdef
    have hQ : Qᴴ * Q = 1 := by
      ext i j
      have h := orthonormal_iff_ite.1 (v.orthonormal.comp _ (Fin.castLE_injective hr)) i j
      rw [mul_apply, one_apply, ← h, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct, conjTranspose_apply, hQdef, of_apply, Pi.star_apply,
        Function.comp_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    refine ⟨Q, hQ, ?_⟩
    dsimp only
    rw [hobj, ← hsum, ← hS.sum_re_inner_eigenvectorBasis hn hr]
    rfl
  · rintro _ ⟨Q, hQ, rfl⟩
    dsimp only
    rw [hobj, ← hsum]
    exact hS.sum_re_inner_le_sum_eigenvalues hn
      (orthonormal_toLp_transpose_of_conjTranspose_mul_self_eq_one hQ) hr

/-- **Von Neumann's trace inequality, real part**: `re tr(A B) ≤ ∑_i σ_i(A) σ_i(B)`. The trace
inequality for two symmetric operators
(`LinearMap.IsSymmetric.re_trace_comp_le_sum_eigenvalues_mul`) applied to the dilations of `A` and
`Bᴴ`: `re tr(H(A) H(Bᴴ)) = 2 re tr(A B)`, and the sorted spectra `±σ(A)`, `±σ(B)` of the
dilations pair up to `2 ∑ σ_i(A) σ_i(B)`. -/
theorem re_trace_mul_le_sum_sortedSingularValues_mul [DecidableEq m] (A : Matrix m n 𝕜)
    (B : Matrix n m 𝕜) :
    RCLike.re (trace (A * B)) ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      A.sortedSingularValues i * B.sortedSingularValues i := by
  have hH1 := isHermitian_hermitianDilation A
  have hH2 := isHermitian_hermitianDilation Bᴴ
  have key := LinearMap.IsSymmetric.re_trace_comp_le_sum_eigenvalues_mul finrank_euclideanSpace
    (isSymmetric_toEuclideanLin_iff.mpr hH1) (isSymmetric_toEuclideanLin_iff.mpr hH2)
  have htr : LinearMap.trace 𝕜 _ (toEuclideanLin (hermitianDilation A) ∘ₗ
      toEuclideanLin (hermitianDilation Bᴴ)) =
        trace (hermitianDilation A * hermitianDilation Bᴴ) := by
    rw [← toEuclideanLin_mul, toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]
  have hblock : trace (hermitianDilation A * hermitianDilation Bᴴ) =
      trace (Aᴴ * Bᴴ) + trace (A * B) := by
    simp only [hermitianDilation, fromBlocks_multiply, conjTranspose_conjTranspose,
      Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, trace, Fintype.sum_sum_type,
      diag_apply, fromBlocks_apply₁₁, fromBlocks_apply₂₂]
  have hconj : trace (Aᴴ * Bᴴ) = star (trace (A * B)) := by
    rw [← conjTranspose_mul, trace_conjTranspose, trace_mul_comm]
  rw [htr, hblock, hconj, map_add, RCLike.star_def, RCLike.conj_re] at key
  have hp : ∀ k, min (Fintype.card n) (Fintype.card m) ≤ k → B.sortedSingularValues k = 0 :=
    fun k hk => B.sortedSingularValues_eq_zero_of_min_le hk
  have hrefl := sum_range_sub_reflect_mul_sub_reflect (two_mul_min_le_card_sum (m := m) (n := n))
    (fun k hk => A.sortedSingularValues_eq_zero_of_min_le hk)
    (fun k hk => hp k (by rwa [min_comm]))
  rw [Finset.sum_range] at hrefl
  have hsum : ∑ i, (isSymmetric_toEuclideanLin_iff.mpr hH1).eigenvalues finrank_euclideanSpace i *
      (isSymmetric_toEuclideanLin_iff.mpr hH2).eigenvalues finrank_euclideanSpace i =
        2 * ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
          A.sortedSingularValues i * B.sortedSingularValues i := by
    rw [← hrefl]
    refine Finset.sum_congr rfl fun i _ => ?_
    change hH1.eigenvalues₀ i * hH2.eigenvalues₀ i = _
    rw [IsHermitian.eigenvalues₀_hermitianDilation, IsHermitian.eigenvalues₀_hermitianDilation,
      sortedSingularValues_conjTranspose]
  linarith

/-- **Von Neumann's trace inequality** (von Neumann 1937): for `A : Matrix m n 𝕜` and
`B : Matrix n m 𝕜`, `|tr(A B)| ≤ ∑_{i < min(m, n)} σ_i(A) σ_i(B)`. The real-part form
`Matrix.re_trace_mul_le_sum_sortedSingularValues_mul` applied to `c A` with the phase
`c = conj(tr(A B)) / |tr(A B)|`, which does not change the singular values. The one-sided
Procrustes bound is the case of a unitary factor, all of whose singular values are `1`. -/
theorem norm_trace_mul_le_sum_sortedSingularValues_mul [DecidableEq m] (A : Matrix m n 𝕜)
    (B : Matrix n m 𝕜) :
    ‖trace (A * B)‖ ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      A.sortedSingularValues i * B.sortedSingularValues i := by
  set z := trace (A * B) with hz
  rcases eq_or_ne z 0 with hz0 | hz0
  · rw [hz0, norm_zero]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (A.sortedSingularValues_nonneg i) (B.sortedSingularValues_nonneg i)
  set c : 𝕜 := star z / ((‖z‖ : ℝ) : 𝕜) with hc
  have hz' : ((‖z‖ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz0)
  have hcn : ‖c‖ = 1 := by
    rw [hc, norm_div, norm_star, RCLike.norm_ofReal, abs_norm, div_self (norm_ne_zero_iff.2 hz0)]
  have hcz : c * z = ((‖z‖ : ℝ) : 𝕜) := by
    rw [hc, div_mul_eq_mul_div, RCLike.star_def, RCLike.conj_mul, div_eq_iff hz']
    ring
  have h := re_trace_mul_le_sum_sortedSingularValues_mul (c • A) B
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul, ← hz, hcz, RCLike.ofReal_re] at h
  simpa only [sortedSingularValues_smul, hcn, one_mul] using h

end KyFan

/-! ### Deleting blocks -/

section Blocks

variable {m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

/-- **Deleting a trailing column block does not increase any singular value** ([golub2013matrix]
Corollary 8.6.3 iterated, and the step `σ_n(C) ≥ σ_n(C₁)` of Theorem 6.3.1):
`σ_i(C₁) ≤ σ_i([C₁ C₂])`, `Matrix.sortedSingularValues_submatrix_le` along `Sum.inl`. -/
theorem sortedSingularValues_fromCols_left_le [DecidableEq n] [DecidableEq k] (C₁ : Matrix m n 𝕜)
    (C₂ : Matrix m k 𝕜) (i : ℕ) :
    C₁.sortedSingularValues i ≤ (fromCols C₁ C₂).sortedSingularValues i := by
  have h : C₁ = (fromCols C₁ C₂).submatrix id Sum.inl := by
    ext a b
    simp
  conv_lhs => rw [h]
  exact sortedSingularValues_submatrix_le _ Function.injective_id Sum.inl_injective i

/-- **Deleting a leading column block does not increase any singular value**:
`σ_i(C₂) ≤ σ_i([C₁ C₂])`, the twin of `Matrix.sortedSingularValues_fromCols_left_le`. -/
theorem sortedSingularValues_fromCols_right_le [DecidableEq n] [DecidableEq k]
    (C₁ : Matrix m n 𝕜) (C₂ : Matrix m k 𝕜) (i : ℕ) :
    C₂.sortedSingularValues i ≤ (fromCols C₁ C₂).sortedSingularValues i := by
  have h : C₂ = (fromCols C₁ C₂).submatrix id Sum.inr := by
    ext a b
    simp
  conv_lhs => rw [h]
  exact sortedSingularValues_submatrix_le _ Function.injective_id Sum.inr_injective i

/-- **Deleting the bottom row block does not increase any singular value**:
`σ_i(R₁) ≤ σ_i([R₁; R₂])`, the row form of `Matrix.sortedSingularValues_fromCols_left_le`. -/
theorem sortedSingularValues_fromRows_left_le [DecidableEq n] (R₁ : Matrix m n 𝕜)
    (R₂ : Matrix l n 𝕜) (i : ℕ) :
    R₁.sortedSingularValues i ≤ (fromRows R₁ R₂).sortedSingularValues i := by
  have h : R₁ = (fromRows R₁ R₂).submatrix Sum.inl id := by
    ext a b
    simp
  conv_lhs => rw [h]
  exact sortedSingularValues_submatrix_le _ Sum.inl_injective Function.injective_id i

/-- **Deleting the top row block does not increase any singular value**:
`σ_i(R₂) ≤ σ_i([R₁; R₂])`. -/
theorem sortedSingularValues_fromRows_right_le [DecidableEq n] (R₁ : Matrix m n 𝕜)
    (R₂ : Matrix l n 𝕜) (i : ℕ) :
    R₂.sortedSingularValues i ≤ (fromRows R₁ R₂).sortedSingularValues i := by
  have h : R₂ = (fromRows R₁ R₂).submatrix Sum.inr id := by
    ext a b
    simp
  conv_lhs => rw [h]
  exact sortedSingularValues_submatrix_le _ Sum.inr_injective Function.injective_id i

open scoped Matrix.Norms.L2Operator in
/-- **A trailing block bounds a singular value** ([golub2013matrix] §5.4.3, and the `ρ` of
(5.4.10)): for a block upper triangular `R = [R₁₁ R₁₂; 0 R₂₂]` whose leading block row has
`card m` rows, `σ_{card m}(R) ≤ ‖R₂₂‖₂`. The leading block row has rank at most `card m`, and
`R` differs from it by `[0 0; 0 R₂₂]`, of norm at most `‖R₂₂‖₂`
(`Matrix.l2_opNorm_fromBlocks_le`); the lower half of Eckart–Young concludes. -/
theorem sortedSingularValues_le_l2_opNorm_trailing [DecidableEq n] [DecidableEq l]
    (R₁₁ : Matrix m n 𝕜) (R₁₂ : Matrix m l 𝕜) (R₂₂ : Matrix k l 𝕜) :
    (fromBlocks R₁₁ R₁₂ 0 R₂₂).sortedSingularValues (Fintype.card m) ≤ ‖R₂₂‖ := by
  classical
  have hrank : (fromBlocks R₁₁ R₁₂ (0 : Matrix k n 𝕜) 0).rank ≤ Fintype.card m := by
    have h : fromBlocks R₁₁ R₁₂ (0 : Matrix k n 𝕜) 0 =
        fromRows (1 : Matrix m m 𝕜) 0 * fromCols R₁₁ R₁₂ := by
      rw [fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
      ext (i | i) (j | j) <;> simp
    rw [h]
    exact (rank_mul_le_right _ _).trans (rank_le_card_height _)
  have h1 := sortedSingularValues_le_l2_opNorm_sub_of_rank_le
    (A := fromBlocks R₁₁ R₁₂ 0 R₂₂) hrank
  have hsub : fromBlocks R₁₁ R₁₂ 0 R₂₂ - fromBlocks R₁₁ R₁₂ 0 0 = fromBlocks 0 0 0 R₂₂ := by
    ext (i | i) (j | j) <;> simp
  rw [hsub] at h1
  refine h1.trans ((l2_opNorm_fromBlocks_le (μ := 0) (γ := 0) (by simp) (by simp) (by simp)
    le_rfl).trans_eq ?_)
  rw [show (0 - ‖R₂₂‖) ^ 2 + 4 * (0 : ℝ) ^ 2 = ‖R₂₂‖ ^ 2 by ring,
    Real.sqrt_sq (norm_nonneg _)]
  ring

open scoped Matrix.Norms.L2Operator in
/-- The lower triangular (ULV) form of `Matrix.sortedSingularValues_le_l2_opNorm_trailing`
([golub2013matrix] (5.4.11)): for `L = [L₁₁ 0; L₂₁ L₂₂]` whose leading block column has `card n`
columns, `σ_{card n}(L) ≤ ‖L₂₂‖₂`. The upper form for `Lᴴ`. -/
theorem sortedSingularValues_le_l2_opNorm_trailing_lower [DecidableEq n] [DecidableEq l]
    (L₁₁ : Matrix m n 𝕜) (L₂₁ : Matrix k n 𝕜) (L₂₂ : Matrix k l 𝕜) :
    (fromBlocks L₁₁ 0 L₂₁ L₂₂).sortedSingularValues (Fintype.card n) ≤ ‖L₂₂‖ := by
  classical
  have h := sortedSingularValues_le_l2_opNorm_trailing L₁₁ᴴ L₂₁ᴴ L₂₂ᴴ
  have e : fromBlocks L₁₁ᴴ L₂₁ᴴ (0 : Matrix l m 𝕜) L₂₂ᴴ = (fromBlocks L₁₁ 0 L₂₁ L₂₂)ᴴ := by
    rw [fromBlocks_conjTranspose, conjTranspose_zero]
  rwa [e, sortedSingularValues_conjTranspose, l2_opNorm_conjTranspose] at h

open scoped Matrix.Norms.L2Operator in
/-- **The least stretch is `1`-Lipschitz in the `2`-norm** ([golub2013matrix] Corollary 2.4.4 at the
last index): `|σ_min(A) - σ_min(B)| ≤ ‖A - B‖₂`, with `σ_min = ⨅ i, σ_i` over the columns (the least
stretch for every shape, `Matrix.iInf_colSingularValues_eq_iInf_norm`). Weyl's bound
`LinearMap.abs_singularValues_sub_le` at the last sorted index. (Column-indexed on purpose: the
consumers state `σ_min` as `⨅ i` over the columns.) -/
theorem abs_iInf_colSingularValues_sub_le [DecidableEq n] [Nonempty n] (A B : Matrix m n 𝕜) :
    |(⨅ i, A.colSingularValues i) - ⨅ i, B.colSingularValues i| ≤ ‖A - B‖ := by
  rw [← A.sortedSingularValues_eq_iInf_colSingularValues,
    ← B.sortedSingularValues_eq_iInf_colSingularValues]
  exact LinearMap.abs_singularValues_sub_le (S := toEuclideanLin B) (T := toEuclideanLin A)
    (norm_nonneg _) (fun x => by
      rw [LinearMap.sub_apply, ← toEuclideanLin_sub_apply]
      exact norm_toEuclideanLin_apply_le _ x) _

end Blocks

/-! ### Stability of full rank

A positive least stretch `σ_min(A) = ⨅ i, A.colSingularValues i` is the same as linearly
independent columns, and by Weyl's bound it survives a perturbation smaller than itself; the row
statements are those for `Aᴴ`. -/

section Stability

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator

/-- **Weyl stability of the least stretch** ([golub2013matrix] Corollary 2.4.4):
`σ_min(A) - ‖δA‖₂ ≤ σ_min(A + δA)`. -/
theorem sub_l2_opNorm_le_iInf_colSingularValues_add [Nonempty n] (A δA : Matrix m n 𝕜) :
    (⨅ i, A.colSingularValues i) - ‖δA‖ ≤ ⨅ i, (A + δA).colSingularValues i := by
  have h := abs_iInf_colSingularValues_sub_le (A + δA) A
  rw [add_sub_cancel_left] at h
  linarith [neg_abs_le ((⨅ i, (A + δA).colSingularValues i) - ⨅ i, A.colSingularValues i)]

/-- A perturbation smaller than the least stretch cannot happen without columns: `‖δA‖ < σ_min(A)`
forces `n` to be nonempty, since `σ_min` of a matrix without columns is `0`. -/
theorem nonempty_of_l2_opNorm_lt_iInf_colSingularValues {A δA : Matrix m n 𝕜}
    (h : ‖δA‖ < ⨅ i, A.colSingularValues i) : Nonempty n := by
  by_contra hn
  rw [not_nonempty_iff] at hn
  rw [Real.iInf_of_isEmpty] at h
  exact absurd h (not_lt.2 (norm_nonneg _))

/-- **A small perturbation keeps the columns independent**: `‖δA‖₂ < σ_min(A)` implies that
`A + δA` has linearly independent columns ([golub2013matrix] Theorem 2.5.2's use in the proof of
Theorem 5.3.1). -/
theorem linearIndependent_transpose_add_of_l2_opNorm_lt {A δA : Matrix m n 𝕜}
    (h : ‖δA‖ < ⨅ i, A.colSingularValues i) : LinearIndependent 𝕜 (A + δA)ᵀ := by
  have := nonempty_of_l2_opNorm_lt_iInf_colSingularValues h
  exact linearIndependent_transpose_of_iInf_colSingularValues_pos
    ((sub_pos.2 h).trans_le (sub_l2_opNorm_le_iInf_colSingularValues_add A δA))

/-- **Independent columns survive along a line**: if `A` has linearly independent columns, so has
`A + t E` for every `t` near `0`. -/
theorem eventually_linearIndependent_transpose_add_smul {m n : Type*} [Finite m] [Finite n]
    {A : Matrix m n 𝕜} (hA : LinearIndependent 𝕜 Aᵀ) (E : Matrix m n 𝕜) :
    ∀ᶠ t in nhds (0 : 𝕜), LinearIndependent 𝕜 (A + t • E)ᵀ := by
  classical
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Filter.Eventually.of_forall fun _ => linearIndependent_empty_type
  have hlim : Filter.Tendsto (fun t : 𝕜 => ‖t • E‖) (nhds 0) (nhds 0) := by
    have := ((continuous_id.smul (continuous_const (y := E))).norm).tendsto (0 : 𝕜)
    simpa using this
  filter_upwards [hlim.eventually_lt_const (iInf_colSingularValues_pos_of_linearIndependent hA)]
    with t ht
  exact linearIndependent_transpose_add_of_l2_opNorm_lt ht

variable [DecidableEq m]

/-- A small perturbation keeps the rows independent: `‖δA‖₂ < σ_min(Aᴴ)` implies that `A + δA` has
linearly independent rows. The column statement for `Aᴴ`, through `star (y ᵥ* M) = Mᴴ *ᵥ star y`. -/
theorem linearIndependent_add_of_l2_opNorm_lt {A δA : Matrix m n 𝕜}
    (h : ‖δA‖ < ⨅ i, Aᴴ.colSingularValues i) : LinearIndependent 𝕜 (A + δA) := by
  have h' : ‖δAᴴ‖ < ⨅ i, Aᴴ.colSingularValues i := by rwa [l2_opNorm_conjTranspose]
  have hc := linearIndependent_transpose_add_of_l2_opNorm_lt h'
  rw [← conjTranspose_add] at hc
  refine vecMul_injective_iff.1 fun v w hvw => ?_
  have h1 := congrArg star hvw
  rw [star_vecMul, star_vecMul] at h1
  exact star_injective (mulVec_injective_iff.2 hc h1)

/-- **Independent rows survive along a line**: if `A` has linearly independent rows, so has
`A + t E` for every `t` near `0`; the dual of
`Matrix.eventually_linearIndependent_transpose_add_smul`. -/
theorem eventually_linearIndependent_add_smul {m n : Type*} [Finite m] [Finite n]
    {A : Matrix m n 𝕜} (hA : LinearIndependent 𝕜 A) (E : Matrix m n 𝕜) :
    ∀ᶠ t in nhds (0 : 𝕜), LinearIndependent 𝕜 (A + t • E) := by
  classical
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  rcases isEmpty_or_nonempty m with hm | hm
  · exact Filter.Eventually.of_forall fun _ => linearIndependent_empty_type
  have hc : LinearIndependent 𝕜 Aᴴᵀ := by
    refine mulVec_injective_iff.1 fun v w hvw => ?_
    have e : ∀ u, Aᴴ *ᵥ u = star (star u ᵥ* A) := fun u => by rw [star_vecMul, star_star]
    rw [e, e] at hvw
    exact star_injective (vecMul_injective_iff.2 hA (star_injective hvw))
  have hlim : Filter.Tendsto (fun t : 𝕜 => ‖t • E‖) (nhds 0) (nhds 0) := by
    have := ((continuous_id.smul (continuous_const (y := E))).norm).tendsto (0 : 𝕜)
    simpa using this
  filter_upwards [hlim.eventually_lt_const (iInf_colSingularValues_pos_of_linearIndependent hc)]
    with t ht
  exact linearIndependent_add_of_l2_opNorm_lt ht

end Stability

/-! ### Stacked isometries and the distance between subspaces -/

section Stacked

variable {n k l : Type*} [Fintype n] [Fintype k] [Fintype l]

/-- The columns of `[Q₁; Q₂]` are orthonormal: `‖Q₁ x‖² + ‖Q₂ x‖² = ‖x‖²`. -/
private theorem norm_sq_add_norm_sq_of_stacked [DecidableEq n] {Q₁ : Matrix k n 𝕜}
    {Q₂ : Matrix l n 𝕜}
    (hQ : Q₁ᴴ * Q₁ + Q₂ᴴ * Q₂ = 1) (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin Q₁ x‖ ^ 2 + ‖toEuclideanLin Q₂ x‖ ^ 2 = ‖x‖ ^ 2 := by
  classical
  have h : inner 𝕜 (toEuclideanLin Q₁ x) (toEuclideanLin Q₁ x) +
      inner 𝕜 (toEuclideanLin Q₂ x) (toEuclideanLin Q₂ x) = inner 𝕜 x x := by
    rw [← toEuclideanLin_conjTranspose_inner_left, ← toEuclideanLin_conjTranspose_inner_left,
      ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, ← inner_add_left,
      ← LinearMap.add_apply, ← map_add, hQ, toEuclideanLin_one, LinearMap.id_apply]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

open scoped Matrix.Norms.L2Operator in
/-- **The stacked-isometry identity for matrices** ([golub2013matrix] proof of Theorem 2.5.1): if
the columns of `[Q₁; Q₂]` are orthonormal, `Q₁ᴴ Q₁ + Q₂ᴴ Q₂ = 1`, then
`‖Q₂‖₂² = 1 - σ_min(Q₁)²`, `σ_min` the last sorted singular value `σ_{card n - 1}`. The matrix
instance of `LinearMap.norm_toContinuousLinearMap_sq_eq_one_sub_sq_singularValues`. -/
theorem l2_opNorm_sq_eq_one_sub_sq_sortedSingularValues [DecidableEq n] [Nonempty n]
    {Q₁ : Matrix k n 𝕜}
    {Q₂ : Matrix l n 𝕜} (hQ : Q₁ᴴ * Q₁ + Q₂ᴴ * Q₂ = 1) :
    ‖Q₂‖ ^ 2 = 1 - Q₁.sortedSingularValues (Fintype.card n - 1) ^ 2 := by
  have hn : finrank 𝕜 (EuclideanSpace 𝕜 n) = Fintype.card n := finrank_euclideanSpace
  have h := LinearMap.norm_toContinuousLinearMap_sq_eq_one_sub_sq_singularValues
    (toEuclideanLin Q₁) (toEuclideanLin Q₂) (by rw [hn]; exact Fintype.card_pos)
    (norm_sq_add_norm_sq_of_stacked hQ)
  rw [hn] at h
  rw [l2_opNorm_def, LinearEquiv.trans_apply]
  exact h

open scoped Matrix.Norms.L2Operator in
/-- **The tan form of the stacked-isometry identity** ([golub2013matrix] §6.3.1,
`‖V₁₂ V₂₂⁻¹‖₂² = (1 - σ_k(V₂₂)²)/σ_k(V₂₂)²`): if `V₁₂ᴴ V₁₂ + V₂₂ᴴ V₂₂ = 1` and `V₂₂` is invertible,
with least singular value `s = σ_{card k - 1}(V₂₂)`, then `‖V₁₂ V₂₂⁻¹‖₂² = (1 - s²)/s²`. With
`y = V₂₂ w`, `‖V₁₂ V₂₂⁻¹ y‖² = ‖w‖² - ‖y‖²`, and `‖w‖ ≤ ‖y‖/s` with equality at a least right
singular vector. -/
theorem l2_opNorm_mul_inv_sq_eq [DecidableEq k] [Nonempty k] {V₁₂ : Matrix l k 𝕜}
    {V₂₂ : Matrix k k 𝕜}
    (hV₂₂ : IsUnit V₂₂) (hV : V₁₂ᴴ * V₁₂ + V₂₂ᴴ * V₂₂ = 1) :
    ‖V₁₂ * V₂₂⁻¹‖ ^ 2 = (1 - V₂₂.sortedSingularValues (Fintype.card k - 1) ^ 2) /
      V₂₂.sortedSingularValues (Fintype.card k - 1) ^ 2 := by
  rw [sortedSingularValues_eq_iInf_colSingularValues]
  obtain ⟨x, hx1, hx⟩ := V₂₂.exists_norm_eq_iInf_colSingularValues
  set σ := ⨅ i, V₂₂.colSingularValues i with hσ
  have hPy := norm_sq_add_norm_sq_of_stacked hV
  have hinv : ∀ y, toEuclideanLin V₂₂ (toEuclideanLin V₂₂⁻¹ y) = y :=
    toEuclideanLin_mul_nonsing_inv_apply hV₂₂
  have hσpos : 0 < σ := by
    rw [← hx]
    refine norm_pos_iff.2 fun h0 => ?_
    have h := congrArg (toEuclideanLin V₂₂⁻¹) h0
    rw [toEuclideanLin_nonsing_inv_mul_apply hV₂₂, map_zero] at h
    rw [h, norm_zero] at hx1
    exact zero_ne_one hx1
  have hσ1 : σ ≤ 1 := by
    have h := hPy x
    rw [hx1, hx] at h
    nlinarith [sq_nonneg ‖toEuclideanLin V₁₂ x‖]
  apply le_antisymm
  · have hb : ‖V₁₂ * V₂₂⁻¹‖ ≤ √((1 - σ ^ 2) / σ ^ 2) := by
      refine l2_opNorm_le_of_forall_norm_toEuclideanLin_le _ (Real.sqrt_nonneg _) fun y => ?_
      rw [toEuclideanLin_mul_apply]
      set w := toEuclideanLin V₂₂⁻¹ y
      have h1 := hPy w
      rw [hinv] at h1
      have h2 := V₂₂.iInf_colSingularValues_mul_norm_le w
      rw [hinv] at h2
      have h3 : (σ * ‖w‖) ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      rw [← Real.sqrt_sq (norm_nonneg y),
        ← Real.sqrt_mul (div_nonneg (by nlinarith) (by positivity)),
        ← Real.sqrt_sq (norm_nonneg (toEuclideanLin V₁₂ w))]
      refine Real.sqrt_le_sqrt ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    calc ‖V₁₂ * V₂₂⁻¹‖ ^ 2 ≤ √((1 - σ ^ 2) / σ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = (1 - σ ^ 2) / σ ^ 2 := Real.sq_sqrt (div_nonneg (by nlinarith) (by positivity))
  · have h1 := norm_toEuclideanLin_apply_le (V₁₂ * V₂₂⁻¹) (toEuclideanLin V₂₂ x)
    rw [toEuclideanLin_mul_apply, toEuclideanLin_nonsing_inv_mul_apply hV₂₂, hx] at h1
    have h2 := hPy x
    rw [hx1, hx] at h2
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- Two names for one subspace give the same orthogonal projection (the instance argument of
`Submodule.starProjection` depends on the subspace, so `rw` cannot do this). -/
private theorem starProjection_apply_congr {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {S S' : Submodule 𝕜 E} [S.HasOrthogonalProjection]
    [S'.HasOrthogonalProjection] (h : S = S') (y : E) :
    S.starProjection y = S'.starProjection y := by
  subst h
  rfl

open scoped Matrix.Norms.L2Operator in
/-- **The distance between subspaces in matrix form** ([golub2013matrix] Theorem 2.5.1): if `W₁`,
`Z₁`, `Z₂` have orthonormal columns and `range Z₂ = (range Z₁)ᗮ`, then the gap between the ranges
of `W₁` and `Z₁` is `‖W₁ᴴ Z₂‖₂`. The two ranges have the same dimension, so the gap is the one-sided
`‖P_{L⊥} P_K‖` (`Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq`), and
`P_{L⊥} P_K = Z₂ (Z₂ᴴ W₁) W₁ᴴ`, whose outer factors are isometries. -/
theorem gap_range_eq_l2_opNorm_conjTranspose_mul [DecidableEq k] [DecidableEq l]
    {W₁ Z₁ : Matrix n k 𝕜} {Z₂ : Matrix n l 𝕜}
    (hW₁ : W₁ᴴ * W₁ = 1) (hZ₁ : Z₁ᴴ * Z₁ = 1) (hZ₂ : Z₂ᴴ * Z₂ = 1)
    (hZ : LinearMap.range (toEuclideanLin Z₂) = (LinearMap.range (toEuclideanLin Z₁))ᗮ) :
    (LinearMap.range (toEuclideanLin W₁)).gap (LinearMap.range (toEuclideanLin Z₁)) =
      ‖W₁ᴴ * Z₂‖ := by
  classical
  set K := LinearMap.range (toEuclideanLin W₁)
  set L := LinearMap.range (toEuclideanLin Z₁)
  rw [Submodule.gap_eq_norm_orthogonal_mul_of_finrank_eq K L
    ((finrank_range_of_conjTranspose_mul_self_eq_one hW₁).trans
      (finrank_range_of_conjTranspose_mul_self_eq_one hZ₁).symm)]
  have hPK : ∀ y, K.starProjection y = toEuclideanLin W₁ (toEuclideanLin W₁ᴴ y) := fun y => by
    rw [← toEuclideanLin_mul_apply,
      LinearMap.congr_fun (toEuclideanLin_mul_conjTranspose_eq_starProjection hW₁) y]
    rfl
  have hPL : ∀ y, Lᗮ.starProjection y = toEuclideanLin Z₂ (toEuclideanLin Z₂ᴴ y) := fun y => by
    rw [← toEuclideanLin_mul_apply,
      LinearMap.congr_fun (toEuclideanLin_mul_conjTranspose_eq_starProjection hZ₂) y]
    exact (starProjection_apply_congr hZ y).symm
  have hCLM : Lᗮ.starProjection * K.starProjection =
      (toEuclideanLin.trans LinearMap.toContinuousLinearMap) (Z₂ * (Z₂ᴴ * W₁) * W₁ᴴ) := by
    refine ContinuousLinearMap.ext fun y => ?_
    change Lᗮ.starProjection (K.starProjection y) = toEuclideanLin (Z₂ * (Z₂ᴴ * W₁) * W₁ᴴ) y
    rw [hPK, hPL, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
  rw [hCLM, ← l2_opNorm_def, l2_opNorm_mul_conjTranspose_of_conjTranspose_mul_self_eq_one hW₁,
    l2_opNorm_mul_of_conjTranspose_mul_self_eq_one hZ₂, ← l2_opNorm_conjTranspose,
    conjTranspose_mul, conjTranspose_conjTranspose]

/-- **Distance and least cosine** ([golub2013matrix] (7.3.19), the thin CS decomposition read for
two subspaces): for `W₁`, `Z₁` with `card k ≥ 1` orthonormal columns,
`gap(range W₁, range Z₁)² + σ_min(W₁ᴴ Z₁)² = 1`. The gap is the sine of the largest principal
angle (`Submodule.gap_eq_sin_principalAngle`), whose cosine is `σ_min(W₁ᴴ Z₁)`
(`Submodule.cosPrincipalAngle_eq_singularValues`). -/
theorem gap_range_sq_add_sortedSingularValues_sq [DecidableEq k] [Nonempty k] {W₁ Z₁ : Matrix n k 𝕜}
    (hW₁ : W₁ᴴ * W₁ = 1) (hZ₁ : Z₁ᴴ * Z₁ = 1) :
    (LinearMap.range (toEuclideanLin W₁)).gap (LinearMap.range (toEuclideanLin Z₁)) ^ 2 +
      (W₁ᴴ * Z₁).sortedSingularValues (Fintype.card k - 1) ^ 2 = 1 := by
  have hk : Fintype.card k = Fintype.card k - 1 + 1 := (Nat.sub_add_cancel Fintype.card_pos).symm
  have hF := (finrank_range_of_conjTranspose_mul_self_eq_one hW₁).trans hk
  have hG := (finrank_range_of_conjTranspose_mul_self_eq_one hZ₁).trans hk
  have hc1 := Submodule.cosPrincipalAngle_le_one (LinearMap.range (toEuclideanLin W₁))
    (LinearMap.range (toEuclideanLin Z₁)) (Fintype.card k - 1)
  have hc0 := Submodule.cosPrincipalAngle_nonneg (LinearMap.range (toEuclideanLin W₁))
    (LinearMap.range (toEuclideanLin Z₁)) (Fintype.card k - 1)
  have hcs := Submodule.cosPrincipalAngle_eq_singularValues hW₁ hZ₁ (Fintype.card k - 1)
  rw [Submodule.gap_eq_sin_principalAngle _ _ hF hG, Submodule.principalAngle, Real.sin_arccos,
    Real.sq_sqrt (by nlinarith), hcs]
  ring

end Stacked

/-! ### The pseudoinverse: norms and the rectangular condition number -/

section Pinv

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **The condition number of a rectangular matrix** through its pseudoinverse, in the operator
`p`-norm: `pinvCondNumberLp p A = ‖A‖_p ‖A⁺‖_p`, beside the square `Matrix.condNumberLp`. The
book's rectangular `κ₂(A) = ‖A‖₂ ‖A⁺‖₂` ([golub2013matrix] (5.2.4)) is `pinvCondNumberLp 2 A`: for
full column rank it is `σ_max/σ_min` (`Matrix.pinvCondNumberLp_two_eq_div_colSingularValues`), and
for an invertible square matrix it is `condNumberLp p A`
(`Matrix.pinvCondNumberLp_eq_condNumberLp`). -/
noncomputable def pinvCondNumberLp (p : ENNReal) [Fact (1 ≤ p)] (A : Matrix m n 𝕜) : ℝ :=
  lpOpNorm p A * lpOpNorm p A.pinv

/-- For an invertible square matrix the rectangular condition number is the square one. -/
theorem pinvCondNumberLp_eq_condNumberLp (p : ENNReal) [Fact (1 ≤ p)] {A : Matrix n n 𝕜}
    (hA : IsUnit A) : pinvCondNumberLp p A = condNumberLp p A := by
  rw [pinvCondNumberLp, condNumberLp, pinv_eq_inv hA]

omit [DecidableEq m] in
open scoped ComplexOrder in
/-- For linearly independent columns the pseudoinverse is a left inverse, `A⁺ A = 1`. -/
theorem pinv_mul_self_of_linearIndependent {A : Matrix m n 𝕜} (hA : LinearIndependent 𝕜 Aᵀ) :
    A.pinv * A = 1 := by
  rw [pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA, Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp
      (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit)]

open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **The norm of the pseudoinverse** ([golub2013matrix] (5.3.9), `‖(AᵀA)⁻¹Aᵀ‖₂ = 1/σ_n(A)`): for
linearly independent columns, `‖A⁺‖₂ = (⨅ i, σ_i(A))⁻¹`. `A A⁺` is the orthogonal projection onto
the range, so `σ_min ‖A⁺ y‖ ≤ ‖A A⁺ y‖ ≤ ‖y‖`, with equality at `y = A x` for a least right singular
vector `x`, where `A⁺ y = x`. (Column-indexed on purpose: `⨅ i` over the columns is `σ_min` for
every shape; the sorted reading is `Matrix.sortedSingularValues_eq_iInf_colSingularValues`.) -/
theorem l2_opNorm_pinv_eq_inv_iInf_colSingularValues [Nonempty n] {A : Matrix m n 𝕜}
    (hA : LinearIndependent 𝕜 Aᵀ) : ‖A.pinv‖ = (⨅ i, A.colSingularValues i)⁻¹ := by
  obtain ⟨x, hx1, hx⟩ := A.exists_norm_eq_iInf_colSingularValues
  set σ := ⨅ i, A.colSingularValues i with hσ
  have hleft : ∀ z, toEuclideanLin A.pinv (toEuclideanLin A z) = z := fun z => by
    rw [← toEuclideanLin_mul_apply, pinv_mul_self_of_linearIndependent hA, toEuclideanLin_one,
      LinearMap.id_apply]
  have hσpos : 0 < σ := by
    rw [← hx]
    refine norm_pos_iff.2 fun h0 => ?_
    have h := hleft x
    rw [h0, map_zero] at h
    rw [← h, norm_zero] at hx1
    exact zero_ne_one hx1
  apply le_antisymm
  · refine l2_opNorm_le_of_forall_norm_toEuclideanLin_le _ (inv_nonneg.2 hσpos.le) fun y => ?_
    have h1 := A.iInf_colSingularValues_mul_norm_le (toEuclideanLin A.pinv y)
    rw [← toEuclideanLin_mul_apply, LinearMap.congr_fun (mul_pinv_eq_starProjection A) y] at h1
    have h2 := h1.trans ((LinearMap.range (toEuclideanLin A)).norm_starProjection_apply_le y)
    rw [inv_mul_eq_div, le_div_iff₀ hσpos]
    linarith
  · have h1 := norm_toEuclideanLin_apply_le A.pinv (toEuclideanLin A x)
    rw [hleft, hx1, hx] at h1
    rw [inv_le_iff_one_le_mul₀ hσpos]
    linarith

open scoped Matrix.Norms.L2Operator in
/-- **The rectangular condition number from the singular values** ([golub2013matrix] (5.2.4)): for
linearly independent columns, `pinvCondNumberLp 2 A = σ_max / σ_min`. (Column-indexed on purpose,
as `Matrix.l2_opNorm_pinv_eq_inv_iInf_colSingularValues`.) -/
theorem pinvCondNumberLp_two_eq_div_colSingularValues [Nonempty n] {A : Matrix m n 𝕜}
    (hA : LinearIndependent 𝕜 Aᵀ) :
    pinvCondNumberLp 2 A = (⨆ i, A.colSingularValues i) / (⨅ i, A.colSingularValues i) := by
  rw [pinvCondNumberLp, lpOpNorm_two, lpOpNorm_two, l2_opNorm_eq_iSup_colSingularValues,
    l2_opNorm_pinv_eq_inv_iInf_colSingularValues hA, div_eq_mul_inv]

open scoped Matrix.Norms.L2Operator in
/-- **The projection onto the range has norm one** ([golub2013matrix] (5.3.9)): `‖A A⁺‖₂ = 1` for
`A ≠ 0`, `A A⁺` being the orthogonal projection onto the (nonzero) range of `A`. -/
theorem l2_opNorm_mul_pinv_eq_one {A : Matrix m n 𝕜} (hA : A ≠ 0) : ‖A * A.pinv‖ = 1 := by
  rw [l2_opNorm_def, LinearEquiv.trans_apply, mul_pinv_eq_starProjection]
  refine (congrArg norm (ContinuousLinearMap.ext fun _ => rfl)).trans
    (Submodule.norm_starProjection _ fun h => hA ?_)
  exact (LinearEquiv.map_eq_zero_iff _).1 (LinearMap.range_eq_bot.1 h)

/-- `1 - A A⁺` acts as the orthogonal projection onto the orthogonal complement of the range. -/
theorem toEuclideanLin_one_sub_mul_pinv (A : Matrix m n 𝕜) :
    toEuclideanLin (1 - A * A.pinv) = ((LinearMap.range (toEuclideanLin A))ᗮ.starProjection :
      EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 m) := by
  rw [map_sub, toEuclideanLin_one, mul_pinv_eq_starProjection]
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sub_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_coe, Submodule.starProjection_orthogonal_val]

omit [DecidableEq m] in
/-- `A A⁺` is an orthogonal projector (a Hermitian idempotent), onto the range of `A`. -/
theorem isStarProjection_mul_pinv (A : Matrix m n 𝕜) : IsStarProjection (A * A.pinv) :=
  ⟨by rw [IsIdempotentElem, ← Matrix.mul_assoc, A.mul_pinv_mul_self], A.isHermitian_mul_pinv⟩

omit [DecidableEq m] in
/-- `A⁺ A` is an orthogonal projector (a Hermitian idempotent), onto the row space of `A`. -/
theorem isStarProjection_pinv_mul (A : Matrix m n 𝕜) : IsStarProjection (A.pinv * A) :=
  ⟨by rw [IsIdempotentElem, ← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv],
    A.isHermitian_pinv_mul⟩

open scoped Matrix.Norms.L2Operator in
/-- The projection `1 - A A⁺` onto the orthogonal complement of the range has norm at most one. -/
theorem l2_opNorm_one_sub_mul_pinv_le_one (A : Matrix m n 𝕜) : ‖1 - A * A.pinv‖ ≤ 1 :=
  IsStarProjection.norm_le _ (isStarProjection_mul_pinv A).one_sub

omit [DecidableEq m] in
open scoped Matrix.Norms.L2Operator in
/-- The projection `A⁺ A` onto the row space has norm one when `A ≠ 0`, the dual of
`Matrix.l2_opNorm_mul_pinv_eq_one`. -/
theorem l2_opNorm_pinv_mul_eq_one {A : Matrix m n 𝕜} (hA : A ≠ 0) : ‖A.pinv * A‖ = 1 := by
  classical
  have h := l2_opNorm_mul_pinv_eq_one (A := Aᴴ) fun h => hA (conjTranspose_eq_zero.1 h)
  rwa [pinv_conjTranspose, ← conjTranspose_mul, l2_opNorm_conjTranspose] at h

omit [DecidableEq m] in
open scoped Matrix.Norms.L2Operator in
/-- The projection `A⁺ A` onto the row space has norm at most one. -/
theorem l2_opNorm_pinv_mul_le_one (A : Matrix m n 𝕜) : ‖A.pinv * A‖ ≤ 1 :=
  IsStarProjection.norm_le _ (isStarProjection_pinv_mul A)

omit [DecidableEq m] in
open scoped Matrix.Norms.L2Operator in
/-- The projection `1 - A⁺ A` onto the null space has norm at most one, the dual of
`Matrix.l2_opNorm_one_sub_mul_pinv_le_one`. -/
theorem l2_opNorm_one_sub_pinv_mul_le_one (A : Matrix m n 𝕜) : ‖1 - A.pinv * A‖ ≤ 1 :=
  IsStarProjection.norm_le _ (isStarProjection_pinv_mul A).one_sub

open scoped Matrix.Norms.L2Operator in
/-- **The projection onto the orthogonal complement of the range has norm one**
([golub2013matrix] (5.3.9), `m > n`): `‖1 - A A⁺‖₂ = 1` when `A` has fewer columns than rows, so
that its range is a proper subspace. -/
theorem l2_opNorm_one_sub_mul_pinv_eq_one {A : Matrix m n 𝕜}
    (h : Fintype.card n < Fintype.card m) : ‖1 - A * A.pinv‖ = 1 := by
  rw [l2_opNorm_def, LinearEquiv.trans_apply, toEuclideanLin_one_sub_mul_pinv]
  refine (congrArg norm (ContinuousLinearMap.ext fun _ => rfl)).trans
    (Submodule.norm_starProjection _ fun hbot => ?_)
  have htop := Submodule.orthogonal_eq_bot_iff.1 hbot
  have h1 : finrank 𝕜 (LinearMap.range (toEuclideanLin A)) ≤ finrank 𝕜 (EuclideanSpace 𝕜 n) :=
    LinearMap.finrank_range_le (toEuclideanLin A)
  rw [htop, finrank_top, finrank_euclideanSpace, finrank_euclideanSpace] at h1
  omega

omit [DecidableEq m] in
open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **The norm of the inverse Gram matrix** ([golub2013matrix] (5.3.9)): for linearly independent
columns, `‖(Aᴴ A)⁻¹‖₂ = σ_min(A)⁻²`. `(Aᴴ A)⁻¹ = A⁺ A⁺ᴴ`, whose norm is `‖A⁺‖₂²`. -/
theorem l2_opNorm_inv_conjTranspose_mul_self [Nonempty n] {A : Matrix m n 𝕜}
    (hA : LinearIndependent 𝕜 Aᵀ) : ‖(Aᴴ * A)⁻¹‖ = (⨅ i, A.colSingularValues i)⁻¹ ^ 2 := by
  classical
  have hU := (isUnit_iff_isUnit_det _).mp
    (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit
  have hH : ((Aᴴ * A)⁻¹)ᴴ = (Aᴴ * A)⁻¹ := (isHermitian_conjTranspose_mul_self A).inv
  have hG : (Aᴴ * A)⁻¹ = A.pinvᴴᴴ * A.pinvᴴ := by
    rw [conjTranspose_conjTranspose, pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose hA,
      conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc,
      ← Matrix.mul_assoc Aᴴ A, ← Matrix.mul_assoc (Aᴴ * A)⁻¹, nonsing_inv_mul _ hU,
      Matrix.one_mul]
  rw [hG, l2_opNorm_conjTranspose_mul_self, l2_opNorm_conjTranspose,
    l2_opNorm_pinv_eq_inv_iInf_colSingularValues hA, sq]

open scoped Matrix.Norms.L2Operator ComplexOrder in
/-- **The normal equations square the condition number** ([golub2013matrix] (5.3.4),
`κ₂(AᵀA) = κ₂(A)²`): for linearly independent columns,
`pinvCondNumberLp 2 (Aᴴ A) = pinvCondNumberLp 2 A ^ 2`. -/
theorem pinvCondNumberLp_two_conjTranspose_mul_self [Nonempty n] {A : Matrix m n 𝕜}
    (hA : LinearIndependent 𝕜 Aᵀ) : pinvCondNumberLp 2 (Aᴴ * A) = pinvCondNumberLp 2 A ^ 2 := by
  have hU := (posDef_conjTranspose_mul_self_of_linearIndependent hA).isUnit
  rw [pinvCondNumberLp, pinvCondNumberLp, pinv_eq_inv hU, lpOpNorm_two, lpOpNorm_two,
    lpOpNorm_two, lpOpNorm_two, l2_opNorm_conjTranspose_mul_self,
    l2_opNorm_inv_conjTranspose_mul_self hA,
    l2_opNorm_pinv_eq_inv_iInf_colSingularValues hA]
  ring

end Pinv

/-! ### Wedin's bound: the perturbation of the pseudoinverse -/

section Wedin

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

open scoped Matrix.Norms.Frobenius

/-- **Wedin's decomposition** of the difference of two pseudoinverses ([golub2013matrix] §5.5.3):
`B⁺ - A⁺ = -B⁺ (B - A) A⁺ + B⁺ B⁺ᴴ (B - A)ᴴ (1 - A A⁺) + (1 - B⁺ B) (B - A)ᴴ A⁺ᴴ A⁺`. Only the four
Penrose conditions of `A⁺` and `B⁺` enter the proof, and they characterize the pseudoinverse
(`Matrix.pinv_unique`). -/
theorem pinv_sub_pinv_eq (A B : Matrix m n 𝕜) :
    B.pinv - A.pinv = -(B.pinv * ((B - A) * A.pinv))
      + B.pinv * (B.pinvᴴ * ((B - A)ᴴ * (1 - A * A.pinv)))
      + (1 - B.pinv * B) * ((B - A)ᴴ * A.pinvᴴ * A.pinv) := by
  set P := A.pinv
  set Q := B.pinv
  have f1 : Aᴴ * (1 - A * P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← A.isHermitian_mul_pinv.eq, ← conjTranspose_mul,
      A.mul_pinv_mul_self, sub_self]
  have f2 : Q * Qᴴ * Bᴴ = Q := by
    rw [Matrix.mul_assoc, ← conjTranspose_mul, B.isHermitian_mul_pinv.eq, ← Matrix.mul_assoc,
      B.pinv_mul_self_mul_pinv]
  have f3 : (1 - Q * B) * Bᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, ← B.isHermitian_pinv_mul.eq, ← conjTranspose_mul,
      ← Matrix.mul_assoc, B.mul_pinv_mul_self, sub_self]
  have f4 : Aᴴ * Pᴴ * P = P := by
    rw [← conjTranspose_mul, A.isHermitian_pinv_mul.eq, A.pinv_mul_self_mul_pinv]
  have T2 : Q * (Qᴴ * ((B - A)ᴴ * (1 - A * P))) = Q * (1 - A * P) := by
    rw [conjTranspose_sub, Matrix.sub_mul Bᴴ Aᴴ (1 - A * P), f1, sub_zero,
      ← Matrix.mul_assoc Q Qᴴ (Bᴴ * (1 - A * P)), ← Matrix.mul_assoc (Q * Qᴴ) Bᴴ (1 - A * P), f2]
  have T3 : (1 - Q * B) * ((B - A)ᴴ * Pᴴ * P) = -((1 - Q * B) * P) := by
    rw [conjTranspose_sub, Matrix.sub_mul Bᴴ Aᴴ Pᴴ, Matrix.sub_mul (Bᴴ * Pᴴ) (Aᴴ * Pᴴ) P, f4,
      Matrix.mul_sub (1 - Q * B) (Bᴴ * Pᴴ * P) P, Matrix.mul_assoc Bᴴ Pᴴ P,
      ← Matrix.mul_assoc (1 - Q * B) Bᴴ (Pᴴ * P), f3, Matrix.zero_mul, zero_sub]
  rw [T2, T3]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  abel

/-- The scalar end of Wedin's bound: three terms, each at most `e max(p², q²)`, whose squares add
to `d²`, give `d ≤ 2 e max(p², q²)` (as `√3 ≤ 2`). -/
private theorem wedin_real_bound {d t₁ t₂ t₃ p q e : ℝ}
    (hsq : d ^ 2 = t₁ ^ 2 + t₂ ^ 2 + t₃ ^ 2)
    (hd : 0 ≤ d) (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂) (h₃ : 0 ≤ t₃) (he : 0 ≤ e)
    (b₁ : t₁ ≤ q * (e * p)) (b₂ : t₂ ≤ q * (q * (e * 1))) (b₃ : t₃ ≤ 1 * (e * p * p)) :
    d ≤ 2 * e * max (p ^ 2) (q ^ 2) := by
  have hpM : p ^ 2 ≤ max (p ^ 2) (q ^ 2) := le_max_left _ _
  have hqM : q ^ 2 ≤ max (p ^ 2) (q ^ 2) := le_max_right _ _
  generalize max (p ^ 2) (q ^ 2) = M at *
  have hM0 : 0 ≤ M := (sq_nonneg p).trans hpM
  have hqp : q * p ≤ M := by nlinarith [sq_nonneg (q - p)]
  have k₁ : t₁ ≤ e * M := b₁.trans (by nlinarith [mul_le_mul_of_nonneg_left hqp he])
  have k₂ : t₂ ≤ e * M := b₂.trans (by nlinarith [mul_le_mul_of_nonneg_left hqM he])
  have k₃ : t₃ ≤ e * M := b₃.trans (by nlinarith [mul_le_mul_of_nonneg_left hpM he])
  have hfin : d ^ 2 ≤ (2 * e * M) ^ 2 := by
    rw [hsq]
    nlinarith [pow_le_pow_left₀ h₁ k₁ 2, pow_le_pow_left₀ h₂ k₂ 2, pow_le_pow_left₀ h₃ k₃ 2,
      sq_nonneg (e * M)]
  exact (pow_le_pow_iff_left₀ hd (by positivity) two_ne_zero).1 hfin

/-- **Wedin's bound** ([golub2013matrix] §5.5.3, after Wedin (1973) and Stewart (1977)): for
`A, E : Matrix m n 𝕜`, `‖(A + E)⁺ - A⁺‖_F ≤ 2 ‖E‖_F max(‖A⁺‖₂², ‖(A + E)⁺‖₂²)`, with no rank
hypothesis. The three terms of Wedin's decomposition `Matrix.pinv_sub_pinv_eq` are mutually
orthogonal for the Frobenius inner product and bounded by `‖B⁺‖₂ ‖E‖_F ‖A⁺‖₂`, `‖B⁺‖₂² ‖E‖_F`
and `‖E‖_F ‖A⁺‖₂²`; the constant is `√3 ≤ 2`.

The Frobenius norm is the scoped instance `Matrix.Norms.Frobenius`, and the spectral norms are
written `lpOpNorm 2`. -/
theorem frobenius_norm_pinv_sub_le (A E : Matrix m n 𝕜) :
    ‖(A + E).pinv - A.pinv‖ ≤ 2 * ‖E‖ *
      max (lpOpNorm 2 A.pinv ^ 2) (lpOpNorm 2 (A + E).pinv ^ 2) := by
  have hdec := pinv_sub_pinv_eq A (A + E)
  rw [add_sub_cancel_left] at hdec
  set B := A + E
  set P := A.pinv
  set Q := B.pinv
  -- the two orthogonal projectors `1 - A P` and `1 - Q B`
  have hAP : IsStarProjection (1 - A * P) := (isStarProjection_mul_pinv A).one_sub
  have hQB : IsStarProjection (1 - Q * B) := (isStarProjection_pinv_mul B).one_sub
  have h0 : (1 - A * P) * (A * P) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, A.mul_pinv_mul_self, sub_self]
  -- orthogonality of the first two terms and the third
  have hO1 : trace ((-(Q * (E * P)) + Q * (Qᴴ * (Eᴴ * (1 - A * P))))ᴴ
      * ((1 - Q * B) * (Eᴴ * Pᴴ * P))) = 0 := by
    have hQ : Qᴴ * (1 - Q * B) = 0 := by
      rw [← (isHermitian_one.sub B.isHermitian_pinv_mul).eq, ← conjTranspose_mul, Matrix.sub_mul,
        Matrix.one_mul, B.pinv_mul_self_mul_pinv, sub_self, conjTranspose_zero]
    rw [← Matrix.mul_neg, ← Matrix.mul_add, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Qᴴ (1 - Q * B), hQ, Matrix.zero_mul, Matrix.mul_zero, trace_zero]
  -- orthogonality of the first two terms
  have hO2 : trace ((-(Q * (E * P)))ᴴ * (Q * (Qᴴ * (Eᴴ * (1 - A * P))))) = 0 := by
    have hPh : Pᴴ = A * P * Pᴴ := by
      have h : P = P * (A * P) := by rw [← Matrix.mul_assoc, A.pinv_mul_self_mul_pinv]
      calc Pᴴ = (P * (A * P))ᴴ := by rw [← h]
        _ = A * P * Pᴴ := by rw [conjTranspose_mul, A.isHermitian_mul_pinv.eq]
    have e1 : (-(Q * (E * P)))ᴴ * (Q * (Qᴴ * (Eᴴ * (1 - A * P))))
        = -(Pᴴ * (Eᴴ * Qᴴ * Q * Qᴴ * Eᴴ * (1 - A * P))) := by
      simp only [conjTranspose_neg, conjTranspose_mul, Matrix.neg_mul, Matrix.mul_assoc]
    rw [e1, trace_neg, hPh, Matrix.mul_assoc (A * P) Pᴴ,
      trace_mul_comm (A * P), Matrix.mul_assoc Pᴴ _ (A * P),
      Matrix.mul_assoc (Eᴴ * Qᴴ * Q * Qᴴ * Eᴴ) (1 - A * P) (A * P), h0, Matrix.mul_zero,
      Matrix.mul_zero, trace_zero, neg_zero]
  -- the three bounds
  have hq0 := lpOpNorm_nonneg 2 Q
  have hp0 := lpOpNorm_nonneg 2 P
  have he0 := norm_nonneg E
  have hB1 : ‖-(Q * (E * P))‖ ≤ lpOpNorm 2 Q * (‖E‖ * lpOpNorm 2 P) := by
    rw [norm_neg]
    exact (frobenius_norm_mul_le_lpOpNorm_two_mul Q _).trans
      (mul_le_mul_of_nonneg_left (frobenius_norm_mul_le_mul_lpOpNorm_two E P) hq0)
  have hB2 : ‖Q * (Qᴴ * (Eᴴ * (1 - A * P)))‖ ≤ lpOpNorm 2 Q * (lpOpNorm 2 Q * (‖E‖ * 1)) := by
    have hEP : ‖Eᴴ * (1 - A * P)‖ ≤ ‖E‖ * 1 := by
      refine (frobenius_norm_mul_le_mul_lpOpNorm_two _ _).trans ?_
      rw [frobenius_norm_conjTranspose]
      exact mul_le_mul_of_nonneg_left (lpOpNorm_two_le_one_of_isStarProjection hAP) he0
    have h2 := frobenius_norm_mul_le_lpOpNorm_two_mul Qᴴ (Eᴴ * (1 - A * P))
    rw [lpOpNorm_two_conjTranspose] at h2
    exact (frobenius_norm_mul_le_lpOpNorm_two_mul Q _).trans
      (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hEP hq0)) hq0)
  have hB3 : ‖(1 - Q * B) * (Eᴴ * Pᴴ * P)‖ ≤ 1 * (‖E‖ * lpOpNorm 2 P * lpOpNorm 2 P) := by
    have h1 : ‖Eᴴ * Pᴴ‖ ≤ ‖E‖ * lpOpNorm 2 P := by
      have := frobenius_norm_mul_le_mul_lpOpNorm_two Eᴴ Pᴴ
      rwa [frobenius_norm_conjTranspose, lpOpNorm_two_conjTranspose] at this
    have h2 : ‖Eᴴ * Pᴴ * P‖ ≤ ‖E‖ * lpOpNorm 2 P * lpOpNorm 2 P :=
      (frobenius_norm_mul_le_mul_lpOpNorm_two _ P).trans (mul_le_mul_of_nonneg_right h1 hp0)
    exact (frobenius_norm_mul_le_lpOpNorm_two_mul _ _).trans
      (mul_le_mul (lpOpNorm_two_le_one_of_isStarProjection hQB) h2 (norm_nonneg _) zero_le_one)
  have hsq : ‖Q - P‖ ^ 2 = ‖-(Q * (E * P))‖ ^ 2 + ‖Q * (Qᴴ * (Eᴴ * (1 - A * P)))‖ ^ 2
      + ‖(1 - Q * B) * (Eᴴ * Pᴴ * P)‖ ^ 2 := by
    rw [hdec, frobenius_norm_add_sq_of_trace_eq_zero hO1,
      frobenius_norm_add_sq_of_trace_eq_zero hO2]
  exact wedin_real_bound hsq (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    he0 hB1 hB2 hB3

end Wedin

/-! ### The norm of `P (I + Pᴴ P)^{-1/2}` -/

section GramSqrt

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
open scoped Matrix.Norms.Frobenius ComplexOrder MatrixOrder in
/-- [golub2013matrix] (8.1.3) (and (7.2.6)): for `P : Matrix m n 𝕜`,
`‖P (I + Pᴴ P)^{-1/2}‖₂ ≤ ‖P‖₂ ≤ ‖P‖_F`, the square root being `CFC.sqrt`. With
`S = (I + Pᴴ P)^{1/2}` Hermitian and `x = S y`, `‖x‖² = ‖y‖² + ‖P y‖² ≥ ‖y‖²`, so
`‖P S⁻¹ x‖ = ‖P y‖ ≤ ‖P‖₂ ‖y‖ ≤ ‖P‖₂ ‖x‖`; no diagonalization is needed. The second inequality is
`Matrix.l2_opNorm_le_frobenius_norm`. -/
theorem l2_opNorm_mul_inv_sqrt_one_add_gram_le (P : Matrix m n 𝕜) :
    lpOpNorm 2 (P * (CFC.sqrt (1 + Pᴴ * P))⁻¹) ≤ lpOpNorm 2 P ∧ lpOpNorm 2 P ≤ ‖P‖ := by
  classical
  refine ⟨?_, l2_opNorm_le_frobenius_norm P⟩
  set S := CFC.sqrt (1 + Pᴴ * P) with hS
  have hG : 0 ≤ 1 + Pᴴ * P :=
    nonneg_iff_posSemidef.2 (PosSemidef.one.add (posSemidef_conjTranspose_mul_self P))
  have hSS : S * S = 1 + Pᴴ * P := CFC.sqrt_mul_sqrt_self _ hG
  have hSh : Sᴴ = S := (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg (1 + Pᴴ * P))).isHermitian
  have hGu : IsUnit (1 + Pᴴ * P) :=
    ((PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self P))).isUnit
  have hSu : IsUnit S := isUnit_of_mul_isUnit_left (hSS ▸ hGu)
  have hnorm : ∀ y, ‖toEuclideanLin S y‖ ^ 2 = ‖y‖ ^ 2 + ‖toEuclideanLin P y‖ ^ 2 := by
    intro y
    have h : inner 𝕜 (toEuclideanLin S y) (toEuclideanLin S y) =
        inner 𝕜 y y + inner 𝕜 (toEuclideanLin P y) (toEuclideanLin P y) := by
      rw [← toEuclideanLin_conjTranspose_inner_left S, ← toEuclideanLin_mul_apply, hSh, hSS,
        map_add, LinearMap.add_apply, toEuclideanLin_one, LinearMap.id_apply, inner_add_left,
        toEuclideanLin_mul_apply, toEuclideanLin_conjTranspose_inner_left]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    exact_mod_cast h
  have hP : ∀ y, ‖toEuclideanLin P y‖ ≤ lpOpNorm 2 P * ‖y‖ := fun y => (lpCLM 2 P).le_opNorm y
  refine ContinuousLinearMap.opNorm_le_bound _ (lpOpNorm_nonneg 2 P) fun x => ?_
  change ‖toEuclideanLin (P * S⁻¹) x‖ ≤ lpOpNorm 2 P * ‖x‖
  set y := toEuclideanLin S⁻¹ x
  have hx : x = toEuclideanLin S y := (toEuclideanLin_mul_nonsing_inv_apply hSu x).symm
  have hy : ‖y‖ ≤ ‖x‖ := by
    have h := hnorm y
    rw [← hx] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (by nlinarith [sq_nonneg ‖toEuclideanLin P y‖])
  rw [toEuclideanLin_mul_apply]
  exact (hP y).trans (mul_le_mul_of_nonneg_left hy (lpOpNorm_nonneg 2 P))

end GramSqrt

/-! ### Uniqueness of the Frobenius-optimal low-rank approximation -/

section EckartYoungEquality

/-- **The equality case of a weighted count**: if `0 ≤ aᵢ ≤ 1`, `∑ aᵢ ≤ |J|`, `sᵢ ≥ t₁` on `J` and
`sᵢ ≤ t₂` off `J` with `t₂ ≥ 0`, then `∑ sᵢ aᵢ + (t₁ - t₂) ∑_{i ∈ J} (1 - aᵢ) ≤ ∑_{i ∈ J} sᵢ`. The
maximum of `∑ sᵢ aᵢ` under the constraints is `∑_J sᵢ`, with a defect proportional to the gap. -/
private theorem sum_mul_add_gap_le {ι : Type*} [Fintype ι] (J : Finset ι) {s a : ι → ℝ}
    {t₁ t₂ : ℝ} (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (hsum : ∑ i, a i ≤ J.card)
    (hJ : ∀ i ∈ J, t₁ ≤ s i) (hJc : ∀ i ∉ J, s i ≤ t₂) (ht₂ : 0 ≤ t₂) :
    ∑ i, s i * a i + (t₁ - t₂) * ∑ i ∈ J, (1 - a i) ≤ ∑ i ∈ J, s i := by
  classical
  have hsplit : ∀ f : ι → ℝ, ∑ i, f i = ∑ i ∈ J, f i + ∑ i ∈ Jᶜ, f i := fun f => by
    rw [← Finset.sum_add_sum_compl J f]
  have h1 : ∑ i ∈ Jᶜ, s i * a i ≤ t₂ * ∑ i ∈ Jᶜ, a i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hJc i (Finset.mem_compl.1 hi)) (ha0 i)
  have h2 : t₁ * ∑ i ∈ J, (1 - a i) ≤ ∑ i ∈ J, s i * (1 - a i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hJ i hi) (by linarith [ha1 i])
  have h3 : ∑ i ∈ Jᶜ, a i ≤ ∑ i ∈ J, (1 - a i) := by
    rw [hsplit a] at hsum
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  have h4 : ∑ i ∈ J, s i * (1 - a i) = ∑ i ∈ J, s i - ∑ i ∈ J, s i * a i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit fun i => s i * a i]
  nlinarith [mul_le_mul_of_nonneg_left h3 ht₂]

variable {m n : ℕ} {C : Matrix (Fin m) (Fin n) 𝕜}
  {U : Matrix (Fin m) (Fin m) 𝕜} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) 𝕜}

open scoped Matrix.Norms.Frobenius

/-- The column `j` of `M V Σᴴ`: `σ_j M v_j` below the width of `Σ`, and `0` beyond. -/
private theorem norm_col_mul_mul_rectDiagonal_sq (M : Matrix (Fin n) (Fin n) 𝕜) (j : Fin m) :
    ‖(WithLp.toLp 2 fun k => (M * V *
        (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin n) (Fin m) 𝕜)) k j :
        EuclideanSpace 𝕜 (Fin n))‖ ^ 2 =
      if h : (j : ℕ) < n then
        σ j ^ 2 * ‖toEuclideanLin M (WithLp.toLp 2 (Vᵀ ⟨j, h⟩))‖ ^ 2 else 0 := by
  split_ifs with h
  · have hv : (fun k => (M * V *
        (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin n) (Fin m) 𝕜)) k j) =
        ((σ j : ℝ) : 𝕜) • WithLp.ofLp (toEuclideanLin M (WithLp.toLp 2 (Vᵀ ⟨j, h⟩))) := by
      funext k
      rw [mul_apply, Finset.sum_eq_single ⟨j, h⟩]
      · rw [rectDiagonal_apply, ite_eq_left rfl]
        simp only [ofLp_toEuclideanLin, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
          mul_apply, transpose_apply]
        ring
      · intro l _ hl
        rw [rectDiagonal_apply, ite_eq_right (fun hlj => hl (Fin.ext hlj)), mul_zero]
      · simp
    rw [hv, WithLp.toLp_smul, WithLp.toLp_ofLp, norm_smul, mul_pow, RCLike.norm_ofReal, sq_abs]
  · have hv : (fun k => (M * V *
        (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin n) (Fin m) 𝕜)) k j) = 0 := by
      funext k
      rw [mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [rectDiagonal_apply, ite_eq_right (fun hlj => h (by rw [← hlj]; exact l.isLt)),
        mul_zero]
    rw [hv]
    simp

/-- **The Frobenius norm against `Cᴴ` in singular coordinates**: for an SVD `C = U Σ Vᴴ` and any
`M`, `‖M Cᴴ‖_F² = ∑_{i < min(m, n)} σᵢ² ‖M vᵢ‖²`, `vᵢ` the columns of `V`. -/
private theorem frobenius_norm_mul_conjTranspose_sq (h : IsSVD C U σ V)
    (M : Matrix (Fin n) (Fin n) 𝕜) :
    ‖M * Cᴴ‖ ^ 2 = ∑ i : Fin (min m n), σ i ^ 2 *
      ‖toEuclideanLin M (WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i)))‖ ^ 2 := by
  have hC : Cᴴ = V * (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin n) (Fin m) 𝕜) *
      star U := h.conjTranspose.eq_mul_mul_star
  have h1 : M * Cᴴ = (1 : Matrix (Fin n) (Fin n) 𝕜) * (M * V *
      (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin n) (Fin m) 𝕜)) * star U := by
    rw [hC, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  rw [h1, frobenius_norm_unitary_mul_mul_unitary (unitaryGroup (Fin n) 𝕜).one_mem _
    (Unitary.star_mem h.mem_unitaryGroup_left), frobenius_norm_sq_eq_sum_norm_sq_col]
  simp_rw [norm_col_mul_mul_rectDiagonal_sq]
  set g : Fin m → ℝ := fun j => if h : (j : ℕ) < n then
    σ j ^ 2 * ‖toEuclideanLin M (WithLp.toLp 2 (Vᵀ ⟨j, h⟩))‖ ^ 2 else 0 with hg
  have hL : ∑ i : Fin (min m n), σ i ^ 2 *
      ‖toEuclideanLin M (WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i)))‖ ^ 2 =
      ∑ i : Fin (min m n), g (Fin.castLE (min_le_left m n) i) :=
    Finset.sum_congr rfl fun i _ => by
      simp only [hg, Fin.val_castLE, dite_eq_left (lt_of_lt_of_le i.isLt (min_le_right m n))]
      rfl
  rw [hL, Fin.sum_castLE_eq_sum_ite (min_le_left m n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : (j : ℕ) < n
  · rw [ite_eq_left (lt_min j.isLt hj)]
  · rw [ite_eq_right fun h' => hj (lt_of_lt_of_le h' (min_le_right m n)), hg]
    exact dite_eq_right hj

/-- The columns of `P V` are the images of the columns of `V`. -/
private theorem toEuclideanLin_toLp_transpose (P V : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    toEuclideanLin P (WithLp.toLp 2 (Vᵀ i)) = WithLp.toLp 2 fun k => (P * V) k i := by
  simp only [toEuclideanLin_toLp]
  congr 1

/-- An orthogonal projector of rank at most `r` has Frobenius norm at most `√r`. -/
private theorem frobenius_norm_sq_le_of_isStarProjection {P : Matrix (Fin n) (Fin n) 𝕜}
    (hP : IsStarProjection P) {r : ℕ} (hr : P.rank ≤ r) : ‖P‖ ^ 2 ≤ r := by
  have h3 : ‖P‖ ≤ √(r : ℝ) :=
    (frobenius_norm_le_sqrt_rank_mul_l2_opNorm P).trans
      ((mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hr))
        (lpOpNorm_two_le_one_of_isStarProjection hP) (lpOpNorm_nonneg _ _)
        (Real.sqrt_nonneg _)).trans (mul_one _).le)
  calc ‖P‖ ^ 2 ≤ √(r : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    _ = r := Real.sq_sqrt (Nat.cast_nonneg _)

/-- **Pythagoras for a projector fixing `Ĉ`**: if `P` is an orthogonal projector with `Ĉ P = Ĉ`,
then `‖C - Ĉ‖_F² = ‖(C - Ĉ) P‖_F² + ‖C (1 - P)‖_F²`. -/
private theorem frobenius_norm_sub_sq_eq_of_isStarProjection {C Ĉ : Matrix (Fin m) (Fin n) 𝕜}
    {P : Matrix (Fin n) (Fin n) 𝕜} (hP : IsStarProjection P) (hĈP : Ĉ * P = Ĉ) :
    ‖C - Ĉ‖ ^ 2 = ‖(C - Ĉ) * P‖ ^ 2 + ‖C * (1 - P)‖ ^ 2 := by
  have hPH : Pᴴ = P := hP.isSelfAdjoint.star_eq
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hXY : (C - Ĉ) * P + C * (1 - P) = C - Ĉ := by
    rw [Matrix.sub_mul, hĈP, Matrix.mul_sub, Matrix.mul_one]
    abel
  have h0 : C * (1 - P) * P = 0 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPP, sub_self, Matrix.mul_zero]
  have htr : trace (((C - Ĉ) * P)ᴴ * (C * (1 - P))) = 0 := by
    rw [conjTranspose_mul, hPH, trace_mul_comm, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      trace_zero]
  rw [← frobenius_norm_add_sq_of_trace_eq_zero htr, hXY]

/-- If `P` fixes the leading `r` right singular vectors of `C` and kills the others, then
`C P = U Σ_r Vᴴ`: `P = V D Vᴴ` with `D` the leading-`r` indicator. -/
private theorem mul_eq_svdTruncation_of_toEuclideanLin (h : IsSVD C U σ V) {r : ℕ}
    {P : Matrix (Fin n) (Fin n) 𝕜} (hPv : ∀ i : Fin n, toEuclideanLin P (WithLp.toLp 2 (Vᵀ i)) =
      if (i : ℕ) < r then WithLp.toLp 2 (Vᵀ i) else 0) :
    C * P = svdTruncation U σ V r := by
  set D : Matrix (Fin n) (Fin n) 𝕜 := diagonal fun i => if (i : ℕ) < r then 1 else 0 with hD
  have hPV : P * V = V * D := by
    ext k i
    have h1 : WithLp.ofLp (toEuclideanLin P (WithLp.toLp 2 (Vᵀ i))) k =
        WithLp.ofLp (if (i : ℕ) < r then WithLp.toLp 2 (Vᵀ i) else 0) k := by rw [hPv i]
    rw [toEuclideanLin_toLp_transpose] at h1
    rw [hD, mul_diagonal]
    refine h1.trans ?_
    split_ifs <;> simp
  have hVV : V * star V = 1 := mem_unitaryGroup_iff.1 h.mem_unitaryGroup_right
  have hPeq : P = V * D * star V := by
    rw [← hPV, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have hsV : star V * V = 1 := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
  rw [hPeq, h.eq_mul_mul_star, svdTruncation]
  have hSD : (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin m) (Fin n) 𝕜) * D =
      rectDiagonal fun i => if i < r then ((σ i : ℝ) : 𝕜) else 0 := by
    ext i j
    rw [hD, mul_diagonal, rectDiagonal_apply, rectDiagonal_apply]
    by_cases hij : (i : ℕ) = j
    · simp only [hij, ite_true]
      split_ifs <;> simp
    · simp [hij]
  calc U * (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin m) (Fin n) 𝕜) * star V *
        (V * D * star V)
      = U * ((rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin m) (Fin n) 𝕜) *
          (star V * V) * D) * star V := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hsV, Matrix.mul_one, hSD]

/-- **The Frobenius-optimal rank-`r` approximation is unique under a gap** (the equality case of
Eckart–Young–Mirsky; [golub2013matrix] Theorem 6.3.1, "`[E₀ | R₀]` is the unique minimizer"): if
`IsSVD C U σ V`, `σ_{r-1} > σ_r` (which forces `0 < r`), `rank Ĉ ≤ r` and
`‖C - Ĉ‖_F² ≤ ∑_{r ≤ i < min(m, n)} σᵢ²`, then `Ĉ` is the truncation `U Σ_r Vᴴ`. With `P = Ĉ⁺ Ĉ`
the projection onto the row space of `Ĉ` (rank `≤ r`),
`‖C - Ĉ‖_F² = ‖(C - Ĉ) P‖_F² + ‖C (1 - P)‖_F²` and
`‖C (1 - P)‖_F² = ∑ σᵢ² (1 - ‖P vᵢ‖²)` with `∑ ‖P vᵢ‖² = ‖P‖_F² ≤ r`; the gap then forces
`(C - Ĉ) P = 0` and `P vᵢ = vᵢ` for `i < r` (`P vᵢ = 0` for `i ≥ r` by the count), so `P` is the
projection onto the leading right singular vectors and `Ĉ = C P = U Σ_r Vᴴ`. -/
theorem eq_svdTruncation_of_frobenius_norm_sub_sq_le (h : IsSVD C U σ V) {r : ℕ}
    (hgap : σ r < σ (r - 1)) {Ĉ : Matrix (Fin m) (Fin n) 𝕜} (hĈ : Ĉ.rank ≤ r)
    (hle : ‖C - Ĉ‖ ^ 2 ≤ ∑ i ∈ Finset.Ico r (min m n), σ i ^ 2) :
    Ĉ = svdTruncation U σ V r := by
  have hsvd := h.eq_mul_mul_star
  rcases le_or_gt (min m n) r with hmr | hmr
  · -- no singular value is dropped: `Ĉ = C`
    rw [Finset.Ico_eq_empty_of_le hmr, Finset.sum_empty] at hle
    have h0 : C - Ĉ = 0 := by
      rw [← norm_eq_zero]
      nlinarith [norm_nonneg (C - Ĉ)]
    rw [← sub_eq_zero.1 h0, hsvd, svdTruncation]
    congr 2
    refine rectDiagonal_congr fun i him hin => ?_
    rw [ite_eq_left (lt_of_lt_of_le (lt_min him hin) hmr)]
  obtain ⟨P, hPdef⟩ : ∃ P, P = Ĉ.pinv * Ĉ := ⟨_, rfl⟩
  set v : Fin n → EuclideanSpace 𝕜 (Fin n) := fun i => WithLp.toLp 2 (Vᵀ i) with hv
  have hV : Vᴴ * V = 1 := conjTranspose_mul_self_of_mem_unitaryGroup h.mem_unitaryGroup_right
  have hvo : Orthonormal 𝕜 v := orthonormal_toLp_transpose_of_conjTranspose_mul_self_eq_one hV
  have hPs : IsStarProjection P := by rw [hPdef]; exact isStarProjection_pinv_mul Ĉ
  have hPH : Pᴴ = P := hPs.isSelfAdjoint.star_eq
  have hĈP : Ĉ * P = Ĉ := by rw [hPdef, ← Matrix.mul_assoc, mul_pinv_mul_self]
  have hFP : ‖P‖ ^ 2 ≤ r := frobenius_norm_sq_le_of_isStarProjection hPs
    (by rw [hPdef]; exact (rank_mul_le_right _ _).trans hĈ)
  have hsplit := frobenius_norm_sub_sq_eq_of_isStarProjection (C := C) hPs hĈP
  -- the weights `aᵢ = ‖P vᵢ‖²`
  set K := LinearMap.range (toEuclideanLin Ĉᴴ) with hK
  have hPK : ∀ x, toEuclideanLin P x = K.starProjection x := fun x => by
    rw [hPdef, pinv_mul_eq_starProjection]
    try rfl
  have hPK' : ∀ x, toEuclideanLin (1 - P) x = Kᗮ.starProjection x := fun x => by
    rw [map_sub, LinearMap.sub_apply, toEuclideanLin_one, LinearMap.id_apply, hPK,
      Submodule.starProjection_orthogonal_val]
  have hab : ∀ i, ‖toEuclideanLin P (v i)‖ ^ 2 + ‖toEuclideanLin (1 - P) (v i)‖ ^ 2 = 1 :=
    fun i => by rw [hPK, hPK', ← Submodule.norm_sq_eq_add_norm_sq_starProjection, hvo.1 i,
      one_pow]
  have hcolP : ∀ i, toEuclideanLin P (v i) = WithLp.toLp 2 fun k => (P * V) k i := fun i =>
    toEuclideanLin_toLp_transpose P V i
  have hsumN : ∑ i, ‖toEuclideanLin P (v i)‖ ^ 2 ≤ r := by
    have h1 : ‖P * V‖ = ‖P‖ := by
      simpa using frobenius_norm_unitary_mul_mul_unitary (unitaryGroup (Fin n) 𝕜).one_mem P
        h.mem_unitaryGroup_right
    calc ∑ i, ‖toEuclideanLin P (v i)‖ ^ 2 = ‖P * V‖ ^ 2 := by
          rw [frobenius_norm_sq_eq_sum_norm_sq_col]
          exact Finset.sum_congr rfl fun i _ => by rw [hcolP]
      _ = ‖P‖ ^ 2 := by rw [h1]
      _ ≤ r := hFP
  set p := min m n with hp
  have hpn : p ≤ n := min_le_right m n
  set a : Fin p → ℝ := fun i => ‖toEuclideanLin P (v (Fin.castLE hpn i))‖ ^ 2 with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => sq_nonneg _
  have ha1 : ∀ i, a i ≤ 1 := fun i => by
    have := hab (Fin.castLE hpn i)
    simp only [ha]
    nlinarith [sq_nonneg ‖toEuclideanLin (1 - P) (v (Fin.castLE hpn i))‖]
  have hsum : ∑ i, a i ≤ r := by
    refine le_trans (le_of_eq (Fin.sum_castLE_eq_sum_ite hpn
      (fun j => ‖toEuclideanLin P (v j)‖ ^ 2))) (le_trans ?_ hsumN)
    exact Finset.sum_le_sum fun i _ => by split_ifs <;> [exact le_rfl; exact sq_nonneg _]
  -- `‖C (1 - P)‖_F² = ∑ σᵢ² (1 - aᵢ)`
  have hC1P : ‖C * (1 - P)‖ ^ 2 = ∑ i : Fin p, σ i ^ 2 * (1 - a i) := by
    have hcj : (C * (1 - P))ᴴ = (1 - P) * Cᴴ := by
      rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hPH]
    rw [← frobenius_norm_conjTranspose, hcj, frobenius_norm_mul_conjTranspose_sq h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hab (Fin.castLE hpn i)
    simp only [ha, hv] at this ⊢
    rw [← this]
    ring
  -- the count
  set J : Finset (Fin p) := Finset.univ.filter fun i => (i : ℕ) < r with hJ
  have hJcard : J.card = r := by
    rw [hJ, Fin.card_filter_val_lt, min_eq_right hmr.le]
  have hmain := sum_mul_add_gap_le J (s := fun i => σ i ^ 2) ha0 ha1 (by rw [hJcard]; exact hsum)
    (t₁ := σ (r - 1) ^ 2) (t₂ := σ r ^ 2)
    (fun i hi => pow_le_pow_left₀ (h.nonneg _)
      (h.antitone (Nat.le_sub_one_of_lt (Finset.mem_filter.1 hi).2)) 2)
    (fun i hi => pow_le_pow_left₀ (h.nonneg _)
      (h.antitone (not_lt.1 fun h' => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩))) 2)
    (sq_nonneg _)
  -- the hypothesis, in the same terms
  have hIco : ∑ i ∈ Finset.Ico r p, σ i ^ 2 = ∑ i : Fin p, σ i ^ 2 - ∑ i ∈ J, σ i ^ 2 := by
    have h1 : ∑ i : Fin p, σ i ^ 2 = ∑ i ∈ Finset.range p, σ i ^ 2 :=
      Fin.sum_univ_eq_sum_range (fun i => σ i ^ 2) p
    have h2 : ∑ i ∈ J, σ i ^ 2 = ∑ i ∈ Finset.range r, σ i ^ 2 := by
      rw [hJ, Finset.sum_filter,
        Fin.sum_univ_eq_sum_range (fun i => if i < r then σ i ^ 2 else 0) p, ← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [h1, h2, Finset.sum_range_add_sum_Ico _ hmr.le |>.symm]
    ring
  have hexp : ∑ i : Fin p, σ i ^ 2 * (1 - a i) =
      ∑ i : Fin p, σ i ^ 2 - ∑ i : Fin p, σ i ^ 2 * a i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hgap2 : 0 < σ (r - 1) ^ 2 - σ r ^ 2 := by
    have := h.nonneg r
    nlinarith
  have hJpos : 0 ≤ ∑ i ∈ J, (1 - a i) := Finset.sum_nonneg fun i _ => by linarith [ha1 i]
  rw [hsplit, hC1P, hexp, hIco] at hle
  have hprod : (σ (r - 1) ^ 2 - σ r ^ 2) * ∑ i ∈ J, (1 - a i) ≤ -‖(C - Ĉ) * P‖ ^ 2 := by
    linarith
  have hX : ‖(C - Ĉ) * P‖ ^ 2 ≤ 0 := by nlinarith [mul_nonneg hgap2.le hJpos]
  have hJ0 : ∑ i ∈ J, (1 - a i) ≤ 0 :=
    le_of_not_gt fun hc => by nlinarith [mul_pos hgap2 hc, sq_nonneg ‖(C - Ĉ) * P‖]
  -- consequences: `Ĉ = C P`, and `P vᵢ = vᵢ` for `i < r`
  have hĈCP : Ĉ = C * P := by
    have h0 : (C - Ĉ) * P = 0 := by
      rw [← norm_eq_zero]
      nlinarith [norm_nonneg ((C - Ĉ) * P)]
    rw [Matrix.sub_mul, hĈP, sub_eq_zero] at h0
    exact h0.symm
  have ha_one : ∀ i : Fin p, (i : ℕ) < r → a i = 1 := fun i hi => by
    have hle' := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by linarith [ha1 j]).1
      (le_antisymm hJ0 hJpos) i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    linarith
  have hPv : ∀ i : Fin n, toEuclideanLin P (v i) = if (i : ℕ) < r then v i else 0 := by
    intro i
    split_ifs with hi
    · -- `‖P vᵢ‖ = 1 = ‖vᵢ‖`, so `(1 - P) vᵢ = 0`
      have hip : (i : ℕ) < p := lt_of_lt_of_le hi hmr.le
      have h1 := ha_one ⟨i, hip⟩ hi
      have h2 := hab i
      have hci : Fin.castLE hpn ⟨i, hip⟩ = i := Fin.ext rfl
      simp only [ha, hci] at h1
      have h3 : toEuclideanLin (1 - P) (v i) = 0 :=
        norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (by linarith))
      rw [map_sub, LinearMap.sub_apply, toEuclideanLin_one, LinearMap.id_apply,
        sub_eq_zero] at h3
      exact h3.symm
    · -- the count leaves no room off the first `r`
      have hsplitN : ∑ j : Fin n, ‖toEuclideanLin P (v j)‖ ^ 2 =
          ∑ j ∈ (Finset.univ.filter fun j : Fin n => (j : ℕ) < r),
            ‖toEuclideanLin P (v j)‖ ^ 2 +
          ∑ j ∈ (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < r),
            ‖toEuclideanLin P (v j)‖ ^ 2 :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      have htop : ∑ j ∈ (Finset.univ.filter fun j : Fin n => (j : ℕ) < r),
          ‖toEuclideanLin P (v j)‖ ^ 2 = r := by
        rw [Finset.sum_congr rfl fun j hj => ?_, Finset.sum_const, nsmul_eq_mul, mul_one,
          Fin.card_filter_val_lt, min_eq_right (hmr.le.trans hpn)]
        have hj' := (Finset.mem_filter.1 hj).2
        have hjp : (j : ℕ) < p := lt_of_lt_of_le hj' hmr.le
        have := ha_one ⟨j, hjp⟩ hj'
        simp only [ha] at this
        rwa [show Fin.castLE hpn ⟨j, hjp⟩ = j from Fin.ext rfl] at this
      have hrest : ∑ j ∈ (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < r),
          ‖toEuclideanLin P (v j)‖ ^ 2 ≤ 0 := by linarith
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1
        (le_antisymm hrest (Finset.sum_nonneg fun j _ => sq_nonneg _)) i
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hzero)
  rw [hĈCP]
  exact mul_eq_svdTruncation_of_toEuclideanLin h hPv

end EckartYoungEquality

/-! ### Subset selection -/

section SubsetSelection

variable {M N : ℕ} {A : Matrix (Fin M) (Fin N) 𝕜} {U : Matrix (Fin M) (Fin M) 𝕜} {σ : ℕ → ℝ}
  {V : Matrix (Fin N) (Fin N) 𝕜}

/-- Scaling the coordinates by numbers of modulus at least `c ≥ 0` stretches by at least `c`. -/
private theorem mul_norm_le_norm_toLp_mul {r : ℕ} {s : Fin r → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ i, c ≤ s i) (d : Fin r → 𝕜) :
    c * ‖(WithLp.toLp 2 d : EuclideanSpace 𝕜 (Fin r))‖ ≤
      ‖(WithLp.toLp 2 fun i => (s i : 𝕜) * d i : EuclideanSpace 𝕜 (Fin r))‖ := by
  have h := PiLp.norm_toLp_le_mul_norm_toLp 2 zero_le_one
    (y := (c : 𝕜) • d) (z := fun i => (s i : 𝕜) * d i) fun i => by
      rw [one_mul, Pi.smul_apply, norm_smul, norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal,
        abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_right ((hs i).trans (le_abs_self _)) (norm_nonneg _)
  rwa [one_mul, WithLp.toLp_smul, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hc] at h

open scoped Matrix.Norms.L2Operator in
/-- **The lower bound of SVD-based subset selection** ([golub2013matrix] Theorem 5.5.2, lower
bound):
let `IsSVD A U σ V`, `π` a permutation of the columns, `B₁` the first `r` columns of `A P`
(`(A P) i j = A i (π j)`) and `Ṽ₁₁` the leading `r × r` block of `Pᵀ V`, assumed invertible. Then
`σ_{r-1}(A) ≤ ‖Ṽ₁₁⁻¹‖₂ σ_{r-1}(B₁)` (the book's `σ_r(A)/‖Ṽ₁₁⁻¹‖₂ ≤ σ_r(B₁)`, 1-based). For
`w ∈ 𝕜^r`, `‖B₁ w‖ = ‖Σ Vᴴ P [w; 0]‖ ≥ σ_{r-1} ‖Ṽ₁₁ᴴ w‖ ≥ σ_{r-1} ‖w‖ / ‖Ṽ₁₁⁻¹‖₂`, and the least
stretch of `B₁` is `σ_{r-1}(B₁)`. The upper bound `σ_{r-1}(B₁) ≤ σ_{r-1}(A)` is
`Matrix.sortedSingularValues_submatrix_le`. -/
theorem IsSVD.sortedSingularValues_le_mul_submatrix (h : IsSVD A U σ V) (π : Equiv.Perm (Fin N))
    {r : ℕ} (hr0 : 0 < r) (hrM : r ≤ M) (hrN : r ≤ N)
    (hV : IsUnit ((V.submatrix π id).submatrix (Fin.castLE hrN) (Fin.castLE hrN))) :
    A.sortedSingularValues (r - 1) ≤
      ‖((V.submatrix π id).submatrix (Fin.castLE hrN) (Fin.castLE hrN))⁻¹‖ *
        ((A.submatrix id π).submatrix id (Fin.castLE hrN)).sortedSingularValues (r - 1) := by
  set e : Fin r → Fin N := fun i => π (Fin.castLE hrN i) with he
  have he_inj : Function.Injective e := π.injective.comp (Fin.castLE_injective hrN)
  set V₁₁ := (V.submatrix π id).submatrix (Fin.castLE hrN) (Fin.castLE hrN) with hV₁₁
  set B₁ := (A.submatrix id π).submatrix id (Fin.castLE hrN) with hB₁
  have hB₁e : B₁ = A.submatrix id e := rfl
  have hVe : V₁₁ᴴ = (star V).submatrix (Fin.castLE hrN) e := by
    ext i j
    simp [hV₁₁, he, star_eq_conjTranspose]
  have hVu : IsUnit V₁₁ᴴ := (isUnit_conjTranspose _).2 hV
  have hσA : A.sortedSingularValues (r - 1) = σ (r - 1) :=
    (h.singularValues_eq (by omega) (by omega)).symm
  set s := σ (r - 1) with hs
  have hs0 : 0 ≤ s := h.nonneg _
  have hsvd : A = U * (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin M) (Fin N) 𝕜) *
      star V := h.eq_mul_mul_star
  -- the key estimate: `s ‖w‖ ≤ ‖Ṽ₁₁⁻¹‖ ‖B₁ w‖`
  have key : ∀ w : EuclideanSpace 𝕜 (Fin r), s * ‖w‖ ≤ ‖V₁₁⁻¹‖ * ‖toEuclideanLin B₁ w‖ := by
    intro w
    set z := Function.extend e (WithLp.ofLp w) 0 with hz
    set c := star V *ᵥ z with hc
    have hBw : toEuclideanLin B₁ w =
        WithLp.toLp 2 (U *ᵥ ((rectDiagonal fun i => ((σ i : ℝ) : 𝕜)) *ᵥ c)) := by
      rw [toEuclideanLin_apply, hB₁e, submatrix_mulVec_eq_comp_mulVec_extend A id he_inj,
        Function.comp_id, hsvd, ← mulVec_mulVec, ← mulVec_mulVec]
    have hVw : V₁₁ᴴ *ᵥ WithLp.ofLp w = c ∘ Fin.castLE hrN := by
      rw [hVe, submatrix_mulVec_eq_comp_mulVec_extend _ _ he_inj]
    have hdiag : (rectDiagonal (fun i => ((σ i : ℝ) : 𝕜)) *ᵥ c) ∘ Fin.castLE hrM =
        fun i : Fin r => ((σ i : ℝ) : 𝕜) * (c ∘ Fin.castLE hrN) i := by
      funext i
      rw [Function.comp_apply, rectDiagonal_mulVec _ _ _ (by simp; omega)]
      rfl
    have h1 : s * ‖(WithLp.toLp 2 (c ∘ Fin.castLE hrN) : EuclideanSpace 𝕜 (Fin r))‖ ≤
        ‖toEuclideanLin B₁ w‖ := by
      rw [hBw, norm_toLp_mulVec_of_mem_unitaryGroup h.mem_unitaryGroup_left]
      refine le_trans ?_ (PiLp.norm_toLp_comp_le 2 (Fin.castLE_injective hrM) _)
      rw [hdiag]
      exact mul_norm_le_norm_toLp_mul hs0 (fun i => h.antitone (Nat.le_sub_one_of_lt i.isLt)) _
    have h2 : ‖w‖ ≤
        ‖V₁₁⁻¹‖ * ‖(WithLp.toLp 2 (c ∘ Fin.castLE hrN) : EuclideanSpace 𝕜 (Fin r))‖ := by
      have hw := toEuclideanLin_nonsing_inv_mul_apply hVu w
      have hn : ‖V₁₁ᴴ⁻¹‖ = ‖V₁₁⁻¹‖ := by
        rw [← conjTranspose_nonsing_inv, l2_opNorm_conjTranspose]
      rw [← hVw, ← hn]
      calc ‖w‖ = ‖toEuclideanLin V₁₁ᴴ⁻¹ (toEuclideanLin V₁₁ᴴ w)‖ := by rw [hw]
        _ ≤ _ := norm_toEuclideanLin_apply_le _ _
    calc s * ‖w‖ ≤ s * (‖V₁₁⁻¹‖ *
          ‖(WithLp.toLp 2 (c ∘ Fin.castLE hrN) : EuclideanSpace 𝕜 (Fin r))‖) :=
          mul_le_mul_of_nonneg_left h2 hs0
      _ = ‖V₁₁⁻¹‖ * (s * ‖(WithLp.toLp 2 (c ∘ Fin.castLE hrN) : EuclideanSpace 𝕜 (Fin r))‖) := by
          ring
      _ ≤ ‖V₁₁⁻¹‖ * ‖toEuclideanLin B₁ w‖ := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  rw [hσA]
  rcases (norm_nonneg V₁₁⁻¹).eq_or_lt with h0 | hpos
  · -- a zero inverse is impossible, unless `s = 0`
    have hk := key (EuclideanSpace.single ⟨0, hr0⟩ 1)
    rw [← h0, zero_mul, PiLp.norm_single, norm_one, mul_one] at hk
    rw [← h0, zero_mul]
    exact hk
  · have hfin : finrank 𝕜 (⊤ : Submodule 𝕜 (EuclideanSpace 𝕜 (Fin r))) = r - 1 + 1 := by
      rw [finrank_top, finrank_euclideanSpace_fin]
      omega
    have hc := (toEuclideanLin B₁).le_singularValues_of_mul_norm_le (c := s / ‖V₁₁⁻¹‖)
      hfin.ge fun w _ => by
        rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        linarith [key w]
    rw [div_le_iff₀ hpos] at hc
    change s ≤ ‖V₁₁⁻¹‖ * (toEuclideanLin B₁).singularValues (r - 1)
    linarith

end SubsetSelection

/-! ### Perturbation of a singular subspace pair -/

section SingularSubspacePair

open scoped Matrix.Norms.Frobenius

/-- A separation survives perturbations of both sides: if `δ ≤ |a − b|`, `|a' − a| ≤ ε₁` and
`|b' − b| ≤ ε₂`, then `δ − (ε₁ + ε₂) ≤ |a' − b'|`. -/
private theorem le_abs_sub_of_abs_sub_le {a b a' b' δ ε₁ ε₂ : ℝ} (h : δ ≤ |a - b|)
    (ha : |a' - a| ≤ ε₁) (hb : |b' - b| ≤ ε₂) : δ - (ε₁ + ε₂) ≤ |a' - b'| := by
  have h1 := abs_sub_abs_le_abs_sub (a - b) (a' - b')
  have h2 : |a - b - (a' - b')| ≤ ε₁ + ε₂ := by
    rw [abs_le] at ha hb ⊢
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  linarith

/-- `|s − t| ≤ |s + t|` for nonnegative `s`, `t`. -/
private theorem abs_sub_le_abs_add_of_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |s - t| ≤ |s + t| := by
  rw [abs_of_nonneg (add_nonneg hs ht)]
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- The eigenvalues of the Hermitian dilation of a square matrix are `±` its singular values. -/
private theorem exists_eigenvalues₀_hermitianDilation_eq {k : Type*} [Fintype k]
    [DecidableEq k] (B : Matrix k k 𝕜) (h : (hermitianDilation B).IsHermitian)
    (b : Fin (Fintype.card (k ⊕ k))) : ∃ i < Fintype.card k,
      h.eigenvalues₀ b = B.sortedSingularValues i ∨
        h.eigenvalues₀ b = -B.sortedSingularValues i := by
  have hb := b.isLt
  have hK : Fintype.card (k ⊕ k) = Fintype.card k + Fintype.card k := Fintype.card_sum
  rw [IsHermitian.eigenvalues₀_hermitianDilation]
  by_cases hbk : (b : ℕ) < Fintype.card k
  · refine ⟨b, hbk, Or.inl ?_⟩
    rw [B.sortedSingularValues_eq_zero_of_min_le (k := Fintype.card (k ⊕ k) - 1 - b)
      (by rw [min_self]; omega), sub_zero]
  · refine ⟨Fintype.card (k ⊕ k) - 1 - b, by omega, Or.inr ?_⟩
    rw [B.sortedSingularValues_eq_zero_of_min_le (k := (b : ℕ)) (by rw [min_self]; omega),
      zero_sub]

/-- The eigenvalues of the Hermitian dilation of a rectangular matrix are `±` its singular values,
or `0` when the matrix is not square. -/
private theorem eigenvalues₀_hermitianDilation_cases {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] (B : Matrix q p 𝕜) (h : (hermitianDilation B).IsHermitian)
    (a : Fin (Fintype.card (p ⊕ q))) :
    (∃ j < min (Fintype.card q) (Fintype.card p),
      h.eigenvalues₀ a = B.sortedSingularValues j ∨
        h.eigenvalues₀ a = -B.sortedSingularValues j) ∨
      (h.eigenvalues₀ a = 0 ∧ Fintype.card p ≠ Fintype.card q) := by
  have ha := a.isLt
  have hPQ : Fintype.card (p ⊕ q) = Fintype.card p + Fintype.card q := Fintype.card_sum
  rw [IsHermitian.eigenvalues₀_hermitianDilation]
  by_cases h1 : (a : ℕ) < min (Fintype.card q) (Fintype.card p)
  · refine Or.inl ⟨a, h1, Or.inl ?_⟩
    rw [B.sortedSingularValues_eq_zero_of_min_le (k := Fintype.card (p ⊕ q) - 1 - a)
      (by omega), sub_zero]
  · by_cases h2 : Fintype.card (p ⊕ q) - 1 - a < min (Fintype.card q) (Fintype.card p)
    · refine Or.inl ⟨_, h2, Or.inr ?_⟩
      rw [B.sortedSingularValues_eq_zero_of_min_le (k := (a : ℕ)) (by omega), zero_sub]
    · refine Or.inr ⟨?_, by omega⟩
      rw [B.sortedSingularValues_eq_zero_of_min_le (k := (a : ℕ)) (by omega),
        B.sortedSingularValues_eq_zero_of_min_le (k := Fintype.card (p ⊕ q) - 1 - a)
          (by omega), sub_self]

/-- **The coupled Sylvester operator of a singular subspace pair is bounded below by the
separation of the singular values**: if the singular values of the square `B₁` and of `B₂` are
`c`-separated, and those of `B₁` are at least `c` when `B₂` is not square, then
`c² (‖P‖² + ‖Q‖²) ≤ ‖B₂ᴴ Q − P B₁ᴴ‖² + ‖B₂ P − Q B₁‖²`. The operator is the Sylvester operator of
the Hermitian dilations of `B₂` and `B₁` on `fromBlocks P 0 0 Q`, whose separation is the least
distance between their spectra (`Matrix.IsHermitian.sep_eq_iInf_abs_eigenvalues_sub`), and those
spectra are `±` the singular values, padded by zeros
(`Matrix.IsHermitian.eigenvalues₀_hermitianDilation`). -/
private theorem sq_mul_le_of_sortedSingularValues_sep {k p q : Type*} [Fintype k] [Fintype p]
    [Fintype q] [DecidableEq k] [DecidableEq p] {B₁ : Matrix k k 𝕜}
    {B₂ : Matrix q p 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (hsep : ∀ i < Fintype.card k, ∀ j < min (Fintype.card q) (Fintype.card p),
      c ≤ |B₁.sortedSingularValues i - B₂.sortedSingularValues j|)
    (hw : Fintype.card p ≠ Fintype.card q →
      ∀ i < Fintype.card k, c ≤ B₁.sortedSingularValues i)
    (P : Matrix p k 𝕜) (Q : Matrix q k 𝕜) :
    c ^ 2 * (‖P‖ ^ 2 + ‖Q‖ ^ 2) ≤ ‖B₂ᴴ * Q - P * B₁ᴴ‖ ^ 2 + ‖B₂ * P - Q * B₁‖ ^ 2 := by
  classical
  set X : Matrix (p ⊕ q) (k ⊕ k) 𝕜 := fromBlocks P 0 0 Q with hXdef
  have hX : ‖X‖ ^ 2 = ‖P‖ ^ 2 + ‖Q‖ ^ 2 := by
    rw [hXdef, frobenius_norm_fromBlocks_sq, norm_zero, norm_zero]
    ring
  have hY : hermitianDilation B₂ * X - X * hermitianDilation B₁ =
      fromBlocks 0 (B₂ᴴ * Q - P * B₁ᴴ) (B₂ * P - Q * B₁) 0 := by
    rw [hXdef, hermitianDilation, hermitianDilation, fromBlocks_multiply, fromBlocks_multiply]
    ext (i | i) (j | j) <;> simp
  have hZ : ‖hermitianDilation B₂ * X - X * hermitianDilation B₁‖ ^ 2 =
      ‖B₂ᴴ * Q - P * B₁ᴴ‖ ^ 2 + ‖B₂ * P - Q * B₁‖ ^ 2 := by
    rw [hY, frobenius_norm_fromBlocks_sq, norm_zero, norm_zero]
    ring
  rw [← hX, ← hZ]
  rcases isEmpty_or_nonempty (p ⊕ q) with hpq | hpq
  · rw [Subsingleton.elim X 0]
    simp
  rcases isEmpty_or_nonempty (k ⊕ k) with hkk | hkk
  · rw [Subsingleton.elim X 0]
    simp
  have h₂ := isHermitian_hermitianDilation B₂
  have h₁ := isHermitian_hermitianDilation B₁
  -- the two spectra are `c`-separated
  have hkey : ∀ (a : Fin (Fintype.card (p ⊕ q))) (b : Fin (Fintype.card (k ⊕ k))),
      c ≤ |h₂.eigenvalues₀ a - h₁.eigenvalues₀ b| := by
    intro a b
    obtain ⟨i, hi, hb⟩ := exists_eigenvalues₀_hermitianDilation_eq B₁ h₁ b
    have hσ := B₁.sortedSingularValues_nonneg i
    rcases eigenvalues₀_hermitianDilation_cases B₂ h₂ a with ⟨j, hj, ha⟩ | ⟨ha, hpq'⟩
    · have hγ := B₂.sortedSingularValues_nonneg j
      have hs := hsep i hi j hj
      rcases hb with hb | hb <;> rcases ha with ha | ha <;> rw [hb, ha]
      · rwa [abs_sub_comm]
      · rw [show -B₂.sortedSingularValues j - B₁.sortedSingularValues i =
          -(B₁.sortedSingularValues i + B₂.sortedSingularValues j) by ring, abs_neg]
        exact hs.trans (abs_sub_le_abs_add_of_nonneg hσ hγ)
      · rw [sub_neg_eq_add, add_comm]
        exact hs.trans (abs_sub_le_abs_add_of_nonneg hσ hγ)
      · rwa [sub_neg_eq_add, neg_add_eq_sub]
    · rcases hb with hb | hb <;> rw [hb, ha]
      · rw [zero_sub, abs_neg, abs_of_nonneg hσ]
        exact hw hpq' i hi
      · rw [zero_sub, neg_neg, abs_of_nonneg hσ]
        exact hw hpq' i hi
  have hsepc : c ≤ sep (hermitianDilation B₂) (hermitianDilation B₁) := by
    rw [h₂.sep_eq_iInf_abs_eigenvalues_sub h₁]
    exact le_ciInf fun a => le_ciInf fun b =>
      hkey ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm a)
        ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm b)
  have hmul := sep_mul_norm_le (A := hermitianDilation B₂) (B := hermitianDilation B₁) X
  calc c ^ 2 * ‖X‖ ^ 2 = (c * ‖X‖) ^ 2 := by ring
    _ ≤ (sep (hermitianDilation B₂) (hermitianDilation B₁) * ‖X‖) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hc (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hsepc (norm_nonneg _)) 2
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (sep_nonneg _ _) (norm_nonneg _)) hmul 2

/-- The scalar estimate behind the Lipschitz bound of the quadratic part:
`(η (a X + b Y))² + (η (b X + a Y))² ≤ (η (X + Y))² (a² + b²)`. -/
private theorem sq_add_sq_le_of_le_mul {d₁ d₂ a b X Y η : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hd₁0 : 0 ≤ d₁) (hd₂0 : 0 ≤ d₂)
    (hd₁ : d₁ ≤ η * (a * X + b * Y)) (hd₂ : d₂ ≤ η * (b * X + a * Y)) :
    d₁ ^ 2 + d₂ ^ 2 ≤ (η * (X + Y)) ^ 2 * (a ^ 2 + b ^ 2) := by
  have h1 := pow_le_pow_left₀ hd₁0 hd₁ 2
  have h2 := pow_le_pow_left₀ hd₂0 hd₂ 2
  have h3 : (a * X + b * Y) ^ 2 + (b * X + a * Y) ^ 2 ≤ (a ^ 2 + b ^ 2) * (X + Y) ^ 2 := by
    have := mul_nonneg (mul_nonneg hX hY) (sq_nonneg (a - b))
    nlinarith
  calc d₁ ^ 2 + d₂ ^ 2 ≤ (η * (a * X + b * Y)) ^ 2 + (η * (b * X + a * Y)) ^ 2 :=
        add_le_add h1 h2
    _ = η ^ 2 * ((a * X + b * Y) ^ 2 + (b * X + a * Y) ^ 2) := by ring
    _ ≤ η ^ 2 * ((a ^ 2 + b ^ 2) * (X + Y) ^ 2) := mul_le_mul_of_nonneg_left h3 (sq_nonneg η)
    _ = _ := by ring

/-- The Frobenius norm of a triple product. -/
private theorem frobenius_norm_mul_mul_le {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c]
    [Fintype d] (X : Matrix a b 𝕜) (Y : Matrix b c 𝕜) (Z : Matrix c d 𝕜) :
    ‖X * Y * Z‖ ≤ ‖X‖ * ‖Y‖ * ‖Z‖ :=
  (frobenius_norm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (frobenius_norm_mul _ _) (norm_nonneg _))

/-- `‖X C Y − X' C Y'‖ ≤ η (‖X − X'‖ ‖Y‖ + ‖X'‖ ‖Y − Y'‖)` for `‖C‖ ≤ η`. -/
private theorem frobenius_norm_mul_mul_sub_le {a b c d : Type*} [Fintype a] [Fintype b]
    [Fintype c] [Fintype d] {C : Matrix b c 𝕜} {η : ℝ} (hC : ‖C‖ ≤ η) (X X' : Matrix a b 𝕜)
    (Y Y' : Matrix c d 𝕜) :
    ‖X * C * Y - X' * C * Y'‖ ≤ η * (‖X - X'‖ * ‖Y‖ + ‖X'‖ * ‖Y - Y'‖) := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hC
  rw [show X * C * Y - X' * C * Y' = (X - X') * C * Y + X' * C * (Y - Y') by
    simp only [Matrix.sub_mul, Matrix.mul_sub]; abel]
  refine (norm_add_le _ _).trans ?_
  have e1 := frobenius_norm_mul_mul_le (X - X') C Y
  have e2 := frobenius_norm_mul_mul_le X' C (Y - Y')
  have f1 : ‖X - X'‖ * ‖C‖ * ‖Y‖ ≤ ‖X - X'‖ * η * ‖Y‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (norm_nonneg _)) (norm_nonneg _)
  have f2 : ‖X'‖ * ‖C‖ * ‖Y - Y'‖ ≤ ‖X'‖ * η * ‖Y - Y'‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (norm_nonneg _)) (norm_nonneg _)
  linarith [show η * (‖X - X'‖ * ‖Y‖ + ‖X'‖ * ‖Y - Y'‖) =
    ‖X - X'‖ * η * ‖Y‖ + ‖X'‖ * η * ‖Y - Y'‖ by ring]

/-- **The quadratic part of the coupled equations is Lipschitz on balls**:
`[P; Q] ↦ [P C Q; Q D P]` with `‖C‖, ‖D‖ ≤ η` satisfies
`‖φ x − φ y‖ ≤ η (‖x‖ + ‖y‖) ‖x − y‖` in the Frobenius norm. -/
private theorem frobenius_norm_fromRows_quadratic_sub_le {k p q : Type*} [Fintype k] [Fintype p]
    [Fintype q] {C : Matrix k q 𝕜} {D : Matrix k p 𝕜} {η : ℝ} (hC : ‖C‖ ≤ η) (hD : ‖D‖ ≤ η)
    (P P' : Matrix p k 𝕜) (Q Q' : Matrix q k 𝕜) :
    ‖fromRows (P * C * Q - P' * C * Q') (Q * D * P - Q' * D * P')‖ ≤
      η * (‖fromRows P Q‖ + ‖fromRows P' Q'‖) * ‖fromRows (P - P') (Q - Q')‖ := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hC
  obtain ⟨hP, hQ⟩ := frobenius_norm_le_fromRows P Q
  obtain ⟨hP', hQ'⟩ := frobenius_norm_le_fromRows P' Q'
  have d₁ := frobenius_norm_mul_mul_sub_le hC P P' Q Q'
  have d₂ := frobenius_norm_mul_mul_sub_le hD Q Q' P P'
  -- bound the norms of the factors by those of the stacked matrices
  have g₁ : ‖P - P'‖ * ‖Q‖ + ‖P'‖ * ‖Q - Q'‖ ≤
      ‖P - P'‖ * ‖fromRows P Q‖ + ‖Q - Q'‖ * ‖fromRows P' Q'‖ := by
    have := mul_le_mul_of_nonneg_left hQ (norm_nonneg (P - P'))
    have := mul_le_mul_of_nonneg_right hP' (norm_nonneg (Q - Q'))
    linarith
  have g₂ : ‖Q - Q'‖ * ‖P‖ + ‖Q'‖ * ‖P - P'‖ ≤
      ‖Q - Q'‖ * ‖fromRows P Q‖ + ‖P - P'‖ * ‖fromRows P' Q'‖ := by
    have := mul_le_mul_of_nonneg_left hP (norm_nonneg (Q - Q'))
    have := mul_le_mul_of_nonneg_right hQ' (norm_nonneg (P - P'))
    linarith
  have s := sq_add_sq_le_of_le_mul (norm_nonneg (fromRows P Q)) (norm_nonneg (fromRows P' Q'))
    (norm_nonneg _) (norm_nonneg _)
    (d₁.trans (mul_le_mul_of_nonneg_left g₁ hη)) (d₂.trans (mul_le_mul_of_nonneg_left g₂ hη))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (mul_nonneg hη
    (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _)) two_ne_zero).1 ?_
  rw [frobenius_norm_fromRows_sq, mul_pow, frobenius_norm_fromRows_sq (P - P')]
  exact s

variable {k p q : Type*} [Fintype k] [Fintype p] [Fintype q]

/-- The coupled Sylvester operator `[P; Q] ↦ [B₂ᴴ Q − P B₁ᴴ; B₂ P − Q B₁]` of a singular subspace
pair, on stacked matrices. -/
private def pairSylvester (B₁ : Matrix k k 𝕜) (B₂ : Matrix q p 𝕜) :
    Matrix (p ⊕ q) k 𝕜 →ₗ[𝕜] Matrix (p ⊕ q) k 𝕜 where
  toFun x := fromRows (B₂ᴴ * x.toRows₂ - x.toRows₁ * B₁ᴴ) (B₂ * x.toRows₁ - x.toRows₂ * B₁)
  map_add' x y := by
    have h₁ : (x + y).toRows₁ = x.toRows₁ + y.toRows₁ := rfl
    have h₂ : (x + y).toRows₂ = x.toRows₂ + y.toRows₂ := rfl
    rw [h₁, h₂, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
    ext (i | i) j <;>
      simp only [fromRows_apply_inl, fromRows_apply_inr, add_apply, sub_apply] <;> abel
  map_smul' c x := by
    have h₁ : (c • x).toRows₁ = c • x.toRows₁ := rfl
    have h₂ : (c • x).toRows₂ = c • x.toRows₂ := rfl
    rw [h₁, h₂, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
    ext (i | i) j <;>
      simp only [fromRows_apply_inl, fromRows_apply_inr, smul_apply, sub_apply,
        RingHom.id_apply, smul_sub]

private theorem pairSylvester_fromRows (B₁ : Matrix k k 𝕜) (B₂ : Matrix q p 𝕜)
    (P : Matrix p k 𝕜) (Q : Matrix q k 𝕜) :
    pairSylvester B₁ B₂ (fromRows P Q) = fromRows (B₂ᴴ * Q - P * B₁ᴴ) (B₂ * P - Q * B₁) := by
  change fromRows (B₂ᴴ * (fromRows P Q).toRows₂ - (fromRows P Q).toRows₁ * B₁ᴴ)
    (B₂ * (fromRows P Q).toRows₁ - (fromRows P Q).toRows₂ * B₁) = _
  rw [toRows₁_fromRows, toRows₂_fromRows]

/-- The sum of two stacked matrices is stacked blockwise. -/
private theorem fromRows_add_fromRows {a b c : Type*} (P P' : Matrix a c 𝕜)
    (Q Q' : Matrix b c 𝕜) : fromRows P Q + fromRows P' Q' = fromRows (P + P') (Q + Q') := by
  ext (i | i) j <;> rfl

/-- The difference of two stacked matrices is stacked blockwise. -/
private theorem fromRows_sub_fromRows {a b c : Type*} (P P' : Matrix a c 𝕜)
    (Q Q' : Matrix b c 𝕜) : fromRows P Q - fromRows P' Q' = fromRows (P - P') (Q - Q') := by
  ext (i | i) j <;> rfl

/-- **The coupled quadratic equations of a singular subspace pair**: if the singular values of
`B₁₁` and `B₂₂` are `δ`-separated (and those of `B₁₁` are at least `δ` when `B₂₂` is not square),
and `‖B₁₂‖² + ‖B₂₁‖² ≤ ε²` with `4 ε² < δ²`, there are `P`, `Q` with `‖[P; Q]‖ ≤ 2 ε / δ` solving
`B₂₂ᴴ Q − P B₁₁ᴴ − P B₂₁ᴴ Q = −B₁₂ᴴ` and `B₂₂ P − Q B₁₁ − Q B₁₂ P = −B₂₁`. -/
private theorem exists_pair_quadratic [DecidableEq k] [DecidableEq p] {B₁₁ : Matrix k k 𝕜}
    {B₁₂ : Matrix k p 𝕜} {B₂₁ : Matrix q k 𝕜} {B₂₂ : Matrix q p 𝕜} {δ ε : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i < Fintype.card k, ∀ j < min (Fintype.card q) (Fintype.card p),
      δ ≤ |B₁₁.sortedSingularValues i - B₂₂.sortedSingularValues j|)
    (hw : Fintype.card p ≠ Fintype.card q →
      ∀ i < Fintype.card k, δ ≤ B₁₁.sortedSingularValues i)
    (hoff : ‖B₁₂‖ ^ 2 + ‖B₂₁‖ ^ 2 ≤ ε ^ 2) (hε : 0 ≤ ε) (hεδ : 4 * ε ^ 2 < δ ^ 2) :
    ∃ (P : Matrix p k 𝕜) (Q : Matrix q k 𝕜), ‖fromRows P Q‖ ≤ 2 * ε / δ ∧
      B₂₂ᴴ * Q - P * B₁₁ᴴ - P * B₂₁ᴴ * Q = -B₁₂ᴴ ∧
      B₂₂ * P - Q * B₁₁ - Q * B₁₂ * P = -B₂₁ := by
  have h₁₂ : ‖B₁₂‖ ≤ ε := (pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero).1 (by
    nlinarith [sq_nonneg ‖B₂₁‖])
  have h₂₁ : ‖B₂₁ᴴ‖ ≤ ε := by
    rw [frobenius_norm_conjTranspose]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero).1 (by
      nlinarith [sq_nonneg ‖B₁₂‖])
  have hL : ∀ x, δ * ‖x‖ ≤ ‖pairSylvester B₁₁ B₂₂ x‖ := by
    intro x
    rw [← fromRows_toRows x, pairSylvester_fromRows]
    refine (pow_le_pow_iff_left₀ (mul_nonneg hδ.le (norm_nonneg _)) (norm_nonneg _)
      two_ne_zero).1 ?_
    rw [mul_pow, frobenius_norm_fromRows_sq, frobenius_norm_fromRows_sq]
    exact sq_mul_le_of_sortedSingularValues_sep hδ.le hsep hw _ _
  let φ : Matrix (p ⊕ q) k 𝕜 → Matrix (p ⊕ q) k 𝕜 := fun x =>
    fromRows (-(x.toRows₁ * B₂₁ᴴ * x.toRows₂)) (-(x.toRows₂ * B₁₂ * x.toRows₁))
  have hφ₁ : ∀ P Q, φ (fromRows P Q) = fromRows (-(P * B₂₁ᴴ * Q)) (-(Q * B₁₂ * P)) :=
    fun P Q => by simp only [φ, toRows₁_fromRows, toRows₂_fromRows]
  have hφ0 : φ 0 = 0 := by
    rw [← fromRows_zero, hφ₁]
    simp only [Matrix.zero_mul, neg_zero, fromRows_zero]
  have hφ : ∀ x y, ‖φ x - φ y‖ ≤ ε * (‖x‖ + ‖y‖) * ‖x - y‖ := by
    intro x y
    rw [← fromRows_toRows x, ← fromRows_toRows y, hφ₁, hφ₁, fromRows_sub_fromRows,
      fromRows_sub_fromRows, neg_sub_neg, neg_sub_neg, ← norm_neg (fromRows _ _),
      fromRows_neg, neg_sub, neg_sub]
    exact frobenius_norm_fromRows_quadratic_sub_le h₂₁ h₁₂ _ _ _ _
  have hg : ‖fromRows (-B₁₂ᴴ) (-B₂₁)‖ ≤ ε := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero).1 ?_
    rw [frobenius_norm_fromRows_sq, norm_neg, norm_neg, frobenius_norm_conjTranspose]
    exact hoff
  obtain ⟨x, hx, hxn⟩ := (pairSylvester B₁₁ B₂₂).exists_apply_add_eq_of_quadratic_of_le_norm hδ
    hL hg hφ0 hφ (by nlinarith)
  rw [← fromRows_toRows x] at hx hxn
  rw [pairSylvester_fromRows, hφ₁, fromRows_add_fromRows] at hx
  obtain ⟨e₁, e₂⟩ := fromRows_inj hx
  exact ⟨x.toRows₁, x.toRows₂, hxn, by rw [← e₁, sub_eq_add_neg], by rw [← e₂, sub_eq_add_neg]⟩

/-- A solution of the coupled equation makes `[1; P]` map into `[1; Q]`:
`[B₁₁ B₁₂; B₂₁ B₂₂] [1; P] = [1; Q] (B₁₁ + B₁₂ P)` when `B₂₂ P − Q B₁₁ − Q B₁₂ P = −B₂₁`. -/
private theorem fromBlocks_mul_fromRows_one_eq {a b c : Type*} [Fintype a] [Fintype c]
    [DecidableEq a] {B₁₁ : Matrix a a 𝕜} {B₁₂ : Matrix a c 𝕜} {B₂₁ : Matrix b a 𝕜}
    {B₂₂ : Matrix b c 𝕜} {P : Matrix c a 𝕜} {Q : Matrix b a 𝕜}
    (h : B₂₂ * P - Q * B₁₁ - Q * B₁₂ * P = -B₂₁) :
    fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ * fromRows 1 P = fromRows 1 Q * (B₁₁ + B₁₂ * P) := by
  rw [fromBlocks_mul_fromRows, fromRows_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
  congr 1
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← sub_eq_zero,
    show B₂₁ + B₂₂ * P - (Q * B₁₁ + Q * B₁₂ * P) =
      B₂₁ + (B₂₂ * P - Q * B₁₁ - Q * B₁₂ * P) by abel, h, add_neg_cancel]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [DecidableEq k]
  [DecidableEq p] [DecidableEq q]

/-- **The perturbation of a singular subspace pair** ([golub2013matrix] Theorem 8.6.5, corrected;
G. W. Stewart, SIAM Rev. 15 (1973), Theorem 6.4; P.-Å. Wedin, BIT 12 (1972)), in the coordinates
of the pair: let `U : Matrix m (k ⊕ q) 𝕜` and `V : Matrix n (k ⊕ p) 𝕜` be unitary (`Uᴴ U = 1`,
`U Uᴴ = 1`, and likewise for `V`) with `Uᴴ A V = [A₁₁ 0; 0 A₂₂]`, i.e. the first columns `V₁`,
`U₁` span a singular subspace pair of `A`. Let the singular values of `A₁₁` and `A₂₂` be
`δ`-separated, `δ ≤ |σ_i(A₁₁) − σ_j(A₂₂)|`, and, when `A₂₂` is not square, let
`δ ≤ σ_i(A₁₁)` (**Wedin's condition**: the `|card p − card q|` further zero singular values of
`A₂₂` count too; without it the book's statement fails for `m > n`: for `A = [0 0; 0 1; 0 0]`,
`U = V = 1` with one leading column and `E = ε e₃e₁ᵀ`, `0 < ε ≤ 1/5`, the only one-dimensional
singular subspace pairs of `A + E` are `(span e₁, span e₃)` and `(span e₂, span e₂)`, neither of
the form below). If `‖E‖_F ≤ δ / 5`, there are
`P : Matrix p k 𝕜` and `Q : Matrix q k 𝕜` with `‖[Q; P]‖_F ≤ 4 ‖E‖_F / δ` such that
`V₁ + V₂ P = V [1; P]` and `U₁ + U₂ Q = U [1; Q]` span a singular subspace pair of `A + E`:
`(A + E) V [1; P] = U [1; Q] M` and `(A + E)ᴴ U [1; Q] = V [1; P] N`. No `m ≥ n` is needed.

With `B = Uᴴ (A + E) V`, the two inclusions are the coupled quadratic equations
`B₂₂ P − Q B₁₁ − Q B₁₂ P = −B₂₁` and `B₂₂ᴴ Q − P B₁₁ᴴ − P B₂₁ᴴ Q = −B₁₂ᴴ` in `x = [P; Q]`, solved
by Stewart's quadratic-equation lemma (`ContinuousLinearEquiv.exists_apply_add_eq_of_quadratic`):
the linear part is bounded below by `δ − 2 ‖E‖_F ≥ 3δ/5` (Weyl's inequality moves each singular
value of `B₁₁`, `B₂₂` by at most `‖E‖_F`), the quadratic part is `‖E‖_F`-Lipschitz on balls, and
the right side has norm at most `‖E‖_F`. -/
theorem exists_singularSubspacePair_perturbation {A E : Matrix m n 𝕜}
    {U : Matrix m (k ⊕ q) 𝕜} {V : Matrix n (k ⊕ p) 𝕜} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hV : Vᴴ * V = 1) (hV' : V * Vᴴ = 1) (h₁₂ : (Uᴴ * A * V).toBlocks₁₂ = 0)
    (h₂₁ : (Uᴴ * A * V).toBlocks₂₁ = 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i < Fintype.card k, ∀ j < min (Fintype.card q) (Fintype.card p),
      δ ≤ |(Uᴴ * A * V).toBlocks₁₁.sortedSingularValues i -
        (Uᴴ * A * V).toBlocks₂₂.sortedSingularValues j|)
    (hw : Fintype.card p ≠ Fintype.card q →
      ∀ i < Fintype.card k, δ ≤ (Uᴴ * A * V).toBlocks₁₁.sortedSingularValues i)
    (hE : ‖E‖ ≤ δ / 5) :
    ∃ (P : Matrix p k 𝕜) (Q : Matrix q k 𝕜), ‖fromRows Q P‖ ≤ 4 * ‖E‖ / δ ∧
      (∃ M, (A + E) * (V * fromRows 1 P) = U * fromRows 1 Q * M) ∧
      ∃ N, (A + E)ᴴ * (U * fromRows 1 Q) = V * fromRows 1 P * N := by
  set A' := Uᴴ * A * V with hA'
  set S := Uᴴ * E * V with hS
  have hε0 : 0 ≤ ‖E‖ := norm_nonneg _
  have hSn : ‖S‖ = ‖E‖ := by
    rw [hS, Matrix.mul_assoc, frobenius_norm_mul_of_conjTranspose_mul_self_eq_one
      (by rw [conjTranspose_conjTranspose]; exact hU'), ← frobenius_norm_conjTranspose (E * V),
      conjTranspose_mul, frobenius_norm_mul_of_conjTranspose_mul_self_eq_one
        (by rw [conjTranspose_conjTranspose]; exact hV'), frobenius_norm_conjTranspose]
  obtain ⟨hS₁₁, hS₂₂, hSoff⟩ := frobenius_norm_toBlocks_le S
  rw [hSn] at hS₁₁ hS₂₂ hSoff
  -- the blocks of `Uᴴ (A + E) V`
  have hB : Uᴴ * (A + E) * V = fromBlocks (A'.toBlocks₁₁ + S.toBlocks₁₁) S.toBlocks₁₂
      S.toBlocks₂₁ (A'.toBlocks₂₂ + S.toBlocks₂₂) := by
    have hA'b : A' = fromBlocks A'.toBlocks₁₁ 0 0 A'.toBlocks₂₂ := by
      rw [← h₁₂, ← h₂₁, fromBlocks_toBlocks]
    rw [Matrix.mul_add, Matrix.add_mul, ← hA', ← hS]
    conv_lhs => rw [hA'b, ← fromBlocks_toBlocks S]
    rw [fromBlocks_add, zero_add, zero_add]
  have hAE : A + E = U * (Uᴴ * (A + E) * V) * Vᴴ := by
    simp only [← Matrix.mul_assoc]
    rw [hU', Matrix.one_mul, Matrix.mul_assoc, hV', Matrix.mul_one]
  rw [hB] at hAE
  -- the perturbed separation `δ' = δ − 2 ‖E‖`
  have hsep' : ∀ i < Fintype.card k, ∀ j < min (Fintype.card q) (Fintype.card p),
      δ - 2 * ‖E‖ ≤ |(A'.toBlocks₁₁ + S.toBlocks₁₁).sortedSingularValues i -
        (A'.toBlocks₂₂ + S.toBlocks₂₂).sortedSingularValues j| := by
    intro i hi j hj
    have h := le_abs_sub_of_abs_sub_le (hsep i hi j hj)
      ((abs_sortedSingularValues_add_sub_le_frobenius_norm A'.toBlocks₁₁ S.toBlocks₁₁ i).trans hS₁₁)
      ((abs_sortedSingularValues_add_sub_le_frobenius_norm A'.toBlocks₂₂ S.toBlocks₂₂ j).trans hS₂₂)
    linarith
  have hw' : Fintype.card p ≠ Fintype.card q →
      ∀ i < Fintype.card k, δ - 2 * ‖E‖ ≤ (A'.toBlocks₁₁ + S.toBlocks₁₁).sortedSingularValues i :=
    fun hpq i hi => by
      have h1 := (abs_sortedSingularValues_add_sub_le_frobenius_norm A'.toBlocks₁₁ S.toBlocks₁₁
        i).trans hS₁₁
      have h2 := hw hpq i hi
      linarith [(abs_le.1 h1).1]
  have hδ' : 3 * δ / 5 ≤ δ - 2 * ‖E‖ := by linarith
  have hδ'0 : 0 < δ - 2 * ‖E‖ := by linarith
  obtain ⟨P, Q, hPQ, e₁, e₂⟩ := exists_pair_quadratic hδ'0 hsep' hw' hSoff hε0 (by
    have h1 := pow_le_pow_left₀ (by linarith) hδ' 2
    have h2 := pow_le_pow_left₀ hε0 hE 2
    nlinarith)
  refine ⟨P, Q, ?_, ⟨A'.toBlocks₁₁ + S.toBlocks₁₁ + S.toBlocks₁₂ * P, ?_⟩,
    ⟨(A'.toBlocks₁₁ + S.toBlocks₁₁)ᴴ + S.toBlocks₂₁ᴴ * Q, ?_⟩⟩
  · -- the size of the solution
    rw [frobenius_norm_fromRows_comm]
    refine hPQ.trans ?_
    rw [div_le_div_iff₀ hδ'0 hδ]
    nlinarith [mul_le_mul_of_nonneg_left hδ' hε0]
  · -- `(A + E) V [1; P] = U [1; Q] M`
    rw [hAE, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul,
      fromBlocks_mul_fromRows_one_eq e₂, ← Matrix.mul_assoc]
  · -- `(A + E)ᴴ U [1; Q] = V [1; P] N`
    rw [hAE, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      fromBlocks_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU,
      Matrix.one_mul, fromBlocks_mul_fromRows_one_eq e₁, ← Matrix.mul_assoc]

end SingularSubspacePair

end Matrix
