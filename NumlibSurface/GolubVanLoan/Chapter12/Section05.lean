import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Tensor.CP
import Numlib.LinearAlgebra.Tensor.HOSVD
import Numlib.LinearAlgebra.Tensor.SingularValue
import Numlib.LinearAlgebra.Tensor.Train
import Numlib.LinearAlgebra.Tensor.Tucker
import NumlibSurface.GolubVanLoan.Chapter12.Section03
import NumlibSurface.GolubVanLoan.Chapter12.Section04

/-!
# Golub–Van Loan §12.5: tensor decompositions and iterations

Surface file for §12.5 of Golub and Van Loan, *Matrix Computations* (4th edition): the SVD
viewpoint (12.5.1)–(12.5.3), the higher-order SVD (Theorem 12.5.1, (12.5.4)–(12.5.10)), truncation
(12.5.11), the Tucker problem (§12.5.3), the CP problem and its alternating least squares updates
((12.5.14)–(12.5.21)), variational singular values and eigenvalues (12.5.22)–(12.5.24), and tensor
trains (12.5.25)–(12.5.29).

## Design

Tensors are chapter 12's `RTensor n` (§12.4), the book's modal unfoldings `𝒜_(k)` its flattened
`modalUnfolding` (columns in the vec order). The book's SVDs are the backbone's
`Matrix.IsSVD A U σ V` (`Uᵀ A V = diag(σ)`, `σ` sorted and nonnegative); the backbone's canonical
HOSVD factors are `Tensor.hosvdFactor`, whose columns are ordered as the column-indexed singular
values `Matrix.singularValues` of the unfolding's transpose. Over `ℝ` the backbone's conjugate
transposes are transposes (`Matrix.conjTranspose_eq_transpose_of_trivial`).

The "Repeat" iterations of the section (Tucker-ALS, CP-ALS, the higher-order power methods) are not
programmed; what each update solves is stated.

## Not formalized here

The "Repeat" iterations themselves; the claim that the truncated HOSVD does not solve the Tucker
problem (no example is given); Complications 1–6 of §12.5.5 (tensor rank: NP-hardness, maximal and
typical ranks, real versus complex rank, degeneracy); the tensor-train counts.
-/

open Matrix

namespace GolubVanLoan.Chapter12

/-! ### The SVD viewpoint (12.5.1)–(12.5.3) -/

section SVD

variable {m n : ℕ}

/-- A real rectangular diagonal matrix with coerced entries is the one with the real entries. -/
private theorem rectDiagonal_ofReal (σ : ℕ → ℝ) :
    (rectDiagonal fun i => ((σ i : ℝ) : ℝ) : Matrix (Fin m) (Fin n) ℝ) = rectDiagonal σ :=
  rfl

/-- The factors of a real SVD are orthogonal: `U Uᵀ = Uᵀ U = I`, `V Vᵀ = Vᵀ V = I`, and
`A = U Σ Vᵀ`, `Uᵀ A = Σ Vᵀ`. -/
theorem isSVD_real_facts {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) :
    U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧ V * Vᵀ = 1 ∧ Vᵀ * V = 1 ∧
      A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ ∧
      Uᵀ * A = (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
  have hU := h.mem_unitaryGroup_left
  have hV := h.mem_unitaryGroup_right
  have h1 : U * Uᵀ = 1 := by
    have := mem_unitaryGroup_iff.1 hU
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have h2 : Uᵀ * U = 1 := by
    have := mem_unitaryGroup_iff'.1 hU
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have h3 : V * Vᵀ = 1 := by
    have := mem_unitaryGroup_iff.1 hV
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have h4 : Vᵀ * V = 1 := by
    have := mem_unitaryGroup_iff'.1 hV
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hA : A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
    have := h.eq_mul_mul_star
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, rectDiagonal_ofReal]
      at this
  refine ⟨h1, h2, h3, h4, hA, ?_⟩
  rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

/-- The Gram matrix of a rectangular diagonal matrix: `(Σ Σᵀ)_{ii} = σ_i²` for `i < n`, and `0`
beyond. -/
theorem rectDiagonal_mul_transpose_apply (σ : ℕ → ℝ) (i : Fin m) :
    ((rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * (rectDiagonal σ)ᵀ : Matrix (Fin m) (Fin m) ℝ)
      i i =
      if (i : ℕ) < n then σ i ^ 2 else 0 := by
  rw [mul_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single ⟨i, hi⟩]
    · simp [rectDiagonal_apply, sq]
    · intro j _ hj
      have : (i : ℕ) ≠ j := fun h => hj (Fin.ext h.symm)
      simp [rectDiagonal_apply, this]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    have : (i : ℕ) ≠ j := fun h => hi (h ▸ j.isLt)
    simp [rectDiagonal_apply, this]

/-- **(12.5.1)–(12.5.2)**: for `A ∈ ℝ^{m×n}` with SVD `A = U Σ Vᵀ` (`Matrix.IsSVD A U σ V`),
`Uᵀ A = Σ Vᵀ`, whose rows `σ_i v_iᵀ` are mutually orthogonal (`(Uᵀ A)(Uᵀ A)ᵀ = Σ Σᵀ` is diagonal)
and nonincreasing in norm. (The book's `v_i T` in (12.5.1) is `v_iᵀ`.) -/
theorem equation_12_5_1 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) :
    A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ ∧
      Uᵀ * A = (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ ∧
      (Uᵀ * A) * (Uᵀ * A)ᵀ = (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * (rectDiagonal σ)ᵀ ∧
      Antitone fun i : Fin m => ∑ j, (Uᵀ * A) i j ^ 2 := by
  obtain ⟨-, -, -, h4, hA, hUA⟩ := (isSVD_real_facts h)
  have hG : (Uᵀ * A) * (Uᵀ * A)ᵀ =
      (rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * (rectDiagonal σ)ᵀ := by
    rw [hUA, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ, h4,
      Matrix.one_mul]
  refine ⟨hA, hUA, hG, ?_⟩
  have hrow : ∀ i, ∑ j, (Uᵀ * A) i j ^ 2 = if (i : ℕ) < n then σ i ^ 2 else 0 := by
    intro i
    rw [← rectDiagonal_mul_transpose_apply, ← hG, mul_apply]
    simp only [transpose_apply, sq]
  intro i i' hii'
  simp only [hrow]
  split_ifs with h1 h2 h2
  · exact pow_le_pow_left₀ (h.nonneg _) (h.antitone (Fin.le_iff_val_le_val.1 hii')) 2
  · exact absurd (lt_of_le_of_lt (Fin.le_iff_val_le_val.1 hii') h1) h2
  · exact sq_nonneg _
  · exact le_rfl

open scoped Matrix.Norms.Frobenius in
/-- **(12.5.3)** and the sentence after it: for `A ∈ ℝ^{m×n}` with an SVD `Uᵀ A V = Σ` and
`r ≤ min(m, n)`, the largest value of `‖QᵀA‖_F²` over the `Q ∈ ℝ^{m×r}` with `QᵀQ = I_r` is
`σ₁² + ⋯ + σ_r²`, "and it can be attained by setting `Q = U(:, 1:r)`" (the book writes the maximum
of `‖QᵀA‖_F` as `σ₁² + ⋯ + σ_r²`, dropping a square). Ky Fan's maximum principle,
`Matrix.isGreatest_frobenius_norm_sq_conjTranspose_mul`, with the diagonal of the SVD identified
with the singular values. -/
theorem equation_12_5_3 {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V) {r : ℕ} (hrm : r ≤ m) (hrn : r ≤ n) :
    IsGreatest ((fun Q : Matrix (Fin m) (Fin r) ℝ => ‖Qᵀ * A‖ ^ 2) '' {Q | Qᵀ * Q = 1})
        (∑ i ∈ Finset.range r, σ i ^ 2) ∧
      ‖(U.submatrix id (Fin.castLE hrm))ᵀ * A‖ ^ 2 = ∑ i ∈ Finset.range r, σ i ^ 2 := by
  have hσ : ∑ i ∈ Finset.range r, σ i ^ 2 =
      ∑ i ∈ Finset.range r, A.sortedSingularValues i ^ 2 :=
    Finset.sum_congr rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [h.singularValues_eq (by omega) (by omega)]
  have hK := isGreatest_frobenius_norm_sq_conjTranspose_mul A (r := r) (by simpa using hrm)
  simp only [conjTranspose_eq_transpose_of_trivial] at hK
  refine ⟨hσ ▸ hK, ?_⟩
  obtain ⟨-, -, -, -, -, hUA⟩ := isSVD_real_facts h
  have hQA : (U.submatrix id (Fin.castLE hrm))ᵀ * A =
      (1 : Matrix (Fin r) (Fin r) ℝ) *
        ((rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ).submatrix (Fin.castLE hrm) id) * Vᵀ := by
    have hsub : (U.submatrix id (Fin.castLE hrm))ᵀ * A = (Uᵀ * A).submatrix (Fin.castLE hrm) id :=
      by ext a b; simp [mul_apply]
    rw [hsub, hUA, Matrix.one_mul]
    ext a b
    simp [mul_apply]
  have hVT : Vᵀ ∈ unitaryGroup (Fin n) ℝ := by
    have := Unitary.star_mem h.mem_unitaryGroup_right
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  rw [hQA, frobenius_norm_unitary_mul_mul_unitary (one_mem _) _ hVT, frobenius_norm_sq_eq_sum_sq,
    ← Fin.sum_univ_eq_sum_range (fun i => σ i ^ 2) r]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single ⟨a, lt_of_lt_of_le a.isLt hrn⟩]
  · simp [rectDiagonal_apply]
  · intro b _ hb
    have : (a : ℕ) ≠ b := fun h => hb (Fin.ext h.symm)
    simp [rectDiagonal_apply, this]
  · simp

end SVD

/-! ### The higher-order SVD (Theorem 12.5.1, (12.5.4)–(12.5.11)) -/

section HOSVD

variable {d : ℕ}

/-- **§12.5.1**, before Theorem 12.5.1: with `U_k` the HOSVD factor of mode `k` (the backbone's
canonical left singular vectors of `𝒜_(k)`, `Tensor.hosvdFactor`) and `ℬ⁽ᵏ⁾ = 𝒜 ×_k U_kᵀ` (the
book's (12.5.5) prints `×_k U_k`, which does not produce the stated unfoldings), the rows of
`ℬ⁽ᵏ⁾_(k)` are mutually orthogonal and the `i`-th has norm `σ_i(𝒜_(k))`: `‖ℬ⁽¹⁾(i, :, :)‖_F =
σ_i(𝒜_(1))` and its siblings, in every mode of a tensor of any order (the book's displayed
unfoldings `ℬ⁽¹⁾_(1) = Σ₁ V₁ᵀ (U₃ ⊗ U₂)ᵀ` are misprints and are not reproduced). -/
theorem hosvd_modeProduct_slices {n : Fin d → ℕ} (A : RTensor n) (k : Fin d) :
    (A.modeProd k (A.hosvdFactor k)ᵀ).modeUnfold k *
        ((A.modeProd k (A.hosvdFactor k)ᵀ).modeUnfold k)ᵀ =
          diagonal (fun i => (A.modeUnfold k)ᵀ.singularValues i ^ 2) ∧
      ∀ i, ∑ c, (A.modeProd k (A.hosvdFactor k)ᵀ).modeUnfold k i c ^ 2 =
        (A.modeUnfold k)ᵀ.singularValues i ^ 2 := by
  have h := Tensor.modeProd_hosvdFactor_row A k
  simp only [conjTranspose_eq_transpose_of_trivial] at h
  refine ⟨h, fun i => ?_⟩
  have := congrFun (congrFun h i) i
  rw [mul_apply, diagonal_apply_eq] at this
  simpa [sq] using this

variable {n : Fin (d + 1) → ℕ}

/-- **Theorem 12.5.1** (HOSVD), (12.5.6)–(12.5.9): for `𝒜 ∈ ℝ^{n₁ × ⋯ × n_d}` and, for every mode
`k`, an SVD `𝒜_(k) = U_k Σ_k V_kᵀ` of the modal unfolding, with `𝒮 = 𝒜 ×₁ U₁ᵀ ⋯ ×_d U_dᵀ`:
`𝒜 = 𝒮 ×₁ U₁ ⋯ ×_d U_d`, equivalently `𝒜 = ∑_j 𝒮(j) U₁(:, j₁) ∘ ⋯ ∘ U_d(:, j_d)`,
`𝒜(i) = ∑_j 𝒮(j) U₁(i₁, j₁) ⋯ U_d(i_d, j_d)` and `vec(𝒜) = (U_d ⊗ ⋯ ⊗ U₁) vec(𝒮)` (the flattened
family product, `Matrix.piKronecker_reindex_finPiFinEquiv`). The proof uses only the orthogonality
of the `U_k`; the SVD matters for (12.5.10), `theorem_12_5_1_b`. -/
theorem theorem_12_5_1 (A : RTensor n) (U : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ)
    (σ : Fin (d + 1) → ℕ → ℝ) (V : ∀ k, Matrix (Fin (∏ j : Fin d, n (k.succAbove j)))
      (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ)
    (h : ∀ k, IsSVD (modalUnfolding A k) (U k) (σ k) (V k)) :
    let S : RTensor n := Tensor.multilinearProd (fun k => (U k)ᵀ) A
    A = Tensor.multilinearProd U S ∧
      A = ∑ j, S j • Tensor.rankOne (κ := fun k => Fin (n k)) (fun k x => U k x (j k)) ∧
      (∀ i, A i = ∑ j, S j * ∏ k, U k (i k) (j k)) ∧
      Tensor.vecFin A = (piKronecker U).reindex finPiFinEquiv finPiFinEquiv *ᵥ Tensor.vecFin S := by
  intro S
  have hUU : ∀ k, U k * (U k)ᵀ = 1 := fun k => (isSVD_real_facts (h k)).1
  have hA : A = Tensor.multilinearProd U S := by
    simp only [S, Tensor.multilinearProd_multilinearProd, hUU, Tensor.multilinearProd_one]
  refine ⟨hA, ?_, fun i => ?_, ?_⟩
  · conv_lhs => rw [hA]
    exact Tensor.multilinearProd_eq_sum_rankOne _ _
  · conv_lhs => rw [hA]
    rw [Tensor.multilinearProd_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · conv_lhs => rw [hA]
    exact Tensor.vecFin_multilinearProd U S

/-- The flattened Kronecker product of the transposes of orthogonal factors is orthogonal. -/
private theorem transpose_mul_reindex_piKronecker {n : Fin d → ℕ}
    (U : ∀ j, Matrix (Fin (n j)) (Fin (n j)) ℝ) (hU : ∀ j, U j * (U j)ᵀ = 1) :
    ((piKronecker fun j => (U j)ᵀ).reindex finPiFinEquiv finPiFinEquiv)ᵀ *
      (piKronecker fun j => (U j)ᵀ).reindex finPiFinEquiv finPiFinEquiv = 1 := by
  rw [reindex_apply, transpose_submatrix, submatrix_mul_equiv, transpose_piKronecker,
    piKronecker_mul_piKronecker]
  simp only [transpose_transpose, hU, piKronecker_one, submatrix_one_equiv]

/-- **Theorem 12.5.1**, (12.5.10): when each `U_k` is the left factor of an SVD of `𝒜_(k)` with
sorted singular values `σ_k`, the rows of `𝒮_(k)` are mutually orthogonal and `‖𝒮_(k)(i, :)‖_F =
σ_i(𝒜_(k))`: `𝒮_(k) 𝒮_(k)ᵀ = Σ_k Σ_kᵀ` (the book's proof: `𝒮_(k) = Σ_k V_kᵀ (U_d ⊗ ⋯)ᵀ`); the `σ_k
i` are the sorted singular values of `𝒜_(k)` (`Matrix.IsSVD.singularValues_eq`), so the rows beyond
`rank(𝒜_(k))` vanish and the HOSVD sums may stop at `rank_*(𝒜)` (§12.5.2). -/
theorem theorem_12_5_1_b (A : RTensor n) (U : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ)
    (σ : Fin (d + 1) → ℕ → ℝ) (V : ∀ k, Matrix (Fin (∏ j : Fin d, n (k.succAbove j)))
      (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ)
    (h : ∀ k, IsSVD (modalUnfolding A k) (U k) (σ k) (V k)) (k : Fin (d + 1)) :
    let S : RTensor n := Tensor.multilinearProd (fun k => (U k)ᵀ) A
    modalUnfolding S k * (modalUnfolding S k)ᵀ =
        (rectDiagonal (σ k) : Matrix (Fin (n k)) (Fin (∏ j : Fin d, n (k.succAbove j))) ℝ) *
          (rectDiagonal (σ k))ᵀ ∧
      ∀ i : ℕ, i < n k → i < ∏ j : Fin d, n (k.succAbove j) →
        σ k i = (modalUnfolding A k).sortedSingularValues i := by
  intro S
  refine ⟨?_, fun i hi hi' => (h k).singularValues_eq hi hi'⟩
  have hS : modalUnfolding S k = (U k)ᵀ * modalUnfolding A k *
      ((piKronecker fun j : Fin d => (U (k.succAbove j))ᵀ).reindex finPiFinEquiv
        finPiFinEquiv)ᵀ :=
    theorem_12_4_1 (fun k => (U k)ᵀ) A k
  have hK := transpose_mul_reindex_piKronecker (fun j : Fin d => U (k.succAbove j))
    fun j => (isSVD_real_facts (h _)).1
  calc modalUnfolding S k * (modalUnfolding S k)ᵀ
      = ((U k)ᵀ * modalUnfolding A k) *
          (((piKronecker fun j : Fin d => (U (k.succAbove j))ᵀ).reindex finPiFinEquiv
            finPiFinEquiv)ᵀ *
          (piKronecker fun j : Fin d => (U (k.succAbove j))ᵀ).reindex finPiFinEquiv
            finPiFinEquiv) * ((U k)ᵀ * modalUnfolding A k)ᵀ := by
        rw [hS, transpose_mul, transpose_transpose]
        simp only [Matrix.mul_assoc]
    _ = ((U k)ᵀ * modalUnfolding A k) * ((U k)ᵀ * modalUnfolding A k)ᵀ := by
        rw [hK, Matrix.mul_one]
    _ = rectDiagonal (σ k) * (rectDiagonal (σ k))ᵀ := (equation_12_5_1 (h k)).2.2.1

/-- **(12.5.11)**, corrected: the truncated HOSVD keeping, in each mode, the factor columns in a set
`s_k` (the book keeps the leading `r_k` left singular vectors) satisfies
`‖𝒜 − 𝒜^{(s)}‖_F² ≤ ∑_{k=1}^{d} ∑_{i ∉ s_k} σ_i(𝒜_(k))²`, the singular values attached to the
columns of the factors. The book prints `min_{1≤k≤d}` in place of `∑_{k=1}^{d}`, which is false:
every tensor of multilinear rank `≤ r` is at squared distance at least `max_k ∑_{i>r_k} σ_i(𝒜_(k))²`
from `𝒜`, so the printed bound fails whenever one tail vanishes and another does not. -/
theorem equation_12_5_11 {n : Fin d → ℕ} (A : RTensor n) (s : ∀ k, Finset (Fin (n k))) :
    ‖A - A.truncatedHOSVD s‖ ^ 2 ≤
      ∑ k, ∑ i ∈ (s k)ᶜ, (A.modeUnfold k)ᵀ.singularValues i ^ 2 := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using Tensor.norm_sub_truncatedHOSVD_sq_le A s

end HOSVD

/-! ### The Tucker problem (§12.5.3) -/

section Tucker

variable {d : ℕ} {n r : Fin d → ℕ}

/-- The Euclidean norm of the vectorization of a tensor is its Frobenius norm. -/
theorem norm_toLp_vecFin (T : RTensor n) : ‖WithLp.toLp 2 (Tensor.vecFin T)‖ = ‖T‖ := by
  rw [EuclideanSpace.norm_eq, Tensor.frobenius_norm_def]
  congr 1
  rw [← finPiFinEquiv.sum_comp]
  simp [Tensor.vecFin_apply]

/-- **§12.5.3**: for `U_k ∈ ℝ^{n_k×r_k}` with orthonormal columns and `𝒳 = 𝒮 ×₁ U₁ ⋯ ×_d U_d` of the
form (12.5.13), `‖𝒜 − 𝒳‖_F = ‖vec(𝒜) − (U_d ⊗ ⋯ ⊗ U₁) vec(𝒮)‖₂`; the best core is `𝒮 = 𝒜 ×₁ U₁ᵀ ⋯
×_d U_dᵀ` (`vec(𝒮) = (U_dᵀ ⊗ ⋯ ⊗ U₁ᵀ) vec(𝒜)`), and then
`‖𝒜 − 𝒳‖_F² = ‖vec(𝒜)‖² − ‖(U_d ⊗ ⋯ ⊗ U₁)ᵀ vec(𝒜)‖²` (for every order, the book printing order 3).
-/
theorem tucker_best_core (U : ∀ k, Matrix (Fin (n k)) (Fin (r k)) ℝ) (hU : ∀ k, (U k)ᵀ * U k = 1)
    (A : RTensor n) :
    (∀ S : RTensor r, ‖A - Tensor.multilinearProd U S‖ =
      ‖WithLp.toLp 2 (Tensor.vecFin A -
        (piKronecker U).reindex finPiFinEquiv finPiFinEquiv *ᵥ Tensor.vecFin S)‖) ∧
      (∀ S : RTensor r, ‖A - Tensor.multilinearProd U S‖ ^ 2 =
        ‖A‖ ^ 2 - ‖Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ^ 2 +
          ‖S - Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ^ 2) ∧
      IsMinOn (fun S : RTensor r => ‖A - Tensor.multilinearProd U S‖) Set.univ
        (Tensor.multilinearProd (fun k => (U k)ᵀ) A) ∧
      ‖A - Tensor.multilinearProd U (Tensor.multilinearProd (fun k => (U k)ᵀ) A)‖ ^ 2 =
        ‖A‖ ^ 2 - ‖Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ^ 2 := by
  have hU' : ∀ k, (U k)ᴴ * U k = 1 := fun k => by
    rw [conjTranspose_eq_transpose_of_trivial]; exact hU k
  have key : ∀ S : RTensor r, ‖A - Tensor.multilinearProd U S‖ ^ 2 =
      ‖A‖ ^ 2 - ‖Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ^ 2 +
        ‖S - Tensor.multilinearProd (fun k => (U k)ᵀ) A‖ ^ 2 := fun S => by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Tensor.norm_sub_multilinearProd_sq hU' A S
  refine ⟨fun S => ?_, key, fun S _ => ?_, ?_⟩
  · rw [← norm_toLp_vecFin]
    congr 2
    rw [← Tensor.vecFin_multilinearProd]
    rfl
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    change ‖A - Tensor.multilinearProd U (Tensor.multilinearProd (fun k => (U k)ᵀ) A)‖ ^ 2 ≤
      ‖A - Tensor.multilinearProd U S‖ ^ 2
    rw [key, key, sub_self, norm_zero]
    nlinarith [sq_nonneg ‖S - Tensor.multilinearProd (fun k => (U k)ᵀ) A‖]
  · rw [key, sub_self, norm_zero]
    ring

end Tucker

/-! ### The CP problem (12.5.14)–(12.5.21) -/

section CP

variable {d r : ℕ} {n : Fin (d + 1) → ℕ}

/-- **(12.5.16)–(12.5.18)** with the displays before them, at every order: for
`𝒳 = ∑_j λ_j F⁽¹⁾(:, j) ∘ ⋯ ∘ F⁽ᵈ⁾(:, j)` (`Tensor.cp`), `𝒳_(k) = F⁽ᵏ⁾ diag(λ) (F⁽ᵈ⁾ ⊙ ⋯ ⊙ F⁽ᵏ⁺¹⁾ ⊙
F⁽ᵏ⁻¹⁾ ⊙ ⋯ ⊙ F⁽¹⁾)ᵀ` (the Khatri–Rao product of the other factors flattened in the book's reversed
order), `‖𝒜 − 𝒳‖_F = ‖𝒜_(k) − 𝒳_(k)‖_F` for every `k`, and `vec(𝒳) = (F⁽ᵈ⁾ ⊙ ⋯ ⊙ F⁽¹⁾) λ` (P12.5.6).
-/
theorem equation_12_5_16 (c : Fin r → ℝ) (F : ∀ k, Matrix (Fin (n k)) (Fin r) ℝ)
    (k : Fin (d + 1)) :
    modalUnfolding (Tensor.cp c F : RTensor n) k =
        F k * diagonal c *
          ((piKhatriRao fun j : Fin d => F (k.succAbove j)).reindex finPiFinEquiv
            (Equiv.refl _))ᵀ ∧
      (∀ A : RTensor n, ‖A - Tensor.cp c F‖ =
        (open scoped Matrix.Norms.Frobenius in
          ‖modalUnfolding A k - modalUnfolding (Tensor.cp c F : RTensor n) k‖)) ∧
      Tensor.vecFin (Tensor.cp c F : RTensor n) =
        (piKhatriRao F).reindex finPiFinEquiv (Equiv.refl _) *ᵥ c := by
  have hP : (piKhatriRao fun j : {j // j ≠ k} => F j).reindex (modalColumnEquiv n k)
      (Equiv.refl _) =
        (piKhatriRao fun j : Fin d => F (k.succAbove j)).reindex finPiFinEquiv
          (Equiv.refl _) := by
    ext a t
    obtain ⟨a', rfl⟩ := (modalColumnEquiv n k).surjective a
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, piKhatriRao_apply,
      modalColumnEquiv_symm_apply, Equiv.refl_symm, Equiv.coe_refl, id]
    rw [← (finSuccAboveEquiv k).prod_comp]
    rfl
  refine ⟨?_, fun A => ?_, Tensor.vecFin_cp c F⟩
  · rw [modalUnfolding, Tensor.modeUnfold_cp, ← hP]
    simp only [reindex_apply, Equiv.refl_symm, Equiv.coe_refl, transpose_submatrix]
    rw [Matrix.submatrix_mul _ _ id id _ Function.bijective_id, submatrix_id_id]
  · open scoped Matrix.Norms.Frobenius in
    rw [show modalUnfolding A k - modalUnfolding (Tensor.cp c F : RTensor n) k =
        modalUnfolding (A - Tensor.cp c F) k from rfl, modalUnfolding, frobenius_norm_reindex,
      Tensor.frobenius_norm_modeUnfold]

end CP

section ALS

open scoped Matrix.Norms.Frobenius

/-- **(12.5.19)–(12.5.20)**: the CP-ALS update `F̃` minimizing `‖𝒜_(1) − F̃ (H ⊙ G)ᵀ‖_F` is
characterized by the normal equations `F̃ ((HᵀH) .* (GᵀG)) = 𝒜_(1) (H ⊙ G)` (the Khatri–Rao Gram
identity `(H ⊙ G)ᵀ(H ⊙ G) = (HᵀH) .* (GᵀG)`); with a single row (`N = 1`) this is the vector
statement: `z` minimizes `‖(B ⊙ C) z − d‖₂` iff `((BᵀB) .* (CᵀC)) z = (B ⊙ C)ᵀ d`. -/
theorem equation_12_5_20 {N p q r : ℕ} (H : Matrix (Fin p) (Fin r) ℝ) (G : Matrix (Fin q) (Fin r) ℝ)
    (A : Matrix (Fin N) (Fin p × Fin q) ℝ) (F : Matrix (Fin N) (Fin r) ℝ) :
    (∀ F' : Matrix (Fin N) (Fin r) ℝ,
        ‖A - F * (khatriRao H G)ᵀ‖ ≤ ‖A - F' * (khatriRao H G)ᵀ‖) ↔
      F * ((Hᵀ * H) ⊙ (Gᵀ * G)) = A * khatriRao H G := by
  have h := isMinOn_norm_sub_mul_transpose_iff A (khatriRao H G) F
  simp only [conjTranspose_eq_transpose_of_trivial, khatriRao_transpose_mul_self] at h
  exact h

end ALS

/-! ### Variational singular values and eigenvalues (12.5.22)–(12.5.23) -/

/-- **(12.5.22)** and the gradient display after it: the singular values of `A ∈ ℝ^{n₁×n₂}` are the
stationary values of `ψ_A(u, v) = uᵀ A v / (‖u‖₂ ‖v‖₂)` (up to sign): at nonzero `u`, `v`, with
`û = u/‖u‖`, `v̂ = v/‖v‖`, `∇ψ_A = 0` iff `A v̂ = ψ_A û` and `Aᵀ û = ψ_A v̂`, and then `|ψ_A(u, v)|`
is a singular value of `A`. -/
theorem equation_12_5_22 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {u : EuclideanSpace ℝ (Fin m)}
    {v : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) (hv : v ≠ 0) :
    (fderiv ℝ A.bilinearRayleigh (u, v) = 0 ↔
        toEuclideanLin A (‖v‖⁻¹ • v) = A.bilinearRayleigh (u, v) • ‖u‖⁻¹ • u ∧
          toEuclideanLin Aᵀ (‖u‖⁻¹ • u) = A.bilinearRayleigh (u, v) • ‖v‖⁻¹ • v) ∧
      (fderiv ℝ A.bilinearRayleigh (u, v) = 0 →
        ∃ i, |A.bilinearRayleigh (u, v)| = A.singularValues i) :=
  ⟨A.fderiv_bilinearRayleigh_eq_zero_iff hu hv,
    A.abs_critical_bilinearRayleigh_mem_singularValues hu hv⟩

/-- **(12.5.23)**: the eigenvalues of a symmetric `C ∈ ℝ^{N×N}` are the stationary values of
`φ_C(x) = xᵀ C x / xᵀ x` and the stationary vectors are eigenvectors: at `x ≠ 0` the derivative of
`φ_C` vanishes iff `C x = φ_C(x) x`. -/
theorem equation_12_5_23 {N : ℕ} {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.IsSymm)
    {x : EuclideanSpace ℝ (Fin N)} (hx : x ≠ 0) {f' : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hf : HasFDerivAt (toEuclideanLin C).rayleighQuotient f' x) :
    f' = 0 ↔ toEuclideanLin C x = (toEuclideanLin C).rayleighQuotient x • x := by
  have hH : C.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hC
  exact (isSymmetric_toEuclideanLin_iff.2 hH).hasFDerivAt_rayleighQuotient_eq_zero_iff hx hf

/-! ### Tensor trains (12.5.25)–(12.5.29) -/

section TensorTrain

variable {n r : ℕ → ℕ}

/-- **(12.5.25)**, the book's tensor train from its carriages `𝒢_k ∈ ℝ^{r_{k−1} × n_k × r_k}`
(0-based here: `𝒢 k` has shape `r k × n k × r (k + 1)`, the first and last read as
`1 × n₁ × r₁` and `r_{d−1} × n_d × 1` when `r 0 = r d = 1`):
`𝒯(i) = ∑_κ 𝒢₁(κ₀, i₁, κ₁) 𝒢₂(κ₁, i₂, κ₂) ⋯ 𝒢_d(κ_{d−1}, i_d, κ_d)`, the sum over all rank
indices (the boundary ones range over a single value). -/
noncomputable def trainOfCarriages (d : ℕ)
    (𝒢 : ∀ k : ℕ, Fin (r k) → Fin (n k) → Fin (r (k + 1)) → ℝ) :
    Tensor (fun k : Fin d => Fin (n k)) ℝ :=
  Tensor.of fun i => ∑ κ : (∀ j : Fin (d + 1), Fin (r j)),
    ∏ k : Fin d, 𝒢 k (κ k.castSucc) (i k) (κ k.succ)

/-- The carriages read as matrix-valued cores (the backbone's `Tensor.tensorTrain` convention). -/
def carriageCores (𝒢 : ∀ k : ℕ, Fin (r k) → Fin (n k) → Fin (r (k + 1)) → ℝ) (k : ℕ)
    (x : Fin (n k)) : Matrix (Fin (r k)) (Fin (r (k + 1))) ℝ :=
  of fun p q => 𝒢 k p x q

/-- The chain sums: `u ᵀ (G₀(i₀) ⋯ G_{D−1}(i_{D−1})) v` summed out over all rank indices. -/
private theorem dotProduct_ttPartial_mulVec
    (𝒢 : ∀ k : ℕ, Fin (r k) → Fin (n k) → Fin (r (k + 1)) → ℝ) :
    ∀ (D : ℕ) (i : ∀ k : Fin D, Fin (n k)) (u : Fin (r 0) → ℝ) (v : Fin (r D) → ℝ),
      u ⬝ᵥ (Tensor.ttPartial (carriageCores 𝒢) D i *ᵥ v) =
        ∑ κ : (∀ j : Fin (D + 1), Fin (r j)),
          u (κ ⟨0, D.succ_pos⟩) * (∏ k : Fin D, 𝒢 k (κ k.castSucc) (i k) (κ k.succ)) *
            v (κ (Fin.last D))
  | 0, i, u, v => by
    rw [Tensor.ttPartial_zero, one_mulVec, dotProduct]
    rw [← (Equiv.piUnique fun j : Fin 1 => Fin (r j)).symm.sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rfl
  | D + 1, i, u, v => by
    rw [Tensor.ttPartial_succ, ← mulVec_mulVec, dotProduct_ttPartial_mulVec 𝒢 D]
    rw [← (Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun κ _ => ?_
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Fin.prod_univ_castSucc]
    have h0 : (Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)) (s, κ) ⟨0, (D + 1).succ_pos⟩ =
        κ ⟨0, D.succ_pos⟩ :=
      Fin.snoc_castSucc (α := fun j : Fin (D + 2) => Fin (r j)) (p := κ) (x := s) ⟨0, D.succ_pos⟩
    have hl : (Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)) (s, κ) (Fin.last (D + 1)) = s :=
      Fin.snoc_last (α := fun j : Fin (D + 2) => Fin (r j)) (p := κ) (x := s)
    have hc : ∀ k : Fin (D + 1),
        (Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)) (s, κ) k.castSucc = κ k := fun k =>
      Fin.snoc_castSucc (α := fun j : Fin (D + 2) => Fin (r j)) (p := κ) (x := s) k
    have hs : ∀ k : Fin D,
        ((Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)) (s, κ) k.castSucc.succ :
          Fin (r (k + 1))) = κ k.succ := fun k =>
      Fin.snoc_castSucc (α := fun j : Fin (D + 2) => Fin (r j)) (p := κ) (x := s) k.succ
    rw [h0, hl]
    simp only [hc, hs]
    have hls : ((Fin.snocEquiv fun j : Fin (D + 2) => Fin (r j)) (s, κ) (Fin.last D).succ :
        Fin (r (D + 1))) = s := hl
    rw [hls, carriageCores, of_apply]
    have e1 : (∏ x : Fin D, 𝒢 (↑x.castSucc) (κ x.castSucc) (i x.castSucc) (κ x.succ)) =
        ∏ k : Fin D, 𝒢 k (κ k.castSucc) (i k.castSucc) (κ k.succ) := rfl
    have e2 : 𝒢 (↑(Fin.last D)) (κ (Fin.last D)) (i (Fin.last D)) s =
        𝒢 D (κ (Fin.last D)) (i (Fin.last D)) s := rfl
    rw [e1, e2]
    ring

/-- **(12.5.25)**: the book's tensor train from its carriages (`trainOfCarriages`, with
`r 0 = r d = 1`) is the backbone's `Tensor.tensorTrain` with cores `G k (i) = 𝒢_k(:, i, :)`. -/
theorem equation_12_5_25 (d : ℕ) (𝒢 : ∀ k : ℕ, Fin (r k) → Fin (n k) → Fin (r (k + 1)) → ℝ)
    (h0 : r 0 = 1) (hd : r d = 1) :
    trainOfCarriages d 𝒢 = Tensor.tensorTrain (carriageCores 𝒢) d h0 hd := by
  ext i
  rw [Tensor.tensorTrain_apply]
  have key := dotProduct_ttPartial_mulVec 𝒢 d i (Pi.single (Fin.cast h0.symm 0) 1)
    (Pi.single (Fin.cast hd.symm 0) 1)
  rw [single_dotProduct, one_mul, mulVec_single_one, col_apply] at key
  rw [key, trainOfCarriages, Tensor.of_apply]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have e0 : κ ⟨0, d.succ_pos⟩ = Fin.cast h0.symm 0 :=
    Fin.ext (by have := (κ ⟨0, d.succ_pos⟩).isLt; simp [h0] at this ⊢; omega)
  have ed : κ (Fin.last d) = Fin.cast hd.symm 0 :=
    Fin.ext (by have := (κ (Fin.last d)).isLt; simp [hd] at this ⊢; omega)
  rw [e0, ed, Pi.single_eq_same, Pi.single_eq_same, one_mul, mul_one]

end TensorTrain

/-- **(12.5.26)–(12.5.28)** (P12.5.11): if the unfolding `C = 𝒞_{[1 2] × [3 4]}` (rows `(k₂, i₃)`)
factors as `C = U₃ W` with `U₃` of `s` columns — the thin SVD `C = U₃ (Σ₃ V₃ᵀ)` with `s = r₃ =
rank(C)` — then `𝒢₃(k₂, i₃, k₃) = U₃((k₂, i₃), k₃)` and `𝒞̃ = W` satisfy (12.5.26),
`𝒞(k₂, i₃, ·) = ∑_{k₃} 𝒢₃(k₂, i₃, k₃) 𝒞̃(k₃, ·)`; and such a core exists whenever `rank(C) ≤ s`
(`Tensor.exists_ttCore_of_rank`). -/
theorem equation_12_5_28 {p m s : ℕ} {N : Type*} [Fintype N] (C : Matrix (Fin p × Fin m) N ℝ) :
    (∀ (U₃ : Matrix (Fin p × Fin m) (Fin s) ℝ) (W : Matrix (Fin s) N ℝ), C = U₃ * W →
      ∀ k i c, C (k, i) c = ((of fun k' k₃ => U₃ (k', i) k₃) * W) k c) ∧
    (C.rank ≤ s → ∃ (G : Fin m → Matrix (Fin p) (Fin s) ℝ) (C' : Matrix (Fin s) N ℝ),
      ∀ k i c, C (k, i) c = (G i * C') k c) := by
  refine ⟨fun U₃ W hC k i c => ?_, Tensor.exists_ttCore_of_rank C⟩
  rw [hC, mul_apply, mul_apply]
  rfl

/-! ### Tensor singular values and eigenvalues, tensor trains -/

section Variational

variable {d : ℕ} {n : Fin d → ℕ}

/-- **§12.5.6**, tensor singular values: `ψ_𝒜(u) = 𝒜(u₁, …, u_d)/(‖u₁‖ ⋯ ‖u_d‖)` has numerator
`𝒜(u) = u_kᵀ 𝒜_(k) (⊗_{j ≠ k} u_j)` for every mode `k` (the book's
`u₁ᵀ 𝒜_(1)(u₃ ⊗ u₂) = u₂ᵀ 𝒜_(2)(u₃ ⊗ u₁) = u₃ᵀ 𝒜_(3)(u₂ ⊗ u₁)` for `d = 3`), and at nonzero `u` the
equation `∇ψ_𝒜 = 0` holds iff, with `û_i = u_i/‖u_i‖`, `𝒜_(k)(⊗_{j ≠ k} û_j) = ψ_𝒜(u) û_k` for every
`k` — the book's definition of a singular value of the tensor (`Tensor.IsSingularValue`). The
unfoldings are the backbone's typed `Tensor.modeUnfold`, whose columns are the tuples of the other
indices. -/
theorem tensor_singular_value (A : RTensor n) :
    (∀ (u : ∀ i, Fin (n i) → ℝ) (k : Fin d), Tensor.multilinearForm A u =
      u k ⬝ᵥ (A.modeUnfold k *ᵥ Tensor.rankOne fun j : {j // j ≠ k} => u j)) ∧
    ∀ {u : ∀ i, EuclideanSpace ℝ (Fin (n i))}, (∀ i, u i ≠ 0) →
      (HasFDerivAt (Tensor.multilinearRayleigh A)
          (0 : (∀ i, EuclideanSpace ℝ (Fin (n i))) →L[ℝ] ℝ) u ↔
        ∀ k, A.modeUnfold k *ᵥ Tensor.rankOne (fun j : {j // j ≠ k} => (‖u j‖⁻¹ • u j).ofLp)
          = Tensor.multilinearRayleigh A u • (‖u k‖⁻¹ • u k).ofLp) :=
  ⟨fun u k => Tensor.multilinearForm_eq_modeUnfold A u k,
    fun hu => Tensor.hasFDerivAt_multilinearRayleigh_eq_zero_iff A hu⟩

/-- **(12.5.24)** and the sentences around it: for a symmetric `𝒞 ∈ ℝ^{N×⋯×N}` (§12.5.7), all
modal unfoldings are equal (up to the relabelling of their columns by the transposition of the two
modes), and at `x ≠ 0` the gradient of `φ_𝒞(x) = 𝒞(x, …, x)/‖x‖^d` vanishes iff, with
`x̂ = x/‖x‖`, `𝒞_(k)(x̂ ⊗ ⋯ ⊗ x̂) = φ_𝒞(x) x̂` — the book's tensor eigenvalue. (The book's
gradient omits the factor `d`, harmless at zero.) -/
theorem equation_12_5_24 {N : ℕ} {C : Tensor (fun _ : Fin d => Fin N) ℝ} (hC : C.IsSymm) :
    (∀ k l, C.modeUnfold l = (C.modeUnfold k).submatrix id (Tensor.swapColEquiv k l).symm) ∧
    ∀ {x : EuclideanSpace ℝ (Fin N)}, x ≠ 0 → ∀ k,
      (HasFDerivAt (Tensor.symmetricRayleigh C) (0 : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) x ↔
        C.modeUnfold k *ᵥ Tensor.rankOne (fun _ : {j // j ≠ k} => (‖x‖⁻¹ • x).ofLp)
          = Tensor.symmetricRayleigh C x • (‖x‖⁻¹ • x).ofLp) :=
  ⟨fun k l => hC.modeUnfold_eq k l,
    fun hx k => Tensor.hasFDerivAt_symmetricRayleigh_eq_zero_iff hC hx k⟩

end Variational

/-- **(12.5.29)**, the TT-SVD (Oseledets–Tyrtyshnikov): every tensor `𝒜` of order `d ≥ 1` has a
tensor-train representation (12.5.25) `𝒜 = trainOfCarriages d 𝒢` whose ranks `r_k` are the ranks of
the sequential unfoldings `𝒜_{[1:k] × [k+1:d]}`, `0 < k < d`, with `r_0 = r_d = 1` — the ranks of
the matrices the procedure's successive SVDs factor (`Tensor.exists_tensorTrain_of_ne_zero`, through
`equation_12_5_25`). For `d = 0` a train is the constant `1`, so `d ≠ 0` is needed. -/
theorem equation_12_5_29 {n : ℕ → ℕ} {d : ℕ} (hd : d ≠ 0)
    (A : Tensor (fun k : Fin d => Fin (n k)) ℝ) :
    ∃ (r : ℕ → ℕ) (_ : r 0 = 1) (_ : r d = 1),
      (∀ k, 0 < k → k < d → r k = (A.unfold fun i : Fin d => (i : ℕ) < k).rank) ∧
      ∃ 𝒢 : ∀ k : ℕ, Fin (r k) → Fin (n k) → Fin (r (k + 1)) → ℝ, A = trainOfCarriages d 𝒢 := by
  obtain ⟨r, h0, hr, hrk, G, hG⟩ := Tensor.exists_tensorTrain_of_ne_zero A hd
  refine ⟨r, h0, hr, hrk, fun k p x q => G k x p q, ?_⟩
  rw [equation_12_5_25 d _ h0 hr, hG]
  rfl

end GolubVanLoan.Chapter12
