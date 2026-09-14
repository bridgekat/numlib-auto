import Numlib.LinearAlgebra.Matrix.SVD
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Basics

/-!
# Quarteroni–Sacco–Saleri §1.9: the singular value decomposition

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §1.9, over the backbone `Numlib/LinearAlgebra/Matrix/SVD`. The
rectangular diagonal matrix `Σ = diag(σ₁, …, σ_p) ∈ ℂ^{m×n}` of (1.9) is
`Matrix.rectDiagonal σ` for `σ : ℕ → ℂ`, and the sorted singular values `σ₁ ≥ σ₂ ≥ … ≥ 0` are
Mathlib's `(toEuclideanLin A).singularValues : ℕ → ℝ`, indexed from `0`; the backbone's
`Matrix.singularValues A : Fin n → ℝ` are the same numbers indexed by the columns of `A`, in the
order of the eigenvalues of `Aᴴ A`, and (1.10) is their definition. The statements about "an
SVD" take an arbitrary factorization `Uᴴ A V = Σ` with unitary `U`, `V` as their hypothesis.

## Contents

* `property_1_7` — the singular value decomposition, complex and real.
* `equation_1_10`, `singularValues_of_isHermitian` — `σᵢ = √λᵢ(Aᴴ A)`, the singular vectors as
  eigenvectors of `A Aᴴ` and `Aᴴ A`, the Hermitian case `σᵢ = |λᵢ|`.
* `rank_eq_card_singularValues_ne_zero`, `ker_range_of_svd` — the rank, the kernel and the range
  read off the SVD.
* `definition_1_15`, `definition_1_15_fullRank`, `exercise_1_12` — the Moore–Penrose
  pseudo-inverse `A⁺ = V Σ⁺ Uᴴ`, its full-rank and square forms, and Exercise 12's identities.

## Conventions

The columns `uᵢ` of `U` and `vⱼ` of `V` are `Uᵀ i` and `Vᵀ j`; `0`-based indices, so the book's
`σ₁` is `σ 0`. Lean's `0⁻¹ = 0` makes `Σ⁺ = diag(1/σ₁, …, 1/σ_r, 0, …, 0)` the entrywise inverse
of the diagonal of `Σ`, with no case split on the rank.
-/

open Finset Matrix
open scoped ComplexOrder

namespace QuarteroniSaccoSaleri.Chapter01

variable {m n : ℕ}

/-! ### Property 1.7: the SVD -/

/-- **Property 1.7, (1.9).** Let `A ∈ ℂ^{m×n}`. There are unitary `U ∈ ℂ^{m×m}` and `V ∈ ℂ^{n×n}`
with `Uᴴ A V = Σ = diag(σ₁, …, σ_p) ∈ ℂ^{m×n}`, `p = min(m, n)`, and `σ₁ ≥ … ≥ σ_p ≥ 0`: the
*singular value decomposition* of `A`, the `σᵢ` its *singular values* — Mathlib's sorted
`(toEuclideanLin A).singularValues`, which vanish from `p` on (backbone `Matrix.exists_svd`).
If `A` is real, `U` and `V` are real orthogonal and `Uᵀ A V = Σ`. -/
theorem property_1_7 (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) (Fin n) ℝ) :
    (∃ U ∈ unitaryGroup (Fin m) ℂ, ∃ V ∈ unitaryGroup (Fin n) ℂ,
      star U * A * V = rectDiagonal fun i => (((toEuclideanLin A).singularValues i : ℝ) : ℂ)) ∧
      Antitone (toEuclideanLin A).singularValues ∧
      (∀ i, 0 ≤ (toEuclideanLin A).singularValues i) ∧
      (∀ i, min m n ≤ i → (toEuclideanLin A).singularValues i = 0) ∧
      ∃ U ∈ orthogonalGroup (Fin m) ℝ, ∃ V ∈ orthogonalGroup (Fin n) ℝ,
        Uᵀ * B * V = rectDiagonal fun i => (toEuclideanLin B).singularValues i := by
  refine ⟨exists_svd A, (toEuclideanLin A).singularValues_antitone,
    (toEuclideanLin A).singularValues_nonneg, fun i hi => ?_, ?_⟩
  · rcases le_or_gt m n with hmn | hmn
    · rw [min_eq_left hmn] at hi
      exact (toEuclideanLin A).singularValues_of_finrank_codomain_le
        (finrank_euclideanSpace_fin.trans_le hi)
    · rw [min_eq_right hmn.le] at hi
      exact (toEuclideanLin A).singularValues_of_finrank_le (finrank_euclideanSpace_fin.trans_le hi)
  · obtain ⟨U, hU, V, hV, h⟩ := exists_svd B
    refine ⟨U, hU, V, hV, ?_⟩
    rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose, h]
    rfl

/-! ### (1.10): the singular values through `Aᴴ A` -/

/-- Column `j` of `M V` is `M` applied to column `j` of `V`, and column `j` of `V D` for a
diagonal `D` is `d j` times column `j` of `V`: so `M V = V D` says that the columns of `V` are
eigenvectors of `M`. -/
private theorem mulVec_transpose_eq_of_mul_eq_mul_diagonal {k : ℕ} {M V : Matrix (Fin k) (Fin k) ℂ}
    {d : Fin k → ℂ} (h : M * V = V * diagonal d) (j : Fin k) : M *ᵥ Vᵀ j = d j • Vᵀ j := by
  ext r
  have := congrFun (congrFun h r) j
  rw [mul_diagonal] at this
  simp only [mulVec, dotProduct, transpose_apply, Pi.smul_apply, smul_eq_mul]
  rw [← mul_apply, this, mul_comm]

/-- **(1.10).** `σᵢ(A) = √λᵢ(Aᴴ A)`, `i = 1, …, n`: the backbone's `Matrix.singularValues A i` is
by definition the square root of the `i`-th eigenvalue of the Hermitian matrix `Aᴴ A`, so
`σᵢ(A)² = λᵢ(Aᴴ A)`; and for any SVD `Uᴴ A V = Σ = diag(σ)` with `σ` antitone and nonnegative,
the `σᵢ`, `i < min(m, n)`, are the sorted singular values (`Matrix.singularValues_eq_of_svd`).
Indeed `A = U Σ Vᴴ` gives `Aᴴ A = V Σᴴ Σ Vᴴ`, so the columns of `V` — the *right singular
vectors* — are eigenvectors of `Aᴴ A` for the eigenvalues `|σⱼ|²` (`0` beyond the height of
`Σ`), and the columns of `U` — the *left singular vectors* — are eigenvectors of `A Aᴴ`. -/
theorem equation_1_10 (A : Matrix (Fin m) (Fin n) ℂ) {U : Matrix (Fin m) (Fin m) ℂ}
    {V : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin m) ℂ)
    (hV : V ∈ unitaryGroup (Fin n) ℂ) {σ : ℕ → ℂ} (h : star U * A * V = rectDiagonal σ) :
    (∀ i, A.singularValues i = √((isHermitian_conjTranspose_mul_self A).eigenvalues i) ∧
        A.singularValues i ^ 2 = (isHermitian_conjTranspose_mul_self A).eigenvalues i) ∧
      (∀ τ : ℕ → ℝ, Antitone τ → (∀ i, 0 ≤ τ i) →
        star U * A * V = rectDiagonal (fun i => ((τ i : ℝ) : ℂ)) →
        ∀ i, i < m → i < n → (toEuclideanLin A).singularValues i = τ i) ∧
      A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℂ) * star V ∧
      Aᴴ * A = V * ((rectDiagonal σ : Matrix (Fin m) (Fin n) ℂ)ᴴ * rectDiagonal σ) * star V ∧
      (∀ j : Fin n, (Aᴴ * A) *ᵥ Vᵀ j = (if (j : ℕ) < m then star (σ j) * σ j else 0) • Vᵀ j) ∧
      ∀ i : Fin m, (A * Aᴴ) *ᵥ Uᵀ i = (if (i : ℕ) < n then σ i * star (σ i) else 0) • Uᵀ i := by
  have hA : A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℂ) * Vᴴ :=
    eq_mul_mul_star_of_star_mul_mul_eq hU hV h
  have hUU : Uᴴ * U = 1 := mem_unitaryGroup_iff'.1 hU
  have hVV : Vᴴ * V = 1 := mem_unitaryGroup_iff'.1 hV
  have hAA : Aᴴ * A = V * ((rectDiagonal σ : Matrix (Fin m) (Fin n) ℂ)ᴴ * rectDiagonal σ) *
      Vᴴ := by
    rw [hA, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ, hUU, Matrix.one_mul]
  refine ⟨fun i => ⟨rfl, sq_singularValues A i⟩,
    fun τ hτ hτ0 hτA i him hin => singularValues_eq_of_svd hU hV hτ hτ0 hτA him hin, hA, hAA,
    fun j => ?_, fun i => ?_⟩
  · refine mulVec_transpose_eq_of_mul_eq_mul_diagonal
      (d := fun j : Fin n => if (j : ℕ) < m then star (σ j) * σ j else 0) ?_ j
    rw [hAA, Matrix.mul_assoc, hVV, Matrix.mul_one, conjTranspose_rectDiagonal_mul_self]
  · refine mulVec_transpose_eq_of_mul_eq_mul_diagonal
      (d := fun i : Fin m => if (i : ℕ) < n then σ i * star (σ i) else 0) ?_ i
    have hAAt : A * Aᴴ = U * (rectDiagonal σ * (rectDiagonal σ : Matrix (Fin m) (Fin n) ℂ)ᴴ) *
        Uᴴ := by
      rw [hA, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ, hVV, Matrix.one_mul]
    rw [hAAt, Matrix.mul_assoc, hUU, Matrix.mul_one, conjTranspose_rectDiagonal,
      rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
    rfl

/-- **§1.9, the Hermitian case.** If `A ∈ ℂ^{n×n}` is Hermitian with eigenvalues `λ₁, …, λₙ`, its
singular values are the moduli `|λ₁|, …, |λₙ|` (since `A Aᴴ = A²`, `σᵢ = √λᵢ² = |λᵢ|`): after a
relabelling `e` of the indices, `σ_{e i}(A) = |λᵢ(A)|` (backbone
`Matrix.IsHermitian.exists_equiv_singularValues_eq_abs_eigenvalues`). -/
theorem singularValues_of_isHermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ∃ e : Fin n ≃ Fin n, ∀ i, A.singularValues (e i) = |hA.eigenvalues i| :=
  hA.exists_equiv_singularValues_eq_abs_eigenvalues

/-! ### The rank, the kernel and the range from the SVD -/

/-- **§1.9, the rank.** If `σ₁ ≥ … ≥ σ_r > σ_{r+1} = … = σ_p = 0` then `rank A = r`: the rank is
the number of nonzero singular values (backbone `Matrix.card_singularValues_ne_zero`, and
Mathlib's `LinearMap.card_support_singularValues` for the sorted ones), so that the sorted
singular value `σᵢ` is positive exactly for `i < rank A` and vanishes exactly for
`i ≥ rank A`. -/
theorem rank_eq_card_singularValues_ne_zero (A : Matrix (Fin m) (Fin n) ℂ) :
    A.rank = Fintype.card {i : Fin n // A.singularValues i ≠ 0} ∧
      A.rank = (toEuclideanLin A).singularValues.support.card ∧
      (∀ i, 0 < (toEuclideanLin A).singularValues i ↔ i < A.rank) ∧
      ∀ i, (toEuclideanLin A).singularValues i = 0 ↔ A.rank ≤ i := by
  have hr : Module.finrank ℂ (LinearMap.range (toEuclideanLin A)) = A.rank := by
    rw [rank_eq_finrank_range_toLin A (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis, toEuclideanLin_eq_toLin_orthonormal]
  refine ⟨(card_singularValues_ne_zero A).symm, ?_, fun i => ?_, fun i => ?_⟩
  · rw [LinearMap.card_support_singularValues, hr]
  · rw [LinearMap.singularValues_pos_iff_lt_finrank_range, hr]
  · rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range, hr]

/-- **§1.9, the kernel and the range.** From an SVD `Uᴴ A V = Σ = diag(σ)`: the kernel of `A` is
the span of the columns `vⱼ` of `V` whose singular value vanishes — `{v_{r+1}, …, vₙ}` for
sorted singular values, here the `j ≥ m` beyond the height of `Σ` together with the `σⱼ = 0` —
and the range of `A` is the span of the columns `uᵢ` of `U` with `σᵢ ≠ 0`, `{u₁, …, u_r}`
(backbone `Matrix.ker_mulVecLin_eq_span_of_svd`, `Matrix.range_mulVecLin_eq_span_of_svd`). -/
theorem ker_range_of_svd {A : Matrix (Fin m) (Fin n) ℂ} {U : Matrix (Fin m) (Fin m) ℂ}
    {V : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin m) ℂ)
    (hV : V ∈ unitaryGroup (Fin n) ℂ) {σ : ℕ → ℂ} (h : star U * A * V = rectDiagonal σ) :
    LinearMap.ker A.mulVecLin = Submodule.span ℂ (Vᵀ '' {j : Fin n | m ≤ (j : ℕ) ∨ σ j = 0}) ∧
      LinearMap.range A.mulVecLin = Submodule.span ℂ (Uᵀ '' {i : Fin m | (i : ℕ) < n ∧ σ i ≠ 0}) :=
  ⟨ker_mulVecLin_eq_span_of_svd hU hV h, range_mulVecLin_eq_span_of_svd hU hV h⟩

/-! ### Definition 1.15: the Moore–Penrose pseudo-inverse -/

/-- **Definition 1.15, (1.11).** Suppose `A ∈ ℂ^{m×n}` admits an SVD `Uᴴ A V = Σ = diag(σ)`. The
*Moore–Penrose pseudo-inverse* (or *generalized inverse*) of `A` is `A⁺ = V Σ⁺ Uᴴ` with
`Σ⁺ = diag(1/σ₁, …, 1/σ_r, 0, …, 0)`, the entrywise inverse of the diagonal of `Σ` (Lean's
`0⁻¹ = 0`); it is the backbone's `Matrix.pinv A` (backbone `Matrix.pinv_eq_of_svd`), which does
not depend on the SVD chosen. -/
theorem definition_1_15 {A : Matrix (Fin m) (Fin n) ℂ} {U : Matrix (Fin m) (Fin m) ℂ}
    {V : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ unitaryGroup (Fin m) ℂ)
    (hV : V ∈ unitaryGroup (Fin n) ℂ) {σ : ℕ → ℂ} (h : star U * A * V = rectDiagonal σ) :
    A.pinv = V * (rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℂ) * star U :=
  pinv_eq_of_svd hU hV h

-- TODO(backbone): the converse of `Matrix.rank_of_isUnit` over a field, beside
-- `Matrix.rank_add_finrank_ker_mulVecLin` in `Numlib/LinearAlgebra/Matrix/Rank`.
/-- A square matrix over a field of full rank is nonsingular: its kernel has dimension `0` by
rank–nullity, so `x ↦ A x` is injective. -/
theorem isUnit_of_rank_eq_card {K : Type*} [Field K] {A : Matrix (Fin n) (Fin n) K}
    (h : A.rank = n) : IsUnit A := by
  have hk := rank_add_finrank_ker_mulVecLin A
  rw [Fintype.card_fin, h] at hk
  rw [← mulVec_injective_iff_isUnit, ← coe_mulVecLin, ← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.1 (by omega)

/-- **Definition 1.15, the full-rank cases.** If `rank A = n` (`A ∈ ℂ^{m×n}` with independent
columns, e.g. `n < m`) then `A⁺ = (Aᴴ A)⁻¹ Aᴴ` — for a real `A`, `(Aᵀ A)⁻¹ Aᵀ` — and if
`n = m = rank A` then `A⁺ = A⁻¹` (backbone
`Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit`, `Matrix.pinv_eq_inv`). -/
theorem definition_1_15_fullRank (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℂ) :
    (A.rank = n → A.pinv = (Aᴴ * A)⁻¹ * Aᴴ) ∧ (B.rank = n → B.pinv = (Bᵀ * B)⁻¹ * Bᵀ) ∧
      (C.rank = n → C.pinv = C⁻¹) := by
  refine ⟨fun hA => ?_, fun hB => ?_, fun hC => pinv_eq_inv (isUnit_of_rank_eq_card hC)⟩
  · exact pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit
      (isUnit_of_rank_eq_card (by rw [rank_conjTranspose_mul_self, hA]))
  · rw [← conjTranspose_eq_transpose_of_trivial]
    exact pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit
      (isUnit_of_rank_eq_card (by rw [rank_conjTranspose_mul_self, hB]))

/-- **Exercise 12** (cited by §1.9 for the properties of `A⁺`). Let `A ∈ ℂ^{m×n}` with
`rank A = n`. Then (1) `A⁺ A = Iₙ`; (2) `A⁺ A A⁺ = A⁺` and `A A⁺ A = A` — these two hold for every
`A` (backbone `Matrix.pinv_mul_self_mul_pinv`, `Matrix.mul_pinv_mul_self`); (3) if `m = n` then
`A⁺ = A⁻¹`. -/
theorem exercise_1_12 (A : Matrix (Fin m) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ) :
    (A.rank = n → A.pinv * A = 1) ∧ (A.pinv * A * A.pinv = A.pinv ∧ A * A.pinv * A = A) ∧
      (C.rank = n → C.pinv = C⁻¹) := by
  refine ⟨fun hA => ?_, ⟨pinv_mul_self_mul_pinv A, mul_pinv_mul_self A⟩,
    (definition_1_15_fullRank A 0 C).2.2⟩
  have hG : IsUnit (Aᴴ * A) := isUnit_of_rank_eq_card (by rw [rank_conjTranspose_mul_self, hA])
  rw [(definition_1_15_fullRank A 0 C).1 hA, Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hG)]

end QuarteroniSaccoSaleri.Chapter01
