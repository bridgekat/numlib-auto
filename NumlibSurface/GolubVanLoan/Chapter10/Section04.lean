import Numlib.Analysis.Matrix.SingularValues
import Numlib.Krylov.Bidiagonalization
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub–Van Loan §10.4: large sparse SVD frameworks

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition, §10.4:
the upper bidiagonal form (10.4.1) and its column equations (10.4.2)–(10.4.7), the Golub–Kahan
relations (10.4.9)–(10.4.12), Ritz approximations (10.4.13)–(10.4.15), the lower form (10.4.18)
and the Paige–Saunders relation (10.4.19), the truncated SVD of the low-rank approximation
problem (10.4.20), and the deterministic identities of the CUR sketch (10.4.22)–(10.4.24).

## Conventions

`A : Matrix (Fin m) (Fin n) ℝ`; the backbone is `Numlib/Krylov/Bidiagonalization` (namespace
`GolubKahan`), instantiated with `toEuclideanLin A` and `toEuclideanLin Aᵀ`: the book's `v_{j+1}`,
`u_{j+1}`, `α_{j+1}`, `β_{j+1}` are `GolubKahan.rightVec/leftVec/alpha/beta … j`, the matrices
`V_k`, `U_k`, `B_k` are `GolubKahan.rightMatrix A v k`, `GolubKahan.leftMatrix A v k`,
`GolubKahan.bidiag … k`. Paige–Saunders (Algorithm 10.4.2) is Golub–Kahan of `Aᵀ`. Submatrices
`X(:, 1:k)` are `X.submatrix id (Fin.castLE _)`. Indices are `0`-based.

## Not formalized

The randomized sampling of §10.4.5 and its probabilistic bound, the 4 × 3 permutation example of
§10.4.3, operation counts.
-/

open Matrix Krylov FloatingPoint
open GolubVanLoan.Chapter01

namespace GolubVanLoan.Chapter10

/-! ### The upper bidiagonal form (§10.4.1) -/

/-- Singular values are invariant under orthogonal equivalence: `σ(Uᵀ A V) = σ(A)`. -/
theorem sortedSingularValues_transpose_mul_mul {m n : ℕ} {U : Matrix (Fin m) (Fin m) ℝ}
    (hU : U ∈ orthogonalGroup (Fin m) ℝ) {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (Uᵀ * A * V).sortedSingularValues = A.sortedSingularValues := by
  have hUt : Uᵀ ∈ orthogonalGroup (Fin m) ℝ := by
    rw [mem_orthogonalGroup_iff, transpose_transpose]
    exact (mem_orthogonalGroup_iff' _ _).1 hU
  have key : toEuclideanLin (Uᵀ * A * V) =
      (unitaryLinearIsometryEquiv hUt).toLinearIsometry.toLinearMap ∘ₗ toEuclideanLin A ∘ₗ
        (unitaryLinearIsometryEquiv hV).toLinearIsometry.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    simp only [toEuclideanLin_mul_apply, LinearMap.comp_apply]
    rfl
  funext i
  change (toEuclideanLin (Uᵀ * A * V)).singularValues i = (toEuclideanLin A).singularValues i
  rw [key, LinearMap.singularValues_comp_linearIsometryEquiv]

/-- **(10.4.1)**: for `A ∈ ℝ^{m×n}`, `m ≥ n`, there are orthogonal `U`, `V` with `Uᵀ A V = B` zero
below row `n` and upper bidiagonal on top, and `A`, `B` have the same singular values. Backbone
`Matrix.exists_orthogonal_mul_mul_orthogonal_isUpperBidiagonal` (chapter 5's Householder
bidiagonalization computes it). -/
theorem equation_10_4_1 {m n : ℕ} (hnm : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U ∈ orthogonalGroup (Fin m) ℝ, ∃ V ∈ orthogonalGroup (Fin n) ℝ,
      (∀ (i : Fin m) (j : Fin n), n ≤ (i : ℕ) → (Uᵀ * A * V) i j = 0) ∧
      ((Uᵀ * A * V).submatrix (Fin.castLE hnm) id).IsUpperBidiagonal ∧
      (Uᵀ * A * V).sortedSingularValues = A.sortedSingularValues := by
  obtain ⟨U, hU, V, hV, h1, h2⟩ := exists_orthogonal_mul_mul_orthogonal_isUpperBidiagonal hnm A
  rw [conjTranspose_eq_transpose_of_trivial] at h1 h2
  exact ⟨U, hU, V, hV, h1, h2, sortedSingularValues_transpose_mul_mul hU hV A⟩

section Columns

variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
  {V : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin m) (Fin n) ℝ}

/-- `A V = U B` from `Uᵀ A V = B` with `U` orthogonal. -/
private theorem mul_eq_mul_of_transpose_mul_mul (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hB : Uᵀ * A * V = B) : A * V = U * B := by
  rw [← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, (mem_orthogonalGroup_iff _ _).1 hU,
    Matrix.one_mul]

/-- `Aᵀ U = V Bᵀ` from `Uᵀ A V = B` with `V` orthogonal. -/
private theorem transpose_mul_eq_mul_transpose (hV : V ∈ orthogonalGroup (Fin n) ℝ)
    (hB : Uᵀ * A * V = B) : Aᵀ * U = V * Bᵀ := by
  rw [← hB, transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, (mem_orthogonalGroup_iff _ _).1 hV, Matrix.one_mul]

/-- **(10.4.2)**: in the setting of (10.4.1) (`Uᵀ A V = B` upper bidiagonal, `U`, `V` orthogonal,
`n ≤ m`), `A v_k = α_k u_k + β_{k−1} u_{k−1}` for `k = 1 : n` (`β_0 u_0 = 0`), with `α_k`, `β_{k−1}`
the entries `B(k, k)`, `B(k−1, k)`: column `k` of `A V = U B`. -/
theorem equation_10_4_2 (hnm : n ≤ m) (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hB : Uᵀ * A * V = B) (hBb : B.IsUpperBidiagonalRect) (k : Fin n) :
    A *ᵥ V.col k = B (Fin.castLE hnm k) k • U.col (Fin.castLE hnm k) +
      (if h : 0 < (k : ℕ) then B ⟨k - 1, by omega⟩ k • U.col ⟨k - 1, by omega⟩ else 0) := by
  have hAV := mul_eq_mul_of_transpose_mul_mul hU hB
  ext x
  have h1 : (A *ᵥ V.col k) x = (U * B) x k := by
    rw [← hAV, mul_apply, mulVec, dotProduct]
    rfl
  rw [h1, mul_apply]
  have hz : ∀ i : Fin m, (i : ℕ) ≠ k → (i : ℕ) + 1 ≠ k → U x i * B i k = 0 :=
    fun i h1 h2 => by rw [hBb i k (Ne.symm h1) (Ne.symm h2), mul_zero]
  split_ifs with hk
  · rw [Fintype.sum_eq_add (Fin.castLE hnm k) ⟨k - 1, by omega⟩
      (fun h => by have := congrArg Fin.val h; simp at this; omega)
      (fun i hi => hz i (fun h => hi.1 (Fin.ext (by simpa using h)))
        (fun h => hi.2 (Fin.ext (by simp; omega))))]
    simp [mul_comm]
  · rw [Fintype.sum_eq_single (Fin.castLE hnm k)
      (fun i hi => hz i (fun h => hi (Fin.ext (by simpa using h))) (by omega))]
    simp [mul_comm]

/-- **(10.4.3)**: in the setting of (10.4.1), `Aᵀ u_k = α_k v_k + β_k v_{k+1}` for `k = 1 : n`
(`β_n v_{n+1} = 0`), with `α_k = B(k, k)`, `β_k = B(k, k+1)`: column `k` of `Aᵀ U = V Bᵀ`. -/
theorem equation_10_4_3 (hnm : n ≤ m) (hV : V ∈ orthogonalGroup (Fin n) ℝ)
    (hB : Uᵀ * A * V = B) (hBb : B.IsUpperBidiagonalRect) (k : Fin n) :
    Aᵀ *ᵥ U.col (Fin.castLE hnm k) = B (Fin.castLE hnm k) k • V.col k +
      (if h : (k : ℕ) + 1 < n then B (Fin.castLE hnm k) ⟨k + 1, h⟩ • V.col ⟨k + 1, h⟩
        else 0) := by
  have hAU := transpose_mul_eq_mul_transpose hV hB
  ext x
  have h1 : (Aᵀ *ᵥ U.col (Fin.castLE hnm k)) x = (V * Bᵀ) x (Fin.castLE hnm k) := by
    rw [← hAU, mul_apply, mulVec, dotProduct]
    rfl
  rw [h1, mul_apply]
  have hz : ∀ i : Fin n, i ≠ k → (i : ℕ) ≠ k + 1 → V x i * Bᵀ i (Fin.castLE hnm k) = 0 :=
    fun i h1 h2 => by
      rw [transpose_apply, hBb _ i (by simpa [Fin.ext_iff] using h1) (by simpa using h2),
        mul_zero]
  split_ifs with hk
  · rw [Fintype.sum_eq_add k ⟨k + 1, hk⟩ (fun h => by have := congrArg Fin.val h; simp at this)
      (fun i hi => hz i hi.1 (fun h => hi.2 (Fin.ext h)))]
    simp [mul_comm]
  · rw [Fintype.sum_eq_single k (fun i hi => hz i hi (by have := i.isLt; omega))]
    simp [mul_comm]

/-- A sum over `Fin m` whose terms vanish from index `k` on is the sum over `Fin k`. -/
private theorem sum_fin_eq_sum_castLE {M : Type*} [AddCommMonoid M] {k m : ℕ} (hkm : k ≤ m)
    (f : Fin m → M) (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) :
    ∑ i, f i = ∑ i : Fin k, f (Fin.castLE hkm i) := by
  rw [show (∑ i : Fin k, f (Fin.castLE hkm i)) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb hkm), f i by
    rw [Finset.sum_map]; rfl]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_).symm
  by_contra h
  exact hi (Finset.mem_map.2 ⟨⟨i, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/-- **(10.4.6)**: in the setting of (10.4.2), `A V(:, 1:k) = U(:, 1:k) B(1:k, 1:k)` for every
`k ≤ n`. The book prints `A U(:, 1:k) = V(:, 1:k) B(1:k, 1:k)`, which does not typecheck, and
attributes the identity to `β_k = 0`, which only (10.4.7) needs. -/
theorem equation_10_4_6 (hnm : n ≤ m) (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hB : Uᵀ * A * V = B) (hBb : B.IsUpperBidiagonalRect) {k : ℕ} (hk : k ≤ n) :
    A * V.submatrix id (Fin.castLE hk) =
      U.submatrix id (Fin.castLE (hk.trans hnm)) *
        B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk) := by
  have hAV := mul_eq_mul_of_transpose_mul_mul hU hB
  ext x j
  have h1 : (A * V.submatrix id (Fin.castLE hk)) x j = (U * B) x (Fin.castLE hk j) := by
    rw [← hAV]
    rfl
  rw [h1, mul_apply, mul_apply, sum_fin_eq_sum_castLE (hk.trans hnm) _ fun i hi => by
    rw [hBb i _ (by simp; omega) (by simp; omega), mul_zero]]
  rfl

/-- **(10.4.7)**: if `β_k = 0` (`B(k, k+1) = 0`), then `Aᵀ U(:, 1:k) = V(:, 1:k) B(1:k, 1:k)ᵀ` (the
book's `Aᵀ V(:, 1:k) = U(:, 1:k) …` swaps `U` and `V`), and hence
`Aᵀ A V(:, 1:k) = V(:, 1:k) B(1:k, 1:k)ᵀ B(1:k, 1:k)`. -/
theorem equation_10_4_7 (hnm : n ≤ m) (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) (hB : Uᵀ * A * V = B) (hBb : B.IsUpperBidiagonalRect)
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) (hβ : ∀ h : k < n, B ⟨k - 1, by omega⟩ ⟨k, h⟩ = 0) :
    Aᵀ * U.submatrix id (Fin.castLE (hk.trans hnm)) =
        V.submatrix id (Fin.castLE hk) *
          (B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk))ᵀ ∧
      Aᵀ * A * V.submatrix id (Fin.castLE hk) =
        V.submatrix id (Fin.castLE hk) *
          ((B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk))ᵀ *
            B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk)) := by
  have hAU := transpose_mul_eq_mul_transpose hV hB
  have h1 : Aᵀ * U.submatrix id (Fin.castLE (hk.trans hnm)) =
      V.submatrix id (Fin.castLE hk) *
        (B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk))ᵀ := by
    ext x j
    have e : (Aᵀ * U.submatrix id (Fin.castLE (hk.trans hnm))) x j =
        (V * Bᵀ) x (Fin.castLE (hk.trans hnm) j) := by
      rw [← hAU]
      rfl
    rw [e, mul_apply, mul_apply, sum_fin_eq_sum_castLE hk _ fun i hi => ?_]
    · rfl
    · rw [transpose_apply]
      by_cases h2 : (i : ℕ) = k ∧ (j : ℕ) + 1 = k
      · have hz := hβ (by rw [← h2.1]; exact i.isLt)
        have hB0 : B (Fin.castLE (hk.trans hnm) j) i = 0 := by
          convert hz using 2 <;> apply Fin.ext <;> simp <;> omega
        rw [hB0, mul_zero]
      · rw [hBb _ i (by simp; omega) (by simp; omega), mul_zero]
  refine ⟨h1, ?_⟩
  rw [Matrix.mul_assoc, equation_10_4_6 hnm hU hB hBb hk, ← Matrix.mul_assoc, h1,
    Matrix.mul_assoc]

end Columns

/-- **The singular values of `B(1:k, 1:k)` are singular values of `A`** (§10.4.1, after (10.4.7)):
if `β_k = 0`, every singular value of `B_k = B(1:k, 1:k)` is a singular value of `A`: the range of
`V(:, 1:k)` is `AᵀA`-invariant with `AᵀA` acting as `B_kᵀ B_k` there ((10.4.7)), so an eigenvector
`y` of `B_kᵀ B_k` gives the eigenvector `V(:, 1:k) y` of `AᵀA` for the same eigenvalue, and singular
values are the square roots of these eigenvalues (`Matrix.sq_singularValues`). -/
theorem singularValues_bidiag_subset {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin m) (Fin n) ℝ}
    (hnm : n ≤ m) (hU : U ∈ orthogonalGroup (Fin m) ℝ) (hV : V ∈ orthogonalGroup (Fin n) ℝ)
    (hB : Uᵀ * A * V = B) (hBb : B.IsUpperBidiagonalRect) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    (hβ : ∀ h : k < n, B ⟨k - 1, by omega⟩ ⟨k, h⟩ = 0) (i : Fin k) :
    ∃ j : Fin n, (B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk)).singularValues i =
      A.singularValues j := by
  set Bk := B.submatrix (Fin.castLE (hk.trans hnm)) (Fin.castLE hk) with hBk
  set Vk := V.submatrix id (Fin.castLE hk) with hVk
  have hgram := (equation_10_4_7 hnm hU hV hB hBb hk1 hk hβ).2
  have hVkV : Vkᵀ * Vk = 1 := by
    ext a b
    have h := congrFun (congrFun ((mem_orthogonalGroup_iff' _ _).1 hV) (Fin.castLE hk a))
      (Fin.castLE hk b)
    simpa [hVk, mul_apply, one_apply, Fin.ext_iff] using h
  set hH := isHermitian_conjTranspose_mul_self Bk
  set y : Fin k → ℝ := ⇑(hH.eigenvectorBasis i) with hy
  have hy0 : y ≠ 0 := by
    intro h
    rw [hy] at h
    apply hH.eigenvectorBasis.orthonormal.ne_zero i
    ext a
    simpa using congrFun h a
  have hey : (Bkᴴ * Bk) *ᵥ y = hH.eigenvalues i • y := hH.mulVec_eigenvectorBasis i
  rw [← conjTranspose_eq_transpose_of_trivial Bk] at hgram
  -- the eigenvector of `AᵀA`
  have hAA : (Aᵀ * A) *ᵥ (Vk *ᵥ y) = hH.eigenvalues i • (Vk *ᵥ y) := by
    rw [mulVec_mulVec, hgram, ← mulVec_mulVec, hey, mulVec_smul]
  have hVy : Vk *ᵥ y ≠ 0 := by
    intro h
    apply hy0
    have := congrArg (Vkᵀ *ᵥ ·) h
    simpa only [mulVec_mulVec, hVkV, one_mulVec, mulVec_zero] using this
  have hG := isHermitian_conjTranspose_mul_self A
  have hspec : hH.eigenvalues i ∈ spectrum ℝ (Aᴴ * A) := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
      ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨Vk *ᵥ y, hVy, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, sub_mulVec, smul_mulVec, one_mulVec,
      conjTranspose_eq_transpose_of_trivial A, hAA, sub_self]
  rw [hG.spectrum_real_eq_range_eigenvalues] at hspec
  obtain ⟨j, hj⟩ := hspec
  refine ⟨j, ?_⟩
  have h1 := Bk.sq_singularValues i
  have h2 := A.sq_singularValues j
  rw [← hj] at h1
  rw [← h2] at h1
  exact (pow_left_inj₀ (Bk.singularValues_nonneg i) (A.singularValues_nonneg j)
    two_ne_zero).1 h1

/-! ### The Golub–Kahan relations (§10.4.1) -/

section GolubKahan

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))

/-- **(10.4.9)**: `A V_k = U_k B_k` for the Golub–Kahan matrices, `B_k` the upper bidiagonal
matrix (10.4.8) of the `α_j`, `β_j` (at every `k`; past breakdown both sides have zero columns).
Backbone `GolubKahan.mul_rightMatrix`. -/
theorem equation_10_4_9 (k : ℕ) :
    A * GolubKahan.rightMatrix A v k =
      GolubKahan.leftMatrix A v k *
        GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k := by
  have h := GolubKahan.mul_rightMatrix A v k
  rw [conjTranspose_eq_transpose_of_trivial] at h
  simpa using h

/-- **(10.4.10)**: `Aᵀ U_k = V_k B_kᵀ + p_k e_kᵀ` with `p_k = β_k v_{k+1}` (`k ≥ 1`; the backbone's
`β_{k−1}` and `v_k`, `0`-based). Backbone `GolubKahan.conjTranspose_mul_leftMatrix`
(`Aᵀ U_k = V_{k+1} B̄_k`) split into the first `k` columns of `V_{k+1}` and the last. -/
theorem equation_10_4_10 {k : ℕ} (hk : 1 ≤ k) :
    Aᵀ * GolubKahan.leftMatrix A v k =
      GolubKahan.rightMatrix A v k *
          (GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k)ᵀ +
        vecMulVec (GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (k - 1) •
            (GolubKahan.rightVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v k).ofLp)
          (Krylov.lastVec (1 : ℝ) k) := by
  have h := GolubKahan.conjTranspose_mul_leftMatrix A v k
  rw [conjTranspose_eq_transpose_of_trivial] at h
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
  have hsub := GolubKahan.bidiagLower_submatrix_castSucc (toEuclideanLin A) (toEuclideanLin Aᵀ)
    v k
  rw [h]
  ext x j
  rw [Matrix.add_apply, mul_apply, Fin.sum_univ_castSucc, mul_apply, vecMulVec_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (congrFun hsub i) j
    simp only [submatrix_apply, id] at this
    rw [this]
    rfl
  · have hj := j.isLt
    simp only [GolubKahan.rightMatrix, of_apply, Fin.val_last, GolubKahan.bidiagLower_apply,
      Krylov.lastVec, Pi.smul_apply, smul_eq_mul, conjTranspose_eq_transpose_of_trivial]
    by_cases h1 : (j : ℕ) + 1 = k
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left h1,
        show k - 1 = j by omega]
      ring
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h1]
      ring

/-- **(10.4.11)**: `span {v_1, …, v_k} = 𝒦(AᵀA, v_c, k)`. Backbone `GolubKahan.span_rightVec`. -/
theorem equation_10_4_11 (k : ℕ) :
    Submodule.span ℝ (GolubKahan.rightVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin (Aᵀ * A)) v k := by
  rw [GolubKahan.span_rightVec, toEuclideanLin_mul]

/-- **(10.4.12)**: `span {u_1, …, u_k} = 𝒦(AAᵀ, A v_c, k)`. Backbone `GolubKahan.span_leftVec`. -/
theorem equation_10_4_12 (k : ℕ) :
    Submodule.span ℝ (GolubKahan.leftVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v '' Set.Iio k) =
      Krylov.subspace (toEuclideanLin (A * Aᵀ)) (toEuclideanLin A v) k := by
  rw [GolubKahan.span_leftVec, toEuclideanLin_mul]

/-- **The Lanczos connection** (§10.4.1, "the symmetric Lanczos convergence theory … can be
applied"): `B_kᵀ B_k = T_k(AᵀA, v_c)`, the Lanczos tridiagonal matrix of `AᵀA` from `v_c`; so the
squared singular values of `B_k` are the Ritz values of `AᵀA` on `𝒦(AᵀA, v_c, k)`
(`Lanczos.ritzValues`), which Theorems 10.1.2–10.1.4 bound. Backbone
`GolubKahan.bidiag_conjTranspose_mul_bidiag`. -/
theorem bidiag_transpose_mul_bidiag (k : ℕ) :
    (GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k)ᵀ *
        GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k =
      Lanczos.tridiag (toEuclideanLin (Aᵀ * A)) v k := by
  have h := GolubKahan.bidiag_conjTranspose_mul_bidiag (A := toEuclideanLin A)
    (Astar := toEuclideanLin Aᵀ) v (fun u x => by
      have := toEuclideanLin_conjTranspose_inner_left A x u
      rwa [conjTranspose_eq_transpose_of_trivial] at this) k
  rw [conjTranspose_eq_transpose_of_trivial] at h
  rw [h, toEuclideanLin_mul]

/-! ### Ritz approximations (§10.4.2) -/

/-- **(10.4.14)**: with an SVD `F_kᵀ B_k G_k = Γ = diag(γ_1, …, γ_k)` (10.4.13) of `B_k`
(`F_k`, `G_k` orthogonal), `Y_k = V_k G_k` and `Z_k = U_k F_k` satisfy `A Y_k = Z_k Γ`, i.e.
`A y_i = γ_i z_i`. From (10.4.9). -/
theorem equation_10_4_14 {k : ℕ} {F G : Matrix (Fin k) (Fin k) ℝ}
    (hF : F ∈ orthogonalGroup (Fin k) ℝ) {γ : Fin k → ℝ}
    (hSVD : Fᵀ * GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k * G = diagonal γ) :
    A * (GolubKahan.rightMatrix A v k * G) = (GolubKahan.leftMatrix A v k * F) * diagonal γ := by
  rw [← Matrix.mul_assoc, equation_10_4_9, ← hSVD]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (GolubKahan.leftMatrix A v k) F Fᵀ, (mem_orthogonalGroup_iff _ _).1 hF,
    Matrix.mul_one]

/-- **(10.4.15)**: in the setting of (10.4.14), with `G_k` orthogonal as well,
`Aᵀ Z_k = Y_k Γ + p_k e_kᵀ F_k`, i.e. `Aᵀ z_i = γ_i y_i + [F_k]_{ki} p_k`. From (10.4.10). -/
theorem equation_10_4_15 {k : ℕ} (hk : 1 ≤ k) {F G : Matrix (Fin k) (Fin k) ℝ}
    (hF : F ∈ orthogonalGroup (Fin k) ℝ) (hG : G ∈ orthogonalGroup (Fin k) ℝ) {γ : Fin k → ℝ}
    (hSVD : Fᵀ * GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k * G = diagonal γ) :
    Aᵀ * (GolubKahan.leftMatrix A v k * F) =
      (GolubKahan.rightMatrix A v k * G) * diagonal γ +
        vecMulVec (GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (k - 1) •
            (GolubKahan.rightVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v k).ofLp)
          (Krylov.lastVec (1 : ℝ) k ᵥ* F) := by
  set Bk := GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k
  have hBF : Bkᵀ * F = G * diagonal γ := by
    have hB : Bk = F * diagonal γ * Gᵀ := by
      rw [← hSVD]
      simp only [← Matrix.mul_assoc]
      rw [(mem_orthogonalGroup_iff _ _).1 hF, Matrix.one_mul, Matrix.mul_assoc,
        (mem_orthogonalGroup_iff _ _).1 hG, Matrix.mul_one]
    rw [hB, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
      Matrix.mul_assoc, Matrix.mul_assoc, (mem_orthogonalGroup_iff' _ _).1 hF, Matrix.mul_one]
  rw [← Matrix.mul_assoc, equation_10_4_10 A v hk, Matrix.add_mul, vecMulVec_mul,
    Matrix.mul_assoc, hBF, Matrix.mul_assoc]

end GolubKahan

/-! ### The lower bidiagonal form (§10.4.4) -/

/-- **(10.4.18)**: for `A ∈ ℝ^{m×n}` there are orthogonal `U`, `V` with `Uᵀ A V = B` lower
bidiagonal (entries only at `(i, i)` and `(i + 1, i)`, so that for `m > n` only the first `n + 1`
rows can be nonzero): the transpose of the upper bidiagonalization of `Aᵀ`
(`Matrix.exists_unitary_mul_mul_unitary_apply_eq_zero`). -/
theorem equation_10_4_18 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U ∈ orthogonalGroup (Fin m) ℝ, ∃ V ∈ orthogonalGroup (Fin n) ℝ,
      (Uᵀ * A * V).IsLowerBidiagonalRect := by
  obtain ⟨U', hU', V', hV', h⟩ := exists_unitary_mul_mul_unitary_apply_eq_zero Aᵀ
  refine ⟨V', hV', U', hU', fun i j h1 h2 => ?_⟩
  have := h j i (Ne.symm h1) (fun h' => h2 (by omega))
  rw [conjTranspose_eq_transpose_of_trivial] at this
  have e : V'ᵀ * A * U' = (U'ᵀ * Aᵀ * V')ᵀ := by
    simp [transpose_mul, Matrix.mul_assoc]
  rw [e, transpose_apply]
  exact this

/-- **(10.4.19)**, Paige–Saunders: the lower bidiagonalization of `A` from `u_c ∈ ℝ^m` is the
Golub–Kahan process of `Aᵀ` from `u_c` (Algorithm 10.4.2 is Algorithm 10.4.1 for `Aᵀ`): its `u_j`
are `GolubKahan.rightVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u_c (j − 1)` and its `v_j` the
corresponding `leftVec`, and after `k` steps `A V(:, 1:k) = U(:, 1:k) B(1:k, 1:k) + p_k e_kᵀ` with
`B(1:k, 1:k)` lower bidiagonal (the transpose of the upper `B_k` of `Aᵀ`) and `p_k = β_{k+1}
u_{k+1}`. Equation (10.4.10) for `Aᵀ`. -/
theorem equation_10_4_19 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin m))
    {k : ℕ} (hk : 1 ≤ k) :
    A * GolubKahan.leftMatrix Aᵀ u k =
      GolubKahan.rightMatrix Aᵀ u k *
          (GolubKahan.bidiag (toEuclideanLin Aᵀ) (toEuclideanLin A) u k)ᵀ +
        vecMulVec (GolubKahan.beta (toEuclideanLin Aᵀ) (toEuclideanLin A) u (k - 1) •
            (GolubKahan.rightVec (toEuclideanLin Aᵀ) (toEuclideanLin A) u k).ofLp)
          (Krylov.lastVec (1 : ℝ) k) := by
  have h := equation_10_4_10 Aᵀ u hk
  rwa [transpose_transpose] at h

/-! ### Randomized low-rank approximation (§10.4.5) -/

/-- `Z̃₁ Z̃₁ᵀ = U P_k Uᵀ` for the first `k` columns `Z̃₁ = U(:, 1:k)` of `U`, `P_k` the diagonal
projector onto the first `k` coordinates. -/
private theorem submatrix_castLE_mul_transpose {m k : ℕ} (hkm : k ≤ m)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    U.submatrix id (Fin.castLE hkm) * (U.submatrix id (Fin.castLE hkm))ᵀ =
      U * (rectDiagonal fun i => if i < k then (1 : ℝ) else 0) * Uᵀ := by
  ext a b
  simp only [mul_apply, submatrix_apply, id_eq, transpose_apply, rectDiagonal_apply]
  set F : ℕ → ℝ := fun i => if h : i < m then U a ⟨i, h⟩ * U b ⟨i, h⟩ else 0 with hF
  have h1 : ∀ j : Fin k, U a (Fin.castLE hkm j) * U b (Fin.castLE hkm j) = F j := fun j => by
    have hj : (j : ℕ) < m := by omega
    simp only [hF, hj, ↓reduceDIte]
    rfl
  have h2 : ∀ i : Fin m,
      (∑ l : Fin m, U a l * (if (l : ℕ) = i then (if (l : ℕ) < k then (1 : ℝ) else 0) else 0)) *
        U b i = (fun i : ℕ => if i < k then F i else 0) i := fun i => by
    rw [Finset.sum_eq_single i (fun l _ hl => by rw [ite_eq_right (fun h => hl (Fin.ext h)),
      mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
    simp only [hF, i.isLt, ↓reduceDIte, ite_true]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_congr rfl fun i _ => h2 i,
    Fin.sum_univ_eq_sum_range F k,
    Fin.sum_univ_eq_sum_range (fun i => if i < k then F i else 0) m, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

open scoped Matrix.Norms.L2Operator in
/-- **(10.4.20)**: for an SVD `A = Z̃ Σ̃ Ỹᵀ` (`IsSVD A Z̃ σ Ỹ`) and `k ≤ rank A`, the truncation
`Ã_k = Z̃₁ Σ̃₁ Ỹ₁ᵀ` (`Matrix.svdTruncation`, (2.4.3)) equals `Z̃₁ Z̃₁ᵀ A`, `Z̃₁ = Z̃(:, 1:k)`, has
rank `k`, and is a closest matrix of rank at most `k` to `A` in the 2-norm (Eckart–Young,
chapter 2's Theorem 2.4.8; the Frobenius half is `equation_10_4_20_frobenius`). Backbone
`Matrix.rank_svdTruncation`, `Matrix.l2_opNorm_sub_svdTruncation` and
`Matrix.isLeast_l2_opNorm_sub_of_rank_le` (chapter 2's §2.4 restatements are not yet written). -/
theorem equation_10_4_20 {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V)
    {k : ℕ} (hk : k ≤ A.rank) :
    let Z₁ := U.submatrix id
      (Fin.castLE (hk.trans ((rank_le_card_height A).trans_eq (Fintype.card_fin m))))
    svdTruncation U σ V k = Z₁ * Z₁ᵀ * A ∧ (svdTruncation U σ V k).rank = k ∧
      ∀ B : Matrix (Fin m) (Fin n) ℝ, B.rank ≤ k →
        ‖A - svdTruncation U σ V k‖ ≤ ‖A - B‖ := by
  intro Z₁
  have hkm : k ≤ m := hk.trans ((rank_le_card_height A).trans_eq (Fintype.card_fin m))
  refine ⟨?_, rank_svdTruncation h hk, fun B hB => ?_⟩
  · have hUU : Uᵀ * U = 1 := by
      have := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_left
      rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
    have hPR : (rectDiagonal fun i => if i < k then (1 : ℝ) else 0 : Matrix (Fin m) (Fin m) ℝ) *
        (rectDiagonal fun i => ((σ i : ℝ) : ℝ) : Matrix (Fin m) (Fin n) ℝ) =
          rectDiagonal fun i => if i < k then σ i else 0 := by
      rw [rectDiagonal_mul_rectDiagonal]
      congr 1
      funext i
      split_ifs <;> first | simp | omega
    simp only [Z₁]
    rw [submatrix_castLE_mul_transpose hkm]
    conv_rhs => rw [h.eq_mul_mul_star]
    simp only [Matrix.mul_assoc, RCLike.ofReal_real_eq_id, id]
    rw [← Matrix.mul_assoc Uᵀ U, hUU, Matrix.one_mul, ← Matrix.mul_assoc _ _ (star V), hPR]
    simp only [svdTruncation, Matrix.mul_assoc, RCLike.ofReal_real_eq_id, id]
  · rw [l2_opNorm_sub_svdTruncation h k]
    exact (isLeast_l2_opNorm_sub_of_rank_le A k).2 ⟨B, hB, rfl⟩

open scoped Matrix.Norms.Frobenius in
/-- **(10.4.20), Frobenius half**: the truncation `Ã_k` of an SVD is a closest matrix of rank at
most `k` to `A` in the Frobenius norm (the Eckart–Young–Mirsky remark after chapter 2's
Theorem 2.4.8). Backbone `Matrix.frobenius_norm_sub_svdTruncation` and
`Matrix.isLeast_frobenius_norm_sub_of_rank_le`. -/
theorem equation_10_4_20_frobenius {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ} (h : IsSVD A U σ V)
    (k : ℕ) (B : Matrix (Fin m) (Fin n) ℝ) (hB : B.rank ≤ k) :
    ‖A - svdTruncation U σ V k‖ ≤ ‖A - B‖ := by
  rw [frobenius_norm_sub_svdTruncation h k]
  have := (isLeast_frobenius_norm_sub_of_rank_le A k).2 ⟨B, hB, rfl⟩
  simpa only [Fintype.card_fin] using this

/-! ### The CUR identities (§10.4.5) -/

section CUR

variable {m c k r s : ℕ} {C : Matrix (Fin m) (Fin c) ℝ} {Z₁ : Matrix (Fin m) (Fin k) ℝ}
  {Z₂ : Matrix (Fin m) (Fin r) ℝ} {σ₁ : Fin k → ℝ} {σ₂ : Fin r → ℝ}
  {Y₁ : Matrix (Fin c) (Fin k) ℝ} {Y₂ : Matrix (Fin c) (Fin r) ℝ}

/-- **(10.4.22)**: for `C ∈ ℝ^{m×c}` with SVD `C = Z₁ Σ₁ Y₁ᵀ + Z₂ Σ₂ Y₂ᵀ` (`Y = [Y₁ | Y₂]`
orthogonal, so `Y₁ᵀ Y₁ = I` and `Y₂ᵀ Y₁ = 0`; `Σ₁ = diag(σ₁)` nonsingular) and
`Φ = Y₁ Σ₁⁻² Y₁ᵀ`: `C Φ = Z₁ Σ₁⁻¹ Y₁ᵀ`. -/
theorem equation_10_4_22 (hC : C = Z₁ * diagonal σ₁ * Y₁ᵀ + Z₂ * diagonal σ₂ * Y₂ᵀ)
    (hY₁ : Y₁ᵀ * Y₁ = 1) (hY₂₁ : Y₂ᵀ * Y₁ = 0) (hσ : ∀ i, σ₁ i ≠ 0) :
    C * (Y₁ * diagonal (fun i => (σ₁ i)⁻¹ ^ 2) * Y₁ᵀ) =
      Z₁ * diagonal (fun i => (σ₁ i)⁻¹) * Y₁ᵀ := by
  have hd : diagonal σ₁ * diagonal (fun i => (σ₁ i)⁻¹ ^ 2) = diagonal (fun i => (σ₁ i)⁻¹) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    field_simp [hσ i]
  rw [hC, Matrix.add_mul]
  have e1 : Z₁ * diagonal σ₁ * Y₁ᵀ * (Y₁ * diagonal (fun i => (σ₁ i)⁻¹ ^ 2) * Y₁ᵀ) =
      Z₁ * diagonal (fun i => (σ₁ i)⁻¹) * Y₁ᵀ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Y₁ᵀ Y₁, hY₁, Matrix.one_mul, ← Matrix.mul_assoc (diagonal σ₁), hd]
  have e2 : Z₂ * diagonal σ₂ * Y₂ᵀ * (Y₁ * diagonal (fun i => (σ₁ i)⁻¹ ^ 2) * Y₁ᵀ) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Y₂ᵀ Y₁, hY₂₁, Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  rw [e1, e2, add_zero]

/-- Selecting rows commutes with multiplying on the right: `(M N)(row, :) = M(row, :) N`. -/
private theorem submatrix_mul_id {p q t : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (N : Matrix (Fin q) (Fin t) ℝ) (row : Fin s → Fin p) :
    (M * N).submatrix row id = M.submatrix row id * N := by
  ext i j
  simp [mul_apply]

/-- **(10.4.23)**: with a row selection `row : Fin s → Fin m`, a diagonal scaling `D_R = diag(d)`,
`R = D_R A(row, :)` and `Ψ = D_R C(row, :)`:
`Ψᵀ R = (D_R (Z₁(row, :) Σ₁ Y₁ᵀ + Z₂(row, :) Σ₂ Y₂ᵀ))ᵀ D_R A(row, :)` — the SVD substituted in the
selected rows. The book's left side is printed `Ψᵀ R` here but `Ψ R` in (10.4.24). -/
theorem equation_10_4_23 {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (row : Fin s → Fin m)
    (d : Fin s → ℝ) (hC : C = Z₁ * diagonal σ₁ * Y₁ᵀ + Z₂ * diagonal σ₂ * Y₂ᵀ) :
    (diagonal d * C.submatrix row id)ᵀ * (diagonal d * A.submatrix row id) =
      (diagonal d * (Z₁.submatrix row id * diagonal σ₁ * Y₁ᵀ +
          Z₂.submatrix row id * diagonal σ₂ * Y₂ᵀ))ᵀ * (diagonal d * A.submatrix row id) := by
  rw [hC, submatrix_add, Pi.add_apply, Pi.add_apply, submatrix_mul_id, submatrix_mul_id,
    submatrix_mul_id, submatrix_mul_id]

/-- **(10.4.24)**: with `U = Φ Ψᵀ`, `C U R = (C Φ)(Ψᵀ R) = Z₁ (D_R Z₁(row, :))ᵀ (D_R A(row, :))` —
the book prints `(CΦ)(ΨR)` and omits the transpose. From (10.4.22), (10.4.23) and `Y₁ᵀ Y₂ = 0`. -/
theorem equation_10_4_24 {n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (row : Fin s → Fin m)
    (d : Fin s → ℝ) (hC : C = Z₁ * diagonal σ₁ * Y₁ᵀ + Z₂ * diagonal σ₂ * Y₂ᵀ)
    (hY₁ : Y₁ᵀ * Y₁ = 1) (hY₂₁ : Y₂ᵀ * Y₁ = 0) (hσ : ∀ i, σ₁ i ≠ 0) :
    C * ((Y₁ * diagonal (fun i => (σ₁ i)⁻¹ ^ 2) * Y₁ᵀ) * (diagonal d * C.submatrix row id)ᵀ) *
        (diagonal d * A.submatrix row id) =
      Z₁ * (diagonal d * Z₁.submatrix row id)ᵀ * (diagonal d * A.submatrix row id) := by
  have hY₁₂ : Y₁ᵀ * Y₂ = 0 := by
    rw [← transpose_transpose (Y₁ᵀ * Y₂), transpose_mul, transpose_transpose, hY₂₁,
      transpose_zero]
  have hinv : diagonal (fun i => (σ₁ i)⁻¹) * diagonal σ₁ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hσ i)
  rw [← Matrix.mul_assoc C, equation_10_4_22 hC hY₁ hY₂₁ hσ, Matrix.mul_assoc,
    equation_10_4_23 A row d hC]
  simp only [transpose_mul, transpose_add, transpose_transpose, diagonal_transpose,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Y₁ᵀ Y₁, hY₁, Matrix.one_mul, ← Matrix.mul_assoc Y₁ᵀ Y₂, hY₁₂]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  rw [← Matrix.mul_assoc (diagonal fun i => (σ₁ i)⁻¹), hinv, Matrix.one_mul]

end CUR

/-! ### Ritz pairs of `AᵀA` (§10.4.2) -/

/-- **Ritz pairs of `AᵀA`** (§10.4.2, after (10.4.15)): in the setting of (10.4.14)–(10.4.15),
`AᵀA y_i = γ_i² y_i + γ_i [F_k]_{ki} p_k` (the book prints `γ_i² z_i + [F_k]_{ki} p_k`), and
`(γ_i², y_i)` is a Ritz pair of `AᵀA` with respect to `ran(V_k) = 𝒦(AᵀA, v_c, k)` (the book writes
`{γ_i, y_i}`): `B_kᵀ B_k = T_k(AᵀA)` has the eigenvector `G_k e_i` for `γ_i²`
(`Arnoldi.isRitzPair_of_mulVec_eq_smul`). Here `y_i = Y_k e_i`, `k ≤` the grade of `v_c`. -/
theorem isRitzPair_gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : EuclideanSpace ℝ (Fin n))
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ grade (toEuclideanLin (Aᵀ * A)) v)
    {F G : Matrix (Fin k) (Fin k) ℝ} (hF : F ∈ orthogonalGroup (Fin k) ℝ)
    (hG : G ∈ orthogonalGroup (Fin k) ℝ) {γ : Fin k → ℝ}
    (hSVD : Fᵀ * GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k * G = diagonal γ)
    (i : Fin k) :
    let y := (GolubKahan.rightMatrix A v k * G) *ᵥ Pi.single i 1
    let p := GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (k - 1) •
      (GolubKahan.rightVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v k).ofLp
    (Aᵀ * A) *ᵥ y = (γ i ^ 2) • y + (γ i * F ⟨k - 1, by omega⟩ i) • p ∧
      Krylov.IsRitzPair (toEuclideanLin (Aᵀ * A))
        (Krylov.subspace (toEuclideanLin (Aᵀ * A)) v k) (γ i ^ 2) (WithLp.toLp 2 y) := by
  intro y p
  set Bk := GolubKahan.bidiag (toEuclideanLin A) (toEuclideanLin Aᵀ) v k with hBk
  have hGG : Gᵀ * G = 1 := (mem_orthogonalGroup_iff' _ _).1 hG
  have hB : Bk = F * diagonal γ * Gᵀ := by
    rw [← hSVD]
    simp only [← Matrix.mul_assoc]
    rw [(mem_orthogonalGroup_iff _ _).1 hF, Matrix.one_mul, Matrix.mul_assoc,
      (mem_orthogonalGroup_iff _ _).1 hG, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · have h14 := equation_10_4_14 A v hF hSVD
    have h15 := equation_10_4_15 A v hk1 hF hG hSVD
    have hw : (Krylov.lastVec (1 : ℝ) k ᵥ* F) i = F ⟨k - 1, by omega⟩ i := by
      simp only [vecMul, dotProduct, Krylov.lastVec]
      rw [Finset.sum_eq_single ⟨k - 1, by omega⟩ (fun l _ hl => by
        rw [ite_eq_right (fun h => hl (Fin.ext (by simp; omega))), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp only [ite_eq_left (show k - 1 + 1 = k by omega), one_mul]
    have hs : ∀ c : ℝ, (Pi.single i c : Fin k → ℝ) = c • Pi.single i (1 : ℝ) := fun c => by
      ext l
      simp [Pi.single_apply]
    simp only [y, p]
    generalize GolubKahan.rightMatrix A v k = V at h14 h15 ⊢
    generalize GolubKahan.leftMatrix A v k = U at h14 h15
    generalize GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (k - 1) •
      (GolubKahan.rightVec (toEuclideanLin A) (toEuclideanLin Aᵀ) v k).ofLp = p' at h15 ⊢
    have hmat : (Aᵀ * A) * (V * G) = (V * G) * diagonal γ * diagonal γ +
        vecMulVec p' (Krylov.lastVec (1 : ℝ) k ᵥ* F) * diagonal γ := by
      rw [Matrix.mul_assoc, h14, ← Matrix.mul_assoc, h15, Matrix.add_mul]
    have t1 : ((V * G) * diagonal γ * diagonal γ) *ᵥ Pi.single i 1 =
        (γ i ^ 2) • ((V * G) *ᵥ Pi.single i 1) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, diagonal_mulVec_single, diagonal_mulVec_single,
        hs, mulVec_smul, sq, mul_one]
    have t2 : (vecMulVec p' (Krylov.lastVec (1 : ℝ) k ᵥ* F) * diagonal γ) *ᵥ Pi.single i 1 =
        (γ i * F ⟨k - 1, by omega⟩ i) • p' := by
      rw [← mulVec_mulVec, diagonal_mulVec_single, vecMulVec_mulVec, dotProduct_single, hw,
        op_smul_eq_smul, mul_one, mul_comm]
    rw [mulVec_mulVec, hmat, add_mulVec, t1, t2]
  · have hsymm : (toEuclideanLin (Aᵀ * A)).IsSymmetric :=
      isSymmetric_toEuclideanLin_iff.mpr (by
        have := isHermitian_conjTranspose_mul_self A
        rwa [conjTranspose_eq_transpose_of_trivial] at this)
    have hy0 : G *ᵥ Pi.single i 1 ≠ 0 := by
      intro h
      have h2 : Gᵀ *ᵥ (G *ᵥ Pi.single i 1) = Pi.single i 1 := by
        rw [mulVec_mulVec, hGG, one_mulVec]
      rw [h, mulVec_zero] at h2
      have h3 := congrFun h2 i
      simp at h3
    have hBB : (Bkᵀ * Bk) * G = G * diagonal (fun j => γ j ^ 2) := by
      rw [hB, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Fᵀ F, (mem_orthogonalGroup_iff' _ _).1 hF, Matrix.one_mul,
        hGG, Matrix.mul_one, diagonal_mul_diagonal]
      congr 2
      funext j
      ring
    have hH : (Arnoldi.hessenbergSq (toEuclideanLin (Aᵀ * A)) v k) *ᵥ (G *ᵥ Pi.single i 1) =
        (γ i ^ 2) • (G *ᵥ Pi.single i 1) := by
      rw [Lanczos.hessenbergSq_eq_map_tridiag v hsymm, ← bidiag_transpose_mul_bidiag A v k]
      simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]
      rw [mulVec_mulVec, hBB, ← mulVec_mulVec, diagonal_mulVec_single]
      ext x
      simp only [mulVec, dotProduct, Pi.single_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      ring
    simp only [y]
    rw [← mulVec_mulVec, GolubKahan.rightMatrix_eq_basisMatrix,
      conjTranspose_eq_transpose_of_trivial, toLp_basisMatrix_mulVec]
    exact Arnoldi.isRitzPair_of_mulVec_eq_smul _ v hk hy0 hH

/-! ### Algorithms 10.4.1 and 10.4.2 -/

/-- The state of the bidiagonalization programs: the number `k` of steps taken, the right and
left vectors (`v j`, `u j` are the book's `v_{j+1}`, `u_{j+1}` in Algorithm 10.4.1), the
coefficients (`alpha j`, `beta j` are `α_{j+1}`, `β_{j+1}`), the vector `p` (the book's `p_k`) and
the `done` flag of the `while β_k ≠ 0` loop. -/
structure BidiagState (m n : ℕ) where
  /-- The book's step counter `k`. -/
  k : ℕ
  /-- The right vectors, `0`-based. -/
  v : ℕ → Fin n → ℝ
  /-- The left vectors, `0`-based. -/
  u : ℕ → Fin m → ℝ
  /-- The diagonal coefficients `α`, `0`-based. -/
  alpha : ℕ → ℝ
  /-- The off-diagonal coefficients `β`, `0`-based. -/
  beta : ℕ → ℝ
  /-- The vector `p_k`. -/
  p : Fin n → ℝ
  /-- Whether the loop has stopped (`β_k = 0`). -/
  done : Bool

section BidiagProgram

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ) {m n : ℕ}

/-- One pass of the `while` loop of Algorithm 10.4.1 for the pair `(B, C)` (`C` playing `Bᵀ`), a
no-op once `done`:
```
v_{k+1} = p_k/β_k,  k = k + 1,  r_k = B v_k − β_{k−1} u_{k−1},  α_k = ‖r_k‖₂,  u_k = r_k/α_k,
p_k = C u_k − α_k v_k,  β_k = ‖p_k‖₂
```
with `β_0 = 1` and `u_0 = 0` at the first pass. For `(B, C) = (A, Aᵀ)` it is Algorithm 10.4.1; for
`(Aᵀ, A)` it is Algorithm 10.4.2 with the roles of `u` and `v` exchanged. -/
noncomputable def bidiagStep (B : Matrix (Fin m) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (s : BidiagState m n) : M (BidiagState m n) :=
  if s.done then pure s else do
    let bk : ℝ := if s.k = 0 then 1 else s.beta (s.k - 1)
    let vk ← vecDiv rnd s.p bk
    let w ← algorithm_1_1_3 rnd B vk 0
    let r ← algorithm_1_1_2 rnd (-bk) (if s.k = 0 then 0 else s.u (s.k - 1)) w
    let a ← vecNorm rnd r
    let uk ← vecDiv rnd r a
    let z ← algorithm_1_1_3 rnd C uk 0
    let p ← algorithm_1_1_2 rnd (-a) vk z
    let b ← vecNorm rnd p
    pure
      { k := s.k + 1
        v := Function.update s.v s.k vk
        u := Function.update s.u s.k uk
        alpha := Function.update s.alpha s.k a
        beta := Function.update s.beta s.k b
        p := p
        done := decide (b = 0) }

/-- The bidiagonalization loop for the pair `(B, C)` from `v₀`: at most `fuel` passes of
`bidiagStep`. -/
noncomputable def bidiagLoop (B : Matrix (Fin m) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ)
    (v₀ : Fin n → ℝ) (fuel : ℕ) : M (BidiagState m n) :=
  (List.range fuel).foldlM (fun s _ => bidiagStep rnd B C s)
    { k := 0, v := fun _ => 0, u := fun _ => 0, alpha := fun _ => 0, beta := fun _ => 0,
      p := v₀, done := false }

/-- **Algorithm 10.4.1 (Golub–Kahan Bidiagonalization).** "Given a matrix `A ∈ ℝ^{m×n}` with full
column rank and a unit 2-norm `v_c ∈ ℝⁿ`, the following algorithm computes the factorization
`AV = UB`":
```
k = 0, p_0 = v_c, β_0 = 1, u_0 = 0
while β_k ≠ 0
  v_{k+1} = p_k/β_k,  k = k + 1
  r_k = A v_k − β_{k−1} u_{k−1},  α_k = ‖r_k‖₂,  u_k = r_k/α_k
  p_k = Aᵀ u_k − α_k v_k,  β_k = ‖p_k‖₂
end
```
The `while` loop is at most `fuel` passes (convention 3). -/
noncomputable def algorithm_10_4_1 (A : Matrix (Fin m) (Fin n) ℝ) (vc : Fin n → ℝ) (fuel : ℕ) :
    M (BidiagState m n) :=
  bidiagLoop rnd A Aᵀ vc fuel

/-- **Algorithm 10.4.2 (Paige–Saunders Lower Bidiagonalization).** "Given a matrix `A ∈ ℝ^{m×n}`
with the property that `A(1:n, 1:n)` is nonsingular and a unit 2-norm `u_c ∈ ℝ^m` (the book prints
`ℝⁿ`), the following algorithm computes the factorization `AV(:, 1:k) = U(:, 1:k+1) B(1:k+1, 1:k)`":
```
k = 1, p_0 = u_c, β_1 = 1, v_0 = 0
while β_k > 0
  u_k = p_{k−1}/β_k,  r_k = Aᵀ u_k − β_k v_{k−1},  α_k = ‖r_k‖₂,  v_k = r_k/α_k
  p_k = A v_k − α_k u_k,  β_{k+1} = ‖p_k‖₂,  k = k + 1
end
```
It is the loop of Algorithm 10.4.1 for the pair `(Aᵀ, A)`: the state's right vectors (`v`) are the
book's `u_k` and its left vectors (`u`) the book's `v_k`. -/
noncomputable def algorithm_10_4_2 (A : Matrix (Fin m) (Fin n) ℝ) (uc : Fin m → ℝ) (fuel : ℕ) :
    M (BidiagState n m) :=
  bidiagLoop rnd Aᵀ A uc fuel

end BidiagProgram

/-- `‖c • x‖ = c` for `c ≥ 0` and `x` a unit vector or `x = 0` with `c = 0`. -/
private theorem norm_smul_of_unit_or {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c : ℝ} (hc : 0 ≤ c) {x : E} (hx : x ≠ 0 → ‖x‖ = 1) (h0 : x = 0 → c = 0) :
    ‖c • x‖ = c := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  rcases eq_or_ne x 0 with h | h
  · rw [h0 h, zero_mul]
  · rw [hx h, mul_one]

/-- The exact run after `t + 1` passes is one more pass. -/
private theorem bidiagLoop_succ {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (v₀ : Fin n → ℝ) (t : ℕ) :
    Id.run (bidiagLoop pure B C v₀ (t + 1)) =
      Id.run (bidiagStep pure B C (Id.run (bidiagLoop pure B C v₀ t))) := by
  simp only [bidiagLoop, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- Exact semantics of the bidiagonalization loop, for `C = Bᵀ` and a unit `v₀`: the run stops
after `min fuel m` passes (`m` the grade of `v₀` for `BᵀB`) and every computed quantity is the
backbone's Golub–Kahan one. -/
theorem bidiagLoop_spec {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) {v₀ : Fin n → ℝ}
    (hv : ‖(WithLp.toLp 2 v₀ : EuclideanSpace ℝ (Fin n))‖ = 1) (fuel : ℕ) :
    let s := Id.run (bidiagLoop pure B Bᵀ v₀ fuel)
    let T := Matrix.toEuclideanLin B
    let Ts := Matrix.toEuclideanLin Bᵀ
    let q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v₀
    s.k = min fuel (grade (Ts ∘ₗ T) q) ∧
      ∀ j < s.k, s.v j = (GolubKahan.rightVec T Ts q j).ofLp ∧
        s.u j = (GolubKahan.leftVec T Ts q j).ofLp ∧ s.alpha j = GolubKahan.alpha T Ts q j ∧
        s.beta j = GolubKahan.beta T Ts q j := by
  intro s T Ts q
  have hadj : ∀ u x, inner ℝ (Ts u) x = inner ℝ u (T x) := fun u x => by
    have := Matrix.toEuclideanLin_conjTranspose_inner_left B x u
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hTx : ∀ x, (T x).ofLp = B *ᵥ x.ofLp := fun x => rfl
  have hTsx : ∀ x, (Ts x).ofLp = Bᵀ *ᵥ x.ofLp := fun x => rfl
  have hq0 : q ≠ 0 := by
    intro h
    have h1 : ‖q‖ = 1 := hv
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hg : 0 < grade (Ts ∘ₗ T) q := by
    rw [Nat.pos_iff_ne_zero, Ne, grade_eq_zero_iff]
    push Not
    exact ⟨hq0, inferInstance⟩
  have hunit_r : ∀ j, GolubKahan.rightVec T Ts q j ≠ 0 → ‖GolubKahan.rightVec T Ts q j‖ = 1 :=
    fun j h => Arnoldi.norm_vec_eq_one_of_ne_zero _ _ h
  have hunit_l : ∀ j, GolubKahan.leftVec T Ts q j ≠ 0 → ‖GolubKahan.leftVec T Ts q j‖ = 1 :=
    fun j h => Arnoldi.norm_vec_eq_one_of_ne_zero _ _ h
  have halpha0 : ∀ j, GolubKahan.leftVec T Ts q j = 0 → GolubKahan.alpha T Ts q j = 0 :=
    fun j h => by rw [GolubKahan.alpha, h, inner_zero_left, map_zero]
  have hbeta0 : ∀ j, GolubKahan.rightVec T Ts q (j + 1) = 0 → GolubKahan.beta T Ts q j = 0 :=
    fun j h => by rw [GolubKahan.beta, h, inner_zero_left, map_zero]
  let P : ℕ → BidiagState m n → Prop := fun t s =>
    s.k = min t (grade (Ts ∘ₗ T) q) ∧ s.done = decide (grade (Ts ∘ₗ T) q ≤ s.k) ∧
      (∀ j < s.k, s.v j = (GolubKahan.rightVec T Ts q j).ofLp ∧
        s.u j = (GolubKahan.leftVec T Ts q j).ofLp ∧ s.alpha j = GolubKahan.alpha T Ts q j ∧
        s.beta j = GolubKahan.beta T Ts q j) ∧
      s.p = if s.k = 0 then v₀ else
        (GolubKahan.beta T Ts q (s.k - 1) • GolubKahan.rightVec T Ts q s.k).ofLp
  have hP : ∀ t, P t (Id.run (bidiagLoop pure B Bᵀ v₀ t)) := by
    intro t
    induction t with
    | zero =>
      refine ⟨by simp [bidiagLoop], ?_, fun j hj => ?_, by simp [bidiagLoop]⟩
      · simp [bidiagLoop, hg.ne']
      · simp [bidiagLoop] at hj
    | succ t ih =>
      rw [bidiagLoop_succ]
      set s := Id.run (bidiagLoop pure B Bᵀ v₀ t)
      obtain ⟨hk, hdone, hvec, hp⟩ := ih
      cases hsd : s.done with
      | true =>
        have hle : grade (Ts ∘ₗ T) q ≤ s.k := by simpa [hsd] using hdone.symm
        simp only [bidiagStep, hsd, ↓reduceIte, Id.run_pure]
        refine ⟨?_, hdone, hvec, hp⟩
        rw [hk] at hle ⊢
        omega
      | false =>
        have hlt : s.k < grade (Ts ∘ₗ T) q := by
          have : ¬ grade (Ts ∘ₗ T) q ≤ s.k := by simpa [hsd] using hdone.symm
          omega
        have hvk_ne : GolubKahan.rightVec T Ts q s.k ≠ 0 := by
          rw [GolubKahan.rightVec, Ne, Arnoldi.vec_eq_zero_iff]
          omega
        -- the new right vector
        have hvk : (if s.k = 0 then 1 else s.beta (s.k - 1))⁻¹ • s.p =
            (GolubKahan.rightVec T Ts q s.k).ofLp := by
          rcases Nat.eq_zero_or_pos s.k with h0 | hpos
          · simp only [hp, h0, ↓reduceIte, inv_one, one_smul]
            rw [GolubKahan.rightVec, Arnoldi.vec_zero _ q hq0, show ‖q‖ = 1 from hv]
            simp [q]
          · obtain ⟨j, hj⟩ : ∃ j, s.k = j + 1 := ⟨s.k - 1, by omega⟩
            simp only [hp, hj, add_eq_zero, one_ne_zero, and_false, ↓reduceIte,
              Nat.add_sub_cancel]
            rw [(hvec j (by omega)).2.2.2]
            have hb : GolubKahan.beta T Ts q j ≠ 0 := by
              intro h
              apply hvk_ne
              rw [hj]
              exact GolubKahan.rightVec_eq_zero_of_beta_eq_zero _ _ _ h
            rw [WithLp.ofLp_smul, smul_smul, inv_mul_cancel₀ hb, one_smul]
        -- `r_k = B v_k − β_{k−1} u_{k−1} = α_k u_k`
        have hr : B *ᵥ (GolubKahan.rightVec T Ts q s.k).ofLp +
              (-(if s.k = 0 then 1 else s.beta (s.k - 1))) •
                (if s.k = 0 then 0 else s.u (s.k - 1)) =
            (GolubKahan.alpha T Ts q s.k • GolubKahan.leftVec T Ts q s.k).ofLp := by
          rcases Nat.eq_zero_or_pos s.k with h0 | hpos
          · simp only [h0, ↓reduceIte, smul_zero, add_zero]
            rw [← hTx, GolubKahan.apply_rightVec_zero]
            rfl
          · obtain ⟨j, hj⟩ : ∃ j, s.k = j + 1 := ⟨s.k - 1, by omega⟩
            simp only [hj, add_eq_zero, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
            rw [(hvec j (by omega)).2.1, (hvec j (by omega)).2.2.2, ← hTx,
              GolubKahan.apply_rightVec q hadj j]
            simp only [WithLp.ofLp_add, WithLp.ofLp_smul, RCLike.ofReal_real_eq_id, id]
            module
        have ha : ‖(WithLp.toLp 2 ((GolubKahan.alpha T Ts q s.k •
            GolubKahan.leftVec T Ts q s.k).ofLp) : EuclideanSpace ℝ (Fin m))‖ =
            GolubKahan.alpha T Ts q s.k := by
          rw [WithLp.toLp_ofLp]
          exact norm_smul_of_unit_or (GolubKahan.alpha_nonneg _ _ _ _) (hunit_l s.k)
            (halpha0 s.k)
        have huk : (GolubKahan.alpha T Ts q s.k)⁻¹ •
            (GolubKahan.alpha T Ts q s.k • GolubKahan.leftVec T Ts q s.k).ofLp =
            (GolubKahan.leftVec T Ts q s.k).ofLp := by
          by_cases h0 : GolubKahan.alpha T Ts q s.k = 0
          · rw [GolubKahan.leftVec_eq_zero_of_alpha_eq_zero _ _ _ h0]
            simp
          · rw [WithLp.ofLp_smul, smul_smul, inv_mul_cancel₀ h0, one_smul]
        -- `p_k = Bᵀ u_k − α_k v_k = β_k v_{k+1}`
        have hpk : Bᵀ *ᵥ (GolubKahan.leftVec T Ts q s.k).ofLp +
              (-GolubKahan.alpha T Ts q s.k) • (GolubKahan.rightVec T Ts q s.k).ofLp =
            (GolubKahan.beta T Ts q s.k • GolubKahan.rightVec T Ts q (s.k + 1)).ofLp := by
          rw [← hTsx, GolubKahan.adjoint_apply_leftVec q hadj s.k]
          simp only [WithLp.ofLp_add, WithLp.ofLp_smul, RCLike.ofReal_real_eq_id, id]
          module
        have hb : ‖(WithLp.toLp 2 ((GolubKahan.beta T Ts q s.k •
            GolubKahan.rightVec T Ts q (s.k + 1)).ofLp) : EuclideanSpace ℝ (Fin n))‖ =
            GolubKahan.beta T Ts q s.k := by
          rw [WithLp.toLp_ofLp]
          exact norm_smul_of_unit_or (GolubKahan.beta_nonneg _ _ _ _) (hunit_r (s.k + 1))
            (hbeta0 s.k)
        simp only [P, bidiagStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
          Id.run_pure, vecDiv_spec, algorithm_1_1_3_spec, algorithm_1_1_2_spec, vecNorm_spec,
          zero_add]
        rw [hvk, hr, ha, huk, hpk, hb]
        refine ⟨by omega, ?_, fun j hj => ?_, by simp⟩
        · have hiff : GolubKahan.beta T Ts q s.k = 0 ↔ grade (Ts ∘ₗ T) q ≤ s.k + 1 := by
            rw [← Arnoldi.vec_eq_zero_iff]
            exact ⟨GolubKahan.rightVec_eq_zero_of_beta_eq_zero _ _ _, hbeta0 s.k⟩
          simp only [hiff]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · simp only [Function.update_of_ne hj.ne]
            exact hvec j hj
          · simp
  obtain ⟨hk, -, hvec, -⟩ := hP fuel
  exact ⟨hk, hvec⟩

/-- **Exact semantics of Algorithm 10.4.1.** For a unit `v_c` the exact run stops after
`min fuel m` passes, `m = grade(AᵀA, v_c)`, and for `j` below that `v_{j+1}`, `u_{j+1}`, `α_{j+1}`,
`β_{j+1}` are the backbone's `GolubKahan.rightVec/leftVec/alpha/beta … j` (so each `α_j`, `β_j` is
a nonnegative norm, `GolubKahan.alpha_nonneg`). The book's full-column-rank hypothesis is not
needed for this identification; under it (`ker A = 0`) every computed `α_j` is positive, so the
loop never divides by zero (the grades of `AᵀA` from `v_c` and of `AAᵀ` from `A v_c` agree,
`GolubKahan.grade_comp_adjoint_add_finrank`). Invariant induction with `GolubKahan.apply_rightVec`,
`GolubKahan.adjoint_apply_leftVec`. -/
theorem algorithm_10_4_1_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {vc : Fin n → ℝ}
    (hv : ‖(WithLp.toLp 2 vc : EuclideanSpace ℝ (Fin n))‖ = 1) (fuel : ℕ) :
    let s := Id.run (algorithm_10_4_1 pure A vc fuel)
    let T := Matrix.toEuclideanLin A
    let Ts := Matrix.toEuclideanLin Aᵀ
    let q : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 vc
    s.k = min fuel (grade (Ts ∘ₗ T) q) ∧
      ∀ j < s.k, s.v j = (GolubKahan.rightVec T Ts q j).ofLp ∧
        s.u j = (GolubKahan.leftVec T Ts q j).ofLp ∧ s.alpha j = GolubKahan.alpha T Ts q j ∧
        s.beta j = GolubKahan.beta T Ts q j ∧
        (LinearMap.ker T = ⊥ → 0 < s.alpha j) := by
  intro s T Ts q
  obtain ⟨hk, hvec⟩ := bidiagLoop_spec A hv fuel
  refine ⟨hk, fun j hj => ⟨(hvec j hj).1, (hvec j hj).2.1, (hvec j hj).2.2.1, (hvec j hj).2.2.2,
    fun hker => ?_⟩⟩
  have hgr := GolubKahan.grade_comp_adjoint_add_finrank T Ts q
  rw [hker, inf_bot_eq, finrank_bot, add_zero] at hgr
  have hne : GolubKahan.leftVec T Ts q j ≠ 0 := by
    rw [GolubKahan.leftVec, Ne, Arnoldi.vec_eq_zero_iff, hgr]
    have : s.k = min fuel (grade (Ts ∘ₗ T) q) := hk
    omega
  have hα : GolubKahan.alpha T Ts q j ≠ 0 := fun h =>
    hne (GolubKahan.leftVec_eq_zero_of_alpha_eq_zero _ _ _ h)
  have hsα : s.alpha j = GolubKahan.alpha T Ts q j := (hvec j hj).2.2.1
  rw [hsα]
  exact lt_of_le_of_ne (GolubKahan.alpha_nonneg _ _ _ _) (Ne.symm hα)

/-- **Exact semantics of Algorithm 10.4.2**: it is Algorithm 10.4.1 for `Aᵀ` started from `u_c`,
the Golub–Kahan process of the pair `(Aᵀ, A)`: the book's `u_j`, `v_j`, `α_j`, `β_{j+1}` are
`GolubKahan.rightVec/leftVec/alpha/beta (toEuclideanLin Aᵀ) (toEuclideanLin A) u_c (j − 1)`, for `j`
up to the stopping index `min fuel (grade (A Aᵀ) u_c)`. The book's hypothesis "`A(1:n, 1:n)`
nonsingular" is not what the algorithm needs (full column rank is); the identification needs
neither. -/
theorem algorithm_10_4_2_spec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {uc : Fin m → ℝ}
    (hu : ‖(WithLp.toLp 2 uc : EuclideanSpace ℝ (Fin m))‖ = 1) (fuel : ℕ) :
    let s := Id.run (algorithm_10_4_2 pure A uc fuel)
    let T := Matrix.toEuclideanLin Aᵀ
    let Ts := Matrix.toEuclideanLin A
    let q : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 uc
    s.k = min fuel (grade (Ts ∘ₗ T) q) ∧
      ∀ j < s.k, s.v j = (GolubKahan.rightVec T Ts q j).ofLp ∧
        s.u j = (GolubKahan.leftVec T Ts q j).ofLp ∧ s.alpha j = GolubKahan.alpha T Ts q j ∧
        s.beta j = GolubKahan.beta T Ts q j := by
  have h := bidiagLoop_spec Aᵀ hu fuel
  rwa [transpose_transpose] at h

/-! ### The tridiagonal–bidiagonal connection (§10.4.3) -/

/-- Two operators whose Arnoldi coefficients agree have the same Lanczos matrices. -/
private theorem tridiag_eq_of_coeff_eq {E E' : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] {T : E →ₗ[ℝ] E}
    {T' : E' →ₗ[ℝ] E'} {b : E} {b' : E'} (h : Arnoldi.coeff T' b' = Arnoldi.coeff T b) (k : ℕ) :
    Lanczos.tridiag T' b' k = Lanczos.tridiag T b k := by
  have ha : ∀ j, Lanczos.alpha T' b' j = Lanczos.alpha T b j := fun j => by
    rw [Lanczos.alpha, Lanczos.alpha, h]
  have hb : ∀ j, Lanczos.beta T' b' j = Lanczos.beta T b j := fun j => by
    have h1 := Lanczos.coe_beta T' b' j
    have h2 := Lanczos.coe_beta T b j
    rw [h] at h1
    simpa using h1.trans h2.symm
  ext i j
  simp only [Lanczos.tridiag_apply, ha, hb]

/-- **The tridiagonal–bidiagonal connection** (§10.4.3 with (10.4.16)–(10.4.17)): the Lanczos
process of the Jordan–Wielandt matrix of `A`, started from the vector with `v_c` in the `ℝⁿ` block,
has zero diagonal and off-diagonal `α_1, β_1, α_2, β_2, …` (the Golub–Kahan coefficients): its
`k`-th Lanczos matrix `T_k` is `[0 α_1; α_1 0 β_1; …]`. The book's `C = [0 A; Aᵀ 0]` acts on
`ℝ^{m+n}` from `[0; v_c]`; here the two blocks are exchanged, `C = [0 Aᵀ; A 0]` on `ℝ^{n+m}` from
`[v_c; 0]` (the same operator up to the permutation of the blocks, and the same Lanczos
coefficients), which is the backbone's Hermitian dilation `LinearMap.hermitianDilation` read in
coordinates. Backbone `GolubKahan.lanczos_jordanWielandt`, carried to coordinates by
`Arnoldi.coeff_conj_linearIsometryEquiv` along `PiLp.sumPiLpEquivProdLpPiLp`. -/
theorem lanczos_jordanWielandt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Lanczos.tridiag (toEuclideanLin (Matrix.fromBlocks 0 Aᵀ A 0))
        (WithLp.toLp 2 (Sum.elim v.ofLp 0)) k =
      Matrix.of fun i j : Fin k =>
        if (i : ℕ) + 1 = j then
          (if (i : ℕ) % 2 = 0 then GolubKahan.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) v (i / 2)
            else GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (i / 2))
        else if (j : ℕ) + 1 = i then
          (if (j : ℕ) % 2 = 0 then GolubKahan.alpha (toEuclideanLin A) (toEuclideanLin Aᵀ) v (j / 2)
            else GolubKahan.beta (toEuclideanLin A) (toEuclideanLin Aᵀ) v (j / 2))
        else 0 := by
  have hadj : ∀ u x, inner ℝ (toEuclideanLin Aᵀ u) x = inner ℝ u (toEuclideanLin A x) :=
    fun u x => by
      have := Matrix.toEuclideanLin_conjTranspose_inner_left A x u
      rwa [conjTranspose_eq_transpose_of_trivial] at this
  set e := (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : Fin n ⊕ Fin m => ℝ)).symm with he
  set D := LinearMap.hermitianDilation (toEuclideanLin A) (toEuclideanLin Aᵀ) with hD
  have hconj : e.toLinearEquiv.conj D = toEuclideanLin (Matrix.fromBlocks 0 Aᵀ A 0) := by
    refine LinearMap.ext fun z => ?_
    ext (i | i) <;>
      simp [e, D, LinearEquiv.conj_apply, Matrix.fromBlocks_mulVec, Matrix.toEuclideanLin_apply,
        LinearMap.hermitianDilation_apply] <;> rfl
  have hb : e (WithLp.toLp 2 (v, 0)) = WithLp.toLp 2 (Sum.elim v.ofLp 0) := by
    ext (i | i) <;> simp [e]
  rw [← hconj, ← hb, tridiag_eq_of_coeff_eq (Arnoldi.coeff_conj_linearIsometryEquiv _ _ _),
    GolubKahan.lanczos_jordanWielandt v hadj]

end GolubVanLoan.Chapter10
