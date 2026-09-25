/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Tensor.MultilinearProduct

/-!
# The higher-order SVD

The higher-order singular value decomposition ([golub2013matrix] §12.5.1–12.5.2, Theorem 12.5.1;
De Lathauwer–De Moor–Vandewalle 2000) of a tensor `A` over `𝕜` (`RCLike`; the real book reads `ᴴ`
as `ᵀ`), with the multilinear rank and the truncated HOSVD.

**Canonical factors.** The mode-`k` factor `Tensor.hosvdFactor A k` is the right singular unitary
of `(A.modeUnfold k)ᴴ` (`Matrix.rightSingularUnitary`): its columns are an orthonormal eigenbasis of
`A_(k) A_(k)ᴴ`, i.e. left singular vectors of the unfolding `A_(k)`, paired index by index with the
singular values `((A.modeUnfold k)ᴴ).singularValues`, which are indexed by `κ k` in no particular
order. The core is `Tensor.hosvdCore A = A ×₁ U₁ᴴ ⋯ ×_d U_dᴴ`, and the HOSVD is a theorem about
these definitions rather than an existence statement; the book's sorted version is the surface's.

**The truncation bound** ([golub2013matrix] (12.5.11)) is misprinted in the book with `min_k`,
which is false (a tensor truncated in one mode only has `min_k = 0` and a nonzero error); the bound
proved here, `Tensor.norm_sub_truncatedHOSVD_sq_le`, has `∑_k`.

## Main definitions

* `Tensor.multilinearRank A k`: the rank of the mode-`k` unfolding.
* `Tensor.hosvdFactor`, `Tensor.hosvdCore`: the factors and the core of the HOSVD.
* `Tensor.truncatedHOSVD A s`: the HOSVD truncated to the singular directions `s k` in each mode.

## Main statements

* `Tensor.multilinearProd_hosvdFactor_hosvdCore`: [golub2013matrix] Theorem 12.5.1.
* `Tensor.modeUnfold_hosvdCore_row`: all-orthogonality (12.5.10).
* `Tensor.norm_sub_truncatedHOSVD_sq_le`: the truncation error, (12.5.11) corrected.

## References

* [golub2013matrix], §12.5.1–12.5.2.
-/

universe u v

open Matrix

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]

/-- The multilinear rank ([golub2013matrix] §12.5.2, `rank_*(𝒜)`): the vector of the ranks of the
modal unfoldings. -/
noncomputable def multilinearRank {R : Type*} [CommRing R] (A : Tensor κ R) (k : ι) : ℕ :=
  (A.modeUnfold k).rank

variable {𝕜 : Type*} [RCLike 𝕜] [∀ i, DecidableEq (κ i)]

/-! ### The factors and the core -/

/-- The mode-`k` factor of the HOSVD: a unitary matrix whose columns are left singular vectors of
the mode-`k` unfolding, paired with the singular values `((A.modeUnfold k)ᴴ).singularValues`. -/
noncomputable def hosvdFactor (A : Tensor κ 𝕜) (k : ι) : Matrix (κ k) (κ k) 𝕜 :=
  (A.modeUnfold k)ᴴ.rightSingularUnitary

/-- The core tensor of the HOSVD ([golub2013matrix] (12.5.6)): `𝒮 = 𝒜 ×₁ U₁ᴴ ⋯ ×_d U_dᴴ`. -/
noncomputable def hosvdCore (A : Tensor κ 𝕜) : Tensor κ 𝕜 :=
  multilinearProd (fun k => (hosvdFactor A k)ᴴ) A

variable (A : Tensor κ 𝕜)

/-- The HOSVD factors are unitary. -/
theorem hosvdFactor_mem_unitaryGroup (k : ι) : hosvdFactor A k ∈ unitaryGroup (κ k) 𝕜 :=
  rightSingularUnitary_mem_unitaryGroup _

theorem conjTranspose_hosvdFactor_mul_hosvdFactor (k : ι) :
    (hosvdFactor A k)ᴴ * hosvdFactor A k = 1 := by
  rw [← star_eq_conjTranspose]
  exact star_mul_rightSingularUnitary _

theorem hosvdFactor_mul_conjTranspose_hosvdFactor (k : ι) :
    hosvdFactor A k * (hosvdFactor A k)ᴴ = 1 := by
  rw [← star_eq_conjTranspose]
  exact rightSingularUnitary_mul_star _

/-- **The HOSVD** ([golub2013matrix] Theorem 12.5.1, (12.5.6)): `𝒜 = 𝒮 ×₁ U₁ ⋯ ×_d U_d`. -/
theorem multilinearProd_hosvdFactor_hosvdCore :
    multilinearProd (hosvdFactor A) (hosvdCore A) = A := by
  rw [hosvdCore, multilinearProd_multilinearProd]
  simp_rw [hosvdFactor_mul_conjTranspose_hosvdFactor, multilinearProd_one]

/-- The HOSVD as a sum of rank-one tensors ([golub2013matrix] (12.5.7)). -/
theorem hosvd_eq_sum_rankOne :
    A = ∑ j, hosvdCore A j • rankOne fun k i => hosvdFactor A k i (j k) := by
  conv_lhs => rw [← multilinearProd_hosvdFactor_hosvdCore A]
  exact multilinearProd_eq_sum_rankOne _ _

/-! ### All-orthogonality -/

/-- The Gram matrix of `U_kᴴ A_(k)` is the diagonal of the squared singular values of `A_(k)`. -/
theorem conjTranspose_hosvdFactor_mul_modeUnfold_mul_conjTranspose (k : ι) :
    (hosvdFactor A k)ᴴ * A.modeUnfold k * ((hosvdFactor A k)ᴴ * A.modeUnfold k)ᴴ
      = diagonal fun i => ((((A.modeUnfold k)ᴴ.singularValues i) ^ 2 : ℝ) : 𝕜) := by
  have h := conjTranspose_mul_self_eq_conj_diagonal (A.modeUnfold k)ᴴ
  rw [conjTranspose_conjTranspose] at h
  rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc
    (A.modeUnfold k), h, hosvdFactor, star_eq_conjTranspose]
  simp only [← Matrix.mul_assoc]
  rw [← star_eq_conjTranspose, star_mul_rightSingularUnitary, Matrix.one_mul, Matrix.mul_assoc,
    star_mul_rightSingularUnitary, Matrix.mul_one]

/-- The Kronecker product of the conjugate-transposed HOSVD factors of the other modes, transposed,
is a unitary: `W Wᴴ = 1`. -/
private theorem transpose_piKronecker_mul_conjTranspose (k : ι) :
    (piKronecker fun j : {j // j ≠ k} => (hosvdFactor A j)ᴴ)ᵀ
        * ((piKronecker fun j : {j // j ≠ k} => (hosvdFactor A j)ᴴ)ᵀ)ᴴ = 1 := by
  set P := piKronecker fun j : {j // j ≠ k} => (hosvdFactor A j)ᴴ
  have hP : Pᴴ * P = 1 := conjTranspose_piKronecker_mul_piKronecker fun j => by
    rw [conjTranspose_conjTranspose]
    exact hosvdFactor_mul_conjTranspose_hosvdFactor A j
  have hT : (Pᵀ)ᴴ = (Pᴴ)ᵀ := by
    ext
    simp
  rw [hT, ← transpose_mul, hP, transpose_one]

/-- [golub2013matrix] (12.5.10), **all-orthogonality**: the rows of the mode-`k` unfolding of the
core are pairwise orthogonal, with Euclidean norms the singular values of `A_(k)`. -/
theorem modeUnfold_hosvdCore_row (k : ι) :
    (hosvdCore A).modeUnfold k * ((hosvdCore A).modeUnfold k)ᴴ
      = diagonal fun i => ((((A.modeUnfold k)ᴴ.singularValues i) ^ 2 : ℝ) : 𝕜) := by
  rw [hosvdCore, modeUnfold_multilinearProd, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ (((hosvdFactor A k)ᴴ * A.modeUnfold k)ᴴ),
    transpose_piKronecker_mul_conjTranspose, Matrix.one_mul,
    conjTranspose_hosvdFactor_mul_modeUnfold_mul_conjTranspose]

/-- The rows of the core's mode-`k` unfolding have Euclidean norms the singular values of
`A_(k)`. -/
theorem sum_norm_sq_modeUnfold_hosvdCore (k : ι) (i : κ k) :
    ∑ c, ‖(hosvdCore A).modeUnfold k i c‖ ^ 2 = (A.modeUnfold k)ᴴ.singularValues i ^ 2 := by
  have h := congrFun (congrFun (modeUnfold_hosvdCore_row A k) i) i
  rw [mul_apply, diagonal_apply_eq] at h
  simp only [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj] at h
  exact_mod_cast h

/-- The single-mode statement of [golub2013matrix] §12.5.1: `ℬ⁽ᵏ⁾ = 𝒜 ×_k U_kᴴ` (the book prints
`×_k U_k`) has `ℬ⁽ᵏ⁾_(k) ℬ⁽ᵏ⁾_(k)ᴴ = Σ_k²`: its mode-`k` slices are orthogonal, with Frobenius norms
the singular values of `A_(k)`. -/
theorem modeProd_hosvdFactor_row (k : ι) :
    (A.modeProd k (hosvdFactor A k)ᴴ).modeUnfold k
        * ((A.modeProd k (hosvdFactor A k)ᴴ).modeUnfold k)ᴴ
      = diagonal fun i => ((((A.modeUnfold k)ᴴ.singularValues i) ^ 2 : ℝ) : 𝕜) := by
  rw [modeUnfold_modeProd, conjTranspose_hosvdFactor_mul_modeUnfold_mul_conjTranspose]

/-! ### Truncation -/

/-- The truncated HOSVD ([golub2013matrix] §12.5.2, `𝒜^{(r)}`): the multilinear product by the
orthogonal projections onto the kept left singular vectors `s k` of each mode. -/
noncomputable def truncatedHOSVD (s : ∀ k, Finset (κ k)) : Tensor κ 𝕜 :=
  multilinearProd (fun k => hosvdFactor A k * diagonal (fun i => if i ∈ s k then 1 else 0)
    * (hosvdFactor A k)ᴴ) A

/-- The truncated HOSVD is the multilinear product of the factors with the core restricted to the
kept indices. -/
theorem truncatedHOSVD_eq_multilinearProd (s : ∀ k, Finset (κ k)) :
    truncatedHOSVD A s = multilinearProd (hosvdFactor A)
      (of fun j => if j ∈ Fintype.piFinset s then hosvdCore A j else 0) := by
  have h : (fun k => hosvdFactor A k * diagonal (fun i => if i ∈ s k then (1 : 𝕜) else 0)
      * (hosvdFactor A k)ᴴ) = fun k => hosvdFactor A k
        * (diagonal (fun i => if i ∈ s k then (1 : 𝕜) else 0) * (hosvdFactor A k)ᴴ) :=
    funext fun k => Matrix.mul_assoc _ _ _
  rw [truncatedHOSVD, h, ← multilinearProd_multilinearProd, ← multilinearProd_multilinearProd,
    ← hosvdCore, multilinearProd_diagonal]
  congr 1
  ext j
  simp only [of_apply, Finset.prod_boole, Fintype.mem_piFinset, ite_mul, one_mul, zero_mul,
    Finset.mem_univ, true_implies]

/-- [golub2013matrix] §12.5.2: `𝒜^{(r)} = ∑_{j ∈ ∏ s} 𝒮(j) U₁(:, j₁) ∘ ⋯ ∘ U_d(:, j_d)`. -/
theorem truncatedHOSVD_eq_sum (s : ∀ k, Finset (κ k)) :
    truncatedHOSVD A s
      = ∑ j ∈ Fintype.piFinset s, hosvdCore A j • rankOne fun k i => hosvdFactor A k i (j k) := by
  rw [truncatedHOSVD_eq_multilinearProd, multilinearProd_eq_sum_rankOne,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Fintype.piFinset s)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter (· ∉ Fintype.piFinset s)) fun j hj => by
    rw [of_apply, ite_eq_right (Finset.mem_filter.1 hj).2, zero_smul], add_zero,
    Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact Finset.sum_congr rfl fun j hj => by rw [of_apply, ite_eq_left hj]

/-- **The truncation error of the HOSVD** ([golub2013matrix] (12.5.11), corrected: the book prints
`min_k` where `∑_k` is meant): `‖𝒜 − 𝒜^{(r)}‖² ≤ ∑_k ∑_{i ∉ s_k} σ_i(A_(k))²`. -/
theorem norm_sub_truncatedHOSVD_sq_le (s : ∀ k, Finset (κ k)) :
    ‖A - truncatedHOSVD A s‖ ^ 2
      ≤ ∑ k, ∑ i ∈ (s k)ᶜ, (A.modeUnfold k)ᴴ.singularValues i ^ 2 := by
  have hA : A - truncatedHOSVD A s = multilinearProd (hosvdFactor A)
      (of fun j => if j ∈ Fintype.piFinset s then 0 else hosvdCore A j) := by
    have h1 : A - truncatedHOSVD A s = multilinearProd (hosvdFactor A) (hosvdCore A)
        - multilinearProd (hosvdFactor A)
          (of fun j => if j ∈ Fintype.piFinset s then hosvdCore A j else 0) := by
      rw [truncatedHOSVD_eq_multilinearProd, multilinearProd_hosvdFactor_hosvdCore]
    rw [h1, ← multilinearProd_sub]
    congr 1
    ext j
    simp only [sub_apply, of_apply]
    split_ifs <;> simp
  rw [hA, frobenius_norm_multilinearProd_of_orthonormal
    (conjTranspose_hosvdFactor_mul_hosvdFactor A), frobenius_norm_sq]
  -- every excluded index is excluded in some mode
  have hle : ∀ j : ∀ k, κ k, ‖(of fun j => if j ∈ Fintype.piFinset s then 0 else hosvdCore A j :
      Tensor κ 𝕜) j‖ ^ 2 ≤ ∑ k, if j k ∈ s k then 0 else ‖hosvdCore A j‖ ^ 2 := by
    intro j
    rw [of_apply]
    split_ifs with hj
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
    · obtain ⟨k, hk⟩ : ∃ k, j k ∉ s k := by simpa [Fintype.mem_piFinset] using hj
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun k => if j k ∈ s k then 0 else ‖hosvdCore A j‖ ^ 2)
        (fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ k))
      simp [hk]
  refine (Finset.sum_le_sum fun j _ => hle j).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← (Equiv.piSplitAt k κ).symm.sum_comp, Fintype.sum_prod_type]
  have hx : ∀ (x : κ k) (y : ∀ j : {j // j ≠ k}, κ j), (Equiv.piSplitAt k κ).symm (x, y) k = x :=
    fun x y => by simp [Equiv.piSplitAt_symm_apply]
  simp only [hx]
  calc _ = ∑ x, if x ∈ (s k)ᶜ then (A.modeUnfold k)ᴴ.singularValues x ^ 2 else 0 :=
        Finset.sum_congr rfl fun x _ => by
          simp only [Finset.mem_compl]
          split_ifs with h
          · simp
          · rw [← sum_norm_sq_modeUnfold_hosvdCore A k x]
            rfl
    _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]

end Tensor
