/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a new `Mathlib.LinearAlgebra.Tensor` directory beside `Mathlib.LinearAlgebra.Matrix`.
The exception is `Numlib/Analysis/Matrix/SingularValues` (the Frobenius Eckart–Young bound behind
the truncation estimate), which is not a candidate and would have to go upstream first; keep it
free of any other dependency on the rest of `Numlib` than other upstreaming candidates.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Tensor.MultilinearProduct

/-!
# The higher-order SVD

The higher-order singular value decomposition ([golub2013matrix] §12.5.1–12.5.2, Theorem 12.5.1;
De Lathauwer–De Moor–Vandewalle 2000) of a tensor `A` over `𝕜` (`RCLike`; the real book reads `ᴴ`
as `ᵀ`), with the multilinear rank and the truncated HOSVD.

**Any SVD factors.** The core `Tensor.hosvdCoreOf U A = A ×₁ U₁ᴴ ⋯ ×_d U_dᴴ` and the truncation
`Tensor.truncatedHOSVDOf U A s` are defined for any unitary family `U`, and the HOSVD
(`Tensor.multilinearProd_hosvdCoreOf`), all-orthogonality
(`Tensor.modeUnfold_hosvdCoreOf_mul_conjTranspose`) and the truncation bound
(`Tensor.norm_sub_truncatedHOSVDOf_sq_le`, for `U_kᴴ 𝒜_(k) 𝒜_(k)ᴴ U_k = diag(σ_k²)`, i.e. the left
factors of any SVDs of the unfoldings, sorted or not) are proved there.

**Canonical factors.** The mode-`k` factor `Tensor.hosvdFactor A k` is the right singular unitary
of `(A.modeUnfold k)ᴴ` (`Matrix.rightSingularUnitary`): its columns are an orthonormal eigenbasis of
`A_(k) A_(k)ᴴ`, i.e. left singular vectors of the unfolding `A_(k)`, paired index by index with the
singular values `((A.modeUnfold k)ᴴ).colSingularValues`, which are indexed by `κ k` in no particular
order. The core is `Tensor.hosvdCore A = A ×₁ U₁ᴴ ⋯ ×_d U_dᴴ`, and the HOSVD is a theorem about
these definitions rather than an existence statement, the case `U = hosvdFactor A` of the above.

**The truncation bound** ([golub2013matrix] (12.5.11)) is misprinted in the book with `min_k`,
which is false (a tensor truncated in one mode only has `min_k = 0` and a nonzero error); the bound
proved here, `Tensor.norm_sub_truncatedHOSVD_sq_le`, has `∑_k`.

## Main definitions

* `Tensor.multilinearRank A k`: the rank of the mode-`k` unfolding.
* `Tensor.hosvdCoreOf`, `Tensor.truncatedHOSVDOf`: the core and the truncation in any unitary
  factors.
* `Tensor.hosvdFactor`, `Tensor.hosvdCore`: the canonical factors and core of the HOSVD.
* `Tensor.truncatedHOSVD A s`: the HOSVD truncated to the singular directions `s k` in each mode.

## Main statements

* `Tensor.multilinearProd_hosvdFactor_hosvdCore`: [golub2013matrix] Theorem 12.5.1.
* `Tensor.modeUnfold_hosvdCore_row`: all-orthogonality (12.5.10).
* `Tensor.norm_sub_truncatedHOSVDOf_sq_le`, `Tensor.norm_sub_truncatedHOSVD_sq_le`: the truncation
  error, (12.5.11) corrected, in any SVD factors and in the canonical ones.
* `Tensor.sum_sq_le_norm_sub_sq_of_multilinearRank_le`: the matching lower bound for every
  approximation of multilinear rank at most `r` (Eckart–Young–Mirsky for each unfolding).

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

/-! ### Cores and truncations in any unitary factors

Everything below the definition of the canonical factors holds for *any* unitary family
`U : ∀ k, Matrix (κ k) (κ k) 𝕜`, in particular for the factors of any SVDs of the unfoldings
([golub2013matrix] Theorem 12.5.1 builds the HOSVD from arbitrary SVDs): the core
`𝒜 ×₁ U₁ᴴ ⋯ ×_d U_dᴴ` recovers `𝒜`, the rows of its mode-`k` unfolding have the Gram matrix
`U_kᴴ 𝒜_(k) 𝒜_(k)ᴴ U_k`, and the truncation bound holds as soon as that Gram matrix is diagonal. -/

section Factors

/-- The core `𝒜 ×₁ U₁ᴴ ⋯ ×_d U_dᴴ` of `𝒜` in the factors `U` ([golub2013matrix] (12.5.6)). -/
noncomputable def hosvdCoreOf (U : ∀ k, Matrix (κ k) (κ k) 𝕜) (A : Tensor κ 𝕜) : Tensor κ 𝕜 :=
  multilinearProd (fun k => (U k)ᴴ) A

/-- The truncation of `𝒜` to the columns `s k` of the factors `U k` ([golub2013matrix] §12.5.2,
`𝒜^{(r)}`): the multilinear product by the orthogonal projections onto the kept columns. -/
noncomputable def truncatedHOSVDOf (U : ∀ k, Matrix (κ k) (κ k) 𝕜) (A : Tensor κ 𝕜)
    (s : ∀ k, Finset (κ k)) : Tensor κ 𝕜 :=
  multilinearProd (fun k => U k * diagonal (fun i => if i ∈ s k then 1 else 0) * (U k)ᴴ) A

variable {U : ∀ k, Matrix (κ k) (κ k) 𝕜} (A : Tensor κ 𝕜)

omit [Fintype ι] [DecidableEq ι] in
private theorem conjTranspose_mul_self_of_mem (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜) (k : ι) :
    (U k)ᴴ * U k = 1 := by
  rw [← star_eq_conjTranspose]
  exact mem_unitaryGroup_iff'.1 (hU k)

omit [Fintype ι] [DecidableEq ι] in
private theorem mul_conjTranspose_self_of_mem (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜) (k : ι) :
    U k * (U k)ᴴ = 1 := by
  rw [← star_eq_conjTranspose]
  exact mem_unitaryGroup_iff.1 (hU k)

/-- **The HOSVD in any unitary factors** ([golub2013matrix] Theorem 12.5.1, (12.5.6)):
`𝒜 = 𝒮 ×₁ U₁ ⋯ ×_d U_d` with `𝒮 = 𝒜 ×₁ U₁ᴴ ⋯ ×_d U_dᴴ`. -/
theorem multilinearProd_hosvdCoreOf (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜) :
    multilinearProd U (hosvdCoreOf U A) = A := by
  rw [hosvdCoreOf, multilinearProd_multilinearProd]
  simp_rw [mul_conjTranspose_self_of_mem hU, multilinearProd_one]

/-- The HOSVD in any unitary factors as a sum of rank-one tensors ([golub2013matrix] (12.5.7)). -/
theorem eq_sum_hosvdCoreOf_smul_rankOne (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜) :
    A = ∑ j, hosvdCoreOf U A j • rankOne fun k i => U k i (j k) := by
  conv_lhs => rw [← multilinearProd_hosvdCoreOf A hU]
  exact multilinearProd_eq_sum_rankOne _ _

/-- The Kronecker product of the conjugate-transposed unitary factors of the other modes,
transposed, is a unitary: `W Wᴴ = 1`. -/
private theorem transpose_piKronecker_mul_conjTranspose (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜)
    (k : ι) :
    (piKronecker fun j : {j // j ≠ k} => (U j)ᴴ)ᵀ
        * ((piKronecker fun j : {j // j ≠ k} => (U j)ᴴ)ᵀ)ᴴ = 1 := by
  set P := piKronecker fun j : {j // j ≠ k} => (U j)ᴴ
  have hP : Pᴴ * P = 1 := conjTranspose_piKronecker_mul_piKronecker fun j => by
    rw [conjTranspose_conjTranspose]
    exact mul_conjTranspose_self_of_mem hU j
  have hT : (Pᵀ)ᴴ = (Pᴴ)ᵀ := by
    ext
    simp
  rw [hT, ← transpose_mul, hP, transpose_one]

/-- **All-orthogonality in any unitary factors** ([golub2013matrix] (12.5.10)): the rows of the
mode-`k` unfolding of the core have the Gram matrix `U_kᴴ 𝒜_(k) (U_kᴴ 𝒜_(k))ᴴ`. -/
theorem modeUnfold_hosvdCoreOf_mul_conjTranspose (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜)
    (k : ι) :
    (hosvdCoreOf U A).modeUnfold k * ((hosvdCoreOf U A).modeUnfold k)ᴴ
      = (U k)ᴴ * A.modeUnfold k * ((U k)ᴴ * A.modeUnfold k)ᴴ := by
  rw [hosvdCoreOf, modeUnfold_multilinearProd, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ (((U k)ᴴ * A.modeUnfold k)ᴴ),
    transpose_piKronecker_mul_conjTranspose hU, Matrix.one_mul]

/-- When `U_kᴴ 𝒜_(k) 𝒜_(k)ᴴ U_k = diag(σ_k²)` — `U_k` the left factor of an SVD of `𝒜_(k)` — the
rows of the core's mode-`k` unfolding have Euclidean norms `σ_k`. -/
theorem sum_norm_sq_modeUnfold_hosvdCoreOf (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜) {k : ι}
    {σ : κ k → ℝ}
    (hσ : (U k)ᴴ * A.modeUnfold k * (A.modeUnfold k)ᴴ * U k = diagonal fun i => ((σ i ^ 2 : ℝ) : 𝕜))
    (i : κ k) :
    ∑ c, ‖(hosvdCoreOf U A).modeUnfold k i c‖ ^ 2 = σ i ^ 2 := by
  have h := congrFun (congrFun (modeUnfold_hosvdCoreOf_mul_conjTranspose A hU k) i) i
  rw [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc, hσ,
    diagonal_apply_eq, mul_apply] at h
  simp only [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj] at h
  exact_mod_cast h

/-- The truncation in the factors `U` is the multilinear product of the factors with the core
restricted to the kept indices. -/
theorem truncatedHOSVDOf_eq_multilinearProd (s : ∀ k, Finset (κ k)) :
    truncatedHOSVDOf U A s = multilinearProd U
      (of fun j => if j ∈ Fintype.piFinset s then hosvdCoreOf U A j else 0) := by
  have h : (fun k => U k * diagonal (fun i => if i ∈ s k then (1 : 𝕜) else 0) * (U k)ᴴ)
      = fun k => U k * (diagonal (fun i => if i ∈ s k then (1 : 𝕜) else 0) * (U k)ᴴ) :=
    funext fun k => Matrix.mul_assoc _ _ _
  rw [truncatedHOSVDOf, h, ← multilinearProd_multilinearProd, ← multilinearProd_multilinearProd,
    ← hosvdCoreOf, multilinearProd_diagonal]
  congr 1
  ext j
  simp only [of_apply, Finset.prod_boole, Fintype.mem_piFinset, ite_mul, one_mul, zero_mul,
    Finset.mem_univ, true_implies]

/-- [golub2013matrix] §12.5.2, in any factors:
`𝒜^{(r)} = ∑_{j ∈ ∏ s} 𝒮(j) U₁(:, j₁) ∘ ⋯ ∘ U_d(:, j_d)`. -/
theorem truncatedHOSVDOf_eq_sum (s : ∀ k, Finset (κ k)) :
    truncatedHOSVDOf U A s
      = ∑ j ∈ Fintype.piFinset s, hosvdCoreOf U A j • rankOne fun k i => U k i (j k) := by
  rw [truncatedHOSVDOf_eq_multilinearProd, multilinearProd_eq_sum_rankOne,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Fintype.piFinset s)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter (· ∉ Fintype.piFinset s)) fun j hj => by
    rw [of_apply, ite_eq_right (Finset.mem_filter.1 hj).2, zero_smul], add_zero,
    Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact Finset.sum_congr rfl fun j hj => by rw [of_apply, ite_eq_left hj]

/-- **The truncation error of the HOSVD, in any SVD factors** ([golub2013matrix] (12.5.11),
corrected: the book prints `min_k` where `∑_k` is meant): if every `U_k` is unitary with
`U_kᴴ 𝒜_(k) 𝒜_(k)ᴴ U_k = diag(σ_k²)` — the left factor of any SVD of `𝒜_(k)`, as in Theorem 12.5.1
— then `‖𝒜 − 𝒜^{(r)}‖² ≤ ∑_k ∑_{i ∉ s_k} σ_k(i)²`. -/
theorem norm_sub_truncatedHOSVDOf_sq_le (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜)
    {σ : ∀ k, κ k → ℝ}
    (hσ : ∀ k, (U k)ᴴ * A.modeUnfold k * (A.modeUnfold k)ᴴ * U k =
      diagonal fun i => ((σ k i ^ 2 : ℝ) : 𝕜))
    (s : ∀ k, Finset (κ k)) :
    ‖A - truncatedHOSVDOf U A s‖ ^ 2 ≤ ∑ k, ∑ i ∈ (s k)ᶜ, σ k i ^ 2 := by
  have hA : A - truncatedHOSVDOf U A s = multilinearProd U
      (of fun j => if j ∈ Fintype.piFinset s then 0 else hosvdCoreOf U A j) := by
    have h1 : A - truncatedHOSVDOf U A s = multilinearProd U (hosvdCoreOf U A)
        - multilinearProd U
          (of fun j => if j ∈ Fintype.piFinset s then hosvdCoreOf U A j else 0) := by
      rw [truncatedHOSVDOf_eq_multilinearProd, multilinearProd_hosvdCoreOf A hU]
    rw [h1, ← multilinearProd_sub]
    congr 1
    ext j
    simp only [sub_apply, of_apply]
    split_ifs <;> simp
  rw [hA, frobenius_norm_multilinearProd_of_orthonormal (conjTranspose_mul_self_of_mem hU),
    frobenius_norm_sq]
  -- every excluded index is excluded in some mode
  have hle : ∀ j : ∀ k, κ k, ‖(of fun j => if j ∈ Fintype.piFinset s then 0 else
      hosvdCoreOf U A j : Tensor κ 𝕜) j‖ ^ 2 ≤
        ∑ k, if j k ∈ s k then 0 else ‖hosvdCoreOf U A j‖ ^ 2 := by
    intro j
    rw [of_apply]
    split_ifs with hj
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
    · obtain ⟨k, hk⟩ : ∃ k, j k ∉ s k := by simpa [Fintype.mem_piFinset] using hj
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun k => if j k ∈ s k then 0 else ‖hosvdCoreOf U A j‖ ^ 2)
        (fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ k))
      simp [hk]
  refine (Finset.sum_le_sum fun j _ => hle j).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← (Equiv.piSplitAt k κ).symm.sum_comp, Fintype.sum_prod_type]
  have hx : ∀ (x : κ k) (y : ∀ j : {j // j ≠ k}, κ j), (Equiv.piSplitAt k κ).symm (x, y) k = x :=
    fun x y => by simp [Equiv.piSplitAt_symm_apply]
  simp only [hx]
  calc _ = ∑ x, if x ∈ (s k)ᶜ then σ k x ^ 2 else 0 :=
        Finset.sum_congr rfl fun x _ => by
          simp only [Finset.mem_compl]
          split_ifs with h
          · simp
          · rw [← sum_norm_sq_modeUnfold_hosvdCoreOf A hU (hσ k) x]
            rfl
    _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]

end Factors

/-! ### The canonical factors -/

/-- The mode-`k` factor of the HOSVD: a unitary matrix whose columns are left singular vectors of
the mode-`k` unfolding, paired with the singular values `((A.modeUnfold k)ᴴ).colSingularValues`. -/
noncomputable def hosvdFactor (A : Tensor κ 𝕜) (k : ι) : Matrix (κ k) (κ k) 𝕜 :=
  (A.modeUnfold k)ᴴ.rightSingularUnitary

/-- The core tensor of the HOSVD ([golub2013matrix] (12.5.6)): `𝒮 = 𝒜 ×₁ U₁ᴴ ⋯ ×_d U_dᴴ`, the
core `Tensor.hosvdCoreOf` in the canonical factors. -/
noncomputable def hosvdCore (A : Tensor κ 𝕜) : Tensor κ 𝕜 :=
  hosvdCoreOf (hosvdFactor A) A

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
    multilinearProd (hosvdFactor A) (hosvdCore A) = A :=
  multilinearProd_hosvdCoreOf A (hosvdFactor_mem_unitaryGroup A)

/-- The HOSVD as a sum of rank-one tensors ([golub2013matrix] (12.5.7)). -/
theorem hosvd_eq_sum_rankOne :
    A = ∑ j, hosvdCore A j • rankOne fun k i => hosvdFactor A k i (j k) :=
  eq_sum_hosvdCoreOf_smul_rankOne A (hosvdFactor_mem_unitaryGroup A)

/-! ### All-orthogonality -/

/-- The Gram matrix of `U_kᴴ A_(k)` is the diagonal of the squared singular values of `A_(k)`. -/
theorem conjTranspose_hosvdFactor_mul_modeUnfold_mul_conjTranspose (k : ι) :
    (hosvdFactor A k)ᴴ * A.modeUnfold k * ((hosvdFactor A k)ᴴ * A.modeUnfold k)ᴴ
      = diagonal fun i => ((((A.modeUnfold k)ᴴ.colSingularValues i) ^ 2 : ℝ) : 𝕜) := by
  have h := conjTranspose_mul_self_eq_conj_diagonal (A.modeUnfold k)ᴴ
  rw [conjTranspose_conjTranspose] at h
  rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc
    (A.modeUnfold k), h, hosvdFactor, star_eq_conjTranspose]
  simp only [← Matrix.mul_assoc]
  rw [← star_eq_conjTranspose, star_mul_rightSingularUnitary, Matrix.one_mul, Matrix.mul_assoc,
    star_mul_rightSingularUnitary, Matrix.mul_one]

/-- The canonical factors diagonalize the Gram matrices of the unfoldings,
`U_kᴴ 𝒜_(k) 𝒜_(k)ᴴ U_k = diag(σ²)`, the hypothesis of the results in any factors. -/
theorem conjTranspose_hosvdFactor_mul_modeUnfold_mul_mul_hosvdFactor (k : ι) :
    (hosvdFactor A k)ᴴ * A.modeUnfold k * (A.modeUnfold k)ᴴ * hosvdFactor A k
      = diagonal fun i => ((((A.modeUnfold k)ᴴ.colSingularValues i) ^ 2 : ℝ) : 𝕜) := by
  rw [← conjTranspose_hosvdFactor_mul_modeUnfold_mul_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.mul_assoc _ (A.modeUnfold k)ᴴ]

/-- [golub2013matrix] (12.5.10), **all-orthogonality**: the rows of the mode-`k` unfolding of the
core are pairwise orthogonal, with Euclidean norms the singular values of `A_(k)`. -/
theorem modeUnfold_hosvdCore_row (k : ι) :
    (hosvdCore A).modeUnfold k * ((hosvdCore A).modeUnfold k)ᴴ
      = diagonal fun i => ((((A.modeUnfold k)ᴴ.colSingularValues i) ^ 2 : ℝ) : 𝕜) := by
  rw [hosvdCore, modeUnfold_hosvdCoreOf_mul_conjTranspose A (hosvdFactor_mem_unitaryGroup A),
    conjTranspose_hosvdFactor_mul_modeUnfold_mul_conjTranspose]

/-- The rows of the core's mode-`k` unfolding have Euclidean norms the singular values of
`A_(k)`. -/
theorem sum_norm_sq_modeUnfold_hosvdCore (k : ι) (i : κ k) :
    ∑ c, ‖(hosvdCore A).modeUnfold k i c‖ ^ 2 = (A.modeUnfold k)ᴴ.colSingularValues i ^ 2 :=
  sum_norm_sq_modeUnfold_hosvdCoreOf A (hosvdFactor_mem_unitaryGroup A)
    (conjTranspose_hosvdFactor_mul_modeUnfold_mul_mul_hosvdFactor A k) i

/-- The single-mode statement of [golub2013matrix] §12.5.1: `ℬ⁽ᵏ⁾ = 𝒜 ×_k U_kᴴ` (the book prints
`×_k U_k`) has `ℬ⁽ᵏ⁾_(k) ℬ⁽ᵏ⁾_(k)ᴴ = U_kᴴ 𝒜_(k) (U_kᴴ 𝒜_(k))ᴴ` for any square `U_k`; for the
left factor of an SVD of `𝒜_(k)` this is `Σ_k²`. -/
theorem modeProd_conjTranspose_row (k : ι) (V : Matrix (κ k) (κ k) 𝕜) :
    (A.modeProd k Vᴴ).modeUnfold k * ((A.modeProd k Vᴴ).modeUnfold k)ᴴ
      = Vᴴ * A.modeUnfold k * (Vᴴ * A.modeUnfold k)ᴴ := by
  rw [modeUnfold_modeProd]

/-- The single-mode statement of [golub2013matrix] §12.5.1 for the canonical factor: the mode-`k`
slices of `𝒜 ×_k U_kᴴ` are orthogonal, with Frobenius norms the singular values of `A_(k)`. -/
theorem modeProd_hosvdFactor_row (k : ι) :
    (A.modeProd k (hosvdFactor A k)ᴴ).modeUnfold k
        * ((A.modeProd k (hosvdFactor A k)ᴴ).modeUnfold k)ᴴ
      = diagonal fun i => ((((A.modeUnfold k)ᴴ.colSingularValues i) ^ 2 : ℝ) : 𝕜) := by
  rw [modeProd_conjTranspose_row, conjTranspose_hosvdFactor_mul_modeUnfold_mul_conjTranspose]

/-! ### Truncation -/

/-- The truncated HOSVD ([golub2013matrix] §12.5.2, `𝒜^{(r)}`) in the canonical factors: the
multilinear product by the orthogonal projections onto the kept left singular vectors `s k` of
each mode. -/
noncomputable def truncatedHOSVD (s : ∀ k, Finset (κ k)) : Tensor κ 𝕜 :=
  truncatedHOSVDOf (hosvdFactor A) A s

/-- The truncated HOSVD is the multilinear product of the factors with the core restricted to the
kept indices. -/
theorem truncatedHOSVD_eq_multilinearProd (s : ∀ k, Finset (κ k)) :
    truncatedHOSVD A s = multilinearProd (hosvdFactor A)
      (of fun j => if j ∈ Fintype.piFinset s then hosvdCore A j else 0) :=
  truncatedHOSVDOf_eq_multilinearProd A s

/-- [golub2013matrix] §12.5.2: `𝒜^{(r)} = ∑_{j ∈ ∏ s} 𝒮(j) U₁(:, j₁) ∘ ⋯ ∘ U_d(:, j_d)`. -/
theorem truncatedHOSVD_eq_sum (s : ∀ k, Finset (κ k)) :
    truncatedHOSVD A s
      = ∑ j ∈ Fintype.piFinset s, hosvdCore A j • rankOne fun k i => hosvdFactor A k i (j k) :=
  truncatedHOSVDOf_eq_sum A s

/-- **The truncation error of the HOSVD** ([golub2013matrix] (12.5.11), corrected: the book prints
`min_k` where `∑_k` is meant): `‖𝒜 − 𝒜^{(r)}‖² ≤ ∑_k ∑_{i ∉ s_k} σ_i(A_(k))²`, the canonical case of
`Tensor.norm_sub_truncatedHOSVDOf_sq_le`. -/
theorem norm_sub_truncatedHOSVD_sq_le (s : ∀ k, Finset (κ k)) :
    ‖A - truncatedHOSVD A s‖ ^ 2
      ≤ ∑ k, ∑ i ∈ (s k)ᶜ, (A.modeUnfold k)ᴴ.colSingularValues i ^ 2 :=
  norm_sub_truncatedHOSVDOf_sq_le A (hosvdFactor_mem_unitaryGroup A)
    (conjTranspose_hosvdFactor_mul_modeUnfold_mul_mul_hosvdFactor A) s

open scoped Matrix.Norms.Frobenius in
/-- **The lower bound for approximations of low multilinear rank**: if the mode-`k` unfolding of
`B` has rank at most `r`, then `∑_{r ≤ i < n_k} σ_i(A_(k))² ≤ ‖A − B‖²`, `n_k = card (κ k)`.
Eckart–Young–Mirsky (`Matrix.sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le`) for
the unfoldings, which are isometries (`Tensor.frobenius_norm_modeUnfold`). Together with
`Tensor.norm_sub_truncatedHOSVD_sq_le` it puts the truncated HOSVD within a factor `d` (the number
of modes) of the best approximation of multilinear rank `r` in squared norm, and it refutes the
`min_k` misprint of [golub2013matrix] (12.5.11) for any `A` truncated in one mode only. -/
theorem sum_sq_le_norm_sub_sq_of_multilinearRank_le {A B : Tensor κ 𝕜} {r : ℕ} {k : ι}
    (hB : multilinearRank B k ≤ r) :
    ∑ i ∈ Finset.Ico r (Fintype.card (κ k)), (A.modeUnfold k).sortedSingularValues i ^ 2 ≤
      ‖A - B‖ ^ 2 := by
  have h := sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le
    (C := A.modeUnfold k) (Ĉ := B.modeUnfold k) hB
  have hsub : A.modeUnfold k - B.modeUnfold k = (A - B).modeUnfold k := rfl
  rw [hsub, frobenius_norm_modeUnfold] at h
  refine le_trans (le_of_eq ?_) h
  refine (Finset.sum_subset (Finset.Ico_subset_Ico_right (min_le_left _ _))
    fun i hi hi' => ?_).symm
  rw [Finset.mem_Ico] at hi hi'
  rw [sortedSingularValues_eq_zero_of_min_le _ (by omega), zero_pow two_ne_zero]

end Tensor
