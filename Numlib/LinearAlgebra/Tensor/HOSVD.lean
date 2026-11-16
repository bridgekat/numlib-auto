/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $\mathcal{A}$ be a tensor over
$\mathbb{K}$ with finite index types $\kappa_k$. The **higher-order singular value decomposition**
(HOSVD) of $\mathcal{A}$ ([golub2013matrix], §12.5.1–12.5.2 and Theorem 12.5.1, after De Lathauwer,
De Moor and Vandewalle) is
$$\mathcal{A} = \mathcal{S} \times_1 U_1 \cdots \times_d U_d, \qquad \mathcal{S} = \mathcal{A}
  \times_1 U_1^H \cdots \times_d U_d^H,$$
where each $U_k$ is the unitary matrix of left singular vectors of the mode-$k$ unfolding
$\mathcal{A}_{(k)}$. The core $\mathcal{S}$ is all-orthogonal: the rows of $\mathcal{S}_{(k)}$ are
pairwise orthogonal, and their Euclidean norms are the singular values of $\mathcal{A}_{(k)}$. The
multilinear rank of $\mathcal{A}$ is the vector of the ranks of the unfoldings $\mathcal{A}_{(k)}$.
The truncated HOSVD $\mathcal{A}^{(r)}$ keeps a set $s_k$ of columns of each $U_k$, and its error
satisfies
$$\|\mathcal{A} - \mathcal{A}^{(r)}\|^2 \le \sum_k \sum_{i \notin s_k}
  \sigma_i(\mathcal{A}_{(k)})^2.$$
Every approximation $\mathcal{B}$ with $\operatorname{rank} \mathcal{B}_{(k)} \le r$ has the error
$\|\mathcal{A} - \mathcal{B}\|^2 \ge \sum_{i > r} \sigma_i(\mathcal{A}_{(k)})^2$.

[golub2013matrix] prints the truncation bound (12.5.11) with $\min_k$ in place of $\sum_k$. That
bound is false: a tensor that is truncated in one mode only has $\min_k = 0$ and a nonzero error.
The bound proved here has $\sum_k$.

## Main definitions

* `Tensor.multilinearRank`: the rank of the mode-$k$ unfolding.
* `Tensor.hosvdCoreOf`, `Tensor.truncatedHOSVDOf`: the core and the truncation for any family of
  unitary factors.
* `Tensor.hosvdFactor`, `Tensor.hosvdCore`: the canonical factors and the canonical core of the
  HOSVD.
* `Tensor.truncatedHOSVD`: the HOSVD truncated to the singular directions $s_k$ in each mode.

## Main results

* `Tensor.multilinearProd_hosvdFactor_hosvdCore`: Theorem 12.5.1 of [golub2013matrix],
  $\mathcal{A} = \mathcal{S} \times_1 U_1 \cdots \times_d U_d$.
* `Tensor.modeUnfold_hosvdCore_row`: all-orthogonality (12.5.10), $\mathcal{S}_{(k)}
  \mathcal{S}_{(k)}^H = \operatorname{diag}(\sigma_i(\mathcal{A}_{(k)})^2)$.
* `Tensor.norm_sub_truncatedHOSVDOf_sq_le`, `Tensor.norm_sub_truncatedHOSVD_sq_le`: the truncation
  error bound, (12.5.11) with $\sum_k$, for the factors of any SVDs of the unfoldings and for the
  canonical factors.
* `Tensor.sum_sq_le_norm_sub_sq_of_multilinearRank_le`: the lower bound for every approximation of
  multilinear rank at most $r$, from the Eckart–Young–Mirsky theorem for each unfolding.

## Implementation notes

* The real case of [golub2013matrix] reads $U^H$ as $U^T$.
* The core `Tensor.hosvdCoreOf U A` and the truncation `Tensor.truncatedHOSVDOf U A s` are defined
  for any family $U$ of unitary matrices. The HOSVD (`Tensor.multilinearProd_hosvdCoreOf`),
  all-orthogonality (`Tensor.modeUnfold_hosvdCoreOf_mul_conjTranspose`) and the truncation bound
  (`Tensor.norm_sub_truncatedHOSVDOf_sq_le`) are proved in this generality. The truncation bound
  needs $U_k^H \mathcal{A}_{(k)} \mathcal{A}_{(k)}^H U_k = \operatorname{diag}(\sigma_k^2)$, so it
  holds for the left factors of any SVDs of the unfoldings, with the singular values sorted or not.
* The canonical mode-$k$ factor `Tensor.hosvdFactor A k` is the right singular unitary
  `Matrix.rightSingularUnitary` of $\mathcal{A}_{(k)}^H$. Its columns are an orthonormal eigenbasis
  of $\mathcal{A}_{(k)} \mathcal{A}_{(k)}^H$, that is, left singular vectors of $\mathcal{A}_{(k)}$.
  They are paired index by index with the singular values `((A.modeUnfold k)ᴴ).colSingularValues`,
  which are indexed by `κ k` in no particular order. The canonical core is `Tensor.hosvdCore A`. The
  HOSVD is therefore a theorem about these definitions, not an existence statement: it is the case
  `U = Tensor.hosvdFactor A` of the results for any factors.
-/

universe u v

open Matrix

namespace Tensor

variable {ι : Type u} {κ : ι → Type v} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]

/-- The **multilinear rank** of a tensor $\mathcal{A}$ over a commutative ring ([golub2013matrix],
§12.5.2, $\operatorname{rank}_*(\mathcal{A})$) is the vector of the ranks of the unfoldings: its
component at the mode $k$ is $\operatorname{rank} \mathcal{A}_{(k)}$. -/
noncomputable def multilinearRank {R : Type*} [CommRing R] (A : Tensor κ R) (k : ι) : ℕ :=
  (A.modeUnfold k).rank

variable {𝕜 : Type*} [RCLike 𝕜] [∀ i, DecidableEq (κ i)]

/-!
### Cores and truncations for any unitary factors

The results of this section hold for any family of unitary matrices $U_k$ indexed by $\kappa_k$, in
particular for the factors of any SVDs of the unfoldings (Theorem 12.5.1 of [golub2013matrix] builds
the HOSVD from arbitrary SVDs). The core $\mathcal{A} \times_1 U_1^H \cdots \times_d U_d^H$ recovers
$\mathcal{A}$, the rows of its mode-$k$ unfolding have the Gram matrix $U_k^H \mathcal{A}_{(k)}
\mathcal{A}_{(k)}^H U_k$, and the truncation bound holds when this Gram matrix is diagonal.
-/

section Factors

/-- The **core** of $\mathcal{A}$ for the factors $U_k$ ([golub2013matrix], (12.5.6)) is
$\mathcal{A} \times_1 U_1^H \cdots \times_d U_d^H$. -/
noncomputable def hosvdCoreOf (U : ∀ k, Matrix (κ k) (κ k) 𝕜) (A : Tensor κ 𝕜) : Tensor κ 𝕜 :=
  multilinearProd (fun k => (U k)ᴴ) A

/-- The **truncation** of $\mathcal{A}$ to the columns $s_k$ of the factors $U_k$
([golub2013matrix], §12.5.2, $\mathcal{A}^{(r)}$) is the multilinear product of $\mathcal{A}$ by
the matrices $U_k D_k U_k^H$, where $D_k$ is the diagonal matrix with $1$ at the indices in
$s_k$ and $0$ elsewhere. For unitary $U_k$, these matrices are the orthogonal projections onto
the span of the kept columns. -/
noncomputable def truncatedHOSVDOf (U : ∀ k, Matrix (κ k) (κ k) 𝕜) (A : Tensor κ 𝕜)
    (s : ∀ k, Finset (κ k)) : Tensor κ 𝕜 :=
  multilinearProd (fun k => U k * diagonal (fun i => if i ∈ s k then 1 else 0) * (U k)ᴴ) A

variable {U : ∀ k, Matrix (κ k) (κ k) 𝕜} (A : Tensor κ 𝕜)

/-- **The HOSVD for any unitary factors** ([golub2013matrix], Theorem 12.5.1 and (12.5.6)). If every
$U_k$ is unitary, then
$$\mathcal{A} = \mathcal{S} \times_1 U_1 \cdots \times_d U_d, \qquad \mathcal{S} = \mathcal{A}
  \times_1 U_1^H \cdots \times_d U_d^H.$$
-/
theorem multilinearProd_hosvdCoreOf (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜) :
    multilinearProd U (hosvdCoreOf U A) = A := by
  rw [hosvdCoreOf, multilinearProd_multilinearProd]
  simp_rw [fun k => mul_conjTranspose_self_of_mem_unitaryGroup (hU k), multilinearProd_one]

/-- The HOSVD for any unitary factors as a sum of rank-one tensors ([golub2013matrix], (12.5.7)): if
every $U_k$ is unitary and $\mathcal{S}$ is the core, then $\mathcal{A} = \sum_j \mathcal{S}(j)
\, U_1(:, j_1) \circ \cdots \circ U_d(:, j_d)$. -/
theorem eq_sum_hosvdCoreOf_smul_rankOne (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜) :
    A = ∑ j, hosvdCoreOf U A j • rankOne fun k i => U k i (j k) := by
  conv_lhs => rw [← multilinearProd_hosvdCoreOf A hU]
  exact multilinearProd_eq_sum_rankOne _ _

/-- If every $U_j$ is unitary, then the transpose $W$ of the Kronecker product of the matrices
$U_j^H$ with $j \neq k$ satisfies $W W^H = I$. -/
private theorem transpose_piKronecker_mul_conjTranspose (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜)
    (k : ι) :
    (piKronecker fun j : {j // j ≠ k} => (U j)ᴴ)ᵀ
        * ((piKronecker fun j : {j // j ≠ k} => (U j)ᴴ)ᵀ)ᴴ = 1 := by
  set P := piKronecker fun j : {j // j ≠ k} => (U j)ᴴ
  have hP : Pᴴ * P = 1 := conjTranspose_piKronecker_mul_piKronecker fun j => by
    rw [conjTranspose_conjTranspose]
    exact mul_conjTranspose_self_of_mem_unitaryGroup (hU j)
  have hT : (Pᵀ)ᴴ = (Pᴴ)ᵀ := by
    ext
    simp
  rw [hT, ← transpose_mul, hP, transpose_one]

/-- **All-orthogonality for any unitary factors** ([golub2013matrix], (12.5.10)). If every $U_k$ is
unitary and $\mathcal{S} = \mathcal{A} \times_1 U_1^H \cdots \times_d U_d^H$, then for every
mode $k$ the rows of $\mathcal{S}_{(k)}$ have the Gram matrix
$$\mathcal{S}_{(k)} \mathcal{S}_{(k)}^H = U_k^H \mathcal{A}_{(k)} \bigl(U_k^H
  \mathcal{A}_{(k)}\bigr)^H.$$
-/
theorem modeUnfold_hosvdCoreOf_mul_conjTranspose (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜)
    (k : ι) :
    (hosvdCoreOf U A).modeUnfold k * ((hosvdCoreOf U A).modeUnfold k)ᴴ
      = (U k)ᴴ * A.modeUnfold k * ((U k)ᴴ * A.modeUnfold k)ᴴ := by
  rw [hosvdCoreOf, modeUnfold_multilinearProd, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ (((U k)ᴴ * A.modeUnfold k)ᴴ),
    transpose_piKronecker_mul_conjTranspose hU, Matrix.one_mul]

/-- Let every $U_k$ be unitary, and let $U_k^H \mathcal{A}_{(k)} \mathcal{A}_{(k)}^H U_k =
\operatorname{diag}(\sigma_i^2)$, for example because $U_k$ is the left factor of an SVD of
$\mathcal{A}_{(k)}$. Then the row $i$ of the mode-$k$ unfolding of the core has the squared
Euclidean norm $\sigma_i^2$. -/
theorem sum_norm_sq_modeUnfold_hosvdCoreOf (hU : ∀ k, U k ∈ unitaryGroup (κ k) 𝕜) {k : ι}
    {σ : κ k → ℝ}
    (hσ : (U k)ᴴ * A.modeUnfold k * (A.modeUnfold k)ᴴ * U k = diagonal fun i => ((σ i ^ 2 : ℝ) : 𝕜))
    (i : κ k) :
    ∑ c, ‖(hosvdCoreOf U A).modeUnfold k i c‖ ^ 2 = σ i ^ 2 := by
  have h := congrFun (congrFun (modeUnfold_hosvdCoreOf_mul_conjTranspose A hU k) i) i
  rw [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc, hσ,
    diagonal_apply_eq, Matrix.mul_apply] at h
  simp only [conjTranspose_apply, RCLike.star_def, RCLike.mul_conj] at h
  exact_mod_cast h

/-- The truncation for the factors $U_k$ is the multilinear product of the $U_k$ with the core
restricted to the kept indices: the core entries at the tuples $j$ with $j_k \in s_k$ for every
$k$ are kept, and the other entries are replaced by $0$. -/
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

/-- The truncation for any factors as a sum of rank-one tensors ([golub2013matrix], §12.5.2):
$$\mathcal{A}^{(r)} = \sum_{j \in s_1 \times \cdots \times s_d} \mathcal{S}(j) \, U_1(:, j_1)
  \circ \cdots \circ U_d(:, j_d),$$
where $\mathcal{S}$ is the core for the factors $U_k$. -/
theorem truncatedHOSVDOf_eq_sum (s : ∀ k, Finset (κ k)) :
    truncatedHOSVDOf U A s
      = ∑ j ∈ Fintype.piFinset s, hosvdCoreOf U A j • rankOne fun k i => U k i (j k) := by
  rw [truncatedHOSVDOf_eq_multilinearProd, multilinearProd_eq_sum_rankOne,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Fintype.piFinset s)]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter (· ∉ Fintype.piFinset s)) fun j hj => by
    rw [of_apply, ite_eq_right (Finset.mem_filter.1 hj).2, zero_smul], add_zero,
    Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact Finset.sum_congr rfl fun j hj => by rw [of_apply, ite_eq_left hj]

/-- **The truncation error of the HOSVD, for any SVD factors** ([golub2013matrix], (12.5.11)). Let
every $U_k$ be unitary with
$$U_k^H \mathcal{A}_{(k)} \mathcal{A}_{(k)}^H U_k = \operatorname{diag}(\sigma_k(i)^2)_{i \in
  \kappa_k},$$
which holds when $U_k$ is the left factor of any SVD of $\mathcal{A}_{(k)}$, as in Theorem
12.5.1. Then for all sets $s_k$ of kept indices, the truncation $\mathcal{A}^{(r)}$ satisfies
$$\|\mathcal{A} - \mathcal{A}^{(r)}\|^2 \le \sum_k \sum_{i \notin s_k} \sigma_k(i)^2.$$

[golub2013matrix] prints $\min_k$ in place of $\sum_k$. That bound is false: a tensor that is
truncated in one mode only has $\min_k = 0$ and a nonzero error; see
`Tensor.sum_sq_le_norm_sub_sq_of_multilinearRank_le`. -/
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
  rw [hA, frobenius_norm_multilinearProd_of_orthonormal
      (fun k => conjTranspose_mul_self_of_mem_unitaryGroup (hU k)),
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

/-- The **mode-$k$ factor of the HOSVD**: a unitary matrix whose columns are left singular vectors
of the mode-$k$ unfolding $\mathcal{A}_{(k)}$. The column $i$ is paired with the singular value
`((A.modeUnfold k)ᴴ).colSingularValues i`.

It is `Matrix.rightSingularUnitary` of $\mathcal{A}_{(k)}^H$. -/
noncomputable def hosvdFactor (A : Tensor κ 𝕜) (k : ι) : Matrix (κ k) (κ k) 𝕜 :=
  (A.modeUnfold k)ᴴ.rightSingularUnitary

/-- The **core tensor of the HOSVD** ([golub2013matrix], (12.5.6)): $\mathcal{S} = \mathcal{A}
\times_1 U_1^H \cdots \times_d U_d^H$, the core `Tensor.hosvdCoreOf` for the canonical factors
$U_k$ = `Tensor.hosvdFactor A k`. -/
noncomputable def hosvdCore (A : Tensor κ 𝕜) : Tensor κ 𝕜 :=
  hosvdCoreOf (hosvdFactor A) A

variable (A : Tensor κ 𝕜)

/-- The factors of the HOSVD are unitary. -/
theorem hosvdFactor_mem_unitaryGroup (k : ι) : hosvdFactor A k ∈ unitaryGroup (κ k) 𝕜 :=
  rightSingularUnitary_mem_unitaryGroup _

/-- The factors of the HOSVD have orthonormal columns: $U_k^H U_k = I$. -/
theorem conjTranspose_hosvdFactor_mul_hosvdFactor (k : ι) :
    (hosvdFactor A k)ᴴ * hosvdFactor A k = 1 := by
  rw [← star_eq_conjTranspose]
  exact star_mul_rightSingularUnitary _

/-- The factors of the HOSVD have orthonormal rows: $U_k U_k^H = I$. -/
theorem hosvdFactor_mul_conjTranspose_hosvdFactor (k : ι) :
    hosvdFactor A k * (hosvdFactor A k)ᴴ = 1 := by
  rw [← star_eq_conjTranspose]
  exact rightSingularUnitary_mul_star _

/-- **The HOSVD** ([golub2013matrix], Theorem 12.5.1 and (12.5.6)). Let $\mathbb{K}$ be $\mathbb{R}$
or $\mathbb{C}$, let $\mathcal{A}$ be a tensor over $\mathbb{K}$ with finite index types, let
$U_k$ be the canonical factors (`Tensor.hosvdFactor`), and let $\mathcal{S}$ be the canonical
core (`Tensor.hosvdCore`). Then
$$\mathcal{A} = \mathcal{S} \times_1 U_1 \cdots \times_d U_d.$$
-/
theorem multilinearProd_hosvdFactor_hosvdCore :
    multilinearProd (hosvdFactor A) (hosvdCore A) = A :=
  multilinearProd_hosvdCoreOf A (hosvdFactor_mem_unitaryGroup A)

/-- The HOSVD as a sum of rank-one tensors ([golub2013matrix], (12.5.7)): $\mathcal{A} = \sum_j
\mathcal{S}(j) \, U_1(:, j_1) \circ \cdots \circ U_d(:, j_d)$ for the canonical factors and
core. -/
theorem hosvd_eq_sum_rankOne :
    A = ∑ j, hosvdCore A j • rankOne fun k i => hosvdFactor A k i (j k) :=
  eq_sum_hosvdCoreOf_smul_rankOne A (hosvdFactor_mem_unitaryGroup A)

/-! ### All-orthogonality -/

/-- The Gram matrix of $U_k^H \mathcal{A}_{(k)}$, for the canonical factor $U_k$, is the diagonal
matrix of the squared singular values of $\mathcal{A}_{(k)}$: $U_k^H \mathcal{A}_{(k)} (U_k^H
\mathcal{A}_{(k)})^H = \operatorname{diag}(\sigma_i^2)$. -/
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

/-- The canonical factors diagonalize the Gram matrices of the unfoldings: $U_k^H \mathcal{A}_{(k)}
\mathcal{A}_{(k)}^H U_k = \operatorname{diag}(\sigma_i^2)$, with the singular values $\sigma_i$
of $\mathcal{A}_{(k)}$. This is the hypothesis of the results for any factors. -/
theorem conjTranspose_hosvdFactor_mul_modeUnfold_mul_mul_hosvdFactor (k : ι) :
    (hosvdFactor A k)ᴴ * A.modeUnfold k * (A.modeUnfold k)ᴴ * hosvdFactor A k
      = diagonal fun i => ((((A.modeUnfold k)ᴴ.colSingularValues i) ^ 2 : ℝ) : 𝕜) := by
  rw [← conjTranspose_hosvdFactor_mul_modeUnfold_mul_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.mul_assoc _ (A.modeUnfold k)ᴴ]

/-- **All-orthogonality** ([golub2013matrix], (12.5.10)). Let $\mathcal{S}$ be the canonical core of
the HOSVD of $\mathcal{A}$. Then for every mode $k$,
$$\mathcal{S}_{(k)} \mathcal{S}_{(k)}^H =
  \operatorname{diag}\bigl(\sigma_i(\mathcal{A}_{(k)})^2\bigr)_{i \in \kappa_k}:$$
the rows of $\mathcal{S}_{(k)}$ are pairwise orthogonal, and their Euclidean norms are the
singular values of $\mathcal{A}_{(k)}$.

The singular value $\sigma_i(\mathcal{A}_{(k)})$ is `((A.modeUnfold k)ᴴ).colSingularValues i`,
indexed by `κ k` in no particular order. -/
theorem modeUnfold_hosvdCore_row (k : ι) :
    (hosvdCore A).modeUnfold k * ((hosvdCore A).modeUnfold k)ᴴ
      = diagonal fun i => ((((A.modeUnfold k)ᴴ.colSingularValues i) ^ 2 : ℝ) : 𝕜) := by
  rw [hosvdCore, modeUnfold_hosvdCoreOf_mul_conjTranspose A (hosvdFactor_mem_unitaryGroup A),
    conjTranspose_hosvdFactor_mul_modeUnfold_mul_conjTranspose]

/-- The row $i$ of the mode-$k$ unfolding of the canonical core has the squared Euclidean norm
$\sigma_i(\mathcal{A}_{(k)})^2$. -/
theorem sum_norm_sq_modeUnfold_hosvdCore (k : ι) (i : κ k) :
    ∑ c, ‖(hosvdCore A).modeUnfold k i c‖ ^ 2 = (A.modeUnfold k)ᴴ.colSingularValues i ^ 2 :=
  sum_norm_sq_modeUnfold_hosvdCoreOf A (hosvdFactor_mem_unitaryGroup A)
    (conjTranspose_hosvdFactor_mul_modeUnfold_mul_mul_hosvdFactor A k) i

/-- The single-mode statement of [golub2013matrix], §12.5.1, for any square matrix $V$ indexed by
$\kappa_k$: the tensor $\mathcal{B} = \mathcal{A} \times_k V^H$ satisfies
$$\mathcal{B}_{(k)} \mathcal{B}_{(k)}^H = V^H \mathcal{A}_{(k)} \bigl(V^H
  \mathcal{A}_{(k)}\bigr)^H.$$
For the left factor of an SVD of $\mathcal{A}_{(k)}$, this is $\Sigma_k^2$.

The book prints $\mathcal{B}^{(k)} = \mathcal{A} \times_k U_k$; the product with $U_k^H$ is
meant. -/
theorem modeProd_conjTranspose_row (k : ι) (V : Matrix (κ k) (κ k) 𝕜) :
    (A.modeProd k Vᴴ).modeUnfold k * ((A.modeProd k Vᴴ).modeUnfold k)ᴴ
      = Vᴴ * A.modeUnfold k * (Vᴴ * A.modeUnfold k)ᴴ := by
  rw [modeUnfold_modeProd]

/-- The single-mode statement of [golub2013matrix], §12.5.1, for the canonical factor $U_k$: the
tensor $\mathcal{B} = \mathcal{A} \times_k U_k^H$ satisfies $\mathcal{B}_{(k)}
\mathcal{B}_{(k)}^H = \operatorname{diag}(\sigma_i(\mathcal{A}_{(k)})^2)$. Hence the mode-$k$
slices of $\mathcal{B}$ are orthogonal, and their Frobenius norms are the singular values of
$\mathcal{A}_{(k)}$. -/
theorem modeProd_hosvdFactor_row (k : ι) :
    (A.modeProd k (hosvdFactor A k)ᴴ).modeUnfold k
        * ((A.modeProd k (hosvdFactor A k)ᴴ).modeUnfold k)ᴴ
      = diagonal fun i => ((((A.modeUnfold k)ᴴ.colSingularValues i) ^ 2 : ℝ) : 𝕜) := by
  rw [modeProd_conjTranspose_row, conjTranspose_hosvdFactor_mul_modeUnfold_mul_conjTranspose]

/-! ### Truncation -/

/-- The **truncated HOSVD** $\mathcal{A}^{(r)}$ ([golub2013matrix], §12.5.2) for the canonical
factors $U_k$: the multilinear product of $\mathcal{A}$ by the orthogonal projections onto the
kept left singular vectors $U_k(:, i)$, $i \in s_k$, of each mode. -/
noncomputable def truncatedHOSVD (s : ∀ k, Finset (κ k)) : Tensor κ 𝕜 :=
  truncatedHOSVDOf (hosvdFactor A) A s

/-- The truncated HOSVD is the multilinear product of the canonical factors with the canonical core
restricted to the kept indices: the core entries at the tuples $j$ with $j_k \in s_k$ for every
$k$ are kept, and the other entries are replaced by $0$. -/
theorem truncatedHOSVD_eq_multilinearProd (s : ∀ k, Finset (κ k)) :
    truncatedHOSVD A s = multilinearProd (hosvdFactor A)
      (of fun j => if j ∈ Fintype.piFinset s then hosvdCore A j else 0) :=
  truncatedHOSVDOf_eq_multilinearProd A s

/-- The truncated HOSVD as a sum of rank-one tensors ([golub2013matrix], §12.5.2):
$$\mathcal{A}^{(r)} = \sum_{j \in s_1 \times \cdots \times s_d} \mathcal{S}(j) \, U_1(:, j_1)
  \circ \cdots \circ U_d(:, j_d).$$
-/
theorem truncatedHOSVD_eq_sum (s : ∀ k, Finset (κ k)) :
    truncatedHOSVD A s
      = ∑ j ∈ Fintype.piFinset s, hosvdCore A j • rankOne fun k i => hosvdFactor A k i (j k) :=
  truncatedHOSVDOf_eq_sum A s

/-- **The truncation error of the HOSVD** ([golub2013matrix], (12.5.11)). Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $\mathcal{A}$ be a tensor over $\mathbb{K}$ with finite index
types, and let $s_k \subseteq \kappa_k$ be the kept indices of each mode. Then the truncated
HOSVD $\mathcal{A}^{(r)}$ satisfies
$$\|\mathcal{A} - \mathcal{A}^{(r)}\|^2 \le \sum_k \sum_{i \notin s_k}
  \sigma_i(\mathcal{A}_{(k)})^2.$$

[golub2013matrix] prints $\min_k$ in place of $\sum_k$. That bound is false: a tensor that is
truncated in one mode only has $\min_k = 0$ and a nonzero error.

The singular value $\sigma_i(\mathcal{A}_{(k)})$ is `((A.modeUnfold k)ᴴ).colSingularValues i`.
This is the case of the canonical factors of `Tensor.norm_sub_truncatedHOSVDOf_sq_le`. -/
theorem norm_sub_truncatedHOSVD_sq_le (s : ∀ k, Finset (κ k)) :
    ‖A - truncatedHOSVD A s‖ ^ 2
      ≤ ∑ k, ∑ i ∈ (s k)ᶜ, (A.modeUnfold k)ᴴ.colSingularValues i ^ 2 :=
  norm_sub_truncatedHOSVDOf_sq_le A (hosvdFactor_mem_unitaryGroup A)
    (conjTranspose_hosvdFactor_mul_modeUnfold_mul_mul_hosvdFactor A) s

open scoped Matrix.Norms.Frobenius in
/-- **The lower bound for approximations of low multilinear rank.** Let $\mathbb{K}$ be $\mathbb{R}$
or $\mathbb{C}$, and let $\mathcal{A}$ and $\mathcal{B}$ be tensors over $\mathbb{K}$ with
finite index types. If $\operatorname{rank} \mathcal{B}_{(k)} \le r$ for a mode $k$, then
$$\sum_{i = r+1}^{n_k} \sigma_i(\mathcal{A}_{(k)})^2 \le \|\mathcal{A} - \mathcal{B}\|^2, \qquad
  n_k = |\kappa_k|,$$
with the singular values $\sigma_1 \ge \sigma_2 \ge \cdots$ in nonincreasing order.

The singular value $\sigma_{i+1}(\mathcal{A}_{(k)})$ is
`Matrix.sortedSingularValues (A.modeUnfold k) i`, so the Lean sum runs over $r \le i < n_k$. The
proof applies the Eckart–Young–Mirsky theorem
`Matrix.sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le` to the unfoldings,
which preserve the Frobenius norm (`Tensor.frobenius_norm_modeUnfold`). Together with
`Tensor.norm_sub_truncatedHOSVD_sq_le`, the bound puts the truncated HOSVD within a factor $d$,
the number of modes, of the best approximation of multilinear rank $r$ in squared norm. It also
refutes the misprint $\min_k$ in (12.5.11) of [golub2013matrix] for every $\mathcal{A}$ that is
truncated in one mode only. -/
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
