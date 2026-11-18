/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.SingularValues`, beside Mathlib's
`LinearMap.singularValues`. The condition-number section is the exception: it names
`NormedRing.condNumber`, which is `Numlib`'s.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Numlib.Analysis.InnerProductSpace.NormPow
import Numlib.Analysis.InnerProductSpace.Orthonormal
import Numlib.Analysis.InnerProductSpace.SingularValues
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Ring.CondNumber
import Numlib.Data.Fin.Sum
import Numlib.Data.Fin.Tuple.Sort
import Numlib.LinearAlgebra.Matrix.Charpoly
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv

/-!
# The singular value decomposition

Let $A \in \mathbb{K}^{m \times n}$ with $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The singular
values $\sigma_i$ of $A$ are the square roots of the eigenvalues of the positive semidefinite matrix
$A^H A$. An orthonormal eigenbasis $(u_i)$ of $A^H A$ is a family of *right singular vectors*: the
images $A u_i$ are pairwise orthogonal with $\|A u_i\| = \sigma_i$, so the normalized nonzero images
form an orthonormal family $(v_i)$ of *left singular vectors*, and $Ax = \sum_i \sigma_i \langle
u_i, x \rangle v_i$. This is the *singular system* of [kress1998numerical], §5.2, Theorem 5.4. The
full factorization $U^H A V = \Sigma$, with unitary $U$ and $V$ and the sorted singular values on
the diagonal of the rectangular diagonal matrix $\Sigma$, is Property 1.7 of
[quarteroni2000numerical], §1.9, and Theorem 2.4.1 of [golub2013matrix], §2.4.

Two constructions use the singular system. The **Moore–Penrose pseudoinverse** $A^+ = (A^H A)^+ A^H$
inverts the nonzero eigenvalues of $A^H A$ and keeps the zero ones. It is the unique matrix that
satisfies the four Penrose conditions, $A^+ y$ is the least-squares solution of $Ax = y$ of smallest
norm, and $A A^+$ and $A^+ A$ are the orthogonal projections onto the ranges of $A$ and $A^H$
([golub2013matrix], §5.5). The **spectral condition number** of a nonsingular matrix is the ratio
$\sigma_{\max} / \sigma_{\min}$ of its extreme singular values. Every consequence of a factorization
$U^H A V = \Sigma$ is stated for an arbitrary such factorization, because the factors are not
unique.

## Main definitions

* `Matrix.colSingularValues` and `Matrix.rightSingularBasis`: the singular values indexed by the
  columns of $A$ (not sorted), and the orthonormal eigenbasis of $A^H A$ that they come from.
  `Matrix.rightSingularUnitary` is the same eigenbasis as a unitary matrix.
* `Matrix.sortedSingularValues`: the singular values $\sigma_0 \ge \sigma_1 \ge \dots$ in
  nonincreasing order, indexed from $0$.
* `Matrix.gramPinv` and `Matrix.pinv`: the Moore–Penrose pseudoinverses of $A^H A$ and of $A$.
* `Matrix.rectDiagonal`: the rectangular diagonal matrix $\operatorname{diag}(\sigma_0, \sigma_1,
  \dots) \in \mathbb{K}^{m \times n}$. `Matrix.shiftedRectDiagonal k σ` has $\sigma_j$ at the
  entries $(j - k, j)$.
* `Matrix.sortedRightSingularVec`: the right singular vectors sorted by decreasing singular value.
* `Matrix.unitaryOfBasis`: the unitary matrix whose columns are the vectors of an orthonormal basis
  of $\mathbb{K}^n$.
* `Matrix.IsSVD`: the property that $U^H A V = \operatorname{diag}(\sigma)$ is a singular value
  decomposition.
* `Matrix.svdTruncation`: the rank-$k$ truncation $\sum_{i < k} \sigma_i u_i v_i^H$ of a
  factorization.

## Main results

* `Matrix.exists_singularSystem`: the singular system of $A$ and the expansion of $A$ along it.
  `Matrix.norm_sq_toEuclideanLin_apply` is the Parseval identity $\|Ax\|^2 = \sum_i \sigma_i^2
  |\langle u_i, x \rangle|^2$.
* `Matrix.pinv_unique`: the four Penrose conditions characterize $A^+$.
  `Matrix.norm_toEuclideanLin_pinv_sub_eq_iInf` and `Matrix.norm_pinv_le_of_normalEquations`:
  $A^+ y$ is the least-squares solution of least norm. `Matrix.mul_pinv_eq_starProjection` and
  `Matrix.pinv_mul_eq_starProjection`: the two orthogonal projections.
* `Matrix.l2_opNorm_eq_iSup_colSingularValues`, `Matrix.l2_opNorm_inv_eq_inv_iInf_colSingularValues`
  and `Matrix.condNumber_l2_eq_div_colSingularValues`: $\|A\|_2 = \sigma_{\max}$,
  $\|A^{-1}\|_2 = 1/\sigma_{\min}$ and $\kappa_2(A) = \sigma_{\max}/\sigma_{\min}$.
* `Matrix.exists_equiv_colSingularValues_eq_sortedSingularValues`: the column-indexed and the sorted
  singular values are the same multiset. `Matrix.sortedSingularValues_zero_eq_l2_opNorm`
  ($\sigma_0 = \|A\|_2$), `Matrix.sortedSingularValues_eq_zero_iff_rank_le` (the rank counts the
  positive singular values) and `Matrix.iInf_colSingularValues_eq_iInf_norm` (the least singular
  value is the least stretch $\min_{\|x\| = 1} \|Ax\|$), from [golub2013matrix], §2.4.
* `Matrix.exists_mem_unitaryGroup_submatrix_eq`: orthonormal columns extend to a unitary matrix
  ([golub2013matrix], Theorem 2.1.1).
* `Matrix.exists_svd`: the full factorization $U^H A V = \Sigma$ with square unitary factors and the
  sorted singular values on the diagonal ([quarteroni2000numerical], Property 1.7), and
  `Matrix.exists_thin_svd`, the thin factorization.
* `Matrix.pinv_eq_of_svd` ($A^+ = V \Sigma^+ U^H$, Definition 1.15 of [quarteroni2000numerical]),
  `Matrix.ker_mulVecLin_eq_span_of_svd`, `Matrix.range_mulVecLin_eq_span_of_svd` and
  `Matrix.singularValues_eq_of_svd` (uniqueness of the singular values): the consequences of any
  factorization, each also stated for `Matrix.IsSVD` (`Matrix.IsSVD.pinv_eq`, …,
  `Matrix.IsSVD.singularValues_eq`).
* `Matrix.IsHermitian.exists_equiv_colSingularValues_eq_abs_eigenvalues`: the singular values of a
  Hermitian matrix are the moduli $|\lambda_i|$ of its eigenvalues. It is a case of
  `Matrix.exists_equiv_colSingularValues_eq_of_conjTranspose_mul_self_eq`: if
  $A^H A = U \operatorname{diag}(d_i^2) U^H$ with $d \ge 0$, then the $d_i$ are the singular values.
* `Matrix.sortedSingularValues_unitary_mul_mul`: the sorted singular values are unitarily invariant.
  `Matrix.isUnit_of_iInf_colSingularValues_pos`: a square matrix with positive least singular value
  is invertible. `Matrix.exists_colSingularValues_eq_of_mulVec`: if $A^H A g = s^2 g$ with
  $g \neq 0$ and $s \ge 0$, then $s$ is a singular value.
* `Matrix.exists_eq_sum_sortedSingularValues_smul_vecMulVec`: the sorted singular expansion $M =
  \sum_{k < \operatorname{rank} M} \sigma_k u_k v_k^H$ with orthonormal $u$, $v$ and positive
  $\sigma_k$.
* `Matrix.svdTruncation_eq_sum`: the truncation $U \Sigma_k V^H$ is
  $\sum_{i < k} \sigma_i u_i v_i^H$ ([golub2013matrix], (2.4.3)). `Matrix.exists_wide_thin_svd` is
  the thin factorization of a wide matrix.
* `Matrix.IsSVD.norm_sq_toEuclideanLin_apply` ($\|Ax\|^2 = \sum_i \sigma_i^2 |(V^H x)_i|^2$) and
  `Matrix.IsSVD.norm_toEuclideanLin_eq_iff_mem_span`: for a tall matrix,
  $\|Ax\| = \sigma_{\min} \|x\|$ exactly on the span of the right singular vectors of the smallest
  singular value ([golub2013matrix], §6.3.2).

## Implementation notes

* `Matrix.colSingularValues` is indexed by the columns of $A$ and is not sorted, because Mathlib
  indexes `Matrix.IsHermitian.eigenvalues` this way, and because most uses need the value that
  belongs to a given right singular vector rather than the $j$-th largest one. Over the columns, the
  infimum and the supremum of the singular values are $\sigma_{\min}$ and $\sigma_{\max}$ for every
  shape. The prefix `col` marks this indexing.
* The sorted reading is Mathlib's `LinearMap.singularValues`, an $\mathbb{N}$-indexed sequence,
  written `A.sortedSingularValues i` where an index matters ($\sigma_k$, truncations, Eckart–Young).
  `Matrix.singularValues_eq_of_svd` and `Matrix.IsSVD.singularValues_eq` are about it.
* A matrix acts on Euclidean space through `Matrix.toEuclideanLin`, and its norm is the operator
  norm of the scope `Matrix.Norms.L2Operator`.
* The pseudoinverse uses $0^{-1} = 0$, so that no case split on the rank is needed.
* The coordinate-free facts about singular values are in
  `Numlib.Analysis.InnerProductSpace.SingularValues`. The singular value inequalities (Weyl, Mirsky,
  Eckart–Young) and the bound of Wedin on $\|B^+ - A^+\|_F$ are in
  `Numlib.Analysis.Matrix.SingularValues`, because the Frobenius norm needs
  `Numlib.Analysis.Matrix.OperatorNorm`, which imports this module. Tikhonov regularization, which
  [kress1998numerical] builds on the same singular system, is in
  `Numlib.LinearAlgebra.Matrix.LeastSquares.Regularized`.
-/

open Module

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### Singular values and right singular vectors -/

/-- Let $A \in \mathbb{K}^{m \times n}$. The **singular values** of $A$, indexed by the columns of
$A$, are
$$\sigma_i = \sqrt{\lambda_i(A^H A)}, \qquad i \in n,$$
where $\lambda_i(A^H A)$ is the eigenvalue of index $i$ of the positive semidefinite matrix
$A^H A$.

The eigenvalues are `Matrix.IsHermitian.eigenvalues`, listed with multiplicity but in no
particular order, and so are the singular values. The sorted sequence is
`Matrix.sortedSingularValues`, which is Mathlib's `LinearMap.singularValues`. -/
noncomputable def colSingularValues (A : Matrix m n 𝕜) (i : n) : ℝ :=
  Real.sqrt ((isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- Let $A \in \mathbb{K}^{m \times n}$. The **right singular vectors** of $A$ are an orthonormal
eigenbasis $(u_i)_{i \in n}$ of $A^H A$, with $A^H A u_i = \sigma_i^2 u_i$ for the singular
value $\sigma_i$ = `Matrix.colSingularValues A i` of the same index.

The basis is `Matrix.IsHermitian.eigenvectorBasis` of $A^H A$. -/
noncomputable def rightSingularBasis (A : Matrix m n 𝕜) :
    OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  (isHermitian_conjTranspose_mul_self A).eigenvectorBasis

variable (A : Matrix m n 𝕜)

/-- Every singular value `Matrix.colSingularValues A i` is nonnegative. -/
theorem colSingularValues_nonneg (i : n) : 0 ≤ A.colSingularValues i := Real.sqrt_nonneg _

/-- Let $A \in \mathbb{K}^{m \times n}$. For every column index $i$, the square of the singular
value $\sigma_i$ is the eigenvalue of the same index of $A^H A$:
$$\sigma_i^2 = \lambda_i(A^H A).$$
-/
theorem sq_colSingularValues (i : n) :
    A.colSingularValues i ^ 2 = (isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  Real.sq_sqrt (eigenvalues_conjTranspose_mul_self_nonneg A i)

/-- **An eigenvector of the Gram matrix gives a singular value.** Let
$A \in \mathbb{K}^{m \times n}$, let $g \in \mathbb{K}^n$ be nonzero and let $s \ge 0$. If
$A^H A g = s^2 g$, then $s = \sigma_i$ for some column index $i$. -/
theorem exists_colSingularValues_eq_of_mulVec {g : n → 𝕜} (hg : g ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    (h : (Aᴴ * A) *ᵥ g = ((s : 𝕜) ^ 2) • g) : ∃ i, A.colSingularValues i = s := by
  have hspec : ((s ^ 2 : ℝ) : 𝕜) ∈ spectrum 𝕜 (Aᴴ * A) := by
    rw [← Matrix.spectrum_toLin']
    apply Module.End.HasEigenvalue.mem_spectrum
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := g)
    refine ⟨Module.End.mem_eigenspace_iff.2 ?_, hg⟩
    rw [toLin'_apply, h, RCLike.ofReal_pow]
  rw [(isHermitian_conjTranspose_mul_self A).spectrum_eq_image_range] at hspec
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hspec
  have he : (isHermitian_conjTranspose_mul_self A).eigenvalues i = s ^ 2 :=
    RCLike.ofReal_injective hi
  refine ⟨i, (sq_eq_sq₀ (colSingularValues_nonneg _ _) hs).1 ?_⟩
  rw [sq_colSingularValues, he]

/-- Let $A \in \mathbb{K}^{m \times n}$. Every right singular vector $u_i$ is an eigenvector of
$A^H A$ for the squared singular value: $A^H A u_i = \sigma_i^2 u_i$. -/
theorem toEuclideanLin_conjTranspose_mul_self_rightSingularBasis (i : n) :
    toEuclideanLin (Aᴴ * A) (A.rightSingularBasis i)
      = ((A.colSingularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularBasis i := by
  have h := (isHermitian_conjTranspose_mul_self A).mulVec_eigenvectorBasis i
  rw [sq_colSingularValues]
  apply WithLp.ofLp_injective
  rw [WithLp.ofLp_smul, ← RCLike.real_smul_eq_coe_smul (K := 𝕜), toLpLin_apply, WithLp.ofLp_toLp]
  exact h

/-- Let $A \in \mathbb{K}^{m \times n}$. For $x, y \in \mathbb{K}^n$, $\langle Ax, Ay \rangle =
\langle x, A^H A y \rangle$. -/
theorem inner_toEuclideanLin_apply (x y : EuclideanSpace 𝕜 n) :
    (inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) : 𝕜)
      = inner 𝕜 x (toEuclideanLin (Aᴴ * A) y) := by
  classical
  rw [toLpLin_mul_same, LinearMap.comp_apply, toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

/-- Let $A \in \mathbb{K}^{m \times n}$ with right singular vectors $u_i$ and singular values
$\sigma_i$. **The images of the right singular vectors are pairwise orthogonal**, with the
squared singular values as squared norms:
$$\langle A u_i, A u_j \rangle = \begin{cases} \sigma_i^2 & \text{if } i = j, \\
  0 & \text{otherwise.} \end{cases}$$
This fact is the core of the singular value decomposition. -/
theorem inner_toEuclideanLin_rightSingularBasis (i j : n) :
    (inner 𝕜 (toEuclideanLin A (A.rightSingularBasis i))
        (toEuclideanLin A (A.rightSingularBasis j)) : 𝕜)
      = if i = j then ((A.colSingularValues i ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [inner_toEuclideanLin_apply, toEuclideanLin_conjTranspose_mul_self_rightSingularBasis,
    inner_smul_right, orthonormal_iff_ite.1 A.rightSingularBasis.orthonormal i j]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero]

/-- Let $A \in \mathbb{K}^{m \times n}$. The image of a right singular vector has the singular value
of the same index as its norm: $\|A u_i\| = \sigma_i$. -/
@[simp]
theorem norm_toEuclideanLin_rightSingularBasis (i : n) :
    ‖toEuclideanLin A (A.rightSingularBasis i)‖ = A.colSingularValues i := by
  have h : (inner 𝕜 (toEuclideanLin A (A.rightSingularBasis i))
      (toEuclideanLin A (A.rightSingularBasis i)) : 𝕜)
        = ((A.colSingularValues i ^ 2 : ℝ) : 𝕜) := by
    simpa using A.inner_toEuclideanLin_rightSingularBasis i i
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖toEuclideanLin A (A.rightSingularBasis i)‖ ^ 2 = A.colSingularValues i ^ 2 := by
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (A.colSingularValues_nonneg i) two_ne_zero).1 h2

/-- Let $A \in \mathbb{K}^{m \times n}$. If the singular value $\sigma_i$ is $0$, then the right
singular vector $u_i$ is in the kernel of $A$: $A u_i = 0$. -/
theorem toEuclideanLin_rightSingularBasis_eq_zero {i : n} (hi : A.colSingularValues i = 0) :
    toEuclideanLin A (A.rightSingularBasis i) = 0 := by
  rw [← norm_eq_zero, norm_toEuclideanLin_rightSingularBasis, hi]

/-- Let $A \in \mathbb{K}^{m \times n}$. For $x \in \mathbb{K}^n$,
$Ax = \sum_i \langle u_i, x \rangle A u_i$, where $(u_i)$ are the right singular vectors. -/
theorem toEuclideanLin_eq_sum_rightSingularBasis (x : EuclideanSpace 𝕜 n) :
    toEuclideanLin A x = ∑ i, (inner 𝕜 (A.rightSingularBasis i) x : 𝕜) •
      toEuclideanLin A (A.rightSingularBasis i) := by
  conv_lhs => rw [← A.rightSingularBasis.sum_repr' x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _

/-- **Parseval's identity for the singular values.** Let $A \in \mathbb{K}^{m \times n}$. For
$x \in \mathbb{K}^n$,
$$\|Ax\|^2 = \sum_i \sigma_i^2 \, |\langle u_i, x \rangle|^2,$$
where $(u_i)$ are the right singular vectors and $\sigma_i$ the singular values. -/
theorem norm_sq_toEuclideanLin_apply (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A x‖ ^ 2 =
      ∑ i, A.colSingularValues i ^ 2 * ‖(inner 𝕜 (A.rightSingularBasis i) x : 𝕜)‖ ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c : n → 𝕜, c = fun i => (inner 𝕜 (A.rightSingularBasis i) x : 𝕜) :=
    ⟨_, rfl⟩
  have hx : x = ∑ i, c i • A.rightSingularBasis i := by
    rw [hc]; exact (A.rightSingularBasis.sum_repr' x).symm
  have hHx : toEuclideanLin (Aᴴ * A) x
      = ∑ i, (c i * ((A.colSingularValues i ^ 2 : ℝ) : 𝕜)) • A.rightSingularBasis i := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, toEuclideanLin_conjTranspose_mul_self_rightSingularBasis, smul_smul]
  have key : (inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A x) : 𝕜)
      = ∑ i, ((A.colSingularValues i ^ 2 * ‖c i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [inner_toEuclideanLin_apply, hHx]
    conv_lhs => rw [hx]
    rw [A.rightSingularBasis.orthonormal.inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, RCLike.conj_mul]
    push_cast
    ring
  rw [inner_self_eq_norm_sq_to_K] at key
  have key2 : ((‖toEuclideanLin A x‖ ^ 2 : ℝ) : 𝕜)
      = ((∑ i, A.colSingularValues i ^ 2 * ‖c i‖ ^ 2 : ℝ) : 𝕜) := by
    push_cast
    push_cast at key
    exact key
  simp only [hc] at key2
  exact_mod_cast key2

/-! ### The singular system -/

open scoped ComplexOrder in
/-- Let $A \in \mathbb{K}^{m \times n}$. The number of column indices $i$ with $\sigma_i \neq 0$ is
the rank of $A$. -/
theorem card_colSingularValues_ne_zero :
    Fintype.card {i : n // A.colSingularValues i ≠ 0} = A.rank := by
  classical
  have h1 : (Aᴴ * A).rank = Fintype.card
      {i : n // (isHermitian_conjTranspose_mul_self A).eigenvalues i ≠ 0} :=
    (isHermitian_conjTranspose_mul_self A).rank_eq_card_non_zero_eigs
  have h2 : {i : n // A.colSingularValues i ≠ 0} ≃
      {i : n // (isHermitian_conjTranspose_mul_self A).eigenvalues i ≠ 0} :=
    Equiv.subtypeEquivRight fun i => by
      rw [← sq_colSingularValues, ne_eq, ne_eq, pow_eq_zero_iff two_ne_zero]
  rw [Fintype.card_congr h2, ← h1, rank_conjTranspose_mul_self]

/-- **The singular system of a matrix.** Let $A \in \mathbb{K}^{m \times n}$ and
$r = \operatorname{rank} A$. There are numbers $\mu_0, \dots, \mu_{r-1} > 0$, an orthonormal
family $u_0, \dots, u_{r-1}$ in $\mathbb{K}^n$ and an orthonormal family $v_0, \dots, v_{r-1}$
in $\mathbb{K}^m$ such that
$$A u_j = \mu_j v_j, \qquad A^H v_j = \mu_j u_j$$
for every $j$, and
$$Ax = \sum_{j < r} \mu_j \langle u_j, x \rangle v_j
  \qquad \text{for every } x \in \mathbb{K}^n.$$
This is Theorem 5.4 of [kress1998numerical].

The expansion says that $A$ acts diagonally between the two families, and it gives $Az = 0$ for
every $z$ orthogonal to all $u_j$. The families are indexed by `Fin A.rank` in no particular
order. They are built from `Matrix.colSingularValues` and `Matrix.rightSingularBasis`, which are
indexed by the columns of $A$. -/
theorem exists_singularSystem [DecidableEq m] :
    ∃ (μ : Fin A.rank → ℝ) (u : Fin A.rank → EuclideanSpace 𝕜 n)
      (v : Fin A.rank → EuclideanSpace 𝕜 m),
      (∀ j, 0 < μ j) ∧ Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      (∀ j, toEuclideanLin A (u j) = ((μ j : ℝ) : 𝕜) • v j) ∧
      (∀ j, toEuclideanLin Aᴴ (v j) = ((μ j : ℝ) : 𝕜) • u j) ∧
      (∀ x, toEuclideanLin A x = ∑ j, (((μ j : ℝ) : 𝕜) * inner 𝕜 (u j) x) • v j) := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin A.rank ≃ {i : n // A.colSingularValues i ≠ 0}) :=
    ⟨(Fintype.equivFinOfCardEq A.card_colSingularValues_ne_zero).symm⟩
  have hpos : ∀ j : Fin A.rank, 0 < A.colSingularValues (e j) := fun j =>
    lt_of_le_of_ne (A.colSingularValues_nonneg _) (Ne.symm (e j).2)
  have hne : ∀ j : Fin A.rank, ((A.colSingularValues (e j) : ℝ) : 𝕜) ≠ 0 := fun j => by
    simpa using (hpos j).ne'
  have hinj : Function.Injective fun j : Fin A.rank => ((e j : n)) :=
    Subtype.val_injective.comp e.injective
  refine ⟨fun j => A.colSingularValues (e j), fun j => A.rightSingularBasis (e j),
    fun j => ((A.colSingularValues (e j) : ℝ) : 𝕜)⁻¹ •
      toEuclideanLin A (A.rightSingularBasis (e j)), hpos, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Function.comp_def] using
      A.rightSingularBasis.orthonormal.comp (fun j : Fin A.rank => ((e j : n))) hinj
  · constructor
    · intro j
      rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos (hpos j),
        norm_toEuclideanLin_rightSingularBasis, inv_mul_cancel₀ (hpos j).ne']
    · intro i j hij
      have hne' : ((e i : n)) ≠ ((e j : n)) := fun h => hij (hinj h)
      rw [inner_smul_left, inner_smul_right, A.inner_toEuclideanLin_rightSingularBasis,
        ite_eq_right_of_eq_false _ _ (eq_false hne'), mul_zero, mul_zero]
  · intro j
    rw [smul_smul, mul_inv_cancel₀ (hne j), one_smul]
  · intro j
    rw [map_smul, ← toEuclideanLin_mul_apply,
      toEuclideanLin_conjTranspose_mul_self_rightSingularBasis, smul_smul]
    congr 1
    have h := hne j
    push_cast at h ⊢
    field_simp
  · intro x
    rw [toEuclideanLin_eq_sum_rightSingularBasis]
    have hz : ∀ i : n, i ∈ (Finset.univ : Finset n) →
        i ∉ Finset.univ.filter (fun i => A.colSingularValues i ≠ 0) →
        (inner 𝕜 (A.rightSingularBasis i) x : 𝕜) •
          toEuclideanLin A (A.rightSingularBasis i) = 0 := by
      intro i _ hi
      rw [A.toEuclideanLin_rightSingularBasis_eq_zero (by simpa using hi), smul_zero]
    rw [(Finset.sum_subset (Finset.filter_subset _ _) hz).symm,
      Finset.sum_subtype _ Finset.mem_filter_univ _, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [smul_smul]
    congr 1
    rw [mul_comm ((A.colSingularValues (e j) : ℝ) : 𝕜), mul_assoc,
      mul_inv_cancel₀ (hne j), mul_one]

/-! ### The Moore–Penrose pseudoinverse -/

section Pinv

open scoped ComplexOrder

/-- For every scalar $x$, $x^{-1} x x^{-1} = x^{-1}$, also at $x = 0$, where $0^{-1} = 0$. -/
private theorem inv_mul_mul_inv (x : 𝕜) : x⁻¹ * x * x⁻¹ = x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · rw [inv_mul_cancel₀ h, one_mul]

/-- Let $A \in \mathbb{K}^{m \times n}$. The **right singular unitary** of $A$ is the unitary matrix
$V \in \mathbb{K}^{n \times n}$ whose columns are the right singular vectors of $A$, that is,
the eigenvector matrix `Matrix.IsHermitian.eigenvectorUnitary` of $A^H A$. -/
noncomputable def rightSingularUnitary (A : Matrix m n 𝕜) : Matrix n n 𝕜 :=
  (isHermitian_conjTranspose_mul_self A).eigenvectorUnitary

/-- The right singular unitary `Matrix.rightSingularUnitary A` is a unitary matrix. -/
theorem rightSingularUnitary_mem_unitaryGroup : A.rightSingularUnitary ∈ unitaryGroup n 𝕜 :=
  ((isHermitian_conjTranspose_mul_self A).eigenvectorUnitary).2

/-- The right singular unitary $V$ = `Matrix.rightSingularUnitary A` satisfies $V^H V = I$. -/
theorem star_mul_rightSingularUnitary :
    star A.rightSingularUnitary * A.rightSingularUnitary = 1 :=
  mem_unitaryGroup_iff'.1 A.rightSingularUnitary_mem_unitaryGroup

/-- The right singular unitary $V$ = `Matrix.rightSingularUnitary A` satisfies $V V^H = I$. -/
theorem rightSingularUnitary_mul_star :
    A.rightSingularUnitary * star A.rightSingularUnitary = 1 :=
  mem_unitaryGroup_iff.1 A.rightSingularUnitary_mem_unitaryGroup

/-- The spectral decomposition of the Gram matrix: $A^H A = V \operatorname{diag}(\sigma_i^2) V^H$,
where $V$ is the right singular unitary `Matrix.rightSingularUnitary A` and $\sigma_i$ are the
singular values. -/
theorem conjTranspose_mul_self_eq_conj_diagonal :
    Aᴴ * A = A.rightSingularUnitary * diagonal (fun i => ((A.colSingularValues i ^ 2 : ℝ) : 𝕜))
      * star A.rightSingularUnitary := by
  conv_lhs => rw [(isHermitian_conjTranspose_mul_self A).spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  simp [rightSingularUnitary, Function.comp_def, sq_colSingularValues]

/-- Let $V$ be the right singular unitary `Matrix.rightSingularUnitary A`. For
$f, g : n \to \mathbb{K}$,
$$\bigl(V \operatorname{diag}(f) V^H\bigr) \bigl(V \operatorname{diag}(g) V^H\bigr)
  = V \operatorname{diag}(f g) V^H.$$
-/
theorem conj_diagonal_mul_conj_diagonal (f g : n → 𝕜) :
    (A.rightSingularUnitary * diagonal f * star A.rightSingularUnitary) *
        (A.rightSingularUnitary * diagonal g * star A.rightSingularUnitary)
      = A.rightSingularUnitary * diagonal (fun i => f i * g i)
        * star A.rightSingularUnitary := by
  have hd : diagonal f * diagonal g = diagonal (fun i => f i * g i) :=
    diagonal_mul_diagonal f g
  calc (A.rightSingularUnitary * diagonal f * star A.rightSingularUnitary) *
        (A.rightSingularUnitary * diagonal g * star A.rightSingularUnitary)
      = A.rightSingularUnitary * diagonal f *
          (star A.rightSingularUnitary * A.rightSingularUnitary) * diagonal g *
            star A.rightSingularUnitary := by noncomm_ring
    _ = A.rightSingularUnitary * (diagonal f * diagonal g) * star A.rightSingularUnitary := by
          rw [A.star_mul_rightSingularUnitary]; noncomm_ring
    _ = _ := by rw [hd]

/-- Let $A \in \mathbb{K}^{m \times n}$. The **Moore–Penrose pseudoinverse of the Gram matrix**
$A^H A$ is
$$(A^H A)^+ = V \operatorname{diag}(\sigma_i^{-2}) V^H,$$
where $V$ is the right singular unitary and $0^{-1} = 0$. It inverts the nonzero eigenvalues of
$A^H A$ and keeps the zero ones. `Matrix.pinv` is built from it. -/
noncomputable def gramPinv (A : Matrix m n 𝕜) : Matrix n n 𝕜 :=
  A.rightSingularUnitary * diagonal (fun i => ((A.colSingularValues i ^ 2 : ℝ) : 𝕜)⁻¹)
    * star A.rightSingularUnitary

/-- The pseudoinverse of the Gram matrix `Matrix.gramPinv A` is
$V \operatorname{diag}(\sigma_i^{-2}) V^H$, where $V$ is the right singular unitary
`Matrix.rightSingularUnitary A`. -/
theorem gramPinv_def : A.gramPinv = A.rightSingularUnitary *
    diagonal (fun i => ((A.colSingularValues i ^ 2 : ℝ) : 𝕜)⁻¹) * star A.rightSingularUnitary :=
  rfl

/-- The pseudoinverse $(A^H A)^+$ of the Gram matrix is Hermitian, because its eigenvalues
$\sigma_i^{-2}$ are real. -/
theorem isHermitian_gramPinv : A.gramPinv.IsHermitian := by
  have hf : (star fun i => (((A.colSingularValues i ^ 2 : ℝ) : 𝕜))⁻¹)
      = fun i => (((A.colSingularValues i ^ 2 : ℝ) : 𝕜))⁻¹ := by
    funext i
    rw [Pi.star_apply, star_inv₀, RCLike.star_def, RCLike.conj_ofReal]
  rw [Matrix.IsHermitian, gramPinv_def, star_eq_conjTranspose, conjTranspose_mul,
    conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, hf, Matrix.mul_assoc]

/-- The first Penrose condition for the Gram matrix: $A^H A \, (A^H A)^+ \, A^H A = A^H A$. -/
theorem gram_mul_gramPinv_mul_gram : Aᴴ * A * A.gramPinv * (Aᴴ * A) = Aᴴ * A := by
  rw [conjTranspose_mul_self_eq_conj_diagonal, gramPinv_def, conj_diagonal_mul_conj_diagonal,
    conj_diagonal_mul_conj_diagonal]
  congr 2
  exact congrArg diagonal (funext fun i => mul_inv_mul_cancel _)

/-- The second Penrose condition for the Gram matrix: $(A^H A)^+ \, A^H A \, (A^H A)^+ = (A^H A)^+$.
-/
theorem gramPinv_mul_gram_mul_gramPinv : A.gramPinv * (Aᴴ * A) * A.gramPinv = A.gramPinv := by
  rw [conjTranspose_mul_self_eq_conj_diagonal, gramPinv_def, conj_diagonal_mul_conj_diagonal,
    conj_diagonal_mul_conj_diagonal]
  congr 2
  exact congrArg diagonal (funext fun i => inv_mul_mul_inv _)

/-- The Gram matrix commutes with its pseudoinverse, $(A^H A)^+ A^H A = A^H A (A^H A)^+$, because
both are diagonal in the basis of right singular vectors. -/
theorem gramPinv_mul_gram_comm : A.gramPinv * (Aᴴ * A) = Aᴴ * A * A.gramPinv := by
  rw [conjTranspose_mul_self_eq_conj_diagonal, gramPinv_def, conj_diagonal_mul_conj_diagonal,
    conj_diagonal_mul_conj_diagonal]
  congr 2
  exact congrArg diagonal (funext fun i => mul_comm _ _)

/-- Let $A \in \mathbb{K}^{m \times n}$. The **Moore–Penrose pseudoinverse** of $A$ is
$$A^+ = (A^H A)^+ A^H \in \mathbb{K}^{n \times m},$$
where the pseudoinverse $(A^H A)^+$ = `Matrix.gramPinv A` of the Gram matrix inverts its nonzero
eigenvalues and keeps the zero ones.

The four Penrose conditions characterize $A^+$ (`Matrix.pinv_unique`). The vector $A^+ y$ is the
least-squares solution of $Ax = y$ of smallest norm
(`Matrix.norm_toEuclideanLin_pinv_sub_eq_iInf` and `Matrix.norm_pinv_le_of_normalEquations`). -/
noncomputable def pinv (A : Matrix m n 𝕜) : Matrix n m 𝕜 := A.gramPinv * Aᴴ

/-- The pseudoinverse is $A^+ = (A^H A)^+ A^H$, by definition. -/
theorem pinv_def : A.pinv = A.gramPinv * Aᴴ := rfl

omit [DecidableEq n] in
/-- Let $A \in \mathbb{K}^{m \times n}$ and $M \in \mathbb{K}^{n \times k}$. If $A^H A M = 0$, then
$AM = 0$, because then $(AM)^H (AM) = 0$. -/
theorem mul_eq_zero_of_conjTranspose_mul_self_mul_eq_zero {k : Type*}
    {M : Matrix n k 𝕜} (h : Aᴴ * A * M = 0) : A * M = 0 := by
  rw [← conjTranspose_mul_self_eq_zero (A := A * M), conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Aᴴ, h, Matrix.mul_zero]

/-- The first Penrose condition. For every $A \in \mathbb{K}^{m \times n}$,
$$A A^+ A = A.$$
-/
theorem mul_pinv_mul_self : A * A.pinv * A = A := by
  have key : A * (1 - A.gramPinv * (Aᴴ * A)) = 0 := by
    refine A.mul_eq_zero_of_conjTranspose_mul_self_mul_eq_zero ?_
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, gram_mul_gramPinv_mul_gram, sub_self]
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at key
  calc A * A.pinv * A = A * (A.gramPinv * (Aᴴ * A)) := by
        simp only [pinv_def, Matrix.mul_assoc]
    _ = A := key.symm

/-- The second Penrose condition. For every $A \in \mathbb{K}^{m \times n}$,
$$A^+ A A^+ = A^+.$$
-/
theorem pinv_mul_self_mul_pinv : A.pinv * A * A.pinv = A.pinv := by
  calc A.pinv * A * A.pinv = A.gramPinv * (Aᴴ * A) * A.gramPinv * Aᴴ := by
        simp only [pinv_def, Matrix.mul_assoc]
    _ = A.pinv := by rw [gramPinv_mul_gram_mul_gramPinv, pinv_def]

/-- The third Penrose condition: $A A^+$ is Hermitian. -/
theorem isHermitian_mul_pinv : (A * A.pinv).IsHermitian := by
  rw [Matrix.IsHermitian, pinv_def, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, A.isHermitian_gramPinv, Matrix.mul_assoc]

/-- The fourth Penrose condition: $A^+ A$ is Hermitian. -/
theorem isHermitian_pinv_mul : (A.pinv * A).IsHermitian := by
  have h : A.pinv * A = A.gramPinv * (Aᴴ * A) := by rw [pinv_def, Matrix.mul_assoc]
  rw [Matrix.IsHermitian, h, conjTranspose_mul, (isHermitian_conjTranspose_mul_self A).eq,
    A.isHermitian_gramPinv, ← gramPinv_mul_gram_comm]

/-- The pseudoinverse solves the normal equations: $A^H (A A^+) = A^H$. -/
theorem conjTranspose_mul_mul_pinv : Aᴴ * (A * A.pinv) = Aᴴ := by
  rw [← A.isHermitian_mul_pinv, ← conjTranspose_mul, mul_pinv_mul_self]

/-- **The Moore–Penrose pseudoinverse is the unique matrix that satisfies the four Penrose
conditions.** Let $A \in \mathbb{K}^{m \times n}$ and $B \in \mathbb{K}^{n \times m}$ satisfy
$$ABA = A, \qquad BAB = B, \qquad (AB)^H = AB, \qquad (BA)^H = BA.$$
Then $B = A^+$.

The four conditions give $BA = A^+ A$ and $AB = A A^+$, and then $B = BAB = A^+ A A^+ = A^+$. -/
theorem pinv_unique {B : Matrix n m 𝕜} (h1 : A * B * A = A) (h2 : B * A * B = B)
    (h3 : (A * B).IsHermitian) (h4 : (B * A).IsHermitian) : B = A.pinv := by
  have c1 : B * A = A.pinv * A := by
    calc B * A = (B * A)ᴴ := h4.symm
      _ = Aᴴ * Bᴴ := conjTranspose_mul _ _
      _ = (A * A.pinv * A)ᴴ * Bᴴ := by rw [mul_pinv_mul_self]
      _ = (A.pinv * A)ᴴ * (B * A)ᴴ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = A.pinv * A * (B * A) := by rw [A.isHermitian_pinv_mul, h4]
      _ = A.pinv * (A * B * A) := by simp only [Matrix.mul_assoc]
      _ = A.pinv * A := by rw [h1]
  have c2 : A * B = A * A.pinv := by
    calc A * B = (A * B)ᴴ := h3.symm
      _ = Bᴴ * Aᴴ := conjTranspose_mul _ _
      _ = Bᴴ * (A * A.pinv * A)ᴴ := by rw [mul_pinv_mul_self]
      _ = (A * B)ᴴ * (A * A.pinv)ᴴ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = A * B * (A * A.pinv) := by rw [h3, A.isHermitian_mul_pinv]
      _ = A * B * A * A.pinv := by simp only [Matrix.mul_assoc]
      _ = A * A.pinv := by rw [h1]
  calc B = B * A * B := h2.symm
    _ = A.pinv * A * B := by rw [c1]
    _ = A.pinv * (A * B) := by rw [Matrix.mul_assoc]
    _ = A.pinv * (A * A.pinv) := by rw [c2]
    _ = A.pinv * A * A.pinv := by rw [Matrix.mul_assoc]
    _ = A.pinv := pinv_mul_self_mul_pinv A

/-! ### Least-squares solutions -/

section LeastSquares

/-- A Hermitian matrix $M \in \mathbb{K}^{n \times n}$ is self-adjoint on Euclidean space:
$\langle Mu, z \rangle = \langle u, Mz \rangle$ for all $u, z \in \mathbb{K}^n$. -/
theorem inner_toEuclideanLin_of_isHermitian {M : Matrix n n 𝕜} (hM : M.IsHermitian)
    (u z : EuclideanSpace 𝕜 n) :
    (inner 𝕜 (toEuclideanLin M u) z : 𝕜) = inner 𝕜 u (toEuclideanLin M z) := by
  conv_lhs => rw [← hM]
  rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

variable [DecidableEq m]

/-- Let $A \in \mathbb{K}^{m \times n}$. The residual of the pseudoinverse solution is orthogonal to
the range of $A$: for $y \in \mathbb{K}^m$ and $w \in \mathbb{K}^n$,
$$\langle Aw, A A^+ y - y \rangle = 0.$$
-/
theorem inner_toEuclideanLin_sub_pinv (y : EuclideanSpace 𝕜 m) (w : EuclideanSpace 𝕜 n) :
    (inner 𝕜 (toEuclideanLin A w)
      (toEuclideanLin A (toEuclideanLin A.pinv y) - y) : 𝕜) = 0 := by
  have hmat : Aᴴ * A * A.pinv = Aᴴ := by
    rw [Matrix.mul_assoc, conjTranspose_mul_mul_pinv]
  have hres : toEuclideanLin Aᴴ (toEuclideanLin A (toEuclideanLin A.pinv y) - y) = 0 := by
    rw [map_sub, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, hmat, sub_self]
  rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint, hres,
    inner_zero_right]

/-- **$A^+ y$ is a least-squares solution.** Let $A \in \mathbb{K}^{m \times n}$. For
$y \in \mathbb{K}^m$ and every $x \in \mathbb{K}^n$, $\|A A^+ y - y\| \le \|Ax - y\|$. -/
theorem norm_toEuclideanLin_pinv_sub_le (y : EuclideanSpace 𝕜 m) (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A (toEuclideanLin A.pinv y) - y‖ ≤ ‖toEuclideanLin A x - y‖ := by
  have hsplit : toEuclideanLin A x - y
      = toEuclideanLin A (x - toEuclideanLin A.pinv y)
        + (toEuclideanLin A (toEuclideanLin A.pinv y) - y) := by
    rw [map_sub]
    abel
  have hpy : ‖toEuclideanLin A x - y‖ ^ 2
      = ‖toEuclideanLin A (x - toEuclideanLin A.pinv y)‖ ^ 2
        + ‖toEuclideanLin A (toEuclideanLin A.pinv y) - y‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (A.inner_toEuclideanLin_sub_pinv y _)
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  nlinarith [hpy, sq_nonneg ‖toEuclideanLin A (x - toEuclideanLin A.pinv y)‖]

/-- **The residual of the pseudoinverse solution is the least-squares minimum.** Let
$A \in \mathbb{K}^{m \times n}$. For every $y \in \mathbb{K}^m$,
$$\|A A^+ y - y\| = \inf_{x \in \mathbb{K}^n} \|Ax - y\|.$$
-/
theorem norm_toEuclideanLin_pinv_sub_eq_iInf (y : EuclideanSpace 𝕜 m) :
    ‖toEuclideanLin A (toEuclideanLin A.pinv y) - y‖
      = ⨅ x : EuclideanSpace 𝕜 n, ‖toEuclideanLin A x - y‖ := by
  refine le_antisymm (le_ciInf fun x => A.norm_toEuclideanLin_pinv_sub_le y x) ?_
  exact ciInf_le ⟨0, fun r hr => by obtain ⟨x, rfl⟩ := hr; exact norm_nonneg _⟩ _

/-- **Among the least-squares solutions, $A^+ y$ has the smallest norm.** Let
$A \in \mathbb{K}^{m \times n}$ and $y \in \mathbb{K}^m$, and let $x \in \mathbb{K}^n$ satisfy
the normal equations
$$A^H A x = A^H y.$$
Then $\|A^+ y\| \le \|x\|$.

The normal equations characterize the least-squares solutions. -/
theorem norm_pinv_le_of_normalEquations (y : EuclideanSpace 𝕜 m) {x : EuclideanSpace 𝕜 n}
    (hx : toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ y) :
    ‖toEuclideanLin A.pinv y‖ ≤ ‖x‖ := by
  have hmat : Aᴴ * A * A.pinv = Aᴴ := by
    rw [Matrix.mul_assoc, conjTranspose_mul_mul_pinv]
  have hp : toEuclideanLin (Aᴴ * A) (toEuclideanLin A.pinv y) = toEuclideanLin Aᴴ y := by
    rw [← toEuclideanLin_mul_apply, hmat]
  have hgram : toEuclideanLin (Aᴴ * A) (x - toEuclideanLin A.pinv y) = 0 := by
    rw [map_sub, hx, hp, sub_self]
  have hker : toEuclideanLin A (x - toEuclideanLin A.pinv y) = 0 := by
    have h := A.inner_toEuclideanLin_apply (x - toEuclideanLin A.pinv y)
      (x - toEuclideanLin A.pinv y)
    rw [hgram, inner_zero_right] at h
    exact inner_self_eq_zero.1 h
  have hperp : ∀ d : EuclideanSpace 𝕜 n, toEuclideanLin A d = 0 →
      (inner 𝕜 (toEuclideanLin A.pinv y) d : 𝕜) = 0 := by
    intro d hd
    have hpp : toEuclideanLin (A.pinv * A) (toEuclideanLin A.pinv y)
        = toEuclideanLin A.pinv y := by
      rw [← toEuclideanLin_mul_apply, pinv_mul_self_mul_pinv]
    rw [← hpp, inner_toEuclideanLin_of_isHermitian A.isHermitian_pinv_mul,
      toEuclideanLin_mul_apply, hd, map_zero, inner_zero_right]
  have hxeq : toEuclideanLin A.pinv y + (x - toEuclideanLin A.pinv y) = x := by abel
  have hsum : ‖x‖ ^ 2
      = ‖toEuclideanLin A.pinv y‖ ^ 2 + ‖x - toEuclideanLin A.pinv y‖ ^ 2 := by
    conv_lhs => rw [← hxeq]
    simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (hperp _ hker)
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  nlinarith [hsum, sq_nonneg ‖x - toEuclideanLin A.pinv y‖]

end LeastSquares

/-! ### The pseudoinverse of the adjoint, and the pseudoinverse as a projector -/

section Projector

/-- Let $A \in \mathbb{K}^{m \times n}$. Then $A^+ A$ is the identity on the range of $A^H$:
$$A^+ A A^H = A^H.$$
-/
theorem pinv_mul_self_mul_conjTranspose : A.pinv * A * Aᴴ = Aᴴ := by
  have h : (A.pinv * A * Aᴴ)ᴴ = (Aᴴ)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, A.isHermitian_pinv_mul.eq,
      ← Matrix.mul_assoc, mul_pinv_mul_self]
  exact conjTranspose_injective h

variable [DecidableEq m]

/-- **The pseudoinverse commutes with the conjugate transpose.** For every
$A \in \mathbb{K}^{m \times n}$,
$$(A^H)^+ = (A^+)^H.$$

The Penrose conditions for $A$ and $A^+$, conjugate-transposed, are those for $A^H$ and
$(A^+)^H$. -/
theorem pinv_conjTranspose : Aᴴ.pinv = A.pinvᴴ := by
  symm
  refine pinv_unique Aᴴ ?_ ?_ ?_ ?_
  · rw [← conjTranspose_mul, ← conjTranspose_mul, ← Matrix.mul_assoc, mul_pinv_mul_self]
  · rw [← conjTranspose_mul, ← conjTranspose_mul, ← Matrix.mul_assoc, pinv_mul_self_mul_pinv]
  · rw [IsHermitian, ← conjTranspose_mul, conjTranspose_conjTranspose,
      A.isHermitian_pinv_mul.eq]
  · rw [IsHermitian, ← conjTranspose_mul, conjTranspose_conjTranspose,
      A.isHermitian_mul_pinv.eq]

/-- **$A A^+$ is the orthogonal projection onto the range of $A$.** Let
$A \in \mathbb{K}^{m \times n}$. The linear map $y \mapsto A A^+ y$ on $\mathbb{K}^m$ is the
orthogonal projection onto the range of $x \mapsto Ax$. This is [golub2013matrix], §5.5.2, where
it is written $A A^+ = U_1 U_1^H$.

The values of $A A^+$ lie in the range, and the residual $y - A A^+ y$ is orthogonal to the
range because $A^H A A^+ = A^H$. The projection is `Submodule.starProjection`. -/
theorem mul_pinv_eq_starProjection :
    toEuclideanLin (A * A.pinv) = ((LinearMap.range (toEuclideanLin A)).starProjection :
      EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 m) := by
  ext1 x
  rw [ContinuousLinearMap.coe_coe]
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [toEuclideanLin_mul_apply]
    exact LinearMap.mem_range_self _ _
  · rintro _ ⟨y, rfl⟩
    rw [← inner_conj_symm, ← toEuclideanLin_conjTranspose_inner_right, map_sub,
      ← toEuclideanLin_mul_apply, conjTranspose_mul_mul_pinv, sub_self, inner_zero_right,
      map_zero]

omit [DecidableEq m] in
/-- The orthogonal range projector of $A$ fixes $C$ exactly when every column of $C$
lies in the range of $A$. -/
theorem range_toEuclideanLin_le_iff_mul_pinv_mul_eq {p : Type*} [Fintype p] [DecidableEq p]
    (C : Matrix m p 𝕜) :
    (toEuclideanLin C).range ≤ (toEuclideanLin A).range ↔ A * A.pinv * C = C := by
  classical
  constructor
  · intro h
    apply toEuclideanLin.injective
    ext1 z
    rw [toEuclideanLin_mul_apply, A.mul_pinv_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr (h ⟨z, rfl⟩)
  · rintro h x ⟨z, rfl⟩
    have f := congrArg (fun M => toEuclideanLin M z) h
    rw [toEuclideanLin_mul_apply, A.mul_pinv_eq_starProjection] at f
    exact Submodule.starProjection_eq_self_iff.mp f

/-- **$A^+ A$ is the orthogonal projection onto the range of $A^H$.** Let
$A \in \mathbb{K}^{m \times n}$. The linear map $x \mapsto A^+ A x$ on $\mathbb{K}^n$ is the
orthogonal projection onto the range of $y \mapsto A^H y$. This is [golub2013matrix], §5.5.2,
where it is written $A^+ A = V_1 V_1^H$.

It is `Matrix.mul_pinv_eq_starProjection` for $A^H$, because $A^+ A = (A^+ A)^H = A^H (A^H)^+$. -/
theorem pinv_mul_eq_starProjection :
    toEuclideanLin (A.pinv * A) = ((LinearMap.range (toEuclideanLin Aᴴ)).starProjection :
      EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n) := by
  rw [← mul_pinv_eq_starProjection, pinv_conjTranspose, ← conjTranspose_mul,
    A.isHermitian_pinv_mul.eq]

end Projector

end Pinv

/-! ### The spectral condition number -/

section CondNumber

open scoped Matrix.Norms.L2Operator

/-- Parseval's identity in the basis of right singular vectors:
$\sum_i |\langle u_i, x \rangle|^2 = \|x\|^2$ for $x \in \mathbb{K}^n$. -/
theorem sum_norm_inner_rightSingularBasis_sq (x : EuclideanSpace 𝕜 n) :
    ∑ i, ‖(inner 𝕜 (A.rightSingularBasis i) x : 𝕜)‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq (A.rightSingularBasis.repr x)
  rw [A.rightSingularBasis.repr.norm_map] at h
  simp only [OrthonormalBasis.repr_apply_apply] at h
  exact h.symm

variable [Nonempty n]

/-- Let $A \in \mathbb{K}^{m \times n}$ with $n \ge 1$. The largest singular value bounds $A$ as an
operator: for every $x \in \mathbb{K}^n$,
$$\|Ax\| \le \bigl(\max_i \sigma_i\bigr) \|x\|.$$
-/
theorem norm_toEuclideanLin_le_iSup_colSingularValues (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A x‖ ≤ (⨆ i, A.colSingularValues i) * ‖x‖ := by
  have hbdd : BddAbove (Set.range A.colSingularValues) := (Set.finite_range _).bddAbove
  have hle : ∀ i, A.colSingularValues i ≤ ⨆ j, A.colSingularValues j := fun i => le_ciSup hbdd i
  have hnn : 0 ≤ ⨆ j, A.colSingularValues j :=
    le_trans (A.colSingularValues_nonneg (Classical.arbitrary n)) (hle _)
  refine le_of_sq_le_sq ?_ (mul_nonneg hnn (norm_nonneg _))
  rw [A.norm_sq_toEuclideanLin_apply, mul_pow, ← A.sum_norm_inner_rightSingularBasis_sq x,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (A.colSingularValues_nonneg i) (hle i) 2) (sq_nonneg _)

/-- Let $A \in \mathbb{K}^{m \times n}$ with $n \ge 1$. The smallest singular value bounds $A$ from
below: $(\min_i \sigma_i) \|x\| \le \|Ax\|$ for every $x \in \mathbb{K}^n$. -/
theorem iInf_colSingularValues_mul_norm_le (x : EuclideanSpace 𝕜 n) :
    (⨅ i, A.colSingularValues i) * ‖x‖ ≤ ‖toEuclideanLin A x‖ := by
  have hbdd : BddBelow (Set.range A.colSingularValues) := (Set.finite_range _).bddBelow
  have hge : ∀ i, (⨅ j, A.colSingularValues j) ≤ A.colSingularValues i := fun i => ciInf_le hbdd i
  have hnn : 0 ≤ ⨅ j, A.colSingularValues j := le_ciInf fun i => A.colSingularValues_nonneg i
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [A.norm_sq_toEuclideanLin_apply, mul_pow, ← A.sum_norm_inner_rightSingularBasis_sq x,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hnn (hge i) 2) (sq_nonneg _)

/-- Let $A \in \mathbb{K}^{m \times n}$ with $n \ge 1$. **The operator 2-norm of $A$ is its largest
singular value:**
$$\|A\|_2 = \max_i \sigma_i.$$
This holds for rectangular matrices as well as square ones.

The norm is the operator norm induced by the Euclidean norms, from the scope
`Matrix.Norms.L2Operator`. -/
theorem l2_opNorm_eq_iSup_colSingularValues : ‖A‖ = ⨆ i, A.colSingularValues i := by
  have hbdd : BddAbove (Set.range A.colSingularValues) := (Set.finite_range _).bddAbove
  have hnn : 0 ≤ ⨆ j, A.colSingularValues j :=
    le_trans (A.colSingularValues_nonneg (Classical.arbitrary n)) (le_ciSup hbdd _)
  rw [l2_opNorm_def, LinearEquiv.trans_apply]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ hnn fun x =>
    A.norm_toEuclideanLin_le_iSup_colSingularValues x) (ciSup_le fun i => ?_)
  calc A.colSingularValues i = ‖toEuclideanLin A (A.rightSingularBasis i)‖ :=
        (A.norm_toEuclideanLin_rightSingularBasis i).symm
    _ ≤ ‖LinearMap.toContinuousLinearMap (toEuclideanLin A)‖ * ‖A.rightSingularBasis i‖ := by
        simpa using ContinuousLinearMap.le_opNorm
          (LinearMap.toContinuousLinearMap (toEuclideanLin A)) (A.rightSingularBasis i)
    _ = ‖LinearMap.toContinuousLinearMap (toEuclideanLin A)‖ := by
        rw [A.rightSingularBasis.orthonormal.1 i, mul_one]

variable (B : Matrix n n 𝕜)

omit [Nonempty n] in
/-- Let $B \in \mathbb{K}^{n \times n}$ have invertible determinant. Then every singular value of
$B$ is positive. -/
theorem colSingularValues_pos (hB : IsUnit B.det) (i : n) : 0 < B.colSingularValues i := by
  refine lt_of_le_of_ne (B.colSingularValues_nonneg i) (Ne.symm fun h => ?_)
  have h0 : toEuclideanLin B (B.rightSingularBasis i) = 0 :=
    B.toEuclideanLin_rightSingularBasis_eq_zero h
  have hinv : toEuclideanLin B⁻¹ (toEuclideanLin B (B.rightSingularBasis i))
      = B.rightSingularBasis i := by
    rw [← toEuclideanLin_mul_apply, Matrix.nonsing_inv_mul B hB, toLpLin_one, LinearMap.id_apply]
  rw [h0, map_zero] at hinv
  have hone := B.rightSingularBasis.orthonormal.1 i
  rw [← hinv, norm_zero] at hone
  exact zero_ne_one hone

/-- **A positive least singular value makes a square matrix invertible.** Let
$B \in \mathbb{K}^{n \times n}$ with $n \ge 1$. If $\min_i \sigma_i(B) > 0$, then $B$ is
invertible.

This is the converse of `Matrix.colSingularValues_pos`. The bound
$\sigma_{\min} \|x\| \le \|Bx\|$ makes $x \mapsto Bx$ injective. -/
theorem isUnit_of_iInf_colSingularValues_pos (h : 0 < ⨅ i, B.colSingularValues i) : IsUnit B := by
  rw [← mulVec_injective_iff_isUnit]
  intro v w hvw
  have h1 := B.iInf_colSingularValues_mul_norm_le (WithLp.toLp 2 (v - w))
  rw [toEuclideanLin_toLp, mulVec_sub, hvw, sub_self, WithLp.toLp_zero, norm_zero] at h1
  have h2 : ‖(WithLp.toLp 2 (v - w) : EuclideanSpace 𝕜 n)‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h1 h) (norm_nonneg _)
  have h3 := congrArg WithLp.ofLp (norm_eq_zero.1 h2)
  simpa [sub_eq_zero] using h3

/-- **The norm of the inverse is the reciprocal of the smallest singular value.** Let
$B \in \mathbb{K}^{n \times n}$ with $n \ge 1$ have invertible determinant. Then
$$\|B^{-1}\|_2 = \frac{1}{\min_i \sigma_i(B)}.$$
-/
theorem l2_opNorm_inv_eq_inv_iInf_colSingularValues (hB : IsUnit B.det) :
    ‖B⁻¹‖ = (⨅ i, B.colSingularValues i)⁻¹ := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min B.colSingularValues
  have hbdd : BddBelow (Set.range B.colSingularValues) := (Set.finite_range _).bddBelow
  have hinf : (⨅ i, B.colSingularValues i) = B.colSingularValues i₀ :=
    le_antisymm (ciInf_le hbdd i₀) (le_ciInf hi₀)
  have hpos : 0 < B.colSingularValues i₀ := B.colSingularValues_pos hB i₀
  rw [hinf, l2_opNorm_eq_norm_toEuclideanLin]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_) ?_
  · have hz : toEuclideanLin B (toEuclideanLin B⁻¹ z) = z := by
      rw [← toEuclideanLin_mul_apply, Matrix.mul_nonsing_inv B hB, toLpLin_one, LinearMap.id_apply]
    have h1 := B.iInf_colSingularValues_mul_norm_le (toEuclideanLin B⁻¹ z)
    rw [hinf, hz] at h1
    rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact h1
  · have hy : toEuclideanLin B⁻¹ (toEuclideanLin B (B.rightSingularBasis i₀))
        = B.rightSingularBasis i₀ := by
      rw [← toEuclideanLin_mul_apply, Matrix.nonsing_inv_mul B hB, toLpLin_one, LinearMap.id_apply]
    have h2 := ContinuousLinearMap.le_opNorm
      (LinearMap.toContinuousLinearMap (toEuclideanLin B⁻¹))
      (toEuclideanLin B (B.rightSingularBasis i₀))
    simp only [LinearMap.coe_toContinuousLinearMap'] at h2
    rw [hy, B.rightSingularBasis.orthonormal.1 i₀,
      B.norm_toEuclideanLin_rightSingularBasis i₀] at h2
    refine le_of_mul_le_mul_right ?_ hpos
    rw [inv_mul_cancel₀ hpos.ne']
    exact h2

/-- **The spectral condition number is the ratio of the extreme singular values.** Let
$B \in \mathbb{K}^{n \times n}$ with $n \ge 1$ have invertible determinant. Then
$$\kappa_2(B) = \|B\|_2 \, \|B^{-1}\|_2 = \frac{\max_i \sigma_i(B)}{\min_i \sigma_i(B)}.$$

The condition number is `NormedRing.condNumber` for the operator 2-norm of the scope
`Matrix.Norms.L2Operator`. -/
theorem condNumber_l2_eq_div_colSingularValues (hB : IsUnit B.det) :
    NormedRing.condNumber B = (⨆ i, B.colSingularValues i) / (⨅ i, B.colSingularValues i) := by
  rw [NormedRing.condNumber, ← Matrix.nonsing_inv_eq_ringInverse,
    l2_opNorm_eq_iSup_colSingularValues, l2_opNorm_inv_eq_inv_iInf_colSingularValues B hB,
    div_eq_mul_inv]

end CondNumber

/-! ### Sorted singular values, and the least singular value -/

section Sorted

/-- Let $A \in \mathbb{K}^{m \times n}$. The **sorted singular values**
$\sigma_0 \ge \sigma_1 \ge \dots \ge 0$ of $A$ are the singular values of the operator
$x \mapsto Ax$ on Euclidean space, in nonincreasing order and with multiplicity, indexed by
$\mathbb{N}$ from $0$. They are $0$ from the index $\operatorname{rank} A$ on.

The definition is Mathlib's `LinearMap.singularValues` of `Matrix.toEuclideanLin A`. The
singular value $\sigma_{i+1}(A)$ of [golub2013matrix], §2.4.1, is `A.sortedSingularValues i`.
The definition is an abbreviation, so that statements about `Matrix.toEuclideanLin A` and about
this function agree by `rfl`. It exists for dot notation, beside the column-indexed
`Matrix.colSingularValues`. -/
noncomputable abbrev sortedSingularValues (i : ℕ) : ℝ :=
  (toEuclideanLin A).singularValues i

/-- Let $A \in \mathbb{K}^{m \times n}$. Every sorted singular value is nonnegative:
$\sigma_i \ge 0$ for all $i \in \mathbb{N}$. -/
theorem sortedSingularValues_nonneg (i : ℕ) : 0 ≤ A.sortedSingularValues i :=
  (toEuclideanLin A).singularValues_nonneg i

/-- Let $A \in \mathbb{K}^{m \times n}$. The sorted singular values are nonincreasing:
$\sigma_j \le \sigma_i$ for all $i \le j$. -/
theorem sortedSingularValues_antitone : Antitone A.sortedSingularValues :=
  (toEuclideanLin A).singularValues_antitone

/-- **The column-indexed and the sorted singular values are the same multiset.** Let
$A \in \mathbb{K}^{m \times n}$ and let $N$ be the number of columns. There is a bijection
$e : \{0, \dots, N - 1\} \to n$ such that, for every $k$, the column-indexed singular value of
index $e(k)$ is the sorted singular value $\sigma_k$.

Both are square roots of the eigenvalues of $A^H A$, which is the composition of the adjoint of
`Matrix.toEuclideanLin A` with `Matrix.toEuclideanLin A`. Mathlib's
`Matrix.IsHermitian.eigenvalues` is by definition the sorted list reindexed along
`Fintype.equivOfCardEq`. -/
theorem exists_equiv_colSingularValues_eq_sortedSingularValues :
    ∃ e : Fin (Fintype.card n) ≃ n, ∀ k, A.colSingularValues (e k) = A.sortedSingularValues k := by
  classical
  refine ⟨Fintype.equivOfCardEq (Fintype.card_fin _), fun k => ?_⟩
  set T : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m := toEuclideanLin A with hT
  have hn : finrank 𝕜 (EuclideanSpace 𝕜 n) = Fintype.card n := finrank_euclideanSpace
  have hTT : LinearMap.adjoint T ∘ₗ T = toEuclideanLin (Aᴴ * A) := by
    rw [toEuclideanLin_mul, toEuclideanLin_conjTranspose_eq_adjoint]
  have heig : T.isSymmetric_adjoint_comp_self.eigenvalues hn
      = (isHermitian_conjTranspose_mul_self A).eigenvalues₀ := by
    rw [IsHermitian.eigenvalues₀, T.isSymmetric_adjoint_comp_self.eigenvalues_eq_eigenvalues_iff]
    rw [hTT]
  rw [sortedSingularValues, T.singularValues_fin hn k, colSingularValues, heig]
  simp [IsHermitian.eigenvalues]

/-- **The number of positive singular values is the rank.** Let $A \in \mathbb{K}^{m \times n}$. For
every $k \in \mathbb{N}$,
$$\sigma_k(A) = 0 \iff \operatorname{rank} A \le k.$$
This is Corollary 2.4.6 of [golub2013matrix]. -/
theorem sortedSingularValues_eq_zero_iff_rank_le (k : ℕ) :
    A.sortedSingularValues k = 0 ↔ A.rank ≤ k := by
  classical
  rw [sortedSingularValues, LinearMap.singularValues_eq_zero_iff_le_finrank_range,
    rank_eq_finrank_range_toLin A (EuclideanSpace.basisFun m 𝕜).toBasis
      (EuclideanSpace.basisFun n 𝕜).toBasis, ← toEuclideanLin_eq_toLin_orthonormal]

open scoped Matrix.Norms.L2Operator in
/-- **The largest singular value is the 2-norm.** For every $A \in \mathbb{K}^{m \times n}$,
$$\sigma_0(A) = \|A\|_2.$$
This is Corollary 2.4.3 of [golub2013matrix], where the largest singular value is $\sigma_1$.

The statement holds for every shape. When $A$ has no columns, both sides are $0$. The norm is
the operator norm of the scope `Matrix.Norms.L2Operator`. -/
theorem sortedSingularValues_zero_eq_l2_opNorm : A.sortedSingularValues 0 = ‖A‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hA : A = 0 := by ext i j; exact isEmptyElim j
    subst hA
    simp [sortedSingularValues]
  · obtain ⟨e, he⟩ := A.exists_equiv_colSingularValues_eq_sortedSingularValues
    have hpos : 0 < Fintype.card n := Fintype.card_pos
    rw [l2_opNorm_eq_iSup_colSingularValues]
    refine le_antisymm ?_ (ciSup_le fun i => ?_)
    · rw [← he ⟨0, hpos⟩]
      exact le_ciSup (Set.finite_range _).bddAbove _
    · rw [← e.apply_symm_apply i, he]
      exact A.sortedSingularValues_antitone (Nat.zero_le _)

/-- Let $A \in \mathbb{K}^{m \times n}$ with $N \ge 1$ columns. **The last sorted singular value is
the least column-indexed one:**
$$\sigma_{N-1}(A) = \min_i \sigma_i(A),$$
where the right-hand side is over the column-indexed singular values. This holds for every
shape; for a wide matrix both sides are $0$. -/
theorem sortedSingularValues_eq_iInf_colSingularValues [Nonempty n] :
    A.sortedSingularValues (Fintype.card n - 1) = ⨅ i, A.colSingularValues i := by
  obtain ⟨e, he⟩ := A.exists_equiv_colSingularValues_eq_sortedSingularValues
  have hpos : 0 < Fintype.card n := Fintype.card_pos
  refine le_antisymm (le_ciInf fun i => ?_) ?_
  · rw [← e.apply_symm_apply i, he]
    exact A.sortedSingularValues_antitone (Nat.le_sub_one_of_lt (e.symm i).isLt)
  · rw [← he ⟨Fintype.card n - 1, Nat.sub_lt hpos one_pos⟩]
    exact ciInf_le (Set.finite_range _).bddBelow _

/-- **The least singular value is the least stretch.** For every $A \in \mathbb{K}^{m \times n}$,
$$\min_i \sigma_i(A) = \inf_{\|x\| = 1} \|Ax\|,$$
where the left-hand side is over the column-indexed singular values. This is in
[golub2013matrix], §2.4.

The statement holds for every shape. When $A$ has no columns, both sides are $0$, the infimum of
the empty set in `ℝ`. The column-indexed singular values are used on purpose: over the columns,
the infimum is $\sigma_{\min}$ without a sorted index. The sorted form is
`Matrix.sortedSingularValues_eq_iInf_colSingularValues`. -/
theorem iInf_colSingularValues_eq_iInf_norm :
    ⨅ i, A.colSingularValues i
      = ⨅ x : {x : EuclideanSpace 𝕜 n // ‖x‖ = 1}, ‖toEuclideanLin A x‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : IsEmpty {x : EuclideanSpace 𝕜 n // ‖x‖ = 1} := ⟨fun x => by
      have h0 : (x : EuclideanSpace 𝕜 n) = 0 := by ext i; exact isEmptyElim i
      have := x.2
      rw [h0, norm_zero] at this
      exact zero_ne_one this⟩
    rw [Real.iInf_of_isEmpty, Real.iInf_of_isEmpty]
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min A.colSingularValues
    have hinf : ⨅ i, A.colSingularValues i = A.colSingularValues i₀ :=
      le_antisymm (ciInf_le (Set.finite_range _).bddBelow i₀) (le_ciInf hi₀)
    have hne : Nonempty {x : EuclideanSpace 𝕜 n // ‖x‖ = 1} :=
      ⟨⟨A.rightSingularBasis i₀, A.rightSingularBasis.orthonormal.1 i₀⟩⟩
    refine le_antisymm (le_ciInf fun x => ?_) ?_
    · simpa [x.2] using A.iInf_colSingularValues_mul_norm_le x
    · rw [hinf, ← A.norm_toEuclideanLin_rightSingularBasis i₀]
      have hbdd : BddBelow (Set.range fun x : {x : EuclideanSpace 𝕜 n // ‖x‖ = 1} =>
          ‖toEuclideanLin A x‖) := ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
      exact ciInf_le hbdd ⟨A.rightSingularBasis i₀, A.rightSingularBasis.orthonormal.1 i₀⟩

/-- **The least singular value is attained.** Let $A \in \mathbb{K}^{m \times n}$ with $n \ge 1$.
There is $x \in \mathbb{K}^n$ with $\|x\| = 1$ and
$$\|Ax\| = \min_i \sigma_i(A).$$

The vector is a right singular vector of a least singular value. The singular values are
column-indexed, as in `Matrix.iInf_colSingularValues_eq_iInf_norm`. -/
theorem exists_norm_eq_iInf_colSingularValues [Nonempty n] :
    ∃ x : EuclideanSpace 𝕜 n, ‖x‖ = 1 ∧ ‖toEuclideanLin A x‖ = ⨅ i, A.colSingularValues i := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min A.colSingularValues
  refine ⟨A.rightSingularBasis i₀, A.rightSingularBasis.orthonormal.1 i₀, ?_⟩
  rw [norm_toEuclideanLin_rightSingularBasis]
  exact le_antisymm (le_ciInf hi₀) (ciInf_le (Set.finite_range _).bddBelow i₀)

/-- **A positive least singular value makes the columns independent.** Let
$A \in \mathbb{K}^{m \times n}$. If $\min_i \sigma_i(A) > 0$, then the columns of $A$ are
linearly independent, that is, $Ax = 0$ implies $x = 0$.

The columns of $A$ are the rows of `Aᵀ`. -/
theorem linearIndependent_transpose_of_iInf_colSingularValues_pos {A : Matrix m n 𝕜}
    (h : 0 < ⨅ i, A.colSingularValues i) : LinearIndependent 𝕜 Aᵀ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Real.iInf_of_isEmpty] at h
    exact absurd h (lt_irrefl 0)
  refine mulVec_injective_iff.1 fun v w hvw => ?_
  have h1 := A.iInf_colSingularValues_mul_norm_le (WithLp.toLp 2 (v - w))
  rw [toEuclideanLin_toLp, mulVec_sub, hvw, sub_self, WithLp.toLp_zero, norm_zero] at h1
  have h2 : ‖(WithLp.toLp 2 (v - w) : EuclideanSpace 𝕜 n)‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h1 h) (norm_nonneg _)
  have h3 := congrArg WithLp.ofLp (norm_eq_zero.1 h2)
  simpa [sub_eq_zero] using h3

/-- **Linearly independent columns give a positive least singular value.** Let
$A \in \mathbb{K}^{m \times n}$ with $n \ge 1$. If the columns of $A$ are linearly independent,
then $\min_i \sigma_i(A) > 0$.

This is the converse of `Matrix.linearIndependent_transpose_of_iInf_colSingularValues_pos`. -/
theorem iInf_colSingularValues_pos_of_linearIndependent [Nonempty n] {A : Matrix m n 𝕜}
    (hA : LinearIndependent 𝕜 Aᵀ) : 0 < ⨅ i, A.colSingularValues i := by
  obtain ⟨x, hx1, hx⟩ := A.exists_norm_eq_iInf_colSingularValues
  rw [← hx]
  refine norm_pos_iff.2 fun h0 => ?_
  have h1 : A *ᵥ WithLp.ofLp x = A *ᵥ 0 := by
    rw [mulVec_zero]
    exact congrArg WithLp.ofLp h0
  have h2 := mulVec_injective_iff.2 hA h1
  have hx0 : x = 0 := by
    ext i
    simpa using congrFun h2 i
  rw [hx0, norm_zero] at hx1
  exact zero_ne_one hx1

/-- **The least singular value is unitarily invariant.** Let $A \in \mathbb{K}^{m \times n}$, and
let $U \in \mathbb{K}^{m \times m}$ and $V \in \mathbb{K}^{n \times n}$ be unitary. Then
$$\min_i \sigma_i(UAV) = \min_i \sigma_i(A).$$
This is in [golub2013matrix], §7.9.5.

The matrix $V$ permutes the unit sphere and $U$ is an isometry. The singular values are
column-indexed, as in `Matrix.iInf_colSingularValues_eq_iInf_norm`. -/
theorem iInf_colSingularValues_unitary_mul_mul [DecidableEq m] {U : Matrix m m 𝕜}
    {V : Matrix n n 𝕜} (hU : U ∈ unitaryGroup m 𝕜) (hV : V ∈ unitaryGroup n 𝕜) :
    ⨅ i, (U * A * V).colSingularValues i = ⨅ i, A.colSingularValues i := by
  rw [iInf_colSingularValues_eq_iInf_norm, iInf_colSingularValues_eq_iInf_norm]
  let e : {x : EuclideanSpace 𝕜 n // ‖x‖ = 1} ≃ {x : EuclideanSpace 𝕜 n // ‖x‖ = 1} :=
    (unitaryLinearIsometryEquiv hV).toEquiv.subtypeEquiv fun x => by simp
  conv_rhs => rw [← e.iInf_comp]
  refine congrArg _ (funext fun x => ?_)
  simp only [e, Equiv.subtypeEquiv_apply]
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    norm_toEuclideanLin_apply_of_mem_unitaryGroup hU]
  rfl

/-- **The sorted singular values are unitarily invariant.** Let $A \in \mathbb{K}^{m \times n}$, and
let $U$ and $V$ be unitary. Then $\sigma_k(UAV) = \sigma_k(A)$ for every $k$. This is the matrix
form of `LinearMap.singularValues_comp_linearIsometryEquiv`. -/
theorem sortedSingularValues_unitary_mul_mul [DecidableEq m] {U : Matrix m m 𝕜}
    {V : Matrix n n 𝕜} (hU : U ∈ unitaryGroup m 𝕜) (hV : V ∈ unitaryGroup n 𝕜) :
    (U * A * V).sortedSingularValues = A.sortedSingularValues := by
  have key : toEuclideanLin (U * A * V) =
      (unitaryLinearIsometryEquiv hU).toLinearIsometry.toLinearMap ∘ₗ toEuclideanLin A ∘ₗ
        (unitaryLinearIsometryEquiv hV).toLinearIsometry.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    simp only [toEuclideanLin_mul_apply, LinearMap.comp_apply]
    rfl
  funext i
  change (toEuclideanLin (U * A * V)).singularValues i = (toEuclideanLin A).singularValues i
  rw [key, LinearMap.singularValues_comp_linearIsometryEquiv]

/-- A unitary factor on the left does not change the sorted singular values:
$\sigma_k(UA) = \sigma_k(A)$ for unitary $U$. -/
theorem sortedSingularValues_unitary_mul [DecidableEq m] {U : Matrix m m 𝕜}
    (hU : U ∈ unitaryGroup m 𝕜) : (U * A).sortedSingularValues = A.sortedSingularValues := by
  simpa using A.sortedSingularValues_unitary_mul_mul hU (one_mem (unitaryGroup n 𝕜))

/-- A unitary factor on the right does not change the sorted singular values:
$\sigma_k(AV) = \sigma_k(A)$ for unitary $V$. -/
theorem sortedSingularValues_mul_unitary {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) :
    (A * V).sortedSingularValues = A.sortedSingularValues := by
  classical
  simpa using A.sortedSingularValues_unitary_mul_mul (one_mem (unitaryGroup m 𝕜)) hV

end Sorted

end Matrix

namespace Matrix

/-! ### The rectangular diagonal matrix -/

section RectDiagonal

variable {l m n : ℕ}

section Zero

variable {α : Type*} [Zero α]

/-- Let $\sigma : \mathbb{N} \to \alpha$. The **rectangular diagonal matrix**
$\operatorname{diag}(\sigma_0, \sigma_1, \dots) \in \alpha^{m \times n}$ has the entry
$\sigma_i$ at $(i, i)$ for $i < \min(m, n)$, and $0$ elsewhere. This is the matrix of
[quarteroni2000numerical], (1.9).

The diagonal is a function on $\mathbb{N}$, so that one $\sigma$ serves every shape, and the
transpose has the same $\sigma$ on the transposed shape. The values $\sigma_i$ for
$i \ge \min(m, n)$ are not used. -/
def rectDiagonal (σ : ℕ → α) : Matrix (Fin m) (Fin n) α :=
  of fun i j => if (i : ℕ) = j then σ i else 0

/-- The entry $(i, j)$ of the rectangular diagonal matrix $\operatorname{diag}(\sigma)$ is
$\sigma_i$ if $i = j$, and $0$ otherwise. -/
theorem rectDiagonal_apply (σ : ℕ → α) (i : Fin m) (j : Fin n) :
    rectDiagonal σ i j = if (i : ℕ) = j then σ i else 0 := rfl

/-- Let $\sigma, \tau : \mathbb{N} \to \alpha$ with $\sigma_i = \tau_i$ for all $i < \min(m, n)$.
Then the rectangular diagonal matrices $\operatorname{diag}(\sigma)$ and
$\operatorname{diag}(\tau)$ in $\alpha^{m \times n}$ are equal. -/
theorem rectDiagonal_congr {σ τ : ℕ → α} (h : ∀ i, i < m → i < n → σ i = τ i) :
    (rectDiagonal σ : Matrix (Fin m) (Fin n) α) = rectDiagonal τ := by
  ext i j
  simp only [rectDiagonal_apply]
  split_ifs with hij
  · exact h i i.isLt (hij ▸ j.isLt)
  · rfl

/-- The transpose of the rectangular diagonal matrix $\operatorname{diag}(\sigma) \in \alpha^{m
\times n}$ is the rectangular diagonal matrix $\operatorname{diag}(\sigma) \in \alpha^{n \times
m}$ with the same diagonal. -/
theorem rectDiagonal_transpose (σ : ℕ → α) :
    (rectDiagonal σ : Matrix (Fin m) (Fin n) α)ᵀ = rectDiagonal σ := by
  ext i j
  simp only [transpose_apply, rectDiagonal_apply]
  split_ifs with h1 h2 h2
  · rw [h1]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

/-- A square rectangular diagonal matrix is a diagonal matrix: $\operatorname{diag}(\sigma) \in
\alpha^{n \times n}$ is the diagonal matrix with diagonal entries
$\sigma_0, \dots, \sigma_{n-1}$. -/
theorem rectDiagonal_eq_diagonal (σ : ℕ → α) :
    (rectDiagonal σ : Matrix (Fin n) (Fin n) α) = diagonal fun i : Fin n => σ i := by
  ext i j
  simp only [rectDiagonal_apply, diagonal_apply, Fin.ext_iff]

/-- Let $k \in \mathbb{N}$ and $\sigma : \mathbb{N} \to \alpha$. The **shifted rectangular diagonal
matrix** in $\alpha^{m \times n}$ has the entry $\sigma_j$ at $(i, j)$ when $j = i + k$, and $0$
elsewhere.

It is the block $D_B$ of a generalized singular value decomposition, and the sine block of a
thin CS decomposition with fewer rows than columns ([golub2013matrix], (6.1.23)). For $k = 0$ it
is `Matrix.rectDiagonal` (`Matrix.shiftedRectDiagonal_zero`). -/
def shiftedRectDiagonal (k : ℕ) (σ : ℕ → α) : Matrix (Fin m) (Fin n) α :=
  of fun i j => if (j : ℕ) = i + k then σ j else 0

/-- The entry $(i, j)$ of the shifted rectangular diagonal matrix with shift $k$ is $\sigma_j$ if
$j = i + k$, and $0$ otherwise. -/
theorem shiftedRectDiagonal_apply (k : ℕ) (σ : ℕ → α) (i : Fin m) (j : Fin n) :
    shiftedRectDiagonal k σ i j = if (j : ℕ) = i + k then σ j else 0 := rfl

/-- With shift $0$, the shifted rectangular diagonal matrix is the rectangular diagonal matrix
$\operatorname{diag}(\sigma)$. -/
theorem shiftedRectDiagonal_zero (σ : ℕ → α) :
    (shiftedRectDiagonal 0 σ : Matrix (Fin m) (Fin n) α) = rectDiagonal σ := by
  ext i j
  rw [shiftedRectDiagonal_apply, rectDiagonal_apply, add_zero]
  by_cases h : (i : ℕ) = j
  · rw [ite_eq_left h.symm, ite_eq_left h, h]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h]

end Zero

/-- The conjugate transpose of the rectangular diagonal matrix $\operatorname{diag}(\sigma) \in
\alpha^{m \times n}$ is the rectangular diagonal matrix $\operatorname{diag}(\bar\sigma) \in
\alpha^{n \times m}$, where $\bar\sigma_i$ is the star of $\sigma_i$. -/
theorem rectDiagonal_conjTranspose {α : Type*} [AddMonoid α] [StarAddMonoid α] (σ : ℕ → α) :
    (rectDiagonal σ : Matrix (Fin m) (Fin n) α)ᴴ = rectDiagonal (star ∘ σ) := by
  ext i j
  simp only [conjTranspose_apply, rectDiagonal_apply, Function.comp_apply]
  split_ifs with h1 h2 h2
  · rw [h1]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact star_zero α

section Semiring

variable {α : Type*} [NonUnitalNonAssocSemiring α]

/-- Let $\Sigma = \operatorname{diag}(\sigma) \in \alpha^{m \times n}$ and $x \in \alpha^n$. For
$i < n$, $(\Sigma x)_i = \sigma_i x_i$. -/
theorem rectDiagonal_mulVec (σ : ℕ → α) (x : Fin n → α) (i : Fin m) (h : (i : ℕ) < n) :
    (rectDiagonal σ *ᵥ x) i = σ i * x ⟨i, h⟩ := by
  rw [mulVec_apply_eq_sum, Finset.sum_eq_single ⟨i, h⟩]
  · simp [rectDiagonal_apply]
  · intro j _ hj
    rw [rectDiagonal_apply, ite_eq_right (fun hij => hj (Fin.ext hij.symm)), zero_mul]
  · exact fun h' => absurd (Finset.mem_univ _) h'

/-- Let $\Sigma = \operatorname{diag}(\sigma) \in \alpha^{m \times n}$ and $x \in \alpha^n$. For
$i \ge n$, $(\Sigma x)_i = 0$. -/
theorem rectDiagonal_mulVec_of_le (σ : ℕ → α) (x : Fin n → α) (i : Fin m) (h : n ≤ i) :
    (rectDiagonal σ *ᵥ x) i = 0 := by
  rw [mulVec_apply_eq_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [rectDiagonal_apply,
    ite_eq_right (fun hij : (i : ℕ) = j => absurd (lt_of_eq_of_lt hij j.isLt) (not_lt.2 h)),
    zero_mul]

/-- Let $\Sigma = \operatorname{diag}(\sigma) \in \alpha^{m \times n}$ and
$M \in \alpha^{n \times o}$. For $i < n$, $(\Sigma M)_{ij} = \sigma_i M_{ij}$. This is the
matrix form of `Matrix.rectDiagonal_mulVec`. -/
theorem rectDiagonal_mul_apply {o : Type*} (σ : ℕ → α) (M : Matrix (Fin n) o α)
    (i : Fin m) (j : o) (h : (i : ℕ) < n) :
    ((rectDiagonal σ : Matrix (Fin m) (Fin n) α) * M) i j = σ i * M ⟨i, h⟩ j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨i, h⟩]
  · rw [rectDiagonal_apply, ite_eq_left rfl]
  · intro k _ hk
    rw [rectDiagonal_apply, ite_eq_right (fun hik => hk (Fin.ext hik.symm)), zero_mul]
  · exact fun h' => absurd (Finset.mem_univ _) h'

/-- Let $M \in \alpha^{o \times m}$ and $\Sigma = \operatorname{diag}(\sigma) \in \alpha^{m \times
n}$. Then $(M \Sigma)_{ij} = M_{ij} \sigma_j$ if $j < m$, and $(M \Sigma)_{ij} = 0$ otherwise. -/
theorem mul_rectDiagonal_apply {o : Type*} (M : Matrix o (Fin m) α) (σ : ℕ → α) (i : o)
    (j : Fin n) :
    (M * (rectDiagonal σ : Matrix (Fin m) (Fin n) α)) i j
      = if h : (j : ℕ) < m then M i ⟨j, h⟩ * σ j else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · rw [rectDiagonal_apply, ite_eq_left rfl]
    · intro k _ hk
      rw [rectDiagonal_apply, ite_eq_right (fun hkj => hk (Fin.ext hkj)), mul_zero]
    · exact fun h' => absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [rectDiagonal_apply, ite_eq_right (fun hkj : (k : ℕ) = j => h (hkj ▸ k.isLt)), mul_zero]

/-- Let $D \in \alpha^{m \times n}$ be the shifted rectangular diagonal matrix with shift $k$, and
let $x \in \alpha^n$. For $i + k < n$, $(Dx)_i = \sigma_{i+k} x_{i+k}$. -/
theorem shiftedRectDiagonal_mulVec (k : ℕ) (σ : ℕ → α) (x : Fin n → α) (i : Fin m)
    (h : (i : ℕ) + k < n) :
    (shiftedRectDiagonal k σ *ᵥ x) i = σ (i + k) * x ⟨i + k, h⟩ := by
  rw [mulVec_apply_eq_sum, Finset.sum_eq_single ⟨i + k, h⟩]
  · simp [shiftedRectDiagonal_apply]
  · intro j _ hj
    rw [shiftedRectDiagonal_apply, ite_eq_right (fun hij => hj (Fin.ext hij)), zero_mul]
  · exact fun h' => absurd (Finset.mem_univ _) h'

/-- The product of two rectangular diagonal matrices is the rectangular diagonal matrix of the
products, truncated at the inner dimension: for $\operatorname{diag}(\sigma) \in \alpha^{l
\times m}$ and $\operatorname{diag}(\tau) \in \alpha^{m \times n}$,
$$\operatorname{diag}(\sigma) \operatorname{diag}(\tau) = \operatorname{diag}(\rho),
  \qquad \rho_i = \begin{cases} \sigma_i \tau_i & \text{if } i < m, \\
  0 & \text{otherwise.} \end{cases}$$
-/
theorem rectDiagonal_mul_rectDiagonal (σ τ : ℕ → α) :
    (rectDiagonal σ : Matrix (Fin l) (Fin m) α) * (rectDiagonal τ : Matrix (Fin m) (Fin n) α)
      = rectDiagonal fun i => if i < m then σ i * τ i else 0 := by
  ext i j
  rw [Matrix.mul_apply, rectDiagonal_apply]
  by_cases hm : (i : ℕ) < m
  · rw [Finset.sum_eq_single ⟨i, hm⟩]
    · simp only [rectDiagonal_apply, ite_eq_left hm]
      split_ifs <;> simp
    · intro k _ hk
      rw [rectDiagonal_apply, ite_eq_right (fun hik => hk (Fin.ext hik.symm)), zero_mul]
    · exact fun h' => absurd (Finset.mem_univ _) h'
  · rw [ite_eq_right hm, ite_self]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [rectDiagonal_apply, ite_eq_right (fun hik : (i : ℕ) = k => hm (lt_of_eq_of_lt hik k.isLt)),
      zero_mul]

end Semiring

end RectDiagonal

/-! ### The full singular value decomposition -/

section SVD

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-- Let $\Sigma = \operatorname{diag}(\sigma) \in \mathbb{K}^{m \times n}$. Then
$\Sigma^H \Sigma \in \mathbb{K}^{n \times n}$ is the diagonal matrix with entries
$\bar\sigma_j \sigma_j = |\sigma_j|^2$ for $j < m$ and $0$ for $j \ge m$. -/
theorem conjTranspose_rectDiagonal_mul_self (σ : ℕ → 𝕜) :
    (rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜)ᴴ * rectDiagonal σ
      = diagonal fun j : Fin n => if (j : ℕ) < m then star (σ j) * σ j else 0 := by
  rw [rectDiagonal_conjTranspose, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
  rfl

/-- Let $D \in \mathbb{K}^{m \times n}$ be the shifted rectangular diagonal matrix with shift $k$.
Then $D^H D \in \mathbb{K}^{n \times n}$ is the diagonal matrix with entries
$\bar\sigma_j \sigma_j = |\sigma_j|^2$ for $k \le j < m + k$ and $0$ for the other $j$. The
shift disappears. -/
theorem conjTranspose_shiftedRectDiagonal_mul_self (k : ℕ) (σ : ℕ → 𝕜) :
    (shiftedRectDiagonal k σ : Matrix (Fin m) (Fin n) 𝕜)ᴴ * shiftedRectDiagonal k σ
      = diagonal fun j : Fin n => if k ≤ j ∧ (j : ℕ) < m + k then star (σ j) * σ j else 0 := by
  ext j l
  rw [Matrix.mul_apply, diagonal_apply]
  simp only [conjTranspose_apply, shiftedRectDiagonal_apply]
  by_cases hjl : j = l
  · subst hjl
    rw [ite_eq_left rfl]
    by_cases hc : k ≤ (j : ℕ) ∧ (j : ℕ) < m + k
    · rw [ite_eq_left hc, Finset.sum_eq_single (⟨j - k, by omega⟩ : Fin m)]
      · have hj : (j : ℕ) = ((⟨j - k, by omega⟩ : Fin m) : ℕ) + k := by dsimp only; omega
        rw [ite_eq_left hj]
      · intro i _ hi
        have : ¬ (j : ℕ) = i + k := fun h => hi (Fin.ext (by dsimp only; omega))
        rw [ite_eq_right this, star_zero, zero_mul]
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [ite_eq_right hc]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : ¬ (j : ℕ) = i + k := fun h => hc ⟨by omega, by omega⟩
      rw [ite_eq_right this, star_zero, zero_mul]
  · rw [ite_eq_right hjl]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : (j : ℕ) = i + k
    · have : ¬ (l : ℕ) = i + k := fun h => hjl (Fin.ext (by omega))
      rw [ite_eq_right this, mul_zero]
    · rw [ite_eq_right h1, star_zero, zero_mul]

/-- Let $D \in \mathbb{K}^{m \times n}$ be the shifted rectangular diagonal matrix with shift $k$,
and let $M \in \mathbb{K}^{m \times o}$. Then row $a$ of $D^H M$ is $\bar\sigma_a$ times row
$a - k$ of $M$ when $k \le a$ and $a - k < m$, and zero otherwise. -/
theorem conjTranspose_shiftedRectDiagonal_mul_apply {o : Type*} (k : ℕ) (σ : ℕ → 𝕜)
    (M : Matrix (Fin m) o 𝕜) (a : Fin n) (b : o) :
    ((shiftedRectDiagonal k σ : Matrix (Fin m) (Fin n) 𝕜)ᴴ * M) a b
      = if h : k ≤ (a : ℕ) ∧ (a : ℕ) - k < m then star (σ a) * M ⟨a - k, h.2⟩ b else 0 := by
  rw [Matrix.mul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a - k, h.2⟩]
    · rw [conjTranspose_apply, shiftedRectDiagonal_apply, ite_eq_left (by simp only; omega)]
    · intro j _ hj
      rw [conjTranspose_apply, shiftedRectDiagonal_apply,
        ite_eq_right (fun hij => hj (Fin.ext (by simp only; omega))), star_zero, zero_mul]
    · exact fun h' => absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [conjTranspose_apply, shiftedRectDiagonal_apply,
      ite_eq_right (fun hij => h ⟨by omega, by omega⟩), star_zero, zero_mul]

/-- Let $D \in \mathbb{K}^{m \times n}$ be the shifted rectangular diagonal matrix with shift $k$,
and let $v \in \mathbb{K}^m$. Then $(D^H v)_i = \bar\sigma_i v_{i-k}$ when $k \le i$ and
$i - k < m$, and $(D^H v)_i = 0$ otherwise. This is the vector form of
`Matrix.conjTranspose_shiftedRectDiagonal_mul_apply`. -/
theorem conjTranspose_shiftedRectDiagonal_mulVec (k : ℕ) (σ : ℕ → 𝕜) (v : Fin m → 𝕜)
    (i : Fin n) :
    ((shiftedRectDiagonal k σ : Matrix (Fin m) (Fin n) 𝕜)ᴴ *ᵥ v) i
      = if h : k ≤ (i : ℕ) ∧ (i : ℕ) - k < m then star (σ i) * v ⟨i - k, h.2⟩ else 0 := by
  rw [mulVec_apply_eq_sum]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i - k, h.2⟩]
    · rw [conjTranspose_apply, shiftedRectDiagonal_apply, ite_eq_left (by simp only; omega)]
    · intro j _ hj
      rw [conjTranspose_apply, shiftedRectDiagonal_apply,
        ite_eq_right (fun hij => hj (Fin.ext (by simp only; omega))), star_zero, zero_mul]
    · exact fun h' => absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [conjTranspose_apply, shiftedRectDiagonal_apply,
      ite_eq_right (fun hij => h ⟨by omega, by omega⟩), star_zero, zero_mul]

/-- Let $n \le m$, $W \in \mathbb{K}^{m \times m}$ and $\Sigma = \operatorname{diag}(\sigma) \in
\mathbb{K}^{m \times n}$. Then $W \Sigma = W_1 \operatorname{diag}(\sigma_0, \dots,
\sigma_{n-1})$, where $W_1$ consists of the first $n$ columns of $W$. -/
theorem mul_rectDiagonal_eq_submatrix_mul_diagonal (hnm : n ≤ m) (W : Matrix (Fin m) (Fin m) 𝕜)
    (σ : ℕ → 𝕜) :
    W * (rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜)
      = W.submatrix id (Fin.castLE hnm) * diagonal fun i : Fin n => σ i := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hnm j),
      Finset.sum_eq_single j]
  · simp [rectDiagonal_apply, submatrix_apply]
  · intro l _ hl
    simp [hl]
  · simp
  · intro l _ hl
    have hl' : (l : ℕ) ≠ j := fun h' => hl (Fin.ext h')
    simp [rectDiagonal_apply, hl']
  · simp

/-- Let $m \le n$, $\Sigma = \operatorname{diag}(\sigma) \in \mathbb{K}^{m \times n}$ and
$W \in \mathbb{K}^{n \times n}$. Then $\Sigma W = \operatorname{diag}(\sigma_0, \dots,
\sigma_{m-1}) W_1$, where $W_1$ consists of the first $m$ rows of $W$. This is the dual of
`Matrix.mul_rectDiagonal_eq_submatrix_mul_diagonal`. -/
theorem rectDiagonal_mul_eq_diagonal_mul_submatrix (hmn : m ≤ n) (σ : ℕ → 𝕜)
    (W : Matrix (Fin n) (Fin n) 𝕜) :
    (rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜) * W
      = (diagonal fun i : Fin m => σ i) * W.submatrix (Fin.castLE hmn) id := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hmn i),
      Finset.sum_eq_single i]
  · simp [rectDiagonal_apply, submatrix_apply]
  · intro l _ hl
    simp [Ne.symm hl]
  · simp
  · intro l _ hl
    have hl' : (i : ℕ) ≠ l := fun h' => hl (Fin.ext h'.symm)
    simp [rectDiagonal_apply, hl']
  · simp

/-- Let $n \le m$ and let $W \in \mathbb{K}^{m \times m}$ be unitary. The first $n$ columns $W_1$ of
$W$ are orthonormal: $W_1^H W_1 = I$. -/
theorem conjTranspose_submatrix_castLE_mul_self (hnm : n ≤ m) {W : Matrix (Fin m) (Fin m) 𝕜}
    (hW : W ∈ unitaryGroup (Fin m) 𝕜) :
    (W.submatrix id (Fin.castLE hnm))ᴴ * W.submatrix id (Fin.castLE hnm) = 1 := by
  rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hW]
  exact submatrix_one _ (Fin.castLE_injective hnm)

/-- Let $b$ be an orthonormal basis of $\mathbb{K}^\iota$. The matrix `Matrix.unitaryOfBasis b` is
the matrix whose column $j$ is the basis vector $b_j$. It is the change-of-basis matrix from the
standard basis to $b$, and it is unitary (`Matrix.unitaryOfBasis_mem_unitaryGroup`). -/
noncomputable def unitaryOfBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) : Matrix ι ι 𝕜 :=
  (EuclideanSpace.basisFun ι 𝕜).toBasis.toMatrix b.toBasis

/-- The entry $(i, j)$ of `Matrix.unitaryOfBasis b` is the coordinate $i$ of the basis vector $b_j$,
so its column $j$ is $b_j$. -/
theorem unitaryOfBasis_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) (i j : ι) : unitaryOfBasis b i j = b j i :=
  rfl

/-- For an orthonormal basis $b$ of $\mathbb{K}^\iota$, the matrix `Matrix.unitaryOfBasis b` with
columns $b_j$ is unitary. -/
theorem unitaryOfBasis_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) : unitaryOfBasis b ∈ unitaryGroup ι 𝕜 :=
  (EuclideanSpace.basisFun ι 𝕜).toMatrix_orthonormalBasis_mem_unitary b

/-- Row $j$ of the transpose of `Matrix.unitaryOfBasis b`, that is, column $j$ of
`Matrix.unitaryOfBasis b`, is the basis vector $b_j$. -/
theorem unitaryOfBasis_transpose_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) (j : ι) :
    (unitaryOfBasis b)ᵀ j = ⇑(b j) := rfl

/-- Let $V \in \mathbb{K}^{\iota \times r}$ satisfy $V^H V = I$. Then the columns of $V$ are
orthonormal vectors of the Euclidean space $\mathbb{K}^\iota$. -/
theorem orthonormal_toLp_transpose_of_conjTranspose_mul_self_eq_one {ι r : Type*} [Fintype ι]
    [DecidableEq r] {V : Matrix ι r 𝕜} (hV : Vᴴ * V = 1) :
    Orthonormal 𝕜 fun j => (WithLp.toLp 2 (Vᵀ j) : EuclideanSpace 𝕜 ι) :=
  conjTranspose_mul_self_eq_one_iff_orthonormal.mp hV

/-- **Orthonormal columns extend to a unitary matrix.** Let $V \in \mathbb{K}^{\iota \times r}$
satisfy $V^H V = I$, and let $f : r \to \iota$ be injective. Then there is a unitary
$U \in \mathbb{K}^{\iota \times \iota}$ whose column $f(j)$ is column $j$ of $V$ for every
$j \in r$. This is Theorem 2.1.1 of [golub2013matrix].

The columns of $V$ extend to an orthonormal basis of $\mathbb{K}^\iota$
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), and $U$ is its matrix
`Matrix.unitaryOfBasis`. -/
theorem exists_mem_unitaryGroup_submatrix_eq {ι r : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq r] (V : Matrix ι r 𝕜) (hV : Vᴴ * V = 1) (f : r ↪ ι) :
    ∃ U ∈ unitaryGroup ι 𝕜, U.submatrix id f = V := by
  classical
  set w : r → EuclideanSpace 𝕜 ι := fun j => WithLp.toLp 2 (Vᵀ j) with hw
  have hwo : Orthonormal 𝕜 w := orthonormal_toLp_transpose_of_conjTranspose_mul_self_eq_one hV
  set v : ι → EuclideanSpace 𝕜 ι := Function.extend f w 0 with hv
  have hvf : ∀ j, v (f j) = w j := fun j => f.injective.extend_apply w 0 j
  have hvo : Orthonormal 𝕜 ((Set.range f).domRestrict v) := by
    have heq : (Set.range f).domRestrict v = w ∘ (Equiv.ofInjective f f.injective).symm := by
      funext x
      obtain ⟨_, j, rfl⟩ := x
      simp only [Set.domRestrict_apply, Function.comp_apply, Equiv.ofInjective_symm_apply, hvf]
    rw [heq]
    exact hwo.comp _ (Equiv.injective _)
  obtain ⟨b, hb⟩ := hvo.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := 𝕜) (ι := ι))
  refine ⟨unitaryOfBasis b, unitaryOfBasis_mem_unitaryGroup b, ?_⟩
  ext i j
  rw [submatrix_apply, id, unitaryOfBasis_apply, hb (f j) ⟨j, rfl⟩, hvf]
  rfl

open scoped Matrix.Norms.L2Operator in
/-- **The 2-norm of a rectangular diagonal matrix** is the largest modulus on its diagonal: for
$\Sigma = \operatorname{diag}(\sigma) \in \mathbb{K}^{m \times n}$,
$$\|\Sigma\|_2 = \max_{i < \min(m, n)} |\sigma_i|,$$
and $\|\Sigma\|_2 = 0$ when $\min(m, n) = 0$. This is Problem P2.3.3 of [golub2013matrix] for
$p = 2$.

The proof uses $\|\Sigma\|_2^2 = \|\Sigma^H \Sigma\|_2$, where $\Sigma^H \Sigma$ is the diagonal
matrix of the $|\sigma_i|^2$. -/
theorem l2_opNorm_rectDiagonal (σ : ℕ → 𝕜) :
    ‖(rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜)‖ = ⨆ i : Fin (min m n), ‖σ i‖ := by
  set S : Matrix (Fin m) (Fin n) 𝕜 := rectDiagonal σ with hS
  set s : ℝ := ⨆ i : Fin (min m n), ‖σ i‖ with hs
  set d : Fin n → 𝕜 := fun j => if (j : ℕ) < m then star (σ j) * σ j else 0 with hd
  have hs0 : 0 ≤ s := Real.iSup_nonneg fun i => norm_nonneg _
  have hle : ∀ i : ℕ, i < m → i < n → ‖σ i‖ ≤ s := fun i him hin =>
    le_ciSup (f := fun i : Fin (min m n) => ‖σ i‖) (Set.finite_range _).bddAbove
      ⟨i, lt_min him hin⟩
  have hdj : ∀ j : Fin n, ‖d j‖ = if (j : ℕ) < m then ‖σ j‖ ^ 2 else 0 := fun j => by
    simp only [hd]
    split_ifs
    · rw [norm_mul, norm_star, sq]
    · exact norm_zero
  have hSS : ‖S‖ * ‖S‖ = ‖d‖ := by
    rw [← l2_opNorm_conjTranspose_mul_self, hS, conjTranspose_rectDiagonal_mul_self,
      l2_opNorm_diagonal]
  have hdle : ‖d‖ ≤ s ^ 2 := by
    refine (pi_norm_le_iff_of_nonneg (sq_nonneg s)).2 fun j => ?_
    rw [hdj]
    split_ifs with hj
    · exact pow_le_pow_left₀ (norm_nonneg _) (hle j hj j.isLt) 2
    · exact sq_nonneg s
  have hsle : s ^ 2 ≤ ‖d‖ := by
    rcases isEmpty_or_nonempty (Fin (min m n)) with he | he
    · rw [hs, Real.iSup_of_isEmpty]; simp
    · have hsd : s ≤ Real.sqrt ‖d‖ := by
        refine ciSup_le fun i => ?_
        have hi := i.isLt
        have him : (i : ℕ) < m := lt_of_lt_of_le hi (min_le_left _ _)
        have hin : (i : ℕ) < n := lt_of_lt_of_le hi (min_le_right _ _)
        have h1 := norm_le_pi_norm d ⟨i, hin⟩
        rw [hdj, ite_eq_left him] at h1
        exact Real.le_sqrt_of_sq_le h1
      calc s ^ 2 ≤ Real.sqrt ‖d‖ ^ 2 := pow_le_pow_left₀ hs0 hsd 2
        _ = ‖d‖ := Real.sq_sqrt (norm_nonneg _)
  have hsq : ‖S‖ ^ 2 = s ^ 2 := by rw [sq, hSS]; exact le_antisymm hdle hsle
  exact (pow_left_inj₀ (norm_nonneg _) hs0 two_ne_zero).1 hsq

open scoped ComplexOrder in
/-- **The rank of a rectangular diagonal matrix** $\operatorname{diag}(\sigma) \in \mathbb{K}^{m
\times n}$ is the number of nonzero entries on its diagonal, that is, the number of
$j < \min(m, n)$ with $\sigma_j \neq 0$. -/
theorem rank_rectDiagonal (σ : ℕ → 𝕜) :
    (rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜).rank
      = Fintype.card {j : Fin n // (j : ℕ) < m ∧ σ j ≠ 0} := by
  classical
  rw [← rank_conjTranspose_mul_self, conjTranspose_rectDiagonal_mul_self, rank_diagonal]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun j => ?_)
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Let $U \in \mathbb{K}^{m \times m}$, $A \in \mathbb{K}^{m \times n}$ and
$V \in \mathbb{K}^{n \times n}$, with columns $u_i$ of $U$ and $v_j$ of $V$. Then
$$(U^H A V)_{ij} = \langle u_i, A v_j \rangle.$$
-/
theorem star_mul_mul_apply (U : Matrix (Fin m) (Fin m) 𝕜) (A : Matrix (Fin m) (Fin n) 𝕜)
    (V : Matrix (Fin n) (Fin n) 𝕜) (i : Fin m) (j : Fin n) :
    (star U * A * V) i j = inner 𝕜 (WithLp.toLp 2 (Uᵀ i) : EuclideanSpace 𝕜 (Fin m))
      (toEuclideanLin A (WithLp.toLp 2 (Vᵀ j))) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin, dotProduct, mulVec,
    Matrix.mul_apply, star_apply, transpose_apply, Pi.star_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- Let $A \in \mathbb{K}^{m \times n}$. The **sorted right singular vectors**
$v_0, v_1, \dots \in \mathbb{K}^n$ of $A$ are, for $j < n$, the vectors of the orthonormal
eigenbasis of $A^H A$ sorted by decreasing eigenvalue, so that $v_j$ belongs to the sorted
singular value $\sigma_j$. For $j \ge n$, $v_j = 0$.

The family is indexed by $\mathbb{N}$, like `Matrix.rectDiagonal` and
`LinearMap.singularValues`. The eigenbasis is `LinearMap.IsSymmetric.eigenvectorBasis` of the
composition of the adjoint of `Matrix.toEuclideanLin A` with `Matrix.toEuclideanLin A`. -/
noncomputable def sortedRightSingularVec (A : Matrix (Fin m) (Fin n) 𝕜) (j : ℕ) :
    EuclideanSpace 𝕜 (Fin n) :=
  if h : j < n then
    (toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin
      ⟨j, h⟩
  else 0

/-- For $j < n$, the sorted right singular vector $v_j$ is the vector of index $j$ of the sorted
eigenbasis of $A^H A$. -/
theorem sortedRightSingularVec_of_lt (A : Matrix (Fin m) (Fin n) 𝕜) {j : ℕ} (h : j < n) :
    A.sortedRightSingularVec j = (toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis
      finrank_euclideanSpace_fin ⟨j, h⟩ := by
  rw [sortedRightSingularVec, dite_eq_left h]

/-- For $j \ge n$, the sorted right singular vector $v_j$ is $0$. -/
theorem sortedRightSingularVec_of_le (A : Matrix (Fin m) (Fin n) 𝕜) {j : ℕ} (h : n ≤ j) :
    A.sortedRightSingularVec j = 0 := by
  rw [sortedRightSingularVec, dite_eq_right (not_lt.2 h)]

/-- Let $A \in \mathbb{K}^{m \times n}$ with sorted right singular vectors $v_j$ and sorted singular
values $\sigma_j$. For all $i, j \in \mathbb{N}$,
$$\langle A v_i, A v_j \rangle = \begin{cases} \sigma_j^2 & \text{if } i = j < n, \\
  0 & \text{otherwise.} \end{cases}$$
-/
theorem inner_toEuclideanLin_sortedRightSingularVec (A : Matrix (Fin m) (Fin n) 𝕜) (i j : ℕ) :
    inner 𝕜 (toEuclideanLin A (A.sortedRightSingularVec i))
        (toEuclideanLin A (A.sortedRightSingularVec j))
      = if i = j ∧ j < n then (((toEuclideanLin A).singularValues j ^ 2 : ℝ) : 𝕜) else 0 := by
  by_cases hj : j < n
  · by_cases hi : i < n
    · rw [sortedRightSingularVec_of_lt A hi, sortedRightSingularVec_of_lt A hj,
        (toEuclideanLin A).inner_apply_eigenvectorBasis_adjoint_comp_self]
      simp only [Fin.mk.injEq, hj, and_true]
    · rw [sortedRightSingularVec_of_le A (not_lt.1 hi), map_zero, inner_zero_left,
        ite_eq_right (fun h : i = j ∧ j < n => hi (h.1 ▸ hj))]
  · rw [sortedRightSingularVec_of_le A (not_lt.1 hj), map_zero, inner_zero_right,
      ite_eq_right (fun h : i = j ∧ j < n => hj h.2)]

/-- Let $A \in \mathbb{K}^{m \times n}$. For every $j \in \mathbb{N}$, $\|A v_j\| = \sigma_j$, where
$v_j$ is the sorted right singular vector and $\sigma_j$ the sorted singular value. -/
theorem norm_toEuclideanLin_sortedRightSingularVec (A : Matrix (Fin m) (Fin n) 𝕜) (j : ℕ) :
    ‖toEuclideanLin A (A.sortedRightSingularVec j)‖ = (toEuclideanLin A).singularValues j := by
  by_cases hj : j < n
  · rw [sortedRightSingularVec_of_lt A hj,
      (toEuclideanLin A).norm_apply_eigenvectorBasis_adjoint_comp_self]
  · rw [sortedRightSingularVec_of_le A (not_lt.1 hj), map_zero, norm_zero,
      (toEuclideanLin A).singularValues_of_finrank_le (finrank_euclideanSpace_fin.trans_le
        (not_lt.1 hj))]

/-- Let $A \in \mathbb{K}^{m \times n}$. The sorted right singular vectors are orthonormal below
$n$: for $i, j < n$, $\langle v_i, v_j \rangle = 1$ if $i = j$ and $0$ otherwise. -/
theorem inner_sortedRightSingularVec (A : Matrix (Fin m) (Fin n) 𝕜) {i j : ℕ} (hi : i < n)
    (hj : j < n) :
    inner 𝕜 (A.sortedRightSingularVec i) (A.sortedRightSingularVec j) = if i = j then 1 else 0 := by
  rw [sortedRightSingularVec_of_lt A hi, sortedRightSingularVec_of_lt A hj,
    orthonormal_iff_ite.1 ((toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis
      finrank_euclideanSpace_fin).orthonormal]
  simp only [Fin.mk.injEq]

/-- Let $A \in \mathbb{K}^{m \times n}$ with sorted right singular vectors $v_i$ and sorted singular
values $\sigma_i$. The normalized images $\sigma_i^{-1} A v_i$, for the indices $i < m$ with
$\sigma_i \neq 0$, form an orthonormal family in $\mathbb{K}^m$. -/
theorem orthonormal_leftSingular (A : Matrix (Fin m) (Fin n) 𝕜) :
    Orthonormal 𝕜 (({i : Fin m | (toEuclideanLin A).singularValues i ≠ 0} : Set (Fin m)).domRestrict
      fun i : Fin m => (((toEuclideanLin A).singularValues i : ℝ) : 𝕜)⁻¹ •
        toEuclideanLin A (A.sortedRightSingularVec i)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Set.domRestrict, inner_smul_left, inner_smul_right, map_inv₀, RCLike.conj_ofReal,
    inner_toEuclideanLin_sortedRightSingularVec, Subtype.mk.injEq, Fin.ext_iff]
  have hj' : (j : ℕ) < n := by
    by_contra h
    exact hj ((toEuclideanLin A).singularValues_of_finrank_le
      (finrank_euclideanSpace_fin.trans_le (not_lt.1 h)))
  simp only [hj', and_true]
  split_ifs with h
  · rw [h]
    have : (((toEuclideanLin A).singularValues j : ℝ) : 𝕜) ≠ 0 := by
      simpa using (hj : (toEuclideanLin A).singularValues j ≠ 0)
    push_cast
    field_simp
  · simp

/-- **The singular value decomposition.** Let $A \in \mathbb{K}^{m \times n}$ with sorted singular
values $\sigma_0 \ge \sigma_1 \ge \dots \ge 0$. There are unitary matrices
$U \in \mathbb{K}^{m \times m}$ and $V \in \mathbb{K}^{n \times n}$ with
$$U^H A V = \Sigma = \operatorname{diag}(\sigma_0, \sigma_1, \dots)
  \in \mathbb{K}^{m \times n}.$$
This is Property 1.7 of [quarteroni2000numerical]. For $\mathbb{K} = \mathbb{R}$ the factors are
real orthogonal matrices, which is the real case of the source.

The diagonal of $\Sigma$ is `Matrix.sortedSingularValues A`, which unfolds to Mathlib's
`LinearMap.singularValues` of `Matrix.toEuclideanLin A`, and the matrix `Matrix.rectDiagonal`
gives $\Sigma$. The
columns of $V$ are the sorted right singular vectors `Matrix.sortedRightSingularVec`. The images
$A v_j$ are pairwise orthogonal with $\|A v_j\| = \sigma_j$, so the normalized ones with
$\sigma_j \neq 0$ are orthonormal (`Matrix.orthonormal_leftSingular`). Placed at the same
indices, they extend to an orthonormal basis of $\mathbb{K}^m$
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), whose vectors are the columns of
$U$. -/
theorem exists_svd (A : Matrix (Fin m) (Fin n) 𝕜) :
    ∃ U ∈ unitaryGroup (Fin m) 𝕜, ∃ V ∈ unitaryGroup (Fin n) 𝕜,
      star U * A * V = rectDiagonal fun i => (((toEuclideanLin A).singularValues i : ℝ) : 𝕜) := by
  obtain ⟨b, hb⟩ := A.orthonormal_leftSingular.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace_fin.trans (Fintype.card_fin m).symm)
  set v : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
    (toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin
    with hv
  refine ⟨unitaryOfBasis b, unitaryOfBasis_mem_unitaryGroup b, unitaryOfBasis v,
    unitaryOfBasis_mem_unitaryGroup v, ?_⟩
  ext i j
  rw [star_mul_mul_apply, rectDiagonal_apply, unitaryOfBasis_transpose_apply,
    unitaryOfBasis_transpose_apply, WithLp.toLp_ofLp, WithLp.toLp_ofLp, hv,
    ← A.sortedRightSingularVec_of_lt j.isLt]
  by_cases hj : (toEuclideanLin A).singularValues j = 0
  · have hTv : toEuclideanLin A (A.sortedRightSingularVec j) = 0 := by
      rw [← norm_eq_zero, norm_toEuclideanLin_sortedRightSingularVec, hj]
    rw [hTv, inner_zero_right]
    split_ifs with hij
    · rw [hij, hj, RCLike.ofReal_zero]
    · rfl
  · have hjm : (j : ℕ) < m := by
      by_contra h
      exact hj ((toEuclideanLin A).singularValues_of_finrank_codomain_le
        (finrank_euclideanSpace_fin.trans_le (not_lt.1 h)))
    have hbj : b ⟨j, hjm⟩ = (((toEuclideanLin A).singularValues j : ℝ) : 𝕜)⁻¹ •
        toEuclideanLin A (A.sortedRightSingularVec j) := hb ⟨j, hjm⟩ hj
    have hTv : toEuclideanLin A (A.sortedRightSingularVec j)
        = (((toEuclideanLin A).singularValues j : ℝ) : 𝕜) • b ⟨j, hjm⟩ := by
      rw [hbj, smul_smul, mul_inv_cancel₀ (by simpa using hj), one_smul]
    rw [hTv, inner_smul_right, orthonormal_iff_ite.1 b.orthonormal i ⟨j, hjm⟩]
    by_cases hij : (i : ℕ) = j
    · rw [ite_eq_left (Fin.ext hij), ite_eq_left hij, mul_one, hij]
    · rw [ite_eq_right (fun h => hij (congrArg Fin.val h)), ite_eq_right hij, mul_zero]

/-!
### Consequences of a singular value decomposition

The results below take as hypothesis an arbitrary factorization $U^H A V = \Sigma$ with unitary $U$,
$V$ and rectangular diagonal $\Sigma$, not necessarily the one that `Matrix.exists_svd` gives. From
it they compute the pseudoinverse, the kernel, the range and the singular values.
-/

/-- Let $A \in \mathbb{K}^{m \times n}$, let $U \in \mathbb{K}^{m \times m}$ and
$V \in \mathbb{K}^{n \times n}$ be unitary, and let $U^H A V = S$. Then $A = U S V^H$. -/
theorem eq_mul_mul_star_of_star_mul_mul_eq {A : Matrix (Fin m) (Fin n) 𝕜}
    {U : Matrix (Fin m) (Fin m) 𝕜} {V : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin m) 𝕜)
    (hV : V ∈ unitaryGroup (Fin n) 𝕜) {S : Matrix (Fin m) (Fin n) 𝕜} (h : star U * A * V = S) :
    A = U * S * star V := by
  rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, mem_unitaryGroup_iff.1 hV, Matrix.mul_one,
    ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU, Matrix.one_mul]

/-- **The thin singular value decomposition.** Let $A \in \mathbb{K}^{m \times n}$ with $n \le m$,
and let $\sigma_0 \ge \sigma_1 \ge \dots$ be its sorted singular values. There are
$U_1 \in \mathbb{K}^{m \times n}$ with orthonormal columns, $U_1^H U_1 = I$, and a unitary
$V \in \mathbb{K}^{n \times n}$ with
$$A = U_1 \operatorname{diag}(\sigma_0, \dots, \sigma_{n-1}) V^H.$$
This is in [golub2013matrix], §2.4.3.

The matrix $U_1$ consists of the first $n$ columns of the $U$ of `Matrix.exists_svd`, which are
the only columns that $U \Sigma$ uses. -/
theorem exists_thin_svd (A : Matrix (Fin m) (Fin n) 𝕜) (hnm : n ≤ m) :
    ∃ U₁ : Matrix (Fin m) (Fin n) 𝕜, U₁ᴴ * U₁ = 1 ∧ ∃ V ∈ unitaryGroup (Fin n) 𝕜,
      A = U₁ * diagonal (fun i : Fin n => ((A.sortedSingularValues i : ℝ) : 𝕜)) * star V := by
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  refine ⟨U.submatrix id (Fin.castLE hnm), ?_, V, hV, ?_⟩
  · rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hU]
    exact submatrix_one _ (Fin.castLE_injective hnm)
  · conv_lhs => rw [eq_mul_mul_star_of_star_mul_mul_eq hU hV h]
    congr 1
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hnm j),
      Finset.sum_eq_single j]
    · simp [rectDiagonal_apply, submatrix_apply, sortedSingularValues]
    · intro l _ hl
      simp [hl]
    · simp
    · intro l _ hl
      have hl' : (l : ℕ) ≠ j := fun h' => hl (Fin.ext h')
      simp [rectDiagonal_apply, hl']
    · simp

/-- **The thin singular value decomposition of a wide matrix.** Let $A \in \mathbb{K}^{m \times n}$
with $m \le n$, and let $\sigma_0 \ge \sigma_1 \ge \dots$ be its sorted singular values. There
are $V_1 \in \mathbb{K}^{n \times m}$ with orthonormal columns, $V_1^H V_1 = I$, and a unitary
$U \in \mathbb{K}^{m \times m}$ with
$$A = U \operatorname{diag}(\sigma_0, \dots, \sigma_{m-1}) V_1^H.$$
This is in [golub2013matrix], §2.4.3.

This is the dual of `Matrix.exists_thin_svd`. The matrix $V_1$ consists of the first $m$ columns
of the $V$ of `Matrix.exists_svd`, which are the only columns that $\Sigma V^H$ uses. -/
theorem exists_wide_thin_svd (A : Matrix (Fin m) (Fin n) 𝕜) (hmn : m ≤ n) :
    ∃ V₁ : Matrix (Fin n) (Fin m) 𝕜, V₁ᴴ * V₁ = 1 ∧ ∃ U ∈ unitaryGroup (Fin m) 𝕜,
      A = U * diagonal (fun i : Fin m => ((A.sortedSingularValues i : ℝ) : 𝕜)) * V₁ᴴ := by
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  refine ⟨V.submatrix id (Fin.castLE hmn), conjTranspose_submatrix_castLE_mul_self hmn hV, U, hU,
    ?_⟩
  conv_lhs => rw [eq_mul_mul_star_of_star_mul_mul_eq hU hV h]
  rw [Matrix.mul_assoc, rectDiagonal_mul_eq_diagonal_mul_submatrix hmn, ← Matrix.mul_assoc,
    star_eq_conjTranspose, conjTranspose_submatrix]

/-- **The pseudoinverse from a singular value decomposition.** Let $A \in \mathbb{K}^{m \times n}$,
let $U$ and $V$ be unitary, and let $\sigma : \mathbb{N} \to \mathbb{K}$ satisfy $U^H A V =
\Sigma = \operatorname{diag}(\sigma) \in \mathbb{K}^{m \times n}$. Then
$$A^+ = V \Sigma^+ U^H, \qquad \Sigma^+ = \operatorname{diag}(\sigma_0^{-1}, \sigma_1^{-1}, \dots)
  \in \mathbb{K}^{n \times m},$$
with $0^{-1} = 0$. This is Definition 1.15 of [quarteroni2000numerical].

The convention $0^{-1} = 0$ gives exactly the matrix $\operatorname{diag}(1/\sigma_1, \dots,
1/\sigma_r, 0, \dots, 0)$ of (1.11) in the source, without a case split on the rank. Nothing is
assumed about $\sigma$, not even that it is real. The right-hand side satisfies the four Penrose
conditions, and `Matrix.pinv_unique` identifies it with $A^+$. -/
theorem pinv_eq_of_svd {A : Matrix (Fin m) (Fin n) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜}
    {V : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin m) 𝕜)
    (hV : V ∈ unitaryGroup (Fin n) 𝕜) {σ : ℕ → 𝕜} (h : star U * A * V = rectDiagonal σ) :
    A.pinv = V * (rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) 𝕜) * star U := by
  have hA : A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜) * star V :=
    eq_mul_mul_star_of_star_mul_mul_eq hU hV h
  have hUU : ∀ {k : Type} (X : Matrix (Fin m) k 𝕜), star U * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, mem_unitaryGroup_iff'.1 hU, Matrix.one_mul]
  have hVV : ∀ {k : Type} (X : Matrix (Fin n) k 𝕜), star V * (V * X) = X := fun X => by
    rw [← Matrix.mul_assoc, mem_unitaryGroup_iff'.1 hV, Matrix.one_mul]
  have hstar : ∀ i, star (σ i * (σ i)⁻¹) = σ i * (σ i)⁻¹ := fun i => by
    rcases eq_or_ne (σ i) 0 with h0 | h0
    · simp [h0]
    · rw [mul_inv_cancel₀ h0, star_one]
  have hstar' : ∀ i, star ((σ i)⁻¹ * σ i) = (σ i)⁻¹ * σ i := fun i => by
    rw [mul_comm]; exact hstar i
  -- the diagonal identities
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin m) (Fin n) 𝕜, S = rectDiagonal σ := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Matrix (Fin n) (Fin m) 𝕜, S' = rectDiagonal fun i => (σ i)⁻¹ :=
    ⟨_, rfl⟩
  rw [← hS] at hA
  rw [← hS']
  have h1 : S * S' * S = S := by
    rw [hS, hS', rectDiagonal_mul_rectDiagonal, rectDiagonal_mul_rectDiagonal]
    refine rectDiagonal_congr fun i him hin => ?_
    rw [ite_eq_left him, ite_eq_left hin, mul_inv_mul_cancel]
  have h2 : S' * S * S' = S' := by
    rw [hS, hS', rectDiagonal_mul_rectDiagonal, rectDiagonal_mul_rectDiagonal]
    refine rectDiagonal_congr fun i hin him => ?_
    rw [ite_eq_left hin, ite_eq_left him, inv_mul_mul_inv]
  have h3 : (S * S')ᴴ = S * S' := by
    rw [hS, hS', rectDiagonal_mul_rectDiagonal, rectDiagonal_conjTranspose]
    refine rectDiagonal_congr fun i _ _ => ?_
    simp only [Function.comp_apply]
    split_ifs
    · exact hstar i
    · exact star_zero 𝕜
  have h4 : (S' * S)ᴴ = S' * S := by
    rw [hS, hS', rectDiagonal_mul_rectDiagonal, rectDiagonal_conjTranspose]
    refine rectDiagonal_congr fun i _ _ => ?_
    simp only [Function.comp_apply]
    split_ifs
    · exact hstar' i
    · exact star_zero 𝕜
  symm
  refine pinv_unique A ?_ ?_ ?_ ?_
  · rw [hA]
    simp only [Matrix.mul_assoc]
    rw [hVV, hUU, ← Matrix.mul_assoc S, ← Matrix.mul_assoc (S * S'), h1]
  · rw [hA]
    simp only [Matrix.mul_assoc]
    rw [hUU, hVV, ← Matrix.mul_assoc S', ← Matrix.mul_assoc (S' * S), h2]
  · rw [hA, IsHermitian]
    simp only [Matrix.mul_assoc]
    rw [hVV, ← Matrix.mul_assoc S, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, h3, Matrix.mul_assoc]
  · rw [hA, IsHermitian]
    simp only [Matrix.mul_assoc]
    rw [hUU, ← Matrix.mul_assoc S', star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, h4, Matrix.mul_assoc]

end SVD

section PinvSpecial

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The pseudoinverse of a nonsingular matrix is its inverse: if $A \in \mathbb{K}^{n \times n}$ is
invertible, then $A^+ = A^{-1}$. This is in [quarteroni2000numerical], §1.9, as $A^+ = A^{-1}$
when $n = m = \operatorname{rank} A$. -/
theorem pinv_eq_inv {A : Matrix n n 𝕜} (hA : IsUnit A) : A.pinv = A⁻¹ := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det _).1 hA
  symm
  refine pinv_unique A ?_ ?_ ?_ ?_
  · rw [mul_nonsing_inv _ hdet, Matrix.one_mul]
  · rw [nonsing_inv_mul _ hdet, Matrix.one_mul]
  · rw [mul_nonsing_inv _ hdet]
    exact isHermitian_one
  · rw [nonsing_inv_mul _ hdet]
    exact isHermitian_one

/-- Let $A \in \mathbb{K}^{m \times n}$ have nonsingular Gram matrix $A^H A$, that is, full column
rank. Then
$$A^+ = (A^H A)^{-1} A^H.$$
This is in [quarteroni2000numerical], §1.9, as $A^+ = (A^T A)^{-1} A^T$ when
$\operatorname{rank} A = n < m$.

The same identity, with the hypothesis that the columns of $A$ are linearly independent, is
`Matrix.pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose`. -/
theorem pinv_eq_inv_conjTranspose_mul_self_mul_conjTranspose_of_isUnit {A : Matrix m n 𝕜}
    (h : IsUnit (Aᴴ * A)) : A.pinv = (Aᴴ * A)⁻¹ * Aᴴ := by
  have hdet : IsUnit (Aᴴ * A).det := (isUnit_iff_isUnit_det _).1 h
  have hH : (Aᴴ * A)⁻¹.IsHermitian := (isHermitian_conjTranspose_mul_self A).inv
  symm
  refine pinv_unique A ?_ ?_ ?_ ?_
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.mul_one]
  · rw [Matrix.mul_assoc (Aᴴ * A)⁻¹ Aᴴ A, nonsing_inv_mul _ hdet, Matrix.one_mul]
  · rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq,
      Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, nonsing_inv_mul _ hdet]
    exact isHermitian_one

end PinvSpecial

section SVD2

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-- For a unitary $V$ with columns $v_j$, $V^H v_j = e_j$, the standard basis vector. -/
private theorem star_mulVec_transpose_apply {V : Matrix (Fin n) (Fin n) 𝕜}
    (hV : V ∈ unitaryGroup (Fin n) 𝕜) (j : Fin n) : star V *ᵥ Vᵀ j = Pi.single j 1 := by
  have : Vᵀ j = V *ᵥ Pi.single j 1 := by rw [mulVec_single_one]; rfl
  rw [this, mulVec_mulVec, mem_unitaryGroup_iff'.1 hV, one_mulVec]

/-- For a unitary $V$ with columns $v_j$, every $x$ expands as $x = \sum_j (V^H x)_j \, v_j$. -/
private theorem eq_sum_star_mulVec_smul_transpose {V : Matrix (Fin n) (Fin n) 𝕜}
    (hV : V ∈ unitaryGroup (Fin n) 𝕜) (x : Fin n → 𝕜) :
    x = ∑ j, (star V *ᵥ x) j • Vᵀ j := by
  conv_lhs => rw [← one_mulVec x, ← mem_unitaryGroup_iff.1 hV, ← mulVec_mulVec, mulVec_eq_sum]
  simp only [op_smul_eq_smul]

/-- **The kernel from a singular value decomposition.** Let $A \in \mathbb{K}^{m \times n}$, let $U$
and $V$ be unitary with columns $v_j$ of $V$, and let $\sigma : \mathbb{N} \to \mathbb{K}$
satisfy $U^H A V = \operatorname{diag}(\sigma) \in \mathbb{K}^{m \times n}$. Then
$$\ker A = \operatorname{span}\{v_j : j \ge m \text{ or } \sigma_j = 0\}.$$
This is in [quarteroni2000numerical], §1.9.

The spanning columns are those whose singular value is zero: the columns beyond the height of
$\Sigma$, and those with $\sigma_j = 0$. For sorted singular values and
$r = \operatorname{rank} A$, these are $v_{r+1}, \dots, v_n$ in the numbering from $1$ of the
source. -/
theorem ker_mulVecLin_eq_span_of_svd {A : Matrix (Fin m) (Fin n) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜}
    {V : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin m) 𝕜)
    (hV : V ∈ unitaryGroup (Fin n) 𝕜) {σ : ℕ → 𝕜} (h : star U * A * V = rectDiagonal σ) :
    LinearMap.ker A.mulVecLin
      = Submodule.span 𝕜 (Vᵀ '' {j : Fin n | m ≤ (j : ℕ) ∨ σ j = 0}) := by
  have hA : A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜) * star V :=
    eq_mul_mul_star_of_star_mul_mul_eq hU hV h
  -- `A x = 0` exactly when `Σ (Vᴴ x) = 0`
  have key : ∀ x, A *ᵥ x = 0 ↔
      (rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜) *ᵥ (star V *ᵥ x) = 0 := by
    intro x
    rw [hA, ← mulVec_mulVec, ← mulVec_mulVec]
    constructor
    · intro hx
      have h0 : star U *ᵥ (U *ᵥ ((rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜) *ᵥ (star V *ᵥ x)))
          = 0 := by rw [hx, mulVec_zero]
      rwa [mulVec_mulVec, mem_unitaryGroup_iff'.1 hU, one_mulVec] at h0
    · intro hx
      rw [hx, mulVec_zero]
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · intro x hx
    rw [LinearMap.mem_ker, mulVecLin_apply, key] at hx
    rw [eq_sum_star_mulVec_smul_transpose hV x]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : m ≤ (j : ℕ) ∨ σ j = 0
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · push Not at hj
      have hzero := congrFun hx ⟨j, hj.1⟩
      rw [rectDiagonal_mulVec σ _ ⟨j, hj.1⟩ j.isLt, Pi.zero_apply, mul_eq_zero] at hzero
      rw [(hzero.resolve_left hj.2 : (star V *ᵥ x) j = 0), zero_smul]
      exact Submodule.zero_mem _
  · rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, mulVecLin_apply, key, star_mulVec_transpose_apply hV]
    funext i
    rw [mulVec_single, Pi.zero_apply, op_smul_eq_smul, Pi.smul_apply, col_apply,
      rectDiagonal_apply, smul_eq_mul, one_mul]
    split_ifs with hij
    · rcases hj with hj | hj
      · exact absurd (lt_of_eq_of_lt hij.symm i.isLt) (not_lt.2 hj)
      · rw [hij]
        exact hj
    · rfl

/-- **The range from a singular value decomposition.** Let $A \in \mathbb{K}^{m \times n}$, let $U$
and $V$ be unitary with columns $u_i$ of $U$, and let $\sigma : \mathbb{N} \to \mathbb{K}$
satisfy $U^H A V = \operatorname{diag}(\sigma) \in \mathbb{K}^{m \times n}$. Then
$$\operatorname{range} A = \operatorname{span}\{u_i : i < n \text{ and } \sigma_i \neq 0\}.$$
This is in [quarteroni2000numerical], §1.9.

For sorted singular values and $r = \operatorname{rank} A$, the spanning columns are
$u_1, \dots, u_r$ in the numbering from $1$ of the source. -/
theorem range_mulVecLin_eq_span_of_svd {A : Matrix (Fin m) (Fin n) 𝕜}
    {U : Matrix (Fin m) (Fin m) 𝕜} {V : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin m) 𝕜)
    (hV : V ∈ unitaryGroup (Fin n) 𝕜) {σ : ℕ → 𝕜} (h : star U * A * V = rectDiagonal σ) :
    LinearMap.range A.mulVecLin
      = Submodule.span 𝕜 (Uᵀ '' {i : Fin m | (i : ℕ) < n ∧ σ i ≠ 0}) := by
  have hA : A = U * (rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜) * star V :=
    eq_mul_mul_star_of_star_mul_mul_eq hU hV h
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, rfl⟩
    rw [mulVecLin_apply, hA, ← mulVec_mulVec, ← mulVec_mulVec,
      eq_sum_star_mulVec_smul_transpose hU (U *ᵥ _), mulVec_mulVec, mem_unitaryGroup_iff'.1 hU,
      one_mulVec]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < n ∧ σ i ≠ 0
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · have hzero : (rectDiagonal σ *ᵥ (star V *ᵥ x)) i = 0 := by
        by_cases hin : (i : ℕ) < n
        · rw [rectDiagonal_mulVec _ _ _ hin]
          have : σ i = 0 := by
            by_contra h0
            exact hi ⟨hin, h0⟩
          rw [this, zero_mul]
        · exact rectDiagonal_mulVec_of_le _ _ _ (not_lt.1 hin)
      rw [hzero, zero_smul]
      exact Submodule.zero_mem _
  · rintro _ ⟨i, ⟨hin, hi⟩, rfl⟩
    refine ⟨V *ᵥ Pi.single ⟨i, hin⟩ (σ i)⁻¹, ?_⟩
    rw [mulVecLin_apply, hA, mulVec_mulVec, Matrix.mul_assoc (U * rectDiagonal σ),
      mem_unitaryGroup_iff'.1 hV, Matrix.mul_one, ← mulVec_mulVec]
    have hS : rectDiagonal σ *ᵥ Pi.single (⟨i, hin⟩ : Fin n) (σ i)⁻¹ = Pi.single i 1 := by
      funext k
      rw [mulVec_single, op_smul_eq_smul, Pi.smul_apply, col_apply, rectDiagonal_apply,
        smul_eq_mul, Fin.val_mk]
      by_cases hki : k = i
      · subst hki
        rw [ite_eq_left rfl, Pi.single_eq_same, inv_mul_cancel₀ hi]
      · rw [ite_eq_right (fun hk => hki (Fin.ext hk)), mul_zero, Pi.single_eq_of_ne hki]
    rw [hS, mulVec_single_one]
    rfl

end SVD2

/-!
### Uniqueness of the singular values

The singular values of every factorization $U^H A V = \Sigma$ are determined by $A$: the multiset of
their squares is the multiset of eigenvalues of $A^H A$, and when they are sorted they are Mathlib's
`LinearMap.singularValues`. The proofs compare characteristic polynomials, which the unitary
similarity $A^H A = V \Sigma^H \Sigma V^H$ preserves.
-/

section Uniqueness

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The singular values from a unitary diagonalization of the Gram matrix.** Let
$A \in \mathbb{K}^{m \times n}$, let $U \in \mathbb{K}^{n \times n}$ be unitary, and let
$d : n \to \mathbb{R}$ with $d_i \ge 0$ satisfy
$$A^H A = U \operatorname{diag}(d_i^2) U^H.$$
Then there is a permutation $e$ of $n$ with $\sigma_{e(i)}(A) = d_i$ for every $i$.

The characteristic polynomial of $A^H A$ is that of $\operatorname{diag}(d_i^2)$, so the
multiset of eigenvalues of $A^H A$ is that of the $d_i^2$, and `Matrix.colSingularValues` are
their square roots. -/
theorem exists_equiv_colSingularValues_eq_of_conjTranspose_mul_self_eq {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] {A : Matrix m n 𝕜} {U : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜)
    {d : n → ℝ} (hd : ∀ i, 0 ≤ d i)
    (h : Aᴴ * A = U * diagonal (fun i => ((d i ^ 2 : ℝ) : 𝕜)) * star U) :
    ∃ e : n ≃ n, ∀ i, A.colSingularValues (e i) = d i := by
  set hG := isHermitian_conjTranspose_mul_self A with hGdef
  have hchar : (Aᴴ * A).charpoly = (diagonal fun i => ((d i ^ 2 : ℝ) : 𝕜)).charpoly := by
    rw [h, charpoly_unitary_conj hU]
  have hmult : Multiset.map hG.eigenvalues Finset.univ.val
      = Multiset.map (fun i => d i ^ 2) Finset.univ.val := by
    have h1 := hG.roots_charpoly_eq_eigenvalues
    rw [hchar, roots_charpoly_diagonal] at h1
    have h2 := congrArg (Multiset.map RCLike.re) h1
    simpa [Multiset.map_map, Function.comp_def] using h2.symm
  obtain ⟨e, he⟩ := exists_equiv_of_map_univ_val_eq hmult
  exact ⟨e, fun i => by rw [colSingularValues, he i, Real.sqrt_sq (hd i)]⟩

/-- **The singular values of a Hermitian matrix are the moduli of its eigenvalues.** Let
$A \in \mathbb{K}^{n \times n}$ be Hermitian with eigenvalues $\lambda_i$. Then there is a
permutation $e$ of $n$ with
$$\sigma_{e(i)}(A) = |\lambda_i(A)| \qquad \text{for every } i.$$
This is in [quarteroni2000numerical], §1.9, after (1.10).

The eigenvalues are `Matrix.IsHermitian.eigenvalues`. Since $A^H A = A^2$ has the characteristic
polynomial of $\operatorname{diag}(\lambda_i^2)$, this is a case of
`Matrix.exists_equiv_colSingularValues_eq_of_conjTranspose_mul_self_eq`. -/
theorem IsHermitian.exists_equiv_colSingularValues_eq_abs_eigenvalues {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ e : n ≃ n, ∀ i, A.colSingularValues (e i) = |hA.eigenvalues i| := by
  refine exists_equiv_colSingularValues_eq_of_conjTranspose_mul_self_eq
    hA.eigenvectorUnitary.2 (fun i => abs_nonneg _) ?_
  have hAA : Aᴴ * A = hA.eigenvectorUnitary * diagonal (fun i => ((|hA.eigenvalues i| ^ 2 : ℝ) : 𝕜))
      * star hA.eigenvectorUnitary := by
    conv_lhs => rw [hA.eq, hA.spectral_theorem, ← map_mul, Unitary.conjStarAlgAut_apply,
      diagonal_mul_diagonal]
    congr 2
    funext i
    simp [Function.comp_apply, sq]
  rw [hAA, Unitary.coe_star]

variable {m n : ℕ}

/-- **Uniqueness of the singular values.** Let $A \in \mathbb{K}^{m \times n}$, let $U$ and $V$ be
unitary, and let $\sigma : \mathbb{N} \to \mathbb{R}$ be nonincreasing and nonnegative with
$$U^H A V = \operatorname{diag}(\sigma) \in \mathbb{K}^{m \times n}.$$
Then for every $i < \min(m, n)$, $\sigma_i$ is the sorted singular value $\sigma_i(A)$. This is
(1.10) of [quarteroni2000numerical], $\sigma_i(A) = \sqrt{\lambda_i(A^H A)}$.

The sorted singular values are `(toEuclideanLin A).singularValues`. From
$A^H A = V \Sigma^H \Sigma V^H$, the characteristic polynomial of $A^H A$ is that of the
diagonal matrix of the $\sigma_i^2$, padded by zeros, which is a nonincreasing family. The
characterization of sorted eigenvalues `LinearMap.IsSymmetric.eigenvalues_eq_of_antitone` then
identifies it with the eigenvalues of $A^H A$. -/
theorem singularValues_eq_of_svd {A : Matrix (Fin m) (Fin n) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜}
    {V : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin m) 𝕜)
    (hV : V ∈ unitaryGroup (Fin n) 𝕜) {σ : ℕ → ℝ} (hσ : Antitone σ) (hσ0 : ∀ i, 0 ≤ σ i)
    (h : star U * A * V = rectDiagonal fun i => ((σ i : ℝ) : 𝕜)) {i : ℕ} (him : i < m)
    (hin : i < n) : (toEuclideanLin A).singularValues i = σ i := by
  have hA : A = U * (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin m) (Fin n) 𝕜) * star V :=
    eq_mul_mul_star_of_star_mul_mul_eq hU hV h
  -- the padded squares, an antitone family on `Fin n`
  set d : Fin n → ℝ := fun j => if (j : ℕ) < m then σ j ^ 2 else 0 with hd
  have hdanti : Antitone d := by
    intro j k hjk
    have hjk' : (j : ℕ) ≤ k := hjk
    simp only [hd]
    split_ifs with hk hj hj
    · exact pow_le_pow_left₀ (hσ0 _) (hσ hjk') 2
    · exact absurd (lt_of_le_of_lt hjk' hk) hj
    · positivity
    · exact le_rfl
  -- `Aᴴ A = V diag(d) Vᴴ`
  have hgram : Aᴴ * A = V * diagonal (fun j => ((d j : ℝ) : 𝕜)) * star V := by
    have hSS : (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin m) (Fin n) 𝕜)ᴴ
        * rectDiagonal (fun i => ((σ i : ℝ) : 𝕜)) = diagonal fun j => ((d j : ℝ) : 𝕜) := by
      rw [conjTranspose_rectDiagonal_mul_self]
      congr 1
      funext j
      simp only [hd]
      split_ifs <;> simp [sq, RCLike.conj_ofReal]
    have hUU : ∀ {k : Type} (X : Matrix (Fin m) k 𝕜), Uᴴ * (U * X) = X := fun X => by
      rw [← Matrix.mul_assoc, ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hU, Matrix.one_mul]
    rw [hA, conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose (star V), star_star]
    simp only [Matrix.mul_assoc]
    rw [hUU, ← Matrix.mul_assoc (rectDiagonal _)ᴴ, hSS]
  -- the operator `T† T` and the reference operator `diag(d)`
  set T : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin m) := toEuclideanLin A with hT
  have hTsym := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := finrank_euclideanSpace_fin
  have hDsym : (toEuclideanLin (diagonal fun j => ((d j : ℝ) : 𝕜))).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.2
      (isHermitian_diagonal_iff.2 fun i => RCLike.conj_ofReal (d i))
  have hTT : LinearMap.adjoint T ∘ₗ T = toEuclideanLin (Aᴴ * A) := by
    rw [toEuclideanLin_mul, toEuclideanLin_conjTranspose_eq_adjoint]
  have hchar : (LinearMap.adjoint T ∘ₗ T).charpoly
      = (toEuclideanLin (diagonal fun j => ((d j : ℝ) : 𝕜))).charpoly := by
    rw [hTT, toEuclideanLin, toLpLin_eq_toLin, Matrix.charpoly_toLin, Matrix.charpoly_toLin,
      hgram, charpoly_unitary_conj hV]
  have heig : hTsym.eigenvalues hn = d := by
    rw [(hTsym.eigenvalues_eq_eigenvalues_iff hn hDsym hn).2 hchar]
    refine hDsym.eigenvalues_eq_of_antitone hn hdanti ?_
    rw [toEuclideanLin, toLpLin_eq_toLin, Matrix.charpoly_toLin]
    exact roots_charpoly_diagonal _
  rw [T.singularValues_of_lt hn hin, heig]
  simp only [hd, ite_eq_left him]
  exact Real.sqrt_sq (hσ0 i)

end Uniqueness

/-! ### Expansions along the columns of a factorization -/

section Expansion

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-- Let $U \in \mathbb{K}^{m \times m}$ with columns $u_i$, and let $b \in \mathbb{K}^m$. The
coordinates of $U^H b$ are the inner products with the columns:
$(U^H b)_i = \langle u_i, b \rangle$. -/
theorem star_mulVec_apply_eq_inner (U : Matrix (Fin m) (Fin m) 𝕜) (b : EuclideanSpace 𝕜 (Fin m))
    (i : Fin m) :
    (star U *ᵥ WithLp.ofLp b) i
      = inner 𝕜 (WithLp.toLp 2 (Uᵀ i) : EuclideanSpace 𝕜 (Fin m)) b := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [mulVec, dotProduct, star_apply, transpose_apply, Pi.star_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **The action of $V \Sigma U^H$ in the columns of $U$ and $V$.** Let
$U \in \mathbb{K}^{m \times m}$ and $V \in \mathbb{K}^{n \times n}$ with columns $u_i$ and
$v_i$, and let $\Sigma = \operatorname{diag}(\tau) \in \mathbb{K}^{n \times m}$. For every
$b \in \mathbb{K}^m$,
$$V \Sigma U^H b = \sum_{i < \min(m, n)} \tau_i \langle u_i, b \rangle \, v_i.$$

This expansion gives the formulas for $A^+$ and for the Tikhonov matrix in terms of singular
vectors. -/
theorem toEuclideanLin_mul_rectDiagonal_mul_star_apply (U : Matrix (Fin m) (Fin m) 𝕜)
    (V : Matrix (Fin n) (Fin n) 𝕜) (τ : ℕ → 𝕜) (b : EuclideanSpace 𝕜 (Fin m)) :
    toEuclideanLin (V * (rectDiagonal τ : Matrix (Fin n) (Fin m) 𝕜) * star U) b
      = ∑ i : Fin (min m n), τ i • inner 𝕜
          (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) : EuclideanSpace 𝕜 (Fin m)) b •
          (WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i)) : EuclideanSpace 𝕜 (Fin n)) := by
  set c := star U *ᵥ WithLp.ofLp b with hc
  have hcoord : ∀ j : Fin n, ((rectDiagonal τ : Matrix (Fin n) (Fin m) 𝕜) *ᵥ c) j
      = if h : (j : ℕ) < m then τ j * c ⟨j, h⟩ else 0 := by
    intro j
    split_ifs with hj
    · exact rectDiagonal_mulVec τ c j hj
    · exact rectDiagonal_mulVec_of_le τ c j (not_lt.1 hj)
  apply WithLp.ofLp_injective
  funext k
  rw [ofLp_toEuclideanLin, ← mulVec_mulVec, ← mulVec_mulVec, WithLp.ofLp_sum,
    Finset.sum_apply]
  set G : Fin n → 𝕜 := fun j => if h : (j : ℕ) < m then τ j * (c ⟨j, h⟩ * V k j) else 0
    with hG
  have hR : ∀ i : Fin (min m n), (WithLp.ofLp (τ i • inner 𝕜
      (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) : EuclideanSpace 𝕜 (Fin m)) b •
      (WithLp.toLp 2 (Vᵀ (Fin.castLE (min_le_right m n) i)) : EuclideanSpace 𝕜 (Fin n)))) k
        = G (Fin.castLE (min_le_right m n) i) := by
    intro i
    have him : (i : ℕ) < m := lt_of_lt_of_le i.isLt (min_le_left m n)
    simp only [hG, Fin.val_castLE, him, ↓reduceDIte, WithLp.ofLp_smul, Pi.smul_apply,
      transpose_apply, smul_eq_mul]
    rw [hc, star_mulVec_apply_eq_inner]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hR i, Fin.sum_castLE_eq_sum_ite, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoord, hG]
  by_cases hj : (j : ℕ) < m
  · simp only [hj, lt_min hj j.isLt, ↓reduceDIte, ↓reduceIte]
    ring
  · have hj' : ¬ (j : ℕ) < min m n := fun h => hj (lt_of_lt_of_le h (min_le_left m n))
    simp only [hj, hj', ↓reduceDIte, ↓reduceIte, mul_zero]

/-- **Parseval's identity for $V \Sigma U^H b$.** Let $U \in \mathbb{K}^{m \times m}$ with columns
$u_i$, let $V \in \mathbb{K}^{n \times n}$ be unitary, and let $\Sigma =
\operatorname{diag}(\tau) \in \mathbb{K}^{n \times m}$. For every $b \in \mathbb{K}^m$,
$$\|V \Sigma U^H b\|^2 = \sum_{i < \min(m, n)} |\tau_i|^2 \, |\langle u_i, b \rangle|^2.$$
-/
theorem norm_sq_toEuclideanLin_mul_rectDiagonal_mul_star_apply (U : Matrix (Fin m) (Fin m) 𝕜)
    {V : Matrix (Fin n) (Fin n) 𝕜} (hV : V ∈ unitaryGroup (Fin n) 𝕜) (τ : ℕ → 𝕜)
    (b : EuclideanSpace 𝕜 (Fin m)) :
    ‖toEuclideanLin (V * (rectDiagonal τ : Matrix (Fin n) (Fin m) 𝕜) * star U) b‖ ^ 2
      = ∑ i : Fin (min m n), ‖τ i‖ ^ 2 * ‖inner 𝕜
          (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) : EuclideanSpace 𝕜 (Fin m))
            b‖ ^ 2 := by
  have hV' : Vᴴ * V = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hV
  have ho := (orthonormal_toLp_transpose_of_conjTranspose_mul_self_eq_one hV').comp _
    (Fin.castLE_injective (min_le_right m n))
  rw [toEuclideanLin_mul_rectDiagonal_mul_star_apply]
  simp_rw [smul_smul]
  have := ho.norm_sum_smul_sq fun i => τ i * inner 𝕜
    (WithLp.toLp 2 (Uᵀ (Fin.castLE (min_le_left m n) i)) : EuclideanSpace 𝕜 (Fin m)) b
  simp only [Function.comp_apply, norm_mul, mul_pow] at this ⊢
  exact this

/-- Entrywise conjugation preserves orthonormality of Euclidean vectors: if $(v_k)$ is orthonormal,
so is $(\bar v_k)$, because $\langle \bar x, \bar y \rangle = \langle y, x \rangle$. -/
theorem orthonormal_toLp_star {ι p : Type*} [Fintype p] {v : ι → EuclideanSpace 𝕜 p}
    (hv : Orthonormal 𝕜 v) : Orthonormal 𝕜 fun k => WithLp.toLp 2 (star ⇑(v k)) := by
  classical
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_toLp, star_star,
    dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, hv j i]
  exact if_congr eq_comm rfl rfl

/-- **The sorted singular expansion.** Let $M \in \mathbb{K}^{p \times q}$ and
$r = \operatorname{rank} M$. There are orthonormal families $u_0, \dots, u_{r-1}$ in
$\mathbb{K}^p$ and $v_0, \dots, v_{r-1}$ in $\mathbb{K}^q$ such that the sorted singular values
$\sigma_0, \dots, \sigma_{r-1}$ of $M$ are positive and
$$M = \sum_{k < r} \sigma_k \, u_k v_k^H.$$

The index types are arbitrary finite types, and $\sigma_k$ is `M.sortedSingularValues k`. The
vectors $v_k$ are right singular vectors relabelled by
`Matrix.exists_equiv_colSingularValues_eq_sortedSingularValues`. -/
theorem exists_eq_sum_sortedSingularValues_smul_vecMulVec {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq q] (M : Matrix p q 𝕜) :
    ∃ (u : Fin M.rank → EuclideanSpace 𝕜 p) (v : Fin M.rank → EuclideanSpace 𝕜 q),
      Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧ (∀ k : Fin M.rank, 0 < M.sortedSingularValues k) ∧
      M = ∑ k : Fin M.rank,
        ((M.sortedSingularValues k : ℝ) : 𝕜) • vecMulVec ⇑(u k) (star ⇑(v k)) := by
  classical
  obtain ⟨e, he⟩ := M.exists_equiv_colSingularValues_eq_sortedSingularValues
  have hr : M.rank ≤ Fintype.card q := (rank_le_card_width M).trans_eq rfl
  set b := M.rightSingularBasis with hb
  let w : Fin M.rank → q := fun k => e (Fin.castLE hr k)
  have hw : Function.Injective w := e.injective.comp (Fin.castLE_injective hr)
  have hσw : ∀ k : Fin M.rank, M.colSingularValues (w k) = M.sortedSingularValues k :=
    fun k => he _
  have hpos : ∀ k : Fin M.rank, 0 < M.sortedSingularValues k := fun k =>
    lt_of_le_of_ne (M.sortedSingularValues_nonneg k)
      (Ne.symm ((M.sortedSingularValues_eq_zero_iff_rank_le k).not.2 (not_le.2 k.2)))
  have hne : ∀ k : Fin M.rank, ((M.sortedSingularValues k : ℝ) : 𝕜) ≠ 0 := fun k => by
    exact_mod_cast (hpos k).ne'
  refine ⟨fun k : Fin M.rank => ((M.sortedSingularValues k : ℝ) : 𝕜)⁻¹ • toEuclideanLin M (b (w k)),
    fun k => b (w k), ?_, b.orthonormal.comp w hw, hpos, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    rw [inner_smul_left, inner_smul_right, M.inner_toEuclideanLin_rightSingularBasis]
    simp only [hw.eq_iff]
    split_ifs with h
    · subst h
      rw [hσw, map_inv₀, RCLike.conj_ofReal]
      have := hne i
      push_cast
      field_simp
    · simp
  · -- the expansion along all right singular vectors
    have hexp : M = ∑ i, vecMulVec ⇑(toEuclideanLin M (b i)) (star ⇑(b i)) := by
      have hU := M.rightSingularUnitary_mul_star
      ext x y
      conv_lhs => rw [← Matrix.mul_one M, ← hU]
      simp only [Matrix.mul_apply, star_apply, Matrix.sum_apply, vecMulVec_apply,
        ofLp_toEuclideanLin, mulVec, dotProduct, Pi.star_apply, rightSingularUnitary,
        IsHermitian.eigenvectorUnitary_apply, hb, rightSingularBasis, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun z _ => by ring
    conv_lhs => rw [hexp]
    rw [← e.sum_comp]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _
      (fun c hc => ?_) (fun k => ?_)
    · have hc' : M.rank ≤ (c : ℕ) := by
        by_contra hlt
        exact hc ⟨⟨c, not_le.1 hlt⟩, rfl⟩
      rw [M.toEuclideanLin_rightSingularBasis_eq_zero
        (by rw [he]; exact (M.sortedSingularValues_eq_zero_iff_rank_le c).2 hc')]
      ext
      simp
    · ext x y
      simp only [Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, WithLp.ofLp_smul, Pi.smul_apply]
      have := hne k
      field_simp
      rfl

end Expansion

/-!
### Singular value decompositions as a specification

`Matrix.IsSVD A U σ V` collects the hypotheses of the consequences above:
$U^H A V = \operatorname{diag}(\sigma)$ with $U$, $V$ unitary and $\sigma$ nonincreasing and
nonnegative. It is the output condition of every step "compute the SVD" of an algorithm. The results
below take it as hypothesis rather than "the" SVD, which is not unique.
-/

section IsSVD

variable {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ}

/-- **A singular value decomposition, as a specification.** Let $A \in \mathbb{K}^{m \times n}$,
$U \in \mathbb{K}^{m \times m}$, $V \in \mathbb{K}^{n \times n}$ and
$\sigma : \mathbb{N} \to \mathbb{R}$. Then $(U, \sigma, V)$ is a **singular value
decomposition** of $A$ if $U$ and $V$ are unitary,
$$U^H A V = \Sigma = \operatorname{diag}(\sigma_0, \sigma_1, \dots)
  \in \mathbb{K}^{m \times n},$$
and $\sigma$ is nonincreasing and nonnegative. This is the factorization of Theorem 2.4.1 of
[golub2013matrix].

The structure extends `Matrix.IsUnitaryEquiv`, which holds the unitarity of $U$ and $V$ and the
factorization. The values $\sigma_i$ for $i \ge \min(m, n)$ are not used by
`Matrix.rectDiagonal`, and only the two order conditions constrain them. -/
structure IsSVD (A : Matrix (Fin m) (Fin n) 𝕜) (U : Matrix (Fin m) (Fin m) 𝕜) (σ : ℕ → ℝ)
    (V : Matrix (Fin n) (Fin n) 𝕜) : Prop
    extends IsUnitaryEquiv A U (rectDiagonal fun i => ((σ i : ℝ) : 𝕜)) V where
  /-- The diagonal is nonincreasing: $\sigma_j \le \sigma_i$ for $i \le j$. -/
  antitone : Antitone σ
  /-- The diagonal entries are nonnegative: $\sigma_i \ge 0$ for every $i$. -/
  nonneg : ∀ i, 0 ≤ σ i

/-- **Every matrix has a singular value decomposition.** For every $A \in \mathbb{K}^{m \times n}$
there are $U$, $\sigma$ and $V$ such that $(U, \sigma, V)$ is a singular value decomposition of
$A$.

The diagonal is the sorted singular values, from `Matrix.exists_svd`. -/
theorem exists_isSVD (A : Matrix (Fin m) (Fin n) 𝕜) : ∃ U σ V, IsSVD A U σ V := by
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  exact ⟨U, A.sortedSingularValues, V, ⟨hU, hV, h⟩, A.sortedSingularValues_antitone,
    A.sortedSingularValues_nonneg⟩

variable {A : Matrix (Fin m) (Fin n) 𝕜} {U : Matrix (Fin m) (Fin m) 𝕜} {σ : ℕ → ℝ}
  {V : Matrix (Fin n) (Fin n) 𝕜}

/-- If $(U, \sigma, V)$ is a singular value decomposition of $A$, then $A = U \Sigma V^H$ with
$\Sigma = \operatorname{diag}(\sigma) \in \mathbb{K}^{m \times n}$. -/
theorem IsSVD.eq_mul_mul_star (h : IsSVD A U σ V) :
    A = U * (rectDiagonal fun i => ((σ i : ℝ) : 𝕜) : Matrix (Fin m) (Fin n) 𝕜) * star V :=
  eq_mul_mul_star_of_star_mul_mul_eq h.mem_unitaryGroup_left h.mem_unitaryGroup_right
    h.star_mul_mul

/-- **The diagonal of every SVD is the sorted singular values.** If $(U, \sigma, V)$ is a singular
value decomposition of $A \in \mathbb{K}^{m \times n}$, then $\sigma_i = \sigma_i(A)$, the
sorted singular value, for every $i < \min(m, n)$. The factorization is that of Theorem 2.4.1 of
[golub2013matrix].

It is `Matrix.singularValues_eq_of_svd`. -/
theorem IsSVD.singularValues_eq (h : IsSVD A U σ V) {i : ℕ} (him : i < m) (hin : i < n) :
    σ i = A.sortedSingularValues i :=
  (singularValues_eq_of_svd h.mem_unitaryGroup_left h.mem_unitaryGroup_right h.antitone h.nonneg
    h.star_mul_mul him hin).symm

/-- **The pseudoinverse from an SVD.** If $(U, \sigma, V)$ is a singular value decomposition of
$A \in \mathbb{K}^{m \times n}$, then
$$A^+ = V \operatorname{diag}(\sigma_0^{-1}, \sigma_1^{-1}, \dots) U^H,$$
with the diagonal matrix in $\mathbb{K}^{n \times m}$ and $0^{-1} = 0$. This is
`Matrix.pinv_eq_of_svd`. -/
theorem IsSVD.pinv_eq (h : IsSVD A U σ V) :
    A.pinv = V * (rectDiagonal fun i => ((σ i : 𝕜))⁻¹ : Matrix (Fin n) (Fin m) 𝕜) * star U :=
  pinv_eq_of_svd h.mem_unitaryGroup_left h.mem_unitaryGroup_right h.star_mul_mul

/-- **The kernel from an SVD.** If $(U, \sigma, V)$ is a singular value decomposition of
$A \in \mathbb{K}^{m \times n}$ and $V$ has columns $v_j$, then
$$\ker A = \operatorname{span}\{v_j : j \ge m \text{ or } \sigma_j = 0\}.$$
This is `Matrix.ker_mulVecLin_eq_span_of_svd`. -/
theorem IsSVD.ker_mulVecLin_eq_span (h : IsSVD A U σ V) :
    LinearMap.ker A.mulVecLin
      = Submodule.span 𝕜 (Vᵀ '' {j : Fin n | m ≤ (j : ℕ) ∨ σ j = 0}) := by
  rw [ker_mulVecLin_eq_span_of_svd h.mem_unitaryGroup_left h.mem_unitaryGroup_right
    h.star_mul_mul]
  simp only [RCLike.ofReal_eq_zero]

/-- **The range from an SVD.** If $(U, \sigma, V)$ is a singular value decomposition of
$A \in \mathbb{K}^{m \times n}$ and $U$ has columns $u_i$, then
$$\operatorname{range} A = \operatorname{span}\{u_i : i < n \text{ and } \sigma_i \neq 0\}.$$
This is `Matrix.range_mulVecLin_eq_span_of_svd`. -/
theorem IsSVD.range_mulVecLin_eq_span (h : IsSVD A U σ V) :
    LinearMap.range A.mulVecLin
      = Submodule.span 𝕜 (Uᵀ '' {i : Fin m | (i : ℕ) < n ∧ σ i ≠ 0}) := by
  rw [range_mulVecLin_eq_span_of_svd h.mem_unitaryGroup_left h.mem_unitaryGroup_right
    h.star_mul_mul]
  simp only [ne_eq, RCLike.ofReal_eq_zero]

/-- **An SVD of $A^H$.** If $(U, \sigma, V)$ is a singular value decomposition of
$A \in \mathbb{K}^{m \times n}$, then $(V, \sigma, U)$ is a singular value decomposition of
$A^H$: $V^H A^H U = \Sigma^H = \operatorname{diag}(\sigma) \in \mathbb{K}^{n \times m}$. -/
theorem IsSVD.conjTranspose (h : IsSVD A U σ V) : IsSVD Aᴴ V σ U where
  mem_unitaryGroup_left := h.mem_unitaryGroup_right
  mem_unitaryGroup_right := h.mem_unitaryGroup_left
  antitone := h.antitone
  nonneg := h.nonneg
  star_mul_mul := by
    have h1 := congrArg (fun M : Matrix (Fin m) (Fin n) 𝕜 => Mᴴ) h.star_mul_mul
    simp only [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
      rectDiagonal_conjTranspose] at h1
    rw [star_eq_conjTranspose, Matrix.mul_assoc, h1]
    congr 1
    funext i
    simp

/-- **The least singular value from an SVD.** Let $0 < n \le m$. If $(U, \sigma, V)$ is a singular
value decomposition of $A \in \mathbb{K}^{m \times n}$, then
$\min_i \sigma_i(A) = \sigma_{n-1}$, the last diagonal entry. The minimum is over the
column-indexed singular values. -/
theorem IsSVD.iInf_colSingularValues_eq (h : IsSVD A U σ V) (hn : 0 < n) (hnm : n ≤ m) :
    ⨅ i, A.colSingularValues i = σ (n - 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← sortedSingularValues_eq_iInf_colSingularValues, Fintype.card_fin,
    h.singularValues_eq (by omega) (by omega)]

/-- **$\|Ax\|^2$ in the right singular coordinates.** If $(U, \sigma, V)$ is a singular value
decomposition of $A \in \mathbb{K}^{m \times n}$, then for every $x \in \mathbb{K}^n$,
$$\|Ax\|^2 = \sum_{i < \min(n, m)} \sigma_i^2 \, |(V^H x)_i|^2.$$
-/
theorem IsSVD.norm_sq_toEuclideanLin_apply (h : IsSVD A U σ V) (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖toEuclideanLin A x‖ ^ 2 = ∑ i : Fin (min n m),
      σ i ^ 2 * ‖(star V *ᵥ WithLp.ofLp x) (Fin.castLE (min_le_left n m) i)‖ ^ 2 := by
  rw [h.eq_mul_mul_star,
    norm_sq_toEuclideanLin_mul_rectDiagonal_mul_star_apply _ h.mem_unitaryGroup_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mulVec_apply_eq_inner, RCLike.norm_ofReal, sq_abs]

/-- **$\|Ax\|^2$ in the right singular coordinates for a tall matrix.** Let $n \le m$. If
$(U, \sigma, V)$ is a singular value decomposition of $A \in \mathbb{K}^{m \times n}$, then
every coordinate is weighted: for every $x \in \mathbb{K}^n$,
$$\|Ax\|^2 = \sum_{i < n} \sigma_i^2 \, |(V^H x)_i|^2.$$
-/
theorem IsSVD.norm_sq_toEuclideanLin_apply_of_le (h : IsSVD A U σ V) (hnm : n ≤ m)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖toEuclideanLin A x‖ ^ 2 = ∑ i : Fin n, σ i ^ 2 * ‖(star V *ᵥ WithLp.ofLp x) i‖ ^ 2 := by
  rw [h.norm_sq_toEuclideanLin_apply]
  refine (Fin.sum_castLE_eq_sum_ite (min_le_left n m)
    fun j : Fin n => σ j ^ 2 * ‖(star V *ᵥ WithLp.ofLp x) j‖ ^ 2).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ite_eq_left (lt_min i.isLt (lt_of_lt_of_le i.isLt hnm))]

/-- **The minimizers of $\|Ax\| / \|x\|$ in coordinates.** Let $n \le m$ and let $(U, \sigma, V)$ be
a singular value decomposition of $A \in \mathbb{K}^{m \times n}$. Let $r \in \mathbb{N}$
satisfy $\sigma_{n-1} < \sigma_j$ for all $j < r$ and $\sigma_r = \sigma_{n-1}$. Then for every
$x \in \mathbb{K}^n$,
$$\|Ax\| = \sigma_{n-1} \|x\| \iff (V^H x)_j = 0 \text{ for all } j < r.$$
This is in [golub2013matrix], §6.3.2.

The difference $\|Ax\|^2 - \sigma_{n-1}^2 \|x\|^2 = \sum_j (\sigma_j^2 - \sigma_{n-1}^2) |(V^H
x)_j|^2$ is a sum of nonnegative terms, and the weight is positive exactly for $j < r$. -/
theorem IsSVD.norm_toEuclideanLin_eq_iff (h : IsSVD A U σ V) (hnm : n ≤ m) {r : ℕ}
    (hgap : ∀ j < r, σ (n - 1) < σ j) (heq : σ r = σ (n - 1)) (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖toEuclideanLin A x‖ = σ (n - 1) * ‖x‖ ↔
      ∀ j : Fin n, (j : ℕ) < r → (star V *ᵥ WithLp.ofLp x) j = 0 := by
  set c := star V *ᵥ WithLp.ofLp x with hc
  set s := σ (n - 1)
  have hs : 0 ≤ s := h.nonneg _
  have hx : ‖x‖ ^ 2 = ∑ j : Fin n, ‖c j‖ ^ 2 := by
    rw [← norm_toEuclideanLin_apply_of_mem_unitaryGroup
      (Unitary.star_mem h.mem_unitaryGroup_right) x, EuclideanSpace.norm_sq_eq]
    rfl
  have hle : ∀ j : Fin n, s ≤ σ j := fun j => h.antitone (Nat.le_sub_one_of_lt j.isLt)
  have hge : ∀ j : Fin n, r ≤ (j : ℕ) → σ j = s := fun j hj =>
    le_antisymm (heq ▸ h.antitone hj) (hle j)
  have hsum : ‖toEuclideanLin A x‖ ^ 2 - (s * ‖x‖) ^ 2
      = ∑ j : Fin n, (σ j ^ 2 - s ^ 2) * ‖c j‖ ^ 2 := by
    rw [h.norm_sq_toEuclideanLin_apply_of_le hnm, mul_pow, hx, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hnn : ∀ j : Fin n, 0 ≤ (σ j ^ 2 - s ^ 2) * ‖c j‖ ^ 2 := fun j =>
    mul_nonneg (sub_nonneg.2 (pow_le_pow_left₀ hs (hle j) 2)) (sq_nonneg _)
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hs (norm_nonneg _)), ← sub_eq_zero, hsum,
    Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j]
  constructor
  · intro h0 j hj
    have hpos : 0 < σ j ^ 2 - s ^ 2 :=
      sub_pos.2 (pow_lt_pow_left₀ (hgap j hj) hs two_ne_zero)
    have := h0 j (Finset.mem_univ j)
    rw [mul_eq_zero, or_iff_right hpos.ne', sq_eq_zero_iff, norm_eq_zero] at this
    exact this
  · intro h0 j _
    by_cases hj : (j : ℕ) < r
    · rw [h0 j hj, norm_zero]
      ring
    · rw [hge j (not_lt.1 hj), sub_self, zero_mul]

/-- **The span of the trailing columns of a unitary matrix** is cut out by the leading coordinates.
Let $V \in \mathbb{K}^{n \times n}$ be unitary with columns $v_j$, and let $r \in \mathbb{N}$.
For every $x \in \mathbb{K}^n$,
$$x \in \operatorname{span}\{v_j : j \ge r\} \iff (V^H x)_j = 0 \text{ for all } j < r.$$
-/
theorem mem_span_toLp_transpose_iff (hV : V ∈ unitaryGroup (Fin n) 𝕜) (r : ℕ)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    x ∈ Submodule.span 𝕜
        ((fun j => (WithLp.toLp 2 (Vᵀ j) : EuclideanSpace 𝕜 (Fin n))) '' {j | r ≤ (j : ℕ)}) ↔
      ∀ j : Fin n, (j : ℕ) < r → (star V *ᵥ WithLp.ofLp x) j = 0 := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      intro j hj
      have := congrFun (congrFun (mem_unitaryGroup_iff'.1 hV) j) k
      rw [Matrix.mul_apply, one_apply_ne (fun e => by rw [e] at hj; exact absurd hk (not_le.2 hj))]
        at this
      rw [← this]
      rfl
    | zero => intro j _; simp
    | add y z _ _ hy hz =>
      intro j hj
      rw [WithLp.ofLp_add, mulVec_add, Pi.add_apply, hy j hj, hz j hj, add_zero]
    | smul a y _ hy =>
      intro j hj
      rw [WithLp.ofLp_smul, mulVec_smul, Pi.smul_apply, hy j hj, smul_zero]
  · intro hx
    have hxV : x = toEuclideanLin V (WithLp.toLp 2 (star V *ᵥ WithLp.ofLp x)) := by
      rw [toEuclideanLin_toLp, mulVec_mulVec, mem_unitaryGroup_iff.1 hV, one_mulVec]
    rw [hxV, toEuclideanLin_apply_eq_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < r
    · rw [hx j hj, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, not_lt.1 hj, rfl⟩)

/-- **The minimizers of $\|Ax\| / \|x\|$ are the trailing right singular vectors.** Let $n \le m$
and let $(U, \sigma, V)$ be a singular value decomposition of $A \in \mathbb{K}^{m \times n}$,
where $V$ has columns $v_j$. Let $r \in \mathbb{N}$ satisfy $\sigma_{n-1} < \sigma_j$ for all
$j < r$ and $\sigma_r = \sigma_{n-1}$. Then for every $x \in \mathbb{K}^n$,
$$\|Ax\| = \sigma_{n-1} \|x\| \iff x \in \operatorname{span}\{v_j : j \ge r\}.$$
This is in [golub2013matrix], §6.3.2. -/
theorem IsSVD.norm_toEuclideanLin_eq_iff_mem_span (h : IsSVD A U σ V) (hnm : n ≤ m) {r : ℕ}
    (hgap : ∀ j < r, σ (n - 1) < σ j) (heq : σ r = σ (n - 1)) (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖toEuclideanLin A x‖ = σ (n - 1) * ‖x‖ ↔ x ∈ Submodule.span 𝕜
      ((fun j => (WithLp.toLp 2 (Vᵀ j) : EuclideanSpace 𝕜 (Fin n))) '' {j | r ≤ (j : ℕ)}) := by
  rw [h.norm_toEuclideanLin_eq_iff hnm hgap heq,
    mem_span_toLp_transpose_iff h.mem_unitaryGroup_right]

/-- Let $U \in \mathbb{K}^{m \times m}$, $V \in \mathbb{K}^{n \times n}$,
$\sigma : \mathbb{N} \to \mathbb{R}$ and $k \in \mathbb{N}$. The **rank-$k$ truncation** of the
factorization is
$$A_k = U \Sigma_k V^H,
  \qquad \Sigma_k = \operatorname{diag}(\sigma_0, \dots, \sigma_{k-1}, 0, 0, \dots)
  \in \mathbb{K}^{m \times n}.$$
This is the matrix of [golub2013matrix], (2.4.3).

It is defined from the factors, because the SVD is not unique. For $k \le \min(m, n)$ it is
$\sum_{i < k} \sigma_i u_i v_i^H$ (`Matrix.svdTruncation_eq_sum`). -/
noncomputable def svdTruncation (U : Matrix (Fin m) (Fin m) 𝕜) (σ : ℕ → ℝ)
    (V : Matrix (Fin n) (Fin n) 𝕜) (k : ℕ) : Matrix (Fin m) (Fin n) 𝕜 :=
  U * (rectDiagonal (fun i => if i < k then (σ i : 𝕜) else 0) : Matrix (Fin m) (Fin n) 𝕜) *
    star V

/-- **The truncation as a sum of rank-one matrices.** Let $U \in \mathbb{K}^{m \times m}$ and
$V \in \mathbb{K}^{n \times n}$ with columns $u_i$ and $v_i$, let
$\sigma : \mathbb{N} \to \mathbb{R}$, and let $k \le m$ and $k \le n$. Then
$$U \Sigma_k V^H = \sum_{i < k} \sigma_i \, u_i v_i^H.$$
This is (2.4.3) of [golub2013matrix]. -/
theorem svdTruncation_eq_sum (U : Matrix (Fin m) (Fin m) 𝕜) (σ : ℕ → ℝ)
    (V : Matrix (Fin n) (Fin n) 𝕜) {k : ℕ} (hkm : k ≤ m) (hkn : k ≤ n) :
    svdTruncation U σ V k = ∑ i : Fin k,
      (σ i : 𝕜) • vecMulVec (U.col (Fin.castLE hkm i)) (star (V.col (Fin.castLE hkn i))) := by
  ext a b
  rw [svdTruncation, Matrix.mul_apply, Matrix.sum_apply]
  have hg : ∀ j : Fin n,
      (U * (rectDiagonal (fun i => if i < k then (σ i : 𝕜) else 0) :
        Matrix (Fin m) (Fin n) 𝕜)) a j * star V j b =
        if (j : ℕ) < k then (if h : (j : ℕ) < m then U a ⟨j, h⟩ * σ j else 0) * star (V b j)
        else 0 := by
    intro j
    rw [mul_rectDiagonal_apply, star_apply]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => hg j, ← Fin.sum_castLE_eq_sum_ite hkn]
  refine Finset.sum_congr rfl fun i _ => ?_
  have him : (i : ℕ) < m := lt_of_lt_of_le i.isLt hkm
  simp only [Fin.val_castLE, him, ↓reduceDIte, Matrix.smul_apply, vecMulVec_apply, col_apply,
    smul_eq_mul, Pi.star_apply]
  rw [show (⟨i, him⟩ : Fin m) = Fin.castLE hkm i from rfl]
  ring

/-- **The truncation of an SVD at $k \le \operatorname{rank} A$ has rank $k$.** If $(U, \sigma, V)$
is a singular value decomposition of $A \in \mathbb{K}^{m \times n}$ and
$k \le \operatorname{rank} A$, then the truncation $U \Sigma_k V^H$ has rank $k$.

The unitary factors do not change the rank, and the first $k$ singular values are positive
(`Matrix.sortedSingularValues_eq_zero_iff_rank_le`). -/
theorem rank_svdTruncation (h : IsSVD A U σ V) {k : ℕ} (hk : k ≤ A.rank) :
    (svdTruncation U σ V k).rank = k := by
  classical
  have hUd : IsUnit U.det :=
    isUnit_det_of_left_inverse (mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_left)
  have hVd : IsUnit (star V).det :=
    isUnit_det_of_left_inverse (mem_unitaryGroup_iff.1 h.mem_unitaryGroup_right)
  rw [svdTruncation, rank_mul_eq_left_of_isUnit_det _ _ hVd,
    rank_mul_eq_right_of_isUnit_det _ _ hUd, rank_rectDiagonal]
  have hrm : A.rank ≤ m := (rank_le_card_height A).trans_eq (Fintype.card_fin m)
  have hrn : A.rank ≤ n := (rank_le_card_width A).trans_eq (Fintype.card_fin n)
  have hσ : ∀ j : ℕ, j < k → σ j ≠ 0 := fun j hj => by
    rw [h.singularValues_eq (by omega) (by omega)]
    intro h0
    rw [sortedSingularValues_eq_zero_iff_rank_le] at h0
    omega
  calc Fintype.card {j : Fin n // (j : ℕ) < m ∧
        (if (j : ℕ) < k then ((σ j : ℝ) : 𝕜) else 0) ≠ 0}
      = Fintype.card {j : Fin n // (j : ℕ) < k} := by
        refine Fintype.card_congr (Equiv.subtypeEquivRight fun j => ?_)
        by_cases hj : (j : ℕ) < k
        · simp [hj, hσ j hj, show (j : ℕ) < m by omega]
        · simp [hj]
    _ = k := by rw [Fintype.card_subtype, Fin.card_filter_val_lt, min_eq_right (by omega)]

end IsSVD

end Matrix
