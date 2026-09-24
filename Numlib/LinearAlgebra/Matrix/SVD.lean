/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.SingularValues`, beside Mathlib's
`LinearMap.singularValues`. The condition-number section is the exception: it names
`NormedRing.condNumber`, which is `Numlib`'s.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Rank
import Numlib.Analysis.InnerProductSpace.SingularValues
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.Analysis.Normed.Ring.CondNumber

/-!
# The singular value decomposition

The singular values of `A : Matrix m n 𝕜` are the square roots of the eigenvalues of the positive
semidefinite matrix `Aᴴ A`, and an orthonormal eigenbasis `u` of `Aᴴ A` is a family of *right
singular vectors*: the images `A u_i` are pairwise orthogonal of norm `σ_i`, so the normalized
nonzero ones are an orthonormal family `v` of *left singular vectors*, and `A x = ∑ σ_i ⟪u_i, x⟫
v_i`. That is the *singular system* of [kress1998numerical] (Theorem 5.4), and
`Matrix.exists_singularSystem` states it.

Three things are built on it. The **Moore–Penrose pseudoinverse** `A⁺ = (Aᴴ A)⁺ Aᴴ`, obtained by
inverting the nonzero eigenvalues of the Gram matrix and leaving the zero ones alone, is the unique
matrix satisfying the four Penrose conditions, and `A⁺ y` is the least-squares solution of `A x = y`
of smallest norm. The **spectral condition number** of a nonsingular matrix is the ratio of its
extreme singular values. And the **Tikhonov regularization** `(α + Aᴴ A)⁻¹ Aᴴ` at level `α > 0` is
the unique solution of the regularized normal equations and the unique minimizer of `x ↦ ‖A x - y‖²
+ α ‖x‖²` ([kress1998numerical], Theorem 5.7); the **discrepancy principle** chooses `α` so that the
residual has exactly the size of the data error, and does so uniquely
([kress1998numerical], Theorem 5.10).

## Main definitions

* `Matrix.singularValues`, `Matrix.rightSingularBasis`: the singular values indexed by the columns
  of `A`, and the orthonormal eigenbasis of `Aᴴ A` they come from; `Matrix.rightSingularUnitary` is
  the same eigenbasis as a unitary matrix.
* `Matrix.gramPinv` and `Matrix.pinv`: the Moore–Penrose pseudoinverse of `Aᴴ A` and of `A`.
* `Matrix.tikhonov`: the Tikhonov regularization of `A` at level `α`.
* `Matrix.rectDiagonal`: the rectangular diagonal matrix `diag(σ₀, σ₁, …) ∈ 𝕜^{m × n}` of a
  factorization `Uᴴ A V = Σ`, and `Matrix.sortedRightSingularVec`, the right singular vectors
  sorted by decreasing singular value.
* `Matrix.unitaryOfBasis b`: the unitary matrix whose columns are the vectors of an orthonormal
  basis `b` of a Euclidean space, the form in which `Matrix.exists_svd` produces its factors.

## Main results

* `Matrix.exists_singularSystem`: the singular system of `A` and the expansion of `A` along it;
  `Matrix.norm_sq_toEuclideanLin_apply` is the Parseval identity behind every bound here.
* `Matrix.pinv_unique`: the four Penrose conditions characterize `A⁺`;
  `Matrix.norm_toEuclideanLin_pinv_sub_eq_iInf` and `Matrix.norm_pinv_le_of_normalEquations`: it is
  the least-squares solution of least norm.
* `Matrix.l2_opNorm_eq_iSup_singularValues`, `Matrix.l2_opNorm_inv_eq_inv_iInf_singularValues` and
  `Matrix.condNumber_l2_eq_div_singularValues`: the spectral condition number is `σmax/σmin`.
* `Matrix.tikhonov_unique` and `Matrix.norm_sub_sq_add_mul_norm_sq_tikhonov_le`: the regularized
  normal equations and the variational characterization of the regularized solution.
* `Matrix.exists_discrepancy_tikhonov` and
  `Matrix.tendsto_tikhonov_of_norm_toEuclideanLin_sub_eq`: the discrepancy principle picks out a
  unique regularization parameter, and the solutions it picks converge to `A⁺ y` as the data error
  tends to `0` ([kress1998numerical], Theorem 5.10).
* `Matrix.exists_svd`: the full factorization `Uᴴ A V = Σ` with square unitary factors and the
  sorted singular values of Mathlib's `LinearMap.singularValues` on the diagonal
  ([quarteroni2000numerical] Property 1.7); from any such factorization,
  `Matrix.pinv_eq_of_svd` (`A⁺ = V Σ⁺ Uᴴ`, their Definition 1.15),
  `Matrix.ker_mulVecLin_eq_span_of_svd` and `Matrix.range_mulVecLin_eq_span_of_svd`, and the
  uniqueness of the singular values `Matrix.singularValues_eq_of_svd`;
  `Matrix.IsHermitian.exists_equiv_singularValues_eq_abs_eigenvalues` is the Hermitian case
  `σ_i = |λ_i|`.

## Implementation notes

`Matrix.singularValues` is indexed by the columns of `A`, not sorted, because that is how Mathlib
indexes `Matrix.IsHermitian.eigenvalues`, and because every consumer here wants the value attached
to a given right singular vector rather than the `j`-th largest. Mathlib's
`LinearMap.singularValues` is the sorted `ℕ`-indexed sequence; it appears here only in the full
factorization `Matrix.exists_svd` and its uniqueness, and the coordinate-free facts about it that
those use are in `Numlib/Analysis/InnerProductSpace/SingularValues`.
-/

open Module

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### Singular values and right singular vectors -/

/-- The **singular values** of `A`, indexed by the columns of `A`: `A.singularValues i` is the
square root of the `i`-th eigenvalue of the positive semidefinite matrix `Aᴴ A`. They are listed
with multiplicity but in no particular order, matching `Matrix.IsHermitian.eigenvalues`; the sorted
sequence is Mathlib's `LinearMap.singularValues`. -/
noncomputable def singularValues (A : Matrix m n 𝕜) (i : n) : ℝ :=
  Real.sqrt ((isHermitian_conjTranspose_mul_self A).eigenvalues i)

/-- The **right singular vectors** of `A`: an orthonormal eigenbasis of `Aᴴ A`, paired with
`Matrix.singularValues` index by index. -/
noncomputable def rightSingularBasis (A : Matrix m n 𝕜) :
    OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  (isHermitian_conjTranspose_mul_self A).eigenvectorBasis

variable (A : Matrix m n 𝕜)

/-- Singular values are nonnegative, being square roots. -/
theorem singularValues_nonneg (i : n) : 0 ≤ A.singularValues i := Real.sqrt_nonneg _

/-- The square of a singular value is the corresponding eigenvalue of the Gram matrix. -/
theorem sq_singularValues (i : n) :
    A.singularValues i ^ 2 = (isHermitian_conjTranspose_mul_self A).eigenvalues i :=
  Real.sq_sqrt (eigenvalues_conjTranspose_mul_self_nonneg A i)

/-- The right singular vectors are eigenvectors of `Aᴴ A`, for the squared singular values. -/
theorem toEuclideanLin_conjTranspose_mul_self_rightSingularBasis (i : n) :
    toEuclideanLin (Aᴴ * A) (A.rightSingularBasis i)
      = ((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularBasis i := by
  have h := (isHermitian_conjTranspose_mul_self A).mulVec_eigenvectorBasis i
  rw [sq_singularValues]
  apply WithLp.ofLp_injective
  rw [WithLp.ofLp_smul, ← RCLike.real_smul_eq_coe_smul (K := 𝕜), toLpLin_apply, WithLp.ofLp_toLp]
  exact h

/-- The inner product of two images is the quadratic form of the Gram matrix `Aᴴ A`. -/
theorem inner_toEuclideanLin_apply (x y : EuclideanSpace 𝕜 n) :
    (inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) : 𝕜)
      = inner 𝕜 x (toEuclideanLin (Aᴴ * A) y) := by
  classical
  rw [toLpLin_mul_same, LinearMap.comp_apply, toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

/-- **The images of the right singular vectors are pairwise orthogonal**, with squared norms the
squared singular values. This is the whole of the singular value decomposition. -/
theorem inner_toEuclideanLin_rightSingularBasis (i j : n) :
    (inner 𝕜 (toEuclideanLin A (A.rightSingularBasis i))
        (toEuclideanLin A (A.rightSingularBasis j)) : 𝕜)
      = if i = j then ((A.singularValues i ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [inner_toEuclideanLin_apply, toEuclideanLin_conjTranspose_mul_self_rightSingularBasis,
    inner_smul_right, orthonormal_iff_ite.1 A.rightSingularBasis.orthonormal i j]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero]

/-- The image of a right singular vector has the corresponding singular value as its norm. -/
@[simp]
theorem norm_toEuclideanLin_rightSingularBasis (i : n) :
    ‖toEuclideanLin A (A.rightSingularBasis i)‖ = A.singularValues i := by
  have h : (inner 𝕜 (toEuclideanLin A (A.rightSingularBasis i))
      (toEuclideanLin A (A.rightSingularBasis i)) : 𝕜)
        = ((A.singularValues i ^ 2 : ℝ) : 𝕜) := by
    simpa using A.inner_toEuclideanLin_rightSingularBasis i i
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖toEuclideanLin A (A.rightSingularBasis i)‖ ^ 2 = A.singularValues i ^ 2 := by
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (A.singularValues_nonneg i) two_ne_zero).1 h2

/-- A right singular vector with singular value `0` lies in the kernel. -/
theorem toEuclideanLin_rightSingularBasis_eq_zero {i : n} (hi : A.singularValues i = 0) :
    toEuclideanLin A (A.rightSingularBasis i) = 0 := by
  rw [← norm_eq_zero, norm_toEuclideanLin_rightSingularBasis, hi]

/-- `A x` expanded along the right singular basis. -/
theorem toEuclideanLin_eq_sum_rightSingularBasis (x : EuclideanSpace 𝕜 n) :
    toEuclideanLin A x = ∑ i, (inner 𝕜 (A.rightSingularBasis i) x : 𝕜) •
      toEuclideanLin A (A.rightSingularBasis i) := by
  conv_lhs => rw [← A.rightSingularBasis.sum_repr' x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _

/-- **Parseval for the singular values**: the squared norm of `A x` is the weighted sum of the
squared coefficients of `x` in the right singular basis. -/
theorem norm_sq_toEuclideanLin_apply (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A x‖ ^ 2 =
      ∑ i, A.singularValues i ^ 2 * ‖(inner 𝕜 (A.rightSingularBasis i) x : 𝕜)‖ ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c : n → 𝕜, c = fun i => (inner 𝕜 (A.rightSingularBasis i) x : 𝕜) :=
    ⟨_, rfl⟩
  have hx : x = ∑ i, c i • A.rightSingularBasis i := by
    rw [hc]; exact (A.rightSingularBasis.sum_repr' x).symm
  have hHx : toEuclideanLin (Aᴴ * A) x
      = ∑ i, (c i * ((A.singularValues i ^ 2 : ℝ) : 𝕜)) • A.rightSingularBasis i := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul, toEuclideanLin_conjTranspose_mul_self_rightSingularBasis, smul_smul]
  have key : (inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A x) : 𝕜)
      = ∑ i, ((A.singularValues i ^ 2 * ‖c i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [inner_toEuclideanLin_apply, hHx]
    conv_lhs => rw [hx]
    rw [A.rightSingularBasis.orthonormal.inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, RCLike.conj_mul]
    push_cast
    ring
  rw [inner_self_eq_norm_sq_to_K] at key
  have key2 : ((‖toEuclideanLin A x‖ ^ 2 : ℝ) : 𝕜)
      = ((∑ i, A.singularValues i ^ 2 * ‖c i‖ ^ 2 : ℝ) : 𝕜) := by
    push_cast
    push_cast at key
    exact key
  simp only [hc] at key2
  exact_mod_cast key2

/-- Composing with the conjugate transpose gives back the Gram matrix. -/
theorem toEuclideanLin_conjTranspose_toEuclideanLin [DecidableEq m] (y : EuclideanSpace 𝕜 n) :
    toEuclideanLin Aᴴ (toEuclideanLin A y) = toEuclideanLin (Aᴴ * A) y := by
  rw [toLpLin_mul_same, LinearMap.comp_apply]

/-! ### The singular system -/

open scoped ComplexOrder in
/-- The number of nonzero singular values is the rank of `A`. -/
theorem card_singularValues_ne_zero :
    Fintype.card {i : n // A.singularValues i ≠ 0} = A.rank := by
  classical
  have h1 : (Aᴴ * A).rank = Fintype.card
      {i : n // (isHermitian_conjTranspose_mul_self A).eigenvalues i ≠ 0} :=
    (isHermitian_conjTranspose_mul_self A).rank_eq_card_non_zero_eigs
  have h2 : {i : n // A.singularValues i ≠ 0} ≃
      {i : n // (isHermitian_conjTranspose_mul_self A).eigenvalues i ≠ 0} :=
    Equiv.subtypeEquivRight fun i => by
      rw [← sq_singularValues, ne_eq, ne_eq, pow_eq_zero_iff two_ne_zero]
  rw [Fintype.card_congr h2, ← h1, rank_conjTranspose_mul_self]

/-- **The singular system of a matrix** ([kress1998numerical], Theorem 5.4): there are `r = A.rank`
positive numbers `μ j`, an orthonormal family `u` of right singular vectors and an orthonormal
family `v` of left singular vectors with `A u_j = μ_j v_j` and `Aᴴ v_j = μ_j u_j`, along which `A`
expands as `A x = ∑ j, μ_j ⟪u_j, x⟫ v_j`. That expansion is the factorization `A = V Σ Uᴴ`: it says
the matrix acts diagonally between the two families, and it forces `A z = 0` for every `z`
orthogonal to all the `u_j`.

The families are indexed by `Fin A.rank` in no particular order; the underlying data are
`Matrix.singularValues` and `Matrix.rightSingularBasis`, indexed by the columns of `A`. -/
theorem exists_singularSystem [DecidableEq m] :
    ∃ (μ : Fin A.rank → ℝ) (u : Fin A.rank → EuclideanSpace 𝕜 n)
      (v : Fin A.rank → EuclideanSpace 𝕜 m),
      (∀ j, 0 < μ j) ∧ Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      (∀ j, toEuclideanLin A (u j) = ((μ j : ℝ) : 𝕜) • v j) ∧
      (∀ j, toEuclideanLin Aᴴ (v j) = ((μ j : ℝ) : 𝕜) • u j) ∧
      (∀ x, toEuclideanLin A x = ∑ j, (((μ j : ℝ) : 𝕜) * inner 𝕜 (u j) x) • v j) := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin A.rank ≃ {i : n // A.singularValues i ≠ 0}) :=
    ⟨(Fintype.equivFinOfCardEq A.card_singularValues_ne_zero).symm⟩
  have hpos : ∀ j : Fin A.rank, 0 < A.singularValues (e j) := fun j =>
    lt_of_le_of_ne (A.singularValues_nonneg _) (Ne.symm (e j).2)
  have hne : ∀ j : Fin A.rank, ((A.singularValues (e j) : ℝ) : 𝕜) ≠ 0 := fun j => by
    simpa using (hpos j).ne'
  have hinj : Function.Injective fun j : Fin A.rank => ((e j : n)) :=
    Subtype.val_injective.comp e.injective
  refine ⟨fun j => A.singularValues (e j), fun j => A.rightSingularBasis (e j),
    fun j => ((A.singularValues (e j) : ℝ) : 𝕜)⁻¹ •
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
    rw [map_smul, toEuclideanLin_conjTranspose_toEuclideanLin,
      toEuclideanLin_conjTranspose_mul_self_rightSingularBasis, smul_smul]
    congr 1
    have h := hne j
    push_cast at h ⊢
    field_simp
  · intro x
    rw [toEuclideanLin_eq_sum_rightSingularBasis]
    have hz : ∀ i : n, i ∈ (Finset.univ : Finset n) →
        i ∉ Finset.univ.filter (fun i => A.singularValues i ≠ 0) →
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
    rw [mul_comm ((A.singularValues (e j) : ℝ) : 𝕜), mul_assoc,
      mul_inv_cancel₀ (hne j), mul_one]

/-! ### The Moore–Penrose pseudoinverse -/

section Pinv

open scoped ComplexOrder

/-- `x x⁻¹ x = x`, at `x = 0` too. -/
private theorem mul_inv_mul_self (x : 𝕜) : x * x⁻¹ * x = x := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · rw [mul_inv_cancel₀ h, one_mul]

/-- `x⁻¹ x x⁻¹ = x⁻¹`, at `x = 0` too. -/
private theorem inv_mul_mul_inv (x : 𝕜) : x⁻¹ * x * x⁻¹ = x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | h
  · simp
  · rw [inv_mul_cancel₀ h, one_mul]

/-- The unitary whose columns are the right singular vectors of `A`, that is, the eigenvector
unitary of the Gram matrix `Aᴴ A`. -/
noncomputable def rightSingularUnitary (A : Matrix m n 𝕜) : Matrix n n 𝕜 :=
  (isHermitian_conjTranspose_mul_self A).eigenvectorUnitary

/-- The right singular unitary is unitary. -/
theorem rightSingularUnitary_mem_unitaryGroup : A.rightSingularUnitary ∈ unitaryGroup n 𝕜 :=
  ((isHermitian_conjTranspose_mul_self A).eigenvectorUnitary).2

/-- One half of unitarity of the right singular unitary, in equational form. -/
theorem star_mul_rightSingularUnitary :
    star A.rightSingularUnitary * A.rightSingularUnitary = 1 :=
  mem_unitaryGroup_iff'.1 A.rightSingularUnitary_mem_unitaryGroup

/-- The other half of unitarity of the right singular unitary, in equational form. -/
theorem rightSingularUnitary_mul_star :
    A.rightSingularUnitary * star A.rightSingularUnitary = 1 :=
  mem_unitaryGroup_iff.1 A.rightSingularUnitary_mem_unitaryGroup

/-- The spectral decomposition of the Gram matrix: `Aᴴ A = V Σ² Vᴴ`. -/
theorem conjTranspose_mul_self_eq_conj_diagonal :
    Aᴴ * A = A.rightSingularUnitary * diagonal (fun i => ((A.singularValues i ^ 2 : ℝ) : 𝕜))
      * star A.rightSingularUnitary := by
  conv_lhs => rw [(isHermitian_conjTranspose_mul_self A).spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  simp [rightSingularUnitary, Function.comp_def, sq_singularValues]

/-- Conjugation by the right singular unitary turns a product of conjugated diagonal matrices into
the conjugate of the product of their diagonals. -/
private theorem conj_diagonal_mul_conj_diagonal (f g : n → 𝕜) :
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

/-- The Moore–Penrose pseudoinverse of the Gram matrix `Aᴴ A`, obtained by inverting its nonzero
eigenvalues and leaving the zero ones alone; the auxiliary from which `Matrix.pinv` is built. -/
noncomputable def gramPinv (A : Matrix m n 𝕜) : Matrix n n 𝕜 :=
  A.rightSingularUnitary * diagonal (fun i => ((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹)
    * star A.rightSingularUnitary

/-- The pseudoinverse of the Gram matrix, unfolded. -/
theorem gramPinv_def : A.gramPinv = A.rightSingularUnitary *
    diagonal (fun i => ((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹) * star A.rightSingularUnitary :=
  rfl

/-- The pseudoinverse of the Gram matrix is Hermitian, its eigenvalues being real. -/
theorem isHermitian_gramPinv : A.gramPinv.IsHermitian := by
  have hf : (star fun i => (((A.singularValues i ^ 2 : ℝ) : 𝕜))⁻¹)
      = fun i => (((A.singularValues i ^ 2 : ℝ) : 𝕜))⁻¹ := by
    funext i
    rw [Pi.star_apply, star_inv₀, RCLike.star_def, RCLike.conj_ofReal]
  rw [Matrix.IsHermitian, gramPinv_def, star_eq_conjTranspose, conjTranspose_mul,
    conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, hf, Matrix.mul_assoc]

/-- The first Penrose condition for the Gram matrix. -/
theorem gram_mul_gramPinv_mul_gram : Aᴴ * A * A.gramPinv * (Aᴴ * A) = Aᴴ * A := by
  rw [conjTranspose_mul_self_eq_conj_diagonal, gramPinv_def, conj_diagonal_mul_conj_diagonal,
    conj_diagonal_mul_conj_diagonal]
  congr 2
  exact congrArg diagonal (funext fun i => mul_inv_mul_self _)

/-- The second Penrose condition for the Gram matrix. -/
theorem gramPinv_mul_gram_mul_gramPinv : A.gramPinv * (Aᴴ * A) * A.gramPinv = A.gramPinv := by
  rw [conjTranspose_mul_self_eq_conj_diagonal, gramPinv_def, conj_diagonal_mul_conj_diagonal,
    conj_diagonal_mul_conj_diagonal]
  congr 2
  exact congrArg diagonal (funext fun i => inv_mul_mul_inv _)

/-- The Gram matrix commutes with its pseudoinverse, both being diagonal in the right singular
basis. -/
theorem gramPinv_mul_gram_comm : A.gramPinv * (Aᴴ * A) = Aᴴ * A * A.gramPinv := by
  rw [conjTranspose_mul_self_eq_conj_diagonal, gramPinv_def, conj_diagonal_mul_conj_diagonal,
    conj_diagonal_mul_conj_diagonal]
  congr 2
  exact congrArg diagonal (funext fun i => mul_comm _ _)

/-- The **Moore–Penrose pseudoinverse** of a matrix, `A⁺ = (Aᴴ A)⁺ Aᴴ`, where the pseudoinverse of
the Gram matrix inverts its nonzero eigenvalues and leaves the zero ones alone. It is characterized
by the four Penrose conditions (`Matrix.pinv_unique`), and `A⁺ y` is the least-squares solution of
`A x = y` of smallest norm. -/
noncomputable def pinv (A : Matrix m n 𝕜) : Matrix n m 𝕜 := A.gramPinv * Aᴴ

/-- The pseudoinverse, unfolded. -/
theorem pinv_def : A.pinv = A.gramPinv * Aᴴ := rfl

omit [DecidableEq n] in
/-- A matrix killed by `Aᴴ A` is killed by `A`, because `Aᴴ A M = 0` forces `(A M)ᴴ (A M) = 0`. -/
theorem mul_eq_zero_of_conjTranspose_mul_self_mul_eq_zero {k : Type*}
    {M : Matrix n k 𝕜} (h : Aᴴ * A * M = 0) : A * M = 0 := by
  rw [← conjTranspose_mul_self_eq_zero (A := A * M), conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Aᴴ, h, Matrix.mul_zero]

/-- The first Penrose condition. -/
theorem mul_pinv_mul_self : A * A.pinv * A = A := by
  have key : A * (1 - A.gramPinv * (Aᴴ * A)) = 0 := by
    refine A.mul_eq_zero_of_conjTranspose_mul_self_mul_eq_zero ?_
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, gram_mul_gramPinv_mul_gram, sub_self]
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at key
  calc A * A.pinv * A = A * (A.gramPinv * (Aᴴ * A)) := by
        simp only [pinv_def, Matrix.mul_assoc]
    _ = A := key.symm

/-- The second Penrose condition. -/
theorem pinv_mul_self_mul_pinv : A.pinv * A * A.pinv = A.pinv := by
  calc A.pinv * A * A.pinv = A.gramPinv * (Aᴴ * A) * A.gramPinv * Aᴴ := by
        simp only [pinv_def, Matrix.mul_assoc]
    _ = A.pinv := by rw [gramPinv_mul_gram_mul_gramPinv, pinv_def]

/-- The third Penrose condition: `A A⁺` is Hermitian. -/
theorem isHermitian_mul_pinv : (A * A.pinv).IsHermitian := by
  rw [Matrix.IsHermitian, pinv_def, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, A.isHermitian_gramPinv, Matrix.mul_assoc]

/-- The fourth Penrose condition: `A⁺ A` is Hermitian. -/
theorem isHermitian_pinv_mul : (A.pinv * A).IsHermitian := by
  have h : A.pinv * A = A.gramPinv * (Aᴴ * A) := by rw [pinv_def, Matrix.mul_assoc]
  rw [Matrix.IsHermitian, h, conjTranspose_mul, (isHermitian_conjTranspose_mul_self A).eq,
    A.isHermitian_gramPinv, ← gramPinv_mul_gram_comm]

/-- The pseudoinverse solves the normal equations: `Aᴴ (A A⁺) = Aᴴ`. -/
theorem conjTranspose_mul_mul_pinv : Aᴴ * (A * A.pinv) = Aᴴ := by
  rw [← A.isHermitian_mul_pinv, ← conjTranspose_mul, mul_pinv_mul_self]

/-- **The Moore–Penrose pseudoinverse is the unique matrix satisfying the four Penrose conditions.**
The Penrose conditions force `B A = A⁺ A` and `A B = A A⁺`, after which `B = B A B = A⁺ A A⁺ = A⁺`.
-/
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

/-- A Hermitian matrix acts as a self-adjoint operator on Euclidean space. -/
theorem inner_toEuclideanLin_of_isHermitian {M : Matrix n n 𝕜} (hM : M.IsHermitian)
    (u z : EuclideanSpace 𝕜 n) :
    (inner 𝕜 (toEuclideanLin M u) z : 𝕜) = inner 𝕜 u (toEuclideanLin M z) := by
  conv_lhs => rw [← hM]
  rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

variable [DecidableEq m]

/-- The residual of the pseudoinverse solution is orthogonal to the range of `A`. -/
theorem inner_toEuclideanLin_sub_pinv (y : EuclideanSpace 𝕜 m) (w : EuclideanSpace 𝕜 n) :
    (inner 𝕜 (toEuclideanLin A w)
      (toEuclideanLin A (toEuclideanLin A.pinv y) - y) : 𝕜) = 0 := by
  have hmat : Aᴴ * A * A.pinv = Aᴴ := by
    rw [Matrix.mul_assoc, conjTranspose_mul_mul_pinv]
  have hres : toEuclideanLin Aᴴ (toEuclideanLin A (toEuclideanLin A.pinv y) - y) = 0 := by
    rw [map_sub, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, hmat, sub_self]
  rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint, hres,
    inner_zero_right]

/-- **`A⁺ y` is a least-squares solution**: it minimizes the residual `‖A x - y‖`. -/
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

/-- **The residual of the pseudoinverse solution is the least-squares minimum.** -/
theorem norm_toEuclideanLin_pinv_sub_eq_iInf (y : EuclideanSpace 𝕜 m) :
    ‖toEuclideanLin A (toEuclideanLin A.pinv y) - y‖
      = ⨅ x : EuclideanSpace 𝕜 n, ‖toEuclideanLin A x - y‖ := by
  refine le_antisymm (le_ciInf fun x => A.norm_toEuclideanLin_pinv_sub_le y x) ?_
  exact ciInf_le ⟨0, fun r hr => by obtain ⟨x, rfl⟩ := hr; exact norm_nonneg _⟩ _

/-- **Among the least-squares solutions, `A⁺ y` has the smallest norm.** The hypothesis is the
normal equations `Aᴴ A x = Aᴴ y`, which characterize the least-squares solutions. -/
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

end Pinv

/-! ### The spectral condition number -/

section CondNumber

open scoped Matrix.Norms.L2Operator

/-- Parseval in the right singular basis. -/
theorem sum_norm_inner_rightSingularBasis_sq (x : EuclideanSpace 𝕜 n) :
    ∑ i, ‖(inner 𝕜 (A.rightSingularBasis i) x : 𝕜)‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := EuclideanSpace.norm_sq_eq (A.rightSingularBasis.repr x)
  rw [A.rightSingularBasis.repr.norm_map] at h
  simp only [OrthonormalBasis.repr_apply_apply] at h
  exact h.symm

variable [Nonempty n]

/-- The largest singular value bounds `A` as an operator. -/
theorem norm_toEuclideanLin_le_iSup_singularValues (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A x‖ ≤ (⨆ i, A.singularValues i) * ‖x‖ := by
  have hbdd : BddAbove (Set.range A.singularValues) := (Set.finite_range _).bddAbove
  have hle : ∀ i, A.singularValues i ≤ ⨆ j, A.singularValues j := fun i => le_ciSup hbdd i
  have hnn : 0 ≤ ⨆ j, A.singularValues j :=
    le_trans (A.singularValues_nonneg (Classical.arbitrary n)) (hle _)
  refine le_of_sq_le_sq ?_ (mul_nonneg hnn (norm_nonneg _))
  rw [A.norm_sq_toEuclideanLin_apply, mul_pow, ← A.sum_norm_inner_rightSingularBasis_sq x,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (A.singularValues_nonneg i) (hle i) 2) (sq_nonneg _)

/-- The smallest singular value bounds `A` from below. -/
theorem iInf_singularValues_mul_norm_le (x : EuclideanSpace 𝕜 n) :
    (⨅ i, A.singularValues i) * ‖x‖ ≤ ‖toEuclideanLin A x‖ := by
  have hbdd : BddBelow (Set.range A.singularValues) := (Set.finite_range _).bddBelow
  have hge : ∀ i, (⨅ j, A.singularValues j) ≤ A.singularValues i := fun i => ciInf_le hbdd i
  have hnn : 0 ≤ ⨅ j, A.singularValues j := le_ciInf fun i => A.singularValues_nonneg i
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [A.norm_sq_toEuclideanLin_apply, mul_pow, ← A.sum_norm_inner_rightSingularBasis_sq x,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hnn (hge i) 2) (sq_nonneg _)

variable (B : Matrix n n 𝕜)

/-- **Under the `l₂` operator norm the norm of a matrix is its largest singular value.** -/
theorem l2_opNorm_eq_iSup_singularValues : ‖B‖ = ⨆ i, B.singularValues i := by
  have hbdd : BddAbove (Set.range B.singularValues) := (Set.finite_range _).bddAbove
  have hnn : 0 ≤ ⨆ j, B.singularValues j :=
    le_trans (B.singularValues_nonneg (Classical.arbitrary n)) (le_ciSup hbdd _)
  rw [l2_opNorm_eq_norm_toEuclideanLin]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ hnn fun x =>
    B.norm_toEuclideanLin_le_iSup_singularValues x) (ciSup_le fun i => ?_)
  calc B.singularValues i = ‖toEuclideanLin B (B.rightSingularBasis i)‖ :=
        (B.norm_toEuclideanLin_rightSingularBasis i).symm
    _ ≤ ‖LinearMap.toContinuousLinearMap (toEuclideanLin B)‖ * ‖B.rightSingularBasis i‖ := by
        simpa using ContinuousLinearMap.le_opNorm
          (LinearMap.toContinuousLinearMap (toEuclideanLin B)) (B.rightSingularBasis i)
    _ = ‖LinearMap.toContinuousLinearMap (toEuclideanLin B)‖ := by
        rw [B.rightSingularBasis.orthonormal.1 i, mul_one]

omit [Nonempty n] in
/-- An invertible matrix has no zero singular value. -/
theorem singularValues_pos (hB : IsUnit B.det) (i : n) : 0 < B.singularValues i := by
  refine lt_of_le_of_ne (B.singularValues_nonneg i) (Ne.symm fun h => ?_)
  have h0 : toEuclideanLin B (B.rightSingularBasis i) = 0 :=
    B.toEuclideanLin_rightSingularBasis_eq_zero h
  have hinv : toEuclideanLin B⁻¹ (toEuclideanLin B (B.rightSingularBasis i))
      = B.rightSingularBasis i := by
    rw [← toEuclideanLin_mul_apply, Matrix.nonsing_inv_mul B hB, toLpLin_one, LinearMap.id_apply]
  rw [h0, map_zero] at hinv
  have hone := B.rightSingularBasis.orthonormal.1 i
  rw [← hinv, norm_zero] at hone
  exact zero_ne_one hone

/-- **The norm of the inverse is the reciprocal of the smallest singular value.** -/
theorem l2_opNorm_inv_eq_inv_iInf_singularValues (hB : IsUnit B.det) :
    ‖B⁻¹‖ = (⨅ i, B.singularValues i)⁻¹ := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min B.singularValues
  have hbdd : BddBelow (Set.range B.singularValues) := (Set.finite_range _).bddBelow
  have hinf : (⨅ i, B.singularValues i) = B.singularValues i₀ :=
    le_antisymm (ciInf_le hbdd i₀) (le_ciInf hi₀)
  have hpos : 0 < B.singularValues i₀ := B.singularValues_pos hB i₀
  rw [hinf, l2_opNorm_eq_norm_toEuclideanLin]
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_) ?_
  · have hz : toEuclideanLin B (toEuclideanLin B⁻¹ z) = z := by
      rw [← toEuclideanLin_mul_apply, Matrix.mul_nonsing_inv B hB, toLpLin_one, LinearMap.id_apply]
    have h1 := B.iInf_singularValues_mul_norm_le (toEuclideanLin B⁻¹ z)
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

/-- **The spectral condition number is the ratio of the extreme singular values**, `κ₂(A) =
σmax/σmin`. -/
theorem condNumber_l2_eq_div_singularValues (hB : IsUnit B.det) :
    NormedRing.condNumber B = (⨆ i, B.singularValues i) / (⨅ i, B.singularValues i) := by
  rw [NormedRing.condNumber, ← Matrix.nonsing_inv_eq_ringInverse,
    l2_opNorm_eq_iSup_singularValues, l2_opNorm_inv_eq_inv_iInf_singularValues B hB,
    div_eq_mul_inv]

end CondNumber

/-! ### Tikhonov regularization -/

section Tikhonov

variable (α : ℝ)

/-- The **Tikhonov regularization** of `A` at level `α`: the matrix `(α + Aᴴ A)⁻¹ Aᴴ`, whose action
on `y` is the regularized solution of `A x = y`. For `α > 0` it is the unique solution of the
regularized normal equations `α x + Aᴴ A x = Aᴴ y` (`Matrix.tikhonov_unique`) and the unique
minimizer of `x ↦ ‖A x - y‖² + α ‖x‖²` (`Matrix.norm_sub_sq_add_mul_norm_sq_tikhonov_le`). In the
right singular basis it multiplies the `i`-th coordinate by `σ_i/(α + σ_i²)`, which is
`Matrix.mul_inv_smul_one_add_gram` read through `Matrix.exists_singularSystem`. -/
noncomputable def tikhonov (A : Matrix m n 𝕜) (α : ℝ) : Matrix n m 𝕜 :=
  ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * Aᴴ

/-- The Tikhonov regularization, unfolded. -/
theorem tikhonov_def : A.tikhonov α = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * Aᴴ := rfl

/-- The regularized Gram matrix is diagonal in the right singular basis, with entries `α + σ_i²`. -/
theorem smul_one_add_gram_eq :
    (α : 𝕜) • 1 + Aᴴ * A
      = A.rightSingularUnitary * diagonal (fun i => ((α + A.singularValues i ^ 2 : ℝ) : 𝕜))
        * star A.rightSingularUnitary := by
  have hconst : (diagonal fun _ : n => (α : 𝕜)) = (α : 𝕜) • (1 : Matrix n n 𝕜) := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h]
  have h1 : (α : 𝕜) • (1 : Matrix n n 𝕜)
      = A.rightSingularUnitary * diagonal (fun _ : n => (α : 𝕜))
        * star A.rightSingularUnitary := by
    rw [hconst, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      A.rightSingularUnitary_mul_star]
  rw [h1, conjTranspose_mul_self_eq_conj_diagonal, ← Matrix.add_mul, ← Matrix.mul_add,
    diagonal_add]
  congr 2
  funext i
  push_cast
  ring

/-- For `α > 0` the regularized Gram matrix has an explicit right inverse, obtained by inverting its
diagonal in the right singular basis. -/
theorem mul_inv_smul_one_add_gram (hα : 0 < α) :
    ((α : 𝕜) • 1 + Aᴴ * A) * (A.rightSingularUnitary *
        diagonal (fun i => ((α + A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹)
        * star A.rightSingularUnitary) = 1 := by
  have hne : ∀ i, ((α + A.singularValues i ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    intro i
    have hpos : (0 : ℝ) < α + A.singularValues i ^ 2 := by positivity
    rw [Ne, RCLike.ofReal_eq_zero]
    exact hpos.ne'
  rw [smul_one_add_gram_eq, conj_diagonal_mul_conj_diagonal]
  have hone : (fun i => ((α + A.singularValues i ^ 2 : ℝ) : 𝕜)
      * ((α + A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹) = fun _ : n => (1 : 𝕜) :=
    funext fun i => mul_inv_cancel₀ (hne i)
  have hdiag : (diagonal fun _ : n => (1 : 𝕜)) = 1 := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h]
  rw [hone, hdiag, Matrix.mul_one, A.rightSingularUnitary_mul_star]

/-- For `α > 0` the regularized Gram matrix is nonsingular. -/
theorem isUnit_det_smul_one_add_gram (hα : 0 < α) :
    IsUnit ((α : 𝕜) • 1 + Aᴴ * A).det :=
  Matrix.isUnit_det_of_right_inverse (A.mul_inv_smul_one_add_gram α hα)

/-- The regularized Gram matrix acts as `x ↦ α x + Aᴴ A x`. -/
theorem toEuclideanLin_smul_one_add_gram (x : EuclideanSpace 𝕜 n) :
    toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A) x = (α : 𝕜) • x + toEuclideanLin (Aᴴ * A) x := by
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, toLpLin_one,
    LinearMap.id_apply]

variable [DecidableEq m]

/-- **The Tikhonov solution is the unique solution of the regularized normal equations** `α x + Aᴴ A
x = Aᴴ y` ([kress1998numerical], Theorem 5.7). -/
theorem tikhonov_unique (hα : 0 < α) (y : EuclideanSpace 𝕜 m) (x : EuclideanSpace 𝕜 n) :
    (α : 𝕜) • x + toEuclideanLin (Aᴴ * A) x = toEuclideanLin Aᴴ y
      ↔ x = toEuclideanLin (A.tikhonov α) y := by
  have hdet := A.isUnit_det_smul_one_add_gram α hα
  rw [← toEuclideanLin_smul_one_add_gram]
  constructor
  · intro h
    have h2 := congrArg (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹) h
    rw [← toEuclideanLin_mul_apply, Matrix.nonsing_inv_mul _ hdet, toLpLin_one,
      LinearMap.id_apply] at h2
    rw [h2, tikhonov_def, toEuclideanLin_mul_apply]
  · intro h
    rw [h, tikhonov_def, ← toEuclideanLin_mul_apply, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]

/-- **A solution of the regularized normal equations minimizes the regularized least-squares
functional** `x ↦ ‖A x - y‖² + α ‖x‖²` ([kress1998numerical], Theorem 5.7). The first-order term of
the expansion around `z` vanishes exactly because `z` solves the normal equations, and the remainder
`‖A (x - z)‖² + α ‖x - z‖²` is nonnegative. -/
theorem norm_sub_sq_add_mul_norm_sq_le_of_smul_add_gram (hα : 0 ≤ α) (y : EuclideanSpace 𝕜 m)
    {z : EuclideanSpace 𝕜 n} (hz : (α : 𝕜) • z + toEuclideanLin (Aᴴ * A) z = toEuclideanLin Aᴴ y)
    (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A z - y‖ ^ 2 + α * ‖z‖ ^ 2
      ≤ ‖toEuclideanLin A x - y‖ ^ 2 + α * ‖x‖ ^ 2 := by
  have hzero : toEuclideanLin Aᴴ (toEuclideanLin A z - y) + (α : 𝕜) • z = 0 := by
    rw [map_sub, ← toEuclideanLin_mul_apply, ← hz]
    abel
  have hip : (inner 𝕜 (toEuclideanLin Aᴴ (toEuclideanLin A z - y)) (x - z) : 𝕜)
      + (α : 𝕜) * inner 𝕜 z (x - z) = 0 := by
    have h := congrArg (fun w => (inner 𝕜 w (x - z) : 𝕜)) hzero
    simp only [inner_add_left, inner_zero_left, inner_smul_left, RCLike.conj_ofReal] at h
    exact h
  have hre : RCLike.re (inner 𝕜 (toEuclideanLin A z - y) (toEuclideanLin A (x - z)) : 𝕜)
      + α * RCLike.re (inner 𝕜 z (x - z) : 𝕜) = 0 := by
    have hadj : (inner 𝕜 (toEuclideanLin A z - y) (toEuclideanLin A (x - z)) : 𝕜)
        = inner 𝕜 (toEuclideanLin Aᴴ (toEuclideanLin A z - y)) (x - z) := by
      rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
    rw [hadj]
    have h2 := congrArg RCLike.re hip
    simpa [RCLike.re_ofReal_mul] using h2
  have hAd : toEuclideanLin A x - y
      = (toEuclideanLin A z - y) + toEuclideanLin A (x - z) := by
    rw [map_sub]
    abel
  have hxd : x = z + (x - z) := by abel
  have hn1 : ‖toEuclideanLin A x - y‖ ^ 2
      = ‖toEuclideanLin A z - y‖ ^ 2
        + 2 * RCLike.re (inner 𝕜 (toEuclideanLin A z - y) (toEuclideanLin A (x - z)) : 𝕜)
        + ‖toEuclideanLin A (x - z)‖ ^ 2 := by
    rw [hAd]
    exact norm_add_sq (𝕜 := 𝕜) _ _
  have hn2 : ‖x‖ ^ 2 = ‖z‖ ^ 2 + 2 * RCLike.re (inner 𝕜 z (x - z) : 𝕜) + ‖x - z‖ ^ 2 := by
    conv_lhs => rw [hxd]
    exact norm_add_sq (𝕜 := 𝕜) _ _
  have hn2' : α * ‖x‖ ^ 2
      = α * ‖z‖ ^ 2 + 2 * (α * RCLike.re (inner 𝕜 z (x - z) : 𝕜)) + α * ‖x - z‖ ^ 2 := by
    rw [hn2]
    ring
  linarith [hn1, hn2', hre, sq_nonneg ‖toEuclideanLin A (x - z)‖,
    mul_nonneg hα (sq_nonneg ‖x - z‖)]

/-- **The Tikhonov solution is the minimizer of the regularized least-squares functional.** -/
theorem norm_sub_sq_add_mul_norm_sq_tikhonov_le (hα : 0 < α) (y : EuclideanSpace 𝕜 m)
    (x : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A (toEuclideanLin (A.tikhonov α) y) - y‖ ^ 2
        + α * ‖toEuclideanLin (A.tikhonov α) y‖ ^ 2
      ≤ ‖toEuclideanLin A x - y‖ ^ 2 + α * ‖x‖ ^ 2 :=
  A.norm_sub_sq_add_mul_norm_sq_le_of_smul_add_gram α hα.le y
    ((A.tikhonov_unique α hα y _).2 rfl) x

end Tikhonov

/-! ### The discrepancy principle -/

section Discrepancy

/-- Pythagoras for a difference of orthogonal vectors, in squared form. -/
private theorem norm_sub_sq_of_inner_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (x y : E) (h : (inner 𝕜 x y : 𝕜) = 0) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h' : (inner 𝕜 x (-y) : 𝕜) = 0 := by rw [inner_neg_right, h, neg_zero]
  have key := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) x (-y) h'
  rw [← sub_eq_add_neg, norm_neg] at key
  rw [pow_two, pow_two, pow_two, key]

/-- `A⁺ A` acts as the identity on the range of `Aᴴ`. -/
theorem pinv_mul_self_mul_conjTranspose : A.pinv * A * Aᴴ = Aᴴ := by
  have h : (A.pinv * A * Aᴴ)ᴴ = (Aᴴ)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, A.isHermitian_pinv_mul.eq,
      ← Matrix.mul_assoc, mul_pinv_mul_self]
  exact conjTranspose_injective h

/-- **The Tikhonov solution is a correction of the least-squares solution**: since `Aᴴ y` and
`Aᴴ A A⁺ y` agree, `(α + Aᴴ A)⁻¹ Aᴴ = A⁺ - α (α + Aᴴ A)⁻¹ A⁺`. -/
theorem tikhonov_eq_pinv_sub (α : ℝ) (hα : 0 < α) :
    A.tikhonov α = A.pinv - (α : 𝕜) • (((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * A.pinv) := by
  have hdet := A.isUnit_det_smul_one_add_gram α hα
  have h1 : ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * ((α : 𝕜) • 1 + Aᴴ * A) = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have hAH : Aᴴ * A * A.pinv = Aᴴ := by rw [Matrix.mul_assoc, conjTranspose_mul_mul_pinv]
  have h2 : (((α : 𝕜) • 1 + Aᴴ * A) - (α : 𝕜) • 1) * A.pinv
      = ((α : 𝕜) • 1 + Aᴴ * A) * A.pinv - (α : 𝕜) • A.pinv := by
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
  calc A.tikhonov α
      = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * (Aᴴ * A * A.pinv) := by rw [hAH, tikhonov_def]
    _ = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * ((((α : 𝕜) • 1 + Aᴴ * A) - (α : 𝕜) • 1) * A.pinv) := by
        congr 2
        abel
    _ = A.pinv - (α : 𝕜) • (((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * A.pinv) := by
        rw [h2, Matrix.mul_sub, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_smul]

/-- The Tikhonov solution lies in the range of `Aᴴ`, on which `A⁺ A` is the identity: the
projector `A⁺ A` commutes with the regularized Gram matrix, both being diagonal in the right
singular basis. -/
theorem pinv_mul_self_mul_tikhonov (α : ℝ) (hα : 0 < α) :
    A.pinv * A * A.tikhonov α = A.tikhonov α := by
  have hdet := A.isUnit_det_smul_one_add_gram α hα
  have h1 : A.pinv * A * (Aᴴ * A) = Aᴴ * A := by
    rw [← Matrix.mul_assoc, pinv_mul_self_mul_conjTranspose]
  have h2 : Aᴴ * A * (A.pinv * A) = Aᴴ * A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A A.pinv A, mul_pinv_mul_self]
  have hcomm : A.pinv * A * ((α : 𝕜) • 1 + Aᴴ * A)
      = ((α : 𝕜) • 1 + Aᴴ * A) * (A.pinv * A) := by
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hinv : A.pinv * A * ((α : 𝕜) • 1 + Aᴴ * A)⁻¹
      = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * (A.pinv * A) := by
    calc A.pinv * A * ((α : 𝕜) • 1 + Aᴴ * A)⁻¹
        = (((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * ((α : 𝕜) • 1 + Aᴴ * A)) *
            (A.pinv * A * ((α : 𝕜) • 1 + Aᴴ * A)⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
      _ = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * ((((α : 𝕜) • 1 + Aᴴ * A) * (A.pinv * A)) *
            ((α : 𝕜) • 1 + Aᴴ * A)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * ((A.pinv * A * ((α : 𝕜) • 1 + Aᴴ * A)) *
            ((α : 𝕜) • 1 + Aᴴ * A)⁻¹) := by rw [hcomm]
      _ = ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ * (A.pinv * A) := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  rw [tikhonov_def, ← Matrix.mul_assoc, hinv, Matrix.mul_assoc,
    pinv_mul_self_mul_conjTranspose]

/-- **The resolvent of the Gram matrix is diagonal in the right singular basis**: it divides the
`i`-th coefficient by `α + σ_i²`. -/
theorem inner_rightSingularBasis_inv_smul_one_add_gram (α : ℝ) (hα : 0 < α)
    (v : EuclideanSpace 𝕜 n) (i : n) :
    (inner 𝕜 (A.rightSingularBasis i)
        (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ v) : 𝕜)
      = ((α + A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹ * inner 𝕜 (A.rightSingularBasis i) v := by
  have hdet := A.isUnit_det_smul_one_add_gram α hα
  have hne : ((α + A.singularValues i ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    have hpos : (0 : ℝ) < α + A.singularValues i ^ 2 := by positivity
    rw [Ne, RCLike.ofReal_eq_zero]
    exact hpos.ne'
  have hmp : (α : 𝕜) • toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ v
      + toEuclideanLin (Aᴴ * A) (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ v) = v := by
    rw [← toEuclideanLin_smul_one_add_gram, ← toEuclideanLin_mul_apply,
      Matrix.mul_nonsing_inv _ hdet, toLpLin_one, LinearMap.id_apply]
  have hinner := congrArg (fun x => (inner 𝕜 (A.rightSingularBasis i) x : 𝕜)) hmp
  simp only [inner_add_right, inner_smul_right] at hinner
  rw [← inner_toEuclideanLin_of_isHermitian (isHermitian_conjTranspose_mul_self A),
    toEuclideanLin_conjTranspose_mul_self_rightSingularBasis, inner_smul_left,
    RCLike.conj_ofReal] at hinner
  have h2 : ((α + A.singularValues i ^ 2 : ℝ) : 𝕜) *
      (inner 𝕜 (A.rightSingularBasis i)
        (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ v) : 𝕜)
      = inner 𝕜 (A.rightSingularBasis i) v := by
    push_cast at hinner ⊢
    linear_combination hinner
  rw [← h2, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The squared norm of the image under `A` of the resolvent applied to `v`, in the right singular
basis: the `i`-th coefficient is multiplied by `σ_i/(α + σ_i²)`. -/
theorem norm_sq_toEuclideanLin_inv_smul_one_add_gram (α : ℝ) (hα : 0 < α)
    (v : EuclideanSpace 𝕜 n) :
    ‖toEuclideanLin A (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ v)‖ ^ 2
      = ∑ i, (A.singularValues i / (α + A.singularValues i ^ 2)) ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i) v : 𝕜)‖ ^ 2 := by
  rw [norm_sq_toEuclideanLin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpos : (0 : ℝ) < α + A.singularValues i ^ 2 := by positivity
  have hne : α + A.singularValues i ^ 2 ≠ 0 := hpos.ne'
  rw [A.inner_rightSingularBasis_inv_smul_one_add_gram α hα v i, norm_mul, norm_inv,
    RCLike.norm_ofReal, abs_of_pos hpos]
  field_simp

variable [DecidableEq m]

/-- **The squared norm of the Tikhonov residual.** Writing `w = A⁺ yδ`, the residual splits
orthogonally into the least-squares residual `A w - yδ`, which is independent of `α`, and a
correction inside the range of `A` whose `i`-th coefficient in the right singular basis is
`α σ_i/(α + σ_i²)` times that of `w`. -/
theorem norm_sq_toEuclideanLin_tikhonov_sub (α : ℝ) (hα : 0 < α) (yδ : EuclideanSpace 𝕜 m) :
    ‖toEuclideanLin A (toEuclideanLin (A.tikhonov α) yδ) - yδ‖ ^ 2
      = ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ ^ 2
        + ∑ i, (α * A.singularValues i / (α + A.singularValues i ^ 2)) ^ 2 *
            ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := by
  have hres : toEuclideanLin A (toEuclideanLin (A.tikhonov α) yδ) - yδ
      = (toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ)
        - (α : 𝕜) • toEuclideanLin A
            (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ (toEuclideanLin A.pinv yδ)) := by
    rw [tikhonov_eq_pinv_sub A α hα]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      toEuclideanLin_mul_apply]
    abel
  have hperp : (inner 𝕜 (toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ)
      ((α : 𝕜) • toEuclideanLin A
        (toEuclideanLin ((α : 𝕜) • 1 + Aᴴ * A)⁻¹ (toEuclideanLin A.pinv yδ))) : 𝕜) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, A.inner_toEuclideanLin_sub_pinv yδ _, map_zero,
      mul_zero]
  rw [hres, norm_sub_sq_of_inner_eq_zero (𝕜 := 𝕜) _ _ hperp, norm_smul, mul_pow,
    RCLike.norm_ofReal, abs_of_pos hα,
    A.norm_sq_toEuclideanLin_inv_smul_one_add_gram α hα, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The discrepancy principle for Tikhonov regularization** ([kress1998numerical], Theorem 5.10):
if the best achievable residual `dist (yδ, range A)` is below the error level `δ`, which is in turn
below `‖yδ‖`, then there is exactly one regularization parameter `α > 0` at which the Tikhonov
residual has norm exactly `δ`.

The two hypotheses are sharp: the residual norm increases strictly from `dist (yδ, range A)` at
`α = 0` to `‖yδ‖` as `α → ∞`. Kress states the lower hypothesis as `‖yδ - y‖ ≤ δ` for some
`y` in the range of `A`, which gives only `dist (yδ, range A) ≤ δ`; with equality there is no such
`α`, as `A = diag (1, 0)`, `y = (1, 0)`, `yδ = (1, δ)` shows. -/
theorem exists_discrepancy_tikhonov (yδ : EuclideanSpace 𝕜 m) {δ : ℝ}
    (hlow : ⨅ x : EuclideanSpace 𝕜 n, ‖toEuclideanLin A x - yδ‖ < δ) (hhigh : δ < ‖yδ‖) :
    ∃! α : ℝ, 0 < α ∧
      ‖toEuclideanLin A (toEuclideanLin (A.tikhonov α) yδ) - yδ‖ = δ := by
  classical
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun t =>
      ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ ^ 2
        + ∑ i, (t * A.singularValues i / (t + A.singularValues i ^ 2)) ^ 2 *
            ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := ⟨_, rfl⟩
  have hd : ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ < δ := by
    rw [A.norm_toEuclideanLin_pinv_sub_eq_iInf yδ]; exact hlow
  have hδ0 : 0 < δ := lt_of_le_of_lt (norm_nonneg _) hd
  have hsplit : ‖yδ‖ ^ 2 = ‖toEuclideanLin A (toEuclideanLin A.pinv yδ)‖ ^ 2
      + ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ ^ 2 := by
    have key := norm_sub_sq_of_inner_eq_zero (𝕜 := 𝕜)
      (toEuclideanLin A (toEuclideanLin A.pinv yδ))
      (toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ)
      (A.inner_toEuclideanLin_sub_pinv yδ _)
    rwa [sub_sub_cancel] at key
  have hAw : 0 < ‖toEuclideanLin A (toEuclideanLin A.pinv yδ)‖ ^ 2 := by
    nlinarith [norm_nonneg (toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ), hd, hδ0, hhigh,
      hsplit]
  have hParseval : ∑ i, A.singularValues i ^ 2 *
      ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2
      = ‖toEuclideanLin A (toEuclideanLin A.pinv yδ)‖ ^ 2 :=
    (A.norm_sq_toEuclideanLin_apply _).symm
  obtain ⟨i₀, -, hi₀⟩ : ∃ i₀ ∈ (Finset.univ : Finset n), (0 : ℝ) < A.singularValues i₀ ^ 2 *
      ‖(inner 𝕜 (A.rightSingularBasis i₀) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := by
    refine Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ)) ?_
    rw [Finset.sum_const_zero, hParseval]
    exact hAw
  have hσ₀ : 0 < A.singularValues i₀ := by
    rcases (A.singularValues_nonneg i₀).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hi₀; simp at hi₀
  have hc₀ : 0 < ‖(inner 𝕜 (A.rightSingularBasis i₀) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := by
    nlinarith [hi₀, sq_nonneg (A.singularValues i₀)]
  have hFeq : ∀ t : ℝ, 0 < t →
      ‖toEuclideanLin A (toEuclideanLin (A.tikhonov t) yδ) - yδ‖ ^ 2 = F t := by
    intro t ht
    rw [hF]
    exact A.norm_sq_toEuclideanLin_tikhonov_sub t ht yδ
  have hF0 : F 0 = ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ ^ 2 := by
    rw [hF]; simp
  have hmono : StrictMonoOn F (Set.Ici (0 : ℝ)) := by
    intro s hs t ht hst
    simp only [Set.mem_Ici] at hs ht
    have h1 : ∀ i ∈ (Finset.univ : Finset n),
        (s * A.singularValues i / (s + A.singularValues i ^ 2)) ^ 2 *
            ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2
          ≤ (t * A.singularValues i / (t + A.singularValues i ^ 2)) ^ 2 *
            ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := by
      intro i _
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rcases (A.singularValues_nonneg i).lt_or_eq with hσ | hσ
      · have hs' : (0 : ℝ) < s + A.singularValues i ^ 2 := by positivity
        have ht' : (0 : ℝ) < t + A.singularValues i ^ 2 := by positivity
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        rw [div_le_div_iff₀ hs' ht']
        have hcube : s * (A.singularValues i * A.singularValues i * A.singularValues i)
            ≤ t * (A.singularValues i * A.singularValues i * A.singularValues i) :=
          mul_le_mul_of_nonneg_right hst.le (by positivity)
        nlinarith [hcube]
      · rw [← hσ]; simp
    have h2 : (s * A.singularValues i₀ / (s + A.singularValues i₀ ^ 2)) ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i₀) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2
        < (t * A.singularValues i₀ / (t + A.singularValues i₀ ^ 2)) ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i₀) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2 := by
      refine mul_lt_mul_of_pos_right ?_ hc₀
      have hs' : (0 : ℝ) < s + A.singularValues i₀ ^ 2 := by positivity
      have ht' : (0 : ℝ) < t + A.singularValues i₀ ^ 2 := by positivity
      have hnn : (0 : ℝ) ≤ s * A.singularValues i₀ / (s + A.singularValues i₀ ^ 2) := by
        positivity
      refine pow_lt_pow_left₀ ?_ hnn two_ne_zero
      rw [div_lt_div_iff₀ hs' ht']
      have hcube : s * (A.singularValues i₀ * A.singularValues i₀ * A.singularValues i₀)
          < t * (A.singularValues i₀ * A.singularValues i₀ * A.singularValues i₀) :=
        mul_lt_mul_of_pos_right hst (by positivity)
      nlinarith [hcube]
    have key := Finset.sum_lt_sum h1 ⟨i₀, Finset.mem_univ _, h2⟩
    simp only [hF]
    linarith
  have hcont : ContinuousOn F (Set.Ici (0 : ℝ)) := by
    rw [hF]
    refine continuousOn_const.add (continuousOn_finsetSum _ fun i _ => ?_)
    rcases eq_or_ne (A.singularValues i) 0 with hσ | hσ
    · have hzero : (fun t : ℝ => (t * A.singularValues i / (t + A.singularValues i ^ 2)) ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2)
          = fun _ : ℝ => 0 := by
        funext t; simp [hσ]
      rw [hzero]
      exact continuousOn_const
    · have hne : ∀ t ∈ Set.Ici (0 : ℝ), t + A.singularValues i ^ 2 ≠ 0 := by
        intro t ht
        simp only [Set.mem_Ici] at ht
        have hp : (0 : ℝ) < A.singularValues i ^ 2 :=
          pow_pos (lt_of_le_of_ne (A.singularValues_nonneg i) (Ne.symm hσ)) 2
        positivity
      exact (((continuousOn_id.mul continuousOn_const).div
        (continuousOn_id.add continuousOn_const) hne).pow 2).mul continuousOn_const
  have hlim : Filter.Tendsto F Filter.atTop (nhds (‖yδ‖ ^ 2)) := by
    have hterm : ∀ i : n, Filter.Tendsto
        (fun t : ℝ => t * A.singularValues i / (t + A.singularValues i ^ 2)) Filter.atTop
        (nhds (A.singularValues i)) := by
      intro i
      have h0 : Filter.Tendsto (fun t : ℝ => A.singularValues i ^ 2 /
          (t + A.singularValues i ^ 2)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop
          (Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id)
      have h1 : Filter.Tendsto (fun t : ℝ => A.singularValues i *
          (1 - A.singularValues i ^ 2 / (t + A.singularValues i ^ 2))) Filter.atTop
          (nhds (A.singularValues i * (1 - 0))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.sub h0)
      rw [sub_zero, mul_one] at h1
      refine h1.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
      have hne : t + A.singularValues i ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    have hsum : Filter.Tendsto (fun t : ℝ => ∑ i,
        (t * A.singularValues i / (t + A.singularValues i ^ 2)) ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2)
        Filter.atTop (nhds (∑ i, A.singularValues i ^ 2 *
          ‖(inner 𝕜 (A.rightSingularBasis i) (toEuclideanLin A.pinv yδ) : 𝕜)‖ ^ 2)) :=
      tendsto_finsetSum _ fun i _ => ((hterm i).pow 2).mul_const _
    rw [hF, hsplit]
    have hadd := (tendsto_const_nhds (α := ℝ) (f := Filter.atTop (α := ℝ))
      (x := ‖toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ‖ ^ 2)).add hsum
    rw [hParseval] at hadd
    simpa [add_comm] using hadd
  obtain ⟨M, hM0, hMF⟩ : ∃ M : ℝ, 0 ≤ M ∧ δ ^ 2 ≤ F M := by
    have hδ2 : δ ^ 2 < ‖yδ‖ ^ 2 := by nlinarith [hδ0, hhigh]
    have hev := (hlim.eventually (eventually_gt_nhds hδ2)).and
      (Filter.eventually_ge_atTop (0 : ℝ))
    obtain ⟨M, hM1, hM2⟩ := hev.exists
    exact ⟨M, hM2, hM1.le⟩
  have hF0lt : F 0 < δ ^ 2 := by
    rw [hF0]
    nlinarith [hd, norm_nonneg (toEuclideanLin A (toEuclideanLin A.pinv yδ) - yδ), hδ0]
  obtain ⟨a, ha, hFa⟩ : ∃ a ∈ Set.Icc (0 : ℝ) M, F a = δ ^ 2 :=
    intermediate_value_Icc hM0 (hcont.mono Set.Icc_subset_Ici_self) ⟨hF0lt.le, hMF⟩
  have ha0 : 0 < a := by
    rcases ha.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hFa; linarith
  have hres : ‖toEuclideanLin A (toEuclideanLin (A.tikhonov a) yδ) - yδ‖ = δ := by
    have h := hFeq a ha0
    rw [hFa] at h
    exact (pow_left_inj₀ (norm_nonneg _) hδ0.le two_ne_zero).1 h
  refine ⟨a, ⟨ha0, hres⟩, fun b hb => ?_⟩
  have hFb : F b = δ ^ 2 := by rw [← hFeq b hb.1, hb.2]
  exact hmono.injOn (Set.mem_Ici.2 hb.1.le) (Set.mem_Ici.2 ha0.le) (hFb.trans hFa.symm)

/-- **The discrepancy principle is regular**: if the data error tends to `0`, the regularized
solutions chosen by the discrepancy principle converge to the least-squares solution `A⁺ y` of the
exact problem ([kress1998numerical], Theorem 5.10). No estimate on `α` is needed: the discrepancy
condition alone forces the residual to `0`, and `A⁺ A` is the identity on the range of `Aᴴ`, where
all the Tikhonov solutions live. -/
theorem tendsto_tikhonov_of_norm_toEuclideanLin_sub_eq {ι : Type*} {l : Filter ι}
    {y : EuclideanSpace 𝕜 m} (hy : y ∈ LinearMap.range (toEuclideanLin A))
    {yδ : ι → EuclideanSpace 𝕜 m} {δ α : ι → ℝ} (hα : ∀ i, 0 < α i)
    (hyδ : ∀ i, ‖yδ i - y‖ ≤ δ i)
    (hres : ∀ i, ‖toEuclideanLin A (toEuclideanLin (A.tikhonov (α i)) (yδ i)) - yδ i‖ = δ i)
    (hδ : Filter.Tendsto δ l (nhds 0)) :
    Filter.Tendsto (fun i => toEuclideanLin (A.tikhonov (α i)) (yδ i)) l
      (nhds (toEuclideanLin A.pinv y)) := by
  obtain ⟨x₀, rfl⟩ := hy
  have hAp : toEuclideanLin A (toEuclideanLin A.pinv (toEuclideanLin A x₀))
      = toEuclideanLin A x₀ := by
    rw [← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply, Matrix.mul_assoc,
      ← Matrix.mul_assoc A, mul_pinv_mul_self]
  have himg : Filter.Tendsto (fun i => toEuclideanLin A
      (toEuclideanLin (A.tikhonov (α i)) (yδ i) - toEuclideanLin A.pinv (toEuclideanLin A x₀)))
      l (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ i, ‖toEuclideanLin A (toEuclideanLin (A.tikhonov (α i)) (yδ i)
        - toEuclideanLin A.pinv (toEuclideanLin A x₀))‖ ≤ 2 * δ i := by
      intro i
      rw [map_sub, hAp]
      calc ‖toEuclideanLin A (toEuclideanLin (A.tikhonov (α i)) (yδ i)) - toEuclideanLin A x₀‖
          ≤ ‖toEuclideanLin A (toEuclideanLin (A.tikhonov (α i)) (yδ i)) - yδ i‖
            + ‖yδ i - toEuclideanLin A x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ i + δ i := add_le_add (hres i).le (hyδ i)
        _ = 2 * δ i := by ring
    refine squeeze_zero (fun i => norm_nonneg _) hbound ?_
    simpa using hδ.const_mul 2
  have hfix : ∀ i, toEuclideanLin A.pinv (toEuclideanLin A
      (toEuclideanLin (A.tikhonov (α i)) (yδ i)
        - toEuclideanLin A.pinv (toEuclideanLin A x₀)))
      = toEuclideanLin (A.tikhonov (α i)) (yδ i)
        - toEuclideanLin A.pinv (toEuclideanLin A x₀) := by
    intro i
    rw [map_sub, map_sub, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
      ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
      pinv_mul_self_mul_tikhonov A (α i) (hα i), pinv_mul_self_mul_pinv]
  have hcontp : Continuous
      (toEuclideanLin A.pinv : EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 n) :=
    LinearMap.continuous_of_finiteDimensional _
  have hdiff : Filter.Tendsto (fun i => toEuclideanLin (A.tikhonov (α i)) (yδ i)
      - toEuclideanLin A.pinv (toEuclideanLin A x₀)) l (nhds 0) := by
    have hcomp := (hcontp.tendsto 0).comp himg
    simp only [Function.comp_def, map_zero] at hcomp
    exact hcomp.congr fun i => hfix i
  have hfinal := hdiff.add (tendsto_const_nhds
    (x := toEuclideanLin A.pinv (toEuclideanLin A x₀)) (f := l))
  simpa using hfinal

end Discrepancy

end Matrix

namespace Matrix

/-! ### The rectangular diagonal matrix -/

section RectDiagonal

variable {l m n : ℕ}

section Zero

variable {α : Type*} [Zero α]

/-- The rectangular "diagonal" matrix `diag(σ 0, σ 1, …) ∈ α^{m × n}` of
[quarteroni2000numerical] (1.9): `σ i` at the entries `(i, i)` with `i < min m n`, and `0`
elsewhere. It is indexed by a function on `ℕ`, so that one `σ` serves every shape and the
transpose is the same `σ` on the transposed shape; the values `σ i` for `i ≥ min m n` are never
read. -/
def rectDiagonal (σ : ℕ → α) : Matrix (Fin m) (Fin n) α :=
  of fun i j => if (i : ℕ) = j then σ i else 0

/-- The entries of a rectangular diagonal matrix. -/
theorem rectDiagonal_apply (σ : ℕ → α) (i : Fin m) (j : Fin n) :
    rectDiagonal σ i j = if (i : ℕ) = j then σ i else 0 := rfl

/-- Two rectangular diagonal matrices of the same shape agree when their diagonals agree below
`min m n`. -/
theorem rectDiagonal_congr {σ τ : ℕ → α} (h : ∀ i, i < m → i < n → σ i = τ i) :
    (rectDiagonal σ : Matrix (Fin m) (Fin n) α) = rectDiagonal τ := by
  ext i j
  simp only [rectDiagonal_apply]
  split_ifs with hij
  · exact h i i.isLt (hij ▸ j.isLt)
  · rfl

/-- The transpose of a rectangular diagonal matrix is the rectangular diagonal matrix of the
transposed shape, with the same diagonal. -/
theorem rectDiagonal_transpose (σ : ℕ → α) :
    (rectDiagonal σ : Matrix (Fin m) (Fin n) α)ᵀ = rectDiagonal σ := by
  ext i j
  simp only [transpose_apply, rectDiagonal_apply]
  split_ifs with h1 h2 h2
  · rw [h1]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

/-- A square rectangular diagonal matrix is a diagonal matrix. -/
theorem rectDiagonal_eq_diagonal (σ : ℕ → α) :
    (rectDiagonal σ : Matrix (Fin n) (Fin n) α) = diagonal fun i : Fin n => σ i := by
  ext i j
  simp only [rectDiagonal_apply, diagonal_apply, Fin.ext_iff]

end Zero

/-- The conjugate transpose of a rectangular diagonal matrix. -/
theorem conjTranspose_rectDiagonal {α : Type*} [AddMonoid α] [StarAddMonoid α] (σ : ℕ → α) :
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

/-- A rectangular diagonal matrix acts on a vector by scaling the coordinates it can see. -/
theorem rectDiagonal_mulVec (σ : ℕ → α) (x : Fin n → α) (i : Fin m) (h : (i : ℕ) < n) :
    (rectDiagonal σ *ᵥ x) i = σ i * x ⟨i, h⟩ := by
  rw [mulVec_apply_eq_sum, Finset.sum_eq_single ⟨i, h⟩]
  · simp [rectDiagonal_apply]
  · intro j _ hj
    rw [rectDiagonal_apply, ite_eq_right (fun hij => hj (Fin.ext hij.symm)), zero_mul]
  · exact fun h' => absurd (Finset.mem_univ _) h'

/-- A rectangular diagonal matrix kills the coordinates beyond its width. -/
theorem rectDiagonal_mulVec_of_le (σ : ℕ → α) (x : Fin n → α) (i : Fin m) (h : n ≤ i) :
    (rectDiagonal σ *ᵥ x) i = 0 := by
  rw [mulVec_apply_eq_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [rectDiagonal_apply,
    ite_eq_right (fun hij : (i : ℕ) = j => absurd (lt_of_eq_of_lt hij j.isLt) (not_lt.2 h)),
    zero_mul]

/-- The product of two rectangular diagonal matrices is the rectangular diagonal matrix of the
products, truncated at the inner dimension. -/
theorem rectDiagonal_mul_rectDiagonal (σ τ : ℕ → α) :
    (rectDiagonal σ : Matrix (Fin l) (Fin m) α) * (rectDiagonal τ : Matrix (Fin m) (Fin n) α)
      = rectDiagonal fun i => if i < m then σ i * τ i else 0 := by
  ext i j
  rw [mul_apply, rectDiagonal_apply]
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

/-- `Σᴴ Σ` is the square diagonal matrix of the `|σ i|²`, truncated at the height of `Σ`. -/
theorem conjTranspose_rectDiagonal_mul_self (σ : ℕ → 𝕜) :
    (rectDiagonal σ : Matrix (Fin m) (Fin n) 𝕜)ᴴ * rectDiagonal σ
      = diagonal fun j : Fin n => if (j : ℕ) < m then star (σ j) * σ j else 0 := by
  rw [conjTranspose_rectDiagonal, rectDiagonal_mul_rectDiagonal, rectDiagonal_eq_diagonal]
  rfl

/-- The unitary matrix whose columns are the vectors of an orthonormal basis `b` of a Euclidean
space: the change-of-basis matrix from the standard basis to `b`, whose `j`-th column is `b j`
(`Matrix.unitaryOfBasis_apply`). -/
noncomputable def unitaryOfBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) : Matrix ι ι 𝕜 :=
  (EuclideanSpace.basisFun ι 𝕜).toBasis.toMatrix b.toBasis

/-- The entries of `Matrix.unitaryOfBasis b` are the coordinates of the basis vectors: the `j`-th
column is `b j`. -/
theorem unitaryOfBasis_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) (i j : ι) : unitaryOfBasis b i j = b j i :=
  rfl

/-- The matrix of an orthonormal basis of a Euclidean space is unitary. -/
theorem unitaryOfBasis_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) : unitaryOfBasis b ∈ unitaryGroup ι 𝕜 :=
  (EuclideanSpace.basisFun ι 𝕜).toMatrix_orthonormalBasis_mem_unitary b

/-- The rows of the transpose of `Matrix.unitaryOfBasis b`, that is its columns, are the vectors
of `b`. -/
theorem unitaryOfBasis_transpose_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) (j : ι) :
    (unitaryOfBasis b)ᵀ j = ⇑(b j) := rfl

/-- The entries of `Uᴴ A V` are the inner products `⟪u_i, A v_j⟫` of the columns of `U` with the
images of the columns of `V`. -/
theorem star_mul_mul_apply (U : Matrix (Fin m) (Fin m) 𝕜) (A : Matrix (Fin m) (Fin n) 𝕜)
    (V : Matrix (Fin n) (Fin n) 𝕜) (i : Fin m) (j : Fin n) :
    (star U * A * V) i j = inner 𝕜 (WithLp.toLp 2 (Uᵀ i) : EuclideanSpace 𝕜 (Fin m))
      (toEuclideanLin A (WithLp.toLp 2 (Vᵀ j))) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin, dotProduct, mulVec,
    mul_apply, star_apply, transpose_apply, Pi.star_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The right singular vectors of `A`, sorted by decreasing singular value and extended by zero to
an `ℕ`-indexed family: `A.sortedRightSingularVec j` for `j < n` is the `j`-th vector of the sorted
orthonormal eigenbasis of `Aᴴ A`, paired with `(toEuclideanLin A).singularValues j`. The
`ℕ`-indexing matches `Matrix.rectDiagonal` and `LinearMap.singularValues`. -/
noncomputable def sortedRightSingularVec (A : Matrix (Fin m) (Fin n) 𝕜) (j : ℕ) :
    EuclideanSpace 𝕜 (Fin n) :=
  if h : j < n then
    (toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin
      ⟨j, h⟩
  else 0

/-- Below `n`, the sorted right singular vectors are the sorted eigenbasis of `Aᴴ A`. -/
theorem sortedRightSingularVec_of_lt (A : Matrix (Fin m) (Fin n) 𝕜) {j : ℕ} (h : j < n) :
    A.sortedRightSingularVec j = (toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis
      finrank_euclideanSpace_fin ⟨j, h⟩ := by
  rw [sortedRightSingularVec, dite_eq_left h]

/-- From `n` on, the sorted right singular vectors are zero. -/
theorem sortedRightSingularVec_of_le (A : Matrix (Fin m) (Fin n) 𝕜) {j : ℕ} (h : n ≤ j) :
    A.sortedRightSingularVec j = 0 := by
  rw [sortedRightSingularVec, dite_eq_right (not_lt.2 h)]

/-- The images of the sorted right singular vectors are pairwise orthogonal, with the squared
singular values as squared norms; beyond `n` they vanish. -/
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

/-- The image of the `j`-th sorted right singular vector has norm the `j`-th singular value. -/
theorem norm_toEuclideanLin_sortedRightSingularVec (A : Matrix (Fin m) (Fin n) 𝕜) (j : ℕ) :
    ‖toEuclideanLin A (A.sortedRightSingularVec j)‖ = (toEuclideanLin A).singularValues j := by
  by_cases hj : j < n
  · rw [sortedRightSingularVec_of_lt A hj,
      (toEuclideanLin A).norm_apply_eigenvectorBasis_adjoint_comp_self]
  · rw [sortedRightSingularVec_of_le A (not_lt.1 hj), map_zero, norm_zero,
      (toEuclideanLin A).singularValues_of_finrank_le (finrank_euclideanSpace_fin.trans_le
        (not_lt.1 hj))]

/-- The sorted right singular vectors are orthonormal below `n`. -/
theorem inner_sortedRightSingularVec (A : Matrix (Fin m) (Fin n) 𝕜) {i j : ℕ} (hi : i < n)
    (hj : j < n) :
    inner 𝕜 (A.sortedRightSingularVec i) (A.sortedRightSingularVec j) = if i = j then 1 else 0 := by
  rw [sortedRightSingularVec_of_lt A hi, sortedRightSingularVec_of_lt A hj,
    orthonormal_iff_ite.1 ((toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis
      finrank_euclideanSpace_fin).orthonormal]
  simp only [Fin.mk.injEq]

/-- The normalized images `A v_j / σ_j` of the sorted right singular vectors with `σ_j ≠ 0`,
placed at their own indices in `Fin m`, are orthonormal. -/
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

/-- **The singular value decomposition** ([quarteroni2000numerical] Property 1.7): every
`A : Matrix (Fin m) (Fin n) 𝕜` has unitary `U` (`m × m`) and `V` (`n × n`) with
`Uᴴ A V = Σ = diag(σ₀, σ₁, …)`, the rectangular diagonal matrix carrying Mathlib's sorted singular
values `(toEuclideanLin A).singularValues`, `σ₀ ≥ σ₁ ≥ … ≥ 0`. Over `𝕜 = ℝ` the factors are real
orthogonal matrices, which is the book's real case.

The columns of `V` are the sorted orthonormal eigenbasis of `Aᴴ A`
(`Matrix.sortedRightSingularVec`); the images `A v_j` are pairwise orthogonal of norm `σ_j`, so the
normalized ones with `σ_j ≠ 0` are orthonormal (`Matrix.orthonormal_leftSingular`) and, placed at
the same indices, extend to an orthonormal basis of `𝕜^m`
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), whose vectors are the columns of `U`.
-/
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

/-! #### Consequences of a singular value decomposition

Everything below takes an arbitrary factorization `Uᴴ A V = Σ` with unitary `U`, `V` and
rectangular diagonal `Σ` as its hypothesis — not necessarily the one `Matrix.exists_svd` produces —
and reads off the pseudoinverse, the kernel and the range, and the singular values. -/

/-- A factorization `Uᴴ A V = Σ` with unitary factors is `A = U Σ Vᴴ`. -/
theorem eq_mul_mul_star_of_star_mul_mul_eq {A : Matrix (Fin m) (Fin n) 𝕜}
    {U : Matrix (Fin m) (Fin m) 𝕜} {V : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin m) 𝕜)
    (hV : V ∈ unitaryGroup (Fin n) 𝕜) {S : Matrix (Fin m) (Fin n) 𝕜} (h : star U * A * V = S) :
    A = U * S * star V := by
  rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, mem_unitaryGroup_iff.1 hV, Matrix.mul_one,
    ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU, Matrix.one_mul]

/-- **The pseudoinverse from a singular value decomposition** ([quarteroni2000numerical]
Definition 1.15): if `Uᴴ A V = Σ = diag(σ)` with `U`, `V` unitary, then `A⁺ = V Σ⁺ Uᴴ` with
`Σ⁺ = diag(σ⁻¹)` — Lean's `0⁻¹ = 0` produces exactly the `diag(1/σ₁, …, 1/σ_r, 0, …, 0)` of the
book's (1.11), with no case split on the rank. The right-hand side satisfies the four Penrose
conditions, and `Matrix.pinv_unique` identifies it; nothing is assumed about `σ`, not even that it
is real. -/
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
    rw [ite_eq_left him, ite_eq_left hin, mul_inv_mul_self]
  have h2 : S' * S * S' = S' := by
    rw [hS, hS', rectDiagonal_mul_rectDiagonal, rectDiagonal_mul_rectDiagonal]
    refine rectDiagonal_congr fun i hin him => ?_
    rw [ite_eq_left hin, ite_eq_left him, inv_mul_mul_inv]
  have h3 : (S * S')ᴴ = S * S' := by
    rw [hS, hS', rectDiagonal_mul_rectDiagonal, conjTranspose_rectDiagonal]
    refine rectDiagonal_congr fun i _ _ => ?_
    simp only [Function.comp_apply]
    split_ifs
    · exact hstar i
    · exact star_zero 𝕜
  have h4 : (S' * S)ᴴ = S' * S := by
    rw [hS, hS', rectDiagonal_mul_rectDiagonal, conjTranspose_rectDiagonal]
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

/-- The pseudoinverse of a nonsingular matrix is its inverse ([quarteroni2000numerical] §1.9:
`A⁺ = A⁻¹` when `n = m = rank A`). -/
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

/-- The pseudoinverse of a matrix of full column rank — one whose Gram matrix `Aᴴ A` is
nonsingular — is `(Aᴴ A)⁻¹ Aᴴ` ([quarteroni2000numerical] §1.9: `A⁺ = (Aᵀ A)⁻¹ Aᵀ` when
`rank A = n < m`). `LinearAlgebra/Matrix/LeastSquares` has the same identity under the hypothesis
`LinearIndependent 𝕜 Aᵀ`. -/
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

/-- The columns of a unitary matrix are sent to the standard basis vectors by its adjoint. -/
private theorem star_mulVec_transpose_apply {V : Matrix (Fin n) (Fin n) 𝕜}
    (hV : V ∈ unitaryGroup (Fin n) 𝕜) (j : Fin n) : star V *ᵥ Vᵀ j = Pi.single j 1 := by
  have : Vᵀ j = V *ᵥ Pi.single j 1 := by rw [mulVec_single_one]; rfl
  rw [this, mulVec_mulVec, mem_unitaryGroup_iff'.1 hV, one_mulVec]

/-- A vector expanded along the columns of a unitary matrix, `x = ∑ (Vᴴ x)_j V_j`. -/
private theorem eq_sum_star_mulVec_smul_transpose {V : Matrix (Fin n) (Fin n) 𝕜}
    (hV : V ∈ unitaryGroup (Fin n) 𝕜) (x : Fin n → 𝕜) :
    x = ∑ j, (star V *ᵥ x) j • Vᵀ j := by
  conv_lhs => rw [← one_mulVec x, ← mem_unitaryGroup_iff.1 hV, ← mulVec_mulVec, mulVec_eq_sum]
  simp only [op_smul_eq_smul]

/-- **The kernel from a singular value decomposition** ([quarteroni2000numerical] §1.9): if
`Uᴴ A V = Σ = diag(σ)` with `U`, `V` unitary, the kernel of `A` is spanned by the columns of `V`
whose singular value vanishes — the columns `j ≥ m` beyond the height of `Σ`, and those with
`σ j = 0`; for sorted singular values these are `v_{r+1}, …, v_n`, `r` the rank. -/
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

/-- **The range from a singular value decomposition** ([quarteroni2000numerical] §1.9): if
`Uᴴ A V = Σ = diag(σ)` with `U`, `V` unitary, the range of `A` is spanned by the columns of `U`
whose singular value does not vanish — `u_1, …, u_r` for sorted singular values, `r` the rank. -/
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

/-! #### Uniqueness of the singular values

The singular values of any factorization `Uᴴ A V = Σ` are determined by `A`: the multiset of their
squares is the multiset of eigenvalues of `Aᴴ A`, and when they are sorted they are Mathlib's
`LinearMap.singularValues`. The bridge is the characteristic polynomial, which the unitary
similarity `Aᴴ A = V Σᴴ Σ Vᴴ` preserves. -/

section Uniqueness

/-- Two functions on a finite type with the same multiset of values, in a linear order, differ
by a permutation of the index type: sort both. -/
theorem _root_.exists_equiv_of_map_univ_val_eq {ι α : Type*} [Fintype ι] [LinearOrder α]
    {f g : ι → α} (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ e : ι ≃ ι, ∀ i, f (e i) = g i := by
  classical
  set e₀ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he₀
  have hperm : List.Perm (List.ofFn (f ∘ e₀)) (List.ofFn (g ∘ e₀)) := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map, ← Multiset.map_map,
      ← Multiset.map_map, Multiset.map_univ_val_equiv, h]
  set σf := Tuple.sort (f ∘ e₀) with hσf
  set σg := Tuple.sort (g ∘ e₀) with hσg
  have hsorted : List.ofFn (f ∘ e₀ ∘ σf) = List.ofFn (g ∘ e₀ ∘ σg) := by
    refine List.Perm.eq_of_sortedLE (Tuple.monotone_sort (f ∘ e₀)).sortedLE_ofFn
      (Tuple.monotone_sort (g ∘ e₀)).sortedLE_ofFn ?_
    exact ((σf.ofFn_comp_perm (f ∘ e₀)).trans hperm).trans (σg.ofFn_comp_perm (g ∘ e₀)).symm
  have hfun : f ∘ e₀ ∘ σf = g ∘ e₀ ∘ σg := List.ofFn_injective hsorted
  refine ⟨(e₀.symm.trans σg.symm).trans (σf.trans e₀), fun i => ?_⟩
  have := congrFun hfun (σg.symm (e₀.symm i))
  simpa using this

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The `n × n` diagonal matrix of real entries `d` is Hermitian. -/
private theorem isHermitian_diagonal_ofReal {n : Type*} [DecidableEq n] (d : n → ℝ) :
    (diagonal fun i => ((d i : ℝ) : 𝕜)).IsHermitian :=
  isHermitian_diagonal_iff.2 fun i => RCLike.conj_ofReal (d i)

/-- The characteristic polynomial of a unitary conjugate `U M Uᴴ` is that of `M`. -/
private theorem charpoly_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜) (M : Matrix n n 𝕜) :
    (U * M * star U).charpoly = M.charpoly := by
  rw [charpoly_mul_comm, ← Matrix.mul_assoc, mem_unitaryGroup_iff'.1 hU, Matrix.one_mul]

/-- The roots of the characteristic polynomial of a real diagonal matrix are its diagonal
entries. -/
private theorem roots_charpoly_diagonal_ofReal {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) :
    (diagonal fun i => ((d i : ℝ) : 𝕜)).charpoly.roots
      = Multiset.map (RCLike.ofReal ∘ d) Finset.univ.val := by
  rw [charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- **The singular values of a Hermitian matrix are the moduli of its eigenvalues**
([quarteroni2000numerical] §1.9, after (1.10)): there is a relabelling `e` with
`σ_{e i}(A) = |λ_i(A)|`. Since `Aᴴ A = A²` has the characteristic polynomial of `diag(λ_i²)`, the
multiset of eigenvalues of `Aᴴ A` is that of the `λ_i²`, and `Matrix.singularValues` are their
square roots. -/
theorem IsHermitian.exists_equiv_singularValues_eq_abs_eigenvalues {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ e : n ≃ n, ∀ i, A.singularValues (e i) = |hA.eigenvalues i| := by
  set hG := isHermitian_conjTranspose_mul_self A with hGdef
  -- the characteristic polynomial of `Aᴴ A = A²` is that of `diag(λ²)`
  have hchar : (Aᴴ * A).charpoly
      = (diagonal fun i => ((hA.eigenvalues i ^ 2 : ℝ) : 𝕜)).charpoly := by
    have hAA : Aᴴ * A = hA.eigenvectorUnitary * diagonal (fun i => ((hA.eigenvalues i ^ 2 : ℝ) : 𝕜))
        * star hA.eigenvectorUnitary := by
      conv_lhs => rw [hA.eq, hA.spectral_theorem, ← map_mul, Unitary.conjStarAlgAut_apply,
        diagonal_mul_diagonal]
      congr 2
      funext i
      simp [Function.comp_apply, sq]
    rw [hAA, Unitary.coe_star, charpoly_unitary_conj hA.eigenvectorUnitary.2]
  -- hence the multisets of eigenvalues agree
  have hmult : Multiset.map hG.eigenvalues Finset.univ.val
      = Multiset.map (fun i => hA.eigenvalues i ^ 2) Finset.univ.val := by
    have h1 := hG.roots_charpoly_eq_eigenvalues
    rw [hchar, roots_charpoly_diagonal_ofReal] at h1
    have h2 := congrArg (Multiset.map RCLike.re) h1
    simpa [Multiset.map_map, Function.comp_def] using h2.symm
  obtain ⟨e, he⟩ := exists_equiv_of_map_univ_val_eq hmult
  refine ⟨e, fun i => ?_⟩
  rw [singularValues, he i, Real.sqrt_sq_eq_abs]

variable {m n : ℕ}

/-- **Uniqueness of the singular values** ([quarteroni2000numerical] (1.10), `σ_i(A) = √λ_i(Aᴴ A)`):
if `Uᴴ A V = Σ = diag(σ)` with `U`, `V` unitary and `σ` antitone and nonnegative, then the `σ_i`
with `i < min m n` are Mathlib's sorted singular values `(toEuclideanLin A).singularValues i`.
From `Aᴴ A = V Σᴴ Σ Vᴴ` the characteristic polynomial of `Aᴴ A` is that of the diagonal matrix of
the `σ_i²` (padded by zeros), an antitone family, which the sorted-eigenvalue characterization
`LinearMap.IsSymmetric.eigenvalues_eq_of_antitone` identifies with the eigenvalues of `T† T`. -/
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
    isSymmetric_toEuclideanLin_iff.2 (isHermitian_diagonal_ofReal d)
  have hTT : LinearMap.adjoint T ∘ₗ T = toEuclideanLin (Aᴴ * A) := by
    rw [toEuclideanLin_mul, toEuclideanLin_conjTranspose]
  have hchar : (LinearMap.adjoint T ∘ₗ T).charpoly
      = (toEuclideanLin (diagonal fun j => ((d j : ℝ) : 𝕜))).charpoly := by
    rw [hTT, toEuclideanLin, toLpLin_eq_toLin, Matrix.charpoly_toLin, Matrix.charpoly_toLin,
      hgram, charpoly_unitary_conj hV]
  have heig : hTsym.eigenvalues hn = d := by
    rw [(hTsym.eigenvalues_eq_eigenvalues_iff hn hDsym hn).2 hchar]
    refine hDsym.eigenvalues_eq_of_antitone hn hdanti ?_
    rw [toEuclideanLin, toLpLin_eq_toLin, Matrix.charpoly_toLin, roots_charpoly_diagonal_ofReal]
  rw [T.singularValues_of_lt hn hin, heig]
  simp only [hd, ite_eq_left him]
  exact Real.sqrt_sq (hσ0 i)

end Uniqueness

end Matrix
