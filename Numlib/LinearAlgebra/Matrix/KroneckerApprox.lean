/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: beside `Mathlib.LinearAlgebra.Matrix.Kronecker`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Matrix.OperatorNorm
import Numlib.LinearAlgebra.Matrix.HermitianPart
import Numlib.LinearAlgebra.Matrix.Kronecker
import Numlib.LinearAlgebra.Matrix.Rank

/-!
# Approximation by Kronecker products

The Van Loan–Pitsianis rearrangement `𝓡` ([golub2013matrix] §12.3.6–12.3.9; Van Loan–Pitsianis
1993) turns Kronecker products into rank-one matrices: `𝓡(B ⊗ C) = vec B (vec C)ᵀ`. It permutes
entries, so it is an isometry for the Frobenius norm, and every nearest-Kronecker-product statement
is a nearest-low-rank statement for `𝓡(A)` pulled back.

**Typed indices.** For `A : Matrix (m₁ × m₂) (n₁ × n₂) K`, `kroneckerRearrange A : Matrix (n₁ × m₁)
(n₂ × m₂) K` has entry `A (i, k) (j, l)` at `((j, i), (l, k))`: row `(j, i)` is the block
`A_{ij}` in the book's column-major block order, column `(l, k)` indexes `vec A_{ij}` (Mathlib's
`Matrix.vec` is column-major, `vec X (j, i) = X i j`). The Kronecker product rank is the rank of
`𝓡(A)`.

The two structured nearest-rank lemmas of §12.3.8 (Lemmas 12.3.2–12.3.3) rest on the norm identities
`Matrix.norm_sub_smul_vecMulVec_self_sq` and `Matrix.norm_sub_skew_sq`.

## Main definitions

* `Matrix.kroneckerRearrange`, `Matrix.kroneckerRearrangeLinearEquiv`: the rearrangement `𝓡`.
* `Matrix.kroneckerRank`: the Kronecker product rank.

## Main statements

* `Matrix.kroneckerRearrange_kronecker`: `𝓡(B ⊗ C) = vec B (vec C)ᵀ`.
* `Matrix.frobenius_norm_kroneckerRearrange`: `𝓡` is a Frobenius isometry.
* `Matrix.eq_sum_kronecker_iff`: sums of Kronecker products are rearranged sums of rank-one
  matrices (the proof of [golub2013matrix] Theorem 12.3.1).
* `Matrix.kroneckerRank_le_iff`: the Kronecker rank is the least number of Kronecker terms.
* `Matrix.exists_kroneckerSVD`: the Kronecker product SVD ([golub2013matrix] Theorem 12.3.1).
* `Matrix.isMinOn_frobenius_norm_sub_symm_rank_le_one`: [golub2013matrix] Lemma 12.3.2.
* `Matrix.exists_eq_vecMulVec_sub_vecMulVec_of_rank_le_two`: a skew-symmetric matrix of rank at
  most two is `x yᵀ − y xᵀ`.
* `Matrix.isMinOn_frobenius_norm_sub_skew_rank_le_two`: [golub2013matrix] Lemma 12.3.3.

## References

* [golub2013matrix], §12.3.6–12.3.9.
-/

open scoped Kronecker Matrix

namespace Matrix

variable {R : Type*} {m₁ m₂ n₁ n₂ : Type*}

/-! ### The rearrangement -/

/-- The Van Loan–Pitsianis rearrangement `𝓡(A)` ([golub2013matrix] §12.3.6, (12.3.16) and the
display after it): row `(j, i)` is `vec (A_{ij})ᵀ` for the block `A_{ij} = A (i, ·) (j, ·)`. -/
def kroneckerRearrange (A : Matrix (m₁ × m₂) (n₁ × n₂) R) : Matrix (n₁ × m₁) (n₂ × m₂) R :=
  of fun ji lk => A (ji.2, lk.2) (ji.1, lk.1)

@[simp]
theorem kroneckerRearrange_apply (A : Matrix (m₁ × m₂) (n₁ × n₂) R) (i : m₁) (j : n₁) (k : m₂)
    (l : n₂) : kroneckerRearrange A (j, i) (l, k) = A (i, k) (j, l) :=
  rfl

/-- The rearrangement as a linear equivalence. -/
def kroneckerRearrangeLinearEquiv [Semiring R] :
    Matrix (m₁ × m₂) (n₁ × n₂) R ≃ₗ[R] Matrix (n₁ × m₁) (n₂ × m₂) R where
  toFun := kroneckerRearrange
  invFun B := of fun ik jl => B (jl.1, ik.1) (jl.2, ik.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem kroneckerRearrangeLinearEquiv_apply [Semiring R] (A : Matrix (m₁ × m₂) (n₁ × n₂) R) :
    kroneckerRearrangeLinearEquiv A = kroneckerRearrange A :=
  rfl

/-- `𝓡(B ⊗ C) = vec B (vec C)ᵀ` ([golub2013matrix] §12.3.6). -/
theorem kroneckerRearrange_kronecker [Mul R] (B : Matrix m₁ n₁ R) (C : Matrix m₂ n₂ R) :
    kroneckerRearrange (B ⊗ₖ C) = vecMulVec (vec B) (vec C) := by
  ext ⟨j, i⟩ ⟨l, k⟩
  rfl

/-- Sums of Kronecker products rearrange to sums of rank-one matrices: the proof of
[golub2013matrix] Theorem 12.3.1. -/
theorem eq_sum_kronecker_iff [CommSemiring R] {τ : Type*} [Fintype τ]
    (A : Matrix (m₁ × m₂) (n₁ × n₂) R) (σ : τ → R) (u : τ → n₁ × m₁ → R) (v : τ → n₂ × m₂ → R) :
    A = ∑ k, σ k • (unvec (u k) ⊗ₖ unvec (v k))
      ↔ kroneckerRearrange A = ∑ k, σ k • vecMulVec (u k) (v k) := by
  have h : kroneckerRearrangeLinearEquiv (∑ k, σ k • (unvec (u k) ⊗ₖ unvec (v k)))
      = ∑ k, σ k • vecMulVec (u k) (v k) := by
    simp only [map_sum, map_smul, kroneckerRearrangeLinearEquiv_apply,
      kroneckerRearrange_kronecker, vec_unvec]
  rw [← h, ← kroneckerRearrangeLinearEquiv_apply, kroneckerRearrangeLinearEquiv.injective.eq_iff]

/-- The Kronecker product rank ([golub2013matrix] §12.3.6): the rank of `𝓡(A)`. -/
noncomputable def kroneckerRank [CommRing R] [Fintype n₂] [Fintype m₂]
    (A : Matrix (m₁ × m₂) (n₁ × n₂) R) : ℕ :=
  (kroneckerRearrange A).rank

/-- The rearrangement of a sum of Kronecker products is the product of the matrix whose columns
are the `vec`s of the left factors with the matrix whose rows are the `vec`s of the right ones. -/
theorem kroneckerRearrange_sum_kronecker [CommSemiring R] {r : Type*} [Fintype r]
    (B : r → Matrix m₁ n₁ R) (C : r → Matrix m₂ n₂ R) :
    kroneckerRearrange (∑ k, B k ⊗ₖ C k)
      = (of fun x k => vec (B k) x : Matrix (n₁ × m₁) r R) * of fun k y => vec (C k) y := by
  rw [← kroneckerRearrangeLinearEquiv_apply, map_sum]
  ext x y
  simp only [kroneckerRearrangeLinearEquiv_apply, kroneckerRearrange_kronecker, Matrix.sum_apply,
    vecMulVec_apply, mul_apply, of_apply]

/-- **The Kronecker product rank counts Kronecker terms** ([golub2013matrix] §12.3.6):
`kroneckerRank A ≤ r` iff `A` is a sum of `r` Kronecker products. The rank factorization of `𝓡(A)`
(`Matrix.rank_le_iff_exists_mul`) read through `kroneckerRearrange_sum_kronecker`. -/
theorem kroneckerRank_le_iff {K : Type*} [Field K] [Fintype m₂] [Fintype n₂]
    (A : Matrix (m₁ × m₂) (n₁ × n₂) K) (r : ℕ) :
    kroneckerRank A ≤ r ↔ ∃ (B : Fin r → Matrix m₁ n₁ K) (C : Fin r → Matrix m₂ n₂ K),
      A = ∑ k, B k ⊗ₖ C k := by
  rw [kroneckerRank, rank_le_iff_exists_mul]
  constructor
  · rintro ⟨P, Q, hPQ⟩
    refine ⟨fun k => unvec fun x => P x k, fun k => unvec (Q k), ?_⟩
    apply kroneckerRearrangeLinearEquiv.injective
    rw [kroneckerRearrangeLinearEquiv_apply, kroneckerRearrangeLinearEquiv_apply,
      kroneckerRearrange_sum_kronecker, hPQ]
    rfl
  · rintro ⟨B, C, rfl⟩
    exact ⟨_, _, kroneckerRearrange_sum_kronecker B C⟩

/-! ### The rearrangement is a Frobenius isometry -/

section Norm

open scoped Matrix.Norms.Frobenius

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]

/-- `‖𝓡(A)‖_F = ‖A‖_F` ([golub2013matrix] §12.3.6, the display after (12.3.14)): `𝓡` permutes the
entries. -/
theorem frobenius_norm_kroneckerRearrange (A : Matrix (m₁ × m₂) (n₁ × n₂) 𝕜) :
    ‖kroneckerRearrange A‖ = ‖A‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [frobenius_norm_sq_eq_sum_sq, frobenius_norm_sq_eq_sum_sq, ← Fintype.sum_prod_type',
    ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.prodProdProdComm n₁ m₁ n₂ m₂).trans (Equiv.prodComm _ _)) _ _
    fun _ => rfl

end Norm

/-! ### The Kronecker product SVD -/

section KroneckerSVD

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Entrywise conjugation preserves orthonormality of Euclidean vectors:
`⟪x̄, ȳ⟫ = ⟪y, x⟫`. -/
theorem orthonormal_toLp_star {ι p : Type*} [Fintype p] {v : ι → EuclideanSpace 𝕜 p}
    (hv : Orthonormal 𝕜 v) : Orthonormal 𝕜 fun k => WithLp.toLp 2 (star ⇑(v k)) := by
  classical
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_toLp, star_star,
    dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, hv j i]
  exact if_congr eq_comm rfl rfl

/-- **The sorted singular expansion** of a matrix over any finite index types:
`M = ∑_{k < rank M} σ_k u_k v_kᴴ` with orthonormal left vectors `u`, orthonormal right vectors `v`
and positive sorted singular values `σ_k = M.sortedSingularValues k`. The right vectors are right
singular vectors relabelled by `Matrix.exists_equiv_singularValues_eq_sortedSingularValues`. -/
theorem exists_eq_sum_sortedSingularValues_smul_vecMulVec {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq q] (M : Matrix p q 𝕜) :
    ∃ (u : Fin M.rank → EuclideanSpace 𝕜 p) (v : Fin M.rank → EuclideanSpace 𝕜 q),
      Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧ (∀ k : Fin M.rank, 0 < M.sortedSingularValues k) ∧
      M = ∑ k : Fin M.rank,
        ((M.sortedSingularValues k : ℝ) : 𝕜) • vecMulVec ⇑(u k) (star ⇑(v k)) := by
  classical
  obtain ⟨e, he⟩ := M.exists_equiv_singularValues_eq_sortedSingularValues
  have hr : M.rank ≤ Fintype.card q := (rank_le_card_width M).trans_eq rfl
  set b := M.rightSingularBasis with hb
  let w : Fin M.rank → q := fun k => e (Fin.castLE hr k)
  have hw : Function.Injective w := e.injective.comp (Fin.castLE_injective hr)
  have hσw : ∀ k : Fin M.rank, M.singularValues (w k) = M.sortedSingularValues k :=
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
      simp only [mul_apply, star_apply, Matrix.sum_apply, vecMulVec_apply, ofLp_toEuclideanLin,
        mulVec, dotProduct, Pi.star_apply, rightSingularUnitary,
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
      simp only [smul_apply, vecMulVec_apply, smul_eq_mul, WithLp.ofLp_smul, Pi.smul_apply]
      have := hne k
      field_simp
      rfl

/-- **The Kronecker product SVD** ([golub2013matrix] Theorem 12.3.1): with `r` the Kronecker rank
of `A`, `A = ∑_{k < r} σ_k U_k ⊗ V_k` with Frobenius-orthonormal families `U`, `V` and
`σ_k = σ_k(𝓡(A)) > 0` the sorted singular values of the rearrangement. The sorted singular
expansion of `𝓡(A)` pulled back by `Matrix.eq_sum_kronecker_iff`. -/
theorem exists_kroneckerSVD [Fintype m₂] [Fintype n₁] [Fintype n₂] [Fintype m₁] [DecidableEq n₂]
    [DecidableEq m₂] (A : Matrix (m₁ × m₂) (n₁ × n₂) 𝕜) :
    ∃ (U : Fin (kroneckerRank A) → Matrix m₁ n₁ 𝕜) (V : Fin (kroneckerRank A) → Matrix m₂ n₂ 𝕜),
      Orthonormal 𝕜 (fun k => WithLp.toLp 2 (vec (U k))) ∧
      Orthonormal 𝕜 (fun k => WithLp.toLp 2 (vec (V k))) ∧
      (∀ k : Fin (kroneckerRank A), 0 < (kroneckerRearrange A).sortedSingularValues k) ∧
      A = ∑ k : Fin (kroneckerRank A),
        (((kroneckerRearrange A).sortedSingularValues k : ℝ) : 𝕜) • (U k ⊗ₖ V k) := by
  obtain ⟨u, v, hu, hv, hpos, h⟩ :=
    exists_eq_sum_sortedSingularValues_smul_vecMulVec (kroneckerRearrange A)
  refine ⟨fun k => unvec ⇑(u k), fun k => unvec (star ⇑(v k)), hu, orthonormal_toLp_star hv,
    hpos, ?_⟩
  exact (eq_sum_kronecker_iff A
    (fun k : Fin (kroneckerRank A) => (((kroneckerRearrange A).sortedSingularValues k : ℝ) : 𝕜))
    (fun k => ⇑(u k)) (fun k => star ⇑(v k))).2 h

end KroneckerSVD

/-! ### The norm identities behind Lemmas 12.3.2 and 12.3.3 -/

section Identities

open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n]

/-- The squared Frobenius norm of a real matrix is the sum of the squared entries. -/
private theorem frobenius_norm_sq_real (A : Matrix n n ℝ) : ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_sq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- The identity behind [golub2013matrix] Lemma 12.3.2 (P12.3.11): for a unit vector `x`,
`‖M − α x xᵀ‖_F² = ‖M‖_F² − 2 α xᵀ M x + α²`; the book writes `xᵀ T x` with `T = (M + Mᵀ)/2`, the
same number. -/
theorem norm_sub_smul_vecMulVec_self_sq (M : Matrix n n ℝ) {x : n → ℝ} (hx : x ⬝ᵥ x = 1)
    (α : ℝ) : ‖M - α • vecMulVec x x‖ ^ 2 = ‖M‖ ^ 2 - 2 * α * (x ⬝ᵥ (M *ᵥ x)) + α ^ 2 := by
  have hxx : (∑ i, ∑ j, x i ^ 2 * x j ^ 2) = 1 := by
    rw [← Finset.sum_mul_sum, ← sq]
    simp only [dotProduct, ← sq] at hx
    rw [hx, one_pow]
  have hM : x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, x i * M i j * x j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [frobenius_norm_sq_real, frobenius_norm_sq_real, hM]
  conv_rhs => rw [← mul_one (α ^ 2), ← hxx]
  simp only [sub_apply, smul_apply, vecMulVec_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The identity behind [golub2013matrix] Lemma 12.3.3 (P12.3.12):
`‖M − (x yᵀ − y xᵀ)‖_F² = ‖M‖_F² + 2 ‖x‖² ‖y‖² − 2 (xᵀ y)² − 2 (xᵀ M y − yᵀ M x)`; the book writes
the last term as `4 xᵀ S y` with `S = (M − Mᵀ)/2`, the same number. -/
theorem norm_sub_skew_sq (M : Matrix n n ℝ) (x y : n → ℝ) :
    ‖M - (vecMulVec x y - vecMulVec y x)‖ ^ 2
      = ‖M‖ ^ 2 + 2 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) - 2 * (x ⬝ᵥ y) ^ 2
        - 2 * (x ⬝ᵥ (M *ᵥ y) - y ⬝ᵥ (M *ᵥ x)) := by
  have h1 : 2 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) = ∑ i, ∑ j, (x i ^ 2 * y j ^ 2 + y i ^ 2 * x j ^ 2) := by
    have ha : (x ⬝ᵥ x) * (y ⬝ᵥ y) = ∑ i, ∑ j, x i ^ 2 * y j ^ 2 := by
      simp only [dotProduct, Finset.sum_mul_sum, sq]
    have hb : (x ⬝ᵥ x) * (y ⬝ᵥ y) = ∑ i, ∑ j, y i ^ 2 * x j ^ 2 := by
      rw [mul_comm]
      simp only [dotProduct, Finset.sum_mul_sum, sq]
    simp only [Finset.sum_add_distrib]
    rw [← ha, ← hb]
    ring
  have h2 : (x ⬝ᵥ y) ^ 2 = ∑ i, ∑ j, x i * y i * (x j * y j) := by
    simp only [dotProduct, sq, Finset.sum_mul_sum]
  have h3 : x ⬝ᵥ (M *ᵥ y) = ∑ i, ∑ j, x i * M i j * y j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have h4 : y ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, x j * M i j * y i := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [frobenius_norm_sq_real, frobenius_norm_sq_real, h1, h2, h3, h4]
  simp only [sub_apply, vecMulVec_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Identities

/-! ### Lemma 12.3.2: the nearest symmetric rank-one matrix -/

section Lemma1232

open scoped Matrix.Norms.Frobenius InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral decomposition of a real symmetric matrix as a sum of rank-one projections:
`A = ∑ₗ λₗ qₗ qₗᵀ` over an orthonormal eigenbasis. -/
theorem IsHermitian.eq_sum_smul_vecMulVec {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A = ∑ l, hA.eigenvalues l • vecMulVec ⇑(hA.eigenvectorBasis l) ⇑(hA.eigenvectorBasis l) := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext i j
  simp only [mul_apply, diagonal_apply, Function.comp_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.sum_apply, smul_apply,
    vecMulVec_apply, smul_eq_mul, star_apply, star_trivial, IsHermitian.eigenvectorUnitary_apply,
    RCLike.ofReal_real_eq_id, id_eq]
  exact Finset.sum_congr rfl fun l _ => by ring

omit [DecidableEq n] in
/-- The dot product of a real Euclidean vector with itself is its squared norm. -/
private theorem dotProduct_self_ofLp_eq_norm_sq (x : EuclideanSpace ℝ n) : ⇑x ⬝ᵥ ⇑x = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- The eigenvectors of a real symmetric matrix are unit vectors. -/
private theorem dotProduct_eigenvectorBasis_self {A : Matrix n n ℝ} (hA : A.IsHermitian) (l : n) :
    ⇑(hA.eigenvectorBasis l) ⬝ᵥ ⇑(hA.eigenvectorBasis l) = 1 := by
  rw [dotProduct_self_ofLp_eq_norm_sq, hA.eigenvectorBasis.orthonormal.1 l, one_pow]

omit [DecidableEq n] in
/-- A real symmetric matrix of rank at most one is `β x xᵀ` for a unit vector `x`. -/
theorem exists_eq_smul_vecMulVec_self_of_rank_le_one [Nonempty n] {Z : Matrix n n ℝ}
    (hZ : Z.IsSymm) (hr : Z.rank ≤ 1) :
    ∃ (β : ℝ) (x : n → ℝ), x ⬝ᵥ x = 1 ∧ Z = β • vecMulVec x x := by
  classical
  have hH : Z.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hZ
  rw [hH.rank_eq_card_non_zero_eigs, Fintype.card_le_one_iff] at hr
  by_cases h0 : ∀ l, hH.eigenvalues l = 0
  · refine ⟨0, _, dotProduct_eigenvectorBasis_self hH (Classical.arbitrary n), ?_⟩
    conv_lhs => rw [hH.eq_sum_smul_vecMulVec]
    simp [h0]
  · push Not at h0
    obtain ⟨l₀, hl₀⟩ := h0
    refine ⟨hH.eigenvalues l₀, _, dotProduct_eigenvectorBasis_self hH l₀, ?_⟩
    conv_lhs => rw [hH.eq_sum_smul_vecMulVec]
    refine Finset.sum_eq_single l₀ (fun l _ hl => ?_) (by simp)
    by_cases h : hH.eigenvalues l = 0
    · rw [h, zero_smul]
    · exact absurd (congrArg Subtype.val (hr ⟨l, h⟩ ⟨l₀, hl₀⟩)) hl

/-- **The Rayleigh quotient bound**: for a real symmetric `A` and a unit vector `x`,
`|xᵀ A x| ≤ max |λ|`. -/
theorem abs_dotProduct_mulVec_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {k : n}
    (hk : ∀ i, |hA.eigenvalues i| ≤ |hA.eigenvalues k|) {x : n → ℝ} (hx : x ⬝ᵥ x = 1) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ |hA.eigenvalues k| := by
  set q := fun l => ⇑(hA.eigenvectorBasis l)
  have hexp : x ⬝ᵥ (A *ᵥ x) = ∑ l, hA.eigenvalues l * (q l ⬝ᵥ x) ^ 2 := by
    conv_lhs => rw [hA.eq_sum_smul_vecMulVec]
    rw [sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, dotProduct_comm x (q l), sq]
  have hpars : ∑ l, (q l ⬝ᵥ x) ^ 2 = 1 := by
    have h := hA.eigenvectorBasis.sum_sq_norm_inner_right (WithLp.toLp 2 x)
    rw [← dotProduct_self_ofLp_eq_norm_sq, hx] at h
    rw [← h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [EuclideanSpace.inner_eq_star_dotProduct, Real.norm_eq_abs, sq_abs]
    simp [q, dotProduct_comm]
  rw [hexp]
  calc |∑ l, hA.eigenvalues l * (q l ⬝ᵥ x) ^ 2|
      ≤ ∑ l, |hA.eigenvalues l| * (q l ⬝ᵥ x) ^ 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp_rw [abs_mul, abs_sq]
    _ ≤ ∑ l, |hA.eigenvalues k| * (q l ⬝ᵥ x) ^ 2 :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hk l) (sq_nonneg _)
    _ = |hA.eigenvalues k| := by rw [← Finset.mul_sum, hpars, mul_one]

omit [DecidableEq n] in
/-- The quadratic form of the symmetric part of a real matrix is that of the matrix. -/
theorem dotProduct_mulVec_hermitianPart (M : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (hermitianPart M *ᵥ x) = x ⬝ᵥ (M *ᵥ x) := by
  rw [hermitianPart, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add,
    conjTranspose_eq_transpose_of_trivial, dotProduct_mulVec x Mᵀ, vecMul_transpose,
    dotProduct_comm (M *ᵥ x) x, smul_eq_mul]
  ring

/-- **[golub2013matrix] Lemma 12.3.2**: with `T = (M + Mᵀ)/2` and `α_k` an eigenvalue of `T` of
largest modulus, eigenvector `q_k`, the matrix `α_k q_k q_kᵀ` is a nearest symmetric matrix of rank
at most one to `M` in the Frobenius norm. (The book's "`rank(Z) = 1`" fails when `T = 0`, where the
infimum over rank exactly one is not attained; `rank ≤ 1` is the correct reading.) -/
theorem isMinOn_frobenius_norm_sub_symm_rank_le_one (M : Matrix n n ℝ) {k : n}
    (hk : ∀ i, |(hermitianPart_isHermitian M).eigenvalues i|
      ≤ |(hermitianPart_isHermitian M).eigenvalues k|) :
    IsMinOn (fun Z => ‖M - Z‖) {Z | Z.IsSymm ∧ Z.rank ≤ 1}
      ((hermitianPart_isHermitian M).eigenvalues k
        • vecMulVec ⇑((hermitianPart_isHermitian M).eigenvectorBasis k)
          ⇑((hermitianPart_isHermitian M).eigenvectorBasis k)) := by
  set hT := hermitianPart_isHermitian M
  set α := hT.eigenvalues k
  set q := ⇑(hT.eigenvectorBasis k)
  have hq : q ⬝ᵥ q = 1 := dotProduct_eigenvectorBasis_self hT k
  have hqM : q ⬝ᵥ (M *ᵥ q) = α := by
    rw [← dotProduct_mulVec_hermitianPart, hT.mulVec_eigenvectorBasis, dotProduct_smul, hq,
      smul_eq_mul, mul_one]
  have hopt : ‖M - α • vecMulVec q q‖ ^ 2 = ‖M‖ ^ 2 - α ^ 2 := by
    rw [norm_sub_smul_vecMulVec_self_sq M hq, hqM]
    ring
  rintro Z ⟨hZs, hZr⟩
  rcases isEmpty_or_nonempty n with hn | hn
  · change ‖M - α • vecMulVec q q‖ ≤ ‖M - Z‖
    rw [Subsingleton.elim Z (α • vecMulVec q q)]
  obtain ⟨β, x, hx, rfl⟩ := exists_eq_smul_vecMulVec_self_of_rank_le_one hZs hZr
  have ht : |x ⬝ᵥ (M *ᵥ x)| ≤ |α| := by
    rw [← dotProduct_mulVec_hermitianPart]
    exact abs_dotProduct_mulVec_le hT hk hx
  have ht2 := sq_le_sq.2 ht
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  change ‖M - α • vecMulVec q q‖ ^ 2 ≤ ‖M - β • vecMulVec x x‖ ^ 2
  rw [hopt, norm_sub_smul_vecMulVec_self_sq M hx]
  nlinarith [sq_nonneg (β - x ⬝ᵥ (M *ᵥ x))]

end Lemma1232

/-! ### Lemma 12.3.3: the nearest skew-symmetric matrix of rank at most two -/

section Lemma1233

open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n]

/-- **The normal form of a skew-symmetric matrix of rank at most two**: over a field in which
`2 ≠ 0`, `Zᵀ = −Z` and `rank Z ≤ 2` give `Z = x yᵀ − y xᵀ`. If `c = Z i j ≠ 0`, the `3 × 3` minors
on rows `i, j, l` and columns `i, j, k` vanish, which reads `c Z = zᵢ zⱼᵀ − zⱼ zᵢᵀ` for the
columns `zᵢ, zⱼ` of `Z`. -/
theorem exists_eq_vecMulVec_sub_vecMulVec_of_rank_le_two {K : Type*} [Field K] [NeZero (2 : K)]
    {Z : Matrix n n K} (hZ : Zᵀ = -Z) (hr : Z.rank ≤ 2) :
    ∃ x y : n → K, Z = vecMulVec x y - vecMulVec y x := by
  have hs : ∀ i j, Z i j = -Z j i := fun i j => by
    simpa using congrFun (congrFun hZ j) i
  have hd : ∀ i, Z i i = 0 := fun i => by
    have h2 : (2 : K) * Z i i = 0 := by linear_combination hs i i
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  by_cases h0 : ∀ i j, Z i j = 0
  · exact ⟨0, 0, by ext i j; simp [h0]⟩
  push Not at h0
  obtain ⟨i, j, hij⟩ := h0
  have key : ∀ l k, Z i j * Z l k = Z i k * Z l j - Z j k * Z l i := by
    intro l k
    by_contra hne
    have hdet : (Z.submatrix ![i, j, l] ![i, j, k]).det ≠ 0 := by
      have e : (Z.submatrix ![i, j, l] ![i, j, k]).det
          = Z i j * (Z i j * Z l k - (Z i k * Z l j - Z j k * Z l i)) := by
        rw [det_fin_three]
        simp only [submatrix_apply, cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons,
          hd]
        rw [hs j i]
        ring
      rw [e]
      exact mul_ne_zero hij (sub_ne_zero.2 hne)
    have := card_le_rank_of_det_submatrix_ne_zero Z hdet
    omega
  refine ⟨(Z i j)⁻¹ • fun l => Z l i, fun l => Z l j, ?_⟩
  ext l k
  simp only [sub_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination key l k + Z l j * hs i k - Z l i * hs j k

variable [DecidableEq n]

/-- `xᵀ A y ≤ ‖A‖₂ ‖x‖₂ ‖y‖₂` for a real matrix. -/
private theorem dotProduct_mulVec_le_lpOpNorm_two (A : Matrix n n ℝ) (x y : n → ℝ) :
    x ⬝ᵥ (A *ᵥ y) ≤ lpOpNorm 2 A * (‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖) := by
  have h1 : x ⬝ᵥ (A *ᵥ y) = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 (A *ᵥ y)) := by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  have h2 := lpSeminorm_mulVec_le 2 A y
  simp only [lpSeminorm_apply] at h2
  rw [h1]
  calc inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 (A *ᵥ y))
      ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 (A *ᵥ y)‖ := real_inner_le_norm _ _
    _ ≤ ‖WithLp.toLp 2 x‖ * (lpOpNorm 2 A * ‖WithLp.toLp 2 y‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = _ := by ring

omit [DecidableEq n] in
/-- `‖x‖₂² = xᵀ x` for a real vector. -/
private theorem norm_toLp_sq (x : n → ℝ) : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]

omit [DecidableEq n] in
/-- `xᵀ M y − yᵀ M x = 2 xᵀ S y` for the skew-symmetric part `S = (M − Mᵀ)/2`. -/
private theorem dotProduct_mulVec_sub_dotProduct_mulVec (M : Matrix n n ℝ) (x y : n → ℝ) :
    x ⬝ᵥ (M *ᵥ y) - y ⬝ᵥ (M *ᵥ x) = 2 * (x ⬝ᵥ (((1 / 2 : ℝ) • (M - Mᵀ)) *ᵥ y)) := by
  rw [smul_mulVec, sub_mulVec, dotProduct_smul, dotProduct_sub, dotProduct_mulVec x Mᵀ,
    vecMul_transpose, dotProduct_comm (M *ᵥ x) y, smul_eq_mul]
  ring

/-- **[golub2013matrix] Lemma 12.3.3**: with `S = (M − Mᵀ)/2`, `μ = ‖S‖₂` and orthonormal `u, v`
with `S v = μ u` (the book's `S [u | v] = [u | v] [0 μ; −μ 0]`, whose other half `S u = −μ v`
is not needed), the matrix `μ (u vᵀ − v uᵀ)` is a nearest skew-symmetric matrix of rank at most
two to `M` in the Frobenius norm. Every competitor is `x yᵀ − y xᵀ` with `x ⊥ y`
(`Matrix.exists_eq_vecMulVec_sub_vecMulVec_of_rank_le_two`, then Gram–Schmidt), its distance is
`‖M‖² + 2 ‖x‖² ‖y‖² − 4 xᵀ S y` (`Matrix.norm_sub_skew_sq`), and `xᵀ S y ≤ μ ‖x‖ ‖y‖`. (The
book's "rank 2" fails when `S = 0`, as in Lemma 12.3.2; `rank ≤ 2` is the correct reading.) -/
theorem isMinOn_frobenius_norm_sub_skew_rank_le_two (M : Matrix n n ℝ) {u v : n → ℝ} {μ : ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0)
    (hSv : ((1 / 2 : ℝ) • (M - Mᵀ)) *ᵥ v = μ • u)
    (hμ : μ = lpOpNorm 2 ((1 / 2 : ℝ) • (M - Mᵀ))) :
    IsMinOn (fun Z => ‖M - Z‖) {Z | Zᵀ = -Z ∧ Z.rank ≤ 2}
      (μ • (vecMulVec u v - vecMulVec v u)) := by
  have hμ0 : 0 ≤ μ := hμ ▸ lpOpNorm_nonneg _ _
  have hopt : ‖M - μ • (vecMulVec u v - vecMulVec v u)‖ ^ 2 = ‖M‖ ^ 2 - 2 * μ ^ 2 := by
    have e : μ • (vecMulVec u v - vecMulVec v u)
        = vecMulVec (μ • u) v - vecMulVec v (μ • u) := by
      rw [smul_sub, smul_vecMulVec, vecMulVec_smul]
    rw [e, norm_sub_skew_sq, dotProduct_mulVec_sub_dotProduct_mulVec, hSv]
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, hu, hv, huv]
    ring
  rintro Z ⟨hZs, hZr⟩
  obtain ⟨x, y, rfl⟩ := exists_eq_vecMulVec_sub_vecMulVec_of_rank_le_two hZs hZr
  -- Gram–Schmidt: replace `y` by its component orthogonal to `x`.
  set y' := y - (x ⬝ᵥ y / x ⬝ᵥ x) • x with hy'
  have hZ' : vecMulVec x y - vecMulVec y x = vecMulVec x y' - vecMulVec y' x := by
    rw [hy', vecMulVec_sub, sub_vecMulVec, vecMulVec_smul, smul_vecMulVec]
    abel
  have hxy' : x ⬝ᵥ y' = 0 := by
    rw [hy', dotProduct_sub, dotProduct_smul, smul_eq_mul]
    by_cases hx : x ⬝ᵥ x = 0
    · rw [dotProduct_self_eq_zero.1 hx]
      simp
    · field_simp
      ring
  have hb := dotProduct_mulVec_le_lpOpNorm_two ((1 / 2 : ℝ) • (M - Mᵀ)) x y'
  rw [← hμ] at hb
  set a := ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y'‖
  have ha : a ^ 2 = (x ⬝ᵥ x) * (y' ⬝ᵥ y') := by
    rw [mul_pow, norm_toLp_sq, norm_toLp_sq]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  change ‖M - μ • (vecMulVec u v - vecMulVec v u)‖ ^ 2
    ≤ ‖M - (vecMulVec x y - vecMulVec y x)‖ ^ 2
  rw [hopt, hZ', norm_sub_skew_sq, dotProduct_mulVec_sub_dotProduct_mulVec, hxy']
  nlinarith [sq_nonneg (a - μ)]

end Lemma1233

end Matrix
