/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter06.Section02
import Numlib.LinearAlgebra.Matrix.LeastSquares.Total
import Numlib.LinearAlgebra.Matrix.Procrustes

/-!
# Low-rank approximation and total least squares

Section 6.3 of [benIsrael2003generalized] minimizes Frobenius error by
truncating an SVD and applies the construction to total least squares.

## Deviations from the source

* **Theorem 4** (correction). A minimizing right singular vector for the
  smallest singular value must have a nonzero last coordinate. If every
  minimizing vector has last coordinate zero, the TLS infimum is not attained.
* **Exercise 34** (correction). The target of the adjoint approximation is $A^H$.
-/

namespace BenIsraelGreville.Chapter06

open Matrix
open scoped Matrix.Norms.Frobenius

/-- **Definition 1** of [benIsrael2003generalized], Chapter 6. A best
rank-$k$ approximation attains the smallest Frobenius error over matrices
of exactly that rank. -/
def IsBestRankApproximation {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (k : ℕ) (X : Matrix m n ℂ) : Prop :=
  X.rank = k ∧ ∀ Y : Matrix m n ℂ, Y.rank = k → ‖A - X‖ ≤ ‖A - Y‖

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 6, Equation (50).
Truncating an SVD at $k$ gives a best rank-$k$ approximation, and the error is
the square root of the sum of squares of the omitted singular values. -/
theorem theorem_6_3 {m n k : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ} {σ : ℕ → ℝ}
    (h : IsSingularValueDecomposition A U σ V) (hk : k ≤ A.rank) :
    let X := svdTruncation U σ V k
    IsBestRankApproximation A k X ∧
      ‖A - X‖ = Real.sqrt (∑ i ∈ Finset.Ico k A.rank, A.sortedSingularValues i ^ 2) := by
  have hErr := frobenius_norm_sub_svdTruncation h.1 k
  have hLeast := isLeast_frobenius_norm_sub_of_rank_le A k
  simp only [Fintype.card_fin] at hLeast
  refine ⟨⟨rank_svdTruncation h.1 hk, ?_⟩, ?_⟩
  · intro Y hY
    exact hErr.trans_le (hLeast.2 ⟨Y, hY.le, rfl⟩)
  · rw [hErr]
    congr 1
    rw [← Finset.sum_Ico_consecutive _ hk (le_min A.rank_le_height A.rank_le_width)]
    have hz : ∑ i ∈ Finset.Ico A.rank (min m n), A.sortedSingularValues i ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [(A.sortedSingularValues_eq_zero_iff_rank_le i).mpr (Finset.mem_Ico.mp hi).1]
    rw [hz, add_zero]

/-- The best rank-$k$ approximation is unique when the last retained
singular value exceeds the first omitted one. -/
theorem bestRankApproximation_unique_of_gap {m n k : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ} {σ : ℕ → ℝ}
    (h : IsSingularValueDecomposition A U σ V) (hk : k ≤ A.rank)
    (hgap : σ k < σ (k - 1)) : ∃! X, IsBestRankApproximation A k X := by
  refine ⟨svdTruncation U σ V k, (theorem_6_3 h hk).1, ?_⟩
  intro Y hY
  have hle := hY.2 _ (rank_svdTruncation h.1 hk)
  apply eq_svdTruncation_of_frobenius_norm_sub_sq_le h.1 hgap hY.1.le
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [frobenius_norm_sub_svdTruncation h.1, Real.sq_sqrt
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hsq
  rw [h.eq_sortedSingularValues]
  exact hsq

private theorem exists_distinct_truncation_of_tied_singularValues
    {m n k : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ} {σ : ℕ → ℝ}
    (h : IsSingularValueDecomposition A U σ V) (hk : 0 < k) (hkr : k < A.rank)
    (htie : σ k = σ (k - 1)) :
    ∃ U' V', IsSingularValueDecomposition A U' σ V' ∧
      svdTruncation U' σ V' k ≠ svdTruncation U σ V k := by
  let a := k - 1
  let b := k
  have hab : a < b := Nat.sub_lt hk one_pos
  have hbm : b < m := hkr.trans_le A.rank_le_height
  have hbn : b < n := hkr.trans_le A.rank_le_width
  let e := Equiv.swap a b
  let eM := Equiv.swap (⟨a, hab.trans hbm⟩ : Fin m) ⟨b, hbm⟩
  let eN := Equiv.swap (⟨a, hab.trans hbn⟩ : Fin n) ⟨b, hbn⟩
  have heM (i : Fin m) : (eM i).val = e i.val := Fin.val_injective.map_swap _ _ _
  have heN (i : Fin n) : (eN i).val = e i.val := Fin.val_injective.map_swap _ _ _
  let U' := U.submatrix id eM
  let V' := V.submatrix id eN
  have hU' : U' ∈ unitaryGroup (Fin m) ℂ :=
    submatrix_equiv_mem_unitaryGroup h.1.mem_unitaryGroup_left (Equiv.refl _) eM
  have hV' : V' ∈ unitaryGroup (Fin n) ℂ :=
    submatrix_equiv_mem_unitaryGroup h.1.mem_unitaryGroup_right (Equiv.refl _) eN
  have hRect (f : ℕ → ℂ) :
      (rectDiagonal f : Matrix (Fin m) (Fin n) ℂ).submatrix eM eN =
        rectDiagonal (fun i => f (e i)) := by
    ext i j
    simp only [submatrix_apply, rectDiagonal_apply, heM, heN, e.injective.eq_iff]
  let D : Matrix (Fin m) (Fin n) ℂ := rectDiagonal (fun i => (σ i : ℂ))
  have hD : D.submatrix eM eN = D := by
    change (rectDiagonal (fun i => (σ i : ℂ)) : Matrix (Fin m) (Fin n) ℂ).submatrix eM eN = _
    rw [hRect]
    apply congrArg rectDiagonal
    funext i
    by_cases ha : i = a
    · subst i
      rw [show e a = b from Equiv.swap_apply_left a b]
      exact congrArg Complex.ofReal htie
    · by_cases hb : i = b
      · subst i
        rw [show e b = a from Equiv.swap_apply_right a b]
        exact congrArg Complex.ofReal htie.symm
      · rw [show e i = i from Equiv.swap_apply_of_ne_of_ne ha hb]
  have hCore : Uᴴ * A * V = D := h.1.star_mul_mul
  have hCore' : U'ᴴ * A * V' = D := by
    change ((U.submatrix (Equiv.refl _) eM)ᴴ * A.submatrix (Equiv.refl _) (Equiv.refl _)) *
      V.submatrix (Equiv.refl _) eN = _
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hCore, hD]
  have h' : IsSingularValueDecomposition A U' σ V' :=
    ⟨⟨⟨hU', hV', hCore'⟩, h.1.antitone, h.1.nonneg⟩, h.2⟩
  refine ⟨U', V', h', ?_⟩
  let f (i : ℕ) : ℂ := if i < k then (σ i : ℂ) else 0
  let Dk : Matrix (Fin m) (Fin n) ℂ := rectDiagonal f
  have hPush : U' * Dk.submatrix eM eN * V'ᴴ = U * Dk * Vᴴ := by
    change (U.submatrix id eM) * Dk.submatrix eM eN * (V.submatrix id eN)ᴴ = _
    rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]
  intro heq
  change U' * Dk * V'ᴴ = U * Dk * Vᴴ at heq
  rw [← hPush] at heq
  have hU'U : U'ᴴ * U' = 1 := conjTranspose_mul_self_of_mem_unitaryGroup hU'
  have hV'V : V'ᴴ * V' = 1 := conjTranspose_mul_self_of_mem_unitaryGroup hV'
  have hSame : Dk = Dk.submatrix eM eN := by
    have he := congrArg (fun X : Matrix (Fin m) (Fin n) ℂ => U'ᴴ * X * V') heq
    simpa only [Matrix.mul_assoc, hV'V, Matrix.mul_one, ← Matrix.mul_assoc U'ᴴ U',
      hU'U, Matrix.one_mul] using he
  have he := congrArg (fun M : Matrix (Fin m) (Fin n) ℂ =>
    M ⟨a, hab.trans hbm⟩ ⟨a, hab.trans hbn⟩) hSame
  change Dk ⟨a, hab.trans hbm⟩ ⟨a, hab.trans hbn⟩ =
    Dk (eM ⟨a, hab.trans hbm⟩) (eN ⟨a, hab.trans hbn⟩) at he
  have hzero : (σ a : ℂ) = 0 := by
    have hak : a < k := hab
    have hbk : ¬ b < k := Nat.lt_irrefl k
    simpa only [Dk, rectDiagonal_apply, Fin.val_mk, heM, heN,
      show e a = b from Equiv.swap_apply_left a b, eq_self, ite_true, f,
      ite_eq_left hak, ite_eq_right hbk] using he
  have hr : A.rank ≤ a := (A.sortedSingularValues_eq_zero_iff_rank_le a).mp
    ((congrFun h.eq_sortedSingularValues a).symm.trans (Complex.ofReal_eq_zero.mp hzero))
  exact (not_lt_of_ge hr) (hab.trans hkr)

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 6, Equation (52).
For positive $k$ at most the rank, the best rank-$k$ approximation is
unique exactly when there is a singular value gap at the truncation. -/
theorem bestRankApproximation_unique_iff_gap {m n k : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ} {σ : ℕ → ℝ}
    (h : IsSingularValueDecomposition A U σ V) (hk : 0 < k) (hkr : k ≤ A.rank) :
    (∃! X, IsBestRankApproximation A k X) ↔ σ k < σ (k - 1) := by
  refine ⟨?_, bestRankApproximation_unique_of_gap h hkr⟩
  rintro ⟨X, -, hX⟩
  by_contra hn
  have htie := le_antisymm (h.1.antitone (Nat.sub_le k 1)) (le_of_not_gt hn)
  have hr : k < A.rank := by
    by_contra! he
    have hz : σ (k - 1) = 0 := htie.symm.trans (h.2 k he)
    rw [h.eq_sortedSingularValues, A.sortedSingularValues_eq_zero_iff_rank_le] at hz
    omega
  obtain ⟨U', V', h', hne⟩ := exists_distinct_truncation_of_tied_singularValues h hk hr htie
  exact hne ((hX _ (theorem_6_3 h' hkr).1).trans (hX _ (theorem_6_3 h hkr).1).symm)

section TotalLeastSquares

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem tlsWeighted_one (A : Matrix m n ℂ) (B : Matrix m Unit ℂ) :
    tlsWeighted (1 : m → ℝ) (1 : n ⊕ Unit → ℝ) A B = fromCols A B := by
  simp [tlsWeighted]

/-- **Theorem 4** of [benIsrael2003generalized], Chapter 6, Equations
(59)–(61), with a smallest-singular-value vector whose last coordinate is
nonzero. Its rank-one correction attains the least Frobenius error. -/
theorem theorem_6_4 (A : Matrix m n ℂ) (b : m → ℂ) (w : n ⊕ Unit → ℂ)
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (n ⊕ Unit))‖ = 1)
    (hmin : ‖(WithLp.toLp 2 (fromCols A (replicateCol Unit b) *ᵥ w) : EuclideanSpace ℂ m)‖ =
      (fromCols A (replicateCol Unit b)).sortedSingularValues (Fintype.card n))
    (hα : w (Sum.inr ()) ≠ 0) :
    let B := replicateCol Unit b
    let C := fromCols A B
    ∃ E R, IsTLSPerturbation 1 1 A B E R ∧
      (A + E) * replicateCol Unit (fun j => -w (Sum.inl j) / w (Sum.inr ())) = B + R ∧
      fromCols E R = -vecMulVec (C *ᵥ w) (star w) ∧
      ‖fromCols E R‖ = C.sortedSingularValues (Fintype.card n) := by
  let B := replicateCol Unit b
  let C := fromCols A B
  have hσ : C.sortedSingularValues (Fintype.card n) = ⨅ j, C.colSingularValues j := by
    rw [← C.sortedSingularValues_eq_iInf_colSingularValues]
    simp
  have hMin : ‖(WithLp.toLp 2 (tlsWeighted (1 : m → ℝ) (1 : n ⊕ Unit → ℝ) A B *ᵥ w) :
      EuclideanSpace ℂ m)‖ = ⨅ j,
        (tlsWeighted (1 : m → ℝ) (1 : n ⊕ Unit → ℝ) A B).colSingularValues j := by
    rw [tlsWeighted_one]
    exact hmin.trans hσ
  obtain ⟨E, R, hp, hx, hER⟩ := isTLSSolution_of_mem_smallest
    (A := A) (b := b) (d := 1) (t := 1) (by simp) (by simp) hw hMin hα
  rw [tlsWeighted_one, tlsWeighted_one] at hER
  refine ⟨E, R, hp, ?_, hER, ?_⟩
  · simpa only [Pi.one_apply, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_one, one_mul]
      using hx
  · rw [hER, norm_neg, frobenius_norm_vecMulVec_star, hw, mul_one]
    exact hmin

/-- If every least-stretch unit vector has zero last coordinate, the
unweighted single-right-hand-side total least-squares problem has no solution. -/
theorem no_totalLeastSquaresSolution_of_minimizers_last_eq_zero
    (A : Matrix m n ℂ) (b : m → ℂ)
    (h : ∀ w : n ⊕ Unit → ℂ,
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (n ⊕ Unit))‖ = 1 →
      ‖(WithLp.toLp 2 (fromCols A (replicateCol Unit b) *ᵥ w) : EuclideanSpace ℂ m)‖ =
        (fromCols A (replicateCol Unit b)).sortedSingularValues (Fintype.card n) →
      w (Sum.inr ()) = 0) :
    ¬ ∃ X, IsTLSSolution 1 1 A (replicateCol Unit b) X := by
  apply not_isTLSSolution_of_forall_last_eq_zero (d := 1) (t := 1) (by simp) (by simp)
  intro w hw hmin
  apply h w hw
  rw [tlsWeighted_one] at hmin
  rw [hmin, ← sortedSingularValues_eq_iInf_colSingularValues]
  simp

/-- **Exercise 36** of [benIsrael2003generalized], Chapter 6.
For an inconsistent system with deficient column rank, adjoining the right
hand side increases rank by one, and the TLS infimum is unattained. -/
theorem exercise_6_36 (A : Matrix m n ℂ) (b : m → ℂ)
    (hA : A.rank < Fintype.card n) (hb : b ∉ LinearMap.range A.mulVecLin) :
    (fromCols A (replicateCol Unit b)).rank = A.rank + 1 ∧
      ¬ ∃ X, IsTLSSolution 1 1 A (replicateCol Unit b) X := by
  let B := replicateCol Unit b
  let C := fromCols A B
  have hcol : Set.range C.col = Set.range A.col ∪ {b} := by
    ext x
    constructor
    · rintro ⟨i | ⟨⟩, rfl⟩
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr rfl
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr (), rfl⟩
  have hrange : LinearMap.range C.mulVecLin =
      LinearMap.range A.mulVecLin ⊔ ℂ ∙ b := by
    rw [range_mulVecLin, hcol, Submodule.span_union, ← range_mulVecLin]
  have hb0 : b ≠ 0 := fun he => hb (he ▸ Submodule.zero_mem _)
  have hr : C.rank = A.rank + 1 := by
    have hi := (Submodule.disjoint_span_singleton_of_notMem (K := ℂ) hb).eq_bot
    have hd := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range A.mulVecLin) (ℂ ∙ b)
    rw [hi, finrank_bot, add_zero, finrank_span_singleton hb0] at hd
    rw [Matrix.rank, hrange, Matrix.rank]
    exact hd
  refine ⟨hr, no_totalLeastSquaresSolution_of_minimizers_last_eq_zero A b ?_⟩
  intro w _ hw
  have hzero : C.sortedSingularValues (Fintype.card n) = 0 :=
    (C.sortedSingularValues_eq_zero_iff_rank_le _).mpr (by omega)
  have hw0 : C *ᵥ w = 0 := by
    exact congrArg WithLp.ofLp (norm_eq_zero.mp (hw.trans hzero))
  by_contra hα
  have hB : B *ᵥ (w ∘ Sum.inr) = w (Sum.inr ()) • b := by
    ext i
    simp [B, mulVec, dotProduct, mul_comm]
  change fromCols A B *ᵥ w = 0 at hw0
  rw [fromCols_mulVec, hB] at hw0
  have hAx : A *ᵥ (w ∘ Sum.inl) = (-w (Sum.inr ())) • b := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hw0
  apply hb
  refine ⟨(-w (Sum.inr ()))⁻¹ • (w ∘ Sum.inl), ?_⟩
  change A *ᵥ ((-w (Sum.inr ()))⁻¹ • (w ∘ Sum.inl)) = b
  rw [mulVec_smul, hAx, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hα), one_smul]

end TotalLeastSquares

section Exercises

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Exercise 26** of [benIsrael2003generalized], Chapter 6, Equation (67).
A perturbation of rank at most $k$ leaves a spectral-norm error at least
the $(k+1)$st singular value. -/
theorem exercise_6_26 {A B : Matrix m n ℂ} {k : ℕ} (hB : B.rank ≤ k) :
    A.sortedSingularValues k ≤ (A - B).sortedSingularValues 0 := by
  open scoped Matrix.Norms.L2Operator in
  rw [sortedSingularValues_zero_eq_l2_opNorm]
  exact sortedSingularValues_le_l2_opNorm_sub_of_rank_le hB

/-- **Exercise 27** of [benIsrael2003generalized], Chapter 6, Equation (68).
Weyl's inequality for the ordered singular values of a sum. -/
theorem exercise_6_27 (A B : Matrix m n ℂ) (i j : ℕ) :
    (A + B).sortedSingularValues (i + j) ≤ A.sortedSingularValues i + B.sortedSingularValues j :=
  sortedSingularValues_add_le A B i j

/-- **Exercise 28** of [benIsrael2003generalized], Chapter 6, Equation (69).
Subtracting a rank-at-most-$k$ matrix shifts the lower singular-value bound by $k$. -/
theorem exercise_6_28 {A B : Matrix m n ℂ} {k : ℕ} (hB : B.rank ≤ k) (i : ℕ) :
    A.sortedSingularValues (i + k) ≤ (A - B).sortedSingularValues i := by
  simpa only [sub_add_cancel, (B.sortedSingularValues_eq_zero_iff_rank_le k).mpr hB, add_zero]
    using exercise_6_27 (A - B) B i k

/-- **Exercise 29** of [benIsrael2003generalized], Chapter 6, Equation (70).
The squared Frobenius error of a rank-at-most-$k$ approximation bounds the
sum of the squares of discarded positive singular values. -/
theorem exercise_6_29 {A B : Matrix m n ℂ} {k : ℕ} (hB : B.rank ≤ k) :
    ∑ i ∈ Finset.Ico k A.rank, A.sortedSingularValues i ^ 2 ≤ ‖A - B‖ ^ 2 := by
  refine le_trans ?_ (sum_sq_sortedSingularValues_le_frobenius_norm_sub_sq_of_rank_le hB)
  have hd : A.rank ≤ min (Fintype.card m) (Fintype.card n) :=
    le_min (rank_le_card_height A) (rank_le_card_width A)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hd)
    (fun _ _ _ => sq_nonneg _)

/-- **Exercise 30**, Equation (71), of [benIsrael2003generalized], Chapter 6.
In Frobenius norm, the smallest positive singular value is the minimum
distance to the matrices of lower rank. -/
theorem exercise_6_30_frobenius (A : Matrix m n ℂ) (hA : 0 < A.rank) :
    IsLeast ((fun B => ‖A - B‖) '' {B | B.rank ≤ A.rank - 1})
      (A.sortedSingularValues (A.rank - 1)) := by
  have h := isLeast_frobenius_norm_sub_of_rank_le A (A.rank - 1)
  have hd : A.rank ≤ min (Fintype.card m) (Fintype.card n) :=
    le_min (rank_le_card_height A) (rank_le_card_width A)
  have hs : ∑ i ∈ Finset.Ico (A.rank - 1) (min (Fintype.card m) (Fintype.card n)),
      A.sortedSingularValues i ^ 2 = A.sortedSingularValues (A.rank - 1) ^ 2 := by
    rw [← Finset.sum_Ico_consecutive _ (Nat.sub_le A.rank 1) hd]
    have hz : ∑ i ∈ Finset.Ico A.rank (min (Fintype.card m) (Fintype.card n)),
        A.sortedSingularValues i ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [(A.sortedSingularValues_eq_zero_iff_rank_le i).mpr (Finset.mem_Ico.mp hi).1]
    have hi : Finset.Ico (A.rank - 1) A.rank = {A.rank - 1} := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [hz, add_zero, hi, Finset.sum_singleton]
  rwa [hs, Real.sqrt_sq (A.sortedSingularValues_nonneg _)] at h

open scoped Matrix.Norms.L2Operator in
/-- **Exercise 30**, Equation (71), of [benIsrael2003generalized], Chapter 6.
The distance to lower rank in spectral norm is also the smallest positive
singular value. -/
theorem exercise_6_30_spectral (A : Matrix m n ℂ) :
    IsLeast ((fun B => ‖A - B‖) '' {B | B.rank ≤ A.rank - 1})
      (A.sortedSingularValues (A.rank - 1)) :=
  isLeast_l2_opNorm_sub_of_rank_le A (A.rank - 1)

/-- **Exercise 30(a)** of [benIsrael2003generalized], Chapter 6.
A perturbation smaller in Frobenius norm than the smallest positive
singular value cannot lower the rank. -/
theorem exercise_6_30a_frobenius (A B : Matrix m n ℂ)
    (hB : ‖B‖ < A.sortedSingularValues (A.rank - 1)) : A.rank ≤ (A + B).rank := by
  by_contra! hr
  have h := (exercise_6_30_frobenius A (Nat.zero_lt_of_lt hr)).2
    ⟨A + B, by change (A + B).rank ≤ A.rank - 1; omega, rfl⟩
  dsimp only at h
  rw [sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg] at h
  exact (not_le_of_gt hB) h

open scoped Matrix.Norms.L2Operator in
/-- **Exercise 30(a)** of [benIsrael2003generalized], Chapter 6.
The same rank protection holds for perturbations measured in spectral norm. -/
theorem exercise_6_30a_spectral (A B : Matrix m n ℂ)
    (hB : ‖B‖ < A.sortedSingularValues (A.rank - 1)) : A.rank ≤ (A + B).rank := by
  by_contra! hr
  have h := (exercise_6_30_spectral A).2
    ⟨A + B, by change (A + B).rank ≤ A.rank - 1; omega, rfl⟩
  dsimp only at h
  rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← sortedSingularValues_zero_eq_l2_opNorm,
    show -B = (-1 : ℂ) • B by simp, sortedSingularValues_smul, norm_neg, norm_one, one_mul,
    sortedSingularValues_zero_eq_l2_opNorm] at h
  exact (not_le_of_gt hB) h

omit [Fintype m] [DecidableEq n] in
/-- **Exercise 30(b)** of [benIsrael2003generalized], Chapter 6.
The matrices of rank at most $k$ form a closed set. -/
theorem exercise_6_30b [Finite m] (k : ℕ) : IsClosed {A : Matrix m n ℂ | A.rank ≤ k} := by
  have he : {A : Matrix m n ℂ | A.rank ≤ k} =
      ⋂ q : ℕ, ⋂ (_ : k < q), ⋂ r : Fin q → m, ⋂ c : Fin q → n,
        {A | (A.submatrix r c).det = 0} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h q hq r c
      by_contra hd
      exact (not_le_of_gt hq) ((A.card_le_rank_of_det_submatrix_ne_zero hd).trans h)
    · intro h
      by_contra! hk
      obtain ⟨r, c, hd⟩ := A.exists_det_submatrix_ne_zero
      exact hd (h _ hk r c)
  rw [he]
  refine isClosed_iInter fun q => isClosed_iInter fun _ =>
    isClosed_iInter fun r => isClosed_iInter fun c => ?_
  exact isClosed_eq (continuous_id.matrix_submatrix r c).matrix_det continuous_const

/-- **Exercise 31** of [benIsrael2003generalized], Chapter 6.
The first truncation whose discarded Frobenius norm meets the tolerance
has minimal rank among all approximations meeting that tolerance. -/
theorem exercise_6_31 {p q : ℕ} {A : Matrix (Fin p) (Fin q) ℂ}
    {U : Matrix (Fin p) (Fin p) ℂ} {V : Matrix (Fin q) (Fin q) ℂ} {σ : ℕ → ℝ}
    (h : IsSingularValueDecomposition A U σ V) {ε : ℝ} (hε : 0 ≤ ε) :
    let tail := fun k => Real.sqrt (∑ i ∈ Finset.Ico k A.rank, A.sortedSingularValues i ^ 2)
    ∃ k ≤ A.rank, tail k ≤ ε ∧ (∀ j < k, ε < tail j) ∧
      (svdTruncation U σ V k).rank = k ∧ ‖A - svdTruncation U σ V k‖ ≤ ε ∧
      ∀ B : Matrix (Fin p) (Fin q) ℂ, ‖A - B‖ ≤ ε → k ≤ B.rank := by
  let tail := fun k => Real.sqrt (∑ i ∈ Finset.Ico k A.rank, A.sortedSingularValues i ^ 2)
  have hr : tail A.rank ≤ ε := by simpa [tail] using hε
  have he : ∃ k, tail k ≤ ε := ⟨A.rank, hr⟩
  let k := Nat.find he
  have hk : k ≤ A.rank := Nat.find_min' he hr
  have htail : tail k ≤ ε := Nat.find_spec he
  have hmin : ∀ j < k, ε < tail j := fun j hj => lt_of_not_ge (Nat.find_min he hj)
  have hX := theorem_6_3 h hk
  refine ⟨k, hk, htail, hmin, hX.1.1, hX.2.trans_le htail, ?_⟩
  intro B hB
  by_contra! hBr
  have hle := Real.sqrt_le_sqrt (exercise_6_29 (A := A) (B := B) (le_refl B.rank))
  rw [Real.sqrt_sq (norm_nonneg _)] at hle
  exact (not_le_of_gt (hmin B.rank hBr)) (hle.trans hB)

/-- **Exercise 33** of [benIsrael2003generalized], Chapter 6.
The unitary product from an SVD of $B^H A$ minimizes the Frobenius
distance from $A$ to $BW$. -/
theorem exercise_6_33 {p : ℕ} {A B : Matrix m (Fin p) ℂ}
    {U V : Matrix (Fin p) (Fin p) ℂ} {σ : ℕ → ℝ}
    (h : IsSingularValueDecomposition (Bᴴ * A) U σ V) :
    U * Vᴴ ∈ unitaryGroup (Fin p) ℂ ∧
      ∀ W ∈ unitaryGroup (Fin p) ℂ, ‖A - B * (U * Vᴴ)‖ ≤ ‖A - B * W‖ :=
  frobenius_norm_sub_mul_le_of_isSVD h.1

/-- **Exercise 32** of [benIsrael2003generalized], Chapter 6.
An SVD gives a nearest unitary matrix and reduces its error to the
Frobenius norm of the diagonal minus the identity. -/
theorem exercise_6_32 {p : ℕ} {A U V : Matrix (Fin p) (Fin p) ℂ} {σ : ℕ → ℝ}
    (h : IsSingularValueDecomposition A U σ V) :
    let D : Matrix (Fin p) (Fin p) ℂ := diagonal (fun i => (σ i : ℂ))
    (U * Vᴴ ∈ unitaryGroup (Fin p) ℂ) ∧
      ‖A - U * Vᴴ‖ = ‖D - 1‖ ∧
      ∀ W ∈ unitaryGroup (Fin p) ℂ, ‖D - 1‖ ≤ ‖A - W‖ := by
  let D : Matrix (Fin p) (Fin p) ℂ := diagonal (fun i => (σ i : ℂ))
  have hD : (rectDiagonal (fun i => (σ i : ℂ)) : Matrix (Fin p) (Fin p) ℂ) = D := by
    ext i j
    simp only [D, rectDiagonal_apply, diagonal_apply, Fin.val_inj]
  have hA : A = U * D * Vᴴ := by
    have hA : A = U * (rectDiagonal (fun i => (σ i : ℂ)) : Matrix (Fin p) (Fin p) ℂ) * Vᴴ :=
      h.1.eq_mul_mul_star
    rwa [hD] at hA
  have hErr : ‖A - U * Vᴴ‖ = ‖D - 1‖ := by
    have hSub : A - U * Vᴴ = U * (D - 1) * Vᴴ := by
      rw [hA, mul_sub, mul_one, sub_mul]
    rw [hSub,
      frobenius_norm_unitary_mul_mul_unitary h.1.mem_unitaryGroup_left _
        (conjTranspose_mem_unitaryGroup h.1.mem_unitaryGroup_right)]
  have hu := exercise_6_33 (A := A) (B := 1) (by simpa only [conjTranspose_one, one_mul] using h)
  refine ⟨hu.1, hErr, ?_⟩
  intro W hW
  change ‖D - 1‖ ≤ _
  rw [← hErr]
  simpa only [one_mul] using hu.2 W hW

/-- **Exercise 32**, error formula, of [benIsrael2003generalized], Chapter 6.
The zeros on the singular-value diagonal each contribute one to the
squared error of the nearest unitary matrix. -/
theorem exercise_6_32_error {p : ℕ} {A U V : Matrix (Fin p) (Fin p) ℂ} {σ : ℕ → ℝ}
    (h : IsSingularValueDecomposition A U σ V) :
    ‖A - U * Vᴴ‖ =
      Real.sqrt ((∑ i ∈ Finset.range A.rank, (1 - σ i) ^ 2) + (p - A.rank : ℕ)) := by
  have hErr := (exercise_6_32 h).2.1
  change ‖A - U * Vᴴ‖ = ‖diagonal (fun i : Fin p => (σ i : ℂ)) - 1‖ at hErr
  rw [hErr, ← diagonal_one, diagonal_sub, frobenius_norm_diagonal, EuclideanSpace.norm_eq]
  congr 1
  change (∑ i : Fin p, ‖(σ i : ℂ) - 1‖ ^ 2) = _
  have hnorm (i : Fin p) : ‖(σ i : ℂ) - 1‖ ^ 2 = (1 - σ i) ^ 2 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, sub_sq_comm]
  simp only [hnorm]
  have hTail :
    (∑ i ∈ Finset.Ico A.rank p, (1 - σ i) ^ 2) =
      ((p - A.rank : ℕ) : ℝ) := by
    calc
      (∑ i ∈ Finset.Ico A.rank p, (1 - σ i) ^ 2) =
          ∑ _i ∈ Finset.Ico A.rank p, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [h.2 i (Finset.mem_Ico.mp hi).1, sub_zero, one_pow]
      _ = (p - A.rank : ℕ) := by simp
  calc
    (∑ i : Fin p, (1 - σ i) ^ 2) = ∑ i ∈ Finset.range p, (1 - σ i) ^ 2 :=
      Fin.sum_univ_eq_sum_range (fun i => (1 - σ i) ^ 2) p
    _ = _ := by
      rw [← Finset.sum_range_add_sum_Ico _ A.rank_le_width, hTail]

/-- **Exercise 35** of [benIsrael2003generalized], Chapter 6.
A real matrix admits real orthogonal singular-vector factors. -/
theorem exercise_6_35 {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    ∃ U V, IsSVD A U A.sortedSingularValues V := by
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  exact ⟨U, V, ⟨⟨hU, hV, h⟩, A.sortedSingularValues_antitone,
    A.sortedSingularValues_nonneg⟩⟩

end Exercises

/-- **Equations (53)–(58)** of [benIsrael2003generalized], Chapter 6.
The perturbed system is consistent exactly when the augmented kernel
has a vector whose last coordinate is $-1$. -/
theorem tlsFeasibleAugmented_iff {𝕜 m n : Type*} [Field 𝕜] [Fintype n]
    (A : Matrix m n 𝕜) (b : m → 𝕜) :
    (∃ x : n → 𝕜, A *ᵥ x = b) ↔
      ∃ w : n ⊕ Unit → 𝕜, w (Sum.inr ()) = -1 ∧
        fromCols A (replicateCol Unit b) *ᵥ w = 0 := by
  have hform (w : n ⊕ Unit → 𝕜) (hw : w (Sum.inr ()) = -1) :
      fromCols A (replicateCol Unit b) *ᵥ w = A *ᵥ (w ∘ Sum.inl) - b := by
    rw [fromCols_mulVec]
    funext i
    simp [mulVec, dotProduct, hw, sub_eq_add_neg]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨Sum.elim x (fun _ => -1), rfl, by rw [hform _ rfl]; exact sub_eq_zero.mpr hx⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨w ∘ Sum.inl, sub_eq_zero.mp ((hform w hw).symm.trans h)⟩

/-- **Equation (62)** of [benIsrael2003generalized], Chapter 6.
An orthonormal right singular basis has a vector with a nonzero last
coordinate. No restriction on the augmented right-hand side is needed. -/
theorem tls_nonzeroLastIndices_nonempty {𝕜 n : Type*} [RCLike 𝕜]
    [Fintype n] [DecidableEq n] {V : Matrix (n ⊕ Unit) (n ⊕ Unit) 𝕜}
    (hV : V ∈ unitaryGroup (n ⊕ Unit) 𝕜) :
    Set.Nonempty {j | V (Sum.inr ()) j ≠ 0} := by
  classical
  by_contra h
  have hz (j : n ⊕ Unit) : V (Sum.inr ()) j = 0 := by
    by_contra hj
    exact h ⟨j, hj⟩
  have hV' := mul_conjTranspose_self_of_mem_unitaryGroup hV
  have hLast := congrArg (fun W : Matrix (n ⊕ Unit) (n ⊕ Unit) 𝕜 =>
    W (Sum.inr ()) (Sum.inr ())) hV'
  simp [Matrix.mul_apply, hz] at hLast

/-- **Equations (63)–(66)** of [benIsrael2003generalized], Chapter 6.
In the singular coordinates of the augmented matrix, the squared error
of a perturbation with columns in its range is a weighted sum of squares.
The augmented kernel condition becomes a fixed-point equation for the
right singular coordinates scaled by the singular values. -/
theorem tlsAugmentedError_svd_coordinates {𝕜 m q : Type*} [RCLike 𝕜]
    [Fintype m] [Fintype q] [DecidableEq q]
    {U : Matrix m q 𝕜} {V : Matrix q q 𝕜}
    (hU : Uᴴ * U = 1) (hV : V ∈ unitaryGroup q 𝕜) (σ : q → ℝ)
    (Y : Matrix q q 𝕜) (z : q → 𝕜) :
    let D : Matrix q q 𝕜 := diagonal (fun j => (σ j : 𝕜))
    let C := U * D * Vᴴ
    let C' := C - U * Y * D * Vᴴ
    ‖C' - C‖ ^ 2 = ∑ i : q, ∑ j : q, σ j ^ 2 * ‖Y i j‖ ^ 2 ∧
      (C' *ᵥ (V *ᵥ z) = 0 ↔ Y *ᵥ (D *ᵥ z) = D *ᵥ z) := by
  let D : Matrix q q 𝕜 := diagonal (fun j => (σ j : 𝕜))
  let C := U * D * Vᴴ
  let C' := C - U * Y * D * Vᴴ
  change ‖C' - C‖ ^ 2 = _ ∧ _
  have hstar := conjTranspose_mul_self_of_mem_unitaryGroup hV
  constructor
  · have he : C' - C = -(U * (Y * D * Vᴴ)) := by
      simp only [C', sub_sub_cancel_left, Matrix.mul_assoc]
    rw [he, norm_neg, frobenius_norm_mul_of_conjTranspose_mul_self_eq_one hU,
      show ‖Y * D * Vᴴ‖ = ‖Y * D‖ from
        by simpa only [Matrix.one_mul, star_eq_conjTranspose] using
          (frobenius_norm_unitary_mul_mul_unitary (A := Y * D) (one_mem _) (Unitary.star_mem hV)),
      frobenius_norm_sq_eq_sum_sq]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change ‖(Y * diagonal (fun k => (σ k : 𝕜))) i j‖ ^ 2 = _
    rw [mul_diagonal, norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs, mul_comm]
  · have he : C' *ᵥ (V *ᵥ z) = U *ᵥ (D *ᵥ z - Y *ᵥ (D *ᵥ z)) := by
      simp only [C', C, sub_mulVec, ← mulVec_mulVec, mulVec_sub]
      simp only [mulVec_mulVec, hstar, Matrix.mul_one]
    rw [he]
    constructor
    · intro hz
      have h := congrArg (Uᴴ *ᵥ ·) hz
      rw [mulVec_mulVec, hU, one_mulVec, mulVec_zero] at h
      exact (sub_eq_zero.mp h).symm
    · intro hz
      rw [hz, sub_self, mulVec_zero]

open scoped ComplexOrder

private theorem gram_of_singular_factors {m n : ℕ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ unitaryGroup (Fin m) ℂ) (σ : ℕ → ℝ)
    (hσ : ∀ j, m ≤ j → σ j = 0) :
    let D : Matrix (Fin m) (Fin n) ℂ := rectDiagonal (fun j => (σ j : ℂ))
    let X := U * D * Vᴴ
    Xᴴ * X = V * (rectDiagonal (fun j => ((σ j ^ 2 : ℝ) : ℂ)) :
      Matrix (Fin n) (Fin n) ℂ) * Vᴴ := by
  let D : Matrix (Fin m) (Fin n) ℂ := rectDiagonal (fun j => (σ j : ℂ))
  change (U * D * Vᴴ)ᴴ * (U * D * Vᴴ) = _
  have hcore : Dᴴ * D = (rectDiagonal (fun j => ((σ j ^ 2 : ℝ) : ℂ)) :
      Matrix (Fin n) (Fin n) ℂ) := by
    dsimp only [D]
    rw [conjTranspose_rectDiagonal_mul_self, rectDiagonal_eq_diagonal]
    apply congrArg diagonal
    funext j
    by_cases hj : j.val < m
    · simp [hj, sq]
    · simp [hj, hσ j (Nat.le_of_not_gt hj)]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, ← hcore]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U,
    conjTranspose_mul_self_of_mem_unitaryGroup hU, Matrix.one_mul]

private theorem gram_has_bestRankApproximation {m n k : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ} {σ : ℕ → ℝ}
    (h : IsSingularValueDecomposition A U σ V) (hk : k ≤ A.rank) :
    IsBestRankApproximation (Aᴴ * A) k
      ((svdTruncation U σ V k)ᴴ * svdTruncation U σ V k) := by
  let τ : ℕ → ℝ := fun j => σ j ^ 2
  let φ : ℕ → ℝ := fun j => if j < k then σ j else 0
  have hτ : Antitone τ := fun _ _ hj =>
    pow_le_pow_left₀ (h.1.nonneg _) (h.1.antitone hj) _
  have hgram : Aᴴ * A = V * (rectDiagonal (fun j => (τ j : ℂ)) :
      Matrix (Fin n) (Fin n) ℂ) * Vᴴ := by
    rw [h.1.eq_mul_mul_star]
    exact gram_of_singular_factors h.1.mem_unitaryGroup_left σ
      (fun j hj => h.2 j (A.rank_le_height.trans hj))
  have hX : svdTruncation U σ V k = U *
      (rectDiagonal (fun j => (φ j : ℂ)) : Matrix (Fin m) (Fin n) ℂ) * Vᴴ := by
    change U * (rectDiagonal (fun j => if j < k then (σ j : ℂ) else 0) :
      Matrix (Fin m) (Fin n) ℂ) * Vᴴ = _
    have hd : (rectDiagonal (fun j => if j < k then (σ j : ℂ) else 0) :
        Matrix (Fin m) (Fin n) ℂ) = rectDiagonal (fun j => (φ j : ℂ)) := by
      apply congrArg rectDiagonal
      funext j
      by_cases hj : j < k <;> simp [φ, hj]
    rw [hd]
  have hgramX : (svdTruncation U σ V k)ᴴ * svdTruncation U σ V k =
      svdTruncation V τ V k := by
    rw [hX, gram_of_singular_factors h.1.mem_unitaryGroup_left φ
      (fun j hj => by simp [φ, not_lt_of_ge (hk.trans (A.rank_le_height.trans hj))])]
    change _ = V * (rectDiagonal (fun j => if j < k then (τ j : ℂ) else 0) :
      Matrix (Fin n) (Fin n) ℂ) * Vᴴ
    have hd : (rectDiagonal (fun j => ((φ j ^ 2 : ℝ) : ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) = rectDiagonal (fun j => if j < k then (τ j : ℂ) else 0) := by
      apply congrArg rectDiagonal
      funext j
      by_cases hj : j < k <;> simp [φ, τ, hj]
    rw [hd]
  have hGS : (Aᴴ * A).IsSVD V τ V := by
    refine ⟨⟨h.1.mem_unitaryGroup_right, h.1.mem_unitaryGroup_right, ?_⟩, hτ,
      fun j => sq_nonneg (σ j)⟩
    have hV := conjTranspose_mul_self_of_mem_unitaryGroup h.1.mem_unitaryGroup_right
    change Vᴴ * (Aᴴ * A) * V = _
    rw [hgram]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.mul_one, Matrix.one_mul]
    rfl
  have hp : A.rank = (Aᴴ * A).rank := (rank_conjTranspose_mul_self A).symm
  have hG : IsSingularValueDecomposition (Aᴴ * A) V τ V :=
    ⟨hGS, fun j hj => by simp [τ, h.2 j (hp ▸ hj)]⟩
  rw [hgramX]
  exact (theorem_6_3 hG (hk.trans_eq hp)).1

/-- **Exercise 34**, the adjoint and two Gram approximations, of
[benIsrael2003generalized], Chapter 6. The adjoint of the source matrix
is the first comparison target. -/
theorem exercise_6_34 {m n k : ℕ} {A : Matrix (Fin m) (Fin n) ℂ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ} {σ : ℕ → ℝ}
    (h : IsSingularValueDecomposition A U σ V) (hk : k ≤ A.rank) :
    let X := svdTruncation U σ V k
    IsBestRankApproximation Aᴴ k Xᴴ ∧
      IsBestRankApproximation (A * Aᴴ) k (X * Xᴴ) ∧
      IsBestRankApproximation (Aᴴ * A) k (Xᴴ * X) := by
  have hstar : IsSingularValueDecomposition Aᴴ V σ U :=
    ⟨h.1.conjTranspose, by simpa only [rank_conjTranspose] using h.2⟩
  have hk' : k ≤ Aᴴ.rank := by simpa only [rank_conjTranspose] using hk
  have hX : (svdTruncation U σ V k)ᴴ = svdTruncation V σ U k := by
    rw [svdTruncation, conjTranspose_mul, conjTranspose_mul, rectDiagonal_conjTranspose]
    simp only [star_eq_conjTranspose, conjTranspose_conjTranspose, svdTruncation, Matrix.mul_assoc]
    change V * ((rectDiagonal (star ∘ fun j => if j < k then (σ j : ℂ) else 0) :
      Matrix (Fin n) (Fin m) ℂ) * Uᴴ) =
      V * ((rectDiagonal (fun j => if j < k then (σ j : ℂ) else 0) :
        Matrix (Fin n) (Fin m) ℂ) * Uᴴ)
    have hd : (rectDiagonal (star ∘ fun j => if j < k then (σ j : ℂ) else 0) :
        Matrix (Fin n) (Fin m) ℂ) = rectDiagonal (fun j => if j < k then (σ j : ℂ) else 0) := by
      apply congrArg rectDiagonal
      funext j
      by_cases hj : j < k <;> simp [hj]
    rw [hd]
  refine ⟨by rw [hX]; exact (theorem_6_3 hstar hk').1, ?_, gram_has_bestRankApproximation h hk⟩
  have h' := gram_has_bestRankApproximation hstar hk'
  rw [← hX, conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h'
  exact h'

/-- **Exercise 34**, the normal powers, of [benIsrael2003generalized], Chapter 6.
For an eigenbasis-aligned truncation of a normal matrix, every positive
integer power is a best rank-$k$ approximation to the corresponding power. -/
theorem exercise_6_34_normal_pow {n k p : ℕ} {A U : Matrix (Fin n) (Fin n) ℂ}
    {d : ℕ → ℂ} (h : IsUDVDecomposition A U d U) (hk : k ≤ A.rank) (hp : 0 < p) :
    let X := U * diagonal (fun i : Fin n => if i.val < k then d i else 0) * Uᴴ
    IsBestRankApproximation (A ^ p) k (X ^ p) := by
  let S : unitary (Matrix (Fin n) (Fin n) ℂ) := ⟨U, h.1⟩
  let e := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) S
  let t : ℕ → ℂ := fun i => d i ^ p
  let σ : ℕ → ℝ := fun i => ‖t i‖
  let f : Fin n → ℂ := fun i => if t i = 0 then 1 else t i / (‖t i‖ : ℂ)
  let V := U * (diagonal f)ᴴ
  let X := U * diagonal (fun i : Fin n => if i.val < k then d i else 0) * Uᴴ
  have hA : A ^ p = U * diagonal (fun i : Fin n => t i) * Uᴴ := by
    have he : A = e (diagonal (fun i : Fin n => d i)) := by
      simpa only [e, Unitary.conjStarAlgAut_apply, S, star_eq_conjTranspose,
        rectDiagonal_eq_diagonal] using h.2.2.1
    rw [he, ← map_pow, diagonal_pow]
    rfl
  have hX : X ^ p = U * diagonal (fun i : Fin n => if i.val < k then t i else 0) * Uᴴ := by
    have he : X = e (diagonal (fun i : Fin n => if i.val < k then d i else 0)) := rfl
    rw [he, ← map_pow, diagonal_pow]
    have hf : ((fun i : Fin n => if i.val < k then d i else 0) ^ p) =
        (fun i : Fin n => if i.val < k then t i else 0) := by
      funext i
      by_cases hi : i.val < k <;> simp [hi, t, hp.ne']
    rw [hf]
    rfl
  have hnorm (i : Fin n) : ‖f i‖ = 1 := by
    by_cases hi : t i = 0
    · simp [f, hi]
    · simp [f, hi, (norm_pos_iff.mpr hi).ne']
  have hfU : diagonal f ∈ unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    apply congrArg diagonal
    funext i
    change starRingEnd ℂ (f i) * f i = 1
    rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm, hnorm, one_pow, Complex.ofReal_one]
  have hV : V ∈ unitaryGroup (Fin n) ℂ := mul_mem h.1 (Unitary.star_mem hfU)
  have hphase (i : Fin n) : t i * star (f i) = (σ i : ℂ) := by
    by_cases hi : t i = 0
    · simp [hi, σ]
    · have hpos : (‖t i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hi).ne'
      change t i * starRingEnd ℂ (f i) = _
      rw [show f i = t i / (‖t i‖ : ℂ) by simp [f, hi], map_div₀, Complex.conj_ofReal,
        ← mul_div_assoc, Complex.mul_conj, ← Complex.sq_norm, Complex.ofReal_pow, sq,
        mul_div_cancel_right₀ _ hpos]
  have hphase' (i : Fin n) : (σ i : ℂ) * f i = t i := by
    by_cases hi : t i = 0
    · simp [hi, σ]
    · have hpos : (‖t i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hi).ne'
      rw [show f i = t i / (‖t i‖ : ℂ) by simp [f, hi], mul_comm]
      exact div_mul_cancel₀ (t i) hpos
  have hU := conjTranspose_mul_self_of_mem_unitaryGroup h.1
  have hsort : Antitone σ := by
    intro i j hij
    simp only [σ, t, norm_pow, h.2.2.2]
    exact pow_le_pow_left₀ (A.sortedSingularValues_nonneg _) (A.sortedSingularValues_antitone hij) p
  have hS : (A ^ p).IsSVD U σ V := by
    refine ⟨⟨h.1, hV, ?_⟩, hsort, fun j => norm_nonneg _⟩
    change Uᴴ * A ^ p * (U * (diagonal f)ᴴ) = _
    rw [hA]
    have he : diagonal (fun i : Fin n => t i) * (diagonal f)ᴴ =
        diagonal (fun i : Fin n => (σ i : ℂ)) := by
      rw [diagonal_conjTranspose, diagonal_mul_diagonal]
      exact congrArg diagonal (funext hphase)
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]
    rw [he, rectDiagonal_eq_diagonal]
    rfl
  have hSfull : IsSingularValueDecomposition (A ^ p) U σ V := by
    refine ⟨hS, fun j hj => ?_⟩
    by_cases hn : j < n
    · rw [hS.singularValues_eq hn hn]
      exact ((A ^ p).sortedSingularValues_eq_zero_iff_rank_le _).mpr hj
    · have hz := (A.sortedSingularValues_eq_zero_iff_rank_le j).mpr
        (A.rank_le_width.trans (Nat.le_of_not_gt hn))
      simp [σ, t, norm_pow, h.2.2.2 j, hz, hp.ne']
  have hr : k ≤ (A ^ p).rank := by
    by_contra! hc
    have hn : (A ^ p).rank < n := hc.trans_le (hk.trans A.rank_le_width)
    have hz := hSfull.2 (A ^ p).rank le_rfl
    have hσnz : A.sortedSingularValues (A ^ p).rank ≠ 0 := fun he =>
      (not_le_of_gt (hc.trans_le hk)) ((A.sortedSingularValues_eq_zero_iff_rank_le _).mp he)
    exact (pow_ne_zero p hσnz) (by
      simpa only [σ, t, norm_pow, h.2.2.2] using hz)
  have hTruncation : svdTruncation U σ V k = X ^ p := by
    rw [hX]
    change U * (rectDiagonal (fun j => if j < k then (σ j : ℂ) else 0) :
      Matrix (Fin n) (Fin n) ℂ) * (U * (diagonal f)ᴴ)ᴴ = _
    rw [rectDiagonal_eq_diagonal, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      Matrix.mul_assoc U _ (diagonal f), diagonal_mul_diagonal]
    have he : (fun i : Fin n => (if i.val < k then (σ i : ℂ) else 0) * f i) =
        (fun i : Fin n => if i.val < k then t i else 0) := by
      funext i
      by_cases hi : i.val < k <;> simp [hi, hphase']
    rw [he]
  change IsBestRankApproximation (A ^ p) k (X ^ p)
  rw [← hTruncation]
  exact (theorem_6_3 hSfull hr).1

/-- **Theorem 4**, uniqueness with a spectral gap, of
[benIsrael2003generalized], Chapter 6. An admissible least-stretch vector
gives existence. A gap at the smallest singular value makes the optimal
perturbation unique. -/
theorem theorem_6_4_unique_of_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (b : Fin m → ℂ) (w : Fin n ⊕ Unit → ℂ)
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n ⊕ Unit))‖ = 1)
    (hmin : ‖(WithLp.toLp 2 (fromCols A (replicateCol Unit b) *ᵥ w) :
      EuclideanSpace ℂ (Fin m))‖ = (fromCols A (replicateCol Unit b)).sortedSingularValues n)
    (hα : w (Sum.inr ()) ≠ 0)
    (hfull : (fromCols A (replicateCol Unit b)).rank = n + 1)
    (hgap : (fromCols A (replicateCol Unit b)).sortedSingularValues n <
      (fromCols A (replicateCol Unit b)).sortedSingularValues (n - 1)) :
    ∃! ER : Matrix (Fin m) (Fin n) ℂ × Matrix (Fin m) Unit ℂ,
      IsTLSPerturbation 1 1 A (replicateCol Unit b) ER.1 ER.2 := by
  let B := replicateCol Unit b
  let C := fromCols A B
  let e : Fin (n + 1) ≃ Fin n ⊕ Unit := Fintype.equivOfCardEq (by simp)
  let D := C.submatrix (Equiv.refl _) e
  let approx (E : Matrix (Fin m) (Fin n) ℂ) (R : Matrix (Fin m) Unit ℂ) :=
    (fromCols (A + E) (B + R)).submatrix (Equiv.refl _) e
  have hσ : D.sortedSingularValues = C.sortedSingularValues :=
    sortedSingularValues_submatrix_equiv C (Equiv.refl _) e
  have hnm : n + 1 ≤ m := by
    rw [← hfull]
    simpa only [Fintype.card_fin] using C.rank_le_card_height
  obtain ⟨E, R, hER, _, _, herror⟩ := theorem_6_4 A b w hw (by simpa using hmin) hα
  obtain ⟨U, hU, V, hV, hD⟩ := D.exists_svd
  let σ := D.sortedSingularValues
  have hs : D.IsSVD U σ V :=
    ⟨⟨hU, hV, hD⟩, D.sortedSingularValues_antitone, D.sortedSingularValues_nonneg⟩
  have hApprox (E' : Matrix (Fin m) (Fin n) ℂ) (R' : Matrix (Fin m) Unit ℂ)
      (hP : IsTLSPerturbation 1 1 A B E' R') : approx E' R' = svdTruncation U σ V n := by
    obtain ⟨X, hX⟩ := exists_mul_eq_of_range_mulVecLin_le hP.range_le
    have hprod : fromCols (A + E') (B + R') = (A + E') * fromCols 1 X := by
      rw [mul_fromCols, Matrix.mul_one, hX]
    have hRank : (approx E' R').rank ≤ n := by
      rw [show (approx E' R').rank = (fromCols (A + E') (B + R')).rank from
        rank_submatrix _ (Equiv.refl _) e, hprod]
      exact (rank_mul_le_left _ _).trans ((A + E').rank_le_width)
    have hn' := hP.norm_le E R hER.range_le
    rw [tlsWeighted_one, tlsWeighted_one, herror] at hn'
    have hdiff : D - approx E' R' = (-(fromCols E' R')).submatrix (Equiv.refl _) e := by
      ext i j
      change C i (e j) - fromCols (A + E') (B + R') i (e j) = -(fromCols E' R' i (e j))
      rcases e j with j | j <;> simp [C]
    apply eq_svdTruncation_of_frobenius_norm_sub_sq_le hs
      (by simpa only [σ, hσ] using hgap) hRank
    rw [hdiff, frobenius_norm_submatrix_equiv, norm_neg,
      min_eq_right hnm, Nat.Ico_succ_singleton, Finset.sum_singleton, show σ n = C.sortedSingularValues n from congrFun hσ n]
    simpa only [Fintype.card_fin] using pow_le_pow_left₀ (norm_nonneg _) hn' 2
  refine ⟨(E, R), hER, ?_⟩
  rintro ⟨E', R'⟩ hP
  have heq := (hApprox E' R' hP).trans (hApprox E R hER).symm
  have heq' : fromCols (A + E') (B + R') = fromCols (A + E) (B + R) := by
    ext i j
    have he := congrArg (fun M : Matrix (Fin m) (Fin (n + 1)) ℂ => M i (e.symm j)) heq
    simpa only [approx, submatrix_apply, Equiv.refl_apply, Equiv.apply_symm_apply] using he
  apply Prod.ext
  · exact add_left_cancel (congrArg (fun M => toCols₁ M) heq')
  · exact add_left_cancel (congrArg (fun M => toCols₂ M) heq')

open scoped InnerProductSpace in
private theorem least_stretch_iff_vanishes_above {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n]
    (C : Matrix m n ℂ) (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, c ≤ C.colSingularValues i)
    (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin C x‖ = c * ‖x‖ ↔
      ∀ i, c < C.colSingularValues i → inner ℂ (C.rightSingularBasis i) x = 0 := by
  have hsum :
      (∑ i, (C.colSingularValues i ^ 2 - c ^ 2) *
        ‖inner ℂ (C.rightSingularBasis i) x‖ ^ 2) = ‖toEuclideanLin C x‖ ^ 2 - (c * ‖x‖) ^ 2 := by
    simp only [sub_mul, Finset.sum_sub_distrib, C.norm_sq_toEuclideanLin_apply,
      mul_pow, ← Finset.mul_sum, C.sum_norm_inner_rightSingularBasis_sq]
  have hnn (i : n) : 0 ≤ (C.colSingularValues i ^ 2 - c ^ 2) *
      ‖inner ℂ (C.rightSingularBasis i) x‖ ^ 2 :=
    mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hc (hmin i) 2)) (sq_nonneg _)
  constructor
  · intro h i hi
    have hs := hsum.trans (by rw [h, sub_self])
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp hs i (Finset.mem_univ i)
    have hp : 0 < C.colSingularValues i ^ 2 - c ^ 2 :=
      sub_pos.mpr (pow_lt_pow_left₀ hi hc (by decide))
    have hn := (mul_eq_zero.mp hz).resolve_left hp.ne'
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  · intro h
    have hz : (∑ i, (C.colSingularValues i ^ 2 - c ^ 2) *
        ‖inner ℂ (C.rightSingularBasis i) x‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases (hmin i).eq_or_lt with h' | h'
      · simp [h']
      · simp [h i h']
    apply (pow_left_inj₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).mp
    exact sub_eq_zero.mp (hsum.symm.trans hz)

open scoped InnerProductSpace in
private theorem tls_not_unique_of_tie {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (b : Fin m → ℂ) (w : Fin n ⊕ Unit → ℂ)
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n ⊕ Unit))‖ = 1)
    (hmin : ‖(WithLp.toLp 2 (fromCols A (replicateCol Unit b) *ᵥ w) :
      EuclideanSpace ℂ (Fin m))‖ = (fromCols A (replicateCol Unit b)).sortedSingularValues n)
    (hα : w (Sum.inr ()) ≠ 0) (hn : 0 < n)
    (hfull : (fromCols A (replicateCol Unit b)).rank = n + 1)
    (htie : (fromCols A (replicateCol Unit b)).sortedSingularValues n =
      (fromCols A (replicateCol Unit b)).sortedSingularValues (n - 1)) :
    ¬ ∃! ER : Matrix (Fin m) (Fin n) ℂ × Matrix (Fin m) Unit ℂ,
      IsTLSPerturbation 1 1 A (replicateCol Unit b) ER.1 ER.2 := by
  let B := replicateCol Unit b
  let C := fromCols A B
  let c := C.sortedSingularValues n
  let x : EuclideanSpace ℂ (Fin n ⊕ Unit) := WithLp.toLp 2 w
  let last : EuclideanSpace ℂ (Fin n ⊕ Unit) →ₗ[ℂ] ℂ := PiLp.projₗ 2 (fun _ : Fin n ⊕ Unit => ℂ) (Sum.inr ())
  have hlx : last x ≠ 0 := hα
  have hleast : ∀ i, c ≤ C.colSingularValues i := by
    intro i
    have h := ciInf_le (Set.finite_range C.colSingularValues).bddBelow i
    rw [← C.sortedSingularValues_eq_iInf_colSingularValues] at h
    simpa [c] using h
  have hchar (y : EuclideanSpace ℂ (Fin n ⊕ Unit)) :=
    least_stretch_iff_vanishes_above C c (C.sortedSingularValues_nonneg n) hleast y
  have hx : ∀ i, c < C.colSingularValues i → inner ℂ (C.rightSingularBasis i) x = 0 := by
    apply (hchar x).mp
    change ‖toEuclideanLin C (WithLp.toLp 2 w)‖ = c * ‖x‖
    rw [toEuclideanLin_toLp, show ‖x‖ = 1 from hw, mul_one]
    exact hmin
  obtain ⟨e, he⟩ := C.exists_equiv_colSingularValues_eq_sortedSingularValues
  have hcard : Fintype.card (Fin n ⊕ Unit) = n + 1 := by simp
  let a := e ⟨n - 1, by omega⟩
  let a' := e ⟨n, by omega⟩
  have haa' : a ≠ a' := by
    intro h
    have hh := congrArg Fin.val (e.injective h)
    change n - 1 = n at hh
    omega
  have heq : C.colSingularValues a = c := (he _).trans htie.symm
  have heq' : C.colSingularValues a' = c := he _
  let v := C.rightSingularBasis a
  let v' := C.rightSingularBasis a'
  have hbasis := orthonormal_iff_ite.mp C.rightSingularBasis.orthonormal
  have hv (i) (hi : c < C.colSingularValues i) : inner ℂ (C.rightSingularBasis i) v = 0 := by
    have hne : i ≠ a := by
      rintro rfl
      rw [heq] at hi
      exact (lt_irrefl c) hi
    simp [v, hbasis, hne]
  have hv' (i) (hi : c < C.colSingularValues i) : inner ℂ (C.rightSingularBasis i) v' = 0 := by
    have hne : i ≠ a' := by
      rintro rfl
      rw [heq'] at hi
      exact (lt_irrefl c) hi
    simp [v', hbasis, hne]
  obtain ⟨z, hz, hlz, hzs⟩ : ∃ z : EuclideanSpace ℂ (Fin n ⊕ Unit),
      z ≠ 0 ∧ last z = 0 ∧
      ∀ i, c < C.colSingularValues i → inner ℂ (C.rightSingularBasis i) z = 0 := by
    by_cases hzero : last v = 0
    · exact ⟨v, norm_ne_zero_iff.mp (by simp [v]), hzero, hv⟩
    · refine ⟨last v' • v - last v • v', ?_, by simp [mul_comm], ?_⟩
      · intro H
        have h := congrArg (inner ℂ v') H
        simp [inner_sub_right, inner_smul_right, v, v', hbasis, Ne.symm haa'] at h
        exact hzero h
      · intro i hi
        simp [inner_sub_right, inner_smul_right, hv i hi, hv' i hi]
  let q := x + z
  have hlq : last q = last x := by simp [q, hlz]
  have hq : q ≠ 0 := by
    intro h
    exact hlx (hlq.symm.trans (h ▸ map_zero last))
  let t : ℂ := (‖q‖ : ℂ)⁻¹
  let y := t • q
  let w' := WithLp.ofLp y
  have ht : t ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hq))
  have hy1 : ‖y‖ = 1 := by
    rw [show y = t • q from rfl, norm_smul]
    simp [t, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq)]
  have hyl : w' (Sum.inr ()) ≠ 0 := by
    change last y ≠ 0
    rw [show y = t • q from rfl, map_smul, hlq, smul_eq_mul]
    exact mul_ne_zero ht hlx
  have hym : ‖(WithLp.toLp 2 (C *ᵥ w') : EuclideanSpace ℂ (Fin m))‖ = c := by
    have h := (hchar y).mpr (by
      intro i hi
      simp [y, q, inner_add_right, inner_smul_right, hx i hi, hzs i hi])
    rwa [hy1, mul_one, ← WithLp.toLp_ofLp 2 y, toEuclideanLin_toLp] at h
  obtain ⟨E, R, hER, _, hP, _⟩ := theorem_6_4 A b w hw (by simpa using hmin) hα
  obtain ⟨E', R', hER', _, hP', _⟩ := theorem_6_4 A b w' hy1 (by simpa [c, C, B] using hym) hyl
  rintro ⟨ER, _, hUnique⟩
  have hsame : (E, R) = (E', R') := (hUnique _ hER).trans (hUnique _ hER').symm
  have hsameP : vecMulVec (C *ᵥ w) (star w) = vecMulVec (C *ᵥ w') (star w') := by
    apply neg_injective
    exact hP.symm.trans ((congrArg (fun p : Matrix (Fin m) (Fin n) ℂ × Matrix (Fin m) Unit ℂ =>
      fromCols p.1 p.2) hsame).trans hP')
  have hproj := congrArg (fun M : Matrix (Fin m) (Fin n ⊕ Unit) ℂ => M *ᵥ w') hsameP
  have hself : star w' ⬝ᵥ w' = 1 := by rw [star_dotProduct_self, show ‖WithLp.toLp 2 w'‖ = 1 from hy1]; simp
  rw [vecMulVec_mulVec, vecMulVec_mulVec, hself] at hproj
  have hproj' : (star w ⬝ᵥ w') • (C *ᵥ w) = C *ᵥ w' := by
    funext i
    simpa only [Pi.smul_apply, op_smul_eq_mul, smul_eq_mul, one_mul, mul_comm] using congrFun hproj i
  have hinj : Function.Injective C.mulVec := by
    rw [mulVec_injective_iff, linearIndependent_iff_card_eq_finrank_span,
      Set.finrank, ← C.rank_eq_finrank_span_cols, hfull, hcard]
  let s := star w ⬝ᵥ w'
  have heqv : s • w = w' := hinj (by
    rw [mulVec_smul]
    exact hproj')
  have heqy : s • x = y := congrArg (WithLp.toLp 2) heqv
  have heql := congrArg last heqy
  change last (s • x) = last (t • q) at heql
  simp only [map_smul, hlq, smul_eq_mul] at heql
  have hst : s = t := mul_right_cancel₀ hlx heql
  have hsame_xq : x = q := by
    have hwq : t • x = t • q := by
      simpa only [hst] using (show s • x = t • q from heqy)
    have h := congrArg (t⁻¹ • ·) hwq
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using h
  exact hz (by simpa [q] using hsame_xq.symm)

/-- **Theorem 4**, uniqueness, of [benIsrael2003generalized], Chapter 6.
For a full-column-rank augmentation with at least two columns and an
admissible least-stretch vector, the Frobenius-optimal perturbation is
unique exactly when the least singular value is simple. -/
theorem theorem_6_4_unique_iff_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (b : Fin m → ℂ) (w : Fin n ⊕ Unit → ℂ)
    (hw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n ⊕ Unit))‖ = 1)
    (hmin : ‖(WithLp.toLp 2 (fromCols A (replicateCol Unit b) *ᵥ w) :
      EuclideanSpace ℂ (Fin m))‖ = (fromCols A (replicateCol Unit b)).sortedSingularValues n)
    (hα : w (Sum.inr ()) ≠ 0) (hn : 0 < n)
    (hfull : (fromCols A (replicateCol Unit b)).rank = n + 1) :
    (∃! ER : Matrix (Fin m) (Fin n) ℂ × Matrix (Fin m) Unit ℂ,
        IsTLSPerturbation 1 1 A (replicateCol Unit b) ER.1 ER.2) ↔
      (fromCols A (replicateCol Unit b)).sortedSingularValues n <
        (fromCols A (replicateCol Unit b)).sortedSingularValues (n - 1) := by
  refine ⟨?_, theorem_6_4_unique_of_gap A b w hw hmin hα hfull⟩
  intro h
  by_contra hg
  have htie := le_antisymm
    ((fromCols A (replicateCol Unit b)).sortedSingularValues_antitone (Nat.sub_le n 1))
    (not_lt.mp hg)
  exact tls_not_unique_of_tie A b w hw hmin hα hn hfull htie h

end BenIsraelGreville.Chapter06
