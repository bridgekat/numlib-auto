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

end BenIsraelGreville.Chapter06
