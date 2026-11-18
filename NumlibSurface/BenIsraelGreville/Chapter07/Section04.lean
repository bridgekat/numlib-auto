/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter00.Section03
import NumlibSurface.BenIsraelGreville.Chapter02.Section06
import NumlibSurface.BenIsraelGreville.Chapter04.Section06
import NumlibSurface.BenIsraelGreville.Chapter05.Section02
import NumlibSurface.BenIsraelGreville.Chapter07.Section01
import NumlibSurface.BenIsraelGreville.Chapter07.Section03

/-!
# Computing prescribed outer inverses

Section 7.4 of [benIsrael2003generalized] computes an outer inverse from
matrices with the prescribed range and kernel. The method specializes to
the Moore–Penrose, group, and Drazin inverses.
-/

namespace BenIsraelGreville.Chapter07

open Matrix Module

variable {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]

private theorem rank_eq_of_ker_eq {u v w : Type*} [Fintype w]
    (A : Matrix u w ℂ) (B : Matrix v w ℂ) (h : A.mulVecLin.ker = B.mulVecLin.ker) :
    A.rank = B.rank := by
  have ha := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hb := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [h] at ha
  exact Nat.add_right_cancel (ha.trans hb.symm)

/-- **Equation (17)** of [benIsrael2003generalized], Chapter 7.
A prescribed outer inverse equals $U Y V$ for any inner inverse $Y$ of $VAU$.
The ranks agree, including when the outer inverse is zero. -/
theorem outerInverse_eq_of_range_ker {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    (hX : A.IsOuterInverse X) (U : Matrix n p ℂ) (V : Matrix q m ℂ)
    (hR : U.mulVecLin.range = X.mulVecLin.range) (hK : V.mulVecLin.ker = X.mulVecLin.ker) :
    U.rank = V.rank ∧ V.rank = (V * A * U).rank ∧
      ∀ Y : Matrix p q ℂ, (V * A * U).IsInnerInverse Y → X = U * Y * V := by
  have hx : X * A * X = X := isOuterInverse_iff.mp hX
  have hu : X * A * U = U := by
    rw [ext_iff_mulVec]
    intro v
    obtain ⟨w, hw⟩ := hR ▸ LinearMap.mem_range_self U.mulVecLin v
    change X *ᵥ w = U *ᵥ v at hw
    rw [← mulVec_mulVec, ← hw, mulVec_mulVec, hx]
  have hbker : (V * A * U).mulVecLin.ker = U.mulVecLin.ker := by
    ext v
    simp only [LinearMap.mem_ker, mulVecLin_apply]
    constructor
    · intro hv
      have h : A *ᵥ (U *ᵥ v) ∈ X.mulVecLin.ker := by
        rw [← hK, LinearMap.mem_ker, mulVecLin_apply, mulVec_mulVec, mulVec_mulVec]
        exact hv
      rw [LinearMap.mem_ker, mulVecLin_apply, mulVec_mulVec, mulVec_mulVec, hu] at h
      exact h
    · intro hv
      rw [← mulVec_mulVec, hv, mulVec_zero]
  have hur : U.rank = X.rank := by rw [rank, rank, hR]
  have hvr : V.rank = X.rank := rank_eq_of_ker_eq _ _ hK
  have hbr := rank_eq_of_ker_eq _ _ hbker
  refine ⟨hur.trans hvr.symm, hvr.trans (hur.symm.trans hbr.symm), ?_⟩
  intro Y hy
  let B := V * A * U
  have hfix : U * Y * B = U := by
    rw [ext_iff_mulVec]
    intro z
    have h : Y *ᵥ (B *ᵥ z) - z ∈ B.mulVecLin.ker := by
      rw [LinearMap.mem_ker, mulVecLin_apply, mulVec_sub, mulVec_mulVec, mulVec_mulVec,
        isInnerInverse_iff.mp hy, sub_self]
    rw [show B.mulVecLin.ker = U.mulVecLin.ker from hbker, LinearMap.mem_ker,
      mulVecLin_apply, mulVec_sub, mulVec_mulVec, mulVec_mulVec, sub_eq_zero] at h
    exact h
  have hv : V * A * X = V := by
    rw [ext_iff_mulVec]
    intro z
    have h : (A * X) *ᵥ z - z ∈ X.mulVecLin.ker := by
      rw [LinearMap.mem_ker, mulVecLin_apply, mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc,
        hx, sub_self]
    rw [← hK, LinearMap.mem_ker, mulVecLin_apply, mulVec_sub, mulVec_mulVec,
      ← Matrix.mul_assoc, sub_eq_zero] at h
    exact h
  have hc : U * Y * V * A * X = X := by
    rw [ext_iff_mulVec]
    intro z
    obtain ⟨w, hw⟩ := hR.symm ▸ LinearMap.mem_range_self X.mulVecLin z
    change U *ᵥ w = X *ᵥ z at hw
    rw [← mulVec_mulVec, ← hw, mulVec_mulVec]
    have he : U * Y * V * A * U = U * Y * B := by simp only [B, Matrix.mul_assoc]
    rw [he, hfix]
  calc
    X = U * Y * V * A * X := hc.symm
    _ = U * Y * (V * A * X) := by simp only [Matrix.mul_assoc]
    _ = U * Y * V := by rw [hv]

/-- **Equation (18)** of [benIsrael2003generalized], Chapter 7.
Zlobec's formula computes the Moore–Penrose inverse from any inner inverse
of $A^H A A^H$. -/
theorem pinv_eq_zlobec [DecidableEq n] (A : Matrix m n ℂ) (Y : Matrix m n ℂ)
    (hY : (Aᴴ * A * Aᴴ).IsInnerInverse Y) : A.pinv = Aᴴ * Y * Aᴴ :=
  Chapter02.exercise_39 A Y hY

/-- Powers at or beyond the index have the range and kernel of the
Drazin inverse. -/
theorem range_ker_drazinInverse_eq_pow [DecidableEq n]
    (A : Matrix n n ℂ) {l : ℕ} (hl : Chapter04.matrixIndex A ≤ l) :
    (A ^ l).mulVecLin.range = (Chapter04.drazinInverse A).mulVecLin.range ∧
      (A ^ l).mulVecLin.ker = (Chapter04.drazinInverse A).mulVecLin.ker := by
  obtain ⟨_, hR, hK⟩ := (drazin_unique_outerInverse_range_ker A hl).1
  exact ⟨hR.symm, hK.symm⟩

/-- **Equation (4.48)** of [benIsrael2003generalized], Chapter 7.
Greville's formula computes the Drazin inverse from any inner inverse
of the indicated power. -/
theorem drazin_eq_greville [DecidableEq n] (A : Matrix n n ℂ) {l : ℕ}
    (hl : Chapter04.matrixIndex A ≤ l) (Y : Matrix n n ℂ)
    (hY : (A ^ (2 * l + 1)).IsInnerInverse Y) :
    Chapter04.drazinInverse A = A ^ l * Y * A ^ l := by
  obtain ⟨hR, hK⟩ := range_ker_drazinInverse_eq_pow A hl
  apply (outerInverse_eq_of_range_ker (Chapter04.isDrazinInverseAt_drazinInverse A).outer
    (A ^ l) (A ^ l) hR hK).2.2 Y
  rw [← pow_succ, ← pow_add, show l + 1 + l = 2 * l + 1 by omega]
  exact hY

/-- **Equation (5.28)** of [benIsrael2003generalized], Chapter 7, in the
coordinates in which the nonsingular maximal pivot is the first block.
Row and column reindexing are handled by `Chapter05.pinv_submatrix_equiv`. -/
theorem pinv_eq_noble {r : Type*} [Fintype r] [DecidableEq r] [DecidableEq n]
    {A : Matrix r r ℂ} (B : Matrix r n ℂ) (C : Matrix m r ℂ) (D : Matrix m n ℂ)
    (hA : IsUnit A) (hr : (fromBlocks A B C D).rank = A.rank) :
    let S := Chapter05.rowMultiplier A C
    let T := Chapter05.columnMultiplier A B
    (fromBlocks A B C D).pinv =
      (fromCols (1 : Matrix r r ℂ) T)ᴴ * (1 + T * Tᴴ)⁻¹ * A⁻¹ *
        (1 + Sᴴ * S)⁻¹ * (fromRows (1 : Matrix r r ℂ) S)ᴴ := by
  dsimp only
  simpa only [Matrix.mul_assoc] using (Chapter05.theorem_5_2 B C D hA hr).2.2.2

/-- **Equation (1.17)** of [benIsrael2003generalized], Chapter 7.
MacDuffee's formula uses the nonsingular compressed matrix $F^H A G^H$. -/
theorem pinv_eq_macDuffee {r : Type*} [Fintype r] [DecidableEq r] [DecidableEq n]
    {A : Matrix m n ℂ} {F : Matrix m r ℂ} {G : Matrix r n ℂ}
    (hA : A = F * G) (hr : 0 < A.rank) (hF : F.rank = Fintype.card r)
    (hG : G.rank = Fintype.card r) :
    IsUnit (Fᴴ * A * Gᴴ) ∧ A.pinv = Gᴴ * (Fᴴ * A * Gᴴ)⁻¹ * Fᴴ :=
  Chapter01.theorem_5 hA hr hF hG

/-- **Equation (4.22)** of [benIsrael2003generalized], Chapter 7.
For a full-rank factorization $FG$, the compressed product $GF$ is
invertible exactly when the group inverse exists. -/
theorem groupInverse_eq_cline {r : Type*} [Fintype r] [DecidableEq r] [DecidableEq n]
    (F : Matrix n r ℂ) (G : Matrix r n ℂ)
    (hF : F.rank = Fintype.card r) (hG : G.rank = Fintype.card r) (X : Matrix n n ℂ) :
    Chapter04.IsGroupInverse (F * G) X ↔ IsUnit (G * F) ∧ X = F * (G * F)⁻¹ ^ 2 * G :=
  Chapter04.theorem_4_3 F G hF hG X

/-- **Equations (4.46a)–(4.46b)** of [benIsrael2003generalized], Chapter 7.
A Cline chain stores the successive full-rank factorizations from a
square matrix to a compressed square matrix. -/
inductive ClineRankChain :
    (steps : ℕ) → {a b : ℕ} → Matrix (Fin a) (Fin a) ℂ → Matrix (Fin b) (Fin b) ℂ → Type where
  | done {a : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) : ClineRankChain 0 A A
  | step {k a b c : ℕ} (F : Matrix (Fin a) (Fin b) ℂ) (G : Matrix (Fin b) (Fin a) ℂ)
      (hF : F.rank = Fintype.card (Fin b)) (hG : G.rank = Fintype.card (Fin b))
      {H : Matrix (Fin c) (Fin c) ℂ} (tail : ClineRankChain k (G * F) H) :
      ClineRankChain (k + 1) (F * G) H

namespace ClineRankChain

variable {k a b : ℕ} {A : Matrix (Fin a) (Fin a) ℂ} {H : Matrix (Fin b) (Fin b) ℂ}

/-- The product of the left factors in forward order. -/
def left : ∀ {k a b : ℕ} {A : Matrix (Fin a) (Fin a) ℂ} {H : Matrix (Fin b) (Fin b) ℂ},
    ClineRankChain k A H → Matrix (Fin a) (Fin b) ℂ
  | _, _, _, _, _, .done _ => 1
  | _, _, _, _, _, .step F _ _ _ tail => F * left tail

/-- The product of the right factors in reverse order. -/
def right : ∀ {k a b : ℕ} {A : Matrix (Fin a) (Fin a) ℂ} {H : Matrix (Fin b) (Fin b) ℂ},
    ClineRankChain k A H → Matrix (Fin b) (Fin a) ℂ
  | _, _, _, _, _, .done _ => 1
  | _, _, _, _, _, .step _ G _ _ tail => right tail * G

private theorem pow_mul_factor {a b : ℕ}
    (F : Matrix (Fin a) (Fin b) ℂ) (G : Matrix (Fin b) (Fin a) ℂ) (j : ℕ) :
    (F * G) ^ (j + 1) = F * (G * F) ^ j * G := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ (F * G), ih, pow_succ (G * F)]
    simp only [Matrix.mul_assoc]

/-- Every power at or beyond the chain length factors through the final matrix. -/
theorem pow_eq (chain : ClineRankChain k A H) (j : ℕ) :
    A ^ (k + j) = chain.left * H ^ j * chain.right := by
  induction chain with
  | done A => simp [left, right]
  | @step k a b c F G hF hG H tail ih =>
    rw [show k + 1 + j = k + j + 1 by omega, pow_mul_factor, ih]
    simp only [left, right, Matrix.mul_assoc]

/-- At the chain length and beyond, the rank is the rank of the corresponding
power of the final matrix. -/
theorem rank_pow_eq (chain : ClineRankChain k A H) (j : ℕ) :
    (A ^ (k + j)).rank = (H ^ j).rank := by
  induction chain with
  | done A => simp
  | @step k a b c F G hF hG H tail ih =>
    rw [show k + 1 + j = k + j + 1 by omega, pow_mul_factor,
      Chapter01.exercise_7 F ((G * F) ^ (k + j)) G hF hG, ih]

private theorem left_comm (chain : ClineRankChain k A H) :
    A * chain.left = chain.left * H := by
  induction chain with
  | done A => simp [left]
  | @step k a b c F G hF hG H tail ih =>
    simp only [left, ← Matrix.mul_assoc]
    calc
      F * G * F * tail.left = F * ((G * F) * tail.left) := by simp only [Matrix.mul_assoc]
      _ = F * (tail.left * H) := by rw [ih]
      _ = _ := by simp only [Matrix.mul_assoc]

private theorem right_comm (chain : ClineRankChain k A H) :
    chain.right * A = H * chain.right := by
  induction chain with
  | done A => simp [right]
  | @step k a b c F G hF hG H tail ih =>
    simp only [right]
    calc
      tail.right * G * (F * G) = tail.right * (G * F) * G := by
        simp only [Matrix.mul_assoc]
      _ = H * (tail.right * G) := by rw [ih, Matrix.mul_assoc]

private theorem right_mul_left (chain : ClineRankChain k A H) :
    chain.right * chain.left = H ^ k := by
  induction chain with
  | done A => simp [left, right]
  | @step k a b c F G hF hG H tail ih =>
    simp only [left, right]
    calc
      tail.right * G * (F * tail.left) = tail.right * ((G * F) * tail.left) := by
        simp only [Matrix.mul_assoc]
      _ = tail.right * (tail.left * H) := by rw [tail.left_comm]
      _ = H ^ (k + 1) := by rw [← Matrix.mul_assoc, ih, pow_succ]

/-- A sequence of full-rank factorizations can be continued for any
specified finite number of steps. -/
theorem exists_chain (A : Matrix (Fin a) (Fin a) ℂ) (k : ℕ) :
    ∃ b, ∃ H : Matrix (Fin b) (Fin b) ℂ, Nonempty (ClineRankChain k A H) := by
  induction k generalizing a with
  | zero => exact ⟨a, A, ⟨.done A⟩⟩
  | succ k ih =>
    obtain ⟨F, G, hFG⟩ := (rank_le_iff_exists_mul A A.rank).mp le_rfl
    have hcard : Fintype.card (Fin A.rank) = (F * G).rank := by simp [← hFG]
    have hF := le_antisymm F.rank_le_card_width (hcard.le.trans (rank_mul_le_left _ _))
    have hG := le_antisymm G.rank_le_card_height (hcard.le.trans (rank_mul_le_right _ _))
    obtain ⟨b, H, ⟨tail⟩⟩ := ih (G * F)
    exact ⟨b, H, ⟨hFG ▸ ClineRankChain.step F G hF hG tail⟩⟩

end ClineRankChain

/-- **Equation (4.46c)** of [benIsrael2003generalized], Chapter 7.
At the index, Cline's repeated factorization yields an invertible final
matrix and computes the Drazin inverse by lifting its inverse power. -/
theorem drazin_eq_cline {a b k : ℕ}
    {A : Matrix (Fin a) (Fin a) ℂ} {H : Matrix (Fin b) (Fin b) ℂ}
    (chain : ClineRankChain k A H) (hk : Chapter04.matrixIndex A ≤ k) :
    IsUnit H ∧ Chapter04.drazinInverse A = chain.left * H⁻¹ ^ (k + 1) * chain.right := by
  let P := chain.left
  let Q := chain.right
  let J := H⁻¹ ^ (k + 1)
  let X := P * J * Q
  have hk₀ : 0 < k := A.rankStabilizationIndex_spec.1.trans_le hk
  have hr := (A.rank_pow_eq_succ_iff hk₀).mpr hk
  have hr₀ : (A ^ k).rank = Fintype.card (Fin b) := by
    simpa using chain.rank_pow_eq 0
  have hr₁ : (A ^ (k + 1)).rank = H.rank := by
    simpa only [pow_one] using chain.rank_pow_eq 1
  have hH : IsUnit H :=
    mulVec_surjective_iff_isUnit.mp (mulVec_surjective_iff_rank_eq_card.mpr
      (hr₁.symm.trans (hr.symm.trans hr₀)))
  have hDet := (isUnit_iff_isUnit_det H).mp hH
  have hInv : Commute H H⁻¹ := by
    change H * H⁻¹ = H⁻¹ * H
    rw [mul_nonsing_inv H hDet, nonsing_inv_mul H hDet]
  have hJ : H ^ (k + 1) * J = 1 := by
    change H ^ (k + 1) * H⁻¹ ^ (k + 1) = 1
    rw [← hInv.mul_pow, mul_nonsing_inv H hDet, one_pow]
  have hAP : A * P = P * H := chain.left_comm
  have hQA : Q * A = H * Q := chain.right_comm
  have hQP : Q * P = H ^ k := chain.right_mul_left
  have hPow₀ : A ^ k = P * Q := by simpa using chain.pow_eq 0
  have hPow₁ : A ^ (k + 1) = P * H * Q := by
    simpa only [pow_one] using chain.pow_eq 1
  have hComm : Commute A X := by
    change A * (P * J * Q) = P * J * Q * A
    calc
      _ = (A * P) * J * Q := by simp only [Matrix.mul_assoc]
      _ = P * (H * J) * Q := by rw [hAP, Matrix.mul_assoc P H J]
      _ = P * J * (H * Q) := by
        have hHJ : H * J = J * H := (hInv.pow_right (k + 1)).eq
        rw [hHJ]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hQA]; simp only [Matrix.mul_assoc]
  have hS : A ^ (k + 1) * X = A ^ k := by
    change A ^ (k + 1) * (P * J * Q) = A ^ k
    calc
      _ = P * (H * (Q * P)) * J * Q := by rw [hPow₁]; simp only [Matrix.mul_assoc]
      _ = P * (H ^ (k + 1) * J) * Q := by rw [hQP, pow_succ', Matrix.mul_assoc P]
      _ = _ := by rw [hJ, Matrix.mul_one, hPow₀]
  have hO : X * A * X = X := by
    change P * J * Q * A * (P * J * Q) = P * J * Q
    calc
      _ = P * J * ((Q * A) * P) * J * Q := by simp only [Matrix.mul_assoc]
      _ = P * J * (H ^ (k + 1) * J) * Q := by
        rw [hQA, Matrix.mul_assoc H Q P, hQP, pow_succ', Matrix.mul_assoc (P * J)]
      _ = _ := by rw [hJ, Matrix.mul_one]
  exact ⟨hH, ((Chapter04.isDrazinInverseAt_drazinInverse A).mono hk).unique
    ⟨hComm, hO, hS⟩⟩

omit [Fintype n] in
/-- **Exercise 6**, Equations (19)–(20) of [benIsrael2003generalized],
Chapter 7. In the permuted coordinates, the row operation matrix reduces
the pivot block to the identity and records the inverse pivot and the
row multiplier in the augmented identity block. -/
theorem exercise_6_block {r : Type*} [Fintype r] [DecidableEq r] [DecidableEq m]
    (J : Matrix r r ℂ) (S : Matrix m r ℂ) (T : Matrix r n ℂ) (hJ : IsUnit J) :
    let F := fromRows (1 : Matrix r r ℂ) S
    let G := fromCols (1 : Matrix r r ℂ) T
    let E := fromBlocks J⁻¹ (0 : Matrix r m ℂ) (-S) (1 : Matrix m m ℂ)
    IsUnit E ∧
      E * fromCols (F * J * G) (1 : Matrix (r ⊕ m) (r ⊕ m) ℂ) =
        fromCols (fromBlocks (1 : Matrix r r ℂ) T (0 : Matrix m r ℂ)
          (0 : Matrix m n ℂ)) E := by
  dsimp only
  let E := fromBlocks J⁻¹ (0 : Matrix r m ℂ) (-S) (1 : Matrix m m ℂ)
  have hDet := (isUnit_iff_isUnit_det J).mp hJ
  have hLeft : E *
      fromBlocks J (0 : Matrix r m ℂ) (S * J) (1 : Matrix m m ℂ) = 1 := by
    change fromBlocks J⁻¹ (0 : Matrix r m ℂ) (-S) (1 : Matrix m m ℂ) *
      fromBlocks J (0 : Matrix r m ℂ) (S * J) (1 : Matrix m m ℂ) = 1
    rw [fromBlocks_multiply, nonsing_inv_mul J hDet, ← fromBlocks_one]
    simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul,
      Matrix.neg_mul, add_zero, zero_add, neg_add_cancel]
  refine ⟨(isUnit_iff_isUnit_det E).mpr (isUnit_det_of_right_inverse hLeft), ?_⟩
  have hF : E * fromRows (1 : Matrix r r ℂ) S = fromRows J⁻¹ (0 : Matrix m r ℂ) := by
    change fromBlocks J⁻¹ (0 : Matrix r m ℂ) (-S) 1 * fromRows (1 : Matrix r r ℂ) S = _
    rw [fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.zero_mul, add_zero,
      Matrix.mul_one, Matrix.one_mul, neg_add_cancel]
  change E * fromCols (_ * J * _) 1 = fromCols _ E
  rw [mul_fromCols, Matrix.mul_one E, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hF,
    fromRows_mul, nonsing_inv_mul J hDet, Matrix.zero_mul, fromRows_mul_fromCols]
  simp only [Matrix.one_mul, Matrix.zero_mul]

omit [Fintype n] in
/-- **Exercise 6**, Equations (19)–(20) of [benIsrael2003generalized],
Chapter 7. After reindexing the pivot first, the augmented reduction
can be carried out by elementary row scalings and additions. -/
theorem exercise_6_elementary_operations {r : Type*} [Fintype r] [DecidableEq r] [DecidableEq m]
    (J : Matrix r r ℂ) (S : Matrix m r ℂ) (T : Matrix r n ℂ) (hJ : IsUnit J) :
    let F := fromRows (1 : Matrix r r ℂ) S
    let G := fromCols (1 : Matrix r r ℂ) T
    let E := fromBlocks J⁻¹ (0 : Matrix r m ℂ) (-S) (1 : Matrix m m ℂ)
    ∃ l : List (Matrix (r ⊕ m) (r ⊕ m) ℂ),
      l.prod * fromCols (F * J * G) (1 : Matrix (r ⊕ m) (r ⊕ m) ℂ) =
        fromCols (fromBlocks (1 : Matrix r r ℂ) T (0 : Matrix m r ℂ)
          (0 : Matrix m n ℂ)) E ∧
      ∀ W ∈ l, Chapter00.IsScaleOrAddRowMatrix W := by
  dsimp only
  obtain ⟨hUnit, hReduction⟩ := exercise_6_block J S T hJ
  obtain ⟨l, hl, hop⟩ := Chapter00.exists_list_scaleOrAdd_of_isUnit _ hUnit
  exact ⟨l, hl.symm ▸ hReduction, hop⟩

/-- **Exercise 7**, Equations (6.30a)–(6.30b) of [benIsrael2003generalized],
Chapter 7. A reduced SVD gives the pseudoinverse by compressing onto
the two orthonormal singular-vector families. The middle factor only
needs to be invertible. -/
theorem pinv_eq_of_thinSVD {r : Type*} [Fintype r] [DecidableEq r]
    [DecidableEq n]
    {A : Matrix m n ℂ} (U : Matrix m r ℂ) (V : Matrix n r ℂ) (D : Matrix r r ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hD : IsUnit D)
    (hA : A = U * D * Vᴴ) :
    A.pinv = V * D⁻¹ * Uᴴ ∧ A.pinv = V * (Uᴴ * A * V)⁻¹ * Uᴴ := by
  classical
  let X := V * D⁻¹ * Uᴴ
  have hd₁ := D.mul_nonsing_inv ((isUnit_iff_isUnit_det D).mp hD)
  have hd₂ := D.nonsing_inv_mul ((isUnit_iff_isUnit_det D).mp hD)
  have hAX : A * X = U * Uᴴ := by
    change A * (V * D⁻¹ * Uᴴ) = _
    rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (U * D) Vᴴ V,
      hV, Matrix.mul_one, Matrix.mul_assoc U D D⁻¹, hd₁, Matrix.mul_one]
  have hXA : X * A = V * Vᴴ := by
    change (V * D⁻¹ * Uᴴ) * A = _
    rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (V * D⁻¹) Uᴴ U,
      hU, Matrix.mul_one, Matrix.mul_assoc V D⁻¹ D, hd₂, Matrix.mul_one]
  have hp : X = A.pinv := by
    apply A.pinv_unique
    · rw [hAX, hA]
      calc
        (U * Uᴴ) * (U * D * Vᴴ) = U * (Uᴴ * U) * D * Vᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.mul_one]
    · rw [hXA]
      change (V * Vᴴ) * (V * D⁻¹ * Uᴴ) = V * D⁻¹ * Uᴴ
      calc
        (V * Vᴴ) * (V * D⁻¹ * Uᴴ) = V * (Vᴴ * V) * D⁻¹ * Uᴴ := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV, Matrix.mul_one]
    · rw [hAX]
      exact isHermitian_mul_conjTranspose_self U
    · rw [hXA]
      exact isHermitian_mul_conjTranspose_self V
  have he : Uᴴ * A * V = D := calc
    Uᴴ * A * V = (Uᴴ * U) * D * (Vᴴ * V) := by rw [hA]; simp only [Matrix.mul_assoc]
    _ = D := by rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
  have hR : V.mulVecLin.range = A.pinv.mulVecLin.range := by
    rw [← hp]
    change V.mulVecLin.range = (V * D⁻¹ * Uᴴ).mulVecLin.range
    apply le_antisymm ?_ (by
      rw [Matrix.mul_assoc, mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _)
    have hVU : X * U * D = V := by
      change V * D⁻¹ * Uᴴ * U * D = V
      rw [Matrix.mul_assoc (V * D⁻¹) Uᴴ U, hU, Matrix.mul_one,
        Matrix.mul_assoc V D⁻¹ D, hd₂, Matrix.mul_one]
    conv_lhs => rw [← hVU, mulVecLin_mul, mulVecLin_mul]
    exact (LinearMap.range_comp_le_range _ _).trans (LinearMap.range_comp_le_range _ _)
  have hK : Uᴴ.mulVecLin.ker = A.pinv.mulVecLin.ker := by
    rw [← hp]
    change Uᴴ.mulVecLin.ker = (V * D⁻¹ * Uᴴ).mulVecLin.ker
    apply le_antisymm (by rw [mulVecLin_mul]; exact LinearMap.ker_le_ker_comp _ _) ?_
    have hVX : D * Vᴴ * X = Uᴴ := by
      change D * Vᴴ * (V * D⁻¹ * Uᴴ) = Uᴴ
      calc
        _ = D * (Vᴴ * V) * D⁻¹ * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = Uᴴ := by rw [hV, Matrix.mul_one, hd₁, Matrix.one_mul]
    conv_rhs => rw [← hVX, mulVecLin_mul]
    exact LinearMap.ker_le_ker_comp _ _
  refine ⟨hp.symm, (outerInverse_eq_of_range_ker A.pinv_mul_self_mul_pinv V Uᴴ hR hK).2.2
    (Uᴴ * A * V)⁻¹ ?_⟩
  rw [he, isInnerInverse_iff, hd₁, Matrix.one_mul]

/-- The Moore–Penrose and group inverse for the matrix of Exercise 5. -/
noncomputable def exercise_7_5_inverse : Matrix (Fin 4) (Fin 4) ℂ :=
  !![3/8, 3/8, -1/8, -1/8; -1/8, 3/8, 3/8, -1/8;
    -1/8, -1/8, 3/8, 3/8; 3/8, -1/8, -1/8, 3/8]

/-- A pivot-supported inner inverse for the compressed matrix in Exercise 9(a). -/
noncomputable def exercise_9_zlobecInnerInverse : Matrix (Fin 4) (Fin 4) ℂ :=
  !![3/8, -1/2, 3/8, 0; 0, 1/2, -1/2, 0; -1/8, 0, 3/8, 0; 0, 0, 0, 0]

set_option maxHeartbeats 1200000 in
-- Evaluate the entries of the exact product of the four-by-four matrices.
/-- **Exercise 9(a)** of [benIsrael2003generalized], Chapter 7.
A concrete inner inverse of the compressed matrix gives the exact
Moore–Penrose inverse by Zlobec's formula. -/
theorem exercise_9_zlobec :
    (exercise_7_5_matrixᴴ * exercise_7_5_matrix * exercise_7_5_matrixᴴ).IsInnerInverse
        exercise_9_zlobecInnerInverse ∧
      exercise_7_5_matrix.pinv = exercise_7_5_inverse := by
  have hY : (exercise_7_5_matrixᴴ * exercise_7_5_matrix * exercise_7_5_matrixᴴ).IsInnerInverse
      exercise_9_zlobecInnerInverse := by
    rw [isInnerInverse_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [exercise_7_5_matrix, exercise_9_zlobecInnerInverse, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ]
  refine ⟨hY, (pinv_eq_zlobec exercise_7_5_matrix exercise_9_zlobecInnerInverse hY).trans ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [exercise_7_5_matrix, exercise_9_zlobecInnerInverse, exercise_7_5_inverse,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

/-- The left factor of the matrix from Exercise 5, used in Exercises 9–10. -/
def exercise_7_5_leftFactor : Matrix (Fin 4) (Fin 3) ℂ :=
  !![1, 0, 0; 1, 1, 0; 0, 1, 1; 0, 0, 1]

/-- The right factor of the matrix from Exercise 5, used in Exercises 9–10. -/
def exercise_7_5_rightFactor : Matrix (Fin 3) (Fin 4) ℂ :=
  !![1, 0, 0, 1; 0, 1, 0, -1; 0, 0, 1, 1]

private theorem worked_rankFactorization :
    exercise_7_5_matrix = exercise_7_5_leftFactor * exercise_7_5_rightFactor ∧
      exercise_7_5_leftFactor.rank = Fintype.card (Fin 3) ∧
      exercise_7_5_rightFactor.rank = Fintype.card (Fin 3) := by
  let L : Matrix (Fin 3) (Fin 4) ℂ := !![1, 0, 0, 0; -1, 1, 0, 0; 1, -1, 1, 0]
  let R : Matrix (Fin 4) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0; 0, 0, 1; 0, 0, 0]
  have hF : L * exercise_7_5_leftFactor = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [L, exercise_7_5_leftFactor, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
  have hG : exercise_7_5_rightFactor * R = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [R, exercise_7_5_rightFactor, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]
  refine ⟨?_, le_antisymm exercise_7_5_leftFactor.rank_le_card_width ?_,
    le_antisymm exercise_7_5_rightFactor.rank_le_card_height ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [exercise_7_5_matrix, exercise_7_5_leftFactor, exercise_7_5_rightFactor,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · rw [← rank_one (R := ℂ), ← hF]
    exact rank_mul_le_right _ _
  · rw [← rank_one (R := ℂ), ← hG]
    exact rank_mul_le_left _ _

private theorem worked_matrix_rank : exercise_7_5_matrix.rank = Fintype.card (Fin 3) := by
  obtain ⟨hA, hF, hG⟩ := worked_rankFactorization
  rw [hA]
  simpa only [Matrix.mul_one, rank_one] using
    Chapter01.exercise_7 exercise_7_5_leftFactor (1 : Matrix (Fin 3) (Fin 3) ℂ)
      exercise_7_5_rightFactor hF hG

/-- **Exercise 9(b)** of [benIsrael2003generalized], Chapter 7.
Noble's formula using the leading three-by-three pivot gives the exact
worked pseudoinverse in the corresponding block coordinates. -/
theorem exercise_9_noble :
    let e : Fin 3 ⊕ Fin 1 ≃ Fin 4 := finSumFinEquiv
    let J : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 1, 1, 0; 0, 1, 1]
    let S := Chapter05.rowMultiplier J (!![0, 0, 1] : Matrix (Fin 1) (Fin 3) ℂ)
    let T := Chapter05.columnMultiplier J (!![1; 0; 0] : Matrix (Fin 3) (Fin 1) ℂ)
    exercise_7_5_inverse.submatrix e e =
      (fromCols (1 : Matrix (Fin 3) (Fin 3) ℂ) T)ᴴ * (1 + T * Tᴴ)⁻¹ * J⁻¹ *
        (1 + Sᴴ * S)⁻¹ * (fromRows (1 : Matrix (Fin 3) (Fin 3) ℂ) S)ᴴ := by
  dsimp only
  let e : Fin 3 ⊕ Fin 1 ≃ Fin 4 := finSumFinEquiv
  let J : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 1, 1, 0; 0, 1, 1]
  let B : Matrix (Fin 3) (Fin 1) ℂ := !![1; 0; 0]
  let C : Matrix (Fin 1) (Fin 3) ℂ := !![0, 0, 1]
  let D : Matrix (Fin 1) (Fin 1) ℂ := !![1]
  have hJ : IsUnit J := by
    apply (isUnit_iff_isUnit_det J).mpr
    rw [isUnit_iff_ne_zero, det_fin_three]
    norm_num [J]
  have hM : exercise_7_5_matrix.submatrix e e = fromBlocks J B C D := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> rfl
  have hr : (fromBlocks J B C D).rank = J.rank := by
    rw [← hM, rank_submatrix, worked_matrix_rank, rank_of_isUnit J hJ]
  change exercise_7_5_inverse.submatrix e e = _
  rw [← exercise_9_zlobec.2, ← Chapter05.pinv_submatrix_equiv, hM]
  exact pinv_eq_noble B C D hJ hr

/-- **Exercise 9(c)** of [benIsrael2003generalized], Chapter 7.
The leading independent columns and the coefficients of all columns
give the MacDuffee computation for Exercise 5. -/
theorem exercise_9_macDuffee :
    exercise_7_5_rightFactorᴴ *
      (exercise_7_5_leftFactorᴴ * exercise_7_5_matrix * exercise_7_5_rightFactorᴴ)⁻¹ *
      exercise_7_5_leftFactorᴴ = exercise_7_5_inverse := by
  obtain ⟨hA, hF, hG⟩ := worked_rankFactorization
  have hr : 0 < exercise_7_5_matrix.rank := by rw [worked_matrix_rank, Fintype.card_fin]; omega
  exact (pinv_eq_macDuffee hA hr hF hG).2.symm.trans exercise_9_zlobec.2

/-- **Exercise 10** of [benIsrael2003generalized], Chapter 7.
The group inverse in this example equals the Moore–Penrose inverse. -/
theorem exercise_10_group :
    Chapter04.IsGroupInverse exercise_7_5_matrix exercise_7_5_inverse := by
  have hc : Commute exercise_7_5_matrix exercise_7_5_inverse := by
    change exercise_7_5_matrix * exercise_7_5_inverse = exercise_7_5_inverse * exercise_7_5_matrix
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [exercise_7_5_matrix, exercise_7_5_inverse, Matrix.mul_apply, Fin.sum_univ_succ]
  refine (Chapter04.isDrazinInverseAt_iff 1 _ _).mpr ⟨?_, ?_, hc⟩
  · rw [Chapter04.SatisfiesFirstPowerEquation, pow_one, ← exercise_9_zlobec.2]
    exact exercise_7_5_matrix.mul_pinv_mul_self
  · rw [← exercise_9_zlobec.2, isOuterInverse_iff]
    exact exercise_7_5_matrix.pinv_mul_self_mul_pinv

/-- **Exercise 10(a)** of [benIsrael2003generalized], Chapter 7.
Cline's group-inverse formula applied to the worked rank factorization. -/
theorem exercise_10_cline :
    exercise_7_5_leftFactor * (exercise_7_5_rightFactor * exercise_7_5_leftFactor)⁻¹ ^ 2 *
      exercise_7_5_rightFactor = exercise_7_5_inverse := by
  obtain ⟨hA, hF, hG⟩ := worked_rankFactorization
  have h := exercise_10_group
  rw [hA] at h
  exact ((groupInverse_eq_cline exercise_7_5_leftFactor exercise_7_5_rightFactor
    hF hG exercise_7_5_inverse).mp h).2.symm

/-- A pivot-supported inner inverse for the third power in Exercise 10(b). -/
noncomputable def exercise_10_powerInnerInverse : Matrix (Fin 4) (Fin 4) ℂ :=
  !![-1/8, 1/2, -1/8, 0; 0, -1/2, 1/2, 0; 3/8, 0, -1/8, 0; 0, 0, 0, 0]

set_option maxHeartbeats 1200000 in
-- Evaluate the third power and its inner-inverse product in exact arithmetic.
/-- **Exercise 10(b)** of [benIsrael2003generalized], Chapter 7.
The inner inverse of the third power gives the same group inverse in
Equation (4.29). -/
theorem exercise_10_power :
    (exercise_7_5_matrix ^ 3).IsInnerInverse exercise_10_powerInnerInverse ∧
      exercise_7_5_matrix * exercise_10_powerInnerInverse * exercise_7_5_matrix =
        exercise_7_5_inverse := by
  refine ⟨?_, ?_⟩
  · rw [isInnerInverse_iff, show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [exercise_7_5_matrix, exercise_10_powerInnerInverse,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [exercise_7_5_matrix, exercise_10_powerInnerInverse, exercise_7_5_inverse,
        Matrix.mul_apply, Fin.sum_univ_succ]

end BenIsraelGreville.Chapter07
