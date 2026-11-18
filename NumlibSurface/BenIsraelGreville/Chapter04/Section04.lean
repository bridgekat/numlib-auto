/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter04.Section02
import NumlibSurface.BenIsraelGreville.Chapter01.Section03

/-!
# The group inverse

Section 4.4 of [benIsrael2003generalized] studies the commuting reflexive inverse of a
square matrix. It exists exactly at index one, and its rank-factorization formula uses
the inverse of the square product of the factors in reverse order.
-/

namespace BenIsraelGreville.Chapter04

open Matrix

variable {n k : Type*} [Fintype n] [DecidableEq n]

/-- **Section 4.4** of [benIsrael2003generalized]. A group inverse satisfies
$AXA=A$, $XAX=X$, and $AX=XA$. -/
abbrev IsGroupInverse (A X : Matrix n n ℂ) : Prop :=
  _root_.IsGroupInverse A X

/-- **Equations (23)–(24)** of [benIsrael2003generalized], Chapter 4. A matrix is
range-Hermitian when its column range equals the column range of its conjugate transpose. -/
def IsRangeHermitian (A : Matrix n n ℂ) : Prop :=
  LinearMap.range (toEuclideanLin A) = LinearMap.range (toEuclideanLin Aᴴ)

private theorem groupInverseFormula [Fintype k] [DecidableEq k] (F : Matrix n k ℂ)
    (G : Matrix k n ℂ) (hUnit : IsUnit (G * F)) :
    IsGroupInverse (F * G) (F * (G * F)⁻¹ ^ 2 * G) := by
  let J := G * F
  let Q := J⁻¹
  have hL : J * Q = 1 := J.mul_nonsing_inv ((isUnit_iff_isUnit_det _).mp hUnit)
  have hR : Q * J = 1 := J.nonsing_inv_mul ((isUnit_iff_isUnit_det _).mp hUnit)
  let X := F * Q ^ 2 * G
  change IsGroupInverse (F * G) X
  have hAX : (F * G) * X = F * Q * G := calc
    (F * G) * X = F * (J * Q) * Q * G := by
      dsimp only [X, J]
      simp only [pow_two, Matrix.mul_assoc]
    _ = _ := by rw [hL, Matrix.mul_one]
  have hXA : X * (F * G) = F * Q * G := calc
    X * (F * G) = F * Q * (Q * J) * G := by
      dsimp only [X, J]
      simp only [pow_two, Matrix.mul_assoc]
    _ = _ := by rw [hR, Matrix.mul_one]
  refine isGroupInverse_iff.mpr ⟨hAX.trans hXA.symm, ?_, ?_⟩
  · calc
      (F * G) * X * (F * G) = F * (Q * J) * G := by
        rw [hAX]
        dsimp only [J]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR, Matrix.mul_one]
  · calc
      X * (F * G) * X = F * (Q * J) * Q ^ 2 * G := by
        rw [hXA]
        dsimp only [X, J]
        simp only [Matrix.mul_assoc]
      _ = X := by rw [hR, Matrix.mul_one]

private theorem rank_square_factor [Fintype k] (F : Matrix n k ℂ) (G : Matrix k n ℂ)
    (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k) :
    ((F * G) ^ 2).rank = (G * F).rank := by
  have h : (F * G) ^ 2 = F * (G * F) * G := by
    simp only [pow_two, Matrix.mul_assoc]
  rw [h, Chapter01.exercise_7 F (G * F) G hF hG]

/-- **Theorem 2** of [benIsrael2003generalized], Chapter 4. A square matrix has
a group inverse exactly when its index is one, in which case the inverse is unique. -/
theorem theorem_4_2 (A : Matrix n n ℂ) :
    (∃! X, IsGroupInverse A X) ↔ matrixIndex A = 1 := by
  constructor
  · rintro ⟨X, hX, _⟩
    have hle := (theorem_4_1_solvable A Nat.one_pos).mp ⟨X, hX.stable⟩
    have hpos := A.rankStabilizationIndex_spec.1
    exact le_antisymm hle hpos
  · intro hidx
    obtain ⟨F, G, hFG⟩ := (rank_le_iff_exists_mul A A.rank).mp le_rfl
    have hFG_rank : (F * G).rank = A.rank := congrArg rank hFG.symm
    have hcard : Fintype.card (Fin A.rank) = (F * G).rank :=
      (Fintype.card_fin _).trans hFG_rank.symm
    have hF : F.rank = Fintype.card (Fin A.rank) :=
      le_antisymm F.rank_le_card_width (hcard.le.trans (rank_mul_le_left _ _))
    have hG : G.rank = Fintype.card (Fin A.rank) :=
      le_antisymm G.rank_le_card_height (hcard.le.trans (rank_mul_le_right _ _))
    have hA₂ := (A.rank_pow_eq_succ_iff Nat.one_pos).mpr hidx.le
    have hUnit : IsUnit (G * F) := by
      apply isUnit_of_rank_eq_card
      calc
        (G * F).rank = ((F * G) ^ 2).rank := (rank_square_factor F G hF hG).symm
        _ = (A ^ 2).rank := congrArg (fun B : Matrix n n ℂ => (B ^ 2).rank) hFG.symm
        _ = A.rank := by simpa only [pow_one] using hA₂.symm
        _ = _ := (Fintype.card_fin _).symm
    let X := F * (G * F)⁻¹ ^ 2 * G
    have hX : IsGroupInverse A X := hFG ▸ groupInverseFormula F G hUnit
    exact ⟨X, hX, fun Y hY => hY.unique hX⟩

/-- **Theorem 3** of [benIsrael2003generalized], Chapter 4. For a full-rank factorization
$A=FG$, the group inverse exists precisely when $GF$ is nonsingular, and then it is
$F(GF)^{-2}G$. -/
theorem theorem_4_3 [Fintype k] [DecidableEq k] (F : Matrix n k ℂ) (G : Matrix k n ℂ)
    (hF : F.rank = Fintype.card k) (hG : G.rank = Fintype.card k) (X : Matrix n n ℂ) :
    IsGroupInverse (F * G) X ↔ IsUnit (G * F) ∧ X = F * (G * F)⁻¹ ^ 2 * G := by
  constructor
  · intro hX
    have hle := (theorem_4_1_solvable (F * G) Nat.one_pos).mp ⟨X, hX.stable⟩
    have hRank := ((F * G).rank_pow_eq_succ_iff Nat.one_pos).mpr hle
    have hFG := Chapter01.exercise_7 F (1 : Matrix k k ℂ) G hF hG
    rw [Matrix.mul_one, rank_one] at hFG
    have hUnit : IsUnit (G * F) := by
      apply isUnit_of_rank_eq_card
      rw [← rank_square_factor F G hF hG, ← hFG]
      simpa only [pow_one] using hRank.symm
    exact ⟨hUnit, hX.unique (groupInverseFormula F G hUnit)⟩
  · rintro ⟨hUnit, rfl⟩
    exact groupInverseFormula F G hUnit

/-- A square matrix is range-Hermitian exactly when it commutes with its
Moore–Penrose inverse. -/
theorem rangeHermitian_iff_commute_pinv (A : Matrix n n ℂ) :
    IsRangeHermitian A ↔ Commute A A.pinv := by
  have h₁ := A.mul_pinv_eq_starProjection
  have h₂ := A.pinv_mul_eq_starProjection
  constructor
  · intro hrange
    have hmap : toEuclideanLin (A * A.pinv) = toEuclideanLin (A.pinv * A) := by
      rw [h₁, h₂]
      exact congrArg (fun S : Submodule ℂ (EuclideanSpace ℂ n) =>
        (S.starProjection : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)) hrange
    exact toEuclideanLin.injective hmap
  · intro hc
    have h : LinearMap.range (toEuclideanLin (A * A.pinv)) =
        LinearMap.range (toEuclideanLin (A.pinv * A)) := by rw [hc.eq]
    rw [h₁, h₂, Submodule.range_starProjection, Submodule.range_starProjection] at h
    exact h

/-- **Theorem 4** of [benIsrael2003generalized], Chapter 4. An existing group inverse
equals the Moore–Penrose inverse exactly when $A$ is range-Hermitian. -/
theorem theorem_4_4 {A X : Matrix n n ℂ} (hX : IsGroupInverse A X) :
    X = A.pinv ↔ IsRangeHermitian A := by
  rw [rangeHermitian_iff_commute_pinv]
  exact ⟨fun he => he ▸ hX.commute, fun hc =>
    hX.unique (isGroupInverse_iff.mpr ⟨hc, A.mul_pinv_mul_self, A.pinv_mul_self_mul_pinv⟩)⟩

end BenIsraelGreville.Chapter04
