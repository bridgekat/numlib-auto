/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.RingTheory.Nilpotent.Basic
import Numlib.LinearAlgebra.Matrix.Block

/-!
# Existence of reduced row-echelon form

A rectangular matrix over a field can be put in reduced row-echelon form by
left multiplication by an invertible matrix. The proof processes the columns
from left to right, reducing the trailing submatrix after each nonzero pivot.
-/

namespace Matrix

variable {K : Type*} [Field K] {m n : ℕ}

private theorem isUnit_one_sub_vecMulVec (x y : Fin m → K) (h : y ⬝ᵥ x = 0) :
    IsUnit (1 - vecMulVec x y) := by
  apply IsNilpotent.isUnit_one_sub
  refine ⟨2, ?_⟩
  rw [pow_two, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

private theorem isLeadingEntry_succ_iff_of_zero {A : Matrix (Fin m) (Fin (n + 1)) K}
    {i : Fin m} {j : Fin n} (hi : A i 0 = 0) :
    A.IsLeadingEntry i j.succ ↔ (A.submatrix id Fin.succ).IsLeadingEntry i j := by
  constructor
  · intro h
    exact ⟨fun k hk => h.1 k.succ (Fin.succ_lt_succ_iff.mpr hk), h.2⟩
  · intro h
    refine ⟨?_, h.2⟩
    intro k hk
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
    · exact hi
    · exact h.1 k (Fin.succ_lt_succ_iff.mp hk)

private theorem isReducedRowEchelon_of_zero_first_col {A : Matrix (Fin m) (Fin (n + 1)) K}
    (h0 : ∀ i, A i 0 = 0) (ht : (A.submatrix id Fin.succ).IsReducedRowEchelon) :
    A.IsReducedRowEchelon := by
  constructor
  · intro i₁ i₂ hi j hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact h0 i₂
    · exact ht.isRowEchelon hi fun k hk => hj _ (Fin.succ_lt_succ_iff.mpr hk)
  · intro i j hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact (hj.2 (h0 i)).elim
    · exact ht.eq_one ((isLeadingEntry_succ_iff_of_zero (h0 i)).mp hj)
  · intro i₁ i₂ j hi hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact h0 i₁
    · exact ht.eq_zero hi ((isLeadingEntry_succ_iff_of_zero (h0 i₂)).mp hj)

private theorem exists_first_pivot (A : Matrix (Fin (m + 1)) (Fin n) K) (c : Fin n)
    (i : Fin (m + 1)) (hi : A i c ≠ 0) :
    ∃ E : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit E ∧
      (E * A) 0 c = 1 ∧ ∀ j : Fin m, (E * A) j.succ c = 0 := by
  let S := swap K 0 i
  let D := rowScale (0 : Fin (m + 1)) (A i c)⁻¹
  let B := D * (S * A)
  have hS : IsUnit S := ⟨GeneralLinearGroup.swap K 0 i, rfl⟩
  have hD : IsUnit D :=
    ⟨GeneralLinearGroup.rowScale 0 (Units.mk0 _ (inv_ne_zero hi)), rfl⟩
  have hb : B 0 c = 1 := by
    simp [B, D, S, rowScale_mul, Matrix.row_apply, hi]
  let u : Fin (m + 1) → K := Fin.cons 0 fun j => B j.succ c
  let e : Fin (m + 1) → K := Pi.single 0 1
  let L := 1 - vecMulVec u e
  have hL : IsUnit L := isUnit_one_sub_vecMulVec u e (by simp [e, u, single_dotProduct])
  have hEntry (j k) : (L * B) j k = B j k - u j * B 0 k := by
    dsimp only [L, e]
    rw [Matrix.sub_mul, Matrix.one_mul, vecMulVec_mul, single_one_vecMul,
      Matrix.sub_apply, vecMulVec_apply, Matrix.row_apply]
  refine ⟨L * (D * S), hL.mul (hD.mul hS), ?_⟩
  simp only [Matrix.mul_assoc]
  exact ⟨by rw [hEntry]; simp [u, hb], fun j => by rw [hEntry]; simp [u, hb]⟩

private theorem isUnit_consDiag (E : Matrix (Fin m) (Fin m) K) (hE : IsUnit E) :
    IsUnit (consDiag 1 E) := by
  obtain ⟨U, rfl⟩ := hE
  apply isUnit_iff_exists_inv.mpr
  exact ⟨consDiag 1 U.inv, by rw [consDiag_mul_consDiag, Units.val_inv, mul_one, consDiag_one]⟩

private theorem leadingEntry_succ_succ_iff {A : Matrix (Fin (m + 1)) (Fin (n + 1)) K}
    {i : Fin m} {j : Fin n} (h0 : A i.succ 0 = 0) :
    A.IsLeadingEntry i.succ j.succ ↔ (A.submatrix Fin.succ Fin.succ).IsLeadingEntry i j :=
  isLeadingEntry_succ_iff_of_zero (A := A) h0

private theorem isReducedRowEchelon_of_first_pivot
    {A : Matrix (Fin (m + 1)) (Fin (n + 1)) K} (h00 : A 0 0 = 1)
    (h0 : ∀ i : Fin m, A i.succ 0 = 0)
    (ht : (A.submatrix Fin.succ Fin.succ).IsReducedRowEchelon)
    (hAbove : ∀ (i : Fin m) (j : Fin n),
      (A.submatrix Fin.succ Fin.succ).IsLeadingEntry i j → A 0 j.succ = 0) :
    A.IsReducedRowEchelon := by
  constructor
  · intro i₁ i₂ hi j hj
    obtain ⟨i₂, rfl⟩ := Fin.eq_zero_or_eq_succ i₂ |>.resolve_left
      (fun hi₂ => Fin.not_lt_zero i₁ (hi₂ ▸ hi))
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · exact h0 i₂
    · rcases Fin.eq_zero_or_eq_succ i₁ with rfl | ⟨i₁, rfl⟩
      · exact (one_ne_zero (h00.symm.trans (hj 0 (Fin.succ_pos j)))).elim
      · exact ht.isRowEchelon (Fin.succ_lt_succ_iff.mp hi)
          fun k hk => hj _ (Fin.succ_lt_succ_iff.mpr hk)
  · intro i j h
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · have hp : A.IsLeadingEntry 0 0 := ⟨fun k hk => (Fin.not_lt_zero k hk).elim,
        h00.trans_ne one_ne_zero⟩
      rwa [h.unique hp]
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · exact (h.2 (h0 i)).elim
      · exact ht.eq_one ((leadingEntry_succ_succ_iff (h0 i)).mp h)
  · intro i₁ i₂ j hi hj
    obtain ⟨i₂, rfl⟩ := Fin.eq_zero_or_eq_succ i₂ |>.resolve_left
      (fun hi₂ => Fin.not_lt_zero i₁ (hi₂ ▸ hi))
    obtain ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ j |>.resolve_left
      (fun hj0 => hj.2 (hj0 ▸ h0 i₂))
    have hp := (leadingEntry_succ_succ_iff (h0 i₂)).mp hj
    rcases Fin.eq_zero_or_eq_succ i₁ with rfl | ⟨i₁, rfl⟩
    · exact hAbove i₂ j hp
    · exact ht.eq_zero (Fin.succ_lt_succ_iff.mp hi) hp

private theorem exists_clear_above_pivots (A : Matrix (Fin (m + 1)) (Fin (n + 1)) K)
    (h0 : ∀ i : Fin m, A i.succ 0 = 0)
    (ht : (A.submatrix Fin.succ Fin.succ).IsReducedRowEchelon) :
    ∃ L : Matrix (Fin (m + 1)) (Fin (m + 1)) K, IsUnit L ∧
      (L * A) 0 0 = A 0 0 ∧
      (∀ (i : Fin m) j, (L * A) i.succ j = A i.succ j) ∧
      ∀ (i : Fin m) (j : Fin n),
        (A.submatrix Fin.succ Fin.succ).IsLeadingEntry i j → (L * A) 0 j.succ = 0 := by
  classical
  let B := A.submatrix Fin.succ Fin.succ
  let w (i : Fin m) := if h : ∃ c, B.IsLeadingEntry i c then A 0 h.choose.succ else 0
  let v : Fin (m + 1) → K := Fin.cons 0 w
  let e : Fin (m + 1) → K := Pi.single 0 1
  let L := 1 - vecMulVec e v
  have hL : IsUnit L := isUnit_one_sub_vecMulVec e v (by simp [e, v, dotProduct_single])
  have hEntry (i j) : (L * A) i j = A i j - e i * ∑ k, w k * A k.succ j := by
    dsimp only [L]
    rw [Matrix.sub_mul, Matrix.one_mul, vecMulVec_mul, Matrix.sub_apply, vecMulVec_apply]
    simp [vecMul, dotProduct, Fin.sum_univ_succ, v]
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · rw [hEntry]
    simp [h0]
  · intro i j
    rw [hEntry]
    simp [e, Fin.succ_ne_zero]
  · intro i j hj
    have hw : w i = A 0 j.succ := by
      have h : ∃ c, B.IsLeadingEntry i c := ⟨j, hj⟩
      dsimp only [w]
      rw [dite_eq_left h, h.choose_spec.unique hj]
    have hsum : ∑ k, w k * A k.succ j.succ = A 0 j.succ := by
      rw [Finset.sum_eq_single i]
      · rw [hw, show A i.succ j.succ = 1 from ht.eq_one hj, mul_one]
      · intro k _ hki
        rw [show A k.succ j.succ = 0 from ht.eq_zero_of_ne_of_isLeadingEntry hki hj, mul_zero]
      · simp
    rw [hEntry, hsum]
    simp [e]

/-- A finite rectangular matrix over a field admits reduced row-echelon form
by an invertible row transformation. -/
theorem exists_isUnit_mul_isReducedRowEchelon (A : Matrix (Fin m) (Fin n) K) :
    ∃ E : Matrix (Fin m) (Fin m) K, IsUnit E ∧ (E * A).IsReducedRowEchelon := by
  induction n generalizing m with
  | zero =>
    refine ⟨1, isUnit_one, ⟨?_, ?_, ?_⟩⟩
    · intro _ _ _ j
      exact Fin.elim0 j
    · intro _ j
      exact Fin.elim0 j
    · intro _ _ j
      exact Fin.elim0 j
  | succ n ih =>
    by_cases hcol : ∀ i, A i 0 = 0
    · obtain ⟨E, hE, he⟩ := ih (A.submatrix id Fin.succ)
      refine ⟨E, hE, isReducedRowEchelon_of_zero_first_col ?_ ?_⟩
      · intro i
        simp [Matrix.mul_apply, hcol]
      · exact he
    · obtain ⟨i, hi⟩ := not_forall.mp hcol
      cases m with
      | zero => exact Fin.elim0 i
      | succ m =>
        obtain ⟨E, hE, h00, h0⟩ := exists_first_pivot A 0 i hi
        let B := E * A
        obtain ⟨P, hP, hp⟩ := ih (B.submatrix Fin.succ Fin.succ)
        let P' := consDiag 1 P
        let C := P' * B
        have hTop (j) : C 0 j = B 0 j := by
          simp [C, P', Matrix.mul_apply, Fin.sum_univ_succ]
        have hBottom (i : Fin m) (j : Fin (n + 1)) :
            C i.succ j = ∑ k, P i k * B k.succ j := by
          simp [C, P', Matrix.mul_apply, Fin.sum_univ_succ]
        have hC0 (i : Fin m) : C i.succ 0 = 0 := by
          rw [hBottom]
          simp [B, h0]
        have hCt : (C.submatrix Fin.succ Fin.succ).IsReducedRowEchelon := by
          convert hp using 1
          ext i j
          exact hBottom i j.succ
        obtain ⟨L, hL, hNew00, hNewBottom, hAbove⟩ := exists_clear_above_pivots C hC0 hCt
        have hTail : (L * C).submatrix Fin.succ Fin.succ = C.submatrix Fin.succ Fin.succ := by
          ext i j
          exact hNewBottom i j.succ
        refine ⟨L * (P' * E), hL.mul ((isUnit_consDiag _ hP).mul hE), ?_⟩
        simp only [Matrix.mul_assoc]
        apply isReducedRowEchelon_of_first_pivot
        · exact hNew00.trans ((hTop 0).trans h00)
        · exact fun i => (hNewBottom i 0).trans (hC0 i)
        · exact hTail.symm ▸ hCt
        · intro i j hj
          exact hAbove i j (hTail ▸ hj)

end Matrix
