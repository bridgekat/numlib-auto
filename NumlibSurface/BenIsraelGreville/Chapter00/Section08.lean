/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Swap
import Numlib.LinearAlgebra.Matrix.SVD

/-!
# The Smith normal form

Section 0.8 of [benIsrael2003generalized] studies equivalence by integral
matrix units and the rectangular diagonal form with a chain of invariant factors.

## Deviations from the source

* **Exercise 83** (correction). In size $1\times 1$, the matrices $[1]$ and
  $[-1]$ are equivalent. Swaps and additions of another row or column leave
  their entries unchanged.
-/

namespace BenIsraelGreville.Chapter00

open Matrix

section Equivalence

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Section 0.8** of [benIsrael2003generalized]. An integral unit has a
two-sided inverse in the same integral matrix ring. -/
theorem isIntegralUnit_iff (A : Matrix n n ℤ) :
    IsUnit A ↔ ∃ B : Matrix n n ℤ, A * B = 1 ∧ B * A = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨↑u⁻¹, u.mul_inv, u.inv_mul⟩
  · rintro ⟨B, hAB, hBA⟩
    exact ⟨⟨A, B, hAB, hBA⟩, rfl⟩

/-- **Equation (132)** of [benIsrael2003generalized], Chapter 0. Integral
equivalence is multiplication by integral units on both sides. -/
def equivalentOverIntegers (A B : Matrix m n ℤ) : Prop :=
  ∃ (P : (Matrix m m ℤ)ˣ) (Q : (Matrix n n ℤ)ˣ), (P : Matrix m m ℤ) * A * Q.val = B

/-- Every integral matrix is equivalent to itself. -/
theorem equivalentOverIntegers.refl (A : Matrix m n ℤ) : equivalentOverIntegers A A :=
  ⟨1, 1, by simp⟩

/-- Integral equivalence is transitive. -/
theorem equivalentOverIntegers.trans {A B C : Matrix m n ℤ}
    (hAB : equivalentOverIntegers A B) (hBC : equivalentOverIntegers B C) :
    equivalentOverIntegers A C := by
  obtain ⟨P, Q, hP⟩ := hAB
  obtain ⟨U, V, hU⟩ := hBC
  refine ⟨U * P, Q * V, ?_⟩
  rw [← hU, ← hP]
  simp only [Units.val_mul, Matrix.mul_assoc]

/-- Integral equivalence is symmetric. -/
theorem equivalentOverIntegers.symm {A B : Matrix m n ℤ}
    (h : equivalentOverIntegers A B) : equivalentOverIntegers B A := by
  obtain ⟨P, Q, h⟩ := h
  refine ⟨P⁻¹, Q⁻¹, ?_⟩
  rw [← h, ← Matrix.mul_assoc (↑P⁻¹ : Matrix m m ℤ), ← Matrix.mul_assoc (↑P⁻¹ : Matrix m m ℤ),
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

private theorem equivalentOverIntegers.of_isUnit {A : Matrix m n ℤ}
    (P : Matrix m m ℤ) (Q : Matrix n n ℤ) (hP : IsUnit P) (hQ : IsUnit Q) :
    equivalentOverIntegers A (P * A * Q) := by
  obtain ⟨P, rfl⟩ := hP
  obtain ⟨Q, rfl⟩ := hQ
  exact ⟨P, Q, rfl⟩

/-- Multiplication by integral units preserves rank. -/
theorem equivalentOverIntegers.rank_eq {A B : Matrix m n ℤ}
    (h : equivalentOverIntegers A B) : A.rank = B.rank := by
  obtain ⟨P, Q, rfl⟩ := h
  rw [rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).mp Q.isUnit),
    rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).mp P.isUnit)]

private theorem equivalentOverIntegers.dvd_entry {A B : Matrix m n ℤ}
    (h : equivalentOverIntegers A B) {d : ℤ} (hA : ∀ i j, d ∣ A i j) :
    ∀ i j, d ∣ B i j := by
  obtain ⟨P, Q, rfl⟩ := h
  intro i j
  rw [Matrix.mul_apply]
  apply Finset.dvd_sum
  intro k _
  apply dvd_mul_of_dvd_left
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (hA l k) _

end Equivalence

section SmithForm

variable {m n : ℕ}

/-- **Section 0.8** of [benIsrael2003generalized]. A Smith normal form has
nonzero diagonal entries in its first $r$ positions and a divisibility
chain along those entries. -/
def IsSmithNormalForm (S : Matrix (Fin m) (Fin n) ℤ) (r : ℕ) : Prop :=
  ∃ (d : ℕ → ℤ), r ≤ min m n ∧ S = Matrix.rectDiagonal d ∧
    (∀ i < r, d i ≠ 0) ∧ (∀ i, r ≤ i → d i = 0) ∧ (∀ i, i + 1 < r → d i ∣ d (i + 1))

/-- The nonzero diagonal entries of a Smith normal form, in order. -/
def smithInvariantFactors (S : Matrix (Fin m) (Fin n) ℤ) (r : ℕ)
    (hr : r ≤ min m n) (i : Fin r) : ℤ :=
  S (Fin.castLE (hr.trans (min_le_left _ _)) i) (Fin.castLE (hr.trans (min_le_right _ _)) i)

private theorem exists_minimal_pivot {A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ} (hA : A ≠ 0) :
    ∃ B, equivalentOverIntegers A B ∧ B 0 0 ≠ 0 ∧
      ∀ C, equivalentOverIntegers A C → ∀ i j, C i j ≠ 0 →
        (B 0 0).natAbs ≤ (C i j).natAbs := by
  classical
  let admissible (d : ℕ) := ∃ (B : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (i : Fin (m + 1)) (j : Fin (n + 1)),
      equivalentOverIntegers A B ∧ B i j ≠ 0 ∧ (B i j).natAbs = d
  have hnz : ∃ i j, A i j ≠ 0 := by
    by_contra! h
    exact hA (Matrix.ext h)
  have hex : ∃ d, admissible d := by
    obtain ⟨i, j, hij⟩ := hnz
    exact ⟨_, A, i, j, equivalentOverIntegers.refl _, hij, rfl⟩
  obtain ⟨B, i, j, hB, hij, hmin⟩ := Nat.find_spec hex
  let P := Matrix.GeneralLinearGroup.swap ℤ 0 i
  let Q := Matrix.GeneralLinearGroup.swap ℤ 0 j
  let C := P.val * B * Q.val
  have hc : C 0 0 = B i j := by
    change (Matrix.swap ℤ 0 i * B * Matrix.swap ℤ 0 j) 0 0 = B i j
    rw [mul_swap_apply_left, swap_mul_apply_left]
  refine ⟨C, hB.trans ⟨P, Q, rfl⟩, by simpa only [hc] using hij, ?_⟩
  intro D hD i' j' hn
  rw [hc, hmin]
  exact Nat.find_min' hex ⟨D, i', j', hD, hn, rfl⟩

private theorem natAbs_emod_lt {a b : ℤ} (hb : b ≠ 0) :
    (a % b).natAbs < b.natAbs := by
  have h := Int.emod_lt_abs a hb
  rwa [← Int.natAbs_of_nonneg (Int.emod_nonneg a hb), Int.abs_eq_natAbs,
    Int.ofNat_lt] at h

private theorem isUnit_transvection_int {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (b : ℤ) : IsUnit (Matrix.transvection i j b) := by
  rw [isUnit_iff_isUnit_det, Matrix.det_transvection_of_ne i j hij]
  exact isUnit_one

private theorem minimal_pivot_dvd_first_row_col
    {A B : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ}
    (hB : equivalentOverIntegers A B) (hb : B 0 0 ≠ 0)
    (hmin : ∀ C, equivalentOverIntegers A C → ∀ i j, C i j ≠ 0 →
      (B 0 0).natAbs ≤ (C i j).natAbs) :
    (∀ i, B 0 0 ∣ B i 0) ∧ ∀ j, B 0 0 ∣ B 0 j := by
  constructor
  · intro i
    rcases eq_or_ne i 0 with rfl | hi
    · exact dvd_refl _
    · let T := Matrix.transvection i 0 (-(B i 0 / B 0 0))
      have hC : equivalentOverIntegers A (T * B) := by
        have hE := equivalentOverIntegers.of_isUnit (A := B) T 1
          (isUnit_transvection_int i 0 hi _) isUnit_one
        simpa only [Matrix.mul_one] using hB.trans hE
      have hE : (T * B) i 0 = B i 0 % B 0 0 := by
        dsimp only [T]
        rw [Matrix.transvection_mul_apply_same, neg_mul]
        linarith only [Int.emod_add_ediv_mul (B i 0) (B 0 0)]
      apply Int.dvd_of_emod_eq_zero
      by_contra hn
      have h := hmin _ hC i 0 (fun hz => hn (hE.symm.trans hz))
      rw [hE] at h
      exact (not_lt_of_ge h) (natAbs_emod_lt hb)
  · intro j
    rcases eq_or_ne j 0 with rfl | hj
    · exact dvd_refl _
    · let T := Matrix.transvection 0 j (-(B 0 j / B 0 0))
      have hC : equivalentOverIntegers A (B * T) := by
        have hE := equivalentOverIntegers.of_isUnit (A := B) 1 T
          isUnit_one (isUnit_transvection_int 0 j hj.symm _)
        simpa only [Matrix.one_mul] using hB.trans hE
      have hE : (B * T) 0 j = B 0 j % B 0 0 := by
        dsimp only [T]
        rw [Matrix.mul_transvection_apply_same, neg_mul]
        linarith only [Int.emod_add_ediv_mul (B 0 j) (B 0 0)]
      apply Int.dvd_of_emod_eq_zero
      by_contra hn
      have h := hmin _ hC 0 j (fun hz => hn (hE.symm.trans hz))
      rw [hE] at h
      exact (not_lt_of_ge h) (natAbs_emod_lt hb)

private theorem isUnit_one_add_vecMulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℤ) (hxy : y ⬝ᵥ x = 0) : IsUnit (1 + vecMulVec x y) := by
  let N := vecMulVec x y
  have hN : N * N = 0 := by
    dsimp only [N]
    rw [vecMulVec_mul_vecMulVec, hxy, zero_smul, vecMulVec_zero]
  apply isUnit_iff_exists_inv.mpr
  refine ⟨1 - N, ?_⟩
  change (1 + N) * (1 - N) = 1
  calc
    (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
    _ = 1 := by rw [hN, sub_zero]

/-- A nonzero integer matrix has an equivalent form with a nonzero leading
entry, zeros in its first row and column away from the leading entry, and a
leading entry that divides every other entry. -/
theorem exists_cleared_smithPivot {A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ} (hA : A ≠ 0) :
    ∃ B, equivalentOverIntegers A B ∧ B 0 0 ≠ 0 ∧
      (∀ i : Fin m, B i.succ 0 = 0) ∧ (∀ j : Fin n, B 0 j.succ = 0) ∧
      ∀ i j, B 0 0 ∣ B i j := by
  obtain ⟨B, hB, hb, hmin⟩ := exists_minimal_pivot hA
  obtain ⟨hcol, hrow⟩ := minimal_pivot_dvd_first_row_col hB hb hmin
  let u (i : Fin (m + 1)) := if i = 0 then 0 else -(B i 0 / B 0 0)
  let v (j : Fin (n + 1)) := if j = 0 then 0 else -(B 0 j / B 0 0)
  let em : Fin (m + 1) → ℤ := Pi.single 0 1
  let en : Fin (n + 1) → ℤ := Pi.single 0 1
  let L := 1 + vecMulVec u em
  let R := 1 + vecMulVec en v
  let C := L * B * R
  have hL : IsUnit L := isUnit_one_add_vecMulVec u em (by simp [em, u, single_dotProduct])
  have hR : IsUnit R := isUnit_one_add_vecMulVec en v (by simp [en, v, dotProduct_single])
  have hC : equivalentOverIntegers A C := hB.trans (equivalentOverIntegers.of_isUnit L R hL hR)
  have hLeft (i j) : (L * B) i j = B i j + u i * B 0 j := by
    dsimp only [L, em]
    rw [Matrix.add_mul, Matrix.one_mul, vecMulVec_mul, single_one_vecMul, Matrix.add_apply,
      vecMulVec_apply, Matrix.row_apply]
  have hRight (i j) : C i j = (L * B) i j + (L * B) i 0 * v j := by
    dsimp only [C, R, en]
    rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, mulVec_single_one, Matrix.add_apply,
      vecMulVec_apply, Matrix.col_apply]
  have hCCol (i : Fin (m + 1)) : C i 0 = if i = 0 then B 0 0 else 0 := by
    rw [hRight, hLeft]
    simp only [v, ite_eq_left rfl, mul_zero, add_zero]
    rcases eq_or_ne i 0 with rfl | hi
    · simp [u]
    · simp only [u, ite_eq_right hi, neg_mul]
      have he := Int.emod_add_ediv_mul (B i 0) (B 0 0)
      rw [Int.emod_eq_zero_of_dvd (hcol i), zero_add] at he
      linarith
  have hCRow (j : Fin (n + 1)) : C 0 j = if j = 0 then B 0 0 else 0 := by
    rw [hRight, hLeft 0 j, hLeft 0 0]
    simp only [u, ite_eq_left rfl, zero_mul, add_zero]
    rcases eq_or_ne j 0 with rfl | hj
    · simp [v]
    · simp only [v, ite_eq_right hj, mul_comm (B 0 0)]
      have he := Int.emod_add_ediv_mul (B 0 j) (B 0 0)
      rw [Int.emod_eq_zero_of_dvd (hrow j), zero_add] at he
      linarith
  have h00 : C 0 0 = B 0 0 := by simp [hCCol]
  refine ⟨C, hC, by rwa [h00], fun i => by simp [hCCol],
    fun j => by simp [hCRow], ?_⟩
  intro i j
  rcases eq_or_ne i 0 with rfl | hi
  · rw [h00, hCRow]
    split_ifs <;> simp
  · rcases eq_or_ne j 0 with rfl | hj
    · rw [hCCol i, ite_eq_right hi]
      exact dvd_zero _
    · let T := Matrix.transvection 0 i (1 : ℤ)
      let D := T * C
      have hD : equivalentOverIntegers A D := by
        have hCD := equivalentOverIntegers.of_isUnit (A := C) T 1
          (isUnit_transvection_int 0 i hi.symm 1) isUnit_one
        simpa only [D, Matrix.mul_one] using hC.trans hCD
      have hD00 : D 0 0 = B 0 0 := by
        dsimp only [D, T]
        rw [Matrix.transvection_mul_apply_same, hCCol i, ite_eq_right hi, h00]
        simp
      have hD0j : D 0 j = C i j := by
        dsimp only [D, T]
        rw [Matrix.transvection_mul_apply_same, hCRow, ite_eq_right hj, one_mul, zero_add]
      have hMinD : ∀ E, equivalentOverIntegers A E → ∀ i j, E i j ≠ 0 →
          (D 0 0).natAbs ≤ (E i j).natAbs := by
        simpa only [hD00] using hmin
      have hd := (minimal_pivot_dvd_first_row_col hD (by rwa [hD00]) hMinD).2 j
      rwa [hD00, hD0j, ← h00] at hd

/-- A cleared Smith pivot is a greatest common divisor of the original
entries, characterized by its divisors. -/
theorem exists_smithPivot_gcd {A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ} (hA : A ≠ 0) :
    ∃ B, equivalentOverIntegers A B ∧ B 0 0 ≠ 0 ∧
      (∀ i : Fin m, B i.succ 0 = 0) ∧ (∀ j : Fin n, B 0 j.succ = 0) ∧
      ∀ d, (∀ i j, d ∣ A i j) ↔ d ∣ B 0 0 := by
  obtain ⟨B, hB, h0, hcol, hrow, hdiv⟩ := exists_cleared_smithPivot hA
  refine ⟨B, hB, h0, hcol, hrow, fun d => ?_⟩
  exact ⟨fun hd => hB.dvd_entry hd 0 0,
    fun hd => hB.symm.dvd_entry (fun i j => hd.trans (hdiv i j))⟩

private def firstAndTail (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) :=
  finSumFinEquiv.trans (finCongr (Nat.one_add n))

@[simp] private theorem firstAndTail_zero (n : ℕ) : (firstAndTail n) (Sum.inl 0) = 0 := by
  apply Fin.ext
  rfl

@[simp] private theorem firstAndTail_succ (i : Fin n) :
    (firstAndTail n) (Sum.inr i) = i.succ := by
  apply Fin.ext
  change 1 + i.val = i.val + 1
  omega

@[simp] private theorem firstAndTail_symm_zero (n : ℕ) :
    (firstAndTail n).symm 0 = Sum.inl 0 :=
  (Equiv.symm_apply_eq _).mpr (firstAndTail_zero n).symm

@[simp] private theorem firstAndTail_symm_succ (i : Fin n) :
    (firstAndTail n).symm i.succ = Sum.inr i :=
  (Equiv.symm_apply_eq _).mpr (firstAndTail_succ i).symm

private def prependDiagonalEntry (a : ℤ) (B : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ :=
  (fromBlocks (Matrix.of (fun _ _ : Fin 1 => a)) 0 0 B).reindex (firstAndTail m) (firstAndTail n)

private theorem eq_prependDiagonalEntry_of_cleared (B : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (hcol : ∀ i : Fin m, B i.succ 0 = 0) (hrow : ∀ j : Fin n, B 0 j.succ = 0) :
    B = prependDiagonalEntry (B 0 0) (B.submatrix Fin.succ Fin.succ) := by
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩ <;>
      simp [prependDiagonalEntry, reindex_apply, fromBlocks, hcol, hrow]

private theorem prependDiagonalEntry_rectDiagonal (a : ℤ) (d : ℕ → ℤ) :
    prependDiagonalEntry a (rectDiagonal d : Matrix (Fin m) (Fin n) ℤ) =
      rectDiagonal (fun i => Nat.casesOn i a d) := by
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩ <;>
      simp [prependDiagonalEntry, reindex_apply, fromBlocks, rectDiagonal_apply]

private theorem isSmithNormalForm_zero (m n : ℕ) : IsSmithNormalForm (0 : Matrix (Fin m) (Fin n) ℤ)
    0 := by
  refine ⟨0, Nat.zero_le _, ?_, by simp, by simp, by simp⟩
  ext
  simp [rectDiagonal_apply]

/-- A Smith normal form with $r$ nonzero diagonal entries has rank $r$. -/
theorem IsSmithNormalForm.rank_eq {S : Matrix (Fin m) (Fin n) ℤ} {r : ℕ}
    (h : IsSmithNormalForm S r) : S.rank = r := by
  obtain ⟨d, hr, rfl, hnz, hz, _⟩ := h
  let im : Fin r ↪ Fin m := Fin.castLEEmb (hr.trans (min_le_left _ _))
  let jn : Fin r ↪ Fin n := Fin.castLEEmb (hr.trans (min_le_right _ _))
  apply le_antisymm
  · let rows : Finset (Fin m) := Finset.univ.map im
    have hc : rows.card = r := by simp [rows]
    rw [← hc]
    apply rank_le_card_of_support_subset
    rw [Function.support_subset_iff']
    intro i hi
    have hi' : r ≤ i.val := by
      by_contra! hlt
      exact hi (Finset.mem_map.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    funext j
    simp [Matrix.row, Matrix.rectDiagonal_apply, hz _ hi']
  · have he : (rectDiagonal d : Matrix (Fin m) (Fin n) ℤ).submatrix im jn =
        diagonal (fun i : Fin r => d i.val) := by
      ext i j
      simp only [submatrix_apply, rectDiagonal_apply, diagonal_apply, im, jn]
      have he : (i : ℕ) = (j : ℕ) ↔ i = j := Fin.ext_iff.symm
      simp only [Fin.castLEEmb_apply, Fin.val_castLE, he]
    have hd : (diagonal (fun i : Fin r => d i.val)).det ≠ 0 := by
      rw [det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hnz i.val i.isLt
    have hEq : (diagonal (fun i : Fin r => d i.val)).rank = r :=
      (rank_of_det_ne_zero hd).trans (Fintype.card_fin r)
    rw [← hEq, ← he]
    exact rank_submatrix_le _ _ _

end SmithForm

section ElementarySteps

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Equations (133)–(134)** of [benIsrael2003generalized], Chapter 0.
An elementary integral step swaps rows or columns, or adds an integer
multiple of one of them to a distinct one. -/
inductive IntegralElementaryStep (A : Matrix m n ℤ) : Matrix m n ℤ → Prop
  | swapRows (i j : m) : IntegralElementaryStep A (Matrix.swap ℤ i j * A)
  | swapCols (i j : n) : IntegralElementaryStep A (A * Matrix.swap ℤ i j)
  | addRow (i j : m) (hne : i ≠ j) (a : ℤ) :
      IntegralElementaryStep A (Matrix.transvection i j a * A)
  | addCol (i j : n) (hne : i ≠ j) (a : ℤ) :
      IntegralElementaryStep A (A * Matrix.transvection i j a)

/-- **Exercise 83** of [benIsrael2003generalized], Chapter 0. A sequence
of the stated elementary operations preserves integral equivalence. -/
theorem equivalentOverIntegers_of_elementarySteps {A B : Matrix m n ℤ}
    (h : Relation.ReflTransGen IntegralElementaryStep A B) : equivalentOverIntegers A B := by
  have hStep {C D : Matrix m n ℤ} (h : IntegralElementaryStep C D) :
      equivalentOverIntegers C D := by
    cases h with
    | swapRows i j =>
        exact ⟨Matrix.GeneralLinearGroup.swap ℤ i j, 1, by simp⟩
    | swapCols i j =>
        exact ⟨1, Matrix.GeneralLinearGroup.swap ℤ i j, by simp⟩
    | addRow i j hij a =>
        simpa only [Matrix.mul_one] using equivalentOverIntegers.of_isUnit (A := C)
          (Matrix.transvection i j a) 1 (isUnit_transvection_int i j hij a) isUnit_one
    | addCol i j hij a =>
        simpa only [Matrix.one_mul] using equivalentOverIntegers.of_isUnit (A := C)
          1 (Matrix.transvection i j a) isUnit_one (isUnit_transvection_int i j hij a)
  induction h with
  | refl => exact equivalentOverIntegers.refl _
  | tail _ h ih => exact ih.trans (hStep h)

/-- **Exercise 83** of [benIsrael2003generalized], Chapter 0.
The converse has a size-one counterexample since changing the sign
of the single entry requires an additional elementary operation. -/
theorem exercise_83_counterexample :
    let A : Matrix (Fin 1) (Fin 1) ℤ := 1
    let B : Matrix (Fin 1) (Fin 1) ℤ := -1
    equivalentOverIntegers A B ∧ ¬Relation.ReflTransGen IntegralElementaryStep A B := by
  intro A B
  constructor
  · exact ⟨-1, 1, by simp [A, B]⟩
  · intro h
    have he {C D : Matrix (Fin 1) (Fin 1) ℤ} (h : IntegralElementaryStep C D) : C = D := by
      cases h with
      | swapRows i j =>
          rw [Subsingleton.elim j i]
          simp [Matrix.swap]
      | swapCols i j =>
          rw [Subsingleton.elim j i]
          simp [Matrix.swap]
      | addRow i j h _ => exact (h (Subsingleton.elim i j)).elim
      | addCol i j h _ => exact (h (Subsingleton.elim i j)).elim
    have key {D : Matrix (Fin 1) (Fin 1) ℤ}
        (hD : Relation.ReflTransGen IntegralElementaryStep A D) : A = D := by
      induction hD with
      | refl => rfl
      | tail _ h ih => exact ih.trans (he h)
    have h00 := congrArg (fun C : Matrix (Fin 1) (Fin 1) ℤ => C 0 0) (key h)
    norm_num [A, B] at h00

end ElementarySteps

section SmithReduction

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private theorem transpose_transvection_int {ι : Type*} [DecidableEq ι] (i j : ι) (c : ℤ) :
    (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by
  simp only [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

private theorem IntegralElementaryStep.transpose {A B : Matrix m n ℤ}
    (h : IntegralElementaryStep A B) : IntegralElementaryStep Aᵀ Bᵀ := by
  cases h with
  | swapRows i j =>
    simpa only [Matrix.transpose_mul, Matrix.transpose_swap] using
      IntegralElementaryStep.swapCols (A := Aᵀ) i j
  | swapCols i j =>
    simpa only [Matrix.transpose_mul, Matrix.transpose_swap] using
      IntegralElementaryStep.swapRows (A := Aᵀ) i j
  | addRow i j hij a =>
    simpa only [Matrix.transpose_mul, transpose_transvection_int] using
      IntegralElementaryStep.addCol (A := Aᵀ) j i hij.symm a
  | addCol i j hij a =>
    simpa only [Matrix.transpose_mul, transpose_transvection_int] using
      IntegralElementaryStep.addRow (A := Aᵀ) j i hij.symm a

private def addRowsFrom (A : Matrix m n ℤ) (p : m) (s : Finset m) (c : m → ℤ) :
    Matrix m n ℤ :=
  Matrix.of fun i j => if i ∈ s then A i j + c i * A p j else A i j

private theorem addRowsFrom_reachable (A : Matrix m n ℤ)
    (p : m) (s : Finset m) (hs : p ∉ s) (c : m → ℤ) :
    Relation.ReflTransGen IntegralElementaryStep A (addRowsFrom A p s c) := by
  induction s using Finset.induction_on with
  | empty =>
    have he : addRowsFrom A p ∅ c = A := Matrix.ext fun i j => by simp [addRowsFrom]
    rw [he]
  | @insert i s hi ih =>
    have hpi : p ≠ i := fun h => hs (h ▸ Finset.mem_insert_self i s)
    have hp : p ∉ s := fun hp => hs (Finset.mem_insert_of_mem hp)
    refine (ih hp).tail ?_
    have he : addRowsFrom A p (insert i s) c =
        Matrix.transvection i p (c i) * addRowsFrom A p s c := by
      ext a b
      by_cases ha : a = i
      · subst a
        simp [addRowsFrom, hp, hi]
      · rw [Matrix.transvection_mul_apply_of_ne i p a b ha]
        simp [addRowsFrom, ha]
    rw [he]
    exact .addRow i p hpi.symm (c i)

private def addColsFrom (A : Matrix m n ℤ) (p : n) (s : Finset n) (c : n → ℤ) :
    Matrix m n ℤ :=
  (addRowsFrom Aᵀ p s c)ᵀ

private theorem addColsFrom_reachable (A : Matrix m n ℤ)
    (p : n) (s : Finset n) (hs : p ∉ s) (c : n → ℤ) :
    Relation.ReflTransGen IntegralElementaryStep A (addColsFrom A p s c) := by
  have h := Relation.ReflTransGen.lift Matrix.transpose
    (fun _ _ h => IntegralElementaryStep.transpose h) _ _ (addRowsFrom_reachable Aᵀ p s hs c)
  simpa only [addColsFrom, Function.onFun, Matrix.transpose_transpose] using h

end SmithReduction

section SmithPivotReduction

variable {m n : ℕ}

private abbrev SmithSteps {m n : ℕ} :=
  Relation.ReflTransGen (IntegralElementaryStep (m := Fin m) (n := Fin n))

/-- A leading Smith entry is cleared when all other entries of its row
and column vanish and it divides every entry of the matrix. -/
def IsClearedSmithPivot (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ) : Prop :=
  A 0 0 ≠ 0 ∧ (∀ i : Fin m, A i.succ 0 = 0) ∧ (∀ j : Fin n, A 0 j.succ = 0) ∧
    ∀ i j, A 0 0 ∣ A i j

private theorem SmithSteps.transpose {A B : Matrix (Fin m) (Fin n) ℤ} (h : SmithSteps A B) :
    SmithSteps Aᵀ Bᵀ :=
  Relation.ReflTransGen.lift (fun C : Matrix (Fin m) (Fin n) ℤ => Cᵀ)
    (fun _ _ hs => IntegralElementaryStep.transpose hs) _ _ h

private theorem exists_row_remainder_pivot (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (i : Fin (m + 1)) (hi : i ≠ 0) :
    ∃ B, SmithSteps A B ∧ B 0 0 = A i 0 % A 0 0 := by
  let k := -(A i 0 / A 0 0)
  let C := Matrix.transvection i 0 k * A
  let B := Matrix.swap ℤ 0 i * C
  refine ⟨B, (Relation.ReflTransGen.single (.addRow i 0 hi k)).tail (.swapRows 0 i), ?_⟩
  change (Matrix.swap ℤ 0 i * C) 0 0 = _
  rw [Matrix.swap_mul_apply_left]
  change (Matrix.transvection i 0 k * A) i 0 = _
  rw [Matrix.transvection_mul_apply_same]
  dsimp only [k]
  linarith only [Int.emod_add_ediv_mul (A i 0) (A 0 0)]

private theorem exists_col_remainder_pivot (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    ∃ B, SmithSteps A B ∧ B 0 0 = A 0 j % A 0 0 := by
  obtain ⟨B, hB, he⟩ := exists_row_remainder_pivot Aᵀ j hj
  exact ⟨Bᵀ, by simpa only [Matrix.transpose_transpose] using hB.transpose, he⟩

private theorem clear_divisible_smith_pivot (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (hcol : ∀ i, A 0 0 ∣ A i 0) (hrow : ∀ j, A 0 0 ∣ A 0 j) :
    ∃ C, SmithSteps A C ∧ C 0 0 = A 0 0 ∧
      (∀ i : Fin m, C i.succ 0 = 0) ∧ ∀ j : Fin n, C 0 j.succ = 0 := by
  let s := (Finset.univ : Finset (Fin (m + 1))).erase 0
  let t := (Finset.univ : Finset (Fin (n + 1))).erase 0
  let f (i : Fin (m + 1)) := -(A i 0 / A 0 0)
  let g (j : Fin (n + 1)) := -(A 0 j / A 0 0)
  let B := addRowsFrom A 0 s f
  let C := addColsFrom B 0 t g
  have hB0 (j) : B 0 j = A 0 j := by simp [B, addRowsFrom, s]
  have hBi (i : Fin m) : B i.succ 0 = 0 := by
    have h := Int.ediv_mul_cancel (hcol i.succ)
    simp [B, addRowsFrom, s, f, Fin.succ_ne_zero, h]
  have hC0 (i) : C i 0 = B i 0 := by simp [C, addColsFrom, addRowsFrom, t]
  have hCj (j : Fin n) : C 0 j.succ = 0 := by
    have h := Int.ediv_mul_cancel (hrow j.succ)
    simp [C, addColsFrom, addRowsFrom, t, g, Fin.succ_ne_zero, hB0, h]
  exact ⟨C, (addRowsFrom_reachable A 0 s (by simp [s]) f).trans
    (addColsFrom_reachable B 0 t (by simp [t]) g),
    (hC0 0).trans (hB0 0), fun i => (hC0 i.succ).trans (hBi i), hCj⟩

/-- One iteration of the Euclidean pivot reduction either clears a
dividing pivot or replaces its magnitude by a strictly smaller nonzero
magnitude. Every transformation is a finite sequence of the source's
elementary row and column operations. -/
theorem smithPivotReduction_step (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (hA : A 0 0 ≠ 0) :
    (∃ C, SmithSteps A C ∧ IsClearedSmithPivot C) ∨
    ∃ C, SmithSteps A C ∧ C 0 0 ≠ 0 ∧ (C 0 0).natAbs < (A 0 0).natAbs := by
  by_cases hc : ∀ i, A 0 0 ∣ A i 0
  · by_cases hr : ∀ j, A 0 0 ∣ A 0 j
    · obtain ⟨C, hC, he, hCcol, hCrow⟩ := clear_divisible_smith_pivot A hc hr
      have hz : C 0 0 ≠ 0 := he ▸ hA
      by_cases hd : ∀ i j, C 0 0 ∣ C i j
      · exact Or.inl ⟨C, hC, hz, hCcol, hCrow, hd⟩
      · push Not at hd
        obtain ⟨i, j, hij⟩ := hd
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
          · exact (hij (dvd_refl _)).elim
          · exact (hij (hCrow j ▸ dvd_zero _)).elim
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · exact (hij (hCcol i ▸ dvd_zero _)).elim
        let D := Matrix.transvection 0 i.succ (1 : ℤ) * C
        have hD : SmithSteps A D := hC.tail (.addRow 0 i.succ i.succ_ne_zero.symm 1)
        have hD0 : D 0 0 = C 0 0 := by
          simp [D, Matrix.transvection_mul_apply_same, hCcol]
        have hDj : D 0 j.succ = C i.succ j.succ := by
          simp [D, Matrix.transvection_mul_apply_same, hCrow]
        obtain ⟨E, hE, hrem⟩ := exists_col_remainder_pivot D j.succ j.succ_ne_zero
        rw [hD0, hDj] at hrem
        apply Or.inr
        refine ⟨E, hD.trans hE, fun h => hij (Int.dvd_of_emod_eq_zero (hrem.symm.trans h)), ?_⟩
        rw [hrem, ← he]
        exact natAbs_emod_lt hz
    · push Not at hr
      obtain ⟨j, hj⟩ := hr
      have hj' : j ≠ 0 := fun he => hj (he ▸ dvd_refl _)
      obtain ⟨C, hC, he⟩ := exists_col_remainder_pivot A j hj'
      refine Or.inr ⟨C, hC, fun h => hj (Int.dvd_of_emod_eq_zero (he.symm.trans h)), ?_⟩
      rw [he]
      exact natAbs_emod_lt hA
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    have hi' : i ≠ 0 := fun he => hi (he ▸ dvd_refl _)
    obtain ⟨C, hC, he⟩ := exists_row_remainder_pivot A i hi'
    refine Or.inr ⟨C, hC, fun h => hi (Int.dvd_of_emod_eq_zero (he.symm.trans h)), ?_⟩
    rw [he]
    exact natAbs_emod_lt hA

/-- Strict decrease of the nonzero leading magnitude gives a finite
trace from any nonzero matrix to a cleared, dividing pivot. -/
theorem smithPivotReduction_terminates (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ)
    (hA : A ≠ 0) : ∃ C, SmithSteps A C ∧ IsClearedSmithPivot C := by
  have reduce (k : ℕ) : ∀ B : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ,
      (B 0 0).natAbs = k → B 0 0 ≠ 0 → ∃ C, SmithSteps B C ∧ IsClearedSmithPivot C := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro B hk hb
      rcases smithPivotReduction_step B hb with h | ⟨C, hBC, hc, hlt⟩
      · exact h
      · rw [hk] at hlt
        obtain ⟨D, hCD, hD⟩ := ih (C 0 0).natAbs hlt C rfl hc
        exact ⟨D, hBC.trans hCD, hD⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra! h
    exact hA (Matrix.ext h)
  let B := Matrix.swap ℤ 0 i * A * Matrix.swap ℤ 0 j
  have hB : SmithSteps A B :=
    (Relation.ReflTransGen.single (.swapRows 0 i)).tail (.swapCols 0 j)
  have hb : B 0 0 ≠ 0 := by
    change (Matrix.swap ℤ 0 i * A * Matrix.swap ℤ 0 j) 0 0 ≠ 0
    rwa [Matrix.mul_swap_apply_left, Matrix.swap_mul_apply_left]
  obtain ⟨C, hC, hc⟩ := reduce (B 0 0).natAbs B rfl hb
  exact ⟨C, hB.trans hC, hc⟩

private theorem transpose_prependDiagonalEntry (a : ℤ) (B : Matrix (Fin m) (Fin n) ℤ) :
    (prependDiagonalEntry a B)ᵀ = prependDiagonalEntry a Bᵀ := by
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩ <;>
      simp [prependDiagonalEntry, reindex_apply, fromBlocks]

private theorem prependDiagonalEntry_swapRows (a : ℤ) (B : Matrix (Fin m) (Fin n) ℤ)
    (i j : Fin m) :
    prependDiagonalEntry a (Matrix.swap ℤ i j * B) =
      Matrix.swap ℤ i.succ j.succ * prependDiagonalEntry a B := by
  ext k l
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
  · rw [Matrix.swap_mul_of_ne i.succ_ne_zero.symm j.succ_ne_zero.symm]
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
      simp [prependDiagonalEntry, reindex_apply, fromBlocks]
  · rcases eq_or_ne k i with rfl | hki
    · rw [Matrix.swap_mul_apply_left]
      rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
        simp [prependDiagonalEntry, reindex_apply, fromBlocks]
    · rcases eq_or_ne k j with rfl | hkj
      · rw [Matrix.swap_mul_apply_right]
        rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
          simp [prependDiagonalEntry, reindex_apply, fromBlocks, Matrix.swap_mul_apply_right]
      · rw [Matrix.swap_mul_of_ne (fun h => hki (Fin.succ_injective _ h))
          (fun h => hkj (Fin.succ_injective _ h))]
        rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
          simp [prependDiagonalEntry, reindex_apply, fromBlocks, Matrix.swap_mul_of_ne hki hkj]

private theorem prependDiagonalEntry_addRow (a : ℤ) (B : Matrix (Fin m) (Fin n) ℤ)
    (i j : Fin m) (c : ℤ) :
    prependDiagonalEntry a (Matrix.transvection i j c * B) =
      Matrix.transvection i.succ j.succ c * prependDiagonalEntry a B := by
  ext k l
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩
  · rw [Matrix.transvection_mul_apply_of_ne i.succ j.succ _ _ i.succ_ne_zero.symm]
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
      simp [prependDiagonalEntry, reindex_apply, fromBlocks]
  · rcases eq_or_ne k i with rfl | hki
    · rw [Matrix.transvection_mul_apply_same]
      rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
        simp [prependDiagonalEntry, reindex_apply, fromBlocks]
    · rw [Matrix.transvection_mul_apply_of_ne i.succ j.succ _ _
        (fun h => hki (Fin.succ_injective _ h))]
      rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
        simp [prependDiagonalEntry, reindex_apply, fromBlocks, Matrix.transvection_mul_apply_of_ne
          i j k _ hki]

private theorem elementaryStep_prependDiagonalEntry (a : ℤ) {B C : Matrix (Fin m) (Fin n) ℤ}
    (h : IntegralElementaryStep B C) : IntegralElementaryStep
      (prependDiagonalEntry a B) (prependDiagonalEntry a C) := by
  cases h with
  | swapRows i j =>
    rw [prependDiagonalEntry_swapRows]
    exact .swapRows i.succ j.succ
  | swapCols i j =>
    have he := (IntegralElementaryStep.swapRows (A := prependDiagonalEntry a Bᵀ) i.succ j.succ)
    rw [← prependDiagonalEntry_swapRows] at he
    have ht := he.transpose
    rwa [transpose_prependDiagonalEntry, transpose_prependDiagonalEntry, Matrix.transpose_mul,
      Matrix.transpose_swap, Matrix.transpose_transpose] at ht
  | addRow i j hij c =>
    rw [prependDiagonalEntry_addRow]
    exact .addRow i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) c
  | addCol i j hij c =>
    have he := (IntegralElementaryStep.addRow (A := prependDiagonalEntry a Bᵀ)
      j.succ i.succ (fun h => hij.symm (Fin.succ_injective _ h)) c)
    rw [← prependDiagonalEntry_addRow] at he
    have ht := he.transpose
    rwa [transpose_prependDiagonalEntry, transpose_prependDiagonalEntry, Matrix.transpose_mul,
      transpose_transvection_int, Matrix.transpose_transpose] at ht

private theorem SmithSteps.prepend (a : ℤ) {B C : Matrix (Fin m) (Fin n) ℤ}
    (h : SmithSteps B C) : SmithSteps (prependDiagonalEntry a B) (prependDiagonalEntry a C) :=
  Relation.ReflTransGen.lift (prependDiagonalEntry a)
    (fun _ _ hs => elementaryStep_prependDiagonalEntry a hs) _ _ h

private theorem exists_smithNormalForm_elementary (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ r S, SmithSteps A S ∧ IsSmithNormalForm S r := by
  induction m generalizing n with
  | zero =>
    have h : A = 0 := Matrix.ext fun i _ => Fin.elim0 i
    subst A
    exact ⟨0, 0, .refl, isSmithNormalForm_zero _ _⟩
  | succ m ih =>
    cases n with
    | zero =>
      have h : A = 0 := Matrix.ext fun _ j => Fin.elim0 j
      subst A
      exact ⟨0, 0, .refl, isSmithNormalForm_zero _ _⟩
    | succ n =>
      by_cases hA : A = 0
      · subst A
        exact ⟨0, 0, .refl, isSmithNormalForm_zero _ _⟩
      obtain ⟨B, hB, hb, hcol, hrow, hdiv⟩ := smithPivotReduction_terminates A hA
      let T := B.submatrix Fin.succ Fin.succ
      obtain ⟨r, S, hTS, d, hr, hS, hnz, hz, hchain⟩ := ih T
      have hB' : B = prependDiagonalEntry (B 0 0) T :=
        eq_prependDiagonalEntry_of_cleared B hcol hrow
      have hBS : SmithSteps B (prependDiagonalEntry (B 0 0) S) :=
        hB' ▸ hTS.prepend (B 0 0)
      have hSdiv := (equivalentOverIntegers_of_elementarySteps hTS).dvd_entry
        (fun i j => hdiv i.succ j.succ)
      refine ⟨r + 1, prependDiagonalEntry (B 0 0) S, hB.trans hBS,
        (fun i => Nat.casesOn i (B 0 0) d), ?_, ?_, ?_, ?_, ?_⟩
      · exact le_min (Nat.succ_le_succ (hr.trans (min_le_left _ _)))
          (Nat.succ_le_succ (hr.trans (min_le_right _ _)))
      · rw [hS, prependDiagonalEntry_rectDiagonal]
      · intro i hi
        cases i with
        | zero => exact hb
        | succ i => exact hnz i (Nat.lt_of_succ_lt_succ hi)
      · intro i hi
        cases i with
        | zero => omega
        | succ i => exact hz i (Nat.le_of_succ_le_succ hi)
      · intro i hi
        cases i with
        | zero =>
          have hr0 : 0 < r := Nat.lt_of_succ_lt_succ hi
          let i₀ : Fin m := ⟨0, hr0.trans_le (hr.trans (min_le_left _ _))⟩
          let j₀ : Fin n := ⟨0, hr0.trans_le (hr.trans (min_le_right _ _))⟩
          have h := hSdiv i₀ j₀
          simpa [hS, rectDiagonal_apply, i₀, j₀] using h
        | succ i => exact hchain i (Nat.lt_of_succ_lt_succ hi)

/-- **Exercise 84** of [benIsrael2003generalized]. Euclidean pivot
reduction terminates in a Smith normal form. Its first phase strictly
decreases the nonzero pivot magnitude, and its second phase recurses
on the trailing submatrix. -/
theorem smithNormalForm_algorithm (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ S, Relation.ReflTransGen IntegralElementaryStep A S ∧ IsSmithNormalForm S A.rank := by
  obtain ⟨r, S, hS, hr⟩ := exists_smithNormalForm_elementary A
  have he := (equivalentOverIntegers_of_elementarySteps hS).rank_eq.trans hr.rank_eq
  exact ⟨S, hS, he ▸ hr⟩

/-- The cleared pivot represents the greatest common divisor of the
original entries up to an integer unit. -/
theorem IsClearedSmithPivot.dvd_iff_of_steps
    {A B : Matrix (Fin (m + 1)) (Fin (n + 1)) ℤ}
    (hB : IsClearedSmithPivot B) (h : SmithSteps A B) (d : ℤ) :
    d ∣ B 0 0 ↔ ∀ i j, d ∣ A i j := by
  have he := equivalentOverIntegers_of_elementarySteps h
  exact ⟨fun hd => he.symm.dvd_entry (fun i j => hd.trans (hB.2.2.2 i j)),
    fun hd => he.dvd_entry hd 0 0⟩

/-- **Theorem 4** of [benIsrael2003generalized], Chapter 0. Every integer
matrix of rank $r$ is equivalent over the integers to Smith normal form
with $r$ nonzero invariant factors. -/
theorem theorem_4 (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ S, equivalentOverIntegers A S ∧ IsSmithNormalForm S A.rank := by
  obtain ⟨S, hS, hs⟩ := smithNormalForm_algorithm A
  exact ⟨S, equivalentOverIntegers_of_elementarySteps hS, hs⟩

end SmithPivotReduction

section SignedElementarySteps

variable {m n : ℕ}

/-- Multiplying by an integer unit in a single coordinate changes only
the sign of the selected row or column. -/
def integralSignMatrix (i : Fin n) (u : ℤˣ) : Matrix (Fin n) (Fin n) ℤ :=
  diagonal (fun j => if j = i then (u : ℤ) else 1)

private theorem integralSignMatrix_mul_inv (i : Fin n) (u : ℤˣ) :
    integralSignMatrix i u * integralSignMatrix i u⁻¹ = 1 := by
  unfold integralSignMatrix
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

private theorem isUnit_integralSignMatrix (i : Fin n) (u : ℤˣ) :
    IsUnit (integralSignMatrix i u) :=
  isUnit_iff_exists_inv.mpr ⟨_, integralSignMatrix_mul_inv i u⟩

/-- The signed elementary operations extend the printed list in
**Exercise 83** by sign changes on individual rows and columns. -/
inductive SignedIntegralElementaryStep (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m) (Fin n) ℤ → Prop
  | elementary {B} (h : IntegralElementaryStep A B) : SignedIntegralElementaryStep A B
  | scaleRow (i : Fin m) (u : ℤˣ) :
      SignedIntegralElementaryStep A (integralSignMatrix i u * A)
  | scaleCol (j : Fin n) (u : ℤˣ) :
      SignedIntegralElementaryStep A (A * integralSignMatrix j u)

private abbrev SignedSteps {m n : ℕ} :=
  Relation.ReflTransGen (SignedIntegralElementaryStep (m := m) (n := n))

private theorem SignedIntegralElementaryStep.to_equivalentOverIntegers
    {A B : Matrix (Fin m) (Fin n) ℤ} (h : SignedIntegralElementaryStep A B) :
    equivalentOverIntegers A B := by
  cases h with
  | elementary h =>
    exact equivalentOverIntegers_of_elementarySteps (Relation.ReflTransGen.single h)
  | scaleRow i u =>
    simpa only [Matrix.mul_one] using equivalentOverIntegers.of_isUnit (A := A)
      (integralSignMatrix i u) 1 (isUnit_integralSignMatrix i u) isUnit_one
  | scaleCol j u =>
    simpa only [Matrix.one_mul] using equivalentOverIntegers.of_isUnit (A := A)
      1 (integralSignMatrix j u) isUnit_one (isUnit_integralSignMatrix j u)

private theorem transvection_mul_neg_transvection (i j : Fin n) (h : i ≠ j) (a : ℤ) :
    Matrix.transvection i j a * Matrix.transvection i j (-a) = 1 := by
  rw [Matrix.transvection_mul_transvection_same i j h, add_neg_cancel, Matrix.transvection_zero]

private def ActsBySignedOperations (P : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ (m : ℕ) (A : Matrix (Fin n) (Fin m) ℤ), SignedSteps A (P * A)) ∧
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin n) ℤ), SignedSteps A (A * P)

private theorem actsBySignedOperations_one (n : ℕ) :
    ActsBySignedOperations (1 : Matrix (Fin n) (Fin n) ℤ) := by
  constructor <;> intro m A
  · rw [Matrix.one_mul]
  · rw [Matrix.mul_one]

private theorem ActsBySignedOperations.mul {P Q : Matrix (Fin n) (Fin n) ℤ}
    (hP : ActsBySignedOperations P) (hQ : ActsBySignedOperations Q) :
    ActsBySignedOperations (P * Q) := by
  constructor <;> intro m A
  · rw [Matrix.mul_assoc]
    exact (hQ.1 _ _).trans (hP.1 _ _)
  · rw [← Matrix.mul_assoc]
    exact (hP.2 _ _).trans (hQ.2 _ _)

private theorem actsBySignedOperations_swap (i j : Fin n) :
    ActsBySignedOperations (Matrix.swap ℤ i j) :=
  ⟨fun _ _ => Relation.ReflTransGen.single (.elementary (.swapRows i j)),
    fun _ _ => Relation.ReflTransGen.single (.elementary (.swapCols i j))⟩

private theorem actsBySignedOperations_transvection (i j : Fin n) (h : i ≠ j) (a : ℤ) :
    ActsBySignedOperations (Matrix.transvection i j a) :=
  ⟨fun _ _ => Relation.ReflTransGen.single (.elementary (.addRow i j h a)),
    fun _ _ => Relation.ReflTransGen.single (.elementary (.addCol i j h a))⟩

private theorem actsBySignedOperations_sign (i : Fin n) (u : ℤˣ) :
    ActsBySignedOperations (integralSignMatrix i u) :=
  ⟨fun _ _ => Relation.ReflTransGen.single (.scaleRow i u),
    fun _ _ => Relation.ReflTransGen.single (.scaleCol i u)⟩

private theorem actsBySignedOperations_of_elementaryStep {P Q : Matrix (Fin n) (Fin n) ℤ}
    (h : IntegralElementaryStep P Q) (hQ : ActsBySignedOperations Q) :
    ActsBySignedOperations P := by
  cases h with
  | swapRows i j =>
    have he := (actsBySignedOperations_swap i j).mul hQ
    rwa [← Matrix.mul_assoc, Matrix.swap_mul_self, Matrix.one_mul] at he
  | swapCols i j =>
    have he := hQ.mul (actsBySignedOperations_swap i j)
    rwa [Matrix.mul_assoc, Matrix.swap_mul_self, Matrix.mul_one] at he
  | addRow i j hij a =>
    have he := (actsBySignedOperations_transvection i j hij (-a)).mul hQ
    rw [← Matrix.mul_assoc, show Matrix.transvection i j (-a) * Matrix.transvection i j a = 1 by
      simpa only [neg_neg] using transvection_mul_neg_transvection i j hij (-a),
      Matrix.one_mul] at he
    exact he
  | addCol i j hij a =>
    have he := hQ.mul (actsBySignedOperations_transvection i j hij (-a))
    rwa [Matrix.mul_assoc, transvection_mul_neg_transvection i j hij a, Matrix.mul_one] at he

private theorem actsBySignedOperations_diagonal (d : Fin n → ℤˣ) :
    ActsBySignedOperations (diagonal fun i => (d i : ℤ)) := by
  have h (s : Finset (Fin n)) :
      ActsBySignedOperations (diagonal fun i => if i ∈ s then (d i : ℤ) else 1) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.notMem_empty, ite_false, diagonal_one] using
        actsBySignedOperations_one n
    | @insert i s hi ih =>
      have he : (diagonal fun j => if j ∈ insert i s then (d j : ℤ) else 1) =
          integralSignMatrix i (d i) * diagonal (fun j => if j ∈ s then (d j : ℤ) else 1) := by
        rw [integralSignMatrix, diagonal_mul_diagonal]
        apply congrArg diagonal
        funext j
        by_cases hj : j = i
        · subst j
          simp [hi]
        · simp [hj, Finset.mem_insert]
      rw [he]
      exact (actsBySignedOperations_sign i (d i)).mul ih
  simpa only [Finset.mem_univ, ite_true] using h Finset.univ

private theorem actsBySignedOperations_of_steps {P S : Matrix (Fin n) (Fin n) ℤ}
    (h : SmithSteps P S) (hs : ActsBySignedOperations S) : ActsBySignedOperations P := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact ih (actsBySignedOperations_of_elementaryStep hstep hs)

private theorem actsBySignedOperations_of_isUnit {P : Matrix (Fin n) (Fin n) ℤ} (hP : IsUnit P) :
    ActsBySignedOperations P := by
  obtain ⟨S, hS, d, _, hd, _, _, _⟩ := smithNormalForm_algorithm P
  have hu : IsUnit S := by
    obtain ⟨U, V, he⟩ := equivalentOverIntegers_of_elementarySteps hS
    rw [← he]
    exact (U.isUnit.mul hP).mul V.isUnit
  have he : S = diagonal fun i : Fin n => d i.val := by
    rw [hd]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [rectDiagonal_apply]
    · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp [rectDiagonal_apply, hij, hne]
  rw [he] at hu
  have hv (i : Fin n) : IsUnit (d i.val) := by
    obtain ⟨u, hu⟩ := Matrix.isUnit_diagonal.mp hu
    change (u : Fin n → ℤ) = (fun i : Fin n => d i.val) at hu
    refine ⟨⟨u.val i, u.inv i, congrFun u.val_inv i, congrFun u.inv_val i⟩, congrFun hu i⟩
  let units : Fin n → ℤˣ := fun i => (hv i).unit
  have hs : ActsBySignedOperations S := by
    rw [he]
    exact actsBySignedOperations_diagonal units
  exact actsBySignedOperations_of_steps hS hs

/-- **Exercise 83** of [benIsrael2003generalized]. Integral equivalence
is generated by swaps, additions of integer multiples of other rows
or columns, and individual sign changes. -/
theorem equivalentOverIntegers_iff_signedElementarySteps {A B : Matrix (Fin m) (Fin n) ℤ} :
    equivalentOverIntegers A B ↔ Relation.ReflTransGen SignedIntegralElementaryStep A B := by
  constructor
  · rintro ⟨P, Q, rfl⟩
    have hP := actsBySignedOperations_of_isUnit P.isUnit
    have hQ := actsBySignedOperations_of_isUnit Q.isUnit
    exact (hP.1 _ _).trans (hQ.2 _ _)
  · intro h
    induction h with
    | refl => exact equivalentOverIntegers.refl _
    | tail _ hstep ih => exact ih.trans hstep.to_equivalentOverIntegers

end SignedElementarySteps

end BenIsraelGreville.Chapter00
