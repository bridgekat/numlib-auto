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

private theorem equivalentOverIntegers_prependDiagonalEntry (a : ℤ)
    {B C : Matrix (Fin m) (Fin n) ℤ} (h : equivalentOverIntegers B C) :
    equivalentOverIntegers (prependDiagonalEntry a B) (prependDiagonalEntry a C) := by
  obtain ⟨P, Q, hPQ⟩ := h
  let L := fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 P.val
  let R := fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 Q.val
  have hL : IsUnit L := isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, P.isUnit⟩
  have hR : IsUnit R := isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, Q.isUnit⟩
  have hL' := hL.map (reindexRingEquiv ℤ (firstAndTail m)).toMonoidHom
  have hR' := hR.map (reindexRingEquiv ℤ (firstAndTail n)).toMonoidHom
  let D : Matrix (Fin 1) (Fin 1) ℤ := Matrix.of (fun _ _ => a)
  have hMul : L * fromBlocks D 0 0 B * R = fromBlocks D 0 0 C := by
    simp only [L, R, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, hPQ]
  convert equivalentOverIntegers.of_isUnit (A := prependDiagonalEntry a B) _ _ hL' hR'
    using 1
  change prependDiagonalEntry a C = L.reindex (firstAndTail m) (firstAndTail m) *
    prependDiagonalEntry a B * R.reindex (firstAndTail n) (firstAndTail n)
  change (fromBlocks D 0 0 C).reindex (firstAndTail m) (firstAndTail n) =
    L.reindex (firstAndTail m) (firstAndTail m) *
      (fromBlocks D 0 0 B).reindex (firstAndTail m) (firstAndTail n) *
      R.reindex (firstAndTail n) (firstAndTail n)
  simp only [reindex_apply, submatrix_mul_equiv, hMul]

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

private theorem exists_smithForm_aux (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ r S, equivalentOverIntegers A S ∧ IsSmithNormalForm S r := by
  induction m generalizing n with
  | zero =>
    have h : A = 0 := Matrix.ext fun i _ => Fin.elim0 i
    subst A
    exact ⟨0, 0, equivalentOverIntegers.refl _, isSmithNormalForm_zero _ _⟩
  | succ m ih =>
    cases n with
    | zero =>
      have h : A = 0 := Matrix.ext fun _ j => Fin.elim0 j
      subst A
      exact ⟨0, 0, equivalentOverIntegers.refl _, isSmithNormalForm_zero _ _⟩
    | succ n =>
      by_cases hA : A = 0
      · subst A
        exact ⟨0, 0, equivalentOverIntegers.refl _, isSmithNormalForm_zero _ _⟩
      obtain ⟨B, hB, hb, hcol, hrow, hdiv⟩ := exists_cleared_smithPivot hA
      let T := B.submatrix Fin.succ Fin.succ
      obtain ⟨r, S, hTS, d, hr, hS, hnz, hz, hchain⟩ := ih T
      have hB' : B = prependDiagonalEntry (B 0 0) T :=
        eq_prependDiagonalEntry_of_cleared B hcol hrow
      have hBS : equivalentOverIntegers B (prependDiagonalEntry (B 0 0) S) :=
        hB'.symm ▸ equivalentOverIntegers_prependDiagonalEntry (B 0 0) hTS
      have hSdiv := hTS.dvd_entry (fun i j => hdiv i.succ j.succ)
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

/-- **Theorem 4** of [benIsrael2003generalized], Chapter 0. Every integer
matrix of rank $r$ is equivalent over the integers to Smith normal form
with $r$ nonzero invariant factors. -/
theorem theorem_4 (A : Matrix (Fin m) (Fin n) ℤ) :
    ∃ S, equivalentOverIntegers A S ∧ IsSmithNormalForm S A.rank := by
  obtain ⟨r, S, hS, hs⟩ := exists_smithForm_aux A
  exact ⟨S, hS, (hS.rank_eq.trans hs.rank_eq).symm ▸ hs⟩

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

end BenIsraelGreville.Chapter00
