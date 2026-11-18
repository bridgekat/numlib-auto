/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter04.Section07

/-!
# The index-one and nilpotent parts of a square matrix

Section 4.8 of [benIsrael2003generalized] splits a complex matrix into a
group-invertible part and a nilpotent part that annihilate one another.

## Deviations from the source

* In Theorem 12 the ranges and kernels used to compare the Drazin
  projectors belong to the Drazin inverses. They are the stable ranges
  and kernels of the original matrices.
-/

namespace BenIsraelGreville.Chapter04

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The index-one part of a square matrix is the group inverse of its Drazin inverse. -/
noncomputable def groupInvertiblePart (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A ^ 2 * drazinInverse A

/-- **Equation (56)** of [benIsrael2003generalized], Chapter 4.
The nilpotent part is the difference between the matrix and its index-one part. -/
noncomputable def nilpotentPart (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A - groupInvertiblePart A

/-- The index-one part is the group inverse of the Drazin inverse. -/
theorem isGroupInverse_groupInvertiblePart (A : Matrix n n ℂ) :
    IsGroupInverse (drazinInverse A) (groupInvertiblePart A) :=
  (isDrazinInverseAt_drazinInverse A).isGroupInverse_square_mul

/-- The Drazin inverse is the group inverse of the index-one part. -/
theorem isGroupInverse_drazinInverse_groupInvertiblePart (A : Matrix n n ℂ) :
    IsGroupInverse (groupInvertiblePart A) (drazinInverse A) := by
  obtain ⟨hc, hi, ho⟩ := _root_.isGroupInverse_iff.mp (isGroupInverse_groupInvertiblePart A)
  exact _root_.isGroupInverse_iff.mpr ⟨hc.symm, ho, hi⟩

/-- The group-invertible part and the nilpotent part add to the original matrix. -/
theorem groupInvertiblePart_add_nilpotentPart (A : Matrix n n ℂ) :
    groupInvertiblePart A + nilpotentPart A = A := by
  unfold nilpotentPart
  abel

/-- Each part annihilates the other on both sides. -/
theorem groupInvertiblePart_mul_nilpotentPart (A : Matrix n n ℂ) :
    groupInvertiblePart A * nilpotentPart A = 0 ∧
      nilpotentPart A * groupInvertiblePart A = 0 := by
  let D := drazinInverse A
  have hD := isDrazinInverseAt_drazinInverse A
  have hB : Commute A (A ^ 2 * D) := ((Commute.refl A).pow_right 2).mul_right hD.commute
  have hsq : (A ^ 2 * D) * (A ^ 2 * D) = A * (A ^ 2 * D) := calc
    _ = A ^ 2 * (D * A ^ 2) * D := by noncomm_ring
    _ = A ^ 2 * (A ^ 2 * D) * D := by rw [(hD.commute.pow_left 2).eq]
    _ = A * (A ^ 2 * (A * D ^ 2)) := by noncomm_ring
    _ = _ := by rw [hD.mul_sq]
  constructor
  · change (A ^ 2 * D) * (A - A ^ 2 * D) = 0
    rw [mul_sub, hsq, hB.eq, sub_self]
  · change (A - A ^ 2 * D) * (A ^ 2 * D) = 0
    rw [sub_mul, hsq, sub_self]

private theorem pow_add_of_mul_eq_zero {R : Type*} [Ring R] {B N : R}
    (hBN : B * N = 0) (hNB : N * B = 0) (k : ℕ) :
    (B + N) ^ (k + 1) = B ^ (k + 1) + N ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h₁ : B ^ (k + 1) * N = 0 := by rw [pow_succ, mul_assoc, hBN, mul_zero]
    have h₂ : N ^ (k + 1) * B = 0 := by rw [pow_succ, mul_assoc, hNB, mul_zero]
    rw [pow_succ (B + N), ih, add_mul, mul_add, mul_add, h₁, h₂, add_zero, zero_add,
      ← pow_succ, ← pow_succ]

/-- **Equation (54)** of [benIsrael2003generalized], Chapter 4.
Every positive power is the sum of the same powers of its two parts. -/
theorem pow_eq_groupInvertiblePart_add_nilpotentPart (A : Matrix n n ℂ) {k : ℕ} (hk : 0 < k) :
    A ^ k = groupInvertiblePart A ^ k + nilpotentPart A ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  calc
    A ^ (j + 1) = (groupInvertiblePart A + nilpotentPart A) ^ (j + 1) :=
      congrArg (· ^ (j + 1)) (groupInvertiblePart_add_nilpotentPart A).symm
    _ = _ := pow_add_of_mul_eq_zero (groupInvertiblePart_mul_nilpotentPart A).1
      (groupInvertiblePart_mul_nilpotentPart A).2 j

/-- The group-invertible part agrees with the original matrix in powers at or
above the matrix index. -/
theorem groupInvertiblePart_pow_eq (A : Matrix n n ℂ) {k : ℕ} (hk : matrixIndex A ≤ k) :
    groupInvertiblePart A ^ k = A ^ k := by
  let D := drazinInverse A
  have hD := (isDrazinInverseAt_drazinInverse A).mono hk
  have hcancel (j : ℕ) : A ^ (k + j) * D ^ j = A ^ k := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show k + (j + 1) = k + j + 1 by omega, pow_succ' D, ← mul_assoc,
        (hD.mono (Nat.le_add_right k j)).stable, ih]
  change (A ^ 2 * D) ^ k = A ^ k
  rw [(hD.commute.pow_left 2).mul_pow, ← pow_mul, show 2 * k = k + k by omega, hcancel]

/-- The nilpotent part vanishes when raised to the matrix index. -/
theorem nilpotentPart_pow_matrixIndex (A : Matrix n n ℂ) :
    nilpotentPart A ^ matrixIndex A = 0 := by
  have h := pow_eq_groupInvertiblePart_add_nilpotentPart A A.rankStabilizationIndex_spec.1
  rw [groupInvertiblePart_pow_eq A le_rfl] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

private theorem drazinInverse_eq_of_isDrazinInverseAt {A X : Matrix n n ℂ} {k : ℕ}
    (hX : IsDrazinInverseAt k A X) : drazinInverse A = X :=
  ((isDrazinInverseAt_drazinInverse A).mono (le_max_left _ _)).unique
    (hX.mono (le_max_right _ _))

/-- A core–nilpotent decomposition is an annihilating sum of an index-one
matrix and a nilpotent matrix. -/
def IsCoreNilpotentDecomposition (A B N : Matrix n n ℂ) : Prop :=
  A = B + N ∧ matrixIndex B = 1 ∧ IsNilpotent N ∧ B * N = 0 ∧ N * B = 0

private theorem groupInverse_of_coreNilpotentDecomposition {A B N : Matrix n n ℂ}
    (h : IsCoreNilpotentDecomposition A B N) : IsGroupInverse (drazinInverse A) B := by
  obtain ⟨hA, hB, ⟨k, hk⟩, hBN, hNB⟩ := h
  obtain ⟨G, hG, _⟩ := (theorem_4_2 B).mpr hB
  have hG₂ : G ^ 2 * B = G := (hG.commute.pow_right 2).eq.symm.trans hG.mul_sq
  have hGN : G * N = 0 := by
    rw [← hG₂, mul_assoc, hBN, mul_zero]
  have hNG : N * G = 0 := by
    rw [← hG.mul_sq, ← mul_assoc, hNB, zero_mul]
  have hpow : N ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  have hpow' : N ^ (k + 1 + 1) = 0 := by rw [pow_succ, hpow, zero_mul]
  have hD : IsDrazinInverseAt (k + 1) A G := by
    refine ⟨?_, ?_, ?_⟩
    · change A * G = G * A
      rw [hA, add_mul, mul_add, hNG, hGN, add_zero, add_zero, hG.commute.eq]
    · rw [hA, mul_add, hGN, add_zero, hG.outer]
    · rw [hA, pow_add_of_mul_eq_zero hBN hNB (k + 1), pow_add_of_mul_eq_zero hBN hNB k,
        hpow, hpow', add_zero, add_zero]
      exact (hG.mono (by omega)).stable
  rw [drazinInverse_eq_of_isDrazinInverseAt hD]
  obtain ⟨hc, hi, ho⟩ := _root_.isGroupInverse_iff.mp hG
  exact _root_.isGroupInverse_iff.mpr ⟨hc.symm, ho, hi⟩

/-- **Theorem 11** of [benIsrael2003generalized], Chapter 4.
The unique index-one and nilpotent parts are the group inverse of the
Drazin inverse and its difference from the original matrix. -/
theorem theorem_4_11 (A : Matrix n n ℂ) :
    IsCoreNilpotentDecomposition A (groupInvertiblePart A) (nilpotentPart A) ∧
      ∀ B N, IsCoreNilpotentDecomposition A B N →
        B = groupInvertiblePart A ∧ N = nilpotentPart A := by
  have hG := isGroupInverse_drazinInverse_groupInvertiblePart A
  have hidx := (theorem_4_2 (groupInvertiblePart A)).mp
    ⟨drazinInverse A, hG, fun _ h => h.unique hG⟩
  refine ⟨⟨(groupInvertiblePart_add_nilpotentPart A).symm, hidx,
    ⟨matrixIndex A, nilpotentPart_pow_matrixIndex A⟩, groupInvertiblePart_mul_nilpotentPart A⟩, ?_⟩
  intro B N h
  have hB := (groupInverse_of_coreNilpotentDecomposition h).unique
    (isGroupInverse_groupInvertiblePart A)
  refine ⟨hB, ?_⟩
  rw [nilpotentPart, ← hB, h.1, add_sub_cancel_left]

/-- The nilpotent part is zero for an index-one matrix. -/
theorem nilpotentPart_eq_zero_of_matrixIndex_one (A : Matrix n n ℂ)
    (h : matrixIndex A = 1) : nilpotentPart A = 0 := by
  simpa only [h, pow_one] using nilpotentPart_pow_matrixIndex A

/-- The Drazin projector selects the stable range along the stable kernel. -/
noncomputable def drazinProjector (A : Matrix n n ℂ) : Matrix n n ℂ := A * drazinInverse A

/-- The Drazin projector is idempotent. -/
theorem drazinProjector_mul_self (A : Matrix n n ℂ) :
    drazinProjector A * drazinProjector A = drazinProjector A := by
  unfold drazinProjector
  rw [mul_assoc A, ← mul_assoc (drazinInverse A), (isDrazinInverseAt_drazinInverse A).outer]

/-- The core times its group inverse is the Drazin projector. -/
theorem groupInvertiblePart_mul_drazinInverse (A : Matrix n n ℂ) :
    groupInvertiblePart A * drazinInverse A = drazinProjector A := by
  unfold groupInvertiblePart drazinProjector
  rw [pow_two, mul_assoc, mul_assoc, ← pow_two, (isDrazinInverseAt_drazinInverse A).mul_sq]

/-- The Drazin inverse annihilates the nilpotent part in both orders. -/
theorem drazinInverse_mul_nilpotentPart (A : Matrix n n ℂ) :
    drazinInverse A * nilpotentPart A = 0 ∧ nilpotentPart A * drazinInverse A = 0 := by
  have h := isGroupInverse_drazinInverse_groupInvertiblePart A
  have hD := isDrazinInverseAt_drazinInverse A
  have hc : drazinInverse A * groupInvertiblePart A = drazinProjector A :=
    h.commute.eq.symm.trans (groupInvertiblePart_mul_drazinInverse A)
  constructor
  · rw [nilpotentPart, mul_sub, hc, ← hD.commute.eq, drazinProjector, sub_self]
  · rw [nilpotentPart, sub_mul, groupInvertiblePart_mul_drazinInverse, drazinProjector, sub_self]

private theorem drazinProjector_range_ker (A : Matrix n n ℂ) :
    (drazinProjector A).mulVecLin.range = (drazinInverse A).mulVecLin.range ∧
      (drazinProjector A).mulVecLin.ker = (drazinInverse A).mulVecLin.ker := by
  let P := drazinProjector A
  let D := drazinInverse A
  have hD := isDrazinInverseAt_drazinInverse A
  have hDP : D * P = D := by
    change D * (A * D) = D
    rw [← mul_assoc, hD.outer]
  have hPD : P * D = D := by
    change A * D * D = D
    rw [mul_assoc, ← pow_two, hD.mul_sq]
  constructor
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      refine ⟨A *ᵥ v, ?_⟩
      change D *ᵥ (A *ᵥ v) = (A * D) *ᵥ v
      rw [mulVec_mulVec, hD.commute.eq]
    · rintro _ ⟨v, rfl⟩
      refine ⟨D *ᵥ v, ?_⟩
      change P *ᵥ (D *ᵥ v) = D *ᵥ v
      rw [mulVec_mulVec, hPD]
  · ext v
    change P *ᵥ v = 0 ↔ D *ᵥ v = 0
    constructor
    · intro hv
      calc
        D *ᵥ v = D *ᵥ (P *ᵥ v) := by rw [mulVec_mulVec, hDP]
        _ = 0 := by rw [hv, mulVec_zero]
    · intro hv
      change (A * D) *ᵥ v = 0
      rw [← mulVec_mulVec, hv, mulVec_zero]

private theorem drazinProjector_eq_of_range_ker {A X : Matrix n n ℂ}
    (hR : (drazinInverse A).mulVecLin.range = (drazinInverse X).mulVecLin.range)
    (hK : (drazinInverse A).mulVecLin.ker = (drazinInverse X).mulVecLin.ker) :
    drazinProjector A = drazinProjector X := by
  let P := drazinProjector A
  let Q := drazinProjector X
  obtain ⟨hRA, hKA⟩ := drazinProjector_range_ker A
  obtain ⟨hRX, hKX⟩ := drazinProjector_range_ker X
  have hRange : P.mulVecLin.range = Q.mulVecLin.range := hRA.trans (hR.trans hRX.symm)
  have hKer : P.mulVecLin.ker = Q.mulVecLin.ker := hKA.trans (hK.trans hKX.symm)
  rw [ext_iff_mulVec]
  intro v
  have h₁ : v - Q *ᵥ v ∈ Q.mulVecLin.ker := by
    change Q *ᵥ (v - Q *ᵥ v) = 0
    rw [mulVec_sub, mulVec_mulVec, drazinProjector_mul_self X, sub_self]
  rw [← hKer] at h₁
  change P *ᵥ (v - Q *ᵥ v) = 0 at h₁
  rw [mulVec_sub, sub_eq_zero] at h₁
  obtain ⟨w, hw⟩ := hRange.symm ▸ Q.mulVecLin.mem_range_self v
  change P *ᵥ w = Q *ᵥ v at hw
  change P *ᵥ v = Q *ᵥ v
  rw [h₁, ← hw, mulVec_mulVec, drazinProjector_mul_self A]

/-- Exchanging the Drazin inverse and core in one direction also
exchanges them in the other direction. -/
theorem groupInvertiblePart_eq_drazinInverse_of_drazinInverse_eq_groupInvertiblePart
    {A X : Matrix n n ℂ} (h : drazinInverse X = groupInvertiblePart A) :
    groupInvertiblePart X = drazinInverse A := by
  have hX := isGroupInverse_groupInvertiblePart X
  rw [h] at hX
  exact hX.unique (isGroupInverse_drazinInverse_groupInvertiblePart A)

private theorem drazinProjector_sandwich (A : Matrix n n ℂ) :
    drazinProjector A * A * drazinProjector A = groupInvertiblePart A := by
  have h : A * drazinProjector A = drazinProjector A * A :=
    ((Commute.refl A).mul_right (isDrazinInverseAt_drazinInverse A).commute).eq
  rw [← h, mul_assoc, drazinProjector_mul_self]
  simp only [drazinProjector, groupInvertiblePart, pow_two, mul_assoc]

/-- **Theorem 12**, forward direction, of [benIsrael2003generalized], Chapter 4.
Equality of the Drazin inverse of one matrix and the core of the other
implies S-prime inversion. -/
theorem theorem_4_12_of_drazinInverse_eq_groupInvertiblePart {A X : Matrix n n ℂ}
    (h : drazinInverse X = groupInvertiblePart A) : IsSPrimeInverse A X := by
  have hB := groupInvertiblePart_eq_drazinInverse_of_drazinInverse_eq_groupInvertiblePart h
  have hp : drazinProjector X = drazinProjector A := calc
    _ = groupInvertiblePart X * drazinInverse X := (groupInvertiblePart_mul_drazinInverse X).symm
    _ = drazinInverse A * groupInvertiblePart A := by rw [hB, h]
    _ = groupInvertiblePart A * drazinInverse A := (isGroupInverse_groupInvertiblePart A).commute.eq
    _ = _ := groupInvertiblePart_mul_drazinInverse A
  let l := max (matrixIndex A) (matrixIndex X)
  have hlA : matrixIndex A ≤ l := le_max_left _ _
  have hlX : matrixIndex X ≤ l := le_max_right _ _
  have shift {B Y : Matrix n n ℂ} (hB : matrixIndex B ≤ l)
      (he : drazinInverse Y = groupInvertiblePart B)
      (hr : groupInvertiblePart Y = drazinInverse B) :
      Y * B ^ (l + 1) = B ^ l := by
    have hn : nilpotentPart Y * groupInvertiblePart B = 0 := by
      rw [← he]
      exact (drazinInverse_mul_nilpotentPart Y).2
    calc
      _ = (groupInvertiblePart Y + nilpotentPart Y) * groupInvertiblePart B ^ (l + 1) := by
        rw [groupInvertiblePart_add_nilpotentPart,
          groupInvertiblePart_pow_eq B (hB.trans (Nat.le_succ l))]
      _ = drazinInverse B * groupInvertiblePart B ^ (l + 1) := by
        rw [add_mul, hr, pow_succ' (groupInvertiblePart B), ← mul_assoc (nilpotentPart Y),
          hn, zero_mul, add_zero, ← pow_succ']
      _ = _ := by
        rw [groupInvertiblePart_pow_eq B (hB.trans (Nat.le_succ l))]
        exact ((isDrazinInverseAt_drazinInverse B).mono hB).stable_left
  refine ⟨?_, ?_⟩
  · intro μ hμ v p
    refine ⟨lemma_4_4 A X (shift hlA h hB) hμ, fun hv => ?_⟩
    simpa only [inv_inv] using lemma_4_4 X A (shift hlX hB.symm h.symm) (inv_ne_zero hμ) hv
  · rw [maxGenEigenspace_zero_eq_stableKer A hlA, maxGenEigenspace_zero_eq_stableKer X hlX,
      ← (drazinInverse_range_ker_eq_stablePow A hlA).2,
      ← (drazinInverse_range_ker_eq_stablePow X hlX).2,
      ← (drazinProjector_range_ker A).2, ← (drazinProjector_range_ker X).2, hp]

/-- **Theorem 12** of [benIsrael2003generalized], Chapter 4.
Among inner or outer inverses S-prime inversion is equivalent to
equality of one Drazin inverse with the other core. -/
theorem theorem_4_12 {A X : Matrix n n ℂ} (hi : A.IsInnerInverse X ∨ A.IsOuterInverse X) :
    IsSPrimeInverse A X ↔ drazinInverse X = groupInvertiblePart A := by
  refine ⟨fun h => ?_, theorem_4_12_of_drazinInverse_eq_groupInvertiblePart⟩
  have converse {B Y : Matrix n n ℂ} (hs : IsSPrimeInverse B Y) (hI : B.IsInnerInverse Y) :
      drazinInverse B = groupInvertiblePart Y := by
    obtain ⟨hR, hK⟩ := hs.drazinInverse_range_ker_eq
    have hP := drazinProjector_eq_of_range_ker hR hK
    have hD := isDrazinInverseAt_drazinInverse B
    calc
      drazinInverse B = drazinInverse B * B * drazinInverse B := hD.outer.symm
      _ = drazinInverse B * (B * Y * B) * drazinInverse B := by
        rw [isInnerInverse_iff.mp hI]
      _ = drazinProjector B * Y * drazinProjector B := by
        simp only [drazinProjector, hD.commute.eq, mul_assoc]
      _ = _ := by rw [hP, drazinProjector_sandwich]
  rcases hi with hi | hi
  · exact groupInvertiblePart_eq_drazinInverse_of_drazinInverse_eq_groupInvertiblePart
      (converse h hi) |>.symm
  · exact converse h.symm hi

/-- **Exercise 42** of [benIsrael2003generalized], Chapter 4.
In a similarity with an invertible block and a nilpotent block, the two
parts are obtained by retaining just one of the respective blocks. -/
theorem exercise_4_42 {i j : Type*} [Fintype i] [Fintype j] [DecidableEq i] [DecidableEq j]
    (C : (Matrix i i ℂ)ˣ) (Z : Matrix j j ℂ) (hZ : IsNilpotent Z)
    (P : (Matrix (i ⊕ j) (i ⊕ j) ℂ)ˣ) :
    let A := (P : Matrix (i ⊕ j) (i ⊕ j) ℂ) * fromBlocks (C : Matrix i i ℂ) 0 0 Z *
      (↑P⁻¹ : Matrix (i ⊕ j) (i ⊕ j) ℂ)
    groupInvertiblePart A =
      (P : Matrix (i ⊕ j) (i ⊕ j) ℂ) * fromBlocks (C : Matrix i i ℂ) 0 0 (0 : Matrix j j ℂ) *
        (↑P⁻¹ : Matrix (i ⊕ j) (i ⊕ j) ℂ) ∧
    nilpotentPart A =
      (P : Matrix (i ⊕ j) (i ⊕ j) ℂ) * fromBlocks (0 : Matrix i i ℂ) 0 0 Z *
        (↑P⁻¹ : Matrix (i ⊕ j) (i ⊕ j) ℂ) := by
  intro A
  let S := Matrix (i ⊕ j) (i ⊕ j) ℂ
  let B : Matrix (i ⊕ j) (i ⊕ j) ℂ := fromBlocks (C : Matrix i i ℂ) 0 0 0
  let G : Matrix (i ⊕ j) (i ⊕ j) ℂ := fromBlocks (↑C⁻¹ : Matrix i i ℂ) 0 0 0
  let N : Matrix (i ⊕ j) (i ⊕ j) ℂ := fromBlocks 0 0 0 Z
  let f : S →+* S :=
    { toFun := fun M => (P : S) * M * (↑P⁻¹ : S)
      map_zero' := by simp
      map_one' := by rw [mul_one, Units.mul_inv]
      map_add' := fun M N => by rw [mul_add, add_mul]
      map_mul' := fun M N => by simp only [mul_assoc, Units.inv_mul_cancel_left] }
  have hG : IsGroupInverse B G := by
    apply _root_.isGroupInverse_iff.mpr
    refine ⟨?_, ?_, ?_⟩
    · change B * G = G * B
      simp [B, G, fromBlocks_multiply]
    · simp [B, G, fromBlocks_multiply]
    · simp [B, G, fromBlocks_multiply]
  have hBN : B * N = 0 := by
    simp [B, N, fromBlocks_multiply]
  have hNB : N * B = 0 := by
    simp [B, N, fromBlocks_multiply]
  have hN : IsNilpotent N := by
    obtain ⟨k, hk⟩ := hZ
    have hpow (l : ℕ) : N ^ (l + 1) = fromBlocks (0 : Matrix i i ℂ) 0 0 (Z ^ (l + 1)) := by
      induction l with
      | zero => simp [N]
      | succ l ih =>
        rw [pow_succ N (l + 1), ih, pow_succ Z (l + 1)]
        simp [N, fromBlocks_multiply]
    exact ⟨k + 1, by rw [hpow, pow_succ, hk, zero_mul, fromBlocks_zero]⟩
  have hAf : A = f (B + N) := by
    change f (fromBlocks (C : Matrix i i ℂ) 0 0 Z) = f (B + N)
    simp [B, N, fromBlocks_add]
  have hFG := hG.map f.toMonoidHom
  have hsplit : IsCoreNilpotentDecomposition A (f B) (f N) := by
    refine ⟨hAf.trans (map_add f B N), (theorem_4_2 (f B)).mp ⟨_, hFG, fun _ h => h.unique hFG⟩,
      ?_, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hN
      exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
    · rw [← map_mul, hBN, map_zero]
    · rw [← map_mul, hNB, map_zero]
  obtain ⟨hB', hN'⟩ := (theorem_4_11 A).2 _ _ hsplit
  exact ⟨hB'.symm, hN'.symm⟩

end BenIsraelGreville.Chapter04
