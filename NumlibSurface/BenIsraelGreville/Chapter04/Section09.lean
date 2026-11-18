/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter04.Section08

/-!
# Quasi-commuting inverses

Section 4.9 of [benIsrael2003generalized] characterizes quasi-commuting
inverses by their Drazin and nilpotent parts.
-/

namespace BenIsraelGreville.Chapter04

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Section 4.9** of [benIsrael2003generalized].
Quasi-commuting inverses are reflexive inverses, each commuting with a
common positive power of the other. -/
def AreQuasiCommutingInverses (A X : Matrix n n ℂ) : Prop :=
  A.IsInnerInverse X ∧ A.IsOuterInverse X ∧
    ∃ k : ℕ, 0 < k ∧ Commute (A ^ k) X ∧ Commute A (X ^ k)

/-- Quasi-commuting inversion is symmetric. -/
theorem AreQuasiCommutingInverses.symm {A X : Matrix n n ℂ}
    (h : AreQuasiCommutingInverses A X) : AreQuasiCommutingInverses X A := by
  obtain ⟨hi, ho, k, hk, hc, hd⟩ := h
  exact ⟨ho, hi, k, hk, hd.symm, hc.symm⟩

private theorem left_power_eq_of_inner_commute {A X : Matrix n n ℂ} {k : ℕ} (hk : 0 < k)
    (hI : A.IsInnerInverse X) (hC : Commute (A ^ k) X) :
    X * A ^ (k + 1) = A ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [pow_succ A (j + 1), ← mul_assoc, ← hC.eq, pow_succ A j, mul_assoc (A ^ j),
    mul_assoc (A ^ j), isInnerInverse_iff.mp hI]

private theorem cancel_left_powers_of_step {M : Type*} [Monoid M] {A X : M}
    {l : ℕ} (h : A * X ^ (l + 1) = X ^ l) (j : ℕ) :
    A ^ j * X ^ (l + j) = X ^ l := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      _ = A ^ j * (A * (X ^ (l + 1) * X ^ j)) := by
        rw [pow_succ, ← pow_add, show l + (j + 1) = l + 1 + j by omega, mul_assoc]
      _ = A ^ j * X ^ (l + j) := by rw [← mul_assoc A, h, ← pow_add]
      _ = _ := ih

/-- **Theorem 13** of [benIsrael2003generalized], Chapter 4.
Quasi-commuting inverses have reciprocal nonzero grades and equal
maximal generalized zero-eigenspaces. -/
theorem theorem_4_13 {A X : Matrix n n ℂ} (h : AreQuasiCommutingInverses A X) :
    IsSPrimeInverse A X := by
  obtain ⟨hi, ho, k, hk, hc, hd⟩ := h
  let m := max (matrixIndex A) (matrixIndex X)
  let l := k * m
  have hmA : matrixIndex A ≤ m := le_max_left _ _
  have hmX : matrixIndex X ≤ m := le_max_right _ _
  have hml : m ≤ l := by
    simpa only [one_mul, l] using Nat.mul_le_mul_right m (show 1 ≤ k from hk)
  have hlA := hmA.trans hml
  have hlX := hmX.trans hml
  have hl : 0 < l := A.rankStabilizationIndex_spec.1.trans_le hlA
  have hAX : Commute (A ^ l) X := by
    simpa only [l, pow_mul] using hc.pow_left m
  have hXA : Commute (X ^ l) A := by
    simpa only [l, pow_mul] using hd.symm.pow_left m
  have hleft := left_power_eq_of_inner_commute hl hi hAX
  have hright := left_power_eq_of_inner_commute hl ho hXA
  constructor
  · intro μ hμ v p
    refine ⟨lemma_4_4 A X hleft hμ, fun hv => ?_⟩
    simpa only [inv_inv] using lemma_4_4 X A hright (inv_ne_zero hμ) hv
  · rw [maxGenEigenspace_zero_eq_stableKer A hlA, maxGenEigenspace_zero_eq_stableKer X hlX]
    have hK {B Y : Matrix n n ℂ} (hC : Commute (B ^ l) Y)
        (hStep : B * Y ^ (l + 1) = Y ^ l) :
        (B ^ l).mulVecLin.ker ≤ (Y ^ l).mulVecLin.ker := by
      intro v hv
      change (B ^ l) *ᵥ v = 0 at hv
      change (Y ^ l) *ᵥ v = 0
      calc
        _ = (B ^ l * Y ^ (l + l)) *ᵥ v :=
          congrArg (fun M : Matrix n n ℂ => M *ᵥ v) (cancel_left_powers_of_step hStep l).symm
        _ = (Y ^ (l + l) * B ^ l) *ᵥ v :=
          congrArg (fun M : Matrix n n ℂ => M *ᵥ v) (hC.pow_right (l + l)).eq
        _ = 0 := by rw [← mulVec_mulVec, hv, mulVec_zero]
    exact le_antisymm (hK hAX hright) (hK hXA hleft)

/-- For exchanged cores and Drazin inverses, the first Penrose equation
reduces to the first Penrose equation for the nilpotent parts. -/
theorem innerInverse_iff_nilpotentPart_of_drazinInverse_eq_groupInvertiblePart
    {A X : Matrix n n ℂ} (h : drazinInverse X = groupInvertiblePart A) :
    A.IsInnerInverse X ↔ (nilpotentPart A).IsInnerInverse (nilpotentPart X) := by
  have hcore := groupInvertiblePart_eq_drazinInverse_of_drazinInverse_eq_groupInvertiblePart h
  let B := groupInvertiblePart A
  let C := groupInvertiblePart X
  let N := nilpotentPart A
  let M := nilpotentPart X
  have hBA : B + N = A := groupInvertiblePart_add_nilpotentPart A
  have hCX : C + M = X := groupInvertiblePart_add_nilpotentPart X
  have hBM : B * M = 0 := by
    change groupInvertiblePart A * nilpotentPart X = 0
    rw [← h]
    exact (drazinInverse_mul_nilpotentPart X).1
  have hMB : M * B = 0 := by
    change nilpotentPart X * groupInvertiblePart A = 0
    rw [← h]
    exact (drazinInverse_mul_nilpotentPart X).2
  have hCN : C * N = 0 := by
    change groupInvertiblePart X * nilpotentPart A = 0
    rw [hcore]
    exact (drazinInverse_mul_nilpotentPart A).1
  have hNC : N * C = 0 := by
    change nilpotentPart A * groupInvertiblePart X = 0
    rw [hcore]
    exact (drazinInverse_mul_nilpotentPart A).2
  have hBCB : B * C * B = B := by
    change groupInvertiblePart A * groupInvertiblePart X * groupInvertiblePart A = _
    rw [hcore]
    exact (_root_.isGroupInverse_iff.mp (isGroupInverse_drazinInverse_groupInvertiblePart A)).2.1
  have hAXA : A * X * A = B + N * M * N := calc
    _ = (B + N) * (C + M) * (B + N) := by rw [hBA, hCX]
    _ = _ := by
      simp only [add_mul, mul_add, hBM, hNC, add_zero, zero_add, mul_assoc B C N, hCN,
        mul_zero, mul_assoc N M B, hMB, hBCB]
  rw [isInnerInverse_iff, isInnerInverse_iff, hAXA]
  exact ⟨fun he => add_left_cancel (he.trans hBA.symm), fun he => by rw [he]; exact hBA⟩

/-- **Corollary 4** of [benIsrael2003generalized], Chapter 4.
Quasi-commutation is equivalent to exchanged Drazin inverses and
group-invertible parts and reflexive inversion of the nilpotent parts. -/
theorem corollary_4_4 (A X : Matrix n n ℂ) :
    AreQuasiCommutingInverses A X ↔
      drazinInverse X = groupInvertiblePart A ∧
        (nilpotentPart A).IsInnerInverse (nilpotentPart X) ∧
        (nilpotentPart A).IsOuterInverse (nilpotentPart X) := by
  constructor
  · intro h
    have hd := (theorem_4_12 (Or.inl h.1)).mp (theorem_4_13 h)
    have hd' := groupInvertiblePart_eq_drazinInverse_of_drazinInverse_eq_groupInvertiblePart hd
    exact ⟨hd, (innerInverse_iff_nilpotentPart_of_drazinInverse_eq_groupInvertiblePart hd).mp h.1,
      (innerInverse_iff_nilpotentPart_of_drazinInverse_eq_groupInvertiblePart hd'.symm).mp h.2.1⟩
  · rintro ⟨hd, hi, ho⟩
    have hd' := groupInvertiblePart_eq_drazinInverse_of_drazinInverse_eq_groupInvertiblePart hd
    let l := max (matrixIndex A) (matrixIndex X)
    have hA : matrixIndex A ≤ l := le_max_left _ _
    have hX : matrixIndex X ≤ l := le_max_right _ _
    refine ⟨(innerInverse_iff_nilpotentPart_of_drazinInverse_eq_groupInvertiblePart hd).mpr hi,
      (innerInverse_iff_nilpotentPart_of_drazinInverse_eq_groupInvertiblePart hd'.symm).mpr ho,
      l, A.rankStabilizationIndex_spec.1.trans_le hA, ?_, ?_⟩
    · rw [← groupInvertiblePart_pow_eq A hA, ← hd]
      exact (isDrazinInverseAt_drazinInverse X).commute.symm.pow_left l
    · rw [← groupInvertiblePart_pow_eq X hX, hd']
      exact (isDrazinInverseAt_drazinInverse A).commute.pow_right l

end BenIsraelGreville.Chapter04
