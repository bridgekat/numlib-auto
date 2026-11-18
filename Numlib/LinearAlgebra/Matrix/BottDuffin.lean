/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.GeneralizedInverse

/-!
# Bott–Duffin inverse

For an idempotent matrix $P$, the Bott–Duffin inverse associated with $P$ is
$B=P(AP+I-P)^{-1}$. When the indicated ordinary inverse exists, $B$ is a reflexive
inverse of $AP$, $PA$, and $PAP$. The Bott–Duffin inverse of $B$ at the same projection
is the compression $PAP$.
-/

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- The Bott–Duffin inverse of $A$ along the idempotent $P$ is $P(AP+I-P)^{-1}$. -/
noncomputable def bottDuffin (A P : Matrix n n K) : Matrix n n K :=
  P * (A * P + (1 - P))⁻¹

/-- The Bott–Duffin inverse $B$ satisfies $BAP=P=PAB$ and $PB=B=BP$. -/
theorem bottDuffin_identities {A P : Matrix n n K} (hP : IsIdempotentElem P)
    (hU : IsUnit (A * P + (1 - P))) :
    bottDuffin A P * A * P = P ∧ P * A * bottDuffin A P = P ∧
      P * bottDuffin A P = bottDuffin A P ∧
      bottDuffin A P * P = bottDuffin A P := by
  let Q := 1 - P
  let M := A * P + Q
  let B := bottDuffin A P
  have hMdet := (isUnit_iff_isUnit_det M).mp hU
  have hBM : B * M = P := by
    change (P * M⁻¹) * M = P
    rw [mul_assoc, nonsing_inv_mul _ hMdet, mul_one]
  have hMQ : M * Q = Q := by
    change (A * P + (1 - P)) * (1 - P) = 1 - P
    rw [add_mul, mul_assoc A, hP.mul_one_sub_self, mul_zero, hP.one_sub.eq, zero_add]
  have hBQ : B * Q = 0 := by
    rw [← hMQ, ← mul_assoc, hBM]
    exact hP.mul_one_sub_self
  have hBAP : B * A * P = P := by
    change B * (A * P + Q) = P at hBM
    rw [mul_add, ← mul_assoc B A P, hBQ, add_zero] at hBM
    exact hBM
  have hPB : P * B = B := by
    change P * (P * M⁻¹) = P * M⁻¹
    rw [← mul_assoc, hP.eq]
  have hBP : B * P = B := by
    change B * (1 - P) = 0 at hBQ
    rw [mul_sub, mul_one, sub_eq_zero] at hBQ
    exact hBQ.symm
  have hPM : P * M = P * A * P := by
    change P * (A * P + (1 - P)) = P * A * P
    rw [mul_add, hP.mul_one_sub_self, add_zero, mul_assoc]
  have hPAB : P * A * B = P := calc
    P * A * B = (P * A * P) * M⁻¹ := by
      change P * A * (P * M⁻¹) = _
      simp only [mul_assoc]
    _ = P := by rw [← hPM, mul_assoc, mul_nonsing_inv _ hMdet, mul_one]
  exact ⟨hBAP, hPAB, hPB, hBP⟩

/-- The Bott–Duffin inverse is a reflexive inverse of each of $AP$, $PA$, and $PAP$. -/
theorem bottDuffin_reflexive {A P : Matrix n n K} (hP : IsIdempotentElem P)
    (hU : IsUnit (A * P + (1 - P))) :
    ∀ C ∈ ({A * P, P * A, P * A * P} : Set (Matrix n n K)),
      C.IsInnerInverse (bottDuffin A P) ∧ C.IsOuterInverse (bottDuffin A P) := by
  let B := bottDuffin A P
  obtain ⟨hBAP, hPAB, hPB, hBP⟩ := bottDuffin_identities hP hU
  change B * A * P = P at hBAP
  change P * A * B = P at hPAB
  change P * B = B at hPB
  change B * P = B at hBP
  intro C hC
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with rfl | rfl | rfl
  · rw [isInnerInverse_iff, isOuterInverse_iff]
    change (A * P) * B * (A * P) = A * P ∧ B * (A * P) * B = B
    constructor
    · have h : (A * P) * B * (A * P) = A * (P * B) * A * P := by
        simp only [mul_assoc]
      rw [h, hPB, mul_assoc A B A, mul_assoc A (B * A) P, hBAP]
    · rw [← mul_assoc B A P, hBAP, hPB]
  · rw [isInnerInverse_iff, isOuterInverse_iff]
    change (P * A) * B * (P * A) = P * A ∧ B * (P * A) * B = B
    constructor
    · rw [hPAB, ← mul_assoc, hP.eq]
    · rw [← mul_assoc B P A, hBP]
      calc
        B * A * B = B * (P * A * B) := by rw [← mul_assoc, ← mul_assoc, hBP]
        _ = B := by rw [hPAB, hBP]
  · rw [isInnerInverse_iff, isOuterInverse_iff]
    change (P * A * P) * B * (P * A * P) = P * A * P ∧
      B * (P * A * P) * B = B
    have hCB : (P * A * P) * B = P := by rw [mul_assoc (P * A), hPB, hPAB]
    have hBC : B * (P * A * P) = P := by rw [← mul_assoc, ← mul_assoc B P A, hBP, hBAP]
    constructor
    · rw [hCB, ← mul_assoc P (P * A) P, ← mul_assoc P P A, hP.eq]
    · rw [hBC, hPB]

/-- Applying the construction twice at the same projection gives $PAP$. The second
ordinary inverse exists under the hypothesis for the first. -/
theorem bottDuffin_bottDuffin {A P : Matrix n n K} (hP : IsIdempotentElem P)
    (hU : IsUnit (A * P + (1 - P))) :
    IsUnit (bottDuffin A P * P + (1 - P)) ∧
      bottDuffin (bottDuffin A P) P = P * A * P := by
  let B := bottDuffin A P
  let C := P * A * P
  let Q := 1 - P
  obtain ⟨hBAP, hPAB, hPB, hBP⟩ := bottDuffin_identities hP hU
  change B * A * P = P at hBAP
  change P * A * B = P at hPAB
  change P * B = B at hPB
  change B * P = B at hBP
  have hBC : B * C = P := by
    change B * (P * A * P) = P
    rw [← mul_assoc, ← mul_assoc B P A, hBP, hBAP]
  have hBQ : B * Q = 0 := by
    change B * (1 - P) = 0
    rw [mul_sub, mul_one, hBP, sub_self]
  have hQC : Q * C = 0 := by
    change Q * (P * A * P) = 0
    rw [← mul_assoc, ← mul_assoc, hP.one_sub_mul_self, zero_mul, zero_mul]
  have hMC : (B * P + Q) * (C + Q) = 1 := by
    rw [hBP, add_mul, mul_add, mul_add, hBC, hBQ, hQC, hP.one_sub.eq, add_zero, zero_add]
    exact add_sub_cancel _ _
  refine ⟨isUnit_iff_exists_inv.mpr ⟨C + Q, hMC⟩, ?_⟩
  change P * (B * P + Q)⁻¹ = C
  rw [inv_eq_right_inv hMC, mul_add, hP.mul_one_sub_self, add_zero]
  change P * (P * A * P) = P * A * P
  rw [← mul_assoc, ← mul_assoc, hP.eq]

end Matrix
