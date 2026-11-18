/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter04.Section05
import NumlibSurface.BenIsraelGreville.Chapter04.Section06

/-!
# Spectral properties of the Drazin inverse

Section 4.7 of [benIsrael2003generalized] relaxes spectral inversion at
zero by retaining the generalized eigenspace and allowing the grades to change.
-/

namespace BenIsraelGreville.Chapter04

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Theorem 9** of [benIsrael2003generalized], Chapter 4.
An S-inverse satisfying either Penrose inverse equation has index one,
as does the original matrix. -/
theorem theorem_4_9 {A X : Matrix n n ℂ} (h : IsSInverse A X)
    (hi : A.IsInnerInverse X ∨ A.IsOuterInverse X) :
    matrixIndex A = 1 ∧ matrixIndex X = 1 :=
  h.matrixIndex_eq_one hi

/-- **Definition 3** of [benIsrael2003generalized], Chapter 4.
S-prime inversion preserves exact grades at reciprocal nonzero
eigenvalues and preserves the maximal generalized zero-eigenspace. -/
def IsSPrimeInverse (A X : Matrix n n ℂ) : Prop :=
  (∀ μ : ℂ, μ ≠ 0 → ∀ v p, IsVectorOfGrade A μ v p ↔ IsVectorOfGrade X μ⁻¹ v p) ∧
    End.maxGenEigenspace A.mulVecLin 0 = End.maxGenEigenspace X.mulVecLin 0

omit [DecidableEq n] in
/-- S-prime inversion is symmetric. -/
theorem IsSPrimeInverse.symm {A X : Matrix n n ℂ} (h : IsSPrimeInverse A X) :
    IsSPrimeInverse X A := by
  refine ⟨?_, h.2.symm⟩
  intro μ hμ v p
  simpa only [inv_inv] using (h.1 μ⁻¹ (inv_ne_zero hμ) v p).symm

/-- The range and kernel of the Drazin inverse equal those of every
matrix power at or above the stabilization index. -/
theorem drazinInverse_range_ker_eq_stablePow (A : Matrix n n ℂ) {l : ℕ}
    (hl : matrixIndex A ≤ l) :
    (drazinInverse A).mulVecLin.range = (A ^ l).mulVecLin.range ∧
      (drazinInverse A).mulVecLin.ker = (A ^ l).mulVecLin.ker := by
  let D := drazinInverse A
  have hD := (isDrazinInverseAt_drazinInverse A).mono hl
  have hd : A ^ l * D ^ (l + 1) = D := hD.pow_mul_pow_succ l
  have hd' : D ^ (l + 1) * A ^ l = D := ((hD.commute.pow_pow l (l + 1)).eq.symm).trans hd
  constructor
  · apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      refine ⟨(D ^ (l + 1)) *ᵥ v, ?_⟩
      change (A ^ l) *ᵥ ((D ^ (l + 1)) *ᵥ v) = D *ᵥ v
      rw [mulVec_mulVec, hd]
    · rintro _ ⟨v, rfl⟩
      refine ⟨(A ^ (l + 1)) *ᵥ v, ?_⟩
      change D *ᵥ ((A ^ (l + 1)) *ᵥ v) = (A ^ l) *ᵥ v
      rw [mulVec_mulVec, hD.stable_left]
  · ext v
    change D *ᵥ v = 0 ↔ (A ^ l) *ᵥ v = 0
    constructor
    · intro hv
      rw [← hD.stable, ← mulVec_mulVec, hv, mulVec_zero]
    · intro hv
      rw [← hd', ← mulVec_mulVec, hv, mulVec_zero]

/-- The Drazin inverse always has index one in the textbook convention. -/
theorem matrixIndex_drazinInverse (A : Matrix n n ℂ) : matrixIndex (drazinInverse A) = 1 := by
  have h := (isDrazinInverseAt_drazinInverse A).isGroupInverse_square_mul
  exact (theorem_4_2 (drazinInverse A)).mp ⟨_, h, fun _ hx => hx.unique h⟩

/-- **Theorem 10** of [benIsrael2003generalized], Chapter 4.
A square matrix and its Drazin inverse are S-prime inverses. -/
theorem theorem_4_10 (A : Matrix n n ℂ) : IsSPrimeInverse A (drazinInverse A) := by
  have hD := isDrazinInverseAt_drazinInverse A
  constructor
  · intro μ hμ v p
    refine ⟨lemma_4_4 A (drazinInverse A) hD.stable_left hμ, ?_⟩
    intro hv
    have hr : A * drazinInverse A ^ (1 + 1) = drazinInverse A ^ 1 := by
      simpa only [pow_one] using hD.mul_sq
    simpa only [inv_inv] using lemma_4_4 (drazinInverse A) A hr (inv_ne_zero hμ) hv
  · rw [maxGenEigenspace_zero_eq_stableKer A le_rfl,
      maxGenEigenspace_zero_eq_stableKer (drazinInverse A) (matrixIndex_drazinInverse A).le,
      pow_one]
    exact (drazinInverse_range_ker_eq_stablePow A le_rfl).2.symm

/-- S-prime inverses have equal stable kernels and stable ranges. -/
theorem IsSPrimeInverse.drazinInverse_range_ker_eq {A X : Matrix n n ℂ}
    (h : IsSPrimeInverse A X) :
    (drazinInverse A).mulVecLin.range = (drazinInverse X).mulVecLin.range ∧
      (drazinInverse A).mulVecLin.ker = (drazinInverse X).mulVecLin.ker := by
  obtain ⟨hRa, hKa⟩ := drazinInverse_range_ker_eq_stablePow A le_rfl
  obtain ⟨hRx, hKx⟩ := drazinInverse_range_ker_eq_stablePow X le_rfl
  refine ⟨?_, ?_⟩
  · rw [hRa, hRx, stableRange_eq_nonzeroSpectralSubspace A le_rfl,
      stableRange_eq_nonzeroSpectralSubspace X le_rfl, End.spectralSubspace, End.spectralSubspace]
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ => ?_)
    · rw [maxGenEigenspace_eq_of_grade_iff (h.1 μ hμ)]
      exact le_iSup₂_of_le μ⁻¹ (inv_ne_zero hμ) le_rfl
    · rw [maxGenEigenspace_eq_of_grade_iff (h.symm.1 μ hμ)]
      exact le_iSup₂_of_le μ⁻¹ (inv_ne_zero hμ) le_rfl
  · rw [hKa, hKx, ← maxGenEigenspace_zero_eq_stableKer A le_rfl,
      ← maxGenEigenspace_zero_eq_stableKer X le_rfl]
    exact h.2

end BenIsraelGreville.Chapter04
