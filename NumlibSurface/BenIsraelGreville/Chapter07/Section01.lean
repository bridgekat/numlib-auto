/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.BenIsraelGreville.Chapter02.Section06
import NumlibSurface.BenIsraelGreville.Chapter04.Section06

/-!
# Outer inverses in generalized inverse computation

Section 7.1 of [benIsrael2003generalized] identifies the Moore–Penrose and Drazin
inverses as outer inverses with prescribed range and null space.
-/

namespace BenIsraelGreville.Chapter07

open Matrix Module
open BenIsraelGreville.Chapter02 (prescribedOuterInverses)

private theorem unique_prescribedOuterInverse
    {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m n ℂ} {X : Matrix n m ℂ}
    {R : Submodule ℂ (n → ℂ)} {S : Submodule ℂ (m → ℂ)}
    (hX : X ∈ prescribedOuterInverses A R S) :
    ∀ Y ∈ prescribedOuterInverses A R S, Y = X := by
  obtain ⟨ho, hr, hk⟩ := hX
  have hdim : finrank ℂ R + finrank ℂ S = Fintype.card m := by
    rw [← hr, ← hk, LinearMap.finrank_range_add_finrank_ker, finrank_fintype_fun_eq_card]
  have h₁ := isOuterInverse_iff_isInnerInverse.mp ho
  obtain ⟨hComp, -⟩ := Chapter02.theorem_8.1 _ h₁.isIdempotentElem_mul_rev
  have hR : (A * X).mulVecLin.range = R.map A.mulVecLin := by
    rw [mulVecLin_mul, LinearMap.range_comp, hr]
  rw [hR, h₁.ker_mul_rev, hk] at hComp
  intro Y hY
  exact ((Chapter02.theorem_14 A R S hdim).mpr hComp).unique hY ⟨ho, hr, hk⟩

/-- **Section 7.1** of [benIsrael2003generalized]. The Moore–Penrose inverse
is the unique outer inverse of $A$ with the range and kernel of $A^H$. -/
theorem pinv_unique_outerInverse_range_ker {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) :
    A.pinv ∈ prescribedOuterInverses A Aᴴ.mulVecLin.range Aᴴ.mulVecLin.ker ∧
      ∀ X ∈ prescribedOuterInverses A Aᴴ.mulVecLin.range Aᴴ.mulVecLin.ker, X = A.pinv := by
  have h := (Chapter02.exercise_38 A).1
  have hp : A.pinv ∈ prescribedOuterInverses A Aᴴ.mulVecLin.range Aᴴ.mulVecLin.ker :=
    ⟨A.pinv_mul_self_mul_pinv, h.2.1, h.2.2⟩
  exact ⟨hp, unique_prescribedOuterInverse hp⟩

/-- **Section 7.1** of [benIsrael2003generalized]. At any exponent at least
the matrix index, the Drazin inverse is the unique outer inverse of $A$
with the range and kernel of that power of $A$. -/
theorem drazin_unique_outerInverse_range_ker {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) {k : ℕ} (hk : Chapter04.matrixIndex A ≤ k) :
    Chapter04.drazinInverse A ∈
        prescribedOuterInverses A (A ^ k).mulVecLin.range (A ^ k).mulVecLin.ker ∧
      ∀ X ∈ prescribedOuterInverses A (A ^ k).mulVecLin.range (A ^ k).mulVecLin.ker,
        X = Chapter04.drazinInverse A := by
  let X := Chapter04.drazinInverse A
  have h := (Chapter04.isDrazinInverseAt_drazinInverse A).mono hk
  change IsDrazinInverseAt k A X at h
  have hr : X.mulVecLin.range = (A ^ k).mulVecLin.range := by
    apply le_antisymm
    · rw [← h.pow_mul_pow_succ k, mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    · rw [← h.stable_left, mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
  have hK : X.mulVecLin.ker = (A ^ k).mulVecLin.ker := by
    apply le_antisymm
    · rw [← h.stable, mulVecLin_mul]
      exact LinearMap.ker_le_ker_comp _ _
    · rw [← h.pow_mul_pow_succ k, (h.commute.pow_pow k (k + 1)).eq, mulVecLin_mul]
      exact LinearMap.ker_le_ker_comp _ _
  have hX : X ∈ prescribedOuterInverses A (A ^ k).mulVecLin.range (A ^ k).mulVecLin.ker :=
    ⟨h.outer, hr, hK⟩
  exact ⟨hX, unique_prescribedOuterInverse hX⟩

/-- **Section 7.1** of [benIsrael2003generalized]. When the index of $A$ is at
most one, its Drazin inverse is a group inverse and has the range and kernel of $A$. -/
theorem groupInverse_unique_outerInverse_range_ker {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : Chapter04.matrixIndex A ≤ 1) :
    IsGroupInverse A (Chapter04.drazinInverse A) ∧
      Chapter04.drazinInverse A ∈ prescribedOuterInverses A A.mulVecLin.range A.mulVecLin.ker ∧
      ∀ X ∈ prescribedOuterInverses A A.mulVecLin.range A.mulVecLin.ker,
        X = Chapter04.drazinInverse A := by
  exact ⟨(Chapter04.isDrazinInverseAt_drazinInverse A).mono hA,
    by simpa only [pow_one] using drazin_unique_outerInverse_range_ker A hA⟩

end BenIsraelGreville.Chapter07
