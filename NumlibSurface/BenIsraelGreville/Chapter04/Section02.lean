/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.RankStabilization
import NumlibSurface.BenIsraelGreville.Chapter04.Section01

/-!
# The matrix index

Section 4.2 of [benIsrael2003generalized] defines the index by the first positive equality
of successive ranks. From the index onward the range and kernel of the powers are constant.

## Deviations from the source

* **Lemma 1(d)** (reading). The exponents under consideration are the positive exponents
  of the spectral inverse equations.
-/

namespace BenIsraelGreville.Chapter04

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Equations (5), (7), and (8)** of [benIsrael2003generalized], Chapter 4. For commuting
matrices $A,X$, the spectral inverse equations $A^kXA=A^k$ and $XAX=X$ can be written
$A^{k+1}X=A^k$ and $AX^2=X$. -/
theorem drazin_equations_iff (k : ℕ) (A X : Matrix n n ℂ) (h : Commute A X) :
    SatisfiesFirstPowerEquation k A X ∧ A.IsOuterInverse X ↔
      A ^ (k + 1) * X = A ^ k ∧ A * X ^ 2 = X := by
  rw [SatisfiesFirstPowerEquation, isOuterInverse_iff, pow_succ, pow_two,
    Matrix.mul_assoc (A ^ k) A X, h.eq, ← Matrix.mul_assoc (A ^ k) X A]
  rw [← Matrix.mul_assoc A X X, h.eq]

/-- **Definition 1** of [benIsrael2003generalized], Chapter 4. The matrix index is the
least positive $k$ for which $A^k$ and $A^{k+1}$ have the same rank. -/
noncomputable abbrev matrixIndex (A : Matrix n n ℂ) : ℕ :=
  A.rankStabilizationIndex

private theorem matrixIndex_eq_of_rank_pow_eq (A B : Matrix n n ℂ)
    (h : ∀ k : ℕ, (A ^ k).rank = (B ^ k).rank) :
    matrixIndex A = matrixIndex B := by
  have ha := A.rankStabilizationIndex_spec
  have hb := B.rankStabilizationIndex_spec
  refine le_antisymm ((A.rank_pow_eq_succ_iff hb.1).mp ?_) ((B.rank_pow_eq_succ_iff ha.1).mp ?_)
  · rw [h, h]
    exact hb.2
  · rw [← h, ← h]
    exact ha.2

/-- Transposing a complex square matrix leaves its index unchanged. -/
theorem matrixIndex_transpose (A : Matrix n n ℂ) :
    matrixIndex Aᵀ = matrixIndex A :=
  matrixIndex_eq_of_rank_pow_eq _ _ fun k => by rw [← transpose_pow, rank_transpose]

/-- Taking the conjugate transpose of a complex square matrix leaves its index unchanged. -/
theorem matrixIndex_conjTranspose (A : Matrix n n ℂ) :
    matrixIndex Aᴴ = matrixIndex A :=
  matrixIndex_eq_of_rank_pow_eq _ _ fun k => by rw [← conjTranspose_pow, rank_conjTranspose]

/-- **Lemma 1** of [benIsrael2003generalized], Chapter 4. The powers of $A$, $A^T$, and $A^H$
have ranks, ranges, and kernels constant from the index onward. At a positive exponent below
the index the range and kernel both differ from those at every strictly greater exponent.

**Reading.** Part (d) concerns positive exponents, as in the surrounding spectral equations.
With the positive-index convention, an invertible matrix has index one and already stabilizes
at exponent zero. -/
theorem lemma_4_1 (A : Matrix n n ℂ) (B : Matrix n n ℂ)
    (hB : B = A ∨ B = Aᵀ ∨ B = Aᴴ) :
    (∀ l : ℕ, matrixIndex A ≤ l →
      (B ^ matrixIndex A).rank = (B ^ l).rank ∧
        LinearMap.range (B ^ matrixIndex A).mulVecLin = LinearMap.range (B ^ l).mulVecLin ∧
        LinearMap.ker (B ^ matrixIndex A).mulVecLin = LinearMap.ker (B ^ l).mulVecLin) ∧
    (∀ k l : ℕ, 0 < k → k < matrixIndex A → k < l →
      LinearMap.range (B ^ k).mulVecLin ≠ LinearMap.range (B ^ l).mulVecLin ∧
        LinearMap.ker (B ^ k).mulVecLin ≠ LinearMap.ker (B ^ l).mulVecLin) := by
  have hBA : matrixIndex B = matrixIndex A := by
    rcases hB with rfl | rfl | rfl
    · rfl
    · exact matrixIndex_transpose A
    · exact matrixIndex_conjTranspose A
  rw [← hBA]
  constructor
  · intro l hl
    have h := B.rank_pow_eq_of_eq_succ B.rankStabilizationIndex_spec.2 hl
    exact ⟨h, (B.rank_pow_eq_iff_range_eq hl).mp h, (B.rank_pow_eq_iff_ker_eq hl).mp h⟩
  · intro k l hpos hbelow hkl
    have hne : (B ^ k).rank ≠ (B ^ l).rank := by
      intro eq
      have hstep : (B ^ (k + 1)).rank ≤ (B ^ k).rank := by
        rw [pow_succ]
        exact rank_mul_le_left _ _
      have hlstep : (B ^ l).rank ≤ (B ^ (k + 1)).rank :=
        Submodule.finrank_mono (B.antitone_range_mulVecLin_pow hkl)
      have h : (B ^ k).rank = (B ^ (k + 1)).rank :=
        le_antisymm (by exact eq.le.trans hlstep) hstep
      exact hbelow.not_ge ((B.rank_pow_eq_succ_iff hpos).mp h)
    exact ⟨hne ∘ (B.rank_pow_eq_iff_range_eq hkl.le).mpr,
      hne ∘ (B.rank_pow_eq_iff_ker_eq hkl.le).mpr⟩

/-- **Theorem 1, solvability criterion** of [benIsrael2003generalized], Chapter 4. For
positive $k$, the power equation $A^{k+1}X=A^k$ is solvable precisely when $k$ is at least
the index of $A$. -/
theorem theorem_4_1_solvable (A : Matrix n n ℂ) {k : ℕ} (hk : 0 < k) :
    (∃ X : Matrix n n ℂ, A ^ (k + 1) * X = A ^ k) ↔ matrixIndex A ≤ k := by
  rw [← A.rank_pow_eq_succ_iff hk]
  constructor
  · rintro ⟨X, hX⟩
    refine le_antisymm ?_ ?_
    · calc
        (A ^ k).rank = (A ^ (k + 1) * X).rank := congrArg rank hX.symm
        _ ≤ (A ^ (k + 1)).rank := rank_mul_le_left _ _
    · rw [pow_succ]
      exact rank_mul_le_left _ _
  · intro heq
    let B := A ^ (k + 1)
    refine ⟨B.pinv * A ^ k, ext_iff_mulVec.mpr fun x => ?_⟩
    have hx : (A ^ k).mulVecLin x ∈ LinearMap.range B.mulVecLin := by
      rw [← (A.rank_pow_eq_iff_range_eq (Nat.le_succ k)).mp heq]
      exact LinearMap.mem_range_self _ _
    obtain ⟨y, hy⟩ := hx
    change B.mulVecLin y = (A ^ k).mulVecLin x at hy
    change (B * (B.pinv * A ^ k)).mulVecLin x = (A ^ k).mulVecLin x
    rw [mulVecLin_mul, LinearMap.comp_apply, mulVecLin_mul, LinearMap.comp_apply, ← hy,
      ← LinearMap.comp_apply, ← mulVecLin_mul, ← LinearMap.comp_apply, ← mulVecLin_mul,
      mul_pinv_mul_self]

end BenIsraelGreville.Chapter04
