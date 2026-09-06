import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.LinearSolve.Stationary.Splitting

/-!
# Regular splittings

A splitting `A = M - N` of a real matrix is *regular* when `M⁻¹` and `N` are entrywise nonnegative,
and it converges exactly when `A` is invertible with `A⁻¹` entrywise nonnegative
([Saad][saad2003iterative], Definition 4.3 and Theorem 4.4). The engine is the nonnegative Neumann
criterion `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff` of
`Numlib/LinearAlgebra/Matrix/MMatrix`, applied to the iteration operator `G = M⁻¹ N`.
-/

open scoped Matrix

namespace Stationary.Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- **Regular splitting** (Saad, *Iterative Methods for Sparse Linear Systems*, Definition 4.3):
the splitting `A = M - N` is regular when `M⁻¹` and `N` are entrywise nonnegative. -/
def IsRegular (s : Splitting A) : Prop :=
  (Ring.inverse s.m).EntrywiseNonneg ∧ s.n.EntrywiseNonneg

namespace IsRegular

variable {s : Splitting A} (hs : s.IsRegular)
include hs

/-- The iteration operator `G = M⁻¹ N` of a regular splitting is entrywise nonnegative. -/
theorem entrywiseNonneg_iterationOperator : s.iterationOperator.EntrywiseNonneg := by
  rw [s.iterationOperator_eq]; exact hs.1.mul hs.2

/-- **Saad's Theorem 4.4** (*Iterative Methods for Sparse Linear Systems*): a regular splitting
`A = M - N` converges exactly when `A` is invertible with an entrywise nonnegative inverse.

Both directions go through the nonnegative Neumann criterion applied to `G = M⁻¹ N`, using
`1 - G = M⁻¹ A`. Forwards, `A = M (1 - G)` is a product of units and `A⁻¹ = (1 - G)⁻¹ M⁻¹` a
product of nonnegative matrices. Backwards, the identity `(1 - G)⁻¹ = A⁻¹ M = 1 + A⁻¹ N` — which
is Saad's `A⁻¹ N = (1 - G)⁻¹ G` in a form that needs no inverse of `N` — exhibits `(1 - G)⁻¹` as
nonnegative. -/
theorem complexSpectralRadius_lt_one_iff :
    s.iterationOperator.complexSpectralRadius < 1 ↔ IsUnit A ∧ A⁻¹.EntrywiseNonneg := by
  have hMinv : Ring.inverse s.m = s.m⁻¹ := (nonsing_inv_eq_ringInverse _).symm
  have hone : 1 - s.iterationOperator = s.m⁻¹ * A := by
    rw [s.one_sub_iterationOperator, hMinv]
  have hfactor : A = s.m * (1 - s.iterationOperator) := by
    rw [hone, ← mul_assoc, mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.1 s.isUnit), one_mul]
  rw [hs.entrywiseNonneg_iterationOperator.complexSpectralRadius_lt_one_iff]
  constructor
  · rintro ⟨hu, hnn⟩
    refine ⟨hfactor ▸ s.isUnit.mul hu, ?_⟩
    rw [hfactor, Matrix.mul_inv_rev, ← hMinv]
    exact hnn.mul hs.1
  · rintro ⟨hu, hnn⟩
    have hdet : IsUnit A.det := isUnit_iff_isUnit_det _ |>.1 hu
    have hunit : IsUnit (1 - s.iterationOperator) := by
      rw [hone]
      exact (isUnit_nonsing_inv_iff.2 s.isUnit).mul hu
    refine ⟨hunit, ?_⟩
    -- `(1 - G)⁻¹ = A⁻¹ M = A⁻¹ (A + N) = 1 + A⁻¹ N`.
    -- `A` occurs in the type `Splitting A` of `s`, so it cannot be rewritten; move the splitting
    -- identity to the form that replaces `s.m` instead.
    have hmA : s.m = A + s.n := sub_eq_iff_eq_add.mp s.m_sub_n
    have hinv : (1 - s.iterationOperator)⁻¹ = 1 + A⁻¹ * s.n := by
      rw [hone, Matrix.mul_inv_rev,
        nonsing_inv_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.1 s.isUnit), hmA, mul_add,
        nonsing_inv_mul _ hdet]
    rw [hinv]
    exact entrywiseNonneg_one.add (hnn.mul hs.2)

/-- Every regular splitting of an M-matrix converges (the remark after Saad's Theorem 4.4 in
*Iterative Methods for Sparse Linear Systems*): an M-matrix is invertible with a nonnegative
inverse, which is exactly the right-hand side of
`Stationary.Splitting.IsRegular.complexSpectralRadius_lt_one_iff`. -/
theorem complexSpectralRadius_lt_one_of_isMMatrix (hA : A.IsMMatrix) :
    s.iterationOperator.complexSpectralRadius < 1 :=
  hs.complexSpectralRadius_lt_one_iff.2 ⟨hA.isUnit, hA.inv_entrywiseNonneg⟩

end IsRegular

end Stationary.Splitting
