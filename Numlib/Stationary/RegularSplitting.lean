/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.Stationary.Splitting

/-!
# Regular splittings

A splitting $A = M - N$ of a real square matrix $A$, with $M$ invertible, is **regular** if $M^{-1}$
and $N$ are entrywise nonnegative ([saad2003iterative], Definition 4.3). A regular splitting
converges, that is, its iteration matrix $G = M^{-1} N$ has spectral radius $\rho(G) < 1$, if and
only if $A$ is invertible and $A^{-1}$ is entrywise nonnegative ([saad2003iterative], Theorem 4.4).
In particular, every regular splitting of an M-matrix converges. The proofs apply the nonnegative
Neumann criterion `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff` of
`Numlib.LinearAlgebra.Matrix.MMatrix` to the iteration matrix $G$.

## Main definitions

* `Stationary.Splitting.IsRegular`: the splitting $A = M - N$ has $M^{-1} \ge 0$ and $N \ge 0$
  entrywise.

## Main results

* `Stationary.Splitting.IsRegular.entrywiseNonneg_iterationOperator`: the iteration matrix of a
  regular splitting is entrywise nonnegative.
* `Stationary.Splitting.IsRegular.complexSpectralRadius_lt_one_iff`: a regular splitting converges
  if and only if $A$ is invertible with $A^{-1} \ge 0$.
* `Stationary.Splitting.IsRegular.complexSpectralRadius_lt_one_of_isMMatrix`: every regular
  splitting of an M-matrix converges.

## Proof outline

Both directions of the criterion use $1 - G = M^{-1} A$. If $\rho(G) < 1$, then $1 - G$ is
invertible with a nonnegative inverse, so $A = M (1 - G)$ is invertible and
$A^{-1} = (1 - G)^{-1} M^{-1}$ is a product of nonnegative matrices. Conversely, if $A^{-1} \ge 0$,
the identity $(1 - G)^{-1} = A^{-1} M = 1 + A^{-1} N$ shows that $(1 - G)^{-1}$ is nonnegative. This
identity is the relation $A^{-1} N = (1 - G)^{-1} G$ of [saad2003iterative] in a form that needs no
inverse of $N$.

## Implementation notes

* The spectral radius of a real matrix is `Matrix.complexSpectralRadius`, the spectral radius of its
  complexification.
* The matrix $M^{-1}$ is `Ring.inverse s.m`, and $N = M - A$ is `Stationary.Splitting.n`.
-/

open scoped Matrix

namespace Stationary.Splitting

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- A splitting $A = M - N$ of a real square matrix $A$, with $M$ invertible, is a **regular
splitting** if $M^{-1}$ and $N$ are entrywise nonnegative. This is Definition 4.3 of
[saad2003iterative].

The matrix $M^{-1}$ is `Ring.inverse s.m`, and $N = M - A$ is `Stationary.Splitting.n`. -/
def IsRegular (s : Splitting A) : Prop :=
  (Ring.inverse s.m).EntrywiseNonneg ∧ s.n.EntrywiseNonneg

namespace IsRegular

variable {s : Splitting A} (hs : s.IsRegular)
include hs

/-- Let $A = M - N$ be a regular splitting of a real square matrix $A$. Then its iteration matrix
$G = M^{-1} N$ is entrywise nonnegative.

The iteration matrix is `Stationary.Splitting.iterationOperator`, which is defined as
$1 - M^{-1} A$. -/
theorem entrywiseNonneg_iterationOperator : s.iterationOperator.EntrywiseNonneg := by
  rw [s.iterationOperator_eq]; exact hs.1.mul hs.2

/-- Let $A = M - N$ be a regular splitting of a real square matrix $A$, with iteration matrix
$G = M^{-1} N$. Then $\rho(G) < 1$ if and only if $A$ is invertible and $A^{-1}$ is entrywise
nonnegative. This is Theorem 4.4 of [saad2003iterative].

The spectral radius is `Matrix.complexSpectralRadius`. Both directions apply the nonnegative
Neumann criterion `Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff` to $G$, with
$1 - G = M^{-1} A$. -/
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

/-- Let $A$ be a real M-matrix and let $A = M - N$ be a regular splitting of $A$. Then the iteration
matrix satisfies $\rho(M^{-1} N) < 1$. This is the remark after Theorem 4.4 of
[saad2003iterative].

An M-matrix is invertible with an entrywise nonnegative inverse (`Matrix.IsMMatrix`). This is
the right-hand side of `Stationary.Splitting.IsRegular.complexSpectralRadius_lt_one_iff`. -/
theorem complexSpectralRadius_lt_one_of_isMMatrix (hA : A.IsMMatrix) :
    s.iterationOperator.complexSpectralRadius < 1 :=
  hs.complexSpectralRadius_lt_one_iff.2 ⟨hA.isUnit, hA.inv_entrywiseNonneg⟩

end IsRegular

end Stationary.Splitting
