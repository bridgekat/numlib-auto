import Mathlib.Data.Int.Interval
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal

/-!
# Index conventions

Appendix A.1 uses finite index intervals and restrictions of vectors and matrices.
These are aliases for Mathlib intervals, function restriction, and matrix submatrices.
The Kronecker delta is `Pi.single i 1`, also the entry function of the identity matrix.
-/

namespace CartisGouldToint.AppendixA.Section01

/-- The inclusive finite integer interval `[p : q]`, empty when `q < p`. -/
abbrev integerInterval (p q : ℤ) : Finset ℤ := Finset.Icc p q

/-- Membership in the textbook's integer interval. -/
@[simp] theorem mem_integerInterval {p q i : ℤ} :
    i ∈ integerInterval p q ↔ p ≤ i ∧ i ≤ q := Finset.mem_Icc

/-- An integer interval with reversed endpoints is empty. -/
theorem integerInterval_eq_empty {p q : ℤ} (h : q < p) :
    integerInterval p q = ∅ := Finset.Icc_eq_empty_of_lt h

/-- The subvector indexed by a subset is ordinary function restriction. -/
abbrev subvector {ι α : Type*} (v : ι → α) (I : Set ι) : I → α := I.domRestrict v

/-- Restriction preserves the value at each retained index. -/
@[simp] theorem subvector_apply {ι α : Type*} (v : ι → α) (I : Set ι) (i : I) :
    subvector v I i = v i := rfl

/-- The submatrix indexed by two subsets is Mathlib's `Matrix.submatrix`. -/
abbrev submatrix {ι κ α : Type*} (A : Matrix ι κ α) (I : Set ι) (J : Set κ) :
    Matrix I J α := A.submatrix Subtype.val Subtype.val

/-- Submatrix entries are the corresponding original entries. -/
@[simp] theorem submatrix_apply {ι κ α : Type*} (A : Matrix ι κ α)
    (I : Set ι) (J : Set κ) (i : I) (j : J) : submatrix A I J i j = A i j := rfl

/-- The Kronecker delta notation, using Mathlib's single-coordinate function. -/
abbrev kroneckerDelta {ι : Type*} [DecidableEq ι] (i j : ι) : ℝ := (Pi.single i 1 : ι → ℝ) j

/-- The delta is one on the diagonal and zero off it. -/
theorem kroneckerDelta_eq {ι : Type*} [DecidableEq ι] (i j : ι) :
    kroneckerDelta i j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j; simp [kroneckerDelta]
  · simp [kroneckerDelta, h, Ne.symm h]

/-- Identity matrix entries are Kronecker deltas. -/
theorem identity_apply {ι : Type*} [DecidableEq ι] (i j : ι) :
    (1 : Matrix ι ι ℝ) i j = kroneckerDelta i j := by
  simp [Matrix.one_apply, kroneckerDelta_eq]

end CartisGouldToint.AppendixA.Section01
