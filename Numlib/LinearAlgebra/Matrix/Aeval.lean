/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly` (the polynomial lemmas) and
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse` (the commutation lemmas).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.Block
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Polynomials evaluated at matrices

Evaluating a polynomial at a matrix (`Polynomial.aeval`) commutes with the structural operations
on matrices: block diagonal matrices (`Matrix.aeval_blockDiagonal'`,
`Matrix.aeval_fromBlocks_zero`),
the transpose (`Matrix.aeval_transpose`, hence `Matrix.minpoly_transpose`) and an entrywise ring
endomorphism of the scalars (`Matrix.map_aeval`, Mathlib's `Polynomial.map_aeval_eq_aeval_map`
for `φ.mapMatrix`). Whatever commutes with an element of a monoid with zero commutes with its ring
inverse (`Commute.ringInverse_right`, `Commute.ringInverse_left`), so whatever commutes with a
matrix commutes with its nonsingular inverse (`Matrix.commute_nonsing_inv_right`,
`Matrix.commute_nonsing_inv_left`).

These are the algebraic inputs of the matrix forms of the primary functional calculus
(`Numlib/Analysis/Matrix/Function/Basic`).
-/

open Polynomial

section RingInverse

variable {M₀ : Type*} [MonoidWithZero M₀] {b c : M₀}

/-- Whatever commutes with `b` commutes with its ring inverse `Ring.inverse b` (which is `0` when
`b` is not a unit). Mathlib has the two-sided `Commute.ringInverse_ringInverse`. -/
theorem Commute.ringInverse_right (h : Commute c b) : Commute c (Ring.inverse b) := by
  by_cases hb : IsUnit b
  · obtain ⟨u, rfl⟩ := hb
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hb]
    exact Commute.zero_right c

/-- The ring inverse `Ring.inverse b` commutes with whatever commutes with `b`. -/
theorem Commute.ringInverse_left (h : Commute b c) : Commute (Ring.inverse b) c :=
  h.symm.ringInverse_right.symm

end RingInverse

namespace Matrix

section CommSemiring

variable {R : Type*} [CommSemiring R] {n : Type*} [Fintype n] [DecidableEq n]

/-- Polynomials commute with `blockDiagonal'`. -/
theorem aeval_blockDiagonal' {o : Type*} [Fintype o] [DecidableEq o] {m : o → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (M : ∀ i, Matrix (m i) (m i) R) (p : R[X]) :
    aeval (blockDiagonal' M) p = blockDiagonal' fun i => aeval (M i) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, ← blockDiagonal'_add]
    congr 1
    funext i
    rw [Pi.add_apply, map_add]
  | monomial k c =>
    simp only [aeval_monomial, ← Algebra.smul_def, ← blockDiagonal'_pow, ← blockDiagonal'_smul]
    rfl

/-- Polynomials commute with block diagonal `fromBlocks`. -/
theorem aeval_fromBlocks_zero {l : Type*} [Fintype l] [DecidableEq l] (B : Matrix l l R)
    (C : Matrix n n R) (p : R[X]) :
    aeval (fromBlocks B 0 0 C) p = fromBlocks (aeval B p) 0 0 (aeval C p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, map_add, map_add, fromBlocks_add]
    simp only [add_zero]
  | monomial k c =>
    simp only [aeval_monomial, ← Algebra.smul_def, fromBlocks_diagonal_pow, fromBlocks_smul,
      smul_zero]

/-- Polynomials commute with the transpose. -/
theorem aeval_transpose (A : Matrix n n R) (p : R[X]) : aeval Aᵀ p = (aeval A p)ᵀ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, map_add, transpose_add]
  | monomial k c =>
    simp only [aeval_monomial, ← Algebra.smul_def, transpose_smul, transpose_pow]

/-- Polynomials commute with an entrywise ring homomorphism of the scalars: Mathlib's
`Polynomial.map_aeval_eq_aeval_map` for `φ.mapMatrix`, which carries the scalar matrices to the
scalar matrices. -/
theorem map_aeval {S : Type*} [CommSemiring S] (φ : R →+* S) (A : Matrix n n R) (p : R[X]) :
    (aeval A p).map φ = aeval (A.map φ) (p.map φ) :=
  map_aeval_eq_aeval_map (ψ := φ.mapMatrix) (RingHom.ext fun c => by
    ext i j
    by_cases h : i = j <;> simp [algebraMap_eq_diagonal, h]) p A

end CommSemiring

/-- A matrix and its transpose have the same minimal polynomial. -/
theorem minpoly_transpose {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : minpoly K Aᵀ = minpoly K A := by
  have hA : IsIntegral K A := Algebra.IsIntegral.isIntegral _
  refine (minpoly.unique K Aᵀ (minpoly.monic hA) ?_ fun q hq h0 => ?_).symm
  · rw [aeval_transpose, minpoly.aeval, transpose_zero]
  · refine minpoly.min K A hq ?_
    rw [← transpose_transpose A, aeval_transpose, h0, transpose_zero]

section CommRing

variable {α : Type*} [CommRing α] {n : Type*} [Fintype n] [DecidableEq n]

/-- Whatever commutes with a matrix commutes with its (nonsingular) inverse `B⁻¹` (which is `0`
when `B` is singular). -/
theorem commute_nonsing_inv_right {B C : Matrix n n α} (h : Commute C B) : Commute C B⁻¹ := by
  rw [nonsing_inv_eq_ringInverse]
  exact h.ringInverse_right

/-- The (nonsingular) inverse `B⁻¹` of a matrix commutes with whatever commutes with `B`. -/
theorem commute_nonsing_inv_left {B C : Matrix n n α} (h : Commute B C) : Commute B⁻¹ C :=
  (commute_nonsing_inv_right h.symm).symm

end CommRing

end Matrix
