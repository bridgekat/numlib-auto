/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The inverse of a nonsingular matrix, acting on vectors

Mathlib's `Matrix.mul_nonsing_inv` and `Matrix.nonsing_inv_mul` cancel a matrix against its inverse
inside a *product of matrices*. This module carries the same cancellation one step further, to the
action `Matrix.mulVec` on vectors: `A *ᵥ (A⁻¹ *ᵥ u) = u` and `A⁻¹ *ᵥ (A *ᵥ u) = u` for an
invertible `A`, and the form in which they are usually wanted, namely that `A⁻¹ *ᵥ u` is *the*
solution of `A *ᵥ v = u`.

Every direct solver and every preconditioned iteration writes a step as `A⁻¹ *ᵥ u` and then needs
to know that applying `A` undoes it; without these lemmas the same
`Matrix.mulVec_mulVec`/`Matrix.mul_nonsing_inv`/`Matrix.one_mulVec` rewrite is repeated at each such
step. Invertibility is stated as `IsUnit A` rather than as `IsUnit A.det`, the two being
interchangeable by `Matrix.isUnit_iff_isUnit_det`.

The module also carries the two rank-update formulas for the inverse: the Sherman–Morrison–Woodbury
formula `(C + U B V)⁻¹ = C⁻¹ - C⁻¹ U (1 + B V C⁻¹ U)⁻¹ B V C⁻¹` in the form of
[quarteroni2000numerical] (3.57), whose middle factor `B` may be singular
(`Matrix.add_mul_mul_mul_inv_eq_sub_of_isUnit_one_add`), and its rank-one case, the
Sherman–Morrison formula `Matrix.inv_add_vecMulVec` with the nonsingularity
`Matrix.isUnit_add_vecMulVec` of the update.
-/

namespace Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- Applying `A` undoes applying `A⁻¹`: `A (A⁻¹ u) = u` for an invertible `A`. -/
theorem mulVec_nonsing_inv_mulVec {A : Matrix n n R} (hA : IsUnit A) (u : n → R) :
    A *ᵥ (A⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA), one_mulVec]

/-- Applying `A⁻¹` undoes applying `A`: `A⁻¹ (A u) = u` for an invertible `A`. -/
theorem nonsing_inv_mulVec_mulVec {A : Matrix n n R} (hA : IsUnit A) (u : n → R) :
    A⁻¹ *ᵥ (A *ᵥ u) = u := by
  rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA), one_mulVec]

/-- For an invertible `A`, the vector `A⁻¹ u` is *the* solution of `A v = u`: a `v` that solves the
system is already `A⁻¹ u`. -/
theorem nonsing_inv_mulVec_eq {A : Matrix n n R} (hA : IsUnit A) {u v : n → R} (h : A *ᵥ v = u) :
    A⁻¹ *ᵥ u = v := by
  rw [← h, nonsing_inv_mulVec_mulVec hA]

/-! ### The Sherman–Morrison–Woodbury formula -/

section Woodbury

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **The Sherman–Morrison–Woodbury formula** in the form of [quarteroni2000numerical] (3.57): for
`C` nonsingular and `1 + B V C⁻¹ U` nonsingular,
`(C + U B V)⁻¹ = C⁻¹ - C⁻¹ U (1 + B V C⁻¹ U)⁻¹ B V C⁻¹`. Unlike Mathlib's
`Matrix.add_mul_mul_inv_eq_sub`, the middle factor `B` may be singular: the book's form never
inverts it. The proof multiplies out `(C + U B V)` against the right-hand side, using
`U (1 + B V C⁻¹ U)⁻¹ + U B V C⁻¹ U (1 + B V C⁻¹ U)⁻¹ = U` to cancel the inner inverse. -/
theorem add_mul_mul_mul_inv_eq_sub_of_isUnit_one_add {C : Matrix n n R} (hC : IsUnit C)
    (U : Matrix n m R) (B : Matrix m m R) (V : Matrix m n R)
    (hW : IsUnit (1 + B * V * C⁻¹ * U)) :
    (C + U * B * V)⁻¹ = C⁻¹ - C⁻¹ * U * (1 + B * V * C⁻¹ * U)⁻¹ * B * V * C⁻¹ := by
  have hCC : ∀ X : Matrix n n R, C * (C⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hC), Matrix.one_mul]
  obtain ⟨W, hWdef⟩ : ∃ W : Matrix m m R, W = (1 + B * V * C⁻¹ * U)⁻¹ := ⟨_, rfl⟩
  have hWW : (1 + B * V * C⁻¹ * U) * W = 1 := by
    rw [hWdef]
    exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hW)
  rw [← hWdef]
  -- the cancellation of the inner inverse, applied to `Y = B V C⁻¹`
  have key : U * (W * (B * (V * C⁻¹))) + U * (B * (V * (C⁻¹ * (U * (W * (B * (V * C⁻¹)))))))
      = U * (B * (V * C⁻¹)) := by
    have h : U * (1 + B * V * C⁻¹ * U) * W * (B * (V * C⁻¹)) = U * (B * (V * C⁻¹)) := by
      rw [Matrix.mul_assoc U, hWW, Matrix.mul_one]
    rw [← h]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  refine inv_eq_right_inv ?_
  simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_assoc, hCC,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hC)]
  rw [← key]
  abel

end Woodbury

/-! ### The Sherman–Morrison formula -/

section ShermanMorrison

variable {K : Type*} [Field K]

/-- The product `(A + u vᵀ)` against the Sherman–Morrison candidate is the identity. -/
private theorem add_vecMulVec_mul_eq_one {A : Matrix n n K} (hA : IsUnit A) {u v : n → K}
    (h : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + vecMulVec u v)
      * (A⁻¹ - (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) • vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹)) = 1 := by
  have hAA : A * A⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hA)
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, hAA, Matrix.mul_smul, Matrix.mul_smul,
    mul_vecMulVec, mulVec_nonsing_inv_mulVec hA, vecMulVec_mul, vecMulVec_mul_vecMulVec,
    vecMulVec_smul, smul_smul]
  have hc : (1 : K) - 1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))
      - 1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) * (v ⬝ᵥ (A⁻¹ *ᵥ u)) = 0 := by
    field_simp
    ring
  calc 1 - (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) • vecMulVec u (v ᵥ* A⁻¹)
        + (vecMulVec u (v ᵥ* A⁻¹)
          - (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) * (v ⬝ᵥ (A⁻¹ *ᵥ u))) • vecMulVec u (v ᵥ* A⁻¹))
      = 1 + ((1 : K) - 1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))
          - 1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) * (v ⬝ᵥ (A⁻¹ *ᵥ u))) • vecMulVec u (v ᵥ* A⁻¹) := by
        simp only [sub_smul, one_smul]
        abel
    _ = 1 := by rw [hc, zero_smul, add_zero]

/-- **The Sherman–Morrison formula**, [quarteroni2000numerical] (3.57) for a rank-one update, as
used in their §7.2.7: for `A` nonsingular and `1 + v ⬝ A⁻¹ u ≠ 0`,
`(A + u vᵀ)⁻¹ = A⁻¹ - (1 + v ⬝ A⁻¹ u)⁻¹ (A⁻¹ u)(v A⁻¹)ᵀ`. Verified by multiplying out, with
`(u vᵀ)(x yᵀ) = (v ⬝ x) (u yᵀ)`. -/
theorem inv_add_vecMulVec {A : Matrix n n K} (hA : IsUnit A) {u v : n → K}
    (h : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + vecMulVec u v)⁻¹
      = A⁻¹ - (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) • vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) :=
  inv_eq_right_inv (add_vecMulVec_mul_eq_one hA h)

/-- The rank-one update `A + u vᵀ` of a nonsingular `A` is nonsingular when `1 + v ⬝ A⁻¹ u ≠ 0`:
the matrix determinant lemma, in the direction the Sherman–Morrison formula needs. -/
theorem isUnit_add_vecMulVec {A : Matrix n n K} (hA : IsUnit A) {u v : n → K}
    (h : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) : IsUnit (A + vecMulVec u v) :=
  ⟨⟨_, _, add_vecMulVec_mul_eq_one hA h, mul_eq_one_comm.1 (add_vecMulVec_mul_eq_one hA h)⟩, rfl⟩

end ShermanMorrison

end Matrix
