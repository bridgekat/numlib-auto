/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The inverse of a nonsingular matrix, acting on vectors

Let $A$ be an invertible square matrix over a commutative ring. This file proves the cancellation of
$A$ against $A^{-1}$ in the action on vectors: $A(A^{-1} u) = u$ and $A^{-1}(Au) = u$, and, in the
form in which these facts are usually needed, that $A^{-1} u$ is the unique solution $v$ of
$Av = u$. Mathlib's `Matrix.mul_nonsing_inv` and `Matrix.nonsing_inv_mul` give the same cancellation
inside a product of matrices. Every direct solver and every preconditioned iteration writes a step
as $A^{-1} u$ and then needs to know that an application of $A$ undoes it.

The file also proves two formulas for the inverse of an updated matrix: the
Sherman–Morrison–Woodbury formula $$(C + UBV)^{-1} = C^{-1} - C^{-1} U (I + B V C^{-1} U)^{-1} B V
C^{-1}$$ in the form of [quarteroni2000numerical] (3.57), in which the middle factor $B$ can be
singular, and its rank-one case, the Sherman–Morrison formula, together with the nonsingularity of
the rank-one update.

## Main results

* `Matrix.mulVec_nonsing_inv_mulVec`, `Matrix.nonsing_inv_mulVec_mulVec`: $A(A^{-1} u) = u$ and
  $A^{-1}(Au) = u$ for an invertible $A$.
* `Matrix.nonsing_inv_mulVec_eq`: if $Av = u$ and $A$ is invertible, then $A^{-1} u = v$.
* `Matrix.add_mul_mul_mul_inv_eq_sub_of_isUnit_one_add`: the Sherman–Morrison–Woodbury formula.
* `Matrix.inv_add_vecMulVec`, `Matrix.isUnit_add_vecMulVec`: the Sherman–Morrison formula, and the
  nonsingularity of $A + uv^T$ when $1 + v^T A^{-1} u \neq 0$.

## Implementation notes

* Invertibility is stated as `IsUnit A`, not as `IsUnit A.det`. The two are equivalent by
  `Matrix.isUnit_iff_isUnit_det`.
-/

namespace Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- Let $A$ be an invertible $n \times n$ matrix over a commutative ring $R$ and let $u \in R^n$.
Then $A(A^{-1} u) = u$. -/
theorem mulVec_nonsing_inv_mulVec {A : Matrix n n R} (hA : IsUnit A) (u : n → R) :
    A *ᵥ (A⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA), one_mulVec]

/-- Let $A$ be an invertible $n \times n$ matrix over a commutative ring $R$ and let $u \in R^n$.
Then $A^{-1}(Au) = u$. -/
theorem nonsing_inv_mulVec_mulVec {A : Matrix n n R} (hA : IsUnit A) (u : n → R) :
    A⁻¹ *ᵥ (A *ᵥ u) = u := by
  rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA), one_mulVec]

/-- Let $A$ be an invertible $n \times n$ matrix over a commutative ring $R$, and let $u, v \in R^n$
with $Av = u$. Then $A^{-1} u = v$. So $A^{-1} u$ is the unique solution of $Av = u$. -/
theorem nonsing_inv_mulVec_eq {A : Matrix n n R} (hA : IsUnit A) {u v : n → R} (h : A *ᵥ v = u) :
    A⁻¹ *ᵥ u = v := by
  rw [← h, nonsing_inv_mulVec_mulVec hA]

/-! ### The Sherman–Morrison–Woodbury formula -/

section Woodbury

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The **Sherman–Morrison–Woodbury formula** in the form of [quarteroni2000numerical] (3.57). Let
$R$ be a commutative ring, let $C \in R^{n \times n}$ be invertible, let $U \in R^{n \times m}$,
$B \in R^{m \times m}$ and $V \in R^{m \times n}$, and let $I + B V C^{-1} U$ be invertible.
Then $$(C + UBV)^{-1} = C^{-1} - C^{-1} U (I + B V C^{-1} U)^{-1} B V C^{-1}.$$

Unlike Mathlib's `Matrix.add_mul_mul_inv_eq_sub`, the statement allows a singular middle factor
$B$, because this form of the formula never inverts $B$. The proof multiplies $C + UBV$ by the
right-hand side and uses $U (I + B V C^{-1} U)^{-1} + U B V C^{-1} U (I + B V C^{-1} U)^{-1} =
U$ to cancel the inner inverse. -/
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

/-- The product of $A + uv^T$ with the Sherman–Morrison candidate $A^{-1} - (1 + v^T A^{-1} u)^{-1}
(A^{-1} u)(v^T A^{-1})$ is the identity. -/
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

/-- The **Sherman–Morrison formula**: the rank-one case of [quarteroni2000numerical] (3.57), as used
in §7.2.7 of the source. Let $K$ be a field, let $A \in K^{n \times n}$ be invertible, and let
$u, v \in K^n$ with $1 + v^T A^{-1} u \neq 0$. Then $$(A + uv^T)^{-1} = A^{-1} - \frac{1}{1 +
v^T A^{-1} u} (A^{-1} u)(v^T A^{-1}).$$

The proof multiplies out, with $(uv^T)(xy^T) = (v^T x)\, uy^T$. The rank-one matrix $uv^T$ is
`Matrix.vecMulVec u v`. -/
theorem inv_add_vecMulVec {A : Matrix n n K} (hA : IsUnit A) {u v : n → K}
    (h : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + vecMulVec u v)⁻¹
      = A⁻¹ - (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) • vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) :=
  inv_eq_right_inv (add_vecMulVec_mul_eq_one hA h)

/-- Let $K$ be a field, let $A \in K^{n \times n}$ be invertible, and let $u, v \in K^n$ with
$1 + v^T A^{-1} u \neq 0$. Then $A + uv^T$ is invertible. This is the direction of the matrix
determinant lemma that the Sherman–Morrison formula needs. -/
theorem isUnit_add_vecMulVec {A : Matrix n n K} (hA : IsUnit A) {u v : n → K}
    (h : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) : IsUnit (A + vecMulVec u v) :=
  ⟨⟨_, _, add_vecMulVec_mul_eq_one hA h, mul_eq_one_comm.1 (add_vecMulVec_mul_eq_one hA h)⟩, rfl⟩

end ShermanMorrison

end Matrix
