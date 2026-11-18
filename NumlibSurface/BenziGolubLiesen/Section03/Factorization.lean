import Numlib.LinearAlgebra.Matrix.SchurComplement
import NumlibSurface.BenziGolubLiesen.Section01

/-!
# Benzi, Golub and Liesen, Section 3: Schur complement factorization

For an invertible leading block $A$, block Gaussian elimination of (1.1) gives the Schur
complement $S=-C-B_2 A^{-1}B_1^T$ and three factorizations. It also reduces nonsingularity of
the full system to nonsingularity of $S$.

## Main definitions

* `BenziGolubLiesen.saddleSchurComplement`: the Schur complement with the survey's sign.

## Main results

* `BenziGolubLiesen.saddlePointMatrix_ldu`: the block LDU factorization (3.1).
* `BenziGolubLiesen.saddlePointMatrix_lower_upper` and
  `BenziGolubLiesen.saddlePointMatrix_unitLower_upper`: the LU variants (3.2) and (3.3).
* `BenziGolubLiesen.saddlePointMatrix_inv_eq`: the block inverse (3.4).
-/

namespace BenziGolubLiesen

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  {A : Matrix n n ℝ} {B₁ B₂ : Matrix m n ℝ} {C : Matrix m m ℝ}

/-- **Section 3.1** of [benzi2005numerical]. The Schur complement of the leading block in (1.1). -/
noncomputable abbrev saddleSchurComplement (A : Matrix n n ℝ) (B₁ B₂ : Matrix m n ℝ)
    (C : Matrix m m ℝ) : Matrix m m ℝ := (saddlePointMatrix A B₁ B₂ C).schurComplement

omit [Fintype m] [DecidableEq m] in
/-- **Section 3.1** of [benzi2005numerical]. The sign convention is $S=-(C+B_2 A^{-1}B_1^T)$. -/
theorem saddleSchurComplement_eq : saddleSchurComplement A B₁ B₂ C = -(C + B₂ * A⁻¹ * B₁ᵀ) := by
  rw [saddleSchurComplement, schurComplement_fromBlocks, neg_add, sub_eq_add_neg]

/-- **Equation (3.3)** of [benzi2005numerical]. The left factor is unit lower triangular. -/
theorem saddlePointMatrix_unitLower_upper (hA : IsUnit A) :
    saddlePointMatrix A B₁ B₂ C =
      fromBlocks 1 0 (B₂ * A⁻¹) 1 * fromBlocks A B₁ᵀ 0 (saddleSchurComplement A B₁ B₂ C) :=
  fromBlocks_eq_mul_fromBlocks_schurComplement hA

/-- **Equation (3.2)** of [benzi2005numerical]. The right factor is unit upper triangular. -/
theorem saddlePointMatrix_lower_upper (hA : IsUnit A) :
    saddlePointMatrix A B₁ B₂ C =
      fromBlocks A 0 B₂ (saddleSchurComplement A B₁ B₂ C) * fromBlocks 1 (A⁻¹ * B₁ᵀ) 0 1 := by
  have hinv : A * A⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hA)
  simp only [saddlePointMatrix, saddleSchurComplement, schurComplement_fromBlocks,
    fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, add_zero, ← Matrix.mul_assoc A, hinv,
    Matrix.one_mul, ← Matrix.mul_assoc B₂]
  congr 1
  abel

/-- **Equation (3.1)** of [benzi2005numerical]. The diagonal factor contains $A$ and $S$. -/
theorem saddlePointMatrix_ldu (hA : IsUnit A) :
    saddlePointMatrix A B₁ B₂ C =
      fromBlocks 1 0 (B₂ * A⁻¹) 1 * fromBlocks A 0 0 (saddleSchurComplement A B₁ B₂ C) *
        fromBlocks 1 (A⁻¹ * B₁ᵀ) 0 1 := by
  let := invertibleOfIsUnitDet A ((isUnit_iff_isUnit_det _).mp hA)
  simpa only [saddlePointMatrix, saddleSchurComplement, schurComplement_fromBlocks,
    invOf_eq_nonsing_inv] using fromBlocks_eq_of_invertible₁₁ A B₁ᵀ B₂ (-C)

/-- **Section 3.2** of [benzi2005numerical]. With $A$ invertible, (1.1) is nonsingular if and
only if its Schur complement is nonsingular. -/
theorem isUnit_saddlePointMatrix_iff_isUnit_schurComplement (hA : IsUnit A) :
    IsUnit (saddlePointMatrix A B₁ B₂ C) ↔ IsUnit (saddleSchurComplement A B₁ B₂ C) :=
  (isUnit_schurComplement_iff (A := saddlePointMatrix A B₁ B₂ C) hA).symm

/-- **Equation (3.4)** of [benzi2005numerical]. When $A$ and the full matrix are nonsingular,
their inverses and the Schur complement give the four blocks of the inverse. -/
theorem saddlePointMatrix_inv_eq (hA : IsUnit A) (hM : IsUnit (saddlePointMatrix A B₁ B₂ C)) :
    let S := saddleSchurComplement A B₁ B₂ C
    (saddlePointMatrix A B₁ B₂ C)⁻¹ =
      fromBlocks (A⁻¹ + A⁻¹ * B₁ᵀ * S⁻¹ * B₂ * A⁻¹) (-(A⁻¹ * B₁ᵀ * S⁻¹))
        (-(S⁻¹ * B₂ * A⁻¹)) S⁻¹ :=
  inv_fromBlocks_eq hA hM

end BenziGolubLiesen
