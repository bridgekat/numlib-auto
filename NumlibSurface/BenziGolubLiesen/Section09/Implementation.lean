import Numlib.LinearAlgebra.Matrix.Cholesky

/-!
# Benzi, Golub and Liesen, Section 9: Symmetric preconditioning

A preconditioner with a factorization $P=LL^T$ allows a change of variables from the left
preconditioned equation to a system involving $L^{-1}AL^{-T}$. Congruence preserves symmetry
and positive definiteness, enabling symmetric Krylov methods on the transformed system.

## Main results

* `BenziGolubLiesen.symmetricPreconditionedSystem_iff`: equivalence under $v=L^Tu$.
* `BenziGolubLiesen.exists_symmetricPreconditionedSystem_of_posDef`: use a Cholesky factor of $P$.
* `BenziGolubLiesen.isHermitian_symmetricPreconditionedMatrix` and
  `BenziGolubLiesen.posDef_symmetricPreconditionedMatrix`: the congruence preserves the
  corresponding property of $A$.

## Deviations from the source

* **Generalization.** The symmetry statement also applies to a singular factor, whose
  total inverse is zero. The system equivalence requires an invertible factor.
-/

namespace BenziGolubLiesen

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Section 9.3** of [benzi2005numerical]. With $P=LL^T$ and $L$ invertible, the left
preconditioned system is equivalent to the split system at $v=L^T u$. -/
theorem symmetricPreconditionedSystem_iff (A L : Matrix ι ι ℝ) (hL : IsUnit L) (u b : ι → ℝ) :
    let P := L * Lᵀ
    (P⁻¹ * A) *ᵥ u = P⁻¹ *ᵥ b ↔ (L⁻¹ * A * Lᵀ⁻¹) *ᵥ (Lᵀ *ᵥ u) = L⁻¹ *ᵥ b := by
  intro P
  have hLt : IsUnit Lᵀ := (Matrix.isUnit_transpose (A := L)).mpr hL
  have hP : IsUnit P := hL.mul hLt
  have hcancel : Lᵀ⁻¹ * Lᵀ = 1 := nonsing_inv_mul _ (isUnit_iff_isUnit_det _ |>.mp hLt)
  rw [mulVec_mulVec, Matrix.mul_assoc (L⁻¹ * A), hcancel, Matrix.mul_one,
    ← mulVec_mulVec, ← mulVec_mulVec]
  have hiP := mulVec_injective_iff_isUnit.mpr (isUnit_nonsing_inv_iff.mpr hP)
  have hiL := mulVec_injective_iff_isUnit.mpr (isUnit_nonsing_inv_iff.mpr hL)
  exact hiP.eq_iff.trans hiL.eq_iff.symm

/-- **Section 9.3** of [benzi2005numerical]. A positive definite preconditioner admits
an invertible lower Cholesky factor giving an equivalent split system. -/
theorem exists_symmetricPreconditionedSystem_of_posDef {κ : Type*} [Fintype κ] [LinearOrder κ]
    (A : Matrix κ κ ℝ) {P : Matrix κ κ ℝ} (hP : P.PosDef) :
    ∃ L : Matrix κ κ ℝ, L.IsLowerTriangular ∧ IsUnit L ∧ P = L * Lᵀ ∧
      ∀ u b : κ → ℝ,
        (P⁻¹ * A) *ᵥ u = P⁻¹ *ᵥ b ↔ (L⁻¹ * A * Lᵀ⁻¹) *ᵥ (Lᵀ *ᵥ u) = L⁻¹ *ᵥ b := by
  obtain ⟨H, hH⟩ := exists_isCholesky hP
  have hL : IsUnit Hᵀ := (isUnit_transpose (A := H)).mpr hH.isUnit
  have hform : P = Hᵀ * Hᵀᵀ := by simpa using hH.conjTranspose_mul_self.symm
  refine ⟨Hᵀ, hH.isUpperTriangular.transpose, hL, hform, fun u b => ?_⟩
  rw [hform]
  exact symmetricPreconditionedSystem_iff A Hᵀ hL u b

/-- **Section 9.3** of [benzi2005numerical]. Splitting the preconditioner preserves symmetry.

**Generalization.** For singular $L$, the total inverse makes the transformed matrix zero. -/
theorem isHermitian_symmetricPreconditionedMatrix {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (L : Matrix ι ι ℝ) : (L⁻¹ * A * Lᵀ⁻¹).IsHermitian := by
  simpa [transpose_nonsing_inv] using isHermitian_mul_mul_conjTranspose L⁻¹ hA

/-- **Section 9.3** of [benzi2005numerical]. An invertible Cholesky factor preserves positive
definiteness under the split transformation. -/
theorem posDef_symmetricPreconditionedMatrix {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (L : Matrix ι ι ℝ) (hL : IsUnit L) : (L⁻¹ * A * Lᵀ⁻¹).PosDef := by
  have hinj := vecMul_injective_iff_isUnit.mpr (isUnit_nonsing_inv_iff.mpr hL)
  simpa [transpose_nonsing_inv] using hA.mul_mul_conjTranspose_same hinj

end BenziGolubLiesen
