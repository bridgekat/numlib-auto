/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Preconditioner.Constraint

/-!
# Section 10.2: constraint preconditioning

[benzi2005numerical, Theorem 10.1] describes the characteristic polynomial and eigenvectors of the
constraint-preconditioned saddle matrix with zero trailing block.
-/

open Matrix Polynomial

namespace BenziGolubLiesen

/-- **[benzi2005numerical, Theorem 10.1].** The characteristic polynomial of the
constraint-preconditioned saddle matrix has `2 * m` roots at 1 together with all the eigenvalues
of the reduced pencil, counted with multiplicities. A root of the reduced pencil at 1 increases
the total multiplicity at 1. If the reduced preconditioner is positive definite, a reduced
eigenbasis supplies independent lifts for all reduced eigenvalues different from 1. In the
original coordinates the primal component of such a lift is `Z *ᵥ z`. The lifts are jointly
independent with the multiplier coordinate vectors and the eigenvectors at 1 constructed from
a basis of the kernel of `A - G`. -/
theorem theorem_10_1 {n m : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin m) (Fin n) ℝ}
    {Z : Matrix (Fin n) (Fin (n - m)) ℝ} (hA : A.IsSymm) (_hG : G.IsSymm) (_hGA : G ≠ A)
    (_hmn : m < n) (hB : B.rank = m)
    (_hAUnit : IsUnit (fromBlocks A Bᵀ B 0)) (hP : IsUnit (fromBlocks G Bᵀ B 0))
    (hZi : Function.Injective Z.mulVec)
    (hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin) :
    let M := (fromBlocks G Bᵀ B 0)⁻¹ * fromBlocks A Bᵀ B 0
    let Ared := Zᵀ * A * Z
    let Gred := Zᵀ * G * Z
    IsUnit Gred ∧ M.charpoly = (X - 1) ^ (2 * m) * (Gred⁻¹ * Ared).charpoly ∧
      (Gred.PosDef →
        ∃ (w : Fin (Module.finrank ℝ (LinearMap.ker (A - G).mulVecLin)) → Fin n → ℝ)
          (d : Fin (n - m) → ℝ) (z : Fin (n - m) → Fin (n - m) → ℝ)
          (y : {j // d j ≠ 1} → Fin m → ℝ),
          (∀ i, A *ᵥ w i = G *ᵥ w i) ∧
          (∀ j, HasPencilEigenvector Ared Gred (d j) (z j)) ∧
          LinearIndependent ℝ z ∧
          let u := Sum.elim (fun j : Fin m => Sum.elim (0 : Fin n → ℝ) (Pi.single j 1))
            (fun i => Sum.elim (w i) (0 : Fin m → ℝ))
          let v := fun j : {j // d j ≠ 1} => Sum.elim (Z *ᵥ z j) (y j)
          LinearIndependent ℝ (Sum.elim u v) ∧ (∀ i, M *ᵥ u i = u i) ∧
            (∀ j, M *ᵥ v j = d j • v j)) := by
  have hP' : IsUnit (saddleMatrix G Bᴴ 0) := by
    simpa [saddleMatrix, conjTranspose_eq_transpose_of_trivial] using hP
  have hBs : Function.Surjective B.mulVec :=
    mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hB)
  refine ⟨?_, ?_, fun hGred => ?_⟩
  · simpa [conjTranspose_eq_transpose_of_trivial] using isUnit_nullspaceCompression hZi hZ hP'
  · simpa [constraintPreconditioned, saddleMatrix, conjTranspose_eq_transpose_of_trivial] using
      charpoly_constraintPreconditioned (A := A) hBs hZi hZ hP'
  · have hG' : (Zᴴ * G * Z).PosDef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hGred
    simpa [constraintPreconditioned, saddleMatrix, conjTranspose_eq_transpose_of_trivial] using
      exists_constraintPreconditioned_eigenvectors (isHermitian_iff_isSymm.mpr hA) hZi hZ hP' hG'

/-- In [benzi2005numerical, Theorem 10.1] the total algebraic multiplicity of 1 may exceed
`2 * m`, even when both saddle matrices are nonsingular and `A` and `G` are distinct. For
`A = diag(2, 1)`, `G = I`, and `B = [1, 0]`, the preconditioned matrix has three roots at 1. -/
theorem theorem_10_1_multiplicity_example :
    ∃ (A G : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 1) (Fin 2) ℝ),
      A.IsSymm ∧ G.IsSymm ∧ G ≠ A ∧ B.rank = 1 ∧
      IsUnit (fromBlocks A Bᵀ B 0) ∧ IsUnit (fromBlocks G Bᵀ B 0) ∧
      ((fromBlocks G Bᵀ B 0)⁻¹ * fromBlocks A Bᵀ B 0).charpoly = (X - 1) ^ 3 := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![2, 1]
  let G : Matrix (Fin 2) (Fin 2) ℝ := 1
  let B : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
  let Z : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
  have hA : A.PosDef := posDef_diagonal_iff.mpr (by intro i; fin_cases i <;> norm_num)
  have hG : G.PosDef := PosDef.one
  have hGA : G ≠ A := by
    intro h
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [G, A] at h'
  have hB : ∀ x : Fin 2 → ℝ, B *ᵥ x = ![x 0] := by
    intro x
    funext i
    fin_cases i
    simp [B, mulVec, dotProduct, Fin.sum_univ_two]
  have hBT : Function.Injective Bᵀ.mulVec := by
    intro x y h
    funext i
    fin_cases i
    have h' := congrFun h (0 : Fin 2)
    simpa [B, mulVec, dotProduct, Fin.sum_univ_one] using h'
  have hBs : Function.Surjective B.mulVec := by
    intro y
    refine ⟨![y 0, 0], ?_⟩
    rw [hB]
    funext i
    fin_cases i
    rfl
  have hZcol : ∀ z : Fin 1 → ℝ, Z *ᵥ z = ![0, z 0] := by
    intro z
    funext i
    fin_cases i <;> simp [Z, mulVec, dotProduct]
  have hZi : Function.Injective Z.mulVec := by
    intro x y h
    simp only [hZcol] at h
    funext i
    fin_cases i
    simpa using congrFun h (1 : Fin 2)
  have hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin := by
    ext x
    change (∃ z, Z *ᵥ z = x) ↔ B *ᵥ x = 0
    simp only [hZcol, hB]
    constructor
    · rintro ⟨z, rfl⟩
      funext i
      fin_cases i
      rfl
    · intro hx
      refine ⟨![x 1], ?_⟩
      funext i
      fin_cases i
      · simpa using (congrFun hx (0 : Fin 1)).symm
      · rfl
  have hPA : IsUnit (fromBlocks A Bᵀ B 0) := by
    simpa [saddleMatrix, conjTranspose_eq_transpose_of_trivial] using
      (isUnit_saddleMatrix_zero hA hBT)
  have hPG : IsUnit (fromBlocks G Bᵀ B 0) := by
    simpa [saddleMatrix, conjTranspose_eq_transpose_of_trivial] using
      (isUnit_saddleMatrix_zero hG hBT)
  have hBr : B.rank = 1 := by simpa using mulVec_surjective_iff_rank_eq_card.mp hBs
  have hAr : Zᵀ * A * Z = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Z, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  have hGr : Zᵀ * G * Z = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Z, G, Matrix.mul_apply, Fin.sum_univ_two]
  have hc := (theorem_10_1 hA.1.isSymm hG.1.isSymm hGA (by decide) hBr hPA hPG hZi hZ).2.1
  rw [hAr, hGr, inv_one, Matrix.one_mul, Matrix.charpoly_one] at hc
  refine ⟨A, G, B, hA.1.isSymm, hG.1.isSymm, hGA, hBr, hPA, hPG, ?_⟩
  rw [hc]
  simp
  ring

end BenziGolubLiesen
