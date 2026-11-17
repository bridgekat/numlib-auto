import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.PosDef

/-!
# Weighted adjoints of matrices

For a positive definite matrix $B$, the adjoint of $A$ in the $B$-inner product
is $B^{-1} A^H B$. An invertible change of coordinates $W$ with $W^H B W=I$ carries
the weighted adjoint to the ordinary adjoint.

## Main definitions

* `Matrix.similarityAlgEquiv` is the algebra equivalence $Amapsto Y^{-1}AY$.
* `Matrix.weightedAdjoint` is the matrix $B^{-1} A^H B$.

## Main results

* `Matrix.similarityAlgEquiv_weightedAdjoint` gives the ordinary adjoint in coordinates
  that make the metric equal to the identity.
* `Matrix.exists_diagonal_similarity_of_commute_weightedAdjoint` gives an orthonormal
  eigenbasis for a matrix commuting with its weighted adjoint.
* `Matrix.similarityAlgEquiv_weightedAdjoint_of_block` gives the conjugated diagonal
  entries when the inverse metric is supported within equal-eigenvalue blocks.
-/

open scoped Matrix ComplexOrder

namespace Matrix

section Similarity

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The algebra equivalence $A\mapsto Y^{-1}AY$ for an invertible matrix $Y$. -/
noncomputable def similarityAlgEquiv (Y : Matrix n n R) (hY : IsUnit Y) :
    Matrix n n R ≃ₐ[R] Matrix n n R where
  toRingEquiv := MulSemiringAction.toRingEquiv _ _ (ConjAct.toConjAct hY.unit⁻¹)
  commutes' c := by
    change (↑(hY.unit⁻¹) : Matrix n n R) * algebraMap R (Matrix n n R) c *
      (↑hY.unit : Matrix n n R) = _
    rw [← Algebra.commutes, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-- The matrix formula for similarity by $Y$. -/
@[simp]
theorem similarityAlgEquiv_apply (Y : Matrix n n R) (hY : IsUnit Y) (A : Matrix n n R) :
    similarityAlgEquiv Y hY A = Y⁻¹ * A * Y := by
  change (↑(hY.unit⁻¹) : Matrix n n R) * A * (↑hY.unit : Matrix n n R) = _
  rw [coe_units_inv, hY.unit_spec]

/-- The inverse change of coordinates sends $A$ to $YAY^{-1}$. -/
@[simp]
theorem similarityAlgEquiv_symm_apply (Y : Matrix n n R) (hY : IsUnit Y) (A : Matrix n n R) :
    (similarityAlgEquiv Y hY).symm A = Y * A * Y⁻¹ := by
  apply (similarityAlgEquiv Y hY).injective
  rw [AlgEquiv.apply_symm_apply, similarityAlgEquiv_apply]
  have hd := (isUnit_iff_isUnit_det Y).mp hY
  calc
    A = (Y⁻¹ * Y) * A * (Y⁻¹ * Y) := by simp only [nonsing_inv_mul Y hd, one_mul, mul_one]
    _ = Y⁻¹ * (Y * A * Y⁻¹) * Y := by simp only [Matrix.mul_assoc]

/-- Equality in the new coordinates is equivalent to the corresponding similarity formula. -/
theorem similarityAlgEquiv_apply_eq_iff (Y : Matrix n n R) (hY : IsUnit Y)
    (A C : Matrix n n R) : similarityAlgEquiv Y hY A = C ↔ A = Y * C * Y⁻¹ := by
  let e := similarityAlgEquiv Y hY
  change e A = C ↔ _
  rw [← similarityAlgEquiv_symm_apply Y hY]
  change e A = C ↔ A = e.symm C
  constructor
  · intro h
    rw [← h, AlgEquiv.symm_apply_apply]
  · intro h
    rw [h, AlgEquiv.apply_symm_apply]

end Similarity

section Weighted

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The adjoint $B^{-1}A^H B$ in the inner product with matrix $B$. -/
noncomputable def weightedAdjoint (A B : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  B⁻¹ * Aᴴ * B

/-- An invertible change $W$ with $W^H B W=I$ gives $W^H B=W^{-1}$. -/
theorem conjTranspose_mul_eq_inv_of_conj_eq_one {B W : Matrix n n 𝕜} (hW : IsUnit W)
    (hWmetric : Wᴴ * B * W = 1) : Wᴴ * B = W⁻¹ := by
  have hd := (isUnit_iff_isUnit_det W).mp hW
  calc
    Wᴴ * B = (Wᴴ * B) * (W * W⁻¹) := by rw [mul_nonsing_inv W hd, mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hWmetric, one_mul]

/-- An invertible change $W$ with $W^H B W=I$ gives $B^{-1}=WW^H$ for invertible $B$. -/
theorem inv_eq_mul_conjTranspose_of_conj_eq_one {B W : Matrix n n 𝕜} (hB : IsUnit B)
    (hW : IsUnit W) (hWmetric : Wᴴ * B * W = 1) : B⁻¹ = W * Wᴴ := by
  have hWinv := conjTranspose_mul_eq_inv_of_conj_eq_one hW hWmetric
  have hdB := (isUnit_iff_isUnit_det B).mp hB
  have hdW := (isUnit_iff_isUnit_det W).mp hW
  calc
    B⁻¹ = (W * W⁻¹) * B⁻¹ := by rw [mul_nonsing_inv W hdW, one_mul]
    _ = W * (Wᴴ * B) * B⁻¹ := by rw [hWinv]
    _ = W * Wᴴ := by
      rw [← Matrix.mul_assoc W Wᴴ B, Matrix.mul_assoc, mul_nonsing_inv B hdB, mul_one]

/-- An invertible coordinate change that makes a Hermitian metric equal to the identity
carries the weighted adjoint to conjugate transpose. -/
theorem similarityAlgEquiv_weightedAdjoint {A B W : Matrix n n 𝕜} (hB : B.PosDef)
    (hW : IsUnit W) (hWmetric : Wᴴ * B * W = 1) :
    similarityAlgEquiv W hW (A.weightedAdjoint B) = (similarityAlgEquiv W hW A)ᴴ := by
  have hWinv := conjTranspose_mul_eq_inv_of_conj_eq_one hW hWmetric
  have hBW : B * W = (W⁻¹)ᴴ := by
    have h := congrArg Matrix.conjTranspose hWinv
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, hB.1.eq] at h
  have hdB := (isUnit_iff_isUnit_det B).mp hB.isUnit
  have hInvB : W⁻¹ * B⁻¹ = Wᴴ := by
    rw [← hWinv, Matrix.mul_assoc, mul_nonsing_inv B hdB, mul_one]
  simp only [similarityAlgEquiv_apply, weightedAdjoint, conjTranspose_mul]
  calc
    _ = (W⁻¹ * B⁻¹) * Aᴴ * (B * W) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hInvB, hBW]; simp only [Matrix.mul_assoc]

/-- A matrix commuting with its weighted adjoint has a basis of eigenvectors
orthonormal for the weight. -/
theorem exists_diagonal_similarity_of_commute_weightedAdjoint [IsAlgClosed 𝕜]
    {A B : Matrix n n 𝕜} (hB : B.PosDef) (hA : Commute (A.weightedAdjoint B) A) :
    ∃ (Y : Matrix n n 𝕜) (hY : IsUnit Y) (d : n → 𝕜),
      similarityAlgEquiv Y hY A = diagonal d ∧ Yᴴ * B * Y = 1 := by
  obtain ⟨W, hW, hWmetric⟩ := hB.exists_isUnit_conj_eq_one
  rw [star_eq_conjTranspose] at hWmetric
  let e := similarityAlgEquiv W hW
  have hC : IsStarNormal (e A) := ⟨by
    rw [star_eq_conjTranspose, ← similarityAlgEquiv_weightedAdjoint hB hW hWmetric]
    exact hA.map e⟩
  obtain ⟨U, hUmem, d, hd⟩ := IsStarNormal.spectral_theorem.mp hC
  have hU : IsUnit U := Unitary.isUnit_coe (U := ⟨U, hUmem⟩)
  have hUmetric : Uᴴ * U = 1 := (Unitary.mem_iff.1 hUmem).1
  have hUinv : Uᴴ = U⁻¹ := by
    have h := conjTranspose_mul_eq_inv_of_conj_eq_one (B := 1) hU
      (by simpa only [mul_one] using hUmetric)
    simpa only [mul_one] using h
  refine ⟨W * U, hW.mul hU, d, ?_, ?_⟩
  · rw [similarityAlgEquiv_apply, Matrix.mul_inv_rev]
    calc
      U⁻¹ * W⁻¹ * A * (W * U) = Uᴴ * e A * U := by
        rw [hUinv]
        simp only [e, similarityAlgEquiv_apply, Matrix.mul_assoc]
      _ = _ := hd
  · rw [conjTranspose_mul]
    calc
      Uᴴ * Wᴴ * B * (W * U) = Uᴴ * (Wᴴ * B * W) * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWmetric, mul_one, hUmetric]

/-- The inverse metric in the coordinates given by $Y$, conjugated back by $Y$. -/
theorem mul_invMetric_mul_conjTranspose {B Y : Matrix n n 𝕜} (hY : IsUnit Y) :
    Y * (Y⁻¹ * B⁻¹ * (Y⁻¹)ᴴ) * Yᴴ = B⁻¹ := by
  have hdet := (isUnit_iff_isUnit_det Y).mp hY
  have hstar : (Y⁻¹)ᴴ * Yᴴ = 1 := by
    rw [← conjTranspose_mul, mul_nonsing_inv Y hdet, conjTranspose_one]
  calc
    _ = (Y * Y⁻¹) * B⁻¹ * ((Y⁻¹)ᴴ * Yᴴ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hstar, mul_nonsing_inv Y hdet, one_mul, mul_one]

/-- Transporting the weighted adjoint to any invertible coordinates gives a
commutation relation with the inverse of the transformed metric. -/
theorem similarityAlgEquiv_weightedAdjoint_mul {A B Y D : Matrix n n 𝕜} (hB : IsUnit B)
    (hY : IsUnit Y) (hD : B⁻¹ = Y * D * Yᴴ) :
    similarityAlgEquiv Y hY (A.weightedAdjoint B) * D =
      D * (similarityAlgEquiv Y hY A)ᴴ := by
  have hdY := (isUnit_iff_isUnit_det Y).mp hY
  have hdB := (isUnit_iff_isUnit_det B).mp hB
  have hYY : Yᴴ * (Y⁻¹)ᴴ = 1 := by
    rw [← conjTranspose_mul, nonsing_inv_mul Y hdY, conjTranspose_one]
  have hleft : Y * D = B⁻¹ * (Y⁻¹)ᴴ := by
    rw [hD, Matrix.mul_assoc, hYY, mul_one]
  have hright : D * Yᴴ = Y⁻¹ * B⁻¹ := by
    rw [hD, ← Matrix.mul_assoc Y⁻¹, ← Matrix.mul_assoc Y⁻¹, nonsing_inv_mul Y hdY, one_mul]
  simp only [similarityAlgEquiv_apply, weightedAdjoint, conjTranspose_mul]
  calc
    _ = (Y⁻¹ * B⁻¹) * Aᴴ * B * (Y * D) := by simp only [Matrix.mul_assoc]
    _ = (Y⁻¹ * B⁻¹) * Aᴴ * (B * B⁻¹) * (Y⁻¹)ᴴ := by
      rw [hleft]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [mul_nonsing_inv B hdB, mul_one, ← hright]
      simp only [Matrix.mul_assoc]

/-- A matrix supported within the blocks of equal values of $d$ commutes with
the conjugate transpose of $operatorname{diag}(d)$. -/
theorem commute_diagonal_conjTranspose_of_block {D : Matrix n n 𝕜} {d : n → 𝕜}
    (hD : ∀ i j, d i ≠ d j → D i j = 0) : Commute D (diagonal d)ᴴ := by
  change D * (diagonal d)ᴴ = (diagonal d)ᴴ * D
  rw [diagonal_conjTranspose]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  change D i j * star (d j) = star (d i) * D i j
  by_cases h : d i = d j
  · rw [h, mul_comm]
  · simp [hD i j h]

/-- For a diagonalized matrix, a positive definite inverse metric supported within
equal-eigenvalue blocks gives the ordinary adjoint in the eigenbasis. -/
theorem similarityAlgEquiv_weightedAdjoint_of_block {A B Y D : Matrix n n 𝕜} {d : n → 𝕜}
    (hB : IsUnit B) (hY : IsUnit Y) (hdiag : similarityAlgEquiv Y hY A = diagonal d)
    (hD : D.PosDef) (hBfac : B⁻¹ = Y * D * Yᴴ)
    (hblock : ∀ i j, d i ≠ d j → D i j = 0) :
    similarityAlgEquiv Y hY (A.weightedAdjoint B) = (diagonal d)ᴴ := by
  have h := similarityAlgEquiv_weightedAdjoint_mul hB hY hBfac (A := A)
  rw [hdiag, (commute_diagonal_conjTranspose_of_block hblock).eq] at h
  have h' := congrArg (· * D⁻¹) h
  simpa only [mul_nonsing_inv_cancel_right D _ ((isUnit_iff_isUnit_det D).mp hD.isUnit)] using h'

end Weighted
end Matrix
