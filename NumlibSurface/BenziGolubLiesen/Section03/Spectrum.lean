/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.LinearAlgebra.Matrix.SaddlePoint
import Numlib.LinearAlgebra.Matrix.SaddlePoint.ScalarDiagonal
import Numlib.LinearAlgebra.Matrix.SaddlePoint.Spectrum
import NumlibSurface.BenziGolubLiesen.Section01

/-!
# Benzi, Golub and Liesen, Section 3.4

Spectral bounds for the symmetric saddle-point matrix and for the sign-flipped
form, with explicit eigenvalues when the top block is a scalar identity.

The paragraph after Theorem 3.8 calls the nonreal roots purely imaginary.
Their real part is `η / 2`, as given by the theorem's formulas.
-/

namespace BenziGolubLiesen

open Matrix WithLp
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- The sign-flipped coefficient matrix in equation (3.10) of [benzi2005numerical]. -/
abbrev signFlippedSaddlePointMatrix (A : Matrix n n ℝ) (B : Matrix m n ℝ) (C : Matrix m m ℝ) :
    Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  fromBlocks A Bᵀ (-B) C

omit [DecidableEq n] [DecidableEq m] in
private theorem fullRowRank_mulVec_transpose_injective {B : Matrix m n ℝ}
    (hB : B.rank = Fintype.card m) : Function.Injective Bᵀ.mulVec :=
  Matrix.mulVec_injective_iff_rank_eq_card.mpr (by rwa [Matrix.rank_transpose])

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
private theorem map_ofReal_transpose (B : Matrix m n ℝ) :
    Bᵀ.map Complex.ofReal = (B.map Complex.ofReal)ᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
private theorem complexify_signFlippedSaddlePointMatrix
    (A : Matrix n n ℝ) (B : Matrix m n ℝ) (C : Matrix m m ℝ) :
    (signFlippedSaddlePointMatrix A B C).complexify =
      fromBlocks A.complexify (B.map Complex.ofReal)ᴴ (-(B.map Complex.ofReal)) C.complexify := by
  rw [show (signFlippedSaddlePointMatrix A B C).complexify =
    (fromBlocks A Bᵀ (-B) C).map Complex.ofReal from rfl, fromBlocks_map,
    map_ofReal_transpose]
  congr 1
  ext i j
  simp

omit [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
private theorem hermitianPart_complexify (A : Matrix n n ℝ) :
    A.complexify.hermitianPart = A.hermitianPart.complexify := by
  rw [hermitianPart, hermitianPart, complexify_smul, complexify_add, complexify_conjTranspose]
  norm_num

omit [Fintype m] [DecidableEq m] in
private theorem iInf_eigenvalues_pos [Nonempty n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    0 < ⨅ i, hA.isHermitian.eigenvalues i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ hA.isHermitian.eigenvalues
    Finset.univ_nonempty
  exact (hA.eigenvalues_pos i).trans_le (le_ciInf fun j => hi j (Finset.mem_univ _))

/-- **Theorem 3.5** of [benzi2005numerical]. The symmetric saddle-point spectrum lies
in the two Rusten–Winther intervals, in terms of the extreme eigenvalues of `A`
and singular values of `B`. -/
theorem theorem_3_5 [Nonempty n] [Nonempty m] {A : Matrix n n ℝ} {B : Matrix m n ℝ}
    (hA : A.PosDef) (hB : B.rank = Fintype.card m) :
    let μₙ := ⨅ i, hA.isHermitian.eigenvalues i
    let μ₁ := ⨆ i, hA.isHermitian.eigenvalues i
    let σₘ := B.sortedSingularValues (Fintype.card m - 1)
    let σ₁ := B.sortedSingularValues 0
    spectrum ℂ (saddlePointMatrix A B B 0).complexify ⊆ Complex.ofReal ''
      (Set.Icc ((μₙ - Real.sqrt (μₙ ^ 2 + 4 * σ₁ ^ 2)) / 2)
        ((μ₁ - Real.sqrt (μ₁ ^ 2 + 4 * σₘ ^ 2)) / 2) ∪
      Set.Icc μₙ ((μ₁ + Real.sqrt (μ₁ ^ 2 + 4 * σ₁ ^ 2)) / 2)) := by
  dsimp only
  have hM : (saddlePointMatrix A B B 0).IsHermitian := by
    simpa [saddleMatrix, saddlePointMatrix, conjTranspose_eq_transpose_of_trivial] using
      hA.isHermitian.saddleMatrix Bᵀ (isHermitian_zero : (0 : Matrix m m ℝ).IsHermitian)
  have hMc := (isHermitian_complexify_iff _).2 hM
  intro μ hμ
  obtain ⟨a, -, rfl⟩ := hMc.spectrum_eq_image_range ▸ hμ
  refine ⟨a, ?_, rfl⟩
  have ha := (ofReal_mem_spectrum_complexify_iff _ a).1 hμ
  simp only [saddlePointMatrix, neg_zero] at ha
  refine spectrum_fromBlocks_transpose_zero_subset B hA (fullRowRank_mulVec_transpose_injective hB)
    (iInf_eigenvalues_pos hA) (B.sortedSingularValues_nonneg _) ?_ ?_ ?_ ?_ ha
  · exact hA.isHermitian.posSemidef_sub_smul_one_of_le_eigenvalues
      (ciInf_le (Set.finite_range _).bddBelow)
  · exact hA.isHermitian.posSemidef_smul_one_sub_of_eigenvalues_le
      (le_ciSup (Set.finite_range _).bddAbove)
  · intro y
    have hσ : B.sortedSingularValues = Bᵀ.sortedSingularValues := by
      simpa [conjTranspose_eq_transpose_of_trivial] using
        (sortedSingularValues_conjTranspose B).symm
    rw [hσ, sortedSingularValues_eq_iInf_colSingularValues]
    exact Bᵀ.iInf_colSingularValues_mul_norm_le (toLp 2 y)
  · intro x
    rw [B.sortedSingularValues_zero_eq_l2_opNorm]
    exact B.l2_opNorm_mulVec (toLp 2 x)

/-- **Theorem 3.6** of [benzi2005numerical]. The sign-flipped matrix has
nonnegative quadratic form and nonnegative real parts of its eigenvalues.
The real parts are positive when the symmetric part of `A` is positive definite. -/
theorem theorem_3_6 {A : Matrix n n ℝ} {B : Matrix m n ℝ} {C : Matrix m m ℝ}
    (hA : A.hermitianPart.PosSemidef) (hB : B.rank = Fintype.card m)
    (hC : C.PosSemidef)
    (_hker : LinearMap.ker A.hermitianPart.mulVecLin ⊓ LinearMap.ker B.mulVecLin = ⊥) :
    let M := signFlippedSaddlePointMatrix A B C
    (∀ v, 0 ≤ v ⬝ᵥ (M *ᵥ v)) ∧
      (∀ μ ∈ spectrum ℂ M.complexify, 0 ≤ μ.re) ∧
      (A.hermitianPart.PosDef → ∀ μ ∈ spectrum ℂ M.complexify, 0 < μ.re) := by
  dsimp only
  refine ⟨dotProduct_fromBlocks_neg_transpose_mulVec_nonneg B hA hC, ?_, ?_⟩
  · intro μ hμ
    rw [complexify_signFlippedSaddlePointMatrix] at hμ
    exact re_nonneg_of_mem_spectrum_fromBlocks_neg_conjTranspose (B.map Complex.ofReal)ᴴ (by
      rw [hermitianPart_complexify]
      exact hA.complexify) hC.complexify (by simpa using hμ)
  · intro hA' μ hμ
    rw [complexify_signFlippedSaddlePointMatrix] at hμ
    exact re_pos_of_mem_spectrum_fromBlocks_neg_conjTranspose (by
      rw [hermitianPart_complexify, posDef_complexify_iff]
      exact hA') hC.complexify (Matrix.mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank hB)
      (by simpa using hμ)

/-- **Theorem 3.7** of [benzi2005numerical]. If the smallest eigenvalue of `A`
is at least four times the Euclidean operator norm of the Schur complement
`B A⁻¹ Bᵀ`, all eigenvalues of the sign-flipped matrix are real and positive. -/
theorem theorem_3_7 [Nonempty n] {A : Matrix n n ℝ} {B : Matrix m n ℝ}
    (hA : A.PosDef) (hB : B.rank = Fintype.card m)
    (hS : 4 * ‖B * A⁻¹ * Bᵀ‖ ≤ ⨅ i, hA.isHermitian.eigenvalues i) :
    ∀ μ ∈ spectrum ℂ (signFlippedSaddlePointMatrix A B 0).complexify,
      μ.im = 0 ∧ 0 < μ.re := by
  intro μ hμ
  rw [complexify_signFlippedSaddlePointMatrix, complexify_zero] at hμ
  let Bc := B.map Complex.ofReal
  have hBc := Matrix.mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank hB
  have hAc : A.complexify.PosDef := posDef_complexify_iff.2 hA
  have hmin :
      ∀ x : n → ℂ, (⨅ i, hA.isHermitian.eigenvalues i) * ‖toLp 2 x‖ ^ 2 ≤
        (star x ⬝ᵥ (A.complexify *ᵥ x)).re := by
    let a := ⨅ i, hA.isHermitian.eigenvalues i
    have ha : (A - a • 1).PosSemidef :=
      hA.isHermitian.posSemidef_sub_smul_one_of_le_eigenvalues
        (ciInf_le (Set.finite_range _).bddBelow)
    intro x
    have h := (Complex.nonneg_iff.1 (ha.complexify.dotProduct_mulVec_nonneg x)).1
    rw [complexify_sub, complexify_smul, complexify_one, sub_mulVec, smul_mulVec,
      one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, star_dotProduct_self] at h
    change 0 ≤ (star x ⬝ᵥ (A.complexify *ᵥ x) -
      (a : ℂ) * ((‖toLp 2 x‖ : ℝ) : ℂ) ^ 2).re at h
    rw [← Complex.ofReal_pow, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
    exact sub_nonneg.mp h
  have hSc : ‖Bc * A.complexify⁻¹ * Bcᴴ‖ = ‖B * A⁻¹ * Bᵀ‖ := by
    rw [← l2_opNorm_complexify]
    congr 1
    have h : (B * A⁻¹ * Bᵀ).map Complex.ofRealHom =
        B.map Complex.ofRealHom * (A⁻¹).map Complex.ofRealHom * Bᵀ.map Complex.ofRealHom := by
      simp only [Matrix.map_mul]
    rw [show (B * A⁻¹ * Bᵀ).complexify =
      Bc * (A⁻¹).complexify * Bᵀ.map Complex.ofReal from h, complexify_inv,
      map_ofReal_transpose]
  refine ⟨im_eq_zero_of_mem_spectrum_fromBlocks_neg_conjTranspose_zero
    hAc hBc hmin (hSc.symm ▸ hS) hμ, ?_⟩
  exact re_pos_of_mem_spectrum_fromBlocks_neg_conjTranspose
    (hAc.isHermitian.hermitianPart_eq.symm ▸ hAc) PosSemidef.zero hBc (by simpa using hμ)

section ScalarDiagonal

variable {rows cols : ℕ}

/-- The scalar-block matrices in equation (3.13) of [benzi2005numerical],
with `ε = 1` for the symmetric form and `ε = -1` for the sign-flipped form. -/
abbrev scaledSaddlePointMatrix (B : Matrix (Fin rows) (Fin cols) ℝ) (η ε : ℝ) :
    Matrix (Fin cols ⊕ Fin rows) (Fin cols ⊕ Fin rows) ℝ :=
  fromBlocks (η • 1) Bᵀ (ε • B) 0

/-- Square root of the discriminant for the sign-flipped form in Theorem 3.8. -/
noncomputable def signFlippedDiscriminantRoot (η σ : ℝ) : ℂ :=
  if 2 * σ ≤ η then (Real.sqrt (η ^ 2 - 4 * σ ^ 2) : ℂ)
  else Complex.I * (Real.sqrt (4 * σ ^ 2 - η ^ 2) : ℂ)

private theorem signFlippedDiscriminantRoot_sq {η σ : ℝ} (hη : 0 < η) (hσ : 0 ≤ σ) :
    signFlippedDiscriminantRoot η σ ^ 2 = (η : ℂ) ^ 2 - 4 * (σ : ℂ) ^ 2 := by
  unfold signFlippedDiscriminantRoot
  split_ifs with h
  · have hnonneg : 0 ≤ η ^ 2 - 4 * σ ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ η - 2 * σ by linarith)
        (show 0 ≤ η + 2 * σ by positivity)]
    rw [← Complex.ofReal_pow, Real.sq_sqrt hnonneg]
    push_cast
    ring
  · have hnonneg : 0 ≤ 4 * σ ^ 2 - η ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ 2 * σ - η by linarith)
        (show 0 ≤ η + 2 * σ by positivity)]
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hnonneg]
    push_cast
    ring

/-- **Theorem 3.8** of [benzi2005numerical]. The complex eigenvalues, counted with
algebraic multiplicity, are zero and `η` with multiplicities given by the
left and right nullities, and the stated pair of roots for each nonzero
singular value. The sign-flipped discriminant gives a complex conjugate pair
when `σ > η / 2`, including both roots with their multiplicities. -/
theorem theorem_3_8 (hmn : rows ≤ cols) (B : Matrix (Fin rows) (Fin cols) ℝ)
    {η : ℝ} (hη : 0 < η) :
    let base := (rows - B.rank) • ({0} : Multiset ℂ) +
      (cols - B.rank) • ({(η : ℂ)} : Multiset ℂ)
    let pair (d : ℂ) := ({((η : ℂ) + d) / 2} : Multiset ℂ) + {((η : ℂ) - d) / 2}
    ((scaledSaddlePointMatrix B η 1).complexify.charpoly.roots =
      base + Finset.univ.val.bind (fun i : Fin B.rank =>
        pair (Real.sqrt (4 * B.sortedSingularValues i ^ 2 + η ^ 2) : ℂ))) ∧
    ((scaledSaddlePointMatrix B η (-1)).complexify.charpoly.roots =
      base + Finset.univ.val.bind (fun i : Fin B.rank =>
        pair (signFlippedDiscriminantRoot η (B.sortedSingularValues i)))) := by
  dsimp only
  constructor
  · refine roots_charpoly_complexify_fromBlocks_smul_one_transpose_zero hmn B η 1 _ ?_
    intro i
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  · refine roots_charpoly_complexify_fromBlocks_smul_one_transpose_zero hmn B η (-1) _ ?_
    intro i
    rw [signFlippedDiscriminantRoot_sq hη (B.sortedSingularValues_nonneg _)]
    push_cast
    ring

/-- In the nonreal branch of Theorem 3.8, each root has real part `η / 2`. -/
theorem signFlipped_roots_re_of_lt {η σ : ℝ} (h : η < 2 * σ) :
    (((η : ℂ) + signFlippedDiscriminantRoot η σ) / 2).re = η / 2 ∧
      (((η : ℂ) - signFlippedDiscriminantRoot η σ) / 2).re = η / 2 := by
  simp [signFlippedDiscriminantRoot, not_le.mpr h, Complex.mul_re]

end ScalarDiagonal

end BenziGolubLiesen
