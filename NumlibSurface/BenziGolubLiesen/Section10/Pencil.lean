/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Preconditioner.ConstraintPencil

/-!
# Benzi, Golub and Liesen, Section 10.2

The generalized eigenproblem in equation (10.21) and the corrected Lemma 10.2 of
[benzi2005numerical]. The zero eigenspace is the product of the kernel of the primal block and
the entire multiplier space. The spectral interval includes zero as a possible endpoint on
either side. For example, scalar blocks `B = C = 1` and `E = -1` have a nonzero eigenvalue
`-1/2`, which exceeds the largest eigenvalue of `E`.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
variable {B : Matrix m n ℝ} {C : Matrix m m ℝ} {E : Matrix n n ℝ}
variable {γ : ℂ} {x : n → ℂ} {y : m → ℂ}

/-- Equation (10.21) of [benzi2005numerical], interpreted over complex eigenvectors. -/
abbrev IsConstraintPencilEigenvector (B : Matrix m n ℝ) (C : Matrix m m ℝ)
    (E : Matrix n n ℝ) (γ : ℂ) (x : n → ℂ) (y : m → ℂ) : Prop :=
  Matrix.HasPencilEigenvector (fromBlocks E.complexify 0 0 0)
    (fromBlocks 1 (B.map Complex.ofReal)ᴴ (B.map Complex.ofReal) (-C.complexify)) γ (Sum.elim x y)

/-- **Lemma 10.2(i)** of [benzi2005numerical]. If `C` is positive definite and `E x ≠ 0`, the
eigenvalue is the nonzero Rayleigh quotient obtained by eliminating the multiplier. -/
theorem lemma_10_2_i [DecidableEq m] (hB : B.rank = Fintype.card m) (hC : C.PosDef)
    (h : IsConstraintPencilEigenvector B C E γ x y) (hEx : E.complexify *ᵥ x ≠ 0) :
    γ = (star x ⬝ᵥ (E.complexify *ᵥ x)) /
      (star x ⬝ᵥ ((1 + (B.map Complex.ofReal)ᴴ * C.complexify⁻¹ *
        (B.map Complex.ofReal)) *ᵥ x)) ∧ γ ≠ 0 :=
  h.primalBlock_eq_rayleigh (mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank hB)
    (posDef_complexify_iff.mpr hC) hEx

/-- **Lemma 10.2(ii)** of [benzi2005numerical], corrected. For an eigenpair, the eigenvalue is
zero exactly when `E x = 0`. The multiplier may be zero when the primal component is nonzero.
The dimension of the zero eigenspace is the nullity of the complexification of `E` plus `m`. -/
theorem lemma_10_2_ii (hB : B.rank = Fintype.card m) (hC : C.PosSemidef)
    (h : IsConstraintPencilEigenvector B C E γ x y) :
    (γ = 0 ↔ E.complexify *ᵥ x = 0) ∧
    Module.finrank ℂ (LinearMap.ker
      (fromBlocks E.complexify 0 0 (0 : Matrix m m ℂ)).mulVecLin) =
      Module.finrank ℂ (LinearMap.ker E.complexify.mulVecLin) + Fintype.card m :=
  ⟨h.primalBlock_eq_zero_iff (mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank hB)
      hC.complexify,
    finrank_ker_fromBlocks_primal E.complexify⟩

/-- **Lemma 10.2(iii)** of [benzi2005numerical], corrected. Each nonzero eigenvalue is real and lies
between `min 0 (λmin E)` and `max 0 (λmax E)`. -/
theorem lemma_10_2_iii [Nonempty n] (hB : B.rank = Fintype.card m) (hC : C.PosSemidef)
    (hE : E.IsHermitian) (h : IsConstraintPencilEigenvector B C E γ x y) (hγ : γ ≠ 0) :
    γ ∈ Complex.ofReal '' Set.Icc (min 0 (⨅ i, hE.eigenvalues i))
      (max 0 (⨆ i, hE.eigenvalues i)) := by
  have hEc : E.complexify.IsHermitian := (isHermitian_complexify_iff _).mpr hE
  have hbounds := hEc.isSymmetricBoundedBy_toEuclideanLin
    (lmin := ⨅ i, hE.eigenvalues i) (lmax := ⨆ i, hE.eigenvalues i)
  refine h.primalBlock_mem_interval (mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank hB)
    hC.complexify (hbounds fun i ↦ ?_) hγ
  have hμ := (ofReal_mem_spectrum_complexify_iff E (hEc.eigenvalues i)).mp
    (hEc.eigenvalues_mem_spectrum_real i)
  rw [hE.spectrum_real_eq_range_eigenvalues] at hμ
  obtain ⟨j, hj⟩ := hμ
  rw [← hj]
  exact ⟨ciInf_le (Set.finite_range _).bddBelow j, le_ciSup (Set.finite_range _).bddAbove j⟩

/-- Scalar counterexample to requiring a nonzero multiplier in Lemma 10.2(ii). -/
theorem lemma_10_2_zero_multiplier_example :
    IsConstraintPencilEigenvector (1 : Matrix Unit Unit ℝ) 1 0 0
      (fun _ ↦ 1) (fun _ ↦ 0) := by
  constructor
  · intro h
    have h0 := congrFun h (Sum.inl ())
    norm_num at h0
  · simp

/-- Scalar counterexample to the printed upper bound in Lemma 10.2(iii).
The pencil has eigenvalue `-1/2` while the only eigenvalue of `E` is `-1`. -/
theorem lemma_10_2_upper_endpoint_example :
    IsConstraintPencilEigenvector (1 : Matrix Unit Unit ℝ) 1 (-1) (-1 / 2)
      (fun _ ↦ 1) (fun _ ↦ 1) ∧
      spectrum ℝ (-1 : Matrix Unit Unit ℝ) = {-1} := by
  constructor
  · constructor
    · intro h
      have h0 := congrFun h (Sum.inl ())
      norm_num at h0
    · rw [fromBlocks_mulVec, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
      funext i
      cases i <;> norm_num [Matrix.mulVec, dotProduct, Matrix.one_apply, Complex.ofReal_neg,
        Complex.ofReal_one]
  · simpa only [map_neg, map_one] using spectrum.scalar_eq (A := Matrix Unit Unit ℝ) (-1 : ℝ)

end BenziGolubLiesen
