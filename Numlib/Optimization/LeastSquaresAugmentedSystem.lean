import Numlib.Optimization.LeastSquaresModel
import Mathlib.Data.Matrix.Block
import Numlib.Optimization.WeightedQuadraticSubproblem

/-!
# Augmented systems for regularized least squares

Eliminating the residual variable identifies the saddle system with the normal equation.
This algebraic equivalence does not require an invertible normal matrix.
-/

noncomputable section
namespace Matrix.LeastSquaresModel
variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- The saddle matrix with residual variables ordered after step variables. -/
def augmentedMatrix (J : Matrix ι κ R) (M : Matrix κ κ R) (lambda : R) :
    Matrix (κ ⊕ ι) (κ ⊕ ι) R := fromBlocks (lambda • M) Jᵀ J (-1)

/-- The actual block equation with right-hand side `-(0,r)`. -/
def IsAugmentedSolution (J : Matrix ι κ R) (M : Matrix κ κ R) (lambda : R)
    (r : ι → R) (s : κ → R) (z : ι → R) : Prop :=
  augmentedMatrix J M lambda *ᵥ Sum.elim s z = Sum.elim (fun _ => 0) (-r)

/-- The two rows expose stationarity and the actual residual definition. -/
theorem isAugmentedSolution_iff_rows (J : Matrix ι κ R) (M : Matrix κ κ R)
    (lambda : R) (r : ι → R) (s : κ → R) (z : ι → R) :
    IsAugmentedSolution J M lambda r s z ↔
      (lambda • M) *ᵥ s + Jᵀ *ᵥ z = 0 ∧ J *ᵥ s - z = -r := by
  unfold IsAugmentedSolution augmentedMatrix
  rw [fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, neg_mulVec, one_mulVec,
    sub_eq_add_neg]
  constructor
  · intro h
    exact ⟨congrArg (fun v => v ∘ Sum.inl) h, congrArg (fun v => v ∘ Sum.inr) h⟩
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]
    rfl

/-- Eliminating the residual variable gives the regularized normal equation. -/
theorem isAugmentedSolution_iff_normal (J : Matrix ι κ R) (M : Matrix κ κ R)
    (lambda : R) (r : ι → R) (s : κ → R) (z : ι → R) :
    IsAugmentedSolution J M lambda r s z ↔
      (Jᵀ * J + lambda • M) *ᵥ s = -(Jᵀ *ᵥ r) ∧ z = J *ᵥ s + r := by
  rw [isAugmentedSolution_iff_rows]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hz : z = J *ᵥ s + r := by
      funext i
      have hh := congrFun h₂ i
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply] at hh ⊢
      linear_combination -hh
    refine ⟨?_, hz⟩
    rw [hz, mulVec_add] at h₁
    rw [add_mulVec, ← mulVec_mulVec]
    funext i
    have hh := congrFun h₁ i
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hh ⊢
    linear_combination hh
  · rintro ⟨h, hz⟩
    constructor
    · rw [hz, mulVec_add]
      rw [add_mulVec, ← mulVec_mulVec] at h
      funext i
      have hh := congrFun h i
      simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hh ⊢
      linear_combination hh
    · rw [hz]
      abel

/-- The normal equation is equivalent to existence of an actual residual block solution. -/
theorem normal_iff_exists_augmented (J : Matrix ι κ R) (M : Matrix κ κ R)
    (lambda : R) (r : ι → R) (s : κ → R) :
    (Jᵀ * J + lambda • M) *ᵥ s = -(Jᵀ *ᵥ r) ↔
      ∃ z, IsAugmentedSolution J M lambda r s z := by
  constructor
  · intro h
    exact ⟨J *ᵥ s + r, (isAugmentedSolution_iff_normal J M lambda r s _).2 ⟨h, rfl⟩⟩
  · rintro ⟨z, hz⟩
    exact ((isAugmentedSolution_iff_normal J M lambda r s z).1 hz).1

omit [DecidableEq ι] [Fintype κ] in
/-- A nonnegative semidefinite metric shift preserves Gram positivity. -/
theorem shiftedGram_posSemidef [Finite κ] (J : Matrix ι κ ℝ) {M : Matrix κ κ ℝ}
    (hM : M.PosSemidef) {lambda : ℝ} (hl : 0 ≤ lambda) :
    (Jᵀ * J + lambda • M).PosSemidef :=
  (gram_posSemidef J).add (hM.smul hl)

omit [DecidableEq ι] in
/-- The Gram Hessian remains positive after transport to any positive definite metric. -/
theorem energyHessian_gram_isPositive [DecidableEq κ] (J : Matrix ι κ ℝ)
    {M : Matrix κ κ ℝ} (hM : M.PosDef) :
    (Optimization.QuadraticSubproblem.energyHessian hM.isPreconditioner_toEuclideanLin
      (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℝ) (Jᵀ * J))).IsPositive := by
  have hH := gram_posSemidef J
  have hh := (Optimization.QuadraticSubproblem.isPositive_energy_shift_iff
    hM.isPreconditioner_toEuclideanLin
    (H := Matrix.toEuclideanCLM (n := κ) (𝕜 := ℝ) (Jᵀ * J))
    hH.isSymm.isSymmetric_toEuclideanLin 0).2 (by
      simpa only [zero_smul, add_zero, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
        (Matrix.isPositive_toEuclideanLin_iff.mpr hH))
  simpa only [zero_smul, add_zero] using hh

omit [DecidableEq ι] [Fintype κ] in
/-- A positive metric shift makes the Gram matrix positive definite. -/
theorem shiftedGram_posDef [Finite κ] (J : Matrix ι κ ℝ) {M : Matrix κ κ ℝ}
    (hM : M.PosDef) {lambda : ℝ} (hl : 0 < lambda) :
    (Jᵀ * J + lambda • M).PosDef :=
  Matrix.PosDef.posSemidef_add (gram_posSemidef J) (hM.smul hl)

omit [DecidableEq ι] in
/-- Applying the actual inverse gives a solution of the positive-shift normal equation. -/
theorem inverse_normal_solution [DecidableEq κ] (J : Matrix ι κ ℝ) {M : Matrix κ κ ℝ}
    (hM : M.PosDef) {lambda : ℝ} (hl : 0 < lambda) (r : ι → ℝ) :
    (Jᵀ * J + lambda • M) *ᵥ
      ((Jᵀ * J + lambda • M)⁻¹ *ᵥ (-(Jᵀ *ᵥ r))) = -(Jᵀ *ᵥ r) := by
  classical
  let A := Jᵀ * J + lambda • M
  have hA : A.PosDef := shiftedGram_posDef J hM hl
  rw [mulVec_mulVec, A.mul_nonsing_inv (A.isUnit_iff_isUnit_det.mp hA.isUnit), one_mulVec]

omit [DecidableEq ι] in
/-- The positive-shift normal equation has a unique solution given by the actual inverse. -/
theorem existsUnique_normal_solution (J : Matrix ι κ ℝ) {M : Matrix κ κ ℝ}
    (hM : M.PosDef) {lambda : ℝ} (hl : 0 < lambda) (r : ι → ℝ) :
    ∃! s : κ → ℝ, (Jᵀ * J + lambda • M) *ᵥ s = -(Jᵀ *ᵥ r) := by
  classical
  have hs := inverse_normal_solution J hM hl r
  exact ⟨(Jᵀ * J + lambda • M)⁻¹ *ᵥ (-(Jᵀ *ᵥ r)), hs,
    fun y hy => (shiftedGram_posDef J hM hl).mulVec_injective (hy.trans hs.symm)⟩

/-- The augmented saddle system has exactly one solution at every positive metric shift. -/
theorem existsUnique_augmentedSolution (J : Matrix ι κ ℝ) {M : Matrix κ κ ℝ}
    (hM : M.PosDef) {lambda : ℝ} (hl : 0 < lambda) (r : ι → ℝ) :
    ∃! sz : (κ → ℝ) × (ι → ℝ), IsAugmentedSolution J M lambda r sz.1 sz.2 := by
  obtain ⟨s, hs, huniq⟩ := existsUnique_normal_solution J hM hl r
  refine ⟨(s, J *ᵥ s + r), (isAugmentedSolution_iff_normal J M lambda r s _).2
    ⟨hs, rfl⟩, ?_⟩
  intro yz hy
  obtain ⟨hyn, hyz⟩ := (isAugmentedSolution_iff_normal J M lambda r yz.1 yz.2).1 hy
  have hys := huniq yz.1 hyn
  exact Prod.ext hys (hyz.trans (by rw [hys]))

end Matrix.LeastSquaresModel
