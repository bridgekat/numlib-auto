import Numlib.Analysis.Calculus.NormRpowHessian
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Least bilinear curvature

The infimum of a bounded real bilinear form over nonzero Rayleigh quotients has the usual
quadratic lower-bound interface. For symmetric forms in finite dimension it is an actual
eigenvalue of the Riesz-represented operator.
-/
noncomputable section
namespace Optimization
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Rayleigh infimum of a continuous bilinear form, with zero vectors excluded. -/
def leastCurvature (B : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  ⨅ u : {u : E // u ≠ 0}, B u u / ‖(u : E)‖ ^ 2

/-- Rayleigh quotients are bounded below by the negative bilinear operator norm. -/
theorem bddBelow_bilinearRayleigh (B : E →L[ℝ] E →L[ℝ] ℝ) :
    BddBelow (Set.range fun u : {u : E // u ≠ 0} => B u u / ‖(u : E)‖ ^ 2) := by
  refine ⟨-‖B‖, ?_⟩
  rintro _ ⟨u, rfl⟩
  rw [le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr u.property))]
  have h := (abs_le.mp (ContinuousLinearMap.abs_apply_self_le B (u : E))).1
  nlinarith

/-- A lower bound on least curvature is equivalent to a quadratic-form lower bound. -/
theorem le_leastCurvature_iff [Nontrivial E] (B : E →L[ℝ] E →L[ℝ] ℝ) (a : ℝ) :
    a ≤ leastCurvature B ↔ ∀ u : E, a * ‖u‖ ^ 2 ≤ B u u := by
  have : Nonempty {u : E // u ≠ 0} := by
    obtain ⟨u, hu⟩ := exists_ne (0 : E)
    exact ⟨⟨u, hu⟩⟩
  rw [leastCurvature, le_ciInf_iff (bddBelow_bilinearRayleigh B)]
  constructor
  · intro h u
    by_cases hu : u = 0
    · simp [hu]
    · exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hu))).mp (h ⟨u, hu⟩)
  · intro h u
    exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr u.property))).mpr (h u)

/-- An exactly scalar quadratic form has that scalar as its least curvature. -/
theorem leastCurvature_eq_of_scalar [Nontrivial E] (H : E →L[ℝ] E →L[ℝ] ℝ)
    {a : ℝ} (hH : ∀ u, H u u = a * ‖u‖ ^ 2) : leastCurvature H = a := by
  apply le_antisymm
  · obtain ⟨u, hu⟩ := exists_ne (0 : E)
    have hh := ciInf_le (bddBelow_bilinearRayleigh H) (⟨u, hu⟩ : {u : E // u ≠ 0})
    have hn : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
    change leastCurvature H ≤ H u u / ‖u‖ ^ 2 at hh
    rw [hH, mul_div_cancel_right₀ a hn] at hh
    exact hh
  · exact (le_leastCurvature_iff H a).mpr (fun u => (hH u).ge)

variable [CompleteSpace E]

/-- A symmetric bilinear form gives a symmetric represented operator. -/
theorem bilinearOperator_isSymmetric {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ u v, B u v = B v u) : (continuousLinearMapOfBilin B).toLinearMap.IsSymmetric := by
  intro u v
  change inner ℝ (continuousLinearMapOfBilin B u) v = inner ℝ u (continuousLinearMapOfBilin B v)
  rw [continuousLinearMapOfBilin_apply, real_inner_comm, continuousLinearMapOfBilin_apply]
  exact hB u v

/-- In finite dimension, least curvature of a symmetric form is an actual eigenvalue. -/
theorem hasEigenvalue_leastCurvature [FiniteDimensional ℝ E] [Nontrivial E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : ∀ u v, B u v = B v u) :
    Module.End.HasEigenvalue (continuousLinearMapOfBilin B).toLinearMap (leastCurvature B) := by
  simpa [leastCurvature] using
    (bilinearOperator_isSymmetric hB).hasEigenvalue_iInf_of_finiteDimensional

/-- Least curvature is no larger than any eigenvalue of the represented operator. -/
theorem leastCurvature_le_eigenvalue [Nontrivial E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} {mu : ℝ}
    (hmu : Module.End.HasEigenvalue (continuousLinearMapOfBilin B).toLinearMap mu) :
    leastCurvature B ≤ mu := by
  obtain ⟨v, hv, hv0⟩ := hmu.exists_hasEigenvector
  have he : continuousLinearMapOfBilin B v = mu • v :=
    Module.End.mem_eigenspace_iff.mp hv
  have hform : B v v = mu * ‖v‖ ^ 2 := by
    rw [← continuousLinearMapOfBilin_apply B, he, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hq : B v v / ‖v‖ ^ 2 = mu := by rw [hform]; field_simp
  rw [← hq]
  exact ciInf_le (bddBelow_bilinearRayleigh B) ⟨v, hv0⟩

/-- In finite dimension a symmetric form attains its least curvature in a unit direction. -/
theorem exists_unit_leastCurvature [FiniteDimensional ℝ E] [Nontrivial E]
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : ∀ u v, B u v = B v u) :
    ∃ u : E, ‖u‖ = 1 ∧ B u u = leastCurvature B := by
  obtain ⟨v, hv, hv0⟩ := (hasEigenvalue_leastCurvature hB).exists_hasEigenvector
  have he : continuousLinearMapOfBilin B v = leastCurvature B • v :=
    Module.End.mem_eigenspace_iff.mp hv
  have hform : B v v = leastCurvature B * ‖v‖ ^ 2 := by
    rw [← continuousLinearMapOfBilin_apply B, he, real_inner_smul_left, real_inner_self_eq_norm_sq]
  refine ⟨NormedSpace.normalize v, NormedSpace.norm_normalize hv0, ?_⟩
  simp only [NormedSpace.normalize, map_smul, smul_apply, smul_eq_mul, hform]
  field_simp

omit [CompleteSpace E] in
/-- Hessians of twice differentiable scalar objectives are symmetric bilinear forms. -/
theorem hessian_symmetric {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    ∀ u v, fderiv ℝ (fderiv ℝ f) x u v = fderiv ℝ (fderiv ℝ f) x v u :=
  hf.isSymmSndFDerivAt (by norm_num)

end Optimization
