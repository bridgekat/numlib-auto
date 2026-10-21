import Numlib.Optimization.WeightedQuadraticSubproblem
import Numlib.Optimization.QuadraticDerivatives
import Numlib.Analysis.Calculus.LinearPullback
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual derivatives of weighted power models

The metric norm is transported to the energy inner product space. Pulling back its actual
radial derivatives retains the original metric in the gradient and the rank-one Hessian.
-/

noncomputable section
open scoped InnerProductSpace
namespace Optimization.QuadraticSubproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M Minv : E →ₗ[ℝ] E}

/-- The metric transport as a continuous linear map in finite dimension. -/
abbrev energyEmbedding (hM : Krylov.IsPreconditioner M Minv) : E →L[ℝ] hM.EnergySpace :=
  hM.toEnergy.toLinearMap.toContinuousLinearMap

/-- The continuous metric transport is the original linear energy equivalence. -/
@[simp] theorem energyEmbedding_apply (hM : Krylov.IsPreconditioner M Minv) (s : E) :
    energyEmbedding hM s = hM.toEnergy s := rfl

/-- Powers above two of an SPD metric norm are globally twice continuously differentiable. -/
theorem contDiff_two_energyNorm_rpow (hM : Krylov.IsPreconditioner M Minv)
    {r : ℝ} (hr : 2 < r) : ContDiff ℝ 2 (fun s : E => energyNorm M s ^ r) := by
  simpa only [Function.comp_def, energyEmbedding_apply, WithEnergy.norm_equiv] using
    (contDiff_two_norm_rpow (E := hM.EnergySpace) hr).comp (energyEmbedding hM).contDiff

/-- The genuine metric radial derivative contains the metric applied to the point. -/
theorem hasFDerivAt_energyNorm_rpow (hM : Krylov.IsPreconditioner M Minv)
    {r : ℝ} (hr : 1 < r) (s : E) :
    HasFDerivAt (fun x : E => energyNorm M x ^ r)
      ((r * energyNorm M s ^ (r - 2)) • innerSL ℝ (M s)) s := by
  have h := (hasFDerivAt_norm_rpow (energyEmbedding hM s) hr).comp s
    (energyEmbedding hM).hasFDerivAt
  convert h using 1
  · rfl
  · ext u
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      innerSL_apply_apply, energyEmbedding_apply, WithEnergy.norm_equiv,
      WithEnergy.inner_equiv, energyInner, smul_eq_mul]

/-- The actual metric radial Hessian evaluated on arbitrary directions, including the origin. -/
theorem fderiv_fderiv_energyNorm_rpow_apply (hM : Krylov.IsPreconditioner M Minv)
    {r : ℝ} (hr : 2 < r) (s u v : E) :
    fderiv ℝ (fderiv ℝ (fun x : E => energyNorm M x ^ r)) s u v =
      r * energyNorm M s ^ (r - 2) * inner ℝ (M u) v +
      r * (r - 2) * energyNorm M s ^ (r - 4) * inner ℝ (M s) u * inner ℝ (M s) v := by
  have h := (energyEmbedding hM).secondFDeriv_comp_right_apply
    (contDiff_two_norm_rpow (E := hM.EnergySpace) hr) s u v
  simpa only [energyEmbedding_apply, WithEnergy.norm_equiv,
    fderiv_fderiv_norm_rpow hr, normRpowHessian_apply,
    WithEnergy.inner_equiv, energyInner, mul_assoc] using h

/-- The weighted regularized model is genuinely C² for every exponent above two. -/
theorem contDiff_two_weightedPowerQuadratic (hM : Krylov.IsPreconditioner M Minv)
    (g : E) (H : E →L[ℝ] E) (sigma : ℝ) {r : ℝ} (hr : 2 < r) :
    ContDiff ℝ 2 (weightedPowerQuadratic g H M sigma r) := by
  have hq := contDiff_quadratic g H 2
  exact hq.add ((contDiff_two_energyNorm_rpow hM hr).const_smul (sigma / r))

/-- The actual weighted-model derivative is represented by its metric radial gradient. -/
theorem hasFDerivAt_weightedPowerQuadratic (hM : Krylov.IsPreconditioner M Minv)
    (g : E) {H : E →L[ℝ] E} (hH : H.IsSymmetric) (sigma : ℝ) {r : ℝ} (hr : 1 < r)
    (s : E) : HasFDerivAt (weightedPowerQuadratic g H M sigma r)
      (innerSL ℝ (g + H s + (sigma * energyNorm M s ^ (r - 2)) • M s)) s := by
  have h := (hasFDerivAt_quadratic g hH s).add
    ((hasFDerivAt_energyNorm_rpow hM hr s).const_mul (sigma / r))
  have he : innerSL ℝ (g + H s + (sigma * energyNorm M s ^ (r - 2)) • M s) =
      innerSL ℝ (g + H s) + (sigma / r) •
        ((r * energyNorm M s ^ (r - 2)) • innerSL ℝ (M s)) := by
    ext u
    simp only [innerSL_apply_apply, inner_add_left, inner_smul_left, RCLike.conj_to_real,
      add_apply, smul_apply, smul_eq_mul]
    field_simp
  rw [he]
  exact h

/-- The metric regularized Hessian is the original Hessian plus its radial and rank-one terms. -/
theorem fderiv_fderiv_weightedPowerQuadratic_apply (hM : Krylov.IsPreconditioner M Minv)
    (g : E) {H : E →L[ℝ] E} (hH : H.IsSymmetric) (sigma : ℝ) {r : ℝ} (hr : 2 < r)
    (s u v : E) :
    fderiv ℝ (fderiv ℝ (weightedPowerQuadratic g H M sigma r)) s u v =
      inner ℝ (H u) v + sigma * energyNorm M s ^ (r - 2) * inner ℝ (M u) v +
      sigma * (r - 2) * energyNorm M s ^ (r - 4) * inner ℝ (M s) u * inner ℝ (M s) v := by
  have hq := contDiff_quadratic g H 2
  have hw := contDiff_two_energyNorm_rpow hM hr
  have hsum := iteratedFDeriv_add_apply hq.contDiffAt
    ((hw.const_smul (sigma / r)).contDiffAt (x := s))
  rw [iteratedFDeriv_const_smul_apply' hw.contDiffAt] at hsum
  have h := congrArg (fun A : E [×2]→L[ℝ] ℝ => A ![u, v]) hsum
  simp only [
    add_apply, smul_apply, smul_eq_mul, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_fderiv_quadratic_apply g hH,
    fderiv_fderiv_energyNorm_rpow_apply hM hr] at h
  change fderiv ℝ (fderiv ℝ (weightedPowerQuadratic g H M sigma r)) s u v = _ at h
  rw [h]
  have hr0 : r ≠ 0 := by linarith
  field_simp
  ring

/-- Split a radial power into its quadratic and residual factors, also at zero. -/
theorem sq_mul_rpow_sub_two {a r : ℝ} (ha : 0 ≤ a) (hr : 2 < r) :
    a ^ 2 * a ^ (r - 2) = a ^ r := by
  by_cases h0 : a = 0
  · simp [h0, Real.zero_rpow (by linarith : r ≠ 0)]
  · have hp : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    rw [← Real.rpow_natCast, ← Real.rpow_add hp]
    congr 1
    norm_num

omit [FiniteDimensional ℝ E] in
/-- Shifted stationarity splits the actual model into shifted energy and radial error. -/
theorem weightedPowerQuadratic_eq_of_shift (hM : Krylov.IsPreconditioner M Minv)
    (g : E) (H : E →L[ℝ] E) (sigma : ℝ) {r : ℝ} (hr : 2 < r) {s : E} {lambda : ℝ}
    (hstat : g + H s + lambda • M s = 0) :
    weightedPowerQuadratic g H M sigma r s =
      -(1 / 2 : ℝ) * inner ℝ s (H s + lambda • M s) +
        energyNorm M s ^ 2 * (sigma / r * energyNorm M s ^ (r - 2) - lambda / 2) := by
  have he := congrArg (fun z => inner ℝ z s) hstat
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real, inner_zero_left] at he
  have hn : energyNorm M s ^ 2 = inner ℝ (M s) s := by
    simpa only [RCLike.re_to_real] using hM.isSymmetricCoercive.energyNorm_sq s
  unfold weightedPowerQuadratic quadratic
  rw [← sq_mul_rpow_sub_two (energyNorm_nonneg M s) hr, hn, inner_add_right,
    inner_smul_right, real_inner_comm (H s) s, real_inner_comm (M s) s]
  nlinarith

/-- The shifted linear residual determines the entire actual weighted-model gradient. -/
theorem gradient_weightedPowerQuadratic_of_shift (hM : Krylov.IsPreconditioner M Minv)
    {g s : E} {H : E →L[ℝ] E} (hH : H.IsSymmetric) (sigma : ℝ) {r : ℝ} (hr : 1 < r)
    {lambda : ℝ} (hstat : g + H s + lambda • M s = 0) :
    gradient (weightedPowerQuadratic g H M sigma r) s =
      (sigma * energyNorm M s ^ (r - 2) - lambda) • M s := by
  have hg : HasGradientAt (weightedPowerQuadratic g H M sigma r)
      (g + H s + (sigma * energyNorm M s ^ (r - 2)) • M s) s := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hasFDerivAt_weightedPowerQuadratic hM g hH sigma hr s
  rw [hg.gradient]
  have hs : g + H s = -(lambda • M s) := eq_neg_of_add_eq_zero_left hstat
  rw [hs, sub_smul]
  abel

omit [FiniteDimensional ℝ E] in
/-- Multiplication by the metric turns its primal norm into the inverse-metric dual norm. -/
theorem energyNorm_inverse_smul_apply (hM : Krylov.IsPreconditioner M Minv) (c : ℝ) (s : E) :
    energyNorm Minv (c • M s) = |c| * energyNorm M s := by
  have he : inner ℝ (Minv (c • M s)) (c • M s) = c ^ 2 * inner ℝ (M s) s := by
    rw [map_smul, hM.inv_apply, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (M s) s]
    ring
  simp only [energyNorm, RCLike.re_to_real, he]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The actual shifted gradient residual has its exact inverse-metric norm. -/
theorem energyNorm_gradient_weightedPowerQuadratic_of_shift
    (hM : Krylov.IsPreconditioner M Minv) {g s : E} {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) (sigma : ℝ) {r : ℝ} (hr : 1 < r) {lambda : ℝ}
    (hstat : g + H s + lambda • M s = 0) :
    energyNorm Minv (gradient (weightedPowerQuadratic g H M sigma r) s) =
      |sigma * energyNorm M s ^ (r - 2) - lambda| * energyNorm M s := by
  rw [gradient_weightedPowerQuadratic_of_shift hM hH sigma hr hstat,
    energyNorm_inverse_smul_apply hM]

/-- A positive shifted Hessian gives a lower metric bound on the actual model Hessian. -/
theorem weightedPowerQuadratic_hessian_lower_of_shift
    (hM : Krylov.IsPreconditioner M Minv) (g : E) {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) {sigma r lambda : ℝ} (hsigma : 0 ≤ sigma) (hr : 2 < r)
    (hA : (H + lambda • M.toContinuousLinearMap).IsPositive) (s d : E) :
    (sigma * energyNorm M s ^ (r - 2) - lambda) * energyNorm M d ^ 2 ≤
      fderiv ℝ (fderiv ℝ (weightedPowerQuadratic g H M sigma r)) s d d := by
  rw [fderiv_fderiv_weightedPowerQuadratic_apply hM g hH sigma hr]
  have hp := hA.inner_nonneg_left d
  have hn : energyNorm M d ^ 2 = inner ℝ (M d) d := by
    simpa only [RCLike.re_to_real] using hM.isSymmetricCoercive.energyNorm_sq d
  have hterm : 0 ≤ sigma * (r - 2) * energyNorm M s ^ (r - 4) * (inner ℝ (M s) d) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hsigma (by linarith))
      (Real.rpow_nonneg (energyNorm_nonneg M s) _)) (sq_nonneg _)
  change 0 ≤ inner ℝ (H d + lambda • M d) d at hp
  simp only [inner_add_left, real_inner_smul_left] at hp
  rw [hn]
  nlinarith

/-- At the zero step the radial Hessian vanishes and the actual Hessian is the quadratic one. -/
@[simp] theorem fderiv_fderiv_weightedPowerQuadratic_zero_apply
    (hM : Krylov.IsPreconditioner M Minv) (g : E) {H : E →L[ℝ] E}
    (hH : H.IsSymmetric) (sigma : ℝ) {r : ℝ} (hr : 2 < r) (u v : E) :
    fderiv ℝ (fderiv ℝ (weightedPowerQuadratic g H M sigma r)) 0 u v = inner ℝ (H u) v := by
  rw [fderiv_fderiv_weightedPowerQuadratic_apply hM g hH sigma hr]
  simp [energyNorm, Real.zero_rpow (by linarith : r - 2 ≠ 0)]

end Optimization.QuadraticSubproblem
