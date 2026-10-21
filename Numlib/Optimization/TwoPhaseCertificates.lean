import Numlib.Optimization.TwoPhaseTargets

/-!
# Certificates from scalar-target stationarity

Positive homogeneity of the feasible derivative gap converts a genuine derivative test for
the squared target residual to a scaled Lagrangian test. At zero objective residual it gives
an infeasibility certificate, with a weak lower residual bound including the boundary.
-/

noncomputable section
namespace Optimization.TwoPhaseTargets
open FeasibleCriticality

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The equality Lagrangian with the multiplier subtracted from the objective. -/
def lagrangian (f : E → ℝ) (c : E → F) (y : F) (z : E) : ℝ :=
  f z - inner ℝ y (c z)

/-- The multiplier prescribed by a strictly positive objective-target gap. -/
def targetMultiplier (f : E → ℝ) (c : E → F) (t : ℝ) (x : E) : F :=
  (-(f x - t)⁻¹) • c x

/-- The scale is the Euclidean norm of the multiplier with last coordinate one. -/
def multiplierScale (y : F) : ℝ := Real.sqrt (‖y‖ ^ 2 + 1)

/-- The actual Lagrangian derivative uses the chosen sign convention. -/
theorem lagrangian_hasFDerivAt {f : E → ℝ} {c : E → F} {x : E}
    {f' : E →L[ℝ] ℝ} {c' : E →L[ℝ] F}
    (hf : HasFDerivAt f f' x) (hc : HasFDerivAt c c' x) (y : F) :
    HasFDerivAt (lagrangian f c y) (f' - (innerSL ℝ y).comp c') x :=
  hf.sub ((innerSL ℝ y).hasFDerivAt.comp x hc)

/-- Multiplying the actual Lagrangian derivative by the positive scalar gap gives exactly
 the actual squared-residual derivative, without any independent derivative oracle. -/
theorem fderiv_objective_eq_gap_smul {f : E → ℝ} {c : E → F} {t : ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (ha : f x - t ≠ 0) :
    fderiv ℝ (TargetLeastSquares.objective f c t) x =
      (f x - t) • fderiv ℝ (lagrangian f c (targetMultiplier f c t x)) x := by
  rw [(TargetLeastSquares.objective_hasFDerivAt hf.hasFDerivAt hc.hasFDerivAt t).fderiv,
    (lagrangian_hasFDerivAt hf.hasFDerivAt hc.hasFDerivAt _).fderiv]
  ext d
  simp only [add_apply, smul_apply,
    sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    targetMultiplier, inner_smul_left, smul_eq_mul, conj_trivial]
  field_simp
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The augmented multiplier scale is exactly augmented residual norm divided by the gap. -/
theorem multiplierScale_targetMultiplier {f : E → ℝ} {c : E → F} {t : ℝ} {x : E}
    (ha : 0 < f x - t) :
    multiplierScale (targetMultiplier f c t x) = residualNorm f c t x / (f x - t) := by
  have hy : ‖targetMultiplier f c t x‖ = ‖c x‖ / (f x - t) := by
    simp [targetMultiplier, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
      div_eq_mul_inv, mul_comm]
  have hs : multiplierScale (targetMultiplier f c t x) ^ 2 =
      ‖targetMultiplier f c t x‖ ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have hr := residualNorm_sq f c t x
  have hq : (residualNorm f c t x / (f x - t)) ^ 2 =
      (‖c x‖ / (f x - t)) ^ 2 + 1 := by
    rw [div_pow, hr]
    field_simp
  rw [hy] at hs
  have hn : 0 ≤ multiplierScale (targetMultiplier f c t x) := Real.sqrt_nonneg _
  have hqn := div_nonneg (residualNorm_nonneg f c t x) ha.le
  nlinarith

/-- Positive homogeneity transfers true squared-residual criticality to true Lagrangian
criticality, including the exact multiplier scale. -/
theorem scaled_lagrangian_criticality [FiniteDimensional ℝ E] {f : E → ℝ} {c : E → F} {C : Set E}
    {t epsilon1 : ℝ} {x : E} (hC : IsClosed C) (hx : x ∈ C)
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x)
    (ha : 0 < f x - t)
    (hw : feasibleCriticality C x (fderiv ℝ (TargetLeastSquares.objective f c t) x) ≤
      epsilon1 * residualNorm f c t x) :
    feasibleCriticality C x
      (fderiv ℝ (lagrangian f c (targetMultiplier f c t x)) x) ≤
      epsilon1 * multiplierScale (targetMultiplier f c t x) := by
  rw [fderiv_objective_eq_gap_smul hf hc ha.ne',
    feasibleCriticality_smul hC hx _ ha.le] at hw
  rw [multiplierScale_targetMultiplier ha]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ ha).mpr
  nlinarith [hw]

/-- At zero scalar gap, the actual target derivative equals that of constraint least squares. -/
theorem fderiv_objective_eq_constraint {f : E → ℝ} {c : E → F} {t : ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hc : DifferentiableAt ℝ c x) (ha : f x = t) :
    fderiv ℝ (TargetLeastSquares.objective f c t) x =
      fderiv ℝ (fun z => ‖c z‖ ^ 2 / 2) x := by
  have hh : HasFDerivAt (fun z => ‖c z‖ ^ 2 / 2) ((innerSL ℝ (c x)).comp
      (fderiv ℝ c x)) x := by
    convert hc.hasFDerivAt.norm_sq.const_mul (1 / 2) using 1
    · funext z; ring
    · ext d; simp
  rw [(TargetLeastSquares.objective_hasFDerivAt hf.hasFDerivAt hc.hasFDerivAt t).fderiv,
    hh.fderiv, ha, sub_self, zero_smul, add_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ F] in
/-- A vanishing scalar gap identifies the augmented norm with constraint infeasibility. -/
theorem residualNorm_of_gap_zero {f : E → ℝ} {c : E → F} {t : ℝ} {x : E}
    (ha : f x = t) : residualNorm f c t x = ‖c x‖ := by
  simp [residualNorm, ha]

end Optimization.TwoPhaseTargets
