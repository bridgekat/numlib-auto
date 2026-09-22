/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts`, beside
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The integral of a directional derivative of a compactly supported function vanishes

For `f : E → ℝ` differentiable with compact support and `∂_v f` integrable for an additive Haar
measure `μ`, `∫ ∂_v f dμ = 0` (`integral_fderiv_apply_eq_zero_of_hasCompactSupport`): Mathlib's
integration by parts `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` against the constant
`1`. Continuity of `fderiv ℝ f` is not needed, only its integrability, which is what the Leibniz
step of the divergence theorem on an epigraph has.
-/

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The integral of a derivative of a compactly supported function vanishes**: for `f : E → ℝ`
differentiable with compact support and `∂_v f` integrable, `∫ ∂_v f dμ = 0` for every additive
Haar measure `μ`. Mathlib's integration by parts
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` against the constant `1`. Continuity of
`fderiv ℝ f` is not needed, only its integrability — which is what the Leibniz step
`EuclideanSpace.integral_fderiv_castSucc_epigraph` has. -/
theorem integral_fderiv_apply_eq_zero_of_hasCompactSupport {f : E → ℝ} (hf : Differentiable ℝ f)
    (hfc : HasCompactSupport f) {v : E} (hf' : Integrable (fun x ↦ fderiv ℝ f x v) μ) :
    ∫ x, fderiv ℝ f x v ∂μ = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := fun _ ↦ (1 : ℝ))
    (g := f) (v := v) (by simp) (by simpa using hf')
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hfc)
    (fun x _ ↦ differentiableAt_const _) (fun x _ ↦ hf x)
  simpa using h

/-- The integral of a derivative of a compactly supported `C¹` function vanishes. -/
theorem integral_fderiv_apply_eq_zero_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (v : E) : ∫ x, fderiv ℝ f x v ∂μ = 0 :=
  integral_fderiv_apply_eq_zero_of_hasCompactSupport (hf.differentiable one_ne_zero) hfc
    (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.fderiv_apply ℝ hfc v))
