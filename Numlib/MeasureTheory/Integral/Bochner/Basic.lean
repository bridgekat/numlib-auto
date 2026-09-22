/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Integral.Bochner.Basic`, beside
`MemLp.eLpNorm_eq_integral_rpow_norm`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Bochner integral of a power of a norm as a lower Lebesgue integral

`∫ ‖f‖^P = (∫⁻ ‖f‖ₑ^P).toReal` for `0 ≤ P` and `f` almost everywhere strongly measurable
(`MeasureTheory.integral_norm_rpow_eq_toReal_lintegral`): the integrand is nonnegative, so the
Bochner integral is the `toReal` of the lower Lebesgue integral. It is how an `ℝ≥0∞`-valued
estimate (Hölder, a Poincaré inequality in `ℝ≥0∞` form) is read back as an inequality of Bochner
integrals.
-/

open scoped ENNReal

namespace MeasureTheory

/-- `∫ ‖f‖^P = (∫⁻ ‖f‖ₑ^P).toReal` for `0 ≤ P` and `f` almost everywhere strongly measurable. -/
theorem integral_norm_rpow_eq_toReal_lintegral {α G : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup G] {f : α → G} (hf : AEStronglyMeasurable f μ) {P : ℝ}
    (hP : 0 ≤ P) : ∫ x, ‖f x‖ ^ P ∂μ = (∫⁻ x, ‖f x‖ₑ ^ P ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x ↦ by positivity)
    (hf.norm.aemeasurable.pow_const P).aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP]

end MeasureTheory
