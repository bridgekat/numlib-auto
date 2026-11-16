/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $f$ be an almost everywhere strongly measurable function with values in a normed group, and let
$P \ge 0$. The integrand $\|f\|^P$ is nonnegative, so its Bochner integral is the real part of its
lower Lebesgue integral:
$$\int \|f\|^P \, d\mu = \Big(\int^- \|f\|^P \, d\mu\Big)_{\mathbb{R}}.$$
This identity reads an estimate in $[0, \infty]$, such as Hölder's inequality or a Poincaré
inequality in that form, as an inequality between Bochner integrals.

## Main results

* `MeasureTheory.integral_norm_rpow_eq_toReal_lintegral`: the identity above.

## Implementation notes

* The real part of $a \in [0, \infty]$ is `ENNReal.toReal a`, which is $0$ for $a = \infty$. When
  the lower integral is infinite, both sides are $0$.
-/

open scoped ENNReal

namespace MeasureTheory

/-- Let $\mu$ be a measure, let $G$ be a normed group, let $f \colon \alpha \to G$ be almost
everywhere strongly measurable, and let $P \ge 0$ be real. Then
$$\int \|f(x)\|^P \, d\mu(x) = \Big(\int^- \|f(x)\|^P \, d\mu(x)\Big)_{\mathbb{R}},$$
where the right side is the lower Lebesgue integral converted to a real number.

The conversion is `ENNReal.toReal`, which sends $\infty$ to $0$. The integrand on the right is
the `ℝ≥0∞`-valued norm `‖f x‖ₑ ^ P`. -/
theorem integral_norm_rpow_eq_toReal_lintegral {α G : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup G] {f : α → G} (hf : AEStronglyMeasurable f μ) {P : ℝ}
    (hP : 0 ≤ P) : ∫ x, ‖f x‖ ^ P ∂μ = (∫⁻ x, ‖f x‖ₑ ^ P ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x ↦ by positivity)
    (hf.norm.aemeasurable.pow_const P).aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun x ↦ ?_
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP]

end MeasureTheory
