/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$. If
$f : E \to \mathbb{R}$ is differentiable with compact support and the directional derivative
$\partial_v f$ is integrable, then $\int_E \partial_v f \, d\mu = 0$. This is Mathlib's integration
by parts `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` against the constant function $1$.

## Main results

* `integral_fderiv_apply_eq_zero_of_hasCompactSupport`: the statement for a differentiable $f$ with
  integrable $\partial_v f$.
* `integral_fderiv_apply_eq_zero_of_contDiff`: the statement for a $C^1$ function $f$.

## Implementation notes

* The first result needs only the integrability of $\partial_v f$, not the continuity of the
  derivative of $f$. The Leibniz step of the divergence theorem on an epigraph
  (`EuclideanSpace.integral_fderiv_castSucc_epigraph`) has only this integrability.
-/

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The integral of a directional derivative of a compactly supported function vanishes.** Let $E$
be a finite-dimensional real normed space with an additive Haar measure $\mu$, and let
$v \in E$. If $f : E \to \mathbb{R}$ is differentiable, has compact support, and
$x \mapsto Df(x)[v]$ is $\mu$-integrable, then
$$\int_E Df(x)[v] \, d\mu(x) = 0.$$

The proof is Mathlib's integration by parts
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` against the constant $1$. The continuity
of the derivative of $f$ is not needed, only the integrability of $Df(\cdot)[v]$. This is what
the Leibniz step `EuclideanSpace.integral_fderiv_castSucc_epigraph` has. -/
theorem integral_fderiv_apply_eq_zero_of_hasCompactSupport {f : E → ℝ} (hf : Differentiable ℝ f)
    (hfc : HasCompactSupport f) {v : E} (hf' : Integrable (fun x ↦ fderiv ℝ f x v) μ) :
    ∫ x, fderiv ℝ f x v ∂μ = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := fun _ ↦ (1 : ℝ))
    (g := f) (v := v) (by simp) (by simpa using hf')
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hfc)
    (fun x _ ↦ differentiableAt_const _) (fun x _ ↦ hf x)
  simpa using h

/-- Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$. If
$f : E \to \mathbb{R}$ is $C^1$ with compact support, then $\int_E Df(x)[v] \, d\mu(x) = 0$ for
every $v \in E$. -/
theorem integral_fderiv_apply_eq_zero_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (v : E) : ∫ x, fderiv ℝ f x v ∂μ = 0 :=
  integral_fderiv_apply_eq_zero_of_hasCompactSupport (hf.differentiable one_ne_zero) hfc
    (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.fderiv_apply ℝ hfc v))
