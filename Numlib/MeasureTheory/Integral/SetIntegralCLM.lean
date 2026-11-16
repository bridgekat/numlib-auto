/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`, beside
`MeasureTheory.L1.integralCLM`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The integral over a set as a bounded linear functional on $L^1$

Let $\mu$ be a measure on $\alpha$, let $F$ be a normed space over $\mathbb{R}$ and over a field
$\mathbb{K}$ that is $\mathbb{R}$ or $\mathbb{C}$, and let $A \subseteq \alpha$. This file defines
the map $u \mapsto \int_A u \, d\mu$ as a continuous $\mathbb{K}$-linear map $L^1(\mu; F) \to F$ of
norm at most $1$. It is the analogue of Mathlib's `MeasureTheory.L1.integralCLM` for the integral
over $A$, and it does not pass through the restricted measure. It makes an $L^1$-valued Bochner
integral commute with the integral over a set, in `Numlib.Analysis.Convolution.Bochner`.

## Main definitions

* `MeasureTheory.L1.setIntegralCLM`: the map $u \mapsto \int_A u \, d\mu$ as a continuous linear map
  on $L^1(\mu; F)$.
-/

open Filter
open scoped ENNReal

namespace MeasureTheory

/-! ### The integral over a set as a functional on $L^1$ -/

section SetIntegralCLM

variable {α F 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜) in
/-- Let $\mu$ be a measure on $\alpha$, let $F$ be a normed space over $\mathbb{R}$ and over
$\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$ with compatible scalar actions, and let
$A \subseteq \alpha$. The **integral over $A$** is the continuous $\mathbb{K}$-linear map
$$L^1(\mu; F) \to F, \qquad u \mapsto \int_A u \, d\mu,$$
with operator norm at most $1$.

The set $A$ need not be measurable. The bound on the norm is $\|\int_A u \, d\mu\| \le \int
\|u\| \, d\mu = \|u\|_{L^1}$. -/
noncomputable def L1.setIntegralCLM (A : Set α) : (α →₁[μ] F) →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x in A, u x ∂μ
      map_add' := fun u v => by
        rw [← MeasureTheory.integral_add (L1.integrable_coeFn u).integrableOn
          (L1.integrable_coeFn v).integrableOn]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add u v))
      map_smul' := fun c u => by
        rw [RingHom.id_apply, ← MeasureTheory.integral_smul]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c u)) }
    1 fun u => by
      rw [one_mul, L1.norm_eq_integral_norm]
      refine (norm_integral_le_integral_norm _).trans ?_
      exact setIntegral_le_integral (L1.integrable_coeFn u).norm
        (Eventually.of_forall fun x => norm_nonneg _)

/-- The value of `MeasureTheory.L1.setIntegralCLM` at $u \in L^1(\mu; F)$ is $\int_A u \, d\mu$. -/
theorem L1.setIntegralCLM_apply (A : Set α) (u : α →₁[μ] F) :
    L1.setIntegralCLM 𝕜 A u = ∫ x in A, u x ∂μ := rfl

end SetIntegralCLM

end MeasureTheory
