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
# The integral over a set as a bounded linear functional on `L¹`

`MeasureTheory.L1.setIntegralCLM 𝕜 A : (α →₁[μ] F) →L[𝕜] F` is `u ↦ ∫ x in A, u x ∂μ`, of norm
at most `1`: the restriction of Mathlib's `MeasureTheory.L1.integralCLM` to a measurable set
without passing through the restricted measure. It is what makes an `L¹`-valued Bochner integral
commute with integration over a set (`Numlib/Analysis/Convolution/Bochner.lean`).
-/

open Filter
open scoped ENNReal

namespace MeasureTheory

/-! ### The integral over a set as a functional on `L¹` -/

section SetIntegralCLM

variable {α F 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜) in
/-- **The integral over a set as a bounded linear functional on `L¹`**, `u ↦ ∫ x in A, u x ∂μ`, of
norm at most `1`. -/
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

theorem L1.setIntegralCLM_apply (A : Set α) (u : α →₁[μ] F) :
    L1.setIntegralCLM 𝕜 A u = ∫ x in A, u x ∂μ := rfl

end SetIntegralCLM

end MeasureTheory
