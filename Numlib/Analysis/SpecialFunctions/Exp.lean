/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Exp`, beside `Real.tendsto_exp_atBot`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A product of factors `1 - bᵢ` with divergent `∑ bᵢ` tends to `0`

`Real.tendsto_prod_one_sub_of_tendsto_sum`: if `bᵢ ≤ 1` and `∑ bᵢ → ∞`, then
`∏_{i < n} (1 - bᵢ) → 0`, by `1 - x ≤ e^{-x}`. With the Weierstrass product inequality
`Finset.one_sub_sum_le_prod_one_sub` it is the dichotomy behind Müntz's theorem: the products
stay away from `0` exactly when `∑ bᵢ` converges.
-/

open Filter Topology

namespace Real

/-- If `∑ bᵢ` diverges and `bᵢ ≤ 1`, then `∏_{i < n} (1 - bᵢ) → 0`, by `1 - x ≤ exp (-x)`. -/
theorem tendsto_prod_one_sub_of_tendsto_sum {b : ℕ → ℝ} (hb1 : ∀ i, b i ≤ 1)
    (hdiv : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, b i) atTop atTop) :
    Tendsto (fun n ↦ ∏ i ∈ Finset.range n, (1 - b i)) atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ Finset.prod_nonneg fun i _ ↦ by linarith [hb1 i])
    (g := fun n ↦ Real.exp (-∑ i ∈ Finset.range n, b i)) (fun n ↦ ?_) ?_
  · calc ∏ i ∈ Finset.range n, (1 - b i) ≤ ∏ i ∈ Finset.range n, Real.exp (-b i) :=
          Finset.prod_le_prod₀ (fun i _ ↦ by linarith [hb1 i])
            (fun i _ ↦ by linarith [Real.add_one_le_exp (-b i)])
      _ = Real.exp (-∑ i ∈ Finset.range n, b i) := by
          rw [← Real.exp_sum, Finset.sum_neg_distrib]
  · exact Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.2 hdiv)

end Real
