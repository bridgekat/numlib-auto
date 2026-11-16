/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Exp`, beside `Real.tendsto_exp_atBot`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Products of factors $1 - b_i$ with divergent $\sum b_i$

Let $(b_i)_{i \ge 0}$ be real numbers with $b_i \le 1$. This file proves that if the partial sums
$\sum_{i < n} b_i$ tend to $+\infty$, then the partial products $\prod_{i < n} (1 - b_i)$ tend to
$0$. The proof uses the inequality $1 - x \le e^{-x}$. Together with the Weierstrass product
inequality `Finset.one_sub_sum_le_prod_one_sub`, this gives the dichotomy behind Müntz's theorem:
the products stay away from $0$ exactly when $\sum b_i$ converges.

## Main results

* `Real.tendsto_prod_one_sub_of_tendsto_sum`: if $b_i \le 1$ for all $i$ and
  $\sum_{i < n} b_i \to \infty$, then $\prod_{i < n} (1 - b_i) \to 0$.
-/

open Filter Topology

namespace Real

/-- Let $(b_i)_{i \ge 0}$ be a real sequence with $b_i \le 1$ for all $i$. If
$\sum_{i < n} b_i \to +\infty$ as $n \to \infty$, then
$$\prod_{i < n} (1 - b_i) \to 0 \qquad (n \to \infty).$$

The proof bounds the product between $0$ and $\exp\bigl(-\sum_{i < n} b_i\bigr)$, with the
inequality $1 - x \le e^{-x}$. -/
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
