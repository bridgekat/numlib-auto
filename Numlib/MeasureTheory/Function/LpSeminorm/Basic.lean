/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Function.LpSeminorm.Basic`, beside
`MemLp.left_of_add_measure`; the measurability lemma beside
`AEStronglyMeasurable.add_measure`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# $L^p$ for a finite sum of measures

Let $(\mu_i)_{i \in s}$ be finitely many measures on a measurable space. This file proves that a
function that is almost everywhere strongly measurable, or in $L^p$, for each $\mu_i$ has the same
property for the sum $\sum_{i \in s} \mu_i$. It also computes the $L^p$ seminorm for the sum when
the function vanishes almost everywhere for all summands but one. Mathlib has these facts for the
sum of two measures (`MeasureTheory.MemLp.left_of_add_measure`,
`MeasureTheory.AEStronglyMeasurable.add_measure`). The finite sums are needed for the boundary
measure of a polygon, which is the sum of the arclength measures of its edges.

## Main results

* `MeasureTheory.aestronglyMeasurable_finsetSum_measure`: a function that is almost everywhere
  strongly measurable for each $\mu_i$ is almost everywhere strongly measurable for $\sum_i \mu_i$.
* `MeasureTheory.memLp_finsetSum_measure`: for $0 < p < \infty$, a function in $L^p(\mu_i)$ for each
  $i$ is in $L^p(\sum_i \mu_i)$.
* `MeasureTheory.eLpNorm_finsetSum_measure_of_ae_eq_zero`: for $0 < p < \infty$, if $f = 0$ almost
  everywhere for every $\mu_i$ with $i \neq e$, then
  $\|f\|_{L^p(\sum_i \mu_i)} = \|f\|_{L^p(\mu_e)}$.
-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {ι : Type*} {s : Finset ι} {μ : ι → Measure α}
  {p : ℝ≥0∞} {f : α → ℝ}

/-- Let $(\mu_i)_{i \in s}$ be a finite family of measures on a measurable space $\alpha$, and let
$\beta$ be a pseudometrizable topological space. If $f \colon \alpha \to \beta$ is almost
everywhere strongly measurable for each $\mu_i$, then $f$ is almost everywhere strongly
measurable for $\sum_{i \in s} \mu_i$. -/
theorem aestronglyMeasurable_finsetSum_measure {β : Type*} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] {f : α → β} {s : Finset ι} {μ : ι → Measure α}
    (h : ∀ i ∈ s, AEStronglyMeasurable f (μ i)) : AEStronglyMeasurable f (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add_measure
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Let $(\mu_i)_{i \in s}$ be a finite family of measures on a measurable space $\alpha$, and let
$0 < p < \infty$. If $f \colon \alpha \to \mathbb{R}$ is in $L^p(\mu_i)$ for each $i \in s$,
then $f$ is in $L^p(\sum_{i \in s} \mu_i)$. -/
theorem memLp_finsetSum_measure (hp0 : p ≠ 0) (hp : p ≠ ⊤) (h : ∀ i ∈ s, MemLp f p (μ i)) :
    MemLp f p (∑ i ∈ s, μ i) := by
  have hm : AEStronglyMeasurable f (∑ i ∈ s, μ i) :=
    MeasureTheory.aestronglyMeasurable_finsetSum_measure
      fun i hi ↦ (h i hi).aestronglyMeasurable
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hm, lintegral_finsetSum_measure]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ENNReal.sum_lt_top.2 fun i hi ↦ ?_).ne
  exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp (h i hi).eLpNorm_lt_top

/-- Let $(\mu_i)_{i \in s}$ be a finite family of measures on a measurable space $\alpha$, let
$0 < p < \infty$, let $e \in s$, and let $f \colon \alpha \to \mathbb{R}$ be almost everywhere
strongly measurable for $\mu_e$. If $f = 0$ $\mu_i$-almost everywhere for every $i \in s$ with
$i \neq e$, then
$$\|f\|_{L^p(\sum_{i \in s} \mu_i)} = \|f\|_{L^p(\mu_e)}.$$

The seminorms are the `ℝ≥0∞`-valued seminorms `MeasureTheory.eLpNorm`. -/
theorem eLpNorm_finsetSum_measure_of_ae_eq_zero (hp0 : p ≠ 0) (hp : p ≠ ⊤) {e : ι} (he : e ∈ s)
    (hm : AEStronglyMeasurable f (μ e)) (h : ∀ i ∈ s, i ≠ e → f =ᵐ[μ i] 0) :
    eLpNorm f p (∑ i ∈ s, μ i) = eLpNorm f p (μ e) := by
  have hm' : AEStronglyMeasurable f (∑ i ∈ s, μ i) :=
    MeasureTheory.aestronglyMeasurable_finsetSum_measure fun i hi ↦ by
      by_cases hie : i = e
      · exact hie ▸ hm
      · exact (aestronglyMeasurable_const (b := (0 : ℝ))).congr (h i hi hie).symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hm',
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hm, lintegral_finsetSum_measure,
    Finset.sum_eq_single_of_mem e he]
  intro i hi hie
  rw [lintegral_congr_ae ((h i hi hie).mono fun x hx ↦ ?_), lintegral_zero]
  rw [hx, Pi.zero_apply, enorm_zero, ENNReal.zero_rpow_of_pos]
  exact ENNReal.toReal_pos hp0 hp

end MeasureTheory
