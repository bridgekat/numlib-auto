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
# `L^p` for a finite sum of measures

Mathlib treats the sum of two measures (`MemLp.left_of_add_measure`,
`AEStronglyMeasurable.add_measure`); these are the `Finset` forms, which the boundary measure of
a polygon — a sum of arclength measures, one per boundary edge — needs:

* `MeasureTheory.aestronglyMeasurable_finsetSum_measure`;
* `MeasureTheory.memLp_finsetSum_measure`;
* `MeasureTheory.eLpNorm_finsetSum_measure_of_ae_eq_zero`: the seminorm of a function that
  vanishes almost everywhere for all but one summand is the seminorm for that summand.
-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {ι : Type*} {s : Finset ι} {μ : ι → Measure α}
  {p : ℝ≥0∞} {f : α → ℝ}

/-- A function strongly measurable for each of finitely many measures is strongly measurable for
their sum. -/
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

/-- A function in `L^p` of each of finitely many measures is in `L^p` of their sum,
`0 < p < ∞`. -/
theorem memLp_finsetSum_measure (hp0 : p ≠ 0) (hp : p ≠ ⊤) (h : ∀ i ∈ s, MemLp f p (μ i)) :
    MemLp f p (∑ i ∈ s, μ i) := by
  have hm : AEStronglyMeasurable f (∑ i ∈ s, μ i) :=
    MeasureTheory.aestronglyMeasurable_finsetSum_measure
      fun i hi ↦ (h i hi).aestronglyMeasurable
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hm, lintegral_finsetSum_measure]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ENNReal.sum_lt_top.2 fun i hi ↦ ?_).ne
  exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp (h i hi).eLpNorm_lt_top

/-- The `L^p` seminorm for a finite sum of measures of a function vanishing almost everywhere
for all but one of them is the seminorm for that one, `0 < p < ∞`. -/
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
