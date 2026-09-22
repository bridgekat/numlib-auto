/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Integral.IntegrableOn`, beside `IntegrableOn.of_bound`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability from a bound and a support condition

A function bounded on a measurable set `s`, strongly measurable there, and vanishing on `s`
outside a set `K` of finite measure is integrable on `s`
(`integrableOn_of_forall_norm_le_of_eq_zero`): the bound gives integrability on `s ∩ K` and the
rest of `s` carries the zero function. This is the shape in which a compactly supported field of
class `C¹(Ω̄)` is integrable on an unbounded `Ω`.
-/

open MeasureTheory Set

/-- A function bounded on a measurable set `s`, strongly measurable there, and vanishing on `s`
outside a set `K` of finite measure is integrable on `s`. -/
theorem integrableOn_of_forall_norm_le_of_eq_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {G : Type*} [NormedAddCommGroup G] {φ : X → G} {s K : Set X}
    (hs : MeasurableSet s) (hK : μ K ≠ ⊤) (hφ : AEStronglyMeasurable φ (μ.restrict s)) {M : ℝ}
    (hM : ∀ y ∈ s, ‖φ y‖ ≤ M) (h0 : ∀ y ∈ s, y ∉ K → φ y = 0) : IntegrableOn φ s μ := by
  have h1 : IntegrableOn φ (s ∩ K) μ := by
    refine IntegrableOn.of_bound ((measure_mono inter_subset_right).trans_lt hK.lt_top)
      (hφ.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) M ?_
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left (ae_restrict_of_forall_mem hs hM)
  exact h1.of_forall_sdiff_eq_zero hs fun y hy ↦ h0 y hy.1 fun hK' ↦ hy.2 ⟨hy.1, hK'⟩
