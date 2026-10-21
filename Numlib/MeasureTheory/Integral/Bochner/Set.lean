/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Integral.Bochner.Set`, beside
`MeasureTheory.integral_biUnion_finset`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrals over disjoint pieces of a set

`MeasureTheory.sum_setIntegral_le_setIntegral_of_pairwiseDisjoint`: for a nonnegative `F`
integrable on `J`, the integrals of `F` over finitely many pairwise disjoint measurable subsets of
`J` add up to at most its integral over `J`.
-/

open Filter Set

namespace MeasureTheory

/-- A finite sum of integrals of a nonnegative function over pairwise disjoint measurable subsets
of `J` is at most the integral over `J`. -/
theorem sum_setIntegral_le_setIntegral_of_pairwiseDisjoint {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} (S : Finset ι) {I : ι → Set X} {J : Set X} {F : X → ℝ}
    (hI : ∀ e ∈ S, MeasurableSet (I e)) (hIJ : ∀ e ∈ S, I e ⊆ J)
    (hdisj : (S : Set ι).PairwiseDisjoint I) (hF : IntegrableOn F J μ) (hF0 : ∀ x, 0 ≤ F x) :
    ∑ e ∈ S, ∫ x in I e, F x ∂μ ≤ ∫ x in J, F x ∂μ := by
  rw [← integral_biUnion_finset S hI hdisj fun e he ↦ hF.mono_set (hIJ e he)]
  exact setIntegral_mono_set hF (Eventually.of_forall hF0)
    (LE.le.eventuallySubset (iUnion₂_subset hIJ))

end MeasureTheory
