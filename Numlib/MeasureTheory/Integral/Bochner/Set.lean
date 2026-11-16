/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $F$ be a nonnegative real function that is integrable on a set $J$. If $I_e$, for $e$ in a
finite set $S$, are pairwise disjoint measurable subsets of $J$, then the integrals of $F$ over the
sets $I_e$ add up to at most its integral over $J$.

## Main results

* `MeasureTheory.sum_setIntegral_le_setIntegral_of_pairwiseDisjoint`: $\sum_{e \in S} \int_{I_e} F
  \, d\mu \le \int_J F \, d\mu$.
-/

open Filter Set

namespace MeasureTheory

/-- Let $\mu$ be a measure on $X$, let $S$ be a finite index set, let $J \subseteq X$, and let
$(I_e)_{e \in S}$ be pairwise disjoint measurable subsets of $J$. If $F \colon X \to \mathbb{R}$
is integrable on $J$ and $F(x) \ge 0$ for every $x \in X$, then
$$\sum_{e \in S} \int_{I_e} F \, d\mu \le \int_J F \, d\mu.$$
-/
theorem sum_setIntegral_le_setIntegral_of_pairwiseDisjoint {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} (S : Finset ι) {I : ι → Set X} {J : Set X} {F : X → ℝ}
    (hI : ∀ e ∈ S, MeasurableSet (I e)) (hIJ : ∀ e ∈ S, I e ⊆ J)
    (hdisj : (S : Set ι).PairwiseDisjoint I) (hF : IntegrableOn F J μ) (hF0 : ∀ x, 0 ≤ F x) :
    ∑ e ∈ S, ∫ x in I e, F x ∂μ ≤ ∫ x in J, F x ∂μ := by
  rw [← integral_biUnion_finset S hI hdisj fun e he ↦ hF.mono_set (hIJ e he)]
  exact setIntegral_mono_set hF (Eventually.of_forall hF0)
    (LE.le.eventuallySubset (iUnion₂_subset hIJ))

end MeasureTheory
