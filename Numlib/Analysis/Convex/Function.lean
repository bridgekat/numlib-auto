/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Convex.Function`, beside `ConvexOn.add`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Function

/-!
# Finite sums of convex functions

`ConvexOn.sum`: a finite sum of functions convex on `s` is convex on `s`, the `Finset` form of
Mathlib's `ConvexOn.add`.
-/

/-- **A finite sum of convex functions is convex.** -/
theorem ConvexOn.sum {𝕜 E β ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β]
    {s : Set E} {t : Finset ι} {f : ι → E → β} (hs : Convex 𝕜 s)
    (hf : ∀ i ∈ t, ConvexOn 𝕜 s (f i)) : ConvexOn 𝕜 s fun x => ∑ i ∈ t, f i x := by
  have h : ConvexOn 𝕜 s (∑ i ∈ t, f i) :=
    Finset.sum_induction f (ConvexOn 𝕜 s) (fun _ _ => ConvexOn.add) (convexOn_const 0 hs) hf
  convert h using 1
  funext x
  simp [Finset.sum_apply]
