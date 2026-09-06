/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The Arzelà–Ascoli theorem in `C(X, Y)`

Mathlib proves the Arzelà–Ascoli theorem for the bounded continuous functions `X →ᵇ Y`
(`BoundedContinuousFunction.arzela_ascoli`). When `X` is compact the two spaces are isometric
(`ContinuousMap.isometryEquivBoundedOfCompact`), so the theorem transports to the space `C(X, Y)`
of *all* continuous maps with the uniform metric; that is the form in which the theorem is used,
because `C(X, ℝ)` is the Banach space the classical integral operators act on.

## Main statements

* `ContinuousMap.isCompact_closure_of_equicontinuous` — an equicontinuous family of continuous maps
  from a compact space whose values lie in one compact set is precompact in `C(X, Y)`.
* `ContinuousMap.isCompact_closure_of_forall_norm_le` — the same for maps into a proper normed
  space, with a uniform bound `‖f x‖ ≤ M` in place of the compact target set. This is the classical
  statement "uniformly bounded and equicontinuous implies precompact".

The domain is only assumed to be a compact topological space: no uniform structure on it is needed,
because equicontinuity is stated pointwise, and a pointwise-equicontinuous family on a compact
space is automatically uniformly equicontinuous.

## References

The theorem is classical; see [han2009theoretical], Theorem 1.6.3, and [kress1989linear], §1.3.
-/

open Metric Set

open scoped BoundedContinuousFunction

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]

/-- **The Arzelà–Ascoli theorem** in `C(X, Y)`, for `X` compact: an equicontinuous set of
continuous maps whose values all lie in a fixed compact set `s ⊆ Y` has compact closure for the
uniform metric.

This is `BoundedContinuousFunction.arzela_ascoli` transported along the isometry
`ContinuousMap.isometryEquivBoundedOfCompact`. -/
theorem isCompact_closure_of_equicontinuous {S : Set C(X, Y)} {s : Set Y} (hs : IsCompact s)
    (hmem : ∀ f ∈ S, ∀ x, f x ∈ s) (heqc : Equicontinuous ((↑) : S → X → Y)) :
    IsCompact (closure S) := by
  let e : C(X, Y) ≃ₜ (X →ᵇ Y) := (isometryEquivBoundedOfCompact X Y).toHomeomorph
  have hu : ∀ g : (e '' S : Set (X →ᵇ Y)), e.symm (g : X →ᵇ Y) ∈ S := by
    rintro ⟨g, f, hf, rfl⟩
    simpa using hf
  have key : IsCompact (closure (e '' S)) := by
    refine BoundedContinuousFunction.arzela_ascoli s hs _ ?_ ?_
    · rintro f x ⟨g, hg, rfl⟩
      exact hmem g hg x
    · exact heqc.comp fun g : (e '' S : Set (X →ᵇ Y)) => (⟨e.symm (g : X →ᵇ Y), hu g⟩ : S)
  have himg : e.symm '' closure (e '' S) = closure S := by
    rw [e.symm.image_closure, ← Set.image_comp]
    simp
  rw [← himg]
  exact key.image e.symm.continuous

/-- **The Arzelà–Ascoli theorem** in the form "uniformly bounded and equicontinuous implies
precompact": a set of continuous maps from a compact space into a proper normed space, bounded by
one constant `M` and equicontinuous, has compact closure in `C(X, E)`. -/
theorem isCompact_closure_of_forall_norm_le {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set C(X, E)} {M : ℝ} (hbdd : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ M)
    (heqc : Equicontinuous ((↑) : S → X → E)) : IsCompact (closure S) :=
  isCompact_closure_of_equicontinuous (isCompact_closedBall 0 M)
    (fun f hf x => mem_closedBall_zero_iff.2 (hbdd f hf x)) heqc

end ContinuousMap
