/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The Arzelà–Ascoli theorem in the space of continuous functions

Let $X$ be a compact topological space and let $Y$ be a metric space. The space $C(X, Y)$ of all
continuous maps $X \to Y$ carries the uniform metric. This file proves the Arzelà–Ascoli theorem in
$C(X, Y)$: an equicontinuous set of maps whose values lie in one compact set has compact closure.
For maps into a proper normed group, a uniform bound on the values replaces the compact set. The
theorem is classical; see Theorem 1.6.3 of [han2009theoretical] and §1.3 of [kress1989linear]. This
is the form in which the theorem is used, because $C(X, \mathbb{R})$ is the Banach space on which
the classical integral operators act.

## Main results

* `ContinuousMap.isCompact_closure_of_equicontinuous`: an equicontinuous set of continuous maps from
  a compact space whose values lie in one compact set has compact closure in $C(X, Y)$.
* `ContinuousMap.isCompact_closure_of_forall_norm_le`: an equicontinuous set of continuous maps from
  a compact space into a proper normed group, with a uniform bound $\|f(x)\| \le M$, has compact
  closure. This is the classical statement "uniformly bounded and equicontinuous implies
  precompact".

## Implementation notes

* Mathlib proves the theorem for the bounded continuous functions `X →ᵇ Y`
  (`BoundedContinuousFunction.arzela_ascoli`). For compact $X$, the isometry
  `ContinuousMap.isometryEquivBoundedOfCompact` identifies $C(X, Y)$ with this space, and the
  theorem transports along it.
* The domain is only a compact topological space, with no uniform structure. Equicontinuity is
  pointwise equicontinuity, and a pointwise equicontinuous family on a compact space is uniformly
  equicontinuous.
-/

open Metric Set

open scoped BoundedContinuousFunction

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]

/-- The **Arzelà–Ascoli theorem** in $C(X, Y)$. Let $X$ be a compact topological space, let $Y$ be a
metric space, and let $s \subseteq Y$ be compact. Let $S \subseteq C(X, Y)$ be equicontinuous,
with $f(x) \in s$ for all $f \in S$ and $x \in X$. Then the closure of $S$ in $C(X, Y)$, for the
uniform metric, is compact.

Equicontinuity is pointwise equicontinuity of the family of maps $X \to Y$ indexed by $S$. The
proof transports `BoundedContinuousFunction.arzela_ascoli` along the isometry
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

/-- The **Arzelà–Ascoli theorem**, in the form "uniformly bounded and equicontinuous implies
precompact". Let $X$ be a compact topological space, let $E$ be a normed additive group in which
closed bounded sets are compact (a proper space), and let $M \in \mathbb{R}$. Let
$S \subseteq C(X, E)$ be equicontinuous, with $\|f(x)\| \le M$ for all $f \in S$ and $x \in X$.
Then the closure of $S$ in $C(X, E)$ is compact.

The proof applies `ContinuousMap.isCompact_closure_of_equicontinuous` with the closed ball of
radius $M$ as the compact set. -/
theorem isCompact_closure_of_forall_norm_le {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set C(X, E)} {M : ℝ} (hbdd : ∀ f ∈ S, ∀ x, ‖f x‖ ≤ M)
    (heqc : Equicontinuous ((↑) : S → X → E)) : IsCompact (closure S) :=
  isCompact_closure_of_equicontinuous (isCompact_closedBall 0 M)
    (fun f hf x => mem_closedBall_zero_iff.2 (hbdd f hf x)) heqc

end ContinuousMap
