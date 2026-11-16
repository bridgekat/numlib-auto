/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Convex.Function`, beside `ConvexOn.add`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Convex.Function

/-!
# Finite sums of convex functions

A finite sum of functions that are convex on a convex set $s$ is convex on $s$. This is the `Finset`
form of Mathlib's `ConvexOn.add`.

## Main results

* `ConvexOn.sum`: if $s$ is convex and each $f_i$, $i \in t$, is convex on $s$, then
  $\sum_{i \in t} f_i$ is convex on $s$.
-/

/-- **A finite sum of convex functions is convex.** Let $\Bbbk$ be an ordered semiring, let $E$ be
an additive commutative monoid with a scalar multiplication by $\Bbbk$, and let $\beta$ be an
ordered additive commutative monoid that is a $\Bbbk$-module. Let $s \subseteq E$ be convex, let
$t$ be a finite index set, and let $f_i \colon E \to \beta$ be convex on $s$ for every
$i \in t$. Then the function
$$x \mapsto \sum_{i \in t} f_i(x)$$
is convex on $s$.

The convexity of $s$ is needed for the empty sum: the zero function is convex on $s$ only when
$s$ is convex. -/
theorem ConvexOn.sum {𝕜 E β ι : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E]
    [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β]
    {s : Set E} {t : Finset ι} {f : ι → E → β} (hs : Convex 𝕜 s)
    (hf : ∀ i ∈ t, ConvexOn 𝕜 s (f i)) : ConvexOn 𝕜 s fun x => ∑ i ∈ t, f i x := by
  have h : ConvexOn 𝕜 s (∑ i ∈ t, f i) :=
    Finset.sum_induction f (ConvexOn 𝕜 s) (fun _ _ => ConvexOn.add) (convexOn_const 0 hs) hf
  convert h using 1
  funext x
  simp [Finset.sum_apply]
