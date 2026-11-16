/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions` (the `L^∞` membership)
and `Mathlib.MeasureTheory.Measure.OpenPos` (the almost-everywhere bound on an open set).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Functions continuous on the closure of a set

This file proves facts about functions that are continuous on the closure $\bar s$ of a set $s$.
Such functions are the coefficients and the data of boundary value problems on a bounded open set
$\Omega$, where they are continuous on $\bar \Omega$. A function continuous on $\bar s$ is
essentially bounded on $s$ when $\bar s$ is compact, in particular when $s$ is a bounded set in a
proper metric space. For a measure that is positive on nonempty open sets and an open set $s$,
properties that hold almost everywhere on $s$ pass to every point by continuity: a bound $|g| \le C$
almost everywhere on $s$ holds on $\bar s$, two functions that are equal almost everywhere on $s$
are equal on $\bar s$, and two functions that are ordered almost everywhere on $s$ are ordered on
$s$.

## Main results

* `ContinuousOn.memLp_top_restrict_of_isCompact_closure`: a function continuous on $\bar s$, with
  $\bar s$ compact and $s$ measurable, is in $L^\infty(s)$.
* `ContinuousOn.memLp_top_restrict_of_isBounded`: a function continuous on $\bar s$, with $s$
  bounded and measurable in a proper space, is in $L^\infty(s)$.
* `ContinuousOn.abs_le_on_closure_of_ae_abs_le`: a bound $|g| \le C$ almost everywhere on an open
  set $s$ holds everywhere on $\bar s$.
* `ContinuousOn.eqOn_closure_of_ae_eq`: two functions continuous on $\bar s$ and equal almost
  everywhere on an open set $s$ are equal on $\bar s$.
* `le_on_of_ae_le`: two functions continuous on an open set $s$ with $g \le h$ almost everywhere on
  $s$ satisfy $g \le h$ on $s$.

## Implementation notes

* Membership in $L^\infty(s)$ is `MemLp f ⊤ (μ.restrict s)`, and "almost everywhere on $s$" is
  "almost everywhere for `μ.restrict s`".
* "Positive on nonempty open sets" is `MeasureTheory.Measure.IsOpenPosMeasure`.
-/

open MeasureTheory Set
open scoped ENNReal

variable {X F : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X}

section MemLpTop

variable [NormedAddCommGroup F] [SecondCountableTopologyEither X F] {f : X → F} {s : Set X}

/-- Let $X$ be a topological space in which open sets are measurable, let $\mu$ be a measure on $X$,
and let $F$ be a normed group, with $X$ or $F$ second countable. Let $s \subseteq X$ be a
measurable set whose closure $\bar s$ is compact, and let $f \colon X \to F$ be continuous on
$\bar s$. Then $f$ is essentially bounded on $s$, that is, $f \in L^\infty(s, \mu)$.

In Lean, the conclusion is `MemLp f ⊤ (μ.restrict s)`. -/
theorem ContinuousOn.memLp_top_restrict_of_isCompact_closure (hs : IsCompact (closure s))
    (hsm : MeasurableSet s) (hf : ContinuousOn f (closure s)) : MemLp f ⊤ (μ.restrict s) := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf
  refine memLp_top_of_bound ((hf.mono subset_closure).aestronglyMeasurable hsm) C ?_
  filter_upwards [ae_restrict_mem hsm] with x hx
  exact hC x (subset_closure hx)

/-- Let $X$ be a proper pseudometric space in which open sets are measurable, let $\mu$ be a measure
on $X$, and let $F$ be a normed group, with $X$ or $F$ second countable. Let $s \subseteq X$ be
a bounded measurable set, and let $f \colon X \to F$ be continuous on $\bar s$. Then
$f \in L^\infty(s, \mu)$.

In Lean, the conclusion is `MemLp f ⊤ (μ.restrict s)`. The proof is
`ContinuousOn.memLp_top_restrict_of_isCompact_closure`, since a bounded set in a proper space
has compact closure. -/
theorem ContinuousOn.memLp_top_restrict_of_isBounded {X : Type*} [PseudoMetricSpace X]
    [ProperSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {f : X → F}
    [SecondCountableTopologyEither X F] {s : Set X} (hs : Bornology.IsBounded s)
    (hsm : MeasurableSet s) (hf : ContinuousOn f (closure s)) : MemLp f ⊤ (μ.restrict s) :=
  hf.memLp_top_restrict_of_isCompact_closure hs.isCompact_closure hsm

end MemLpTop

omit [OpensMeasurableSpace X] in
/-- Let $X$ be a topological space with a measure $\mu$ that is positive on nonempty open sets, let
$s \subseteq X$ be open, and let $g \colon X \to \mathbb{R}$ be continuous on $\bar s$. If
$C \in \mathbb{R}$ and $|g(x)| \le C$ for $\mu$-almost every $x \in s$, then $|g(x)| \le C$ for
every $x \in \bar s$. -/
theorem ContinuousOn.abs_le_on_closure_of_ae_abs_le [μ.IsOpenPosMeasure] {s : Set X}
    (hs : IsOpen s) {g : X → ℝ} (hg : ContinuousOn g (closure s)) {C : ℝ}
    (hb : ∀ᵐ x ∂(μ.restrict s), |g x| ≤ C) : ∀ x ∈ closure s, |g x| ≤ C := by
  have hc : ContinuousOn (fun x ↦ max (|g x| - C) 0) (closure s) :=
    ContinuousOn.sup ((continuous_abs.comp_continuousOn hg).sub continuousOn_const)
      continuousOn_const
  have h1 : EqOn (fun x ↦ max (|g x| - C) 0) (fun _ ↦ (0 : ℝ)) s := by
    refine Measure.eqOn_open_of_ae_eq (μ := μ) ?_ hs (hc.mono subset_closure) continuousOn_const
    filter_upwards [hb] with x hx
    simp [max_eq_right (sub_nonpos.2 hx)]
  intro x hx
  have h2 := h1.of_subset_closure hc continuousOn_const subset_closure le_rfl hx
  exact sub_nonpos.1 (max_eq_right_iff.1 h2)

omit [OpensMeasurableSpace X] in
/-- Let $X$ be a topological space with a measure $\mu$ that is positive on nonempty open sets, let
$Y$ be a Hausdorff topological space, and let $s \subseteq X$ be open. If $f, g \colon X \to Y$
are continuous on $\bar s$ and $f = g$ $\mu$-almost everywhere on $s$, then $f = g$ on $\bar s$.

The two functions agree on $s$ by `MeasureTheory.Measure.eqOn_open_of_ae_eq`, and hence on
$\bar s$ by continuity. The result gives the uniqueness, up to the boundary, of the continuous
representative of an element of $L^p(s)$. -/
theorem ContinuousOn.eqOn_closure_of_ae_eq [μ.IsOpenPosMeasure] {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] {s : Set X} (hs : IsOpen s) {f g : X → Y} (hf : ContinuousOn f (closure s))
    (hg : ContinuousOn g (closure s)) (h : f =ᵐ[μ.restrict s] g) : EqOn f g (closure s) :=
  (Measure.eqOn_open_of_ae_eq h hs (hf.mono subset_closure)
    (hg.mono subset_closure)).of_subset_closure hf hg subset_closure subset_rfl

omit [OpensMeasurableSpace X] in
/-- Let $X$ be a topological space with a measure $\mu$ that is positive on nonempty open sets, and
let $s \subseteq X$ be open. If $g, h \colon X \to \mathbb{R}$ are continuous on $s$ and
$g \le h$ $\mu$-almost everywhere on $s$, then $g(x) \le h(x)$ for every $x \in s$. -/
theorem le_on_of_ae_le [μ.IsOpenPosMeasure] {s : Set X} (hs : IsOpen s) {g h : X → ℝ}
    (hle : g ≤ᵐ[μ.restrict s] h) (hg : ContinuousOn g s) (hh : ContinuousOn h s) :
    ∀ x ∈ s, g x ≤ h x := by
  have hmin : (fun x ↦ min (g x) (h x)) =ᵐ[μ.restrict s] g := hle.mono fun x hx ↦ min_eq_left hx
  have heq := Measure.eqOn_open_of_ae_eq hmin hs (ContinuousOn.inf hg hh) hg
  intro x hx
  exact min_eq_left_iff.1 (heq hx)
