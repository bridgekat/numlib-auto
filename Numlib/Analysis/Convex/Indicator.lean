/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Epigraph

/-!
# Indicator functions

The indicator function $\delta(\cdot \mid s)$ of a set $s \subseteq E$ takes the value $0$ on $s$
and $+\infty$ off $s$. With it, every statement about convex sets becomes an instance of a statement
about convex functions, and the library uses it in this way throughout. The presentation follows
[rockafellar1970convex], §4.

## Main definitions

* `ConvexAnalysis.indicatorFn`: the indicator function $\delta(\cdot \mid s)$ of a set $s$.

## Main results

* `ConvexAnalysis.convexFn_indicatorFn`: $\delta(\cdot \mid s)$ is convex if and only if $s$ is
  convex.
* `ConvexAnalysis.convexDom_indicatorFn`: the effective domain of $\delta(\cdot \mid s)$ is $s$.
* `ConvexAnalysis.properConvex_indicatorFn`: $\delta(\cdot \mid s)$ is proper if and only if $s$ is
  nonempty.
* `ConvexAnalysis.indicatorFn_add`, `ConvexAnalysis.indicatorFn_finsetSum`: a sum of indicator
  functions is the indicator function of the intersection of the sets.
* `ConvexAnalysis.epi_indicatorFn`: the epigraph of $\delta(\cdot \mid s)$ is
  $s \times [0, \infty)$.
-/

open Set Pointwise

namespace ConvexAnalysis

section Basic

variable {E : Type*}

/-- The **indicator function** $\delta(\cdot \mid s) : E \to [-\infty, +\infty]$ of a set
$s \subseteq E$ is $\delta(x \mid s) = 0$ for $x \in s$ and $\delta(x \mid s) = +\infty$ for
$x \notin s$.

It is `ConvexAnalysis.convexRestrict s` applied to the constant function $0$. -/
noncomputable def indicatorFn (s : Set E) : E → EReal := convexRestrict s (fun _ => 0)

/-- For $x \in s$, $\delta(x \mid s) = 0$. -/
@[simp] theorem indicatorFn_of_mem {s : Set E} {x : E} (hx : x ∈ s) : indicatorFn s x = 0 :=
  convexRestrict_of_mem hx

/-- For $x \notin s$, $\delta(x \mid s) = +\infty$. -/
@[simp] theorem indicatorFn_of_notMem {s : Set E} {x : E} (hx : x ∉ s) : indicatorFn s x = ⊤ :=
  convexRestrict_of_notMem hx

/-- An indicator function never takes the value $-\infty$. -/
theorem indicatorFn_ne_bot (s : Set E) (x : E) : indicatorFn s x ≠ ⊥ := by
  by_cases hx : x ∈ s <;> simp [hx]

/-- The effective domain $\{x \mid \delta(x \mid s) < +\infty\}$ of the indicator function of a set
$s$ is $s$. -/
@[simp] theorem convexDom_indicatorFn (s : Set E) : convexDom (indicatorFn s) = s := by
  ext x; by_cases hx : x ∈ s <;> simp [hx]

/-- The indicator function $\delta(\cdot \mid s)$ is proper if and only if $s$ is nonempty.

For example, in a constrained problem $h + \delta(\cdot \mid C)$, the constraint term is proper
whenever $C$ is nonempty, also when $C$ is not closed. -/
@[simp] theorem properConvex_indicatorFn {s : Set E} : ProperConvex (indicatorFn s) ↔ s.Nonempty :=
  ⟨fun h => by simpa using h.convexDom_nonempty,
    fun h => ⟨by simpa using h, indicatorFn_ne_bot s⟩⟩

/-- **Adding indicator functions intersects the sets.** For sets $s, t \subseteq E$,
$$\delta(\cdot \mid s) + \delta(\cdot \mid t) = \delta(\cdot \mid s \cap t).$$

There is no side condition, because $0 + 0 = 0$ and $+\infty$ absorbs both values that an
indicator function can take. For this reason the intersection forms of results about convex sets
are the indicator instances of results about sums of convex functions. -/
@[simp] theorem indicatorFn_add (s t : Set E) :
    indicatorFn s + indicatorFn t = indicatorFn (s ∩ t) := by
  funext x
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;>
    simp [Pi.add_apply, hs, ht]

/-- Let $C_i \subseteq E$ be sets indexed by $i \in \iota$, and let $s$ be a finite subset of
$\iota$. Then
$$\sum_{i \in s} \delta(\cdot \mid C_i) = \delta\Big(\cdot \Bigm| \bigcap_{i \in s} C_i\Big),$$
with no side condition.

This is the finite form of `ConvexAnalysis.indicatorFn_add`. For $s = \emptyset$ both sides are
the zero function, since the empty intersection is all of $E$. -/
theorem indicatorFn_finsetSum {ι : Type*} (C : ι → Set E) (s : Finset ι) :
    ∑ i ∈ s, indicatorFn (C i) = indicatorFn (⋂ i ∈ s, C i) := by
  induction s using Finset.cons_induction with
  | empty => funext z; simp
  | cons i t hi ih =>
    rw [Finset.sum_cons, ih, indicatorFn_add]
    congr 1
    ext z
    simp [Finset.mem_cons]

/-- The epigraph of an indicator function is a half-cylinder with cross-section $s$:
$$\operatorname{epi} \delta(\cdot \mid s) = s \times [0, \infty) \subseteq E \times
  \mathbb{R}.$$
-/
theorem epi_indicatorFn (s : Set E) : epi (indicatorFn s) = s ×ˢ Ici (0 : ℝ) := by
  ext p
  by_cases hp : p.1 ∈ s <;> simp [epi, hp, EReal.coe_nonneg]

end Basic

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Let $E$ be a real vector space. The indicator function $\delta(\cdot \mid s)$ of a set
$s \subseteq E$ is a convex function if and only if $s$ is a convex set. -/
@[simp] theorem convexFn_indicatorFn {s : Set E} : ConvexFn (indicatorFn s) ↔ Convex ℝ s := by
  constructor
  · intro h
    simpa using h.convex_convexDom
  · intro h
    refine ⟨?_⟩
    rw [epi_indicatorFn]
    exact h.prod (convex_Ici 0)

omit [Module ℝ E] in
/-- **Translating the set translates the indicator function.** For $a, x \in E$ and $s \subseteq E$,
$\delta(x \mid a + s) = \delta(x - a \mid s)$. -/
@[simp] theorem indicatorFn_vadd (a : E) (s : Set E) (x : E) :
    indicatorFn (a +ᵥ s) x = indicatorFn s (x - a) := by
  have hmem : x ∈ a +ᵥ s ↔ x - a ∈ s := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
  by_cases hx : x - a ∈ s
  · rw [indicatorFn_of_mem (hmem.2 hx), indicatorFn_of_mem hx]
  · rw [indicatorFn_of_notMem fun h => hx (hmem.1 h), indicatorFn_of_notMem hx]

omit [AddCommGroup E] [Module ℝ E] in
/-- Let $f : E \to [-\infty, +\infty]$ never take the value $-\infty$. Then the restriction of $f$
to $s$, extended by $+\infty$ off $s$, is $f + \delta(\cdot \mid s)$.

The restriction is `ConvexAnalysis.convexRestrict s f`. The hypothesis on $f$ is needed because
$-\infty + \infty = -\infty$ in `EReal`. -/
theorem convexRestrict_eq_add_indicatorFn {s : Set E} {f : E → EReal} (hf : ∀ x, f x ≠ ⊥) :
    convexRestrict s f = f + indicatorFn s := by
  funext x
  by_cases hx : x ∈ s
  · simp [hx]
  · simp only [convexRestrict_of_notMem hx, Pi.add_apply, indicatorFn_of_notMem hx]
    exact (EReal.add_top_of_ne_bot (hf x)).symm

end Module

end ConvexAnalysis
