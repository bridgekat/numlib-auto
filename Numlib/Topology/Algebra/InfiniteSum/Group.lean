/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.Algebra.InfiniteSum.Group`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Splitting off a finite set of terms from an infinite sum

Let $f : \beta \to \alpha$ be a summable family in a Hausdorff topological additive commutative
group $\alpha$, and let $s \subseteq \beta$ be finite. This file proves that the sum of $f$ is the
finite sum over $s$ plus the sum of the family that agrees with $f$ off $s$ and is $0$ on $s$.
Mathlib's `Summable.tsum_eq_add_tsum_ite` splits off one term $f(b)$ in this form, and
`Summable.sum_add_tsum_compl` splits off a finite set with the rest written as a sum over the
complement of $s$ as a subtype.

## Main results

* `Summable.tsum_eq_sum_add_tsum_ite`: $\sum_b f(b) = \sum_{b \in s} f(b) + \sum_b g(b)$, where
  $g(b) = 0$ for $b \in s$ and $g(b) = f(b)$ otherwise.
-/

variable {α β : Type*} [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α]
  [T2Space α] [DecidableEq β]

/-- Let $\alpha$ be a Hausdorff topological additive commutative group, let $f : \beta \to \alpha$
be summable, and let $s \subseteq \beta$ be a finite set. Then
$$\sum_{b} f(b) = \sum_{b \in s} f(b) + \sum_{b} g(b), \qquad g(b) = \begin{cases} 0, & b \in s,
  \\ f(b), & b \notin s. \end{cases}$$

This is the finite-set version of `Summable.tsum_eq_add_tsum_ite`, which splits off one term.
The family $g$ is written `if b ∈ s then 0 else f b`. -/
theorem Summable.tsum_eq_sum_add_tsum_ite {f : β → α} (hf : Summable f) (s : Finset β) :
    ∑' b, f b = ∑ b ∈ s, f b + ∑' b, (if b ∈ s then 0 else f b) := by
  rw [← hf.sum_add_tsum_compl (s := s), tsum_subtype]
  congr 1
  refine tsum_congr fun b => ?_
  by_cases hb : b ∈ s <;> simp [hb]
