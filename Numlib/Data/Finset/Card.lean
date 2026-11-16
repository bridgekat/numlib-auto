/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Finset.Card`, beside `Finset.card_equiv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Fintype.Card

/-!
# Counting along an equivalence

Let $e \colon \alpha \to \beta$ be a bijection between finite types, and let $p$ be a predicate on
$\beta$. Counting the elements that satisfy $p$ does not change when the type is relabelled by $e$:
$\#\{a \in \alpha : p(e(a))\} = \#\{b \in \beta : p(b)\}$. This is how counts of eigenvalues indexed
in two different ways are identified: by the index type of a matrix, and by `Fin n` in sorted order.

Two further counting facts are proved. In a finite linear order, an element $a < b$ has fewer
elements below it than $b$. A finite set $t \subseteq \mathbb{N}$ misses some $k \le \#t$, which
bounds the least natural number outside $t$.

## Main results

* `Finset.card_filter_comp_equiv`: $\#\{a : p(e(a))\} = \#\{b : p(b)\}$ for a bijection $e$.
* `Finset.card_filter_lt_lt_of_lt`: if $a < b$, then $\#\{k : k < a\} < \#\{k : k < b\}$.
* `Finset.exists_le_card_notMem`: a finite set $t \subseteq \mathbb{N}$ misses some $k \le \#t$.
-/

namespace Finset

/-- Let $\alpha$ and $\beta$ be finite types, let $e \colon \alpha \to \beta$ be a bijection, and
let $p$ be a predicate on $\beta$. Then
$$\#\{a \in \alpha : p(e(a))\} = \#\{b \in \beta : p(b)\}.$$
-/
theorem card_filter_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (p : β → Prop)
    [DecidablePred p] : #{a | p (e a)} = #{b | p b} :=
  card_equiv e fun _ => by simp

/-- Let $n$ be a finite linearly ordered type and let $a < b$ in $n$. Then fewer elements of $n$ lie
below $a$ than below $b$:
$$\#\{k \in n : k < a\} < \#\{k \in n : k < b\}.$$
-/
theorem card_filter_lt_lt_of_lt {n : Type*} [Fintype n] [LinearOrder n] {a b : n} (h : a < b) :
    #{k | k < a} < #{k | k < b} := by
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset (fun k hk => ?_) |>.2 ⟨a, ?_, ?_⟩)
  · simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact hk.trans h
  · simp [h]
  · simp

/-- Every finite set $t \subseteq \mathbb{N}$ misses some natural number $k \le \#t$. The reason is
that the $\#t + 1$ numbers $0, 1, \dots, \#t$ cannot all lie in $t$. -/
theorem exists_le_card_notMem (t : Finset ℕ) : ∃ k ≤ #t, k ∉ t := by
  by_contra! h
  have hsub : range (#t + 1) ⊆ t := fun k hk => h k (by simpa [Nat.lt_succ_iff] using hk)
  have := card_le_card hsub
  rw [card_range] at this
  omega

end Finset
