/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-!
# Brezis, Section 2.1: The Baire category theorem

This module formalizes Section 2.1 of [brezis2011functional] for a complete metric space $X$. The
Baire category theorem (Theorem 2.1) states that a countable union of closed sets with empty
interior has empty interior. Remark 1 gives the form in which the theorem is used: if countably many
closed sets cover a nonempty complete metric space, then one of them has nonempty interior.

Both statements restate Mathlib's `dense_iInter_of_isOpen_nat` and
`nonempty_interior_of_iUnion_of_closed`, for $X$ a Baire space by
`BaireSpace.of_completelyPseudoMetrizable`.

## Main results

* Theorem 2.1, `Brezis.Chapter02.theorem_2_1`: if $(X_n)$ are closed with
  $\operatorname{Int} X_n = \emptyset$, then $\operatorname{Int}(\bigcup_n X_n) = \emptyset$
  (Baire).
* Remark 1, `Brezis.Chapter02.remark_2_1`: if $X \neq \emptyset$ and $\bigcup_n X_n = X$ with $X_n$
  closed, then some $X_{n_0}$ has nonempty interior.
-/

namespace Brezis.Chapter02

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- **Theorem 2.1** of [brezis2011functional] (Baire). Let $X$ be a complete metric space and let
$(X_n)_{n \ge 1}$ be a sequence of closed subsets of $X$ with
$\operatorname{Int} X_n = \emptyset$ for every $n$. Then
$$\operatorname{Int}\Big(\bigcup_{n=1}^\infty X_n\Big) = \emptyset.$$

The sequence is indexed by `ℕ`, starting at $0$. -/
theorem theorem_2_1 (S : ℕ → Set X) (hc : ∀ n, IsClosed (S n)) (hi : ∀ n, interior (S n) = ∅) :
    interior (⋃ n, S n) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, Set.compl_iUnion]
  exact dense_iInter_of_isOpen_nat (fun n => (hc n).isOpen_compl) fun n =>
    interior_eq_empty_iff_dense_compl.1 (hi n)

/-- **Remark 1** of [brezis2011functional]. Let $X$ be a nonempty complete metric space and let
$(X_n)_{n \ge 1}$ be a sequence of closed subsets of $X$ with $\bigcup_{n=1}^\infty X_n = X$.
Then there is $n_0$ with $\operatorname{Int} X_{n_0} \neq \emptyset$.

This is the form in which the Baire category theorem is used. -/
theorem remark_2_1 [Nonempty X] (S : ℕ → Set X) (hc : ∀ n, IsClosed (S n))
    (hU : ⋃ n, S n = Set.univ) : ∃ n, (interior (S n)).Nonempty :=
  nonempty_interior_of_iUnion_of_closed hc hU

end Brezis.Chapter02
