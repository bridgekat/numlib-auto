import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-!
# Brezis §2.1: the Baire category theorem

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §2.1, over a complete metric space `X` (a `BaireSpace`
by Mathlib's `BaireSpace.of_completelyPseudoMetrizable`). Both statements are Mathlib's
(`dense_iInter_of_isOpen_nat`, `nonempty_interior_of_iUnion_of_closed`), restated in the book's
two forms.

## Main results

* `theorem_2_1` — Baire: a countable union of closed sets with empty interior has empty interior.
* `remark_2_1` — the form in which it is used: if a countable family of closed sets covers a
  nonempty complete metric space, one of them has nonempty interior.
-/

namespace Brezis.Chapter02

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- **Theorem 2.1 (Baire).** Let `X` be a complete metric space and `(Xₙ)` a sequence of closed
subsets with `Int Xₙ = ∅` for every `n`. Then `Int (⋃ n, Xₙ) = ∅`. -/
theorem theorem_2_1 (S : ℕ → Set X) (hc : ∀ n, IsClosed (S n)) (hi : ∀ n, interior (S n) = ∅) :
    interior (⋃ n, S n) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl, Set.compl_iUnion]
  exact dense_iInter_of_isOpen_nat (fun n => (hc n).isOpen_compl) fun n =>
    interior_eq_empty_iff_dense_compl.1 (hi n)

/-- **Remark 1.** The form in which the Baire category theorem is used: if `X` is a nonempty
complete metric space and `(Xₙ)` a sequence of closed subsets with `⋃ n, Xₙ = X`, then
`Int Xₙ₀ ≠ ∅` for some `n₀`. -/
theorem remark_2_1 [Nonempty X] (S : ℕ → Set X) (hc : ∀ n, IsClosed (S n))
    (hU : ⋃ n, S n = Set.univ) : ∃ n, (interior (S n)).Nonempty :=
  nonempty_interior_of_iUnion_of_closed hc hU

end Brezis.Chapter02
