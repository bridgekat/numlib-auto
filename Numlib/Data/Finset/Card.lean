/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Finset.Card`, beside `Finset.card_equiv`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Fintype.Card

/-!
# Counting along an equivalence

Counting the elements of a finite type that satisfy a predicate does not change when the type is
relabelled by an equivalence: `#{a | p (e a)} = #{b | p b}` (`Finset.card_filter_comp_equiv`). This
is how counts of eigenvalues indexed in two different ways (by the index type of a matrix and by
`Fin n` in sorted order) are identified.

A finite set `t` of naturals misses some `k ≤ #t` (`Finset.exists_le_card_notMem`), which bounds
the least natural number outside it.
-/

namespace Finset

/-- Counting the values of `p ∘ e` for an equivalence `e` is counting the values of `p`. -/
theorem card_filter_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (p : β → Prop)
    [DecidablePred p] : #{a | p (e a)} = #{b | p b} :=
  card_equiv e fun _ => by simp

/-- A smaller strict initial segment has fewer elements. -/
theorem card_filter_lt_lt_of_lt {n : Type*} [Fintype n] [LinearOrder n] {a b : n} (h : a < b) :
    #{k | k < a} < #{k | k < b} := by
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset (fun k hk => ?_) |>.2 ⟨a, ?_, ?_⟩)
  · simp only [mem_filter, mem_univ, true_and] at hk ⊢
    exact hk.trans h
  · simp [h]
  · simp

/-- Below the cardinality of a finite set of naturals there is a number the set misses: the
`k + 1` numbers `0, …, k` do not all fit in a set of `k` elements. -/
theorem exists_le_card_notMem (t : Finset ℕ) : ∃ k ≤ #t, k ∉ t := by
  by_contra! h
  have hsub : range (#t + 1) ⊆ t := fun k hk => h k (by simpa [Nat.lt_succ_iff] using hk)
  have := card_le_card hsub
  rw [card_range] at this
  omega

end Finset
