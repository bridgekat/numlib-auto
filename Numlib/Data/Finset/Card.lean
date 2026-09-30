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
-/

namespace Finset

/-- Counting the values of `p ∘ e` for an equivalence `e` is counting the values of `p`. -/
theorem card_filter_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (p : β → Prop)
    [DecidablePred p] : #{a | p (e a)} = #{b | p b} :=
  card_equiv e fun _ => by simp

end Finset
