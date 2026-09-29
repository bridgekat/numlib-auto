/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Fin.Tuple.Sort`, beside `Tuple.sort`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.EquivFin

/-!
# Functions with the same multiset of values

Two functions on a finite type with the same multiset of values, in a linear order, differ by a
permutation of the index type (`exists_equiv_of_map_univ_val_eq`): sort both with `Tuple.sort`.
This is how a spectrum or a list of singular values given as a multiset is turned into a
reindexing.
-/

/-- Two functions on a finite type with the same multiset of values, in a linear order, differ
by a permutation of the index type: sort both. -/
theorem exists_equiv_of_map_univ_val_eq {ι α : Type*} [Fintype ι] [LinearOrder α]
    {f g : ι → α} (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ e : ι ≃ ι, ∀ i, f (e i) = g i := by
  classical
  set e₀ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he₀
  have hperm : List.Perm (List.ofFn (f ∘ e₀)) (List.ofFn (g ∘ e₀)) := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map, ← Multiset.map_map,
      ← Multiset.map_map, Multiset.map_univ_val_equiv, h]
  set σf := Tuple.sort (f ∘ e₀) with hσf
  set σg := Tuple.sort (g ∘ e₀) with hσg
  have hsorted : List.ofFn (f ∘ e₀ ∘ σf) = List.ofFn (g ∘ e₀ ∘ σg) := by
    refine List.Perm.eq_of_sortedLE (Tuple.monotone_sort (f ∘ e₀)).sortedLE_ofFn
      (Tuple.monotone_sort (g ∘ e₀)).sortedLE_ofFn ?_
    exact ((σf.ofFn_comp_perm (f ∘ e₀)).trans hperm).trans (σg.ofFn_comp_perm (g ∘ e₀)).symm
  have hfun : f ∘ e₀ ∘ σf = g ∘ e₀ ∘ σg := List.ofFn_injective hsorted
  refine ⟨(e₀.symm.trans σg.symm).trans (σf.trans e₀), fun i => ?_⟩
  have := congrFun hfun (σg.symm (e₀.symm i))
  simpa using this
