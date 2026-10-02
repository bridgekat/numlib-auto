/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Fintype.Card`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Fintype.EquivFin

/-!
# Functions with the same multiset of values

Two functions on a finite type have the same multiset of values exactly when they differ by a
permutation of the index type (`map_univ_val_eq_iff_exists_equiv`,
`exists_equiv_of_map_univ_val_eq`): the fibres of each value have the same cardinality, and a
bijection of fibres is a permutation (`Equiv.ofFiberEquiv`). This is how a spectrum or a list of
singular values given as a multiset is turned into a reindexing.
-/

/-- The number of indices at which `k` takes the value `c` is the multiplicity of `c` in the
multiset of values. -/
theorem Fintype.card_subtype_eq_count_map_univ_val {ι α : Type*} [Fintype ι] [DecidableEq α]
    (k : ι → α) (c : α) :
    Fintype.card {i // k i = c} = Multiset.count c (Multiset.map k Finset.univ.val) := by
  rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
  exact congrArg _ (Multiset.filter_congr fun _ _ => eq_comm)

/-- Two functions on a finite type with the same multiset of values differ by a permutation of the
index type: the fibres of each value have the same cardinality. -/
theorem exists_equiv_of_map_univ_val_eq {ι α : Type*} [Fintype ι]
    {f g : ι → α} (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ e : ι ≃ ι, ∀ i, f (e i) = g i := by
  classical
  have hcard : ∀ c, Fintype.card {i // g i = c} = Fintype.card {i // f i = c} := fun c => by
    have hc := congrArg (Multiset.count c) h
    rw [← Fintype.card_subtype_eq_count_map_univ_val,
      ← Fintype.card_subtype_eq_count_map_univ_val] at hc
    convert hc.symm
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c),
    Equiv.ofFiberEquiv_map _⟩

/-- Two functions on a finite type have the same multiset of values if and only if they differ by
a permutation of the index type. -/
theorem map_univ_val_eq_iff_exists_equiv {ι α : Type*} [Fintype ι] {f g : ι → α} :
    Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val ↔ ∃ e : ι ≃ ι, f ∘ e = g := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_equiv_of_map_univ_val_eq h
    exact ⟨e, funext he⟩
  · rintro ⟨e, rfl⟩
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
