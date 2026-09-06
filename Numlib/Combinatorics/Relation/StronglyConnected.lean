/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: beside `Mathlib.Combinatorics.Quiver.ConnectedComponent`, whose
`Quiver.stronglyConnectedSetoid` is the same equivalence for a quiver.
Keep it free of dependencies on the rest of `Numlib`.
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Relation
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring

/-!
# Strongly connected components of a relation on a finite type

Two elements are *strongly connected* for a relation `r` when each is reachable from the other by a
finite chain of `r`-steps, that is, when `Relation.ReflTransGen r` holds both ways. This is an
equivalence relation, and its classes are the strongly connected components of the digraph of `r`.

The result of the file is `Relation.exists_rank_stronglyConnected`: on a finite type there is a
**topological ordering** of the strongly connected components, that is, a rank `b : α → ℕ` which
never decreases along `r` and whose fibres are *exactly* the components. Sorting the type by `b`
lists the components in an order in which every arrow points forward, which is what puts a matrix
into block triangular form with its strongly connected components on the diagonal.

## Implementation notes

No linear-extension theorem and no quotient are needed. Two numbers are attached to a vertex `i`:

* the number of vertices from which `i` can be reached, `(L i).card`. It never decreases along `r`,
  it is constant on a component, and — the point — when `i` reaches `j` and the two counts agree,
  the two predecessor sets agree, so `j` reaches `i` and the two are in the same component;
* a tag `q i` separating the components that the count fails to separate: the least index, under an
  arbitrary enumeration of the type, of a vertex in the component of `i`. It is constant on a
  component, distinct components get distinct tags, and it is bounded by the cardinality of the
  type.

The rank is that pair read as a single number in base `card α + 1`, namely
`q i + (card α + 1) * (L i).card`.
-/

namespace Relation

variable {α : Type*} {r : α → α → Prop}

/-- Two elements are **strongly connected** for a relation `r` when each is reachable from the other
by a finite chain of `r`-steps. The classes of this equivalence relation are the strongly connected
components of the digraph of `r`. -/
def StronglyConnected (r : α → α → Prop) (i j : α) : Prop :=
  ReflTransGen r i j ∧ ReflTransGen r j i

/-- Every element is strongly connected to itself. -/
theorem StronglyConnected.refl (r : α → α → Prop) (i : α) : StronglyConnected r i i :=
  ⟨ReflTransGen.refl, ReflTransGen.refl⟩

/-- Strong connectivity is symmetric. -/
theorem StronglyConnected.symm {i j : α} (h : StronglyConnected r i j) :
    StronglyConnected r j i := ⟨h.2, h.1⟩

/-- Strong connectivity is transitive. -/
theorem StronglyConnected.trans {i j k : α} (h : StronglyConnected r i j)
    (h' : StronglyConnected r j k) : StronglyConnected r i k :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- Strong connectivity is an equivalence relation. -/
theorem equivalence_stronglyConnected (r : α → α → Prop) : Equivalence (StronglyConnected r) :=
  ⟨StronglyConnected.refl r, StronglyConnected.symm, StronglyConnected.trans⟩

/-- A single `r`-step is strong connectivity in one direction only, so a function that does not
decrease along `r` does not decrease along reachability either. -/
theorem apply_le_of_reflTransGen {β : Type*} [Preorder β] {b : α → β}
    (hb : ∀ i j, r i j → b i ≤ b j) {i j : α} (h : ReflTransGen r i j) : b i ≤ b j := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (hb _ _ hstep)

/-- Reading a pair `(a, p)` with `p < K` as the number `p + K * a` loses nothing. -/
private theorem eq_of_add_mul_eq {K a p a' p' : ℕ} (hp : p < K) (hp' : p' < K)
    (h : p + K * a = p' + K * a') : a = a' ∧ p = p' := by
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le _) hp
  have ha : a = a' := by
    have h1 : (p + K * a) / K = a := by
      rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hp, zero_add]
    have h2 : (p' + K * a') / K = a' := by
      rw [Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt hp', zero_add]
    rw [← h1, ← h2, h]
  subst ha
  exact ⟨rfl, Nat.add_right_cancel h⟩

/-- **A topological ordering of the strongly connected components** of a relation on a finite type:
a rank `b : α → ℕ` that never decreases along `r` and whose fibres are exactly the strongly
connected components. -/
theorem exists_rank_stronglyConnected [Finite α] (r : α → α → Prop) :
    ∃ b : α → ℕ, (∀ i j, r i j → b i ≤ b j) ∧ ∀ i j, b i = b j ↔ StronglyConnected r i j := by
  classical
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨e⟩ : Nonempty (α ≃ Fin (Fintype.card α)) := ⟨Fintype.equivFin α⟩
  obtain ⟨L, hLdef⟩ : ∃ L : α → Finset α,
      ∀ i, L i = Finset.univ.filter fun k => ReflTransGen r k i := ⟨_, fun _ => rfl⟩
  have hLmem : ∀ i k, k ∈ L i ↔ ReflTransGen r k i := by
    intro i k; rw [hLdef]; simp
  have hLsub : ∀ i j, ReflTransGen r i j → L i ⊆ L j := fun i j hij k hk =>
    (hLmem _ _).2 (((hLmem _ _).1 hk).trans hij)
  have hLeq : ∀ i j, StronglyConnected r i j → L i = L j := fun i j h =>
    Finset.Subset.antisymm (hLsub _ _ h.1) (hLsub _ _ h.2)
  have hLcard : ∀ i j, ReflTransGen r i j → (L i).card ≤ (L j).card := fun i j h =>
    Finset.card_le_card (hLsub _ _ h)
  have hLtight : ∀ i j, ReflTransGen r i j → (L j).card ≤ (L i).card →
      StronglyConnected r i j := by
    intro i j hij hcard
    have hLij : L i = L j := Finset.eq_of_subset_of_card_le (hLsub _ _ hij) hcard
    have hj : j ∈ L j := (hLmem j j).2 ReflTransGen.refl
    rw [← hLij] at hj
    exact ⟨hij, (hLmem i j).1 hj⟩
  obtain ⟨q, hqdef⟩ : ∃ q : α → ℕ,
      ∀ i, q i = sInf {k | ∃ x, StronglyConnected r i x ∧ (e x : ℕ) = k} := ⟨_, fun _ => rfl⟩
  have hqmem : ∀ i, ∃ x, StronglyConnected r i x ∧ (e x : ℕ) = q i := by
    intro i
    have hne : {k | ∃ x, StronglyConnected r i x ∧ (e x : ℕ) = k}.Nonempty :=
      ⟨(e i : ℕ), i, StronglyConnected.refl r i, rfl⟩
    rw [hqdef]
    exact Nat.sInf_mem hne
  have hqlt : ∀ i, q i < Fintype.card α + 1 := by
    intro i
    obtain ⟨x, -, hx⟩ := hqmem i
    rw [← hx]
    exact Nat.lt_succ_of_lt (e x).isLt
  have hqeq : ∀ i j, StronglyConnected r i j → q i = q j := by
    intro i j h
    rw [hqdef, hqdef]
    congr 1
    ext k
    exact ⟨fun ⟨x, hx, hk⟩ => ⟨x, h.symm.trans hx, hk⟩, fun ⟨x, hx, hk⟩ => ⟨x, h.trans hx, hk⟩⟩
  have hqinj : ∀ i j, q i = q j → StronglyConnected r i j := by
    intro i j h
    obtain ⟨x, hx, hxe⟩ := hqmem i
    obtain ⟨y, hy, hye⟩ := hqmem j
    have hxy : x = y := e.injective (Fin.val_injective (by rw [hxe, h, ← hye]))
    rw [← hxy] at hy
    exact hx.trans hy.symm
  refine ⟨fun i => q i + (Fintype.card α + 1) * (L i).card, fun i j hr => ?_, fun i j => ?_⟩
  · change q i + (Fintype.card α + 1) * (L i).card ≤ q j + (Fintype.card α + 1) * (L j).card
    have hij : ReflTransGen r i j := ReflTransGen.single hr
    rcases lt_or_eq_of_le (hLcard i j hij) with hlt | heq
    · have h1 : q i + (Fintype.card α + 1) * (L i).card
          < (Fintype.card α + 1) * ((L i).card + 1) := by
        have hmul : (Fintype.card α + 1) * ((L i).card + 1)
            = (Fintype.card α + 1) * (L i).card + (Fintype.card α + 1) := by ring
        have := hqlt i
        omega
      have h2 : (Fintype.card α + 1) * ((L i).card + 1) ≤ (Fintype.card α + 1) * (L j).card :=
        Nat.mul_le_mul_left _ hlt
      omega
    · have hsc := hLtight i j hij (le_of_eq heq.symm)
      exact le_of_eq (by rw [hqeq i j hsc, heq])
  · change q i + (Fintype.card α + 1) * (L i).card = q j + (Fintype.card α + 1) * (L j).card ↔ _
    constructor
    · intro h
      exact hqinj i j (eq_of_add_mul_eq (hqlt i) (hqlt j) h).2
    · intro h
      rw [hqeq i j h, hLeq i j h]

end Relation
