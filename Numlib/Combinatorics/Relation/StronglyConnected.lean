/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $r$ be a relation on a type $\alpha$. Two elements are **strongly connected** for $r$ when each
is reachable from the other by a finite chain of $r$-steps. This is an equivalence relation, and its
classes are the strongly connected components of the directed graph of $r$.

On a finite type there is a **topological ordering** of the strongly connected components: a rank
$b \colon \alpha \to \mathbb{N}$ that never decreases along $r$ and whose fibres are exactly the
components. If the elements are sorted by $b$, then the components appear in an order in which every
arrow points forward. This order puts a matrix into block triangular form with its strongly
connected components on the diagonal.

## Main definitions

* `Relation.StronglyConnected`: $i$ and $j$ are strongly connected for $r$.

## Main results

* `Relation.equivalence_stronglyConnected`: strong connectivity is an equivalence relation.
* `Relation.apply_le_of_reflTransGen`: a function that does not decrease along $r$ does not decrease
  along reachability.
* `Relation.exists_rank_stronglyConnected`: on a finite type, there is a rank
  $b \colon \alpha \to \mathbb{N}$ that does not decrease along $r$ and with $b(i) = b(j)$ if and
  only if $i$ and $j$ are strongly connected.

## Proof outline

The proof needs no linear extension theorem and no quotient. Two numbers are attached to each
element $i$. The first is the number $|L_i|$ of elements from which $i$ can be reached. It never
decreases along $r$, and it is constant on a component. If $i$ reaches $j$ and $|L_i| = |L_j|$, then
$L_i = L_j$, so $j$ reaches $i$ and the two are in the same component. The second number $q_i$
separates the components that the first number does not separate. It is the least index, under a
fixed enumeration of $\alpha$, of an element of the component of $i$. It is constant on a component,
distinct components have distinct values, and it is at most $|\alpha|$. The rank is the pair read as
one number in base $|\alpha| + 1$:
$$b(i) = q_i + (|\alpha| + 1) \, |L_i|.$$

## Implementation notes

* Reachability by a finite chain of $r$-steps is `Relation.ReflTransGen r`, so every element is
  reachable from itself.
* Mathlib's `Quiver.stronglyConnectedSetoid` in `Mathlib.Combinatorics.Quiver.ConnectedComponent` is
  the same equivalence relation for a quiver.
-/

namespace Relation

variable {α : Type*} {r : α → α → Prop}

/-- Let $r$ be a relation on $\alpha$. Two elements $i, j \in \alpha$ are **strongly connected** for
$r$ if $j$ is reachable from $i$ and $i$ is reachable from $j$ by finite chains of $r$-steps,
where a chain may be empty. The classes of this equivalence relation are the strongly connected
components of the directed graph of $r$. -/
def StronglyConnected (r : α → α → Prop) (i j : α) : Prop :=
  ReflTransGen r i j ∧ ReflTransGen r j i

/-- Every element is strongly connected to itself. -/
theorem StronglyConnected.refl (r : α → α → Prop) (i : α) : StronglyConnected r i i :=
  ⟨ReflTransGen.refl, ReflTransGen.refl⟩

/-- Strong connectivity is symmetric: if $i$ and $j$ are strongly connected, then $j$ and $i$ are
strongly connected. -/
theorem StronglyConnected.symm {i j : α} (h : StronglyConnected r i j) :
    StronglyConnected r j i := ⟨h.2, h.1⟩

/-- Strong connectivity is transitive: if $i, j$ and $j, k$ are strongly connected, then $i, k$ are
strongly connected. -/
theorem StronglyConnected.trans {i j k : α} (h : StronglyConnected r i j)
    (h' : StronglyConnected r j k) : StronglyConnected r i k :=
  ⟨h.1.trans h'.1, h'.2.trans h.2⟩

/-- Strong connectivity for $r$ is an equivalence relation. -/
theorem equivalence_stronglyConnected (r : α → α → Prop) : Equivalence (StronglyConnected r) :=
  ⟨StronglyConnected.refl r, StronglyConnected.symm, StronglyConnected.trans⟩

/-- Let $\beta$ be a preordered type and let $b \colon \alpha \to \beta$ satisfy $b(i) \le b(j)$
whenever $r(i, j)$. If $j$ is reachable from $i$ by a finite chain of $r$-steps, then
$b(i) \le b(j)$. -/
theorem apply_le_of_reflTransGen {β : Type*} [Preorder β] {b : α → β}
    (hb : ∀ i j, r i j → b i ≤ b j) {i j : α} (h : ReflTransGen r i j) : b i ≤ b j := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (hb _ _ hstep)

/-- A **topological ordering of the strongly connected components**. Let $\alpha$ be a finite type
and let $r$ be a relation on $\alpha$. Then there is a function $b \colon \alpha \to \mathbb{N}$
such that

* $b(i) \le b(j)$ whenever $r(i, j)$, and
* for all $i, j \in \alpha$, $b(i) = b(j)$ if and only if $i$ and $j$ are strongly connected for
  $r$. -/
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
      refine hqinj i j ?_
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hqlt i), Nat.mod_eq_of_lt (hqlt j)] using
        congrArg (· % (Fintype.card α + 1)) h
    · intro h
      rw [hqeq i j h, hLeq i j h]

end Relation
