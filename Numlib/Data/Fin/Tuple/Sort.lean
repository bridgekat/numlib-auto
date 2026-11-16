/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Data.Fintype.Card`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Fintype.EquivFin

/-!
# Functions with the same multiset of values

Let $\iota$ be a finite type. The multiset of values of a function $f \colon \iota \to \alpha$ is
$\operatorname{vals}(f) = \{\!\{ f(i) : i \in \iota \}\!\}$, the Lean term
`Multiset.map f Finset.univ.val`. This module proves that two functions
$f, g \colon \iota \to \alpha$ have the same multiset of values if and only if $f \circ e = g$ for a
permutation $e$ of $\iota$. This is how a spectrum or a list of singular values that is given as a
multiset is turned into a reindexing.

## Main results

* `Fintype.card_subtype_eq_count_map_univ_val`: the number of indices $i$ with $f(i) = c$ is the
  multiplicity of $c$ in $\operatorname{vals}(f)$.
* `exists_equiv_of_map_univ_val_eq`: if $\operatorname{vals}(f) = \operatorname{vals}(g)$, then
  $f \circ e = g$ for a permutation $e$ of $\iota$.
* `map_univ_val_eq_iff_exists_equiv`: $\operatorname{vals}(f) = \operatorname{vals}(g)$ if and only
  if $f \circ e = g$ for a permutation $e$ of $\iota$.

## Proof outline

The multiplicity of a value $c$ in $\operatorname{vals}(f)$ is the cardinality of the fibre
$f^{-1}(c)$. If $\operatorname{vals}(f) = \operatorname{vals}(g)$, the fibres of $f$ and $g$ over
each value have the same cardinality, and a family of bijections between the fibres is a permutation
of $\iota$ (`Equiv.ofFiberEquiv`).
-/

/-- Let $\iota$ be a finite type, let $k \colon \iota \to \alpha$, and let $c \in \alpha$. The
number of indices at which $k$ takes the value $c$ is the multiplicity of $c$ in the multiset of
values of $k$:
$$\#\{i \in \iota : k(i) = c\} = \operatorname{count}_c \{\!\{ k(i) : i \in \iota \}\!\}.$$
-/
theorem Fintype.card_subtype_eq_count_map_univ_val {ι α : Type*} [Fintype ι] [DecidableEq α]
    (k : ι → α) (c : α) :
    Fintype.card {i // k i = c} = Multiset.count c (Multiset.map k Finset.univ.val) := by
  rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
  exact congrArg _ (Multiset.filter_congr fun _ _ => eq_comm)

/-- Let $\iota$ be a finite type and let $f, g \colon \iota \to \alpha$. If $f$ and $g$ have the
same multiset of values, $\{\!\{ f(i) : i \in \iota \}\!\} = \{\!\{ g(i) : i \in \iota \}\!\}$,
then there is a permutation $e$ of $\iota$ with
$$f(e(i)) = g(i) \quad \text{for all } i \in \iota.$$

The multiset of values of $f$ is `Multiset.map f Finset.univ.val`. The fibres of $f$ and $g$
over each value have the same cardinality by `Fintype.card_subtype_eq_count_map_univ_val`, and
the proof glues bijections between them with `Equiv.ofFiberEquiv`. -/
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

/-- Let $\iota$ be a finite type and let $f, g \colon \iota \to \alpha$. Then $f$ and $g$ have the
same multiset of values, $\{\!\{ f(i) : i \in \iota \}\!\} = \{\!\{ g(i) : i \in \iota \}\!\}$,
if and only if there is a permutation $e$ of $\iota$ with
$$f \circ e = g.$$

The multiset of values of $f$ is `Multiset.map f Finset.univ.val`. -/
theorem map_univ_val_eq_iff_exists_equiv {ι α : Type*} [Fintype ι] {f g : ι → α} :
    Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val ↔ ∃ e : ι ≃ ι, f ∘ e = g := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_equiv_of_map_univ_val_eq h
    exact ⟨e, funext he⟩
  · rintro ⟨e, rfl⟩
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
