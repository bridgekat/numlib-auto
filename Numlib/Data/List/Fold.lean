/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: core's `Init.Data.List.Lemmas` / `Init.Data.List.Monadic` and
`Mathlib.Data.List.Basic`, `Mathlib.Algebra.BigOperators.Group.List.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Forall2

/-!
# Loops as folds

An algorithm written as a program is a loop over an index list $l = [x_0, \dots, x_{n-1}]$. A step
function $f$ turns the state $s_i$ into the state $s_{i+1} = f(s_i, x_i)$, starting from $s_0 = b$,
and the loop returns $s_n$. In Lean the loop is `List.foldlM f b l` for a monad, and in exact
arithmetic (the identity monad `Id`) it is the fold `List.foldl f b l` (core's `List.idRun_foldlM`).
This module collects the general facts about such folds that the proofs about algorithms need. List
indices start at $0$.

The facts fall into four groups. Loop invariants: if an invariant holds at $s_0$ and each step
preserves it, then it holds at $s_n$; the invariant may depend on the processed prefix of $l$ or on
the step count. Restructuring a loop: a loop commutes with a map of states that intertwines its
steps, a loop over a concatenation of lists is a loop of loops, and a loop that acts on one
component of its state is one update of that component. Loops that write one entry per step, over a
state $y \colon \kappa \to \beta$, where $y[k \mapsto v]$ denotes $y$ with the entry $k$ replaced by
$v$: an entry that no step writes keeps its value; if no step reads an entry written by an earlier
step, each written entry holds the value that its step computes from the initial state; and in an
in-place (Gauss–Seidel) loop, a step reads the entries written before it. Exact arithmetic: running
sums and differences, loop interchange, and a loop that accumulates into one entry.

## Main results

* `List.exists_cons_cons_of_two_le_length`: a list of length at least $2$ starts with two elements.
* `List.mem_prefix_of_pairwise`: in a list ordered by $r$, an element $j \neq i$ with not $r(i, j)$
  comes before $i$.
* `List.Forall₂.exists_map_eq_of_nodup`: values related one by one to a list of distinct indices are
  the values of a function on the indices.
* `List.prod_map_filter`, `List.sum_map_filter`: a product over a filtered list is the product over
  the list with the factors outside the filter replaced by $1$.
* `List.prod_map_filter_finRange`, `List.sum_map_filter_finRange`: a product over a filtered list
  $[0, \dots, n - 1]$ is the `Finset` product over the filter.
* `List.foldl_prefix_induction`: a loop invariant indexed by the processed prefix.
* `List.foldl_induction`, `List.foldl_finRange_induction`: a loop invariant indexed by the step
  count.
* `List.idRun_foldlM_induction`, `List.idRun_foldlM_induction'`,
  `List.idRun_foldlM_finRange_induction`: the same invariants for loops in the identity monad.
* `List.foldl_lens`, `List.foldlM_lens`: a loop that acts on one component of its state is one
  update of that component.
* `List.foldlM_hom`: a loop commutes with a map of states that intertwines its steps.
* `List.foldlM_flatMap`, `List.foldlM_foldlM_eq_foldlM_flatMap`: a loop over a concatenation of
  lists is a loop of loops, and a loop of loops is one loop over the pairs of indices.
* `List.foldlM_update_self`, `List.foldl_update_self`: a loop that only rewrites the entry $i$, each
  time from its current value, is one update of the entry $i$.
* `List.foldlM_range_succ`, `List.idRun_foldlM_range_succ`: the last pass of a loop over
  $[0, \dots, n]$.
* `List.foldl_add_eq_add_sum_map`, `List.foldl_sub_eq_sub_sum_map`: a running sum or difference is
  $c \pm \sum_i f(x_i)$.
* `List.foldl_apply_of_pi`: if each step acts entrywise, each entry of the result is the loop run on
  that entry alone.
* `List.foldl_update_apply_of_forall_ne`: an entry that no step writes keeps its value.
* `List.foldl_update_apply_of_pairwise`: if no step reads an entry written by an earlier step, each
  written entry holds its step's value on the initial state.
* `List.foldl_update_of_nodup`, `List.foldl_update_eq_ite`: a loop that writes entry $i$ at step
  $i$, from values that do not depend on the other written entries, is a simultaneous update.
* `List.foldl_foldl_update_update_of_nodup`, `List.foldl_foldl_update_update_eq_ite`: the same for a
  double loop over rows and columns.
* `List.exists_foldl_update_apply_of_pairwise_rel`, `List.foldl_update_apply_of_pairwise_rel`: in an
  in-place loop along an ordered list, the value written by a step is computed from the entries
  written before it and the initial values of the others.
* `List.idRun_foldlM_update_apply`: a loop in the identity monad that rewrites each entry of a list
  of distinct indices once, from its current value, writes each entry from its initial value.

## Implementation notes

* The update $y[k \mapsto v]$ is `Function.update y k v`.
* A loop invariant that does not depend on the step count is core's `List.foldlRecOn`.
  `List.foldl_induction` is the `List` form of core's `Array.foldl_induction`.
* `List.foldlM_hom` and `List.foldlM_flatMap` are the monadic forms of core's `List.foldl_hom` and
  `List.foldl_flatMap`. The monadic results hold in every lawful monad.
* The results whose names start with `idRun_foldlM` are the forms, for the identity monad `Id`, of
  the corresponding results on `List.foldl`. They are stated with `Id.run`.
-/

universe u v

namespace List

variable {α β γ κ : Type*}

/-! ### Small list facts -/

/-- A list $l$ of length at least $2$ starts with two elements: `l = a :: b :: t` for some elements
$a, b$ and a list $t$. -/
theorem exists_cons_cons_of_two_le_length :
    ∀ {l : List α}, 2 ≤ l.length → ∃ a b t, l = a :: b :: t
  | a :: b :: t, _ => ⟨a, b, t, rfl⟩
  | [], h => absurd h (by simp)
  | [_], h => absurd h (by simp)

/-- Let $r \le n$. Keep the elements $k < r$ of the list $[0, 1, \dots, n - 1]$ of elements of
`Fin n`, and read each of them as an element of `Fin r`. The result is the list
$[0, 1, \dots, r - 1]$, that is, `List.finRange r`. -/
theorem filterMap_finRange_of_le {r n : ℕ} (hrn : r ≤ n) :
    (finRange n).filterMap
        (fun k : Fin n => if h : (k : ℕ) < r then some (⟨k, h⟩ : Fin r) else none) =
      finRange r := by
  induction n, hrn using Nat.le_induction with
  | base =>
    conv_rhs => rw [← filterMap_some (l := finRange r)]
    exact filterMap_congr fun k _ => by simp
  | succ m hrm ih =>
    rw [finRange_succ_last, filterMap_append, filterMap_map]
    have hlast : (filterMap (fun k : Fin (m + 1) =>
        if h : (k : ℕ) < r then some (⟨k, h⟩ : Fin r) else none) [Fin.last m]) = [] := by
      simp only [filterMap_cons, filterMap_nil, Fin.val_last]
      rw [dite_eq_right (by omega)]
    rw [hlast, append_nil, ← ih]
    rfl

/-- Let $r$ be a relation on $\alpha$, and let $l$ be a list in which $r(x, y)$ holds whenever $x$
comes before $y$ (`List.Pairwise r l`). Suppose that $l$ is the concatenation of a list $p$, an
element $i$ and a list $q$. If $j$ is an element of $l$ with $j \neq i$ and not $r(i, j)$, then
$j$ is an element of $p$. -/
theorem mem_prefix_of_pairwise {r : α → α → Prop} {l p q : List α} {i j : α}
    (hs : l.Pairwise r) (h : l = p ++ i :: q) (hj : j ∈ l) (hji : j ≠ i) (hr : ¬ r i j) :
    j ∈ p := by
  rw [h] at hs hj
  rcases mem_append.1 hj with hj | hj
  · exact hj
  · rcases mem_cons.1 hj with rfl | hj
    · exact absurd rfl hji
    · exact absurd ((pairwise_cons.1 (pairwise_append.1 hs).2.1).1 j hj) hr

/-- Let $R$ be a relation between $\alpha$ and $\beta$, let $o = [o_0, \dots, o_{n-1}]$ be a list of
distinct elements of $\alpha$, and let $ps = [q_0, \dots, q_{n-1}]$ be a list of elements of
$\beta$ with $R(o_k, q_k)$ for every $k < n$ (`List.Forall₂ R o ps`). Let
$d \colon \alpha \to \beta$ be any function. Then there is a function
$p \colon \alpha \to \beta$ such that $R(i, p(i))$ holds for every element $i$ of $o$ and
$[p(o_0), \dots, p(o_{n-1})] = ps$.

The function $d$ makes sure that a function $\alpha \to \beta$ exists. The proof takes $p = d$
outside the list $o$, but the statement does not record this. -/
theorem Forall₂.exists_map_eq_of_nodup {R : α → β → Prop} {o : List α} {ps : List β}
    (h : Forall₂ R o ps) (ho : o.Nodup) (d : α → β) :
    ∃ p : α → β, (∀ i ∈ o, R i (p i)) ∧ o.map p = ps := by
  classical
  induction h with
  | nil => exact ⟨d, by simp, rfl⟩
  | @cons a b o ps hab _ ih =>
    rcases nodup_cons.1 ho with ⟨ha, ho'⟩
    obtain ⟨p, hp, hmap⟩ := ih ho'
    refine ⟨Function.update p a b, fun i hi => ?_, ?_⟩
    · rcases mem_cons.1 hi with rfl | hi
      · rwa [Function.update_self]
      · rw [Function.update_of_ne fun (e : i = a) => ha (e ▸ hi)]
        exact hp i hi
    · rw [map_cons, Function.update_self, ← hmap]
      congr 1
      exact map_congr_left fun i hi => Function.update_of_ne (fun (e : i = a) => ha (e ▸ hi)) _ _

/-- Let $M$ be a monoid, let $p$ be a decidable predicate on $\alpha$, let $f \colon \alpha \to M$,
and let $l$ be a list. The product, in list order, of the values $f(a)$ at the elements $a$ of
$l$ that satisfy $p$ equals the product over all elements $a$ of $l$ of $f(a)$ if $p(a)$ holds
and $1$ otherwise. -/
@[to_additive /-- Let $M$ be an additive monoid, let $p$ be a decidable predicate on $\alpha$, let
$f \colon \alpha \to M$, and let $l$ be a list. The sum, in list order, of the values $f(a)$ at
the elements $a$ of $l$ that satisfy $p$ equals the sum over all elements $a$ of $l$ of $f(a)$ if
$p(a)$ holds and $0$ otherwise. -/]
theorem prod_map_filter {M : Type*} [Monoid M] (p : α → Prop) [DecidablePred p] (f : α → M)
    (l : List α) : ((l.filter p).map f).prod = (l.map fun a => if p a then f a else 1).prod := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

/-- Let $M$ be a commutative monoid, let $p$ be a decidable predicate on $\{0, \dots, n - 1\}$, and
let $f \colon \{0, \dots, n - 1\} \to M$. The product of $f$ over the elements of the list
$[0, \dots, n - 1]$ (`List.finRange n`) that satisfy $p$ equals the `Finset` product
$\prod_{i : p(i)} f(i)$. -/
@[to_additive /-- Let $M$ be a commutative additive monoid, let $p$ be a decidable predicate on
$\{0, \dots, n - 1\}$, and let $f \colon \{0, \dots, n - 1\} \to M$. The sum of $f$ over the
elements of the list $[0, \dots, n - 1]$ (`List.finRange n`) that satisfy $p$ equals the `Finset`
sum $\sum_{i : p(i)} f(i)$. -/]
theorem prod_map_filter_finRange {M : Type*} [CommMonoid M] {n : ℕ} (p : Fin n → Prop)
    [DecidablePred p] (f : Fin n → M) :
    (((finRange n).filter p).map f).prod = ∏ i ∈ Finset.univ.filter p, f i := by
  rw [prod_map_filter, Finset.prod_filter, Fin.prod_univ_def]

/-! ### Invariants -/

/-- Let $f \colon \beta \times \alpha \to \beta$ be a step function, let $l$ be a list, let
$b \in \beta$, and let $I$ be a predicate on pairs of a list and a state. Suppose that
$I([\,], b)$ holds, and that for every decomposition of $l$ as the concatenation of a list $p$,
an element $x$ and a list $q$, and every state $s$ with $I(p, s)$, also
$I(p \mathbin{+\!\!+} [x], f(s, x))$ holds. Then $I(l, s)$ holds for the result $s$ of the loop
`List.foldl f b l`. This is a loop invariant indexed by the processed prefix. -/
theorem foldl_prefix_induction {l : List α} (f : β → α → β) (I : List α → β → Prop) {b : β}
    (h0 : I [] b) (hstep : ∀ p x q, l = p ++ x :: q → ∀ s, I p s → I (p ++ [x]) (f s x)) :
    I l (l.foldl f b) := by
  suffices H : ∀ (r p : List α) (s : β), p ++ r = l → I p s → I l (r.foldl f s) from
    H l [] b rfl h0
  intro r
  induction r with
  | nil => rintro p s rfl hs; simpa using hs
  | cons x r ih =>
    rintro p s rfl hs
    exact ih (p ++ [x]) (f s x) (by simp) (hstep p x r rfl s hs)

/-- Let $l = [x_0, \dots, x_{n-1}]$, let $f \colon \beta \times \alpha \to \beta$, let
$b \in \beta$, and let $P_i$ be a predicate on $\beta$ for each $i \in \mathbb{N}$. Suppose that
$P_0(b)$ holds, and that $P_i(s)$ implies $P_{i+1}(f(s, x_i))$ for every $i < n$ and every state
$s$. Then $P_n$ holds for the result of the loop `List.foldl f b l`. This is a loop invariant
indexed by the step count, and the `List` form of core's `Array.foldl_induction`.

The predicate $P_i$ is `motive i`, and $x_i$ is `l[i]`. -/
theorem foldl_induction {l : List α} (motive : ℕ → β → Prop) {init : β} (h0 : motive 0 init)
    {f : β → α → β} (hf : ∀ i : Fin l.length, ∀ b, motive i b → motive (i + 1) (f b l[i])) :
    motive l.length (l.foldl f init) := by
  induction l generalizing motive init with
  | nil => exact h0
  | cons a l ih =>
    exact ih (fun k b => motive (k + 1) b) (hf ⟨0, by simp⟩ init h0)
      fun i b hb => hf ⟨i + 1, by simp⟩ b hb

/-- Let $f \colon \beta \times \{0, \dots, n - 1\} \to \beta$, let $b \in \beta$, and let $P_i$ be a
predicate on $\beta$ for each $i \in \mathbb{N}$. Suppose that $P_0(b)$ holds, and that $P_k(s)$
implies $P_{k+1}(f(s, k))$ for every $k < n$ and every state $s$. Then $P_n$ holds for the
result of the loop `List.foldl f b (List.finRange n)` over $k = 0, 1, \dots, n - 1$. -/
theorem foldl_finRange_induction {n : ℕ} (motive : ℕ → β → Prop) {init : β} (h0 : motive 0 init)
    {f : β → Fin n → β} (hf : ∀ (k : Fin n) (b : β), motive k b → motive (k + 1) (f b k)) :
    motive n ((finRange n).foldl f init) := by
  have h := foldl_induction (l := finRange n) motive h0 fun i b hb => by
    have e : (finRange n)[i] = ⟨i, by simpa using i.2⟩ := Fin.ext (by simp)
    rw [e]
    exact hf ⟨i, by simpa using i.2⟩ b hb
  rwa [length_finRange] at h

/-- Let $l = [x_0, \dots, x_{n-1}]$, let $f$ be a step function from $\beta \times \alpha$ to the
identity monad `Id β`, let $b \in \beta$, and let $P_i$ be a predicate on $\beta$ for each
$i \in \mathbb{N}$. Suppose that $P_0(b)$ holds, and that $P_i(s)$ implies $P_{i+1}(f(s, x_i))$
for every $i < n$ and every state $s$. Then $P_n$ holds for the result `(List.foldlM f b l).run`
of the loop. This is the form of `List.foldl_induction` for loops in exact arithmetic. -/
theorem idRun_foldlM_induction {α β : Type u} {l : List α} (motive : ℕ → β → Prop) {init : β}
    (h0 : motive 0 init) {f : β → α → Id β}
    (hf : ∀ i : Fin l.length, ∀ b, motive i b → motive (i + 1) (f b l[i]).run) :
    motive l.length (l.foldlM f init).run := by
  rw [idRun_foldlM]
  exact foldl_induction motive h0 hf

/-- Let $l = [x_0, \dots, x_{n-1}]$, let $f$ be a step function from $\beta \times \alpha$ to the
identity monad `Id β`, let $b \in \beta$, and let $P_i$ be a predicate on $\beta$ for each
$i \in \mathbb{N}$. Suppose that $P_0(b)$ holds, and that $P_k(s)$ implies $P_{k+1}(f(s, x_k))$
for every natural number $k < n$ and every state $s$. Then $P_n$ holds for the result
`(List.foldlM f b l).run` of the loop.

This is `List.idRun_foldlM_induction` with the hypothesis on the steps stated for natural
numbers $k$ and the entries `l[k]`, instead of for elements of `Fin l.length`. -/
theorem idRun_foldlM_induction' {α β : Type u} (l : List α) (motive : ℕ → β → Prop) {init : β}
    (h0 : motive 0 init) {f : β → α → Id β}
    (hf : ∀ (k : ℕ) (hk : k < l.length) (b : β), motive k b → motive (k + 1) (f b l[k]).run) :
    motive l.length (l.foldlM f init).run :=
  idRun_foldlM_induction motive h0 fun i b hb => hf i i.2 b hb

/-- Let $f$ be a step function from $\beta \times \{0, \dots, n - 1\}$ to the identity monad `Id β`,
let $b \in \beta$, and let $P_i$ be a predicate on $\beta$ for each $i \in \mathbb{N}$. Suppose
that $P_0(b)$ holds, and that $P_k(s)$ implies $P_{k+1}(f(s, k))$ for every $k < n$ and every
state $s$. Then $P_n$ holds for the result `((List.finRange n).foldlM f b).run` of the loop over
$k = 0, 1, \dots, n - 1$. This is the form of `List.foldl_finRange_induction` for loops in exact
arithmetic. -/
theorem idRun_foldlM_finRange_induction {β : Type u} {n : ℕ} (motive : ℕ → β → Prop) {init : β}
    (h0 : motive 0 init) {f : β → Fin n → Id β}
    (hf : ∀ (k : Fin n) (b : β), motive k b → motive (k + 1) (f b k).run) :
    motive n ((finRange n).foldlM f init).run := by
  rw [idRun_foldlM]
  exact foldl_finRange_induction motive h0 hf

/-! ### Restructuring a loop -/

/-- Let $\mathrm{get} \colon \sigma \to \beta$ and $\mathrm{set} \colon \sigma \times \beta \to
\sigma$ form a lens: $\mathrm{get}(\mathrm{set}(s, b)) = b$, $\mathrm{set}(\mathrm{set}(s, b),
b') = \mathrm{set}(s, b')$ and $\mathrm{set}(s, \mathrm{get}(s)) = s$ for all $s, b, b'$. Let
$f \colon \beta \times \alpha \to \beta$, let $l$ be a list, and let $s_0 \in \sigma$. Then the
loop over $l$ with the step $(s, a) \mapsto \mathrm{set}(s, f(\mathrm{get}(s), a))$, started at
$s_0$, returns $\mathrm{set}(s_0, t)$, where $t$ is the result of the loop over $l$ with the
step $f$, started at $\mathrm{get}(s_0)$. So a loop that acts on one component of its state is
one update of that component. This is the pure form of `List.foldlM_lens`. -/
theorem foldl_lens {σ : Type*} (get : σ → β) (set : σ → β → σ)
    (hgs : ∀ s b, get (set s b) = b) (hss : ∀ s b b', set (set s b) b' = set s b')
    (hsg : ∀ s, set s (get s) = s) (f : β → α → β) (l : List α) (s₀ : σ) :
    l.foldl (fun s a => set s (f (get s) a)) s₀ = set s₀ (l.foldl f (get s₀)) := by
  induction l generalizing s₀ with
  | nil => exact (hsg s₀).symm
  | cons a l ih => simp only [foldl_cons, ih, hgs, hss]

section Monadic

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- Let $m$ be a lawful monad, let $f \colon \beta_1 \to \beta_2$, and let $g_1 \colon \beta_1
\times \alpha \to m\,\beta_1$ and $g_2 \colon \beta_2 \times \alpha \to m\,\beta_2$ be steps
that $f$ intertwines: $g_2(f(x), y)$ is $f$ applied to the result of $g_1(x, y)$
(`g₂ (f x) y = Functor.map f (g₁ x y)`) for all $x$ and $y$. Then for every list $l$ and every
$b \in \beta_1$, the loop over $l$ with the step $g_2$, started at $f(b)$, is $f$ applied to the
result of the loop over $l$ with the step $g_1$, started at $b$. This is the monadic form of
core's `List.foldl_hom`. -/
theorem foldlM_hom {β₁ β₂ : Type u} (f : β₁ → β₂) {g₁ : β₁ → α → m β₁} {g₂ : β₂ → α → m β₂}
    {l : List α} {init : β₁} (H : ∀ x y, g₂ (f x) y = f <$> g₁ x y) :
    l.foldlM g₂ (f init) = f <$> l.foldlM g₁ init := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp only [foldlM_cons, map_bind, ← ih, H, bind_map_left]

/-- Let $m$ be a lawful monad, let $f$ map each element of $\alpha$ to a list of elements of
$\gamma$, let $g \colon \beta \times \gamma \to m\,\beta$, let $l = [x_0, \dots, x_{n-1}]$, and
let $b \in \beta$. The loop with the step $g$ over the concatenation $f(x_0) \mathbin{+\!\!+}
\dots \mathbin{+\!\!+} f(x_{n-1})$ (`List.flatMap f l`), started at $b$, equals the loop over
$l$ whose step at $x$ is the loop with the step $g$ over $f(x)$. This is the monadic form of
core's `List.foldl_flatMap`. -/
theorem foldlM_flatMap {β : Type u} {f : α → List γ} {g : β → γ → m β} {l : List α} {init : β} :
    (l.flatMap f).foldlM g init = l.foldlM (fun acc x => (f x).foldlM g acc) init := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Let $m$ be a lawful monad, let $l_1$ be a list of elements of $\alpha$, let $l_2(a)$ be a list
of elements of $\beta$ for each $a \in \alpha$, let $f \colon \sigma \times \alpha \times \beta
\to m\,\sigma$, and let $s \in \sigma$. The double loop over $a$ in $l_1$ (outer) and $b$ in
$l_2(a)$ (inner) with the step $f(\cdot, a, b)$, started at $s$, equals one loop with the same
step over the list of pairs $(a, b)$, with $a$ in the order of $l_1$ and, for each $a$, $b$ in
the order of $l_2(a)$. -/
theorem foldlM_foldlM_eq_foldlM_flatMap {σ : Type u} (l₁ : List α) (l₂ : α → List β)
    (f : σ → α → β → m σ) (s : σ) :
    l₁.foldlM (fun s a => (l₂ a).foldlM (fun s b => f s a b) s) s =
      (l₁.flatMap fun a => (l₂ a).map (a, ·)).foldlM (fun s p => f s p.1 p.2) s := by
  simp only [foldlM_flatMap, foldlM_map]

/-- Let $m$ be a lawful monad, and let $\mathrm{get} \colon \sigma \to \beta$ and $\mathrm{set}
\colon \sigma \times \beta \to \sigma$ form a lens: $\mathrm{get}(\mathrm{set}(s, b)) = b$,
$\mathrm{set}(\mathrm{set}(s, b), b') = \mathrm{set}(s, b')$ and
$\mathrm{set}(s, \mathrm{get}(s)) = s$ for all $s, b, b'$. Let
$f \colon \beta \times \alpha \to m\,\beta$, let $l$ be a list, and let $s_0 \in \sigma$.
Consider the loop over $l$ whose step at $a$ computes $b$ by $f(\mathrm{get}(s), a)$ and returns
$\mathrm{set}(s, b)$, started at $s_0$. It equals the program that computes $t$ by the loop over
$l$ with the step $f$, started at $\mathrm{get}(s_0)$, and returns $\mathrm{set}(s_0, t)$. So a
loop that acts on one component of its state is one update of that component. -/
theorem foldlM_lens {σ β : Type u} (get : σ → β) (set : σ → β → σ)
    (hgs : ∀ s b, get (set s b) = b) (hss : ∀ s b b', set (set s b) b' = set s b')
    (hsg : ∀ s, set s (get s) = s) (f : β → α → m β) (l : List α) (s₀ : σ) :
    l.foldlM (fun s a => do let b ← f (get s) a; pure (set s b)) s₀
      = (do let b ← l.foldlM f (get s₀); pure (set s₀ b)) := by
  induction l generalizing s₀ with
  | nil => simp only [foldlM_nil, pure_bind, hsg]
  | cons a l ih => simp only [foldlM_cons, bind_assoc, pure_bind, ih, hgs, hss]

/-- Let $m$ be a lawful monad, let $i \in \iota$, let $h \colon \alpha \times \beta \to m\,\beta$,
let $l$ be a list, and let $y \colon \iota \to \beta$. Consider the loop over $l$ whose step at
$a$ computes $b$ by $h(a, y_i)$ from the current state $y$ and replaces $y$ by $y[i \mapsto b]$,
started at $y$. It equals the program that computes $c$ by the loop over $l$ with the step
$(b, a) \mapsto h(a, b)$, started at $y_i$, and returns $y[i \mapsto c]$. Here $y[i \mapsto b]$
is `Function.update y i b`. This is the monadic form of `List.foldl_update_self`. -/
theorem foldlM_update_self {ι β : Type u} [DecidableEq ι] (i : ι) (h : α → β → m β) (l : List α)
    (y : ι → β) :
    l.foldlM (fun (y : ι → β) a => do let b ← h a (y i); pure (Function.update y i b)) y
      = (do let b ← l.foldlM (fun b a => h a b) (y i); pure (Function.update y i b)) :=
  foldlM_lens (fun y => y i) (fun y b => Function.update y i b) (by simp) (by simp) (by simp)
    (fun b a => h a b) l y

/-- Let $m$ be a lawful monad, let $f \colon \beta \times \mathbb{N} \to m\,\beta$, let
$b \in \beta$, and let $n \in \mathbb{N}$. The loop with the step $f$ over $[0, \dots, n]$
(`List.range (n + 1)`), started at $b$, runs the loop over $[0, \dots, n - 1]$ and then the step
$f(\cdot, n)$: `(range (n + 1)).foldlM f b = (range n).foldlM f b >>= fun c => f c n`. -/
theorem foldlM_range_succ {β : Type u} (f : β → ℕ → m β) (b : β) (n : ℕ) :
    (range (n + 1)).foldlM f b = (range n).foldlM f b >>= fun c => f c n := by
  rw [range_succ, foldlM_append]
  simp

end Monadic

/-- Let $f$ be a step function from $\beta \times \mathbb{N}$ to the identity monad `Id β`, let
$b \in \beta$, and let $n \in \mathbb{N}$. If $c$ is the result of the loop with the step $f$
over $[0, \dots, n - 1]$, started at $b$, then the loop over $[0, \dots, n]$, started at $b$,
returns $f(c, n)$. -/
theorem idRun_foldlM_range_succ {β : Type u} (f : β → ℕ → Id β) (b : β) (n : ℕ) :
    ((range (n + 1)).foldlM f b).run = (f ((range n).foldlM f b).run n).run := by
  rw [foldlM_range_succ]
  rfl

/-! ### Folds in exact arithmetic -/

/-- Let $M$ be an additive monoid, let $f \colon \alpha \to M$, let $l = [x_0, \dots, x_{n-1}]$, and
let $c \in M$. The running sum $$(\cdots((c + f(x_0)) + f(x_1)) + \cdots) + f(x_{n-1})$$ equals
$c + (f(x_0) + \dots + f(x_{n-1}))$, the sum taken in list order. -/
theorem foldl_add_eq_add_sum_map {M : Type*} [AddMonoid M] (f : α → M) (l : List α) (c : M) :
    l.foldl (fun c k => c + f k) c = c + (l.map f).sum := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => simp [ih, add_assoc]

/-- Let $M$ be a commutative additive monoid with a subtraction (a `SubtractionCommMonoid`), let
$f \colon \alpha \to M$, let $l = [x_0, \dots, x_{n-1}]$, and let $c \in M$. The running
difference $$(\cdots((c - f(x_0)) - f(x_1)) - \cdots) - f(x_{n-1})$$ equals
$c - \sum_{i < n} f(x_i)$. -/
theorem foldl_sub_eq_sub_sum_map {M : Type*} [SubtractionCommMonoid M] (f : α → M) (l : List α)
    (c : M) : l.foldl (fun c k => c - f k) c = c - (l.map f).sum := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => simp [ih, sub_sub]

/-- Let $f \colon (\iota \to \beta) \times \alpha \to (\iota \to \beta)$ be a step that acts
entrywise: there is $g \colon \alpha \times \iota \times \beta \to \beta$ with
$f(y, a)_i = g(a, i, y_i)$ for all $y$, $a$ and $i$. Then for every list $l$, every initial
state $y_0$ and every $i \in \iota$, the entry $i$ of the result of the loop over $l$ with the
step $f$, started at $y_0$, is the result of the loop over $l$ with the step
$(b, a) \mapsto g(a, i, b)$, started at $(y_0)_i$. This is loop interchange in exact arithmetic. -/
theorem foldl_apply_of_pi {ι : Type*} (f : (ι → β) → α → ι → β) (g : α → ι → β → β)
    (hf : ∀ y a i, f y a i = g a i (y i)) (l : List α) (y₀ : ι → β) (i : ι) :
    l.foldl f y₀ i = l.foldl (fun b a => g a i b) (y₀ i) := by
  induction l generalizing y₀ with
  | nil => rfl
  | cons a l ih => simp [ih, hf]

/-- Let $h \colon \alpha \times \beta \to \beta$, let $i \in \iota$, let $l$ be a list, and let
$y \colon \iota \to \beta$. The loop over $l$ whose step at $k$ replaces the state $y$ by
$y[i \mapsto h(k, y_i)]$, started at $y$, returns $y[i \mapsto c]$, where $c$ is the result of
the loop over $l$ with the step $(b, k) \mapsto h(k, b)$, started at $y_i$. Here
$y[i \mapsto b]$ is `Function.update y i b`. -/
theorem foldl_update_self {ι : Type*} [DecidableEq ι] (h : α → β → β) (i : ι) (l : List α)
    (y : ι → β) :
    l.foldl (fun y k => Function.update y i (h k (y i))) y
      = Function.update y i (l.foldl (fun b k => h k b) (y i)) := by
  induction l generalizing y with
  | nil => simp
  | cons a l ih => simp [ih]

/-! ### Loops writing one entry per step -/

section Update

variable [DecidableEq κ]

/-- Let $w \colon \alpha \to \kappa$ and $h \colon \alpha \times (\kappa \to \beta) \to \beta$, and
consider the loop over a list $l$ whose step at $a$ replaces the state
$y \colon \kappa \to \beta$ by $y[w(a) \mapsto h(a, y)]$. If $k \in \kappa$ satisfies
$w(a) \neq k$ for every element $a$ of $l$, then the entry $k$ of the result is the entry $y_k$
of the initial state $y$: an entry that no step writes keeps its value. Here $y[k \mapsto v]$ is
`Function.update y k v`. -/
theorem foldl_update_apply_of_forall_ne (w : α → κ) (h : α → (κ → β) → β) {l : List α} {k : κ}
    (hk : ∀ a ∈ l, w a ≠ k) (y : κ → β) :
    l.foldl (fun y a => Function.update y (w a) (h a y)) y k = y k := by
  induction l generalizing y with
  | nil => rfl
  | cons a l ih =>
    rw [foldl_cons, ih (fun b hb => hk b (mem_cons_of_mem a hb)),
      Function.update_of_ne (hk a mem_cons_self).symm]

/-- Let $w \colon \alpha \to \kappa$ and $h \colon \alpha \times (\kappa \to \beta) \to \beta$, and
consider the loop over a list $l$ whose step at $a$ replaces the state
$y \colon \kappa \to \beta$ by $y[w(a) \mapsto h(a, y)]$. Suppose that for all elements $a$
before $b$ in $l$, we have $w(a) \neq w(b)$, and $h(b, y) = h(b, y')$ for all states $y$ and
$y'$ that agree outside the entry $w(a)$; that is, the written entries are distinct and no step
reads an entry written by an earlier step. Then for every element $a$ of $l$, the entry $w(a)$
of the result is $h(a, y)$ for the initial state $y$.

Together with `List.foldl_update_apply_of_forall_ne`, this says that the loop is a simultaneous
update. The update $y[k \mapsto v]$ is `Function.update y k v`. -/
theorem foldl_update_apply_of_pairwise (w : α → κ) (h : α → (κ → β) → β) {l : List α}
    (hl : l.Pairwise fun a b => w a ≠ w b ∧
      ∀ y y' : κ → β, (∀ k, k ≠ w a → y k = y' k) → h b y = h b y')
    (y : κ → β) {a : α} (ha : a ∈ l) :
    l.foldl (fun y a => Function.update y (w a) (h a y)) y (w a) = h a y := by
  induction l generalizing y with
  | nil => exact absurd ha not_mem_nil
  | cons b l ih =>
    obtain ⟨hbl, hl'⟩ := pairwise_cons.1 hl
    rw [foldl_cons]
    rcases mem_cons.1 ha with rfl | ha
    · rw [foldl_update_apply_of_forall_ne w h (fun c hc => (hbl c hc).1.symm),
        Function.update_self]
    · rw [ih hl' _ ha]
      exact (hbl a ha).2 _ _ fun k hk => Function.update_of_ne hk _ _

/-- Let $l$ be a list of distinct elements of $\kappa$, and let $g \colon \kappa \times (\kappa \to
\beta) \to \beta$. Suppose that for every $i$ in $l$, the value $g(i, y)$ depends only on $y_i$
and on the entries of $y$ outside $l$: $g(i, y) = g(i, y')$ whenever $y_i = y'_i$ and
$y_r = y'_r$ for every $r \notin l$. Then the loop over $l$ whose step at $i$ replaces the state
$y$ by $y[i \mapsto g(i, y)]$, started at $y$, returns the state
$$r \mapsto \begin{cases} g(r, y) & \text{if } r \in l, \\ y_r & \text{otherwise.} \end{cases}$$
Here $y[i \mapsto v]$ is
`Function.update y i v`. -/
theorem foldl_update_of_nodup {l : List κ} (hl : l.Nodup) (g : κ → (κ → β) → β)
    (hg : ∀ i ∈ l, ∀ y y' : κ → β, (∀ r, r ∉ l → y r = y' r) → y i = y' i → g i y = g i y')
    (y : κ → β) :
    l.foldl (fun y i => Function.update y i (g i y)) y = fun r => if r ∈ l then g r y else y r := by
  have hpw : l.Pairwise fun a b => id a ≠ id b ∧
      ∀ y y' : κ → β, (∀ k, k ≠ id a → y k = y' k) → g b y = g b y' :=
    hl.pairwise_of_forall_ne fun a ha b hb hab => ⟨hab, fun z z' hz =>
      hg b hb z z' (fun r hr => hz r fun e => hr (e ▸ ha)) (hz b (Ne.symm hab))⟩
  funext r
  split_ifs with hr
  · exact foldl_update_apply_of_pairwise id g hpw y hr
  · exact foldl_update_apply_of_forall_ne id g (fun a ha (e : a = r) => hr (e ▸ ha)) y

/-- Let $g \colon \kappa \to \beta$, let $l$ be a list of elements of $\kappa$, and let
$y \colon \kappa \to \beta$. The loop over $l$ whose step at $i$ replaces the state by its
update $y[i \mapsto g(i)]$, started at $y$, returns the state that is $g(i)$ at every $i \in l$
and $y_i$ at every other $i$. The list may contain repeated elements. -/
theorem foldl_update_eq_ite (g : κ → β) (l : List κ) (y : κ → β) :
    l.foldl (fun y i => Function.update y i (g i)) y = fun i => if i ∈ l then g i else y i := by
  induction l generalizing y with
  | nil => simp
  | cons a l ih =>
    rw [foldl_cons, ih]
    funext i
    by_cases hi : i ∈ l
    · simp [hi]
    · by_cases hia : i = a
      · subst hia; simp [hi]
      · simp [hi, hia]

/-- Let $R$ be a list of distinct elements of $\kappa$, let $C$ be a list of distinct elements of
$\iota$, and let $h \colon (\kappa \to \iota \to \beta) \times \kappa \times \iota \to \beta$.
Suppose that for every $i \in R$ and $j \in C$, the value $h(y, i, j)$ depends only on the entry
$y_{ij}$ and on the entries $y_{ab}$ with $(a, b) \notin R \times C$. Consider the double loop
over the rows $i \in R$ (outer) and the columns $j \in C$ (inner) whose step at $(i, j)$
replaces the entry $(i, j)$ of the current state $y$ by $h(y, i, j)$. Started at $y$, it returns
the state whose entry $(i, j)$ is $h(y, i, j)$ for $(i, j) \in R \times C$ and $y_{ij}$
otherwise.

The state is a function `κ → ι → β`, and the step is `Function.update y i (Function.update (y i)
j (h y i j))`. -/
theorem foldl_foldl_update_update_of_nodup {ι : Type*} [DecidableEq ι] {R : List κ} {C : List ι}
    (hR : R.Nodup) (hC : C.Nodup) (h : (κ → ι → β) → κ → ι → β)
    (hh : ∀ y y' : κ → ι → β, (∀ a b, ¬ (a ∈ R ∧ b ∈ C) → y a b = y' a b) →
      ∀ i ∈ R, ∀ j ∈ C, y i j = y' i j → h y i j = h y' i j)
    (y : κ → ι → β) :
    R.foldl (fun y i => C.foldl (fun y j =>
        Function.update y i (Function.update (y i) j (h y i j))) y) y =
      fun i j => if i ∈ R ∧ j ∈ C then h y i j else y i j := by
  -- one row
  have hrow : ∀ i₀ ∈ R, ∀ C' : List ι, C'.Nodup → (∀ b ∈ C', b ∈ C) → ∀ (y : κ → ι → β) a b,
      C'.foldl (fun y j => Function.update y i₀ (Function.update (y i₀) j (h y i₀ j))) y a b =
        if a = i₀ ∧ b ∈ C' then h y i₀ b else y a b := by
    intro i₀ hi₀ C' hC' hsub
    induction C' with
    | nil => intro y a b; simp
    | cons c C' ih =>
      intro y a b
      obtain ⟨hc, hC''⟩ := nodup_cons.1 hC'
      rw [foldl_cons, ih hC'' fun b hb => hsub b (mem_cons_of_mem _ hb)]
      set y₁ := Function.update y i₀ (Function.update (y i₀) c (h y i₀ c)) with hy₁
      have hy₁a : ∀ a b, ¬ (a = i₀ ∧ b = c) → y₁ a b = y a b := fun a b hab => by
        rw [hy₁, Function.update_apply]
        split_ifs with ha
        · rw [ha, Function.update_of_ne fun hb => hab ⟨ha, hb⟩]
        · rfl
      by_cases hab : a = i₀ ∧ b ∈ C'
      · have hbc : b ≠ c := fun e => hc (e ▸ hab.2)
        rw [ite_eq_left hab, ite_eq_left ⟨hab.1, mem_cons_of_mem _ hab.2⟩]
        refine hh y₁ y (fun a' b' h' => hy₁a a' b' fun e => h' ⟨e.1 ▸ hi₀,
          e.2 ▸ hsub c mem_cons_self⟩) i₀ hi₀ b (hsub b (mem_cons_of_mem _ hab.2))
          (hy₁a i₀ b fun e => hbc e.2)
      · rw [ite_eq_right hab]
        by_cases hac : a = i₀ ∧ b = c
        · obtain ⟨rfl, rfl⟩ := hac
          simp [hy₁]
        · rw [hy₁a a b hac, ite_eq_right fun h' => ?_]
          rcases mem_cons.1 h'.2 with e | e
          · exact hac ⟨h'.1, e⟩
          · exact hab ⟨h'.1, e⟩
  -- all rows
  have hall : ∀ R' : List κ, R'.Nodup → (∀ a ∈ R', a ∈ R) → ∀ (y : κ → ι → β) a b,
      R'.foldl (fun y i => C.foldl (fun y j =>
        Function.update y i (Function.update (y i) j (h y i j))) y) y a b =
        if a ∈ R' ∧ b ∈ C then h y a b else y a b := by
    intro R' hR' hsub
    induction R' with
    | nil => intro y a b; simp
    | cons c R' ih =>
      intro y a b
      obtain ⟨hc, hR''⟩ := nodup_cons.1 hR'
      rw [foldl_cons, ih hR'' fun a ha => hsub a (mem_cons_of_mem _ ha)]
      have hrowc := hrow c (hsub c mem_cons_self) C hC fun b hb => hb
      set y₁ := C.foldl (fun y j => Function.update y c (Function.update (y c) j (h y c j))) y
        with hy₁
      have hy₁a : ∀ a b, ¬ (a = c ∧ b ∈ C) → y₁ a b = y a b := fun a b hab => by
        rw [hy₁, hrowc, ite_eq_right hab]
      by_cases hab : a ∈ R' ∧ b ∈ C
      · have hac : a ≠ c := fun e => hc (e ▸ hab.1)
        rw [ite_eq_left hab, ite_eq_left ⟨mem_cons_of_mem _ hab.1, hab.2⟩]
        refine hh y₁ y (fun a' b' h' => hy₁a a' b' fun e => h' ⟨e.1 ▸ hsub c mem_cons_self,
          e.2⟩) a (hsub a (mem_cons_of_mem _ hab.1)) b hab.2 (hy₁a a b fun e => hac e.1)
      · rw [ite_eq_right hab, hy₁, hrowc]
        by_cases hac : a = c
        · subst hac
          by_cases hb : b ∈ C <;> simp [hb]
        · have : ¬ (a ∈ c :: R' ∧ b ∈ C) := fun h' =>
            hab ⟨(mem_cons.1 h'.1).resolve_left hac, h'.2⟩
          rw [ite_eq_right fun e => hac e.1, ite_eq_right this]
  funext a b
  exact hall R hR (fun a ha => ha) y a b

/-- Let $g \colon \kappa \times \iota \to \beta$, let $R$ be a list of elements of $\kappa$, let $C$
be a list of elements of $\iota$, and let $y \colon \kappa \to \iota \to \beta$. The double loop
over $i \in R$ (outer) and $j \in C$ (inner) whose step at $(i, j)$ replaces the entry $(i, j)$
of the state by $g(i, j)$, started at $y$, returns the state whose entry $(i, j)$ is $g(i, j)$
for $(i, j) \in R \times C$ and $y_{ij}$ otherwise. The lists may contain repeated elements,
because a repeated step writes the same value again. -/
theorem foldl_foldl_update_update_eq_ite {ι : Type*} [DecidableEq ι] (g : κ → ι → β)
    (R : List κ) (C : List ι) (y : κ → ι → β) :
    R.foldl (fun y i => C.foldl (fun y j =>
        Function.update y i (Function.update (y i) j (g i j))) y) y =
      fun i j => if i ∈ R ∧ j ∈ C then g i j else y i j := by
  have hrow : ∀ (a : κ) (y : κ → ι → β),
      C.foldl (fun y j => Function.update y a (Function.update (y a) j (g a j))) y =
        fun i j => if i = a ∧ j ∈ C then g a j else y i j := by
    intro a
    induction C with
    | nil => intro y; funext i j; simp
    | cons b C ih =>
      intro y
      rw [foldl_cons, ih]
      funext i j
      by_cases hia : i = a
      · subst hia
        by_cases hj : j ∈ C
        · simp [hj]
        · by_cases hjb : j = b
          · subst hjb; simp [hj]
          · simp [hj, hjb]
      · simp [hia]
  induction R generalizing y with
  | nil => funext i j; simp
  | cons a R ih =>
    rw [foldl_cons, ih, hrow]
    funext i j
    by_cases hi : i ∈ R
    · by_cases hj : j ∈ C <;> simp [hi, hj]
    · by_cases hia : i = a
      · subst hia; simp [hi]
      · simp [hi, hia]

/-- Let $w \colon \alpha \to \kappa$, let $r$ be an asymmetric relation on $\alpha$ ($r(i, j)$
excludes $r(j, i)$), and let $f \colon \alpha \times (\kappa \to \beta) \to \beta$. Let $l$ be a
list with $r(a, b)$ for all elements $a$ before $b$, and let $w$ be injective on the elements of
$l$. Consider the loop over $l$ whose step at $j$ replaces the state $y$ by
$y[w(j) \mapsto f(j, y)]$, and let $z$ be its result from the initial state $x$. Then for every
element $i$ of $l$ there is a state $v$ with the following properties:

* $v_{w(j)} = z_{w(j)}$ for every element $j$ of $l$ with $r(j, i)$;
* $v_k = x_k$ for every $k \in \kappa$ that is $w(j)$ for no element $j$ of $l$ with $r(j, i)$;
* $z_{w(i)} = f(i, v)$.

This is the in-place (Gauss–Seidel) form of a loop: the step at $i$ reads the final values of
the entries written before it, and the initial values of the other entries. The update
$y[k \mapsto v]$ is `Function.update y k v`. -/
theorem exists_foldl_update_apply_of_pairwise_rel (w : α → κ) (r : α → α → Prop)
    (hr : ∀ i j, r i j → ¬ r j i) (f : α → (κ → β) → β) {l : List α}
    (hw : Set.InjOn w {a | a ∈ l}) (hl : l.Pairwise r) (x : κ → β) {i : α} (hi : i ∈ l) :
    ∃ v : κ → β,
      (∀ j ∈ l, r j i → v (w j) = l.foldl (fun y j => Function.update y (w j) (f j y)) x (w j)) ∧
      (∀ k, (∀ j ∈ l, r j i → w j ≠ k) → v k = x k) ∧
      l.foldl (fun y j => Function.update y (w j) (f j y)) x (w i) = f i v := by
  induction l generalizing x with
  | nil => exact absurd hi not_mem_nil
  | cons a l ih =>
    rw [pairwise_cons] at hl
    have ha : a ∉ l := fun h => hr a a (hl.1 a h) (hl.1 a h)
    have hne : ∀ j ∈ l, w j ≠ w a := fun j hj h =>
      ha (hw (mem_cons_of_mem a hj) mem_cons_self h ▸ hj)
    simp only [foldl_cons]
    rcases mem_cons.1 hi with rfl | hil
    · refine ⟨x, fun j hj hji => ?_, fun _ _ => rfl, ?_⟩
      · rcases mem_cons.1 hj with rfl | hjl
        · exact absurd hji (fun h => hr _ _ h h)
        · exact absurd (hl.1 j hjl) (hr _ _ hji)
      · rw [foldl_update_apply_of_forall_ne w f hne, Function.update_self]
    · obtain ⟨v, hv₁, hv₂, hv₃⟩ := ih (hw.mono fun j hj => mem_cons_of_mem a hj) hl.2
        (Function.update x (w a) (f a x)) hil
      have hva : v (w a) = f a x := by
        rw [hv₂ (w a) fun j hj _ => hne j hj, Function.update_self]
      refine ⟨v, fun j hj hji => ?_, fun k hk => ?_, hv₃⟩
      · rcases mem_cons.1 hj with rfl | hjl
        · rw [hva, foldl_update_apply_of_forall_ne w f hne, Function.update_self]
        · exact hv₁ j hjl hji
      · rw [hv₂ k fun j hj hji => hk j (mem_cons_of_mem a hj) hji]
        exact Function.update_of_ne (hk a mem_cons_self (hl.1 i hil)).symm _ _

/-- Let $r$ be an asymmetric decidable relation on $\kappa$, let $f \colon \kappa \times (\kappa \to
\beta) \to \beta$, and let $l$ be a list of elements of $\kappa$ with $r(a, b)$ for all elements
$a$ before $b$. Consider the loop over $l$ whose step at $i$ replaces the state $y$ by
$y[i \mapsto f(i, y)]$, and let $z$ be its result from the initial state $x$. Then for every
element $i$ of $l$,
$$z_i = f(i, v), \qquad
  v_j = \begin{cases} z_j & \text{if } j \in l \text{ and } r(j, i), \\
    x_j & \text{otherwise.} \end{cases}$$

This is the in-place (Gauss–Seidel) form of a loop, in which each step writes the entry of its
own index. Compared with `List.exists_foldl_update_apply_of_pairwise_rel`, the state $v$ is
given explicitly. The update $y[i \mapsto v]$ is `Function.update y i v`. -/
theorem foldl_update_apply_of_pairwise_rel (r : κ → κ → Prop) [DecidableRel r]
    (hr : ∀ i j, r i j → ¬ r j i) (f : κ → (κ → β) → β) {l : List κ} (hl : l.Pairwise r)
    (x : κ → β) {i : κ} (hi : i ∈ l) :
    l.foldl (fun y i => Function.update y i (f i y)) x i =
      f i (fun j => if j ∈ l ∧ r j i then
        l.foldl (fun y i => Function.update y i (f i y)) x j else x j) := by
  obtain ⟨v, hv₁, hv₂, hv₃⟩ :=
    exists_foldl_update_apply_of_pairwise_rel id r hr f (Set.injOn_id _) hl x hi
  have hv₃' : l.foldl (fun y i => Function.update y i (f i y)) x i = f i v := hv₃
  rw [hv₃']
  congr 1
  funext j
  split_ifs with hj
  · exact hv₁ j hj.1 hj.2
  · exact hv₂ j fun j' hj' hj'i e => hj (e ▸ ⟨hj', hj'i⟩)

end Update

/-- Let $l$ be a list of distinct elements of $\iota$, let $g$ be a function from
$\iota \times \beta$ to the identity monad `Id β`, let $y_0 \colon \iota \to \beta$, and let
$i \in \iota$. Consider the loop over $l$ whose step at $a$ computes $b = g(a, y_a)$ from the
current state $y$ and replaces $y$ by $y[a \mapsto b]$. Started at $y_0$, its result has the
entry $g(i, (y_0)_i)$ at $i$ if $i$ is in $l$, and the entry $(y_0)_i$ otherwise. Here
$y[a \mapsto b]$ is `Function.update y a b`. -/
theorem idRun_foldlM_update_apply {ι β : Type u} [DecidableEq ι] (g : ι → β → Id β)
    (l : List ι) (hl : l.Nodup) (y₀ : ι → β) (i : ι) :
    (l.foldlM (fun (y : ι → β) a => do
      let b ← g a (y a); pure (Function.update y a b)) y₀).run i =
      if i ∈ l then (g i (y₀ i)).run else y₀ i := by
  rw [idRun_foldlM]
  exact congrFun (foldl_update_of_nodup hl (fun a y => (g a (y a)).run)
    (fun a _ y y' _ h => by rw [h]) y₀) i

end List
