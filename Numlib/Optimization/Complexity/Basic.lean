/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Count
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Runs, first hits, success sets and evaluation counts

The evaluation-complexity analysis of iterative methods in [cartis2022evaluation] (Sections 1.2.4
and 2.2.2, and (2.3.9)–(2.3.10)) uses a vocabulary that does not depend on the method. This module
defines it. A run of a method is modelled relationally: it is a family of sequences indexed by
$\mathbb{N}$ (iterates, steps, parameters and so on) that satisfies the rule of the method at every
iteration $k$ at which the method has not terminated yet. The termination test $t$ is applied to the
current iterate before any other work, so the rule at iteration $k$ is imposed only when $t(j)$
failed at all $j \le k$. The method terminates at the first index where $t$ holds.

Let $S$ be a predicate on $\mathbb{N}$ ("iteration $j$ is successful"). The success set
$\mathcal{S}_k$ is the set of $j \in \{0, \dots, k\}$ with $S(j)$, and the failure set
$\mathcal{U}_k$ is the set of the other $j$ in that range, so
$|\mathcal{S}_k| + |\mathcal{U}_k| = k + 1$. A model-based method that terminates at iteration $k$
evaluates the objective $k + 1$ times, and it evaluates the derivatives once at $x_0$ and once after
each successful iteration $j < k$. Every complexity theorem ends with the same counting argument: if
$k + 1 \le A |\mathcal{S}_k| + B$ and $|\mathcal{S}_k| \le N$ at every iteration $k$ before
termination, then the method terminates at an iteration $k \le AN + B$.

## Main definitions

* `Optimization.IsFirstHit`: the test holds at $k$ and fails at every $j < k$.
* `Optimization.UntilHit`: the rule holds at every $k$ such that the test failed at every $j \le k$.
* `Optimization.successSet` and `Optimization.failureSet`: the sets $\mathcal{S}_k$ and
  $\mathcal{U}_k$ of (2.3.10).
* `Optimization.funEvalCount` and `Optimization.derivEvalCount`: the numbers of objective and
  derivative evaluations of a model-based method that terminates at iteration $k$.

## Main results

* `Optimization.card_successSet_add_card_failureSet`: $|\mathcal{S}_k| + |\mathcal{U}_k| = k + 1$.
* `Optimization.exists_hit_le_of_counting`: if $A \ge 0$, and $k + 1 \le A |\mathcal{S}_k| + B$ and
  $|\mathcal{S}_k| \le N$ at every $k$ before termination, then the test holds at some
  $k \le \lfloor AN + B \rfloor$.
* `Optimization.exists_isFirstHit_le_of_counting`: under the same hypotheses and $AN + B \ge 0$, the
  method terminates at some $k \le AN + B$.
* `Optimization.exists_isFirstHit_evalCount_le_of_counting`: in addition, at that iteration at most
  $AN + B + 1$ objective evaluations and at most $N + 1$ derivative evaluations have been made.
* `Optimization.derivEvalCount_le_of_isFirstHit`: if $|\mathcal{S}_k| \le N$ before termination, at
  most $N + 1$ derivative evaluations are made.
* `Optimization.exists_isFirstHit_of_sub_ge`: a quantity bounded below by $\varphi_{\mathrm{low}}$
  that decreases by at least $c > 0$ at every iteration before termination forces termination at
  some $k$ with $kc \le \varphi_0 - \varphi_{\mathrm{low}}$.
* `Optimization.card_successSet_le_two_mul_add_one`: if every successful iteration that is not good
  is followed, at the next success, by a good one, then $|\mathcal{S}_k| \le 2 |\mathcal{G}_k| + 1$,
  where $\mathcal{G}_k$ is the set of good iterations in $\{0, \dots, k\}$. This is the counting
  argument of Theorems 3.4.6 and 3.4.12 of [cartis2022evaluation].

## Implementation notes

* The index sets are `Finset.filter`s of `Finset.range` with classical decidability, so that the
  predicates, typically $j \mapsto \eta_1 \le \rho_j$ on real sequences, need no decidability
  instances. Use their API (`Optimization.mem_successSet`, the cardinality lemmas, and
  `Optimization.card_successSet_eq_count`, which relates them to `Nat.count`) instead of unfolding
  the definitions.
* The evaluation counts are those of methods with one trial point per iteration. Methods with inner
  loops state their own counts.
-/

open Finset

namespace Optimization

/-! ### First hits -/

/-- The method **terminates at iteration $k$** for the termination test $t$ if $t(k)$ holds and
$t(j)$ fails for every $j < k$. -/
def IsFirstHit (test : ℕ → Prop) (k : ℕ) : Prop :=
  test k ∧ ∀ j < k, ¬ test j

section IsFirstHit

variable {p : ℕ → Prop} {j k k' : ℕ}

/-- The method terminates at iteration $k$ if and only if $t(k)$ holds and $t(j)$ fails for every
$j < k$. -/
theorem isFirstHit_iff : IsFirstHit p k ↔ p k ∧ ∀ j < k, ¬ p j := Iff.rfl

/-- If the method terminates at iteration $k$, then the test holds at $k$. -/
theorem IsFirstHit.test (h : IsFirstHit p k) : p k := h.1

/-- If the method terminates at iteration $k$ and $j < k$, then the test fails at $j$. -/
theorem IsFirstHit.not_test_of_lt (h : IsFirstHit p k) (hj : j < k) : ¬ p j := h.2 j hj

/-- If the method terminates at iteration $k$ and $k' < k$, then the test fails at every $j \le k'$.
-/
theorem IsFirstHit.forall_le_not_test (h : IsFirstHit p k) (hk : k' < k) :
    ∀ j ≤ k', ¬ p j :=
  fun _ hj => h.not_test_of_lt (hj.trans_lt hk)

/-- If the method terminates at iteration $k$ and the test holds at $j$, then $k \le j$. -/
theorem IsFirstHit.le_of_test (h : IsFirstHit p k) (hj : p j) : k ≤ j :=
  not_lt.1 fun hjk => h.not_test_of_lt hjk hj

/-- The iteration at which the method terminates is unique. -/
theorem IsFirstHit.unique (h : IsFirstHit p k) (h' : IsFirstHit p k') : k = k' :=
  le_antisymm (h.le_of_test h'.test) (h'.le_of_test h.test)

/-- If the test holds at some index, the method terminates at iteration $k$ if and only if $k$ is
the least index at which the test holds (`Nat.find`). -/
theorem isFirstHit_iff_eq_find [DecidablePred p] (h : ∃ k, p k) :
    IsFirstHit p k ↔ k = Nat.find h := by
  constructor
  · intro hk
    exact le_antisymm (hk.le_of_test (Nat.find_spec h))
      (Nat.find_min' h hk.test)
  · rintro rfl
    exact ⟨Nat.find_spec h, fun _ hj => Nat.find_min h hj⟩

/-- If the test holds at some index, the method terminates at the least such index. -/
theorem isFirstHit_find [DecidablePred p] (h : ∃ k, p k) : IsFirstHit p (Nat.find h) :=
  (isFirstHit_iff_eq_find h).2 rfl

/-- If the test holds at $j$, then the method terminates at some iteration $k \le j$. -/
theorem exists_isFirstHit_le (hj : p j) : ∃ k ≤ j, IsFirstHit p k := by
  classical
  have h : ∃ k, p k := ⟨j, hj⟩
  exact ⟨Nat.find h, Nat.find_min' h hj, isFirstHit_find h⟩

/-- If the test holds at some index, then the method terminates at some iteration. -/
theorem exists_isFirstHit (h : ∃ k, p k) : ∃ k, IsFirstHit p k :=
  let ⟨_, hj⟩ := h
  let ⟨k, _, hk⟩ := exists_isFirstHit_le hj
  ⟨k, hk⟩

end IsFirstHit

/-! ### Rules imposed until termination -/

/-- The rule $r$ of a method holds **until termination** for the test $t$ if $r(k)$ holds at every
iteration $k$ at which the method has not terminated yet, that is, at every $k$ such that $t(j)$
fails for all $j \le k$. -/
def UntilHit (test rule : ℕ → Prop) : Prop :=
  ∀ k, (∀ j ≤ k, ¬ test j) → rule k

section UntilHit

variable {test rule rule' : ℕ → Prop} {k K : ℕ}

/-- The rule $r$ holds until termination for $t$ if and only if $r(k)$ holds at every $k$ such that
$t(j)$ fails for all $j \le k$. -/
theorem untilHit_iff : UntilHit test rule ↔ ∀ k, (∀ j ≤ k, ¬ test j) → rule k := Iff.rfl

/-- A rule that holds at every iteration holds until termination. -/
theorem UntilHit.of_forall (h : ∀ k, rule k) : UntilHit test rule := fun k _ => h k

/-- If the rule $r$ holds until termination and $r(k)$ implies $r'(k)$ for every $k$, then $r'$
holds until termination. -/
theorem UntilHit.mono (h : UntilHit test rule) (hr : ∀ k, rule k → rule' k) :
    UntilHit test rule' :=
  fun k hk => hr k (h k hk)

/-- If the rules $r$ and $r'$ hold until termination, then their conjunction holds until
termination. -/
theorem UntilHit.and (h : UntilHit test rule) (h' : UntilHit test rule') :
    UntilHit test fun k => rule k ∧ rule' k :=
  fun k hk => ⟨h k hk, h' k hk⟩

/-- The conjunction of two rules holds until termination if and only if each of them does. -/
theorem untilHit_and_iff :
    UntilHit test (fun k => rule k ∧ rule' k) ↔ UntilHit test rule ∧ UntilHit test rule' :=
  ⟨fun h => ⟨h.mono fun _ => And.left, h.mono fun _ => And.right⟩, fun h => h.1.and h.2⟩

/-- If the rule $r$ holds until termination and the method terminates at iteration $K$, then $r(k)$
holds for every $k < K$. -/
theorem UntilHit.of_lt_isFirstHit (h : UntilHit test rule) (hK : IsFirstHit test K)
    (hk : k < K) : rule k :=
  h k (hK.forall_le_not_test hk)

/-- If the rule $r$ holds until termination and the test fails at every $j < k$, then $r(j)$ holds
for every $j < k$. -/
theorem UntilHit.forall_lt (h : UntilHit test rule) (hk : ∀ j < k, ¬ test j) :
    ∀ j < k, rule j :=
  fun j hj => h j fun i hi => hk i (hi.trans_lt hj)

end UntilHit

/-! ### Success and failure sets -/

open Classical in
/-- The **success set** $\mathcal{S}_k$ of the predicate $S$ is the set of iterations
$j \in \{0, \dots, k\}$ with $S(j)$. For $S(j) \iff \eta_1 \le \rho_j$ this is the set
$$\mathcal{S}_k = \{ j \in \{0, \dots, k\} : \rho_j \ge \eta_1 \}$$
of (2.3.10) of [cartis2022evaluation]. It contains $k$ itself if $S(k)$ holds. -/
noncomputable def successSet (succ : ℕ → Prop) (k : ℕ) : Finset ℕ :=
  (range (k + 1)).filter succ

/-- The **failure set** $\mathcal{U}_k$ of the predicate $S$ is the set of iterations
$j \in \{0, \dots, k\}$ at which $S(j)$ fails. It is the set $\mathcal{U}_k = \{0, \dots, k\}
\setminus \mathcal{S}_k$ of (2.3.10) of [cartis2022evaluation]. -/
noncomputable def failureSet (succ : ℕ → Prop) (k : ℕ) : Finset ℕ :=
  successSet (fun j => ¬ succ j) k

section successSet

variable {succ succ' : ℕ → Prop} {j k k' : ℕ}

/-- $j \in \mathcal{S}_k$ if and only if $j \le k$ and $S(j)$ holds. -/
@[simp]
theorem mem_successSet : j ∈ successSet succ k ↔ j ≤ k ∧ succ j := by
  classical
  simp [successSet, Nat.lt_succ_iff]

/-- $j \in \mathcal{U}_k$ if and only if $j \le k$ and $S(j)$ fails. -/
@[simp]
theorem mem_failureSet : j ∈ failureSet succ k ↔ j ≤ k ∧ ¬ succ j :=
  mem_successSet

/-- For a decidable predicate, $\mathcal{S}_k$ is the filter of $\{0, \dots, k\}$ by $S$, with any
decidability instance. -/
theorem successSet_eq_filter [DecidablePred succ] :
    successSet succ k = (range (k + 1)).filter succ := by
  ext j
  simp [Nat.lt_succ_iff]

/-- $|\mathcal{S}_k|$ is the number of $j < k + 1$ with $S(j)$, as counted by `Nat.count`. -/
theorem card_successSet_eq_count [DecidablePred succ] :
    (successSet succ k).card = Nat.count succ (k + 1) := by
  rw [successSet_eq_filter, Nat.count_eq_card_filter_range]

/-- $\mathcal{S}_k \subseteq \{0, \dots, k\}$. -/
theorem successSet_subset_range : successSet succ k ⊆ range (k + 1) := fun j hj => by
  simp only [mem_successSet] at hj
  simpa [Nat.lt_succ_iff] using hj.1

/-- If $k \le k'$, then $\mathcal{S}_k \subseteq \mathcal{S}_{k'}$. -/
theorem successSet_mono (h : k ≤ k') : successSet succ k ⊆ successSet succ k' := fun j hj => by
  simp only [mem_successSet] at hj ⊢
  exact ⟨hj.1.trans h, hj.2⟩

/-- Monotonicity in the predicate: if $S(j)$ implies $S'(j)$ for every $j \le k$, then the success
set of $S$ up to $k$ is contained in that of $S'$. An example is the set of good successful
iterations inside the set of all successful ones. -/
theorem successSet_subset_successSet (h : ∀ j ≤ k, succ j → succ' j) :
    successSet succ k ⊆ successSet succ' k := fun j hj => by
  simp only [mem_successSet] at hj ⊢
  exact ⟨hj.1, h j hj.1 hj.2⟩

/-- If $k \le k'$, then $|\mathcal{S}_k| \le |\mathcal{S}_{k'}|$. -/
theorem card_successSet_mono (h : k ≤ k') :
    (successSet succ k).card ≤ (successSet succ k').card :=
  card_le_card (successSet_mono h)

/-- $|\mathcal{S}_k| \le k + 1$. -/
theorem card_successSet_le : (successSet succ k).card ≤ k + 1 :=
  (card_le_card successSet_subset_range).trans_eq (card_range _)

/-- If $S(0)$ holds, then $\mathcal{S}_0 = \{0\}$. -/
theorem successSet_zero_of_succ (h : succ 0) : successSet succ 0 = {0} := by
  ext j; simp only [mem_successSet, Nat.le_zero, mem_singleton]
  exact ⟨And.left, fun hj => ⟨hj, hj ▸ h⟩⟩

/-- If $S(0)$ fails, then $\mathcal{S}_0 = \emptyset$. -/
theorem successSet_zero_of_not_succ (h : ¬ succ 0) : successSet succ 0 = ∅ := by
  ext j; simp only [mem_successSet, Nat.le_zero, notMem_empty, iff_false, not_and]
  rintro rfl; exact h

/-- If $S(k + 1)$ holds, then $\mathcal{S}_{k+1} = \mathcal{S}_k \cup \{k + 1\}$. -/
theorem successSet_add_one_of_succ (h : succ (k + 1)) :
    successSet succ (k + 1) = insert (k + 1) (successSet succ k) := by
  ext j; simp only [mem_successSet, mem_insert]
  constructor
  · rintro ⟨hj, hs⟩
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact Or.inr ⟨Nat.lt_succ_iff.1 hj, hs⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨hj, hs⟩)
    · exact ⟨le_rfl, h⟩
    · exact ⟨hj.trans k.le_succ, hs⟩

/-- If $S(k + 1)$ fails, then $\mathcal{S}_{k+1} = \mathcal{S}_k$. -/
theorem successSet_add_one_of_not_succ (h : ¬ succ (k + 1)) :
    successSet succ (k + 1) = successSet succ k := by
  ext j; simp only [mem_successSet]
  constructor
  · rintro ⟨hj, hs⟩
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact ⟨Nat.lt_succ_iff.1 hj, hs⟩
    · exact absurd hs h
  · rintro ⟨hj, hs⟩
    exact ⟨hj.trans k.le_succ, hs⟩

/-- If $S(k + 1)$ holds, then $|\mathcal{S}_{k+1}| = |\mathcal{S}_k| + 1$. -/
theorem card_successSet_add_one_of_succ (h : succ (k + 1)) :
    (successSet succ (k + 1)).card = (successSet succ k).card + 1 := by
  rw [successSet_add_one_of_succ h, card_insert_of_notMem]
  simp

/-- If $S(k + 1)$ fails, then $|\mathcal{S}_{k+1}| = |\mathcal{S}_k|$. -/
theorem card_successSet_add_one_of_not_succ (h : ¬ succ (k + 1)) :
    (successSet succ (k + 1)).card = (successSet succ k).card := by
  rw [successSet_add_one_of_not_succ h]

/-- $|\mathcal{S}_{k+1}| \le |\mathcal{S}_k| + 1$. -/
theorem card_successSet_add_one_le :
    (successSet succ (k + 1)).card ≤ (successSet succ k).card + 1 := by
  by_cases h : succ (k + 1)
  · exact (card_successSet_add_one_of_succ h).le
  · rw [card_successSet_add_one_of_not_succ h]
    exact Nat.le_succ _

/-- For every predicate $S$ and every $k$, the success and failure sets partition $\{0, \dots, k\}$
in size:
$$|\mathcal{S}_k| + |\mathcal{U}_k| = k + 1.$$
-/
theorem card_successSet_add_card_failureSet :
    (successSet succ k).card + (failureSet succ k).card = k + 1 := by
  classical
  rw [failureSet, successSet_eq_filter, successSet_eq_filter, card_filter_add_card_filter_not,
    card_range]

/-- For every predicate $S$ and every $k$, the failure set is the complement of the success set in
$\{0, \dots, k\}$:
$$\mathcal{U}_k = \{0, \dots, k\} \setminus \mathcal{S}_k.$$
-/
theorem failureSet_eq_sdiff : failureSet succ k = range (k + 1) \ successSet succ k := by
  ext j
  simp only [mem_failureSet, mem_sdiff, mem_range, mem_successSet, Nat.lt_succ_iff]
  tauto

/-- If no $j \le k$ satisfies both $S(j)$ and $S'(j)$, then the iterations in $\{0, \dots, k\}$ that
satisfy $S$ or $S'$ are counted separately: their number is the size of the success set of $S$
plus the size of the success set of $S'$. -/
theorem card_successSet_or (h : ∀ j ≤ k, succ j → ¬ succ' j) :
    (successSet (fun j => succ j ∨ succ' j) k).card =
      (successSet succ k).card + (successSet succ' k).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext j; simp only [mem_successSet, mem_union]; tauto
  · rw [disjoint_left]
    intro j hj hj'
    simp only [mem_successSet] at hj hj'
    exact h j hj.1 hj.2 hj'.2

end successSet

/-! ### Evaluation counts -/

/-- The **number of objective evaluations** of a model-based method that terminates at iteration $k$
is $k + 1$: the initial value $f(x_0)$ and one trial value $f(x_j + s_j)$ for each iteration
$j < k$. -/
def funEvalCount (k : ℕ) : ℕ := k + 1

open Classical in
/-- The **number of derivative evaluations** of a model-based method that terminates at iteration
$k$, for the success predicate $S$, is $|\{ j < k : S(j) \}| + 1$: the initial derivatives at
$x_0$ and one evaluation after each successful iteration $j < k$.

The predicate can be any predicate $p$: the value counts one initial evaluation and one
evaluation for each iteration $j < k$ that satisfies $p$. Examples are
$p = \mathcal{S} \cup \mathcal{A}$ for the derivative evaluations, and
$p = \mathcal{T} = \mathcal{S} \cup \mathcal{U}$ for the function evaluations, of the
dynamic-accuracy methods of Chapter 13 of [cartis2022evaluation]. -/
noncomputable def derivEvalCount (succ : ℕ → Prop) (k : ℕ) : ℕ :=
  ((range k).filter succ).card + 1

section evalCount

variable {succ : ℕ → Prop} {k : ℕ}

/-- The number of objective evaluations at termination at iteration $k$ is $k + 1$. -/
@[simp]
theorem funEvalCount_eq (k : ℕ) : funEvalCount k = k + 1 := rfl

/-- A method that terminates at iteration $0$ makes one derivative evaluation. -/
@[simp]
theorem derivEvalCount_zero : derivEvalCount succ 0 = 1 := by
  simp [derivEvalCount]

/-- For a decidable predicate $S$, the number of derivative evaluations at termination at iteration
$k$ is $1$ plus the number of $j < k$ with $S(j)$, as counted by `Nat.count`. -/
theorem derivEvalCount_eq_count [DecidablePred succ] :
    derivEvalCount succ k = Nat.count succ k + 1 := by
  rw [derivEvalCount, Nat.count_eq_card_filter_range]
  congr 2
  ext j; simp

/-- The number of derivative evaluations at termination at iteration $k + 1$ is
$|\mathcal{S}_k| + 1$. -/
@[simp]
theorem derivEvalCount_add_one :
    derivEvalCount succ (k + 1) = (successSet succ k).card + 1 := by
  classical
  rw [derivEvalCount_eq_count, card_successSet_eq_count]

/-- The number of derivative evaluations at termination at iteration $k$ is at most
$|\mathcal{S}_k| + 1$. -/
theorem derivEvalCount_le_card_successSet_add_one :
    derivEvalCount succ k ≤ (successSet succ k).card + 1 := by
  cases k with
  | zero => simp
  | succ k => rw [derivEvalCount_add_one]; exact Nat.succ_le_succ (card_successSet_mono k.le_succ)

/-- The number of derivative evaluations at termination at iteration $k$ is at most the number
$k + 1$ of objective evaluations. -/
theorem derivEvalCount_le_funEvalCount : derivEvalCount succ k ≤ funEvalCount k := by
  classical
  rw [derivEvalCount_eq_count, funEvalCount_eq]
  exact Nat.succ_le_succ (Nat.count_le _)

/-- For predicates $p$ and $q$ and every $k$, the iterations $j < k$ that satisfy $p$ or $q$ give at
most the counts of $p$ and of $q$ together:
$$\mathrm{count}_{p \lor q}(k) + 1 \le \mathrm{count}_p(k) + \mathrm{count}_q(k),$$
where $\mathrm{count}_p(k) = |\{ j < k : p(j) \}| + 1$ is `Optimization.derivEvalCount p k`. An
example is the derivative evaluations of the dynamic-accuracy methods, made once per successful
and once per accuracy-improving iteration. -/
theorem derivEvalCount_or_add_one_le (p q : ℕ → Prop) (k : ℕ) :
    derivEvalCount (fun j => p j ∨ q j) k + 1 ≤ derivEvalCount p k + derivEvalCount q k := by
  classical
  simp only [derivEvalCount_eq_count]
  have : Nat.count (fun j => p j ∨ q j) k ≤ Nat.count p k + Nat.count q k := by
    simp only [Nat.count_eq_card_filter_range]
    rw [filter_or]
    exact card_union_le _ _
  omega

/-- Let $p$ be a predicate on $\mathbb{N}$ and $k \in \mathbb{N}$. If $p(j)$ holds for every
$j < k$, then
$$|\{ j < k : p(j) \}| = k.$$

The decidability instance of $p$ is an implicit argument, so that the lemma rewrites filters
built with any decidability instance. -/
theorem card_filter_range_of_forall {p : ℕ → Prop} {_ : DecidablePred p} {k : ℕ}
    (hp : ∀ j < k, p j) : ((range k).filter p).card = k := by
  rw [filter_true_of_mem fun j hj => hp j (mem_range.1 hj), card_range]

/-- Let $S$ be a predicate on $\mathbb{N}$ and $k \in \mathbb{N}$. If $S(j)$ holds for every
$j < k$, then the number of derivative evaluations at termination at iteration $k$ is
$$|\{ j < k : S(j) \}| + 1 = k + 1.$$
-/
theorem derivEvalCount_of_forall (hp : ∀ j < k, succ j) : derivEvalCount succ k = k + 1 := by
  rw [derivEvalCount, card_filter_range_of_forall hp]

end evalCount

/-! ### The counting skeleton -/

section counting

variable {test succ : ℕ → Prop} {A B N : ℝ}

/-- **Complexity skeleton.** Let $t$ be the termination test and $S$ the success predicate, and let
$A, B, N \in \mathbb{R}$ with $A \ge 0$. Suppose that at every iteration $k$ before termination
(that is, $t(j)$ fails for all $j \le k$) the number of iterations is bounded in terms of the
number of successful ones,
$$k + 1 \le A |\mathcal{S}_k| + B,$$
and the number of successful iterations is bounded, $|\mathcal{S}_k| \le N$. Then the test holds
at some iteration $k \le \lfloor AN + B \rfloor$.

Here $\lfloor \cdot \rfloor$ is `Nat.floor`, which is $0$ at negative arguments. -/
theorem exists_hit_le_of_counting (hA : 0 ≤ A)
    (hcount : ∀ k, (∀ j ≤ k, ¬ test j) → (k + 1 : ℝ) ≤ A * (successSet succ k).card + B)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ test j) → ((successSet succ k).card : ℝ) ≤ N) :
    ∃ k ≤ ⌊A * N + B⌋₊, test k := by
  by_contra hcon
  push Not at hcon
  set K := ⌊A * N + B⌋₊
  have hK : ∀ j ≤ K, ¬ test j := hcon
  have h1 := hcount K hK
  have h2 := mul_le_mul_of_nonneg_left (hsucc K hK) hA
  have h3 : A * N + B < K + 1 := Nat.lt_floor_add_one _
  linarith

/-- **Complexity skeleton**, first-hit form. Let $t$ be the termination test and $S$ the success
predicate, and let $A, B, N \in \mathbb{R}$ with $A \ge 0$ and $AN + B \ge 0$. Suppose that at
every iteration $k$ before termination
$$k + 1 \le A |\mathcal{S}_k| + B \quad\text{and}\quad |\mathcal{S}_k| \le N.$$
Then the method terminates at an iteration $k \le AN + B$. -/
theorem exists_isFirstHit_le_of_counting (hA : 0 ≤ A) (hAB : 0 ≤ A * N + B)
    (hcount : ∀ k, (∀ j ≤ k, ¬ test j) → (k + 1 : ℝ) ≤ A * (successSet succ k).card + B)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ test j) → ((successSet succ k).card : ℝ) ≤ N) :
    ∃ k, IsFirstHit test k ∧ (k : ℝ) ≤ A * N + B := by
  obtain ⟨j, hj, hjt⟩ := exists_hit_le_of_counting hA hcount hsucc
  obtain ⟨k, hkj, hk⟩ := exists_isFirstHit_le hjt
  exact ⟨k, hk, (Nat.cast_le.2 (hkj.trans hj)).trans (Nat.floor_le hAB)⟩

/-- Let $t$ be the termination test and $S$ the success predicate, and let $N \ge 0$. Suppose that
$|\mathcal{S}_k| \le N$ for every $k$ such that $t(j)$ fails for all $j \le k + 1$, that is, the
successful iterations before every iteration $k + 1$ that precedes termination number at most
$N$. Then $|\mathcal{S}_k| \le N + 1$ at every iteration $k$ before termination.

This turns the bounds on $\mathcal{S}_{k-1}$ of some analyses into the hypothesis of
`Optimization.exists_hit_le_of_counting`. -/
theorem card_successSet_le_add_one_of_forall (hN : 0 ≤ N)
    (hsucc : ∀ k, (∀ j ≤ k + 1, ¬ test j) → ((successSet succ k).card : ℝ) ≤ N) :
    ∀ k, (∀ j ≤ k, ¬ test j) → ((successSet succ k).card : ℝ) ≤ N + 1 := by
  intro k hk
  cases k with
  | zero =>
    have : (successSet succ 0).card ≤ 1 := card_successSet_le
    have : ((successSet succ 0).card : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  | succ k =>
    have h1 : ((successSet succ (k + 1)).card : ℝ) ≤ (successSet succ k).card + 1 := by
      exact_mod_cast card_successSet_add_one_le
    linarith [hsucc k hk]

/-- **Derivative evaluations at termination.** Let $t$ be the termination test, $S$ the success
predicate and $N \ge 0$. If $|\mathcal{S}_k| \le N$ at every iteration $k$ before termination
and the method terminates at iteration $K$, then the number of derivative evaluations satisfies
$$|\{ j < K : S(j) \}| + 1 \le N + 1.$$

The successful iterations before $K$ form the set $\mathcal{S}_{K-1}$, which the hypothesis
bounds when $K \ge 1$. -/
theorem derivEvalCount_le_of_isFirstHit {K : ℕ} (hN : 0 ≤ N) (hK : IsFirstHit test K)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ test j) → ((successSet succ k).card : ℝ) ≤ N) :
    (derivEvalCount succ K : ℝ) ≤ N + 1 := by
  cases K with
  | zero => simp [hN]
  | succ k =>
    rw [derivEvalCount_add_one]
    push_cast
    linarith [hsucc k (hK.forall_le_not_test k.lt_succ_self)]

/-- **Complexity skeleton with evaluation counts.** Let $t$ be the termination test and $S$ the
success predicate, and let $A, B, N \in \mathbb{R}$ with $A \ge 0$, $N \ge 0$ and
$AN + B \ge 0$. Suppose that at every iteration $k$ before termination
$$k + 1 \le A |\mathcal{S}_k| + B \quad\text{and}\quad |\mathcal{S}_k| \le N.$$
Then the method terminates at some iteration $k$ at which the number of objective evaluations is
at most $AN + B + 1$ and the number of derivative evaluations is at most $N + 1$. -/
theorem exists_isFirstHit_evalCount_le_of_counting (hA : 0 ≤ A) (hN : 0 ≤ N)
    (hAB : 0 ≤ A * N + B)
    (hcount : ∀ k, (∀ j ≤ k, ¬ test j) → (k + 1 : ℝ) ≤ A * (successSet succ k).card + B)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ test j) → ((successSet succ k).card : ℝ) ≤ N) :
    ∃ k, IsFirstHit test k ∧ (funEvalCount k : ℝ) ≤ A * N + B + 1 ∧
      (derivEvalCount succ k : ℝ) ≤ N + 1 := by
  obtain ⟨k, hk, hkle⟩ := exists_isFirstHit_le_of_counting hA hAB hcount hsucc
  refine ⟨k, hk, ?_, derivEvalCount_le_of_isFirstHit hN hk hsucc⟩
  rw [funEvalCount_eq]
  push_cast
  linarith

end counting

/-! ### Uniform decrease -/

section decrease

variable {φ : ℕ → ℝ} {test : ℕ → Prop} {c φlow : ℝ}

/-- If $c \le \varphi_k - \varphi_{k+1}$ at every index $k$ before termination, then
$\varphi_K \le \varphi_0 - Kc$ for every $K$ such that the test fails at all $j < K$. -/
private theorem le_sub_mul_of_forall
    (hdec : ∀ k, (∀ j ≤ k, ¬ test j) → c ≤ φ k - φ (k + 1)) :
    ∀ K, (∀ j < K, ¬ test j) → φ K ≤ φ 0 - K * c := by
  intro K
  induction K with
  | zero => intro _; simp
  | succ K ih =>
    intro hK
    have h1 := ih fun j hj => hK j (hj.trans K.lt_succ_self)
    have h2 := hdec K fun j hj => hK j (Nat.lt_succ_of_le hj)
    push_cast
    linarith

/-- **Termination under a uniform decrease.** Let $t$ be the termination test, let
$\varphi \colon \mathbb{N} \to \mathbb{R}$ and $\varphi_{\mathrm{low}} \in \mathbb{R}$ with
$\varphi_k \ge \varphi_{\mathrm{low}}$ for all $k$, and let $c > 0$. If
$$c \le \varphi_k - \varphi_{k+1}$$
at every index $k$ before termination, then the method terminates at some iteration $k$ with
$$kc \le \varphi_0 - \varphi_{\mathrm{low}}.$$

This is the counting argument of Theorems 2.2.2 and 2.2.4 of [cartis2022evaluation], for methods
without unsuccessful iterations. -/
theorem exists_isFirstHit_of_sub_ge (hc : 0 < c)
    (hdec : ∀ k, (∀ j ≤ k, ¬ test j) → c ≤ φ k - φ (k + 1)) (hlow : ∀ k, φlow ≤ φ k) :
    ∃ k, IsFirstHit test k ∧ (k : ℝ) * c ≤ φ 0 - φlow := by
  have key := le_sub_mul_of_forall hdec
  have hex : ∃ k, test k := by
    by_contra hne
    push Not at hne
    obtain ⟨K, hK⟩ := exists_nat_gt ((φ 0 - φlow) / c)
    have := key K fun j _ => hne j
    rw [div_lt_iff₀ hc] at hK
    linarith [hlow K]
  obtain ⟨k, hk⟩ := exists_isFirstHit hex
  exact ⟨k, hk, by linarith [key k fun j hj => hk.not_test_of_lt hj, hlow k]⟩

end decrease

/-! ### Successes with a good successor -/

/-- **Counting successes with a good successor.** Let $S$ and $G$ be predicates on $\mathbb{N}$
("successful" and "good") and let $K \in \mathbb{N}$. Suppose that $G(j)$ implies $S(j)$ for
every $j \le K$, and that whenever $j < j' \le K$, $j$ is successful but not good, $j'$ is
successful, and no iteration strictly between $j$ and $j'$ is successful, then $j'$ is good.
Then for every $k \le K$,
$$|\mathcal{S}_k| \le 2 |\mathcal{G}_k| + 1,$$
where $\mathcal{G}_k$ is the set of good iterations in $\{0, \dots, k\}$.

This is the counting argument of Theorems 3.4.6 and 3.4.12 of [cartis2022evaluation]. -/
theorem card_successSet_le_two_mul_add_one {succ good : ℕ → Prop} {K : ℕ}
    (hgood : ∀ j ≤ K, good j → succ j)
    (hnext : ∀ j j', j < j' → j' ≤ K → succ j → ¬ good j → succ j' →
      (∀ i, j < i → i < j' → ¬ succ i) → good j') :
    ∀ k ≤ K, (successSet succ k).card ≤ 2 * (successSet good k).card + 1 := by
  -- `b k`: some bad success `j ≤ k` has no success after it up to `k`
  let b : ℕ → Prop := fun k => ∃ j ≤ k, succ j ∧ ¬ good j ∧ ∀ i, j < i → i ≤ k → ¬ succ i
  have key : ∀ k ≤ K, (b k → (successSet succ k).card ≤ 2 * (successSet good k).card + 1) ∧
      (¬ b k → (successSet succ k).card ≤ 2 * (successSet good k).card) := by
    intro k
    induction k with
    | zero =>
      intro _
      by_cases hs : succ 0
      · by_cases hg : good 0
        · rw [successSet_zero_of_succ hs, successSet_zero_of_succ hg]
          simp
        · have hb : b 0 := ⟨0, le_rfl, hs, hg, fun i hi hi' => absurd hi' (by omega)⟩
          rw [successSet_zero_of_succ hs]
          exact ⟨fun _ => by simp, fun h => absurd hb h⟩
      · rw [successSet_zero_of_not_succ hs]
        simp
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (Nat.le_of_succ_le hk)
      by_cases hs : succ (k + 1)
      · rw [card_successSet_add_one_of_succ hs]
        by_cases hg : good (k + 1)
        · rw [card_successSet_add_one_of_succ hg]
          have : (successSet succ k).card ≤ 2 * (successSet good k).card + 1 := by
            by_cases hb : b k
            · exact ih1 hb
            · exact (ih2 hb).trans (Nat.le_succ _)
          constructor <;> intro <;> omega
        · rw [card_successSet_add_one_of_not_succ hg]
          have hnb : ¬ b k := by
            rintro ⟨j, hj, hsj, hgj, hnone⟩
            exact hg (hnext j (k + 1) (by omega) hk hsj hgj hs fun i hi hi' =>
              hnone i hi (by omega))
          have := ih2 hnb
          refine ⟨fun _ => by omega, fun hb => absurd ⟨k + 1, le_rfl, hs, hg,
            fun i hi hi' => absurd hi' (by omega)⟩ hb⟩
      · rw [card_successSet_add_one_of_not_succ hs,
          card_successSet_add_one_of_not_succ fun hg => hs (hgood _ hk hg)]
        have hbb : b (k + 1) ↔ b k := by
          constructor
          · rintro ⟨j, hj, hsj, hgj, hnone⟩
            rcases Nat.lt_or_eq_of_le hj with hj | rfl
            · exact ⟨j, Nat.lt_succ_iff.1 hj, hsj, hgj, fun i hi hi' => hnone i hi (by omega)⟩
            · exact absurd hsj hs
          · rintro ⟨j, hj, hsj, hgj, hnone⟩
            refine ⟨j, hj.trans k.le_succ, hsj, hgj, fun i hi hi' => ?_⟩
            rcases Nat.lt_or_eq_of_le hi' with hi' | rfl
            · exact hnone i hi (Nat.lt_succ_iff.1 hi')
            · exact hs
        rw [hbb]
        exact ⟨ih1, ih2⟩
  intro k hk
  by_cases hb : b k
  · exact (key k hk).1 hb
  · exact ((key k hk).2 hb).trans (Nat.le_succ _)

end Optimization
