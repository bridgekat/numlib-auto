import Mathlib.Data.Nat.Count
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Runs, first hits, success sets and evaluation counts

Algorithm-agnostic vocabulary for the evaluation-complexity analysis of iterative methods
([cartis2022evaluation], Sections 1.2.4, 2.2.2, (2.3.9)–(2.3.10)).

An iterative method is modelled *relationally*: a run is a family of sequences indexed by `ℕ`
(iterates, steps, parameters, …) satisfying the rule of the method at every iteration `k` at which
the method has not yet terminated. Termination is tested at the current iterate before any other
work is done, so the rule at iteration `k` is imposed only when the termination test has failed
at all iterations `j ≤ k` (`Optimization.UntilHit`). The method terminates at the first index
where the test holds (`Optimization.IsFirstHit`).

* `Optimization.IsFirstHit test k`: `test k` holds and `test j` fails for `j < k`.
* `Optimization.UntilHit test rule`: `rule k` holds whenever `test` failed at every `j ≤ k`.
* `Optimization.successSet succ k`: the iterations `j ∈ [0, k]` satisfying `succ` (the book's
  `𝒮_k`, which *includes* `k`), and `Optimization.failureSet succ k` (the book's `𝒰_k`), with
  `|𝒮_k| + |𝒰_k| = k + 1` (`Optimization.card_successSet_add_card_failureSet`).
* Evaluation counts of model-based methods terminating at iteration `k`:
  `Optimization.funEvalCount k = k + 1` objective values (the initial one and one trial value per
  iteration `0, …, k - 1`) and `Optimization.derivEvalCount succ k` derivative values (the initial
  one and one after each successful iteration `j < k`). Methods with inner loops state their own
  counts.
* `Optimization.exists_hit_le_of_counting`: the counting skeleton of every complexity theorem. If
  before termination `k + 1 ≤ A |𝒮_k| + B` and `|𝒮_k| ≤ N`, then the test holds at some
  `k ≤ ⌊A N + B⌋₊`; `Optimization.exists_isFirstHit_le_of_counting` gives the first such index
  with `k ≤ A N + B`, and `Optimization.exists_isFirstHit_evalCount_le_of_counting` bounds the
  evaluation counts at that index (`funEvalCount k ≤ A N + B + 1`, `derivEvalCount succ k ≤ N + 1`,
  via `Optimization.derivEvalCount_le_of_isFirstHit`).
* `Optimization.card_successSet_le_two_mul_add_one`: if every successful iteration that is not
  "good" is followed (at the next success) by a good one, then `|𝒮_k| ≤ 2 |𝒢_k| + 1` (the counting
  of the corrected Theorems 3.4.6 and 3.4.12 of [cartis2022evaluation]).
* `Optimization.exists_isFirstHit_of_sub_ge`: the counting skeleton of methods with a uniform
  decrease per iteration (no unsuccessful iterations): a potential bounded below by `φlow` that
  decreases by `c > 0` at every iteration before termination forces termination at some `k` with
  `k c ≤ φ 0 - φlow`.

## Implementation notes

The index sets are `Finset.filter`s of `Finset.range` with classical decidability, so that the
predicates (typically `fun j => η₁ ≤ ρ j` on real sequences) need no decidability instances. Their
API (`Optimization.mem_successSet`, the cardinality lemmas, `Optimization.card_successSet_eq_count`
relating to `Nat.count`) should be used instead of unfolding the definitions.
-/

open Finset

namespace Optimization

/-! ### First hits -/

/-- `IsFirstHit test k`: the termination test holds at iteration `k` and at no earlier
iteration, i.e. the method terminates at iteration `k`. -/
def IsFirstHit (test : ℕ → Prop) (k : ℕ) : Prop :=
  test k ∧ ∀ j < k, ¬ test j

section IsFirstHit

variable {p : ℕ → Prop} {j k k' : ℕ}

theorem isFirstHit_iff : IsFirstHit p k ↔ p k ∧ ∀ j < k, ¬ p j := Iff.rfl

theorem IsFirstHit.test (h : IsFirstHit p k) : p k := h.1

theorem IsFirstHit.not_test_of_lt (h : IsFirstHit p k) (hj : j < k) : ¬ p j := h.2 j hj

/-- The test fails up to any iteration before the first hit. -/
theorem IsFirstHit.forall_le_not_test (h : IsFirstHit p k) (hk : k' < k) :
    ∀ j ≤ k', ¬ p j :=
  fun _ hj => h.not_test_of_lt (hj.trans_lt hk)

theorem IsFirstHit.le_of_test (h : IsFirstHit p k) (hj : p j) : k ≤ j :=
  not_lt.1 fun hjk => h.not_test_of_lt hjk hj

theorem IsFirstHit.unique (h : IsFirstHit p k) (h' : IsFirstHit p k') : k = k' :=
  le_antisymm (h.le_of_test h'.test) (h'.le_of_test h.test)

theorem isFirstHit_iff_eq_find [DecidablePred p] (h : ∃ k, p k) :
    IsFirstHit p k ↔ k = Nat.find h := by
  constructor
  · intro hk
    exact le_antisymm (hk.le_of_test (Nat.find_spec h))
      (Nat.find_min' h hk.test)
  · rintro rfl
    exact ⟨Nat.find_spec h, fun _ hj => Nat.find_min h hj⟩

theorem isFirstHit_find [DecidablePred p] (h : ∃ k, p k) : IsFirstHit p (Nat.find h) :=
  (isFirstHit_iff_eq_find h).2 rfl

/-- If the test holds at `j`, the method terminates at some iteration `k ≤ j`. -/
theorem exists_isFirstHit_le (hj : p j) : ∃ k ≤ j, IsFirstHit p k := by
  classical
  have h : ∃ k, p k := ⟨j, hj⟩
  exact ⟨Nat.find h, Nat.find_min' h hj, isFirstHit_find h⟩

theorem exists_isFirstHit (h : ∃ k, p k) : ∃ k, IsFirstHit p k :=
  let ⟨_, hj⟩ := h
  let ⟨k, _, hk⟩ := exists_isFirstHit_le hj
  ⟨k, hk⟩

end IsFirstHit

/-! ### Rules imposed until termination -/

/-- `UntilHit test rule`: the rule `rule k` of the method holds at every iteration `k` at which
the method has not terminated yet, i.e. whenever the termination test failed at all `j ≤ k`. -/
def UntilHit (test rule : ℕ → Prop) : Prop :=
  ∀ k, (∀ j ≤ k, ¬ test j) → rule k

section UntilHit

variable {test rule rule' : ℕ → Prop} {k K : ℕ}

theorem untilHit_iff : UntilHit test rule ↔ ∀ k, (∀ j ≤ k, ¬ test j) → rule k := Iff.rfl

theorem UntilHit.of_forall (h : ∀ k, rule k) : UntilHit test rule := fun k _ => h k

theorem UntilHit.mono (h : UntilHit test rule) (hr : ∀ k, rule k → rule' k) :
    UntilHit test rule' :=
  fun k hk => hr k (h k hk)

theorem UntilHit.and (h : UntilHit test rule) (h' : UntilHit test rule') :
    UntilHit test fun k => rule k ∧ rule' k :=
  fun k hk => ⟨h k hk, h' k hk⟩

theorem untilHit_and_iff :
    UntilHit test (fun k => rule k ∧ rule' k) ↔ UntilHit test rule ∧ UntilHit test rule' :=
  ⟨fun h => ⟨h.mono fun _ => And.left, h.mono fun _ => And.right⟩, fun h => h.1.and h.2⟩

/-- The rule holds at every iteration before the first hit. -/
theorem UntilHit.of_lt_isFirstHit (h : UntilHit test rule) (hK : IsFirstHit test K)
    (hk : k < K) : rule k :=
  h k (hK.forall_le_not_test hk)

/-- If the test failed at every `j < k`, the rule held at every `j < k`. -/
theorem UntilHit.forall_lt (h : UntilHit test rule) (hk : ∀ j < k, ¬ test j) :
    ∀ j < k, rule j :=
  fun j hj => h j fun i hi => hk i (hi.trans_lt hj)

end UntilHit

/-! ### Success and failure sets -/

open Classical in
/-- `successSet succ k` is the set of iterations `j ∈ [0, k]` satisfying `succ`: the book's
`𝒮_k = {j ∈ [0 : k] | ρ_j ≥ η₁}` (2.3.10) for `succ j = (η₁ ≤ ρ j)`. It includes `k` itself. -/
noncomputable def successSet (succ : ℕ → Prop) (k : ℕ) : Finset ℕ :=
  (range (k + 1)).filter succ

/-- `failureSet succ k` is the set of iterations `j ∈ [0, k]` not satisfying `succ`: the book's
`𝒰_k = [0 : k] ∖ 𝒮_k` (2.3.10). -/
noncomputable def failureSet (succ : ℕ → Prop) (k : ℕ) : Finset ℕ :=
  successSet (fun j => ¬ succ j) k

section successSet

variable {succ succ' : ℕ → Prop} {j k k' : ℕ}

@[simp]
theorem mem_successSet : j ∈ successSet succ k ↔ j ≤ k ∧ succ j := by
  classical
  simp [successSet, Nat.lt_succ_iff]

@[simp]
theorem mem_failureSet : j ∈ failureSet succ k ↔ j ≤ k ∧ ¬ succ j :=
  mem_successSet

theorem successSet_eq_filter [DecidablePred succ] :
    successSet succ k = (range (k + 1)).filter succ := by
  ext j
  simp [Nat.lt_succ_iff]

theorem card_successSet_eq_count [DecidablePred succ] :
    (successSet succ k).card = Nat.count succ (k + 1) := by
  rw [successSet_eq_filter, Nat.count_eq_card_filter_range]

theorem successSet_subset_range : successSet succ k ⊆ range (k + 1) := fun j hj => by
  simp only [mem_successSet] at hj
  simpa [Nat.lt_succ_iff] using hj.1

theorem successSet_mono (h : k ≤ k') : successSet succ k ⊆ successSet succ k' := fun j hj => by
  simp only [mem_successSet] at hj ⊢
  exact ⟨hj.1.trans h, hj.2⟩

/-- Monotonicity in the predicate (e.g. "good" successful iterations among all successful ones). -/
theorem successSet_subset_successSet (h : ∀ j ≤ k, succ j → succ' j) :
    successSet succ k ⊆ successSet succ' k := fun j hj => by
  simp only [mem_successSet] at hj ⊢
  exact ⟨hj.1, h j hj.1 hj.2⟩

theorem card_successSet_mono (h : k ≤ k') :
    (successSet succ k).card ≤ (successSet succ k').card :=
  card_le_card (successSet_mono h)

theorem card_successSet_le : (successSet succ k).card ≤ k + 1 :=
  (card_le_card successSet_subset_range).trans_eq (card_range _)

theorem successSet_zero_of_succ (h : succ 0) : successSet succ 0 = {0} := by
  ext j; simp only [mem_successSet, Nat.le_zero, mem_singleton]
  exact ⟨And.left, fun hj => ⟨hj, hj ▸ h⟩⟩

theorem successSet_zero_of_not_succ (h : ¬ succ 0) : successSet succ 0 = ∅ := by
  ext j; simp only [mem_successSet, Nat.le_zero, notMem_empty, iff_false, not_and]
  rintro rfl; exact h

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

theorem card_successSet_add_one_of_succ (h : succ (k + 1)) :
    (successSet succ (k + 1)).card = (successSet succ k).card + 1 := by
  rw [successSet_add_one_of_succ h, card_insert_of_notMem]
  simp

theorem card_successSet_add_one_of_not_succ (h : ¬ succ (k + 1)) :
    (successSet succ (k + 1)).card = (successSet succ k).card := by
  rw [successSet_add_one_of_not_succ h]

theorem card_successSet_add_one_le :
    (successSet succ (k + 1)).card ≤ (successSet succ k).card + 1 := by
  by_cases h : succ (k + 1)
  · exact (card_successSet_add_one_of_succ h).le
  · rw [card_successSet_add_one_of_not_succ h]
    exact Nat.le_succ _

/-- `|𝒮_k| + |𝒰_k| = k + 1`. -/
theorem card_successSet_add_card_failureSet :
    (successSet succ k).card + (failureSet succ k).card = k + 1 := by
  classical
  rw [failureSet, successSet_eq_filter, successSet_eq_filter, card_filter_add_card_filter_not,
    card_range]

/-- `𝒰_k = [0 : k] ∖ 𝒮_k`. -/
theorem failureSet_eq_sdiff : failureSet succ k = range (k + 1) \ successSet succ k := by
  ext j
  simp only [mem_failureSet, mem_sdiff, mem_range, mem_successSet, Nat.lt_succ_iff]
  tauto

/-- The iterations satisfying one of two incompatible predicates are counted separately. -/
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

/-- Number of objective evaluations of a model-based method that terminates at iteration `k`:
the initial value `f(x₀)` and one trial value `f(x_j + s_j)` for each iteration `j < k`. -/
def funEvalCount (k : ℕ) : ℕ := k + 1

open Classical in
/-- Number of derivative evaluations of a model-based method that terminates at iteration `k`:
the initial derivatives at `x₀` and one evaluation after each successful iteration `j < k`.

`succ` may be any predicate: `derivEvalCount p k = |{j < k | p j}| + 1` counts the initial
evaluation plus one per iteration `j < k` satisfying `p` (e.g. `p = 𝒮 ∪ 𝒜` for the derivative
evaluations, or `p = 𝒯 = 𝒮 ∪ 𝒰` for the function evaluations of the methods of Chapter 13). -/
noncomputable def derivEvalCount (succ : ℕ → Prop) (k : ℕ) : ℕ :=
  ((range k).filter succ).card + 1

section evalCount

variable {succ : ℕ → Prop} {k : ℕ}

@[simp]
theorem funEvalCount_eq (k : ℕ) : funEvalCount k = k + 1 := rfl

@[simp]
theorem derivEvalCount_zero : derivEvalCount succ 0 = 1 := by
  simp [derivEvalCount]

theorem derivEvalCount_eq_count [DecidablePred succ] :
    derivEvalCount succ k = Nat.count succ k + 1 := by
  rw [derivEvalCount, Nat.count_eq_card_filter_range]
  congr 2
  ext j; simp

@[simp]
theorem derivEvalCount_add_one :
    derivEvalCount succ (k + 1) = (successSet succ k).card + 1 := by
  classical
  rw [derivEvalCount_eq_count, card_successSet_eq_count]

theorem derivEvalCount_le_card_successSet_add_one :
    derivEvalCount succ k ≤ (successSet succ k).card + 1 := by
  cases k with
  | zero => simp
  | succ k => rw [derivEvalCount_add_one]; exact Nat.succ_le_succ (card_successSet_mono k.le_succ)

theorem derivEvalCount_le_funEvalCount : derivEvalCount succ k ≤ funEvalCount k := by
  classical
  rw [derivEvalCount_eq_count, funEvalCount_eq]
  exact Nat.succ_le_succ (Nat.count_le _)

/-- Counting the iterations `j < k` with `p j ∨ q j` (e.g. the derivative evaluations of the
dynamic-accuracy methods, once per successful or accuracy-improving iteration):
`derivEvalCount (p ∨ q) k + 1 ≤ derivEvalCount p k + derivEvalCount q k`. -/
theorem derivEvalCount_or_add_one_le (p q : ℕ → Prop) (k : ℕ) :
    derivEvalCount (fun j => p j ∨ q j) k + 1 ≤ derivEvalCount p k + derivEvalCount q k := by
  classical
  simp only [derivEvalCount_eq_count]
  have : Nat.count (fun j => p j ∨ q j) k ≤ Nat.count p k + Nat.count q k := by
    simp only [Nat.count_eq_card_filter_range]
    rw [filter_or]
    exact card_union_le _ _
  omega

end evalCount

/-! ### The counting skeleton -/

section counting

variable {test succ : ℕ → Prop} {A B N : ℝ}

/-- **Complexity skeleton.** Suppose that at every iteration `k` before termination the number of
iterations is bounded in terms of the number of successful ones, `k + 1 ≤ A |𝒮_k| + B` with
`A ≥ 0`, and the number of successful iterations is bounded, `|𝒮_k| ≤ N`. Then the termination test
holds at some iteration `k ≤ ⌊A N + B⌋₊`. -/
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

/-- **Complexity skeleton**, first-hit form: under the hypotheses of
`Optimization.exists_hit_le_of_counting` and `0 ≤ A N + B`, the method terminates at an
iteration `k ≤ A N + B`. -/
theorem exists_isFirstHit_le_of_counting (hA : 0 ≤ A) (hAB : 0 ≤ A * N + B)
    (hcount : ∀ k, (∀ j ≤ k, ¬ test j) → (k + 1 : ℝ) ≤ A * (successSet succ k).card + B)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ test j) → ((successSet succ k).card : ℝ) ≤ N) :
    ∃ k, IsFirstHit test k ∧ (k : ℝ) ≤ A * N + B := by
  obtain ⟨j, hj, hjt⟩ := exists_hit_le_of_counting hA hcount hsucc
  obtain ⟨k, hkj, hk⟩ := exists_isFirstHit_le hjt
  exact ⟨k, hk, (Nat.cast_le.2 (hkj.trans hj)).trans (Nat.floor_le hAB)⟩

/-- If the successful iterations *before* every iteration `k + 1` preceding termination are at
most `N` (`|𝒮_k| ≤ N` whenever the test fails up to `k + 1`), then `|𝒮_k| ≤ N + 1` at every
iteration `k` preceding termination. This converts the "`𝒮_{k-1}`" bounds of some analyses into
the hypothesis of `Optimization.exists_hit_le_of_counting`. -/
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

/-- **Derivative evaluations at termination.** If `|𝒮_k| ≤ N` (with `0 ≤ N`) at every iteration
`k` before termination and the method terminates at iteration `K`, then
`derivEvalCount succ K ≤ N + 1` (the successful iterations before `K` form `𝒮_{K-1}`). -/
theorem derivEvalCount_le_of_isFirstHit {K : ℕ} (hN : 0 ≤ N) (hK : IsFirstHit test K)
    (hsucc : ∀ k, (∀ j ≤ k, ¬ test j) → ((successSet succ k).card : ℝ) ≤ N) :
    (derivEvalCount succ K : ℝ) ≤ N + 1 := by
  cases K with
  | zero => simp [hN]
  | succ k =>
    rw [derivEvalCount_add_one]
    push_cast
    linarith [hsucc k (hK.forall_le_not_test k.lt_succ_self)]

/-- **Complexity skeleton with evaluation counts.** Suppose that at every iteration `k` before
termination `k + 1 ≤ A |𝒮_k| + B` (`A ≥ 0`) and `|𝒮_k| ≤ N` (`N ≥ 0`), and `0 ≤ A N + B`. Then the
method terminates at some iteration `k` with `funEvalCount k ≤ A N + B + 1` and
`derivEvalCount succ k ≤ N + 1`. -/
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

/-- A sequence decreasing by at least `c` at every index before termination decreases by `K c`
over the first `K` indices. -/
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

/-- **Termination under a uniform decrease** (the counting of [cartis2022evaluation] Theorems
2.2.2 and 2.2.4). If a quantity bounded below by `φlow` decreases by at least `c > 0` at every
index before termination, then the test holds at some first index `k` with
`k c ≤ φ 0 - φlow`. -/
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

/-- **Counting successes with a good successor.** Let `good j` imply `succ j` for `j ≤ K`, and
suppose that whenever a successful iteration `j` is not good, the next successful iteration
`j' ≤ K` (no success strictly between) is good. Then `|𝒮_k| ≤ 2 |𝒢_k| + 1` for every `k ≤ K`,
where `𝒢_k` are the good iterations in `[0, k]`. -/
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
