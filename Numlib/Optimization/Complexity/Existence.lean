/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic

/-!
# Existence of runs of relationally specified methods

The iterative methods of [cartis2022evaluation] are specified relationally (see
`Numlib.Optimization.Complexity.Basic`): a run is a sequence of states that satisfies the rule of
the method at every iteration before termination. The complexity theorems quantify over all runs, so
each method needs an existence theorem, which shows that these statements are not vacuous. Existence
follows from dependent choice along $\mathbb{N}$ as soon as every admissible state at which the
method has not stopped has an admissible successor.

## Main results

* `Optimization.exists_run_of_forall_exists`: if an initial state exists and every state at which
  the method has not stopped has a successor, there is a sequence that starts at an initial state
  and follows the step relation at every iteration at which it has not stopped.
* `Optimization.exists_run_of_forall_exists_of_invariant`: the same with an invariant, such as
  positivity of a regularization parameter, that the step relation needs and preserves. The
  conclusion holds up to termination, in the form of `Optimization.UntilHit`.
* `Optimization.exists_run_of_forall_exists_hist`: the same when the step may depend on the whole
  history $(r_0, \dots, r_k)$.

## Implementation notes

* States are typically tuples $(x_k, s_k, \sigma_k, \dots)$. The admissibility of the chosen step is
  part of the step relation.
-/

namespace Optimization

variable {α : Type*}

/-- **Existence of runs** (dependent choice). Let $\alpha$ be a type of states, let $\mathrm{init}$
be a predicate on $\alpha$, and for each $k \in \mathbb{N}$ let $\mathrm{stop}_k$ be a predicate
on $\alpha$ and $\mathrm{step}_k$ a relation on $\alpha$. Suppose that some $a$ satisfies
$\mathrm{init}(a)$, and that for every $k$ and every $a$ with $\lnot \mathrm{stop}_k(a)$ there
is $b$ with $\mathrm{step}_k(a, b)$. Then there is a sequence $r \colon \mathbb{N} \to \alpha$
with $\mathrm{init}(r_0)$ such that
$$\lnot \mathrm{stop}_k(r_k) \implies \mathrm{step}_k(r_k, r_{k+1}) \quad \text{for every } k.$$
-/
theorem exists_run_of_forall_exists {init : α → Prop} {stop : ℕ → α → Prop}
    {step : ℕ → α → α → Prop} (h0 : ∃ a, init a)
    (hstep : ∀ k a, ¬ stop k a → ∃ b, step k a b) :
    ∃ r : ℕ → α, init (r 0) ∧ ∀ k, ¬ stop k (r k) → step k (r k) (r (k + 1)) := by
  classical
  obtain ⟨a₀, ha₀⟩ := h0
  let next : ℕ → α → α := fun k a =>
    if h : ¬ stop k a then Classical.choose (hstep k a h) else a
  have hnext : ∀ k a, ¬ stop k a → step k a (next k a) := fun k a h => by
    simp only [next, h, not_false_eq_true, dite_true]
    exact Classical.choose_spec (hstep k a h)
  let r : ℕ → α := fun k => Nat.rec a₀ (fun k a => next k a) k
  exact ⟨r, ha₀, fun k hk => hnext k (r k) hk⟩

/-- **Existence of runs** with an invariant. Let $\alpha$ be a type of states, let $\mathrm{init}$
be a predicate on $\alpha$, and for each $k \in \mathbb{N}$ let $\mathrm{inv}_k$ and
$\mathrm{stop}_k$ be predicates on $\alpha$ and $\mathrm{step}_k$ a relation on $\alpha$.
Suppose that some $a$ satisfies $\mathrm{init}(a)$, that every $a$ with $\mathrm{init}(a)$
satisfies $\mathrm{inv}_0(a)$, and that for every $k$ and every $a$ with $\mathrm{inv}_k(a)$ and
$\lnot \mathrm{stop}_k(a)$ there is $b$ with $\mathrm{inv}_{k+1}(b)$ and
$\mathrm{step}_k(a, b)$. Then there is a sequence $r \colon \mathbb{N} \to \alpha$ with
$\mathrm{init}(r_0)$ such that, at every iteration $k$ before termination
($\lnot \mathrm{stop}_j(r_j)$ for all $j \le k$),
$$\mathrm{inv}_k(r_k) \quad\text{and}\quad \mathrm{step}_k(r_k, r_{k+1}).$$
-/
theorem exists_run_of_forall_exists_of_invariant {init : α → Prop} {inv : ℕ → α → Prop}
    {stop : ℕ → α → Prop} {step : ℕ → α → α → Prop} (h0 : ∃ a, init a)
    (hinit : ∀ a, init a → inv 0 a)
    (hstep : ∀ k a, inv k a → ¬ stop k a → ∃ b, inv (k + 1) b ∧ step k a b) :
    ∃ r : ℕ → α, init (r 0) ∧
      ∀ k, (∀ j ≤ k, ¬ stop j (r j)) → inv k (r k) ∧ step k (r k) (r (k + 1)) := by
  obtain ⟨r, hr0, hr⟩ := exists_run_of_forall_exists (init := init)
    (stop := fun k a => ¬ inv k a ∨ stop k a)
    (step := fun k a b => inv (k + 1) b ∧ step k a b) h0
    (fun k a h => by
      simp only [not_or, not_not] at h
      exact hstep k a h.1 h.2)
  refine ⟨r, hr0, ?_⟩
  have hinv : ∀ k, (∀ j ≤ k, ¬ stop j (r j)) → inv k (r k) := by
    intro k
    induction k with
    | zero => exact fun _ => hinit _ hr0
    | succ k ih =>
      intro hk
      have hk' : ∀ j ≤ k, ¬ stop j (r j) := fun j hj => hk j (Nat.le_trans hj k.le_succ)
      exact (hr k (by simp [ih hk', hk' k (Nat.le_refl k)])).1
  intro k hk
  have hi := hinv k hk
  exact ⟨hi, (hr k (by simp [hi, hk k (Nat.le_refl k)])).2⟩

/-- **Existence of runs** with history-dependent steps. Let $\alpha$ be a type of states and
$\mathrm{init}$ a predicate on $\alpha$. For each $k \in \mathbb{N}$, let $\mathrm{stop}_k$ be a
predicate on histories $(a_0, \dots, a_k) \in \alpha^{k+1}$, and let $\mathrm{step}_k$ relate a
history $(a_0, \dots, a_k)$ to a next state. Suppose that some $a$ satisfies $\mathrm{init}(a)$,
and that for every $k$ and every history $h$ with $\lnot \mathrm{stop}_k(h)$ there is $b$ with
$\mathrm{step}_k(h, b)$. Then there is a sequence $r \colon \mathbb{N} \to \alpha$ with
$\mathrm{init}(r_0)$ such that for every $k$
$$\lnot \mathrm{stop}_k(r_0, \dots, r_k) \implies \mathrm{step}_k((r_0, \dots, r_k), r_{k+1}).$$

A history is a map `Fin (k + 1) → α`. -/
theorem exists_run_of_forall_exists_hist {init : α → Prop}
    {stop : (k : ℕ) → (Fin (k + 1) → α) → Prop}
    {step : (k : ℕ) → (Fin (k + 1) → α) → α → Prop} (h0 : ∃ a, init a)
    (hstep : ∀ k (a : Fin (k + 1) → α), ¬ stop k a → ∃ b, step k a b) :
    ∃ r : ℕ → α, init (r 0) ∧
      ∀ k, ¬ stop k (fun i => r i) → step k (fun i => r i) (r (k + 1)) := by
  classical
  -- States are whole sequences whose first `k + 1` entries form the history at iteration `k`.
  obtain ⟨R, hR0, hR⟩ := exists_run_of_forall_exists (α := ℕ → α)
    (init := fun u => init (u 0)) (stop := fun _ _ => False)
    (step := fun k u v => (∀ i ≤ k, v i = u i) ∧
      (¬ stop k (fun i => u i) → step k (fun i => u i) (v (k + 1))))
    (let ⟨a, ha⟩ := h0; ⟨fun _ => a, ha⟩)
    (fun k u _ => by
      by_cases h : stop k (fun i => u i)
      · exact ⟨u, fun _ _ => rfl, fun h' => absurd h h'⟩
      · obtain ⟨b, hb⟩ := hstep k _ h
        refine ⟨Function.update u (k + 1) b, fun i hi => ?_, fun _ => by simpa using hb⟩
        rw [Function.update_of_ne (by omega)])
  have hcons : ∀ k i, i ≤ k → R k i = R i i := by
    intro k
    induction k with
    | zero => intro i hi; rw [Nat.le_zero.1 hi]
    | succ k ih =>
      intro i hi
      rcases Nat.lt_or_eq_of_le hi with hi | rfl
      · rw [(hR k not_false).1 i (Nat.lt_succ_iff.1 hi), ih i (Nat.lt_succ_iff.1 hi)]
      · rfl
  refine ⟨fun k => R k k, hR0, fun k hk => ?_⟩
  have hhist : (fun i : Fin (k + 1) => R i i) = fun i : Fin (k + 1) => R k i :=
    funext fun i => (hcons k i (Nat.lt_succ_iff.1 i.2)).symm
  rw [hhist] at hk ⊢
  exact (hR k not_false).2 hk

end Optimization
