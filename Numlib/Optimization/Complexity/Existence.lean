import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic

/-!
# Existence of runs of relationally specified methods

Iterative methods are specified relationally (see `Numlib/Optimization/Complexity/Basic`): a run
is a sequence of states satisfying the rule of the method at every iteration before termination.
Complexity theorems quantify over all runs, so every method needs an existence theorem to show
that these statements are not vacuous ([cartis2022evaluation], all algorithms). Existence follows
from dependent choice along `ℕ` as soon as every non-terminal admissible state has an admissible
successor.

* `Optimization.exists_run_of_forall_exists`: if an initial state exists and every state at which
  the method has not stopped has a successor, there is a sequence starting at an initial state and
  following the step relation at every non-stopped iteration.
* `Optimization.exists_run_of_forall_exists_of_invariant`: the same with an invariant (such as
  positivity of a regularization parameter) that the step relation needs and preserves; the
  conclusion is stated up to termination, in the form of `Optimization.UntilHit`.
* `Optimization.exists_run_of_forall_exists_hist`: the step may depend on the whole history
  `(r 0, …, r k)`.

States are typically tuples `(x_k, s_k, σ_k, …)`; admissibility of the chosen step is encoded in
the step relation.
-/

namespace Optimization

variable {α : Type*}

/-- **Existence of runs** (dependent choice). If an initial state exists and every state at which
the method has not stopped has an admissible successor, then there is a sequence of states `r`
with `init (r 0)` that follows `step` at every iteration `k` at which it has not stopped. -/
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

/-- **Existence of runs** with an invariant. If an initial state exists, every initial state
satisfies the invariant `inv 0`, and every state satisfying `inv k` at which the method has not
stopped has an admissible successor satisfying `inv (k + 1)`, then there is a sequence of states
`r` with `init (r 0)` such that at every iteration `k` before termination (the method has not
stopped at any `j ≤ k`) the invariant holds and `r` follows `step`. -/
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

/-- **Existence of runs** with history-dependent steps. If an initial state exists and for every
history `(a 0, …, a k)` at which the method has not stopped there is an admissible next state, then
there is a sequence `r` with `init (r 0)` such that `step k (r 0, …, r k) (r (k + 1))` holds at
every iteration `k` at which the method has not stopped. -/
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
