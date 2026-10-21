import Mathlib.Order.WellFounded
import Lean.Elab.Tactic.Omega

/-!
# Finite stopping chains from natural-valued ranks

A relation that preserves an invariant and strictly decreases a natural rank admits a finite
chain to a stopping state whenever a next step exists at every invariant nonstopping state.
-/

namespace Relation

/-- A strictly decreasing natural rank constructs a finite relation chain reaching a stopping
state from every state satisfying the invariant. Choices need not be deterministic. -/
theorem exists_finite_stopped_chain_of_rank {X : Type*} (R : X → X → Prop) (rank : X → ℕ)
    (stop good : X → Prop) (hnext : ∀ a, good a → ¬stop a → ∃ b, R a b)
    (hpres : ∀ a b, good a → R a b → good b)
    (hdrop : ∀ a b, good a → R a b → rank b < rank a)
    {a : X} (ha : good a) :
    ∃ N : ℕ, ∃ state : ℕ → X, state 0 = a ∧ stop (state N) ∧
      ∀ k < N, R (state k) (state (k + 1)) := by
  classical
  have hall : ∀ n, ∀ a, rank a = n → good a →
      ∃ N : ℕ, ∃ state : ℕ → X, state 0 = a ∧ stop (state N) ∧
        ∀ k < N, R (state k) (state (k + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a he ha
      by_cases hs : stop a
      · exact ⟨0, fun _ => a, rfl, hs, fun k hk => (by omega : False).elim⟩
      obtain ⟨b, hab⟩ := hnext a ha hs
      have hlt : rank b < n := by simpa only [← he] using hdrop a b ha hab
      obtain ⟨N, state, hzero, hstop, htrans⟩ := ih (rank b) hlt b rfl (hpres a b ha hab)
      refine ⟨N + 1, fun k => if k = 0 then a else state (k - 1), by simp, ?_, ?_⟩
      · simpa using hstop
      · intro k hk
        cases k with
        | zero => simpa only [ite_true, Nat.zero_add, Nat.one_ne_zero, ite_false,
            Nat.sub_self, hzero] using hab
        | succ k => simpa using htrans k (by omega)
  exact hall (rank a) a rfl ha

end Relation
