import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite descent budgets

A bounded objective can pay for only finitely many iterations with a fixed positive decrease.
The scalar statements here apply equally to function values, residual norms and merit functions.
`card_mul_le_gap` counts a selected set of successful iterations, allowing unsuccessful iterations
with zero decrease. `exists_first_of_decrease` only requires the decrease rule until the first
successful termination test; the algorithm need not keep decreasing after termination.

These are the telescoping arguments used throughout Cartis–Gould–Toint, *Evaluation Complexity
of Algorithms for Nonconvex Optimization* (2022), beginning with the proof of Theorem 2.2.2.
-/

namespace Optimization.EvaluationComplexity

/-- The decrease over a finite prefix telescopes to the gap between its endpoints. -/
theorem sum_decrease_eq (u : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (u k - u (k + 1)) = u 0 - u n :=
  Finset.sum_range_sub' u n

/-- A selected set of successful iterations consumes at least its cardinality times the
guaranteed decrease. Other iterations need only leave the objective nonincreasing. -/
theorem card_mul_le_gap {u : ℕ → ℝ} {n : ℕ} {S : Finset ℕ} {low δ : ℝ}
    (hS : S ⊆ Finset.range n) (hlow : low ≤ u n)
    (hmono : ∀ k < n, u (k + 1) ≤ u k)
    (hdec : ∀ k ∈ S, δ ≤ u k - u (k + 1)) :
    (S.card : ℝ) * δ ≤ u 0 - low := by
  calc
    (S.card : ℝ) * δ = ∑ _k ∈ S, δ := by simp
    _ ≤ ∑ k ∈ S, (u k - u (k + 1)) := Finset.sum_le_sum hdec
    _ ≤ ∑ k ∈ Finset.range n, (u k - u (k + 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS fun k hk _ =>
        sub_nonneg.mpr (hmono k (Finset.mem_range.mp hk))
    _ = u 0 - u n := sum_decrease_eq u n
    _ ≤ u 0 - low := sub_le_sub_left hlow _

/-- A positive decrease at each of the first `n` steps bounds their number by the initial gap
divided by that decrease. Only the last objective value needs a lower bound. -/
theorem iteration_bound {u : ℕ → ℝ} {n : ℕ} {low δ : ℝ} (hδ : 0 < δ)
    (hlow : low ≤ u n) (hdec : ∀ k < n, δ ≤ u k - u (k + 1)) :
    (n : ℝ) ≤ (u 0 - low) / δ := by
  rw [le_div_iff₀ hδ]
  simpa using card_mul_le_gap (S := Finset.range n) (fun _ h => h) hlow
    (fun k hk => by linarith [hdec k hk]) (fun k hk => hdec k (Finset.mem_range.mp hk))

/-- A uniform bound on every unterminated prefix forces a first successful test. -/
theorem exists_first_of_prefix_bound {P : ℕ → Prop} {B : ℝ}
    (hbound : ∀ n, (∀ j < n, ¬ P j) → (n : ℝ) ≤ B) :
    ∃ k ≤ ⌊B⌋₊, P k ∧ ∀ j < k, ¬ P j := by
  classical
  have hex : ∃ k ≤ ⌊B⌋₊, P k := by
    by_contra! h
    have hb := hbound (⌊B⌋₊ + 1) (fun j hj => h j (by omega))
    have hflo := Nat.lt_floor_add_one B
    push_cast at hb
    linarith
  obtain ⟨k, hk, hPk⟩ := hex
  have hex' : ∃ j, P j := ⟨k, hPk⟩
  exact ⟨Nat.find hex', (Nat.find_min' hex' hPk).trans hk,
    Nat.find_spec hex', fun j hj => Nat.find_min hex' hj⟩

/-- If failure of the termination test forces a positive decrease while all preceding tests
have failed, the first successful test occurs within the finite descent budget. -/
theorem exists_first_of_decrease {u : ℕ → ℝ} {P : ℕ → Prop} {low δ : ℝ}
    (hδ : 0 < δ) (hlow : ∀ n, low ≤ u n)
    (hdec : ∀ n, (∀ j ≤ n, ¬ P j) → δ ≤ u n - u (n + 1)) :
    ∃ k ≤ ⌊(u 0 - low) / δ⌋₊, P k ∧ ∀ j < k, ¬ P j := by
  apply exists_first_of_prefix_bound
  intro n hn
  exact iteration_bound hδ (hlow n) (fun k hk =>
    hdec k (fun j hj => hn j (by omega)))

end Optimization.EvaluationComplexity
