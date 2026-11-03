import Numlib.Optimization.ModelBased.ReferenceDecrease
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# A nonmonotone trust-region method

The historical sum can be zero when there are no accepted steps since the reference iteration.
The historical ratio still has a positive denominator because it includes the current predicted
reduction.
-/

open scoped BigOperators

namespace ConnGouldToint.Chapter10

/-- Reference indices for (10.1.2), corrected to allow the same index to be retained.
The reference objective decreases strictly whenever the reference index changes. -/
def IsReferenceSchedule (f : ℕ → ℝ) (r : ℕ → ℕ) : Prop :=
  (∀ k, r k ≤ k) ∧ ∀ k, r (k + 1) ≠ r k → f (r (k + 1)) < f (r k)

/-- An iteration contributes to the cumulative decrease only when accepted. -/
noncomputable def acceptedDecrease (S : Set ℕ) (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  open Classical in if k ∈ S then d k else 0

/-- The acceptance ratio (10.1.3), the maximum of the historical and current ratios. -/
noncomputable def nonmonotoneRatio (S : Set ℕ) (f trial d : ℕ → ℝ) (r k : ℕ) : ℝ :=
  max ((f r - trial k) / ((∑ i ∈ Finset.Ico r k, acceptedDecrease S d i) + d k))
    ((f k - trial k) / d k)

/-- Lemma 10.1.1. Under the model decrease condition AA.1, the nonmonotone
acceptance rule yields a bound on the sum of decreases over successful iterations.
Here `f` and `trial` are the objective values at the iterates and trial points,
`d` is predicted reduction, and `g` is the gradient norm. -/
theorem lemma_10_1_1 (S : Set ℕ) (f trial d g β Δ : ℕ → ℝ) (r : ℕ → ℕ)
    {η κ : ℝ} (hη : 0 < η) (hr : ∀ k, r k ≤ k) (hd : ∀ k, 0 < d k)
    (haa : ∀ k, κ * (g k * min (g k / β k) (Δ k)) ≤ d k)
    (hs : ∀ k ∈ S, η ≤ nonmonotoneRatio S f trial d (r k) k)
    (haccept : ∀ k ∈ S, f (k + 1) = trial k)
    (hreject : ∀ k ∉ S, f (k + 1) = f k) (k : ℕ) :
    η * κ * (∑ i ∈ Finset.range (k + 1),
      acceptedDecrease S (fun j ↦ g j * min (g j / β j) (Δ j)) i) ≤ f 0 - f (k + 1) := by
  classical
  let c (i : ℕ) := acceptedDecrease S (fun j ↦ g j * min (g j / β j) (Δ j)) i
  have hcost (i : ℕ) : κ * c i ≤ acceptedDecrease S d i := by
    by_cases hi : i ∈ S
    · simpa [c, acceptedDecrease, hi] using haa i
    · simp [c, acceptedDecrease, hi]
  have hpos (a j : ℕ) :
      0 < (∑ i ∈ Finset.Ico a j, acceptedDecrease S d i) + d j := by
    apply add_pos_of_nonneg_of_pos _ (hd j)
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i ∈ S
    · simpa [acceptedDecrease, hi] using (hd i).le
    · simp [acceptedDecrease, hi]
  have hsum (a j : ℕ) :
      (∑ i ∈ Finset.Ico a j, η * κ * c i) ≤
        η * (∑ i ∈ Finset.Ico a j, acceptedDecrease S d i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hcost i) hη.le
  have hstep (j : ℕ) : ∃ a ≤ j,
      (∑ i ∈ Finset.Ico a (j + 1), η * κ * c i) ≤ f a - f (j + 1) := by
    by_cases hj : j ∈ S
    · have h := hs j hj
      rw [nonmonotoneRatio, le_max_iff] at h
      rcases h with hh | hc
      · refine ⟨r j, hr j, (hsum (r j) (j + 1)).trans ?_⟩
        rw [Finset.sum_Ico_succ_top (hr j), acceptedDecrease, ite_eq_left hj, haccept j hj]
        exact (le_div_iff₀ (hpos (r j) j)).1 hh
      · refine ⟨j, le_rfl, (hsum j (j + 1)).trans ?_⟩
        simpa [Nat.Ico_succ_singleton, acceptedDecrease, hj, haccept j hj] using
          (le_div_iff₀ (hd j)).1 hc
    · refine ⟨j, le_rfl, ?_⟩
      simp [Nat.Ico_succ_singleton, c, acceptedDecrease, hj, hreject j hj]
  have h := Optimization.reference_decrease_sum f (fun i ↦ η * κ * c i) hstep (k + 1)
  rwa [← Finset.mul_sum] at h

end ConnGouldToint.Chapter10
