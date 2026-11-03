import Numlib.Optimization.ModelBased.ReferenceDecrease
import NumlibSurface.ConnGouldToint.Chapter06.Section04
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

open Chapter06 in
/-- Theorem 10.1.2. The nonmonotone ratio dominates the current reduction ratio,
so the small-radius acceptance bound also prevents radius contraction here. -/
theorem theorem_10_1_2 {E : Type*} [NormedAddCommGroup E] {P : BTRParams}
    {f m : E → ℝ} {x s g : E} {β Δ Δ' κ C : ℝ}
    (S : Set ℕ) (values trial d : ℕ → ℝ) (r k : ℕ)
    (hvalues : values k = f x) (htrial : trial k = f (x + s)) (hd : d k = m x - m (x + s))
    (hβ : 0 < β) (hβC : β ≤ C) (hΔ : 0 < Δ) (hg : g ≠ 0)
    (hval : f x = m x) (hdec : HasSufficientModelDecrease m x s g β Δ κ)
    (herr : |f (x + s) - m (x + s)| ≤ C * Δ ^ 2)
    (hsmall : Δ ≤ κ * ‖g‖ * (1 - P.η₂) / C)
    (hupdate : BTRRadiusUpdate P (nonmonotoneRatio S values trial d r k) Δ Δ') :
    P.η₂ ≤ nonmonotoneRatio S values trial d r k ∧ Δ ≤ Δ' := by
  have hcurrent : P.η₂ ≤ btrRatio f m x s :=
    btrRatio_ge_eta₂_of_small_radius hβ hβC hΔ hg hval hdec herr hsmall
  have hdom : btrRatio f m x s ≤ nonmonotoneRatio S values trial d r k := by
    simp only [nonmonotoneRatio, hvalues, htrial, hd, btrRatio, Optimization.reductionRatio]
    exact le_max_right _ _
  exact ⟨hcurrent.trans hdom, hupdate.very_successful (hcurrent.trans hdom)⟩

end ConnGouldToint.Chapter10
