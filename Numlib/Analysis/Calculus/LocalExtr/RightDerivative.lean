import Numlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

/-!
# One-sided higher-order conditions for a local minimum

On the normalized right interval `[0,1]`, the first nonvanishing derivative of a smooth
function at a local minimum is nonnegative. The theorem works at every positive order,
with smoothness only on a neighborhood of each interval point and no global extension.
-/

open Set Filter Topology

/-- At a local minimum on a right-hand interval, the first nonvanishing derivative
has nonnegative value. Smoothness is only required near the interval points. -/
theorem IsLocalMinOn.iteratedDeriv_nonneg_of_lower_eq_zero {f : ℝ → ℝ} {k : ℕ}
    (hk : 0 < k) (hmin : IsLocalMinOn f (Icc 0 1) 0)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ k f t)
    (hzero : ∀ j, 0 < j → j < k → iteratedDeriv j f 0 = 0) :
    0 ≤ iteratedDeriv k f 0 := by
  cases k with
  | zero => omega
  | succ n =>
    by_contra hn
    have hneg : iteratedDeriv (n + 1) f 0 < 0 := lt_of_not_ge hn
    have hcont : ContinuousAt (iteratedDeriv (n + 1) f) 0 := by
      rw [iteratedDeriv_eq_equiv_comp]
      have hmap :=
        (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin (n + 1)) ℝ).symm.continuous.continuousAt
      exact hmap.comp ((hf 0 (by simp)).continuousAt_iteratedFDeriv le_rfl)
    have hmnear : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Icc (0 : ℝ) 1 → f 0 ≤ f t :=
      eventually_nhdsWithin_iff.mp hmin
    have hnear := hmnear.and (hcont.eventually (gt_mem_nhds hneg))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
    set y : ℝ := Min.min ε 1 / 2 with hydef
    have hy : 0 < y := by dsimp [y]; positivity
    have hye : y < ε := by dsimp [y]; linarith [min_le_left ε (1 : ℝ)]
    have hy1 : y ≤ 1 := by dsimp [y]; linarith [min_le_right ε (1 : ℝ)]
    have hne : (0 : ℝ) ≠ y := ne_of_lt hy
    have hsub : uIcc (0 : ℝ) y ⊆ Icc 0 1 :=
      uIcc_subset_Icc (by simp) ⟨hy.le, hy1⟩
    obtain ⟨ξ, hξ, hT⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul (n := n) hne
      (fun t ht => (hf t (hsub ht)).contDiffWithinAt)
    rw [taylorWithinEval_eq_sum_of_contDiffAt hne
      ((hf 0 (by simp)).of_le (by exact_mod_cast Nat.le_succ n))] at hT
    have hξnorm : dist ξ 0 < ε := by
      have h := abs_sub_left_of_mem_uIcc (Ioo_subset_Icc_self hξ)
      simp only [sub_zero, abs_of_pos hy] at h
      rw [Real.dist_eq, sub_zero]
      exact h.trans_lt hye
    have hξneg := (hball hξnorm).2
    have hminy := (hball (show dist y 0 < ε by
      rw [Real.dist_eq, sub_zero, abs_of_pos hy]; exact hye)).1 ⟨hy.le, hy1⟩
    have hsum : (∑ j ∈ Finset.range (n + 1),
        (y - 0) ^ j / j.factorial * iteratedDeriv j f 0) = f 0 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        rw [hzero j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.mp hj), mul_zero]
      · simp
    rw [hsum] at hT
    have hprod : iteratedDeriv (n + 1) f ξ * (y - 0) ^ (n + 1) / (n + 1).factorial < 0 :=
      div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos hξneg (pow_pos (by simpa using hy) (n + 1))) (by positivity)
    linarith
