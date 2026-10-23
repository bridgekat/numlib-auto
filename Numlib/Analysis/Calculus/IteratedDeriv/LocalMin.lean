import Numlib.Analysis.Calculus.RootMultiplicity
import Mathlib.Tactic

/-!
# The first nonvanishing jet at a local minimum

A negative first nonzero derivative would give a negative continuous factor in
the local Taylor factorization. Positive displacements then contradict local
minimality. The argument uses only finite smoothness at the point.
-/

namespace ScalarOptimality
open Filter

/-- At a local minimum, vanishing lower positive-order derivatives force the next actual
derivative to be nonnegative. -/
theorem iteratedDeriv_nonneg_of_isLocalMin {g : ℝ → ℝ} {n : ℕ} {a : ℝ}
    (hn : 0 < n) (hg : ContDiffAt ℝ n g a) (hmin : IsLocalMin g a)
    (hzero : ∀ i, 0 < i → i < n → iteratedDeriv i g a = 0) :
    0 ≤ iteratedDeriv n g a := by
  by_contra hh
  have hneg : iteratedDeriv n g a < 0 := lt_of_not_ge hh
  let F : ℝ → ℝ := fun t => g t - g a
  have hF : ContDiffAt ℝ n F a := hg.sub contDiffAt_const
  have hD (i : ℕ) (hi : 0 < i) (hin : i ≤ n) :
      iteratedDeriv i F a = iteratedDeriv i g a := by
    change iteratedDeriv i (g - fun _ => g a) a = _
    rw [iteratedDeriv_sub (hg.of_le (by exact_mod_cast hin)) contDiffAt_const]
    simp [iteratedDeriv_const, hi.ne']
  have hroot : IsRootOfMultiplicity F a n := by
    refine ⟨?_, ?_⟩
    · intro i hi
      by_cases h : i = 0
      · subst i; simp [F]
      · rw [hD i (Nat.pos_of_ne_zero h) hi.le]
        exact hzero i (Nat.pos_of_ne_zero h) hi
    · rw [hD n hn le_rfl]
      exact hneg.ne
  obtain ⟨H, hH, hH0, hfactor⟩ :=
    hroot.exists_eq_pow_mul (n := 0) (by simpa using hF)
  have hHneg : H a < 0 := by
    rw [hH0, hD n hn le_rfl]
    exact div_neg_of_neg_of_pos hneg (by positivity)
  have he : ∀ᶠ t in nhds a, H t < 0 ∧ g a ≤ g t :=
    (hH.continuousAt.eventually (gt_mem_nhds hHneg)).and hmin
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp he
  have ht : 0 < r / 2 := by positivity
  have hdist : dist (a + r / 2) a < r := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos ht]
    linarith
  have hbound := hb hdist
  have hfneg : F (a + r / 2) < 0 := by
    rw [hfactor]
    simp only [add_sub_cancel_left]
    exact mul_neg_of_pos_of_neg (by positivity) hbound.1
  change g (a + r / 2) - g a < 0 at hfneg
  linarith [hbound.2]
end ScalarOptimality
