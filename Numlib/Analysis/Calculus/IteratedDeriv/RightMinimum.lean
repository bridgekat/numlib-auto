import Numlib.Analysis.Calculus.RootMultiplicity
import Mathlib.Tactic

/-!
# Finite necessary conditions at a right local minimum

A genuine right local minimum makes the first nonvanishing actual derivative
nonnegative. Local Taylor factorization supplies the sign argument with only
finite smoothness at the point.
-/

open Filter Set Topology

namespace ScalarOptimality

/-- Right local minimality and vanishing lower jets force the next actual derivative
to be nonnegative. -/
theorem iteratedDeriv_nonneg_of_right_min {g : ℝ → ℝ} {n : ℕ} {a : ℝ}
    (hn : 0 < n) (hg : ContDiffAt ℝ n g a)
    (hmin : ∀ᶠ t in 𝓝[>] a, g a ≤ g t)
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
  have hlocal : ∀ᶠ t in 𝓝[>] a, H t < 0 :=
    (hH.continuousAt.eventually (gt_mem_nhds hHneg)).filter_mono nhdsWithin_le_nhds
  have he : ∀ᶠ t in 𝓝[>] a, H t < 0 ∧ g a ≤ g t ∧ a < t :=
    hlocal.and (hmin.and self_mem_nhdsWithin)
  obtain ⟨t, htH, htmin, ht⟩ := he.exists
  have hfneg : F t < 0 := by
    rw [hfactor]
    exact mul_neg_of_pos_of_neg (pow_pos (sub_pos.mpr ht) _) htH
  change g t - g a < 0 at hfneg
  linarith
end ScalarOptimality
