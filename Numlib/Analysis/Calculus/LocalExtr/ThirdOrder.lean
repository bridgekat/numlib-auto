/-
Upstreaming candidate: higher-order necessary conditions for a scalar local extremum.
Natural home: Mathlib.Analysis.Calculus.LocalExtr.
-/
import Numlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

/-!
# Third derivatives at local minima

At a local minimum of a `C³` real function whose second derivative vanishes, its third
derivative vanishes as well. Taylor's Lagrange remainder excludes a negative third
derivative to the right; reflection excludes a positive one. Translation gives the result
at an arbitrary expansion point.
-/

open Set Filter Topology

/-- A third derivative at a local minimum cannot be negative when the second vanishes. -/
theorem IsLocalMin.iteratedDeriv_three_nonneg {f : ℝ → ℝ}
    (hmin : IsLocalMin f 0) (hf : ContDiff ℝ 3 f)
    (hsecond : iteratedDeriv 2 f 0 = 0) : 0 ≤ iteratedDeriv 3 f 0 := by
  by_contra hn
  have hneg : iteratedDeriv 3 f 0 < 0 := lt_of_not_ge hn
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), f 0 ≤ f t ∧ iteratedDeriv 3 f t < 0 :=
    hmin.and (((hf.continuous_iteratedDeriv 3 le_rfl).continuousAt).eventually
      (gt_mem_nhds hneg))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hy : (0 : ℝ) < ε / 2 := by positivity
  have hne : (0 : ℝ) ≠ ε / 2 := ne_of_lt hy
  obtain ⟨ξ, hξ, hT⟩ := exists_taylorWithinEval_add_iteratedDeriv_mul
    (n := 2) hne hf.contDiffOn
  rw [taylorWithinEval_eq_sum_of_contDiffAt hne
    (hf.contDiffAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))] at hT
  have hξnorm : dist ξ 0 < ε := by
    have h := abs_sub_left_of_mem_uIcc (Ioo_subset_Icc_self hξ)
    rw [Real.dist_eq, sub_zero]
    simp only [sub_zero, abs_of_pos hy] at h
    exact h.trans_lt (by linarith)
  have hξneg := (hball hξnorm).2
  have hminy := (hball (show dist (ε / 2) 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_of_pos hy]
    linarith)).1
  have hfirst : deriv f 0 = 0 := hmin.deriv_eq_zero
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    hfirst, hsecond] at hT
  have hprod : iteratedDeriv 3 f ξ * (ε / 2) ^ 3 / 6 < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hξneg (pow_pos hy 3)) (by norm_num)
  linarith

/-- At a local minimum, a vanishing second derivative forces the third derivative to vanish. -/
theorem IsLocalMin.iteratedDeriv_three_eq_zero_at_zero {f : ℝ → ℝ}
    (hmin : IsLocalMin f 0) (hf : ContDiff ℝ 3 f)
    (hsecond : iteratedDeriv 2 f 0 = 0) : iteratedDeriv 3 f 0 = 0 := by
  have hpos := hmin.iteratedDeriv_three_nonneg hf hsecond
  have hmneg : IsLocalMin (fun t => f (-t)) 0 := by
    simpa [Function.comp_def] using
      (show IsLocalMin f (- (0 : ℝ)) by simpa using hmin).comp_continuous
        (continuous_neg.continuousAt)
  have hfneg : ContDiff ℝ 3 (fun t => f (-t)) := hf.comp contDiff_neg
  have hsneg : iteratedDeriv 2 (fun t => f (-t)) 0 = 0 := by
    simpa [iteratedDeriv_comp_neg] using hsecond
  have hneg := hmneg.iteratedDeriv_three_nonneg hfneg hsneg
  simp [iteratedDeriv_comp_neg] at hneg
  linarith

/-- At any local minimum, a vanishing second derivative forces the third derivative to vanish. -/
theorem IsLocalMin.iteratedDeriv_three_eq_zero {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hf : ContDiff ℝ 3 f)
    (hsecond : iteratedDeriv 2 f x = 0) : iteratedDeriv 3 f x = 0 := by
  have hm : IsLocalMin (fun t : ℝ => f (x + t)) 0 := by
    simpa [Function.comp_def] using
      (show IsLocalMin f (x + (0 : ℝ)) by simpa using hmin).comp_continuous
        (g := fun t : ℝ => x + t) (b := 0)
        (continuous_const.add continuous_id).continuousAt
  have hg : ContDiff ℝ 3 (fun t : ℝ => f (x + t)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have hs : iteratedDeriv 2 (fun t : ℝ => f (x + t)) 0 = 0 := by
    simpa [iteratedDeriv_comp_const_add] using hsecond
  have heq := hm.iteratedDeriv_three_eq_zero_at_zero hg hs
  simpa [iteratedDeriv_comp_const_add] using heq

