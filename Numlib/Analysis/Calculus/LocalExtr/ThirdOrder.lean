/-
Upstreaming candidate: higher-order necessary conditions for a scalar local extremum.
Natural home: Mathlib.Analysis.Calculus.LocalExtr.
-/
import Numlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Numlib.Analysis.Calculus.LocalExtr.RightDerivative
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
  have hm : IsLocalMinOn f (Icc 0 1) 0 := hmin.filter_mono nhdsWithin_le_nhds
  apply hm.iteratedDeriv_nonneg_of_lower_eq_zero (by norm_num : 0 < 3)
    (fun _ _ => hf.contDiffAt)
  intro j hj hj3
  have hcases : j = 1 ∨ j = 2 := by omega
  rcases hcases with rfl | rfl
  · simpa [iteratedDeriv_one] using hmin.deriv_eq_zero
  · exact hsecond

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
