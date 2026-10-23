import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuity and zero derivatives from power growth

Positive power growth implies continuity at the origin. Superlinear power
growth implies an actual zero Fréchet derivative, by a little-o estimate.
-/

open Filter Topology Asymptotics
section Bound
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Positive power growth at the origin makes a normed-space map continuous there. -/
theorem continuousAt_zero_of_norm_le_rpow {g : E → F} {C a : ℝ} (ha : 0 < a)
    (hbound : ∀ x, ‖g x‖ ≤ C * ‖x‖ ^ a) : ContinuousAt g 0 := by
  have hg0 : g 0 = 0 := norm_eq_zero.mp (le_antisymm
    (by simpa only [norm_zero, Real.zero_rpow ha.ne', mul_zero] using hbound 0)
    (norm_nonneg _))
  rw [ContinuousAt, hg0, tendsto_zero_iff_norm_tendsto_zero]
  have hc : Tendsto (fun x : E => C * ‖x‖ ^ a) (𝓝 0) (𝓝 0) := by
    have hh := ((continuousAt_const : ContinuousAt (fun _ : E => C) 0).mul
      (continuousAt_id.norm.rpow_const (Or.inr ha.le))).tendsto
    convert! hh using 1
    simp only [Pi.mul_apply, id_eq, norm_zero, Real.zero_rpow ha.ne', mul_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun x => norm_nonneg _) hbound

/-- Superlinear norm growth gives a zero Fréchet derivative at the origin. -/
theorem hasFDerivAt_zero_of_norm_le_rpow {g : E → F} {C a : ℝ} (ha : 1 < a)
    (hbound : ∀ x, ‖g x‖ ≤ C * ‖x‖ ^ a) : HasFDerivAt g (0 : E →L[ℝ] F) 0 := by
  have ha0 : a ≠ 0 := ne_of_gt (zero_lt_one.trans ha)
  have hg0 : g 0 = 0 := norm_eq_zero.mp (le_antisymm
    (by simpa only [norm_zero, Real.zero_rpow ha0, mul_zero] using hbound 0)
    (norm_nonneg _))
  apply HasFDerivAt.of_isLittleO
  simp only [hg0, sub_zero, zero_apply]
  have hbig : g =O[𝓝 0] (fun x : E => ‖x‖ ^ a) := by
    refine isBigO_of_le' (f := g) (g := fun x : E => ‖x‖ ^ a) (c := C) (𝓝 0) ?_
    intro x
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) a)] using hbound x
  have hlittle : (fun x : E => ‖x‖ ^ a) =o[𝓝 0] (fun x : E => x) := by
    have h2 : 0 < a - 1 := sub_pos.mpr ha
    calc (fun x : E => ‖x‖ ^ a) = (fun x : E => ‖x‖ * ‖x‖ ^ (a - 1)) := by
          ext x
          rw [← Real.rpow_one_add' (norm_nonneg x) (by positivity)]
          congr 1
          ring
      _ =o[𝓝 0] (fun x : E => ‖x‖ * 1) := by
          refine (isBigO_refl _ _).mul_isLittleO ((isLittleO_const_iff (by simp)).mpr ?_)
          have hh := (continuousAt_id (x := (0 : E)).norm.rpow_const (Or.inr h2.le)).tendsto
          simpa only [id_eq, norm_zero, Real.zero_rpow h2.ne'] using hh
      _ =O[𝓝 0] (fun x : E => x) := by
          simp only [mul_one]
          exact (isBigO_refl (fun x : E => x) (𝓝 0)).norm_left
  exact hbig.trans_isLittleO hlittle

end Bound

open Metric Set

section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A linear growth bound and a bounded derivative off the origin give a
global Lipschitz estimate, without differentiability at the origin. -/
theorem norm_sub_le_of_growth_and_fderiv_bound {g : E → F} {B C : ℝ}
    (hB : 0 ≤ B) (hg : ∀ x, ‖g x‖ ≤ B * ‖x‖)
    (hd : ∀ x : E, x ≠ 0 → DifferentiableAt ℝ g x)
    (hbound : ∀ x : E, x ≠ 0 → ‖fderiv ℝ g x‖ ≤ C) (x y : E) :
    ‖g x - g y‖ ≤ max (5 * B) C * ‖x - y‖ := by
  by_cases hnear : ‖x‖ ≤ 2 * ‖x - y‖
  · have hny : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      have hh := norm_sub_le x (x - y)
      simpa only [sub_sub_cancel] using hh
    have hsum : ‖g x - g y‖ ≤ 5 * B * ‖x - y‖ := by
      have hh := norm_sub_le (g x) (g y)
      have hx := hg x
      have hy := hg y
      nlinarith
    exact hsum.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · have hfar : 2 * ‖x - y‖ < ‖x‖ := lt_of_not_ge hnear
    have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (by positivity) hfar
    have hball : ∀ z ∈ ball x ‖x‖, z ≠ (0 : E) := by
      intro z hz hzero
      subst z
      exact (lt_irrefl ‖x‖) (by simpa only [mem_ball, dist_zero_left] using hz)
    have hb := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => hd z (hball z hz)) (fun z hz => hbound z (hball z hz))
      (convex_ball x ‖x‖) (show x ∈ ball x ‖x‖ by simpa using hxpos)
      (show y ∈ ball x ‖x‖ by
        rw [mem_ball, dist_comm, dist_eq_norm]
        linarith [norm_nonneg (x - y)])
    rw [norm_sub_rev (g y), norm_sub_rev y] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
end General
