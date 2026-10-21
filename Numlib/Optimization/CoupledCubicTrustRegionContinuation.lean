import Numlib.Optimization.CoupledCubic
import Numlib.Optimization.ConstrainedTrustRegion

/-!
# Feasible trust-region continuation for the coupled cubic

Global feasible-ball Taylor maximizers can be chosen in the nonnegative second and third
coordinate directions when both center coordinates exceed the radius. Their actual reduction
dominates the selected first- or second-order prediction.
-/

noncomputable section
namespace Optimization.CoupledCubic
open ConstrainedTrustRegion TaylorCriticality HigherOrderTrustRegion
open Set Metric

/-- The second-order decrement on the plane with first coordinate zero. -/
def planeDecrement (y z v w : ℝ) : ℝ :=
  z * y * v + y ^ 2 * w / 2 + z * v ^ 2 / 2 + y * v * w

/-- Negative changes in both coupled coordinates have nonpositive quadratic decrement
when neither change exceeds its corresponding center coordinate. -/
theorem planeDecrement_nonpos_of_nonpos {y z r t : ℝ}
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hry : r ≤ y) (htz : t ≤ z) : planeDecrement y z (-r) (-t) ≤ 0 := by
  by_cases hhalf : r ≤ y / 2
  · have h₁ : z * r * (-y + r / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hz hr) (by linarith)
    have h₂ : t * y * (r - y / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ht hy) (by linarith)
    dsimp [planeDecrement]
    nlinarith only [h₁, h₂]
  · have hcoef : 0 ≤ y * (r - y / 2) := mul_nonneg hy (by linarith)
    have hm := mul_le_mul_of_nonneg_right htz hcoef
    have hs : r ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hr hy).mpr hry
    have hzsq := mul_nonneg hz (sub_nonneg.mpr hs)
    dsimp [planeDecrement]
    nlinarith only [hm, hzsq]

/-- Zeroing negative coordinates dominates the full quadratic decrement on the whole ball. -/
theorem planeDecrement_le_positive {y z v w : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hv : -y ≤ v) (hw : -z ≤ w) :
    planeDecrement y z v w ≤ planeDecrement y z (max v 0) (max w 0) := by
  by_cases hv0 : 0 ≤ v <;> by_cases hw0 : 0 ≤ w
  · simp only [max_eq_left hv0, max_eq_left hw0, le_refl]
  · rw [max_eq_left hv0, max_eq_right (le_of_not_ge hw0)]
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hw0)
      (add_nonneg (div_nonneg (sq_nonneg y) (by norm_num : (0 : ℝ) ≤ 2)) (mul_nonneg hy hv0))
    dsimp [planeDecrement]
    nlinarith only [hm]
  · rw [max_eq_right (le_of_not_ge hv0), max_eq_left hw0]
    have hc : 0 ≤ y * (z + w) + z * v / 2 := by
      have h₁ := mul_nonneg hz (show 0 ≤ y + v / 2 by linarith)
      have h₂ := mul_nonneg hy hw0
      nlinarith only [h₁, h₂]
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hv0) hc
    dsimp [planeDecrement]
    nlinarith only [hm]
  · rw [max_eq_right (le_of_not_ge hv0), max_eq_right (le_of_not_ge hw0)]
    have h := planeDecrement_nonpos_of_nonpos hy hz
      (neg_nonneg.mpr (le_of_not_ge hv0)) (neg_nonneg.mpr (le_of_not_ge hw0))
      (show -v ≤ y by linarith) (show -w ≤ z by linarith)
    simpa [planeDecrement] using h

/-- Dropping the first coordinate and zeroing negative coupled coordinates. -/
def positiveDirection (d : Space) : Space := point 0 (max (d 1) 0) (max (d 2) 0)

/-- Clipping a direction does not increase its Euclidean norm. -/
theorem norm_positiveDirection_le (d : Space) : ‖positiveDirection d‖ ≤ ‖d‖ := by
  have h₁ : (max (d 1) 0) ^ 2 ≤ (d 1) ^ 2 := by
    by_cases h : 0 ≤ d 1
    · rw [max_eq_left h]
    · rw [max_eq_right (le_of_not_ge h)]; nlinarith [sq_nonneg (d 1)]
  have h₂ : (max (d 2) 0) ^ 2 ≤ (d 2) ^ 2 := by
    by_cases h : 0 ≤ d 2
    · rw [max_eq_left h]
    · rw [max_eq_right (le_of_not_ge h)]; nlinarith [sq_nonneg (d 2)]
  have hnorm := norm_sq_eq d
  have hpos := norm_point_sq 0 (max (d 1) 0) (max (d 2) 0)
  change ‖point 0 (max (d 1) 0) (max (d 2) 0)‖ ≤ ‖d‖
  nlinarith [norm_nonneg d, norm_nonneg (point 0 (max (d 1) 0) (max (d 2) 0)),
    sq_nonneg (d 0)]

/-- Clipping preserves feasibility of a direction at a nonnegative box center. -/
theorem positiveDirection_mem {y z R : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hx : point 0 y z ∈ box) {d : Space} (hd : d ∈ testingSet box (point 0 y z) R) :
    positiveDirection d ∈ testingSet box (point 0 y z) R := by
  obtain ⟨hend, hn⟩ := mem_testingSet.mp hd
  refine mem_testingSet.mpr ⟨?_, (norm_positiveDirection_le d).trans hn⟩
  have h₁ := (abs_le.mp (hend 1)).2
  have h₂ := (abs_le.mp (hend 2)).2
  have hy2 := (abs_le.mp (hx 1)).2
  have hz2 := (abs_le.mp (hx 2)).2
  rw [positiveDirection, point_add, zero_add, point_mem_box]
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [abs_of_nonneg (add_nonneg hy (le_max_right _ _))]
    by_cases h : 0 ≤ d 1
    · simpa only [max_eq_left h, PiLp.add_apply, point_one_coord] using h₁
    · simpa only [max_eq_right (le_of_not_ge h), add_zero, point_one_coord] using hy2
  · rw [abs_of_nonneg (add_nonneg hz (le_max_right _ _))]
    by_cases h : 0 ≤ d 2
    · simpa only [max_eq_left h, PiLp.add_apply, point_two_coord] using h₂
    · simpa only [max_eq_right (le_of_not_ge h), add_zero, point_two_coord] using hz2

/-- Clipping dominates either actual Taylor decrement over the whole feasible ball. -/
theorem taylorDecrement_le_positiveDirection {y z R : ℝ} (hR : 0 ≤ R)
    (hy : R ≤ y) (hz : R ≤ z) {d : Space}
    (hd : ‖d‖ ≤ R) {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ 2) :
    taylorDecrement objective j (point 0 y z) d ≤
      taylorDecrement objective j (point 0 y z) (positiveDirection d) := by
  have hy0 := hR.trans hy
  have hz0 := hR.trans hz
  have hv : -y ≤ d 1 := by
    have hh := (abs_le.mp ((abs_coordinate_le_norm d 1).trans hd)).1
    linarith
  have hw : -z ≤ d 2 := by
    have hh := (abs_le.mp ((abs_coordinate_le_norm d 2).trans hd)).1
    linarith
  interval_cases j
  · simp only [taylorDecrement_one, point_zero_coord, point_one_coord, point_two_coord,
      positiveDirection, neg_zero, zero_mul, zero_add]
    have h₁ := mul_le_mul_of_nonneg_left (le_max_left (d 1) 0) (mul_nonneg hz0 hy0)
    have h₂ := mul_le_mul_of_nonneg_left (le_max_left (d 2) 0) (sq_nonneg y)
    linarith
  · have hh := planeDecrement_le_positive hy0 hz0 hv hw
    simp only [taylorDecrement_two, point_zero_coord, point_one_coord, point_two_coord,
      positiveDirection, neg_zero, zero_mul, zero_add]
    dsimp [planeDecrement] at hh
    nlinarith [sq_nonneg (d 0)]

/-- Global feasible Taylor maxima admit nonnegative coupled directions and zero first component. -/
theorem exists_positive_maximizer {y z R : ℝ} (hR : 0 ≤ R)
    (hy : R ≤ y) (hz : R ≤ z) (hx : point 0 y z ∈ box)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ 2) :
    ∃ d ∈ testingSet box (point 0 y z) R,
      d 0 = 0 ∧ 0 ≤ d 1 ∧ 0 ≤ d 2 ∧
      taylorDecrement objective j (point 0 y z) d =
        gapOn (taylorDecrement objective j (point 0 y z)) (testingSet box (point 0 y z) R) := by
  obtain ⟨d, hd, he⟩ := exists_maximizer isClosed_box hx hR objective j
  let e := positiveDirection d
  have hem : e ∈ testingSet box (point 0 y z) R :=
    positiveDirection_mem (hR.trans hy) (hR.trans hz) hx hd
  have hle := taylorDecrement_le_positiveDirection hR hy hz (mem_testingSet.mp hd).2 hj hjq
  have hge := le_gapOn (isCompact_testingSet isClosed_box _ _)
    (continuous_taylorDecrement objective j (point 0 y z)).continuousOn hem
  refine ⟨e, hem, rfl, le_max_right _ _, le_max_right _ _, ?_⟩
  exact le_antisymm hge (he ▸ hle)

/-- Actual decrease dominates either selected Taylor prediction for every nonnegative
coupled direction with zero first component. -/
theorem reduction_ge_taylor {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    {d : Space} (hd0 : d 0 = 0) (hd1 : 0 ≤ d 1) (hd2 : 0 ≤ d 2)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ 2) :
    taylorDecrement objective j (point 0 y z) d ≤
      objective (point 0 y z) - objective (point 0 y z + d) := by
  rw [reduction_eq]
  have hrem := div_nonneg (mul_nonneg hd2 (sq_nonneg (d 1))) (by norm_num : (0 : ℝ) ≤ 2)
  interval_cases j
  · simp only [taylorDecrement_one, taylorDecrement_two, point_zero_coord, point_one_coord,
      point_two_coord, hd0, neg_zero, zero_mul, zero_add]
    have h₁ := mul_nonneg hz (sq_nonneg (d 1))
    have h₂ := mul_nonneg (mul_nonneg hy hd1) hd2
    linarith
  · linarith

end Optimization.CoupledCubic
