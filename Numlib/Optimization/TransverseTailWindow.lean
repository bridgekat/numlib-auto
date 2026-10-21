import Numlib.Optimization.TransversePrelude
import Numlib.Optimization.TransverseTailTrial

/-!
# A common interval for vertical tail trials

The ordinate reached by the transverse injection starts a single interval on which all
prescribed vertical trials satisfy the same slope and curvature bounds. The integer
length defined here measures available vertical steps; it does not count oracle calls.
-/

noncomputable section
namespace Optimization.TransverseTailWindow
open TransverseObjective TransversePrelude

/-- The ordinate reached by the prescribed transverse injection at the first crossing. -/
def injectionOrdinate (ε : ℝ) (hε : 0 < ε) : ℝ :=
  ordinate (crossingIndex ε hε) + 4 * ε

/-- The injected ordinate stays beyond seventeen. -/
theorem seventeen_le_injectionOrdinate {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 65536) : 17 ≤ injectionOrdinate ε hε := by
  unfold injectionOrdinate
  linarith [seventeen_le_crossing hε hsmall]

/-- The injection loses less than one quarter of the crossing's lower slope estimate. -/
theorem injection_slope_lower {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536) :
    ε / 4 < slope (injectionOrdinate ε hε) := by
  have hw := crossing_window hε hsmall
  have hl := slope_short_increment_lower hw.2.2
    (show 0 ≤ 4 * ε by positivity) (show 4 * ε ≤ 1 by linarith)
  change (16 / 17 : ℝ) ^ 2 * slope (ordinate (crossingIndex ε hε)) ≤
    slope (injectionOrdinate ε hε) at hl
  nlinarith

/-- Doubling a positive tail ordinate divides its slope by less than three. -/
theorem slope_double_lower {Y : ℝ} (hY : 1 ≤ Y) :
    TransversePrelude.slope Y / 3 < TransversePrelude.slope (2 * Y) := by
  have hfactor : (1 / 3 : ℝ) < (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hp : 0 ≤ (2 : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hs : ((2 : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = (1 / 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [Real.rpow_neg, Real.rpow_natCast]
    nlinarith
  rw [slope_eq hY, slope_eq (show 1 ≤ 2 * Y by linarith),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ Y)]
  have hp := Real.rpow_pos_of_pos (show 0 < Y by linarith) (-(3 / 2 : ℝ))
  nlinarith [mul_lt_mul_of_pos_right hfactor hp]

/-- Every point of the common doubled interval satisfies the genuine tail-trial conditions. -/
theorem conditions {ε y : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536)
    (hlo : injectionOrdinate ε hε ≤ y) (hhi : y ≤ 2 * injectionOrdinate ε hε) :
    TransverseTailTrial.Conditions ε y := by
  have hY := seventeen_le_injectionOrdinate hε hsmall
  have hy : 1 ≤ y := by linarith
  have hu := one_le_ordinate (crossingIndex ε hε)
  have huy : ordinate (crossingIndex ε hε) ≤ y := by
    unfold injectionOrdinate at hlo
    linarith
  refine ⟨hε, hsmall, hy, ?_, ?_, ?_⟩
  · have hm := antitoneOn_slope hy (show 1 ≤ 2 * injectionOrdinate ε hε by linarith) hhi
    have hs := slope_double_lower (show 1 ≤ injectionOrdinate ε hε by linarith)
    have hl := injection_slope_lower hε hsmall
    change ε / 12 < slope y
    linarith
  · exact (antitoneOn_slope hu hy huy).trans (slope_crossingIndex_le hε)
  · exact (InverseSqrtTail.antitoneOn_second hu hy huy).trans (second_crossing_le hε hsmall)

/-- The number of full vertical increments available before doubling the injected ordinate. -/
def tailCount (ε : ℝ) (hε : 0 < ε) : ℕ := ⌊injectionOrdinate ε hε / (8 * ε)⌋₊

/-- The ordinate after a specified number of prescribed vertical increments. -/
def tailOrdinate (ε : ℝ) (hε : 0 < ε) (j : ℕ) : ℝ :=
  injectionOrdinate ε hε + j * (8 * ε)

/-- The initial tail ordinate is the injection endpoint. -/
@[simp] theorem tailOrdinate_zero (ε : ℝ) (hε : 0 < ε) :
    tailOrdinate ε hε 0 = injectionOrdinate ε hε := by simp [tailOrdinate]

/-- The tail ordinate recurrence adds exactly the prescribed vertical displacement. -/
@[simp] theorem tailOrdinate_succ (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    tailOrdinate ε hε (j + 1) = tailOrdinate ε hε j + 8 * ε := by
  simp [tailOrdinate, Nat.cast_add]
  ring

/-- Every ordinal index through the full tail count lies in the common doubled interval. -/
theorem tailOrdinate_mem {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536)
    {j : ℕ} (hj : j ≤ tailCount ε hε) :
    injectionOrdinate ε hε ≤ tailOrdinate ε hε j ∧
      tailOrdinate ε hε j ≤ 2 * injectionOrdinate ε hε := by
  have hY := seventeen_le_injectionOrdinate hε hsmall
  have hf := Nat.floor_le (show 0 ≤ injectionOrdinate ε hε / (8 * ε) by positivity)
  change (tailCount ε hε : ℝ) ≤ injectionOrdinate ε hε / (8 * ε) at hf
  have hjr : (j : ℝ) ≤ tailCount ε hε := by exact_mod_cast hj
  have hm := (le_div_iff₀ (show 0 < 8 * ε by positivity)).mp (hjr.trans hf)
  unfold tailOrdinate
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · linarith

/-- All tail starts and the final endpoint have the same actual trial bounds. -/
theorem tailOrdinate_conditions {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536)
    {j : ℕ} (hj : j ≤ tailCount ε hε) :
    TransverseTailTrial.Conditions ε (tailOrdinate ε hε j) :=
  conditions hε hsmall (tailOrdinate_mem hε hsmall hj).1
    (tailOrdinate_mem hε hsmall hj).2

/-- The available vertical length is at least half the unfloored length. -/
theorem tailCount_lower {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536) :
    injectionOrdinate ε hε / (16 * ε) ≤ (tailCount ε hε : ℝ) := by
  have hY := seventeen_le_injectionOrdinate hε hsmall
  have hr : 2 ≤ injectionOrdinate ε hε / (8 * ε) := by
    apply (le_div_iff₀ (show 0 < 8 * ε by positivity)).mpr
    linarith
  have hf := Nat.lt_floor_add_one (injectionOrdinate ε hε / (8 * ε))
  change injectionOrdinate ε hε / (8 * ε) < (tailCount ε hε : ℝ) + 1 at hf
  have he : injectionOrdinate ε hε / (16 * ε) =
      (injectionOrdinate ε hε / (8 * ε)) / 2 := by ring
  rw [he]
  linarith

/-- The prescribed vertical tail contains at least one full increment. -/
theorem tailCount_pos {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536) :
    0 < tailCount ε hε := by
  apply Nat.floor_pos.mpr
  apply (le_div_iff₀ (show 0 < 8 * ε by positivity)).mpr
  have hY := seventeen_le_injectionOrdinate hε hsmall
  linarith

/-- A tail step adds the actual prescribed displacement to the full Euclidean point. -/
theorem point_tailOrdinate_succ (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    point (2 * ε / 3) (tailOrdinate ε hε (j + 1)) =
      point (2 * ε / 3) (tailOrdinate ε hε j) + TransverseTailTrial.step ε := by
  simp [TransverseTailTrial.step, tailOrdinate_succ]

/-- Throughout the common interval the actual gradient remains below tolerance. -/
theorem tailOrdinate_norm_fderiv_lt {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 65536) {j : ℕ} (hj : j ≤ tailCount ε hε) :
    ‖fderiv ℝ objective (point (2 * ε / 3) (tailOrdinate ε hε j))‖ < ε :=
  TransverseTailTrial.norm_fderiv_lt_epsilon (tailOrdinate_conditions hε hsmall hj)

end Optimization.TransverseTailWindow
