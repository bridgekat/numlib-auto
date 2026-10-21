import Numlib.Optimization.TransverseTailWindow
import Numlib.Optimization.TransverseInjection

/-!
# The actual three-phase accepted-point schedule

The fixed initial point follows the actual global-minimum prelude until its first slope
crossing, takes one transverse injection, and traverses the whole common vertical tail
window. Every displacement reaches the next full Euclidean point. All phase-specific
analytic conditions hold at their actual starts, and the tail conditions include the final
endpoint. These accepted indices carry no assertion about oracle query counts.
-/

noncomputable section
namespace Optimization.TransverseAcceptedSchedule
open TransverseObjective TransversePrelude

/-- The total number of prescribed accepted steps, including the single injection. -/
def totalCount (ε : ℝ) (hε : 0 < ε) : ℕ :=
  crossingIndex ε hε + 1 + TransverseTailWindow.tailCount ε hε

/-- The actual full Euclidean point at each accepted index. -/
def pointAt (ε : ℝ) (hε : 0 < ε) (n : ℕ) : Plane :=
  if n ≤ crossingIndex ε hε then point 0 (ordinate n)
  else point (2 * ε / 3) (TransverseTailWindow.tailOrdinate ε hε
    (n - crossingIndex ε hε - 1))

/-- The actual displacement at each accepted index, according to its phase. -/
def stepAt (ε : ℝ) (hε : 0 < ε) (n : ℕ) : Plane :=
  if n < crossingIndex ε hε then step (ordinate n)
  else if n = crossingIndex ε hε then TransverseInjection.step ε
  else TransverseTailTrial.step ε

/-- The complete prelude, including the crossing point, has its original ordinate. -/
theorem pointAt_prelude {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : n ≤ crossingIndex ε hε) : pointAt ε hε n = point 0 (ordinate n) := by
  simp [pointAt, hn]

/-- Every point after the crossing is the actual indexed tail point. -/
theorem pointAt_tail {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : crossingIndex ε hε < n) :
    pointAt ε hε n = point (2 * ε / 3)
      (TransverseTailWindow.tailOrdinate ε hε (n - crossingIndex ε hε - 1)) := by
  simp [pointAt, not_le.mpr hn]

/-- Counting tail indices from the injection endpoint removes all truncated subtraction. -/
theorem pointAt_tail_index (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    pointAt ε hε (crossingIndex ε hε + 1 + j) =
      point (2 * ε / 3) (TransverseTailWindow.tailOrdinate ε hε j) := by
  rw [pointAt_tail hε (by omega)]
  congr 2
  omega

/-- The actual prescribed prelude displacement is selected strictly before the crossing. -/
theorem stepAt_prelude {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : n < crossingIndex ε hε) : stepAt ε hε n = step (ordinate n) := by
  simp [stepAt, hn]

/-- The unique crossing step is the prescribed transverse injection. -/
@[simp] theorem stepAt_injection (ε : ℝ) (hε : 0 < ε) :
    stepAt ε hε (crossingIndex ε hε) = TransverseInjection.step ε := by
  simp [stepAt]

/-- Every step after the injection has the prescribed vertical displacement. -/
theorem stepAt_tail {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : crossingIndex ε hε < n) : stepAt ε hε n = TransverseTailTrial.step ε := by
  simp [stepAt, not_lt.mpr hn.le, Nat.ne_of_gt hn]

/-- The schedule starts at the fixed tolerance-independent point. -/
@[simp] theorem pointAt_zero (ε : ℝ) (hε : 0 < ε) :
    pointAt ε hε 0 = point 0 1 := by
  rw [pointAt_prelude hε (Nat.zero_le _), ordinate_zero]

/-- The injection endpoint is precisely the initial point of the common tail window. -/
theorem pointAt_injection_endpoint (ε : ℝ) (hε : 0 < ε) :
    pointAt ε hε (crossingIndex ε hε + 1) =
      point (2 * ε / 3) (TransverseTailWindow.injectionOrdinate ε hε) := by
  simpa using pointAt_tail_index ε hε 0

/-- The final accepted point is the actual final ordinate of the full tail window. -/
theorem pointAt_totalCount (ε : ℝ) (hε : 0 < ε) :
    pointAt ε hε (totalCount ε hε) = point (2 * ε / 3)
      (TransverseTailWindow.tailOrdinate ε hε (TransverseTailWindow.tailCount ε hε)) :=
  pointAt_tail_index ε hε _

/-- The injection and its endpoint both occur within the accepted schedule. -/
theorem crossingIndex_lt_totalCount (ε : ℝ) (hε : 0 < ε) :
    crossingIndex ε hε < totalCount ε hε := by
  unfold totalCount
  omega

/-- Every displacement before the endpoint reaches the next full Euclidean point. -/
theorem pointAt_succ {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : n < totalCount ε hε) :
    pointAt ε hε (n + 1) = pointAt ε hε n + stepAt ε hε n := by
  by_cases hpre : n < crossingIndex ε hε
  · rw [pointAt_prelude hε (by omega), pointAt_prelude hε hpre.le,
      stepAt_prelude hε hpre]
    exact point_ordinate_succ n
  · by_cases he : n = crossingIndex ε hε
    · subst n
      rw [pointAt_injection_endpoint, pointAt_prelude hε le_rfl, stepAt_injection]
      simp [TransverseInjection.step, TransverseTailWindow.injectionOrdinate]
    · have htail : crossingIndex ε hε < n := by omega
      rw [pointAt_tail hε (by omega), pointAt_tail hε htail, stepAt_tail hε htail]
      have hi : n + 1 - crossingIndex ε hε - 1 =
          (n - crossingIndex ε hε - 1) + 1 := by omega
      rw [hi]
      exact TransverseTailWindow.point_tailOrdinate_succ ε hε _

/-- Before the crossing, the genuine prelude gates hold at the actual accepted ordinate. -/
theorem prelude_conditions {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : n < crossingIndex ε hε) :
    1 ≤ ordinate n ∧ 2 * ε / 5 < slope (ordinate n) :=
  ⟨one_le_ordinate n, lt_slope_of_lt_crossingIndex hε hn⟩

/-- The actual crossing point satisfies every scalar gate of the transverse injection. -/
theorem injection_conditions {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536) :
    TransverseInjection.Conditions ε (ordinate (crossingIndex ε hε)) := by
  obtain ⟨hl, hu, _⟩ := crossing_window hε hsmall
  exact ⟨hε, hsmall, one_le_ordinate _, hl, hu, second_crossing_le hε hsmall⟩

/-- Each post-injection index through the final endpoint remains in the full tail window. -/
theorem tail_index_le {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : n ≤ totalCount ε hε) :
    n - crossingIndex ε hε - 1 ≤ TransverseTailWindow.tailCount ε hε := by
  unfold totalCount at hn
  omega

/-- Genuine tail-trial conditions hold at every later start and at the final endpoint. -/
theorem tail_conditions {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536) {n : ℕ}
    (hn : crossingIndex ε hε < n) (hN : n ≤ totalCount ε hε) :
    TransverseTailTrial.Conditions ε (pointAt ε hε n 1) := by
  rw [pointAt_tail hε hn, point_one_coord]
  exact TransverseTailWindow.tailOrdinate_conditions hε hsmall (tail_index_le hε hN)

/-- Every schedule point lies in the nonnegative quadratic strip and the slow tail. -/
theorem pointAt_geometry {ε : ℝ} (hε : 0 < ε) (hsmall : ε ≤ 1 / 65536) {n : ℕ}
    (hn : n ≤ totalCount ε hε) :
    0 ≤ pointAt ε hε n 0 ∧ pointAt ε hε n 0 ≤ 1 ∧ 1 ≤ pointAt ε hε n 1 := by
  by_cases hpre : n ≤ crossingIndex ε hε
  · rw [pointAt_prelude hε hpre]
    exact ⟨by simp, by simp, one_le_ordinate n⟩
  · have htail : crossingIndex ε hε < n := by omega
    have hc := tail_conditions hε hsmall htail hn
    rw [pointAt_tail hε htail]
    simp only [point_zero_coord, point_one_coord]
    refine ⟨by positivity, by linarith, ?_⟩
    simpa only [pointAt_tail hε htail, point_one_coord] using hc.tail

/-- Every actual post-injection point through the endpoint has gradient below tolerance. -/
theorem pointAt_norm_fderiv_lt_epsilon {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 65536) {n : ℕ} (hn : crossingIndex ε hε < n)
    (hN : n ≤ totalCount ε hε) : ‖fderiv ℝ objective (pointAt ε hε n)‖ < ε := by
  rw [pointAt_tail hε hn]
  exact TransverseTailWindow.tailOrdinate_norm_fderiv_lt hε hsmall (tail_index_le hε hN)

/-- Every actual point of the complete schedule has true gradient norm strictly below one. -/
theorem pointAt_norm_fderiv_lt_one {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 65536) {n : ℕ} (hn : n ≤ totalCount ε hε) :
    ‖fderiv ℝ objective (pointAt ε hε n)‖ < 1 := by
  by_cases hpre : n ≤ crossingIndex ε hε
  · rw [pointAt_prelude hε hpre, TransverseInjection.initial_slope_eq]
    have hs := slope_le_half (one_le_ordinate n)
    change -InverseSqrtTail.first (ordinate n) ≤ 1 / 2 at hs
    linarith
  · have hs := pointAt_norm_fderiv_lt_epsilon hε hsmall (by omega) hn
    linarith

/-- The actual objective derivative is nonzero at every point of the schedule. -/
theorem pointAt_fderiv_ne_zero {ε : ℝ} (hε : 0 < ε)
    (hsmall : ε ≤ 1 / 65536) {n : ℕ} (hn : n ≤ totalCount ε hε) :
    fderiv ℝ objective (pointAt ε hε n) ≠ 0 := by
  have hy := (pointAt_geometry hε hsmall hn).2.2
  rw [← point_coords (pointAt ε hε n)]
  exact TransverseCubicModel.fderiv_objective_ne_zero_of_tail _ hy

end Optimization.TransverseAcceptedSchedule
