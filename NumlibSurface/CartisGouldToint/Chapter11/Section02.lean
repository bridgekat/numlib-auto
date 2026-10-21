import Numlib.Optimization.StepScaledUpdates
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Chapter 11, Section 2: practical parameter updates

The radius update uses the actual step length on rejection; its lower bound therefore differs
from a radius-scaled theoretical update. Power calibration is a suggested parameter choice,
not a theorem guaranteeing algorithmic efficiency.
-/

noncomputable section
namespace CartisGouldToint.Chapter11.Section02

/-- Acceptance thresholds and the contraction/expansion factors for practical updates. -/
abbrev PracticalParameters := Optimization.StepScaledUpdates.Parameters

/-- Practical trust-region update (11.2.1), with the actual trial-step norm. -/
def practicalTrustRegionUpdate {n : ℕ} (p : PracticalParameters) (delta : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) (rho : ℝ) : ℝ :=
  Optimization.StepScaledUpdates.radius p delta ‖s‖ rho

/-- Practical regularization update (11.2.2), with the lower weight safeguard. -/
def practicalRegularizationUpdate (p : PracticalParameters) (minimum sigma rho : ℝ) : ℝ :=
  Optimization.StepScaledUpdates.weight p minimum sigma rho

/-- The very successful radius branch is exactly the source maximum. -/
@[simp] theorem practicalTrustRegionUpdate_of_very_successful {n : ℕ}
    (p : PracticalParameters) (delta : ℝ) (s : EuclideanSpace ℝ (Fin n)) (rho : ℝ)
    (h : p.eta2 ≤ rho) :
    practicalTrustRegionUpdate p delta s rho = max delta (p.grow * ‖s‖) :=
  Optimization.StepScaledUpdates.radius_of_very_successful p delta ‖s‖ rho h

/-- Successful trials below the upper threshold retain the radius. -/
@[simp] theorem practicalTrustRegionUpdate_of_successful {n : ℕ}
    (p : PracticalParameters) (delta : ℝ) (s : EuclideanSpace ℝ (Fin n)) (rho : ℝ)
    (h₁ : p.eta1 ≤ rho) (h₂ : rho < p.eta2) :
    practicalTrustRegionUpdate p delta s rho = delta :=
  Optimization.StepScaledUpdates.radius_of_successful p delta ‖s‖ rho h₁ h₂

/-- The rejected branch contracts the actual step norm, rather than the current radius. -/
@[simp] theorem practicalTrustRegionUpdate_of_rejected {n : ℕ}
    (p : PracticalParameters) (delta : ℝ) (s : EuclideanSpace ℝ (Fin n)) (rho : ℝ)
    (h : rho < p.eta1) : practicalTrustRegionUpdate p delta s rho = p.shrink * ‖s‖ :=
  Optimization.StepScaledUpdates.radius_of_rejected p delta ‖s‖ rho h

/-- Positive radii and nonzero trial steps give positive updated radii. -/
theorem practicalTrustRegionUpdate_pos {n : ℕ} (p : PracticalParameters)
    {delta : ℝ} (hd : 0 < delta) {s : EuclideanSpace ℝ (Fin n)} (hs : s ≠ 0) (rho : ℝ) :
    0 < practicalTrustRegionUpdate p delta s rho :=
  Optimization.StepScaledUpdates.radius_pos p hd (norm_pos_iff.mpr hs) rho

/-- Feasibility bounds the new radius by the current radius times the expansion factor. -/
theorem practicalTrustRegionUpdate_le {n : ℕ} (p : PracticalParameters)
    {delta : ℝ} {s : EuclideanSpace ℝ (Fin n)} (hs : ‖s‖ ≤ delta) (rho : ℝ) :
    practicalTrustRegionUpdate p delta s rho ≤ p.grow * delta :=
  Optimization.StepScaledUpdates.radius_le p (norm_nonneg _) hs rho

/-- The very successful regularization branch uses the lower safeguard. -/
@[simp] theorem practicalRegularizationUpdate_of_very_successful (p : PracticalParameters)
    (minimum sigma rho : ℝ) (h : p.eta2 ≤ rho) :
    practicalRegularizationUpdate p minimum sigma rho = max minimum (p.shrink * sigma) :=
  Optimization.StepScaledUpdates.weight_of_very_successful p minimum sigma rho h

/-- The intermediate regularization branch leaves the weight unchanged. -/
@[simp] theorem practicalRegularizationUpdate_of_successful (p : PracticalParameters)
    (minimum sigma rho : ℝ) (h₁ : p.eta1 ≤ rho) (h₂ : rho < p.eta2) :
    practicalRegularizationUpdate p minimum sigma rho = sigma :=
  Optimization.StepScaledUpdates.weight_of_successful p minimum sigma rho h₁ h₂

/-- Rejection multiplies the regularization weight by the expansion factor. -/
@[simp] theorem practicalRegularizationUpdate_of_rejected (p : PracticalParameters)
    (minimum sigma rho : ℝ) (h : rho < p.eta1) :
    practicalRegularizationUpdate p minimum sigma rho = p.grow * sigma :=
  Optimization.StepScaledUpdates.weight_of_rejected p minimum sigma rho h

/-- The weight safeguard is invariant under the practical update. -/
theorem minimum_le_practicalRegularizationUpdate (p : PracticalParameters)
    {minimum sigma : ℝ} (hm : 0 ≤ minimum) (hms : minimum ≤ sigma) (rho : ℝ) :
    minimum ≤ practicalRegularizationUpdate p minimum sigma rho :=
  Optimization.StepScaledUpdates.minimum_le_weight p hm hms rho

/-- Positive regularization weights remain positive even if the safeguard is zero. -/
theorem practicalRegularizationUpdate_pos (p : PracticalParameters)
    {sigma : ℝ} (hs : 0 < sigma) (minimum rho : ℝ) :
    0 < practicalRegularizationUpdate p minimum sigma rho :=
  Optimization.StepScaledUpdates.weight_pos p hs minimum rho

/-- The suggested large-weight calibration (11.2.6), as a parameter definition. -/
def practicalPowerCalibration (p : PracticalParameters) (r : ℝ) : ℝ × ℝ :=
  Optimization.StepScaledUpdates.powerCalibration p.shrink p.grow r

/-- The calibration gives the two reciprocal powers displayed in the source. -/
@[simp] theorem practicalPowerCalibration_eq (p : PracticalParameters) (r : ℝ) :
    practicalPowerCalibration p r = ((p.grow ^ (r - 1))⁻¹, (p.shrink ^ (r - 1))⁻¹) :=
  Optimization.StepScaledUpdates.powerCalibration_eq p.shrink p.grow r p.shrink_pos.le
    (zero_lt_one.trans p.one_lt_grow).le

/-- For regularization order above one, the calibrated factors have the required directions. -/
theorem practicalPowerCalibration_bounds (p : PracticalParameters) {r : ℝ} (hr : 1 < r) :
    0 < (practicalPowerCalibration p r).1 ∧ (practicalPowerCalibration p r).1 < 1 ∧
      1 < (practicalPowerCalibration p r).2 :=
  Optimization.StepScaledUpdates.powerCalibration_bounds p hr

end CartisGouldToint.Chapter11.Section02
