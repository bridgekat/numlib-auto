import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Step-scaled radius and regularization updates

Deterministic practical updates distinguish very successful, successful, and rejected trials.
A rejected radius is scaled from the actual step length, whereas a rejected regularization
weight is scaled from its current value.
-/

noncomputable section
namespace Optimization.StepScaledUpdates

/-- Ordered acceptance thresholds and contraction/expansion factors. -/
structure Parameters where
  eta1 : ℝ
  eta2 : ℝ
  shrink : ℝ
  grow : ℝ
  eta1_pos : 0 < eta1
  eta_le : eta1 ≤ eta2
  eta2_lt_one : eta2 < 1
  shrink_pos : 0 < shrink
  shrink_lt_one : shrink < 1
  one_lt_grow : 1 < grow

/-- A radius update using the actual trial step length in the outer branches. -/
def radius (p : Parameters) (delta length rho : ℝ) : ℝ :=
  if p.eta2 ≤ rho then max delta (p.grow * length)
  else if p.eta1 ≤ rho then delta else p.shrink * length

/-- A regularization update with a fixed lower safeguard. -/
def weight (p : Parameters) (minimum sigma rho : ℝ) : ℝ :=
  if p.eta2 ≤ rho then max minimum (p.shrink * sigma)
  else if p.eta1 ≤ rho then sigma else p.grow * sigma

/-- Very successful radius updates retain at least the current radius. -/
@[simp] theorem radius_of_very_successful (p : Parameters) (delta length rho : ℝ)
    (h : p.eta2 ≤ rho) : radius p delta length rho = max delta (p.grow * length) := by
  simp [radius, h]

/-- The intermediate radius branch leaves the radius unchanged. -/
@[simp] theorem radius_of_successful (p : Parameters) (delta length rho : ℝ)
    (h₁ : p.eta1 ≤ rho) (h₂ : rho < p.eta2) : radius p delta length rho = delta := by
  simp [radius, h₁, h₂.not_ge]

/-- Rejected trials scale the radius from their actual step length. -/
@[simp] theorem radius_of_rejected (p : Parameters) (delta length rho : ℝ)
    (h : rho < p.eta1) : radius p delta length rho = p.shrink * length := by
  simp [radius, h.not_ge, (h.trans_le p.eta_le).not_ge]

/-- Very successful trials decrease the weight, subject to the lower safeguard. -/
@[simp] theorem weight_of_very_successful (p : Parameters) (minimum sigma rho : ℝ)
    (h : p.eta2 ≤ rho) : weight p minimum sigma rho = max minimum (p.shrink * sigma) := by
  simp [weight, h]

/-- The intermediate weight branch leaves the weight unchanged. -/
@[simp] theorem weight_of_successful (p : Parameters) (minimum sigma rho : ℝ)
    (h₁ : p.eta1 ≤ rho) (h₂ : rho < p.eta2) : weight p minimum sigma rho = sigma := by
  simp [weight, h₁, h₂.not_ge]

/-- Rejected trials expand the current regularization weight. -/
@[simp] theorem weight_of_rejected (p : Parameters) (minimum sigma rho : ℝ)
    (h : rho < p.eta1) : weight p minimum sigma rho = p.grow * sigma := by
  simp [weight, h.not_ge, (h.trans_le p.eta_le).not_ge]

/-- A positive radius and nonzero step retain a positive practical radius. -/
theorem radius_pos (p : Parameters) {delta length : ℝ} (hd : 0 < delta)
    (hl : 0 < length) (rho : ℝ) : 0 < radius p delta length rho := by
  unfold radius
  split_ifs
  · exact hd.trans_le (le_max_left _ _)
  · exact hd
  · exact mul_pos p.shrink_pos hl

/-- Feasible steps make every practical radius update no larger than the expanded radius. -/
theorem radius_le (p : Parameters) {delta length : ℝ} (hl : 0 ≤ length)
    (hld : length ≤ delta) (rho : ℝ) : radius p delta length rho ≤ p.grow * delta := by
  have hd : 0 ≤ delta := hl.trans hld
  have hg : 0 ≤ p.grow := (zero_lt_one.trans p.one_lt_grow).le
  have hdelta : delta ≤ p.grow * delta := le_mul_of_one_le_left hd p.one_lt_grow.le
  unfold radius
  split_ifs
  · exact max_le hdelta (mul_le_mul_of_nonneg_left hld hg)
  · exact hdelta
  · exact (mul_le_of_le_one_left hl p.shrink_lt_one.le).trans (hld.trans hdelta)

/-- The regularization safeguard is retained by every branch. -/
theorem minimum_le_weight (p : Parameters) {minimum sigma : ℝ} (hm : 0 ≤ minimum)
    (hms : minimum ≤ sigma) (rho : ℝ) : minimum ≤ weight p minimum sigma rho := by
  unfold weight
  split_ifs
  · exact le_max_left _ _
  · exact hms
  · exact hms.trans (le_mul_of_one_le_left (hm.trans hms) p.one_lt_grow.le)

/-- Practical weight updates preserve positivity without a positive safeguard. -/
theorem weight_pos (p : Parameters) {sigma : ℝ} (hs : 0 < sigma)
    (minimum rho : ℝ) : 0 < weight p minimum sigma rho := by
  unfold weight
  split_ifs
  · exact (mul_pos p.shrink_pos hs).trans_le (le_max_right _ _)
  · exact hs
  · exact mul_pos (zero_lt_one.trans p.one_lt_grow) hs

/-- Power calibration suggested when the corresponding regularization weight is large.
This is a parameter choice, not a performance guarantee. -/
def powerCalibration (shrink grow order : ℝ) : ℝ × ℝ :=
  (grow ^ (-(order - 1)), shrink ^ (-(order - 1)))

/-- The calibration has the two stated reciprocal-power factors. -/
@[simp] theorem powerCalibration_eq (shrink grow order : ℝ) (hs : 0 ≤ shrink) (hg : 0 ≤ grow) :
    powerCalibration shrink grow order = ((grow ^ (order - 1))⁻¹,
      (shrink ^ (order - 1))⁻¹) := by
  simp only [powerCalibration, Real.rpow_neg hs, Real.rpow_neg hg]

/-- For order greater than one, the suggested factors are a contraction and an expansion. -/
theorem powerCalibration_bounds (p : Parameters) {order : ℝ} (ho : 1 < order) :
    0 < (powerCalibration p.shrink p.grow order).1 ∧
    (powerCalibration p.shrink p.grow order).1 < 1 ∧
    1 < (powerCalibration p.shrink p.grow order).2 := by
  have he : -(order - 1) < 0 := by linarith
  exact ⟨Real.rpow_pos_of_pos (zero_lt_one.trans p.one_lt_grow) _,
    Real.rpow_lt_one_of_one_lt_of_neg p.one_lt_grow he,
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg p.shrink_pos p.shrink_lt_one he⟩

end Optimization.StepScaledUpdates
