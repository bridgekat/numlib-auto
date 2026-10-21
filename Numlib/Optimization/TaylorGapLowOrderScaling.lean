import Numlib.Optimization.TaylorCriticalityCriteria
import Numlib.Optimization.HigherOrderApproximateRegularizationBounds
import Mathlib.Tactic

/-!
# Unit-radius transfer for low-order Taylor gaps

Linear and quadratic Taylor gap bounds normalized by the radius power imply the same bound
on the unit ball. The quadratic proof combines the opposite scaled displacements with
nonnegative weights. No analogous assertion is made for higher Taylor orders.
-/

noncomputable section
open scoped Nat
namespace Optimization.TaylorCriticality
open Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A quadratic Taylor decrement is a nonnegative combination of its values at opposite
scaled displacements when the scaling lies in `(0,1]`. -/
theorem taylorDecrement_two_scaled_combination (f : E → ℝ) (x d : E) {δ : ℝ}
    (hδ : δ ≠ 0) :
    taylorDecrement f 2 x d =
      (1 + δ) / (2 * δ ^ 2) * taylorDecrement f 2 x (δ • d) +
      (1 - δ) / (2 * δ ^ 2) * taylorDecrement f 2 x ((-δ) • d) := by
  simp only [taylorDecrement_two, map_smul, smul_apply, smul_eq_mul]
  field_simp
  ring

/-- A normalized first-order gap estimate at any positive radius implies its unit-radius
version. The argument uses the actual linear Taylor decrement. -/
theorem gapOn_taylorDecrement_one_unit [ProperSpace E] (f : E → ℝ) (x : E)
    {δ ε : ℝ} (hδ : 0 < δ)
    (hgap : gapOn (taylorDecrement f 1 x) (closedBall 0 δ) ≤ ε * δ) :
    gapOn (taylorDecrement f 1 x) (closedBall 0 1) ≤ ε := by
  apply gapOn_le ⟨0, by simp⟩
  intro d hd
  have hmem : δ • d ∈ closedBall (0 : E) δ := by
    simp only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    exact mul_le_of_le_one_right hδ.le (mem_closedBall_zero_iff.mp hd)
  have h := (le_gapOn (isCompact_closedBall (0 : E) δ)
    (continuous_taylorDecrement f 1 x).continuousOn hmem).trans hgap
  simp only [taylorDecrement_one, map_smul, smul_eq_mul] at h ⊢
  nlinarith

/-- A normalized quadratic gap estimate on a radius at most one implies the same estimate
on the unit ball. Both opposite scaled steps are feasible in the smaller symmetric ball. -/
theorem gapOn_taylorDecrement_two_unit [ProperSpace E] (f : E → ℝ) (x : E)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgap : gapOn (taylorDecrement f 2 x) (closedBall 0 δ) ≤ ε * δ ^ 2 / 2) :
    gapOn (taylorDecrement f 2 x) (closedBall 0 1) ≤ ε / 2 := by
  apply gapOn_le ⟨0, by simp⟩
  intro d hd
  have hp : δ • d ∈ closedBall (0 : E) δ := by
    simp only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    exact mul_le_of_le_one_right hδ.le (mem_closedBall_zero_iff.mp hd)
  have hm : (-δ) • d ∈ closedBall (0 : E) δ := by
    simpa only [neg_smul, mem_closedBall_zero_iff, norm_neg] using hp
  have hpos := (le_gapOn (isCompact_closedBall (0 : E) δ)
    (continuous_taylorDecrement f 2 x).continuousOn hp).trans hgap
  have hneg := (le_gapOn (isCompact_closedBall (0 : E) δ)
    (continuous_taylorDecrement f 2 x).continuousOn hm).trans hgap
  rw [taylorDecrement_two_scaled_combination f x d hδ.ne']
  have ha : 0 ≤ (1 + δ) / (2 * δ ^ 2) := by positivity
  have hb : 0 ≤ (1 - δ) / (2 * δ ^ 2) := div_nonneg (by linarith) (by positivity)
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hpos ha)
    (mul_le_mul_of_nonneg_left hneg hb)
  apply hsum.trans_eq
  field_simp
  ring

/-- Normalized actual Taylor gap bounds transfer to the unit ball at orders one and two. -/
theorem gapOn_taylorDecrement_unit_of_le_two [ProperSpace E] (f : E → ℝ) (x : E)
    {j : ℕ} (hj : 1 ≤ j) (hj2 : j ≤ 2) {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgap : gapOn (taylorDecrement f j x) (closedBall 0 δ) ≤ ε * δ ^ j / (j ! : ℝ)) :
    gapOn (taylorDecrement f j x) (closedBall 0 1) ≤ ε / (j ! : ℝ) := by
  interval_cases j
  · simpa using gapOn_taylorDecrement_one_unit f x hδ (by simpa using hgap)
  · simpa using gapOn_taylorDecrement_two_unit f x hδ hδ1 (by simpa using hgap)

end Optimization.TaylorCriticality

namespace Optimization.HigherOrderApproximateRegularization
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- True simultaneous criteria at valid inspected radii imply unit-radius quality when
at most the first two Taylor orders are requested. -/
theorem SatisfiesCriteria.unit_of_order_le_two {P : Parameters} {f : E → ℝ} {x : E}
    {δ : ℕ → ℝ} (h : SatisfiesCriteria P f x δ) (hδ : ValidRadii P δ) (hq : P.q ≤ 2) :
    SatisfiesCriteria P f x (fun _ => 1) := by
  intro j hj hjq
  simpa only [one_pow, mul_one] using
    TaylorCriticality.gapOn_taylorDecrement_unit_of_le_two f x hj (hjq.trans hq)
      (hδ j hj hjq).1 (hδ j hj hjq).2 (h j hj hjq)

end Optimization.HigherOrderApproximateRegularization
