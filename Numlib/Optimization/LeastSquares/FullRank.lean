import Numlib.Optimization.LeastSquares.Measures
import Numlib.Optimization.MeasureDomination.Trace
import Numlib.Optimization.MeasureDomination.RootTarget

/-!
# Actual residual-power domination under a uniform first-measure bound

The source full-rank condition is the positive lower bound on the normalized
actual objective gradient at nonzero residuals. It gives domination only along
visited points, with no additional ambient root-existence assumption.
-/

namespace LeastSquares
open MeasureDomination Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  {r : E → F} {ℓ κ : ℝ} {x : ℕ → E}

/-- Source condition(5.1.62), imposed until residual zero. At a residual zero
the corresponding weighted gradient lower bound is automatically nonnegative. -/
def UniformFirstMeasure (r : E → F) (ℓ κ : ℝ) (x : ℕ → E) : Prop :=
  ∀ k, r (x k) ≠ 0 → κ ≤ firstMeasure r ℓ (x k)

/-- The source first-measure condition bounds the actual objective derivative
norm by its exact residual weight, including residual zeros. -/
theorem UniformFirstMeasure.gradient_lower_bound (h : UniformFirstMeasure r ℓ κ x)
    (hℓ : 1 < ℓ) (k : ℕ) :
    κ * ‖r (x k)‖ ^ (ℓ - 1) ≤ ‖fderiv ℝ (powerObjective r ℓ) (x k)‖ := by
  by_cases hz : r (x k) = 0
  · simp only [hz, norm_zero, Real.zero_rpow (by linarith : ℓ - 1 ≠ 0), mul_zero]
    exact norm_nonneg _
  · have hh := (le_div_iff₀ (derivativeWeight_pos r ℓ hz)).mp (h k hz)
    exact hh

/-- Residual-power domination follows from the actual normalized derivative
bound, with the exact exponent `ℓ/(ℓ−1)` and accuracy-independent coefficient. -/
theorem UniformFirstMeasure.along_domination (h : UniformFirstMeasure r ℓ κ x)
    (hℓ : 1 < ℓ) (hκ : 0 < κ) :
    AlongDomination (powerObjective r ℓ)
      (fun z => ‖fderiv ℝ (powerObjective r ℓ) z‖) 0 (ℓ / (ℓ - 1))
      (1 / (ℓ * κ ^ (ℓ / (ℓ - 1)))) x := by
  have hℓpos : 0 < ℓ := zero_lt_one.trans hℓ
  have hd : 0 < ℓ - 1 := by linarith
  have hμ : 0 < ℓ / (ℓ - 1) := div_pos hℓpos hd
  refine ⟨fun k => ?_, fun _ => norm_nonneg _, (one_le_div hd).mpr (by linarith),
    by positivity, fun k => ?_⟩
  · simp only [gap, powerObjective_apply, sub_zero]
    exact div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hℓpos.le
  · have hh := Real.rpow_le_rpow
      (mul_nonneg hκ.le (Real.rpow_nonneg (norm_nonneg _) _))
      (h.gradient_lower_bound hℓ k) hμ.le
    rw [Real.mul_rpow hκ.le (Real.rpow_nonneg (norm_nonneg _) _),
      ←Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ ℓ hd.ne'] at hh
    have hc : 0 < κ ^ (ℓ / (ℓ - 1)) := Real.rpow_pos_of_pos hκ _
    have hb := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ 1 / (ℓ * κ ^ (ℓ / (ℓ - 1))) by positivity)
    simp only [gap, powerObjective_apply, sub_zero]
    convert hb using 1; field_simp

/-- In the trust-region power regime, actual residual targets have the source
inverse power `ℓ−2`, with all initialization and first-attainment clauses. -/
theorem UniformFirstMeasure.tr_power_cost (h : UniformFirstMeasure r ℓ κ x)
    (hℓ : 2 < ℓ) (hκ : 0 < κ) {κν κR κA : ℝ} {S : Set ℕ}
    (hr : TRRun (powerObjective r ℓ)
      (fun z => ‖fderiv ℝ (powerObjective r ℓ) z‖) x S 2 κν κR κA) :
    PowerCost (ℓ - 2) (fun k => ‖r (x k)‖) S := by
  have hl : 1 < ℓ := by linarith
  have hd := h.along_domination hl hκ
  have hμν : ℓ / (ℓ - 1) < 2 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
  have hh := (hr.trace_run (fstar := 0)).gap_power_cost hd.dominated hμν
  simp only [gap, traceObjective_iterate, sub_zero, powerObjective_apply] at hh
  have hc := hh.root (zero_lt_one.trans hl) (fun k => norm_nonneg (r (x k)))
  have he : ℓ * ((2 - ℓ / (ℓ - 1)) / (ℓ / (ℓ - 1))) = ℓ - 2 := by
    field_simp [(by linarith : ℓ ≠ 0), (by linarith : ℓ - 1 ≠ 0)]
    ring
  simpa only [he] using hc

/-- In the quadratic-residual case, actual initialized residual-target costs are
logarithmic, with constants chosen before every positive accuracy. -/
theorem UniformFirstMeasure.tr_logarithmic_cost (h : UniformFirstMeasure r 2 κ x)
    (hκ : 0 < κ) {κν κR κA : ℝ} {S : Set ℕ}
    (hr : TRRun (powerObjective r 2)
      (fun z => ‖fderiv ℝ (powerObjective r 2) z‖) x S 2 κν κR κA) :
    LogarithmicCost (fun k => ‖r (x k)‖) S := by
  have hd := h.along_domination (by norm_num : (1 : ℝ) < 2) hκ
  have hh := (hr.trace_run (fstar := 0)).gap_logarithmic hd.dominated (by norm_num)
  simp only [gap, traceObjective_iterate, sub_zero, powerObjective_apply] at hh
  exact hh.root (by norm_num) (fun k => norm_nonneg (r (x k)))

/-- The actual residuals converge above the domination level, with a genuine
sublinear upper envelope allowing faster convergence and exact attainment. -/
theorem UniformFirstMeasure.tr_sublinear (h : UniformFirstMeasure r ℓ κ x)
    (hℓ : 2 < ℓ) (hκ : 0 < κ) {κν κR κA : ℝ} {S : Set ℕ}
    (hr : TRRun (powerObjective r ℓ)
      (fun z => ‖fderiv ℝ (powerObjective r ℓ) z‖) x S 2 κν κR κA) :
    Tendsto (fun j => ‖r (x (successIndex S j))‖) Filter.atTop (nhds 0) ∧
      ((∀ j, ‖r (x (successIndex S j))‖ = 0) ∨
        ∃ t : ℕ → ℝ, (∀ j, 0 < t j) ∧
          (∀ j, ‖r (x (successIndex S j))‖ ≤ t j) ∧
          Tendsto t Filter.atTop (nhds 0) ∧
          Tendsto (fun j => t (j + 1) / t j) Filter.atTop (nhds 1)) := by
  have hl : 1 < ℓ := by linarith
  have hd := h.along_domination hl hκ
  have hμν : ℓ / (ℓ - 1) < 2 := (div_lt_iff₀ (by linarith)).mpr (by linarith)
  have ht := (hr.trace_run (fstar := 0)).successful_tendsto_zero hd.dominated
  have he := (hr.trace_run (fstar := 0)).successful_sublinear_envelope hd.dominated hμν
  change Tendsto (fun j => powerObjective r ℓ (x (successIndex S j)) - 0)
    atTop (nhds 0) at ht
  simp only [MeasureDomination.successfulGap, gap, traceObjective_iterate, sub_zero,
    powerObjective_apply] at ht he
  exact ⟨tendsto_zero_of_scaled_power (ℓ := ℓ) (by linarith) (fun _ => norm_nonneg _) ht,
    sublinear_envelope_of_scaled_power (ℓ := ℓ) (by linarith) (fun _ => norm_nonneg _) he⟩

/-- Quadratic-residual trust-region iterates either reach residual zero at the
first accepted endpoint or contract linearly with a genuine factor below one. -/
theorem UniformFirstMeasure.tr_linear (h : UniformFirstMeasure r 2 κ x)
    (hκ : 0 < κ) {κν κR κA : ℝ} {S : Set ℕ}
    (hr : TRRun (powerObjective r 2)
      (fun z => ‖fderiv ℝ (powerObjective r 2) z‖) x S 2 κν κR κA) :
    Tendsto (fun j => ‖r (x (successIndex S j))‖) atTop (nhds 0) ∧
      (r (x (successIndex S 0 + 1)) = 0 ∨
        ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ j,
          ‖r (x (successIndex S (j + 1)))‖ ≤ c * ‖r (x (successIndex S j))‖) := by
  have hd := h.along_domination (by norm_num : (1 : ℝ) < 2) hκ
  have ht := (hr.trace_run (fstar := 0)).successful_tendsto_zero hd.dominated
  have he := (hr.trace_run (fstar := 0)).linear_alternative hd.dominated (by norm_num)
  change Tendsto (fun j => powerObjective r 2 (x (successIndex S j)) - 0)
    atTop (nhds 0) at ht
  simp only [MeasureDomination.successfulGap, gap, traceObjective_iterate, sub_zero,
    powerObjective_apply] at ht he
  refine ⟨tendsto_zero_of_scaled_power (ℓ := 2) (by norm_num) (fun _ => norm_nonneg _) ht, ?_⟩
  rcases he with hz | ⟨hcoeff, hlin⟩
  · left
    have hh := root_scaled_power (by norm_num : (0 : ℝ) < 2)
      (norm_nonneg (r (x (successIndex S 0 + 1))))
    rw [hz, mul_zero, Real.zero_rpow (by norm_num : (1 / (2 : ℝ)) ≠ 0)] at hh
    exact norm_eq_zero.mp hh.symm
  · right
    let a := 1 - κν / (1 / (2 * κ ^ ((2 : ℝ) / (2 - 1))))
    have hcpos : 0 < 1 / (2 * κ ^ ((2 : ℝ) / (2 - 1))) := by positivity
    have ha : 0 ≤ a := sub_nonneg.mpr ((div_le_one hcpos).mpr hcoeff.le)
    have ha1 : a < 1 := by
      dsimp [a]
      have hh := div_pos hr.coefficient_pos hcpos
      linarith
    refine ⟨a ^ (1 / 2 : ℝ), Real.rpow_nonneg ha _,
      Real.rpow_lt_one ha ha1 (by norm_num), ?_⟩
    intro j
    exact linear_step_of_scaled_power (by norm_num) (norm_nonneg _) ha
      (norm_nonneg _) (hlin j)

end LeastSquares
