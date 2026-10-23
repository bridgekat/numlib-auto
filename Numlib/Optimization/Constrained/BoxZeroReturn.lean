import Numlib.Optimization.Regularization.HighOrder.ConstrainedOuterReturn
import Numlib.Optimization.Constrained.FirstOrderCriticality
import Numlib.Optimization.Composite.ZeroReturnCounterexample
import Numlib.Analysis.Calculus.IteratedBilinearBounds

/-!
# A feasible zero exit with full local value and derivative regularity

A bounded scalar box supplies simple constraints. On its open convex
neighborhood, the actual quadratic objective has bounded Lipschitz zeroth and
first jets. A legal large model return causes immediate termination at the
initial point, where every legal positive constrained testing radius fails.
-/

namespace RegularizationZeroReturn.Box
open Set

/-- A closed nonempty convex scalar box whose membership requires no oracle. -/
def feasible : Set ℝ := Icc (-5) 5

/-- An open convex neighborhood of the feasible box. -/
def neighborhood : Set ℝ := Ioo (-6) 6

/-- The concrete feasible set and neighborhood have all required geometry. -/
theorem geometry : IsClosed feasible ∧ feasible.Nonempty ∧ Convex ℝ feasible ∧
    IsOpen neighborhood ∧ Convex ℝ neighborhood ∧ feasible ⊆ neighborhood := by
  refine ⟨isClosed_Icc, ⟨0, by norm_num [feasible]⟩, convex_Icc _ _,
    isOpen_Ioo, convex_Ioo _ _, ?_⟩
  intro x hx
  simp only [feasible, mem_Icc] at hx
  simp only [neighborhood, mem_Ioo]
  constructor <;> linarith

/-- Both the initial point and the selected large model step are feasible. -/
theorem initial_trial_feasible : (0 : ℝ) ∈ feasible ∧ (0 : ℝ) + 4 ∈ feasible := by
  norm_num [feasible]

/-- Every unit testing displacement is feasible from the initial point. -/
theorem testing_ball {δ : ℝ} (hδ : δ ≤ 1) {d : ℝ} (hd : ‖d‖ ≤ δ) :
    (0 : ℝ) + d ∈ feasible := by
  rw [Real.norm_eq_abs, abs_le] at hd
  simp only [feasible, mem_Icc, zero_add]
  constructor <;> linarith

/-- The actual constrained Taylor criticality equals twice the radius. -/
theorem criticality_formula {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    TaylorModel.constrainedCriticality objective 1 feasible 0 δ = 2 * δ := by
  rw [TaylorModel.constrainedCriticality_eq_of_ball
    (fun d hd => testing_ball hδ1 hd), RegularizationZeroReturn.criticality_formula hδ]

/-- The actual objective is Lipschitz on the open convex neighborhood. -/
theorem value_lipschitz {x y : ℝ} (hx : x ∈ neighborhood) (hy : y ∈ neighborhood) :
    ‖objective x - objective y‖ ≤ 8 * ‖x - y‖ := by
  have hfac : objective x - objective y = (x - y) * (x + y - 4) / 2 := by
    unfold objective
    ring
  have hb : |x + y - 4| ≤ 16 := by
    simp only [neighborhood, mem_Ioo] at hx hy
    rw [abs_le]
    constructor <;> linarith
  rw [hfac, Real.norm_eq_abs, abs_div, abs_mul]
  norm_num
  have hh := mul_le_mul_of_nonneg_left hb (abs_nonneg (x - y))
  simpa only [Real.norm_eq_abs] using (by linarith : |x - y| * |x + y - 4| / 2 ≤
    8 * |x - y|)

/-- The actual first jet is uniformly bounded on the neighborhood. -/
theorem derivative_bound {x : ℝ} (hx : x ∈ neighborhood) :
    ‖iteratedFDeriv ℝ 1 objective x‖ ≤ 8 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro d
  simp only [iteratedFDeriv_one_apply, fderiv_objective, norm_mul]
  have hb : ‖x - 2‖ ≤ 8 := by
    simp only [neighborhood, mem_Ioo] at hx
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  simpa only [Fin.prod_univ_one] using mul_le_mul_of_nonneg_right hb (norm_nonneg (d 0))

/-- The actual objective is uniformly bounded on the neighborhood. -/
theorem value_bound {x : ℝ} (hx : x ∈ neighborhood) : ‖objective x‖ ≤ 32 := by
  have hb : |x - 2| ≤ 8 := by
    simp only [neighborhood, mem_Ioo] at hx
    rw [abs_le]
    constructor <;> linarith
  have hs : (x - 2) ^ 2 ≤ 64 := by
    have hh := (sq_le_sq₀ (abs_nonneg (x - 2)) (by norm_num : (0 : ℝ) ≤ 8)).mpr hb
    simpa only [sq_abs, show (8 : ℝ) ^ 2 = 64 by norm_num] using hh
  rw [Real.norm_eq_abs, abs_of_nonneg (nonneg x)]
  unfold objective
  linarith

/-- Every requested positive unit-or-smaller radius fails approximate criticality. -/
theorem not_critical {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ¬TaylorModel.constrainedCriticality objective 1 feasible 0 δ ≤ (1 / 2 : ℝ) * δ := by
  rw [criticality_formula hδ.le hδ1]
  linarith

/-- All actual zeroth and first jets satisfy the source anchored Lipschitz
and sublevel bounds, with fixed constants eight and thirty-two. -/
theorem source_regularity : ContDiffOn ℝ 1 objective neighborhood ∧
    (∀ j : ℕ, j ≤ 1 → ∀ x ∈ feasible, objective x ≤ objective 0 →
      ‖iteratedFDeriv ℝ j objective x‖ ≤ 32 ∧ ∀ y ∈ neighborhood,
        ‖iteratedFDeriv ℝ j objective x - iteratedFDeriv ℝ j objective y‖ ≤
          8 * ‖x - y‖) ∧ ∀ x ∈ feasible, 0 ≤ objective x := by
  refine ⟨(smooth 1).contDiffOn, ?_, fun x _ => nonneg x⟩
  intro j hj x hx _
  have hxS := geometry.2.2.2.2.2 hx
  interval_cases j
  · constructor
    · simpa only [norm_iteratedFDeriv_zero] using value_bound hxS
    · intro y hy
      simpa only [norm_iteratedFDeriv_zero_sub] using value_lipschitz hxS hy
  · refine ⟨(derivative_bound hxS).trans (by norm_num), ?_⟩
    intro y hy
    have hh := derivative_lipschitz x y
    exact hh.trans (by nlinarith [norm_nonneg (x - y)])

/-- Fixed legal first-order settings, with the requested unit-radius policy. -/
noncomputable abbrev settings := Composite.ZeroReturnCounterexample.settings

/-- The sole computed initial direction is feasible, exact and fails the
literal constrained relative optimality test. -/
theorem initial_check : HighOrderRegularization.ConstrainedOptimalityCheck objective
    feasible settings.zeta (fun _ : Fin 1 => 1 / 2) (fun _ => 1) 0
      (fun _ => 1) (some 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a _
    norm_num [feasible]
  · intro a _
    have ha : InexactTrustRegion.modelOrder a = 1 := by
      unfold InexactTrustRegion.modelOrder
      omega
    rw [ha, criticality_formula (by norm_num) (by norm_num),
      RegularizationZeroReturn.decrement_formula]
    norm_num [settings, Composite.ZeroReturnCounterexample.settings]
  · intro hn
    contradiction
  · intro a _
    have ha : InexactTrustRegion.modelOrder a = 1 := by
      unfold InexactTrustRegion.modelOrder
      omega
    rw [ha, RegularizationZeroReturn.decrement_formula]
    norm_num [settings, Composite.ZeroReturnCounterexample.settings]
  · intro a _ b hb
    have ha0 : a = 0 := Fin.eq_zero a
    have hb0 : b = 0 := Fin.eq_zero b
    omega

/-- The large returned step is feasible, preserves the unit radius and has
zero model decrease, so the literal constrained outer algorithm exits at zero. -/
theorem actual_exit : HighOrderRegularization.ConstrainedOuterZeroExit objective
    feasible settings (fun _ : Fin 1 => 1 / 2) 0 4 (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 0) 0 := by
  refine ⟨by intro a; norm_num, initial_trial_feasible.1,
    by intro a; norm_num, initial_check, ?_, ?_⟩
  · refine ⟨initial_trial_feasible.2, ?_, by intro a; norm_num,
      Or.inl ⟨by norm_num, rfl⟩⟩
    change HighOrderRegularization.model objective 1 0 1 4 ≤
      HighOrderRegularization.model objective 1 0 1 0
    exact zero_improvement.le
  · change HighOrderRegularization.model objective 1 0 1 4 =
      HighOrderRegularization.model objective 1 0 1 0
    exact zero_improvement

/-- No point produced by the immediate constrained exit satisfies the actual
first-order constrained certificate at any legal positive radius. -/
theorem no_produced_certificate : ¬∃ (z δ : ℝ), actual_exit.producedPoint z ∧
    0 < δ ∧ δ ≤ 1 ∧
      TaylorModel.constrainedCriticality objective 1 feasible z δ ≤ (1 / 2 : ℝ) * δ := by
  rintro ⟨z, δ, hz, hd, hd1, hc⟩
  rw [actual_exit.producedPoint_iff] at hz
  subst z
  exact not_critical hd hd1 hc

end RegularizationZeroReturn.Box
