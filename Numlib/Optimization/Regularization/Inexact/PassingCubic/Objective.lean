import Numlib.Optimization.Regularization.Inexact.PassingCubic.Model
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# True derivative errors at passing cubic checks

A globally smooth trigonometric objective has the prescribed first three jets and globally
Lipschitz tensors including order zero. Its small actual first-order error separates the true
criticality and explicit verification budget from a passing computed check. This component
does not assert any preceding parameter or accuracy execution.
-/

namespace InexactRegularization.PassingCubic

/-- A globally smooth true objective with a small linear jet perturbation of the computed
cubic. -/
noncomputable def objective (G B x : ℝ) : ℝ :=
  (G - 1) * x + Real.sin x + B * (1 - Real.cos x)

/-- The true first derivative of the scalar trigonometric objective. -/
theorem derivative_objective (G B : ℝ) : deriv (objective G B) =
    fun x => G - 1 + Real.cos x + B * Real.sin x := by
  funext x
  have hh := (((hasDerivAt_id x).const_mul (G - 1)).add (Real.hasDerivAt_sin x)).add
    (((hasDerivAt_const x 1).sub (Real.hasDerivAt_cos x)).const_mul B)
  have hd : deriv (objective G B) x =
      (G - 1) * 1 + Real.cos x + B * (0 - -Real.sin x) := hh.deriv
  linarith


/-- Differentiating the actual first derivative gives the stated second derivative. -/
theorem derivative_first (G B : ℝ) :
    deriv (fun x => G - 1 + Real.cos x + B * Real.sin x) =
      fun x => -Real.sin x + B * Real.cos x := by
  funext x
  have hh := ((hasDerivAt_const x (G - 1)).add (Real.hasDerivAt_cos x)).add
    ((Real.hasDerivAt_sin x).const_mul B)
  convert hh.deriv using 1
  ring

/-- Differentiating the actual second derivative gives the stated third derivative. -/
theorem derivative_second (B : ℝ) :
    deriv (fun x => -Real.sin x + B * Real.cos x) =
      fun x => -Real.cos x - B * Real.sin x := by
  funext x
  have hh := (Real.hasDerivAt_sin x).neg.add ((Real.hasDerivAt_cos x).const_mul B)
  convert hh.deriv using 1
  ring

/-- The actual objective jets at zero differ from the computed cubic only in the first
derivative. -/
theorem objective_jets (G B : ℝ) {j : ℕ} (hj : j ≤ 3) :
    iteratedDeriv j (objective G B) 0 =
      if j = 0 then 0 else if j = 1 then G else if j = 2 then B else -1 := by
  interval_cases j
  · simp [objective]
  · rw [iteratedDeriv_one, derivative_objective]
    simp
  · rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
      derivative_objective, derivative_first]
    simp
  · rw [show 3 = 2 + 1 by rfl, iteratedDeriv_succ,
      show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
      derivative_objective, derivative_first, derivative_second]
    simp

/-- The true third-order Taylor decrement includes the actual linear perturbation. -/
theorem true_decrement (G B u : ℝ) :
    TaylorModel.decrement (objective G B) 3 0 u = -G * u - B / 2 * u ^ 2 + u ^ 3 / 6 := by
  rw [TaylorModel.decrement_eq, TaylorModel.eval_eq_sum_iteratedDeriv]
  have hh := fun i (hi : i ≤ 3) => objective_jets G B hi
  norm_num [Finset.sum_range_succ, hh, objective]
  ring

/-- Every sufficiently small returned third-order radius fails the true requested
criticality test. -/
theorem true_failure {G B δ : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hδB : δ ≤ 4 * B)
    (hG : 6 * B ^ 2 < G) :
    (1 / 2 : ℝ) * δ ^ 3 / 6 < TaylorModel.criticality (objective G B) 3 0 δ := by
  have hl := TaylorModel.decrement_le_criticality (objective G B) 3 0 (s := -δ)
    (by simpa only [norm_neg, Real.norm_eq_abs, abs_of_pos hδ] using le_refl δ)
  rw [true_decrement] at hl
  have hδsq : δ ^ 2 ≤ 16 * B ^ 2 := by nlinarith
  have hBδ : B * δ ≤ 4 * B ^ 2 := by nlinarith
  have hbracket : δ * ((1 / 2 : ℝ) * δ ^ 2 / 6 + B / 2 * δ + δ ^ 2 / 6) < δ * G := by
    apply mul_lt_mul_of_pos_left _ hδ
    nlinarith
  nlinarith
end InexactRegularization.PassingCubic
namespace InexactRegularization.PassingCubic

/-- The true objective has every finite order of continuous derivatives. -/
theorem smooth_objective (G B : ℝ) (n : ℕ) : ContDiff ℝ n (objective G B) := by
  unfold objective
  fun_prop

/-- The fourth derivative is the stated bounded trigonometric combination. -/
theorem derivative_third (B : ℝ) :
    deriv (fun x => -Real.cos x - B * Real.sin x) =
      fun x => Real.sin x - B * Real.cos x := by
  funext x
  have hh := (Real.hasDerivAt_cos x).neg.sub ((Real.hasDerivAt_sin x).const_mul B)
  convert hh.deriv using 1
  ring

/-- The actual scalar derivatives through order four have explicit trigonometric formulas. -/
theorem objective_derivative_formula (G B : ℝ) {j : ℕ} (hj : j ≤ 4) (x : ℝ) :
    iteratedDeriv j (objective G B) x =
      if j = 0 then objective G B x else if j = 1 then G - 1 + Real.cos x + B * Real.sin x
      else if j = 2 then -Real.sin x + B * Real.cos x
      else if j = 3 then -Real.cos x - B * Real.sin x
      else Real.sin x - B * Real.cos x := by
  interval_cases j
  · rfl
  · rw [iteratedDeriv_one, derivative_objective]
    rfl
  · rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
      derivative_objective, derivative_first]
    rfl
  · rw [show 3 = 2 + 1 by rfl, iteratedDeriv_succ,
      show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
      derivative_objective, derivative_first, derivative_second]
    rfl
  · rw [show 4 = 3 + 1 by rfl, iteratedDeriv_succ,
      show 3 = 2 + 1 by rfl, iteratedDeriv_succ,
      show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
      derivative_objective, derivative_first, derivative_second, derivative_third]
    rfl

/-- A bounded constant and two bounded trigonometric terms have a common absolute bound. -/
theorem abs_combination_le {c a b B : ℝ} (hc : |c| ≤ 1) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hB : 0 ≤ B) (hB1 : B ≤ 1) : |c + a + B * b| ≤ 3 := by
  have hh := abs_add_le (c + a) (B * b)
  have hh2 := abs_add_le c a
  rw [abs_mul, abs_of_nonneg hB] at hh
  have hmul := mul_le_of_le_one_right hB hb
  linarith

/-- Every positive actual derivative through order four has absolute value at most three. -/
theorem objective_derivative_bound {G B : ℝ} (hG : 0 ≤ G) (hG1 : G ≤ 1)
    (hB : 0 ≤ B) (hB1 : B ≤ 1) {j : ℕ} (hj : 1 ≤ j) (hj4 : j ≤ 4) (x : ℝ) :
    |iteratedDeriv j (objective G B) x| ≤ 3 := by
  rw [objective_derivative_formula G B hj4]
  have hGabs : |G - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := Real.abs_sin_le_one x
  have hc := Real.abs_cos_le_one x
  interval_cases j <;> norm_num only <;> simp only [ite_true, ite_false]
  · exact abs_combination_le hGabs hc hs hB hB1
  · simpa only [zero_add, neg_mul, mul_neg] using
      abs_combination_le (c := 0) (a := -Real.sin x) (b := Real.cos x)
        (by norm_num) (by simpa only [abs_neg] using hs) hc hB hB1
  · convert abs_combination_le (c := 0) (a := -Real.cos x) (b := -Real.sin x)
      (by norm_num) (by simpa only [abs_neg] using hc)
      (by simpa only [abs_neg] using hs) hB hB1 using 1
    congr 1
    ring
  · convert abs_combination_le (c := 0) (a := Real.sin x) (b := -Real.cos x)
      (by norm_num) hs (by simpa only [abs_neg] using hc) hB hB1 using 1
    congr 1
    ring

/-- All actual tensor derivatives through order three, including the objective itself, are
globally three-Lipschitz. -/
theorem objective_lipschitz {G B : ℝ} (hG : 0 ≤ G) (hG1 : G ≤ 1)
    (hB : 0 ≤ B) (hB1 : B ≤ 1) (j : ℕ) (hj : j ≤ 3) (x y : ℝ) :
    ‖iteratedFDeriv ℝ j (objective G B) x - iteratedFDeriv ℝ j (objective G B) y‖ ≤
      3 * ‖x - y‖ := by
  rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub]
  have hf := (smooth_objective G B (j + 1)).differentiable_iteratedDeriv' j
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (f := iteratedDeriv j (objective G B)) (s := Set.univ)
    (fun z _ => hf z) (fun z _ => ?_) (convex_univ) (Set.mem_univ y) (Set.mem_univ x)
  rw [← iteratedDeriv_succ]
  simpa only [Real.norm_eq_abs] using objective_derivative_bound hG hG1 hB hB1
    (by omega : 1 ≤ j + 1) (by omega : j + 1 ≤ 4) z

/-- The actual computed tensor error is exactly the small first-order perturbation and
vanishes at the other positive orders. -/
theorem oracle_error (G B : ℝ) {j : ℕ} (hj : 1 ≤ j) (hj3 : j ≤ 3) :
    ‖jet B j - iteratedFDeriv ℝ j (objective G B) 0‖ = if j = 1 then |G| else 0 := by
  change ‖iteratedFDeriv ℝ j (polynomial B).eval 0 -
    iteratedFDeriv ℝ j (objective G B) 0‖ = _
  simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply]
  rw [← map_sub, LinearIsometryEquiv.norm_map, polynomial_jets B hj3, objective_jets G B hj3]
  interval_cases j <;> simp [Real.norm_eq_abs]
end InexactRegularization.PassingCubic
namespace InexactRegularization.PassingCubic
open InexactTrustRegion

/-- The explicit finite verification budget fails at every small passing third-order
radius. -/
theorem verification_fails {G B δ : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hδB : δ ≤ 4 * B)
    (hG : 6 * B ^ 2 < G) :
    (1 / 2 : ℝ) / 2 * (1 / 2) * δ ^ 3 / 6 < tensorErrorBudget (fun _ => G) 3 δ := by
  have hGpos : 0 < G := lt_of_le_of_lt (by positivity) hG
  have hh : δ * (δ ^ 2 / 48) < δ * G := by
    apply mul_lt_mul_of_pos_left _ hδ
    nlinarith
  norm_num [tensorErrorBudget, Finset.sum_range_succ]
  nlinarith [mul_nonneg hGpos.le (pow_nonneg hδ.le 2),
    mul_nonneg hGpos.le (pow_nonneg hδ.le 3)]

/-- A complete actual passing Step1 computation with a globally smooth Lipschitz true
objective and genuine tensor errors can fail true third-order criticality and the
explicit verification budget. -/
theorem exists_passing_component {G B σ : ℝ} (hσ : 0 < σ) (hBσ : 1 / 3 ≤ B * σ)
    (hG : 6 * B ^ 2 < G) (hG1 : G ≤ 1) (hB1 : B ≤ 1)
    (initial : Fin 3 → ℝ) (hinit : ∀ a, 0 < initial a ∧ initial a ≤ 1) :
    ∃ (reduced : Fin 3 → ℝ) (reference : ℝ) (direction : Fin 3 → ℕ → ℝ)
      (count : Fin 3 → ℕ),
      ContDiff ℝ 3 (objective G B) ∧
      (∀ j ≤ 3, ∀ x y, ‖iteratedFDeriv ℝ j (objective G B) x -
        iteratedFDeriv ℝ j (objective G B) y‖ ≤ 3 * ‖x - y‖) ∧
      (∀ j, 1 ≤ j → j ≤ 3 →
        ‖jet B j - iteratedFDeriv ℝ j (objective G B) 0‖ ≤ G) ∧
      StepOneComputation (jet B) 3 σ (1 / 2) (fun _ => 1 / 2)
        initial reduced reference direction count none ∧
      0 < reduced 2 ∧ reduced 2 ≤ 4 * B ∧
      (1 / 2 : ℝ) * reduced 2 ^ 3 / 6 <
        TaylorModel.criticality (objective G B) 3 0 (reduced 2) ∧
      (1 / 2 : ℝ) / 2 * (1 / 2) * reduced 2 ^ 3 / 6 <
        tensorErrorBudget (fun _ => G) 3 (reduced 2) := by
  have hB : 0 < B := by nlinarith
  have hGpos : 0 < G := lt_of_le_of_lt (by positivity) hG
  obtain ⟨reduced, reference, direction, count, hone, hbound⟩ :=
    exists_passing hσ hBσ initial hinit
  have hδ := (hone.radius_bounds hinit 2).1
  refine ⟨reduced, reference, direction, count, smooth_objective G B 3,
    fun j hj x y => objective_lipschitz hGpos.le hG1 hB.le hB1 j hj x y,
    ?_, hone, hδ, hbound, true_failure hδ hB.le hbound hG,
    verification_fails hδ hB.le hbound hG⟩
  intro j hj hj3
  rw [oracle_error G B hj hj3]
  split_ifs
  · exact le_of_eq (abs_of_pos hGpos)
  · exact hGpos.le
end InexactRegularization.PassingCubic
