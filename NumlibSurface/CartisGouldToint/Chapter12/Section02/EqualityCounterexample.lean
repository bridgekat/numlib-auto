import Numlib.Optimization.HigherOrderApproximateRegularizationSharpness
import Numlib.Optimization.HigherOrderDerivativeFamily

/-!
# A literal ARqp equality stop without true optimality

The supplied outer Step2 conditions alone permit an equality stop at a point that fails every
positive-radius first-order criterion. Actual inner fraction provenance excludes this behavior.
-/

noncomputable section
open scoped Nat
open Optimization HigherOrderApproximateRegularization
open HigherOrderApproximateRegularizationSharpness TaylorCriticality Metric Set
namespace CartisGouldToint.Chapter12.Section02
private def P : Parameters := parameters 1 1 le_rfl le_rfl (1 / 2) 1
  (by norm_num) (by norm_num) (by norm_num)
private def f (x : ℝ) : ℝ := x ^ 2 / 2 - 2 * x
private theorem df (x : ℝ) : deriv f x = x - 2 := by
  have h := (((hasDerivAt_id x).pow 2).div_const 2).sub ((hasDerivAt_id x).const_mul 2)
  change HasDerivAt f _ x at h
  rw [h.deriv]
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring
private theorem lip : LipschitzWith 1 (deriv f) := by
  have he : deriv f = fun x => x - 2 := funext df
  rw [he]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul]
  have heq : x - 2 - (y - 2) = x - y := by ring
  rw [heq]
private theorem family : HigherOrderDerivativeFamily f 1 (fun _ => 1) := by
  have hf : ContDiff ℝ 1 f := by unfold f; fun_prop
  refine ⟨hf, fun _ _ _ => by norm_num, ?_⟩
  intro j hj hjp x y d
  have he : j = 1 := by omega
  subst j
  have hl : LipschitzWith 1 (iteratedFDeriv ℝ 1 f) :=
    HigherOrderSharpness.iteratedFDeriv_lipschitz (by simpa only [iteratedDeriv_one] using lip)
  apply (HigherOrderRegularization.DiagonalLipschitz.of_operator hf (by norm_num) ?_).bound x y d
  intro a b
  simpa only [dist_eq_norm, NNReal.coe_one] using hl.dist_le_mul a b
private theorem model_formula (t : ℝ) : model f 1 0 1 t = -2*t+t^2/2 := by
  change RegularizedTaylorModel.taylorModel f 1 0 t +
    1/((1+1)! : ℝ)*‖t‖^(1+1) = _
  rw [RegularizedTaylorModel.taylorModel_one, fderiv_eq_deriv_mul, df]
  norm_num [f, Real.norm_eq_abs, sq_abs]
  ring
private theorem dec (d : ℝ) : taylorDecrement f 1 0 d = 2*d := by
  rw [taylorDecrement_one, fderiv_eq_deriv_mul, df]
  norm_num
private theorem gap : gapOn (taylorDecrement f 1 0) (closedBall 0 1) = 2 := by
  apply le_antisymm
  · apply gapOn_le ⟨0, by simp⟩
    intro d hd
    rw [dec]
    have hh : |d| ≤ 1 := by simpa [Real.dist_eq] using hd
    linarith [le_abs_self d]
  · have hh := le_gapOn (isCompact_closedBall (0 : ℝ) 1)
      (continuous_taylorDecrement f 1 0).continuousOn (show (1:ℝ) ∈ closedBall 0 1 by simp)
    simpa only [dec, mul_one] using hh
private theorem truegap_failure (δ : ℝ) (hδ : 0 < δ) :
    (1 / 2 : ℝ) * δ < gapOn (taylorDecrement f 1 0) (closedBall 0 δ) := by
  have hh := le_gapOn (isCompact_closedBall (0 : ℝ) δ)
    (continuous_taylorDecrement f 1 0).continuousOn
    (show δ ∈ closedBall 0 δ by simp [abs_of_pos hδ])
  rw [dec] at hh
  linarith
private theorem failed : Nonempty (FailedTest P f 0 (fun _ => 1)) := by
  refine ⟨⟨1, le_rfl, le_rfl, fun _ => 1, ?_, ?_, ?_⟩⟩
  · intro j hj hjq
    have he : j = 1 := by omega
    subst j
    constructor
    · norm_num
    · change 1 * gapOn (taylorDecrement f 1 0) (closedBall 0 1) ≤ _
      rw [gap, dec]
      norm_num
  · intro j hj hjq
    omega
  · change 1 * (1 / 2 : ℝ) * 1^1 / (1! : ℝ) ≤ _
    rw [dec]
    norm_num
/-- The literal outer algorithm may stop by equality at order one, even for a bounded-below
quadratic with globally Lipschitz derivative. Its legal long step has no inner provenance. -/
private theorem bounded_quadratic_stopEqual :
    ContDiff ℝ 1 f ∧ LipschitzWith 1 (deriv f) ∧
      HigherOrderDerivativeFamily f 1 (fun _ => 1) ∧ (∀ x, -2 ≤ f x) ∧
      (∀ δ : ℝ, 0 < δ → (1 / 2 : ℝ)*δ < gapOn (taylorDecrement f 1 0) (closedBall 0 δ)) ∧
      ∃ run : OuterExecution P f 0 1 (fun _ => 1) 0,
        run.last = .stopEqual (run.state 0) ∧ P.q = 1 ∧ P.p = 1 ∧
        run.state 0 = ⟨0, 1, fun _ => 1, 0, true⟩ ∧
        P.epsilon 1 < gapOn (taylorDecrement f 1 0) (closedBall 0 1) := by
  refine ⟨by unfold f; fun_prop, lip, family, ?_, truegap_failure, ?_⟩
  · intro x
    dsimp [f]
    nlinarith [sq_nonneg (x - 2)]
  · let a : OuterState ℝ := ⟨0, 1, fun _ => 1, 0, true⟩
    let trial : ModelStep P f 0 1 (fun _ => 1) := {
      step := 4
      radii := fun _ => 1
      radii_valid := by intro j hj hjq; norm_num
      nonincrease := by
        change model f 1 0 1 4 ≤ model f 1 0 1 0
        rw [model_formula, model_formula]
        norm_num
      direction := fun _ => 0
      quality := Or.inl ⟨by norm_num, rfl⟩ }
    have heq : model f P.p a.point a.sigma trial.step = model f P.p a.point a.sigma 0 := by
      change model f 1 0 1 4 = model f 1 0 1 0
      rw [model_formula, model_formula]
      norm_num
    let run : OuterExecution P f 0 1 (fun _ => 1) 0 := {
      state := fun _ => a
      functionCalls := fun _ => 0
      derivativeCalls := fun _ => 1
      last := .stopEqual a
      initial := by refine ⟨le_rfl, ?_, rfl⟩; intro j hj hjq; norm_num
      valid := by
        intro k hk
        exact ⟨le_rfl, (fun j hj hjq => ⟨by norm_num, le_rfl⟩), Nat.zero_le _, by simp [a]⟩
      transition := by intro k hk; omega
      final := OuterTransition.equal a (fun _ => failed)
        (by norm_num [P, parameters, a]) trial heq }
    refine ⟨run, rfl, rfl, rfl, rfl, ?_⟩
    change (1 / 2 : ℝ) < _
    rw [gap]
    norm_num
/-- A legal equality stop of the literal outer algorithm can return no true approximate
minimizer, even with a bounded-below quadratic, unit radii, and order one. This explains why
an inner-generated correction must retain the actual positive fraction-of-global-decrease
certificate instead of relying only on the outer model-nonincreasing conditions. -/
theorem literal_arqp_equality_stop_counterexample :
    ∃ (f : ℝ → ℝ) (P : Parameters), P.p = 1 ∧ P.q = 1 ∧ P.epsilon 1 = (1 / 2 : ℝ) ∧
      HigherOrderDerivativeFamily f 1 (fun _ => 1) ∧ (∀ x, -2 ≤ f x) ∧
      (∀ δ : ℝ, 0 < δ → (1 / 2 : ℝ) * δ <
        gapOn (taylorDecrement f 1 0) (closedBall 0 δ)) ∧
      ∃ run : OuterExecution P f 0 1 (fun _ => 1) 0,
        run.state 0 = ⟨0, 1, fun _ => 1, 0, true⟩ ∧
        run.last = .stopEqual (run.state 0) := by
  obtain ⟨_, _, hf, hb, hgap, run, hstop, hq, hp, hstate, _⟩ := bounded_quadratic_stopEqual
  exact ⟨f, P, hp, hq, rfl, hf, hb, hgap, run, hstate, hstop⟩

end CartisGouldToint.Chapter12.Section02
