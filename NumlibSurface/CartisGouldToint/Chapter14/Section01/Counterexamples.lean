import NumlibSurface.CartisGouldToint.Chapter14.Section01.ARqpC
import Numlib.Optimization.CompositeRegularizationEmbedding
import Numlib.Optimization.QuadraticRegularization
import Numlib.Optimization.HigherOrderApproximateRegularizationSharpness

/-!
# Counterexamples for the supplied literal ARqpC outer conditions

The composition is the nonzero convex norm and the smooth inner map is constantly zero.
Every assumption on the composite objective and actual generalized models is therefore
verified, while the composition remains nonsmooth. The results concern the supplied
transcription's outer conditions, without assuming provenance from its detailed inner loop.
-/

noncomputable section
open scoped Nat NNReal ContDiff
namespace CartisGouldToint.Chapter14.Section01
open Optimization CompositeTaylorModels CompositeRegularization RegularizedTaylorModel
open TaylorCriticality Metric Set
open HigherOrderApproximateRegularization (Parameters OuterState OuterOutcome ValidRadii)

private def composition : LipschitzSubadditiveComposition ℝ := normComposition ℝ
private def innerMap (_ : ℝ) : ℝ := 0

private def params (fraction : ℝ) (hf0 : 0 < fraction) (hf1 : fraction ≤ 1) : Parameters where
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := 3
  sigmaMin := 1
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num
  sigmaMin_pos := by norm_num
  p := 1
  q := 1
  order_pos := le_rfl
  order_le := le_rfl
  epsilon := fun _ => 1 / 2
  epsilon_pos := by intros; norm_num
  epsilon_lt_one := by intros; norm_num
  theta := 1 / 2
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  fraction := fraction
  fraction_pos := hf0
  fraction_le_one := hf1

private def equalityParameters : Parameters := params 1 (by norm_num) le_rfl
private def conservativeParameters : Parameters := params (1 / 200) (by norm_num) (by norm_num)

private theorem composition_nonzero : ∃ z : ℝ, composition z ≠ 0 := by
  exact ⟨1, by norm_num [composition]⟩
private theorem composition_convex : ConvexOn ℝ univ composition := normComposition_convex

private theorem innerMap_smooth : ContDiff ℝ (⊤ : ℕ∞ω) innerMap := contDiff_const

private theorem innerMap_derivative_lipschitz (j : ℕ) (hj : 1 ≤ j) :
    LipschitzWith 0 (iteratedFDeriv ℝ j innerMap) := by
  have he : iteratedFDeriv ℝ j innerMap = 0 := iteratedFDeriv_const_of_ne (by omega) 0
  rw [he]
  exact LipschitzWith.const 0

@[simp] private theorem constant_objective (f : ℝ → ℝ) (x : ℝ) :
    objective f innerMap composition x = f x := objective_const_zero f composition x

@[simp] private theorem constant_model (f : ℝ → ℝ) (p : ℕ) (x σ s : ℝ) :
    CompositeTaylorModels.regularizedModel f innerMap composition p x σ s =
      HigherOrderApproximateRegularization.model f p x σ s :=
  regularizedModel_const_zero f composition p x σ s

@[simp] private theorem dec_const (f : ℝ → ℝ) (j : ℕ) (x d : ℝ) :
    decrement f innerMap composition j x d = taylorDecrement f j x d :=
  decrement_const_zero f composition j x d

@[simp] private theorem dec_const_fun (f : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    decrement f innerMap composition j x = taylorDecrement f j x := funext (dec_const f j x)

private theorem failed_quadratic {P : Parameters} (b x : ℝ)
    (hq : P.q = 1) (hε : P.epsilon 1 = 1 / 2)
    (hstrict : P.fraction * (1 / 2 : ℝ) < -(x - b)) :
    Nonempty (FailedTest P (QuadraticRegularization.objective b) innerMap composition x
      (fun _ => 1)) := by
  refine ⟨⟨1, le_rfl, hq.ge, fun _ => 1, ?_, ?_, ?_⟩⟩
  · intro j hj hj1
    have hjj : j = 1 := by omega
    subst j
    refine ⟨by norm_num, ?_⟩
    simp only [dec_const_fun, dec_const,
      QuadraticRegularization.gap_formula b x 1 (by norm_num),
      QuadraticRegularization.decrement_formula, one_mul, mul_one]
    have hneg : x - b < 0 := by nlinarith [P.fraction_pos]
    rw [abs_of_neg hneg]
    exact mul_le_of_le_one_left (by linarith) P.fraction_le_one
  · intro j hj hj1
    omega
  · simpa only [dec_const, QuadraticRegularization.decrement_formula,
      hε, one_pow, Nat.factorial_one, Nat.cast_one, div_one, mul_one] using hstrict

private def exactSmoothStep (P : Parameters) (hp : P.p = 1) (b x : ℝ) :
    HigherOrderApproximateRegularization.ModelStep P (QuadraticRegularization.objective b)
      x 2 (fun _ => 1) where
  step := (b - x) / 2
  radii := fun _ => 1
  radii_valid := by intro j _ _; norm_num
  nonincrease := by
    rw [hp, QuadraticRegularization.model_formula, QuadraticRegularization.model_formula]
    nlinarith [sq_nonneg (x - b)]
  direction := fun _ => 0
  quality := Or.inr (by
    intro j hj hjq
    have hj1 : j = 1 := by have := P.order_le; omega
    subst j
    constructor
    · refine ⟨by norm_num, ?_⟩
      rw [hp, gapOn_taylorDecrement_one _ _ (by norm_num),
        ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs, QuadraticRegularization.model_deriv]
      simp only [one_mul, taylorDecrement_zero]
      have hz : x - b + 2 * ((b - x) / 2) = 0 := by ring
      rw [hz, abs_zero, mul_zero]
    · rw [taylorDecrement_zero]
      have hε := P.epsilon_pos 1 le_rfl (by omega)
      exact le_of_lt (div_pos (mul_pos (mul_pos (mul_pos P.fraction_pos P.theta_pos) hε)
        (by norm_num)) (by positivity)))

private def exactStep : ModelStep conservativeParameters
    (QuadraticRegularization.objective (1 / 100)) innerMap composition (0 : ℝ) 2 :=
  ModelStep.ofSmooth composition (exactSmoothStep conservativeParameters rfl (1 / 100) 0)

private theorem conservative_transition (x : ℝ)
    (hfail : Nonempty (FailedTest conservativeParameters
      (QuadraticRegularization.objective (1 / 100)) innerMap composition x (fun _ => 1)))
    (hstrict : HigherOrderApproximateRegularization.model
      (QuadraticRegularization.objective (1 / 100)) 1 x 2 ((1 / 100 - x) / 2) <
      HigherOrderApproximateRegularization.model
        (QuadraticRegularization.objective (1 / 100)) 1 x 2 0)
    (hratio : ratio (QuadraticRegularization.objective (1 / 100)) innerMap composition
      1 x ((1 / 100 - x) / 2) = 3 / 4) :
    OuterTransition conservativeParameters (QuadraticRegularization.objective (1 / 100))
      innerMap composition ⟨x, 2, fun _ => 1, 0, true⟩
      (.next ⟨x + (1 / 100 - x) / 2, 2, fun _ => 1, 0, true⟩) 1 1 := by
  let trial := ModelStep.ofSmooth composition
    (exactSmoothStep conservativeParameters rfl (1 / 100) x)
  have hu : HigherOrderApproximateRegularization.ParameterUpdate conservativeParameters
      (ratio (QuadraticRegularization.objective (1 / 100)) innerMap composition
        1 x ((1 / 100 - x) / 2)) 2 2 := by
    rw [hratio]
    norm_num [HigherOrderApproximateRegularization.ParameterUpdate, conservativeParameters, params]
  have ht := OuterTransition.trial ⟨x, 2, fun _ => 1, 0, true⟩ (fun _ => hfail)
    (show 0 ≤ conservativeParameters.p by decide) trial
    (by simpa [trial, ModelStep.ofSmooth, exactSmoothStep, conservativeParameters, params,
      show innerMap = (fun _ : ℝ => (0 : ℝ)) from rfl] using hstrict) 2 hu
  simpa only [trial, ModelStep.ofSmooth, exactSmoothStep,
    show conservativeParameters.p = 1 from rfl, hratio,
    show conservativeParameters.eta1 = 1 / 4 from rfl,
    show (1 / 4 : ℝ) ≤ 3 / 4 by norm_num, ↓reduceIte, Nat.sub_zero] using ht

/-- A nonzero convex norm composition and an actual initialized literal composite execution
can stop by model equality at a point failing every positive-radius first-order criterion.
This refutes the supplied transcription's equality and unconditional return claims. -/
theorem literal_arqpc_equality_stop_counterexample :
    ∃ (P : Parameters) (f : ℝ → ℝ) (c : ℝ → ℝ)
      (h : LipschitzSubadditiveComposition ℝ),
      P.p = 1 ∧ P.q = 1 ∧ P.epsilon 1 = (1 / 2 : ℝ) ∧
      HigherOrderDerivativeFamily f 1 (fun _ => 1) ∧
      ContDiff ℝ (⊤ : ℕ∞ω) c ∧
      (∀ j, 1 ≤ j → LipschitzWith 0 (iteratedFDeriv ℝ j c)) ∧
      (∃ z, h z ≠ 0) ∧ ConvexOn ℝ univ h ∧
      (∀ x, -2 ≤ objective f c h x) ∧
      (∀ δ : ℝ, 0 < δ → (1 / 2 : ℝ) * δ <
        gapOn (decrement f c h 1 0) (closedBall 0 δ)) ∧
      ∃ (run : OuterExecution P f c h 0 1 (fun _ => 1) 0) (out : OuterState ℝ),
        run.state 0 = ⟨0, 1, fun _ => 1, 0, true⟩ ∧
        run.last = .stopEqual out ∧ out.point = 0 ∧ run.functionCount = 1 ∧
        run.derivativeCount = 1 := by
  let f := QuadraticRegularization.objective 2
  let a : OuterState ℝ := ⟨0, 1, fun _ => 1, 0, true⟩
  let trial : ModelStep equalityParameters f innerMap composition 0 1 := {
    step := 4
    radii := fun _ => 1
    radii_valid := by intro j hj hjq; norm_num
    nonincrease := by
      norm_num [f, innerMap, equalityParameters, params, QuadraticRegularization.model_formula,
        QuadraticRegularization.objective]
    direction := fun _ => 0
    quality := Or.inl (by norm_num) }
  have hfail : Nonempty (FailedTest equalityParameters f innerMap composition 0
      (fun _ => 1)) := failed_quadratic 2 0 rfl rfl (by norm_num [equalityParameters, params])
  have heq : regularizedModel f innerMap composition equalityParameters.p a.point a.sigma
      trial.step =
        regularizedModel f innerMap composition equalityParameters.p a.point a.sigma 0 := by
    norm_num [f, innerMap, a, trial, equalityParameters, params,
      QuadraticRegularization.model_formula, QuadraticRegularization.objective]
  let run : OuterExecution equalityParameters f innerMap composition 0 1 (fun _ => 1) 0 := {
    state := fun _ => a
    functionCalls := fun _ => 0
    derivativeCalls := fun _ => 1
    last := .stopEqual a
    initial := by refine ⟨le_rfl, ?_, rfl⟩; intro j hj hjq; norm_num
    valid := by
      intro k hk
      exact ⟨le_rfl, (fun j hj hjq => ⟨by norm_num, le_rfl⟩), Nat.zero_le _, by simp [a]⟩
    transition := by intro k hk; omega
    final := OuterTransition.equal a (fun _ => hfail) (by decide) trial heq }
  refine ⟨equalityParameters, f, innerMap, composition, rfl, rfl, rfl,
    QuadraticRegularization.derivativeFamily 2, innerMap_smooth, innerMap_derivative_lipschitz,
    composition_nonzero, composition_convex, ?_, ?_, run, a, rfl, rfl, rfl, rfl, rfl⟩
  · intro x
    have hx := QuadraticRegularization.objective_lower 2 x
    norm_num at hx
    simpa [f] using hx
  · intro δ hδ
    simp only [dec_const_fun, f,
      QuadraticRegularization.gap_formula 2 0 δ hδ.le]
    norm_num
    linarith

/-- Conservative computed nontermination can occur at true composite approximate optimality.
Two actual accepted transitions, all regularity assumptions, and the printed first-order
transfer, step, and decrease constants are checked with a nonzero convex norm composition. -/
theorem conservative_composite_test_counterexample :
    ∃ (P : Parameters) (f : ℝ → ℝ) (c : ℝ → ℝ)
      (h : LipschitzSubadditiveComposition ℝ) (trial : ModelStep P f c h 0 2),
      P.p = 1 ∧ P.q = 1 ∧ HigherOrderDerivativeFamily f 1 (fun _ => 1) ∧
      ContDiff ℝ (⊤ : ℕ∞ω) c ∧
      (∀ j, 1 ≤ j → LipschitzWith 0 (iteratedFDeriv ℝ j c)) ∧
      (∃ z, h z ≠ 0) ∧ ConvexOn ℝ univ h ∧
      (∀ x, -(1 / 20000 : ℝ) ≤ objective f c h x) ∧ trial.step = 1 / 200 ∧
      trial.radii = (fun _ => 1) ∧
      Nonempty (FailedTest P f c h trial.step trial.radii) ∧
      gapOn (decrement f c h 1 trial.step) (closedBall 0 1) ≤ P.epsilon 1 ∧
      OuterTransition P f c h ⟨0, 2, fun _ => 1, 0, true⟩
        (.next ⟨trial.step, 2, trial.radii, 0, true⟩) 1 1 ∧
      (∃ next, OuterTransition P f c h ⟨trial.step, 2, trial.radii, 0, true⟩ (.next next) 1 1) ∧
      max (2 : ℝ) (P.gamma3 * (1 / (1 - P.eta2))) = 6 ∧
      (1 - P.theta) * P.epsilon 1 > (1 + 6) * ‖trial.step‖ ∧
      ‖trial.step‖ < (1 - P.theta) / (3 * (1 + 6)) * P.epsilon 1 ∧
      decrement f c h 1 0 trial.step <
        P.sigmaMin / 2 * ((1 - P.theta) / (3 * (1 + 6))) ^ 2 * P.epsilon 1 ^ 2 := by
  refine ⟨conservativeParameters, QuadraticRegularization.objective (1 / 100), innerMap,
    composition, exactStep, rfl, rfl, QuadraticRegularization.derivativeFamily (1 / 100),
    innerMap_smooth, innerMap_derivative_lipschitz, composition_nonzero, composition_convex,
    ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hx := QuadraticRegularization.objective_lower (1 / 100) x
    norm_num at hx
    simpa using hx
  · norm_num [exactStep, ModelStep.ofSmooth, exactSmoothStep]
  · convert failed_quadratic (P := conservativeParameters) (1 / 100) (1 / 200) rfl rfl
      (by norm_num [conservativeParameters, params]) using 1
    norm_num [exactStep, ModelStep.ofSmooth, exactSmoothStep]
  · norm_num [dec_const_fun, exactStep, ModelStep.ofSmooth, exactSmoothStep,
      QuadraticRegularization.gap_formula, conservativeParameters, params]
  · convert conservative_transition 0
      (failed_quadratic (P := conservativeParameters) (1 / 100) 0 rfl rfl
        (by norm_num [conservativeParameters, params]))
      (by norm_num [QuadraticRegularization.model_formula, QuadraticRegularization.objective])
      (by norm_num [ratio, QuadraticRegularization.decrement_formula,
        QuadraticRegularization.objective]) using 1
    norm_num [exactStep, ModelStep.ofSmooth, exactSmoothStep]
  · refine ⟨⟨3 / 400, 2, fun _ => 1, 0, true⟩, ?_⟩
    convert conservative_transition (1 / 200)
      (failed_quadratic (P := conservativeParameters) (1 / 100) (1 / 200) rfl rfl
        (by norm_num [conservativeParameters, params]))
      (by norm_num [QuadraticRegularization.model_formula, QuadraticRegularization.objective])
      (by norm_num [ratio, QuadraticRegularization.decrement_formula,
        QuadraticRegularization.objective]) using 1 <;>
      norm_num [exactStep, ModelStep.ofSmooth, exactSmoothStep]
  · norm_num [conservativeParameters, params]
  · norm_num [exactStep, ModelStep.ofSmooth, exactSmoothStep, conservativeParameters, params]
  · norm_num [exactStep, ModelStep.ofSmooth, exactSmoothStep, conservativeParameters, params]
  · norm_num [exactStep, ModelStep.ofSmooth, exactSmoothStep,
      conservativeParameters, params, QuadraticRegularization.decrement_formula]

end CartisGouldToint.Chapter14.Section01
