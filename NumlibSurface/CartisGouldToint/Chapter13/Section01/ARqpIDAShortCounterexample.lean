import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDARadii
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Numlib.Optimization.ExplicitRegularizationTrial

/-!
# Short-step counterexamples to the literal ARqpIDA bounds

The literal order-one accuracy check does not inspect the supplied Hessian when p=2.
An exact linear objective and an inaccurate positive Hessian give a short accepted step
whose new true gradient remains one. All radius-search and inner choices are retained.
The first execution refutes the jet and step-length bounds; a second, shorter execution
refutes both printed decrease bounds. Neither objective satisfies boundedness below.
The reusable `TinyStep.explicitTrial` packages that same actual model and inner execution
with a known-error value oracle and the stricter endpoint-error constant required by EDA.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter13.Section01
open Optimization InexactRegularization InexactTaylorModels TaylorCriticality

private abbrev Line := EuclideanSpace ℝ (Fin 1)
private def point (t : ℝ) : Line := EuclideanSpace.single 0 t
private def projection : Line →L[ℝ] ℝ := EuclideanSpace.proj 0
private def objective : Line → ℝ := projection
private abbrev constants : ARqpIDAParameters := {
  p := 2
  q := 1
  order_pos := le_rfl
  order_le := by norm_num
  epsilon := fun _ => 1 / 2
  epsilon_pos := by intro j hj hjq; norm_num
  epsilon_lt_one := by intro j hj hjq; norm_num
  theta := 1 / 2
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  fraction := 1
  fraction_pos := by norm_num
  fraction_le_one := le_rfl
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
  kappaInitial := 255 / 16
  kappaInitial_nonneg := by norm_num
  kappaStep := 1 / 8
  kappaStep_pos := by norm_num
  gammaAccuracy := 1 / 2
  gammaAccuracy_pos := by norm_num
  gammaAccuracy_lt_one := by norm_num }

private theorem line_norm (x : Line) : ‖x‖ = |x 0| := by
  have he : x = point (x 0) := by ext i; fin_cases i; simp [point]
  rw [he]
  simp [point]

private theorem jet_one (x : Line) (v : Fin 1 → Line) :
    iteratedFDeriv ℝ 1 objective x v = v 0 0 := by
  rw [iteratedFDeriv_one_apply]
  change fderiv ℝ (projection : Line → ℝ) x (v 0) = _
  rw [ContinuousLinearMap.fderiv]
  rfl

private theorem jet_two (x : Line) : iteratedFDeriv ℝ 2 objective x = 0 := by
  ext v
  rw [iteratedFDeriv_succ_apply_right]
  have hf : fderiv ℝ objective = fun _ => projection := by
    funext y
    exact ContinuousLinearMap.fderiv projection
  rw [hf]
  simp [iteratedFDeriv_const_of_ne]

private def squareTensor : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Line) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
    (fun _ => projection)

private theorem squareTensor_apply (v : Fin 2 → Line) :
    squareTensor v = v 0 0 * v 1 0 := by
  simp [squareTensor, projection, EuclideanSpace.proj, Fin.prod_univ_two]

private theorem squareTensor_norm : ‖squareTensor‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro v
  simp only [squareTensor_apply, norm_mul, Real.norm_eq_abs, one_mul, Fin.prod_univ_two]
  exact mul_le_mul (by simp [line_norm])
    (by simp [line_norm]) (abs_nonneg _) (norm_nonneg _)

private def linearTensors (b : ℝ) (x : Line) (h : ℕ → ℝ) : Coefficients Line := fun i =>
  iteratedFDeriv ℝ i objective x +
    if hi : i = 2 then hi ▸ (min (h 2) b • squareTensor) else 0

private theorem linearTensors_error (b : ℝ) (hb : 0 ≤ b) (x : Line) (h : ℕ → ℝ)
    (hh : ∀ i ∈ Finset.Icc 1 2, 0 < h i) (i : ℕ) (hi : i ∈ Finset.Icc 1 2) :
    ‖linearTensors b x h i - iteratedFDeriv ℝ i objective x‖ ≤ 1 * h i := by
  by_cases hi2 : i = 2
  · subst i
    simp only [linearTensors, dite_true, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, one_mul]
    have hn : 0 ≤ min (h 2) b := le_min (hh 2 (by simp)).le hb
    rw [abs_of_nonneg hn]
    exact (mul_le_mul_of_nonneg_left squareTensor_norm hn).trans (by simp)
  · simpa [linearTensors, hi2] using (hh i hi).le

private def linearOracle (b : ℝ) (hb : 0 ≤ b) : ImplicitAccuracyOracle objective 2 where
  derivative := linearTensors b
  accuracy := ⟨fun _ => 1, fun _ _ => by norm_num, linearTensors_error b hb⟩

private theorem scalar_model_minimum (b t : ℝ) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hbt : b * t + t ^ 2 = 1) (x : ℝ) :
    -t + b / 2 * (-t) ^ 2 + |(-t)| ^ 3 / 3 ≤
      x + b / 2 * x ^ 2 + |x| ^ 3 / 3 := by
  rw [abs_neg, abs_of_nonneg ht]
  have hr := congrArg (fun z : ℝ => z * t) hbt
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    have hc := pow_nonneg hx 3
    have hbq := mul_nonneg hb (sq_nonneg x)
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge hx)]
    have hf := mul_nonneg (sq_nonneg (x + t))
      (show 0 ≤ b / 2 + (2 * t - x) / 3 by linarith)
    have hrx := congrArg (fun z : ℝ => z * (x + t)) hbt
    nlinarith

private abbrev tensors := linearTensors (255 / 16)
private abbrev oracle := linearOracle (255 / 16) (by norm_num)

private def request (i : ℕ) : ℝ := if i = 2 then 255 / 16 else 1 / 4096
private def coefficients : Coefficients Line := tensors 0 request

private theorem coefficients_one (s : Line) : coefficients 1 (fun _ => s) = s 0 := by
  simp only [coefficients, tensors, linearTensors,
    show ¬(1 : ℕ) = 2 by decide, dite_false, add_zero]
  change (iteratedFDeriv ℝ 1 objective 0) (fun _ => s) = _
  exact jet_one _ _

private theorem coefficients_two (s : Line) :
    coefficients 2 (fun _ => s) = (255 / 16 : ℝ) * s 0 ^ 2 := by
  simp [coefficients, tensors, linearTensors, jet_two, request, squareTensor_apply, pow_two]

private theorem decrement_one (s : Line) : decrement coefficients 1 s = -s 0 := by
  simp [decrement, coefficients_one]

private theorem model_formula (s : Line) :
    regularizedPolynomial 0 coefficients 2 2 s =
      s 0 + (255 / 32 : ℝ) * s 0 ^ 2 + |s 0| ^ 3 / 3 := by
  norm_num [regularizedPolynomial, polynomial, Finset.sum_Icc_succ_top,
    coefficients_one, coefficients_two, line_norm]
  rw [coefficients_two]
  ring

private theorem model_minimum (s : Line) :
    regularizedPolynomial 0 coefficients 2 2 (point (-1 / 16)) ≤
      regularizedPolynomial 0 coefficients 2 2 s := by
  rw [model_formula, model_formula]
  have hh := scalar_model_minimum (255 / 16) (1 / 16)
    (by norm_num) (by norm_num) (by norm_num) (s 0)
  norm_num [point] at hh ⊢
  exact hh

private theorem witness (δ : ℝ) (hδ : 0 ≤ δ) :
    CoefficientWitness coefficients 1 δ 1 (point (-δ)) := by
  have hg : gapOn (decrement coefficients 1) (Metric.closedBall 0 δ) ≤ δ := by
    apply gapOn_le ⟨0, by simpa using hδ⟩
    intro d hd
    rw [decrement_one]
    have hn : |d 0| ≤ δ := by simpa [line_norm] using hd
    linarith [neg_le_abs (d 0)]
  exact ⟨by simp [point, abs_of_nonneg hδ], by simpa [decrement_one, point] using hg⟩

private def inspection : Inspection constants 0 coefficients 2 (fun _ => 1) where
  order := 1
  order_pos := le_rfl
  order_le := by norm_num [constants]
  halvings := fun _ => 4
  search := by
    intro j hj hjq hjo
    have hj1 : j = 1 := by change j ≤ 1 at hjq; omega
    subst j
    exact {
      direction := fun k => point (-halvedRadius 1 k)
      witness := fun k _ => witness _ (halvedRadius_pos (by norm_num) k).le
      failed := by
        intro k hk
        interval_cases k <;>
          norm_num [constants, halvedRadius, decrement_one, model_formula, point] }
  earlier := by intro j hj hjq hjo; omega
  failed := by intro hq; norm_num [constants, halvedRadius, decrement_one, point]
  retained := by intro hq; norm_num [constants, halvedRadius, model_formula, point]

private def innerState (k : ℕ) : HigherOrderApproximateRegularization.InnerState Line :=
  if k = 0 then ⟨1, fun _ => 1, 0, .minimize⟩
  else ⟨1, fun _ => 1, point (-1 / 16), if k = 1 then .inspect 1 else .returned⟩

private theorem model_local_min :
    IsLocalMin (regularizedPolynomial 0 coefficients 2 2) (point (-1 / 16)) :=
  (isMinOn_univ_iff.mpr model_minimum).isLocalMin (by simp)

private def inner : InnerResult constants 0 coefficients 2 inspection.radii
    (inspection.direction (by norm_num [inspection, constants])) where
  minimizer := point (-1 / 16)
  length := 2
  execution := {
    state := innerState
    is_minimizer := model_minimum
    initial := by exact ⟨by norm_num [innerState], by norm_num [innerState], rfl, rfl⟩
    transition := by
      intro k hk
      interval_cases k
      · have ht := HigherOrderApproximateRegularization.InnerTransition.minimize
          (P := constants.toParameters) (m := regularizedPolynomial 0 coefficients 2 2)
          (minimizer := point (-1 / 16)) (innerState 0) rfl (point (-1 / 16))
          (by change (1 : ℝ) * _ ≤ _; simp)
        norm_num [innerState, point] at ht ⊢
        exact ht
      · have hw : HigherOrderApproximateRegularization.GapWitness
            (regularizedPolynomial 0 coefficients 2 2) 1 (point (-1 / 16)) 1 1 0 := by
          refine ⟨by norm_num, ?_⟩
          have hg := gapOn_taylorDecrement_eq_zero_of_isLocalMin (Or.inl rfl)
            ((contDiff_regularizedPolynomial 0 coefficients 2 2).of_le (by norm_num))
            model_local_min (by norm_num : (0 : ℝ) < 1)
          simp [hg]
        have ht := HigherOrderApproximateRegularization.InnerTransition.pass
          (P := constants.toParameters) (m := regularizedPolynomial 0 coefficients 2 2)
          (minimizer := point (-1 / 16)) (innerState 1) 1 rfl le_rfl le_rfl 0 hw
          (by simp [innerState])
        simpa [innerState, constants] using ht }
  returned := rfl
  retained := by
    change regularizedPolynomial 0 coefficients 2 2 (point (-1 / 16)) ≤ _
    exact model_minimum _


private theorem decrement_two (s : Line) :
    decrement coefficients 2 s = -s 0 - (255 / 32 : ℝ) * s 0 ^ 2 := by
  norm_num [decrement, Finset.sum_Icc_succ_top, coefficients_one]
  rw [coefficients_two]
  ring

private def outerState (k : ℕ) : InexactRegularization.State Line :=
  ⟨if k = 0 then 0 else point (-1 / 16), 2, fun _ => 1, request, true⟩

private theorem outerRatio :
    ratio constants objective oracle.derivative (outerState 0) inner.step = 512 / 257 := by
  change (objective 0 - objective (0 + point (-1 / 16))) /
    decrement coefficients 2 (point (-1 / 16)) = _
  norm_num [objective, projection, EuclideanSpace.proj, decrement_two, point]

private def run : algorithm_13_1_2 constants objective oracle 1 where
  state := outerState
  trial := fun _ => true
  accepted := fun _ => true
  initial_fresh := rfl
  initial_sigma := by norm_num [outerState, constants]
  initial_radii := by intro j hj hjq; exact ⟨by norm_num [outerState], by norm_num [outerState]⟩
  initial_tolerance := by intro j hj hjq; norm_num [constants, outerState]
  initial_request := by intro i hi; norm_num [outerState, request]; split_ifs <;> norm_num
  initial_request_le := by
    intro i hi
    norm_num [outerState, request, constants]
    split_ifs <;> norm_num
  transition := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    have hu : HigherOrderApproximateRegularization.ParameterUpdate constants.toParameters
        (ratio constants objective oracle.derivative (outerState 0) inner.step)
        (outerState 0).sigma 2 := by
      rw [outerRatio]
      norm_num [HigherOrderApproximateRegularization.ParameterUpdate, constants, outerState]
    have ht := Transition.trial (P := constants) (checked := constants.q)
      (f := objective) (oracle := oracle.derivative) (outerState 0) inspection
      (by norm_num [inspection, constants]) inner (Or.inr (by
        intro i hi
        have hi1 : i = 1 := by have hh := Finset.mem_Icc.mp hi; change 1 ≤ i ∧ i ≤ 1 at hh; omega
        subst i
        change (1 / 4096 : ℝ) ≤ 1 / 8 * ‖point (-1 / 16)‖ ^ 2
        norm_num [point])) 2 hu
    have hacc : constants.eta1 ≤
        ratio constants objective oracle.derivative (outerState 0) inner.step := by
      rw [outerRatio]
      norm_num [constants]
    change (1 / 4 : ℝ) ≤
      ratio constants objective oracle.derivative (outerState 0) inner.step at hacc
    split_ifs at ht with hc
    swap
    · exact (hc hacc).elim
    simp only [decide_eq_true hc] at ht
    have hr : inner.radii = (fun _ => (1 : ℝ)) := by
      funext j
      change (if 1 ≤ ‖point (-1 / 16)‖ then inspection.radii else fun _ => (1 : ℝ)) j = 1
      norm_num [point]
    change Transition constants constants.q objective oracle.derivative (outerState 0)
      ⟨0 + inner.step, 2, inner.radii, request, true⟩ true true at ht
    rw [hr] at ht
    convert ht using 1
    simp only [outerState, show ¬(0 + 1 : ℕ) = 0 by decide, ite_false, zero_add]
    rfl

private theorem objective_fderiv (x : Line) : fderiv ℝ objective x = projection :=
  ContinuousLinearMap.fderiv projection

private theorem lipschitz (i : ℕ) (hi : i ≤ 2) (x y : Line) :
    ‖iteratedFDeriv ℝ i objective x - iteratedFDeriv ℝ i objective y‖ ≤ 1 * ‖x - y‖ := by
  interval_cases i
  · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map, one_mul]
    change ‖projection (x - y)‖ ≤ ‖x - y‖
    simpa [projection, EuclideanSpace.proj] using PiLp.norm_apply_le (x - y) (0 : Fin 1)
  · have he : iteratedFDeriv ℝ 1 objective x = iteratedFDeriv ℝ 1 objective y := by
      ext v; rw [jet_one, jet_one]
    rw [he, sub_self, norm_zero]
    positivity
  · rw [jet_two, jet_two, sub_self, norm_zero]
    positivity

private theorem smooth : ImplicitSmoothness objective 2 where
  contDiff := projection.contDiff
  lipschitz := fun i hi => ⟨1, le_rfl, lipschitz i hi⟩

private theorem true_gap_failure :
    ¬HigherOrderApproximateRegularization.SatisfiesCriteria constants.toParameters objective
      (run.state 1).point (run.state 1).radii := by
  intro hh
  have hg := hh 1 le_rfl le_rfl
  have hd : (point (-1)) ∈ Metric.closedBall (0 : Line) 1 := by norm_num [point]
  have he := le_gapOn (isCompact_closedBall (0 : Line) 1)
    (continuous_taylorDecrement objective 1 (point (-1 / 16))).continuousOn hd
  norm_num [taylorDecrement_one, objective_fderiv, projection, EuclideanSpace.proj, point] at he
  change gapOn (taylorDecrement objective 1 (point (-1 / 16))) (Metric.closedBall 0 1) ≤
    (1 / 2 : ℝ) * 1 ^ 1 / (1! : ℝ) at hg
  norm_num [point] at hg
  linarith

/-- A complete legal p=2,q=1 execution of literal Algorithm 13.1.2 refutes the full
inequality in Lemma 13.1.16. The objective is globally linear and satisfies f.D0pL with
all Lipschitz constants one. The all-request oracle has error multiplier one; the
printed q-only accuracy test accepts its inaccurate Hessian. The actual inner minimizer
is -1/16, the exact acceptance ratio is 512/257, and the next true gradient is still one.
The printed sigma maximum is 30, and its right side is 251/2048 < 1/4. -/
theorem literal_arqpida_short_step_jet_counterexample :
    ∃ (P : ARqpIDAParameters) (f : EuclideanSpace ℝ (Fin 1) → ℝ)
      (O : ImplicitAccuracyOracle f P.p) (r : algorithm_13_1_2 P f O 1),
      P.p = 2 ∧ P.q = 1 ∧ ImplicitSmoothness f P.p ∧
      (∀ i ≤ P.p, ∀ x y,
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ 1 * ‖x - y‖) ∧
      (∀ x h, (∀ i ∈ Finset.Icc 1 P.p, 0 < h i) →
        ∀ i ∈ Finset.Icc 1 P.p,
          ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ 1 * h i) ∧
      r.trial 0 = true ∧ r.accepted 0 = true ∧
      ‖(r.state 1).point - (r.state 0).point‖ = (1 / 16 : ℝ) ∧
      (∀ j ≤ 2, (r.state 1).radii j = 1) ∧
      ¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters f
        (r.state 1).point (r.state 1).radii ∧
      ∀ j, 1 ≤ j → j ≤ P.q →
        (1 + max (r.state 0).sigma
          (P.gamma3 * ((2 * (1 : ℝ) + 4 * ((P.p + 1)! : ℝ) * P.kappaStep * 1) /
            (1 - P.eta2))) + 3 * 1 * P.kappaStep) *
          (∑ ℓ ∈ Finset.Icc 1 j, (r.state 1).radii j ^ ℓ / (ℓ ! : ℝ) *
            ‖(r.state 1).point - (r.state 0).point‖ ^ (P.p - ℓ + 1)) <
        (1 - P.theta) * P.epsilon j * (r.state 1).radii j ^ j / (j ! : ℝ) := by
  refine ⟨constants, objective, oracle, run, rfl, rfl, smooth, lipschitz, ?_,
    rfl, rfl, ?_, ?_, true_gap_failure, ?_⟩
  · exact linearTensors_error (255 / 16) (by norm_num)
  · norm_num [run, outerState, point]
  · intro j hj; rfl
  · intro j hj hjq
    have hj1 : j = 1 := by change j ≤ 1 at hjq; omega
    subst j
    norm_num [run, outerState, constants, point]

/-- The same complete literal execution refutes the step lower bound (13.1.80) of
Lemma 13.1.17. Its returned radii are one at orders one and two, so both prescribed
radius conditions (13.1.69) and (13.1.70) hold. The only admissible index is one,
and the printed lower bound is `sqrt (1 / 251)`, strictly larger than `1 / 16`. -/
theorem literal_arqpida_short_step_length_counterexample :
    ∃ (P : ARqpIDAParameters) (f : EuclideanSpace ℝ (Fin 1) → ℝ)
      (O : ImplicitAccuracyOracle f P.p) (r : algorithm_13_1_2 P f O 1),
      P.p = 2 ∧ P.q = 1 ∧ ImplicitSmoothness f P.p ∧
      (∀ i ≤ P.p, ∀ x y,
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ 1 * ‖x - y‖) ∧
      (∀ x h, (∀ i ∈ Finset.Icc 1 P.p, 0 < h i) →
        ∀ i ∈ Finset.Icc 1 P.p,
          ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ 1 * h i) ∧
      r.trial 0 = true ∧ r.accepted 0 = true ∧
      (∀ j ≤ 2, (r.state 1).radii j = 1) ∧
      (∀ j, 3 ≤ j → j ≤ P.q →
        P.fraction * P.theta / (24 * max (1 + P.kappaInitial) (r.state 0).sigma) *
          P.epsilon j ≤ (r.state 1).radii j) ∧
      ¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters f
        (r.state 1).point (r.state 1).radii ∧
      ∀ j, 1 ≤ j → j ≤ P.q →
        ‖(r.state 1).point - (r.state 0).point‖ <
          ((1 - P.theta) / (2 * (j ! : ℝ) *
            (1 + max (r.state 0).sigma
              (P.gamma3 * ((2 * (1 : ℝ) + 4 * ((P.p + 1)! : ℝ) * P.kappaStep * 1) /
                (1 - P.eta2))) + 3 * 1 * P.kappaStep))) ^
            (1 / (P.p - j + 1 : ℕ) : ℝ) *
            P.epsilon j ^ (1 / (P.p - j + 1 : ℕ) : ℝ) := by
  -- Reuse the concrete run, retaining its original all-request validity proof.
  refine ⟨constants, objective, oracle, run, rfl, rfl, smooth, lipschitz, ?_,
    rfl, rfl, ?_, ?_, true_gap_failure, ?_⟩
  · exact linearTensors_error (255 / 16) (by norm_num)
  · intro j hj; rfl
  · intro j hj hjq
    have : j ≤ 1 := hjq
    omega
  · intro j hj hjq
    have hj1 : j = 1 := by change j ≤ 1 at hjq; omega
    subst j
    norm_num [run, outerState, constants, point]
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2 / 251)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
    rw [← Real.sqrt_eq_rpow]
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr (by norm_num)

namespace TinyStep

private abbrev constants : ARqpIDAParameters :=
  { CartisGouldToint.Chapter13.Section01.constants with
    kappaInitial := 1099511627775 / 1048576
    kappaInitial_nonneg := by norm_num }

private abbrev tensors := linearTensors (1099511627775 / 1048576)
private abbrev oracle := linearOracle (1099511627775 / 1048576) (by norm_num)

private def request (i : ℕ) : ℝ := if i = 2 then 1099511627775 / 1048576 else 1 / 17592186044416
private abbrev coefficients : Coefficients Line := tensors 0 request

private theorem coefficients_one (s : Line) : coefficients 1 (fun _ => s) = s 0 := by
  simp only [coefficients, tensors, linearTensors,
    show ¬(1 : ℕ) = 2 by decide, dite_false, add_zero]
  change (iteratedFDeriv ℝ 1 objective 0) (fun _ => s) = _
  exact jet_one _ _

private theorem coefficients_two (s : Line) :
    coefficients 2 (fun _ => s) = (1099511627775 / 1048576 : ℝ) * s 0 ^ 2 := by
  simp [coefficients, tensors, linearTensors, jet_two, request, squareTensor_apply, pow_two]

private theorem decrement_one (s : Line) : decrement coefficients 1 s = -s 0 := by
  simp [decrement, coefficients_one]

private theorem model_formula (s : Line) :
    regularizedPolynomial 0 coefficients 2 2 s =
      s 0 + (1099511627775 / 2097152 : ℝ) * s 0 ^ 2 + |s 0| ^ 3 / 3 := by
  norm_num [regularizedPolynomial, polynomial, Finset.sum_Icc_succ_top,
    coefficients_one, coefficients_two, line_norm]
  rw [coefficients_two]
  ring

private theorem model_minimum (s : Line) :
    regularizedPolynomial 0 coefficients 2 2 (point (-1 / 1048576)) ≤
      regularizedPolynomial 0 coefficients 2 2 s := by
  rw [model_formula, model_formula]
  have hh := scalar_model_minimum (1099511627775 / 1048576) (1 / 1048576)
    (by norm_num) (by norm_num) (by norm_num) (s 0)
  norm_num [point] at hh ⊢
  exact hh

private theorem witness (δ : ℝ) (hδ : 0 ≤ δ) :
    CoefficientWitness coefficients 1 δ 1 (point (-δ)) := by
  have hg : gapOn (decrement coefficients 1) (Metric.closedBall 0 δ) ≤ δ := by
    apply gapOn_le ⟨0, by simpa using hδ⟩
    intro d hd
    rw [decrement_one]
    have hn : |d 0| ≤ δ := by simpa [line_norm] using hd
    linarith [neg_le_abs (d 0)]
  exact ⟨by simp [point, abs_of_nonneg hδ], by simpa [decrement_one, point] using hg⟩

private def inspection : Inspection constants 0 coefficients 2 (fun _ => 1) where
  order := 1
  order_pos := le_rfl
  order_le := by norm_num [constants]
  halvings := fun _ => 20
  search := by
    intro j hj hjq hjo
    have hj1 : j = 1 := by change j ≤ 1 at hjq; omega
    subst j
    exact {
      direction := fun k => point (-halvedRadius 1 k)
      witness := fun k _ => witness _ (halvedRadius_pos (by norm_num) k).le
      failed := by
        intro k hk
        interval_cases k <;>
          norm_num [constants, halvedRadius, decrement_one, model_formula, point] }
  earlier := by intro j hj hjq hjo; omega
  failed := by intro hq; norm_num [constants, halvedRadius, decrement_one, point]
  retained := by intro hq; norm_num [constants, halvedRadius, model_formula, point]

private def innerState (k : ℕ) : HigherOrderApproximateRegularization.InnerState Line :=
  if k = 0 then ⟨1, fun _ => 1, 0, .minimize⟩
  else ⟨1, fun _ => 1, point (-1 / 1048576), if k = 1 then .inspect 1 else .returned⟩

private theorem model_local_min :
    IsLocalMin (regularizedPolynomial 0 coefficients 2 2) (point (-1 / 1048576)) :=
  (isMinOn_univ_iff.mpr model_minimum).isLocalMin (by simp)

private def inner : InnerResult constants 0 coefficients 2 inspection.radii
    (inspection.direction (by norm_num [inspection, constants])) where
  minimizer := point (-1 / 1048576)
  length := 2
  execution := {
    state := innerState
    is_minimizer := model_minimum
    initial := by exact ⟨by norm_num [innerState], by norm_num [innerState], rfl, rfl⟩
    transition := by
      intro k hk
      interval_cases k
      · have ht := HigherOrderApproximateRegularization.InnerTransition.minimize
          (P := constants.toParameters) (m := regularizedPolynomial 0 coefficients 2 2)
          (minimizer := point (-1 / 1048576)) (innerState 0) rfl (point (-1 / 1048576))
          (by change (1 : ℝ) * _ ≤ _; simp)
        norm_num [innerState, point] at ht ⊢
        exact ht
      · have hw : HigherOrderApproximateRegularization.GapWitness
            (regularizedPolynomial 0 coefficients 2 2) 1 (point (-1 / 1048576)) 1 1 0 := by
          refine ⟨by norm_num, ?_⟩
          have hg := gapOn_taylorDecrement_eq_zero_of_isLocalMin (Or.inl rfl)
            ((contDiff_regularizedPolynomial 0 coefficients 2 2).of_le (by norm_num))
            model_local_min (by norm_num : (0 : ℝ) < 1)
          simp [hg]
        have ht := HigherOrderApproximateRegularization.InnerTransition.pass
          (P := constants.toParameters) (m := regularizedPolynomial 0 coefficients 2 2)
          (minimizer := point (-1 / 1048576)) (innerState 1) 1 rfl le_rfl le_rfl 0 hw
          (by simp [innerState])
        simpa [innerState, constants] using ht }
  returned := rfl
  retained := by
    change regularizedPolynomial 0 coefficients 2 2 (point (-1 / 1048576)) ≤ _
    exact model_minimum _


private theorem decrement_two (s : Line) :
    decrement coefficients 2 s = -s 0 - (1099511627775 / 2097152 : ℝ) * s 0 ^ 2 := by
  norm_num [decrement, Finset.sum_Icc_succ_top, coefficients_one]
  rw [coefficients_two]
  ring

private def outerState (k : ℕ) : InexactRegularization.State Line :=
  ⟨if k = 0 then 0 else point (-1 / 1048576), 2, fun _ => 1, request, true⟩

private theorem outerRatio :
    ratio constants objective oracle.derivative (outerState 0) inner.step =
      2199023255552 / 1099511627777 := by
  change (objective 0 - objective (0 + point (-1 / 1048576))) /
    decrement coefficients 2 (point (-1 / 1048576)) = _
  norm_num [objective, projection, EuclideanSpace.proj, decrement_two, point]

private def run : algorithm_13_1_2 constants objective oracle 1 where
  state := outerState
  trial := fun _ => true
  accepted := fun _ => true
  initial_fresh := rfl
  initial_sigma := by norm_num [outerState, constants]
  initial_radii := by intro j hj hjq; exact ⟨by norm_num [outerState], by norm_num [outerState]⟩
  initial_tolerance := by intro j hj hjq; norm_num [constants, outerState]
  initial_request := by intro i hi; norm_num [outerState, request]; split_ifs <;> norm_num
  initial_request_le := by
    intro i hi
    norm_num [outerState, request, constants]
    split_ifs <;> norm_num
  transition := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    have hu : HigherOrderApproximateRegularization.ParameterUpdate constants.toParameters
        (ratio constants objective oracle.derivative (outerState 0) inner.step)
        (outerState 0).sigma 2 := by
      rw [outerRatio]
      norm_num [HigherOrderApproximateRegularization.ParameterUpdate, constants, outerState]
    have ht := Transition.trial (P := constants) (checked := constants.q)
      (f := objective) (oracle := oracle.derivative) (outerState 0) inspection
      (by norm_num [inspection, constants]) inner (Or.inr (by
        intro i hi
        have hi1 : i = 1 := by have hh := Finset.mem_Icc.mp hi; change 1 ≤ i ∧ i ≤ 1 at hh; omega
        subst i
        change (1 / 17592186044416 : ℝ) ≤ 1 / 8 * ‖point (-1 / 1048576)‖ ^ 2
        norm_num [point])) 2 hu
    have hacc : constants.eta1 ≤
        ratio constants objective oracle.derivative (outerState 0) inner.step := by
      rw [outerRatio]
      norm_num [constants]
    change (1 / 4 : ℝ) ≤
      ratio constants objective oracle.derivative (outerState 0) inner.step at hacc
    split_ifs at ht with hc
    swap
    · exact (hc hacc).elim
    simp only [decide_eq_true hc] at ht
    have hr : inner.radii = (fun _ => (1 : ℝ)) := by
      funext j
      change (if 1 ≤ ‖point (-1 / 1048576)‖ then inspection.radii else fun _ => (1 : ℝ)) j = 1
      norm_num [point]
    change Transition constants constants.q objective oracle.derivative (outerState 0)
      ⟨0 + inner.step, 2, inner.radii, request, true⟩ true true at ht
    rw [hr] at ht
    convert ht using 1
    simp only [outerState, show ¬(0 + 1 : ℕ) = 0 by decide, ite_false, zero_add]
    rfl

private theorem true_gap_failure :
    ¬HigherOrderApproximateRegularization.SatisfiesCriteria constants.toParameters objective
      (run.state 1).point (run.state 1).radii := by
  intro hh
  have hg := hh 1 le_rfl le_rfl
  have hd : (point (-1)) ∈ Metric.closedBall (0 : Line) 1 := by norm_num [point]
  have he := le_gapOn (isCompact_closedBall (0 : Line) 1)
    (continuous_taylorDecrement objective 1 (point (-1 / 1048576))).continuousOn hd
  norm_num [taylorDecrement_one, objective_fderiv, projection, EuclideanSpace.proj, point] at he
  change gapOn (taylorDecrement objective 1 (point (-1 / 1048576))) (Metric.closedBall 0 1) ≤
    (1 / 2 : ℝ) * 1 ^ 1 / (1! : ℝ) at hg
  norm_num [point] at hg
  linarith

/-- A complete legal literal execution with twenty first-search halvings refutes both
printed decrease bounds (13.1.82) and (13.1.83) in Lemma 13.1.18. The objective and its
true gradient remain linear and exact, while the unchecked Hessian forces a step of
length `2⁻²⁰`. The printed decrease constant is independent of that Hessian request. -/
theorem literal_arqpida_tiny_step_decrease_counterexample :
    ∃ (P : ARqpIDAParameters) (f : EuclideanSpace ℝ (Fin 1) → ℝ)
      (O : ImplicitAccuracyOracle f P.p) (r : algorithm_13_1_2 P f O 1),
      P.p = 2 ∧ P.q = 1 ∧ ImplicitSmoothness f P.p ∧
      (∀ i ≤ P.p, ∀ x y,
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ 1 * ‖x - y‖) ∧
      (∀ x h, (∀ i ∈ Finset.Icc 1 P.p, 0 < h i) →
        ∀ i ∈ Finset.Icc 1 P.p,
          ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ 1 * h i) ∧
      r.trial 0 = true ∧ r.accepted 0 = true ∧
      (∀ j ≤ 2, (r.state 1).radii j = 1) ∧
      (∀ k ≤ 1, ¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters f
        (r.state k).point (r.state k).radii) ∧
      let σmax := max (r.state 0).sigma
        (P.gamma3 * ((2 * (1 : ℝ) + 4 * ((P.p + 1)! : ℝ) * P.kappaStep * 1) /
          (1 - P.eta2)))
      let κ := P.sigmaMin / ((P.p + 1)! : ℝ) *
        ((1 - P.theta) / (2 * (P.q ! : ℝ) *
          (1 + σmax + 3 * 1 * P.kappaStep))) ^
          (((P.p + 1 : ℕ) : ℝ) / (P.p - P.q + 1 : ℕ))
      decrement (O.derivative (r.state 0).point (r.state 0).request) P.p
          ((r.state 1).point - (r.state 0).point) <
        κ * P.epsilon 1 ^ (((P.p + 1 : ℕ) : ℝ) / (P.p - 1 + 1 : ℕ)) ∧
      f (r.state 0).point - f (r.state 1).point <
        P.eta1 / 2 * κ * P.epsilon 1 ^
          (((P.p + 1 : ℕ) : ℝ) / (P.p - 1 + 1 : ℕ)) := by
  refine ⟨constants, objective, oracle, run, rfl, rfl, smooth, lipschitz, ?_,
    rfl, rfl, ?_, ?_, ?_⟩
  · exact linearTensors_error (1099511627775 / 1048576) (by norm_num)
  · intro j hj; rfl
  · intro k hk
    interval_cases k
    · intro hh
      have hg := hh 1 le_rfl le_rfl
      have hd : (point (-1)) ∈ Metric.closedBall (0 : Line) 1 := by norm_num [point]
      have he := le_gapOn (isCompact_closedBall (0 : Line) 1)
        (continuous_taylorDecrement objective 1 0).continuousOn hd
      norm_num [taylorDecrement_one, objective_fderiv, projection, EuclideanSpace.proj, point] at he
      change gapOn (taylorDecrement objective 1 0) (Metric.closedBall 0 1) ≤
        (1 / 2 : ℝ) * 1 ^ 1 / (1! : ℝ) at hg
      norm_num at hg
      linarith
    · exact true_gap_failure
  · dsimp only
    simp only [run, outerState, ite_true, show ¬(1 : ℕ) = 0 by decide, ite_false, sub_zero]
    change decrement coefficients 2 (point (-1 / 1048576)) < _ ∧ _
    rw [decrement_two]
    norm_num [run, outerState, constants, CartisGouldToint.Chapter13.Section01.constants,
      objective, projection, EuclideanSpace.proj, point]
    simp_rw [mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2 / 251)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
    have hroot : (1 / 16 : ℝ) < Real.sqrt (1 / 251) :=
      (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr (by norm_num)
    have hpow : (1 / 4096 : ℝ) < (1 / 251 : ℝ) ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 251), Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      nlinarith
    constructor <;> nlinarith


private abbrev explicitConstants : ExplicitRegularization.Parameters := {
  toImplicitParameters := { constants with
    kappaStep := 1 / 16
    kappaStep_pos := by norm_num }
  step_acceptance := by norm_num [constants, Section01.constants]
  step_success := by norm_num [constants, Section01.constants] }

private abbrev explicitOracle : ExplicitRegularization.Oracle objective 2 where
  value := fun x _ => objective x
  derivative := fun _ h => tensors 0 h
  value_accuracy := by intro x h hh; simpa using hh.le
  derivative_accuracy := by
    intro x h hh i hi
    have hl := linearTensors_error (1099511627775 / 1048576) (by norm_num) 0 h hh i hi
    have hh' := Finset.mem_Icc.mp hi
    change 1 ≤ i ∧ i ≤ 2 at hh'
    rcases hh' with ⟨hi1, hi2⟩
    interval_cases i
    · have he : iteratedFDeriv ℝ 1 objective x = iteratedFDeriv ℝ 1 objective 0 := by
        ext v; rw [jet_one, jet_one]
      simpa only [he, one_mul] using hl
    · simpa only [jet_two, one_mul] using hl

private def explicitInspection : Inspection explicitConstants.toImplicitParameters 0
    coefficients 2 (fun _ => 1) where
  order := inspection.order
  order_pos := inspection.order_pos
  order_le := inspection.order_le
  halvings := inspection.halvings
  search := inspection.search
  earlier := inspection.earlier
  failed := inspection.failed
  retained := inspection.retained

private def explicitInner : InnerResult explicitConstants.toImplicitParameters 0 coefficients 2
    explicitInspection.radii (explicitInspection.direction (by norm_num [explicitInspection,
      inspection, explicitConstants, constants, Section01.constants])) where
  minimizer := inner.minimizer
  length := inner.length
  execution := inner.execution
  returned := inner.returned
  retained := inner.retained

private abbrev explicitInitial : ExplicitRegularization.State Line :=
  ⟨⟨0, 2, fun _ => 1, request, true⟩, none⟩

private def explicitValues : ExplicitRegularization.ValueTrial explicitConstants explicitOracle
    explicitInitial explicitInner.step where
  request := 1 / 67108864
  request_pos := by norm_num
  budget := by
    change (1 / 67108864 : ℝ) ≤ 1 / 16 * decrement coefficients 2 (point (-1 / 1048576))
    norm_num [decrement_two, point]
  currentRequest := 1 / 67108864
  current_pos := by norm_num
  current_le := le_rfl
  recompute := true
  fresh_request := by intro h; rfl
  cached_request := by intro h; cases h

private theorem explicitRatio : explicitValues.ratio = 2199023255552 / 1099511627777 := by
  change (objective 0 - objective (0 + point (-1 / 1048576))) /
    decrement coefficients 2 (point (-1 / 1048576)) = _
  norm_num [objective, projection, EuclideanSpace.proj, decrement_two, point]

private theorem explicitAccepted : explicitConstants.eta1 ≤ explicitValues.ratio := by
  rw [explicitRatio]
  norm_num [explicitConstants, constants, Section01.constants]

private theorem explicitRadii : explicitInner.radii = (fun _ => (1 : ℝ)) := by
  funext j
  change (if 1 ≤ ‖point (-1 / 1048576)‖ then explicitInspection.radii
    else fun _ => (1 : ℝ)) j = 1
  norm_num [point]

private theorem explicitNext_eq
    (hq : explicitInspection.order ≤ explicitConstants.q) :
    ExplicitRegularization.trialState (P := explicitConstants) (O := explicitOracle)
      explicitInitial explicitInspection hq explicitInner
      explicitValues 2 =
        ⟨⟨point (-1 / 1048576), 2, fun _ => 1, request, true⟩, some (1 / 67108864)⟩ := by
  rw [ExplicitRegularization.trialState, ite_eq_left explicitAccepted, explicitRadii]
  simp only [show explicitInner.step = point (-1 / 1048576) from rfl, zero_add]
  rfl

/-- The tiny linear-model fixture also supplies a legal known-error trial. Its unit-error
oracle is valid at every positive request, its scalar values are exact, and its common
positive endpoint request makes both actual value calls. The stricter constant `1/16`
satisfies both endpoint-error restrictions without changing the model or inner execution. -/
def explicitTrial : ExplicitRegularization.TrialData (EuclideanSpace ℝ (Fin 1)) where
  parameters := explicitConstants
  objective := objective
  oracle := explicitOracle
  initial := explicitInitial
  inspection := explicitInspection
  failed := by norm_num [explicitInspection, inspection, explicitConstants, constants,
    Section01.constants]
  inner := explicitInner
  accurate := Or.inr (by
    intro i hi
    have hi1 : i = 1 := by
      have hh := Finset.mem_Icc.mp hi
      change 1 ≤ i ∧ i ≤ 1 at hh
      omega
    subst i
    change (1 / 17592186044416 : ℝ) ≤ 1 / 16 * ‖point (-1 / 1048576)‖ ^ 2
    norm_num [point])
  values := explicitValues
  nextSigma := 2
  update := by
    rw [explicitRatio]
    norm_num [HigherOrderApproximateRegularization.ParameterUpdate, explicitConstants,
      constants, Section01.constants, explicitInitial, outerState]
  terminalInspection := by
    rw [explicitNext_eq]
    exact explicitInspection
  initial_fresh := rfl
  initial_cache := rfl
  initial_sigma := by norm_num [explicitConstants, constants, Section01.constants,
    explicitInitial, outerState]
  initial_radii := by
    intro j hj hjq
    exact ⟨by norm_num [explicitInitial, outerState], by norm_num [explicitInitial, outerState]⟩
  initial_tolerance := by
    intro j hj hjq
    norm_num [explicitConstants, constants, Section01.constants, explicitInitial, outerState]
  initial_request := by
    intro i hi
    norm_num [explicitInitial, outerState, request]
    split_ifs <;> norm_num
  initial_request_le := by
    intro i hi
    norm_num [explicitInitial, outerState, request, explicitConstants, constants]
    split_ifs <;> norm_num

/-- Characterization of the reusable explicit trial: all active true gaps fail, both
endpoint calls are actual, and both printed decrease expressions exceed the actual ones.
The Lipschitz constants and every known tensor-error multiplier are one. -/
theorem explicitTrial_properties :
    let d := explicitTrial
    let P := d.parameters
    let f := d.objective
    let O := d.oracle
    let r := d.execution
    P.p = 2 ∧ P.q = 1 ∧ Section01.ImplicitSmoothness f P.p ∧
    (∀ i ≤ P.p, ∀ x y,
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ 1 * ‖x - y‖) ∧
    (∀ x h, O.value x h = f x) ∧
    r.trial 0 = true ∧ r.accepted 0 = true ∧ (r.queries 0).length = 2 ∧
    (∀ j ≤ 2, (r.state 1).radii j = 1) ∧
    (∀ j, 3 ≤ j → j ≤ P.q →
      P.fraction * P.theta / (24 * max (1 + P.kappaInitial) (r.state 0).sigma) *
        P.epsilon j ≤ (r.state 1).radii j) ∧
    (∀ k ≤ 1, ¬HigherOrderApproximateRegularization.SatisfiesCriteria
      P.toImplicitParameters.toParameters f (r.state k).point (r.state k).radii) ∧
    let σmax := max (r.state 0).sigma
      (P.gamma3 * ((2 * (1 : ℝ) + 4 * ((P.p + 1)! : ℝ) * P.kappaStep) /
        (1 - P.eta2)))
    let κ := P.sigmaMin / ((P.p + 1)! : ℝ) *
      ((1 - P.theta) / (2 * (P.q ! : ℝ) *
        (1 + σmax + 3 * P.kappaStep))) ^
        (((P.p + 1 : ℕ) : ℝ) / (P.p - P.q + 1 : ℕ))
    decrement (O.derivative (r.state 0).point (r.state 0).request) P.p
        ((r.state 1).point - (r.state 0).point) <
      κ * P.epsilon 1 ^ (((P.p + 1 : ℕ) : ℝ) / (P.p - 1 + 1 : ℕ)) ∧
    f (r.state 0).point - f (r.state 1).point <
      P.eta1 / 2 * κ * P.epsilon 1 ^
        (((P.p + 1 : ℕ) : ℝ) / (P.p - 1 + 1 : ℕ)) := by
  dsimp only
  have hs0 : explicitTrial.execution.state 0 = explicitInitial := rfl
  have hs1 : explicitTrial.execution.state 1 =
      ⟨⟨point (-1 / 1048576), 2, fun _ => 1, request, true⟩, some (1 / 67108864)⟩ := by
    exact explicitNext_eq _
  refine ⟨rfl, rfl, smooth, lipschitz, fun _ _ => rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · change decide (explicitConstants.eta1 ≤ explicitValues.ratio) = true
    exact decide_eq_true explicitAccepted
  · intro j hj
    rw [hs1]
  · intro j hj hjq
    change j ≤ 1 at hjq
    omega
  · intro k hk
    interval_cases k
    · rw [hs0]
      intro hh
      have hg := hh 1 le_rfl le_rfl
      have hd : (point (-1)) ∈ Metric.closedBall (0 : Line) 1 := by norm_num [point]
      have he := le_gapOn (isCompact_closedBall (0 : Line) 1)
        (continuous_taylorDecrement objective 1 0).continuousOn hd
      norm_num [taylorDecrement_one, objective_fderiv, projection, EuclideanSpace.proj, point] at he
      change gapOn (taylorDecrement objective 1 0) (Metric.closedBall 0 1) ≤
        (1 / 2 : ℝ) * 1 ^ 1 / (1! : ℝ) at hg
      norm_num at hg
      linarith
    · rw [hs1]
      exact true_gap_failure
  · rw [hs0, hs1]
    simp only [sub_zero]
    change decrement coefficients 2 (point (-1 / 1048576)) < _ ∧ _
    rw [decrement_two]
    norm_num [explicitTrial, explicitConstants, constants, Section01.constants, explicitInitial,
      outerState, objective, projection, EuclideanSpace.proj, point]
    simp_rw [mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4 / 355)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
    have hroot : (1 / 16 : ℝ) < Real.sqrt (2 / 355) :=
      (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr (by norm_num)
    have hpow : (1 / 4096 : ℝ) < (2 / 355 : ℝ) ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2 / 355), Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      nlinarith
    constructor <;> nlinarith

end TinyStep

end CartisGouldToint.Chapter13.Section01
