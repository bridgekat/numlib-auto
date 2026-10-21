import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDA
import Numlib.Analysis.TwoSine
import Numlib.Analysis.Calculus.EuclideanOne
import Numlib.Optimization.InexactRegularizationCubicInspection
import Numlib.Optimization.InexactRegularizationIsometry
import Numlib.Optimization.InexactRegularizationCubicTrial

/-!
# A bounded cubic stopping fixture for explicit dynamic accuracy

The objective is a bounded sum of two sine harmonics. Its small gradient is hidden by a
uniformly valid tensor oracle. A rejected long model step raises the regularization parameter;
a subsequent accuracy refinement reveals a small cubic coefficient. The operational
fractional-witness inspection can then pass at a radius where the true cubic gap fails.
Both function endpoints are queried at the same positive, model-paid accuracy. The literal
known-error sum fails despite the complete printed request threshold, so the actual source
branch goes to Step 5. This refutes part (ii) of Lemma 13.3.6 while leaving its valid
certification implication and the separate first-attainment complexity question untouched.
-/

set_option exponentiation.threshold 1000

noncomputable section
open scoped Nat ContDiff
namespace CartisGouldToint.Chapter13.Section03.CubicStop
open Optimization InexactRegularization InexactTaylorModels TaylorCriticality

/-- The large initial request and regularization parameter. -/
private def B : ℝ := 2 ^ 100

/-- The final common positive accuracy request. -/
private def H : ℝ := (1 / 2) ^ 360

/-- The true gradient at the origin. -/
private def b : ℝ := (1 / 2) ^ 361

/-- The finite Euclidean line on which the literal source algorithm operates. -/
private abbrev Line := EuclideanSpace ℝ (Fin 1)

/-- Scalar coordinates viewed as Euclidean displacement vectors. -/
private def point (x : ℝ) : Line := EuclideanOne.coord.symm x

/-- The bounded two-harmonic objective on the Euclidean line. -/
private def objective : Line → ℝ := EuclideanOne.lift (TwoSine.objective b)

/-- The explicit algorithm constants used by the cubic stopping fixture. -/
private def constants : Section01.ARqpIDAParameters where
  p := 3
  q := 3
  order_pos := by norm_num
  order_le := le_rfl
  epsilon := fun _ => 1 / 2
  epsilon_pos := by intros; norm_num
  epsilon_lt_one := by intros; norm_num
  theta := 1 / 2
  theta_pos := by norm_num
  theta_lt_one := by norm_num
  fraction := 1 / 8
  fraction_pos := by norm_num
  fraction_le_one := by norm_num
  eta1 := 1 / 4
  eta2 := 1 / 2
  gamma1 := 1 / 2
  gamma2 := 2
  gamma3 := B
  sigmaMin := 1
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma1_lt_one := by norm_num
  one_lt_gamma2 := by norm_num
  gamma2_lt_gamma3 := by norm_num [B]
  sigmaMin_pos := by norm_num
  kappaInitial := B
  kappaInitial_nonneg := by unfold B; positivity
  kappaStep := 1 / 16
  kappaStep_pos := by norm_num
  gammaAccuracy := H / B
  gammaAccuracy_pos := by unfold H B; positivity
  gammaAccuracy_lt_one := by norm_num [H, B, div_pow]

/-- Every true jet through degree three has global Lipschitz constant one. -/
private theorem objective_lipschitz (i : ℕ) (hi : i ≤ 3) (x y : Line) :
    ‖iteratedFDeriv ℝ i objective x - iteratedFDeriv ℝ i objective y‖ ≤ 1 * ‖x - y‖ := by
  have heq (z : Line) : iteratedFDeriv ℝ i objective z =
      (iteratedFDeriv ℝ i (TwoSine.objective b) (EuclideanOne.coord z)).compContinuousLinearMap
        (fun _ => (EuclideanOne.coord : Line →L[ℝ] ℝ)) :=
    (EuclideanOne.coord : Line →L[ℝ] ℝ).iteratedFDeriv_comp_right
      (TwoSine.contDiff b i) z le_rfl
  rw [heq x, heq y]
  have hsub :
      (iteratedFDeriv ℝ i (TwoSine.objective b) (EuclideanOne.coord x)).compContinuousLinearMap
          (fun _ => (EuclideanOne.coord : Line →L[ℝ] ℝ)) -
        (iteratedFDeriv ℝ i (TwoSine.objective b) (EuclideanOne.coord y)).compContinuousLinearMap
          (fun _ => (EuclideanOne.coord : Line →L[ℝ] ℝ)) =
      (iteratedFDeriv ℝ i (TwoSine.objective b) (EuclideanOne.coord x) -
        iteratedFDeriv ℝ i (TwoSine.objective b) (EuclideanOne.coord y)).compContinuousLinearMap
          (fun _ => (EuclideanOne.coord : Line →L[ℝ] ℝ)) := by ext v; rfl
  rw [hsub, ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
  simpa only [← EuclideanOne.coord.map_sub, EuclideanOne.coord.norm_map] using
    TwoSine.iteratedFDeriv_sub_le (b := b) (by unfold b; positivity) (by norm_num [b, div_pow]) hi
      (EuclideanOne.coord x) (EuclideanOne.coord y)

/-- The objective satisfies the source's global smoothness hypothesis. -/
private theorem objective_smooth : Section01.ImplicitSmoothness objective constants.p where
  contDiff := EuclideanOne.contDiff (TwoSine.contDiff b 3)
  lipschitz := fun i hi => ⟨1, le_rfl, objective_lipschitz i hi⟩

/-- The objective is bounded in absolute value, hence satisfies boundedness below as well. -/
private theorem objective_bound (x : Line) : |objective x| ≤ 1 / 16 :=
  TwoSine.abs_objective_le (by unfold b; positivity) (by norm_num [b, div_pow]) _

/-- The exact objective value at the retained point is zero. -/
private theorem objective_zero : objective 0 = 0 := by
  simpa [objective] using (TwoSine.jets_zero b).1

/-- The true Euclidean jets have the scalar origin derivatives in isometric coordinates. -/
private theorem objective_jet_zero (i : ℕ) :
    iteratedFDeriv ℝ i objective 0 = pullCoefficients EuclideanOne.coord
      (fun j => iteratedFDeriv ℝ j (TwoSine.objective b) 0) i := by
  have he := (EuclideanOne.coord : Line →L[ℝ] ℝ).iteratedFDeriv_comp_right
    (TwoSine.contDiff b i) 0 le_rfl
  have hf : (TwoSine.objective b ∘ (EuclideanOne.coord : Line →L[ℝ] ℝ)) = objective := by
    ext z
    rfl
  rw [hf] at he
  simpa only [map_zero, pullCoefficients] using he

/-- The oracle uses exact jets except at the two explicitly requested batches at zero. -/
private def scalarOracle (x : ℝ) (h : ℕ → ℝ) : Coefficients ℝ := by
  classical
  exact if x = 0 ∧ h = (fun _ => B) then cubicCoefficients B else
  if x = 0 ∧ h = (fun _ => H) then cubicCoefficients (1 / 8) else
    fun i => iteratedFDeriv ℝ i (TwoSine.objective b) x

/-- The initial large batch is exactly the negative cubic of magnitude `B`. -/
private theorem scalarOracle_initial : scalarOracle 0 (fun _ => B) = cubicCoefficients B := by
  simp [scalarOracle]

/-- The refined batch has no gradient or Hessian and the exact cubic coefficient. -/
private theorem scalarOracle_refined : scalarOracle 0 (fun _ => H) = cubicCoefficients (1 / 8) := by
  have hne : (fun _ : ℕ => H) ≠ (fun _ => B) := by
    intro he
    have h := congrFun he 1
    norm_num [H, B] at h
  simp [scalarOracle, hne]

/-- Uniform all-point, all-positive-request accuracy with fixed multiplier one. -/
private theorem scalarOracle_accuracy (x : ℝ) (h : ℕ → ℝ)
    (hh : ∀ i ∈ Finset.Icc 1 3, 0 < h i) (i : ℕ) (hi : i ∈ Finset.Icc 1 3) :
    ‖scalarOracle x h i - iteratedFDeriv ℝ i (TwoSine.objective b) x‖ ≤ 1 * h i := by
  classical
  rcases Finset.mem_Icc.mp hi with ⟨hil, hiu⟩
  unfold scalarOracle
  split_ifs with hlarge hsmall
  · rcases hlarge with ⟨rfl, rfl⟩
    rw [cubicCoefficients_equiv, iteratedFDeriv_eq_equiv_comp, Function.comp_apply,
      ← map_sub, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    interval_cases i <;>
      norm_num [TwoSine.iteratedDeriv_objective, TwoSine.secondAmplitude,
        TwoSine.firstAmplitude, B, b, div_pow]
  · rcases hsmall with ⟨rfl, rfl⟩
    rw [cubicCoefficients_equiv, iteratedFDeriv_eq_equiv_comp, Function.comp_apply,
      ← map_sub, LinearIsometryEquiv.norm_map, Real.norm_eq_abs]
    interval_cases i <;>
      norm_num [TwoSine.iteratedDeriv_objective, TwoSine.secondAmplitude,
        TwoSine.firstAmplitude, H, b, div_pow]
  · simpa using (hh i hi).le

/-- The transported global oracle has fixed error multiplier one at every positive request. -/
private theorem oracle_derivative_accuracy (x : Line) (h : ℕ → ℝ)
    (hh : ∀ i ∈ Finset.Icc 1 3, 0 < h i) (i : ℕ) (hi : i ∈ Finset.Icc 1 3) :
    ‖pullCoefficients EuclideanOne.coord (scalarOracle (EuclideanOne.coord x) h) i -
      iteratedFDeriv ℝ i objective x‖ ≤ 1 * h i := by
  have ht : iteratedFDeriv ℝ i objective x = pullCoefficients EuclideanOne.coord
      (fun j => iteratedFDeriv ℝ j (TwoSine.objective b) (EuclideanOne.coord x)) i :=
    (EuclideanOne.coord : Line →L[ℝ] ℝ).iteratedFDeriv_comp_right
      (TwoSine.contDiff b i) x le_rfl
  rw [ht]
  have he : pullCoefficients EuclideanOne.coord (scalarOracle (EuclideanOne.coord x) h) i -
      pullCoefficients EuclideanOne.coord
        (fun j => iteratedFDeriv ℝ j (TwoSine.objective b) (EuclideanOne.coord x)) i =
      pullCoefficients EuclideanOne.coord
        (fun j => scalarOracle (EuclideanOne.coord x) h j -
          iteratedFDeriv ℝ j (TwoSine.objective b) (EuclideanOne.coord x)) i := by ext v; rfl
  rw [he, norm_pullCoefficients]
  exact scalarOracle_accuracy _ h hh i hi

/-- The genuine global oracle on the finite Euclidean line. -/
private def oracle : Section01.ImplicitAccuracyOracle objective constants.p where
  derivative := fun x h => pullCoefficients EuclideanOne.coord
    (scalarOracle (EuclideanOne.coord x) h)
  accuracy := ⟨fun _ => 1, by intros; norm_num, oracle_derivative_accuracy⟩

/-- The initial oracle batch has precisely the transported large cubic coefficients. -/
private theorem oracle_initial : oracle.derivative 0 (fun _ => B) =
    pullCoefficients EuclideanOne.coord (cubicCoefficients B) := by
  simp [oracle, scalarOracle_initial]

/-- The refined oracle batch has precisely the transported small cubic coefficients. -/
private theorem oracle_refined : oracle.derivative 0 (fun _ => H) =
    pullCoefficients EuclideanOne.coord (cubicCoefficients (1 / 8)) := by
  simp [oracle, scalarOracle_refined]

/-- The actual supplied regularized model has its literal scalar quartic expression. -/
private theorem initial_model (σ : ℝ) (s : Line) :
    regularizedPolynomial 0 (oracle.derivative 0 (fun _ => B)) constants.p σ s =
      -B * EuclideanOne.coord s ^ 3 / 6 + σ * EuclideanOne.coord s ^ 4 / 24 := by
  rw [oracle_initial, regularizedPolynomial_pullCoefficients]
  exact regularizedPolynomial_cubicCoefficients B σ _

/-- The initial supplied decrement is its actual pure cubic expression. -/
private theorem initial_decrement (s : Line) :
    decrement (oracle.derivative 0 (fun _ => B)) constants.p s =
      B * EuclideanOne.coord s ^ 3 / 6 := by
  rw [oracle_initial, decrement_pullCoefficients]
  exact decrement_cubicCoefficients B _

/-- The first inspection fails at order three and retains the unit endpoint without halving. -/
private def firstInspection : Inspection constants 0
    (oracle.derivative 0 (fun _ => B)) B (fun _ => 1) :=
  ((cubicFailedInspection constants rfl rfl rfl rfl B B 0 (by norm_num [B])
    (by intro k hk; omega) (by norm_num [B, halvedRadius])).pull EuclideanOne.coord).congr
      rfl oracle_initial.symm

/-- All initial radii are retained by the first inspection. -/
private theorem firstInspection_radii : firstInspection.radii = (fun _ => 1) := by
  unfold firstInspection
  rw [Inspection.congr_radii, Inspection.pull_radii]
  simpa only [halvedRadius_zero, ite_self] using
    cubicFailedInspection_radii constants rfl rfl rfl rfl B B 0 (by norm_num [B])
      (by intro k hk; omega) (by norm_num [B, halvedRadius])

/-- The long step three globally minimizes the actual first quartic model. -/
private theorem first_model_minimum (s : Line) :
    regularizedPolynomial 0 (oracle.derivative 0 (fun _ => B)) constants.p B
        (point 3) ≤
      regularizedPolynomial 0 (oracle.derivative 0 (fun _ => B)) constants.p B s := by
  rw [initial_model, initial_model]
  simp only [point, EuclideanOne.coord.apply_symm_apply]
  have hp := mul_nonneg (sq_nonneg (EuclideanOne.coord s - 3))
    (show 0 ≤ (EuclideanOne.coord s + 1) ^ 2 + 2 by positivity)
  have hh := mul_nonneg (show 0 ≤ B by unfold B; positivity) hp
  nlinarith

/-- The one-transition inner execution chooses the actual global minimizer three. -/
private def firstInner : InnerResult constants 0
    (oracle.derivative 0 (fun _ => B)) B firstInspection.radii
    (firstInspection.direction (by exact le_rfl)) where
  minimizer := point 3
  length := 1
  execution := {
    state := fun k => if k = 0 then ⟨1, fun _ => 1, 0, .minimize⟩
      else ⟨1, fun _ => 1, point 3, .returned⟩
    is_minimizer := first_model_minimum
    initial := ⟨by norm_num, by norm_num, rfl, rfl⟩
    transition := by
      intro k hk
      have he : k = 0 := by omega
      subst k
      have ht := HigherOrderApproximateRegularization.InnerTransition.minimize
        (P := constants.toParameters)
        (m := regularizedPolynomial 0 (oracle.derivative 0 (fun _ => B))
          constants.p B) (minimizer := point 3)
        ⟨1, fun _ => 1, 0, .minimize⟩ rfl (point 3) (by simp)
      simpa [point] using ht }
  returned := rfl
  retained := by
    exact first_model_minimum _

/-- The actual inner result is the long step three. -/
private theorem firstInner_step : firstInner.step = point 3 := rfl

/-- The first inner return retains unit radii on its long-step branch. -/
private theorem firstInner_radii : firstInner.radii = (fun _ => 1) := by
  rw [InnerResult.radii, firstInner_step, ite_eq_left (by norm_num [point])]
  exact firstInspection_radii

/-- The explicit endpoint-error restrictions hold with the smaller step constant. -/
private abbrev edaConstants : ARqpEDAParameters where
  toImplicitParameters := constants
  step_acceptance := by norm_num [constants]
  step_success := by norm_num [constants]

/-- Exact function values and the global unit-error tensor oracle satisfy every positive query. -/
private abbrev knownOracle : ExplicitAccuracyOracle objective edaConstants.p where
  value := fun x _ => objective x
  derivative := oracle.derivative
  value_accuracy := by intro x h hh; simpa using hh.le
  derivative_accuracy := by
    intro x h hh i hi
    simpa only [one_mul, oracle] using oracle_derivative_accuracy x h hh i hi

/-- The initial state requests a fresh tensor batch and has no cached function value. -/
private def initialState : ExplicitRegularization.State Line :=
  ⟨⟨0, B, fun _ => 1, fun _ => B, true⟩, none⟩

/-- Both endpoints are requested at the same positive accuracy, paid by the model decrease. -/
private def firstValue : ExplicitRegularization.ValueTrial edaConstants knownOracle
    initialState firstInner.step where
  request := 1
  request_pos := by norm_num
  budget := by
    change (1 : ℝ) ≤ (1 / 16) * decrement (oracle.derivative 0 (fun _ => B))
      constants.p firstInner.step
    rw [firstInner_step, initial_decrement]
    norm_num [point, B]
  currentRequest := 1
  current_pos := by norm_num
  current_le := le_rfl
  recompute := true
  fresh_request := by intro h; rfl
  cached_request := by intro h; cases h

/-- The actual common-request endpoint ratio is below the rejection threshold. -/
private theorem first_ratio_lt : firstValue.ratio < edaConstants.eta1 := by
  change (objective 0 - objective (0 + firstInner.step)) /
    decrement (oracle.derivative 0 (fun _ => B)) constants.p firstInner.step < 1 / 4
  rw [firstInner_step, objective_zero, initial_decrement]
  simp only [zero_add, point, EuclideanOne.coord.apply_symm_apply]
  have hb := (abs_le.mp (objective_bound (EuclideanOne.coord.symm 3))).1
  apply (div_lt_iff₀ (by unfold B; positivity)).mpr
  norm_num [B] at *
  linarith

/-- Rejection retains the tensor key and stores the actually queried current function value. -/
private def rejectedState : ExplicitRegularization.State Line :=
  ⟨⟨0, B ^ 2, fun _ => 1, fun _ => B, false⟩, some 1⟩

/-- The actual first trial rejects and makes the largest permitted parameter update. -/
private theorem first_transition : ExplicitRegularization.Transition edaConstants knownOracle
    initialState firstInspection rejectedState true false firstValue.queries := by
  have hu : HigherOrderApproximateRegularization.ParameterUpdate constants.toParameters
      firstValue.ratio B (B ^ 2) := by
    have h1 : firstValue.ratio < constants.eta1 := first_ratio_lt
    have h2 : ¬constants.eta2 ≤ firstValue.ratio := by
      have := constants.eta_le; linarith
    rw [HigherOrderApproximateRegularization.ParameterUpdate, ite_eq_right h2,
      ite_eq_right (not_le_of_gt h1)]
    norm_num [constants, B]
  have ha : StepAccurate constants constants.q (fun _ => B) firstInner.step :=
    Or.inl (by rw [firstInner_step]; norm_num [point])
  have ht := ExplicitRegularization.Transition.trial (P := edaConstants) (O := knownOracle)
    (a := initialState) (I := firstInspection) (by exact le_rfl)
    firstInner ha firstValue (B ^ 2) hu
  have hrej : ¬constants.eta1 ≤ firstValue.ratio := not_le_of_gt first_ratio_lt
  dsimp only [ExplicitRegularization.trialState] at ht
  erw [ite_eq_right hrej] at ht
  have hd : decide (constants.eta1 ≤ firstValue.ratio) = false := by simp [hrej]
  erw [hd] at ht
  change ExplicitRegularization.Transition edaConstants knownOracle initialState firstInspection
    ⟨⟨0, B ^ 2, firstInspection.radii, fun _ => B, false⟩, some 1⟩
    true false firstValue.queries at ht
  have he : (⟨⟨0, B ^ 2, firstInspection.radii, fun _ => B, false⟩, some 1⟩ :
      ExplicitRegularization.State Line) = rejectedState := by
    rw [firstInspection_radii]
    rfl
  rw [he] at ht
  exact ht

/-- The second search must halve through radius `2^-98` before its retained endpoint. -/
private theorem second_before (k : ℕ) (hk : k < 99) :
    4 * B ≤ B ^ 2 * halvedRadius 1 k := by
  have hh := halvedRadius_antitone (by norm_num : (0 : ℝ) ≤ 1) (show k ≤ 98 by omega)
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ B ^ 2 by positivity)
  norm_num [B, halvedRadius] at hm ⊢
  linarith

/-- The final second-search endpoint has enough actual quartic-model decrease. -/
private theorem second_last : (1 / 8 : ℝ) * (1 / 2) * halvedRadius 1 99 ^ 3 / 24 ≤
    B * halvedRadius 1 99 ^ 3 / 6 - B ^ 2 * halvedRadius 1 99 ^ 4 / 24 := by
  norm_num [B, halvedRadius]

/-- At the squared parameter the actual Step 1 search returns its order-three endpoint. -/
private def secondInspection : Inspection constants 0
    (oracle.derivative 0 (fun _ => B)) (B ^ 2) (fun _ => 1) :=
  ((cubicFailedInspection constants rfl rfl rfl rfl B (B ^ 2) 99
    (by norm_num [B]) second_before second_last).pull EuclideanOne.coord).congr
      rfl oracle_initial.symm

/-- The second inspection fails at the third order. -/
private theorem secondInspection_order : secondInspection.order = 3 := rfl

/-- Every active initial supplied tensor has norm bounded by the actual request `B`. -/
private theorem initial_coefficient_bound (i : ℕ) (_hi : i ∈ Finset.Icc 1 constants.p) :
    ‖oracle.derivative 0 (fun _ => B) i‖ ≤ B := by
  rw [oracle_initial, norm_pullCoefficients, cubicCoefficients_equiv,
    LinearIsometryEquiv.norm_map]
  split_ifs <;> norm_num [B]

/-- The detailed inner procedure really has a finite returned execution at the squared parameter. -/
private def secondInner : InnerResult constants 0
    (oracle.derivative 0 (fun _ => B)) (B ^ 2) secondInspection.radii
    (secondInspection.direction (by rw [secondInspection_order]; exact le_rfl)) :=
  Classical.choice (exists_innerResult constants 0
    (oracle.derivative 0 (fun _ => B)) (by unfold B; positivity)
    (show 1 ≤ B by norm_num [B]) initial_coefficient_bound secondInspection.radii
    (secondInspection.direction (by rw [secondInspection_order]; exact le_rfl)))

/-- The second actual inner return has strictly negative model value. -/
private theorem secondInner_model_neg :
    regularizedPolynomial 0 (oracle.derivative 0 (fun _ => B)) constants.p
      (B ^ 2) secondInner.step < 0 := by
  have hr := secondInspection.retained (by rw [secondInspection_order]; exact le_rfl)
  have hs := secondInner.retained
  have hd : 0 < constants.fraction * constants.epsilon secondInspection.order *
      halvedRadius 1 (secondInspection.halvings secondInspection.order) ^ secondInspection.order /
        (4 * (secondInspection.order ! : ℝ)) := by
    rw [secondInspection_order]
    change 0 < (1 / 8 : ℝ) * (1 / 2) * halvedRadius 1 99 ^ 3 / (4 * (3! : ℝ))
    have := halvedRadius_pos (by norm_num : (0 : ℝ) < 1) 99
    positivity
  change _ ≤ (0 : ℝ) - regularizedPolynomial 0 _ _ _
    (secondInspection.direction _) at hr
  change regularizedPolynomial 0 _ _ _ secondInner.step ≤ _ at hs
  linarith only [hr, hs, hd]

/-- Every negative-value point of this strongly regularized cubic model is a short step. -/
private theorem secondInner_short : ‖secondInner.step‖ < 1 := by
  have hn := secondInner_model_neg
  rw [initial_model] at hn
  rw [← EuclideanOne.coord.norm_map, Real.norm_eq_abs]
  by_contra hh
  have habs : 1 ≤ |EuclideanOne.coord secondInner.step| := le_of_not_gt hh
  have hB : 0 ≤ B := by unfold B; positivity
  have hB4 : 4 * B ≤ B ^ 2 := by norm_num [B]
  by_cases hx : 0 ≤ EuclideanOne.coord secondInner.step
  · rw [abs_of_nonneg hx] at habs
    have hc : 0 ≤ EuclideanOne.coord secondInner.step ^ 3 := pow_nonneg hx 3
    have hp := mul_nonneg hc (sub_nonneg.mpr habs)
    have he : EuclideanOne.coord secondInner.step ^ 3 ≤
        EuclideanOne.coord secondInner.step ^ 4 := by nlinarith
    have hprod := mul_le_mul hB4 he hc (sq_nonneg B)
    nlinarith
  · have hc : EuclideanOne.coord secondInner.step ^ 3 ≤ 0 :=
      by simpa using (Odd.strictMono_pow (by decide : Odd 3)).monotone (le_of_not_ge hx)
    have hp := mul_nonpos_of_nonneg_of_nonpos hB hc
    have hq : 0 ≤ B ^ 2 * EuclideanOne.coord secondInner.step ^ 4 := by positivity
    nlinarith

/-- The original large request fails the literal Step 2 test at the actual short return. -/
private theorem secondInner_inaccurate : ¬StepAccurate constants constants.q (fun _ => B)
    secondInner.step := by
  rw [StepAccurate.short_iff secondInner_short]
  intro hh
  have h := hh 3 (by simp [constants])
  change B ≤ 1 / 16 * ‖secondInner.step‖ ^ 1 at h
  norm_num only [pow_one] at h
  have hb : 1 ≤ B := by norm_num [B]
  linarith [secondInner_short]

/-- Refining the actual inaccurate short return restores unit radii and keeps the value cache. -/
private def refinedState : ExplicitRegularization.State Line :=
  ⟨⟨0, B ^ 2, fun _ => 1, fun _ => H, true⟩, some 1⟩

/-- The literal EDA Step 2 refinement follows the actual finite inner return. -/
private theorem second_transition : ExplicitRegularization.Transition edaConstants knownOracle
    rejectedState secondInspection refinedState false false [] := by
  have ht := ExplicitRegularization.Transition.refineStep (P := edaConstants) (O := knownOracle)
    (a := rejectedState) (I := secondInspection)
    (by rw [secondInspection_order]; exact le_rfl) secondInner secondInner_inaccurate
  have he : ExplicitRegularization.refine edaConstants rejectedState = refinedState := by
    simp [ExplicitRegularization.refine, InexactRegularization.refine,
      constants, rejectedState, refinedState, B, H]
  rw [he] at ht
  exact ht

/-- The final actual Step 1 inspection uses the source-permitted fractional witness switch. -/
private def terminalInspection : Inspection constants 0
    (oracle.derivative 0 (fun _ => H)) (B ^ 2) (fun _ => 1) :=
  ((cubicPassingInspection constants rfl rfl rfl rfl 190
    (by norm_num [B, halvedRadius])).pull EuclideanOne.coord).congr
      rfl oracle_refined.symm

/-- The last inspection passes all three requested orders and branches to Step 5. -/
private theorem terminalInspection_order : terminalInspection.order = constants.q + 1 := rfl

/-- The returned cubic inspection radius is exactly two to the power minus 190. -/
private theorem terminalInspection_radius : terminalInspection.radii 3 = (1 / 2 : ℝ) ^ 190 := by
  unfold terminalInspection
  rw [Inspection.congr_radii, Inspection.pull_radii]
  simpa only [halvedRadius, one_mul] using
    cubicPassingInspection_radius constants rfl rfl rfl rfl 190
      (σ := B ^ 2) (by norm_num [B, halvedRadius])

/-- The exact true cubic Taylor decrement at zero includes the masked positive gradient. -/
private theorem true_decrement (s : Line) : taylorDecrement objective 3 0 s =
    -b * EuclideanOne.coord s + EuclideanOne.coord s ^ 3 / 48 := by
  rw [← decrement_iteratedFDeriv]
  have ht : (fun i => iteratedFDeriv ℝ i objective 0) =
      pullCoefficients EuclideanOne.coord (fun i => iteratedFDeriv ℝ i (TwoSine.objective b) 0) :=
    funext objective_jet_zero
  rw [ht, decrement_pullCoefficients]
  norm_num [decrement, Finset.sum_Icc_succ_top, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Fin.prod_univ_succ, TwoSine.iteratedDeriv_objective, TwoSine.secondAmplitude,
    TwoSine.firstAmplitude]
  ring

/-- At the final inspected radii the actual true approximate optimality conclusion fails. -/
private theorem terminal_true_quality_fails :
    ¬HigherOrderApproximateRegularization.SatisfiesCriteria constants.toParameters objective 0
      terminalInspection.radii := by
  intro hh
  have hg := hh 3 (by norm_num) (by norm_num [constants])
  erw [terminalInspection_radius] at hg
  let δ : ℝ := (1 / 2) ^ 190
  have hd : point (-δ) ∈ Metric.closedBall (0 : Line) δ := by
    simp [point, δ]
  have hl := le_gapOn (isCompact_closedBall (0 : Line) δ)
    (continuous_taylorDecrement objective 3 0).continuousOn hd
  have hv : constants.epsilon 3 * δ ^ 3 / (3! : ℝ) <
      taylorDecrement objective 3 0 (point (-δ)) := by
    rw [true_decrement]
    norm_num [point, δ, constants, b]
  exact (not_lt_of_ge (hl.trans hg)) hv

/-- The exact printed sigma bound uses the source constants, with objective and error maxima one. -/
private def printedSigma : ℝ := max B (constants.gamma3 *
  ((2 * (1 : ℝ) + 4 * ((constants.p + 1)! : ℝ) * constants.kappaStep * 1) /
    (1 - constants.eta2)))

/-- For this initialized source run the printed bound is sixteen times `B`. -/
private theorem printedSigma_eq : printedSigma = 16 * B := by norm_num [printedSigma, constants, B]

/-- The exact source radius factor includes the coefficient bound `1 + B`. -/
private def printedRadiusFactor : ℝ := constants.fraction * constants.theta /
  (24 * max (1 + 1 * constants.kappaInitial) printedSigma)

/-- The exact source radius factor has the prescribed fixed denominator. -/
private theorem printedRadiusFactor_eq : printedRadiusFactor = 1 / (6144 * B) := by
  norm_num [printedRadiusFactor, printedSigma, constants, B]

/-- The actual refined common request satisfies the printed source accuracy threshold. -/
private theorem source_accuracy_threshold :
    H ≤ constants.fraction * printedRadiusFactor ^ constants.q *
    ((1 / 2 : ℝ) ^ (constants.q + 1)) / (4 * (constants.q ! : ℝ) * 1) := by
  rw [printedRadiusFactor_eq]
  norm_num [constants, H, B]

/-- The actual finite minimum of all three source tolerances is exactly one half. -/
private theorem epsilonMinimum_eq :
    Chapter12.Section02.TRq.epsilonMinimum constants.q constants.epsilon = 1 / 2 := by
  simp [Chapter12.Section02.TRq.epsilonMinimum, constants]

/-- The literal full error sum fails at the actual completed cubic inspection. -/
private theorem terminal_error_fails :
    ¬ExplicitRegularization.ErrorCheck edaConstants refinedState terminalInspection := by
  intro hh
  have h := hh 3 (by norm_num) (by norm_num [edaConstants, constants])
  erw [terminalInspection_radius] at h
  norm_num [refinedState, edaConstants, constants, H, Finset.sum_Icc_succ_top] at h

/-- The source takes Step 1.5.2 to Step 5, retaining the correct pre-inspection state. -/
private theorem terminal_transition : ExplicitRegularization.Transition edaConstants knownOracle
    refinedState terminalInspection (ExplicitRegularization.refine edaConstants refinedState)
      false false [] :=
  ExplicitRegularization.Transition.refineInspection terminalInspection_order terminal_error_fails

/-- The actual states through the final completed all-pass inspection. -/
private def outerState : ℕ → ExplicitRegularization.State Line
  | 0 => initialState
  | 1 => rejectedState
  | _ + 2 => refinedState

/-- Each state stores its actual completed inspection, including the reachable final one. -/
private def edaInspection (k : ℕ) :
    ExplicitRegularization.Inspection edaConstants knownOracle.derivative (outerState k) :=
  match k with
  | 0 => firstInspection
  | 1 => secondInspection
  | _ + 2 => terminalInspection

/-- A complete actual EDA prefix with paid value calls and a genuine Step 2 refinement. -/
private def execution : algorithm_13_3_2 edaConstants knownOracle 2 where
  state := outerState
  inspection := edaInspection
  trial := fun k => decide (k = 0)
  accepted := fun _ => false
  queries := fun k => if k = 0 then firstValue.queries else []
  initial_fresh := rfl
  initial_cache := rfl
  initial_sigma := by norm_num [outerState, initialState, edaConstants, constants, B]
  initial_radii := by
    intro j hj hjq
    exact ⟨by norm_num [outerState, initialState], by norm_num [outerState, initialState]⟩
  initial_tolerance := by
    intro j hj hjq
    norm_num [edaConstants, constants, outerState, initialState]
  initial_request := by intro i hi; norm_num [outerState, initialState, B]
  initial_request_le := by intro i hi; exact le_rfl
  transition := by
    intro k hk
    interval_cases k
    · simpa [outerState, edaInspection] using first_transition
    · simpa [outerState, edaInspection] using second_transition

/-- The prefix has precisely two actual value calls and two eager derivative batches. -/
private theorem execution_counts : execution.functionQueries.length = 2 ∧
    execution.derivativeQueries.length = 2 := by
  norm_num [ExplicitRegularization.Execution.functionQueries,
    ExplicitRegularization.Execution.derivativeQueries, execution, outerState,
    initialState, rejectedState, refinedState, ExplicitRegularization.ValueTrial.queries,
    firstValue, List.range_succ, Finset.range_add_one, Finset.filter_insert,
    Finset.filter_singleton]

/-- A complete bounded Euclidean EDA execution reaches an all-pass Step 1 inspection
at the printed small-request threshold yet fails the literal error sum and branches to
Step 5. The globally valid known-error oracle uses exact function values, with both first
trial endpoints paid at a common positive request. The actual true cubic gap also violates
the claimed optimality at the inspected radius. This refutes part (ii) of Lemma 13.3.6;
the valid certification implication in part (i) is unaffected. No complexity claim follows. -/
theorem literal_arqpeda_cubic_stop_counterexample :
    ∃ (P : ARqpEDAParameters) (f : EuclideanSpace ℝ (Fin 1) → ℝ)
      (O : ExplicitAccuracyOracle f P.p) (r : algorithm_13_3_2 P O 2),
      P.p = 3 ∧ P.q = 3 ∧ Section01.ImplicitSmoothness f P.p ∧
      (∀ x, -(1 / 16 : ℝ) ≤ f x) ∧
      (∀ i ≤ P.p, ∀ x y,
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ 1 * ‖x - y‖) ∧
      (∀ x h, O.value x h = f x) ∧
      r.trial 0 = true ∧ r.accepted 0 = false ∧ r.trial 1 = false ∧
      (r.state 0).fresh = true ∧ (r.state 1).fresh = false ∧ (r.state 2).fresh = true ∧
      r.functionQueries.length = 2 ∧ r.derivativeQueries.length = 2 ∧
      (r.inspection 2).order = P.q + 1 ∧
      ¬ExplicitRegularization.ErrorCheck P (r.state 2) (r.inspection 2) ∧
      ExplicitRegularization.Transition P O (r.state 2) (r.inspection 2)
        (ExplicitRegularization.refine P (r.state 2)) false false [] ∧
      let σmax := max (r.state 0).sigma
        (P.gamma3 * ((2 * (1 : ℝ) + 4 * ((P.p + 1)! : ℝ) * P.kappaStep * 1) /
          (1 - P.eta2)))
      let κδ := P.fraction * P.theta / (24 * max (1 + 1 * P.kappaInitial) σmax)
      let εmin := Chapter12.Section02.TRq.epsilonMinimum P.q P.epsilon
      (∀ i ∈ Finset.Icc 1 P.p, (r.state 2).request i ≤
        P.fraction * κδ ^ P.q * εmin ^ (P.q + 1) / (4 * (P.q ! : ℝ) * 1)) ∧
      ¬HigherOrderApproximateRegularization.SatisfiesCriteria P.toImplicitParameters.toParameters
        f (r.state 2).point (r.inspection 2).radii := by
  refine ⟨edaConstants, objective, knownOracle, execution,
    rfl, rfl, objective_smooth, fun x => (abs_le.mp (objective_bound x)).1,
    objective_lipschitz, fun _ _ => rfl,
    rfl, rfl, rfl, rfl, rfl, rfl,
    execution_counts.1, execution_counts.2, ?_, ?_, ?_, ?_⟩
  · simpa [execution, edaInspection, outerState, refinedState] using terminalInspection_order
  · simpa [execution, edaInspection, outerState, refinedState] using terminal_error_fails
  · simpa [execution, edaInspection, outerState, refinedState] using terminal_transition
  · change (∀ i ∈ Finset.Icc 1 constants.p, H ≤
    constants.fraction * printedRadiusFactor ^ constants.q *
      Chapter12.Section02.TRq.epsilonMinimum constants.q constants.epsilon ^
        (constants.q + 1) / (4 * (constants.q ! : ℝ) * 1)) ∧ _
    rw [epsilonMinimum_eq]
    refine ⟨fun _ _ => source_accuracy_threshold, ?_⟩
    simpa [execution, edaInspection, outerState, refinedState] using terminal_true_quality_fails

end CartisGouldToint.Chapter13.Section03.CubicStop
