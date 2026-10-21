import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDA

/-!
# A long-step counterexample to the printed ARqpIDA parameter bound

The objective is constant on one-dimensional Euclidean space. Requested accuracy 64 gives
an approximate gradient -64. At σ=32 its actual model minimizer is the long step 2, which
skips the printed Step 2 accuracy check. Here `p=q=1`, so the same run also belongs to
the distinct all-order variant. Its exact-objective ratio is zero and a legal rejected
update gives σ=64, above the printed κ_s-only bound 32. The oracle contract holds at every
positive request, and the detailed inner procedure actually produces the selected step.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter13.Section01
open Optimization InexactRegularization InexactTaylorModels TaylorCriticality

private abbrev Line := EuclideanSpace ℝ (Fin 1)
private def point (t : ℝ) : Line := EuclideanSpace.single 0 t
private def objective (_x : Line) : ℝ := 0
private abbrev constants : ARqpIDAParameters := {
  p := 1
  q := 1
  order_pos := le_rfl
  order_le := le_rfl
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
  kappaInitial := 64
  kappaInitial_nonneg := by norm_num
  kappaStep := 1 / 8
  kappaStep_pos := by norm_num
  gammaAccuracy := 1 / 2
  gammaAccuracy_pos := by norm_num
  gammaAccuracy_lt_one := by norm_num }

private def tensors (h : ℕ → ℝ) : Coefficients Line
  | 1 => (continuousMultilinearCurryFin1 ℝ Line ℝ).symm
      ((-h 1) • EuclideanSpace.proj (0 : Fin 1))
  | _ => 0

private theorem tensors_one (h : ℕ → ℝ) (s : Line) :
    tensors h 1 (fun _ => s) = -h 1 * s 0 := by
  simp [tensors, continuousMultilinearCurryFin1_symm_apply, EuclideanSpace.proj]

private theorem tensors_norm (h : ℕ → ℝ) (hh : 0 ≤ h 1) : ‖tensors h 1‖ ≤ h 1 := by
  have hp : ‖(EuclideanSpace.proj (0 : Fin 1) : Line →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simpa using PiLp.norm_apply_le x (0 : Fin 1)
  change ‖(continuousMultilinearCurryFin1 ℝ Line ℝ).symm
    ((-h 1) • EuclideanSpace.proj (0 : Fin 1))‖ ≤ h 1
  rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hh]
  nlinarith

private def oracle : ImplicitAccuracyOracle objective 1 where
  derivative := fun _ h => tensors h
  accuracy := by
    refine ⟨fun _ => 1, fun _ _ => by norm_num, ?_⟩
    intro x h hh i hi
    have he : i = 1 := by have := Finset.mem_Icc.mp hi; omega
    subst i
    change ‖tensors h 1 - iteratedFDeriv ℝ 1 (fun _ : Line => (0 : ℝ)) x‖ ≤ 1 * h 1
    rw [iteratedFDeriv_const_of_ne (by norm_num : (1 : ℕ) ≠ 0)]
    simpa using tensors_norm h (hh 1 (by simp)).le

private theorem line_norm (x : Line) : ‖x‖ = |x 0| := by
  have he : x = point (x 0) := by ext i; fin_cases i; simp [point]
  rw [he]
  simp [point]

private theorem decrement_formula (s : Line) :
    decrement (tensors (fun _ => 64)) 1 s = 64 * s 0 := by
  simp [decrement, tensors_one]

private theorem model_formula (s : Line) :
    regularizedPolynomial 0 (tensors (fun _ => 64)) 1 32 s =
      -64 * s 0 + 16 * (s 0) ^ 2 := by
  simp [regularizedPolynomial, polynomial, tensors_one, line_norm, sq_abs]
  ring

private theorem witness :
    CoefficientWitness (tensors (fun _ => 64)) 1 1 1 (point 1) := by
  have hg : gapOn (decrement (tensors (fun _ => 64)) 1) (Metric.closedBall 0 1) ≤ 64 := by
    apply gapOn_le ⟨0, by simp⟩
    intro d hd
    rw [decrement_formula]
    have hn : ‖d‖ ≤ 1 := by simpa using hd
    rw [line_norm] at hn
    linarith [le_abs_self (d 0)]
  refine ⟨by simp [point], ?_⟩
  simpa [decrement_formula, point] using hg

private def inspection : Inspection constants 0 (tensors (fun _ => 64)) 32 (fun _ => 1) where
  order := 1
  order_pos := le_rfl
  order_le := by norm_num [constants]
  halvings := fun _ => 0
  search := by
    intro j hj hjq hjo
    have hj1 : j = 1 := by omega
    subst j
    exact {
      direction := fun _ => point 1
      witness := by
        intro k hk
        have he : k = 0 := by omega
        subst k
        simpa only [halvedRadius_zero] using witness
      failed := by intro k hk; omega }
  earlier := by intro j hj hjq hjo; omega
  failed := by
    intro hq
    change (1 : ℝ) * (1 / 2) * halvedRadius 1 0 ^ 1 / (2 * (1! : ℝ)) <
      decrement (tensors (fun _ => 64)) 1 (point 1)
    norm_num [decrement_formula, point]
  retained := by
    intro hq
    change (1 : ℝ) * (1 / 2) * halvedRadius 1 0 ^ 1 / (4 * (1! : ℝ)) ≤
      0 - regularizedPolynomial 0 (tensors (fun _ => 64)) 1 32 (point 1)
    norm_num [model_formula, point]

private def innerState (k : ℕ) : HigherOrderApproximateRegularization.InnerState Line :=
  if k = 0 then ⟨1, fun _ => 1, 0, .minimize⟩ else ⟨1, fun _ => 1, point 2, .returned⟩

private def inner : InnerResult constants 0 (tensors (fun _ => 64)) 32 inspection.radii
    (inspection.direction (by norm_num [inspection, constants,
      constants])) where
  minimizer := point 2
  length := 1
  execution := {
    state := innerState
    is_minimizer := by
      intro t
      change regularizedPolynomial 0 (tensors (fun _ => 64)) 1 32 (point 2) ≤
        regularizedPolynomial 0 (tensors (fun _ => 64)) 1 32 t
      rw [model_formula, model_formula]
      norm_num [point]
      nlinarith [sq_nonneg (t 0 - 2)]
    initial := by
      exact ⟨by norm_num [innerState], by norm_num [innerState], rfl, rfl⟩
    transition := by
      intro k hk
      have hk0 : k = 0 := by omega
      subst k
      have hn : 1 ≤ ‖point 2‖ := by norm_num [point]
      have ht := HigherOrderApproximateRegularization.InnerTransition.minimize
        (P := constants.toParameters)
        (m := regularizedPolynomial 0 (tensors (fun _ => 64)) 1 32)
        (minimizer := point 2) (innerState 0) rfl (point 2) (by
          change (1 : ℝ) * (_ - _) ≤ _ - _
          simp)
      simpa [innerState, hn] using ht }
  returned := rfl
  retained := by
    change regularizedPolynomial 0 (tensors (fun _ => 64)) 1 32 (point 2) ≤
      regularizedPolynomial 0 (tensors (fun _ => 64)) 1 32 (point 1)
    norm_num [model_formula, point]

private def outerState (k : ℕ) : InexactRegularization.State Line :=
  ⟨0, if k = 0 then 32 else 64, fun _ => 1, fun _ => 64, decide (k = 0)⟩

private theorem outerRatio :
    ratio constants objective oracle.derivative (outerState 0) inner.step = 0 := by
  simp [ratio, objective]

private def run : algorithm_13_1_2 constants objective oracle 1 where
  state := outerState
  trial := fun _ => true
  accepted := fun _ => false
  initial_fresh := rfl
  initial_sigma := by norm_num [outerState, constants,
    constants]
  initial_radii := by intro j hj hjq; exact ⟨by norm_num [outerState], by norm_num [outerState]⟩
  initial_tolerance := by intro j hj hjq; norm_num [constants, outerState]
  initial_request := by intro i hi; norm_num [outerState]
  initial_request_le := by intro i hi; norm_num [outerState, constants]
  transition := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    have hu : HigherOrderApproximateRegularization.ParameterUpdate constants.toParameters
        (ratio constants objective oracle.derivative (outerState 0) inner.step)
        (outerState 0).sigma 64 := by
      rw [outerRatio]
      norm_num [HigherOrderApproximateRegularization.ParameterUpdate, constants,
        outerState]
    have ht := Transition.trial (P := constants) (checked := constants.q)
      (f := objective) (oracle := oracle.derivative)
      (outerState 0) inspection (by norm_num [inspection, constants]) inner
      (Or.inl (by change 1 ≤ ‖point 2‖; norm_num [point])) 64 hu
    dsimp only [ratio, objective] at ht
    simp only [sub_self, zero_div] at ht
    norm_num only [constants, ite_false, decide_false] at ht
    have hr : inspection.radii = (fun _ => (1 : ℝ)) := by
      funext j
      simp [Inspection.radii, inspection]
    change Transition constants constants.q objective oracle.derivative (outerState 0)
      ⟨0, 64, inspection.radii, fun _ => 64, false⟩ true false at ht
    rw [hr] at ht
    exact ht

private theorem derivative_zero (i : ℕ) (x : Line) :
    iteratedFDeriv ℝ i objective x = 0 := by
  change iteratedFDeriv ℝ i (0 : Line → ℝ) x = 0
  simp only [iteratedFDeriv_zero, Pi.zero_apply]

private theorem smooth : ImplicitSmoothness objective 1 where
  contDiff := contDiff_const
  lipschitz := by
    intro i hi
    refine ⟨1, le_rfl, ?_⟩
    intro x y
    rw [derivative_zero, derivative_zero, sub_self, norm_zero]
    positivity

/-- The literal ARqpIDA algorithm admits a complete legal Euclidean one-step execution
violating the printed bound in Lemma 13.1.14. The objective is globally smooth and bounded
below; all derivative Lipschitz constants and the fixed oracle error multiplier are one.
The independent initial accuracy bound is 64 and κ_s=1/8. The actual inner minimum is a
long step, so the printed algorithm permits it without the small-step accuracy check. -/
theorem literal_arqpida_long_step_sigma_counterexample :
    ∃ (P : ARqpIDAParameters) (f : EuclideanSpace ℝ (Fin 1) → ℝ)
      (O : ImplicitAccuracyOracle f P.p) (r : algorithm_13_1_2 P f O 1)
      (rAll : arqpida_allp_algorithm P f O 1),
      rAll.state = r.state ∧
      P.p = 1 ∧ P.q = 1 ∧ P.kappaInitial = 64 ∧ P.kappaStep = (1 / 8 : ℝ) ∧
      ImplicitSmoothness f P.p ∧ (∀ x, 0 ≤ f x) ∧
      (∀ i ≤ P.p, ∀ x y,
        ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ 1 * ‖x - y‖) ∧
      (∀ x h, (∀ i ∈ Finset.Icc 1 P.p, 0 < h i) →
        ∀ i ∈ Finset.Icc 1 P.p,
          ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ 1 * h i) ∧
      r.trial 0 = true ∧ r.accepted 0 = false ∧ (r.state 0).sigma = 32 ∧
      (r.state 1).sigma = 64 ∧
      max (r.state 0).sigma
        (P.gamma3 * ((2 * (1 : ℝ) + 4 * ((P.p + 1)! : ℝ) * P.kappaStep * 1) /
          (1 - P.eta2))) < (r.state 1).sigma := by
  refine ⟨constants, objective, oracle, run, run, rfl, rfl, rfl, rfl, rfl, smooth,
    fun _ => le_rfl, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · intro i hi x y
    rw [derivative_zero, derivative_zero, sub_self, norm_zero]
    positivity
  · intro x h hh i hi
    have he : i = 1 := by
      have hmem := Finset.mem_Icc.mp hi
      change 1 ≤ i ∧ i ≤ 1 at hmem
      omega
    subst i
    change ‖tensors h 1 - iteratedFDeriv ℝ 1 (fun _ : Line => (0 : ℝ)) x‖ ≤ 1 * h 1
    rw [iteratedFDeriv_const_of_ne (by norm_num : (1 : ℕ) ≠ 0)]
    simpa using tensors_norm h (hh 1 (by simp)).le
  · norm_num [run, outerState, constants]

end CartisGouldToint.Chapter13.Section01
