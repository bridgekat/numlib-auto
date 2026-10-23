import Numlib.Optimization.Regularization.Convex.DerivativeRun
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Independent constrained third-order tolerances may admit no target

The bounded-below quartic has a globally Lipschitz actual third derivative.
Near its minimizer, nonzero unit-ball directions pass both finite lower
derivative restrictions while their signed third diagonal stays above a fixed
third tolerance. The source stopping target is therefore empty. At the actual
global minimizer its regularized cubic model equals the entire objective, so
the source strict-improvement step is unavailable although its stop fails.
-/

namespace ConvexRegularization.TargetObstruction
open Set Polynomial TaylorModel

/-- The fixed bounded-below scalar quartic supplying the counterexample. -/
noncomputable def polynomial : ℝ[X] := C (1 / 2) * X^2 + C (1 / 6) * X^3 + C (1 / 24) * X^4
/-- The actual scalar polynomial objective, evaluated without supplied derivative data. -/
noncomputable def objective (x : ℝ) : ℝ := polynomial.eval x

/-- The exact scalar objective formula. -/
theorem objective_value (x : ℝ) : objective x = x^2 / 2 + x^3 / 6 + x^4 / 24 := by
  simp [objective,polynomial]; ring

/-- The actual first, second and third scalar derivatives of the quartic. -/
theorem jets (x : ℝ) :
    iteratedDeriv 1 objective x = x + x^2 / 2 + x^3 / 6 ∧
    iteratedDeriv 2 objective x = 1 + x + x^2 / 2 ∧
    iteratedDeriv 3 objective x = 1 + x := by
  have he : objective = fun x => polynomial.eval x := rfl
  rw [he,Polynomial.iteratedDeriv_eval,Polynomial.iteratedDeriv_eval,
    Polynomial.iteratedDeriv_eval]
  norm_num [polynomial,Function.iterate_succ_apply',Polynomial.derivative_mul,
    Polynomial.derivative_pow,Polynomial.derivative_add]
  constructor
  · ring
  constructor <;> ring

/-- The fixed polynomial has the source third-order continuous differentiability. -/
theorem objective_contDiff : ContDiff ℝ 3 objective := by
  rw [show objective = fun x => x^2 / 2 + x^3 / 6 + x^4 / 24 from funext objective_value]
  fun_prop

/-- The scalar objective is globally bounded below by zero. -/
theorem objective_nonneg (x : ℝ) : 0 ≤ objective x := by
  rw [objective_value]
  have he : x^2 / 2 + x^3 / 6 + x^4 / 24 = x^2 * ((x + 2)^2 / 24 + 1 / 3) := by ring
  rw [he]; positivity

/-- The genuine scalar third derivative tensor is globally Lipschitz with constant one. -/
theorem third_lipschitz (x y : ℝ) :
    ‖iteratedFDeriv ℝ 3 objective x - iteratedFDeriv ℝ 3 objective y‖ ≤ ‖x - y‖ := by
  rw [norm_iteratedFDeriv_sub_eq_norm_iteratedDeriv_sub,(jets x).2.2,(jets y).2.2]
  simp only [add_sub_add_left_eq_sub]
  rfl

/-- Every point satisfying the actual first-order tolerance lies near the global minimizer. -/
theorem first_small_implies_near {x : ℝ}
    (hx : constrainedCriticality objective 1 univ x 1 ≤ (1 / 100 : ℝ)) : |x| ≤ 1 / 2 := by
  rw [constrainedCriticality_univ,TaylorModel.criticality_one _ _ zero_lt_one,
    gradient_eq_deriv,Real.norm_eq_abs,one_mul,←iteratedDeriv_one,(jets x).1] at hx
  simp only [starRingEnd_apply,star_trivial] at hx
  have hbracket : 5 / 8 ≤ 1 + x / 2 + x^2 / 6 := by nlinarith [sq_nonneg (x + 3 / 2)]
  have he : |x + x^2 / 2 + x^3 / 6| = |x| * (1 + x / 2 + x^2 / 6) := by
    rw [show x + x^2 / 2 + x^3 / 6 = x * (1 + x / 2 + x^2 / 6) by ring,abs_mul,
      abs_of_nonneg (show 0 ≤ 1 + x / 2 + x^2 / 6 by linarith)]
  rw [he] at hx
  nlinarith [abs_nonneg x]


/-- A fixed independent third tolerance fails at every scalar first-order approximate minimizer. -/
theorem scalar_no_target {x : ℝ}
    (hx : constrainedCriticality objective 1 univ x 1 ≤ (1 / 100 : ℝ)) :
    (1 / 10000 : ℝ) < objectiveDerivativeCriticality objective univ x
      ((1 / 2) * (1 / 100)) ((1 / 2) * (1 / 2)) 2 := by
  have hn := first_small_implies_near hx
  have hx' : |deriv objective x| ≤ (1 / 100 : ℝ) := by
    rw [constrainedCriticality_univ,TaylorModel.criticality_one _ _ zero_lt_one,
      gradient_eq_deriv,Real.norm_eq_abs,one_mul] at hx
    simpa only [starRingEnd_apply,star_trivial] using hx
  have hd : (-1 / 10 : ℝ) ∈ secondRestrictedDirections objective
      (feasibleDisplacements univ x) x ((1 / 2) * (1 / 100)) ((1 / 2) * (1 / 2)) := by
    refine ⟨⟨by simp [feasibleDisplacements],?_⟩,?_⟩
    · rw [fderiv_eq_deriv_mul,abs_mul]
      norm_num
      nlinarith
    · rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,(jets x).2.1]
      simp only [Fin.prod_const,smul_eq_mul]
      have hb : |1 + x + x^2 / 2| ≤ 2 := by
        apply abs_le.mpr
        constructor <;> nlinarith [(abs_le.mp hn).1,(abs_le.mp hn).2,sq_nonneg x]
      rw [abs_mul]
      norm_num
      nlinarith
  have hh := neg_diagonal_le_tensorCriticality
    (iteratedFDeriv ℝ 3 objective x) hd (by norm_num : ‖(-1 / 10 : ℝ)‖ ≤ 1)
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,(jets x).2.2] at hh
  simp only [Fin.prod_const,smul_eq_mul] at hh
  change (1 / 10000 : ℝ) < tensorCriticality (iteratedFDeriv ℝ 3 objective x)
    (secondRestrictedDirections objective (feasibleDisplacements univ x) x
      ((1 / 2) * (1 / 100)) ((1 / 2) * (1 / 2)))
  nlinarith [(abs_le.mp hn).1]


/-- The genuine one-dimensional Euclidean source space. -/
abbrev E := EuclideanSpace ℝ (Fin 1)
/-- The canonical linear isometry from the source Euclidean line to the real numbers. -/
noncomputable def coordinate : E ≃ₗᵢ[ℝ] ℝ :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
/-- The actual scalar quartic transported isometrically to the source Euclidean space. -/
noncomputable def euclideanObjective : E → ℝ := objective ∘ coordinate

/-- Every actual Euclidean derivative through order three is obtained by the genuine chain rule. -/
theorem euclidean_jets (j : ℕ) (hj : j ≤ 3) (x : E) (v : Fin j → E) :
    iteratedFDeriv ℝ j euclideanObjective x v =
      (∏ i, coordinate (v i)) * iteratedDeriv j objective (coordinate x) := by
  have he := coordinate.toContinuousLinearMap.iteratedFDeriv_comp_right
    objective_contDiff x (i := j) (by exact_mod_cast hj)
  change iteratedFDeriv ℝ j euclideanObjective x = _ at he
  rw [he]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,smul_eq_mul]
  rfl

/-- The source Euclidean objective is continuously differentiable through order three. -/
theorem euclidean_contDiff : ContDiff ℝ 3 euclideanObjective :=
  objective_contDiff.comp coordinate.contDiff

/-- The actual Euclidean objective is globally bounded below by zero. -/
theorem euclidean_nonneg (x : E) : 0 ≤ euclideanObjective x := objective_nonneg _

/-- The initialized Euclidean objective value is exactly zero. -/
@[simp] theorem euclidean_zero : euclideanObjective 0 = 0 := by
  simp [euclideanObjective,objective_value]

/-- Zero is an actual global minimizer on the source feasible set. -/
theorem euclidean_global_minimum : IsMinOn euclideanObjective univ 0 := by
  intro x _
  rw [euclidean_zero]
  exact euclidean_nonneg x

/-- The actual third derivative tensor is globally Lipschitz with constant one. -/
theorem euclidean_third_lipschitz (x y : E) :
    ‖iteratedFDeriv ℝ 3 euclideanObjective x-
      iteratedFDeriv ℝ 3 euclideanObjective y‖ ≤ ‖x - y‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  simp only [sub_apply,euclidean_jets 3 (by decide),
    (jets (coordinate x)).2.2,(jets (coordinate y)).2.2]
  have he : (∏ i, coordinate (v i)) * (1 + coordinate x)-
      (∏ i, coordinate (v i)) * (1 + coordinate y) =
      coordinate (x - y) * (∏ i, coordinate (v i)) := by rw [map_sub];ring
  rw [he,norm_mul,norm_prod,coordinate.norm_map]
  simp only [coordinate.norm_map]
  exact le_rfl

/-- Actual first-order Euclidean criticality bounds the scalar first-order criticality. -/
theorem euclidean_first_to_scalar {x : E}
    (hx : constrainedCriticality euclideanObjective 1 univ x 1 ≤ (1 / 100 : ℝ)) :
    constrainedCriticality objective 1 univ (coordinate x) 1 ≤ (1 / 100 : ℝ) := by
  have hp := neg_diagonal_le_tensorCriticality
    (iteratedFDeriv ℝ 1 euclideanObjective x)
    (show coordinate.symm (1 : ℝ) ∈ feasibleDisplacements univ x by simp)
    (by simp : ‖coordinate.symm (1 : ℝ)‖ ≤ 1)
  have hn := neg_diagonal_le_tensorCriticality
    (iteratedFDeriv ℝ 1 euclideanObjective x)
    (show coordinate.symm (-1 : ℝ) ∈ feasibleDisplacements univ x by simp)
    (by simp : ‖coordinate.symm (-1 : ℝ)‖ ≤ 1)
  rw [tensorCriticality_one] at hp hn
  rw [euclidean_jets 1 (by decide)] at hp hn
  simp only [Fin.prod_const,coordinate.apply_symm_apply,pow_one] at hp hn
  rw [constrainedCriticality_univ,TaylorModel.criticality_one _ _ zero_lt_one,
    gradient_eq_deriv,Real.norm_eq_abs,one_mul,←iteratedDeriv_one]
  simp only [starRingEnd_apply,star_trivial]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- A genuine unit direction satisfies both lower derivative restrictions but
violates the third tolerance. -/
theorem euclidean_no_target {x : E}
    (hx : constrainedCriticality euclideanObjective 1 univ x 1 ≤ (1 / 100 : ℝ)) :
    (1 / 10000 : ℝ) < objectiveDerivativeCriticality euclideanObjective univ x
      ((1 / 2) * (1 / 100)) ((1 / 2) * (1 / 2)) 2 := by
  have hs := euclidean_first_to_scalar hx
  have hn := first_small_implies_near hs
  have hg : |iteratedDeriv 1 objective (coordinate x)| ≤ (1 / 100 : ℝ) := by
    rw [constrainedCriticality_univ,TaylorModel.criticality_one _ _ zero_lt_one,
      gradient_eq_deriv,Real.norm_eq_abs,one_mul,←iteratedDeriv_one] at hs
    simpa only [starRingEnd_apply,star_trivial] using hs
  simp only [iteratedDeriv_one] at hg
  let d : E := coordinate.symm (-1 / 10)
  have hd : d ∈ secondRestrictedDirections euclideanObjective
      (feasibleDisplacements univ x) x ((1 / 2) * (1 / 100)) ((1 / 2) * (1 / 2)) := by
    refine ⟨⟨by simp [feasibleDisplacements],?_⟩,?_⟩
    · have he := euclidean_jets 1 (by decide) x (fun _ => d)
      rw [iteratedFDeriv_one_apply] at he
      simp only [Fin.prod_const,pow_one,d,coordinate.apply_symm_apply] at he
      rw [he,abs_mul]
      norm_num
      nlinarith
    · rw [euclidean_jets 2 (by decide),(jets (coordinate x)).2.1]
      simp only [Fin.prod_const,d,coordinate.apply_symm_apply]
      have hb : |1 + coordinate x + (coordinate x)^2 / 2| ≤ 2 := by
        apply abs_le.mpr
        constructor <;> nlinarith [(abs_le.mp hn).1,(abs_le.mp hn).2,
          sq_nonneg (coordinate x)]
      rw [abs_mul]
      norm_num
      nlinarith
  have hh := neg_diagonal_le_tensorCriticality (iteratedFDeriv ℝ 3 euclideanObjective x)
    hd (by norm_num [d] : ‖d‖ ≤ 1)
  rw [euclidean_jets 3 (by decide),(jets (coordinate x)).2.2] at hh
  simp only [Fin.prod_const,d,coordinate.apply_symm_apply] at hh
  change (1 / 10000 : ℝ) < tensorCriticality (iteratedFDeriv ℝ 3 euclideanObjective x)
    (secondRestrictedDirections euclideanObjective (feasibleDisplacements univ x) x
      ((1 / 2) * (1 / 100)) ((1 / 2) * (1 / 2)))
  nlinarith [(abs_le.mp hn).1]


/-- Fixed legal finite-third-order source settings, including both tau/theta margin conditions. -/
noncomputable def settings : DerivativeSettings 3 2 where
  toSettings := {
    order_pos := by decide
    tau := 1 / 2
    theta := 3 / 4
    eta1 := 1 / 4
    eta2 := 3 / 4
    gamma1 := 1 / 2
    gamma2 := 2
    gamma3 := 3
    sigmaMin := 1
    sigmaInitial := 1
    tau_pos := by norm_num
    tau_lt_one := by norm_num
    theta_lower := by norm_num
    theta_lt_one := by norm_num
    eta1_pos := by norm_num
    eta1_le_eta2 := by norm_num
    eta2_lt_one := by norm_num
    gamma1_pos := by norm_num
    gamma1_lt_one := by norm_num
    one_lt_gamma2 := by norm_num
    gamma2_lt_gamma3 := by norm_num
    sigmaMin_pos := by norm_num
    sigmaMin_le_initial := by norm_num }
  enabled_order := by decide
  tauTwo := 1 / 2
  thetaTwo := 3 / 4
  thetaThree := 1 / 2
  tauTwo_pos := by norm_num
  tauTwo_lt_one := by norm_num
  thetaTwo_lower := by norm_num
  thetaTwo_lt_one := by norm_num
  thetaThree_pos := by norm_num
  thetaThree_lt_one := by norm_num

/-- Three legal independent source tolerances that admit no simultaneous true target. -/
noncomputable def accuracy : Fin 3 → ℝ := ![1 / 100,1 / 2,1 / 10000]

/-- Every requested accuracy belongs to the source interval(0,1]. -/
theorem accuracy_bounds (j : Fin 3) : 0 < accuracy j ∧ accuracy j ≤ 1 := by
  fin_cases j <;> norm_num [accuracy]

/-- No point satisfies the literal enabled third-order source stopping test. -/
theorem all_stops_fail (x : E) : ¬derivativeStop euclideanObjective univ settings accuracy x := by
  intro h
  have h0 := h 0 (by decide)
  have h2 := h 2 (by decide)
  change objectiveDerivativeCriticality euclideanObjective univ x
    ((1 / 2) * (1 / 100)) ((1 / 2) * (1 / 2)) 0 ≤ 1 / 100 at h0
  rw [objectiveDerivativeCriticality_zero] at h0
  exact not_lt_of_ge h2 (euclidean_no_target h0)

/-- At the global minimizer, the actual regularized cubic Taylor model equals the entire quartic. -/
theorem initial_model_eq (s : E) :
    HighOrderRegularization.model euclideanObjective 3 0 1 s = euclideanObjective s := by
  rw [HighOrderRegularization.model_eq,TaylorModel.eval_eq_sum]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  rw [euclidean_jets 0 (by decide),euclidean_jets 1 (by decide),
    euclidean_jets 2 (by decide),euclidean_jets 3 (by decide)]
  simp only [Fin.prod_const,coordinate.map_zero]
  rw [(jets 0).1,(jets 0).2.1,(jets 0).2.2]
  rw [←coordinate.norm_map s]
  change _ = objective (coordinate s)
  rw [objective_value]
  norm_num [iteratedDeriv_zero,objective_value,Real.norm_eq_abs,pow_abs,smul_eq_mul]
  have hn : ‖s‖^4 = (coordinate s)^4 := by
    rw [←coordinate.norm_map s,Real.norm_eq_abs]
    nlinarith [sq_abs (coordinate s),sq_nonneg ((coordinate s)^2)]
  rw [hn]
  ring

/-- The literal algorithm cannot compute a strictly improving first trial
from its global minimizer. -/
theorem no_initial_step (s : E) :
    ¬HighOrderRegularization.model euclideanObjective 3 0 1 s <
      HighOrderRegularization.model euclideanObjective 3 0 1 0 := by
  rw [initial_model_eq,HighOrderRegularization.model_zero]
  have hz : euclideanObjective 0 = 0 := by simp [euclideanObjective,objective_value]
  rw [hz]
  exact not_lt_of_ge (euclidean_nonneg s)


/-- From its legal initialized global minimizer, the literal algorithm admits
no positive-length primitive execution because the first improving trial is unavailable. -/
theorem no_positive_run (D : Data E) (N : ℕ) (hzero : D.point 0 = 0) :
    ¬DerivativeRun euclideanObjective univ settings accuracy D (N + 1) := by
  intro h
  have hh := h.modelTrace.improvement 0 (Nat.zero_lt_succ N)
  rw [hzero,h.initial_parameter] at hh
  exact no_initial_step (D.step 0) hh

end ConvexRegularization.TargetObstruction
