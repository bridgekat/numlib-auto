import Numlib.Optimization.Quadratic.Derivatives
import Numlib.Optimization.Regularization.Convex.FixedStep
import Numlib.Optimization.Regularization.Cubic.Gradient
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A factorial obstruction in the printed constrained decrease coefficient

A genuine two-dimensional quadratic has a permitted improving cubic trial
with zero actual model derivative. The initialized and accepted endpoint both
fail the requested first-order test. Its exact objective drop is smaller than
the coefficient printed with p! instead of the model penalty's (p+1)!.
-/

namespace ConvexRegularization.DecreaseCounterexample
open Set TaylorModel
open scoped Matrix
/-- The genuine Euclidean plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)
/-- Explicit Euclidean coordinate vectors. -/
noncomputable def vec (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
/-- The bounded symmetric Hessian of the actual quadratic objective. -/
noncomputable def H : E →L[ℝ] E :=
  (Matrix.toEuclideanLin
    (![![-1333/2000,1],![1,0]] : Matrix (Fin 2) (Fin 2) ℝ)).toContinuousLinearMap
/-- The genuine initial linear coefficient. -/
noncomputable def g : E := vec (333/2000) (-1)
/-- The actual trial step. -/
noncomputable def v : E := vec 1 0
/-- The actual quadratic objective. -/
noncomputable def objective : E → ℝ := QuadraticOptimality.model H g
/-- The exact action of the Hessian on Euclidean coordinates. -/
theorem H_apply (x : E) : H x = vec (-1333/2000*x 0+x 1) (x 0) := by
  change WithLp.toLp 2
    ((![![-1333/2000,1],![1,0]] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ WithLp.ofLp x) = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,vec]
/-- The actual Hessian is symmetric in the Euclidean inner product. -/
theorem H_symmetric : H.toLinearMap.IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe,H_apply]
  simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,vec]
  ring
/-- The actual step is a Euclidean unit vector. -/
theorem v_norm : ‖v‖ = 1 := by
  have hh : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    norm_num [v,vec,Fin.sum_univ_two]
  nlinarith [norm_nonneg v]
/-- The actual quadratic is smooth to every finite order. -/
theorem objective_contDiff (n : ℕ) : ContDiff ℝ n objective :=
  QuadraticOptimality.contDiff_model H g n
/-- The genuine gradient is its affine quadratic gradient. -/
theorem objective_gradient (x : E) : gradient objective x = g + H x :=
  QuadraticOptimality.gradient_model H_symmetric g x
/-- The actual Hessian tensor is constant, so the declared positive Lipschitz
bound holds on the entire ambient space. -/
theorem objective_lipschitz (x y : E) :
    ‖iteratedFDeriv ℝ 2 objective x - iteratedFDeriv ℝ 2 objective y‖ ≤
      (1/12000 : ℝ) * ‖x-y‖ := by
  have he : iteratedFDeriv ℝ 2 objective x = iteratedFDeriv ℝ 2 objective y := by
    ext w
    exact (QuadraticOptimality.iteratedFDeriv_two_model H_symmetric g x w).trans
      (QuadraticOptimality.iteratedFDeriv_two_model H_symmetric g y w).symm
  rw [he,sub_self,norm_zero]
  positivity
/-- The quadratic Taylor model is exact at the initial point. -/
theorem taylor_exact (s : E) : eval objective 2 0 s = objective s := by
  simpa [objective] using QuadraticOptimality.taylor_two_model H_symmetric g (0 : E) s
/-- Exact initial and trial objective values. -/
theorem objective_values : objective 0 = 0 ∧ objective v = -667/4000 := by
  norm_num [objective,QuadraticOptimality.model_eq,H_apply,v,g,vec,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two]
/-- The true cubic model derivative at the selected step vanishes exactly. -/
theorem model_derivative_zero :
    fderiv ℝ (HighOrderRegularization.model objective 2 0 1) v = 0 := by
  change fderiv ℝ (CubicRegularization.model objective 0 1) v = 0
  rw [CubicRegularization.fderiv_model (objective_contDiff 2).contDiffAt]
  apply ContinuousLinearMap.ext
  intro d
  simp only [quadraticDerivative,add_apply,smul_apply,zero_apply,innerSL_apply_apply]
  rw [show fderiv ℝ objective 0 = innerSL ℝ g by
    simpa [objective] using QuadraticOptimality.fderiv_model_eq H_symmetric g (0 : E)]
  rw [show fderiv ℝ (fderiv ℝ objective) 0 v d = inner ℝ (H v) d from
    QuadraticOptimality.fderiv_fderiv_model_apply H_symmetric g 0 v d]
  rw [v_norm]
  simp [H_apply,g,v,vec,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two]
  ring

/-- Fixed legal first-order-only constrained settings for the actual trial. -/
noncomputable def settings : Settings 2 where
  order_pos := by decide
  tau := 1/10000
  theta := 5001/10000
  eta1 := 999/1000
  eta2 := 1999/2000
  gamma1 := 1/2
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
  sigmaMin_le_initial := le_rfl

/-- A positive declared Hessian Lipschitz constant with exact parameter cap one. -/
noncomputable def L : ℝ := 1/12000
/-- The requested accuracy makes the printed power coefficient an exact rational cube. -/
noncomputable def epsilon : ℝ := (49/100) * (L + 1) / (2*(1-settings.theta))
/-- The legal requested accuracy is smaller than one half. -/
theorem epsilon_bounds : 0 < epsilon ∧ epsilon < 1/2 := by
  norm_num [epsilon,L,settings]
/-- The actual source parameter cap equals the constant parameter of the run. -/
theorem parameter_cap : parameterCap settings L = 1 := by
  norm_num [parameterCap,L,settings]
/-- Actual initialized and accepted-point arrays for the single trial. -/
noncomputable def data : Data E where
  point := fun k => if k = 0 then 0 else v
  step := fun _ => v
  parameter := fun _ => 1
  ratio := fun _ => 1

/-- The first-order constrained criticality is the genuine gradient norm. -/
theorem criticality_formula (x : E) :
    constrainedCriticality objective 1 univ x 1 = ‖g + H x‖ := by
  rw [constrainedCriticality_one_eq_norm_of_ball zero_lt_one
    (fun _ _ => mem_univ _) objective,one_mul,objective_gradient]
/-- The initial point genuinely fails the requested first-order test. -/
theorem initial_fails : epsilon < constrainedCriticality objective 1 univ 0 1 := by
  rw [criticality_formula,map_zero,add_zero]
  have hh : 1 ≤ ‖g‖ := by
    have hcoord := PiLp.norm_apply_le (p := 2) g (1 : Fin 2)
    simpa [g,vec] using hcoord
  linarith [epsilon_bounds.2]
/-- The accepted endpoint also genuinely fails its actual first-order test. -/
theorem endpoint_fails : epsilon < constrainedCriticality objective 1 univ v 1 := by
  rw [criticality_formula]
  have he : g + H v = (-1/2 : ℝ) • v := by
    ext i
    fin_cases i <;> norm_num [H_apply,g,v,vec]
  rw [he,norm_smul,v_norm]
  norm_num only [Real.norm_eq_abs,abs_of_nonpos (by norm_num : (-1/2 : ℝ) ≤ 0),
    neg_neg,mul_one]
  exact epsilon_bounds.2

/-- The actual strict improvement, objective ratio and update intervals give
one genuine complete first-order ARp-CC trial. -/
theorem run : Run objective univ settings epsilon data 1 := by
  refine {
    accuracy_pos := epsilon_bounds.1
    initial_parameter := rfl
    initial_mem := mem_univ _
    modelTrace := ?_
    feasible_trial := fun _ _ => mem_univ _
    model_test := ?_
    continues := ?_ }
  · refine {
      order_pos := by decide
      updates := ?_
      improvement := ?_
      ratio := ?_
      point_update := ?_ }
    · refine ⟨by norm_num [settings],by norm_num [data,settings],
        by norm_num [settings],by norm_num [settings],by norm_num [settings],
        by norm_num [settings],by norm_num [settings],by norm_num [settings],
        by norm_num [settings],fun i hi => ?_⟩
      norm_num [data,settings]
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      unfold HighOrderRegularization.model ModelDecrease.penalized
      simp only [data,ite_true,taylor_exact,v_norm]
      rw [objective_values.1,objective_values.2]
      norm_num
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      simp only [data,ite_true]
      unfold HighOrderRegularization.ratio TaylorModel.decrement
      rw [zero_add,taylor_exact,taylor_exact]
      norm_num [objective_values.1,objective_values.2]
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      norm_num [data,settings]
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    have hz := constrainedCriticality_one_eq_zero_of_fderiv isClosed_univ
      (show v ∈ (univ : Set E) by trivial) zero_le_one model_derivative_zero
    have hset : feasibleDisplacements (univ : Set E) (0 : E) = univ := by ext d;simp
    simp only [data,ite_true,hset]
    rw [hz]
    have hε := epsilon_bounds.1
    norm_num [settings]
    positivity
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    exact initial_fails

/-- The literal first-order coefficient printed in Lemma6.2.2. -/
noncomputable def printedCoefficient : ℝ :=
  settings.eta1 * settings.sigmaMin / (2 : ℕ).factorial *
    ((2 : ℕ).factorial * (1-settings.theta) / (L + parameterCap settings L)) ^
      (((2+1 : ℕ) : ℝ) / 2)

/-- The declared accuracy gives an exact rational square before raising to three halves. -/
theorem accuracy_product :
    ((2 : ℕ).factorial * (1-settings.theta) / (L + parameterCap settings L)) *
      epsilon = 49/100 := by
  rw [parameter_cap]
  norm_num [settings,L,epsilon]

/-- The relevant real power is exactly the cube of seven tenths. -/
theorem rational_power : (49/100 : ℝ) ^ (3/2 : ℝ) = 343/1000 := by
  rw [show (49/100 : ℝ) = (7/10 : ℝ)^2 by norm_num]
  rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7/10)]
  norm_num

/-- The exact source coefficient times the legal accuracy power exceeds the actual drop. -/
theorem printed_decrease_value :
    printedCoefficient * epsilon ^ (3/2 : ℝ) = 342657/2000000 := by
  have hb : 0 ≤ ((2 : ℕ).factorial * (1-settings.theta) /
      (L + parameterCap settings L)) := by rw [parameter_cap];norm_num [settings,L]
  change 0 ≤ (2 : ℝ) * (1-settings.theta) / (L + parameterCap settings L) at hb
  have he := epsilon_bounds.1.le
  unfold printedCoefficient
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat]
  rw [mul_assoc,←Real.mul_rpow hb he]
  have hprod : ((2 : ℝ) * (1-settings.theta) / (L + parameterCap settings L)) *
      epsilon = 49/100 := by simpa using accuracy_product
  rw [hprod,rational_power]
  norm_num [settings]

/-- A genuine accepted nonterminal trial violates the printed first-order
successful-decrease bound with all legal fixed source parameters. -/
theorem printed_decrease_fails :
    ¬printedCoefficient * epsilon ^ (3/2 : ℝ) <
      objective (data.point 0) - objective (data.point 1) := by
  rw [printed_decrease_value]
  norm_num [data,objective_values.1,objective_values.2]

end ConvexRegularization.DecreaseCounterexample
