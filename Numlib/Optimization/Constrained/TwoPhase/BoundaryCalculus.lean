import Numlib.Optimization.Constrained.TwoPhase.Geometry
import Numlib.Optimization.Regularization.Cubic.Gradient
import Numlib.Optimization.Constrained.TargetCriticality

/-!
# Actual derivatives for a two-phase equality-boundary obstruction

The objective and equality are separate Euclidean coordinates. Their genuine
squared target merit is quadratic, and the selected cubic-model step has zero
actual derivative. Interior-ball criticality detects the failed normalized test.
-/

namespace Constrained.TwoPhase.Boundary
open Set Metric TaylorModel

/-- The genuine two-dimensional Euclidean ambient space. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- Continuous linear coordinate projection. -/
noncomputable def P (i : Fin 2) : E →L[ℝ] ℝ := EuclideanSpace.proj i

/-- A vector with the two indicated Euclidean coordinates. -/
noncomputable def vec (a b : ℝ) : E := WithLp.toLp 2 ![a, b]

/-- The bounded convex constraint region. -/
def region : Set E := closedBall 0 2

/-- The linear objective on coordinate zero. -/
noncomputable def objective (x : E) : ℝ := x 0

/-- The independent linear equality on coordinate one. -/
noncomputable def constraint (x : E) : ℝ := x 1

/-- The actual old-target quadratic merit. -/
noncomputable def oldMerit : E → ℝ := targetMerit objective constraint (-1 / 2)

/-- The actual inner endpoint exactly on the outer residual boundary. -/
noncomputable def endpoint : E := vec (-1 / 4) 0

/-- The genuine squared Euclidean norm of the specified coordinate vector. -/
theorem vec_norm_sq (a b : ℝ) : ‖vec a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [vec, Fin.sum_univ_two]

/-- The actual chosen step has norm one quarter. -/
theorem endpoint_norm : ‖endpoint‖ = 1 / 4 := by
  have hh := vec_norm_sq (-1 / 4) 0
  change ‖endpoint‖ ^ 2 = _ at hh
  nlinarith [norm_nonneg endpoint]

/-- Both coordinate maps are smooth to every order. -/
theorem coordinates_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n objective ∧ ContDiff ℝ n constraint :=
  ⟨(P 0).contDiff, (P 1).contDiff⟩

/-- Every genuine target merit is smooth to every order. -/
theorem merit_contDiff (t : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (targetMerit objective constraint t) := by
  change ContDiff ℝ n (fun x => ‖constraint x‖ ^ 2 / 2 + (objective x - t) ^ 2 / 2)
  exact (((coordinates_contDiff n).2.norm_sq ℝ).div_const 2).add
    ((((coordinates_contDiff n).1.sub contDiff_const).pow 2).div_const 2)

/-- The exact derivative of the actual target merit at every point. -/
theorem merit_fderiv (t : ℝ) (x : E) :
    fderiv ℝ (targetMerit objective constraint t) x =
      x 1 • P 1 + (x 0 - t) • P 0 := by
  have hf : HasFDerivAt objective (P 0) x := (P 0).hasFDerivAt
  have hc : HasFDerivAt constraint (P 1) x := (P 1).hasFDerivAt
  rw [(hasFDerivAt_targetMerit hf.differentiableAt hc.differentiableAt t).fderiv,
    hf.fderiv, hc.fderiv]
  ext v
  simp [objective, constraint, P, innerSL_apply_apply]
  ring

/-- The derivative of the actual gradient functional is the constant Euclidean
bilinear form, independent of both point and target. -/
theorem merit_second_fderiv (t : ℝ) (x v w : E) :
    fderiv ℝ (fderiv ℝ (targetMerit objective constraint t)) x v w =
      v 1 * w 1 + v 0 * w 0 := by
  have he : fderiv ℝ (targetMerit objective constraint t) =
      fun z => z 1 • P 1 + (z 0 - t) • P 0 := funext (merit_fderiv t)
  have hd := (((P 1).hasFDerivAt (x := x)).smul_const (P 1)).add
    ((((P 0).hasFDerivAt (x := x)).sub_const t).smul_const (P 0))
  change HasFDerivAt (fun z : E => z 1 • P 1 + (z 0 - t) • P 0) _ x at hd
  rw [he, hd.fderiv]
  simp [P, smul_eq_mul]

/-- The actual target-merit Hessian tensor has the constant Euclidean formula. -/
theorem merit_second (t : ℝ) (x : E) (w : Fin 2 → E) :
    iteratedFDeriv ℝ 2 (targetMerit objective constraint t) x w =
      w 0 1 * w 1 1 + w 0 0 * w 1 0 := by
  rw [iteratedFDeriv_two_apply, merit_second_fderiv]

/-- The actual merit gradient is the two-coordinate residual vector. -/
theorem merit_gradient (t : ℝ) (x : E) :
    gradient (targetMerit objective constraint t) x = vec (x 0 - t) (x 1) := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient, merit_fderiv]
  ext v
  simp [P, vec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- Unit testing displacements from both actual points remain in the bounded
convex region, so constrained criticality has its literal Euclidean value. -/
theorem testing_ball_feasible {x : E} (hx : ‖x‖ ≤ 1) {d : E} (hd : ‖d‖ ≤ 1) :
    x + d ∈ region := by
  change dist (x + d) 0 ≤ 2
  rw [dist_zero_right]
  exact (norm_add_le x d).trans (by linarith)

/-- Exact merit criticality at the initial point and actual inner endpoint. -/
theorem old_criticalities : firstCriticality oldMerit region 0 = 1 / 2 ∧
    firstCriticality oldMerit region endpoint = 1 / 4 := by
  have hzero : ∀ d : E, ‖d‖ ≤ 1 → (0 : E) + d ∈ region :=
    fun _ hd => testing_ball_feasible (by simp) hd
  have hend : ∀ d : E, ‖d‖ ≤ 1 → endpoint + d ∈ region :=
    fun _ hd => testing_ball_feasible (by rw [endpoint_norm]; norm_num) hd
  rw [firstCriticality, constrainedCriticality_one_eq_norm_of_ball zero_lt_one hzero,
    firstCriticality, constrainedCriticality_one_eq_norm_of_ball zero_lt_one hend]
  have hg0 : ‖gradient oldMerit 0‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by
    rw [oldMerit, merit_gradient, vec_norm_sq]
    norm_num
  have hge : ‖gradient oldMerit endpoint‖ ^ 2 = (1 / 4 : ℝ) ^ 2 := by
    rw [oldMerit, merit_gradient, vec_norm_sq]
    norm_num [endpoint, vec]
  constructor <;> nlinarith [norm_nonneg (gradient oldMerit 0),
    norm_nonneg (gradient oldMerit endpoint)]

/-- The actual p=2 regularized model has zero derivative at the selected step,
with fixed regularization parameter eight. -/
theorem model_fderiv_zero :
    fderiv ℝ (HighOrderRegularization.model oldMerit 2 0 8) endpoint = 0 := by
  change fderiv ℝ
    (CubicRegularization.model (targetMerit objective constraint (-1 / 2)) 0 8) endpoint = 0
  rw [CubicRegularization.fderiv_model (merit_contDiff (-1 / 2) 2).contDiffAt,
    endpoint_norm]
  ext v
  simp only [TaylorModel.quadraticDerivative, add_apply,
    merit_fderiv, merit_second_fderiv, smul_apply,
    innerSL_apply_apply, zero_apply]
  simp [P, endpoint, vec, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_two]
  ring

/-- The genuine quadratic Taylor model at zero exactly agrees with the actual
old-target quadratic merit on every trial point. -/
theorem taylor_exact (s : E) : TaylorModel.eval oldMerit 2 0 s = oldMerit s := by
  dsimp only [oldMerit]
  rw [TaylorModel.eval_two_eq, merit_fderiv, merit_second_fderiv]
  simp [targetMerit, objective, constraint, P, Real.norm_eq_abs, sq_abs]
  ring

/-- The selected step strictly improves the actual regularized model. -/
theorem model_improves : HighOrderRegularization.model oldMerit 2 0 8 endpoint <
    HighOrderRegularization.model oldMerit 2 0 8 0 := by
  rw [HighOrderRegularization.model_eq, HighOrderRegularization.model_zero,
    taylor_exact, endpoint_norm]
  norm_num [oldMerit, targetMerit, objective, constraint, endpoint, vec]

/-- The actual objective/Taylor ratio is exactly one, so the chosen fixed
regularization parameter follows a legal very-successful update. -/
theorem actual_ratio : HighOrderRegularization.ratio oldMerit 2 0 endpoint = 1 := by
  rw [HighOrderRegularization.ratio_eq, TaylorModel.decrement_eq, taylor_exact]
  norm_num [oldMerit, targetMerit, objective, constraint, endpoint, vec]

/-- Every multiplier has the actual Lagrangian gradient `(1,−y)`. -/
theorem lagrangian_gradient (y : ℝ) (x : E) :
    gradient (vectorLagrangian objective constraint y) x = vec 1 (-y) := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient]
  have hf : HasFDerivAt objective (P 0) x := (P 0).hasFDerivAt
  have hc : HasFDerivAt constraint (P 1) x := (P 1).hasFDerivAt
  have hh := hf.sub (((innerSL ℝ y).hasFDerivAt).comp x hc)
  change HasFDerivAt (vectorLagrangian objective constraint y) _ x at hh
  rw [hh.fderiv]
  ext v
  simp [P, vec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- The literal scaled first-order Lagrangian inequality fails for every
multiplier at the actual endpoint, even though feasibility is exact. -/
theorem no_multiplier : ¬∃ y : ℝ,
    firstCriticality (vectorLagrangian objective constraint y) region endpoint ≤
      (1 / 10 : ℝ) * multiplierNorm y := by
  rintro ⟨y, hy⟩
  have hball : ∀ d : E, ‖d‖ ≤ 1 → endpoint + d ∈ region :=
    fun _ hd => testing_ball_feasible (by rw [endpoint_norm]; norm_num) hd
  rw [firstCriticality, constrainedCriticality_one_eq_norm_of_ball zero_lt_one hball,
    one_mul, lagrangian_gradient] at hy
  have hn := vec_norm_sq 1 (-y)
  have hm : multiplierNorm y ^ 2 = 1 + y ^ 2 := by
    rw [multiplierNorm, Real.sq_sqrt (by positivity)]
    simp [Real.norm_eq_abs, sq_abs]
  have he : ‖vec 1 (-y)‖ = multiplierNorm y := by
    nlinarith [norm_nonneg (vec 1 (-y)), multiplierNorm_pos y]
  rw [he] at hy
  linarith [multiplierNorm_pos y]

end Constrained.TwoPhase.Boundary
