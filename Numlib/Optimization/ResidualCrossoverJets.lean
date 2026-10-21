import Numlib.Optimization.CompactAnchoredJets
import Numlib.Optimization.TaylorCriticalityCriteria
import Numlib.Analysis.Calculus.LinearPullback
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.ComputeDegree

/-!
# A polynomial residual with crossing first- and second-order scales

An explicit Hermite polynomial on a Euclidean line has residual values `1`, `7999/10000`,
and `16/25` at coordinates `0`, `1`, and `-1`. Its squared residual has prescribed first
and second jets at those points. The objective is globally nonnegative and its actual jets
satisfy boundedness and anchored Lipschitz comparisons on a full bounded neighborhood.
-/

noncomputable section
open Set Metric
open scoped ContDiff
open Polynomial
namespace Optimization.ResidualCrossoverJets
open ConstrainedTaylorCriticality TaylorCriticality

/-- The one-dimensional Euclidean domain and residual space. -/
abbrev Line := EuclideanSpace ℝ (Fin 1)

/-- The point with the given sole coordinate. -/
def point (t : ℝ) : Line := WithLp.toLp 2 (fun _ => t)

/-- The simple closed feasible ball. -/
def feasible : Set Line := closedBall 0 3

/-- The open convex neighborhood of the feasible ball. -/
def neighborhood : Set Line := ball 0 4

/-- The first derivative at the intermediate point. -/
def slope : ℝ := 1583901 / 10000000

/-- The residual value at the intermediate point. -/
def middleResidual : ℝ := 7999 / 10000

/-- The residual derivative required by the intermediate objective slope. -/
def middleDerivative : ℝ := slope / middleResidual

/-- The residual second derivative making the intermediate objective curvature vanish. -/
def middleSecondDerivative : ℝ := -(middleDerivative ^ 2) / middleResidual

/-- A degree-eight Hermite residual polynomial. Each summand vanishes to order three at the
other two interpolation nodes. -/
def rho : ℝ[X] :=
  (-1 + X - C (11 / 4) * X ^ 2) * (X ^ 2 - 1) ^ 3 +
  (C (middleResidual / 8) + C ((middleDerivative - 36 * (middleResidual / 8)) / 8) * (X - 1) +
    C ((middleSecondDerivative - 132 * (middleResidual / 8) -
      72 * ((middleDerivative - 36 * (middleResidual / 8)) / 8)) / 16) * (X - 1) ^ 2) *
    X ^ 3 * (X + 1) ^ 3 +
  (C (2 / 25) + C (9 / 25) * (X + 1) + C (24 / 25) * (X + 1) ^ 2) *
    X ^ 3 * (X - 1) ^ 3

/-- The construction needs no terms above degree eight. -/
theorem rho_natDegree_le : rho.natDegree ≤ 8 := by
  unfold rho
  compute_degree

/-- The actual polynomial residual on the Euclidean line. -/
def residual (x : Line) : Line := point (rho.eval (x 0))

/-- The actual least-squares objective of the residual. -/
def objective : Line → ℝ := squaredResidual residual

/-- Its scalar polynomial representation. -/
def objectivePolynomial : ℝ[X] := C (1 / 2) * rho ^ 2

/-- A coordinate is the actual scalar used by the point constructor. -/
@[simp] theorem point_apply (t : ℝ) (i : Fin 1) : point t i = t := rfl

/-- Every vector on the Euclidean line is determined by its sole coordinate. -/
@[simp] theorem point_coord (x : Line) : point (x 0) = x := by
  ext i
  fin_cases i
  rfl

/-- Point addition agrees with scalar addition. -/
@[simp] theorem point_add (s t : ℝ) : point (s + t) = point s + point t := by
  ext i
  rfl

/-- The origin is the point with coordinate zero. -/
@[simp] theorem point_zero : point 0 = 0 := rfl

/-- Point subtraction agrees with scalar subtraction. -/
@[simp] theorem point_sub (s t : ℝ) : point (s - t) = point s - point t := by
  ext i
  rfl

/-- Point negation agrees with scalar negation. -/
@[simp] theorem point_neg (t : ℝ) : point (-t) = -point t := by
  ext i
  rfl

/-- The point constructor commutes with scalar multiplication. -/
@[simp] theorem point_smul (s t : ℝ) : point (s * t) = s • point t := by
  ext i
  rfl

/-- Scalar absolute value is the actual Euclidean norm. -/
@[simp] theorem norm_point (t : ℝ) : ‖point t‖ = |t| := by
  have hp : point t = PiLp.single 2 (0 : Fin 1) t := by
    ext i
    fin_cases i
    simp [point]
  rw [hp, PiLp.norm_single, Real.norm_eq_abs]

/-- The norm of a vector equals the absolute value of its coordinate. -/
theorem norm_eq_abs_coord (x : Line) : ‖x‖ = |x 0| := by
  rw [← norm_point, point_coord]

/-- Scalar membership characterizes feasibility. -/
@[simp] theorem point_mem_feasible (t : ℝ) : point t ∈ feasible ↔ |t| ≤ 3 := by
  simp [feasible]

/-- The feasible set is closed. -/
theorem isClosed_feasible : IsClosed feasible := isClosed_closedBall

/-- The feasible set is convex. -/
theorem convex_feasible : Convex ℝ feasible := convex_closedBall 0 3

/-- The feasible set contains the origin. -/
theorem zero_mem_feasible : (0 : Line) ∈ feasible := by
  simp [feasible]

/-- The entire unit displacement ball is feasible at every point of coordinate at most two. -/
theorem add_mem_feasible {t : ℝ} (ht : |t| ≤ 2) {d : Line} (hd : ‖d‖ ≤ 1) :
    point t + d ∈ feasible := by
  rw [feasible, mem_closedBall_zero_iff]
  calc
    ‖point t + d‖ ≤ ‖point t‖ + ‖d‖ := norm_add_le _ _
    _ = |t| + ‖d‖ := by rw [norm_point]
    _ ≤ 3 := by linarith

/-- Unit feasible displacement balls at interior sample points are the full unit ball. -/
theorem feasibleBall_eq {t : ℝ} (ht : |t| ≤ 2) :
    feasibleDisplacements feasible (point t) ∩ closedBall 0 1 = closedBall 0 1 := by
  ext d
  constructor
  · exact fun h => h.2
  · intro hd
    exact ⟨add_mem_feasible ht (by simpa using hd), hd⟩

/-- The objective is the scalar squared polynomial composed with the coordinate map. -/
theorem objective_eq (x : Line) : objective x = objectivePolynomial.eval (x 0) := by
  simp [objective, squaredResidual, residual, objectivePolynomial, sq_abs]
  ring

/-- The residual is infinitely continuously differentiable. -/
theorem contDiff_residual : ContDiff ℝ ∞ residual := by
  have heq : residual = fun x : Line => rho.eval (x 0) • point 1 := by
    funext x
    ext i
    simp [residual, point]
  rw [heq]
  have hp : ContDiff ℝ ∞ (fun t : ℝ => rho.eval t) := by
    simpa using rho.contDiff_aeval (𝕜 := ℝ) ∞
  exact (hp.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff).smul contDiff_const

/-- The objective is infinitely continuously differentiable. -/
theorem contDiff_objective : ContDiff ℝ ∞ objective := by
  have heq : objective = fun x : Line =>
      objectivePolynomial.eval ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) x) :=
    funext objective_eq
  rw [heq]
  have hp : ContDiff ℝ ∞ (fun t : ℝ => objectivePolynomial.eval t) := by
    simpa using objectivePolynomial.contDiff_aeval (𝕜 := ℝ) ∞
  exact hp.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff

/-- The actual objective is nonnegative everywhere. -/
theorem objective_nonneg (x : Line) : 0 ≤ objective x := by
  exact div_nonneg (sq_nonneg ‖residual x‖) (by norm_num)

/-- The exact residual at the origin. -/
theorem rho_eval_zero : rho.eval 0 = 1 := by norm_num [rho]

/-- The exact residual at coordinate one. -/
theorem rho_eval_one : rho.eval 1 = middleResidual := by norm_num [rho]

/-- The exact residual at coordinate minus one. -/
theorem rho_eval_neg_one : rho.eval (-1) = 16 / 25 := by norm_num [rho]

/-- The residual derivative at the origin. -/
theorem rho_derivative_zero : rho.derivative.eval 0 = -1 := by
  norm_num [rho, derivative_mul, derivative_pow]

/-- The residual derivative at coordinate one. -/
theorem rho_derivative_one : rho.derivative.eval 1 = middleDerivative := by
  norm_num [rho, derivative_mul, derivative_pow]
  ring

/-- The residual derivative at coordinate minus one. -/
theorem rho_derivative_neg_one : rho.derivative.eval (-1) = 0 := by
  norm_num [rho, derivative_mul, derivative_pow]

/-- The residual second derivative at the origin. -/
theorem rho_secondDerivative_zero : rho.derivative.derivative.eval 0 = -(1 / 2) := by
  norm_num [rho, derivative_mul, derivative_pow]

/-- The residual second derivative at coordinate one. -/
theorem rho_secondDerivative_one : rho.derivative.derivative.eval 1 = middleSecondDerivative := by
  norm_num [rho, derivative_mul, derivative_pow]
  ring

/-- The residual second derivative at coordinate minus one. -/
theorem rho_secondDerivative_neg_one : rho.derivative.derivative.eval (-1) = 0 := by
  norm_num [rho, derivative_mul, derivative_pow]

/-- Differentiating the squared residual polynomial once gives the product rule. -/
theorem objectivePolynomial_derivative (t : ℝ) :
    objectivePolynomial.derivative.eval t = rho.eval t * rho.derivative.eval t := by
  simp [objectivePolynomial, derivative_mul, derivative_pow]
  ring

/-- Differentiating the squared residual polynomial twice gives its actual curvature. -/
theorem objectivePolynomial_secondDerivative (t : ℝ) :
    objectivePolynomial.derivative.derivative.eval t =
      rho.derivative.eval t ^ 2 + rho.eval t * rho.derivative.derivative.eval t := by
  simp [objectivePolynomial, derivative_mul, derivative_pow]
  ring

/-- The actual derivative of the Euclidean objective is its scalar polynomial derivative. -/
theorem fderiv_objective (x d : Line) :
    fderiv ℝ objective x d = objectivePolynomial.derivative.eval (x 0) * d 0 := by
  have heq : objective = fun y : Line => objectivePolynomial.eval (y 0) :=
    funext objective_eq
  rw [heq]
  have h := (objectivePolynomial.hasFDerivAt (x 0)).comp x
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, EuclideanSpace.coe_proj,
    smul_eq_mul, mul_comm] using congrArg (fun A : Line →L[ℝ] ℝ => A d) h.fderiv

/-- The actual bilinear second derivative is the scalar polynomial curvature times coordinates. -/
theorem secondFDeriv_objective (x a b : Line) :
    fderiv ℝ (fderiv ℝ objective) x a b =
      objectivePolynomial.derivative.derivative.eval (x 0) * a 0 * b 0 := by
  have heq : fderiv ℝ objective = fun y : Line =>
      objectivePolynomial.derivative.eval (y 0) •
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) := by
    funext y
    ext d
    simp [fderiv_objective]
  rw [heq]
  have h := ((objectivePolynomial.derivative.hasFDerivAt (x 0)).comp x
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt).smul_const
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1))
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, EuclideanSpace.coe_proj,
    smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      congrArg (fun A : Line →L[ℝ] (Line →L[ℝ] ℝ) => A a b) h.fderiv

/-- The exact norm of the initial residual. -/
theorem residual_norm_zero : ‖residual (point 0)‖ = 1 := by
  simp [residual, rho_eval_zero]

/-- The exact norm of the intermediate residual. -/
theorem residual_norm_one : ‖residual (point 1)‖ = 7999 / 10000 := by
  norm_num [residual, rho_eval_one, middleResidual]

/-- The exact norm of the terminal residual. -/
theorem residual_norm_neg_one : ‖residual (point (-1))‖ = 16 / 25 := by
  norm_num [residual, rho_eval_neg_one]

/-- The least-squares identity exposes the actual norm squared without implementation unfolding. -/
theorem objective_eq_half_norm_sq (x : Line) : objective x = ‖residual x‖ ^ 2 / 2 := rfl

/-- The exact initial objective value. -/
theorem objective_point_zero : objective (point 0) = 1 / 2 := by
  rw [objective_eq_half_norm_sq, residual_norm_zero]
  norm_num

/-- The exact intermediate objective value. -/
theorem objective_point_one : objective (point 1) = 63984001 / 200000000 := by
  rw [objective_eq_half_norm_sq, residual_norm_one]
  norm_num

/-- The exact terminal objective value. -/
theorem objective_point_neg_one : objective (point (-1)) = 128 / 625 := by
  rw [objective_eq_half_norm_sq, residual_norm_neg_one]
  norm_num

/-- The initial objective derivative is minus the sole coordinate. -/
theorem fderiv_objective_zero (d : Line) : fderiv ℝ objective (point 0) d = -d 0 := by
  rw [fderiv_objective, point_apply, objectivePolynomial_derivative,
    rho_eval_zero, rho_derivative_zero]
  ring

/-- The intermediate objective derivative is its specified positive slope. -/
theorem fderiv_objective_one (d : Line) :
    fderiv ℝ objective (point 1) d = slope * d 0 := by
  rw [fderiv_objective, point_apply, objectivePolynomial_derivative,
    rho_eval_one, rho_derivative_one]
  norm_num [middleDerivative, middleResidual, slope]

/-- The terminal objective derivative vanishes. -/
theorem fderiv_objective_neg_one (d : Line) :
    fderiv ℝ objective (point (-1)) d = 0 := by
  rw [fderiv_objective, point_apply, objectivePolynomial_derivative,
    rho_eval_neg_one, rho_derivative_neg_one]
  ring

/-- The initial objective Hessian is one half times the coordinate product. -/
theorem secondFDeriv_objective_zero (a b : Line) :
    fderiv ℝ (fderiv ℝ objective) (point 0) a b = (1 / 2) * a 0 * b 0 := by
  rw [secondFDeriv_objective, point_apply, objectivePolynomial_secondDerivative,
    rho_eval_zero, rho_derivative_zero, rho_secondDerivative_zero]
  ring

/-- The intermediate objective Hessian vanishes. -/
theorem secondFDeriv_objective_one (a b : Line) :
    fderiv ℝ (fderiv ℝ objective) (point 1) a b = 0 := by
  rw [secondFDeriv_objective, point_apply, objectivePolynomial_secondDerivative,
    rho_eval_one, rho_derivative_one, rho_secondDerivative_one]
  norm_num [middleSecondDerivative, middleDerivative, middleResidual, slope]

/-- The terminal objective Hessian vanishes. -/
theorem secondFDeriv_objective_neg_one (a b : Line) :
    fderiv ℝ (fderiv ℝ objective) (point (-1)) a b = 0 := by
  rw [secondFDeriv_objective, point_apply, objectivePolynomial_secondDerivative,
    rho_eval_neg_one, rho_derivative_neg_one, rho_secondDerivative_neg_one]
  ring

/-- The initial first-order Taylor decrement. -/
theorem taylorDecrement_one_zero (d : Line) :
    taylorDecrement objective 1 (point 0) d = d 0 := by
  rw [taylorDecrement_one, fderiv_objective_zero, neg_neg]

/-- The initial second-order Taylor decrement. -/
theorem taylorDecrement_two_zero (d : Line) :
    taylorDecrement objective 2 (point 0) d = d 0 - (1 / 4) * (d 0) ^ 2 := by
  rw [taylorDecrement_two, fderiv_objective_zero, secondFDeriv_objective_zero]
  ring

/-- The intermediate first-order Taylor decrement. -/
theorem taylorDecrement_one_one (d : Line) :
    taylorDecrement objective 1 (point 1) d = -slope * d 0 := by
  simp [fderiv_objective_one, neg_mul]

/-- The intermediate second-order Taylor decrement equals its first-order decrement. -/
theorem taylorDecrement_two_one (d : Line) :
    taylorDecrement objective 2 (point 1) d = -slope * d 0 := by
  rw [taylorDecrement_two, fderiv_objective_one, secondFDeriv_objective_one]
  ring

/-- The terminal first-order Taylor decrement vanishes. -/
theorem taylorDecrement_one_neg_one (d : Line) :
    taylorDecrement objective 1 (point (-1)) d = 0 := by
  rw [taylorDecrement_one, fderiv_objective_neg_one, neg_zero]

/-- The terminal second-order Taylor decrement vanishes. -/
theorem taylorDecrement_two_neg_one (d : Line) :
    taylorDecrement objective 2 (point (-1)) d = 0 := by
  rw [taylorDecrement_two, fderiv_objective_neg_one, secondFDeriv_objective_neg_one]
  ring

/-- Coordinate evaluation on the Euclidean line has operator norm one. -/
theorem norm_coordinate : ‖EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simp [norm_eq_abs_coord]
  · have h := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).le_opNorm (point 1)
    simpa using h

/-- Both constrained Taylor gaps at the intermediate sample equal the specified slope. -/
theorem taylorGap_one (j : ℕ) (hj : 1 ≤ j) (hjq : j ≤ 2) :
    taylorGap objective feasible j (point 1) 1 = slope := by
  have hjet : taylorDecrement objective j (point 1) = fun d : Line =>
      -(slope • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) d := by
    funext d
    interval_cases j
    · rw [taylorDecrement_one_one]
      simp [neg_mul]
    · rw [taylorDecrement_two_one]
      simp [neg_mul]
  unfold taylorGap
  rw [feasibleBall_eq (by norm_num : |(1 : ℝ)| ≤ 2), hjet,
    gapOn_norm_linear _ (by norm_num), norm_smul, norm_coordinate]
  norm_num [slope]

/-- Both constrained Taylor gaps at the terminal sample vanish. -/
theorem taylorGap_neg_one (j : ℕ) (hj : 1 ≤ j) (hjq : j ≤ 2) :
    taylorGap objective feasible j (point (-1)) 1 = 0 := by
  have hx : point (-1) ∈ feasible := by rw [point_mem_feasible]; norm_num
  apply le_antisymm
  · apply (taylorGap_le_iff objective isClosed_feasible j hx (by norm_num) 0).mpr
    intro d _ _
    interval_cases j
    · rw [taylorDecrement_one_neg_one]
    · rw [taylorDecrement_two_neg_one]
  · exact taylorGap_nonneg objective isClosed_feasible j hx (by norm_num)

/-- The global smooth objective has actual bounded and anchored Lipschitz jets throughout the
full feasible ball and its open convex neighborhood, with all constants at least one. -/
theorem exists_anchoredBoundedJets :
    ∃ L B : ℕ → ℝ, (∀ j, 1 ≤ L j) ∧ (∀ j, 1 ≤ B j) ∧
      HasAnchoredBoundedJets objective 2 feasible neighborhood false L B := by
  exact exists_anchoredBoundedJets_of_contDiff 2 (contDiff_objective.of_le (by simp))
    (by norm_num : (3 : ℝ) < 4)

/-- The same actual constants cover every initial feasible sublevel set. -/
theorem exists_anchoredBoundedJets_sublevel (x₀ : Line) :
    ∃ L B : ℕ → ℝ, (∀ j, 1 ≤ L j) ∧ (∀ j, 1 ≤ B j) ∧
      HasAnchoredBoundedJets objective 2 (feasibleSublevelSet objective feasible x₀)
        neighborhood false L B := by
  obtain ⟨L, B, hL, hB, hj⟩ := exists_anchoredBoundedJets
  exact ⟨L, B, hL, hB, hj.mono_centers (fun _ hx => hx.1)⟩

end Optimization.ResidualCrossoverJets
