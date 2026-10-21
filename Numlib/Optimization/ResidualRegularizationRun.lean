import Numlib.Optimization.ResidualPowerObjective
import Numlib.Optimization.HigherOrderRegularizationRun

/-!
# Regularization runs with normalized residual stopping tests

The local trial laws are the existing actual ARp laws for the residual-power objective. Only
the stopping tests change. The zero-residual case is separated before division; cubic tests
use the current computed model directions. Oracle accounting reuses cached residual jets.
-/

noncomputable section
namespace Optimization.ResidualRegularization
open HigherOrderRegularization ParameterUpdates

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F]

/-- Actual normalized low-order derivative values at a nonzero residual. -/
structure NormalizedResidualMeasures (E : Type*) where
  first : ℝ
  second : ℝ
  quadratic : E → ℝ
  cubic : E → ℝ

/-- The nonnegative criticality value for each derivative order; second order uses the
negative part of the signed least curvature. -/
def NormalizedResidualMeasures.nonnegativeMeasure (m : NormalizedResidualMeasures E)
    (j : Fin 3) (d : E) : ℝ :=
  match j.val with
  | 0 => m.first
  | 1 => max 0 (-m.second)
  | _ => m.cubic d

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- First-order criticality is the normalized gradient norm. -/
@[simp] theorem NormalizedResidualMeasures.nonnegativeMeasure_zero
    (m : NormalizedResidualMeasures E) (d : E) : m.nonnegativeMeasure 0 d = m.first := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Second-order criticality is the nonnegative negative part of signed curvature. -/
@[simp] theorem NormalizedResidualMeasures.nonnegativeMeasure_one
    (m : NormalizedResidualMeasures E) (d : E) :
    m.nonnegativeMeasure 1 d = max 0 (-m.second) := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Third-order criticality is the normalized absolute cubic directional value. -/
@[simp] theorem NormalizedResidualMeasures.nonnegativeMeasure_two
    (m : NormalizedResidualMeasures E) (d : E) : m.nonnegativeMeasure 2 d = m.cubic d := rfl

/-- No ratios are formed at a zero residual. Otherwise these are actual derivatives of the
residual-power objective, including signed least curvature and absolute directional values. -/
def normalizedResidualMeasures (r : E → F) (ell : ℝ) (x : E) :
    Option (NormalizedResidualMeasures E) := by
  classical
  exact if r x = 0 then none else some {
    first := ‖fderiv ℝ (residualPowerObjective r ell) x‖ / ‖r x‖ ^ (ell - 1)
    second := leastCurvature (fderiv ℝ (fderiv ℝ (residualPowerObjective r ell)) x) /
      ‖r x‖ ^ (ell - 1)
    quadratic := fun d => |iteratedFDeriv ℝ 2 (residualPowerObjective r ell) x (fun _ => d)| /
      ‖r x‖ ^ (ell - 1)
    cubic := fun d => |iteratedFDeriv ℝ 3 (residualPowerObjective r ell) x (fun _ => d)| /
      ‖r x‖ ^ (ell - 1) }

/-- Objective flat directions use normalized absolute actual Hessian curvature. -/
def residualFlatDirections (r : E → F) (ell epsilon2 : ℝ) (x : E) : Set E :=
  {d | ‖d‖ = 1 ∧ ∃ m, normalizedResidualMeasures r ell x = some m ∧
    m.quadratic d ≤ epsilon2}

/-- Membership is exactly unit norm and the normalized actual quadratic test. -/
@[simp] theorem mem_residualFlatDirections (r : E → F) (ell epsilon2 : ℝ) (x d : E) :
    d ∈ residualFlatDirections r ell epsilon2 x ↔ ‖d‖ = 1 ∧
      ∃ m, normalizedResidualMeasures r ell x = some m ∧ m.quadratic d ≤ epsilon2 := Iff.rfl

/-- The exact low-order residual termination alternatives. `order` activates first, second,
and third order. A zero residual terminates before ratios, and strict positive curvature
retains its independent termination branch. -/
def Stationary (order : ℕ) (epsilon0 : ℝ) (epsilon : Fin 3 → ℝ)
    (r : E → F) (ell : ℝ) (x : E) (M : Set E) : Prop :=
  ‖r x‖ ≤ epsilon0 ∨ match normalizedResidualMeasures r ell x with
    | none => True
    | some m => m.first ≤ epsilon 0 ∧ (2 ≤ order → epsilon 1 < m.second ∨
      (-epsilon 1 ≤ m.second ∧ (3 ≤ order → M.Nonempty ∧ ∀ d ∈ M,
        m.cubic d ≤ epsilon 2 ∧ m.quadratic d ≤ epsilon 1)))

/-- A finite prefix has actual model decrease, model residuals, acceptance, iterates and
parameter updates; it contains no stopping-time or complexity assertion. -/
structure RunPrefix (params : RegularizationParameters) (order degree : ℕ)
    (theta epsilon : Fin 3 → ℝ) (epsilon0 : ℝ) (r : E → F) (ell : ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    toARpPrefix : HigherOrderRegularization.RunPrefix params order degree theta epsilon
      (residualPowerObjective r ell) x s sigma N where
  exponent_ge_two : 2 ≤ ell
  residual_tolerance_pos : 0 < epsilon0

/-- A complete actual residual regularization run stops at its first normalized test.
Initialization retains the unscaled objective directions of the underlying ARp algorithm;
only the stopping tests are replaced. -/
structure IsRun (params : RegularizationParameters) (order degree : ℕ)
    (theta epsilon : Fin 3 → ℝ) (epsilon0 : ℝ) (r : E → F) (ell : ℝ)
    (x s : ℕ → E) (sigma : ℕ → ℝ) (N : ℕ) : Prop extends
    toResidualPrefix : RunPrefix params order degree theta epsilon epsilon0 r ell x s sigma N where
  terminal : Stationary order epsilon0 epsilon r ell (x N)
    (directionSequence degree (theta 1) (epsilon 1)
      (residualPowerObjective r ell) x s sigma N)
  first : ∀ k < N, ¬Stationary order epsilon0 epsilon r ell (x k)
    (directionSequence degree (theta 1) (epsilon 1)
      (residualPowerObjective r ell) x s sigma k)

/-- Zero residuals select the separate branch. -/
@[simp] theorem normalizedResidualMeasures_of_zero {r : E → F} {ell : ℝ} {x : E}
    (hx : r x = 0) : normalizedResidualMeasures r ell x = none := by
  simp [normalizedResidualMeasures, hx]

/-- The separate branch is selected exactly at a zero residual. -/
@[simp] theorem normalizedResidualMeasures_eq_none_iff (r : E → F) (ell : ℝ) (x : E) :
    normalizedResidualMeasures r ell x = none ↔ r x = 0 := by
  classical
  by_cases hx : r x = 0 <;> simp [normalizedResidualMeasures, hx]

/-- At a nonzero residual the values are precisely the actual derivative ratios. -/
theorem normalizedResidualMeasures_of_ne_zero {r : E → F} {ell : ℝ} {x : E}
    (hx : r x ≠ 0) : normalizedResidualMeasures r ell x = some {
      first := ‖fderiv ℝ (residualPowerObjective r ell) x‖ / ‖r x‖ ^ (ell - 1)
      second := leastCurvature (fderiv ℝ (fderiv ℝ (residualPowerObjective r ell)) x) /
        ‖r x‖ ^ (ell - 1)
      quadratic := fun d => |iteratedFDeriv ℝ 2 (residualPowerObjective r ell) x (fun _ => d)| /
        ‖r x‖ ^ (ell - 1)
      cubic := fun d => |iteratedFDeriv ℝ 3 (residualPowerObjective r ell) x (fun _ => d)| /
        ‖r x‖ ^ (ell - 1) } := by
  simp [normalizedResidualMeasures, hx]

/-- Outside the zero branch the stopping test has precisely the computed measure clauses. -/
theorem stationary_iff_of_measures {order : ℕ} {epsilon0 ell : ℝ} {epsilon : Fin 3 → ℝ}
    {r : E → F} {x : E} {M : Set E} {m : NormalizedResidualMeasures E}
    (hm : normalizedResidualMeasures r ell x = some m) :
    Stationary order epsilon0 epsilon r ell x M ↔ ‖r x‖ ≤ epsilon0 ∨
      m.first ≤ epsilon 0 ∧ (2 ≤ order → epsilon 1 < m.second ∨
        (-epsilon 1 ≤ m.second ∧ (3 ≤ order → M.Nonempty ∧ ∀ d ∈ M,
          m.cubic d ≤ epsilon 2 ∧ m.quadratic d ≤ epsilon 1))) := by
  simp only [Stationary, hm]

/-- The first termination branch needs only the residual norm. -/
theorem stationary_of_residual_le {order : ℕ} {epsilon0 ell : ℝ} {epsilon : Fin 3 → ℝ}
    {r : E → F} {x : E} {M : Set E} (h : ‖r x‖ ≤ epsilon0) :
    Stationary order epsilon0 epsilon r ell x M := Or.inl h

/-- The first-order test has no Hessian or direction-set requirement. -/
@[simp] theorem stationary_one_iff (epsilon0 : ℝ) (epsilon : Fin 3 → ℝ)
    (r : E → F) (ell : ℝ) (x : E) (M : Set E) :
    Stationary 1 epsilon0 epsilon r ell x M ↔ ‖r x‖ ≤ epsilon0 ∨ r x = 0 ∨
      ‖fderiv ℝ (residualPowerObjective r ell) x‖ / ‖r x‖ ^ (ell - 1) ≤ epsilon 0 := by
  by_cases hz : r x = 0 <;> simp [Stationary, normalizedResidualMeasures, hz]

/-- No executed earlier index passes the actual residual/normalized stopping test. -/
theorem IsRun.no_earlier_stop {params : RegularizationParameters} {order degree N : ℕ}
    {theta epsilon : Fin 3 → ℝ} {epsilon0 ell : ℝ} {r : E → F}
    {x s : ℕ → E} {sigma : ℕ → ℝ}
    (h : IsRun params order degree theta epsilon epsilon0 r ell x s sigma N)
    {k : ℕ} (hk : k < N) : epsilon0 < ‖r (x k)‖ := by
  exact lt_of_not_ge fun hb => h.first k hk (Or.inl hb)

/-- One residual-vector evaluation occurs initially and at every executed trial. -/
def residualFunctionEvaluations (N : ℕ) : ℕ := functionEvaluations N

/-- Each residual derivative order is evaluated initially and after each accepted trial;
rejected trials reuse the actual residual jets at the unchanged iterate. -/
def residualDerivativeEvaluations (params : RegularizationParameters) (degree : ℕ)
    (r : E → F) (ell : ℝ) (x s : ℕ → E) (N : ℕ) : ℕ :=
  derivativeEvaluations params degree (residualPowerObjective r ell) x s N

end Optimization.ResidualRegularization
