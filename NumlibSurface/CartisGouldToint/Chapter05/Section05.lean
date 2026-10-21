import Numlib.Optimization.UniversalRegularization
import Numlib.Analysis.Calculus.Gradient
import NumlibSurface.CartisGouldToint.Chapter01.Section03

/-!
# Chapter 5, Section 5: universal regularization

The real regularization exponent uses the book's finite-product factorial. The actual
highest derivative has the diagonal tensor Hölder bound of f.DpH. Algorithm 5.5.1 checks
criticality at every trial, including rejected trials, and its oracle schedule charges these
checks. Rejection is the logical complement of all acceptance tests, correcting the update
rule's transcribed conjunction. No fixed positive regularization floor is imposed.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section05
open Chapter01.Section03
open Optimization.UniversalRegularization

variable {n : ℕ}

/-- The finite-product real factorial (5.5.2); this is the book's normalization. -/
abbrev realPowerFactorial (r : ℝ) : ℝ := Real.powerFactorial r

/-- The real factorial is positive on its intended nonnegative domain. -/
theorem realPowerFactorial_pos {r : ℝ} (hr : 0 ≤ r) : 0 < realPowerFactorial r :=
  Real.powerFactorial_pos hr

/-- At integer powers the normalization is the ordinary factorial. -/
@[simp] theorem realPowerFactorial_natCast (p : ℕ) : realPowerFactorial (p : ℝ) = p.factorial :=
  Real.powerFactorial_natCast p

/-- The book's shifted-factorial identity includes integer endpoints. -/
theorem realPowerFactorial_sub_one {r : ℝ} (hr : 1 ≤ r) :
    realPowerFactorial r = r * realPowerFactorial (r - 1) := Real.powerFactorial_sub_one hr

/-- Assumption f.DpH: actual continuous derivatives, the tensor norm (A.7), a nonnegative
Hölder constant and an exponent in `[0,1]`. When `p=1` the exponent is positive, as required
by the source. Exponent zero bounds oscillation and does not imply continuity by itself. -/
structure holderDerivativeAssumption (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (H beta : ℝ) : Prop extends Optimization.HolderDerivative f p H beta where
  first_exponent_pos : p = 1 → 0 < beta

/-- The model (5.5.1) uses the actual Taylor polynomial and the finite-product factorial. -/
def universalModel (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma r : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ :=
  taylorModel f p x s + sigma / realPowerFactorial r * ‖s‖ ^ r

/-- The surface model is precisely the reusable radial regularization model. -/
theorem universalModel_eq_model (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (sigma r : ℝ) :
    universalModel f p x sigma r = model f p x sigma r := rfl

/-- The legal initialization constants of Algorithm 5.5.1; `q=1` means infinite second
accuracy and `q=2` activates the finite second-order accuracy. -/
abbrev universalParameters (q p : ℕ) (r : ℝ) := Parameters q p r

/-- Actual model decrease and model derivative residuals in Step 1. -/
abbrev universalComputedStep {q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (sigma : ℝ)
    (s : EuclideanSpace ℝ (Fin n)) : Prop := ComputedStep a f x sigma s

/-- A finite legal nonterminal prefix of Algorithm 5.5.1, with all trial derivative checks,
ratio and length acceptance tests, and the actual parameter update intervals. -/
abbrev universalPrefix {q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) (N : ℕ) : Prop := RunPrefix a f x s sigma N

/-- Algorithm 5.5.1: the actual real-power model, strict decrease, activated residuals,
first trial stopping, exact acceptance and update intervals, and cache-aware oracle schedule.
`N` counts computed trials and may be zero for an initial stop. The final trial is tested
before computing its objective value. No complexity conclusion is a run hypothesis. -/
abbrev algorithm_5_5_1 {q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) (N : ℕ) : Prop := IsRun a f x s sigma N

/-- The actual ordered oracle calls of Algorithm 5.5.1. Every trial charges its active
first and second derivatives, irrespective of acceptance. -/
abbrev universalOracleCalls {q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) (N : ℕ) := oracleCalls a f x s sigma N

/-- Per-order oracle cost is counted from the actual schedule; order zero counts values. -/
abbrev universalEvaluations {q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) (N j : ℕ) : ℕ := evaluations a f x s sigma N j

/-- Every activated derivative is evaluated initially and at every computed trial. -/
theorem universalEvaluations_active {q p N j : ℕ} {r : ℝ}
    {a : universalParameters q p r} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ} (hj : 0 < j) (hjq : j ≤ q) :
    universalEvaluations a f x s sigma N j = N + 1 := evaluations_active hj hjq

/-- The terminal trial stops before its value is evaluated. -/
theorem universalEvaluations_value {q p N : ℕ} {r : ℝ}
    {a : universalParameters q p r} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ} :
    universalEvaluations a f x s sigma N 0 = max 1 N := evaluations_value

open Classical in
/-- Derivatives above the active order are cached on rejection and computed after every
accepted nonterminal trial, with no initial higher derivative call at an initial stop. -/
theorem universalEvaluations_high {q p N j : ℕ} {r : ℝ}
    {a : universalParameters q p r} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ} (hjq : q < j) (hjp : j ≤ p) :
    universalEvaluations a f x s sigma N j = if N = 0 then 0 else
      1 + Optimization.ParameterUpdates.successCount
        (fun k => Accepted a f (x k) (sigma k) (s k)) (N - 1) := evaluations_high hjq hjp

/-- Lemma 5.5.1: every computed step pays its finite-product normalized radial term in
Taylor decrease. This also applies to the terminal computed trial. -/
theorem lemma_5_5_1 {q p : ℕ} {r sigma : ℝ} {a : universalParameters q p r}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : EuclideanSpace ℝ (Fin n)}
    (hs : universalComputedStep a f x sigma s) :
    sigma / realPowerFactorial r * ‖s‖ ^ r ≤ f x - taylorModel f p x s := by
  simpa only [taylorModel, Optimization.RegularizedTaylorModel.taylorModel_zero] using
    hs.predicted_decrease

/-- Lemma 5.5.2: the trial gradient and activated negative curvature obey (5.5.13) and
(5.5.14), using actual Taylor remainders and genuine real-power regularizer derivatives.
The positive derivative exponents are precisely the source's `p+beta>q` restriction. -/
theorem lemma_5_5_2 [NeZero n] {q p : ℕ} {r sigma H beta : ℝ}
    {a : universalParameters q p r} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : EuclideanSpace ℝ (Fin n)} (hf : holderDerivativeAssumption f p H beta)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (hsigma : 0 ≤ sigma)
    (hs : universalComputedStep a f x sigma s) :
    ‖gradient f (x + s)‖ ≤
      H / realPowerFactorial ((p : ℝ) + beta - 1) * ‖s‖ ^ ((p : ℝ) + beta - 1) +
        (sigma / realPowerFactorial (r - 1) + a.theta 0) * ‖s‖ ^ (r - 1) ∧
    (2 ≤ q → -leastHessianEigenvalue f (x + s) ≤
      H / realPowerFactorial ((p : ℝ) + beta - 2) * ‖s‖ ^ ((p : ℝ) + beta - 2) +
        (sigma / realPowerFactorial (r - 2) + a.theta 1) * ‖s‖ ^ (r - 2)) := by
  have hp : 1 ≤ p := a.order_pos.trans a.degree_ge_order
  have hr1 : 1 < r := by
    have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith [a.power_gt_degree]
  constructor
  · rw [EuclideanSpace.norm_gradient_eq]
    exact hf.toHolderDerivative.trial_fderiv_bound hp hr1 hsigma x s hs.first
  · intro hq
    have hp2 : 2 ≤ p := hq.trans a.degree_ge_order
    have hr2 : 2 < r := by
      have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith [a.power_gt_degree]
    have hexp2 : (0 : ℝ) < (p : ℝ) + beta - 2 := by
      have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have hb := fun u => hf.toHolderDerivative.trial_curvature_bound hp2 hr2 hsigma x s u
      ((Optimization.le_leastCurvature_iff _ _).mp (hs.second hq) u)
    have he := (Optimization.le_leastCurvature_iff _ _).mpr hb
    change -_ ≤ leastHessianEigenvalue f (x + s) at he
    linarith

end CartisGouldToint.Chapter05.Section05
