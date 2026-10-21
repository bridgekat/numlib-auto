import Numlib.Optimization.TaylorModelGrowth
import Numlib.Optimization.TaylorOptimality
import Numlib.Optimization.HigherOrderRegularization
import Numlib.Analysis.Calculus.NormPowerSmoothness
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Regularization with Taylor-gap stopping tests

Order-indexed witnesses, legal outer trials, and the inner radius/accuracy state machine
use actual Taylor polynomials. A positive radial term dominates every finite Taylor model,
so its global minimum is attained in finite dimension. No convergence assumptions are
included in the transition relations.
-/

noncomputable section
open scoped Nat
open Set Metric
namespace Optimization.HigherOrderApproximateRegularization
open RegularizedTaylorModel TaylorCriticality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The factorial-normalized regularized model with degree one greater than its Taylor part. -/
abbrev model (f : E → ℝ) (p : ℕ) (x : E) (sigma : ℝ) : E → ℝ :=
  HigherOrderRegularization.model f p x sigma

/-- The model retains the objective's constant coefficient. -/
@[simp] theorem model_zero (f : E → ℝ) (p : ℕ) (x : E) (sigma : ℝ) :
    model f p x sigma 0 = f x := HigherOrderRegularization.model_zero f p x sigma

/-- The sum of the norms of the Taylor coefficients. -/
def coefficientBound (f : E → ℝ) (p : ℕ) (x : E) : ℝ :=
  ∑ j ∈ Finset.range (p + 1), ‖iteratedFDeriv ℝ j f x‖ / (j ! : ℝ)

/-- Beyond the unit ball every Taylor term is dominated by the highest scalar power. -/
theorem abs_taylorModel_le (f : E → ℝ) (p : ℕ) (x s : E) (hs : 1 ≤ ‖s‖) :
    |taylorModel f p x s| ≤ coefficientBound f p x * ‖s‖ ^ p :=
  norm_taylorModel_le f p x s hs

/-- Actual polynomial-plus-radial models eventually exceed every prescribed value. -/
theorem model_eventually_ge (f : E → ℝ) (p : ℕ) (x : E) {sigma : ℝ}
    (hsigma : 0 < sigma) (b : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s : E, R ≤ ‖s‖ → b ≤ model f p x sigma s := by
  exact eventually_ge_regularized_of_lower_bound (a := sigma / ((p + 1)! : ℝ)) p
    (div_pos hsigma (by positivity))
    (fun s hs => (abs_le.mp (abs_taylorModel_le f p x s hs)).1) b

/-- Every model sublevel is bounded by an actual radius obtained from radial domination. -/
theorem model_sublevel_isBounded (f : E → ℝ) (p : ℕ) (x : E) {sigma : ℝ}
    (hsigma : 0 < sigma) (b : ℝ) : Bornology.IsBounded {s | model f p x sigma s ≤ b} := by
  obtain ⟨R, hR, hb⟩ := model_eventually_ge f p x hsigma (b + 1)
  apply (isBounded_closedBall (x := (0 : E)) (r := R)).subset
  intro s hs
  have hn : ‖s‖ ≤ R := by
    by_contra hn
    have := hb s (le_of_lt (lt_of_not_ge hn))
    change model f p x sigma s ≤ b at hs
    linarith
  simpa only [mem_closedBall, dist_zero_right] using hn

/-- A positive regularized Taylor model has an attained global minimum in finite dimension. -/
theorem exists_model_minimizer [ProperSpace E] (f : E → ℝ) (p : ℕ) (x : E)
    {sigma : ℝ} (hsigma : 0 < sigma) : ∃ s : E, ∀ t : E,
      model f p x sigma s ≤ model f p x sigma t := by
  have hc : Continuous (model f p x sigma) :=
    (contDiff_taylorModel f p x 0).continuous.add
      (continuous_const.mul (continuous_norm.pow _))
  obtain ⟨R, hR, hb⟩ := model_eventually_ge f p x hsigma (f x)
  obtain ⟨s, hs, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    ⟨0, by simpa using hR⟩ hc.continuousOn
  refine ⟨s, fun t => ?_⟩
  by_cases ht : ‖t‖ ≤ R
  · exact hmin (by simpa using ht)
  · have hzero := hmin (show (0 : E) ∈ closedBall 0 R by simpa using hR)
    change model f p x sigma s ≤ model f p x sigma 0 at hzero
    rw [model_zero] at hzero
    exact hzero.trans (hb t (le_of_lt (lt_of_not_ge ht)))

/-- The actual degree-p model is Cᵖ for every order, including its origin. -/
theorem contDiff_model {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : F → ℝ) (p : ℕ) (x : F) (sigma : ℝ) :
    ContDiff ℝ p (model f p x sigma) := by
  have hn : ContDiff ℝ p (fun s : F => ‖s‖ ^ (p + 1)) := by
    simpa only [Real.rpow_natCast] using
      (contDiff_norm_rpow_of_lt (E := F) (n := p) (r := ((p + 1 : ℕ) : ℝ))
        (by push_cast; linarith))
  exact (contDiff_taylorModel f p x p).add (contDiff_const.mul hn)

/-- A fraction witness is feasible and captures the requested fraction of the actual gap. -/
structure GapWitness (f : E → ℝ) (j : ℕ) (x : E) (delta fraction : ℝ) (d : E) : Prop where
  feasible : ‖d‖ ≤ delta
  fraction_le : fraction * gapOn (taylorDecrement f j x) (closedBall 0 delta) ≤
    taylorDecrement f j x d

/-- Accuracy and update constants for a Taylor-gap regularization method. -/
structure Parameters extends ParameterUpdates.RegularizationParameters where
  p : ℕ
  q : ℕ
  order_pos : 1 ≤ q
  order_le : q ≤ p
  epsilon : ℕ → ℝ
  epsilon_pos : ∀ j, 1 ≤ j → j ≤ q → 0 < epsilon j
  epsilon_lt_one : ∀ j, 1 ≤ j → j ≤ q → epsilon j < 1
  theta : ℝ
  theta_pos : 0 < theta
  theta_lt_one : theta < 1
  fraction : ℝ
  fraction_pos : 0 < fraction
  fraction_le_one : fraction ≤ 1
/-- Positive radii bounded by one at every requested order. -/
def ValidRadii (P : Parameters) (delta : ℕ → ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ P.q → 0 < delta j ∧ delta j ≤ 1

/-- A failed test selects the first failing order and records all inspected witnesses. -/
structure FailedTest (P : Parameters) (f : E → ℝ) (x : E) (delta : ℕ → ℝ) where
  order : ℕ
  order_pos : 1 ≤ order
  order_le : order ≤ P.q
  direction : ℕ → E
  witness : ∀ j, 1 ≤ j → j ≤ order → GapWitness f j x (delta j) P.fraction (direction j)
  earlier : ∀ j, 1 ≤ j → j < order → taylorDecrement f j x (direction j) <
    P.fraction * P.epsilon j * delta j ^ j / (j ! : ℝ)
  fails : P.fraction * P.epsilon order * delta order ^ order / (order ! : ℝ) ≤
    taylorDecrement f order x (direction order)

/-- The successful outer stopping test uses the same computed fraction witnesses. -/
structure PassedTest (P : Parameters) (f : E → ℝ) (x : E) (delta : ℕ → ℝ) where
  direction : ℕ → E
  witness : ∀ j, 1 ≤ j → j ≤ P.q → GapWitness f j x (delta j) P.fraction (direction j)
  passes : ∀ j, 1 ≤ j → j ≤ P.q → taylorDecrement f j x (direction j) <
    P.fraction * P.epsilon j * delta j ^ j / (j ! : ℝ)

/-- All model tests or a long-step branch certify an admissible outer subproblem result. -/
structure ModelStep (P : Parameters) (f : E → ℝ) (x : E) (sigma : ℝ)
    (delta : ℕ → ℝ) where
  step : E
  radii : ℕ → ℝ
  radii_valid : ValidRadii P radii
  nonincrease : model f P.p x sigma step ≤ model f P.p x sigma 0
  direction : ℕ → E
  quality : (1 < ‖step‖ ∧ radii = delta) ∨
    (∀ j, 1 ≤ j → j ≤ P.q →
      GapWitness (model f P.p x sigma) j step (radii j) P.fraction (direction j) ∧
      taylorDecrement (model f P.p x sigma) j step (direction j) ≤
        P.fraction * P.theta * P.epsilon j * radii j ^ j / (j ! : ℝ))

/-- The three literal regularization-parameter update intervals. -/
def ParameterUpdate (P : Parameters) (rho sigma next : ℝ) : Prop :=
  if P.eta2 ≤ rho then max P.sigmaMin (P.gamma1 * sigma) ≤ next ∧ next ≤ sigma
  else if P.eta1 ≤ rho then sigma ≤ next ∧ next ≤ P.gamma2 * sigma
  else P.gamma2 * sigma ≤ next ∧ next ≤ P.gamma3 * sigma

/-- Outer state; the cache contains all derivatives of orders one through `cachedOrder`.
A rejected trial skips the next stopping test and retains the complete derivative cache. -/
structure OuterState (E : Type*) where
  point : E
  sigma : ℝ
  radii : ℕ → ℝ
  cachedOrder : ℕ
  test : Bool

/-- The outcome of one outer pass, distinguishing both termination locations. -/
inductive OuterOutcome (E : Type*) where
  | stopTest (state : OuterState E)
  | stopEqual (state : OuterState E)
  | next (state : OuterState E)

/-- One legal outer pass. Costs count individual derivative orders and objective evaluations;
initialization contributes one objective evaluation separately. -/
inductive OuterTransition (P : Parameters) (f : E → ℝ) :
    OuterState E → OuterOutcome E → ℕ → ℕ → Prop where
  | stop (a : OuterState E) (htest : a.test = true)
      (hcache : a.cachedOrder ≤ P.q) (hpass : PassedTest P f a.point a.radii) :
      OuterTransition P f a (.stopTest a) 0 (P.q - a.cachedOrder)
  | equal (a : OuterState E)
      (hfail : a.test = true → Nonempty (FailedTest P f a.point a.radii))
      (hcache : a.cachedOrder ≤ P.p)
      (trial : ModelStep P f a.point a.sigma a.radii)
      (heq : model f P.p a.point a.sigma trial.step = model f P.p a.point a.sigma 0) :
      OuterTransition P f a (.stopEqual a) 0 (P.p - a.cachedOrder)
  | trial (a : OuterState E)
      (hfail : a.test = true → Nonempty (FailedTest P f a.point a.radii))
      (hcache : a.cachedOrder ≤ P.p)
      (trial : ModelStep P f a.point a.sigma a.radii)
      (hstrict : model f P.p a.point a.sigma trial.step < model f P.p a.point a.sigma 0)
      (nextSigma : ℝ)
      (hupdate : ParameterUpdate P
        ((f a.point - f (a.point + trial.step)) /
          taylorDecrement f P.p a.point trial.step) a.sigma nextSigma) :
      OuterTransition P f a (.next
        (if P.eta1 ≤ (f a.point - f (a.point + trial.step)) /
            taylorDecrement f P.p a.point trial.step then
          ⟨a.point + trial.step, nextSigma, trial.radii, 0, true⟩ else
          ⟨a.point, nextSigma, a.radii, P.p, false⟩)) 1 (P.p - a.cachedOrder)

/-- The outer initialization fixes the actual starting point, parameter, and cache. -/
def IsInitial (P : Parameters) (x : E) (sigma : ℝ) (delta : ℕ → ℝ)
    (a : OuterState E) : Prop :=
  P.sigmaMin ≤ sigma ∧ ValidRadii P delta ∧ a = ⟨x, sigma, delta, 0, true⟩

/-- Inner program counters separate recomputing a model minimizer from inspecting an order. -/
inductive InnerPhase where
  | minimize
  | inspect (order : ℕ)
  | returned
  deriving DecidableEq

/-- Inner accuracy, radius vector, selected point, and program counter. -/
structure InnerState (E : Type*) where
  mu : ℝ
  radii : ℕ → ℝ
  step : E
  phase : InnerPhase

/-- The inner initialization uses unit radii and any positive fraction at most one. -/
def InnerInitial (a : InnerState E) : Prop :=
  0 < a.mu ∧ a.mu ≤ 1 ∧ a.radii = (fun _ => 1) ∧ a.phase = .minimize

/-- The detailed inner procedure as a transition relation. The minimum value is represented
by an attained minimizer, whose existence follows from `exists_model_minimizer`.
The long-step test includes the unit boundary, as in the detailed inner procedure. -/
inductive InnerTransition (P : Parameters) (m : E → ℝ) (minimizer : E) :
    InnerState E → InnerState E → Prop where
  | minimize (a : InnerState E) (hphase : a.phase = .minimize)
      (s : E) (hfrac : a.mu * (m 0 - m minimizer) ≤ m 0 - m s) :
      InnerTransition P m minimizer a
        ⟨a.mu, a.radii, s, if 1 ≤ ‖s‖ then .returned else .inspect 1⟩
  | pass (a : InnerState E) (j : ℕ) (hphase : a.phase = .inspect j)
      (hj : 1 ≤ j) (hjq : j ≤ P.q) (d : E)
      (hw : GapWitness m j a.step (a.radii j) P.fraction d)
      (htest : taylorDecrement m j a.step d ≤
        P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ)) :
      InnerTransition P m minimizer a
        ⟨a.mu, a.radii, a.step, if j = P.q then .returned else .inspect (j + 1)⟩
  | halve (a : InnerState E) (j : ℕ) (hphase : a.phase = .inspect j)
      (hj : 3 ≤ j) (hjq : j ≤ P.q) (d : E)
      (hw : GapWitness m j a.step (a.radii j) P.fraction d)
      (hfail : P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ) <
        taylorDecrement m j a.step d)
      (hsmall : m a.step - m (a.step + d) <
        (1 / 2 : ℝ) * P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ)) :
      InnerTransition P m minimizer a
        ⟨a.mu, Function.update a.radii j (a.radii j / 2), a.step, .inspect j⟩
  | improve (a : InnerState E) (j : ℕ) (hphase : a.phase = .inspect j)
      (hj : 1 ≤ j) (hjq : j ≤ P.q) (d : E)
      (hw : GapWitness m j a.step (a.radii j) P.fraction d)
      (hfail : P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ) <
        taylorDecrement m j a.step d)
      (hother : j ≤ 2 ∨
        (1 / 2 : ℝ) * P.fraction * P.theta * P.epsilon j * a.radii j ^ j / (j ! : ℝ) ≤
          m a.step - m (a.step + d)) :
      InnerTransition P m minimizer a
        ⟨(1 + a.mu) / 2, a.radii, a.step, .minimize⟩

/-- A corrected inner transition for use with the strict outer long-step interface.
At model minimization it returns early only for norm strictly greater than one and copies
the inherited outer radii on that branch. All inspection, halving and accuracy transitions
are the original ones. The unmodified `InnerTransition` remains available separately. -/
def CorrectedInnerTransition (P : Parameters) (m : E → ℝ) (minimizer : E)
    (inherited : ℕ → ℝ) (a b : InnerState E) : Prop :=
  if a.phase = .minimize then
    ∃ s : E, a.mu * (m 0 - m minimizer) ≤ m 0 - m s ∧
      b = ⟨a.mu, if 1 < ‖s‖ then inherited else a.radii, s,
        if 1 < ‖s‖ then .returned else .inspect 1⟩
  else InnerTransition P m minimizer a b

/-- A finite outer execution records every trial, its outcome, and its actual evaluation costs.
The last outcome may continue, so this interface does not assume finite termination. -/
structure OuterExecution (P : Parameters) (f : E → ℝ) (x : E) (sigma : ℝ)
    (delta : ℕ → ℝ) (N : ℕ) where
  state : ℕ → OuterState E
  functionCalls : ℕ → ℕ
  derivativeCalls : ℕ → ℕ
  last : OuterOutcome E
  initial : IsInitial P x sigma delta (state 0)
  valid : ∀ k, k ≤ N → P.sigmaMin ≤ (state k).sigma ∧
    ValidRadii P (state k).radii ∧ (state k).cachedOrder ≤ P.p ∧
    ((state k).test = false → (state k).cachedOrder = P.p)
  transition : ∀ k, k < N → OuterTransition P f (state k) (.next (state (k + 1)))
    (functionCalls k) (derivativeCalls k)
  final : OuterTransition P f (state N) last (functionCalls N) (derivativeCalls N)

/-- Total actual objective evaluations, including the initial objective value. -/
def OuterExecution.functionCount {P : Parameters} {f : E → ℝ} {x : E} {sigma : ℝ}
    {delta : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x sigma delta N) : ℕ :=
  1 + ∑ k ∈ Finset.range (N + 1), run.functionCalls k

/-- Total actual evaluations of individual derivative orders. -/
def OuterExecution.derivativeCount {P : Parameters} {f : E → ℝ} {x : E} {sigma : ℝ}
    {delta : ℕ → ℝ} {N : ℕ} (run : OuterExecution P f x sigma delta N) : ℕ :=
  ∑ k ∈ Finset.range (N + 1), run.derivativeCalls k

/-- The continuous Taylor decrement always has a feasible exact, hence fractional, witness. -/
theorem exists_gapWitness [ProperSpace E] (f : E → ℝ) (j : ℕ) (x : E)
    {delta fraction : ℝ} (hd : 0 ≤ delta) (hf : fraction ≤ 1) :
    ∃ d : E, GapWitness f j x delta fraction d := by
  have hz : (0 : E) ∈ closedBall 0 delta := by simpa using hd
  obtain ⟨d, hdmem, heq⟩ := exists_eq_gapOn (isCompact_closedBall 0 delta)
    ⟨0, hz⟩ (continuous_taylorDecrement f j x).continuousOn
  have hgap : 0 ≤ gapOn (taylorDecrement f j x) (closedBall 0 delta) :=
    gapOn_nonneg (isCompact_closedBall 0 delta)
      (continuous_taylorDecrement f j x).continuousOn hz (by simp)
  refine ⟨d, ⟨by simpa using hdmem, ?_⟩⟩
  rw [heq]
  exact mul_le_of_le_one_left hgap hf

/-- Passing every computed fraction test bounds the actual gaps at all requested orders. -/
theorem PassedTest.gap_le {P : Parameters} {f : E → ℝ} {x : E}
    {delta : ℕ → ℝ} (h : PassedTest P f x delta) {j : ℕ}
    (hj : 1 ≤ j) (hjq : j ≤ P.q) :
    gapOn (taylorDecrement f j x) (closedBall 0 (delta j)) ≤
      P.epsilon j * delta j ^ j / (j ! : ℝ) := by
  have hlow := (h.witness j hj hjq).fraction_le
  have hupp := h.passes j hj hjq
  have heq : P.fraction * P.epsilon j * delta j ^ j / (j ! : ℝ) =
      P.fraction * (P.epsilon j * delta j ^ j / (j ! : ℝ)) := by ring
  rw [heq] at hupp
  nlinarith [P.fraction_pos]

/-- Strict model decrease makes the ratio denominator strictly positive. -/
theorem taylorDecrement_pos_of_model_lt {f : E → ℝ} {p : ℕ} {x s : E}
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (h : model f p x sigma s < model f p x sigma 0) :
    0 < taylorDecrement f p x s := by
  rw [model_zero] at h
  rw [taylorDecrement_eq]
  unfold model HigherOrderRegularization.model at h
  have : 0 ≤ sigma / ((p + 1)! : ℝ) * ‖s‖ ^ (p + 1) := by positivity
  linarith

/-- The update intervals preserve the positive parameter floor. -/
theorem ParameterUpdate.floor_le {P : Parameters} {rho sigma next : ℝ}
    (h : ParameterUpdate P rho sigma next) (hs : P.sigmaMin ≤ sigma) :
    P.sigmaMin ≤ next := by
  unfold ParameterUpdate at h
  split_ifs at h with hvery hsuccess
  · exact (le_max_left _ _).trans h.1
  · exact hs.trans h.1
  · have hs0 : 0 ≤ sigma := P.sigmaMin_pos.le.trans hs
    have hmul : sigma ≤ P.gamma2 * sigma := by nlinarith [P.one_lt_gamma2]
    exact hs.trans (hmul.trans h.1)

omit [NormedSpace ℝ E] in
/-- Any positive fraction of the true global model decrease yields model nonincrease. -/
theorem model_nonincrease_of_fraction {m : E → ℝ} {s minimizer : E} {mu : ℝ}
    (hmin : ∀ t, m minimizer ≤ m t) (hmu : 0 ≤ mu)
    (hfrac : mu * (m 0 - m minimizer) ≤ m 0 - m s) : m s ≤ m 0 := by
  have := mul_nonneg hmu (sub_nonneg.mpr (hmin 0))
  linarith

omit [NormedSpace ℝ E] in
/-- Fraction one necessarily selects a global model minimizer. -/
theorem isMin_of_fraction_one {m : E → ℝ} {s minimizer : E}
    (hmin : ∀ t, m minimizer ≤ m t)
    (hfrac : 1 * (m 0 - m minimizer) ≤ m 0 - m s) :
    ∀ t, m s ≤ m t := by
  intro t
  have := hmin t
  linarith

/-- Fractional model reduction is attainable, including the endpoint fraction one. -/
theorem exists_fraction_step [ProperSpace E] (f : E → ℝ) (p : ℕ) (x : E)
    {sigma mu : ℝ} (hs : 0 < sigma) (hmu : mu ≤ 1) :
    ∃ minimizer s : E,
      (∀ t, model f p x sigma minimizer ≤ model f p x sigma t) ∧
      mu * (model f p x sigma 0 - model f p x sigma minimizer) ≤
        model f p x sigma 0 - model f p x sigma s := by
  obtain ⟨s, hsmin⟩ := exists_model_minimizer f p x hs
  refine ⟨s, s, hsmin, ?_⟩
  exact mul_le_of_le_one_left (sub_nonneg.mpr (hsmin 0)) hmu

/-- The inner procedure's finite prefixes are executable without assuming eventual return. -/
structure InnerExecution (P : Parameters) (m : E → ℝ) (minimizer : E) (N : ℕ) where
  state : ℕ → InnerState E
  is_minimizer : ∀ t, m minimizer ≤ m t
  initial : InnerInitial (state 0)
  transition : ∀ k, k < N → InnerTransition P m minimizer (state k) (state (k + 1))

/-- Inner transitions never change the first two optimality radii. -/
theorem InnerTransition.radii_low_eq {P : Parameters} {m : E → ℝ} {minimizer : E}
    {a b : InnerState E} (h : InnerTransition P m minimizer a b)
    {j : ℕ} (hj : j ≤ 2) : b.radii j = a.radii j := by
  cases h with
  | minimize => rfl
  | pass => rfl
  | halve i hphase hi hiq d hw hfail hsmall =>
    change Function.update a.radii i (a.radii i / 2) j = a.radii j
    exact Function.update_of_ne (by omega) _ _
  | improve => rfl

/-- The accuracy fraction remains positive, bounded by one, and nondecreasing. -/
theorem InnerTransition.mu_bounds {P : Parameters} {m : E → ℝ} {minimizer : E}
    {a b : InnerState E} (h : InnerTransition P m minimizer a b)
    (ha : 0 < a.mu) (ha1 : a.mu ≤ 1) :
    0 < b.mu ∧ b.mu ≤ 1 ∧ a.mu ≤ b.mu := by
  cases h <;> dsimp <;> exact ⟨by linarith, by linarith, by linarith⟩

/-- Every finite inner execution retains unit radii at orders one and two. -/
theorem InnerExecution.radii_low {P : Parameters} {m : E → ℝ} {minimizer : E}
    {N : ℕ} (h : InnerExecution P m minimizer N) {k j : ℕ}
    (hk : k ≤ N) (hj : j ≤ 2) : (h.state k).radii j = 1 := by
  induction k with
  | zero => rw [h.initial.2.2.1]
  | succ k ih =>
    rw [(h.transition k (by omega)).radii_low_eq hj]
    exact ih (by omega)

end Optimization.HigherOrderApproximateRegularization
