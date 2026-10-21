import Numlib.Optimization.ConstrainedTaylorCriticality
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Residual least-squares calls and the least-norm wrapper

An INNER call carries its actual finite point/state trace and evaluation event lists,
including its terminal check. The abstract cost contract uses the initial objective above
its lower bound, with a maximum over active orders. The wrapper never assumes a residual
contraction: it follows from failure of its actual residual-scaled Taylor-gap tests.
-/

open Set Metric
namespace Optimization.ResidualLeastSquares
open ConstrainedTaylorCriticality TaylorCriticality

/-- The two evaluation channels counted by a least-squares solver. -/
inductive EvaluationKind where
  /-- An objective or residual value evaluation. -/
  | function
  /-- A derivative evaluation, exact or inexact according to the solver. -/
  | derivative
  deriving DecidableEq

/-- A finite inner execution, retaining algorithmic state and all query events. The event
list at `length` includes the terminal test, even for a zero-step inner execution. -/
structure InnerTrace (E S : Type*) where
  /-- Inner points, used only through the terminal index. -/
  point : ℕ → E
  /-- Warm-startable solver state. -/
  state : ℕ → S
  /-- Number of inner transitions. -/
  length : ℕ
  /-- Evaluations made at each visited inner stage, including the terminal stage. -/
  queries : ℕ → List EvaluationKind

/-- Count every recorded invocation in one evaluation channel, including terminal events. -/
def InnerTrace.evaluations {E S : Type*} (t : InnerTrace E S) (a : EvaluationKind) : ℕ :=
  ∑ i ∈ Finset.range (t.length + 1), (t.queries i).count a

/-- Maximum of the weights of the active orders, with a zero sentinel for an empty set. -/
noncomputable def orderMaximum (q : ℕ) (w : ℕ → ℝ) : ℝ :=
  (insert 0 (Finset.Icc 1 q)).sup' (by simp) (fun j => if j = 0 then 0 else w j)

/-- The order maximum is nonnegative. -/
theorem orderMaximum_nonneg (q : ℕ) (w : ℕ → ℝ) : 0 ≤ orderMaximum q w := by
  have hh := Finset.le_sup' (s := insert 0 (Finset.Icc 1 q))
    (f := fun j => if j = 0 then (0 : ℝ) else w j) (by simp : 0 ∈ _)
  simpa only [orderMaximum, ite_true] using hh

/-- Each active weight is bounded by the order maximum. -/
theorem le_orderMaximum {q j : ℕ} (w : ℕ → ℝ) (hj : j ∈ Finset.Icc 1 q) :
    w j ≤ orderMaximum q w := by
  have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  have hh := Finset.le_sup' (s := insert 0 (Finset.Icc 1 q))
    (f := fun j => if j = 0 then (0 : ℝ) else w j) (Finset.mem_insert_of_mem hj)
  simpa only [ite_eq_right hj0, orderMaximum] using hh

/-- A nonnegative common bound on the active weights bounds their maximum. -/
theorem orderMaximum_le {q : ℕ} {w : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j ∈ Finset.Icc 1 q, w j ≤ B) : orderMaximum q w ≤ B := by
  apply Finset.sup'_le
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · simpa using hB
  · split_ifs
    · exact hB
    · exact h j hj

/-- The largest inverse tolerance weight among the active derivative orders. -/
noncomputable def toleranceWeight (q : ℕ) (τ π : ℕ → ℝ) : ℝ :=
  orderMaximum q (fun j => τ j ^ (-π j))

/-- The maximum inverse tolerance weight is nonnegative, including an empty order set. -/
theorem toleranceWeight_nonneg (q : ℕ) (τ π : ℕ → ℝ) :
    0 ≤ toleranceWeight q τ π := orderMaximum_nonneg q _

/-- Every active inverse tolerance weight is bounded by their maximum. -/
theorem le_toleranceWeight {q j : ℕ} (τ π : ℕ → ℝ) (hj : j ∈ Finset.Icc 1 q) :
    τ j ^ (-π j) ≤ toleranceWeight q τ π :=
  le_orderMaximum (fun j => τ j ^ (-π j)) hj

/-- A common nonnegative upper bound on all active weights bounds their maximum. -/
theorem toleranceWeight_le {q : ℕ} {τ π : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ j ∈ Finset.Icc 1 q, τ j ^ (-π j) ≤ B) : toleranceWeight q τ π ≤ B :=
  orderMaximum_le hB h

/-- The explicit tolerance-only maximum in a residual-scaled INNER evaluation bound. -/
noncomputable def residualCostWeight (q : ℕ) (β ε₀ : ℝ) (ε π : ℕ → ℝ) : ℝ :=
  orderMaximum q (fun j => β ^ (-π j) * ε₀ ^ (1 - π j) * ε j ^ (-π j))

/-- The residual cost weight is nonnegative. -/
theorem residualCostWeight_nonneg (q : ℕ) (β ε₀ : ℝ) (ε π : ℕ → ℝ) :
    0 ≤ residualCostWeight q β ε₀ ε π := orderMaximum_nonneg q _

/-- Each active explicit residual-cost weight is bounded by their maximum. -/
theorem le_residualCostWeight {q j : ℕ} (β ε₀ : ℝ) (ε π : ℕ → ℝ)
    (hj : j ∈ Finset.Icc 1 q) :
    β ^ (-π j) * ε₀ ^ (1 - π j) * ε j ^ (-π j) ≤ residualCostWeight q β ε₀ ε π :=
  le_orderMaximum (fun j => β ^ (-π j) * ε₀ ^ (1 - π j) * ε j ^ (-π j)) hj

/-- A nonnegative common upper bound on the explicit order weights bounds their maximum. -/
theorem residualCostWeight_le {q : ℕ} {β ε₀ : ℝ} {ε π : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (h : ∀ j ∈ Finset.Icc 1 q, β ^ (-π j) * ε₀ ^ (1 - π j) * ε j ^ (-π j) ≤ B) :
    residualCostWeight q β ε₀ ε π ≤ B := orderMaximum_le hB h

variable {E S F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

/-- Source-style abstract INNER guarantees. The supplied transition and terminal relations
specify the solver being used; event lists count every call. Cost constants and exponents
are fixed inputs, shared between invocations, rather than outputs chosen after the run. -/
structure InnerContract (X : Set E) (f : E → ℝ) (low : ℝ) (q : ℕ) (τ δ π : ℕ → ℝ)
    (κ : EvaluationKind → ℝ)
    (step : (ℕ → ℝ) → E × S → E × S → List EvaluationKind → Prop)
    (terminal : (ℕ → ℝ) → E × S → List EvaluationKind → Prop)
    (t : InnerTrace E S) : Prop where
  /-- Every visited point is feasible. -/
  feasible : ∀ i ≤ t.length, t.point i ∈ X
  /-- Each recorded transition obeys the selected solver's actual rules. -/
  legal : ∀ i < t.length,
    step τ (t.point i, t.state i) (t.point (i + 1), t.state (i + 1)) (t.queries i)
  /-- The last event list performs the supplied solver's terminal checks. -/
  checked : terminal τ (t.point t.length, t.state t.length) (t.queries t.length)
  /-- The returned objective value is evaluated and charged to the terminal event list. -/
  final_value : 1 ≤ (t.queries t.length).count .function
  /-- Monitoring the objective ensures objective nonincrease at return. -/
  objective_nonincrease : f (t.point t.length) ≤ f (t.point 0)
  /-- The reference value bounds the objective throughout the feasible set. -/
  lower_bound : ∀ x ∈ X, low ≤ f x
  /-- Active tolerances are positive and at most one. -/
  tolerance : ∀ j ∈ Finset.Icc 1 q, 0 < τ j ∧ τ j ≤ 1
  /-- Returned radii are positive and at most one. -/
  radius : ∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1
  /-- The abstract complexity exponents exceed one. -/
  exponent : ∀ j ∈ Finset.Icc 1 q, 1 < π j
  /-- Approximate optimality concerns the actual objective Taylor jets. -/
  gap : ∀ j ∈ Finset.Icc 1 q,
    gapOn (taylorDecrement f j (t.point t.length))
      (feasibleDisplacements X (t.point t.length) ∩ closedBall 0 (δ j)) ≤
        τ j * δ j ^ j / (j.factorial : ℝ)
  /-- Complexity coefficients are nonnegative. -/
  coefficient : ∀ a, 0 ≤ κ a
  /-- Both evaluation channels satisfy the starting-objective bound above the lower bound. -/
  cost : ∀ a, (t.evaluations a : ℝ) ≤
    κ a * (f (t.point 0) - low) * toleranceWeight q τ π

/-- A wrapper trace retains the output radii, the warm-start state, and each complete inner
execution. Radius zero at the initial index is a sentinel: no initial gap test is performed. -/
structure Trace (E S : Type*) where
  /-- Outer iterates. -/
  point : ℕ → E
  /-- Returned test radii, with zero sentinel at the initial point. -/
  radius : ℕ → ℕ → ℝ
  /-- Solver state at each outer iterate. -/
  state : ℕ → S
  /-- Inner execution between each consecutive pair of outer iterates. -/
  inner : ℕ → InnerTrace E S

/-- Literal wrapper stopping: first test only the initial residual, and after an INNER call
also test the residual-scaled gaps at the radii actually returned. -/
def Stops (X : Set E) (r : E → F) (q : ℕ) (ε₀ : ℝ) (ε : ℕ → ℝ)
    (t : Trace E S) (k : ℕ) : Prop :=
  ‖r (t.point k)‖ ≤ ε₀ ∨ (0 < k ∧
    ResidualScaledCertificate X r q ε₀ ε (t.radius k) (t.point k))

/-- A supplied execution of the least-norm wrapper. INNER contracts are required only at
indices at which the literal stopping tests fail; no termination or contraction is assumed. -/
structure Execution (X : Set E) (r : E → F) (q : ℕ) (ε₀ β : ℝ)
    (ε π : ℕ → ℝ) (κ : EvaluationKind → ℝ)
    (step : (ℕ → ℝ) → E × S → E × S → List EvaluationKind → Prop)
    (terminal : (ℕ → ℝ) → E × S → List EvaluationKind → Prop)
    (t : Trace E S) : Prop where
  /-- A nonempty active order set. -/
  order_pos : 1 ≤ q
  /-- The initial point is feasible. -/
  initial_feasible : t.point 0 ∈ X
  /-- Primal tolerance is positive and below one. -/
  primal : 0 < ε₀ ∧ ε₀ < 1
  /-- Dual tolerances are positive and at most one, including the endpoint used by TWO-PHASE. -/
  dual : ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1
  /-- The geometric factor lies strictly between zero and one. -/
  factor : 0 < β ∧ β < 1
  /-- The reciprocal restriction is used only in the nonzero residual branch. -/
  initial_scaling : ε₀ < ‖r (t.point 0)‖ → β < (‖r (t.point 0)‖)⁻¹
  /-- The initial sentinel does not supply fictitious gap radii. -/
  initial_radius : ∀ j, t.radius 0 j = 0
  /-- Every INNER call starts at the preceding outer iterate. -/
  start : ∀ k, (t.inner k).point 0 = t.point k
  /-- Every INNER call ends at the next outer iterate. -/
  finish : ∀ k, (t.inner k).point (t.inner k).length = t.point (k + 1)
  /-- Warm-start input agrees with the outer algorithm's state. -/
  state_start : ∀ k, (t.inner k).state 0 = t.state k
  /-- Returned state is retained for the following call. -/
  state_finish : ∀ k, (t.inner k).state (t.inner k).length = t.state (k + 1)
  /-- The shared complexity coefficients are nonnegative even in the zero-call branch. -/
  coefficient : ∀ a, 0 ≤ κ a
  /-- Every executed call uses exactly the residual-scaled input tolerances. -/
  solve : ∀ k, ¬Stops X r q ε₀ ε t k →
    InnerContract X (squaredResidual r) 0 q
      (fun j => β * ‖r (t.point k)‖ * ε j) (t.radius (k + 1)) π
      κ step terminal (t.inner k)

/-- Count both successful and terminal INNER invocations before outer index `K`. The
initial outer residual check is counted separately, so the zero-call branch stays explicit. -/
def evaluations (t : Trace E S) (a : EvaluationKind) (K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range K, (t.inner k).evaluations a

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The initial stopping test performs no INNER calls. -/
@[simp] theorem evaluations_zero (t : Trace E S) (a : EvaluationKind) :
    evaluations t a 0 = 0 := by simp [evaluations]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Extending the outer prefix counts exactly the next complete inner invocation. -/
theorem evaluations_succ (t : Trace E S) (a : EvaluationKind) (K : ℕ) :
    evaluations t a (K + 1) = evaluations t a K + (t.inner K).evaluations a := by
  simp [evaluations, Finset.sum_range_succ]

/-- Full wrapper accounting adds the initial residual evaluation to the complete INNER
invocation counts. Returned residuals are available from each inner terminal event list. -/
def totalEvaluations (t : Trace E S) (a : EvaluationKind) (K : ℕ) : ℕ :=
  (if a = .function then 1 else 0) + evaluations t a K

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- With no INNER invocations only the initial residual query is made. -/
@[simp] theorem totalEvaluations_zero (t : Trace E S) (a : EvaluationKind) :
    totalEvaluations t a 0 = if a = .function then 1 else 0 := by
  simp [totalEvaluations]

variable {X : Set E} {r : E → F} {q : ℕ} {ε₀ β : ℝ} {ε π : ℕ → ℝ}
  {κ : EvaluationKind → ℝ}
  {step : (ℕ → ℝ) → E × S → E × S → List EvaluationKind → Prop}
  {terminal : (ℕ → ℝ) → E × S → List EvaluationKind → Prop} {t : Trace E S}

/-- With the initial radius sentinel, the generic certificate is exactly the literal
wrapper stopping test, including the residual-only initialization branch. -/
theorem Execution.stops_iff_certificate
    (h : Execution X r q ε₀ β ε π κ step terminal t) (k : ℕ) :
    Stops X r q ε₀ ε t k ↔
      ResidualScaledCertificate X r q ε₀ ε (t.radius k) (t.point k) := by
  constructor
  · rintro (hr | ⟨_, hc⟩)
    · exact Or.inl hr
    · exact hc
  · intro hc
    by_cases hk : 0 < k
    · exact Or.inr ⟨hk, hc⟩
    · have hk0 : k = 0 := by omega
      subst k
      rcases hc with hr | hg
      · exact Or.inl hr
      · have hh := (hg 1 (Finset.mem_Icc.mpr ⟨le_rfl, h.order_pos⟩)).1
        rw [h.initial_radius] at hh
        exact (lt_irrefl 0 hh).elim

/-- Failure of the output stopping test forces a strict contraction. The conclusion is
proved from the actual INNER gap inequalities, rather than included in the execution. -/
theorem Execution.contraction (h : Execution X r q ε₀ β ε π κ step terminal t)
    {k : ℕ} (hk : ¬Stops X r q ε₀ ε t k)
    (hk1 : ¬Stops X r q ε₀ ε t (k + 1)) :
    ‖r (t.point (k + 1))‖ < β * ‖r (t.point k)‖ := by
  have hs := h.solve k hk
  have hg := hs.gap
  rw [h.finish] at hg
  exact (certificate_or_residual_contraction (fun j hj => (h.dual j hj).1.le)
    (fun j hj => (hs.radius j hj).1) hg).resolve_left
      (fun hc => hk1 ((h.stops_iff_certificate (k + 1)).2 hc))

/-- Every positive nonterminal index in an actual prefix satisfies the strict geometric
residual bound. At index zero the corresponding bound is equality. -/
theorem Execution.geometric (h : Execution X r q ε₀ β ε π κ step terminal t)
    {K : ℕ} (hbefore : ∀ k < K, ¬Stops X r q ε₀ ε t k) :
    ∀ k < K, 0 < k → ‖r (t.point k)‖ < ‖r (t.point 0)‖ * β ^ k := by
  intro k hk hpos
  induction k with
  | zero => omega
  | succ k ih =>
    have hkK : k < K := by omega
    have hc := h.contraction (hbefore k hkK) (hbefore (k + 1) hk)
    by_cases hk0 : k = 0
    · subst k
      simpa [mul_comm] using hc
    · have hi := ih hkK (by omega)
      calc
        ‖r (t.point (k + 1))‖ < β * ‖r (t.point k)‖ := hc
        _ < β * (‖r (t.point 0)‖ * β ^ k) := mul_lt_mul_of_pos_left hi h.factor.1
        _ = ‖r (t.point 0)‖ * β ^ (k + 1) := by ring

/-- The wrapper reaches its first literal stopping index within the natural logarithmic
ceiling, with zero INNER invocations when the initial residual is already small. -/
theorem Execution.terminates (h : Execution X r q ε₀ β ε π κ step terminal t) :
    ∃ K ≤ MeasureDomination.geometricIterationCount ‖r (t.point 0)‖ β⁻¹ ε₀,
      Stops X r q ε₀ ε t K ∧ ∀ k < K, ¬Stops X r q ε₀ ε t k := by
  classical
  have hex : ∃ K ≤ MeasureDomination.geometricIterationCount ‖r (t.point 0)‖ β⁻¹ ε₀,
      ResidualScaledCertificate X r q ε₀ ε (t.radius K) (t.point K) := by
    apply residual_wrapper_terminates_of_scaled_gaps h.primal.1 h.factor.1 h.factor.2
      (fun j hj => (h.dual j hj).1.le)
    intro k hk
    have hs := h.solve k (fun hs => hk ((h.stops_iff_certificate k).1 hs))
    refine ⟨fun j hj => (hs.radius j hj).1, ?_⟩
    simpa only [h.finish] using hs.gap
  obtain ⟨N, hN, hc⟩ := hex
  have he : ∃ K, Stops X r q ε₀ ε t K := ⟨N, (h.stops_iff_certificate N).2 hc⟩
  refine ⟨Nat.find he, (Nat.find_min' he ((h.stops_iff_certificate N).2 hc)).trans hN,
    Nat.find_spec he, ?_⟩
  exact fun k hk => Nat.find_min he hk

/-- The source cost contract adds across the actual invocation prefix and includes the
last call that produces the stopping iterate. This finite bound does not yet estimate the
residual-dependent sum by a tolerance-only geometric series. -/
theorem Execution.evaluations_le (h : Execution X r q ε₀ β ε π κ step terminal t)
    {K : ℕ} (hbefore : ∀ k < K, ¬Stops X r q ε₀ ε t k) (a : EvaluationKind) :
    (evaluations t a K : ℝ) ≤ ∑ k ∈ Finset.range K,
      κ a * squaredResidual r (t.point k) *
        toleranceWeight q (fun j => β * ‖r (t.point k)‖ * ε j) π := by
  simp only [evaluations, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hs := (h.solve k (hbefore k (Finset.mem_range.mp hk))).cost a
  simpa only [h.start, sub_zero] using hs

/-- Norm nonincrease of each actual INNER return preserves the initial residual level
throughout a prefix, including its final returned point. -/
theorem Execution.residual_le_initial
    (h : Execution X r q ε₀ β ε π κ step terminal t)
    {K : ℕ} (hbefore : ∀ k < K, ¬Stops X r q ε₀ ε t k) :
    ∀ k ≤ K, ‖r (t.point k)‖ ≤ ‖r (t.point 0)‖ := by
  intro k hk
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have hs := (h.solve k (hbefore k (by omega))).objective_nonincrease
    simp only [h.finish, h.start, squaredResidual] at hs
    have hh : ‖r (t.point (k + 1))‖ ≤ ‖r (t.point k)‖ := by
      nlinarith [norm_nonneg (r (t.point (k + 1))), norm_nonneg (r (t.point k))]
    exact hh.trans (ih (by omega))

/-- Full evaluation accounting includes the initial residual check and the complete
terminal INNER call. The residual-dependent finite sum is still explicit. -/
theorem Execution.totalEvaluations_le
    (h : Execution X r q ε₀ β ε π κ step terminal t)
    {K : ℕ} (hbefore : ∀ k < K, ¬Stops X r q ε₀ ε t k) (a : EvaluationKind) :
    (totalEvaluations t a K : ℝ) ≤ (if a = .function then 1 else 0) +
      ∑ k ∈ Finset.range K, κ a * squaredResidual r (t.point k) *
        toleranceWeight q (fun j => β * ‖r (t.point k)‖ * ε j) π := by
  have hc := h.evaluations_le hbefore a
  simp only [totalEvaluations, Nat.cast_add]
  push_cast
  linarith only [hc]

/-- The scalar inverse-power estimate used to sum residual-scaled INNER costs. -/
theorem residual_inverse_power_le {R e β η p : ℝ} (he : 0 < e) (heR : e ≤ R)
    (hβ : 0 ≤ β) (hη : 0 ≤ η) (hp : 1 ≤ p) :
    R * (β * R * η) ^ (-p) ≤ β ^ (-p) * e ^ (1 - p) * η ^ (-p) := by
  have hR : 0 < R := he.trans_le heR
  have hpow := Real.rpow_le_rpow_of_nonpos he heR (by linarith : 1 - p ≤ 0)
  calc
    R * (β * R * η) ^ (-p) = β ^ (-p) * R ^ (1 - p) * η ^ (-p) := by
      rw [Real.mul_rpow (mul_nonneg hβ hR.le) hη,
        Real.mul_rpow hβ hR.le]
      have hr : R * R ^ (-p) = R ^ (1 - p) := by
        calc
          R * R ^ (-p) = R ^ (1 : ℝ) * R ^ (-p) := by rw [Real.rpow_one]
          _ = R ^ (1 + -p) := (Real.rpow_add hR _ _).symm
          _ = R ^ (1 - p) := rfl
      calc
        R * (β ^ (-p) * R ^ (-p) * η ^ (-p)) =
          β ^ (-p) * (R * R ^ (-p)) * η ^ (-p) := by ring
        _ = _ := by rw [hr]
    _ ≤ β ^ (-p) * e ^ (1 - p) * η ^ (-p) := by
      gcongr

/-- A finite geometric prefix has total mass at most the inverse contraction gap. -/
theorem sum_geometric_le {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, β ^ k ≤ 1 / (1 - β) := by
  simpa only [Finset.range_eq_Ico, pow_zero] using
    (geom_sum_Ico_le_of_lt_one (m := 0) (n := K) hβ hβ1)

/-- A tolerance-only evaluation bound with denominator `1 - β`. The scalar `B` is any
nonnegative common upper bound on the displayed, explicit order weights. This avoids an
interchange of a finite sum and a maximum. The initial residual evaluation is included. -/
theorem Execution.totalEvaluations_le_uniform
    (h : Execution X r q ε₀ β ε π κ step terminal t)
    {K : ℕ} (hbefore : ∀ k < K, ¬Stops X r q ε₀ ε t k)
    {B : ℝ} (hB : 0 ≤ B)
    (hweight : ∀ j ∈ Finset.Icc 1 q,
      β ^ (-π j) * ε₀ ^ (1 - π j) * ε j ^ (-π j) ≤ B)
    (a : EvaluationKind) :
    (totalEvaluations t a K : ℝ) ≤ (if a = .function then 1 else 0) +
      κ a / 2 * ‖r (t.point 0)‖ * B / (1 - β) := by
  have hκ := h.coefficient a
  have hnorm : ∀ k < K, ‖r (t.point k)‖ ≤ ‖r (t.point 0)‖ * β ^ k := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k; simp
    · exact (h.geometric hbefore k hk (by omega)).le
  have hcall : ∀ k < K,
      ((t.inner k).evaluations a : ℝ) ≤ κ a / 2 * B * (‖r (t.point 0)‖ * β ^ k) := by
    intro k hk
    have hs := h.solve k (hbefore k hk)
    have hr : ε₀ < ‖r (t.point k)‖ := by
      exact lt_of_not_ge (fun hh => hbefore k hk (Or.inl hh))
    have hR : 0 < ‖r (t.point k)‖ := h.primal.1.trans hr
    have hw : toleranceWeight q (fun j => β * ‖r (t.point k)‖ * ε j) π ≤
        B / ‖r (t.point k)‖ := by
      apply toleranceWeight_le (div_nonneg hB hR.le)
      intro j hj
      apply (le_div_iff₀ hR).2
      rw [mul_comm]
      exact (residual_inverse_power_le h.primal.1 hr.le h.factor.1.le
        (h.dual j hj).1.le (hs.exponent j hj).le).trans (hweight j hj)
    have hc := hs.cost a
    simp only [h.start, squaredResidual, sub_zero] at hc
    have hmul := mul_le_mul_of_nonneg_left hw
      (mul_nonneg hκ (div_nonneg (sq_nonneg ‖r (t.point k)‖) (by norm_num : (0 : ℝ) ≤ 2)))
    have heq : κ a * (‖r (t.point k)‖ ^ 2 / 2) * (B / ‖r (t.point k)‖) =
        κ a / 2 * B * ‖r (t.point k)‖ := by field_simp [hR.ne']
    rw [heq] at hmul
    exact (hc.trans hmul).trans (mul_le_mul_of_nonneg_left (hnorm k hk)
      (mul_nonneg (div_nonneg hκ (by norm_num)) hB))
  have hsum : (evaluations t a K : ℝ) ≤
      κ a / 2 * B * ‖r (t.point 0)‖ * (∑ k ∈ Finset.range K, β ^ k) := by
    simp only [evaluations, Nat.cast_sum]
    calc
      ∑ k ∈ Finset.range K, ((t.inner k).evaluations a : ℝ) ≤
          ∑ k ∈ Finset.range K, κ a / 2 * B * (‖r (t.point 0)‖ * β ^ k) :=
        Finset.sum_le_sum (fun k hk => hcall k (Finset.mem_range.mp hk))
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hcn : 0 ≤ κ a / 2 * B * ‖r (t.point 0)‖ := by positivity
  have hge := mul_le_mul_of_nonneg_left
    (sum_geometric_le h.factor.1.le h.factor.2 K) hcn
  have hcost : (evaluations t a K : ℝ) ≤
      κ a / 2 * ‖r (t.point 0)‖ * B / (1 - β) := by
    calc
      _ ≤ κ a / 2 * B * ‖r (t.point 0)‖ * (1 / (1 - β)) := hsum.trans hge
      _ = _ := by ring
  simp only [totalEvaluations, Nat.cast_add]
  push_cast
  linarith only [hcost]

/-- A closed tolerance-only bound for the complete wrapper evaluation count. Its
`1 - β` denominator comes from summing residual norms; it makes no interchange of a
sum and a maximum. The fixed cost parameters are shared by every INNER invocation. -/
theorem Execution.totalEvaluations_le_residualCostWeight
    (h : Execution X r q ε₀ β ε π κ step terminal t)
    {K : ℕ} (hbefore : ∀ k < K, ¬Stops X r q ε₀ ε t k) (a : EvaluationKind) :
    (totalEvaluations t a K : ℝ) ≤ (if a = .function then 1 else 0) +
      κ a / 2 * ‖r (t.point 0)‖ * residualCostWeight q β ε₀ ε π / (1 - β) :=
  h.totalEvaluations_le_uniform hbefore (residualCostWeight_nonneg q β ε₀ ε π)
    (fun _ hj => le_residualCostWeight β ε₀ ε π hj) a

end Optimization.ResidualLeastSquares
