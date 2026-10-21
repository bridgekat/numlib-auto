import Numlib.Optimization.ResidualLeastSquares
import NumlibSurface.CartisGouldToint.Chapter14.Section02

/-!
# Chapter 14, Section 3: least-norm wrapper foundations

The abstract INNER contract retains actual finite executions and both evaluation channels.
LENq-SC uses residual-scaled tolerances and the initial residual-only stopping test.
Convergence uses the natural ceiling of the logarithmic bound. The geometric evaluation
bound, curve conditions, and two-phase algorithm remain separate obligations.
-/

noncomputable section
open Set Metric Optimization
namespace CartisGouldToint.Chapter14.Section03
open ConstrainedTaylorCriticality
variable {n m : ℕ} {S : Type*}

/-- INNER (14.3.19–21), with its finite execution, fixed exponents and coefficients,
feasible output, positive radii at most one, and actual constrained Taylor gaps. The
reference value bounds the objective on the whole feasible set. Terminal events are counted. -/
abbrev InnerAlgorithmGuarantee (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (low : ℝ) (q : ℕ) (τ δ π : ℕ → ℝ)
    (κ : ResidualLeastSquares.EvaluationKind → ℝ)
    (step : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
      EuclideanSpace ℝ (Fin n) × S → List ResidualLeastSquares.EvaluationKind → Prop)
    (terminal : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
      List ResidualLeastSquares.EvaluationKind → Prop)
    (t : ResidualLeastSquares.InnerTrace (EuclideanSpace ℝ (Fin n)) S) : Prop :=
  ResidualLeastSquares.InnerContract X f low q τ δ π κ step terminal t

/-- The abstract INNER output delegates to the earlier simply constrained minimizer
interface, preserving all active orders and bounded positive radii. -/
theorem InnerAlgorithmGuarantee.toIsConstrainedApproxOrderMinimizer
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {low : ℝ} {q : ℕ} {τ δ π : ℕ → ℝ}
    {κ : ResidualLeastSquares.EvaluationKind → ℝ}
    {step : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
      EuclideanSpace ℝ (Fin n) × S → List ResidualLeastSquares.EvaluationKind → Prop}
    {terminal : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
      List ResidualLeastSquares.EvaluationKind → Prop}
    {t : ResidualLeastSquares.InnerTrace (EuclideanSpace ℝ (Fin n)) S}
    (h : InnerAlgorithmGuarantee f X low q τ δ π κ step terminal t) (hq : 1 ≤ q) :
    Section02.IsConstrainedApproxOrderMinimizer f X (t.point t.length) q τ δ :=
  ⟨h.feasible _ le_rfl, hq, fun j hj => (h.tolerance j hj).1,
    fun j hj => (h.tolerance j hj).2, fun j hj => (h.radius j hj).1,
    fun j hj => (h.radius j hj).2, h.gap⟩

/-- Residual-scaled criticality (14.3.18). Small residuals need no radii; otherwise every
active radius is at most one and the canonical actual squared-residual certificate holds. -/
def residualScaledCriticality (X : Set (EuclideanSpace ℝ (Fin n)))
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (q : ℕ)
    (ε₀ : ℝ) (ε δ : ℕ → ℝ) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖r x‖ ≤ ε₀ ∨ ((∀ j ∈ Finset.Icc 1 q, δ j ≤ 1) ∧
    ResidualScaledCertificate X r q ε₀ ε δ x)

/-- The source residual-scaled criterion supplies the canonical certificate. -/
theorem residualScaledCriticality.toCertificate
    {X : Set (EuclideanSpace ℝ (Fin n))}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {q : ℕ}
    {ε₀ : ℝ} {ε δ : ℕ → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : residualScaledCriticality X r q ε₀ ε δ x) :
    ResidualScaledCertificate X r q ε₀ ε δ x := by
  rcases h with hr | ⟨_, hc⟩
  · exact Or.inl hr
  · exact hc

/-- A small residual introduces the source criterion without any test-radius obligation. -/
theorem residualScaledCriticality.of_residual_le
    {X : Set (EuclideanSpace ℝ (Fin n))}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {q : ℕ}
    {ε₀ : ℝ} {ε δ : ℕ → ℝ} {x : EuclideanSpace ℝ (Fin n)} (h : ‖r x‖ ≤ ε₀) :
    residualScaledCriticality X r q ε₀ ε δ x := Or.inl h

/-- Bounded positive radii and the actual relative Taylor-gap inequalities introduce the
source criterion in its gap branch. -/
theorem residualScaledCriticality.of_gaps
    {X : Set (EuclideanSpace ℝ (Fin n))}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {q : ℕ}
    {ε₀ : ℝ} {ε δ : ℕ → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hδ : ∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧ δ j ≤ 1)
    (hg : ∀ j ∈ Finset.Icc 1 q,
      Section02.constrainedTaylorGap (squaredResidual r) X j x (δ j) ≤
        ε j * ‖r x‖ * δ j ^ j / (j.factorial : ℝ)) :
    residualScaledCriticality X r q ε₀ ε δ x :=
  Or.inr ⟨fun j hj => (hδ j hj).2,
    ResidualScaledCertificate.of_gaps (fun j hj => (hδ j hj).1) hg⟩

/-- Above the primal tolerance, the criterion yields each bounded positive radius and its
source constrained Taylor-gap inequality. -/
theorem residualScaledCriticality.gap
    {X : Set (EuclideanSpace ℝ (Fin n))}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {q : ℕ}
    {ε₀ : ℝ} {ε δ : ℕ → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : residualScaledCriticality X r q ε₀ ε δ x) (hr : ε₀ < ‖r x‖)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 q) :
    0 < δ j ∧ δ j ≤ 1 ∧
      Section02.constrainedTaylorGap (squaredResidual r) X j x (δ j) ≤
        ε j * ‖r x‖ * δ j ^ j / (j.factorial : ℝ) := by
  have hh := h.toCertificate.gap hr hj
  exact ⟨hh.1, (h.resolve_left (not_le.mpr hr)).1 j hj, hh.2⟩

/-- Tangent and critical feasible displacement sets (14.3.45). Nonconvex simple constraints
need not give linear subspaces. The critical set additionally annihilates the objective jet. -/
def lagrangianCriticalSubspaces (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) ×
      Set (EuclideanSpace ℝ (Fin n)) :=
  ({d ∈ Section02.feasibleDisplacements X x | fderiv ℝ c x d = 0},
   {d ∈ Section02.feasibleDisplacements X x | fderiv ℝ c x d = 0 ∧ fderiv ℝ f x d = 0})

/-- Tangent-set membership keeps actual feasibility and the constraint derivative kernel. -/
@[simp] theorem mem_lagrangianCriticalSubspaces_fst
    (X : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x d : EuclideanSpace ℝ (Fin n)) :
    d ∈ (lagrangianCriticalSubspaces X f c x).1 ↔ x + d ∈ X ∧ fderiv ℝ c x d = 0 := Iff.rfl

/-- Critical-set membership imposes both derivative kernels on feasible displacements. -/
@[simp] theorem mem_lagrangianCriticalSubspaces_snd
    (X : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x d : EuclideanSpace ℝ (Fin n)) :
    d ∈ (lagrangianCriticalSubspaces X f c x).2 ↔
      x + d ∈ X ∧ fderiv ℝ c x d = 0 ∧ fderiv ℝ f x d = 0 := Iff.rfl

/-- A Lagrangian Taylor gap over a specified displacement set, with an explicit test
radius and a multiplier held fixed. This applies to either critical set in (14.3.45). -/
def lagrangianTaylorGap (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin m)) (V : Set (EuclideanSpace ℝ (Fin n)))
    (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) : ℝ :=
  TaylorCriticality.gapOn
    (TaylorCriticality.taylorDecrement (residualLagrangian f c y) j x)
    (V ∩ closedBall 0 δ)

/-- The unconditional initialization restriction printed in Algorithm 14.3.1 and
Phase 1 of Algorithm 14.3.2. It is imposed before testing the initial residual. -/
def LiteralLENInput
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin n)) (β : ℝ) : Prop :=
  β ∈ Ioo 0 (min 1 (‖r x₀‖)⁻¹)

/-- The printed initialization factor is positive. -/
theorem LiteralLENInput.factor_pos
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)} {β : ℝ} (h : LiteralLENInput r x₀ β) :
    0 < β := h.1

/-- The printed initialization factor is strictly below one. -/
theorem LiteralLENInput.factor_lt_one
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)} {β : ℝ} (h : LiteralLENInput r x₀ β) :
    β < 1 := lt_of_lt_of_le h.2 (min_le_left _ _)

/-- The reciprocal restriction holds even if the initial residual already passes its test. -/
theorem LiteralLENInput.reciprocal
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)} {β : ℝ} (h : LiteralLENInput r x₀ β) :
    β < (‖r x₀‖)⁻¹ := lt_of_lt_of_le h.2 (min_le_right _ _)

/-- Literal printed inputs have positive initial residual, including with Lean's total inverse. -/
theorem LiteralLENInput.initial_norm_pos
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)} {β : ℝ} (h : LiteralLENInput r x₀ β) :
    0 < ‖r x₀‖ := by
  by_contra hn
  have hz : ‖r x₀‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
  have hr := h.reciprocal
  rw [hz, inv_zero] at hr
  exact (not_lt_of_ge h.factor_pos.le hr).elim

/-- The printed domain is exactly the positive-residual domain with both strict factor bounds. -/
theorem literalLENInput_iff
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin n)) (β : ℝ) :
    LiteralLENInput r x₀ β ↔
      0 < ‖r x₀‖ ∧ 0 < β ∧ β < 1 ∧ β < (‖r x₀‖)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.initial_norm_pos, h.factor_pos, h.factor_lt_one, h.reciprocal⟩
  · rintro ⟨_, hp, h1, hr⟩
    exact ⟨hp, lt_min h1 hr⟩

/-- The operational LENq-SC extension with closed upper dual endpoint and a conditional
initial reciprocal restriction. It admits zero initial residual and positive already-small
residuals without the unconditional printed initialization restriction. Literal source
executions additionally satisfy `LiteralLENInput`; TWO-PHASE records that input separately. -/
abbrev algorithm_14_3_1_closedDual (X : Set (EuclideanSpace ℝ (Fin n)))
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (q : ℕ) (ε₀ β : ℝ) (ε π : ℕ → ℝ)
    (κ : ResidualLeastSquares.EvaluationKind → ℝ)
    (step : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
      EuclideanSpace ℝ (Fin n) × S → List ResidualLeastSquares.EvaluationKind → Prop)
    (terminal : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
      List ResidualLeastSquares.EvaluationKind → Prop)
    (t : ResidualLeastSquares.Trace (EuclideanSpace ℝ (Fin n)) S) : Prop :=
  ResidualLeastSquares.Execution X r q ε₀ β ε π κ step terminal t


/-- LENq-SC (Algorithm 14.3.1), with complete INNER traces, exact residual-scaled input
accuracies, output radii, state handoffs, and both event-count contracts. Its unconditional
printed beta domain precedes the residual-only initial test and excludes zero initial residual. -/
def algorithm_14_3_1 (X : Set (EuclideanSpace ℝ (Fin n)))
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (q : ℕ) (ε₀ β : ℝ) (ε π : ℕ → ℝ)
    (κ : ResidualLeastSquares.EvaluationKind → ℝ)
    (step : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
      EuclideanSpace ℝ (Fin n) × S → List ResidualLeastSquares.EvaluationKind → Prop)
    (terminal : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
      List ResidualLeastSquares.EvaluationKind → Prop)
    (t : ResidualLeastSquares.Trace (EuclideanSpace ℝ (Fin n)) S) : Prop :=
  algorithm_14_3_1_closedDual X r q ε₀ β ε π κ step terminal t ∧
    (∀ j ∈ Finset.Icc 1 q, ε j < 1) ∧ LiteralLENInput r (t.point 0) β

variable {X : Set (EuclideanSpace ℝ (Fin n))}
  {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
  {q : ℕ} {ε₀ β : ℝ} {ε π : ℕ → ℝ}
  {κ : ResidualLeastSquares.EvaluationKind → ℝ}
  {step : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
    EuclideanSpace ℝ (Fin n) × S → List ResidualLeastSquares.EvaluationKind → Prop}
  {terminal : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) × S →
    List ResidualLeastSquares.EvaluationKind → Prop}
  {t : ResidualLeastSquares.Trace (EuclideanSpace ℝ (Fin n)) S}

/-- A literal LEN execution is also an execution of the explicit endpoint extension. -/
theorem algorithm_14_3_1.toClosedDual
    (h : algorithm_14_3_1 X r q ε₀ β ε π κ step terminal t) :
    algorithm_14_3_1_closedDual X r q ε₀ β ε π κ step terminal t := h.1

/-- The broader operational extension becomes literal LEN on its printed dual and input domains. -/
theorem algorithm_14_3_1.ofClosedDual
    (h : algorithm_14_3_1_closedDual X r q ε₀ β ε π κ step terminal t)
    (hstrict : ∀ j ∈ Finset.Icc 1 q, ε j < 1)
    (hinput : LiteralLENInput r (t.point 0) β) :
    algorithm_14_3_1 X r q ε₀ β ε π κ step terminal t := ⟨h, hstrict, hinput⟩

/-- A literal LEN execution exposes its unconditional printed initialization domain. -/
theorem algorithm_14_3_1.input
    (h : algorithm_14_3_1 X r q ε₀ β ε π κ step terminal t) :
    LiteralLENInput r (t.point 0) β := h.2.2

/-- Theorem 14.3.3: literal LENq-SC stops within the logarithmic ceiling, returns a feasible
residual-scaled critical point, and strictly contracts every positive nonterminal residual.
The initial-small-residual branch has zero INNER invocations. -/
theorem theorem_14_3_3 (h : algorithm_14_3_1 X r q ε₀ β ε π κ step terminal t) :
    ∃ K ≤ MeasureDomination.geometricIterationCount ‖r (t.point 0)‖ β⁻¹ ε₀,
      ResidualLeastSquares.Stops X r q ε₀ ε t K ∧
      (∀ k < K, ¬ResidualLeastSquares.Stops X r q ε₀ ε t k) ∧
      t.point K ∈ X ∧ residualScaledCriticality X r q ε₀ ε (t.radius K) (t.point K) ∧
      (∀ k < K, 0 < k → ‖r (t.point k)‖ < ‖r (t.point 0)‖ * β ^ k) := by
  rcases h with ⟨h, _hstrict⟩
  obtain ⟨K, hK, hs, hb⟩ := h.terminates
  refine ⟨K, hK, hs, hb, ?_, ?_, h.geometric hb⟩
  · cases K with
    | zero => exact h.initial_feasible
    | succ k =>
      have hi := (h.solve k (hb k (by omega))).feasible _ le_rfl
      simpa only [h.finish] using hi
  · by_cases hr : ‖r (t.point K)‖ ≤ ε₀
    · exact Or.inl hr
    · have hpos : 0 < K := by
        rcases hs with hs | ⟨hk, _⟩
        · exact (hr hs).elim
        · exact hk
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      exact Or.inr ⟨fun j hj => ((h.solve k (hb k (by omega))).radius j hj).2,
        (h.stops_iff_certificate (k + 1)).1 hs⟩

/-- A tolerance-only LENq-SC evaluation bound with denominator `1 - β`, obtained by
summing residual norms. It counts the initial residual query and all terminal INNER events.
The exact printed prefactors of Theorem 14.3.4 remain a separate obligation. -/
theorem len_evaluation_bound (h : algorithm_14_3_1 X r q ε₀ β ε π κ step terminal t) :
    ∃ K ≤ MeasureDomination.geometricIterationCount ‖r (t.point 0)‖ β⁻¹ ε₀,
      ResidualLeastSquares.Stops X r q ε₀ ε t K ∧
      (∀ k < K, ¬ResidualLeastSquares.Stops X r q ε₀ ε t k) ∧
      residualScaledCriticality X r q ε₀ ε (t.radius K) (t.point K) ∧
      ∀ a, (ResidualLeastSquares.totalEvaluations t a K : ℝ) ≤
        (if a = .function then 1 else 0) + κ a / 2 * ‖r (t.point 0)‖ *
          ResidualLeastSquares.residualCostWeight q β ε₀ ε π / (1 - β) := by
  obtain ⟨K, hK, hs, hb, _, hc, _⟩ := theorem_14_3_3 h
  exact ⟨K, hK, hs, hb, hc, fun a => h.1.totalEvaluations_le_residualCostWeight hb a⟩

end CartisGouldToint.Chapter14.Section03
