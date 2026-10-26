import Numlib.Optimization.Regularization.Constrained.Selection
import Numlib.Optimization.Regularization.Constrained.Complexity

/-!
# Constructed constrained regularization executions

Every state has a feasible point and legal positive parameter and radii.
Attained Taylor checks and genuine finite feasible model solves construct
trials. Actual objective ratios and permitted updates define the recursion.
-/

namespace ConstrainedRegularization
open Set InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {p q : ℕ}

/-- A feasible current point and legal regularization inputs. -/
structure State (X : Set E) (P : Settings p q) where
  point : E
  parameter : ℝ
  radius : Fin q → ℝ
  point_mem : point ∈ X
  parameter_min : P.sigmaMin ≤ parameter
  radius_mem : ∀ a, 0 < radius a ∧ radius a ≤ 1

/-- A genuine computed ordered check and finite feasible model solve. -/
structure Trial (f : E → ℝ) (X : Set E) (P : Settings p q)
    (ε : Fin q → ℝ) (z : State X P) where
  direction : Fin q → E
  selected : Option (Fin q)
  step : E
  solvedRadius : Fin q → ℝ
  check : HighOrderRegularization.ConstrainedOptimalityCheck f X P.zeta ε
    z.radius z.point direction selected
  computation : ModelSolve.ConstrainedStepComputation
    (HighOrderRegularization.model f p z.point z.parameter)
    (TaylorModel.feasibleDisplacements X z.point) modelOrder P.theta P.zeta ε step solvedRadius

/-- Every feasible state admits actual attained checks and finite feasible
model computations. Availability is proved rather than assumed by an execution. -/
theorem exists_trial (f : E → ℝ) {X : Set E} (hX : IsClosed X) (hconv : Convex ℝ X)
    (P : Settings p q) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a) (z : State X P) :
    Nonempty (Trial f X P ε z) := by
  obtain ⟨d, selected, hcheck⟩ := exists_optimalityCheck f hX z.point_mem P.zeta_le_one
    ε z.radius (fun a => (z.radius_mem a).1.le)
  have hA := HighOrderRegularization.tensor_bound_of_derivative_lipschitz f
    (zero_le_one.trans hL) (fun i hi hip => hlip i hi hip.le) z.point
  obtain ⟨s, δ, hs⟩ := ModelSolve.exists_penalized_constrained_stepComputation
    (ftaylorSeries ℝ f z.point) p (hX.preimage (continuous_const.add continuous_id))
    (hconv.translate_preimage_right z.point) (by simpa using z.point_mem)
    (P.sigmaMin_pos.trans_le z.parameter_min) hL hA modelOrder
    (fun a => ⟨by unfold modelOrder; omega, by have := P.order_le; unfold modelOrder; omega⟩)
    P.theta_pos P.zeta_pos P.zeta_le_one ε hε
  exact ⟨⟨d, selected, s, δ, hcheck, hs⟩⟩

/-- A fixed permitted choice in each actual ratio-update branch. -/
noncomputable def parameterUpdate (P : Settings p q) (σ ρ : ℝ) : ℝ :=
  if P.eta2 ≤ ρ then max P.sigmaMin (P.gamma1 * σ)
  else if P.eta1 ≤ ρ then σ else P.gamma2 * σ

/-- The chosen actual penalty update retains the minimum and belongs to the
source interval in every ratio branch. -/
theorem parameterUpdate_mem (P : Settings p q) {σ : ℝ} (hσ : P.sigmaMin ≤ σ) (ρ : ℝ) :
    P.sigmaMin ≤ parameterUpdate P σ ρ ∧
      (if P.eta2 ≤ ρ then parameterUpdate P σ ρ ∈ Icc (max P.sigmaMin (P.gamma1 * σ)) σ
      else if P.eta1 ≤ ρ then parameterUpdate P σ ρ ∈ Icc σ (P.gamma2 * σ)
      else parameterUpdate P σ ρ ∈ Icc (P.gamma2 * σ) (P.gamma3 * σ)) := by
  have hp : 0 ≤ σ := P.sigmaMin_pos.le.trans hσ
  have hγ₁ : P.gamma1 * σ ≤ σ := mul_le_of_le_one_left hp P.gamma1_lt_one.le
  have hγ₂ : σ ≤ P.gamma2 * σ := le_mul_of_one_le_left hp P.one_lt_gamma2.le
  have hγ₃ : P.gamma2 * σ ≤ P.gamma3 * σ :=
    mul_le_mul_of_nonneg_right P.gamma2_lt_gamma3.le hp
  unfold parameterUpdate
  split_ifs <;> simp only [Set.mem_Icc] <;> constructor
  · exact le_max_left _ _
  · exact ⟨le_rfl, max_le hσ hγ₁⟩
  · exact hσ
  · exact ⟨le_rfl, hγ₂⟩
  · exact hσ.trans hγ₂
  · exact ⟨le_rfl, hγ₃⟩

/-- The next feasible state uses the actual objective ratio, point acceptance,
radius inheritance and permitted parameter update. -/
noncomputable def advance {f : E → ℝ} {X : Set E} {P : Settings p q} {ε : Fin q → ℝ}
    (z : State X P) (t : Trial f X P ε z) : State X P := by
  classical
  let ρ := HighOrderRegularization.ratio f p z.point t.step
  exact {
    point := if P.eta1 ≤ ρ then z.point + t.step else z.point
    parameter := parameterUpdate P z.parameter ρ
    radius := if P.eta1 ≤ ρ then t.solvedRadius else z.radius
    point_mem := by
      split_ifs
      · exact t.computation.feasible
      · exact z.point_mem
    parameter_min := (parameterUpdate_mem P z.parameter_min ρ).1
    radius_mem := by
      intro a
      split_ifs
      · exact t.computation.radius_mem a
      · exact z.radius_mem a }

/-- Genuine feasible checks, model solves and actual updates construct total
execution arrays. Every prefix before the first observable target satisfies
all primitive execution rules, without a prefix-availability assumption.
The total continuation after a target is irrelevant to the returned finite run. -/
theorem exists_execution (f : E → ℝ) {X : Set E} (hX : IsClosed X) (hconv : Convex ℝ X)
    (P : Settings p q) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (ε : Fin q → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1)
    (x₀ : E) (hx₀ : x₀ ∈ X) :
    ∃ D : ExecutionData E q, D.point 0 = x₀ ∧ D.parameter 0 = P.sigmaInitial ∧
      (∀ a, D.radius 0 a = 1) ∧
      ∀ N, (∀ k < N, ¬TargetAt f X P ε D k) → Run f X P ε D N := by
  classical
  let trial : (z : State X P) → Trial f X P ε z :=
    fun z => Classical.choice (exists_trial f hX hconv P hL hlip ε (fun a => (hε a).1) z)
  let z₀ : State X P := ⟨x₀, P.sigmaInitial, fun _ => 1, hx₀,
    P.sigmaMin_le_initial, fun _ => ⟨zero_lt_one, le_rfl⟩⟩
  let z : ℕ → State X P := fun n => Nat.rec z₀ (fun _ w => advance w (trial w)) n
  let D : ExecutionData E q := {
    point := fun k => (z k).point
    parameter := fun k => (z k).parameter
    radius := fun k => (z k).radius
    step := fun k => (trial (z k)).step
    solvedRadius := fun k => (trial (z k)).solvedRadius
    direction := fun k => (trial (z k)).direction
    selected := fun k => (trial (z k)).selected
    ratio := fun k => HighOrderRegularization.ratio f p (z k).point (trial (z k)).step }
  have hpoint : ∀ k, D.point (k + 1) =
      if P.eta1 ≤ D.ratio k then D.point k + D.step k else D.point k := fun _ => rfl
  have hparam : ∀ k, D.parameter (k + 1) = parameterUpdate P (D.parameter k) (D.ratio k) :=
    fun _ => rfl
  have hradius : ∀ k, D.radius (k + 1) =
      if P.eta1 ≤ D.ratio k then D.solvedRadius k else D.radius k := fun _ => rfl
  have hcheck : ∀ k, HighOrderRegularization.ConstrainedOptimalityCheck f X P.zeta ε
      (D.radius k) (D.point k) (D.direction k) (D.selected k) :=
    fun k => (trial (z k)).check
  have hsolve : ∀ k, ModelSolve.ConstrainedStepComputation
      (HighOrderRegularization.model f p (D.point k) (D.parameter k))
      (TaylorModel.feasibleDisplacements X (D.point k)) modelOrder P.theta P.zeta ε
        (D.step k) (D.solvedRadius k) := fun k => (trial (z k)).computation
  have hnone : ∀ k, D.selected k = none → TargetAt f X P ε D k := by
    intro k hk
    exact Or.inl (optimality_of_check_none (hcheck k) P.zeta_pos (z k).point_mem
      (z k).radius_mem hk)
  refine ⟨D, rfl, rfl, fun _ => rfl, ?_⟩
  intro N hnot
  have hcont : ∀ k < N, D.selected k ≠ none := by
    intro k hk he
    exact hnot k hk (hnone k he)
  refine {
    accuracy_pos := fun a => (hε a).1
    accuracy_le_one := fun a => (hε a).2
    initial_parameter := rfl
    initial_radii := fun _ => ⟨zero_lt_one, le_rfl⟩
    initial_feasible := hx₀
    check := fun k _ => hcheck k
    step_two := fun k _ _ => hsolve k
    continues := hcont
    radius_update := fun k _ => hradius k
    modelTrace := {
      order_pos := P.order_pos.trans_le P.order_le
      ratio := fun _ _ => rfl
      point_update := fun k _ => hpoint k
      updates := {
        min_pos := P.sigmaMin_pos
        min_le_initial := P.sigmaMin_le_initial
        eta1_pos := P.eta1_pos
        eta1_le_eta2 := P.eta1_le_eta2
        eta2_lt_one := P.eta2_lt_one
        gamma1_pos := P.gamma1_pos
        gamma1_lt_one := P.gamma1_lt_one
        one_lt_gamma2 := P.one_lt_gamma2
        gamma2_lt_gamma3 := P.gamma2_lt_gamma3
        update := ?_ }
      improvement := ?_ } }
  · intro k _
    rw [hparam k]
    exact (parameterUpdate_mem P (z k).parameter_min (D.ratio k)).2
  · intro k hk
    have hzero : (0 : E) ∈ TaylorModel.feasibleDisplacements X (D.point k) := by
      simpa using (z k).point_mem
    have hle := (hsolve k).nonincrease hzero
    apply lt_of_le_of_ne hle
    intro he
    exact hnot k hk (Or.inr ⟨hcont k hk, he.symm⟩)

/-- With derivatives cached on rejection, each enabled derivative order is
evaluated initially and after every accepted point update. -/
noncomputable def derivativeEvaluationsForOrder (P : Settings p q)
    (D : ExecutionData E q) (N j : ℕ) : ℕ :=
  if 1 ≤ j ∧ j ≤ p then
    (EvaluationComplexity.successfulIterations {i | P.eta1 ≤ D.ratio i} N).card + 1 else 0

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Every enabled actual derivative schedule has its initialized exact count. -/
theorem derivativeEvaluationsForOrder_eq (P : Settings p q) (D : ExecutionData E q)
    (N : ℕ) {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p) :
    derivativeEvaluationsForOrder P D N j =
      (EvaluationComplexity.successfulIterations {i | P.eta1 ≤ D.ratio i} N).card + 1 := by
  simp only [derivativeEvaluationsForOrder, hj, hjp, and_self, ite_true]

/-- Constructed actual executions attain all requested constrained Taylor
certificates with constants fixed before every accuracy vector. The full
initialized function and derivative budgets are proved for these executions;
no execution, termination or model-step existence hypothesis is required. -/
theorem exists_certified_execution (f : E → ℝ) (X : Set E)
    (hX : IsClosed X) (hconv : Convex ℝ X) (P : Settings p q)
    (x₀ : E) (hx₀ : x₀ ∈ X) (hf : ContDiff ℝ p f) {L flow : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ x ∈ X, flow ≤ f x) :
    ∃ κs > 0, ∃ κa > 0, ∃ κc > 0,
      ∀ (ε : Fin q → ℝ), (∀ a, 0 < ε a ∧ ε a ≤ 1) →
      ∃ (D : ExecutionData E q) (K : ℕ) (δ : Fin q → ℝ),
        D.point 0 = x₀ ∧ D.parameter 0 = P.sigmaInitial ∧ (∀ a, D.radius 0 a = 1) ∧
        Run f X P ε D K ∧ TargetAt f X P ε D K ∧
        (∀ k < K, ¬TargetAt f X P ε D k) ∧ OptimalityAt f X ε (D.point K) δ ∧
        (∀ a, modelOrder a = 1 → TaylorModel.constrainedCriticality f 1 X (D.point K) 1 ≤
          ε a) ∧
        ((K + 1 : ℕ) : ℝ) ≤ κa * (f x₀ - flow) / accuracyFactor P ε + κc ∧
        (((EvaluationComplexity.successfulIterations {i | P.eta1 ≤ D.ratio i} K).card + 1 :
          ℕ) : ℝ) ≤ κs * (f x₀ - flow) / accuracyFactor P ε + 2 := by
  obtain ⟨κs, hs, κa, ha, κc, hc, hall⟩ :=
    evaluation_complexity_with_unit_first f X hX hconv P x₀ hx₀ hf hL hlip hlow
  refine ⟨κs, hs, κa, ha, κc, hc, ?_⟩
  intro ε hε
  obtain ⟨D, hx, hσ, hδ, hrun⟩ := exists_execution f hX hconv P hL hlip ε hε x₀ hx₀
  obtain ⟨K, δ, hr, ht, hfirst, hopt, hunit, hF, hD⟩ := hall ε D hx hrun
  exact ⟨D, K, δ, hx, hσ, hδ, hr, ht, hfirst, hopt, hunit, hF, hD⟩

end ConstrainedRegularization
