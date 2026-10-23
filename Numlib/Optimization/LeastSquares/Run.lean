import Numlib.Optimization.LeastSquares.Stopping
import Numlib.Optimization.LeastSquares.Cascading
import Numlib.Optimization.Regularization.HighOrder.Run

/-!
# Actual ARpLE operational traces in every enabled order

All disabled/finite stopping branches use actual normalized residual-power
derivatives. Literal and repaired executions differ only in the nonempty-set
guard. The source initialization uses the actual objective Hessian; model
directions are assigned before acceptance even for rejected trials.
-/

namespace LeastSquares
open HighOrderRegularization
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F]

/-- All ARpLE stopping branches, with explicit disabled higher-order tolerances.
The Boolean chooses whether the literal nonempty-direction guard is retained. -/
def stop (literal : Bool) (r : E → F) (ℓ : ℝ) (x : E) (μ : ℝ) (M : Set E)
    (ε₀ ε₁ : ℝ) (ε₂ ε₃ : WithTop ℝ) : Prop :=
  ‖r x‖ ≤ ε₀ ∨ (firstMeasure r ℓ x ≤ ε₁ ∧
    ((ε₂ = ⊤ ∧ ε₃ = ⊤) ∨ ∃ e₂ : ℝ, ε₂ = (e₂ : WithTop ℝ) ∧
      (e₂ < secondMeasure r ℓ x μ ∨ (-e₂ ≤ secondMeasure r ℓ x μ ∧
        (ε₃ = ⊤ ∨ ∃ e₃ : ℝ, ε₃ = (e₃ : WithTop ℝ) ∧
          (literal = true → M.Nonempty) ∧ ∀ v ∈ M,
            thirdMeasure r ℓ x v ≤ e₃ ∧ directionalSecondMeasure r ℓ x v ≤ e₂)))))

/-- Finite real tolerances recover exactly the literal source stopping predicate. -/
theorem stop_true_coe_iff (r : E → F) (ℓ : ℝ) (x : E) (μ : ℝ) (M : Set E)
    (ε₀ ε₁ ε₂ ε₃ : ℝ) :
    stop true r ℓ x μ M ε₀ ε₁ ε₂ ε₃ ↔ literalFiniteStop r ℓ x μ M
      ε₀ ε₁ ε₂ ε₃ := by
  simp [stop, literalFiniteStop]

/-- Finite real tolerances recover exactly the repaired stopping predicate. -/
theorem stop_false_coe_iff (r : E → F) (ℓ : ℝ) (x : E) (μ : ℝ) (M : Set E)
    (ε₀ ε₁ ε₂ ε₃ : ℝ) :
    stop false r ℓ x μ M ε₀ ε₁ ε₂ ε₃ ↔ finiteStop r ℓ x μ M ε₀
      ε₁ ε₂ ε₃ := by
  simp [stop, finiteStop]

/-- With both higher tests disabled, only the actual global residual and first measure remain. -/
theorem stop_top_top_iff (literal : Bool) (r : E → F) (ℓ : ℝ) (x : E) (μ : ℝ)
    (M : Set E) (ε₀ ε₁ : ℝ) :
    stop literal r ℓ x μ M ε₀ ε₁ ⊤ ⊤ ↔
      ‖r x‖ ≤ ε₀ ∨ firstMeasure r ℓ x ≤ ε₁ := by
  simp [stop]

variable [CompleteSpace E]

/-- The complete operational ARpLE algorithm. Only literal stopping differs between the
source and repaired versions; actual models, ratios, accepted points and all parameter
updates are inherited from the real residual-power objective trace. Model directions are
assigned before acceptance, including at rejected trials. -/
structure Run (literal : Bool) (r : E → F) (ℓ : ℝ) (p : ℕ)
    (x s u : ℕ → E) (μ σ ρ : ℕ → ℝ) (M : ℕ → Set E)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ : ℝ)
    (ε₂ ε₃ : WithTop ℝ) (N : ℕ) : Prop where
  trace : RegularizationTrace r ℓ p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  residual_order : 2 ≤ ℓ
  second_order : ε₂ ≠ ⊤ → 2 ≤ p
  third_order : ε₃ ≠ ⊤ → 3 ≤ p
  higher_compatible : ε₃ ≠ ⊤ → ε₂ ≠ ⊤
  theta_first_pos : 0 < θ₁
  theta_first_le_one : θ₁ ≤ 1
  theta_second_pos : 0 < θ₂
  theta_second_le_one : θ₂ ≤ 1
  theta_third_pos : 0 < θ₃
  theta_third_le_one : θ₃ ≤ 1
  accuracy_global_pos : 0 < ε₀
  accuracy_first_pos : 0 < ε₁
  accuracy_second_pos : ∀ e : ℝ, ε₂ = (e : WithTop ℝ) → 0 < e
  accuracy_third_pos : ∀ e : ℝ, ε₃ = (e : WithTop ℝ) → 0 < e
  least_eigenpair : ∀ i ≤ N, ε₂ ≠ ⊤ →
    SecondOrderTrustRegion.IsLeastEigenpair (powerObjective r ℓ) (x i) (μ i) (u i)
  initial_directions : ∀ e : ℝ, ε₃ ≠ ⊤ → ε₂ = (e : WithTop ℝ) →
    M 0 = HighOrderRegularization.initialDirections (powerObjective r ℓ) (x 0) e
  model_directions : ∀ i < N, ε₃ ≠ ⊤ →
    M (i + 1) = smallModelDirections (powerObjective r ℓ) p (x i) (s i) (σ i) θ₂
  not_terminated : ∀ i < N, ¬stop literal r ℓ (x i) (μ i) (M i) ε₀ ε₁ ε₂ ε₃
  stationary_first : ∀ i < N,
    ‖fderiv ℝ (model (powerObjective r ℓ) p (x i) (σ i)) (s i)‖ ≤ θ₁ * ‖s i‖ ^ p
  stationary_second : ∀ i < N, ε₂ ≠ ⊤ → ∀ v : E, ‖v‖ = 1 →
    -θ₂ * ‖s i‖ ^ (p - 1) ≤
      iteratedFDeriv ℝ 2 (model (powerObjective r ℓ) p (x i) (σ i)) (s i) (fun _ => v)
  stationary_third : ∀ i < N, ε₃ ≠ ⊤ →
    ∀ v ∈ smallModelDirections (powerObjective r ℓ) p (x i) (s i) (σ i) θ₂,
      |iteratedFDeriv ℝ 3 (model (powerObjective r ℓ) p (x i) (σ i)) (s i) (fun _ => v)| ≤
        θ₃ * ‖s i‖ ^ (p - 2)

/-- The finite-third-order branch, retaining every actual operational rule of Run. -/
abbrev FiniteRun (literal : Bool) (r : E → F) (ℓ : ℝ) (p : ℕ)
    (x s u : ℕ → E) (μ σ ρ : ℕ → ℝ) (M : ℕ → Set E)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ : ℝ)
      (N : ℕ) : Prop :=
  Run literal r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂
    θ₃ ε₀ ε₁ ε₂ ε₃ N
end LeastSquares

namespace LeastSquares
open HighOrderRegularization
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]
namespace Run
variable {literal : Bool} {r : E → F} {ℓ : ℝ} {p : ℕ}
  {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ} {M : ℕ → Set E}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ : ℝ} {ε₂ ε₃ :
    WithTop ℝ} {N n : ℕ}

/-- Restrict an actual ARpLE execution to an earlier prefix without altering any data. -/
theorem restrict
    (h : Run literal r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁
      θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    (hn : n ≤ N) :
    Run literal r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂
      θ₃ ε₀ ε₁ ε₂ ε₃ n := by
  exact {h with
    trace := h.trace.restrict hn
    least_eigenpair := fun i hi => h.least_eigenpair i (hi.trans hn)
    model_directions := fun i hi => h.model_directions i (hi.trans_le hn)
    not_terminated := fun i hi => h.not_terminated i (hi.trans_le hn)
    stationary_first := fun i hi => h.stationary_first i (hi.trans_le hn)
    stationary_second := fun i hi => h.stationary_second i (hi.trans_le hn)
    stationary_third := fun i hi => h.stationary_third i (hi.trans_le hn)}

/-- Every nonterminal iterate fails the actual global residual threshold. -/
theorem residual_gt_accuracy
    (h : Run literal r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁
      θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    {i : ℕ} (hi : i < N) : ε₀ < ‖r (x i)‖ := by
  by_contra hh
  exact h.not_terminated i hi (Or.inl (not_lt.mp hh))

/-- A nonterminal residual has a genuine positive derivative normalization. -/
theorem derivativeWeight_pos
    (h : Run literal r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁
      θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    {i : ℕ} (hi : i < N) : 0 < derivativeWeight r ℓ (x i) := by
  apply LeastSquares.derivativeWeight_pos
  exact norm_pos_iff.mp (h.accuracy_global_pos.trans (h.residual_gt_accuracy hi))

/-- Actual accepted-point updates make the residual norm nonincreasing at every trial. -/
theorem residual_step_le
    (h : Run literal r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁
      θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    {i : ℕ} (hi : i < N) : ‖r (x (i + 1))‖ ≤ ‖r (x i)‖ := by
  by_cases hs : η₁ ≤ ρ i
  · exact (RegularizationTrace.residual_lt h.trace (by linarith [h.residual_order]) hi hs).le
  · rw [h.trace.point_update i hi, ite_eq_right hs]

/-- Every residual norm is bounded above by the actual initial residual norm. -/
theorem residual_le_initial
    (h : Run literal r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁
      θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    {i : ℕ} (hi : i ≤ N) : ‖r (x i)‖ ≤ ‖r (x 0)‖ := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact (h.residual_step_le (by omega)).trans (ih (by omega))
end Run

namespace FiniteRun
variable {literal : Bool} {r : E → F} {ℓ : ℝ} {p : ℕ}
  {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ} {M : ℕ → Set E}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ : ℝ} {N : ℕ}

/-- Every inherited finite-order model direction is an actual unit vector. -/
theorem directions_unit
    (h : FiniteRun literal r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N)
    {i : ℕ} (hi : i ≤ N) {v : E} (hv : v ∈ M i) : ‖v‖ = 1 := by
  cases i with
  | zero =>
    rw [h.initial_directions ε₂ (by simp) rfl] at hv
    exact hv.1
  | succ i =>
    rw [h.model_directions i (by omega) (by simp)] at hv
    exact hv.1

/-- Finite real tolerances enable all three genuine model derivative conditions. -/
theorem stepConditions
    (h : FiniteRun literal r ℓ p x s u μ σ ρ M η₁ η₂ γ₁ γ₂ γ₃ σmin
      θ₁ θ₂ θ₃ ε₀ ε₁ ε₂ ε₃ N) {i : ℕ} (hi : i < N) :
    StepConditions (powerObjective r ℓ) p (x i) (s i) (σ i) θ₁ θ₂ θ₃ := by
  exact ⟨h.stationary_first i hi, h.stationary_second i hi (by simp),
    h.stationary_third i hi (by simp)⟩
end FiniteRun
end LeastSquares
