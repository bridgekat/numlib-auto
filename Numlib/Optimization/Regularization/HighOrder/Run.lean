import Numlib.Optimization.Regularization.HighOrder.Step

/-!
# Operational high-order regularization traces

First- and second-order branches have explicitly disabled higher-order tests.
The finite third-order branch removes only the source stopping test's nonempty
direction guard, whose obstruction is exhibited in `HighOrder.EmptyDirections`.
Model directions are assigned before acceptance, including on rejected trials.
-/

namespace HighOrderRegularization
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Finite-third-order stopping after removing only the source's nonempty-direction guard. -/
def finiteStop (f : E → ℝ) (x : E) (μ : ℝ) (M : Set E) (ε₁ ε₂ ε₃ : ℝ) : Prop :=
  ‖fderiv ℝ f x‖ ≤ ε₁ ∧ (ε₂ < μ ∨ (-ε₂ ≤ μ ∧
    ∀ v ∈ M, |iteratedFDeriv ℝ 3 f x (fun _ => v)| ≤ ε₃ ∧
      |iteratedFDeriv ℝ 2 f x (fun _ => v)| ≤ ε₂))

/-- Initial true small-Hessian directions used before the first ARp trial. -/
def initialDirections (f : E → ℝ) (x : E) (ε₂ : ℝ) : Set E :=
  {v | ‖v‖ = 1 ∧ |iteratedFDeriv ℝ 2 f x (fun _ => v)| ≤ ε₂}

/-- The full first-order ARp branch, with both higher-order tests explicitly disabled. -/
structure FirstOrderRun (f : E → ℝ) (p : ℕ) (x s : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ ε₁ : ℝ)
    (ε₂ ε₃ : WithTop ℝ) (N : ℕ) : Prop where
  trace : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  second_order_disabled : ε₂ = ⊤
  third_order_disabled : ε₃ = ⊤
  theta_first_pos : 0 < θ₁
  theta_first_le_one : θ₁ ≤ 1
  accuracy_first_pos : 0 < ε₁
  accuracy_first_le_one : ε₁ ≤ 1
  not_terminated : ∀ i < N, ε₁ < ‖fderiv ℝ f (x i)‖
  stationary_first : ∀ i < N,
    ‖fderiv ℝ (model f p (x i) (σ i)) (s i)‖ ≤ θ₁ * ‖s i‖ ^ p

/-- The full finite-second-order ARp branch, with the third-order test explicitly disabled. -/
structure SecondOrderRun (f : E → ℝ) (p : ℕ) (x s u : ℕ → E) (μ σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ : ℝ)
    (ε₃ : WithTop ℝ) (N : ℕ) : Prop where
  trace : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  order_ge_two : 2 ≤ p
  third_order_disabled : ε₃ = ⊤
  theta_first_pos : 0 < θ₁
  theta_first_le_one : θ₁ ≤ 1
  theta_second_pos : 0 < θ₂
  theta_second_le_one : θ₂ ≤ 1
  accuracy_first_pos : 0 < ε₁
  accuracy_first_le_one : ε₁ ≤ 1
  accuracy_second_pos : 0 < ε₂
  accuracy_second_le_one : ε₂ ≤ 1
  least_eigenpair : ∀ i ≤ N, SecondOrderTrustRegion.IsLeastEigenpair f (x i) (μ i) (u i)
  not_terminated : ∀ i < N, ε₁ < ‖fderiv ℝ f (x i)‖ ∨ μ i < -ε₂
  stationary_first : ∀ i < N,
    ‖fderiv ℝ (model f p (x i) (σ i)) (s i)‖ ≤ θ₁ * ‖s i‖ ^ p
  stationary_second : ∀ i < N, ∀ v : E, ‖v‖ = 1 → -θ₂ * ‖s i‖ ^ (p - 1) ≤
    iteratedFDeriv ℝ 2 (model f p (x i) (σ i)) (s i) (fun _ => v)

/-- The full finite-third-order ARp trace with the documented repaired stopping test.
The model-direction set is assigned before acceptance, including rejected trials. -/
structure FiniteRun (f : E → ℝ) (p : ℕ) (x s u : ℕ → E) (μ σ ρ : ℕ → ℝ)
    (M : ℕ → Set E) (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ ε₁ ε₂ ε₃ : ℝ)
    (N : ℕ) : Prop where
  trace : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  order_ge_three : 3 ≤ p
  theta_first_pos : 0 < θ₁
  theta_first_le_one : θ₁ ≤ 1
  theta_second_pos : 0 < θ₂
  theta_second_le_one : θ₂ ≤ 1
  theta_third_pos : 0 < θ₃
  theta_third_le_one : θ₃ ≤ 1
  accuracy_first_pos : 0 < ε₁
  accuracy_first_le_one : ε₁ ≤ 1
  accuracy_second_pos : 0 < ε₂
  accuracy_second_le_one : ε₂ ≤ 1
  accuracy_third_pos : 0 < ε₃
  accuracy_third_le_one : ε₃ ≤ 1
  least_eigenpair : ∀ i ≤ N, SecondOrderTrustRegion.IsLeastEigenpair f (x i) (μ i) (u i)
  initial_directions : M 0 = initialDirections f (x 0) ε₂
  model_directions : ∀ i < N, M (i + 1) = smallModelDirections f p (x i) (s i) (σ i) θ₂
  not_terminated : ∀ i < N, ¬finiteStop f (x i) (μ i) (M i) ε₁ ε₂ ε₃
  stationary : ∀ i < N, StepConditions f p (x i) (s i) (σ i) θ₁ θ₂ θ₃

/-- Function calls include initialization and every objective-based acceptance trial. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Every derivative order from one to p is evaluated initially and at accepted endpoints. -/
noncomputable def derivativeEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : ℕ :=
  (successfulIterations {i | η₁ ≤ ρ i} N).card + 1

omit [CompleteSpace E] in
/-- The repaired finite stopping predicate uses the actual derivative tests. -/
theorem finiteStop_iff (f : E → ℝ) (x : E) (μ : ℝ) (M : Set E) (ε₁ ε₂ ε₃ : ℝ) :
    finiteStop f x μ M ε₁ ε₂ ε₃ ↔ ‖fderiv ℝ f x‖ ≤ ε₁ ∧
      (ε₂ < μ ∨ (-ε₂ ≤ μ ∧ ∀ v ∈ M,
        |iteratedFDeriv ℝ 3 f x (fun _ => v)| ≤ ε₃ ∧
          |iteratedFDeriv ℝ 2 f x (fun _ => v)| ≤ ε₂)) := Iff.rfl

omit [CompleteSpace E] in
/-- Initial directions are exactly the true unit small-curvature directions. -/
theorem mem_initialDirections_iff (f : E → ℝ) (x : E) (ε₂ : ℝ) (v : E) :
    v ∈ initialDirections f x ε₂ ↔ ‖v‖ = 1 ∧
      |iteratedFDeriv ℝ 2 f x (fun _ => v)| ≤ ε₂ := Iff.rfl

/-- The initialized function-evaluation schedule has one call per trial. -/
theorem functionEvaluations_eq (N : ℕ) : functionEvaluations N = N + 1 := rfl

/-- The initialized derivative schedule has one call at every accepted endpoint. -/
theorem derivativeEvaluations_eq (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) :
    derivativeEvaluations ρ η₁ N =
      (successfulIterations {i | η₁ ≤ ρ i} N).card + 1 := rfl

end HighOrderRegularization
