import Numlib.Optimization.TrustRegion.Regularized.Step
import Numlib.Optimization.TrustRegion.SecondOrder.Finite

/-!
# Operational regularized trust-region executions

The finite trace records the fixed regularization, enabled stopping tests,
actual least Hessian eigenpairs, model improvement, interior model stationarity,
forced boundary steps for negative curvature, objective ratio and point/radius
updates. No radius floor, sufficient objective decrease or complexity bound is
assumed in the execution.
-/

namespace RegularizedTrustRegion
open SecondOrderTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual termination test, with an infinite second tolerance disabling
its curvature condition. -/
def Stopped (f : E → ℝ) (x : E) (μ ε₁ : ℝ) (ε₂ : WithTop ℝ) : Prop :=
  ‖gradient f x‖ ≤ ε₁ ∧ ∀ e : ℝ, ε₂ = (e : WithTop ℝ) → -e ≤ μ

/-- The termination predicate is exactly the actual gradient and enabled
least-eigenvalue tests. -/
theorem stopped_iff (f : E → ℝ) (x : E) (μ ε₁ : ℝ) (ε₂ : WithTop ℝ) :
    Stopped f x μ ε₁ ε₂ ↔
      ‖gradient f x‖ ≤ ε₁ ∧
        ∀ e : ℝ, ε₂ = (e : WithTop ℝ) → -e ≤ μ := Iff.rfl

/-- Complete permitted executions of regularized quadratic trust-region steps,
with the first-order or finite-second-order stopping mode specified explicitly. -/
structure Run (f : E → ℝ) (x s u : ℕ → E) (μ Δ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ : ℝ) (ε₂ : WithTop ℝ) (N : ℕ) : Prop
    extends ModelTrace f x s Δ ρ η₁ η₂ γ₁ γ₂ γ₃ ε N where
  first_accuracy_pos : 0 < ε₁
  first_accuracy_le_one : ε₁ ≤ 1
  theta_pos : 0 < θ
  mode : (ε₂ = ⊤ ∧ ε = Real.sqrt ε₁) ∨ (ε₂ = (ε : WithTop ℝ) ∧ ε ≤ 1)
  least_eigenpair : ∀ i ≤ N, ε₂ ≠ ⊤ → IsLeastEigenpair f (x i) (μ i) (u i)
  not_terminated : ∀ i < N, ¬Stopped f (x i) (μ i) ε₁ ε₂
  interior_stationarity : ∀ i < N, ‖s i‖ < Δ i →
    ‖fderiv ℝ (model f (x i) ε) (s i)‖ ≤ θ / 2 * ‖s i‖ ^ 2
  curvature_boundary : ∀ i < N, ∀ e : ℝ, ε₂ = (e : WithTop ℝ) →
    μ i < -e → ‖s i‖ = Δ i
  point_update : ∀ i < N, x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i

namespace Run
variable {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ L : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}

/-- The operational regularization weight lies in the source's normalized interval. -/
theorem regularization_le_one
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N) : ε ≤ 1 := by
  rcases h.mode with ⟨_, he⟩ | ⟨_, he⟩
  · rw [he]
    exact Real.sqrt_le_one.mpr h.first_accuracy_le_one
  · exact he

/-- At an accepted interior step, the next actual gradient satisfies the
minimum-form lower bound on step length. -/
theorem interior_step_lower
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) (ha : η₁ ≤ ρ i) (hs : ‖s i‖ < Δ i) :
    (Real.sqrt (1 + 2 * (L + θ)))⁻¹ *
      min ε (‖gradient f (x (i + 1))‖ * ε⁻¹) ≤ ‖s i‖ := by
  have hn : ‖gradient f (x (i + 1))‖ = ‖fderiv ℝ f (x i + s i)‖ := by
    rw [h.point_update i hi, ite_eq_left ha, ← toDual_gradient,
      (InnerProductSpace.toDual ℝ E).norm_map]
  rw [hn]
  exact RegularizedTrustRegion.interior_step_lower hf hL h.theta_pos.le
    h.regularization_pos hlip (x i) (s i) (h.interior_stationarity i hi hs)

/-- The actual objective ratio and accepted point update give sufficient
objective decrease in terms of the regularized step norm. -/
theorem successful_decrease_step
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    {i : ℕ} (hi : i < N) (ha : η₁ ≤ ρ i) :
    η₁ / 2 * ε * ‖s i‖ ^ 2 ≤ f (x i) - f (x (i + 1)) := by
  have hd := h.toModelTrace.denominator_pos hi
  have hr := ha
  rw [h.ratio i hi] at hr
  have hb := (le_div_iff₀ hd).mp hr
  have hm := model_decrease (h.improvement i hi)
  have hη := h.updates.eta1_pos
  have hh := mul_le_mul_of_nonneg_left hm.le hη.le
  rw [h.point_update i hi, ite_eq_left ha]
  nlinarith

/-- An unsuccessful trial leaves the actual iterate unchanged. -/
theorem rejected_point
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    {i : ℕ} (hi : i < N) (ha : ¬η₁ ≤ ρ i) : x (i + 1) = x i := by
  rw [h.point_update i hi, ite_eq_right ha]

end Run
end RegularizedTrustRegion
