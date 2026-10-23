import Numlib.Optimization.Regularization.HighOrder.CriticalityRun

/-!
# Literal outer high-order regularization returns

The outer algorithm requires nonincrease and either a step of norm strictly
larger than one with unchanged radii, or the actual model criticality tests.
It does not impose a positive fraction of global model decrease. Equal model
values cause an immediate exit before an objective trial or parameter update.
-/

namespace HighOrderRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The literal outer Step2 contract, including its strict large-step bypass. -/
structure OuterStepReturn {p q : ℕ} (f : E → ℝ) (θ ζ : ℝ) (ε : Fin q → ℝ)
    (x s : E) (σ : ℝ) (δ₀ δ : Fin q → ℝ) (direction : Fin q → E) : Prop where
  nonincrease : model f p x σ s ≤ model f p x σ 0
  radius_mem : ∀ a, 0 < δ a ∧ δ a ≤ 1
  tests : (1 < ‖s‖ ∧ δ = δ₀) ∨ ∀ a, ‖direction a‖ ≤ δ a ∧
    ζ * TaylorModel.criticality (model f p x σ) (modelOrder a) s (δ a) ≤
      TaylorModel.decrement (model f p x σ) (modelOrder a) s (direction a) ∧
    TaylorModel.decrement (model f p x σ) (modelOrder a) s (direction a) ≤
      ζ * θ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial
/-- An initial failed actual optimality check followed by a permitted zero-improvement
return. The literal outer algorithm exits at the initial point. -/
structure OuterZeroExit {p q : ℕ} (f : E → ℝ) (P : Settings p q)
    (ε : Fin q → ℝ) (x s : E) (δ₀ δ : Fin q → ℝ) (d₀ d : Fin q → E)
    (selected : Fin q) : Prop where
  accuracy_mem : ∀ a, 0 < ε a ∧ ε a < 1
  initial_radii : ∀ a, 0 < δ₀ a ∧ δ₀ a ≤ 1
  initial_check : OptimalityCheck f P.zeta ε δ₀ x d₀ (some selected)
  returned : OuterStepReturn (p := p) f P.theta P.zeta ε x s P.sigmaInitial δ₀ δ d
  zero_decrease : model f p x P.sigmaInitial s = model f p x P.sigmaInitial 0

/-- Only the initial iterate is produced before an immediate outer zero-model exit. -/
def OuterZeroExit.producedPoint {p q : ℕ} {f : E → ℝ} {P : Settings p q}
    {ε : Fin q → ℝ} {x s : E} {δ₀ δ : Fin q → ℝ} {d₀ d : Fin q → E}
    {selected : Fin q} (_exit : OuterZeroExit f P ε x s δ₀ δ d₀ d selected) (y : E) : Prop :=
  y = x
/-- The produced-point predicate of an immediate outer exit is the initial singleton. -/
theorem OuterZeroExit.producedPoint_iff {p q : ℕ} {f : E → ℝ} {P : Settings p q}
    {ε : Fin q → ℝ} {x s : E} {δ₀ δ : Fin q → ℝ} {d₀ d : Fin q → E}
    {selected : Fin q} (exit : OuterZeroExit f P ε x s δ₀ δ d₀ d selected) (y : E) :
    exit.producedPoint y ↔ y = x := Iff.rfl

end HighOrderRegularization
