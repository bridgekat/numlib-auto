import Numlib.Optimization.Regularization.HighOrder.CriticalityRun
import Numlib.Optimization.HighOrder.ConstrainedCriticality

/-!
# Literal constrained outer regularization returns

Computed feasible Taylor directions and the actual constrained criticality
specify objective and model tests. A permitted large-step return preserves the
radii and bypasses the model tests. Equal model values cause immediate exit
at the current point, before an objective trial or acceptance update.
-/

namespace HighOrderRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Computed feasible Taylor directions select the first failed constrained
objective test, with its true constrained criticality approximation. -/
structure ConstrainedOptimalityCheck (f : E → ℝ) (X : Set E) {q : ℕ}
    (ζ : ℝ) (ε δ : Fin q → ℝ) (x : E) (direction : Fin q → E)
    (selected : Option (Fin q)) : Prop where
  feasible : ∀ a, (∀ b, selected = some b → a ≤ b) →
    x + direction a ∈ X ∧ ‖direction a‖ ≤ δ a
  approximation : ∀ a, (∀ b, selected = some b → a ≤ b) →
    ζ * TaylorModel.constrainedCriticality f (modelOrder a) X x (δ a) ≤
      TaylorModel.decrement f (modelOrder a) x (direction a)
  passed : selected = none → ∀ a,
    TaylorModel.decrement f (modelOrder a) x (direction a) <
      ζ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial
  failed : ∀ a, selected = some a →
    ζ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial ≤
      TaylorModel.decrement f (modelOrder a) x (direction a)
  earlier_passed : ∀ a, selected = some a → ∀ b < a,
    TaylorModel.decrement f (modelOrder b) x (direction b) <
      ζ * ε b * δ b ^ modelOrder b / (modelOrder b).factorial

/-- A literal feasible outer model return: nonincrease, legal radii and either
a large feasible step preserving the radii or the actual constrained model tests.
No positive global-gap condition is imposed by the outer algorithm. -/
structure ConstrainedOuterStepReturn (f : E → ℝ) (X : Set E) (p : ℕ) {q : ℕ}
    (θ ζ : ℝ) (ε δ₀ δ : Fin q → ℝ) (x s : E) (σ : ℝ)
    (direction : Fin q → E) : Prop where
  feasible : x + s ∈ X
  nonincrease : model f p x σ s ≤ model f p x σ 0
  radius_mem : ∀ a, 0 < δ a ∧ δ a ≤ 1
  large_or_tests : (1 < ‖s‖ ∧ δ = δ₀) ∨
    (∀ a, x + (s + direction a) ∈ X ∧ ‖direction a‖ ≤ δ a ∧
      ζ * TaylorModel.constrainedCriticality (model f p x σ) (modelOrder a)
        (TaylorModel.feasibleDisplacements X x) s (δ a) ≤
          TaylorModel.decrement (model f p x σ) (modelOrder a) s (direction a) ∧
      TaylorModel.decrement (model f p x σ) (modelOrder a) s (direction a) ≤
        ζ * θ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial)

/-- An initial failing constrained check followed by a permitted feasible
zero-model return. The algorithm returns the current point before any trial
objective evaluation or acceptance update. -/
structure ConstrainedOuterZeroExit (f : E → ℝ) (X : Set E) {p q : ℕ}
    (P : Settings p q) (ε : Fin q → ℝ) (x s : E)
    (δ₀ δ : Fin q → ℝ) (d₀ d : Fin q → E) (selected : Fin q) : Prop where
  accuracy_mem : ∀ a, 0 < ε a ∧ ε a < 1
  initial_mem : x ∈ X
  initial_radii : ∀ a, 0 < δ₀ a ∧ δ₀ a ≤ 1
  initial_check : ConstrainedOptimalityCheck f X P.zeta ε δ₀ x d₀ (some selected)
  returned : ConstrainedOuterStepReturn f X p P.theta P.zeta ε δ₀ δ x s
    P.sigmaInitial d
  zero_decrease : model f p x P.sigmaInitial s = model f p x P.sigmaInitial 0

/-- An immediate constrained zero exit produces only its initial current iterate. -/
def ConstrainedOuterZeroExit.producedPoint {f : E → ℝ} {X : Set E} {p q : ℕ}
    {P : Settings p q} {ε : Fin q → ℝ} {x s : E} {δ₀ δ : Fin q → ℝ}
    {d₀ d : Fin q → E} {selected : Fin q}
    (_run : ConstrainedOuterZeroExit f X P ε x s δ₀ δ d₀ d selected) (z : E) : Prop := z = x

/-- The sole iterate of an immediate constrained zero exit is its initial point. -/
theorem ConstrainedOuterZeroExit.producedPoint_iff {f : E → ℝ} {X : Set E} {p q : ℕ}
    {P : Settings p q} {ε : Fin q → ℝ} {x s : E} {δ₀ δ : Fin q → ℝ}
    {d₀ d : Fin q → E} {selected : Fin q}
    (run : ConstrainedOuterZeroExit f X P ε x s δ₀ δ d₀ d selected) (z : E) :
    run.producedPoint z ↔ z = x := Iff.rfl

end HighOrderRegularization
