import Numlib.Optimization.Composite.Run

/-!
# Literal outer composite returns and immediate zero-decrease exits

The outer algorithm requires nonincrease and bypasses all model criticality
tests when the returned step has norm at least one. This contract is weaker
than the positive global-gap fraction of its optional detailed solver.
-/

namespace Composite
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The literal outer Step 2 model-return contract, including its large-step
bypass. It imposes no positive fraction of the available global model gap. -/
structure OuterStepReturn (f : E → ℝ) (c : E → F) (h : F → ℝ) (p : ℕ)
    {q : ℕ} (θ ζ : ℝ) (ε : Fin q → ℝ) (x s : E) (σ : ℝ)
    (δ : Fin q → ℝ) (direction : Fin q → E) : Prop where
  nonincrease : regularizedModel f c h p x σ s ≤ regularizedModel f c h p x σ 0
  radius_mem : ∀ a, 0 < δ a ∧ δ a ≤ 1
  tests : ‖s‖ < 1 → ∀ a, ‖direction a‖ ≤ δ a ∧
    ζ * criticality (smoothModel f p x σ) (residualModel c p x) h
      (InexactTrustRegion.modelOrder a) s (δ a) ≤
        decrement (smoothModel f p x σ) (residualModel c p x) h
          (InexactTrustRegion.modelOrder a) s (direction a) ∧
    decrement (smoothModel f p x σ) (residualModel c p x) h
      (InexactTrustRegion.modelOrder a) s (direction a) ≤
        ζ * θ * ε a * δ a ^ InexactTrustRegion.modelOrder a /
          (InexactTrustRegion.modelOrder a).factorial

/-- Every detailed-solver return satisfies the literal outer return contract. -/
theorem StepOutput.outerStepReturn {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p q : ℕ} {θ ζ σ μ : ℝ} {ε δ : Fin q → ℝ} {x s : E} {d : Fin q → E}
    (ho : StepOutput f c h p θ ζ ε x s σ μ δ d) :
    OuterStepReturn f c h p θ ζ ε x s σ δ d :=
  ⟨ho.nonincrease, ho.radius_mem, ho.tests⟩

/-- An initial failing computed check followed by an actual permitted zero-model
return. The algorithm exits before an objective trial or a parameter update. -/
structure OuterZeroExit (f : E → ℝ) (c : E → F) (h : F → ℝ)
    {p q : ℕ} (P : Settings p q) (ε : Fin q → ℝ) (x s : E)
    (δ₀ δ : Fin q → ℝ) (d₀ d : Fin q → E) (selected : Fin q) : Prop where
  accuracy_mem : ∀ a, 0 < ε a ∧ ε a < 1
  initial_radii : ∀ a, 0 < δ₀ a ∧ δ₀ a ≤ 1
  initial_check : OptimalityCheck f c h P.zeta ε δ₀ x d₀ (some selected)
  returned : OuterStepReturn f c h p P.theta P.zeta ε x s P.sigmaInitial δ d
  zero_decrease : regularizedModel f c h p x P.sigmaInitial s =
    regularizedModel f c h p x P.sigmaInitial 0

/-- Exactly the initial point is produced before an immediate outer zero exit. -/
def OuterZeroExit.producedPoint {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p q : ℕ} {P : Settings p q} {ε : Fin q → ℝ} {x s : E}
    {δ₀ δ : Fin q → ℝ} {d₀ d : Fin q → E} {selected : Fin q}
    (_run : OuterZeroExit f c h P ε x s δ₀ δ d₀ d selected) (z : E) : Prop := z = x

/-- The produced-point predicate for an immediate outer exit is a singleton. -/
theorem OuterZeroExit.producedPoint_iff {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p q : ℕ} {P : Settings p q} {ε : Fin q → ℝ} {x s : E}
    {δ₀ δ : Fin q → ℝ} {d₀ d : Fin q → E} {selected : Fin q}
    (run : OuterZeroExit f c h P ε x s δ₀ δ d₀ d selected) (z : E) :
    run.producedPoint z ↔ z = x := Iff.rfl

end Composite
