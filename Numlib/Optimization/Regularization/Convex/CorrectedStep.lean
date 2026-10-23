import Numlib.Optimization.Regularization.Convex.ModelDirections
import Numlib.Optimization.Regularization.Convex.DerivativeStep
import Numlib.Optimization.Regularization.HighOrder.ParameterOn
import Numlib.Optimization.Regularization.HighOrder.Step

/-!
# Complete constrained derivative step estimates

The successful trial uses actual model-restricted direction sets. Every enabled
order has the exact factorial lower bound. Both lower-derivative directional
estimates are stated on the unit ball, the domain of the criticality measures.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- All enabled derivative step bounds and both unit-direction estimates hold
at an actual accepted constrained model trial. Finite enabled order `q` encodes
one, two or three tests without requiring disabled higher model derivatives. -/
theorem constrained_step_estimates {f : E → ℝ} {p : ℕ} {C S : Set E}
    {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ} {N i : ℕ}
    (h : ModelTrace f p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hx : ∀ k < N, x k ∈ C) (hxs : ∀ k < N, x k + s k ∈ C)
    (q : Fin 3) (hp : q.val + 1 ≤ p) (ε θ : Fin 3 → ℝ)
    (hε : ∀ j, 0 < ε j) (hθ : ∀ j, 0 < θ j)
    (hm : ∀ j ≤ q, modelDerivativeCriticality f p C (x i) (σ i) (s i)
      (θ 0 * ε 0) (θ 1 * ε 1) j ≤ θ j * ε j)
    (hi : i < N) (hs : η₁ ≤ ρ i) (τ₁ τ₂ : ℝ) :
    let σmax := max (σ 0) (γ₃ * L / (1 - η₂))
    (∀ j : Fin 3, j ≤ q →
      ε j < tensorCriticality (iteratedFDeriv ℝ (j.val + 1) f (x (i + 1)))
        (modelRestrictedDirections f p C (x i) (σ i) (s i) (θ 0 * ε 0) (θ 1 * ε 1) j) →
      (p - j.val).factorial * (1 - θ j) / (L + σmax) * ε j < ‖s i‖^(p - j.val)) ∧
    (∀ d ∈ firstRestrictedDirections f (feasibleDisplacements C (x (i + 1)))
        (x (i + 1)) (τ₁ * ε 0), ‖d‖ ≤ 1 →
      |fderiv ℝ (model f p (x i) (σ i)) (s i) d| ≤
        (L + σmax) / p.factorial * ‖s i‖^p + τ₁ * ε 0) ∧
    (1 ≤ q.val → ∀ d ∈ secondRestrictedDirections f
        (feasibleDisplacements C (x (i + 1))) (x (i + 1)) (τ₁ * ε 0) (τ₂ * ε 1),
      ‖d‖ ≤ 1 → |iteratedFDeriv ℝ 2 (model f p (x i) (σ i)) (s i) (fun _ => d)| ≤
        (L + σmax) / (p - 1).factorial * ‖s i‖^(p - 1) + τ₂ * ε 1) := by
  dsimp only
  have hcap := h.parameter_le_on hS hCS hC hf hL hlip hx hxs (le_of_lt hi)
  have hpos := h.updates.pos (le_of_lt hi)
  have hne := h.step_ne_zero hi
  have hpoint := h.successful_point hi hs
  constructor
  · intro j hj hfail
    have hjp : j.val + 1 ≤ p := by have := Fin.le_iff_val_le_val.mp hj; omega
    have hz := zero_mem_modelRestrictedDirections (f := f) (p := p) (σ := σ i)
      (hxs i hi)
      (mul_pos (hθ 0) (hε 0)).le (mul_pos (hθ 1) (hε 1)).le j
    rw [hpoint] at hfail
    have hb := derivative_step_lower_of_model_test hjp hS hCS hC hf hL hpos hcap
      hlip (hx i hi) (hxs i hi) hne hz (hm j hj) hfail
    simpa only [show p - (j.val + 1) + 1 = p - j.val by omega] using hb
  constructor
  · intro d hd hn
    have hb := abs_model_diagonal_le_of_objective_bound
      (show 1 ≤ p by omega) hS hCS hC hf hL hpos.le hcap hlip
      (hx i hi) (hxs i hi) hne hn
      (show |iteratedFDeriv ℝ 1 f (x i + s i) (fun _ => d)| ≤ τ₁ * ε 0 by
        simpa only [iteratedFDeriv_one_apply,←hpoint] using hd.2)
    simpa only [Nat.sub_add_cancel (show 1 ≤ p by omega),iteratedFDeriv_one_apply]
      using hb
  · intro hq d hd hn
    have hb := abs_model_diagonal_le_of_objective_bound
      (show 2 ≤ p by omega) hS hCS hC hf hL hpos.le hcap hlip
      (hx i hi) (hxs i hi) hne hn
      (show |iteratedFDeriv ℝ 2 f (x i + s i) (fun _ => d)| ≤ τ₂ * ε 1 by
        rw [←hpoint]; exact hd.2)
    simpa only [show p - 2 + 1 = p - 1 by omega] using hb

end ConvexRegularization
