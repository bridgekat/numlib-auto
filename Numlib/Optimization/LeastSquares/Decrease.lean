import Numlib.Optimization.LeastSquares.Measures
import Numlib.Optimization.Regularization.HighOrder.Step

/-!
# Actual residual-power regularization decrease

The genuine high-order model derivative tests and accepted objective decrease
imply all weighted first-, second- and third-order residual-power bounds.
The specification contains only model, objective-ratio, point and parameter
update components; it does not assert the full ARpLE stopping algorithm.
-/

namespace LeastSquares
open HighOrderRegularization
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]

/-- Only the actual model, ratio, point and parameter update components of ARpLE. -/
abbrev RegularizationTrace (r : E → F) (ℓ : ℝ) (p : ℕ)
    (x s : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop :=
  ModelTrace (powerObjective r ℓ) p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N

namespace RegularizationTrace
variable {r : E → F} {ℓ L η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ θ₃ : ℝ}
  {p N : ℕ}
  {x s : ℕ → E} {σ ρ : ℕ → ℝ}

omit [CompleteSpace E] in
/-- The actual first derivative step condition gives the full weighted residual-power decrease. -/
theorem decrease_first
    (h : RegularizationTrace r ℓ p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hℓ : 0 < ℓ) (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 < L) (hθ : 0 ≤ θ₁)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    (hfirst : ‖fderiv ℝ (model (powerObjective r ℓ) p (x i) (σ i)) (s i)‖ ≤
      θ₁ * ‖s i‖ ^ p) :
    decreaseConstant p p η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₁ * ℓ *
      firstMeasure r ℓ (x (i + 1)) ^ (((p + 1 : ℕ) : ℝ) / p) *
      ‖r (x (i + 1))‖ ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / p) ≤
        ‖r (x i)‖ ^ ℓ - ‖r (x (i + 1))‖ ^ ℓ := by
  have hm : 0 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
    (h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hc := decreaseConstant_pos p p h.updates.eta1_pos h.updates.min_pos hL hm hθ
  have hp : (0 : ℝ) < p := by exact_mod_cast h.order_pos
  have ha : 0 < ((p + 1 : ℕ) : ℝ) / p := div_pos (by positivity) hp
  have hd := ModelTrace.decrease_first h hf hL hθ hlip hi hs hfirst
  simpa only [firstMeasure_eq, mul_div_assoc] using
    residual_decrease_of_power hℓ hc.le (norm_nonneg _) ha hd

/-- The actual least Hessian certificate gives the weighted negative-curvature residual decrease. -/
theorem decrease_second
    (h : RegularizationTrace r ℓ p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp : 2 ≤ p) (hℓ : 0 < ℓ) (hf : ContDiff ℝ p (powerObjective r ℓ))
    (hL : 0 < L) (hθ : 0 ≤ θ₂)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    (hsecond : ∀ v : E, ‖v‖ = 1 → -θ₂ * ‖s i‖ ^ (p - 1) ≤
      iteratedFDeriv ℝ 2 (model (powerObjective r ℓ) p (x i) (σ i)) (s i) (fun _ => v))
    {μ : ℝ} {u : E}
    (heigen : SecondOrderTrustRegion.IsLeastEigenpair (powerObjective r ℓ) (x (i + 1)) μ u) :
    decreaseConstant p (p - 1) η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ * ℓ *
      max 0 (-secondMeasure r ℓ (x (i + 1)) μ) ^
        (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) *
      ‖r (x (i + 1))‖ ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) ≤
        ‖r (x i)‖ ^ ℓ - ‖r (x (i + 1))‖ ^ ℓ := by
  have hm : 0 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
    (h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hc := decreaseConstant_pos p (p - 1) h.updates.eta1_pos h.updates.min_pos hL hm hθ
  have hp' : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 0 < p - 1 by omega)
  have ha : 0 < ((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ) := div_pos (by positivity) hp'
  have hd := ModelTrace.decrease_second h hp hf hL hθ hlip hi hs hsecond heigen
  simpa only [max_neg_secondMeasure, mul_div_assoc] using
    residual_decrease_of_power hℓ hc.le (le_max_left 0 (-μ)) ha hd

omit [CompleteSpace E] in
/-- Every actual small-model-curvature direction satisfies the weighted third residual decrease. -/
theorem decrease_third
    (h : RegularizationTrace r ℓ p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp : 3 ≤ p) (hℓ : 0 < ℓ) (hf : ContDiff ℝ p (powerObjective r ℓ))
    (hL : 0 < L) (hθ : 0 ≤ θ₃)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    (hthird : ∀ v ∈ smallModelDirections (powerObjective r ℓ) p (x i) (s i) (σ i) θ₂,
      |iteratedFDeriv ℝ 3 (model (powerObjective r ℓ) p (x i) (σ i)) (s i) (fun _ => v)| ≤
        θ₃ * ‖s i‖ ^ (p - 2))
    {v : E} (hv : v ∈ smallModelDirections (powerObjective r ℓ) p (x i) (s i) (σ i) θ₂) :
    decreaseConstant p (p - 2) η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₃ * ℓ *
      thirdMeasure r ℓ (x (i + 1)) v ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) *
      ‖r (x (i + 1))‖ ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)) ≤
        ‖r (x i)‖ ^ ℓ - ‖r (x (i + 1))‖ ^ ℓ := by
  have hm : 0 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
    (h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hc := decreaseConstant_pos p (p - 2) h.updates.eta1_pos h.updates.min_pos hL hm hθ
  have hp' : (0 : ℝ) < (p - 2 : ℕ) := by exact_mod_cast (show 0 < p - 2 by omega)
  have ha : 0 < ((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ) := div_pos (by positivity) hp'
  have hd := ModelTrace.decrease_third h hp hf hL hθ hlip hi hs hthird hv
  simpa only [thirdMeasure_eq, mul_div_assoc] using
    residual_decrease_of_power hℓ hc.le (abs_nonneg _) ha hd

omit [CompleteSpace E] in
/-- The actual endpoint Hessian bound implies the final normalized small-curvature clause. -/
theorem small_curvature_le
    (h : RegularizationTrace r ℓ p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp : 2 ≤ p) (hf : ContDiff ℝ p (powerObjective r ℓ)) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    {v : E} (hv : v ∈ smallModelDirections (powerObjective r ℓ) p (x i) (s i) (σ i) θ₂) :
    directionalSecondMeasure r ℓ (x (i + 1)) v * ‖r (x (i + 1))‖ ^ (ℓ - 1) ≤
      1 / stepConstant (p - 1) L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ *
        ‖s i‖ ^ (p - 1) := by
  have hd := ModelTrace.small_curvature_le h hp hf hL hlip hi hs hv
  rw [directionalSecondMeasure_eq, ← derivativeWeight_eq]
  exact (Real.div_mul_normalizer_le (abs_nonneg _)).trans hd

end RegularizationTrace
end LeastSquares
