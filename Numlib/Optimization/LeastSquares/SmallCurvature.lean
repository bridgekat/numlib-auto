import Numlib.Optimization.LeastSquares.Decrease

/-!
# Residual decrease from actual small-model-curvature directions

The actual endpoint directional Hessian has a natural-power step bound,
which yields the full weighted residual decrease with the second-order constant.
-/

namespace LeastSquares
open HighOrderRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F]
namespace RegularizationTrace
variable {r : E → F} {ℓ L η₁ η₂ γ₁ γ₂ γ₃ σmin θ₂ : ℝ} {p N : ℕ}
  {x s : ℕ → E} {σ ρ : ℕ → ℝ}

omit [CompleteSpace E] in
/-- A true small-model direction also yields a full successful decrease from its actual
endpoint directional Hessian, rather than only from the least Hessian value. -/
theorem decrease_directional_second
    (h : RegularizationTrace r ℓ p x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hp : 2 ≤ p) (hℓ : 0 < ℓ) (hf : ContDiff ℝ p (powerObjective r ℓ))
    (hL : 0 < L) (hθ : 0 ≤ θ₂)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p (powerObjective r ℓ) y -
      iteratedFDeriv ℝ p (powerObjective r ℓ) z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i)
    {v : E} (hv : v ∈ smallModelDirections (powerObjective r ℓ) p (x i) (s i) (σ i) θ₂) :
    decreaseConstant p (p - 1) η₁ σmin L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ * ℓ *
      directionalSecondMeasure r ℓ (x (i + 1)) v ^
        (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) *
      ‖r (x (i + 1))‖ ^ ((ℓ - 1) * ((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)) ≤
        ‖r (x i)‖ ^ ℓ - ‖r (x (i + 1))‖ ^ ℓ := by
  have hm : 0 ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
    (h.updates.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  have hk := stepConstant_pos (p - 1) hL hm hθ
  have hc := decreaseConstant_pos p (p - 1) h.updates.eta1_pos h.updates.min_pos hL hm hθ
  have hd := ModelTrace.small_curvature_le h hp hf hL.le hlip hi hs hv
  have hbound : stepConstant (p - 1) L (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ *
      |iteratedFDeriv ℝ 2 (powerObjective r ℓ) (x (i + 1)) (fun _ => v)| ≤
      ‖s i‖ ^ (p - 1) := by
    have hh : |iteratedFDeriv ℝ 2 (powerObjective r ℓ) (x (i + 1)) (fun _ => v)| ≤
        ‖s i‖ ^ (p - 1) / stepConstant (p - 1) L
          (max (σ 0) (γ₃ * L / (1 - η₂))) θ₂ := by
      convert hd using 1
      ring
    simpa only [mul_comm] using (le_div_iff₀ hk).mp hh
  have hobj := ModelTrace.decrease_of_step_lower h hi hs (by omega : 0 < p - 1)
    hk.le (abs_nonneg _) hbound
  have hpR : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (show 0 < p - 1 by omega)
  have ha : 0 < ((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ) := div_pos (by positivity) hpR
  have hres := residual_decrease_of_power hℓ hc.le (abs_nonneg _) ha hobj
  simpa only [directionalSecondMeasure_eq, decreaseConstant, mul_div_assoc] using hres
end RegularizationTrace
end LeastSquares
