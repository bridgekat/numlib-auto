import Numlib.Optimization.HighOrder.ModelDecrease
import Numlib.Analysis.Calculus.TaylorModel.Holder
import Numlib.Optimization.EvaluationComplexity.ParameterUpdates

/-!
# Cubic regularization model decrease and parameter bounds

Only the model-improvement, ratio and parameter-update components of AR2 are
needed for these results. The Taylor polynomial is constructed from the actual
derivative tensors. Stationarity and stopping rules play no role in this bound.
-/

namespace CubicRegularization

open TaylorModel ModelDecrease EvaluationComplexity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual cubic regularization of the quadratic Taylor polynomial. -/
noncomputable def model (f : E → ℝ) (x : E) (σ : ℝ) (s : E) : ℝ :=
  penalized (eval f 2 x) 2 σ s

/-- The components of an AR2 trace relevant to the parameter bound: strict
improvement of the actual cubic model, objective-based ratio and exact updates.
This is a component specification, not a complete AR2 algorithm predicate. -/
structure ModelTrace (f : E → ℝ) (x s : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop where
  updates : RegularizationParameterUpdates σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  improvement : ∀ i < N, model f (x i) (σ i) (s i) < model f (x i) (σ i) 0
  ratio : ∀ i < N, ρ i = (f (x i) - f (x i + s i)) /
    (eval f 2 (x i) 0 - eval f 2 (x i) (s i))

namespace ModelTrace

variable {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ} {N : ℕ}

/-- Strict cubic-model improvement yields (3.3.13). -/
theorem model_decrease (h : ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i : ℕ} (hi : i < N) :
    σ i / 6 * ‖s i‖ ^ 3 < eval f 2 (x i) 0 - eval f 2 (x i) (s i) := by
  convert penalty_lt_decrement (eval f 2 (x i)) 2 (σ i) (s i)
    (h.improvement i hi) using 1
  norm_num

/-- The acceptance ratio is well-defined at every strict model improvement. -/
theorem denominator_pos (h : ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    {i : ℕ} (hi : i < N) : 0 < eval f 2 (x i) 0 - eval f 2 (x i) (s i) := by
  have hσ := h.updates.pos (show i ≤ N by omega)
  have hpen : 0 ≤ σ i / 6 * ‖s i‖ ^ 3 := by positivity
  exact hpen.trans_lt (h.model_decrease hi)

/-- A parameter above the Hessian Lipschitz threshold guarantees very
successful acceptance, using the sharp actual Taylor value remainder. -/
theorem very_successful (h : ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hlarge : L / (1 - η₂) ≤ σ i) : η₂ ≤ ρ i := by
  have hη : 0 < 1 - η₂ := sub_pos.mpr h.updates.eta2_lt_one
  have hmul := (div_le_iff₀ hη).mp hlarge
  have herr := abs_sub_eval_le_lipschitz (p := 1) (C := Set.univ) (D := Set.univ)
    isOpen_univ (Set.Subset.refl _) convex_univ hf.contDiffOn hL
    (fun y _ z _ => hlip y z) (Set.mem_univ (x i)) (Set.mem_univ (x i + s i))
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at herr
  have hd := h.model_decrease hi
  have he : f (x i + s i) - eval f 2 (x i) (s i) ≤
      (1 - η₂) * (eval f 2 (x i) 0 - eval f 2 (x i) (s i)) := by
    have he1 := (abs_le.mp herr).2
    have hd1 := mul_le_mul_of_nonneg_left hd.le hη.le
    have hmul1 := mul_le_mul_of_nonneg_right hmul (pow_nonneg (norm_nonneg (s i)) 3)
    nlinarith
  rw [h.ratio i hi]
  apply (le_div_iff₀ (h.denominator_pos hi)).mpr
  rw [eval_zero] at he ⊢
  linarith

/-- The actual three-case update mechanism gives the uniform bound (3.3.14). -/
theorem parameter_le (h : ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i ≤ N) : σ i ≤ max (σ 0) (γ₃ * L / (1 - η₂)) := by
  simpa only [mul_div_assoc] using h.updates.le_max_initial_threshold
    (fun j hj hlarge => h.very_successful hf hL hlip hj hlarge) hi

end ModelTrace
end CubicRegularization
