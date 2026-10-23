import Numlib.Optimization.Regularization.Cubic.Parameter

/-!
# Cartis–Gould–Toint, Section 3.3: cubic model decrease and parameter bounds

These results use precisely the model-improvement, acceptance-ratio and
parameter-update components of AR2. The model is built from actual Taylor
derivative tensors. Step stationarity, second-order tests and termination are
irrelevant to these two lemmas; the complete AR2 trace remains separately planned.
-/

namespace CartisGouldToint

/-- The actual AR2 cubic model (3.3.1), with coefficient `σ/6`. -/
noncomputable abbrev ar2Model {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) (σ : ℝ) (s : E) : ℝ := CubicRegularization.model f x σ s

/-- The model, actual-ratio and update components of AR2 used in Lemma 3.3.2.
This does not stand in for the complete algorithm trace. -/
abbrev ar2ModelTrace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x s : ℕ → E) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop :=
  CubicRegularization.ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N

/-- **Lemma 3.3.1.** Strict decrease of the actual cubic model, as required
by Step 2 of AR2, gives the Taylor decrease (3.3.13). -/
theorem lemma_3_3_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x s : E) (σ : ℝ) (hs : ar2Model f x σ s < ar2Model f x σ 0) :
    σ / 6 * ‖s‖ ^ 3 < TaylorModel.eval f 2 x 0 - TaylorModel.eval f 2 x s := by
  convert ModelDecrease.penalty_lt_decrement (TaylorModel.eval f 2 x) 2 σ s hs
    using 1
  norm_num

/-- **Lemma 3.3.2.** Actual second-derivative Lipschitz continuity and the
AR2 model/ratio/update rules imply the uniform bound (3.3.14). -/
theorem lemma_3_3_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x s : ℕ → E} {σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin L : ℝ} {N : ℕ}
    (h : ar2ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖) :
    ∀ i ≤ N, σ i ≤ max (σ 0) (γ₃ * L / (1 - η₂)) :=
  fun _ hi => h.parameter_le hf hL hlip hi

end CartisGouldToint
