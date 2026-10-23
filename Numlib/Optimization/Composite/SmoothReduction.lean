import Numlib.Optimization.Composite.Origin

/-!
# Smooth objectives as zero-residual composite problems

An outer function vanishing at zero leaves actual Taylor models and criticality
unchanged when its residual is identically zero.
-/

namespace Composite
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every finite Taylor model of the zero residual vanishes. -/
@[simp] theorem eval_zero_residual (p : ℕ) (x s : E) :
    TaylorModel.eval (fun _ : E => (0 : F)) p x s = 0 := by
  simp [TaylorModel.eval_eq_sum, iteratedFDeriv_fun_zero]

/-- A zero residual preserves the actual smooth Taylor polynomial. -/
theorem taylorModel_zero_residual (f : E → ℝ) {h : F → ℝ} (hh : h 0 = 0)
    (p : ℕ) (x s : E) :
    taylorModel f (fun _ => (0 : F)) h p x s = TaylorModel.eval f p x s := by
  simp [taylorModel, hh]

/-- A zero residual preserves actual smooth Taylor decrements. -/
theorem decrement_zero_residual (f : E → ℝ) {h : F → ℝ} (hh : h 0 = 0)
    (p : ℕ) (x s : E) :
    decrement f (fun _ => (0 : F)) h p x s = TaylorModel.decrement f p x s := by
  simp only [decrement, taylorModel_zero_residual f hh, TaylorModel.decrement]

/-- A zero residual preserves the supremum of actual Taylor decrements. -/
theorem criticality_zero_residual (f : E → ℝ) {h : F → ℝ} (hh : h 0 = 0)
    (p : ℕ) (x : E) (δ : ℝ) :
    criticality f (fun _ => (0 : F)) h p x δ = TaylorModel.criticality f p x δ := by
  unfold criticality TaylorModel.criticality
  congr 1
  congr 1
  funext s
  simp [taylorModel_zero_residual f hh, TaylorModel.decrement, TaylorModel.eval_zero]

/-- A zero residual preserves the genuine smooth regularized model. -/
theorem regularizedModel_zero_residual (f : E → ℝ) {h : F → ℝ} (hh : h 0 = 0)
    (p : ℕ) (x : E) (σ : ℝ) (s : E) :
    regularizedModel f (fun _ => (0 : F)) h p x σ s =
      HighOrderRegularization.model f p x σ s := by
  simp only [regularizedModel, ModelDecrease.penalized, taylorModel_zero_residual f hh,
    HighOrderRegularization.model]

end Composite
