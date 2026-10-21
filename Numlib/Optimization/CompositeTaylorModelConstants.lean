import Numlib.Optimization.CompositeTaylorModels
import Numlib.Optimization.HigherOrderRegularization
import Numlib.Optimization.TaylorOptimality
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Constant inner maps and normalized norm compositions

Taylor polynomials preserve constants. Consequently a normalized composition of a constant
zero inner map leaves every smooth Taylor model and decrement unchanged. The norm gives a
nonzero, convex, Lipschitz subadditive composition without any differentiability requirement.
-/

noncomputable section
open scoped Nat NNReal
open Set
namespace Optimization
namespace RegularizedTaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Taylor polynomials preserve constant maps in every degree. -/
@[simp] theorem taylorModel_const (a : F) (p : ℕ) (x s : E) :
    taylorModel (fun _ : E => a) p x s = a := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [taylorModel_succ, ih, iteratedFDeriv_succ_const]
    simp

/-- Taylor models of the constant zero map are the constant zero function. -/
@[simp] theorem taylorModel_const_zero_fun (p : ℕ) (x : E) :
    taylorModel (fun _ : E => (0 : F)) p x = fun _ => 0 := by
  funext s
  exact taylorModel_const 0 p x s

end RegularizedTaylorModel
namespace CompositeTaylorModels
open RegularizedTaylorModel TaylorCriticality
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The norm is an admissible composition, without any differentiability assumption. -/
def normComposition (F : Type*) [NormedAddCommGroup F] : LipschitzSubadditiveComposition F where
  toFun := norm
  constant := 1
  lipschitz := lipschitzWith_one_norm
  map_zero := norm_zero
  map_add_le := norm_add_le

omit [NormedSpace ℝ F] in
@[simp] theorem normComposition_apply (u : F) : normComposition F u = ‖u‖ := rfl

/-- Convexity needed by the favorable first-order branch is a proved property of the norm. -/
theorem normComposition_convex : ConvexOn ℝ univ (normComposition F) :=
  convexOn_norm convex_univ

/-- A normalized composition and a constant zero vector map leave the Taylor model unchanged. -/
@[simp] theorem model_const_zero (f : E → ℝ) (h : LipschitzSubadditiveComposition F)
    (p : ℕ) (x s : E) : model f (fun _ => (0 : F)) h p x s = taylorModel f p x s := by
  simp [model]

/-- The regularized composite model agrees with the actual smooth regularized model. -/
@[simp] theorem regularizedModel_const_zero (f : E → ℝ)
    (h : LipschitzSubadditiveComposition F) (p : ℕ) (x : E) (σ : ℝ) (s : E) :
    regularizedModel f (fun _ => (0 : F)) h p x σ s =
      HigherOrderRegularization.model f p x σ s := by
  simp only [CompositeTaylorModels.regularizedModel, model_const_zero]
  unfold HigherOrderRegularization.model
  ring

/-- Generalized decrements agree with smooth Taylor decrements on the constant embedding. -/
@[simp] theorem decrement_const_zero (f : E → ℝ) (h : LipschitzSubadditiveComposition F)
    (p : ℕ) (x s : E) : decrement f (fun _ => (0 : F)) h p x s = taylorDecrement f p x s := by
  simp [decrement, taylorDecrement]

/-- The constant embedding also identifies the whole decrement functions. -/
@[simp] theorem decrement_const_zero_fun (f : E → ℝ) (h : LipschitzSubadditiveComposition F)
    (p : ℕ) (x : E) : decrement f (fun _ => (0 : F)) h p x = taylorDecrement f p x := by
  funext s
  exact decrement_const_zero f h p x s

end CompositeTaylorModels
end Optimization
