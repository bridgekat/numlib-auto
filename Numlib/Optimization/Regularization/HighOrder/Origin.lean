import Numlib.Optimization.Regularization.ModelCriticality
import Numlib.Optimization.Regularization.HighOrder.Parameter
import Numlib.Analysis.Calculus.TaylorModel.PolynomialDerivative
import Numlib.Optimization.HighOrder.CriticalityEquality
import Mathlib.Tactic

/-!
# Actual origin derivatives of norm-regularized Taylor models

The norm-power penalty has zero actual derivatives through the Taylor degree
at the origin. The polynomial derivative identity therefore identifies every
model derivative at zero with the corresponding derivative of the objective.
-/

namespace HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every actual derivative of the regularized model at zero through degree
`p` equals the corresponding true objective derivative at its center. -/
theorem iteratedFDeriv_model_zero {f : E → ℝ} {p j : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hjp : j ≤ p) (σ : ℝ) :
    iteratedFDeriv ℝ j (model f p x σ) 0 = iteratedFDeriv ℝ j f x := by
  let c : ℝ := σ / ((p + 1).factorial : ℝ)
  have hpow : ContDiff ℝ j (fun z : E => ‖z‖ ^ (p + 1)) := by
    have hj : (j : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hjp
    simpa only [Real.rpow_natCast] using (contDiff_normRpow_of_nat_lt (E := E) hj)
  have hz : iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) 0 = 0 := by
    have hj : (j : ℝ) < ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_of_le hjp
    simpa only [Real.rpow_natCast] using (iteratedFDeriv_normRpow_zero_of_lt (E := E) hj)
  have hadd := iteratedFDeriv_add_apply (x := (0 : E))
    (TaylorModel.contDiff_eval f p x j).contDiffAt (hpow.contDiffAt.const_smul c)
  have hscale := iteratedFDeriv_const_smul_apply' (x := (0 : E)) (a := c) hpow.contDiffAt
  rw [hscale, hz, smul_zero, add_zero, TaylorModel.iteratedFDeriv_eval hf hjp,
    TaylorModel.eval_zero] at hadd
  convert! hadd using 1

/-- The genuine Taylor polynomial of the model at zero is exactly the
corresponding Taylor polynomial of the original objective at its center. -/
theorem eval_model_zero {f : E → ℝ} {p j : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hjp : j ≤ p) (σ : ℝ) (d : E) :
    TaylorModel.eval (model f p x σ) j 0 d = TaylorModel.eval f j x d := by
  rw [TaylorModel.eval_eq_sum, TaylorModel.eval_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedFDeriv_model_zero hf ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hjp)]

/-- The actual model and objective criticality agree at their respective
centers, on every common displacement ball and at every order through `p`. -/
theorem criticality_model_zero {f : E → ℝ} {p j : ℕ} {x : E}
    (hf : ContDiffAt ℝ p f x) (hjp : j ≤ p) (σ δ : ℝ) :
    TaylorModel.criticality (model f p x σ) j 0 δ = TaylorModel.criticality f j x δ := by
  apply TaylorModel.criticality_eq_of_decrement_eq
  intro d
  rw [TaylorModel.decrement_eq, TaylorModel.decrement_eq, model_zero,
    eval_model_zero hf hjp]

end HighOrderRegularization
