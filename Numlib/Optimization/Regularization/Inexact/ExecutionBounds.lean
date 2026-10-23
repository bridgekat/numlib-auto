import Numlib.Optimization.Regularization.Inexact.RunCounting

/-!
# Analytic caps for actual guarded regularization executions

The true objective's derivative Lipschitz constants and the fixed oracle
settings determine parameter and tensor caps before all accuracies and
execution data. No bound on a computed trace is assumed here.
-/

namespace InexactRegularization

/-- A common actual tensor cap from the objective regularity and initial requests. -/
noncomputable def executionTensorCap {p q : ℕ} (P : Settings p q) (L : ℝ) : ℝ :=
  L + P.errorBound * P.initialCap

/-- A normalized objective regularity bound gives a tensor cap of at least one. -/
theorem one_le_executionTensorCap {p q : ℕ} (P : Settings p q) {L : ℝ} (hL : 1 ≤ L) :
    1 ≤ executionTensorCap P L := hL.trans
  (le_add_of_nonneg_right (mul_nonneg P.errorBound_nonneg P.initialCap_nonneg))

/-- The genuine parameter cap is positive independently of all requested accuracies. -/
theorem executionParameterCap_pos {p q : ℕ} (P : Settings p q) (L : ℝ) :
    0 < executionParameterCap P L :=
  (P.sigmaMin_pos.trans_le P.sigmaMin_le_initial).trans_le (le_max_left _ _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Genuine objective regularity, actual oracle requests and parameter updates
supply the fixed caps for every finite execution, including its endpoint. -/
theorem actual_caps (h : Run f P ε D N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖) :
    (∀ k ≤ N, D.parameter k ≤ executionParameterCap P L) ∧
      (∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ executionTensorCap P L) :=
  ⟨fun _k hk => h.parameter_le hf (zero_le_one.trans hL) (hlip p le_rfl) hk,
    fun _k hk _i hi hip => h.tensor_norm_le (zero_le_one.trans hL)
      (fun j hj => hlip j hj.le) hk hi hip⟩

end Run
end InexactRegularization
