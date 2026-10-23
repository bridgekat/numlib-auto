import Numlib.Optimization.Regularization.Inexact.Explicit.Counting
import Numlib.Optimization.Regularization.Inexact.ExecutionBounds

/-!
# Genuine uniform caps for explicit-accuracy executions

The primitive oracle and actual approximate-objective ratio imply all tensor
and parameter bounds needed for literal stopping budgets.
-/

namespace InexactRegularization.Explicit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Genuine objective regularity, actual oracle requests and parameter updates
supply the fixed caps for every finite execution, including its endpoint. -/
theorem actual_caps (h : Run f P ε D N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖) :
    (∀ k ≤ N, D.parameter k ≤ executionParameterCap P.toSettings L) ∧
      (∀ k ≤ N, ∀ i, 1 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ executionTensorCap
        P.toSettings L) :=
  ⟨fun _k hk => h.parameter_le hf (zero_le_one.trans hL) (hlip p le_rfl) hk,
    fun _k hk _i hi hip => h.tensor_norm_le (zero_le_one.trans hL)
      (fun j hj => hlip j hj.le) hk hi hip⟩

end Run
end InexactRegularization.Explicit
