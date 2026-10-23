import Numlib.Optimization.Regularization.Inexact.Explicit.Radius
import Numlib.Optimization.Regularization.Inexact.ExecutionBounds

/-!
# Finite accuracy verification of literal regularization stopping

Actual EDA radius histories imply a common positive floor. Uniformly small
known derivative requests then force every explicit finite error-budget check
to pass. Thus a completed computed optimality loop exits through literal
Step1.5.1 and certifies true objective criticality.
-/

namespace InexactRegularization.Explicit
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Proved radius floors and a genuine cap on the actual requests force the
literal explicit termination branch after every computed optimality check passes. -/
theorem passing_check_stops_of_caps (h : Run f P ε D N) {M S H : ℝ} (hM : 1 ≤ M)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k ≤ N) (hselected : D.selected k = none) (hH : 0 ≤ H)
    (hrequests : ∀ i, 1 ≤ i → i ≤ q → D.accuracy k i ≤ H)
    (hsmall : H ≤ verificationThreshold q P.zeta
      (stepRadiusCoefficient P.zeta P.theta M S) 1 (minimumAccuracy P.order_pos ε)) :
    StopsAt P ε D k ∧
      ∀ a, TaylorModel.criticality f (modelOrder a) (D.point k) (D.checkedRadius k a) ≤
        ε a * D.checkedRadius k a ^ modelOrder a / (modelOrder a).factorial := by
  have hκ := stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one.le hM
  have hfloor := (h.radius_floor_sharp hM hparam hjet).2.1
  have hb := vectorVerification_of_uniform_cap P.order_pos
    (fun a => (h.checkedRadius_mem hk a).1.le) (fun a => (h.checkedRadius_mem hk a).2)
    P.zeta_pos.le hκ.1.le hκ.2 (by norm_num : (0 : ℝ) < 1)
    h.accuracy_pos h.accuracy_le_one hH
    (fun a => (mul_le_mul_of_nonneg_left (minimumAccuracy_le P.order_pos ε a) hκ.1.le).trans
      (hfloor k hk a)) hsmall (D.accuracy k) hrequests
  have hstop : StopsAt P ε D k := ⟨hselected, fun a => by
    simpa only [one_mul] using hb a⟩
  exact ⟨hstop, (h.stopped_optimality hk hstop).2⟩

/-- Actual smoothness and primitive function/derivative oracle rules derive
all caps needed for explicit stopping. The corrected guarded parameter cap is
used; no printed false cap or radius/decrease conclusion is assumed. -/
theorem passing_check_stops (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L H : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, i ≤ p → ∀ x y,
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖)
    {k : ℕ} (hk : k ≤ N) (hselected : D.selected k = none) (hH : 0 ≤ H)
    (hrequests : ∀ i, 1 ≤ i → i ≤ q → D.accuracy k i ≤ H)
    (hsmall : H ≤ verificationThreshold q P.zeta
      (stepRadiusCoefficient P.zeta P.theta (executionTensorCap P.toSettings L)
        (executionParameterCap P.toSettings L)) 1 (minimumAccuracy P.order_pos ε)) :
    StopsAt P ε D k ∧
      ∀ a, TaylorModel.criticality f (modelOrder a) (D.point k) (D.checkedRadius k a) ≤
        ε a * D.checkedRadius k a ^ modelOrder a / (modelOrder a).factorial := by
  apply h.passing_check_stops_of_caps (one_le_executionTensorCap P.toSettings hL)
    (fun k hk => h.parameter_le hf (zero_le_one.trans hL) (hlip p le_rfl) hk)
    (fun k hk i hi hip => h.tensor_norm_le (zero_le_one.trans hL)
      (fun j hj => hlip j hj.le) hk (by omega) hip)
    hk hselected hH hrequests hsmall

end Run
end InexactRegularization.Explicit
