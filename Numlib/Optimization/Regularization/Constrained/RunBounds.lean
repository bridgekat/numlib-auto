import Numlib.Optimization.Regularization.Constrained.Run
import Numlib.Optimization.Regularization.HighOrder.RunBounds

/-!
# Derived bounds for constrained regularization executions

Actual true-objective ratios and updates bound the penalty parameters. The
primitive feasible model computations give positive radius floors. Actual
all-order tensor errors on translated feasible balls then yield a step-power
obstruction before the next true constrained optimality certificate.
-/

namespace ConstrainedRegularization
open Set InexactTrustRegion
open HighOrderRegularization (parameterCap parameterCap_pos)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {X : Set E} {P : Settings p q}
  {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}

omit [FiniteDimensional ℝ E] in
/-- Actual objective-based ratios and operational parameter updates derive the
uniform cap independently of all requested accuracies and constraints. -/
theorem parameter_le (h : Run f X P ε D N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {k : ℕ} (hk : k ≤ N) : D.parameter k ≤ parameterCap P L := by
  simpa only [parameterCap, h.initial_parameter] using
    h.modelTrace.parameter_le hf (zero_le_one.trans hL) hlip hk

/-- Every short actual feasible detailed solve retains the explicit positive
radius floor derived from its genuine halving guards and model derivatives. -/
theorem solved_radius_floor (h : Run f X P ε D N) (hf : ContDiff ℝ p f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ i f u - iteratedFDeriv ℝ i f v‖ ≤ L * ‖u - v‖)
    {k : ℕ} (hk : k ≤ N) (hselected : D.selected k ≠ none) (hs : ‖D.step k‖ ≤ 1)
    (a : Fin q) :
    P.zeta * P.theta / (8 * (3 * L + parameterCap P L)) * ε a ≤ D.solvedRadius k a := by
  have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
  have hσ := h.modelTrace.updates.pos hk
  have hcap := h.parameter_le hf hL (hlip p hp le_rfl) hk
  have hA := HighOrderRegularization.tensor_bound_of_derivative_lipschitz f
    (zero_le_one.trans hL) (fun i hi hip => hlip i hi hip.le) (D.point k)
  have hm := h.step_two k hk hselected
  change ModelSolve.ConstrainedStepComputation
    (ModelDecrease.penalized (TaylorModel.ofJet (ftaylorSeries ℝ f (D.point k)) p) p
      (D.parameter k)) _ _ _ _ _ _ _ at hm
  have hb := hm.radius_lower_penalized (ftaylorSeries ℝ f (D.point k)) hσ.le hL hA
    (fun a => ⟨by unfold modelOrder; omega, by have := P.order_le; unfold modelOrder; omega⟩)
    P.theta_pos P.theta_lt_one.le P.zeta_le_one
    (fun a => ⟨h.accuracy_pos a, h.accuracy_le_one a⟩) hs a
  have hc : P.zeta * P.theta / (8 * (3 * L + parameterCap P L)) ≤
      P.zeta * P.theta / (8 * (3 * L + D.parameter k)) :=
    div_le_div_of_nonneg_left (mul_pos P.zeta_pos P.theta_pos).le
      (by linarith) (by linarith)
  exact (mul_le_mul_of_nonneg_right hc (h.accuracy_pos a).le).trans hb

/-- Actual accepted short trials before a next true certificate force a
weighted step-power obstruction at actual inherited feasible radii. -/
theorem criticality_obstruction (h : Run f X P ε D N) (hX : IsClosed X)
    (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    {k : ℕ} (hk : k < N) (ha : P.eta1 ≤ D.ratio k) (hs : ‖D.step k‖ ≤ 1)
    (hnot : ¬TargetAt f X P ε D (k + 1)) :
    ∃ a, (1 - P.theta) * ε a * D.solvedRadius k a ^ modelOrder a /
        (modelOrder a).factorial ≤
      (L + parameterCap P L) * ∑ i ∈ Finset.range (modelOrder a),
        D.solvedRadius k a ^ (i + 1) * ‖D.step k‖ ^ (p - (i + 1) + 1) /
          (i + 1).factorial := by
  classical
  have hk1 : k + 1 ≤ N := by omega
  have hx : D.point (k + 1) = D.point k + D.step k := by
    rw [h.modelTrace.point_update k hk, ite_eq_left ha]
  have hδ : D.radius (k + 1) = D.solvedRadius k := by
    rw [h.radius_update k hk, ite_eq_left ha]
  have hfail : ∃ a, ε a * D.radius (k + 1) a ^ modelOrder a /
      (modelOrder a).factorial < TaylorModel.constrainedCriticality f (modelOrder a) X
        (D.point (k + 1)) (D.radius (k + 1) a) := by
    by_contra hn
    apply hnot
    exact Or.inl ⟨h.point_mem hk1, h.radius_mem hk1, fun a =>
      not_lt.mp (fun hh => hn ⟨a, hh⟩)⟩
  obtain ⟨a, hfailing⟩ := hfail
  rw [hx, hδ] at hfailing
  have hm := h.step_two k hk.le (h.continues k hk)
  have hq := P.order_le
  have haj : modelOrder a ≤ p := by unfold modelOrder; omega
  have hlegal := hm.radius_mem a
  have hδ0 := hlegal.1
  have he := TaylorModel.constrainedCriticality_le_regularized_model_add_error f hf haj
    (zero_le_one.trans hL) (h.modelTrace.updates.pos hk.le).le hlegal.1.le hlip hX
    (by simpa only [hx] using h.point_mem hk1)
  have hmc := hm.criticality P.zeta_pos hs a
  have hsum : 0 ≤ ∑ i ∈ Finset.range (modelOrder a),
      D.solvedRadius k a ^ (i + 1) * ‖D.step k‖ ^ (p - (i + 1) + 1) /
        (i + 1).factorial := Finset.sum_nonneg fun _ _ => by positivity
  have hc := mul_le_mul_of_nonneg_right
    (add_le_add_left (h.parameter_le hf hL hlip hk.le) L) hsum
  refine ⟨a, ?_⟩
  have hid : (1 - P.theta) * ε a * D.solvedRadius k a ^ modelOrder a /
      (modelOrder a).factorial = ε a * D.solvedRadius k a ^ modelOrder a /
        (modelOrder a).factorial - P.theta * ε a * D.solvedRadius k a ^ modelOrder a /
          (modelOrder a).factorial := by ring
  rw [hid]
  linarith

end Run
end ConstrainedRegularization
