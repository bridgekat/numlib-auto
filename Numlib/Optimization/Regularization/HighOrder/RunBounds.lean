import Numlib.Optimization.Regularization.HighOrder.CriticalityRun
import Numlib.Optimization.Regularization.HighOrder.CriticalityObstruction

/-!
# Derived analytic bounds for exact high-order regularization executions

Sharp actual model derivatives and primitive update rules imply parameter
caps, successful-step radius floors and the true-criticality obstruction.
All constants are fixed independently of the requested accuracies.
-/

namespace HighOrderRegularization
open InexactTrustRegion
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The source parameter cap depends only on fixed settings and smoothness. -/
noncomputable def parameterCap {p q : ℕ} (P : Settings p q) (L : ℝ) : ℝ :=
  max P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))

/-- The fixed cap is positive because it includes the positive initial parameter. -/
theorem parameterCap_pos {p q : ℕ} (P : Settings p q) (L : ℝ) : 0 < parameterCap P L :=
  (P.sigmaMin_pos.trans_le P.sigmaMin_le_initial).trans_le (le_max_left _ _)

/-- Lipschitz bounds on the preceding actual derivative control every model
tensor of order at least two, without requiring a bound on the gradient. -/
theorem tensor_bound_of_derivative_lipschitz (f : E → ℝ) {p : ℕ} {L : ℝ}
    (hL : 0 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i < p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    (x : E) : ∀ i, 2 ≤ i → i ≤ p → ‖ftaylorSeries ℝ f x i‖ ≤ L := by
  intro i hi hip
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  change ‖iteratedFDeriv ℝ (j + 1) f x‖ ≤ L
  rw [← norm_fderiv_iteratedFDeriv]
  exact norm_fderiv_le_of_lip' ℝ hL
    (Filter.Eventually.of_forall (fun y => hlip j (by omega) (by omega) y x))

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Actual objective ratios and parameter intervals derive the uniform cap. -/
theorem parameter_le (h : Run f P ε D N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k ≤ N) : D.parameter k ≤ parameterCap P L := by
  simpa only [parameterCap, h.initial_parameter] using
    h.modelTrace.parameter_le hf (zero_le_one.trans hL) hlip hk

end Run
end General

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- Every short actual model computation has the printed floor with the fixed
parameter cap. This follows from its changing-candidate halving tests. -/
theorem solved_radius_floor (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k ≤ N) (hselected : D.selected k ≠ none) (hs : ‖D.step k‖ ≤ 1)
    (a : Fin q) :
    P.zeta * P.theta / (8 * (3 * L + parameterCap P L)) * ε a ≤ D.solvedRadius k a := by
  have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
  have hσ := h.modelTrace.updates.pos hk
  have hcap := h.parameter_le hf hL (hlip p hp le_rfl) hk
  have hA := tensor_bound_of_derivative_lipschitz f (zero_le_one.trans hL)
    (fun i hi hip => hlip i hi hip.le) (D.point k)
  have horder : ∀ a : Fin q, 0 < modelOrder a ∧ modelOrder a ≤ p := by
    have hqp := P.order_le
    intro a
    unfold modelOrder
    constructor <;> omega
  have hb := (h.step_two k hk hselected).radius_lower_penalized
    (ftaylorSeries ℝ f (D.point k)) hσ.le hL hA horder P.theta_pos
    P.theta_lt_one.le P.zeta_le_one (fun b => ⟨h.accuracy_pos b, h.accuracy_le_one b⟩) hs a
  have hratio : P.zeta * P.theta / (8 * (3 * L + parameterCap P L)) ≤
      P.zeta * P.theta / (8 * (3 * L + D.parameter k)) :=
    div_le_div_of_nonneg_left (mul_pos P.zeta_pos P.theta_pos).le
      (by linarith) (by linarith)
  exact (mul_le_mul_of_nonneg_right hratio (h.accuracy_pos a).le).trans hb

/-- Actual accepted point/radius updates and the model test imply the source
weighted obstruction whenever the next inherited radii fail true optimality. -/
theorem criticality_obstruction (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hnot : ¬TargetAt f P ε D (k + 1)) :
    ∃ a, (1 - P.theta) * ε a * D.radius (k + 1) a ^ modelOrder a /
        (modelOrder a).factorial ≤
      (L + parameterCap P L) * ∑ i ∈ Finset.range (modelOrder a),
        D.radius (k + 1) a ^ (i + 1) * ‖D.step k‖ ^ (p - (i + 1) + 1) /
          (i + 1).factorial := by
  have hk1 : k + 1 ≤ N := by omega
  have hx : D.point (k + 1) = D.point k + D.step k := by
    rw [h.modelTrace.point_update k hk, ite_eq_left haccepted]
  have hδ : D.radius (k + 1) = D.solvedRadius k := by
    rw [h.radius_update k hk, ite_eq_left haccepted]
  apply HighOrderRegularization.criticality_obstruction P.order_le f hf hL
    (h.modelTrace.updates.pos hk.le).le (h.parameter_le hf hL hlip hk.le) P.theta_pos.le
    hlip (D.point k) (D.step k) ε (D.radius (k + 1))
    (fun a => ⟨h.accuracy_pos a, h.accuracy_le_one a⟩) (h.radius_mem hk1)
  · intro hs a
    rw [hδ]
    exact (h.step_two k hk.le (h.continues k hk)).criticality P.zeta_pos hs a
  · intro hh
    apply hnot
    exact Or.inl ⟨h.radius_mem hk1, by simpa only [hx] using hh⟩

end Run
end Hilbert
end HighOrderRegularization
