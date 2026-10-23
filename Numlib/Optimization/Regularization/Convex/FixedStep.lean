import Numlib.Optimization.Regularization.Convex.FirstOrderComplexity

/-!
# Actual first-order error bounds for fixed-tolerance constrained models

The fixed model tolerance of ARp-CC and the step-scaled tolerance of ARp1-CC
are distinct primitive rules. The true model derivative error transfers the
fixed tolerance to endpoint criticality, yielding the exact first-order step
bound whenever the endpoint still fails its objective test.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  {p : ℕ} {f : E → ℝ} {C S : Set E} {P : Settings p}
  {ε L : ℝ} {D : Data E} {N : ℕ}

omit [ProperSpace E] in
/-- Every actual fixed-tolerance parameter is bounded on the source convex domain. -/
theorem Run.parameter_le (h : Run f C P ε D N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i ≤ N) : D.parameter i ≤ parameterCap P L := by
  have hh := h.modelTrace.parameter_le_on hS hCS hC hf hL hlip
    (fun j hj => h.mem hj.le) h.feasible_trial hi
  rwa [h.initial_parameter] at hh

/-- The genuine constrained endpoint criticality is bounded by the fixed
model tolerance plus the actual model derivative error. -/
theorem Run.trial_criticality_le (h : Run f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) :
    constrainedCriticality f 1 C (D.point i + D.step i) 1 ≤
      P.theta * ε + (L + D.parameter i) / p.factorial * ‖D.step i‖ ^ p := by
  have hb := constrainedCriticality_one_le_model (f := f)
    (m := model f p (D.point i) (D.parameter i)) hclosed (h.feasible_trial i hi)
  have he := norm_model_first_error_le_on P.order_pos hS hCS hC hf hL
    (h.modelTrace.updates.pos hi.le).le hlip (h.mem hi.le) (h.feasible_trial i hi)
    (h.modelTrace.step_ne_zero hi)
  exact hb.trans (add_le_add (h.model_test i hi) he)

/-- At an accepted endpoint whose true criticality exceeds the fixed tolerance,
the actual step satisfies the strict first-order source bound(6.2.13). -/
theorem Run.step_lower_of_endpoint_failure (h : Run f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : P.eta1 ≤ D.ratio i)
    (hfail : ε < constrainedCriticality f 1 C (D.point (i + 1)) 1) :
    p.factorial * (1 - P.theta) / (L + parameterCap P L) * ε < ‖D.step i‖ ^ p := by
  have hh := h.trial_criticality_le hclosed hS hCS hC hf hL.le hlip hi
  rw [←h.modelTrace.successful_point hi hs] at hh
  have hcap := h.parameter_le hS hCS hC hf hL.le hlip hi.le
  have hfac : (0 : ℝ) < p.factorial := by positivity
  have hcap0 := P.sigmaMin_pos.trans_le (P.sigmaMin_le_initial.trans
    (le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))))
  have hden : 0 < L + parameterCap P L := by positivity
  have hb : (L + D.parameter i) / p.factorial * ‖D.step i‖ ^ p ≤
      (L + parameterCap P L) / p.factorial * ‖D.step i‖ ^ p :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (by linarith : L + D.parameter i ≤ L + parameterCap P L)
      hfac.le) (pow_nonneg (norm_nonneg _) _)
  have he : (1 - P.theta) * ε <
      (L + parameterCap P L) / p.factorial * ‖D.step i‖ ^ p := by linarith
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hden).mpr
  have he' := (lt_div_iff₀ hfac).mp (by
    simpa only [div_mul_eq_mul_div] using he)
  nlinarith

/-- A sufficiently large actual endpoint criticality transfers a fixed model
tolerance to a relative criticality bound, without changing the primitive run. -/
theorem Run.relative_step_lower (h : Run f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : P.eta1 ≤ D.ratio i)
    (hlarge : ε ≤ constrainedCriticality f 1 C (D.point (i + 1)) 1) :
    p.factorial * (1 - P.theta) / (L + parameterCap P L) *
      constrainedCriticality f 1 C (D.point (i + 1)) 1 ≤ ‖D.step i‖ ^ p := by
  have hh := h.trial_criticality_le hclosed hS hCS hC hf hL.le hlip hi
  rw [←h.modelTrace.successful_point hi hs] at hh
  have hcap := h.parameter_le hS hCS hC hf hL.le hlip hi.le
  have hfac : (0 : ℝ) < p.factorial := by positivity
  have hcap0 := P.sigmaMin_pos.trans_le (P.sigmaMin_le_initial.trans
    (le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))))
  have hden : 0 < L + parameterCap P L := by positivity
  have hθ : 0 < P.theta := by have := P.theta_lower; have := P.tau_pos; linarith
  have hm := mul_le_mul_of_nonneg_left hlarge hθ.le
  have hb : (L + D.parameter i) / p.factorial * ‖D.step i‖ ^ p ≤
      (L + parameterCap P L) / p.factorial * ‖D.step i‖ ^ p :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (by linarith : L + D.parameter i ≤ L + parameterCap P L)
      hfac.le) (pow_nonneg (norm_nonneg _) _)
  have he : (1 - P.theta) * constrainedCriticality f 1 C (D.point (i + 1)) 1 ≤
      (L + parameterCap P L) / p.factorial * ‖D.step i‖ ^ p := by linarith
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  have he' := (le_div_iff₀ hfac).mp (by
    simpa only [div_mul_eq_mul_div] using he)
  nlinarith

/-- The actual fixed-model relative decrease coefficient includes the source
factorial penalty and the strict model-tolerance margin. -/
noncomputable def fixedDecreaseCoefficient {p : ℕ} (P : Settings p) (L : ℝ) : ℝ :=
  P.eta1 * P.sigmaMin / (p + 1).factorial *
    (p.factorial * (1 - P.theta) / (L + parameterCap P L)) ^
      (((p + 1 : ℕ) : ℝ) / p)

/-- Fixed legal settings give a strictly positive relative decrease coefficient. -/
theorem fixedDecreaseCoefficient_pos {p : ℕ} (P : Settings p) {L : ℝ} (hL : 0 < L) :
    0 < fixedDecreaseCoefficient P L := by
  have hcap0 := P.sigmaMin_pos.trans_le (P.sigmaMin_le_initial.trans
    (le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))))
  have htheta := sub_pos.mpr P.theta_lt_one
  have hη := P.eta1_pos
  have hσ := P.sigmaMin_pos
  have hm : 0 < parameterCap P L := hcap0
  unfold fixedDecreaseCoefficient
  positivity

/-- At an accepted endpoint above the fixed model tolerance, the actual
objective drop bounds the endpoint criticality to the correct power. -/
theorem Run.relative_successful_decrease (h : Run f C P ε D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hs : P.eta1 ≤ D.ratio i)
    (hlarge : ε ≤ constrainedCriticality f 1 C (D.point (i + 1)) 1) :
    fixedDecreaseCoefficient P L * constrainedCriticality f 1 C (D.point (i + 1)) 1 ^
      (((p + 1 : ℕ) : ℝ) / p) ≤ f (D.point i) - f (D.point (i + 1)) := by
  have hcap0 := P.sigmaMin_pos.trans_le (P.sigmaMin_le_initial.trans
    (le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))))
  have htheta := sub_pos.mpr P.theta_lt_one
  exact h.modelTrace.decrease_of_step_lower hi hs P.order_pos
    (by positivity : 0 ≤ p.factorial * (1 - P.theta) / (L + parameterCap P L))
    (constrainedCriticality_nonneg f 1 hclosed (h.mem (by omega)) zero_le_one)
    (h.relative_step_lower hclosed hS hCS hC hf hL hlip hi hs hlarge)

end ConvexRegularization
