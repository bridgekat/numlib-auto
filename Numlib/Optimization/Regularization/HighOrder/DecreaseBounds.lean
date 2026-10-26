import Numlib.Optimization.Regularization.HighOrder.RunBudget

/-!
# Corrected model and function decrease for exact regularization

The sharp accuracy rates apply to every trial whose actual candidate fails true
criticality at the solver radii. This explicit guard replaces nontermination,
which only concerns computed relative tests. The constants use the genuine
parameter cap and the safe common radius coefficient, before all accuracies.
-/

namespace HighOrderRegularization
open InexactTrustRegion HighOrderStep
open InexactRegularization (rootStepExponent evaluationExponent pow_lower_of_root_step)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

omit [FiniteDimensional ℝ E] in
/-- The actual objective ratio transfers any computed prediction floor to
true objective decrease at an accepted exact trial. -/
theorem function_decrease_ge_model (h : Run f P ε D N) {k : ℕ} (hk : k < N)
    (ha : P.eta1 ≤ D.ratio k) :
    P.eta1 * TaylorModel.decrement f p (D.point k) (D.step k) ≤
      f (D.point k) - f (D.point (k + 1)) := by
  have hr := ha
  rw [h.modelTrace.ratio k hk, HighOrderRegularization.ratio_eq] at hr
  have hd := (le_div_iff₀ (h.modelTrace.denominator_pos hk)).mp hr
  simpa only [h.modelTrace.point_update k hk, ite_eq_left ha] using hd

/-- A candidate failing true criticality forces a sharp step-length rate,
including rejected trials. All model tests and radii are those actually computed. -/
theorem exists_root_step_lower_candidate (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N)
    (hnot : ¬OptimalityAt f ε (D.point k + D.step k) (D.solvedRadius k)) :
    ∃ a, rootStepCoefficient P L (parameterCap P L) (modelOrder a) *
      (ε a) ^ rootStepExponent p q (modelOrder a) ≤ ‖D.step k‖ := by
  let S := parameterCap P L
  let κ := regularizationRadiusCoefficient P.zeta P.theta L L S q
  have hS : 0 ≤ S := (parameterCap_pos P L).le
  have hκ := regularizationRadiusCoefficient_mem P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one hL hL hS q
  have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
  have hm := h.step_two k hk.le (h.continues k hk)
  obtain ⟨a, ha⟩ := HighOrderRegularization.criticality_obstruction P.order_le f hf hL
    (h.modelTrace.updates.pos hk.le).le (h.parameter_le hf hL (hlip p hp le_rfl) hk.le)
    P.theta_pos.le (hlip p hp le_rfl) (D.point k) (D.step k) ε (D.solvedRadius k)
    (fun a => ⟨h.accuracy_pos a, h.accuracy_le_one a⟩) hm.radius_mem
    (fun hs a => hm.criticality P.zeta_pos hs a)
    (fun hh => hnot ⟨hm.radius_mem, hh⟩)
  have hj : 1 ≤ modelOrder a := by unfold modelOrder; omega
  have hjq : modelOrder a ≤ q := by unfold modelOrder; omega
  have hunit : q ≤ 2 → D.solvedRadius k a = 1 := fun hq2 =>
    hm.unit_radius a (hjq.trans hq2)
  have hfloor : ‖D.step k‖ ≤ 1 → κ * ε a ≤ D.solvedRadius k a := by
    intro hs
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (h.accuracy_pos a).le).trans
      (h.solved_radius_floor hf hL hlip hk.le (h.continues k hk) hs a)
  have hh := lower_of_obstruction hj hjq P.order_le P.theta_pos P.theta_lt_one
    (by linarith : 1 ≤ L + S) hκ.1.le hκ.2 (min_le_right _ _)
    (h.accuracy_pos a).le (h.accuracy_le_one a) (hm.radius_mem a).1
    (norm_nonneg _) hunit hfloor ha
  refine ⟨a, ?_⟩
  by_cases hq2 : q ≤ 2
  · simpa only [rootStepCoefficient, rootStepExponent, ite_eq_left hq2] using hh
  · simpa only [rootStepCoefficient, rootStepExponent, ite_eq_right hq2] using hh

/-- The actual Taylor decrement has the two sharp source rates whenever the
trial candidate fails true criticality. Acceptance is not required. -/
theorem model_decrease_uniform_candidate (h : Run f P ε D N) (hf : ContDiff ℝ p f)
    {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N)
    (hnot : ¬OptimalityAt f ε (D.point k + D.step k) (D.solvedRadius k)) :
    commonDecreaseCoefficient P L (parameterCap P L) / P.eta1 * accuracyFactor P ε ≤
      TaylorModel.decrement f p (D.point k) (D.step k) := by
  obtain ⟨a, ha⟩ := h.exists_root_step_lower_candidate hf hL hlip hk hnot
  have hr := rootStepCoefficient_pos P hL (parameterCap_pos P L).le (modelOrder a)
  have hp := pow_lower_of_root_step (n := p + 1) hr.le (h.accuracy_pos a).le ha
  have hbase : 0 ≤ P.eta1 * P.sigmaMin / ((p + 1).factorial : ℝ) :=
    div_nonneg (mul_nonneg P.eta1_pos.le P.sigmaMin_pos.le)
    (Nat.cast_nonneg _)
  have hscale := mul_le_mul_of_nonneg_left hp hbase
  have hc := mul_le_mul (commonDecreaseCoefficient_le P L (parameterCap P L) a)
    (accuracyFactor_le P ε a) (accuracyFactor_pos P h.accuracy_pos).le
    (show 0 ≤ orderDecreaseCoefficient P L (parameterCap P L) a by
      unfold orderDecreaseCoefficient; positivity)
  have hm := penalty_le_decrement f p (D.point k) (D.step k) (D.parameter k)
    (h.step_two k hk.le (h.continues k hk)).nonincrease
  have hσ := h.modelTrace.updates.min_le hk.le
  have hpen := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hσ (Nat.cast_nonneg (p + 1).factorial))
    (pow_nonneg (norm_nonneg (D.step k)) (p + 1))
  have hb : commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε ≤
      P.eta1 * TaylorModel.decrement f p (D.point k) (D.step k) := by
    apply hc.trans
    apply le_trans _ (mul_le_mul_of_nonneg_left (hpen.trans hm) P.eta1_pos.le)
    convert hscale using 1
    · unfold orderDecreaseCoefficient evaluationExponent
      ring
    · ring
  have hd : commonDecreaseCoefficient P L (parameterCap P L) * accuracyFactor P ε /
      P.eta1 ≤ TaylorModel.decrement f p (D.point k) (D.step k) :=
    (div_le_iff₀ P.eta1_pos).2 (by convert hb using 1; ring)
  convert hd using 1
  ring

/-- Accepted trials before the next true certificate obey both corrected
model and objective bounds, with the same positive accuracy-independent coefficient. -/
theorem model_function_decrease_before_certificate (h : Run f P ε D N)
    (hf : ContDiff ℝ p f) {L : ℝ} (hL : 1 ≤ L)
    (hlip : ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i f y - iteratedFDeriv ℝ i f z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) (ha : P.eta1 ≤ D.ratio k)
    (hnot : ¬TargetAt f P ε D (k + 1)) :
    let c := commonDecreaseCoefficient P L (parameterCap P L) / P.eta1
    0 < c ∧ c * accuracyFactor P ε ≤ TaylorModel.decrement f p (D.point k) (D.step k) ∧
      P.eta1 * c * accuracyFactor P ε ≤ f (D.point k) - f (D.point (k + 1)) := by
  have hx : D.point (k + 1) = D.point k + D.step k := by
    rw [h.modelTrace.point_update k hk, ite_eq_left ha]
  have hδ : D.radius (k + 1) = D.solvedRadius k := by
    rw [h.radius_update k hk, ite_eq_left ha]
  have hn : ¬OptimalityAt f ε (D.point k + D.step k) (D.solvedRadius k) := by
    intro hh
    apply hnot
    exact Or.inl (by simpa only [hx, hδ] using hh)
  refine ⟨div_pos (commonDecreaseCoefficient_pos P hL (parameterCap_pos P L).le)
    P.eta1_pos, h.model_decrease_uniform_candidate hf hL hlip hk hn, ?_⟩
  convert h.function_decrease_uniform hf hL hlip hk ha hnot using 1
  field_simp [P.eta1_pos.ne']

end Run
end HighOrderRegularization
