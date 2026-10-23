import Numlib.Optimization.Regularization.Universal.Threshold

/-!
# Universal regularization parameter bounds

Actual update intervals and trial failures give the accuracy-dependent cap.
The fixed cap constants precede every accuracy request.
-/
namespace UniversalRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact first-order threshold in the source maximum. -/
noncomputable def firstThreshold {p : ℕ} (P : Settings p) (H β ε : ℝ) : ℝ :=
  max (P.theta1 * Real.finiteFactorial (P.r - 1))
    (thresholdCoefficient P H β 1 * ε ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1)))

/-- The exact second-order threshold, used only when that test is enabled. -/
noncomputable def secondThreshold {p : ℕ} (P : Settings p) (H β ε : ℝ) : ℝ :=
  max (P.theta2 * Real.finiteFactorial (P.r - 2))
    (thresholdCoefficient P H β 2 * ε ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 2)))

/-- Both active accuracy thresholds, with no artificial lower safeguard. -/
noncomputable def accuracyThreshold {p : ℕ} (P : Settings p) (H β ε1 : ℝ)
    (ε2 : Option ℝ) : ℝ :=
  match ε2 with
  | none => firstThreshold P H β ε1
  | some e => max (firstThreshold P H β ε1) (secondThreshold P H β e)

/-- A source threshold is enough for an actual nonterminal trial to be very successful. -/
theorem Run.very_successful_of_threshold {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε1 : ℝ} {ε2 : Option ℝ} {D : Data E} {N k : ℕ}
    (h : Run f P ε1 ε2 D N) (hk : k < N)
    (ha2 : ∀ e ∈ ε2, 2 < (p : ℝ) + β)
    (hcap : accuracyThreshold P H β ε1 ε2 ≤ D.parameter k) :
    P.eta2 ≤ ratio f p D k ∧ LengthChecks f P ε2 D k := by
  have hfirst : firstThreshold P H β ε1 ≤ D.parameter k := by
    cases ε2 with
    | none => exact hcap
    | some e => exact (le_max_left _ _).trans hcap
  have hsecond : ∀ e ∈ ε2, secondThreshold P H β e ≤ D.parameter k := by
    intro e he
    have heq : ε2 = some e := Option.mem_def.mp he
    rw [heq] at hcap
    exact (le_max_right _ _).trans hcap
  have hκ := (h.step_test k hk).threshold_of_trial_failure hf hH hβ hβ1 hholder ha har
    (h.parameter_pos hk.le) h.accuracy1_pos (fun e he => (h.accuracy2 e he).1)
    (h.trial_failure k hk) (fun e he => (h.accuracy2 e he).2.2) ha2 hfirst hsecond
  exact (h.step_test k hk).very_successful hf hH hβ hβ1 hholder ha har
    (h.parameter_pos hk.le) (fun e he => (h.accuracy2 e he).2.2)
    (fun e he => (ha2 e he).le) ((le_max_left _ _).trans hfirst)
    (fun e he => (le_max_left _ _).trans (hsecond e he)) hκ

/-- The actual update intervals alone give the upper multiplicative factor. -/
theorem Run.parameter_succ_le {p : ℕ} {P : Settings p} {f : E → ℝ}
    {ε1 : ℝ} {ε2 : Option ℝ} {D : Data E} {N k : ℕ}
    (h : Run f P ε1 ε2 D N) (hk : k < N) :
    D.parameter (k + 1) ≤ P.gamma3 * D.parameter k := by
  have hp := h.parameter_pos hk.le
  have hu := h.parameter_update k hk
  split_ifs at hu with hv hs
  · exact hu.2.trans (by nlinarith [P.gamma2_gt,P.gamma23])
  · exact hu.2.trans (mul_le_mul_of_nonneg_right P.gamma23.le hp.le)
  · exact hu.2

/-- Every actual nonterminal prefix has the exact accuracy-dependent source cap. -/
theorem Run.parameter_le {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε1 : ℝ} {ε2 : Option ℝ} {D : Data E} {N k : ℕ}
    (h : Run f P ε1 ε2 D N) (hk : k ≤ N)
    (ha2 : ∀ e ∈ ε2, 2 < (p : ℝ) + β) :
    D.parameter k ≤ max P.sigmaInitial (P.gamma3 * accuracyThreshold P H β ε1 ε2) := by
  induction k with
  | zero => rw [h.initial_parameter]; exact le_max_left _ _
  | succ k ih =>
    have hkN : k < N := by omega
    by_cases hc : accuracyThreshold P H β ε1 ε2 ≤ D.parameter k
    · have hv := h.very_successful_of_threshold hf hH hβ hβ1 hholder ha har hkN ha2 hc
      have hu := h.parameter_update k hkN
      rw [ite_eq_left hv] at hu
      exact hu.2.trans (ih hkN.le)
    · exact (h.parameter_succ_le hkN).trans
        ((mul_le_mul_of_nonneg_left (le_of_not_ge hc)
          (by linarith [P.gamma2_gt,P.gamma23])).trans (le_max_right _ _))

/-- The fixed first-order cap constant is independent of requested accuracies. -/
noncomputable def uniformCapOne {p : ℕ} (P : Settings p) (H β : ℝ) : ℝ :=
  max P.sigmaInitial (max (P.gamma3 * (P.theta1 * Real.finiteFactorial (P.r - 1)))
    (P.gamma3 * thresholdCoefficient P H β 1))

/-- The fixed cap when both derivative tests are enabled. -/
noncomputable def uniformCapTwo {p : ℕ} (P : Settings p) (H β : ℝ) : ℝ :=
  max (uniformCapOne P H β)
    (max (P.gamma3 * (P.theta2 * Real.finiteFactorial (P.r - 2)))
      (P.gamma3 * thresholdCoefficient P H β 2))

/-- Accuracy powers in the parameter cap are at least one. -/
theorem one_le_accuracy_power {ε a r j : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hja : j < a) (har : a ≤ r) : 1 ≤ ε ^ ((a - r) / (a - j)) := by
  have he : (a - r) / (a - j) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr har) (sub_pos.mpr hja).le
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 he

/-- A finite maximum of scaled terms is bounded by a common factor at least one. -/
theorem max_scaled_le {a b c u U : ℝ} (ha : a ≤ U) (hb : b ≤ U) (hc : c ≤ U)
    (hU : 0 ≤ U) (hu : 1 ≤ u) : max a (max b (c * u)) ≤ U * u := by
  have hmul : U ≤ U * u := by nlinarith
  exact max_le (ha.trans hmul) (max_le (hb.trans hmul)
    (mul_le_mul_of_nonneg_right hc (by linarith)))

/-- The first-order cap is at most its fixed constant times the single accuracy power. -/
theorem Run.parameter_le_uniform_one {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 1 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε : ℝ} {D : Data E} {N k : ℕ} (h : Run f P ε none D N) (hk : k ≤ N) :
    D.parameter k ≤ uniformCapOne P H β *
      ε ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1)) := by
  have hg : 0 ≤ P.gamma3 := by linarith [P.gamma2_gt,P.gamma23]
  have hcap := h.parameter_le hf hH hβ hβ1 hholder ha har hk (by simp)
  simp only [accuracyThreshold,firstThreshold,mul_max_of_nonneg _ _ hg] at hcap
  rw [←mul_assoc P.gamma3 (thresholdCoefficient P H β 1)] at hcap
  change D.parameter k ≤ uniformCapOne P H β * _
  unfold uniformCapOne
  refine hcap.trans (max_scaled_le (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
    (P.sigmaInitial_pos.le.trans (le_max_left _ _)) ?_)
  exact one_le_accuracy_power h.accuracy1_pos h.accuracy1_le ha har
/-- The two-test cap has the source maximum of the two accuracy powers. -/
theorem Run.parameter_le_uniform_two {p : ℕ} {P : Settings p} {f : E → ℝ}
    (hf : ContDiff ℝ p f) {H β : ℝ} (hH : 0 ≤ H) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hholder : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ H * ‖y - z‖ ^ β)
    (ha : 2 < (p : ℝ) + β) (har : (p : ℝ) + β ≤ P.r)
    {ε1 ε2 : ℝ} {D : Data E} {N k : ℕ} (h : Run f P ε1 (some ε2) D N)
    (hk : k ≤ N) :
    D.parameter k ≤ uniformCapTwo P H β *
      max (ε1 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1)))
        (ε2 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 2))) := by
  let u1 := ε1 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 1))
  let u2 := ε2 ^ (((p : ℝ) + β - P.r) / ((p : ℝ) + β - 2))
  let u := max u1 u2
  let U := uniformCapTwo P H β
  have hu1 : 1 ≤ u1 := one_le_accuracy_power h.accuracy1_pos h.accuracy1_le
    (by linarith) har
  have hu2 : 1 ≤ u2 := one_le_accuracy_power
    (h.accuracy2 ε2 (by simp)).1 (h.accuracy2 ε2 (by simp)).2.1 ha har
  have hu : 1 ≤ u := hu1.trans (le_max_left _ _)
  have hU1 : uniformCapOne P H β ≤ U := le_max_left _ _
  have hU0 : P.sigmaInitial ≤ U := (le_max_left _ _).trans hU1
  have hUpos : 0 ≤ U := P.sigmaInitial_pos.le.trans hU0
  have hUU : U ≤ U * u := by nlinarith
  have hg : 0 ≤ P.gamma3 := by linarith [P.gamma2_gt,P.gamma23]
  have hcap := h.parameter_le hf hH hβ hβ1 hholder (by linarith) har hk
    (fun _ _ => ha)
  simp only [accuracyThreshold,firstThreshold,secondThreshold,
    mul_max_of_nonneg _ _ hg] at hcap
  refine hcap.trans (max_le (hU0.trans hUU) (max_le (max_le ?_ ?_) (max_le ?_ ?_)))
  · exact (((le_max_left _ _).trans (le_max_right _ _)).trans hU1).trans hUU
  · rw [←mul_assoc]
    have hc : P.gamma3 * thresholdCoefficient P H β 1 ≤ U :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans hU1
    exact mul_le_mul hc (le_max_left u1 u2) (by linarith) hUpos
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hUU
  · rw [←mul_assoc]
    have hc : P.gamma3 * thresholdCoefficient P H β 2 ≤ U :=
      (le_max_right _ _).trans (le_max_right _ _)
    exact mul_le_mul hc (le_max_right u1 u2) (by linarith) hUpos
end UniversalRegularization
