import Numlib.Optimization.Regularization.HighOrder.Parameter
import Numlib.Analysis.Calculus.TaylorModel.Perturbation
import Numlib.Optimization.EvaluationComplexity.TrialParameterBounds

/-!
# Parameter bounds with guarded implicit derivative accuracy

Accuracy requests decrease only at accuracy-improvement iterations. The literal
short-step guard in Algorithm 13.1.2 therefore yields a uniform relative error
coefficient `max(κs,κh)`, rather than the printed `κs`. Every derivative order
through `p` is checked, as explicitly required in equation (13.1.46).
-/

namespace InexactRegularization
open TaylorModel ModelDecrease EvaluationComplexity Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual computed Taylor polynomial plus its norm-power regularizer. -/
noncomputable def model (A : FormalMultilinearSeries ℝ E ℝ) (p : ℕ)
    (σ : ℝ) (s : E) : ℝ := penalized (ofJet A p) p σ s

/-- The actual objective-based ratio for a computed Taylor jet. -/
noncomputable def ratio (f : E → ℝ) (A : FormalMultilinearSeries ℝ E ℝ)
    (p : ℕ) (x s : E) : ℝ := (f x - f (x + s)) / jetDecrement A p s

/-- Fixed oracle constants, initial request cap and multiplicative accuracy updates. -/
structure OracleSettings (p : ℕ) where
  stepCoefficient : ℝ
  stepCoefficient_pos : 0 < stepCoefficient
  initialCap : ℝ
  initialCap_nonneg : 0 ≤ initialCap
  errorBound : ℝ
  errorBound_nonneg : 0 ≤ errorBound
  errorCoefficient : ℕ → ℝ
  errorCoefficient_nonneg : ∀ a, 1 ≤ a → a ≤ p → 0 ≤ errorCoefficient a
  errorCoefficient_le : ∀ a, 1 ≤ a → a ≤ p → errorCoefficient a ≤ errorBound
  reduction : ℝ
  reduction_pos : 0 < reduction
  reduction_lt_one : reduction < 1

/-- Shared model, oracle and update components of IDA and EDA regularization,
retaining the short-step
accuracy guard. Accuracy-only steps preserve the point and regularization parameter.
The fields contain primitive checks and updates, without a parameter upper bound. -/
structure OracleTrace (f : E → ℝ) (p : ℕ) (O : OracleSettings p)
    (A : ℕ → FormalMultilinearSeries ℝ E ℝ) (T : Set ℕ)
    (x d s : ℕ → E) (accuracy : ℕ → ℕ → ℝ) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop where
  order_pos : 0 < p
  updates : TrialRegularizationUpdates T σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  initial_accuracy : ∀ a, 1 ≤ a → a ≤ p → accuracy 0 a ∈ Icc 0 O.initialCap
  accuracy_trial : ∀ i < N, i ∈ T → ∀ a, 1 ≤ a → a ≤ p →
    accuracy (i + 1) a = accuracy i a
  accuracy_improvement : ∀ i < N, i ∉ T → ∀ a, 1 ≤ a → a ≤ p →
    accuracy (i + 1) a = O.reduction * accuracy i a
  oracle : ∀ i < N, i ∈ T → ∀ a, 1 ≤ a → a ≤ p →
    ‖A i a - iteratedFDeriv ℝ a f (x i)‖ ≤ O.errorCoefficient a * accuracy i a
  short_request : ∀ i < N, i ∈ T → ‖s i‖ < 1 → ∀ a, 1 ≤ a → a ≤ p →
    accuracy i a ≤ O.stepCoefficient * ‖s i‖ ^ (p - a + 1)
  reference_improvement : ∀ i < N, i ∈ T →
    model (A i) p (σ i) (d i) < model (A i) p (σ i) 0
  comparison : ∀ i < N, i ∈ T →
    model (A i) p (σ i) (s i) ≤ model (A i) p (σ i) (d i)
  point_update : ∀ i < N, i ∈ T →
    x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i
  point_inactive : ∀ i < N, i ∉ T → x (i + 1) = x i

/-- The IDA model trace adds the exact objective constant and true objective
ratio to the shared guarded oracle and update rules. -/
structure ModelTrace (f : E → ℝ) (p : ℕ) (O : OracleSettings p)
    (A : ℕ → FormalMultilinearSeries ℝ E ℝ) (T : Set ℕ)
    (x d s : ℕ → E) (accuracy : ℕ → ℕ → ℝ) (σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop
    extends OracleTrace f p O A T x d s accuracy σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N where
  exact_value : ∀ i < N, i ∈ T → A i 0 (fun _ => 0) = f (x i)
  ratio : ∀ i < N, i ∈ T →
    ρ i = InexactRegularization.ratio f (A i) p (x i) (s i)

/-- The genuine computed decrement exceeds the actual model's norm-power penalty. -/
theorem penalty_lt_decrement {A : FormalMultilinearSeries ℝ E ℝ} {p : ℕ}
    {σ : ℝ} {d s : E} (hd : model A p σ d < model A p σ 0)
    (hs : model A p σ s ≤ model A p σ d) :
    σ / (p + 1).factorial * ‖s‖ ^ (p + 1) < jetDecrement A p s :=
  ModelDecrease.penalty_lt_decrement (ofJet A p) p σ s (hs.trans_lt hd)

/-- True Taylor remainder and actual tensor errors control the computed value
for arbitrary trial lengths, with no unit-ball restriction. -/
theorem value_error_le {f : E → ℝ} {p : ℕ} (hp : 0 < p) (hf : ContDiff ℝ p f)
    {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (A : FormalMultilinearSeries ℝ E ℝ) (x s : E)
    (hzero : A 0 (fun _ => 0) = f x)
    (herr : ∀ a, 1 ≤ a → a ≤ p →
      ‖A a - iteratedFDeriv ℝ a f x‖ ≤ K * ‖s‖ ^ (p - a + 1)) :
    |f (x + s) - ofJet A p s| ≤
      (L + 2 * ((p + 1).factorial : ℝ) * K) * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
  have ht := HighOrderRegularization.value_error_le hp hf hL hlip x s
  have he := norm_ofJet_sub_eval_le_power A f x s le_rfl hK hzero herr
  have htri : |f (x + s) - ofJet A p s| ≤
      |f (x + s) - eval f p x s| + ‖ofJet A p s - eval f p x s‖ := by
    simpa only [Real.norm_eq_abs, abs_sub_comm] using
      norm_sub_le_norm_sub_add_norm_sub (f (x + s)) (eval f p x s) (ofJet A p s)
  calc _ ≤ L * ‖s‖ ^ (p + 1) / (p + 1).factorial +
        2 * K * ‖s‖ ^ (p + 1) := htri.trans (add_le_add ht he)
    _ = _ := by field_simp

/-- The corrected source coefficient retains the large-step request cap. -/
noncomputable def parameterCoefficient {p : ℕ} (O : OracleSettings p) (L : ℝ) : ℝ :=
  2 * L + 4 * ((p + 1).factorial : ℝ) * max O.stepCoefficient O.initialCap * O.errorBound

/-- The printed coefficient is recovered when the initial cap is no larger
than the short-step coefficient. -/
theorem parameterCoefficient_eq_of_cap_le {p : ℕ} (O : OracleSettings p) (L : ℝ)
    (hcap : O.initialCap ≤ O.stepCoefficient) :
    parameterCoefficient O L =
      2 * L + 4 * ((p + 1).factorial : ℝ) * O.stepCoefficient * O.errorBound := by
  simp only [parameterCoefficient, max_eq_left hcap]

/-- The exact ratio error of a computed jet uses its exact constant coefficient. -/
theorem ratio_error_eq {f : E → ℝ} {A : FormalMultilinearSeries ℝ E ℝ}
    {p : ℕ} {x s : E} (hzero : A 0 (fun _ => 0) = f x)
    (hd : 0 < jetDecrement A p s) :
    |ratio f A p x s - 1| = |f (x + s) - ofJet A p s| / jetDecrement A p s := by
  have heq : f x - f (x + s) - jetDecrement A p s = -(f (x + s) - ofJet A p s) := by
    rw [jetDecrement, ofJet_zero, hzero]
    ring
  rw [ratio, div_sub_one hd.ne', heq, abs_div, abs_neg, abs_of_pos hd]

namespace OracleTrace
variable {f : E → ℝ} {p : ℕ} {O : OracleSettings p}
  {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ}
  {x d s : ℕ → E} {accuracy : ℕ → ℕ → ℝ} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ} {N : ℕ}

/-- Actual request updates preserve nonnegativity and the initial request cap. -/
theorem accuracy_mem_Icc (h : OracleTrace f p O A T x d s accuracy σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) {i : ℕ} (hi : i ≤ N)
    {a : ℕ} (ha : 1 ≤ a) (hap : a ≤ p) : accuracy i a ∈ Icc 0 O.initialCap := by
  classical
  induction i with
  | zero => exact h.initial_accuracy a ha hap
  | succ i ih =>
    have hp := ih (by omega)
    by_cases hT : i ∈ T
    · rw [h.accuracy_trial i (by omega) hT a ha hap]
      exact hp
    · rw [h.accuracy_improvement i (by omega) hT a ha hap]
      exact ⟨mul_nonneg O.reduction_pos.le hp.1,
        (mul_le_of_le_one_left hp.1 O.reduction_lt_one.le).trans hp.2⟩

/-- The literal short-step guard and the derived global request cap give the
corrected relative accuracy coefficient at every trial length. -/
theorem request_le (h : OracleTrace f p O A T x d s accuracy σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) {i : ℕ} (hi : i < N) (hT : i ∈ T)
    {a : ℕ} (ha : 1 ≤ a) (hap : a ≤ p) :
    accuracy i a ≤ max O.stepCoefficient O.initialCap * ‖s i‖ ^ (p - a + 1) := by
  by_cases hs : ‖s i‖ < 1
  · exact (h.short_request i hi hT hs a ha hap).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hs1 : 1 ≤ ‖s i‖ := le_of_not_gt hs
    have hp : 1 ≤ ‖s i‖ ^ (p - a + 1) := one_le_pow₀ hs1
    have hm : 0 ≤ max O.stepCoefficient O.initialCap :=
      O.initialCap_nonneg.trans (le_max_right _ _)
    exact (h.accuracy_mem_Icc hi.le ha hap).2.trans
      ((le_max_right _ _).trans (le_mul_of_one_le_right hm hp))

/-- Primitive oracle guarantees and guarded request checks imply actual tensor errors. -/
theorem tensor_error_le (h : OracleTrace f p O A T x d s accuracy σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) {i : ℕ} (hi : i < N) (hT : i ∈ T)
    {a : ℕ} (ha : 1 ≤ a) (hap : a ≤ p) :
    ‖A i a - iteratedFDeriv ℝ a f (x i)‖ ≤
      (max O.stepCoefficient O.initialCap * O.errorBound) * ‖s i‖ ^ (p - a + 1) := by
  have hh := h.oracle i hi hT a ha hap
  have hr := mul_le_mul_of_nonneg_left (h.request_le hi hT ha hap)
    (O.errorCoefficient_nonneg a ha hap)
  have hc := mul_le_mul_of_nonneg_right (O.errorCoefficient_le a ha hap)
    (show 0 ≤ max O.stepCoefficient O.initialCap * ‖s i‖ ^ (p - a + 1) by
      exact mul_nonneg (O.initialCap_nonneg.trans (le_max_right _ _)) (by positivity))
  exact hh.trans (hr.trans (by convert hc using 1; ring))

/-- A trial's actual computed prediction denominator is strictly positive. -/
theorem denominator_pos (h : OracleTrace f p O A T x d s accuracy σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) {i : ℕ} (hi : i < N) (hT : i ∈ T) :
    0 < jetDecrement (A i) p (s i) := by
  have hσ := h.updates.pos hi.le
  have hp := penalty_lt_decrement (h.reference_improvement i hi hT) (h.comparison i hi hT)
  exact (show 0 ≤ σ i / (p + 1).factorial * ‖s i‖ ^ (p + 1) by positivity).trans_lt hp

end OracleTrace

namespace ModelTrace
variable {f : E → ℝ} {p : ℕ} {O : OracleSettings p}
  {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ}
  {x d s : ℕ → E} {accuracy : ℕ → ℕ → ℝ} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ} {N : ℕ}

/-- The actual ratio error obeys the corrected common accuracy coefficient,
for both small and large trial steps. -/
theorem ratio_error_le (h : ModelTrace f p O A T x d s accuracy σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hT : i ∈ T) :
    |ρ i - 1| ≤
      (L + 2 * ((p + 1).factorial : ℝ) *
        (max O.stepCoefficient O.initialCap * O.errorBound)) / σ i := by
  let K := max O.stepCoefficient O.initialCap * O.errorBound
  have hK : 0 ≤ K := mul_nonneg
    (O.initialCap_nonneg.trans (le_max_right _ _)) O.errorBound_nonneg
  have hσ := h.updates.pos hi.le
  have hd := h.toOracleTrace.denominator_pos hi hT
  have hdec := (penalty_lt_decrement
    (h.reference_improvement i hi hT) (h.comparison i hi hT)).le
  have herr := value_error_le h.order_pos hf hL hK hlip (A i) (x i) (s i)
    (h.exact_value i hi hT) (fun a ha hap => h.toOracleTrace.tensor_error_le hi hT ha hap)
  rw [h.ratio i hi hT, InexactRegularization.ratio_error_eq (h.exact_value i hi hT) hd]
  apply (div_le_iff₀ hd).2
  have hC : 0 ≤ L + 2 * ((p + 1).factorial : ℝ) * K := by positivity
  have hm := mul_le_mul_of_nonneg_left hdec (div_nonneg hC hσ.le)
  have heq : ((L + 2 * ((p + 1).factorial : ℝ) * K) / σ i) *
      (σ i / (p + 1).factorial * ‖s i‖ ^ (p + 1)) =
      (L + 2 * ((p + 1).factorial : ℝ) * K) * ‖s i‖ ^ (p + 1) /
        (p + 1).factorial := by field_simp
  rw [heq] at hm
  exact herr.trans hm

/-- Reaching the corrected threshold forces a very successful actual trial. -/
theorem very_successful (h : ModelTrace f p O A T x d s accuracy σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hT : i ∈ T)
    (hlarge : parameterCoefficient O L / (1 - η₂) ≤ σ i) : η₂ ≤ ρ i := by
  have hh := (abs_le.mp (h.ratio_error_le hf hL hlip hi hT)).1
  have hσ := h.updates.pos hi.le
  have hη : 0 < 1 - η₂ := sub_pos.mpr h.updates.eta2_lt_one
  have hm := (div_le_iff₀ hη).1 hlarge
  have hK : 0 ≤ max O.stepCoefficient O.initialCap * O.errorBound :=
    mul_nonneg (O.initialCap_nonneg.trans (le_max_right _ _)) O.errorBound_nonneg
  have hc : (L + 2 * ((p + 1).factorial : ℝ) *
      (max O.stepCoefficient O.initialCap * O.errorBound)) / σ i ≤ 1 - η₂ := by
    apply (div_le_iff₀ hσ).2
    dsimp [parameterCoefficient] at hm
    nlinarith [show 0 ≤ ((p + 1).factorial : ℝ) *
      (max O.stepCoefficient O.initialCap * O.errorBound) by positivity]
  linarith

/-- The corrected very-successful threshold prevents a parameter increase. -/
theorem next_le_of_large (h : ModelTrace f p O A T x d s accuracy σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hT : i ∈ T)
    (hlarge : parameterCoefficient O L / (1 - η₂) ≤ σ i) : σ (i + 1) ≤ σ i := by
  have hg := h.very_successful hf hL hlip hi hT hlarge
  have hu := h.updates.update i hi hT
  rw [ite_eq_left hg] at hu
  exact hu.2

/-- Trial updates and unchanged accuracy-only parameters give the corrected
uniform upper bound, including every endpoint of the finite prefix. -/
theorem parameter_le (h : ModelTrace f p O A T x d s accuracy σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i ≤ N) :
    σ i ≤ max (σ 0) (γ₃ * parameterCoefficient O L / (1 - η₂)) := by
  simpa only [mul_div_assoc] using h.updates.le_max_initial_threshold
    (fun k hk hT hlarge => h.very_successful hf hL hlip hk hT hlarge) hi

/-- The printed bound is valid under the explicit additional condition that
initial requests are no larger than the short-step accuracy coefficient. -/
theorem parameter_le_of_cap_le (h : ModelTrace f p O A T x d s accuracy σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hcap : O.initialCap ≤ O.stepCoefficient) {i : ℕ} (hi : i ≤ N) :
    σ i ≤ max (σ 0) (γ₃ *
      (2 * L + 4 * ((p + 1).factorial : ℝ) * O.stepCoefficient * O.errorBound) /
        (1 - η₂)) := by
  simpa only [parameterCoefficient_eq_of_cap_le O L hcap] using
    h.parameter_le hf hL hlip hi

end ModelTrace
end InexactRegularization
