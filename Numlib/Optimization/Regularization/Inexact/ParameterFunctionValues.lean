import Numlib.Optimization.Regularization.Inexact.Parameter

/-!
# Guarded regularization with approximate objective values

Both objective errors enter the computed acceptance ratio. Shared guarded oracle
rules retain the initial request cap on large steps. The corrected parameter
threshold reserves half of the acceptance margin for objective errors and half
for the true Taylor and derivative errors.
-/

namespace InexactRegularization
open TaylorModel EvaluationComplexity Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual Taylor remainder and tensor errors control the computed decrement,
independently of the constant tensor and for arbitrary trial lengths. -/
theorem objective_decrement_error_le {f : E → ℝ} {p : ℕ}
    (hp : 0 < p) (hf : ContDiff ℝ p f) {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (A : FormalMultilinearSeries ℝ E ℝ) (x s : E)
    (herr : ∀ a, 1 ≤ a → a ≤ p →
      ‖A a - iteratedFDeriv ℝ a f x‖ ≤ K * ‖s‖ ^ (p - a + 1)) :
    |(f x - f (x + s)) - jetDecrement A p s| ≤
      (L + 2 * ((p + 1).factorial : ℝ) * K) * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
  have ht := HighOrderRegularization.value_error_le hp hf hL hlip x s
  have he := norm_jetDecrement_sub_le_power A (ftaylorSeries ℝ f x) le_rfl hK s herr
  have hid : (f x - f (x + s)) - jetDecrement A p s =
      -(f (x + s) - eval f p x s) -
        (jetDecrement A p s - jetDecrement (ftaylorSeries ℝ f x) p s) := by
    simp only [jetDecrement, ofJet_zero, eval, ftaylorSeries, iteratedFDeriv_zero_apply]
    abel
  have htri : |(f x - f (x + s)) - jetDecrement A p s| ≤
      |f (x + s) - eval f p x s| +
        ‖jetDecrement A p s - jetDecrement (ftaylorSeries ℝ f x) p s‖ := by
    rw [hid]
    simpa only [Real.norm_eq_abs, norm_neg] using
      norm_sub_le (-(f (x + s) - eval f p x s))
        (jetDecrement A p s - jetDecrement (ftaylorSeries ℝ f x) p s)
  calc _ ≤ L * ‖s‖ ^ (p + 1) / (p + 1).factorial +
        2 * K * ‖s‖ ^ (p + 1) := htri.trans (add_le_add ht he)
    _ = _ := by field_simp

/-- The EDA trace adds primitive errors for both function evaluations, their
relative request bound, and the actual computed objective ratio. -/
structure FunctionTrace (f : E → ℝ) (p : ℕ) (O : OracleSettings p)
    (A : ℕ → FormalMultilinearSeries ℝ E ℝ) (T : Set ℕ)
    (x d s : ℕ → E) (accuracy : ℕ → ℕ → ℝ) (σ ρ F₀ F₁ h₀ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ) (N : ℕ) : Prop
    extends OracleTrace f p O A T x d s accuracy σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N where
  constant_value : ∀ i < N, i ∈ T → A i 0 (fun _ => 0) = F₀ i
  error_initial : ∀ i < N, i ∈ T → |F₀ i - f (x i)| ≤ h₀ i
  error_trial : ∀ i < N, i ∈ T → |F₁ i - f (x i + s i)| ≤ h₀ i
  request_positive : ∀ i < N, i ∈ T → 0 < h₀ i
  relative_request : ∀ i < N, i ∈ T →
    h₀ i ≤ O.stepCoefficient * jetDecrement (A i) p (s i)
  ratio : ∀ i < N, i ∈ T → ρ i = (F₀ i - F₁ i) / jetDecrement (A i) p (s i)

namespace OracleTrace
variable {f : E → ℝ} {p : ℕ} {O : OracleSettings p}
  {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ}
  {x d s : ℕ → E} {accuracy : ℕ → ℕ → ℝ} {σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ} {N : ℕ}

/-- A shared oracle trace controls the true objective-drop error relative to
its positive computed model decrement, without prescribing its acceptance ratio. -/
theorem objective_error_le (h : OracleTrace f p O A T x d s accuracy σ ρ
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hT : i ∈ T) :
    |(f (x i) - f (x i + s i)) - jetDecrement (A i) p (s i)| ≤
      ((L + 2 * ((p + 1).factorial : ℝ) *
        (max O.stepCoefficient O.initialCap * O.errorBound)) / σ i) *
        jetDecrement (A i) p (s i) := by
  let K := max O.stepCoefficient O.initialCap * O.errorBound
  have hK : 0 ≤ K := mul_nonneg
    (O.initialCap_nonneg.trans (le_max_right _ _)) O.errorBound_nonneg
  have hσ := h.updates.pos hi.le
  have he := objective_decrement_error_le h.order_pos hf hL hK hlip (A i) (x i) (s i)
    (fun a ha hap => h.tensor_error_le hi hT ha hap)
  have hd := (penalty_lt_decrement
    (h.reference_improvement i hi hT) (h.comparison i hi hT)).le
  have hC : 0 ≤ L + 2 * ((p + 1).factorial : ℝ) * K := by positivity
  have hm := mul_le_mul_of_nonneg_left hd (div_nonneg hC hσ.le)
  have heq : ((L + 2 * ((p + 1).factorial : ℝ) * K) / σ i) *
      (σ i / (p + 1).factorial * ‖s i‖ ^ (p + 1)) =
      (L + 2 * ((p + 1).factorial : ℝ) * K) * ‖s i‖ ^ (p + 1) /
        (p + 1).factorial := by field_simp
  rw [heq] at hm
  exact he.trans hm

end OracleTrace
namespace FunctionTrace
variable {f : E → ℝ} {p : ℕ} {O : OracleSettings p}
  {A : ℕ → FormalMultilinearSeries ℝ E ℝ} {T : Set ℕ}
  {x d s : ℕ → E} {accuracy : ℕ → ℕ → ℝ} {σ ρ F₀ F₁ h₀ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin : ℝ} {N : ℕ}

/-- Both relative function-value errors contribute to the computed ratio error. -/
theorem ratio_error_le (h : FunctionTrace f p O A T x d s accuracy σ ρ F₀ F₁ h₀
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i < N) (hT : i ∈ T) :
    |ρ i - 1| ≤ 2 * O.stepCoefficient +
      (L + 2 * ((p + 1).factorial : ℝ) *
        (max O.stepCoefficient O.initialCap * O.errorBound)) / σ i := by
  have hd := h.toOracleTrace.denominator_pos hi hT
  have he := abs_le.mp (h.toOracleTrace.objective_error_le hf hL hlip hi hT)
  have h0 := abs_le.mp ((h.error_initial i hi hT).trans (h.relative_request i hi hT))
  have h1 := abs_le.mp ((h.error_trial i hi hT).trans (h.relative_request i hi hT))
  rw [h.ratio i hi hT, div_sub_one hd.ne', abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  apply abs_le.mpr
  constructor <;> nlinarith

/-- With one quarter of the acceptance margin for each objective value,
the corrected parameter threshold forces very successful acceptance. -/
theorem very_successful (h : FunctionTrace f p O A T x d s accuracy σ ρ F₀ F₁ h₀
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hsmall : O.stepCoefficient ≤ (1 - η₂) / 4)
    {i : ℕ} (hi : i < N) (hT : i ∈ T)
    (hlarge : parameterCoefficient O L / (1 - η₂) ≤ σ i) : η₂ ≤ ρ i := by
  have hh := (abs_le.mp (h.ratio_error_le hf hL hlip hi hT)).1
  have hσ := h.updates.pos hi.le
  have hη : 0 < 1 - η₂ := sub_pos.mpr h.updates.eta2_lt_one
  have hm := (div_le_iff₀ hη).1 hlarge
  have hc : (L + 2 * ((p + 1).factorial : ℝ) *
      (max O.stepCoefficient O.initialCap * O.errorBound)) / σ i ≤ (1 - η₂) / 2 := by
    apply (div_le_iff₀ hσ).2
    dsimp [parameterCoefficient] at hm
    nlinarith
  linarith

/-- Corrected EDA parameter bound, with unchanged accuracy-only steps included. -/
theorem parameter_le (h : FunctionTrace f p O A T x d s accuracy σ ρ F₀ F₁ h₀
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hsmall : O.stepCoefficient ≤ (1 - η₂) / 4) {i : ℕ} (hi : i ≤ N) :
    σ i ≤ max (σ 0) (γ₃ * parameterCoefficient O L / (1 - η₂)) := by
  simpa only [mul_div_assoc] using h.updates.le_max_initial_threshold
    (fun k hk hT hlarge => h.very_successful hf hL hlip hsmall hk hT hlarge) hi

/-- The printed EDA coefficient is restored under the explicit cap condition
and the known unit tensor-oracle constant. -/
theorem parameter_le_of_cap_le (h : FunctionTrace f p O A T x d s accuracy σ ρ F₀ F₁ h₀
    η₁ η₂ γ₁ γ₂ γ₃ σmin N) (hf : ContDiff ℝ p f) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y z,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hsmall : O.stepCoefficient ≤ (1 - η₂) / 4)
    (hcap : O.initialCap ≤ O.stepCoefficient) (hunit : O.errorBound = 1)
    {i : ℕ} (hi : i ≤ N) :
    σ i ≤ max (σ 0) (γ₃ *
      (2 * L + 4 * ((p + 1).factorial : ℝ) * O.stepCoefficient) / (1 - η₂)) := by
  simpa only [parameterCoefficient_eq_of_cap_le O L hcap, hunit, mul_one] using
    h.parameter_le hf hL hlip hsmall hi

end FunctionTrace
end InexactRegularization
