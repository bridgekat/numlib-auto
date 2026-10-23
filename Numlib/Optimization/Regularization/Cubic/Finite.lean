import Numlib.Optimization.Regularization.Cubic.SecondOrder
import Numlib.Optimization.Regularization.Cubic.FirstOrder

/-!
# Finite-second-order cubic-regularization evaluation complexity

A genuine AR2 trace uses actual model derivatives and actual least Hessian eigenpairs.
Its objective and regularization-parameter budgets imply termination and all evaluation
counts. One final accepted endpoint can already meet both stopping tests; its derivative
calls and the initial calls are both included.
-/

namespace CubicRegularization
open TaylorModel EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The full operational AR2 branch with both finite stopping tests enabled. -/
structure FiniteRun (f : E → ℝ) (x s u : ℕ → E) (μ σ ρ : ℕ → ℝ)
    (η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ : ℝ) (N : ℕ) : Prop where
  trace : ModelTrace f x s σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin N
  theta_first_pos : 0 < θ₁
  theta_second_pos : 0 < θ₂
  accuracy_first_pos : 0 < ε₁
  accuracy_first_le_one : ε₁ ≤ 1
  accuracy_second_pos : 0 < ε₂
  accuracy_second_le_one : ε₂ ≤ 1
  least_eigenpair : ∀ i ≤ N, SecondOrderTrustRegion.IsLeastEigenpair f (x i) (μ i) (u i)
  not_terminated : ∀ i < N, ε₁ < ‖fderiv ℝ f (x i)‖ ∨ μ i < -ε₂
  stationary_first : ∀ i < N,
    ‖fderiv ℝ (model f (x i) (σ i)) (s i)‖ ≤ θ₁ / 2 * ‖s i‖ ^ 2
  stationary_second : ∀ i < N, SecondOrderStationary f (x i) (s i) (σ i) θ₂
  step : ∀ i < N, x (i + 1) = if η₁ ≤ ρ i then x i + s i else x i

/-- The common accuracy-independent denominator in the source second-order AR2 bound. -/
noncomputable def finiteDenominator (σ₀ η₂ γ₃ L θ₁ θ₂ : ℝ) : ℝ :=
  L + max 1 (max θ₁ θ₂) + max σ₀ (γ₃ * L / (1 - η₂))

/-- The reciprocal of the printed successful-iteration coefficient. -/
noncomputable def finiteDecreaseCoefficient (σ₀ σmin η₁ η₂ γ₃ L θ₁ θ₂ : ℝ) : ℝ :=
  η₁ * σmin / (6 * finiteDenominator σ₀ η₂ γ₃ L θ₁ θ₂ ^ 3)

/-- The two-accuracy factor in the source second-order cubic complexity bound. -/
noncomputable def finiteAccuracyFactor (ε₁ ε₂ : ℝ) : ℝ :=
  min (ε₁ ^ (3 / 2 : ℝ)) (ε₂ ^ 3)

/-- The actual objective is evaluated initially and at each trial. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Both actual gradient and Hessian are evaluated initially and at accepted trials. -/
noncomputable def derivativeEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : ℕ :=
  (successfulIterations {i | η₁ ≤ ρ i} N).card + 1

/-- Gradient calls include initialization and every accepted trial endpoint. -/
noncomputable abbrev gradientEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : ℕ :=
  derivativeEvaluations ρ η₁ N

/-- Hessian calls follow the same accepted-endpoint schedule. -/
noncomputable abbrev hessianEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : ℕ :=
  derivativeEvaluations ρ η₁ N

namespace FiniteRun
variable {f : E → ℝ} {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ L : ℝ} {N : ℕ}

/-- The fixed denominator is larger than one and than both stationarity denominators. -/
theorem denominator_bounds
    (h : FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    (hL : 0 ≤ L) :
    1 ≤ finiteDenominator (σ 0) η₂ γ₃ L θ₁ θ₂ ∧
      L + θ₁ + max (σ 0) (γ₃ * L / (1 - η₂)) ≤
        finiteDenominator (σ 0) η₂ γ₃ L θ₁ θ₂ ∧
      L + θ₂ + max (σ 0) (γ₃ * L / (1 - η₂)) ≤
        finiteDenominator (σ 0) η₂ γ₃ L θ₁ θ₂ := by
  have hp : 0 < max (σ 0) (γ₃ * L / (1 - η₂)) :=
    (h.trace.updates.pos (Nat.zero_le N)).trans_le (le_max_left _ _)
  unfold finiteDenominator
  constructor
  · linarith [le_max_left (1 : ℝ) (max θ₁ θ₂)]
  · exact ⟨by linarith [le_max_right (1 : ℝ) (max θ₁ θ₂), le_max_left θ₁ θ₂],
      by linarith [le_max_right (1 : ℝ) (max θ₁ θ₂), le_max_right θ₁ θ₂]⟩

/-- The successful-iteration decrease coefficient is strictly positive. -/
theorem finiteDecreaseCoefficient_pos
    (h : FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    (hL : 0 ≤ L) : 0 < finiteDecreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ := by
  have hG : 0 < finiteDenominator (σ 0) η₂ γ₃ L θ₁ θ₂ :=
    zero_lt_one.trans_le (h.denominator_bounds hL).1
  have hη := h.trace.updates.eta1_pos
  have hmin := h.trace.updates.min_pos
  unfold finiteDecreaseCoefficient
  positivity

/-- The reciprocal coefficient is the exact printed successful-iteration constant. -/
theorem inv_finiteDecreaseCoefficient_eq
    (h : FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    (hL : 0 ≤ L) :
    1 / finiteDecreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ =
      6 * finiteDenominator (σ 0) η₂ γ₃ L θ₁ θ₂ ^ 3 / (η₁ * σmin) := by
  have hG : 0 < finiteDenominator (σ 0) η₂ γ₃ L θ₁ θ₂ :=
    zero_lt_one.trans_le (h.denominator_bounds hL).1
  have hη := h.trace.updates.eta1_pos
  have hmin := h.trace.updates.min_pos
  unfold finiteDecreaseCoefficient
  field_simp

/-- Accepted trials attain genuine objective decrease from strict actual model improvement. -/
theorem successful_decrease
    (h : FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    {i : ℕ} (hi : i < N) (hs : η₁ ≤ ρ i) :
    η₁ * σmin / 6 * ‖s i‖ ^ 3 ≤ f (x i) - f (x (i + 1)) := by
  have hr := (le_div_iff₀ (h.trace.denominator_pos hi)).mp ((h.trace.ratio i hi) ▸ hs)
  have hd := mul_le_mul_of_nonneg_left (h.trace.model_decrease hi).le
    h.trace.updates.eta1_pos.le
  have hmin := mul_le_mul_of_nonneg_right (h.trace.updates.min_le (show i ≤ N by omega))
    (pow_nonneg (norm_nonneg (s i)) 3)
  rw [h.step i hi, ite_eq_left hs]
  nlinarith [mul_le_mul_of_nonneg_left hmin h.trace.updates.eta1_pos.le]

/-- Failure of either endpoint stopping test gives the uniform step-cube budget. -/
theorem step_cube_lower
    (h : FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i + 1 < N) (hs : η₁ ≤ ρ i) :
    finiteAccuracyFactor ε₁ ε₂ ≤
      finiteDenominator (σ 0) η₂ γ₃ L θ₁ θ₂ ^ 3 * ‖s i‖ ^ 3 := by
  let G := finiteDenominator (σ 0) η₂ γ₃ L θ₁ θ₂
  have hG1 : 1 ≤ G := (h.denominator_bounds hL).1
  have hG0 : 0 ≤ G := by linarith
  have hmax := h.trace.parameter_le hf hL hlip (i := i) (by omega)
  have hσ := h.trace.updates.pos (show i ≤ N by omega)
  rcases h.not_terminated (i + 1) hi with hg | hc
  · rw [h.step i (by omega), ite_eq_left hs] at hg
    have hb := trial_derivative_le hf hσ.le hlip (x i) (s i) (h.stationary_first i (by omega))
    have hD : L + θ₁ + σ i ≤ G :=
      (by linarith : L + θ₁ + σ i ≤ L + θ₁ + max (σ 0) (γ₃ * L / (1 - η₂))).trans
        (h.denominator_bounds hL).2.1
    have hprod := mul_le_mul_of_nonneg_right hD (sq_nonneg ‖s i‖)
    have hGsq : G / 2 ≤ G ^ 2 := by nlinarith
    have hh : ε₁ ≤ G ^ 2 * ‖s i‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hGsq (sq_nonneg ‖s i‖)]
    have hp := Real.rpow_le_rpow h.accuracy_first_pos.le hh (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have hs3 : (‖s i‖ ^ 2) ^ (3 / 2 : ℝ) = ‖s i‖ ^ 3 := by
      rw [←Real.rpow_natCast, ←Real.rpow_mul (norm_nonneg (s i))]
      norm_num
    have hG3 : (G ^ 2) ^ (3 / 2 : ℝ) = G ^ 3 := by
      rw [←Real.rpow_natCast, ←Real.rpow_mul hG0]
      norm_num
    rw [Real.mul_rpow (sq_nonneg G) (sq_nonneg ‖s i‖), hs3, hG3] at hp
    exact (min_le_left _ _).trans hp
  · have hp := h.least_eigenpair (i + 1) (by omega)
    have he := hp.eigenvector
    rw [h.step i (by omega), ite_eq_left hs] at he
    have hb := trial_curvature_lower hf hσ.le hlip (x i) (s i) (u (i + 1)) hp.unit
      (h.stationary_second i (by omega))
    rw [TaylorModel.tensor_curvature_of_eigenvector f (x i + s i) (u (i + 1)) hp.unit he] at hb
    have hD : L + θ₂ + σ i ≤ G :=
      (by linarith : L + θ₂ + σ i ≤ L + θ₂ + max (σ 0) (γ₃ * L / (1 - η₂))).trans
        (h.denominator_bounds hL).2.2
    have hh : ε₂ ≤ G * ‖s i‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hD (norm_nonneg (s i))]
    have hcub := pow_le_pow_left₀ h.accuracy_second_pos.le hh 3
    rw [mul_pow] at hcub
    exact (min_le_right _ _).trans hcub

/-- Each accepted trial with a nonterminal endpoint consumes the uniform objective budget. -/
theorem nonterminal_successful_decrease
    (h : FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i + 1 < N) (hs : η₁ ≤ ρ i) :
    finiteDecreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ * finiteAccuracyFactor ε₁ ε₂ ≤
      f (x i) - f (x (i + 1)) := by
  have hG : 0 < finiteDenominator (σ 0) η₂ γ₃ L θ₁ θ₂ :=
    zero_lt_one.trans_le (h.denominator_bounds hL).1
  have hc := h.finiteDecreaseCoefficient_pos hL
  have hh := mul_le_mul_of_nonneg_left (h.step_cube_lower hf hL hlip hi hs) hc.le
  have he : finiteDecreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ *
      finiteDenominator (σ 0) η₂ γ₃ L θ₁ θ₂ ^ 3 * ‖s i‖ ^ 3 =
        η₁ * σmin / 6 * ‖s i‖ ^ 3 := by
    unfold finiteDecreaseCoefficient
    field_simp
  have hh' : finiteDecreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ *
      finiteAccuracyFactor ε₁ ε₂ ≤ η₁ * σmin / 6 * ‖s i‖ ^ 3 := by
    simpa only [←mul_assoc, he] using hh
  exact hh'.trans (h.successful_decrease (by omega) hs)

/-- Failed trials leave the actual objective unchanged. -/
theorem objective_eq_of_unsuccessful
    (h : FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    {i : ℕ} (hi : i < N) (hu : ¬η₁ ≤ ρ i) : f (x (i + 1)) = f (x i) := by
  rw [h.step i hi, ite_eq_right hu]

/-- At most one final accepted endpoint is outside the nonterminal objective budget. -/
theorem successful_card_le
    (h : FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤ (f (x 0) - flow) /
      (finiteDecreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ *
        finiteAccuracyFactor ε₁ ε₂) + 1 := by
  have hgap : 0 ≤ f (x 0) - flow := sub_nonneg.mpr (hlow _)
  have ha : 0 < finiteAccuracyFactor ε₁ ε₂ := by
    have h₁ := h.accuracy_first_pos
    have h₂ := h.accuracy_second_pos
    unfold finiteAccuracyFactor
    positivity
  have hdpos := mul_pos (h.finiteDecreaseCoefficient_pos hL) ha
  cases N with
  | zero => simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]; positivity
  | succ k =>
    have hc := card_successful_le_gap_div
      (S := {i | η₁ ≤ ρ i}) (f := fun i => f (x i)) hdpos (hlow (x k))
      (fun i hi hs => h.nonterminal_successful_decrease hf hL hlip (by omega) hs)
      (fun i hi hu => (h.objective_eq_of_unsuccessful (by omega) hu).le)
    have hsucc : ((successfulIterations {i | η₁ ≤ ρ i} (k + 1)).card : ℝ) ≤
        (successfulIterations {i | η₁ ≤ ρ i} k).card + 1 := by
      exact_mod_cast card_successful_succ_le {i | η₁ ≤ ρ i} k
    exact hsucc.trans (add_le_add hc le_rfl)

/-- Actual regularization updates turn the successful-trial budget into the total trial budget. -/
theorem iterations_le
    (h : FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    (N : ℝ) ≤ ((f (x 0) - flow) /
      (finiteDecreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ * finiteAccuracyFactor ε₁ ε₂) + 1) *
        (1 + |Real.log γ₁| / Real.log γ₂) +
      Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂ := by
  have ht := iteration_bound_of_parameter_upper
    (S := {i | η₁ ≤ ρ i}) (fun _ hi => h.trace.updates.pos hi)
    h.trace.updates.gamma1_pos h.trace.updates.gamma1_lt_one
    h.trace.updates.one_lt_gamma2 (h.trace.parameter_le hf hL hlip le_rfl)
    (fun _ hi hs => h.trace.updates.successful_ge hi hs)
    (fun _ hi hu => h.trace.updates.unsuccessful_ge hi hu)
  have hlog := Real.log_pos h.trace.updates.one_lt_gamma2
  have hA : 0 ≤ 1 + |Real.log γ₁| / Real.log γ₂ := by positivity
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right (h.successful_card_le hf hL hlip hlow) hA) le_rfl)
end FiniteRun

/-- Consistent actual finite-tolerance AR2 prefixes terminate at the first iterate
satisfying both requested derivative tests. -/
theorem exists_finite_termination {f : E → ℝ} {x s u : ℕ → E} {μ σ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ε₁ < ‖fderiv ℝ f (x i)‖ ∨ μ i < -ε₂) →
      FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y, flow ≤ f y) :
    ∃ K, ‖fderiv ℝ f (x K)‖ ≤ ε₁ ∧ -ε₂ ≤ μ K ∧
      FiniteRun f x s u μ σ ρ η₁ η₂ γ₁ γ₂ γ₃ σmin θ₁ θ₂ ε₁ ε₂ K ∧
      ∀ i < K, ε₁ < ‖fderiv ℝ f (x i)‖ ∨ μ i < -ε₂ := by
  have hex : ∃ K, ‖fderiv ℝ f (x K)‖ ≤ ε₁ ∧ -ε₂ ≤ μ K := by
    by_contra hn
    push Not at hn
    have hnon : ∀ i, ε₁ < ‖fderiv ℝ f (x i)‖ ∨ μ i < -ε₂ := by
      intro i
      by_cases hg : ε₁ < ‖fderiv ℝ f (x i)‖
      · exact Or.inl hg
      · exact Or.inr (hn i (le_of_not_gt hg))
    let bound := ((f (x 0) - flow) /
      (finiteDecreaseCoefficient (σ 0) σmin η₁ η₂ γ₃ L θ₁ θ₂ * finiteAccuracyFactor ε₁ ε₂) + 1) *
        (1 + |Real.log γ₁| / Real.log γ₂) +
      Real.log (max (σ 0) (γ₃ * L / (1 - η₂)) / σ 0) / Real.log γ₂
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have hb := (hprefix N (fun i _ => hnon i)).iterations_le hf hL hlip hlow
    exact (not_le_of_gt hN) hb
  have hnon : ∀ i < Nat.find hex, ε₁ < ‖fderiv ℝ f (x i)‖ ∨ μ i < -ε₂ := by
    intro i hi
    have hh := Nat.find_min hex hi
    by_cases hg : ε₁ < ‖fderiv ℝ f (x i)‖
    · exact Or.inl hg
    · exact Or.inr (lt_of_not_ge (fun hc => hh ⟨le_of_not_gt hg, hc⟩))
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hprefix _ hnon, hnon⟩
end CubicRegularization
