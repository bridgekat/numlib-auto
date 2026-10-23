import Numlib.Optimization.TrustRegion.Regularized.Decrease
import Numlib.Optimization.EvaluationComplexity.Decrease

/-!
# First-order complexity of regularized trust-region executions

A fixed positive decrease coefficient consumes the objective budget at every
successful trial except possibly the final one. The genuine radius floor and
permitted updates bound unsuccessful trials. Initialized evaluation counts and
the source's logarithmic radius allowance are retained explicitly.
-/

namespace RegularizedTrustRegion
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The initial objective and every actual trial each require one function call. -/
def functionEvaluations (N : ℕ) : ℕ := N + 1

/-- Gradients and Hessians are evaluated at initialization and accepted trial points. -/
noncomputable def derivativeEvaluations (ρ : ℕ → ℝ) (η₁ : ℝ) (N : ℕ) : ℕ :=
  (successfulIterations {i | η₁ ≤ ρ i} N).card + 1

/-- The reciprocal decrease coefficient is the exact successful-iteration
constant in the source, with the maximum of the two reciprocal branch factors. -/
theorem inv_decreaseCoefficient_eq {η₁ η₂ γ₁ L θ : ℝ}
    (hη : 0 < η₁) (hη₂ : η₂ < 1) (hγ : 0 < γ₁) (hL : 0 < L) (hθ : 0 ≤ θ) :
    1 / decreaseCoefficient η₁ η₂ γ₁ L θ =
      2 / η₁ * max (L ^ 2 / (γ₁ ^ 2 * (1 - η₂) ^ 2)) (1 + 2 * (L + θ)) := by
  let A := γ₁ ^ 2 * (1 - η₂) ^ 2 / L ^ 2
  let B := (1 + 2 * (L + θ))⁻¹
  have hdiff : 0 < 1 - η₂ := sub_pos.mpr hη₂
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < 1 + 2 * (L + θ) := by positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hAe : 1 / A = L ^ 2 / (γ₁ ^ 2 * (1 - η₂) ^ 2) := by dsimp [A]; field_simp
  have hBe : 1 / B = 1 + 2 * (L + θ) := by dsimp [B]; field_simp
  change 1 / (η₁ / 2 * min A B) = _
  rw [← hAe, ← hBe]
  rcases le_total A B with hab | hba
  · rw [min_eq_left hab, max_eq_left (one_div_le_one_div_of_le hA hab)]
    field_simp
  · rw [min_eq_right hba, max_eq_right (one_div_le_one_div_of_le hB hba)]
    field_simp

namespace Run
variable {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ L : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}

/-- Disabling the second test gives precisely the first-gradient failure test. -/
theorem gradient_gt_of_disabled
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hdisabled : ε₂ = ⊤) {i : ℕ} (hi : i < N) : ε₁ < ‖gradient f (x i)‖ := by
  by_contra hbad
  apply h.not_terminated i hi
  apply (stopped_iff _ _ _ _ _).mpr
  refine ⟨le_of_not_gt hbad, ?_⟩
  intro e he
  simp only [hdisabled] at he
  exact (WithTop.top_ne_coe he).elim

/-- First-order-only mode uses the square root of the actual gradient tolerance. -/
theorem regularization_eq_sqrt
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hdisabled : ε₂ = ⊤) : ε = Real.sqrt ε₁ := by
  rcases h.mode with ⟨_, he⟩ | ⟨he, _⟩
  · exact he
  · simp only [hdisabled] at he
    exact (WithTop.top_ne_coe he).elim

/-- The cubic regularization scale in first-order mode is the exact `3/2` power. -/
theorem regularization_cube_eq
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hdisabled : ε₂ = ⊤) : ε ^ 3 = ε₁ ^ (3 / 2 : ℝ) := by
  rw [h.regularization_eq_sqrt hdisabled, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul h.first_accuracy_pos.le]
  norm_num

/-- Every accepted trial whose endpoint is still nonterminal consumes the
uniform `epsilon^(3/2)` objective budget in first-order-only mode. -/
theorem firstOrder_successful_decrease
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hdisabled : ε₂ = ⊤) (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i + 1 < N) (ha : η₁ ≤ ρ i) :
    decreaseCoefficient η₁ η₂ γ₁ L θ * ε₁ ^ (3 / 2 : ℝ) ≤
      f (x i) - f (x (i + 1)) := by
  rw [← h.regularization_cube_eq hdisabled]
  by_cases hb : ‖s i‖ = Δ i
  · exact h.successful_decrease_boundary hf hL hlip (by omega) ha hb
  · have hs : ‖s i‖ < Δ i := lt_of_le_of_ne (h.feasible i (by omega)) hb
    have hh := h.successful_decrease_interior hf (zero_le_one.trans hL) hlip (by omega) ha hs
    have hg := h.gradient_gt_of_disabled hdisabled hi
    have hε := h.regularization_pos
    have hεsq : ε ^ 2 = ε₁ := by
      rw [h.regularization_eq_sqrt hdisabled, Real.sq_sqrt h.first_accuracy_pos.le]
    have hG : ε ^ 3 ≤ ‖gradient f (x (i + 1))‖ ^ 2 * ε⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ hε).mpr
      have hsq := pow_le_pow_left₀ h.first_accuracy_pos.le hg.le 2
      nlinarith [hεsq]
    rwa [min_eq_left hG] at hh

/-- All but possibly one successful trial have a nonterminal endpoint. -/
theorem firstOrder_successful_card_le
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hdisabled : ε₂ = ⊤) (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤
      (f (x 0) - flow) /
        (decreaseCoefficient η₁ η₂ γ₁ L θ * ε₁ ^ (3 / 2 : ℝ)) + 1 := by
  have hgap : 0 ≤ f (x 0) - flow := sub_nonneg.mpr (hlow _)
  have hc := decreaseCoefficient_pos h.updates.eta1_pos h.updates.eta2_lt_one
    h.updates.gamma1_pos (zero_lt_one.trans_le hL) h.theta_pos.le
  have hd := mul_pos hc (Real.rpow_pos_of_pos h.first_accuracy_pos (3 / 2))
  cases N with
  | zero => simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]; positivity
  | succ k =>
    have hh := card_successful_le_gap_div
      (S := {i | η₁ ≤ ρ i}) (f := fun i => f (x i)) hd (hlow (x k))
      (fun i hi ha => h.firstOrder_successful_decrease hdisabled hf hL hlip (by omega) ha)
      (fun i hi ha => by rw [h.rejected_point (by omega) ha])
    have hs : ((successfulIterations {i | η₁ ≤ ρ i} (k + 1)).card : ℝ) ≤
        (successfulIterations {i | η₁ ≤ ρ i} k).card + 1 := by
      exact_mod_cast card_successful_succ_le {i | η₁ ≤ ρ i} k
    exact hs.trans (add_le_add hh le_rfl)

/-- The actual radius updates give the first-order trial bound, preserving
the source's half-logarithm accuracy term. -/
theorem firstOrder_iterations_le
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hdisabled : ε₂ = ⊤) (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    (N : ℝ) ≤ ((f (x 0) - flow) /
        (decreaseCoefficient η₁ η₂ γ₁ L θ * ε₁ ^ (3 / 2 : ℝ)) + 1) *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      (|Real.log ((1 - η₂) * γ₁ / (L * Δ 0))| + |Real.log ε₁| / 2) /
        |Real.log γ₂| := by
  let R := (1 - η₂) * γ₁ / L
  have hη : 0 < 1 - η₂ := sub_pos.mpr h.updates.eta2_lt_one
  have hγ := h.updates.gamma1_pos
  have hε := h.regularization_pos
  have hLpos := zero_lt_one.trans_le hL
  have hR : 0 < R := by dsimp [R]; positivity
  have ht := iteration_bound_of_parameter_lower
    (S := {i | η₁ ≤ ρ i}) (fun _ hi => h.updates.pos hi)
    (zero_lt_one.trans h.updates.one_lt_gamma3)
    (h.updates.gamma1_pos.trans_le h.updates.gamma1_le_gamma2)
    h.updates.gamma2_lt_one (h.toModelTrace.radius_floor hf hL hlip le_rfl)
    (mul_pos hR hε) (fun _ hi ha => h.updates.successful_le hi ha)
    (fun _ hi ha => h.updates.unsuccessful_le hi ha)
  have hA : 0 ≤ 1 + Real.log γ₃ / |Real.log γ₂| := by
    have hg := Real.log_pos h.updates.one_lt_gamma3
    positivity
  have hl : |Real.log (R * ε / Δ 0)| ≤
      |Real.log ((1 - η₂) * γ₁ / (L * Δ 0))| + |Real.log ε₁| / 2 := by
    have heq : R * ε / Δ 0 = ((1 - η₂) * γ₁ / (L * Δ 0)) * ε := by dsimp [R]; ring
    rw [heq, Real.log_mul (by have hΔ := h.updates.initial_pos; positivity) hε.ne']
    apply (abs_add_le _ _).trans
    rw [h.regularization_eq_sqrt hdisabled, Real.log_sqrt h.first_accuracy_pos.le,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right (h.firstOrder_successful_card_le hdisabled hf hL hlip hlow) hA)
    (div_le_div_of_nonneg_right hl (abs_nonneg _)))
end Run

/-- Every consistent first-order-only execution reaches the first actual
stopping point; termination is derived from its finite objective and radius budgets. -/
theorem exists_firstOrder_termination {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ¬Stopped f (x i) (μ i) ε₁ ⊤) →
      Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ⊤ N)
    (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hlow : ∀ y, flow ≤ f y) :
    ∃ K, Stopped f (x K) (μ K) ε₁ ⊤ ∧
      Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ⊤ K ∧
      ∀ i < K, ¬Stopped f (x i) (μ i) ε₁ ⊤ := by
  classical
  have hex : ∃ K, Stopped f (x K) (μ K) ε₁ ⊤ := by
    by_contra hn
    push Not at hn
    let bound := ((f (x 0) - flow) /
        (decreaseCoefficient η₁ η₂ γ₁ L θ * ε₁ ^ (3 / 2 : ℝ)) + 1) *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      (|Real.log ((1 - η₂) * γ₁ / (L * Δ 0))| + |Real.log ε₁| / 2) /
        |Real.log γ₂|
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have hb := (hprefix N (fun i _ => hn i)).firstOrder_iterations_le rfl hf hL hlip hlow
    exact (not_le_of_gt hN) hb
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_, ?_⟩ <;>
    exact fun i hi => Nat.find_min hex hi

end RegularizedTrustRegion
