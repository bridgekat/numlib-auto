import Numlib.Optimization.TrustRegion.Regularized.FirstOrder

/-!
# Second-order budgets for regularized trust-region executions

The boundary rule tests curvature at the current iterate. An accepted interior
step can enter negative curvature, so its next-point gradient alone need not
provide a uniform decrease. The potential subtracts half a decrease unit at
points whose gradient test passes. Entering this set pays the potential credit;
leaving it uses the current curvature-forced boundary decrease. This yields the
second-order complexity order with a factor two and explicit initialized counts.
-/

namespace RegularizedTrustRegion
open EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The positive common scale in the finite-second-order decrease budget. -/
noncomputable def secondOrderScale (ε₁ ε₂ : ℝ) : ℝ :=
  min (ε₂ ^ 3) (ε₁ ^ 2 * ε₂⁻¹)

/-- Both positive accuracies give a positive common scale. -/
theorem secondOrderScale_pos {ε₁ ε₂ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) :
    0 < secondOrderScale ε₁ ε₂ := by unfold secondOrderScale; positivity

/-- The reciprocal common scale is exactly the maximum of the two source
complexity powers, with both accuracies allowed to vary independently. -/
theorem inv_secondOrderScale_eq {ε₁ ε₂ : ℝ} (h₁ : 0 < ε₁) (h₂ : 0 < ε₂) :
    (secondOrderScale ε₁ ε₂)⁻¹ = max (ε₂ / ε₁ ^ 2) (ε₂ ^ 3)⁻¹ := by
  have hA : 0 < ε₂ ^ 3 := by positivity
  have hB : 0 < ε₁ ^ 2 * ε₂⁻¹ := by positivity
  have heq : ε₂ / ε₁ ^ 2 = (ε₁ ^ 2 * ε₂⁻¹)⁻¹ := by field_simp
  rw [heq, max_comm]
  unfold secondOrderScale
  rcases le_total (ε₂ ^ 3) (ε₁ ^ 2 * ε₂⁻¹) with h | h
  · rw [min_eq_left h, max_eq_left ((inv_le_inv₀ hB hA).mpr h)]
  · rw [min_eq_right h, max_eq_right ((inv_le_inv₀ hA hB).mpr h)]

/-- The objective potential credits a point passing the first-gradient test.
The credit depends only on the actual point, so rejection preserves it exactly. -/
noncomputable def creditPotential (f : E → ℝ) (ε₁ d : ℝ) (x : E) : ℝ := by
  classical
  exact f x - d / 2 * (if ‖gradient f x‖ ≤ ε₁ then 1 else 0)

/-- The potential stays between the objective minus half a unit and the objective. -/
theorem creditPotential_bounds (f : E → ℝ) (ε₁ : ℝ) {d : ℝ} (hd : 0 ≤ d) (x : E) :
    f x - d / 2 ≤ creditPotential f ε₁ d x ∧ creditPotential f ε₁ d x ≤ f x := by
  classical
  unfold creditPotential
  split_ifs <;> constructor <;> linarith

namespace Run
variable {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ L : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}

/-- The enabled finite-mode stopping test fails by a large gradient or a genuine
negative least Hessian eigenvalue, with the current iterate index unchanged. -/
theorem finite_failure (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hfinite : ε₂ = (ε : WithTop ℝ)) {i : ℕ} (hi : i < N) :
    ε₁ < ‖gradient f (x i)‖ ∨ μ i < -ε := by
  by_cases hg : ε₁ < ‖gradient f (x i)‖
  · exact Or.inl hg
  · right
    by_contra hm
    apply h.not_terminated i hi
    apply (stopped_iff _ _ _ _ _).mpr
    refine ⟨le_of_not_gt hg, ?_⟩
    intro e he
    have heq : ε = e := WithTop.coe_injective (hfinite.symm.trans he)
    simpa only [← heq] using le_of_not_gt hm

/-- Passing the current gradient test forces a boundary step in finite mode,
because this actual current iterate is still nonterminal. -/
theorem boundary_of_small_gradient
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hfinite : ε₂ = (ε : WithTop ℝ)) {i : ℕ} (hi : i < N)
    (hg : ‖gradient f (x i)‖ ≤ ε₁) : ‖s i‖ = Δ i := by
  rcases h.finite_failure hfinite hi with hlarge | hcurv
  · exact (not_lt_of_ge hg hlarge).elim
  · exact h.curvature_boundary i hi ε hfinite hcurv

/-- A next point failing the gradient test gives sufficient actual objective
reduction, without assuming anything about its curvature. -/
theorem successful_decrease_of_next_gradient
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) (ha : η₁ ≤ ρ i)
    (hg : ε₁ ≤ ‖gradient f (x (i + 1))‖) :
    decreaseCoefficient η₁ η₂ γ₁ L θ * secondOrderScale ε₁ ε ≤
      f (x i) - f (x (i + 1)) := by
  have hc := decreaseCoefficient_pos h.updates.eta1_pos h.updates.eta2_lt_one
    h.updates.gamma1_pos (zero_lt_one.trans_le hL) h.theta_pos.le
  by_cases hb : ‖s i‖ = Δ i
  · apply le_trans _ (h.successful_decrease_boundary hf hL hlip hi ha hb)
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le
  · have hh := h.successful_decrease_interior hf (zero_le_one.trans hL) hlip hi ha
      (lt_of_le_of_ne (h.feasible i hi) hb)
    apply le_trans _ hh
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply min_le_min le_rfl
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h.first_accuracy_pos.le hg 2)
      (inv_nonneg.mpr h.regularization_pos.le)

/-- The actual accepted objective is nonincreasing, including trials whose next
point already passes the gradient test. -/
theorem successful_objective_nonincreasing
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    {i : ℕ} (hi : i < N) (ha : η₁ ≤ ρ i) : f (x (i + 1)) ≤ f (x i) := by
  have hh := h.successful_decrease_step hi ha
  have hη := h.updates.eta1_pos
  have hε := h.regularization_pos
  have hnonneg : 0 ≤ η₁ / 2 * ε * ‖s i‖ ^ 2 := by positivity
  linarith

/-- The credited objective loses at least half a common decrease unit at every
accepted finite-mode trial, even when this is the terminal trial. -/
theorem successful_credit_decrease
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hfinite : ε₂ = (ε : WithTop ℝ)) (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) (ha : η₁ ≤ ρ i) :
    let d := decreaseCoefficient η₁ η₂ γ₁ L θ * secondOrderScale ε₁ ε
    d / 2 ≤ creditPotential f ε₁ d (x i) - creditPotential f ε₁ d (x (i + 1)) := by
  classical
  dsimp only
  let d := decreaseCoefficient η₁ η₂ γ₁ L θ * secondOrderScale ε₁ ε
  have hc := decreaseCoefficient_pos h.updates.eta1_pos h.updates.eta2_lt_one
    h.updates.gamma1_pos (zero_lt_one.trans_le hL) h.theta_pos.le
  have hd : 0 < d := mul_pos hc (secondOrderScale_pos h.first_accuracy_pos h.regularization_pos)
  by_cases hcurrent : ‖gradient f (x i)‖ ≤ ε₁
  · have hh := h.successful_decrease_boundary hf hL hlip hi ha
      (h.boundary_of_small_gradient hfinite hi hcurrent)
    have hb : d ≤ f (x i) - f (x (i + 1)) :=
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le).trans hh
    change d / 2 ≤ _
    unfold creditPotential
    rw [ite_eq_left hcurrent]
    split_ifs <;> linarith
  · by_cases hnext : ‖gradient f (x (i + 1))‖ ≤ ε₁
    · have hh := h.successful_objective_nonincreasing hi ha
      change d / 2 ≤ _
      unfold creditPotential
      rw [ite_eq_right hcurrent, ite_eq_left hnext]
      linarith
    · have hh := h.successful_decrease_of_next_gradient hf hL hlip hi ha
        (le_of_not_ge hnext)
      change d / 2 ≤ _
      unfold creditPotential
      rw [ite_eq_right hcurrent, ite_eq_right hnext]
      dsimp only [d] at hd
      linarith

/-- The credited finite objective budget bounds all successful trials, with no
assumption that a new negative-curvature point was reached by a boundary step. -/
theorem secondOrder_successful_card_le
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hfinite : ε₂ = (ε : WithTop ℝ)) (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    ((successfulIterations {i | η₁ ≤ ρ i} N).card : ℝ) ≤
      2 * (f (x 0) - flow) /
        (decreaseCoefficient η₁ η₂ γ₁ L θ * secondOrderScale ε₁ ε) + 1 := by
  let d := decreaseCoefficient η₁ η₂ γ₁ L θ * secondOrderScale ε₁ ε
  have hc := decreaseCoefficient_pos h.updates.eta1_pos h.updates.eta2_lt_one
    h.updates.gamma1_pos (zero_lt_one.trans_le hL) h.theta_pos.le
  have hd : 0 < d := mul_pos hc (secondOrderScale_pos h.first_accuracy_pos h.regularization_pos)
  have hlo : flow - d / 2 ≤ creditPotential f ε₁ d (x N) :=
    (sub_le_sub_right (hlow _) _).trans (creditPotential_bounds f ε₁ hd.le (x N)).1
  have hh := card_successful_le_gap_div
    (S := {i | η₁ ≤ ρ i}) (f := fun i => creditPotential f ε₁ d (x i))
    (show 0 < d / 2 by positivity) hlo
    (fun i hi ha => h.successful_credit_decrease hfinite hf hL hlip hi ha)
    (fun i hi ha => by rw [h.rejected_point hi ha])
  have hinit := (creditPotential_bounds f ε₁ hd.le (x 0)).2
  have hb : (creditPotential f ε₁ d (x 0) - (flow - d / 2)) / (d / 2) ≤
      (f (x 0) - (flow - d / 2)) / (d / 2) :=
    div_le_div_of_nonneg_right (sub_le_sub_right hinit _) (by positivity)
  have heq : (f (x 0) - (flow - d / 2)) / (d / 2) =
      2 * (f (x 0) - flow) / d + 1 := by field_simp; ring
  exact hh.trans (by simpa only [heq, d] using hb)

/-- The exact radius floor and credited objective budget give the complete
finite-second-order trial bound for the literal current-curvature boundary rule. -/
theorem secondOrder_iterations_le
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hfinite : ε₂ = (ε : WithTop ℝ)) (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {flow : ℝ} (hlow : ∀ y, flow ≤ f y) :
    (N : ℝ) ≤ (2 * (f (x 0) - flow) /
        (decreaseCoefficient η₁ η₂ γ₁ L θ * secondOrderScale ε₁ ε) + 1) *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      (|Real.log ((1 - η₂) * γ₁ / (L * Δ 0))| + |Real.log ε|) / |Real.log γ₂| := by
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
      |Real.log ((1 - η₂) * γ₁ / (L * Δ 0))| + |Real.log ε| := by
    have heq : R * ε / Δ 0 = ((1 - η₂) * γ₁ / (L * Δ 0)) * ε := by dsimp [R]; ring
    rw [heq, Real.log_mul (by have hΔ := h.updates.initial_pos; positivity) hε.ne']
    exact abs_add_le _ _
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right (h.secondOrder_successful_card_le hfinite hf hL hlip hlow) hA)
    (div_le_div_of_nonneg_right hl (abs_nonneg _)))

end Run
/-- Every consistent finite-second-order execution reaches the first actual
joint stopping point. The credited potential proves termination without moving
the boundary rule from the current point to the next point. -/
theorem exists_secondOrder_termination {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
    {η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ L flow : ℝ}
    (hprefix : ∀ N, (∀ i < N, ¬Stopped f (x i) (μ i) ε₁ (ε : WithTop ℝ)) →
      Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ (ε : WithTop ℝ) N)
    (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) (hlow : ∀ y, flow ≤ f y) :
    ∃ K, Stopped f (x K) (μ K) ε₁ (ε : WithTop ℝ) ∧
      Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ (ε : WithTop ℝ) K ∧
      ∀ i < K, ¬Stopped f (x i) (μ i) ε₁ (ε : WithTop ℝ) := by
  classical
  have hex : ∃ K, Stopped f (x K) (μ K) ε₁ (ε : WithTop ℝ) := by
    by_contra hn
    push Not at hn
    let bound := (2 * (f (x 0) - flow) /
        (decreaseCoefficient η₁ η₂ γ₁ L θ * secondOrderScale ε₁ ε) + 1) *
        (1 + Real.log γ₃ / |Real.log γ₂|) +
      (|Real.log ((1 - η₂) * γ₁ / (L * Δ 0))| + |Real.log ε|) / |Real.log γ₂|
    obtain ⟨N, hN⟩ := exists_nat_gt bound
    have hb := (hprefix N (fun i _ => hn i)).secondOrder_iterations_le rfl hf hL hlip hlow
    exact (not_le_of_gt hN) hb
  refine ⟨Nat.find hex, Nat.find_spec hex, hprefix _ ?_, ?_⟩ <;>
    exact fun i hi => Nat.find_min hex hi

end RegularizedTrustRegion
