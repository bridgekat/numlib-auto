import Numlib.Optimization.TrustRegion.Regularized.Run

/-!
# Sufficient decrease for regularized trust-region executions

Interior trial stationarity and the global radius floor give the two branches
of the successful objective decrease, with a common accuracy-independent
coefficient. The proof uses the actual accepted point and objective ratio.
-/

namespace RegularizedTrustRegion

/-- The square of a minimum of nonnegative reals is the minimum of their squares. -/
theorem min_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (min a b) ^ 2 = min (a ^ 2) (b ^ 2) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (pow_le_pow_left₀ ha h 2)]
  · rw [min_eq_right h, min_eq_right (pow_le_pow_left₀ hb h 2)]

/-- Squaring the minimum-form step estimate gives the exact two-term
objective decrease scale, without dividing by a possibly zero gradient. -/
theorem minimum_scale_le_sq {G t ε D : ℝ} (hG : 0 ≤ G)
    (hε : 0 < ε) (hD : 0 < D)
    (hstep : (Real.sqrt D)⁻¹ * min ε (G * ε⁻¹) ≤ t) :
    min (ε ^ 3) (G ^ 2 * ε⁻¹) ≤ D * ε * t ^ 2 := by
  have hR : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hm : 0 ≤ min ε (G * ε⁻¹) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hstep hR.le
  have hmin : min ε (G * ε⁻¹) ≤ Real.sqrt D * t := by
    simpa only [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] using hmul
  have hsq := pow_le_pow_left₀ hm hmin 2
  have hεsq := mul_le_mul_of_nonneg_left hsq hε.le
  have heq : ε * (min ε (G * ε⁻¹)) ^ 2 = min (ε ^ 3) (G ^ 2 * ε⁻¹) := by
    rw [min_sq hε.le (by positivity), mul_min_of_nonneg _ _ hε.le]
    congr 1
    · ring
    · field_simp
  rw [heq, mul_pow, Real.sq_sqrt hD.le] at hεsq
  nlinarith

/-- The common source decrease coefficient for accepted regularized trials. -/
noncomputable def decreaseCoefficient (η₁ η₂ γ₁ L θ : ℝ) : ℝ :=
  η₁ / 2 * min (γ₁ ^ 2 * (1 - η₂) ^ 2 / L ^ 2) ((1 + 2 * (L + θ))⁻¹)

/-- The coefficient is positive for legal settings and a positive Hessian
Lipschitz normalization. -/
theorem decreaseCoefficient_pos {η₁ η₂ γ₁ L θ : ℝ}
    (hη : 0 < η₁) (hη₂ : η₂ < 1) (hγ : 0 < γ₁) (hL : 0 < L) (hθ : 0 ≤ θ) :
    0 < decreaseCoefficient η₁ η₂ γ₁ L θ := by
  unfold decreaseCoefficient
  have hh : 0 < 1 - η₂ := sub_pos.mpr hη₂
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Run
variable {f : E → ℝ} {x s u : ℕ → E} {μ Δ ρ : ℕ → ℝ}
  {η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ L : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}

/-- Accepted interior steps give sufficient objective decrease at the printed
minimum of the cubic regularization scale and squared next-gradient scale. -/
theorem successful_decrease_interior
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) (ha : η₁ ≤ ρ i) (hs : ‖s i‖ < Δ i) :
    decreaseCoefficient η₁ η₂ γ₁ L θ *
      min (ε ^ 3) (‖gradient f (x (i + 1))‖ ^ 2 * ε⁻¹) ≤
        f (x i) - f (x (i + 1)) := by
  let D := 1 + 2 * (L + θ)
  have hD : 0 < D := by dsimp [D]; linarith [h.theta_pos]
  have hh := minimum_scale_le_sq (norm_nonneg _) h.regularization_pos hD
    (h.interior_step_lower hf hL hlip hi ha hs)
  have hmin : 0 ≤ min (ε ^ 3) (‖gradient f (x (i + 1))‖ ^ 2 * ε⁻¹) := by
    have hε := h.regularization_pos
    positivity
  have hcoeff : decreaseCoefficient η₁ η₂ γ₁ L θ ≤ η₁ / 2 * D⁻¹ :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith [h.updates.eta1_pos])
  have hfirst := mul_le_mul_of_nonneg_right hcoeff hmin
  have hsecond := mul_le_mul_of_nonneg_left hh (show 0 ≤ η₁ / 2 * D⁻¹ by
    have hη := h.updates.eta1_pos
    positivity)
  have heq : η₁ / 2 * D⁻¹ * (D * ε * ‖s i‖ ^ 2) =
      η₁ / 2 * ε * ‖s i‖ ^ 2 := by field_simp
  rw [heq] at hsecond
  exact (hfirst.trans hsecond).trans (h.successful_decrease_step hi ha)

/-- Accepted boundary steps give sufficient objective decrease at the cubic
regularization scale by the radius floor derived from actual updates. -/
theorem successful_decrease_boundary
    (h : Run f x s u μ Δ ρ η₁ η₂ γ₁ γ₂ γ₃ θ ε ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 1 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) (ha : η₁ ≤ ρ i) (hs : ‖s i‖ = Δ i) :
    decreaseCoefficient η₁ η₂ γ₁ L θ * ε ^ 3 ≤ f (x i) - f (x (i + 1)) := by
  let R := (1 - η₂) * γ₁ / L
  have hη := h.updates.eta1_pos
  have hγ := h.updates.gamma1_pos
  have hη₂ : 0 < 1 - η₂ := sub_pos.mpr h.updates.eta2_lt_one
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hε := h.regularization_pos
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hr := h.toModelTrace.radius_floor hf hL hlip hi.le
  have hsq := pow_le_pow_left₀ (mul_nonneg hR hε.le) hr 2
  rw [← hs] at hsq
  have hcoeff : decreaseCoefficient η₁ η₂ γ₁ L θ ≤ η₁ / 2 * R ^ 2 := by
    unfold decreaseCoefficient
    have heq : γ₁ ^ 2 * (1 - η₂) ^ 2 / L ^ 2 = R ^ 2 := by dsimp [R]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
  have hfirst := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hε.le 3)
  have hsecond := mul_le_mul_of_nonneg_left hsq (show 0 ≤ η₁ / 2 * ε by positivity)
  have hb : η₁ / 2 * R ^ 2 * ε ^ 3 ≤ η₁ / 2 * ε * ‖s i‖ ^ 2 := by
    nlinarith [hsecond]
  exact (hfirst.trans hb).trans (h.successful_decrease_step hi ha)

end Run
end RegularizedTrustRegion
