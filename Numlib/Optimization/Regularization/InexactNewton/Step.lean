import Numlib.Optimization.Regularization.InexactNewton.Parameter

/-!
# Step lower bounds for inexact regularized Newton executions

The actual shifted-model first derivative and the parameter cap control the
next true gradient. A genuine least-Rayleigh certificate on the actual model
subspace gives the projected-curvature step bound from the primitive model
curvature test. The latter bound uses current, rather than next, curvature.
-/

namespace InexactRegularizedNewton
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Run
variable {f : E → ℝ} {x s : ℕ → E} {V : ℕ → Submodule ℝ E}
  {μ ℓ σL σU ρ : ℕ → ℝ}
  {η γ₁ γ₂ σmin σmax κ₁ κ₂ κ₃ κ₄ ε₁ L : ℝ} {ε₂ : WithTop ℝ} {N : ℕ}

/-- The actual trial derivative is controlled by the square of the step norm,
with precisely the upper regularization cap and source model-gradient constant. -/
theorem trial_derivative_le
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) :
    ‖fderiv ℝ f (x i + s i)‖ ≤
      (L / 2 + 2 * upperBound σmax γ₂ η κ₂ L + κ₃) * ‖s i‖ ^ 2 := by
  let S := upperBound σmax γ₂ η κ₂ L
  have hs := h.step i hi.le (Or.inl hi)
  have hℓ := h.multiplier_le hf hL hlip hi.le (Or.inl hi)
  have hstat : ‖fderiv ℝ (model f (x i) (ℓ i)) (s i)‖ ≤
      (2 * (S + κ₃)) / 2 * ‖s i‖ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hℓ (norm_nonneg (s i))
    nlinarith [hs.stationary]
  have hb := RegularizedTrustRegion.trial_derivative_le hf hs.multiplier_nonneg hlip
    (x i) (s i) hstat
  have hm := mul_le_mul_of_nonneg_right hℓ (norm_nonneg (s i))
  nlinarith

/-- Every accepted iRN trial has the exact squared-step lower bound in terms
of the actual next gradient norm. -/
theorem step_lower
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i < N) (ha : η ≤ ρ i) :
    2 / (L + 4 * upperBound σmax γ₂ η κ₂ L + 2 * κ₃) *
      ‖gradient f (x (i + 1))‖ ≤ ‖s i‖ ^ 2 := by
  have hS := h.upperBound_pos (L := L)
  have hκ := h.kappa3_pos
  have hden : 0 < L + 4 * upperBound σmax γ₂ η κ₂ L + 2 * κ₃ := by positivity
  have hb := h.trial_derivative_le hf hL hlip hi
  have hn : ‖gradient f (x (i + 1))‖ = ‖fderiv ℝ f (x i + s i)‖ := by
    rw [h.point_update i hi, ite_eq_left ha, ← toDual_gradient,
      (InnerProductSpace.toDual ℝ E).norm_map]
  rw [hn, div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- The actual projected model-curvature test implies the source's current
least-curvature step bound on any given subspace. No success assumption is needed. -/
theorem projected_step_lower
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i ≤ N) (hcomputed : i < N ∨ ε₂ ≠ ⊤)
    {ν : ℝ} (he : IsLeastCurvatureOn f (x i) (V i) ν)
    (hcurv : ∀ v : E, v ∈ V i → ‖v‖ = 1 →
      -κ₄ * ‖s i‖ ≤
        iteratedFDeriv ℝ 2 (model f (x i) (ℓ i)) (s i) (fun _ => v)) :
    -(κ₄ + upperBound σmax γ₂ η κ₂ L)⁻¹ * ν ≤ ‖s i‖ := by
  obtain ⟨v, hv, hvn, hval⟩ := he.attains
  have hh := hcurv v hv hvn
  rw [RegularizedTrustRegion.iteratedFDeriv_two_model_diag hf.contDiffAt, hvn,
    one_pow, mul_one, hval] at hh
  have hℓ := h.multiplier_le hf hL hlip hi hcomputed
  have hκ := h.kappa4_pos
  have hS := h.upperBound_pos (L := L)
  have hden : 0 < κ₄ + upperBound σmax γ₂ η κ₂ L := by positivity
  have hb : -ν ≤ ‖s i‖ * (κ₄ + upperBound σmax γ₂ η κ₂ L) := by nlinarith
  have hd := (div_le_iff₀ hden).mpr hb
  convert hd using 1
  ring

/-- In finite-second-order mode both the true least-curvature certificate and
the projected model test are supplied by the actual algorithm. -/
theorem finite_projected_step_lower
    (h : Run f x s V μ ℓ σL σU ρ η γ₁ γ₂ σmin σmax
      κ₁ κ₂ κ₃ κ₄ ε₁ ε₂ N)
    (hf : ContDiff ℝ 2 f) (hL : 0 ≤ L)
    (hlip : ∀ y z, ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f z‖ ≤
      L * ‖y - z‖) {i : ℕ} (hi : i ≤ N) (hfinite : ε₂ ≠ ⊤) :
    -(κ₄ + upperBound σmax γ₂ η κ₂ L)⁻¹ * μ i ≤ ‖s i‖ :=
  h.projected_step_lower hf hL hlip hi (Or.inr hfinite)
    (h.least_curvature i hi hfinite) (h.curvature i hi hfinite)

end Run
end InexactRegularizedNewton
