import Numlib.Optimization.ModelBased.QuadraticModel
import NumlibSurface.ConnGouldToint.Chapter17.Section01

/-! # Choosing the initial radius -/

open scoped RealInnerProductSpace

namespace ConnGouldToint.Chapter17

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The two initial-radius choices in (17.2.1). -/
noncomputable def initialRadiusChoices (g : E) : ℝ × ℝ :=
  (1, ‖g‖ / 10)

/-- The right-hand side of (17.2.2) is the parameter of the unnormalized gradient ray. -/
noncomputable def cauchyRayParameter (g : E) (H : E →L[ℝ] E) : ℝ :=
  ‖g‖ ^ 2 / ⟪g, H g⟫

/-- Corrected (17.2.2). The initial radius is the norm of the minimizing step. -/
noncomputable def cauchyInitialRadius (g : E) (H : E →L[ℝ] E) : ℝ :=
  cauchyRayParameter g H * ‖g‖

/-- For positive ray curvature, the corrected radius is the length of the
unconstrained quadratic minimizer on the steepest-descent ray. -/
theorem cauchyInitialRadius_spec {g : E} {H : E →L[ℝ] E} (hH : 0 < ⟪g, H g⟫) :
    let t := cauchyRayParameter g H
    ‖-(t • g)‖ = cauchyInitialRadius g H ∧
      ∀ u : ℝ, Subproblem.quadModel g H (-(t • g)) ≤
        Subproblem.quadModel g H (-(u • g)) := by
  let t := cauchyRayParameter g H
  have ht : 0 ≤ t := div_nonneg (sq_nonneg _) hH.le
  refine ⟨by rw [norm_neg, norm_smul, Real.norm_of_nonneg ht]; rfl, fun u ↦ ?_⟩
  rw [Optimization.quadModel_neg_smul, Optimization.quadModel_neg_smul]
  have hparam : t * ⟪g, H g⟫ = ‖g‖ ^ 2 := div_mul_cancel₀ _ hH.ne'
  rw [← hparam]
  nlinarith only [mul_nonneg (sq_nonneg (u - t)) hH.le]

/-- The displacement probe (17.2.3) before subtracting it from the base point. -/
noncomputable def initialProbeDisplacement (g : E) (Δ : ℝ) : E :=
  (Δ / ‖g‖) • g

/-- The probe displacement has the given radius for a nonzero gradient. -/
theorem norm_initialProbeDisplacement {g : E} (hg : g ≠ 0) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    ‖initialProbeDisplacement g Δ‖ = Δ := by
  rw [initialProbeDisplacement, norm_smul, Real.norm_of_nonneg (by positivity),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hg)]

/-- The initial probe ratio (17.2.4) for a model that agrees at the base point. -/
noncomputable def initialProbeRatio (f m : E → ℝ) (x d : E) : ℝ :=
  (f x - f (x - d)) / (f x - m (x - d))

/-- Safeguards and agreement tolerances for the initial-radius probe. The shrink
fallback `γ₂` is strictly below one, as required by the first branch of (17.2.7). -/
structure ProbeRadiusParams where
  γ₁ : ℝ
  γ₂ : ℝ
  γ₃ : ℝ
  γ₄ : ℝ
  μ₁ : ℝ
  μ₂ : ℝ
  θ : ℝ
  gamma₁_pos : 0 < γ₁
  gamma₁_le_gamma₂ : γ₁ ≤ γ₂
  gamma₂_lt_one : γ₂ < 1
  one_le_gamma₃ : 1 ≤ γ₃
  gamma₃_le_gamma₄ : γ₃ ≤ γ₄
  theta_pos : 0 < θ
  theta_le_mu₂ : θ ≤ μ₂
  mu₂_lt_mu₁ : μ₂ < μ₁

/-- The poor prediction criterion (17.2.5). -/
abbrev probePredictsBadly (P : ProbeRadiusParams) (ρ : ℝ) : Prop := P.μ₁ < |ρ - 1|

/-- The good prediction criterion (17.2.6). -/
abbrev probePredictsWell (P : ProbeRadiusParams) (ρ : ℝ) : Prop := |ρ - 1| ≤ P.μ₂

/-- The quadratic interpolation factors (17.2.8) and (17.2.9).
The common slope along the probe ray is the negative directional pairing. -/
noncomputable def probeInterpolationFactors (P : ProbeRadiusParams) (a l f₁ m₁ : ℝ) : ℝ × ℝ :=
  (interpolatedRadiusFactor (1 - P.θ) a l f₁ m₁,
    interpolatedRadiusFactor (1 + P.θ) a l f₁ m₁)

/-- The smaller and larger interpolation factors (17.2.10). -/
def probeFactorExtrema (t₁ t₂ : ℝ) : ℝ × ℝ := (min t₁ t₂, max t₁ t₂)

/-- The safeguarded choices in (17.2.11)–(17.2.13). On the shrink branch,
a factor equal to one is inadmissible. If both candidates are at least one,
use the strict shrink fallback. -/
noncomputable def safeguardedProbeFactor (P : ProbeRadiusParams) (ρ t₁ t₂ : ℝ) : ℝ :=
  if probePredictsBadly P ρ then
    if t₁ ∈ Set.Ico P.γ₁ 1 then
      if t₂ ∈ Set.Ico P.γ₁ 1 then max t₁ t₂ else t₁
    else if t₂ ∈ Set.Ico P.γ₁ 1 then t₂
    else if 1 ≤ min t₁ t₂ then P.γ₂ else P.γ₁
  else if probePredictsWell P ρ then
    if max t₁ t₂ < 1 then P.γ₃ else min P.γ₄ (max t₁ t₂)
  else max P.γ₂ (min P.γ₃ (max t₁ t₂))

/-- The safeguarded factor always belongs to its designated interval in (17.2.7). -/
theorem safeguardedProbeFactor_mem (P : ProbeRadiusParams) (ρ t₁ t₂ : ℝ) :
    safeguardedProbeFactor P ρ t₁ t₂ ∈
      (if probePredictsBadly P ρ then Set.Ico P.γ₁ 1
       else if probePredictsWell P ρ then Set.Icc 1 P.γ₄ else Set.Icc P.γ₂ P.γ₃) := by
  unfold safeguardedProbeFactor
  by_cases hb : probePredictsBadly P ρ
  · simp only [ite_eq_left hb]
    split
    · rename_i h₁
      split
      · rename_i h₂
        exact ⟨h₁.1.trans (le_max_left _ _), max_lt h₁.2 h₂.2⟩
      · exact h₁
    · split
      · assumption
      · split
        · exact ⟨P.gamma₁_le_gamma₂, P.gamma₂_lt_one⟩
        · exact ⟨le_rfl, P.gamma₁_le_gamma₂.trans_lt P.gamma₂_lt_one⟩
  · simp only [ite_eq_right hb]
    by_cases hw : probePredictsWell P ρ
    · simp only [ite_eq_left hw]
      split
      · exact ⟨P.one_le_gamma₃, P.gamma₃_le_gamma₄⟩
      · rename_i hn
        exact ⟨le_min (P.one_le_gamma₃.trans P.gamma₃_le_gamma₄) (le_of_not_gt hn), min_le_left _ _⟩
    · simp only [ite_eq_right hw]
      exact ⟨le_max_left _ _, max_le (P.gamma₂_lt_one.le.trans P.one_le_gamma₃) (min_le_left _ _)⟩

/-- The radius update (17.2.7) with the safeguarded interpolation factor. -/
noncomputable def probeRadiusUpdate (P : ProbeRadiusParams) (ρ t₁ t₂ Δ : ℝ) : ℝ :=
  safeguardedProbeFactor P ρ t₁ t₂ * Δ

/-- Recommended probe parameters in (17.2.14). -/
noncomputable def recommendedProbeParams : ProbeRadiusParams where
  γ₁ := 0.0625
  γ₂ := 0.5
  γ₃ := 2
  γ₄ := 5
  μ₁ := 0.5
  μ₂ := 0.35
  θ := 0.25
  gamma₁_pos := by norm_num
  gamma₁_le_gamma₂ := by norm_num
  gamma₂_lt_one := by norm_num
  one_le_gamma₃ := by norm_num
  gamma₃_le_gamma₄ := by norm_num
  theta_pos := by norm_num
  theta_le_mu₂ := by norm_num
  mu₂_lt_mu₁ := by norm_num

/-- The recommended trial and restart limits in (17.2.14). -/
def recommendedProbeLimits : ℕ × ℕ := (4, 1)

end ConnGouldToint.Chapter17
