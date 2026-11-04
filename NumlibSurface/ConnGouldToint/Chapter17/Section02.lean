/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

/-- The point, cached value, radius, and additional objective evaluations
returned by Algorithm 17.2.1. -/
structure InitialRadiusResult (E : Type*) where
  point : E
  value : ℝ
  radius : ℝ
  evaluations : ℕ

private structure RadiusProbePass (E : Type*) where
  bestPoint : E
  bestValue : ℝ
  adequate : ℝ
  radius : ℝ

private noncomputable def radiusProbePass (P : ProbeRadiusParams) (f m : E → ℝ)
    (x g : E) (fx : ℝ) : ℕ → RadiusProbePass E → RadiusProbePass E
  | i, state =>
    let d := initialProbeDisplacement g state.radius
    let trial := x - d
    let fTrial := f trial
    let mTrial := m trial
    let pred := fx - mTrial
    let ρ := (fx - fTrial) / pred
    let next : RadiusProbePass E := {
      bestPoint := if fTrial < state.bestValue then trial else state.bestPoint
      bestValue := min fTrial state.bestValue
      adequate := if pred ≠ 0 ∧ |ρ - 1| ≤ P.μ₁ then max state.adequate state.radius else state.adequate
      radius := state.radius }
    match i with
    | 0 => next
    | i + 1 =>
      let candidates := probeInterpolationFactors P fx (-⟪g, d⟫) fTrial mTrial
      let radius := if pred = 0 then P.γ₂ * state.radius
        else probeRadiusUpdate P ρ candidates.1 candidates.2 state.radius
      radiusProbePass P f m x g fx i { next with radius := radius }

private noncomputable def radiusProbeRestarts (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax : ℕ) :
    ℕ → E → ℝ → ℝ → InitialRadiusResult E
  | j, x, fx, adequate =>
    let Δ := seed x
    if ‖g x‖ = 0 then ⟨x, fx, max Δ adequate, 0⟩
    else
      let pass := radiusProbePass P f (m x) x (g x) fx iMax ⟨x, fx, adequate, Δ⟩
      let result : InitialRadiusResult E := ⟨x, fx, max pass.radius pass.adequate, iMax + 1⟩
      match j with
      | 0 => result
      | j + 1 =>
        if pass.bestValue < fx then
          let later := radiusProbeRestarts P f m g seed iMax j
            pass.bestPoint pass.bestValue pass.adequate
          { later with evaluations := iMax + 1 + later.evaluations }
        else result

/-- Corrected Algorithm 17.2.1. The model, gradient and seed radius are
supplied for each base point. A restart carries forward the best adequate
radius and the cached objective value while consuming one restart.
Each pass probes at most `iMax + 1` radii. A zero gradient stops before
probing. If predicted decrease is zero, the trial cannot qualify as
adequate and a further probe uses the strict shrink fallback. -/
noncomputable def chooseInitialRadius (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax jMax : ℕ) (x : E) :
    InitialRadiusResult E :=
  radiusProbeRestarts P f m g seed iMax jMax x (f x) 0

private theorem radiusProbeRestarts_evaluations_le (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax j : ℕ) (x : E) (fx adequate : ℝ) :
    (radiusProbeRestarts P f m g seed iMax j x fx adequate).evaluations ≤ (iMax + 1) * (j + 1) := by
  induction j generalizing x fx adequate with
  | zero =>
    rw [radiusProbeRestarts]
    split <;> simp
  | succ j ih =>
    rw [radiusProbeRestarts]
    dsimp only
    split
    · exact Nat.zero_le _
    · split
      · rw [Nat.mul_succ, Nat.add_comm ((iMax + 1) * (j + 1))]
        exact Nat.add_le_add_left (ih _ _ _) _
      · exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

/-- The corrected restart and trial bounds give the stated maximum number
of extra objective evaluations. The initial base evaluation is excluded. -/
theorem chooseInitialRadius_evaluations_le (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax jMax : ℕ) (x : E) :
    (chooseInitialRadius P f m g seed iMax jMax x).evaluations ≤ (iMax + 1) * (jMax + 1) :=
  radiusProbeRestarts_evaluations_le P f m g seed iMax jMax x (f x) 0

private theorem radiusProbePass_bestValue (P : ProbeRadiusParams) (f m : E → ℝ)
    (x g : E) (fx : ℝ) (i : ℕ) (state : RadiusProbePass E)
    (hstate : state.bestValue = f state.bestPoint) :
    let result := radiusProbePass P f m x g fx i state
    result.bestValue = f result.bestPoint := by
  induction i generalizing state with
  | zero =>
    rw [radiusProbePass]
    dsimp only
    split
    · rename_i h
      exact min_eq_left h.le
    · rename_i h
      exact (min_eq_right (le_of_not_gt h)).trans hstate
  | succ i ih =>
    rw [radiusProbePass]
    dsimp only
    apply ih
    dsimp only
    split
    · rename_i h
      exact min_eq_left h.le
    · rename_i h
      exact (min_eq_right (le_of_not_gt h)).trans hstate

private theorem radiusProbeRestarts_value_spec (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax j : ℕ)
    (x : E) (fx adequate : ℝ) (hfx : fx = f x) :
    let result := radiusProbeRestarts P f m g seed iMax j x fx adequate
    result.value = f result.point ∧ result.value ≤ fx := by
  induction j generalizing x fx adequate with
  | zero =>
    rw [radiusProbeRestarts]
    dsimp only
    split <;> exact ⟨hfx, le_rfl⟩
  | succ j ih =>
    rw [radiusProbeRestarts]
    dsimp only
    split
    · exact ⟨hfx, le_rfl⟩
    · split
      · rename_i hbetter
        have hb := radiusProbePass_bestValue P f (m x) x (g x) fx iMax
          ⟨x, fx, adequate, seed x⟩ hfx
        let pass := radiusProbePass P f (m x) x (g x) fx iMax ⟨x, fx, adequate, seed x⟩
        have h := ih pass.bestPoint pass.bestValue pass.adequate hb
        exact ⟨h.1, h.2.trans hbetter.le⟩
      · exact ⟨hfx, le_rfl⟩

/-- The returned value belongs to the returned point, and restarts can
only improve the initial objective value. -/
theorem chooseInitialRadius_value_spec (P : ProbeRadiusParams) (f : E → ℝ)
    (m : E → E → ℝ) (g : E → E) (seed : E → ℝ) (iMax jMax : ℕ) (x : E) :
    let result := chooseInitialRadius P f m g seed iMax jMax x
    result.value = f result.point ∧ result.value ≤ f x :=
  radiusProbeRestarts_value_spec P f m g seed iMax jMax x (f x) 0 rfl

end ConnGouldToint.Chapter17
