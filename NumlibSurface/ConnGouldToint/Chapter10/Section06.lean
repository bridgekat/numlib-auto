import NumlibSurface.ConnGouldToint.Chapter06.Section06

/-! # Dynamic accuracy in objective evaluations -/

open Filter Topology
open ConnGouldToint.Chapter06

namespace ConnGouldToint.Chapter10

/-- Both objective error tolerances are at most a fixed fraction of the
predicted decrease, as required by (10.6.2). -/
def HasDecreaseAccuracy (η predicted centerTol trialTol : ℝ) : Prop :=
  max centerTol trialTol ≤ η * predicted

/-- Accepted steps with accurate objective evaluations reduce the exact
objective by at least `η₁ - 2 * η₀` times the predicted decrease. -/
theorem actual_decrease_of_accurate_ratio
    {center trial centerApprox trialApprox centerTol trialTol predicted η₀ η₁ : ℝ}
    (hp : 0 < predicted)
    (hc : |centerApprox - center| ≤ centerTol) (ht : |trialApprox - trial| ≤ trialTol)
    (hacc : HasDecreaseAccuracy η₀ predicted centerTol trialTol)
    (hratio : η₁ ≤ (centerApprox - trialApprox) / predicted) :
    (η₁ - 2 * η₀) * predicted ≤ center - trial := by
  have hr := (le_div_iff₀ hp).mp hratio
  have h₁ := (le_abs_self (centerApprox - center)).trans
    (hc.trans ((le_max_left _ _).trans hacc))
  have h₂ := (neg_abs_le (trialApprox - trial)).trans' (neg_le_neg
    (ht.trans ((le_max_right _ _).trans hacc)))
  linarith only [hr, h₁, h₂]

private theorem eventually_decreaseAccuracy_of_floor {η d : ℝ} (hη : 0 < η) (hd : 0 < d)
    {predicted centerTol trialTol : ℕ → ℝ}
    (hp : ∀ᶠ j in atTop, d ≤ predicted j)
    (ht : Tendsto (fun j ↦ max (centerTol j) (trialTol j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, HasDecreaseAccuracy η (predicted j) (centerTol j) (trialTol j) := by
  filter_upwards [hp, ht.eventually_lt_const (mul_pos hη hd)] with j hj hsmall
  exact hsmall.le.trans (mul_le_mul_of_nonneg_left hj hη.le)

/-- Lemma 10.6.1. During refinement the center and radius stay fixed.
Gradient agreement supplies a positive model-gradient floor at a
first-order noncritical center. At a first-order critical center with
negative curvature, Hessian agreement supplies a negative model
curvature margin. In either case, vanishing tolerances pass the test. -/
theorem lemma_10_6_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E) (gModel : ℕ → E) (τ : ℕ → ℝ) (m : ℕ → E → ℝ) (x : E) (s : ℕ → E)
    (β : ℕ → ℝ) (centerTol trialTol : ℕ → ℝ) {η Δ B κ₁ κ₂ : ℝ}
    (hη : 0 < η) (hΔ : 0 < Δ) (hB : 0 < B)
    (hβ : ∀ j, 0 < β j ∧ β j ≤ B)
    (hgrad : ∃ e ∈ Set.Ico (0 : ℝ) 1, ∀ j, ‖gModel j - g‖ ≤ e * ‖g‖)
    (hfirst : ∀ j, HasSufficientModelDecrease (m j) x (s j) (gModel j) (β j) Δ κ₁)
    (hsecond : g = 0 → ∀ j, HasNegativeCurvatureDecrease (m j) x (s j) (τ j) Δ κ₂)
    (hcurv : g = 0 → ∃ a > (0 : ℝ), ∀ᶠ j in atTop, τ j ≤ -a)
    (ht : Tendsto (fun j ↦ max (centerTol j) (trialTol j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop,
      HasDecreaseAccuracy η (m j x - m j (x + s j)) (centerTol j) (trialTol j) := by
  by_cases hg : g = 0
  · obtain ⟨a, ha, hτ⟩ := hcurv hg
    have hκ := (hsecond hg 0).1
    have hd : 0 < κ₂ * a * min (a ^ 2) (Δ ^ 2) :=
      mul_pos (mul_pos hκ ha) (lt_min (sq_pos_of_pos ha) (sq_pos_of_pos hΔ))
    exact eventually_decreaseAccuracy_of_floor hη hd
      (hτ.mono fun j hj ↦ negativeCurvatureDecrease_lower_bound (hsecond hg j)
        ha hΔ.le le_rfl hj) ht
  · obtain ⟨e, he, he'⟩ := hgrad
    let a := (1 - e) * ‖g‖
    have ha : 0 < a := mul_pos (sub_pos.mpr he.2) (norm_pos_iff.mpr hg)
    have hκ := (hfirst 0).1.1
    have hd : 0 < κ₁ * a * min (a / B) Δ :=
      mul_pos (mul_pos hκ ha) (lt_min (div_pos ha hB) hΔ)
    refine eventually_decreaseAccuracy_of_floor hη hd (Eventually.of_forall fun j ↦ ?_) ht
    have hgn : a ≤ ‖gModel j‖ := by
      have hh := norm_sub_le (gModel j) (gModel j - g)
      rw [sub_sub_cancel] at hh
      dsimp [a]
      linarith only [hh, he' j]
    have hh := div_le_div₀ (norm_nonneg _) hgn (hβ j).1 (hβ j).2
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hgn hκ.le) (min_le_min hh le_rfl)
      (le_min (div_nonneg ha.le hB.le) hΔ.le) (by positivity)).trans (hfirst j).2

/-- A uniform contraction factor gives the vanishing tolerances used
by the accuracy-refinement termination proof. -/
theorem lemma_10_6_1_of_geometric_refinement {η d q : ℝ} (hη : 0 < η) (hd : 0 < d)
    (hq : 0 ≤ q) (hq' : q < 1) {predicted centerTol trialTol : ℕ → ℝ}
    (ht₀ : ∀ j, 0 ≤ max (centerTol j) (trialTol j))
    (ht : ∀ j, max (centerTol (j + 1)) (trialTol (j + 1)) ≤
      q * max (centerTol j) (trialTol j))
    (hp : ∀ᶠ j in atTop, d ≤ predicted j) :
    ∃ j, HasDecreaseAccuracy η (predicted j) (centerTol j) (trialTol j) := by
  have hbound (j : ℕ) : max (centerTol j) (trialTol j) ≤
      q ^ j * max (centerTol 0) (trialTol 0) := by
    induction j with
    | zero => simp
    | succ j ih =>
      exact (ht j).trans ((mul_le_mul_of_nonneg_left ih hq).trans_eq (by rw [pow_succ]; ring))
  have hlim : Tendsto (fun j ↦ max (centerTol j) (trialTol j)) atTop (𝓝 0) := by
    apply squeeze_zero ht₀ hbound
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq').mul_const
      (max (centerTol 0) (trialTol 0))
  exact (eventually_decreaseAccuracy_of_floor hη hd hp hlim).exists

end ConnGouldToint.Chapter10
