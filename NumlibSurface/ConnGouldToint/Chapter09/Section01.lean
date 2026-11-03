import Numlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Extr

/-! # Conditional models -/

open Filter Topology

namespace ConnGouldToint.Chapter09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Model validity on the ball (9.1.1) with the prescribed error constant in (9.1.2). -/
def modelValidOnBall (f m : E → ℝ) (x : E) (δ κ : ℝ) : Prop :=
  ∀ z ∈ Metric.closedBall x δ, |f z - m z| ≤ κ * δ ^ 2

private theorem abs_remainder_le {f : E → ℝ} (hf : Differentiable ℝ f)
    (hd : Differentiable ℝ (fderiv ℝ f)) {B : ℝ}
    (hB : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B) (x s : E) :
    |f (x + s) - (f x + fderiv ℝ f x s)| ≤ (1 / 2 : ℝ) * B * ‖s‖ ^ 2 := by
  rw [← Real.norm_eq_abs]
  exact norm_sub_firstOrder_le_of_hessian_bound
    (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ x) (Set.mem_univ (x + s))
    (fun z _ ↦ hf z) (fun z _ ↦ hd z) (fun z _ ↦ hB z)

/-- Theorem 9.1.1. A conditionally valid model has gradient error of order δ
under uniform Hessian bounds. The ball radius must be positive. -/
theorem theorem_9_1_1 {f m : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hm : Differentiable ℝ m) (hDm : Differentiable ℝ (fderiv ℝ m))
    {x : E} {δ κ Bf Bm : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM : ∀ z, ‖fderiv ℝ (fderiv ℝ m) z‖ ≤ Bm)
    (hv : modelValidOnBall f m x δ κ) :
    ‖fderiv ℝ f x - fderiv ℝ m x‖ ≤ (2 * κ + (Bf + Bm) / 2) * δ := by
  let D := fderiv ℝ f x - fderiv ℝ m x
  apply D.opNorm_le_bound (by positivity)
  intro d
  by_cases hd : d = 0
  · simp [hd]
  have hn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let s := (δ / ‖d‖) • d
  have hs : ‖s‖ = δ := by
    rw [show s = (δ / ‖d‖) • d from rfl, norm_smul,
      Real.norm_of_nonneg (by positivity)]
    exact div_mul_cancel₀ _ hn.ne'
  have h₀ := abs_le.mp (hv x (Metric.mem_closedBall_self hδ.le))
  have h₁ := abs_le.mp (hv (x + s) (by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hs]))
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h₂ := abs_le.mp (abs_remainder_le (hf.differentiable (by norm_num))
    (hDf.differentiable (by norm_num)) hF x s)
  have h₃ := abs_le.mp (abs_remainder_le hm hDm hM x s)
  rw [hs] at h₂ h₃
  have hstep : ‖D s‖ ≤ (2 * κ + (Bf + Bm) / 2) * δ ^ 2 := by
    rw [Real.norm_eq_abs, abs_le]
    change -((2 * κ + (Bf + Bm) / 2) * δ ^ 2) ≤ fderiv ℝ f x s - fderiv ℝ m x s ∧
      fderiv ℝ f x s - fderiv ℝ m x s ≤ (2 * κ + (Bf + Bm) / 2) * δ ^ 2
    constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2]
  rw [show s = (δ / ‖d‖) • d from rfl, map_smul, norm_smul,
    Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div] at hstep
  apply (mul_le_mul_iff_of_pos_left hδ).mp
  calc
    δ * ‖D d‖ ≤ ((2 * κ + (Bf + Bm) / 2) * δ ^ 2) * ‖d‖ := (div_le_iff₀ hn).mp hstep
    _ = _ := by ring

/-- At radius zero, the model validity bound gives no control over gradient error. -/
theorem zero_radius_counterexample :
    modelValidOnBall (fun x : ℝ ↦ x) (fun _ ↦ 0) 0 0 1 ∧
      fderiv ℝ (fun x : ℝ ↦ x) 0 ≠ fderiv ℝ (fun _ : ℝ ↦ (0 : ℝ)) 0 := by
  constructor
  · intro z hz
    have hz₀ : z = 0 := by simpa using hz
    simp [hz₀]
  · change fderiv ℝ (id : ℝ → ℝ) 0 ≠ fderiv ℝ (Function.const ℝ (0 : ℝ)) 0
    rw [fderiv_id, fderiv_const]
    intro h
    have := DFunLike.congr_fun h (1 : ℝ)
    norm_num at this

/-- The selected-trial acceptance ratio (9.1.5) uses the model decrease at the original trial. -/
noncomputable def selectedTrialRatio (f m : E → ℝ) (x trial selected : E) : ℝ :=
  (f x - f selected) / (m x - m trial)

/-- Successful indices in Algorithm 9.1.1. -/
def conditionalSuccessful (η₀ : ℝ) (ρhat : ℕ → ℝ) : Set ℕ :=
  {k | η₀ ≤ ρhat k}

/-- Reference-radius reset indices (9.1.7). -/
def referenceRadiusResets (η₀ : ℝ) (ρhat : ℕ → ℝ) (valid : ℕ → Prop) : Set ℕ :=
  {k | η₀ ≤ ρhat k ∨ valid k}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Lemma 9.1.2(i). Selection of a minimum over the candidate set preserves acceptance
when that set contains the original trial point. -/
theorem lemma_9_1_2_i {f m : E → ℝ} {x trial selected : E} {candidates : Set E}
    {η₀ η₁ : ℝ} (hη : η₀ ≤ η₁) (hdec : 0 < m x - m trial)
    (hsel : IsMinOn f candidates selected)
    (htrial : η₁ ≤ selectedTrialRatio f m x trial trial → trial ∈ candidates)
    (hρ : η₁ ≤ selectedTrialRatio f m x trial trial) :
    η₀ ≤ selectedTrialRatio f m x trial selected := by
  exact hη.trans (hρ.trans
    (div_le_div_of_nonneg_right (sub_le_sub_left ((isMinOn_iff.mp hsel) trial (htrial hρ)) _)
      hdec.le))

/-- Lemma 9.1.2(i), the inclusion of successful indices in the reset set. -/
theorem conditionalSuccessful_subset_referenceRadiusResets (η₀ : ℝ)
    (ρhat : ℕ → ℝ) (valid : ℕ → Prop) :
    conditionalSuccessful η₀ ρhat ⊆ referenceRadiusResets η₀ ρhat valid :=
  fun _ hk ↦ Or.inl hk

/-- Lemma 9.1.2(iii). A failed final criticality test forces geometric shrinkage
of successive model gradients. The proof uses each model's actual validity radius. -/
theorem lemma_9_1_2_iii {f : E → ℝ} (hf : ContDiff ℝ 2 f) {m : ℕ → E → ℝ}
    (hm : ∀ k, Differentiable ℝ (m k)) (hDm : ∀ k, Differentiable ℝ (fderiv ℝ (m k)))
    {x : E} {α μ κ Bf Bm : ℝ} (hα : 0 < α) (hα₁ : α < 1) (hμ : 0 < μ)
    (hκ : 0 < κ) (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM : ∀ k z, ‖fderiv ℝ (fderiv ℝ (m k)) z‖ ≤ Bm)
    (hpos : ∀ k, 0 < ‖fderiv ℝ (m k) x‖)
    (hvalid : ∀ k, modelValidOnBall f (m (k + 1)) x (α * μ * ‖fderiv ℝ (m k) x‖) κ)
    (hfailed : ∀ k r, 0 < r → r ≤ μ * ‖fderiv ℝ (m (k + 1)) x‖ →
      ¬ modelValidOnBall f (m (k + 1)) x r κ) :
    fderiv ℝ f x = 0 ∧ Tendsto (fun k ↦ ‖fderiv ℝ (m k) x‖) atTop (𝓝 0) := by
  let g (k : ℕ) := ‖fderiv ℝ (m k) x‖
  have hstep (k : ℕ) : g (k + 1) ≤ α * g k := by
    by_contra! h
    have hle : α * μ * g k ≤ μ * g (k + 1) := by
      rw [mul_comm α μ, mul_assoc]
      exact mul_le_mul_of_nonneg_left h.le hμ.le
    exact hfailed k _ (mul_pos (mul_pos hα hμ) (hpos k)) hle (hvalid k)
  have hgeom (k : ℕ) : g k ≤ α ^ k * g 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      apply (hstep k).trans
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left ih hα.le
  have hpow : Tendsto (fun k : ℕ ↦ α ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα₁
  have hg : Tendsto g atTop (𝓝 0) := by
    refine squeeze_zero (fun k ↦ norm_nonneg _) hgeom ?_
    simpa only [zero_mul] using hpow.mul_const (g 0)
  refine ⟨norm_le_zero_iff.mp ?_, hg⟩
  let C := 2 * κ + (Bf + Bm) / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun k ↦ (C * (α * μ) + α) * g k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hg.const_mul (C * (α * μ) + α)
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
  intro k
  have he := theorem_9_1_1 hf (hm (k + 1)) (hDm (k + 1))
    (mul_pos (mul_pos hα hμ) (hpos k)) hκ hBf hBm hF (hM (k + 1)) (hvalid k)
  let a := fderiv ℝ f x
  let b := fderiv ℝ (m (k + 1)) x
  calc
    ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a - b) b
    _ ≤ C * (α * μ * g k) + α * g k := add_le_add he (hstep k)
    _ = _ := by ring

end ConnGouldToint.Chapter09
