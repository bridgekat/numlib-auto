import Numlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Ring

/-! # Conditional models -/

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
  have h₁ : ContDiff ℝ 1 f := contDiff_one_iff_fderiv.mpr ⟨hf, hd.continuous⟩
  refine norm_sub_firstOrder_le_of_lipschitzAt_segment isOpen_univ h₁.contDiffOn
    (fun _ _ ↦ Set.mem_univ _) (fun z _ ↦ ?_)
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hd z)
    (fun z _ ↦ hB z) (convex_univ : Convex ℝ (Set.univ : Set E))
    (Set.mem_univ x) (Set.mem_univ z)

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

end ConnGouldToint.Chapter09
