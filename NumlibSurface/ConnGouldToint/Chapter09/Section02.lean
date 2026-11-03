import NumlibSurface.ConnGouldToint.Chapter09.Section01
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # First-order criticality transfer -/

open Filter Topology

namespace ConnGouldToint.Chapter09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lemma 9.2.4, with the eventual accepted-model condition of Step 1 made explicit.
The sequences may already be restricted to the subsequence in (9.2.6). -/
theorem lemma_9_2_4 {f : E → ℝ} (hf : ContDiff ℝ 2 f) {m : ℕ → E → ℝ}
    (hm : ∀ k, Differentiable ℝ (m k)) (hDm : ∀ k, Differentiable ℝ (fderiv ℝ (m k)))
    {x : ℕ → E} {δ : ℕ → ℝ} {κ Bf Bm μ : ℝ} (hκ : 0 < κ)
    (hBf : 0 ≤ Bf) (hBm : 0 ≤ Bm)
    (hF : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ Bf)
    (hM : ∀ k z, ‖fderiv ℝ (fderiv ℝ (m k)) z‖ ≤ Bm)
    (hvalid : ∀ᶠ k in atTop, 0 < δ k ∧ δ k ≤ μ * ‖fderiv ℝ (m k) (x k)‖ ∧
      modelValidOnBall f (m k) (x k) (δ k) κ)
    (hg : Tendsto (fun k ↦ ‖fderiv ℝ (m k) (x k)‖) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ‖fderiv ℝ f (x k)‖) atTop (𝓝 0) := by
  let C := 2 * κ + (Bf + Bm) / 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun k ↦ (1 + C * μ) * ‖fderiv ℝ (m k) (x k)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hg (f := fun _ ↦ 1 + C * μ)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hvalid] with k hk
  have he := theorem_9_1_1 hf (hm k) (hDm k) hk.1 hκ hBf hBm hF (hM k) hk.2.2
  let a := fderiv ℝ f (x k)
  let b := fderiv ℝ (m k) (x k)
  have hab : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    simpa only [sub_add_cancel] using norm_add_le (a - b) b
  change ‖a‖ ≤ (1 + C * μ) * ‖b‖
  calc
    ‖a‖ ≤ ‖a - b‖ + ‖b‖ := hab
    _ ≤ C * δ k + ‖b‖ := add_le_add he le_rfl
    _ ≤ C * (μ * ‖b‖) + ‖b‖ := add_le_add (mul_le_mul_of_nonneg_left hk.2.1 hC) le_rfl
    _ = _ := by ring

end ConnGouldToint.Chapter09
