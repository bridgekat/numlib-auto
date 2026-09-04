import Numlib.Nonlinear.FixedPoint
import Numlib.Analysis.NormedRing.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Newton's method in Banach spaces

`Newton.step F F' x = x - (F' x)⁻¹ (F x)` with `ContinuousLinearMap.inverse` (`0` when `F' x` is
not invertible), local quadratic convergence when `F'(x*)` is invertible and `F'` is Lipschitz
(Atkinson–Han Thm 5.3.? / Kress Thm 6.? / Saad-style `‖e_{k+1}‖ ≤ (L ‖F'(x*)⁻¹‖ / 2) ‖e_k‖²`), and
the Newton–Kantorovich theorem with the a priori bound (AH Thm 5.3.?; Kress Thm 6.?).
-/

open Filter Topology

namespace Newton

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- One Newton step `x ↦ x - (F' x)⁻¹ (F x)`. -/
noncomputable def step (Fn : E → F) (F' : E → E →L[𝕜] F) (x : E) : E :=
  x - (F' x).inverse (Fn x)

/-- The Newton iterates. -/
noncomputable def iterate (Fn : E → F) (F' : E → E →L[𝕜] F) (x₀ : E) (k : ℕ) : E :=
  (step Fn F')^[k] x₀

theorem iterate_succ (Fn : E → F) (F' : E → E →L[𝕜] F) (x₀ : E) (k : ℕ) :
    iterate Fn F' x₀ (k + 1) = step Fn F' (iterate Fn F' x₀ k) := by
  sorry

/-- A root is a fixed point of the Newton step. -/
theorem step_eq_self_of_eq_zero (Fn : E → F) (F' : E → E →L[𝕜] F) {x : E} (hx : Fn x = 0) :
    step Fn F' x = x := by
  sorry

section Quadratic

variable [CompleteSpace E] [CompleteSpace F]

/-- Local quadratic convergence (AH Thm 5.3.?, Kress Thm 6.?): if `F` is differentiable near a
root `x*` with `F'(x*)` invertible (inverse `e`) and `F'` is `L`-Lipschitz on a ball, then on a
smaller ball the Newton step satisfies `‖step x - x*‖ ≤ C ‖x - x*‖²`. -/
theorem exists_ball_norm_step_sub_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E}
    (hstar : Fn xstar = 0) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' xstar) {r L : ℝ}
    (hr : 0 < r) (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, ∃ C : ℝ, ∀ x ∈ Metric.ball xstar δ,
      ‖step Fn F' x - xstar‖ ≤ C * ‖x - xstar‖ ^ 2 := by
  sorry

/-- The explicit constant: `‖step x - x*‖ ≤ (L ‖(F' x)⁻¹‖ / 2) ‖x - x*‖²` whenever `F' x` is
invertible on the segment. -/
theorem norm_step_sub_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} (hstar : Fn xstar = 0)
    {r L : ℝ} (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {x : E} (hx : x ∈ Metric.ball xstar r) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x) :
    ‖step Fn F' x - xstar‖ ≤ L * ‖(e.symm : F →L[𝕜] E)‖ / 2 * ‖x - xstar‖ ^ 2 := by
  sorry

/-- Local convergence: from every `x₀` in a small ball, the Newton iterates converge to `x*`. -/
theorem tendsto_iterate {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} (hstar : Fn xstar = 0)
    (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' xstar) {r L : ℝ} (hr : 0 < r)
    (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, ∀ x₀ ∈ Metric.ball xstar δ,
      Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar) := by
  sorry

/-- Newton–Kantorovich (AH Thm 5.3.?, Kress Thm 6.?): if `‖(F' x₀)⁻¹‖ ≤ β`,
`‖(F' x₀)⁻¹ F x₀‖ ≤ η`, `F'` is `L`-Lipschitz on the ball of radius `r` around `x₀`,
`h := β L η ≤ 1/2` and `t* := (1 - √(1 - 2h)) / (β L) ≤ r`, then the Newton iterates stay in the
ball, converge to a root `x*` with `‖x* - x₀‖ ≤ t*`, and
`‖x_k - x*‖ ≤ (2h)^(2^k) η / (2^k h)` (a priori bound, `h > 0`). -/
theorem kantorovich {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r β η L : ℝ} (hβ : 0 < β)
    (hL : 0 < L) (hη : 0 ≤ η) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hh : β * L * η ≤ 1 / 2) (hr : (1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L) ≤ r) :
    ∃ xstar ∈ Metric.closedBall x₀ ((1 - Real.sqrt (1 - 2 * (β * L * η))) / (β * L)),
      Fn xstar = 0 ∧ Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar) ∧
      (∀ k, iterate Fn F' x₀ k ∈ Metric.closedBall x₀ r) ∧
      (0 < β * L * η → ∀ k, ‖iterate Fn F' x₀ k - xstar‖ ≤
        (2 * (β * L * η)) ^ (2 ^ k) * η / (2 ^ k * (β * L * η))) := by
  sorry

end Quadratic

end Newton
