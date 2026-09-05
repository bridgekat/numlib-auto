import Numlib.Nonlinear.FixedPoint
import Numlib.Analysis.Normed.Ring.Inverse
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
    iterate Fn F' x₀ (k + 1) = step Fn F' (iterate Fn F' x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- A root is a fixed point of the Newton step. -/
theorem step_eq_self_of_eq_zero (Fn : E → F) (F' : E → E →L[𝕜] F) {x : E} (hx : Fn x = 0) :
    step Fn F' x = x := by
  simp [step, hx]

section Quadratic

/-! ### Local quadratic convergence

The theorems below carry two hypotheses that are not in the informal statement:
`[IsRCLikeNormedField 𝕜]` and `[NormedSpace ℝ E]`.  They are needed because every proof here goes
through the mean value inequality `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'`, which is
available only over `ℝ`/`ℂ`.  This is not a defect of the proofs: over a general
`NontriviallyNormedField` the statements are false.  For a counterexample take
`𝕜 = E = F = 𝔽ₚ((t))`, `Fn x = x + x ^ p` and `F' x = 1`.  In characteristic `p`,
`(x + h) ^ p = x ^ p + h ^ p` and `‖h ^ p‖ = ‖h‖ ^ p = o (‖h‖)`, so `HasFDerivAt Fn 1 x` for every
`x`; `F'` is constant, hence `L`-Lipschitz with `L = 0`; and `Fn 0 = 0`.  With `e = 1` the
conclusion of `norm_step_sub_le` reads `‖step Fn F' x‖ ≤ 0`, while
`step Fn F' x = x - (x + x ^ p) = -x ^ p ≠ 0` for `x ≠ 0`. -/

variable [CompleteSpace E] [CompleteSpace F] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E]

omit [CompleteSpace F] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
/-- Perturbation (Neumann) lemma: an operator within `1 / (2 K)` of an invertible one, where `K`
bounds the norm of the inverse, is itself invertible, with inverse of norm at most `2 K`. -/
private theorem exists_equiv_of_norm_le {A : E →L[𝕜] F} (e : E ≃L[𝕜] F) {K : ℝ}
    (hK : ‖(e.symm : F →L[𝕜] E)‖ ≤ K) (h : K * ‖(e : E →L[𝕜] F) - A‖ ≤ 1 / 2) :
    ∃ B : E ≃L[𝕜] F, (B : E →L[𝕜] F) = A ∧ ∀ y : F, ‖B.symm y‖ ≤ 2 * K * ‖y‖ := by
  set S : F →L[𝕜] E := (e.symm : F →L[𝕜] E) with hS
  set T : E →L[𝕜] E := S ∘L A with hT
  have hdiff : (1 : E →L[𝕜] E) - T = S ∘L ((e : E →L[𝕜] F) - A) := by
    ext z
    simp [hT, hS]
  have hle : ‖(1 : E →L[𝕜] E) - T‖ ≤ 1 / 2 := by
    rw [hdiff]
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) (le_trans ?_ h)
    exact mul_le_mul_of_nonneg_right hK (norm_nonneg _)
  have hlt : ‖(1 : E →L[𝕜] E) - T‖ < 1 := lt_of_le_of_lt hle (by norm_num)
  have hunit : ((Units.oneSub _ hlt : (E →L[𝕜] E)ˣ) : E →L[𝕜] E) = T := by
    rw [Units.val_oneSub, sub_sub_cancel]
  set B₀ : E ≃L[𝕜] E := ContinuousLinearEquiv.unitsEquiv 𝕜 E (Units.oneSub _ hlt) with hB₀def
  have hB₀ : ∀ z : E, B₀ z = T z := by
    intro z
    rw [hB₀def, ContinuousLinearEquiv.unitsEquiv_apply, hunit]
  have hlow : ∀ z : E, ‖z‖ / 2 ≤ ‖T z‖ := by
    intro z
    have h1 : ‖z - T z‖ ≤ 1 / 2 * ‖z‖ := by
      have h2 := ((1 : E →L[𝕜] E) - T).le_opNorm z
      simp only [sub_apply, one_apply_eq_self] at h2
      exact le_trans h2 (mul_le_mul_of_nonneg_right hle (norm_nonneg _))
    have h3 : ‖z‖ - ‖T z‖ ≤ ‖z - T z‖ := norm_sub_norm_le z (T z)
    linarith
  refine ⟨B₀.trans e, ?_, ?_⟩
  · ext z
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply, hB₀, hT, hS,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  · intro y
    have hz := hlow (B₀.symm (e.symm y))
    rw [← hB₀, ContinuousLinearEquiv.apply_symm_apply] at hz
    have hy : ‖e.symm y‖ ≤ K * ‖y‖ :=
      le_trans ((e.symm : F →L[𝕜] E).le_opNorm y)
        (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
    have hval : (B₀.trans e).symm y = B₀.symm (e.symm y) := rfl
    rw [hval]
    linarith

omit [CompleteSpace E] [CompleteSpace F] in
/-- Taylor-type remainder bound on the closed ball of radius `‖x - x*‖`: the linearization of `Fn`
at `x` approximates `Fn` to second order (with the crude constant `2 L`). -/
private theorem norm_sub_apply_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} {r L : ℝ}
    (hF : ∀ z ∈ Metric.ball xstar r, HasFDerivAt Fn (F' z) z)
    (hL : ∀ z ∈ Metric.ball xstar r, ∀ w ∈ Metric.ball xstar r, ‖F' z - F' w‖ ≤ L * ‖z - w‖)
    {x : E} (hx : x ∈ Metric.ball xstar r) :
    ‖Fn xstar - Fn x - F' x (xstar - x)‖ ≤ 2 * max L 0 * ‖x - xstar‖ * ‖xstar - x‖ := by
  have hdr : ‖x - xstar‖ < r := by rwa [← dist_eq_norm]
  have hsub : Metric.closedBall xstar ‖x - xstar‖ ⊆ Metric.ball xstar r :=
    Metric.closedBall_subset_ball hdr
  have hxs : x ∈ Metric.closedBall xstar ‖x - xstar‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
  have hxstars : xstar ∈ Metric.closedBall xstar ‖x - xstar‖ :=
    Metric.mem_closedBall_self (norm_nonneg _)
  have hf : ∀ z ∈ Metric.closedBall xstar ‖x - xstar‖,
      HasFDerivWithinAt Fn (F' z) (Metric.closedBall xstar ‖x - xstar‖) z :=
    fun z hz => (hF z (hsub hz)).hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.closedBall xstar ‖x - xstar‖,
      ‖F' z - F' x‖ ≤ 2 * max L 0 * ‖x - xstar‖ := by
    intro z hz
    have h1 : ‖F' z - F' x‖ ≤ L * ‖z - x‖ := hL z (hsub hz) x (hsub hxs)
    have h2 : L * ‖z - x‖ ≤ max L 0 * ‖z - x‖ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    have h3 : ‖z - x‖ ≤ ‖z - xstar‖ + ‖xstar - x‖ := by
      simpa [dist_eq_norm] using dist_triangle z xstar x
    have h4 : ‖z - xstar‖ ≤ ‖x - xstar‖ := by
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall.mp hz
    have h5 : ‖xstar - x‖ = ‖x - xstar‖ := norm_sub_rev _ _
    nlinarith [le_max_right L 0, norm_nonneg (z - x)]
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hf hbound
    (convex_closedBall _ _) hxs hxstars

/-- Local quadratic convergence (AH Thm 5.3.?, Kress Thm 6.?): if `F` is differentiable near a
root `x*` with `F'(x*)` invertible (inverse `e`) and `F'` is `L`-Lipschitz on a ball, then on a
smaller ball the Newton step satisfies `‖step x - x*‖ ≤ C ‖x - x*‖²`. -/
theorem exists_ball_norm_step_sub_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E}
    (hstar : Fn xstar = 0) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' xstar) {r L : ℝ}
    (hr : 0 < r) (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, ∃ C : ℝ, ∀ x ∈ Metric.ball xstar δ,
      ‖step Fn F' x - xstar‖ ≤ C * ‖x - xstar‖ ^ 2 := by
  set K : ℝ := ‖(e.symm : F →L[𝕜] E)‖ with hKdef
  set L' : ℝ := max L 0 with hL'def
  have hK0 : 0 ≤ K := norm_nonneg _
  have hL'0 : 0 ≤ L' := le_max_right _ _
  have hm : 0 ≤ K * L' := mul_nonneg hK0 hL'0
  refine ⟨min r (1 / (2 * (K * L' + 1))), lt_min hr (by positivity), 4 * K * L', fun x hx => ?_⟩
  have hxr : x ∈ Metric.ball xstar r := Metric.ball_subset_ball (min_le_left _ _) hx
  have hd : ‖x - xstar‖ < 1 / (2 * (K * L' + 1)) := by
    rw [← dist_eq_norm]
    exact lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_right _ _)
  -- `F' x` is invertible with `‖(F' x)⁻¹‖ ≤ 2 K`
  have hclose : K * ‖(e : E →L[𝕜] F) - F' x‖ ≤ 1 / 2 := by
    have h1 : ‖(e : E →L[𝕜] F) - F' x‖ ≤ L' * ‖x - xstar‖ := by
      rw [he]
      calc ‖F' xstar - F' x‖ ≤ L * ‖xstar - x‖ := hL xstar (Metric.mem_ball_self hr) x hxr
        _ ≤ L' * ‖xstar - x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ = L' * ‖x - xstar‖ := by rw [norm_sub_rev]
    have h2 : K * ‖(e : E →L[𝕜] F) - F' x‖ ≤ K * L' * ‖x - xstar‖ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 hK0
    refine le_trans h2 (le_trans (mul_le_mul_of_nonneg_left hd.le hm) ?_)
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨B, hB, hBnorm⟩ := exists_equiv_of_norm_le e hKdef.ge hclose
  have hinv : (F' x).inverse = (B.symm : F →L[𝕜] E) := by
    rw [← hB, ContinuousLinearMap.inverse_equiv]
  have hBsymm : ∀ z : E, B.symm (F' x z) = z := by
    intro z
    simp only [← hB, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  have hkey : step Fn F' x - xstar = B.symm (F' x (x - xstar) - Fn x) := by
    simp only [map_sub, hBsymm, step, hinv, ContinuousLinearEquiv.coe_coe]
    abel
  have hnorm : ‖step Fn F' x - xstar‖ ≤ 2 * K * ‖F' x (x - xstar) - Fn x‖ := by
    rw [hkey]
    exact hBnorm _
  have heq : Fn xstar - Fn x - F' x (xstar - x) = F' x (x - xstar) - Fn x := by
    rw [hstar, show (xstar - x : E) = -(x - xstar) by abel, map_neg]
    abel
  have htay : ‖F' x (x - xstar) - Fn x‖ ≤ 2 * L' * ‖x - xstar‖ * ‖xstar - x‖ := by
    have h := norm_sub_apply_le hF hL hxr
    rwa [heq] at h
  calc ‖step Fn F' x - xstar‖ ≤ 2 * K * ‖F' x (x - xstar) - Fn x‖ := hnorm
    _ ≤ 2 * K * (2 * L' * ‖x - xstar‖ * ‖xstar - x‖) :=
        mul_le_mul_of_nonneg_left htay (by positivity)
    _ = 4 * K * L' * ‖x - xstar‖ ^ 2 := by rw [norm_sub_rev xstar x]; ring

/-- The explicit constant: `‖step x - x*‖ ≤ (L ‖(F' x)⁻¹‖ / 2) ‖x - x*‖²` whenever `F' x` is
invertible on the segment. -/
theorem norm_step_sub_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} (hstar : Fn xstar = 0)
    {r L : ℝ} (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {x : E} (hx : x ∈ Metric.ball xstar r) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x) :
    ‖step Fn F' x - xstar‖ ≤ L * ‖(e.symm : F →L[𝕜] E)‖ / 2 * ‖x - xstar‖ ^ 2 := by
  -- Obstruction: the sharp constant `L / 2` needs the *second order* mean value estimate
  -- `‖Fn x* - Fn x - F' x (x* - x)‖ ≤ (L / 2) ‖x - x*‖²`, i.e. the integral form
  -- `∫₀¹ ‖F' (x + t (x* - x)) - F' x‖ dt ≤ ∫₀¹ L t ‖x* - x‖ dt = (L / 2) ‖x - x*‖`.
  -- `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` only accepts a *constant* bound on
  -- `‖F' z - φ‖` over the whole convex set, which yields the constant `L` and, with the crude
  -- triangle-inequality bound used in `norm_sub_apply_le` above, `2 L`.  Getting `L / 2` needs
  -- `image_norm_le_of_norm_deriv_right_le_deriv_boundary` applied to
  -- `t ↦ Fn (x + t • (x* - x)) - Fn x - t • F' x (x* - x)` with boundary `B t = L ‖v‖² (t - t²/2)`,
  -- which additionally requires `NormedSpace ℝ F`, `IsScalarTower ℝ 𝕜 E` and `IsScalarTower ℝ 𝕜 F`
  -- to restrict scalars along the real segment.  Left as `sorry` rather than adding three more
  -- instance arguments to the statement.
  sorry

/-- Local convergence: from every `x₀` in a small ball, the Newton iterates converge to `x*`. -/
theorem tendsto_iterate {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} (hstar : Fn xstar = 0)
    (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' xstar) {r L : ℝ} (hr : 0 < r)
    (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖) :
    ∃ δ > 0, ∀ x₀ ∈ Metric.ball xstar δ,
      Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar) := by
  obtain ⟨δ, hδ, C, hC⟩ := exists_ball_norm_step_sub_le hstar e he hr hF hL
  set C' : ℝ := max C 1 with hC'def
  have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set δ' : ℝ := min δ (1 / (2 * C')) with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ (by positivity)
  have hhalf : ∀ x ∈ Metric.ball xstar δ', ‖step Fn F' x - xstar‖ ≤ 1 / 2 * ‖x - xstar‖ := by
    intro x hx
    have hxδ : x ∈ Metric.ball xstar δ := Metric.ball_subset_ball (min_le_left _ _) hx
    have h1 : ‖step Fn F' x - xstar‖ ≤ C * ‖x - xstar‖ ^ 2 := hC x hxδ
    have h2 : ‖x - xstar‖ < 1 / (2 * C') := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le (Metric.mem_ball.mp hx) (min_le_right _ _)
    have h3 : C * ‖x - xstar‖ ^ 2 ≤ C' * ‖x - xstar‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have h5 : C' * ‖x - xstar‖ ≤ 1 / 2 := by
      calc C' * ‖x - xstar‖ ≤ C' * (1 / (2 * C')) := mul_le_mul_of_nonneg_left h2.le hC'0.le
        _ = 1 / 2 := by field_simp
    nlinarith [norm_nonneg (x - xstar)]
  have hmaps : ∀ x ∈ Metric.ball xstar δ', step Fn F' x ∈ Metric.ball xstar δ' := by
    intro x hx
    have h1 := hhalf x hx
    have h2 : ‖x - xstar‖ < δ' := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hx
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [norm_nonneg (x - xstar)]
  refine ⟨δ', hδ'0, fun x₀ hx₀ => ?_⟩
  have hind : ∀ k, iterate Fn F' x₀ k ∈ Metric.ball xstar δ' ∧
      ‖iterate Fn F' x₀ k - xstar‖ ≤ (1 / 2 : ℝ) ^ k * ‖x₀ - xstar‖ := by
    intro k
    induction k with
    | zero => exact ⟨hx₀, by simp [iterate]⟩
    | succ k ih =>
      refine ⟨by rw [iterate_succ]; exact hmaps _ ih.1, ?_⟩
      rw [iterate_succ]
      calc ‖step Fn F' (iterate Fn F' x₀ k) - xstar‖
          ≤ 1 / 2 * ‖iterate Fn F' x₀ k - xstar‖ := hhalf _ ih.1
        _ ≤ 1 / 2 * ((1 / 2 : ℝ) ^ k * ‖x₀ - xstar‖) :=
            mul_le_mul_of_nonneg_left ih.2 (by norm_num)
        _ = (1 / 2 : ℝ) ^ (k + 1) * ‖x₀ - xstar‖ := by ring
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => (hind k).2) ?_
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).mul_const ‖x₀ - xstar‖

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
  -- Obstruction: Newton–Kantorovich needs the *majorant* method.  One builds the scalar Newton
  -- sequence `t_{k+1} = t_k - p t_k / p' t_k` for `p t = (L / (2 β)) t ^ 2 - t / β + η`, proves by
  -- simultaneous induction that `‖x_{k+1} - x_k‖ ≤ t_{k+1} - t_k` and that every `F' x_k` is
  -- invertible with `‖(F' x_k)⁻¹‖ ≤ β / (1 - β L (t_k - t_0))`, and only then reads off the a
  -- priori bound from the closed form of `t_k`.  Even the scalar half (monotone convergence of
  -- `t_k` to `t* = (1 - √(1 - 2h)) / (β L)` and the closed form
  -- `t* - t_k = (2h)^(2^k) η / (2^k h)`) is a substantial development, and the vector half
  -- additionally needs the second-order Taylor estimate that `norm_step_sub_le` above is blocked
  -- on.  Approaches tried and rejected: reducing to `ContractingWith` (the Newton map is not a
  -- contraction on the ball — only the error sequence is dominated by the majorant), and reducing
  -- to `tendsto_iterate` (that gives neither the a priori radius nor existence of the root, which
  -- is the whole content here).
  sorry

end Quadratic

end Newton
