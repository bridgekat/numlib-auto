import Numlib.Nonlinear.FixedPoint
import Numlib.Analysis.Normed.Ring.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Newton's method in Banach spaces

`Newton.step F F' x = x - (F' x)⁻¹ (F x)` with `ContinuousLinearMap.inverse` (`0` when `F' x` is
not invertible), local quadratic convergence when `F'(x*)` is invertible and `F'` is Lipschitz —
`‖e_{k+1}‖ ≤ (L ‖F'(x*)⁻¹‖ / 2) ‖e_k‖²` (Atkinson–Han[^atkinson-han] Thm 5.4.1; Kress[^kress]
Cor 6.15 with Thm 6.20) — and the Newton–Kantorovich theorem with the a priori bound
(Atkinson–Han Thm 5.4.2; Kress Thm 6.14), proved by the majorant method of
Ortega–Rheinboldt[^ortega-rheinboldt] through `Newton.majorant`.

Both rest on `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le`, the second-order mean value
inequality with the sharp constant `L / 2`, proved here for want of a Mathlib version; it is the
natural candidate for upstreaming to `Mathlib.Analysis.Calculus.MeanValue`.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009.
[^kress]: Rainer Kress, *Numerical Analysis*, Graduate Texts in Mathematics 181, Springer, 1998.
[^ortega-rheinboldt]: James M. Ortega and Werner C. Rheinboldt, *Iterative Solution of Nonlinear
  Equations in Several Variables*, Academic Press, 1970.
-/

open Filter Topology

section MeanValue

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Second-order mean value inequality with the sharp constant: if `f` has derivative `f' z` at
every point of a convex set `s` and `‖f' z - f' x‖ ≤ C ‖z - x‖` on `s`, then
`‖f y - f x - f' x (y - x)‖ ≤ C / 2 * ‖y - x‖ ^ 2` for all `x, y ∈ s`.

Mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` bounds the same quantity by
`C' * ‖y - x‖` for a *constant* bound `C'` on `‖f' z - f' x‖`, which loses the factor `1 / 2`.  The
sharp form integrates the variable bound along the segment, through
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` with boundary `t ↦ C ‖y - x‖ ^ 2 * t ^ 2 / 2`.
As for the first-order inequality, the scalar field must be real or complex, because the proof
restricts scalars along the real segment from `x` to `y`. -/
theorem Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le {f : E → F} {f' : E → E →L[𝕜] F}
    {s : Set E} (hs : Convex ℝ s) (hf : ∀ z ∈ s, HasFDerivAt f (f' z) z) {C : ℝ} {x y : E}
    (hx : x ∈ s) (hy : y ∈ s) (hC : ∀ z ∈ s, ‖f' z - f' x‖ ≤ C * ‖z - x‖) :
    ‖f y - f x - f' x (y - x)‖ ≤ C / 2 * ‖y - x‖ ^ 2 := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (y - x) ∈ s := by
    intro t ht
    have h := hs hx hy (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1 (by ring)
    have he : x + t • (y - x) = (1 - t) • x + t • y := by module
    rw [he]
    exact h
  have hcd : ∀ t : ℝ, HasDerivAt (fun v : ℝ => x + v • (y - x)) (y - x) t := fun t => by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => f (x + v • (y - x)) - f x - v • (f' x (y - x)))
        (f' (x + t • (y - x)) (y - x) - f' x (y - x)) t := by
    intro t ht
    have h1 := ((hf _ (hmem t ht)).restrictScalars ℝ).comp_hasDerivAt t (hcd t)
    have h2 : HasDerivAt (fun v : ℝ => v • (f' x (y - x))) (f' x (y - x)) t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const (f' x (y - x))
    exact (h1.sub_const (f x)).sub h2
  have hB : ∀ t : ℝ,
      HasDerivAt (fun v : ℝ => C * ‖y - x‖ ^ 2 * (v ^ 2 / 2)) (C * ‖y - x‖ ^ 2 * t) t := by
    intro t
    have h : HasDerivAt (fun v : ℝ => v ^ 2 / 2) t t := by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    simpa using h.const_mul (C * ‖y - x‖ ^ 2)
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖f' (x + t • (y - x)) (y - x) - f' x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 * t := by
    intro t ht
    have h1 : f' (x + t • (y - x)) (y - x) - f' x (y - x)
        = (f' (x + t • (y - x)) - f' x) (y - x) := by simp
    have h3 : ‖f' (x + t • (y - x)) - f' x‖ ≤ C * ‖x + t • (y - x) - x‖ :=
      hC _ (hmem t ⟨ht.1, ht.2.le⟩)
    have h4 : ‖x + t • (y - x) - x‖ = t * ‖y - x‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    rw [h4] at h3
    rw [h1]
    calc ‖(f' (x + t • (y - x)) - f' x) (y - x)‖
        ≤ ‖f' (x + t • (y - x)) - f' x‖ * ‖y - x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * (t * ‖y - x‖) * ‖y - x‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = C * ‖y - x‖ ^ 2 * t := by ring
  have hzero : ‖f (x + (0 : ℝ) • (y - x)) - f x - (0 : ℝ) • (f' x (y - x))‖
      ≤ C * ‖y - x‖ ^ 2 * ((0 : ℝ) ^ 2 / 2) := by simp
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun v : ℝ => f (x + v • (y - x)) - f x - v • (f' x (y - x)))
    (f' := fun v : ℝ => f' (x + v • (y - x)) (y - x) - f' x (y - x)) (a := 0) (b := 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) hzero hB hbound
    (Set.right_mem_Icc.2 zero_le_one)
  have hx1 : x + (1 : ℝ) • (y - x) = y := by module
  rw [hx1, one_smul] at key
  calc ‖f y - f x - f' x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 * ((1 : ℝ) ^ 2 / 2) := key
    _ = C / 2 * ‖y - x‖ ^ 2 := by ring

end MeanValue

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
through the mean value inequality `Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le`, which
is available only over `ℝ`/`ℂ`.  This is not a defect of the proofs: over a general
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
/-- Taylor-type remainder bound inside the ball: the linearization of `Fn` at `x` approximates `Fn`
to second order, with the sharp constant `L / 2`. -/
private theorem norm_sub_apply_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} {r L : ℝ}
    (hF : ∀ z ∈ Metric.ball xstar r, HasFDerivAt Fn (F' z) z)
    (hL : ∀ z ∈ Metric.ball xstar r, ∀ w ∈ Metric.ball xstar r, ‖F' z - F' w‖ ≤ L * ‖z - w‖)
    {x : E} (hx : x ∈ Metric.ball xstar r) :
    ‖Fn xstar - Fn x - F' x (xstar - x)‖ ≤ L / 2 * ‖xstar - x‖ ^ 2 := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hx)
  exact Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le (convex_ball xstar r) hF hx
    (Metric.mem_ball_self hr) fun z hz => hL z hz x hx

/-- Local quadratic convergence (Atkinson–Han, *Theoretical Numerical Analysis*, Thm 5.4.1; Kress,
*Numerical Analysis*, Cor 6.15 with Thm 6.20): if `F` is differentiable near a root `x*` with
`F'(x*)` invertible (inverse `e`) and `F'` is `L`-Lipschitz on a ball, then on a smaller ball the
Newton step satisfies `‖step x - x*‖ ≤ C ‖x - x*‖²`.  The radius is shrunk far enough that `F' x`
is still invertible, by the Neumann series, with `‖(F' x)⁻¹‖ ≤ 2 ‖(F' x*)⁻¹‖`. -/
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
  refine ⟨min r (1 / (2 * (K * L' + 1))), lt_min hr (by positivity), K * L', fun x hx => ?_⟩
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
  have htay : ‖F' x (x - xstar) - Fn x‖ ≤ L' / 2 * ‖xstar - x‖ ^ 2 := by
    have h := norm_sub_apply_le hF hL hxr
    rw [heq] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    linarith [le_max_left L 0]
  calc ‖step Fn F' x - xstar‖ ≤ 2 * K * ‖F' x (x - xstar) - Fn x‖ := hnorm
    _ ≤ 2 * K * (L' / 2 * ‖xstar - x‖ ^ 2) := mul_le_mul_of_nonneg_left htay (by positivity)
    _ = K * L' * ‖x - xstar‖ ^ 2 := by rw [norm_sub_rev xstar x]; ring

omit [CompleteSpace E] [CompleteSpace F] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
/-- If `F' z` is invertible with inverse `e.symm`, the Newton step at `z` is
`z - (F' z)⁻¹ (Fn z)`, written with the equivalence rather than the junk-valued
`ContinuousLinearMap.inverse`. -/
private theorem step_sub_self {Fn : E → F} {F' : E → E →L[𝕜] F} {z : E} (e : E ≃L[𝕜] F)
    (he : (e : E →L[𝕜] F) = F' z) : step Fn F' z - z = -(e.symm (Fn z)) := by
  have hinv : (F' z).inverse = (e.symm : F →L[𝕜] E) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  simp only [step, hinv, ContinuousLinearEquiv.coe_coe]
  abel

/-- The explicit constant: `‖step x - x*‖ ≤ (L ‖(F' x)⁻¹‖ / 2) ‖x - x*‖²` whenever `F' x` is
invertible on the segment. -/
theorem norm_step_sub_le {Fn : E → F} {F' : E → E →L[𝕜] F} {xstar : E} (hstar : Fn xstar = 0)
    {r L : ℝ} (hF : ∀ x ∈ Metric.ball xstar r, HasFDerivAt Fn (F' x) x)
    (hL : ∀ x ∈ Metric.ball xstar r, ∀ y ∈ Metric.ball xstar r, ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {x : E} (hx : x ∈ Metric.ball xstar r) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x) :
    ‖step Fn F' x - xstar‖ ≤ L * ‖(e.symm : F →L[𝕜] E)‖ / 2 * ‖x - xstar‖ ^ 2 := by
  have htay : ‖Fn xstar - Fn x - F' x (xstar - x)‖ ≤ L / 2 * ‖xstar - x‖ ^ 2 :=
    norm_sub_apply_le hF hL hx
  have hinv : (F' x).inverse = (e.symm : F →L[𝕜] E) := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
  have hesymm : ∀ z : E, e.symm (F' x z) = z := by
    intro z
    simp only [← he, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  have hkey : step Fn F' x - xstar = e.symm (F' x (x - xstar) - Fn x) := by
    simp only [map_sub, hesymm, step, hinv, ContinuousLinearEquiv.coe_coe]
    abel
  have heq : Fn xstar - Fn x - F' x (xstar - x) = F' x (x - xstar) - Fn x := by
    rw [hstar, show (xstar - x : E) = -(x - xstar) by abel, map_neg]
    abel
  rw [heq] at htay
  calc ‖step Fn F' x - xstar‖ = ‖(e.symm : F →L[𝕜] E) (F' x (x - xstar) - Fn x)‖ := by
        rw [hkey]; rfl
    _ ≤ ‖(e.symm : F →L[𝕜] E)‖ * ‖F' x (x - xstar) - Fn x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(e.symm : F →L[𝕜] E)‖ * (L / 2 * ‖xstar - x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left htay (norm_nonneg _)
    _ = L * ‖(e.symm : F →L[𝕜] E)‖ / 2 * ‖x - xstar‖ ^ 2 := by
        rw [norm_sub_rev xstar x]; ring

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

end Quadratic

section Kantorovich

/-! ### The Newton–Kantorovich theorem

The proof follows the majorant method of Ortega–Rheinboldt, *Iterative Solution of Nonlinear
Equations in Several Variables*: the Newton iterates of `Fn` are dominated by the Newton iterates
`t_k` of the scalar quadratic `p t = (L / 2) t ^ 2 - t / β + η / β`, whose smaller root is
`t* = (1 - √(1 - 2 β L η)) / (β L)`.  Instead of `t_k` itself the development below carries the
normalized quantity `majorant u k = 1 - β L t_k`, where `u = √(1 - 2 β L η)`: in that variable the
three parameters `β`, `L`, `η` collapse into one, the scalar Newton recursion becomes the
Babylonian iteration for `√(u ^ 2)`, and the majorant relation driving the induction becomes the
identity `Newton.majorant_sq_div`. -/

/-- The normalized Kantorovich majorant.  With `u = √(1 - 2 β L η)` and `t_k` the Newton sequence
of the scalar majorant polynomial `p t = (L / 2) t ^ 2 - t / β + η / β` started at `t_0 = 0`, one
has `majorant u k = 1 - β L t_k`; the Newton recursion for `p` turns into the Babylonian iteration
`s ↦ (s ^ 2 + u ^ 2) / (2 s)` for `√(u ^ 2) = u` started at `s_0 = 1`.

This makes the two facts the vector induction needs — `majorant u k` decreases to `u`, and
`(majorant u k - majorant u (k + 1)) ^ 2 / (2 majorant u (k + 1))` is the next increment — pure
algebra; see `Newton.majorant_sq_div` and `Newton.majorant_sub_le`. -/
noncomputable def majorant (u : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (majorant u k ^ 2 + u ^ 2) / (2 * majorant u k)

/-- The majorant starts at `1`, i.e. the scalar Newton sequence starts at `t_0 = 0`. -/
@[simp] theorem majorant_zero (u : ℝ) : majorant u 0 = 1 := rfl

/-- The defining recursion of `Newton.majorant`, as a rewrite rule. -/
theorem majorant_succ (u : ℝ) (k : ℕ) :
    majorant u (k + 1) = (majorant u k ^ 2 + u ^ 2) / (2 * majorant u k) := rfl

/-- The majorant never vanishes, so every scalar iterate `t_k` stays strictly below `1 / (β L)`
and the perturbed derivatives stay invertible. -/
theorem majorant_pos (u : ℝ) (k : ℕ) : 0 < majorant u k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [majorant_succ]
    exact div_pos (by nlinarith) (by linarith)

/-- Nonvanishing form of `Newton.majorant_pos`, for `field_simp`. -/
theorem majorant_ne_zero (u : ℝ) (k : ℕ) : majorant u k ≠ 0 := (majorant_pos u k).ne'

/-- The distance of the majorant to its limit `u` obeys the Newton square law. -/
theorem majorant_succ_sub (u : ℝ) (k : ℕ) :
    majorant u (k + 1) - u = (majorant u k - u) ^ 2 / (2 * majorant u k) := by
  have h0 := majorant_ne_zero u k
  rw [majorant_succ]
  field_simp
  ring

/-- The increment of the majorant, in closed form. -/
theorem majorant_sub_succ (u : ℝ) (k : ℕ) :
    majorant u k - majorant u (k + 1) = (majorant u k ^ 2 - u ^ 2) / (2 * majorant u k) := by
  have h0 := majorant_ne_zero u k
  rw [majorant_succ]
  field_simp
  ring

/-- The majorant stays above its limit `u`. -/
theorem le_majorant {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) : u ≤ majorant u k := by
  induction k with
  | zero => simpa using hu1
  | succ k ih =>
    have h := majorant_succ_sub u k
    have hnn : 0 ≤ (majorant u k - u) ^ 2 / (2 * majorant u k) :=
      div_nonneg (sq_nonneg _) (by linarith [majorant_pos u k])
    linarith

/-- The majorant is nonincreasing, so the scalar iterates `t_k` increase. -/
theorem majorant_antitone {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    majorant u (k + 1) ≤ majorant u k := by
  have h := majorant_sub_succ u k
  have hk := le_majorant hu hu1 k
  have hp := majorant_pos u k
  have hnn : 0 ≤ (majorant u k ^ 2 - u ^ 2) / (2 * majorant u k) :=
    div_nonneg (by nlinarith) (by linarith)
  linarith

/-- The majorant stays at most `1`, i.e. the scalar iterates `t_k` are nonnegative. -/
theorem majorant_le_one {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) : majorant u k ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih => exact le_trans (majorant_antitone hu hu1 k) ih

/-- The defining relation of the Newton majorant, in the form the vector induction consumes:
one Newton step of size `(majorant u k - majorant u (k + 1)) / (β L)` produces a residual whose
Newton step has size `(majorant u (k + 1) - majorant u (k + 2)) / (β L)`. -/
theorem majorant_sq_div (u : ℝ) (k : ℕ) :
    (majorant u k - majorant u (k + 1)) ^ 2 / (2 * majorant u (k + 1))
      = majorant u (k + 1) - majorant u (k + 2) := by
  have h0 := majorant_ne_zero u k
  have h1 := majorant_ne_zero u (k + 1)
  rw [majorant_sub_succ u (k + 1), majorant_sub_succ u k, majorant_succ u k]
  field_simp
  ring

/-- Bernoulli's inequality in the form `1 ≤ 2 ^ k u + (1 - u ^ 2) ^ (2 ^ k)`, the arithmetic heart
of the a priori bound. -/
private theorem one_le_two_pow_mul {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    1 ≤ (2 : ℝ) ^ k * u + (1 - u ^ 2) ^ (2 ^ k) := by
  have hb : 1 + ((2 ^ k : ℕ) : ℝ) * (-u ^ 2) ≤ (1 + -u ^ 2) ^ (2 ^ k) :=
    one_add_mul_le_pow (by nlinarith) _
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  rw [hcast] at hb
  have hkey : (1 : ℝ) - (2 : ℝ) ^ k * u ^ 2 ≤ (1 - u ^ 2) ^ (2 ^ k) := by
    calc (1 : ℝ) - (2 : ℝ) ^ k * u ^ 2 = 1 + (2 : ℝ) ^ k * (-u ^ 2) := by ring
      _ ≤ (1 + -u ^ 2) ^ (2 ^ k) := hb
      _ = (1 - u ^ 2) ^ (2 ^ k) := by ring_nf
  nlinarith [mul_nonneg (le_of_lt (show (0 : ℝ) < (2 : ℝ) ^ k by positivity)) hu]

/-- The inductive step of `Newton.majorant_sub_le`, isolated as an inequality between reals. -/
private theorem majorant_step_arith {x P m s u : ℝ} (hu : 0 ≤ u) (hx : 0 ≤ x) (hP : 0 ≤ P)
    (hm : 0 < m) (hQ : m * x ≤ P) (hone : 1 ≤ m * u + P) (hsx : s = u + x) (hs : 0 < s) :
    x ^ 2 / (2 * s) ≤ P ^ 2 / (2 * m) := by
  subst hsx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hQ)
      (by positivity : (0 : ℝ) ≤ u * (m * x + P) + P * x),
    mul_nonneg (mul_nonneg (sq_nonneg x) hm.le) (by linarith : (0 : ℝ) ≤ m * u + P - 1)]

/-- Quadratic decay of the majorant towards `u`: `majorant u k - u ≤ (1 - u²)^(2^k) / 2^k`.  Since
`1 - u ^ 2 = 2 β L η` this is exactly the a priori bound of the Newton–Kantorovich theorem, and it
is an equality at `u = 0`, i.e. in the critical case `β L η = 1 / 2`. -/
theorem majorant_sub_le {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    majorant u k - u ≤ (1 - u ^ 2) ^ (2 ^ k) / 2 ^ k := by
  induction k with
  | zero => simp only [majorant_zero, pow_zero, pow_one, div_one]; nlinarith
  | succ k ih =>
    have hm : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hs := majorant_pos u k
    have hx : 0 ≤ majorant u k - u := by linarith [le_majorant hu hu1 k]
    have hone := one_le_two_pow_mul hu hu1 k
    have hQ : (2 : ℝ) ^ k * (majorant u k - u) ≤ (1 - u ^ 2) ^ (2 ^ k) := by
      rw [le_div_iff₀ hm] at ih
      linarith
    have hsplit : (1 - u ^ 2) ^ (2 ^ (k + 1)) = ((1 - u ^ 2) ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    have h2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [majorant_succ_sub, hsplit, h2]
    exact majorant_step_arith hu hx (pow_nonneg (by nlinarith) _) hm hQ hone (by ring) hs

variable [CompleteSpace E] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E]

omit [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
/-- Perturbation along the ball: `F' z` is invertible as soon as `β L ‖z - x₀‖ < 1`, with
`‖(F' z)⁻¹‖ ≤ β / (1 - β L ‖z - x₀‖)`.  This is the Banach lemma in the two-space form of
`ContinuousLinearEquiv.exists_symm_norm_le_of_add`. -/
private theorem exists_equiv_of_dist_le {F' : E → E →L[𝕜] F} {x₀ : E} {r β L : ℝ} (hβ0 : 0 ≤ β)
    (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀) (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {z : E} (hz : z ∈ Metric.closedBall x₀ r) (hzt : β * L * ‖z - x₀‖ < 1) :
    ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = F' z ∧
      ‖(e'.symm : F →L[𝕜] E)‖ ≤ β / (1 - β * L * ‖z - x₀‖) := by
  have hx0 : x₀ ∈ Metric.closedBall x₀ r := by
    rw [Metric.mem_closedBall, dist_self]
    exact le_trans dist_nonneg (Metric.mem_closedBall.mp hz)
  have ht : ‖F' z - F' x₀‖ ≤ L * ‖z - x₀‖ := hLip z hz x₀ hx0
  have hlt : ‖(e.symm : F →L[𝕜] E)‖ * ‖F' z - F' x₀‖ < 1 := by
    calc ‖(e.symm : F →L[𝕜] E)‖ * ‖F' z - F' x₀‖ ≤ β * (L * ‖z - x₀‖) :=
          mul_le_mul hβ' ht (norm_nonneg _) hβ0
      _ = β * L * ‖z - x₀‖ := by ring
      _ < 1 := hzt
  obtain ⟨e', he'1, he'2, -⟩ := e.exists_symm_norm_le_of_add (F' z - F' x₀) hlt
  refine ⟨e', ?_, he'2.trans ?_⟩
  · rw [he'1, he]; abel
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg hβ0 (norm_nonneg (e.symm : F →L[𝕜] E)))
      (sub_nonneg.2 ht), norm_nonneg (e.symm : F →L[𝕜] E)]

omit [CompleteSpace E] in
/-- The residual after one Newton step is second order in the step: `Fn z + F' z (step z - z) = 0`
by construction, so the sharp Taylor estimate applies. -/
private theorem norm_apply_step_le {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r L : ℝ}
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    {z : E} (hz : z ∈ Metric.closedBall x₀ r) (hsz : step Fn F' z ∈ Metric.closedBall x₀ r)
    (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' z) :
    ‖Fn (step Fn F' z)‖ ≤ L / 2 * ‖step Fn F' z - z‖ ^ 2 := by
  have hstep : step Fn F' z - z = -(e.symm (Fn z)) := step_sub_self e he
  have happ : F' z (step Fn F' z - z) = -Fn z := by
    rw [hstep, map_neg, ← he]
    simp
  have htay := Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le
    (convex_closedBall x₀ r) hF hz hsz fun w hw => hLip w hw z hz
  rw [happ] at htay
  simpa using htay

omit [CompleteSpace E] [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
/-- A point within the `k`-th scalar iterate of `x₀` lies in the ball on which the hypotheses of
the Newton–Kantorovich theorem hold. -/
private theorem mem_closedBall_of_le_majorant {x₀ : E} {r β L u : ℝ} (hA : 0 < β * L) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) (hr : (1 - u) / (β * L) ≤ r) {j : ℕ} {z : E}
    (hz : ‖z - x₀‖ ≤ (1 - majorant u j) / (β * L)) : z ∈ Metric.closedBall x₀ r := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine hz.trans (le_trans ?_ hr)
  gcongr
  exact le_majorant hu0 hu1 j

omit [IsRCLikeNormedField 𝕜] [NormedSpace ℝ E] in
/-- Invertibility with the majorant bound `‖(F' z)⁻¹‖ ≤ β / majorant u j`, the stability estimate
carried by the Kantorovich induction. -/
private theorem exists_equiv_of_le_majorant {F' : E → E →L[𝕜] F} {x₀ : E} {r β L u : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hr : (1 - u) / (β * L) ≤ r) {j : ℕ} {z : E}
    (hz : ‖z - x₀‖ ≤ (1 - majorant u j) / (β * L)) :
    ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = F' z ∧
      ‖(e'.symm : F →L[𝕜] E)‖ ≤ β / majorant u j := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hsj := majorant_pos u j
  have hAz : β * L * ‖z - x₀‖ ≤ 1 - majorant u j := by
    have h := mul_le_mul_of_nonneg_left hz hA.le
    rwa [mul_div_cancel₀ _ hA.ne'] at h
  obtain ⟨e', he'1, he'2⟩ := exists_equiv_of_dist_le hβ.le e he hβ' hLip
    (mem_closedBall_of_le_majorant hA hu0 hu1 hr hz) (by linarith)
  refine ⟨e', he'1, he'2.trans ?_⟩
  gcongr
  linarith

/-- The invariant carried by the Kantorovich induction: the `k`-th Newton iterate stays within
`t_k = (1 - majorant u k) / (β L)` of `x₀`, and the `k`-th Newton increment is bounded by the
scalar increment `t_{k+1} - t_k`. -/
private theorem kantorovich_invariant {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r β η L u : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hueta : 2 * (β * L * η) = 1 - u ^ 2)
    (hr : (1 - u) / (β * L) ≤ r) (k : ℕ) :
    ‖iterate Fn F' x₀ k - x₀‖ ≤ (1 - majorant u k) / (β * L) ∧
      ‖iterate Fn F' x₀ (k + 1) - iterate Fn F' x₀ k‖
        ≤ (majorant u k - majorant u (k + 1)) / (β * L) := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hmem : ∀ (j : ℕ) (z : E), ‖z - x₀‖ ≤ (1 - majorant u j) / (β * L) →
      z ∈ Metric.closedBall x₀ r := fun _ _ hzj =>
    mem_closedBall_of_le_majorant hA hu0 hu1 hr hzj
  have hinvert : ∀ (j : ℕ) (z : E), ‖z - x₀‖ ≤ (1 - majorant u j) / (β * L) →
      ∃ e' : E ≃L[𝕜] F, (e' : E →L[𝕜] F) = F' z ∧
        ‖(e'.symm : F →L[𝕜] E)‖ ≤ β / majorant u j := fun _ _ hzj =>
    exists_equiv_of_le_majorant hβ hL e he hβ' hLip hu0 hu1 hr hzj
  induction k with
  | zero =>
    refine ⟨by simp [iterate], ?_⟩
    have h1 : iterate Fn F' x₀ 1 = step Fn F' x₀ := by
      rw [iterate_succ]
      rfl
    have h0 : iterate Fn F' x₀ 0 = x₀ := rfl
    rw [h1, h0, step_sub_self e he, norm_neg]
    have hs1 : majorant u 1 = (1 + u ^ 2) / 2 := by
      rw [majorant_succ, majorant_zero]
      norm_num
    rw [hs1, majorant_zero]
    have hval : (1 - (1 + u ^ 2) / 2) / (β * L) = η := by
      field_simp
      nlinarith [hueta]
    rw [hval]
    exact hη'
  | succ k ih =>
    obtain ⟨hb, hd⟩ := ih
    have hb1 : ‖iterate Fn F' x₀ (k + 1) - x₀‖ ≤ (1 - majorant u (k + 1)) / (β * L) := by
      have hsplit : iterate Fn F' x₀ (k + 1) - x₀
          = (iterate Fn F' x₀ (k + 1) - iterate Fn F' x₀ k) + (iterate Fn F' x₀ k - x₀) := by
        abel
      rw [hsplit]
      refine (norm_add_le _ _).trans ((add_le_add hd hb).trans (le_of_eq ?_))
      ring
    refine ⟨hb1, ?_⟩
    obtain ⟨ek, hek, -⟩ := hinvert k _ hb
    obtain ⟨ek1, hek1, hek1n⟩ := hinvert (k + 1) _ hb1
    have hzk : iterate Fn F' x₀ k ∈ Metric.closedBall x₀ r := hmem k _ hb
    have hzk1 : iterate Fn F' x₀ (k + 1) ∈ Metric.closedBall x₀ r := hmem (k + 1) _ hb1
    have hstep : step Fn F' (iterate Fn F' x₀ k) = iterate Fn F' x₀ (k + 1) :=
      (iterate_succ Fn F' x₀ k).symm
    have hFn : ‖Fn (iterate Fn F' x₀ (k + 1))‖
        ≤ L / 2 * ‖iterate Fn F' x₀ (k + 1) - iterate Fn F' x₀ k‖ ^ 2 := by
      have h := norm_apply_step_le hF hLip hzk (by rw [hstep]; exact hzk1) ek hek
      rwa [hstep] at h
    have hnext : ‖iterate Fn F' x₀ (k + 2) - iterate Fn F' x₀ (k + 1)‖
        ≤ ‖(ek1.symm : F →L[𝕜] E)‖ * ‖Fn (iterate Fn F' x₀ (k + 1))‖ := by
      rw [iterate_succ Fn F' x₀ (k + 1), step_sub_self ek1 hek1, norm_neg]
      exact ContinuousLinearMap.le_opNorm (ek1.symm : F →L[𝕜] E)
        (Fn (iterate Fn F' x₀ (k + 1)))
    have hs0 := majorant_pos u k
    have hs1 := majorant_pos u (k + 1)
    have hdiff : 0 ≤ majorant u k - majorant u (k + 1) := by
      linarith [majorant_antitone hu0 hu1 k]
    calc ‖iterate Fn F' x₀ (k + 2) - iterate Fn F' x₀ (k + 1)‖
        ≤ ‖(ek1.symm : F →L[𝕜] E)‖ * ‖Fn (iterate Fn F' x₀ (k + 1))‖ := hnext
      _ ≤ (β / majorant u (k + 1)) *
            (L / 2 * ‖iterate Fn F' x₀ (k + 1) - iterate Fn F' x₀ k‖ ^ 2) :=
          mul_le_mul hek1n hFn (norm_nonneg _) (by positivity)
      _ ≤ (β / majorant u (k + 1)) *
            (L / 2 * ((majorant u k - majorant u (k + 1)) / (β * L)) ^ 2) := by gcongr
      _ = ((majorant u k - majorant u (k + 1)) ^ 2 / (2 * majorant u (k + 1))) / (β * L) := by
          field_simp
      _ = (majorant u (k + 1) - majorant u (k + 2)) / (β * L) := by rw [majorant_sq_div]

/-- Newton–Kantorovich, stated with the limit `u` of the majorant supplied as a parameter through
`2 β L η = 1 - u ^ 2`; `Newton.kantorovich` instantiates `u = √(1 - 2 β L η)`. -/
private theorem kantorovich_of_sq {Fn : E → F} {F' : E → E →L[𝕜] F} {x₀ : E} {r β η L u : ℝ}
    (hβ : 0 < β) (hL : 0 < L) (e : E ≃L[𝕜] F) (he : (e : E →L[𝕜] F) = F' x₀)
    (hβ' : ‖(e.symm : F →L[𝕜] E)‖ ≤ β) (hη' : ‖e.symm (Fn x₀)‖ ≤ η)
    (hF : ∀ x ∈ Metric.closedBall x₀ r, HasFDerivAt Fn (F' x) x)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖F' x - F' y‖ ≤ L * ‖x - y‖)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hueta : 2 * (β * L * η) = 1 - u ^ 2)
    (hr : (1 - u) / (β * L) ≤ r) :
    ∃ xstar ∈ Metric.closedBall x₀ ((1 - u) / (β * L)),
      Fn xstar = 0 ∧ Tendsto (iterate Fn F' x₀) atTop (𝓝 xstar) ∧
      (∀ k, iterate Fn F' x₀ k ∈ Metric.closedBall x₀ r) ∧
      (0 < β * L * η → ∀ k, ‖iterate Fn F' x₀ k - xstar‖ ≤
        (2 * (β * L * η)) ^ (2 ^ k) * η / (2 ^ k * (β * L * η))) := by
  have hA : (0 : ℝ) < β * L := mul_pos hβ hL
  have hinv := fun k => kantorovich_invariant hβ hL e he hβ' hη' hF hLip hu0 hu1 hueta hr k
  have hb : ∀ k, ‖iterate Fn F' x₀ k - x₀‖ ≤ (1 - majorant u k) / (β * L) := fun k => (hinv k).1
  have hd : ∀ k, ‖iterate Fn F' x₀ (k + 1) - iterate Fn F' x₀ k‖
      ≤ (majorant u k - majorant u (k + 1)) / (β * L) := fun k => (hinv k).2
  have hstay : ∀ k, iterate Fn F' x₀ k ∈ Metric.closedBall x₀ r := fun k =>
    mem_closedBall_of_le_majorant hA hu0 hu1 hr (hb k)
  have hchain : ∀ k m : ℕ, k ≤ m → ‖iterate Fn F' x₀ m - iterate Fn F' x₀ k‖
      ≤ (majorant u k - majorant u m) / (β * L) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have hsp : iterate Fn F' x₀ (m + 1) - iterate Fn F' x₀ k
          = (iterate Fn F' x₀ (m + 1) - iterate Fn F' x₀ m)
            + (iterate Fn F' x₀ m - iterate Fn F' x₀ k) := by abel
      rw [hsp]
      refine (norm_add_le _ _).trans ((add_le_add (hd m) ih).trans (le_of_eq ?_))
      ring
  have herr : ∀ k m : ℕ, k ≤ m → ‖iterate Fn F' x₀ m - iterate Fn F' x₀ k‖
      ≤ (majorant u k - u) / (β * L) := by
    intro k m hkm
    refine (hchain k m hkm).trans ?_
    gcongr
    exact le_majorant hu0 hu1 m
  have herr0 : ∀ k, 0 ≤ (majorant u k - u) / (β * L) := fun k =>
    div_nonneg (by linarith [le_majorant hu0 hu1 k]) hA.le
  have herrle : ∀ k, (majorant u k - u) / (β * L) ≤ ((1 : ℝ) / 2) ^ k / (β * L) := by
    intro k
    gcongr
    refine (majorant_sub_le hu0 hu1 k).trans ?_
    rw [div_pow, one_pow]
    gcongr
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have htend : Tendsto (fun k => (majorant u k - u) / (β * L)) atTop (𝓝 0) := by
    refine squeeze_zero herr0 herrle ?_
    have h : Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h.div_const (β * L)
  have hcauchy : CauchySeq (iterate Fn F' x₀) := by
    refine cauchySeq_of_le_tendsto_0' (fun k => (majorant u k - u) / (β * L)) ?_ htend
    intro n m hnm
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    exact herr n m hnm
  obtain ⟨xstar, hxstar⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxmem : ‖xstar - x₀‖ ≤ (1 - u) / (β * L) := by
    refine le_of_tendsto ((hxstar.sub_const x₀).norm) (Filter.Eventually.of_forall fun k => ?_)
    refine (hb k).trans ?_
    gcongr
    exact le_majorant hu0 hu1 k
  have hxball : xstar ∈ Metric.closedBall x₀ r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hxmem.trans hr
  have hFnzero : ∀ k, ‖Fn (iterate Fn F' x₀ (k + 1))‖
      ≤ L / 2 * ((majorant u k - majorant u (k + 1)) / (β * L)) ^ 2 := by
    intro k
    obtain ⟨ek, hek, -⟩ := exists_equiv_of_le_majorant hβ hL e he hβ' hLip hu0 hu1 hr (hb k)
    have hstep : step Fn F' (iterate Fn F' x₀ k) = iterate Fn F' x₀ (k + 1) :=
      (iterate_succ Fn F' x₀ k).symm
    have h := norm_apply_step_le hF hLip (hstay k) (by rw [hstep]; exact hstay (k + 1)) ek hek
    rw [hstep] at h
    refine h.trans ?_
    gcongr
    exact hd k
  have hFtend0 : Tendsto (fun k => Fn (iterate Fn F' x₀ (k + 1))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) hFnzero ?_
    have h1 : Tendsto (fun k => (majorant u k - majorant u (k + 1)) / (β * L)) atTop (𝓝 0) := by
      refine squeeze_zero
        (fun k => div_nonneg (by linarith [majorant_antitone hu0 hu1 k]) hA.le)
        (fun k => ?_) htend
      gcongr
      linarith [le_majorant hu0 hu1 (k + 1)]
    simpa using (h1.pow 2).const_mul (L / 2)
  have hFtend : Tendsto (fun k => Fn (iterate Fn F' x₀ (k + 1))) atTop (𝓝 (Fn xstar)) :=
    ((hF xstar hxball).continuousAt.tendsto).comp
      (hxstar.comp (Filter.tendsto_add_atTop_nat 1))
  have hroot : Fn xstar = 0 := tendsto_nhds_unique hFtend hFtend0
  have hapriori : ∀ k, ‖iterate Fn F' x₀ k - xstar‖ ≤ (majorant u k - u) / (β * L) := by
    intro k
    have h1 : Tendsto (fun m => ‖iterate Fn F' x₀ m - iterate Fn F' x₀ k‖) atTop
        (𝓝 ‖xstar - iterate Fn F' x₀ k‖) := (hxstar.sub_const _).norm
    have h2 : ‖xstar - iterate Fn F' x₀ k‖ ≤ (majorant u k - u) / (β * L) :=
      le_of_tendsto h1 (Filter.eventually_atTop.2 ⟨k, fun m hm => herr k m hm⟩)
    rwa [norm_sub_rev] at h2
  refine ⟨xstar, ?_, hroot, hxstar, hstay, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    exact hxmem
  · intro hpos k
    have hηpos : 0 < η := by
      rcases lt_or_ge 0 η with h | h
      · exact h
      · exact absurd hpos (by nlinarith)
    have hEq : (2 * (β * L * η)) ^ (2 ^ k) * η / ((2 : ℝ) ^ k * (β * L * η))
        = (1 - u ^ 2) ^ (2 ^ k) / (2 : ℝ) ^ k / (β * L) := by
      rw [hueta]
      field_simp
    rw [hEq]
    refine (hapriori k).trans ?_
    gcongr
    exact majorant_sub_le hu0 hu1 k

/-- Newton–Kantorovich (Atkinson–Han, *Theoretical Numerical Analysis*, Thm 5.4.2; Kress,
*Numerical Analysis*, Thm 6.14): if `‖(F' x₀)⁻¹‖ ≤ β`,
`‖(F' x₀)⁻¹ F x₀‖ ≤ η`, `F'` is `L`-Lipschitz on the ball of radius `r` around `x₀`,
`h := β L η ≤ 1/2` and `t* := (1 - √(1 - 2h)) / (β L) ≤ r`, then the Newton iterates stay in the
ball, converge to a root `x*` with `‖x* - x₀‖ ≤ t*`, and
`‖x_k - x*‖ ≤ (2h)^(2^k) η / (2^k h)` (a priori bound, `h > 0`).

Unlike `exists_ball_norm_step_sub_le`, every hypothesis here is checkable at the starting point:
existence of the root is a conclusion, not an assumption.  The proof is the majorant argument of
Ortega–Rheinboldt, *Iterative Solution of Nonlinear Equations in Several Variables*, carried by
`Newton.majorant`. -/
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
  have hh0 : (0 : ℝ) ≤ β * L * η := by positivity
  have hrad : (0 : ℝ) ≤ 1 - 2 * (β * L * η) := by linarith
  have hu2 : Real.sqrt (1 - 2 * (β * L * η)) ^ 2 = 1 - 2 * (β * L * η) := Real.sq_sqrt hrad
  have hu0 : (0 : ℝ) ≤ Real.sqrt (1 - 2 * (β * L * η)) := Real.sqrt_nonneg _
  have hu1 : Real.sqrt (1 - 2 * (β * L * η)) ≤ 1 := by nlinarith
  exact kantorovich_of_sq hβ hL e he hβ' hη' hF hLip hu0 hu1 (by linarith) hr

end Kantorovich

end Newton
