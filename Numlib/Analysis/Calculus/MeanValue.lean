import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Numlib.Analysis.Calculus.RootMultiplicity
import Numlib.Approximation.DividedDifference

/-!
# Mean value inequalities with explicit constants

Three mean value statements the error analyses of this library need and Mathlib does not carry:
the second-order inequality with the sharp constant, and two local statements saying that a
difference quotient of a `C¹` function is uniformly close to the derivative near a point, and a
second divided difference of a `C²` function uniformly close to half the second derivative.

## The sharp second-order inequality

If `f` has derivative `f' z` at every point of a convex set and `‖f' z - f' x‖ ≤ C ‖z - x‖` there,
then `‖f y - f x - f' x (y - x)‖ ≤ C / 2 * ‖y - x‖ ^ 2`
(`Convex.norm_image_sub_sub_le_of_norm_hasFDerivAt_sub_le`).

Mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` bounds the same quantity using a
*constant* bound on `‖f' z - f' x‖`, which loses the factor `1 / 2`. The sharp form below
integrates the variable bound along the segment instead. It is the natural candidate for
upstreaming to `Mathlib.Analysis.Calculus.MeanValue`, and is what makes the quadratic convergence
rate of Newton's method come out with the textbook constant.

## Divided differences near a point

`exists_ball_abs_slope_sub_deriv_le` bounds `|(h y - h x) / (y - x) - h'(a)|` by any prescribed
`ε > 0` on a ball around `a`, for `h` of class `C¹`; it is the mean value inequality applied to
`h - h'(a) · id`. `exists_ball_abs_newton_three_sub_le` is its three-node analogue for `f` of
class `C²`, bounding `|f[x, y, z] - f''(a)/2|` at pairwise distinct nodes of a ball. Unlike the
first it is a genuine mean value *theorem* (`DividedDifference.exists_newton_three_eq`, Rolle
twice), because no node can be singled out to lower the order through `dslope`. Both are the form
in which a local convergence proof of a derivative-free rootfinder
(`Numlib/Nonlinear/Secant`) needs its divided differences controlled; neither has any rootfinding
content of its own.
-/

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

/-- **Difference quotients of a `C¹` function are close to its derivative** near a point: for every
`ε > 0` there is a ball around `a` on which `|(h y - h x) / (y - x) - h'(a)| ≤ ε` for all `x ≠ y`.
The mean value inequality for `h - h'(a) · id`, whose derivative is small on the ball. -/
theorem exists_ball_abs_slope_sub_deriv_le {h : ℝ → ℝ} {a : ℝ} (hh : ContDiffAt ℝ 1 h a) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ x ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ, x ≠ y →
      |(h y - h x) / (y - x) - deriv h a| ≤ ε := by
  have hd := hh.eventually_hasDerivAt
  have hc := hh.continuousAt_deriv.eventually (Metric.closedBall_mem_nhds (deriv h a) hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hd.and hc)
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have hne : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have key : ‖(h y - deriv h a * y) - (h x - deriv h a * x)‖ ≤ ε * ‖y - x‖ := by
    refine (convex_ball a δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z => h z - deriv h a * z) (f' := fun z => deriv h z - deriv h a)
      (fun z hz => ?_) (fun z hz => ?_) hx hy
    · exact ((hball (Metric.mem_ball.1 hz)).1.sub ((hasDerivAt_id z).const_mul _)).hasDerivWithinAt
        |>.congr_deriv (by ring)
    · have := (hball (Metric.mem_ball.1 hz)).2
      rwa [dist_eq_norm] at this
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at key
  rw [show (h y - h x) / (y - x) - deriv h a =
      ((h y - deriv h a * y) - (h x - deriv h a * x)) / (y - x) by field_simp; ring, abs_div,
    div_le_iff₀ (abs_pos.2 hne)]
  exact key

/-- **Second divided differences of a `C²` function are close to `f''(a)/2`** near a point: for
every `η > 0` there is a ball around `a` on which `|f[x, y, z] - f''(a)/2| ≤ η` for all pairwise
distinct `x, y, z` in it. The three-node analogue of `exists_ball_abs_slope_sub_deriv_le`, and —
unlike it — a genuine mean value *theorem* (`DividedDifference.exists_newton_three_eq`, Rolle
twice) rather than a mean value inequality, because no node can be singled out to lower the order
through `dslope`. -/
theorem exists_ball_abs_newton_three_sub_le {f : ℝ → ℝ} {a : ℝ} (hf : ContDiffAt ℝ 2 f a)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ, ∀ z ∈ Metric.ball a δ,
      x ≠ y → x ≠ z → y ≠ z →
      |DividedDifference.newton f ![x, y, z] - iteratedDeriv 2 f a / 2| ≤ η := by
  obtain ⟨r, hr, hd, hc⟩ :=
    ContDiffAt.exists_ball_hasDerivAt_iteratedDeriv (N := 2) (by exact_mod_cast hf)
  have hca : ContinuousAt (iteratedDeriv 2 f) a := hc.continuousAt (Metric.ball_mem_nhds a hr)
  obtain ⟨δ₁, hδ₁, hb⟩ := Metric.eventually_nhds_iff.1
    (hca.eventually (Metric.closedBall_mem_nhds (iteratedDeriv 2 f a) hη))
  refine ⟨min r δ₁, lt_min hr hδ₁, fun x hx y hy z hz hxy hxz hyz => ?_⟩
  have hsub : Metric.ball a (min r δ₁) ⊆ Metric.ball a r :=
    Metric.ball_subset_ball (min_le_left _ _)
  obtain ⟨ξ, hξ, hv⟩ := DividedDifference.exists_newton_three_eq
    (f₁ := iteratedDeriv 1 f) (f₂ := iteratedDeriv 2 f)
    (convex_ball a (min r δ₁)) hx hy hz hxy hxz hyz
    (fun u hu => by
      simpa only [iteratedDeriv_zero, zero_add] using hd 0 (by norm_num) u (hsub hu))
    (fun u hu => hd 1 (by norm_num) u (hsub hu))
  have hξ' : |iteratedDeriv 2 f ξ - iteratedDeriv 2 f a| ≤ η := by
    have h := hb (Metric.mem_ball.1 (Metric.ball_subset_ball (min_le_right r δ₁) hξ))
    rwa [Real.dist_eq] at h
  rw [hv, show iteratedDeriv 2 f ξ / 2 - iteratedDeriv 2 f a / 2
    = (iteratedDeriv 2 f ξ - iteratedDeriv 2 f a) / 2 by ring, abs_div, abs_two]
  linarith
