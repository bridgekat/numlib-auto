import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The second-order mean value inequality with the sharp constant

If `f` has derivative `f' z` at every point of a convex set and `‖f' z - f' x‖ ≤ C ‖z - x‖` there,
then `‖f y - f x - f' x (y - x)‖ ≤ C / 2 * ‖y - x‖ ^ 2`.

Mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` bounds the same quantity using a
*constant* bound on `‖f' z - f' x‖`, which loses the factor `1 / 2`. The sharp form below
integrates the variable bound along the segment instead. It is the natural candidate for
upstreaming to `Mathlib.Analysis.Calculus.MeanValue`, and is what makes the quadratic convergence
rate of Newton's method come out with the textbook constant.
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
