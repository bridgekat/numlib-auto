import Mathlib.Analysis.Convex.Deriv

/-!
# Supporting lines of differentiable real convex functions

The derivative determines a supporting affine function, with a strict inequality away from
the contact point under strict convexity. Concave versions follow by negation.
-/

open Set

/-- The tangent line supports a differentiable convex function from below. -/
theorem ConvexOn.tangent_le {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hd : DifferentiableAt ℝ f x) :
    f x + deriv f x * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hs := hf.deriv_le_slope hx hy hxy hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at hs
    linarith
  · simp
  · have hs := hf.slope_le_deriv hy hx hyx hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at hs
    nlinarith

/-- A strictly convex function lies strictly above its tangent away from the contact point. -/
theorem StrictConvexOn.tangent_lt {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConvexOn ℝ s f)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hd : DifferentiableAt ℝ f x) (hxy : x ≠ y) :
    f x + deriv f x * (y - x) < f y := by
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · have hs := hf.deriv_lt_slope hx hy hxy hd
    rw [slope_def_field, lt_div_iff₀ (sub_pos.mpr hxy)] at hs
    linarith
  · have hs := hf.slope_lt_deriv hy hx hyx hd
    rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr hyx)] at hs
    nlinarith

/-- The tangent line supports a differentiable concave function from above. -/
theorem ConcaveOn.le_tangent {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hd : DifferentiableAt ℝ f x) :
    f y ≤ f x + deriv f x * (y - x) := by
  have hh := hf.neg.tangent_le hx hy hd.neg
  simp only [Pi.neg_apply, deriv.neg] at hh
  linarith

/-- A strictly concave function lies strictly below its tangent away from the contact point. -/
theorem StrictConcaveOn.lt_tangent {s : Set ℝ} {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ s f)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hd : DifferentiableAt ℝ f x) (hxy : x ≠ y) :
    f y < f x + deriv f x * (y - x) := by
  have hh := hf.neg.tangent_lt hx hy hd.neg hxy
  simp only [Pi.neg_apply, deriv.neg] at hh
  linarith
