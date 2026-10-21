import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Ray

/-!
# A mean value inequality with one exceptional point

A derivative bound away from one point gives the usual Lipschitz estimate on segments
avoiding that point. A matching radial bound suffices for segments meeting the point.
-/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {C : ℝ} {a : E}

/-- A radial estimate at one exceptional point and a derivative bound elsewhere imply
the global mean value inequality, including segments through the exceptional point. -/
theorem norm_sub_le_of_norm_fderiv_le_off_point
    (hf : ∀ z, z ≠ a → DifferentiableAt ℝ f z)
    (hb : ∀ z, z ≠ a → ‖fderiv ℝ f z‖ ≤ C)
    (ha : ∀ z, ‖f z - f a‖ ≤ C * ‖z - a‖) (x y : E) :
    ‖f x - f y‖ ≤ C * ‖x - y‖ := by
  by_cases hmem : a ∈ segment ℝ x y
  · have he := (mem_segment_iff_sameRay.mp hmem).norm_add
    have he' : ‖x - y‖ = ‖x - a‖ + ‖y - a‖ := by
      rw [show a - x + (y - a) = y - x by abel] at he
      simpa only [norm_sub_rev a x, norm_sub_rev y x] using he
    calc
      _ ≤ ‖f x - f a‖ + ‖f y - f a‖ := by
        simpa only [norm_sub_rev (f a) (f y)] using
          norm_sub_le_norm_sub_add_norm_sub (f x) (f a) (f y)
      _ ≤ C * ‖x - a‖ + C * ‖y - a‖ := add_le_add (ha x) (ha y)
      _ = C * ‖x - y‖ := by rw [he']; ring
  · apply (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => hf z (by rintro rfl; exact hmem hz))
      (fun z hz => hb z (by rintro rfl; exact hmem hz))
      (right_mem_segment ℝ x y) (left_mem_segment ℝ x y)
