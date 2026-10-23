import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Ray

/-!
# Sharp Lipschitz bounds with a puncture at the origin

A segment avoiding zero admits the usual mean-value estimate. On a segment
containing zero, radial growth and the exact equality of the two radial lengths
with the endpoint distance give the same estimate.
-/

open Set
section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- A derivative bound off the origin and the same bound on radial growth imply
a global Lipschitz estimate with the unchanged constant. -/
theorem norm_sub_le_of_punctured_fderiv_bound {g : E → F} {C : ℝ}
    (hg : ∀ z, ‖g z - g 0‖ ≤ C * ‖z‖)
    (hd : ∀ z : E, z ≠ 0 → DifferentiableAt ℝ g z)
    (hb : ∀ z : E, z ≠ 0 → ‖fderiv ℝ g z‖ ≤ C) (x y : E) :
    ‖g x - g y‖ ≤ C * ‖x - y‖ := by
  by_cases hz : (0 : E) ∈ segment ℝ x y
  · have hn := (mem_segment_iff_sameRay.mp hz).norm_add
    have he : ‖x‖ + ‖y‖ = ‖x - y‖ := by
      simpa only [zero_sub, sub_zero, neg_add_eq_sub, norm_neg, norm_sub_rev] using hn.symm
    calc
      ‖g x - g y‖ ≤ ‖g x - g 0‖ + ‖g y - g 0‖ := by
        simpa only [norm_sub_rev (g 0)] using
          norm_sub_le_norm_sub_add_norm_sub (g x) (g 0) (g y)
      _ ≤ C * ‖x‖ + C * ‖y‖ := add_le_add (hg x) (hg y)
      _ = _ := by rw [← mul_add, he]
  · have hz' (z : E) (hzs : z ∈ segment ℝ x y) : z ≠ 0 := by
      intro he
      exact hz (he ▸ hzs)
    simpa only [norm_sub_rev] using
      (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
        (fun z hzs => hd z (hz' z hzs)) (fun z hzs => hb z (hz' z hzs))
        (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
end General
