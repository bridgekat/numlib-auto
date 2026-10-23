import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# The quadratic remainder for a Lipschitz derivative

The sharp first-order Taylor remainder bound follows by comparing the norm of
the remainder along a segment with a quadratic scalar function. Only derivatives
on that segment and their Lipschitz bound relative to its initial point are used.
-/

open Set Metric

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first-order Taylor remainder is at most `L * ‖v‖² / 2` when the derivative
is `L`-Lipschitz from the initial point along the segment. -/
theorem norm_sub_sub_fderiv_le_half_of_segment_bound {f : E → F}
    {f' : E → E →L[ℝ] F} {x v : E} {L : ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt f (f' (x + t • v)) (x + t • v))
    (hL : ∀ t ∈ Icc (0 : ℝ) 1, ‖f' (x + t • v) - f' x‖ ≤ L * ‖t • v‖) :
    ‖f (x + v) - f x - f' x v‖ ≤ L * ‖v‖ ^ 2 / 2 := by
  let r : ℝ → F := fun t => f (x + t • v) - f x - t • f' x v
  let r' : ℝ → F := fun t => (f' (x + t • v) - f' x) v
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt r (r' t) t := by
    intro t ht
    have hline : HasDerivAt (fun u : ℝ => x + u • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h := ((hf t ht).comp_hasDerivAt t hline).sub_const (f x)
    exact (h.sub ((hasDerivAt_id t).smul_const (f' x v))).congr_deriv (by simp [r'])
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖r' t‖ ≤ L * ‖v‖ ^ 2 * t := by
    intro t ht
    calc
      ‖r' t‖ ≤ ‖f' (x + t • v) - f' x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L * ‖t • v‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (hL t (Ico_subset_Icc_self ht)) (norm_nonneg _)
      _ = L * ‖v‖ ^ 2 * t := by
        rw [norm_smul, Real.norm_of_nonneg ht.1]
        ring
  have hB : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => L * ‖v‖ ^ 2 * t ^ 2 / 2) (L * ‖v‖ ^ 2 * t) t := by
    intro t
    exact (((hasDerivAt_pow 2 t).const_mul (L * ‖v‖ ^ 2)).div_const 2).congr_deriv
      (by ring)
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := r) (f' := r') (a := 0) (b := 1)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (B := fun t => L * ‖v‖ ^ 2 * t ^ 2 / 2) (B' := fun t => L * ‖v‖ ^ 2 * t)
    (by simp [r]) hB hbound (right_mem_Icc.mpr zero_le_one)
  simpa [r] using h

/-- The sharp quadratic Taylor bound for a globally Lipschitz derivative map.
The derivative values are tied to `f` by `HasFDerivAt`. -/
theorem norm_sub_sub_fderiv_le_half_of_lipschitz_bound {f : E → F}
    {f' : E → E →L[ℝ] F} {L : ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hL : ∀ x y, ‖f' x - f' y‖ ≤ L * ‖x - y‖) (x v : E) :
    ‖f (x + v) - f x - f' x v‖ ≤ L * ‖v‖ ^ 2 / 2 :=
  norm_sub_sub_fderiv_le_half_of_segment_bound (fun t _ => hf (x + t • v))
    (fun t _ => by simpa using hL (x + t • v) x)

end
