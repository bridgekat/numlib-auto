/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.NormPow`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.NormPow

/-!
# Real powers of the norm away from the origin

Mathlib's `hasFDerivAt_norm_rpow` differentiates `x ↦ ‖x‖ ^ p` on a real inner product space under
the hypothesis `1 < p`, which is what makes the function differentiable at the origin as well.
Away from the origin the same formula holds for *every* real exponent, and that is the case a
radial function with a singularity at the origin needs: the exponent is then typically negative.

## Main statements

* `hasFDerivAt_norm_rpow_of_ne_zero`: `x ↦ ‖x‖ ^ p` has derivative `h ↦ p ‖x‖^{p-2} ⟪x, h⟫` at
  every `x ≠ 0`, for every real `p`.
* `norm_fderiv_norm_rpow_of_ne_zero`: that derivative has operator norm `|p| ‖x‖^{p-1}`, which is
  the statement `|∇ |x|^p| = |p| |x|^{p-1}` in coordinate-free form.
-/

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {x : E}

/-- **The derivative of a real power of the norm away from the origin.** For every real `p` and
every `x ≠ 0`, the function `x ↦ ‖x‖ ^ p` is differentiable at `x`, with derivative
`h ↦ p ‖x‖^{p-2} ⟪x, h⟫`. Mathlib's `hasFDerivAt_norm_rpow` is the same formula under the
hypothesis `1 < p`, which buys differentiability at the origin too; here the exponent is arbitrary
and the origin is excluded. -/
theorem hasFDerivAt_norm_rpow_of_ne_zero (hx : x ≠ 0) (p : ℝ) :
    HasFDerivAt (fun x : E ↦ ‖x‖ ^ p) ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert! (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

/-- Away from the origin the derivative of `x ↦ ‖x‖ ^ p` has operator norm `|p| ‖x‖^{p-1}`: the
coordinate-free form of `|∇ |x|^p| = |p| |x|^{p-1}`. -/
theorem norm_fderiv_norm_rpow_of_ne_zero (hx : x ≠ 0) (p : ℝ) :
    ‖fderiv ℝ (fun x : E ↦ ‖x‖ ^ p) x‖ = |p| * ‖x‖ ^ (p - 1) := by
  rw [(hasFDerivAt_norm_rpow_of_ne_zero hx p).fderiv, norm_smul, norm_mul, innerSL_apply_norm,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) (p - 2)), mul_assoc,
    ← Real.rpow_add_one (norm_ne_zero_iff.2 hx)]
  ring_nf

/-- **The derivative of the norm away from the origin**: `h ↦ ⟪x, h⟫ / ‖x‖`. This is the case
`p = 1` of `hasFDerivAt_norm_rpow_of_ne_zero`, and the norm is not differentiable at the origin,
so the hypothesis `x ≠ 0` cannot be dropped. -/
theorem hasFDerivAt_norm_of_ne_zero (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h := hasFDerivAt_norm_rpow_of_ne_zero hx 1
  simp only [Real.rpow_one] at h
  convert h using 2
  rw [one_mul, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one]
