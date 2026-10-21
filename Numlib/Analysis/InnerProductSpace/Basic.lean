/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Basic`, beside
`norm_sub_sq_eq_norm_sq_add_norm_sq_real`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Pythagoras for a difference

`norm_sub_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`: over any `RCLike` field, orthogonal `x`, `y`
have `‖x - y‖² = ‖x‖² + ‖y‖²`. Mathlib has the sum form over any `RCLike` field
(`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`) but the difference form only over `ℝ`
(`norm_sub_sq_eq_norm_sq_add_norm_sq_real`).

Those two siblings state the product form `‖x‖ * ‖x‖` despite the `sq` in their names. This lemma
states powers `‖x‖ ^ 2`, which is what `sq` names in Mathlib's `norm_sub_sq`; a caller that needs
the product form rewrites with `sq`.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Pythagoras for a difference of orthogonal vectors**, in squared form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E)
    (h : (inner 𝕜 x y : 𝕜) = 0) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h' : (inner 𝕜 x (-y) : 𝕜) = 0 := by rw [inner_neg_right, h, neg_zero]
  have key := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) x (-y) h'
  rw [← sub_eq_add_neg, norm_neg] at key
  rw [pow_two, pow_two, pow_two, key]
