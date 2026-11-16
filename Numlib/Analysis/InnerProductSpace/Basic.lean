/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

Let $E$ be an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. If $x, y \in E$
are orthogonal, then $\|x - y\|^2 = \|x\|^2 + \|y\|^2$. This module proves this form of the theorem
of Pythagoras.

## Main results

* `norm_sub_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`: if $\langle x, y \rangle = 0$, then
  $\|x - y\|^2 = \|x\|^2 + \|y\|^2$.

## Implementation notes

* Mathlib has the form for a sum over every field $\mathbb{K}$
  (`norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`), but the form for a difference only over
  $\mathbb{R}$ (`norm_sub_sq_eq_norm_sq_add_norm_sq_real`).
* These two Mathlib lemmas state the product form `‖x‖ * ‖x‖`, although their names contain `sq`.
  The lemma here states the power `‖x‖ ^ 2`, which is what `sq` names in Mathlib's `norm_sub_sq`. A
  caller that needs the product form rewrites with `sq`.
-/

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Pythagoras for a difference of orthogonal vectors**: let $E$ be an inner product space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let $x, y \in E$ with $\langle x, y \rangle = 0$.
Then
$$\|x - y\|^2 = \|x\|^2 + \|y\|^2.$$
-/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E)
    (h : (inner 𝕜 x y : 𝕜) = 0) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h' : (inner 𝕜 x (-y) : 𝕜) = 0 := by rw [inner_neg_right, h, neg_zero]
  have key := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) x (-y) h'
  rw [← sub_eq_add_neg, norm_neg] at key
  rw [pow_two, pow_two, pow_two, key]
