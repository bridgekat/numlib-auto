/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.RCLike.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.RCLike.Basic

/-!
# Unimodular scalars

A scalar `c` of an `RCLike` field with `star c * c = 1` has norm `1`
(`RCLike.norm_eq_one_of_star_mul_self_eq_one`): the entries of a unitary diagonal matrix are
unimodular, which is the form in which the uniqueness statements of the QR and Hessenberg
factorizations ("unique up to a unimodular diagonal") deliver them.
-/

/-- A scalar with `star c * c = 1` has norm `1`. -/
theorem RCLike.norm_eq_one_of_star_mul_self_eq_one {𝕜 : Type*} [RCLike 𝕜] {c : 𝕜}
    (hc : star c * c = 1) : ‖c‖ = 1 := by
  have h1 : ‖star c * c‖ = 1 := by rw [hc, norm_one]
  rw [norm_mul, norm_star] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 (by rw [sq]; exact h1)
