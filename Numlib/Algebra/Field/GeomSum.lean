/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Field.GeomSum`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Field.GeomSum

/-!
# Geometric sums of roots of unity

Mathlib's `IsPrimitiveRoot.geom_sum_eq_zero` sums the powers of a *primitive* `k`-th root of unity.
`geom_sum_eq_ite_of_pow_eq_one` needs only `x ^ n = 1`: the sum `∑_{i < n} x ^ i` is `n` at `x = 1`
and `0` otherwise, which is the orthogonality relation of the characters of a finite cyclic group.
-/

/-- **The geometric sum of an `n`-th root of unity**: if `x ^ n = 1` then
`∑_{i < n} x ^ i` is `n` at `x = 1` and `0` otherwise. -/
theorem geom_sum_eq_ite_of_pow_eq_one {α : Type*} [DivisionRing α] [DecidableEq α] {x : α}
    {n : ℕ} (h : x ^ n = 1) :
    ∑ i ∈ Finset.range n, x ^ i = if x = 1 then (n : α) else 0 := by
  rcases eq_or_ne x 1 with rfl | hx
  · simp
  · rw [ite_eq_right hx, geom_sum_eq hx, h, sub_self, zero_div]
