/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Topology.Algebra.InfiniteSum.Group`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Splitting off a finite set of terms from an infinite sum

Mathlib's `Summable.tsum_eq_add_tsum_ite` splits one term `f b` off a summable family, and
`Summable.sum_add_tsum_compl` splits off a finite set `s` with the rest as a sum over the
subtype `(↑s)ᶜ`. `Summable.tsum_eq_sum_add_tsum_ite` is the finite-set version in the `ite` form
of the first: `∑' b, f b = ∑ b ∈ s, f b + ∑' b, if b ∈ s then 0 else f b`.
-/

variable {α β : Type*} [AddCommGroup α] [TopologicalSpace α] [IsTopologicalAddGroup α]
  [T2Space α] [DecidableEq β]

/-- A summable family split into the terms indexed by a finite set `s` and the rest:
`∑' b, f b = ∑ b ∈ s, f b + ∑' b, if b ∈ s then 0 else f b`. The finite-set version of
`Summable.tsum_eq_add_tsum_ite`. -/
theorem Summable.tsum_eq_sum_add_tsum_ite {f : β → α} (hf : Summable f) (s : Finset β) :
    ∑' b, f b = ∑ b ∈ s, f b + ∑' b, (if b ∈ s then 0 else f b) := by
  rw [← hf.sum_add_tsum_compl (s := s), tsum_subtype]
  congr 1
  refine tsum_congr fun b => ?_
  by_cases hb : b ∈ s <;> simp [hb]
