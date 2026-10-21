/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Order.BigOperators.Ring.Finset`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# The Weierstrass product inequality

`Finset.one_sub_sum_le_prod_one_sub`: `1 - ∑ bᵢ ≤ ∏ (1 - bᵢ)` for `bᵢ ∈ [0, 1]`, the lower bound
on a product of factors `1 - bᵢ` that keeps it away from `0` while `∑ bᵢ` is small.
-/

namespace Finset

/-- **The Weierstrass product inequality**: `1 - ∑ bᵢ ≤ ∏ (1 - bᵢ)` for `bᵢ ∈ [0, 1]`. -/
theorem one_sub_sum_le_prod_one_sub {ι R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (s : Finset ι) (b : ι → R) (hb0 : ∀ i ∈ s, 0 ≤ b i)
    (hb1 : ∀ i ∈ s, b i ≤ 1) : 1 - ∑ i ∈ s, b i ≤ ∏ i ∈ s, (1 - b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have ih' := ih (fun i hi => hb0 i (mem_insert_of_mem hi))
      (fun i hi => hb1 i (mem_insert_of_mem hi))
    have hS : 0 ≤ ∑ i ∈ s, b i := sum_nonneg fun i hi => hb0 i (mem_insert_of_mem hi)
    have h0 := hb0 a (mem_insert_self a s)
    have h1 := hb1 a (mem_insert_self a s)
    nlinarith [ih', h0, h1]

end Finset
