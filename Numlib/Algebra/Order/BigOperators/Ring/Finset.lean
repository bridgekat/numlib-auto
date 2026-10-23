/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Order.BigOperators.Ring.Finset`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite product and Cauchy–Schwarz inequalities

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

variable {ι R : Type*} [CommRing R]
/-- The finite Lagrange identity over any commutative ring. -/
theorem sum_mul_sub_mul_sq (s : Finset ι) (a b : ι → R) :
    (∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i)^2) =
      2 * ((∑ i ∈ s, (a i)^2) * (∑ i ∈ s, (b i)^2) - (∑ i ∈ s, a i * b i)^2) := by
  have h₁ : (∑ i ∈ s, ∑ j ∈ s, (a i * b j)^2) =
      (∑ i ∈ s, (a i)^2) * (∑ i ∈ s, (b i)^2) := by
    simp_rw [mul_pow, ← Finset.mul_sum]
    rw [Finset.sum_mul]
  have h₂ : (∑ i ∈ s, ∑ j ∈ s, (a j * b i)^2) =
      (∑ i ∈ s, (a i)^2) * (∑ i ∈ s, (b i)^2) := by
    rw [Finset.sum_comm]
    exact h₁
  have h₃ : (∑ i ∈ s, ∑ j ∈ s, 2*(a i * b j)*(a j * b i)) =
      2*(∑ i ∈ s, a i * b i)^2 := by
    have heq (i j : ι) : 2*(a i * b j)*(a j * b i) = 2*((a i * b i)*(a j * b j)) := by ring
    simp_rw [heq, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
    ring
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h₁, h₂, h₃]
  ring

variable [LinearOrder R] [IsStrictOrderedRing R]
/-- Cauchy–Schwarz is strict if two coordinate pairs are not proportional. -/
theorem sum_mul_sq_lt_sq_mul_sq (s : Finset ι) (a b : ι → R)
    (h : ∃ i ∈ s, ∃ j ∈ s, a i * b j ≠ a j * b i) :
    (∑ i ∈ s, a i * b i)^2 < (∑ i ∈ s, (a i)^2) * (∑ i ∈ s, (b i)^2) := by
  obtain ⟨i,hi,j,hj,hij⟩ := h
  have hh : 0 < ∑ u ∈ s, ∑ v ∈ s, (a u * b v - a v * b u)^2 := by
    apply Finset.sum_pos'
    · intro u _
      exact Finset.sum_nonneg (fun v _ => sq_nonneg _)
    · refine ⟨i, hi, ?_⟩
      exact Finset.sum_pos' (fun v _ => sq_nonneg _) ⟨j, hj,
        sq_pos_of_ne_zero (sub_ne_zero.mpr hij)⟩
  rw [sum_mul_sub_mul_sq] at hh
  linarith

end Finset
