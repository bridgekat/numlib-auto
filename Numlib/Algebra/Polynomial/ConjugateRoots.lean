/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic

/-!
# Polynomial equations involving an involution

Over a field with an involution, solutions of $p(z)=z^*$ are roots of
$\overline p(p(z))-z$, where $\overline p$ conjugates the coefficients of $p$.
This gives a square-degree bound for polynomials of degree at least two.
-/

namespace Polynomial

/-- A polynomial $p$ of degree at least two over an involutive field has at
most $(\deg p)^2$ distinct solutions to $p(z)=z^*$. The solution set is finite. -/
theorem finite_setOf_eval_eq_star_and_ncard_le_sq {K : Type*} [Field K] [StarRing K]
    (p : K[X]) (hp : 1 < p.natDegree) :
    {z : K | p.eval z = star z}.Finite ∧
      {z : K | p.eval z = star z}.ncard ≤ p.natDegree ^ 2 := by
  let f := starRingEnd K
  let q := (p.map f).comp p - X
  have hdegree : ((p.map f).comp p).natDegree = p.natDegree ^ 2 := by
    rw [natDegree_comp, natDegree_map_eq_of_injective star_injective, pow_two]
  have hsq : 1 < p.natDegree ^ 2 := by
    rw [pow_two]
    exact Nat.one_lt_mul_iff.2 ⟨by omega, by omega, by omega⟩
  have hdegq : q.natDegree = p.natDegree ^ 2 := by
    dsimp only [q]
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa only [natDegree_X, hdegree] using hsq),
      hdegree]
  have hq : q ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdegq
    omega
  have hsub : {z : K | p.eval z = star z} ⊆ q.rootSet K := by
    intro z hz
    change p.eval z = f z at hz
    rw [mem_rootSet_of_ne hq]
    change ((p.map f).comp p - X).eval z = 0
    rw [eval_sub, eval_comp, hz, eval_map_apply, hz, eval_X]
    exact sub_eq_zero.mpr (star_star z)
  have hfin : (q.rootSet K).Finite := q.rootSet_finite K
  exact ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans
    ((ncard_rootSet_le q K).trans_eq hdegq)⟩

end Polynomial
