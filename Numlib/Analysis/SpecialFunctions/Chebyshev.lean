/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# The roots of the Vieta–Lucas polynomials

`Polynomial.Chebyshev.C R n` is the *rescaled* Chebyshev polynomial of the first kind, the
Vieta–Lucas polynomial, characterized by `C_n(2x) = 2 T_n(x)`. Mathlib has the degree, the leading
coefficient and the real roots of `T` but nothing about those of `C`, and the factorization of `C`
into linear factors is what a cyclic-reduction argument needs: the polynomial `C_{2^r}` evaluated at
a matrix is a product of `2^r` shifted copies of it, so one solve with `C_{2^r}(B)` is `2^r` solves
with tridiagonal matrices.

`C_n` is monic of degree `n` for `n ≥ 1` — unlike `T_n`, whose leading coefficient is `2^{n-1}` —
and `C_n(2 cos θ) = 2 cos(n θ)` puts its `n` roots at `2 cos((2k+1)π/(2n))`, `k = 0, …, n - 1`, all
in `(-2, 2)` and all simple.

## Main results

* `Polynomial.Chebyshev.eval_C_two_mul_cos`: `C_n(2 cos θ) = 2 cos(n θ)`.
* `Polynomial.Chebyshev.natDegree_C_natCast` and `Polynomial.Chebyshev.monic_C_natCast`.
* `Polynomial.Chebyshev.roots_C_real`: the roots as a multiset.
* `Polynomial.Chebyshev.C_natCast_eq_prod`: `C_n = ∏_{k<n} (X - 2 cos((2k+1)π/(2n)))`.
-/

open Real

namespace Polynomial.Chebyshev

/-- The `k`-th root `2 cos((2k+1)π/(2n))` of the Vieta–Lucas polynomial `C_n`.  Mathlib's
`Polynomial.Chebyshev.node` is a different family, the *extremal* points `cos(kπ/n)` of `T_n`. -/
noncomputable def rootNode (n k : ℕ) : ℝ := 2 * Real.cos ((2 * k + 1) * π / (2 * n))

/-- `C_n(2 cos θ) = 2 cos(n θ)`, the defining property `C_n(2x) = 2 T_n(x)` read at `x = cos θ`. -/
theorem eval_C_two_mul_cos (n : ℤ) (θ : ℝ) :
    (C ℝ n).eval (2 * Real.cos θ) = 2 * Real.cos (n * θ) := by
  have h := congrArg (Polynomial.eval (Real.cos θ)) (C_comp_two_mul_X ℝ n)
  rw [eval_comp] at h
  simp only [eval_mul, eval_ofNat, eval_X, T_real_cos] at h
  exact h

/-- `2 * X` has degree one, which is what makes `C_n ↦ C_n ∘ (2X)` degree-preserving. -/
private theorem natDegree_two_mul_X : ((2 : ℝ[X]) * X).natDegree = 1 := by
  rw [← C_ofNat, natDegree_C_mul two_ne_zero, natDegree_X]

/-- The leading coefficient of `2 * X`. -/
private theorem leadingCoeff_two_mul_X : ((2 : ℝ[X]) * X).leadingCoeff = 2 := by
  rw [← C_ofNat, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]

/-- The Vieta–Lucas polynomial `C_n` has degree `n`: composing with `2X` neither raises nor lowers
a degree, and `C_n ∘ (2X) = 2 T_n`. -/
@[simp] theorem natDegree_C_natCast (n : ℕ) : (C ℝ (n : ℤ)).natDegree = n := by
  have h := natDegree_comp (p := C ℝ (n : ℤ)) (q := (2 : ℝ[X]) * X)
  rw [C_comp_two_mul_X, natDegree_two_mul_X, mul_one, ← C_ofNat,
    natDegree_C_mul two_ne_zero, natDegree_T] at h
  simpa using h.symm

/-- The Vieta–Lucas polynomial `C_n` is **monic** for `n ≥ 1`: the leading coefficient `2^{n-1}` of
`T_n` is rescaled to `2 · 2^{n-1} / 2^n = 1`. -/
theorem monic_C_natCast {n : ℕ} (hn : n ≠ 0) : (C ℝ (n : ℤ)).Monic := by
  have h := leadingCoeff_comp (p := C ℝ (n : ℤ)) (q := (2 : ℝ[X]) * X)
    (by rw [natDegree_two_mul_X]; norm_num)
  rw [C_comp_two_mul_X, leadingCoeff_two_mul_X, natDegree_C_natCast, ← C_ofNat, leadingCoeff_mul,
    leadingCoeff_C, leadingCoeff_T] at h
  have h2 : (2 : ℝ) * 2 ^ (n - 1) = 2 ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  simp only [Int.natAbs_natCast] at h
  rw [h2] at h
  have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hlc : (C ℝ (n : ℤ)).leadingCoeff = 1 :=
    mul_right_cancel₀ hne (by rw [one_mul]; exact h.symm)
  exact hlc

/-- The nodes of `C_n` are pairwise distinct: they are `2` times the nodes of `T_n`, which Mathlib
records as `Polynomial.Chebyshev.roots_T_real_nodup`. -/
theorem injOn_rootNode (n : ℕ) : Set.InjOn (rootNode n) (Finset.range n) := by
  have h := (Finset.range n).nodup_map_iff_injOn.mp (roots_T_real_nodup n)
  intro a ha b hb hab
  refine h ha hb ?_
  simp only [rootNode] at hab
  linarith

/-- The **roots of the Vieta–Lucas polynomial** `C_n` over `ℝ`: the `n` distinct reals
`2 cos((2k+1)π/(2n))`, `k = 0, …, n - 1`. -/
theorem roots_C_real (n : ℕ) :
    (C ℝ (n : ℤ)).roots = ((Finset.range n).image (rootNode n)).val := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero, C_zero, ← C_ofNat, roots_C]
    simp
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hmonic : (C ℝ (n : ℤ)).Monic := monic_C_natCast hn
  refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) ?_
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    rw [rootNode, eval_C_two_mul_cos, mul_eq_zero]
    refine Or.inr ?_
    rw [Real.cos_eq_zero_iff]
    refine ⟨k, ?_⟩
    push_cast
    field_simp
  · rw [Finset.card_image_of_injOn (injOn_rootNode n), Finset.card_range,
      Polynomial.degree_eq_natDegree hmonic.ne_zero, natDegree_C_natCast]

/-- **The Vieta–Lucas polynomial splits into its linear factors**:
`C_n = ∏_{k<n} (X - 2 cos((2k+1)π/(2n)))` for `n ≥ 1`. Being monic of degree `n` with `n` distinct
real roots, it is the product of the corresponding monic linear factors. -/
theorem C_natCast_eq_prod {n : ℕ} (hn : n ≠ 0) :
    C ℝ (n : ℤ) = ∏ k ∈ Finset.range n, (X - Polynomial.C (rootNode n k)) := by
  have hcard : Multiset.card (C ℝ (n : ℤ)).roots = (C ℝ (n : ℤ)).natDegree := by
    rw [roots_C_real, natDegree_C_natCast]
    change ((Finset.range n).image (rootNode n)).card = n
    rw [Finset.card_image_of_injOn (injOn_rootNode n), Finset.card_range]
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_C_natCast hn) hcard
  rw [roots_C_real, Finset.image_val_of_injOn (injOn_rootNode n), Multiset.map_map] at hprod
  exact hprod.symm

end Polynomial.Chebyshev
