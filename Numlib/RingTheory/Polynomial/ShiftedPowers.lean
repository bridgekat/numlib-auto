/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Algebra.Polynomial.Degree.Lemmas` or `Mathlib.LinearAlgebra.Vandermonde`,
beside `Matrix.det_vandermonde_ne_zero_iff`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The shifted powers `(X - y_j)^k` at distinct points

Over a field of characteristic zero, the `k + 1` polynomials `(X - y_j)^k` at distinct points
`y_0, …, y_k` are linearly independent (`Polynomial.linearIndependent_X_sub_C_pow`) — they are a
basis of the polynomials of degree at most `k` — and on `k + 2` distinct points the kernel of
`c ↦ ∑_j c_j (X - y_j)^k` is one-dimensional
(`Polynomial.exists_eq_smul_of_sum_C_mul_X_sub_C_pow_eq_zero`). The proof extracts the
coefficients of a vanishing combination, which are the moments `∑_j c_j (-y_j)^p`, `p ≤ k`, a
Vandermonde system in the `c_j`.

This is the algebraic fact behind Schoenberg's characterization of the B-spline as the piecewise
polynomial of minimal support (`Numlib/Approximation/BSpline.lean`).
-/

open Polynomial

namespace Polynomial

/-- **The `k + 1` powers `(X - y_j)^k` at distinct points are linearly independent**: extracting
the coefficients of a vanishing combination gives the vanishing of the moments
`∑_j c_j (-y_j)^p`, `p ≤ k`, a Vandermonde system in the `c_j`. -/
theorem linearIndependent_X_sub_C_pow {K : Type*} [Field K] [CharZero K] {k : ℕ}
    {y : Fin (k + 1) → K} (hy : Function.Injective y) :
    LinearIndependent K fun j => (X - C (y j)) ^ k := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmom : ∀ p : Fin (k + 1), ∑ j, g j * (-y j) ^ (p : ℕ) = 0 := by
    intro p
    have h := congrArg (fun q : K[X] => q.coeff (k - p)) hg
    simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_zero] at h
    have hc : ∀ j, ((X - C (y j)) ^ k).coeff (k - p)
        = (-y j) ^ (p : ℕ) * (k.choose (k - p) : K) := by
      intro j
      rw [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
      congr 2
      have := p.2
      omega
    simp only [hc, ← mul_assoc, ← Finset.sum_mul] at h
    refine (mul_eq_zero.mp h).resolve_right ?_
    exact_mod_cast (Nat.choose_pos (Nat.sub_le k p)).ne'
  have hvm : Matrix.vecMul g (Matrix.vandermonde fun j => -y j) = 0 := by
    funext p
    simpa [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply] using hmom p
  have hdet : (Matrix.vandermonde fun j => -y j).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr (neg_injective.comp hy)
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hvm)

/-- **The kernel of `c ↦ ∑_j c_j (X - y_j)^k` on `k + 2` distinct points is one-dimensional**:
two vanishing combinations, the second nontrivial, are proportional. -/
theorem exists_eq_smul_of_sum_C_mul_X_sub_C_pow_eq_zero {K : Type*} [Field K] [CharZero K]
    {k : ℕ} {y : Fin (k + 2) → K} (hy : Function.Injective y) {c c' : Fin (k + 2) → K}
    (hc : ∑ j, C (c j) * (X - C (y j)) ^ k = 0)
    (hc' : ∑ j, C (c' j) * (X - C (y j)) ^ k = 0) (hne : c' ≠ 0) :
    ∃ l : K, c = l • c' := by
  obtain ⟨m, hm⟩ : ∃ m, c' m ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  refine ⟨c m / c' m, ?_⟩
  set d : Fin (k + 2) → K := c - (c m / c' m) • c' with hd
  have hdm : d m = 0 := by simp [hd, div_mul_cancel₀ _ hm]
  have hdsum : ∑ j, C (d j) * (X - C (y j)) ^ k = 0 := by
    simp only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, C_sub, C_mul, sub_mul,
      Finset.sum_sub_distrib, hc, mul_assoc, ← Finset.mul_sum, hc', mul_zero, sub_zero]
  have hli := linearIndependent_X_sub_C_pow (hy.comp (Fin.succAbove_right_injective (p := m)))
  rw [Fintype.linearIndependent_iff] at hli
  have h0 : ∀ j, d (m.succAbove j) = 0 := by
    refine hli (fun j => d (m.succAbove j)) ?_
    rw [Fin.sum_univ_succAbove _ m, hdm, C_0, zero_mul, zero_add] at hdsum
    simpa only [smul_eq_C_mul, Function.comp] using hdsum
  have : d = 0 := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove m j with rfl | ⟨j', rfl⟩
    · exact hdm
    · exact h0 j'
  exact sub_eq_zero.mp this

end Polynomial
