import Numlib.Approximation.Hermite.Global

/-!
# Cartis–Gould–Toint, Appendix A.9: uniform Hermite interpolation

Theorem A.9.1 includes both uniform conclusions. Its endpoint discrepancies are
measured from the actual derivatives of the initial factorial-normalized Taylor
polynomial. The constants depend only on the order and the common data bound;
they are quantified before the interval length and every endpoint jet.
Theorem A.9.2 gives the global interpolant, including uniform bounds on all lower
derivatives under the additional data bounds. The step index in the source is
corrected to `k < k_e`; the final scalar domain is `ℝ`.
-/

open Polynomial Set
open scoped BigOperators

namespace CartisGouldToint

/-- The unique degree-at-most-`2p+1` polynomial with the specified jets through
order `p` at zero and a positive endpoint, equations (A.23)–(A.26). -/
noncomputable abbrev hermiteEndpointPolynomial (p : ℕ) (s : ℝ) (a b : ℕ → ℝ) : ℝ[X] :=
  Hermite.endpointPolynomial p s a b

/-- The interpolant has the required degree and every prescribed endpoint derivative. -/
theorem hermiteEndpointPolynomial_spec (p : ℕ) {s : ℝ} (hs : 0 < s) (a b : ℕ → ℝ) :
    (hermiteEndpointPolynomial p s a b).natDegree ≤ 2 * p + 1 ∧
      ∀ j ≤ p,
        iteratedDeriv j (fun t => (hermiteEndpointPolynomial p s a b).eval t) 0 = a j ∧
        iteratedDeriv j (fun t => (hermiteEndpointPolynomial p s a b).eval t) s = b j := by
  refine ⟨Hermite.endpointPolynomial_natDegree_le p s a b, ?_⟩
  intro j hj
  simp only [Polynomial.iteratedDeriv_eval]
  exact ⟨Hermite.endpointPolynomial_zero hs.ne' a b hj,
    Hermite.endpointPolynomial_right hs.ne' a b hj⟩

/-- **Theorem A.9.1.** Uniform Hermite interpolation on an interval. The first
conclusion is a Lipschitz bound on the `p`-th derivative under (A.30). Under the
additional bounds (A.31), all derivatives through order `p` have a uniform bound.
Both constants are chosen before the interval and all interpolation data. -/
theorem theorem_A_9_1 (p : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L ≥ 0, ∃ B ≥ 0, ∀ s : ℝ, 0 < s → ∀ a b : ℕ → ℝ,
      (∀ j ≤ p, |b j - iteratedDeriv j
        (fun t => ∑ i ∈ Finset.range (p + 1), a i * t ^ i / i.factorial) s| ≤
          κ * s ^ (p - j + 1)) →
      (∀ u ∈ Icc 0 s, ∀ v ∈ Icc 0 s,
        |iteratedDeriv p (fun t => (hermiteEndpointPolynomial p s a b).eval t) u -
          iteratedDeriv p (fun t => (hermiteEndpointPolynomial p s a b).eval t) v| ≤ L * |u - v|) ∧
      ((∀ j ≤ p, |a j| ≤ κ) → s ≤ κ → ∀ j ≤ p, ∀ t ∈ Icc 0 s,
        |iteratedDeriv j (fun z => (hermiteEndpointPolynomial p s a b).eval z) t| ≤ B) := by
  obtain ⟨L,hL,B,hB,h⟩ := Hermite.endpointPolynomial_uniform_bounds p κ hκ
  refine ⟨L,hL.le,B,hB.le,?_⟩
  intro s hs a b hres
  apply h s hs a b
  intro j hj
  have heq : (fun t => (Hermite.initialPolynomial p a).eval t) =
      (fun t => ∑ i ∈ Finset.range (p + 1), a i * t ^ i / i.factorial) := by
    funext t
    exact Hermite.initialPolynomial_eval p a t
  have hpoly := congrFun (Polynomial.iteratedDeriv_eval (Hermite.initialPolynomial p a) j) s
  rw [heq] at hpoly
  rw [← hpoly]
  exact hres j hj

/-- **Theorem A.9.2.** A finite increasing sequence of real jets satisfying the
Taylor residual inequalities (A.32) admits a global `C^p` Hermite interpolant.
Its highest derivative has a uniform Lipschitz constant. If the initial jets
and steps on every interpolation interval are bounded by `κ`, every derivative
through order `p` is globally bounded by a uniform constant as well. Both
constants are chosen before the number, positions, and values of the data.

The source's step index is corrected to `k < n`, and its final domain to `ℝ`. -/
theorem theorem_A_9_2 (p : ℕ) (_hp : 0 < p) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ L ≥ 0, ∃ B ≥ 0, ∀ n : ℕ, 0 < n → ∀ x : ℕ → ℝ, ∀ a : ℕ → ℕ → ℝ,
      (∀ i j, i < j → j ≤ n → x i < x j) →
      (∀ k < n, ∀ j ≤ p, |a (k + 1) j - iteratedDeriv j
        (fun t => ∑ i ∈ Finset.range (p + 1), a k i * t ^ i / i.factorial)
        (x (k + 1) - x k)| ≤ κ * (x (k + 1) - x k) ^ (p - j + 1)) →
      ∃ f : ℝ → ℝ, ContDiff ℝ p f ∧
        (∀ u v, |iteratedDeriv p f u - iteratedDeriv p f v| ≤ L * |u - v|) ∧
        (∀ k ≤ n, ∀ j ≤ p, iteratedDeriv j f (x k) = a k j) ∧
        (((∀ k < n, ∀ j ≤ p, |a k j| ≤ κ) ∧ (∀ k < n, x (k + 1) - x k ≤ κ)) →
          ∀ j ≤ p, ∀ t, |iteratedDeriv j f t| ≤ B) := by
  obtain ⟨L,hL,B,hB,h⟩ := Hermite.exists_uniform_interpolant p κ hκ
  refine ⟨L,hL.le,B,hB.le,?_⟩
  intro n hn x a hx hres
  have hres' : ∀ k < n, ∀ j ≤ p,
      |a (k + 1) j - (derivative^[j] (Hermite.initialPolynomial p (a k))).eval
        (x (k + 1) - x k)| ≤ κ * (x (k + 1) - x k) ^ (p - j + 1) := by
    intro k hk j hj
    have heq : (fun t => (Hermite.initialPolynomial p (a k)).eval t) =
        (fun t => ∑ i ∈ Finset.range (p + 1), a k i * t ^ i / i.factorial) := by
      funext t
      exact Hermite.initialPolynomial_eval p (a k) t
    have hpoly := congrFun (Polynomial.iteratedDeriv_eval (Hermite.initialPolynomial p (a k)) j)
      (x (k + 1) - x k)
    rw [heq] at hpoly
    rw [← hpoly]
    exact hres k hk j hj
  obtain ⟨f,hf,hLf,hfj,hfb⟩ := h n hn x a hx hres'
  refine ⟨f,hf,?_,hfj,hfb⟩
  intro u v
  have hh := hLf.norm_sub_le u v
  change ‖iteratedDeriv p f u - iteratedDeriv p f v‖ ≤ L * ‖u - v‖ at hh
  simpa only [Real.norm_eq_abs] using hh

end CartisGouldToint
