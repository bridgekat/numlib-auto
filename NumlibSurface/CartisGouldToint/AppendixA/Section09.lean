import Numlib.Approximation.Hermite.Endpoint

/-!
# Cartis–Gould–Toint, Appendix A.9: uniform Hermite interpolation

Theorem A.9.1 includes both uniform conclusions. Its endpoint discrepancies are
measured from the actual derivatives of the initial factorial-normalized Taylor
polynomial. The constants depend only on the order and the common data bound;
they are quantified before the interval length and every endpoint jet.
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

end CartisGouldToint
