/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.Quadrature

/-!
# Stieltjes' moment problem

Section 3.1 of [liesen2013krylov] describes the reconstruction of a distribution from its power
moments. The compact version replaces a distribution by one supported on $n$ ordered nodes,
requiring exact agreement on the monomials of orders $0$ through $2n-1$.

## Main definitions

* `LiesenStrakos.Chapter03.IsStieltjesMomentSolution` specifies a distribution on $[0,\infty)$
  with a prescribed sequence of moments.
* `LiesenStrakos.Chapter03.SolvesStieltjesProblem` specifies the normalized atomic distribution
  solving the compact problem.
* `LiesenStrakos.Chapter03.mechanicalQuadrature` evaluates a function on a finite weighted rule.

## Main results

* `LiesenStrakos.Chapter03.solvesStieltjesProblem_iff` gives the equivalence between matching
  the first $2n$ moments and polynomial exactness through degree $2n-1$.

## Conventions

The measure $\mu$ represents the mass element $d\omega$. A probability measure concentrated on
$(a,b]$ represents the normalized distribution with zero mass at the left endpoint.
-/

open MeasureTheory Polynomial
open scoped Polynomial

namespace LiesenStrakos.Chapter03

/-- The $k$th moment of the distribution $\mu$ is $\int x^k\,d\mu(x)$. -/
noncomputable def stieltjesMoment (μ : Measure ℝ) (k : ℕ) : ℝ :=
  ∫ x, x ^ k ∂μ

/-- A finite distribution $\mu$ on $[0,\infty)$ solves the Stieltjes moment problem for a sequence
$(\xi_k)$ if its monomials are integrable and $\int x^k\,d\mu(x)=\xi_k$ for every $k$. This is
equation (3.1.1) of [liesen2013krylov]. -/
def IsStieltjesMomentSolution (μ : Measure ℝ) (ξ : ℕ → ℝ) : Prop :=
  μ (Set.Ici 0)ᶜ = 0 ∧
    ∀ k : ℕ, Integrable (fun x => x ^ k) μ ∧ stieltjesMoment μ k = ξ k

/-- The distribution function of an atomic rule is the sum of the weights $w_i$ of all nodes
$x_i$ at or below the evaluation point. This is (3.1.4) of [liesen2013krylov]. -/
noncomputable def atomicDistribution {n : ℕ} (x w : Fin n → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ i, if x i ≤ t then w i else 0

/-- The mechanical quadrature with nodes $x_i$ and weights $w_i$ takes $f$ to
$\sum_i w_i f(x_i)$. This is (3.1.8) of [liesen2013krylov]. -/
noncomputable def mechanicalQuadrature {n : ℕ} (x w : Fin n → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, w i * f (x i)

/-- The error of a mechanical quadrature is the difference between the integral and the
quadrature sum. This is the error in (3.1.7) of [liesen2013krylov]. -/
noncomputable def quadratureError (μ : Measure ℝ) {n : ℕ}
    (x w : Fin n → ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ t, f t ∂μ) - mechanicalQuadrature x w f

/-- A mechanical quadrature has algebraic degree of exactness $d$ if it integrates every
polynomial of degree at most $d$, and fails on some polynomial of degree $d+1$. -/
def HasQuadratureDegree (μ : Measure ℝ) {n : ℕ} (x w : Fin n → ℝ) (d : ℕ) : Prop :=
  Quadrature.IsExactOnMeasure μ w x d ∧ ¬ Quadrature.IsExactOnMeasure μ w x (d + 1)

/-- A normalized atomic rule solves Problem 3.1.1 of [liesen2013krylov] for a reference
distribution on $(a,b]$ if its $n$ nodes in $(a,b]$ are strictly increasing, its weights are
positive and sum to one, and it integrates the first $2n$ monomials exactly. -/
def SolvesStieltjesProblem (μ : Measure ℝ) (a b : ℝ) {n : ℕ}
    (x w : Fin n → ℝ) : Prop :=
  0 < n ∧ StrictMono x ∧ (∀ i, x i ∈ Set.Ioc a b) ∧
    (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
    ∀ k : ℕ, k < 2 * n → mechanicalQuadrature x w (fun t => t ^ k) = stieltjesMoment μ k

/-- A rule for a measure with finite moments is exact through degree $d$ if and only if the rule
matches each moment of order at most $d$. -/
theorem isExactOnMeasure_iff_moments {μ : Measure ℝ}
    (hint : ∀ k : ℕ, Integrable (fun t : ℝ => t ^ k) μ) {n d : ℕ} {x w : Fin n → ℝ} :
    Quadrature.IsExactOnMeasure μ w x d ↔
      ∀ k ≤ d, mechanicalQuadrature x w (fun t => t ^ k) = stieltjesMoment μ k := by
  constructor
  · intro h k hk
    simpa only [mechanicalQuadrature, stieltjesMoment, eval_pow, eval_X] using
      h ((X : ℝ[X]) ^ k) (by rw [degree_X_pow]; exact_mod_cast hk)
  · intro h p hp
    have hlt : p.natDegree < d + 1 :=
      lt_of_le_of_lt (natDegree_le_iff_degree_le.2 hp) d.lt_succ_self
    simp_rw [eval_eq_sum_range' hlt, Finset.mul_sum]
    rw [Finset.sum_comm, integral_finsetSum _ fun k _ => (hint k).const_mul _]
    refine Finset.sum_congr rfl fun k hk => ?_
    calc ∑ i, w i * (p.coeff k * x i ^ k)
        = p.coeff k * mechanicalQuadrature x w (fun t => t ^ k) := by
          rw [mechanicalQuadrature, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ = ∫ t, p.coeff k * t ^ k ∂μ := by
          rw [h k (Nat.le_of_lt_succ (Finset.mem_range.1 hk)), integral_const_mul, stieltjesMoment]

/-- For ordered nodes in $(a,b]$ with positive normalized weights, solving Problem 3.1.1 of
[liesen2013krylov] is equivalent to exactness through degree $2n-1$. -/
theorem solvesStieltjesProblem_iff {μ : Measure ℝ}
    (hint : ∀ k : ℕ, Integrable (fun t : ℝ => t ^ k) μ) {a b : ℝ} {n : ℕ}
    (hn : 0 < n) {x w : Fin n → ℝ} (hx : StrictMono x) (hmem : ∀ i, x i ∈ Set.Ioc a b)
    (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = 1) :
    SolvesStieltjesProblem μ a b x w ↔ Quadrature.IsExactOnMeasure μ w x (2 * n - 1) := by
  rw [isExactOnMeasure_iff_moments hint]
  unfold SolvesStieltjesProblem
  refine ⟨fun h k hk => h.2.2.2.2.2 k (by omega), fun h => ?_⟩
  exact ⟨hn, hx, hmem, hw, hsum, fun k hk => h k (by omega)⟩

end LiesenStrakos.Chapter03
