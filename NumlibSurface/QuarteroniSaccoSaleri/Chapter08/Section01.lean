/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Vandermonde
import Numlib.Approximation.Chebyshev
import Numlib.Approximation.Interpolation
import Numlib.Approximation.NewtonForm
import Numlib.Approximation.RungePhenomenon

/-!
# Quarteroni, Sacco and Saleri, Section 8.1: Polynomial interpolation

This module formalizes Section 8.1 of [quarteroni2000numerical], Lagrange interpolation. For $n + 1$
distinct nodes $x_0, \ldots, x_n$ and values $y_0, \ldots, y_n$ there is exactly one polynomial
$\Pi_n \in \mathbb{P}_n$ with $\Pi_n(x_i) = y_i$ (Theorem 8.1). It has the Lagrange form
$\Pi_n(x) = \sum_i y_i l_i(x)$ with the characteristic polynomials $l_i(x) = \prod_{j \neq i} (x -
x_j)/(x_i - x_j)$, and for $f \in C^{n+1}$ the error is
$$f(x) - \Pi_n f(x) = \frac{f^{(n+1)}(\xi)}{(n+1)!} \, \omega_{n+1}(x), \qquad \omega_{n+1}(x) =
  \prod_{i=0}^n (x - x_i)$$
(Theorem 8.2). For an interpolation matrix $X$ on $[a, b]$, the Lebesgue constant $\Lambda_n(X)$ of
(8.11) is the norm of the interpolation operator $\Pi_n$ on $C([a, b])$. It bounds the interpolation
error by the best approximation error (Property 8.1) and measures the stability of interpolation
(Section 8.1.3). The module also states Runge's counterexample (Example 8.1), a lower bound for the
Lebesgue constants of equispaced nodes, and Exercises 1–3 of Chapter 8, which the section cites.

The proofs use Mathlib's `Lagrange.interpolate`, `Lagrange.basis` and `Lagrange.nodal`, and the
backbone modules `Numlib.Approximation.Interpolation` (the error formula
`Lagrange.exists_sub_interpolate_eq_of_contDiffOn`, the interpolation operator
`Lagrange.interpolateCLM` and its norm `Lagrange.norm_interpolateCLM`),
`Numlib.Analysis.Normed.Module.BestApprox` (the Lebesgue lemma
`norm_sub_apply_le_of_isIdempotentElem`) and `Numlib.Approximation.RungePhenomenon` (Runge's
counterexample).

## Main definitions

* Section 8.1.2, `QuarteroniSaccoSaleri.Chapter08.IsInterpMatrix`: an interpolation matrix on
  $[a, b]$, a triangular array of points of $[a, b]$ with distinct points in each row.
* Section 8.1.2, `QuarteroniSaccoSaleri.Chapter08.interpRow`: the interpolation operator $\Pi_n$ at
  the nodes of row $n$.
* (8.11), `QuarteroniSaccoSaleri.Chapter08.lebesgueConstant`: the Lebesgue constant $\Lambda_n(X)$.
* Example 8.1, `QuarteroniSaccoSaleri.Chapter08.example_8_1_nodes`: the equispaced nodes on
  $[-5, 5]$.
* Section 8.1.3, `QuarteroniSaccoSaleri.Chapter08.equispacedMatrix`: the equispaced interpolation
  matrix on $[a, b]$.

## Main results

* Theorem 8.1, `QuarteroniSaccoSaleri.Chapter08.theorem_8_1`: the interpolating polynomial exists
  and is unique.
* Theorem 8.1, `QuarteroniSaccoSaleri.Chapter08.theorem_8_1_isUnisolvent`: point evaluation at
  distinct nodes is unisolvent over $\mathbb{P}_n$.
* (8.3), `QuarteroniSaccoSaleri.Chapter08.equation_8_3`: $l_i(x_j) = \delta_{ij}$.
* (8.4), `QuarteroniSaccoSaleri.Chapter08.equation_8_4`: the Lagrange form $\Pi_n = \sum_i y_i l_i$.
* Exercise 1 of Chapter 8, `QuarteroniSaccoSaleri.Chapter08.exercise_8_1`: the $l_i$ form a basis of
  $\mathbb{P}_n$.
* Exercise 2 of Chapter 8, `QuarteroniSaccoSaleri.Chapter08.exercise_8_2`: the Vandermonde matrix is
  nonsingular if and only if the nodes are distinct.
* Exercise 2 of Chapter 8, `QuarteroniSaccoSaleri.Chapter08.exercise_8_2_det`: the Vandermonde
  determinant is $\prod_{j < i} (x_i - x_j)$.
* (8.6), `QuarteroniSaccoSaleri.Chapter08.equation_8_6`: the nodal polynomial
  $\omega_{n+1}(t) = \prod_i (t - x_i)$.
* Exercise 3 of Chapter 8, `QuarteroniSaccoSaleri.Chapter08.exercise_8_3`: $\omega_{n+1}'(x_i) =
  \prod_{j \neq i} (x_i - x_j)$.
* (8.5), `QuarteroniSaccoSaleri.Chapter08.equation_8_5`: the form of $\Pi_n$ through $\omega_{n+1}$
  and $\omega_{n+1}'$.
* Theorem 8.2, `QuarteroniSaccoSaleri.Chapter08.theorem_8_2`: the interpolation error formula.
* (8.11), `QuarteroniSaccoSaleri.Chapter08.lebesgueConstant_eq_norm`: $\Lambda_n(X) = \|\Pi_n\|$.
* (8.11), `QuarteroniSaccoSaleri.Chapter08.sum_abs_basisCM_le_lebesgueConstant`: the Lebesgue
  function is at most $\Lambda_n(X)$.
* Property 8.1, `QuarteroniSaccoSaleri.Chapter08.property_8_1`: $\|f - \Pi_n f\|_\infty \le (1 +
  \Lambda_n(X)) E_n^*(f)$.
* Property 8.1, `QuarteroniSaccoSaleri.Chapter08.property_8_1_bestApprox`: the same bound with the
  polynomial of best approximation.
* Example 8.1, `QuarteroniSaccoSaleri.Chapter08.example_8_1_one_le`: the interpolation error of
  $1/(1 + x^2)$ at $x = 4.9$ is at least $1$ for every odd $n \ge 401$.
* Example 8.1, `QuarteroniSaccoSaleri.Chapter08.example_8_1`: Runge's counterexample, the equispaced
  interpolants of $1/(1 + x^2)$ on $[-5, 5]$ do not converge at some point.
* Section 8.1.3, `QuarteroniSaccoSaleri.Chapter08.interpRow_sub_le_lebesgueConstant`: the stability
  estimate $\|\Pi_n f - \Pi_n \tilde f\|_\infty \le \Lambda_n(X) \max_i |f(x_i) - \tilde f(x_i)|$.
* Section 8.1.3, `QuarteroniSaccoSaleri.Chapter08.coe_equispacedMatrix`: the nodes of row $n$ of the
  equispaced matrix are $a + j(b - a)/n$.
* Section 8.1.3, `QuarteroniSaccoSaleri.Chapter08.isInterpMatrix_equispacedMatrix`: the equispaced
  nodes form an interpolation matrix.
* Section 8.1.3, `QuarteroniSaccoSaleri.Chapter08.lebesgueConstant_equispaced_lower`: Schönhage's
  lower bound $\Lambda_n \ge 2^n/(8n^2)$ for equispaced nodes.

## Conventions

* The nodes are an injective family `x : Fin (n + 1) → ℝ`; injectivity is the book's "distinct". The
  interpolant of data $y$ is `Lagrange.interpolate Finset.univ x y`, a polynomial in `ℝ[X]`, and the
  interpolant of a function $f$ is `Lagrange.interpolate Finset.univ x (fun i => f (x i))`.
* The space $\mathbb{P}_n$ on $[a, b]$ is `polyLE (Icc a b) n`, a subspace of `C(Icc a b, ℝ)`. The
  interpolation operator on `C(Icc a b, ℝ)` is `Lagrange.interpolateCLM`, whose nodes are points of
  the subtype `Icc a b`.
* The smallest interval $I_x$ that contains the nodes and a point $t$ is
  `Icc (min t (⨅ i, x i)) (max t (⨆ i, x i))`. Theorem 8.2's hypothesis $f \in C^{n+1}(I_x)$ is read
  as `ContDiffOn` on an open set that contains $I_x$.

## Deviations from the source

* **Convention.** The Lagrange formulas use totalized denominators outside the distinct-node
  setting. See `QuarteroniSaccoSaleri.Chapter08.equation_8_4`,
  `QuarteroniSaccoSaleri.Chapter08.equation_8_5`.
* **Generalization.** The Vandermonde result gives an equivalence and a signed product determinant
  formula. See `QuarteroniSaccoSaleri.Chapter08.exercise_8_2`,
  `QuarteroniSaccoSaleri.Chapter08.exercise_8_2_det`.
* **Reading.** The interpolation remainder uses an open neighborhood of the minimal closed interval.
  See `QuarteroniSaccoSaleri.Chapter08.theorem_8_2`.
* **Representation.** The interpolation row is a continuous linear operator, with row injectivity
  required in the estimates. See `QuarteroniSaccoSaleri.Chapter08.interpRow`,
  `QuarteroniSaccoSaleri.Chapter08.lebesgueConstant`.
* **Representation.** The best approximation error is represented as distance to the polynomial
  subspace. See `QuarteroniSaccoSaleri.Chapter08.property_8_1`,
  `QuarteroniSaccoSaleri.Chapter08.property_8_1_bestApprox`.
* **Reading.** The Runge example proves failure of convergence using a uniform subsequence lower
  bound at a specific point. See `QuarteroniSaccoSaleri.Chapter08.example_8_1_nodes`,
  `QuarteroniSaccoSaleri.Chapter08.example_8_1_one_le`,
  `QuarteroniSaccoSaleri.Chapter08.example_8_1`.
* **Specialization.** The equispaced array extends unused entries and a one-sided exponential lower
  bound replaces the asymptotic equivalence. See `QuarteroniSaccoSaleri.Chapter08.equispacedMatrix`,
  `QuarteroniSaccoSaleri.Chapter08.coe_equispacedMatrix`,
  `QuarteroniSaccoSaleri.Chapter08.isInterpMatrix_equispacedMatrix`,
  `QuarteroniSaccoSaleri.Chapter08.lebesgueConstant_equispaced_lower`.

## Not formalized

* **Section 8.1.2, Erdős's lower bound.** For every interpolation matrix $X$ on $[a, b]$ there is
  $C > 0$ with $\Lambda_n(X) > \frac{2}{\pi} \log(n + 1) - C$ for all $n$; so no choice of nodes
  keeps the Lebesgue constants bounded, and the Chebyshev nodes, whose $\Lambda_n$ grows like
  $\frac{2}{\pi} \log n$, are optimal up to an additive constant. The book quotes it without proof
  from Erdős, *Problems and results on the theory of interpolation II* (Acta Math. Acad. Sci.
  Hungar. 12, 1961), whose proof is several pages of hard analysis on the Lebesgue function; the
  bounds on Lagrange interpolation operators in the library are upper bounds and give no lower
  bound.
* **Section 8.1.2, Faber's theorem.** For every interpolation matrix $X$ on $[a, b]$ with $a < b$
  there is $f \in C([a, b])$ whose interpolants $\Pi_n f$ do not converge uniformly to $f$. The book
  quotes it without proof. It follows from the unboundedness of $\Lambda_n(X)$ (Erdős's bound, or
  Bernstein's weaker $\Lambda_n \ge c \log n$) by
  `QuarteroniSaccoSaleri.Chapter08.lebesgueConstant_eq_norm` and the Banach–Steinhaus theorem
  `ContinuousLinearMap.exists_not_tendsto_of_not_bddAbove`, so it waits only for that lower bound.
  Runge's counterexample is one node scheme and one function, and is not a special case of it.
* **Section 8.1.3, the equispaced asymptotics.** For the equispaced matrix,
  $\Lambda_n(X) \simeq 2^{n+1}/(e n \log n)$, that is,
  $\Lambda_n(X) \cdot e n \log n / 2^{n+1} \to 1$. The book quotes it without proof from Turetskii
  (1940; see Natanson, *Constructive Function Theory*); the proof needs a precise evaluation of the
  Lebesgue function near the ends of the interval. The lower bound
  `QuarteroniSaccoSaleri.Chapter08.lebesgueConstant_equispaced_lower` is a one-sided version with a
  weaker constant.
-/

open Polynomial Set

namespace QuarteroniSaccoSaleri.Chapter08

variable {n : ℕ}

/-! ### Theorem 8.1 and the Lagrange form -/

/-- **Theorem 8.1** of [quarteroni2000numerical]. Given $n + 1$ distinct points $x_0, \ldots, x_n$
and $n + 1$ values $y_0, \ldots, y_n$, there exists a unique polynomial $\Pi_n$ of degree at
most $n$ such that $\Pi_n(x_i) = y_i$ for $i = 0, \ldots, n$.

Existence is Mathlib's `Lagrange.interpolate`, and uniqueness is
`Lagrange.eq_interpolate_of_eval_eq`. -/
theorem theorem_8_1 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (y : Fin (n + 1) → ℝ) :
    ∃! p : ℝ[X], p.degree ≤ n ∧ ∀ i, p.eval (x i) = y i := by
  have hcard : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
  refine ⟨Lagrange.interpolate Finset.univ x y, ⟨?_, fun i =>
    Lagrange.eval_interpolate_at_node y hx.injOn (Finset.mem_univ i)⟩, ?_⟩
  · have := Lagrange.degree_interpolate_le (s := Finset.univ) y hx.injOn
    rwa [hcard, Nat.add_sub_cancel] at this
  · rintro p ⟨hdeg, hval⟩
    refine Lagrange.eq_interpolate_of_eval_eq y hx.injOn ?_ fun i _ => hval i
    rw [hcard]
    exact hdeg.trans_lt (by exact_mod_cast Nat.lt_succ_self n)

/-- **Theorem 8.1** of [quarteroni2000numerical], abstract form. Let $x_0, \ldots, x_n$ be distinct
points of $[a, b]$. Then the point evaluations $f \mapsto f(x_i)$ on $C([a, b])$ are unisolvent
over $\mathbb{P}_n$: for all values $y_0, \ldots, y_n$ there is exactly one $p \in \mathbb{P}_n$
with $p(x_i) = y_i$ for all $i$.

Unisolvence is `Approximation.IsUnisolvent` of `Numlib.Approximation.Unisolvent`, and the proof
specializes `Lagrange.isUnisolvent_polyLE`. -/
theorem theorem_8_1_isUnisolvent {a b : ℝ} {x : Fin (n + 1) → Icc a b}
    (hx : Function.Injective x) :
    Approximation.IsUnisolvent (polyLE (Icc a b) n) fun i => ContinuousMap.evalCLM ℝ (x i) :=
  Lagrange.isUnisolvent_polyLE hx

/-- **Equation (8.3)** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be distinct. The
characteristic polynomials
$$l_i(x) = \prod_{j \neq i} \frac{x - x_j}{x_i - x_j}$$
satisfy $l_i(x_j) = \delta_{ij}$.

The polynomial $l_i$ is Mathlib's `Lagrange.basis Finset.univ x i`. -/
theorem equation_8_3 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (i j : Fin (n + 1)) :
    (Lagrange.basis Finset.univ x i).eval (x j) = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    exact Lagrange.eval_basis_self hx.injOn (Finset.mem_univ i)
  · exact Lagrange.eval_basis_of_ne h (Finset.mem_univ j)

/-- **Equation (8.4)** of [quarteroni2000numerical], the Lagrange form of the interpolating
polynomial: for nodes $x_0, \ldots, x_n$ and values $y_0, \ldots, y_n$,
$$\Pi_n(x) = \sum_{i=0}^n y_i l_i(x).$$

**Reading.** The polynomial identity is defined for arbitrary node lists using totalized basis
denominators. The nodal-quotient identity assumes the evaluation point differs from all nodes and
also uses totalized division for repeated nodes. The source starts with distinct nodes.
-/
theorem equation_8_4 (x y : Fin (n + 1) → ℝ) :
    Lagrange.interpolate Finset.univ x y = ∑ i, C (y i) * Lagrange.basis Finset.univ x i :=
  Lagrange.interpolate_apply _ _ _

/-- **Exercise 1 of Chapter 8** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be distinct.
Then the characteristic polynomials $l_0, \ldots, l_n$ of (8.3) form a basis of $\mathbb{P}_n$.

Here $\mathbb{P}_n$ is `Polynomial.degreeLT ℝ (n + 1)`. The $l_i$ are linearly independent,
because a vanishing combination is $0$ at each node, and there are $n + 1 = \dim \mathbb{P}_n$
of them. -/
theorem exercise_8_1 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    ∃ B : Module.Basis (Fin (n + 1)) ℝ (Polynomial.degreeLT ℝ (n + 1)),
      ∀ i, (B i : ℝ[X]) = Lagrange.basis Finset.univ x i := by
  have hcard : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
  have hmem : ∀ i, Lagrange.basis Finset.univ x i ∈ Polynomial.degreeLT ℝ (n + 1) := fun i => by
    rw [Polynomial.mem_degreeLT, Lagrange.degree_basis hx.injOn (Finset.mem_univ i), hcard,
      Nat.add_sub_cancel]
    exact_mod_cast Nat.lt_succ_self n
  set v : Fin (n + 1) → Polynomial.degreeLT ℝ (n + 1) := fun i =>
    ⟨Lagrange.basis Finset.univ x i, hmem i⟩ with hv
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have := congrArg (fun p : Polynomial.degreeLT ℝ (n + 1) => (p : ℝ[X]).eval (x j)) hc
    simp only [hv, Submodule.coe_sum, Submodule.coe_smul, Polynomial.eval_finsetSum,
      Polynomial.eval_smul, smul_eq_mul, equation_8_3 hx, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Submodule.coe_zero, Polynomial.eval_zero]
      at this
    exact this
  have hrank : Fintype.card (Fin (n + 1)) = Module.finrank ℝ (Polynomial.degreeLT ℝ (n + 1)) := by
    rw [Fintype.card_fin, LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv ℝ (n + 1)),
      Module.finrank_fin_fun]
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hrank, fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]⟩

/-- **Exercise 2 of Chapter 8** of [quarteroni2000numerical]. The Vandermonde matrix $[x_i^j]$ of
the nodes $x_0, \ldots, x_n$ is nonsingular if and only if the nodes are distinct.

The proof is Mathlib's `Matrix.det_vandermonde_ne_zero_iff`.

**Generalization.** Exercise 8.2 asks for the implication from distinct nodes to nonsingularity. The
theorem proves the converse as well, and gives the product determinant formula for the chosen
Vandermonde order. The transpose convention has the same determinant.
-/
theorem exercise_8_2 (x : Fin (n + 1) → ℝ) :
    (Matrix.vandermonde x).det ≠ 0 ↔ Function.Injective x :=
  Matrix.det_vandermonde_ne_zero_iff

/-- **Exercise 2 of Chapter 8** of [quarteroni2000numerical], the hint. The determinant of the
Vandermonde matrix of $x_0, \ldots, x_n$ is
$$\det [x_i^j] = \prod_{0 \le j < i \le n} (x_i - x_j).$$

The proof is Mathlib's `Matrix.det_vandermonde`.

**Generalization.** Exercise 8.2 asks for the implication from distinct nodes to nonsingularity. The
theorem proves the converse as well, and gives the product determinant formula for the chosen
Vandermonde order. The transpose convention has the same determinant.
-/
theorem exercise_8_2_det (x : Fin (n + 1) → ℝ) :
    (Matrix.vandermonde x).det = ∏ j, ∏ i ∈ Finset.Ioi j, (x i - x j) :=
  Matrix.det_vandermonde x

/-- **Equation (8.6)** of [quarteroni2000numerical]. The nodal polynomial of $x_0, \ldots, x_n$ has
the values
$$\omega_{n+1}(t) = \prod_{i=0}^n (t - x_i), \qquad t \in \mathbb{R}.$$

The nodal polynomial is Mathlib's `Lagrange.nodal Finset.univ x`. -/
theorem equation_8_6 (x : Fin (n + 1) → ℝ) (t : ℝ) :
    (Lagrange.nodal Finset.univ x).eval t = ∏ i, (t - x i) :=
  Lagrange.eval_nodal

/-- **Exercise 3 of Chapter 8** of [quarteroni2000numerical]. For nodes $x_0, \ldots, x_n$ and each
$i$, $\omega_{n+1}'(x_i) = \prod_{j \neq i} (x_i - x_j)$. -/
theorem exercise_8_3 (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (derivative (Lagrange.nodal Finset.univ x)).eval (x i)
      = ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
  rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i), Lagrange.eval_nodal]

/-- **Equation (8.5)** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be nodes and
$y_0, \ldots, y_n$ values. For every $t$ that is not a node,
$$\Pi_n(t) = \sum_{i=0}^n \frac{\omega_{n+1}(t)}{(t - x_i) \, \omega_{n+1}'(x_i)} \, y_i.$$

The statement assumes no distinctness of the nodes. The proof is Mathlib's first barycentric
form `Lagrange.eval_interpolate_not_at_node`.

**Reading.** The polynomial identity is defined for arbitrary node lists using totalized basis
denominators. The nodal-quotient identity assumes the evaluation point differs from all nodes and
also uses totalized division for repeated nodes. The source starts with distinct nodes.
-/
theorem equation_8_5 (x y : Fin (n + 1) → ℝ) {t : ℝ} (ht : ∀ i, t ≠ x i) :
    (Lagrange.interpolate Finset.univ x y).eval t
      = ∑ i, (Lagrange.nodal Finset.univ x).eval t
          / ((t - x i) * (derivative (Lagrange.nodal Finset.univ x)).eval (x i)) * y i := by
  rw [Lagrange.eval_interpolate_not_at_node y fun i _ => ht i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i)]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ### Theorem 8.2: the interpolation error -/

/-- **Theorem 8.2** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be distinct nodes and
$t \in \mathbb{R}$, and let $I_t$ be the smallest interval that contains the nodes and $t$. Let
$f$ be of class $C^{n+1}$ on an open set that contains $I_t$. Then there is $\xi \in I_t$ with
$$E_n(t) = f(t) - \Pi_n f(t) = \frac{f^{(n+1)}(\xi)}{(n+1)!} \, \omega_{n+1}(t).$$

When $I_t$ has nonempty interior, the proof specializes
`Lagrange.exists_sub_interpolate_eq_of_contDiffOn`. When $I_t$ is a single point, $t$ is the
node $x_0$ and both sides are $0$.

**Reading.** Smoothness is formulated on an open neighborhood of the closed hull of the nodes and
evaluation point. The result includes coincident evaluation with a node, where both sides vanish.
-/
theorem theorem_8_2 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (t : ℝ) {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hUsub : Icc (min t (⨅ i, x i)) (max t (⨆ i, x i)) ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Icc (min t (⨅ i, x i)) (max t (⨆ i, x i)),
      f t - (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t
        = iteratedDeriv (n + 1) f ξ / (n + 1).factorial * ∏ i, (t - x i) := by
  set a := min t (⨅ i, x i) with ha
  set b := max t (⨆ i, x i) with hb
  have hxmem : ∀ i, x i ∈ Icc a b := fun i =>
    ⟨(min_le_right _ _).trans (ciInf_le (Set.finite_range x).bddBelow i),
      (le_ciSup (Set.finite_range x).bddAbove i).trans (le_max_right _ _)⟩
  have htmem : t ∈ Icc a b := ⟨min_le_left _ _, le_max_left _ _⟩
  rcases lt_or_ge a b with hab | hab
  · obtain ⟨ξ, hξ, h⟩ :=
      Lagrange.exists_sub_interpolate_eq_of_contDiffOn hab hU hUsub hf hx hxmem htmem
    exact ⟨ξ, Ioo_subset_Icc_self hξ, h⟩
  · -- the degenerate case: `t` is the node `x 0`
    have ht0 : t = x 0 := by
      have h1 := hxmem 0
      have h2 := htmem
      rw [mem_Icc] at h1 h2
      linarith
    refine ⟨t, htmem, ?_⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ 0) (by rw [ht0, sub_self]), mul_zero, ht0,
      Lagrange.eval_interpolate_at_node _ hx.injOn (Finset.mem_univ 0), sub_self]

/-! ### The interpolation matrix, the Lebesgue constant and Property 8.1 -/

variable {a b : ℝ}

/-- **Section 8.1.2** of [quarteroni2000numerical], the interpolation matrix. An **interpolation
matrix** on $[a, b]$ is a lower triangular matrix $X$ of infinite size whose entries are points
of $[a, b]$ and whose rows have distinct entries: for each $n$, the points
$X_{n,0}, \ldots, X_{n,n}$ of row $n$ are distinct.

The matrix is a function `X : ℕ → ℕ → Icc a b`, and its entries $X_{n,j}$ with $j > n$ are not
used. Row $n$ is the book's $(n + 1)$-st row. -/
def IsInterpMatrix (X : ℕ → ℕ → Icc a b) : Prop :=
  ∀ n, Function.Injective fun j : Fin (n + 1) => X n j

/-- **Section 8.1.2** of [quarteroni2000numerical], the interpolation operator $\Pi_n$ on
$C([a, b])$ at the nodes $X_{n,0}, \ldots, X_{n,n}$ of row $n$ of $X$. It maps $f$ to the
restriction to $[a, b]$ of its interpolating polynomial at these nodes.

The operator is `Lagrange.interpolateCLM` at these nodes.

**Reading.** The row is a continuous linear operator on continuous functions and the Lebesgue
constant is the supremum of the absolute cardinal functions. Definitions are total for arbitrary
node arrays, with row injectivity imposed in estimates.
-/
noncomputable def interpRow (X : ℕ → ℕ → Icc a b) (n : ℕ) : C(Icc a b, ℝ) →L[ℝ] C(Icc a b, ℝ) :=
  Lagrange.interpolateCLM fun j : Fin (n + 1) => X n j

/-- **Equation (8.11)** of [quarteroni2000numerical], the Lebesgue constant. Let $l_j^{(n)}$ be the
characteristic polynomials of the nodes $X_{n,0}, \ldots, X_{n,n}$ of row $n$ of $X$. The
**Lebesgue constant** of $X$ is
$$\Lambda_n(X) = \Big\| \sum_{j=0}^n |l_j^{(n)}| \Big\|_\infty = \sup_{t \in [a, b]}
  \sum_{j=0}^n |l_j^{(n)}(t)|,$$
the maximum over $[a, b]$ of the Lebesgue function $\sum_j |l_j^{(n)}|$.

The maximum is written as the supremum `sSup` of the range of the Lebesgue function on $[a, b]$,
as in Section 10.8.

**Reading.** The row is a continuous linear operator on continuous functions and the Lebesgue
constant is the supremum of the absolute cardinal functions. Definitions are total for arbitrary
node arrays, with row injectivity imposed in estimates.
-/
noncomputable def lebesgueConstant (X : ℕ → ℕ → Icc a b) (n : ℕ) : ℝ :=
  sSup (Set.range fun t : Icc a b =>
    ∑ j, |Lagrange.basisCM (fun j : Fin (n + 1) => X n j) j t|)

/-- **Equation (8.11)** of [quarteroni2000numerical], the Lebesgue constant as a norm. If $X$ is an
interpolation matrix on $[a, b]$, then $\Lambda_n(X) = \|\Pi_n\|$, the operator norm of $\Pi_n$
on $C([a, b])$ with the maximum norm.

The proof specializes `Lagrange.norm_interpolateCLM`. -/
theorem lebesgueConstant_eq_norm {X : ℕ → ℕ → Icc a b} (hX : IsInterpMatrix X) (n : ℕ) :
    lebesgueConstant X n = ‖interpRow X n‖ :=
  have : Nonempty (Icc a b) := ⟨X 0 0⟩
  (Lagrange.norm_interpolateCLM (hX n)).symm

/-- **Equation (8.11)** of [quarteroni2000numerical], pointwise form. If $X$ is an interpolation
matrix on $[a, b]$, then $\sum_{j=0}^n |l_j^{(n)}(t)| \le \Lambda_n(X)$ for every
$t \in [a, b]$. -/
theorem sum_abs_basisCM_le_lebesgueConstant {X : ℕ → ℕ → Icc a b} (hX : IsInterpMatrix X)
    (n : ℕ) (t : Icc a b) :
    ∑ j, |Lagrange.basisCM (fun j : Fin (n + 1) => X n j) j t| ≤ lebesgueConstant X n :=
  have : Nonempty (Icc a b) := ⟨X 0 0⟩
  (lebesgueConstant_eq_norm hX n).symm ▸ (Lagrange.isGreatest_norm_interpolateCLM (hX n)).2 ⟨t, rfl⟩

/-- **Property 8.1** of [quarteroni2000numerical]. Let $X$ be an interpolation matrix on $[a, b]$,
let $f \in C^0([a, b])$ and $n \ge 0$. Then
$$E_{n,\infty}(X) \le (1 + \Lambda_n(X)) E_n^*,$$
where $E_{n,\infty}(X) = \|f - \Pi_n f\|_\infty$ is the interpolation error (8.9) and $E_n^* =
\inf_{q \in \mathbb{P}_n} \|f - q\|_\infty$ is the best approximation error.

The number $E_n^*$ is `Metric.infDist` from $f$ to $\mathbb{P}_n$. The proof is the Lebesgue
lemma `norm_sub_apply_le_of_isIdempotentElem` for the projection $\Pi_n$, whose range is
$\mathbb{P}_n$ and whose norm is $\Lambda_n(X)$.

**Reading.** The best approximation error is first expressed as a distance to the polynomial
subspace. The separate theorem replaces it with the norm error of a given best approximant.
-/
theorem property_8_1 {X : ℕ → ℕ → Icc a b} (hX : IsInterpMatrix X) (f : C(Icc a b, ℝ)) (n : ℕ) :
    ‖f - interpRow X n f‖
      ≤ (1 + lebesgueConstant X n) * Metric.infDist f (polyLE (Icc a b) n : Set C(Icc a b, ℝ)) := by
  have h := norm_sub_apply_le_of_isIdempotentElem (interpRow X n)
    (Lagrange.isIdempotentElem_interpolateCLM (hX n)) f
  rw [lebesgueConstant_eq_norm hX n]
  rwa [interpRow, Lagrange.range_interpolateCLM (hX n)] at h

/-- **Property 8.1** of [quarteroni2000numerical], with the polynomial of best approximation. Let
$X$ be an interpolation matrix on $[a, b]$ and $f \in C^0([a, b])$. If $p_n^* \in \mathbb{P}_n$
is a polynomial of best approximation of $f$ in the maximum norm, then
$$\|f - \Pi_n f\|_\infty \le (1 + \Lambda_n(X)) \|f - p_n^*\|_\infty.$$

For $a < b$ the polynomial of best approximation exists and is unique, by
`existsUnique_isBestApprox_polyLE`.

**Reading.** The best approximation error is first expressed as a distance to the polynomial
subspace. The separate theorem replaces it with the norm error of a given best approximant.
-/
theorem property_8_1_bestApprox {X : ℕ → ℕ → Icc a b} (hX : IsInterpMatrix X)
    {f p : C(Icc a b, ℝ)} (hp : IsBestApprox (polyLE (Icc a b) n : Set C(Icc a b, ℝ)) f p) :
    ‖f - interpRow X n f‖ ≤ (1 + lebesgueConstant X n) * ‖f - p‖ := by
  rw [hp.norm_sub_eq_infDist]
  exact property_8_1 hX f n

/-! ### Section 8.1.3: stability -/

/-- **Section 8.1.3** of [quarteroni2000numerical], the stability estimate. Let $X$ be an
interpolation matrix on $[a, b]$, and let $f, \tilde f \in C([a, b])$, where $\tilde f$ is a
perturbation of the data $f$. Then
$$\|\Pi_n f - \Pi_n \tilde f\|_\infty \le \Lambda_n(X) \max_{i = 0, \ldots, n} |f(x_i) - \tilde
  f(x_i)|,$$
with the nodes $x_i = X_{n,i}$ of row $n$.

So small changes of the data give small changes of the interpolating polynomial only if the
Lebesgue constant is small; the book says that $\Lambda_n(X)$ "plays the role of the condition
number for the interpolation problem". The maximum over the nodes is a supremum over
`Fin (n + 1)`. -/
theorem interpRow_sub_le_lebesgueConstant {X : ℕ → ℕ → Icc a b} (hX : IsInterpMatrix X) (n : ℕ)
    (f g : C(Icc a b, ℝ)) :
    ‖interpRow X n f - interpRow X n g‖
      ≤ lebesgueConstant X n * ⨆ i : Fin (n + 1), |f (X n i) - g (X n i)| := by
  set M : ℝ := ⨆ i : Fin (n + 1), |f (X n i) - g (X n i)| with hM
  have hM0 : 0 ≤ M := Real.iSup_nonneg fun i => abs_nonneg _
  have hMi : ∀ i : Fin (n + 1), |f (X n i) - g (X n i)| ≤ M := fun i =>
    le_ciSup (f := fun i : Fin (n + 1) => |f (X n i) - g (X n i)|) (Set.finite_range _).bddAbove i
  have hΛ0 : 0 ≤ lebesgueConstant X n :=
    Real.sSup_nonneg fun y ⟨t, ht⟩ => ht ▸ Finset.sum_nonneg fun j _ => abs_nonneg _
  rw [← map_sub, ContinuousMap.norm_le _ (mul_nonneg hΛ0 hM0)]
  intro t
  rw [interpRow, Lagrange.interpolateCLM_apply, Real.norm_eq_abs]
  calc |∑ i, (f - g) ((fun j : Fin (n + 1) => X n j) i)
          * Lagrange.basisCM (fun j : Fin (n + 1) => X n j) i t|
      ≤ ∑ i, |(f - g) ((fun j : Fin (n + 1) => X n j) i)|
          * |Lagrange.basisCM (fun j : Fin (n + 1) => X n j) i t| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => abs_mul _ _
    _ ≤ ∑ i, M * |Lagrange.basisCM (fun j : Fin (n + 1) => X n j) i t| := by
        gcongr with i
        exact hMi i
    _ = M * ∑ i, |Lagrange.basisCM (fun j : Fin (n + 1) => X n j) i t| := by
        rw [Finset.mul_sum]
    _ ≤ M * lebesgueConstant X n := by
        gcongr
        exact sum_abs_basisCM_le_lebesgueConstant hX n t
    _ = lebesgueConstant X n * M := mul_comm _ _

/-! ### Example 8.1: Runge's counterexample -/

/-- **Example 8.1** of [quarteroni2000numerical], the equally spaced nodes $x_j^{(n)} = -5 + 10j/n$,
$j = 0, \ldots, n$, on $[-5, 5]$.

For $n = 0$ the single node is $-5$, by the Lean convention $a / 0 = 0$.

**Reading.** The single degree-zero node is the left endpoint. A bound at $49/10$ for every odd
degree at least 400 proves nonconvergence at a specific point. The source's displayed nonzero limit
need not exist for the nonconvergence conclusion.
-/
noncomputable def example_8_1_nodes (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  -5 + 10 * (j : ℝ) / n

/-- **Example 8.1** of [quarteroni2000numerical], quantitative form. Let $f(x) = 1/(1 + x^2)$ be the
function of (8.12), and let $\Pi_n f$ interpolate $f$ at the equally spaced nodes
$x_j^{(n)} = -5 + 10j/n$ on $[-5, 5]$. For every odd $n \ge 400$, that is, every odd
$n \ge 401$,
$$|f(4.9) - \Pi_n f(4.9)| \ge 1.$$

The proof specializes `Runge.one_le_abs_sub_interpolate`.

**Reading.** The single degree-zero node is the left endpoint. A bound at $49/10$ for every odd
degree at least 400 proves nonconvergence at a specific point. The source's displayed nonzero limit
need not exist for the nonconvergence conclusion.
-/
theorem example_8_1_one_le {n : ℕ} (hn : Odd n) (hn400 : 400 ≤ n) :
    1 ≤ |1 / (1 + (49 / 10 : ℝ) ^ 2)
      - (Lagrange.interpolate Finset.univ (example_8_1_nodes n)
          fun j => 1 / (1 + (example_8_1_nodes n j) ^ 2)).eval (49 / 10)| :=
  Runge.one_le_abs_sub_interpolate hn hn400

/-- **Example 8.1** of [quarteroni2000numerical] (Runge's counterexample). Let $f(x) = 1/(1 + x^2)$
on $[-5, 5]$ (8.12), and let $\Pi_n f$ interpolate $f$ at the equally spaced nodes
$x_j^{(n)} = -5 + 10j/n$. Then there is $x \in [-5, 5]$ at which $\Pi_n f(x)$ does not converge
to $f(x)$ as $n \to \infty$. In the words of the book, "some points $x$ exist within the
interpolation interval such that $\lim_{n \to \infty} |f(x) - \Pi_n f(x)| \neq 0$".

The point is $x = 4.9$: along the odd $n$ the error stays at least $1$, by
`QuarteroniSaccoSaleri.Chapter08.example_8_1_one_le`. The book's threshold $|x| > 3.63\ldots$ is
not part of the statement. The proof specializes `Runge.not_tendsto_interpolate`: the error is
$\omega_{n+1}(x) f[x_0, \ldots, x_n, x]$, the divided difference is computed exactly through the
partial fraction $1/(1 + s^2) = \operatorname{Re}(i/(i - s))$, and the products are estimated by
Riemann sums of logarithms.

**Reading.** The single degree-zero node is the left endpoint. A bound at $49/10$ for every odd
degree at least 400 proves nonconvergence at a specific point. The source's displayed nonzero limit
need not exist for the nonconvergence conclusion.
-/
theorem example_8_1 :
    ∃ t ∈ Icc (-5 : ℝ) 5, ¬ Filter.Tendsto
      (fun n => (Lagrange.interpolate Finset.univ (example_8_1_nodes n)
        fun j => 1 / (1 + (example_8_1_nodes n j) ^ 2)).eval t)
      Filter.atTop (nhds (1 / (1 + t ^ 2))) :=
  ⟨49 / 10, by norm_num, Runge.not_tendsto_interpolate⟩

/-! ### Section 8.1.3: a lower bound for the equispaced Lebesgue constants -/

section Equispaced

/-- **Section 8.1.3** of [quarteroni2000numerical], the equispaced interpolation matrix on $[a, b]$,
for $a < b$. Row $n$ consists of the equally spaced nodes
$$x_j^{(n)} = a + \frac{j (b - a)}{n}, \qquad j = 0, \ldots, n,$$
of Runge's example and of the asymptotics $\Lambda_n \simeq 2^{n+1}/(e n \log n)$.

The entries with $j > n$ are not used; `Set.projIcc` moves them into $[a, b]$.

**Reading.** The matrix is extended by projecting unused entries into the interval, and its
degree-zero row uses the left endpoint. The lower bound proves exponential growth but does not give
the printed asymptotic equivalence.
-/
noncomputable def equispacedMatrix (hab : a < b) (n j : ℕ) : Icc a b :=
  projIcc a b hab.le (a + j * (b - a) / n)

/-- The nodes of row $n$ of `QuarteroniSaccoSaleri.Chapter08.equispacedMatrix` are the equally
spaced points: for $j \le n$, the entry $x_j^{(n)}$ is $a + j(b - a)/n$.

**Reading.** The matrix is extended by projecting unused entries into the interval, and its
degree-zero row uses the left endpoint. The lower bound proves exponential growth but does not give
the printed asymptotic equivalence.
-/
theorem coe_equispacedMatrix (hab : a < b) {n j : ℕ} (hj : j ≤ n) :
    ((equispacedMatrix hab n j : Icc a b) : ℝ) = a + j * (b - a) / n := by
  have hmem : a + (j : ℝ) * (b - a) / n ∈ Icc a b := by
    rw [Set.mem_Icc]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0
      norm_num
      exact hab.le
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
      have hba : (0 : ℝ) < b - a := by linarith
      have h1 : (0 : ℝ) ≤ (j : ℝ) * (b - a) / n := by positivity
      have h2 : (j : ℝ) * (b - a) / n ≤ b - a := by
        rw [div_le_iff₀ hn0]
        nlinarith
      exact ⟨by linarith, by linarith⟩
  rw [equispacedMatrix, Set.projIcc_of_mem hab.le hmem]

/-- For $a < b$, the equispaced nodes form an interpolation matrix: the nodes of each row are
distinct.

**Reading.** The matrix is extended by projecting unused entries into the interval, and its
degree-zero row uses the left endpoint. The lower bound proves exponential growth but does not give
the printed asymptotic equivalence.
-/
theorem isInterpMatrix_equispacedMatrix (hab : a < b) :
    IsInterpMatrix (equispacedMatrix hab) := by
  intro n j k hjk
  have hjk' : equispacedMatrix hab n (j : ℕ) = equispacedMatrix hab n (k : ℕ) := hjk
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hj0 : (j : ℕ) = 0 := by have := j.isLt; omega
    have hk0 : (k : ℕ) = 0 := by have := k.isLt; omega
    exact Fin.ext (by rw [hj0, hk0])
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hba : (0 : ℝ) < b - a := by linarith
    have hcoe : ((equispacedMatrix hab n (j : ℕ) : Icc a b) : ℝ)
        = ((equispacedMatrix hab n (k : ℕ) : Icc a b) : ℝ) := by rw [hjk']
    rw [coe_equispacedMatrix hab (Nat.lt_succ_iff.mp j.isLt),
      coe_equispacedMatrix hab (Nat.lt_succ_iff.mp k.isLt)] at hcoe
    have key : ((j : ℕ) : ℝ) * ((b - a) / n) = ((k : ℕ) : ℝ) * ((b - a) / n) := by
      have e1 : ((j : ℕ) : ℝ) * (b - a) / n = ((j : ℕ) : ℝ) * ((b - a) / n) := by ring
      have e2 : ((k : ℕ) : ℝ) * (b - a) / n = ((k : ℕ) : ℝ) * ((b - a) / n) := by ring
      rw [← e1, ← e2]
      linarith
    have hne : (b - a) / (n : ℝ) ≠ 0 := ne_of_gt (by positivity)
    exact Fin.ext (by exact_mod_cast mul_right_cancel₀ hne key)

/-- **Section 8.1.3** of [quarteroni2000numerical], a lower bound for the equispaced Lebesgue
constants (Schönhage). Let $a < b$, let $X$ be the equispaced interpolation matrix on $[a, b]$,
and let $n \ge 1$. Then
$$\Lambda_n(X) \ge \frac{2^n}{8 n^2} = \frac{2^{n-3}}{n^2}.$$
So the equispaced Lebesgue constants grow exponentially, and equispaced interpolation is
unstable.

The book states neither this bound nor the exponent $2^{n-3}$; it quotes the asymptotics
$\Lambda_n \simeq 2^{n+1}/(e n \log n)$ from Turetskii without proof, and this bound is a
one-sided version of them. The bound concerns one interpolation matrix, so it says nothing about
the theorems of Erdős and Faber, which concern all of them.

The proof evaluates the Lebesgue function at the midpoint $t = a + (b - a)/(2n)$ of the first
panel. There the node spacing cancels from every characteristic polynomial,
$l_i(t) = \prod_{j \neq i} (1/2 - j)/(i - j)$. The denominators give $i! \, (n - i)!$ and the
common numerator gives $(2n)!/(2^{2n+1} n!)$, with the largest omitted factor $(2n - 1)/2$. With
$\sum_i 1/(i! \, (n - i)!) = 2^n/n!$ this gives $\binom{2n}{n} 2^n / (4^n (2n - 1))$, which is
at least $2^n/(8n^2)$. The proof specializes
`Lagrange.two_pow_div_le_sum_abs_eval_basis_equispaced`.

**Reading.** The matrix is extended by projecting unused entries into the interval, and its
degree-zero row uses the left endpoint. The lower bound proves exponential growth but does not give
the printed asymptotic equivalence.
-/
theorem lebesgueConstant_equispaced_lower (hab : a < b) {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ n / (8 * (n : ℝ) ^ 2) ≤ lebesgueConstant (equispacedMatrix hab) n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hba : (0 : ℝ) < b - a := by linarith
  have hX := isInterpMatrix_equispacedMatrix hab
  have hmem : a + (b - a) / (2 * n) ∈ Icc a b := by
    rw [Set.mem_Icc]
    have h1 : (0 : ℝ) < (b - a) / (2 * n) := by positivity
    have h2 : (b - a) / (2 * n) ≤ b - a := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact ⟨by linarith, by linarith⟩
  have hnodes : (fun j : Fin (n + 1) => ((equispacedMatrix hab n (j : ℕ) : Icc a b) : ℝ))
      = fun j : Fin (n + 1) => a + ((j : ℕ) : ℝ) * (b - a) / n :=
    funext fun j => coe_equispacedMatrix hab (Nat.lt_succ_iff.mp j.isLt)
  refine le_trans ?_ (sum_abs_basisCM_le_lebesgueConstant hX n ⟨a + (b - a) / (2 * n), hmem⟩)
  refine (Lagrange.two_pow_div_le_sum_abs_eval_basis_equispaced hab hn).trans_eq ?_
  simp only [Lagrange.basisCM_apply, hnodes]

end Equispaced

end QuarteroniSaccoSaleri.Chapter08
