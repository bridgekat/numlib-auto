/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.NewtonForm
import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 8.2: The Newton form of the interpolating polynomial

This module formalizes Section 8.2 of [quarteroni2000numerical]. For distinct nodes
$x_0, \ldots, x_n$, the interpolating polynomial of $f$ is built degree by degree, $\Pi_n f =
\Pi_{n-1} f + \omega_n f[x_0, \ldots, x_n]$, where $\omega_n(x) = \prod_{i < n} (x - x_i)$ and the
Newton divided difference $f[x_0, \ldots, x_n]$ is the coefficient of the new term (8.14)–(8.16).
This gives the Newton divided difference formula (8.17), $\Pi_n f = \sum_{k=0}^n \omega_k f[x_0,
\ldots, x_k]$. The divided difference has the explicit representation
$$f[x_0, \ldots, x_n] = \sum_{i=0}^n \frac{f(x_i)}{\omega_{n+1}'(x_i)} \tag{8.18}$$
and the consequences of Section 8.2.1: symmetry in the nodes, linearity in $f$, the Leibniz formula,
the recursion (8.19), and $f[x_0, \ldots, x_n] = 0$ for $f \in \mathbb{P}_{n-1}$. Section 8.2.2
writes the interpolation error as $\omega_{n+1}(x) f[x_0, \ldots, x_n, x]$ (8.20) and gives the mean
value form $f[x_0, \ldots, x_n, x] = f^{(n+1)}(\xi)/(n+1)!$ (8.21).

The divided difference $f[x_0, \ldots, x_n]$ is `DividedDifference.newton f x` of
`Numlib.Approximation.DividedDifference`, defined by the explicit formula (8.18). The book defines
it by (8.14), so `QuarteroniSaccoSaleri.Chapter08.equation_8_14` is the equivalence of the two
definitions. The other proofs specialize `Numlib.Approximation.NewtonForm`.

## Main results

* (8.14)–(8.15), `QuarteroniSaccoSaleri.Chapter08.equation_8_14`: $f[x_0, \ldots, x_n] = (f(x_n) -
  \Pi_{n-1} f(x_n))/\omega_n(x_n)$.
* (8.16), `QuarteroniSaccoSaleri.Chapter08.equation_8_16`: $\Pi_n f = \Pi_{n-1} f + \omega_n f[x_0,
  \ldots, x_n]$.
* (8.17), `QuarteroniSaccoSaleri.Chapter08.equation_8_17`: the Newton divided difference formula.
* (8.18), `QuarteroniSaccoSaleri.Chapter08.equation_8_18`: the explicit representation of the
  divided difference.
* Section 8.2.1, property 1, `QuarteroniSaccoSaleri.Chapter08.dividedDifference_perm`: the divided
  difference is invariant under permutations of the nodes.
* Section 8.2.1, property 2, `QuarteroniSaccoSaleri.Chapter08.dividedDifference_linear`: the divided
  difference is linear in $f$.
* Section 8.2.1, property 3, `QuarteroniSaccoSaleri.Chapter08.dividedDifference_leibniz`: the
  Leibniz formula for $f = gh$.
* (8.19), `QuarteroniSaccoSaleri.Chapter08.equation_8_19`: the recursion $f[x_0, \ldots, x_n] =
  (f[x_1, \ldots, x_n] - f[x_0, \ldots, x_{n-1}])/(x_n - x_0)$.
* Section 8.2.1, `QuarteroniSaccoSaleri.Chapter08.dividedDifference_eq_zero_of_mem_polyLT`:
  $f[x_0, \ldots, x_n] = 0$ for $f \in \mathbb{P}_{n-1}$.
* (8.20), `QuarteroniSaccoSaleri.Chapter08.equation_8_20`: the interpolation error is
  $\omega_{n+1}(x) f[x_0, \ldots, x_n, x]$.
* (8.21), `QuarteroniSaccoSaleri.Chapter08.equation_8_21`:
  $f[x_0, \ldots, x_n, x] = f^{(n+1)}(\xi)/(n+1)!$.

## Conventions

* As in Section 8.1, the nodes are an injective family `x : Fin (n + 1) → ℝ`, the interpolant of $f$
  is `Lagrange.interpolate Finset.univ x (fun i => f (x i))`, and the nodal polynomial
  $\omega_{n+1}$ is `Lagrange.nodal Finset.univ x`. For $k \le n$, the polynomial $\omega_k$ of the
  first $k$ nodes is `DividedDifference.prefixNodal x k`.
* The book's case $n \ge 1$ in (8.14)–(8.16) is a family `x : Fin (n + 2) → ℝ`. Then `Fin.init x` is
  the family of the first $n + 1$ nodes and `x (Fin.last _)` is the last node.

## Not formalized

* **Examples 8.3 and 8.4.** They are tables of computed divided differences.
-/

open Polynomial Set DividedDifference

namespace QuarteroniSaccoSaleri.Chapter08

variable {n : ℕ} {f : ℝ → ℝ}

/-- **Equations (8.14)–(8.15)** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be distinct
nodes with $n \ge 1$. The coefficient $a_n$ of the polynomial $q_n = a_n \omega_n$ that is added
to $\Pi_{n-1} f$ to obtain $\Pi_n f$ is the $n$-th Newton divided difference:
$$f[x_0, \ldots, x_n] = \frac{f(x_n) - \Pi_{n-1} f(x_n)}{\omega_n(x_n)}, \qquad \omega_n(x_n) =
  \prod_{i=0}^{n-1} (x_n - x_i),$$
where $\Pi_{n-1} f$ interpolates $f$ at $x_0, \ldots, x_{n-1}$.

In Lean the nodes are $x_0, \ldots, x_{n+1}$, so the book's $n$ is $n + 1$ here. The backbone
defines the divided difference by the explicit formula (8.18), so this result is the equivalence
with the book's definition. The proof specializes `DividedDifference.eval_interpolate_snoc_sub`. -/
theorem equation_8_14 (f : ℝ → ℝ) {x : Fin (n + 2) → ℝ} (hx : Function.Injective x) :
    DividedDifference.newton f x
      = (f (x (Fin.last (n + 1)))
          - (Lagrange.interpolate Finset.univ (Fin.init x) fun i => f (Fin.init x i)).eval
              (x (Fin.last (n + 1))))
        / ∏ i : Fin (n + 1), (x (Fin.last (n + 1)) - x i.castSucc) := by
  have h := DividedDifference.eval_interpolate_snoc_sub f (v := Fin.init x)
    (t := x (Fin.last (n + 1))) (by rwa [Fin.snoc_init_self])
  rwa [Fin.snoc_init_self] at h

/-- **Equation (8.16)** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be distinct nodes with
$n \ge 1$. Then, as polynomials,
$$\Pi_n f = \Pi_{n-1} f + \omega_n f[x_0, \ldots, x_n],$$
where $\Pi_{n-1} f$ interpolates $f$ at $x_0, \ldots, x_{n-1}$ and
$\omega_n(x) = \prod_{i=0}^{n-1} (x - x_i)$.

The proof specializes `DividedDifference.interpolate_snoc_eq`. -/
theorem equation_8_16 (f : ℝ → ℝ) {x : Fin (n + 2) → ℝ} (hx : Function.Injective x) :
    (Lagrange.interpolate Finset.univ x fun i => f (x i))
      = (Lagrange.interpolate Finset.univ (Fin.init x) fun i => f (Fin.init x i))
        + C (DividedDifference.newton f x) * Lagrange.nodal Finset.univ (Fin.init x) := by
  have h := DividedDifference.interpolate_snoc_eq f (v := Fin.init x)
    (t := x (Fin.last (n + 1))) (by rwa [Fin.snoc_init_self])
  rwa [Fin.snoc_init_self] at h

/-- **Equation (8.17)** of [quarteroni2000numerical], the Newton divided difference formula. Let
$x_0, \ldots, x_n$ be distinct nodes. Then, with $f[x_0] = f(x_0)$ and $\omega_0 = 1$,
$$\Pi_n f(x) = \sum_{k=0}^n \omega_k(x) f[x_0, \ldots, x_k].$$

The divided difference $f[x_0, \ldots, x_k]$ is taken at the first $k + 1$ nodes
`DividedDifference.prefixNodes x k`.
The polynomial $\omega_k$ is `DividedDifference.prefixNodal x k`.
The proof specializes `DividedDifference.interpolate_eq_sum_newton_mul_prefixNodal`. -/
theorem equation_8_17 (f : ℝ → ℝ) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    (Lagrange.interpolate Finset.univ x fun i => f (x i))
      = ∑ k : Fin (n + 1),
          C (DividedDifference.newton f (DividedDifference.prefixNodes x k))
            * DividedDifference.prefixNodal x k :=
  DividedDifference.interpolate_eq_sum_newton_mul_prefixNodal f hx

/-! ### Section 8.2.1: properties of the Newton divided differences -/

/-- **Equation (8.18)** of [quarteroni2000numerical], the explicit representation. For nodes
$x_0, \ldots, x_n$,
$$f[x_0, \ldots, x_n] = \sum_{i=0}^n \frac{f(x_i)}{\omega_{n+1}'(x_i)}.$$

The statement assumes no distinctness of the nodes; a term with $\omega_{n+1}'(x_i) = 0$ is $0$
by the Lean convention $a / 0 = 0$. The result is the definition of `DividedDifference.newton`
once the denominators $\prod_{j \neq i} (x_i - x_j)$ are read as the values
$\omega_{n+1}'(x_i)$, by Exercise 3 of Chapter 8. -/
theorem equation_8_18 (f : ℝ → ℝ) (x : Fin (n + 1) → ℝ) :
    DividedDifference.newton f x
      = ∑ i, f (x i) / (derivative (Lagrange.nodal Finset.univ x)).eval (x i) := by
  unfold DividedDifference.newton
  exact Finset.sum_congr rfl fun i _ => by rw [exercise_8_3]

/-- **Section 8.2.1** of [quarteroni2000numerical], property 1. The divided difference is invariant
under permutations of the indices of the nodes: for every permutation $\sigma$ of
$\{0, \ldots, n\}$,
$$f[x_{\sigma(0)}, \ldots, x_{\sigma(n)}] = f[x_0, \ldots, x_n].$$

The proof specializes `DividedDifference.newton_comp_perm`. -/
theorem dividedDifference_perm (f : ℝ → ℝ) (x : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) :
    DividedDifference.newton f (x ∘ σ) = DividedDifference.newton f x :=
  DividedDifference.newton_comp_perm f x σ

/-- **Section 8.2.1** of [quarteroni2000numerical], property 2. If $f = \alpha g + \beta h$ for some
$\alpha, \beta \in \mathbb{R}$, then
$$f[x_0, \ldots, x_n] = \alpha g[x_0, \ldots, x_n] + \beta h[x_0, \ldots, x_n].$$

The proof uses `DividedDifference.newton_add` and `DividedDifference.newton_smul`. -/
theorem dividedDifference_linear (α β : ℝ) (g h : ℝ → ℝ) (x : Fin (n + 1) → ℝ) :
    DividedDifference.newton (fun t => α * g t + β * h t) x
      = α * DividedDifference.newton g x + β * DividedDifference.newton h x := by
  rw [show (fun t => α * g t + β * h t) = (fun t => α * g t) + fun t => β * h t from rfl,
    DividedDifference.newton_add, DividedDifference.newton_smul, DividedDifference.newton_smul]

/-- **Section 8.2.1** of [quarteroni2000numerical], property 3 (the Leibniz formula). Let
$x_0, \ldots, x_n$ be distinct nodes. If $f = gh$, then
$$f[x_0, \ldots, x_n] = \sum_{j=0}^n g[x_0, \ldots, x_j] \, h[x_j, \ldots, x_n].$$

The divided difference $g[x_0, \ldots, x_j]$ is taken at the prefix
`DividedDifference.prefixNodes x j`, and $h[x_j, \ldots, x_n]$ at the suffix
`DividedDifference.suffixNodes x j`. The proof specializes `DividedDifference.newton_mul`. -/
theorem dividedDifference_leibniz (g h : ℝ → ℝ) {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) :
    DividedDifference.newton (fun t => g t * h t) x
      = ∑ j : Fin (n + 1), DividedDifference.newton g (DividedDifference.prefixNodes x j)
          * DividedDifference.newton h (DividedDifference.suffixNodes x j) :=
  DividedDifference.newton_mul g h hx

/-- **Equation (8.19)** of [quarteroni2000numerical], the recursive formula (Section 8.2.1, property
4, and Exercise 7 of Chapter 8). Let $x_0, \ldots, x_n$ be distinct nodes with $n \ge 1$. Then
$$f[x_0, \ldots, x_n] = \frac{f[x_1, \ldots, x_n] - f[x_0, \ldots, x_{n-1}]}{x_n - x_0}.$$

In Lean the nodes are $x_0, \ldots, x_{n+1}$, so the book's $n$ is $n + 1$ here. The proof
specializes `DividedDifference.newton_succ`. -/
theorem equation_8_19 (f : ℝ → ℝ) {x : Fin (n + 2) → ℝ} (hx : Function.Injective x) :
    DividedDifference.newton f x
      = (DividedDifference.newton f (Fin.tail x) - DividedDifference.newton f (Fin.init x))
        / (x (Fin.last (n + 1)) - x 0) :=
  DividedDifference.newton_succ f hx

/-- **Section 8.2.1** of [quarteroni2000numerical], after Example 8.3. Let $x_0, \ldots, x_n$ be
distinct nodes. Then $f[x_0, \ldots, x_n] = 0$ for every polynomial $f \in \mathbb{P}_{n-1}$,
that is, of degree less than $n$.

The proof specializes `DividedDifference.newton_eq_zero_of_degree_lt`. -/
theorem dividedDifference_eq_zero_of_mem_polyLT {p : ℝ[X]} (hp : p.degree < n)
    {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    DividedDifference.newton (fun t => p.eval t) x = 0 :=
  DividedDifference.newton_eq_zero_of_degree_lt hp hx

/-! ### Section 8.2.2: the interpolation error using divided differences -/

/-- **Equation (8.20)** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be distinct nodes and
let $x$ be a point distinct from the nodes. Then
$$E_n(x) = f(x) - \Pi_n f(x) = \omega_{n+1}(x) f[x_0, \ldots, x_n, x].$$

The proof specializes `DividedDifference.sub_eval_interpolate_eq_newton`. -/
theorem equation_8_20 (f : ℝ → ℝ) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) {t : ℝ}
    (ht : ∀ i, x i ≠ t) :
    f t - (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t
      = (∏ i, (t - x i)) * DividedDifference.newton f (Fin.snoc x t) :=
  DividedDifference.sub_eval_interpolate_eq_newton f hx ht

/-- **Equation (8.21)** of [quarteroni2000numerical]. Let $x_0, \ldots, x_n$ be distinct nodes, let
$t$ be a point distinct from the nodes, and let $I_t$ be the smallest interval that contains the
nodes and $t$. Let $f$ be of class $C^{n+1}$ on an open set that contains $I_t$, as in Theorem
8.2. Then there is $\xi \in I_t$ with
$$f[x_0, \ldots, x_n, t] = \frac{f^{(n+1)}(\xi)}{(n+1)!}.$$

The book obtains the formula by comparing (8.20) with (8.7). The proof specializes
`DividedDifference.exists_newton_eq_iteratedDeriv_div_of_contDiffOn`, which uses the generalized
Rolle theorem at the $n + 2$ points $x_0, \ldots, x_n, t$. -/
theorem equation_8_21 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) {t : ℝ}
    (ht : ∀ i, x i ≠ t) {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hUsub : Icc (min t (⨅ i, x i)) (max t (⨆ i, x i)) ⊆ U)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Icc (min t (⨅ i, x i)) (max t (⨆ i, x i)),
      DividedDifference.newton f (Fin.snoc x t)
        = iteratedDeriv (n + 1) f ξ / (n + 1).factorial := by
  set a := min t (⨅ i, x i) with ha
  set b := max t (⨆ i, x i) with hb
  have hxmem : ∀ i, x i ∈ Icc a b := fun i =>
    ⟨(min_le_right _ _).trans (ciInf_le (Set.finite_range x).bddBelow i),
      (le_ciSup (Set.finite_range x).bddAbove i).trans (le_max_right _ _)⟩
  have htmem : t ∈ Icc a b := ⟨min_le_left _ _, le_max_left _ _⟩
  have hw : Function.Injective (Fin.snoc x t : Fin (n + 2) → ℝ) :=
    Fin.snoc_injective_iff.mpr ⟨hx, fun ⟨i, hi⟩ => ht i hi⟩
  have hwmem : ∀ i, (Fin.snoc x t : Fin (n + 2) → ℝ) i ∈ Icc a b := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa using htmem
    | cast i => simpa using hxmem i
  obtain ⟨ξ, hξ, h⟩ :=
    DividedDifference.exists_newton_eq_iteratedDeriv_div_of_contDiffOn hU hUsub hf hw hwmem
  exact ⟨ξ, Ioo_subset_Icc_self hξ, h⟩

end QuarteroniSaccoSaleri.Chapter08
