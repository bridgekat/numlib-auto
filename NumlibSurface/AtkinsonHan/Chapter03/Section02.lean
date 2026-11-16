/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Vandermonde
import Numlib.Approximation.DividedDifference
import Numlib.Approximation.Hermite

/-!
# Atkinson and Han, Section 3.2: Interpolation theory

This module formalizes Section 3.2 of [han2009theoretical]. The section first poses the
interpolation problem abstractly: given an $n$-dimensional subspace $V_n$ of a normed space $V$ and
bounded linear functionals $L_1, \dots, L_n$ on $V$, find $u_n \in V_n$ with $L_i u_n = b_i$ for
$i = 1, \dots, n$. The problem has a unique solution for every datum $b$ if and only if the
functionals are linearly independent over $V_n$, if and only if $\det(L_i v_j) \neq 0$ for a basis
$v_1, \dots, v_n$ of $V_n$. The section then treats four instances: Lagrange polynomial
interpolation, with Lagrange's formula and the error formula $f(x) - p_n(x) = \omega_n(x)
f^{(n+1)}(\xi_x)/(n + 1)!$; Hermite interpolation; piecewise linear interpolation, with the error
bounds $\omega(f, h)$ and $h^2 \|f''\|_\infty / 8$; and trigonometric interpolation at $2n + 1$
nodes of a period.

The abstract problem is the backbone module `Numlib.Approximation.Unisolvent`. Lagrange
interpolation and piecewise linear interpolation are `Numlib.Approximation.Interpolation`, Hermite
interpolation is `Numlib.Approximation.Hermite`, and the divided differences are
`Numlib.Approximation.DividedDifference`.

## Main definitions

* Definition 3.2.1, `AtkinsonHan.Chapter03.definition_3_2_1`: the functionals $L_1, \dots, L_n$ are
  linearly independent over $V_n$ if and only if the interpolation problem has a unique solution for
  every datum.

## Main results

* Lemma 3.2.2, `AtkinsonHan.Chapter03.lemma_3_2_2`: the functionals are linearly independent over
  $V_n$ if and only if $\det(L_i v_j) \neq 0$.
* Theorem 3.2.3, `AtkinsonHan.Chapter03.theorem_3_2_3`: four equivalent forms of the unique
  solvability of the interpolation problem.
* Equation (3.2.1), `AtkinsonHan.Chapter03.equation_3_2_1`: Lagrange interpolation at $n + 1$
  distinct nodes has a unique solution in $\mathcal{P}_n$.
* Equation (3.2.2), `AtkinsonHan.Chapter03.equation_3_2_2` and
  `AtkinsonHan.Chapter03.equation_3_2_2_ne_zero`: the Vandermonde determinant is
  $\prod_{j > i} (x_j - x_i)$, which is nonzero at distinct nodes.
* Equation (3.2.3), `AtkinsonHan.Chapter03.equation_3_2_3` and
  `AtkinsonHan.Chapter03.equation_3_2_3_delta`: Lagrange's formula $p_n = \sum_i f(x_i) \varphi_i$,
  and $\varphi_i(x_j) = \delta_{ij}$.
* Proposition 3.2.4, `AtkinsonHan.Chapter03.proposition_3_2_4`: the error formula $f(x) - p_n(x) =
  \omega_n(x) f^{(n+1)}(\xi_x)/(n + 1)!$.
* Equation (3.2.5), `AtkinsonHan.Chapter03.equation_3_2_5`: the error formula $f(x) - p_n(x) =
  \omega_n(x) f[x_0, \dots, x_n, x]$.
* Equation (3.2.6), `AtkinsonHan.Chapter03.equation_3_2_6`: Hermite interpolation of values and
  first derivatives at $n$ distinct nodes has a unique solution of degree at most $2n - 1$.
* Equation (3.2.6), `AtkinsonHan.Chapter03.equation_3_2_6_general` and
  `AtkinsonHan.Chapter03.equation_3_2_6_general_error`: Hermite interpolation with multiplicities,
  and its error formula.
* Equation (3.2.7), `AtkinsonHan.Chapter03.equation_3_2_7` and
  `AtkinsonHan.Chapter03.equation_3_2_7_unique`: the piecewise linear interpolant is affine on each
  subinterval, and is the only such continuous interpolant.
* Equation (3.2.8), `AtkinsonHan.Chapter03.equation_3_2_8`: $|f - \Pi f| \le \omega(f, h)$.
* Equation (3.2.9), `AtkinsonHan.Chapter03.equation_3_2_9`:
  $|f - \Pi f| \le h^2 \|f''\|_\infty / 8$.
* Equation (3.2.13), `AtkinsonHan.Chapter03.equation_3_2_13`: $\mathcal{T}_n$ consists of the
  functions $a_0 + \sum_{j=1}^n (a_j \cos(jx) + b_j \sin(jx))$.
* Equation (3.2.16), `AtkinsonHan.Chapter03.equation_3_2_16`: the evenly spaced nodes $x_j = j h$,
  $h = 2\pi/(2n + 1)$.
* Equation (3.2.17), `AtkinsonHan.Chapter03.equation_3_2_17` and
  `AtkinsonHan.Chapter03.equation_3_2_17_equispaced`: trigonometric interpolation at $2n + 1$
  distinct nodes of a period has a unique solution in $\mathcal{T}_n$.
* Example 3.2.5, `AtkinsonHan.Chapter03.example_3_2_5`: the function $e^{\sin x} \sin x$ of (3.2.18)
  and its trigonometric interpolants at the nodes (3.2.16).
* Exercise 3.2.6, `AtkinsonHan.Chapter03.exercise_3_2_6`: the error formula $f(x) - p(x) =
  f^{(2n)}(\xi) \prod_i (x - x_i)^2/(2n)!$ for Hermite interpolation.

## Conventions

* $\mathcal{P}_n$ on a compact $X \subseteq \mathbb{R}$ is `polyLE X n`, the subspace of `C(X, ℝ)`
  of the restrictions of real polynomials of degree at most $n$.
* $C_p(2\pi)$ is `C(AddCircle (2 * π), ℝ)`, as in the rest of the library, and $\mathcal{T}_n$ is
  its subspace `trigPolyLE (2 * π) n`.
* The source indexes the Lagrange nodes $x_0 < \cdots < x_n$ from $0$ and the Hermite nodes
  $x_1 < \cdots < x_n$ from $1$. Both are indexed from $0$ here. So in
  `AtkinsonHan.Chapter03.exercise_3_2_6` the $n$ nodes of (3.2.6) become $n + 1$ nodes, and the
  degree bound $2n - 1$ becomes $2(n + 1) - 1$.
* Where the source bounds the maximum of $|f - \Pi f|$ over $[a, b]$, the statements here give the
  bound at each point. On a compact interval the two are the same, and the pointwise form needs no
  supremum.

## Implementation notes

* "The interpolation problem has a unique solution" is `Approximation.IsUnisolvent Vₙ L`. Definition
  3.2.1, Lemma 3.2.2 and Theorem 3.2.3 specialize
  `Approximation.isUnisolvent_iff_linearIndependent`, `Approximation.isUnisolvent_iff_det_ne_zero`
  and `Approximation.isUnisolvent_tfae`.
* Trigonometric interpolation at the evenly spaced nodes is `trigInterpCLM`. Its unique solvability
  comes from the Haar condition for `trigPolyLE`, which the backbone proves once in
  `Numlib.Approximation.Chebyshev` by the substitution $z = e^{ix}$ of (3.2.15).

## Not formalized

* **The estimates (3.2.10)–(3.2.12)** for piecewise linear interpolation in $H^2(a, b)$. They need
  Sobolev spaces.
* **The Newton form of the interpolant**, which the source only cites. The divided-difference form
  (3.2.5) of the error is `AtkinsonHan.Chapter03.equation_3_2_5`, from `DividedDifference.newton`.
* **Table 3.1**, the computed maximum errors of Example 3.2.5 for $n = 1, \dots, 14$. Each entry is
  a supremum over the circle of a transcendental function, so a rigorous value needs verified
  numerics, which the project does not have. The source draws nothing from the table beyond the
  convergence that §3.7 proves.
-/

open scoped Polynomial Real

namespace AtkinsonHan.Chapter03

/-! ### The abstract interpolation problem -/

section Abstract

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {n : ℕ} {Vₙ : Submodule 𝕜 V} {L : Fin n → StrongDual 𝕜 V}

/-- **Definition 3.2.1** of [han2009theoretical]. Let $V$ be a normed space over a nontrivially
normed field $\mathbb{K}$, let $V_n$ be a subspace of $V$ with a basis of $n$ elements, and let
$L_1, \dots, L_n$ be bounded linear functionals on $V$. The functionals are **linearly
independent over $V_n$** if
$$\sum_{i=1}^n c_i L_i(v) = 0 \text{ for all } v \in V_n \implies c_1 = \cdots = c_n = 0.$$
This holds if and only if the interpolation problem $L_i u_n = b_i$, $i = 1, \dots, n$, has
exactly one solution $u_n \in V_n$ for every $b \in \mathbb{K}^n$.

The unique solvability is the backbone's `Approximation.IsUnisolvent Vₙ L`, and the proof is
`Approximation.isUnisolvent_iff_linearIndependent`. The basis `v` only fixes $\dim V_n = n$. -/
theorem definition_3_2_1 (v : Module.Basis (Fin n) 𝕜 Vₙ) :
    Approximation.IsUnisolvent Vₙ L ↔
      ∀ c : Fin n → 𝕜, (∀ w ∈ Vₙ, ∑ i, c i * L i w = 0) → ∀ i, c i = 0 := by
  rw [Approximation.isUnisolvent_iff_linearIndependent v, Fintype.linearIndependent_iff]
  refine forall_congr' fun c => imp_congr_left ?_
  constructor
  · intro hsum w hw
    have := congrArg (fun g : Vₙ →ₗ[𝕜] 𝕜 => g ⟨w, hw⟩) hsum
    simpa using this
  · intro hsum
    refine LinearMap.ext fun u => ?_
    simpa using hsum (u : V) u.2

/-- **Lemma 3.2.2** of [han2009theoretical]. Let $V_n$ be a subspace of a normed space $V$ with a
basis $v_1, \dots, v_n$, and let $L_1, \dots, L_n$ be bounded linear functionals on $V$. Then
$L_1, \dots, L_n$ are linearly independent over $V_n$ if and only if
$$\det(L_i v_j)_{i,j=1}^n \neq 0.$$
Since the left-hand side does not mention the basis, the nonvanishing of the determinant does
not depend on the basis. -/
theorem lemma_3_2_2 (v : Module.Basis (Fin n) 𝕜 Vₙ) :
    (∀ c : Fin n → 𝕜, (∀ w ∈ Vₙ, ∑ i, c i * L i w = 0) → ∀ i, c i = 0) ↔
      (Matrix.of fun i j => L i (v j : V)).det ≠ 0 :=
  (definition_3_2_1 v).symm.trans (Approximation.isUnisolvent_iff_det_ne_zero v)

/-- **Theorem 3.2.3** of [han2009theoretical]. Let $V_n$ be a subspace of a normed space $V$ with a
basis of $n$ elements, and let $L_1, \dots, L_n$ be bounded linear functionals on $V$. The
following are equivalent:

1. for every $b \in \mathbb{K}^n$ the interpolation problem $L_i u_n = b_i$, $i = 1, \dots, n$,
   has exactly one solution $u_n \in V_n$;
2. the functionals are linearly independent over $V_n$;
3. the only $u_n \in V_n$ with $L_i u_n = 0$ for all $i$ is $u_n = 0$;
4. for every $b \in \mathbb{K}^n$ the interpolation problem has at least one solution
   $u_n \in V_n$.

The equivalence is stated as `List.TFAE`. -/
theorem theorem_3_2_3 (v : Module.Basis (Fin n) 𝕜 Vₙ) :
    List.TFAE
      [∀ b : Fin n → 𝕜, ∃! u : Vₙ, ∀ i, L i (u : V) = b i,
        ∀ c : Fin n → 𝕜, (∀ w ∈ Vₙ, ∑ i, c i * L i w = 0) → ∀ i, c i = 0,
        ∀ u : Vₙ, (∀ i, L i (u : V) = 0) → u = 0,
        ∀ b : Fin n → 𝕜, ∃ u : Vₙ, ∀ i, L i (u : V) = b i] := by
  tfae_have 1 ↔ 2 := definition_3_2_1 v
  tfae_have 1 ↔ 3 := Approximation.isUnisolvent_iff_forall_eq_zero v
  tfae_have 1 ↔ 4 := Approximation.isUnisolvent_iff_forall_exists v
  tfae_finish

end Abstract

/-! ### Lagrange polynomial interpolation -/

section Lagrange

variable {a b : ℝ} {n : ℕ}

/-- The Lagrange basis function $\varphi_i$ of (3.2.3) is $\varphi_i(t) = \prod_{j \neq i} (t -
x_j)/(x_i - x_j)$. -/
private theorem basisCM_eq_prod (x : Fin (n + 1) → Set.Icc a b) (i : Fin (n + 1))
    (t : Set.Icc a b) :
    Lagrange.basisCM x i t
      = ∏ j ∈ Finset.univ.erase i, ((t : ℝ) - (x j : ℝ)) / ((x i : ℝ) - (x j : ℝ)) := by
  rw [Lagrange.basisCM_apply, Lagrange.basis, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun j _ => by simp [Lagrange.basisDivisor, div_eq_inv_mul]

/-- **Equation (3.2.1)** of [han2009theoretical]. Let $x_0, \dots, x_n$ be distinct nodes in
$[a, b]$ and let $f \in C[a, b]$. Then there is exactly one $p_n \in \mathcal{P}_n$ with
$$p_n(x_i) = f(x_i), \qquad i = 0, \dots, n.$$

$\mathcal{P}_n$ is `polyLE (Set.Icc a b) n`, and the distinctness of the nodes is
`Function.Injective x`. -/
theorem equation_3_2_1 {x : Fin (n + 1) → Set.Icc a b} (hx : Function.Injective x)
    (f : C(Set.Icc a b, ℝ)) :
    ∃! p : polyLE (Set.Icc a b) n, ∀ i, (p : C(Set.Icc a b, ℝ)) (x i) = f (x i) :=
  Lagrange.isUnisolvent_polyLE hx fun i => f (x i)

/-- **Equation (3.2.2)** of [han2009theoretical]. Let $x_0, \dots, x_n \in \mathbb{R}$. In the
monomial basis $v_j(x) = x^j$ of $\mathcal{P}_n$, the matrix $(L_i v_j) = (x_i^j)$ of the
Lagrange interpolation problem is the Vandermonde matrix of the nodes, and
$$\det\bigl(x_i^j\bigr)_{i,j=0}^n = \prod_{0 \le i < j \le n} (x_j - x_i).$$
-/
theorem equation_3_2_2 (x : Fin (n + 1) → ℝ) :
    (Matrix.of fun i j : Fin (n + 1) => ((Polynomial.X : ℝ[X]) ^ (j : ℕ)).eval (x i)).det
      = ∏ i, ∏ j ∈ Finset.Ioi i, (x j - x i) := by
  have h : (Matrix.of fun i j : Fin (n + 1) => ((Polynomial.X : ℝ[X]) ^ (j : ℕ)).eval (x i))
      = Matrix.vandermonde x := by
    ext i j
    simp [Matrix.vandermonde]
  rw [h, Matrix.det_vandermonde]

/-- **Equation (3.2.2)** of [han2009theoretical], the nonvanishing. If the nodes
$x_0, \dots, x_n \in \mathbb{R}$ are distinct, then the Vandermonde determinant $\det(x_i^j)$ is
nonzero. With Lemma 3.2.2 this gives the unique solvability (3.2.1) again. -/
theorem equation_3_2_2_ne_zero {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) :
    (Matrix.of fun i j : Fin (n + 1) => ((Polynomial.X : ℝ[X]) ^ (j : ℕ)).eval (x i)).det ≠ 0 := by
  rw [equation_3_2_2]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  exact sub_ne_zero.mpr fun h => absurd (hx h) (Finset.mem_Ioi.mp hj).ne'

/-- **Equation (3.2.3)** of [han2009theoretical] (Lagrange's formula). Let
$x_0, \dots, x_n \in [a, b]$ and $f \in C[a, b]$. The Lagrange interpolant of $f$ is
$$p_n(t) = \sum_{i=0}^n f(x_i) \varphi_i(t), \qquad \varphi_i(t) = \prod_{j \neq i} \frac{t -
  x_j}{x_i - x_j}.$$

The interpolant is `Lagrange.interpolateCLM x f`. The identity holds for any nodes, with Lean's
convention that division by $0$ gives $0$. It is the interpolant of (3.2.1) when the nodes are
distinct. -/
theorem equation_3_2_3 (x : Fin (n + 1) → Set.Icc a b) (f : C(Set.Icc a b, ℝ))
    (t : Set.Icc a b) :
    Lagrange.interpolateCLM x f t
      = ∑ i, f (x i) * ∏ j ∈ Finset.univ.erase i,
          ((t : ℝ) - (x j : ℝ)) / ((x i : ℝ) - (x j : ℝ)) := by
  rw [Lagrange.interpolateCLM_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [basisCM_eq_prod]

/-- **Equation (3.2.3)** of [han2009theoretical], the cardinal property. Let $x_0, \dots, x_n$ be
distinct nodes in $[a, b]$. Then the Lagrange basis functions satisfy
$$\varphi_i(x_j) = \delta_{ij}, \qquad i, j = 0, \dots, n.$$
This makes (3.2.3) an interpolant and the $\varphi_i$ a basis of $\mathcal{P}_n$. -/
theorem equation_3_2_3_delta {x : Fin (n + 1) → Set.Icc a b} (hx : Function.Injective x)
    (i j : Fin (n + 1)) :
    (∏ k ∈ Finset.univ.erase i, ((x j : ℝ) - (x k : ℝ)) / ((x i : ℝ) - (x k : ℝ)))
      = if i = j then 1 else 0 := by
  rw [← basisCM_eq_prod]
  by_cases hij : i = j
  · subst hij
    simp [Lagrange.basisCM_apply_node_self hx]
  · simp [Lagrange.basisCM_apply_node_ne hij, hij]

/-- **Proposition 3.2.4** of [han2009theoretical], with (3.2.4). Let $f \in C^{n+1}(\mathbb{R})$,
let $x_0 < x_1 < \cdots < x_n$, let $p_n$ be the Lagrange interpolant of $f$ at these nodes, and
let $t \in \mathbb{R}$. Then there is a $\xi$ with $\min\{t, x_0\} \le \xi \le \max\{t, x_n\}$
and
$$f(t) - p_n(t) = \frac{\omega_n(t)}{(n + 1)!} f^{(n+1)}(\xi), \qquad \omega_n(t) =
  \prod_{i=0}^n (t - x_i).$$

The interpolant is `Lagrange.interpolate`. The backbone's `Lagrange.exists_sub_interpolate_eq`
places $\xi$ strictly inside any interval that contains the nodes and $t$; the interval
$[\min\{t, x_0\}, \max\{t, x_n\}]$ gives the localization of the source. The statement uses the
closed interval because the interval is a single point when $t$ is the only node, and there both
sides of the identity are $0$. -/
theorem proposition_3_2_4 {f : ℝ → ℝ} (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f)
    {x : Fin (n + 1) → ℝ} (hx : StrictMono x) (t : ℝ) :
    ∃ ξ ∈ Set.Icc (min t (x 0)) (max t (x (Fin.last n))),
      f t - (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t
        = (∏ i, (t - x i)) / (n + 1).factorial * iteratedDeriv (n + 1) f ξ := by
  set lo := min t (x 0) with hlo
  set hi := max t (x (Fin.last n)) with hhi
  have hxlo : ∀ i, lo ≤ x i := fun i =>
    le_trans (min_le_right _ _) (hx.monotone (Fin.zero_le i))
  have hxhi : ∀ i, x i ≤ hi := fun i =>
    le_trans (hx.monotone (Fin.le_last i)) (le_max_right _ _)
  have htmem : t ∈ Set.Icc lo hi := ⟨min_le_left _ _, le_max_left _ _⟩
  rcases lt_or_ge lo hi with hlt | hge
  · obtain ⟨ξ, hξ, hval⟩ := Lagrange.exists_sub_interpolate_eq hlt hf hx.injective
      (fun i => ⟨hxlo i, hxhi i⟩) htmem
    exact ⟨ξ, Set.Ioo_subset_Icc_self hξ, by rw [hval]; ring⟩
  · -- the degenerate case: the interval collapses, so every node equals `t`
    have hlot : lo = t := le_antisymm htmem.1 (htmem.2.trans hge)
    have hxt : ∀ i, x i = t :=
      fun i => le_antisymm ((hxhi i).trans (hge.trans hlot.le)) (hlot ▸ hxlo i)
    refine ⟨t, htmem, ?_⟩
    have hev : (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t = f t := by
      rw [← hxt 0, Lagrange.eval_interpolate_at_node _ hx.injective.injOn (Finset.mem_univ 0)]
    rw [hev, sub_self, Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n + 1)))
      (by rw [hxt 0, sub_self])]
    simp

/-- **Equation (3.2.5)** of [han2009theoretical]. Let $x_0, \dots, x_n$ be distinct nodes, let
$f : \mathbb{R} \to \mathbb{R}$, let $p_n$ be the Lagrange interpolant of $f$ at the nodes, and
let $x$ be a point that is not a node. Then
$$f(x) - p_n(x) = \omega_n(x) \, f[x_0, \dots, x_n, x], \qquad \omega_n(x) = \prod_{i=0}^n (x -
  x_i),$$
where $f[x_0, \dots, x_n, x]$ is the Newton divided difference of order $n + 1$.

Unlike Proposition 3.2.4, the formula needs nothing of $f$ beyond its values at the nodes and at
$x$. The source states it in passing and uses it for the Newton form of the interpolant. The
divided difference is `DividedDifference.newton f (Fin.snoc x t)`. -/
theorem equation_3_2_5 {f : ℝ → ℝ} {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) {t : ℝ}
    (ht : ∀ i, x i ≠ t) :
    f t - (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t
      = (∏ i, (t - x i)) * DividedDifference.newton f (Fin.snoc x t) :=
  DividedDifference.sub_eval_interpolate_eq_newton f hx ht

end Lagrange

/-! ### Hermite polynomial interpolation -/

section Hermite

/-- **Equation (3.2.6)** of [han2009theoretical] (Hermite interpolation). Let $x_1, \dots, x_n$ be
distinct real nodes and let $f : \mathbb{R} \to \mathbb{R}$. Then there is exactly one real
polynomial $p$ of degree at most $2n - 1$ with
$$p(x_i) = f(x_i), \qquad p'(x_i) = f'(x_i), \qquad i = 1, \dots, n.$$

The degree bound is `p.degree < 2 * n`, which for $n = 0$ forces $p = 0$. No smoothness of $f$
is assumed: the statement is about the prescribed numbers $f(x_i)$ and $f'(x_i)$ and holds
whatever they are. The derivative is `deriv f`, which is $0$ where $f$ is not differentiable. -/
theorem equation_3_2_6 {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) (f : ℝ → ℝ) :
    ∃! p : ℝ[X], p.degree < ((2 * n : ℕ) : WithBot ℕ) ∧
      (∀ i, p.eval (x i) = f (x i)) ∧
      (∀ i, (Polynomial.derivative p).eval (x i) = deriv f (x i)) := by
  have hM : ∑ _i : Fin n, ((1 : ℕ) + 1) = 2 * n := by
    simp [Finset.sum_const, mul_comm]
  have key := Hermite.isUnisolvent hx (m := fun _ => 1) hM fun i j => iteratedDeriv j f (x i)
  have hiff : ∀ p : ℝ[X],
      (∀ i, ∀ j ≤ 1, (Polynomial.derivative^[j] p).eval (x i) = iteratedDeriv j f (x i))
        ↔ ((∀ i, p.eval (x i) = f (x i)) ∧
            ∀ i, (Polynomial.derivative p).eval (x i) = deriv f (x i)) := by
    intro p
    constructor
    · refine fun h => ⟨fun i => by simpa using h i 0 (by omega), fun i => ?_⟩
      simpa [iteratedDeriv_one] using h i 1 le_rfl
    · rintro ⟨h0, h1⟩ i j hj
      interval_cases j
      · simpa using h0 i
      · simpa [iteratedDeriv_one] using h1 i
  simpa only [hiff] using key

/-- **Exercise 3.2.6** of [han2009theoretical], the error of Hermite interpolation (3.2.6). Let
$x_0 < x_1 < \cdots < x_n$ be $n + 1$ real nodes, let $f \in C^{2(n+1)}(\mathbb{R})$, let $p$ be
the Hermite interpolant of the values and first derivatives of $f$ at the nodes, and let
$t \in \mathbb{R}$. Then there is a $\xi$ with $\min\{t, x_0\} \le \xi \le \max\{t, x_n\}$ and
$$f(t) - p(t) = \frac{f^{(2(n+1))}(\xi)}{(2(n + 1))!} \prod_{i=0}^n (t - x_i)^2.$$

The nodes are indexed by `Fin (n + 1)`, so $n$ of the source is $n + 1$ here. The interpolant is
`Hermite.interpolate x (fun _ => 1) f`, with multiplicity $1$ at every node. -/
theorem exercise_3_2_6 {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * (n + 1) : ℕ) : WithTop ℕ∞) f) {x : Fin (n + 1) → ℝ}
    (hx : StrictMono x) (t : ℝ) :
    ∃ ξ ∈ Set.Icc (min t (x 0)) (max t (x (Fin.last n))),
      f t - (Hermite.interpolate x (fun _ => 1) f).eval t
        = (∏ i, (t - x i) ^ 2) / (2 * (n + 1)).factorial * iteratedDeriv (2 * (n + 1)) f ξ := by
  have hxlo : ∀ i, min t (x 0) ≤ x i := fun i =>
    le_trans (min_le_right _ _) (hx.monotone (Fin.zero_le i))
  have hxhi : ∀ i, x i ≤ max t (x (Fin.last n)) := fun i =>
    le_trans (hx.monotone (Fin.le_last i)) (le_max_right _ _)
  have hsum : ∑ _i : Fin (n + 1), ((1 : ℕ) + 1) = 2 * n + 1 + 1 := by
    simp [Finset.sum_const]
    ring
  have hf' : ContDiff ℝ ((2 * n + 1 + 1 : ℕ) : WithTop ℕ∞) f := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
    exact hf
  obtain ⟨ξ, hξ, hval⟩ := Hermite.exists_sub_interpolate_eq (N := 2 * n + 1)
    hf' hx.injective (fun i => ⟨hxlo i, hxhi i⟩) hsum
    (⟨min_le_left _ _, le_max_left _ _⟩ : t ∈ Set.Icc _ _)
  refine ⟨ξ, hξ, ?_⟩
  rw [hval, show 2 * n + 1 + 1 = 2 * (n + 1) by ring]
  ring

/-- **The general Hermite interpolation problem**, which extends (3.2.6) of [han2009theoretical] to
multiplicities. Let $x_1, \dots, x_n$ be distinct real nodes, let $m_1, \dots, m_n \ge 0$ with
$\sum_i (m_i + 1) = N + 1$, and let $f : \mathbb{R} \to \mathbb{R}$. Then there is exactly one
$p \in \mathcal{P}_N$ with
$$p^{(j)}(x_i) = f^{(j)}(x_i), \qquad 0 \le j \le m_i, \quad i = 1, \dots, n.$$

The nodes are indexed from $0$. The derivatives of $f$ are `iteratedDeriv j f`, so, as in
`AtkinsonHan.Chapter03.equation_3_2_6`, no smoothness of $f$ is assumed. -/
theorem equation_3_2_6_general {n N : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x)
    {m : Fin n → ℕ} (hN : ∑ i, (m i + 1) = N + 1) (f : ℝ → ℝ) :
    ∃! p : ℝ[X], p.degree < ((N + 1 : ℕ) : WithBot ℕ) ∧
      ∀ i, ∀ j ≤ m i, (Polynomial.derivative^[j] p).eval (x i) = iteratedDeriv j f (x i) :=
  Hermite.isUnisolvent hx hN fun i j => iteratedDeriv j f (x i)

/-- **The error of the general Hermite interpolation problem** of
`AtkinsonHan.Chapter03.equation_3_2_6_general`. Let $x_1, \dots, x_n$ be distinct nodes in
$[a, b]$, let $m_1, \dots, m_n \ge 0$ with $\sum_i (m_i + 1) = N + 1$, let
$f \in C^{N+1}(\mathbb{R})$, let $p$ be its Hermite interpolant, and let $t \in [a, b]$. Then
there is a $\xi \in [a, b]$ with
$$f(t) - p(t) = \frac{f^{(N+1)}(\xi)}{(N + 1)!} \prod_{i=1}^n (t - x_i)^{m_i + 1}.$$

The interpolant is `Hermite.interpolate x m f`. -/
theorem equation_3_2_6_general_error {n N : ℕ} {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f) {x : Fin n → ℝ} (hx : Function.Injective x)
    (hxmem : ∀ i, x i ∈ Set.Icc a b) {m : Fin n → ℕ} (hN : ∑ i, (m i + 1) = N + 1) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Icc a b, f t - (Hermite.interpolate x m f).eval t
      = (∏ i, (t - x i) ^ (m i + 1)) / (N + 1).factorial * iteratedDeriv (N + 1) f ξ := by
  obtain ⟨ξ, hξ, hval⟩ := Hermite.exists_sub_interpolate_eq hf hx hxmem hN ht
  exact ⟨ξ, hξ, by rw [hval]; ring⟩

end Hermite

/-! ### Piecewise linear interpolation -/

section PiecewiseLinear

variable {a b : ℝ} {n : ℕ} {x : ℕ → Set.Icc a b}

/-- **Equation (3.2.7)** of [han2009theoretical]. Let $x_0 < x_1 < \cdots < x_{n+1}$ be nodes in
$[a, b]$, let $f \in C[a, b]$, and let $\Pi f$ be its piecewise linear interpolant. For
$0 \le j \le n$ and $t \in [x_j, x_{j+1}]$,
$$\Pi f(t) = \frac{(x_{j+1} - t) f(x_j) + (t - x_j) f(x_{j+1})}{h_j}, \qquad h_j = x_{j+1} -
  x_j.$$

The interpolant is `piecewiseLinearInterpCLM n x f`. The nodes are a sequence
`x : ℕ → Set.Icc a b`, of which only $x_0, \dots, x_{n+1}$ are used. -/
theorem equation_3_2_7 (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (f : C(Set.Icc a b, ℝ))
    {j : ℕ} (hj : j ≤ n) {t : Set.Icc a b} (h1 : (x j : ℝ) ≤ (t : ℝ))
    (h2 : (t : ℝ) ≤ (x (j + 1) : ℝ)) :
    piecewiseLinearInterpCLM n x f t
      = ((x (j + 1) : ℝ) - (t : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)) * f (x j)
        + ((t : ℝ) - (x j : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)) * f (x (j + 1)) := by
  have hd : ((x (j + 1) : ℝ) - (x j : ℝ)) ≠ 0 := sub_ne_zero.mpr (hstep j hj).ne'
  rw [piecewiseLinearInterpCLM_apply_of_mem hstep f hj h1 h2]
  field_simp
  ring

/-- **Equation (3.2.7)** of [han2009theoretical], uniqueness. Let
$a = x_0 < x_1 < \cdots < x_{n+1} = b$ and let $f, g \in C[a, b]$. If $g(x_j) = f(x_j)$ for
$0 \le j \le n + 1$ and $g$ is affine on every subinterval $[x_j, x_{j+1}]$, in the sense that
(3.2.7) holds for $g$ in place of $\Pi f$, then $g = \Pi f$. -/
theorem equation_3_2_7_unique (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ))
    (hfirst : (x 0 : ℝ) = a) (hlast : (x (n + 1) : ℝ) = b) (f g : C(Set.Icc a b, ℝ))
    (hnode : ∀ j ≤ n + 1, g (x j) = f (x j))
    (haffine : ∀ j ≤ n, ∀ t : Set.Icc a b, (x j : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ (x (j + 1) : ℝ) →
      g t = ((x (j + 1) : ℝ) - (t : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)) * g (x j)
        + ((t : ℝ) - (x j : ℝ)) / ((x (j + 1) : ℝ) - (x j : ℝ)) * g (x (j + 1))) :
    g = piecewiseLinearInterpCLM n x f := by
  refine ContinuousMap.ext fun t => ?_
  obtain ⟨j, hj, h1, h2⟩ := exists_mem_subinterval hfirst hlast t
  rw [haffine j hj t h1 h2, equation_3_2_7 hstep f hj h1 h2, hnode j (by omega),
    hnode (j + 1) (by omega)]

/-- **Equation (3.2.8)** of [han2009theoretical]. Let $a = x_0 < x_1 < \cdots < x_{n+1} = b$ be a
partition with $x_{j+1} - x_j \le h$ for all $j$, and let $f \in C[a, b]$. Then for every
$t \in [a, b]$,
$$|f(t) - \Pi f(t)| \le \omega(f, h),$$
where $\omega(f, h) = \sup\{|f(u) - f(v)| : u, v \in [a, b], |u - v| \le h\}$ is the modulus of
continuity of $f$.

The modulus of continuity is `ContinuousMap.modulusOfContinuity f h`. -/
theorem equation_3_2_8 (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) (f : C(Set.Icc a b, ℝ)) {h : ℝ}
    (hmesh : ∀ i ≤ n, (x (i + 1) : ℝ) - (x i : ℝ) ≤ h) (t : Set.Icc a b) :
    |f t - piecewiseLinearInterpCLM n x f t| ≤ f.modulusOfContinuity h :=
  calc |f t - piecewiseLinearInterpCLM n x f t|
      = ‖(f - piecewiseLinearInterpCLM n x f) t‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖f - piecewiseLinearInterpCLM n x f‖ := ContinuousMap.norm_coe_le_norm _ t
    _ ≤ f.modulusOfContinuity h :=
        norm_sub_piecewiseLinearInterpCLM_le_modulus
          ⟨fun i hi => hstep i (by omega), hfirst, hlast⟩ f hmesh

/-- **Equation (3.2.9)** of [han2009theoretical]. Let $a = x_0 < x_1 < \cdots < x_{n+1} = b$ be a
partition with $x_{j+1} - x_j \le h$ for all $j$, and let $f \in C^2[a, b]$ with
$|f''(t)| \le M$ for all $t \in [a, b]$. Then for every $t \in [a, b]$,
$$|f(t) - \Pi f(t)| \le \frac{h^2}{8} M.$$

`C([a, b], ℝ)` carries no derivative of its own, so $f$ is given as a $C^2$ function
$g : \mathbb{R} \to \mathbb{R}$ that agrees with the continuous function on $[a, b]$. The source
writes $\|f''\|_\infty$ for $M$. -/
theorem equation_3_2_9 (hstep : ∀ i ≤ n, (x i : ℝ) < (x (i + 1) : ℝ)) (hfirst : (x 0 : ℝ) = a)
    (hlast : (x (n + 1) : ℝ) = b) {g : ℝ → ℝ} (hg : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) g)
    {f : C(Set.Icc a b, ℝ)} (hf : ∀ t : Set.Icc a b, f t = g (t : ℝ)) {h M : ℝ}
    (hmesh : ∀ i ≤ n, (x (i + 1) : ℝ) - (x i : ℝ) ≤ h)
    (hM : ∀ t ∈ Set.Icc a b, |iteratedDeriv 2 g t| ≤ M) (t : Set.Icc a b) :
    |f t - piecewiseLinearInterpCLM n x f t| ≤ h ^ 2 / 8 * M :=
  calc |f t - piecewiseLinearInterpCLM n x f t|
      = ‖(f - piecewiseLinearInterpCLM n x f) t‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖f - piecewiseLinearInterpCLM n x f‖ := ContinuousMap.norm_coe_le_norm _ t
    _ ≤ h ^ 2 / 8 * M :=
        norm_sub_piecewiseLinearInterpCLM_le ⟨fun i hi => hstep i (by omega), hfirst, hlast⟩ hg hf
          hmesh hM

end PiecewiseLinear

/-! ### Trigonometric interpolation -/

section Trigonometric

/-- A sum over the symmetric range $-n \le m \le n$ of $\mathbb{Z}$ is the middle term plus the sum
of the pairs $g(j) + g(-j)$, $1 \le j \le n$. -/
private theorem sum_Icc_neg (g : ℤ → ℝ) (n : ℕ) :
    ∑ m ∈ Finset.Icc (-(n : ℤ)) n, g m = g 0 + ∑ j ∈ Finset.Icc 1 n, (g j + g (-j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1)
        = insert ((n : ℤ) + 1) (insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) (n : ℤ))) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h2 : ((n : ℤ) + 1) ∉ insert (-((n : ℤ) + 1)) (Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have h3 : (-((n : ℤ) + 1)) ∉ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    push_cast
    rw [h1, Finset.sum_insert h2, Finset.sum_insert h3, ih,
      Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]
    push_cast
    abel

/-- On the circle of circumference $2\pi$, the member of index $j \ge 1$ of the real trigonometric
system is $\sqrt{2} \cos(jt)$. -/
private theorem trigFun_two_pi_cos {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    trigFun (2 * π) (j : ℤ) (↑t : AddCircle (2 * π)) = √2 * Real.cos (j * t) := by
  rw [trigFun_coe_of_pos (by exact_mod_cast hj) t, Int.cast_natCast]

/-- On the circle of circumference $2\pi$, the member of index $-j$, $j \ge 1$, of the real
trigonometric system is $\sqrt{2} \sin(jt)$. -/
private theorem trigFun_two_pi_sin {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    trigFun (2 * π) (-(j : ℤ)) (↑t : AddCircle (2 * π)) = √2 * Real.sin (j * t) := by
  rw [trigFun_coe_of_neg (by omega) t]
  push_cast
  ring_nf

/-- The value at $t$ of a combination of the members of index $-n, \dots, n$ of the real
trigonometric system, written with $\cos(jt)$ and $\sin(jt)$. -/
private theorem sum_trigFun_two_pi_coe (d : ℤ → ℝ) (n : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.Icc (-(n : ℤ)) n, d m • trigFun (2 * π) m) (↑t : AddCircle (2 * π))
      = d 0 + ∑ j ∈ Finset.Icc 1 n,
          (√2 * d j * Real.cos (j * t) + √2 * d (-j) * Real.sin (j * t)) := by
  rw [ContinuousMap.sum_apply]
  have hval : ∀ m : ℤ, (d m • trigFun (2 * π) m) (↑t : AddCircle (2 * π))
      = d m * trigFun (2 * π) m ↑t := fun _ => rfl
  simp only [hval]
  rw [sum_Icc_neg fun m => d m * trigFun (2 * π) m (↑t : AddCircle (2 * π))]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [trigFun_two_pi_cos hj1, trigFun_two_pi_sin hj1]
    ring

/-- **Equation (3.2.13)** of [han2009theoretical]. A function $p \in C_p(2\pi)$ is a trigonometric
polynomial of degree at most $n$, that is, $p \in \mathcal{T}_n$, if and only if there are real
coefficients $a_j$ and $b_j$ with
$$p(x) = a_0 + \sum_{j=1}^n \bigl(a_j \cos(jx) + b_j \sin(jx)\bigr) \quad \text{for all } x \in
  \mathbb{R}.$$

$\mathcal{T}_n$ is `trigPolyLE (2 * π) n`, the span of the members of index $-n, \dots, n$ of
`trigFun (2 * π)`. -/
theorem equation_3_2_13 {n : ℕ} {p : C(AddCircle (2 * π), ℝ)} :
    p ∈ trigPolyLE (2 * π) n ↔
      ∃ a b : ℕ → ℝ, ∀ t : ℝ,
        p (↑t : AddCircle (2 * π))
          = a 0 + ∑ j ∈ Finset.Icc 1 n, (a j * Real.cos (j * t) + b j * Real.sin (j * t)) := by
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  constructor
  · rintro hp
    obtain ⟨d, rfl⟩ := mem_trigPolyLE_iff.mp hp
    refine ⟨Function.update (fun j : ℕ => √2 * d j) 0 (d 0), fun j => √2 * d (-j), fun t => ?_⟩
    rw [sum_trigFun_two_pi_coe d n t, Function.update_self]
    refine congrArg _ (Finset.sum_congr rfl fun j hj => ?_)
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [Function.update_of_ne (by omega : j ≠ 0)]
  · rintro ⟨a, b, hab⟩
    set d : ℤ → ℝ := fun m => if m = 0 then a 0
      else if 0 < m then (√2)⁻¹ * a m.toNat else (√2)⁻¹ * b (-m).toNat with hd
    have hd0 : d 0 = a 0 := by simp [hd]
    have hdval : ∀ j : ℕ, 1 ≤ j →
        d (j : ℤ) = (√2)⁻¹ * a j ∧ d (-(j : ℤ)) = (√2)⁻¹ * b j := by
      intro j hj
      have hjne : j ≠ 0 := by omega
      have hjpos : 0 < j := by omega
      exact ⟨by simp [hd, hjne, hjpos], by simp [hd, hjne]⟩
    refine mem_trigPolyLE_iff.mpr ⟨d, ContinuousMap.ext fun z => ?_⟩
    induction z using QuotientAddGroup.induction_on with
    | H t =>
      rw [hab t, sum_trigFun_two_pi_coe d n t, hd0]
      refine congrArg _ (Finset.sum_congr rfl fun j hj => ?_)
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      rw [(hdval j hj1).1, (hdval j hj1).2]
      field_simp

/-- **Equation (3.2.16)** of [han2009theoretical]. The evenly spaced nodes of a period are
$$x_j = j h, \qquad h = \frac{2\pi}{2n + 1}, \qquad j = 0, \dots, 2n.$$

The nodes are `trigInterpNode (2 * π) n`, as points of `AddCircle (2 * π)`. -/
theorem equation_3_2_16 (n : ℕ) (j : Fin (2 * n + 1)) :
    trigInterpNode (2 * π) n j
      = (((j : ℕ) * (2 * π / (2 * (n : ℝ) + 1)) : ℝ) : AddCircle (2 * π)) := by
  rw [trigInterpNode, mul_div_assoc]

/-- **Equation (3.2.17)** of [han2009theoretical]. Let $0 \le x_0 < x_1 < \cdots < x_{2n} < 2\pi$
and let $c_0, \dots, c_{2n} \in \mathbb{R}$. Then there is exactly one $p_n \in \mathcal{T}_n$
with
$$p_n(x_j) = c_j, \qquad j = 0, \dots, 2n.$$

The substitution $z = e^{ix}$ of (3.2.15) turns the problem into complex polynomial
interpolation at the distinct points $z_j = e^{ix_j}$. The backbone carries this out once, as
the Haar condition for `trigPolyLE`. -/
theorem equation_3_2_17 {n : ℕ} {x : Fin (2 * n + 1) → ℝ} (hmono : StrictMono x)
    (hmem : ∀ j, x j ∈ Set.Ico 0 (2 * π)) (c : Fin (2 * n + 1) → ℝ) :
    ∃! p : trigPolyLE (2 * π) n,
      ∀ j, (p : C(AddCircle (2 * π), ℝ)) ((x j : ℝ) : AddCircle (2 * π)) = c j := by
  have hmem' : ∀ j, x j ∈ Set.Ico (0 : ℝ) (0 + 2 * π) := by simpa using hmem
  have hinj : Function.Injective fun j => ((x j : ℝ) : AddCircle (2 * π)) := by
    intro i j hij
    exact hmono.injective ((AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem' i) (hmem' j)).mp hij)
  exact isUnisolvent_trigPolyLE (2 * π) hinj c

/-- **Equation (3.2.17)** of [han2009theoretical], at the evenly spaced nodes (3.2.16). For
$f \in C_p(2\pi)$, the trigonometric interpolant $p_n$ = `trigInterpCLM (2 * π) n f` lies in
$\mathcal{T}_n$ and satisfies $p_n(x_j) = f(x_j)$ at the $2n + 1$ evenly spaced nodes $x_j$. -/
theorem equation_3_2_17_equispaced (n : ℕ) (f : C(AddCircle (2 * π), ℝ)) :
    trigInterpCLM (2 * π) n f ∈ trigPolyLE (2 * π) n ∧
      ∀ j, trigInterpCLM (2 * π) n f (trigInterpNode (2 * π) n j)
        = f (trigInterpNode (2 * π) n j) :=
  ⟨trigInterpCLM_mem f, fun j => trigInterpCLM_apply_node f j⟩

/-- **Example 3.2.5** of [han2009theoretical]. The function of (3.2.18),
$$f(x) = e^{\sin x} \sin x,$$
is continuous and $2\pi$-periodic, so it is an element of $C_p(2\pi)$. For every $n \ge 0$ there
is exactly one $p_n \in \mathcal{T}_n$ with $p_n(x_j) = f(x_j)$ at the evenly spaced nodes
(3.2.16), and `trigInterpCLM (2 * π) n f` takes these values.

Table 3.1 of the source, the maximum errors $\|f - p_n\|_\infty$ for $n = 1, \dots, 14$,
consists of computed numbers and is not part of the statement. Each entry is a supremum over the
circle of a transcendental function, so a rigorous value would need verified numerics, which the
project does not have. The source draws nothing from the table beyond the convergence that §3.7
proves. -/
theorem example_3_2_5 (n : ℕ) :
    ∃ f : C(AddCircle (2 * π), ℝ),
      (∀ x : ℝ, f ((x : ℝ) : AddCircle (2 * π)) = Real.exp (Real.sin x) * Real.sin x) ∧
        (∃! p : trigPolyLE (2 * π) n, ∀ j,
            (p : C(AddCircle (2 * π), ℝ)) (trigInterpNode (2 * π) n j)
              = f (trigInterpNode (2 * π) n j)) ∧
        ∀ j, trigInterpCLM (2 * π) n f (trigInterpNode (2 * π) n j)
          = f (trigInterpNode (2 * π) n j) := by
  have hper : Function.Periodic (fun x : ℝ => Real.exp (Real.sin x) * Real.sin x) (2 * π) :=
    fun x => by simp [Real.sin_periodic x]
  refine ⟨⟨hper.lift, continuous_quot_lift _ (by fun_prop)⟩, fun x => hper.lift_coe x, ?_,
    fun j => trigInterpCLM_apply_node _ j⟩
  exact isUnisolvent_trigPolyLE (2 * π) (injective_trigInterpNode (2 * π) n) _

end Trigonometric

end AtkinsonHan.Chapter03
