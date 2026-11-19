/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 10.2: Gaussian integration and interpolation

This module formalizes Section 10.2 of [quarteroni2000numerical]. Let $x_0, \dots, x_n$ be $n + 1$
distinct nodes in $[-1, 1]$ and let $w$ be a weight. The section studies the weighted quadrature
rules $I_{n,w}(f) = \sum_i \alpha_i f(x_i)$ of (10.13) and their degree of exactness $r$ with
respect to $w$, which means that the error $E_{n,w}(p) = I_w(p) - I_{n,w}(p)$ vanishes for every
$p \in \mathbb{P}_r$. The interpolatory weights $\alpha_i = \int l_i w$ give degree of exactness at
least $n$ (10.14). Jacobi's theorem (Theorem 10.1) characterizes degree $n + m$ by the orthogonality
(10.15) of the nodal polynomial $\omega_{n+1}$ to $\mathbb{P}_{m-1}$. The maximal degree is $2n + 1$
(Corollary 10.1), and only the Gauss nodes, the zeros of $p_{n+1}$ (10.16), attain it; their weights
are positive and the nodes are interior.

The Gauss–Lobatto rule (10.17)–(10.18) includes the endpoints and has degree of exactness $2n - 1$;
(10.19) gives its interpolant. Remark 10.2 identifies its interior nodes for a Jacobi weight with
the extremal points of the Jacobi polynomial of degree $n$. Gaussian and Gauss–Lobatto integration
converge for every continuous integrand, and Remark 10.3 maps a rule from $[-1, 1]$ to $[a, b]$. The
proofs specialize the exactness theory of `Numlib.Approximation.Quadrature` and the Gauss–Lobatto
construction of `Numlib.Approximation.GaussLobatto`.

## Main results

* Section 10.2, `QuarteroniSaccoSaleri.Chapter10.isExactOnMeasure_iff_forall_sub_eq_zero`: the
  degree of exactness $r$ with respect to $w$ means $E_{n,w}(p) = 0$ for all $p \in \mathbb{P}_r$.
* Equations (10.13)–(10.14), `QuarteroniSaccoSaleri.Chapter10.equation_10_14`: the weights are
  interpolatory if and only if the degree of exactness is at least $n$, and then the rule is the
  integral of the Lagrange interpolant.
* Theorem 10.1, `QuarteroniSaccoSaleri.Chapter10.theorem_10_1`: Jacobi's characterization of degree
  of exactness $n + m$.
* Corollary 10.1, `QuarteroniSaccoSaleri.Chapter10.corollary_10_1`: the maximal degree of exactness
  of a rule with $n + 1$ distinct nodes is $2n + 1$.
* Equation (10.16), `QuarteroniSaccoSaleri.Chapter10.exists_gauss_nodes`: $p_{n+1}$ has $n + 1$
  distinct real zeros.
* Equation (10.16), `QuarteroniSaccoSaleri.Chapter10.equation_10_16`: a rule has degree of exactness
  $2n + 1$ if and only if its nodes are the zeros of $p_{n+1}$ and its weights are interpolatory.
* Section 10.2, `QuarteroniSaccoSaleri.Chapter10.gauss_weights_pos_nodes_mem_Ioo`: the Gauss weights
  are positive and the Gauss nodes lie in $(-1, 1)$.
* Equations (10.17)–(10.18), `QuarteroniSaccoSaleri.Chapter10.equation_10_18`: the Gauss–Lobatto
  rule exists, with nodes $-1 = \bar x_0, \dots, \bar x_n = 1$, positive weights and degree of
  exactness $2n - 1$.
* Equation (10.19), `QuarteroniSaccoSaleri.Chapter10.equation_10_19`: the Gauss–Lobatto interpolant,
  and the rule as its integral.
* Remark 10.2, `QuarteroniSaccoSaleri.Chapter10.remark_10_2`: for a Jacobi weight, the interior
  Gauss–Lobatto nodes are the zeros of $(J_n^{(\alpha,\beta)})'$.
* Section 10.2, `QuarteroniSaccoSaleri.Chapter10.gauss_tendsto`: Gaussian integration converges for
  every $f \in C^0([-1, 1])$.
* Section 10.2, `QuarteroniSaccoSaleri.Chapter10.gaussLobatto_tendsto`: Gauss–Lobatto integration
  converges for every $f \in C^0([-1, 1])$.
* Remark 10.3, `QuarteroniSaccoSaleri.Chapter10.remark_10_3`: a rule on $[-1, 1]$ mapped affinely to
  $[a, b]$ keeps its degree of exactness.

## Conventions

* A rule with $n + 1$ nodes is a pair `x α : Fin (n + 1) → ℝ` of nodes and weights. The nodes are
  distinct when `Function.Injective x`.
* The weight $w(x)\,dx$ is a measure $\mu$ with `OrthogonalPolynomial.IsWeight μ`. Where the
  interval matters, $\mu$ is carried by $[-1, 1]$, that is, `μ (Icc (-1) 1)ᶜ = 0`.
* The degree of exactness $r$ is `Quadrature.IsExactOnMeasure μ α x r`:
  $\sum_i \alpha_i p(x_i) = \int p \, d\mu$ for every real polynomial $p$ of degree at most $r$.
* The characteristic Lagrange polynomials $l_i$ and the nodal polynomial $\omega_{n+1}$ are
  Mathlib's `Lagrange.basis Finset.univ x i` and `Lagrange.nodal Finset.univ x`, as in Section 8.1.
  The polynomials $\{p_k\}$ are the monic orthogonal family `OrthogonalPolynomial.family μ` of
  Section 10.1.
* The Gauss–Lobatto nodes are an injective enumeration with $\bar x_0 = -1$ and $\bar x_n = 1$, the
  labelling of the book.
* The Jacobi polynomial $J_n^{(\alpha,\beta)}$ of the book is the monic `OrthogonalPolynomial.family
  (OrthogonalPolynomial.jacobiMeasure α β) n`, which has the same zeros and the same extremal
  points.
* A continuous function on $[-1, 1]$ is a function `f : ℝ → ℝ` with `ContinuousOn f (Icc (-1) 1)`.

## Deviations from the source

* **Equations (10.13)–(10.16), Theorem 10.1, and Corollary 10.1** (generalization). The
  exactness definition, interpolation criterion, Jacobi criterion, sharp bound, and Gauss node
  characterization use measure weights in place of the density on $(-1,1)$. These statements
  permit real nodes outside the interval. `gauss_weights_pos_nodes_mem_Ioo` recovers interiority
  and positivity for measure weights supported on $[-1,1]$.
* **Equations (10.17)–(10.19)** (reading). `equation_10_18` makes $n\geq 1$ explicit and states
  exactness through $2n-1$ for its Lobatto rule. The printed discussion also claims maximality
  among rules containing both endpoints. `equation_10_19` extends the identity to any rule whose
  coefficients are integrals of the Lagrange basis polynomials.
* **Section 10.2, convergence of Gaussian integration** (generalization). `gauss_tendsto`
  permits a general measure weight on $[-1,1]$. `gaussLobatto_tendsto` states the result for
  positive rules with interval nodes and the Lobatto exactness bound, without requiring that the
  nodes include the endpoints.
* **Remark 10.2** (typo). The book prints the Jacobi weight as $(1 - x)^\alpha (1 - x)^\beta$. The
  library uses $(1 - x)^\alpha (1 + x)^\beta$. See `QuarteroniSaccoSaleri.Chapter10.remark_10_2`.
* **Remark 10.3** (typo). The book prints the map $\varphi(\xi) = \frac{a + b}{2} \xi + \frac{b -
  a}{2}$ and the factor $\frac{a + b}{2}$. The library uses $\varphi(\xi) = \frac{b - a}{2} \xi +
  \frac{a + b}{2}$ and the factor $\frac{b - a}{2}$. See
  `QuarteroniSaccoSaleri.Chapter10.remark_10_3`.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Quadrature Real Set Filter Topology

namespace QuarteroniSaccoSaleri.Chapter10

variable {μ : Measure ℝ} {n : ℕ}

/-! ### Degree of exactness with respect to a weight, and interpolatory rules (10.13)–(10.14) -/

/-- **Section 10.2** of [quarteroni2000numerical], the degree of exactness with respect to a weight.
Let $\mu$ be a measure, and let a rule (10.13), $I_{n,w}(f) = \sum_i \alpha_i f(x_i)$, have
weights $\alpha_i$ and nodes $x_i$. Then the rule has degree of exactness $r$ with respect to
$\mu$ if and only if the error
$$E_{n,w}(p) = I_w(p) - I_{n,w}(p)$$
vanishes for every $p \in \mathbb{P}_r$.

The left side is `Quadrature.IsExactOnMeasure μ α x r`, the form of the degree of exactness used
in the whole chapter.

**Generalization.** Uses measure integration and permits real nodes on the full line. The
source starts with a weight density and nodes on $[-1,1]$. -/
theorem isExactOnMeasure_iff_forall_sub_eq_zero {m : ℕ} (α x : Fin m → ℝ) (r : ℕ) :
    IsExactOnMeasure μ α x r ↔
      ∀ p : ℝ[X], p.degree ≤ r → (∫ t, p.eval t ∂μ) - ∑ i, α i * p.eval (x i) = 0 :=
  forall₂_congr fun _ _ => by rw [sub_eq_zero, eq_comm]

/-- **Equations (10.13)–(10.14)** of [quarteroni2000numerical]. Let $\mu$ be a weight, and let
$x_0, \dots, x_n$ be distinct nodes. The rule $I_{n,w}(f) = \sum_i \alpha_i f(x_i)$ has degree
of exactness at least $n$ if and only if its weights are
$$\alpha_i = \int_{-1}^1 l_i(x) w(x) \, dx, \qquad i = 0, \dots, n, \tag{10.14}$$
where $l_i$ are the characteristic Lagrange polynomials of the nodes. In this case
$I_{n,w}(f) = \int_{-1}^1 \Pi_n f(x) w(x) \, dx$ for every $f$, where $\Pi_n f$ is the Lagrange
interpolant (8.4) of $f$.

The book states the sufficiency. The converse is the remark of Section 9.1 that a formula on
$n + 1$ distinct nodes that is exact on $\mathbb{P}_n$ is interpolatory. The proof specializes
`Quadrature.isInterpolatoryMeasure_iff_isExactOnMeasure`.

**Generalization.** Uses measure integration and permits real nodes on the full line. The
source starts with a weight density and nodes on $[-1,1]$. -/
theorem equation_10_14 (hw : IsWeight μ) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (α : Fin (n + 1) → ℝ) :
    ((∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ) ↔ IsExactOnMeasure μ α x n) ∧
      ((∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ) → ∀ f : ℝ → ℝ,
        ∑ i, α i * f (x i) =
          ∫ t, (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t ∂μ) :=
  ⟨isInterpolatoryMeasure_iff_isExactOnMeasure hw hx, fun hint f =>
    sum_mul_eq_integral_interpolate hw hint f⟩

/-! ### Theorem 10.1, Corollary 10.1 and the Gauss nodes (10.15)–(10.16) -/

/-- **Theorem 10.1** of [quarteroni2000numerical] (Jacobi). Let $\mu$ be a weight, let $m > 0$, and
let $x_0, \dots, x_n$ be distinct nodes. The quadrature formula (10.13) has degree of exactness
$n + m$ if and only if it is of interpolatory type, that is, its weights are given by (10.14),
and the nodal polynomial $\omega_{n+1}$ (8.6) of the nodes satisfies
$$\int_{-1}^1 \omega_{n+1}(x) p(x) w(x) \, dx = 0 \quad \text{for all } p \in \mathbb{P}_{m-1}.
  \tag{10.15}$$

The proof specializes `Quadrature.isExactOnMeasure_add_iff`.

**Generalization.** Uses measure integration and permits real nodes on the full line. The
source starts with a weight density and nodes on $[-1,1]$. -/
theorem theorem_10_1 (hw : IsWeight μ) {m : ℕ} (hm : 0 < m) {x : Fin (n + 1) → ℝ}
    (hx : Function.Injective x) (α : Fin (n + 1) → ℝ) :
    IsExactOnMeasure μ α x (n + m) ↔
      (∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ) ∧
        ∀ p : ℝ[X], p.degree ≤ ((m - 1 : ℕ) : WithBot ℕ) →
          ∫ t, (Lagrange.nodal Finset.univ x).eval t * p.eval t ∂μ = 0 :=
  isExactOnMeasure_add_iff hw hm hx α

/-- **Corollary 10.1** of [quarteroni2000numerical]. Let $\mu$ be a weight. The maximum degree of
exactness of a quadrature formula (10.13) with $n + 1$ distinct nodes is $2n + 1$.

The maximum is stated with `IsGreatest` over the set of degrees $r$ for which such a rule
exists. No rule with $n + 1$ distinct nodes is exact on $\mathbb{P}_{2n+2}$
(`Quadrature.not_isExactOnMeasure_two_mul_add_two`), and the Gauss rule
(`Quadrature.exists_gauss`) attains $2n + 1$.

**Generalization.** Uses measure integration and permits real nodes on the full line. The
source starts with a weight density and nodes on $[-1,1]$. -/
theorem corollary_10_1 (hw : IsWeight μ) (n : ℕ) :
    IsGreatest {r | ∃ x α : Fin (n + 1) → ℝ, Function.Injective x ∧ IsExactOnMeasure μ α x r}
      (2 * n + 1) := by
  constructor
  · obtain ⟨x, α, hx, -, hexact⟩ := exists_gauss hw (n + 1)
    refine ⟨x, α, hx, isExactOnMeasure_iff_forall_degree_lt.mpr fun p hp => hexact p ?_⟩
    rwa [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
  · rintro r ⟨x, α, -, hexact⟩
    by_contra hlt
    push Not at hlt
    exact not_isExactOnMeasure_two_mul_add_two hw α x (hexact.mono (by omega))

/-- **Equation (10.16)** of [quarteroni2000numerical], existence of the Gauss nodes. Let $\mu$ be a
weight. Then the orthogonal polynomial $p_{n+1}$ has $n + 1$ distinct real zeros
$x_0, \dots, x_n$, the abscissae of (10.16).

The proof specializes `OrthogonalPolynomial.exists_injective_family_eq_prod`.

**Generalization.** Uses measure integration and permits real nodes on the full line. The
source starts with a weight density and nodes on $[-1,1]$. -/
theorem exists_gauss_nodes (hw : IsWeight μ) (n : ℕ) :
    ∃ x : Fin (n + 1) → ℝ, Function.Injective x ∧ ∀ j, (family μ (n + 1)).eval (x j) = 0 := by
  obtain ⟨x, hx, hprod⟩ := exists_injective_family_eq_prod hw (n + 1)
  refine ⟨x, hx, fun j => ?_⟩
  rw [hprod, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

/-- **Equation (10.16)** of [quarteroni2000numerical], the Gauss nodes. Let $\mu$ be a weight, and
let $x_0, \dots, x_n$ be distinct nodes. A rule on these nodes has degree of exactness $2n + 1$,
the maximum of Corollary 10.1, if and only if its nodes are the zeros of $p_{n+1}$,
$$p_{n+1}(x_j) = 0, \qquad j = 0, \dots, n,$$
and its weights are given by (10.14). This rule is the **Gauss quadrature formula**.

The proof specializes `Quadrature.isExactOnMeasure_two_mul_add_one_iff`. Its condition
$\omega_{n+1} = p_{n+1}$ is equivalent, for distinct nodes, to $p_{n+1}(x_j) = 0$ for all $j$
(`Quadrature.nodal_eq_family_of_forall_eval_eq_zero`).

**Generalization.** Uses measure integration and permits real nodes on the full line. The
source starts with a weight density and nodes on $[-1,1]$. -/
theorem equation_10_16 (hw : IsWeight μ) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (α : Fin (n + 1) → ℝ) :
    IsExactOnMeasure μ α x (2 * n + 1) ↔
      (∀ j, (family μ (n + 1)).eval (x j) = 0) ∧
        ∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ := by
  rw [isExactOnMeasure_two_mul_add_one_iff hw hx α]
  refine and_congr_left' ⟨fun h j => ?_, fun h => nodal_eq_family_of_forall_eval_eq_zero μ hx h⟩
  rw [← h]
  exact Lagrange.eval_nodal_at_node (Finset.mem_univ j)

/-- **Section 10.2** of [quarteroni2000numerical], the text after (10.16). Let $\mu$ be a weight
carried by $[-1, 1]$, and let a rule have $n + 1$ distinct nodes $x_i$, weights $\alpha_i$ and
degree of exactness $2n + 1$. Then $\alpha_i > 0$ and $x_i \in (-1, 1)$ for every $i$.

The book refers for this fact to Canuto, Hussaini, Quarteroni and Zang (1988), p. 56. The
positivity follows from exactness on $l_i^2$. The location of the nodes is
`OrthogonalPolynomial.root_family_mem_Ioo`, because the nodes are the zeros of $p_{n+1}$ by
(10.16).

**Generalization.** Uses an arbitrary measure weight carried by $[-1,1]$ in place of a density
on that interval. -/
theorem gauss_weights_pos_nodes_mem_Ioo (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0)
    {x α : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hexact : IsExactOnMeasure μ α x (2 * n + 1)) :
    (∀ i, 0 < α i) ∧ ∀ i, x i ∈ Ioo (-1 : ℝ) 1 :=
  ⟨pos_of_isExactOnMeasure_of_le hw hx (by omega) hexact, fun i =>
    root_family_mem_Ioo hw hsupp (((equation_10_16 hw hx α).mp hexact).1 i)⟩

/-! ### The Gauss–Lobatto formula (10.17)–(10.19) -/

/-- **Equations (10.17)–(10.18)** of [quarteroni2000numerical], the Gauss–Lobatto formula. Let $\mu$
be a weight carried by $[-1, 1]$, and let $n \ge 1$. Consider the polynomial
$$\bar\omega_{n+1} = p_{n+1} + a p_n + b p_{n-1}, \tag{10.17}$$
with the constants $a, b$ chosen so that $\bar\omega_{n+1}(-1) = \bar\omega_{n+1}(1) = 0$. Then
there are nodes $\bar x_0, \dots, \bar x_n$ and weights $\bar\alpha_0, \dots, \bar\alpha_n$ such
that:

* the nodes are distinct, lie in $[-1, 1]$, and satisfy $\bar x_0 = -1$ and $\bar x_n = 1$;
* the nodal polynomial of the nodes is $\bar\omega_{n+1}$ for some $a, b$ with
  $\bar\omega_{n+1}(\pm 1) = 0$;
* every pair $a, b$ with $\bar\omega_{n+1}(\pm 1) = 0$ gives this nodal polynomial, so the two
  conditions determine $\bar\omega_{n+1}$;
* the weights are $\bar\alpha_i = \int_{-1}^1 \bar l_i w \, dx$ as in (10.14), and they are
  positive;
* the formula $I^{GL}_{n,w}(f) = \sum_i \bar\alpha_i f(\bar x_i)$ of (10.18) has degree of
  exactness $2n - 1$.

This is the **Gauss–Lobatto formula** with $n + 1$ nodes.

The proof specializes `Quadrature.exists_gaussLobatto`, with
`Quadrature.lobattoNodal_eq_add_smul` and `Quadrature.eq_lobattoNodal_of_eval_eq_zero` for the
form (10.17) of the nodal polynomial. The polynomial $p_{n-1}$ is `family μ (n - 1)` with
natural subtraction.

**Reading.** Requires $n\geq 1$ for the two endpoint nodes and states exactness through $2n-1$.
The book also claims maximality over rules including the endpoints. -/
theorem equation_10_18 (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0) (hn : 1 ≤ n) :
    ∃ x α : Fin (n + 1) → ℝ, Function.Injective x ∧ x 0 = -1 ∧ x (Fin.last n) = 1 ∧
      (∀ i, x i ∈ Icc (-1 : ℝ) 1) ∧
      (∃ a b : ℝ, Lagrange.nodal Finset.univ x =
          family μ (n + 1) + C a * family μ n + C b * family μ (n - 1) ∧
        (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval (-1) = 0 ∧
        (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval 1 = 0) ∧
      (∀ a b : ℝ, (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval (-1) = 0 →
        (family μ (n + 1) + C a * family μ n + C b * family μ (n - 1)).eval 1 = 0 →
        family μ (n + 1) + C a * family μ n + C b * family μ (n - 1) =
          Lagrange.nodal Finset.univ x) ∧
      (∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ) ∧ (∀ i, 0 < α i) ∧
      IsExactOnMeasure μ α x (2 * n - 1) := by
  obtain ⟨x, α, hxinj, hx0, hxlast, hxmem, hpos, hexact, hnodal, hint⟩ :=
    exists_gaussLobatto hw hsupp hn
  obtain ⟨a, b, hab⟩ := lobattoNodal_eq_add_smul hw hsupp hn
  refine ⟨x, α, hxinj, hx0, hxlast, hxmem, ⟨a, b, hnodal.trans hab, ?_, ?_⟩, ?_, hint, hpos, hexact⟩
  · rw [← hab]
    exact lobattoNodal_eval_neg_one μ n
  · rw [← hab]
    exact lobattoNodal_eval_one μ n
  · intro a' b' h1 h2
    rw [hnodal]
    exact eq_lobattoNodal_of_eval_eq_zero hw hsupp hn h2 h1

/-- **Equation (10.19)** of [quarteroni2000numerical]. Let $\mu$ be a weight, and let a rule have
nodes $\bar x_i$ and the interpolatory weights $\bar\alpha_i = \int \bar l_i w \, dx$. Let
$\Pi^{GL}_{n,w} f$ be the polynomial of degree at most $n$ that interpolates $f$ at the nodes.
Then
$$\Pi^{GL}_{n,w} f(x) = \sum_i f(\bar x_i) \bar l_i(x),$$
and the rule is its integral,
$$I^{GL}_{n,w}(f) = \int_{-1}^1 \Pi^{GL}_{n,w} f(x) w(x) \, dx.$$

The statement holds for any rule with interpolatory weights. The Gauss–Lobatto rule of
`QuarteroniSaccoSaleri.Chapter10.equation_10_18` has such weights.

**Generalization.** The two identities hold for a general measure weight whenever the weights
equal the integrated Lagrange basis polynomials. This includes the Gauss–Lobatto construction. -/
theorem equation_10_19 (hw : IsWeight μ) {x α : Fin (n + 1) → ℝ}
    (hint : ∀ i, α i = ∫ t, (Lagrange.basis Finset.univ x i).eval t ∂μ) (f : ℝ → ℝ) :
    (Lagrange.interpolate Finset.univ x fun i => f (x i)) =
        ∑ i, C (f (x i)) * Lagrange.basis Finset.univ x i ∧
      ∑ i, α i * f (x i) =
        ∫ t, (Lagrange.interpolate Finset.univ x fun i => f (x i)).eval t ∂μ :=
  ⟨Lagrange.interpolate_apply _ _ _, sum_mul_eq_integral_interpolate hw hint f⟩

/-! ### Remark 10.2: The Gauss–Lobatto nodes of a Jacobi weight -/

/-- **Remark 10.2** of [quarteroni2000numerical]. Let $\alpha, \beta > -1$, let $n \ge 1$, and let
$\{J_k\}$ be the monic orthogonal polynomials of the Jacobi weight
$w(x) = (1 - x)^\alpha (1 + x)^\beta$. Let $a, b \in \mathbb{R}$ be such that the polynomial
$\bar\omega_{n+1} = J_{n+1} + a J_n + b J_{n-1}$ vanishes at $-1$ and at $1$, and let
$\bar x_0, \dots, \bar x_n$ be distinct roots of $\bar\omega_{n+1}$. Then a point
$t \in (-1, 1)$ is a node $\bar x_i$ if and only if $J_n'(t) = 0$. So the interior Gauss–Lobatto
nodes are the roots of $(J_n^{(\alpha,\beta)})'$, the extremal points of the Jacobi polynomial
of degree $n$.

**Typo.** The book prints the weight as $(1 - x)^\alpha (1 - x)^\beta$. The intended weight is
$(1 - x)^\alpha (1 + x)^\beta$.

The nodes are described as in (10.17). The proof uses
`Quadrature.derivative_family_jacobiMeasure`: for the monic families, $(J_n^{(\alpha,\beta)})' =
n J_{n-1}^{(\alpha+1,\beta+1)}$, and the Gauss–Lobatto nodal polynomial is
$(x^2 - 1) J_{n-1}^{(\alpha+1,\beta+1)}$. -/
theorem remark_10_2 {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (hn : 1 ≤ n) {a b : ℝ}
    (h1 : (family (jacobiMeasure α β) (n + 1) + C a * family (jacobiMeasure α β) n +
      C b * family (jacobiMeasure α β) (n - 1)).eval (-1) = 0)
    (h2 : (family (jacobiMeasure α β) (n + 1) + C a * family (jacobiMeasure α β) n +
      C b * family (jacobiMeasure α β) (n - 1)).eval 1 = 0)
    {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hroot : ∀ i, (family (jacobiMeasure α β) (n + 1) + C a * family (jacobiMeasure α β) n +
      C b * family (jacobiMeasure α β) (n - 1)).eval (x i) = 0) :
    ∀ t ∈ Ioo (-1 : ℝ) 1,
      (∃ i, x i = t) ↔ (derivative (family (jacobiMeasure α β) n)).eval t = 0 := by
  have hw := isWeight_jacobiMeasure hα hβ
  have hsupp := jacobiMeasure_compl_Icc α β
  have hω := eq_lobattoNodal_of_eval_eq_zero hw hsupp hn h2 h1
  rw [hω] at hroot
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hder := derivative_family_jacobiMeasure hα hβ hn
  rw [← lobattoMeasure_jacobiMeasure] at hder
  intro t ht
  have ht' : t ^ 2 - 1 ≠ 0 := by nlinarith [ht.1, ht.2]
  -- `t` is a node iff `ω̄_{n+1}(t) = 0`
  have hnodal : Lagrange.nodal Finset.univ x = lobattoNodal (jacobiMeasure α β) n :=
    Lagrange.nodal_eq_of_forall_eval_eq_zero hx (lobattoNodal_monic _ _)
      (natDegree_eq_of_degree_eq_some (degree_lobattoNodal _ hn)) hroot
  rw [Lagrange.exists_eq_iff_eval_nodal_eq_zero, hnodal, lobattoNodal, hder, eval_mul, eval_mul,
    eval_sub, eval_pow, eval_X, eval_one, eval_C, mul_eq_zero, mul_eq_zero, or_iff_right ht',
    or_iff_right hnR]

/-! ### Convergence of Gaussian integration -/

/-- **Section 10.2** of [quarteroni2000numerical], the convergence of Gaussian integration. Let
$\mu$ be a weight carried by $[-1, 1]$. For each $k$ let a rule have $k + 1$ distinct nodes
$x_j^{(k)}$, weights $\alpha_j^{(k)}$ and degree of exactness $2k + 1$; these are the Gauss
formulae. Then for every $f \in C^0([-1, 1])$,
$$\lim_{k \to \infty} \left| \int_{-1}^1 f(x) w(x) \, dx - \sum_j \alpha_j^{(k)} f(x_j^{(k)})
  \right| = 0.$$

The book refers for this fact to Atkinson (1989), Chapter 5. The proof uses the Szegő–Pólya
criterion `Quadrature.tendsto_of_isExactOnMeasure`. Its hypotheses hold because the weights are
positive and the nodes are interior
(`QuarteroniSaccoSaleri.Chapter10.gauss_weights_pos_nodes_mem_Ioo`).

**Generalization.** Uses an arbitrary measure weight carried by $[-1,1]$ in place of a density
on that interval. -/
theorem gauss_tendsto (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0)
    {x α : ∀ k : ℕ, Fin (k + 1) → ℝ} (hx : ∀ k, Function.Injective (x k))
    (hexact : ∀ k, IsExactOnMeasure μ (α k) (x k) (2 * k + 1)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto (fun k => |(∫ t, f t ∂μ) - ∑ j, α k j * f (x k j)|) atTop (𝓝 0) := by
  have := hw.isFiniteMeasure
  have h := tendsto_of_isExactOnMeasure hsupp hx
    (fun k i => Ioo_subset_Icc_self ((gauss_weights_pos_nodes_mem_Ioo hw hsupp (hx k)
      (hexact k)).2 i))
    (fun k i => ((gauss_weights_pos_nodes_mem_Ioo hw hsupp (hx k) (hexact k)).1 i).le)
    (tendsto_atTop_atTop.mpr fun N => ⟨N, fun k hk => by omega⟩) hexact hf
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  refine h.congr fun k => ?_
  rw [Real.norm_eq_abs, abs_sub_comm]

/-- **Section 10.2** of [quarteroni2000numerical], "a similar result also holds for Gauss–Lobatto
integration". Let $\mu$ be a weight carried by $[-1, 1]$. For each $n \ge 1$ let a rule have
$n + 1$ distinct nodes in $[-1, 1]$, positive weights and degree of exactness $2n - 1$, as
`QuarteroniSaccoSaleri.Chapter10.equation_10_18` provides. Then for every $f \in C^0([-1, 1])$,
$$\lim_{n \to \infty} \left| \int_{-1}^1 f(x) w(x) \, dx - \sum_j \bar\alpha_j^{(n)} f(\bar
  x_j^{(n)}) \right| = 0.$$

The sequence of rules is indexed by $k = n - 1 \ge 0$, so the rule of index $k$ has $k + 2$
nodes and degree of exactness $2(k + 1) - 1$.

**Generalization.** Uses positive weights, interval nodes and exactness through $2n-1$ for
$n+1$ nodes. The hypotheses permit rules other than those that include both endpoints. -/
theorem gaussLobatto_tendsto (hw : IsWeight μ) (hsupp : μ (Icc (-1 : ℝ) 1)ᶜ = 0)
    {x α : ∀ k : ℕ, Fin (k + 2) → ℝ} (hx : ∀ k, Function.Injective (x k))
    (hmem : ∀ k i, x k i ∈ Icc (-1 : ℝ) 1) (hα : ∀ k i, 0 < α k i)
    (hexact : ∀ k, IsExactOnMeasure μ (α k) (x k) (2 * (k + 1) - 1)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto (fun k => |(∫ t, f t ∂μ) - ∑ j, α k j * f (x k j)|) atTop (𝓝 0) := by
  have := hw.isFiniteMeasure
  have h := tendsto_of_isExactOnMeasure hsupp hx hmem (fun k i => (hα k i).le)
    (tendsto_atTop_atTop.mpr fun N => ⟨N, fun k hk => by omega⟩) hexact hf
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  refine h.congr fun k => ?_
  rw [Real.norm_eq_abs, abs_sub_comm]

/-! ### Remark 10.3: Integration over an arbitrary interval -/

/-- **Remark 10.3** of [quarteroni2000numerical] (integration over an arbitrary interval). Let
$a < b$, and let a quadrature formula on $[-1, 1]$ with nodes $\xi_j$ and coefficients $\beta_j$
be exact for the Lebesgue measure on all polynomials of degree at most $r$. Let $\varphi(\xi) =
\frac{b - a}{2} \xi + \frac{a + b}{2}$ be the affine map of $[-1, 1]$ onto $[a, b]$. Then for
every $f$
$$\int_a^b f(x) \, dx = \frac{b - a}{2} \int_{-1}^1 (f \circ \varphi)(\xi) \, d\xi,$$
and the formula with nodes $x_j = \varphi(\xi_j)$ and weights
$\alpha_j = \frac{b - a}{2} \beta_j$ has degree of exactness $r$ on $[a, b]$.

**Typo.** The book prints the map as $\varphi(\xi) = \frac{a + b}{2} \xi + \frac{b - a}{2}$ and
the factor as $\frac{a + b}{2}$. The printed map does not send $[-1, 1]$ onto $[a, b]$; both are
read as here.

The integrals are interval integrals. The proof specializes
`Quadrature.isExactOnMeasure_volume_Icc_of_affine`. -/
theorem remark_10_3 {a b : ℝ} (hab : a < b) {m : ℕ} {ξ β : Fin m → ℝ} {r : ℕ}
    (h : ∀ p : ℝ[X], p.degree ≤ r → ∑ j, p.eval (ξ j) * β j = ∫ t in (-1 : ℝ)..1, p.eval t) :
    (∀ f : ℝ → ℝ, ∫ t in a..b, f t =
        (b - a) / 2 * ∫ t in (-1 : ℝ)..1, f ((b - a) / 2 * t + (a + b) / 2)) ∧
      ∀ q : ℝ[X], q.degree ≤ r →
        ∑ j, q.eval ((b - a) / 2 * ξ j + (a + b) / 2) * ((b - a) / 2 * β j) =
          ∫ t in a..b, q.eval t := by
  have hIcc : ∀ (c d : ℝ) (g : ℝ → ℝ), c ≤ d → ∫ t in Icc c d, g t = ∫ t in c..d, g t := by
    intro c d g hcd
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
  constructor
  · intro f
    rw [← smul_eq_mul, intervalIntegral.smul_integral_comp_mul_add,
      show (b - a) / 2 * (-1) + (a + b) / 2 = a by ring,
      show (b - a) / 2 * 1 + (a + b) / 2 = b by ring]
  · have h' : IsExactOnMeasure (volume.restrict (Icc (-1 : ℝ) 1)) β ξ r := fun p hp => by
      rw [hIcc _ _ _ (by norm_num), ← h p hp]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    intro q hq
    have := isExactOnMeasure_volume_Icc_of_affine hab h' q hq
    rw [hIcc _ _ _ hab.le] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end QuarteroniSaccoSaleri.Chapter10
