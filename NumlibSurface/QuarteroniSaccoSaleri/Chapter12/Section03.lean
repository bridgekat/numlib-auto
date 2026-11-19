/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.OrthogonalPolynomial.LegendreBounds
import NumlibSurface.QuarteroniSaccoSaleri.Chapter12.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 12.3: The Spectral Collocation Method

This module formalizes Section 12.3 of [quarteroni2000numerical]. The boundary value problem
$Lu = -u'' = f$ is set on $(-1, 1)$ and discretized by collocation. The approximation $u_n$ is
sought in the space $\mathbb{P}_n^0$ of polynomials of degree at most $n$ that vanish at both
endpoints, and the equation $L_n u_n(x_j) = f(x_j)$ is imposed at the $n - 1$ interior
Legendre–Gauss–Lobatto nodes (12.36). Here $L_n v = L(I_n v)$ applies the differential operator to
the interpolant at all $n + 1$ nodes, so $L_n v = Lv$ on $\mathbb{P}_n$. With the discrete scalar
product $(u, v)_n = \sum_{j=0}^n u(x_j) v(x_j) w_j$ of the Gauss–Lobatto weights (12.37), the
collocation problem is equivalent to the discrete weak form $(L_n u_n, v_n)_n = (f, v_n)_n$ for all
$v_n \in \mathbb{P}_n^0$ (12.38). Since the quadrature is exact on $\mathbb{P}_{2n-1}$, the energy
$(L_n v_n, v_n)_n$ equals $\|v_n'\|_{L^2(-1, 1)}^2$, and this gives the stability estimate after
(12.38) and the uniqueness of the collocation solution.

The proofs specialize the Gauss–Lobatto quadrature of `Numlib.Approximation.GaussLobatto` and the
closed-form Gauss–Lobatto weights of `Numlib.Approximation.OrthogonalPolynomial.LegendreBounds`.

## Main definitions

* Section 12.3, `QuarteroniSaccoSaleri.Chapter12.IsLegendreLobatto`: $x$ and $w$ are the $n + 1$
  Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$;
  `QuarteroniSaccoSaleri.Chapter12.exists_isLegendreLobatto` shows that they exist.
* Equation (12.36), `QuarteroniSaccoSaleri.Chapter12.equation_12_36`: the spectral collocation
  problem.
* Equation (12.37), `QuarteroniSaccoSaleri.Chapter12.equation_12_37`: the discrete scalar product.

## Main results

* Equation (12.37), `QuarteroniSaccoSaleri.Chapter12.equation_12_37_exact`: the discrete scalar
  product equals the integral on $\mathbb{P}_{2n-1}$;
  `QuarteroniSaccoSaleri.Chapter12.equation_12_37_self_nonneg` shows that it is a positive form.
* Equation (12.37), `QuarteroniSaccoSaleri.Chapter12.equation_12_37_sum_weights`,
  `QuarteroniSaccoSaleri.Chapter12.equation_12_37_le_sup` and
  `QuarteroniSaccoSaleri.Chapter12.equation_12_37_inner_mul_le`: the weights sum to $2$, hence
  $\|f\|_n \le \sqrt{2} \|f\|_\infty$, and the Cauchy–Schwarz inequality for $(\cdot, \cdot)_n$.
* Equation (12.38), `QuarteroniSaccoSaleri.Chapter12.equation_12_38`: the collocation problem
  (12.36) is the discrete weak form (12.38).
* Section 12.3, `QuarteroniSaccoSaleri.Chapter12.equation_12_38_energy`:
  $(L_n v, v)_n = \|v'\|_{L^2(-1, 1)}^2$ for $v \in \mathbb{P}_n^0$.
* Exercise 12.8, `QuarteroniSaccoSaleri.Chapter12.exercise_12_8`: Young's inequality
  $ab \le \varepsilon a^2 + b^2/(4\varepsilon)$ (12.40).
* Section 12.3, `QuarteroniSaccoSaleri.Chapter12.equation_12_37_norm_equiv`: the norm equivalence
  $\|v_n\|_{L^2} \le \|v_n\|_n \le \sqrt{3} \|v_n\|_{L^2}$ on $\mathbb{P}_n$.
* Section 12.3, `QuarteroniSaccoSaleri.Chapter12.equation_12_38_stability` and
  `QuarteroniSaccoSaleri.Chapter12.equation_12_36_unique`: the stability estimate
  $\|u_n'\|_{L^2} \le \sqrt{6} C_P \|f\|_\infty$ after (12.38), and the uniqueness of the
  collocation solution.

## Conventions

* Polynomials are `Polynomial ℝ`, and $Lv$ is `-(derivative (derivative v))`. A polynomial $p$ lies
  in $\mathbb{P}_n^0$ when `p.natDegree ≤ n`, `p.eval (-1) = 0` and `p.eval 1 = 0`.

## Deviations from the source

* **Equations (12.36)–(12.38)** (reading). `IsLegendreLobatto` describes the Lobatto rule by
  positivity, endpoints and exactness. `equation_12_37` is a total finite sum for arbitrary real
  data. The weak form and collocation statement use the corrected endpoints $\pm1$.
* **Section 12.3, stability and uniqueness** (reading). `poincare_poly` specializes (12.16) with
  an explicit constant and needs only the left endpoint condition. `equation_12_36_unique`
  proves equality of any two solutions. The source also asserts existence.
* **Equation (12.36)** (typo). The source writes the conditions of $\mathbb{P}_n^0$ as
  $p(0) = p(1) = 0$, although the problem is posed on $(-1, 1)$; the conditions are $p(\pm 1) = 0$.
  See `QuarteroniSaccoSaleri.Chapter12.equation_12_36`.
* **The stability estimate after (12.38)** (generalization). The source bounds by $\|f\|_\infty$; a
  bound $M$ on the values of $f$ at the nodes is enough. See
  `QuarteroniSaccoSaleri.Chapter12.equation_12_38_stability`.

## Not formalized

* **Theorem 12.2**: for $f \in H^s(-1, 1)$ with $s \ge 1$, the collocation solution satisfies
  $\|u' - u_n'\|_{L^2(-1, 1)} \le C n^{-s} (\|f\|_{H^s(-1, 1)} + \|u\|_{H^{s+1}(-1, 1)})$ with $C$
  independent of $n$. The source sketches the proof and quotes the two estimates it rests on from
  Canuto, Hussaini, Quarteroni and Zang (1988): the error $|E(f, v_n)| \le C n^{-s} \|f\|_{H^s}
  \|v_n\|_{L^2}$ of the Gauss–Lobatto quadrature, (10.36)–(10.37), and the error
  $\|u - I_n u\|_{H^1} \le C n^{1-s} \|u\|_{H^s}$ of the interpolation at the Gauss–Lobatto nodes,
  (10.22) and (10.71). Both estimates are not formalized in Chapter 10 either;
  `NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section03` lists what they need: weighted Sobolev
  seminorms on $(-1, 1)$, the decay $|\hat{f}_k| \le C k^{-s} \|f\|_{H^s}$ of the Legendre
  coefficients, and the aliasing step from the projection to the interpolant. The other steps of the
  proof are in this module: `QuarteroniSaccoSaleri.Chapter12.equation_12_38`,
  `QuarteroniSaccoSaleri.Chapter12.exercise_12_8`,
  `QuarteroniSaccoSaleri.Chapter12.equation_12_37_exact`,
  `QuarteroniSaccoSaleri.Chapter12.equation_12_37_norm_equiv` and
  `QuarteroniSaccoSaleri.Chapter12.poincare_poly`. The constant $C$ of the source is not explicit,
  so a faithful statement must quantify one $C$ over all $n$, and no weaker form is available
  without the two estimates.
-/

open MeasureTheory Polynomial Set

open scoped Nat

namespace QuarteroniSaccoSaleri.Chapter12

/-! ### The Legendre–Gauss–Lobatto rule -/

/-- **Section 12.3** of [quarteroni2000numerical], the Legendre–Gauss–Lobatto nodes and weights of
Section 10.4. Nodes $x_0, \dots, x_n$ and weights $w_0, \dots, w_n$ are the
**Legendre–Gauss–Lobatto nodes and weights** of $[-1, 1]$ if the nodes are distinct, $x_0 = -1$,
$x_n = 1$, every node lies in $[-1, 1]$, every weight is positive, and
$$\sum_{j=0}^n w_j \, p(x_j) = \int_{-1}^1 p(x)\, dx \qquad \text{for every polynomial } p
  \text{ of degree at most } 2n - 1.$$

The structure is a bundle of hypotheses; it does not fix the nodes by a formula. The exactness
is `Quadrature.IsExactOnMeasure` for `OrthogonalPolynomial.legendreMeasure`, the Lebesgue
measure on $(-1, 1)$.

**Reading.** Uses an exactness/positivity predicate instead of explicit derivative-root and weight
formulas.
-/
structure IsLegendreLobatto (n : ℕ) (x w : Fin (n + 1) → ℝ) : Prop where
  /-- The nodes are distinct. -/
  injective : Function.Injective x
  /-- The first node is the left endpoint: $x_0 = -1$. -/
  first : x 0 = -1
  /-- The last node is the right endpoint: $x_n = 1$. -/
  last : x (Fin.last n) = 1
  /-- Every node lies in $[-1, 1]$. -/
  mem : ∀ i, x i ∈ Icc (-1 : ℝ) 1
  /-- Every weight is positive: $w_j > 0$. -/
  weight_pos : ∀ i, 0 < w i
  /-- The rule integrates every polynomial of degree at most $2n - 1$ exactly. -/
  exact : Quadrature.IsExactOnMeasure OrthogonalPolynomial.legendreMeasure w x (2 * n - 1)

/-- **Section 12.3** of [quarteroni2000numerical], existence of the Legendre–Gauss–Lobatto rule of
Section 10.4. For every $n \ge 1$ there are nodes and weights $x, w \in \mathbb{R}^{n+1}$ that
are Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$.

The proof specializes `Quadrature.exists_gaussLobatto` to the Legendre weight. -/
theorem exists_isLegendreLobatto {n : ℕ} (hn : 1 ≤ n) :
    ∃ x w : Fin (n + 1) → ℝ, IsLegendreLobatto n x w := by
  have hsupp : OrthogonalPolynomial.legendreMeasure (Icc (-1 : ℝ) 1)ᶜ = 0 := by
    have hempty : (Icc (-1 : ℝ) 1)ᶜ ∩ Ioo (-1 : ℝ) 1 = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨ht1, ht2⟩
      exact ht1 ⟨ht2.1.le, ht2.2.le⟩
    rw [OrthogonalPolynomial.legendreMeasure, Measure.restrict_apply' measurableSet_Ioo, hempty,
      measure_empty]
  obtain ⟨x, w, hinj, hfirst, hlast, hmem, hwpos, hexact, -, -⟩ :=
    Quadrature.exists_gaussLobatto OrthogonalPolynomial.isWeight_legendreMeasure hsupp hn
  exact ⟨x, w, ⟨hinj, hfirst, hlast, hmem, hwpos, hexact⟩⟩

/-! ### The collocation problem (12.36) and the discrete scalar product (12.37) -/

/-- **Equation (12.36)** of [quarteroni2000numerical] (spectral collocation problem). Let
$x_0, \dots, x_n$ be nodes and $f : \mathbb{R} \to \mathbb{R}$. A polynomial $u_n$ **solves the
collocation problem** if $u_n \in \mathbb{P}_n^0$, that is, $\deg u_n \le n$ and
$u_n(-1) = u_n(1) = 0$, and
$$-u_n''(x_j) = f(x_j), \qquad j = 1, \dots, n - 1.$$

**Typo.** The source writes the conditions of $\mathbb{P}_n^0$ as $p(0) = p(1) = 0$, although
the problem is posed on $(-1, 1)$. The conditions here are $p(\pm 1) = 0$, which the nodes and
the rest of the section use.

The source writes the equation as $L_n u_n(x_j) = f(x_j)$ with $L = -d^2/dx^2$ and
$L_n v = L(I_n v)$. On $\mathbb{P}_n$ the interpolant $I_n v$ is $v$, so $L_n u_n = -u_n''$.

**Reading.** Uses zero values at $-1,1$. The description of $\mathbb P_n^0$ following (12.36)
prints $0,1$. -/
def equation_12_36 (n : ℕ) (x : Fin (n + 1) → ℝ) (f : ℝ → ℝ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n ∧ p.eval (-1) = 0 ∧ p.eval 1 = 0 ∧
    ∀ j : Fin (n + 1), j ≠ 0 → j ≠ Fin.last n →
      -(derivative (derivative p)).eval (x j) = f (x j)

/-- **Equation (12.37)** of [quarteroni2000numerical]. For nodes $x_0, \dots, x_n$ and weights
$w_0, \dots, w_n$, the **discrete scalar product** of $u, v : \mathbb{R} \to \mathbb{R}$ is
$$(u, v)_n = \sum_{j=0}^n u(x_j) v(x_j) w_j.$$

The definition is `Quadrature.discreteInner`.

**Generalization.** The finite expression is defined without requiring Lobatto nodes or
positive weights. -/
noncomputable def equation_12_37 (n : ℕ) (x w : Fin (n + 1) → ℝ) (u v : ℝ → ℝ) : ℝ :=
  Quadrature.discreteInner w x u v

/-- **Equation (12.37)** of [quarteroni2000numerical], unfolded:
$(u, v)_n = \sum_{j=0}^n u(x_j) v(x_j) w_j$.

**Generalization.** The finite expression is defined without requiring Lobatto nodes or
positive weights. -/
theorem equation_12_37_eq (n : ℕ) (x w : Fin (n + 1) → ℝ) (u v : ℝ → ℝ) :
    equation_12_37 n x w u v = ∑ j, u (x j) * v (x j) * w j := by
  simp only [equation_12_37, Quadrature.discreteInner]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Equation (12.37)** of [quarteroni2000numerical], exactness. Let $x$ and $w$ be the
Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$, and let $P$ and $Q$ be polynomials with
$\deg(PQ) \le 2n - 1$. Then
$$(P, Q)_n = \int_{-1}^1 P(t) Q(t)\, dt.$$

This is the exactness of the Gauss–Lobatto rule of Sections 10.2 and 10.4. -/
theorem equation_12_37_exact {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : IsLegendreLobatto n x w)
    {P Q : ℝ[X]} (hPQ : (P * Q).degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ)) :
    equation_12_37 n x w (fun t => P.eval t) (fun t => Q.eval t)
      = ∫ t in (-1 : ℝ)..1, P.eval t * Q.eval t := by
  have h := hx.exact (P * Q) hPQ
  rw [OrthogonalPolynomial.integral_legendreMeasure] at h
  have hQ : (∫ t in (-1 : ℝ)..1, P.eval t * Q.eval t)
      = ∫ t in (-1 : ℝ)..1, (P * Q).eval t :=
    intervalIntegral.integral_congr fun t _ => by rw [eval_mul]
  simp only [equation_12_37, Quadrature.discreteInner]
  rw [hQ, ← h]
  exact Finset.sum_congr rfl fun j _ => by rw [eval_mul]; ring

/-- **Equation (12.37)** of [quarteroni2000numerical], positivity. If $x$ and $w$ are the
Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$, then $(v, v)_n \ge 0$ for every
$v : \mathbb{R} \to \mathbb{R}$. -/
theorem equation_12_37_self_nonneg {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : IsLegendreLobatto n x w)
    (v : ℝ → ℝ) : 0 ≤ equation_12_37 n x w v v := by
  simp only [equation_12_37, Quadrature.discreteInner]
  refine Finset.sum_nonneg fun j _ => ?_
  have hw := (hx.weight_pos j).le
  nlinarith [sq_nonneg (v (x j))]

/-- **Equation (12.37)** of [quarteroni2000numerical], the sum of the weights. If $x$ and $w$ are
the Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$, then $\sum_{j=0}^n w_j = 2$, the
length of the interval, because the rule is exact on the constants. -/
theorem equation_12_37_sum_weights {n : ℕ} {x w : Fin (n + 1) → ℝ}
    (hx : IsLegendreLobatto n x w) : ∑ j, w j = 2 := by
  have hdeg : (1 : ℝ[X]).degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) := by
    rw [degree_one]
    exact_mod_cast Nat.zero_le _
  have h := hx.exact 1 hdeg
  rw [OrthogonalPolynomial.integral_legendreMeasure] at h
  simp only [eval_one, mul_one] at h
  rw [h]
  norm_num

/-- **Equation (12.37)** of [quarteroni2000numerical], the bound
$\|f\|_n \le \sqrt{2} \|f\|_\infty$. Let $x$ and $w$ be the Legendre–Gauss–Lobatto nodes and
weights of $[-1, 1]$, and let $|f(x_j)| \le M$ for $j = 0, \dots, n$. Then
$$(f, f)_n \le 2M^2.$$

This is the first of the two estimates that the stability bound after (12.38) uses.

**Generalization.** A bound on the finitely many nodal values suffices. -/
theorem equation_12_37_le_sup {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : IsLegendreLobatto n x w)
    {f : ℝ → ℝ} {M : ℝ} (hM : ∀ j, |f (x j)| ≤ M) :
    equation_12_37 n x w f f ≤ 2 * M ^ 2 := by
  have hsum := equation_12_37_sum_weights hx
  have hle : ∀ j : Fin (n + 1), f (x j) * f (x j) * w j ≤ M ^ 2 * w j := by
    intro j
    have hw := (hx.weight_pos j).le
    have hsq : f (x j) * f (x j) ≤ M ^ 2 := by
      have := abs_nonneg (f (x j))
      nlinarith [hM j, sq_abs (f (x j))]
    exact mul_le_mul_of_nonneg_right hsq hw
  calc equation_12_37 n x w f f = ∑ j, f (x j) * f (x j) * w j := equation_12_37_eq n x w f f
    _ ≤ ∑ j, M ^ 2 * w j := Finset.sum_le_sum fun j _ => hle j
    _ = M ^ 2 * ∑ j, w j := by rw [Finset.mul_sum]
    _ = 2 * M ^ 2 := by rw [hsum]; ring

/-- **Equation (12.37)** of [quarteroni2000numerical], the Cauchy–Schwarz inequality. If $x$ and $w$
are the Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$, then for all
$u, v : \mathbb{R} \to \mathbb{R}$
$$(u, v)_n^2 \le (u, u)_n \, (v, v)_n.$$

This is the step $(f, v_n)_n \le \|f\|_n \|v_n\|_n$ of the stability estimate after (12.38). -/
theorem equation_12_37_inner_mul_le {n : ℕ} {x w : Fin (n + 1) → ℝ}
    (hx : IsLegendreLobatto n x w) (u v : ℝ → ℝ) :
    equation_12_37 n x w u v ^ 2
      ≤ equation_12_37 n x w u u * equation_12_37 n x w v v := by
  have hw : ∀ j : Fin (n + 1), (0 : ℝ) ≤ w j := fun j => (hx.weight_pos j).le
  have key := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin (n + 1)))
    (r := fun j => u (x j) * v (x j) * w j) (f := fun j => u (x j) * u (x j) * w j)
    (g := fun j => v (x j) * v (x j) * w j)
    (fun j _ => by nlinarith [hw j, sq_nonneg (u (x j))])
    (fun j _ => by nlinarith [hw j, sq_nonneg (v (x j))])
    (fun j _ => by nlinarith [hw j, sq_nonneg (u (x j) * v (x j) * w j)])
  rw [equation_12_37_eq, equation_12_37_eq, equation_12_37_eq]
  exact key

/-! ### The discrete weak form (12.38) -/

/-- **Equation (12.38)** of [quarteroni2000numerical] (discrete weak form). Let $x$ and $w$ be the
Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$, let $f : \mathbb{R} \to \mathbb{R}$, and
let $p$ be a polynomial. Then $p$ solves the collocation problem (12.36) if and only if
$p \in \mathbb{P}_n^0$ and
$$(-p'', q)_n = (f, q)_n \qquad \text{for every } q \in \mathbb{P}_n^0.$$

In the forward direction, both sides are sums over the nodes; the endpoint terms vanish because
$q(\pm 1) = 0$, and the interior terms agree by the collocation equations. In the backward
direction, one tests with the Lagrange basis polynomial of an interior node and divides by its
positive weight.

**Reading.** Uses zero values at $-1,1$. The description of $\mathbb P_n^0$ following (12.36)
prints $0,1$. -/
theorem equation_12_38 {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : IsLegendreLobatto n x w) (f : ℝ → ℝ)
    (p : ℝ[X]) :
    equation_12_36 n x f p ↔ p.natDegree ≤ n ∧ p.eval (-1) = 0 ∧ p.eval 1 = 0 ∧
      ∀ q : ℝ[X], q.natDegree ≤ n → q.eval (-1) = 0 → q.eval 1 = 0 →
        equation_12_37 n x w (fun t => -(derivative (derivative p)).eval t) (fun t => q.eval t)
          = equation_12_37 n x w f (fun t => q.eval t) := by
  classical
  constructor
  · rintro ⟨hdeg, hm1, h1, hcoll⟩
    refine ⟨hdeg, hm1, h1, fun q _ hqm1 hq1 => ?_⟩
    simp only [equation_12_37, Quadrature.discreteInner]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj0 : j = 0
    · rw [hj0, hx.first, hqm1]
      ring
    by_cases hjn : j = Fin.last n
    · rw [hjn, hx.last, hq1]
      ring
    rw [hcoll j hj0 hjn]
  · rintro ⟨hdeg, hm1, h1, hweak⟩
    refine ⟨hdeg, hm1, h1, fun j hj0 hjn => ?_⟩
    set q := Lagrange.basis Finset.univ x j with hq
    have hqdeg : q.natDegree ≤ n := by
      rw [natDegree_le_iff_degree_le, hq,
        Lagrange.degree_basis hx.injective.injOn (Finset.mem_univ j)]
      simp
    have hqself : q.eval (x j) = 1 :=
      Lagrange.eval_basis_self hx.injective.injOn (Finset.mem_univ j)
    have hqne : ∀ k : Fin (n + 1), k ≠ j → q.eval (x k) = 0 := fun k hk =>
      Lagrange.eval_basis_of_ne (Ne.symm hk) (Finset.mem_univ k)
    have hqm1 : q.eval (-1) = 0 := by
      rw [← hx.first]
      exact hqne 0 (Ne.symm hj0)
    have hq1 : q.eval 1 = 0 := by
      rw [← hx.last]
      exact hqne (Fin.last n) (Ne.symm hjn)
    have hkey := hweak q hqdeg hqm1 hq1
    simp only [equation_12_37, Quadrature.discreteInner] at hkey
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j] at hkey
    · rw [hqself, mul_one, mul_one] at hkey
      exact mul_left_cancel₀ (hx.weight_pos j).ne' hkey
    · intro k _ hkj
      rw [hqne k hkj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
    · intro k _ hkj
      rw [hqne k hkj, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h

/-- **Section 12.3** of [quarteroni2000numerical], the energy identity. Let $x$ and $w$ be the
Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$, and let $v \in \mathbb{P}_n^0$. Then
$$(L_n v, v)_n = (-v'', v)_n = \int_{-1}^1 v'(t)^2\, dt = \|v'\|_{L^2(-1, 1)}^2.$$

The discrete scalar product is exact on $v'' v \in \mathbb{P}_{2n-2}$, so
$(L_n v, v)_n = (Lv, v)$, and the integration by parts has no boundary terms because $v$
vanishes at both endpoints. This coercivity makes the collocation problem uniquely solvable and
stable. -/
theorem equation_12_38_energy {n : ℕ} {x w : Fin (n + 1) → ℝ} (hx : IsLegendreLobatto n x w)
    {v : ℝ[X]} (hdeg : v.natDegree ≤ n) (hm1 : v.eval (-1) = 0) (h1 : v.eval 1 = 0) :
    equation_12_37 n x w (fun t => -(derivative (derivative v)).eval t) (fun t => v.eval t)
      = ∫ t in (-1 : ℝ)..1, (derivative v).eval t ^ 2 := by
  -- the quadrature is exact on the product, whose degree is at most `2n - 2`
  have hprod : ((-derivative (derivative v)) * v).degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) := by
    rw [← natDegree_le_iff_degree_le]
    have d1 := natDegree_derivative_le v
    have d2 := natDegree_derivative_le (derivative v)
    have hm := natDegree_mul_le (p := -derivative (derivative v)) (q := v)
    rw [natDegree_neg] at hm
    omega
  have hex := hx.exact _ hprod
  rw [OrthogonalPolynomial.integral_legendreMeasure] at hex
  have hlhs : equation_12_37 n x w (fun t => -(derivative (derivative v)).eval t)
      (fun t => v.eval t) = ∑ j, w j * ((-derivative (derivative v)) * v).eval (x j) := by
    simp only [equation_12_37, Quadrature.discreteInner, eval_mul, eval_neg]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t => (derivative v).eval t) (u' := fun t => (derivative (derivative v)).eval t)
    (v := fun t => v.eval t) (v' := fun t => (derivative v).eval t) (a := (-1 : ℝ)) (b := 1)
    (fun t _ => (derivative v).hasDerivAt t) (fun t _ => v.hasDerivAt t)
    ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)
  rw [h1, hm1, mul_zero, mul_zero, sub_zero, zero_sub] at hibp
  have e1 : (∫ t in (-1 : ℝ)..1, ((-derivative (derivative v)) * v).eval t)
      = -∫ t in (-1 : ℝ)..1, (derivative (derivative v)).eval t * v.eval t := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [eval_mul, eval_neg]
    ring
  have e2 : (∫ t in (-1 : ℝ)..1, (derivative v).eval t ^ 2)
      = ∫ t in (-1 : ℝ)..1, (derivative v).eval t * (derivative v).eval t :=
    intervalIntegral.integral_congr fun t _ => by rw [sq]
  rw [hlhs, hex, e1, e2, hibp]

/-! ### Young's inequality -/

/-- **Exercise 12.8** of [quarteroni2000numerical] (Young's inequality, (12.40)). For every
$\varepsilon > 0$ and all $a, b \in \mathbb{R}$,
$$ab \le \varepsilon a^2 + \frac{b^2}{4\varepsilon}.$$

The source uses it in the proofs of Theorem 12.2 and Theorem 12.4. -/
theorem exercise_12_8 {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    a * b ≤ ε * a ^ 2 + b ^ 2 / (4 * ε) := by
  rw [← sub_nonneg]
  have h : ε * a ^ 2 + b ^ 2 / (4 * ε) - a * b = (2 * ε * a - b) ^ 2 / (4 * ε) := by
    field_simp
    ring
  rw [h]
  positivity

/-! ### The stability estimate after (12.38) -/

/-- The Legendre–Gauss–Lobatto rule is interpolatory and has the Lobatto nodal polynomial; these are
the two facts that the closed-form weights in
`QuarteroniSaccoSaleri.Chapter12.equation_12_37_norm_equiv` need. Let $n \ge 1$, and let $x$ and
$w$ be the Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$. Then the rule is interpolatory
for the Legendre weight, and the nodal polynomial $\prod_{j=0}^n (X - x_j)$ is the Lobatto nodal
polynomial `Quadrature.lobattoNodal` of degree $n + 1$.

The proof uses the uniqueness of the Gauss–Lobatto rule,
`Quadrature.nodal_eq_lobattoNodal_of_isExactOnMeasure`.

**Reading.** Characterizes the rule by its endpoints, interval membership, positivity and
exactness. The source refers to the explicit Legendre–Lobatto construction from Section 10.4. -/
theorem IsLegendreLobatto.isInterpolatoryMeasure_and_nodal_eq {n : ℕ} (hn : 1 ≤ n)
    {x w : Fin (n + 1) → ℝ} (hx : IsLegendreLobatto n x w) :
    Quadrature.IsInterpolatoryMeasure OrthogonalPolynomial.legendreMeasure w x ∧
      Lagrange.nodal Finset.univ x =
        Quadrature.lobattoNodal OrthogonalPolynomial.legendreMeasure n :=
  ⟨Quadrature.isInterpolatoryMeasure_of_isExactOnMeasure_two_mul_sub_one
      OrthogonalPolynomial.isWeight_legendreMeasure hn hx.injective hx.exact,
    Quadrature.nodal_eq_lobattoNodal_of_isExactOnMeasure
      OrthogonalPolynomial.isWeight_legendreMeasure OrthogonalPolynomial.legendreMeasure_compl_Icc
      hn hx.injective ⟨Fin.last n, hx.last⟩ ⟨0, hx.first⟩ hx.exact⟩

/-- **Section 12.3** of [quarteroni2000numerical], the norm equivalence on $\mathbb{P}_n$. Let
$n \ge 1$, let $x$ and $w$ be the Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$, and let
$v$ be a polynomial of degree at most $n$. Then
$$\int_{-1}^1 v(t)^2\, dt \le (v, v)_n \le 3 \int_{-1}^1 v(t)^2\, dt.$$
That is, $\|v\|_{L^2(-1, 1)} \le \|v\|_n \le \sqrt{3} \|v\|_{L^2(-1, 1)}$.

The source quotes this equivalence from Canuto, Hussaini, Quarteroni and Zang (1988), p. 286.
The proof specializes `Quadrature.integral_sq_le_discreteInner_self_legendre` and
`Quadrature.discreteInner_self_legendre_le_three_mul_integral_sq`. -/
theorem equation_12_37_norm_equiv {n : ℕ} (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ}
    (hx : IsLegendreLobatto n x w) {v : ℝ[X]} (hv : v.natDegree ≤ n) :
    (∫ t in (-1 : ℝ)..1, v.eval t ^ 2) ≤
        equation_12_37 n x w (fun t => v.eval t) (fun t => v.eval t) ∧
      equation_12_37 n x w (fun t => v.eval t) (fun t => v.eval t) ≤
        3 * ∫ t in (-1 : ℝ)..1, v.eval t ^ 2 := by
  obtain ⟨hint, hnodal⟩ := hx.isInterpolatoryMeasure_and_nodal_eq hn
  have h1 := Quadrature.integral_sq_le_discreteInner_self_legendre hn hx.injective hint hnodal
    hx.exact hv
  have h2 := Quadrature.discreteInner_self_legendre_le_three_mul_integral_sq hn hx.injective hint
    hnodal hx.exact hv
  rw [OrthogonalPolynomial.integral_legendreMeasure] at h1 h2
  exact ⟨h1, h2⟩

/-- The Poincaré inequality (12.16) on $(-1, 1)$ for a polynomial, used in the stability estimate
after (12.38). Let $p$ be a polynomial with $p(-1) = 0$. Then
$$\int_{-1}^1 p(t)^2\, dt \le 2 \int_{-1}^1 p'(t)^2\, dt,$$
with the constant $C_P^2 = (b - a)^2/2 = 2$.

From $p(y) = \int_{-1}^y p'$, the Cauchy–Schwarz inequality against $1$ gives
$p(y)^2 \le (y + 1) \int_{-1}^1 (p')^2$, and $\int_{-1}^1 (y + 1)\, dy = 2$. The proof
specializes `intervalIntegral.integral_sq_le_of_hasDerivAt_of_left_eq_zero`.

**Reading.** Gives the squared Poincaré bound on $[-1,1]$ for a polynomial with only its left
endpoint value set to zero. -/
theorem poincare_poly {p : ℝ[X]} (hm1 : p.eval (-1) = 0) :
    (∫ t in (-1 : ℝ)..1, p.eval t ^ 2) ≤ 2 * ∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2 := by
  have := intervalIntegral.integral_sq_le_of_hasDerivAt_of_left_eq_zero
    (by norm_num : (-1 : ℝ) ≤ 1) p.continuous.continuousOn (derivative p).continuous.continuousOn
    (fun t _ => p.hasDerivAt t) hm1
  norm_num at this
  exact this

/-- **Section 12.3** of [quarteroni2000numerical], the stability estimate after (12.38). Let
$n \ge 1$, let $x$ and $w$ be the Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$, let
$|f(x_j)| \le M$ for $j = 0, \dots, n$, and let $u_n$ solve the collocation problem (12.36).
Then
$$\|u_n'\|_{L^2(-1, 1)} \le \sqrt{6} \, C_P M, \qquad C_P = \frac{2}{\sqrt{2}},$$
where $C_P = (b - a)/\sqrt{2}$ is the Poincaré constant of (12.16) on $(-1, 1)$.

**Generalization.** The source takes $M = \|f\|_\infty$. A bound on the values of $f$ at the
nodes is enough.

Testing (12.38) with $v_n = u_n$, the energy identity
`QuarteroniSaccoSaleri.Chapter12.equation_12_38_energy` gives $\|u_n'\|^2 = (f, u_n)_n \le
\|f\|_n \|u_n\|_n \le \sqrt{2} M \cdot \sqrt{3} \|u_n\|_{L^2}$, by
`QuarteroniSaccoSaleri.Chapter12.equation_12_37_inner_mul_le`,
`QuarteroniSaccoSaleri.Chapter12.equation_12_37_le_sup` and
`QuarteroniSaccoSaleri.Chapter12.equation_12_37_norm_equiv`. The Poincaré inequality
$\|u_n\|_{L^2} \le C_P \|u_n'\|_{L^2}$ closes the estimate. -/
theorem equation_12_38_stability {n : ℕ} (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ}
    (hx : IsLegendreLobatto n x w) {f : ℝ → ℝ} {M : ℝ} (hM : ∀ j, |f (x j)| ≤ M) {p : ℝ[X]}
    (hp : equation_12_36 n x f p) :
    Real.sqrt (∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2) ≤
      Real.sqrt 6 * (2 / Real.sqrt 2) * M := by
  obtain ⟨hdeg, hm1, h1, hweak⟩ := (equation_12_38 hx f p).1 hp
  set E := ∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2 with hE
  set P := ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 with hP
  have hE0 : 0 ≤ E := intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  have hP0 : 0 ≤ P := intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- the energy identity: `E = (f, p)_n`
  have henergy : E = equation_12_37 n x w f fun t => p.eval t := by
    rw [hE, ← equation_12_38_energy hx hdeg hm1 h1, hweak p hdeg hm1 h1]
  -- Cauchy–Schwarz, `‖f‖_n² ≤ 2 M²`, `‖p‖_n² ≤ 3 P`
  have hcs := equation_12_37_inner_mul_le hx f fun t => p.eval t
  have hf := equation_12_37_le_sup hx hM
  have hpn := (equation_12_37_norm_equiv hn hx hdeg).2
  have hpp0 := equation_12_37_self_nonneg hx fun t => p.eval t
  -- Poincaré: `P ≤ 2 E`
  have hpoinc : P ≤ 2 * E := poincare_poly hm1
  -- assemble: `E² ≤ 2 M² · 3 P ≤ 12 M² E`, hence `E ≤ 12 M²`
  have hE2 : E ^ 2 ≤ 12 * M ^ 2 * E := by
    calc E ^ 2 = (equation_12_37 n x w f fun t => p.eval t) ^ 2 := by rw [henergy]
      _ ≤ equation_12_37 n x w f f * equation_12_37 n x w (fun t => p.eval t) fun t => p.eval t :=
          hcs
      _ ≤ (2 * M ^ 2) * (3 * P) := mul_le_mul hf hpn hpp0 (by positivity)
      _ ≤ (2 * M ^ 2) * (3 * (2 * E)) := by gcongr
      _ = 12 * M ^ 2 * E := by ring
  have hEle : E ≤ 12 * M ^ 2 := by
    rcases hE0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · nlinarith [hE2, hpos]
  have hconst : Real.sqrt 6 * (2 / Real.sqrt 2) * M = Real.sqrt (12 * M ^ 2) := by
    rw [Real.div_sqrt, ← Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num) (M ^ 2),
      Real.sqrt_sq hM0]
    norm_num
  rw [hconst]
  exact Real.sqrt_le_sqrt hEle

/-- **Section 12.3** of [quarteroni2000numerical], uniqueness for the collocation problem (12.36),
the consequence of the stability estimate after (12.38). Let $n \ge 1$, let $x$ and $w$ be the
Legendre–Gauss–Lobatto nodes and weights of $[-1, 1]$, and let $p$ and $q$ solve the collocation
problem (12.36) with the same $f$. Then $p = q$.

The difference $p - q$ solves (12.36) with $f = 0$, so $\|(p - q)'\|_{L^2} \le 0$. A polynomial
with zero derivative is constant, and this constant vanishes at $\pm 1$.

**Partial.** Establishes equality of two supplied collocation solutions. The text also asserts
existence.

**Reading.** States at most one solution rather than existence and uniqueness.
-/
theorem equation_12_36_unique {n : ℕ} (hn : 1 ≤ n) {x w : Fin (n + 1) → ℝ}
    (hx : IsLegendreLobatto n x w) {f : ℝ → ℝ} {p q : ℝ[X]} (hp : equation_12_36 n x f p)
    (hq : equation_12_36 n x f q) : p = q := by
  obtain ⟨hpdeg, hpm1, hp1, hpcoll⟩ := hp
  obtain ⟨hqdeg, hqm1, hq1, hqcoll⟩ := hq
  have hd : equation_12_36 n x (fun _ => 0) (p - q) := by
    refine ⟨(natDegree_sub_le p q).trans (max_le hpdeg hqdeg),
      by rw [eval_sub, hpm1, hqm1, sub_zero], by rw [eval_sub, hp1, hq1, sub_zero],
      fun j hj0 hjn => ?_⟩
    have h1 := hpcoll j hj0 hjn
    have h2 := hqcoll j hj0 hjn
    rw [derivative_sub, derivative_sub, eval_sub]
    simp only
    linarith
  have hst := equation_12_38_stability hn hx (M := 0) (fun _ => by simp) hd
  rw [mul_zero] at hst
  have hE0 : (0 : ℝ) ≤ ∫ t in (-1 : ℝ)..1, (derivative (p - q)).eval t ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  have hE : ∫ t in (-1 : ℝ)..1, (derivative (p - q)).eval t ^ 2 = 0 := by
    have := Real.sqrt_eq_zero'.mp (le_antisymm hst (Real.sqrt_nonneg _))
    exact le_antisymm this hE0
  -- the derivative vanishes identically, so `p - q` is a constant, vanishing at `1`
  have hder : derivative (p - q) = 0 := by
    by_contra hne
    have hpos := OrthogonalPolynomial.isWeight_legendreMeasure.integral_eval_sq_pos hne
    rw [OrthogonalPolynomial.integral_legendreMeasure] at hpos
    exact hpos.ne' hE
  have hc := Polynomial.eq_C_of_derivative_eq_zero hder
  have h1 : (p - q).eval 1 = 0 := by rw [eval_sub, hp1, hq1, sub_zero]
  rw [hc, eval_C] at h1
  rw [h1, C_0] at hc
  exact sub_eq_zero.mp hc

end QuarteroniSaccoSaleri.Chapter12
