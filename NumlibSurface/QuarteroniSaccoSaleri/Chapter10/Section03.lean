/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section08

/-!
# Quarteroni, Sacco and Saleri, Section 10.3: Chebyshev integration and interpolation

This module formalizes Section 10.3 of [quarteroni2000numerical], on Gaussian integration for the
Chebyshev weight $w(x) = (1 - x^2)^{-1/2}$. The Gauss nodes and weights are
$x_j = -\cos((2j + 1)\pi / (2(n + 1)))$ and $\alpha_j = \pi / (n + 1)$ (10.20); the nodes are the
zeros of $T_{n+1}$. The Gauss–Lobatto nodes and weights are $\bar x_j = -\cos(\pi j / n)$ and
$\bar\alpha_j = \pi / (d_j n)$, with $d_0 = d_n = 2$ and $d_j = 1$ otherwise (10.21); the interior
nodes are the zeros of $T_n' = n U_{n-1}$. The section bounds the interpolation error at the Gauss
nodes through the Lebesgue constant (10.25), defines the weighted Sobolev norm (10.23), and states
that the Gauss–Lobatto formula converges.

It then introduces the discrete scalar product $(f, g)_n = I^{GL}_{n,w}(fg)$ (10.28) and derives the
Chebyshev discrete transform: the interpolant at the Gauss–Lobatto nodes is
$\sum_{k \le n} \tilde f_k T_k$ (10.29), with coefficients $\tilde f_k$ given by (10.31) and the
inverse transform (10.30). The proofs specialize Mathlib's Chebyshev–Gauss rule
`Polynomial.Chebyshev.integral_eq_sumZeroes`, the Chebyshev–Gauss–Lobatto results of
`Numlib.Approximation.GaussLobatto`, the Lebesgue constant bound of
`Numlib.Approximation.Interpolation`, and the convergence criterion of
`Numlib.Approximation.Quadrature`.

## Main definitions

* Equation (10.20), `QuarteroniSaccoSaleri.Chapter10.chebyshevGaussNode`: the Chebyshev–Gauss node
  $x_j = -\cos((2j + 1)\pi / (2(n + 1)))$.
* Equation (10.20), `QuarteroniSaccoSaleri.Chapter10.chebyshevGaussNodeIcc`: the Chebyshev–Gauss
  nodes as points of $[-1, 1]$, the nodes of the interpolant $\Pi^G_n$.
* Equation (10.21), `QuarteroniSaccoSaleri.Chapter10.chebyshevLobattoNode`: the
  Chebyshev–Gauss–Lobatto node $\bar x_j = -\cos(\pi j / n)$.
* Equations (10.23) and (10.35), `QuarteroniSaccoSaleri.Chapter10.equation_10_23`: the weighted
  Sobolev norm $\|f\|_{s,w}$.
* Equation (10.28), `QuarteroniSaccoSaleri.Chapter10.equation_10_28`: the discrete scalar product
  $(f, g)_n$ of the Gauss–Lobatto rule.
* Equation (10.31), `QuarteroniSaccoSaleri.Chapter10.chebyshevDiscreteCoeff`: the discrete
  coefficients $\tilde f_k$ of the Chebyshev discrete transform.

## Main results

* Equation (10.20), `QuarteroniSaccoSaleri.Chapter10.equation_10_20`: the Chebyshev–Gauss formula
  has increasing nodes, which are the zeros of $T_{n+1}$, and degree of exactness $2n + 1$.
* Equation (10.21), `QuarteroniSaccoSaleri.Chapter10.equation_10_21`: the Chebyshev–Gauss–Lobatto
  formula has increasing nodes from $-1$ to $1$, the given weights and degree of exactness $2n - 1$,
  and its interior nodes are zeros of $T_n' = n U_{n-1}$.
* Equation (10.25), `QuarteroniSaccoSaleri.Chapter10.equation_10_25_interpolation_error`: $\|f -
  \Pi^G_n f\|_\infty \le (1 + \Lambda_n) E_n^*(f)$ at the Chebyshev–Gauss nodes.
* Equation (10.25), `QuarteroniSaccoSaleri.Chapter10.equation_10_25`:
  $\Lambda_n \le 2 + (2/\pi) \log(2n + 2)$, and the resulting error bound.
* Section 10.3, `QuarteroniSaccoSaleri.Chapter10.lobatto_tendsto`: $I^{GL}_{n,w}(f) \to \int_{-1}^1
  f(x) (1 - x^2)^{-1/2} \, dx$ for every $f \in C^0([-1, 1])$.
* Equations (10.29)–(10.31) and Exercise 10.2, `QuarteroniSaccoSaleri.Chapter10.equation_10_31`: the
  Chebyshev discrete transform and its inverse, and the equality of the interpolant with the
  discrete truncation $f_n^*$ of (10.4).

## Conventions

* The node index $j$ runs over `Fin (n + 1)`. The nodes increase with $j$, so $\bar x_0 = -1$ and
  $\bar x_n = 1$, as in the book.
* The Gauss–Lobatto weights $\bar\alpha_j$ and the factors $d_j$ are the backbone's
  `Polynomial.Chebyshev.lobattoWeight` and `Polynomial.Chebyshev.lobattoFactor`.
* The interpolation operator $\Pi_n$ at nodes $x$ is `Lagrange.interpolateCLM x` on
  $C^0([-1, 1])$. The Lebesgue constant $\Lambda_n$ is the supremum over $t$ of
  $\sum_i |l_i(t)|$, with $l_i$ = `Lagrange.basisCM x i`.
* The best approximation error $E_n^*(f)$ is
  `QuarteroniSaccoSaleri.Chapter10.bestApproximationError` of Section 10.8.

## Implementation notes

* The backbone and Mathlib state the Chebyshev rules at the nodes $\cos(j\pi / n)$
  (`Polynomial.Chebyshev.node`) and $\cos((2j + 1)\pi / (2(n + 1)))$. The nodes of the book are
  these nodes in the opposite order, $\bar x_j = \cos((n - j)\pi / n)$, and every statement here is
  transported along $j \mapsto n - j$.
* The convergence of the Gauss–Lobatto formula is the Szegő–Pólya criterion in the form
  `Quadrature.tendsto_of_isExactOnMeasure`.
* The estimates (10.22), (10.24) and (10.26)–(10.27) of this section, together with (10.36)–(10.37)
  of Section 10.4, (10.71) of Section 10.10 and Theorem 12.2 of Section 12.3, are quoted by the book
  from Canuto, Hussaini, Quarteroni and Zang (1988) without proof. They need three pieces of theory
  that the library does not have. The first is calculus for the weighted Sobolev seminorms on
  $(-1, 1)$; `QuarteroniSaccoSaleri.Chapter10.equation_10_23` is only a definition. Because
  $(1 - x^2)^{k/2} \le 1$, a projection estimate in the seminorm with the weights $(1 - x^2)^{k/2}$
  bounds the right side of the book, with the norm (10.23), term by term. The second is the decay of
  the coefficients and the projection estimate $\|f - P_n f\|_w \le C n^{-s} \|f\|_{s,w}$ for
  $f \in C^s[-1, 1]$, where $P_n$ is the truncation of the orthogonal expansion. It follows from the
  Sturm–Liouville symmetry $\int (Lu) v w = \int u (Lv) w$, in which the factor $1 - x^2$ removes
  the boundary terms, applied $\lfloor s/2 \rfloor$ times, and from a bound on the tail of the
  expansion with the eigenvalues $\lambda_k = k^2$ (Chebyshev) or $\lambda_k = k(k + 1)$ (Legendre).
  The third is the passage from the projection to the interpolant. The elementary argument
  $\Pi_n f - P_n f = \Pi_n (P_n f - f)$, with the equivalence of the discrete and continuous norms,
  loses a factor $n^{1/2}$ and gives only the rate $n^{1/2 - s}$. The printed rate $n^{-s}$ needs
  the $H^1$ projection and a Marcinkiewicz–Zygmund-type bound
  $\|v\|_n \le C (\|v\|_w + n^{-1} \|v'\|_w)$, which rests on an estimate of the spacing of the
  nodes.
* The sup-norm estimate (10.24) also needs (10.71) and the one-dimensional Gagliardo–Nirenberg
  inequality $\|v\|_\infty^2 \le \|v\|_{L^2(-1,1)}^2 + 2 \|v\| \|v'\|$. The library has the
  embedding $\|u\|_\infty \le C \|u\|_{W^{1,p}}$ of `Numlib.Analysis.Sobolev.Interval.Embedding`,
  but not this product form. The rate $n^{1/2 - s}$ of (10.24) is not better than the rate that the
  elementary argument above gives for (10.22).
* Estimate (10.26) is the case $v_n = 1$ of (10.27), with $\|1\|_w = \sqrt{\pi}$. Because the
  Gauss–Lobatto rule is exact on $\mathbb{P}_{2n-1}$, (10.27) reduces to $g = f - P_{n-1} f$: $(f,
  v_n)_w - (f, v_n)_n = (g, v_n)_w - (g, v_n)_n$, so $|(f, v_n)_w - (f, v_n)_n| \le \|g\|_w
  \|v_n\|_w + \|g\|_n \|v_n\|_n$.

## Deviations from the source

* **Equations (10.30)–(10.31)** (correction). The book prints $\cos(kj\pi / n)$, which is
  $T_k(\bar x_{n-j})$ and not $T_k(\bar x_j)$ for the increasing nodes of (10.21). The library uses
  $\cos(k(n - j)\pi / n) = T_k(\bar x_j)$. See
  `QuarteroniSaccoSaleri.Chapter10.chebyshevDiscreteCoeff` and
  `QuarteroniSaccoSaleri.Chapter10.equation_10_31`.

## Not formalized

* **Equation (10.22)**, the estimate $\|f - \Pi^{GL}_{n,w} f\|_w \le C n^{-s} \|f\|_{s,w}$ for the
  interpolant at the Chebyshev–Gauss–Lobatto nodes. The library has no theory of spectral projection
  in weighted Sobolev norms. The book calls the interpolant of degree $n + 1$; it has degree $n$.
* **Equation (10.24)** and **Exercise 10.3**, the estimate $\|f - \Pi^{GL}_{n,w} f\|_\infty \le C
  n^{1/2 - s} \|f\|_{s,w}$ and the same estimate at the Gauss nodes. The reason is the same as for
  (10.22), and the one-dimensional Gagliardo–Nirenberg inequality is also missing.
* **Equations (10.26)–(10.27)**, the error of the discrete scalar product and of the Gauss–Lobatto
  formula in the norm $\|f\|_{s,w}$. The reason is the same as for (10.22).
* **Equation (10.25)**, Rivlin's bound $\Lambda_n \le (2/\pi) \log(n + 1) + 1$. It is sharp at
  $n = 0$ and needs two theorems that nothing else uses; the library proves
  $\Lambda_n \le 2 + (2/\pi) \log(2n + 2)$ instead.
* **Section 10.3, convergence of the Gauss–Lobatto formula** for every $f$ with finite weighted
  integral. Only continuous $f$ are treated.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Quadrature Real Set Filter Topology

namespace QuarteroniSaccoSaleri.Chapter10

variable {n : ℕ}

/-! ### The Chebyshev–Gauss formula (10.20) -/

/-- **Equation (10.20)** of [quarteroni2000numerical], the Chebyshev–Gauss nodes. For
$0 \le j \le n$, the **Chebyshev–Gauss node** is
$$x_j = -\cos\left(\frac{(2j + 1)\pi}{2(n + 1)}\right).$$
-/
noncomputable def chebyshevGaussNode (n j : ℕ) : ℝ := -cos ((2 * j + 1) * π / (2 * (n + 1)))

/-- Supports equation (10.20). For $j \le n$, the Gauss node $x_j$ of the book is
$\cos((2(n - j) + 1)\pi / (2(n + 1)))$, the node of Mathlib's `Polynomial.Chebyshev.sumZeroes`
of index $n - j$. The two families are the same points in the opposite order. -/
theorem chebyshevGaussNode_eq {j : ℕ} (hj : j ≤ n) :
    chebyshevGaussNode n j = cos ((2 * ((n - j : ℕ) : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ)) * π) := by
  rw [chebyshevGaussNode, ← cos_pi_sub, Nat.cast_sub hj]
  congr 1
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- For $j \le n$, the angle $(2j + 1)\pi / (2(n + 1))$ lies in $[0, \pi]$. -/
private theorem gaussAngle_mem_Icc {j : ℕ} (hj : j ≤ n) :
    (2 * (j : ℝ) + 1) * π / (2 * ((n : ℝ) + 1)) ∈ Icc 0 π := by
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have : (j : ℝ) ≤ n := by exact_mod_cast hj
  nlinarith [pi_pos]

/-- **Equation (10.20)** of [quarteroni2000numerical]. For the Chebyshev weight
$w(x) = (1 - x^2)^{-1/2}$, the Gauss nodes and coefficients are
$$x_j = -\cos\left(\frac{(2j + 1)\pi}{2(n + 1)}\right), \qquad \alpha_j = \frac{\pi}{n + 1},
  \qquad 0 \le j \le n.$$
The nodes increase with $j$, they are the zeros of the Chebyshev polynomial
$T_{n+1} \in \mathbb{P}_{n+1}$, and the formula has degree of exactness $2n + 1$ for $w$.

The weight $w(x)\,dx$ is `OrthogonalPolynomial.chebyshevMeasure`. The proof specializes
Mathlib's `Polynomial.Chebyshev.integral_eq_sumZeroes`, whose nodes
$\cos((2i + 1)\pi / (2(n + 1)))$ are those of the book under $j \mapsto n - j$. -/
theorem equation_10_20 (n : ℕ) :
    StrictMono (fun j : Fin (n + 1) => chebyshevGaussNode n j) ∧
      (∀ j : Fin (n + 1), (Chebyshev.T ℝ (n + 1)).eval (chebyshevGaussNode n j) = 0) ∧
      IsExactOnMeasure chebyshevMeasure (fun _ : Fin (n + 1) => π / (n + 1))
        (fun j : Fin (n + 1) => chebyshevGaussNode n j) (2 * n + 1) := by
  refine ⟨?_, fun j => ?_, fun p hp => ?_⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    simp only [chebyshevGaussNode, Fin.val_castSucc, Fin.val_succ, neg_lt_neg_iff]
    refine strictAntiOn_cos (gaussAngle_mem_Icc (by omega : (i : ℕ) ≤ n))
      (gaussAngle_mem_Icc (by omega : (i : ℕ) + 1 ≤ n)) ?_
    push_cast
    gcongr
    linarith
  · rw [chebyshevGaussNode_eq (Nat.lt_succ_iff.mp j.2), Chebyshev.T_real_cos, cos_eq_zero_iff]
    refine ⟨((n - j : ℕ) : ℤ), ?_⟩
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  · have hdeg : p.degree < ((2 * (n + 1) : ℕ) : WithBot ℕ) :=
      hp.trans_lt (by exact_mod_cast (by omega : 2 * n + 1 < 2 * (n + 1)))
    rw [chebyshevMeasure, Chebyshev.integral_eq_sumZeroes (n := n + 1) (Nat.succ_ne_zero n)
      (by exact_mod_cast hdeg), Chebyshev.sumZeroes, Finset.mul_sum,
      ← Finset.sum_range_reflect (fun i => π / ((n + 1 : ℕ) : ℝ) *
        p.eval (cos ((2 * (i : ℝ) + 1) / (2 * ((n + 1 : ℕ) : ℝ)) * π))) (n + 1),
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [chebyshevGaussNode_eq (Nat.lt_succ_iff.mp j.2), Nat.add_sub_cancel, Nat.cast_succ]

/-- The Chebyshev–Gauss nodes lie in $[-1, 1]$. -/
theorem chebyshevGaussNode_mem_Icc (n j : ℕ) : chebyshevGaussNode n j ∈ Icc (-1 : ℝ) 1 :=
  ⟨neg_le_neg (cos_le_one _), by
    rw [chebyshevGaussNode, neg_le]
    exact neg_one_le_cos _⟩

/-- Supports equation (10.25). The Chebyshev–Gauss nodes (10.20) as points of $[-1, 1]$. They are
the nodes of the interpolant $\Pi^G_n$ of (10.25). -/
noncomputable def chebyshevGaussNodeIcc (n : ℕ) (j : Fin (n + 1)) : Icc (-1 : ℝ) 1 :=
  ⟨chebyshevGaussNode n j, chebyshevGaussNode_mem_Icc n j⟩

/-- Supports equation (10.25). The Gauss node $x_{n-j}$ of the book is the backbone's Chebyshev node
`Lagrange.chebNode n j`, which is $\cos((2j + 1)\pi / (2(n + 1)))$. The index $n - j$ is
`Fin.rev j`. -/
theorem chebyshevGaussNode_rev (j : Fin (n + 1)) :
    chebyshevGaussNode n (Fin.rev j) = Lagrange.chebNode n j := by
  rw [chebyshevGaussNode_eq (Nat.lt_succ_iff.mp (Fin.rev j).2), Lagrange.chebNode,
    Lagrange.chebAngle]
  have hj : n - (Fin.rev j : ℕ) = j := by rw [Fin.val_rev]; omega
  rw [hj]
  congr 1
  push_cast
  ring

/-- Supports equation (10.25). The Gauss nodes of the book are the backbone's nodes
`Lagrange.chebNodeIcc n` in the opposite order. So the two families differ by a permutation, and
the two interpolation operators are equal. -/
theorem chebyshevGaussNodeIcc_eq (n : ℕ) :
    chebyshevGaussNodeIcc n = Lagrange.chebNodeIcc n ∘ Fin.revPerm := by
  funext j
  apply Subtype.ext
  change chebyshevGaussNode n j = Lagrange.chebNode n (Fin.rev j)
  rw [← chebyshevGaussNode_rev (Fin.rev j), Fin.rev_rev]

/-- The Chebyshev–Gauss nodes are distinct. -/
theorem injective_chebyshevGaussNodeIcc (n : ℕ) : Function.Injective (chebyshevGaussNodeIcc n) :=
  fun _ _ h => (equation_10_20 n).1.injective (congrArg Subtype.val h)

/-- **Equation (10.25)** of [quarteroni2000numerical], the first inequality. Let
$f \in C^0([-1, 1])$, and let $\Pi^G_n f$ be its interpolant at the $n + 1$ Chebyshev–Gauss
nodes (10.20). Then
$$\|f - \Pi^G_n f\|_\infty \le (1 + \Lambda_n) E_n^*(f),$$
where $\Lambda_n = \sup_{t \in [-1, 1]} \sum_j |l_j(t)|$ is the Lebesgue constant of the
Chebyshev–Gauss nodes and $E_n^*(f)$ is the best approximation error of Section 10.8.

The proof applies `QuarteroniSaccoSaleri.Chapter10.interpolation_error_le_lebesgue` of Section
10.8 at these nodes. The bound on $\Lambda_n$ is
`QuarteroniSaccoSaleri.Chapter10.equation_10_25`. -/
theorem equation_10_25_interpolation_error (n : ℕ) (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    ‖f - Lagrange.interpolateCLM (chebyshevGaussNodeIcc n) f‖ ≤
      (1 + sSup (Set.range fun t : Icc (-1 : ℝ) 1 =>
          ∑ i, |Lagrange.basisCM (chebyshevGaussNodeIcc n) i t|)) *
        bestApproximationError (-1) 1 n f :=
  interpolation_error_le_lebesgue (injective_chebyshevGaussNodeIcc n) f

/-- **Equation (10.25)** of [quarteroni2000numerical]. Let $f \in C^0([-1, 1])$, and let $\Pi^G_n f$
be its interpolant at the $n + 1$ Chebyshev–Gauss nodes (10.20). Let $\Lambda_n = \sup_{t \in
[-1, 1]} \sum_j |l_j(t)|$ be the Lebesgue constant of these nodes, and let $E_n^*(f)$ be the
best approximation error of Section 10.8. Then
$$\Lambda_n \le 2 + \frac{2}{\pi} \log(2n + 2), \qquad \|f - \Pi^G_n f\|_\infty \le \left(1 +
  2 + \frac{2}{\pi} \log(2n + 2)\right) E_n^*(f).$$

The book prints Rivlin's sharper bound $\Lambda_n \le (2/\pi) \log(n + 1) + 1$
([rivlin1969introduction], Theorem 1.2). The statement here has the same growth rate
$(2/\pi) \log n$ and a larger additive constant. Rivlin's bound is not formalized: it is an
equality at $n = 0$, where $\Lambda_0 = 1$, so no step of its proof may lose anything, and it
needs two further theorems that nothing else in the library uses. These are that the Lebesgue
function attains its maximum at $\pm 1$, and Rivlin's bound on the cotangent sum that it equals
there. The argument through `SineSum.sum_term_le` that proves the bound here loses $1.441\ldots$
in the additive constant, against a margin of $0.0375$. See also the section `Not formalized` of
`Numlib.Approximation.Interpolation`.

The first inequality is `QuarteroniSaccoSaleri.Chapter10.equation_10_25_interpolation_error`.
The bound on $\Lambda_n$ is the backbone's `Lagrange.norm_interpolateCLM_chebyshev_le`, because
$\Lambda_n = \|\Pi^G_n\|$ (`Lagrange.norm_interpolateCLM`) and the nodes of the book are the
backbone's `Lagrange.chebNodeIcc n` in the opposite order
(`QuarteroniSaccoSaleri.Chapter10.chebyshevGaussNodeIcc_eq`,
`Lagrange.interpolateCLM_comp_equiv`). -/
theorem equation_10_25 (n : ℕ) (f : C(Icc (-1 : ℝ) 1, ℝ)) :
    sSup (Set.range fun t : Icc (-1 : ℝ) 1 =>
        ∑ i, |Lagrange.basisCM (chebyshevGaussNodeIcc n) i t|) ≤
      2 + 2 / π * Real.log (2 * n + 2) ∧
    ‖f - Lagrange.interpolateCLM (chebyshevGaussNodeIcc n) f‖ ≤
      (1 + (2 + 2 / π * Real.log (2 * n + 2))) * bestApproximationError (-1) 1 n f := by
  have : Nonempty (Icc (-1 : ℝ) 1) := ⟨⟨1, by norm_num⟩⟩
  have hΛ : sSup (Set.range fun t : Icc (-1 : ℝ) 1 =>
      ∑ i, |Lagrange.basisCM (chebyshevGaussNodeIcc n) i t|) ≤
        2 + 2 / π * Real.log (2 * n + 2) := by
    rw [← Lagrange.norm_interpolateCLM (injective_chebyshevGaussNodeIcc n),
      chebyshevGaussNodeIcc_eq, Lagrange.interpolateCLM_comp_equiv]
    exact Lagrange.norm_interpolateCLM_chebyshev_le n
  refine ⟨hΛ, (equation_10_25_interpolation_error n f).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) Metric.infDist_nonneg

/-! ### The Chebyshev–Gauss–Lobatto formula (10.21) -/

/-- **Equation (10.21)** of [quarteroni2000numerical], the Chebyshev–Gauss–Lobatto nodes. For
$n \ge 1$ and $0 \le j \le n$, the **Chebyshev–Gauss–Lobatto node** is
$\bar x_j = -\cos(\pi j / n)$. -/
noncomputable def chebyshevLobattoNode (n j : ℕ) : ℝ := -cos (j * π / n)

/-- Supports equation (10.21). Let $n \ge 1$ and $j \le n$. The Gauss–Lobatto node $\bar x_j$ of the
book is $\cos((n - j)\pi / n)$, the extremal point of $T_n$ of index $n - j$ in Mathlib's
`Polynomial.Chebyshev.node`. The two families are the same points in the opposite order. -/
theorem chebyshevLobattoNode_eq_node (hn : n ≠ 0) {j : ℕ} (hj : j ≤ n) :
    chebyshevLobattoNode n j = Chebyshev.node n (n - j) := by
  rw [chebyshevLobattoNode, Chebyshev.node, ← cos_pi_sub, Nat.cast_sub hj]
  congr 1
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- Supports equation (10.21). The factors $d_j$ of (10.21) satisfy $d_{n-j} = d_j$ for $j \le n$.
-/
theorem lobattoFactor_sub {j : ℕ} (hj : j ≤ n) :
    Chebyshev.lobattoFactor n (n - j) = Chebyshev.lobattoFactor n j := by
  unfold Chebyshev.lobattoFactor
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

/-- Supports equation (10.21). The weights $\bar\alpha_j$ of (10.21) satisfy
$\bar\alpha_{n-j} = \bar\alpha_j$ for $j \le n$. -/
theorem lobattoWeight_sub {j : ℕ} (hj : j ≤ n) :
    Chebyshev.lobattoWeight n (n - j) = Chebyshev.lobattoWeight n j := by
  simp only [Chebyshev.lobattoWeight, lobattoFactor_sub hj]

/-- Supports equation (10.21). For $n \ge 1$, the node $\bar x_{n-j}$ of the book is Mathlib's
$\cos(j\pi / n)$. The index $n - j$ is `Fin.rev j`. -/
theorem chebyshevLobattoNode_rev (hn : n ≠ 0) (j : Fin (n + 1)) :
    chebyshevLobattoNode n (Fin.rev j) = Chebyshev.node n j := by
  rw [chebyshevLobattoNode_eq_node hn (Nat.lt_succ_iff.mp (Fin.rev j).2)]
  congr 1
  rw [Fin.val_rev]
  omega

/-- Supports equation (10.21). The weights $\bar\alpha_j$ are symmetric under $j \mapsto n - j$,
written with `Fin.rev`. -/
theorem lobattoWeight_rev (j : Fin (n + 1)) :
    Chebyshev.lobattoWeight n (Fin.rev j) = Chebyshev.lobattoWeight n j := by
  rw [Fin.val_rev, show n + 1 - ((j : ℕ) + 1) = n - j by omega,
    lobattoWeight_sub (Nat.lt_succ_iff.mp j.2)]

/-- Supports equation (10.21). For $n \ge 1$, the Chebyshev–Gauss–Lobatto rule, with the nodes in
the order of the book, has degree of exactness $2n - 1$ for the Chebyshev weight. -/
theorem isExactOnMeasure_chebyshevLobatto (hn : n ≠ 0) :
    IsExactOnMeasure chebyshevMeasure (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j)
      (fun j : Fin (n + 1) => chebyshevLobattoNode n j) (2 * n - 1) := by
  have h := (isExactOnMeasure_comp_equiv (μ := chebyshevMeasure)
    (w := fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j)
    (x := fun j : Fin (n + 1) => Chebyshev.node n j) Fin.revPerm (d := 2 * n - 1)).mpr
    (Chebyshev.isExactOnMeasure_lobattoWeight_node hn)
  have hw' : (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j) =
      (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j) ∘ Fin.revPerm := by
    ext j
    exact (lobattoWeight_rev j).symm
  have hx' : (fun j : Fin (n + 1) => chebyshevLobattoNode n j) =
      (fun j : Fin (n + 1) => Chebyshev.node n j) ∘ Fin.revPerm := by
    ext j
    rw [Function.comp_apply, Fin.revPerm_apply, ← chebyshevLobattoNode_rev hn (Fin.rev j),
      Fin.rev_rev]
  rwa [← hw', ← hx'] at h

/-- Supports equation (10.21). For $n \ge 1$, the Chebyshev–Gauss–Lobatto nodes are distinct. -/
theorem injective_chebyshevLobattoNode (hn : n ≠ 0) :
    Function.Injective fun j : Fin (n + 1) => chebyshevLobattoNode n j := by
  intro i j hij
  have hi := Nat.lt_succ_iff.mp i.2
  have hj := Nat.lt_succ_iff.mp j.2
  simp only [chebyshevLobattoNode_eq_node hn hi, chebyshevLobattoNode_eq_node hn hj] at hij
  have := (Chebyshev.strictAntiOn_node n).injOn
    (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega : n - i < n + 1)))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega : n - j < n + 1))) hij
  exact Fin.ext (by omega)

/-- **Equation (10.21)** of [quarteroni2000numerical]. Let $n \ge 1$. The Chebyshev–Gauss–Lobatto
nodes and weights are
$$\bar x_j = -\cos\left(\frac{\pi j}{n}\right), \qquad \bar\alpha_j = \frac{\pi}{d_j n}, \qquad
  0 \le j \le n,$$
with $d_0 = d_n = 2$ and $d_j = 1$ for $j = 1, \dots, n - 1$. The nodes increase from
$\bar x_0 = -1$ to $\bar x_n = 1$, and the formula has degree of exactness $2n - 1$ for the
Chebyshev weight. Moreover $T_n' = n U_{n-1}$, and every internal node
$\bar x_1, \dots, \bar x_{n-1}$ is a zero of $T_n'$, as anticipated in Remark 10.2.

The formula for $\bar\alpha_j$ holds for every natural number $j$. The proof specializes the
backbone's `Polynomial.Chebyshev.integral_eq_sumExtrema` at the nodes $\cos(j\pi / n)$, in the
opposite order, with Mathlib's `Polynomial.Chebyshev.T_derivative_eq_U` and
`Polynomial.Chebyshev.U_real_cos`. -/
theorem equation_10_21 (hn : 1 ≤ n) :
    StrictMono (fun j : Fin (n + 1) => chebyshevLobattoNode n j) ∧
      chebyshevLobattoNode n 0 = -1 ∧ chebyshevLobattoNode n n = 1 ∧
      (∀ j, Chebyshev.lobattoWeight n j = π / (Chebyshev.lobattoFactor n j * n)) ∧
      Chebyshev.lobattoFactor n 0 = 2 ∧ Chebyshev.lobattoFactor n n = 2 ∧
      (∀ j, 0 < j → j < n → Chebyshev.lobattoFactor n j = 1) ∧
      IsExactOnMeasure chebyshevMeasure (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j)
        (fun j : Fin (n + 1) => chebyshevLobattoNode n j) (2 * n - 1) ∧
      derivative (Chebyshev.T ℝ n) = (n : ℝ[X]) * Chebyshev.U ℝ (n - 1) ∧
      ∀ j, 0 < j → j < n → (derivative (Chebyshev.T ℝ n)).eval (chebyshevLobattoNode n j) = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hder : derivative (Chebyshev.T ℝ n) = (n : ℝ[X]) * Chebyshev.U ℝ (n - 1) := by
    rw [Chebyshev.T_derivative_eq_U]
    push_cast [Nat.cast_sub hn]
    rfl
  refine ⟨?_, ?_, ?_, fun j => rfl, by simp [Chebyshev.lobattoFactor],
    by simp [Chebyshev.lobattoFactor], fun j hj0 hjn => Chebyshev.lobattoFactor_of_ne (by omega)
      (by omega), isExactOnMeasure_chebyshevLobatto hn0, hder, fun j hj0 hjn => ?_⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    change chebyshevLobattoNode n i.castSucc < chebyshevLobattoNode n i.succ
    rw [chebyshevLobattoNode_eq_node hn0 (Nat.lt_succ_iff.mp i.castSucc.2),
      chebyshevLobattoNode_eq_node hn0 (Nat.lt_succ_iff.mp i.succ.2), Fin.val_castSucc,
      Fin.val_succ]
    exact Chebyshev.node_lt (i := n - ((i : ℕ) + 1)) (j := n - i) (by omega) (by omega)
  · simp [chebyshevLobattoNode]
  · rw [chebyshevLobattoNode, mul_div_cancel_left₀ π hnR, cos_pi]
    norm_num
  · -- `x̄ⱼ = cos θ` with `θ = (n - j)π/n ∈ (0, π)`, and `sin(nθ) = sin((n - j)π) = 0`
    have hθ : chebyshevLobattoNode n j = cos (((n - j : ℕ) : ℝ) * π / n) :=
      chebyshevLobattoNode_eq_node hn0 hjn.le
    have hnj : (0 : ℝ) < ((n - j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - j)
    have hsin : sin (((n - j : ℕ) : ℝ) * π / n) ≠ 0 := by
      refine (sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
      rw [div_lt_iff₀ (by positivity), Nat.cast_sub hjn.le]
      have : (0 : ℝ) < j := by exact_mod_cast hj0
      nlinarith [pi_pos]
    have hU := Chebyshev.U_real_cos (θ := ((n - j : ℕ) : ℝ) * π / n) (n := (n : ℤ) - 1)
    push_cast at hU
    rw [sub_add_cancel, show (n : ℝ) * (((n - j : ℕ) : ℝ) * π / n) = ((n - j : ℕ) : ℝ) * π by
      field_simp, sin_nat_mul_pi] at hU
    have hUzero := (mul_eq_zero.mp hU).resolve_right hsin
    rw [hder, eval_mul, hθ, eval_natCast, hUzero, mul_zero]

/-! ### The weighted Sobolev norm (10.23) -/

/-- **Equations (10.23) and (10.35)** of [quarteroni2000numerical], the weighted Sobolev norm. Let
$\mu$ be a measure and $s \ge 0$. The **weighted Sobolev norm** of order $s$ of a function $f$
is
$$\|f\|_{s,w} = \left(\sum_{k=0}^s \|f^{(k)}\|_w^2\right)^{1/2}, \qquad \|g\|_w^2 = \int g^2 \,
  d\mu.$$
The norm $\|\cdot\|_{s,w}$ of (10.23) is the case $\mu$ =
`OrthogonalPolynomial.chebyshevMeasure`, and the norm $\|\cdot\|_s$ of (10.35) is the case
$\mu$ = `OrthogonalPolynomial.legendreMeasure`.

The derivatives are `iteratedDeriv`, and an integral that does not exist counts as $0$. The
definition serves to state the estimates of the book, which are not formalized; no results about
it are proved. -/
noncomputable def equation_10_23 (μ : Measure ℝ) (s : ℕ) (f : ℝ → ℝ) : ℝ :=
  √(∑ k ∈ Finset.range (s + 1), ∫ x, (iteratedDeriv k f x) ^ 2 ∂μ)

/-! ### Convergence of the Chebyshev–Gauss–Lobatto formula -/

/-- **Section 10.3** of [quarteroni2000numerical], the convergence of the Chebyshev–Gauss–Lobatto
formula. For every $f \in C^0([-1, 1])$,
$$\int_{-1}^1 f(x) (1 - x^2)^{-1/2} \, dx = \lim_{n \to \infty} I^{GL}_{n,w}(f), \qquad
  I^{GL}_{n,w}(f) = \sum_{j=0}^n \bar\alpha_j f(\bar x_j).$$

The book states the limit for every $f$ whose weighted integral is finite, and refers to Szegő
(1967), p. 342. Only continuous $f$ are treated here. The proof uses the Szegő–Pólya criterion
`Quadrature.tendsto_of_isExactOnMeasure`: the weights $\pi / (d_j n)$ are positive, and the
degree of exactness $2n - 1$ is unbounded. -/
theorem lobatto_tendsto {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto (fun n => ∑ j : Fin (n + 1), Chebyshev.lobattoWeight n j * f (chebyshevLobattoNode n j))
      atTop (𝓝 (∫ x in (-1 : ℝ)..1, f x / √(1 - x ^ 2))) := by
  have := isWeight_chebyshevMeasure.isFiniteMeasure
  have hint : ∫ x in (-1 : ℝ)..1, f x / √(1 - x ^ 2) = ∫ x, f x ∂chebyshevMeasure := by
    rw [chebyshevMeasure, Chebyshev.integral_measureT]
    simp only [div_eq_mul_inv, Real.sqrt_inv]
  rw [hint, ← tendsto_add_atTop_iff_nat 1]
  exact tendsto_of_isExactOnMeasure chebyshevMeasure_compl_Icc
    (x := fun k (j : Fin (k + 1 + 1)) => chebyshevLobattoNode (k + 1) j)
    (α := fun k (j : Fin (k + 1 + 1)) => Chebyshev.lobattoWeight (k + 1) j)
    (fun k => injective_chebyshevLobattoNode (Nat.succ_ne_zero k))
    (fun k j => by
      rw [chebyshevLobattoNode_eq_node (Nat.succ_ne_zero k) (Nat.lt_succ_iff.mp j.2)]
      exact Chebyshev.node_mem_Icc)
    (fun k j => (Chebyshev.lobattoWeight_pos (Nat.succ_ne_zero k) j).le)
    (d := fun k => 2 * (k + 1) - 1) (tendsto_atTop_atTop.mpr fun N => ⟨N, fun k hk => by omega⟩)
    (fun k => isExactOnMeasure_chebyshevLobatto (Nat.succ_ne_zero k)) hf

/-! ### The discrete scalar product (10.28) and the Chebyshev discrete transform (10.29)–(10.31) -/

/-- **Equation (10.28)** of [quarteroni2000numerical], the discrete scalar product of the
Chebyshev–Gauss–Lobatto formula:
$$(f, g)_n = \sum_{j=0}^n \bar\alpha_j f(\bar x_j) g(\bar x_j) = I^{GL}_{n,w}(fg).$$

The definition is `Quadrature.discreteInner` at the weights and nodes (10.21). -/
noncomputable def equation_10_28 (n : ℕ) (f g : ℝ → ℝ) : ℝ :=
  discreteInner (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j)
    (fun j : Fin (n + 1) => chebyshevLobattoNode n j) f g

/-- Supports equation (10.28). The discrete scalar product is $(f, g)_n = \sum_j \bar\alpha_j f(\bar
x_j) g(\bar x_j)$, and it is also $\sum_j \bar\alpha_j (fg)(\bar x_j) = I^{GL}_{n,w}(fg)$. -/
theorem equation_10_28_eq (n : ℕ) (f g : ℝ → ℝ) :
    equation_10_28 n f g =
        ∑ j : Fin (n + 1), Chebyshev.lobattoWeight n j * f (chebyshevLobattoNode n j) *
          g (chebyshevLobattoNode n j) ∧
      equation_10_28 n f g =
        ∑ j : Fin (n + 1), Chebyshev.lobattoWeight n j * (f * g) (chebyshevLobattoNode n j) :=
  ⟨rfl, by
    unfold equation_10_28 discreteInner
    exact Finset.sum_congr rfl fun j _ => by rw [Pi.mul_apply, mul_assoc]⟩

/-- **Equation (10.31)** of [quarteroni2000numerical], the discrete coefficients of the Chebyshev
discrete transform (CDT). For $k = 0, \dots, n$,
$$\tilde f_k = \frac{2}{n d_k} \sum_{j=0}^n \frac{1}{d_j} \cos\left(\frac{k(n - j)\pi}{n}\right)
  f(\bar x_j).$$
The cosine is $T_k(\bar x_j)$ for the node ordering of (10.21).

**Correction.** The book prints $\cos(kj\pi / n)$, which is $T_k(\bar x_{n-j})$ and not
$T_k(\bar x_j)$ for the increasing nodes of (10.21). With $\cos(kj\pi / n)$ the formula holds
for the nodes $\cos(j\pi / n)$. Since $\cos(k(n - j)\pi / n) = (-1)^k \cos(kj\pi / n)$, the two
forms differ by the sign $(-1)^k$.

At $n = 0$ the factor $2 / (n d_k)$ is $0$ by the Lean convention for division by zero. -/
noncomputable def chebyshevDiscreteCoeff (n : ℕ) (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  2 / (n * Chebyshev.lobattoFactor n k) * ∑ j ∈ Finset.range (n + 1),
    (Chebyshev.lobattoFactor n j)⁻¹ * cos ((k : ℝ) * ((n - j : ℕ) : ℝ) * π / n) *
      f (chebyshevLobattoNode n j)

/-- Supports equation (10.31). For $n \ge 1$, the discrete coefficients in the order of the book
equal those of the backbone's `Polynomial.Chebyshev.interpolate_eq_sum_cdt` at the nodes
$\cos(j\pi / n)$:
$$\tilde f_k = \frac{2}{n d_k} \sum_{j=0}^n \frac{1}{d_j} \cos\left(\frac{kj\pi}{n}\right)
  f(\cos(j\pi / n)).$$
The two sums agree under $j \mapsto n - j$. -/
theorem chebyshevDiscreteCoeff_eq (hn : n ≠ 0) (f : ℝ → ℝ) (k : ℕ) :
    chebyshevDiscreteCoeff n f k = 2 / (n * Chebyshev.lobattoFactor n k) *
      ∑ j ∈ Finset.range (n + 1), (Chebyshev.lobattoFactor n j)⁻¹ *
        cos ((k : ℝ) * (j : ℝ) * π / n) * f (Chebyshev.node n j) := by
  rw [chebyshevDiscreteCoeff, ← Finset.sum_range_reflect (fun j => (Chebyshev.lobattoFactor n j)⁻¹ *
    cos ((k : ℝ) * (j : ℝ) * π / n) * f (Chebyshev.node n j)) (n + 1)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [show n + 1 - 1 - j = n - j by omega, lobattoFactor_sub hj',
    chebyshevLobattoNode_eq_node hn hj']

/-- **Equations (10.29)–(10.31)** and **Exercise 10.2** of [quarteroni2000numerical], the Chebyshev
discrete transform. Let $n \ge 1$ and $f : \mathbb{R} \to \mathbb{R}$. The interpolating
polynomial $\Pi^{GL}_{n,w} f$ at the $n + 1$ Gauss–Lobatto nodes (10.21) is
$$\Pi^{GL}_{n,w} f = \sum_{k=0}^n \tilde f_k T_k, \tag{10.29}$$
with the coefficients $\tilde f_k = \frac{2}{n d_k} \sum_{j=0}^n d_j^{-1} T_k(\bar x_j) f(\bar
x_j)$ of (10.31). The inverse transform is
$$f(\bar x_j) = \sum_{k=0}^n T_k(\bar x_j) \tilde f_k, \qquad T_k(\bar x_j) =
  \cos\left(\frac{k(n - j)\pi}{n}\right). \tag{10.30}$$
Finally $\Pi^{GL}_{n,w} f$ equals the discrete truncation $f_n^*$ of (10.4) for the discrete
scalar product (10.28).

**Correction.** The book prints (10.30) and (10.31) with $\cos(kj\pi / n)$ in place of
$T_k(\bar x_j) = \cos(k(n - j)\pi / n)$. See
`QuarteroniSaccoSaleri.Chapter10.chebyshevDiscreteCoeff`.

The proof reindexes the backbone's `Polynomial.Chebyshev.interpolate_eq_sum_cdt`, whose
ingredients are the discrete norms `Polynomial.Chebyshev.discreteInner_T_T` of the hint of the
exercise, and uses `Quadrature.interpolate_eq_sum_discreteInner_smul`. -/
theorem equation_10_31 (hn : 1 ≤ n) (f : ℝ → ℝ) :
    (Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
        fun j => f (chebyshevLobattoNode n j)) =
      ∑ k ∈ Finset.range (n + 1), C (chebyshevDiscreteCoeff n f k) * Chebyshev.T ℝ k ∧
    (∀ j : Fin (n + 1), f (chebyshevLobattoNode n j) = ∑ k ∈ Finset.range (n + 1),
      cos ((k : ℝ) * ((n - j : ℕ) : ℝ) * π / n) * chebyshevDiscreteCoeff n f k) ∧
    (Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
        fun j => f (chebyshevLobattoNode n j)) =
      discreteTruncation chebyshevMeasure (fun j : Fin (n + 1) => Chebyshev.lobattoWeight n j)
        (fun j : Fin (n + 1) => chebyshevLobattoNode n j) n f := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hinj := injective_chebyshevLobattoNode hn0
  -- (10.29), from the backbone's transform at the reversed nodes
  have hcdt : (Lagrange.interpolate Finset.univ (fun j : Fin (n + 1) => chebyshevLobattoNode n j)
      fun j => f (chebyshevLobattoNode n j)) =
      ∑ k ∈ Finset.range (n + 1), C (chebyshevDiscreteCoeff n f k) * Chebyshev.T ℝ k := by
    have h := Chebyshev.interpolate_eq_sum_cdt hn0 f
    have hnodes : (fun j : Fin (n + 1) => Chebyshev.node n j) =
        (fun j : Fin (n + 1) => chebyshevLobattoNode n j) ∘ Fin.revPerm := by
      ext j
      exact (chebyshevLobattoNode_rev hn0 j).symm
    have hvals : (fun j : Fin (n + 1) => f (Chebyshev.node n j)) =
        fun j => f (((fun j : Fin (n + 1) => chebyshevLobattoNode n j) ∘ Fin.revPerm) j) := by
      ext j
      exact congrArg f (chebyshevLobattoNode_rev hn0 j).symm
    rw [hnodes, hvals, Lagrange.interpolate_comp_equiv hinj Fin.revPerm f] at h
    rw [h]
    exact Finset.sum_congr rfl fun k _ => by rw [chebyshevDiscreteCoeff_eq hn0]
  refine ⟨hcdt, fun j => ?_, ?_⟩
  · -- (10.30): evaluate (10.29) at `x̄ⱼ`
    have hj := Nat.lt_succ_iff.mp j.2
    have hev := Lagrange.eval_interpolate_at_node
      (fun j : Fin (n + 1) => f (chebyshevLobattoNode n j)) hinj.injOn (Finset.mem_univ j)
    rw [hcdt] at hev
    rw [← hev, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_C, chebyshevLobattoNode_eq_node hn0 hj, Chebyshev.node, Chebyshev.T_real_cos,
      mul_comm]
    congr 2
    push_cast
    ring
  · exact interpolate_eq_sum_discreteInner_smul isWeight_chebyshevMeasure hn hinj
      (fun j => Chebyshev.lobattoWeight_pos hn0 j) (isExactOnMeasure_chebyshevLobatto hn0) f

end QuarteroniSaccoSaleri.Chapter10
