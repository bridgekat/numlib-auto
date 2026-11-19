/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.OrthogonalPolynomial.LegendreBounds
import NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section02

/-!
# Quarteroni, Sacco and Saleri, Section 10.4: Legendre integration and interpolation

This module formalizes Section 10.4 of [quarteroni2000numerical], on Gaussian integration for the
Legendre weight $w \equiv 1$ on $(-1, 1)$. The Gauss nodes are the zeros of $L_{n+1}$, with weights
$\alpha_j = 2 / ((1 - x_j^2) L'_{n+1}(x_j)^2)$ (10.32). The Gauss–Lobatto nodes are $\bar x_0 = -1$,
$\bar x_n = 1$ and the zeros of $L_n'$ (10.33), with weights
$\bar\alpha_j = 2 / (n(n + 1) L_n(\bar x_j)^2)$ (10.34). The section states bounds on the
Gauss–Lobatto weights, which are proved here, and derives the discrete Legendre transform: the
interpolant at the Gauss–Lobatto nodes is $\sum_{k \le n} \tilde f_k L_k$ (10.38), with the inverse
transform $f(\bar x_j) = \sum_k \tilde f_k L_k(\bar x_j)$ (10.39) and the coefficients (10.40).

The Gauss and Gauss–Lobatto rules are (10.16) and (10.17)–(10.18) of Section 10.2 for the weight
`OrthogonalPolynomial.legendreMeasure`, related to the Legendre polynomials by
`OrthogonalPolynomial.family_eq_legendre`. The closed forms of the weights, the zeros of $L_n'$ and
the transform come from `Numlib.Approximation.GaussLobatto`, and the bounds on the weights from
`Numlib.Approximation.OrthogonalPolynomial.LegendreBounds`.

## Main definitions

* Equation (10.40), `QuarteroniSaccoSaleri.Chapter10.legendreDiscreteCoeff`: the coefficients
  $\tilde f_k$ of the discrete Legendre transform.

## Main results

* Equation (10.32), `QuarteroniSaccoSaleri.Chapter10.equation_10_32`: the $n + 1$ zeros of $L_{n+1}$
  exist, and with them the weights $2 / ((1 - x_j^2) L'_{n+1}(x_j)^2)$ are positive and give degree
  of exactness $2n + 1$.
* Equation (10.33), `QuarteroniSaccoSaleri.Chapter10.legendreLobatto_nodal_eq`: the nodal polynomial
  of the Legendre–Gauss–Lobatto nodes is the backbone's Gauss–Lobatto nodal polynomial.
* Equations (10.33)–(10.34), `QuarteroniSaccoSaleri.Chapter10.equation_10_34`: the
  Legendre–Gauss–Lobatto nodes exist, and for any such nodes the weights
  $2 / (n(n + 1) L_n(\bar x_j)^2)$ are positive and give degree of exactness $2n - 1$.
* Section 10.4, `QuarteroniSaccoSaleri.Chapter10.legendreLobattoNode_mem_Icc`: the
  Legendre–Gauss–Lobatto nodes lie in $[-1, 1]$, and $(1 - \bar x_j^2) L_n'(\bar x_j) = 0$.
* Section 10.4, `QuarteroniSaccoSaleri.Chapter10.legendreLobattoWeight_bounds`:
  $2 / (n(n + 1)) \le \bar\alpha_j \le C / n$, with $C$ independent of $n$.
* Equations (10.38)–(10.40) and Exercise 10.6, `QuarteroniSaccoSaleri.Chapter10.equation_10_40`: the
  discrete Legendre transform and its inverse, the discrete norms of the Legendre polynomials, and
  the equality of the interpolant with the discrete truncation $f_n^*$ of (10.4).

## Conventions

* Nodes are an injective family `x : Fin (n + 1) → ℝ`. "The zeros of $L_{n+1}$" means
  $L_{n+1}(x_j) = 0$ for all $j$; for $n + 1$ distinct points this is the full set of zeros, by
  counting.
* The Gauss–Lobatto nodes are described as the book describes them: $\bar x_0 = -1$, $\bar x_n = 1$,
  and $L_n'(\bar x_j) = 0$ for $0 < j < n$.
* Integrals are $\int_{-1}^1$, because the Legendre weight is the Lebesgue measure on $(-1, 1)$. The
  Legendre polynomial $L_k$ is `Polynomial.legendre k`.

## Implementation notes

* The estimates (10.36)–(10.37) belong to the group of spectral estimates that the book quotes
  without proof; the implementation notes of
  `NumlibSurface.QuarteroniSaccoSaleri.Chapter10.Section03` describe the theory that they need. Two
  facts make the Legendre case easier. First, the reduction is that of (10.27) for the
  Legendre–Gauss–Lobatto rule, which is exact on $\mathbb{P}_{2n-1}$:
  $(f, v_n) - (f, v_n)_n = (g, v_n) - (g, v_n)_n$ for $g = f - P_{n-1} f$, with
  $\|v_n\|_n \le \sqrt{3} \|v_n\|$ by the proved equivalence of norms, and
  $\|g\|_n \le \sqrt{2} \|g\|_\infty$ because the weights sum to $2$; (10.37) is then the case
  $v_n = 1$. Second, the coefficient identity of the projection estimate is $\hat f_k = -(k(k +
  1))^{-1} \widehat{((1 - x^2) f')'}_k$. It follows from `Polynomial.legendre_ode` and one
  integration by parts on $[-1, 1]$, whose boundary terms vanish because of the factor $1 - x^2$.
  Parseval's equality in $L^2(-1, 1)$ is `OrthogonalPolynomial.hilbertBasis` with
  `OrthogonalPolynomial.family_eq_legendre`.

## Deviations from the source

* **Equation (10.34)** (reading). `equation_10_34` evaluates $L_n$ in the weight denominator at
  the Lobatto nodes $\bar x_j$. The printed denominator uses $x_j$, which labels the Gauss nodes
  in (10.32). `legendreLobattoWeight_bounds` also applies to repeated choices from the Lobatto
  nodes.
* **Equation (10.40)** (generalization). `legendreDiscreteCoeff` is a total expression on
  arbitrary nodes, including $n=0$ and $k>n$. The transform theorem uses the distinct Lobatto
  nodes and the stated coefficient range.

## Not formalized

* **Equations (10.36)–(10.37)**, the estimates $|(f, v_n) - (f, v_n)_n| \le C n^{-s} \|f\|_s
  \|v_n\|_{L^2(-1,1)}$ for $v_n \in \mathbb{P}_n$, and $|\int_{-1}^1 f - I^{GL}_n f| \le C n^{-s}
  \|f\|_s$, together with the Legendre forms of (10.22) and (10.24) in the norm (10.35). The book
  quotes them from Canuto, Hussaini, Quarteroni and Zang (1988) without proof, and the library has
  no theory of spectral projection in weighted Sobolev norms.
-/

open MeasureTheory Polynomial OrthogonalPolynomial Quadrature Real Set Filter Topology

namespace QuarteroniSaccoSaleri.Chapter10

variable {n : ℕ}

/-! ### The Legendre–Gauss formula (10.32) -/

/-- **Equation (10.32)** of [quarteroni2000numerical], the Legendre–Gauss formula. Let $n \ge 0$.
The Legendre polynomial $L_{n+1}$ has $n + 1$ distinct zeros $x_0, \dots, x_n$. For any $n + 1$
distinct zeros $x_0, \dots, x_n$ of $L_{n+1}$, the coefficients
$$\alpha_j = \frac{2}{(1 - x_j^2) [L'_{n+1}(x_j)]^2}, \qquad j = 0, \dots, n,$$
are positive, and the formula has degree of exactness $2n + 1$:
$$\sum_j \alpha_j p(x_j) = \int_{-1}^1 p(x) \, dx \quad \text{for every } p \in
  \mathbb{P}_{2n+1}.$$

The zeros of $L_{n+1}$ are those of the monic orthogonal polynomial of the Legendre weight
(`OrthogonalPolynomial.family_eq_legendre`), so the nodes are the Gauss nodes (10.16). The
closed form of the interpolatory weights is `Quadrature.legendreGaussWeight_eq`. -/
theorem equation_10_32 (n : ℕ) :
    (∃ x : Fin (n + 1) → ℝ, Function.Injective x ∧ ∀ j, (legendre (n + 1)).eval (x j) = 0) ∧
      ∀ x : Fin (n + 1) → ℝ, Function.Injective x → (∀ j, (legendre (n + 1)).eval (x j) = 0) →
        (∀ j, 0 < 2 / ((1 - x j ^ 2) * (derivative (legendre (n + 1))).eval (x j) ^ 2)) ∧
        ∀ p : ℝ[X], p.degree ≤ ((2 * n + 1 : ℕ) : WithBot ℕ) →
          ∑ j, 2 / ((1 - x j ^ 2) * (derivative (legendre (n + 1))).eval (x j) ^ 2) * p.eval (x j) =
            ∫ t in (-1 : ℝ)..1, p.eval t := by
  have hw := isWeight_legendreMeasure
  have hfam : ∀ x : ℝ, (family legendreMeasure (n + 1)).eval x = 0 ↔
      (legendre (n + 1)).eval x = 0 := fun x => by
    rw [family_eq_legendre, eval_mul, eval_C, mul_eq_zero, or_iff_right
      (inv_ne_zero (leadingCoeff_ne_zero.mpr (legendre_ne_zero (n + 1))))]
  refine ⟨?_, fun x hx hroot => ?_⟩
  · obtain ⟨x, hx, hroot⟩ := exists_gauss_nodes hw n
    exact ⟨x, hx, fun j => (hfam _).mp (hroot j)⟩
  set α : Fin (n + 1) → ℝ := fun j => ∫ t, (Lagrange.basis Finset.univ x j).eval t ∂legendreMeasure
    with hα
  have hint : IsInterpolatoryMeasure legendreMeasure α x := fun j => rfl
  have hexact : IsExactOnMeasure legendreMeasure α x (2 * n + 1) :=
    (equation_10_16 hw hx α).mpr ⟨fun j => (hfam _).mpr (hroot j), hint⟩
  have hform : ∀ j, α j = 2 / ((1 - x j ^ 2) * (derivative (legendre (n + 1))).eval (x j) ^ 2) :=
    fun j => legendreGaussWeight_eq hx hint hroot j
  refine ⟨fun j => hform j ▸ pos_of_isExactOnMeasure_of_le hw hx (by omega) hexact j,
    fun p hp => ?_⟩
  rw [← integral_legendreMeasure, ← hexact p hp]
  exact Finset.sum_congr rfl fun j _ => by rw [hform j]

/-! ### The Legendre–Gauss–Lobatto formula (10.33)–(10.34) -/

/-- Supports equation (10.33), the nodal polynomial of the Legendre–Gauss–Lobatto nodes. Let
$n \ge 1$, and let $\bar x_0, \dots, \bar x_n$ be distinct points with $\bar x_0 = -1$,
$\bar x_n = 1$ and $L_n'(\bar x_j) = 0$ for $0 < j < n$. Then the nodal polynomial of these
points is the backbone's Gauss–Lobatto nodal polynomial
`Quadrature.lobattoNodal legendreMeasure n`.

That polynomial is $(x^2 - 1) q_{n-1}$, where $L_n'$ is a nonzero multiple of $q_{n-1}$
(`Quadrature.derivative_legendre_eq_family`). So it vanishes at every node. -/
theorem legendreLobatto_nodal_eq (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (h0 : x 0 = -1) (hl : x (Fin.last n) = 1)
    (hint : ∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n →
      (derivative (legendre n)).eval (x j) = 0) :
    Lagrange.nodal Finset.univ x = lobattoNodal legendreMeasure n := by
  have hder := derivative_legendre_eq_family hn
  have hc : (n : ℝ) * (legendre n).leadingCoeff ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0))
      (leadingCoeff_ne_zero.mpr (legendre_ne_zero n))
  refine Lagrange.nodal_eq_of_forall_eval_eq_zero hx (lobattoNodal_monic _ _)
    (natDegree_eq_of_degree_eq_some (degree_lobattoNodal _ hn)) fun j => ?_
  rw [lobattoNodal, eval_mul, eval_sub, eval_pow, eval_X, eval_one]
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [h0]
    norm_num
  rcases eq_or_ne j (Fin.last n) with rfl | hjl
  · rw [hl]
    norm_num
  have hq : (family (lobattoMeasure legendreMeasure) (n - 1)).eval (x j) = 0 := by
    have h := hint j (Nat.pos_of_ne_zero (fun h => hj0 (Fin.ext h)))
      (lt_of_le_of_ne (Nat.lt_succ_iff.mp j.2) (fun h => hjl (Fin.ext h)))
    rw [hder, eval_mul, eval_C, mul_eq_zero] at h
    exact h.resolve_left hc
  rw [hq, mul_zero]

/-- **Equations (10.33)–(10.34)** of [quarteroni2000numerical], the Legendre–Gauss–Lobatto formula.
Let $n \ge 1$. There are $n + 1$ distinct points $\bar x_0, \dots, \bar x_n$ with
$\bar x_0 = -1$, $\bar x_n = 1$ and $L_n'(\bar x_j) = 0$ for $j = 1, \dots, n - 1$; these are
the Gauss–Lobatto nodes (10.33). For any such family of points:

* every zero of $L_n'$ in $(-1, 1)$ is one of the nodes;
* $L_n(\bar x_j) \neq 0$ for every $j$;
* the weights $\bar\alpha_j = \frac{2}{n(n + 1)} \frac{1}{[L_n(\bar x_j)]^2}$,
  $j = 0, \dots, n$, of (10.34) are positive;
* the formula has degree of exactness $2n - 1$: $\sum_j \bar\alpha_j p(\bar x_j) = \int_{-1}^1
  p(x) \, dx$ for every $p \in \mathbb{P}_{2n-1}$.

Here $L_n$ is the Legendre polynomial (10.12) of degree $n$. The existence is (10.17)–(10.18)
for the Legendre weight, with `Quadrature.derivative_legendre_eq_family`. The weights are
`Quadrature.legendreLobattoWeight_eq`.

**Reading.** Evaluate the denominator at the Lobatto nodes $\bar x_j$ from (10.33). The source
prints $x_j$, which it uses for the Gauss nodes in (10.32). -/
theorem equation_10_34 (hn : 1 ≤ n) :
    (∃ x : Fin (n + 1) → ℝ, Function.Injective x ∧ x 0 = -1 ∧ x (Fin.last n) = 1 ∧
      ∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n → (derivative (legendre n)).eval (x j) = 0) ∧
    ∀ x : Fin (n + 1) → ℝ, Function.Injective x → x 0 = -1 → x (Fin.last n) = 1 →
      (∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n → (derivative (legendre n)).eval (x j) = 0) →
      (∀ t ∈ Ioo (-1 : ℝ) 1, (derivative (legendre n)).eval t = 0 → ∃ j, x j = t) ∧
      (∀ j, (legendre n).eval (x j) ≠ 0) ∧
      (∀ j, 0 < 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2)) ∧
      ∀ p : ℝ[X], p.degree ≤ ((2 * n - 1 : ℕ) : WithBot ℕ) →
        ∑ j, 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2) * p.eval (x j) =
          ∫ t in (-1 : ℝ)..1, p.eval t := by
  have hw := isWeight_legendreMeasure
  have hsupp := legendreMeasure_compl_Icc
  have hder := derivative_legendre_eq_family hn
  have hc : (n : ℝ) * (legendre n).leadingCoeff ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0))
      (leadingCoeff_ne_zero.mpr (legendre_ne_zero n))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · obtain ⟨x, α, hxinj, hx0, hxlast, -, -, -, hnodal, -⟩ := exists_gaussLobatto hw hsupp hn
    refine ⟨x, hxinj, hx0, hxlast, fun j hj0 hjn => ?_⟩
    have hroot : (lobattoNodal legendreMeasure n).eval (x j) = 0 := by
      rw [← hnodal]
      exact Lagrange.eval_nodal_at_node (Finset.mem_univ j)
    have hne : x j ^ 2 - 1 ≠ 0 := by
      intro h
      have h' : (x j - 1) * (x j + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact absurd (hxinj (hxlast.trans (by linarith) : x (Fin.last n) = x j))
          (fun h => by have := congrArg Fin.val h; simp at this; omega)
      · exact absurd (hxinj (hx0.trans (by linarith) : x 0 = x j))
          (fun h => by have := congrArg Fin.val h; simp at this; omega)
    rw [lobattoNodal, eval_mul, eval_sub, eval_pow, eval_X, eval_one, mul_eq_zero] at hroot
    rw [hder, eval_mul, hroot.resolve_left hne, mul_zero]
  · intro x hx h0 hl hint
    have hnodal := legendreLobatto_nodal_eq hn hx h0 hl hint
    set α : Fin (n + 1) → ℝ :=
      fun j => ∫ t, (Lagrange.basis Finset.univ x j).eval t ∂legendreMeasure with hα
    have hintα : IsInterpolatoryMeasure legendreMeasure α x := fun j => rfl
    have hexact := isExactOnMeasure_of_nodal_eq_lobattoNodal hw hsupp hn hx hintα hnodal
    have hform : ∀ j, α j = 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2) := fun j =>
      legendreLobattoWeight_eq hn hx hintα hnodal j
    have hLn : ∀ j, (legendre n).eval (x j) ≠ 0 := fun j =>
      legendre_eval_ne_zero_of_nodal_eq_lobattoNodal hn hx hnodal j
    refine ⟨fun t ht hroot => ?_, hLn, fun j => by have := hLn j; positivity, fun p hp => ?_⟩
    · rw [Lagrange.exists_eq_iff_eval_nodal_eq_zero, hnodal, lobattoNodal, eval_mul]
      rw [hder, eval_mul, eval_C, mul_eq_zero] at hroot
      rw [hroot.resolve_left hc, mul_zero]
    · rw [← integral_legendreMeasure, ← hexact p hp]
      exact Finset.sum_congr rfl fun j _ => by rw [hform j]

/-! ### The bounds on the Gauss–Lobatto weights -/

/-- Supports the bounds on the Gauss–Lobatto weights in Section 10.4. Let $n \ge 1$, and let
$\bar x_0, \dots, \bar x_n$ be points with $\bar x_0 = -1$, $\bar x_n = 1$ and
$L_n'(\bar x_j) = 0$ for $0 < j < n$. Then every node lies in $[-1, 1]$, and
$(1 - \bar x_j^2) L_n'(\bar x_j) = 0$.

At the two endpoints the factor $1 - x^2$ vanishes. An interior node is a zero of $L_n'$, hence
a zero of the orthogonal polynomial of degree $n - 1$ for the weight $(1 - x^2)\,dx$
(`Quadrature.derivative_legendre_eq_family`), and the zeros of an orthogonal polynomial lie
inside the interval that carries its weight. -/
theorem legendreLobattoNode_mem_Icc (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (h0 : x 0 = -1)
    (hl : x (Fin.last n) = 1)
    (hint : ∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n →
      (derivative (legendre n)).eval (x j) = 0) (j : Fin (n + 1)) :
    x j ∈ Icc (-1 : ℝ) 1 ∧ (1 - x j ^ 2) * (derivative (legendre n)).eval (x j) = 0 := by
  rcases eq_or_ne (j : ℕ) 0 with hj0 | hj0
  · rw [show j = 0 from Fin.ext hj0, h0]
    norm_num
  rcases eq_or_ne (j : ℕ) n with hjn | hjn
  · rw [show j = Fin.last n from Fin.ext (by simpa using hjn), hl]
    norm_num
  have hroot := hint j (Nat.pos_of_ne_zero hj0)
    (lt_of_le_of_ne (Nat.lt_succ_iff.mp j.2) hjn)
  refine ⟨?_, by rw [hroot, mul_zero]⟩
  have hw := isWeight_legendreMeasure
  have hsupp := legendreMeasure_compl_Icc
  have hc : (n : ℝ) * (legendre n).leadingCoeff ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0))
      (leadingCoeff_ne_zero.mpr (legendre_ne_zero n))
  have hfam : (family (lobattoMeasure legendreMeasure) (n - 1)).eval (x j) = 0 := by
    rw [derivative_legendre_eq_family hn, eval_mul, eval_C, mul_eq_zero] at hroot
    exact hroot.resolve_left hc
  exact Ioo_subset_Icc_self
    (root_family_mem_Ioo (isWeight_lobattoMeasure hw hsupp) (lobattoMeasure_compl_Icc hsupp) hfam)

/-- **Section 10.4** of [quarteroni2000numerical], the bounds on the Legendre–Gauss–Lobatto weights
stated after (10.34). There is a constant $C$ such that for every $n \ge 1$ and every family of
points $\bar x_0, \dots, \bar x_n$ with $\bar x_0 = -1$, $\bar x_n = 1$ and $L_n'(\bar x_j) = 0$
for $0 < j < n$, the weights $\bar\alpha_j = 2 / (n(n + 1) L_n(\bar x_j)^2)$ of (10.34) satisfy
$$\frac{2}{n(n + 1)} \le \bar\alpha_j \le \frac{C}{n}, \qquad j = 0, \dots, n.$$

The book quotes this from Bernardi and Maday. The proof gives the explicit constant $C = 8$ from
two bounds of `Numlib.Approximation.OrthogonalPolynomial.LegendreBounds`:
$L_n(\bar x_j)^2 \le 1$ on $[-1, 1]$ gives the lower bound, and $L_n(\bar x_j)^2 \ge 1/(4n)$ at
a point where $(1 - x^2) L_n'$ vanishes gives the upper bound. The nodes need not be distinct.

**Generalization.** The bounds also hold pointwise for repetitions of the Lobatto nodes, since
they depend only on the node values. -/
theorem legendreLobattoWeight_bounds :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ x : Fin (n + 1) → ℝ, x 0 = -1 → x (Fin.last n) = 1 →
      (∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n →
        (derivative (legendre n)).eval (x j) = 0) →
      ∀ j : Fin (n + 1),
        2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
            2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2) ∧
          2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2) ≤ c / n := by
  refine ⟨8, fun n hn x h0 hl hint j => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hmem, hcrit⟩ := legendreLobattoNode_mem_Icc hn h0 hl hint j
  have hup : (legendre n).eval (x j) ^ 2 ≤ 1 := eval_legendre_sq_le_one n hmem
  have hlow : 1 / (4 * (n : ℝ)) ≤ (legendre n).eval (x j) ^ 2 :=
    inv_le_eval_legendre_sq hn hmem hcrit
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (n : ℝ))] at hlow
  have hpos : 0 < (legendre n).eval (x j) ^ 2 := by nlinarith [hnR, hlow]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((n : ℝ) * ((n : ℝ) + 1)))
      (by linarith : (0 : ℝ) ≤ 1 - (legendre n).eval (x j) ^ 2)]
  · rw [div_le_div_iff₀ (by positivity) hnR]
    nlinarith [hnR, hlow,
      mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1))
        (by linarith : (0 : ℝ) ≤ (legendre n).eval (x j) ^ 2 * (4 * (n : ℝ)) - 1)]

/-! ### The discrete Legendre transform (10.38)–(10.40) -/

/-- **Equation (10.40)** of [quarteroni2000numerical], the coefficients of the discrete Legendre
transform (DLT) at Gauss–Lobatto nodes $\bar x_0, \dots, \bar x_n$:
$$\tilde f_k = \frac{2k + 1}{n(n + 1)} \sum_{j=0}^n \frac{L_k(\bar x_j) f(\bar x_j)}{L_n(\bar
  x_j)^2}, \quad k = 0, \dots, n - 1, \qquad \tilde f_n = \frac{1}{n + 1} \sum_{j=0}^n
  \frac{f(\bar x_j)}{L_n(\bar x_j)}.$$

The definition is given for every natural number $k$: the first formula is used for every
$k \neq n$.

**Generalization.** The finite formula is total on arbitrary nodes and extends to $n=0$ and
$k>n$. -/
noncomputable def legendreDiscreteCoeff (n : ℕ) (x : Fin (n + 1) → ℝ) (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  if k = n then 1 / ((n : ℝ) + 1) * ∑ j, f (x j) / (legendre n).eval (x j)
  else (2 * k + 1) / ((n : ℝ) * ((n : ℝ) + 1)) *
    ∑ j, (legendre k).eval (x j) * f (x j) / (legendre n).eval (x j) ^ 2

/-- **Equations (10.38)–(10.40)** and **Exercise 10.6** of [quarteroni2000numerical], the discrete
Legendre transform. Let $n \ge 1$, let $\bar x_0, \dots, \bar x_n$ be distinct points with
$\bar x_0 = -1$, $\bar x_n = 1$ and $L_n'(\bar x_j) = 0$ for $0 < j < n$, and let $\bar\alpha_j$
be the weights of (10.34). Then for every $f : \mathbb{R} \to \mathbb{R}$:

* the interpolating polynomial at the nodes is $\Pi^{GL}_n f = \sum_{k=0}^n \tilde f_k L_k$
  (10.38), with the coefficients $\tilde f_k$ of (10.40);
* the inverse transform is $f(\bar x_j) = \sum_{k=0}^n \tilde f_k L_k(\bar x_j)$ (10.39);
* $\Pi^{GL}_n f$ equals the discrete truncation $f_n^*$ of (10.4) for the discrete scalar
  product $(\cdot, \cdot)_n$ of the rule;
* for $k, l \le n$ the Legendre polynomials satisfy $(L_k, L_l)_n = 0$ if $k \neq l$,
  $(L_k, L_k)_n = 2 / (2k + 1)$ if $k < n$, and $(L_n, L_n)_n = 2 / n$. This is the hint of the
  exercise.

The proof specializes the backbone's `Quadrature.interpolate_eq_sum_dlt` and
`Quadrature.discreteInner_legendre_legendre`. -/
theorem equation_10_40 (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (h0 : x 0 = -1) (hl : x (Fin.last n) = 1)
    (hint : ∀ j : Fin (n + 1), 0 < (j : ℕ) → (j : ℕ) < n → (derivative (legendre n)).eval (x j) = 0)
    (f : ℝ → ℝ) :
    (Lagrange.interpolate Finset.univ x fun j => f (x j)) =
        ∑ k ∈ Finset.range (n + 1), C (legendreDiscreteCoeff n x f k) * legendre k ∧
      (∀ j, f (x j) = ∑ k ∈ Finset.range (n + 1),
        legendreDiscreteCoeff n x f k * (legendre k).eval (x j)) ∧
      (Lagrange.interpolate Finset.univ x fun j => f (x j)) =
        discreteTruncation legendreMeasure
          (fun j => 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2)) x n f ∧
      ∀ k l, k ≤ n → l ≤ n →
        discreteInner (fun j => 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2)) x
            (fun t => (legendre k).eval t) (fun t => (legendre l).eval t) =
          if k = l then (if k = n then (2 : ℝ) / n else 2 / (2 * (k : ℝ) + 1)) else 0 := by
  have hw := isWeight_legendreMeasure
  have hsupp := legendreMeasure_compl_Icc
  have hnodal := legendreLobatto_nodal_eq hn hx h0 hl hint
  set α : Fin (n + 1) → ℝ := fun j => 2 / ((n : ℝ) * ((n : ℝ) + 1) * (legendre n).eval (x j) ^ 2)
    with hα
  have hintα : IsInterpolatoryMeasure legendreMeasure α x := fun j =>
    (legendreLobattoWeight_eq hn hx (fun _ => rfl) hnodal j).symm
  have hexact := isExactOnMeasure_of_nodal_eq_lobattoNodal hw hsupp hn hx hintα hnodal
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : ∀ j, 0 < α j := fun j => by
    have := legendre_eval_ne_zero_of_nodal_eq_lobattoNodal hn hx hnodal j
    positivity
  have hdlt := interpolate_eq_sum_dlt hn hx hpos hintα hnodal hexact f
  refine ⟨hdlt, fun j => ?_, ?_, fun k l hk hl => ?_⟩
  · have hev := Lagrange.eval_interpolate_at_node (fun j => f (x j)) hx.injOn (Finset.mem_univ j)
    rw [hdlt, eval_finsetSum] at hev
    rw [← hev]
    exact Finset.sum_congr rfl fun k _ => by rw [eval_mul, eval_C, legendreDiscreteCoeff]
  · exact interpolate_eq_sum_discreteInner_smul hw hn hx hpos hexact f
  · exact discreteInner_legendre_legendre hn hx hintα hnodal hexact hk hl

end QuarteroniSaccoSaleri.Chapter10
