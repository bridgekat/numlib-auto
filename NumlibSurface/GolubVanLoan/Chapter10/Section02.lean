/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.GaussLobatto
import Numlib.Krylov.Quadrature
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub and Van Loan, Section 10.2: Lanczos, quadrature, and approximation

This module formalizes §10.2 of [golub2013matrix], which estimates quadratic forms $u^T f(A) u$ for
a symmetric $A \in \mathbb{R}^{n \times n}$ by Gauss quadrature. With the Schur decomposition
$A = X \Lambda X^T$, the quadratic form is the Riemann–Stieltjes integral
$u^T f(A) u = \int f(\lambda) \, dw(\lambda)$ against a step function $w$ whose jumps are the
squared components $[X^T u]_i^2$ ((10.2.2)–(10.2.6)). The module proves the existence of the Gauss,
Gauss–Radau and Gauss–Lobatto rules (10.2.7)–(10.2.10) for a general weight, their remainders, and
the two-sided bound for $f(\lambda) = 1/\lambda^2$. It proves Facts 1 and 2 of §10.2.3 on orthogonal
polynomials and Jacobi matrices, and the three-term recurrence (10.2.13) of the Lanczos polynomials.
It then shows that $k$ steps of the Lanczos process give the Gauss rule of the spectral weight (Fact
3 with (10.2.11)–(10.2.12)) and, after a modification of $T_{k+1}$, the Gauss–Radau rule (§10.2.5),
and it proves the bounds $b_k \le u^T f(A) u \le B_k$ of §10.2.6. The module starts with the
identity that motivates the section: the squared error of an approximate solution of $Ax = b$ is
such a quadratic form.

The proofs specialize the backbone modules `Numlib.Approximation.Quadrature`,
`Numlib.Approximation.GaussLobatto` and `Numlib.Approximation.OrthogonalPolynomial` (quadrature
rules of a measure, their remainders, and orthogonal polynomials), and
`Numlib.Krylov.OrthogonalPolynomials` and `Numlib.Krylov.Quadrature` (the spectral measure, the
Lanczos polynomials, and the quadrature rules that the Lanczos process computes).

## Main definitions

* Equation (10.2.2), `GolubVanLoan.Chapter10.stepWeight`: the step weight with jumps
  $w_\mu - w_{\mu+1}$ at the points $\lambda_\mu$.
* Equation (10.2.5), `GolubVanLoan.Chapter10.spectralWeight`: the spectral weight $w(\lambda) =
  \sum_{\lambda_i \le \lambda} [X^T u]_i^2$ of $A$ and $u$.

## Main results

* §10.2, `GolubVanLoan.Chapter10.norm_error_sq_eq_residual`: $\|A^{-1} b - x\|_2^2 = r^T A^{-2} r$
  for the residual $r = b - Ax$.
* Equation (10.2.3), `GolubVanLoan.Chapter10.equation_10_2_3`: the integral against the step weight
  is $\sum_\mu (w_\mu - w_{\mu+1}) f(\lambda_\mu)$.
* Equation (10.2.6), `GolubVanLoan.Chapter10.equation_10_2_6`: $u^T f(A) u = \sum_i [X^T u]_i^2
  f(\lambda_i) = \int f \, dw$.
* Equation (10.2.7), `GolubVanLoan.Chapter10.equation_10_2_7`: the $k$-point Gauss rule exists and
  is exact to degree $2k - 1$.
* Equations (10.2.8) and (10.2.9), `GolubVanLoan.Chapter10.equation_10_2_8` and
  `GolubVanLoan.Chapter10.equation_10_2_9`: the Gauss–Radau rules with the prescribed node $a$ or
  $b$ exist and are exact to degree $2k$.
* Equation (10.2.10), `GolubVanLoan.Chapter10.equation_10_2_10`: the Gauss–Lobatto rule exists and
  is exact to degree $2k + 1$.
* §10.2.2, `GolubVanLoan.Chapter10.gauss_remainder`, `GolubVanLoan.Chapter10.gaussRadau_remainder`
  and `GolubVanLoan.Chapter10.gaussLobatto_remainder`: the remainders of the three kinds of rules.
* §10.2.2, `GolubVanLoan.Chapter10.gauss_le_integral_le_gaussRadau`: for $f(\lambda) = 1/\lambda^2$
  and $0 < a$, the Gauss rule and the Gauss–Radau rule bracket the integral.
* Fact 1 of §10.2.3, `GolubVanLoan.Chapter10.orthonormalPolynomials_threeTerm`: the orthonormal
  polynomials of a weight satisfy a three-term recurrence and are unique up to sign.
* Fact 2 of §10.2.3, `GolubVanLoan.Chapter10.roots_orthonormalPolynomial_eq_eigenvalues`: the zeros
  of $p_k$ are the eigenvalues of the Jacobi matrix $T_k$, and they are distinct.
* Equation (10.2.13), `GolubVanLoan.Chapter10.equation_10_2_13`: $q_{j+1} = p_j(A) u$ for the
  Lanczos polynomials, which satisfy the Lanczos recurrence.
* §10.2.4, `GolubVanLoan.Chapter10.lanczosPolynomials_orthonormal`: the Lanczos polynomials are
  orthonormal for the spectral weight.
* Equation (10.2.12), `GolubVanLoan.Chapter10.equation_10_2_12`: the eigenvalues $\theta_j$ of $T_k$
  and the weights $\|u\|^2 s_{1j}^2$ form a rule that is exact to degree $2k - 1$ for the spectral
  weight.
* §10.2.4, `GolubVanLoan.Chapter10.lanczos_gaussRule`: the remainder of the Gauss rule computed by
  Lanczos.
* §10.2.5, `GolubVanLoan.Chapter10.gaussRadau_tridiag`: $a$ is an eigenvalue of the modified matrix
  $\tilde T_{k+1}$.
* §10.2.5, `GolubVanLoan.Chapter10.gaussRadau_via_lanczos`: the eigenpairs of $\tilde T_{k+1}$ give
  a rule with the node $a$ that is exact to degree $2k$.
* §10.2.6, `GolubVanLoan.Chapter10.lanczos_quadrature_bounds`: $b_k \le u^T f(A) u \le B_k$ when
  $f^{(2k)} \ge 0 \ge f^{(2k+1)}$ on $[a, b]$.

## Conventions

* The conventions of §10.1 (`NumlibSurface.GolubVanLoan.Chapter10.Section01`) apply. The matrix
  function $f(A)$ is `cfc f A`.
* A Riemann–Stieltjes integral $\int_a^b f \, dw$ is the Lebesgue–Stieltjes integral against
  `StieltjesFunction.measure` of $w$. For the continuous integrands of the section the two agree.
* A general weight on $[a, b]$ is a measure $\mu$ with `OrthogonalPolynomial.IsWeight μ` (every
  moment is finite and $\mu$ is not carried by a finite set, so every Gauss rule exists) that is
  carried by $[a, b]$, that is, `μ (Set.Icc a b)ᶜ = 0`. The spectral weight (10.2.5) is carried by a
  finite set, so its rules exist only up to the grade of $u$; for this reason the statements about
  the Lanczos rules assume $\dim \mathcal{K}(A, u, k) = k$.
* A quadrature rule with $k$ nodes is a pair of families `t` (nodes) and `w` (weights) indexed by
  `Fin k`. Exactness to degree $d$ is `Quadrature.IsExactOnMeasure μ w t d`.
* The Lanczos quantities are those of `toEuclideanLin A` started at $u$, which need not be a unit
  vector. The matrix $T_k$ is `Lanczos.tridiag (toEuclideanLin A) u k`, with the orthonormal
  eigenvectors $s_j$ and the eigenvalues $\theta_j$ of `Lanczos.tridiag_isHermitian`; indices are
  0-based, so the source's $s_{1j}$ is the entry $0$ of $s_j$. The Lanczos polynomials are
  `Lanczos.poly`, normalized by $p_0 = 1/\|u\|$, so that $q_{j+1} = p_j(A) u$.

## Deviations from the source

* **Remainder of the Gauss rule, §10.2.2** (typo). The source prints $(2n)!$; the rule has $k$ nodes
  and the factor is $(2k)!$. See `GolubVanLoan.Chapter10.gauss_remainder`.
* **Remainder of the Gauss–Lobatto rule, §10.2.2** (typo). The source's list prints this remainder
  as $R_{GG}$. See `GolubVanLoan.Chapter10.gaussLobatto_remainder`.
* **(10.2.13)** (correction). The source prints the recurrence with $\beta_{k-1}^2$, which is the
  recurrence of the monic polynomials $\det(\lambda I - T_k)$; the Lanczos polynomials have
  $\beta_j$. See `GolubVanLoan.Chapter10.equation_10_2_13`.
* **(10.2.13)** (typo). The source writes $q_k = p_k(A) q_1$ for a polynomial of degree $k$; the
  index is off by one. See `GolubVanLoan.Chapter10.equation_10_2_13`.
* **(10.2.12)** (generalization). The source's weights $s_{1j}^2$ assume $\|u\| = 1$; the statement
  holds for every $u$, with the weights $\|u\|^2 s_{1j}^2$. See
  `GolubVanLoan.Chapter10.equation_10_2_12`.
* **Gauss rule by Lanczos, §10.2.4** (generalization). The source locates $\eta$ in
  $[\lambda_n, \lambda_1]$; the statement allows any interval that contains the spectrum. See
  `GolubVanLoan.Chapter10.lanczos_gaussRule`.
* **Gauss–Radau modification, §10.2.5** (typo). The source prints $\beta_{k+1}^2$ for $\beta_k^2$ in
  $\tilde\alpha_{k+1}$, and its display of $\tilde T_{k+1}$ omits $\beta_k$ above the diagonal. See
  `GolubVanLoan.Chapter10.gaussRadau_tridiag`.

## Not formalized

* **The Riemann–Stieltjes sums of §10.2.1.**
* **The Golub–Welsch weight formula of Fact 3 for a general weight.** The source uses Fact 3 only
  through §10.2.4, where it is formalized for the spectral weight.
* **The strict location $a < \eta < b$ in the remainders of the Gauss–Radau and Gauss–Lobatto
  rules.** The statements give $\eta \in [a, b]$, which is what the mean value argument of the
  backbone gives.
* **Numerical remarks.**
-/

open MeasureTheory Polynomial Matrix Krylov Quadrature OrthogonalPolynomial
open GolubVanLoan.Chapter01

namespace GolubVanLoan.Chapter10

/-! ### Errors from residuals (§10.2, introduction) -/

/-- **Section 10.2** of [golub2013matrix], the error from the residual (the display before §10.2.1).
Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let $b, x \in \mathbb{R}^n$,
let $x_* = A^{-1} b$ and let $r = b - Ax$. Then
$$\|x_* - x\|_2^2 = r^T f(A) r, \qquad f(\lambda) = 1/\lambda^2.$$
So the norm of the error is a quadratic form $u^T f(A) u$ of the kind that §10.2 estimates.

The source's approximate solution $\hat x$ is `x`, and $f(A)$ is `cfc f A`. The proof uses
Mathlib's `cfc_inv` and `cfc_pow_id` to get $f(A) = (A^2)^{-1} = A^{-1} A^{-1}$. -/
theorem norm_error_sq_eq_residual {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (b x : Fin n → ℝ) :
    (A⁻¹ *ᵥ b - x) ⬝ᵥ (A⁻¹ *ᵥ b - x) =
      (b - A *ᵥ x) ⬝ᵥ (cfc (fun t : ℝ => (t ^ 2)⁻¹) A *ᵥ (b - A *ᵥ x)) := by
  have hU : IsUnit A := hA.isUnit
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hU
  have e1 : A⁻¹ *ᵥ b - x = A⁻¹ *ᵥ (b - A *ᵥ x) := by
    rw [mulVec_sub, mulVec_mulVec, nonsing_inv_mul _ hd, one_mulVec]
  have h0 : ∀ t ∈ spectrum ℝ A, t ^ 2 ≠ 0 := fun t ht =>
    pow_ne_zero 2 fun h => spectrum.zero_notMem ℝ hU (h ▸ ht)
  have hcfc : cfc (fun t : ℝ => (t ^ 2)⁻¹) A = A⁻¹ * A⁻¹ := by
    have h1 : cfc (fun t : ℝ => (t ^ 2)⁻¹) A = Ring.inverse (cfc (fun t : ℝ => t ^ 2) A) :=
      cfc_inv (fun t : ℝ => t ^ 2) A h0 (ha := hA.1)
    have h2 : cfc (fun t : ℝ => t ^ 2) A = A ^ 2 := cfc_pow_id A 2 (ha := hA.1)
    rw [h1, h2, sq,
      Ring.inverse_mul (Or.inl hU), ← nonsing_inv_eq_ringInverse]
  have hsym : A⁻¹ᵀ = A⁻¹ := by
    rw [transpose_nonsing_inv, ← conjTranspose_eq_transpose_of_trivial, hA.1]
  rw [e1, hcfc, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, hsym]
  exact dotProduct_comm _ _

/-! ### Gauss-type rules for a weight (§10.2.2) -/

section Rules

variable {μ : Measure ℝ}

/-- **Equation (10.2.7)** of [golub2013matrix], the Gauss rule. Let $\mu$ be a weight, that is, a
measure on $\mathbb{R}$ with finite moments that is not carried by a finite set, and let
$k \in \mathbb{N}$. Then there are distinct nodes $t_1, \dots, t_k$ and positive weights
$w_1, \dots, w_k$ such that
$$\int p \, d\mu = \sum_{i=1}^k w_i p(t_i)$$
for every polynomial $p$ of degree at most $2k - 1$.

The weight hypothesis is `OrthogonalPolynomial.IsWeight μ`. The proof specializes
`Quadrature.exists_gauss`. -/
theorem equation_10_2_7 (hw : IsWeight μ) (k : ℕ) :
    ∃ t w : Fin k → ℝ, Function.Injective t ∧ (∀ i, 0 < w i) ∧
      ∀ p : ℝ[X], p.degree < ((2 * k : ℕ) : WithBot ℕ) →
        ∫ x, p.eval x ∂μ = ∑ i, w i * p.eval (t i) := by
  obtain ⟨t, w, ht, hpos, hex⟩ := exists_gauss hw k
  exact ⟨t, w, ht, hpos, fun p hp => (hex p hp).symm⟩

/-- **Equation (10.2.8)** of [golub2013matrix], the Gauss–Radau rule with the prescribed node $a$.
Let $\mu$ be a weight carried by $[a, b]$, and let $k \in \mathbb{N}$. Then there are distinct
nodes $t_0 = a$ and $t_1, \dots, t_k \in (a, b]$ and positive weights $w_0, \dots, w_k$ such
that
$$\int p \, d\mu = w_0 p(a) + \sum_{i=1}^k w_i p(t_i)$$
for every polynomial $p$ of degree at most $2k$.

The prescribed node is the first node. The proof specializes `Quadrature.exists_gaussRadau`. -/
theorem equation_10_2_8 (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) (k : ℕ) :
    ∃ t w : Fin (k + 1) → ℝ, Function.Injective t ∧ t 0 = a ∧
      (∀ i, i ≠ 0 → t i ∈ Set.Ioc a b) ∧ (∀ i, 0 < w i) ∧ IsExactOnMeasure μ w t (2 * k) := by
  obtain ⟨t, w, ht, h0, hmem, hpos, hex, -⟩ := exists_gaussRadau hw hsupp k
  refine ⟨t, w, ht, h0, fun i hi => ⟨lt_of_le_of_ne (hmem i).1 ?_, (hmem i).2⟩, hpos, hex⟩
  intro h
  exact hi (ht (h0.trans h).symm)

/-- **Equation (10.2.9)** of [golub2013matrix], the Gauss–Radau rule with the prescribed node $b$.
Let $\mu$ be a weight carried by $[a, b]$, and let $k \in \mathbb{N}$. Then there are distinct
nodes $t_0 = b$ and $t_1, \dots, t_k \in [a, b)$ and positive weights $w_0, \dots, w_k$ such
that
$$\int p \, d\mu = w_0 p(b) + \sum_{i=1}^k w_i p(t_i)$$
for every polynomial $p$ of degree at most $2k$.

The prescribed node is the first node. The proof specializes
`Quadrature.exists_gaussRadau_right`, which is the rule of (10.2.8) for the reflected weight,
transported back. -/
theorem equation_10_2_9 (hw : IsWeight μ) {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) (k : ℕ) :
    ∃ t w : Fin (k + 1) → ℝ, Function.Injective t ∧ t 0 = b ∧
      (∀ i, i ≠ 0 → t i ∈ Set.Ico a b) ∧ (∀ i, 0 < w i) ∧ IsExactOnMeasure μ w t (2 * k) := by
  obtain ⟨t, w, ht, h0, hmem, hpos, hex⟩ := exists_gaussRadau_right hw hsupp k
  refine ⟨t, w, ht, h0, fun i hi => ⟨(hmem i).1, lt_of_le_of_ne (hmem i).2 ?_⟩, hpos, hex⟩
  intro h
  exact hi (ht (h.trans h0.symm))

/-- **Equation (10.2.10)** of [golub2013matrix], the Gauss–Lobatto rule. Let $\mu$ be a weight
carried by $[a, b]$, with $a < b$, and let $k \in \mathbb{N}$. Then there are distinct nodes
$t_0 = a$, $t_{k+1} = b$ and $t_1, \dots, t_k \in [a, b]$, and positive weights
$w_0, \dots, w_{k+1}$, such that
$$\int p \, d\mu = \sum_{i=0}^{k+1} w_i p(t_i)$$
for every polynomial $p$ of degree at most $2k + 1$.

Since the nodes are distinct, the $k$ interior nodes lie in $(a, b)$. The proof specializes
`Quadrature.exists_gaussLobatto` on $[-1, 1]$, with $k + 1$ in place of its $n$, for the image
of $\mu$ under the affine map from $[a, b]$ onto $[-1, 1]$, and transports the rule back
(`Quadrature.isExactOnMeasure_map_affine`). -/
theorem equation_10_2_10 (hw : IsWeight μ) {a b : ℝ} (hab : a < b)
    (hsupp : μ (Set.Icc a b)ᶜ = 0) (k : ℕ) :
    ∃ t w : Fin (k + 2) → ℝ, Function.Injective t ∧ t 0 = a ∧ t (Fin.last (k + 1)) = b ∧
      (∀ i, t i ∈ Set.Icc a b) ∧ (∀ i, 0 < w i) ∧ IsExactOnMeasure μ w t (2 * k + 1) := by
  have hba : 0 < b - a := sub_pos.2 hab
  set c : ℝ := 2 / (b - a) with hc
  set d : ℝ := -(a + b) / (b - a) with hd
  have hc0 : c ≠ 0 := by positivity
  have hν := hw.map_affine hc0 d
  have hsupp' : (μ.map fun t => c * t + d) (Set.Icc (-1) 1)ᶜ = 0 := by
    rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
    refine measure_mono_null (fun x hx => ?_) hsupp
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc] at hx ⊢
    intro hxab
    apply hx
    have e : c * x + d = (2 * x - a - b) / (b - a) := by
      rw [hc, hd]; field_simp; ring
    rw [e, le_div_iff₀ hba, div_le_iff₀ hba]
    constructor <;> nlinarith [hxab.1, hxab.2]
  obtain ⟨x, w, hx, h0, hl, hmem, hpos, hex, -⟩ :=
    exists_gaussLobatto hν hsupp' (n := k + 1) (by omega)
  set c' : ℝ := (b - a) / 2
  set d' : ℝ := (a + b) / 2
  have hcomp : ∀ t : ℝ, c' * (c * t + d) + d' = t := fun t => by
    rw [hc, hd]; field_simp; ring
  have hmap : (μ.map fun t => c * t + d).map (fun t => c' * t + d') = μ := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    convert Measure.map_id using 2
    funext t
    exact hcomp t
  have hex' := isExactOnMeasure_map_affine hex c' d'
  rw [hmap, show 2 * (k + 1) - 1 = 2 * k + 1 by omega] at hex'
  have hc'0 : 0 < c' := by positivity
  refine ⟨(fun t => c' * t + d') ∘ x, w, fun i j hij => hx ?_, ?_, ?_, fun i => ?_, hpos, hex'⟩
  · have := mul_left_cancel₀ hc'0.ne' (add_right_cancel hij)
    exact this
  · simp only [Function.comp_apply, h0]; ring
  · simp only [Function.comp_apply, hl]; ring
  · obtain ⟨h1, h2⟩ := hmem i
    have e : c' * x i + d' = a + (b - a) * ((x i + 1) / 2) := by
      simp only [c', d']; ring
    simp only [Function.comp_apply, Set.mem_Icc, e]
    have hx0 : 0 ≤ (x i + 1) / 2 := by linarith
    have hx1 : (x i + 1) / 2 ≤ 1 := by linarith
    constructor
    · nlinarith [mul_nonneg hba.le hx0]
    · nlinarith [mul_le_of_le_one_right hba.le hx1]

end Rules

/-! ### Remainders (§10.2.2) -/

section Remainders

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- **Section 10.2.2** of [golub2013matrix], the remainder $R_G$ of the Gauss rule. Let $\mu$ be a
finite measure carried by $[a, b]$, and let $k \ge 1$. Let a rule have $k$ distinct nodes
$t_1, \dots, t_k \in [a, b]$ and weights $w_1, \dots, w_k$, and let it be exact for polynomials
of degree at most $2k - 1$, as the Gauss rule (10.2.7) is. Then for every $f$ of class $C^{2k}$
there is $\eta \in [a, b]$ with
$$\int f \, d\mu - \sum_{i=1}^k w_i f(t_i) = \frac{f^{(2k)}(\eta)}{(2k)!} \int \prod_{i=1}^k
  (\lambda - t_i)^2 \, d\mu(\lambda).$$

**Typo.** The source prints $(2n)!$. The rule has $k$ nodes, and the factor is $(2k)!$.

The statement needs a finite measure, not a weight, and no sign of the rule's weights. The proof
specializes `Quadrature.exists_error_eq_of_hermite`, with every node doubled. -/
theorem gauss_remainder (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ} (hk : 1 ≤ k) {t w : Fin k → ℝ}
    (ht : Function.Injective t) (hmem : ∀ i, t i ∈ Set.Icc a b)
    (hex : IsExactOnMeasure μ w t (2 * k - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * k : ℕ) : WithTop ℕ∞) f) :
    ∃ η ∈ Set.Icc a b, (∫ x, f x ∂μ) - ∑ i, w i * f (t i) =
      iteratedDeriv (2 * k) f η / (2 * k).factorial * ∫ x, ∏ i, (x - t i) ^ 2 ∂μ := by
  have hN : 2 * k - 1 + 1 = 2 * k := by omega
  have hsum : ∑ _i : Fin k, (1 + 1) = 2 * k - 1 + 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hf' : ContDiff ℝ ((2 * k - 1 + 1 : ℕ) : WithTop ℕ∞) f := by rwa [hN]
  obtain ⟨η, hη, he⟩ := exists_error_eq_of_hermite hsupp ht hmem hsum
    (Or.inl fun x _ => by
      simp only [Hermite.nodal, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
      exact Finset.prod_nonneg fun i _ => Even.pow_nonneg ⟨1, rfl⟩ _) hex hf'
  refine ⟨η, hη, ?_⟩
  rw [he, hN]
  simp [Hermite.nodal, eval_prod]

/-- The nodal polynomial of a rule whose first node is simple and whose other nodes are double is
$(x - t_0) \prod_{i \ge 1} (x - t_i)^2$. -/
private theorem eval_nodal_radau {k : ℕ} (t : Fin (k + 1) → ℝ) (x : ℝ) :
    (Hermite.nodal t (Fin.cases 0 fun _ => 1)).eval x =
      (x - t 0) * ∏ i : Fin k, (x - t i.succ) ^ 2 := by
  simp [Hermite.nodal, eval_prod, Fin.prod_univ_succ]

/-- **Section 10.2.2** of [golub2013matrix], the remainders $R_{GR(a)}$ and $R_{GR(b)}$ of the
Gauss–Radau rules. Let $\mu$ be a finite measure carried by $[a, b]$, and let
$k \in \mathbb{N}$. Let a rule have $k + 1$ distinct nodes $t_0, \dots, t_k \in [a, b]$, with
$t_0 = a$ or $t_0 = b$, and weights $w_0, \dots, w_k$, and let it be exact for polynomials of
degree at most $2k$, as the rules (10.2.8) and (10.2.9) are. Then for every $f$ of class
$C^{2k+1}$ there is $\eta \in [a, b]$ with
$$\int f \, d\mu - \sum_{i=0}^k w_i f(t_i) = \frac{f^{(2k+1)}(\eta)}{(2k+1)!} \int (\lambda -
  t_0) \prod_{i=1}^k (\lambda - t_i)^2 \, d\mu(\lambda).$$

The nodal polynomial $(\lambda - t_0) \prod_{i \ge 1} (\lambda - t_i)^2$ has constant sign on
$[a, b]$. The source has $a < \eta < b$. The statement gives only $\eta \in [a, b]$, which is
what the mean value argument of the backbone gives. The proof specializes
`Quadrature.exists_error_eq_of_hermite`, with multiplicity one at the prescribed node and two at
the other nodes. -/
theorem gaussRadau_remainder (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ} {t w : Fin (k + 1) → ℝ}
    (ht : Function.Injective t) (hmem : ∀ i, t i ∈ Set.Icc a b) (h0 : t 0 = a ∨ t 0 = b)
    (hex : IsExactOnMeasure μ w t (2 * k)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * k + 1 : ℕ) : WithTop ℕ∞) f) :
    ∃ η ∈ Set.Icc a b, (∫ x, f x ∂μ) - ∑ i, w i * f (t i) =
      iteratedDeriv (2 * k + 1) f η / (2 * k + 1).factorial *
        ∫ x, (x - t 0) * ∏ i : Fin k, (x - t i.succ) ^ 2 ∂μ := by
  have hsum : ∑ i : Fin (k + 1), ((Fin.cases 0 fun _ => 1 : Fin (k + 1) → ℕ) i + 1) =
      2 * k + 1 := by
    rw [Fin.sum_univ_succ]
    simp [mul_comm]
    ring
  have hsign : (∀ x ∈ Set.Icc a b, 0 ≤ (Hermite.nodal t (Fin.cases 0 fun _ => 1)).eval x) ∨
      ∀ x ∈ Set.Icc a b, (Hermite.nodal t (Fin.cases 0 fun _ => 1)).eval x ≤ 0 := by
    have hp : ∀ x, 0 ≤ ∏ i : Fin k, (x - t i.succ) ^ 2 :=
      fun x => Finset.prod_nonneg fun i _ => by positivity
    rcases h0 with h0 | h0
    · refine Or.inl fun x hx => ?_
      rw [eval_nodal_radau, h0]
      exact mul_nonneg (by linarith [hx.1]) (hp x)
    · refine Or.inr fun x hx => ?_
      rw [eval_nodal_radau, h0]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) (hp x)
  obtain ⟨η, hη, he⟩ := exists_error_eq_of_hermite hsupp ht hmem hsum hsign hex hf
  refine ⟨η, hη, ?_⟩
  rw [he]
  simp only [eval_nodal_radau]

/-- The nodal polynomial of a rule whose two end nodes are simple and whose other nodes are double
is $(x - t_0)(x - t_{k+1}) \prod_{i=1}^{k} (x - t_i)^2$. -/
private theorem eval_nodal_lobatto {k : ℕ} (t : Fin (k + 2) → ℝ) (x : ℝ) :
    (Hermite.nodal t (Fin.cases 0 (Fin.lastCases 0 fun _ => 1))).eval x =
      (x - t 0) * (x - t (Fin.last (k + 1))) * ∏ i : Fin k, (x - t i.castSucc.succ) ^ 2 := by
  simp only [Hermite.nodal, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  simp only [Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last, Fin.lastCases_castSucc,
    zero_add, pow_one]
  rw [Fin.succ_last]
  ring

/-- **Section 10.2.2** of [golub2013matrix], the remainder $R_{GL}$ of the Gauss–Lobatto rule. Let
$\mu$ be a finite measure carried by $[a, b]$, and let $k \in \mathbb{N}$. Let a rule have
$k + 2$ distinct nodes $t_0, \dots, t_{k+1} \in [a, b]$, with $t_0 = a$ and $t_{k+1} = b$, and
weights $w_0, \dots, w_{k+1}$, and let it be exact for polynomials of degree at most $2k + 1$,
as the rule (10.2.10) is. Then for every $f$ of class $C^{2k+2}$ there is $\eta \in [a, b]$ with
$$\int f \, d\mu - \sum_{i=0}^{k+1} w_i f(t_i) = \frac{f^{(2k+2)}(\eta)}{(2k+2)!} \int
  (\lambda - a)(\lambda - b) \prod_{i=1}^k (\lambda - t_i)^2 \, d\mu(\lambda).$$

**Typo.** The source's list of remainders prints this remainder as $R_{GG}$.

The source has $a < \eta < b$. The statement gives only $\eta \in [a, b]$, which is what the
mean value argument of the backbone gives. The proof specializes
`Quadrature.exists_error_eq_of_hermite`, with multiplicity one at both ends. -/
theorem gaussLobatto_remainder (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ} {t w : Fin (k + 2) → ℝ}
    (ht : Function.Injective t) (hmem : ∀ i, t i ∈ Set.Icc a b) (h0 : t 0 = a)
    (hl : t (Fin.last (k + 1)) = b) (hex : IsExactOnMeasure μ w t (2 * k + 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * k + 1 + 1 : ℕ) : WithTop ℕ∞) f) :
    ∃ η ∈ Set.Icc a b, (∫ x, f x ∂μ) - ∑ i, w i * f (t i) =
      iteratedDeriv (2 * k + 2) f η / (2 * k + 2).factorial *
        ∫ x, (x - a) * (x - b) * ∏ i : Fin k, (x - t i.castSucc.succ) ^ 2 ∂μ := by
  have hsum : ∑ i : Fin (k + 2),
      ((Fin.cases 0 (Fin.lastCases 0 fun _ => 1) : Fin (k + 2) → ℕ) i + 1) = 2 * k + 1 + 1 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.cases_zero, Fin.cases_succ, Fin.lastCases_last, Fin.lastCases_castSucc]
    simp [mul_comm]
    ring
  have hsign : (∀ x ∈ Set.Icc a b,
        0 ≤ (Hermite.nodal t (Fin.cases 0 (Fin.lastCases 0 fun _ => 1))).eval x) ∨
      ∀ x ∈ Set.Icc a b,
        (Hermite.nodal t (Fin.cases 0 (Fin.lastCases 0 fun _ => 1))).eval x ≤ 0 := by
    refine Or.inr fun x hx => ?_
    rw [eval_nodal_lobatto, h0, hl]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith [hx.1]) (by linarith [hx.2]))
      (Finset.prod_nonneg fun i _ => by positivity)
  obtain ⟨η, hη, he⟩ := exists_error_eq_of_hermite hsupp ht hmem hsum hsign hex hf
  refine ⟨η, hη, ?_⟩
  rw [he]
  simp only [eval_nodal_lobatto, h0, hl]

/-- The $j$-th derivative of $\lambda \mapsto \lambda^{-2}$ is $(-2)(-3) \cdots (-1-j) \,
\lambda^{-2-j} = (-1)^j (j+1)! \, \lambda^{-2-j}$. -/
private theorem iteratedDeriv_inv_sq (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun y : ℝ => (y ^ 2)⁻¹) x =
      (∏ i ∈ Finset.range j, ((-2 : ℤ) - i : ℝ)) * x ^ ((-2 : ℤ) - j) := by
  have hf : (fun y : ℝ => (y ^ 2)⁻¹) = fun y => y ^ (-2 : ℤ) := by
    funext y
    rw [_root_.zpow_neg, zpow_ofNat]
  rw [hf, iteratedDeriv_eq_iterate, iter_deriv_zpow]

private theorem prod_neg_two_sub (j : ℕ) :
    ∏ i ∈ Finset.range j, ((-2 : ℤ) - i : ℝ) = (-1) ^ j * ∏ i ∈ Finset.range j, (2 + i : ℝ) := by
  rw [show ((-1 : ℝ)) ^ j = ∏ _i ∈ Finset.range j, (-1 : ℝ) by simp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast
  ring

/-- **Section 10.2.2** of [golub2013matrix], the two-sided bound for $f(\lambda) = 1/\lambda^2$. Let
$0 < a$, let $\mu$ be a finite measure carried by $[a, b]$, and let $k \ge 1$. Let $(t, w)$ be a
rule with $k$ distinct nodes in $[a, b]$ that is exact for polynomials of degree at most
$2k - 1$, and let $(t', w')$ be a rule with $k + 1$ distinct nodes $t'_0, \dots, t'_k$ in
$[a, b]$, with $t'_0 = a$, that is exact for polynomials of degree at most $2k$. Then
$$\sum_{i=1}^k \frac{w_i}{t_i^2} \le \int \frac{d\mu(\lambda)}{\lambda^2} \le \sum_{i=0}^k
  \frac{w'_i}{(t'_i)^2},$$
that is, $I_G(f) \le \int f \, d\mu \le I_{GR(a)}(f)$ for the Gauss rule (10.2.7) and the
Gauss–Radau rule (10.2.8).

The derivatives of $\lambda^{-2}$ alternate in sign on $(0, \infty)$: $f^{(2k)} > 0$ and
$f^{(2k+1)} < 0$. The proof specializes `Quadrature.gauss_le_integral_le_gaussRadau`, in which
the rules are given by their exactness. -/
theorem gauss_le_integral_le_gaussRadau (ha : 0 < a) (hsupp : μ (Set.Icc a b)ᶜ = 0) {k : ℕ}
    (hk : 1 ≤ k) {t w : Fin k → ℝ} (ht : Function.Injective t) (hmem : ∀ i, t i ∈ Set.Icc a b)
    (hex : IsExactOnMeasure μ w t (2 * k - 1)) {t' w' : Fin (k + 1) → ℝ}
    (ht' : Function.Injective t') (hmem' : ∀ i, t' i ∈ Set.Icc a b) (h0 : t' 0 = a)
    (hex' : IsExactOnMeasure μ w' t' (2 * k)) :
    ∑ i, w i * (t i ^ 2)⁻¹ ≤ ∫ x, (x ^ 2)⁻¹ ∂μ ∧ ∫ x, (x ^ 2)⁻¹ ∂μ ≤ ∑ i, w' i * (t' i ^ 2)⁻¹ := by
  have hsign : ∀ j : ℕ, ∀ x ∈ Set.Icc a b,
      iteratedDeriv j (fun y : ℝ => (y ^ 2)⁻¹) x =
        (-1) ^ j * ((∏ i ∈ Finset.range j, (2 + i : ℝ)) * x ^ ((-2 : ℤ) - j)) := by
    intro j x _
    rw [iteratedDeriv_inv_sq, prod_neg_two_sub, mul_assoc]
  have hpos : ∀ j : ℕ, ∀ x ∈ Set.Icc a b,
      0 < (∏ i ∈ Finset.range j, (2 + i : ℝ)) * x ^ ((-2 : ℤ) - j) := fun j x hx =>
    mul_pos (Finset.prod_pos fun i _ => by positivity) (zpow_pos (ha.trans_le hx.1) _)
  exact Quadrature.gauss_le_integral_le_gaussRadau (f := fun y : ℝ => (y ^ 2)⁻¹) hsupp hk ht hmem
    hex ht' hmem' h0 hex' isOpen_Ioi
    (fun x hx => ha.trans_le hx.1)
    (((contDiff_id.pow 2).contDiffOn).inv fun x hx => pow_ne_zero 2 (ne_of_gt hx))
    (fun x hx => by
      rw [hsign _ x hx, pow_mul, neg_one_sq, one_pow, one_mul]
      exact (hpos _ x hx).le)
    (fun x hx => by
      rw [hsign _ x hx, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul]
      exact neg_nonpos.2 (hpos _ x hx).le)

end Remainders

/-! ### The Stieltjes weights (§10.2.1) -/

section Weights

open Filter Topology

/-- The Heaviside step at $c \in \mathbb{R}$ as a Stieltjes function: $x \mapsto 1$ for $x \ge c$
and $x \mapsto 0$ for $x < c$. It is right-continuous, and its measure is the Dirac mass at $c$
(`GolubVanLoan.Chapter10.heavisideStieltjes_measure`). -/
noncomputable def heavisideStieltjes (c : ℝ) : StieltjesFunction ℝ where
  toFun x := if c ≤ x then 1 else 0
  mono' x y hxy := by
    dsimp only
    split_ifs with h1 h2 <;> first | exact absurd (h1.trans hxy) h2 | exact le_rfl | norm_num
  right_continuous' x := by
    by_cases hx : c ≤ x
    · refine (continuousWithinAt_const (b := (1 : ℝ))).congr (fun y hy => ?_) ?_
      · simp only [ite_eq_left (hx.trans hy)]
      · simp only [ite_eq_left hx]
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Iio_mem_nhds (not_le.1 hx))] with y hy
        simp only [ite_eq_right (not_le.2 hy)]
      · simp only [ite_eq_right hx]

/-- The Stieltjes measure of the unit step at $c$ is the Dirac mass $\delta_c$. -/
theorem heavisideStieltjes_measure (c : ℝ) :
    (heavisideStieltjes c).measure = Measure.dirac c := by
  refine Measure.ext_of_Ioc _ _ fun a b hab => ?_
  rw [StieltjesFunction.measure_Ioc, Measure.dirac_apply' _ measurableSet_Ioc]
  change ENNReal.ofReal ((if c ≤ b then 1 else 0) - if c ≤ a then 1 else 0) = _
  by_cases h1 : c ≤ a
  · rw [ite_eq_left (h1.trans hab.le), ite_eq_left h1, sub_self, ENNReal.ofReal_zero,
      Set.indicator_of_notMem (fun (h : c ∈ Set.Ioc a b) => not_lt.2 h1 h.1)]
  · by_cases h2 : c ≤ b
    · rw [ite_eq_left h2, ite_eq_right h1, sub_zero, ENNReal.ofReal_one,
        Set.indicator_of_mem (show c ∈ Set.Ioc a b from ⟨not_le.1 h1, h2⟩)]
      rfl
    · rw [ite_eq_right h2, ite_eq_right h1, sub_self, ENNReal.ofReal_zero,
        Set.indicator_of_notMem (fun (h : c ∈ Set.Ioc a b) => h2 h.2)]

private theorem measure_finset_sum {ι : Type*} (s : Finset ι) (g : ι → StieltjesFunction ℝ) :
    (∑ i ∈ s, g i).measure = ∑ i ∈ s, (g i).measure := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [StieltjesFunction.measure_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, StieltjesFunction.measure_add, ih]

/-- The measure of the Stieltjes function $d + \sum_i \max(c_i, 0) H_{\lambda_i}$, where $H_\lambda$
is the unit step at $\lambda$, is $\sum_i \max(c_i, 0) \, \delta_{\lambda_i}$. -/
private theorem measure_sum_smul_heaviside {ι : Type*} [Fintype ι] (c : ι → ℝ) (lam : ι → ℝ)
    (d : ℝ) :
    (StieltjesFunction.const ℝ d +
        ∑ i, (c i).toNNReal • heavisideStieltjes (lam i)).measure =
      ∑ i, ENNReal.ofReal (c i) • Measure.dirac (lam i) := by
  rw [StieltjesFunction.measure_add, StieltjesFunction.measure_const, zero_add,
    measure_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [StieltjesFunction.measure_smul, heavisideStieltjes_measure]
  rfl

/-- For $c_i \ge 0$, the integral of $f$ against $\sum_i c_i \delta_{\lambda_i}$ is
$\sum_i c_i f(\lambda_i)$. -/
private theorem integral_sum_smul_dirac {ι : Type*} [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    (lam : ι → ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(∑ i, ENNReal.ofReal (c i) • Measure.dirac (lam i)) = ∑ i, c i * f (lam i) := by
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_dirac (by simp)).smul_measure (by simp)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hc i), smul_eq_mul]

/-- **Equation (10.2.2)** of [golub2013matrix], the step weight. Let $\lambda_1, \dots, \lambda_N$
and $w_1, \dots, w_{N+1}$ be real numbers. The step weight is the right-continuous step function
$$w(\lambda) = w_{N+1} + \sum_{\mu=1}^{N} \max(w_\mu - w_{\mu+1}, 0) \, H(\lambda -
  \lambda_\mu),$$
where $H(x) = 1$ for $x \ge 0$ and $H(x) = 0$ for $x < 0$. When $\lambda_1 > \dots > \lambda_N$
and $w_1 \ge \dots \ge w_{N+1}$, as in the source, it is the function of (10.2.2):
$w(\lambda) = w_{N+1}$ for $\lambda < \lambda_N$, $w(\lambda) = w_\mu$ for
$\lambda_\mu \le \lambda < \lambda_{\mu-1}$, and $w(\lambda) = w_1$ for $\lambda \ge \lambda_1$.

The source also has $w_{N+1} \ge 0$. In Lean $N$ is `n + 1`: the points are
`lam : Fin (n + 1) → ℝ`, with `lam 0` the largest, and the values are `w : Fin (n + 2) → ℝ`. The
jump $\max(w_\mu - w_{\mu+1}, 0)$ is `Real.toNNReal`, and it is $w_\mu - w_{\mu+1}$ when $w$ is
decreasing. -/
noncomputable def stepWeight {n : ℕ} (lam : Fin (n + 1) → ℝ) (w : Fin (n + 2) → ℝ) :
    StieltjesFunction ℝ :=
  StieltjesFunction.const ℝ (w (Fin.last (n + 1))) +
    ∑ i, (w i.castSucc - w i.succ).toNNReal • heavisideStieltjes (lam i)

/-- **Equation (10.2.3)** of [golub2013matrix]. Let $\lambda_1 > \dots > \lambda_N$, let
$w_1 \ge \dots \ge w_{N+1}$, let $w$ be the step weight (10.2.2), and let $a = \lambda_N$ and
$b = \lambda_1$. Then for every function $f$
$$\int_a^b f \, dw = \sum_{\mu=1}^{N} (w_\mu - w_{\mu+1}) f(\lambda_\mu).$$

The integral is over the closed interval $[a, b]$, against the measure of
`GolubVanLoan.Chapter10.stepWeight lam w`. That measure is $\sum_\mu (w_\mu - w_{\mu+1})
\delta_{\lambda_\mu}$ (by `StieltjesFunction.measure_Ioc` on the jumps), and all its atoms lie
in $[a, b]$. -/
theorem equation_10_2_3 {n : ℕ} {lam : Fin (n + 1) → ℝ} (hlam : StrictAnti lam)
    {w : Fin (n + 2) → ℝ} (hw : Antitone w) (f : ℝ → ℝ) :
    ∫ x in Set.Icc (lam (Fin.last n)) (lam 0), f x ∂(stepWeight lam w).measure =
      ∑ i, (w i.castSucc - w i.succ) * f (lam i) := by
  have hc : ∀ i : Fin (n + 1), 0 ≤ w i.castSucc - w i.succ :=
    fun i => sub_nonneg.2 (hw Fin.castSucc_lt_succ.le)
  rw [stepWeight, measure_sum_smul_heaviside]
  have hmem : ∀ i, lam i ∈ Set.Icc (lam (Fin.last n)) (lam 0) :=
    fun i => ⟨hlam.antitone (Fin.le_last i), hlam.antitone (Fin.zero_le i)⟩
  have hres : (∑ i, ENNReal.ofReal (w i.castSucc - w i.succ) • Measure.dirac (lam i)).restrict
      (Set.Icc (lam (Fin.last n)) (lam 0)) =
      ∑ i, ENNReal.ofReal (w i.castSucc - w i.succ) • Measure.dirac (lam i) := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Measure.smul_apply,
      show {x : ℝ | ¬x ∈ Set.Icc (lam (Fin.last n)) (lam 0)} =
        (Set.Icc (lam (Fin.last n)) (lam 0))ᶜ from rfl,
      Measure.dirac_apply' _ (MeasurableSet.compl measurableSet_Icc),
      Set.indicator_of_notMem (by simpa using hmem i), smul_zero]
  rw [hres, integral_sum_smul_dirac hc]

end Weights

/-! ### Orthogonal polynomials and Jacobi matrices (§10.2.3) -/

section Facts

variable {μ : Measure ℝ}

/-- **Section 10.2.3** of [golub2013matrix], Fact 1. Let $\mu$ be a weight. For the monic orthogonal
polynomials $\pi_0, \pi_1, \dots$ of $\mu$, with $\|\pi\|^2 = \int \pi^2 \, d\mu$, let
$$\gamma_k = \frac{\|\pi_k\|}{\|\pi_{k-1}\|}, \qquad \omega_k = \frac{\int \lambda \,
  \pi_{k-1}(\lambda)^2 \, d\mu(\lambda)}{\|\pi_{k-1}\|^2} \qquad (k \ge 1).$$
Then the polynomials $p_k = \pi_k / \|\pi_k\|$ satisfy $\deg p_k = k$ and
$\int p_i p_j \, d\mu = \delta_{ij}$, and, with $p_{-1} = 0$,
$$\gamma_k p_k(\lambda) = (\lambda - \omega_k) p_{k-1}(\lambda) - \gamma_{k-1} p_{k-2}(\lambda)
  \qquad (k \ge 1).$$
They are unique up to sign: a polynomial $q$ of degree $k$ that is orthogonal to every
polynomial of lower degree and satisfies $\int q^2 \, d\mu = 1$ is $p_k$ or $-p_k$.

The source writes $w_k$ for $\omega_k$. The proof specializes
`OrthogonalPolynomial.orthonormalFamily_recurrence` and
`OrthogonalPolynomial.eq_orthonormalFamily_or_eq_neg`. In Lean, $p_k$ is
`OrthogonalPolynomial.orthonormalFamily μ k`, the norm of the monic polynomial of degree $k$ is
`OrthogonalPolynomial.normOf μ k`, and `OrthogonalPolynomial.alpha μ (k - 1)` is $\omega_k$. -/
theorem orthonormalPolynomials_threeTerm (hw : IsWeight μ) :
    (∀ k, (orthonormalFamily μ k).degree = k) ∧
    (∀ i j, ∫ x, (orthonormalFamily μ i).eval x * (orthonormalFamily μ j).eval x ∂μ =
      if i = j then 1 else 0) ∧
    C (normOf μ 1 / normOf μ 0) * orthonormalFamily μ 1 =
      (X - C (OrthogonalPolynomial.alpha μ 0)) * orthonormalFamily μ 0 ∧
    (∀ k, C (normOf μ (k + 2) / normOf μ (k + 1)) * orthonormalFamily μ (k + 2) =
      (X - C (OrthogonalPolynomial.alpha μ (k + 1))) * orthonormalFamily μ (k + 1) -
        C (normOf μ (k + 1) / normOf μ k) * orthonormalFamily μ k) ∧
    (∀ (k : ℕ) (q : ℝ[X]), q.degree = k →
      (∀ r : ℝ[X], r.degree < k → ∫ x, q.eval x * r.eval x ∂μ = 0) →
      ∫ x, q.eval x ^ 2 ∂μ = 1 → q = orthonormalFamily μ k ∨ q = -orthonormalFamily μ k) := by
  have hN : ∀ k, normOf μ k ≠ 0 := fun k => (normOf_pos hw k).ne'
  refine ⟨degree_orthonormalFamily hw, fun i j => ?_, ?_, fun k => ?_, fun k q hq horth hq1 => ?_⟩
  · split_ifs with h
    · subst h
      simpa [sq] using integral_orthonormalFamily_sq hw i
    · exact integral_orthonormalFamily_mul hw h
  · apply Polynomial.funext
    intro x
    simp only [orthonormalFamily, family_one, family_zero, eval_mul, eval_C, eval_sub, eval_X,
      eval_one]
    field_simp [hN 0, hN 1]
  · apply Polynomial.funext
    intro x
    have h := congrArg (eval x) (orthonormalFamily_recurrence hw k)
    simp only [eval_mul, eval_sub, eval_add, eval_C, eval_X] at h ⊢
    rw [h]
    simp only [cdA, cdB, cdC, show k + 1 - 1 = k by omega]
    field_simp [hN k, hN (k + 1), hN (k + 2)]
    ring
  · exact eq_orthonormalFamily_or_eq_neg hw hq horth hq1

/-- **Section 10.2.3** of [golub2013matrix], Fact 2. Let $\mu$ be a weight and let
$k \in \mathbb{N}$. The zeros of $p_k$ are the eigenvalues of the Jacobi matrix $T_k$, the
symmetric tridiagonal matrix with the diagonal $\omega_1, \dots, \omega_k$ and the off-diagonal
$\gamma_1, \dots, \gamma_{k-1}$ of Fact 1, and they are distinct. Precisely, there are distinct
real numbers $x_1, \dots, x_k$ such that the multiset of the roots of $p_k$ and the multiset of
the roots of the characteristic polynomial of $T_k$ are both $\{x_1, \dots, x_k\}$.

The Jacobi matrix is `OrthogonalPolynomial.jacobiMatrix μ k`. The source proves Fact 2 with
Theorem 8.4.1. The proof here is the orthogonal-polynomial argument: the characteristic
polynomial of $T_k$ is the monic $\pi_k$ (`OrthogonalPolynomial.charpoly_jacobiMatrix`), whose
roots are real and simple (`OrthogonalPolynomial.exists_injective_family_eq_prod`). -/
theorem roots_orthonormalPolynomial_eq_eigenvalues (hw : IsWeight μ) (k : ℕ) :
    ∃ x : Fin k → ℝ, Function.Injective x ∧
      (orthonormalFamily μ k).roots = Finset.univ.val.map x ∧
      (jacobiMatrix μ k).charpoly.roots = Finset.univ.val.map x := by
  obtain ⟨x, hx, hprod⟩ := exists_injective_family_eq_prod hw k
  have hroots : (family μ k).roots = Finset.univ.val.map x := by
    rw [hprod, roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun i _ => X_sub_C_ne_zero (x i))]
    simp [roots_X_sub_C]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [orthonormalFamily, roots_C_mul _ (inv_ne_zero (normOf_pos hw k).ne'), hroots]
  · rw [charpoly_jacobiMatrix hw, hroots]

end Facts

/-! ### The spectral weight and the Lanczos rules (§10.2.1, §10.2.4–10.2.6) -/

section Lanczos

open Lanczos

variable {n : ℕ}

/-- **Equation (10.2.5)** of [golub2013matrix], the spectral weight. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $A = X \Lambda X^T$ as in (10.2.4), where $X$
is orthogonal and $\Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$, and let
$u \in \mathbb{R}^n$. The spectral weight of $A$ and $u$ is the right-continuous step function
$$w(\lambda) = \sum_{i \,:\, \lambda_i \le \lambda} [X^T u]_i^2,$$
whose jumps are the squared components of $u$ along the orthonormal eigenvectors of $A$.

The eigenvectors and eigenvalues are Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis` and
`LinearMap.IsSymmetric.eigenvalues` of `toEuclideanLin A`. When the eigenvalues are distinct,
$w$ is the step weight (10.2.2) with the source's $w_\mu = [X^T u]_\mu^2 + \dots + [X^T u]_n^2$;
this definition does not need distinct eigenvalues. Its measure is the backbone's
`Krylov.spectralMeasure` (`GolubVanLoan.Chapter10.spectralWeight_measure`). -/
noncomputable def spectralWeight {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) : StieltjesFunction ℝ :=
  StieltjesFunction.const ℝ 0 +
    ∑ i, (‖inner ℝ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace i)
        u‖ ^ 2).toNNReal •
      heavisideStieltjes ((hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace i)

/-- The measure of the spectral weight of $A$ and $u$ is the spectral measure
$\sum_i [X^T u]_i^2 \, \delta_{\lambda_i}$, the backbone's `Krylov.spectralMeasure`. -/
theorem spectralWeight_measure {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) :
    (spectralWeight hA u).measure =
      Krylov.spectralMeasure hA.isSymmetric_toEuclideanLin finrank_euclideanSpace u := by
  rw [spectralWeight, measure_sum_smul_heaviside]
  rfl

/-- **Equation (10.2.6)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ be symmetric
with $A = X \Lambda X^T$ as in (10.2.4), let $u \in \mathbb{R}^n$, and let $f$ be any real
function. Then
$$u^T f(A) u = \sum_{i=1}^n [X^T u]_i^2 f(\lambda_i) = \int f \, dw,$$
where $w$ is the spectral weight (10.2.5).

The integral is against the measure of `GolubVanLoan.Chapter10.spectralWeight hA u`. The proof
specializes `Matrix.IsHermitian.inner_cfc_eq_integral_spectralMeasure`. -/
theorem equation_10_2_6 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) (f : ℝ → ℝ) :
    u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) =
        ∑ i, inner ℝ ((hA.isSymmetric_toEuclideanLin).eigenvectorBasis finrank_euclideanSpace i)
            u ^ 2 * f ((hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace i) ∧
      u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) = ∫ x, f x ∂(spectralWeight hA u).measure := by
  have hH : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  have h := hH.inner_cfc_eq_integral_spectralMeasure f u.ofLp
  simp only [star_trivial, WithLp.toLp_ofLp, RCLike.ofReal_real_eq_id, id] at h
  have h2 : u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) = ∫ x, f x ∂(spectralWeight hA u).measure := by
    rw [h, spectralWeight_measure]
  refine ⟨?_, h2⟩
  rw [h2, spectralWeight_measure, Krylov.integral_spectralMeasure]
  simp [Real.norm_eq_abs, sq_abs]

/-- **Equation (10.2.13)** of [golub2013matrix], the Lanczos polynomials. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $u \in \mathbb{R}^n$, and let $m$ be the grade
of $u$. Let $q_1, q_2, \dots$ be the Lanczos vectors and $\alpha_1, \alpha_2, \dots$ and
$\beta_1, \beta_2, \dots$ the Lanczos coefficients of $A$ started at $u$, and let
$p_0, p_1, \dots$ be the Lanczos polynomials. Then:
* $q_{j+1} = p_j(A) u$ for every $j \ge 0$;
* $\deg p_j = j$ for $j < m$;
* if $m > 1$, then $\beta_1 p_1(\lambda) = (\lambda - \alpha_1) p_0(\lambda)$;
* if $1 \le j$ and $j + 1 < m$, then $\beta_{j+1} p_{j+1}(\lambda) = (\lambda - \alpha_{j+1})
  p_j(\lambda) - \beta_j p_{j-1}(\lambda)$.

**Correction.** The source prints the recurrence with $\beta_{k-1}^2$. That is the recurrence of
the monic polynomials $\det(\lambda I - T_k)$, not of the polynomials $p_j$ with
$q_{j+1} = p_j(A) u$.

**Typo.** The source writes $q_k = p_k(A) q_1$ for a polynomial $p_k$ of degree $k$. The index
is off by one: the statement here is $q_{j+1} = p_j(A) u$ with $\deg p_j = j$.

The polynomials are `Lanczos.poly (toEuclideanLin A) u`, normalized by $p_0 = 1/\|u\|$. The
vector $q_{j+1}$ is `Arnoldi.vec (toEuclideanLin A) u j`, and $\alpha_{j+1}$ and $\beta_{j+1}$
are `Lanczos.alpha` and `Lanczos.beta` at the index $j$. The first step
$\beta_1 p_1 = (\lambda - \alpha_1) p_0$ is the source's convention $\beta_0 q_0 \equiv 0$. The
proof uses `Lanczos.aeval_poly`, `Lanczos.poly_degree` and `Lanczos.poly_add_two`. -/
theorem equation_10_2_13 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) :
    (∀ j, aeval (toEuclideanLin A) (Lanczos.poly (toEuclideanLin A) u j) u =
      Arnoldi.vec (toEuclideanLin A) u j) ∧
    (∀ j, j < grade (toEuclideanLin A) u → (Lanczos.poly (toEuclideanLin A) u j).degree = j) ∧
    (1 < grade (toEuclideanLin A) u →
      C (Lanczos.beta (toEuclideanLin A) u 0) * Lanczos.poly (toEuclideanLin A) u 1 =
        (X - C (Lanczos.alpha (toEuclideanLin A) u 0)) * Lanczos.poly (toEuclideanLin A) u 0) ∧
    (∀ j, j + 2 < grade (toEuclideanLin A) u →
      C (Lanczos.beta (toEuclideanLin A) u (j + 1)) * Lanczos.poly (toEuclideanLin A) u (j + 2) =
        (X - C (Lanczos.alpha (toEuclideanLin A) u (j + 1))) *
            Lanczos.poly (toEuclideanLin A) u (j + 1) -
          C (Lanczos.beta (toEuclideanLin A) u j) * Lanczos.poly (toEuclideanLin A) u j) := by
  refine ⟨Lanczos.aeval_poly hA.isSymmetric_toEuclideanLin u,
    fun j hj => Lanczos.poly_degree _ u hj, fun hg => ?_, fun j hj => ?_⟩
  · have hβ : Lanczos.beta (toEuclideanLin A) u 0 ≠ 0 := by
      rw [Ne, Lanczos.beta_eq_zero_iff u]
      omega
    rw [Lanczos.poly_one]
    simp only [RCLike.ofReal_real_eq_id, id]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hβ, C_1, one_mul]
  have hβ : Lanczos.beta (toEuclideanLin A) u (j + 1) ≠ 0 := by
    rw [Ne, Lanczos.beta_eq_zero_iff u]
    omega
  rw [Lanczos.poly_add_two]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hβ, C_1, one_mul]

/-- **Section 10.2.4** of [golub2013matrix], orthonormality of the Lanczos polynomials (the chain of
equalities after (10.2.13)). Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let
$u \in \mathbb{R}^n$, and let $i, j < m$, where $m$ is the grade of $u$. Then
$$\int p_i p_j \, dw = q_{i+1}^T q_{j+1} = \delta_{ij},$$
where $w$ is the spectral weight of $A$ and $u$. So the Lanczos polynomials, normalized by
$p_0 = 1/\|u\|$, are the orthonormal polynomials of $w$.

The Lean statement is the equality of the outer terms. The proof specializes
`Lanczos.polyInner_poly` and `Krylov.polyInner_eq_integral`. -/
theorem lanczosPolynomials_orthonormal {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) {i j : ℕ} (hi : i < grade (toEuclideanLin A) u)
    (hj : j < grade (toEuclideanLin A) u) :
    ∫ x, (Lanczos.poly (toEuclideanLin A) u i).eval x *
        (Lanczos.poly (toEuclideanLin A) u j).eval x ∂(spectralWeight hA u).measure =
      if i = j then 1 else 0 := by
  have h := Krylov.polyInner_eq_integral hA.isSymmetric_toEuclideanLin finrank_euclideanSpace u
    (Lanczos.poly (toEuclideanLin A) u i) (Lanczos.poly (toEuclideanLin A) u j)
  rw [Algebra.algebraMap_self, Polynomial.map_id, Polynomial.map_id,
    Lanczos.polyInner_poly hA.isSymmetric_toEuclideanLin u hi hj] at h
  rw [spectralWeight_measure]
  simpa using h.symm

/-- **Equation (10.2.12)** of [golub2013matrix], with Fact 3 and (10.2.11), for the spectral weight.
Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $u \in \mathbb{R}^n$, and let $k \ge 1$
with $\dim \mathcal{K}(A, u, k) = k$. Let $T_k$ be the Lanczos matrix started at $u$, with the
orthonormal eigenvectors $s_1, \dots, s_k$ and the eigenvalues $\theta_1, \dots, \theta_k$, so
that $S^T T_k S = \operatorname{diag}(\theta_1, \dots, \theta_k)$ for
$S = [s_1 | \cdots | s_k]$. Then for every polynomial $p$ of degree at most $2k - 1$
$$\int p \, dw = \|u\|^2 \sum_{j=1}^k s_{1j}^2 \, p(\theta_j),$$
where $w$ is the spectral weight. So the nodes $\theta_j$ and the weights $\|u\|^2 s_{1j}^2$
form the $k$-point Gauss rule (10.2.7) of $w$.

**Generalization.** The source's weights $s_{1j}^2$ assume $\int dw = 1$, that is, $\|u\| = 1$.
The statement holds for every $u$, with the weights $\|u\|^2 s_{1j}^2$.

The degree bound is on `natDegree`, so the zero polynomial is included. The proof specializes
`Lanczos.gauss_quadrature` and `Lanczos.integral_spectralMeasure_compression_eq_sum_tridiag`. -/
theorem equation_10_2_12 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk0 : 0 < k)
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) u k) = k) {p : ℝ[X]}
    (hp : p.natDegree < 2 * k) :
    ∫ x, p.eval x ∂(spectralWeight hA u).measure =
      ‖u‖ ^ 2 * ∑ j, ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvectorBasis j
          ⟨0, hk0⟩) ^ 2 * p.eval ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvalues j) := by
  rw [spectralWeight_measure, Lanczos.gauss_quadrature hA.isSymmetric_toEuclideanLin _ u hk0 hk hp,
    Lanczos.integral_spectralMeasure_compression_eq_sum_tridiag hA.isSymmetric_toEuclideanLin u
      hk0 hk]

/-- If the spectrum of $A$ lies in $[a, b]$, then every eigenvalue $\lambda_i$ of $A$ lies in
$[a, b]$. -/
private theorem eigenvalues_mem_Icc {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {a b : ℝ}
    (hab : spectrum ℝ A ⊆ Set.Icc a b) (i : Fin (Fintype.card (Fin n))) :
    (hA.isSymmetric_toEuclideanLin).eigenvalues finrank_euclideanSpace i ∈ Set.Icc a b := by
  have hH : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  have h := hab (hH.eigenvalues_mem_spectrum_real ((Fintype.equivOfCardEq (Fintype.card_fin _)) i))
  convert h using 1
  simp [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀]

/-- **Section 10.2.4** of [golub2013matrix], the Gauss rule computed by Lanczos (Steps 1–3). Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with spectrum in $[a, b]$, let
$u \in \mathbb{R}^n$, and let $k \ge 1$ with $\dim \mathcal{K}(A, u, k) = k$. Let $\theta_j$ and
$s_j$ be as in (10.2.12), and for a function $f$ let
$$\sigma = \|u\|^2 \bigl(s_{11}^2 f(\theta_1) + \dots + s_{1k}^2 f(\theta_k)\bigr)$$
be the value computed from $k$ Lanczos steps. If $f$ is of class $C^{2k}$, then there is
$\eta \in [a, b]$ with
$$u^T f(A) u - \sigma = \frac{f^{(2k)}(\eta)}{(2k)!} \int \pi_k(\lambda)^2 \, dw(\lambda),$$
where $\pi_k(\lambda) = \det(\lambda I - T_k)$ and $w$ is the spectral weight.

**Generalization.** The source takes the interval $[\lambda_n, \lambda_1]$. The statement allows
any interval $[a, b]$ that contains the spectrum of $A$.

The rule is exact for polynomials of degree at most $2k - 1$ by
`GolubVanLoan.Chapter10.equation_10_2_12`. The polynomial $\pi_k$ is the characteristic
polynomial of `Lanczos.tridiag (toEuclideanLin A) u k`. The proof specializes
`Lanczos.exists_gauss_error_eq`. -/
theorem lanczos_gaussRule {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk0 : 0 < k)
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) u k) = k) {a b : ℝ}
    (hab : spectrum ℝ A ⊆ Set.Icc a b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((2 * k : ℕ) : WithTop ℕ∞) f) :
    ∃ η ∈ Set.Icc a b, u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) -
        ‖u‖ ^ 2 * ∑ j, ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvectorBasis j
          ⟨0, hk0⟩) ^ 2 * f ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvalues j) =
      iteratedDeriv (2 * k) f η / (2 * k).factorial *
        ∫ x, ((Lanczos.tridiag (toEuclideanLin A) u k).charpoly.eval x) ^ 2
          ∂(spectralWeight hA u).measure := by
  obtain ⟨η, hη, he⟩ := Lanczos.exists_gauss_error_eq hA.isSymmetric_toEuclideanLin
    finrank_euclideanSpace u hk0 hk (eigenvalues_mem_Icc hA hab) hf
  refine ⟨η, hη, ?_⟩
  rw [(equation_10_2_6 hA u f).2, spectralWeight_measure, ← he,
    Lanczos.integral_spectralMeasure_compression_eq_sum_tridiag hA.isSymmetric_toEuclideanLin u
      hk0 hk]

/-- If $T_k - aI$ is nonsingular, then the Gauss–Radau matrix satisfies
$\tilde T_{k+1} [x; -1] = a [x; -1]$ for $x = \beta_k (T_k - aI)^{-1} e_k$, which is empty for
$k = 0$. -/
private theorem radauTridiag_mulVec_snoc {A : Matrix (Fin n) (Fin n) ℝ}
    (u : EuclideanSpace ℝ (Fin n)) (k : ℕ) {a : ℝ}
    (ha : IsUnit (Lanczos.tridiag (toEuclideanLin A) u k - a • 1).det) :
    ∃ x : Fin k → ℝ, Lanczos.radauTridiag (toEuclideanLin A) u k a *ᵥ
        (Fin.snoc x (-1) : Fin (k + 1) → ℝ) = a • (Fin.snoc x (-1) : Fin (k + 1) → ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨Fin.elim0, ?_⟩
    ext i
    fin_cases i
    simp [Lanczos.radauTridiag, Lanczos.radauCorrection, Matrix.mulVec, dotProduct]
  set T := Lanczos.tridiag (toEuclideanLin A) u k
  set R := (T - a • 1)⁻¹
  set β := Lanczos.beta (toEuclideanLin A) u (k - 1)
  have hTRm : T * R = 1 + a • R := by
    have h := Matrix.mul_nonsing_inv _ ha
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h
    rw [← h]
    abel
  have hTR : ∀ i j, ∑ l, T i l * R l j = (if i = j then 1 else 0) + a * R i j := by
    intro i j
    have h := congrFun (congrFun hTRm i) j
    rw [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul] at h
    exact h
  refine ⟨fun i => β * R i ⟨k - 1, by omega⟩, ?_⟩
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have hrow : ∀ j : Fin k,
        Lanczos.radauTridiag (toEuclideanLin A) u k a (Fin.last k) j.castSucc =
        if (j : ℕ) + 1 = k then Lanczos.beta (toEuclideanLin A) u j else 0 := by
      intro j
      rw [Lanczos.radauTridiag_apply_of_ne _ _ _ _ fun h => absurd h.2 (Fin.castSucc_ne_last j),
        Lanczos.tridiag_apply]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hll : Lanczos.radauTridiag (toEuclideanLin A) u k a (Fin.last k) (Fin.last k) =
        a + β ^ 2 * R ⟨k - 1, by omega⟩ ⟨k - 1, by omega⟩ := by
      simp only [Lanczos.radauTridiag, Matrix.of_apply, and_self, ↓reduceIte,
        Lanczos.radauCorrection, hk, ↓reduceDIte]
      rfl
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc,
      hrow, hll, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
    · rw [ite_eq_left (by simp; omega)]
      ring
    · intro j _ hj
      rw [ite_eq_right fun h => hj (Fin.ext (by simp; omega)), zero_mul]
    · simp
  · have hcol :
        Lanczos.radauTridiag (toEuclideanLin A) u k a i.castSucc (Fin.last k) =
        if (i : ℕ) + 1 = k then Lanczos.beta (toEuclideanLin A) u i else 0 := by
      rw [Lanczos.radauTridiag_apply_of_ne _ _ _ _ fun h => absurd h.1 (Fin.castSucc_ne_last i),
        Lanczos.tridiag_apply]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ite_eq_right (by omega)]
      by_cases h : (i : ℕ) + 1 = k
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h, ite_eq_right (by omega)]
    have hin : ∀ j : Fin k,
        Lanczos.radauTridiag (toEuclideanLin A) u k a i.castSucc j.castSucc = T i j := fun j => by
      rw [Lanczos.radauTridiag_apply_of_ne _ _ _ _ fun h => absurd h.1 (Fin.castSucc_ne_last i)]
      rfl
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc,
      hcol, hin, Pi.smul_apply, smul_eq_mul]
    have hs : ∑ j, T i j * (β * R j ⟨k - 1, by omega⟩) =
        β * ((if i = ⟨k - 1, by omega⟩ then 1 else 0) + a * R i ⟨k - 1, by omega⟩) := by
      rw [← hTR, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    by_cases h : (i : ℕ) + 1 = k
    · have hi : i = ⟨k - 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [ite_eq_left h, ite_eq_left hi, hi]
      ring
    · have hi : i ≠ ⟨k - 1, by omega⟩ := fun h' => h (by rw [h']; simp; omega)
      rw [ite_eq_right h, ite_eq_right hi]
      ring

/-- **Section 10.2.5** of [golub2013matrix], the Gauss–Radau modification. Let
$A \in \mathbb{R}^{n \times n}$, $u \in \mathbb{R}^n$, $k \in \mathbb{N}$ and
$a \in \mathbb{R}$, and let $T_k - aI$ be nonsingular. Let $\tilde T_{k+1}$ be $T_{k+1}$ with
the last diagonal entry replaced by
$$\tilde\alpha_{k+1} = a + \beta_k^2 \, e_k^T (T_k - aI)^{-1} e_k.$$
Then $a$ is an eigenvalue of $\tilde T_{k+1}$, with an eigenvector of the form of the source's
derivation: $\tilde T_{k+1} [x; -1] = a [x; -1]$ for some $x \in \mathbb{R}^k$.

**Typo.** The source prints $\beta_{k+1}^2$ in $\tilde\alpha_{k+1}$, and its display of
$\tilde T_{k+1}$ omits $\beta_k$ above the diagonal.

The matrix $\tilde T_{k+1}$ is `Lanczos.radauTridiag (toEuclideanLin A) u k a`. For $k = 0$,
$\tilde\alpha_1 = a$. The vector in the proof is $x = \beta_k (T_k - aI)^{-1} e_k$. The
statement needs no symmetry of $A$ and no bound on $k$. The proof specializes
`Lanczos.radauTridiag_hasEigenvalue`. -/
theorem gaussRadau_tridiag {A : Matrix (Fin n) (Fin n) ℝ} (u : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    {a : ℝ} (ha : IsUnit (Lanczos.tridiag (toEuclideanLin A) u k - a • 1).det) :
    a ∈ spectrum ℝ (Lanczos.radauTridiag (toEuclideanLin A) u k a) ∧
      ∃ x : Fin k → ℝ, Lanczos.radauTridiag (toEuclideanLin A) u k a *ᵥ
        (Fin.snoc x (-1) : Fin (k + 1) → ℝ) = a • (Fin.snoc x (-1) : Fin (k + 1) → ℝ) :=
  ⟨Lanczos.radauTridiag_hasEigenvalue (A := toEuclideanLin A) (v := u) (m := k) (a := a) ha,
    radauTridiag_mulVec_snoc u k ha⟩

/-- **Section 10.2.5** of [golub2013matrix], the Gauss–Radau rule computed by Lanczos ("Guided by
Gauss quadrature theory …"). Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let
$u \in \mathbb{R}^n$, let $k \in \mathbb{N}$ with $\dim \mathcal{K}(A, u, k + 1) = k + 1$, and
let $a \in \mathbb{R}$ with $T_k - aI$ nonsingular. Let $\tilde\theta_j$ and $\tilde s_j$ be the
eigenvalues and the orthonormal eigenvectors of the matrix $\tilde T_{k+1}$ of the Gauss–Radau
modification. Then $a$ is one of the $\tilde\theta_j$, and
$$\int p \, dw = \|u\|^2 \sum_{j=1}^{k+1} \tilde s_{1j}^2 \, p(\tilde\theta_j)$$
for every polynomial $p$ of degree at most $2k$, where $w$ is the spectral weight. So this rule
has the node $a$ and the exactness of the Gauss–Radau rule (10.2.8).

The eigenvalues and eigenvectors are those of `Lanczos.radauTridiag_isHermitian`. The proof
specializes `Lanczos.radau_quadrature`. -/
theorem gaussRadau_via_lanczos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) {k : ℕ}
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) u (k + 1)) = k + 1) {a : ℝ}
    (ha : IsUnit (Lanczos.tridiag (toEuclideanLin A) u k - a • 1).det) :
    (∃ j, (radauTridiag_isHermitian (toEuclideanLin A) u k a).eigenvalues j = a) ∧
      ∀ p : ℝ[X], p.natDegree ≤ 2 * k →
        ∫ x, p.eval x ∂(spectralWeight hA u).measure =
          ‖u‖ ^ 2 * ∑ j, ((radauTridiag_isHermitian (toEuclideanLin A) u k a).eigenvectorBasis
              j 0) ^ 2 *
            p.eval ((radauTridiag_isHermitian (toEuclideanLin A) u k a).eigenvalues j) := by
  refine ⟨(Lanczos.radau_quadrature (toEuclideanLin A) u k a hA.isSymmetric_toEuclideanLin
    finrank_euclideanSpace hk ha
    (f := 0) (by simp)).1, fun p hp => ?_⟩
  rw [spectralWeight_measure]
  exact (Lanczos.radau_quadrature (toEuclideanLin A) u k a hA.isSymmetric_toEuclideanLin
    finrank_euclideanSpace hk ha hp).2

/-- **Section 10.2.6** of [golub2013matrix], the bounds of the framework. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with spectrum in $[a, b]$, let
$u \in \mathbb{R}^n$, and let $k \ge 1$ with $\dim \mathcal{K}(A, u, k + 1) = k + 1$ and
$T_k - aI$ nonsingular. Let $f$ be of class $C^{2k+1}$ on an open set that contains $[a, b]$,
with $f^{(2k)} \ge 0$ and $f^{(2k+1)} \le 0$ on $[a, b]$. Let
$$b_k = \|u\|^2 \sum_{j=1}^{k} s_{1j}^2 f(\theta_j), \qquad B_k = \|u\|^2 \sum_{j=1}^{k+1}
  \tilde s_{1j}^2 f(\tilde\theta_j)$$
be the Gauss value of `GolubVanLoan.Chapter10.lanczos_gaussRule` and the Gauss–Radau value of
`GolubVanLoan.Chapter10.gaussRadau_via_lanczos`. Then
$$b_k \le u^T f(A) u \le B_k.$$

An example is $f(\lambda) = 1/\lambda^2$ with $0 < a$. The source does not claim that
$B_k - b_k \to 0$, and the statement does not either. The proof specializes
`Lanczos.gauss_le_integral_le_radau` with (10.2.6). -/
theorem lanczos_quadrature_bounds {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u : EuclideanSpace ℝ (Fin n)) {k : ℕ} (hk0 : 0 < k)
    (hk : Module.finrank ℝ (Krylov.subspace (toEuclideanLin A) u (k + 1)) = k + 1) {a b : ℝ}
    (ha : IsUnit (Lanczos.tridiag (toEuclideanLin A) u k - a • 1).det)
    (hab : spectrum ℝ A ⊆ Set.Icc a b) {U : Set ℝ} (hU : IsOpen U) (hUsub : Set.Icc a b ⊆ U)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ ((2 * k + 1 : ℕ) : WithTop ℕ∞) f U)
    (heven : ∀ t ∈ Set.Icc a b, 0 ≤ iteratedDeriv (2 * k) f t)
    (hodd : ∀ t ∈ Set.Icc a b, iteratedDeriv (2 * k + 1) f t ≤ 0) :
    ‖u‖ ^ 2 * ∑ j, ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvectorBasis j
        ⟨0, hk0⟩) ^ 2 * f ((tridiag_isHermitian (toEuclideanLin A) u k).eigenvalues j) ≤
        u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) ∧
      u.ofLp ⬝ᵥ (cfc f A *ᵥ u.ofLp) ≤
        ‖u‖ ^ 2 * ∑ j, ((radauTridiag_isHermitian (toEuclideanLin A) u k a).eigenvectorBasis
          j 0) ^ 2 * f ((radauTridiag_isHermitian (toEuclideanLin A) u k a).eigenvalues j) := by
  rw [(equation_10_2_6 hA u f).2, spectralWeight_measure]
  exact Lanczos.gauss_le_integral_le_radau hA.isSymmetric_toEuclideanLin finrank_euclideanSpace
    u hk0 hk ha (eigenvalues_mem_Icc hA hab) hU hUsub hf heven hodd

end Lanczos

end GolubVanLoan.Chapter10
