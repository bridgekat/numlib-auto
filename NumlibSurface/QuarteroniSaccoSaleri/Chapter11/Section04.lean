/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Numlib.Algebra.LinearRecurrence

/-!
# Quarteroni, Sacco and Saleri, Section 11.4: Difference Equations

This module formalizes Section 11.4 of [quarteroni2000numerical]. The linear difference equation of
order $k$ with constant coefficients $\alpha_0, \dots, \alpha_{k-1}$ is
$$u_{n+k} + \alpha_{k-1} u_{n+k-1} + \dots + \alpha_0 u_n = \varphi_{n+k}, \qquad n \ge 0,$$
which is (11.28), and (11.29) is the homogeneous equation with $\varphi = 0$. Its characteristic
polynomial is $\Pi(r) = r^k + \alpha_{k-1} r^{k-1} + \dots + \alpha_0$ (11.30). The sequence $r^n$
solves (11.29) if and only if $\Pi(r) = 0$ (11.31). If the roots $r_j$ are simple, the solutions are
the combinations $\sum_j \gamma_j r_j^n$ (11.32); a root of multiplicity $m$ contributes the
solutions $n^s r^n$, $s < m$ (11.33). The fundamental solutions $\psi_j$ with
$\psi_j^{(i)} = \delta_{ij}$ (11.34) give every solution of (11.29) as
$u_n = \sum_j u_j \psi_j^{(n)}$ (11.35), and for simple roots they are computed from a transposed
Vandermonde system (11.36)–(11.37). The discrete Duhamel formula (11.42) solves the inhomogeneous
equation. Examples 11.3–11.7 work out particular equations.

The equations are read over a field $K$; the book names none, its coefficients are real and its
roots complex. The statements that need every root of $\Pi$ are stated over $\mathbb{C}$. The proofs
specialize the backbone module `Numlib.Algebra.LinearRecurrence`, which extends Mathlib's
`LinearRecurrence`.

## Main definitions

* Equation (11.28), `QuarteroniSaccoSaleri.Chapter11.equation_11_28`: the difference equation with
  coefficients $\alpha_0, \dots, \alpha_{k-1}$, as a `LinearRecurrence`.
* Equation (11.30), `QuarteroniSaccoSaleri.Chapter11.equation_11_30`: the characteristic polynomial
  $\Pi$.
* Equation (11.34), `QuarteroniSaccoSaleri.Chapter11.equation_11_34`: the fundamental solutions
  $\psi_j$ with $\psi_j^{(i)} = \delta_{ij}$.
* Equation (11.37), `QuarteroniSaccoSaleri.Chapter11.equation_11_37_matrix`: the matrix
  $R = (r_m^i)$.

## Main results

* Equation (11.28), `QuarteroniSaccoSaleri.Chapter11.equation_11_28_iff`: $u$ solves (11.28) if and
  only if $u_{n+k} + \sum_i \alpha_i u_{n+i} = \varphi_{n+k}$ for every $n$.
* Equation (11.29), `QuarteroniSaccoSaleri.Chapter11.equation_11_29_iff`: the same for the
  homogeneous equation.
* Equation (11.30), `QuarteroniSaccoSaleri.Chapter11.equation_11_30_eq`: $\Pi$ is the characteristic
  polynomial `LinearRecurrence.charPoly` of the recurrence.
* Equation (11.31), `QuarteroniSaccoSaleri.Chapter11.equation_11_31`: $r^n$ solves (11.29) if and
  only if $\Pi(r) = 0$.
* Equation (11.32), `QuarteroniSaccoSaleri.Chapter11.equation_11_32`: every combination
  $\sum_j \gamma_j r_j^n$ of roots $r_j$ of $\Pi$ solves (11.29).
* Equation (11.32), `QuarteroniSaccoSaleri.Chapter11.equation_11_32_existsUnique`: for $k$ distinct
  roots, every solution is $\sum_j \gamma_j r_j^n$ for a unique $\gamma$ (Exercise 4).
* Equation (11.33), `QuarteroniSaccoSaleri.Chapter11.equation_11_33_isSolution`: $n^s r^n$ solves
  (11.29) for $s$ less than the multiplicity of $r$.
* Equation (11.33), `QuarteroniSaccoSaleri.Chapter11.equation_11_33`: over $\mathbb{C}$ with
  $\alpha_0 \neq 0$, every solution is $\sum_j p_j(n) r_j^n$ with $\deg p_j < m_j$.
* Example 11.3, `QuarteroniSaccoSaleri.Chapter11.example_11_3_charPoly`,
  `QuarteroniSaccoSaleri.Chapter11.example_11_3`: the equation $u_{n+2} - u_n = 0$.
* Example 11.4, `QuarteroniSaccoSaleri.Chapter11.example_11_4_charPoly`,
  `QuarteroniSaccoSaleri.Chapter11.example_11_4`: the equation
  $u_{n+3} - 2u_{n+2} - 7u_{n+1} - 4u_n = 0$.
* Equation (11.35), `QuarteroniSaccoSaleri.Chapter11.equation_11_35`: every solution of (11.29) is
  $u_n = \sum_j u_j \psi_j^{(n)}$.
* Equation (11.37), `QuarteroniSaccoSaleri.Chapter11.equation_11_37_det_ne_zero`: for distinct
  $r_m$, the matrix $R$ is nonsingular (Exercise 5).
* Equation (11.36), `QuarteroniSaccoSaleri.Chapter11.equation_11_36`: for simple roots,
  $\psi_j^{(n)} = \sum_m \beta_{j,m} r_m^n$ for unique coefficients.
* Equation (11.37), `QuarteroniSaccoSaleri.Chapter11.equation_11_37`: the coefficients $b_j$ of
  (11.36) solve $R b_j = e_j$.
* Example 11.5, `QuarteroniSaccoSaleri.Chapter11.example_11_5_matrix`,
  `QuarteroniSaccoSaleri.Chapter11.example_11_5`: the matrix $R$ and the three $\psi_j$ for the
  equation of Example 11.4.
* Example 11.6, `QuarteroniSaccoSaleri.Chapter11.example_11_6`: the solution
  $u_n = ((-1)^n + 3^n)/n!$ of the variable-coefficient equation (11.41).
* Example 11.7, `QuarteroniSaccoSaleri.Chapter11.example_11_7`,
  `QuarteroniSaccoSaleri.Chapter11.example_11_7_isSolutionWith`: a particular solution of
  $u_{n+3} - u_{n+2} + u_{n+1} - u_n = 2^n n^2$.
* Equation (11.42), `QuarteroniSaccoSaleri.Chapter11.equation_11_42`: the discrete Duhamel formula
  for (11.28).

## Conventions

* The coefficients $\alpha_0, \dots, \alpha_{k-1}$ are `α : Fin k → K`. In Mathlib's convention a
  `LinearRecurrence` writes $u_{n+k} = \sum_i c_i u_{n+i}$, so $c_i = -\alpha_i$.
* A solution of (11.28) with right-hand side $\varphi$ is `(equation_11_28 α).IsSolutionWith φ u`,
  and a solution of (11.29) is `(equation_11_28 α).IsSolution u`. The right-hand side is indexed as
  in the book, at $n + k$, so the values $\varphi_0, \dots, \varphi_{k-1}$ are never read.
* The book assumes $\alpha_0 \neq 0$ throughout, that is $\Pi(0) \neq 0$
  (`QuarteroniSaccoSaleri.Chapter11.equation_11_30_eval_zero`). Only (11.33) needs it, and only
  there is it a hypothesis.

## Implementation notes

* The fundamental system of the backbone for a root $r$ of multiplicity $m$ is
  $\binom{n}{s} r^{n-s}$, $s < m$, which does not need $\alpha_0 \neq 0$. The surface states the
  form $n^s r^n$ of the book.

## Deviations from the source

* **Example 11.5** (reading). The book writes $r_2$ for the root $4$ that Example 11.4 calls $r_1$.
  The matrix is the one printed. See `QuarteroniSaccoSaleri.Chapter11.example_11_5_matrix`.
* **Equation (11.33)** (reading). The general solution needs the standing assumption
  $\alpha_0 \neq 0$, since for $\alpha_0 = 0$ the sequence $n^s 0^n$ vanishes for $s \ge 1$. The
  statement assumes it. See `QuarteroniSaccoSaleri.Chapter11.equation_11_33`.

## Not formalized

* **Difference equations with variable coefficients (11.38)**, beyond Example 11.6.
* **The generating-function derivation (11.38)–(11.40).** It is a technique, not a stated result.
-/

open Finset LinearRecurrence Polynomial

namespace QuarteroniSaccoSaleri.Chapter11

variable {K : Type*} [Field K] {k : ℕ}

/-! ### (11.28)–(11.30): the equation and its characteristic polynomial -/

/-- **Equation (11.28)** of [quarteroni2000numerical]. Let $K$ be a field and
$\alpha_0, \dots, \alpha_{k-1} \in K$. The **linear difference equation of order $k$** with
these constant coefficients is
$$u_{n+k} + \alpha_{k-1} u_{n+k-1} + \dots + \alpha_0 u_n = \varphi_{n+k}, \qquad n \ge 0.$$
The definition is the Mathlib `LinearRecurrence` of order $k$ with coefficients $-\alpha_i$.

A sequence $u$ solves the equation with right-hand side $\varphi$ if and only if
`(equation_11_28 α).IsSolutionWith φ u` (`QuarteroniSaccoSaleri.Chapter11.equation_11_28_iff`),
and it solves the homogeneous equation (11.29) if and only if `(equation_11_28 α).IsSolution u`
(`QuarteroniSaccoSaleri.Chapter11.equation_11_29_iff`). The variable coefficients of (11.38) are
not formalized beyond Example 11.6. -/
def equation_11_28 (α : Fin k → K) : LinearRecurrence K :=
  ⟨k, fun i => -α i⟩

/-- The difference equation (11.28) has order $k$. -/
@[simp]
theorem equation_11_28_order (α : Fin k → K) : (equation_11_28 α).order = k := rfl

/-- The coefficients of (11.28) in the convention of Mathlib's `LinearRecurrence` are $-\alpha_i$.
-/
@[simp]
theorem equation_11_28_coeffs (α : Fin k → K) (i : Fin k) : (equation_11_28 α).coeffs i = -α i :=
  rfl

/-- **Equation (11.28)** of [quarteroni2000numerical]. Let $\alpha_0, \dots, \alpha_{k-1} \in K$ and
let $\varphi, u : \mathbb{N} \to K$. Then $u$ solves (11.28) with right-hand side $\varphi$ if
and only if
$$u_{n+k} + \sum_{i=0}^{k-1} \alpha_i u_{n+i} = \varphi_{n+k} \qquad \text{for every } n.$$
-/
theorem equation_11_28_iff (α : Fin k → K) (φ u : ℕ → K) :
    (equation_11_28 α).IsSolutionWith φ u ↔
      ∀ n, u (n + k) + ∑ i : Fin k, α i * u (n + i) = φ (n + k) := by
  change (∀ n, u (n + k) = ∑ i : Fin k, -α i * u (n + i) + φ (n + k)) ↔ _
  simp only [neg_mul, sum_neg_distrib, ← sub_eq_neg_add, eq_sub_iff_add_eq]

/-- **Equation (11.29)** of [quarteroni2000numerical], the homogeneous equation. Let
$\alpha_0, \dots, \alpha_{k-1} \in K$ and $u : \mathbb{N} \to K$. Then $u$ solves the
homogeneous equation if and only if
$$u_{n+k} + \sum_{i=0}^{k-1} \alpha_i u_{n+i} = 0 \qquad \text{for every } n.$$
-/
theorem equation_11_29_iff (α : Fin k → K) (u : ℕ → K) :
    (equation_11_28 α).IsSolution u ↔ ∀ n, u (n + k) + ∑ i : Fin k, α i * u (n + i) = 0 := by
  rw [← isSolutionWith_zero_iff, equation_11_28_iff]
  rfl

/-- **Equation (11.30)** of [quarteroni2000numerical]. Let $\alpha_0, \dots, \alpha_{k-1} \in K$.
The **characteristic polynomial** of the difference equation (11.28) is
$$\Pi(r) = r^k + \alpha_{k-1} r^{k-1} + \dots + \alpha_1 r + \alpha_0.$$

It is the characteristic polynomial `LinearRecurrence.charPoly` of the recurrence
(`QuarteroniSaccoSaleri.Chapter11.equation_11_30_eq`). -/
noncomputable def equation_11_30 (α : Fin k → K) : K[X] :=
  X ^ k + ∑ i : Fin k, C (α i) * X ^ (i : ℕ)

/-- **Equation (11.30)** of [quarteroni2000numerical]. The polynomial $\Pi$ is the characteristic
polynomial `LinearRecurrence.charPoly` of the recurrence
`QuarteroniSaccoSaleri.Chapter11.equation_11_28 α`. -/
theorem equation_11_30_eq (α : Fin k → K) : equation_11_30 α = (equation_11_28 α).charPoly := by
  change _ = monomial k 1 - ∑ i : Fin k, monomial (i : ℕ) (-α i)
  simp only [equation_11_30, ← C_mul_X_pow_eq_monomial, C_1, one_mul, C_neg, neg_mul,
    sum_neg_distrib, sub_neg_eq_add]

/-- The characteristic polynomial $\Pi$ has degree $k$. -/
theorem equation_11_30_degree (α : Fin k → K) : (equation_11_30 α).degree = k := by
  rw [equation_11_30_eq, charPoly_degree_eq_order, equation_11_28_order]

/-- **Equation (11.30)** of [quarteroni2000numerical], the constant term. If $k \ge 1$, then
$\Pi(0) = \alpha_0$. So the standing assumption $\alpha_0 \neq 0$ of the book says that $0$ is
not a root of $\Pi$. -/
theorem equation_11_30_eval_zero (α : Fin k → K) (hk : 0 < k) :
    (equation_11_30 α).eval 0 = α ⟨0, hk⟩ := by
  simp only [equation_11_30, eval_add, eval_pow, eval_X, zero_pow hk.ne', eval_finsetSum, eval_mul,
    eval_C, zero_add]
  rw [sum_eq_single ⟨0, hk⟩ (fun i _ hi => ?_) (by simp)]
  · simp
  · rw [zero_pow (by simpa [Fin.ext_iff] using hi), mul_zero]

/-! ### (11.31)–(11.33): the fundamental solutions -/

/-- **Equation (11.31)** of [quarteroni2000numerical]. Let $\alpha_0, \dots, \alpha_{k-1} \in K$ and
$r \in K$. The sequence $u_n = r^n$ solves the homogeneous equation (11.29) if and only if $r$
is a root of the characteristic polynomial $\Pi$. -/
theorem equation_11_31 (α : Fin k → K) (r : K) :
    ((equation_11_28 α).IsSolution fun n => r ^ n) ↔ (equation_11_30 α).IsRoot r := by
  rw [equation_11_30_eq, geom_sol_iff_root_charPoly]

/-- **Equation (11.32)** of [quarteroni2000numerical]. Let $r_0, \dots, r_{k-1} \in K$ be roots of
$\Pi$, not necessarily distinct, and let $\gamma_0, \dots, \gamma_{k-1} \in K$. Then
$$u_n = \sum_{j=0}^{k-1} \gamma_j r_j^n$$
solves the homogeneous equation (11.29), since the equation is linear. -/
theorem equation_11_32 (α : Fin k → K) {r : Fin k → K}
    (hroot : ∀ j, (equation_11_30 α).IsRoot (r j)) (γ : Fin k → K) :
    (equation_11_28 α).IsSolution fun n => ∑ j, γ j * r j ^ n := by
  have : (fun n => ∑ j, γ j * r j ^ n) = ∑ j, γ j • fun n => r j ^ n := by
    ext n; simp [Finset.sum_apply]
  rw [this, is_sol_iff_mem_solSpace]
  exact (equation_11_28 α).solSpace.sum_mem fun j _ =>
    (equation_11_28 α).solSpace.smul_mem _ ((equation_11_31 α (r j)).2 (hroot j))

/-- **Equation (11.32)** of [quarteroni2000numerical], the converse (Exercise 4 of Chapter 11). Let
$r_0, \dots, r_{k-1} \in K$ be $k$ distinct roots of $\Pi$, so that all roots of $\Pi$ are
simple. Then every solution $u$ of the homogeneous equation (11.29) has the form
$$u_n = \sum_{j=0}^{k-1} \gamma_j r_j^n \qquad \text{for every } n$$
for a unique $\gamma = (\gamma_0, \dots, \gamma_{k-1}) \in K^k$.

The coefficients $\gamma$ are fixed by the initial values $u_0, \dots, u_{k-1}$ through the
Vandermonde system of (11.37). -/
theorem equation_11_32_existsUnique (α : Fin k → K) {r : Fin k → K} (hr : Function.Injective r)
    (hroot : ∀ j, (equation_11_30 α).IsRoot (r j)) {u : ℕ → K}
    (hu : (equation_11_28 α).IsSolution u) :
    ∃! γ : Fin k → K, ∀ n, u n = ∑ j, γ j * r j ^ n := by
  have h := (equation_11_28 α).eq_sum_smul_pow_of_injective_roots hr
    (fun j => (equation_11_30_eq α) ▸ hroot j) hu
  simp only [smul_eq_mul] at h
  exact h

/-- **Equation (11.33)** of [quarteroni2000numerical], the fundamental solutions of a multiple root.
Let $r \in K$ be a root of $\Pi$ of multiplicity $m$, and let $s < m$. Then the sequence
$u_n = n^s r^n$ solves the homogeneous equation (11.29). So $r^n, n r^n, \dots, n^{m-1} r^n$ are
solutions. -/
theorem equation_11_33_isSolution (α : Fin k → K) {r : K} {s : ℕ}
    (hs : s < (equation_11_30 α).rootMultiplicity r) :
    (equation_11_28 α).IsSolution fun n => (n : K) ^ s * r ^ n :=
  (equation_11_28 α).isSolution_pow_mul_pow (equation_11_30_eq α ▸ hs)

/-- **Equation (11.33)** of [quarteroni2000numerical], the general solution. Let $k \ge 1$ and
$\alpha_0, \dots, \alpha_{k-1} \in \mathbb{C}$ with $\alpha_0 \neq 0$. Let $r_j$ be the distinct
roots of $\Pi$, with multiplicities $m_j$. Then every solution $u$ of the homogeneous equation
(11.29) has the form
$$u_n = \sum_j \Bigl(\sum_{s=0}^{m_j - 1} \gamma_{sj} n^s\Bigr) r_j^n \qquad \text{for every }
  n.$$

**Reading.** The formula needs the standing assumption $\alpha_0 \neq 0$ of the book: for
$\alpha_0 = 0$ the root $0$ contributes the sequences $n^s 0^n$, which vanish for $s \ge 1$. The
statement assumes it.

The inner sums are stated as polynomials $p_j$ of degree less than $m_j$, evaluated at $n$;
$\gamma_{sj}$ is the coefficient of $X^s$ in $p_j$. In Lean, $p$ is a function from $\mathbb{C}$
to polynomials, and the condition on the degree for a number that is not a root forces $p = 0$
there. -/
theorem equation_11_33 (α : Fin k → ℂ) (hk : 0 < k) (h0 : α ⟨0, hk⟩ ≠ 0) {u : ℕ → ℂ}
    (hu : (equation_11_28 α).IsSolution u) :
    ∃ p : ℂ → ℂ[X], (∀ r, (p r).degree < ((equation_11_30 α).rootMultiplicity r : WithBot ℕ)) ∧
      ∀ n, u n = ∑ r ∈ (equation_11_30 α).roots.toFinset, (p r).eval (n : ℂ) * r ^ n := by
  rw [equation_11_30_eq]
  refine (equation_11_28 α).exists_eq_sum_eval_mul_pow_of_splits (IsAlgClosed.splits _) ?_ hu
  rw [IsRoot.def, ← equation_11_30_eq, equation_11_30_eval_zero α hk]
  exact h0

/-! ### Examples 11.3 and 11.4 -/

/-- **Example 11.3** of [quarteroni2000numerical], the characteristic polynomial. For the equation
$u_{n+2} - u_n = 0$, that is $\alpha_0 = -1$ and $\alpha_1 = 0$, the characteristic polynomial
is $\Pi(r) = r^2 - 1$, with the roots $r_0 = -1$ and $r_1 = 1$. -/
theorem example_11_3_charPoly : equation_11_30 (K := ℝ) ![-1, 0] = X ^ 2 - 1 := by
  simp [equation_11_30, Fin.sum_univ_two]
  ring

/-- **Example 11.3** of [quarteroni2000numerical]. Let $u$ be a real solution of
$u_{n+2} - u_n = 0$. Then for every $n$,
$$u_n = \gamma_{00} (-1)^n + \gamma_{01}, \qquad \gamma_{00} = \frac{u_0 - u_1}{2}, \quad
  \gamma_{01} = \frac{u_0 + u_1}{2}.$$
-/
theorem example_11_3 {u : ℕ → ℝ} (hu : (equation_11_28 ![-1, 0]).IsSolution u) (n : ℕ) :
    u n = (u 0 - u 1) / 2 * (-1) ^ n + (u 0 + u 1) / 2 := by
  have hv : (equation_11_28 ![-1, 0]).IsSolution
      fun n => (u 0 - u 1) / 2 * (-1 : ℝ) ^ n + (u 0 + u 1) / 2 := by
    rw [equation_11_29_iff]
    intro n
    simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, add_zero]
    ring
  refine congrFun (((equation_11_28 _).eq_iff_eqOn_range_order u _ hu hv).2 fun i hi => ?_) n
  rw [coe_range, Set.mem_Iio, equation_11_28_order] at hi
  interval_cases i <;> simp <;> ring

/-- **Example 11.4** of [quarteroni2000numerical], the characteristic polynomial. For the equation
$u_{n+3} - 2u_{n+2} - 7u_{n+1} - 4u_n = 0$, the characteristic polynomial is
$$\Pi(r) = r^3 - 2r^2 - 7r - 4 = (r + 1)^2 (r - 4).$$
So the roots are $r_0 = -1$, with multiplicity $2$, and $r_1 = 4$. -/
theorem example_11_4_charPoly :
    equation_11_30 (K := ℝ) ![-4, -7, -2] = X ^ 3 - 2 * X ^ 2 - 7 * X - 4 ∧
      equation_11_30 (K := ℝ) ![-4, -7, -2] = (X + 1) ^ 2 * (X - 4) := by
  have : equation_11_30 (K := ℝ) ![-4, -7, -2] = X ^ 3 - 2 * X ^ 2 - 7 * X - 4 := by
    simp [equation_11_30, Fin.sum_univ_three, map_ofNat]
    ring
  exact ⟨this, this.trans (by ring)⟩

/-- **Example 11.4** of [quarteroni2000numerical]. Let $u$ be a real solution of
$u_{n+3} - 2u_{n+2} - 7u_{n+1} - 4u_n = 0$. Then for every $n$,
$$u_n = (\gamma_{00} + n\gamma_{10})(-1)^n + \gamma_{01} 4^n$$
with
$$\gamma_{00} = \frac{24u_0 - 2u_1 - u_2}{25}, \quad \gamma_{10} = \frac{u_2 - 3u_1 - 4u_0}{5},
  \quad \gamma_{01} = \frac{2u_1 + u_0 + u_2}{25}.$$

These coefficients solve the linear system of the initial conditions. -/
theorem example_11_4 {u : ℕ → ℝ} (hu : (equation_11_28 ![-4, -7, -2]).IsSolution u) (n : ℕ) :
    u n = ((24 * u 0 - 2 * u 1 - u 2) / 25 + n * ((u 2 - 3 * u 1 - 4 * u 0) / 5)) * (-1) ^ n +
      (2 * u 1 + u 0 + u 2) / 25 * 4 ^ n := by
  have hv : (equation_11_28 ![-4, -7, -2]).IsSolution fun n : ℕ =>
      ((24 * u 0 - 2 * u 1 - u 2) / 25 + n * ((u 2 - 3 * u 1 - 4 * u 0) / 5)) * (-1 : ℝ) ^ n +
        (2 * u 1 + u 0 + u 2) / 25 * 4 ^ n := by
    rw [equation_11_29_iff]
    intro n
    simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
      Fin.val_two, add_zero]
    push_cast
    ring
  refine congrFun (((equation_11_28 _).eq_iff_eqOn_range_order u _ hu hv).2 fun i hi => ?_) n
  rw [coe_range, Set.mem_Iio, equation_11_28_order] at hi
  interval_cases i <;> simp <;> ring

/-! ### (11.34)–(11.37): the Kronecker fundamental solutions -/

/-- **Equation (11.34)** of [quarteroni2000numerical]. Let $\alpha_0, \dots, \alpha_{k-1} \in K$ and
$0 \le j \le k - 1$. The **fundamental solution** $\psi_j$ is the solution of the homogeneous
equation (11.29) with the initial values
$$\psi_j^{(i)} = \delta_{ij}, \qquad i = 0, \dots, k - 1.$$

The definition is `LinearRecurrence.kroneckerSol`. -/
noncomputable def equation_11_34 (α : Fin k → K) (j : Fin k) : ℕ → K :=
  (equation_11_28 α).kroneckerSol j

/-- The fundamental solutions $\psi_j$ of (11.34) solve the homogeneous equation (11.29). -/
theorem equation_11_34_isSolution (α : Fin k → K) (j : Fin k) :
    (equation_11_28 α).IsSolution (equation_11_34 α j) :=
  (equation_11_28 α).isSolution_kroneckerSol j

/-- **Equation (11.34)** of [quarteroni2000numerical], the initial values for a natural number
index. For every natural number $i < k$ and every $j$, $\psi_j^{(i)} = \delta_{ij}$. -/
theorem equation_11_34_apply_of_lt (α : Fin k → K) (j : Fin k) {i : ℕ} (hi : i < k) :
    equation_11_34 α j i = if i = j then 1 else 0 :=
  (equation_11_28 α).kroneckerSol_apply_of_lt j hi

/-- **Equation (11.34)** of [quarteroni2000numerical], the initial values. For all
$i, j \in \{0, \dots, k - 1\}$, $\psi_j^{(i)} = \delta_{ij}$. -/
theorem equation_11_34_apply (α : Fin k → K) (i j : Fin k) :
    equation_11_34 α j i = if i = j then 1 else 0 := by
  rw [equation_11_34_apply_of_lt α j i.is_lt]
  simp [Fin.ext_iff]

/-- **Equation (11.35)** of [quarteroni2000numerical]. Let $u$ solve the homogeneous equation
(11.29). Then for every $n$,
$$u_n = \sum_{j=0}^{k-1} u_j \psi_j^{(n)}.$$
-/
theorem equation_11_35 (α : Fin k → K) {u : ℕ → K} (hu : (equation_11_28 α).IsSolution u) (n : ℕ) :
    u n = ∑ j : Fin k, u j * equation_11_34 α j n :=
  (equation_11_28 α).eq_sum_kroneckerSol hu n

/-- **Equation (11.37)** of [quarteroni2000numerical], the matrix. For $r_0, \dots, r_{k-1} \in K$,
the matrix $R \in K^{k \times k}$ has the entries
$$r_{im} = r_m^i, \qquad i, m = 0, \dots, k - 1.$$

It is the transpose of Mathlib's Vandermonde matrix `Matrix.vandermonde r`, whose entries are
$r_i^m$. -/
def equation_11_37_matrix (r : Fin k → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i m => r m ^ (i : ℕ)

/-- The matrix $R$ of (11.37) is the transpose of the Vandermonde matrix `Matrix.vandermonde r`. -/
theorem equation_11_37_matrix_eq (r : Fin k → K) :
    equation_11_37_matrix r = (Matrix.vandermonde r).transpose := rfl

/-- **Equation (11.37)** of [quarteroni2000numerical], nonsingularity (Exercise 5 of Chapter 11). If
$r_0, \dots, r_{k-1} \in K$ are distinct, for example the roots of $\Pi$ when they are all
simple, then $\det R \neq 0$. -/
theorem equation_11_37_det_ne_zero {r : Fin k → K} (hr : Function.Injective r) :
    (equation_11_37_matrix r).det ≠ 0 :=
  det_vandermonde_transpose_ne_zero hr

/-- **Equation (11.36)** of [quarteroni2000numerical]. Let $r_0, \dots, r_{k-1} \in K$ be $k$
distinct roots of $\Pi$, and let $0 \le j \le k - 1$. Then there is a unique row
$b_j = (\beta_{j,0}, \dots, \beta_{j,k-1})$ with
$$\psi_j^{(n)} = \sum_{m=0}^{k-1} \beta_{j,m} r_m^n \qquad \text{for every } n.$$
-/
theorem equation_11_36 (α : Fin k → K) {r : Fin k → K} (hr : Function.Injective r)
    (hroot : ∀ j, (equation_11_30 α).IsRoot (r j)) (j : Fin k) :
    ∃! β : Fin k → K, ∀ n, equation_11_34 α j n = ∑ m, β m * r m ^ n :=
  equation_11_32_existsUnique α hr hroot (equation_11_34_isSolution α j)

/-- **Equation (11.37)** of [quarteroni2000numerical]. Let $r_0, \dots, r_{k-1} \in K$, let
$0 \le j \le k - 1$, and let $b_j = (\beta_{j,0}, \dots, \beta_{j,k-1})$ satisfy
$\psi_j^{(n)} = \sum_m \beta_{j,m} r_m^n$ for every $n$. Then $b_j$ solves the linear system
$$R b_j = e_j,$$
where $R = (r_m^i)$ and $e_j$ is the $j$-th unit vector.

The statement has no hypothesis on the $r_m$: the system follows from the initial values (11.34)
alone. -/
theorem equation_11_37 (α : Fin k → K) (r : Fin k → K) (j : Fin k) (β : Fin k → K)
    (hβ : ∀ n, equation_11_34 α j n = ∑ m, β m * r m ^ n) :
    (equation_11_37_matrix r).mulVec β = Pi.single j 1 := by
  ext i
  have := hβ i
  rw [equation_11_34_apply] at this
  simp only [equation_11_37_matrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.single_apply]
  rw [this]
  exact sum_congr rfl fun m _ => mul_comm _ _

/-! ### Example 11.5 -/

/-- **Example 11.5** of [quarteroni2000numerical], the matrix. For the equation of Example 11.4,
with the fundamental system $(-1)^n$, $n(-1)^n$, $4^n$, the matrix of (11.37) has the entries
$(-1)^i$, $i(-1)^i$ and $4^i$ in its three columns, $i = 0, 1, 2$:
$$R = \begin{bmatrix} r_0^0 & 0 & r_2^0 \\ r_0^1 & r_0^1 & r_2^1 \\ r_0^2 & 2r_0^2 & r_2^2
  \end{bmatrix} = \begin{bmatrix} 1 & 0 & 1 \\ -1 & -1 & 4 \\ 1 & 2 & 16 \end{bmatrix}.$$

**Reading.** The book writes $r_2$ for the root $4$, which Example 11.4 calls $r_1$. The matrix
is the one printed. -/
theorem example_11_5_matrix :
    (Matrix.of fun i m : Fin 3 => ![(-1 : ℝ) ^ (i : ℕ), i * (-1) ^ (i : ℕ), 4 ^ (i : ℕ)] m) =
      !![1, 0, 1; -1, -1, 4; 1, 2, 16] := by
  ext i m
  fin_cases i <;> fin_cases m <;> norm_num

/-- **Example 11.5** of [quarteroni2000numerical]. For the equation
$u_{n+3} - 2u_{n+2} - 7u_{n+1} - 4u_n = 0$ of Example 11.4, the fundamental solutions (11.34)
are, for every $n$,
$$\begin{aligned} \psi_0^{(n)} &= \tfrac{24}{25}(-1)^n - \tfrac{4}{5} n (-1)^n + \tfrac{1}{25}
  4^n, \\ \psi_1^{(n)} &= -\tfrac{2}{25}(-1)^n - \tfrac{3}{5} n (-1)^n + \tfrac{2}{25} 4^n, \\
  \psi_2^{(n)} &= -\tfrac{1}{25}(-1)^n + \tfrac{1}{5} n (-1)^n + \tfrac{1}{25} 4^n.
  \end{aligned}$$

The book obtains them by solving the three systems (11.37). With (11.35),
$u_n = \sum_j u_j \psi_j^{(n)}$ is the solution of Example 11.4
(`QuarteroniSaccoSaleri.Chapter11.example_11_4`). -/
theorem example_11_5 (n : ℕ) :
    equation_11_34 (K := ℝ) ![-4, -7, -2] 0 n =
        24 / 25 * (-1) ^ n - 4 / 5 * n * (-1) ^ n + 1 / 25 * 4 ^ n ∧
      equation_11_34 (K := ℝ) ![-4, -7, -2] 1 n =
        -(2 / 25) * (-1) ^ n - 3 / 5 * n * (-1) ^ n + 2 / 25 * 4 ^ n ∧
      equation_11_34 (K := ℝ) ![-4, -7, -2] 2 n =
        -(1 / 25) * (-1) ^ n + 1 / 5 * n * (-1) ^ n + 1 / 25 * 4 ^ n := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [example_11_4 (equation_11_34_isSolution _ _) n,
      equation_11_34_apply_of_lt _ _ (by norm_num : (0 : ℕ) < 3),
      equation_11_34_apply_of_lt _ _ (by norm_num : (1 : ℕ) < 3),
      equation_11_34_apply_of_lt _ _ (by norm_num : (2 : ℕ) < 3)]
    norm_num [Fin.val_zero, Fin.val_one, Fin.val_two]
    ring

/-! ### Example 11.6: a variable-coefficient equation -/

/-- **Example 11.6** of [quarteroni2000numerical]. Let $u$ be a real sequence that satisfies the
difference equation (11.41),
$$(n + 2)(n + 1) u_{n+2} - 2(n + 1) u_{n+1} - 3u_n = 0, \qquad n \ge 0,$$
with the initial values $u_0 = u_1 = 2$. Then $u_n = ((-1)^n + 3^n)/n!$ for every $n$.

These are the coefficients of the generating function $F(t) = e^{3t} + e^{-t}$, which solves
$F'' - 2F' - 3F = 0$ with $F(0) = F'(0) = 2$. The proof does not use the generating function. It
checks that the closed form satisfies the equation and the initial values; the equation
determines $u_{n+2}$, since its leading coefficient $(n + 2)(n + 1)$ is not zero. -/
theorem example_11_6 {u : ℕ → ℝ}
    (hu : ∀ n : ℕ, ((n : ℝ) + 2) * (n + 1) * u (n + 2) - 2 * (n + 1) * u (n + 1) - 3 * u n = 0)
    (h0 : u 0 = 2) (h1 : u 1 = 2) (n : ℕ) : u n = ((-1) ^ n + 3 ^ n) / n.factorial := by
  set v : ℕ → ℝ := fun n => ((-1) ^ n + 3 ^ n) / n.factorial with hv
  have hstep : ∀ n : ℕ, u n = v n → u (n + 1) = v (n + 1) → u (n + 2) = v (n + 2) := by
    intro n hn hn1
    have h := hu n
    rw [hn, hn1] at h
    have hf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    have hpos : ((n : ℝ) + 2) * (n + 1) ≠ 0 := by positivity
    simp only [hv, Nat.factorial_succ] at h ⊢
    push_cast at h ⊢
    field_simp at h ⊢
    linear_combination h
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by norm_num [hv, h0], by norm_num [hv, h1]⟩
    | succ n ih => exact ⟨ih.2, hstep n ih.1 ih.2⟩
  exact (key n).1

/-! ### Example 11.7: the method of undetermined coefficients -/

/-- **Example 11.7** of [quarteroni2000numerical]. The sequence
$$u_n = 2^n (b_2 n^2 + b_1 n + b_0), \qquad b_2 = \frac{1}{5}, \quad b_1 = -\frac{36}{25}, \quad
  b_0 = \frac{358}{125},$$
is a particular solution of $u_{n+3} - u_{n+2} + u_{n+1} - u_n = 2^n n^2$: the equation holds
for every $n$.

In the book, the substitution of the ansatz gives $5b_2 n^2 + (36b_2 + 5b_1) n + (58b_2 +
18b_1 + 5b_0) = n^2$, and the principle of identity for polynomials determines the coefficients. -/
theorem example_11_7 (n : ℕ) :
    let u : ℕ → ℝ := fun n => 2 ^ n * ((n : ℝ) ^ 2 / 5 - 36 * n / 25 + 358 / 125)
    u (n + 3) - u (n + 2) + u (n + 1) - u n = 2 ^ n * (n : ℝ) ^ 2 := by
  intro u
  simp only [u]
  push_cast
  ring

/-- **Example 11.7** of [quarteroni2000numerical], in the form (11.28). The sequence
$u_n = 2^n (n^2/5 - 36n/25 + 358/125)$ solves (11.28) with $\alpha = (-1, 1, -1)$ and the
right-hand side $\varphi_{n+3} = 2^n n^2$.

The right-hand side is given as $\varphi_m = 2^{m-3} (m - 3)^2$; its values for $m < 3$ are
never read. -/
theorem example_11_7_isSolutionWith :
    (equation_11_28 ![-1, 1, -1]).IsSolutionWith
      (fun m => 2 ^ (m - 3) * ((m : ℝ) - 3) ^ 2)
      (fun n => 2 ^ n * ((n : ℝ) ^ 2 / 5 - 36 * n / 25 + 358 / 125)) := by
  rw [equation_11_28_iff]
  intro n
  simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two,
    add_zero, Nat.add_sub_cancel]
  push_cast
  ring

/-! ### (11.42): the inhomogeneous equation -/

/-- **Equation (11.42)** of [quarteroni2000numerical], the solution of the inhomogeneous equation.
Let $k \ge 1$, and let $u$ solve (11.28) with right-hand side $\varphi$. Then for every $n$,
$$u_n = \sum_{j=0}^{k-1} u_j \psi_j^{(n)} + \sum_{l=k}^{n} \varphi_l \,
  \psi_{k-1}^{(n-l+k-1)}.$$

The book uses the conventions $\psi_{k-1}^{(i)} = 0$ for $i < 0$ and $\varphi_j = 0$ for
$j < k$. Here the second sum runs over $k \le l \le n$ only, so that every index is a natural
number, and the values $\varphi_j$, $j < k$, are never read. -/
theorem equation_11_42 (α : Fin k → K) (hk : 0 < k) {φ u : ℕ → K}
    (hu : (equation_11_28 α).IsSolutionWith φ u) (n : ℕ) :
    u n = (∑ j : Fin k, u j * equation_11_34 α j n) +
      ∑ l ∈ Icc k n, φ l * equation_11_34 α ⟨k - 1, by omega⟩ (n - l + (k - 1)) :=
  eq_sum_kroneckerSol_add_sum hk hu n

end QuarteroniSaccoSaleri.Chapter11
