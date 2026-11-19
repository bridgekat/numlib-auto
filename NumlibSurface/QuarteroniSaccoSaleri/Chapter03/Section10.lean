/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section09

/-!
# Quarteroni, Sacco and Saleri, Section 3.10: Accuracy of the solution achieved using GEM

This module formalizes Section 3.10 of [quarteroni2000numerical]. The solution $\hat x$ that
Gaussian elimination computes in floating-point arithmetic with unit roundoff $u$ is the exact
solution of a perturbed system $(A + \delta A)\hat x = b$. The size of $\delta A$ is controlled by
the computed factors $|\hat L||\hat U|$ (3.64)–(3.65), and through them by the growth factor
$$\rho_n = \frac{\max_{i,j,k} |a^{(k)}_{ij}|}{\max_{i,j} |a_{ij}|}$$
of (3.66), which gives Wilkinson's bound $\|\delta A\|_\infty \lesssim n^3 u \rho_n \|A\|_\infty$
(3.67). The module states these bounds, the known bounds on $\rho_n$ for partial pivoting, for
special classes of matrices and for complete pivoting, and the examples that show the role of the
condition number: a small residual need not mean a small error.

The proofs specialize the backbone modules `Numlib.FloatingPoint.LU` (the backward error of the LU
solve, `FloatingPoint.exists_roundsLU_solve_eq`, and Wilkinson's normwise bound
`FloatingPoint.linfty_opNorm_le_of_roundsLU_solve`) and `Numlib.LinearAlgebra.Matrix.LU.Pivoting`
(the growth factor `Matrix.growthFactor` and its bounds).

## Main definitions

* (3.66), `QuarteroniSaccoSaleri.Chapter03.equation_3_66`: the growth factor $\rho_n$ of Gaussian
  elimination.

## Main results

* (3.64), `QuarteroniSaccoSaleri.Chapter03.equation_3_64`: the computed solution solves
  $(A + \delta A)\hat x = b$ with $|\delta A| \le \gamma_{3n} |\hat L||\hat U|$.
* (3.65), `QuarteroniSaccoSaleri.Chapter03.equation_3_65`: with multipliers bounded by $1$,
  $\|\delta A\|_\infty \le n\gamma_{3n} \|\hat U\|_\infty$.
* (3.66), `QuarteroniSaccoSaleri.Chapter03.equation_3_66_spec`: the formula for $\rho_n$, and
  $|a^{(k)}_{ij}| \le \rho_n \max_{i,j} |a_{ij}|$.
* (3.67), `QuarteroniSaccoSaleri.Chapter03.equation_3_67`: Wilkinson's bound $\|\delta A\|_\infty
  \le n^2 \gamma_{3n} \rho \|A\|_\infty$, in conditional form.
* Section 3.10, `QuarteroniSaccoSaleri.Chapter03.growthFactor_le_two_pow`: $\rho_n \le 2^{n-1}$ for
  multipliers bounded by $1$, in particular with partial pivoting.
* Section 3.10, item (1), `QuarteroniSaccoSaleri.Chapter03.growthFactor_tridiagonal`: $\rho_n \le 2$
  for tridiagonal matrices with partial pivoting.
* Section 3.10, item (2), `QuarteroniSaccoSaleri.Chapter03.growthFactor_hessenberg`: $\rho_n \le n$
  for upper Hessenberg matrices with partial pivoting.
* Section 3.10, item (3), `QuarteroniSaccoSaleri.Chapter03.growthFactor_posDef`: $\rho_n = 1$ for
  symmetric positive definite matrices.
* Section 3.10, item (4), `QuarteroniSaccoSaleri.Chapter03.growthFactor_colDiagDominant`:
  $\rho_n \le 2$ for matrices strictly diagonally dominant by columns.
* Section 3.10, `QuarteroniSaccoSaleri.Chapter03.growthFactor_completePivoting`: Wilkinson's bound
  $\rho_n \le n^{1/2}(2 \cdot 3^{1/2} \cdots n^{1/(n-1)})^{1/2}$ for complete pivoting.
* Example 3.7, `QuarteroniSaccoSaleri.Chapter03.example_3_7_cond`: the matrix $\begin{bmatrix}
  \varepsilon & 1 \\ 1 & 0 \end{bmatrix}$ is well conditioned.
* Example 3.7 and Exercise 6, `QuarteroniSaccoSaleri.Chapter03.example_3_7_lu`: its LU factorization
  has large entries without pivoting and bounded entries with partial pivoting.
* Section 3.10, `QuarteroniSaccoSaleri.Chapter03.residual_error_bound`: the relative error is
  bounded by the condition number times the relative residual.
* Example 3.8, `QuarteroniSaccoSaleri.Chapter03.example_3_8`: an ill-conditioned system with a small
  residual and a large error.
* Section 3.10, `QuarteroniSaccoSaleri.Chapter03.equation_3_69`: if $u K_\infty(A) \le 1/2$, the
  relative error is at most $4u K_\infty(A)$.

## Conventions

* The computed solution $\hat x$ of $Ax = b$ by GEM is described relationally: computed factors
  $\hat L$, $\hat U$ (an admissible `FloatingPoint.RoundsLU m A L̂ Û`), then a forward substitution
  `FloatingPoint.RoundsForwardSubst m L̂ b ŷ` and a backward substitution
  `FloatingPoint.RoundsBackSubst m Û ŷ x̂`. All of them are in the relational rounding model
  `m : FloatingPoint.RoundingModel ℝ` with unit roundoff `m.u`.
* The constant $\gamma_k = ku/(1 - ku)$ is `FloatingPoint.gamma m.u k`.
* The growth factor $\rho_n$ of (3.66) is `Matrix.growthFactor A`, defined on the exact stages
  `Matrix.gemStage A k` of Gaussian elimination without pivoting. For GEM with partial pivoting it
  is `growthFactor (P A)` with $P$ the permutation matrix of Section 3.5, because the pivoted stages
  are the plain stages of $PA$ up to the order of the rows.
* The number $\max_{i,j} |a_{ij}|$ is `Matrix.supAbs A`.
* Norms are the $\infty$-norms of Section 3.1. The matrix norm $\|A\|_\infty$ is the scoped
  Mathlib norm `Matrix.Norms.Operator`. The sup norm of `Fin n → ℝ` is the vector norm
  $\|x\|_\infty$. The condition number $K_\infty(A)$ is
  `QuarteroniSaccoSaleri.Chapter03.condNumber ⊤ A`.

## Deviations from the source

* **(3.64)–(3.65)** (reading). The source prints bounds of first order in $u$, such as $|\delta A|
  \le nu(3|A| + 5|\hat L||\hat U|) + O(u^2)$. The module states the rigorous forms of Theorem 9.4 of
  [higham2002accuracy] with $\gamma_{3n} = 3nu + O(u^2)$, which imply the printed ones to first
  order. See `QuarteroniSaccoSaleri.Chapter03.equation_3_64` and
  `QuarteroniSaccoSaleri.Chapter03.equation_3_65`.
* **(3.66)** (reading). The source defines $\rho_n$ with the computed entries $\hat a^{(k)}_{ij}$.
  The definition uses the exact stages, for which bounds are available. See
  `QuarteroniSaccoSaleri.Chapter03.equation_3_66`.
* **(3.67)** (reading). The source prints $\|\delta A\|_\infty \le 8un^3\rho_n\|A\|_\infty +
  O(u^2)$. The module states the conditional form of Theorem 9.5 of [higham2002accuracy], $\|\delta
  A\|_\infty \le n^2\gamma_{3n}\rho\|A\|_\infty$ under bounds on the computed factors. See
  `QuarteroniSaccoSaleri.Chapter03.equation_3_67`.

## Not formalized

* **The banded bound of item (1)**, Bohte's $\rho_n \le 2^{2p-1} - (p - 1)2^{p-2}$ for band width
  $p$. Neither this book nor [higham2002accuracy] (Theorem 9.11) proves it; both cite Bohte (1975),
  and Problem 9.15 of [higham2002accuracy] records the general case as an open research problem. The
  backbone proves the weaker bound $\rho_n \le 2^{p+q}$ for lower bandwidth $p$ and upper bandwidth
  $q$ (`Matrix.growthFactor_le_two_pow_of_hasBandwidth`), which is not restated here because it is
  not the book's inequality.
* **The estimate** $\simeq u K_\infty(A)$ of (3.69), and the count of $t - m$ exact digits, which
  are heuristics.
-/

open Finset Matrix
open scoped ENNReal

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### (3.64)–(3.67): the backward error of GEM and the growth factor -/

section Backward

open FloatingPoint
open scoped Matrix.Norms.Operator

variable {m : RoundingModel ℝ} {A L U : Matrix (Fin n) (Fin n) ℝ} {b y x : Fin n → ℝ}

/-- **Equation (3.64)** of [quarteroni2000numerical], rigorous form. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, $b \in \mathbb{R}^n$, and let $u$ be the unit
roundoff of a rounding model with $3nu < 1$. Let $\hat L$, $\hat U$ be the factors that GEM
computes in floating-point arithmetic, with nonzero computed pivots, let $\hat y$ be the
computed solution of $\hat L y = b$ by forward substitution, and let $\hat x$ be the computed
solution of $\hat U x = \hat y$ by backward substitution. Then there is a matrix $\delta A$ with
$$(A + \delta A)\hat x = b, \qquad |\delta A| \le \gamma_{3n} |\hat L||\hat U|, \qquad
  \gamma_{3n} = \frac{3nu}{1 - 3nu},$$
where the absolute values and the inequality are entrywise.

**Reading.** The source prints the first-order bound $|\delta A| \le nu(3|A| + 5|\hat L||\hat
U|) + O(u^2)$, after [golub2013matrix]. The theorem states the rigorous form of Theorem 9.4 of
[higham2002accuracy]. Since $\gamma_{3n} = 3nu + O(u^2)$ and $|A| \le |\hat L||\hat U| + O(u)$
by (3.40), it implies the printed bound.

The proof uses `FloatingPoint.exists_roundsLU_solve_eq`. -/
theorem equation_3_64 [NeZero n] (hn : ((3 * n : ℕ) : ℝ) * m.u < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) (hy : RoundsForwardSubst m L b y) (hx : RoundsBackSubst m U y x) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      δA.abs ≤ₑ ((3 * n : ℕ) * m.u / (1 - (3 * n : ℕ) * m.u)) • (L.abs * U.abs) ∧
        (A + δA) *ᵥ x = b := by
  have hu : m.u < 1 := by
    have h1 : (1 : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by norm_num) (NeZero.ne n))
    nlinarith [m.u_nonneg]
  obtain ⟨δA, hδA, hAx⟩ := exists_roundsLU_solve_eq hu (by rwa [Fintype.card_fin]) h hd hy hx
  refine ⟨δA, ?_, hAx⟩
  rwa [Fintype.card_fin, gamma_def] at hδA

/-- **Equation (3.65)** of [quarteroni2000numerical], rigorous form. In the setting of (3.64), with
$3nu < 1$ and $n \ge 1$, assume moreover that the computed multipliers satisfy
$|\hat l_{ij}| \le 1$, as partial pivoting gives. Then $\|\hat L\|_\infty \le n$, and there is a
matrix $\delta A$ with
$$(A + \delta A)\hat x = b, \qquad \|\delta A\|_\infty \le n \gamma_{3n} \|\hat U\|_\infty.$$

**Reading.** The source prints the first-order bound $\|\delta A\|_\infty \le nu(3\|A\|_\infty +
5n\|\hat U\|_\infty) + O(u^2)$. It follows from the theorem as for (3.64).

The proof uses `Matrix.linfty_opNorm_le_of_abs_entrywiseLE` and the submultiplicativity of
$\|\cdot\|_\infty$. -/
theorem equation_3_65 [NeZero n] (hn : ((3 * n : ℕ) : ℝ) * m.u < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) (hy : RoundsForwardSubst m L b y) (hx : RoundsBackSubst m U y x)
    (hL : ∀ i j, |L i j| ≤ 1) :
    ‖L‖ ≤ n ∧ ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      ‖δA‖ ≤ n * ((3 * n : ℕ) * m.u / (1 - (3 * n : ℕ) * m.u)) * ‖U‖ ∧ (A + δA) *ᵥ x = b := by
  have hLn : ‖L‖ ≤ n := linfty_opNorm_le_of_forall_sum_le (Nat.cast_nonneg n) fun i => by
    calc ∑ j, |L i j| ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ => hL i j
      _ = n := by simp
  obtain ⟨δA, hδA, hAx⟩ := equation_3_64 hn h hd hy hx
  refine ⟨hLn, δA, ?_, hAx⟩
  set γ : ℝ := (3 * n : ℕ) * m.u / (1 - (3 * n : ℕ) * m.u) with hγ
  have hγ0 : 0 ≤ γ := by
    rw [hγ]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) m.u_nonneg) (by linarith)
  have h1 : ‖δA‖ ≤ ‖γ • (L.abs * U.abs)‖ := by
    refine linfty_opNorm_le_of_abs_entrywiseLE fun i j => ?_
    have := hδA i j
    have hM : 0 ≤ (L.abs * U.abs) i j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    simp only [Matrix.abs_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
    rw [abs_mul, abs_of_nonneg hγ0, abs_of_nonneg hM]
    exact this
  calc ‖δA‖ ≤ ‖γ • (L.abs * U.abs)‖ := h1
    _ = γ * ‖L.abs * U.abs‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
    _ ≤ γ * (‖L.abs‖ * ‖U.abs‖) := mul_le_mul_of_nonneg_left (linfty_opNorm_mul _ _) hγ0
    _ = γ * (‖L‖ * ‖U‖) := by rw [Matrix.linfty_opNorm_abs, Matrix.linfty_opNorm_abs]
    _ ≤ γ * (n * ‖U‖) := by gcongr
    _ = n * γ * ‖U‖ := by ring

/-- **Equation (3.66)** of [quarteroni2000numerical], the **growth factor** of Gaussian elimination
on $A \in \mathbb{R}^{n \times n}$:
$$\rho_n = \frac{\max_{i,j,k} |a^{(k)}_{ij}|}{\max_{i,j} |a_{ij}|},$$
where $A^{(k)}$, $k = 1, \ldots, n$, are the stages of Gaussian elimination without pivoting.
For the zero matrix, $\rho_n = 0$.

**Reading.** The source writes the computed entries $\hat a^{(k)}_{ij}$. The definition uses the
exact stages `Matrix.gemStage A k`, for which bounds are available ([higham2002accuracy], after
Theorem 9.5).

The definition is `Matrix.growthFactor A`. For GEM with partial pivoting, the growth factor is
that of $PA$, where $P$ is the permutation matrix of Section 3.5. -/
noncomputable def equation_3_66 (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := growthFactor A

/-- **Equation (3.66)** of [quarteroni2000numerical], spelled out. Let
$A \in \mathbb{R}^{n \times n}$. The growth factor $\rho_n$ is the largest entry in modulus of
any stage $A^{(k)}$ divided by the largest entry in modulus of $A$. Moreover, every entry of
every stage, of $U = A^{(n)}$ in particular, satisfies
$$|a^{(k)}_{ij}| \le \rho_n \max_{i,j} |a_{ij}|.$$

The maximum over the stages runs over the $0$-based stages $k = 0, \ldots, n - 1$ of
`Matrix.gemStage`, which are the book's $A^{(1)}, \ldots, A^{(n)}$; the bound holds for every
$k \in \mathbb{N}$. The proof uses `Matrix.abs_gemStage_le_growthFactor_mul_supAbs`.

**Reading.** Spells out the exact-stage quotient and entry bounds.
-/
theorem equation_3_66_spec (A : Matrix (Fin n) (Fin n) ℝ) :
    equation_3_66 A =
      (⨆ p : Fin n × Fin n × Fin n, |gemStage A p.1 p.2.1 p.2.2|) /
        ⨆ p : Fin n × Fin n, |A p.1 p.2| ∧
    ∀ (k : ℕ) (i j : Fin n),
      |gemStage A k i j| ≤ equation_3_66 A * ⨆ p : Fin n × Fin n, |A p.1 p.2| :=
  ⟨rfl, fun k i j => abs_gemStage_le_growthFactor_mul_supAbs A k i j⟩

/-- **Equation (3.67)** of [quarteroni2000numerical] (Wilkinson's bound), conditional form. In the
setting of (3.64), with $3nu < 1$ and $n \ge 1$, let $\rho \ge 0$, and assume that the computed
factors satisfy $|\hat l_{ij}| \le 1$ and $|\hat u_{ij}| \le \rho \max_{i,j} |a_{ij}|$ for all
$i, j$. Then there is a matrix $\delta A$ with
$$(A + \delta A)\hat x = b, \qquad \|\delta A\|_\infty \le n^2 \gamma_{3n} \rho \|A\|_\infty.$$

**Reading.** The source prints $\|\delta A\|_\infty \le 8un^3\rho_n\|A\|_\infty + O(u^2)$, and
it uses for the computed factors the bounds $|l_{ij}| \le 1$ and
$|u_{ij}| \le \rho_n \max_{i,j}|a_{ij}|$ of the exact factors, as [higham2002accuracy] does. The
theorem makes these bounds hypotheses, in the conditional form of Theorem 9.5 of
[higham2002accuracy]. Its constant $n^2\gamma_{3n} = 3n^3u + O(u^2)$ differs from the book's
$8n^3u$ only in the numerical factor.

The proof uses `FloatingPoint.linfty_opNorm_le_of_roundsLU_solve`. -/
theorem equation_3_67 [NeZero n] (hn : ((3 * n : ℕ) : ℝ) * m.u < 1) (h : RoundsLU m A L U)
    (hd : ∀ j, U j j ≠ 0) (hy : RoundsForwardSubst m L b y) (hx : RoundsBackSubst m U y x)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hL : ∀ i j, |L i j| ≤ 1)
    (hU : ∀ i j, |U i j| ≤ ρ * ⨆ p : Fin n × Fin n, |A p.1 p.2|) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      ‖δA‖ ≤ (n : ℝ) ^ 2 * ((3 * n : ℕ) * m.u / (1 - (3 * n : ℕ) * m.u)) * ρ * ‖A‖ ∧
        (A + δA) *ᵥ x = b := by
  have hu : m.u < 1 := by
    have h1 : (1 : ℝ) ≤ ((3 * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by norm_num) (NeZero.ne n))
    nlinarith [m.u_nonneg]
  obtain ⟨δA, hδA, hAx⟩ := linfty_opNorm_le_of_roundsLU_solve hu (by rwa [Fintype.card_fin]) h hd
    hy hx hρ hL hU
  refine ⟨δA, ?_, hAx⟩
  rwa [Fintype.card_fin, gamma_def] at hδA

end Backward

/-! ### The bounds on the growth factor -/

section Growth

variable (A : Matrix (Fin n) (Fin n) ℝ)

/-- **Section 3.10** of [quarteroni2000numerical], the bound $\rho_n \le 2^{n-1}$. Let
$A \in \mathbb{R}^{n \times n}$. If all multipliers of Gaussian elimination have modulus at most
$1$, that is, $|a^{(k)}_{ik} / a^{(k)}_{kk}| \le 1$ for all $k < n$ and $i > k$, then
$\rho_n \le 2^{n-1}$. In particular, for the permutation matrix $P$ of GEM with partial
pivoting, $\rho_n(PA) \le 2^{n-1}$.

The matrix of Exercise 5 attains the bound. A zero pivot gives a zero multiplier in Lean. The
proof uses `Matrix.growthFactor_le_two_pow` and
`Matrix.growthFactor_le_two_pow_of_partialPivotRow`.

**Reading.** Exact-stage bound assumes bounded multipliers, including partial pivoting.
-/
theorem growthFactor_le_two_pow :
    ((∀ (k : ℕ) (hk : k < n) (i : Fin n), ⟨k, hk⟩ < i →
      |gemStage A k i ⟨k, hk⟩ / gemStage A k ⟨k, hk⟩ ⟨k, hk⟩| ≤ 1) →
      equation_3_66 A ≤ 2 ^ (n - 1)) ∧
    equation_3_66 ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) ≤ 2 ^ (n - 1) :=
  ⟨fun hmul => Matrix.growthFactor_le_two_pow A hmul, growthFactor_le_two_pow_of_partialPivotRow A⟩

/-- **Section 3.10** of [quarteroni2000numerical], item (1), the tridiagonal case. Let
$A \in \mathbb{R}^{n \times n}$ be tridiagonal, and let $P$ be the permutation matrix of GEM
with partial pivoting. Then $\rho_n(PA) \le 2$.

This is the case $p = 1$ of Bohte's banded bound, which is not formalized. The proof uses
`Matrix.growthFactor_le_two_of_isTridiagonal`.

**Reading.** The factor 2 bounds the exact-stage quotient.
-/
theorem growthFactor_tridiagonal (hA : A.IsTridiagonal) :
    equation_3_66 ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) ≤ 2 :=
  growthFactor_le_two_of_isTridiagonal hA

/-- **Section 3.10** of [quarteroni2000numerical], item (2), Hessenberg matrices. Let
$A \in \mathbb{R}^{n \times n}$ be upper Hessenberg, and let $P$ be the permutation matrix of
GEM with partial pivoting. Then $\rho_n(PA) \le n$.

The proof uses `Matrix.growthFactor_le_card_of_isUpperHessenberg`.

**Reading.** The bound applies explicitly to upper Hessenberg matrices with partial pivoting on
exact stages.
-/
theorem growthFactor_hessenberg (hA : A.IsUpperHessenberg) :
    equation_3_66 ((gemPivotStage A partialPivotRow n).2.permMatrix ℝ * A) ≤ n :=
  growthFactor_le_card_of_isUpperHessenberg hA

/-- **Section 3.10** of [quarteroni2000numerical], item (3), symmetric positive definite matrices.
Let $A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, with $n \ge 1$. Then
$\rho_n = 1$: Gaussian elimination without pivoting never increases the largest entry.

The proof uses `Matrix.growthFactor_eq_one_of_posDef`.

**Reading.** Growth factor 1 is for exact stages in positive dimension.
-/
theorem growthFactor_posDef [NeZero n] (hA : A.PosDef) : equation_3_66 A = 1 :=
  growthFactor_eq_one_of_posDef hA (Nat.pos_of_ne_zero (NeZero.ne n))

/-- **Section 3.10** of [quarteroni2000numerical], item (4), matrices strictly diagonally dominant
by columns. Let $A \in \mathbb{R}^{n \times n}$ satisfy $\sum_{i \neq j} |a_{ij}| < |a_{jj}|$
for every column $j$. Then $\rho_n \le 2$ for Gaussian elimination without pivoting.

The bound holds more generally for every nonsingular matrix that is weakly diagonally dominant
by columns (`Matrix.growthFactor_le_two_of_isColDiagDominant`). Strict dominance gives both the
weak dominance and the nonsingularity.

**Reading.** The factor 2 bounds the exact-stage quotient.
-/
theorem growthFactor_colDiagDominant (hA : A.IsStrictColDiagDominant) : equation_3_66 A ≤ 2 :=
  growthFactor_le_two_of_isColDiagDominant hA.isUnit hA.isColDiagDominant

/-- **Section 3.10** of [quarteroni2000numerical], complete pivoting (Wilkinson). Let
$A \in \mathbb{R}^{n \times n}$, and let $P$ and $Q$ be the row and column permutation matrices
of Gaussian elimination with complete pivoting, for any complete pivoting strategy. Then
$$\rho_n(PAQ) \le n^{1/2} \big( 2 \cdot 3^{1/2} \cdot 4^{1/3} \cdots n^{1/(n-1)} \big)^{1/2}.$$
The source remarks that this growth is slower than $2^{n-1}$ as $n$ increases, so that complete
pivoting would seem to be mandatory.

The permutations are those that the complete pivoting recurrence `Matrix.gemFullPivotStage`
accumulates for a strategy `piv` with `Matrix.IsCompletePivot piv`; `Matrix.completePivotEntry`
is one such strategy. The elimination stages of $PAQ$ are the pivoted ones up to the order of
the rows and of the columns. The product is written as $\prod_{t=0}^{n-2} (t + 2)^{1/(t+1)}$.
The proof uses `Matrix.growthFactor_le_wilkinson_of_isCompletePivot`, which follows from
`Matrix.growthFactor_le_of_completePivoting` under the stage dominance
$|a^{(k)}_{ij}| \le |a^{(k)}_{kk}|$ that complete pivoting arranges.

**Reading.** Same numerical bound for exactly pivoted stages.
-/
theorem growthFactor_completePivoting
    {piv : Matrix (Fin n) (Fin n) ℝ → Fin n → Fin n × Fin n} (hpiv : IsCompletePivot piv) :
    equation_3_66 ((gemFullPivotStage A piv n).2.1.permMatrix ℝ * A *
        ((gemFullPivotStage A piv n).2.2⁻¹).permMatrix ℝ) ≤
      Real.sqrt n * Real.sqrt (∏ t ∈ range (n - 1), ((t : ℝ) + 2) ^ ((t : ℝ) + 1)⁻¹) := by
  rw [equation_3_66, permMatrix_mul_mul_permMatrix]
  exact growthFactor_le_wilkinson_of_isCompletePivot A hpiv

end Growth

/-! ### Examples 3.7–3.8 and the role of the condition number -/

section Examples

open scoped Matrix.Norms.Operator

/-- For $B \in \mathbb{R}^{2 \times 2}$, if both absolute row sums of $B$ are at most $c$ and one of
them equals $c$, then $\|B\|_\infty = c$. -/
private theorem linfty_opNorm_fin_two_eq {B : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ}
    (h0 : |B 0 0| + |B 0 1| ≤ c) (h1 : |B 1 0| + |B 1 1| ≤ c)
    (hc : |B 0 0| + |B 0 1| = c ∨ |B 1 0| + |B 1 1| = c) : ‖B‖ = c := by
  have hc0 : 0 ≤ c := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans h0
  refine le_antisymm (linfty_opNorm_le_of_forall_sum_le hc0 fun i => ?_) ?_
  · fin_cases i
    · simpa [Fin.sum_univ_two] using h0
    · simpa [Fin.sum_univ_two] using h1
  · rcases hc with hc | hc
    · rw [← hc]
      simpa [Fin.sum_univ_two] using sum_abs_apply_le_linfty_opNorm B 0
    · rw [← hc]
      simpa [Fin.sum_univ_two] using sum_abs_apply_le_linfty_opNorm B 1

/-- **Example 3.7** of [quarteroni2000numerical], equation (3.68), the conditioning. Let
$\varepsilon > 0$, and let
$$A = \begin{bmatrix} \varepsilon & 1 \\ 1 & 0 \end{bmatrix}, \qquad b = \begin{bmatrix} 1 +
  \varepsilon \\ 1 \end{bmatrix}.$$
Then the system $Ax = b$ has the exact solution $x = (1, 1)^T$, and $A$ is well conditioned:
$$A^{-1} = \begin{bmatrix} 0 & 1 \\ 1 & -\varepsilon \end{bmatrix}, \qquad \|A\|_\infty =
  \|A^{-1}\|_\infty = 1 + \varepsilon, \qquad K_\infty(A) = (1 + \varepsilon)^2.$$

The norm $\|\cdot\|_\infty$ is `Matrix.lpOpNorm ⊤`.

**Reading.** The text writes $(1+\varepsilon)^2$ after allowing any real $\varepsilon$ for
the exact solution. The condition number for arbitrary real $\varepsilon$ is
$(1+|\varepsilon|)^2$. The displayed form is used here with positive $\varepsilon$. -/
theorem example_3_7_cond {ε : ℝ} (hε : 0 < ε) :
    !![ε, 1; 1, 0] *ᵥ ![1, 1] = ![1 + ε, 1] ∧ (!![ε, 1; 1, 0])⁻¹ = !![0, 1; 1, -ε] ∧
      lpOpNorm ⊤ !![ε, 1; 1, 0] = 1 + ε ∧ lpOpNorm ⊤ (!![ε, 1; 1, 0])⁻¹ = 1 + ε ∧
      condNumber ⊤ !![ε, 1; 1, 0] = (1 + ε) ^ 2 := by
  have hinv : (!![ε, 1; 1, 0])⁻¹ = !![0, 1; 1, -ε] := by
    refine inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hA : lpOpNorm ⊤ !![ε, 1; 1, 0] = 1 + ε := by
    rw [lpOpNorm_top]
    refine linfty_opNorm_fin_two_eq ?_ ?_ (Or.inl ?_)
    · simp [abs_of_pos hε, add_comm]
    · simp
      linarith
    · simp [abs_of_pos hε, add_comm]
  have hAinv : lpOpNorm ⊤ (!![ε, 1; 1, 0])⁻¹ = 1 + ε := by
    rw [hinv, lpOpNorm_top]
    refine linfty_opNorm_fin_two_eq ?_ ?_ (Or.inr ?_)
    · simp
      linarith
    · simp [abs_of_pos hε]
    · simp [abs_of_pos hε]
  refine ⟨?_, hinv, hA, hAinv, ?_⟩
  · ext i
    fin_cases i
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · simp [mulVec, dotProduct, Fin.sum_univ_two]
  · rw [condNumber, hA, hAinv, sq]

/-- **Example 3.7** of [quarteroni2000numerical], with Exercise 6, the factorizations. Let
$\varepsilon \neq 0$ and $A = \begin{bmatrix} \varepsilon & 1 \\ 1 & 0 \end{bmatrix}$. The LU
factorization of $A$ without pivoting is
$$L = \begin{bmatrix} 1 & 0 \\ 1/\varepsilon & 1 \end{bmatrix}, \qquad U = \begin{bmatrix}
  \varepsilon & 1 \\ 0 & -1/\varepsilon \end{bmatrix},$$
and it is unique; its entries $l_{21}$ and $u_{22}$ have modulus $1/|\varepsilon|$, which is
large for small $\varepsilon$. With the row exchange $P = \begin{bmatrix} 0 & 1 \\ 1 & 0
\end{bmatrix}$ of partial pivoting,
$$PA = \begin{bmatrix} 1 & 0 \\ \varepsilon & 1 \end{bmatrix} = L' U', \qquad L' =
  \begin{bmatrix} 1 & 0 \\ \varepsilon & 1 \end{bmatrix}, \quad U' = I,$$
and if $|\varepsilon| \le 1$, the entries of $L'$ have modulus at most $1$.

For $|\varepsilon| \le 1$ the second row is the pivot row of partial pivoting. The uniqueness
follows from Theorem 3.4. -/
theorem example_3_7_lu {ε : ℝ} (hε : ε ≠ 0) :
    IsLU !![ε, 1; 1, 0] !![1, 0; ε⁻¹, 1] !![ε, 1; 0, -ε⁻¹] ∧
      (∀ L U, IsLU !![ε, 1; 1, 0] L U → L = !![1, 0; ε⁻¹, 1] ∧ U = !![ε, 1; 0, -ε⁻¹]) ∧
      IsLU (!![(0 : ℝ), 1; 1, 0] * !![ε, 1; 1, 0]) !![1, 0; ε, 1] 1 ∧
      (|ε| ≤ 1 → ∀ i j, |(!![1, 0; ε, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1) := by
  have hprod : !![ε, 1; 1, 0] = !![1, 0; ε⁻¹, 1] * !![ε, 1; 0, -ε⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hε]
  have hLU : IsLU !![ε, 1; 1, 0] !![1, 0; ε⁻¹, 1] !![ε, 1; 0, -ε⁻¹] := by
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, hprod.symm⟩
    · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> simp
    · fin_cases i <;> fin_cases j <;> simp_all
  have hstrict :
      ∀ k, IsUnit ((!![ε, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).strictLeadingPrincipalSubmatrix k) :=
    (gemStage_pivots_ne_zero_iff _).1 fun k hk hk1 => by
      interval_cases k
      · simpa using hε
      · exact absurd hk1 (by norm_num)
  have hPA : !![(0 : ℝ), 1; 1, 0] * !![ε, 1; 1, 0] = !![1, 0; ε, 1] * 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hLU, fun L U h => h.unique hLU hstrict, ?_, fun hε1 i j => ?_⟩
  · rw [hPA]
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, rfl⟩
    · have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> simp
    · exact one_apply_ne hij.ne'
  · fin_cases i <;> fin_cases j <;> simp [hε1]

/-- **Section 3.10** of [quarteroni2000numerical], the residual and the error. Let
$1 \le p \le \infty$, let $A \in \mathbb{R}^{n \times n}$ be nonsingular, let $Ax = b$ with
$b \neq 0$, and let $\hat x \in \mathbb{R}^n$ be any vector, with residual
$\hat r = b - A\hat x$. Then
$$\frac{\|x - \hat x\|_p}{\|x\|_p} \le \frac{K_p(A) \|\hat r\|_p}{\|A\|_p \|x\|_p} \le
  \frac{K_p(A) \|\hat r\|_p}{\|b\|_p}.$$
So a small residual does not guarantee a small error when $K_p(A) \gg 1$ (Example 3.8).

This is the bound (3.11) with $\delta b$ regarded as the residual of the computed solution. The
norms of vectors are those of `WithLp p (Fin n → ℝ)`, and $\|A\|_p$ and $K_p(A)$ are
`Matrix.lpOpNorm p A` and `QuarteroniSaccoSaleri.Chapter03.condNumber p A`. -/
theorem residual_error_bound (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : Matrix (Fin n) (Fin n) ℝ}
    {b x : Fin n → ℝ} (hA : IsUnit A) (hx : A *ᵥ x = b) (hb : b ≠ 0) (xhat : Fin n → ℝ) :
    ‖WithLp.toLp p (x - xhat)‖ / ‖WithLp.toLp p x‖ ≤
        condNumber p A * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ / (lpOpNorm p A * ‖WithLp.toLp p x‖) ∧
      condNumber p A * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ / (lpOpNorm p A * ‖WithLp.toLp p x‖) ≤
        condNumber p A * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ / ‖WithLp.toLp p b‖ := by
  have hne : NeZero n := ⟨fun h => hb (by subst h; exact Subsingleton.elim _ _)⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hb (by rw [← hx, mulVec_zero])
  have hxn : 0 < ‖WithLp.toLp p x‖ := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  have hbn : 0 < ‖WithLp.toLp p b‖ := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  have hK0 : 0 ≤ condNumber p A := mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _)
  have hApos : 0 < lpOpNorm p A := by
    have h1 := one_le_condNumberLp p hA
    rw [condNumberLp] at h1
    refine (lpOpNorm_nonneg p A).lt_of_ne fun h => ?_
    rw [← h, zero_mul] at h1
    norm_num at h1
  have hr0 : 0 ≤ ‖WithLp.toLp p (b - A *ᵥ xhat)‖ := norm_nonneg _
  -- `x - x̂ = A⁻¹ (b - A x̂)`
  have herr : x - xhat = A⁻¹ *ᵥ (b - A *ᵥ xhat) := by
    rw [mulVec_sub, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).1 hA),
      one_mulVec, ← hx, mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).1 hA),
      one_mulVec]
  have h1 : ‖WithLp.toLp p (x - xhat)‖ ≤ lpOpNorm p A⁻¹ * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ := by
    rw [herr]
    exact (lpCLM p A⁻¹).le_opNorm (WithLp.toLp p (b - A *ᵥ xhat))
  -- `‖b‖ ≤ ‖A‖ ‖x‖`
  have h2 : ‖WithLp.toLp p b‖ ≤ lpOpNorm p A * ‖WithLp.toLp p x‖ := by
    rw [← hx]
    exact (lpCLM p A).le_opNorm (WithLp.toLp p x)
  constructor
  · rw [div_le_div_iff₀ hxn (mul_pos hApos hxn)]
    calc ‖WithLp.toLp p (x - xhat)‖ * (lpOpNorm p A * ‖WithLp.toLp p x‖)
        ≤ lpOpNorm p A⁻¹ * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ * (lpOpNorm p A * ‖WithLp.toLp p x‖) :=
          mul_le_mul_of_nonneg_right h1 (mul_pos hApos hxn).le
      _ = condNumber p A * ‖WithLp.toLp p (b - A *ᵥ xhat)‖ * ‖WithLp.toLp p x‖ := by
          rw [condNumber]; ring
  · exact div_le_div_of_nonneg_left (mul_nonneg hK0 hr0) hbn h2

/-- **Example 3.8** of [quarteroni2000numerical]. The matrix
$$A = \begin{bmatrix} 1 & 1.0001 \\ 1.0001 & 1 \end{bmatrix}$$
is ill conditioned, with $K_\infty(A) = 20001$. For $b = (1, 1)^T$, the vector
$\hat x = (-4.499775, 5.5002249)^T$ has the small residual $\|b - A\hat x\|_\infty \le 10^{-3}$,
although it is far from the exact solution $x = A^{-1}b$: $\|\hat x - x\|_\infty \ge 4$.

The condition number comes from $\|A\|_\infty = 2.0001$ and $\|A^{-1}\|_\infty = 10000$. The
exact solution has both components equal to $1/2.0001 \approx 0.499975$. -/
theorem example_3_8 :
    condNumber ⊤ !![(1 : ℝ), 1.0001; 1.0001, 1] = 20001 ∧
      ‖![(1 : ℝ), 1] - !![(1 : ℝ), 1.0001; 1.0001, 1] *ᵥ ![-4.499775, 5.5002249]‖ ≤ 1 / 1000 ∧
      4 ≤ ‖![(-4.499775 : ℝ), 5.5002249] - (!![(1 : ℝ), 1.0001; 1.0001, 1])⁻¹ *ᵥ ![1, 1]‖ := by
  have hinv : (!![(1 : ℝ), 1.0001; 1.0001, 1])⁻¹ =
      !![-(1 / 0.00020001), 1.0001 / 0.00020001; 1.0001 / 0.00020001, -(1 / 0.00020001)] := by
    refine inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩
  · rw [condNumber, hinv, lpOpNorm_top, lpOpNorm_top,
      linfty_opNorm_fin_two_eq (c := 2.0001) (by norm_num) (by norm_num) (Or.inl (by norm_num)),
      linfty_opNorm_fin_two_eq (c := 10000) (by norm_num) (by norm_num) (Or.inl (by norm_num))]
    norm_num
  · rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two, Real.norm_eq_abs, abs_le]
  · rw [hinv]
    refine le_trans ?_ (norm_le_pi_norm _ 0)
    norm_num [mulVec, dotProduct, Fin.sum_univ_two, Real.norm_eq_abs, le_abs]

/-- **Section 3.10** of [quarteroni2000numerical], the display before (3.69). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $Ax = b$ with $b \neq 0$, and let
$(A + \delta A)(x + \delta x) = b + \delta b$. Let $u \ge 0$ with
$\|\delta A\|_\infty \le u\|A\|_\infty$, $\|\delta b\|_\infty \le u\|b\|_\infty$ and
$uK_\infty(A) \le 1/2$. Then
$$\frac{\|\delta x\|_\infty}{\|x\|_\infty} \le \frac{2uK_\infty(A)}{1 - uK_\infty(A)} \le
  4uK_\infty(A).$$

This is (3.13) applied with $\gamma = u$, in the setting of Theorem 3.3 for the $\infty$-norm.
The estimate $\simeq uK_\infty(A)$ of (3.69) and the count of $t - m$ exact digits are
heuristics and are not formalized.

**Reading.** Formalizes the preceding perturbation bound with an explicit smallness threshold.
-/
theorem equation_3_69 {A δA : Matrix (Fin n) (Fin n) ℝ} {b δb x δx : Fin n → ℝ} (hA : IsUnit A)
    (hx : A *ᵥ x = b) (hb : b ≠ 0) (hδx : (A + δA) *ᵥ (x + δx) = b + δb) {u : ℝ} (hu : 0 ≤ u)
    (hδA : lpOpNorm ⊤ δA ≤ u * lpOpNorm ⊤ A) (hδb : ‖δb‖ ≤ u * ‖b‖)
    (hK : u * condNumber ⊤ A ≤ 1 / 2) :
    ‖δx‖ / ‖x‖ ≤ 2 * u * condNumber ⊤ A / (1 - u * condNumber ⊤ A) ∧
      2 * u * condNumber ⊤ A / (1 - u * condNumber ⊤ A) ≤ 4 * u * condNumber ⊤ A := by
  have hK0 : 0 ≤ u * condNumber ⊤ A :=
    mul_nonneg hu (mul_nonneg (lpOpNorm_nonneg _ _) (lpOpNorm_nonneg _ _))
  have h := theorem_3_3 (p := ⊤) hA hx hb hδx hδA (by rwa [PiLp.norm_toLp, PiLp.norm_toLp])
    (by linarith)
  rw [PiLp.norm_toLp, PiLp.norm_toLp] at h
  refine ⟨h.trans (le_of_eq (by ring)), ?_⟩
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end Examples

end QuarteroniSaccoSaleri.Chapter03
