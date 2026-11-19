/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Int.Log
import Numlib.Analysis.Matrix.Function.Exp
import Numlib.Analysis.Matrix.Function.Pade
import Numlib.Analysis.Matrix.Function.Sign
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.Schur
import NumlibSurface.GolubVanLoan.Chapter01.Section02
import NumlibSurface.GolubVanLoan.Chapter03.Section04
import NumlibSurface.GolubVanLoan.Chapter07.Section09
import NumlibSurface.GolubVanLoan.Chapter09.Section02

/-!
# Golub and Van Loan, Section 9.3: The matrix exponential

This module formalizes §9.3 of [golub2013matrix], the computation and the sensitivity of the matrix
exponential $e^{At}$. For the Padé method it states the Padé approximants
$R_{pq}(z) = D_{pq}(z)^{-1} N_{pq}(z)$ of $e^z$, the remainder formula (9.3.1), the Moler–Van Loan
backward error bound of scaling and squaring, and the even and odd splitting of $N_{qq}$ and
$D_{qq}$. It defines Algorithm 9.3.1 (scaling and squaring) and proves its exact semantics. The
backward error claim of the algorithm holds only under an extra hypothesis, so the module also
defines a corrected variant whose claim holds for every $A$. For the perturbation theory it proves
that $e^{At}$ is the unique solution of $\dot X = AX$, $X(0) = I$, the variation-of-constants
identity for $e^{(A+E)t} - e^{At}$, the bound (9.3.2) with the spectral abscissa (9.3.3), the
relative perturbation bound, the properties of Van Loan's condition number $\nu(A, t)$, the identity
(9.3.4) for normal matrices, the $2 \times 2$ example (9.3.5), the pseudospectral lower bound
(9.3.6), and the normal case of §9.3.4.

The proofs specialize the backbone modules `Numlib.Analysis.Matrix.Function.Pade` and
`Numlib.Analysis.Matrix.Function.Exp` (Padé approximants and their error bounds),
`Numlib.Analysis.Normed.Algebra.Exponential` (the perturbation identity, uniqueness for the
differential equation, the condition number and the Laplace-transform bound on the resolvent),
`Numlib.Analysis.Normed.Algebra.SpectralRadius` (the spectral abscissa) and
`Numlib.LinearAlgebra.Matrix.Schur` (normal matrices have a diagonal Schur form). Algorithm 9.3.1
calls Algorithm 1.1.5 of Chapter 1 and the solve after Gaussian elimination with partial pivoting of
Chapter 3, and (9.3.6) uses the pseudospectra of Chapter 7.

## Main definitions

* Algorithm 9.3.1, `GolubVanLoan.Chapter09.updateEntriesM`: the entrywise overwrite of a matrix used
  by Algorithm 9.3.1.
* Algorithm 9.3.1, `GolubVanLoan.Chapter09.scalingSquaring`: scaling and squaring with the exponent
  $j = \max\{0, o + \lfloor \log_2 \|A\|_\infty \rfloor\}$ for an offset $o$.
* Algorithm 9.3.1, `GolubVanLoan.Chapter09.algorithm_9_3_1`: scaling and squaring as printed, with
  offset $1$.
* Algorithm 9.3.1, `GolubVanLoan.Chapter09.algorithm_9_3_1_corrected`: scaling and squaring with the
  corrected offset $2$.

## Main results

* §9.3.1, `GolubVanLoan.Chapter09.pade_def`: the coefficients of $N_{pq}$ and $D_{pq}$, and $R_{p0}$
  is the Taylor polynomial of degree $p$.
* Equation (9.3.1), `GolubVanLoan.Chapter09.equation_9_3_1`: the remainder $e^A - R_{pq}(A)$ as an
  integral.
* §9.3.1, `GolubVanLoan.Chapter09.moler_van_loan`: if $\|A\|_\infty / 2^j \le 1/2$, then
  $R_{pq}(A/2^j)^{2^j} = e^{A+E}$ with $\|E\|_\infty \le \epsilon(p, q) \|A\|_\infty$.
* §9.3.1, `GolubVanLoan.Chapter09.pade_even_odd`: $N_{qq}(A) = U + AV$ and $D_{qq}(A) = U - AV$ with
  $U$, $V$ polynomials in $A^2$.
* Algorithm 9.3.1, `GolubVanLoan.Chapter09.scalingSquaring_spec` and
  `GolubVanLoan.Chapter09.algorithm_9_3_1_spec`: in exact arithmetic the algorithm returns
  $R_{qq}(A/2^j)^{2^j}$.
* Algorithm 9.3.1, `GolubVanLoan.Chapter09.scalingSquaring_spec_backward` and
  `GolubVanLoan.Chapter09.algorithm_9_3_1_spec_backward`: if $\|A\|_\infty / 2^j \le 1/2$, the
  output is $e^{A+E}$ with $\|E\|_\infty \le \delta \|A\|_\infty$.
* Algorithm 9.3.1, `GolubVanLoan.Chapter09.algorithm_9_3_1_corrected_spec_backward`: with the
  corrected exponent the output is always $e^{A+E}$ with $\|E\|_\infty \le \delta \|A\|_\infty$.
* §9.3.2, `GolubVanLoan.Chapter09.exp_unique_ode`: $e^{At}$ is the unique solution of
  $\dot X(t) = A X(t)$, $X(0) = I$.
* §9.3.2, `GolubVanLoan.Chapter09.exp_perturbation_integral`: $e^{(A+E)t} - e^{At} = \int_0^t
  e^{A(t-s)} E e^{(A+E)s} \, ds$ and the resulting relative bound.
* Equation (9.3.3), `GolubVanLoan.Chapter09.equation_9_3_3`: the spectral abscissa $\alpha(A)$ is
  the largest real part of an eigenvalue.
* Equation (9.3.2), `GolubVanLoan.Chapter09.equation_9_3_2`:
  $\|e^{At}\|_2 \le e^{\alpha(A) t} M_S(t)$.
* §9.3.2, `GolubVanLoan.Chapter09.exp_perturbation_schur`: the relative perturbation bound
  $t \|E\|_2 M_S(t)^2 \exp(t M_S(t) \|E\|_2)$.
* §9.3.2, `GolubVanLoan.Chapter09.schurDeparture_eq_one_iff`: $M_S(t) = 1$ for all $t > 0$ if and
  only if $A$ is normal.
* §9.3.2, `GolubVanLoan.Chapter09.expCondNumber_ge`: $\nu(A, t) \ge t \|A\|_2$.
* Equation (9.3.4), `GolubVanLoan.Chapter09.equation_9_3_4`: $\|e^{At}\|_2 = e^{\alpha(A) t}$ for
  normal $A$.
* §9.3.2, `GolubVanLoan.Chapter09.expCondNumber_eq_of_isStarNormal`: $\nu(A, t) = t \|A\|_2$ for
  normal $A$.
* Equation (9.3.5), `GolubVanLoan.Chapter09.equation_9_3_5`: the exponential of $\begin{bmatrix} -1
  & 1000 \\ 0 & -1 \end{bmatrix} t$.
* §9.3.2, `GolubVanLoan.Chapter09.expCondNumber_eq_iff_counterexample`: a matrix that is not normal
  and has $\nu(A, t) = t \|A\|_2$ for all $t \ge 0$.
* Equation (9.3.6), `GolubVanLoan.Chapter09.equation_9_3_6`: $\sup_{t > 0} \|e^{At}\|_2 \ge
  \alpha_\epsilon(A) / \epsilon$.
* §9.3.4, `GolubVanLoan.Chapter09.normal_squaring`: for normal $A$, $G = R_{qq}(A/2^j)$ is normal
  and $\|G^m\|_2 = \|G\|_2^m$.

## Conventions

* The exponential $e^{At}$ is Mathlib's `NormedSpace.exp (t • A)`, which needs no norm on matrices.
* The matrix $A$ is real, `Matrix (Fin n) (Fin n) ℝ`, where the source is real (§9.3.1 and the start
  of §9.3.2). It is complex where the source uses the Schur decomposition
  $Q^H A Q = \operatorname{diag}(\lambda_i) + N$, with `Q ∈ Matrix.unitaryGroup` and `star Q` for
  $Q^H$.
* The norm $\|\cdot\|_\infty$ of §9.3.1 is the operator norm of the scope `Matrix.Norms.Operator`,
  and the norm $\|\cdot\|_2$ of §9.3.2–§9.3.4 is the operator norm of the scope
  `Matrix.Norms.L2Operator`. Integrals of matrix-valued functions are taken in whichever of these
  norms is open; all norms give the same integral.
* The Padé polynomials $N_{pq}$ and $D_{pq}$ and the approximant $R_{pq}(A)$ are
  `Pade.expNum ℝ p q`, `Pade.expDen ℝ p q` and `Pade.expApprox ℝ p q A`. The Moler–Van Loan
  constant `Pade.errorBound p q` is $\epsilon(p, q)$.
* The spectral abscissa $\alpha(A)$ is `spectralAbscissa A`.
* Van Loan's condition number $\nu(A, t)$ is `NormedSpace.expCondNumber A t`: the operator norm of
  the Fréchet derivative $E \mapsto \int_0^t e^{A(t-s)} E e^{As} \, ds$, times
  $\|A\|_2 / \|e^{At}\|_2$. The operator norm is the source's $\max_{\|E\|_2 \le 1}$.

## Implementation notes

* Algorithm 9.3.1 follows the algorithm conventions of `NumlibSurface.GolubVanLoan`. Its products
  $X = AX$ and $F = F^2$ are Algorithm 1.1.5 of Chapter 1 from $C = 0$, and the solve $DF = N$ is
  Gaussian elimination with partial pivoting of Chapter 3,
  `GolubVanLoan.Chapter03.solveMultipleRHS`, as in (3.4.12).
* The printed algorithm and the corrected one are both instances of
  `GolubVanLoan.Chapter09.scalingSquaring`, which takes the offset $o$ of the exponent as a
  parameter.
* The pseudospectral abscissa of (9.3.6) is `GolubVanLoan.Chapter07.pseudospectralAbscissa`, (7.9.8)
  of Chapter 7.

## Deviations from the source

* **§9.3.1, even and odd evaluation** (generalization). `GolubVanLoan.Chapter09.pade_even_odd`
  proves the split for every diagonal Padé order. The source gives the example $q=8$.
* **§9.3.1, the Padé fraction and Equation (9.3.1)** (reading).
  `GolubVanLoan.Chapter09.pade_def` uses a total inverse when the denominator is singular, and
  `GolubVanLoan.Chapter09.equation_9_3_1` makes the invertibility needed for the remainder
  formula explicit.
* **§9.3.2–§9.3.3, time domain** (reading). `GolubVanLoan.Chapter09.exp_perturbation_integral`,
  `GolubVanLoan.Chapter09.exp_perturbation_schur`, and `GolubVanLoan.Chapter09.equation_9_3_4`
  make the nonnegative time restriction on the norm results explicit.
* **Equation (9.3.6)** (reading). `GolubVanLoan.Chapter09.equation_9_3_6` gives a lower bound on
  every real uniform upper bound, expressing the source’s supremum bound without requiring a
  finite supremum.
* **§9.3.4, normal squaring** (reading). `GolubVanLoan.Chapter09.normal_squaring` includes the
  zeroth power and uses totalized Padé evaluation.
* **Algorithm 9.3.1** (correction). The printed exponent $j = \max\{0, 1 + \lfloor \log_2
  \|A\|_\infty \rfloor\}$ only guarantees $\|A/2^j\|_\infty < 1$, not the bound
  $\|A/2^j\|_\infty \le 1/2$ that the Moler–Van Loan bound needs. The library proves the claim of
  the printed algorithm under this extra hypothesis, and proves it for every $A$ with the exponent
  $\max\{0, 2 + \lfloor \log_2 \|A\|_\infty \rfloor\}$. See
  `GolubVanLoan.Chapter09.algorithm_9_3_1_spec_backward` and
  `GolubVanLoan.Chapter09.algorithm_9_3_1_corrected_spec_backward`.
* **Equation (9.3.2)** (typo). The source prints $e^{\alpha(A) t M_S(t)}$ for
  $e^{\alpha(A) t} M_S(t)$. See `GolubVanLoan.Chapter09.equation_9_3_2`.
* **§9.3.2, the equality case of $\nu(A, t) \ge t \|A\|_2$** (correction). The source states
  equality for all $t \ge 0$ if and only if $A$ is normal. The "only if" direction is false. The
  library proves the "if" direction. See `GolubVanLoan.Chapter09.expCondNumber_eq_of_isStarNormal`
  and `GolubVanLoan.Chapter09.expCondNumber_eq_iff_counterexample`.
* **Equation (9.3.6)** (typo). The source cites "(7.8.8)" for the pseudospectral abscissa, which is
  (7.9.8). See `GolubVanLoan.Chapter09.equation_9_3_6`.

## Not formalized

* The flop counts.
* Figure 9.3.1 and the estimate $\alpha_{.01}(A)/.01 \approx 216$.
* The heuristic claim of §9.3.2 about a matrix $E$ for which an approximate equality holds.
* The heuristic claims of §9.3.4: the rounding estimate $\gamma$ and what "numerical experiments
  suggest".
-/

open Polynomial Finset NormedSpace
open scoped Nat

namespace GolubVanLoan.Chapter09

variable {n : ℕ}

/-! ### §9.3.1 A Padé approximation method -/

/-- **§9.3.1** of [golub2013matrix], definition of the Padé functions. The $(p, q)$ Padé approximant
of $e^z$ is $R_{pq}(z) = D_{pq}(z)^{-1} N_{pq}(z)$ with
$$N_{pq}(z) = \sum_{k=0}^{p} \frac{(p+q-k)! \, p!}{(p+q)! \, k! \, (p-k)!} z^k, \qquad
  D_{pq}(z) = \sum_{k=0}^{q} \frac{(p+q-k)! \, q!}{(p+q)! \, k! \, (q-k)!} (-z)^k.$$
For every $A \in \mathbb{R}^{n \times n}$, $R_{pq}(A) = D_{pq}(A)^{-1} N_{pq}(A)$, and
$R_{p0}(A) = I + A + \dots + A^p/p!$ is the Taylor polynomial of degree $p$.

The statement gives the coefficients of `Pade.expNum ℝ p q` and `Pade.expDen ℝ p q`. The inverse
is the Lean inverse, which is $0$ for a singular $D_{pq}(A)$.

**Reading.** The source defines an ordinary rational matrix function wherever its denominator
is invertible. The Lean inverse is total and extends the formula by zero when $D_{pq}(A)$ is
singular. -/
theorem pade_def (p q : ℕ) :
    (∀ k, (Pade.expNum ℝ p q).coeff k = if k ≤ p then
      (((p + q - k)! * p ! : ℕ) / ((p + q)! * k ! * (p - k)! : ℕ) : ℝ) else 0) ∧
    (∀ k, (Pade.expDen ℝ p q).coeff k = if k ≤ q then
      (-1) ^ k * (((p + q - k)! * q ! : ℕ) / ((p + q)! * k ! * (q - k)! : ℕ) : ℝ) else 0) ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, Pade.expApprox ℝ p q A =
      (aeval A (Pade.expDen ℝ p q))⁻¹ * aeval A (Pade.expNum ℝ p q)) ∧
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
      Pade.expApprox ℝ p 0 A = ∑ k ∈ range (p + 1), ((k ! : ℝ)⁻¹) • A ^ k := by
  refine ⟨Pade.coeff_expNum p q, Pade.coeff_expDen p q, fun A => ?_, fun A => ?_⟩
  · rw [Pade.expApprox, Matrix.nonsing_inv_eq_ringInverse]
  · rw [Pade.expApprox, Pade.expDen_zero_right, Pade.expNum_zero_right, map_one,
      Ring.inverse_one, one_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.smul_def]

section Infinity

open scoped Matrix.Norms.Operator

/-- **Equation (9.3.1)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and $p, q \ge 0$,
and suppose that $D_{pq}(A)$ is nonsingular. Then
$$e^A = R_{pq}(A) + \frac{(-1)^q}{(p+q)!} A^{p+q+1} D_{pq}(A)^{-1} \int_0^1 u^p (1 - u)^q
  e^{A(1-u)} \, du.$$

**Reading.** The source leaves the invertibility required by $D_{pq}(A)^{-1}$ implicit. The
Lean theorem assumes it. -/
theorem equation_9_3_1 (p q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hD : IsUnit (aeval A (Pade.expDen ℝ p q))) :
    exp A = Pade.expApprox ℝ p q A + ((-1) ^ q / (p + q)! : ℝ) • (A ^ (p + q + 1) *
      (aeval A (Pade.expDen ℝ p q))⁻¹ *
        ∫ u in (0 : ℝ)..1, (u ^ p * (1 - u) ^ q) • exp ((1 - u) • A)) := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact Pade.exp_eq_expApprox_add p q A hD

/-- **§9.3.1** of [golub2013matrix], the Moler–Van Loan bound quoted in the source. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, let $p, q, j \ge 0$, and suppose that
$\|A\|_\infty / 2^j \le 1/2$. Let $F_{pq} = R_{pq}(A/2^j)^{2^j}$ and
$$\epsilon(p, q) = 2^{3-(p+q)} \frac{p! \, q!}{(p+q)! \, (p+q+1)!}.$$
Then $F_{pq} = e^{A+E}$ for some $E$ with $AE = EA$ and
$\|E\|_\infty \le \epsilon(p, q) \|A\|_\infty$, and consequently
$$\frac{\|e^A - F_{pq}\|_\infty}{\|e^A\|_\infty} \le \epsilon(p, q) \|A\|_\infty e^{\epsilon(p,
  q) \|A\|_\infty}.$$
-/
theorem moler_van_loan [NeZero n] (p q j : ℕ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ‖A‖ / 2 ^ j ≤ 1 / 2) :
    (∃ E : Matrix (Fin n) (Fin n) ℝ,
      Pade.expApprox ℝ p q ((2⁻¹ : ℝ) ^ j • A) ^ 2 ^ j = exp (A + E) ∧ A * E = E * A ∧
        ‖E‖ ≤ Pade.errorBound p q * ‖A‖) ∧
    ‖exp A - Pade.expApprox ℝ p q ((2⁻¹ : ℝ) ^ j • A) ^ 2 ^ j‖ / ‖exp A‖ ≤
      Pade.errorBound p q * ‖A‖ * Real.exp (Pade.errorBound p q * ‖A‖) := by
  have hA' : ‖A‖ ≤ 2 ^ j / 2 := by
    rw [div_le_iff₀ (by positivity)] at hA
    linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨E, hc, hE, h⟩ := Pade.exists_exp_add_eq_expApprox_pow p q j hA'
    exact ⟨E, h, hc.eq, hE⟩
  · have hpos : 0 < ‖exp A‖ := norm_pos_iff.mpr (Matrix.isUnit_exp A).ne_zero
    rw [div_le_iff₀ hpos]
    exact Pade.norm_exp_sub_expApprox_pow_le p q j hA'

end Infinity

/-- A sum over $k < 2m$ splits into the sum of its even terms and the sum of its odd terms. -/
private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ k ∈ range m, f (2 * k) + ∑ k ∈ range m, f (2 * k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    abel

/-- **§9.3.1** of [golub2013matrix], the even and odd evaluation of the diagonal approximants. Let
$A \in \mathbb{R}^{n \times n}$, let $c_k$ be the coefficients of $N_{qq}$, and let
$$U = \sum_{k=0}^{q} c_{2k} A^{2k}, \qquad V = \sum_{k=0}^{q} c_{2k+1} A^{2k}.$$
Then $N_{qq}(A) = U + AV$ and $D_{qq}(A) = U - AV$.

For $q = 8$ the source writes $U$ and $V$ explicitly and evaluates them by Horner's scheme in
$A^2$. The coefficients $c_k$ vanish for $k > q$.

**Generalization.** The sums describe the even and odd parts for arbitrary diagonal Padé order.
The source illustrates the splitting at order eight, with an evaluation scheme using powers of
$A^2$. -/
theorem pade_even_odd (q : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    let c := fun k => (Pade.expNum ℝ q q).coeff k
    let U := ∑ k ∈ range (q + 1), c (2 * k) • A ^ (2 * k)
    let V := ∑ k ∈ range (q + 1), c (2 * k + 1) • A ^ (2 * k)
    aeval A (Pade.expNum ℝ q q) = U + A * V ∧ aeval A (Pade.expDen ℝ q q) = U - A * V := by
  intro c U V
  have hden : ∀ k, (Pade.expDen ℝ q q).coeff k = (-1) ^ k * c k := fun k => by
    simp only [c, Pade.coeff_expDen, Pade.coeff_expNum]
    split_ifs <;> simp
  have hdeg : ∀ P : ℝ[X], (∀ k, q < k → P.coeff k = 0) → P.natDegree < 2 * (q + 1) :=
    fun P hP => lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun k hk => hP k
      (by exact_mod_cast hk)) (by omega)
  have hNz : ∀ k, q < k → (Pade.expNum ℝ q q).coeff k = 0 := fun k hk => by
    rw [Pade.coeff_expNum, ite_eq_right (by omega)]
  have hDz : ∀ k, q < k → (Pade.expDen ℝ q q).coeff k = 0 := fun k hk => by
    rw [Pade.coeff_expDen, ite_eq_right (by omega)]
  have hodd : ∀ (d : ℝ) (k : ℕ), d • A ^ (2 * k + 1) = A * (d • A ^ (2 * k)) := fun d k => by
    rw [mul_smul_comm, ← pow_succ']
  constructor
  · rw [aeval_eq_sum_range' (hdeg _ hNz), sum_range_two_mul]
    simp only [U, V, c, Finset.mul_sum, hodd]
  · rw [aeval_eq_sum_range' (hdeg _ hDz), sum_range_two_mul, sub_eq_add_neg, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hden, pow_mul (-1 : ℝ) 2 k, neg_one_sq, one_pow, one_mul]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hden, pow_succ (-1 : ℝ) (2 * k), pow_mul (-1 : ℝ) 2 k, neg_one_sq, one_pow, one_mul,
        neg_one_mul, neg_smul, hodd]

/-! ### Algorithm 9.3.1: scaling and squaring -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 9.3.1** of [golub2013matrix], the entrywise updates. The matrix $C$ is overwritten
entry by entry, $c_{il} \leftarrow g(i, l, c_{il})$, row by row and from left to right. This is
the form of the updates $A = A/2^j$, $N = N + cX$ and $D = D + (-1)^k cX$ of Algorithm 9.3.1. -/
def updateEntriesM (g : Fin n → Fin n → ℝ → M ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun C i => do
    let r ← (List.finRange n).foldlM (fun (r : Fin n → ℝ) l => do
      let b ← g i l (r l)
      pure (Function.update r l b)) (C i)
    pure (C.updateRow i r)) C

/-- **Algorithm 9.3.1** of [golub2013matrix], with an offset $o$ in the exponent. This is the
program of Algorithm 9.3.1 with the scaling exponent $j = \max\{0, o + \lfloor \log_2
\|A\|_\infty \rfloor\}$ in place of the printed $j = \max\{0, 1 + \lfloor \log_2 \|A\|_\infty
\rfloor\}$.

The source prints $o = 1$, which is `GolubVanLoan.Chapter09.algorithm_9_3_1`. The corrected
choice $o = 2$, for which the claimed backward error holds, is
`GolubVanLoan.Chapter09.algorithm_9_3_1_corrected`.

**Reading.** Parameterizes the exponent offset and explicitly selects elimination with partial
pivoting.
-/
noncomputable def scalingSquaring (o : ℤ) (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) := do
  let s ← (List.finRange n).foldlM (fun (s : Fin n → ℝ) i => do
    let t ← (List.finRange n).foldlM (fun c l => rnd (c + |A i l|)) 0
    pure (Function.update s i t)) 0
  let j : ℕ := (o + Int.log 2 (⨆ i, s i)).toNat
  let B ← updateEntriesM (fun i l _ => rnd (A i l / 2 ^ j)) A
  let q : ℕ := sInf {q : ℕ | Pade.errorBound q q ≤ δ}
  let st ← (List.range q).foldlM (fun (st : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ×
      Matrix (Fin n) (Fin n) ℝ × ℝ) k₀ => do
    let t ← rnd (st.2.2.2 * ((q - (k₀ + 1) + 1 : ℕ) : ℝ))
    let c ← rnd (t / (((2 * q - (k₀ + 1) + 1) * (k₀ + 1) : ℕ) : ℝ))
    let X ← Chapter01.algorithm_1_1_5 rnd B st.2.2.1 0
    let N ← updateEntriesM (fun i l x => do let p ← rnd (c * X i l); rnd (x + p)) st.2.1
    let D ← updateEntriesM (fun i l x => do
      let p ← rnd ((-1) ^ (k₀ + 1) * c * X i l); rnd (x + p)) st.1
    pure (D, N, X, c)) (1, 1, 1, 1)
  let F ← Chapter03.solveMultipleRHS rnd st.1 st.2.1
  (List.range j).foldlM (fun F _ => Chapter01.algorithm_1_1_5 rnd F F 0) F

/-- **Algorithm 9.3.1** of [golub2013matrix] (scaling and squaring). "Given $\delta > 0$ and
$A \in \mathbb{R}^{n \times n}$, the following algorithm computes $F = e^{A+E}$ where
$\|E\|_\infty \le \delta \|A\|_\infty$":
```
j = max{0, 1 + floor(log₂(‖A‖_∞))}
A = A/2^j
Let q be the smallest nonnegative integer such that ε(q, q) ≤ δ
D = I, N = I, X = I, c = 1
for k = 1:q
    c = c · (q - k + 1)/((2q - k + 1) k)
    X = AX, N = N + c · X, D = D + (-1)^k c · X
end
Solve DF = N for F using Gaussian elimination
for k = 1:j
    F = F²
end
```
The program computes $\|A\|_\infty = \max_i \sum_l |a_{il}|$ with rounded additions; the
absolute values and the maximum are exact. The numbers $j$ and $q$ are exact discrete choices on
computed values, with $q$ the least integer such that $\epsilon(q, q) \le \delta$, and $q = 0$
if there is none. The integer factors of the update of $c$ are exact. The products $X = AX$ and
$F = F^2$ are Algorithm 1.1.5 of Chapter 1 from $C = 0$, and the solve is Gaussian elimination
with partial pivoting of Chapter 3 for the multiple right-hand side $N$,
`GolubVanLoan.Chapter03.solveMultipleRHS`.

The definition is `GolubVanLoan.Chapter09.scalingSquaring` with the printed offset $1$. Its
backward error claim needs $\|A\|_\infty / 2^j \le 1/2$, which this exponent does not guarantee;
see `GolubVanLoan.Chapter09.algorithm_9_3_1_spec_backward`. -/
noncomputable def algorithm_9_3_1 (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  scalingSquaring rnd 1 δ A

/-- **Algorithm 9.3.1** of [golub2013matrix], with the corrected scaling exponent $j = \max\{0, 2 +
\lfloor \log_2 \|A\|_\infty \rfloor\}$. This exponent guarantees $\|A\|_\infty / 2^j \le 1/2$.

**Correction.** The source prints $j = \max\{0, 1 + \lfloor \log_2 \|A\|_\infty \rfloor\}$,
which only guarantees $\|A\|_\infty / 2^j < 1$.

The definition is `GolubVanLoan.Chapter09.scalingSquaring` with offset $2$. -/
noncomputable def algorithm_9_3_1_corrected (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    M (Matrix (Fin n) (Fin n) ℝ) :=
  scalingSquaring rnd 2 δ A

end Programs

/-- In exact arithmetic, the entrywise update replaces each entry $c_{il}$ by $h(i, l, c_{il})$. -/
private theorem updateEntriesM_id (h : Fin n → Fin n → ℝ → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Id.run (updateEntriesM (M := Id) (fun i l x => pure (h i l x)) C) =
      Matrix.of fun i l => h i l (C i l) := by
  ext i l
  have h1 := Matrix.idRun_foldlM_updateRow_apply (fun i (row : Fin n → ℝ) =>
    (List.finRange n).foldlM (fun (r : Fin n → ℝ) l => do
      let b ← (pure (h i l (r l)) : Id ℝ)
      pure (Function.update r l b)) row) (List.finRange n) (List.nodup_finRange n) C i
  have h2 := List.idRun_foldlM_update_apply (fun l (x : ℝ) => (pure (h i l x) : Id ℝ))
    (List.finRange n) (List.nodup_finRange n) (C i) l
  rw [ite_eq_left (List.mem_finRange i)] at h1
  rw [ite_eq_left (List.mem_finRange l)] at h2
  simp only [updateEntriesM, Matrix.of_apply]
  rw [h1, h2]
  rfl

/-- The recurrence of the Padé coefficients used by Algorithm 9.3.1: for the coefficients $c_k$ of
$N_{qq}$ and $1 \le k \le q$, $c_k = c_{k-1} (q - k + 1) / ((2q - k + 1) k)$. -/
private theorem coeff_expNum_succ {q k : ℕ} (hk : k + 1 ≤ q) :
    (Pade.expNum ℝ q q).coeff (k + 1) = (Pade.expNum ℝ q q).coeff k *
      ((q - (k + 1) + 1 : ℕ) : ℝ) / (((2 * q - (k + 1) + 1) * (k + 1) : ℕ) : ℝ) := by
  obtain ⟨b, rfl⟩ : ∃ b, q = k + 1 + b := ⟨q - (k + 1), by omega⟩
  rw [Pade.coeff_expNum, Pade.coeff_expNum, ite_eq_left hk, ite_eq_left (by omega)]
  have e1 : k + 1 + b + (k + 1 + b) - (k + 1) = k + 1 + 2 * b := by omega
  have e2 : k + 1 + b + (k + 1 + b) - k = (k + 1 + 2 * b) + 1 := by omega
  have e3 : k + 1 + b - (k + 1) = b := by omega
  have e4 : k + 1 + b - k = b + 1 := by omega
  have e5 : 2 * (k + 1 + b) - (k + 1) + 1 = (k + 1 + 2 * b) + 1 := by omega
  rw [e1, e2, e3, e4, e5, Nat.factorial_succ (k + 1 + 2 * b), Nat.factorial_succ b,
    Nat.factorial_succ k]
  have h1 := Nat.factorial_pos (k + 1 + 2 * b)
  have h2 := Nat.factorial_pos b
  have h3 := Nat.factorial_pos k
  have h4 := Nat.factorial_pos (k + 1 + b + (k + 1 + b))
  push_cast
  field_simp

/-- In exact arithmetic, after $m \le q$ steps of the loop over $k$ in Algorithm 9.3.1,
$D = \sum_{k \le m} (-1)^k c_k B^k$, $N = \sum_{k \le m} c_k B^k$, $X = B^m$ and $c = c_m$. -/
private theorem padeLoop_id (B : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) :
    ∀ m ≤ q, Id.run ((List.range m).foldlM (fun (st : Matrix (Fin n) (Fin n) ℝ ×
        Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × ℝ) k₀ => do
      let t ← (pure (st.2.2.2 * ((q - (k₀ + 1) + 1 : ℕ) : ℝ)) : Id ℝ)
      let c ← (pure (t / (((2 * q - (k₀ + 1) + 1) * (k₀ + 1) : ℕ) : ℝ)) : Id ℝ)
      let X ← Chapter01.algorithm_1_1_5 pure B st.2.2.1 0
      let N ← updateEntriesM (M := Id) (fun i l x => do
        let p ← (pure (c * X i l) : Id ℝ); pure (x + p)) st.2.1
      let D ← updateEntriesM (M := Id) (fun i l x => do
        let p ← (pure ((-1) ^ (k₀ + 1) * c * X i l) : Id ℝ); pure (x + p)) st.1
      pure (D, N, X, c)) (1, 1, 1, 1)) =
      (∑ k ∈ range (m + 1), ((-1) ^ k * (Pade.expNum ℝ q q).coeff k) • B ^ k,
        ∑ k ∈ range (m + 1), (Pade.expNum ℝ q q).coeff k • B ^ k, B ^ m,
        (Pade.expNum ℝ q q).coeff m) := by
  intro m hm
  rw [List.idRun_foldlM]
  induction m with
  | zero =>
    have h0 : (Pade.expNum ℝ q q).coeff 0 = 1 := by
      rw [Pade.coeff_expNum, ite_eq_left (Nat.zero_le q)]
      simp only [Nat.sub_zero, Nat.factorial_zero, mul_one]
      exact div_self (by positivity)
    simp [h0]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
    simp only [pure_bind, Id.run_pure, Id.run_bind]
    rw [Chapter01.algorithm_1_1_5_spec, zero_add, updateEntriesM_id, updateEntriesM_id,
      ← coeff_expNum_succ hm, pow_succ' B m]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · ext i l
      simp only [Finset.sum_range_succ, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
        pow_succ', Matrix.of_apply]
    · ext i l
      simp only [Finset.sum_range_succ, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
        pow_succ', Matrix.of_apply]

/-- In exact arithmetic, the squaring loop $F \leftarrow F^2$, run $j$ times, returns $F^{2^j}$. -/
private theorem squaring_id (F : Matrix (Fin n) (Fin n) ℝ) (j : ℕ) :
    Id.run ((List.range j).foldlM (fun F _ => Chapter01.algorithm_1_1_5 pure F F 0) F) =
      F ^ 2 ^ j := by
  rw [List.idRun_foldlM]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Chapter01.algorithm_1_1_5_spec, zero_add, pow_succ, pow_mul, sq]

/-- The Padé polynomials $N_{qq}$ and $D_{qq}$ at a matrix $B$ are the sums that the loop of
Algorithm 9.3.1 accumulates: $N_{qq}(B) = \sum_{k \le q} c_k B^k$ and
$D_{qq}(B) = \sum_{k \le q} (-1)^k c_k B^k$. -/
private theorem aeval_padeNum_denom (B : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) :
    aeval B (Pade.expNum ℝ q q) = ∑ k ∈ range (q + 1), (Pade.expNum ℝ q q).coeff k • B ^ k ∧
      aeval B (Pade.expDen ℝ q q) =
        ∑ k ∈ range (q + 1), ((-1) ^ k * (Pade.expNum ℝ q q).coeff k) • B ^ k := by
  have hdeg : ∀ P : ℝ[X], (∀ k, q < k → P.coeff k = 0) → P.natDegree < q + 1 :=
    fun P hP => Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun k hk => hP k
      (by exact_mod_cast hk))
  have hN := hdeg (Pade.expNum ℝ q q) fun k hk => by
    rw [Pade.coeff_expNum, ite_eq_right (by omega)]
  have hD := hdeg (Pade.expDen ℝ q q) fun k hk => by
    rw [Pade.coeff_expDen, ite_eq_right (by omega)]
  refine ⟨aeval_eq_sum_range' hN B, ?_⟩
  rw [aeval_eq_sum_range' hD B]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Pade.coeff_expDen, Pade.coeff_expNum, ite_eq_left hkq, ite_eq_left hkq]

/-- **Algorithm 9.3.1** of [golub2013matrix], exact semantics with an offset $o$ in the exponent.
Let $A \in \mathbb{R}^{n \times n}$ and $\delta \in \mathbb{R}$. Let
$\nu = \max_i \sum_l |a_{il}| = \|A\|_\infty$, $j = \max\{0, o + \lfloor \log_2 \nu \rfloor\}$,
and let $q$ be the least integer with $\epsilon(q, q) \le \delta$, as the program computes them.
If $D_{qq}(A/2^j)$ is nonsingular, then in exact arithmetic
`GolubVanLoan.Chapter09.scalingSquaring` returns
$$R_{qq}(A/2^j)^{2^j}.$$

The loop computes $c_k = (2q-k)! \, q! / ((2q)! \, k! \, (q-k)!)$ by the recurrence
$c_k = c_{k-1} (q-k+1)/((2q-k+1)k)$, so $N = N_{qq}(A/2^j)$ and $D = D_{qq}(A/2^j)$ by
`GolubVanLoan.Chapter09.pade_def`. The solve returns $D^{-1} N$, as in (3.4.12) of Chapter 3,
and the squarings give the power $2^j$. The integer logarithm `Int.log 2` is $0$ at $\nu = 0$,
and $q = 0$ if no $q$ has $\epsilon(q, q) \le \delta$.

**Reading.** Exact-arithmetic Padé result for any exponent offset and invertible denominator.
-/
theorem scalingSquaring_spec (o : ℤ) (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) {j q : ℕ}
    (hj : j = (o + Int.log 2 (⨆ i, ∑ l, |A i l|)).toNat)
    (hq : q = sInf {q : ℕ | Pade.errorBound q q ≤ δ})
    (hD : IsUnit (aeval ((2⁻¹ : ℝ) ^ j • A) (Pade.expDen ℝ q q))) :
    Id.run (scalingSquaring pure o δ A) = Pade.expApprox ℝ q q ((2⁻¹ : ℝ) ^ j • A) ^ 2 ^ j := by
  have hs : Id.run ((List.finRange n).foldlM (fun (s : Fin n → ℝ) i => do
      let t ← (List.finRange n).foldlM (fun c l => (pure (c + |A i l|) : Id ℝ)) 0
      pure (Function.update s i t)) 0) = fun i => ∑ l, |A i l| := by
    funext i
    have h := List.idRun_foldlM_update_apply (fun i (_ : ℝ) =>
      (List.finRange n).foldlM (fun c l => (pure (c + |A i l|) : Id ℝ)) 0) (List.finRange n)
      (List.nodup_finRange n) 0 i
    rw [ite_eq_left (List.mem_finRange i)] at h
    rw [h, List.foldlM_pure, Id.run_pure, List.foldl_add_eq_add_sum_map, zero_add,
      ← Fin.sum_univ_def]
  set B : Matrix (Fin n) (Fin n) ℝ := (2⁻¹ : ℝ) ^ j • A with hBdef
  have hB : Id.run (updateEntriesM (M := Id) (fun i l _ => pure (A i l / 2 ^ j)) A) = B := by
    rw [updateEntriesM_id]
    ext i l
    simp [hBdef, div_eq_mul_inv, mul_comm]
  obtain ⟨hNum, hDen⟩ := aeval_padeNum_denom B q
  have hloop := padeLoop_id B q q le_rfl
  have hDd : IsUnit (aeval B (Pade.expDen ℝ q q)).det := (Matrix.isUnit_iff_isUnit_det _).1 hD
  have hsolve : Id.run (Chapter03.solveMultipleRHS pure (aeval B (Pade.expDen ℝ q q))
      (aeval B (Pade.expNum ℝ q q))) = Pade.expApprox ℝ q q B := by
    have h := (Chapter03.equation_3_4_12 hD (aeval B (Pade.expNum ℝ q q))).1
    set X := Id.run (Chapter03.solveMultipleRHS pure (aeval B (Pade.expDen ℝ q q))
      (aeval B (Pade.expNum ℝ q q))) with hX
    rw [(pade_def q q).2.2.1 B, ← h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDd,
      Matrix.one_mul]
  rw [scalingSquaring, Id.run_bind, hs]
  dsimp only
  rw [← hj, Id.run_bind, hB]
  rw [← hq, Id.run_bind, hloop]
  rw [← hNum, ← hDen, Id.run_bind, hsolve, squaring_id]

/-- **Algorithm 9.3.1** of [golub2013matrix], exact semantics. Let $A \in \mathbb{R}^{n \times n}$
and $\delta \in \mathbb{R}$. Let $\nu = \max_i \sum_l |a_{il}| = \|A\|_\infty$,
$j = \max\{0, 1 + \lfloor \log_2 \nu \rfloor\}$, and let $q$ be the least integer with
$\epsilon(q, q) \le \delta$, as the algorithm computes them. If $D_{qq}(A/2^j)$ is nonsingular,
then in exact arithmetic the algorithm returns
$$R_{qq}(A/2^j)^{2^j}.$$

For $A = 0$ the integer logarithm gives $j = 1$, which does not change the result. The proof
specializes `GolubVanLoan.Chapter09.scalingSquaring_spec`.

**Reading.** Isolates the exact-arithmetic Padé output with an explicit invertible denominator
hypothesis.
-/
theorem algorithm_9_3_1_spec (δ : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) {j q : ℕ}
    (hj : j = (1 + Int.log 2 (⨆ i, ∑ l, |A i l|)).toNat)
    (hq : q = sInf {q : ℕ | Pade.errorBound q q ≤ δ})
    (hD : IsUnit (aeval ((2⁻¹ : ℝ) ^ j • A) (Pade.expDen ℝ q q))) :
    Id.run (algorithm_9_3_1 pure δ A) = Pade.expApprox ℝ q q ((2⁻¹ : ℝ) ^ j • A) ^ 2 ^ j :=
  scalingSquaring_spec 1 δ A hj hq hD

section Infinity

open scoped Matrix.Norms.Operator

/-- **Algorithm 9.3.1** of [golub2013matrix], backward error with an offset $o$ in the exponent. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, and let $\delta$ be such that some $q$ has
$\epsilon(q, q) \le \delta$. Let $j$ and $q$ be as in
`GolubVanLoan.Chapter09.scalingSquaring_spec`, and suppose that $\|A\|_\infty / 2^j \le 1/2$.
Then in exact arithmetic `GolubVanLoan.Chapter09.scalingSquaring` returns $F = e^{A+E}$ for some
$E$ with $AE = EA$ and
$$\|E\|_\infty \le \delta \|A\|_\infty.$$

Under the hypothesis, $\|A/2^j\|_\infty < \log 2$, so $D_{qq}(A/2^j)$ is nonsingular
(`Pade.isUnit_aeval_expDen`). The Moler–Van Loan bound with $\epsilon(q, q) \le \delta$ then
gives the claim.

**Reading.** Arbitrary offset, exact rounded operations, explicit tolerance feasibility and
scaled-norm premise.
-/
theorem scalingSquaring_spec_backward [NeZero n] (o : ℤ) {δ : ℝ}
    (hδ : ∃ q, Pade.errorBound q q ≤ δ) (A : Matrix (Fin n) (Fin n) ℝ) {j q : ℕ}
    (hj : j = (o + Int.log 2 (⨆ i, ∑ l, |A i l|)).toNat)
    (hq : q = sInf {q : ℕ | Pade.errorBound q q ≤ δ}) (hA : ‖A‖ / 2 ^ j ≤ 1 / 2) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ,
      Id.run (scalingSquaring pure o δ A) = exp (A + E) ∧ A * E = E * A ∧ ‖E‖ ≤ δ * ‖A‖ := by
  have hsmall : ‖(2⁻¹ : ℝ) ^ j • A‖ < Real.log 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_pow, ← div_eq_inv_mul]
    linarith [Real.log_two_gt_d9]
  have hD := (Pade.isUnit_aeval_expDen (𝕂 := ℝ) q q hsmall).1
  obtain ⟨⟨E, hE, hc, hEn⟩, -⟩ := moler_van_loan q q j hA
  have hqδ : Pade.errorBound q q ≤ δ :=
    hq ▸ Nat.sInf_mem (s := {q | Pade.errorBound q q ≤ δ}) hδ
  refine ⟨E, (scalingSquaring_spec o δ A hj hq hD).trans hE, hc, hEn.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hqδ (norm_nonneg A)

/-- **Algorithm 9.3.1** of [golub2013matrix], the claim of the algorithm, under an extra hypothesis.
Let $A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, and let $\delta$ be such that some $q$ has
$\epsilon(q, q) \le \delta$. Let $j = \max\{0, 1 + \lfloor \log_2 \|A\|_\infty \rfloor\}$ and
$q$ be as the algorithm computes them, and suppose that $\|A\|_\infty / 2^j \le 1/2$. Then in
exact arithmetic the algorithm "computes $F = e^{A+E}$ where
$\|E\|_\infty \le \delta \|A\|_\infty$", and moreover $AE = EA$.

**Correction.** The source claims the bound with no hypothesis on $A$, but the printed exponent
does not deliver $\|A\|_\infty / 2^j \le 1/2$, which the Moler–Van Loan bound needs. With
$\nu = \|A\|_\infty$, the hypothesis holds for $\nu \le 1/2$, where $j = 0$ and no scaling
happens. It fails for $\nu \in (1/2, 1)$, where $j = 0$ and the ratio is $\nu$. For $\nu \ge 1$
the ratio $\nu / 2^j$ lies in $[1/2, 1)$, and it equals $1/2$ only when $\nu$ is a power of two;
for example $\nu = 3$ gives $j = 2$ and the ratio $3/4$. So where scaling happens the hypothesis
almost never holds. The corrected exponent $\max\{0, 2 + \lfloor \log_2 \nu \rfloor\}$ always
delivers it; see `GolubVanLoan.Chapter09.algorithm_9_3_1_corrected_spec_backward`.

A suitable $q$ exists for every $\delta > 0$. The hypothesis on $\delta$ states this existence
directly. -/
theorem algorithm_9_3_1_spec_backward [NeZero n] {δ : ℝ} (hδ : ∃ q, Pade.errorBound q q ≤ δ)
    (A : Matrix (Fin n) (Fin n) ℝ) {j q : ℕ}
    (hj : j = (1 + Int.log 2 (⨆ i, ∑ l, |A i l|)).toNat)
    (hq : q = sInf {q : ℕ | Pade.errorBound q q ≤ δ}) (hA : ‖A‖ / 2 ^ j ≤ 1 / 2) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ,
      Id.run (algorithm_9_3_1 pure δ A) = exp (A + E) ∧ A * E = E * A ∧ ‖E‖ ≤ δ * ‖A‖ :=
  scalingSquaring_spec_backward 1 hδ A hj hq hA

/-- With the norm $\|\cdot\|_\infty$ and $n \ge 1$, $\|A\|_\infty$ is the largest absolute row sum
$\max_i \sum_l |a_{il}|$. -/
private theorem norm_eq_iSup_sum_abs [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A‖ = ⨆ i, ∑ l, |A i l| := by
  rw [Matrix.linfty_opNorm_def, Finset.sup_univ_eq_ciSup, NNReal.coe_iSup]
  simp [Real.norm_eq_abs]

/-- For every $\nu \ge 0$, the corrected exponent $j = \max\{0, 2 + \lfloor \log_2 \nu \rfloor\}$
gives $\nu / 2^j \le 1/2$.

**Reading.** Proves the needed inequality for offset 2 and explicit zero case.
-/
private theorem div_two_pow_corrected_le {ν : ℝ} (hν : 0 ≤ ν) :
    ν / 2 ^ (2 + Int.log 2 ν).toNat ≤ 1 / 2 := by
  rcases hν.eq_or_lt with rfl | hν
  · simp
  have hlt : ν < (2 : ℝ) ^ (Int.log 2 ν + 1) := Int.lt_zpow_succ_log_self (by norm_num) ν
  have hpos : (0 : ℝ) < 2 ^ (2 + Int.log 2 ν).toNat := by positivity
  rw [div_le_iff₀ hpos]
  have hcast : ((2 : ℝ) ^ (2 + Int.log 2 ν).toNat) = (2 : ℝ) ^ ((2 + Int.log 2 ν).toNat : ℤ) :=
    (zpow_natCast _ _).symm
  rw [hcast]
  have hmono : (2 : ℝ) ^ (2 + Int.log 2 ν) ≤ 2 ^ ((2 + Int.log 2 ν).toNat : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (Int.self_le_toNat _)
  have heq : (2 : ℝ) ^ (2 + Int.log 2 ν) = 2 * 2 ^ (Int.log 2 ν + 1) := by
    rw [show 2 + Int.log 2 ν = 1 + (Int.log 2 ν + 1) by ring, zpow_add₀ (by norm_num), zpow_one]
  nlinarith

/-- **Algorithm 9.3.1** of [golub2013matrix], with the corrected exponent, delivers its claim. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$, and let $\delta$ be such that some $q$ has
$\epsilon(q, q) \le \delta$. Then in exact arithmetic
`GolubVanLoan.Chapter09.algorithm_9_3_1_corrected`, with $j = \max\{0, 2 + \lfloor \log_2
\|A\|_\infty \rfloor\}$, computes $F = e^{A+E}$ for some $E$ with $AE = EA$ and
$$\|E\|_\infty \le \delta \|A\|_\infty.$$
There is no hypothesis on $A$.

**Correction.** The source prints the exponent $j = \max\{0, 1 + \lfloor \log_2 \|A\|_\infty
\rfloor\}$, for which the claim needs the extra hypothesis of
`GolubVanLoan.Chapter09.algorithm_9_3_1_spec_backward`. -/
theorem algorithm_9_3_1_corrected_spec_backward [NeZero n] {δ : ℝ}
    (hδ : ∃ q, Pade.errorBound q q ≤ δ) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ,
      Id.run (algorithm_9_3_1_corrected pure δ A) = exp (A + E) ∧ A * E = E * A ∧
        ‖E‖ ≤ δ * ‖A‖ := by
  refine scalingSquaring_spec_backward 2 hδ A rfl rfl ?_
  rw [norm_eq_iSup_sum_abs]
  exact div_two_pow_corrected_le
    (Real.iSup_nonneg fun i => Finset.sum_nonneg fun l _ => abs_nonneg _)

end Infinity

/-! ### §9.3.2 Perturbation theory -/

section Two

open scoped Matrix.Norms.L2Operator

/-- **§9.3.2** of [golub2013matrix], the differential equation. Let $A \in \mathbb{R}^{n \times n}$.
Then $X(t) = e^{At}$ satisfies $\dot X(t) = A X(t)$ for every $t \in \mathbb{R}$ and $X(0) = I$,
and it is the unique function $X : \mathbb{R} \to \mathbb{R}^{n \times n}$ with these
properties. -/
theorem exp_unique_ode (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => exp (s • A)) (A * exp (t • A)) t) ∧
    exp ((0 : ℝ) • A) = 1 ∧
    ∀ X : ℝ → Matrix (Fin n) (Fin n) ℝ, (∀ t, HasDerivAt X (A * X t) t) → X 0 = 1 →
      ∀ t, X t = exp (t • A) :=
  ⟨fun t => hasDerivAt_exp_smul_const' A t, by rw [zero_smul, exp_zero],
    fun _ hX h0 t => eq_exp_smul_of_hasDerivAt hX h0 t⟩

/-- **§9.3.2** of [golub2013matrix], the variation-of-constants identity. Let
$A, E \in \mathbb{R}^{n \times n}$ and $t \in \mathbb{R}$. Then
$$e^{(A+E)t} - e^{At} = \int_0^t e^{A(t-s)} E e^{(A+E)s} \, ds,$$
and for $t \ge 0$
$$\frac{\|e^{(A+E)t} - e^{At}\|_2}{\|e^{At}\|_2} \le \frac{\|E\|_2}{\|e^{At}\|_2} \int_0^t
  \|e^{A(t-s)}\|_2 \|e^{(A+E)s}\|_2 \, ds.$$

**Reading.** The source leaves the time domain implicit. The Lean identity holds for all real
$t$, while the relative norm estimate assumes $t\geq 0$. -/
theorem exp_perturbation_integral (A E : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    exp (t • (A + E)) - exp (t • A) =
      ∫ s in (0 : ℝ)..t, exp ((t - s) • A) * E * exp (s • (A + E)) ∧
    (0 ≤ t → ‖exp (t • (A + E)) - exp (t • A)‖ / ‖exp (t • A)‖ ≤
      ‖E‖ / ‖exp (t • A)‖ * ∫ s in (0 : ℝ)..t, ‖exp ((t - s) • A)‖ * ‖exp (s • (A + E))‖) := by
  refine ⟨exp_smul_add_sub_exp_smul A E t, fun ht => ?_⟩
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (norm_exp_smul_add_sub_exp_smul_le A E ht) (norm_nonneg _)

/-- **Equation (9.3.3)** of [golub2013matrix], the spectral abscissa. Let
$A \in \mathbb{C}^{n \times n}$ with $n \ge 1$. The spectral abscissa $\alpha(A) =
\max\{\operatorname{Re} \lambda : \lambda \in \lambda(A)\}$ is attained by an eigenvalue of $A$,
and $\operatorname{Re} \lambda \le \alpha(A)$ for every eigenvalue $\lambda$.

The spectral abscissa is `spectralAbscissa A`, a supremum of real parts. -/
theorem equation_9_3_3 [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ μ ∈ spectrum ℂ A, μ.re = spectralAbscissa A) ∧
    ∀ μ ∈ spectrum ℂ A, μ.re ≤ spectralAbscissa A :=
  ⟨exists_mem_spectrum_re_eq_spectralAbscissa (Matrix.finite_spectrum A).isCompact
      (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ A),
    fun _ hμ => re_le_spectralAbscissa (Matrix.finite_spectrum A).isBounded hμ⟩

/-- **Equation (9.3.2)** of [golub2013matrix], corrected. Let $A, Q \in \mathbb{C}^{n \times n}$
with $n \ge 1$, $Q$ unitary and $Q^H A Q = \operatorname{diag}(\lambda_i) + N$ upper triangular,
with $N$ the strictly upper triangular part. Then for $t \ge 0$
$$\|e^{At}\|_2 \le e^{\alpha(A) t} M_S(t), \qquad M_S(t) = \sum_{k=0}^{n-1}
  \frac{\|Nt\|_2^k}{k!}.$$

**Typo.** The source prints $e^{\alpha(A) t M_S(t)}$ for $e^{\alpha(A) t} M_S(t)$. As printed
the bound fails for $\alpha(A) < 0$ and $N \neq 0$. -/
theorem equation_9_3_2 [NeZero n] {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : (star Q * A * Q).IsUpperTriangular) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖exp (t • A)‖ ≤ Real.exp (spectralAbscissa A * t) * ∑ k ∈ range n,
      ‖t • (star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i)‖ ^ k / k ! := by
  simpa only [Matrix.schurExpFactor, Fintype.card_fin] using
    Matrix.l2_opNorm_exp_smul_le_of_schur hQ hT ht

/-- **§9.3.2** of [golub2013matrix], the relative perturbation bound obtained "with a little
manipulation". Let $A, Q, E \in \mathbb{C}^{n \times n}$ with $n \ge 1$, $Q$ unitary and
$Q^H A Q = \operatorname{diag}(\lambda_i) + N$ upper triangular, and let $M_S(t)$ be as in
(9.3.2). Then for $t \ge 0$
$$\frac{\|e^{(A+E)t} - e^{At}\|_2}{\|e^{At}\|_2} \le t \|E\|_2 M_S(t)^2 \exp(t M_S(t)
  \|E\|_2).$$

**Reading.** The relative bound assumes $t\geq 0$, as required by its right-hand side and the
integral estimate. -/
theorem exp_perturbation_schur [NeZero n] {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : (star Q * A * Q).IsUpperTriangular)
    (E : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : 0 ≤ t) :
    let N := star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i
    let MS : ℝ → ℝ := fun s => (∑ k ∈ range n, ‖s • N‖ ^ k / k !)
    ‖exp (t • (A + E)) - exp (t • A)‖ / ‖exp (t • A)‖ ≤
      t * ‖E‖ * MS t ^ 2 * Real.exp (t * MS t * ‖E‖) := by
  have h := Matrix.l2_opNorm_exp_smul_add_sub_le hQ hT E ht
  simp only [Matrix.schurExpFactor, Fintype.card_fin] at h
  exact h

/-- **§9.3.2** of [golub2013matrix], the normal case of $M_S$. Let
$A, Q \in \mathbb{C}^{n \times n}$ with $n \ge 1$, $Q$ unitary and
$Q^H A Q = \operatorname{diag}(\lambda_i) + N$ upper triangular. Then $M_S(t) = 1$ for all
$t > 0$ if and only if $A$ is normal.

For normal $A$ the Schur form is diagonal, $N = 0$. -/
theorem schurDeparture_eq_one_iff [NeZero n] {A Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : (star Q * A * Q).IsUpperTriangular) :
    (∀ t : ℝ, 0 < t → ∑ k ∈ range n,
      ‖t • (star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i)‖ ^ k / k ! = 1) ↔
      IsStarNormal A := by
  rw [Matrix.isStarNormal_iff_strictUpper_eq_zero hQ hT, ← sub_eq_zero]
  set N := star Q * A * Q - Matrix.diagonal fun i => (star Q * A * Q) i i
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  constructor
  · intro h
    have h1 := h 1 one_pos
    rw [Finset.sum_range_succ', pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      add_eq_right] at h1
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => by positivity).mp h1
    rcases m with _ | m
    · ext i j
      obtain rfl : i = j := Fin.ext (by have := i.2; have := j.2; omega)
      simp [N]
    · have h0 := hz 0 (Finset.mem_range.mpr (Nat.succ_pos m))
      simpa [one_smul] using h0
  · intro hN t _
    rw [hN, Finset.sum_range_succ']
    simp

/-- **§9.3.2** of [golub2013matrix], the lower bound on the condition number. Let
$A \in \mathbb{C}^{n \times n}$ with $n \ge 1$. Then Van Loan's condition number satisfies
$\nu(A, t) \ge t \|A\|_2$ for every $t \ge 0$. -/
theorem expCondNumber_ge [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : 0 ≤ t) :
    t * ‖A‖ ≤ expCondNumber A t :=
  mul_norm_le_expCondNumber A ht

/-- **Equation (9.3.4)** of [golub2013matrix]. Let $A \in \mathbb{C}^{n \times n}$ be normal, with
$n \ge 1$. Then for $t \ge 0$
$$\|e^{At}\|_2 = e^{\alpha(A) t}.$$

**Reading.** The identity with the largest real part of an eigenvalue holds for nonnegative
$t$. The Lean theorem makes that time restriction explicit. -/
theorem equation_9_3_4 [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) {t : ℝ}
    (ht : 0 ≤ t) : ‖exp (t • A)‖ = Real.exp (spectralAbscissa A * t) :=
  Matrix.l2_opNorm_exp_smul_of_isStarNormal hA ht

/-- **§9.3.2** of [golub2013matrix], the equality case for normal matrices. Let
$A \in \mathbb{C}^{n \times n}$ be normal, with $n \ge 1$. Then $\nu(A, t) = t \|A\|_2$ for
every $t \ge 0$.

**Correction.** The source states "equality holding for all nonnegative $t$ if and only if the
matrix $A$ is normal". Only the "if" direction, stated here, is true; see
`GolubVanLoan.Chapter09.expCondNumber_eq_iff_counterexample`. -/
theorem expCondNumber_eq_of_isStarNormal [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsStarNormal A) {t : ℝ} (ht : 0 ≤ t) : expCondNumber A t = t * ‖A‖ :=
  Matrix.expCondNumber_eq_of_isStarNormal hA ht

end Two

/-- **Equation (9.3.5)** of [golub2013matrix]. For every $t \in \mathbb{R}$,
$$\exp\left( \begin{bmatrix} -1 & 1000 \\ 0 & -1 \end{bmatrix} t \right) = e^{-t}
  \begin{bmatrix} 1 & 1000 t \\ 0 & 1 \end{bmatrix}.$$
-/
theorem equation_9_3_5 (t : ℝ) :
    exp (t • !![-1, 1000; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) =
      Real.exp (-t) • !![1, 1000 * t; 0, 1] := by
  set N : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1000 * t; 0, 0]
  have hsplit : (t • !![-1, 1000; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.diagonal (fun _ => -t) + N := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, mul_comm]
  have hN2 : N ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hc : Commute (Matrix.diagonal fun _ : Fin 2 => -t) N := by
    rw [← Matrix.smul_one_eq_diagonal]
    exact (Commute.one_left N).smul_left _
  have hexpN : exp N = 1 + N := NormedSpace.exp_eq_one_add_of_sq_eq_zero hN2
  rw [hsplit, Matrix.exp_add_of_commute _ _ hc, Matrix.exp_diagonal, hexpN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Pi.exp_def, ← Real.exp_eq_exp_ℝ]

section Counterexample

open scoped Matrix.Norms.L2Operator

/-- The exponential of the counterexample matrix $A = [1] \oplus \begin{bmatrix} 0 & 1 \\ 0 & 0
\end{bmatrix}$ is $e^{sA} = [e^s] \oplus \begin{bmatrix} 1 & s \\ 0 & 1 \end{bmatrix}$. -/
private theorem exp_smul_cex (s : ℝ) :
    exp (s • (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ)) =
      !![(Real.exp s : ℂ), 0, 0; 0, 1, (s : ℂ); 0, 0, 1] := by
  set N : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 0; 0, 0, (s : ℂ); 0, 0, 0]
  have hsplit : (s • !![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) =
      Matrix.diagonal ![(s : ℂ), 0, 0] + N := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N]
  have hN2 : N ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, sq, Matrix.mul_apply, Fin.sum_univ_three]
  have hc : Commute (Matrix.diagonal ![(s : ℂ), 0, 0]) N := by
    unfold Commute SemiconjBy
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply, Fin.sum_univ_three]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hc, Matrix.exp_diagonal,
    NormedSpace.exp_eq_one_add_of_sq_eq_zero hN2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.mul_apply, Fin.sum_univ_three, Pi.exp_def, ← Complex.exp_eq_exp_ℂ,
      Complex.ofReal_exp]

/-- For the counterexample matrix $A$ and $s \ge 0$, $\|e^{sA}\|_2 = e^s$, because the block
$\begin{bmatrix} 1 & s \\ 0 & 1 \end{bmatrix}$ has norm at most $1 + s \le e^s$. -/
private theorem norm_exp_smul_cex {s : ℝ} (hs : 0 ≤ s) :
    ‖exp (s • (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ))‖ = Real.exp s := by
  rw [exp_smul_cex]
  set M : Matrix (Fin 3) (Fin 3) ℂ := !![(Real.exp s : ℂ), 0, 0; 0, 1, (s : ℂ); 0, 0, 1]
  set E := Real.exp s
  have hE : 0 < E := Real.exp_pos s
  have hv : ∀ x : EuclideanSpace ℂ (Fin 3),
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x) 0 = (E : ℂ) * x 0 ∧
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x) 1 = x 1 + (s : ℂ) * x 2 ∧
      (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x) 2 = x 2 := fun x => by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [M, E, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hsq : ∀ x : EuclideanSpace ℂ (Fin 3),
      ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x‖ ^ 2 =
        ‖(E : ℂ) * x 0‖ ^ 2 + ‖x 1 + (s : ℂ) * x 2‖ ^ 2 + ‖x 2‖ ^ 2 := fun x => by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, (hv x).1, (hv x).2.1, (hv x).2.2]
  have hEn : ‖(E : ℂ)‖ = E := by rw [Complex.norm_real, Real.norm_of_nonneg hE.le]
  apply le_antisymm
  · rw [Matrix.cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ hE.le fun x => ?_
    have h1 : 1 + s ≤ E := by linarith [Real.add_one_le_exp s]
    set a := ‖x 1‖
    set b := ‖x 2‖
    set c := ‖x 0‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have hab : ‖x 1 + (s : ℂ) * x 2‖ ≤ a + s * b := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
    have hx : ‖x‖ ^ 2 = c ^ 2 + a ^ 2 + b ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), hsq, mul_pow, hx, norm_mul, hEn]
    have h2 : ‖x 1 + (s : ℂ) * x 2‖ ^ 2 ≤ (a + s * b) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hab 2
    have h3 : (a + s * b) ^ 2 + b ^ 2 ≤ (1 + s) ^ 2 * (a ^ 2 + b ^ 2) := by
      nlinarith [mul_nonneg hs (sq_nonneg (a - b)), sq_nonneg (s * a),
        mul_nonneg hs (add_nonneg (sq_nonneg a) (sq_nonneg b))]
    have h4 : (1 + s) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith [mul_le_mul_of_nonneg_right h4 (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  · rw [Matrix.cstar_norm_def]
    set x : EuclideanSpace ℂ (Fin 3) := EuclideanSpace.single 0 1
    have hx : ‖x‖ = 1 := by simp [x]
    have hMx : ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x‖ = E := by
      rw [← sq_eq_sq₀ (norm_nonneg _) hE.le, hsq]
      simp [x]
    calc E = ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M x‖ := hMx.symm
      _ ≤ ‖Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) M‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [hx, mul_one]

/-- **§9.3.2** of [golub2013matrix], counterexample to the equality case. The matrix
$$A = [1] \oplus \begin{bmatrix} 0 & 1 \\ 0 & 0 \end{bmatrix} = \begin{bmatrix} 1 & 0 & 0 \\ 0 &
  0 & 1 \\ 0 & 0 & 0 \end{bmatrix} \in \mathbb{C}^{3 \times 3}$$
is not normal, and yet $\nu(A, t) = t \|A\|_2$ for every $t \ge 0$. So the "only if" direction
of the source's "equality holding for all nonnegative $t$ if and only if the matrix $A$ is
normal" is false.

The equality holds because $\|e^{sA}\|_2 = e^s$ for $s \ge 0$.

**Correction.** Provides nonnormal counterexample to the claimed necessary direction.
-/
theorem expCondNumber_eq_iff_counterexample :
    ¬ IsStarNormal (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) ∧
    ∀ t : ℝ, 0 ≤ t → expCondNumber (!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) t =
      t * ‖(!![1, 0, 0; 0, 0, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ)‖ := by
  refine ⟨fun h => ?_, fun t ht => expCondNumber_eq_of_norm_exp_smul_eq _ ht fun s hs => by
    rw [one_mul]
    exact norm_exp_smul_cex hs.1⟩
  have := congrFun (congrFun h.star_comm_self 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_eq_conjTranspose] at this

end Counterexample

/-! ### §9.3.3 Pseudospectra and transient growth -/

section Pseudospectra

open scoped Matrix.Norms.L2Operator
open Filter Topology

/-- **Equation (9.3.6)** of [golub2013matrix]. Let $A \in \mathbb{C}^{n \times n}$ with $n \ge 1$,
and let $\epsilon > 0$. If $\|e^{At}\|_2 \le M$ for all $t > 0$, then
$$\alpha_\epsilon(A) \le \epsilon M,$$
where $\alpha_\epsilon(A) = \sup_{z \in \Lambda_\epsilon(A)} \operatorname{Re} z$ is the
$\epsilon$-pseudospectral abscissa. This is the source's $\sup_{t > 0} \|e^{At}\|_2 \ge
\alpha_\epsilon(A) / \epsilon$, stated for every bound $M$ of the supremum.

**Typo.** The source cites "(7.8.8)" for the pseudospectral abscissa, which is (7.9.8).

The pseudospectral abscissa is `GolubVanLoan.Chapter07.pseudospectralAbscissa`. It is attained
at some $z \in \Lambda_\epsilon(A)$. If $\operatorname{Re} z > 0$, then $z \notin \lambda(A)$
and $1/\epsilon \le \|(zI - A)^{-1}\|_2 \le M / \operatorname{Re} z$, by (7.9.6) and the
Laplace-transform bound `norm_resolvent_le_of_norm_exp_smul_le`; that bound also needs the bound
at $t = 0$, which follows by continuity. -/
theorem equation_9_3_6 [NeZero n] {ε : ℝ} (hε : 0 < ε) (A : Matrix (Fin n) (Fin n) ℂ) {M : ℝ}
    (hM : ∀ t : ℝ, 0 < t → ‖exp (t • A)‖ ≤ M) :
    Chapter07.pseudospectralAbscissa ε A ≤ ε * M := by
  have hM0 : ∀ t : ℝ, 0 ≤ t → ‖exp (t • A)‖ ≤ M := by
    intro t ht
    rcases ht.eq_or_lt with rfl | ht
    · have hsm : Continuous fun t : ℝ => t • A := continuous_id.smul continuous_const
      have hc : ContinuousAt (fun t : ℝ => ‖exp (t • A)‖) 0 :=
        (((NormedSpace.exp_analytic (𝕂 := ℂ) ((0 : ℝ) • A)).continuousAt).comp
          (f := fun t : ℝ => t • A) hsm.continuousAt).norm
      exact le_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall (s := Set.Ioi 0) fun t ht => hM t ht)
    · exact hM t ht
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM0 0 le_rfl)
  obtain ⟨z, hz, hre⟩ := (Chapter07.pseudospectralAbscissa_spec hε.le A).2.2.1
  rw [← hre]
  rcases le_or_gt z.re 0 with hz0 | hz0
  · exact hz0.trans (mul_nonneg hε.le hMnn)
  · obtain ⟨hns, hres⟩ := norm_resolvent_le_of_norm_exp_smul_le hM0 hz0
    have h1 := ((Chapter07.equation_7_9_6 hε A z).1 hz).resolve_left hns
    rw [Algebra.algebraMap_eq_smul_one, ← Matrix.nonsing_inv_eq_ringInverse] at hres
    have h2 : 1 / ε ≤ M / z.re := h1.trans hres
    rw [div_le_div_iff₀ hε hz0] at h2
    linarith

end Pseudospectra

/-! ### §9.3.4 Some stability issues -/

section Two

open scoped Matrix.Norms.L2Operator

/-- **§9.3.4** of [golub2013matrix], the normal case. Let $A \in \mathbb{C}^{n \times n}$ be normal,
with $n \ge 1$, and let $q, j \ge 0$. Then $G = R_{qq}(A/2^j)$ is normal, and
$\|G^m\|_2 = \|G\|_2^m$ for every $m \ge 0$.

**Reading.** The Lean statement extends the power identity to $m=0$. Its Padé evaluation also
uses a total inverse, so $G$ is defined as zero when the Padé denominator is singular. -/
theorem normal_squaring [NeZero n] {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A)
    (q j : ℕ) :
    IsStarNormal (Pade.expApprox ℂ q q ((2⁻¹ : ℂ) ^ j • A)) ∧
    ∀ m : ℕ, ‖Pade.expApprox ℂ q q ((2⁻¹ : ℂ) ^ j • A) ^ m‖ =
      ‖Pade.expApprox ℂ q q ((2⁻¹ : ℂ) ^ j • A)‖ ^ m := by
  set B := (2⁻¹ : ℂ) ^ j • A
  have hB : IsStarNormal B := ⟨by
    rw [star_smul]
    exact (hA.star_comm_self.smul_left _).smul_right _⟩
  obtain ⟨r, hr⟩ := Matrix.IsStarNormal.exists_aeval_eq_conjTranspose hB
  have hsB : star B = aeval B r := by rw [Matrix.star_eq_conjTranspose, hr]
  set Dm := aeval B (Pade.expDen ℂ q q)
  set Nm := aeval B (Pade.expNum ℂ q q)
  have hG : Pade.expApprox ℂ q q B = Dm⁻¹ * Nm := by
    rw [Pade.expApprox, Matrix.nonsing_inv_eq_ringInverse]
  -- anything commuting with `B` commutes with `G`
  have hcomm : ∀ X : Matrix (Fin n) (Fin n) ℂ, Commute X B → Commute X (Dm⁻¹ * Nm) :=
    fun X hX => (Matrix.commute_nonsing_inv_right (hX.aeval_right _)).mul_right
      (hX.aeval_right _)
  have hGB : Commute (Dm⁻¹ * Nm) B := (hcomm B (Commute.refl B)).symm
  have hGsB : Commute (Dm⁻¹ * Nm) (star B) := by
    rw [hsB]
    exact hGB.aeval_right r
  have hsGB : Commute (star (Dm⁻¹ * Nm)) B := by
    simpa only [star_star] using hGsB.star_star
  have hN : IsStarNormal (Pade.expApprox ℂ q q B) := by
    rw [hG]
    exact ⟨hcomm _ hsGB⟩
  refine ⟨hN, fun m => ?_⟩
  have hNm : IsStarNormal (Pade.expApprox ℂ q q B ^ m) := IsStarNormal.pow m
  have h1 := Matrix.l2_opNorm_eq_spectralRadius_of_isStarNormal (Pade.expApprox ℂ q q B ^ m)
  rw [spectralRadius_pow, ← Matrix.l2_opNorm_eq_spectralRadius_of_isStarNormal] at h1
  have h2 : ‖Pade.expApprox ℂ q q B ^ m‖₊ = ‖Pade.expApprox ℂ q q B‖₊ ^ m := by
    exact_mod_cast h1
  rw [← coe_nnnorm, h2, NNReal.coe_pow, coe_nnnorm]

end Two

end GolubVanLoan.Chapter09
