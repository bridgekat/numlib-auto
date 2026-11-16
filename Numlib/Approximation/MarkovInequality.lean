/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Approximation.OrthogonalPolynomial.LegendreBounds
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# The $L^2$ Markov inequality on $[-1, 1]$

Let $\mathbb{P}_N$ be the real polynomials of degree at most $N$, and let $L_k$ be the Legendre
polynomials, normalized by Rodrigues' formula so that $L_k(1) = 1$. This module proves that every
$p \in \mathbb{P}_N$ satisfies
$$\|p'\|_{L^2(-1,1)} \le N (N + 1) \|p\|_{L^2(-1,1)}.$$
This is the $L^2$ analogue of Markov's inequality $\|p'\|_\infty \le N^2 \|p\|_\infty$. It is the
reason why the largest eigenvalue of a spectral (Legendre or Gauss–Lobatto) stiffness matrix grows
like $N^4$ ([quarteroni2000numerical], §13.3.1, (13.24)). The constant $N (N + 1)$ is not the sharp
one, but the order $N^2$ is: the test polynomial $L_N' \in \mathbb{P}_{N-1}$ satisfies
$\|L_N''\|^2 \ge ((N(N+1))^2/36) \|L_N'\|^2$ for $N \ge 2$. For the inverse inequalities of Legendre
expansions, see also Canuto, Hussaini, Quarteroni and Zang, *Spectral Methods in Fluid Dynamics*
(Springer, 1988), §9.4.

The proofs use the Legendre coefficients $\hat p_k = ((2k + 1)/2) \int_{-1}^1 p L_k$ of a polynomial
$p$. For $p \in \mathbb{P}_N$ they give the expansion $p = \sum_{k \le N} \hat p_k L_k$ and
Parseval's identity $\int_{-1}^1 p^2 = \sum_{k \le N} \hat p_k^2 \cdot 2/(2k + 1)$.

## Main definitions

* `Polynomial.legendreCoeff`: the Legendre coefficient $\hat p_k = ((2k + 1)/2) \int_{-1}^1 p L_k$.

## Main results

* `Polynomial.eq_sum_legendreCoeff`: the Legendre expansion $p = \sum_{k \le N} \hat p_k L_k$ of
  $p \in \mathbb{P}_N$.
* `Polynomial.integral_sq_eq_sum_legendreCoeff`: Parseval's identity $\int_{-1}^1 p^2 = \sum_{k \le
  N} \hat p_k^2 \cdot 2/(2k + 1)$ for $p \in \mathbb{P}_N$.
* `Polynomial.eval_one_derivative_legendre`, `Polynomial.eval_neg_one_derivative_legendre`:
  $L_n'(1) = n(n+1)/2$ and $L_n'(-1) = (-1)^{n+1} n(n+1)/2$.
* `Polynomial.integral_derivative_legendre_mul_legendre`: $\int_{-1}^1 L_k' L_j = 1 - (-1)^{k+j}$
  for $j < k$, and $0$ for $k \le j$.
* `Polynomial.integral_derivative_sq_le`: the $L^2$ Markov inequality $\int_{-1}^1 (p')^2 \le
  (N(N+1))^2 \int_{-1}^1 p^2$ for $p \in \mathbb{P}_N$.
* `Polynomial.sqrt_integral_derivative_sq_le`: the same inequality for the $L^2$ norms.
* `Polynomial.integral_derivative_legendre_sq`: $\|L_n'\|^2_{L^2(-1,1)} = n(n+1)$.
* `Polynomial.integral_derivative_derivative_legendre_sq_ge`: for $N \ge 2$,
  $\|L_N''\|^2 \ge ((N(N+1))^2/36) \|L_N'\|^2$, so the order $N^2$ of the constant cannot be
  improved.

## Proof outline

The expansion and Parseval's identity follow from the orthogonality
$\int_{-1}^1 L_j L_k = (2/(2k + 1)) \delta_{jk}$ of `Numlib.Approximation.OrthogonalPolynomial`.
Integration by parts gives $\int_{-1}^1 L_k' L_j = 1 - (-1)^{k+j}$ for $j < k$ and $0$ otherwise.
This is the identity behind the classical expansion $L_k' = \sum_{j < k,\ k - j \text{ odd}}
(2j + 1) L_j$. Hence the coefficients of $p'$ satisfy $|\widehat{(p')}_j| \le (2j + 1) \sum_k |\hat
p_k|$. The Cauchy–Schwarz inequality $(\sum_k |\hat p_k|)^2 \le ((N + 1)^2/2) \int p^2$ and the sum
$\sum_{j < N} (2j + 1) = N^2$ then give the bound. For the sharpness, integration by parts gives
$\int_{-1}^1 x L_N' L_N'' = (N(N+1)/2)^2 - N(N+1)/2$ and $\|L_N'\|^2 = N(N+1)$, from the endpoint
values $L_n'(\pm 1) = (\pm 1)^{n+1} n(n+1)/2$, and the Cauchy–Schwarz inequality against $x L_N'$
gives the lower bound.

## Implementation notes

* A polynomial $p \in \mathbb{P}_N$ is a `p : ℝ[X]` with `p.natDegree ≤ N`. The zero polynomial is
  included. The Legendre polynomial $L_k$ is `Polynomial.legendre k`.
* The $L^2(-1, 1)$ norms are written as interval integrals $\int_{-1}^1$ of squares, and their
  square roots.
* The Cauchy–Schwarz inequality for interval integrals of continuous functions is
  `intervalIntegral.sq_integral_mul_le_of_continuousOn` of
  `Numlib.MeasureTheory.Integral.IntervalIntegral`.
-/

open MeasureTheory Polynomial Set

namespace Polynomial

/-! ### The Legendre coefficients of a polynomial -/

/-- The **$k$-th Legendre coefficient** of a real polynomial $p$ is
$$\hat p_k = \frac{2k + 1}{2} \int_{-1}^1 p(t) L_k(t) \, dt.$$

For $p$ of degree at most $N$, the expansion $p = \sum_{k \le N} \hat p_k L_k$ is
`Polynomial.eq_sum_legendreCoeff`. -/
noncomputable def legendreCoeff (p : ℝ[X]) (k : ℕ) : ℝ :=
  (2 * k + 1) / 2 * ∫ t in (-1 : ℝ)..1, p.eval t * (legendre k).eval t

/-- The Legendre coefficients are additive in the polynomial:
$\widehat{(p + q)}_k = \hat p_k + \hat q_k$. -/
theorem legendreCoeff_add (p q : ℝ[X]) (k : ℕ) :
    legendreCoeff (p + q) k = legendreCoeff p k + legendreCoeff q k := by
  simp only [legendreCoeff, eval_add, add_mul]
  rw [intervalIntegral.integral_add]
  · ring
  · exact ((Polynomial.continuous p).mul (Polynomial.continuous _)).intervalIntegrable _ _
  · exact ((Polynomial.continuous q).mul (Polynomial.continuous _)).intervalIntegrable _ _

/-- The Legendre coefficients are homogeneous in the polynomial: for $c \in \mathbb{R}$,
$\widehat{(c p)}_k = c \hat p_k$. -/
theorem legendreCoeff_C_mul (c : ℝ) (p : ℝ[X]) (k : ℕ) :
    legendreCoeff (C c * p) k = c * legendreCoeff p k := by
  simp only [legendreCoeff, eval_mul, eval_C, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The Legendre coefficients commute with finite sums: for a finite family of polynomials $p_i$,
$i \in s$, the $k$-th coefficient of $\sum_{i \in s} p_i$ is $\sum_{i \in s} \widehat{(p_i)}_k$. -/
theorem legendreCoeff_sum {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) (k : ℕ) :
    legendreCoeff (∑ i ∈ s, p i) k = ∑ i ∈ s, legendreCoeff (p i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [legendreCoeff]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, legendreCoeff_add, ih]

/-- The Legendre polynomial $L_j$ has the Legendre coefficients $\widehat{(L_j)}_k = \delta_{jk}$:
the coefficient is $1$ if $j = k$ and $0$ otherwise.

This is the orthogonality relation $\int_{-1}^1 L_j L_k = (2/(2k+1)) \delta_{jk}$. -/
theorem legendreCoeff_legendre (j k : ℕ) :
    legendreCoeff (legendre j) k = if j = k then 1 else 0 := by
  rw [legendreCoeff, integral_legendre_mul_legendre]
  split_ifs with h
  · field_simp
  · simp

/-- If a real polynomial $p$ has degree less than $k$, then its $k$-th Legendre coefficient
$\hat p_k$ is $0$. -/
theorem legendreCoeff_eq_zero_of_natDegree_lt {p : ℝ[X]} {k : ℕ} (hp : p.natDegree < k) :
    legendreCoeff p k = 0 := by
  have h := OrthogonalPolynomial.integral_legendre_mul_of_degree_lt
    (n := k) (p := p) ((degree_lt_iff_coeff_zero p k).mpr fun m hm =>
      coeff_eq_zero_of_natDegree_lt (hp.trans_le hm))
  rw [OrthogonalPolynomial.integral_legendreMeasure] at h
  rw [legendreCoeff, intervalIntegral.integral_congr (fun t _ => mul_comm (p.eval t) _), h,
    mul_zero]

/-- The **Legendre expansion of a polynomial**: if a real polynomial $p$ has degree at most $N$,
then
$$p = \sum_{k = 0}^{N} \hat p_k L_k.$$

The Legendre polynomials $L_0, \dots, L_N$ span the polynomials of degree at most $N$
(`OrthogonalPolynomial.exists_eq_sum_family`), and orthogonality gives the coefficients of any
such expansion. -/
theorem eq_sum_legendreCoeff {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    p = ∑ k ∈ Finset.range (N + 1), C (legendreCoeff p k) * legendre k := by
  obtain ⟨c, hc⟩ := OrthogonalPolynomial.exists_eq_sum_family OrthogonalPolynomial.legendreMeasure
    (n := N + 1) (q := p)
    (degree_le_of_natDegree_le hp |>.trans_lt (by exact_mod_cast N.lt_succ_self))
  have hexp : p = ∑ k ∈ Finset.range (N + 1),
      C (c k * ((legendre k).leadingCoeff)⁻¹) * legendre k := by
    rw [hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [OrthogonalPolynomial.family_eq_legendre, smul_eq_C_mul, ← mul_assoc, ← C_mul]
  have hcoeff : ∀ k ∈ Finset.range (N + 1),
      legendreCoeff p k = c k * ((legendre k).leadingCoeff)⁻¹ := by
    intro k hk
    conv_lhs => rw [hexp]
    rw [legendreCoeff_sum, Finset.sum_eq_single k]
    · rw [legendreCoeff_C_mul, legendreCoeff_legendre, ite_eq_left rfl, mul_one]
    · intro j _ hjk
      rw [legendreCoeff_C_mul, legendreCoeff_legendre, ite_eq_right hjk, mul_zero]
    · intro h; exact absurd hk h
  conv_lhs => rw [hexp]
  exact Finset.sum_congr rfl fun k hk => by rw [hcoeff k hk]

/-- **Parseval's identity for the Legendre expansion**: if a real polynomial $p$ has degree at most
$N$, then
$$\int_{-1}^1 p(t)^2 \, dt = \sum_{k = 0}^{N} \hat p_k^2 \, \frac{2}{2k + 1}.$$
-/
theorem integral_sq_eq_sum_legendreCoeff {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 =
      ∑ k ∈ Finset.range (N + 1), legendreCoeff p k ^ 2 * (2 / (2 * k + 1)) := by
  have hint : ∀ q r : ℝ[X], IntervalIntegrable (fun t => q.eval t * r.eval t) volume (-1) 1 :=
    fun q r => ((Polynomial.continuous q).mul (Polynomial.continuous r)).intervalIntegrable _ _
  have hsq : ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 = ∫ t in (-1 : ℝ)..1, p.eval t * p.eval t :=
    intervalIntegral.integral_congr fun t _ => sq _
  rw [hsq]
  have hexp := eq_sum_legendreCoeff hp
  have hev : ∀ t, p.eval t * p.eval t = ∑ k ∈ Finset.range (N + 1),
        legendreCoeff p k * (p.eval t * (legendre k).eval t) := by
    intro t
    calc p.eval t * p.eval t
        = (∑ k ∈ Finset.range (N + 1), C (legendreCoeff p k) * legendre k).eval t * p.eval t := by
          rw [← hexp]
      _ = _ := by
          rw [eval_finsetSum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by rw [eval_mul, eval_C]; ring
  simp only [hev]
  rw [intervalIntegral.integral_finsetSum fun k _ => (hint p (legendre k)).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have h2k : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have : ∫ t in (-1 : ℝ)..1, p.eval t * (legendre k).eval t =
      legendreCoeff p k * (2 / (2 * k + 1)) := by
    rw [legendreCoeff]
    field_simp
  rw [this]
  ring

/-! ### The derivatives of the Legendre polynomials at the endpoints -/

/-- For every $n \in \mathbb{N}$, the derivative of the Legendre polynomial $L_n$ at $1$ is
$L_n'(1) = n(n + 1)/2$.

The proof evaluates the recurrence $L_{n+1}' = x L_n' + (n + 1) L_n$ at $x = 1$. -/
theorem eval_one_derivative_legendre (n : ℕ) :
    (derivative (legendre n)).eval 1 = (n : ℝ) * (n + 1) / 2 := by
  induction n with
  | zero => simp [legendre_zero]
  | succ k ih =>
    rw [derivative_legendre_succ, eval_add, eval_mul, eval_X, ih, eval_mul, eval_add,
      eval_natCast, eval_one, legendre_eval_one]
    push_cast
    ring

/-- For every $n \in \mathbb{N}$, the derivative of the Legendre polynomial $L_n$ at $-1$ is
$L_n'(-1) = (-1)^{n+1} n(n + 1)/2$.

The proof evaluates the recurrence $L_{n+1}' = x L_n' + (n + 1) L_n$ at $x = -1$. -/
theorem eval_neg_one_derivative_legendre (n : ℕ) :
    (derivative (legendre n)).eval (-1) = (-1) ^ (n + 1) * ((n : ℝ) * (n + 1) / 2) := by
  induction n with
  | zero => simp [legendre_zero]
  | succ k ih =>
    rw [derivative_legendre_succ, eval_add, eval_mul, eval_X, ih, eval_mul, eval_add,
      eval_natCast, eval_one, legendre_eval_neg_one]
    push_cast
    ring

/-- For $k, j \in \mathbb{N}$,
$$\int_{-1}^1 L_k'(t) L_j(t) \, dt = \begin{cases} 1 - (-1)^{k+j} & \text{if } j < k, \\ 0 &
  \text{if } k \le j. \end{cases}$$

Integration by parts gives $\int L_k' L_j = [L_k L_j]_{-1}^1 - \int L_k L_j'$. For $j < k$ the
last integral vanishes because $L_j'$ has degree less than $k$. For $k \le j$ the integral
$\int L_k' L_j$ vanishes because $L_k'$ has degree less than $j$. This is the identity behind
the expansion $L_k' = \sum_{j < k,\ k - j \text{ odd}} (2j + 1) L_j$. -/
theorem integral_derivative_legendre_mul_legendre (k j : ℕ) :
    ∫ t in (-1 : ℝ)..1, (derivative (legendre k)).eval t * (legendre j).eval t =
      if j < k then 1 - (-1) ^ (k + j) else 0 := by
  -- orthogonality of `L_m` to derivatives of lower index
  have horth : ∀ a b : ℕ, a ≤ b →
      ∫ t in (-1 : ℝ)..1, (derivative (legendre a)).eval t * (legendre b).eval t = 0 := by
    intro a b hab
    have hdeg : (derivative (legendre a)).degree < b := by
      refine (degree_derivative_lt (legendre_ne_zero a)).trans_le ?_
      rw [degree_legendre]
      exact_mod_cast hab
    have h := OrthogonalPolynomial.integral_legendre_mul_of_degree_lt hdeg
    rw [OrthogonalPolynomial.integral_legendreMeasure] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun t _ => mul_comm _ _
  split_ifs with hjk
  · have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun t => (legendre j).eval t) (u' := fun t => (derivative (legendre j)).eval t)
      (v := fun t => (legendre k).eval t) (v' := fun t => (derivative (legendre k)).eval t)
      (a := (-1 : ℝ)) (b := 1) (fun t _ => (legendre j).hasDerivAt t)
      (fun t _ => (legendre k).hasDerivAt t)
      ((Polynomial.continuous _).intervalIntegrable _ _)
      ((Polynomial.continuous _).intervalIntegrable _ _)
    rw [horth j k hjk.le, sub_zero, legendre_eval_one, legendre_eval_one, legendre_eval_neg_one,
      legendre_eval_neg_one] at hibp
    rw [intervalIntegral.integral_congr (fun t _ => mul_comm ((derivative (legendre k)).eval t) _),
      hibp, pow_add]
    ring
  · exact horth k j (not_lt.mp hjk)

/-- For $k, j \in \mathbb{N}$, the $j$-th Legendre coefficient of $L_k'$ satisfies
$|\widehat{(L_k')}_j| \le 2j + 1$. -/
theorem abs_legendreCoeff_derivative_legendre_le (k j : ℕ) :
    |legendreCoeff (derivative (legendre k)) j| ≤ 2 * j + 1 := by
  rw [legendreCoeff, integral_derivative_legendre_mul_legendre, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 * j + 1) / 2)]
  have hb : |(if j < k then (1 : ℝ) - (-1) ^ (k + j) else 0)| ≤ 2 := by
    split_ifs
    · rcases neg_one_pow_eq_or ℝ (k + j) with h | h <;> rw [h] <;> norm_num
    · simp
  calc (2 * (j : ℝ) + 1) / 2 * |if j < k then (1 : ℝ) - (-1) ^ (k + j) else 0|
      ≤ (2 * (j : ℝ) + 1) / 2 * 2 := by gcongr
    _ = 2 * j + 1 := by ring

/-! ### The $L^2$ Markov inequality -/

/-- If a real polynomial $p$ has degree at most $N$, then for every $j \in \mathbb{N}$ the Legendre
coefficients of $p'$ satisfy
$$|\widehat{(p')}_j| \le (2j + 1) \sum_{k = 0}^{N} |\hat p_k|.$$

The proof writes $p' = \sum_k \hat p_k L_k'$ and uses $|\widehat{(L_k')}_j| \le 2j + 1$
(`Polynomial.abs_legendreCoeff_derivative_legendre_le`). -/
theorem abs_legendreCoeff_derivative_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) (j : ℕ) :
    |legendreCoeff (derivative p) j| ≤
      (2 * j + 1) * ∑ k ∈ Finset.range (N + 1), |legendreCoeff p k| := by
  have hder : derivative p = ∑ k ∈ Finset.range (N + 1),
      C (legendreCoeff p k) * derivative (legendre k) := by
    conv_lhs => rw [eq_sum_legendreCoeff hp]
    rw [derivative_sum]
    exact Finset.sum_congr rfl fun k _ => derivative_C_mul _ _
  rw [hder, legendreCoeff_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [legendreCoeff_C_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_legendreCoeff_derivative_legendre_le k j) (abs_nonneg _)

/-- For every $N \in \mathbb{N}$, $\sum_{k = 0}^{N} (2k + 1) = (N + 1)^2$ in $\mathbb{R}$. -/
theorem sum_range_two_mul_add_one (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (2 * (k : ℝ) + 1) = ((N : ℝ) + 1) ^ 2 := by
  induction N with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **Cauchy–Schwarz inequality for the Legendre coefficients**: if a real polynomial $p$ has degree
at most $N$, then
$$\Bigl(\sum_{k = 0}^{N} |\hat p_k|\Bigr)^2 \le \frac{(N + 1)^2}{2} \int_{-1}^1 p(t)^2 \, dt.$$

The proof writes $|\hat p_k| = \sqrt{(2k + 1)/2} \cdot \sqrt{\hat p_k^2 \cdot 2/(2k + 1)}$ and
applies Parseval's identity `Polynomial.integral_sq_eq_sum_legendreCoeff`. -/
theorem sq_sum_abs_legendreCoeff_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    (∑ k ∈ Finset.range (N + 1), |legendreCoeff p k|) ^ 2 ≤
      ((N : ℝ) + 1) ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range (N + 1))
    (r := fun k => |legendreCoeff p k|) (f := fun k => (2 * (k : ℝ) + 1) / 2)
    (g := fun k => legendreCoeff p k ^ 2 * (2 / (2 * k + 1)))
    (fun k _ => by positivity) (fun k _ => by positivity)
    (fun k _ => le_of_eq (by
      have h2k : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
      rw [sq_abs]
      field_simp))
  rw [integral_sq_eq_sum_legendreCoeff hp]
  refine hcs.trans (le_of_eq ?_)
  rw [← Finset.sum_div, sum_range_two_mul_add_one]

/-- The **$L^2$ Markov inequality on $[-1, 1]$**: if a real polynomial $p$ has degree at most $N$,
then
$$\int_{-1}^1 p'(t)^2 \, dt \le (N (N + 1))^2 \int_{-1}^1 p(t)^2 \, dt,$$
that is, $\|p'\|_{L^2(-1,1)} \le N (N + 1) \|p\|_{L^2(-1,1)}$. The constant is not sharp, but
the sharp constant has the same order $N^2$
(`Polynomial.integral_derivative_derivative_legendre_sq_ge`).

This inequality is behind the growth $O(N^4)$ of the eigenvalues of the spectral stiffness
matrix in [quarteroni2000numerical], §13.3.1; see also Canuto, Hussaini, Quarteroni and Zang,
*Spectral Methods in Fluid Dynamics*, §9.4. The proof expands $p = \sum_{k \le N} \hat p_k L_k$.
Then $p'$ has degree less than $N$ and its Legendre coefficients satisfy $|\widehat{(p')}_j| \le
(2j + 1) \sum_k |\hat p_k|$ (`Polynomial.abs_legendreCoeff_derivative_le`). Parseval's identity
gives $\int (p')^2 = \sum_{j < N} \widehat{(p')}_j^2 \cdot 2/(2j + 1) \le 2 (\sum_{j < N} (2j +
1)) (\sum_k |\hat p_k|)^2$. The Cauchy–Schwarz inequality $(\sum_k |\hat p_k|)^2 \le ((N +
1)^2/2) \int p^2$ and $\sum_{j < N} (2j + 1) = N^2$ finish the proof. -/
theorem integral_derivative_sq_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    ∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2 ≤
      ((N : ℝ) * (N + 1)) ^ 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by
  have hpN : (0 : ℝ) ≤ ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · -- a constant has zero derivative
    have hc : derivative p = 0 := by
      rw [eq_C_of_natDegree_le_zero hp, derivative_C]
    rw [hc]
    simp only [eval_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      intervalIntegral.integral_zero]
    positivity
  have hderdeg : (derivative p).natDegree ≤ N - 1 :=
    (natDegree_derivative_le p).trans (Nat.sub_le_sub_right hp 1)
  set S := ∑ k ∈ Finset.range (N + 1), |legendreCoeff p k| with hS
  have hSsq := sq_sum_abs_legendreCoeff_le hp
  rw [← hS] at hSsq
  -- Parseval for `p'`, term by term
  rw [integral_sq_eq_sum_legendreCoeff hderdeg]
  have hterm : ∀ j ∈ Finset.range (N - 1 + 1),
      legendreCoeff (derivative p) j ^ 2 * (2 / (2 * (j : ℝ) + 1)) ≤
        2 * (2 * (j : ℝ) + 1) * S ^ 2 := by
    intro j _
    have h := abs_legendreCoeff_derivative_le hp j
    rw [← hS] at h
    have h2 : legendreCoeff (derivative p) j ^ 2 ≤ ((2 * (j : ℝ) + 1) * S) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc legendreCoeff (derivative p) j ^ 2 * (2 / (2 * (j : ℝ) + 1))
        ≤ ((2 * (j : ℝ) + 1) * S) ^ 2 * (2 / (2 * (j : ℝ) + 1)) := by gcongr
      _ = 2 * (2 * (j : ℝ) + 1) * S ^ 2 := by field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  -- `∑_{j < N} (2j + 1) = N²`
  have hsum : ∑ j ∈ Finset.range (N - 1 + 1), (2 * (j : ℝ) + 1) ≤ (N : ℝ) ^ 2 := by
    rw [sum_range_two_mul_add_one, Nat.cast_sub hNpos]
    push_cast
    ring_nf
    exact le_rfl
  calc 2 * (∑ j ∈ Finset.range (N - 1 + 1), (2 * (j : ℝ) + 1)) * S ^ 2
      ≤ 2 * (N : ℝ) ^ 2 * (((N : ℝ) + 1) ^ 2 / 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2) := by
        gcongr
    _ = ((N : ℝ) * (N + 1)) ^ 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2 := by ring

/-- The **$L^2$ Markov inequality in norm form**: if a real polynomial $p$ has degree at most $N$,
then
$$\Bigl(\int_{-1}^1 p'(t)^2 \, dt\Bigr)^{1/2} \le N (N + 1) \Bigl(\int_{-1}^1 p(t)^2 \,
  dt\Bigr)^{1/2}.$$
-/
theorem sqrt_integral_derivative_sq_le {N : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ N) :
    Real.sqrt (∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2) ≤
      (N : ℝ) * (N + 1) * Real.sqrt (∫ t in (-1 : ℝ)..1, p.eval t ^ 2) := by
  have h := integral_derivative_sq_le hp
  calc Real.sqrt (∫ t in (-1 : ℝ)..1, (derivative p).eval t ^ 2)
      ≤ Real.sqrt (((N : ℝ) * (N + 1)) ^ 2 * ∫ t in (-1 : ℝ)..1, p.eval t ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = (N : ℝ) * (N + 1) * Real.sqrt (∫ t in (-1 : ℝ)..1, p.eval t ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

end Polynomial

namespace Polynomial

/-! ### Sharpness: the test polynomial $L_N'$ -/

/-- For every $n \in \mathbb{N}$, $\int_{-1}^1 L_n(t) L_n''(t) \, dt = 0$, because $L_n''$ has
degree less than $n$. -/
theorem integral_legendre_mul_derivative_derivative (n : ℕ) :
    ∫ t in (-1 : ℝ)..1,
      (legendre n).eval t * (derivative (derivative (legendre n))).eval t = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [legendre_zero]
  have hdeg : (derivative (derivative (legendre n))).degree < n := by
    refine (degree_le_of_natDegree_le ((natDegree_derivative_le _).trans
      (Nat.sub_le_sub_right (natDegree_derivative_le _) 1))).trans_lt ?_
    rw [natDegree_legendre]
    exact_mod_cast (by omega : n - 1 - 1 < n)
  have h := OrthogonalPolynomial.integral_legendre_mul_of_degree_lt hdeg
  rwa [OrthogonalPolynomial.integral_legendreMeasure] at h

/-- For every $n \in \mathbb{N}$,
$$\|L_n'\|^2_{L^2(-1,1)} = \int_{-1}^1 L_n'(t)^2 \, dt = n(n + 1).$$

Integration by parts gives $\int (L_n')^2 = [L_n' L_n]_{-1}^1 - \int L_n'' L_n$. The last
integral vanishes by orthogonality, and $L_n'(\pm 1) L_n(\pm 1) = \pm n(n + 1)/2$. -/
theorem integral_derivative_legendre_sq (n : ℕ) :
    ∫ t in (-1 : ℝ)..1, (derivative (legendre n)).eval t ^ 2 = (n : ℝ) * (n + 1) := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t => (derivative (legendre n)).eval t)
    (u' := fun t => (derivative (derivative (legendre n))).eval t)
    (v := fun t => (legendre n).eval t) (v' := fun t => (derivative (legendre n)).eval t)
    (a := (-1 : ℝ)) (b := 1) (fun t _ => (derivative (legendre n)).hasDerivAt t)
    (fun t _ => (legendre n).hasDerivAt t)
    ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)
  have horth : ∫ t in (-1 : ℝ)..1,
      (derivative (derivative (legendre n))).eval t * (legendre n).eval t = 0 := by
    rw [← integral_legendre_mul_derivative_derivative n]
    exact intervalIntegral.integral_congr fun t _ => mul_comm _ _
  rw [horth, sub_zero, eval_one_derivative_legendre, eval_neg_one_derivative_legendre,
    legendre_eval_one, legendre_eval_neg_one] at hibp
  rw [intervalIntegral.integral_congr (fun t _ => sq ((derivative (legendre n)).eval t)), hibp,
    pow_succ]
  have h1 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  linear_combination ((n : ℝ) * (n + 1) / 2) * h1

/-- For every $n \in \mathbb{N}$,
$$\int_{-1}^1 t \, L_n'(t) \, L_n''(t) \, dt = \Bigl(\frac{n(n + 1)}{2}\Bigr)^2 - \frac{n(n +
  1)}{2}.$$

The proof uses $(x (L_n')^2)' = (L_n')^2 + 2x L_n' L_n''$, so that $2 \int x L_n' L_n'' =
L_n'(1)^2 + L_n'(-1)^2 - \|L_n'\|^2$. -/
theorem integral_X_mul_derivative_legendre_mul_derivative_derivative (n : ℕ) :
    ∫ t in (-1 : ℝ)..1, t * (derivative (legendre n)).eval t *
        (derivative (derivative (legendre n))).eval t =
      ((n : ℝ) * (n + 1) / 2) ^ 2 - (n : ℝ) * (n + 1) / 2 := by
  set L' := fun t => (derivative (legendre n)).eval t with hL'
  set L'' := fun t => (derivative (derivative (legendre n))).eval t with hL''
  have hderiv : ∀ t, HasDerivAt (fun t => t * L' t ^ 2) (L' t ^ 2 + 2 * t * L' t * L'' t) t := by
    intro t
    have h1 : HasDerivAt (fun t => L' t ^ 2) (2 * L' t * L'' t) t := by
      have := ((derivative (legendre n)).hasDerivAt t).fun_pow 2
      simpa [hL', hL'', mul_comm, mul_assoc, mul_left_comm] using this
    have := (hasDerivAt_id t).fun_mul h1
    simpa [id, mul_comm, mul_assoc, mul_left_comm] using this
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := 1)
    (fun t _ => hderiv t) (by
      have : Continuous fun t => L' t ^ 2 + 2 * t * L' t * L'' t := by
        simp only [hL', hL'']; fun_prop
      exact this.intervalIntegrable _ _)
  have hsq := integral_derivative_legendre_sq n
  have hsplit : ∫ t in (-1 : ℝ)..1, (L' t ^ 2 + 2 * t * L' t * L'' t) =
      (∫ t in (-1 : ℝ)..1, L' t ^ 2) + 2 * ∫ t in (-1 : ℝ)..1, t * L' t * L'' t := by
    rw [intervalIntegral.integral_add, ← intervalIntegral.integral_const_mul]
    · exact congrArg _ (intervalIntegral.integral_congr fun t _ => by ring)
    · exact ((Polynomial.continuous _).pow 2).intervalIntegrable _ _
    · have : Continuous fun t => 2 * t * L' t * L'' t := by simp only [hL', hL'']; fun_prop
      exact this.intervalIntegrable _ _
  simp only [hL', hL''] at hsplit hsq
  rw [hsplit, hsq] at hftc
  simp only [hL', eval_one_derivative_legendre, eval_neg_one_derivative_legendre] at hftc
  have hpow : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  have : ∫ t in (-1 : ℝ)..1, t * (derivative (legendre n)).eval t *
      (derivative (derivative (legendre n))).eval t =
      (((n : ℝ) * (n + 1) / 2) ^ 2 + (-1 * ((-1) ^ (n + 1) * ((n : ℝ) * (n + 1) / 2)) ^ 2 * (-1))
        - (n : ℝ) * (n + 1)) / 2 := by
    linarith
  rw [this, mul_pow, hpow]
  ring

/-- The **$L^2$ Markov inequality is sharp up to a constant**: for $N \ge 2$, the test polynomial
$L_N'$, of degree $N - 1$, satisfies
$$\frac{(N (N + 1))^2}{36} \int_{-1}^1 L_N'(t)^2 \, dt \le \int_{-1}^1 L_N''(t)^2 \, dt.$$
Hence the growth $N^2$ of the constant in `Polynomial.integral_derivative_sq_le` cannot be
improved.

Let $m = N(N + 1) \ge 6$. The Cauchy–Schwarz inequality against $x L_N'$ gives $(\int x L_N'
L_N'')^2 \le \|x L_N'\|^2 \|L_N''\|^2 \le \|L_N'\|^2 \|L_N''\|^2$, with
$\int x L_N' L_N'' = m(m - 2)/4 \ge m^2/6$ and $\|L_N'\|^2 = m$. -/
theorem integral_derivative_derivative_legendre_sq_ge {N : ℕ} (hN : 2 ≤ N) :
    ((N : ℝ) * (N + 1)) ^ 2 / 36 * ∫ t in (-1 : ℝ)..1, (derivative (legendre N)).eval t ^ 2 ≤
      ∫ t in (-1 : ℝ)..1, (derivative (derivative (legendre N))).eval t ^ 2 := by
  set m : ℝ := (N : ℝ) * (N + 1) with hm
  have hm6 : 6 ≤ m := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    rw [hm]; nlinarith
  have hcs := intervalIntegral.sq_integral_mul_le_of_continuousOn (a := (-1 : ℝ)) (b := 1)
    (f := fun t => t * (derivative (legendre N)).eval t)
    (g := fun t => (derivative (derivative (legendre N))).eval t) (by norm_num)
    (continuous_id.mul (Polynomial.continuous _)).continuousOn
    (Polynomial.continuous _).continuousOn
  rw [integral_X_mul_derivative_legendre_mul_derivative_derivative, ← hm] at hcs
  -- `∫ (x L_N')² ≤ ∫ (L_N')²`
  have hxle : (∫ t in (-1 : ℝ)..1, (t * (derivative (legendre N)).eval t) ^ 2) ≤
      ∫ t in (-1 : ℝ)..1, (derivative (legendre N)).eval t ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_id.mul (Polynomial.continuous _)).pow 2 |>.intervalIntegrable _ _)
      (((Polynomial.continuous _).pow 2).intervalIntegrable _ _) fun t ht => ?_
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg _) ht2
  rw [integral_derivative_legendre_sq, ← hm] at hxle
  set E := ∫ t in (-1 : ℝ)..1, (derivative (derivative (legendre N))).eval t ^ 2 with hE
  have hE0 : 0 ≤ E := intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
  rw [integral_derivative_legendre_sq, ← hm]
  -- `(m²/4 - m/2)² ≤ m E`, and `m²/4 - m/2 ≥ m²/6`
  have hD : m ^ 2 / 6 ≤ (m / 2) ^ 2 - m / 2 := by nlinarith
  have hD2 : (m ^ 2 / 6) ^ 2 ≤ ((m / 2) ^ 2 - m / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hD 2
  have hkey : (m ^ 2 / 6) ^ 2 ≤ m * E :=
    hD2.trans (hcs.trans (mul_le_mul_of_nonneg_right hxle hE0))
  nlinarith [hkey]

end Polynomial
