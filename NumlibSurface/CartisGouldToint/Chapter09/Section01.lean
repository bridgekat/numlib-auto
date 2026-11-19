/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Cartis, Gould and Toint, Section 9.1: Matrix factorization

This module formalizes Section 9.1 of [cartis2022evaluation]. Let $H$ be symmetric, $M$ symmetric
positive definite, and let $\lambda$ be such that $H + \lambda M$ is positive definite with a
factorization $H + \lambda M = L D L^T$ (9.1.1), $D$ diagonal. Algorithm 9.1.1 computes the secular
function $\pi(\lambda) = \|s(\lambda)\|_M^2$ and its derivatives $\pi^{(j)}(\lambda)$ by solves with
$L$, $D$ and $L^T$. Corollary 9.1.1 shows that the output is correct, by Theorem 8.2.6. The proof
rests on the derivative vectors of `CartisGouldToint.Chapter08.secularDerivVec`.

## Main definitions

* Algorithm 9.1.1, `CartisGouldToint.Chapter09.algorithm_9_1_1`: the output
  $j \mapsto \pi^{(j)}(\lambda)$, computed from the vectors `CartisGouldToint.Chapter09.algS`,
  `CartisGouldToint.Chapter09.algY` and `CartisGouldToint.Chapter09.algZ`.

## Main results

* Algorithm 9.1.1, `CartisGouldToint.Chapter09.algS_eq`: the vectors of the algorithm are
  $(-1)^k s^{(k)}(\lambda)$, with $s^{(k)}$ of (8.2.29).
* Corollary 9.1.1, `CartisGouldToint.Chapter09.corollary_9_1_1`: Algorithm 9.1.1 computes
  $\pi^{(j)}(\lambda)$ for every $j$.

## Implementation notes

* The algorithm is deterministic, so it is a function `CartisGouldToint.Chapter09.algorithm_9_1_1 L
  D M g : ℕ → ℝ` and not a run predicate.
* Solves with $L$, $D$ and $L^T$ are written with the matrix inverses, which are $0$ for a singular
  matrix.

## Deviations from the source

* **Algorithm 9.1.1** (typo). The right-hand side $(k + 1) M s^{(k)}$ has the sign opposite to
  (8.2.29), so the vectors of the algorithm are $(-1)^k s^{(k)}$; the values $\pi^{(j)}$ are not
  affected. See `CartisGouldToint.Chapter09.algS_eq`.
* **Algorithm 9.1.1, loop bound** (correction). The inclusive bound
  $k \le \lceil l_{\max}/2 \rceil$ attempts an extra odd derivative. For odd $l_{\max}$,
  its input vector has not been computed by the conditional solve. The formal sequence
  defines each derivative by its order and can be read through $l_{\max}$.
  See `CartisGouldToint.Chapter09.algorithm_9_1_1`.
* **Remark after Algorithm 9.1.1, Cholesky factorization** (typo). The odd derivatives are
  $\pi^{(2k+1)} = -\beta_k \|y^{(k+1)}\|^2$, not $-2\beta_k \|y^{(k+1)}\|^2$. See
  `CartisGouldToint.Chapter09.corollary_9_1_1`.
-/

open Matrix
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter09

open CartisGouldToint.Chapter08

variable {n : ℕ}

/-- **Algorithm 9.1.1** of [cartis2022evaluation], the vectors $s^{(k)}$. Let
$L, D, M \in \mathbb{R}^{n \times n}$ and $g \in \mathbb{R}^n$. The vector $s^{(0)}$ is obtained
by solving $L y = -g$, $D z = y$ and $L^T s^{(0)} = z$, and $s^{(k+1)}$ is obtained by solving
$L y = (k + 1) M s^{(k)}$, $D z = y$ and $L^T s^{(k+1)} = z$.

The solves are written with the matrix inverses, which are $0$ for a singular matrix.

**Reading.** Implements the positive recurrence of the pseudocode; these are signed derivatives
relative to (8.2.29), and inverses totalize singular factors.
-/
noncomputable def algS (L D M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => toEuclideanLin Lᵀ⁻¹ (toEuclideanLin D⁻¹ (toEuclideanLin L⁻¹ (-g)))
  | k + 1 => toEuclideanLin Lᵀ⁻¹ (toEuclideanLin D⁻¹
      (toEuclideanLin L⁻¹ ((k + 1 : ℝ) • toEuclideanLin M (algS L D M g k))))

/-- The vectors $y^{(k+1)} = L^{-1} \bigl((k + 1) M s^{(k)}\bigr)$ of Algorithm 9.1.1 of
[cartis2022evaluation]. The index `k` gives $y^{(k+1)}$. -/
noncomputable def algY (L D M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin L⁻¹ ((k + 1 : ℝ) • toEuclideanLin M (algS L D M g k))

/-- The vectors $z^{(k+1)} = D^{-1} y^{(k+1)}$ of Algorithm 9.1.1 of [cartis2022evaluation]. The
index `k` gives $z^{(k+1)}$. -/
noncomputable def algZ (L D M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  toEuclideanLin D⁻¹ (algY L D M g k)

/-- The coefficients $\beta_k = 2\alpha_k/(k + 1)$ of Algorithm 9.1.1 of [cartis2022evaluation],
where $\alpha_k$ are the coefficients (8.2.30) (`CartisGouldToint.Chapter08.alphaCoeff`). -/
noncomputable def algBeta (k : ℕ) : ℝ := 2 * alphaCoeff k / (k + 1)

/-- The coefficients satisfy $\alpha_{k+1} = (2k + 3) \beta_k$. -/
theorem alphaCoeff_succ_eq (k : ℕ) : alphaCoeff (k + 1) = (2 * k + 3) * algBeta k := by
  rw [alphaCoeff, algBeta]; ring

/-- **Algorithm 9.1.1** of [cartis2022evaluation]. The algorithm takes $\lambda \in \mathcal{F}$ and
a factorization $H + \lambda M = L D L^T$, and finds $\pi(\lambda)$ and its derivatives. Its
output is the sequence $j \mapsto \pi^{(j)}(\lambda)$ with
$$\pi^{(0)} = \langle s^{(0)}, M s^{(0)} \rangle, \qquad \pi^{(2k+1)} = -\beta_k \langle
  y^{(k+1)}, z^{(k+1)} \rangle, \qquad \pi^{(2k+2)} = \alpha_{k+1} \langle s^{(k+1)}, M
  s^{(k+1)} \rangle,$$
where $s^{(k)}$, $y^{(k+1)}$ and $z^{(k+1)}$ are the vectors of the algorithm, $\alpha_k$ are
the coefficients (8.2.30), and $\beta_k = 2\alpha_k/(k + 1)$.

**Typo.** The right-hand side $L y^{(k+1)} = (k + 1) M s^{(k)}$ of the algorithm has the sign
opposite to (8.2.29). So the vectors of the algorithm are $(-1)^k s^{(k)}$
(`CartisGouldToint.Chapter09.algS_eq`). The computed values $\pi^{(j)}$ are not affected.

The three cases are `CartisGouldToint.Chapter09.algorithm_9_1_1_zero`,
`CartisGouldToint.Chapter09.algorithm_9_1_1_odd` and
`CartisGouldToint.Chapter09.algorithm_9_1_1_even`.

**Correction.** The printed loop includes $k=\lceil l_{\max}/2\rceil$, computing an odd
derivative beyond $l_{\max}$. For instance, with $l_{\max}=1$, iteration $k=0$ skips
$s^{(1)}$, which iteration $k=1$ then uses. The formal output is defined for every $j$ by
recursion, and orders $j\le l_{\max}$ give the requested prefix. -/
noncomputable def algorithm_9_1_1 (L D M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) : ℕ → ℝ
  | 0 => ⟪algS L D M g 0, toEuclideanLin M (algS L D M g 0)⟫
  | j + 1 =>
    if Even j then -algBeta (j / 2) * ⟪algY L D M g (j / 2), algZ L D M g (j / 2)⟫
    else alphaCoeff (j / 2 + 1) *
      ⟪algS L D M g (j / 2 + 1), toEuclideanLin M (algS L D M g (j / 2 + 1))⟫

variable {L D M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

/-- The output of Algorithm 9.1.1 at $j = 0$ is $\langle s^{(0)}, M s^{(0)} \rangle$. -/
theorem algorithm_9_1_1_zero :
    algorithm_9_1_1 L D M g 0 = ⟪algS L D M g 0, toEuclideanLin M (algS L D M g 0)⟫ := rfl

/-- The output of Algorithm 9.1.1 at $j = 2k + 1$ is
$-\beta_k \langle y^{(k+1)}, z^{(k+1)} \rangle$. -/
theorem algorithm_9_1_1_odd (k : ℕ) :
    algorithm_9_1_1 L D M g (2 * k + 1) = -algBeta k * ⟪algY L D M g k, algZ L D M g k⟫ := by
  rw [algorithm_9_1_1, ite_eq_left (even_two_mul k), Nat.mul_div_cancel_left k two_pos]

/-- The output of Algorithm 9.1.1 at $j = 2k + 2$ is $\alpha_{k+1} \langle s^{(k+1)}, M s^{(k+1)}
\rangle$. -/
theorem algorithm_9_1_1_even (k : ℕ) :
    algorithm_9_1_1 L D M g (2 * k + 2) =
      alphaCoeff (k + 1) * ⟪algS L D M g (k + 1), toEuclideanLin M (algS L D M g (k + 1))⟫ := by
  have h1 : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from rfl, algorithm_9_1_1, ite_eq_right h1, h2]

/-- Let $H + \lambda M = L D L^T$ with $D$ diagonal. Then for every $x$,
$$(H + \lambda M)^{-1} x = L^{-T} \bigl(D^{-1} (L^{-1} x)\bigr),$$
so the solves of Algorithm 9.1.1 compute $(H + \lambda M)^{-1}$. All inverses are the matrix
inverses of Mathlib, which are $0$ for a singular matrix. -/
theorem toEuclideanLin_inv_of_ldl {H : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ} {d : Fin n → ℝ}
    (hfac : H + lam • M = L * diagonal d * Lᵀ) (x : EuclideanSpace ℝ (Fin n)) :
    toEuclideanLin (H + lam • M)⁻¹ x =
      toEuclideanLin Lᵀ⁻¹ (toEuclideanLin (diagonal d)⁻¹ (toEuclideanLin L⁻¹ x)) := by
  rw [hfac, Matrix.mul_inv_rev, Matrix.mul_inv_rev, toEuclideanLin_mul_apply,
    toEuclideanLin_mul_apply]

/-- **Algorithm 9.1.1** of [cartis2022evaluation], the vectors of the algorithm. Let
$H + \lambda M = L D L^T$ with $D$ diagonal. Then for every $k$, the vector $s^{(k)}$ of
Algorithm 9.1.1 is
$$s^{(k)}_{\mathrm{alg}} = (-1)^k s^{(k)}(\lambda),$$
where $s^{(k)}(\lambda)$ are the derivative vectors (8.2.29) of Theorem 8.2.6.

**Typo.** The algorithm solves $L y^{(k+1)} = (k + 1) M s^{(k)}$, while (8.2.29) has
$-(k + 1) M s^{(k)}$. This theorem records the resulting sign.

The derivative vectors are `CartisGouldToint.Chapter08.secularDerivVec`. -/
theorem algS_eq {H : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ} {d : Fin n → ℝ}
    (hfac : H + lam • M = L * diagonal d * Lᵀ) (k : ℕ) :
    algS L (diagonal d) M g k = (-1 : ℝ) ^ k • secularDerivVec g H M lam k := by
  induction k with
  | zero =>
    rw [algS, secularDerivVec_zero, stepOf_def, toEuclideanLin_inv_of_ldl hfac, pow_zero, one_smul]
  | succ k ih =>
    rw [algS, secularDerivVec_succ, toEuclideanLin_inv_of_ldl hfac, ih]
    simp only [map_smul, map_neg]
    module

/-- **Corollary 9.1.1** of [cartis2022evaluation] (derivatives of the secular function via $LDL^T$
factors). Let $H$ be symmetric, $M$ symmetric positive definite, and let $\lambda$ be such that
$H + \lambda M$ is positive definite with $H + \lambda M = L D L^T$, $D$ diagonal. Then:

* Algorithm 9.1.1 computes the derivatives of $\pi$: its output at $j$ is $\pi^{(j)}(\lambda)$,
  for every $j$;
* the vectors of the algorithm are $(-1)^k s^{(k)}(\lambda)$, with $s^{(k)}$ of (8.2.29);
* the odd derivatives are also $\pi^{(2k+1)}(\lambda) = 2\alpha_k \langle s^{(k)}(\lambda), M
  s^{(k+1)}(\lambda) \rangle$, as in Theorem 8.2.6;
* for a Cholesky factorization ($D = I$), $\pi^{(2k+1)}(\lambda) = -\beta_k
  \|y^{(k+1)}(\lambda)\|^2$.

**Typo.** For a Cholesky factorization the source prints
$\pi^{(2k+1)} = -2\beta_k \|y^{(k+1)}\|^2$. The factor $2$ is spurious.

**Typo.** The vectors of Algorithm 9.1.1 differ from those of (8.2.29) by the sign $(-1)^k$
(`CartisGouldToint.Chapter09.algS_eq`). The alternative expression for the odd derivatives holds
with the vectors of Theorem 8.2.6. The appendix proof identifies the two vector recurrences
without accounting for the alternating signs.

The derivatives are `iteratedDeriv` of `CartisGouldToint.Chapter08.secularFn`, the derivative
vectors are `CartisGouldToint.Chapter08.secularDerivVec`, and $D$ is `diagonal d`. -/
theorem corollary_9_1_1 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) (hM : M.PosDef)
    {lam : ℝ} (hpd : (H + lam • M).PosDef) {d : Fin n → ℝ}
    (hfac : H + lam • M = L * diagonal d * Lᵀ) :
    (∀ j, algorithm_9_1_1 L (diagonal d) M g j = iteratedDeriv j (secularFn g H M) lam) ∧
    (∀ k, algS L (diagonal d) M g k = (-1 : ℝ) ^ k • secularDerivVec g H M lam k) ∧
    (∀ k, iteratedDeriv (2 * k + 1) (secularFn g H M) lam = 2 * alphaCoeff k *
        ⟪secularDerivVec g H M lam k, toEuclideanLin M (secularDerivVec g H M lam (k + 1))⟫) ∧
    (d = 1 → ∀ k, iteratedDeriv (2 * k + 1) (secularFn g H M) lam =
        -algBeta k * ‖algY L (diagonal d) M g k‖ ^ 2) := by
  have hMs := isSymmetric_toEuclideanLin_iff.2 hM.isHermitian
  have hS := algS_eq (g := g) hfac
  -- the odd outputs
  have hodd : ∀ k, algorithm_9_1_1 L (diagonal d) M g (2 * k + 1) =
      iteratedDeriv (2 * k + 1) (secularFn g H M) lam := by
    intro k
    have hyz : ⟪algY L (diagonal d) M g k, algZ L (diagonal d) M g k⟫ =
        (k + 1 : ℝ) * ⟪toEuclideanLin M (algS L (diagonal d) M g k),
          algS L (diagonal d) M g (k + 1)⟫ := by
      rw [algZ, algY, ← toEuclideanLin_transpose_inner_right, transpose_nonsing_inv, algS,
        inner_smul_left, RCLike.conj_to_real]
    rw [algorithm_9_1_1_odd, hyz, (theorem_8_2_6 hH hM hpd k).1, hS, hS]
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    rw [← hMs, algBeta, pow_succ]
    generalize ⟪toEuclideanLin M (secularDerivVec g H M lam k),
      secularDerivVec g H M lam (k + 1)⟫ = I
    have h1 : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    have hk : (k : ℝ) + 1 ≠ 0 := by positivity
    rw [show (-1 : ℝ) ^ k * -1 * ((-1) ^ k * I) = -I * ((-1) ^ k) ^ 2 by ring, h1]
    field_simp
  have heven : ∀ k, algorithm_9_1_1 L (diagonal d) M g (2 * k + 2) =
      iteratedDeriv (2 * k + 2) (secularFn g H M) lam := by
    intro k
    rw [algorithm_9_1_1_even, (theorem_8_2_6 hH hM hpd k).2, hS]
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    generalize ⟪secularDerivVec g H M lam (k + 1),
      toEuclideanLin M (secularDerivVec g H M lam (k + 1))⟫ = I
    have h2 : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [show (-1 : ℝ) ^ (k + 1) * ((-1) ^ (k + 1) * I) = I * ((-1) ^ (k + 1)) ^ 2 by ring, h2,
      mul_one]
  refine ⟨fun j => ?_, hS, fun k => (theorem_8_2_6 hH hM hpd k).1, fun hd k => ?_⟩
  · obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · rcases k with _ | k
      · rw [algorithm_9_1_1_zero, iteratedDeriv_zero, hS, pow_zero, one_smul, secularDerivVec,
          secularFn_def]
      · rw [show 2 * (k + 1) = 2 * k + 2 by ring]; exact heven k
    · exact hodd k
  · have h1 : diagonal (1 : Fin n → ℝ) = 1 := diagonal_one
    rw [← hodd, algorithm_9_1_1_odd, algZ, hd, h1, inv_one, toEuclideanLin_one_apply,
      real_inner_self_eq_norm_sq]

end CartisGouldToint.Chapter09
