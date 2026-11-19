/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Direct.Levinson
import Numlib.Eigen.DivideConquer
import Numlib.FloatingPoint.Program

/-!
# Golub and Van Loan, Section 4.7: Classical methods for Toeplitz systems

This module formalizes §4.7 of [golub2013matrix], the solution of linear systems with a symmetric
positive definite Toeplitz matrix $T_n = (r_{|i-j|}) \in \mathbb{R}^{n \times n}$ with $r_0 = 1$.
Such a matrix is persymmetric, $\mathcal{E}_n T_n \mathcal{E}_n = T_n^T$ for the exchange
permutation $\mathcal{E}_n$, and the inverse of a nonsingular Toeplitz matrix is persymmetric
(§4.7.1). Durbin's algorithm solves the Yule–Walker systems $T_k y^{(k)} = -(r_1, \dots, r_k)^T$ for
$k = 1, \dots, n$ by bordering: $y^{(k+1)} = (y^{(k)} + \alpha_k \mathcal{E}_k y^{(k)}, \alpha_k)$,
with a reflection coefficient $\alpha_k$ and a denominator $\beta_k = 1 + r^T y^{(k)} > 0$ ((4.7.1),
Algorithm 4.7.1). Levinson's algorithm solves $T_n x = b$ for a general $b$ by the same bordering
((4.7.2)–(4.7.3), Algorithm 4.7.2), and Trench's algorithm computes $T_n^{-1}$ from $y^{(n-1)}$ and
the persymmetry of the inverse ((4.7.4)–(4.7.5), Algorithm 4.7.3).

The module also formalizes Cybenko's bounds on $\|T_n^{-1}\|_1$ and $\|y\|_1$ in terms of the
reflection coefficients ((4.7.6)–(4.7.7)), the method of Cybenko and Van Loan for the smallest
eigenvalue of $T_n$ (§4.7.7: the secular function, Newton's method on it, and the bisection (4.7.11)
for a starting value), and the bordering for unsymmetric Toeplitz systems ((4.7.12)–(4.7.13)). The
proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.Toeplitz`,
`Numlib.Direct.Levinson` and `Numlib.Eigen.DivideConquer`.

## Main definitions

* §4.7.1, `GolubVanLoan.Chapter04.IsPersymmetricExchange`: $B$ is persymmetric if
  $\mathcal{E}_n B \mathcal{E}_n = B^T$.
* Algorithm 4.7.1, `GolubVanLoan.Chapter04.algorithm_4_7_1`: Durbin's algorithm, with one pass
  `GolubVanLoan.Chapter04.durbinStep`.
* Algorithm 4.7.2, `GolubVanLoan.Chapter04.algorithm_4_7_2`: Levinson's algorithm.
* Algorithm 4.7.3, `GolubVanLoan.Chapter04.algorithm_4_7_3`: Trench's algorithm.
* §4.7.7, `GolubVanLoan.Chapter04.shiftedToeplitzSeq`: the data of the normalized shifted matrix
  $T_\lambda = (T - \lambda I)/(1 - \lambda)$.
* §4.7.7, `GolubVanLoan.Chapter04.bisectionIndex`: the index $m(\lambda)$ of the first nonpositive
  $\beta_k$ of Durbin's recurrence for $T_\lambda$.
* (4.7.11), `GolubVanLoan.Chapter04.durbinIndex`: the program that computes $m(\lambda)$.
* (4.7.11), `GolubVanLoan.Chapter04.durbinBisection`: the bisection for a starting value of Newton's
  method.

## Main results

* §4.7.1, `GolubVanLoan.Chapter04.isPersymmetric_iff`: the persymmetry of the source is the
  entrywise `Matrix.IsPersymmetric`.
* §4.7.1, `GolubVanLoan.Chapter04.isSymm_exchange_mul`: if $B$ is persymmetric, then
  $\mathcal{E}_n B$ is symmetric.
* §4.7.1, `GolubVanLoan.Chapter04.isPersymmetric_inv`: the inverse of a persymmetric matrix is
  persymmetric.
* §4.7.1, `GolubVanLoan.Chapter04.isPersymmetric_inv_of_isToeplitz`: the inverse of a Toeplitz
  matrix is persymmetric.
* §4.7.3, `GolubVanLoan.Chapter04.durbin_step`: the bordering step from order $k$ to order $k + 1$
  of the Yule–Walker system.
* §4.7.3, `GolubVanLoan.Chapter04.durbin_denominator_pos`: the congruence that makes the denominator
  $1 + r^T y$ positive.
* (4.7.1), `GolubVanLoan.Chapter04.equation_4_7_1`: for positive definite $T_n$, Durbin's recurrence
  solves the Yule–Walker systems of every order, with positive denominators.
* §4.7.3, `GolubVanLoan.Chapter04.durbin_beta_succ`: $\beta_{k+1} = (1 - \alpha_k^2) \beta_k$.
* Algorithm 4.7.1, `GolubVanLoan.Chapter04.algorithm_4_7_1_spec`: the exact run solves
  $T_n y = -(r_1, \dots, r_n)^T$.
* (4.7.2)→(4.7.3), `GolubVanLoan.Chapter04.equation_4_7_3`: the bordering step for a general
  right-hand side.
* Algorithm 4.7.2, `GolubVanLoan.Chapter04.algorithm_4_7_2_spec`: the exact run solves $T_n x = b$.
* (4.7.4), `GolubVanLoan.Chapter04.equation_4_7_4`: the last column and the leading block of
  $T_n^{-1}$ in terms of $y^{(n-1)}$.
* (4.7.5), `GolubVanLoan.Chapter04.equation_4_7_5`: the recursion for the entries of $T_n^{-1}$ that
  Trench's algorithm uses.
* Algorithm 4.7.3, `GolubVanLoan.Chapter04.algorithm_4_7_3_spec`: the exact run computes $T_n^{-1}$
  on the upper wedge $i \le j$, $i + j \le n + 1$.
* §4.7.6, `GolubVanLoan.Chapter04.abs_reflection_lt_one`: for positive definite $T_n$, the
  reflection coefficients satisfy $|\alpha_k| < 1$.
* (4.7.6), `GolubVanLoan.Chapter04.equation_4_7_6_lower` and
  `GolubVanLoan.Chapter04.equation_4_7_6_upper`: Cybenko's lower and upper bounds on
  $\|T_n^{-1}\|_1$.
* (4.7.7), `GolubVanLoan.Chapter04.equation_4_7_7`: if all reflection coefficients are nonnegative,
  then $\|y\|_1 = \prod_k (1 + \alpha_k) - 1$.
* §4.7.7, `GolubVanLoan.Chapter04.secular_lambdaMin`: an eigenvalue of $T$ below the spectrum of $B$
  is a zero of the secular function $f(\lambda) = 1 - \lambda - r^T (B - \lambda I)^{-1} r$.
* §4.7.7, `GolubVanLoan.Chapter04.secular_deriv`: $f'(\lambda) = -1 - \|(B - \lambda I)^{-1} r\|_2^2
  \le -1$ and $f''(\lambda) = -2 r^T (B - \lambda I)^{-3} r \le 0$.
* (4.7.9)–(4.7.10), `GolubVanLoan.Chapter04.equation_4_7_10`: Newton's method on $f$ converges to
  $\lambda_{\min}(T)$ monotonically from the right.
* §4.7.7, `GolubVanLoan.Chapter04.newton_step_eq`: the Newton step through the shifted Yule–Walker
  system.
* §4.7.7, `GolubVanLoan.Chapter04.durbin_beta_pos_iff`: $T(1{:}k{+}1, 1{:}k{+}1)$ is positive
  definite if and only if $\beta_0, \dots, \beta_k > 0$.
* §4.7.7, `GolubVanLoan.Chapter04.bisectionIndex_spec`: $m(\lambda) = n - 1$ if and only if
  $B - \lambda I$ is positive definite and $T - \lambda I$ is not, and $m$ is antitone.
* §4.7.7, `GolubVanLoan.Chapter04.lambdaMin_bracket`: $0 < \lambda_{\min}(T) \le \lambda_{\min}(B)
  \le 1 - |r_1|$, stated through shifted matrices.
* (4.7.11), `GolubVanLoan.Chapter04.durbinIndex_spec`: the exact run of
  `GolubVanLoan.Chapter04.durbinIndex` is $m(\lambda)$.
* (4.7.11), `GolubVanLoan.Chapter04.equation_4_7_11`: the exact bisection keeps its bracket, and on
  exit its value satisfies (4.7.9).
* (4.7.12)→(4.7.13), `GolubVanLoan.Chapter04.equation_4_7_13`: the bordering step for unsymmetric
  Toeplitz systems.

## Conventions

* $T_k$ is `Matrix.symmToeplitz k r` with `r : ℕ → ℝ` and `r 0 = 1`; the source normalizes the
  diagonal to $1$. "$T_n$ is positive definite" is `(Matrix.symmToeplitz n r).PosDef`.
* The exchange permutation $\mathcal{E}_k$ is `Matrix.exchange k`, and the vector
  $r = (r_1, \dots, r_k)$ of the source is `fun i : Fin k => r (i + 1)`, indexed from $0$.
* The vectors $y^{(k)}$ and the scalars $\beta_k$ and $\alpha_k$ of (4.7.1) are the backbone's
  `Durbin.sol r k`, `Durbin.beta r k` and `Durbin.alpha r k`. They are $\mathbb{N}$-indexed, and
  `Durbin.sol r k` is zero from index $k$ on.
* In §4.7.6 the source reuses the letter $\alpha_j$ for Cybenko's reflection coefficient
  $y^{(j)}_j$, $j = 1, \dots, n$. It is `Durbin.alpha r (j - 1)`.

## Implementation notes

* The algorithms follow the algorithm conventions of the library index: every $+$, $-$, $\times$ and
  $/$ passes through the rounding hook `rnd`, negation and copies are exact, and loops are
  `List.foldlM`.
* The growing vectors of Algorithms 4.7.1–4.7.3 are held as $\mathbb{N}$-indexed state, with
  $y(1{:}k)$ in the entries $0, \dots, k - 1$, which is the shape of the backbone recurrences. The
  output is read back on `Fin n`.
* Every scalar update of the form "$c \pm$ inner product" is read literally: in Durbin's and
  Levinson's $\alpha$, Levinson's $\mu$ and Trench's $\gamma$, the inner product is accumulated from
  $0$ by `FloatingPoint.dotAccum` and then combined with $c$ by one rounded $\pm$.
* The bisection (4.7.11) is the program `GolubVanLoan.Chapter04.durbinBisection`. Its `while`
  loop has a bound `fuel` on the number of passes and a flag `done`.
* The program `GolubVanLoan.Chapter04.durbinIndex` computes the index $m(\mu)$ of (4.7.11). It
  runs the passes of Algorithm 4.7.1 (`GolubVanLoan.Chapter04.durbinStep`) on the rounded entries
  of $T_\mu = (T - \mu I)/(1 - \mu)$ and stops at the first nonpositive $\beta$.

## Deviations from the source

* **Generalization.** The persymmetry results include the totalized inverse of a singular matrix.
  See `GolubVanLoan.Chapter04.isPersymmetric_inv`,
  `GolubVanLoan.Chapter04.isPersymmetric_inv_of_isToeplitz`.
* **Generalization.** The Durbin and Levinson bordering identities require only a nonzero
  denominator. See `GolubVanLoan.Chapter04.durbin_step`, `GolubVanLoan.Chapter04.equation_4_7_3`.
* **Reading.** The beta recurrence explicitly assumes the previous denominator is nonzero. See
  `GolubVanLoan.Chapter04.durbin_beta_succ`.
* **Reading.** The rounded Durbin and Levinson programs totalize division at zero pivots. See
  `GolubVanLoan.Chapter04.durbinStep`, `GolubVanLoan.Chapter04.algorithm_4_7_1`,
  `GolubVanLoan.Chapter04.algorithm_4_7_2`.
* **Reading.** The Trench program returns zeros for the uncomputed entries. See
  `GolubVanLoan.Chapter04.algorithm_4_7_3`.
* **Generalization.** The secular identity and Newton convergence also apply to indefinite Toeplitz
  matrices. See `GolubVanLoan.Chapter04.secular_lambdaMin`,
  `GolubVanLoan.Chapter04.equation_4_7_10`.
* **Generalization.** The derivative formulas and shifted Newton step require only symmetry of the
  trailing block. See `GolubVanLoan.Chapter04.secular_deriv`,
  `GolubVanLoan.Chapter04.newton_step_eq`.
* **Generalization.** The definiteness criteria include converses and the bisection index is
  antitone. See `GolubVanLoan.Chapter04.durbin_beta_pos_iff`,
  `GolubVanLoan.Chapter04.bisectionIndex_spec`.
* **Reading.** The normalized Toeplitz data are total at shift one. See
  `GolubVanLoan.Chapter04.shiftedToeplitzSeq`.
* **Reading.** The exact bisection index uses the matrix size when every denominator is positive.
  See `GolubVanLoan.Chapter04.bisectionIndex`, `GolubVanLoan.Chapter04.durbinIndex_spec`.
* **Reading.** The bisection index tests the denominator after the full Durbin step. See
  `GolubVanLoan.Chapter04.durbinIndex`.
* **Scope.** The Toeplitz bisection returns a bracket and an explicit stopping flag. See
  `GolubVanLoan.Chapter04.durbinBisection`.
* **Generalization.** The unsymmetric Toeplitz bordering implication uses cross-multiplied scalar
  equations. See `GolubVanLoan.Chapter04.equation_4_7_13`.
* **The bracket of §4.7.7** (reading). The source writes $\lambda_{\min}(T) < \lambda_{\min}(B)$,
  which is the hypothesis (4.7.8). The theorem proves $\lambda_{\min}(T) \le \lambda_{\min}(B)$
  without it. See `GolubVanLoan.Chapter04.lambdaMin_bracket`.
* **The invariant after (4.7.11)** (correction). The source prints $m(L) \le n - 1 \le m(R)$. Since
  $m$ is antitone, the update rule maintains $m(R) \le n - 1 \le m(L)$ instead. See
  `GolubVanLoan.Chapter04.equation_4_7_11`.

## Not formalized

* **The error approximations of §4.7.6**, stated with $\approx$.
* **The count of $O(\log n)$ Newton steps in §4.7.7.**
* **The lookahead strategy of §4.7.8.**
-/

open Matrix Finset FloatingPoint

namespace GolubVanLoan.Chapter04

variable {n : ℕ}

/-! ### §4.7.1 Persymmetry -/

/-- **Section 4.7.1** of [golub2013matrix], persymmetry. A matrix $B \in \mathbb{R}^{n \times n}$ is
**persymmetric** if
$$\mathcal{E}_n B \mathcal{E}_n = B^T,$$
where $\mathcal{E}_n$ is the exchange permutation matrix `Matrix.exchange n`. -/
def IsPersymmetricExchange (B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  exchange n * B * exchange n = Bᵀ

/-- **Section 4.7.1** of [golub2013matrix], persymmetry entrywise. A matrix
$B \in \mathbb{R}^{n \times n}$ is persymmetric in the sense
$\mathcal{E}_n B \mathcal{E}_n = B^T$ if and only if $b_{n-1-j, n-1-i} = b_{ij}$ for all $i, j$
(indices from $0$), that is, $B$ is symmetric about the antidiagonal.

The entrywise form is the backbone's `Matrix.IsPersymmetric`, with the reversal `Fin.rev`. -/
theorem isPersymmetric_iff {B : Matrix (Fin n) (Fin n) ℝ} :
    IsPersymmetricExchange B ↔ B.IsPersymmetric :=
  isPersymmetric_iff_exchange_mul_mul_exchange.symm

/-- **Section 4.7.1** of [golub2013matrix]. If $B \in \mathbb{R}^{n \times n}$ is persymmetric, then
$\mathcal{E}_n B$ is symmetric. -/
theorem isSymm_exchange_mul {B : Matrix (Fin n) (Fin n) ℝ} (hB : IsPersymmetricExchange B) :
    (exchange n * B).IsSymm :=
  (isPersymmetric_iff.1 hB).isSymm_exchange_mul

/-- **Section 4.7.1** of [golub2013matrix]. If $B \in \mathbb{R}^{n \times n}$ is persymmetric, then
$B^{-1}$ is persymmetric:
$$\mathcal{E}_n B^{-1} \mathcal{E}_n = (\mathcal{E}_n B \mathcal{E}_n)^{-1} = (B^T)^{-1} =
  (B^{-1})^T.$$

The inverse is Mathlib's matrix inverse, which is $0$ for a singular matrix; the statement
therefore holds for singular $B$ as well.

**Generalization.** Lean's matrix inverse is total. The theorem also applies to singular matrices,
whose Lean inverse is zero. The source's inverse requires nonsingularity.
-/
theorem isPersymmetric_inv {B : Matrix (Fin n) (Fin n) ℝ} (hB : IsPersymmetricExchange B) :
    IsPersymmetricExchange B⁻¹ :=
  isPersymmetric_iff.2 (isPersymmetric_iff.1 hB).inv

/-- **Section 4.7.1** of [golub2013matrix]. If $A \in \mathbb{R}^{n \times n}$ is Toeplitz, then
$A^{-1}$ is persymmetric.

The source states this for nonsingular $A$. With Mathlib's inverse, which is $0$ for a singular
matrix, it holds for every Toeplitz $A$. "Toeplitz" is `Matrix.IsToeplitz`: $A$ is
`Matrix.toeplitz` of a two-sided sequence.

**Generalization.** Lean's matrix inverse is total. The theorem also applies to singular matrices,
whose Lean inverse is zero. The source's inverse requires nonsingularity.
-/
theorem isPersymmetric_inv_of_isToeplitz {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsToeplitz) :
    IsPersymmetricExchange A⁻¹ :=
  isPersymmetric_inv (isPersymmetric_iff.2 hA.isPersymmetric)

/-! ### §4.7.3 The Yule–Walker equations -/

/-- For $r = (r_1, \dots, r_k)$, $r^T \mathcal{E}_k y = \sum_i r_{k-i} y_i$, with indices from $0$.
-/
private theorem dotProduct_exchange_mulVec {k : ℕ} (ρ : ℕ → ℝ) (y : Fin k → ℝ) :
    (fun i : Fin k => ρ (i + 1)) ⬝ᵥ (exchange k *ᵥ y) = ∑ i : Fin k, ρ (k - i) * y i := by
  simp only [dotProduct, exchange_mulVec_apply]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Fin.val_rev]
  congr 2
  omega

/-- If $T_n$ is positive definite and $k \le n$, then $T_k$ is positive definite. -/
private theorem posDef_symmToeplitz_of_le {r : ℕ → ℝ} {k : ℕ}
    (hT : (symmToeplitz n r).PosDef) (hk : k ≤ n) : (symmToeplitz k r).PosDef := by
  rw [← leadingPrincipal_symmToeplitz hk]
  exact hT.submatrix (Fin.castLE_injective hk)

/-- If $T_k$ is positive definite, then the Yule–Walker system $T_k y = -(r_1, \dots, r_k)^T$ has
the unique solution $y^{(k)}$. -/
private theorem eq_sol_of_mulVec_eq {r : ℕ → ℝ} (hr : r 0 = 1) {k : ℕ}
    (hT : (symmToeplitz k r).PosDef) {y : Fin k → ℝ}
    (hy : symmToeplitz k r *ᵥ y = fun i : Fin _ => -r ((i : ℕ) + 1)) :
    y = fun i : Fin k => Durbin.sol r k i := by
  have hβ : ∀ j < k, Durbin.beta r j ≠ 0 := fun j hj => (Durbin.beta_pos hr hT j hj).ne'
  refine mulVec_injective_iff_isUnit.2 hT.isUnit ?_
  rw [hy, Durbin.symmToeplitz_mulVec_sol hr hβ]

/-- **Section 4.7.3** of [golub2013matrix], the bordering step of Durbin's algorithm. Let $r_0 = 1$,
let $y \in \mathbb{R}^k$ solve the Yule–Walker system $T_k y = -r$ with
$r = (r_1, \dots, r_k)^T$, and assume $1 + r^T y \neq 0$. Let
$$\alpha = -\frac{r_{k+1} + r^T \mathcal{E}_k y}{1 + r^T y}, \qquad z = y + \alpha \mathcal{E}_k
  y.$$
Then $(z, \alpha)$ solves the Yule–Walker system of order $k + 1$:
$$T_{k+1} \begin{bmatrix} z \\ \alpha \end{bmatrix} = -(r_1, \dots, r_{k+1})^T.$$

**Generalization.** The solution step assumes the bordered denominator is nonzero. The source works
with positive definite leading blocks, which guarantee that the denominator is positive.
-/
theorem durbin_step {r : ℕ → ℝ} (hr : r 0 = 1) {k : ℕ} {y : Fin k → ℝ}
    (hy : symmToeplitz k r *ᵥ y = fun i : Fin _ => -r ((i : ℕ) + 1))
    (hβ : 1 + (fun i : Fin k => r (i + 1)) ⬝ᵥ y ≠ 0) {α : ℝ}
    (hα : α = -(r (k + 1) + (fun i : Fin k => r (i + 1)) ⬝ᵥ (exchange k *ᵥ y)) /
      (1 + (fun i : Fin k => r (i + 1)) ⬝ᵥ y)) :
    symmToeplitz (k + 1) r *ᵥ Fin.snoc (y + α • (exchange k *ᵥ y)) α =
      fun i : Fin _ => -r ((i : ℕ) + 1) := by
  refine Durbin.bordered_solve hr hy α ?_
  change α * (1 + (fun i : Fin k => r (i + 1)) ⬝ᵥ y) = _
  rw [hα, div_mul_cancel₀ _ hβ, dotProduct_exchange_mulVec]

/-- **Section 4.7.3** of [golub2013matrix], the denominator of Durbin's step. Let $r_0 = 1$ and let
$y \in \mathbb{R}^k$ solve $T_k y = -r$ with $r = (r_1, \dots, r_k)^T$. Then
$$\begin{bmatrix} I & \mathcal{E}_k y \\ 0 & 1 \end{bmatrix}^T \begin{bmatrix} T_k &
  \mathcal{E}_k r \\ r^T \mathcal{E}_k & 1 \end{bmatrix} \begin{bmatrix} I & \mathcal{E}_k y \\
  0 & 1 \end{bmatrix} = \begin{bmatrix} T_k & 0 \\ 0 & 1 + r^T y \end{bmatrix}.$$
If moreover $T_{k+1}$ is positive definite, then $1 + r^T y > 0$.

The middle matrix is $T_{k+1}$ in block form. The source uses the congruence to show that the
denominator in Durbin's step is positive. -/
theorem durbin_denominator_pos {r : ℕ → ℝ} (hr : r 0 = 1) {k : ℕ} {y : Fin k → ℝ}
    (hy : symmToeplitz k r *ᵥ y = fun i : Fin _ => -r ((i : ℕ) + 1)) :
    (fromBlocks 1 (replicateCol (Fin 1) (exchange k *ᵥ y)) 0 1)ᵀ *
        fromBlocks (symmToeplitz k r)
          (replicateCol (Fin 1) (exchange k *ᵥ fun i : Fin k => r (i + 1)))
          (replicateRow (Fin 1) ((fun i : Fin k => r (i + 1)) ᵥ* exchange k))
          (of fun _ _ => 1) *
        fromBlocks 1 (replicateCol (Fin 1) (exchange k *ᵥ y)) 0 1 =
      fromBlocks (symmToeplitz k r) 0 0 (of fun _ _ => 1 + (fun i : Fin k => r (i + 1)) ⬝ᵥ y) ∧
    ((symmToeplitz (k + 1) r).PosDef → 0 < 1 + (fun i : Fin k => r (i + 1)) ⬝ᵥ y) := by
  set r' : Fin k → ℝ := fun i => r (i + 1) with hr'
  -- `T_k ℰ y = ℰ T_k y = −ℰ r`
  have hTE : symmToeplitz k r *ᵥ (exchange k *ᵥ y) = -(exchange k *ᵥ r') := by
    rw [mulVec_mulVec, ← exchange_mul_symmToeplitz k r, ← mulVec_mulVec, hy]
    ext i
    simp [hr']
  -- `(ℰ r)ᵀ (ℰ y) = rᵀ y` and `yᵀ T_k y = −rᵀ y`
  have hEE : (exchange k *ᵥ r') ⬝ᵥ (exchange k *ᵥ y) = r' ⬝ᵥ y := by
    simp only [dotProduct, exchange_mulVec_apply]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun i => by simp
  have hrow : r' ᵥ* exchange k = exchange k *ᵥ r' := by
    ext i
    simp
  set u : Fin k → ℝ := exchange k *ᵥ y with hu
  have hsym : ∀ j, ∑ i, u i * symmToeplitz k r i j = (symmToeplitz k r *ᵥ u) j := fun j => by
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, (isSymm_symmToeplitz k r).apply j i]
  refine ⟨?_, fun hT => ?_⟩
  · rw [hrow]
    have h1 : (fromBlocks 1 (replicateCol (Fin 1) u) 0 1)ᵀ *
        fromBlocks (symmToeplitz k r) (replicateCol (Fin 1) (exchange k *ᵥ r'))
          (replicateRow (Fin 1) (exchange k *ᵥ r')) (of fun _ _ => 1) =
        fromBlocks (symmToeplitz k r) (replicateCol (Fin 1) (exchange k *ᵥ r')) 0
          (of fun _ _ => 1 + u ⬝ᵥ (exchange k *ᵥ r')) := by
      rw [fromBlocks_transpose, transpose_one, transpose_zero, transpose_one,
        transpose_replicateCol, fromBlocks_multiply]
      congr 1
      · simp
      · simp
      · ext a j
        simp only [Matrix.add_apply, Matrix.one_mul, Matrix.mul_apply, replicateRow_apply,
          Matrix.zero_apply]
        rw [hsym j, hTE]
        simp
      · ext a b
        simp [Matrix.mul_apply, dotProduct, add_comm]
    rw [h1, fromBlocks_multiply]
    congr 1
    · simp
    · ext i a
      simp only [Matrix.add_apply, Matrix.mul_one, Matrix.mul_apply, replicateCol_apply,
        Matrix.zero_apply]
      have := congrFun hTE i
      simp only [mulVec, dotProduct, Pi.neg_apply] at this
      rw [this]
      simp [mulVec, dotProduct]
    · simp
    · ext a b
      simp only [Matrix.zero_mul, zero_add, Matrix.mul_one, of_apply]
      rw [dotProduct_comm, hEE]
  · have hβ : ∀ j < k, Durbin.beta r j ≠ 0 := fun j hj =>
      (Durbin.beta_pos hr hT j (by omega)).ne'
    have hy' := eq_sol_of_mulVec_eq hr (posDef_symmToeplitz_of_le hT (Nat.le_succ k)) hy
    have hb := Durbin.beta_pos hr hT k (Nat.lt_succ_self k)
    rw [hy']
    rw [Durbin.beta, Durbin.betaOf,
      ← Fin.sum_univ_eq_sum_range (fun i => r (i + 1) * Durbin.sol r k i)] at hb
    exact hb

/-- **Equation (4.7.1)** of [golub2013matrix], Durbin's recurrence. Let $r_0 = 1$ and let $T_n$ be
positive definite. Then the vectors $y^{(k)}$ of Durbin's recurrence solve the Yule–Walker
systems of every order,
$$T_k y^{(k)} = -(r_1, \dots, r_k)^T, \qquad k = 0, \dots, n,$$
and the denominators satisfy $\beta_k > 0$ for $k = 0, \dots, n-1$.

The recurrence is $y^{(0)} = 0$ and $y^{(k+1)} = (y^{(k)} + \alpha_k \mathcal{E}_k y^{(k)},
\alpha_k)$, with $\beta_k = 1 + r^T y^{(k)}$ and $\alpha_k = -(r_{k+1} + r^T \mathcal{E}_k
y^{(k)})/\beta_k$. These are `Durbin.sol`, `Durbin.beta` and `Durbin.alpha`. -/
theorem equation_4_7_1 {r : ℕ → ℝ} (hr : r 0 = 1) (hT : (symmToeplitz n r).PosDef) :
    (∀ k ≤ n, symmToeplitz k r *ᵥ (fun i : Fin k => Durbin.sol r k i) =
      fun i : Fin _ => -r ((i : ℕ) + 1)) ∧ ∀ k < n, 0 < Durbin.beta r k :=
  ⟨fun k hk => Durbin.symmToeplitz_mulVec_sol hr fun j hj =>
      (Durbin.beta_pos hr hT j (by omega)).ne',
    fun k hk => Durbin.beta_pos hr hT k hk⟩

/-- **Section 4.7.3** of [golub2013matrix], the recursion for the denominators. For every sequence
$r$ and every $k$ with $\beta_k \neq 0$,
$$\beta_{k+1} = (1 - \alpha_k^2) \beta_k.$$

The source writes $\beta_k = (1 - \alpha_{k-1}^2) \beta_{k-1}$ before Algorithm 4.7.1. The
scalars are `Durbin.beta` and `Durbin.alpha`.

**Reading.** The nonzero previous denominator is explicit because the reflection coefficient is
defined by division. The source obtains this nonvanishing from positive definiteness.
-/
theorem durbin_beta_succ {r : ℕ → ℝ} {k : ℕ} (h : Durbin.beta r k ≠ 0) :
    Durbin.beta r (k + 1) = (1 - Durbin.alpha r k ^ 2) * Durbin.beta r k :=
  Durbin.beta_succ h

/-! ### Algorithm 4.7.1 (Durbin) -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.7.1** of [golub2013matrix], one pass. Pass $p$ is the source's step $k = p + 1$ on
the state $(y, \alpha, \beta)$:
```
β = (1 − α²) β
α = −(r(k+1) + r(k:−1:1)ᵀ y(1:k)) / β
z(1:k) = y(1:k) + α y(k:−1:1)
y(1:k+1) = [z(1:k); α]
```
The program updates $\beta$ as $\mathrm{fl}(\mathrm{fl}(1 - \mathrm{fl}(\alpha^2)) \beta)$. It
accumulates the inner product $r(k{:}{-1}{:}1)^T y(1{:}k)$ from $0$ (`FloatingPoint.dotAccum`),
adds $r_{k+1}$ with one rounding, and then divides with one rounding; the negation is exact. The
entries are $z_i = \mathrm{fl}(y_i + \mathrm{fl}(\alpha y_{k-1-i}))$, indexed from $0$.

The same pass computes the index $m(\lambda)$ of (4.7.11) in
`GolubVanLoan.Chapter04.durbinIndex`.

**Reading.** The functions are defined without the source's normalization and definiteness
preconditions, totalize division, and round each arithmetic operation. The exact solve theorems
impose the source's input conditions.
-/
noncomputable def durbinStep (r : ℕ → ℝ) (st : (ℕ → ℝ) × ℝ × ℝ) (p : ℕ) :
    M ((ℕ → ℝ) × ℝ × ℝ) := do
  let a ← rnd (st.2.1 * st.2.1)
  let c ← rnd (1 - a)
  let β ← rnd (c * st.2.2)
  let s ← dotAccum rnd (List.range (p + 1)) (fun j => r (p + 1 - j)) st.1 0
  let s' ← rnd (r (p + 2) + s)
  let α ← rnd (-s' / β)
  let z ← (List.range (p + 1)).foldlM (fun (z : ℕ → ℝ) (i : ℕ) => do
      let q ← rnd (α * st.1 (p - i))
      let zi ← rnd (st.1 i + q)
      pure (Function.update z i zi)) st.1
  pure (Function.update z (p + 1) α, α, β)

/-- **Algorithm 4.7.1** of [golub2013matrix] (Durbin). Given real numbers $r_0, r_1, \dots, r_n$
with $r_0 = 1$ such that $T = (r_{|i-j|}) \in \mathbb{R}^{n \times n}$ is positive definite, the
algorithm computes $y \in \mathbb{R}^n$ such that $Ty = -(r_1, \dots, r_n)^T$:
```
y(1) = −r(1); β = 1; α = −r(1)
for k = 1:n−1
    β = (1 − α²) β
    α = −(r(k+1) + r(k:−1:1)ᵀ y(1:k)) / β
    z(1:k) = y(1:k) + α y(k:−1:1)
    y(1:k+1) = [z(1:k); α]
end
```
Pass $p$ of the loop is the source's $k = p + 1$, and it is `GolubVanLoan.Chapter04.durbinStep`.
The state $(y, \alpha, \beta)$ holds $y(1{:}k)$ in the entries $0, \dots, k - 1$ of `y : ℕ → ℝ`,
and the output is the first $n$ entries of $y$.

**Reading.** The functions are defined without the source's normalization and definiteness
preconditions, totalize division, and round each arithmetic operation. The exact solve theorems
impose the source's input conditions.
-/
noncomputable def algorithm_4_7_1 (n : ℕ) (r : ℕ → ℝ) : M (Fin n → ℝ) := do
  let st ← (List.range (n - 1)).foldlM (fun st p => durbinStep rnd r st p)
    (Function.update 0 0 (-r 1), -r 1, 1)
  pure fun i => st.1 i

end Programs

/-- Overwriting the entries $i < m$ of a vector, one after the other, by values $g_i$ that do not
depend on the vector gives the vector with entries $g_i$ for $i < m$ and unchanged entries
otherwise. -/
private theorem foldl_range_update (g : ℕ → ℝ) (m : ℕ) (y : ℕ → ℝ) :
    (List.range m).foldl (fun (z : ℕ → ℝ) (i : ℕ) => Function.update z i (g i)) y =
      fun i => if i < m then g i else y i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih]
    funext i
    simp only [List.foldl_cons, List.foldl_nil, Function.update_apply]
    rcases lt_trichotomy i m with h | rfl | h
    · simp [h.ne, h, Nat.lt_succ_of_lt h]
    · simp
    · simp [h.ne', not_lt.2 h.le, show ¬ i < m + 1 by omega]

/-- A list sum over `List.range m` is the `Finset` sum over `Finset.range m`. -/
private theorem sum_map_range (f : ℕ → ℝ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- One pass of Algorithm 4.7.1 in exact arithmetic. -/
private noncomputable def durbinExactStep (r : ℕ → ℝ) (st : (ℕ → ℝ) × ℝ × ℝ) (p : ℕ) :
    (ℕ → ℝ) × ℝ × ℝ :=
  let β := (1 - st.2.1 * st.2.1) * st.2.2
  let α := -(r (p + 2) + (0 + ((List.range (p + 1)).map fun j => r (p + 1 - j) * st.1 j).sum)) / β
  (Function.update ((List.range (p + 1)).foldl
    (fun (z : ℕ → ℝ) (i : ℕ) => Function.update z i (st.1 i + α * st.1 (p - i))) st.1)
    (p + 1) α, α, β)

/-- In exact arithmetic, one pass of Algorithm 4.7.1 is `GolubVanLoan.Chapter04.durbinExactStep`. -/
private theorem durbinStep_id (r : ℕ → ℝ) (st : (ℕ → ℝ) × ℝ × ℝ) (p : ℕ) :
    Id.run (durbinStep pure r st p) = durbinExactStep r st p := by
  simp only [durbinStep, dotAccum_pure, pure_bind, List.foldlM_pure]
  rfl

/-- In exact arithmetic, Algorithm 4.7.1 is a fold of its exact passes. -/
private theorem algorithm_4_7_1_id (n : ℕ) (r : ℕ → ℝ) :
    Id.run (algorithm_4_7_1 pure n r) =
      fun i : Fin n => ((List.range (n - 1)).foldl (durbinExactStep r)
        (Function.update 0 0 (-r 1), -r 1, 1)).1 i := by
  simp only [algorithm_4_7_1, Id.run_bind, List.idRun_foldlM, durbinStep_id]
  rfl

/-- If $\beta_j \neq 0$ for $j < p$, then after $p$ exact passes the state of Algorithm 4.7.1 is
$(y^{(p+1)}, \alpha_p, \beta_p)$. -/
private theorem durbin_foldl {r : ℕ → ℝ} (p : ℕ) (hβ : ∀ j < p, Durbin.beta r j ≠ 0) :
    (List.range p).foldl (durbinExactStep r) (Function.update 0 0 (-r 1), -r 1, 1) =
      (Durbin.sol r (p + 1), Durbin.alpha r p, Durbin.beta r p) := by
  induction p with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    have ha : Durbin.alpha r 0 = -r 1 := by simp [Durbin.alpha, Durbin.alphaOf, Durbin.betaOf]
    refine Prod.ext ?_ (Prod.ext ha.symm (Durbin.beta_zero r).symm)
    funext i
    dsimp only
    rw [Durbin.sol_succ]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [ha]
    · simp [hi.ne']
  | succ p ih =>
    rw [List.range_succ, List.foldl_append, ih fun j hj => hβ j (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, durbinExactStep]
    have hb : (1 - Durbin.alpha r p * Durbin.alpha r p) * Durbin.beta r p =
        Durbin.beta r (p + 1) := by
      rw [Durbin.beta_succ (hβ p (by omega))]
      ring
    have ha : -(r (p + 2) + (0 + ((List.range (p + 1)).map fun j =>
        r (p + 1 - j) * Durbin.sol r (p + 1) j).sum)) / Durbin.beta r (p + 1) =
        Durbin.alpha r (p + 1) := by
      rw [zero_add, sum_map_range]
      rfl
    rw [hb, ha, foldl_range_update]
    refine Prod.ext ?_ rfl
    funext i
    dsimp only
    rw [Durbin.sol_succ r (p + 1) i, Function.update_apply]
    rcases lt_trichotomy i (p + 1) with h | rfl | h
    · simp [h, h.ne]
    · simp
    · simp [h.ne', show ¬ i < p + 1 by omega, Durbin.sol_of_le r h.le]

/-- **Algorithm 4.7.1** of [golub2013matrix], exact correctness. Let $r_0 = 1$ and let $T_n$ be
positive definite. In exact arithmetic, Algorithm 4.7.1 returns a vector $y \in \mathbb{R}^n$
with
$$T_n y = -(r_1, \dots, r_n)^T.$$

After $k$ passes of the loop, that is, after the source's step $k$, the state is
$(y^{(k+1)}, \alpha_k, \beta_k)$ of (4.7.1); the update $\beta \leftarrow (1 - \alpha^2) \beta$
of the source is `Durbin.beta_succ`. -/
theorem algorithm_4_7_1_spec {r : ℕ → ℝ} (hr : r 0 = 1) (hT : (symmToeplitz n r).PosDef) :
    symmToeplitz n r *ᵥ Id.run (algorithm_4_7_1 pure n r) = fun i : Fin _ => -r ((i : ℕ) + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext i
    exact i.elim0
  have hβ : ∀ j < n, Durbin.beta r j ≠ 0 := fun j hj => (Durbin.beta_pos hr hT j hj).ne'
  rw [algorithm_4_7_1_id, durbin_foldl (n - 1) fun j hj => hβ j (by omega)]
  change symmToeplitz n r *ᵥ (fun i : Fin n => Durbin.sol r (n - 1 + 1) i) = _
  rw [Nat.sub_add_cancel hn]
  exact Durbin.symmToeplitz_mulVec_sol hr hβ

/-! ### §4.7.4 The general right-hand side -/

/-- **Equations (4.7.2)→(4.7.3)** of [golub2013matrix], the bordering step for a general right-hand
side. Let $r_0 = 1$, let $x, y, b \in \mathbb{R}^k$ and $b_{k+1} \in \mathbb{R}$, and let
$r = (r_1, \dots, r_k)^T$. Assume that $T_k x = b$ (4.7.2), that $T_k y = -r$, and that
$1 + r^T y \neq 0$. Let
$$\mu = \frac{b_{k+1} - r^T \mathcal{E}_k x}{1 + r^T y}, \qquad v = x + \mu \mathcal{E}_k y.$$
Then $(v, \mu)$ solves the system (4.7.3) of order $k + 1$:
$$\begin{bmatrix} T_k & \mathcal{E}_k r \\ r^T \mathcal{E}_k & 1 \end{bmatrix} \begin{bmatrix} v
  \\ \mu \end{bmatrix} = \begin{bmatrix} b \\ b_{k+1} \end{bmatrix}.$$

The source remarks that the transition from (4.7.2) to (4.7.3) costs $O(k)$ flops. The block
matrix is $T_{k+1}$.

**Generalization.** The solution step assumes the bordered denominator is nonzero. The source works
with positive definite leading blocks, which guarantee that the denominator is positive.
-/
theorem equation_4_7_3 {r : ℕ → ℝ} (hr : r 0 = 1) {k : ℕ} {x y b : Fin k → ℝ} (b' : ℝ)
    (hx : symmToeplitz k r *ᵥ x = b)
    (hy : symmToeplitz k r *ᵥ y = fun i : Fin _ => -r ((i : ℕ) + 1))
    (hβ : 1 + (fun i : Fin k => r (i + 1)) ⬝ᵥ y ≠ 0) {μ : ℝ}
    (hμ : μ = (b' - (fun i : Fin k => r (i + 1)) ⬝ᵥ (exchange k *ᵥ x)) /
      (1 + (fun i : Fin k => r (i + 1)) ⬝ᵥ y)) :
    symmToeplitz (k + 1) r *ᵥ Fin.snoc (x + μ • (exchange k *ᵥ y)) μ = Fin.snoc b b' := by
  refine Levinson.bordered_solve hr b' hy hx μ ?_
  change μ * (1 + (fun i : Fin k => r (i + 1)) ⬝ᵥ y) = _
  rw [hμ, div_mul_cancel₀ _ hβ, dotProduct_exchange_mulVec]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.7.2** of [golub2013matrix] (Levinson). Given $b \in \mathbb{R}^n$ and real numbers
$1 = r_0, r_1, \dots, r_n$ such that $T = (r_{|i-j|}) \in \mathbb{R}^{n \times n}$ is positive
definite, the algorithm computes $x \in \mathbb{R}^n$ such that $Tx = b$:
```
y(1) = −r(1); x(1) = b(1); β = 1; α = −r(1)
for k = 1:n−1
    β = (1 − α²) β
    μ = (b(k+1) − r(1:k)ᵀ x(k:−1:1)) / β
    v(1:k) = x(1:k) + μ y(k:−1:1)
    x(1:k+1) = [v(1:k); μ]
    if k < n−1
        α = −(r(k+1) + r(1:k)ᵀ y(k:−1:1)) / β
        z(1:k) = y(1:k) + α y(k:−1:1)
        y(1:k+1) = [z(1:k); α]
    end
end
```
Pass $p$ is the source's $k = p + 1$. The state $(x, y, \alpha, \beta)$ holds $x(1{:}k)$ and
$y(1{:}k)$ in the entries $0, \dots, k - 1$ of $\mathbb{N}$-indexed vectors, as in
`GolubVanLoan.Chapter04.algorithm_4_7_1`. The inner product $r(1{:}k)^T x(k{:}{-1}{:}1)$ is
accumulated from $0$ (`FloatingPoint.dotAccum`) and then subtracted from $b_{k+1}$ with one
rounding. The inner product in $\alpha$ is accumulated from $0$ and then added to $r_{k+1}$ with
one rounding.

**Reading.** The functions are defined without the source's normalization and definiteness
preconditions, totalize division, and round each arithmetic operation. The exact solve theorems
impose the source's input conditions.
-/
noncomputable def algorithm_4_7_2 (n : ℕ) (r : ℕ → ℝ) (b : Fin n → ℝ) : M (Fin n → ℝ) := do
  let bv : ℕ → ℝ := fun j => if h : j < n then b ⟨j, h⟩ else 0
  let st ← (List.range (n - 1)).foldlM
    (fun (st : (ℕ → ℝ) × (ℕ → ℝ) × ℝ × ℝ) (p : ℕ) => do
      let a ← rnd (st.2.2.1 * st.2.2.1)
      let c ← rnd (1 - a)
      let β ← rnd (c * st.2.2.2)
      let s ← dotAccum rnd (List.range (p + 1)) (fun j => r (j + 1)) (fun j => st.1 (p - j)) 0
      let d ← rnd (bv (p + 1) - s)
      let μ ← rnd (d / β)
      let v ← (List.range (p + 1)).foldlM (fun (v : ℕ → ℝ) (i : ℕ) => do
          let q ← rnd (μ * st.2.1 (p - i))
          let vi ← rnd (st.1 i + q)
          pure (Function.update v i vi)) st.1
      if p + 1 < n - 1 then do
        let t ← dotAccum rnd (List.range (p + 1)) (fun j => r (j + 1))
          (fun j => st.2.1 (p - j)) 0
        let t' ← rnd (r (p + 2) + t)
        let α ← rnd (-t' / β)
        let z ← (List.range (p + 1)).foldlM (fun (z : ℕ → ℝ) (i : ℕ) => do
            let q ← rnd (α * st.2.1 (p - i))
            let zi ← rnd (st.2.1 i + q)
            pure (Function.update z i zi)) st.2.1
        pure (Function.update v (p + 1) μ, Function.update z (p + 1) α, α, β)
      else pure (Function.update v (p + 1) μ, st.2.1, st.2.2.1, β))
    (Function.update 0 0 (bv 0), Function.update 0 0 (-r 1), -r 1, 1)
  pure fun i => st.1 i

end Programs

/-- One pass of Algorithm 4.7.2 in exact arithmetic. -/
private noncomputable def levinsonExactStep (n : ℕ) (r bv : ℕ → ℝ)
    (st : (ℕ → ℝ) × (ℕ → ℝ) × ℝ × ℝ) (p : ℕ) : (ℕ → ℝ) × (ℕ → ℝ) × ℝ × ℝ :=
  let β := (1 - st.2.2.1 * st.2.2.1) * st.2.2.2
  let μ := (bv (p + 1) - (0 + ((List.range (p + 1)).map
    fun j => r (j + 1) * st.1 (p - j)).sum)) / β
  let v := (List.range (p + 1)).foldl
    (fun (v : ℕ → ℝ) (i : ℕ) => Function.update v i (st.1 i + μ * st.2.1 (p - i))) st.1
  if p + 1 < n - 1 then
    let α := -(r (p + 2) + (0 + ((List.range (p + 1)).map
      fun j => r (j + 1) * st.2.1 (p - j)).sum)) / β
    (Function.update v (p + 1) μ, Function.update ((List.range (p + 1)).foldl
      (fun (z : ℕ → ℝ) (i : ℕ) => Function.update z i (st.2.1 i + α * st.2.1 (p - i))) st.2.1)
      (p + 1) α, α, β)
  else (Function.update v (p + 1) μ, st.2.1, st.2.2.1, β)

/-- In exact arithmetic, Algorithm 4.7.2 is a fold of its exact passes. -/
private theorem algorithm_4_7_2_id (n : ℕ) (r : ℕ → ℝ) (b : Fin n → ℝ) :
    Id.run (algorithm_4_7_2 pure n r b) =
      fun i : Fin n => ((List.range (n - 1)).foldl
        (levinsonExactStep n r fun j => if h : j < n then b ⟨j, h⟩ else 0)
        (Function.update 0 0 (if h : 0 < n then b ⟨0, h⟩ else 0),
          Function.update 0 0 (-r 1), -r 1, 1)).1 i := by
  simp only [algorithm_4_7_2, dotAccum_pure, pure_bind, List.foldlM_pure, ite_pure]
  rfl

/-- Reversing the order of an inner product of length $p + 1$: $\sum_{j=0}^{p} f_{j+1} g_{p-j} =
\sum_{i=0}^{p} f_{p+1-i} g_i$. -/
private theorem sum_range_succ_reflect (f g : ℕ → ℝ) (p : ℕ) :
    ∑ j ∈ range (p + 1), f (j + 1) * g (p - j) = ∑ i ∈ range (p + 1), f (p + 1 - i) * g i := by
  rw [← Finset.sum_range_reflect (fun i => f (p + 1 - i) * g i) (p + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := mem_range.1 hj
  rw [show p + 1 - (p + 1 - 1 - j) = j + 1 by omega, show p + 1 - 1 - j = p - j by omega]

/-- Levinson's solution $x^{(k)}$ vanishes from index $k$ on. -/
private theorem levinson_sol_of_le {r b : ℕ → ℝ} {k i : ℕ} (h : k ≤ i) :
    Levinson.sol r b k i = 0 := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [Levinson.sol_succ]
    split_ifs <;> first | rfl | omega

/-- The update of Durbin's solution in the order of the source: $y^{(k+1)} = (y^{(k)} + \alpha_k
\mathcal{E}_k y^{(k)}, \alpha_k)$. -/
private theorem durbin_sol_update (r : ℕ → ℝ) (p : ℕ) :
    Function.update ((List.range (p + 1)).foldl (fun (z : ℕ → ℝ) (i : ℕ) =>
        Function.update z i (Durbin.sol r (p + 1) i +
          Durbin.alpha r (p + 1) * Durbin.sol r (p + 1) (p - i))) (Durbin.sol r (p + 1)))
      (p + 1) (Durbin.alpha r (p + 1)) = Durbin.sol r (p + 1 + 1) := by
  rw [foldl_range_update]
  funext i
  rw [Durbin.sol_succ r (p + 1) i, Function.update_apply]
  rcases lt_trichotomy i (p + 1) with h | rfl | h
  · simp [h, h.ne]
  · simp
  · simp [h.ne', show ¬ i < p + 1 by omega, Durbin.sol_of_le r h.le]

/-- If $\beta_j \neq 0$ for $j < n$, then after $p \le n - 1$ exact passes of Algorithm 4.7.2 the
state has $x = x^{(p+1)}$ of Levinson's recurrence and $\beta = \beta_p$, and, if $p < n - 1$,
also $(y, \alpha) = (y^{(p+1)}, \alpha_p)$ of Durbin's recurrence. -/
private theorem levinson_foldl {n : ℕ} {r bv : ℕ → ℝ} (hβ : ∀ j < n, Durbin.beta r j ≠ 0) :
    ∀ p, p ≤ n - 1 →
      ((List.range p).foldl (levinsonExactStep n r bv)
          (Function.update 0 0 (bv 0), Function.update 0 0 (-r 1), -r 1, 1)).1 =
        Levinson.sol r bv (p + 1) ∧
      ((List.range p).foldl (levinsonExactStep n r bv)
          (Function.update 0 0 (bv 0), Function.update 0 0 (-r 1), -r 1, 1)).2.2.2 =
        Durbin.beta r p ∧
      (p < n - 1 →
        ((List.range p).foldl (levinsonExactStep n r bv)
            (Function.update 0 0 (bv 0), Function.update 0 0 (-r 1), -r 1, 1)).2.1 =
          Durbin.sol r (p + 1) ∧
        ((List.range p).foldl (levinsonExactStep n r bv)
            (Function.update 0 0 (bv 0), Function.update 0 0 (-r 1), -r 1, 1)).2.2.1 =
          Durbin.alpha r p) := by
  intro p
  induction p with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil]
    have ha : Durbin.alpha r 0 = -r 1 := by simp [Durbin.alpha, Durbin.alphaOf, Durbin.betaOf]
    refine ⟨?_, (Durbin.beta_zero r).symm, fun _ => ⟨?_, ha.symm⟩⟩
    · funext i
      rw [Levinson.sol_succ]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [Levinson.mu, Levinson.muOf]
      · simp [hi.ne']
    · funext i
      rw [Durbin.sol_succ]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [ha]
      · simp [hi.ne']
  | succ p ih =>
    intro hp
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    obtain ⟨h3, h4⟩ := h3 (by omega)
    rw [List.range_succ, List.foldl_append]
    generalize (List.range p).foldl (levinsonExactStep n r bv)
      (Function.update 0 0 (bv 0), Function.update 0 0 (-r 1), -r 1, 1) = st at h1 h2 h3 h4
    obtain ⟨x, y, α, β⟩ := st
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    have hb : (1 - Durbin.alpha r p * Durbin.alpha r p) * Durbin.beta r p =
        Durbin.beta r (p + 1) := by
      rw [Durbin.beta_succ (hβ p (by omega))]
      ring
    have hμ : (bv (p + 1) - (0 + ((List.range (p + 1)).map
        fun j => r (j + 1) * Levinson.sol r bv (p + 1) (p - j)).sum)) /
          ((1 - Durbin.alpha r p * Durbin.alpha r p) * Durbin.beta r p) =
        Levinson.mu r bv (p + 1) := by
      rw [hb, zero_add, sum_map_range, sum_range_succ_reflect]
      rfl
    have hx : Function.update ((List.range (p + 1)).foldl (fun (v : ℕ → ℝ) (i : ℕ) =>
        Function.update v i (Levinson.sol r bv (p + 1) i +
          Levinson.mu r bv (p + 1) * Durbin.sol r (p + 1) (p - i))) (Levinson.sol r bv (p + 1)))
        (p + 1) (Levinson.mu r bv (p + 1)) = Levinson.sol r bv (p + 1 + 1) := by
      rw [foldl_range_update]
      funext i
      rw [Levinson.sol_succ r bv (p + 1) i, Function.update_apply]
      rcases lt_trichotomy i (p + 1) with h | rfl | h
      · simp [h, h.ne]
      · simp
      · simp [h.ne', show ¬ i < p + 1 by omega, levinson_sol_of_le h.le]
    simp only [List.foldl_cons, List.foldl_nil, levinsonExactStep]
    rw [hμ]
    split_ifs with hlt
    · have hα : -(r (p + 2) + (0 + ((List.range (p + 1)).map
          fun j => r (j + 1) * Durbin.sol r (p + 1) (p - j)).sum)) /
            ((1 - Durbin.alpha r p * Durbin.alpha r p) * Durbin.beta r p) =
          Durbin.alpha r (p + 1) := by
        rw [hb, zero_add, sum_map_range, sum_range_succ_reflect]
        rfl
      rw [hα]
      exact ⟨hx, hb, fun _ => ⟨durbin_sol_update r p, rfl⟩⟩
    · exact ⟨hx, hb, fun h => absurd h hlt⟩

/-- **Algorithm 4.7.2** of [golub2013matrix], exact correctness. Let $r_0 = 1$, let $T_n$ be
positive definite, and let $b \in \mathbb{R}^n$. In exact arithmetic, Algorithm 4.7.2 returns a
vector $x \in \mathbb{R}^n$ with
$$T_n x = b.$$

After $k$ passes of the loop, that is, after the source's step $k$, the state has
$x = x^{(k+1)}$ and $\beta = \beta_k$ of Levinson's and Durbin's recurrences (`Levinson.sol`,
`Durbin.beta`). For $k < n - 1$ it also has $(y, \alpha) = (y^{(k+1)}, \alpha_k)$ of Durbin's
recurrence (`Durbin.sol`, `Durbin.alpha`); the last pass does not update $y$ and $\alpha$. -/
theorem algorithm_4_7_2_spec {r : ℕ → ℝ} (hr : r 0 = 1) (hT : (symmToeplitz n r).PosDef)
    (b : Fin n → ℝ) : symmToeplitz n r *ᵥ Id.run (algorithm_4_7_2 pure n r b) = b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext i
    exact i.elim0
  have hβ : ∀ j < n, Durbin.beta r j ≠ 0 := fun j hj => (Durbin.beta_pos hr hT j hj).ne'
  rw [algorithm_4_7_2_id,
    (levinson_foldl (bv := fun j => if h : j < n then b ⟨j, h⟩ else 0) hβ (n - 1) le_rfl).1]
  change symmToeplitz n r *ᵥ (fun i : Fin n => Levinson.sol r
    (fun j => if h : j < n then b ⟨j, h⟩ else 0) (n - 1 + 1) i) = _
  rw [Nat.sub_add_cancel hn, Levinson.symmToeplitz_mulVec_sol hr _ hβ]
  funext i
  simp

/-! ### §4.7.5 The inverse -/

/-- **Equation (4.7.4)** of [golub2013matrix], with the formulas after it. Let $r_0 = 1$, let
$n = m + 1$, and let $T_n$ be positive definite. Partition
$$T_n^{-1} = \begin{bmatrix} B & v \\ v^T & \gamma \end{bmatrix}, \qquad B \in \mathbb{R}^{m
  \times m}.$$
Let $y \in \mathbb{R}^m$ solve the Yule–Walker system $T_m y = -(r_1, \dots, r_m)^T$. Then
$$\gamma = \frac{1}{1 + r^T y}, \qquad v = \gamma \mathcal{E}_m y, \qquad B = T_m^{-1} + \frac{v
  v^T}{\gamma}.$$

The theorem takes $\gamma$ and $v$ defined by the first two formulas, and states that the last
column of $T_n^{-1}$ is $(v, \gamma)$ and that its leading $m \times m$ block is
$T_m^{-1} + \gamma^{-1} v v^T$. -/
theorem equation_4_7_4 {r : ℕ → ℝ} (hr : r 0 = 1) {m : ℕ}
    (hT : (symmToeplitz (m + 1) r).PosDef) {y : Fin m → ℝ}
    (hy : symmToeplitz m r *ᵥ y = fun i : Fin _ => -r ((i : ℕ) + 1)) {γ : ℝ} {v : Fin m → ℝ}
    (hγ : γ = 1 / (1 + (fun i : Fin m => r (i + 1)) ⬝ᵥ y)) (hv : v = γ • (exchange m *ᵥ y)) :
    (fun i => (symmToeplitz (m + 1) r)⁻¹ i (Fin.last m)) = Fin.snoc v γ ∧
      (symmToeplitz (m + 1) r)⁻¹.submatrix Fin.castSucc Fin.castSucc =
        (symmToeplitz m r)⁻¹ + γ⁻¹ • vecMulVec v v := by
  have hβ : ∀ j < m + 1, Durbin.beta r j ≠ 0 := fun j hj => (Durbin.beta_pos hr hT j hj).ne'
  have hy' := eq_sol_of_mulVec_eq hr (posDef_symmToeplitz_of_le hT (Nat.le_succ m)) hy
  have hγ' : γ = Trench.gamma r m := by
    rw [hγ, hy', Trench.gamma, Durbin.beta, Durbin.betaOf,
      ← Fin.sum_univ_eq_sum_range (fun i => r (i + 1) * Durbin.sol r m i)]
    rfl
  have hv' : v = Trench.lastCol r m := by rw [hv, hγ', hy']; rfl
  rw [hγ', hv']
  exact ⟨Trench.inv_symmToeplitz_last hr hβ, Trench.inv_symmToeplitz_eq hr hβ⟩

/-- **Equation (4.7.5)** of [golub2013matrix]. Let $r_0 = 1$, let $n = m + 1$, let $T_n$ be positive
definite, and partition $T_n^{-1} = \begin{bmatrix} B & v \\ v^T & \gamma \end{bmatrix}$ as in
(4.7.4). Then for $i, j = 1, \dots, m$,
$$b_{ij} = b_{n-j, n-i} + \frac{v_i v_j - v_{n-j} v_{n-i}}{\gamma}.$$

The indices here start at $1$, as in the source. In the Lean statement they start at $0$, and
the reflected index $n - j$ is `Fin.rev j` in the index set `Fin m` of $B$. The entries
$b_{ij}$, $v_i$ and $\gamma$ are read off $T_n^{-1}$. -/
theorem equation_4_7_5 {r : ℕ → ℝ} (hr : r 0 = 1) {m : ℕ}
    (hT : (symmToeplitz (m + 1) r).PosDef) (i j : Fin m) :
    (symmToeplitz (m + 1) r)⁻¹ i.castSucc j.castSucc =
      (symmToeplitz (m + 1) r)⁻¹ j.rev.castSucc i.rev.castSucc +
        ((symmToeplitz (m + 1) r)⁻¹ i.castSucc (Fin.last m) *
            (symmToeplitz (m + 1) r)⁻¹ j.castSucc (Fin.last m) -
          (symmToeplitz (m + 1) r)⁻¹ j.rev.castSucc (Fin.last m) *
            (symmToeplitz (m + 1) r)⁻¹ i.rev.castSucc (Fin.last m)) /
          (symmToeplitz (m + 1) r)⁻¹ (Fin.last m) (Fin.last m) := by
  have hβ : ∀ j < m + 1, Durbin.beta r j ≠ 0 := fun j hj => (Durbin.beta_pos hr hT j hj).ne'
  have hc := Trench.inv_symmToeplitz_last hr hβ
  have hcol : ∀ a : Fin m, (symmToeplitz (m + 1) r)⁻¹ a.castSucc (Fin.last m) =
      Trench.lastCol r m a := fun a => by
    rw [show (symmToeplitz (m + 1) r)⁻¹ a.castSucc (Fin.last m) =
      (fun i => (symmToeplitz (m + 1) r)⁻¹ i (Fin.last m)) a.castSucc from rfl, hc,
      Fin.snoc_castSucc]
  have hlast : (symmToeplitz (m + 1) r)⁻¹ (Fin.last m) (Fin.last m) = Trench.gamma r m := by
    rw [show (symmToeplitz (m + 1) r)⁻¹ (Fin.last m) (Fin.last m) =
      (fun i => (symmToeplitz (m + 1) r)⁻¹ i (Fin.last m)) (Fin.last m) from rfl, hc,
      Fin.snoc_last]
  rw [hcol, hcol, hcol, hcol, hlast]
  exact Trench.inv_symmToeplitz_apply_succ hr hβ i j

/-- The first row of $B$ in Trench's algorithm: $B(1, 1) = \gamma$ and
$B(1, 2{:}n) = v(n{-}1{:}{-1}{:}1)^T$. -/
private def trenchRow0 (n : ℕ) (γ : ℝ) (v : ℕ → ℝ) : ℕ → ℕ → ℝ :=
  Function.update 0 0 fun j => if j = 0 then γ else if j < n then v (n - 1 - j) else 0

/-- The row $i$ of the loop of Trench's algorithm, in exact arithmetic. -/
private noncomputable def trenchStep (n : ℕ) (γ : ℝ) (v : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (i : ℕ) :
    ℕ → ℕ → ℝ :=
  (List.range' i (n - 2 * i)).foldl (fun (B : ℕ → ℕ → ℝ) (j : ℕ) =>
    Function.update B i (Function.update (B i) j
      (B (i - 1) (j - 1) + (v (n - 1 - j) * v (n - 1 - i) - v (i - 1) * v (j - 1)) / γ))) B

/-- Trench's computation of $B$ from its edges to its interior, in exact arithmetic and with
$\mathbb{N}$-indexed entries: the first row, and then for
$i = 2, \dots, \lfloor (n-1)/2 \rfloor + 1$ and $j = i, \dots, n - i + 1$, $B(i, j) = B(i-1,
j-1) + (v_{n+1-j} v_{n+1-i} - v_{i-1} v_{j-1})/\gamma$ (indices from $1$ here, from $0$ in the
code). -/
private noncomputable def trenchWedge (n : ℕ) (γ : ℝ) (v : ℕ → ℝ) : ℕ → ℕ → ℝ :=
  (List.range' 1 ((n - 1) / 2)).foldl (trenchStep n γ v) (trenchRow0 n γ v)

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 4.7.3** of [golub2013matrix] (Trench). Given real numbers $1 = r_0, r_1, \dots, r_n$
such that $T = (r_{|i-j|}) \in \mathbb{R}^{n \times n}$ is positive definite, the algorithm
computes $B = T_n^{-1}$. Only the entries $b_{ij}$ with $i \le j$ and $i + j \le n + 1$ are
computed:
```
Use Algorithm 4.7.1 to solve T_{n−1} y = −(r₁, …, r_{n−1})ᵀ.
γ = 1/(1 + r(1:n−1)ᵀ y(1:n−1))
v(1:n−1) = γ y(n−1:−1:1)
B(1, 1) = γ
B(1, 2:n) = v(n−1:−1:1)ᵀ
for i = 2:floor((n−1)/2) + 1
    for j = i:n−i+1
        B(i, j) = B(i−1, j−1) + (v(n+1−j) v(n+1−i) − v(i−1) v(j−1))/γ
    end
end
```
The program is indexed from $0$, and holds $B$ as $\mathbb{N}$-indexed entries. The first row is
copied, not computed. The entries outside the upper wedge are $0$. The inner product $r^T y$ is
accumulated from $0$ (`FloatingPoint.dotAccum`) and then added to $1$ with one rounding.

**Reading.** The program returns a full matrix with zero placeholders outside the computed upper
wedge. The source leaves those entries uncomputed. Arithmetic is rounded and division is totalized;
exact correctness assumes the stated input conditions.
-/
noncomputable def algorithm_4_7_3 (n : ℕ) (r : ℕ → ℝ) : M (Matrix (Fin n) (Fin n) ℝ) := do
  let y ← algorithm_4_7_1 rnd (n - 1) r
  let yv : ℕ → ℝ := fun j => if h : j < n - 1 then y ⟨j, h⟩ else 0
  let s ← dotAccum rnd (List.range (n - 1)) (fun j => r (j + 1)) yv 0
  let t ← rnd (1 + s)
  let γ ← rnd (1 / t)
  let v ← (List.range (n - 1)).foldlM (fun (v : ℕ → ℝ) (i : ℕ) => do
      let q ← rnd (γ * yv (n - 2 - i))
      pure (Function.update v i q)) 0
  let B ← (List.range' 1 ((n - 1) / 2)).foldlM (fun (B : ℕ → ℕ → ℝ) (i : ℕ) =>
      (List.range' i (n - 2 * i)).foldlM (fun (B : ℕ → ℕ → ℝ) (j : ℕ) => do
        let p₁ ← rnd (v (n - 1 - j) * v (n - 1 - i))
        let p₂ ← rnd (v (i - 1) * v (j - 1))
        let d ← rnd (p₁ - p₂)
        let e ← rnd (d / γ)
        let bij ← rnd (B (i - 1) (j - 1) + e)
        pure (Function.update B i (Function.update (B i) j bij))) B)
    (Function.update 0 0 fun j => if j = 0 then γ else if j < n then v (n - 1 - j) else 0)
  pure (Matrix.of fun i j => B i j)

end Programs

/-- The exact $\gamma = 1/(1 + r^T y)$ of Algorithm 4.7.3. -/
private noncomputable def trenchGamma (n : ℕ) (r yv : ℕ → ℝ) : ℝ :=
  1 / (1 + (0 + ((List.range (n - 1)).map fun j => r (j + 1) * yv j).sum))

/-- The exact $v = \gamma\, y(n{-}1{:}{-1}{:}1)$ of Algorithm 4.7.3. -/
private def trenchV (n : ℕ) (γ : ℝ) (yv : ℕ → ℝ) : ℕ → ℝ :=
  (List.range (n - 1)).foldl
    (fun (v : ℕ → ℝ) (i : ℕ) => Function.update v i (γ * yv (n - 2 - i))) 0

/-- The exact semantics of Algorithm 4.7.3. -/
private theorem algorithm_4_7_3_id (n : ℕ) (r : ℕ → ℝ) :
    Id.run (algorithm_4_7_3 pure n r) = Matrix.of fun i j : Fin n =>
      trenchWedge n (trenchGamma n r fun j =>
          if h : j < n - 1 then Id.run (algorithm_4_7_1 pure (n - 1) r) ⟨j, h⟩ else 0)
        (trenchV n (trenchGamma n r fun j =>
          if h : j < n - 1 then Id.run (algorithm_4_7_1 pure (n - 1) r) ⟨j, h⟩ else 0)
          fun j => if h : j < n - 1 then Id.run (algorithm_4_7_1 pure (n - 1) r) ⟨j, h⟩ else 0)
        i j := by
  simp only [algorithm_4_7_3, dotAccum_pure, pure_bind, List.foldlM_pure]
  rfl

/-- If $\beta_j \neq 0$ for $j < n - 1$, then the exact run of Algorithm 4.7.1 returns Durbin's
solution $y^{(n)}$. -/
private theorem algorithm_4_7_1_id_eq_sol {r : ℕ → ℝ} (n : ℕ)
    (hβ : ∀ j < n - 1, Durbin.beta r j ≠ 0) :
    Id.run (algorithm_4_7_1 pure n r) = fun i : Fin n => Durbin.sol r n i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · funext i
    exact i.elim0
  rw [algorithm_4_7_1_id, durbin_foldl (n - 1) hβ]
  funext i
  change Durbin.sol r (n - 1 + 1) i = _
  rw [Nat.sub_add_cancel hn]

/-- One row of the loop of Trench's algorithm: the entries $(i, l)$ with $i \le l < i + c$ become
$B(i-1, l-1) + e_l$, and no other entry changes. -/
private theorem foldl_trenchRow (i : ℕ) (hi : 1 ≤ i) (e : ℕ → ℝ) (B : ℕ → ℕ → ℝ) (c : ℕ) :
    (∀ k l, (k ≠ i ∨ l < i ∨ i + c ≤ l) →
      (List.range' i c).foldl (fun (B : ℕ → ℕ → ℝ) (j : ℕ) =>
        Function.update B i (Function.update (B i) j (B (i - 1) (j - 1) + e j))) B k l =
        B k l) ∧
    ∀ l, i ≤ l → l < i + c →
      (List.range' i c).foldl (fun (B : ℕ → ℕ → ℝ) (j : ℕ) =>
        Function.update B i (Function.update (B i) j (B (i - 1) (j - 1) + e j))) B i l =
        B (i - 1) (l - 1) + e l := by
  induction c with
  | zero => exact ⟨fun _ _ _ => rfl, fun l h1 h2 => by omega⟩
  | succ c ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hB₀ : (List.range' i c).foldl (fun (B : ℕ → ℕ → ℝ) (j : ℕ) =>
      Function.update B i (Function.update (B i) j (B (i - 1) (j - 1) + e j))) B = B₀ at ih1 ih2
    have hprev : B₀ (i - 1) (i + 1 * c - 1) = B (i - 1) (i + 1 * c - 1) :=
      ih1 _ _ (Or.inl (by omega))
    refine ⟨fun k l hkl => ?_, fun l h1 h2 => ?_⟩
    · by_cases hk : k = i
      · subst hk
        have hl : l ≠ k + 1 * c := by omega
        rw [Function.update_self, Function.update_of_ne hl]
        exact ih1 _ _ (by omega)
      · rw [Function.update_of_ne hk]
        exact ih1 _ _ (Or.inl hk)
    · rw [Function.update_self]
      by_cases hl : l = i + 1 * c
      · subst hl
        rw [Function.update_self, hprev]
      · rw [Function.update_of_ne hl]
        exact ih2 l h1 (by omega)

/-- If $g$ has the first row $(\gamma, v_{n-1}, \dots, v_1)$ of Trench's algorithm on row $0$ and
satisfies the recursion (4.7.5) on the wedge, then the loop of Trench's algorithm reproduces $g$
on the wedge $i \le j$, $i + j \le n - 1$ (indices from $0$). -/
private theorem trenchWedge_eq {n : ℕ} (hn : 1 ≤ n) {γ : ℝ} {v : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    (h0 : ∀ j, j ≤ n - 1 → g 0 j = if j = 0 then γ else v (n - 1 - j))
    (hrec : ∀ i j, 1 ≤ i → i ≤ j → i + j ≤ n - 1 →
      g i j = g (i - 1) (j - 1) + (v (n - 1 - j) * v (n - 1 - i) - v (i - 1) * v (j - 1)) / γ)
    (i j : ℕ) (hij : i ≤ j) (hw : i + j ≤ n - 1) : trenchWedge n γ v i j = g i j := by
  -- the invariant after the rows `1, …, c`
  suffices H : ∀ c, c ≤ (n - 1) / 2 → ∀ i j, i ≤ c → i ≤ j → i + j ≤ n - 1 →
      (List.range' 1 c).foldl (trenchStep n γ v) (trenchRow0 n γ v) i j = g i j from
    H _ le_rfl i j (by omega) hij hw
  intro c
  induction c with
  | zero =>
    intro _ i j hi _ hw
    obtain rfl : i = 0 := by omega
    rw [show List.range' 1 0 = [] from rfl, List.foldl_nil, trenchRow0, Function.update_self,
      h0 j (by omega)]
    split_ifs <;> first | rfl | omega
  | succ c ih =>
    intro hc i j hi hij hw
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range' 1 c).foldl (trenchStep n γ v) (trenchRow0 n γ v) = B₀ at ih ⊢
    have hrow := foldl_trenchRow (1 + 1 * c) (by omega)
      (fun j => (v (n - 1 - j) * v (n - 1 - (1 + 1 * c)) - v (1 + 1 * c - 1) * v (j - 1)) / γ)
      B₀ (n - 2 * (1 + 1 * c))
    beta_reduce at hrow
    rw [trenchStep]
    rcases Nat.lt_or_ge i (c + 1) with hic | hic
    · rw [hrow.1 i j (Or.inl (by omega))]
      exact ih (by omega) i j (by omega) hij hw
    · obtain rfl : i = c + 1 := by omega
      rw [show c + 1 = 1 + 1 * c by ring, hrow.2 j (by omega) (by omega),
        ih (by omega) (1 + 1 * c - 1) (j - 1) (by omega) (by omega) (by omega),
        hrec (1 + 1 * c) j (by omega) (by omega) (by omega)]

/-- **Algorithm 4.7.3** of [golub2013matrix], exact correctness. Let $r_0 = 1$ and let $T_n$ be
positive definite. In exact arithmetic, the matrix $B$ that Algorithm 4.7.3 returns agrees with
$T_n^{-1}$ on the upper wedge:
$$b_{ij} = (T_n^{-1})_{ij} \qquad \text{for } i \le j, \; i + j \le n + 1,$$
with indices from $1$ as in the source.

In the Lean statement the indices start at $0$, and the wedge is $i \le j$, $i + j \le n - 1$.
The other entries of $T_n^{-1}$ follow by symmetry and persymmetry
(`GolubVanLoan.Chapter04.isPersymmetric_inv_of_isToeplitz`). The first row is (4.7.4) read
through persymmetry, and each further entry is (4.7.5) applied to the reflected entry. -/
theorem algorithm_4_7_3_spec {r : ℕ → ℝ} (hr : r 0 = 1) (hT : (symmToeplitz n r).PosDef)
    (i j : Fin n) (hij : i ≤ j) (hw : (i : ℕ) + j ≤ n - 1) :
    Id.run (algorithm_4_7_3 pure n r) i j = (symmToeplitz n r)⁻¹ i j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.isLt; omega⟩
  have hβ : ∀ j < m + 1, Durbin.beta r j ≠ 0 := fun j hj => (Durbin.beta_pos hr hT j hj).ne'
  have hP : (symmToeplitz (m + 1) r)⁻¹.IsPersymmetric := (isPersymmetric_symmToeplitz _ r).inv
  have hc := Trench.inv_symmToeplitz_last hr hβ
  set G := (symmToeplitz (m + 1) r)⁻¹ with hG
  -- the exact quantities of the algorithm
  have hy := algorithm_4_7_1_id_eq_sol (r := r) (m + 1 - 1) fun j hj => hβ j (by omega)
  have hyv : (fun j => if h : j < m + 1 - 1 then
      Id.run (algorithm_4_7_1 pure (m + 1 - 1) r) ⟨j, h⟩ else 0) = Durbin.sol r m := by
    funext j
    rw [hy]
    split_ifs with h
    · rfl
    · exact (Durbin.sol_of_le r (by omega)).symm
  have hγ : trenchGamma (m + 1) r (Durbin.sol r m) = Trench.gamma r m := by
    rw [trenchGamma, zero_add, sum_map_range, Nat.add_sub_cancel]
    rfl
  rw [algorithm_4_7_3_id, hyv, of_apply, hγ]
  -- the book's `v` is `lastCol`
  generalize hvdef : trenchV (m + 1) (Trench.gamma r m) (Durbin.sol r m) = v
  have hv : ∀ a : Fin m, v a = Trench.lastCol r m a := fun a => by
    rw [← hvdef, trenchV, foldl_range_update]
    simp only [show (a : ℕ) < m + 1 - 1 by omega, ↓reduceIte, Trench.lastCol, Pi.smul_apply,
      exchange_mulVec_apply, smul_eq_mul, Fin.val_rev]
    congr 2
    omega
  have hcol : ∀ a : Fin m, G a.castSucc (Fin.last m) = Trench.lastCol r m a := fun a => by
    have := congrFun hc a.castSucc
    simpa only [Fin.snoc_castSucc] using this
  have hlast : G (Fin.last m) (Fin.last m) = Trench.gamma r m := by
    have := congrFun hc (Fin.last m)
    simpa only [Fin.snoc_last] using this
  -- persymmetry of `T⁻¹`, entrywise on `ℕ` indices
  have hper : ∀ a b (ha : a < m + 1) (hb : b < m + 1),
      G ⟨a, ha⟩ ⟨b, hb⟩ = G ⟨m - b, by omega⟩ ⟨m - a, by omega⟩ := fun a b ha hb => by
    rw [← hP ⟨a, ha⟩ ⟨b, hb⟩]
    congr 1 <;> ext <;> simp [Fin.val_rev]
  set g : ℕ → ℕ → ℝ := fun a b => if h : a < m + 1 ∧ b < m + 1 then
    G ⟨a, h.1⟩ ⟨b, h.2⟩ else 0 with hgdef
  have hg : ∀ a b (ha : a < m + 1) (hb : b < m + 1), g a b = G ⟨a, ha⟩ ⟨b, hb⟩ :=
    fun a b ha hb => by rw [hgdef]; simp [ha, hb]
  have key := trenchWedge_eq (n := m + 1) (γ := Trench.gamma r m) (v := v) (g := g)
    (by omega) ?_ ?_ i j (Fin.le_iff_val_le_val.1 hij) hw
  · rw [key, hg _ _ i.isLt j.isLt]
  · -- the first row
    intro b hb
    rw [hg 0 b (by omega) (by omega), hper 0 b (by omega) (by omega)]
    split_ifs with hb0
    · subst hb0
      rw [← hlast]
      rfl
    · have := hcol ⟨m - b, by omega⟩
      rw [← hv] at this
      rw [show m + 1 - 1 - b = m - b by omega, ← this]
      rfl
  · -- the recursion (4.7.5), through persymmetry
    intro a b ha hab hw'
    rw [hg a b (by omega) (by omega), hper a b (by omega) (by omega),
      hg (a - 1) (b - 1) (by omega) (by omega)]
    have h475 := Trench.inv_symmToeplitz_apply_succ hr hβ ⟨m - b, by omega⟩ ⟨m - a, by omega⟩
    have e1 : (⟨m - b, by omega⟩ : Fin m).castSucc = ⟨m - b, by omega⟩ := rfl
    have e2 : (⟨m - a, by omega⟩ : Fin m).castSucc = ⟨m - a, by omega⟩ := rfl
    have e3 : (Fin.rev (⟨m - a, by omega⟩ : Fin m)).castSucc = ⟨a - 1, by omega⟩ := by
      ext; simp [Fin.val_rev]; omega
    have e4 : (Fin.rev (⟨m - b, by omega⟩ : Fin m)).castSucc = ⟨b - 1, by omega⟩ := by
      ext; simp [Fin.val_rev]; omega
    rw [e1, e2, e3, e4] at h475
    rw [← hG] at h475
    rw [h475, ← hv, ← hv, ← hv, ← hv]
    have f1 : ((⟨m - b, by omega⟩ : Fin m) : ℕ) = m + 1 - 1 - b := by
      change m - b = m + 1 - 1 - b; omega
    have f2 : ((⟨m - a, by omega⟩ : Fin m) : ℕ) = m + 1 - 1 - a := by
      change m - a = m + 1 - 1 - a; omega
    have f3 : ((Fin.rev (⟨m - a, by omega⟩ : Fin m)) : ℕ) = a - 1 := by
      simp [Fin.val_rev]; omega
    have f4 : ((Fin.rev (⟨m - b, by omega⟩ : Fin m)) : ℕ) = b - 1 := by
      simp [Fin.val_rev]; omega
    rw [f1, f2, f3, f4]

/-! ### §4.7.6 Stability issues -/

/-- **Section 4.7.6** of [golub2013matrix]. Let $r_0 = 1$ and let $T_n$ be positive definite. Then
the reflection coefficients satisfy
$$|\alpha_k| < 1, \qquad k = 0, \dots, n - 2.$$

The source states that "in exact arithmetic these scalars satisfy $|\alpha_k| < 1$". Here
$\alpha_k$ is `Durbin.alpha r k`, which is Cybenko's $\alpha_{k+1}$; the range $k + 1 < n$ gives
Cybenko's $\alpha_1, \dots, \alpha_{n-1}$. -/
theorem abs_reflection_lt_one {r : ℕ → ℝ} (hr : r 0 = 1) (hT : (symmToeplitz n r).PosDef)
    {k : ℕ} (hk : k + 1 < n) : |Durbin.alpha r k| < 1 :=
  Durbin.abs_alpha_lt_one hr hT hk

/-- **Equation (4.7.6)** of [golub2013matrix], the lower bounds. Let $r_0 = 1$, let $n = m + 1$, and
let $T_n$ be positive definite, with Cybenko's reflection coefficients
$\alpha_1, \dots, \alpha_{n-1}$. Then
$$\max\left\{ \frac{1}{\prod_{j=1}^{n-1} (1 - \alpha_j^2)}, \; \frac{1}{\prod_{j=1}^{n-1} (1 -
  \alpha_j)} \right\} \le \|T_n^{-1}\|_1.$$

Cybenko's $\alpha_j$ is `Durbin.alpha r (j - 1)`, and the norm is `Matrix.lpOpNorm 1`. -/
theorem equation_4_7_6_lower {r : ℕ → ℝ} (hr : r 0 = 1) {m : ℕ}
    (hT : (symmToeplitz (m + 1) r).PosDef) :
    max (1 / ∏ j ∈ range m, (1 - Durbin.alpha r j ^ 2))
        (1 / ∏ j ∈ range m, (1 - Durbin.alpha r j)) ≤
      lpOpNorm 1 (symmToeplitz (m + 1) r)⁻¹ :=
  Durbin.max_inv_prod_le_lpOpNorm_one_inv hr hT

/-- **Equation (4.7.6)** of [golub2013matrix], the upper bound (Cybenko's bound). Let $r_0 = 1$, let
$n = m + 1$, and let $T_n$ be positive definite, with Cybenko's reflection coefficients
$\alpha_1, \dots, \alpha_{n-1}$. Then
$$\|T_n^{-1}\|_1 \le \prod_{j=1}^{n-1} \frac{1 + |\alpha_j|}{1 - |\alpha_j|}.$$

Cybenko's $\alpha_j$ is `Durbin.alpha r (j - 1)`, and the norm is `Matrix.lpOpNorm 1`. -/
theorem equation_4_7_6_upper {r : ℕ → ℝ} (hr : r 0 = 1) {m : ℕ}
    (hT : (symmToeplitz (m + 1) r).PosDef) :
    lpOpNorm 1 (symmToeplitz (m + 1) r)⁻¹ ≤
      ∏ j ∈ range m, (1 + |Durbin.alpha r j|) / (1 - |Durbin.alpha r j|) :=
  Durbin.lpOpNorm_one_inv_le hr hT

/-- **Equation (4.7.7)** of [golub2013matrix]. Let $r_0 = 1$, let $T_n$ be positive definite, and
let $y \in \mathbb{R}^n$ solve the Yule–Walker system $T_n y = -(r_1, \dots, r_n)^T$. If
Cybenko's reflection coefficients $\alpha_1, \dots, \alpha_n$ are all nonnegative, then
$$\|y\|_1 = \prod_{k=1}^{n} (1 + \alpha_k) - 1.$$

Cybenko's $\alpha_k$ is `Durbin.alpha r (k - 1)`, and $\|y\|_1$ is $\sum_i |y_i|$. -/
theorem equation_4_7_7 {r : ℕ → ℝ} (hr : r 0 = 1) (hT : (symmToeplitz n r).PosDef)
    {y : Fin n → ℝ} (hy : symmToeplitz n r *ᵥ y = fun i : Fin _ => -r ((i : ℕ) + 1))
    (hα : ∀ j < n, 0 ≤ Durbin.alpha r j) :
    ∑ i, |y i| = ∏ j ∈ range n, (1 + Durbin.alpha r j) - 1 := by
  rw [eq_sol_of_mulVec_eq hr hT hy, ← Durbin.sum_abs_sol_eq hα]
  exact Fin.sum_univ_eq_sum_range (fun i => |Durbin.sol r n i|) n

/-! ### §4.7.7 A Toeplitz eigenvalue problem -/

/-- If $B$ is symmetric and $\lambda$ is less than every eigenvalue of $B$, then $B - \lambda I$ is
nonsingular. -/
private theorem isUnit_sub_smul_one_of_lt {m : ℕ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) {t : ℝ} (ht : ∀ i, t < hB.eigenvalues i) : IsUnit (B - t • 1) := by
  rw [isUnit_iff_isUnit_det, hB.det_sub_smul_one_eq_prod t]
  refine (Finset.prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 ?_).isUnit
  simpa using (ht i).ne'

/-- The partition of the indices of $T = \begin{bmatrix} 1 & r^T \\ r & B \end{bmatrix}$: the first
index, then the others. -/
private def frontEquiv (m : ℕ) : Fin 1 ⊕ Fin m ≃ Fin (m + 1) :=
  finSumFinEquiv.trans (finCongr (Nat.add_comm 1 m))

private theorem frontEquiv_inl (m : ℕ) (a : Fin 1) : frontEquiv m (Sum.inl a) = 0 := by
  ext
  simp [frontEquiv]

private theorem frontEquiv_inr (m : ℕ) (i : Fin m) : frontEquiv m (Sum.inr i) = i.succ := by
  ext
  simp [frontEquiv]

/-- A symmetric Toeplitz matrix with unit diagonal has the block form $T_{m+1} = \begin{bmatrix} 1 &
r^T \\ r & T_m \end{bmatrix}$. -/
private theorem symmToeplitz_submatrix_frontEquiv {ρ : ℕ → ℝ} (hρ : ρ 0 = 1) (m : ℕ) :
    (symmToeplitz (m + 1) ρ).submatrix (frontEquiv m) (frontEquiv m) =
      fromBlocks 1 (replicateRow (Fin 1) fun i : Fin m => ρ (i + 1))
        (replicateCol (Fin 1) fun i : Fin m => ρ (i + 1)) (symmToeplitz m ρ) := by
  ext (a | a) (b | b)
  · simp [frontEquiv_inl, symmToeplitz_apply, hρ, Subsingleton.elim a b]
  · simp only [submatrix_apply, frontEquiv_inl, frontEquiv_inr, fromBlocks_apply₁₂,
      replicateRow_apply, symmToeplitz_apply, Fin.val_zero, Fin.val_succ]
    congr 1
  · simp only [submatrix_apply, frontEquiv_inl, frontEquiv_inr, fromBlocks_apply₂₁,
      replicateCol_apply, symmToeplitz_apply, Fin.val_zero, Fin.val_succ]
    congr 1
  · simp only [submatrix_apply, frontEquiv_inr, fromBlocks_apply₂₂, symmToeplitz_apply,
      Fin.val_succ]
    congr 1
    omega

/-- **Section 4.7.7** of [golub2013matrix], $\lambda_{\min}(T)$ as a zero of the secular function.
Let $\rho_0 = 1$, let $n = m + 1$, and write the symmetric Toeplitz matrix $T = T_n$ as
$$T = \begin{bmatrix} 1 & r^T \\ r & B \end{bmatrix}, \qquad B = T_{n-1}, \quad r = (\rho_1,
  \dots, \rho_{n-1})^T.$$
Let $\lambda$ be less than every eigenvalue of $B$, and let $(\alpha, y) \neq 0$ satisfy
$T(\alpha, y) = \lambda (\alpha, y)$. Then $\alpha \neq 0$,
$y = -\alpha (B - \lambda I)^{-1} r$, and $\lambda$ is a zero of the secular function
$$f(\lambda) = 1 - \lambda - r^T (B - \lambda I)^{-1} r.$$

Under the hypothesis (4.7.8), $\lambda_{\min}(T) < \lambda_{\min}(B)$, the eigenvalue
$\lambda_{\min}(T)$ satisfies the condition on $\lambda$. The symmetry of $B$ is
`Matrix.IsHermitian`, its eigenvalues are `Matrix.IsHermitian.eigenvalues`, and $f$ is
`Matrix.borderedSecularFunction`.

**Generalization.** The target is any supplied eigenvalue of the normalized symmetric Toeplitz
matrix strictly below the spectrum of the trailing block, with a corresponding nonzero eigenvector.
This singles out the least eigenvalue when it exists, and the hypotheses allow the matrix to be
indefinite.
-/
theorem secular_lambdaMin {ρ : ℕ → ℝ} (hρ : ρ 0 = 1) {m : ℕ}
    (hB : (symmToeplitz m ρ).IsHermitian) {t : ℝ} (ht : ∀ i, t < hB.eigenvalues i)
    {x : Fin (m + 1) → ℝ} (hx0 : x ≠ 0) (hx : symmToeplitz (m + 1) ρ *ᵥ x = t • x) :
    x 0 ≠ 0 ∧
      (fun i : Fin m => x i.succ) =
        -x 0 • ((symmToeplitz m ρ - t • 1)⁻¹ *ᵥ fun i : Fin m => ρ (i + 1)) ∧
      borderedSecularFunction (fun i : Fin m => ρ (i + 1)) (symmToeplitz m ρ) t = 0 := by
  have hU := isUnit_sub_smul_one_of_lt hB ht
  have hxe : x ∘ frontEquiv m = Sum.elim (fun _ : Fin 1 => x 0) fun i => x i.succ := by
    funext a
    rcases a with a | a
    · simp [frontEquiv_inl]
    · simp [frontEquiv_inr]
  have hne : Sum.elim (fun _ : Fin 1 => x 0) (fun i : Fin m => x i.succ) ≠ 0 := by
    rw [← hxe]
    intro h
    apply hx0
    funext i
    simpa using congrFun h ((frontEquiv m).symm i)
  have hmul : fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ)
      (replicateRow (Fin 1) fun i : Fin m => ρ (i + 1))
      (replicateCol (Fin 1) fun i : Fin m => ρ (i + 1)) (symmToeplitz m ρ) *ᵥ
        Sum.elim (fun _ => x 0) (fun i => x i.succ) =
      t • Sum.elim (fun _ => x 0) (fun i => x i.succ) := by
    rw [← symmToeplitz_submatrix_frontEquiv hρ, ← hxe, submatrix_mulVec_equiv,
      Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id, hx]
    rfl
  exact borderedSecularFunction_eq_zero_of_mulVec_eq hU hne hmul

/-- **Section 4.7.7** of [golub2013matrix], the derivatives of the secular function. Let
$B \in \mathbb{R}^{m \times m}$ be symmetric, let $r \in \mathbb{R}^m$, let $f(\lambda) = 1 -
\lambda - r^T (B - \lambda I)^{-1} r$, and let $\lambda$ be less than every eigenvalue of $B$.
Then
$$f'(\lambda) = -1 - \|(B - \lambda I)^{-1} r\|_2^2 \le -1, \qquad f''(\lambda) = -2 r^T (B -
  \lambda I)^{-3} r \le 0.$$

The statement uses neither the Toeplitz structure nor positive definiteness. The function $f$ is
`Matrix.borderedSecularFunction r B`, and $f''$ is the derivative of `deriv f`.

**Generalization.** The formulas hold for an arbitrary symmetric trailing block and vector. The
source derives them for the bordered positive definite Toeplitz system.
-/
theorem secular_deriv {m : ℕ} {r : Fin m → ℝ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) {t : ℝ} (ht : ∀ i, t < hB.eigenvalues i) :
    HasDerivAt (borderedSecularFunction r B)
        (-1 - ((B - t • 1)⁻¹ *ᵥ r) ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r)) t ∧
      -1 - ((B - t • 1)⁻¹ *ᵥ r) ⬝ᵥ ((B - t • 1)⁻¹ *ᵥ r) ≤ -1 ∧
      HasDerivAt (deriv (borderedSecularFunction r B))
        (-2 * r ⬝ᵥ ((B - t • 1)⁻¹ ^ 3 *ᵥ r)) t ∧
      -2 * r ⬝ᵥ ((B - t • 1)⁻¹ ^ 3 *ᵥ r) ≤ 0 := by
  obtain ⟨h1, h2⟩ := hasDerivAt_borderedSecularFunction (r := r) hB fun i => (ht i).ne'
  obtain ⟨h3, h4⟩ := neg_one_sub_dotProduct_le_and_neg_two_mul_dotProduct_nonpos (r := r) hB ht
  exact ⟨h1, h3, h2, h4⟩

open Filter Topology in
/-- **Equations (4.7.9)–(4.7.10)** of [golub2013matrix], Newton's method for $\lambda_{\min}(T)$.
Let $\rho_0 = 1$, let $n = m + 1$, and write $T = T_n = \begin{bmatrix} 1 & r^T \\ r & B
\end{bmatrix}$ with $B = T_{n-1}$ and $r = (\rho_1, \dots, \rho_{n-1})^T$. Let $\lambda$ be an
eigenvalue of $T$, with an eigenvector $x \neq 0$, that is less than every eigenvalue of $B$,
and let $\lambda^{(0)}$ satisfy
$$\lambda \le \lambda^{(0)} < \lambda_{\min}(B).$$
Let $\lambda^{(k+1)} = \lambda^{(k)} - f(\lambda^{(k)})/f'(\lambda^{(k)})$ be Newton's iteration
for the secular function $f$. Then $\lambda \le \lambda^{(k+1)} \le \lambda^{(k)}$ for every
$k$, and $\lambda^{(k)} \to \lambda$.

The source states that the iteration converges to $\lambda_{\min}(T)$ monotonically from the
right. Under the hypothesis (4.7.8), $\lambda_{\min}(T)$ is the only eigenvalue of $T$ below the
spectrum of $B$, so $\lambda = \lambda_{\min}(T)$. The Newton step is `Newton.scalarStep` with
$f'$ given by `deriv`, and $f$ is `Matrix.borderedSecularFunction`.

**Generalization.** The target is any supplied eigenvalue of the normalized symmetric Toeplitz
matrix strictly below the spectrum of the trailing block, with a corresponding nonzero eigenvector.
This singles out the least eigenvalue when it exists, and the hypotheses allow the matrix to be
indefinite.
-/
theorem equation_4_7_10 {ρ : ℕ → ℝ} (hρ : ρ 0 = 1) {m : ℕ}
    (hB : (symmToeplitz m ρ).IsHermitian) {t : ℝ} (ht : ∀ i, t < hB.eigenvalues i)
    {x : Fin (m + 1) → ℝ} (hx0 : x ≠ 0) (hx : symmToeplitz (m + 1) ρ *ᵥ x = t • x) {x₀ : ℝ}
    (htx : t ≤ x₀) (hx₀ : ∀ i, x₀ < hB.eigenvalues i) :
    (∀ k, t ≤ (Newton.scalarStep (borderedSecularFunction (fun i : Fin m => ρ (i + 1))
          (symmToeplitz m ρ)) (deriv (borderedSecularFunction (fun i : Fin m => ρ (i + 1))
          (symmToeplitz m ρ))))^[k + 1] x₀ ∧
        (Newton.scalarStep (borderedSecularFunction (fun i : Fin m => ρ (i + 1))
          (symmToeplitz m ρ)) (deriv (borderedSecularFunction (fun i : Fin m => ρ (i + 1))
          (symmToeplitz m ρ))))^[k + 1] x₀ ≤
        (Newton.scalarStep (borderedSecularFunction (fun i : Fin m => ρ (i + 1))
          (symmToeplitz m ρ)) (deriv (borderedSecularFunction (fun i : Fin m => ρ (i + 1))
          (symmToeplitz m ρ))))^[k] x₀) ∧
      Tendsto (fun k => (Newton.scalarStep (borderedSecularFunction
          (fun i : Fin m => ρ (i + 1)) (symmToeplitz m ρ))
          (deriv (borderedSecularFunction (fun i : Fin m => ρ (i + 1))
          (symmToeplitz m ρ))))^[k] x₀) atTop (𝓝 t) :=
  tendsto_newton_borderedSecularFunction hB (secular_lambdaMin hρ hB ht hx0 hx).2.2 htx hx₀

/-- **Section 4.7.7** of [golub2013matrix], the Newton step. Let $B \in \mathbb{R}^{m \times m}$ be
symmetric, let $r \in \mathbb{R}^m$, let $\lambda$ be less than every eigenvalue of $B$, and let
$w$ solve the shifted Yule–Walker system $(B - \lambda I) w = -r$. Then the Newton step for the
secular function $f(\lambda) = 1 - \lambda - r^T (B - \lambda I)^{-1} r$ is
$$\lambda - \frac{f(\lambda)}{f'(\lambda)} = \lambda + \frac{1 + r^T w - \lambda}{1 + w^T w}.$$

The Newton step is `Newton.scalarStep` with $f'$ given by `deriv`, and $f$ is
`Matrix.borderedSecularFunction r B`.

**Generalization.** The formulas hold for an arbitrary symmetric trailing block and vector. The
source derives them for the bordered positive definite Toeplitz system.
-/
theorem newton_step_eq {m : ℕ} {r : Fin m → ℝ} {B : Matrix (Fin m) (Fin m) ℝ}
    (hB : B.IsHermitian) {t : ℝ} (ht : ∀ i, t < hB.eigenvalues i) {w : Fin m → ℝ}
    (hw : (B - t • 1) *ᵥ w = -r) :
    Newton.scalarStep (borderedSecularFunction r B) (deriv (borderedSecularFunction r B)) t =
      t + (1 + r ⬝ᵥ w - t) / (1 + w ⬝ᵥ w) := by
  have hU := isUnit_sub_smul_one_of_lt hB ht
  have hw' : (B - t • 1)⁻¹ *ᵥ r = -w := by
    rw [← neg_neg r, ← hw, mulVec_neg, mulVec_mulVec,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hU), one_mulVec]
  have hd := ((secular_deriv (r := r) hB ht).1).deriv
  have hpos : 0 < 1 + w ⬝ᵥ w := by
    have : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith
  rw [Newton.scalarStep, hd, borderedSecularFunction, hw']
  simp only [dotProduct_neg, neg_dotProduct, neg_neg]
  have hne : (-1 - w ⬝ᵥ w) = -(1 + w ⬝ᵥ w) := by ring
  rw [hne, div_neg]
  field_simp
  ring

/-- **Section 4.7.7** of [golub2013matrix], Durbin's $\beta$ and definiteness. Let $r_0 = 1$ and
$k \in \mathbb{N}$. Then $T_{k+1}$ is positive definite if and only if $\beta_j > 0$ for
$j = 0, \dots, k$. In particular, if $\beta_j > 0$ for $j < k$ and $\beta_k \le 0$, then $T_k$
is positive definite and $T_{k+1}$ is not.

The source applies this to $T_\lambda$: "if $\beta_k \le 0$ and $\beta_1, \dots, \beta_{k-1}$
are all positive, then $T(1{:}k, 1{:}k)$ is positive definite but $T(1{:}k{+}1, 1{:}k{+}1)$ is
not". Here $T_k$ is the leading $k \times k$ block $T(1{:}k, 1{:}k)$, and $\beta_j$ is
`Durbin.beta r j`.

**Generalization.** Lean includes converses for the definiteness criteria and proves that the index
of the first nonpositive denominator is antitone for shifts below one.
-/
theorem durbin_beta_pos_iff {r : ℕ → ℝ} (hr : r 0 = 1) (k : ℕ) :
    ((symmToeplitz (k + 1) r).PosDef ↔ ∀ j ≤ k, 0 < Durbin.beta r j) ∧
      ((∀ j < k, 0 < Durbin.beta r j) → Durbin.beta r k ≤ 0 →
        (symmToeplitz k r).PosDef ∧ ¬(symmToeplitz (k + 1) r).PosDef) := by
  refine ⟨?_, fun hpos hk => ⟨(Durbin.posDef_symmToeplitz_iff hr).2 hpos, fun h => ?_⟩⟩
  · rw [Durbin.posDef_symmToeplitz_iff hr]
    simp only [Nat.lt_succ_iff]
  · exact absurd hk (not_le.2 ((Durbin.posDef_symmToeplitz_iff hr).1 h k (Nat.lt_succ_self k)))

/-- **Section 4.7.7** of [golub2013matrix], the normalized shift. For a symmetric Toeplitz matrix
$T = (r_{|i-j|})$ with $r_0 = 1$ and a scalar $\lambda$, the matrix
$T_\lambda = (T - \lambda I)/(1 - \lambda)$ is again symmetric Toeplitz with unit diagonal. This
is its sequence of data: $1$ at index $0$, and $r_j/(1 - \lambda)$ at index $j \ge 1$.

At $\lambda = 1$ the division by zero gives $0$.

**Reading.** At shift one the off-diagonal values are zero by totalized division and the diagonal is
fixed at one. The normalized shift in the source requires a nonzero denominator.
-/
noncomputable def shiftedToeplitzSeq (r : ℕ → ℝ) (t : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else r j / (1 - t)

/-- For $\lambda < 1$, $T_k - \lambda I = (1 - \lambda) T_{k,\lambda}$, where $T_{k,\lambda}$ is the
normalized shift of $T_k$. -/
private theorem symmToeplitz_sub_smul_one {r : ℕ → ℝ} (hr : r 0 = 1) {t : ℝ} (ht : t < 1)
    (k : ℕ) :
    symmToeplitz k r - t • (1 : Matrix (Fin k) (Fin k) ℝ) =
      (1 - t) • symmToeplitz k (shiftedToeplitzSeq r t) := by
  have ht' : (1 - t) ≠ 0 := by linarith
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, symmToeplitz_apply, Matrix.one_apply, smul_eq_mul,
    shiftedToeplitzSeq]
  by_cases hij : i = j
  · subst hij
    simp [hr]
  · have hd : ((i : ℤ) - j).natAbs ≠ 0 := by
      intro h
      apply hij
      ext
      omega
    simp only [hij, hd, ↓reduceIte, mul_zero, sub_zero]
    field_simp

/-- For $\lambda < 1$, $T_k - \lambda I$ is positive definite if and only if the normalized shift
$T_{k,\lambda}$ is positive definite. -/
private theorem posDef_sub_smul_one_iff {r : ℕ → ℝ} (hr : r 0 = 1) {t : ℝ} (ht : t < 1)
    (k : ℕ) :
    (symmToeplitz k r - t • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef ↔
      (symmToeplitz k (shiftedToeplitzSeq r t)).PosDef := by
  rw [symmToeplitz_sub_smul_one hr ht]
  have hc : 0 < 1 - t := by linarith
  refine ⟨fun h => ?_, fun h => h.smul hc⟩
  have := h.smul (inv_pos.2 hc)
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this

open Classical in
/-- **Section 4.7.7** of [golub2013matrix], the index $m(\lambda)$ of (4.7.11). Apply Durbin's
recurrence (4.7.1) to the normalized shift $T_\lambda = (T - \lambda I)/(1 - \lambda)$ of
$T = T_n$. Then **$m(\lambda)$** is the least $k < n$ with $\beta_k \le 0$, and $n$ if there is
no such $k$.

The source defines $m(\lambda)$ as the index of the first nonpositive $\beta$. The data of
$T_\lambda$ are `GolubVanLoan.Chapter04.shiftedToeplitzSeq r λ`. Since $\beta_0 = 1$,
$m(\lambda) \ge 1$ when $n \ge 1$.

**Reading.** Lean returns the matrix size when there is no nonpositive denominator among the
computed indices. The source defines the index as the first failure, and its comparison uses the
no-failure case without giving it a numerical value.
-/
noncomputable def bisectionIndex (n : ℕ) (r : ℕ → ℝ) (t : ℝ) : ℕ :=
  if h : ∃ k, k < n ∧ Durbin.beta (shiftedToeplitzSeq r t) k ≤ 0 then Nat.find h else n

/-- For $j \le n$, $j \le m(\lambda)$ if and only if $\beta_k > 0$ for all $k < j$, where the
$\beta_k$ are Durbin's denominators for $T_\lambda$. -/
private theorem le_bisectionIndex_iff {n : ℕ} {r : ℕ → ℝ} {t : ℝ} {j : ℕ} (hj : j ≤ n) :
    j ≤ bisectionIndex n r t ↔ ∀ k < j, 0 < Durbin.beta (shiftedToeplitzSeq r t) k := by
  classical
  unfold bisectionIndex
  split_ifs with h
  · rw [Nat.le_find_iff]
    refine forall₂_congr fun k hk => ?_
    rw [not_and, not_le]
    exact ⟨fun h' => h' (by omega), fun h' _ => h'⟩
  · refine iff_of_true hj fun k hk => ?_
    by_contra h'
    exact h ⟨k, by omega, not_lt.1 h'⟩

/-- $m(\lambda) \le n$. -/
private theorem bisectionIndex_le (n : ℕ) (r : ℕ → ℝ) (t : ℝ) : bisectionIndex n r t ≤ n := by
  classical
  unfold bisectionIndex
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- For $\lambda < 1$ and $j \le n$, $j \le m(\lambda)$ if and only if $T_j - \lambda I$ is positive
definite. -/
private theorem le_bisectionIndex_iff_posDef {n : ℕ} {r : ℕ → ℝ} (hr : r 0 = 1) {t : ℝ}
    (ht : t < 1) {j : ℕ} (hj : j ≤ n) :
    j ≤ bisectionIndex n r t ↔ (symmToeplitz j r - t • (1 : Matrix (Fin j) (Fin j) ℝ)).PosDef := by
  rw [le_bisectionIndex_iff hj, posDef_sub_smul_one_iff hr ht,
    Durbin.posDef_symmToeplitz_iff (by simp [shiftedToeplitzSeq])]

/-- **Section 4.7.7** of [golub2013matrix], the index $m(\lambda)$ through the shifted matrices. Let
$r_0 = 1$, let $n \ge 1$, let $T = T_n$ and $B = T_{n-1}$, and let $\lambda < 1$. Then:

1. $m(\lambda) \ge n - 1$ if and only if $B - \lambda I$ is positive definite.
2. $m(\lambda) = n - 1$ if and only if $B - \lambda I$ is positive definite and $T - \lambda I$
   is not.
3. $m$ is antitone: if $\lambda \le \lambda' < 1$, then $m(\lambda') \le m(\lambda)$.

The source concludes that "if $m(\lambda^{(0)}) = n - 1$ then $B - \lambda^{(0)} I$ is positive
definite and $T - \lambda^{(0)} I$ is not, thereby establishing (4.7.9)", that is,
$\lambda_{\min}(T) \le \lambda^{(0)} < \lambda_{\min}(B)$. Part 3 shows that the bisection
(4.7.11) keeps $m(R) \le n - 1 \le m(L)$; see `GolubVanLoan.Chapter04.equation_4_7_11` for the
invariant that the source prints. The matrix $B$ is the leading block of $T$; by persymmetry it
is also the trailing block of the source's partition $T = \begin{bmatrix} 1 & r^T \\ r & B
\end{bmatrix}$.

**Generalization.** Lean includes converses for the definiteness criteria and proves that the index
of the first nonpositive denominator is antitone for shifts below one.
-/
theorem bisectionIndex_spec {r : ℕ → ℝ} (hr : r 0 = 1) {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t < 1) :
    (n - 1 ≤ bisectionIndex n r t ↔
      (symmToeplitz (n - 1) r - t • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosDef) ∧
    (bisectionIndex n r t = n - 1 ↔
      (symmToeplitz (n - 1) r - t • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosDef ∧
        ¬(symmToeplitz n r - t • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) ∧
    ∀ t', t ≤ t' → t' < 1 → bisectionIndex n r t' ≤ bisectionIndex n r t := by
  have h1 := le_bisectionIndex_iff_posDef (n := n) hr ht (Nat.sub_le n 1)
  have h2 := le_bisectionIndex_iff_posDef (n := n) hr ht le_rfl
  have hle := bisectionIndex_le n r t
  refine ⟨h1, ⟨fun h => ⟨h1.1 h.ge, fun h' => by have := h2.2 h'; omega⟩,
    fun ⟨hB, hT⟩ => ?_⟩, fun t' htt' ht' => ?_⟩
  · have hge := h1.2 hB
    have hlt : ¬ n ≤ bisectionIndex n r t := fun h => hT (h2.1 h)
    omega
  · -- `T_j − λ'I` positive definite implies `T_j − λI` positive definite
    have key : ∀ j ≤ n, j ≤ bisectionIndex n r t' → j ≤ bisectionIndex n r t := by
      intro j hj h
      rw [le_bisectionIndex_iff_posDef hr ht' hj] at h
      rw [le_bisectionIndex_iff_posDef hr ht hj]
      have hpsd : ((t' - t) • (1 : Matrix (Fin j) (Fin j) ℝ)).PosSemidef :=
        PosDef.one.posSemidef.smul (by linarith)
      have := h.add_posSemidef hpsd
      rwa [show symmToeplitz j r - t' • (1 : Matrix (Fin j) (Fin j) ℝ) + (t' - t) • 1 =
        symmToeplitz j r - t • 1 by rw [sub_smul]; abel] at this
    exact key _ (bisectionIndex_le n r t') le_rfl

/-- The leading $k \times k$ block of $T_N - \lambda I$ is $T_k - \lambda I$. -/
private theorem symmToeplitz_sub_smul_one_submatrix (r : ℕ → ℝ) (t : ℝ) {k N : ℕ} (h : k ≤ N) :
    (symmToeplitz N r - t • (1 : Matrix (Fin N) (Fin N) ℝ)).submatrix (Fin.castLE h)
        (Fin.castLE h) = symmToeplitz k r - t • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  ext i j
  simp only [submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    symmToeplitz_apply, Fin.val_castLE, Fin.castLE_inj]

/-- **Section 4.7.7** of [golub2013matrix], the initial bracket of (4.7.11). Let $r_0 = 1$, let
$n \ge 3$, let $T = T_n$ be positive definite, and let $B = T_{n-1}$. Then
$$0 < \lambda_{\min}(T) \le \lambda_{\min}(B) \le 1 - |r_1|,$$
in the following form, which uses that $\lambda < \lambda_{\min}(A)$ if and only if
$A - \lambda I$ is positive definite:

1. $T - \lambda I$ is positive definite for every $\lambda \le 0$.
2. If $T - \lambda I$ is positive definite, then $B - \lambda I$ is positive definite.
3. If $B - \lambda I$ is positive definite, then $\lambda < 1 - |r_1|$.

**Reading.** The source writes $\lambda_{\min}(T) < \lambda_{\min}(B)$ in the middle, which is
the hypothesis (4.7.8). The theorem proves $\lambda_{\min}(T) \le \lambda_{\min}(B)$, which
holds without (4.7.8).

The source obtains the last bound from $\lambda_{\min}(B) \le
\lambda_{\min}\left(\begin{bmatrix} 1 & r_1 \\ r_1 & 1 \end{bmatrix}\right) = 1 - |r_1|$. -/
theorem lambdaMin_bracket {r : ℕ → ℝ} (hr : r 0 = 1) {n : ℕ} (hn : 3 ≤ n)
    (hT : (symmToeplitz n r).PosDef) :
    (∀ t : ℝ, t ≤ 0 → (symmToeplitz n r - t • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) ∧
    (∀ t : ℝ, (symmToeplitz n r - t • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef →
      (symmToeplitz (n - 1) r - t • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosDef) ∧
    (∀ t : ℝ, (symmToeplitz (n - 1) r - t • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosDef →
      t < 1 - |r 1|) := by
  refine ⟨fun t ht => ?_, fun t h => ?_, fun t h => ?_⟩
  · have hpsd : ((-t) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
      PosDef.one.posSemidef.smul (by linarith)
    have := hT.add_posSemidef hpsd
    rwa [neg_smul, ← sub_eq_add_neg] at this
  · rw [← symmToeplitz_sub_smul_one_submatrix r t (Nat.sub_le n 1)]
    exact h.submatrix (Fin.castLE_injective _)
  · have h2 := h.submatrix (Fin.castLE_injective (show 2 ≤ n - 1 by omega))
    rw [symmToeplitz_sub_smul_one_submatrix] at h2
    -- the test vector `(1, −sign r₁)`
    set s : ℝ := if 0 ≤ r 1 then 1 else -1 with hs
    have hsr : s * r 1 = |r 1| := by
      rw [hs]; split_ifs with h0
      · rw [one_mul, abs_of_nonneg h0]
      · rw [abs_of_neg (not_le.1 h0)]; ring
    have hss : s * s = 1 := by rw [hs]; split_ifs <;> norm_num
    have hx : (![1, -s] : Fin 2 → ℝ) ≠ 0 := fun h0 => by
      simpa using congrFun h0 0
    have hq := h2.dotProduct_mulVec_pos hx
    have e00 : (symmToeplitz 2 r - t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = 1 - t := by
      simp [symmToeplitz_apply, hr]
    have e01 : (symmToeplitz 2 r - t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 = r 1 := by
      simp [symmToeplitz_apply]
    have e10 : (symmToeplitz 2 r - t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 = r 1 := by
      simp [symmToeplitz_apply]
    have e11 : (symmToeplitz 2 r - t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 = 1 - t := by
      simp [symmToeplitz_apply, hr]
    simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_two, e00, e01, e10, e11,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hq
    have hts : t * (s * s) = t := by rw [hss, mul_one]
    nlinarith [hsr, hss, hts]

/-! ### (4.7.11): The bisection for a starting value -/

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Equation (4.7.11)** of [golub2013matrix], the index $m(\lambda)$ as a program. The source
applies Durbin's algorithm to $T_\lambda = (T - \lambda I)/(1 - \lambda)$ and lets $m(\lambda)$
be the index of the first nonpositive $\beta$. The program rounds each entry $r_j/(1 - \lambda)$
of $T_\lambda$, $j = 1, \dots, n$, once, as $\mathrm{fl}(r_j / \mathrm{fl}(1 - \lambda))$. It
then runs the passes of Algorithm 4.7.1 (`GolubVanLoan.Chapter04.durbinStep`) on these entries.
The first pass $p$ whose $\beta_{p+1}$ is nonpositive records the index $p + 1$ and stops the
loop.

The state holds $n$ while no $\beta$ has been nonpositive, and $\beta_0 = 1$.

**Reading.** Lean precomputes the rounded normalized entries and executes the whole Durbin step
before testing the updated denominator. The first failed step therefore still performs its division
and vector updates. The index uses that step's denominator, and no later step is executed.
-/
noncomputable def durbinIndex (n : ℕ) (r : ℕ → ℝ) (t : ℝ) : M ℕ := do
  let c ← rnd (1 - t)
  let ρ ← (List.range n).foldlM (fun (ρ : ℕ → ℝ) (j : ℕ) => do
      let q ← rnd (r (j + 1) / c)
      pure (Function.update ρ (j + 1) q)) (Function.update 0 0 1)
  let st ← (List.range (n - 1)).foldlM (fun (st : ((ℕ → ℝ) × ℝ × ℝ) × ℕ) (p : ℕ) =>
      if st.2 < n then pure st else do
        let s ← durbinStep rnd ρ st.1 p
        pure (s, if s.2.2 ≤ 0 then p + 1 else n))
    ((Function.update 0 0 (-ρ 1), -ρ 1, 1), n)
  pure st.2

/-- **Equation (4.7.11)** of [golub2013matrix], the bisection for a starting value $\lambda^{(0)}$
of Newton's method:
```
L = 0; R = 1 − |r₁|; μ = (L + R)/2
while m(μ) ≠ n − 1
    if m(μ) < n − 1
        R = μ
    else
        L = μ
    end
    μ = (L + R)/2
end
λ⁽⁰⁾ = μ
```
The loop runs on the state $(L, R, \mu, \mathit{done})$ for at most `fuel` passes, as in
convention 3 of the library index. Each pass computes $m(\mu)$ once, by
`GolubVanLoan.Chapter04.durbinIndex`. The value $\lambda^{(0)}$ is the component $\mu$ of the
returned state. Every arithmetic result is rounded: $1 - |r_1|$, each sum $L + R$ and each
halving.

**Reading.** The source uses a while loop that exits on the desired index. Lean bounds the number of
passes, returns the current bracket and midpoint, and marks whether the stopping test succeeded.
-/
noncomputable def durbinBisection (n : ℕ) (r : ℕ → ℝ) (fuel : ℕ) : M (ℝ × ℝ × ℝ × Bool) := do
  let R ← rnd (1 - |r 1|)
  let s ← rnd (0 + R)
  let μ ← rnd (s / 2)
  (List.range fuel).foldlM (fun (st : ℝ × ℝ × ℝ × Bool) (_ : ℕ) =>
      if st.2.2.2 then pure st else do
        let m ← durbinIndex rnd n r st.2.2.1
        if m = n - 1 then pure (st.1, st.2.1, st.2.2.1, true) else do
          let L := if m < n - 1 then st.1 else st.2.2.1
          let R := if m < n - 1 then st.2.2.1 else st.2.1
          let s ← rnd (L + R)
          let μ ← rnd (s / 2)
          pure (L, R, μ, false))
    (0, R, μ, false)

end Programs

/-- Writing the entries $j + 1$, $j < m$, of a vector by values $g_{j+1}$ fixed in advance gives the
vector with entries $g_i$ for $1 \le i \le m$ and unchanged entries otherwise. -/
private theorem foldl_range_update_succ (g : ℕ → ℝ) (m : ℕ) (y : ℕ → ℝ) :
    (List.range m).foldl (fun (z : ℕ → ℝ) (j : ℕ) => Function.update z (j + 1) (g (j + 1))) y =
      fun i => if 1 ≤ i ∧ i ≤ m then g i else y i := by
  induction m with
  | zero =>
    funext i
    simp only [List.range_zero, List.foldl_nil]
    rw [ite_eq_right (by omega)]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih]
    funext i
    simp only [List.foldl_cons, List.foldl_nil, Function.update_apply]
    by_cases h : i = m + 1
    · simp [h]
    · rw [ite_eq_right h]
      by_cases h' : 1 ≤ i ∧ i ≤ m
      · rw [ite_eq_left h', ite_eq_left (by omega)]
      · rw [ite_eq_right h', ite_eq_right (by omega)]

/-- If $\beta_j \neq 0$ for $j \le p$, then one exact pass of Durbin's algorithm takes
$(y^{(p+1)}, \alpha_p, \beta_p)$ to $(y^{(p+2)}, \alpha_{p+1}, \beta_{p+1})$. -/
private theorem durbinExactStep_sol {r : ℕ → ℝ} {p : ℕ} (hβ : ∀ j < p + 1, Durbin.beta r j ≠ 0) :
    durbinExactStep r (Durbin.sol r (p + 1), Durbin.alpha r p, Durbin.beta r p) p =
      (Durbin.sol r (p + 2), Durbin.alpha r (p + 1), Durbin.beta r (p + 1)) := by
  have h := durbin_foldl (r := r) (p + 1) hβ
  rw [List.range_succ, List.foldl_append, durbin_foldl p fun j hj => hβ j (by omega)] at h
  simpa using h

/-- **Equation (4.7.11)** of [golub2013matrix], the exact index $m(\lambda)$. For every $n$, every
sequence $r$ and every $\lambda$, the exact run of `GolubVanLoan.Chapter04.durbinIndex` is
$m(\lambda)$, `GolubVanLoan.Chapter04.bisectionIndex n r λ`.

**Reading.** Lean returns the matrix size when there is no nonpositive denominator among the
computed indices. The source defines the index as the first failure, and its comparison uses the
no-failure case without giving it a numerical value.
-/
theorem durbinIndex_spec (n : ℕ) (r : ℕ → ℝ) (t : ℝ) :
    Id.run (durbinIndex pure n r t) = bisectionIndex n r t := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℝ,
      ρ = fun i => if 1 ≤ i ∧ i ≤ n then r i / (1 - t) else Function.update (0 : ℕ → ℝ) 0 1 i :=
    ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ((ℕ → ℝ) × ℝ × ℝ) × ℕ → ℕ → Id (((ℕ → ℝ) × ℝ × ℝ) × ℕ),
      F = (fun st p => if st.2 < n then pure st else do
        let s ← durbinStep (M := Id) pure ρ st.1 p
        pure (s, if s.2.2 ≤ 0 then p + 1 else n)) := ⟨_, rfl⟩
  obtain ⟨I₀, hI₀⟩ : ∃ I₀ : ((ℕ → ℝ) × ℝ × ℝ) × ℕ,
      I₀ = ((Function.update (0 : ℕ → ℝ) 0 (-ρ 1), -ρ 1, (1 : ℝ)), n) := ⟨_, rfl⟩
  have hrun : Id.run (durbinIndex pure n r t) =
      (Id.run ((List.range (n - 1)).foldlM F I₀)).2 := by
    have hρfold : Id.run ((List.range n).foldlM (fun (ρ : ℕ → ℝ) (j : ℕ) => do
        let q ← (pure (r (j + 1) / (1 - t)) : Id ℝ)
        pure (Function.update ρ (j + 1) q)) (Function.update 0 0 1)) = ρ := by
      rw [List.idRun_foldlM, hρ]
      exact foldl_range_update_succ (fun j => r j / (1 - t)) n _
    rw [hF, hI₀, ← hρfold]
    rfl
  have hρ' : ∀ j, 1 ≤ j → j ≤ n → ρ j = shiftedToeplitzSeq r t j := fun j h1 h2 => by
    rw [hρ]
    dsimp only
    rw [ite_eq_left ⟨h1, h2⟩, shiftedToeplitzSeq, ite_eq_right (by omega)]
  have hβ : ∀ k, k < n → Durbin.beta ρ k = Durbin.beta (shiftedToeplitzSeq r t) k :=
    fun k hk => Durbin.beta_congr fun j h1 h2 => hρ' j h1 (by omega)
  -- the invariant of the pass loop
  let Inv : ℕ → ((ℕ → ℝ) × ℝ × ℝ) × ℕ → Prop := fun q st =>
    (st.2 = n ∧ (∀ k ≤ q, 0 < Durbin.beta ρ k) ∧
        st.1 = (Durbin.sol ρ (q + 1), Durbin.alpha ρ q, Durbin.beta ρ q)) ∨
      (st.2 < n ∧ (∀ k < st.2, 0 < Durbin.beta ρ k) ∧ Durbin.beta ρ st.2 ≤ 0)
  have h0 : Inv 0 I₀ := by
    rw [hI₀]
    refine Or.inl ⟨rfl, fun k hk => ?_, ?_⟩
    · rw [Nat.le_zero.1 hk, Durbin.beta_zero]
      exact one_pos
    · exact (durbin_foldl (r := ρ) 0 fun j hj => absurd hj (Nat.not_lt_zero _))
  have key := List.idRun_foldlM_induction' (List.range (n - 1)) Inv h0 (f := F)
    fun q hq st hst => by
      have hq' : q < n - 1 := by simpa using hq
      rw [hF]
      simp only [List.getElem_range]
      rcases hst with ⟨hn, hpos, hst⟩ | ⟨hlt, hpos, hle⟩
      · rw [ite_eq_right (show ¬ st.2 < n by omega), Id.run_bind, durbinStep_id, hst,
          durbinExactStep_sol fun j hj => (hpos j (by omega)).ne']
        by_cases hb : Durbin.beta ρ (q + 1) ≤ 0
        · rw [ite_eq_left hb]
          exact Or.inr ⟨show q + 1 < n by omega,
            fun k (hk : k < q + 1) => hpos k (by omega), hb⟩
        · rw [ite_eq_right hb]
          refine Or.inl ⟨rfl, fun k hk => ?_, rfl⟩
          rcases Nat.lt_or_eq_of_le hk with hk | rfl
          · exact hpos k (by omega)
          · exact not_le.1 hb
      · rw [ite_eq_left hlt]
        exact Or.inr ⟨hlt, hpos, hle⟩
  rw [List.length_range] at key
  rw [hrun]
  generalize Id.run ((List.range (n - 1)).foldlM F I₀) = S at key ⊢
  rcases key with ⟨hn, hpos, -⟩ | ⟨hlt, hpos, hle⟩
  · rw [hn]
    refine le_antisymm ?_ (bisectionIndex_le n r t)
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]
      exact Nat.zero_le _
    · exact (le_bisectionIndex_iff le_rfl).2 fun k hk => by
        rw [← hβ k hk]
        exact hpos k (by omega)
  · refine le_antisymm ((le_bisectionIndex_iff hlt.le).2 fun k hk => ?_) ?_
    · rw [← hβ k (by omega)]
      exact hpos k hk
    · by_contra hgt
      have := ((le_bisectionIndex_iff (Nat.succ_le_of_lt hlt)).1
        (Nat.succ_le_of_lt (not_le.1 hgt))) S.2
        (Nat.lt_succ_self _)
      rw [← hβ S.2 hlt] at this
      exact absurd hle (not_le.2 this)

/-- **Equation (4.7.11)** of [golub2013matrix], exact correctness of the bisection. Let $r_0 = 1$,
let $n \ge 3$, let $T = T_n$ be positive definite, and let $B = T_{n-1}$. For every bound `fuel`
on the number of passes, the exact run of `GolubVanLoan.Chapter04.durbinBisection` returns a
state $(L, R, \mu, \mathit{done})$ that satisfies:

1. $L < R$;
2. $m(L) \ge n - 1$, which is equivalent to: $B - LI$ is positive definite;
3. $B - RI$ is not positive definite, which for $R < 1$ is equivalent to $m(R) < n - 1$;
4. if $\mathit{done}$ holds, then $m(\mu) = n - 1$, $B - \mu I$ is positive definite and
   $T - \mu I$ is not, so that $\lambda^{(0)} = \mu$ satisfies (4.7.9), $\lambda_{\min}(T) \le
   \lambda^{(0)} < \lambda_{\min}(B)$.

**Correction.** The source prints the invariant $m(L) \le n - 1 \le m(R)$. Since $m$ is antitone
(`GolubVanLoan.Chapter04.bisectionIndex_spec`), the update rule maintains the reverse,
$m(R) \le n - 1 \le m(L)$, which parts 2 and 3 state.

The theorem does not state that some finite `fuel` suffices for $\mathit{done}$, although the
bracket halves in every pass. -/
theorem equation_4_7_11 {r : ℕ → ℝ} (hr : r 0 = 1) {n : ℕ} (hn : 3 ≤ n)
    (hT : (symmToeplitz n r).PosDef) (fuel : ℕ) :
    (Id.run (durbinBisection pure n r fuel)).1 < (Id.run (durbinBisection pure n r fuel)).2.1 ∧
      n - 1 ≤ bisectionIndex n r (Id.run (durbinBisection pure n r fuel)).1 ∧
      ¬(symmToeplitz (n - 1) r - (Id.run (durbinBisection pure n r fuel)).2.1 •
        (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosDef ∧
      ((Id.run (durbinBisection pure n r fuel)).2.2.2 = true →
        bisectionIndex n r (Id.run (durbinBisection pure n r fuel)).2.2.1 = n - 1 ∧
        (symmToeplitz (n - 1) r - (Id.run (durbinBisection pure n r fuel)).2.2.1 •
          (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosDef ∧
        ¬(symmToeplitz n r - (Id.run (durbinBisection pure n r fuel)).2.2.1 •
          (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) := by
  obtain ⟨hb1, hb2, hb3⟩ := lambdaMin_bracket hr hn hT
  obtain ⟨F, hF⟩ : ∃ F : ℝ × ℝ × ℝ × Bool → ℕ → Id (ℝ × ℝ × ℝ × Bool),
      F = (fun st _ => if st.2.2.2 then pure st else do
        let m ← durbinIndex (M := Id) pure n r st.2.2.1
        if m = n - 1 then pure (st.1, st.2.1, st.2.2.1, true) else do
          let L := if m < n - 1 then st.1 else st.2.2.1
          let R := if m < n - 1 then st.2.2.1 else st.2.1
          let s ← (pure (L + R) : Id ℝ)
          let μ ← (pure (s / 2) : Id ℝ)
          pure (L, R, μ, false)) := ⟨_, rfl⟩
  have hrun : Id.run (durbinBisection pure n r fuel) =
      Id.run ((List.range fuel).foldlM F (0, 1 - |r 1|, (0 + (1 - |r 1|)) / 2, false)) := by
    rw [hF]
    rfl
  rw [hrun]
  -- the invariant of the loop
  let Inv : ℕ → ℝ × ℝ × ℝ × Bool → Prop := fun _ st =>
    st.1 < st.2.1 ∧ st.2.1 ≤ 1 ∧
      (symmToeplitz (n - 1) r - st.1 • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosDef ∧
      ¬(symmToeplitz (n - 1) r - st.2.1 • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosDef ∧
      (st.2.2.2 = false → st.2.2.1 = (st.1 + st.2.1) / 2) ∧
      (st.2.2.2 = true → bisectionIndex n r st.2.2.1 = n - 1 ∧
        (symmToeplitz (n - 1) r - st.2.2.1 • (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosDef ∧
        ¬(symmToeplitz n r - st.2.2.1 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef)
  have hB0 : (symmToeplitz (n - 1) r - (0 : ℝ) •
      (1 : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ)).PosDef := hb2 0 (hb1 0 le_rfl)
  have hR0 : 0 < 1 - |r 1| := hb3 0 hB0
  have h0 : Inv 0 (0, 1 - |r 1|, (0 + (1 - |r 1|)) / 2, false) :=
    ⟨hR0, by linarith [abs_nonneg (r 1)], hB0, fun h => lt_irrefl _ (hb3 _ h),
      fun _ => rfl, fun h => absurd h (by simp)⟩
  have key := List.idRun_foldlM_induction' (List.range fuel) Inv h0 (f := F) fun q _ st hst => by
    obtain ⟨L, R, μ, done⟩ := st
    obtain ⟨hLR, hR1, hL, hR, hμ, hdone⟩ := hst
    rw [hF]
    cases done with
    | true => exact ⟨hLR, hR1, hL, hR, hμ, hdone⟩
    | false =>
      have hμ' : μ = (L + R) / 2 := hμ rfl
      have hμ1 : μ < 1 := by rw [hμ']; linarith
      obtain ⟨hs1, hs2, -⟩ := bisectionIndex_spec hr (by omega : 1 ≤ n) hμ1
      simp only [Bool.false_eq_true, ↓reduceIte, Id.run_bind, durbinIndex_spec]
      by_cases hm : bisectionIndex n r μ = n - 1
      · rw [ite_eq_left hm]
        exact ⟨hLR, hR1, hL, hR, fun h => absurd h (by simp), fun _ => ⟨hm, hs2.1 hm⟩⟩
      · rw [ite_eq_right hm]
        by_cases hlt : bisectionIndex n r μ < n - 1
        · simp only [ite_eq_left hlt, Id.run_pure, Id.run_bind]
          refine (show L < μ ∧ μ ≤ 1 ∧ _ ∧ _ ∧ _ ∧ _ from ?_)
          exact ⟨by rw [hμ']; linarith, hμ1.le, hL, fun h => by have := hs1.2 h; omega,
            fun _ => rfl, fun h => absurd h (by simp)⟩
        · simp only [ite_eq_right hlt, Id.run_pure, Id.run_bind]
          refine (show μ < R ∧ R ≤ 1 ∧ _ ∧ _ ∧ _ ∧ _ from ?_)
          exact ⟨by rw [hμ']; linarith, hR1, hs1.1 (by omega), hR, fun _ => rfl,
            fun h => absurd h (by simp)⟩
  rw [List.length_range] at key
  generalize Id.run ((List.range fuel).foldlM F (0, 1 - |r 1|, (0 + (1 - |r 1|)) / 2, false)) = S
    at key ⊢
  obtain ⟨hLR, -, hL, hR, -, hdone⟩ := key
  refine ⟨hLR, ?_, hR, hdone⟩
  have hL1 : S.1 < 1 := by
    have := hb3 _ hL
    linarith [abs_nonneg (r 1)]
  exact (bisectionIndex_spec hr (by omega : 1 ≤ n) hL1).1.2 hL

/-! ### §4.7.8 Unsymmetric Toeplitz systems -/

/-- **Equations (4.7.12)→(4.7.13)** of [golub2013matrix], the bordering for unsymmetric Toeplitz
systems. Let $\rho : \mathbb{Z} \to \mathbb{R}$ with $\rho_0 = 1$, and let
$T_k = (\rho_{j-i}) \in \mathbb{R}^{k \times k}$, so that $T_{k+1} = \begin{bmatrix} T_k &
\mathcal{E}_k r \\ p^T \mathcal{E}_k & 1 \end{bmatrix}$ with $r_j = \rho_j$ above the diagonal
and $p_j = \rho_{-j}$ below it. Let $y, w, x, b \in \mathbb{R}^k$ and $b_{k+1} \in \mathbb{R}$
satisfy (4.7.12):
$$T_k^T y = -r, \qquad T_k w = -p, \qquad T_k x = b.$$
Let $\alpha, \nu, \mu \in \mathbb{R}$ satisfy
$$\alpha (1 + r^T w) = -(r_{k+1} + r^T \mathcal{E}_k y), \quad \nu (1 + p^T y) = -(p_{k+1} + p^T
  \mathcal{E}_k w), \quad \mu (1 + p^T y) = b_{k+1} - p^T \mathcal{E}_k x.$$
Then the three bordered systems (4.7.13) are solved:
$$T_{k+1}^T \begin{bmatrix} y + \alpha \mathcal{E}_k w \\ \alpha \end{bmatrix} = -(r_1, \dots,
  r_{k+1})^T, \quad T_{k+1} \begin{bmatrix} w + \nu \mathcal{E}_k y \\ \nu \end{bmatrix} =
  -(p_1, \dots, p_{k+1})^T, \quad T_{k+1} \begin{bmatrix} x + \mu \mathcal{E}_k y \\ \mu
  \end{bmatrix} = \begin{bmatrix} b \\ b_{k+1} \end{bmatrix}.$$

The source states that the transition "can be shown" to cost $O(k)$ flops; the formulas are its
Problem P4.7.11. The matrix $T_k$ is `Matrix.toeplitz ρ` on `Fin k`. The scalars are given by
the equations above rather than as quotients, so that no denominator needs to be nonzero.

**Generalization.** The bordered systems hold for any supplied solutions of the smaller systems and
scalars satisfying the cross-multiplied equations. This algebraic result requires no nonsingularity
or existence of a solution for the coefficients.
-/
theorem equation_4_7_13 {ρ : ℤ → ℝ} (hρ : ρ 0 = 1) {k : ℕ} {y w x b : Fin k → ℝ} (b' : ℝ)
    (hy : (toeplitz ρ)ᵀ *ᵥ y = fun i : Fin k => -ρ ((i : ℤ) + 1))
    (hw : toeplitz ρ *ᵥ w = fun i : Fin k => -ρ (-((i : ℤ) + 1))) (hx : toeplitz ρ *ᵥ x = b)
    (α ν μ : ℝ)
    (hα : α * (1 + ∑ i : Fin k, ρ ((i : ℤ) + 1) * w i) =
      -(ρ ((k : ℤ) + 1) + ∑ i : Fin k, ρ (k - (i : ℤ)) * y i))
    (hν : ν * (1 + ∑ i : Fin k, ρ (-((i : ℤ) + 1)) * y i) =
      -(ρ (-((k : ℤ) + 1)) + ∑ i : Fin k, ρ ((i : ℤ) - k) * w i))
    (hμ : μ * (1 + ∑ i : Fin k, ρ (-((i : ℤ) + 1)) * y i) =
      b' - ∑ i : Fin k, ρ ((i : ℤ) - k) * x i) :
    ((toeplitz ρ)ᵀ *ᵥ Fin.snoc (y + α • (exchange k *ᵥ w)) α =
        fun i : Fin (k + 1) => -ρ ((i : ℤ) + 1)) ∧
      (toeplitz ρ *ᵥ Fin.snoc (w + ν • (exchange k *ᵥ y)) ν =
        fun i : Fin (k + 1) => -ρ (-((i : ℤ) + 1))) ∧
      toeplitz ρ *ᵥ Fin.snoc (x + μ • (exchange k *ᵥ y)) μ = Fin.snoc b b' :=
  Levinson.bordered_solve_toeplitz hρ b' hy hw hx α ν μ hα hν hμ

end GolubVanLoan.Chapter04
