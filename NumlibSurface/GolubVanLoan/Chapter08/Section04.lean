/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.DivideConquer
import Numlib.Eigen.InverseEigenvalue
import Numlib.Eigen.Sturm
import Numlib.Nonlinear.Bisection
import NumlibSurface.GolubVanLoan.Chapter08.Section01

/-!
# Golub and Van Loan, Section 8.4: More methods for tridiagonal problems

This module formalizes §8.4 of [golub2013matrix]. Let $T = T_n$ be the symmetric tridiagonal matrix
(8.4.1) with diagonal entries $\alpha_1, \dots, \alpha_n$ and off-diagonal entries
$\beta_1, \dots, \beta_{n-1}$, let $T_r$ be its leading $r \times r$ principal submatrix, let
$p_r(x) = \det(T_r - xI)$, and let $\lambda_1(T) \ge \dots \ge \lambda_n(T)$ be the eigenvalues of
$T$. For bisection (§8.4.1–8.4.2) the module states the three-term recurrence (8.4.2) for $p_r$, one
step of bisection on $p_n$, the Sturm sequence property (Theorem 8.4.1), the bisection (8.4.3) for
$\lambda_k(T)$, and the count of the eigenvalues below $\mu$ from an $LDL^T$ factorization of
$A - \mu I$. For a diagonal-plus-rank-one matrix $D + \rho zz^T$ (§8.4.3) it states the eigenvalue
equation (8.4.4), Lemma 8.4.2, the secular equation and the interlacing of Theorem 8.4.3, and the
deflation of Theorem 8.4.4.

For divide and conquer (§8.4.4) the module states the tearing (8.4.5)–(8.4.6) of $T$ into two
tridiagonal halves and a rank-one term, and the merge of the Schur decompositions of the halves. For
the inverse eigenvalue problem of §8.4.6 it states the formulas (8.4.10)–(8.4.12) and the existence
of a symmetric tridiagonal $T$ with prescribed eigenvalues of $T$ and of $T(2{:}n, 2{:}n)$. The
proofs use the backbone modules `Numlib.Eigen.Sturm`, `Numlib.Eigen.DivideConquer`,
`Numlib.Eigen.InverseEigenvalue` and `Numlib.Nonlinear.Bisection`.

## Main definitions

* §8.4.3, `GolubVanLoan.Chapter08.secularFunction`: the secular function $f(\lambda) = 1 + \rho
  \sum_i z_i^2 / (d_i - \lambda)$ of $D + \rho zz^T$.

## Main results

* (8.4.2), `GolubVanLoan.Chapter08.equation_8_4_2`: the leading principal submatrices of $T$ are
  $T_r$, $p_1(x) = \alpha_1 - x$, and $p_r(x) = (\alpha_r - x) p_{r-1}(x) - \beta_{r-1}^2
  p_{r-2}(x)$.
* §8.4.1, `GolubVanLoan.Chapter08.bisection_bracket`: one bisection step on a sign change of $p_n$
  halves the bracket and keeps an eigenvalue of $T$ in it.
* Theorem 8.4.1, `GolubVanLoan.Chapter08.theorem_8_4_1`: if $T$ is unreduced, the eigenvalues of
  $T_{r-1}$ strictly separate those of $T_r$.
* Theorem 8.4.1, `GolubVanLoan.Chapter08.theorem_8_4_1_b`: if $T$ is unreduced, the number
  $a(\lambda)$ of sign changes in $p_0(\lambda), \dots, p_n(\lambda)$ is the number of eigenvalues
  of $T$ that are $\le \lambda$.
* §8.4.2, `GolubVanLoan.Chapter08.gershgorin_bracket`: the eigenvalues of $T$ lie in the Gershgorin
  interval of $T$.
* (8.4.3), `GolubVanLoan.Chapter08.equation_8_4_3`: the bisection for $\lambda_k(T)$ halves its
  bracket at each step and keeps $\lambda_k(T)$ in it.
* §8.4.2, `GolubVanLoan.Chapter08.ldlt_inertia_count`: if $A - \mu I = LDL^T$, the number of
  negative diagonal entries of $D$ is the number of eigenvalues of $A$ less than $\mu$.
* (8.4.4), `GolubVanLoan.Chapter08.equation_8_4_4`: $(D + \rho zz^T) v = \lambda v$ if and only if
  $(D - \lambda I) v + \rho (z^T v) z = 0$.
* Lemma 8.4.2, `GolubVanLoan.Chapter08.lemma_8_4_2`: for distinct $d_i$, $\rho \ne 0$ and $z$
  without zero components, an eigenvector $v$ of $D + \rho zz^T$ has $z^T v \ne 0$, and
  $D - \lambda I$ is nonsingular.
* Theorem 8.4.3(a), (c), `GolubVanLoan.Chapter08.theorem_8_4_3`: the eigenvalues of $D + \rho zz^T$
  are the zeros of the secular function, and the eigenvectors are multiples of
  $(D - \lambda_i I)^{-1} z$.
* Theorem 8.4.3(b), `GolubVanLoan.Chapter08.theorem_8_4_3_b`: the eigenvalues of $D + \rho zz^T$
  strictly interlace the $d_i$.
* Theorem 8.4.4, `GolubVanLoan.Chapter08.theorem_8_4_4`: an orthogonal $V_1$ diagonalizes $D$ and
  makes exactly the first $r$ components of $V_1^T z$ nonzero, with distinct diagonal entries in the
  first $r$ positions.
* (8.4.5)–(8.4.6), `GolubVanLoan.Chapter08.equation_8_4_6`:
  $T = \operatorname{diag}(T_1, T_2) + \rho vv^T$ for the tearing of $T$ at its middle.
* §8.4.4, `GolubVanLoan.Chapter08.divideConquer_merge`: Schur decompositions of $T_1$, $T_2$ and of
  the diagonal-plus-rank-one matrix combine to a Schur decomposition of
  $\operatorname{diag}(T_1, T_2) + \rho vv^T$.
* (8.4.10)–(8.4.11), `GolubVanLoan.Chapter08.equation_8_4_10`: $e_1^T (T - \lambda I)^{-1} e_1 =
  \sum_i d_i^2 / (\lambda_i - \lambda) = \det(T(2{:}n, 2{:}n) - \lambda I) / \det(T - \lambda I)$.
* (8.4.12), `GolubVanLoan.Chapter08.equation_8_4_12`: under strict interlacing, $d_k^2$ is a
  quotient of products of eigenvalue differences, and these quotients are positive with sum $1$.
* §8.4.6, `GolubVanLoan.Chapter08.inverseTridiagonal_exists`: for strictly interlacing $\lambda$ and
  $\tilde\lambda$ there is a symmetric tridiagonal $T$ with $\lambda(T) = \lambda$ and
  $\lambda(T(2{:}n, 2{:}n)) = \tilde\lambda$.

## Conventions

* The tridiagonal matrix (8.4.1) is `Matrix.symmTridiagonalOf α β n`, with data `α β : ℕ → ℝ`
  indexed from $0$: the book's $\alpha_r$ and $\beta_r$ are `α (r - 1)` and `β (r - 1)`. Its
  leading principal submatrix $T_r$ is `Matrix.symmTridiagonalOf α β r`.
* "$T$ is unreduced", that is, $\beta_1, \dots, \beta_{n-1}$ are nonzero, is the hypothesis
  `∀ j, j + 1 < n → β j ≠ 0`.
* The Sturm sequence $p_0, \dots, p_n$ is `Sturm.seq`. The sign convention at a zero (a vanishing
  $p_r(\lambda)$ takes the sign opposite to that of $p_{r-1}(\lambda)$) is `Sturm.sign`, the count
  $a(\lambda)$ of sign changes is `Sturm.signChanges`, and Givens' bisection is
  `Sturm.bisectionIterate`.
* The book's $\lambda_k(A)$ is `GolubVanLoan.Chapter08.symmEigenvalue hA ⟨k - 1, _⟩` of §8.1.

## Deviations from the source

* **§8.4.1, bisection loop** (reading). In exact arithmetic the first bisection loop need not
  terminate when the bracketed zero is $0$. The declaration states one step of the loop. See
  `GolubVanLoan.Chapter08.bisection_bracket`.
* **Theorem 8.4.1** (correction). The source says that $a(\lambda)$ is the number of eigenvalues
  less than $\lambda$. With the sign convention of the source, $a(\lambda)$ is the number of
  eigenvalues $\le \lambda$; the two numbers differ exactly when $\lambda$ is an eigenvalue. See
  `GolubVanLoan.Chapter08.theorem_8_4_1_b`.
* **(8.4.3)** (correction). The source tests $a(x) \ge n - k$. The correct test is
  $a(x) \ge n - k + 1$. See `GolubVanLoan.Chapter08.equation_8_4_3`.
* **Theorem 8.4.4** (correction). The source claims $\mu_r \ge \mu_{r+1}$ across the deflation
  boundary. This is false for $d = (2, 1)$ and $z = (0, 1)$. The declaration orders the two parts
  separately. See `GolubVanLoan.Chapter08.theorem_8_4_4`.
* **(8.4.6)** (generalization). The source takes $\theta \in \{-1, 1\}$. The identity holds for
  every real $\theta$. See `GolubVanLoan.Chapter08.equation_8_4_6`.
* **(8.4.6)–(8.4.7)** (typo). The source prints $a_m$ for $\alpha_m$ and a stray $\lambda'_{n-1}$.
  See `GolubVanLoan.Chapter08.equation_8_4_6` and `GolubVanLoan.Chapter08.equation_8_4_12`.
* **(8.4.12)** (typo). The product in the denominator runs over $j \ne k$, $j = 1, \dots, n$. See
  `GolubVanLoan.Chapter08.equation_8_4_12`.

## Not formalized

* **§8.4.5**, the parallel divide-and-conquer tree and Figure 8.4.1.
* **§8.4.6**, the Lagrange-multiplier motivation of the inverse eigenvalue problem.
* **Operation counts.**
-/

open Matrix Polynomial

namespace GolubVanLoan.Chapter08

/-! ### §8.4.1 Eigenvalues by bisection -/

/-- The Sturm polynomial `Sturm.seq α β r` takes the value $p_r(x) = \det(T_r - xI)$ at every $x$.
-/
private theorem eval_seq_eq_det (α β : ℕ → ℝ) (r : ℕ) (x : ℝ) :
    (Sturm.seq α β r).eval x = (symmTridiagonalOf α β r - x • 1).det := by
  rw [Sturm.seq_eq_det, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [RingHom.mapMatrix_apply, h]

/-- **Equation (8.4.2)** of [golub2013matrix]. Let $\alpha_1, \alpha_2, \dots$ and
$\beta_1, \beta_2, \dots$ be real numbers, let $T_r$ be the symmetric tridiagonal matrix of
order $r$ with diagonal $\alpha_1, \dots, \alpha_r$ and off-diagonal
$\beta_1, \dots, \beta_{r-1}$, and let $p_r(x) = \det(T_r - xI)$. Then the leading $r \times r$
principal submatrix of $T_n$ is $T_r$ for every $r \le n$, $p_1(x) = \alpha_1 - x$ for every
real $x$, and for $r \ge 2$ and every real $x$
$$p_r(x) = (\alpha_r - x) p_{r-1}(x) - \beta_{r-1}^2 p_{r-2}(x).$$

The data are `α β : ℕ → ℝ`, indexed from $0$, and the recurrence is stated for the index $r + 2$
with $r \ge 0$. Its first instance uses $p_0(x) = 1$, the determinant of the $0 \times 0$
matrix. -/
theorem equation_8_4_2 (α β : ℕ → ℝ) :
    (∀ r n (h : r ≤ n), (symmTridiagonalOf α β n).submatrix (Fin.castLE h) (Fin.castLE h) =
      symmTridiagonalOf α β r) ∧
    (∀ x : ℝ, (symmTridiagonalOf α β 1 - x • 1).det = α 0 - x) ∧
    ∀ (r : ℕ) (x : ℝ), (symmTridiagonalOf α β (r + 2) - x • 1).det =
      (α (r + 1) - x) * (symmTridiagonalOf α β (r + 1) - x • 1).det -
        β r ^ 2 * (symmTridiagonalOf α β r - x • 1).det := by
  refine ⟨fun r n h => ?_, fun x => ?_, fun r x => ?_⟩
  · ext i j
    simp [symmTridiagonalOf_apply]
  · rw [← eval_seq_eq_det, Sturm.seq_one]
    simp
  · rw [← eval_seq_eq_det, ← eval_seq_eq_det, ← eval_seq_eq_det, Sturm.seq_add_two]
    simp

/-- **Section 8.4.1** of [golub2013matrix], one step of the bisection loop on $p_n$. Let $T_n$ and
$p_n(x) = \det(T_n - xI)$ be as in (8.4.2), and let $y < z$ with $p_n(y) p_n(z) < 0$. Let
$x = (y + z)/2$, and let $(y', z') = (y, x)$ if $p_n(x) p_n(y) < 0$ and $(y', z') = (x, z)$
otherwise. Then $y' < z'$, $z' - y' = (z - y)/2$, the interval $[y', z']$ contains an eigenvalue
of $T_n$, and $p_n(y') p_n(z') < 0$ unless $p_n(x) = 0$.

**Reading.** The source repeats this step in a `while` loop. In exact arithmetic that loop need
not terminate when the bracketed zero is $0$, so the declaration states one step. -/
theorem bisection_bracket (α β : ℕ → ℝ) (n : ℕ) {y z : ℝ} (hyz : y < z)
    (h : (symmTridiagonalOf α β n - y • 1).det * (symmTridiagonalOf α β n - z • 1).det < 0) :
    let p := fun t : ℝ => (symmTridiagonalOf α β n - t • 1).det
    let x := (y + z) / 2
    let yz' := if p x * p y < 0 then (y, x) else (x, z)
    yz'.1 < yz'.2 ∧ yz'.2 - yz'.1 = (z - y) / 2 ∧
      (∃ μ ∈ Set.Icc yz'.1 yz'.2, μ ∈ spectrum ℝ (symmTridiagonalOf α β n)) ∧
      (p x ≠ 0 → p yz'.1 * p yz'.2 < 0) := by
  intro p x yz'
  have h' : p y * p z < 0 := h
  have hp : Continuous p := by
    have : p = fun t => (Sturm.seq α β n).eval t :=
      funext fun t => (eval_seq_eq_det α β n t).symm
    rw [this]
    exact Polynomial.continuous _
  have hmem : ∀ μ, p μ = 0 → μ ∈ spectrum ℝ (symmTridiagonalOf α β n) := fun μ hμ => by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot.def, Matrix.eval_charpoly]
    have : (scalar (Fin n) μ - symmTridiagonalOf α β n) =
        -(symmTridiagonalOf α β n - μ • 1) := by
      rw [neg_sub, smul_one_eq_diagonal]; rfl
    have hμ' : (symmTridiagonalOf α β n - μ • 1).det = 0 := hμ
    rw [this, det_neg, hμ', mul_zero]
  have hyx : y < x := by simp only [x]; linarith
  have hxz : x < z := by simp only [x]; linarith
  have hroot : ∀ a b, a ≤ b → p a * p b ≤ 0 → ∃ μ ∈ Set.Icc a b, μ ∈ spectrum ℝ _ :=
    fun a b hab hab' => by
      obtain ⟨μ, hμ, h0⟩ := exists_eq_zero_Icc_of_mul_nonpos hab hp.continuousOn hab'
      exact ⟨μ, hμ, hmem μ h0⟩
  by_cases hc : p x * p y < 0
  · simp only [yz', hc, ite_true]
    refine ⟨hyx, by simp only [x]; ring, hroot y x hyx.le (by linarith [mul_comm (p x) (p y)]),
      fun _ => by linarith [mul_comm (p x) (p y)]⟩
  · simp only [yz', hc, ite_false]
    have hy : p y ≠ 0 := fun h0 => by rw [h0, zero_mul] at h'; exact lt_irrefl _ h'
    have key : p x * p z * p y ^ 2 = (p x * p y) * (p y * p z) := by ring
    have hxz' : p x * p z ≤ 0 := by
      have h1 : 0 ≤ p x * p y := le_of_not_gt hc
      have h2 : (p x * p y) * (p y * p z) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 h'.le
      have hy2 : 0 < p y ^ 2 := by positivity
      nlinarith
    refine ⟨hxz, by simp only [x]; ring, hroot x z hxz.le hxz', fun hx0 => ?_⟩
    rcases hxz'.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rcases mul_eq_zero.1 heq with h0 | h0
      · exact hx0 h0
      · rw [h0, mul_zero] at h'; exact lt_irrefl _ h'

/-! ### §8.4.2 Sturm sequence methods -/

/-- **Theorem 8.4.1** of [golub2013matrix] (Sturm sequence property), interlacing part. Let
$T_{r+1}$ be the symmetric tridiagonal matrix of (8.4.2), and assume that
$\beta_1, \dots, \beta_r$ are nonzero. Then the eigenvalues of $T_r$ strictly separate those of
$T_{r+1}$: for $k = 1, \dots, r$,
$$\lambda_{k+1}(T_{r+1}) < \lambda_k(T_r) < \lambda_k(T_{r+1}).$$

The source states this for $T_{r-1}$ and $T_r$. In Lean, $T_r$ is
`Matrix.symmTridiagonalOf α β r`, and the index `k : Fin r` is the book's $k - 1$. -/
theorem theorem_8_4_1 (α β : ℕ → ℝ) (r : ℕ) (hβ : ∀ j, j + 1 < r + 1 → β j ≠ 0) (k : Fin r) :
    symmEigenvalue (isSymm_symmTridiagonalOf α β (r + 1)) k.succ <
        symmEigenvalue (isSymm_symmTridiagonalOf α β r) k ∧
      symmEigenvalue (isSymm_symmTridiagonalOf α β r) k <
        symmEigenvalue (isSymm_symmTridiagonalOf α β (r + 1)) k.castSucc :=
  ⟨Sturm.eigenvalues_succ_lt α β r hβ k, Sturm.eigenvalues_lt_castSucc α β r hβ k⟩

/-- **Theorem 8.4.1** of [golub2013matrix] (Sturm sequence property), counting part. Let $T = T_n$
be the symmetric tridiagonal matrix of (8.4.2) with $\beta_1, \dots, \beta_{n-1}$ nonzero, and
let $\mu \in \mathbb{R}$. Let $a(\mu)$ be the number of sign changes in the sequence
$p_0(\mu), p_1(\mu), \dots, p_n(\mu)$, where a vanishing $p_r(\mu)$ takes the sign opposite to
that of $p_{r-1}(\mu)$. Then $a(\mu)$ is the number of eigenvalues of $T$ that are $\le \mu$. If
$\mu$ is not an eigenvalue of $T$, then $a(\mu)$ is also the number of eigenvalues of $T$ that
are $< \mu$.

**Correction.** The source states that $a(\mu)$ is the number of eigenvalues less than $\mu$.
With the sign convention of the source this is false exactly when $\mu$ is an eigenvalue of $T$.
Off the spectrum the printed statement holds, and it is the second part.

The count $a(\mu)$ is `Sturm.signChanges α β n μ`, and the sign convention is `Sturm.sign`.
Eigenvalues are counted with multiplicity, as the number of indices $k$ with
$\lambda_k(T) \le \mu$ (or $< \mu$). -/
theorem theorem_8_4_1_b (α β : ℕ → ℝ) (n : ℕ) (hβ : ∀ j, j + 1 < n → β j ≠ 0) (μ : ℝ) :
    Sturm.signChanges α β n μ = (Finset.univ.filter fun k =>
        symmEigenvalue (isSymm_symmTridiagonalOf α β n) k ≤ μ).card ∧
      (μ ∉ spectrum ℝ (symmTridiagonalOf α β n) → Sturm.signChanges α β n μ =
        (Finset.univ.filter fun k =>
          symmEigenvalue (isSymm_symmTridiagonalOf α β n) k < μ).card) := by
  have h := Sturm.signChanges_eq_count α β n hβ μ
  refine ⟨h, fun hμ => ?_⟩
  rw [h, Sturm.count]
  congr 1
  refine Finset.filter_congr fun k _ => ⟨fun hk => lt_of_le_of_ne hk fun he => hμ ?_, le_of_lt⟩
  rw [← he]
  exact symmEigenvalue_mem_spectrum _ k

/-- **Section 8.4.2** of [golub2013matrix], the Gershgorin bracket. Let $T = T_n$ be the symmetric
tridiagonal matrix of (8.4.2), and put $\beta_0 = \beta_n = 0$. Then every eigenvalue of $T$
lies in $[y, z]$, where
$$y = \min_i (\alpha_i - |\beta_i| - |\beta_{i-1}|), \qquad z = \max_i (\alpha_i + |\beta_i| +
  |\beta_{i-1}|).$$

The radius $|\beta_{i-1}| + |\beta_i|$ is `Sturm.gershgorinRadius β n i`. -/
theorem gershgorin_bracket (α β : ℕ → ℝ) (n : ℕ) :
    spectrum ℝ (symmTridiagonalOf α β n) ⊆
      Set.Icc (⨅ i : Fin n, (α i - Sturm.gershgorinRadius β n i))
        (⨆ i : Fin n, (α i + Sturm.gershgorinRadius β n i)) :=
  Sturm.spectrum_subset_Icc α β n

/-- **Equation (8.4.3)** of [golub2013matrix], bisection for $\lambda_k(T)$. Let $T = T_n$ be the
symmetric tridiagonal matrix of (8.4.2) with $\beta_1, \dots, \beta_{n-1}$ nonzero, let
$1 \le k \le n$, let $a(x)$ be the sign-change count of Theorem 8.4.1, and let
$r_i = |\beta_{i-1}| + |\beta_i|$ be the Gershgorin radius of row $i$. Then:

* if $y < \min_i (\alpha_i - r_i)$ and $z \ge \max_i (\alpha_i + r_i)$, then
  $a(y) \le n - k < a(z)$;
* if $a(y_0) \le n - k < a(z_0)$ and the intervals $(y_j, z_j)$ come from $(y_0, z_0)$ by the
  loop below, then $z_j - y_j = (z_0 - y_0)/2^j$ and $y_j < \lambda_k(T) \le z_j$ for every
  $j \ge 0$.

```
x = (y + z)/2
if a(x) ≥ n - k + 1 then z = x else y = x
```

**Correction.** The source prints the test $a(x) \ge n - k$. The correct test is
$a(x) \ge n - k + 1$, and the declaration uses it.

The intervals $(y_j, z_j)$ are `Sturm.bisectionIterate α β n k (y₀, z₀) j`. -/
theorem equation_8_4_3 (α β : ℕ → ℝ) {n k : ℕ} (hβ : ∀ j, j + 1 < n → β j ≠ 0) (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    (∀ {y z : ℝ}, y < ⨅ i : Fin n, (α i - Sturm.gershgorinRadius β n i) →
      (⨆ i : Fin n, (α i + Sturm.gershgorinRadius β n i)) ≤ z →
      Sturm.signChanges α β n y ≤ n - k ∧ n - k < Sturm.signChanges α β n z) ∧
    ∀ {yz : ℝ × ℝ}, Sturm.signChanges α β n yz.1 ≤ n - k ∧
        n - k < Sturm.signChanges α β n yz.2 → ∀ r : ℕ,
      (Sturm.bisectionIterate α β n k yz r).2 - (Sturm.bisectionIterate α β n k yz r).1 =
          (yz.2 - yz.1) / 2 ^ r ∧
        symmEigenvalue (isSymm_symmTridiagonalOf α β n) ⟨k - 1, by omega⟩ ∈
          Set.Ioc (Sturm.bisectionIterate α β n k yz r).1 (Sturm.bisectionIterate α β n k yz r).2 :=
  ⟨fun hy hz => by
    rw [Sturm.signChanges_eq_count α β n hβ, Sturm.signChanges_eq_count α β n hβ,
      Sturm.count_eq_zero_of_lt α β hy, Sturm.count_eq_of_le α β hz]
    omega,
  fun h r => ⟨Sturm.bisectionIterate_length α β n k _ r,
    Sturm.eigenvalues_mem_bisectionIterate α β hβ hk hkn h r⟩⟩

/-- **Section 8.4.2** of [golub2013matrix], the eigenvalue count from an $LDL^T$ factorization. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric and $\mu \in \mathbb{R}$, and let
$A - \mu I = LDL^T$ with $L$ unit lower triangular and
$D = \operatorname{diag}(d_1, \dots, d_n)$. Then the number of indices $i$ with $d_i < 0$ is the
number of eigenvalues $\lambda_k(A) < \mu$, counted with multiplicity.

The factorization is `Matrix.IsLDM (A - μ • 1) L (diagonal d) L`. -/
theorem ldlt_inertia_count {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) {μ : ℝ}
    {L : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ} (h : IsLDM (A - μ • 1) L (diagonal d) L) :
    (Finset.univ.filter fun k => symmEigenvalue hA k < μ).card =
      (Finset.univ.filter fun i => d i < 0).card := by
  rw [card_filter_symmEigenvalue hA (· < μ)]
  exact (isHermitian_iff_isSymm.2 hA).card_eigenvalues_lt_eq_card_neg_of_isLDM h

/-! ### §8.4.3 Eigensystems of diagonal plus rank-1 matrices -/

section RankOne

variable {n : ℕ}

/-- **Equation (8.4.4)** of [golub2013matrix]. Let $D = \operatorname{diag}(d_1, \dots, d_n)$,
$\rho \in \mathbb{R}$, $z, v \in \mathbb{R}^n$ and $\lambda \in \mathbb{R}$. Then
$(D + \rho zz^T) v = \lambda v$ if and only if
$$(D - \lambda I) v + \rho (z^T v) z = 0.$$
-/
theorem equation_8_4_4 (d : Fin n → ℝ) (ρ : ℝ) (z v : Fin n → ℝ) (t : ℝ) :
    (diagonal d + ρ • vecMulVec z z) *ᵥ v = t • v ↔
      (diagonal d - t • 1) *ᵥ v + (ρ * (z ⬝ᵥ v)) • z = 0 := by
  have h := Matrix.diagonal_add_rankOne_mulVec_eq_iff (𝕜 := ℝ) (d := d) (ρ := ρ) (z := z)
    (v := v) (t := t)
  simp only [RCLike.ofReal_real_eq_id, id_eq, star_trivial] at h
  rw [h, funext_iff]
  refine forall_congr' fun i => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_mulVec, smul_mulVec,
    one_mulVec, Pi.sub_apply, mulVec_diagonal, Pi.zero_apply]
  constructor <;> intro h' <;> linarith

/-- **Lemma 8.4.2** of [golub2013matrix]. Let $D = \operatorname{diag}(d_1, \dots, d_n)$ with
distinct $d_i$, let $\rho \ne 0$, and let $z \in \mathbb{R}^n$ have no zero component. If
$v \in \mathbb{R}^n$ is nonzero and $(D + \rho zz^T) v = \lambda v$, then $z^T v \ne 0$ and
$D - \lambda I$ is nonsingular. -/
theorem lemma_8_4_2 {d : Fin n → ℝ} (hd : Function.Injective d) {ρ : ℝ} (hρ : ρ ≠ 0)
    {z : Fin n → ℝ} (hz : ∀ i, z i ≠ 0) {v : Fin n → ℝ} (hv : v ≠ 0) {t : ℝ}
    (h : (diagonal d + ρ • vecMulVec z z) *ᵥ v = t • v) :
    z ⬝ᵥ v ≠ 0 ∧ IsUnit (diagonal d - t • 1) := by
  have h' := isUnit_diagonal_sub_of_hasEigenvector_add_rankOne (𝕜 := ℝ) hd hρ hz hv
    (by simpa using h)
  refine ⟨by simpa using h'.1, ?_⟩
  rw [smul_one_eq_diagonal, diagonal_sub, isUnit_iff_isUnit_det, det_diagonal,
    isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun i _ => sub_ne_zero.2 (by simpa using h'.2 i)

/-- **Section 8.4.3** of [golub2013matrix], the secular function. For $d, z \in \mathbb{R}^n$,
$D = \operatorname{diag}(d)$ and $\rho \in \mathbb{R}$, the **secular function** of
$D + \rho zz^T$ is
$$f(\lambda) = 1 + \rho z^T (D - \lambda I)^{-1} z = 1 + \rho \sum_{i=1}^n \frac{z_i^2}{d_i -
  \lambda}.$$

The definition is the sum, `Matrix.secularFunction`. At a pole $\lambda = d_i$ the Lean value
uses $z_i^2 / 0 = 0$ and has no meaning; the statements about $f$ assume
$\lambda \notin \{d_1, \dots, d_n\}$. -/
noncomputable def secularFunction (d : Fin n → ℝ) (ρ : ℝ) (z : Fin n → ℝ) (t : ℝ) : ℝ :=
  Matrix.secularFunction d ρ z t

/-- For every $\lambda$, the secular function is $f(\lambda) = 1 + \rho \sum_i z_i^2 / (d_i -
\lambda)$. If $\lambda \notin \{d_1, \dots, d_n\}$, then also $f(\lambda) = 1 + \rho z^T (D -
\lambda I)^{-1} z$, and $f$ has the derivative $f'(\lambda) = \rho \sum_i z_i^2 / (d_i -
\lambda)^2$ at $\lambda$. -/
theorem secularFunction_eq (d : Fin n → ℝ) (ρ : ℝ) (z : Fin n → ℝ) (t : ℝ) :
    secularFunction d ρ z t = 1 + ρ * ∑ i, z i ^ 2 / (d i - t) ∧
      (t ∉ Set.range d → secularFunction d ρ z t = 1 + ρ * (z ⬝ᵥ (diagonal d - t • 1)⁻¹ *ᵥ z) ∧
        HasDerivAt (secularFunction d ρ z) (ρ * ∑ i, z i ^ 2 / (d i - t) ^ 2) t) := by
  refine ⟨by simp [secularFunction, Matrix.secularFunction, Real.norm_eq_abs, sq_abs],
    fun ht => ⟨?_, ?_⟩⟩
  · rw [secularFunction, Matrix.secularFunction_eq_inner_resolvent d ρ z ht]
    have : diagonal d - t • 1 = diagonal fun i => d i - t := by
      rw [smul_one_eq_diagonal, diagonal_sub]
    rw [this]
    simp
  · have := Matrix.hasDerivAt_secularFunction d ρ z ht
    change HasDerivAt (Matrix.secularFunction d ρ z) _ t
    simpa [Real.norm_eq_abs, sq_abs] using this

/-- **Theorem 8.4.3(a), (c)** of [golub2013matrix]. Let $D = \operatorname{diag}(d_1, \dots, d_n)$
with distinct $d_i$, let $\rho \ne 0$, and let $z \in \mathbb{R}^n$ have no zero component. Let
$V \in \mathbb{R}^{n \times n}$ be orthogonal with $V^T (D + \rho zz^T) V =
\operatorname{diag}(\lambda_1, \dots, \lambda_n)$, and let $f$ be the secular function. Then:

* (a) each $\lambda_i$ differs from every $d_j$ and satisfies $f(\lambda_i) = 0$, and every zero
  of $f$ outside $\{d_1, \dots, d_n\}$ is one of the $\lambda_i$;
* (c) each column $V(:, i)$ is a multiple of $(D - \lambda_i I)^{-1} z$.

The $\lambda_i$ need not be sorted. Part (b) is `GolubVanLoan.Chapter08.theorem_8_4_3_b`. -/
theorem theorem_8_4_3 {d : Fin n → ℝ} (hd : Function.Injective d) {ρ : ℝ} (hρ : ρ ≠ 0)
    {z : Fin n → ℝ} (hz : ∀ i, z i ≠ 0) {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) {l : Fin n → ℝ}
    (hVl : Vᵀ * (diagonal d + ρ • vecMulVec z z) * V = diagonal l) :
    (∀ i, l i ∉ Set.range d ∧ secularFunction d ρ z (l i) = 0) ∧
      (∀ t, t ∉ Set.range d → secularFunction d ρ z t = 0 → ∃ i, l i = t) ∧
      ∀ i, ∃ c : ℝ, V.col i = c • fun j => z j / (d j - l i) := by
  set M := diagonal d + ρ • vecMulVec z z
  have hVV : V * Vᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 hV
  have hVV' : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hV
  have hMV : M * V = V * diagonal l := by
    rw [← hVl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hVV, Matrix.one_mul]
  have hcol : ∀ i, M *ᵥ V.col i = l i • V.col i := fun i => by
    rw [← col_mul_eq_mulVec_col, hMV]
    ext j
    simp [col_apply, mul_diagonal, mul_comm]
  have hcol0 : ∀ i, V.col i ≠ 0 := fun i h0 => by
    have := congrFun (congrFun hVV' i) i
    simp only [Matrix.mul_apply, transpose_apply, one_apply_eq] at this
    have h' : ∀ j, V j i = 0 := fun j => congrFun h0 j
    simp [h'] at this
  have hiff := fun t => hasEigenvalue_iff_secularFunction_eq_zero (𝕜 := ℝ) hd hρ hz t
  simp only [RCLike.ofReal_real_eq_id, id_eq, star_trivial] at hiff
  refine ⟨fun i => ?_, fun t ht hf => ?_, fun i => ?_⟩
  · refine (hiff (l i)).1
      (Module.End.hasEigenvalue_of_hasEigenvector (x := V.col i) ⟨?_, hcol0 i⟩)
    rw [Module.End.mem_genEigenspace_one, toLin'_apply]
    exact hcol i
  · obtain ⟨v, hv⟩ := ((hiff t).2 ⟨ht, hf⟩).exists_hasEigenvector
    have hMv : M *ᵥ v = t • v := by
      have := hv.apply_eq_smul
      rwa [toLin'_apply] at this
    set w := Vᵀ *ᵥ v
    have hw : diagonal l *ᵥ w = t • w := by
      rw [← hVl]
      simp only [w, mulVec_mulVec, Matrix.mul_assoc, hVV, Matrix.mul_one]
      rw [← mulVec_mulVec, hMv, mulVec_smul]
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra! h0
      have : v = V *ᵥ w := by rw [mulVec_mulVec, hVV, one_mulVec]
      exact hv.2 (by rw [this, show w = 0 from funext h0, mulVec_zero])
    refine ⟨i, ?_⟩
    have := congrFun hw i
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hi this
  · obtain ⟨c, -, hc⟩ := hasEigenvector_diagonal_add_rankOne_resolvent (𝕜 := ℝ) hd hρ hz
      (hcol0 i) (by simpa using hcol i)
    exact ⟨c, by simpa using hc⟩

/-- **Theorem 8.4.3(b)** of [golub2013matrix], strict interlacing. Let $d_1 > d_2 > \dots > d_n$,
$D = \operatorname{diag}(d)$ and $\rho \ne 0$, and let $z \in \mathbb{R}^n$ have no zero
component. Let $\lambda_1 \ge \dots \ge \lambda_n$ be the eigenvalues of the symmetric matrix
$D + \rho zz^T$. If $\rho > 0$, then
$$\lambda_1 > d_1 > \lambda_2 > d_2 > \dots > \lambda_n > d_n.$$
If $\rho < 0$, then
$$d_1 > \lambda_1 > d_2 > \lambda_2 > \dots > d_n > \lambda_n.$$

The eigenvalues are `GolubVanLoan.Chapter08.symmEigenvalue hM`, where `hM` proves that
$D + \rho zz^T$ is symmetric. For $\rho > 0$ the chain is stated as $d_i < \lambda_i$ for all
$i$ and $\lambda_{i+1} < d_i$ for $i < n$; for $\rho < 0$ it is $\lambda_i < d_i$ and
$d_{i+1} < \lambda_i$. -/
theorem theorem_8_4_3_b {d : Fin n → ℝ} (hd : StrictAnti d) {ρ : ℝ} (hρ : ρ ≠ 0)
    {z : Fin n → ℝ} (hz : ∀ i, z i ≠ 0) (hM : (diagonal d + ρ • vecMulVec z z).IsSymm) :
    (0 < ρ → (∀ i, d i < symmEigenvalue hM i) ∧
        ∀ i j : Fin n, (j : ℕ) = i + 1 → symmEigenvalue hM j < d i) ∧
      (ρ < 0 → (∀ i, symmEigenvalue hM i < d i) ∧
        ∀ i j : Fin n, (j : ℕ) = i + 1 → d j < symmEigenvalue hM i) := by
  have heq : ((diagonal fun i => (RCLike.ofReal (d i) : ℝ)) + (RCLike.ofReal ρ : ℝ) •
      vecMulVec z (star z)) = diagonal d + ρ • vecMulVec z z := by simp
  have hM' : ((diagonal fun i => (RCLike.ofReal (d i) : ℝ)) + (RCLike.ofReal ρ : ℝ) •
      vecMulVec z (star z)).IsHermitian := by
    rw [heq]; exact isHermitian_iff_isSymm.2 hM
  have h := eigenvalues₀_diagonal_add_rankOne_strictInterlace (𝕜 := ℝ) hd hρ hz hM'
  rw [IsHermitian.sortedEigenvalues_congr heq hM' (isHermitian_iff_isSymm.2 hM)] at h
  exact h

/-- **Theorem 8.4.4** of [golub2013matrix] (deflation). Let
$D = \operatorname{diag}(d_1, \dots, d_n)$ and $z \in \mathbb{R}^n$. Then there are an
orthogonal $V_1 \in \mathbb{R}^{n \times n}$, real numbers $\mu_1, \dots, \mu_n$ and an integer
$r$ with $0 \le r \le n$ such that $V_1^T D V_1 = \operatorname{diag}(\mu_1, \dots, \mu_n)$, the
vector $w = V_1^T z$ has $w_i \ne 0$ exactly for $i \le r$, $\mu_1 > \dots > \mu_r$, and
$\mu_{r+1} \ge \dots \ge \mu_n$.

**Correction.** The source also claims $\mu_r \ge \mu_{r+1}$, so that all of
$\mu_1, \dots, \mu_n$ are in decreasing order. This is false in general. For $d = (2, 1)$ and
$z = (0, 1)$, the matrix $V_1$ must be a signed permutation, so $w$ has exactly one nonzero
component and $r = 1$; that component belongs to the eigenvalue $1$, so $\mu_1 = 1 < 2 = \mu_2$.
The declaration orders the two parts separately.

In Lean the indices are 0-based: $w_i \ne 0$ is `(i : ℕ) < r`. -/
theorem theorem_8_4_4 (d z : Fin n → ℝ) :
    ∃ V₁ ∈ orthogonalGroup (Fin n) ℝ, ∃ μ : Fin n → ℝ, ∃ r ≤ n,
      V₁ᵀ * diagonal d * V₁ = diagonal μ ∧
      (∀ i j : Fin n, i < j → (j : ℕ) < r → μ j < μ i) ∧
      (∀ i j : Fin n, r ≤ (i : ℕ) → i ≤ j → μ j ≤ μ i) ∧
      ∀ i, (V₁ᵀ *ᵥ z) i ≠ 0 ↔ (i : ℕ) < r :=
  exists_orthogonal_deflation d z

end RankOne

/-! ### §8.4.4 A divide-and-conquer framework -/

/-- **Equations (8.4.5)–(8.4.6)** of [golub2013matrix], tearing. Let $T$ be the symmetric
tridiagonal matrix of (8.4.2) of order $n = 2m$, with diagonal $\alpha_1, \dots, \alpha_n$ and
off-diagonal $\beta_1, \dots, \beta_{n-1}$. Let $\theta, \rho \in \mathbb{R}$ with
$\rho\theta = \beta_m$, and let $v = (e_m, \theta e_1) \in \mathbb{R}^{2m}$, where $e_m$ and
$e_1$ are unit vectors of $\mathbb{R}^m$. Then
$$T = \begin{bmatrix} T_1 & 0 \\ 0 & T_2 \end{bmatrix} + \rho vv^T,$$
where $T_1$ is the symmetric tridiagonal matrix with diagonal
$\alpha_1, \dots, \alpha_{m-1}, \alpha_m - \rho$ and off-diagonal $\beta_1, \dots, \beta_{m-1}$,
and $T_2$ is the symmetric tridiagonal matrix with diagonal $\alpha_{m+1} - \rho\theta^2,
\alpha_{m+2}, \dots, \alpha_n$ and off-diagonal $\beta_{m+1}, \dots, \beta_{n-1}$.

**Generalization.** The source takes $\theta \in \{-1, 1\}$. The identity holds for every real
$\theta$.

**Typo.** Displays (8.4.6)–(8.4.7) of the source print $a_m$ for $\alpha_m$ and a stray
$\lambda'_{n-1}$. The declaration uses $\alpha_m$.

The matrix $T$ is reindexed from `Fin (2m)` to `Fin m ⊕ Fin m` by `finSumFinEquiv`, and the block
matrix is `Matrix.fromBlocks`. The half order $m$ is `m + 1` in Lean; hence $m \ge 1$. -/
theorem equation_8_4_6 (α β : ℕ → ℝ) (m : ℕ) {θ ρ : ℝ} (hρ : ρ * θ = β m) :
    (symmTridiagonalOf α β (m + 1 + (m + 1))).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (symmTridiagonalOf (Function.update α m (α m - ρ)) β (m + 1)) 0 0
        (symmTridiagonalOf (Function.update (fun i => α (m + 1 + i)) 0 (α (m + 1) - ρ * θ ^ 2))
          (fun i => β (m + 1 + i)) (m + 1)) +
      ρ • vecMulVec (Sum.elim (Pi.single (Fin.last m) 1) (θ • Pi.single 0 1))
        (Sum.elim (Pi.single (Fin.last m) 1) (θ • Pi.single 0 1)) := by
  ext (i | i) (j | j) <;>
    simp only [submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Matrix.add_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.smul_apply, vecMulVec_apply,
      Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, symmTridiagonalOf_apply,
      Fin.val_castAdd, Fin.val_natAdd, Pi.single_apply, Fin.ext_iff, Fin.val_last, Fin.val_zero,
      Function.update_apply] <;>
    split_ifs <;> (try ring_nf) <;>
    first
    | omega
    | rfl
    | (congr 1 <;> omega)
    | (rw [hρ]; congr 1)

/-- **Section 8.4.4** of [golub2013matrix], the merge step of divide and conquer. Let
$T_1, T_2, Q_1, Q_2 \in \mathbb{R}^{m \times m}$ with $Q_1$ and $Q_2$ orthogonal,
$Q_1^T T_1 Q_1 = \operatorname{diag}(d_1)$ and $Q_2^T T_2 Q_2 = \operatorname{diag}(d_2)$, and
let $\rho, \theta \in \mathbb{R}$. Let $v = (e_m, \theta e_1)$ be the tearing vector of (8.4.6),
and let $U = \operatorname{diag}(Q_1, Q_2)$. Then:

* $U$ is orthogonal, and $U^T (\operatorname{diag}(T_1, T_2) + \rho vv^T) U = D + \rho zz^T$
  with $D = \operatorname{diag}(d_1, d_2)$ and $z = U^T v$;
* $z = (Q_1^T e_m, \theta Q_2^T e_1)$, that is, the last row of $Q_1$ followed by $\theta$ times
  the first row of $Q_2$;
* if $V$ is orthogonal and $V^T (D + \rho zz^T) V = \operatorname{diag}(\lambda)$, then $UV$ is
  orthogonal and $(UV)^T (\operatorname{diag}(T_1, T_2) + \rho vv^T) (UV) =
  \operatorname{diag}(\lambda)$.

The last part gives the Schur decomposition (8.4.5) with $Q = UV$. By
`GolubVanLoan.Chapter08.equation_8_4_6`, the matrix $\operatorname{diag}(T_1, T_2) + \rho vv^T$
is $T$ when $T_1$ and $T_2$ are the halves of the tearing. The order $m$ is `m + 1` in Lean. -/
theorem divideConquer_merge {m : ℕ} {T₁ Q₁ T₂ Q₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hQ₁ : Q₁ ∈ orthogonalGroup _ ℝ) (hQ₂ : Q₂ ∈ orthogonalGroup _ ℝ) {d₁ d₂ : Fin (m + 1) → ℝ}
    (h₁ : Q₁ᵀ * T₁ * Q₁ = diagonal d₁) (h₂ : Q₂ᵀ * T₂ * Q₂ = diagonal d₂) (ρ θ : ℝ) :
    let v := Sum.elim (Pi.single (Fin.last m) 1) (θ • Pi.single 0 1)
    let U := fromBlocks Q₁ 0 0 Q₂
    U ∈ orthogonalGroup _ ℝ ∧
      Uᵀ * (fromBlocks T₁ 0 0 T₂ + ρ • vecMulVec v v) * U =
        diagonal (Sum.elim d₁ d₂) + ρ • vecMulVec (Uᵀ *ᵥ v) (Uᵀ *ᵥ v) ∧
      Uᵀ *ᵥ v = Sum.elim (fun j => Q₁ (Fin.last m) j) (fun j => θ * Q₂ 0 j) ∧
      ∀ V ∈ orthogonalGroup _ ℝ, ∀ l : Fin (m + 1) ⊕ Fin (m + 1) → ℝ,
        Vᵀ * (diagonal (Sum.elim d₁ d₂) + ρ • vecMulVec (Uᵀ *ᵥ v) (Uᵀ *ᵥ v)) * V = diagonal l →
          U * V ∈ orthogonalGroup _ ℝ ∧
            (U * V)ᵀ * (fromBlocks T₁ 0 0 T₂ + ρ • vecMulVec v v) * (U * V) = diagonal l := by
  intro v U
  obtain ⟨hU, hconj⟩ := conj_fromBlocks_add_rankOne_eq hQ₁ hQ₂ h₁ h₂ ρ v
  refine ⟨hU, hconj, ?_, fun V hV l hVl => ⟨Submonoid.mul_mem _ hU hV, ?_⟩⟩
  · ext (j | j)
    · simp [U, v, mulVec, dotProduct, Pi.single_apply]
    · simp [U, v, mulVec, dotProduct, Pi.single_apply]
      ring
  · have e : (U * V)ᵀ * (fromBlocks T₁ 0 0 T₂ + ρ • vecMulVec v v) * (U * V) =
        Vᵀ * (Uᵀ * (fromBlocks T₁ 0 0 T₂ + ρ • vecMulVec v v) * U) * V := by
      simp only [transpose_mul, Matrix.mul_assoc]
    rw [e]
    exact (congrArg (fun X => Vᵀ * X * V) hconj).trans hVl

/-! ### §8.4.6 An inverse tridiagonal eigenvalue problem -/

/-- **Equations (8.4.10)–(8.4.11)** of [golub2013matrix]. Let $T, Q \in \mathbb{R}^{n \times n}$
with $n \ge 1$, $Q$ orthogonal and $T = Q^T \Lambda Q$, where $\Lambda =
\operatorname{diag}(\lambda_1, \dots, \lambda_n)$, and let $d = Q(:, 1)$. Let
$\lambda \in \mathbb{R}$ differ from every $\lambda_i$. Then
$$e_1^T (T - \lambda I)^{-1} e_1 = \sum_{i=1}^n \frac{d_i^2}{\lambda_i - \lambda} =
  \frac{\det(T(2{:}n, 2{:}n) - \lambda I)}{\det(T - \lambda I)}.$$

The second equality is Cramer's rule. The source reads off from it that the zeros of the sum are
the eigenvalues of $T(2{:}n, 2{:}n)$ that are not eigenvalues of $T$. The scalar $\lambda$ is `c`
in Lean, and the order $n$ is `N + 1`. -/
theorem equation_8_4_10 {N : ℕ} {T Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup _ ℝ) {l : Fin (N + 1) → ℝ} (hT : T = Qᵀ * diagonal l * Q) {c : ℝ}
    (hc : ∀ i, l i ≠ c) :
    (T - c • 1)⁻¹ 0 0 = ∑ i, Q i 0 ^ 2 / (l i - c) ∧
      (T - c • 1)⁻¹ 0 0 = (T.submatrix Fin.succ Fin.succ - c • 1).det / (T - c • 1).det := by
  refine ⟨?_, inv_sub_apply_zero_zero_eq_det_div T c⟩
  have hQt : Qᵀ ∈ unitaryGroup (Fin (N + 1)) ℝ := by
    have := Unitary.star_mem hQ
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hQ
  have hQA : star Qᵀ * T * Qᵀ = diagonal l := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, transpose_transpose, hT]
    simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  rw [inv_sub_smul_one_apply_eq_sum hQt hQA hc 0 0]
  simp [sq]

/-- If the characteristic polynomial of $M$ is $\prod_j (X - \mu_j)$, then
$\det(M - cI) = \prod_j (\mu_j - c)$ for every $c$. -/
private theorem det_sub_smul_one_of_charpoly {N : ℕ} {M : Matrix (Fin N) (Fin N) ℝ}
    {μ : Fin N → ℝ} (h : M.charpoly = ∏ j, (X - C (μ j))) (c : ℝ) :
    (M - c • 1).det = ∏ j, (μ j - c) := by
  have e := congrArg (Polynomial.eval c) h
  rw [eval_charpoly, eval_prod] at e
  simp only [eval_sub, eval_X, eval_C] at e
  have hneg : M - c • 1 = -(scalar (Fin N) c - M) := by
    rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
  rw [hneg, det_neg, e, Fintype.card_fin,
    show ∏ j, (μ j - c) = ∏ j, -(c - μ j) from by simp only [neg_sub], Finset.prod_neg,
    Finset.card_univ, Fintype.card_fin]

/-- **Equation (8.4.12)** of [golub2013matrix]. Let $\lambda_1, \dots, \lambda_n$ and
$\tilde\lambda_1, \dots, \tilde\lambda_{n-1}$ be real numbers with the strict interlacing
(8.4.7)
$$\lambda_1 > \tilde\lambda_1 > \lambda_2 > \tilde\lambda_2 > \dots > \tilde\lambda_{n-1} >
  \lambda_n.$$
Let $T, Q \in \mathbb{R}^{n \times n}$ with $Q$ orthogonal and $T = Q^T
\operatorname{diag}(\lambda_1, \dots, \lambda_n) Q$, and assume that the characteristic
polynomial of $T(2{:}n, 2{:}n)$ is $\prod_{j=1}^{n-1} (x - \tilde\lambda_j)$. Then $d = Q(:, 1)$
satisfies, for $k = 1, \dots, n$,
$$d_k^2 = \frac{\prod_{j=1}^{n-1} (\tilde\lambda_j - \lambda_k)}{\prod_{j = 1, j \ne k}^{n}
  (\lambda_j - \lambda_k)},$$
each of these $n$ quotients is positive, and their sum is $1$.

**Typo.** The source prints the product in the denominator over a wrong range of $j$; the range
is $j \ne k$, $j = 1, \dots, n$. Displays (8.4.6)–(8.4.7) also print a stray $\lambda'_{n-1}$;
the hypothesis here is the chain above.

In Lean the order $n$ is `N + 1`, and the vectors `l` and `μ` hold the numbers $\lambda_i$ and
$\tilde\lambda_j$. -/
theorem equation_8_4_12 {N : ℕ} {T Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hQ : Q ∈ orthogonalGroup _ ℝ) {l : Fin (N + 1) → ℝ} (hT : T = Qᵀ * diagonal l * Q)
    {μ : Fin N → ℝ} (h₁ : ∀ j, μ j < l j.castSucc) (h₂ : ∀ j, l j.succ < μ j)
    (hsub : (T.submatrix Fin.succ Fin.succ).charpoly = ∏ j, (X - C (μ j))) :
    (∀ k, Q k 0 ^ 2 = (∏ j, (μ j - l k)) / ∏ j ∈ Finset.univ.erase k, (l j - l k)) ∧
      (∀ k, 0 < (∏ j, (μ j - l k)) / ∏ j ∈ Finset.univ.erase k, (l j - l k)) ∧
      ∑ k, (∏ j, (μ j - l k)) / ∏ j ∈ Finset.univ.erase k, (l j - l k) = 1 := by
  obtain ⟨hpos, hsum⟩ := prod_sub_div_prod_sub_pos_of_strictInterlace h₁ h₂
  refine ⟨fun k => ?_, hpos, hsum⟩
  have hl : StrictAnti l := Fin.strictAnti_iff_succ_lt.mpr fun j => (h₂ j).trans (h₁ j)
  have hQt : Qᵀ ∈ unitaryGroup (Fin (N + 1)) ℝ := by
    have := Unitary.star_mem hQ
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hQQ : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff _ ℝ).1 hQ
  have hTs : T.IsHermitian := by
    rw [hT, IsHermitian, conjTranspose_eq_transpose_of_trivial]
    simp [transpose_mul, Matrix.mul_assoc]
  have hQA : star Qᵀ * T * Qᵀ = diagonal l := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, transpose_transpose, hT]
    simp only [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have h := hTs.norm_sq_eigenvector_mul_prod_eq hQt hQA k
  -- the eigenvalues of the trailing block are the `μ j`
  have hprod : ∏ j, ((hTs.submatrix Fin.succ).eigenvalues j - l k) = ∏ j, (μ j - l k) := by
    have e1 := (hTs.submatrix Fin.succ).det_sub_smul_one_eq_prod (l k)
    rw [det_sub_smul_one_of_charpoly hsub] at e1
    simpa using e1.symm
  have hne : ∏ j ∈ Finset.univ.erase k, (l j - l k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j hj =>
      sub_ne_zero.2 (hl.injective.ne (Finset.ne_of_mem_erase hj))
  rw [eq_div_iff hne, ← hprod, ← h]
  simp [Real.norm_eq_abs, sq_abs]

/-- **Section 8.4.6** of [golub2013matrix], the inverse eigenvalue problem. Let
$\lambda_1, \dots, \lambda_n$ and $\tilde\lambda_1, \dots, \tilde\lambda_{n-1}$ satisfy the
strict interlacing (8.4.7). Then there is a symmetric tridiagonal
$T \in \mathbb{R}^{n \times n}$ with $\lambda(T) = \{\lambda_1, \dots, \lambda_n\}$ (8.4.8) and
$\lambda(T(2{:}n, 2{:}n)) = \{\tilde\lambda_1, \dots, \tilde\lambda_{n-1}\}$ (8.4.9), with
multiplicity.

The source attributes the result to Golub (1973). The two spectra are stated as characteristic
polynomials, $\det(xI - T) = \prod_i (x - \lambda_i)$ and $\det(xI - T(2{:}n, 2{:}n)) = \prod_j
(x - \tilde\lambda_j)$. The order $n$ is `N + 1` in Lean. -/
theorem inverseTridiagonal_exists {N : ℕ} {l : Fin (N + 1) → ℝ} {μ : Fin N → ℝ}
    (h₁ : ∀ j, μ j < l j.castSucc) (h₂ : ∀ j, l j.succ < μ j) :
    ∃ T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ, T.IsSymm ∧ T.IsTridiagonal ∧
      T.charpoly = ∏ i, (X - C (l i)) ∧
        (T.submatrix Fin.succ Fin.succ).charpoly = ∏ j, (X - C (μ j)) :=
  exists_isTridiagonal_eigenvalues_eq_of_strictInterlace h₁ h₂

end GolubVanLoan.Chapter08
