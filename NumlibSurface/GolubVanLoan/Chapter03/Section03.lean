/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.GolubVanLoan.Chapter03.Section02

/-!
# Golub and Van Loan, Section 3.3: Roundoff error in Gaussian elimination

This module formalizes the two backward error theorems of §3.3 of [golub2013matrix]. Let $u$ be the
unit roundoff and $\gamma_k = ku/(1 - ku)$. Theorem 3.3.1 says that the factors $\hat L$ and
$\hat U$ that Gaussian elimination (Algorithm 3.2.1) computes for $A \in \mathbb{R}^{n \times n}$
satisfy $\hat L \hat U = A + H$ with $|H| \le \gamma_n |\hat L| |\hat U|$ entrywise. Theorem 3.3.2
says that if $\hat L$ and $\hat U$ are then used in the triangular solves of §3.1 for
$b \in \mathbb{R}^n$, the computed solution $\hat x$ satisfies $(A + E) \hat x = b$ with
$|E| \le \gamma_{3n} |\hat L| |\hat U|$ entrywise. Both theorems are statements about every output
of the programs of §3.1–3.2 in the relational rounding model `FloatingPoint.RoundingModel`.

Each proof applies a rounding bridge of §3.1–3.2, which says that every run satisfies a relation of
the backbone, and then a backbone theorem about that relation:
`FloatingPoint.exists_roundsLU_mul_eq_add`, `FloatingPoint.exists_roundsLU_solveDot_eq` and
`FloatingPoint.exists_roundsLU_solve_eq`. These are Theorems 9.3 and 9.4 of [higham2002accuracy].

## Main results

* Theorem 3.3.1, `GolubVanLoan.Chapter03.theorem_3_3_1`: the packed factors computed by Algorithm
  3.2.1 satisfy $\hat L \hat U = A + H$ with $|H| \le \gamma_n |\hat L| |\hat U|$.
* §3.3.1, `GolubVanLoan.Chapter03.theorem_3_3_1_gaxpy`: the same bound for the factors computed by
  Algorithm 3.2.2.
* Theorem 3.3.2, `GolubVanLoan.Chapter03.theorem_3_3_2`: factoring by Algorithm 3.2.1 and solving by
  Algorithms 3.1.1 and 3.1.2 gives $(A + E) \hat x = b$ with
  $|E| \le \gamma_{3n} |\hat L| |\hat U|$.
* Theorem 3.3.2 for the column-oriented solves, `GolubVanLoan.Chapter03.theorem_3_3_2_column`: the
  same bound when the solves are Algorithms 3.1.3 and 3.1.4.

## Conventions

* The source states first-order bounds, $|H| \le 2(n-1)u(|A| + |\hat L||\hat U|) + O(u^2)$ and
  $|E| \le nu(2|A| + 4|\hat L||\hat U|) + O(u^2)$. The theorems state the rigorous bounds
  $|H| \le \gamma_n |\hat L||\hat U|$ and $|E| \le \gamma_{3n} |\hat L||\hat U|$. Since
  $\gamma_k = ku + O(u^2)$, the Lean bounds use different first-order coefficients and omit the
  $|A|$ term.
* A computed quantity is any element of the run set of its program in the rounding model `fp`, with
  the hook `fp.round`. A composite of factoring and solving is stated with one universal quantifier
  per program. The hypotheses are about the returned packed factors only.

## Deviations from the source

* **Theorems 3.3.1 and 3.3.2** (generalization). The source assumes that the entries of $A$ are
  floating point numbers. The theorems hold for every real matrix $A$. See
  `GolubVanLoan.Chapter03.theorem_3_3_1` and `GolubVanLoan.Chapter03.theorem_3_3_2`.
* **Theorem 3.3.1** (generalization). The source assumes that no zero pivots occur. Only the pivots
  that are used as divisors, $\hat u_{jj}$ for $j < n$, must be nonzero. See
  `GolubVanLoan.Chapter03.theorem_3_3_1`.
* **Theorems 3.3.1 and 3.3.2** (reading). The error estimates use explicit $\gamma_n$ and
  $\gamma_{3n}$ bounds with smallness hypotheses. The solves require every diagonal pivot
  of $\hat U$ to be nonzero. See `GolubVanLoan.Chapter03.theorem_3_3_1`,
  `GolubVanLoan.Chapter03.theorem_3_3_1_gaxpy`, `GolubVanLoan.Chapter03.theorem_3_3_2` and
  `GolubVanLoan.Chapter03.theorem_3_3_2_column`.

## Not formalized

* **Displays (3.3.3)–(3.3.13).** They are steps of the proof in the source; the backbone proves the
  entrywise bound of [higham2002accuracy] Theorem 9.3 directly.
-/

open FloatingPoint Matrix

namespace GolubVanLoan.Chapter03

variable {fp : RoundingModel ℝ} {n : ℕ}

/-- **Theorem 3.3.1** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$, and let the unit
roundoff $u$ satisfy $u < 1$ and $nu < 1$. Let $F$ be a packed matrix computed by Algorithm
3.2.1 from $A$, and let $\hat L$ and $\hat U$ be the unit lower triangular and the upper
triangular factors stored in $F$. If the pivots $\hat u_{jj}$ are nonzero for
$j = 1, \dots, n-1$, then there is $H \in \mathbb{R}^{n \times n}$ with
$$\hat L \hat U = A + H, \qquad |H| \le \gamma_n |\hat L| |\hat U|$$
entrywise, where $\gamma_n = nu/(1 - nu)$.

**Generalization.** The source assumes that $A$ is a matrix of floating point numbers and that
no zero pivots are encountered. The theorem holds for every real $A$, and it needs only the
pivots that are divisors to be nonzero: the last pivot $\hat u_{nn}$ can vanish.

**Reading.** The source prints $2(n-1)u(|A|+|\hat L||\hat U|)+O(u^2)$. The theorem uses
the explicit $\gamma_n|\hat L||\hat U|$ under $u<1$ and $nu<1$. At $n=1$ the printed
leading coefficient is zero because the factorization makes no elimination updates. -/
theorem theorem_3_3_1 (hu : fp.u < 1) (hn : (n : ℝ) * fp.u < 1) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ F ∈ (algorithm_3_2_1 fp.round A).run, (∀ j : Fin n, (j : ℕ) + 1 < n → F j j ≠ 0) →
      ∃ H : Matrix (Fin n) (Fin n) ℝ, packedL F * packedU F = A + H ∧
        H.abs ≤ₑ gamma fp.u n • ((packedL F).abs * (packedU F).abs) := by
  intro F hF hpiv
  obtain ⟨H, hH, hLU⟩ := exists_roundsLU_mul_eq_add hu (by simpa using hn)
    (algorithm_3_2_1_rounds A F hF) fun j i hji => by
      rw [packedU_apply_of_le F le_rfl]
      exact hpiv j (by have := Fin.lt_def.1 hji; omega)
  exact ⟨H, hLU, by simpa using hH⟩

/-- **Section 3.3.1** of [golub2013matrix], the remark that the error bounds also apply to the gaxpy
formulation. Let $A \in \mathbb{R}^{n \times n}$, and let $u < 1$ and $nu < 1$. If
$(\hat L, \hat U)$ is computed by Algorithm 3.2.2 from $A$ and the pivots $\hat u_{jj}$ are
nonzero for $j = 1, \dots, n-1$, then there is $H \in \mathbb{R}^{n \times n}$ with
$$\hat L \hat U = A + H, \qquad |H| \le \gamma_n |\hat L| |\hat U|$$
entrywise.

**Generalization.** The source extends Theorem 3.3.1 to the gaxpy formulation.
Real input entries and a zero final pivot are allowed here.

**Reading.** The error estimate uses $\gamma_n|\hat L||\hat U|$ with $u<1$ and $nu<1$
in place of the printed first-order bound. -/
theorem theorem_3_3_1_gaxpy (hu : fp.u < 1) (hn : (n : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ out ∈ (algorithm_3_2_2 fp.round A).run, (∀ j : Fin n, (j : ℕ) + 1 < n → out.2 j j ≠ 0) →
      ∃ H : Matrix (Fin n) (Fin n) ℝ, out.1 * out.2 = A + H ∧
        H.abs ≤ₑ gamma fp.u n • (out.1.abs * out.2.abs) := by
  intro out hout hpiv
  obtain ⟨H, hH, hLU⟩ := exists_roundsLU_mul_eq_add hu (by simpa using hn)
    (algorithm_3_2_2_rounds A out hout) fun j i hji =>
      hpiv j (by have := Fin.lt_def.1 hji; omega)
  exact ⟨H, hLU, by simpa using hH⟩

/-- **Theorem 3.3.2** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$b \in \mathbb{R}^n$, and let the unit roundoff $u$ satisfy $u < 1$ and $3nu < 1$. Let $\hat L$
and $\hat U$ be the factors stored in a packed matrix computed by Algorithm 3.2.1 from $A$, and
assume that every diagonal entry $\hat u_{jj}$ is nonzero. Let $\hat y$ be a solution of
$\hat L y = b$ computed by row-oriented forward substitution (Algorithm 3.1.1), and let $\hat x$
be a solution of $\hat U x = \hat y$ computed by row-oriented back substitution (Algorithm
3.1.2). Then there is $E \in \mathbb{R}^{n \times n}$ with
$$(A + E) \hat x = b, \qquad |E| \le \gamma_{3n} |\hat L| |\hat U|$$
entrywise.

**Generalization.** The source assumes that $A$ is a matrix of floating point numbers. The
theorem holds for every real $A$.

**Reading.** The source prints $nu(2|A|+4|\hat L||\hat U|)+O(u^2)$. The theorem uses
the explicit $\gamma_{3n}|\hat L||\hat U|$ under $u<1$ and $3nu<1$. Every diagonal pivot
of $\hat U$ is explicitly nonzero for the solves. This theorem uses row-oriented solves. -/
theorem theorem_3_3_2 (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ F ∈ (algorithm_3_2_1 fp.round A).run, (∀ j, F j j ≠ 0) →
      ∀ y ∈ (algorithm_3_1_1 fp.round (packedL F) b).run,
      ∀ x ∈ (algorithm_3_1_2 fp.round (packedU F) y).run,
        ∃ E : Matrix (Fin n) (Fin n) ℝ, (A + E) *ᵥ x = b ∧
          E.abs ≤ₑ gamma fp.u (3 * n) • ((packedL F).abs * (packedU F).abs) := by
  intro F hF hpiv y hy x hx
  obtain ⟨E, hE, hAx⟩ := exists_roundsLU_solveDot_eq hu (by simpa using hn)
    (algorithm_3_2_1_rounds A F hF) (fun j => by rw [packedU_apply_of_le F le_rfl]; exact hpiv j)
    (algorithm_3_1_1_rounds fp _ b y hy) (algorithm_3_1_2_rounds fp _ y x hx)
  exact ⟨E, hAx, by simpa using hE⟩

/-- **Theorem 3.3.2** of [golub2013matrix], with the column-oriented solves of §3.1.3. Let
$A \in \mathbb{R}^{n \times n}$ and $b \in \mathbb{R}^n$, and let $u < 1$ and $3nu < 1$. Let
$\hat L$ and $\hat U$ be the factors stored in a packed matrix computed by Algorithm 3.2.1 from
$A$, with every $\hat u_{jj}$ nonzero. If $\hat y$ is computed from $\hat L$ and $b$ by
Algorithm 3.1.3 and $\hat x$ from $\hat U$ and $\hat y$ by Algorithm 3.1.4, then there is
$E \in \mathbb{R}^{n \times n}$ with
$$(A + E) \hat x = b, \qquad |E| \le \gamma_{3n} |\hat L| |\hat U|$$
entrywise.

**Generalization.** The real input matrix can have arbitrary entries. The source
assumes floating point entries.

**Reading.** As for the row-oriented solves, the theorem uses the explicit
$\gamma_{3n}$ coefficient and assumes $u<1$, $3nu<1$, and nonzero pivots.
This version implements the column-oriented solves. -/
theorem theorem_3_3_2_column (hu : fp.u < 1) (hn : ((3 * n : ℕ) : ℝ) * fp.u < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ∀ F ∈ (algorithm_3_2_1 fp.round A).run, (∀ j, F j j ≠ 0) →
      ∀ y ∈ (algorithm_3_1_3 fp.round (packedL F) b).run,
      ∀ x ∈ (algorithm_3_1_4 fp.round (packedU F) y).run,
        ∃ E : Matrix (Fin n) (Fin n) ℝ, (A + E) *ᵥ x = b ∧
          E.abs ≤ₑ gamma fp.u (3 * n) • ((packedL F).abs * (packedU F).abs) := by
  intro F hF hpiv y hy x hx
  obtain ⟨E, hE, hAx⟩ := exists_roundsLU_solve_eq hu (by simpa using hn)
    (algorithm_3_2_1_rounds A F hF) (fun j => by rw [packedU_apply_of_le F le_rfl]; exact hpiv j)
    (algorithm_3_1_3_rounds fp _ b y hy) (algorithm_3_1_4_rounds fp _ y x hx)
  exact ⟨E, hAx, by simpa using hE⟩

end GolubVanLoan.Chapter03
