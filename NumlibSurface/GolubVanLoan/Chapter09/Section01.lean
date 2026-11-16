/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Analysis.Matrix.Function.Basic
import Numlib.Analysis.Matrix.Function.Triangular
import Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Analytic
import Numlib.Conditioning.Problem
import Numlib.LinearAlgebra.Matrix.Sylvester

/-!
# Golub and Van Loan, Section 9.1: Eigenvalue methods

This module formalizes §9.1 of [golub2013matrix], the definition of a function $f(A)$ of a matrix
$A \in \mathbb{C}^{n \times n}$ and its computation from eigenvalue decompositions. The source
defines $f(A)$ through the Jordan form (9.1.1)–(9.1.4). Here $f(A)$ is the primary functional
calculus `pfc f A` of the backbone, and the Jordan-form expression is a theorem. The module proves
the Taylor series representation (Lemma 9.1.1, Theorem 9.1.2) with the series of $\exp$, $\log$,
$\sin$ and $\cos$, the identities (9.1.6)–(9.1.8), and the eigenvector approach (Corollary 9.1.3).
For the Schur approach it proves the divided-difference formula for $f(T)$ with $T$ upper triangular
(Theorem 9.1.4), the Parlett recurrence (9.1.11) and the exact correctness of Algorithm 9.1.1. For
the block Schur–Parlett approach it proves the block Parlett equations (9.1.12) and the unique
solvability of their Sylvester equations. Last, it defines the relative condition number of §9.1.6
and expresses it through the Fréchet derivative.

The proofs specialize the backbone modules
`Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Basic` and
`Numlib.Analysis.Normed.Algebra.PrimaryFunctionalCalculus.Analytic` (the definition of `pfc`, its
power series, products, inverses and commutation), `Numlib.Analysis.Matrix.Function.Basic` and
`Numlib.Analysis.Matrix.Function.Triangular` (`pfc` of a similarity, of a Jordan block and of a
triangular matrix, and the Sylvester equations of a block triangular matrix),
`Numlib.LinearAlgebra.Matrix.Sylvester` (the injectivity half of Lemma 7.1.5 for any finite index
types) and `Numlib.Conditioning.Problem` (the scaled relative condition number).

## Main definitions

* Algorithm 9.1.1, `GolubVanLoan.Chapter09.algorithm_9_1_1`: the Schur–Parlett algorithm for
  $F = f(T)$ with $T$ upper triangular.
* §9.1.6, `GolubVanLoan.Chapter09.condRel`: the relative condition number
  $\operatorname{cond}_{\mathrm{rel}}(f, A)$.

## Main results

* §9.1, `GolubVanLoan.Chapter09.rational_example`: the rational functions of the introduction, such
  as $f(A) = (I + A)(I - A)^{-1}$ for $f(z) = (1 + z)/(1 - z)$.
* Equations (9.1.1)–(9.1.3), `GolubVanLoan.Chapter09.equation_9_1_3`: $f(A) = X
  \operatorname{diag}(f(J_1), \dots, f(J_q)) X^{-1}$ for a Jordan decomposition $A = X
  \operatorname{diag}(J_1, \dots, J_q) X^{-1}$.
* Equation (9.1.4), `GolubVanLoan.Chapter09.equation_9_1_4`: $f$ of a Jordan block is upper
  triangular Toeplitz with entries $f^{(j-i)}(\lambda)/(j-i)!$.
* Lemma 9.1.1, `GolubVanLoan.Chapter09.lemma_9_1_1`: the Taylor series of $f$ at $z_0$ gives $f(B)$
  for a Jordan block $B$ with eigenvalue in the disk of convergence.
* Equation (9.1.6), `GolubVanLoan.Chapter09.equation_9_1_6`: $f(\lambda I + E) = \sum_{p=0}^{m-1}
  f^{(p)}(\lambda) E^p / p!$ for a Jordan block.
* Theorem 9.1.2, `GolubVanLoan.Chapter09.theorem_9_1_2`: the Taylor series of $f$ at $z_0$ gives
  $f(A)$ when every eigenvalue of $A$ lies in the disk of convergence.
* §9.1.2, `GolubVanLoan.Chapter09.taylor_exp`, `GolubVanLoan.Chapter09.taylor_log_one_sub` and
  `GolubVanLoan.Chapter09.taylor_sin_cos`: the series of $\exp(A)$, $\log(I - A)$, $\sin(A)$ and
  $\cos(A)$.
* Equation (9.1.7), `GolubVanLoan.Chapter09.equation_9_1_7`: $A f(A) = f(A) A$.
* Equation (9.1.8), `GolubVanLoan.Chapter09.equation_9_1_8`: $f(X^{-1} A X) = X^{-1} f(A) X$.
* Corollary 9.1.3, `GolubVanLoan.Chapter09.corollary_9_1_3`: $f(X \operatorname{diag}(\lambda_i)
  X^{-1}) = X \operatorname{diag}(f(\lambda_i)) X^{-1}$.
* Theorem 9.1.4, `GolubVanLoan.Chapter09.theorem_9_1_4`: the entries of $f(T)$ for upper triangular
  $T$, as sums of products of entries of $T$ times divided differences of $f$.
* Equation (9.1.11), `GolubVanLoan.Chapter09.equation_9_1_11`: the Parlett recurrence.
* Algorithm 9.1.1, `GolubVanLoan.Chapter09.algorithm_9_1_1_spec`: in exact arithmetic, for distinct
  diagonal entries, the algorithm returns $f(T)$.
* §9.1.5, `GolubVanLoan.Chapter09.blockParlett_diag`: the blocks of $f(T)$ for block upper
  triangular $T$ vanish below the diagonal, and $F_{ii} = f(T_{ii})$.
* Equation (9.1.12), `GolubVanLoan.Chapter09.equation_9_1_12`: the block Parlett equations.
* Equation (9.1.12), `GolubVanLoan.Chapter09.equation_9_1_12_unique`: if $T_{ii}$ and $T_{jj}$ have
  no common eigenvalue, then $F_{ij}$ is the unique solution of its Sylvester equation.
* §9.1.6, `GolubVanLoan.Chapter09.condRel_eq_of_hasFDerivAt`: $\operatorname{cond}_{\mathrm{rel}}(F,
  A) = \|L\| \|A\| / \|F(A)\|$ for the Fréchet derivative $L$ of $F$ at $A$.

## Conventions

* The matrix is $A \in \mathbb{C}^{n \times n}$, `A : Matrix (Fin n) (Fin n) ℂ`, and the function is
  `f : ℂ → ℂ`. Indices are 0-based.
* The source's $f(A)$ is `pfc f A`, the Hermite interpolant of $f$ and its derivatives at the roots
  of the minimal polynomial of $A$, evaluated at $A$.
* An upper triangular matrix is `Matrix.IsUpperTriangular`. A block upper triangular matrix is
  `Matrix.BlockTriangular T b` for a block index `b : Fin n → Fin p`, and its blocks are
  `Matrix.toBlock`.
* The strictly increasing sequences $S_{ij}$ of Theorem 9.1.4 are the lists `Matrix.path i s j` for
  `s ⊆ Finset.Ioo i j`.

## Implementation notes

* The source defines $f(A)$ by (9.1.3). Here (9.1.3) is a theorem,
  `GolubVanLoan.Chapter09.equation_9_1_3`, so its right side does not depend on the chosen Jordan
  decomposition.
* `pfc` is total. The hypothesis that $f(A)$ is defined appears only where a proof uses it. At a
  point where $f$ is not differentiable, Mathlib's `iteratedDeriv k f z` is $0$, and this value
  enters both sides of every identity in the same way.
* Algorithm 9.1.1 follows the algorithm conventions of `NumlibSurface.GolubVanLoan`, over any field.
  The evaluation $f(t_{ii})$ is rounded once.
* The Sylvester equations of §9.1.5 are solved on the index types of the blocks, with
  `Matrix.eq_zero_of_mul_sub_mul_eq_zero`, the injectivity half of Lemma 7.1.5 of Chapter 7 for any
  finite index types.

## Deviations from the source

* **§9.1.2, the logarithm series** (typo). The source prints $\log(I - A) = \sum_{k \ge 1} A^k / k$,
  which is the series of $-\log(I - A)$. See `GolubVanLoan.Chapter09.taylor_log_one_sub`.
* **Equation (9.1.7)** (generalization). The source restricts the identity to functions given by a
  Taylor series. It holds for every $f$. See `GolubVanLoan.Chapter09.equation_9_1_7`.
* **Equation (9.1.8)** (typo). The source prints $f(X^{-1} A X) = X f(A) X^{-1}$, with $X$ and
  $X^{-1}$ exchanged on the right. See `GolubVanLoan.Chapter09.equation_9_1_8`.

## Not formalized

* The numerical example of §9.1.3, with eigenvalues $1 \pm 10^{-5}$.
* The $3 \times 3$ illustration of Theorem 9.1.4.
* The flop counts.
* The forward-stability heuristic $\|\hat F - f(A)\| / \|f(A)\| \approx u
  \operatorname{cond}_{\mathrm{rel}}(f, A)$ of §9.1.6.
-/

open Polynomial Finset Filter Topology
open scoped Nat ENNReal

namespace GolubVanLoan.Chapter09

variable {n : ℕ}

/-! ### Complex matrices are integral and have a split minimal polynomial -/

/-- A root of the minimal polynomial of $A$ is an eigenvalue of $A$. -/
private theorem mem_spectrum_of_mem_roots {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ}
    (hμ : μ ∈ (minpoly ℂ A).roots) : μ ∈ spectrum ℂ A :=
  (spectrum.mem_iff_isRoot_minpoly (Algebra.IsIntegral.isIntegral A)).2
    (Polynomial.isRoot_of_mem_roots hμ)

/-- For $f(z) = a + bz$, $f(A) = aI + bA$. -/
private theorem pfc_affine (a b : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    pfc (fun z => a + b * z) A = a • 1 + b • A := by
  have h := pfc_polynomial (Algebra.IsIntegral.isIntegral A) (IsAlgClosed.splits _) (C a + C b * X)
  simp only [eval_add, eval_C, eval_mul, eval_X, map_add, aeval_C, map_mul, aeval_X,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
  exact h

/-! ### §9.1.1 The Jordan-based definition -/

/-- **§9.1** of [golub2013matrix], rational examples of the introduction. Let
$A \in \mathbb{C}^{n \times n}$. Then:

* for $p(z) = 1 + z$, $p(A) = I + A$;
* if $2 \notin \lambda(A)$, then for $r(z) = (1 - z/2)^{-1}(1 + z/2)$,
  $r(A) = (I - A/2)^{-1}(I + A/2)$;
* "if $f(z) = (1 + z)/(1 - z)$ and $1 \notin \lambda(A)$, then $f(A) = (I + A)(I - A)^{-1}$". -/
theorem rational_example (A : Matrix (Fin n) (Fin n) ℂ) :
    pfc (fun z : ℂ => 1 + z) A = 1 + A ∧
    ((2 : ℂ) ∉ spectrum ℂ A → pfc (fun z : ℂ => (1 - z / 2)⁻¹ * (1 + z / 2)) A =
      (1 - (2 : ℂ)⁻¹ • A)⁻¹ * (1 + (2 : ℂ)⁻¹ • A)) ∧
    ((1 : ℂ) ∉ spectrum ℂ A → pfc (fun z : ℂ => (1 + z) / (1 - z)) A = (1 + A) * (1 - A)⁻¹) := by
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral A
  have hs := IsAlgClosed.splits (minpoly ℂ A)
  -- affine functions and their `pfc`
  have hlin : ∀ a b : ℂ, pfc (fun z => a + b * z) A = a • 1 + b • A := fun a b => pfc_affine a b A
  have hcd : ∀ (a b : ℂ) (k : ℕ) (μ : ℂ), ContDiffAt ℂ k (fun z : ℂ => a + b * z) μ :=
    fun a b k μ => (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffAt
  -- the inverse of an affine function without a root on the spectrum
  have hinv : ∀ a b : ℂ, (∀ μ ∈ spectrum ℂ A, a + b * μ ≠ 0) →
      pfc (fun z => (a + b * z)⁻¹) A = (a • 1 + b • A)⁻¹ := by
    intro a b h0
    have h := (pfc_inv hI hs (fun μ _ => hcd a b _ μ)
      fun μ hμ => h0 μ (mem_spectrum_of_mem_roots hμ)).2
    rw [h, hlin, Matrix.nonsing_inv_eq_ringInverse]
  have hcdi : ∀ a b : ℂ, (∀ μ ∈ spectrum ℂ A, a + b * μ ≠ 0) → ∀ (k : ℕ) (μ : ℂ),
      μ ∈ (minpoly ℂ A).roots → ContDiffAt ℂ k (fun z : ℂ => (a + b * z)⁻¹) μ :=
    fun a b h0 k μ hμ => (hcd a b k μ).inv (h0 μ (mem_spectrum_of_mem_roots hμ))
  refine ⟨?_, fun h2 => ?_, fun h1 => ?_⟩
  · simpa using hlin 1 1
  · have h0 : ∀ μ ∈ spectrum ℂ A, (1 : ℂ) + (-2⁻¹) * μ ≠ 0 := fun μ hμ h => by
      apply h2
      convert hμ
      linear_combination 2 * h
    have hf : (fun z : ℂ => (1 - z / 2)⁻¹ * (1 + z / 2)) =
        (fun z : ℂ => (1 + (-2⁻¹) * z)⁻¹) * fun z : ℂ => 1 + 2⁻¹ * z := by
      funext z
      simp only [Pi.mul_apply]
      ring_nf
    rw [hf, pfc_mul hI hs (fun μ hμ => hcdi _ _ h0 _ μ hμ) (fun μ _ => hcd _ _ _ μ), hinv _ _ h0,
      hlin]
    congr 1
    · congr 1
      simp only [one_smul, neg_smul, sub_eq_add_neg]
    · simp only [one_smul]
  · have h0 : ∀ μ ∈ spectrum ℂ A, (1 : ℂ) + (-1) * μ ≠ 0 := fun μ hμ h => by
      apply h1
      convert hμ
      linear_combination h
    have hf : (fun z : ℂ => (1 + z) / (1 - z)) =
        (fun z : ℂ => 1 + 1 * z) * fun z : ℂ => (1 + (-1) * z)⁻¹ := by
      funext z
      simp only [Pi.mul_apply]
      ring
    rw [hf, pfc_mul hI hs (fun μ _ => hcd _ _ _ μ) (fun μ hμ => hcdi _ _ h0 _ μ hμ), hinv _ _ h0,
      hlin]
    simp only [one_smul, neg_smul, sub_eq_add_neg]

/-- **Equations (9.1.1)–(9.1.3)** of [golub2013matrix] (the Jordan-based definition), as a theorem.
Let $A, X \in \mathbb{C}^{n \times n}$ with $X$ nonsingular, and suppose that $X^{-1} A X =
\operatorname{diag}(J_1, \dots, J_q)$ is a Jordan form, with $J_i$ the Jordan block of size
$e_i$ for the eigenvalue $\mu_i$. Then for every $f : \mathbb{C} \to \mathbb{C}$,
$$f(A) = X \operatorname{diag}(F_1, \dots, F_q) X^{-1}, \qquad F_i = f(J_i).$$
The matrices $F_i$ are given by (9.1.4), `GolubVanLoan.Chapter09.equation_9_1_4`.

The Jordan form is `Matrix.jordanForm e μ`, with its rows and columns placed in `Fin n` by the
bijection `σ`. The source takes this formula as the definition of $f(A)$. -/
theorem equation_9_1_3 {q : ℕ} (e : Fin q → ℕ) (μ : Fin q → ℂ) (σ : (Σ i, Fin (e i)) ≃ Fin n)
    {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X)
    (h : X⁻¹ * A * X = Matrix.reindex σ σ (Matrix.jordanForm e μ)) (f : ℂ → ℂ) :
    pfc f A = X * Matrix.reindex σ σ
      (Matrix.blockDiagonal' fun i => pfc f (Matrix.jordanBlock (e i) (μ i))) * X⁻¹ :=
  Matrix.pfc_conj_jordanForm σ hX h f

/-- **Equation (9.1.4)** of [golub2013matrix]. Let $J = J_m(\mu)$ be the Jordan block of size $m$
for $\mu \in \mathbb{C}$, and let $f : \mathbb{C} \to \mathbb{C}$. Then $f(J)$ is upper
triangular Toeplitz:
$$f(J)_{ij} = \begin{cases} f^{(j-i)}(\mu) / (j - i)! & i \le j, \\ 0 & i > j. \end{cases}$$

The derivatives are `iteratedDeriv`, which is $0$ where $f$ is not differentiable. -/
theorem equation_9_1_4 (f : ℂ → ℂ) (m : ℕ) (μ : ℂ) (i j : Fin m) :
    pfc f (Matrix.jordanBlock m μ) i j =
      if i ≤ j then iteratedDeriv ((j : ℕ) - i) f μ / ((j : ℕ) - i)! else 0 :=
  Matrix.pfc_jordanBlock_apply f m μ i j

/-! ### §9.1.2 The Taylor series representation -/

/-- If $f$ has the power series $p$ on a ball about $z_0$, then the $k$-th coefficient of $p$ is
$f^{(k)}(z_0)/k!$, as in (9.1.5). -/
private theorem coeff_eq_taylor {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ}
    {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p z₀ r) (k : ℕ) :
    p.coeff k = iteratedDeriv k f z₀ / k ! := by
  rw [hf.hasFPowerSeriesAt.eq_formalMultilinearSeries hf.analyticAt.hasFPowerSeriesAt,
    FormalMultilinearSeries.coeff_ofScalars]

/-- If $f$ has the power series $p$ on the ball of radius $r$ about $z_0$ and every eigenvalue of
$A$ lies in this ball, then $\sum_k p_k (A - z_0 I)^k = f(A)$. -/
private theorem hasSum_pfc_matrix {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ}
    {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p z₀ r) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ μ ∈ spectrum ℂ A, μ ∈ Metric.eball z₀ r) :
    HasSum (fun k => p.coeff k • (A - z₀ • 1) ^ k) (pfc f A) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using
    hasSum_pfc hf (Algebra.IsIntegral.isIntegral A) (IsAlgClosed.splits _) hA

/-- The spectrum of the Jordan block $J_m(c)$ is contained in $\{c\}$. -/
private theorem spectrum_jordanBlock_subset (m : ℕ) (c : ℂ) :
    spectrum ℂ (Matrix.jordanBlock m c) ⊆ {c} := by
  intro μ hμ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_jordanBlock, IsRoot.def,
    eval_pow, eval_sub, eval_X, eval_C] at hμ
  exact sub_eq_zero.mp (pow_eq_zero_iff'.mp hμ).1

/-- **Lemma 9.1.1** of [golub2013matrix]. Let $f : \mathbb{C} \to \mathbb{C}$ be given by its Taylor
series (9.1.5)
$$f(z) = \sum_{k=0}^{\infty} \frac{f^{(k)}(z_0)}{k!} (z - z_0)^k$$
for $|z - z_0| < r$, with $r \in (0, \infty]$. Let $B = \lambda I + E$ be the Jordan block of
size $m$ for $\lambda$, with $|\lambda - z_0| < r$. Then
$$f(B) = \sum_{k=0}^{\infty} \frac{f^{(k)}(z_0)}{k!} (B - z_0 I)^k.$$

The hypothesis on $f$ is `HasFPowerSeriesOnBall f p z₀ r`, that is, $f$ is the sum of a power
series $p$ on the open ball of radius $r$ about $z_0$. The series of matrices converges
entrywise (`HasSum`). -/
theorem lemma_9_1_1 {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (m : ℕ) {c : ℂ} (hc : c ∈ Metric.eball z₀ r) :
    HasSum (fun k => (iteratedDeriv k f z₀ / k !) • (Matrix.jordanBlock m c - z₀ • 1) ^ k)
      (pfc f (Matrix.jordanBlock m c)) := by
  simpa only [coeff_eq_taylor hf] using hasSum_pfc_matrix hf fun μ hμ => by
    rw [Set.mem_singleton_iff.mp (spectrum_jordanBlock_subset m c hμ)]
    exact hc

/-- **Equation (9.1.6)** of [golub2013matrix]. Let $B = \lambda I + E$ be the Jordan block of size
$m$ for $\lambda \in \mathbb{C}$, so that $E$ is the Jordan block for $0$. Then $(E^p)_{ij} = 1$
if $i + p = j$ and $(E^p)_{ij} = 0$ otherwise, and for every $f : \mathbb{C} \to \mathbb{C}$
$$f(B) = \sum_{p=0}^{m-1} \frac{f^{(p)}(\lambda)}{p!} E^p.$$
-/
theorem equation_9_1_6 (f : ℂ → ℂ) (m : ℕ) (c : ℂ) :
    Matrix.jordanBlock m c = c • 1 + Matrix.jordanBlock m 0 ∧
    (∀ (p : ℕ) (i j : Fin m),
      (Matrix.jordanBlock m (0 : ℂ) ^ p) i j = if (i : ℕ) + p = j then 1 else 0) ∧
    pfc f (Matrix.jordanBlock m c) =
      ∑ p ∈ range m, (iteratedDeriv p f c / p !) • Matrix.jordanBlock m 0 ^ p := by
  refine ⟨by rw [Matrix.jordanBlock_eq_add_smul_one, add_comm],
    fun p i j => Matrix.jordanBlock_zero_pow_apply p i j, ?_⟩
  rw [Matrix.pfc_jordanBlock]
  rfl

/-- **Theorem 9.1.2** of [golub2013matrix]. Let $f : \mathbb{C} \to \mathbb{C}$ be given by its
Taylor series (9.1.5) on $|z - z_0| < r$, with $r \in (0, \infty]$, and let
$A \in \mathbb{C}^{n \times n}$ satisfy $|\lambda - z_0| < r$ for every
$\lambda \in \lambda(A)$. Then
$$f(A) = \sum_{k=0}^{\infty} \frac{f^{(k)}(z_0)}{k!} (A - z_0 I)^k.$$

The hypothesis on $f$ is `HasFPowerSeriesOnBall f p z₀ r`. The series converges in the entrywise
topology of $\mathbb{C}^{n \times n}$. -/
theorem theorem_9_1_2 {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z₀ : ℂ} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ μ ∈ spectrum ℂ A, μ ∈ Metric.eball z₀ r) :
    HasSum (fun k => (iteratedDeriv k f z₀ / k !) • (A - z₀ • 1) ^ k) (pfc f A) := by
  simpa only [coeff_eq_taylor hf] using hasSum_pfc_matrix hf hA

/-- If $f(z) = \sum_k c_k z^k$ for every $z \in \mathbb{C}$, then $f(A) = \sum_k c_k A^k$. -/
private theorem hasSum_pfc_of_hasSum {f : ℂ → ℂ} {c : ℕ → ℂ}
    (h : ∀ z, HasSum (fun k => c k * z ^ k) (f z)) (A : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun k => c k • A ^ k) (pfc f A) := by
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_smul, sub_zero] using
    hasSum_pfc_matrix (hasFPowerSeriesOnBall_ofScalars_of_hasSum h) (A := A) fun μ _ => by simp

/-- **§9.1.2** of [golub2013matrix], the exponential series. For every
$A \in \mathbb{C}^{n \times n}$,
$$\exp(A) = \sum_{k=0}^{\infty} \frac{A^k}{k!},$$
and `pfc Complex.exp A` is Mathlib's matrix exponential `NormedSpace.exp A`. -/
theorem taylor_exp (A : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun k => ((k ! : ℂ)⁻¹) • A ^ k) (pfc Complex.exp A) ∧
    pfc Complex.exp A = NormedSpace.exp A := by
  refine ⟨hasSum_pfc_of_hasSum (fun z => ?_) A,
    pfc_exp_eq_normedSpace_exp (Algebra.IsIntegral.isIntegral A)⟩
  rw [Complex.exp_eq_exp_ℂ]
  simpa only [smul_eq_mul] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z

/-- **§9.1.2** of [golub2013matrix], the logarithm series, with the sign corrected. Let
$A \in \mathbb{C}^{n \times n}$ with $|\lambda| < 1$ for every $\lambda \in \lambda(A)$. Then
$$\log(I - A) = -\sum_{k=1}^{\infty} \frac{A^k}{k}.$$

**Typo.** The source prints $\log(I - A) = \sum_{k \ge 1} A^k / k$, which is the series of
$-\log(I - A)$.

The logarithm is the principal branch `Complex.log`. -/
theorem taylor_log_one_sub {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, ‖μ‖ < 1) :
    HasSum (fun k : ℕ => -(((k + 1 : ℕ) : ℂ)⁻¹) • A ^ (k + 1))
      (pfc (fun z => Complex.log (1 - z)) A) := by
  have h := hasSum_pfc_matrix Complex.hasFPowerSeriesOnBall_log_one_sub (A := A) fun μ hμ => by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
    exact hA μ hμ
  simp only [FormalMultilinearSeries.coeff_ofScalars, zero_smul, sub_zero] at h
  simpa using (hasSum_nat_add_iff' 1).mpr h

/-- The coefficients of the sine series: $0$ at even powers and $(-1)^{\lfloor k/2 \rfloor} / k!$ at
an odd power $k$. -/
private noncomputable def sinCoeff (k : ℕ) : ℂ :=
  if Even k then 0 else (-1) ^ (k / 2) / (k ! : ℂ)

/-- The coefficients of the cosine series: $(-1)^{k/2} / k!$ at an even power $k$ and $0$ at odd
powers. -/
private noncomputable def cosCoeff (k : ℕ) : ℂ :=
  if Even k then (-1) ^ (k / 2) / (k ! : ℂ) else 0

private theorem sinCoeff_odd (k : ℕ) : sinCoeff (2 * k + 1) = (-1) ^ k / ((2 * k + 1) ! : ℂ) := by
  have h1 : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one k)
  have h2 : (2 * k + 1) / 2 = k := by omega
  rw [sinCoeff, ite_eq_right h1, h2]

private theorem cosCoeff_even (k : ℕ) : cosCoeff (2 * k) = (-1) ^ k / ((2 * k) ! : ℂ) := by
  have h2 : 2 * k / 2 = k := by omega
  rw [cosCoeff, ite_eq_left (even_two_mul k), h2]

private theorem sinCoeff_eq_zero {k : ℕ} (hk : k ∉ Set.range fun j : ℕ => 2 * j + 1) :
    sinCoeff k = 0 := by
  rcases Nat.even_or_odd k with he | ⟨j, rfl⟩
  · rw [sinCoeff, ite_eq_left he]
  · exact absurd ⟨j, rfl⟩ hk

private theorem cosCoeff_eq_zero {k : ℕ} (hk : k ∉ Set.range fun j : ℕ => 2 * j) :
    cosCoeff k = 0 := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ho
  · exact absurd ⟨j, by ring⟩ hk
  · rw [cosCoeff, ite_eq_right (Nat.not_even_iff_odd.mpr ho)]

private theorem injective_two_mul_add_one : Function.Injective fun j : ℕ => 2 * j + 1 :=
  fun a b h => by simp only at h; omega

private theorem injective_two_mul : Function.Injective fun j : ℕ => 2 * j :=
  fun a b h => by simp only at h; omega

/-- **§9.1.2** of [golub2013matrix], the sine and cosine series. For every
$A \in \mathbb{C}^{n \times n}$,
$$\sin(A) = \sum_{k=0}^{\infty} \frac{(-1)^k A^{2k+1}}{(2k+1)!}, \qquad \cos(A) =
  \sum_{k=0}^{\infty} \frac{(-1)^k A^{2k}}{(2k)!}.$$
-/
theorem taylor_sin_cos (A : Matrix (Fin n) (Fin n) ℂ) :
    HasSum (fun k : ℕ => ((-1) ^ k / ((2 * k + 1) ! : ℂ)) • A ^ (2 * k + 1)) (pfc Complex.sin A) ∧
    HasSum (fun k : ℕ => ((-1) ^ k / ((2 * k) ! : ℂ)) • A ^ (2 * k)) (pfc Complex.cos A) := by
  constructor
  · have hs : ∀ z, HasSum (fun k => sinCoeff k * z ^ k) (Complex.sin z) := fun z => by
      rw [← injective_two_mul_add_one.hasSum_iff fun k hk => by rw [sinCoeff_eq_zero hk, zero_mul]]
      simpa only [Function.comp_def, sinCoeff_odd, div_mul_eq_mul_div] using Complex.hasSum_sin z
    have h := hasSum_pfc_of_hasSum hs A
    rw [← injective_two_mul_add_one.hasSum_iff fun k hk => by rw [sinCoeff_eq_zero hk, zero_smul]]
      at h
    simpa only [Function.comp_def, sinCoeff_odd] using h
  · have hc : ∀ z, HasSum (fun k => cosCoeff k * z ^ k) (Complex.cos z) := fun z => by
      rw [← injective_two_mul.hasSum_iff fun k hk => by rw [cosCoeff_eq_zero hk, zero_mul]]
      simpa only [Function.comp_def, cosCoeff_even, div_mul_eq_mul_div] using Complex.hasSum_cos z
    have h := hasSum_pfc_of_hasSum hc A
    rw [← injective_two_mul.hasSum_iff fun k hk => by rw [cosCoeff_eq_zero hk, zero_smul]] at h
    simpa only [Function.comp_def, cosCoeff_even] using h

/-- **Equation (9.1.7)** of [golub2013matrix]. For every $A \in \mathbb{C}^{n \times n}$ and every
$f : \mathbb{C} \to \mathbb{C}$,
$$A f(A) = f(A) A.$$

**Generalization.** The source restricts the identity to functions given by a Taylor series,
"for clarity". It holds for every $f$. -/
theorem equation_9_1_7 (f : ℂ → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * pfc f A = pfc f A * A :=
  (commute_pfc A f).eq

/-- **Equation (9.1.8)** of [golub2013matrix], corrected. Let $X \in \mathbb{C}^{n \times n}$ be
nonsingular. For every $A \in \mathbb{C}^{n \times n}$ and every
$f : \mathbb{C} \to \mathbb{C}$,
$$f(X^{-1} A X) = X^{-1} f(A) X.$$

**Typo.** The source prints $X f(A) X^{-1}$ on the right, with $X$ and $X^{-1}$ exchanged. Its
own use in §9.1.4, $f(A) = Q f(T) Q^H$ from $A = Q T Q^H$, is the corrected form. -/
theorem equation_9_1_8 (f : ℂ → ℂ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X)
    (A : Matrix (Fin n) (Fin n) ℂ) : pfc f (X⁻¹ * A * X) = X⁻¹ * pfc f A * X := by
  have hdet : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hX
  have h := Matrix.pfc_conj ((Matrix.isUnit_nonsing_inv_iff).mpr hX) f A
  rwa [Matrix.nonsing_inv_nonsing_inv X hdet] at h

/-! ### §9.1.3 The eigenvector approach -/

/-- **Corollary 9.1.3** of [golub2013matrix], with (9.1.9). Let $A, X \in \mathbb{C}^{n \times n}$
with $X$ nonsingular and $A = X \operatorname{diag}(\lambda_1, \dots, \lambda_n) X^{-1}$. Then
for every $f : \mathbb{C} \to \mathbb{C}$,
$$f(A) = X \operatorname{diag}(f(\lambda_1), \dots, f(\lambda_n)) X^{-1}.$$

For a diagonalizable matrix only the values of $f$ on the spectrum matter, so no hypothesis on
$f$ is needed. -/
theorem corollary_9_1_3 (f : ℂ → ℂ) {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X)
    (d : Fin n → ℂ) (hA : A = X * Matrix.diagonal d * X⁻¹) :
    pfc f A = X * Matrix.diagonal (f ∘ d) * X⁻¹ := by
  rw [hA, Matrix.pfc_conj hX, Matrix.pfc_diagonal]

/-! ### §9.1.4 The Schur decomposition approach -/

/-- **Theorem 9.1.4** of [golub2013matrix], with (9.1.10). Let $T \in \mathbb{C}^{n \times n}$ be
upper triangular with $\lambda_i = t_{ii}$, let $f : \mathbb{C} \to \mathbb{C}$, and let
$F = f(T)$. Then $f_{ij} = 0$ for $i > j$, $f_{ii} = f(\lambda_i)$, and for $i < j$
$$f_{ij} = \sum_{(s_0, \dots, s_k) \in S_{ij}} t_{s_0 s_1} t_{s_1 s_2} \cdots t_{s_{k-1} s_k} \,
  f[\lambda_{s_0}, \dots, \lambda_{s_k}],$$
where $S_{ij}$ is the set of strictly increasing sequences of indices that start at $i$ and end
at $j$, and $f[\cdot]$ is the divided difference, confluent where eigenvalues repeat.

A sequence in $S_{ij}$ is `Matrix.path i s j` for a set `s` of interior indices in
`Finset.Ioo i j`. The product is `Matrix.pathProd`, and the divided difference is
`Hermite.divDiff` of the multiset of diagonal entries along the path. -/
theorem theorem_9_1_4 {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.IsUpperTriangular) (f : ℂ → ℂ) :
    (∀ i j, j < i → pfc f T i j = 0) ∧ (∀ i, pfc f T i i = f (T i i)) ∧
    ∀ i j, i < j → pfc f T i j = ∑ s ∈ (Ioo i j).powerset,
      Matrix.pathProd T (Matrix.path i s j) *
        Hermite.divDiff f ((Matrix.path i s j).map fun k => T k k) :=
  ⟨fun _ _ hji => Matrix.BlockTriangular.pfc hT f hji,
    Matrix.pfc_apply_self_of_isUpperTriangular hT f,
    fun _ _ hij => Matrix.pfc_apply_eq_sum_divDiff hT f hij⟩

/-- **Equation (9.1.11)** of [golub2013matrix] (the Parlett recurrence). Let
$T \in \mathbb{C}^{n \times n}$ be upper triangular, let $f : \mathbb{C} \to \mathbb{C}$ and
$F = f(T)$, and let $i < j$. Then the commutativity equation $FT = TF$ gives
$$\sum_{k=i}^{j} f_{ik} t_{kj} = \sum_{k=i}^{j} t_{ik} f_{kj},$$
and if $t_{ii} \neq t_{jj}$, then
$$f_{ij} = t_{ij} \frac{f_{jj} - f_{ii}}{t_{jj} - t_{ii}} + \sum_{k=i+1}^{j-1} \frac{t_{ik}
  f_{kj} - f_{ik} t_{kj}}{t_{jj} - t_{ii}}.$$
-/
theorem equation_9_1_11 {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.IsUpperTriangular) (f : ℂ → ℂ)
    {i j : Fin n} (hij : i < j) :
    (∑ k ∈ Icc i j, pfc f T i k * T k j = ∑ k ∈ Icc i j, T i k * pfc f T k j) ∧
    (T i i ≠ T j j → pfc f T i j = T i j * (pfc f T j j - pfc f T i i) / (T j j - T i i) +
      ∑ k ∈ Ioo i j, (T i k * pfc f T k j - pfc f T i k * T k j) / (T j j - T i i)) := by
  have hF : (pfc f T).IsUpperTriangular := Matrix.BlockTriangular.pfc hT f
  refine ⟨?_, Matrix.pfc_apply_eq_parlett hT f hij⟩
  rw [← Matrix.IsUpperTriangular.mul_apply hF hT, ← Matrix.IsUpperTriangular.mul_apply hT hF,
    (commute_pfc T f).eq]

section Algorithm

variable {K : Type} [Field K] {M : Type → Type} [Monad M]

/-- The order in which Algorithm 9.1.1 visits the strictly upper triangular positions: the pairs
$(i, j)$ with $j = i + p$ for $p = 1, \dots, n-1$ and $i = 0, \dots, n-1-p$, one superdiagonal
after another. In the source's 1-based notation this is $p = 1{:}n-1$, $i = 1{:}n-p$. -/
def superdiagPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.range' 1 (n - 1)).flatMap fun p =>
    (List.finRange n).filterMap fun (i : Fin n) =>
      if h : (i : ℕ) + p < n then some (i, ⟨i + p, h⟩) else none

/-- **Algorithm 9.1.1** of [golub2013matrix] (Schur–Parlett). Given an upper triangular $T$ with
distinct eigenvalues, the algorithm computes $F = f(T)$.
```
for i = 1:n
    f_ii = f(t_ii)
end
for p = 1:n-1
    for i = 1:n-p
        j = i + p
        s = t_ij (f_jj - f_ii)
        for k = i+1:j-1
            s = s + t_ik f_kj - f_ik t_kj
        end
        f_ij = s/(t_jj - t_ii)
    end
end
```
The program starts from the zero matrix and works over any field $K$, with `f : K → K`. The
value $f(t_{ii})$ is rounded once, and the loop body rounds every addition, subtraction,
multiplication and division in the source's left-to-right order. The positions $(i, j)$ are
visited in the order `GolubVanLoan.Chapter09.superdiagPairs`. -/
def algorithm_9_1_1 (rnd : K → M K) (f : K → K) (T : Matrix (Fin n) (Fin n) K) :
    M (Matrix (Fin n) (Fin n) K) := do
  let F₀ ← (List.finRange n).foldlM (fun F i => do
      let v ← rnd (f (T i i))
      pure (F.updateRow i (Function.update (F i) i v))) (0 : Matrix (Fin n) (Fin n) K)
  (superdiagPairs n).foldlM (fun F ij => do
      let d₀ ← rnd (F ij.2 ij.2 - F ij.1 ij.1)
      let s₀ ← rnd (T ij.1 ij.2 * d₀)
      let s ← ((List.finRange n).filter fun k => ij.1 < k ∧ k < ij.2).foldlM (fun s k => do
          let a ← rnd (T ij.1 k * F k ij.2)
          let t ← rnd (s + a)
          let b ← rnd (F ij.1 k * T k ij.2)
          rnd (t - b)) s₀
      let d ← rnd (T ij.2 ij.2 - T ij.1 ij.1)
      let v ← rnd (s / d)
      pure (F.updateRow ij.1 (Function.update (F ij.1) ij.2 v))) F₀

end Algorithm

/-- The pairs in `GolubVanLoan.Chapter09.superdiagPairs n` are exactly the pairs $(a, b)$ with
$a < b$. -/
private theorem mem_superdiagPairs {a b : Fin n} : (a, b) ∈ superdiagPairs n ↔ a < b := by
  simp only [superdiagPairs, List.mem_flatMap, List.mem_range', List.mem_filterMap,
    List.mem_finRange, true_and, Option.dite_none_right_eq_some, Option.some.injEq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨p, ⟨k, hk, rfl⟩, i, h, rfl, rfl⟩
    rw [Fin.lt_def]
    simp only
    omega
  · intro hab
    rw [Fin.lt_def] at hab
    refine ⟨(b : ℕ) - a, ⟨(b : ℕ) - a - 1, by omega, by omega⟩, a, by omega, rfl, ?_⟩
    ext
    simp only
    omega

/-- `GolubVanLoan.Chapter09.superdiagPairs n` visits the superdiagonals in increasing order of
$j - i$. -/
private theorem pairwise_superdiagPairs :
    (superdiagPairs n).Pairwise fun x y => (x.2 : ℕ) - x.1 ≤ (y.2 : ℕ) - y.1 := by
  have hdiff : ∀ p, ∀ x ∈ (List.finRange n).filterMap (fun (i : Fin n) =>
      if h : (i : ℕ) + p < n then some (i, (⟨i + p, h⟩ : Fin n)) else none),
      (x.2 : ℕ) - x.1 = p := by
    intro p x hx
    simp only [List.mem_filterMap, List.mem_finRange, true_and,
      Option.dite_none_right_eq_some, Option.some.injEq] at hx
    obtain ⟨i, h, rfl⟩ := hx
    simp
  rw [superdiagPairs, List.pairwise_flatMap]
  refine ⟨fun p _ => ?_, ?_⟩
  · refine List.Pairwise.imp_of_mem ?_ (List.pairwise_of_forall (R := fun _ _ => True)
      fun _ _ => trivial)
    intro x y hx hy _
    rw [hdiff p x hx, hdiff p y hy]
  · refine (List.pairwise_lt_range' (s := 1) (n := n - 1)).imp_of_mem ?_
    intro p q _ _ hpq x hx y hy
    rw [hdiff p x hx, hdiff q y hy]
    exact hpq.le

/-- In exact arithmetic the inner loop of Algorithm 9.1.1 computes the running sum
$s_0 + \sum_k (a_k - b_k)$. -/
private theorem foldl_add_sub {ι : Type*} (a b : ι → ℂ) (l : List ι) (s₀ : ℂ) :
    l.foldl (fun s k => s + a k - b k) s₀ = s₀ + (l.map fun k => a k - b k).sum := by
  induction l generalizing s₀ with
  | nil => simp
  | cons k l ih => rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]; ring

/-- A sum over a filtered `List.finRange n` equals the `Finset` sum over the filter. -/
private theorem sum_map_filter_finRange (P : Fin n → Prop) [DecidablePred P] (g : Fin n → ℂ) :
    (((List.finRange n).filter fun k => decide (P k)).map g).sum = ∑ k with P k, g k := by
  rw [Finset.sum_filter, Fin.sum_univ_def]
  induction (List.finRange n) with
  | nil => simp
  | cons a l ih => by_cases h : P a <;> simp [h, ih]

/-- **Algorithm 9.1.1** of [golub2013matrix], exact semantics. Let $T \in \mathbb{C}^{n \times n}$
be upper triangular with distinct diagonal entries, and let $f : \mathbb{C} \to \mathbb{C}$.
Then in exact arithmetic Algorithm 9.1.1 returns $f(T)$.

Each step is the Parlett recurrence (9.1.11), whose right side reads only entries on earlier
superdiagonals. -/
theorem algorithm_9_1_1_spec (f : ℂ → ℂ) {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.IsUpperTriangular) (hdist : Function.Injective fun i => T i i) :
    Id.run (algorithm_9_1_1 pure f T) = pfc f T := by
  set G := pfc f T with hG
  have hGu : G.IsUpperTriangular := Matrix.BlockTriangular.pfc hT f
  -- the exact loop body
  let body : Matrix (Fin n) (Fin n) ℂ → Fin n × Fin n → Matrix (Fin n) (Fin n) ℂ := fun F ij =>
    F.updateRow ij.1 (Function.update (F ij.1) ij.2
      ((((List.finRange n).filter fun k => ij.1 < k ∧ k < ij.2).foldl
        (fun s k => s + T ij.1 k * F k ij.2 - F ij.1 k * T k ij.2)
        (T ij.1 ij.2 * (F ij.2 ij.2 - F ij.1 ij.1))) / (T ij.2 ij.2 - T ij.1 ij.1)))
  let F₀ : Matrix (Fin n) (Fin n) ℂ := (List.finRange n).foldl
    (fun F i => F.updateRow i (Function.update (F i) i (f (T i i)))) 0
  have hrun : Id.run (algorithm_9_1_1 pure f T) = (superdiagPairs n).foldl body F₀ := by
    simp only [algorithm_9_1_1, Id.run_bind, Id.run_pure, List.idRun_foldlM]
    rfl
  -- the diagonal and lower triangle after the first loop
  have key : ∀ (l : List (Fin n)) (F : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n),
      (l.foldl (fun F i => F.updateRow i (Function.update (F i) i (f (T i i)))) F) a b =
        if a = b ∧ a ∈ l then f (T a a) else F a b := by
    intro l
    induction l with
    | nil => intro F a b; simp
    | cons x l ih =>
      intro F a b
      rw [List.foldl_cons, ih]
      by_cases hab : a = b
      · subst hab
        by_cases hax : a = x
        · subst hax
          simp [Matrix.updateRow_apply]
        · simp [Matrix.updateRow_apply, hax]
      · rw [ite_eq_right (fun h => hab h.1), ite_eq_right (fun h => hab h.1),
          Matrix.updateRow_apply]
        split_ifs with hax
        · subst hax
          rw [Function.update_of_ne (Ne.symm hab)]
        · rfl
  have hF₀ : ∀ a b : Fin n, b ≤ a → F₀ a b = G a b := by
    intro a b hba
    rw [show F₀ a b = if a = b ∧ a ∈ List.finRange n then f (T a a)
      else (0 : Matrix (Fin n) (Fin n) ℂ) a b from key _ _ a b]
    rcases eq_or_lt_of_le hba with rfl | hlt
    · rw [ite_eq_left ⟨rfl, List.mem_finRange b⟩, hG, Matrix.pfc_apply_self_of_isUpperTriangular hT]
    · rw [ite_eq_right (fun h => (ne_of_gt hlt) h.1), Matrix.zero_apply,
        hGu (show id b < id a from hlt)]
  -- one step of the superdiagonal loop keeps the invariant
  have hstep : ∀ (pre : List (Fin n × Fin n)) (i j : Fin n) (post : List (Fin n × Fin n))
      (F : Matrix (Fin n) (Fin n) ℂ), pre ++ (i, j) :: post = superdiagPairs n →
      (∀ a b, b ≤ a ∨ (a, b) ∈ pre → F a b = G a b) →
      ∀ a b, b ≤ a ∨ (a, b) ∈ pre ++ [(i, j)] → body F (i, j) a b = G a b := by
    intro pre i j post F hL hF
    have hij : i < j := mem_superdiagPairs.mp (hL ▸ List.mem_append_right _ List.mem_cons_self)
    have hpre : ∀ a b : Fin n, a < b → (b : ℕ) - a < (j : ℕ) - i → (a, b) ∈ pre := by
      intro a b hab hd
      have hmem : (a, b) ∈ pre ++ (i, j) :: post := hL ▸ mem_superdiagPairs.mpr hab
      rcases List.mem_append.mp hmem with h | h
      · exact h
      · exfalso
        rcases List.mem_cons.mp h with h | h
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          omega
        · have hp := pairwise_superdiagPairs (n := n)
          rw [← hL, List.pairwise_append, List.pairwise_cons] at hp
          have := hp.2.1.1 _ h
          simp only at this
          omega
    have hne : T i i ≠ T j j := fun h => (ne_of_lt hij) (hdist h)
    have hval : ((((List.finRange n).filter fun k => i < k ∧ k < j).foldl
        (fun s k => s + T i k * F k j - F i k * T k j) (T i j * (F j j - F i i))) /
          (T j j - T i i)) = G i j := by
      rw [foldl_add_sub, sum_map_filter_finRange (fun k => i < k ∧ k < j),
        hF j j (Or.inl le_rfl), hF i i (Or.inl le_rfl),
        hG, Matrix.pfc_apply_eq_parlett hT f hij hne, ← hG, add_div, Finset.sum_div]
      congr 1
      refine Finset.sum_congr (by ext k; simp) fun k hk => ?_
      rw [Finset.mem_Ioo] at hk
      rw [Fin.lt_def] at hij
      have hk1 := hk.1
      have hk2 := hk.2
      rw [Fin.lt_def] at hk1 hk2
      rw [hF k j (Or.inr (hpre k j hk.2 (by omega))), hF i k (Or.inr (hpre i k hk.1 (by omega)))]
    intro a b hab
    simp only [body, Matrix.updateRow_apply]
    by_cases hai : a = i
    · subst hai
      by_cases hbj : b = j
      · subst hbj
        rw [ite_eq_left rfl, Function.update_self, hval]
      · rw [ite_eq_left rfl, Function.update_of_ne hbj]
        refine hF a b ?_
        rcases hab with h | h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inr h
          · simp [hbj] at h
    · rw [ite_eq_right hai]
      refine hF a b ?_
      rcases hab with h | h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inr h
        · simp [hai] at h
  -- the whole loop
  have hfold : ∀ (post pre : List (Fin n × Fin n)) (F : Matrix (Fin n) (Fin n) ℂ),
      pre ++ post = superdiagPairs n → (∀ a b, b ≤ a ∨ (a, b) ∈ pre → F a b = G a b) →
      ∀ a b, post.foldl body F a b = G a b := by
    intro post
    induction post with
    | nil =>
      intro pre F hL hF a b
      rw [List.append_nil] at hL
      refine hF a b ?_
      rcases le_or_gt b a with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [hL]; exact mem_superdiagPairs.mpr h)
    | cons x post ih =>
      intro pre F hL hF
      obtain ⟨i, j⟩ := x
      rw [List.foldl_cons]
      exact ih (pre ++ [(i, j)]) (body F (i, j)) (by rw [← hL]; simp)
        (hstep pre i j post F hL hF)
  ext a b
  rw [hrun]
  exact hfold _ [] F₀ (List.nil_append _) (fun a b h => hF₀ a b (h.resolve_right (by simp))) a b

/-! ### §9.1.5 A block Schur–Parlett approach -/

/-- **§9.1.5** of [golub2013matrix], the diagonal blocks. Let $T \in \mathbb{C}^{n \times n}$ be
block upper triangular, let $f : \mathbb{C} \to \mathbb{C}$ and $F = f(T)$, partitioned
conformally with $T$. Then $F_{ij} = 0$ for $i > j$ and $F_{ii} = f(T_{ii})$ for every $i$.

The block structure is `Matrix.BlockTriangular T b` for a block index `b : Fin n → Fin p`, and
the block $(i, j)$ is `Matrix.toBlock` on the rows with block index $i$ and the columns with
block index $j$. -/
theorem blockParlett_diag {p : ℕ} {b : Fin n → Fin p} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular b) (f : ℂ → ℂ) :
    (∀ i j : Fin p, j < i → (pfc f T).toBlock (b · = i) (b · = j) = 0) ∧
    ∀ i : Fin p, (pfc f T).toBlock (b · = i) (b · = i) = pfc f (T.toBlock (b · = i) (b · = i)) := by
  refine ⟨fun i j hji => ?_, fun i => Matrix.BlockTriangular.toBlock_pfc hT
    (IsAlgClosed.splits _) i f⟩
  ext x y
  rw [Matrix.toBlock_apply, Matrix.zero_apply]
  exact Matrix.BlockTriangular.pfc hT f (by rw [x.2, y.2]; exact hji)

/-- **Equation (9.1.12)** of [golub2013matrix] (the block Parlett equations). Let
$T \in \mathbb{C}^{n \times n}$ be block upper triangular, let $f : \mathbb{C} \to \mathbb{C}$
and $F = f(T)$, with blocks as in `GolubVanLoan.Chapter09.blockParlett_diag`. For block indices
$i < j$,
$$F_{ij} T_{jj} - T_{ii} F_{ij} = T_{ij} F_{jj} - F_{ii} T_{ij} + \sum_{k=i+1}^{j-1} (T_{ik}
  F_{kj} - F_{ik} T_{kj}).$$
This is a Sylvester equation for the block $F_{ij}$ whose right side involves only blocks nearer
the diagonal. -/
theorem equation_9_1_12 {p : ℕ} {b : Fin n → Fin p} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular b) (f : ℂ → ℂ) {i j : Fin p} (hij : i < j) :
    let F := pfc f T
    let blk := fun (X : Matrix (Fin n) (Fin n) ℂ) (k l : Fin p) => X.toBlock (b · = k) (b · = l)
    blk F i j * blk T j j - blk T i i * blk F i j =
      blk T i j * blk F j j - blk F i i * blk T i j +
        ∑ k ∈ Ioo i j, (blk T i k * blk F k j - blk F i k * blk T k j) :=
  Matrix.BlockTriangular.pfc_sylvester hT f hij

/-- **Equation (9.1.12)** of [golub2013matrix], unique solvability. Let
$T \in \mathbb{C}^{n \times n}$ be block upper triangular, let $f : \mathbb{C} \to \mathbb{C}$
and $F = f(T)$, and let $i < j$ be block indices with $\lambda(T_{ii}) \cap \lambda(T_{jj}) =
\emptyset$, as the clustering of §9.1.5 arranges. Then a matrix $X$ of the shape of $F_{ij}$
satisfies
$$X T_{jj} - T_{ii} X = T_{ij} F_{jj} - F_{ii} T_{ij} + \sum_{k=i+1}^{j-1} (T_{ik} F_{kj} -
  F_{ik} T_{kj})$$
if and only if $X = F_{ij}$. So the blocks of $F$ can be computed one superdiagonal at a time.

The proof combines (9.1.12) with the injectivity of $X \mapsto T_{ii} X - X T_{jj}$ for disjoint
spectra, the content of Lemma 7.1.5 of Chapter 7 (`Matrix.eq_zero_of_mul_sub_mul_eq_zero`), on
the index types of the blocks. -/
theorem equation_9_1_12_unique {p : ℕ} {b : Fin n → Fin p} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.BlockTriangular b) (f : ℂ → ℂ) {i j : Fin p} (hij : i < j)
    (hdisj : spectrum ℂ (T.toBlock (b · = i) (b · = i)) ∩
      spectrum ℂ (T.toBlock (b · = j) (b · = j)) = ∅) :
    let F := pfc f T
    let blk := fun (X : Matrix (Fin n) (Fin n) ℂ) (k l : Fin p) => X.toBlock (b · = k) (b · = l)
    ∀ X : Matrix {a // b a = i} {a // b a = j} ℂ,
      X * blk T j j - blk T i i * X =
          blk T i j * blk F j j - blk F i i * blk T i j +
            ∑ k ∈ Ioo i j, (blk T i k * blk F k j - blk F i k * blk T k j) ↔
        X = blk F i j := by
  have h12 := equation_9_1_12 hT f hij
  dsimp only at h12 ⊢
  intro X
  set Ti := T.toBlock (b · = i) (b · = i) with hTi
  set Tj := T.toBlock (b · = j) (b · = j) with hTj
  set Fij := (pfc f T).toBlock (b · = i) (b · = j) with hFij
  constructor
  · intro hX
    rw [← h12, ← sub_eq_zero] at hX
    refine sub_eq_zero.1
      (Matrix.eq_zero_of_mul_sub_mul_eq_zero (Set.disjoint_iff_inter_eq_empty.2 hdisj) ?_)
    calc Ti * (X - Fij) - (X - Fij) * Tj = -(X * Tj - Ti * X - (Fij * Tj - Ti * Fij)) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul]
          abel
      _ = 0 := by rw [hX, neg_zero]
  · rintro rfl
    exact h12

/-! ### §9.1.6 Sensitivity of matrix functions -/

section Condition

/-- **§9.1.6** of [golub2013matrix], the relative condition number of a matrix function. For a map
$F : V \to V$ of a normed space and $A \in V$,
$$\operatorname{cond}_{\mathrm{rel}}(F, A) = \lim_{\epsilon \to 0} \sup_{\|E\| \le \epsilon
  \|A\|} \frac{\|F(A + E) - F(A)\|}{\epsilon \|F(A)\|}.$$
For $f(A)$ the map is $F = $ `pfc f` on $\mathbb{C}^{n \times n}$ with a chosen norm.

The definition is the backbone's `Conditioning.scaledRelCondNumber F A`. The source's limit is
made total as a `limsup` for $\epsilon \to 0^+$, with values in $[0, \infty]$. -/
noncomputable abbrev condRel {V : Type*} [NormedAddCommGroup V] (F : V → V) (A : V) : ℝ≥0∞ :=
  Conditioning.scaledRelCondNumber F A

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **§9.1.6** of [golub2013matrix], the condition number as "essentially a normalized Fréchet
derivative". Let $V$ be a normed space over $\mathbb{R}$ or $\mathbb{C}$, and let $F : V \to V$
have the Fréchet derivative $L$ at $A$, with $A \neq 0$ and $F(A) \neq 0$. Then
$$\operatorname{cond}_{\mathrm{rel}}(F, A) = \frac{\|L\| \, \|A\|}{\|F(A)\|}.$$

This is `Conditioning.scaledRelCondNumber_eq_of_hasFDerivAt`. The norms are the extended norms
in $[0, \infty]$. -/
theorem condRel_eq_of_hasFDerivAt {F : V → V} {L : V →L[𝕜] V} {A : V} (hF : HasFDerivAt F L A)
    (hA : A ≠ 0) (hFA : F A ≠ 0) : condRel F A = ‖L‖ₑ * ‖A‖ₑ / ‖F A‖ₑ :=
  Conditioning.scaledRelCondNumber_eq_of_hasFDerivAt hF hA hFA

end Condition

end GolubVanLoan.Chapter09
