/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.RayleighQuotientIteration
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section06

/-!
# Quarteroni, Sacco and Saleri, Section 5.7: The QR iteration with shifting techniques

This module formalizes Section 5.7 of [quarteroni2000numerical], which accelerates the QR iteration
of Section 5.4 by shifts. One step with shift $\mu$ factors $T - \mu I = QR$ and returns
$RQ + \mu I = Q^T T Q$, so every iterate is orthogonally similar to the starting matrix $A$. With a
fixed shift the iteration is the basic QR iteration on $A - \mu I$, and its subdiagonal entries tend
to zero at the rate $|(\lambda_j - \mu)/(\lambda_{j-1} - \mu)|^k$. With the Rayleigh-quotient shift
$\mu_k = t_{nn}^{(k)}$ of (5.53), the entry $t_{n,n-1}^{(k)}$ tends to zero quadratically near a
simple real eigenvalue. The double-shift step (5.55) is two single steps with a complex conjugate
pair of shifts. The proofs specialize `Numlib.Eigen.QRAlgorithm` and
`Numlib.Eigen.RayleighQuotientIteration`, and Property 5.9 and (5.37) of Section 5.5.

## Main definitions

* Equation (5.52), `QuarteroniSaccoSaleri.Chapter05.shiftedQrStep`: one QR step with shift $\mu$,
  $T' = RQ + \mu I$ where $QR = T - \mu I$.
* Equation (5.52), `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate`: the QR iteration with a fixed
  shift $\mu$, from $T^{(0)} = A$.
* Equation (5.53), `QuarteroniSaccoSaleri.Chapter05.equation_5_53`: the QR iteration with the shift
  $\mu_k = t_{nn}^{(k)}$.
* Equation (5.55), `QuarteroniSaccoSaleri.Chapter05.equation_5_55`: the double-shift step with the
  shifts $\lambda$ and $\bar\lambda$.

## Main results

* Equation (5.52), `QuarteroniSaccoSaleri.Chapter05.shiftedQrStep_eq` and
  `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate_eq`: the shifted step and iteration agree with
  the backbone definitions.
* Display after (5.52), `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate_eq_conj`: each shifted
  step, and each iterate, is an orthogonal similarity of $A$.
* Section 5.7.1, `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate_eq_qrIterate`: the iteration with
  a fixed shift $\mu$ is the basic QR iteration on $A - \mu I$, plus $\mu I$.
* Section 5.7.1, `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate_rate`: the subdiagonal entries
  tend to zero at the rate $|(\lambda_j - \mu)/(\lambda_{j-1} - \mu)|^k$.
* Equation (5.53), `QuarteroniSaccoSaleri.Chapter05.equation_5_53_eq` and
  `QuarteroniSaccoSaleri.Chapter05.equation_5_53_eq_conj`: the iteration agrees with the backbone,
  and every iterate is orthogonally similar to $A$.
* Equation (5.53), `QuarteroniSaccoSaleri.Chapter05.equation_5_53_quadratic`: near a simple real
  eigenvalue, one step squares $|t_{n,n-1}^{(k)}|$ up to a constant.
* Equation (5.53), `QuarteroniSaccoSaleri.Chapter05.equation_5_53_quadratic_iterate`: once an
  iterate is close enough, $t_{n,n-1}^{(k)} \to 0$ quadratically and $t_{nn}^{(k)} \to \lambda$.
* Equation (5.55), `QuarteroniSaccoSaleri.Chapter05.equation_5_55_eq` and
  `QuarteroniSaccoSaleri.Chapter05.equation_5_55_eq_conj`: the double-shift step agrees with the
  backbone and is a unitary similarity.

## Conventions

* The iterations are defined over a field $\mathbb{K}$ that is $\mathbb{R}$ or $\mathbb{C}$
  (`RCLike 𝕜`), on `Matrix (Fin N) (Fin N) 𝕜`. The similarity statements are over $\mathbb{R}$ with
  orthogonal matrices, and the double-shift step is over $\mathbb{C}$ with unitary matrices.
* The QR factorization at every step is `Matrix.qrQ` and `Matrix.qrR`, the Gram–Schmidt
  factorization, which is defined for every square matrix.
* As in Section 5.4, the iteration starts from $T^{(0)} = A$. The book's start
  $T^{(0)} = (Q^{(0)})^T A Q^{(0)}$ in Hessenberg form is the case $A = $
  `QuarteroniSaccoSaleri.Chapter05.hessenbergReduce A₀` of Section 5.6.

## Implementation notes

* The double-shift step is defined in complex arithmetic, as two complex single steps. The
  real-arithmetic Francis implementation is not defined, because the book only sketches it.

## Deviations from the source

* **Generalization.** The fixed-shift QR recurrence also accepts complex and non-Hessenberg input.
  See `QuarteroniSaccoSaleri.Chapter05.shiftedQrStep`,
  `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate`.
* **Generalization.** The fixed-shift similarity holds for any initial matrix and identifies the
  shifted sequence with ordinary QR. See `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate_eq_conj`,
  `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate_eq_qrIterate`.
* **Correction.** The fixed-shift rate requires strict spectral separation from neighboring shifted
  values and the QR minor condition. See `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate_rate`.
* **Generalization.** The trailing-diagonal shift defines all iterates from any nonempty square
  matrix. See `QuarteroniSaccoSaleri.Chapter05.equation_5_53`,
  `QuarteroniSaccoSaleri.Chapter05.equation_5_53_eq_conj`.
* **Scope.** The double QR step takes an arbitrary supplied shift and proves unitary similarity. See
  `QuarteroniSaccoSaleri.Chapter05.equation_5_55`,
  `QuarteroniSaccoSaleri.Chapter05.equation_5_55_eq_conj`.
* **Scope.** Trailing-diagonal quadratic convergence is local near a specified simple eigenvalue.
  See `QuarteroniSaccoSaleri.Chapter05.equation_5_53_quadratic`,
  `QuarteroniSaccoSaleri.Chapter05.equation_5_53_quadratic_iterate`.
* **Convergence with a fixed shift, Section 5.7.1** (reading). The source orders the eigenvalues by
  $|\lambda_1 - \mu| \ge \dots \ge |\lambda_n - \mu|$; the theorem assumes the strict order,
  $\lambda_n \neq \mu$, and the general-position hypothesis of Property 5.9. See
  `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate_rate`.
* **Quadratic convergence of (5.53)** (reading). The source states $|t_{n,n-1}^{(k+1)}| /
  \|T^{(0)}\|_2 = O(\eta_k^2)$ at one $k$; the theorem gives constants uniform in $k$ at a simple
  real eigenvalue, under two hypotheses that the source leaves implicit, and without the hypothesis
  "unreduced". See `QuarteroniSaccoSaleri.Chapter05.equation_5_53_quadratic`.
* **Section 5.7.2, reference to Remark 5.13** (typo). Remark 5.13 does not exist; Exercise 14 is
  meant.

## Not formalized

* **Section 5.7.2, quadratic convergence of the QR iteration with the Francis double shift.** The
  source cites the claim without proof, notes that special matrices defeat the strategy (the cyclic
  permutation matrix of Exercise 14, which
  `QuarteroniSaccoSaleri.Chapter05.property_5_9_counterexample` shows is left fixed by the
  iteration), and calls a shift strategy that converges for every matrix an open problem. So any
  correct statement needs a genericity hypothesis that none of the cited sources supplies. A proof
  would need a block form of the argument of `Numlib.Eigen.RayleighQuotientIteration`, a subspace
  Rayleigh quotient iteration: the last two columns of $Q$ for the double step are the
  orthonormalization of $(T - \lambda I)^{-T} (T - \bar\lambda I)^{-T} [e_{n-1}, e_n]$, so
  $t_{n-1,n-2}^{(k+1)}$ must be bounded by the gap (`Submodule.gap`) between
  $\operatorname{span}\{e_{n-1}, e_n\}$ and the left invariant subspace of the pair
  $\lambda, \bar\lambda$.
* **The stopping test (5.54).** It is part of a program.
* **Examples 5.10–5.13.** They are numerical.
* **Programs 36 and 37.**
-/

open Filter Finset Matrix Topology

namespace QuarteroniSaccoSaleri.Chapter05

variable {N : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### The QR method with single shift (5.52) -/

/-- **Equation (5.52)** of [quarteroni2000numerical], one step. Let $T \in \mathbb{K}^{n \times n}$
and $\mu \in \mathbb{K}$. One **step of the QR iteration with shift $\mu$** computes the QR
factorization $QR = T - \mu I$ and returns $$T' = RQ + \mu I.$$

The factors $Q$ and $R$ are `Matrix.qrQ (T - μ • 1)` and `Matrix.qrR (T - μ • 1)`.

**Generalization.** The fixed-shift recurrence is defined for real or complex scalars and arbitrary
input matrices. It returns the requested iterate without a convergence test. The source presents
real Hessenberg input.
-/
noncomputable def shiftedQrStep (μ : 𝕜) (T : Matrix (Fin N) (Fin N) 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  qrR (T - μ • 1) * qrQ (T - μ • 1) + μ • 1

/-- **Equation (5.52)** of [quarteroni2000numerical]. The **QR iteration with fixed shift $\mu$**
starts from $T^{(0)} = A$, and for $k = 1, 2, \dots$ computes
$Q^{(k)} R^{(k)} = T^{(k-1)} - \mu I$ and sets $$T^{(k)} = R^{(k)} Q^{(k)} + \mu I.$$

Each step is `QuarteroniSaccoSaleri.Chapter05.shiftedQrStep μ`.

**Generalization.** The fixed-shift recurrence is defined for real or complex scalars and arbitrary
input matrices. It returns the requested iterate without a convergence test. The source presents
real Hessenberg input.
-/
noncomputable def shiftedQrIterate (A : Matrix (Fin N) (Fin N) 𝕜) (μ : 𝕜) :
    ℕ → Matrix (Fin N) (Fin N) 𝕜
  | 0 => A
  | k + 1 => shiftedQrStep μ (shiftedQrIterate A μ k)

/-- The shifted QR step (5.52) of [quarteroni2000numerical] is the backbone step:
`QuarteroniSaccoSaleri.Chapter05.shiftedQrStep μ T` equals `Matrix.shiftedQrStep μ T` for every
$\mu$ and $T$. -/
theorem shiftedQrStep_eq (μ : 𝕜) (T : Matrix (Fin N) (Fin N) 𝕜) :
    shiftedQrStep μ T = Matrix.shiftedQrStep μ T := rfl

/-- The shifted QR iteration (5.52) of [quarteroni2000numerical] is the backbone iteration: for
every $k$, `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate A μ k` equals
`Matrix.shiftedQrIterate A μ k`. -/
theorem shiftedQrIterate_eq (A : Matrix (Fin N) (Fin N) 𝕜) (μ : 𝕜) :
    ∀ k, shiftedQrIterate A μ k = Matrix.shiftedQrIterate A μ k
  | 0 => rfl
  | k + 1 => by
    rw [shiftedQrIterate, shiftedQrIterate_eq A μ k, shiftedQrStep_eq,
      Matrix.shiftedQrIterate_succ]

/-- **Display after Equation (5.52)** of [quarteroni2000numerical]. Let
$A \in \mathbb{R}^{n \times n}$ and $\mu \in \mathbb{R}$. Then:

(i) for every $T \in \mathbb{R}^{n \times n}$, the factor $Q$ of the QR factorization of
$T - \mu I$ is orthogonal, and the shifted step is the similarity $$RQ + \mu I = Q^T T Q;$$

(ii) for every $k$, the product $\tilde Q_k = Q^{(1)} \cdots Q^{(k)}$ of the factors of the
basic QR iteration on $A - \mu I$ is orthogonal, and $$T^{(k)} = \tilde Q_k^T A \tilde Q_k.$$

The product $\tilde Q_k$ is `Matrix.qrAccum (A - μ • 1) k`. The proof specializes
`Matrix.shiftedQrStep_eq_conj` and `Matrix.shiftedQrIterate_eq_conj_qrAccum`.

**Generalization.** The starting matrix is arbitrary. Lean also identifies the entire sequence as
ordinary QR of the shifted matrix plus the shift on the identity.
-/
theorem shiftedQrIterate_eq_conj (A : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) :
    (∀ T : Matrix (Fin N) (Fin N) ℝ, qrQ (T - μ • 1) ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      shiftedQrStep μ T = (qrQ (T - μ • 1))ᵀ * T * qrQ (T - μ • 1)) ∧
      ∀ k, qrAccum (A - μ • 1) k ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
        shiftedQrIterate A μ k = (qrAccum (A - μ • 1) k)ᵀ * A * qrAccum (A - μ • 1) k := by
  refine ⟨fun T => ⟨qrQ_mem_unitaryGroup _, ?_⟩, fun k => ⟨qrAccum_mem_unitaryGroup _ k, ?_⟩⟩
  · rw [shiftedQrStep_eq, Matrix.shiftedQrStep_eq_conj, conjTranspose_eq_transpose_of_trivial]
  · rw [shiftedQrIterate_eq, Matrix.shiftedQrIterate_eq_conj_qrAccum,
      conjTranspose_eq_transpose_of_trivial]

/-- **Section 5.7.1** of [quarteroni2000numerical], a fixed shift. Let
$A \in \mathbb{R}^{n \times n}$ and $\mu \in \mathbb{R}$. For every $k$, the iterate $T^{(k)}$
of the QR iteration with fixed shift $\mu$ is $$T^{(k)} = \hat T^{(k)} + \mu I,$$ where
$\hat T^{(k)}$ is the $k$-th iterate of the basic QR iteration on $A - \mu I$.

The basic iteration is `QuarteroniSaccoSaleri.Chapter05.qrIterate` of Section 5.4. The proof
specializes `Matrix.shiftedQrIterate_eq_qrIterate_sub_add`.

**Generalization.** The starting matrix is arbitrary. Lean also identifies the entire sequence as
ordinary QR of the shifted matrix plus the shift on the identity.
-/
theorem shiftedQrIterate_eq_qrIterate (A : Matrix (Fin N) (Fin N) ℝ) (μ : ℝ) (k : ℕ) :
    shiftedQrIterate A μ k = qrIterate (A - μ • 1) k + μ • 1 := by
  rw [shiftedQrIterate_eq, qrIterate_eq, Matrix.shiftedQrIterate_eq_qrIterate_sub_add]

/-- **Section 5.7.1** of [quarteroni2000numerical], convergence with a fixed shift. Let
$A, X \in \mathbb{R}^{n \times n}$ with $X$ invertible and $X^{-1} A X =
\operatorname{diag}(\lambda_1, \dots, \lambda_n)$. Let $\mu \in \mathbb{R}$ with
$\lambda_i \neq \mu$ for all $i$ and $$|\lambda_1 - \mu| > |\lambda_2 - \mu| > \dots >
|\lambda_n - \mu|,$$ and assume that every leading principal minor of $X^{-1}$ is nonzero (the
hypothesis of Property 5.9). Let $T^{(k)}$ be the QR iteration (5.52) with fixed shift $\mu$.
Then for every subdiagonal position $(j, j - 1)$, the entry $t_{j,j-1}^{(k)}$ tends to $0$ as
$k \to \infty$, and there is a constant $C$ with $$|t_{j,j-1}^{(k)}| \le C \left|
\frac{\lambda_j - \mu}{\lambda_{j-1} - \mu} \right|^k \quad \text{for all } k.$$

**Reading.** The source orders the eigenvalues by $|\lambda_1 - \mu| \ge \dots \ge |\lambda_n -
\mu|$ and claims a rate proportional to $|(\lambda_j - \mu)/(\lambda_{j-1} - \mu)|^k$. With a
tie this ratio is $1$ and nothing tends to zero, so the theorem assumes the strict order and
$|\lambda_n - \mu| > 0$. It also assumes the general-position hypothesis of Property 5.9 for the
eigenvector matrix $X$, which the shift does not change.

Indices are 0-based: the position $(j, j - 1)$ is `(i, j)` with `(i : ℕ) = j + 1`. The proof
applies Property 5.9 and (5.37) to $A - \mu I$, whose eigenvalues are the $\lambda_i - \mu$ with
the same eigenvectors, through `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate_eq_qrIterate`.

**Correction.** The source uses non-strict ordering by distance to the shift. Lean requires strict
gaps, all shifted eigenvalues nonzero, and the leading-minor condition from the corrected basic QR
theorem. The result then bounds each first subdiagonal entry and gives its convergence to zero.
-/
theorem shiftedQrIterate_rate {A X : Matrix (Fin N) (Fin N) ℝ} (hX : IsUnit X) {lam : Fin N → ℝ}
    (hD : X⁻¹ * A * X = diagonal lam) (μ : ℝ) (hne : ∀ i, lam i - μ ≠ 0)
    (hsep : ∀ i j, i < j → |lam j - μ| < |lam i - μ|)
    (hminor : ∀ (m : ℕ) (hm : m ≤ N),
      IsUnit ((X⁻¹).submatrix (Fin.castLE hm) (Fin.castLE hm)).det)
    {i j : Fin N} (hij : (i : ℕ) = j + 1) :
    Tendsto (fun k => shiftedQrIterate A μ k i j) atTop (𝓝 0) ∧
      ∃ C : ℝ, ∀ k, |shiftedQrIterate A μ k i j| ≤ C * (|lam i - μ| / |lam j - μ|) ^ k := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hD' : X⁻¹ * (A - μ • 1) * X = diagonal fun i => lam i - μ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      nonsing_inv_mul X hdet, smul_one_eq_diagonal, diagonal_sub]
  have hji : j ≠ i := fun h => by rw [h] at hij; omega
  have hentry : ∀ k, shiftedQrIterate A μ k i j = qrIterate (A - μ • 1) k i j := fun k => by
    rw [shiftedQrIterate_eq_qrIterate, Matrix.add_apply, Matrix.smul_apply, one_apply_ne hji.symm,
      smul_zero, add_zero]
  simp only [hentry]
  exact ⟨(property_5_9 hX hD' hne hsep hminor).1 i j (Fin.lt_def.2 (by omega)),
    equation_5_37 hX hD' hne hsep hminor hij⟩

/-! ### The Rayleigh-quotient shift (5.53) -/

/-- **Equation (5.53)** of [quarteroni2000numerical]. Let $A \in \mathbb{K}^{n \times n}$ with
$n \ge 1$. The **QR iteration with single shift $\mu_k = t_{nn}^{(k)}$** starts from
$T^{(0)} = A$, and at every step takes the current last diagonal entry as the shift:
$$T^{(k+1)} = RQ + t_{nn}^{(k)} I, \qquad QR = T^{(k)} - t_{nn}^{(k)} I.$$

Here $n = N + 1$, and the last index is `Fin.last N`. Each step is
`QuarteroniSaccoSaleri.Chapter05.shiftedQrStep`.

**Generalization.** The trailing-diagonal shift is defined for any nonempty square matrix and for a
fixed step count. The recurrence also works over complex scalars; the exposed orthogonal similarity
theorem is real.
-/
noncomputable def equation_5_53 (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) :
    ℕ → Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜
  | 0 => A
  | k + 1 => shiftedQrStep (equation_5_53 A k (Fin.last N) (Fin.last N)) (equation_5_53 A k)

/-- The iteration (5.53) of [quarteroni2000numerical] is the backbone iteration: for every $k$,
`QuarteroniSaccoSaleri.Chapter05.equation_5_53 A k` equals `Matrix.rayleighShiftQrIterate A k`. -/
theorem equation_5_53_eq (A : Matrix (Fin (N + 1)) (Fin (N + 1)) 𝕜) :
    ∀ k, equation_5_53 A k = Matrix.rayleighShiftQrIterate A k
  | 0 => rfl
  | k + 1 => by
    rw [equation_5_53, equation_5_53_eq A k, shiftedQrStep_eq,
      Matrix.rayleighShiftQrIterate_succ]

/-- **Equation (5.53)** of [quarteroni2000numerical], similarity. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 1$. For every $k$ there is an orthogonal matrix $Q$
such that the iterate of (5.53) is $T^{(k)} = Q^T A Q$.

Each step is the similarity of `QuarteroniSaccoSaleri.Chapter05.shiftedQrIterate_eq_conj`. The
proof specializes `Matrix.exists_unitary_conj_rayleighShiftQrIterate`.

**Generalization.** The trailing-diagonal shift is defined for any nonempty square matrix and for a
fixed step count. The recurrence also works over complex scalars; the exposed orthogonal similarity
theorem is real.
-/
theorem equation_5_53_eq_conj (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : ℕ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin (N + 1)) ℝ, equation_5_53 A k = Qᵀ * A * Q := by
  obtain ⟨Q, hQ, h⟩ := Matrix.exists_unitary_conj_rayleighShiftQrIterate A k
  exact ⟨Q, hQ, by rw [equation_5_53_eq, h, conjTranspose_eq_transpose_of_trivial]⟩

/-! ### The QR method with double shift (5.55) -/

/-- **Equation (5.55)** of [quarteroni2000numerical]. Let $T \in \mathbb{C}^{n \times n}$ and
$\lambda \in \mathbb{C}$. The **double-shift step** takes two consecutive shifted steps (5.52),
with the shifts $\lambda$ and $\bar\lambda$: $$Q^{(k)} R^{(k)} = T^{(k-1)} - \lambda I, \quad
T^{(k)} = R^{(k)} Q^{(k)} + \lambda I,$$ $$Q^{(k+1)} R^{(k+1)} = T^{(k)} - \bar\lambda I, \quad
T^{(k+1)} = R^{(k+1)} Q^{(k+1)} + \bar\lambda I.$$ The source uses it when a $2 \times 2$
diagonal block cannot be reduced to triangular form: then the two eigenvalues of the block are a
complex conjugate pair $\lambda, \bar\lambda$.

The step is in complex arithmetic. The real-arithmetic Francis implementation is not defined,
because the book only sketches it.

**Reading.** The pair of conjugate shifted steps takes the shift as input. The book selects it from
the trailing block and interleaves double shifts with single shifts and deflation. Lean gives
unitary similarity for the isolated double step.
-/
noncomputable def equation_5_55 (T : Matrix (Fin N) (Fin N) ℂ) (lam : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  shiftedQrStep (starRingEnd ℂ lam) (shiftedQrStep lam T)

/-- The double-shift step (5.55) of [quarteroni2000numerical] is the backbone step:
`QuarteroniSaccoSaleri.Chapter05.equation_5_55 T λ` equals `Matrix.doubleShiftQrStep T λ`. -/
theorem equation_5_55_eq (T : Matrix (Fin N) (Fin N) ℂ) (lam : ℂ) :
    equation_5_55 T lam = Matrix.doubleShiftQrStep T lam := rfl

/-- **Equation (5.55)** of [quarteroni2000numerical], similarity. Let
$T \in \mathbb{C}^{n \times n}$ and $\lambda \in \mathbb{C}$. There is a unitary matrix $Q$ such
that the double-shift step gives $T' = Q^H T Q$.

The matrix $Q$ is the product of the two unitary factors of the two steps. The proof specializes
`Matrix.exists_unitary_conj_doubleShiftQrStep`.

**Reading.** The pair of conjugate shifted steps takes the shift as input. The book selects it from
the trailing block and interleaves double shifts with single shifts and deflation. Lean gives
unitary similarity for the isolated double step.
-/
theorem equation_5_55_eq_conj (T : Matrix (Fin N) (Fin N) ℂ) (lam : ℂ) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin N) ℂ, equation_5_55 T lam = Qᴴ * T * Q :=
  Matrix.exists_unitary_conj_doubleShiftQrStep T lam

/-! ### The quadratic convergence of the single-shift iteration -/

open scoped Matrix.Norms.L2Operator in
/-- **Equation (5.53)** of [quarteroni2000numerical], quadratic convergence. Let
$A \in \mathbb{R}^{n \times n}$ with $n \ge 2$ be upper Hessenberg, and let
$\lambda \in \mathbb{R}$ be a simple root of the characteristic polynomial of $A$. Let $T^{(k)}$
be the iterates of (5.53) from $T^{(0)} = A$, and assume that no shift is an eigenvalue of its
iterate: $T^{(k)} - t_{nn}^{(k)} I$ is nonsingular for every $k$. Then there are constants
$c > 0$ and $\varepsilon_0 > 0$ with $c \varepsilon_0 \le 1$ such that for every $k$: if
$$|t_{n,n-1}^{(k)}| \le \varepsilon_0 \|A\|_2 \quad \text{and} \quad |t_{nn}^{(k)} - \lambda|
\le \varepsilon_0 \|A\|_2,$$ then $$|t_{n,n-1}^{(k+1)}| \le \frac{c\,
|t_{n,n-1}^{(k)}|^2}{\|A\|_2} \quad \text{and} \quad |t_{nn}^{(k+1)} - \lambda| \le \frac{c\,
|t_{n,n-1}^{(k)}|^2}{\|A\|_2}.$$ Since $c \varepsilon_0 \le 1$, the two hypotheses then hold
again at $k + 1$.

**Reading.** The source states, without proof and with a reference to Demmel's book (cited as
Dem97, pp. 161–163), that if $|t_{n,n-1}^{(k)}| / \|T^{(0)}\|_2 = \eta_k < 1$ then
$|t_{n,n-1}^{(k+1)}| / \|T^{(0)}\|_2 = O(\eta_k^2)$. The theorem is the local statement that
this stands for, with constants uniform in $k$. (i) The source assumes only that
$|t_{n,n-1}^{(k)}|$ is small. The second hypothesis, that $t_{nn}^{(k)}$ is close to $\lambda$,
says which eigenvalue the last row converges to, and it is needed: a small $t_{n,n-1}^{(k)}$
alone puts $t_{nn}^{(k)}$ near some eigenvalue, which can be a defective one where the
convergence is only linear. This hypothesis is the closeness of $e_n$ to the left eigenvector of
$\lambda$ that the local statement about Rayleigh quotient iteration in Dem97 assumes. (ii) The
cited source assumes that $T^{(0)}$ is unreduced Hessenberg. This hypothesis is not needed. It
makes the QR factorization of the singular matrix $T - \lambda I$ unique in that discussion;
here the nonsingularity hypothesis on $T^{(k)} - t_{nn}^{(k)} I$ replaces it. In this generic
case the algorithm of the book and `Matrix.qrQ` agree.

The norm $\|A\|_2$ is the operator norm of `Matrix.Norms.L2Operator`, and $n = N + 2$. The
constants depend on the conditioning of $\lambda$, through the resolvent of $A^T - \lambda I$ on
the complement of the right eigenvector. The proof specializes
`Matrix.exists_abs_isShiftedQrStep_last_le_sq`, the local quadratic bound of one shifted step on
a Hessenberg orthogonal conjugate $T^{(k)} = Q^T A Q$
(`QuarteroniSaccoSaleri.Chapter05.equation_5_53_eq_conj`), and
`Matrix.isUpperHessenberg_rayleighShiftQrIterate` gives the Hessenberg form of every iterate.
The idea of that bound is that the last row of a shifted QR step is a step of Rayleigh quotient
iteration on $T^T$ from $e_n$. The constant is $c = (|C| + 1) \|A\|_2$ for the constant $C$ of
the backbone.

**Reading.** The quadratic bounds are local near a simple real eigenvalue, with the trailing
diagonal close to that eigenvalue and all shifted matrices invertible. The hypotheses distinguish
convergence to the selected eigenvalue from the source assertion based on a small subdiagonal alone.
-/
theorem equation_5_53_quadratic {A : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hA : A.IsUpperHessenberg) {lam : ℝ} (hlam : A.charpoly.rootMultiplicity lam = 1)
    (hreg : ∀ k, IsUnit (equation_5_53 A k -
      equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)) •
        (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ))) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ c * ε₀ ≤ 1 ∧ ∀ k,
      |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ ε₀ * ‖A‖ →
      |equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)) - lam| ≤ ε₀ * ‖A‖ →
        |equation_5_53 A (k + 1) (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤
            c * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 / ‖A‖ ∧
          |equation_5_53 A (k + 1) (Fin.last (N + 1)) (Fin.last (N + 1)) - lam| ≤
            c * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 / ‖A‖ := by
  obtain ⟨C, δ, hδ, hstep⟩ := Matrix.exists_abs_isShiftedQrStep_last_le_sq hlam
  -- the starting matrix is not zero, its shifted form being nonsingular
  have hA0 : 0 < ‖A‖ := by
    rcases (norm_nonneg A).lt_or_eq with h | h
    · exact h
    · exfalso
      have hA' : A = 0 := norm_eq_zero.mp h.symm
      have hu := hreg 0
      rw [show equation_5_53 A 0 = A from rfl, hA', Matrix.zero_apply, zero_smul, sub_zero] at hu
      exact not_isUnit_zero hu
  -- every iterate is upper Hessenberg
  have hess : ∀ k, (equation_5_53 A k).IsUpperHessenberg := fun k => by
    rw [equation_5_53_eq]
    refine Matrix.isUpperHessenberg_rayleighShiftQrIterate hA (fun j => ?_) k
    rw [← equation_5_53_eq]
    exact hreg j
  set c : ℝ := (|C| + 1) * ‖A‖ with hcdef
  have hc : 0 < c := by positivity
  refine ⟨c, min (δ / ‖A‖) (1 / c), hc, lt_min (by positivity) (by positivity),
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hc.le).trans_eq (mul_one_div_cancel hc.ne'),
    fun k ht hd => ?_⟩
  have hεA : min (δ / ‖A‖) (1 / c) * ‖A‖ ≤ δ :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hA0.le).trans_eq (div_mul_cancel₀ δ hA0.ne')
  obtain ⟨Q, hQ, hTQ⟩ := equation_5_53_eq_conj A k
  obtain ⟨h1, h2⟩ := hstep Q _ _ hQ hTQ (hess k) (hreg k) (ht.trans hεA) (hd.trans hεA)
    (Matrix.isShiftedQrStep_shiftedQrStep _ _)
  have hnext : equation_5_53 A (k + 1) =
      Matrix.shiftedQrStep (equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)))
        (equation_5_53 A k) := rfl
  have hc' : c * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 / ‖A‖ =
      (|C| + 1) * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 := by
    rw [hcdef]
    field_simp
  have hsq : C * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 ≤
      (|C| + 1) * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ^ 2 :=
    mul_le_mul_of_nonneg_right ((le_abs_self C).trans (by linarith)) (sq_nonneg _)
  rw [hnext, hc']
  exact ⟨h1.trans hsq, h2.trans hsq⟩


open scoped Matrix.Norms.L2Operator in
/-- **Equation (5.53)** of [quarteroni2000numerical], quadratic convergence of the whole tail of the
iteration. Under the hypotheses of `QuarteroniSaccoSaleri.Chapter05.equation_5_53_quadratic`
($A \in \mathbb{R}^{n \times n}$ with $n \ge 2$ upper Hessenberg, $\lambda$ a simple real
eigenvalue, no shift an eigenvalue of its iterate), there are constants $c > 0$ and
$\varepsilon_0 > 0$ with the following property. Let $k$ be such that $$|t_{n,n-1}^{(k)}| \le
\varepsilon_0 \|A\|_2 \quad \text{and} \quad |t_{nn}^{(k)} - \lambda| \le \varepsilon_0
\|A\|_2,$$ and let $\eta_m = c\, |t_{n,n-1}^{(m)}| / \|A\|_2$. Then $\eta_k \le 1/2$,
$$\eta_{k+j} \le \eta_k^{2^j} \quad \text{for all } j,$$ and $t_{n,n-1}^{(k+j)} \to 0$ and
$t_{nn}^{(k+j)} \to \lambda$ as $j \to \infty$.

**Reading.** The source says that "the convergence to zero of the sequence $\{t_{n,n-1}^{(k)}\}$
is quadratic". The theorem states this in the sense above, for the tail of the iteration after
the first iterate in the basin.

The proof is an induction on $j$ from the one-step bound of
`QuarteroniSaccoSaleri.Chapter05.equation_5_53_quadratic`, whose hypotheses propagate because
$c \varepsilon_0 \le 1$.

**Reading.** The quadratic bounds are local near a simple real eigenvalue, with the trailing
diagonal close to that eigenvalue and all shifted matrices invertible. The hypotheses distinguish
convergence to the selected eigenvalue from the source assertion based on a small subdiagonal alone.
-/
theorem equation_5_53_quadratic_iterate {A : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ}
    (hA : A.IsUpperHessenberg) {lam : ℝ} (hlam : A.charpoly.rootMultiplicity lam = 1)
    (hreg : ∀ k, IsUnit (equation_5_53 A k -
      equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)) •
        (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ))) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ∀ k,
      |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| ≤ ε₀ * ‖A‖ →
      |equation_5_53 A k (Fin.last (N + 1)) (Fin.last (N + 1)) - lam| ≤ ε₀ * ‖A‖ →
        c * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| / ‖A‖ ≤ 1 / 2 ∧
        (∀ j, c * |equation_5_53 A (k + j) (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| / ‖A‖ ≤
          (c * |equation_5_53 A k (Fin.last (N + 1)) (Fin.castSucc (Fin.last N))| / ‖A‖) ^
            (2 ^ j)) ∧
        Tendsto (fun j => equation_5_53 A (k + j) (Fin.last (N + 1)) (Fin.castSucc (Fin.last N)))
          atTop (𝓝 0) ∧
        Tendsto (fun j => equation_5_53 A (k + j) (Fin.last (N + 1)) (Fin.last (N + 1)))
          atTop (𝓝 lam) := by
  obtain ⟨c, ε₀, hc, hε₀, hcε, hstep⟩ := equation_5_53_quadratic hA hlam hreg
  have hA0 : 0 < ‖A‖ := by
    rcases (norm_nonneg A).lt_or_eq with h | h
    · exact h
    · exfalso
      have hA' : A = 0 := norm_eq_zero.mp h.symm
      have hu := hreg 0
      rw [show equation_5_53 A 0 = A from rfl, hA', Matrix.zero_apply, zero_smul, sub_zero] at hu
      exact not_isUnit_zero hu
  refine ⟨c, ε₀ / 2, hc, by positivity, fun k ht hd => ?_⟩
  set n : Fin (N + 2) := Fin.last (N + 1) with hn
  set m : Fin (N + 2) := Fin.castSucc (Fin.last N) with hm
  set η : ℕ → ℝ := fun i => c * |equation_5_53 A i n m| / ‖A‖ with hη
  have hη0 : ∀ i, 0 ≤ η i := fun i => by positivity
  -- the basin, and the one-step bound in normalized form
  have hbasin : ∀ i, |equation_5_53 A i n m| ≤ ε₀ * ‖A‖ →
      |equation_5_53 A i n n - lam| ≤ ε₀ * ‖A‖ →
      η (i + 1) ≤ η i ^ 2 ∧ |equation_5_53 A (i + 1) n m| ≤ ε₀ * ‖A‖ ∧
        |equation_5_53 A (i + 1) n n - lam| ≤ ε₀ * ‖A‖ := by
    intro i hti hdi
    obtain ⟨h1, h2⟩ := hstep i hti hdi
    have hsq : c * |equation_5_53 A i n m| ^ 2 / ‖A‖ ≤ ε₀ * ‖A‖ := by
      calc c * |equation_5_53 A i n m| ^ 2 / ‖A‖
          ≤ c * (ε₀ * ‖A‖) ^ 2 / ‖A‖ := by gcongr
        _ = (c * ε₀) * (ε₀ * ‖A‖) := by field_simp
        _ ≤ 1 * (ε₀ * ‖A‖) := by gcongr
        _ = ε₀ * ‖A‖ := one_mul _
    refine ⟨?_, h1.trans hsq, h2.trans hsq⟩
    calc η (i + 1) = c * |equation_5_53 A (i + 1) n m| / ‖A‖ := rfl
      _ ≤ c * (c * |equation_5_53 A i n m| ^ 2 / ‖A‖) / ‖A‖ := by gcongr
      _ = η i ^ 2 := by simp only [hη]; field_simp
  -- the tail stays in the basin and the normalized entries square
  have hht : ∀ j, |equation_5_53 A (k + j) n m| ≤ ε₀ * ‖A‖ ∧
      |equation_5_53 A (k + j) n n - lam| ≤ ε₀ * ‖A‖ ∧ η (k + j) ≤ η k ^ (2 ^ j) := by
    intro j
    induction j with
    | zero =>
      refine ⟨?_, ?_, by simp⟩
      · exact ht.trans (by nlinarith [hA0.le])
      · exact hd.trans (by nlinarith [hA0.le])
    | succ j ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨h4, h5, h6⟩ := hbasin (k + j) h1 h2
      refine ⟨h5, h6, ?_⟩
      calc η (k + (j + 1)) = η (k + j + 1) := rfl
        _ ≤ η (k + j) ^ 2 := h4
        _ ≤ (η k ^ (2 ^ j)) ^ 2 := by gcongr
        _ = η k ^ (2 ^ (j + 1)) := by rw [← pow_mul, pow_succ]
  have hηk : η k ≤ 1 / 2 := by
    calc η k = c * |equation_5_53 A k n m| / ‖A‖ := rfl
      _ ≤ c * (ε₀ / 2 * ‖A‖) / ‖A‖ := by gcongr
      _ = (c * ε₀) / 2 := by field_simp
      _ ≤ 1 / 2 := by linarith
  refine ⟨hηk, fun j => (hht j).2.2, ?_, ?_⟩
  -- the subdiagonal entry tends to zero
  · have hlim : Tendsto (fun j : ℕ => η k ^ (2 ^ j)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (hη0 k) (by linarith)).comp
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have hlim' : Tendsto (fun j : ℕ => ‖A‖ / c * η k ^ (2 ^ j)) atTop (𝓝 0) := by
      simpa using hlim.const_mul (‖A‖ / c)
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun j => abs_nonneg _) (fun j => ?_) hlim'
    calc |equation_5_53 A (k + j) n m| = ‖A‖ / c * η (k + j) := by
          simp only [hη]
          field_simp
      _ ≤ ‖A‖ / c * η k ^ (2 ^ j) :=
          mul_le_mul_of_nonneg_left (hht j).2.2 (by positivity)
  -- the diagonal entry tends to the eigenvalue
  · have hlim : Tendsto (fun j : ℕ => η k ^ (2 ^ j)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (hη0 k) (by linarith)).comp
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have hlim' : Tendsto (fun j : ℕ => ‖A‖ / c * (η k ^ (2 ^ j)) ^ 2) atTop (𝓝 0) := by
      have := (hlim.pow 2).const_mul (‖A‖ / c)
      simpa using this
    rw [← tendsto_sub_nhds_zero_iff, ← tendsto_add_atTop_iff_nat 1,
      tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun j => abs_nonneg _) (fun j => ?_) hlim'
    obtain ⟨h1, h2, h3⟩ := hht j
    have h := (hstep (k + j) h1 h2).2
    calc |equation_5_53 A (k + (j + 1)) n n - lam|
        = |equation_5_53 A (k + j + 1) n n - lam| := rfl
      _ ≤ c * |equation_5_53 A (k + j) n m| ^ 2 / ‖A‖ := h
      _ = ‖A‖ / c * η (k + j) ^ 2 := by
          simp only [hη]
          field_simp
      _ ≤ ‖A‖ / c * (η k ^ (2 ^ j)) ^ 2 := by
          have := (hht j).2.2
          gcongr

end QuarteroniSaccoSaleri.Chapter05
