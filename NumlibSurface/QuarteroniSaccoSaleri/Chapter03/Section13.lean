/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section12

/-!
# Quarteroni, Sacco and Saleri, Section 3.13: Undetermined systems

This module formalizes Section 3.13 of [quarteroni2000numerical], on linear systems $Ax = b$ with a
rectangular matrix $A \in \mathbb{R}^{m \times n}$. For $m \ge n$ a vector $x^*$ is a solution in
the least-squares sense (3.73) if it minimizes $\Phi(x) = \|Ax - b\|_2^2$. The least-squares
solutions are the solutions of the normal equations $A^T A x = A^T b$ (3.74). If $A$ has full rank,
the least-squares solution is unique, and it can be computed by the Cholesky factorization of
$A^T A$ or by the QR factorization of $A$ (Theorem 3.8). In general the problem (3.76) asks for the
least-squares solution of minimal Euclidean norm, and Theorem 3.9 shows that this solution is
$x^* = A^+ b$, with the pseudoinverse $A^+$. Example 3.11 shows that $x^*$ does not depend
continuously on $A$ when $A$ is rank deficient. For $m < n$ and $A$ of full rank, the solution of
minimal norm is $A^T (A A^T)^{-1} b$, and it can be computed from a QR factorization of $A^T$.

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Matrix.LeastSquares` (least-squares
solutions, the normal equations, the QR method and the solution of least norm) and
`Numlib.LinearAlgebra.Matrix.SVD` (the pseudoinverse `Matrix.pinv`).

## Main definitions

* Equation (3.73), `QuarteroniSaccoSaleri.Chapter03.equation_3_73`: $x^*$ is a least-squares
  solution of $Ax = b$.
* Equation (3.76), `QuarteroniSaccoSaleri.Chapter03.equation_3_76`: $x^*$ is a least-squares
  solution of minimal Euclidean norm.

## Main results

* Equation (3.73), `QuarteroniSaccoSaleri.Chapter03.equation_3_73_iff`: the definition agrees with
  the backbone `Matrix.IsLeastSquaresSolution`.
* Equation (3.74), `QuarteroniSaccoSaleri.Chapter03.equation_3_74`: $x^*$ is a least-squares
  solution if and only if $A^T A x^* = A^T b$.
* Section 3.13, `QuarteroniSaccoSaleri.Chapter03.normalMatrix_posDef`: for $A$ of full rank, $A^T A$
  is positive definite and the least-squares solution exists and is unique.
* Section 3.13, `QuarteroniSaccoSaleri.Chapter03.normalEquations_cholesky`: for $A$ of full rank,
  the least-squares solution is found from the Cholesky factorization $A^T A = H^T H$ by two
  triangular solves.
* Theorem 3.8, `QuarteroniSaccoSaleri.Chapter03.theorem_3_8`: for $A$ of full rank with QR
  factorization, the unique least-squares solution is $x^* = \tilde R^{-1} \tilde Q^T b$.
* Theorem 3.8, `QuarteroniSaccoSaleri.Chapter03.theorem_3_8_min`: the identities of the proof, and
  the minimum $\Phi(x^*) = \sum_{i=n+1}^{m} (Q^T b)_i^2$.
* Equation (3.76), `QuarteroniSaccoSaleri.Chapter03.equation_3_76_iff`: the definition agrees with
  the backbone `Matrix.IsMinNormLeastSquaresSolution`.
* Section 3.13, `QuarteroniSaccoSaleri.Chapter03.equation_3_76_of_linearIndependent`: for $A$ of
  full rank, (3.76) is equivalent to (3.73).
* Theorem 3.9, `QuarteroniSaccoSaleri.Chapter03.theorem_3_9`: $A^+ b$ solves (3.76).
* Theorem 3.9, `QuarteroniSaccoSaleri.Chapter03.theorem_3_9_unique`: every solution of (3.76) is
  $A^+ b$.
* Example 3.11, `QuarteroniSaccoSaleri.Chapter03.example_3_11`: a matrix of rank $1$, its
  pseudoinverse, and the solution of (3.76).
* Example 3.11, `QuarteroniSaccoSaleri.Chapter03.example_3_11_perturbed`: after a perturbation of
  size $\varepsilon$, the least-squares solution is $(1, 2/\varepsilon)^T$.
* Section 3.13, `QuarteroniSaccoSaleri.Chapter03.underdetermined_minNorm`: for $A$ with independent
  rows, $A^+ = A^T (A A^T)^{-1}$, and $A^T (A A^T)^{-1} b$ is the solution of $Ax = b$ of minimal
  norm.
* Section 3.13, `QuarteroniSaccoSaleri.Chapter03.underdetermined_qr`: for $A$ with independent rows
  and a QR factorization $A^T = QR$, the solution of minimal norm is $\tilde Q \tilde R^{-T} b$.

## Conventions

* A matrix $A \in \mathbb{R}^{m \times n}$ is `Matrix (Fin m) (Fin n) ℝ`, and vectors are
  `Fin m → ℝ` and `Fin n → ℝ`. The Euclidean norm of Section 3.1 is `‖WithLp.toLp 2 x‖`, and the
  functional of (3.73) is $\Phi(x) = \|Ax - b\|_2^2$.
* "$A$ has full rank" for $m \ge n$ is `LinearIndependent ℝ Aᵀ` (independent columns), and for
  $m < n$ it is `LinearIndependent ℝ A` (independent rows), as in Section 3.4.3.
* The QR factorization and its reduced factors $\tilde Q$ = `Matrix.firstColumns Q h` and
  $\tilde R$ = `Matrix.firstRows R h` are those of Section 3.4.3
  (`QuarteroniSaccoSaleri.Chapter03.property_3_3`).
* Indices are $0$-based: the book's sums $\sum_{i=n+1}^{m}$ are over the indices $n \le i < m$.

## Implementation notes

* The backbone states the least-squares problems on `EuclideanSpace ℝ (Fin m)` through
  `Matrix.toEuclideanLin`. The definitions `QuarteroniSaccoSaleri.Chapter03.equation_3_73` and
  `QuarteroniSaccoSaleri.Chapter03.equation_3_76` state the book's problems on plain vectors, and
  the theorems `QuarteroniSaccoSaleri.Chapter03.equation_3_73_iff` and
  `QuarteroniSaccoSaleri.Chapter03.equation_3_76_iff` connect the two forms.
* The pseudoinverse $A^+$ of Definition 1.15 is `Matrix.pinv A`, the unique matrix that satisfies
  the Penrose conditions (`Matrix.pinv_unique`). Its expression $V \Sigma^+ U^T$ through a singular
  value decomposition is in Chapter 1. The hypothesis "with SVD $A = U \Sigma V^T$" of Theorem 3.9
  is omitted, because every matrix has a singular value decomposition.

## Deviations from the source

* **Equation (3.73)** (reading). The book writes $\Phi(x^*) \le \min_x \Phi(x)$. The definition
  states $\Phi(x^*) \le \Phi(x)$ for all $x$ and allows all matrix shapes.
  See `QuarteroniSaccoSaleri.Chapter03.equation_3_73`.
* **Equation (3.74)** (scope). The normal equations characterize the minimizers in both
  directions for all matrix shapes. The text derives them as a necessary condition in its
  setup with $m \ge n$.
* **Theorem 3.8** (scope). The residual decomposition and minimum objective value also hold
  for a rank-deficient matrix. Only the solution formula requires full column rank.
* **Theorem 3.9** (reading). The source starts with an SVD. The least-squares statements work
  directly with the pseudoinverse, which is defined for every finite real matrix.
* **Example 3.11** (reading). The book says that $\operatorname{rank}(A) = 1$ and that the perturbed
  matrix has full rank $2$. The statements give the rank together with the dependence or the
  independence of the columns. See `QuarteroniSaccoSaleri.Chapter03.example_3_11` and
  `QuarteroniSaccoSaleri.Chapter03.example_3_11_perturbed`.
* **Underdetermined systems** (scope). The minimum-norm formula and transposed QR solve stated
  here include the square, full-rank case.

## Not formalized

* **The example of $\mathrm{fl}(A^T A)$**, a floating-point computation. It states no theorem.
* **Remark 3.8**, flop counts. It states no theorem.
* **Example 3.12**, a numerical run on the Hilbert matrix $H_{15}$. It states no theorem.
-/

open Finset Matrix WithLp

namespace QuarteroniSaccoSaleri.Chapter03

variable {m n : ℕ}

/-! ### Equations (3.73) and (3.74): Least-squares solutions and the normal equations -/

/-- **Equation (3.73)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{m \times n}$ and
$b \in \mathbb{R}^m$. A vector $x^* \in \mathbb{R}^n$ is a **solution of $Ax = b$ in the
least-squares sense** if
$$\Phi(x^*) \le \Phi(x) \quad \text{for all } x \in \mathbb{R}^n, \qquad \Phi(x) = \|Ax -
  b\|_2^2.$$

**Reading.** The book writes $\Phi(x^*) \le \min_{x \in \mathbb{R}^n} \Phi(x)$, for $m \ge n$.
The definition states the inequality for every $x$, and it does not assume $m \ge n$.

The definition is the backbone `Matrix.IsLeastSquaresSolution` on plain vectors; see
`QuarteroniSaccoSaleri.Chapter03.equation_3_73_iff`. -/
def equation_3_73 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (xs : Fin n → ℝ) : Prop :=
  ∀ x, ‖toLp 2 (A *ᵥ xs - b)‖ ^ 2 ≤ ‖toLp 2 (A *ᵥ x - b)‖ ^ 2

/-- **Equation (3.73)** of [quarteroni2000numerical], the backbone form. For
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and $x^* \in \mathbb{R}^n$, the vector
$x^*$ is a least-squares solution of $Ax = b$ if and only if
`Matrix.IsLeastSquaresSolution A b x*` holds for the vectors viewed in `EuclideanSpace ℝ`.

**Generalization.** Equivalent backbone predicate on the generalized shape domain.
-/
theorem equation_3_73_iff (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (xs : Fin n → ℝ) :
    equation_3_73 A b xs ↔ IsLeastSquaresSolution A (toLp 2 b) (toLp 2 xs) := by
  simp only [equation_3_73, IsLeastSquaresSolution, toEuclideanLin_toLp, ← toLp_sub,
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  exact ⟨fun h y => h (ofLp y), fun h x => h (toLp 2 x)⟩

/-- **Equation (3.74)** of [quarteroni2000numerical] (the normal equations). Let
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and $x^* \in \mathbb{R}^n$. Then $x^*$ is
a least-squares solution of $Ax = b$ if and only if it solves the square system
$$A^T A\, x^* = A^T b.$$

The book derives (3.74) from the condition $\nabla \Phi(x^*) = 0$. The proof specializes
`Matrix.isLeastSquaresSolution_iff_normalEquations`, which uses the projection theorem.

**Reading.** Gives necessity and sufficiency for all shapes.
-/
theorem equation_3_74 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (xs : Fin n → ℝ) :
    equation_3_73 A b xs ↔ (Aᵀ * A) *ᵥ xs = Aᵀ *ᵥ b := by
  rw [equation_3_73_iff, isLeastSquaresSolution_iff_normalEquations,
    conjTranspose_eq_transpose_of_trivial, toEuclideanLin_toLp, toEuclideanLin_toLp,
    (toLp_injective 2).eq_iff]

/-- **Section 3.13** of [quarteroni2000numerical], the text after (3.74). Let
$A \in \mathbb{R}^{m \times n}$ have full rank, that is, linearly independent columns. Then
$B = A^T A$ is symmetric positive definite, the system of normal equations is nonsingular, and
for every $b \in \mathbb{R}^m$ the least-squares solution of $Ax = b$ exists and is unique.

The proof specializes `Matrix.posDef_conjTranspose_mul_self_of_linearIndependent` and
`Matrix.existsUnique_isLeastSquaresSolution`. -/
theorem normalMatrix_posDef {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ) :
    (Aᵀ * A).PosDef ∧ IsUnit (Aᵀ * A) ∧ ∀ b : Fin m → ℝ, ∃! xs, equation_3_73 A b xs := by
  have hpd : (Aᵀ * A).PosDef := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact posDef_conjTranspose_mul_self_of_linearIndependent hA
  refine ⟨hpd, hpd.isUnit, fun b => ?_⟩
  obtain ⟨x, hx, huniq⟩ := existsUnique_isLeastSquaresSolution hA (toLp 2 b)
  refine ⟨ofLp x, ?_, fun y hy => ?_⟩
  · change equation_3_73 A b (ofLp x)
    rw [equation_3_73_iff, toLp_ofLp]
    exact hx
  · have := huniq (toLp 2 y) ((equation_3_73_iff A b y).1 hy)
    rw [← this, ofLp_toLp]

/-- **Section 3.13** of [quarteroni2000numerical], the Cholesky method for the normal equations. Let
$A \in \mathbb{R}^{m \times n}$ have linearly independent columns, and let $b \in \mathbb{R}^m$.
Then there is an upper triangular $H \in \mathbb{R}^{n \times n}$ with positive diagonal entries
such that $A^T A = H^T H$ (the Cholesky factorization of Theorem 3.6) and such that, for every
$x^* \in \mathbb{R}^n$, $x^*$ is a least-squares solution of $Ax = b$ if and only if there is a
$y \in \mathbb{R}^n$ with
$$H^T y = A^T b, \qquad H x^* = y.$$
So the least-squares solution is found by two triangular solves. -/
theorem normalEquations_cholesky {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ Aᵀ)
    (b : Fin m → ℝ) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ, (H.IsUpperTriangular ∧ (∀ i, 0 < H i i) ∧ Hᵀ * H = Aᵀ * A) ∧
      ∀ xs, equation_3_73 A b xs ↔ ∃ y, Hᵀ *ᵥ y = Aᵀ *ᵥ b ∧ H *ᵥ xs = y := by
  obtain ⟨H, hH, -⟩ := theorem_3_6 (normalMatrix_posDef hA).1
  refine ⟨H, hH, fun xs => ?_⟩
  rw [equation_3_74, ← hH.2.2, ← mulVec_mulVec]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, hxs⟩ => hxs ▸ hy⟩

/-! ### Theorem 3.8: The QR method -/

section QR

variable {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
variable {R : Matrix (Fin m) (Fin n) ℝ}

/-- **Theorem 3.8** of [quarteroni2000numerical], equation (3.75). Let
$A \in \mathbb{R}^{m \times n}$ with $n \le m$ have full rank, let $A = QR$ be a QR
factorization, and let $\tilde R \in \mathbb{R}^{n \times n}$ and
$\tilde Q \in \mathbb{R}^{m \times n}$ be the reduced factors of (3.48). Then for every
$b \in \mathbb{R}^m$ the vector
$$x^* = \tilde R^{-1} \tilde Q^T b$$
is a least-squares solution of $Ax = b$, and it is the only one.

The QR factorization is `Matrix.IsQR A Q R`. The proof specializes
`Matrix.IsQR.isLeastSquaresSolution`, and the uniqueness follows from
`QuarteroniSaccoSaleri.Chapter03.normalMatrix_posDef`. -/
theorem theorem_3_8 (hA : LinearIndependent ℝ Aᵀ) (h : IsQR A Q R) (hnm : n ≤ m)
    (b : Fin m → ℝ) :
    equation_3_73 A b ((firstRows R hnm)⁻¹ *ᵥ ((firstColumns Q hnm)ᵀ *ᵥ b)) ∧
      ∀ xs, equation_3_73 A b xs → xs = (firstRows R hnm)⁻¹ *ᵥ ((firstColumns Q hnm)ᵀ *ᵥ b) := by
  have h1 : equation_3_73 A b ((firstRows R hnm)⁻¹ *ᵥ ((firstColumns Q hnm)ᵀ *ᵥ b)) := by
    rw [equation_3_73_iff, mulVec_mulVec, ← conjTranspose_eq_transpose_of_trivial,
      ← toEuclideanLin_toLp]
    exact h.isLeastSquaresSolution hnm hA (toLp 2 b)
  obtain ⟨x, -, huniq⟩ := (normalMatrix_posDef hA).2.2 b
  exact ⟨h1, fun xs hxs => (huniq xs hxs).trans (huniq _ h1).symm⟩

/-- **Theorem 3.8** of [quarteroni2000numerical], the minimum and the identities of the proof. Let
$A \in \mathbb{R}^{m \times n}$ with $n \le m$, let $A = QR$ be a QR factorization with reduced
factors $\tilde R$ and $\tilde Q$, and let $b \in \mathbb{R}^m$. Then:

* $\|Ax - b\|_2 = \|Rx - Q^T b\|_2$ for every $x$, because $Q$ preserves the Euclidean norm;
* since $R$ is upper trapezoidal, for every $x$
$$\|Ax - b\|_2^2 = \|\tilde R x - \tilde Q^T b\|_2^2 + \sum_{i=n+1}^{m} \big((Q^T b)_i\big)^2;$$
* if $A$ has full rank, every least-squares solution $x^*$ satisfies $\Phi(x^*) =
  \sum_{i=n+1}^{m} \big((Q^T b)_i\big)^2$.

The sums are over the $0$-based indices $n \le i < m$. The proof specializes
`Matrix.IsQR.norm_sub_eq`, `Matrix.norm_sub_sq_eq_of_isQR` and
`Matrix.norm_sub_sq_eq_of_isQR_of_isLeastSquaresSolution`.

**Reading.** The residual decomposition and attained minimum value hold without the full-rank
assumption.
-/
theorem theorem_3_8_min (h : IsQR A Q R) (hnm : n ≤ m) (b : Fin m → ℝ) :
    (∀ x, ‖toLp 2 (A *ᵥ x - b)‖ = ‖toLp 2 (R *ᵥ x - Qᵀ *ᵥ b)‖) ∧
      (∀ x, ‖toLp 2 (A *ᵥ x - b)‖ ^ 2 =
        ‖toLp 2 (firstRows R hnm *ᵥ x - (firstColumns Q hnm)ᵀ *ᵥ b)‖ ^ 2 +
          ∑ i ∈ univ.filter (fun i : Fin m => n ≤ i), ((Qᵀ *ᵥ b) i) ^ 2) ∧
      (LinearIndependent ℝ Aᵀ → ∀ xs, equation_3_73 A b xs →
        ‖toLp 2 (A *ᵥ xs - b)‖ ^ 2 =
          ∑ i ∈ univ.filter (fun i : Fin m => n ≤ i), ((Qᵀ *ᵥ b) i) ^ 2) := by
  refine ⟨fun x => ?_, fun x => ?_, fun hA xs hxs => ?_⟩
  · have := h.norm_sub_eq (toLp 2 b) (toLp 2 x)
    rwa [conjTranspose_eq_transpose_of_trivial, toEuclideanLin_toLp, toEuclideanLin_toLp,
      ← toLp_sub, ← toLp_sub] at this
  · have := norm_sub_sq_eq_of_isQR h hnm (toLp 2 b) (toLp 2 x)
    simpa only [toEuclideanLin_toLp, ← toLp_sub, conjTranspose_eq_transpose_of_trivial,
      ofLp_toLp, Real.norm_eq_abs, sq_abs] using this
  · have := norm_sub_sq_eq_of_isQR_of_isLeastSquaresSolution h hnm hA
      ((equation_3_73_iff A b xs).1 hxs)
    simpa only [toEuclideanLin_toLp, ← toLp_sub, conjTranspose_eq_transpose_of_trivial,
      ofLp_toLp, Real.norm_eq_abs, sq_abs] using this

end QR

/-! ### Equations (3.76) and (3.77): The solution of least norm and the pseudoinverse -/

/-- **Equation (3.76)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{m \times n}$ and
$b \in \mathbb{R}^m$. A vector $x^* \in \mathbb{R}^n$ is a **least-squares solution of minimal
Euclidean norm** if $x^*$ is a least-squares solution of $Ax = b$ in the sense of (3.73), and
$\|x^*\|_2 \le \|x\|_2$ for every least-squares solution $x$.

When $A$ does not have full rank, the least-squares solution is not unique: if $x^*$ is one and
$z \in \ker A$, then $x^* + z$ is one too. This is the reason for the problem (3.76). The
definition is the backbone `Matrix.IsMinNormLeastSquaresSolution` on plain vectors; see
`QuarteroniSaccoSaleri.Chapter03.equation_3_76_iff`. -/
def equation_3_76 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (xs : Fin n → ℝ) : Prop :=
  equation_3_73 A b xs ∧ ∀ x, equation_3_73 A b x → ‖toLp 2 xs‖ ≤ ‖toLp 2 x‖

/-- **Equation (3.76)** of [quarteroni2000numerical], the backbone form. For
$A \in \mathbb{R}^{m \times n}$, $b \in \mathbb{R}^m$ and $x^* \in \mathbb{R}^n$, the vector
$x^*$ solves (3.76) if and only if `Matrix.IsMinNormLeastSquaresSolution A b x*` holds for the
vectors viewed in `EuclideanSpace ℝ`. -/
theorem equation_3_76_iff (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (xs : Fin n → ℝ) :
    equation_3_76 A b xs ↔ IsMinNormLeastSquaresSolution A (toLp 2 b) (toLp 2 xs) := by
  simp only [equation_3_76, IsMinNormLeastSquaresSolution, equation_3_73_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun y hy => h2 (ofLp y) hy⟩,
    fun ⟨h1, h2⟩ => ⟨h1, fun x hx => h2 (toLp 2 x) hx⟩⟩

/-- **Section 3.13** of [quarteroni2000numerical]: "(3.76) is consistent with (3.73) if $A$ has full
rank". Let $A \in \mathbb{R}^{m \times n}$ have linearly independent columns, and let
$b \in \mathbb{R}^m$ and $x^* \in \mathbb{R}^n$. Then $x^*$ solves (3.76) if and only if it
solves (3.73). The reason is that the least-squares solution is unique. -/
theorem equation_3_76_of_linearIndependent {A : Matrix (Fin m) (Fin n) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (b : Fin m → ℝ) (xs : Fin n → ℝ) :
    equation_3_76 A b xs ↔ equation_3_73 A b xs := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun x hx => ?_⟩⟩
  obtain ⟨y, -, huniq⟩ := (normalMatrix_posDef hA).2.2 b
  rw [(huniq xs h).trans (huniq x hx).symm]

/-- **Theorem 3.9** of [quarteroni2000numerical], equation (3.77). Let
$A \in \mathbb{R}^{m \times n}$ and $b \in \mathbb{R}^m$, and let $A^+$ be the pseudoinverse of
$A$ (Definition 1.15). Then
$$x^* = A^+ b$$
is a least-squares solution of $Ax = b$ of minimal Euclidean norm, that is, a solution of
(3.76).

The book assumes a singular value decomposition $A = U \Sigma V^T$. This is no hypothesis,
because every matrix has one. The pseudoinverse is `Matrix.pinv`. The proof specializes
`Matrix.isMinNormLeastSquaresSolution_pinv`. The solution is unique by
`QuarteroniSaccoSaleri.Chapter03.theorem_3_9_unique`.

**Reading.** Uses the pseudoinverse without a supplied SVD.
-/
theorem theorem_3_9 (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    equation_3_76 A b (A.pinv *ᵥ b) := by
  rw [equation_3_76_iff, ← toEuclideanLin_toLp]
  exact isMinNormLeastSquaresSolution_pinv A (toLp 2 b)

/-- **Theorem 3.9** of [quarteroni2000numerical], uniqueness. Let $A \in \mathbb{R}^{m \times n}$,
$b \in \mathbb{R}^m$, and let $x^* \in \mathbb{R}^n$ solve (3.76). Then $x^* = A^+ b$.

The proof specializes `Matrix.IsMinNormLeastSquaresSolution.eq_pinv`.

**Reading.** Splits out uniqueness without a supplied SVD.
-/
theorem theorem_3_9_unique {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {xs : Fin n → ℝ}
    (h : equation_3_76 A b xs) : xs = A.pinv *ᵥ b := by
  have := ((equation_3_76_iff A b xs).1 h).eq_pinv
  rwa [toEuclideanLin_toLp, (toLp_injective 2).eq_iff] at this

/-! ### Example 3.11 -/

/-- **Example 3.11** of [quarteroni2000numerical], the rank-deficient system. Let
$$A = \begin{bmatrix} 1 & 0 \\ 0 & 0 \\ 0 & 0 \end{bmatrix}, \qquad b = \begin{bmatrix} 1 \\ 2
  \\ 3 \end{bmatrix}.$$
Then $\operatorname{rank}(A) = 1$, the columns of $A$ are linearly dependent, the pseudoinverse
is
$$A^+ = \begin{bmatrix} 1 & 0 & 0 \\ 0 & 0 & 0 \end{bmatrix},$$
and $x^* = A^+ b = (1, 0)^T$ is the solution of (3.76).

**Reading.** The book says that $\operatorname{rank}(A) = 1$. The statement gives the rank
together with the dependence of the columns, so that $A$ does not have full rank in the sense of
this module.

The pseudoinverse is checked with the Penrose conditions (`Matrix.pinv_unique`). -/
theorem example_3_11 :
    let A : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 0]
    let b : Fin 3 → ℝ := ![1, 2, 3]
    A.rank = 1 ∧ ¬ LinearIndependent ℝ Aᵀ ∧ A.pinv = !![1, 0, 0; 0, 0, 0] ∧
      A.pinv *ᵥ b = ![1, 0] ∧ equation_3_76 A b ![1, 0] := by
  intro A b
  have hpinv : A.pinv = !![1, 0, 0; 0, 0, 0] := by
    symm
    refine pinv_unique A ?_ ?_ ?_ ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_succ]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_succ]
  have hsol : A.pinv *ᵥ b = ![1, 0] := by
    rw [hpinv]
    ext i; fin_cases i <;> simp [b, mulVec, dotProduct, Fin.sum_univ_succ]
  have hdep : ¬ LinearIndependent ℝ Aᵀ := fun h =>
    h.ne_zero 1 (by ext i; fin_cases i <;> simp [A])
  have hrank : A.rank = 1 := by
    have hle : A.rank ≤ 1 := by
      have : A = vecMulVec ![1, 0, 0] ![1, 0] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [A, vecMulVec_apply]
      rw [this]
      exact rank_vecMulVec_le _ _
    refine le_antisymm hle (Nat.one_le_iff_ne_zero.2 fun h0 => ?_)
    rw [rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
    have := congrFun (congrArg (fun f => f ![1, 0]) h0) 0
    simp [A, mulVec, dotProduct, Fin.sum_univ_succ] at this
  exact ⟨hrank, hdep, hpinv, hsol, hsol ▸ theorem_3_9 A b⟩

/-- **Example 3.11** of [quarteroni2000numerical], the perturbed system. Let $\varepsilon \neq 0$,
and replace the zero entry $a_{22}$ of the matrix of
`QuarteroniSaccoSaleri.Chapter03.example_3_11` by $\varepsilon$:
$$A_\varepsilon = \begin{bmatrix} 1 & 0 \\ 0 & \varepsilon \\ 0 & 0 \end{bmatrix}, \qquad b =
  \begin{bmatrix} 1 \\ 2 \\ 3 \end{bmatrix}.$$
Then $\operatorname{rank}(A_\varepsilon) = 2$, the columns of $A_\varepsilon$ are linearly
independent, and a vector $x^*$ is a least-squares solution of $A_\varepsilon x = b$ if and only
if $x^* = (1, 2/\varepsilon)^T$. For the book's value $\varepsilon = 10^{-12}$ this solution is
$(1, 2 \cdot 10^{12})^T$. So the solution of (3.76) is not a continuous function of the data
when $A$ is rank deficient.

**Reading.** The book says that the perturbed matrix has full rank $2$. The statement gives the
rank together with the independence of the columns.

The book takes $\varepsilon = 10^{-12}$. The statement holds for every $\varepsilon \neq 0$, and
its last part evaluates the solution at $\varepsilon = 10^{-12}$. -/
theorem example_3_11_perturbed {ε : ℝ} (hε : ε ≠ 0) :
    let Aε : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, ε; 0, 0]
    let b : Fin 3 → ℝ := ![1, 2, 3]
    Aε.rank = 2 ∧ LinearIndependent ℝ Aεᵀ ∧ (∀ xs, equation_3_73 Aε b xs ↔ xs = ![1, 2 / ε]) ∧
      (ε = 1 / 10 ^ 12 → (![1, 2 / ε] : Fin 2 → ℝ) = ![1, 2 * 10 ^ 12]) := by
  intro Aε b
  have hli : LinearIndependent ℝ Aεᵀ := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have h0 : g 0 = 0 := by simpa [Aε, Fin.sum_univ_two] using congrFun hg 0
    have h1 : g 1 = 0 := by simpa [Aε, Fin.sum_univ_two, hε] using congrFun hg 1
    rw [Fin.forall_fin_two]
    exact ⟨h0, h1⟩
  refine ⟨?_, hli, fun xs => ?_, fun h => ?_⟩
  · rw [← rank_transpose]
    exact hli.rank_matrix
  · rw [equation_3_74]
    constructor
    · intro hxs
      have h0 := congrFun hxs 0
      have h1 := congrFun hxs 1
      simp [Aε, b, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
      ext i
      fin_cases i
      · simpa using h0
      · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        rw [eq_div_iff hε]
        apply mul_left_cancel₀ hε
        linear_combination h1
    · rintro rfl
      ext i
      fin_cases i
      · simp [Aε, b, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_succ]
      · simp [Aε, b, Matrix.mul_apply, mulVec, dotProduct, Fin.sum_univ_succ]
        field_simp
  · rw [h]
    norm_num

/-! ### Underdetermined systems -/

/-- **Section 3.13** of [quarteroni2000numerical], underdetermined systems. Let
$A \in \mathbb{R}^{m \times n}$ have full rank with linearly independent rows (so $m \le n$),
and let $b \in \mathbb{R}^m$. Then:

* $A^+ = A^T (A A^T)^{-1}$;
* the vector $x^* = A^T (A A^T)^{-1} b$ solves $A x^* = b$, so the system is consistent;
* $x^*$ is a solution of (3.76);
* $\|x^*\|_2 \le \|x\|_2$ for every solution $x$ of $Ax = b$.

The book considers $m < n$. The statement needs only the independence of the rows, and so it
includes the case $m = n$. The proof specializes
`Matrix.pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose` and
`Matrix.toEuclideanLin_conjTranspose_mul_inv_self_mul_conjTranspose`, together with Theorem 3.9.

**Reading.** States explicit pseudoinverse and minimal-norm formulas and includes the square case.
-/
theorem underdetermined_minNorm {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A)
    (b : Fin m → ℝ) :
    A.pinv = Aᵀ * (A * Aᵀ)⁻¹ ∧ A *ᵥ (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b)) = b ∧
      equation_3_76 A b (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b)) ∧
        ∀ x, A *ᵥ x = b → ‖toLp 2 (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b))‖ ≤ ‖toLp 2 x‖ := by
  have hp : A.pinv = Aᵀ * (A * Aᵀ)⁻¹ := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact pinv_eq_conjTranspose_mul_inv_self_mul_conjTranspose hA
  have hsol : A *ᵥ (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b)) = b := by
    have := toEuclideanLin_conjTranspose_mul_inv_self_mul_conjTranspose hA (toLp 2 b)
    rwa [conjTranspose_eq_transpose_of_trivial, toEuclideanLin_toLp, toEuclideanLin_toLp,
      (toLp_injective 2).eq_iff, ← mulVec_mulVec] at this
  have h76 : equation_3_76 A b (Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b)) := by
    have := theorem_3_9 A b
    rwa [hp, ← mulVec_mulVec] at this
  refine ⟨hp, hsol, h76, fun x hx => h76.2 x fun y => ?_⟩
  rw [hx, sub_self, toLp_zero, norm_zero, zero_pow two_ne_zero]
  positivity

/-- **Section 3.13** of [quarteroni2000numerical], the QR factorization of $A^T$. Let
$A \in \mathbb{R}^{m \times n}$ with $m \le n$ have linearly independent rows, let $A^T = QR$ be
a QR factorization with reduced factors $\tilde Q \in \mathbb{R}^{n \times m}$ and
$\tilde R \in \mathbb{R}^{m \times m}$, and let $b \in \mathbb{R}^m$. Then $\tilde R$ is
nonsingular, $A A^T = \tilde R^T \tilde R$,
$$A^T (A A^T)^{-1} b = \tilde Q\, \tilde R^{-T} b,$$
and this vector is the solution of (3.76). It is obtained from one triangular solve with
$\tilde R^T$.

The book considers $m < n$. The statement includes the case $m = n$.

**Reading.** Spells out the transposed QR solve and includes the square case.
-/
theorem underdetermined_qr {A : Matrix (Fin m) (Fin n) ℝ} (hA : LinearIndependent ℝ A)
    {Q : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin n) (Fin m) ℝ} (h : IsQR Aᵀ Q R) (hmn : m ≤ n)
    (b : Fin m → ℝ) :
    IsUnit (firstRows R hmn) ∧ A * Aᵀ = (firstRows R hmn)ᵀ * firstRows R hmn ∧
      Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b) = firstColumns Q hmn *ᵥ ((firstRows R hmn)ᵀ⁻¹ *ᵥ b) ∧
        equation_3_76 A b (firstColumns Q hmn *ᵥ ((firstRows R hmn)ᵀ⁻¹ *ᵥ b)) := by
  have hA' : LinearIndependent ℝ Aᵀᵀ := by rwa [transpose_transpose]
  have hR : IsUnit (firstRows R hmn) := h.isUnit_firstRows_of_linearIndependent hmn hA'
  obtain ⟨hAT, hQ, -⟩ := property_3_3 h hmn
  have hA_eq : A = (firstRows R hmn)ᵀ * (firstColumns Q hmn)ᵀ := by
    rw [← transpose_mul, ← hAT, transpose_transpose]
  have hAAT : A * Aᵀ = (firstRows R hmn)ᵀ * firstRows R hmn := by
    rw [hA_eq, transpose_mul, transpose_transpose, transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (firstColumns Q hmn)ᵀ, hQ, Matrix.one_mul]
  have hx : Aᵀ *ᵥ ((A * Aᵀ)⁻¹ *ᵥ b) = firstColumns Q hmn *ᵥ ((firstRows R hmn)ᵀ⁻¹ *ᵥ b) := by
    rw [hAAT, mulVec_mulVec, mulVec_mulVec, hAT, Matrix.mul_inv_rev, Matrix.mul_assoc,
      ← Matrix.mul_assoc (firstRows R hmn), mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hR),
      Matrix.one_mul]
  exact ⟨hR, hAAT, hx, hx ▸ (underdetermined_minNorm hA b).2.2.1⟩

end QuarteroniSaccoSaleri.Chapter03
