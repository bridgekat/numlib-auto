/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Numlib.Analysis.Matrix.Function.Log
import Numlib.Analysis.Matrix.Function.Polar
import Numlib.Analysis.Matrix.Function.Sign
import Numlib.Analysis.Matrix.Function.Sqrt
import NumlibSurface.GolubVanLoan.Chapter09.Section03

/-!
# Golub and Van Loan, Section 9.4: The sign, square root, and log of a matrix

This module formalizes §9.4 of [golub2013matrix], three special matrix functions and the iterations
that compute them. For the matrix sign function $\operatorname{sign}(A)$ it proves the Jordan-form
expression, the half-plane projector $(I + \operatorname{sign}(A))/2$, the properties
(9.4.2)–(9.4.4) of Newton's iteration (9.4.1) and its quadratic convergence, and the Newton–Schulz
step (9.4.5). For the principal square root $A^{1/2}$ it proves existence and uniqueness, the
convergence of Newton's square-root iteration (9.4.7), and the properties (9.4.8)–(9.4.10) of the
Denman–Beavers iteration, with $\operatorname{sign}\left(\begin{bmatrix} 0 & A \\ I & 0
\end{bmatrix}\right)$. For the polar decomposition it proves existence (Theorem 9.4.1), the formulas
for the factors, Newton's polar iteration (9.4.11)–(9.4.12) and its convergence, the expression of
the polar factor through $\operatorname{sign}\left(\begin{bmatrix} 0 & A \\ A^T & 0
\end{bmatrix}\right)$, and a corrected form of the Li–Sun perturbation bound. For the principal
logarithm $\log(A)$ it proves existence and uniqueness of the real logarithm, the Maclaurin and
Gregory series, the $(3, 3)$ Padé approximant of $\log(1 + x)$, and the identity behind inverse
scaling and squaring.

The proofs specialize the backbone modules `Numlib.Analysis.Matrix.Function.Sign`,
`Numlib.Analysis.Matrix.Function.Sqrt`, `Numlib.Analysis.Matrix.Function.Log`,
`Numlib.Analysis.Matrix.Function.Polar` and `Numlib.LinearAlgebra.Matrix.Polar`.

## Main definitions

* §9.4.2, `GolubVanLoan.Chapter09.IsPrincipalSqrt`: $F$ is the principal square root of $A$ if
  $F^2 = A$ and every eigenvalue of $F$ has positive real part.

## Main results

* §9.4.1, `GolubVanLoan.Chapter09.matrixSign_eq_conj`: $\operatorname{sign}(A) = X
  \operatorname{diag}(-I_{m_1}, I_{m_2}) X^{-1}$ for a block diagonalization that separates the two
  half planes.
* §9.4.1, `GolubVanLoan.Chapter09.sign_projector`: $(I + \operatorname{sign}(A))/2$ is the
  projection onto the invariant subspace of the eigenvalues in the right half plane.
* §9.4.1, `GolubVanLoan.Chapter09.newtonSign_isUnit`: the Newton iterates $S_k$ of (9.4.1) are well
  defined and $\operatorname{sign}(S_k) = \operatorname{sign}(A)$.
* Equation (9.4.2), `GolubVanLoan.Chapter09.equation_9_4_2`:
  $S_{k+1} - S = \frac12 S_k^{-1} (S_k - S)^2$.
* Equation (9.4.3), `GolubVanLoan.Chapter09.equation_9_4_3`:
  $S_{k+1} + S = \frac12 S_k^{-1} (S_k + S)^2$.
* §9.4.1, `GolubVanLoan.Chapter09.isUnit_add_sign`: $M + \operatorname{sign}(M)$ is nonsingular.
* Equation (9.4.4), `GolubVanLoan.Chapter09.equation_9_4_4`: $G_k = (S_k - S)(S_k + S)^{-1}$
  satisfies $G_k = G_0^{2^k}$, and the eigenvalues of $G_0$ have modulus less than $1$.
* §9.4.1, `GolubVanLoan.Chapter09.newtonSign_tendsto`: $S_k \to \operatorname{sign}(A)$
  quadratically.
* Equation (9.4.5), `GolubVanLoan.Chapter09.equation_9_4_5`: the Newton–Schulz step
  $\frac12 S_k (3I - S_k^2)$.
* §9.4.2, `GolubVanLoan.Chapter09.principalSqrt_existsUnique`: a matrix with no eigenvalue on
  $(-\infty, 0]$ has exactly one principal square root.
* Equation (9.4.7), `GolubVanLoan.Chapter09.newtonSqrt_tendsto`: Newton's square-root iteration
  converges to $A^{1/2}$.
* Equation (9.4.8), `GolubVanLoan.Chapter09.equation_9_4_8`: the Newton sign iterates of
  $\begin{bmatrix} 0 & A \\ I & 0 \end{bmatrix}$ are the Denman–Beavers iterates.
* Equation (9.4.9), `GolubVanLoan.Chapter09.equation_9_4_9`: $X_k = A Y_k$.
* Equation (9.4.10), `GolubVanLoan.Chapter09.equation_9_4_10`: the decoupled forms of the
  Denman–Beavers iteration.
* §9.4.2, `GolubVanLoan.Chapter09.sign_block_sqrt`: $X_k \to A^{1/2}$, $Y_k \to A^{-1/2}$ and
  $\operatorname{sign}\left(\begin{bmatrix} 0 & A \\ I & 0 \end{bmatrix}\right) = \begin{bmatrix} 0
  & A^{1/2} \\ A^{-1/2} & 0 \end{bmatrix}$.
* Theorem 9.4.1, `GolubVanLoan.Chapter09.theorem_9_4_1`: every $A \in \mathbb{R}^{m \times n}$ with
  $m \ge n$ has a polar decomposition $A = UP$.
* §9.4.3, `GolubVanLoan.Chapter09.polar_factors`: $P = (A^T A)^{1/2}$, and $U = A (A^T A)^{-1/2}$
  when $\operatorname{rank}(A) = n$.
* Equations (9.4.11)–(9.4.12), `GolubVanLoan.Chapter09.equation_9_4_12`: Newton's polar iterates
  satisfy $X_k = U P_k$.
* §9.4.3, `GolubVanLoan.Chapter09.newtonPolar_tendsto`: Newton's polar iteration converges
  quadratically to $U$.
* §9.4.3, `GolubVanLoan.Chapter09.sign_block_polar`: $\operatorname{sign}\left(\begin{bmatrix} 0 & A
  \\ A^T & 0 \end{bmatrix}\right) = \begin{bmatrix} 0 & U \\ U^T & 0 \end{bmatrix}$ for nonsingular
  $A$.
* §9.4.3, `GolubVanLoan.Chapter09.li_sun`: the Li–Sun bound on $\|U - \tilde U\|_F$, under
  $\det A \cdot \det \tilde A > 0$.
* §9.4.4, `GolubVanLoan.Chapter09.realLog_existsUnique`: the real principal logarithm exists and is
  unique.
* §9.4.4, `GolubVanLoan.Chapter09.log_maclaurin`: the Maclaurin series of $\log(A)$.
* §9.4.4, `GolubVanLoan.Chapter09.log_gregory`: the Gregory series of $\log(A)$.
* §9.4.4, `GolubVanLoan.Chapter09.log_pade_33`: the $(3, 3)$ Padé approximant of $\log(1 + x)$.
* §9.4.4, `GolubVanLoan.Chapter09.log_inverse_scaling`: $\log(A) = 2^k \log(A_k)$ for the repeated
  square roots $A_k$.

## Conventions

* The matrix is $A \in \mathbb{C}^{n \times n}$, `A : Matrix (Fin n) (Fin n) ℂ`, except for the real
  logarithm and the polar decomposition.
* $\operatorname{sign}(A)$ is `Matrix.matrixSign A`, which is `pfc` of $z \mapsto
  \operatorname{sign}(\operatorname{Re} z)$. $A^{1/2}$ is `Matrix.principalSqrt A`, and $\log(A)$ is
  `Matrix.principalLog A`.
* "No eigenvalue on the imaginary axis" is `∀ μ ∈ spectrum ℂ A, μ.re ≠ 0`. "No eigenvalue on
  $(-\infty, 0]$" is `spectrum ℂ A ⊆ Complex.slitPlane`.
* Block matrices $\begin{bmatrix} P & Q \\ R & S \end{bmatrix}$ are `Matrix.fromBlocks` over
  `Fin m ⊕ Fin n`. A partition $X = [X_1 \; X_2]$ of the columns is given by a bijection
  `e : Fin m₁ ⊕ Fin m₂ ≃ Fin n`, with $X_i$ = `X.submatrix id (e ∘ Sum.in_)`. The columns of
  $X^{-H} = [Y_1 \; Y_2]$ are read through the rows of $X^{-1}$: $Y_i^H$ =
  `X⁻¹.submatrix (e ∘ Sum.in_) id`, written $Z_i$ in the statements.
* The norm $\|\cdot\|_2$ is the operator norm of the scope `Matrix.Norms.L2Operator`.
* A polar decomposition $A = UP$ is `Matrix.IsPolarDecomposition A U P`. Over $\mathbb{R}$ the
  conjugate transpose in its definition is the transpose.

## Deviations from the source

* **§9.4.1** (typo). The source derives the Jordan-form expression of $\operatorname{sign}(A)$ "from
  Theorem 9.1.1", which does not exist; the expression follows from the definition (9.1.3)–(9.1.4).
  The source also writes $S^2 = S$ for $S^2 = I$. See `GolubVanLoan.Chapter09.matrixSign_eq_conj`.
* **§9.4.2, the principal square root** (reading). The source leaves implicit that $A$ has no
  eigenvalue on $(-\infty, 0]$. The statement assumes it. See
  `GolubVanLoan.Chapter09.principalSqrt_existsUnique`.
* **Equation (9.4.11)** (reading). The body of the iteration is lost in the source. It is read off
  (9.4.12) as $X_{k+1} = (X_k + X_k^{-T})/2$. See `GolubVanLoan.Chapter09.equation_9_4_12`.
* **§9.4.3, $\operatorname{sign}\left(\begin{bmatrix} 0 & A \\ A^T & 0 \end{bmatrix}\right) =
  \begin{bmatrix} 0 & U \\ U^T & 0 \end{bmatrix}$** (correction). The identity needs $A$ to be
  nonsingular, which the source omits. See `GolubVanLoan.Chapter09.sign_block_polar`.
* **§9.4.3, the Li–Sun bound** (correction). The bound is false for nonsingular $A$ and $\tilde A$
  alone. The statement assumes $\det A \cdot \det \tilde A > 0$. See
  `GolubVanLoan.Chapter09.li_sun`.
* **§9.4.3, the citation of Li and Sun** (typo). The source dates the paper "(2003)". It appeared in
  SIAM J. Matrix Anal. Appl. 23 (2002). See `GolubVanLoan.Chapter09.li_sun`.

## Not formalized

* The four square roots of $\begin{bmatrix} 4 & 10 \\ 0 & 9 \end{bmatrix}$, a numerical example.
* The scaled Newton iteration (9.4.6) and its choices of $\mu_k$.
* QR with column pivoting on $(I + \operatorname{sign}(A))/2$; only the statement about the range of
  this projection is formalized.
* The `while` loop of inverse scaling and squaring; only its identity $\log(A) = 2^k \log(A_k)$ is
  formalized.
* The Problems.
-/

open Polynomial Finset Filter Topology Asymptotics

namespace GolubVanLoan.Chapter09

variable {n : ℕ}

/-! ### §9.4.1 The matrix sign function -/

/-- **§9.4.1** of [golub2013matrix], the Jordan-form expression of the sign function. Let
$A, X \in \mathbb{C}^{n \times n}$ with $X$ nonsingular and
$$X^{-1} A X = \begin{bmatrix} J_1 & 0 \\ 0 & J_2 \end{bmatrix},$$
where $J_1 \in \mathbb{C}^{m_1 \times m_1}$ has its eigenvalues in the open left half plane and
$J_2 \in \mathbb{C}^{m_2 \times m_2}$ has its eigenvalues in the open right half plane. Then
$$\operatorname{sign}(A) = X \begin{bmatrix} -I_{m_1} & 0 \\ 0 & I_{m_2} \end{bmatrix} X^{-1}.$$

**Typo.** The source derives this expression "from Theorem 9.1.1", which does not exist; it
follows from the definition (9.1.3)–(9.1.4) of $f(A)$. The text of §9.4.1 also writes $S^2 = S$
for $S^2 = I$.

The blocks $J_1$ and $J_2$ need not be Jordan blocks. The block matrix is placed in `Fin n` by
the bijection `e`. -/
theorem matrixSign_eq_conj {m₁ m₂ : ℕ} (e : Fin m₁ ⊕ Fin m₂ ≃ Fin n)
    {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) {J₁ : Matrix (Fin m₁) (Fin m₁) ℂ}
    {J₂ : Matrix (Fin m₂) (Fin m₂) ℂ}
    (h : X⁻¹ * A * X = Matrix.reindex e e (Matrix.fromBlocks J₁ 0 0 J₂))
    (h₁ : ∀ μ ∈ spectrum ℂ J₁, μ.re < 0) (h₂ : ∀ μ ∈ spectrum ℂ J₂, 0 < μ.re) :
    Matrix.matrixSign A = X * Matrix.reindex e e (Matrix.fromBlocks (-1) 0 0 1) * X⁻¹ :=
  Matrix.matrixSign_conj_fromBlocks e hX h h₁ h₂

/-- For a nonsingular $X$ with the column partition $X = [X_1 \; X_2]$ and the conformal row
partition of $X^{-1}$ into $Y_1^H$ and $Y_2^H$, $I = X_1 Y_1^H + X_2 Y_2^H$. -/
private theorem one_eq_add_blocks {m₁ m₂ : ℕ} (e : Fin m₁ ⊕ Fin m₂ ≃ Fin n)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) :
    (1 : Matrix (Fin n) (Fin n) ℂ) =
      X.submatrix id (e ∘ Sum.inl) * X⁻¹.submatrix (e ∘ Sum.inl) id +
        X.submatrix id (e ∘ Sum.inr) * X⁻¹.submatrix (e ∘ Sum.inr) id := by
  rw [← Matrix.mul_nonsing_inv X ((Matrix.isUnit_iff_isUnit_det X).mp hX)]
  ext i j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply, Function.comp_apply,
    id_eq]
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]

/-- **§9.4.1** of [golub2013matrix], the half-plane projector. Let $A$, $X$, $J_1$ and $J_2$ be as
in `GolubVanLoan.Chapter09.matrixSign_eq_conj`, and partition $X = [X_1 \; X_2]$ and
$X^{-H} = [Y_1 \; Y_2]$ conformally. Then
$$\operatorname{sign}(A) = X_2 Y_2^H - X_1 Y_1^H, \qquad I_n = X_1 Y_1^H + X_2 Y_2^H, \qquad X_2
  Y_2^H = \tfrac12 (I_n + \operatorname{sign}(A)).$$
The matrix $\frac12 (I_n + \operatorname{sign}(A))$ is idempotent, its range is
$\operatorname{ran}(X_2)$, the invariant subspace of the eigenvalues in the right half plane,
and this range has dimension $m_2$.

The rows $Y_i^H$ of $X^{-1}$ are written `Z₁` and `Z₂` in the statement. -/
theorem sign_projector {m₁ m₂ : ℕ} (e : Fin m₁ ⊕ Fin m₂ ≃ Fin n)
    {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) {J₁ : Matrix (Fin m₁) (Fin m₁) ℂ}
    {J₂ : Matrix (Fin m₂) (Fin m₂) ℂ}
    (h : X⁻¹ * A * X = Matrix.reindex e e (Matrix.fromBlocks J₁ 0 0 J₂))
    (h₁ : ∀ μ ∈ spectrum ℂ J₁, μ.re < 0) (h₂ : ∀ μ ∈ spectrum ℂ J₂, 0 < μ.re) :
    let X₁ := X.submatrix id (e ∘ Sum.inl)
    let X₂ := X.submatrix id (e ∘ Sum.inr)
    let Z₁ := X⁻¹.submatrix (e ∘ Sum.inl) id
    let Z₂ := X⁻¹.submatrix (e ∘ Sum.inr) id
    Matrix.matrixSign A = X₂ * Z₂ - X₁ * Z₁ ∧
    (1 : Matrix (Fin n) (Fin n) ℂ) = X₁ * Z₁ + X₂ * Z₂ ∧
    X₂ * Z₂ = (2 : ℂ)⁻¹ • (1 + Matrix.matrixSign A) ∧
    IsIdempotentElem ((2 : ℂ)⁻¹ • (1 + Matrix.matrixSign A)) ∧
    LinearMap.range ((2 : ℂ)⁻¹ • (1 + Matrix.matrixSign A)).mulVecLin =
      Submodule.span ℂ (Set.range X₂.col) ∧
    Module.finrank ℂ (LinearMap.range ((2 : ℂ)⁻¹ • (1 + Matrix.matrixSign A)).mulVecLin) = m₂ := by
  intro X₁ X₂ Z₁ Z₂
  obtain ⟨hP, hidem, hran, hdim⟩ := Matrix.range_one_add_matrixSign e hX h h₁ h₂
  have hI : (1 : Matrix (Fin n) (Fin n) ℂ) = X₁ * Z₁ + X₂ * Z₂ := one_eq_add_blocks e hX
  refine ⟨?_, hI, hP.symm, hidem, hran, by rw [hdim, Fintype.card_fin]⟩
  have hS : Matrix.matrixSign A = (2 : ℂ) • ((2 : ℂ)⁻¹ • (1 + Matrix.matrixSign A)) - 1 := by
    rw [smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul, add_sub_cancel_left]
  rw [hS, hP, hI]
  module

/-- **§9.4.1** of [golub2013matrix], "this iteration is well-defined". Let
$A \in \mathbb{C}^{n \times n}$ have no eigenvalue on the imaginary axis, and let $S_k$ be the
Newton iterates (9.4.1), $S_0 = A$ and $S_{k+1} = (S_k + S_k^{-1})/2$. Then every $S_k$ is
nonsingular and has no eigenvalue on the imaginary axis, and $\operatorname{sign}(S_k) =
\operatorname{sign}(A)$.

The iterates are `Matrix.newtonSignIterate A k`. -/
theorem newtonSign_isUnit {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) :
    IsUnit (Matrix.newtonSignIterate A k) ∧
    (∀ μ ∈ spectrum ℂ (Matrix.newtonSignIterate A k), μ.re ≠ 0) ∧
    Matrix.matrixSign (Matrix.newtonSignIterate A k) = Matrix.matrixSign A :=
  ⟨(Matrix.isUnit_newtonSignIterate hA k).1, (Matrix.isUnit_newtonSignIterate hA k).2,
    Matrix.matrixSign_newtonSignIterate hA k⟩

/-- For $A$ with no eigenvalue on the imaginary axis, $\operatorname{sign}(A)^2 = I$, and every
Newton iterate $S_k$ commutes with $\operatorname{sign}(A)$. -/
private theorem newtonSign_aux {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) :
    Matrix.matrixSign A * Matrix.matrixSign A = 1 ∧
    Commute (Matrix.newtonSignIterate A k) (Matrix.matrixSign A) := by
  refine ⟨by rw [← sq]; exact Matrix.matrixSign_sq hA, ?_⟩
  rw [← Matrix.matrixSign_newtonSignIterate hA k]
  exact Matrix.commute_matrixSign _

/-- **Equation (9.4.2)** of [golub2013matrix]. Let $A \in \mathbb{C}^{n \times n}$ have no
eigenvalue on the imaginary axis, let $S = \operatorname{sign}(A)$, and let $S_k$ be the Newton
iterates (9.4.1). Then for every $k$
$$S_{k+1} - S = \tfrac12 S_k^{-1} (S_k - S)^2.$$
-/
theorem equation_9_4_2 {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) :
    Matrix.newtonSignIterate A (k + 1) - Matrix.matrixSign A =
      (2 : ℂ)⁻¹ • ((Matrix.newtonSignIterate A k)⁻¹ *
        (Matrix.newtonSignIterate A k - Matrix.matrixSign A) ^ 2) := by
  obtain ⟨hS, hc⟩ := newtonSign_aux hA k
  rw [Matrix.newtonSignIterate_succ, Matrix.nonsing_inv_eq_ringInverse]
  exact half_smul_add_inverse_sub_eq_of_commute (newtonSign_isUnit hA k).1 hS hc

/-- **Equation (9.4.3)** of [golub2013matrix]. Let $A \in \mathbb{C}^{n \times n}$ have no
eigenvalue on the imaginary axis, let $S = \operatorname{sign}(A)$, and let $S_k$ be the Newton
iterates (9.4.1). Then for every $k$
$$S_{k+1} + S = \tfrac12 S_k^{-1} (S_k + S)^2.$$
-/
theorem equation_9_4_3 {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0)
    (k : ℕ) :
    Matrix.newtonSignIterate A (k + 1) + Matrix.matrixSign A =
      (2 : ℂ)⁻¹ • ((Matrix.newtonSignIterate A k)⁻¹ *
        (Matrix.newtonSignIterate A k + Matrix.matrixSign A) ^ 2) := by
  obtain ⟨hS, hc⟩ := newtonSign_aux hA k
  rw [Matrix.newtonSignIterate_succ, Matrix.nonsing_inv_eq_ringInverse]
  exact half_smul_add_inverse_add_eq_of_commute (newtonSign_isUnit hA k).1 hS hc

/-- **§9.4.1** of [golub2013matrix]. Let $M \in \mathbb{C}^{n \times n}$ have no eigenvalue on the
imaginary axis, so that $\operatorname{sign}(M)$ is defined. Then $M + \operatorname{sign}(M)$
is nonsingular. -/
theorem isUnit_add_sign {M : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ μ ∈ spectrum ℂ M, μ.re ≠ 0) :
    IsUnit (M + Matrix.matrixSign M) :=
  Matrix.isUnit_add_matrixSign hM

/-- For $z \in \mathbb{C}$ off the imaginary axis, $|z - \operatorname{sign}(\operatorname{Re} z)| <
|z + \operatorname{sign}(\operatorname{Re} z)|$.
-/
private theorem norm_sub_sign_lt {z : ℂ} (hz : z.re ≠ 0) :
    ‖z - ((SignType.sign z.re : SignType) : ℂ)‖ < ‖z + ((SignType.sign z.re : SignType) : ℂ)‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  rcases lt_or_gt_of_ne hz with h | h
  · simp only [sign_neg h, SignType.coe_neg, SignType.coe_one, Complex.sub_re, Complex.add_re,
      Complex.sub_im, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
      Complex.one_im]
    nlinarith
  · simp only [sign_pos h, SignType.coe_one, Complex.sub_re, Complex.add_re, Complex.sub_im,
      Complex.add_im, Complex.one_re, Complex.one_im]
    nlinarith

/-- **Equation (9.4.4)** of [golub2013matrix]. Let $A \in \mathbb{C}^{n \times n}$ have no
eigenvalue on the imaginary axis, let $S = \operatorname{sign}(A)$, let $S_k$ be the Newton
iterates (9.4.1), and let $G_k = (S_k - S)(S_k + S)^{-1}$. Then $G_{k+1} = G_k^2$, hence
$G_k = G_0^{2^k}$ for every $k$. Every eigenvalue $\mu$ of $G_0 = (A - S)(A + S)^{-1}$ has the
form
$$\mu = \frac{\lambda - \operatorname{sign}(\operatorname{Re} \lambda)}{\lambda +
  \operatorname{sign}(\operatorname{Re} \lambda)}$$
for an eigenvalue $\lambda$ of $A$, and $|\mu| < 1$. -/
theorem equation_9_4_4 {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0) :
    let S := Matrix.matrixSign A
    let G := fun k => (Matrix.newtonSignIterate A k - S) * (Matrix.newtonSignIterate A k + S)⁻¹
    (∀ k, G (k + 1) = G k ^ 2) ∧ (∀ k, G k = G 0 ^ 2 ^ k) ∧
    ∀ μ ∈ spectrum ℂ (G 0), ∃ l ∈ spectrum ℂ A,
      μ = (l - ((SignType.sign l.re : SignType) : ℂ)) /
        (l + ((SignType.sign l.re : SignType) : ℂ)) ∧
      ‖μ‖ < 1 := by
  intro S G
  have hstep : ∀ k, G (k + 1) = G k ^ 2 := by
    intro k
    set s := Matrix.newtonSignIterate A k
    obtain ⟨hS2, hsS⟩ := newtonSign_aux hA k
    obtain ⟨hsu, hsre, hsign⟩ := newtonSign_isUnit hA k
    obtain ⟨-, hsre', hsign'⟩ := newtonSign_isUnit hA (k + 1)
    have hQ : IsUnit (s + S) := by
      have := Matrix.isUnit_add_matrixSign hsre
      rwa [hsign] at this
    have hQ' : IsUnit (Matrix.newtonSignIterate A (k + 1) + S) := by
      have := Matrix.isUnit_add_matrixSign hsre'
      rwa [hsign'] at this
    set P := s - S
    set Q := s + S
    have hPs : Commute P s := (Commute.refl s).sub_left hsS.symm
    have hPQ : Commute P Q := hPs.add_right (hsS.sub_left (Commute.refl S))
    have hPQi : Commute P Q⁻¹ := Matrix.commute_nonsing_inv_right hPQ
    have hQis : Commute Q⁻¹ s⁻¹ := Matrix.commute_nonsing_inv_right
      (Matrix.commute_nonsing_inv_right ((Commute.refl s).add_right hsS)).symm
    have hQiQc : Commute Q⁻¹ Q := (Matrix.commute_nonsing_inv_right (Commute.refl Q)).symm
    have hPsi : Commute P s⁻¹ := Matrix.commute_nonsing_inv_right hPs
    have hQiQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
    have key : G k ^ 2 * (Matrix.newtonSignIterate A (k + 1) + S) =
        Matrix.newtonSignIterate A (k + 1) - S := by
      rw [equation_9_4_2 hA k, equation_9_4_3 hA k, mul_smul_comm]
      congr 1
      change (P * Q⁻¹) ^ 2 * (s⁻¹ * Q ^ 2) = s⁻¹ * P ^ 2
      calc (P * Q⁻¹) ^ 2 * (s⁻¹ * Q ^ 2)
          = P ^ 2 * ((Q⁻¹ ^ 2 * s⁻¹) * Q ^ 2) := by
            rw [hPQi.mul_pow]; simp only [mul_assoc]
        _ = P ^ 2 * s⁻¹ * (Q⁻¹ ^ 2 * Q ^ 2) := by
            rw [(hQis.pow_left 2).eq]; simp only [mul_assoc]
        _ = s⁻¹ * P ^ 2 := by
            rw [← hQiQc.mul_pow, hQiQ, one_pow, mul_one, (hPsi.pow_left 2).eq]
    have hQ'i : (Matrix.newtonSignIterate A (k + 1) + S) *
        (Matrix.newtonSignIterate A (k + 1) + S)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hQ')
    change (Matrix.newtonSignIterate A (k + 1) - S) *
      (Matrix.newtonSignIterate A (k + 1) + S)⁻¹ = G k ^ 2
    rw [← key, mul_assoc, hQ'i, mul_one]
  have hpow : ∀ k, G k = G 0 ^ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [hstep, ih, ← pow_mul, pow_succ]
  refine ⟨hstep, hpow, ?_⟩
  -- the spectrum of `G₀` through the functional calculus
  have hI : IsIntegral ℂ A := Algebra.IsIntegral.isIntegral A
  have hs := IsAlgClosed.splits (minpoly ℂ A)
  set sg : ℂ → ℂ := fun z => ((SignType.sign z.re : SignType) : ℂ)
  have hroot : ∀ μ ∈ (minpoly ℂ A).roots, μ.re ≠ 0 := fun μ hμ =>
    hA μ ((spectrum.mem_iff_isRoot_minpoly hI).2 (Polynomial.isRoot_of_mem_roots hμ))
  have hsg : ∀ (k : ℕ), ∀ μ ∈ (minpoly ℂ A).roots, ContDiffAt ℂ k sg μ := fun k μ hμ =>
    contDiffAt_const.congr_of_eventuallyEq (Complex.sign_re_eventuallyEq (hroot μ hμ))
  have hid : ∀ (k : ℕ), ∀ μ ∈ (minpoly ℂ A).roots, ContDiffAt ℂ k (fun z : ℂ => z) μ :=
    fun k μ _ => contDiffAt_id
  have hnz : ∀ μ ∈ (minpoly ℂ A).roots, μ + sg μ ≠ 0 := fun μ hμ h => by
    have := norm_sub_sign_lt (hroot μ hμ)
    simp only [sg] at h
    rw [h, norm_zero] at this
    exact absurd this (not_lt.mpr (norm_nonneg _))
  have hsub : A - S = pfc (fun z => z - sg z) A := by
    rw [show (fun z => z - sg z) = (fun z : ℂ => z) - sg from rfl,
      pfc_sub (fun μ hμ => hid _ μ hμ) (fun μ hμ => hsg _ μ hμ), pfc_id hI hs]
    rfl
  have hadd : A + S = pfc (fun z => z + sg z) A := by
    rw [show (fun z => z + sg z) = (fun z : ℂ => z) + sg from rfl,
      pfc_add (fun μ hμ => hid _ μ hμ) (fun μ hμ => hsg _ μ hμ), pfc_id hI hs]
    rfl
  have hcadd : ∀ (k : ℕ), ∀ μ ∈ (minpoly ℂ A).roots, ContDiffAt ℂ k (fun z => z + sg z) μ :=
    fun k μ hμ => (hid k μ hμ).add (hsg k μ hμ)
  have hinv := (pfc_inv hI hs (fun μ hμ => hcadd _ μ hμ) hnz).2
  have hG0 : G 0 = pfc (fun z => (z - sg z) * (z + sg z)⁻¹) A := by
    change (A - S) * (A + S)⁻¹ = _
    rw [show (fun z => (z - sg z) * (z + sg z)⁻¹) =
        (fun z => z - sg z) * fun z => (z + sg z)⁻¹ from rfl,
      pfc_mul (f := fun z => z - sg z) (g := fun z => (z + sg z)⁻¹) hI hs
        (fun μ hμ => (hid _ μ hμ).sub (hsg _ μ hμ))
        (fun μ hμ => (hcadd _ μ hμ).inv (hnz μ hμ)), hinv, hsub, hadd,
      Matrix.nonsing_inv_eq_ringInverse]
  intro μ hμ
  rw [hG0, spectrum_pfc hI hs] at hμ
  obtain ⟨l, hl, rfl⟩ := hμ
  refine ⟨l, hl, by simp only [sg, div_eq_mul_inv], ?_⟩
  have hlt := norm_sub_sign_lt (hA l hl)
  rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one ((norm_nonneg _).trans_lt hlt)]
  exact hlt

open scoped Matrix.Norms.L2Operator in
/-- **§9.4.1** of [golub2013matrix], convergence of Newton's sign iteration. Let
$A \in \mathbb{C}^{n \times n}$ have no eigenvalue on the imaginary axis, let
$S = \operatorname{sign}(A)$, and let $S_k$ be the Newton iterates (9.4.1). Then $S_k \to S$,
and the convergence is quadratic:
$$\|S_{k+1} - S\|_2 \le \tfrac12 \|S_k^{-1}\|_2 \|S_k - S\|_2^2.$$
-/
theorem newtonSign_tendsto {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, μ.re ≠ 0) :
    Tendsto (Matrix.newtonSignIterate A) atTop (𝓝 (Matrix.matrixSign A)) ∧
    ∀ k, ‖Matrix.newtonSignIterate A (k + 1) - Matrix.matrixSign A‖ ≤
      2⁻¹ * ‖(Matrix.newtonSignIterate A k)⁻¹‖ *
        ‖Matrix.newtonSignIterate A k - Matrix.matrixSign A‖ ^ 2 :=
  ⟨Matrix.tendsto_newtonSignIterate hA, Matrix.norm_newtonSignIterate_sub_le hA⟩

/-- **Equation (9.4.5)** of [golub2013matrix] (the Newton–Schulz step). For every
$S \in \mathbb{C}^{n \times n}$, replacing $S^{-1}$ by its Newton approximation $S(2I - S^2)$ in
the Newton step (9.4.1) gives
$$\tfrac12 \big(S + S(2I - S^2)\big) = \tfrac12 S (3I - S^2).$$
-/
theorem equation_9_4_5 (S : Matrix (Fin n) (Fin n) ℂ) :
    (2 : ℂ)⁻¹ • (S + S * (2 • 1 - S ^ 2)) = (2 : ℂ)⁻¹ • (S * (3 • 1 - S ^ 2)) := by
  congr 1
  noncomm_ring

/-! ### §9.4.2 The matrix square root -/

/-- **§9.4.2** of [golub2013matrix], definition of the principal square root. For
$F, A \in \mathbb{C}^{n \times n}$, $F$ is **the principal square root** of $A$ if (a) $F^2 = A$
and (b) every eigenvalue of $F$ has positive real part. -/
def IsPrincipalSqrt (F A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  F ^ 2 = A ∧ ∀ μ ∈ spectrum ℂ F, 0 < μ.re

/-- **§9.4.2** of [golub2013matrix], "we designate this matrix by $A^{1/2}$". Let
$A \in \mathbb{C}^{n \times n}$ have no eigenvalue on $(-\infty, 0]$. Then $A$ has exactly one
principal square root, and it is $A^{1/2}$.

**Reading.** The source leaves implicit the hypothesis that no eigenvalue of $A$ lies on
$(-\infty, 0]$. The statement assumes it.

The matrix $A^{1/2}$ is `Matrix.principalSqrt A`, that is, `pfc` of the principal branch
`Complex.sqrt`. -/
theorem principalSqrt_existsUnique {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : spectrum ℂ A ⊆ Complex.slitPlane) :
    (∃! F, IsPrincipalSqrt F A) ∧ IsPrincipalSqrt (Matrix.principalSqrt A) A :=
  ⟨Matrix.existsUnique_sq_eq_of_re_pos hA,
    ⟨(Matrix.principalSqrt_sq hA).1, (Matrix.principalSqrt_sq hA).2.2⟩⟩

open scoped Matrix.Norms.L2Operator in
/-- **Equation (9.4.7)** of [golub2013matrix] and §9.4.2, Newton's square-root iteration. Let
$A \in \mathbb{C}^{n \times n}$ have no eigenvalue on $(-\infty, 0]$, and let $X_0 = A$ and
$X_{k+1} = (X_k + X_k^{-1} A)/2$. Then $X_k = A^{1/2} S_k$, where $S_k$ are the Newton sign
iterates (9.4.1) of $A^{1/2}$, and $X_k \to A^{1/2}$. "Global convergence and local quadratic
convergence follow from what we know about (9.4.1)": with $S = \operatorname{sign}(A^{1/2})$,
$$\|S_{k+1} - S\|_2 \le \tfrac12 \|S_k^{-1}\|_2 \|S_k - S\|_2^2.$$

The iterates $X_k$ are `Matrix.newtonSqrtIterate A k`. -/
theorem newtonSqrt_tendsto {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : spectrum ℂ A ⊆ Complex.slitPlane) :
    (∀ k, Matrix.newtonSqrtIterate A k =
      Matrix.principalSqrt A * Matrix.newtonSignIterate (Matrix.principalSqrt A) k) ∧
    Tendsto (Matrix.newtonSqrtIterate A) atTop (𝓝 (Matrix.principalSqrt A)) ∧
    ∀ k, ‖Matrix.newtonSignIterate (Matrix.principalSqrt A) (k + 1) -
        Matrix.matrixSign (Matrix.principalSqrt A)‖ ≤
      2⁻¹ * ‖(Matrix.newtonSignIterate (Matrix.principalSqrt A) k)⁻¹‖ *
        ‖Matrix.newtonSignIterate (Matrix.principalSqrt A) k -
          Matrix.matrixSign (Matrix.principalSqrt A)‖ ^ 2 :=
  ⟨Matrix.newtonSqrtIterate_eq_mul_newtonSignIterate hA, Matrix.tendsto_newtonSqrtIterate hA,
    (newtonSign_tendsto fun μ hμ =>
      ((principalSqrt_existsUnique hA).2.2 μ hμ).ne').2⟩

/-- **Equation (9.4.8)** of [golub2013matrix] (the Denman–Beavers iteration). Let
$A \in \mathbb{C}^{n \times n}$ have no eigenvalue on $(-\infty, 0]$, and let $\tilde S_k$ be
the Newton sign iterates (9.4.1) of $\tilde A = \begin{bmatrix} 0 & A \\ I & 0 \end{bmatrix}$.
Then
$$\tilde S_k = \begin{bmatrix} 0 & X_k \\ Y_k & 0 \end{bmatrix},$$
where $X_0 = A$, $Y_0 = I$, $X_{k+1} = (X_k + Y_k^{-1})/2$ and $Y_{k+1} = (Y_k + X_k^{-1})/2$,
and every $X_k$ and $Y_k$ is nonsingular.

The pairs $(X_k, Y_k)$ are `Matrix.denmanBeavers A k`. -/
theorem equation_9_4_8 {A : Matrix (Fin n) (Fin n) ℂ} (hA : spectrum ℂ A ⊆ Complex.slitPlane)
    (k : ℕ) :
    Matrix.newtonSignIterate (Matrix.fromBlocks 0 A 1 0) k =
      Matrix.fromBlocks 0 (Matrix.denmanBeavers A k).1 (Matrix.denmanBeavers A k).2 0 ∧
    Matrix.denmanBeavers A 0 = (A, 1) ∧
    Matrix.denmanBeavers A (k + 1) =
      ((2 : ℂ)⁻¹ • ((Matrix.denmanBeavers A k).1 + (Matrix.denmanBeavers A k).2⁻¹),
        (2 : ℂ)⁻¹ • ((Matrix.denmanBeavers A k).2 + (Matrix.denmanBeavers A k).1⁻¹)) ∧
    IsUnit (Matrix.denmanBeavers A k).1 ∧ IsUnit (Matrix.denmanBeavers A k).2 :=
  ⟨(Matrix.newtonSignIterate_fromBlocks hA k).1, rfl, rfl,
    (Matrix.newtonSignIterate_fromBlocks hA k).2.1, (Matrix.newtonSignIterate_fromBlocks hA k).2.2⟩

/-- **Equation (9.4.9)** of [golub2013matrix]. Let $A \in \mathbb{C}^{n \times n}$ have no
eigenvalue on $(-\infty, 0]$, and let $X_k$, $Y_k$ be the Denman–Beavers iterates (9.4.8). Then
$X_k = A Y_k$ for every $k$.

The source leaves this identity to Problem P9.4.4. -/
theorem equation_9_4_9 {A : Matrix (Fin n) (Fin n) ℂ} (hA : spectrum ℂ A ⊆ Complex.slitPlane)
    (k : ℕ) : (Matrix.denmanBeavers A k).1 = A * (Matrix.denmanBeavers A k).2 :=
  (Matrix.denmanBeavers_fst_eq_mul_snd hA k).1

/-- **Equation (9.4.10)** of [golub2013matrix]. Let $A \in \mathbb{C}^{n \times n}$ have no
eigenvalue on $(-\infty, 0]$, and let $X_k$, $Y_k$ be the Denman–Beavers iterates (9.4.8). Then
for every $k$
$$X_{k+1} = \tfrac12 (X_k + A X_k^{-1}), \qquad Y_{k+1} = \tfrac12 (Y_k + A^{-1} Y_k^{-1}).$$
-/
theorem equation_9_4_10 {A : Matrix (Fin n) (Fin n) ℂ} (hA : spectrum ℂ A ⊆ Complex.slitPlane)
    (k : ℕ) :
    (Matrix.denmanBeavers A (k + 1)).1 =
      (2 : ℂ)⁻¹ • ((Matrix.denmanBeavers A k).1 + A * (Matrix.denmanBeavers A k).1⁻¹) ∧
    (Matrix.denmanBeavers A (k + 1)).2 =
      (2 : ℂ)⁻¹ • ((Matrix.denmanBeavers A k).2 + A⁻¹ * (Matrix.denmanBeavers A k).2⁻¹) := by
  set X := (Matrix.denmanBeavers A k).1
  set Y := (Matrix.denmanBeavers A k).2
  have hXY : X = A * Y := equation_9_4_9 hA k
  have hAu : IsUnit A.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← spectrum.zero_notMem_iff ℂ]
    exact fun h => Complex.slitPlane_ne_zero (hA h) rfl
  -- `X_k` commutes with `A`
  have hcomm : ∀ j, Commute A (Matrix.denmanBeavers A j).1 := by
    intro j
    rw [(Matrix.denmanBeavers_fst_eq_mul_snd hA j).2]
    induction j with
    | zero => exact Commute.refl A
    | succ j ih =>
      rw [Matrix.newtonSqrtIterate]
      exact ((ih.add_right ((Matrix.commute_nonsing_inv_right ih).mul_right
        (Commute.refl A)))).smul_right _
  have hc : Commute A X := hcomm k
  have hY : Y = A⁻¹ * X := by rw [hXY, ← mul_assoc, Matrix.nonsing_inv_mul A hAu, one_mul]
  have hYi : Y⁻¹ = A * X⁻¹ := by
    rw [hY, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv A hAu,
      (Matrix.commute_nonsing_inv_right hc).eq]
  have hAY : Commute A Y := by
    rw [hY]
    exact (Matrix.commute_nonsing_inv_right (Commute.refl A)).mul_right hc
  have hXi : X⁻¹ = A⁻¹ * Y⁻¹ := by
    rw [hXY, Matrix.mul_inv_rev,
      (Matrix.commute_nonsing_inv_right (Matrix.commute_nonsing_inv_right hAY).symm).eq]
  constructor
  · change (2 : ℂ)⁻¹ • (X + Y⁻¹) = _
    rw [hYi]
  · change (2 : ℂ)⁻¹ • (Y + X⁻¹) = _
    rw [hXi]

/-- **§9.4.2** of [golub2013matrix], convergence of the Denman–Beavers iteration. Let
$A \in \mathbb{C}^{n \times n}$ have no eigenvalue on $(-\infty, 0]$, and let $X_k$, $Y_k$ be
the iterates (9.4.8). Then $X_k \to A^{1/2}$, $Y_k \to A^{-1/2}$, and
$$\operatorname{sign}\left(\begin{bmatrix} 0 & A \\ I & 0 \end{bmatrix}\right) = \begin{bmatrix}
  0 & A^{1/2} \\ A^{-1/2} & 0 \end{bmatrix}.$$
-/
theorem sign_block_sqrt {A : Matrix (Fin n) (Fin n) ℂ} (hA : spectrum ℂ A ⊆ Complex.slitPlane) :
    Tendsto (fun k => (Matrix.denmanBeavers A k).1) atTop (𝓝 (Matrix.principalSqrt A)) ∧
    Tendsto (fun k => (Matrix.denmanBeavers A k).2) atTop (𝓝 (Matrix.principalSqrt A)⁻¹) ∧
    Matrix.matrixSign (Matrix.fromBlocks 0 A 1 0) =
      Matrix.fromBlocks 0 (Matrix.principalSqrt A) (Matrix.principalSqrt A)⁻¹ 0 :=
  ⟨Matrix.tendsto_denmanBeavers_fst hA, Matrix.tendsto_denmanBeavers_snd hA,
    Matrix.matrixSign_fromBlocks_zero_one hA⟩

/-! ### §9.4.3 The polar decomposition -/

open scoped Matrix

/-- **Theorem 9.4.1** of [golub2013matrix] (polar decomposition). "If
$A \in \mathbb{R}^{m \times n}$ and $m \ge n$, then there exists a matrix
$U \in \mathbb{R}^{m \times n}$ with orthonormal columns and a symmetric positive semidefinite
$P \in \mathbb{R}^{n \times n}$ so that $A = UP$."

The conclusion is `Matrix.IsPolarDecomposition A U P`: $U^T U = I$, $P$ is positive
semidefinite, and $A = UP$. The proof specializes `Matrix.exists_isPolarDecomposition`, which
constructs the factors from an SVD, as the source does. -/
theorem theorem_9_4_1 {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hmn : n ≤ m) :
    ∃ U P, Matrix.IsPolarDecomposition A U P :=
  Matrix.exists_isPolarDecomposition A (by simpa using hmn)

open scoped MatrixOrder in
/-- **§9.4.3** of [golub2013matrix], the polar factors. Let $A = UP$ be a polar decomposition of
$A \in \mathbb{R}^{m \times n}$. Then $P = (A^T A)^{1/2}$, the positive semidefinite square
root, and if $\operatorname{rank}(A) = n$, then
$$U = A (A^T A)^{-1/2}.$$

The positive semidefinite square root is `CFC.sqrt`. -/
theorem polar_factors {m : ℕ} {A U : Matrix (Fin m) (Fin n) ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (h : Matrix.IsPolarDecomposition A U P) :
    P = CFC.sqrt (Aᵀ * A) ∧ (A.rank = n → U = A * (CFC.sqrt (Aᵀ * A))⁻¹) := by
  have hT : Aᴴ = Aᵀ := Matrix.conjTranspose_eq_transpose_of_trivial A
  refine ⟨hT ▸ h.eq_cfcSqrt, fun hr => ?_⟩
  have hunit : IsUnit (Aᴴ * A) := by
    refine Matrix.isUnit_of_rank_eq_card ?_
    rw [hT, Matrix.rank_transpose_mul_self, hr, Fintype.card_fin]
  exact hT ▸ h.eq_mul_inv_cfcSqrt
    ((Matrix.posSemidef_conjTranspose_mul_self A).posDef_iff_isUnit.2 hunit)

/-- **Equations (9.4.11)–(9.4.12)** of [golub2013matrix] (Newton's polar iteration). Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular with polar decomposition $A = UP$, and let
$X_0 = A$ and $X_{k+1} = (X_k + X_k^{-T})/2$. Then every $X_k$ is nonsingular, and
$X_k = U P_k$, where $P_0 = P$, $P_{k+1} = (P_k + P_k^{-1})/2$ and every $P_k$ is positive
definite.

**Reading.** The body of the iteration (9.4.11) is lost in the source. It is read off (9.4.12).

The iterates $X_k$ and $P_k$ are `Matrix.newtonPolarIterate A k` and
`Matrix.newtonPolarIterate P k`. -/
theorem equation_9_4_12 {A U P : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (h : Matrix.IsPolarDecomposition A U P) (k : ℕ) :
    Matrix.newtonPolarIterate A (k + 1) =
        (2 : ℝ)⁻¹ • (Matrix.newtonPolarIterate A k + ((Matrix.newtonPolarIterate A k)⁻¹)ᵀ) ∧
      IsUnit (Matrix.newtonPolarIterate A k) ∧
      Matrix.newtonPolarIterate A k = U * Matrix.newtonPolarIterate P k ∧
      (Matrix.newtonPolarIterate P k).PosDef ∧
      Matrix.newtonPolarIterate P (k + 1) =
        (2 : ℝ)⁻¹ • (Matrix.newtonPolarIterate P k + (Matrix.newtonPolarIterate P k)⁻¹) := by
  obtain ⟨hX, hP⟩ := Matrix.newtonPolarIterate_eq hA h k
  have hU : IsUnit U := Matrix.isUnit_of_mem_unitaryGroup h.mem_unitaryGroup
  refine ⟨?_, hX ▸ hU.mul hP.isUnit, hX, hP, ?_⟩
  · rw [Matrix.newtonPolarIterate_succ, Matrix.conjTranspose_eq_transpose_of_trivial]
  · rw [Matrix.newtonPolarIterate_succ, hP.inv.isHermitian.eq]

section Newton

open scoped Matrix.Norms.L2Operator

/-- **§9.4.3** of [golub2013matrix], convergence of Newton's polar iteration. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular with polar decomposition $A = UP$, and let $X_k$
and $P_k$ be as in (9.4.12). Then $\|X_k - U\|_2 = \|P_k - I\|_2$ for every $k$, the $P_k$
converge quadratically,
$$\|P_{k+1} - I\|_2 \le \tfrac12 \|P_k^{-1}\|_2 \|P_k - I\|_2^2,$$
and $X_k \to U$.

The iteration for $P_k$ is the Newton sign iteration of $P$, and $\operatorname{sign}(P) = I$. -/
theorem newtonPolar_tendsto {A U P : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (h : Matrix.IsPolarDecomposition A U P) :
    (∀ k, ‖Matrix.newtonPolarIterate A k - U‖ = ‖Matrix.newtonPolarIterate P k - 1‖) ∧
      (∀ k, ‖Matrix.newtonPolarIterate P (k + 1) - 1‖ ≤
        ‖(Matrix.newtonPolarIterate P k)⁻¹‖ * ‖Matrix.newtonPolarIterate P k - 1‖ ^ 2 / 2) ∧
      Tendsto (Matrix.newtonPolarIterate A) atTop (𝓝 U) :=
  ⟨Matrix.l2_opNorm_newtonPolarIterate_sub hA h,
    Matrix.l2_opNorm_newtonPolarIterate_succ_sub_one_le
      (h.posSemidef.posDef_iff_isUnit.2 (h.isUnit hA)),
    Matrix.tendsto_newtonPolarIterate hA h⟩

end Newton

/-! ### The sign of $\begin{bmatrix} 0 & A \\ A^T & 0 \end{bmatrix}$ and the polar factor -/

section SignBlock

open Matrix

variable {A U V : Matrix (Fin n) (Fin n) ℝ} {σ : ℕ → ℝ}

/-- A real SVD of $A$ is a complex SVD of the complexified matrix. -/
private theorem isSVD_complexify (h : IsSVD A U σ V) :
    IsSVD (complexify A) (complexify U) σ (complexify V) := by
  have hunit : ∀ {W : Matrix (Fin n) (Fin n) ℝ}, W ∈ unitaryGroup (Fin n) ℝ →
      complexify W ∈ unitaryGroup (Fin n) ℂ := fun hW => by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, ← complexify_conjTranspose,
      ← complexify_mul, ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 hW, complexify_one]
  refine ⟨⟨hunit h.mem_unitaryGroup_left, hunit h.mem_unitaryGroup_right, ?_⟩, h.antitone, h.nonneg⟩
  rw [star_eq_conjTranspose, ← complexify_conjTranspose, ← complexify_mul, ← complexify_mul,
    ← star_eq_conjTranspose, h.star_mul_mul]
  ext i j
  simp only [complexify_apply, rectDiagonal_apply]
  split_ifs <;> simp

/-- The complexified real matrix $\begin{bmatrix} 0 & A \\ A^T & 0 \end{bmatrix}$ is
$\begin{bmatrix} 0 & A \\ A^H & 0 \end{bmatrix}$. -/
private theorem complexify_fromBlocks_zero (A : Matrix (Fin n) (Fin n) ℝ) :
    complexify (fromBlocks 0 A Aᵀ 0) = fromBlocks 0 (complexify A) (complexify A)ᴴ 0 := by
  ext (i | i) (j | j) <;> simp [complexify_apply]

private theorem inv_sqrt_two_mul_self : (√2)⁻¹ * (√2)⁻¹ = (2 : ℝ)⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]

/-- **§9.4.3** of [golub2013matrix], $\operatorname{sign}\left(\begin{bmatrix} 0 & A \\ A^T & 0
\end{bmatrix}\right)$. Let $A = U_A \Sigma_A V_A^T$ be an SVD of
$A \in \mathbb{R}^{n \times n}$, and let
$$Q = \frac{1}{\sqrt 2} \begin{bmatrix} U_A & 0 \\ 0 & V_A \end{bmatrix} \begin{bmatrix} I_n &
  I_n \\ I_n & -I_n \end{bmatrix}.$$
Then $Q$ is orthogonal,
$$Q^T \begin{bmatrix} 0 & A \\ A^T & 0 \end{bmatrix} Q = \begin{bmatrix} \Sigma_A & 0 \\ 0 &
  -\Sigma_A \end{bmatrix}, \qquad Q \begin{bmatrix} I_n & 0 \\ 0 & -I_n \end{bmatrix} Q^T =
  \begin{bmatrix} 0 & U \\ U^T & 0 \end{bmatrix},$$
where $U = U_A V_A^T$, and $A = UP$ with $P = V_A \Sigma_A V_A^T$ is a polar decomposition. If
$A$ is nonsingular, then "it follows that"
$$\operatorname{sign}\left(\begin{bmatrix} 0 & A \\ A^T & 0 \end{bmatrix}\right) =
  \begin{bmatrix} 0 & U \\ U^T & 0 \end{bmatrix}.$$

**Correction.** The source omits the hypothesis that $A$ is nonsingular, which the last identity
needs: a zero singular value of $A$ is a zero eigenvalue of
$\begin{bmatrix} 0 & A \\ A^T & 0 \end{bmatrix}$, where the sign function is not defined.

The SVD is `Matrix.IsSVD A U σ V`, where the Lean names `U` and `V` stand for $U_A$ and $V_A$.
The sign of a real matrix is the sign of its complexification `Matrix.complexify`. The proof
specializes `Matrix.matrixSign_hermitianDilation`. -/
theorem sign_block_polar {Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (h : IsSVD A U σ V)
    (hQ : Q = (√2)⁻¹ • (fromBlocks U 0 0 V * fromBlocks 1 1 1 (-1))) :
    Qᵀ * Q = 1 ∧
    Qᵀ * fromBlocks 0 A Aᵀ 0 * Q =
      fromBlocks (diagonal fun i : Fin n => σ i) 0 0 (-diagonal fun i : Fin n => σ i) ∧
    Q * fromBlocks 1 0 0 (-1) * Qᵀ = fromBlocks 0 (U * Vᵀ) (U * Vᵀ)ᵀ 0 ∧
    (IsUnit A → matrixSign (complexify (fromBlocks 0 A Aᵀ 0)) =
      complexify (fromBlocks 0 (U * Vᵀ) (U * Vᵀ)ᵀ 0)) ∧
    IsPolarDecomposition A (U * Vᵀ) (V * diagonal (fun i : Fin n => σ i) * Vᵀ) := by
  have hUU : Uᵀ * U = 1 := by
    have := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_left
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hVV : Vᵀ * V = 1 := by
    have := mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at this
  have hS : Uᵀ * A * V = diagonal fun i : Fin n => σ i := by
    have := h.star_mul_mul
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, rectDiagonal_eq_diagonal]
      at this
  have hS' : Vᵀ * Aᵀ * U = diagonal fun i : Fin n => σ i := by
    rw [← diagonal_transpose, ← hS, transpose_mul, transpose_mul, transpose_transpose,
      Matrix.mul_assoc]
  have hpol : IsPolarDecomposition A (U * Vᵀ) (V * diagonal (fun i : Fin n => σ i) * Vᵀ) := by
    have := h.isPolarDecomposition_of_square
    simp only [conjTranspose_eq_transpose_of_trivial] at this
    exact this
  set B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := fromBlocks U 0 0 V with hB
  set J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := fromBlocks 1 1 1 (-1) with hJ
  have hJt : Jᵀ = J := by simp [hJ, fromBlocks_transpose]
  have hJJ : J * J = (2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) := by
    rw [hJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
    simp only [Matrix.mul_one, Matrix.mul_neg, neg_neg, add_neg_cancel, smul_zero, two_smul]
  have hBB : Bᵀ * B = 1 := by
    rw [hB, fromBlocks_transpose, fromBlocks_multiply]
    simp [hUU, hVV]
  have hQQ : ∀ X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ,
      Qᵀ * X * Q = (2 : ℝ)⁻¹ • (J * (Bᵀ * X * B) * J) := fun X => by
    rw [hQ, transpose_smul, transpose_mul, hJt, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, inv_sqrt_two_mul_self]
    simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_, ?_, fun hA => ?_, hpol⟩
  · have := hQQ 1
    rwa [Matrix.mul_one, Matrix.mul_one, hBB, Matrix.mul_one, hJJ, smul_smul,
      inv_mul_cancel₀ two_ne_zero, one_smul] at this
  · have hM : Bᵀ * fromBlocks 0 A Aᵀ 0 * B =
        fromBlocks 0 (diagonal fun i : Fin n => σ i) (diagonal fun i : Fin n => σ i) 0 := by
      rw [hB, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
      simp [hS, hS']
    rw [hQQ, hM, hJ, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul]
    ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [hij] <;> ring
  · rw [hQ]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_sqrt_two_mul_self,
      transpose_mul, hJt]
    rw [hB, hJ]
    simp only [fromBlocks_multiply, fromBlocks_transpose, fromBlocks_smul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul,
      neg_neg, neg_zero, transpose_zero, transpose_transpose, add_neg_cancel, smul_zero]
    congr 1 <;> module
  · have hc := (isSVD_complexify h).isPolarDecomposition_of_square
    have hs := matrixSign_hermitianDilation ((isUnit_complexify_iff A).2 hA) hc
    simp only [hermitianDilation, conjTranspose_conjTranspose] at hs
    have e : complexify (U * Vᵀ) = complexify U * (complexify V)ᴴ := by
      rw [complexify_mul, ← conjTranspose_eq_transpose_of_trivial, complexify_conjTranspose]
    rw [complexify_fromBlocks_zero, complexify_fromBlocks_zero, hs, e]

end SignBlock

open scoped Matrix.Norms.Frobenius in
/-- **§9.4.3** of [golub2013matrix], the Li–Sun bound, corrected. Let $A = UP$ and
$\tilde A = \tilde U \tilde P$ be polar decompositions of
$A, \tilde A \in \mathbb{R}^{n \times n}$ with $\det A \cdot \det \tilde A > 0$. Then
$$\|U - \tilde U\|_F \le \frac{4 \|A - \tilde A\|_F}{\sigma_{n-1}(A) + \sigma_n(A) +
  \sigma_{n-1}(\tilde A) + \sigma_n(\tilde A)},$$
where $\sigma_{n-1}$ and $\sigma_n$ are the two smallest singular values.

**Correction.** The source states the bound for nonsingular $A$ and $\tilde A$. The bound is
false under this hypothesis alone: $A = \operatorname{diag}(1, \epsilon)$ and
$\tilde A = \operatorname{diag}(1, -\epsilon)$ with $0 < \epsilon < 1$ have $\|U - \tilde
U\|_F = 2 > 4 \cdot 2\epsilon / (2 + 2\epsilon)$. The statement assumes
$\det A \cdot \det \tilde A > 0$; the hypothesis $\|A - \tilde A\|_2 < \sigma_n(A) +
\sigma_n(\tilde A)$ of Li and Sun implies it.

**Typo.** The source dates the paper of Li and Sun "(2003)". It appeared in SIAM J. Matrix Anal.
Appl. 23 (2002).

The 1-based $\sigma_{n-1}$ and $\sigma_n$ are the 0-based `Matrix.sortedSingularValues (n - 2)`
and `Matrix.sortedSingularValues (n - 1)`; for $n \le 1$ the truncated subtraction makes both
indices $0$. The norms are Frobenius norms. The proof specializes
`Matrix.frobenius_norm_polar_sub_le`. -/
theorem li_sun {A Ã U Ũ P P' : Matrix (Fin n) (Fin n) ℝ} (h : Matrix.IsPolarDecomposition A U P)
    (h' : Matrix.IsPolarDecomposition Ã Ũ P') (hdet : 0 < A.det * Ã.det) :
    ‖U - Ũ‖ ≤ 4 * ‖A - Ã‖ / (A.sortedSingularValues (n - 2) + A.sortedSingularValues (n - 1) +
      Ã.sortedSingularValues (n - 2) + Ã.sortedSingularValues (n - 1)) :=
  Matrix.frobenius_norm_polar_sub_le h h' hdet

/-! ### §9.4.4 The matrix logarithm -/

/-- **§9.4.4** of [golub2013matrix], the real principal logarithm. Let
$A \in \mathbb{R}^{n \times n}$ be such that every real eigenvalue of $A$ is positive. Then
there is a unique $X \in \mathbb{R}^{n \times n}$ with $e^X = A$ and $\lambda(X) \subseteq \{z :
-\pi < \operatorname{Im} z < \pi\}$, the principal logarithm $\log(A)$. Moreover, every such
$X$, read in $\mathbb{C}^{n \times n}$, is the complex principal logarithm `Matrix.principalLog`
of $A$.

The eigenvalues of a real matrix are those of its image under the entrywise embedding of
$\mathbb{R}$ in $\mathbb{C}$. -/
theorem realLog_existsUnique {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal), μ.im = 0 → 0 < μ.re) :
    (∃! X : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp X = A ∧
      ∀ μ ∈ spectrum ℂ (X.map Complex.ofReal), |μ.im| < Real.pi) ∧
    ∀ X : Matrix (Fin n) (Fin n) ℝ, NormedSpace.exp X = A →
      (∀ μ ∈ spectrum ℂ (X.map Complex.ofReal), |μ.im| < Real.pi) →
        X.map Complex.ofReal = Matrix.principalLog (A.map Complex.ofReal) := by
  have hB : spectrum ℂ (A.map Complex.ofReal) ⊆ Complex.slitPlane := fun μ hμ => by
    rw [Complex.mem_slitPlane_iff]
    by_cases h : μ.im = 0
    · exact Or.inl (hA μ hμ h)
    · exact Or.inr h
  refine ⟨Matrix.existsUnique_real_exp_eq hB, fun X hX hXs => ?_⟩
  obtain ⟨L, -, hLuniq⟩ := Matrix.existsUnique_exp_eq_of_abs_im_lt hB
  have hexp : NormedSpace.exp (X.map Complex.ofReal) = A.map Complex.ofReal := by
    rw [← hX]
    exact (Matrix.complexify_exp X).symm
  rw [hLuniq _ ⟨hexp, hXs⟩, ← hLuniq _ (Matrix.exp_principalLog hB)]

open scoped Matrix.Norms.L2Operator in
/-- **§9.4.4** of [golub2013matrix], the Maclaurin approximants $M_q(A) = \sum_{k=1}^{q} (-1)^{k+1}
(A - I)^k / k$. Let $A \in \mathbb{C}^{n \times n}$ with $|\lambda - 1| < 1$ for every
eigenvalue $\lambda$, that is, $\rho(A - I) < 1$. Then $M_q(A) \to \log(A)$, that is,
$$\log(A) = \sum_{k=1}^{\infty} \frac{(-1)^{k+1}}{k} (A - I)^k,$$
and $\log(A)$ is Mathlib's series logarithm `NormedSpace.log A`.

Mathlib's logarithm is taken with the norm $\|\cdot\|_2$. -/
theorem log_maclaurin {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, ‖μ - 1‖ < 1) :
    HasSum (fun k : ℕ => ((-1) ^ k / (k + 1) : ℂ) • (A - 1) ^ (k + 1)) (Matrix.principalLog A) ∧
    Matrix.principalLog A = NormedSpace.log A :=
  ⟨Matrix.hasSum_principalLog hA,
    pfc_log_eq_normedSpace_log (Algebra.IsIntegral.isIntegral A) hA⟩

/-- **§9.4.4** of [golub2013matrix], the Gregory approximants $G_q(A) = -2 \sum_{k=0}^{q} ((I -
A)(I + A)^{-1})^{2k+1} / (2k + 1)$. Let $A \in \mathbb{C}^{n \times n}$ have only eigenvalues
with positive real part. Then $G_q(A) \to \log(A)$, that is,
$$\log(A) = -2 \sum_{k=0}^{\infty} \frac{1}{2k + 1} \big((I - A)(I + A)^{-1}\big)^{2k+1}.$$
-/
theorem log_gregory {A : Matrix (Fin n) (Fin n) ℂ} (hA : ∀ μ ∈ spectrum ℂ A, 0 < μ.re) :
    HasSum (fun k : ℕ => (-2 / (2 * k + 1) : ℂ) • ((1 - A) * (1 + A)⁻¹) ^ (2 * k + 1))
      (Matrix.principalLog A) :=
  Matrix.hasSum_principalLog_gregory hA

/-- **§9.4.4** of [golub2013matrix], the $(3, 3)$ Padé approximant of $\log(1 + x)$. Let
$$r_{33}(x) = \frac{N(x)}{D(x)}, \qquad N(x) = 60x + 60x^2 + 11x^3, \qquad D(x) = 60 + 90x +
  36x^2 + 3x^3.$$
Then $D$ does not vanish near $x = 0$, so $r_{33}$ is defined there, and
$$r_{33}(x) - \log(1 + x) = O(x^7) \quad \text{as } x \to 0 \text{ in } \mathbb{C}.$$

The source writes $N$ and $D$ at $x = A - I$. -/
theorem log_pade_33 :
    (∀ᶠ x in 𝓝 (0 : ℂ), (60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3 : ℂ) ≠ 0) ∧
    (fun x : ℂ => (60 * x + 60 * x ^ 2 + 11 * x ^ 3) / (60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3) -
      Complex.log (1 + x)) =O[𝓝 0] fun x => x ^ 7 := by
  set D : ℂ → ℂ := fun x => 60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3
  set P : ℂ → ℂ := fun x => -171 / 20 - 27 / 5 * x - 1 / 2 * x ^ 2
  set R : ℂ → ℂ := fun x => Complex.log (1 + x) - Complex.logTaylor 7 x
  have hD : Continuous D := by fun_prop
  have hD0 : D 0 = 60 := by simp [D]
  have hDne : ∀ᶠ x in 𝓝 (0 : ℂ), D x ≠ 0 :=
    hD.continuousAt.eventually_ne (by rw [hD0]; norm_num)
  refine ⟨hDne, ?_⟩
  -- the polynomial part: `D T₆ - N = x⁷ P`
  have hpoly : ∀ x : ℂ, D x * Complex.logTaylor 7 x - (60 * x + 60 * x ^ 2 + 11 * x ^ 3) =
      x ^ 7 * P x := fun x => by
    simp only [D, P, Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  -- the remainder is `O(x⁷)`
  have hR : R =O[𝓝 0] fun x => x ^ 7 := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    have hb := Complex.norm_log_sub_logTaylor_le 6 (hx.trans (by norm_num))
    have h1 : (1 - ‖x‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc ‖R x‖ ≤ ‖x‖ ^ 7 * (1 - ‖x‖)⁻¹ / (6 + 1) := hb
      _ ≤ ‖x‖ ^ 7 * 2 / 1 := by gcongr; norm_num
      _ = 2 * ‖x ^ 7‖ := by rw [norm_pow]; ring
  have hinvD : (fun x => (D x)⁻¹) =O[𝓝 0] fun _ => (1 : ℂ) :=
    ((hD.continuousAt.inv₀ (by rw [hD0]; norm_num)).tendsto).isBigO_one ℂ
  have hPb : P =O[𝓝 0] fun _ => (1 : ℂ) :=
    ((show Continuous P by fun_prop).continuousAt.tendsto).isBigO_one ℂ
  have hmain : (fun x => -(x ^ 7 * P x) * (D x)⁻¹ - R x) =O[𝓝 0] fun x => x ^ 7 := by
    refine IsBigO.sub ?_ hR
    have := ((isBigO_refl (fun x : ℂ => x ^ 7) (𝓝 0)).mul hPb).mul hinvD
    simpa only [mul_one, neg_mul] using this.neg_left
  refine hmain.congr' ?_ EventuallyEq.rfl
  filter_upwards [hDne] with x hx
  have hx' : (60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3 : ℂ) ≠ 0 := hx
  have hDD : (60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3 : ℂ) *
      (60 + 90 * x + 36 * x ^ 2 + 3 * x ^ 3)⁻¹ = 1 := mul_inv_cancel₀ hx'
  rw [← hpoly x]
  simp only [R, D]
  rw [div_eq_mul_inv]
  linear_combination (-Complex.logTaylor 7 x) * hDD

/-- **§9.4.4** of [golub2013matrix], the identity behind inverse scaling and squaring. Let
$A \in \mathbb{C}^{n \times n}$ have no eigenvalue on $(-\infty, 0]$, and let $A_0 = A$ and
$A_k = A_{k-1}^{1/2}$. Then for every $k$
$$\log(A) = 2^k \log(A_k).$$
-/
theorem log_inverse_scaling {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : spectrum ℂ A ⊆ Complex.slitPlane) (k : ℕ) :
    Matrix.principalLog A = (2 ^ k : ℂ) • Matrix.principalLog (Matrix.principalSqrt^[k] A) :=
  Matrix.principalLog_eq_two_pow_smul hA k

end GolubVanLoan.Chapter09
