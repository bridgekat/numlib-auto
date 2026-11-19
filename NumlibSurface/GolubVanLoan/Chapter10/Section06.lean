/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.JacobiDavidson
import Numlib.Eigen.SymmetricPencil
import NumlibSurface.GolubVanLoan.Chapter01.Section04
import NumlibSurface.GolubVanLoan.Chapter10.Section01

/-!
# Golub and Van Loan, Section 10.6: Jacobi–Davidson and related methods

This module formalizes §10.6 of [golub2013matrix], which treats methods that improve an approximate
eigenpair $(x_c, \lambda_c)$ of $A \in \mathbb{R}^{n \times n}$ by an approximate Newton step. The
Newton step for the eigenvalue equation $Ax = \lambda x$ with the normalization $w^T x = 1$ is the
bordered system (10.6.5); its closed-form solution (10.6.7) and the approximate version (10.6.10),
which replaces $A$ by an approximation $M$, follow. For the bordered matrix
$A = [\alpha\ c^T; c\ A_1]$ of (10.6.11) and $w = e_1$, the Newton step reduces to the Jacobi
orthogonal component correction (JOCC) (10.6.13)–(10.6.15). Davidson's method (10.6.16) and the
Jacobi–Davidson framework of §10.6.4 expand an orthonormal basis $V_k$ by a correction vector and
take a Ritz pair of $V_k^T A V_k$. Jacobi–Davidson takes the correction from the projected equation
(10.6.19), which is the Newton step (10.6.17)–(10.6.18) for the normalization $x^T x = 1$. The
module ends with the trace-min principle of §10.6.5.

The Newton systems are proved from the eigenpair residuals and their derivatives in
`Numlib.Eigen.JacobiDavidson`, the Ritz pairs come from `Numlib.Eigen.RayleighRitz`, and the
trace-min principle specializes `Numlib.Eigen.SymmetricPencil`.

## Main definitions

* Equation (10.6.11), `GolubVanLoan.Chapter10.borderedMatrix`: the bordered matrix
  $[\alpha\ c^T; c\ A_1]$.
* Equation (10.6.14), `GolubVanLoan.Chapter10.joccIteration`: the JOCC iteration, as a program.
* Equation (10.6.16), `GolubVanLoan.Chapter10.davidson`: Davidson's method, as a program.
* Equation (10.6.19), `GolubVanLoan.Chapter10.IsJDCorrection`: the Jacobi–Davidson correction
  equation.
* Section 10.6.4, `GolubVanLoan.Chapter10.jacobiDavidson`: the Jacobi–Davidson framework, as a
  program.

## Main results

* Equation (10.6.1), `GolubVanLoan.Chapter10.equation_10_6_1`: the exact correction of an eigenpair
  satisfies $(A - \lambda_c I)\delta x - \delta l\, x_c = -r_c + \delta l\, \delta x$.
* Equation (10.6.4), `GolubVanLoan.Chapter10.equation_10_6_4`: the normalization $w^T x = 1$ forces
  $w^T \delta x = 0$.
* Equation (10.6.5), `GolubVanLoan.Chapter10.equation_10_6_5`: the bordered system is the Newton
  equation of $F(x, \lambda) = (Ax - \lambda x, w^T x - 1)$.
* Equations (10.6.6)–(10.6.7), `GolubVanLoan.Chapter10.equation_10_6_7`: the closed-form solution of
  the bordered system.
* Equations (10.6.8)–(10.6.10), `GolubVanLoan.Chapter10.equation_10_6_10`: the closed-form solution
  of the approximate Newton system with $M$ in place of $A$.
* Equation (10.6.13), `GolubVanLoan.Chapter10.equation_10_6_13`: for the bordered matrix and
  $w = e_1$, the Newton system reduces to a system in $(\delta z, \delta l)$, and a splitting
  $A_1 = M_1 - N_1$ rearranges it.
* Equation (10.6.14), `GolubVanLoan.Chapter10.equation_10_6_14`: the exact JOCC iterates satisfy the
  update equations, and the loop stops at the tolerance or after `fuel` passes.
* Equation (10.6.15), `GolubVanLoan.Chapter10.equation_10_6_15`: the residual of $x_k = [1; z_k]$
  has first component zero.
* Equation (10.6.16), `GolubVanLoan.Chapter10.equation_10_6_16`: in exact arithmetic Davidson's
  method keeps an orthonormal basis and produces Ritz pairs whose residuals are orthogonal to the
  basis.
* Equation (10.6.17), `GolubVanLoan.Chapter10.equation_10_6_17`: the bordered system with $w = x_c$
  is the Newton equation of $F(x, \lambda) = (Ax - \lambda x, (x^T x - 1)/2)$.
* Equation (10.6.18), `GolubVanLoan.Chapter10.equation_10_6_18`: for $\lambda_c = x_c^T A x_c$, the
  bordered system (10.6.17) is equivalent to the projected equation.
* Section 10.6.4, `GolubVanLoan.Chapter10.jacobiDavidson_spec`: in exact arithmetic the
  Jacobi–Davidson framework has the properties of Davidson's method, and its corrections are
  orthogonal to the current Ritz vector.
* Section 10.6.5, `GolubVanLoan.Chapter10.isLeast_trace_transpose_mul_mul`: the trace-min principle
  $\min\{\operatorname{tr}(V^T A V) : V^T B V = I_k\} = \mu_1 + \cdots + \mu_k$.

## Conventions

* The source's $\lambda_c$ is the Lean variable `μ`, and its correction $\delta l$ of the eigenvalue
  is `δμ`. In (10.6.13) the correction is `δl`, and `δμ` is the first entry of $\delta x$.
* The bordered matrix $[\alpha\ c^T; c\ A_1]$ is `GolubVanLoan.Chapter10.borderedMatrix α c A₁ :
  Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ`, and the vector $[t; z]$ is `Fin.cons t z`.
* The indices of the iterations are 0-based: index $j$ of a state is the source's $j + 1$.

## Implementation notes

* Vectors are `Fin n → ℝ` where only algebra enters, and `EuclideanSpace ℝ (Fin n)` where
  derivatives and norms enter. The eigenpair residuals are `ContinuousLinearMap.eigenpairResidual`
  (normalization $w^T x = 1$) and `ContinuousLinearMap.eigenpairResidualSphere` (normalization
  $x^T x = 1$) of `Matrix.toEuclideanCLM A`.
* Davidson's method and the Jacobi–Davidson framework are one program,
  `GolubVanLoan.Chapter10.subspaceExpansion`, whose arguments are the correction step and the choice
  of Ritz pair. `GolubVanLoan.Chapter10.davidson` passes the diagonal solve of (10.6.16) and the
  start $e_1$. `GolubVanLoan.Chapter10.jacobiDavidson` passes a solver of (10.6.19) that the caller
  supplies, for example an iterative method of Chapter 11 (algorithm convention 5), and any unit
  start.
* The basis $V_k$ is the family `v 0, …, v (k - 1)` of the state; `GolubVanLoan.Chapter10.basisCols`
  gives it as a matrix. Its range $\operatorname{ran} V_k$ is a `Submodule.span` in
  `EuclideanSpace ℝ (Fin n)`.
* Each `while` loop runs at most `fuel` passes (algorithm convention 3).

## Deviations from the source

* **Equations (10.6.4)–(10.6.5)** (correction). The linear constraint fixes $w^Tx=1$. Taking
  $w=x_c$ does not force the next vector to have unit norm. See
  `GolubVanLoan.Chapter10.equation_10_6_4`.
* **Equations (10.6.6)–(10.6.10)** (reading). The formulas assume the shifted matrix and scalar
  denominator used in them are invertible. See `GolubVanLoan.Chapter10.equation_10_6_7` and
  `GolubVanLoan.Chapter10.equation_10_6_10`.
* **Davidson and Jacobi–Davidson correctness** (limitation). Five specifications ask for unit
  Ritz vectors in every projected dimension, including dimension zero, where none exist. The
  iteration requests Ritz pairs only in positive dimension. See
  `GolubVanLoan.Chapter10.subspaceExpansion_spec`, `GolubVanLoan.Chapter10.equation_10_6_16`,
  `GolubVanLoan.Chapter10.subspaceExpansion_ritzValue_mono`,
  `GolubVanLoan.Chapter10.davidson_ritzValue_mono`, and
  `GolubVanLoan.Chapter10.jacobiDavidson_spec`.
* **Equation (10.6.13)** (typo). The source prints $\alpha + + c^T z_c$ in the right-hand side; the
  intended term is $\alpha + c^T z_c$. See `GolubVanLoan.Chapter10.equation_10_6_13`.
* **Trace-min principle, §10.6.5** (correction). The source says that every minimizer
  $V_{\mathrm{opt}}$ has $V_{\mathrm{opt}}^T A V_{\mathrm{opt}}$ diagonal; this holds only for some
  minimizer. See `GolubVanLoan.Chapter10.isLeast_trace_transpose_mul_mul`.

## Not formalized

* **Convergence of the methods.** The source makes no convergence claim.
* **The trace-min iteration of §10.6.5.** The source sketches it without a claim.
* **Restarting the Davidson and Jacobi–Davidson loops.** The source only mentions it.
-/

open scoped Matrix InnerProductSpace
open Krylov
open GolubVanLoan.Chapter01

namespace GolubVanLoan.Chapter10

variable {n : ℕ}

/-! ### The approximate Newton framework (§10.6.1) -/

/-- **Equation (10.6.1)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$,
$x_c, \delta x \in \mathbb{R}^n$ and $\lambda_c, \delta l \in \mathbb{R}$. If $A(x_c + \delta
x) = (\lambda_c + \delta l)(x_c + \delta x)$, then
$$(A - \lambda_c I)\,\delta x - \delta l\, x_c = -r_c + \delta l\, \delta x, \qquad r_c = A
  x_c - \lambda_c x_c.$$
-/
theorem equation_10_6_1 (A : Matrix (Fin n) (Fin n) ℝ) {x δx : Fin n → ℝ} {μ δμ : ℝ}
    (h : A *ᵥ (x + δx) = (μ + δμ) • (x + δx)) :
    (A - μ • 1) *ᵥ δx - δμ • x = -(A *ᵥ x - μ • x) + δμ • δx := by
  rw [Matrix.mulVec_add, add_smul, smul_add, smul_add] at h
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h' : A *ᵥ δx = μ • x + μ • δx + (δμ • x + δμ • δx) - A *ᵥ x := eq_sub_of_add_eq' h
  rw [h']
  abel

/-- **Equation (10.6.4)** of [golub2013matrix]. Let $w, x_c, \delta x \in \mathbb{R}^n$, and let
$x_+ = x_c + \delta x$ as in (10.6.3). If $w^T x_+ = 1$ and $w^T x_c = 1$, then
$w^T \delta x = 0$.

**Correction.** The source says that choosing $w=x_c$ forces the next vector to have unit norm.
If $x_c$ has unit norm and $x_c^T\delta x=0$, the new squared norm is $1+\|\delta x\|_2^2$. The
linear constraint preserves $w^Tx=1$. -/
theorem equation_10_6_4 {w x δx : Fin n → ℝ} (hplus : w ⬝ᵥ (x + δx) = 1) (hc : w ⬝ᵥ x = 1) :
    w ⬝ᵥ δx = 0 := by
  rw [dotProduct_add, hc] at hplus
  linarith

/-- **Equation (10.6.5)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$, let
$w, x_c \in \mathbb{R}^n$ with $w^T x_c = 1$, and let $\lambda_c \in \mathbb{R}$. Let
$F(x, \lambda) = (Ax - \lambda x, w^T x - 1)$ on $\mathbb{R}^n \times \mathbb{R}$. Then
$(\delta x, \delta l)$ satisfies the Newton equation $F'(x_c, \lambda_c)(\delta x, \delta l) =
-F(x_c, \lambda_c)$ if and only if it solves the bordered system
$$\begin{bmatrix} A - \lambda_c I & -x_c \\ w^T & 0 \end{bmatrix}
  \begin{bmatrix} \delta x \\ \delta l \end{bmatrix} = -\begin{bmatrix} r_c \\ 0 \end{bmatrix},
  \qquad r_c = A x_c - \lambda_c x_c.$$

The map $F$ is `ContinuousLinearMap.eigenpairResidual` of `Matrix.toEuclideanCLM A` with the
functional $x \mapsto w^T x$ (`innerSL ℝ w`), and $F'$ is the Fréchet derivative `fderiv`. The
vectors are in `EuclideanSpace ℝ (Fin n)`. The proof uses
`ContinuousLinearMap.hasFDerivAt_eigenpairResidual`. -/
theorem equation_10_6_5 (A : Matrix (Fin n) (Fin n) ℝ) {w x : EuclideanSpace ℝ (Fin n)}
    (hwx : ⟪w, x⟫_ℝ = 1) (μ : ℝ) (δx : EuclideanSpace ℝ (Fin n)) (δμ : ℝ) :
    let F := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).eigenpairResidual (innerSL ℝ w)
    fderiv ℝ F (x, μ) (δx, δμ) = -F (x, μ) ↔
      (Matrix.toEuclideanLin A δx - μ • δx - δμ • x = -(Matrix.toEuclideanLin A x - μ • x) ∧
        ⟪w, δx⟫_ℝ = 0) := by
  intro F
  rw [((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).hasFDerivAt_eigenpairResidual
    (innerSL ℝ w) x μ).fderiv]
  simp only [F, ContinuousLinearMap.eigenpairResidual, ContinuousLinearMap.prod_apply,
    sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_apply, ContinuousLinearMap.id_apply, Prod.neg_mk, Prod.mk.injEq,
    hwx, sub_self, neg_zero, sub_apply]
  rfl

/-- For a nonsingular matrix $M$, the ring inverse of the linear map `Matrix.toLin' M` is
`Matrix.toLin'` of $M^{-1}$. -/
private theorem ringInverse_toLin' {M : Matrix (Fin n) (Fin n) ℝ} (hM : IsUnit M) :
    Ring.inverse (Matrix.toLin' M) = Matrix.toLin' M⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det M).1 hM
  have h1 : Matrix.toLin' M * Matrix.toLin' M⁻¹ = 1 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hd,
      Matrix.toLin'_one, Module.End.one_eq_id]
  have h2 : Matrix.toLin' M⁻¹ * Matrix.toLin' M = 1 := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hd,
      Matrix.toLin'_one, Module.End.one_eq_id]
  have hu : IsUnit (Matrix.toLin' M) := ⟨⟨_, _, h1, h2⟩, rfl⟩
  have := (Ring.inverse_mul_eq_iff_eq_mul _ 1 (Matrix.toLin' M⁻¹) hu).2 h1.symm
  rwa [mul_one] at this

/-- If $M - \lambda I$ is nonsingular and $w^T (M - \lambda I)^{-1} x \neq 0$, then
$(M - \lambda I)\delta x - \delta l\, x = -r$ and $w^T \delta x = 0$ hold if and only if
$\delta l$ and $\delta x$ are given by the formulas of (10.6.7) with $M$ in place of $A$.

**Reading.** General residual vector with invertible shifted block and nonzero scalar denominator.
-/
private theorem bordered_iff {M : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ} (hM : IsUnit (M - μ • 1))
    {w x : Fin n → ℝ} (hx : w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ x) ≠ 0) (r δx : Fin n → ℝ) (δμ : ℝ) :
    ((M - μ • 1) *ᵥ δx - δμ • x = -r ∧ w ⬝ᵥ δx = 0) ↔
      (δμ = (w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ r)) / (w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ x)) ∧
        δx = -((M - μ • 1)⁻¹ *ᵥ (r - δμ • x))) := by
  have hT : Matrix.toLin' M - μ • 1 = Matrix.toLin' (M - μ • 1) := by
    rw [map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
  have hU : IsUnit (Matrix.toLin' M - μ • 1) := by
    rw [hT]
    obtain ⟨u, hu⟩ := hM
    exact ⟨⟨Matrix.toLin' u, Matrix.toLin' ↑u⁻¹, by
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, u.mul_inv, Matrix.toLin'_one,
        Module.End.one_eq_id], by
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, u.inv_mul, Matrix.toLin'_one,
        Module.End.one_eq_id]⟩, by rw [← hu]⟩
  have hR : Ring.inverse (Matrix.toLin' M - μ • 1) = Matrix.toLin' (M - μ • 1)⁻¹ := by
    rw [hT, ringInverse_toLin' hM]
  have h := JacobiDavidson.newtonCorrection_eq hU (dotProductBilin ℝ ℝ w) (x := x)
    (by rw [hR]; simpa using hx) r δx δμ
  rw [hR, hT] at h
  simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using h

/-- **Equations (10.6.6)–(10.6.7)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$\lambda_c \in \mathbb{R}$ with $A - \lambda_c I$ nonsingular, let $w, x_c \in \mathbb{R}^n$
with $w^T (A - \lambda_c I)^{-1} x_c \neq 0$, and let $r_c = A x_c - \lambda_c x_c$. Then
$(\delta x, \delta l)$ solves the bordered system (10.6.5), that is, $(A - \lambda_c I)\delta
x - \delta l\, x_c = -r_c$ and $w^T \delta x = 0$, if and only if
$$\delta l = \frac{w^T (A - \lambda_c I)^{-1} r_c}{w^T (A - \lambda_c I)^{-1} x_c}, \qquad
  \delta x = -(A - \lambda_c I)^{-1}(r_c - \delta l\, x_c).$$
In particular the system has exactly one solution.

The proof specializes `JacobiDavidson.newtonCorrection_eq`.

**Reading.** The two quotient formulas apply when the shifted matrix is nonsingular and the
scalar denominator is nonzero. -/
theorem equation_10_6_7 {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ} (hA : IsUnit (A - μ • 1))
    {w x : Fin n → ℝ} (hx : w ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ x) ≠ 0) (δx : Fin n → ℝ) (δμ : ℝ) :
    ((A - μ • 1) *ᵥ δx - δμ • x = -(A *ᵥ x - μ • x) ∧ w ⬝ᵥ δx = 0) ↔
      (δμ = (w ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ (A *ᵥ x - μ • x))) / (w ⬝ᵥ ((A - μ • 1)⁻¹ *ᵥ x)) ∧
        δx = -((A - μ • 1)⁻¹ *ᵥ ((A *ᵥ x - μ • x) - δμ • x))) :=
  bordered_iff hA hx _ δx δμ

/-- **Equations (10.6.8)–(10.6.10)** of [golub2013matrix], the approximate Newton correction. Let
$A, M \in \mathbb{R}^{n \times n}$ and $\lambda_c \in \mathbb{R}$ with $M - \lambda_c I$
nonsingular, let $w, x_c \in \mathbb{R}^n$ with $w^T (M - \lambda_c I)^{-1} x_c \neq 0$, and let
$r_c = A x_c - \lambda_c x_c$. Then $(\delta x, \delta l)$ solves the system (10.6.8), $(M -
\lambda_c I)\delta x - \delta l\, x_c = -r_c$ and $w^T \delta x = 0$, if and only if
$$\delta l = \frac{w^T (M - \lambda_c I)^{-1} r_c}{w^T (M - \lambda_c I)^{-1} x_c}, \qquad
  \delta x = -(M - \lambda_c I)^{-1}(r_c - \delta l\, x_c).$$

The matrix $M$ approximates $A$. With $N = M - A$, the system (10.6.8) is the bordered system
(10.6.5) with $M$ in the operator block and the term $N \delta x$ dropped; the right-hand side
keeps the residual $r_c$ of $A$. The proof specializes `JacobiDavidson.newtonCorrection_eq`.

**Reading.** The inverse-based formulas require a nonsingular shifted $M$ and a nonzero scalar
denominator. The residual is computed with $A$. -/
theorem equation_10_6_10 (A : Matrix (Fin n) (Fin n) ℝ) {M : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (hM : IsUnit (M - μ • 1)) {w x : Fin n → ℝ} (hx : w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ x) ≠ 0)
    (δx : Fin n → ℝ) (δμ : ℝ) :
    ((M - μ • 1) *ᵥ δx - δμ • x = -(A *ᵥ x - μ • x) ∧ w ⬝ᵥ δx = 0) ↔
      (δμ = (w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ (A *ᵥ x - μ • x))) / (w ⬝ᵥ ((M - μ • 1)⁻¹ *ᵥ x)) ∧
        δx = -((M - μ • 1)⁻¹ *ᵥ ((A *ᵥ x - μ • x) - δμ • x))) :=
  bordered_iff hM hx _ δx δμ

/-! ### The Jacobi orthogonal component correction (§10.6.2) -/

/-- **Equation (10.6.11)** of [golub2013matrix]. For $\alpha \in \mathbb{R}$, $c \in \mathbb{R}^n$
and $A_1 \in \mathbb{R}^{n \times n}$, the **bordered matrix** is
$$A = \begin{bmatrix} \alpha & c^T \\ c & A_1 \end{bmatrix} \in \mathbb{R}^{(n+1) \times
  (n+1)}.$$
The first row and column have the index `0` of `Fin (n + 1)`.

**Reading.** Same border arrangement, defined for arbitrary trailing blocks.
-/
def borderedMatrix (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => Fin.cases (Fin.cases α c j) (fun i' => Fin.cases (c i') (A₁ i') j) i

/-- For the bordered matrix $A = [\alpha\ c^T; c\ A_1]$ of (10.6.11), $t \in \mathbb{R}$ and
$z \in \mathbb{R}^n$,
$$A \begin{bmatrix} t \\ z \end{bmatrix} = \begin{bmatrix} \alpha t + c^T z \\ t c + A_1 z
  \end{bmatrix}.$$
-/
theorem borderedMatrix_mulVec_cons (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (z : Fin n → ℝ) :
    borderedMatrix α c A₁ *ᵥ Fin.cons t z = Fin.cons (α * t + c ⬝ᵥ z) (t • c + A₁ *ᵥ z) := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [borderedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [borderedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

/-- **Equation (10.6.15)** of [golub2013matrix]. Let $A = [\alpha\ c^T; c\ A_1]$ be the bordered
matrix (10.6.11), let $z_k \in \mathbb{R}^n$, and let $\lambda_k = \alpha + c^T z_k$ and
$x_k = [1; z_k]$. Then the residual $r_k = (A - \lambda_k I) x_k$ has first component zero:
$$r_k = \begin{bmatrix} 0 \\ (A_1 - \lambda_k I) z_k + c \end{bmatrix}.$$

**Generalization.** Same zero-first residual, extends to all trailing blocks.
-/
theorem equation_10_6_15 (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ) :
    (borderedMatrix α c A₁ - (α + c ⬝ᵥ z) • 1) *ᵥ Fin.cons 1 z =
      Fin.cons 0 ((A₁ - (α + c ⬝ᵥ z) • 1) *ᵥ z + c) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    borderedMatrix_mulVec_cons, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp only [Pi.sub_apply, Pi.smul_apply, Fin.cons_succ, Pi.add_apply, smul_eq_mul]
    ring

/-! ### The Jacobi–Davidson correction (§10.6.4) -/

/-- **Equation (10.6.17)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$, let
$x_c \in \mathbb{R}^n$ with $\|x_c\|_2 = 1$, and let $\lambda_c \in \mathbb{R}$. Let $F(x,
\lambda) = (Ax - \lambda x, (x^T x - 1)/2)$ on $\mathbb{R}^n \times \mathbb{R}$. Then
$(\delta x, \delta l)$ satisfies the Newton equation $F'(x_c, \lambda_c)(\delta x, \delta l) =
-F(x_c, \lambda_c)$ if and only if it solves the bordered system
$$\begin{bmatrix} A - \lambda_c I & -x_c \\ x_c^T & 0 \end{bmatrix}
  \begin{bmatrix} \delta x \\ \delta l \end{bmatrix} = -\begin{bmatrix} r_c \\ 0 \end{bmatrix},
  \qquad r_c = A x_c - \lambda_c x_c.$$

The map $F$ is `ContinuousLinearMap.eigenpairResidualSphere` of `Matrix.toEuclideanCLM A`, and
$F'$ is the Fréchet derivative `fderiv`. The proof uses
`ContinuousLinearMap.hasFDerivAt_eigenpairResidualSphere`. -/
theorem equation_10_6_17 (A : Matrix (Fin n) (Fin n) ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ = 1) (μ : ℝ) (δx : EuclideanSpace ℝ (Fin n)) (δμ : ℝ) :
    let F := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).eigenpairResidualSphere
    fderiv ℝ F (x, μ) (δx, δμ) = -F (x, μ) ↔
      (Matrix.toEuclideanLin A δx - μ • δx - δμ • x = -(Matrix.toEuclideanLin A x - μ • x) ∧
        ⟪x, δx⟫_ℝ = 0) := by
  intro F
  rw [((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A).hasFDerivAt_eigenpairResidualSphere
    x μ).fderiv]
  simp only [F, ContinuousLinearMap.eigenpairResidualSphere, ContinuousLinearMap.prod_apply,
    sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_apply, ContinuousLinearMap.id_apply, Prod.neg_mk, Prod.mk.injEq,
    hx, one_pow, sub_self, zero_div, neg_zero]
  rfl

/-- **Equation (10.6.18)** of [golub2013matrix]. Let $A \in \mathbb{R}^{n \times n}$ and
$x_c \in \mathbb{R}^n$ with $\|x_c\|_2 = 1$, and let $\lambda_c = x_c^T A x_c$ and
$r_c = A x_c - \lambda_c x_c$. Then $(\delta x, \delta l)$ solves the bordered system (10.6.17),
that is, $(A - \lambda_c I)\delta x - \delta l\, x_c = -r_c$ and $x_c^T \delta x = 0$, if and
only if $x_c^T \delta x = 0$,
$$(I - x_c x_c^T)(A - \lambda_c I)(I - x_c x_c^T)\, \delta x = -r_c,$$
and $\delta l = x_c^T (A - \lambda_c I)\, \delta x$.

The source derives the forward implication. The converse is what the source uses when it obtains
the correction by solving the projected system. The matrix $I - x_c x_c^T$ is the orthogonal
projection onto the orthogonal complement of $x_c$, `(ℝ ∙ x)ᗮ.starProjection`. The proof
specializes `JacobiDavidson.newtonStep_iff_projected`. -/
theorem equation_10_6_18 (A : Matrix (Fin n) (Fin n) ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ = 1) (δx : EuclideanSpace ℝ (Fin n)) (δμ : ℝ) :
    let T := Matrix.toEuclideanLin A
    let μ := ⟪x, T x⟫_ℝ
    let P := (ℝ ∙ x)ᗮ.starProjection
    ((T - μ • 1) δx - δμ • x = -(T x - μ • x) ∧ ⟪x, δx⟫_ℝ = 0) ↔
      (⟪x, δx⟫_ℝ = 0 ∧ P ((T - μ • 1) (P δx)) = -(T x - μ • x) ∧
        δμ = ⟪x, (T - μ • 1) δx⟫_ℝ) := by
  intro T μ P
  have hxx : ⟪x, x⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have hr : ⟪x, T x - μ • x⟫_ℝ = 0 := by
    rw [inner_sub_right, real_inner_smul_right, hxx, mul_one, sub_self]
  -- the multiplier of any solution of the bordered system
  have hmult : ∀ δμ', (T - μ • 1) δx - δμ' • x = -(T x - μ • x) →
      δμ' = ⟪x, (T - μ • 1) δx⟫_ℝ := fun δμ' h => by
    have := congrArg (fun y => ⟪x, y⟫_ℝ) h
    simp only [inner_sub_right, real_inner_smul_right, hxx, mul_one, inner_neg_right, hr,
      neg_zero] at this
    linarith
  have hb := JacobiDavidson.newtonStep_iff_projected T hx δx
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨h2', h3⟩ := hb.1 ⟨δμ, h1, h2⟩
    exact ⟨h2', h3, hmult δμ h1⟩
  · rintro ⟨h2, h3, h4⟩
    obtain ⟨δμ', h1', -⟩ := hb.2 ⟨h2, h3⟩
    refine ⟨?_, h2⟩
    rwa [h4, ← hmult δμ' h1']

/-- **Equation (10.6.19)** of [golub2013matrix], the Jacobi–Davidson correction equation. Let
$M \in \mathbb{R}^{n \times n}$ be the preconditioner, let $x_k, r_k \in \mathbb{R}^n$ and let
$\lambda_k \in \mathbb{R}$. A vector $\delta v \in \mathbb{R}^n$ is a **Jacobi–Davidson
correction** for $x_k$, $\lambda_k$, $r_k$ and $M$ if $x_k^T \delta v = 0$ and
$$(I - x_k x_k^T)(M - \lambda_k I)(I - x_k x_k^T)\, \delta v = -r_k.$$

The factor $I - x_k x_k^T$ is encoded as the orthogonal projection onto the orthogonal
complement of $x_k$, `(ℝ ∙ x)ᗮ.starProjection`. The two agree when $\|x_k\|_2 = 1$, which is the
case in which the source uses the equation; the definition does not assume it. The matrix $M$
acts through `Matrix.toEuclideanLin`.

**Reading.** The source's projector $I-xx^T$ equals the orthogonal projection used here when
$x$ is a unit vector. The definition uses the true orthogonal projection for other inputs. -/
def IsJDCorrection (M : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) (μ : ℝ)
    (r δv : EuclideanSpace ℝ (Fin n)) : Prop :=
  ⟪x, δv⟫_ℝ = 0 ∧
    (ℝ ∙ x)ᗮ.starProjection ((Matrix.toEuclideanLin M - μ • 1)
      ((ℝ ∙ x)ᗮ.starProjection δv)) = -r

/-- Let $A \in \mathbb{R}^{n \times n}$ and $x \in \mathbb{R}^n$ with $\|x\|_2 = 1$, and let
$\lambda = x^T A x$ and $r = Ax - \lambda x$. Then $\delta v$ is a Jacobi–Davidson correction
(10.6.19) for $x$, $\lambda$, $r$ and $M = A$ if and only if
$(\delta v, x^T (A - \lambda I) \delta v)$ solves the bordered system (10.6.17). -/
theorem isJDCorrection_self_iff (A : Matrix (Fin n) (Fin n) ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ = 1) (δv : EuclideanSpace ℝ (Fin n)) :
    IsJDCorrection A x ⟪x, Matrix.toEuclideanLin A x⟫_ℝ
        (Matrix.toEuclideanLin A x - ⟪x, Matrix.toEuclideanLin A x⟫_ℝ • x) δv ↔
      ((Matrix.toEuclideanLin A - ⟪x, Matrix.toEuclideanLin A x⟫_ℝ • 1) δv -
          ⟪x, (Matrix.toEuclideanLin A - ⟪x, Matrix.toEuclideanLin A x⟫_ℝ • 1) δv⟫_ℝ • x =
        -(Matrix.toEuclideanLin A x - ⟪x, Matrix.toEuclideanLin A x⟫_ℝ • x) ∧
        ⟪x, δv⟫_ℝ = 0) := by
  have h := equation_10_6_18 A hx δv
    ⟪x, (Matrix.toEuclideanLin A - ⟪x, Matrix.toEuclideanLin A x⟫_ℝ • 1) δv⟫_ℝ
  exact ⟨fun h' => h.2 ⟨h'.1, h'.2, rfl⟩, fun h' => ⟨(h.1 h').1, (h.1 h').2.1⟩⟩

/-! ### The Jacobi orthogonal component correction, continued (§10.6.2) -/

/-- For the bordered matrix $A = [\alpha\ c^T; c\ A_1]$ of (10.6.11), $\mu, t \in \mathbb{R}$ and
$z \in \mathbb{R}^n$,
$$(A - \mu I) \begin{bmatrix} t \\ z \end{bmatrix}
  = \begin{bmatrix} (\alpha - \mu) t + c^T z \\ t c + (A_1 - \mu I) z \end{bmatrix}.$$
-/
theorem borderedMatrix_sub_mulVec_cons (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (μ t : ℝ) (z : Fin n → ℝ) :
    (borderedMatrix α c A₁ - μ • 1) *ᵥ Fin.cons t z =
      Fin.cons ((α - μ) * t + c ⬝ᵥ z) (t • c + (A₁ - μ • 1) *ᵥ z) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, borderedMatrix_mulVec_cons,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Pi.sub_apply, Pi.smul_apply, Fin.cons_zero, smul_eq_mul]
    ring
  · simp only [Pi.sub_apply, Pi.smul_apply, Fin.cons_succ, Pi.add_apply, smul_eq_mul]
    ring

/-- Two vectors $[a; u]$ and $[b; w]$ of $\mathbb{R}^{n+1}$ are equal if and only if $a = b$ and
$u = w$. -/
private theorem cons_eq_cons_iff {a b : ℝ} {u w : Fin n → ℝ} :
    (Fin.cons a u : Fin (n + 1) → ℝ) = Fin.cons b w ↔ a = b ∧ u = w :=
  Fin.cons_injective2.eq_iff

/-- **Equation (10.6.13)** of [golub2013matrix]. Let $A = [\alpha\ c^T; c\ A_1]$ be the bordered
matrix (10.6.11), with $\alpha \in \mathbb{R}$, $c \in \mathbb{R}^n$ and
$A_1 \in \mathbb{R}^{n \times n}$. Let $z_c, \delta z \in \mathbb{R}^n$ and
$\lambda_c, \delta\mu, \delta l \in \mathbb{R}$, and put $w = e_1$, $x_c = [1; z_c]$,
$r_c = (A - \lambda_c I) x_c$ and $\delta x = [\delta\mu; \delta z]$. The statement has two
parts.

First, the Newton system (10.6.5), $(A - \lambda_c I)\delta x - \delta l\, x_c = -r_c$ and
$e_1^T \delta x = 0$, holds if and only if $\delta\mu = 0$ and
$$\begin{bmatrix} A_1 - \lambda_c I & -z_c \\ c^T & -1 \end{bmatrix} \begin{bmatrix} \delta z \\
  \delta l \end{bmatrix} = -\begin{bmatrix} (A_1 - \lambda_c I) z_c + c \\ \alpha + c^T z_c -
  \lambda_c \end{bmatrix}.$$

Second, let $A_1 = M_1 - N_1$ with $M_1, N_1 \in \mathbb{R}^{n \times n}$. If
$(\delta z, \delta l)$ solves the reduced system above, then $z_+ = z_c + \delta z$ and
$\lambda_+ = \lambda_c + \delta l$ satisfy
$$(M_1 - \lambda_c I) z_+ = -c + N_1 z_c + (\delta l\, z_c + N_1 \delta z), \qquad \lambda_+ =
  \alpha + c^T z_+.$$

**Typo.** The source prints the term $\alpha + c^T z_c$ of the right-hand side as
$\alpha + + c^T z_c$.

The vector $e_1$ is `Fin.cons 1 0`, and `μ` is $\lambda_c$. The second part is the rearrangement
that leads to the iteration (10.6.14). -/
theorem equation_10_6_13 (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ) (μ δμ : ℝ) (δz : Fin n → ℝ) (δl : ℝ) :
    (((borderedMatrix α c A₁ - μ • 1) *ᵥ Fin.cons δμ δz - δl • (Fin.cons 1 z : Fin (n + 1) → ℝ) =
          -((borderedMatrix α c A₁ - μ • 1) *ᵥ Fin.cons 1 z) ∧
        (Fin.cons 1 0 : Fin (n + 1) → ℝ) ⬝ᵥ Fin.cons δμ δz = 0) ↔
      (δμ = 0 ∧ (A₁ - μ • 1) *ᵥ δz - δl • z = -((A₁ - μ • 1) *ᵥ z + c) ∧
        c ⬝ᵥ δz - δl = -(α + c ⬝ᵥ z - μ))) ∧
    ∀ M₁ N₁ : Matrix (Fin n) (Fin n) ℝ, A₁ = M₁ - N₁ →
      (A₁ - μ • 1) *ᵥ δz - δl • z = -((A₁ - μ • 1) *ᵥ z + c) →
      c ⬝ᵥ δz - δl = -(α + c ⬝ᵥ z - μ) →
      (M₁ - μ • 1) *ᵥ (z + δz) = -c + N₁ *ᵥ z + (δl • z + N₁ *ᵥ δz) ∧
        μ + δl = α + c ⬝ᵥ (z + δz) := by
  refine ⟨?_, fun M₁ N₁ hA h1 h2 => ⟨?_, ?_⟩⟩
  · have hsmul : δl • (Fin.cons 1 z : Fin (n + 1) → ℝ) = Fin.cons δl (δl • z) := by
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    have hsub : ∀ (a b : ℝ) (u w : Fin n → ℝ),
        (Fin.cons a u : Fin (n + 1) → ℝ) - Fin.cons b w = Fin.cons (a - b) (u - w) := by
      intro a b u w
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    have hneg : ∀ (a : ℝ) (u : Fin n → ℝ),
        -(Fin.cons a u : Fin (n + 1) → ℝ) = Fin.cons (-a) (-u) := by
      intro a u
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    have hdot : (Fin.cons 1 0 : Fin (n + 1) → ℝ) ⬝ᵥ Fin.cons δμ δz = δμ := by
      simp [dotProduct, Fin.sum_univ_succ]
    rw [borderedMatrix_sub_mulVec_cons, borderedMatrix_sub_mulVec_cons, hsmul, hsub, hneg,
      cons_eq_cons_iff, hdot]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      subst h3
      refine ⟨rfl, ?_, ?_⟩
      · rw [zero_smul, zero_add] at h2
        rw [h2, one_smul]
        abel
      · linarith
    · rintro ⟨rfl, h2, h3⟩
      refine ⟨⟨by linarith, ?_⟩, rfl⟩
      rw [zero_smul, zero_add, h2, one_smul]
      abel
  · rw [hA] at h1
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_add]
      at h1 ⊢
    rw [← sub_eq_zero] at h1 ⊢
    rw [← h1]
    module
  · rw [dotProduct_add]
    linarith

/-- The state of the JOCC iteration (10.6.14): the pass counter $k$, the iterates $z_j$, the
eigenvalue estimates $\lambda_j$, the residual norms $\rho_j$, and a flag that records whether
the loop has stopped. Indices are 0-based, so index $j$ is the source's $j + 1$. -/
structure JoccState (n : ℕ) where
  /-- The number $k$ of passes taken; the source's counter is $k + 1$. -/
  k : ℕ
  /-- The iterates $z_j$, 0-based; `z 0 = 0` is the source's $z_1 = 0$. -/
  z : ℕ → Fin n → ℝ
  /-- The eigenvalue estimates $\lambda_j$, 0-based; `lam 0` is the source's $\lambda_1 = \alpha$.
  -/
  lam : ℕ → ℝ
  /-- The residual norms $\rho_j$, 0-based; `rho 0` is the source's $\rho_1 = \|c\|_2$. -/
  rho : ℕ → ℝ
  /-- Whether the loop has stopped, that is, whether $\rho_k \le \mathrm{tol}$ was found. -/
  done : Bool

/-- The matrix $N_1 = M_1 - A_1$ of the JOCC splitting, where $M_1$ is the diagonal of $A_1$:
$(N_1)_{ii} = 0$ and $(N_1)_{ij} = -(A_1)_{ij}$ for $i \neq j$. Its entries are copies and
negations of entries of $A_1$, so no rounding enters (algorithm convention 1). -/
def joccN (A₁ : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then 0 else -A₁ i j

section Jocc

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- One entry of the solve step of (10.6.14): the program returns $\mathrm{fl}(\mathrm{fl}(w_i -
c_i) / \mathrm{fl}((A_1)_{ii} - \lambda))$.

**Reading.** Rounded division and totalized zero denominator.
-/
noncomputable def joccEntry (A₁ : Matrix (Fin n) (Fin n) ℝ) (w c : Fin n → ℝ) (l : ℝ)
    (i : Fin n) : M ℝ := do
  let num ← rnd (w i - c i)
  let den ← rnd (A₁ i i - l)
  rnd (num / den)

/-- The solve step of (10.6.14), $(M_1 - \lambda I) z = w - c$ with $M_1$ the diagonal of $A_1$. The
program computes $z_i = (w_i - c_i)/((A_1)_{ii} - \lambda)$ for each $i$ by
`GolubVanLoan.Chapter10.joccEntry`, with one rounded difference, one rounded shifted diagonal
entry and one rounded quotient per entry.

**Reading.** Same componentwise solve with rounded arithmetic.
-/
noncomputable def joccSolve (A₁ : Matrix (Fin n) (Fin n) ℝ) (w c : Fin n → ℝ) (l : ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (z : Fin n → ℝ) i => do
    let q ← joccEntry rnd A₁ w c l i
    pure (Function.update z i q)) 0

/-- One pass of the iteration (10.6.14); once the loop has stopped, the pass returns the state
unchanged. The pass computes $w = N_1 z_k$ by Algorithm 1.1.3, solves
$(M_1 - \lambda_k I) z_{k+1} = w - c$ entrywise by `GolubVanLoan.Chapter10.joccSolve`, and sets
$\lambda_{k+1} = \alpha + c^T z_{k+1}$ with the dot product of Algorithm 1.1.1. It then
increases $k$ and sets $\rho_k = \|A_1 z_k - \lambda_k z_k + c\|_2$, where the residual comes
from Algorithms 1.1.3 and 1.1.2 and `GolubVanLoan.Chapter01.vecAdd`, and the norm from
`GolubVanLoan.Chapter10.vecNorm`. The loop stops when $\rho_k \le \mathrm{tol}$.

**Reading.** Same active update with total division, rounding and observed stop.
-/
noncomputable def joccStep (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ) (tol : ℝ)
    (s : JoccState n) : M (JoccState n) :=
  if s.done then pure s else do
    let w ← algorithm_1_1_3 rnd (joccN A₁) (s.z s.k) 0
    let z ← joccSolve rnd A₁ w c (s.lam s.k)
    let d ← algorithm_1_1_1 rnd c z
    let l ← rnd (α + d)
    let r ← algorithm_1_1_3 rnd A₁ z 0
    let r ← algorithm_1_1_2 rnd (-l) z r
    let r ← vecAdd rnd r c
    let ρ ← vecNorm rnd r
    pure
      { k := s.k + 1
        z := Function.update s.z (s.k + 1) z
        lam := Function.update s.lam (s.k + 1) l
        rho := Function.update s.rho (s.k + 1) ρ
        done := decide (ρ ≤ tol) }

/-- **Equation (10.6.14)** of [golub2013matrix], the Jacobi orthogonal component correction (JOCC).
For the bordered matrix $A = [\alpha\ c^T; c\ A_1]$ of (10.6.11) and a tolerance $\mathrm{tol}$,
the method is
```
λ_1 = α, z_1 = 0, ρ_1 = ‖c‖₂, k = 1
while ρ_k > tol
  Solve (M₁ − λ_k I) z_{k+1} = −c + N₁ z_k
  λ_{k+1} = α + cᵀ z_{k+1},  k = k + 1,  ρ_k = ‖A₁ z_k − λ_k z_k + c‖₂
end
```
where $M_1$ is the diagonal of $A_1$ and $N_1 = M_1 - A_1$.

The `while` loop runs at most `fuel` passes (algorithm convention 3). Each pass is
`GolubVanLoan.Chapter10.joccStep`, and the result is a `GolubVanLoan.Chapter10.JoccState` with
0-based indices. The norm $\|c\|_2$ is computed by `GolubVanLoan.Chapter10.vecNorm`.

**Reading.** Adds finite fuel and stores initialized stop state.
-/
noncomputable def joccIteration (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (tol : ℝ) (fuel : ℕ) : M (JoccState n) := do
  let ρ ← vecNorm rnd c
  (List.range fuel).foldlM (fun s _ => joccStep rnd α c A₁ tol s)
    { k := 0, z := fun _ => 0, lam := Function.update (fun _ => 0) 0 α,
      rho := Function.update (fun _ => 0) 0 ρ, done := decide (ρ ≤ tol) }

end Jocc

/-- In exact arithmetic the solve step of (10.6.14) returns
$z_i = (w_i - c_i)/((A_1)_{ii} - \lambda)$ for every $i$, with the convention $z_i = 0$ when the
denominator is $0$.

**Reading.** Exact component formula computed even at zero denominator.
-/
theorem joccSolve_spec (A₁ : Matrix (Fin n) (Fin n) ℝ) (w c : Fin n → ℝ) (l : ℝ) :
    Id.run (joccSolve pure A₁ w c l) = fun i => (w i - c i) / (A₁ i i - l) := by
  funext i
  rw [joccSolve, List.idRun_foldlM_update_apply (fun i (_ : ℝ) => joccEntry pure A₁ w c l i) _
    (List.nodup_finRange n), ite_eq_left (List.mem_finRange i)]
  rfl

/-- The exact run with $t + 1$ passes is one pass applied to the exact run with $t$ passes. -/
private theorem joccIteration_succ (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ)
    (tol : ℝ) (t : ℕ) :
    Id.run (joccIteration pure α c A₁ tol (t + 1)) =
      Id.run (joccStep pure α c A₁ tol (Id.run (joccIteration pure α c A₁ tol t))) := by
  simp only [joccIteration, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- **Equation (10.6.14)** of [golub2013matrix], exact semantics. Let
$\alpha, \mathrm{tol} \in \mathbb{R}$, $c \in \mathbb{R}^n$ and
$A_1 \in \mathbb{R}^{n \times n}$. Let $k$, $z_j$, $\lambda_j$ and $\rho_j$ be the final state
of the JOCC iteration in exact arithmetic with at most `fuel` passes, with 0-based indices. Let
$M_1$ be the diagonal of $A_1$ and $N_1 = M_1 - A_1$. Then:

* $\lambda_0 = \alpha$ and $z_0 = 0$;
* $\rho_j = \|(A_1 - \lambda_j I) z_j + c\|_2$ for every $j \le k$;
* for every $j < k$, if $(A_1)_{ii} \neq \lambda_j$ for all $i$, then
  $(M_1 - \lambda_j I) z_{j+1} = -c + N_1 z_j$;
* $\lambda_{j+1} = \alpha + c^T z_{j+1}$ for every $j < k$;
* $\rho_j > \mathrm{tol}$ for every $j < k$;
* $k = \mathrm{fuel}$ or $\rho_k \le \mathrm{tol}$.

By (10.6.15), the vector $x_j = [1; z_j]$ has $(A - \lambda_j I) x_j = [0; r_j]$ with
$r_j = (A_1 - \lambda_j I) z_j + c$, and the corrections $x_{j+1} - x_j = [0; z_{j+1} - z_j]$
are orthogonal to $e_1$, which gives the method its name.

The matrix $N_1$ is `GolubVanLoan.Chapter10.joccN A₁`, and $M_1$ is
`Matrix.diagonal fun i => A₁ i i`.

**Reading.** Same recurrence at attained count, algebraic solve conditional on nonzero shifted
diagonal.
-/
theorem equation_10_6_14 (α : ℝ) (c : Fin n → ℝ) (A₁ : Matrix (Fin n) (Fin n) ℝ) (tol : ℝ)
    (fuel : ℕ) :
    let s := Id.run (joccIteration pure α c A₁ tol fuel)
    s.lam 0 = α ∧ s.z 0 = 0 ∧
      (∀ j ≤ s.k, s.rho j =
        ‖(WithLp.toLp 2 ((A₁ - s.lam j • 1) *ᵥ s.z j + c) : EuclideanSpace ℝ (Fin n))‖) ∧
      (∀ j < s.k, (∀ i, A₁ i i ≠ s.lam j) →
        (Matrix.diagonal (fun i => A₁ i i) - s.lam j • 1) *ᵥ s.z (j + 1) = -c + joccN A₁ *ᵥ s.z j) ∧
      (∀ j < s.k, s.lam (j + 1) = α + c ⬝ᵥ s.z (j + 1)) ∧
      (∀ j < s.k, tol < s.rho j) ∧ (s.k = fuel ∨ s.rho s.k ≤ tol) := by
  intro s
  -- the invariant after `t` passes
  let P : ℕ → JoccState n → Prop := fun t s =>
    s.k ≤ t ∧ s.lam 0 = α ∧ s.z 0 = 0 ∧
      (∀ j ≤ s.k, s.rho j =
        ‖(WithLp.toLp 2 ((A₁ - s.lam j • 1) *ᵥ s.z j + c) : EuclideanSpace ℝ (Fin n))‖) ∧
      (∀ j < s.k, (∀ i, A₁ i i ≠ s.lam j) →
        (Matrix.diagonal (fun i => A₁ i i) - s.lam j • 1) *ᵥ s.z (j + 1) = -c + joccN A₁ *ᵥ s.z j) ∧
      (∀ j < s.k, s.lam (j + 1) = α + c ⬝ᵥ s.z (j + 1)) ∧
      (∀ j < s.k, tol < s.rho j) ∧ s.done = decide (s.rho s.k ≤ tol) ∧
      (s.k = t ∨ s.done = true)
  have hP : ∀ t, P t (Id.run (joccIteration pure α c A₁ tol t)) := by
    intro t
    induction t with
    | zero =>
      simp only [P, joccIteration, Id.run_bind, vecNorm_spec, List.range_zero, List.foldlM_nil,
        Id.run_pure]
      refine ⟨le_rfl, by simp, by simp, fun j hj => ?_, fun j hj => absurd hj (by omega),
        fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega), by simp, by simp⟩
      obtain rfl : j = 0 := by omega
      simp
    | succ t ih =>
      rw [joccIteration_succ]
      set s := Id.run (joccIteration pure α c A₁ tol t)
      obtain ⟨hkt, hl0, hz0, hrho, hupd, hlam, hgt, hdone, hfin⟩ := ih
      cases hsd : s.done with
      | true =>
        simp only [joccStep, hsd, ↓reduceIte, Id.run_pure]
        exact ⟨by omega, hl0, hz0, hrho, hupd, hlam, hgt, hsd ▸ hdone, Or.inr hsd⟩
      | false =>
        have hkt' : s.k = t := hfin.resolve_right (by simp [hsd])
        have hρ : tol < s.rho s.k := by
          have : ¬ s.rho s.k ≤ tol := by simpa [hsd] using hdone.symm
          linarith [not_le.1 this]
        set z' : Fin n → ℝ := fun i =>
          ((joccN A₁ *ᵥ s.z s.k) i - c i) / (A₁ i i - s.lam s.k) with hz'
        simp only [P, joccStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
          algorithm_1_1_3_spec, zero_add, joccSolve_spec, Id.run_pure, algorithm_1_1_1_spec,
          algorithm_1_1_2_spec, vecAdd_spec, vecNorm_spec]
        rw [← hz']
        have hres : A₁ *ᵥ z' + (-(α + c ⬝ᵥ z')) • z' + c =
            (A₁ - (α + c ⬝ᵥ z') • 1) *ᵥ z' + c := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, neg_smul, sub_eq_add_neg]
        rw [hres]
        refine ⟨by omega, ?_, ?_, fun j hj => ?_, fun j hj hne => ?_, fun j hj => ?_,
          fun j hj => ?_, by simp only [Function.update_self], Or.inl (by omega)⟩
        · rw [Function.update_of_ne (by omega)]; exact hl0
        · rw [Function.update_of_ne (by omega)]; exact hz0
        · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hrho j (by omega)
          · simp
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hupd j hj (by
              intro i
              have := hne i
              rwa [Function.update_of_ne (by omega)] at this)
          · rw [Function.update_of_ne (by omega), Function.update_self,
              Function.update_of_ne (by omega)]
            have hne' : ∀ i, A₁ i i - s.lam s.k ≠ 0 := fun i => sub_ne_zero.2 (by
              have := hne i
              rwa [Function.update_of_ne (by omega)] at this)
            ext i
            simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
              Matrix.mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
              Pi.neg_apply, z']
            field_simp [hne' i]
            ring
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hlam j hj
          · simp
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [Function.update_of_ne (by omega)]
            exact hgt j hj
          · rw [Function.update_of_ne (by omega)]
            exact hρ
  obtain ⟨-, hl0, hz0, hrho, hupd, hlam, hgt, hdone, hfin⟩ := hP fuel
  refine ⟨hl0, hz0, hrho, hupd, hlam, hgt, ?_⟩
  rcases hfin with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [h] using hdone.symm)

/-! ### Davidson's method and the Jacobi–Davidson framework (§10.6.3–10.6.4) -/

/-- The state of the subspace expansion loop that Davidson's method (10.6.16) and the
Jacobi–Davidson framework of §10.6.4 share. Indices are 0-based: after $k$ passes the basis is
$v_0, \dots, v_k$ (the source's $V_{k+1}$), $(\lambda_j, x_j)$ is the Ritz pair and $\delta v_j$
the correction of pass $j$, and the state also holds the norm $\|s\|_2$ of the orthogonalized
correction of each pass, the current residual and its norm. -/
structure DavidsonState (n : ℕ) where
  /-- The number $k$ of passes taken. -/
  k : ℕ
  /-- The orthonormal basis vectors $v_0, \dots, v_k$. -/
  v : ℕ → Fin n → ℝ
  /-- The Ritz values $\lambda_j$; `lam 0` is $x_1^T A x_1$ for the starting vector $x_1$. -/
  lam : ℕ → ℝ
  /-- The Ritz vectors $x_j$; `x 0` is the starting vector $x_1$. -/
  x : ℕ → Fin n → ℝ
  /-- The corrections $\delta v_j$, one per pass. -/
  dv : ℕ → Fin n → ℝ
  /-- The norms $\|s\|_2$ of the orthogonalized corrections, one per pass. -/
  sNorm : ℕ → ℝ
  /-- The current residual $r_k = A x_k - \lambda_k x_k$. -/
  r : Fin n → ℝ
  /-- The norm $\|r_k\|_2$ of the current residual. -/
  rho : ℝ
  /-- Whether the loop has stopped, that is, whether $\|r_k\|_2 \le \mathrm{tol}$ was found. -/
  done : Bool

/-- The matrix $V_p \in \mathbb{R}^{n \times p}$ whose columns are $v_0, \dots, v_{p-1}$, the
source's $[v_1 \mid \cdots \mid v_p]$. -/
def basisCols (v : ℕ → Fin n → ℝ) (p : ℕ) : Matrix (Fin n) (Fin p) ℝ :=
  Matrix.of fun i j => v j i

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- The modified Gram–Schmidt expansion of (10.6.16), which computes
$s = (I - V_p V_p^T)\, \delta v$. The source says that "the transition from $V_k$ to $V_{k+1}$
can be effectively carried out by a modified Gram–Schmidt process". The program starts from
$s = \delta v$ and runs $s \leftarrow s - (v_j^T s)\, v_j$ for $j = 0, \dots, p - 1$ in order,
with the dot product of Algorithm 1.1.1 and the saxpy of Algorithm 1.1.2.

**Correction.** Rounded modified Gram–Schmidt for projected correction.
-/
noncomputable def mgsExpand (v : ℕ → Fin n → ℝ) (p : ℕ) (δ : Fin n → ℝ) : M (Fin n → ℝ) :=
  (List.range p).foldlM (fun s j => do
    let h ← algorithm_1_1_1 rnd (v j) s
    algorithm_1_1_2 rnd (-h) (v j) s) δ

/-- One entry of Davidson's correction: the program returns $\mathrm{fl}(-r_i / \mathrm{fl}(a_{ii} -
\lambda))$. The negation is exact.

**Reading.** Same entry ratio with rounding and total division.
-/
noncomputable def davidsonEntry (A : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) (r : Fin n → ℝ)
    (i : Fin n) : M ℝ := do
  let d ← rnd (A i i - l)
  rnd (-r i / d)

/-- Davidson's correction equation $(M - \lambda I)\, \delta v = -r$, where $M$ is the diagonal of
$A$. The program computes $\delta v_i = -r_i / (a_{ii} - \lambda)$ for each $i$ by
`GolubVanLoan.Chapter10.davidsonEntry`.

**Reading.** Rounded diagonal solve for every coordinate.
-/
noncomputable def davidsonCorrection (A : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) (r : Fin n → ℝ) :
    M (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun (z : Fin n → ℝ) i => do
    let q ← davidsonEntry rnd A l r i
    pure (Function.update z i q)) 0

/-- One pass of the subspace expansion loop; once the loop has stopped, the pass returns the state
unchanged. In the source's numbering, the pass computes the correction $\delta v_k =
\mathrm{correct}(x_k, \lambda_k, r_k)$, the expansion $s_{k+1} = (I - V_k V_k^T)\, \delta v_k$
by `GolubVanLoan.Chapter10.mgsExpand`, $v_{k+1} = s_{k+1} / \|s_{k+1}\|_2$, and
$H = V_{k+1}^T A V_{k+1}$ by two matrix products of Algorithm 1.1.5. It takes the Ritz pair
$(\theta, t) = \mathrm{ritz}(H)$, sets $\lambda_{k+1} = \theta$ and $x_{k+1} = V_{k+1} t$, and
computes $r_{k+1} = A x_{k+1} - \lambda_{k+1} x_{k+1}$ and its norm. The loop stops when
$\|r_{k+1}\|_2 \le \mathrm{tol}$.

**Reading.** Generic callback, rounded expansion, explicit stopping and total division.
-/
noncomputable def subspaceExpansionStep (A : Matrix (Fin n) (Fin n) ℝ)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → M (Fin n → ℝ))
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → M (ℝ × (Fin p → ℝ))) (tol : ℝ)
    (s : DavidsonState n) : M (DavidsonState n) :=
  if s.done then pure s else do
    let δ ← correct (s.x s.k) (s.lam s.k) s.r
    let w ← mgsExpand rnd s.v (s.k + 1) δ
    let ν ← vecNorm rnd w
    let vnew ← vecDiv rnd w ν
    let v := Function.update s.v (s.k + 1) vnew
    let AV ← algorithm_1_1_5 rnd A (basisCols v (s.k + 2)) 0
    let H ← algorithm_1_1_5 rnd (basisCols v (s.k + 2))ᵀ AV 0
    let θt ← ritz (s.k + 2) H
    let x ← algorithm_1_1_3 rnd (basisCols v (s.k + 2)) θt.2 0
    let Ax ← algorithm_1_1_3 rnd A x 0
    let r ← algorithm_1_1_2 rnd (-θt.1) x Ax
    let ρ ← vecNorm rnd r
    pure
      { k := s.k + 1
        v := v
        lam := Function.update s.lam (s.k + 1) θt.1
        x := Function.update s.x (s.k + 1) x
        dv := Function.update s.dv s.k δ
        sNorm := Function.update s.sNorm s.k ν
        r := r
        rho := ρ
        done := decide (ρ ≤ tol) }

/-- The subspace expansion loop that Davidson's method (10.6.16) and the Jacobi–Davidson framework
of §10.6.4 of [golub2013matrix] share. From a starting vector $x_1$ the program sets
$\lambda_1 = x_1^T A x_1$, $r_1 = A x_1 - \lambda_1 x_1$ and $V_1 = [x_1]$. Then, while
$\|r_k\|_2 > \mathrm{tol}$, it runs the pass `GolubVanLoan.Chapter10.subspaceExpansionStep` with
the correction step `correct` and the Ritz pair selector `ritz`.

The loop runs at most `fuel` passes (algorithm convention 3). The initial products are
Algorithms 1.1.3, 1.1.1 and 1.1.2.

**Correction.** Explicit finite fuel, supplied correction and Ritz selection and arbitrary initial
vector.
-/
noncomputable def subspaceExpansion (A : Matrix (Fin n) (Fin n) ℝ)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → M (Fin n → ℝ))
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → M (ℝ × (Fin p → ℝ))) (x₁ : Fin n → ℝ)
    (tol : ℝ) (fuel : ℕ) : M (DavidsonState n) := do
  let Ax ← algorithm_1_1_3 rnd A x₁ 0
  let l ← algorithm_1_1_1 rnd x₁ Ax
  let r ← algorithm_1_1_2 rnd (-l) x₁ Ax
  let ρ ← vecNorm rnd r
  (List.range fuel).foldlM (fun s _ => subspaceExpansionStep rnd A correct ritz tol s)
    { k := 0, v := Function.update (fun _ => 0) 0 x₁, lam := Function.update (fun _ => 0) 0 l,
      x := Function.update (fun _ => 0) 0 x₁, dv := fun _ => 0, sNorm := fun _ => 0, r := r,
      rho := ρ, done := decide (ρ ≤ tol) }

/-- **Equation (10.6.16)** of [golub2013matrix] (Davidson's method). For
$A \in \mathbb{R}^{n \times n}$ and a tolerance $\mathrm{tol}$, the method is
```
x_1 = e_1, λ_1 = x_1ᵀ A x_1, r_1 = A x_1 − λ_1 x_1, V_1 = [e_1], k = 1
while ‖r_k‖ > tol
  Solve (M − λ_k I) δv_k = −r_k
  s_{k+1} = (I − V_k V_kᵀ) δv_k,  v_{k+1} = s_{k+1}/‖s_{k+1}‖₂,  V_{k+1} = [V_k | v_{k+1}]
  (V_{k+1}ᵀ A V_{k+1}) t_{k+1} = θ_{k+1} t_{k+1}  (a suitably chosen Ritz pair)
  λ_{k+1} = θ_{k+1},  x_{k+1} = V_{k+1} t_{k+1},  k = k + 1,  r_k = A x_k − λ_k x_k
end
```
where $M$ is the diagonal of $A$.

The orthogonalization is modified Gram–Schmidt, as the source remarks. The source leaves the
choice of the Ritz pair of $V_{k+1}^T A V_{k+1}$ open, so the program takes it from the selector
`ritz` that the caller supplies. The program is `GolubVanLoan.Chapter10.subspaceExpansion` with
the correction `GolubVanLoan.Chapter10.davidsonCorrection` and the start $e_1$.

**Correction.** Source's first coordinate start and diagonal correction with rounded fixed fuel and
Ritz callback.
-/
noncomputable def davidson (A : Matrix (Fin n) (Fin n) ℝ)
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → M (ℝ × (Fin p → ℝ))) (tol : ℝ) (fuel : ℕ) :
    M (DavidsonState n) :=
  subspaceExpansion rnd A (fun _ l r => davidsonCorrection rnd A l r) ritz
    (fun i => if (i : ℕ) = 0 then 1 else 0) tol fuel

/-- **Section 10.6.4** of [golub2013matrix], the Jacobi–Davidson framework. This is Davidson's
method (10.6.16) with two changes: the start is a vector $x_1$ that the caller supplies, and the
Davidson correction is replaced by a solution $\delta v_k$ of the projected correction equation
(10.6.19),
$$(I - x_k x_k^T)(M - \lambda_k I)(I - x_k x_k^T)\, \delta v_k = -r_k, \qquad x_k^T \delta v_k =
  0.$$

The source says that various Chapter 11 iterative solvers can be applied to the correction
equation. The program therefore takes the solver `solve` as an argument, called as
`solve x_k λ_k r_k` (algorithm convention 5). The program is
`GolubVanLoan.Chapter10.subspaceExpansion` with the correction `solve`. The specification
`GolubVanLoan.Chapter10.jacobiDavidson_spec` assumes that $x_1$ is a unit vector.

**Correction.** Arbitrary starting vector, supplied correction and Ritz callback, finite fuel.
-/
noncomputable def jacobiDavidson (A : Matrix (Fin n) (Fin n) ℝ)
    (solve : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → M (Fin n → ℝ))
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → M (ℝ × (Fin p → ℝ))) (x₁ : Fin n → ℝ)
    (tol : ℝ) (fuel : ℕ) : M (DavidsonState n) :=
  subspaceExpansion rnd A solve ritz x₁ tol fuel

end Programs

/-! ### Exact semantics of the subspace expansion loop -/

/-- In exact arithmetic, if $v_0, \dots, v_{p-1}$ are orthonormal, the modified Gram–Schmidt
expansion returns the classical projection
$$\delta - \sum_{j < p} (v_j^T \delta)\, v_j.$$
Modified and classical Gram–Schmidt agree in exact arithmetic
(`InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum`). -/
theorem mgsExpand_spec {v : ℕ → Fin n → ℝ} {p : ℕ}
    (hv : ∀ i < p, ∀ j < p, v i ⬝ᵥ v j = if i = j then 1 else 0) (δ : Fin n → ℝ) :
    Id.run (mgsExpand pure v p δ) = δ - ∑ j ∈ Finset.range p, (v j ⬝ᵥ δ) • v j := by
  induction p with
  | zero => simp [mgsExpand]
  | succ p ih =>
    have ih' := ih (fun i hi j hj => hv i (by omega) j (by omega))
    have hstep : Id.run (mgsExpand pure v (p + 1) δ) =
        Id.run (mgsExpand pure v p δ) -
          (v p ⬝ᵥ Id.run (mgsExpand pure v p δ)) • v p := by
      simp only [mgsExpand, List.range_succ, List.foldlM_append, List.foldlM_cons,
        List.foldlM_nil, bind_pure, Id.run_bind, algorithm_1_1_1_spec, algorithm_1_1_2_spec]
      rw [neg_smul, ← sub_eq_add_neg]
    rw [hstep, ih', Finset.sum_range_succ]
    have hdot : v p ⬝ᵥ (δ - ∑ j ∈ Finset.range p, (v j ⬝ᵥ δ) • v j) = v p ⬝ᵥ δ := by
      rw [dotProduct_sub, dotProduct_sum]
      rw [Finset.sum_eq_zero fun j hj => by
        rw [dotProduct_smul, hv p (by omega) j (by simp at hj; omega),
          ite_eq_right (by simp at hj; omega), smul_zero], sub_zero]
    rw [hdot]
    abel

/-- In exact arithmetic Davidson's correction is $\delta v_i = -r_i / (a_{ii} - \lambda)$ for every
$i$, with the convention $\delta v_i = 0$ when the denominator is $0$. Hence
$(M - \lambda I)\, \delta v = -r$ when $a_{ii} \neq \lambda$ for all $i$, where $M$ is the
diagonal of $A$.

**Reading.** Exact quotient is totalized at zero diagonal shift.
-/
theorem davidsonCorrection_spec (A : Matrix (Fin n) (Fin n) ℝ) (l : ℝ) (r : Fin n → ℝ) :
    Id.run (davidsonCorrection pure A l r) = fun i => -r i / (A i i - l) := by
  funext i
  rw [davidsonCorrection, List.idRun_foldlM_update_apply
    (fun i (_ : ℝ) => davidsonEntry pure A l r i) _ (List.nodup_finRange n),
    ite_eq_left (List.mem_finRange i)]
  rfl

/-- The exact run with $t + 1$ passes is one pass applied to the exact run with $t$ passes. -/
private theorem subspaceExpansion_succ (A : Matrix (Fin n) (Fin n) ℝ)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → Id (Fin n → ℝ))
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))) (x₁ : Fin n → ℝ)
    (tol : ℝ) (t : ℕ) :
    Id.run (subspaceExpansion pure A correct ritz x₁ tol (t + 1)) =
      Id.run (subspaceExpansionStep pure A correct ritz tol
        (Id.run (subspaceExpansion pure A correct ritz x₁ tol t))) := by
  simp only [subspaceExpansion, List.range_succ, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, bind_pure, Id.run_bind]

/-- Entry $i$ of $V_p^T y$ is $v_i^T y$. -/
private theorem basisCols_transpose_mulVec_apply (v : ℕ → Fin n → ℝ) (p : ℕ) (y : Fin n → ℝ)
    (i : Fin p) : ((basisCols v p)ᵀ *ᵥ y) i = v i ⬝ᵥ y := by
  simp [basisCols, Matrix.mulVec, dotProduct]

/-- The product $V_p t$ is $\sum_i t_i v_i$. -/
private theorem basisCols_mulVec (v : ℕ → Fin n → ℝ) (p : ℕ) (t : Fin p → ℝ) :
    basisCols v p *ᵥ t = ∑ i : Fin p, t i • v i := by
  ext a
  simp [basisCols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- If $v_0, \dots, v_{p-1}$ are orthonormal, then $V_p^T V_p = I$. -/
private theorem basisCols_transpose_mul_self {v : ℕ → Fin n → ℝ} {p : ℕ}
    (hv : ∀ i < p, ∀ j < p, v i ⬝ᵥ v j = if i = j then 1 else 0) :
    (basisCols v p)ᵀ * basisCols v p = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h := hv i i.isLt j j.isLt
  simp only [basisCols, Matrix.transpose_apply, Matrix.of_apply] at h ⊢
  rw [← dotProduct.eq_def, h]
  simp [Fin.ext_iff]

/-- A vector orthogonal to $v_0, \dots, v_{p-1}$ is orthogonal to their span
$\operatorname{ran} V_p$. -/
private theorem toLp_mem_orthogonal_span {p : ℕ} (v : ℕ → Fin n → ℝ) (y : Fin n → ℝ)
    (h : ∀ i < p, v i ⬝ᵥ y = 0) :
    (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n)) ∈ (Submodule.span ℝ
      (Set.range fun i : Fin p => (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n))))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
    exact h i i.isLt
  | zero => simp
  | add z w _ _ hz hw => rw [inner_add_left, hz, hw, add_zero]
  | smul c z _ hz => rw [inner_smul_left, hz, mul_zero]

/-- A vector $x$ with $x^T x = 1$ has Euclidean norm $\|x\|_2 = 1$. -/
private theorem norm_toLp_eq_one {x : Fin n → ℝ} (h : x ⬝ᵥ x = 1) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have h2 := real_inner_self_eq_norm_sq (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, h] at h2
  rw [← Real.sqrt_sq (norm_nonneg _), ← h2, Real.sqrt_one]

/-- If $x = \sum_{i \le j} c_i v_i$, $x^T x = 1$, and the residual $Ax - \lambda x$ is orthogonal to
$v_0, \dots, v_j$, then $(\lambda, x)$ is a Ritz pair of $A$ on the span of $v_0, \dots, v_j$. -/
private theorem isRitzPair_of_cond {A : Matrix (Fin n) (Fin n) ℝ} {v : ℕ → Fin n → ℝ}
    {x : Fin n → ℝ} {l : ℝ} {j : ℕ} (hc : ∃ c : Fin (j + 1) → ℝ, x = ∑ i, c i • v i)
    (hx : x ⬝ᵥ x = 1) (hr : ∀ i ≤ j, v i ⬝ᵥ (A *ᵥ x - l • x) = 0) :
    Krylov.IsRitzPair (Matrix.toEuclideanLin A)
      (Submodule.span ℝ (Set.range fun i : Fin (j + 1) =>
        (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n)))) l (WithLp.toLp 2 x) where
  mem := by
    obtain ⟨c, rfl⟩ := hc
    rw [WithLp.toLp_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [WithLp.toLp_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  ne_zero := fun h => by
    have h0 : x = 0 := by simpa using congrArg WithLp.ofLp h
    rw [h0, dotProduct_zero] at hx
    exact zero_ne_one hx
  residual_mem_orthogonal := by
    rw [Matrix.toEuclideanLin_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_sub]
    exact toLp_mem_orthogonal_span v _ fun i hi => hr i (by omega)

/-- Exact semantics of the subspace expansion loop that (10.6.16) and §10.6.4 of [golub2013matrix]
share. Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let `correct` be any correction step,
let the selector `ritz` return, for every symmetric $H \in \mathbb{R}^{p \times p}$, a pair
$(\theta, t)$ with $Ht = \theta t$ and $t^T t = 1$, and let the starting vector satisfy
$x_1^T x_1 = 1$. Consider the final state of the loop in exact arithmetic with at most `fuel`
passes, with 0-based indices: the counter $k$, the basis $v_0, \dots, v_k$, the Ritz pairs
$(\lambda_j, x_j)$, the corrections $\delta v_j$, the residual $r$ and its norm $\rho$. Then:

* $k = \mathrm{fuel}$ or $\rho \le \mathrm{tol}$;
* the first Ritz vector $x_0$ is the starting vector;
* $r = A x_k - \lambda_k x_k$ and $\rho = \|r\|_2$;
* for every $j < k$, the correction of pass $j$ is $\delta v_j = \mathrm{correct}(x_j,
  \lambda_j, A x_j - \lambda_j x_j)$;
* if no orthogonalized correction $s$ has norm $0$, then $v_0, \dots, v_k$ are orthonormal, and
  for every $j \le k$, $(\lambda_j, x_j)$ is a Ritz pair of $A$ on
  $\operatorname{span}\{v_0, \dots, v_j\}$, $\|x_j\|_2 = 1$, and
  $v_i^T (A x_j - \lambda_j x_j) = 0$ for all $i \le j$.

The correction step plays no role in these claims.

A Ritz pair is `Krylov.IsRitzPair` for `Matrix.toEuclideanLin A` on a span in
`EuclideanSpace ℝ (Fin n)`. The norms of the orthogonalized corrections are the field `sNorm` of
the state.

**Limitation.** The unit Ritz-vector hypothesis is quantified over all dimensions `p`. At `p =
0`, the only vector has squared norm zero, so the hypothesis cannot be satisfied. The iteration
only requests Ritz pairs of positive order.

**Reading.** Ritz extractor axiom also requires a unit vector in dimension zero and is impossible.
-/
theorem subspaceExpansion_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → Id (Fin n → ℝ))
    {ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))}
    (hritz : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm →
      H *ᵥ (Id.run (ritz p H)).2 = (Id.run (ritz p H)).1 • (Id.run (ritz p H)).2 ∧
        (Id.run (ritz p H)).2 ⬝ᵥ (Id.run (ritz p H)).2 = 1)
    {x₁ : Fin n → ℝ} (hx₁ : x₁ ⬝ᵥ x₁ = 1) (tol : ℝ) (fuel : ℕ) :
    let s := Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)
    (s.k = fuel ∨ s.rho ≤ tol) ∧ s.x 0 = x₁ ∧
      s.r = A *ᵥ s.x s.k - s.lam s.k • s.x s.k ∧
      s.rho = ‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ ∧
      (∀ j < s.k, s.dv j = Id.run (correct (s.x j) (s.lam j) (A *ᵥ s.x j - s.lam j • s.x j))) ∧
      ((∀ j < s.k, s.sNorm j ≠ 0) →
        (∀ i ≤ s.k, ∀ j ≤ s.k, s.v i ⬝ᵥ s.v j = if i = j then 1 else 0) ∧
        ∀ j ≤ s.k, Krylov.IsRitzPair (Matrix.toEuclideanLin A)
            (Submodule.span ℝ (Set.range fun i : Fin (j + 1) =>
              (WithLp.toLp 2 (s.v i) : EuclideanSpace ℝ (Fin n))))
            (s.lam j) (WithLp.toLp 2 (s.x j)) ∧
          ‖(WithLp.toLp 2 (s.x j) : EuclideanSpace ℝ (Fin n))‖ = 1 ∧
          ∀ i ≤ j, s.v i ⬝ᵥ (A *ᵥ s.x j - s.lam j • s.x j) = 0) := by
  intro s
  let P : ℕ → DavidsonState n → Prop := fun t s =>
    s.k ≤ t ∧ (s.k = t ∨ s.done = true) ∧ s.done = decide (s.rho ≤ tol) ∧ s.x 0 = x₁ ∧
      s.v 0 = x₁ ∧ s.r = A *ᵥ s.x s.k - s.lam s.k • s.x s.k ∧
      s.rho = ‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ ∧
      (∀ j < s.k, s.dv j = Id.run (correct (s.x j) (s.lam j) (A *ᵥ s.x j - s.lam j • s.x j))) ∧
      ((∀ j < s.k, s.sNorm j ≠ 0) →
        (∀ i ≤ s.k, ∀ j ≤ s.k, s.v i ⬝ᵥ s.v j = if i = j then 1 else 0) ∧
        ∀ j ≤ s.k, (∃ c : Fin (j + 1) → ℝ, s.x j = ∑ i, c i • s.v i) ∧ s.x j ⬝ᵥ s.x j = 1 ∧
          ∀ i ≤ j, s.v i ⬝ᵥ (A *ᵥ s.x j - s.lam j • s.x j) = 0)
  have hP : ∀ t, P t (Id.run (subspaceExpansion pure A correct ritz x₁ tol t)) := by
    intro t
    induction t with
    | zero =>
      simp only [subspaceExpansion, Id.run_bind, algorithm_1_1_3_spec, algorithm_1_1_1_spec,
        algorithm_1_1_2_spec, vecNorm_spec, zero_add, List.range_zero, List.foldlM_nil,
        Id.run_pure]
      refine ⟨le_rfl, Or.inl rfl, rfl, ?_, ?_, ?_, rfl, fun j hj => absurd hj (by simp),
        fun _ => ⟨fun i hi j hj => ?_, fun j hj => ?_⟩⟩
      · simp only [Function.update_self]
      · simp only [Function.update_self]
      · simp only [Function.update_self]
        rw [neg_smul, ← sub_eq_add_neg]
      · dsimp only at hi hj
        obtain rfl : i = 0 := by omega
        obtain rfl : j = 0 := by omega
        simpa using hx₁
      · dsimp only at hj
        obtain rfl : j = 0 := by omega
        simp only [Function.update_self]
        refine ⟨⟨fun _ => 1, by simp⟩, hx₁, fun i hi => ?_⟩
        obtain rfl : i = 0 := by omega
        simp only [Function.update_self]
        rw [dotProduct_sub, dotProduct_smul, hx₁, smul_eq_mul, mul_one, sub_self]
    | succ t ih =>
      rw [subspaceExpansion_succ]
      obtain ⟨hkt, hfin, hdone, hx0, hv0, hr, hrho, hdv, hortho⟩ := ih
      set s := Id.run (subspaceExpansion pure A correct ritz x₁ tol t) with hs
      cases hsd : s.done with
      | true =>
        simp only [subspaceExpansionStep, hsd, ↓reduceIte, Id.run_pure]
        exact ⟨by omega, Or.inr hsd, hdone, hx0, hv0, hr, hrho, hdv, hortho⟩
      | false =>
        have hkt' : s.k = t := hfin.resolve_right (by simp [hsd])
        simp only [subspaceExpansionStep, hsd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
          vecNorm_spec, vecDiv_spec, algorithm_1_1_5_spec, algorithm_1_1_3_spec,
          algorithm_1_1_2_spec, zero_add, Id.run_pure]
        set k := s.k with hk
        set δ := Id.run (correct (s.x k) (s.lam k) s.r) with hδ
        set w := Id.run (mgsExpand pure s.v (k + 1) δ) with hw
        set ν := ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n))‖ with hν
        set v' := Function.update s.v (k + 1) (ν⁻¹ • w) with hv'
        set V := basisCols v' (k + 2) with hV
        set H := Vᵀ * (A * V) with hH
        set θ := (Id.run (ritz (k + 2) H)).1 with hθ
        set tt := (Id.run (ritz (k + 2) H)).2 with htt
        set x' := V *ᵥ tt with hx'
        have hv'lo : ∀ i ≤ k, v' i = s.v i := fun i hi => by
          rw [hv', Function.update_of_ne (by omega)]
        refine ⟨?_, Or.inl ?_, rfl, ?_, ?_, ?_, rfl, fun j hj => ?_, fun hs' => ?_⟩
        · dsimp only
          omega
        · dsimp only
          omega
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hx0
        · dsimp only
          rw [hv'lo 0 (by omega)]
          exact hv0
        · dsimp only
          simp only [Function.update_self]
          rw [neg_smul, ← sub_eq_add_neg]
        · dsimp only at hj ⊢
          rw [Function.update_of_ne (show j ≠ k + 1 by omega) x' s.x,
            Function.update_of_ne (show j ≠ k + 1 by omega) θ s.lam]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [Function.update_of_ne (show j ≠ k by omega) δ s.dv]
            exact hdv j hj
          · rw [Function.update_self, hδ, hr]
        -- the orthonormal half
        dsimp only at hs' ⊢
        have hsk : ∀ j < k, s.sNorm j ≠ 0 := fun j hj => by
          have := hs' j (by omega)
          rwa [Function.update_of_ne (by omega)] at this
        have hν0 : ν ≠ 0 := by
          have := hs' k (by omega)
          rwa [Function.update_self] at this
        obtain ⟨horth, hcond⟩ := hortho hsk
        have hwe : w = δ - ∑ j ∈ Finset.range (k + 1), (s.v j ⬝ᵥ δ) • s.v j :=
          mgsExpand_spec (fun i hi j hj => horth i (by omega) j (by omega)) δ
        have hvw : ∀ j ≤ k, s.v j ⬝ᵥ w = 0 := fun j hj => by
          rw [hwe, dotProduct_sub, dotProduct_sum, Finset.sum_eq_single j]
          · rw [dotProduct_smul, horth j hj j hj, ite_eq_left rfl, smul_eq_mul, mul_one, sub_self]
          · intro l hl hlj
            rw [dotProduct_smul, horth j hj l (by simp at hl; omega), ite_eq_right (Ne.symm hlj),
              smul_zero]
          · intro h
            exact absurd (Finset.mem_range.2 (by omega)) h
        have hww : w ⬝ᵥ w = ν ^ 2 := by
          rw [hν, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]
        have horth' : ∀ i ≤ k + 1, ∀ j ≤ k + 1, v' i ⬝ᵥ v' j = if i = j then 1 else 0 := by
          intro i hi j hj
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hi) with hi | rfl <;>
            rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj | rfl
          · rw [hv'lo i (by omega), hv'lo j (by omega)]
            exact horth i (by omega) j (by omega)
          · rw [hv'lo i (by omega), hv', Function.update_self, dotProduct_smul, hvw i (by omega),
              smul_zero, ite_eq_right (by omega)]
          · rw [hv'lo j (by omega), hv', Function.update_self, smul_dotProduct, dotProduct_comm,
              hvw j (by omega), smul_zero, ite_eq_right (by omega)]
          · rw [hv', Function.update_self, smul_dotProduct, dotProduct_smul, hww, ite_eq_left rfl,
              smul_eq_mul, smul_eq_mul]
            field_simp
        have hVV : Vᵀ * V = 1 :=
          basisCols_transpose_mul_self fun i hi j hj => horth' i (by omega) j (by omega)
        have hHs : H.IsSymm := by
          rw [Matrix.IsSymm, hH, Matrix.transpose_mul, Matrix.transpose_mul, hA.eq,
            Matrix.transpose_transpose, Matrix.mul_assoc]
        obtain ⟨hHt, htt1⟩ := hritz (k + 2) H hHs
        refine ⟨horth', fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj | rfl
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          obtain ⟨⟨c, hc⟩, hx1, hres⟩ := hcond j (by omega)
          refine ⟨⟨c, ?_⟩, hx1, fun i hi => ?_⟩
          · rw [hc]
            exact Finset.sum_congr rfl fun i _ => by rw [hv'lo i (by omega)]
          · rw [hv'lo i (by omega)]
            exact hres i hi
        · simp only [Function.update_self]
          refine ⟨⟨tt, by rw [hx', hV, basisCols_mulVec]⟩, ?_, fun i hi => ?_⟩
          · rw [hx', Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
              hVV, Matrix.one_mulVec, dotProduct_comm, htt1]
          · have hi' : v' i ⬝ᵥ (A *ᵥ x' - θ • x') =
                (Vᵀ *ᵥ (A *ᵥ x' - θ • x')) ⟨i, by omega⟩ :=
              (basisCols_transpose_mulVec_apply v' (k + 2) _ ⟨i, by omega⟩).symm
            rw [hi', Matrix.mulVec_sub, Matrix.mulVec_smul, hx', Matrix.mulVec_mulVec,
              Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hVV, Matrix.one_mulVec,
              Matrix.mul_assoc, ← hH, hHt, sub_self]
            rfl
  obtain ⟨-, hfin, hdone, hx0, -, hr, hrho, hdv, hortho⟩ := hP fuel
  refine ⟨?_, hx0, hr, hrho, hdv, fun hs => ?_⟩
  · rcases hfin with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [h] using hdone.symm)
  · obtain ⟨horth, hcond⟩ := hortho hs
    refine ⟨horth, fun j hj => ?_⟩
    obtain ⟨hc, hx1, hres⟩ := hcond j hj
    exact ⟨isRitzPair_of_cond hc hx1 hres, norm_toLp_eq_one hx1, hres⟩

/-- **Equation (10.6.16)** of [golub2013matrix], exact semantics: the claims of §10.6.3 about
Davidson's method. Let $A \in \mathbb{R}^{n \times n}$ be symmetric with $n \ge 1$, and let the
selector `ritz` return, for every symmetric $H \in \mathbb{R}^{p \times p}$, a pair
$(\theta, t)$ with $Ht = \theta t$ and $t^T t = 1$. Consider the final state of Davidson's
method in exact arithmetic with at most `fuel` passes, with 0-based indices: the counter $k$,
the basis $v_0, \dots, v_k$, the Ritz pairs $(\lambda_j, x_j)$, the corrections $\delta v_j$,
the residual $r$ and its norm $\rho$. Then:

* $k = \mathrm{fuel}$ or $\rho \le \mathrm{tol}$;
* $r = A x_k - \lambda_k x_k$ and $\rho = \|r\|_2$;
* for every $j < k$, if $a_{ii} \neq \lambda_j$ for all $i$, then $(M - \lambda_j I)\, \delta
  v_j = -(A x_j - \lambda_j x_j)$, where $M$ is the diagonal of $A$;
* if no orthogonalized correction $s$ has norm $0$, then $v_0, \dots, v_k$ are orthonormal
  ("$V_k$ is an $n$-by-$k$ matrix with orthonormal columns"), and for every $j \le k$,
  $(\lambda_j, x_j)$ is a Ritz pair of $A$ on $\operatorname{span}\{v_0, \dots, v_j\}$ and
  $v_i^T (A x_j - \lambda_j x_j) = 0$ for all $i \le j$ ("$r_k$ is orthogonal to the range of
  $V_k$ as required").

The hypothesis $n \ge 1$ makes the start $e_1$ a unit vector. A Ritz pair is
`Krylov.IsRitzPair`. The proof combines `GolubVanLoan.Chapter10.subspaceExpansion_spec` and
`GolubVanLoan.Chapter10.davidsonCorrection_spec`.

**Limitation.** The unit Ritz-vector hypothesis is quantified over all dimensions `p`. At `p =
0`, the only vector has squared norm zero, so the hypothesis cannot be satisfied. The iteration
only requests Ritz pairs of positive order.

**Reading.** Exact semantics vacuous under unit Ritz-vector requirement in dimension zero.
-/
theorem equation_10_6_16 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))}
    (hritz : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm →
      H *ᵥ (Id.run (ritz p H)).2 = (Id.run (ritz p H)).1 • (Id.run (ritz p H)).2 ∧
        (Id.run (ritz p H)).2 ⬝ᵥ (Id.run (ritz p H)).2 = 1)
    (hn : 0 < n) (tol : ℝ) (fuel : ℕ) :
    let s := Id.run (davidson pure A ritz tol fuel)
    (s.k = fuel ∨ s.rho ≤ tol) ∧ s.r = A *ᵥ s.x s.k - s.lam s.k • s.x s.k ∧
      s.rho = ‖(WithLp.toLp 2 s.r : EuclideanSpace ℝ (Fin n))‖ ∧
      (∀ j < s.k, (∀ i, A i i ≠ s.lam j) →
        (Matrix.diagonal (fun i => A i i) - s.lam j • 1) *ᵥ s.dv j =
          -(A *ᵥ s.x j - s.lam j • s.x j)) ∧
      ((∀ j < s.k, s.sNorm j ≠ 0) →
        (∀ i ≤ s.k, ∀ j ≤ s.k, s.v i ⬝ᵥ s.v j = if i = j then 1 else 0) ∧
        ∀ j ≤ s.k, Krylov.IsRitzPair (Matrix.toEuclideanLin A)
            (Submodule.span ℝ (Set.range fun i : Fin (j + 1) =>
              (WithLp.toLp 2 (s.v i) : EuclideanSpace ℝ (Fin n))))
            (s.lam j) (WithLp.toLp 2 (s.x j)) ∧
          ∀ i ≤ j, s.v i ⬝ᵥ (A *ᵥ s.x j - s.lam j • s.x j) = 0) := by
  intro s
  have he : (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0) ⬝ᵥ
      (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0) = 1 := by
    rw [dotProduct, Finset.sum_eq_single ⟨0, hn⟩
      (fun b _ hb => by rw [ite_eq_right (fun h => hb (Fin.ext h)), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  obtain ⟨hfin, -, hr, hrho, hdv, hortho⟩ :=
    subspaceExpansion_spec hA (fun _ l r => davidsonCorrection pure A l r) hritz he tol fuel
  set s' := Id.run (subspaceExpansion pure A (fun _ l r => davidsonCorrection pure A l r) ritz
    (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0) tol fuel) with hs'
  rw [show s = s' from rfl]
  refine ⟨hfin, hr, hrho, fun j hj hne => ?_, fun hs => ?_⟩
  · have h := hdv j hj
    simp only [davidsonCorrection_spec] at h
    ext i
    rw [h, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Matrix.mulVec_diagonal]
    have hi : A i i - s'.lam j ≠ 0 := sub_ne_zero.2 (hne i)
    field_simp
    ring
  · obtain ⟨horth, hcond⟩ := hortho hs
    exact ⟨horth, fun j hj => ⟨(hcond j hj).1, (hcond j hj).2.2⟩⟩

/-- A pass of the subspace expansion loop that has not stopped increases the counter, keeps the
earlier basis vectors, Ritz values and correction norms, and sets the new Ritz value to the
eigenvalue that the selector returns for $V^T A V$ with the enlarged basis $V$. -/
private theorem subspaceExpansionStep_facts (A : Matrix (Fin n) (Fin n) ℝ)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → Id (Fin n → ℝ))
    (ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))) (tol : ℝ)
    (s₀ : DavidsonState n) (hd : s₀.done = false) :
    (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).k = s₀.k + 1 ∧
      (∀ i ≤ s₀.k, (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).v i = s₀.v i) ∧
      (∀ j ≠ s₀.k + 1,
        (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).lam j = s₀.lam j) ∧
      (∀ j ≠ s₀.k,
        (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).sNorm j = s₀.sNorm j) ∧
      (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).lam (s₀.k + 1) =
        (Id.run (ritz (s₀.k + 2)
          ((basisCols (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).v
            (s₀.k + 2))ᵀ * (A * basisCols
              (Id.run (subspaceExpansionStep pure A correct ritz tol s₀)).v (s₀.k + 2))))).1 := by
  simp only [subspaceExpansionStep, hd, Bool.false_eq_true, ↓reduceIte, Id.run_bind,
    vecNorm_spec, vecDiv_spec, algorithm_1_1_5_spec, algorithm_1_1_3_spec,
    algorithm_1_1_2_spec, zero_add, Id.run_pure]
  refine ⟨by trivial, fun i hi => Function.update_of_ne (by omega) _ _,
    fun j hj => Function.update_of_ne hj _ _, fun j hj => Function.update_of_ne hj _ _, ?_⟩
  simp

/-- If $v_0, \dots, v_{k+1}$ are orthonormal, $x$ is a unit vector in the span of $v_0, \dots, v_k$,
and every Rayleigh quotient $y^T (V_{k+2}^T A V_{k+2}) y$ with $y^T y = 1$ is at most $\theta$,
then $x^T A x \le \theta$. -/
private theorem rayleigh_le_of_mem_span {A : Matrix (Fin n) (Fin n) ℝ}
    {v : ℕ → Fin n → ℝ} {k : ℕ}
    (hv : ∀ i ≤ k + 1, ∀ j ≤ k + 1, v i ⬝ᵥ v j = if i = j then 1 else 0)
    {x : Fin n → ℝ} (c : Fin (k + 1) → ℝ) (hx : x = ∑ i, c i • v i) (hx1 : x ⬝ᵥ x = 1)
    {θ : ℝ} (hθ : ∀ y : Fin (k + 2) → ℝ, y ⬝ᵥ y = 1 →
      y ⬝ᵥ (((basisCols v (k + 2))ᵀ * (A * basisCols v (k + 2))) *ᵥ y) ≤ θ) :
    x ⬝ᵥ (A *ᵥ x) ≤ θ := by
  set V := basisCols v (k + 2) with hV
  have hVV : Vᵀ * V = 1 :=
    basisCols_transpose_mul_self fun i hi j hj => hv i (by omega) j (by omega)
  set y : Fin (k + 2) → ℝ := Fin.snoc c 0 with hy
  have hVy : V *ᵥ y = x := by
    rw [hV, basisCols_mulVec, Fin.sum_univ_castSucc, hx]
    simp [hy]
  have hyy : y ⬝ᵥ y = x ⬝ᵥ x := by
    calc y ⬝ᵥ y = y ⬝ᵥ ((Vᵀ * V) *ᵥ y) := by rw [hVV, Matrix.one_mulVec]
      _ = x ⬝ᵥ x := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hVy]
  have hyHy : y ⬝ᵥ ((Vᵀ * (A * V)) *ᵥ y) = x ⬝ᵥ (A *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, hVy]
  rw [← hyHy]
  exact hθ y (by rw [hyy, hx1])

/-- A Ritz value $\lambda$ is the Rayleigh quotient $x^T A x$ of its unit Ritz vector $x$. -/
private theorem rayleigh_eq_of_residual {A : Matrix (Fin n) (Fin n) ℝ} {v : ℕ → Fin n → ℝ}
    {k : ℕ} {x : Fin n → ℝ} {l : ℝ} (c : Fin (k + 1) → ℝ) (hx : x = ∑ i, c i • v i)
    (hx1 : x ⬝ᵥ x = 1) (hres : ∀ i ≤ k, v i ⬝ᵥ (A *ᵥ x - l • x) = 0) :
    x ⬝ᵥ (A *ᵥ x) = l := by
  set w := A *ᵥ x - l • x with hw
  have h0 : x ⬝ᵥ w = 0 := by
    rw [hx, sum_dotProduct]
    exact Finset.sum_eq_zero fun i _ => by
      rw [smul_dotProduct, hres i (by omega), smul_zero]
  rw [hw, dotProduct_sub, dotProduct_smul, hx1, smul_eq_mul, mul_one, sub_eq_zero] at h0
  exact h0

/-- A vector in the span of $v_0, \dots, v_k$ is a linear combination $\sum_{i \le k} c_i v_i$. -/
private theorem exists_coeffs_of_mem_span {v : ℕ → Fin n → ℝ} {k : ℕ} {x : Fin n → ℝ}
    (h : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) ∈ Submodule.span ℝ
      (Set.range fun i : Fin (k + 1) => (WithLp.toLp 2 (v i) : EuclideanSpace ℝ (Fin n)))) :
    ∃ c : Fin (k + 1) → ℝ, x = ∑ i, c i • v i := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 h
  refine ⟨c, ?_⟩
  have := congrArg WithLp.ofLp hc
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul] at this
  exact this.symm

/-- Let $A \in \mathbb{R}^{n \times n}$ be symmetric, let $x_1^T x_1 = 1$, and let the selector
`ritz` return, for every symmetric $H$, a pair $(\theta, t)$ with $Ht = \theta t$, $t^T t = 1$,
and $y^T H y \le \theta$ for every $y$ with $y^T y = 1$. If no orthogonalized correction of the
exact subspace expansion loop has norm $0$, then for any correction step its Ritz values satisfy
$\lambda_j \le \lambda_{j+1}$ for every $j < k$.

**Limitation.** The unit Ritz-vector hypothesis is quantified over all dimensions `p`. At `p =
0`, the only vector has squared norm zero, so the hypothesis cannot be satisfied. The iteration
only requests Ritz pairs of positive order.

**Reading.** Adds largest Ritz selection monotonicity; unit Ritz-vector premise at dimension zero
impossible.
-/
theorem subspaceExpansion_ritzValue_mono {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (correct : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → Id (Fin n → ℝ))
    {ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))}
    (hritz : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm →
      H *ᵥ (Id.run (ritz p H)).2 = (Id.run (ritz p H)).1 • (Id.run (ritz p H)).2 ∧
        (Id.run (ritz p H)).2 ⬝ᵥ (Id.run (ritz p H)).2 = 1)
    (hmax : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm → ∀ y : Fin p → ℝ, y ⬝ᵥ y = 1 →
      y ⬝ᵥ (H *ᵥ y) ≤ (Id.run (ritz p H)).1)
    {x₁ : Fin n → ℝ} (hx₁ : x₁ ⬝ᵥ x₁ = 1) (tol : ℝ) (fuel : ℕ) :
    (∀ j < (Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)).k,
        (Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)).sNorm j ≠ 0) →
      ∀ j < (Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)).k,
        (Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)).lam j ≤
          (Id.run (subspaceExpansion pure A correct ritz x₁ tol fuel)).lam (j + 1) := by
  induction fuel with
  | zero =>
    intro _ j hj
    simp only [subspaceExpansion, Id.run_bind, List.range_zero, List.foldlM_nil,
      Id.run_pure] at hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ t ih =>
    intro hs j hj
    have hspec1 := (subspaceExpansion_spec hA correct hritz hx₁ tol (t + 1)).2.2.2.2.2 hs
    rw [subspaceExpansion_succ] at hs hj hspec1 ⊢
    set s₀ := Id.run (subspaceExpansion pure A correct ritz x₁ tol t) with hs₀
    cases hd : s₀.done with
    | true =>
      simp only [subspaceExpansionStep, hd, ↓reduceIte, Id.run_pure] at hs hj ⊢
      exact ih hs j hj
    | false =>
      obtain ⟨hk, hv, hlam, hsn, hθ⟩ := subspaceExpansionStep_facts A correct ritz tol s₀ hd
      set s := Id.run (subspaceExpansionStep pure A correct ritz tol s₀) with hsdef
      rw [hk] at hj hs hspec1
      have hs₀n : ∀ j < s₀.k, s₀.sNorm j ≠ 0 := fun j hj' => by
        rw [← hsn j (by omega)]; exact hs j (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hlam j (by omega), hlam (j + 1) (by omega)]
        exact ih hs₀n j hj
      · rw [hlam _ (by omega), hθ]
        obtain ⟨-, hcond⟩ := (subspaceExpansion_spec hA correct hritz hx₁ tol t).2.2.2.2.2 hs₀n
        obtain ⟨hR, hn1, hres⟩ := hcond s₀.k le_rfl
        obtain ⟨c, hc⟩ := exists_coeffs_of_mem_span hR.mem
        have hx1 : s₀.x s₀.k ⬝ᵥ s₀.x s₀.k = 1 := by
          have h2 := real_inner_self_eq_norm_sq
            (WithLp.toLp 2 (s₀.x s₀.k) : EuclideanSpace ℝ (Fin n))
          rw [EuclideanSpace.inner_toLp_toLp, star_trivial, hn1, one_pow] at h2
          rw [dotProduct_comm]; exact h2
        rw [← rayleigh_eq_of_residual c hc hx1 hres]
        have hH : ((basisCols s.v (s₀.k + 2))ᵀ * (A * basisCols s.v (s₀.k + 2))).IsSymm := by
          rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, hA.eq,
            Matrix.transpose_transpose, Matrix.mul_assoc]
        refine rayleigh_le_of_mem_span (hspec1.1) c ?_ hx1 (hmax _ _ hH)
        rw [hc]
        exact Finset.sum_congr rfl fun i _ => by rw [hv i (by omega)]

/-- Monotonicity of the Ritz values of Davidson's method (10.6.16) of [golub2013matrix]. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric with $n \ge 1$, and let the selector `ritz` return,
for every symmetric $H$, a pair $(\theta, t)$ with $Ht = \theta t$ and $t^T t = 1$ whose
eigenvalue is the largest Rayleigh quotient: $y^T H y \le \theta$ for every $y$ with
$y^T y = 1$. If no orthogonalized correction of the exact run has norm $0$, then the Ritz values
satisfy $\lambda_j \le \lambda_{j+1}$ for every $j < k$.

The source does not state this result. It holds because $x_k \in \operatorname{ran} V_k
\subseteq \operatorname{ran} V_{k+1}$ and $\lambda_k = x_k^T A x_k$. The proof specializes
`GolubVanLoan.Chapter10.subspaceExpansion_ritzValue_mono`.

**Limitation.** The unit Ritz-vector hypothesis is quantified over all dimensions `p`. At `p =
0`, the only vector has squared norm zero, so the hypothesis cannot be satisfied. The iteration
only requests Ritz pairs of positive order.

**Reading.** Largest Ritz monotonicity specialization retains impossible zero-order premise.
-/
theorem davidson_ritzValue_mono {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))}
    (hritz : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm →
      H *ᵥ (Id.run (ritz p H)).2 = (Id.run (ritz p H)).1 • (Id.run (ritz p H)).2 ∧
        (Id.run (ritz p H)).2 ⬝ᵥ (Id.run (ritz p H)).2 = 1)
    (hmax : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm → ∀ y : Fin p → ℝ, y ⬝ᵥ y = 1 →
      y ⬝ᵥ (H *ᵥ y) ≤ (Id.run (ritz p H)).1)
    (hn : 0 < n) (tol : ℝ) (fuel : ℕ) :
    (∀ j < (Id.run (davidson pure A ritz tol fuel)).k,
        (Id.run (davidson pure A ritz tol fuel)).sNorm j ≠ 0) →
      ∀ j < (Id.run (davidson pure A ritz tol fuel)).k,
        (Id.run (davidson pure A ritz tol fuel)).lam j ≤
          (Id.run (davidson pure A ritz tol fuel)).lam (j + 1) := by
  have he : (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0) ⬝ᵥ
      (fun i : Fin n => if (i : ℕ) = 0 then (1 : ℝ) else 0) = 1 := by
    rw [dotProduct, Finset.sum_eq_single ⟨0, hn⟩
      (fun b _ hb => by rw [ite_eq_right (fun h => hb (Fin.ext h)), zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  exact subspaceExpansion_ritzValue_mono hA (fun _ l r => davidsonCorrection pure A l r) hritz
    hmax he tol fuel

/-- **Section 10.6.4** of [golub2013matrix], exact semantics of the Jacobi–Davidson framework. Let
$A, M \in \mathbb{R}^{n \times n}$ with $A$ symmetric, and let the starting vector satisfy
$x_1^T x_1 = 1$. Let the selector `ritz` return, for every symmetric
$H \in \mathbb{R}^{p \times p}$, a pair $(\theta, t)$ with $Ht = \theta t$ and $t^T t = 1$. Let
the solver `solve`, called at $(x, \lambda, r)$ with $x^T x = 1$ and $x^T r = 0$, return a
Jacobi–Davidson correction (10.6.19) for $x$, $\lambda$, $r$ and $M$. Consider the final state
of the framework in exact arithmetic with at most `fuel` passes, with 0-based indices: the
counter $k$, the basis $v_0, \dots, v_k$, the Ritz pairs $(\lambda_j, x_j)$, the corrections
$\delta v_j$, the residual $r$ and its norm $\rho$. Then:

* $k = \mathrm{fuel}$ or $\rho \le \mathrm{tol}$;
* $r = A x_k - \lambda_k x_k$;
* if no orthogonalized correction $s$ has norm $0$, then $v_0, \dots, v_k$ are orthonormal; for
  every $j \le k$, $(\lambda_j, x_j)$ is a Ritz pair of $A$ on
  $\operatorname{span}\{v_0, \dots, v_j\}$ and $v_i^T (A x_j - \lambda_j x_j) = 0$ for all
  $i \le j$; and for every $j < k$, $\delta v_j$ is a Jacobi–Davidson correction for $x_j$,
  $\lambda_j$, $A x_j - \lambda_j x_j$ and $M$, and $x_j^T \delta v_j = 0$.

The last claim is the remark of the source that "the Jacobi–Davidson method insists that
$\delta x_c$ be orthogonal to the current eigenvector approximation".

The proof applies `GolubVanLoan.Chapter10.subspaceExpansion_spec`. Its Ritz conditions give
$x_j^T x_j = 1$ and $x_j^T r_j = 0$, so the hypothesis on the solver applies at every pass.

**Limitation.** The unit Ritz-vector hypothesis is quantified over all dimensions `p`. At `p =
0`, the only vector has squared norm zero, so the hypothesis cannot be satisfied. The iteration
only requests Ritz pairs of positive order.

**Correction.** Symmetric case, with global correction solver and impossible unit Ritz-vector
premise at dimension zero.
-/
theorem jacobiDavidson_spec {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    {M : Matrix (Fin n) (Fin n) ℝ} {solve : (Fin n → ℝ) → ℝ → (Fin n → ℝ) → Id (Fin n → ℝ)}
    (hsolve : ∀ x l r, x ⬝ᵥ x = 1 → x ⬝ᵥ r = 0 →
      IsJDCorrection M (WithLp.toLp 2 x) l (WithLp.toLp 2 r) (WithLp.toLp 2 (Id.run (solve x l r))))
    {ritz : (p : ℕ) → Matrix (Fin p) (Fin p) ℝ → Id (ℝ × (Fin p → ℝ))}
    (hritz : ∀ p (H : Matrix (Fin p) (Fin p) ℝ), H.IsSymm →
      H *ᵥ (Id.run (ritz p H)).2 = (Id.run (ritz p H)).1 • (Id.run (ritz p H)).2 ∧
        (Id.run (ritz p H)).2 ⬝ᵥ (Id.run (ritz p H)).2 = 1)
    {x₁ : Fin n → ℝ} (hx₁ : x₁ ⬝ᵥ x₁ = 1) (tol : ℝ) (fuel : ℕ) :
    let s := Id.run (jacobiDavidson pure A solve ritz x₁ tol fuel)
    (s.k = fuel ∨ s.rho ≤ tol) ∧ s.r = A *ᵥ s.x s.k - s.lam s.k • s.x s.k ∧
      ((∀ j < s.k, s.sNorm j ≠ 0) →
        (∀ i ≤ s.k, ∀ j ≤ s.k, s.v i ⬝ᵥ s.v j = if i = j then 1 else 0) ∧
        (∀ j ≤ s.k, Krylov.IsRitzPair (Matrix.toEuclideanLin A)
            (Submodule.span ℝ (Set.range fun i : Fin (j + 1) =>
              (WithLp.toLp 2 (s.v i) : EuclideanSpace ℝ (Fin n))))
            (s.lam j) (WithLp.toLp 2 (s.x j)) ∧
          ∀ i ≤ j, s.v i ⬝ᵥ (A *ᵥ s.x j - s.lam j • s.x j) = 0) ∧
        ∀ j < s.k, IsJDCorrection M (WithLp.toLp 2 (s.x j)) (s.lam j)
            (WithLp.toLp 2 (A *ᵥ s.x j - s.lam j • s.x j)) (WithLp.toLp 2 (s.dv j)) ∧
          s.x j ⬝ᵥ s.dv j = 0) := by
  intro s
  obtain ⟨hfin, -, hr, -, hdv, hortho⟩ :=
    subspaceExpansion_spec hA solve hritz hx₁ tol fuel
  set s' := Id.run (subspaceExpansion pure A solve ritz x₁ tol fuel) with hs'
  rw [show s = s' from rfl]
  refine ⟨hfin, hr, fun hs => ?_⟩
  obtain ⟨horth, hcond⟩ := hortho hs
  have hcorr : ∀ j < s'.k, IsJDCorrection M (WithLp.toLp 2 (s'.x j)) (s'.lam j)
      (WithLp.toLp 2 (A *ᵥ s'.x j - s'.lam j • s'.x j)) (WithLp.toLp 2 (s'.dv j)) := by
    intro j hj
    obtain ⟨hR, hx1, hres⟩ := hcond j (by omega)
    have hx1' : s'.x j ⬝ᵥ s'.x j = 1 := by
      have h2 := real_inner_self_eq_norm_sq (WithLp.toLp 2 (s'.x j) : EuclideanSpace ℝ (Fin n))
      rw [EuclideanSpace.inner_toLp_toLp, star_trivial, hx1, one_pow] at h2
      exact h2
    have hxr : s'.x j ⬝ᵥ (A *ᵥ s'.x j - s'.lam j • s'.x j) = 0 := by
      have h := hR.residual_mem_orthogonal
      rw [Submodule.mem_orthogonal] at h
      have h' := h _ hR.mem
      rwa [Matrix.toEuclideanLin_toLp, ← WithLp.toLp_smul, ← WithLp.toLp_sub,
        EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] at h'
    rw [hdv j hj]
    exact hsolve _ _ _ hx1' hxr
  refine ⟨horth, fun j hj => ⟨(hcond j hj).1, (hcond j hj).2.2⟩, fun j hj => ⟨hcorr j hj, ?_⟩⟩
  have h := (hcorr j hj).1
  rwa [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] at h

/-! ### The trace-min principle (§10.6.5) -/

/-- **Section 10.6.5** of [golub2013matrix], the trace-min principle of Sameh and Wisniewski. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric, let $B \in \mathbb{R}^{n \times n}$ be symmetric
positive definite, and let $k \le n$. Let $\mu_1 \le \cdots \le \mu_n$ be the eigenvalues of the
pencil $A - \lambda B$. Then
$$\min\{\operatorname{tr}(V^T A V) : V \in \mathbb{R}^{n \times k},\ V^T B V = I_k\} = \mu_1 +
  \cdots + \mu_k,$$
and the minimum is attained at a matrix $V_{\mathrm{opt}}$ with
$V_{\mathrm{opt}}^T B V_{\mathrm{opt}} = I_k$ and $V_{\mathrm{opt}}^T A V_{\mathrm{opt}} =
\operatorname{diag}(\mu_k, \dots, \mu_1)$, whose column $j$ satisfies $A V_{\mathrm{opt}}(:,
j) = \mu_{k+1-j} B V_{\mathrm{opt}}(:, j)$.

**Correction.** The source says that if $V_{\mathrm{opt}}$ solves the problem, then
$V_{\mathrm{opt}}^T A V_{\mathrm{opt}} = \operatorname{diag}(\mu_1, \dots, \mu_k)$. This holds
for some minimizer but not for every one: for every orthogonal $Q \in \mathbb{R}^{k \times k}$,
$V_{\mathrm{opt}} Q$ is also a minimizer. The theorem states that a minimizer with a diagonal
$V_{\mathrm{opt}}^T A V_{\mathrm{opt}}$ exists.

The pencil eigenvalues are `Matrix.pencilEigenvalues`, sorted in decreasing order, so
$\mu_1, \dots, \mu_k$ are its last $k$ entries, and the columns of $V_{\mathrm{opt}}$ come in
decreasing order of their eigenvalues; reversing them gives the order
$\operatorname{diag}(\mu_1, \dots, \mu_k)$ of the source. The theorem is the real case of
`Matrix.isLeast_re_trace_conjTranspose_mul_mul`. -/
theorem isLeast_trace_transpose_mul_mul {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hB : B.PosDef) {k : ℕ} (hkn : k ≤ n) :
    let μ := Matrix.pencilEigenvalues (Matrix.isHermitian_iff_isSymm.mpr hA) hB
    let low : Fin k → ℝ := fun i => μ ⟨i + (n - k), by rw [Fintype.card_fin]; omega⟩
    IsLeast {t | ∃ V : Matrix (Fin n) (Fin k) ℝ, Vᵀ * B * V = 1 ∧ t = (Vᵀ * A * V).trace}
        (∑ i, low i) ∧
      ∃ V : Matrix (Fin n) (Fin k) ℝ, Vᵀ * B * V = 1 ∧ Vᵀ * A * V = Matrix.diagonal low ∧
        ∀ j, A *ᵥ V.col j = low j • (B *ᵥ V.col j) := by
  intro μ low
  have hlow : ∀ i : Fin k, Matrix.pencilEigenvalues (Matrix.isHermitian_iff_isSymm.mpr hA) hB
      ⟨i + (Fintype.card (Fin n) - k), by rw [Fintype.card_fin]; omega⟩ = low i := fun i => by
    simp only [low, μ, Fintype.card_fin]
  have h := Matrix.isLeast_re_trace_conjTranspose_mul_mul (Matrix.isHermitian_iff_isSymm.mpr hA) hB
    (k := k) (by rw [Fintype.card_fin]; exact hkn)
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.re_to_real,
    RCLike.ofReal_real_eq_id, id, hlow] at h
  exact h

end GolubVanLoan.Chapter10
