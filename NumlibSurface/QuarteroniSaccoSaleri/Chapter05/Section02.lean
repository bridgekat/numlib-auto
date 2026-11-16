/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Numlib.Eigen.ReducedResolvent
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section01

/-!
# Quarteroni, Sacco and Saleri, Section 5.2: Stability and Conditioning Analysis

This module formalizes Section 5.2 of [quarteroni2000numerical], on the sensitivity of the
eigenvalues and eigenvectors of $A \in \mathbb{C}^{n \times n}$ to perturbations. The Bauer–Fike
theorem (Theorem 5.3) bounds the distance from an eigenvalue of $A + E$ to the spectrum of a
diagonalizable $A$ by $K_2(X) \|E\|_2$, where $X$ diagonalizes $A$; for a normal $A$ the bound is
$\|E\|_2$ (5.9). For a simple eigenvalue $\lambda$ with unit right and left eigenvectors $x$ and
$y$, the derivative of the eigenvalue of $A + \varepsilon E$ at $\varepsilon = 0$ is at most
$1 / |y^H x|$ when $\|E\|_2 = 1$ (Theorem 5.4), which defines the condition number
$\kappa(\lambda) = 1 / |y^H x|$ (5.11). Property 5.5 bounds the first-order change of an eigenvector
of a Hermitian matrix by $\|E\|_2$ divided by the distance to the rest of the spectrum. The a
posteriori estimates of Section 5.2.2 bound the error of an approximate eigenpair
$(\hat\lambda, \hat x)$ by its residual $\hat r = A \hat x - \hat\lambda \hat x$ (Theorem 5.5 and
Properties 5.6 and 5.7).

The proofs specialize the backbone modules `Numlib.Eigen.Perturbation` (the Bauer–Fike theorem, the
condition number of a simple eigenvalue, the derivative of an eigenvalue along a branch, and the
residual bounds for Hermitian matrices) and `Numlib.Eigen.ReducedResolvent` (the derivative of an
eigenvector along a branch and the condition number of an eigenvector).

## Main definitions

* Equation (5.11), `QuarteroniSaccoSaleri.Chapter05.equation_5_11`: the condition number
  $\kappa(\lambda) = 1 / |y^H x|$ of an eigenvalue.

## Main results

* Section 5.2, `QuarteroniSaccoSaleri.Chapter05.inner_toEuclideanLin_eq_of_conjTranspose_eq`: a left
  eigenvector in the sense of the book is a left eigenvector in the sense of the backbone.
* Theorem 5.3, `QuarteroniSaccoSaleri.Chapter05.theorem_5_3`: the Bauer–Fike theorem in the
  $2$-norm.
* Equation (5.9), `QuarteroniSaccoSaleri.Chapter05.equation_5_9`: for a normal $A$, every eigenvalue
  of $A + E$ is within $\|E\|_2$ of $\sigma(A)$.
* Theorem 5.4, `QuarteroniSaccoSaleri.Chapter05.theorem_5_4`: along a differentiable branch through
  a simple eigenvalue, $|\partial \lambda / \partial \varepsilon (0)| \le 1 / |y^H x|$.
* Theorem 5.4, `QuarteroniSaccoSaleri.Chapter05.theorem_5_4_branch`: at a simple eigenvalue, a
  differentiable branch exists, with $\partial \lambda / \partial \varepsilon (0) = y^H E x / y^H
  x$.
* Theorem 5.4, `QuarteroniSaccoSaleri.Chapter05.theorem_5_4_inner_ne_zero`: at a simple eigenvalue,
  $y^H x \neq 0$.
* Equation (5.11), `QuarteroniSaccoSaleri.Chapter05.equation_5_11_eq_eigenvalueCondNumber`: for unit
  vectors, $\kappa(\lambda)$ is the backbone's condition number of an eigenvalue.
* Equation (5.11), `QuarteroniSaccoSaleri.Chapter05.equation_5_11_one_le`: $\kappa(\lambda) \ge 1$.
* Equation (5.11), `QuarteroniSaccoSaleri.Chapter05.equation_5_11_normal`: for a normal $A$,
  $\kappa(\lambda) = 1$.
* Section 5.2.1, `QuarteroniSaccoSaleri.Chapter05.eigenvalueCondNumber_conj_unitary`: a unitary
  similarity does not change $\kappa(\lambda)$.
* Property 5.5, `QuarteroniSaccoSaleri.Chapter05.property_5_5`: for a Hermitian $A$, the derivative
  of the eigenvector is at most $\|E\|_2 / \delta_k$.
* Theorem 5.5, `QuarteroniSaccoSaleri.Chapter05.theorem_5_5`: for a Hermitian $A$, some eigenvalue
  is within $\|\hat r\|_2 / \|\hat x\|_2$ of $\hat\lambda$.
* Property 5.6, `QuarteroniSaccoSaleri.Chapter05.property_5_6`: for a Hermitian $A$, the distance
  from $\hat x$ to a span of eigenvectors is at most $\|\hat r\|_2 / \delta$.
* Property 5.7, `QuarteroniSaccoSaleri.Chapter05.property_5_7`: for a diagonalizable $A$,
  $\|\hat r\|_2 \le \varepsilon \|\hat x\|_2$ gives an eigenvalue within
  $\varepsilon \|X^{-1}\|_2 \|X\|_2$ of $\hat\lambda$.

## Conventions

* The book works in $\mathbb{C}^{n \times n}$ with the Euclidean norm. Matrices are
  `Matrix (Fin n) (Fin n) ℂ`, and vectors are elements of `EuclideanSpace ℂ (Fin n)`, on which
  matrices act through `Matrix.toEuclideanLin`. The norm $\|\cdot\|_2$ of matrices is Mathlib's
  scoped `Matrix.Norms.L2Operator` norm, and $K_2(X) = \|X\|_2 \|X^{-1}\|_2$ is
  `NormedRing.condNumber X` in this norm.
* A right eigenvector satisfies $Ax = \lambda x$. A left eigenvector, $y^H A = \lambda y^H$, is
  written $A^H y = \bar\lambda y$, that is `toEuclideanLin Aᴴ y = star λ • y`. The number $y^H x$ is
  the inner product `inner ℂ y x`.
* A simple eigenvalue has algebraic multiplicity one (Section 1.7):
  `A.charpoly.rootMultiplicity λ = 1`. Mathlib's `LinearMap.finrank_maxGenEigenspace_eq` identifies
  this multiplicity with the dimension of the generalized eigenspace, with which the backbone works
  (`Matrix.finrank_maxGenEigenspace_toEuclideanLin`).
* A diagonalizable matrix is given by $X^{-1} A X = \operatorname{diag}(d)$ with $X$ nonsingular.
* The perturbation parameter $\varepsilon$ of Theorem 5.4 and Property 5.5 is a complex number $t$,
  and the real $\varepsilon \ge 0$ of the book is its restriction. A branch $\lambda(\varepsilon)$,
  $x(\varepsilon)$ is a pair of functions `mu : ℂ → ℂ` and `v : ℂ → EuclideanSpace ℂ (Fin n)` with
  `HasDerivAt` at $0$.

## Deviations from the source

* **Theorem 5.4** (generalization). The book assumes that $A$ is diagonalizable. The statement needs
  only the differentiable branch, which `QuarteroniSaccoSaleri.Chapter05.theorem_5_4_branch`
  supplies at a simple eigenvalue. See `QuarteroniSaccoSaleri.Chapter05.theorem_5_4`.
* **Property 5.5, the matrix** (correction). For a matrix that is not normal, the constant
  $1 / \min_{j \neq k} |\lambda_k - \lambda_j|$ is false. The property is stated for a Hermitian
  $A$. See `QuarteroniSaccoSaleri.Chapter05.property_5_5`.
* **Property 5.5, the remainder** (correction). The remainder $O(\varepsilon^2)$ needs a twice
  differentiable branch, which the hypotheses do not give. The property is stated with
  $o(\varepsilon)$. See `QuarteroniSaccoSaleri.Chapter05.property_5_5`.
* **Property 5.5, the normalization** (reading). The normalization $\|x_k(\varepsilon)\|_2 = 1$ is
  replaced by $x_k^H x_k(\varepsilon) = 1$. The two differ by a factor $1 + O(\varepsilon^2)$. See
  `QuarteroniSaccoSaleri.Chapter05.property_5_5`.
* **Property 5.6** (generalization). The hypothesis $|\lambda_i - \hat\lambda| \le \|\hat r\|_2$ for
  $i = 1, \dots, m$ plays no role and is dropped. See
  `QuarteroniSaccoSaleri.Chapter05.property_5_6`.

## Not formalized

* **Theorem 5.3 in a $p$-norm with $p \neq 2$.** The book states it for any matrix $p$-norm.
* **The floating-point estimate (5.12).**
* **Example 5.2.**
-/

open Filter Matrix Topology
open scoped Matrix.Norms.L2Operator

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ}

/-! ### Bridges between the matrix and the operator vocabulary -/

/-- Let $A \in \mathbb{C}^{n \times n}$, $\lambda \in \mathbb{C}$ and $y \in \mathbb{C}^n$. If $y$
is a left eigenvector of $A$ in the sense of the book, $y^H A = \lambda y^H$, written
$A^H y = \bar\lambda y$, then it is a left eigenvector in the sense of the backbone: $\langle y,
Az \rangle = \lambda \langle y, z \rangle$ for every $z \in \mathbb{C}^n$. -/
theorem inner_toEuclideanLin_eq_of_conjTranspose_eq {A : Matrix (Fin n) (Fin n) ℂ} {lam : ℂ}
    {y : EuclideanSpace ℂ (Fin n)} (hy : toEuclideanLin Aᴴ y = star lam • y)
    (z : EuclideanSpace ℂ (Fin n)) : inner ℂ y (toEuclideanLin A z) = lam * inner ℂ y z := by
  rw [← toEuclideanLin_conjTranspose_inner_left, hy, inner_smul_left]
  simp

/-! ### Theorem 5.3: Bauer–Fike -/

/-- **Theorem 5.3** of [quarteroni2000numerical] (Bauer–Fike), (5.8), for $p = 2$. Let
$A \in \mathbb{C}^{n \times n}$ be diagonalizable, $X^{-1} A X = D =
\operatorname{diag}(\lambda_1, \dots, \lambda_n)$ with $X$ nonsingular, so that the columns of
$X$ are right eigenvectors of $A$. Let $E \in \mathbb{C}^{n \times n}$ and let $\mu$ be an
eigenvalue of $A + E$. Then
$$\min_{\lambda \in \sigma(A)} |\lambda - \mu| \le K_2(X) \, \|E\|_2,$$
where $K_2(X) = \|X\|_2 \|X^{-1}\|_2$ is the condition number of the eigenvalue problem for $A$.

The minimum is stated as the existence of $\lambda \in \sigma(A)$ with
$|\lambda - \mu| \le K_2(X) \|E\|_2$. The proof specializes the backbone's `Matrix.bauer_fike`:
the eigenvalue that attains the minimum is a diagonal entry of $D$, and $\sigma(A) = \sigma(D)$
by similarity. The book states the theorem for any matrix $p$-norm, and only $p = 2$ is
formalized. -/
theorem theorem_5_3 {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) {d : Fin n → ℂ}
    (hD : X⁻¹ * A * X = diagonal d) (E : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ lam ∈ spectrum ℂ A, ‖lam - μ‖ ≤ NormedRing.condNumber X * ‖E‖ := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hA : A = X * diagonal d * X⁻¹ := by
    rw [← hD, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.mul_one,
      ← Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.one_mul]
  obtain ⟨i, hi⟩ := bauer_fike X d hX E (hA ▸ hμ)
  refine ⟨d i, ?_, by rwa [norm_sub_rev]⟩
  have hspec := spectrum.units_conjugate' (R := ℂ) (a := A) (u := hX.unit)
  rw [coe_units_inv, IsUnit.unit_spec, hD, spectrum_diagonal] at hspec
  rw [← hspec]
  exact ⟨i, rfl⟩

/-- **Equation (5.9)** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$ be normal
and $E \in \mathbb{C}^{n \times n}$. Then for every eigenvalue $\mu$ of $A + E$,
$$\min_{\lambda \in \sigma(A)} |\lambda - \mu| \le \|E\|_2.$$
So the eigenvalue problem of a normal matrix is well conditioned with respect to the absolute
error.

For a normal $A$, the matrix $X$ of Theorem 5.3 is unitary, so $K_2(X) = 1$. The proof applies
`QuarteroniSaccoSaleri.Chapter05.theorem_5_3` with the spectral theorem for normal matrices
(`Matrix.IsStarNormal.spectral_theorem`) and `Matrix.condNumber_l2_of_mem_unitaryGroup`. -/
theorem equation_5_9 {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A)
    (E : Matrix (Fin n) (Fin n) ℂ) {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ lam ∈ spectrum ℂ A, ‖lam - μ‖ ≤ ‖E‖ := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · have : Subsingleton (Matrix (Fin n) (Fin n) ℂ) := ⟨fun _ _ => by ext i; exact isEmptyElim i⟩
    simp [spectrum.of_subsingleton] at hμ
  obtain ⟨U, hU, d, hd⟩ := Matrix.IsStarNormal.spectral_theorem.mp hA
  have hUinv : U⁻¹ = Uᴴ := inv_eq_left_inv (mem_unitaryGroup_iff'.mp hU)
  obtain ⟨lam, hlam, h⟩ :=
    theorem_5_3 (X := U) ⟨Unitary.toUnits ⟨U, hU⟩, rfl⟩ (hUinv ▸ hd) E hμ
  exact ⟨lam, hlam, by rwa [condNumber_l2_of_mem_unitaryGroup hU, one_mul] at h⟩

/-! ### Theorem 5.4: the first-order perturbation of a simple eigenvalue -/

/-- **Theorem 5.4** of [quarteroni2000numerical], (5.10). Let $A, E \in \mathbb{C}^{n \times n}$
with $\|E\|_2 = 1$, and let $\lambda$ be a simple eigenvalue of $A$ with right and left
eigenvectors $x$ and $y$, $Ax = \lambda x$ and $y^H A = \lambda y^H$, with
$\|x\|_2 = \|y\|_2 = 1$. Let $\lambda(\varepsilon) \in \mathbb{C}$ and
$x(\varepsilon) \in \mathbb{C}^n$ be differentiable at $\varepsilon = 0$, with
$\lambda(0) = \lambda$, $x(0) = x$, and $(A + \varepsilon E) x(\varepsilon) =
\lambda(\varepsilon) x(\varepsilon)$ for all $\varepsilon$ in a neighborhood of $0$. Then
$$\left| \frac{\partial \lambda}{\partial \varepsilon}(0) \right| \le \frac{1}{|y^H x|}.$$

**Generalization.** The book assumes that $A$ is diagonalizable. This hypothesis is not needed:
the statement needs only the differentiable branch, which
`QuarteroniSaccoSaleri.Chapter05.theorem_5_4_branch` supplies at a simple eigenvalue.

The parameter $\varepsilon$ is complex. The proof specializes the backbone's
`Module.End.norm_deriv_eigenvalue_perturbation_le`, with `Module.End.eigenvalueCondNumber ℂ x y`
$= 1 / |y^H x|$ for unit vectors, and $y^H x \neq 0$ by
`QuarteroniSaccoSaleri.Chapter05.theorem_5_4_inner_ne_zero`. -/
theorem theorem_5_4 {A E : Matrix (Fin n) (Fin n) ℂ} (hE : ‖E‖ = 1) {lam : ℂ}
    {x y : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hAx : toEuclideanLin A x = lam • x) (hAy : toEuclideanLin Aᴴ y = star lam • y)
    (hsimple : A.charpoly.rootMultiplicity lam = 1) {mu : ℂ → ℂ}
    {v : ℂ → EuclideanSpace ℂ (Fin n)} {v' : EuclideanSpace ℂ (Fin n)} {mu' : ℂ}
    (hv : HasDerivAt v v' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ᶠ t in 𝓝 0, toEuclideanLin (A + t • E) (v t) = mu t • v t) (hlam : mu 0 = lam)
    (hv0 : v 0 = x) : ‖mu'‖ ≤ 1 / ‖inner ℂ y x‖ := by
  have hne : inner ℂ y x ≠ 0 :=
    Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one hAx (by simp [← norm_pos_iff, hx])
      (inner_toEuclideanLin_eq_of_conjTranspose_eq hAy) (by simp [← norm_pos_iff, hy])
      (by rw [finrank_maxGenEigenspace_toEuclideanLin]; exact hsimple)
  have h := Module.End.norm_deriv_eigenvalue_perturbation_le
    (A := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) (B := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) E)
    hv hmu (heig.mono fun t ht => by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] at ht
      exact ht)
    (inner_toEuclideanLin_eq_of_conjTranspose_eq hAy) hlam (by rwa [hv0])
  rw [l2_opNorm_toEuclideanCLM, hE, one_mul, Module.End.eigenvalueCondNumber, hv0, hx, hy,
    one_mul] at h
  exact h

/-- **Theorem 5.4** of [quarteroni2000numerical], the branch that it presupposes. Let
$A, E \in \mathbb{C}^{n \times n}$, and let $\lambda$ be a simple eigenvalue of $A$ with a right
eigenvector $x \neq 0$ and a left eigenvector $y \neq 0$. Then there are functions
$\lambda(\varepsilon) \in \mathbb{C}$ and $x(\varepsilon) \in \mathbb{C}^n$ of
$\varepsilon \in \mathbb{C}$ with $\lambda(0) = \lambda$, $x(0) = x$, and $(A + \varepsilon E)
x(\varepsilon) = \lambda(\varepsilon) x(\varepsilon)$ for all $\varepsilon$ in a neighborhood of
$0$, such that $x(\varepsilon)$ is differentiable at $0$ and
$$\frac{\partial \lambda}{\partial \varepsilon}(0) = \frac{y^H E x}{y^H x}.$$
This is the identity that the proof of the book derives.

The proof specializes the backbone's
`Module.End.hasDerivAt_eigenvalue_perturbation_of_finrank_eq_one`, which builds the branch by
the inverse function theorem rather than by the continuity of the roots of the characteristic
polynomial. -/
theorem theorem_5_4_branch {A : Matrix (Fin n) (Fin n) ℂ} (E : Matrix (Fin n) (Fin n) ℂ) {lam : ℂ}
    {x y : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0) (hy : y ≠ 0)
    (hAx : toEuclideanLin A x = lam • x) (hAy : toEuclideanLin Aᴴ y = star lam • y)
    (hsimple : A.charpoly.rootMultiplicity lam = 1) :
    ∃ (mu : ℂ → ℂ) (v : ℂ → EuclideanSpace ℂ (Fin n)) (v' : EuclideanSpace ℂ (Fin n)),
      mu 0 = lam ∧ v 0 = x ∧
        (∀ᶠ t in 𝓝 0, toEuclideanLin (A + t • E) (v t) = mu t • v t) ∧
        HasDerivAt v v' 0 ∧
        HasDerivAt mu (inner ℂ y (toEuclideanLin E x) / inner ℂ y x) 0 := by
  obtain ⟨mu, v, v', h0, hv0, heig, hv, hmu⟩ :=
    Module.End.hasDerivAt_eigenvalue_perturbation_of_finrank_eq_one
      (A := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) (B := toEuclideanCLM (n := Fin n) (𝕜 := ℂ) E)
      hAx hx (inner_toEuclideanLin_eq_of_conjTranspose_eq hAy) hy
      (by rw [coe_toEuclideanCLM_eq_toEuclideanLin, finrank_maxGenEigenspace_toEuclideanLin]
          exact hsimple)
  refine ⟨mu, v, v', h0, hv0, heig.mono fun t ht => ?_, hv, hmu⟩
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  exact ht

/-- **Theorem 5.4** of [quarteroni2000numerical], the first step of its proof. Let $\lambda$ be a
simple eigenvalue of $A \in \mathbb{C}^{n \times n}$, with a right eigenvector $x \neq 0$ and a
left eigenvector $y \neq 0$. Then $y^H x \neq 0$.

The proof specializes the backbone's
`Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one`, which needs no diagonalizability.
The book argues through the biorthogonality of the columns of $X$ and $Y = X^{-H}$. -/
theorem theorem_5_4_inner_ne_zero {A : Matrix (Fin n) (Fin n) ℂ} {lam : ℂ}
    {x y : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0) (hy : y ≠ 0)
    (hAx : toEuclideanLin A x = lam • x) (hAy : toEuclideanLin Aᴴ y = star lam • y)
    (hsimple : A.charpoly.rootMultiplicity lam = 1) : inner ℂ y x ≠ 0 :=
  Module.End.inner_ne_zero_of_finrank_maxGenEigenspace_eq_one hAx hx
    (inner_toEuclideanLin_eq_of_conjTranspose_eq hAy) hy
    (by rw [finrank_maxGenEigenspace_toEuclideanLin]; exact hsimple)

/-! ### Equation (5.11): the condition number of an eigenvalue -/

/-- **Equation (5.11)** of [quarteroni2000numerical]. Let $x, y \in \mathbb{C}^n$ be unit right and
left eigenvectors of an eigenvalue $\lambda$. The **condition number** of $\lambda$ is
$$\kappa(\lambda) = \frac{1}{|y^H x|} = \frac{1}{|\cos \theta_\lambda|},$$
where $\theta_\lambda$ is the angle between $y$ and $x$.

The definition takes any two vectors $x$ and $y$. Its value is $0$ when $y^H x = 0$. -/
noncomputable def equation_5_11 (x y : EuclideanSpace ℂ (Fin n)) : ℝ := 1 / ‖inner ℂ y x‖

/-- For unit vectors $x, y \in \mathbb{C}^n$, the condition number $\kappa(\lambda) = 1 / |y^H x|$
of (5.11) equals the backbone's `Module.End.eigenvalueCondNumber ℂ x y`, which is
$\|x\| \|y\| / |\langle y, x \rangle|$. -/
theorem equation_5_11_eq_eigenvalueCondNumber {x y : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ = 1)
    (hy : ‖y‖ = 1) : equation_5_11 x y = Module.End.eigenvalueCondNumber ℂ x y := by
  rw [equation_5_11, Module.End.eigenvalueCondNumber, hx, hy, one_mul]

/-- **Equation (5.11)** of [quarteroni2000numerical], $\kappa(\lambda) \ge 1$. Let
$x, y \in \mathbb{C}^n$ with $\|x\|_2 = \|y\|_2 = 1$ and $y^H x \neq 0$. Then
$1 \le \kappa(\lambda)$.

The condition $y^H x \neq 0$ holds at a simple eigenvalue
(`QuarteroniSaccoSaleri.Chapter05.theorem_5_4_inner_ne_zero`). The proof specializes the
backbone's `Module.End.one_le_eigenvalueCondNumber`, which is the Cauchy–Schwarz inequality. -/
theorem equation_5_11_one_le {x y : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hne : inner ℂ y x ≠ 0) : 1 ≤ equation_5_11 x y := by
  rw [equation_5_11_eq_eigenvalueCondNumber hx hy]
  exact Module.End.one_le_eigenvalueCondNumber hne

/-- **Equation (5.11)** of [quarteroni2000numerical], the normal case. Let
$A \in \mathbb{C}^{n \times n}$ be normal, and let $\lambda$ be a simple eigenvalue of $A$ with
unit right and left eigenvectors $x$ and $y$. Then $\kappa(\lambda) = 1$.

The left and right eigenvectors of a simple eigenvalue of a normal matrix are equal up to a
scalar, so $\kappa(\lambda) = 1 / \|x\|_2^2 = 1$. The proof specializes the backbone's
`Module.End.eigenvalueCondNumber_eq_one_of_isStarNormal`, which asks for geometric simplicity.
The algebraic simplicity of the book implies it (`Module.End.finrank_eigenspace_le`). -/
theorem equation_5_11_normal {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A) {lam : ℂ}
    {x y : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hAx : toEuclideanLin A x = lam • x) (hAy : toEuclideanLin Aᴴ y = star lam • y)
    (hsimple : A.charpoly.rootMultiplicity lam = 1) : equation_5_11 x y = 1 := by
  have hx0 : x ≠ 0 := by simp [← norm_pos_iff, hx]
  have hgeom : Module.finrank ℂ (Module.End.eigenspace (toEuclideanLin A) lam) = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← hsimple, ← finrank_maxGenEigenspace_toEuclideanLin]
      exact Submodule.finrank_mono (Module.End.eigenspace_le_maxGenEigenspace)
    · exact Submodule.one_le_finrank_iff.mpr
        ((Submodule.ne_bot_iff _).mpr ⟨x, Module.End.mem_eigenspace_iff.mpr hAx, hx0⟩)
  rw [equation_5_11_eq_eigenvalueCondNumber hx hy]
  exact Module.End.eigenvalueCondNumber_eq_one_of_isStarNormal
    (isStarNormal_toEuclideanLin_iff.mpr hA) hAx hx0
    (by rw [← toEuclideanLin_conjTranspose_eq_adjoint]; exact hAy) (by simp [← norm_pos_iff, hy])
    hgeom

/-- **Section 5.2.1** of [quarteroni2000numerical], after (5.11): a unitary similarity preserves the
conditioning. Let $A, U \in \mathbb{C}^{n \times n}$ with $U$ unitary, and let
$\tilde A = U^H A U$. If $x$ and $y$ are right and left eigenvectors of $A$ for $\lambda$, then
$U^H x$ and $U^H y$ are right and left eigenvectors of $\tilde A$ for $\lambda$, and the
condition number does not change:
$$\tilde\kappa(\lambda) = |y^H U U^H x|^{-1} = \kappa(\lambda).$$

A unitary matrix changes neither Euclidean lengths nor the angles between vectors. -/
theorem eigenvalueCondNumber_conj_unitary {A U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ unitaryGroup (Fin n) ℂ) {lam : ℂ} {x y : EuclideanSpace ℂ (Fin n)}
    (hAx : toEuclideanLin A x = lam • x) (hAy : toEuclideanLin Aᴴ y = star lam • y) :
    toEuclideanLin (Uᴴ * A * U) (toEuclideanLin Uᴴ x) = lam • toEuclideanLin Uᴴ x ∧
      toEuclideanLin (Uᴴ * A * U)ᴴ (toEuclideanLin Uᴴ y) = star lam • toEuclideanLin Uᴴ y ∧
      equation_5_11 (toEuclideanLin Uᴴ x) (toEuclideanLin Uᴴ y) = equation_5_11 x y := by
  have hUU : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  refine ⟨?_, ?_, ?_⟩
  · simp only [toEuclideanLin_mul_apply]
    rw [← toEuclideanLin_mul_apply U, hUU, toEuclideanLin_one, LinearMap.id_apply, hAx, map_smul]
  · simp only [conjTranspose_mul, conjTranspose_conjTranspose, toEuclideanLin_mul_apply]
    rw [← toEuclideanLin_mul_apply U, hUU, toEuclideanLin_one, LinearMap.id_apply, hAy, map_smul]
  · have hU' : Uᴴ ∈ unitaryGroup (Fin n) ℂ := Unitary.star_mem hU
    simp only [equation_5_11]
    rw [← inner_toLp_mulVec_of_mem_unitaryGroup hU' (WithLp.ofLp y) (WithLp.ofLp x)]
    rfl

/-! ### Property 5.5: the first-order perturbation of an eigenvector -/

/-- **Property 5.5** of [quarteroni2000numerical], for a Hermitian matrix. Let
$A, E \in \mathbb{C}^{n \times n}$ with $A$ Hermitian, let $\lambda_k \in \mathbb{R}$ be a
simple eigenvalue of $A$ with unit eigenvector $x_k$, and let $\delta_k = \min_{j \neq k}
|\lambda_k - \lambda_j|$ be the distance from $\lambda_k$ to the rest of the spectrum. Let
$\varepsilon \mapsto (\lambda_k(\varepsilon), x_k(\varepsilon))$ be a branch of eigenpairs of
$A(\varepsilon) = A + \varepsilon E$ for all $\varepsilon \in \mathbb{C}$, differentiable at
$\varepsilon = 0$, with $\lambda_k(0) = \lambda_k$, $x_k(0) = x_k$ and
$x_k^H x_k(\varepsilon) = 1$ for all $\varepsilon$. Then
$$\left\| \frac{\partial x_k}{\partial \varepsilon}(0) \right\|_2 \le
  \frac{\|E\|_2}{\delta_k},$$
and hence, as $\varepsilon \to 0$,
$$\|x_k(\varepsilon) - x_k\|_2 \le |\varepsilon| \frac{\|E\|_2}{\delta_k} + o(\varepsilon).$$
The number $\kappa(x_k) = 1 / \delta_k$ is the condition number of the eigenvector.

**Correction.** The book states the property for any matrix, with the remainder
$O(\varepsilon^2)$. For a matrix that is not normal, the constant $1 / \delta_k$ is false: the
first-order constant is the norm of the reduced resolvent (`Module.End.eigenvectorCondNumber`).
So the property is stated for a Hermitian $A$. The remainder $O(\varepsilon^2)$ needs a twice
differentiable branch, which the hypotheses do not give, so the statement uses $o(\varepsilon)$.

**Reading.** The book normalizes by $\|x_k(\varepsilon)\|_2 = 1$. The statement uses the
normalization $x_k^H x_k(\varepsilon) = 1$, which differs from it by a factor
$1 + O(\varepsilon^2)$. The branch is quantified over every $\varepsilon$, as the book
quantifies $x_k(\varepsilon)$.

The number $\delta_k$ is `Metric.infDist (lam : ℂ) (spectrum ℂ A \ {(lam : ℂ)})`, where `lam` is
$\lambda_k$. If $\lambda_k$ is the only eigenvalue, then $\delta_k = 0$ and, since Lean divides
by zero to zero, the bound says that the derivative is $0$. The proof specializes the backbone's
`Module.End.norm_deriv_eigenvector_perturbation_le`, whose normalization is the
spectral-projector normalization $P x_k(\varepsilon) = x_k$
(`Module.End.spectralProjector_apply_of_finrank_eq_one`), with
`Module.End.eigenvectorCondNumber_eq_inv_dist_of_isSymmetric` for the constant. The
$o(\varepsilon)$ form is `HasDerivAt.isLittleO`. -/
theorem property_5_5 {A E : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) {lam : ℝ}
    {x : EuclideanSpace ℂ (Fin n)} (hx : ‖x‖ = 1) (hAx : toEuclideanLin A x = (lam : ℂ) • x)
    (hsimple : A.charpoly.rootMultiplicity (lam : ℂ) = 1) {δ : ℝ}
    (hδ : δ = Metric.infDist (lam : ℂ) (spectrum ℂ A \ {(lam : ℂ)})) {mu : ℂ → ℂ}
    {v : ℂ → EuclideanSpace ℂ (Fin n)} {v' : EuclideanSpace ℂ (Fin n)} {mu' : ℂ}
    (hv : HasDerivAt v v' 0) (hmu : HasDerivAt mu mu' 0)
    (heig : ∀ t, toEuclideanLin (A + t • E) (v t) = mu t • v t) (hlam : mu 0 = lam)
    (hv0 : v 0 = x) (hnorm : ∀ t, inner ℂ x (v t) = 1) :
    ‖v'‖ ≤ ‖E‖ / δ ∧
      ∃ o : ℂ → ℝ, o =o[𝓝 0] (fun ε : ℂ => ε) ∧ ∀ ε, ‖v ε - x‖ ≤ ‖ε‖ * (‖E‖ / δ) + o ε := by
  have hx0 : x ≠ 0 := by simp [← norm_pos_iff, hx]
  have hAy : toEuclideanLin Aᴴ x = star (lam : ℂ) • x := by rwa [hA.eq, Complex.star_def,
    Complex.conj_ofReal]
  set A' : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A with hA'
  set E' : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    toEuclideanCLM (n := Fin n) (𝕜 := ℂ) E with hE'
  have hA'lin : (A' : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = toEuclideanLin A :=
    rfl
  have hsimple' : Module.finrank ℂ (Module.End.maxGenEigenspace
      (A' : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (lam : ℂ)) = 1 := by
    rw [hA'lin, finrank_maxGenEigenspace_toEuclideanLin]
    exact hsimple
  have hAx' : (A' : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) x = (lam : ℂ) • x := by
    rw [hA'lin]; exact hAx
  have hw' : ∀ z, inner ℂ x ((A' : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) z) =
      (lam : ℂ) * inner ℂ x z := fun z => by
    rw [hA'lin]; exact inner_toEuclideanLin_eq_of_conjTranspose_eq hAy z
  have hP : ∀ t, Module.End.spectralProjector
      (A' : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (· = (lam : ℂ)) (v t) = v 0 :=
    fun t => by
      rw [Module.End.spectralProjector_apply_of_finrank_eq_one hAx' hx0 hw' hx0 hsimple', hnorm,
        inner_self_eq_norm_sq_to_K, hx, hv0]
      simp
  have hbound : ‖v'‖ ≤ ‖E‖ / δ := by
    have h := Module.End.norm_deriv_eigenvector_perturbation_le (A := A') (B := E') hv hmu
      (fun t => by
        have ht := heig t
        rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] at ht
        exact ht) hlam hP
    rw [hA'lin, Module.End.eigenvectorCondNumber_eq_inv_dist_of_isSymmetric
      (isSymmetric_toEuclideanLin_iff.mpr hA), spectrum_toLpLin, hE',
      l2_opNorm_toEuclideanCLM, hv0, hx, mul_one, ← hδ] at h
    rwa [div_eq_inv_mul]
  refine ⟨hbound, fun ε => ‖v ε - x - ε • v'‖, ?_, fun ε => ?_⟩
  · have h := hv.isLittleO
    simpa [hv0] using h.norm_left
  · calc ‖v ε - x‖ = ‖ε • v' + (v ε - x - ε • v')‖ := by congr 1; abel
      _ ≤ ‖ε • v'‖ + ‖v ε - x - ε • v'‖ := norm_add_le _ _
      _ ≤ ‖ε‖ * (‖E‖ / δ) + ‖v ε - x - ε • v'‖ := by
          rw [norm_smul]
          gcongr

/-! ### Section 5.2.2: a posteriori estimates -/

/-- **Theorem 5.5** of [quarteroni2000numerical], (5.13). Let $A \in \mathbb{C}^{n \times n}$ be
Hermitian, and let $(\hat\lambda, \hat x)$ with $\hat\lambda \in \mathbb{R}$ and
$\hat x \in \mathbb{C}^n$, $\hat x \neq 0$, be an approximation of an eigenpair, with residual
$\hat r = A \hat x - \hat\lambda \hat x$. Then
$$\min_{\lambda_i \in \sigma(A)} |\hat\lambda - \lambda_i| \le \frac{\|\hat r\|_2}{\|\hat
  x\|_2}.$$

The minimum is stated as the existence of an eigenvalue that satisfies the bound. The
approximation $\hat\lambda$ of the book is real, as a Rayleigh quotient of a Hermitian matrix.
The proof specializes the backbone's `LinearMap.IsSymmetric.exists_hasEigenvalue_dist_le` for
`Matrix.toEuclideanLin A`, whose eigenvalues are the spectrum of $A$. -/
theorem theorem_5_5 {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (lam : ℝ)
    {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0) :
    ∃ μ ∈ spectrum ℂ A, ‖(lam : ℂ) - μ‖ ≤ ‖toEuclideanLin A x - (lam : ℂ) • x‖ / ‖x‖ := by
  obtain ⟨μ, hμ, h⟩ :=
    (isSymmetric_toEuclideanLin_iff.mpr hA).exists_hasEigenvalue_dist_le lam hx
  exact ⟨μ, (hasEigenvalue_toEuclideanLin_iff A μ).mp hμ, by rwa [norm_sub_rev]⟩

/-- **Property 5.6** of [quarteroni2000numerical], (5.15). Let $A \in \mathbb{C}^{n \times n}$ be
Hermitian with orthonormal eigenvectors $u_i$ and eigenvalues $\lambda_i$, let
$\hat\lambda \in \mathbb{R}$ and $\hat x \in \mathbb{C}^n$, and let
$\hat r = A \hat x - \hat\lambda \hat x$. Let $s$ be a set of indices and $\delta > 0$, and
suppose that $|\lambda_i - \hat\lambda| \ge \delta$ for every $i \notin s$. Then the Euclidean
distance from $\hat x$ to the space $U_m$ spanned by the $u_i$ with $i \in s$ satisfies
$$d(\hat x, U_m) \le \frac{\|\hat r\|_2}{\delta}.$$

**Generalization.** The book also assumes $|\lambda_i - \hat\lambda| \le \|\hat r\|_2$ for
$i \in s$. This hypothesis plays no role and is dropped. The hypothesis $\hat x \neq 0$ of
Theorem 5.5 is not needed either.

The book takes $s = \{1, \dots, m\}$. The eigenvectors and eigenvalues are Mathlib's
`Matrix.IsHermitian.eigenvectorBasis` and `Matrix.IsHermitian.eigenvalues`. The proof
specializes the backbone's `LinearMap.IsSymmetric.dist_eigenvectorSpan_le_norm_residual_div`;
the distance is attained at the orthogonal projection (`Submodule.starProjection_minimal`). -/
theorem property_5_6 {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (lam : ℝ)
    (x : EuclideanSpace ℂ (Fin n)) (s : Finset (Fin n)) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∉ s, δ ≤ |hA.eigenvalues i - lam|) :
    Metric.infDist x (Submodule.span ℂ (hA.eigenvectorBasis '' s) : Set (EuclideanSpace ℂ (Fin n)))
      ≤ ‖toEuclideanLin A x - (lam : ℂ) • x‖ / δ := by
  set hA' := isSymmetric_toEuclideanLin_iff.mpr hA
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have hspan : Submodule.span ℂ (hA.eigenvectorBasis '' s) =
      hA'.eigenvectorSpan finrank_euclideanSpace (s.map e.symm.toEmbedding) := by
    rw [LinearMap.IsSymmetric.eigenvectorSpan, Finset.coe_map, Set.image_image]
    congr 1
    refine Set.image_congr fun i _ => ?_
    simp only [Matrix.IsHermitian.eigenvectorBasis, OrthonormalBasis.reindex_apply]
    rfl
  rw [hspan]
  refine (Metric.infDist_le_dist_of_mem
    (Submodule.starProjection_apply_mem (hA'.eigenvectorSpan finrank_euclideanSpace
      (s.map e.symm.toEmbedding)) x)).trans ?_
  rw [dist_eq_norm]
  refine hA'.dist_eigenvectorSpan_le_norm_residual_div finrank_euclideanSpace _ lam x hδ
    fun i hi => ?_
  have hi' : e i ∉ s := fun h => hi (Finset.mem_map.mpr ⟨e i, h, e.symm_apply_apply i⟩)
  have h := hsep (e i) hi'
  rwa [show hA.eigenvalues (e i) = hA'.eigenvalues finrank_euclideanSpace i from
    congrArg (hA'.eigenvalues finrank_euclideanSpace) (e.symm_apply_apply i)] at h

/-- **Property 5.7** of [quarteroni2000numerical]. Let $A \in \mathbb{C}^{n \times n}$ be
diagonalizable, $X^{-1} A X = \operatorname{diag}(\lambda_1, \dots, \lambda_n)$ with $X$
nonsingular. Let $\hat\lambda \in \mathbb{C}$ and $\hat x \in \mathbb{C}^n$ with
$\hat x \neq 0$, and let $\varepsilon \in \mathbb{R}$. If the residual
$\hat r = A \hat x - \hat\lambda \hat x$ satisfies $\|\hat r\|_2 \le \varepsilon \|\hat x\|_2$,
then
$$\min_{\lambda_i \in \sigma(A)} |\hat\lambda - \lambda_i| \le \varepsilon \, \|X^{-1}\|_2
  \|X\|_2.$$

The book takes $\varepsilon > 0$. The hypothesis is not needed, because the bound on the
residual forces $\varepsilon \ge 0$. The proof applies the backbone's
`Matrix.bauer_fike_residual` to the unit vector $\hat x / \|\hat x\|_2$. -/
theorem property_5_7 {A X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X) {d : Fin n → ℂ}
    (hD : X⁻¹ * A * X = diagonal d) (lam : ℂ) {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0)
    {ε : ℝ} (hr : ‖toEuclideanLin A x - lam • x‖ ≤ ε * ‖x‖) :
    ∃ μ ∈ spectrum ℂ A, ‖lam - μ‖ ≤ ε * (‖X⁻¹‖ * ‖X‖) := by
  have hdet := (isUnit_iff_isUnit_det X).mp hX
  have hA : A = X * diagonal d * X⁻¹ := by
    rw [← hD, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.mul_one,
      ← Matrix.mul_assoc, mul_nonsing_inv X hdet, Matrix.one_mul]
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖(‖x‖⁻¹ : ℂ) • x‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxn,
      inv_mul_cancel₀ hxn.ne']
  obtain ⟨i, hi⟩ := bauer_fike_residual X d hX hu lam
  refine ⟨d i, ?_, ?_⟩
  · have hspec := spectrum.units_conjugate' (R := ℂ) (a := A) (u := hX.unit)
    rw [coe_units_inv, IsUnit.unit_spec, hD, spectrum_diagonal] at hspec
    rw [← hspec]
    exact ⟨i, rfl⟩
  · have hres : ‖toEuclideanLin (X * diagonal d * X⁻¹) ((‖x‖⁻¹ : ℂ) • x) - lam • (‖x‖⁻¹ : ℂ) • x‖
        ≤ ε := by
      rw [← hA, map_smul, smul_comm lam, ← smul_sub, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hxn, inv_mul_le_iff₀ hxn, mul_comm]
      exact hr
    calc ‖lam - d i‖ ≤ NormedRing.condNumber X *
          ‖toEuclideanLin (X * diagonal d * X⁻¹) ((‖x‖⁻¹ : ℂ) • x) - lam • (‖x‖⁻¹ : ℂ) • x‖ := hi
      _ ≤ NormedRing.condNumber X * ε :=
          mul_le_mul_of_nonneg_left hres (NormedRing.condNumber_nonneg X)
      _ = ε * (‖X⁻¹‖ * ‖X‖) := by
          rw [NormedRing.condNumber, ← nonsing_inv_eq_ringInverse]
          ring

end QuarteroniSaccoSaleri.Chapter05
