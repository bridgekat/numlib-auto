/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Preconditioner.ConstraintPencil

/-!
# Benzi, Golub and Liesen, Section 10.2: Constraint and indefinite preconditioning

This module formalizes the generalized eigenvalue problem (10.21) and Lemma 10.2 of
[benzi2005numerical]. Let $B \in \mathbb{R}^{m \times n}$, $C \in \mathbb{R}^{m \times m}$ and
$E \in \mathbb{R}^{n \times n}$. The problem asks for $\gamma \in \mathbb{C}$ and $(x, y) \neq 0$
with
$$\begin{bmatrix} E & 0 \\ 0 & 0 \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix} = \gamma
  \begin{bmatrix} I & B^T \\ B & -C \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix}.$$
Lemma 10.2 describes its eigenvalues when $B$ has rank $m$ and $C$ is positive semidefinite. A
nonzero eigenvalue is a Rayleigh quotient of $E$, the eigenvalue $0$ occurs exactly when $Ex = 0$,
and the nonzero eigenvalues are real and lie between $\min\{0, \lambda_{\min}(E)\}$ and
$\max\{0, \lambda_{\max}(E)\}$. The zero eigenspace is the product of $\ker E$ and the whole
multiplier space $\mathbb{C}^m$. The proofs specialize results in
`Numlib.Preconditioner.ConstraintPencil`.

## Main definitions

* Equation (10.21), `BenziGolubLiesen.IsConstraintPencilEigenvector`: $(\gamma, x, y)$ is an
  eigenpair of the generalized eigenvalue problem above.

## Main results

* Lemma 10.2(i), `BenziGolubLiesen.lemma_10_2_i`: if $C$ is positive definite and $Ex \neq 0$, then
  $\gamma = x^H E x / x^H (I + B^T C^{-1} B) x$ and $\gamma \neq 0$.
* Lemma 10.2(ii), `BenziGolubLiesen.lemma_10_2_ii`: $\gamma = 0$ if and only if $Ex = 0$, and the
  kernel of $\operatorname{diag}(E, 0)$ has dimension $\dim \ker E + m$.
* Lemma 10.2(iii), `BenziGolubLiesen.lemma_10_2_iii`: for symmetric $E$, a nonzero eigenvalue is
  real and lies in $[\min\{0, \lambda_{\min}(E)\}, \max\{0, \lambda_{\max}(E)\}]$.
* Counterexample for Lemma 10.2(ii), `BenziGolubLiesen.lemma_10_2_zero_multiplier_example`: for
  $B = C = 1$ and $E = 0$, the eigenvalue $0$ has an eigenvector with $y = 0$.
* Counterexample for Lemma 10.2(iii), `BenziGolubLiesen.lemma_10_2_upper_endpoint_example`: for
  $B = C = 1$ and $E = -1$, the eigenvalue $-1/2$ exceeds $\lambda_{\max}(E) = -1$.

## Implementation notes

* Eigenvalues and eigenvectors are complex. The real matrices act on complex vectors through
  `Matrix.complexify` and `Matrix.map Complex.ofReal`, and $B^T$ is the conjugate transpose of the
  complexified $B$.
* The numbers $\lambda_{\min}(E)$ and $\lambda_{\max}(E)$ are the infimum and the supremum of
  `Matrix.IsHermitian.eigenvalues`.

## Deviations from the source

* **Lemma 10.2(i)–(ii)** (generalization). The Rayleigh formula and zero-eigenvalue
  characterization hold for nonsymmetric $E$ as well. See `BenziGolubLiesen.lemma_10_2_i`
  and `BenziGolubLiesen.lemma_10_2_ii`.
* **Lemma 10.2(ii)** (correction). The source requires $y \neq 0$ for the eigenvalue $0$. The
  condition is $Ex = 0$ alone, with $y$ arbitrary as long as $(x, y) \neq 0$. See
  `BenziGolubLiesen.lemma_10_2_ii`.
* **Lemma 10.2(iii)** (correction). The source prints the upper bound $\lambda_{\max}(E)$. The upper
  bound is $\max\{0, \lambda_{\max}(E)\}$. See `BenziGolubLiesen.lemma_10_2_iii`.
-/

namespace BenziGolubLiesen

open Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]
variable {B : Matrix m n ℝ} {C : Matrix m m ℝ} {E : Matrix n n ℝ}
variable {γ : ℂ} {x : n → ℂ} {y : m → ℂ}

/-- **Equation (10.21)** of [benzi2005numerical]. Let $B \in \mathbb{R}^{m \times n}$,
$C \in \mathbb{R}^{m \times m}$ and $E \in \mathbb{R}^{n \times n}$. A scalar
$\gamma \in \mathbb{C}$ and vectors $x \in \mathbb{C}^n$, $y \in \mathbb{C}^m$ form an
**eigenpair of the constraint pencil** if $(x, y) \neq 0$ and
$$\begin{bmatrix} E & 0 \\ 0 & 0 \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix} = \gamma
  \begin{bmatrix} I & B^T \\ B & -C \end{bmatrix} \begin{bmatrix} x \\ y \end{bmatrix}.$$

The problem is read over the complex numbers: $\gamma$, $x$ and $y$ are complex. The definition
is `Matrix.HasPencilEigenvector` for the two block matrices, with the real matrices embedded
entrywise in the complex matrices, and the pair $(x, y)$ is `Sum.elim x y`. -/
abbrev IsConstraintPencilEigenvector (B : Matrix m n ℝ) (C : Matrix m m ℝ)
    (E : Matrix n n ℝ) (γ : ℂ) (x : n → ℂ) (y : m → ℂ) : Prop :=
  Matrix.HasPencilEigenvector (fromBlocks E.complexify 0 0 0)
    (fromBlocks 1 (B.map Complex.ofReal)ᴴ (B.map Complex.ofReal) (-C.complexify)) γ (Sum.elim x y)

/-- **Lemma 10.2(i)** of [benzi2005numerical]. Let $B \in \mathbb{R}^{m \times n}$ have rank $m$,
let $C \in \mathbb{R}^{m \times m}$ be symmetric positive definite, and let
$E \in \mathbb{R}^{n \times n}$. If $(\gamma, x, y)$ is an eigenpair of the constraint pencil
(10.21) and $Ex \neq 0$, then
$$\gamma = \frac{x^H E x}{x^H (I + B^T C^{-1} B) x} \quad \text{and} \quad \gamma \neq 0.$$
The formula follows by eliminating the multiplier $y$.

**Generalization.** The source assumes $E=E^T$. The formula only uses the block
eigenvalue equations, so $E$ need not be symmetric.

The eigenpair is `BenziGolubLiesen.IsConstraintPencilEigenvector`. The proof specializes
`Matrix.HasPencilEigenvector.primalBlock_eq_rayleigh`. -/
theorem lemma_10_2_i [DecidableEq m] (hB : B.rank = Fintype.card m) (hC : C.PosDef)
    (h : IsConstraintPencilEigenvector B C E γ x y) (hEx : E.complexify *ᵥ x ≠ 0) :
    γ = (star x ⬝ᵥ (E.complexify *ᵥ x)) /
      (star x ⬝ᵥ ((1 + (B.map Complex.ofReal)ᴴ * C.complexify⁻¹ *
        (B.map Complex.ofReal)) *ᵥ x)) ∧ γ ≠ 0 :=
  h.primalBlock_eq_rayleigh (mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank hB)
    (posDef_complexify_iff.mpr hC) hEx

/-- **Lemma 10.2(ii)** of [benzi2005numerical], corrected. Let $B \in \mathbb{R}^{m \times n}$ have
rank $m$, let $C \in \mathbb{R}^{m \times m}$ be symmetric positive semidefinite, and let
$E \in \mathbb{R}^{n \times n}$. If $(\gamma, x, y)$ is an eigenpair of the constraint pencil
(10.21), then $\gamma = 0$ if and only if $Ex = 0$. Moreover, the eigenspace of the eigenvalue
$0$ has dimension $\dim \ker E + m$:
$$\dim \ker \begin{bmatrix} E & 0 \\ 0 & 0 \end{bmatrix} = \dim \ker E + m,$$
with the kernels taken over $\mathbb{C}$.

**Correction.** The source requires $y \neq 0$ for the eigenvalue $0$. The multiplier $y$ is
arbitrary: only $(x, y) \neq 0$ is needed, and $y = 0$ is possible when $x \neq 0$. For
$B = C = 1$ and $E = 0$, the triple $(0, 1, 0)$ is an eigenpair; see
`BenziGolubLiesen.lemma_10_2_zero_multiplier_example`.

**Generalization.** The source assumes $E=E^T$. The zero-eigenvalue characterization
and kernel dimension also hold for nonsymmetric $E$.

The eigenpair is `BenziGolubLiesen.IsConstraintPencilEigenvector`, and $\ker E$ is the kernel of
`Matrix.complexify E`. The proof specializes
`Matrix.HasPencilEigenvector.primalBlock_eq_zero_iff` and
`Matrix.finrank_ker_fromBlocks_primal`. -/
theorem lemma_10_2_ii (hB : B.rank = Fintype.card m) (hC : C.PosSemidef)
    (h : IsConstraintPencilEigenvector B C E γ x y) :
    (γ = 0 ↔ E.complexify *ᵥ x = 0) ∧
    Module.finrank ℂ (LinearMap.ker
      (fromBlocks E.complexify 0 0 (0 : Matrix m m ℂ)).mulVecLin) =
      Module.finrank ℂ (LinearMap.ker E.complexify.mulVecLin) + Fintype.card m :=
  ⟨h.primalBlock_eq_zero_iff (mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank hB)
      hC.complexify,
    finrank_ker_fromBlocks_primal E.complexify⟩

/-- **Lemma 10.2(iii)** of [benzi2005numerical], corrected. Let $B \in \mathbb{R}^{m \times n}$ have
rank $m$, let $C \in \mathbb{R}^{m \times m}$ be symmetric positive semidefinite, and let
$E \in \mathbb{R}^{n \times n}$ be symmetric, with $n \ge 1$. If $(\gamma, x, y)$ is an
eigenpair of the constraint pencil (10.21) and $\gamma \neq 0$, then $\gamma$ is real and
$$\min\{0, \lambda_{\min}(E)\} \le \gamma \le \max\{0, \lambda_{\max}(E)\}.$$

**Correction.** The source prints the upper bound $\lambda_{\max}(E)$. This bound fails when
$\lambda_{\max}(E) < 0$: for $B = C = 1$ and $E = -1$, the pencil has the eigenvalue
$\gamma = -1/2 > -1$. See `BenziGolubLiesen.lemma_10_2_upper_endpoint_example`.

The eigenpair is `BenziGolubLiesen.IsConstraintPencilEigenvector`. The numbers
$\lambda_{\min}(E)$ and $\lambda_{\max}(E)$ are the infimum and the supremum of
`Matrix.IsHermitian.eigenvalues`. The proof specializes
`Matrix.HasPencilEigenvector.primalBlock_mem_interval`. -/
theorem lemma_10_2_iii [Nonempty n] (hB : B.rank = Fintype.card m) (hC : C.PosSemidef)
    (hE : E.IsHermitian) (h : IsConstraintPencilEigenvector B C E γ x y) (hγ : γ ≠ 0) :
    γ ∈ Complex.ofReal '' Set.Icc (min 0 (⨅ i, hE.eigenvalues i))
      (max 0 (⨆ i, hE.eigenvalues i)) := by
  have hEc : E.complexify.IsHermitian := (isHermitian_complexify_iff _).mpr hE
  have hbounds := hEc.isSymmetricBoundedBy_toEuclideanLin
    (lmin := ⨅ i, hE.eigenvalues i) (lmax := ⨆ i, hE.eigenvalues i)
  refine h.primalBlock_mem_interval (mulVec_injective_conjTranspose_map_ofReal_of_fullRowRank hB)
    hC.complexify (hbounds fun i ↦ ?_) hγ
  have hμ := (ofReal_mem_spectrum_complexify_iff E (hEc.eigenvalues i)).mp
    (hEc.eigenvalues_mem_spectrum_real i)
  rw [hE.spectrum_real_eq_range_eigenvalues] at hμ
  obtain ⟨j, hj⟩ := hμ
  rw [← hj]
  exact ⟨ciInf_le (Set.finite_range _).bddBelow j, le_ciSup (Set.finite_range _).bddAbove j⟩

/-- A counterexample to the condition $y \neq 0$ printed in Lemma 10.2(ii) of [benzi2005numerical].
For $n = m = 1$, $B = 1$, $C = 1$ and $E = 0$, the triple $(\gamma, x, y) = (0, 1, 0)$ is an
eigenpair of the constraint pencil (10.21). So the eigenvalue $0$ has an eigenvector whose
multiplier component is zero. -/
theorem lemma_10_2_zero_multiplier_example :
    IsConstraintPencilEigenvector (1 : Matrix Unit Unit ℝ) 1 0 0
      (fun _ ↦ 1) (fun _ ↦ 0) := by
  constructor
  · intro h
    have h0 := congrFun h (Sum.inl ())
    norm_num at h0
  · simp

/-- A counterexample to the upper bound printed in Lemma 10.2(iii) of [benzi2005numerical]. For
$n = m = 1$, $B = 1$, $C = 1$ and $E = -1$, the triple $(\gamma, x, y) = (-1/2, 1, 1)$ is an
eigenpair of the constraint pencil (10.21), and the only eigenvalue of $E$ is $-1$. So the
nonzero eigenvalue $-1/2$ exceeds the printed upper bound $\lambda_{\max}(E) = -1$.

The index type of the scalar case is `Unit`, and the spectrum of $E$ is `spectrum ℝ`. -/
theorem lemma_10_2_upper_endpoint_example :
    IsConstraintPencilEigenvector (1 : Matrix Unit Unit ℝ) 1 (-1) (-1 / 2)
      (fun _ ↦ 1) (fun _ ↦ 1) ∧
      spectrum ℝ (-1 : Matrix Unit Unit ℝ) = {-1} := by
  constructor
  · constructor
    · intro h
      have h0 := congrFun h (Sum.inl ())
      norm_num at h0
    · rw [fromBlocks_mulVec, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
      funext i
      cases i <;> norm_num [Matrix.mulVec, dotProduct, Matrix.one_apply, Complex.ofReal_neg,
        Complex.ofReal_one]
  · simpa only [map_neg, map_one] using spectrum.scalar_eq (A := Matrix Unit Unit ℝ) (-1 : ℝ)

end BenziGolubLiesen
