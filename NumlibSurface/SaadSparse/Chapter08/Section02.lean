/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.SaadSparse.Chapter04.Section02
import NumlibSurface.SaadSparse.Chapter05.Section03
import NumlibSurface.SaadSparse.Chapter05.Section04
import NumlibSurface.SaadSparse.Chapter08.Section01

/-!
# Saad, Section 8.2: Row projection methods

This module formalizes Section 8.2 of [saad2003iterative], together with Problems P-8.2, P-8.3 and
P-8.8. The section introduces no new method: each of its algorithms is a projection process of
Sections 5.3–5.4 over the coordinate subspaces $K_i = \operatorname{span}\{e_i\}$, applied to one of
the two systems of normal equations $A^T A x = A^T b$ and $A A^T u = b$. This module proves the
identification algorithm by algorithm, through `NumlibSurface.SaadSparse.Chapter05.Section03`,
`NumlibSurface.SaadSparse.Chapter05.Section04` and the backbone `Numlib.Projection.Additive`.

One NE-SOR relaxation (Kaczmarz's method, Algorithm 8.1) is the one-dimensional Petrov–Galerkin step
onto $\operatorname{span}\{A^T e_i\}$ orthogonally to $\operatorname{span}\{e_i\}$. One NR-SOR
relaxation (Algorithm 8.2) is the Galerkin step for $A^T A x = A^T b$ on
$\operatorname{span}\{e_i\}$. A full sweep of either is a multiplicative projection process, and
Cimmino's method (Algorithm 8.3) is an additive one. With normalized columns Cimmino's method is
Richardson's iteration for the normal equations, and in general it is Richardson's iteration
preconditioned by the diagonal of $A^T A$. A whole NR-SOR sweep is one SOR step (4.12) for
$A^T A x = A^T b$, so by Theorem 4.10 it converges for $0 < \omega < 2$ when $A$ is nonsingular.

## Main definitions

* Section 8.2, `SaadSparse.Chapter08.coordFamily`: the family of the $n$ coordinate axes of
  $\mathbb{R}^n$ as a projection family of Section 5.4.
* Algorithm 8.1, `SaadSparse.Chapter08.neSORStep`: one NE-SOR (Kaczmarz) relaxation
  $x \mapsto x + \delta_i A^T e_i$.
* Algorithm 8.2, `SaadSparse.Chapter08.nrSORStep`: one NR-SOR relaxation
  $x \mapsto x + \delta_i e_i$.
* Algorithm 8.3, `SaadSparse.Chapter08.cimmino`: one step of Cimmino's method, with all corrections
  computed from the same residual.
* Problem P-8.2, `SaadSparse.Chapter08.colNormDiag`: the diagonal
  $D = \operatorname{diag}(\|Ae_i\|_2^2)$ of $A^T A$.
* Problem P-8.3, `SaadSparse.Chapter08.cimminoNE`: the row form of Cimmino's method.
* Equations (8.26)–(8.27), `SaadSparse.Chapter08.blockCimmino`: the block form of Cimmino's method.

## Main results

* Equations (8.12)–(8.15), `SaadSparse.Chapter08.neSORStep_isPetrovGalerkin`: the NE-SOR relaxation
  is a Petrov–Galerkin step, after which the $i$-th component of the residual vanishes.
* Equations (8.17)–(8.18), `SaadSparse.Chapter08.nrSORStep_isGalerkin`: the NR-SOR relaxation is a
  Galerkin step for the normal equations, after which the $i$-th component of the normal-equations
  residual vanishes.
* Section 8.2, `SaadSparse.Chapter08.sorSweep_eq_multiplicativeSweep`: the NR-SOR sweep is the
  multiplicative projection process for $A^T A x = A^T b$ over the coordinate family.
* Section 8.2, `SaadSparse.Chapter08.neSORSweep_eq_multiplicativeStep`: the NE-SOR sweep is the
  multiplicative Petrov–Galerkin process over the pairs $(\operatorname{span}\{A^T e_i\},
  \operatorname{span}\{e_i\})$.
* Section 8.2, `SaadSparse.Chapter08.cimmino_eq_additiveStep`: Cimmino's method is the additive
  projection process for $A^T A x = A^T b$ over the coordinate family.
* Equation (8.24), `SaadSparse.Chapter08.equation_8_24`: the least-squares projector $P_i$ is the
  orthogonal projector onto the $i$-th column of $A$.
* Equations (8.23)–(8.25) and Problem P-8.8, `SaadSparse.Chapter08.equation_8_25`: the residual
  identity $r_{\mathrm{new}} = (I - \omega \sum_i P_i) r$, and $x_{\mathrm{new}} = x + \omega A^{-1}
  \sum_i P_i r$.
* Problem P-8.2, `SaadSparse.Chapter08.cimmino_eq_richardson`: with unit columns, Cimmino's method
  is Richardson's iteration for the normal equations.
* Equation (8.22), `SaadSparse.Chapter08.equation_8_22`: the convergence interval and the optimal
  parameter of Richardson's iteration for $A^T A$.
* Problem P-8.2(a)–(b), `SaadSparse.Chapter08.cimmino_eq_richardson_diag`: Cimmino's method is
  Richardson's iteration for the normal equations preconditioned by $D$.
* Problem P-8.3, `SaadSparse.Chapter08.cimminoNE_eq_additiveStep`: the row form is the additive
  Petrov–Galerkin process over the pairs $(\operatorname{span}\{A^T e_i\},
  \operatorname{span}\{e_i\})$.
* Problem P-8.3, `SaadSparse.Chapter08.cimminoNE_eq_jacobi`: the row form is Jacobi's iteration for
  $A A^T u = b$, read through $x = A^T u$.
* Equations (8.26)–(8.27), `SaadSparse.Chapter08.blockCimmino_isMinResidual`: the block correction
  solves a least-squares problem.
* Section 8.2.1, `SaadSparse.Chapter08.normal_diag`: the $i$-th diagonal entry of $A^T A$ is
  $\|Ae_i\|_2^2$.
* Section 8.2.1, `SaadSparse.Chapter08.nrSORSweep_eq_sorStep`: one NR-SOR sweep is one SOR step for
  the normal equations.
* Section 8.2.1, `SaadSparse.Chapter08.sorSweep_tendsto`: for nonsingular $A$ and $0 < \omega < 2$,
  the NR-SOR sweep converges to the solution.

## Conventions

* As in Chapter 5, everything is over $\mathbb{R}$. Vectors are in `EuclideanSpace ℝ (Fin n)`, $e_i$
  is `SaadSparse.Chapter08.coordVec i`, and a matrix acts on a vector by `Matrix.toEuclideanLin`,
  written `A ⬝ x`.
* The inner product $(x, y)$ is `inner ℝ x y`. The vector $A e_i$ is the $i$-th column of $A$, and
  $A^T e_i$ is its $i$-th row.
* A sweep visits $i = 1, \dots, n$ in increasing order; in Lean the indices are $0, \dots, n - 1$.

## Implementation notes

* Division by zero is $0$ in Lean. A relaxation whose row or column of $A$ vanishes therefore does
  nothing.
* Statements about Richardson's and the SOR iteration of Chapter 4 use the plain function type
  `Fin n → ℝ`, reached through `WithLp.ofLp`.

## Deviations from the source

* **Problem P-8.2** (typo). The problem writes the normalization $\|A^T e_i\|_2 = 1$ of the rows;
  the hypothesis that makes Cimmino's step Richardson's is the normalization $\|A e_i\|_2 = 1$ of
  the columns, as in Algorithm 8.3 and the text of Section 8.2.2. See
  `SaadSparse.Chapter08.cimmino_eq_richardson`.

## Not formalized

* **Problem P-8.2(c)**, the convergence interval $0 < \omega < 2/\lambda_{\max}(D^{-1/2} A^T A
  D^{-1/2})$ of the unnormalized iteration. It needs the symmetric square root of $D$ and the
  transport of `SaadSparse.Chapter04.example_4_1_tendsto_iff` through that change of variables;
  `SaadSparse.Chapter08.equation_8_22` is the normalized case.
-/

open Matrix Filter Topology

open scoped Matrix SaadSparse

namespace SaadSparse.Chapter08

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

/-! ### The coordinate family -/

/-- The $i$-th coordinate vector $e_i$ of $\mathbb{R}^n$. -/
noncomputable def coordVec (i : Fin n) : E n := EuclideanSpace.single i 1

/-- The $i$-th coordinate vector $e_i$ as an $n \times 1$ matrix, the form of a basis matrix in
`SaadSparse.Chapter05.ProjFamily`. -/
def coordCol (i : Fin n) : Matrix (Fin n) (Fin 1) ℝ :=
  Matrix.of fun p _ => (Pi.single i (1 : ℝ) : Fin n → ℝ) p

/-- **Section 8.2** of [saad2003iterative], the coordinate family. The projection family of Section
5.4 that consists of the $n$ one-dimensional subspaces $K_i = \operatorname{span}\{e_i\}$ of
$\mathbb{R}^n$, $i = 1, \dots, n$, each with the basis matrix $V_i = e_i$.

Every method of Section 8.2 is a projection process of Section 5.4 over this family. -/
noncomputable def coordFamily (n : ℕ) : Chapter05.ProjFamily n where
  p := n
  size _ := 1
  V := coordCol

/-- The coordinate family consists of $n$ subspaces. -/
@[simp] theorem coordFamily_p : (coordFamily n).p = n := rfl

/-- The $i$-th basis matrix of the coordinate family is $e_i$ as an $n \times 1$ matrix. -/
@[simp] theorem coordFamily_V (i : Fin n) : (coordFamily n).V i = coordCol i := rfl

/-- The single column of the $n \times 1$ matrix `SaadSparse.Chapter08.coordCol i` is $e_i$. -/
theorem coordCol_cols (i : Fin n) (j : Fin 1) : (coordCol i).cols j = coordVec i := by
  refine WithLp.ofLp_injective 2 ?_
  funext p
  rw [Matrix.ofLp_cols_apply, coordCol, Matrix.of_apply, coordVec]
  simp [Pi.single_apply]

/-- The $i$-th subspace of the coordinate family is $\operatorname{span}\{e_i\}$. -/
theorem coordFamily_subspace (i : Fin n) : (coordFamily n).subspace i = ℝ ∙ coordVec i := by
  have hsub : (coordFamily n).subspace i
      = Submodule.span ℝ (Set.range (coordCol i).cols) := rfl
  rw [hsub, show (coordCol i).cols = fun _ : Fin 1 => coordVec i from funext (coordCol_cols i),
    Set.range_const]

/-- For $M \in \mathbb{R}^{n \times n}$ and $u, v \in \mathbb{R}^n$, $(M^T u, v) = (u, Mv)$. -/
theorem inner_transpose (M : Matrix (Fin n) (Fin n) ℝ) (u v : E n) :
    inner ℝ (Mᵀ ⬝ u) v = inner ℝ u (M ⬝ v) := by
  have h := inner_conjTranspose M u v
  rwa [Chapter05.conjTranspose_eq_transpose] at h

/-- For $M \in \mathbb{R}^{n \times n}$ and $u, v \in \mathbb{R}^n$, $(u, M^T v) = (Mu, v)$. This is
the companion of `SaadSparse.Chapter08.inner_transpose`. -/
theorem inner_transpose' (M : Matrix (Fin n) (Fin n) ℝ) (u v : E n) :
    inner ℝ u (Mᵀ ⬝ v) = inner ℝ (M ⬝ u) v := by
  rw [real_inner_comm, inner_transpose, real_inner_comm]

/-- For $A \in \mathbb{R}^{n \times n}$, $(e_i, A^T A e_i) = \|Ae_i\|_2^2$: the quadratic form of
the normal-equations matrix on $e_i$ is the squared norm of the $i$-th column of $A$. -/
theorem inner_normal_coordVec (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    inner ℝ (coordVec i) ((Aᵀ * A) ⬝ coordVec i) = ‖A ⬝ coordVec i‖ ^ 2 := by
  rw [Matrix.toEuclideanLin_mul_apply, inner_transpose', real_inner_self_eq_norm_sq]

/-- For $A \in \mathbb{R}^{n \times n}$, $(e_i, A A^T e_i) = \|A^T e_i\|_2^2$: the quadratic form of
$A A^T$ on $e_i$ is the squared norm of the $i$-th row of $A$. -/
theorem inner_normal'_coordVec (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    inner ℝ (coordVec i) (A ⬝ (Aᵀ ⬝ coordVec i)) = ‖Aᵀ ⬝ coordVec i‖ ^ 2 := by
  rw [← inner_transpose, real_inner_self_eq_norm_sq]

/-- For $A \in \mathbb{R}^{n \times n}$ and $b, x \in \mathbb{R}^n$,
$A^T b - A^T A x = A^T (b - Ax)$: the normal-equations residual is $A^T$ times the residual. -/
theorem normal_residual (A : Matrix (Fin n) (Fin n) ℝ) (b x : E n) :
    (Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x) = (Aᵀ ⬝ (b - (A ⬝ x))) := by
  rw [Matrix.toEuclideanLin_mul_apply, ← map_sub]

/-! ### One-dimensional Petrov–Galerkin pairs -/

/-- Let $M$ be a linear operator on $\mathbb{R}^n$ and $v, w \in \mathbb{R}^n$ with
$(w, Mv) \neq 0$. Then the pair $(\operatorname{span}\{v\}, \operatorname{span}\{w\})$ is
nondegenerate for $M$ (`Projection.IsNondegeneratePair`): the two subspaces have the same
dimension, and $M$ maps $\operatorname{span}\{v\}$ injectively modulo
$\operatorname{span}\{w\}^\perp$. This is Proposition 5.1 of [saad2003iterative] in dimension
one. -/
theorem isNondegeneratePair_span_singleton {M : (E n) →ₗ[ℝ] (E n)} {v w : E n}
    (h : inner ℝ w (M v) ≠ 0) : Projection.IsNondegeneratePair M (ℝ ∙ v) (ℝ ∙ w) where
  finrank_eq := by
    have hv : v ≠ 0 := fun hc => h (by rw [hc, map_zero, inner_zero_right])
    have hw : w ≠ 0 := fun hc => h (by rw [hc, inner_zero_left])
    rw [finrank_span_singleton hv, finrank_span_singleton hw]
  eq_zero_of_mem_orthogonal z hz hzo := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h0 : inner ℝ w (M (c • v)) = (0 : ℝ) :=
      (Submodule.mem_orthogonal _ _).1 hzo w (Submodule.mem_span_singleton_self w)
    rw [map_smul, inner_smul_right] at h0
    rcases mul_eq_zero.1 h0 with hc | hcon
    · rw [hc, zero_smul]
    · exact absurd hcon h

/-- Let $M$ be a linear operator on $\mathbb{R}^n$, $c \in \mathbb{R}^n$, and $(K, L)$ a
nondegenerate pair for $M$ with $K = \operatorname{span}\{v\}$, $L = \operatorname{span}\{w\}$
and $(w, Mv) \neq 0$. Then the Petrov–Galerkin step `Projection.pairStep` of the pair is the
elementary step (5.12) of [saad2003iterative]:
$$x \mapsto x + \frac{(w, c - Mx)}{(w, Mv)} \, v.$$
This is what makes every method of Section 8.2 a projection process of Section 5.4. -/
theorem pairStep_eq_step1 {M : (E n) →ₗ[ℝ] (E n)} {c : E n} {K L : Submodule ℝ (E n)}
    [FiniteDimensional ℝ K] [FiniteDimensional ℝ L]
    (h : Projection.IsNondegeneratePair M K L) {v w : E n} (hK : K = ℝ ∙ v) (hL : L = ℝ ∙ w)
    (hvw : inner ℝ w (M v) ≠ 0) (x : E n) :
    Projection.pairStep M c K L h x = Projection.step1 M c v w x := by
  subst hK
  subst hL
  exact (Projection.pairStep_isPetrovGalerkin (b := c) h x).eq_of_forall
    (Projection.step1_isPetrovGalerkin v w x hvw) h.eq_zero_of_mem_orthogonal

/-- Let $M \in \mathbb{R}^{n \times n}$ with $(e_i, M e_i) \neq 0$, and let $V = e_i$ as an
$n \times 1$ matrix. Then the $1 \times 1$ matrix $V^T M V$ is nonsingular. This is the
nondegeneracy hypothesis of Section 5.4 for the coordinate family. -/
theorem isUnit_coordCol {M : Matrix (Fin n) (Fin n) ℝ} {i : Fin n}
    (h : inner ℝ (coordVec i) (M ⬝ coordVec i) ≠ 0) :
    IsUnit ((coordCol i)ᵀ * M * coordCol i) := by
  rw [← Chapter05.crossGram_matrix M (coordCol i) (coordCol i), Matrix.isUnit_iff_isUnit_det,
    Matrix.det_fin_one, Matrix.of_apply, coordCol_cols, isUnit_iff_ne_zero]
  exact h

/-! ### Algorithm 8.1: the NE-SOR relaxation -/

variable (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) (ω : ℝ)

/-- **Algorithm 8.1** of [saad2003iterative] (NE-SOR, Kaczmarz's method), one relaxation; see
(8.11)–(8.15). Let $A \in \mathbb{R}^{n \times n}$, $b \in \mathbb{R}^n$ and
$\omega \in \mathbb{R}$. The relaxation of index $i$ maps $x$ to
$$x + \delta_i A^T e_i, \qquad \delta_i = \omega \frac{\beta_i - (Ax)_i}{\|A^T e_i\|_2^2},$$
where $A^T e_i$ is the $i$-th row of $A$ and $\beta_i$ is the $i$-th component of $b$.

The numerator $\beta_i - (Ax)_i$ is written $(e_i, b - Ax)$, which equals
$\beta_i - (x, A^T e_i)$. If the $i$-th row of $A$ vanishes, then $\delta_i = 0$. -/
noncomputable def neSORStep (i : Fin n) (x : E n) : E n :=
  x + (ω * inner ℝ (coordVec i) (b - (A ⬝ x)) / ‖Aᵀ ⬝ coordVec i‖ ^ 2) • (Aᵀ ⬝ coordVec i)

/-- One forward sweep of Algorithm 8.1 of [saad2003iterative]: the NE-SOR relaxations of index
$i = 1, \dots, n$, applied in this order. -/
noncomputable def neSORSweep (x : E n) : E n :=
  (List.finRange n).foldl (fun y i => neSORStep A b ω i y) x

/-- **Algorithm 8.2** of [saad2003iterative] (NR-SOR), one relaxation; see (8.16)–(8.18). Let
$A \in \mathbb{R}^{n \times n}$, $b \in \mathbb{R}^n$ and $\omega \in \mathbb{R}$. The
relaxation of index $i$ maps $x$ to
$$x + \delta_i e_i, \qquad \delta_i = \omega \frac{(r, Ae_i)}{\|Ae_i\|_2^2}, \qquad r = b -
  Ax,$$
where $Ae_i$ is the $i$-th column of $A$.

If the $i$-th column of $A$ vanishes, then $\delta_i = 0$. -/
noncomputable def nrSORStep (i : Fin n) (x : E n) : E n :=
  x + (ω * inner ℝ (A ⬝ coordVec i) (b - (A ⬝ x)) / ‖A ⬝ coordVec i‖ ^ 2) • coordVec i

/-- One forward sweep of Algorithm 8.2 of [saad2003iterative]: the NR-SOR relaxations of index
$i = 1, \dots, n$, applied in this order. -/
noncomputable def nrSORSweep (x : E n) : E n :=
  (List.finRange n).foldl (fun y i => nrSORStep A b ω i y) x

variable {A b ω}

/-- For $\omega = 1$, the NE-SOR relaxation of index $i$ is the elementary step (5.12) of
[saad2003iterative] for $Ax = b$ with $v = A^T e_i$ and $w = e_i$. -/
theorem neSORStep_eq_step1 (i : Fin n) (x : E n) :
    neSORStep A b 1 i x = Chapter05.step1 A b (Aᵀ ⬝ coordVec i) (coordVec i) x := by
  rw [neSORStep, Chapter05.step1, inner_normal'_coordVec, one_mul]

/-- For $\omega = 1$, the NR-SOR relaxation of index $i$ is the elementary step (5.12) of
[saad2003iterative] for the normal equations $A^T A x = A^T b$ with $v = w = e_i$. -/
theorem nrSORStep_eq_step1 (i : Fin n) (x : E n) :
    nrSORStep A b 1 i x = Chapter05.step1 (Aᵀ * A) (Aᵀ ⬝ b) (coordVec i) (coordVec i) x := by
  rw [nrSORStep, Chapter05.step1, inner_normal_coordVec, normal_residual, inner_transpose', one_mul]

/-- **Equations (8.12)–(8.15)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ with
$A^T e_i \neq 0$, and let $b, x \in \mathbb{R}^n$. Let $x'$ be the NE-SOR relaxation of index
$i$ of $x$ with $\omega = 1$. Then $x'$ is the Petrov–Galerkin step for $Ax = b$ from $x$ onto
$K = \operatorname{span}\{A^T e_i\}$ orthogonally to $L = \operatorname{span}\{e_i\}$:
$$x' - x \in K, \qquad b - Ax' \perp L.$$
In particular the $i$-th component $(e_i, b - Ax')$ of the new residual is $0$.

The Petrov–Galerkin condition is `IsPetrovGalerkin`. -/
theorem neSORStep_isPetrovGalerkin {i : Fin n} (hi : (Aᵀ ⬝ coordVec i) ≠ 0) (x : E n) :
    IsPetrovGalerkin (Matrix.toEuclideanLin A) b x (ℝ ∙ (Aᵀ ⬝ coordVec i)) (ℝ ∙ coordVec i)
        (neSORStep A b 1 i x) ∧
      inner ℝ (coordVec i) (b - (A ⬝ neSORStep A b 1 i x)) = 0 := by
  have hne : inner ℝ (coordVec i) (A ⬝ (Aᵀ ⬝ coordVec i)) ≠ 0 := by
    rw [inner_normal'_coordVec]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hi)
  have hpg := Chapter05.isProjectionApprox_iff.1
    (Chapter05.step1_isProjectionApprox (A := A) (b := b) (x := x) (Aᵀ ⬝ coordVec i)
      (coordVec i) hne)
  rw [← neSORStep_eq_step1] at hpg
  exact ⟨hpg, (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hpg.orth⟩

/-- **Equations (8.17)–(8.18)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ with
$Ae_i \neq 0$, and let $b, x \in \mathbb{R}^n$. Let $x'$ be the NR-SOR relaxation of index $i$
of $x$ with $\omega = 1$. Then $x'$ is the Galerkin step for $A^T A x = A^T b$ from $x$ on
$K = \operatorname{span}\{e_i\}$:
$$x' - x \in K, \qquad A^T b - A^T A x' \perp K.$$
In particular the $i$-th component $(Ae_i, b - Ax')$ of the new normal-equations residual is
$0$.

The Galerkin condition is `IsGalerkin`. -/
theorem nrSORStep_isGalerkin {i : Fin n} (hi : (A ⬝ coordVec i) ≠ 0) (x : E n) :
    IsGalerkin (Matrix.toEuclideanLin (Aᵀ * A)) (Aᵀ ⬝ b) x (ℝ ∙ coordVec i)
        (nrSORStep A b 1 i x) ∧
      inner ℝ (A ⬝ coordVec i) (b - (A ⬝ nrSORStep A b 1 i x)) = 0 := by
  have hne : inner ℝ (coordVec i) ((Aᵀ * A) ⬝ coordVec i) ≠ 0 := by
    rw [inner_normal_coordVec]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hi)
  have hpg := Chapter05.isProjectionApprox_iff.1
    (Chapter05.step1_isProjectionApprox (A := Aᵀ * A) (b := (Aᵀ ⬝ b)) (x := x) (coordVec i)
      (coordVec i) hne)
  rw [← nrSORStep_eq_step1] at hpg
  refine ⟨hpg, ?_⟩
  have h0 := (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hpg.orth
  rwa [show (Matrix.toEuclideanLin (Aᵀ * A)) (nrSORStep A b 1 i x)
    = ((Aᵀ * A) ⬝ nrSORStep A b 1 i x) from rfl, normal_residual, inner_transpose'] at h0

/-! ### The sweeps as multiplicative projection processes -/

/-- **Section 8.2** of [saad2003iterative], the NR-SOR sweep as a projection process. Let
$A \in \mathbb{R}^{n \times n}$ have no zero column, and let $b, x \in \mathbb{R}^n$. Then the
NR-SOR sweep with $\omega = 1$ maps $x$ to the result of the multiplicative projection process
of Section 5.4 (Algorithm 5.6) for $A^T A x = A^T b$ over the coordinate family
$K_i = \operatorname{span}\{e_i\}$, $i = 1, \dots, n$. This is block Gauss–Seidel with
one-dimensional blocks.

The process is `SaadSparse.Chapter05.multiplicativeSweep`. The corresponding statement for the
NE-SOR sweep is `SaadSparse.Chapter08.neSORSweep_eq_multiplicativeStep`. -/
theorem sorSweep_eq_multiplicativeSweep (h : ∀ i : Fin n, (A ⬝ coordVec i) ≠ 0) (x : E n) :
    nrSORSweep A b 1 x = Chapter05.multiplicativeSweep (coordFamily n) (Aᵀ * A) (Aᵀ ⬝ b) x := by
  have hne : ∀ i : Fin n, inner ℝ (coordVec i) ((Aᵀ * A) ⬝ coordVec i) ≠ 0 := fun i => by
    rw [inner_normal_coordVec]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (h i))
  have hunit : ∀ i : Fin (coordFamily n).p,
      IsUnit (((coordFamily n).V i)ᵀ * (Aᵀ * A) * (coordFamily n).V i) :=
    fun i => isUnit_coordCol (hne i)
  have hrhs : Chapter05.multiplicativeSweep (coordFamily n) (Aᵀ * A) (Aᵀ ⬝ b) x
      = (List.finRange n).foldl (fun y i => Projection.pairStep
          (Matrix.toEuclideanLin (Aᵀ * A)) (Aᵀ ⬝ b) ((coordFamily n).subspace i)
          ((coordFamily n).subspace i) (Chapter05.isNondegeneratePair_subspace hunit i) y) x := by
    rw [Chapter05.multiplicativeSweep_eq hunit]
    rfl
  have hfun : (fun (y : E n) (i : Fin n) => nrSORStep A b 1 i y)
      = fun (y : E n) (i : Fin n) => Projection.pairStep
          (Matrix.toEuclideanLin (Aᵀ * A)) (Aᵀ ⬝ b) ((coordFamily n).subspace i)
          ((coordFamily n).subspace i) (Chapter05.isNondegeneratePair_subspace hunit i) y :=
    funext fun y => funext fun i => by
      rw [pairStep_eq_step1 _ (coordFamily_subspace i) (coordFamily_subspace i) (hne i),
        nrSORStep_eq_step1]
      rfl
  rw [nrSORSweep, hrhs, hfun]
  rfl

/-- **Section 8.2** of [saad2003iterative], the NE-SOR sweep as a projection process. Let
$A \in \mathbb{R}^{n \times n}$ with $(e_i, A A^T e_i) \neq 0$ for all $i$, that is, with no
zero row, and let $b, x \in \mathbb{R}^n$. Then the NE-SOR sweep with $\omega = 1$ maps $x$ to
the result of the multiplicative Petrov–Galerkin process for $Ax = b$ over the pairs $(K_i,
L_i) = (\operatorname{span}\{A^T e_i\}, \operatorname{span}\{e_i\})$, $i = 1, \dots, n$.

The process is the backbone `Projection.multiplicativeStep`. It is not
`SaadSparse.Chapter05.multiplicativeSweep`, whose test spaces are its trial spaces; the two
coincide only for NR-SOR. -/
theorem neSORSweep_eq_multiplicativeStep
    (hne : ∀ i : Fin n, inner ℝ (coordVec i) (A ⬝ (Aᵀ ⬝ coordVec i)) ≠ 0) (x : E n) :
    neSORSweep A b 1 x
      = Projection.multiplicativeStep (Matrix.toEuclideanLin A) b
          (fun i => ℝ ∙ (Aᵀ ⬝ coordVec i)) (fun i => ℝ ∙ coordVec i)
          (fun i => isNondegeneratePair_span_singleton (hne i)) (List.finRange n) x := by
  have hrhs : Projection.multiplicativeStep (Matrix.toEuclideanLin A) b
        (fun i => ℝ ∙ (Aᵀ ⬝ coordVec i)) (fun i => ℝ ∙ coordVec i)
        (fun i => isNondegeneratePair_span_singleton (hne i)) (List.finRange n) x
      = (List.finRange n).foldl (fun y i => Projection.pairStep (Matrix.toEuclideanLin A) b
          (ℝ ∙ (Aᵀ ⬝ coordVec i)) (ℝ ∙ coordVec i)
          (isNondegeneratePair_span_singleton (hne i)) y) x := rfl
  have hfun : (fun (y : E n) (i : Fin n) => neSORStep A b 1 i y)
      = fun (y : E n) (i : Fin n) => Projection.pairStep (Matrix.toEuclideanLin A) b
          (ℝ ∙ (Aᵀ ⬝ coordVec i)) (ℝ ∙ coordVec i)
          (isNondegeneratePair_span_singleton (hne i)) y :=
    funext fun y => funext fun i => by
      rw [pairStep_eq_step1 _ rfl rfl (hne i), neSORStep_eq_step1]
      rfl
  rw [neSORSweep, hrhs, hfun]

/-! ### Algorithm 8.3: Cimmino's method -/

variable (A b ω)

/-- **Algorithm 8.3** of [saad2003iterative] (Cimmino's method); see (8.19)–(8.21). Let
$A \in \mathbb{R}^{n \times n}$, $b \in \mathbb{R}^n$ and $\omega \in \mathbb{R}$. One step maps
$x$ to
$$x + \sum_{i=1}^n \delta_i e_i, \qquad \delta_i = \omega \frac{(r, Ae_i)}{\|Ae_i\|_2^2}, \qquad
  r = b - Ax.$$
Every $\delta_i$ is computed from the same residual $r$, and the corrections are added at once.

If the $i$-th column of $A$ vanishes, then $\delta_i = 0$. -/
noncomputable def cimmino (x : E n) : E n :=
  x + ∑ i, (ω * inner ℝ (A ⬝ coordVec i) (b - (A ⬝ x)) / ‖A ⬝ coordVec i‖ ^ 2) • coordVec i

variable {A b ω}

/-- **Section 8.2** of [saad2003iterative], Cimmino's method as a projection process. Let
$A \in \mathbb{R}^{n \times n}$ have no zero column, and let $b, x \in \mathbb{R}^n$ and
$\omega \in \mathbb{R}$. Then one step of Cimmino's method is one step of the additive
projection process of Section 5.4 (Algorithm 5.5) for $A^T A x = A^T b$ over the coordinate
family, with all weights equal to $\omega$.

This is the remark of the book that each instance of Cimmino's method is mathematically
equivalent to an orthogonal projection step for $A^T A x = A^T b$ with
$K = \operatorname{span}\{e_i\}$. The process is `SaadSparse.Chapter05.additiveStep`. -/
theorem cimmino_eq_additiveStep (h : ∀ i : Fin n, (A ⬝ coordVec i) ≠ 0) (x : E n) :
    cimmino A b ω x
      = Chapter05.additiveStep (coordFamily n) (Aᵀ * A) (fun _ => ω) (Aᵀ ⬝ b) x := by
  have hne : ∀ i : Fin n, inner ℝ (coordVec i) ((Aᵀ * A) ⬝ coordVec i) ≠ 0 := fun i => by
    rw [inner_normal_coordVec]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 (h i))
  have hunit : ∀ i : Fin (coordFamily n).p,
      IsUnit (((coordFamily n).V i)ᵀ * (Aᵀ * A) * (coordFamily n).V i) :=
    fun i => isUnit_coordCol (hne i)
  have hrhs : Chapter05.additiveStep (coordFamily n) (Aᵀ * A) (fun _ => ω) (Aᵀ ⬝ b) x
      = x + ∑ i, ω • (Projection.pairStep (Matrix.toEuclideanLin (Aᵀ * A)) (Aᵀ ⬝ b)
          ((coordFamily n).subspace i) ((coordFamily n).subspace i)
          (Chapter05.isNondegeneratePair_subspace hunit i) x - x) := by
    rw [Chapter05.additiveStep_eq hunit]
    rfl
  rw [cimmino, hrhs]
  refine congrArg (fun z : E n => x + z) (Finset.sum_congr rfl fun i _ => ?_)
  rw [pairStep_eq_step1 _ (coordFamily_subspace i) (coordFamily_subspace i) (hne i),
    show Projection.step1 (Matrix.toEuclideanLin (Aᵀ * A)) (Aᵀ ⬝ b) (coordVec i) (coordVec i) x
      = nrSORStep A b 1 i x from (nrSORStep_eq_step1 i x).symm, nrSORStep, add_sub_cancel_left,
    smul_smul, one_mul, mul_div_assoc]

/-! ### Equations (8.23)–(8.25): the projectors and the residual identity -/

/-- For $A \in \mathbb{R}^{n \times n}$, the image of $\operatorname{span}\{e_i\}$ under $A$ is
$\operatorname{span}\{Ae_i\}$, the span of the $i$-th column. -/
theorem map_coordVec (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (ℝ ∙ coordVec i).map (Matrix.toEuclideanLin A) = ℝ ∙ (A ⬝ coordVec i) := by
  rw [Submodule.map_span, Set.image_singleton]

/-- **Equation (8.24)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$ with
$Ae_i \neq 0$. The projector $P_i = V (W^T V)^{-1} W^T$ of (5.22) with $V = W = Ae_i$, that is,
the least-squares case $L_i = A K_i$, is the orthogonal projector onto
$\operatorname{span}\{Ae_i\}$. This projector maps $r \in \mathbb{R}^n$ to
$$P_i r = \frac{(r, Ae_i)}{\|Ae_i\|_2^2} \, Ae_i.$$

The matrix $P_i$ is `Matrix.obliqueProj`, and the orthogonal projector is
`Submodule.starProjection`. -/
theorem equation_8_24 {i : Fin n} (h : (A ⬝ coordVec i) ≠ 0) (r : E n) :
    Matrix.toEuclideanLin (Matrix.obliqueProj (A * coordCol i) (A * coordCol i))
        = ((ℝ ∙ (A ⬝ coordVec i)).starProjection : (E n) →ₗ[ℝ] (E n)) ∧
      (ℝ ∙ (A ⬝ coordVec i)).starProjection r
        = (inner ℝ (A ⬝ coordVec i) r / ‖A ⬝ coordVec i‖ ^ 2) • (A ⬝ coordVec i) := by
  have hgram : ((A * coordCol i)ᵀ * (A * coordCol i))
      = (coordCol i)ᵀ * (Aᵀ * A) * (coordCol i) := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hunit : IsUnit ((A * coordCol i)ᵀ * (A * coordCol i)) := by
    rw [hgram]
    refine isUnit_coordCol ?_
    rw [inner_normal_coordVec]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 h)
  refine ⟨?_, ?_⟩
  · have hls := Chapter05.leastSquares_P_i_eq_starProjection (𝒲 := coordFamily n) (A := A) (i := i)
      hunit
    rw [coordFamily_subspace] at hls
    simp only [map_coordVec] at hls
    exact hls
  · rw [Submodule.starProjection_singleton ℝ r]
    norm_num

/-- **Equations (8.23)–(8.25)** and **Problem P-8.8** of [saad2003iterative]. Let
$A \in \mathbb{R}^{n \times n}$ have no zero column, let $b, x \in \mathbb{R}^n$ and
$\omega \in \mathbb{R}$, and let $x_{\mathrm{new}}$ be one step of Cimmino's method from $x$.
Let $r = b - Ax$, and let $P_i$ be the orthogonal projector onto $\operatorname{span}\{Ae_i\}$.
Then
$$b - Ax_{\mathrm{new}} = \Bigl(I - \omega \sum_{i=1}^n P_i\Bigr) r.$$
If moreover $A$ is nonsingular, then (Problem P-8.8)
$$x_{\mathrm{new}} = x + \omega A^{-1} \sum_{i=1}^n P_i r.$$
-/
theorem equation_8_25 (h : ∀ i : Fin n, (A ⬝ coordVec i) ≠ 0) (x : E n) :
    b - (A ⬝ cimmino A b ω x)
        = (b - (A ⬝ x))
          - ω • ∑ i, (ℝ ∙ (A ⬝ coordVec i)).starProjection (b - (A ⬝ x)) ∧
      (IsUnit A → cimmino A b ω x
        = x + ω • (A⁻¹ ⬝ ∑ i, (ℝ ∙ (A ⬝ coordVec i)).starProjection (b - (A ⬝ x)))) := by
  have hstep : (A ⬝ cimmino A b ω x)
      = (A ⬝ x) + ω • ∑ i, (ℝ ∙ (A ⬝ coordVec i)).starProjection (b - (A ⬝ x)) := by
    rw [cimmino, map_add, map_sum, Finset.smul_sum]
    refine congrArg (fun z : E n => (A ⬝ x) + z) (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_smul, (equation_8_24 (h i) (b - (A ⬝ x))).2, smul_smul, div_eq_mul_inv,
      div_eq_mul_inv]
    ring_nf
  refine ⟨by rw [hstep]; abel, fun hA => ?_⟩
  have hAx : (A ⬝ cimmino A b ω x) - (A ⬝ x)
      = ω • ∑ i, (ℝ ∙ (A ⬝ coordVec i)).starProjection (b - (A ⬝ x)) := by
    rw [hstep]; abel
  have hinv : (A⁻¹ ⬝ (A ⬝ (cimmino A b ω x - x))) = cimmino A b ω x - x := by
    rw [← Matrix.toEuclideanLin_mul_apply,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det A).1 hA), Matrix.toEuclideanLin_one]
    rfl
  have hd : (A⁻¹ ⬝ (A ⬝ (cimmino A b ω x - x)))
      = (A⁻¹ ⬝ (ω • ∑ i, (ℝ ∙ (A ⬝ coordVec i)).starProjection (b - (A ⬝ x)))) := by
    rw [map_sub, hAx]
  rw [hd, map_smul] at hinv
  rw [hinv]
  abel

/-! ### Problem P-8.2 and (8.22): Cimmino's method with normalized columns -/

/-- **Problem P-8.2** of [saad2003iterative], normalized columns. Let
$A \in \mathbb{R}^{n \times n}$ with $\|Ae_i\|_2 = 1$ for every $i$, and let
$b, x \in \mathbb{R}^n$ and $\omega \in \mathbb{R}$. Then one step of Cimmino's method is
$$x_{\mathrm{new}} = x + \omega (A^T b - A^T A x),$$
which is one step of Richardson's iteration for the normal equations $A^T A x = A^T b$.

**Typo.** The problem writes the normalization $\|A^T e_i\|_2 = 1$ of the rows. The hypothesis
that makes the step Richardson's is the normalization $\|Ae_i\|_2 = 1$ of the columns, as in
Algorithm 8.3 and in the text of Section 8.2.2 ("if the columns are not normalized by their
2-norms").

The second conclusion states the same equation in plain coordinates, as
`SaadSparse.Chapter04.richardsonStep`. Without the normalization, Cimmino's step is Richardson's
iteration preconditioned by the diagonal of $A^T A$, whose $i$-th entry is $\|Ae_i\|_2^2$; see
`SaadSparse.Chapter08.cimmino_eq_richardson_diag`. -/
theorem cimmino_eq_richardson (h : ∀ i : Fin n, ‖A ⬝ coordVec i‖ = 1) (x : E n) :
    cimmino A b ω x = x + ω • ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x)) ∧
      WithLp.ofLp (cimmino A b ω x)
        = Chapter04.richardsonStep (Aᵀ * A) ω (Aᵀ *ᵥ WithLp.ofLp b) (WithLp.ofLp x) := by
  have hsum : ∑ i, (ω * inner ℝ (A ⬝ coordVec i) (b - (A ⬝ x)) / ‖A ⬝ coordVec i‖ ^ 2)
      • coordVec i = ω • (Aᵀ ⬝ (b - (A ⬝ x))) := by
    have hb := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' (Aᵀ ⬝ (b - (A ⬝ x)))
    rw [← hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h i, EuclideanSpace.basisFun_apply, smul_smul,
      show EuclideanSpace.single i (1 : ℝ) = coordVec i from rfl, inner_transpose']
    norm_num
  have h1 : cimmino A b ω x = x + ω • ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x)) := by
    rw [cimmino, hsum, normal_residual]
  refine ⟨h1, ?_⟩
  rw [h1, Chapter04.richardsonStep, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub]
  rfl

/-- **Equation (8.22)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$, and let
$\lambda_{\min} > 0$ and $\lambda_{\max}$ be eigenvalues of $A^T A$ such that the spectrum of
$A^T A$ lies in $[\lambda_{\min}, \lambda_{\max}]$. Let $\omega \neq 0$. Then Richardson's
iteration $z_{k+1} = z_k + \omega (c - A^T A z_k)$ converges for every $c$ and every $z_0$ if
and only if
$$0 < \omega < \frac{2}{\lambda_{\max}}.$$
Moreover, among $\omega > 0$, the spectral radius $\rho(I - \omega A^T A)$ is smallest at
$\omega_{\mathrm{opt}} = 2/(\lambda_{\min} + \lambda_{\max})$.

With normalized columns, Cimmino's method is this iteration with $c = A^T b$
(`SaadSparse.Chapter08.cimmino_eq_richardson`), so the statement gives its convergence interval
and its optimal parameter. The proof is Example 4.1 applied to the symmetric positive definite
matrix $A^T A$. The positivity of $\lambda_{\min}$, which nonsingularity of $A$ provides, is a
hypothesis. The hypothesis $\omega \neq 0$ excludes $\omega = 0$, for which the iteration is
constant and converges trivially. The spectral radius is `Matrix.complexSpectralRadius`. -/
theorem equation_8_22 {lmin lmax : ℝ} (hsub : spectrum ℝ (Aᵀ * A) ⊆ Set.Icc lmin lmax)
    (hmin : lmin ∈ spectrum ℝ (Aᵀ * A)) (hmax : lmax ∈ spectrum ℝ (Aᵀ * A)) (hpos : 0 < lmin)
    (hω : ω ≠ 0) :
    ((∀ c z₀ : Fin n → ℝ, ∃ z,
        Tendsto (fun k => (Chapter04.richardsonStep (Aᵀ * A) ω c)^[k] z₀) atTop (𝓝 z)) ↔
      0 < ω ∧ ω < 2 / lmax) ∧
      IsMinOn (fun ω : ℝ => Matrix.complexSpectralRadius (1 - ω • (Aᵀ * A))) (Set.Ioi 0)
        (2 / (lmin + lmax)) := by
  have hherm : (Aᵀ * A).IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_self A
    rwa [Chapter05.conjTranspose_eq_transpose] at h
  exact ⟨Chapter04.example_4_1_tendsto_iff hherm hsub hmin hmax hpos hω,
    (Chapter04.example_4_1_opt hherm hsub hmin hmax hpos).1⟩

/-! ### Problem P-8.2(a)–(b): Cimmino's method with unnormalized columns -/

/-- The $i$-th coordinate of a vector $w$ is $(e_i, w)$. -/
private theorem inner_coordVec (w : E n) (i : Fin n) :
    inner ℝ (coordVec i) w = WithLp.ofLp w i := by
  rw [coordVec, EuclideanSpace.inner_single_left]
  simp

/-- For a diagonal matrix $D = \operatorname{diag}(d)$, $(e_i, Dw) = d_i (e_i, w)$. -/
private theorem inner_coordVec_diagonal (d : Fin n → ℝ) (w : E n) (i : Fin n) :
    inner ℝ (coordVec i) ((Matrix.diagonal d) ⬝ w) = d i * inner ℝ (coordVec i) w := by
  rw [inner_coordVec, inner_coordVec,
    show WithLp.ofLp ((Matrix.diagonal d) ⬝ w) = Matrix.diagonal d *ᵥ WithLp.ofLp w from rfl,
    Matrix.mulVec_diagonal]

/-- For a diagonal matrix $D = \operatorname{diag}(d)$, $Dw = \sum_i d_i (e_i, w) e_i$. -/
private theorem diagonal_apply_eq_sum (d : Fin n → ℝ) (w : E n) :
    ((Matrix.diagonal d) ⬝ w) = ∑ i, (d i * inner ℝ (coordVec i) w) • coordVec i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' ((Matrix.diagonal d) ⬝ w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply, show EuclideanSpace.single i (1 : ℝ) = coordVec i from rfl,
    inner_coordVec_diagonal]

/-- **Problem P-8.2** of [saad2003iterative], the diagonal preconditioner. For
$A \in \mathbb{R}^{n \times n}$, the diagonal matrix
$$D = \operatorname{diag}(\|Ae_1\|_2^2, \dots, \|Ae_n\|_2^2),$$
which is the diagonal of the normal-equations matrix $A^T A$. Cimmino's method carries this
preconditioner when the columns of $A$ are not normalized. -/
noncomputable def colNormDiag (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => ‖A ⬝ coordVec i‖ ^ 2

/-- The diagonal matrix $\operatorname{diag}(\|Ae_1\|_2^{-2}, \dots, \|Ae_n\|_2^{-2})$, with the
entry $0$ where a column of $A$ vanishes. It is the inverse $D^{-1}$ of
`SaadSparse.Chapter08.colNormDiag` when no column of $A$ vanishes
(`SaadSparse.Chapter08.colNormDiag_mul_colNormDiagInv`).

It is written entrywise rather than as the matrix inverse, so that a vanishing column gives $0$
in its place, as the division by zero of the algorithm does. -/
noncomputable def colNormDiagInv (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => (‖A ⬝ coordVec i‖ ^ 2)⁻¹

/-- If no column of $A \in \mathbb{R}^{n \times n}$ vanishes, then $D D^{-1} = I$ for
$D = \operatorname{diag}(\|Ae_i\|_2^2)$ and the entrywise inverse $D^{-1}$. -/
theorem colNormDiag_mul_colNormDiagInv (h : ∀ i : Fin n, (A ⬝ coordVec i) ≠ 0) :
    colNormDiag A * colNormDiagInv A = 1 := by
  rw [colNormDiag, colNormDiagInv, Matrix.diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun i => ?_)
  exact mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.2 (h i)))

/-- **Problem P-8.2(a)–(b)** of [saad2003iterative]. Let $A \in \mathbb{R}^{n \times n}$,
$b, x \in \mathbb{R}^n$ and $\omega \in \mathbb{R}$, and let
$D = \operatorname{diag}(\|Ae_i\|_2^2)$. Then one step of Cimmino's method is
$$x_{\mathrm{new}} = x + \omega D^{-1} (A^T b - A^T A x),$$
which is Richardson's iteration for the normal equations $A^T A x = A^T b$, preconditioned by
the diagonal of $A^T A$.

No hypothesis is needed: $D^{-1}$ is the entrywise inverse
`SaadSparse.Chapter08.colNormDiagInv`, so a vanishing column makes the $\delta_i$ of the book
and the corresponding entry of $D^{-1}$ zero alike. The special case $D = I$, which Section
8.2.2 states in the text, is `SaadSparse.Chapter08.cimmino_eq_richardson`. -/
theorem cimmino_eq_richardson_diag (x : E n) :
    cimmino A b ω x = x + ω • (colNormDiagInv A ⬝ ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x))) := by
  rw [cimmino, normal_residual, colNormDiagInv, diagonal_apply_eq_sum, Finset.smul_sum]
  refine congrArg (fun z : E n => x + z) (Finset.sum_congr rfl fun i _ => ?_)
  rw [smul_smul, inner_transpose', div_eq_mul_inv]
  ring_nf

/-! ### Problem P-8.3: the row form of Cimmino's method -/

variable (A b ω)

/-- **Problem P-8.3** of [saad2003iterative], Cimmino's original row method. Let
$A \in \mathbb{R}^{n \times n}$, $b \in \mathbb{R}^n$ and $\omega \in \mathbb{R}$. One step maps
$x$ to
$$x + \sum_{i=1}^n \delta_i A^T e_i, \qquad \delta_i = \omega \frac{(e_i, b - Ax)}{\|A^T
  e_i\|_2^2}.$$
Each correction $\delta_i A^T e_i$ is the Kaczmarz relaxation of
`SaadSparse.Chapter08.neSORStep`, computed from the same residual, and the corrections are added
at once.

If the $i$-th row of $A$ vanishes, then $\delta_i = 0$. -/
noncomputable def cimminoNE (x : E n) : E n :=
  x + ∑ i, (ω * inner ℝ (coordVec i) (b - (A ⬝ x)) / ‖Aᵀ ⬝ coordVec i‖ ^ 2) • (Aᵀ ⬝ coordVec i)

variable {A b ω}

/-- **Problem P-8.3** of [saad2003iterative], the row form as a projection process. Let
$A \in \mathbb{R}^{n \times n}$ with $(e_i, A A^T e_i) \neq 0$ for all $i$, that is, with no
zero row, and let $b, x \in \mathbb{R}^n$ and $\omega \in \mathbb{R}$. Then one step of the row
form of Cimmino's method is one step of the additive Petrov–Galerkin process for $Ax = b$ over
the pairs $(K_i, L_i) = (\operatorname{span}\{A^T e_i\}, \operatorname{span}\{e_i\})$, with all
weights equal to $\omega$.

Kaczmarz's method is the multiplicative process over the same pairs
(`SaadSparse.Chapter08.neSORSweep_eq_multiplicativeStep`). The process is the backbone
`Projection.additiveStep`. It is not `SaadSparse.Chapter05.additiveStep`, whose test spaces are
its trial spaces; only the column form `SaadSparse.Chapter08.cimmino` is of that kind. -/
theorem cimminoNE_eq_additiveStep
    (hne : ∀ i : Fin n, inner ℝ (coordVec i) (A ⬝ (Aᵀ ⬝ coordVec i)) ≠ 0) (x : E n) :
    cimminoNE A b ω x
      = Projection.additiveStep (Matrix.toEuclideanLin A) b
          (fun i => ℝ ∙ (Aᵀ ⬝ coordVec i)) (fun i => ℝ ∙ coordVec i)
          (fun i => isNondegeneratePair_span_singleton (hne i)) (fun _ => ω) x := by
  rw [cimminoNE, Projection.additiveStep]
  refine congrArg (fun z : E n => x + z) (Finset.sum_congr rfl fun i _ => ?_)
  rw [pairStep_eq_step1 _ rfl rfl (hne i),
    show Projection.step1 (Matrix.toEuclideanLin A) b (Aᵀ ⬝ coordVec i) (coordVec i) x
      = neSORStep A b 1 i x from (neSORStep_eq_step1 i x).symm, neSORStep, add_sub_cancel_left,
    smul_smul, one_mul, mul_div_assoc]

/-- **Problem P-8.3** of [saad2003iterative], the row form as Jacobi's iteration. Let
$A \in \mathbb{R}^{n \times n}$, $b, u \in \mathbb{R}^n$ and $\omega \in \mathbb{R}$, and let
$D' = \operatorname{diag}(\|A^T e_i\|_2^2)$ be the diagonal of $A A^T$. Then one step of the row
form of Cimmino's method from $x = A^T u$ is
$$A^T \bigl(u + \omega D'^{-1} (b - A A^T u)\bigr),$$
that is, $A^T$ applied to one step of the relaxed Jacobi iteration for $A A^T u = b$.

This is the derivation that the problem asks for: the row version of
`SaadSparse.Chapter08.cimmino_eq_richardson_diag`, and Cimmino's own method. The inverse
$D'^{-1}$ is the entrywise inverse `SaadSparse.Chapter08.colNormDiagInv` of $A^T$, with the
entry $0$ where a row of $A$ vanishes. -/
theorem cimminoNE_eq_jacobi (u : E n) :
    cimminoNE A b ω (Aᵀ ⬝ u)
      = (Aᵀ ⬝ (u + ω • (colNormDiagInv (Aᵀ) ⬝ (b - ((A * Aᵀ) ⬝ u))))) := by
  rw [map_add, map_smul, colNormDiagInv, diagonal_apply_eq_sum, map_sum, Finset.smul_sum,
    cimminoNE]
  refine congrArg (fun z : E n => (Aᵀ ⬝ u) + z) (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_smul, smul_smul, Matrix.toEuclideanLin_mul_apply, div_eq_mul_inv]
  congr 1
  ring

/-! ### (8.26)–(8.27): the block form -/

variable (A b ω)

/-- **Equations (8.26)–(8.27)** of [saad2003iterative], the block form of Cimmino's method. Let
$A \in \mathbb{R}^{n \times n}$, $b \in \mathbb{R}^n$ and $\omega \in \mathbb{R}$, and let
$V_1, \dots, V_p$ be the basis matrices of a projection family. With $A_i = A V_i$, one step
maps $x$ to
$$x + \omega \sum_{i=1}^p V_i d_i, \qquad d_i = (A_i^T A_i)^{-1} A_i^T r, \qquad r = b - Ax.$$
The scalar division of Algorithm 8.3 is replaced by the least-squares problem
$\min_d \|r - A_i d\|_2$ (`SaadSparse.Chapter08.blockCimmino_isMinResidual`).

The inverse is Mathlib's matrix inverse, which is $0$ for a singular matrix. So if $A_i^T A_i$
is singular, then $d_i = 0$ and block $i$ adds no correction. -/
noncomputable def blockCimmino (𝒱 : Chapter05.ProjFamily n) (x : E n) : E n :=
  x + ∑ i, ω • ((𝒱.V i * ((A * 𝒱.V i)ᵀ * (A * 𝒱.V i))⁻¹ * (A * 𝒱.V i)ᵀ) ⬝ (b - (A ⬝ x)))

variable {A b ω}

/-- For $A \in \mathbb{R}^{n \times n}$ and a projection family $V_1, \dots, V_p$, the block Cimmino
step is one step of the additive projection process of Section 5.4
(`SaadSparse.Chapter05.additiveStep`) for the normal equations $A^T A x = A^T b$ over the
family, with all weights equal to $\omega$. For one-dimensional blocks this is
`SaadSparse.Chapter08.cimmino_eq_additiveStep`. -/
theorem blockCimmino_eq_additiveStep (𝒱 : Chapter05.ProjFamily n) (x : E n) :
    blockCimmino A b ω 𝒱 x = Chapter05.additiveStep 𝒱 (Aᵀ * A) (fun _ => ω) (Aᵀ ⬝ b) x := by
  rw [blockCimmino, Chapter05.additiveStep]
  refine congrArg (fun z : E n => x + z) (Finset.sum_congr rfl fun i _ => ?_)
  refine congrArg (fun z : E n => ω • z) ?_
  have hmat : 𝒱.V i * ((A * 𝒱.V i)ᵀ * (A * 𝒱.V i))⁻¹ * (A * 𝒱.V i)ᵀ
      = (𝒱.V i * ((𝒱.V i)ᵀ * (Aᵀ * A) * 𝒱.V i)⁻¹ * (𝒱.V i)ᵀ) * Aᵀ := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [Chapter05.corrector, normal_residual, ← Matrix.toEuclideanLin_mul_apply, hmat]

/-- **Equations (8.26)–(8.27)** of [saad2003iterative], the block correction. Let
$A \in \mathbb{R}^{n \times n}$, let $V_i$ be a basis matrix of a projection family, and let
$A_i = A V_i$ with $A_i^T A_i$ nonsingular. Then for every $r \in \mathbb{R}^n$ the correction
$d_i = (A_i^T A_i)^{-1} A_i^T r$ solves the least-squares problem $\min_d \|r - A_i d\|_2$:
$$\|r - A_i d_i\|_2 \le \|r - A_i d\|_2 \quad \text{for all } d.$$
So each substep reduces the residual as far as the columns of $A_i$ allow. The proof is
`SaadSparse.Chapter08.equation_8_1` for the matrix $A_i$. -/
theorem blockCimmino_isMinResidual {𝒱 : Chapter05.ProjFamily n} {i : Fin 𝒱.p}
    (h : IsUnit ((A * 𝒱.V i)ᵀ * (A * 𝒱.V i))) (r : E n) :
    ∀ d : EuclideanSpace ℝ (Fin (𝒱.size i)),
      ‖r - ((A * 𝒱.V i) ⬝ ((((A * 𝒱.V i)ᵀ * (A * 𝒱.V i))⁻¹ * (A * 𝒱.V i)ᵀ) ⬝ r))‖
        ≤ ‖r - ((A * 𝒱.V i) ⬝ d)‖ := by
  have hH : (A * 𝒱.V i)ᴴ = (A * 𝒱.V i)ᵀ := Chapter05.conjTranspose_eq_transpose _
  have hnormal : (((A * 𝒱.V i)ᴴ * (A * 𝒱.V i))
      ⬝ ((((A * 𝒱.V i)ᵀ * (A * 𝒱.V i))⁻¹ * (A * 𝒱.V i)ᵀ) ⬝ r)) = ((A * 𝒱.V i)ᴴ ⬝ r) := by
    rw [hH, ← Matrix.toEuclideanLin_mul_apply, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 h), Matrix.one_mul]
  exact (equation_8_1 (A * 𝒱.V i) r _).1 hnormal

/-!
### Section 8.2.1: the sweeps converge for $0 < \omega < 2$

The back-reference to Chapter 4 at the end of Section 8.2.1: $A^T A$ is symmetric positive definite
when $A$ is nonsingular, so Theorem 4.10 applies to it, and the NR-SOR sweep converges for every
$0 < \omega < 2$. The bridge is `SaadSparse.Chapter08.nrSORSweep_eq_sorStep`: a whole NR-SOR sweep
is one SOR step for the normal equations. Relaxation $i$ changes only the $i$-th entry, and changes
it by $\omega (A^T b - A^T A x)_i / (A^T A)_{ii}$, with the entries below $i$ already updated and
those above $i$ not yet. This is the SOR recursion in the ordering $i = 1, \dots, n$.
-/

section Convergence

variable {A : Matrix (Fin n) (Fin n) ℝ} {b : E n} {ω : ℝ}

/-- **Section 8.2.1** of [saad2003iterative], the diagonal of the normal equations. For
$A \in \mathbb{R}^{n \times n}$, the $i$-th diagonal entry of $A^T A$ is the squared norm of the
$i$-th column of $A$:
$$(A^T A)_{ii} = \|Ae_i\|_2^2.$$
-/
theorem normal_diag (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (Aᵀ * A) i i = ‖A ⬝ coordVec i‖ ^ 2 := by
  rw [← inner_normal_coordVec A i, inner_coordVec]
  simp [coordVec, Matrix.mulVec_single, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- One NR-SOR relaxation of index $i$ changes only the $i$-th entry of $x$, and adds to it
$\omega (A^T b - A^T A x)_i / (A^T A)_{ii}$. -/
private theorem ofLp_nrSORStep (i : Fin n) (x : E n) :
    WithLp.ofLp (nrSORStep A b ω i x)
      = Function.update (WithLp.ofLp x) i
          (WithLp.ofLp x i + ω * WithLp.ofLp ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x)) i / (Aᵀ * A) i i) := by
  have hnum : inner ℝ (A ⬝ coordVec i) (b - (A ⬝ x))
      = WithLp.ofLp ((Aᵀ ⬝ b) - ((Aᵀ * A) ⬝ x)) i := by
    rw [normal_residual, ← inner_transpose', inner_coordVec]
  rw [nrSORStep, hnum, ← normal_diag]
  funext j
  rw [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne j i with rfl | hj
  · rw [Function.update_self]
    simp [coordVec]
  · rw [Function.update_of_ne hj]
    simp [coordVec, hj]

/-- **Section 8.2.1** of [saad2003iterative], the NR-SOR sweep as an SOR step. Let
$A \in \mathbb{R}^{n \times n}$ such that the diagonal of $A^T A$ is nonsingular, that is, $A$
has no zero column, and let $b, x \in \mathbb{R}^n$ and $\omega \in \mathbb{R}$. Then one NR-SOR
sweep from $x$ is one SOR step (4.12) for the normal equations $A^T A x = A^T b$:
$$x_{\mathrm{new}} = (D - \omega E)^{-1} \bigl((\omega F + (1 - \omega) D) x + \omega A^T
  b\bigr), \qquad A^T A = D - E - F.$$
No condition on $\omega$ is needed.

The SOR step is `SaadSparse.Chapter04.sorStep`, stated in plain coordinates. Relaxation $i$ is
the SOR relaxation `Matrix.sorRelax` of the $i$-th unknown of the normal equations, and a loop
of SOR relaxations in the natural order is the SOR sweep (`Matrix.foldl_sorRelax_eq_sorSweep`). -/
theorem nrSORSweep_eq_sorStep (hd : IsUnit (Matrix.diagPart (Aᵀ * A))) (x : E n) :
    WithLp.ofLp (nrSORSweep A b ω x)
      = Chapter04.sorStep (Aᵀ * A) ω (WithLp.ofLp ((Aᵀ ⬝ b) : E n)) (WithLp.ofLp x) := by
  have hfold : ∀ (l : List (Fin n)) (y : E n),
      WithLp.ofLp (l.foldl (fun y i => nrSORStep A b ω i y) y)
        = l.foldl (fun z i => Matrix.sorRelax (Aᵀ * A) ω (WithLp.ofLp ((Aᵀ ⬝ b) : E n)) i z)
          (WithLp.ofLp y) := by
    intro l
    induction l with
    | nil => intro y; rfl
    | cons i l ih =>
      intro y
      rw [List.foldl_cons, List.foldl_cons, ih, ofLp_nrSORStep]
      rfl
  have hsor : Chapter04.sorStep (Aᵀ * A) ω (WithLp.ofLp ((Aᵀ ⬝ b) : E n))
      = Matrix.sorSweep (Aᵀ * A) ω (WithLp.ofLp ((Aᵀ ⬝ b) : E n)) := by
    funext y
    rw [Chapter04.sorStep, Matrix.sorSweep, Chapter04.D, Chapter04.E, Chapter04.F, smul_neg,
      sub_neg_eq_add, smul_neg, neg_add_eq_sub]
  rw [nrSORSweep, hfold, Matrix.foldl_sorRelax_eq_sorSweep hd, hsor]

/-- **Section 8.2.1** of [saad2003iterative], convergence of the NR-SOR sweep. Let
$A \in \mathbb{R}^{n \times n}$ be nonsingular, let $b, x_0 \in \mathbb{R}^n$, and let
$0 < \omega < 2$. Then the iterates of the NR-SOR sweep from $x_0$ converge to the solution
$(A^T A)^{-1} A^T b$ of the normal equations $A^T A x = A^T b$.

The book states this as a back-reference to Chapter 4. The proof is Theorem 4.10 applied to the
symmetric positive definite matrix $A^T A$, through
`SaadSparse.Chapter08.nrSORSweep_eq_sorStep`. The convergence is stated in plain coordinates,
through `WithLp.ofLp`. -/
theorem sorSweep_tendsto (hA : IsUnit A) (hω0 : 0 < ω) (hω2 : ω < 2) (x₀ : E n) :
    Tendsto (fun k => WithLp.ofLp ((nrSORSweep A b ω)^[k] x₀)) atTop
      (𝓝 ((Aᵀ * A)⁻¹ *ᵥ WithLp.ofLp ((Aᵀ ⬝ b) : E n))) := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have hinjVec : Function.Injective (Aᵀ * A).mulVec := by
    refine Matrix.mulVec_injective_of_isUnit ?_
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_transpose]
    exact hAdet.mul hAdet
  have hposdiag : ∀ i : Fin n, 0 < (Aᵀ * A) i i := by
    intro i
    rw [normal_diag]
    have hne : (A ⬝ coordVec i) ≠ 0 := by
      intro h
      have hzero : (Aᵀ * A) *ᵥ WithLp.ofLp (coordVec i) = (Aᵀ * A) *ᵥ 0 := by
        rw [Matrix.mulVec_zero, show ((Aᵀ * A) *ᵥ WithLp.ofLp (coordVec i))
            = WithLp.ofLp ((Aᵀ * A) ⬝ coordVec i) from rfl,
          Matrix.toEuclideanLin_mul_apply,
          show (Matrix.toEuclideanLin A) (coordVec i) = (A ⬝ coordVec i) from rfl, h, map_zero]
        rfl
      exact absurd (congrFun (hinjVec hzero) i) (by simp [coordVec])
    positivity
  have hd : IsUnit (Matrix.diagPart (Aᵀ * A)) :=
    (Matrix.isUnit_diagPart_iff _).2 fun i => (hposdiag i).ne'
  have hsymm : (Aᵀ * A).IsSymm := by
    rw [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hposdef : (Aᵀ * A).PosDef := by
    have h := Matrix.PosDef.conjTranspose_mul_self A (Matrix.mulVec_injective_of_isUnit hA)
    rwa [Chapter05.conjTranspose_eq_transpose] at h
  have hρ : Matrix.complexSpectralRadius
      ((Aᵀ * A).sorSplitting hd hω0.ne').iterationOperator < 1 :=
    (Chapter04.theorem_4_10 hsymm hposdiag hd hω0 hω2).2 hposdef
  have hiter : ∀ k : ℕ, WithLp.ofLp ((nrSORSweep A b ω)^[k] x₀)
      = (Chapter04.sorStep (Aᵀ * A) ω (WithLp.ofLp ((Aᵀ ⬝ b) : E n)))^[k] (WithLp.ofLp x₀) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
        nrSORSweep_eq_sorStep hd]
  simp only [hiter]
  rw [Chapter04.sorStep_eq hd hω0.ne']
  exact Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one _ hρ _ _

end Convergence

end SaadSparse.Chapter08
