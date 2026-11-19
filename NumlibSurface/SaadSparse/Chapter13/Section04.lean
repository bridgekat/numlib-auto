/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Numlib.Multigrid.FullMultigrid
import NumlibSurface.SaadSparse.Chapter02.Section02
import NumlibSurface.SaadSparse.Chapter13.Section02
import NumlibSurface.SaadSparse.Chapter13.Section03
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 13.4: The standard multigrid cycles

This module formalizes Section 13.4 of [saad2003iterative]: the Galerkin coarse problem (13.39), the
smoother written through its error propagation operator (13.40)–(13.42), the two-grid operator
(13.43) and Lemma 13.1, the V- and W-cycles, the cost of one cycle (13.44), and full multigrid with
its error bound, Theorem 13.2. The section works with a general pair of grids: a fine matrix $A_h$,
a prolongation $I_H^h$ and a restriction $I_h^H$. The standing hypotheses are that $A_h$ is
symmetric positive definite, that $I_H^h$ is injective, and that $I_h^H$ is a positive multiple of
$(I_H^h)^T$, as in (13.37). Under them the coarse-grid projector $Q_h = I_H^h A_H^{-1} I_h^H A_h$ is
the $A_h$-orthogonal projector onto the range of $I_H^h$, and Lemma 13.1 follows from this.

The proofs specialize `Numlib.Multigrid.Basic` and `Numlib.Multigrid.FullMultigrid`. The cycles of
Algorithms 13.3–13.5 are definitions only, as in the book: the book proves nothing about them
directly, since the error operator of a cycle is a perturbation of the two-grid operator, whose
analysis is Section 13.5. The theorems about the cycles are the cost bound (13.44) and the full
multigrid error bound, Theorem 13.2. Example 13.6 makes the discretization-error assumption of
Theorem 13.2 concrete for the one-dimensional model problem, with the truncation error (2.12) of
Section 2.2 and the spectrum of the model matrix from Section 13.2.

## Main definitions

* Equation (13.39), `SaadSparse.Chapter13.coarseOperator`: the Galerkin coarse matrix
  $A_H = I_h^H A_h I_H^h$.
* Equation (13.39), `SaadSparse.Chapter13.coarseRhs`: the coarse right-hand side $f^H = I_h^H f^h$.
* Equations (13.40)–(13.41), `SaadSparse.Chapter13.smoother`: the error propagation operator
  $S = I - BA$ of a smoother.
* Equation (13.41), `SaadSparse.Chapter13.smootherStep`: one smoothing step $u \leftarrow Su + Bf$.
* Section 13.4.2, `SaadSparse.Chapter13.IsCoarsening`: the standing hypotheses on a pair of grids.
* Equation (13.43), `SaadSparse.Chapter13.coarsePreconditioner`: the matrix $I_H^h A_H^{-1} I_h^H$.
* Equation (13.43), `SaadSparse.Chapter13.coarseProjector`: the coarse-grid projector
  $Q_h = I_H^h A_H^{-1} I_h^H A_h$.
* Equation (13.43), `SaadSparse.Chapter13.coarseCorrection`: the coarse-grid correction operator
  $T_h^H = I - Q_h$.
* Equation (13.43), `SaadSparse.Chapter13.equation_13_43`: the two-grid operator
  $M_H^h = S^{\nu_2} T_h^H S^{\nu_1}$.
* Section 13.4.3, `SaadSparse.Chapter13.Hierarchy`: the data of a multigrid hierarchy.
* Algorithm 13.4, `SaadSparse.Chapter13.Hierarchy.cycle`: the $\gamma$-cycle.
* Algorithm 13.3, `SaadSparse.Chapter13.Hierarchy.vcycle`: the V-cycle, $\gamma = 1$.
* Section 13.4.3, `SaadSparse.Chapter13.Hierarchy.wcycle`: the W-cycle, $\gamma = 2$.
* Algorithm 13.5, `SaadSparse.Chapter13.Hierarchy.fullMultigrid`: full multigrid.
* Example 13.6, `SaadSparse.Chapter13.gridSample`: the samples of a function at the interior grid
  points.
* Example 13.6, `SaadSparse.Chapter13.discreteL2Norm`: the discrete $L^2$ norm
  $\|v\|_h = h^{1/2}\|v\|_2$.

## Main results

* Equation (13.39), `SaadSparse.Chapter13.coarseOperator_eq_galerkinCoarse`: with
  $I_h^H = c \, (I_H^h)^T$, the coarse matrix is $c$ times the backbone Galerkin operator.
* Equation (13.39), `SaadSparse.Chapter13.posDef_coarseOperator`: the coarse matrix is symmetric
  positive definite.
* Example 13.2, `SaadSparse.Chapter13.example_13_2`: for the one-dimensional model problem,
  $I_h^{2h} A_h I_{2h}^h = \frac14 \operatorname{tridiag}(-1, 2, -1)$.
* Equation (13.41), `SaadSparse.Chapter13.equation_13_41`: the smoothing step is
  $u \leftarrow u + B(f - Au)$.
* Equation (13.41), `SaadSparse.Chapter13.smoother_eq_smootherOperator`: the smoother is the
  backbone error propagation operator.
* Equation (13.42), `SaadSparse.Chapter13.equation_13_42`: $B = (I - S)A^{-1}$.
* Equation (13.42), `SaadSparse.Chapter13.smootherStep_iterate_sub`: the error after $\nu$ smoothing
  steps is $S^\nu d_0$.
* Equation (13.42), `SaadSparse.Chapter13.smootherStep_iterate_residual`: the residual after $\nu$
  smoothing steps is $(I - AB)^\nu r_0$.
* Example 13.3, `SaadSparse.Chapter13.example_13_3_jacobi`,
  `SaadSparse.Chapter13.example_13_3_gaussSeidel` and
  `SaadSparse.Chapter13.example_13_3_richardson`: the Jacobi, Gauss–Seidel and Richardson smoothers.
* Section 13.4.2, `SaadSparse.Chapter13.isCoarsening_model`: the one-dimensional model problem with
  linear interpolation and full weighting satisfies the standing hypotheses.
* Section 13.4.2, `SaadSparse.Chapter13.IsCoarsening.isSymmetricCoercive`: the fine matrix is a
  symmetric coercive operator.
* Equation (13.43), `SaadSparse.Chapter13.toEuclideanLin_coarseProjector`: $Q_h$ is the
  $A_h$-orthogonal projector onto the range of $I_H^h$.
* Equation (13.43), `SaadSparse.Chapter13.toEuclideanLin_coarseCorrection`: $T_h^H$ is the backbone
  coarse-grid correction.
* Equation (13.43), `SaadSparse.Chapter13.equation_13_43_eq`: the two-grid operator is the backbone
  two-grid operator.
* Lemma 13.1, `SaadSparse.Chapter13.lemma_13_1`: $T_h^H$ is a projector.
* Lemma 13.1, `SaadSparse.Chapter13.lemma_13_1_energyInner`: $T_h^H$ is self-adjoint in the
  $A_h$-inner product.
* Lemma 13.1, `SaadSparse.Chapter13.lemma_13_1_energyInner_eq_zero`: the range of $T_h^H$ is
  $A_h$-orthogonal to the range of $I_H^h$.
* Equation (13.44), `SaadSparse.Chapter13.equation_13_44`: if $\gamma < 2^d$, the cost of a
  $\gamma$-cycle is at most $\eta n_l/(1 - \gamma 2^{-d})$.
* Theorem 13.2, `SaadSparse.Chapter13.theorem_13_2`: the full multigrid error bound.
* Example 13.6, `SaadSparse.Chapter13.dirichletExt_gridSample`: the Dirichlet extension of a sampled
  function with zero boundary values.
* Example 13.6, `SaadSparse.Chapter13.example_13_6_truncation`: the truncation error is at most
  $Kh^2/12$ in each component.
* Example 13.6, `SaadSparse.Chapter13.example_13_6`: the discretization error is at most
  $Kh^4/(48\sin^2(\pi h/2))$ in the discrete $L^2$ norm.
* Example 13.6, `SaadSparse.Chapter13.example_13_6_le`: the closing display of the example,
  corrected.

## Implementation notes

* All matrices are real and indexed by `Fin n` and `Fin m`. The book's $Ax$ is
  `Matrix.toEuclideanLin A x`, written `A ⬝ x`.
* The factor $c$ in $I_h^H = c \, (I_H^h)^T$ multiplies both sides of the coarse equation and
  therefore cancels. This is `SaadSparse.Chapter13.coarseProjection_apply_eq_of_smul` of Section
  13.3. The backbone coarse-grid projector `Multigrid.coarseProjection` is the orthogonal projector
  in the energy inner product, so Lemma 13.1 is the idempotence, the self-adjointness and the range
  of that projector.
* A hierarchy is indexed by all of $\mathbb{N}$, with level $0$ the coarsest. A cycle on level $l$
  uses only the levels $0, \dots, l$.
* Example 13.6 uses the scaled model matrix `SaadSparse.Chapter02.laplacian1D n h`
  $= h^{-2}\operatorname{tridiag}(-1, 2, -1)$ of Section 2.2, not the unscaled matrix of Section
  13.2.

## Deviations from the source

* **§13.4.1, after (13.42)** (convention). `SaadSparse.Chapter13.smootherStep_iterate_sub`
  defines the error using the iterate minus the exact solution, reversing the sign convention in
  (13.16). The residual convention is unchanged.
* **(13.43) and Lemma 13.1** (scope and hypotheses). `SaadSparse.Chapter13.equation_13_43`
  defines the full error composition in the preceding display. Printed (13.43) defines the
  coarse correction alone. The inverse in the definitions is total. The projector and
  orthogonality statements assume positive definiteness, injective prolongation and positive-
  scaled transpose restriction.
* **Algorithms 13.3–13.5** (representation). `SaadSparse.Chapter13.Hierarchy` uses natural-
  number levels with an exact inverse-based solve at level zero on the nonsingular domain. The
  $\gamma$-cycle repeats its coarse solver uniformly, which has the same effect as a single
  direct solve at the bottom for $\gamma\ge1$. It also admits $\gamma=0$, when the coarse solver
  is skipped.
* **Theorem 13.2** (reading). `SaadSparse.Chapter13.theorem_13_2` uses Euclidean norms, assumes
  a bound on actual cycle error in place of the linear operator norm, and states the solved
  nonsingular base level explicitly. The argument needs $\xi\ge0$ and $c_2\xi^\mu<1$.
* **Example 13.6, truncation error** (scope). `SaadSparse.Chapter13.example_13_6_truncation`
  proves the componentwise inequality with $K$ bounding the absolute value of the fourth
  derivative. The source gives a Taylor identity with a point between neighboring grid nodes.
* **Example 13.2** (correction). The book's computation ends at
  $A_H e_j^H = -e_{j-1}^H + 2e_j^H - e_{j+1}^H$, which drops a factor $\frac14$; the Galerkin coarse
  matrix is $\frac14 \operatorname{tridiag}(-1, 2, -1)$. See `SaadSparse.Chapter13.example_13_2`.
* **Example 13.3** (correction). The book gives the Gauss–Seidel smoother as $B = (D - E)^{-1}F$;
  the approximate inverse is $B = (D - E)^{-1}$, and $(D - E)^{-1}F$ is the error propagation
  operator. See `SaadSparse.Chapter13.example_13_3_gaussSeidel`.
* **Lemma 13.1** (correction). The third clause names the restriction where the proof of the book
  gives the prolongation: the range of $T_h^H$ is $A_h$-orthogonal to the range of $I_H^h$. See
  `SaadSparse.Chapter13.lemma_13_1_energyInner_eq_zero`.
* **Equation (13.44)** (correction). The book prints the constant $7/3$ for the two-dimensional
  V-cycle; the geometric series $\sum_k 4^{-k}$ of the recurrence is $4/3$. See
  `SaadSparse.Chapter13.equation_13_44`.
* **Example 13.6** (correction). The closing display has $1 - (\pi h/2)^2/6$ in the denominator
  where the derivation gives its square. See `SaadSparse.Chapter13.example_13_6_le`.

## Not formalized

* **Algorithm 13.1** (nested iteration). The book presents it only to introduce the notation, and
  full multigrid supersedes it.
* **The identity $M_h = M_H^h + S^{\nu_2} I_H^h M_H A_H^{-1} I_h^H A_h$** at the end of Section
  13.4.3. It would need the error operator of the whole recursive cycle as an object of its own, and
  the book uses it nowhere.
* **Examples 13.4 and 13.5**, a table of measured V-cycle convergence factors and a plot of measured
  full multigrid errors. Both record floating-point runs and carry no mathematical claim. The
  comparisons that the book draws from them (red-black Gauss–Seidel is the best smoother, a balanced
  $(\nu_1, \nu_2)$ is better than an unbalanced one, the full multigrid error follows the
  discretization error) are read off the numbers and are not proved. The bound that the figure of
  Example 13.5 illustrates is the discretization-error assumption of Theorem 13.2, which
  `SaadSparse.Chapter13.example_13_6_le` states for the model problem.
-/

open Matrix Stationary

open scoped SaadSparse

namespace SaadSparse.Chapter13

variable {n m : ℕ}

/-! ### Section 13.4.1: The Galerkin coarse problem -/

/-- **Equation (13.39)** of [saad2003iterative]. The **Galerkin coarse matrix** of a fine matrix
$A_h \in \mathbb{R}^{n \times n}$, a restriction $I_h^H \in \mathbb{R}^{m \times n}$ and a
prolongation $I_H^h \in \mathbb{R}^{n \times m}$ is
$$A_H = I_h^H A_h I_H^h.$$
-/
def coarseOperator (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  R * A * P

/-- **Equation (13.39)** of [saad2003iterative]. The **coarse right-hand side** $f^H = I_h^H f^h$ of
a fine right-hand side $f^h$. -/
noncomputable def coarseRhs (R : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  R ⬝ f

/-- The adjoint of the linear map of a real matrix $P$ is the linear map of its transpose $P^T$. -/
theorem adjoint_toEuclideanLin (P : Matrix (Fin n) (Fin m) ℝ) :
    LinearMap.adjoint (toEuclideanLin P) = toEuclideanLin Pᵀ := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  congr 1

/-- The Galerkin coarse matrix $P^T A P$, built with the transpose of the prolongation as the
restriction, is the backbone Galerkin coarse operator `Multigrid.galerkinCoarse` of $A$ and $P$. -/
theorem coarseOperator_transpose_eq_galerkinCoarse (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    toEuclideanLin (coarseOperator Pᵀ A P)
      = Multigrid.galerkinCoarse (toEuclideanLin A) (toEuclideanLin P) := by
  have hdef : Multigrid.galerkinCoarse (toEuclideanLin A) (toEuclideanLin P)
      = LinearMap.adjoint (toEuclideanLin P) ∘ₗ toEuclideanLin A ∘ₗ toEuclideanLin P := rfl
  rw [hdef, adjoint_toEuclideanLin, coarseOperator, Matrix.toLpLin_mul_same,
    Matrix.toLpLin_mul_same, LinearMap.comp_assoc]

/-- Rescaling the restriction rescales the coarse matrix: $(cR) A P = c \, (RAP)$.

**Reading.** Proves rescaling identity for every real scale and arbitrary restriction.
-/
theorem coarseOperator_smul (c : ℝ) (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    coarseOperator (c • R) A P = c • coarseOperator R A P := by
  rw [coarseOperator, coarseOperator, Matrix.smul_mul, Matrix.smul_mul]

/-- **Equation (13.39)** of [saad2003iterative] with the restriction of (13.37). Let
$A \in \mathbb{R}^{n \times n}$, $P \in \mathbb{R}^{n \times m}$ and $c \in \mathbb{R}$. The
coarse matrix built with the restriction $c \, P^T$ is $c$ times the backbone Galerkin coarse
operator:
$$(c \, P^T) A P = c \, P^* A P.$$

The book's restriction is $2^{-d}(I_H^h)^T$ by (13.37), so $c = 2^{-d}$ there. The operator
$P^* A P$ is `Multigrid.galerkinCoarse`.

**Reading.** Bridges the two operators with arbitrary real factor rather than fixed 2⁻ᵈ.
-/
theorem coarseOperator_eq_galerkinCoarse (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    toEuclideanLin (coarseOperator (c • Pᵀ) A P)
      = c • Multigrid.galerkinCoarse (toEuclideanLin A) (toEuclideanLin P) := by
  rw [coarseOperator_smul, map_smul, coarseOperator_transpose_eq_galerkinCoarse]

/-- **Equation (13.39)** of [saad2003iterative], the coarse problem is well posed. Let
$A \in \mathbb{R}^{n \times n}$ be symmetric positive definite, let
$P \in \mathbb{R}^{n \times m}$ be injective, and let $c > 0$. Then the Galerkin coarse matrix
$(c \, P^T) A P$ is symmetric positive definite.

So the coarse solve of Algorithm 13.2 makes sense.

**Reading.** Explicit positive-definite fine matrix, injective P and positive restriction factor
ensure SPD coarse operator.
-/
theorem posDef_coarseOperator {A : Matrix (Fin n) (Fin n) ℝ} {P : Matrix (Fin n) (Fin m) ℝ}
    (hA : A.PosDef) (hP : Function.Injective (toEuclideanLin P)) {c : ℝ} (hc : 0 < c) :
    (coarseOperator (c • Pᵀ) A P).PosDef := by
  have h1 : (coarseOperator Pᵀ A P).PosDef := by
    rw [Matrix.posDef_iff_isSymmetricCoercive, coarseOperator_transpose_eq_galerkinCoarse]
    exact Multigrid.galerkinCoarse_isSymmetricCoercive
      ((Matrix.posDef_iff_isSymmetricCoercive A).1 hA) hP
  rw [coarseOperator_smul]
  exact Matrix.PosDef.smul h1 hc

/-! ### Example 13.2 -/

/-- Contracting a vector against a column of the interpolation matrix: since column $q$ has the
stencil $\frac12 [1\ 2\ 1]$ on the fine rows $a = 2q$, $b = 2q + 1$, $c = 2q + 2$, $\sum_i g_i
(I_{2h}^h)_{iq} = (g_a + 2g_b + g_c)/2$. -/
private theorem sum_mul_prolongation1D (m : ℕ) (g : Fin (2 * m + 1) → ℝ) (q : Fin m)
    {a b c : Fin (2 * m + 1)} (ha : (a : ℕ) = 2 * (q : ℕ)) (hb : (b : ℕ) = 2 * (q : ℕ) + 1)
    (hc : (c : ℕ) = 2 * (q : ℕ) + 2) :
    ∑ i, g i * prolongation1D m i q = (g a + 2 * g b + g c) / 2 := by
  have hstep : ∀ i : Fin (2 * m + 1), g i * prolongation1D m i q
      = 2 * (restriction1D m q i * g i) := fun i => by
    rw [prolongation1D_eq_smul_transpose, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun i _ => hstep i, ← Finset.mul_sum, ← Matrix.mulVec_apply_eq_sum,
    restriction1D_mulVec m g q ha hb hc]
  ring

/-- One column of $A_h I_{2h}^h$ for the one-dimensional model problem:
$\operatorname{tridiag}(-1, 2, -1)$ applied to the hat function centred at the fine point
$2q + 1$ gives $1$ there, $-\frac12$ at the fine points $2q - 1$ and $2q + 3$, and $0$
elsewhere. -/
private theorem laplacian1D_mul_prolongation1D_apply (m : ℕ) (i : Fin (2 * m + 1)) (q : Fin m) :
    (laplacian1D (2 * m + 1) * prolongation1D m) i q
      = if (i : ℕ) = 2 * (q : ℕ) + 1 then 1
        else if (i : ℕ) + 1 = 2 * (q : ℕ) then -(1 / 2)
        else if (i : ℕ) = 2 * (q : ℕ) + 3 then -(1 / 2) else 0 := by
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * m + 1), (a : ℕ) = 2 * (q : ℕ) := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (2 * m + 1), (b : ℕ) = 2 * (q : ℕ) + 1 := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin (2 * m + 1), (c : ℕ) = 2 * (q : ℕ) + 2 := ⟨⟨_, by omega⟩, rfl⟩
  rw [Matrix.mul_apply,
    sum_mul_prolongation1D m (fun k => laplacian1D (2 * m + 1) i k) q ha hb hc]
  simp only [laplacian1D_apply, ha, hb, hc]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **Example 13.2** of [saad2003iterative]. In one dimension, with linear interpolation $I_{2h}^h$
and full weighting $I_h^{2h}$, the Galerkin coarse matrix (13.39) of the model matrix is the
coarse model matrix:
$$I_h^{2h} \operatorname{tridiag}(-1, 2, -1)_{2m+1} \, I_{2h}^h = \tfrac14
  \operatorname{tridiag}(-1, 2, -1)_m.$$

**Correction.** The column-by-column computation of the book ends at
$A_H e_j^H = -e_{j-1}^H + 2e_j^H - e_{j+1}^H$, which drops the factor $\frac14$. Full weighting
$\frac14 [1\ 2\ 1]$ applied to the previous line of the book, $-\frac12 e^h_{2j-2} + e^h_{2j} -
\frac12 e^h_{2j+2}$, gives $-\frac14 e^H_{j-1} + \frac12 e^H_j - \frac14 e^H_{j+1}$.

The factor $\frac14$ is the ratio $h^2/(2h)^2$ of the two mesh sizes, because the matrices of
Section 13.2 are unscaled. For the scaled matrices $h^{-2}\operatorname{tridiag}(-1, 2, -1)$ of
Section 2.2.3 the identity reads $A_{2h} = I_h^{2h} A_h I_{2h}^h$ with no factor; in this sense
the Galerkin coarse operator is the coarse discretization. Exercise 6 of the chapter notes that
the corresponding statement is false in two dimensions with full weighting, which is why Section
13.4 takes the Galerkin definition, not the coarse discretization, as primary. -/
theorem example_13_2 (m : ℕ) :
    coarseOperator (restriction1D m) (laplacian1D (2 * m + 1)) (prolongation1D m)
      = (1 / 4 : ℝ) • laplacian1D m := by
  ext q q'
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * m + 1), (a : ℕ) = 2 * (q : ℕ) := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (2 * m + 1), (b : ℕ) = 2 * (q : ℕ) + 1 := ⟨⟨_, by omega⟩, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin (2 * m + 1), (c : ℕ) = 2 * (q : ℕ) + 2 := ⟨⟨_, by omega⟩, rfl⟩
  have hmul : coarseOperator (restriction1D m) (laplacian1D (2 * m + 1)) (prolongation1D m) q q'
      = ∑ i, restriction1D m q i * (laplacian1D (2 * m + 1) * prolongation1D m) i q' := by
    rw [coarseOperator, congrFun₂ (Matrix.mul_assoc (restriction1D m) (laplacian1D (2 * m + 1))
      (prolongation1D m)) q q', Matrix.mul_apply]
  rw [hmul, ← Matrix.mulVec_apply_eq_sum,
    restriction1D_mulVec m (fun i => (laplacian1D (2 * m + 1) * prolongation1D m) i q') q ha hb hc]
  simp only [laplacian1D_mul_prolongation1D_apply, Matrix.smul_apply, laplacian1D_apply,
    smul_eq_mul, ha, hb, hc]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-! ### Section 13.4.1: Smoothers -/

/-- The action of a product of matrices on a vector: $(MN)x = M(Nx)$. -/
private theorem mul_act {p q r : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (N : Matrix (Fin q) (Fin r) ℝ)
    (x : EuclideanSpace ℝ (Fin r)) : ((M * N) ⬝ x) = M ⬝ (N ⬝ x) := by
  rw [Matrix.toLpLin_mul_same]
  rfl

/-- The action of a difference of matrices on a vector: $(M - N)x = Mx - Nx$. -/
private theorem sub_act {p q : ℕ} (M N : Matrix (Fin p) (Fin q) ℝ)
    (x : EuclideanSpace ℝ (Fin q)) : ((M - N) ⬝ x) = (M ⬝ x) - (N ⬝ x) := by
  rw [map_sub]
  rfl

/-- The identity matrix acts as the identity: $Ix = x$. -/
private theorem one_act (x : EuclideanSpace ℝ (Fin n)) : ((1 : Matrix (Fin n) (Fin n) ℝ) ⬝ x) = x :=
  congrFun (congrArg _ (Matrix.toLpLin_one 2)) x

/-- **Equations (13.40)–(13.41)** of [saad2003iterative]. The **error propagation operator** of a
smoother with approximate inverse $B$ for the matrix $A$ is
$$S = I - BA.$$

A smoother enters the chapter only through this operator, because every statement of the theory
is about the error. -/
def smoother (A B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := 1 - B * A

/-- The error propagation operator of a smoother is $S = I - BA$. -/
theorem smoother_def (A B : Matrix (Fin n) (Fin n) ℝ) : smoother A B = 1 - B * A := rfl

/-- **Equation (13.41)** of [saad2003iterative]. One **smoothing step** for $Au = f$ is the affine
map
$$u \mapsto Su + g, \qquad g = Bf,$$
whose error propagation operator is $S = I - BA$. -/
noncomputable def smootherStep (A B : Matrix (Fin n) (Fin n) ℝ)
    (f u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (smoother A B ⬝ u) + (B ⬝ f)

/-- One smoothing step is $u \mapsto Su + Bf$. -/
theorem smootherStep_apply (A B : Matrix (Fin n) (Fin n) ℝ)
    (f u : EuclideanSpace ℝ (Fin n)) :
    smootherStep A B f u = (smoother A B ⬝ u) + (B ⬝ f) := rfl

/-- **Equation (13.41)** of [saad2003iterative], the preconditioning form. For all $A$, $B$, $f$ and
$u$, the smoothing step is
$$Su + Bf = u + B(f - Au).$$
-/
theorem equation_13_41 (A B : Matrix (Fin n) (Fin n) ℝ)
    (f u : EuclideanSpace ℝ (Fin n)) :
    smootherStep A B f u = u + (B ⬝ (f - (A ⬝ u))) := by
  simp only [smootherStep_apply, smoother_def, sub_act, one_act, mul_act]
  simp only [map_sub]
  abel

/-- **Equation (13.41)** of [saad2003iterative], the backbone form. The error propagation operator
$I - BA$ of a smoother is the backbone operator `Multigrid.smootherOperator` of $A$ and $B$. -/
theorem smoother_eq_smootherOperator (A B : Matrix (Fin n) (Fin n) ℝ) :
    toEuclideanLin (smoother A B)
      = Multigrid.smootherOperator (toEuclideanLin A) (toEuclideanLin B) := by
  have hdef : Multigrid.smootherOperator (toEuclideanLin A) (toEuclideanLin B)
      = 1 - toEuclideanLin B ∘ₗ toEuclideanLin A := rfl
  rw [smoother_def, hdef, map_sub, Matrix.toLpLin_mul_same, Matrix.toLpLin_one]
  rfl

/-- **Equation (13.42)** of [saad2003iterative]. Let $A$ be nonsingular. The approximate inverse is
recovered from the error propagation operator:
$$B = (I - S)A^{-1}.$$
-/
theorem equation_13_42 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (B : Matrix (Fin n) (Fin n) ℝ) : (1 - smoother A B) * A⁻¹ = B := by
  rw [smoother_def, sub_sub_cancel, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA), Matrix.mul_one]

/-- The solution of $Ax = f$ is a fixed point of the smoothing step: the smoother is consistent. -/
theorem smootherStep_of_eq {A B : Matrix (Fin n) (Fin n) ℝ} {f x : EuclideanSpace ℝ (Fin n)}
    (hx : (A ⬝ x) = f) : smootherStep A B f x = x := by
  simp only [smootherStep_apply, smoother_def, sub_act, one_act, mul_act, hx]
  abel

/-- One smoothing step multiplies the error by $S$: if $Ax = f$, then $(Su + Bf) - x = S(u - x)$.

**Reading.** Uses iterate minus solution for the error.
-/
theorem smootherStep_sub {A B : Matrix (Fin n) (Fin n) ℝ} {f x : EuclideanSpace ℝ (Fin n)}
    (hx : (A ⬝ x) = f) (u : EuclideanSpace ℝ (Fin n)) :
    smootherStep A B f u - x = smoother A B ⬝ (u - x) := by
  have hfix : (smoother A B ⬝ x) + (B ⬝ f) = x := smootherStep_of_eq hx
  conv_lhs => rw [smootherStep_apply, ← hfix]
  rw [map_sub]
  abel

/-- **Equation (13.42)** of [saad2003iterative], the error. Let $Ax = f$. After $\nu$ smoothing
steps from $u_0$, the error is
$$d_\nu = S^\nu d_0, \qquad d_0 = u_0 - x.$$

**Reading.** Power identity with iterate minus solution convention.
-/
theorem smootherStep_iterate_sub {A B : Matrix (Fin n) (Fin n) ℝ}
    {f x : EuclideanSpace ℝ (Fin n)} (hx : (A ⬝ x) = f) (u₀ : EuclideanSpace ℝ (Fin n)) (ν : ℕ) :
    (smootherStep A B f)^[ν] u₀ - x = (smoother A B ^ ν) ⬝ (u₀ - x) := by
  induction ν with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_act]
  | succ ν ih =>
    rw [Function.iterate_succ_apply', smootherStep_sub hx, ih, ← mul_act, ← pow_succ']

/-- **Equation (13.42)** of [saad2003iterative], the residual. After $\nu$ smoothing steps from
$u_0$, the residual $r_\nu = f - Au_\nu$ is
$$r_\nu = (I - AB)^\nu r_0.$$

No hypothesis on $A$ is needed: the system $Au = f$ need not have a solution. -/
theorem smootherStep_iterate_residual (A B : Matrix (Fin n) (Fin n) ℝ)
    (f u₀ : EuclideanSpace ℝ (Fin n)) (ν : ℕ) :
    f - (A ⬝ ((smootherStep A B f)^[ν] u₀)) = ((1 - A * B) ^ ν) ⬝ (f - (A ⬝ u₀)) := by
  have hstep : ∀ u : EuclideanSpace ℝ (Fin n), f - (A ⬝ (smootherStep A B f u))
      = (1 - A * B) ⬝ (f - (A ⬝ u)) := fun u => by
    simp only [smootherStep_apply, smoother_def, sub_act, one_act, mul_act]
    simp only [map_add, map_sub]
    abel
  induction ν with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_act]
  | succ ν ih =>
    rw [Function.iterate_succ_apply', hstep, ih, ← mul_act, ← pow_succ']

/-- **Example 13.3** of [saad2003iterative], the Jacobi smoother. Let the diagonal $D$ of $A$ be
invertible. The Jacobi smoother has $B = D^{-1}$, and its error propagation operator
$I - D^{-1}A$ is the Jacobi iteration matrix, the iteration operator of
`Matrix.jacobiSplitting`. -/
theorem example_13_3_jacobi (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (diagPart A)) :
    smoother A (diagPart A)⁻¹ = (A.jacobiSplitting h).iterationOperator := by
  change 1 - (diagPart A)⁻¹ * A = 1 - Ring.inverse (diagPart A) * A
  rw [Matrix.nonsing_inv_eq_ringInverse]

/-- **Example 13.3** of [saad2003iterative], the Gauss–Seidel smoother. Let $A = D - E - F$ with $D$
the diagonal, $-E$ the strictly lower part and $-F$ the strictly upper part, and let $D$ be
invertible. The Gauss–Seidel smoother has $B = (D - E)^{-1}$, and its error propagation operator
$I - (D - E)^{-1}A = (D - E)^{-1}F$ is the Gauss–Seidel iteration matrix, the iteration operator
of `Matrix.gaussSeidelSplitting`.

**Correction.** The book gives the smoother as $B = (D - E)^{-1}F$. That matrix is the error
propagation operator $S$; the approximate inverse is $B = (D - E)^{-1}$.

The matrix $D - E$ is `diagPart A + strictLower A`. -/
theorem example_13_3_gaussSeidel (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (diagPart A)) :
    smoother A (diagPart A + strictLower A)⁻¹ = (A.gaussSeidelSplitting h).iterationOperator := by
  change 1 - (diagPart A + strictLower A)⁻¹ * A
    = 1 - Ring.inverse (diagPart A + strictLower A) * A
  rw [Matrix.nonsing_inv_eq_ringInverse]

/-- **Example 13.3** of [saad2003iterative], Richardson's smoother. Let $\omega \neq 0$.
Richardson's smoother has $B = \omega I$, and its error propagation operator is $I - \omega A$,
the iteration operator of `Stationary.Splitting.richardson`.

The hypothesis $\omega \neq 0$ is needed to define the splitting.

**Reading.** B=omega I with nonzero omega to use backbone splitting.
-/
theorem example_13_3_richardson (A : Matrix (Fin n) (Fin n) ℝ) {ω : ℝ} (hω : ω ≠ 0) :
    smoother A (ω • 1) = (Stationary.Splitting.richardson A hω).iterationOperator := by
  rw [Stationary.Splitting.richardson_iterationOperator, smoother_def, Matrix.smul_mul,
    Matrix.one_mul]

/-! ### Section 13.4.2: The two-grid cycle, (13.43) and Lemma 13.1 -/

/-- **Section 13.4.2** of [saad2003iterative], the standing hypotheses on a pair of grids. A fine
matrix $A \in \mathbb{R}^{n \times n}$, a restriction $R \in \mathbb{R}^{m \times n}$ and a
prolongation $P \in \mathbb{R}^{n \times m}$ form a **coarsening** if $A$ is symmetric positive
definite, $P$ is injective, and $R = c \, P^T$ for some $c > 0$, as in (13.37).

Under these hypotheses the Galerkin coarse matrix (13.39) is nonsingular, so the coarse solve of
Algorithm 13.2 makes sense, and the coarse-grid correction (13.43) is the $A$-orthogonal
projector of Lemma 13.1. The one-dimensional model problem of Sections 13.2–13.3 satisfies them
(`SaadSparse.Chapter13.isCoarsening_model`).

**Reading.** Makes SPD and injectivity assumptions explicit and includes arbitrary positive scalar
transpose relationship.
-/
structure IsCoarsening (A : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) : Prop where
  /-- The fine matrix $A$ is symmetric positive definite. -/
  posDef : A.PosDef
  /-- The prolongation $P$ is injective, so the coarse space has the dimension of the coarse grid.
  -/
  injective : Function.Injective (toEuclideanLin P)
  /-- The restriction is a positive multiple of the transpose of the prolongation, $R = c \, P^T$
  with $c > 0$, as in (13.37). -/
  exists_smul : ∃ c : ℝ, 0 < c ∧ R = c • Pᵀ

/-- **Section 13.4.2** of [saad2003iterative], the model problem. The one-dimensional model matrix
$\operatorname{tridiag}(-1, 2, -1)$ of size $2m + 1$, with full weighting as the restriction and
linear interpolation as the prolongation, is a coarsening.

The model matrix is positive definite, linear interpolation is injective, and full weighting is
$\frac12 (I_{2h}^h)^T$ by (13.35). -/
theorem isCoarsening_model (m : ℕ) :
    IsCoarsening (laplacian1D (2 * m + 1)) (restriction1D m) (prolongation1D m) :=
  ⟨laplacian1D_posDef _, injective_prolongation1D m, 1 / 2, by norm_num, equation_13_35 m⟩

namespace IsCoarsening

variable {A : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin m) (Fin n) ℝ}
  {P : Matrix (Fin n) (Fin m) ℝ}

/-- **Section 13.4.2** of [saad2003iterative]. If $(A, R, P)$ is a coarsening, then $A$ is a
symmetric coercive operator.

This is the hypothesis under which the energy inner product $(x, y)_A$ and the backbone
coarse-grid projector exist. -/
theorem isSymmetricCoercive (h : IsCoarsening A R P) : (toEuclideanLin A).IsSymmetricCoercive :=
  (Matrix.posDef_iff_isSymmetricCoercive A).1 h.posDef

/-- If $(A, R, P)$ is a coarsening, then the Galerkin coarse matrix $RAP$ of (13.39) is symmetric
positive definite.

**Reading.** Well-posed coarse problem given explicit rank, SPD and positive scaling conditions.
-/
theorem posDef_coarseOperator (h : IsCoarsening A R P) : (coarseOperator R A P).PosDef := by
  obtain ⟨c, hc, rfl⟩ := h.exists_smul
  exact _root_.SaadSparse.Chapter13.posDef_coarseOperator h.posDef h.injective hc

/-- If $(A, R, P)$ is a coarsening, then the Galerkin coarse matrix $RAP$ of (13.39) is nonsingular,
so $A_H^{-1}$ in (13.43) is a true inverse.

**Reading.** Invertibility of coarse matrix from the same additional hypotheses.
-/
theorem isUnit_coarseOperator (h : IsCoarsening A R P) : IsUnit (coarseOperator R A P) :=
  h.posDef_coarseOperator.isUnit

/-- If $(A, R, P)$ is a coarsening, then $A_H A_H^{-1} = I$ for the Galerkin coarse matrix
$A_H = RAP$. This makes the coarse solve of (13.43) exact.

**Reading.** Exhibits inverse product under the specified coarsening predicates.
-/
theorem coarseOperator_mul_inv (h : IsCoarsening A R P) :
    coarseOperator R A P * (coarseOperator R A P)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit_coarseOperator)

end IsCoarsening

/-- **Equation (13.43)** of [saad2003iterative]. The **coarse-grid preconditioner**
$$B_h = I_H^h A_H^{-1} I_h^H,$$
which restricts a fine residual, solves the coarse problem and interpolates the correction back.
Here $A_H$ is the Galerkin coarse matrix (13.39).

The inverse is the Lean matrix inverse, which is $0$ for a singular matrix; under the hypotheses
of `SaadSparse.Chapter13.IsCoarsening` the matrix $A_H$ is nonsingular.

**Reading.** Source formula for invertible coarse operator, totalized at singular coarse operators.
-/
noncomputable def coarsePreconditioner (R : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  P * (coarseOperator R A P)⁻¹ * R

/-- **Equation (13.43)** of [saad2003iterative]. The **coarse-grid projector**
$$Q_h = I_H^h A_H^{-1} I_h^H A_h = B_h A_h.$$

**Reading.** Uses QA coarse inverse product with total inverse beyond source domain.
-/
noncomputable def coarseProjector (R : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  coarsePreconditioner R A P * A

/-- **Equation (13.43)** of [saad2003iterative]. The **coarse-grid correction operator**
$$T_h^H = I - I_H^h A_H^{-1} I_h^H A_h,$$
the error propagation operator of one coarse-grid correction.

**Reading.** Formula I−P A_H⁻¹ R A with total inverse at singular coarse matrix.
-/
noncomputable def coarseCorrection (R : Matrix (Fin m) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - coarseProjector R A P

/-- The coarse-grid correction operator is $T_h^H = I - Q_h$. -/
theorem coarseCorrection_def (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    coarseCorrection R A P = 1 - coarseProjector R A P := rfl

/-- **Equation (13.43)** of [saad2003iterative] and Algorithm 13.2. The **two-grid iteration
operator** with $\nu_1$ pre-smoothing and $\nu_2$ post-smoothing steps around one coarse-grid
correction is
$$M_H^h = S^{\nu_2} \left(I - I_H^h A_H^{-1} I_h^H A_h\right) S^{\nu_1},$$
where $S$ is the error propagation operator of the smoother.

**Source location.** The source numbers only the middle coarse-grid correction as (13.43). The
full composition with pre- and post-smoothing is the unnumbered display immediately before it.

**Correction.** Defines full two-grid error operator for arbitrary arrays and smoother; (13.43)
itself is only the middle correction.
-/
noncomputable def equation_13_43 (R : Matrix (Fin m) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (ν₁ ν₂ : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  S ^ ν₂ * coarseCorrection R A P * S ^ ν₁

variable {A : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin m) (Fin n) ℝ}
  {P : Matrix (Fin n) (Fin m) ℝ}

/-- **Equation (13.43)** of [saad2003iterative], the coarse-grid projector. If $(A, R, P)$ is a
coarsening, then $Q_h = P A_H^{-1} R A$ is the $A$-orthogonal projector onto the range of $P$:
its linear map is `Multigrid.coarseProjection` of $A$ and $P$.

The factor $c$ in $R = c \, P^T$ multiplies both sides of the coarse equation and so cancels.

**Reading.** Energy projector onto range P using explicit coarsening assumptions.
-/
theorem toEuclideanLin_coarseProjector (h : IsCoarsening A R P) :
    toEuclideanLin (coarseProjector R A P)
      = Multigrid.coarseProjection (toEuclideanLin A) h.isSymmetricCoercive
          (toEuclideanLin P) := by
  have hunit := h.coarseOperator_mul_inv
  obtain ⟨c, hc, rfl⟩ := h.exists_smul
  refine LinearMap.ext fun x => ?_
  have hgal : ∀ z : EuclideanSpace ℝ (Fin m),
      c • Multigrid.galerkinCoarse (toEuclideanLin A) (toEuclideanLin P) z
        = (coarseOperator (c • Pᵀ) A P) ⬝ z := fun z => by
    rw [coarseOperator_eq_galerkinCoarse]
    rfl
  have hadj : ∀ w : EuclideanSpace ℝ (Fin n),
      c • LinearMap.adjoint (toEuclideanLin P) w = (c • Pᵀ) ⬝ w := fun w => by
    rw [adjoint_toEuclideanLin, map_smul]
    rfl
  have hy : c • Multigrid.galerkinCoarse (toEuclideanLin A) (toEuclideanLin P)
        ((coarseOperator (c • Pᵀ) A P)⁻¹ ⬝ ((c • Pᵀ) ⬝ (A ⬝ x)))
      = c • LinearMap.adjoint (toEuclideanLin P) (toEuclideanLin A x) := by
    rw [hgal, hadj, ← mul_act, hunit, one_act]
  rw [coarseProjection_apply_eq_of_smul (toEuclideanLin A) h.isSymmetricCoercive
    (toEuclideanLin P) (ne_of_gt hc) hy, coarseProjector, coarsePreconditioner]
  simp only [mul_act]

/-- **Equation (13.43)** of [saad2003iterative], the coarse-grid correction. If $(A, R, P)$ is a
coarsening, then the linear map of $T_h^H = I - Q_h$ is the backbone coarse-grid correction
`Multigrid.coarseCorrection` of $A$ and $P$.

**Correction.** Identifies correction under explicit coarsening assumptions.
-/
theorem toEuclideanLin_coarseCorrection (h : IsCoarsening A R P) :
    toEuclideanLin (coarseCorrection R A P)
      = Multigrid.coarseCorrection (toEuclideanLin A) h.isSymmetricCoercive
          (toEuclideanLin P) := by
  have hdef : Multigrid.coarseCorrection (toEuclideanLin A) h.isSymmetricCoercive
      (toEuclideanLin P)
      = 1 - Multigrid.coarseProjection (toEuclideanLin A) h.isSymmetricCoercive
          (toEuclideanLin P) := rfl
  rw [coarseCorrection_def, hdef, map_sub, toEuclideanLin_coarseProjector h,
    Matrix.toEuclideanLin_one]
  rfl

/-- **Equation (13.43)** of [saad2003iterative], the two-grid operator. If $(A, R, P)$ is a
coarsening, then for every matrix $S$ and all $\nu_1, \nu_2$ the linear map of
$M_H^h = S^{\nu_2} T_h^H S^{\nu_1}$ is the backbone two-grid operator
`Multigrid.twoGridOperator`.

So the convergence theory of Section 13.5 applies to it.

**Reading.** Identifies full error operator with backbone under explicit coarsening assumptions.
-/
theorem equation_13_43_eq (h : IsCoarsening A R P) (S : Matrix (Fin n) (Fin n) ℝ) (ν₁ ν₂ : ℕ) :
    toEuclideanLin (equation_13_43 R A P S ν₁ ν₂)
      = Multigrid.twoGridOperator (toEuclideanLin A) h.isSymmetricCoercive (toEuclideanLin P)
          (toEuclideanLin S) ν₁ ν₂ := by
  have hdef : Multigrid.twoGridOperator (toEuclideanLin A) h.isSymmetricCoercive
      (toEuclideanLin P) (toEuclideanLin S) ν₁ ν₂
      = (toEuclideanLin S ^ ν₂) ∘ₗ Multigrid.coarseCorrection (toEuclideanLin A)
          h.isSymmetricCoercive (toEuclideanLin P) ∘ₗ (toEuclideanLin S ^ ν₁) := rfl
  rw [equation_13_43, hdef, Matrix.toEuclideanLin_mul, Matrix.toEuclideanLin_mul,
    toEuclideanLin_coarseCorrection h, Matrix.toEuclideanLin_pow, Matrix.toEuclideanLin_pow,
    LinearMap.comp_assoc]

/-- **Lemma 13.1** of [saad2003iterative], the projector property. If $(A, R, P)$ is a coarsening,
with the coarse matrix defined by (13.39), then the coarse-grid correction operator is a
projector:
$$(T_h^H)^2 = T_h^H.$$

**Reading.** Idempotence with explicit positive-scaled-transpose and injectivity hypotheses.
-/
theorem lemma_13_1 (h : IsCoarsening A R P) :
    coarseCorrection R A P * coarseCorrection R A P = coarseCorrection R A P := by
  have hQ : coarseProjector R A P * coarseProjector R A P = coarseProjector R A P := by
    refine (Matrix.toEuclideanLin (𝕜 := ℝ)).injective ?_
    rw [Matrix.toEuclideanLin_mul, toEuclideanLin_coarseProjector h]
    refine LinearMap.ext fun x => ?_
    exact Multigrid.coarseProjection_apply_of_mem _ _ _
      (Multigrid.coarseProjection_apply_mem _ h.isSymmetricCoercive _ x)
  have hexpand : ∀ Q : Matrix (Fin n) (Fin n) ℝ,
      (1 - Q) * (1 - Q) = 1 - Q - (Q - Q * Q) := fun Q => by noncomm_ring
  rw [coarseCorrection_def, hexpand, hQ, sub_self, sub_zero]

/-- **Lemma 13.1** of [saad2003iterative], orthogonality. If $(A, R, P)$ is a coarsening, then the
coarse-grid correction operator is self-adjoint in the $A$-inner product: for all
$x, y \in \mathbb{R}^n$,
$$(A T_h^H x, y) = (A x, T_h^H y).$$

Together with `SaadSparse.Chapter13.lemma_13_1` this says that $T_h^H$ is an $A$-orthogonal
projector. The $A$-inner product is `energyInner`.

**Reading.** Self-adjointness under the coarsening hypotheses needed to justify source proof.
-/
theorem lemma_13_1_energyInner (h : IsCoarsening A R P) (x y : EuclideanSpace ℝ (Fin n)) :
    energyInner (toEuclideanLin A) (coarseCorrection R A P ⬝ x) y
      = energyInner (toEuclideanLin A) x (coarseCorrection R A P ⬝ y) := by
  have hval : ∀ z : EuclideanSpace ℝ (Fin n),
      WithEnergy.equiv (toEuclideanLin A) h.isSymmetricCoercive (coarseCorrection R A P ⬝ z)
        = (WithEnergy.submoduleMap (toEuclideanLin A) h.isSymmetricCoercive
            (LinearMap.range (toEuclideanLin P)))ᗮ.starProjection
              (WithEnergy.equiv (toEuclideanLin A) h.isSymmetricCoercive z) := fun z => by
    rw [toEuclideanLin_coarseCorrection h, Multigrid.coarseCorrection_apply, map_sub,
      Multigrid.equiv_coarseProjection, Submodule.starProjection_orthogonal_val]
  rw [← WithEnergy.inner_equiv (toEuclideanLin A) h.isSymmetricCoercive,
    ← WithEnergy.inner_equiv (toEuclideanLin A) h.isSymmetricCoercive, hval, hval,
    Submodule.inner_starProjection_left_eq_right]

/-- **Lemma 13.1** of [saad2003iterative], the range. If $(A, R, P)$ is a coarsening, then the range
of the coarse-grid correction operator is $A$-orthogonal to the range of the prolongation: for
all $x \in \mathbb{R}^n$ and $u \in \mathbb{R}^m$,
$$(A T_h^H x, P u) = 0.$$
So the error left by a coarse-grid correction has no component in the coarse space.

**Correction.** The third clause of the lemma in the book names the restriction $I_h^H$ where
its own proof gives the prolongation $I_H^h$. -/
theorem lemma_13_1_energyInner_eq_zero (h : IsCoarsening A R P) (x : EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin m)) :
    energyInner (toEuclideanLin A) (coarseCorrection R A P ⬝ x) (P ⬝ u) = 0 := by
  have hmem : (coarseCorrection R A P ⬝ x)
      ∈ LinearMap.range (Multigrid.coarseCorrection (toEuclideanLin A) h.isSymmetricCoercive
          (toEuclideanLin P)) := by
    rw [← toEuclideanLin_coarseCorrection h]
    exact ⟨x, rfl⟩
  rw [Multigrid.range_coarseCorrection, LinearMap.mem_ker, LinearMap.comp_apply] at hmem
  rw [energyInner, ← LinearMap.adjoint_inner_left (toEuclideanLin P) u
    (toEuclideanLin A (coarseCorrection R A P ⬝ x)), hmem, inner_zero_left]

/-! ### Section 13.4.3: The V-cycle, the W-cycle and full multigrid -/

/-- **Section 13.4.3** of [saad2003iterative], a **multigrid hierarchy**. A hierarchy consists of,
for every level $l$, a grid of $n_l$ unknowns with a matrix $A_{h_l}$ and the approximate
inverse $B_{h_l}$ of its smoother (13.40), a prolongation and a restriction between the levels
$l$ and $l + 1$, and the interpolation $\hat I$ from which full multigrid starts each level. The
book allows $\hat I$ to be of higher order than the prolongation of the cycle.

Level $0$ is the coarsest, where the problem is solved exactly, and level $l + 1$ is finer than
level $l$: the $p + 1$ levels $h_0 > h_1 > \dots > h_p$ of the book are the levels
$0, \dots, p$. A hierarchy is indexed by all of $\mathbb{N}$, not by `Fin (p + 1)`, so that no
bound has to be carried through the recursions; a cycle on level $l$ uses only the levels
$0, \dots, l$.

**Reading.** Uses levels indexed by all naturals with separate full-multigrid interpolation;
shape-compatible data without enforced grid relationships.
-/
structure Hierarchy where
  /-- The number $n_l$ of unknowns of level $l$. -/
  size : ℕ → ℕ
  /-- The matrix $A_{h_l}$ of level $l$. -/
  matrix : ∀ l, Matrix (Fin (size l)) (Fin (size l)) ℝ
  /-- The approximate inverse $B_{h_l}$ that defines the smoother (13.40) of level $l$. -/
  approxInverse : ∀ l, Matrix (Fin (size l)) (Fin (size l)) ℝ
  /-- The prolongation $I_{h_l}^{h_{l+1}}$ from level $l$ to the finer level $l + 1$. -/
  prolongation : ∀ l, Matrix (Fin (size (l + 1))) (Fin (size l)) ℝ
  /-- The restriction $I_{h_{l+1}}^{h_l}$ from level $l + 1$ to the coarser level $l$. -/
  restriction : ∀ l, Matrix (Fin (size l)) (Fin (size (l + 1))) ℝ
  /-- The interpolation $\hat I_{h_l}^{h_{l+1}}$ of Algorithm 13.5, from level $l$ to level $l + 1$.
  -/
  fmgInterpolation : ∀ l, Matrix (Fin (size (l + 1))) (Fin (size l)) ℝ

namespace Hierarchy

/-- The vectors of level $l$ of a hierarchy, the Euclidean space $\mathbb{R}^{n_l}$. -/
abbrev Vec (H : Hierarchy) (l : ℕ) : Type := EuclideanSpace ℝ (Fin (H.size l))

/-- One $\gamma$-cycle on level $l + 1$, given a solver $\mathrm{mg}$ for level $l$: $\nu_1$
pre-smoothing steps, a coarse-grid correction obtained by $\gamma$ applications of $\mathrm{mg}$
from $0$ to the restricted residual, and $\nu_2$ post-smoothing steps. This is the body of
Algorithm 13.4.

**Reading.** Uses arbitrary coarse solver parameter; repeats even a level-zero solve γ times and
permits γ=0.
-/
noncomputable def cycleStep (H : Hierarchy) (ν₁ ν₂ γ l : ℕ) (mg : H.Vec l → H.Vec l → H.Vec l)
    (u f : H.Vec (l + 1)) : H.Vec (l + 1) :=
  let S := smootherStep (H.matrix (l + 1)) (H.approxInverse (l + 1)) f
  let u₁ := S^[ν₁] u
  let d := coarseRhs (H.restriction l) (f - (H.matrix (l + 1) ⬝ u₁))
  S^[ν₂] (u₁ + (H.prolongation l ⬝ (fun v => mg v d)^[γ] 0))

/-- **Algorithm 13.4** of [saad2003iterative], the **$\gamma$-cycle**
$\mathrm{MG}(A_h, u, f, \nu_1, \nu_2, \gamma)$. On the coarsest level the system is solved
exactly, $u = A_{h_0}^{-1} f$. On every finer level, $\nu_1$ smoothing steps are followed by
$\gamma$ recursive cycles on the restricted residual, starting from $0$, and then by $\nu_2$
smoothing steps.

The book proves nothing about the cycles themselves, because their error propagation operators
are composites of the two-grid operators of (13.43). So this is a definition only. What Section
13.4 proves about the cycles is the cost estimate `SaadSparse.Chapter13.equation_13_44` and,
through Algorithm 13.5, `SaadSparse.Chapter13.theorem_13_2`. The inverse on level $0$ is the
Lean matrix inverse, which is $0$ for a singular matrix.

**Reading.** Moves direct solve into a coarsest-level base case with total inverse; combines with
γ=0 extension.
-/
noncomputable def cycle (H : Hierarchy) (ν₁ ν₂ γ : ℕ) : ∀ l : ℕ, H.Vec l → H.Vec l → H.Vec l
  | 0 => fun _ f => ((H.matrix 0)⁻¹ ⬝ f)
  | l + 1 => cycleStep H ν₁ ν₂ γ l (cycle H ν₁ ν₂ γ l)

/-- On the coarsest level a cycle solves the system exactly: it returns $A_{h_0}^{-1} f$.

**Reading.** The equation uses total matrix inverse, no invertibility proof at definition.
-/
@[simp]
theorem cycle_zero (H : Hierarchy) (ν₁ ν₂ γ : ℕ) (u f : H.Vec 0) :
    H.cycle ν₁ ν₂ γ 0 u f = ((H.matrix 0)⁻¹ ⬝ f) := rfl

/-- On every finer level a cycle is one cycle step around $\gamma$ cycles of the level below.

**Reading.** Passes to γ coarse cycles uniformly, including the exact base case.
-/
theorem cycle_succ (H : Hierarchy) (ν₁ ν₂ γ l : ℕ) :
    H.cycle ν₁ ν₂ γ (l + 1) = cycleStep H ν₁ ν₂ γ l (H.cycle ν₁ ν₂ γ l) := rfl

/-- **Algorithm 13.3** of [saad2003iterative], the **V-cycle**: the $\gamma$-cycle with
$\gamma = 1$, one recursive call per level. -/
noncomputable def vcycle (H : Hierarchy) (ν₁ ν₂ : ℕ) : ∀ l : ℕ, H.Vec l → H.Vec l → H.Vec l :=
  H.cycle ν₁ ν₂ 1

/-- **Section 13.4.3** of [saad2003iterative], the **W-cycle**: the $\gamma$-cycle with
$\gamma = 2$, two recursive calls per level. -/
noncomputable def wcycle (H : Hierarchy) (ν₁ ν₂ : ℕ) : ∀ l : ℕ, H.Vec l → H.Vec l → H.Vec l :=
  H.cycle ν₁ ν₂ 2

/-- **Algorithm 13.5** of [saad2003iterative], **full multigrid**. The method sweeps once from the
coarsest level upwards. It solves the coarsest problem exactly,
$\tilde u^{h_0} = A_{h_0}^{-1} f^{h_0}$. On each finer level $l + 1$ it takes the interpolant
$\hat I \tilde u^{h_l}$ of the approximation of level $l$ as the initial guess for $\mu$
$\gamma$-cycles with the right-hand side $f^{h_{l+1}}$.

The right-hand sides $f^{h_l}$ are the discretizations of the problem on each level, not
restrictions of one another.

**Reading.** Recursion on indexed levels with total base inverse; uses separate hatted interpolation
and μ fine cycles.
-/
noncomputable def fullMultigrid (H : Hierarchy) (ν₁ ν₂ γ μ : ℕ) (f : ∀ l, H.Vec l) :
    ∀ l : ℕ, H.Vec l
  | 0 => ((H.matrix 0)⁻¹ ⬝ f 0)
  | l + 1 => (fun u => H.cycle ν₁ ν₂ γ (l + 1) u (f (l + 1)))^[μ]
      (H.fmgInterpolation l ⬝ fullMultigrid H ν₁ ν₂ γ μ f l)

/-- Full multigrid solves the coarsest system exactly: it returns $A_{h_0}^{-1} f^{h_0}$ on level
$0$.

**Reading.** Uses total inverse at coarsest level.
-/
@[simp]
theorem fullMultigrid_zero (H : Hierarchy) (ν₁ ν₂ γ μ : ℕ) (f : ∀ l, H.Vec l) :
    H.fullMultigrid ν₁ ν₂ γ μ f 0 = ((H.matrix 0)⁻¹ ⬝ f 0) := rfl

/-- On every finer level $l + 1$, full multigrid applies $\mu$ cycles to the interpolant of the
approximation of level $l$. -/
theorem fullMultigrid_succ (H : Hierarchy) (ν₁ ν₂ γ μ : ℕ) (f : ∀ l, H.Vec l) (l : ℕ) :
    H.fullMultigrid ν₁ ν₂ γ μ f (l + 1)
      = (fun u => H.cycle ν₁ ν₂ γ (l + 1) u (f (l + 1)))^[μ]
          (H.fmgInterpolation l ⬝ H.fullMultigrid ν₁ ν₂ γ μ f l) := rfl

end Hierarchy

/-! ### Section 13.4.3: The cost of a cycle, (13.44) -/

/-- **Equation (13.44)** of [saad2003iterative], the cost of one cycle. Let $\eta \ge 0$,
$\gamma \ge 0$ and $d \in \mathbb{N}$ with $\gamma < 2^d$. Let $n_l > 0$ be the number of
unknowns of level $l$, with $n_{l+1} = 2^d n_l$, as after a coarsening by two in each of $d$
dimensions. Let $C_l$ bound the cost of one $\gamma$-cycle on level $l$, with $C_0 \le \eta n_0$
and
$$C_{l+1} \le \eta n_{l+1} + \gamma C_l:$$
a visit to a level costs $\eta$ per unknown, and the level below is visited $\gamma$ times. Then
for every $l$
$$C_l \le \frac{\eta n_l}{1 - \gamma 2^{-d}}.$$

**Correction.** The book prints the constant $7/3$ for the two-dimensional V-cycle. With
$\gamma = 1$ and $d = 2$ the geometric series $\sum_k 4^{-k}$ of the recurrence is $4/3$.

So the cost is proportional to the number of unknowns of the finest level, which is the $O(n)$
of the book and its condition "$\gamma < 2$ in one dimension and $\gamma < 4$ in two". A V-cycle
($\gamma = 1$) satisfies the condition in every dimension, with the constant $2$ in one
dimension and $4/3$ in two. A W-cycle ($\gamma = 2$) satisfies it for $d \ge 2$, with the
constant $2$ in two dimensions. In one dimension the W-cycle is the borderline case
$\gamma = 2^d$, where the bound fails and the cost grows like $\eta n_l \log_2 n_l$, the
$O(n \log_2 n)$ of the book; this case is not stated here. The proof is the geometric series
$\sum_k (\gamma 2^{-d})^k$. -/
theorem equation_13_44 {C nsize : ℕ → ℝ} {η γ : ℝ} {d : ℕ} (hη : 0 ≤ η) (hγ : 0 ≤ γ)
    (hγd : γ < 2 ^ d) (hn : ∀ l, nsize (l + 1) = 2 ^ d * nsize l) (hnpos : ∀ l, 0 < nsize l)
    (hC₀ : C 0 ≤ η * nsize 0) (hrec : ∀ l, C (l + 1) ≤ η * nsize (l + 1) + γ * C l) (l : ℕ) :
    C l ≤ η * nsize l / (1 - γ / 2 ^ d) := by
  have hs : (0 : ℝ) < 2 ^ d := by positivity
  have ht : γ / 2 ^ d < 1 := (div_lt_one hs).2 hγd
  have ht0 : (0 : ℝ) ≤ γ / 2 ^ d := div_nonneg hγ hs.le
  have hden : (0 : ℝ) < 1 - γ / 2 ^ d := by linarith
  induction l with
  | zero =>
    have h0 : 0 ≤ η * nsize 0 := mul_nonneg hη (hnpos 0).le
    rw [le_div_iff₀ hden]
    nlinarith
  | succ l ih =>
    have hnl : nsize l = nsize (l + 1) / 2 ^ d := by
      rw [hn l]
      field_simp
    have hne : (2 : ℝ) ^ d - γ ≠ 0 := ne_of_gt (sub_pos.2 hγd)
    calc C (l + 1) ≤ η * nsize (l + 1) + γ * C l := hrec l
      _ ≤ η * nsize (l + 1) + γ * (η * nsize l / (1 - γ / 2 ^ d)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hγ)
      _ = η * nsize (l + 1) / (1 - γ / 2 ^ d) := by
          rw [hnl]
          field_simp
          ring

/-! ### Section 13.4.4: Full multigrid, Theorem 13.2 -/

/-- If a map $F$ satisfies $\|x - F(v)\| \le \xi \|x - v\|$ for all $v$, with $\xi \ge 0$, then
$\|x - F^\mu(v)\| \le \xi^\mu \|x - v\|$. -/
private theorem norm_sub_iterate_le {X : Type*} [NormedAddCommGroup X] {F : X → X} {x : X} {ξ : ℝ}
    (hξ : 0 ≤ ξ) (hF : ∀ v, ‖x - F v‖ ≤ ξ * ‖x - v‖) (μ : ℕ) (v : X) :
    ‖x - F^[μ] v‖ ≤ ξ ^ μ * ‖x - v‖ := by
  induction μ generalizing v with
  | zero => simp
  | succ μ ih =>
    calc ‖x - F^[μ + 1] v‖ = ‖x - F^[μ] (F v)‖ := by rw [Function.iterate_succ_apply]
      _ ≤ ξ ^ μ * ‖x - F v‖ := ih (F v)
      _ ≤ ξ ^ μ * (ξ * ‖x - v‖) := mul_le_mul_of_nonneg_left (hF v) (pow_nonneg hξ μ)
      _ = ξ ^ (μ + 1) * ‖x - v‖ := by ring

/-- **Theorem 13.2** of [saad2003iterative], the full multigrid error bound. Let a multigrid
hierarchy have mesh sizes $h_l > 0$ with $h_{l+1} = h_l/2$. Let $u^{h_l}$ be vectors of the
levels, let $f^{h_l}$ be the right-hand sides, and let $\tilde u^{h_l}$ be the full multigrid
approximation of Algorithm 13.5 with $\mu$ $\gamma$-cycles per level. Let $c_1 \ge 0$,
$\xi \ge 0$, $c_2$ and $\kappa$ be real numbers. Assume that
* the coarsest system is solved exactly: $A_{h_0}$ is nonsingular and
  $A_{h_0} u^{h_0} = f^{h_0}$;
* (13.49) the interpolation is accurate to the discretization order: $\|u^{h_{l+1}} - \hat I
  u^{h_l}\| \le c_1 h_{l+1}^\kappa$ for all $l$;
* (13.50) one cycle contracts the error by $\xi$: $\|u^{h_{l+1}} - \mathrm{MG}(v)\| \le \xi
  \|u^{h_{l+1}} - v\|$ for all $l$ and all $v$, where $\mathrm{MG}(v)$ is one cycle from $v$
  with the right-hand side $f^{h_{l+1}}$;
* (13.51) the interpolations are bounded: $\|\hat I\| \le c_2 2^{-\kappa}$ in the operator norm;
* (13.52) $c_2 \xi^\mu < 1$.

Then on every level $l$
$$\|u^{h_l} - \tilde u^{h_l}\| \le c_3 c_1 h_l^\kappa, \qquad c_3 = \frac{\xi^\mu}{1 -
  c_2\xi^\mu}.$$

The book states (13.50) as $\|M_h\| \le \xi < 1$; the form here follows from it once the exact
solution is recognized as a fixed point of the cycle, as in (13.55), and it is the only form
that the proof uses. The assumption (13.48) of the book, that the discrete solution is within
$c h^\kappa$ of the sampled continuous solution, motivates (13.49) but is not used in the proof,
so it does not appear. For $l \ge 1$ the vectors $u^{h_l}$ enter only through (13.49) and
(13.50). The proof specializes `Multigrid.norm_sub_fullMultigrid_le`.

**Reading.** The source permits an arbitrary level norm and bounds the linear iteration
operator by $\xi<1$. The theorem uses Euclidean norms and assumes the bound directly for the
implemented cycle's error relative to the selected solution. It requires $\xi\ge0$ and the
stated product condition without a separate $\xi<1$ bound. -/
theorem theorem_13_2 (H : Hierarchy) {ν₁ ν₂ γ μ : ℕ} {f u : ∀ l, H.Vec l} {hmesh : ℕ → ℝ}
    {c₁ c₂ ξ κ : ℝ} (hh : ∀ l, hmesh (l + 1) = hmesh l / 2) (hhpos : ∀ l, 0 < hmesh l)
    (hunit : IsUnit (H.matrix 0)) (hsolve : (H.matrix 0 ⬝ u 0) = f 0) (hc₁ : 0 ≤ c₁) (hξ : 0 ≤ ξ)
    (hlt : c₂ * ξ ^ μ < 1)
    (h1349 : ∀ l, ‖u (l + 1) - (H.fmgInterpolation l ⬝ u l)‖ ≤ c₁ * hmesh (l + 1) ^ κ)
    (h1350 : ∀ (l : ℕ) (v : H.Vec (l + 1)),
      ‖u (l + 1) - H.cycle ν₁ ν₂ γ (l + 1) v (f (l + 1))‖ ≤ ξ * ‖u (l + 1) - v‖)
    (h1351 : ∀ l, ‖LinearMap.toContinuousLinearMap (toEuclideanLin (H.fmgInterpolation l))‖
      ≤ c₂ * (2 : ℝ) ^ (-κ)) (l : ℕ) :
    ‖u l - H.fullMultigrid ν₁ ν₂ γ μ f l‖ ≤ ξ ^ μ / (1 - c₂ * ξ ^ μ) * c₁ * hmesh l ^ κ := by
  have hexact : H.fullMultigrid ν₁ ν₂ γ μ f 0 = u 0 := by
    rw [Hierarchy.fullMultigrid_zero, ← hsolve, ← mul_act,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit), one_act]
  refine Multigrid.norm_sub_fullMultigrid_le
    (utilde := fun l => H.fullMultigrid ν₁ ν₂ γ μ f l)
    (interp := fun l => LinearMap.toContinuousLinearMap (toEuclideanLin (H.fmgInterpolation l)))
    hh hhpos hexact hc₁ hξ hlt h1349 (fun l => ?_) h1351 l
  rw [Hierarchy.fullMultigrid_succ]
  exact norm_sub_iterate_le hξ (h1350 l) μ _

/-! ### Example 13.6: The discretization error of the one-dimensional model problem -/

section DiscretizationError

open Real

/-- **Example 13.6** of [saad2003iterative], the grid function of a continuous function $u$. It is
the vector of the values $u(x_i)$ at the interior grid points $x_i = ih$, $i = 1, \dots, n$. The
book writes it $u$ again.

The $0$-based index `i : Fin n` stands for the book's $i + 1$.

**Reading.** Samples interior grid at arbitrary real h rather than fixed h=1/(n+1).
-/
noncomputable def gridSample (n : ℕ) (h : ℝ) (u : ℝ → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i : Fin n => u ((((i : ℕ) : ℝ) + 1) * h)

/-- The component $i$ of the grid function of $u$ is the value of $u$ at the interior grid point
$x_i$. -/
theorem gridSample_apply (h : ℝ) (u : ℝ → ℝ) (i : Fin n) :
    WithLp.ofLp (gridSample n h u) i = u ((((i : ℕ) : ℝ) + 1) * h) := rfl

/-- **Example 13.6** of [saad2003iterative]. The **discrete $L^2$ norm** on the grid with mesh size
$h$ is
$$\|v\|_h = h^{1/2} \|v\|_2.$$

**Reading.** Definition is total for h outside positive mesh sizes.
-/
noncomputable def discreteL2Norm (h : ℝ) (v : EuclideanSpace ℝ (Fin n)) : ℝ := √h * ‖v‖

/-- **Example 13.6** of [saad2003iterative], the boundary values. Let $h = 1/(n+1)$ and let
$u(0) = u(1) = 0$. Then the extension of the grid function of $u$ by zero boundary values equals
$u(kh)$ at every grid index $k = 0, 1, \dots, n + 1$, boundary points included.

So the rows of the model matrix are centred second differences of $u$, with no special case at
the two ends. The extension is `SaadSparse.Chapter02.dirichletExt`. -/
theorem dirichletExt_gridSample {h : ℝ} {u : ℝ → ℝ} (hh : h = 1 / ((n : ℝ) + 1))
    (hu0 : u 0 = 0) (hu1 : u 1 = 0) {k : ℕ} (hk : k ≤ n + 1) :
    Chapter02.dirichletExt (WithLp.ofLp (gridSample n h u)) k = u ((k : ℝ) * h) := by
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  match k with
  | 0 => rw [Chapter02.dirichletExt_zero]; simpa using hu0.symm
  | (m + 1) =>
    by_cases hm : m < n
    · rw [Chapter02.dirichletExt_succ, dite_eq_left hm, gridSample_apply]
      push_cast
      ring_nf
    · have hmn : m = n := by omega
      subst hmn
      rw [Chapter02.dirichletExt_of_gt _ (by omega)]
      have hx : ((m : ℕ) + 1 : ℝ) * h = 1 := by rw [hh]; field_simp
      push_cast
      rw [hx, hu1]

/-- **Example 13.6** of [saad2003iterative], the truncation error. Let $h = 1/(n+1)$, let $u$ be of
class $C^4$ with $u(0) = u(1) = 0$, let $f = -u''$, and let $|u^{(4)}(x)| \le K$ for
$x \in [0, 1]$. Let $A_h = h^{-2}\operatorname{tridiag}(-1, 2, -1)$. Then every component of the
truncation error satisfies
$$|(f^h - A_h u)_i| \le \frac{K h^2}{12}.$$

The proof uses (2.12) (`SaadSparse.Chapter02.equation_2_12`), which writes the component as
$h^2/12$ times a value of $u^{(4)}$ in $(x_i - h, x_i + h)$. The matrix $A_h$ is
`SaadSparse.Chapter02.laplacian1D n h`.

**Reading.** Componentwise absolute bound with C⁴ on R and bound on absolute fourth derivatives,
without exact ξ witness.
-/
theorem example_13_6_truncation {h : ℝ} (hh : h = 1 / ((n : ℝ) + 1)) {u f : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u) (hu0 : u 0 = 0) (hu1 : u 1 = 0)
    (hf : ∀ x, f x = -iteratedDeriv 2 u x) {K : ℝ}
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 4 u x| ≤ K) (i : Fin n) :
    |WithLp.ofLp (gridSample n h f - (Chapter02.laplacian1D n h ⬝ gridSample n h u)) i|
      ≤ K * h ^ 2 / 12 := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hh0 : 0 < h := by rw [hh]; positivity
  have hi : ((i : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt i.isLt
  obtain ⟨ξ, hξ, hEq⟩ := Chapter02.equation_2_12 hu ((((i : ℕ) : ℝ) + 1) * h) hh0
  have hAu : WithLp.ofLp (Chapter02.laplacian1D n h ⬝ gridSample n h u) i
      = (-u ((((i : ℕ) : ℝ) + 1) * h - h) + 2 * u ((((i : ℕ) : ℝ) + 1) * h)
          - u ((((i : ℕ) : ℝ) + 1) * h + h)) / h ^ 2 := by
    rw [Matrix.ofLp_toEuclideanLin, Chapter02.laplacian1D_mulVec_apply,
      dirichletExt_gridSample hh hu0 hu1 (by omega : (i : ℕ) ≤ n + 1),
      dirichletExt_gridSample hh hu0 hu1 (by omega : (i : ℕ) + 1 ≤ n + 1),
      dirichletExt_gridSample hh hu0 hu1 (by omega : (i : ℕ) + 2 ≤ n + 1)]
    push_cast
    ring_nf
  have hval : WithLp.ofLp (gridSample n h f - (Chapter02.laplacian1D n h ⬝ gridSample n h u)) i
      = h ^ 2 / 12 * iteratedDeriv 4 u ξ := by
    rw [WithLp.ofLp_sub, Pi.sub_apply, gridSample_apply, hAu, hf]
    have h2 : (u ((((i : ℕ) : ℝ) + 1) * h + h) - 2 * u ((((i : ℕ) : ℝ) + 1) * h)
        + u ((((i : ℕ) : ℝ) + 1) * h - h)) / h ^ 2
          = iteratedDeriv 2 u ((((i : ℕ) : ℝ) + 1) * h) + h ^ 2 / 12 * iteratedDeriv 4 u ξ := hEq
    field_simp at h2 ⊢
    linarith
  have hmem : ξ ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨hl, hr⟩ := hξ
    constructor
    · have : (0 : ℝ) ≤ (((i : ℕ) : ℝ) + 1) * h - h := by
        have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) * h := by positivity
        nlinarith
      linarith
    · have hone : ((n : ℝ) + 1) * h = 1 := by rw [hh]; field_simp
      have hub : (((i : ℕ) : ℝ) + 1) * h + h ≤ 1 := by
        rw [← hone]
        nlinarith [mul_nonneg (sub_nonneg.2 hi) hh0.le]
      linarith
  rw [hval, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ 2 / 12)]
  have := hK ξ hmem
  nlinarith [abs_nonneg (iteratedDeriv 4 u ξ), sq_nonneg h]

/-- **Example 13.6** of [saad2003iterative], the discretization error. Let $h = 1/(n+1)$, let $u$ be
of class $C^4$ with $u(0) = u(1) = 0$, let $f = -u''$, and let $|u^{(4)}(x)| \le K$ for
$x \in [0, 1]$. Let $u^h$ solve $A_h u^h = f^h$ with
$A_h = h^{-2}\operatorname{tridiag}(-1, 2, -1)$. Then, with $u$ sampled on the grid,
$$\|u^h - u\|_h \le \frac{K h^4}{48 \sin^2(\pi h/2)}.$$
This is (13.48) with $\kappa = 2$.

The chain of the book is $\|u^h - u\|_h = \|A_h^{-1}(f^h - A_h u)\|_h \le \|A_h^{-1}\|_h \|f^h -
A_h u\|_h$, with $\|A_h^{-1}\|_h = 1/\lambda_{\min}(A_h)$ and
$\lambda_{\min}(A_h) = 4\sin^2(\pi h/2)/h^2$ from (13.7). The proof uses the same bound in the
form $\lambda_{\min}\|e\| \le \|A_h e\|$ (`LinearMap.IsCoerciveWith.norm_le_norm_apply`) for the
error $e$, with no inverse. The factor $h^{1/2}$ of the discrete $L^2$ norm turns the
componentwise bound $Kh^2/12$ into a bound on the whole vector without a factor $\sqrt n$. -/
theorem example_13_6 {h : ℝ} (hh : h = 1 / ((n : ℝ) + 1)) {u f : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u) (hu0 : u 0 = 0) (hu1 : u 1 = 0)
    (hf : ∀ x, f x = -iteratedDeriv 2 u x) {K : ℝ}
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 4 u x| ≤ K)
    {uh : EuclideanSpace ℝ (Fin n)}
    (huh : (Chapter02.laplacian1D n h ⬝ uh) = gridSample n h f) :
    discreteL2Norm h (uh - gridSample n h u) ≤ K * h ^ 4 / (48 * sin (π * h / 2) ^ 2) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hh0 : 0 < h := by rw [hh]; positivity
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_one hn1]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hK0 : (0 : ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0 ⟨le_refl 0, zero_le_one⟩)
  have hang : π / (2 * ((n : ℝ) + 1)) = π * h / 2 := by
    rw [hh]; field_simp
  have hsin : 0 < sin (π * h / 2) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    nlinarith [Real.pi_pos]
  set M : ℝ := 4 * sin (π * h / 2) ^ 2 / h ^ 2 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  set e : EuclideanSpace ℝ (Fin n) := uh - gridSample n h u with he
  set r : EuclideanSpace ℝ (Fin n) :=
    gridSample n h f - (Chapter02.laplacian1D n h ⬝ gridSample n h u) with hr
  have hAe : (Chapter02.laplacian1D n h ⬝ e) = r := by rw [he, hr, map_sub, huh]
  have hbdd := Chapter02.laplacian1D_isSymmetricBoundedBy n hh0.ne'
  rw [hang] at hbdd
  have hcoer : M * ‖e‖ ≤ ‖r‖ := by
    have := LinearMap.IsCoerciveWith.norm_le_norm_apply hbdd.isCoerciveWith e
    rwa [hAe] at this
  have hnormr : √h * ‖r‖ ≤ K * h ^ 2 / 12 := by
    have hpt : ∀ i : Fin n, ‖WithLp.ofLp r i‖ ^ 2 ≤ (K * h ^ 2 / 12) ^ 2 := by
      intro i
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (example_13_6_truncation hh hu hu0 hu1 hf hK i) 2
    have hsum : ‖r‖ ^ 2 ≤ (n : ℝ) * (K * h ^ 2 / 12) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖WithLp.ofLp r i‖ ^ 2 ≤ ∑ _i : Fin n, (K * h ^ 2 / 12) ^ 2 :=
            Finset.sum_le_sum fun i _ => hpt i
        _ = (n : ℝ) * (K * h ^ 2 / 12) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hhn : h * (n : ℝ) ≤ 1 := by
      rw [hh, div_mul_eq_mul_div, one_mul, div_le_one hn1]
      linarith
    have hsq : (√h * ‖r‖) ^ 2 ≤ (K * h ^ 2 / 12) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hh0.le]
      nlinarith [sq_nonneg (K * h ^ 2 / 12), norm_nonneg r, Nat.cast_nonneg (α := ℝ) n]
    calc √h * ‖r‖ = √((√h * ‖r‖) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √((K * h ^ 2 / 12) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = K * h ^ 2 / 12 := Real.sqrt_sq (by positivity)
  have hfinal : M * discreteL2Norm h e ≤ K * h ^ 2 / 12 := by
    rw [discreteL2Norm, ← mul_assoc, mul_comm M (√h), mul_assoc]
    exact le_trans (by nlinarith [Real.sqrt_nonneg h]) hnormr
  rw [le_div_iff₀ (by positivity)]
  have hkey := mul_le_mul_of_nonneg_left hfinal (by positivity : (0 : ℝ) ≤ 12 * h ^ 2)
  have hMe : 12 * h ^ 2 * (M * discreteL2Norm h e)
      = discreteL2Norm h e * (48 * sin (π * h / 2) ^ 2) := by
    rw [hM]; field_simp; ring
  rw [hMe] at hkey
  calc discreteL2Norm h e * (48 * sin (π * h / 2) ^ 2) ≤ 12 * h ^ 2 * (K * h ^ 2 / 12) := hkey
    _ = K * h ^ 4 := by ring

/-- **Example 13.6** of [saad2003iterative], the closing display. Under the hypotheses of
`SaadSparse.Chapter13.example_13_6`,
$$\|u^h - u\|_h \le \frac{K h^2}{12 \pi^2 \left(1 - (\pi h/2)^2/6\right)^2}.$$

**Correction.** The book bounds $1/\lambda_{\min}$ by $1/(\pi^2(1 - (\pi h/2)^2/6))$ and
concludes $\|u^h - u\|_h \le K h^2/(12\pi^2(1 - (\pi h/2)^2/6))$. Its own step does not give
this: $\lambda_{\min} = \pi^2(\sin x/x)^2$ at $x = \pi h/2$, and $\sin x/x \ge 1 - x^2/6$ bounds
the square by $(1 - x^2/6)^2$, not by $1 - x^2/6$. The printed step is false, because
$1 - x^2/6$ is not a lower bound for $(\sin x/x)^2$: at $h = 1/2$, $(\sin x/x)^2 = 0.8105\ldots
< 0.8971\ldots = 1 - x^2/6$. The statement here has the square, which is what the argument
proves, and is only slightly weaker.

No hypothesis on $h$ beyond $h = 1/(n+1)$ is needed, because $\pi h/2 \le 2$ already makes the
bracket positive. -/
theorem example_13_6_le {h : ℝ} (hh : h = 1 / ((n : ℝ) + 1)) {u f : ℝ → ℝ}
    (hu : ContDiff ℝ 4 u) (hu0 : u 0 = 0) (hu1 : u 1 = 0)
    (hf : ∀ x, f x = -iteratedDeriv 2 u x) {K : ℝ}
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv 4 u x| ≤ K)
    {uh : EuclideanSpace ℝ (Fin n)}
    (huh : (Chapter02.laplacian1D n h ⬝ uh) = gridSample n h f) :
    discreteL2Norm h (uh - gridSample n h u)
      ≤ K * h ^ 2 / (12 * π ^ 2 * (1 - (π * h / 2) ^ 2 / 6) ^ 2) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hh0 : 0 < h := by rw [hh]; positivity
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_one hn1]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hK0 : (0 : ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0 ⟨le_refl 0, zero_le_one⟩)
  have hx : (0 : ℝ) ≤ π * h / 2 := by positivity
  have hpimul : π * h ≤ π := by
    have := mul_le_mul_of_nonneg_left hh1 Real.pi_pos.le
    linarith
  have hxle : π * h / 2 ≤ 2 := by linarith [Real.pi_le_four]
  have hden : (0 : ℝ) < 1 - (π * h / 2) ^ 2 / 6 := by nlinarith [hx, hxle]
  have hlow : (π * h / 2) * (1 - (π * h / 2) ^ 2 / 6) ≤ sin (π * h / 2) := by
    have h1 := Real.sin_ge_sub_cube hx
    have h2 : (π * h / 2) * (1 - (π * h / 2) ^ 2 / 6)
        = π * h / 2 - (π * h / 2) ^ 3 / 6 := by ring
    rw [h2]
    exact h1
  have hsq : (π * h / 2) ^ 2 * (1 - (π * h / 2) ^ 2 / 6) ^ 2 ≤ sin (π * h / 2) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlow 2
  have hsin : 0 < sin (π * h / 2) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
    nlinarith [Real.pi_pos]
  refine le_trans (example_13_6 hh hu hu0 hu1 hf hK huh) ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 48 * K * h ^ 2)
  have heq : 48 * K * h ^ 2 * ((π * h / 2) ^ 2 * (1 - (π * h / 2) ^ 2 / 6) ^ 2)
      = K * h ^ 4 * (12 * π ^ 2 * (1 - (π * h / 2) ^ 2 / 6) ^ 2) := by ring
  rw [heq] at h2
  linarith

end DiscretizationError

end SaadSparse.Chapter13
