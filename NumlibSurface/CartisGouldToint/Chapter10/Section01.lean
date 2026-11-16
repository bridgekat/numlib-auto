/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Krylov.LanczosTridiag
import Numlib.Optimization.Subproblem.KrylovConvergence
import NumlibSurface.CartisGouldToint.Chapter08.Section02

/-!
# Cartis, Gould and Toint, Section 10.1: Krylov-subspace methods

This module formalizes Section 10.1 of [cartis2022evaluation]. Let $H$ be symmetric, $M$ symmetric
positive definite and $g \in \mathbb{R}^n$. The subspace subproblems (10.1.1) minimize the models of
Chapter 8 over a subspace $\mathcal{S}$; with a basis matrix $S$ of $\mathcal{S}$ they are the
subproblems (8.1.2) and (8.1.3) for the reduced data $S^T g$, $S^T H S$ and $S^T M S$ (10.1.2). The
natural subspaces are the Krylov subspaces $\mathcal{K}_k = \mathcal{K}(M^{-1} H, M^{-1} g, k) =
\operatorname{span}\{(M^{-1} H)^i M^{-1} g\}_{i < k}$.

The preconditioned Lanczos method (Algorithm 10.1.1) computes an $M$-orthonormal basis
$Q_k = (q_1, \dots, q_k)$ of $\mathcal{K}_k$ with $Q_k^T H Q_k = T_k$ tridiagonal and
$Q_k^T g = \gamma_1 e_1$, $\gamma_1 = \|g\|_{M^{-1}}$ (10.1.3)–(10.1.4). So on $\mathcal{K}_k$ the
subproblems become the subproblems for $(\gamma_1 e_1, T_k)$ in the Euclidean norm of $\mathbb{R}^k$
(10.1.5)–(10.1.6). Section 10.1.2 shows that in the hard case the Krylov subspaces never meet the
leftmost eigenvectors. The Lanczos quantities are defined through the Lanczos process of the scaled
operator $M^{-1} H$ on the $M$-inner product space `Subproblem.ScaledSpace`, with the backbone
modules `Numlib.Krylov.Subspace`, `Numlib.Krylov.Arnoldi` and `Numlib.Krylov.Lanczos`.

## Main definitions

* Section 10.1.1, `CartisGouldToint.Chapter10.krylovSpace`, `CartisGouldToint.Chapter10.gradeHM`:
  the Krylov subspace $\mathcal{K}_k$ and the grade of $M^{-1} H$ with respect to $M^{-1} g$.
* Equation (10.1.1), `CartisGouldToint.Chapter10.IsTRSubspaceSolution`,
  `CartisGouldToint.Chapter10.IsRegSubspaceSolution`: the subspace subproblems.
* Equation (10.1.3), `CartisGouldToint.Chapter10.lanczosVec`,
  `CartisGouldToint.Chapter10.lanczosBasis`, `CartisGouldToint.Chapter10.lanczosTridiag`: the
  Lanczos vectors $q_j$, the basis matrix $Q_k$ and the tridiagonal matrix $T_k$.
* Equation (10.1.2), `CartisGouldToint.Chapter10.lanczosGrad`: the reduced gradient $Q_k^T g$.
* Algorithm 10.1.1, `CartisGouldToint.Chapter10.algorithm_10_1_1`: a run of the preconditioned
  Lanczos method.

## Main results

* Equation (10.1.2), `CartisGouldToint.Chapter10.subspaceSolution_iff_reduced`: a subspace
  subproblem with basis matrix $S$ is the subproblem for the reduced data $S^T g$, $S^T H S$,
  $S^T M S$.
* Equation (10.1.5), `CartisGouldToint.Chapter10.isTRSubspaceSolution_krylov_iff`: on
  $\mathcal{K}_k$, the trust-region subproblem is the subproblem for $(\gamma_1 e_1, T_k)$ in the
  Euclidean norm.
* Equation (10.1.6), `CartisGouldToint.Chapter10.isRegSubspaceSolution_krylov_iff`: on
  $\mathcal{K}_k$, the regularization subproblem is the subproblem for $(\gamma_1 e_1, T_k)$ in the
  Euclidean norm.
* Algorithm 10.1.1, `CartisGouldToint.Chapter10.algorithm_10_1_1.q_eq_lanczosVec`: every run
  computes the Lanczos vectors.
* Algorithm 10.1.1, `CartisGouldToint.Chapter10.algorithm_10_1_1_spec`: the properties
  (10.1.3)–(10.1.4), (10.1.7) and (10.2.1) of a run, and termination at the grade.
* Section 10.1.2, `CartisGouldToint.Chapter10.krylov_hardCase_10_1_2`: in the hard case the Krylov
  subspaces and the subspace solutions are $M$-orthogonal to the leftmost eigenvectors.

## Implementation notes

* Lanczos indices are $0$-based in the definitions: `CartisGouldToint.Chapter10.lanczosVec hM H g j`
  is $q_{j+1}$.
* Runs of Algorithm 10.1.1 are indexed as in the source, from $k = 1$. The stopping test
  $\gamma_k = 0$ is modelled by the convention $x/0 = 0$ of Lean, under which every quantity
  vanishes after the stop.

## Deviations from the source

* **Equation (10.1.7)** (typo). The leading block of $T_k$ is $T_{k-1}$, not $T_{k-1}^{-1}$. See
  `CartisGouldToint.Chapter10.algorithm_10_1_1_spec`.
* **Section 10.1.1, nesting of the Krylov subspaces** (typo). $\mathcal{K}(A, b, k + 1)$ is the span
  of $\mathcal{K}(A, b, k) \cup \{A^k b\}$, not the union. See
  `CartisGouldToint.Chapter10.krylovSpace_succ`.
-/

open Matrix Set
open scoped RealInnerProductSpace

namespace CartisGouldToint.Chapter10

open Subproblem CartisGouldToint.Chapter08

variable {n : ℕ}

/-! ### Krylov subspaces -/

section KrylovSpace

variable (H M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))

/-- **Section 10.1.1** of [cartis2022evaluation], the **Krylov subspace**. For
$H, M \in \mathbb{R}^{n \times n}$, $g \in \mathbb{R}^n$ and $k \in \mathbb{N}$,
$$\mathcal{K}_k = \mathcal{K}(M^{-1} H, M^{-1} g, k) = \operatorname{span}\{(M^{-1} H)^i M^{-1}
  g \mid i < k\}.$$

The definition is `Krylov.subspace`, and $M^{-1}$ is the matrix inverse of Mathlib. -/
noncomputable def krylovSpace (k : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Krylov.subspace (toEuclideanLin (M⁻¹ * H)) (toEuclideanLin M⁻¹ g) k

/-- **Section 10.1.1** of [cartis2022evaluation], the **grade** of $M^{-1} H$ with respect to
$M^{-1} g$: the least $k$ with $\mathcal{K}(M^{-1} H, M^{-1} g, k) = \mathcal{K}(M^{-1} H,
M^{-1} g)$, the full Krylov subspace.

The definition is `Krylov.grade`, the dimension of the full Krylov subspace. -/
noncomputable def gradeHM : ℕ :=
  Krylov.grade (toEuclideanLin (M⁻¹ * H)) (toEuclideanLin M⁻¹ g)

/-- The Krylov subspaces are nested: $\mathcal{K}_k \subseteq \mathcal{K}_l$ for $k \le l$. -/
theorem krylovSpace_mono : Monotone (krylovSpace H M g) :=
  Krylov.subspace_mono _ _

/-- The dimension of $\mathcal{K}_k$ is $\min(k, \operatorname{grade}(M^{-1} H, M^{-1} g))$. In
particular $\dim \mathcal{K}_k \le k$. -/
theorem finrank_krylovSpace (k : ℕ) :
    Module.finrank ℝ (krylovSpace H M g k) = min k (gradeHM H M g) :=
  Krylov.finrank_subspace _ _ k

/-- The grade satisfies $\operatorname{grade}(M^{-1} H, M^{-1} g) \le n$. -/
theorem gradeHM_le : gradeHM H M g ≤ n :=
  (Krylov.grade_le_finrank _ _).trans_eq (finrank_euclideanSpace_fin)

/-- The Krylov subspaces stabilize at the grade: if
$\operatorname{grade}(M^{-1} H, M^{-1} g) \le k$, then $\mathcal{K}_k =
\mathcal{K}_{\operatorname{grade}}$. -/
theorem krylovSpace_eq_of_gradeHM_le {k : ℕ} (h : gradeHM H M g ≤ k) :
    krylovSpace H M g k = krylovSpace H M g (gradeHM H M g) :=
  Krylov.subspace_eq_of_grade_le _ _ h

/-- **Section 10.1.1** of [cartis2022evaluation], nesting of the Krylov subspaces. For every $k$,
$$\mathcal{K}_{k+1} = \operatorname{span}\bigl(\mathcal{K}_k \cup \{(M^{-1} H)^k M^{-1}
  g\}\bigr).$$

**Typo.** The source writes the union $\mathcal{K}_k \cup \{(M^{-1} H)^k M^{-1} g\}$ in place of
its span. -/
theorem krylovSpace_succ (k : ℕ) :
    krylovSpace H M g (k + 1) =
      krylovSpace H M g k ⊔ ℝ ∙ ((toEuclideanLin (M⁻¹ * H)) ^ k) (toEuclideanLin M⁻¹ g) := by
  simp only [krylovSpace, Krylov.subspace]
  rw [show Set.range (fun i : Fin (k + 1) => ((toEuclideanLin (M⁻¹ * H)) ^ (i : ℕ))
      (toEuclideanLin M⁻¹ g)) = Set.range (fun i : Fin k => ((toEuclideanLin (M⁻¹ * H)) ^ (i : ℕ))
      (toEuclideanLin M⁻¹ g)) ∪ {((toEuclideanLin (M⁻¹ * H)) ^ k) (toEuclideanLin M⁻¹ g)} by
    ext x
    simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      rcases Fin.lastCases (motive := fun i : Fin (k + 1) => (i : ℕ) = k ∨ (i : ℕ) < k)
        (Or.inl rfl) (fun j => Or.inr j.2) i with h | h
      · exact Or.inr (by rw [h])
      · exact Or.inl ⟨⟨i, h⟩, rfl⟩
    · rintro (⟨i, rfl⟩ | rfl)
      · exact ⟨i.castSucc, rfl⟩
      · exact ⟨Fin.last k, rfl⟩, Submodule.span_union]

/-- At the grade, the Krylov subspace $\mathcal{K}_{\operatorname{grade}}$ is invariant under
$M^{-1} H$. -/
theorem krylovSpace_gradeHM_mem_invtSubmodule :
    krylovSpace H M g (gradeHM H M g) ∈ Module.End.invtSubmodule (toEuclideanLin (M⁻¹ * H)) :=
  Krylov.subspace_grade_mem_invtSubmodule _ _

end KrylovSpace

/-! ### The bridge to the $M$-inner product space -/

section Bridge

variable {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

/-- For $M$ positive definite, the scaled operator `Subproblem.scaledOp`, as a linear map, is the
transport of $M^{-1} H$ to the $M$-inner product space. -/
theorem coe_scaledOp_eq (hM : M.PosDef) :
    (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) =
      hM.isPreconditioner_toEuclideanLin.energyEnd (toEuclideanLin (M⁻¹ * H)) := by
  rw [scaledOp, LinearMap.coe_toContinuousLinearMap, toEuclideanLin_mul]

/-- For $M$ positive definite, the image of $\mathcal{K}(M^{-1} H, M^{-1} g, k)$ in the $M$-inner
product space is the Krylov subspace of the scaled operator $M^{-1} H$ and the scaled gradient
$M^{-1} g$ there. -/
theorem map_toScaled_krylovSpace (hM : M.PosDef) (k : ℕ) :
    (krylovSpace H M g k).map (toScaled hM : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ScaledSpace hM) =
      Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g) k := by
  rw [coe_scaledOp_eq, scaledGrad, hM.isPreconditioner_toEuclideanLin.subspace_energyEnd]
  rfl

/-- For $M$ positive definite, a vector $s$ lies in $\mathcal{K}_k$ if and only if its image in the
$M$-inner product space lies in the Krylov subspace of the scaled operator and the scaled
gradient. -/
theorem toScaled_mem_krylov_iff (hM : M.PosDef) {k : ℕ} {s : EuclideanSpace ℝ (Fin n)} :
    toScaled hM s ∈
        Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k ↔
      s ∈ krylovSpace H M g k := by
  rw [← map_toScaled_krylovSpace hM k]
  constructor
  · rintro ⟨x, hx, hxs⟩
    rwa [← (toScaled hM).injective hxs]
  · intro hs
    exact ⟨s, hs, rfl⟩

/-- For $M$ positive definite, the grade of $M^{-1} H$ with respect to $M^{-1} g$ equals the grade
of the scaled operator with respect to the scaled gradient on the $M$-inner product space. -/
theorem gradeHM_eq (hM : M.PosDef) :
    gradeHM H M g =
      Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) := by
  have h : ∀ m, min m (gradeHM H M g) =
      min m (Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g)) := fun m => by
    rw [← finrank_krylovSpace, ← Krylov.finrank_subspace, ← map_toScaled_krylovSpace hM m,
      LinearEquiv.finrank_map_eq]
  have := h (gradeHM H M g + Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
    (scaledGrad hM g))
  omega

end Bridge

/-! ### Subspace subproblems -/

section Subspace

variable {k : ℕ} {g : EuclideanSpace ℝ (Fin n)} {H M : Matrix (Fin n) (Fin n) ℝ}

/-- **Equation (10.1.1)** of [cartis2022evaluation], the trust-region subproblem on a subspace. Let
$\mathcal{S}$ be a subspace of $\mathbb{R}^n$ and $\Delta \in \mathbb{R}$. A vector $s$ is a
**global minimizer of the trust-region subproblem on $\mathcal{S}$** if $s \in \mathcal{S}$,
$\|s\|_M \le \Delta$, and $m(s) \le m(u)$ for every $u \in \mathcal{S}$ with
$\|u\|_M \le \Delta$. -/
def IsTRSubspaceSolution (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ) (Δ : ℝ)
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  s ∈ S ∧ mNorm M s ≤ Δ ∧ ∀ u ∈ S, mNorm M u ≤ Δ → model g H s ≤ model g H u

/-- **Equation (10.1.1)** of [cartis2022evaluation], the regularization subproblem on a subspace.
Let $\mathcal{S}$ be a subspace of $\mathbb{R}^n$ and $\sigma, r \in \mathbb{R}$. A vector $s$
is a **global minimizer of the regularization subproblem on $\mathcal{S}$** if
$s \in \mathcal{S}$ and $m^R(s, \sigma, r) \le m^R(u, \sigma, r)$ for every $u \in \mathcal{S}$. -/
def IsRegSubspaceSolution (g : EuclideanSpace ℝ (Fin n)) (H M : Matrix (Fin n) (Fin n) ℝ)
    (σ r : ℝ) (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (s : EuclideanSpace ℝ (Fin n)) : Prop :=
  s ∈ S ∧ ∀ u ∈ S, regModel g H M σ r s ≤ regModel g H M σ r u

/-- For $S \in \mathbb{R}^{n \times k}$ and $y \in \mathbb{R}^k$, the quadratic model at $S y$ is
the model of the reduced data at $y$: $m_{g, H}(S y) = m_{S^T g, S^T H S}(y)$. -/
theorem model_toEuclideanLin (S : Matrix (Fin n) (Fin k) ℝ) (y : EuclideanSpace ℝ (Fin k)) :
    model g H (toEuclideanLin S y) = model (toEuclideanLin Sᵀ g) (Sᵀ * H * S) y := by
  rw [model_def, model_def, toEuclideanLin_transpose_inner_left, toEuclideanLin_mul_apply,
    toEuclideanLin_mul_apply, toEuclideanLin_transpose_inner_right]

/-- For $S \in \mathbb{R}^{n \times k}$ and $y \in \mathbb{R}^k$, $\|S y\|_M = \|y\|_{S^T M S}$. -/
theorem mNorm_toEuclideanLin (S : Matrix (Fin n) (Fin k) ℝ) (y : EuclideanSpace ℝ (Fin k)) :
    mNorm M (toEuclideanLin S y) = mNorm (Sᵀ * M * S) y := by
  rw [mNorm_def, mNorm_def, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_transpose_inner_right]

/-- For $S \in \mathbb{R}^{n \times k}$, $y \in \mathbb{R}^k$ and $\sigma, r \in \mathbb{R}$, the
regularized model at $S y$ is the regularized model of the reduced data $S^T g$, $S^T H S$,
$S^T M S$ at $y$. -/
theorem regModel_toEuclideanLin (S : Matrix (Fin n) (Fin k) ℝ) (σ r : ℝ)
    (y : EuclideanSpace ℝ (Fin k)) :
    regModel g H M σ r (toEuclideanLin S y) =
      regModel (toEuclideanLin Sᵀ g) (Sᵀ * H * S) (Sᵀ * M * S) σ r y := by
  rw [Chapter08.regModel_def, Chapter08.regModel_def, model_toEuclideanLin, mNorm_toEuclideanLin]

/-- **Equation (10.1.2)** of [cartis2022evaluation], the reduced subproblems. Let
$S \in \mathbb{R}^{n \times k}$, let $\mathcal{S}$ be the column space of $S$, and let
$\bar s \in \mathbb{R}^k$. Then:

* for every $\Delta$, $S \bar s$ is a global minimizer of the trust-region subproblem on
  $\mathcal{S}$ if and only if $\bar s$ is a global minimizer of the trust-region subproblem
  (8.1.2) for $\bar g = S^T g$, $\bar H = S^T H S$ and $\bar M = S^T M S$;
* for all $\sigma, r$, $S \bar s$ is a global minimizer of the regularization subproblem on
  $\mathcal{S}$ if and only if $\bar s$ is a global minimizer of the regularization subproblem
  (8.1.3) for the same reduced data.

The columns of $S$ need not be linearly independent. -/
theorem subspaceSolution_iff_reduced (S : Matrix (Fin n) (Fin k) ℝ)
    (sbar : EuclideanSpace ℝ (Fin k)) :
    (∀ Δ, IsTRSubspaceSolution g H M Δ (LinearMap.range (toEuclideanLin S))
        (toEuclideanLin S sbar) ↔
      IsTrustRegionSolution (toEuclideanLin Sᵀ g) (Sᵀ * H * S) (Sᵀ * M * S) Δ sbar) ∧
    ∀ σ r, IsRegSubspaceSolution g H M σ r (LinearMap.range (toEuclideanLin S))
        (toEuclideanLin S sbar) ↔
      IsRegularizationSolution (toEuclideanLin Sᵀ g) (Sᵀ * H * S) (Sᵀ * M * S) σ r sbar := by
  refine ⟨fun Δ => ?_, fun σ r => ?_⟩
  · simp only [IsTRSubspaceSolution, isTrustRegionSolution_iff, LinearMap.mem_range,
      exists_apply_eq_apply, true_and, forall_exists_index, forall_apply_eq_imp_iff,
      mNorm_toEuclideanLin, model_toEuclideanLin]
  · simp only [IsRegSubspaceSolution, isRegularizationSolution_iff, LinearMap.mem_range,
      exists_apply_eq_apply, true_and, forall_exists_index, forall_apply_eq_imp_iff,
      regModel_toEuclideanLin]

end Subspace

/-! ### The Lanczos vectors, the basis $Q_k$ and the tridiagonal $T_k$ -/

section Lanczos

/-- **Equation (10.1.3)** of [cartis2022evaluation], the **Lanczos vector** $q_{j+1}$. Let $M$ be
symmetric positive definite and $j \in \mathbb{N}$. The vector $q_{j+1}$ is the $j$-th vector of
the Lanczos process of $M^{-1} H$ started from $M^{-1} g$ in the $M$-inner product, read back in
$\mathbb{R}^n$. It is $0$ from the grade on.

The index `j` is $0$-based. The vector is `Arnoldi.vec` of the scaled operator and the scaled
gradient. Algorithm 10.1.1 computes it
(`CartisGouldToint.Chapter10.algorithm_10_1_1.q_eq_lanczosVec`). -/
noncomputable def lanczosVec {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (toScaled hM).symm
    (Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) j)

/-- **Equation (10.1.3)** of [cartis2022evaluation], the **Lanczos basis matrix** $Q_k = (q_1,
\dots, q_k) \in \mathbb{R}^{n \times k}$, whose columns are the Lanczos vectors. -/
noncomputable def lanczosBasis {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => lanczosVec hM H g j i

/-- **Equation (10.1.3)** of [cartis2022evaluation], the **Lanczos tridiagonal matrix**
$T_k \in \mathbb{R}^{k \times k}$: the symmetric tridiagonal matrix with diagonal
$\rho_1, \dots, \rho_k$ and off-diagonal $\gamma_2, \dots, \gamma_k$, the Lanczos coefficients
of $M^{-1} H$ in the $M$-inner product.

The definition is `Lanczos.tridiag` of the scaled operator and the scaled gradient. -/
noncomputable def lanczosTridiag {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Lanczos.tridiag (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k

/-- The Lanczos tridiagonal matrix $T_k$ is `Lanczos.tridiag` of the scaled operator $M^{-1} H$ and
the scaled gradient $M^{-1} g$ on the $M$-inner product space. -/
theorem lanczosTridiag_def {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    lanczosTridiag hM H g k =
      Lanczos.tridiag (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) k :=
  rfl

/-- **Equation (10.1.2)** of [cartis2022evaluation], the **reduced gradient**
$\bar g_k = Q_k^T g \in \mathbb{R}^k$. It equals $\gamma_1 e_1$ for $k \ge 1$
(`CartisGouldToint.Chapter10.lanczosGrad_eq`). -/
noncomputable def lanczosGrad {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef)
    (H : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin k) :=
  toEuclideanLin (lanczosBasis hM H g k)ᵀ g

variable {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)} (hM : M.PosDef) {k : ℕ}

/-- In the $M$-inner product space, the Lanczos vectors are the Arnoldi vectors `Arnoldi.vec` of the
scaled operator and the scaled gradient. -/
@[simp]
theorem toScaled_lanczosVec (j : ℕ) :
    toScaled hM (lanczosVec hM H g j) =
      Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) j :=
  (toScaled hM).apply_symm_apply _

/-- For $y \in \mathbb{R}^k$, $Q_k y = \sum_j y_j q_{j+1}$, with $0$-based $j$. -/
theorem toEuclideanLin_lanczosBasis (y : EuclideanSpace ℝ (Fin k)) :
    toEuclideanLin (lanczosBasis hM H g k) y = ∑ j, y j • lanczosVec hM H g j := by
  ext i
  simp [lanczosBasis, toEuclideanLin_apply, mulVec, dotProduct, mul_comm]

/-- For $j < k$, $Q_k e_j = q_{j+1}$, with $0$-based $j$. -/
theorem toEuclideanLin_lanczosBasis_single (j : Fin k) :
    toEuclideanLin (lanczosBasis hM H g k) (EuclideanSpace.single j 1) = lanczosVec hM H g j := by
  rw [toEuclideanLin_lanczosBasis]
  simp [PiLp.single_apply]

/-- In the $M$-inner product space, $Q_k y = \sum_j y_j v_j$, where $v_j$ are the Arnoldi vectors of
the scaled operator and the scaled gradient. -/
theorem toScaled_lanczosBasis (y : EuclideanSpace ℝ (Fin k)) :
    toScaled hM (toEuclideanLin (lanczosBasis hM H g k) y) =
      ∑ j, y j • Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g) j := by
  rw [toEuclideanLin_lanczosBasis, map_sum]
  simp only [map_smul, toScaled_lanczosVec]

/-- The columns of $Q_k$ span $\mathcal{K}_k$: the range of $Q_k$ is $\mathcal{K}_k$. -/
theorem range_lanczosBasis :
    LinearMap.range (toEuclideanLin (lanczosBasis hM H g k)) = krylovSpace H M g k := by
  ext s
  rw [LinearMap.mem_range, ← toScaled_mem_krylov_iff hM]
  constructor
  · rintro ⟨y, rfl⟩
    rw [toScaled_lanczosBasis]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Arnoldi.vec_mem_subspace_of_lt _ _ j.2)
  · intro hs
    refine ⟨WithLp.toLp 2 fun j : Fin k => ⟪Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] _)
      (scaledGrad hM g) j, toScaled hM s⟫, (toScaled hM).injective ?_⟩
    rw [toScaled_lanczosBasis]
    conv_rhs => rw [Arnoldi.eq_sum_inner_smul_vec _ _ hs]
    exact Fin.sum_univ_eq_sum_range (fun j => ⟪Arnoldi.vec (scaledOp H hM : _ →ₗ[ℝ] _)
      (scaledGrad hM g) j, toScaled hM s⟫ • Arnoldi.vec (scaledOp H hM : _ →ₗ[ℝ] _)
        (scaledGrad hM g) j) k

/-- A matrix entry is a bilinear form of coordinate vectors: $a_{ij} = \langle e_i, A e_j \rangle$.
-/
private theorem entry_eq_inner {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m) :
    A i j = ⟪EuclideanSpace.single i 1, toEuclideanLin A (EuclideanSpace.single j 1)⟫ := by
  simp [EuclideanSpace.inner_single_left, toEuclideanLin_apply]

/-- A matrix entry is a coordinate of the image of a coordinate vector: $a_{ij} = (A e_j)_i$. -/
private theorem entry_eq_apply_single {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) (i : Fin m)
    (j : Fin p) :
    A i j = toEuclideanLin A (EuclideanSpace.single j 1) i := by
  simp [toEuclideanLin_apply]

/-- For $A \in \mathbb{R}^{n \times n}$, the entries of $Q_k^T A Q_k$ are $(Q_k^T A Q_k)_{ij} =
\langle q_{i+1}, A q_{j+1} \rangle$, with $0$-based $i, j$. -/
theorem lanczosBasis_transpose_mul_mul_apply (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin k) :
    ((lanczosBasis hM H g k)ᵀ * A * lanczosBasis hM H g k) i j =
      ⟪lanczosVec hM H g i, toEuclideanLin A (lanczosVec hM H g j)⟫ := by
  refine (entry_eq_inner _ i j).trans ?_
  rw [toEuclideanLin_mul_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_transpose_inner_right, toEuclideanLin_lanczosBasis_single,
    toEuclideanLin_lanczosBasis_single]

/-- The entries of $Q_k^T g$ are $\langle q_{i+1}, g \rangle$, with $0$-based $i$. -/
theorem lanczosGrad_apply (i : Fin k) : lanczosGrad hM H g k i = ⟪lanczosVec hM H g i, g⟫ := by
  rw [← toEuclideanLin_lanczosBasis_single hM (H := H) (g := g) i,
    ← toEuclideanLin_transpose_inner_right, EuclideanSpace.inner_single_left]
  simp [lanczosGrad]

/-- The number $\langle q_{i+1}, M q_{j+1} \rangle$ is the $M$-inner product of the Arnoldi vectors
$v_i$ and $v_j$ of the scaled operator. -/
theorem inner_lanczosVec_M (i j : ℕ) :
    ⟪lanczosVec hM H g i, toEuclideanLin M (lanczosVec hM H g j)⟫ =
      ⟪Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) i,
        Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) j⟫ := by
  rw [real_inner_comm, ← inner_toScaled, real_inner_comm, toScaled_lanczosVec, toScaled_lanczosVec]

/-- The number $\langle q_{i+1}, H q_{j+1} \rangle$ is the Arnoldi coefficient $h_{ij}$ of the
scaled operator. -/
theorem inner_lanczosVec_H (i j : ℕ) :
    ⟪lanczosVec hM H g i, toEuclideanLin H (lanczosVec hM H g j)⟫ =
      Arnoldi.coeff (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
        (scaledGrad hM g) i j := by
  rw [real_inner_comm, ← inner_scaledOp_toScaled, real_inner_comm, toScaled_lanczosVec,
    toScaled_lanczosVec, Arnoldi.coeff]
  rfl

/-- The number $\langle q_{i+1}, g \rangle$ equals $\langle v_i, M^{-1} g \rangle_M$, where $v_i$ is
the Arnoldi vector of the scaled operator. -/
theorem inner_lanczosVec_g (i : ℕ) :
    ⟪lanczosVec hM H g i, g⟫ =
      ⟪Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) i,
        scaledGrad hM g⟫ := by
  rw [← toScaled_lanczosVec, inner_toScaled_scaledGrad]

/-- **Equation (10.1.3)** of [cartis2022evaluation], $M$-orthonormality. If
$k \le \operatorname{grade}(M^{-1} H, M^{-1} g)$, then $Q_k^T M Q_k = I_k$. -/
theorem lanczosBasis_transpose_mul_M (hk : k ≤ gradeHM H M g) :
    (lanczosBasis hM H g k)ᵀ * M * lanczosBasis hM H g k = 1 := by
  ext i j
  rw [lanczosBasis_transpose_mul_mul_apply, inner_lanczosVec_M, Matrix.one_apply]
  rw [gradeHM_eq hM] at hk
  split_ifs with hij
  · subst hij
    rw [real_inner_self_eq_norm_sq, Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (i.2.trans_le hk),
      one_pow]
  · exact Arnoldi.inner_vec_eq_zero _ _ (fun h => hij (Fin.ext h))

/-- **Equation (10.1.3)** of [cartis2022evaluation], tridiagonalization. If $H$ is symmetric, then
$Q_k^T H Q_k = T_k$. -/
theorem lanczosBasis_transpose_mul_H (hH : H.IsHermitian) :
    (lanczosBasis hM H g k)ᵀ * H * lanczosBasis hM H g k = lanczosTridiag hM H g k := by
  ext i j
  rw [lanczosBasis_transpose_mul_mul_apply, inner_lanczosVec_H]
  have h := congrFun (congrFun (Lanczos.hessenbergSq_eq_map_tridiag (scaledGrad hM g)
    (isSymmetric_scaledOp (hM := hM) hH) k) i) j
  simpa [Arnoldi.hessenbergSq, lanczosTridiag] using h

/-- **Equations (10.1.3)–(10.1.4)** of [cartis2022evaluation], the reduced gradient. For $k \ge 1$,
$Q_k^T g = \gamma_1 e_1$ with $\gamma_1 = \|g\|_{M^{-1}}$. -/
theorem lanczosGrad_eq (hk : 0 < k) :
    lanczosGrad hM H g k = EuclideanSpace.single ⟨0, hk⟩ (mNorm M⁻¹ g) := by
  ext i
  rw [lanczosGrad_apply, inner_lanczosVec_g, mNorm_inv_eq_norm_scaledGrad hM,
    PiLp.single_apply]
  rcases eq_or_ne (scaledGrad hM g) 0 with hb | hb
  · rw [hb]; simp
  · set V := Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
      with hV
    have hv0 : V 0 = ‖scaledGrad hM g‖⁻¹ • scaledGrad hM g := by
      rw [hV, Arnoldi.vec_zero _ _ hb]; rfl
    have hb' : scaledGrad hM g = ‖scaledGrad hM g‖ • V 0 := by
      rw [hv0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hb), one_smul]
    have hi : ⟪V i, scaledGrad hM g⟫ = ‖scaledGrad hM g‖ * ⟪V i, V 0⟫ := by
      conv_lhs => rw [hb']
      rw [real_inner_smul_right]
    rw [hi]
    split_ifs with hi0
    · subst hi0
      have : (0 : ℕ) < Krylov.grade (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
          (scaledGrad hM g) := Krylov.grade_pos_of_ne_zero _ _ hb
      rw [real_inner_self_eq_norm_sq, Arnoldi.norm_vec_eq_one_of_lt_grade _ _ this]
      simp
    · rw [Arnoldi.inner_vec_eq_zero _ _ (fun h => hi0 (Fin.ext h)), mul_zero]

/-- **Equation (10.2.1)** of [cartis2022evaluation], the Lanczos relation. Let $H$ be symmetric and
$k = m + 1$. Then
$$H Q_k - M Q_k T_k = \gamma_{k+1} w_{k+1} e_k^T,$$
where $\gamma_{k+1} w_{k+1} = \gamma_{k+1} M q_{k+1}$ and $\gamma_{k+1}$ is the next
off-diagonal Lanczos coefficient, which is $0$ at the grade.

The coefficient $\gamma_{k+1}$ is `Lanczos.beta` at the $0$-based index $m$. -/
theorem lanczos_relation (hH : H.IsHermitian) (m : ℕ) :
    H * lanczosBasis hM H g (m + 1) -
        M * lanczosBasis hM H g (m + 1) * lanczosTridiag hM H g (m + 1) =
      Matrix.of fun a (j : Fin (m + 1)) => if j = Fin.last m then
        Lanczos.beta (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) m *
          toEuclideanLin M (lanczosVec hM H g (m + 1)) a else 0 := by
  -- the relation applied to a vector `y`
  have key : ∀ y : EuclideanSpace ℝ (Fin (m + 1)),
      toEuclideanLin H (toEuclideanLin (lanczosBasis hM H g (m + 1)) y) =
        toEuclideanLin M (toEuclideanLin (lanczosBasis hM H g (m + 1))
          (toEuclideanLin (lanczosTridiag hM H g (m + 1)) y)) +
        (Lanczos.beta (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) m *
          y (Fin.last m)) • toEuclideanLin M (lanczosVec hM H g (m + 1)) := by
    intro y
    have h1 := Lanczos.apply_sum (scaledGrad hM g) (isSymmetric_scaledOp (hM := hM) hH) m
      (WithLp.ofLp y)
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, RCLike.ofReal_real_eq_id,
      id] at h1
    have h2 : toEuclideanLin M⁻¹ (toEuclideanLin H (toEuclideanLin (lanczosBasis hM H g (m + 1)) y))
        = toEuclideanLin (lanczosBasis hM H g (m + 1))
            (toEuclideanLin (lanczosTridiag hM H g (m + 1)) y) +
          (Lanczos.beta (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) m *
            y (Fin.last m)) • lanczosVec hM H g (m + 1) := by
      apply (toScaled hM).injective
      rw [← scaledOp_toScaled, toScaled_lanczosBasis, map_add, toScaled_lanczosBasis, map_smul,
        toScaled_lanczosVec]
      exact h1
    have h3 := congrArg (toEuclideanLin M) h2
    rw [toEuclideanLin_mul_nonsing_inv_apply hM.isUnit, map_add, map_smul] at h3
    exact h3
  ext a j
  refine (entry_eq_apply_single _ a j).trans ?_
  rw [map_sub, LinearMap.sub_apply, toEuclideanLin_mul_apply,
    toEuclideanLin_mul_apply, toEuclideanLin_mul_apply, key, PiLp.sub_apply, PiLp.add_apply,
    add_sub_cancel_left, PiLp.smul_apply, Matrix.of_apply, PiLp.single_apply]
  by_cases hj : j = Fin.last m
  · subst hj; simp
  · simp [hj, Ne.symm hj]

end Lanczos

/-! ### The reduced Krylov subproblems (10.1.5)–(10.1.6) -/

section Reduced

variable {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)} (hM : M.PosDef) {k : ℕ}

/-- **Equation (10.1.5)** of [cartis2022evaluation], the trust-region subproblem on $\mathcal{K}_k$.
Let $H$ be symmetric, $M$ symmetric positive definite,
$k \le \operatorname{grade}(M^{-1} H, M^{-1} g)$, $\Delta \in \mathbb{R}$ and
$\bar s \in \mathbb{R}^k$. Then $Q_k \bar s$ is a global minimizer of the trust-region
subproblem on $\mathcal{K}_k$ if and only if $\bar s$ is a global minimizer of the trust-region
subproblem for the data $(Q_k^T g, T_k) = (\gamma_1 e_1, T_k)$ in the Euclidean norm of
$\mathbb{R}^k$.

Every element of $\mathcal{K}_k$ is some $Q_k \bar s$
(`CartisGouldToint.Chapter10.range_lanczosBasis`). The Euclidean norm is the scaled norm for
$M = I$. -/
theorem isTRSubspaceSolution_krylov_iff (hH : H.IsHermitian) (hk : k ≤ gradeHM H M g) (Δ : ℝ)
    (sbar : EuclideanSpace ℝ (Fin k)) :
    IsTRSubspaceSolution g H M Δ (krylovSpace H M g k)
        (toEuclideanLin (lanczosBasis hM H g k) sbar) ↔
      IsTrustRegionSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 Δ sbar := by
  have h := (subspaceSolution_iff_reduced (g := g) (H := H) (M := M) (lanczosBasis hM H g k)
    sbar).1 Δ
  rwa [range_lanczosBasis, lanczosBasis_transpose_mul_M hM hk,
    lanczosBasis_transpose_mul_H hM hH] at h

/-- **Equation (10.1.6)** of [cartis2022evaluation], the regularization subproblem on
$\mathcal{K}_k$. Let $H$ be symmetric, $M$ symmetric positive definite,
$k \le \operatorname{grade}(M^{-1} H, M^{-1} g)$, $\sigma, r \in \mathbb{R}$ and
$\bar s \in \mathbb{R}^k$. Then $Q_k \bar s$ is a global minimizer of the regularization
subproblem on $\mathcal{K}_k$ if and only if $\bar s$ is a global minimizer of the
regularization subproblem for the data $(Q_k^T g, T_k) = (\gamma_1 e_1, T_k)$ in the Euclidean
norm of $\mathbb{R}^k$. -/
theorem isRegSubspaceSolution_krylov_iff (hH : H.IsHermitian) (hk : k ≤ gradeHM H M g)
    (σ r : ℝ) (sbar : EuclideanSpace ℝ (Fin k)) :
    IsRegSubspaceSolution g H M σ r (krylovSpace H M g k)
        (toEuclideanLin (lanczosBasis hM H g k) sbar) ↔
      IsRegularizationSolution (lanczosGrad hM H g k) (lanczosTridiag hM H g k) 1 σ r sbar := by
  have h := (subspaceSolution_iff_reduced (g := g) (H := H) (M := M) (lanczosBasis hM H g k)
    sbar).2 σ r
  rwa [range_lanczosBasis, lanczosBasis_transpose_mul_M hM hk,
    lanczosBasis_transpose_mul_H hM hH] at h

/-- If $k \le \operatorname{grade}(M^{-1} H, M^{-1} g)$, then $\|Q_k y\|_M = \|y\|$ for every
$y \in \mathbb{R}^k$. -/
theorem mNorm_lanczosBasis (hk : k ≤ gradeHM H M g) (y : EuclideanSpace ℝ (Fin k)) :
    mNorm M (toEuclideanLin (lanczosBasis hM H g k) y) = ‖y‖ := by
  rw [mNorm_toEuclideanLin, lanczosBasis_transpose_mul_M hM hk, mNorm_one]

/-- A vector $s$ is a global minimizer of the regularization subproblem on $\mathcal{K}_k$ if and
only if, in the $M$-inner product space, it lies in the Krylov subspace of the scaled operator
and minimizes the regularized model `Subproblem.regModel` of the scaled data on that subspace. -/
theorem isRegSubspaceSolution_iff_scaled {σ r : ℝ} {s : EuclideanSpace ℝ (Fin n)} :
    IsRegSubspaceSolution g H M σ r (krylovSpace H M g k) s ↔
      toScaled hM s ∈
          Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
            (scaledGrad hM g) k ∧
        IsMinOn (Subproblem.regModel (scaledGrad hM g) (scaledOp H hM) σ r)
          (Krylov.subspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
            (scaledGrad hM g) k : Set (ScaledSpace hM)) (toScaled hM s) := by
  rw [IsRegSubspaceSolution, toScaled_mem_krylov_iff, isMinOn_iff]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h u hu => ?_⟩
  · obtain ⟨u, rfl⟩ := (toScaled hM).surjective x
    rw [← regModel_eq_regModel, ← regModel_eq_regModel]
    exact h u ((toScaled_mem_krylov_iff hM).1 hx)
  · rw [regModel_eq_regModel hM, regModel_eq_regModel hM]
    exact h _ ((toScaled_mem_krylov_iff hM).2 hu)

end Reduced

/-! ### Algorithm 10.1.1 -/

/-- **Algorithm 10.1.1** of [cartis2022evaluation] (the preconditioned Lanczos method), a run.
Sequences $t_k, y_k, w_k, q_k \in \mathbb{R}^n$ and $\gamma_k, \rho_k \in \mathbb{R}$ form a
**run of Algorithm 10.1.1** if $t_1 = g$, $w_0 = 0$ and, for every $k \ge 1$,
$$y_k = M^{-1} t_k, \quad \gamma_k = \sqrt{\langle t_k, y_k \rangle}, \quad w_k = t_k/\gamma_k,
  \quad q_k = y_k/\gamma_k, \quad \rho_k = \langle q_k, H q_k \rangle,$$
$$t_{k+1} = H q_k - \rho_k w_k - \gamma_k w_{k-1}.$$

The sequences are indexed as in the source, from $k = 1$; their values at $k = 0$ other than
$w_0$ are not constrained. The stop at $\gamma_k = 0$ is built in through the convention
$x/0 = 0$: from then on every quantity vanishes. -/
structure algorithm_10_1_1 (H M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (t y w q : ℕ → EuclideanSpace ℝ (Fin n)) (γ ρ : ℕ → ℝ) : Prop where
  /-- The first vector is $t_1 = g$. -/
  t_one : t 1 = g
  /-- The vector $w_0$ is $0$. -/
  w_zero : w 0 = 0
  /-- For $k \ge 1$, $y_k = M^{-1} t_k$. -/
  y_eq : ∀ k, 1 ≤ k → y k = toEuclideanLin M⁻¹ (t k)
  /-- For $k \ge 1$, $\gamma_k = \sqrt{\langle t_k, y_k \rangle}$. -/
  gamma_eq : ∀ k, 1 ≤ k → γ k = √⟪t k, y k⟫
  /-- For $k \ge 1$, $w_k = t_k/\gamma_k$. -/
  w_eq : ∀ k, 1 ≤ k → w k = (γ k)⁻¹ • t k
  /-- For $k \ge 1$, $q_k = y_k/\gamma_k$. -/
  q_eq : ∀ k, 1 ≤ k → q k = (γ k)⁻¹ • y k
  /-- For $k \ge 1$, $\rho_k = \langle q_k, H q_k \rangle$. -/
  rho_eq : ∀ k, 1 ≤ k → ρ k = ⟪q k, toEuclideanLin H (q k)⟫
  /-- For $k \ge 1$, $t_{k+1} = H q_k - \rho_k w_k - \gamma_k w_{k-1}$. -/
  t_succ : ∀ k, 1 ≤ k → t (k + 1) = toEuclideanLin H (q k) - ρ k • w k - γ k • w (k - 1)

/-- The state $(t_{k+1}, w_k)$ of Algorithm 10.1.1 after $k$ iterations. -/
private noncomputable def lanczosState (H M : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)
  | 0 => (g, 0)
  | k + 1 =>
    let t := (lanczosState H M g k).1
    let y := toEuclideanLin M⁻¹ t
    let γ := √⟪t, y⟫
    let q := γ⁻¹ • y
    (toEuclideanLin H q - ⟪q, toEuclideanLin H q⟫ • (γ⁻¹ • t) - γ • (lanczosState H M g k).2,
      γ⁻¹ • t)

/-- The first Arnoldi vector is $v_0 = b/\|b\|$, also for $b = 0$. -/
private theorem vec_zero' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ[ℝ] E) (b : E) : Arnoldi.vec A b 0 = ‖b‖⁻¹ • b := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [smul_zero, Arnoldi.vec_eq_zero_iff_pow_apply_mem, Krylov.subspace_zero, map_zero]
    exact Submodule.zero_mem _
  · exact Arnoldi.vec_zero A b hb

namespace algorithm_10_1_1

variable {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}
  {t y w q : ℕ → EuclideanSpace ℝ (Fin n)} {γ ρ : ℕ → ℝ}

/-- Algorithm 10.1.1 is well defined: for all $H$, $M$ and $g$ it has a run. -/
theorem exists_run (H M : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    ∃ t y w q γ ρ, algorithm_10_1_1 H M g t y w q γ ρ := by
  set T : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (lanczosState H M g (k - 1)).1
  set Y : ℕ → EuclideanSpace ℝ (Fin n) := fun k => toEuclideanLin M⁻¹ (T k)
  set Γ : ℕ → ℝ := fun k => √⟪T k, Y k⟫
  set W : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (Γ k)⁻¹ • T k
  set Q : ℕ → EuclideanSpace ℝ (Fin n) := fun k => (Γ k)⁻¹ • Y k
  refine ⟨T, Y, fun k => if k = 0 then 0 else W k, Q, Γ,
    fun k => ⟪Q k, toEuclideanLin H (Q k)⟫, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun k hk => by simp [Nat.one_le_iff_ne_zero.1 hk, W], fun _ _ => rfl, fun _ _ => rfl,
    fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false, ite_false]
  change (lanczosState H M g (j + 1)).1 = _
  rw [lanczosState]
  rcases j with _ | j
  · simp [T, W, Q, Y, Γ, lanczosState]
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    rfl

variable (h : algorithm_10_1_1 H M g t y w q γ ρ)
include h

/-- For a run of Algorithm 10.1.1 and $M$ positive definite, $t_k = M y_k$ for $k \ge 1$. -/
theorem t_eq (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) : t k = toEuclideanLin M (y k) := by
  rw [h.y_eq k hk, toEuclideanLin_mul_nonsing_inv_apply hM.isUnit]

/-- For a run of Algorithm 10.1.1 and $M$ positive definite, $\gamma_k = \|y_k\|_M$ for $k \ge 1$.
-/
theorem gamma_eq_norm (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) : γ k = ‖toScaled hM (y k)‖ := by
  rw [h.gamma_eq k hk, h.t_eq hM hk, norm_toScaled]

/-- For a run of Algorithm 10.1.1 and $M$ positive definite, $w_k = M q_k$ for $k \ge 1$. -/
theorem w_eq_M (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) : w k = toEuclideanLin M (q k) := by
  rw [h.w_eq k hk, h.q_eq k hk, map_smul, h.t_eq hM hk]

/-- For a run of Algorithm 10.1.1 and $M$ positive definite, $M^{-1} w_k$ is $0$ for $k = 0$ and
$q_k$ for $k \ge 1$. -/
theorem inv_w_pred (hM : M.PosDef) (k : ℕ) :
    toEuclideanLin M⁻¹ (w k) = if k = 0 then 0 else q k := by
  split_ifs with hk
  · rw [hk, h.w_zero, map_zero]
  · rw [h.w_eq_M hM (Nat.one_le_iff_ne_zero.2 hk), toEuclideanLin_nonsing_inv_mul_apply hM.isUnit]

/-- For a run of Algorithm 10.1.1 and $M$ positive definite, $y_{k+1} = M^{-1} H q_k - \rho_k q_k -
\gamma_k q_{k-1}$ for $k \ge 1$, with $q_0$ replaced by $0$. -/
theorem y_succ (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) :
    y (k + 1) = toEuclideanLin M⁻¹ (toEuclideanLin H (q k)) - ρ k • q k -
      γ k • (if k - 1 = 0 then 0 else q (k - 1)) := by
  rw [h.y_eq (k + 1) (by omega), h.t_succ k hk, map_sub, map_sub, map_smul, map_smul,
    h.inv_w_pred hM k, h.inv_w_pred hM (k - 1), ite_eq_right (by omega)]

/-- One step of the identification with the Lanczos process: if $y_{i+1}$, in the $M$-inner product
space, is the $i$-th unnormalized Lanczos vector ($M^{-1} g$ for $i = 0$), then $q_{i+1}$,
$\gamma_{i+1}$ and $\rho_{i+1}$ are the Lanczos vector, its normalization and the diagonal
Lanczos coefficient. -/
private theorem step_of_y (hH : H.IsHermitian) (hM : M.PosDef) (i : ℕ)
    (hi : toScaled hM (y (i + 1)) =
      if i = 0 then scaledGrad hM g
      else Arnoldi.w (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
        (i - 1)) :
    toScaled hM (q (i + 1)) =
        Arnoldi.vec (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g) i ∧
      γ (i + 1) = ‖if i = 0 then scaledGrad hM g
        else Arnoldi.w (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
          (i - 1)‖ ∧
      ρ (i + 1) =
        Lanczos.alpha (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
          (scaledGrad hM g) i := by
  set A := (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
  set b := scaledGrad hM g
  have hA : A.IsSymmetric := isSymmetric_scaledOp hH
  have hγ : γ (i + 1) = ‖if i = 0 then b else Arnoldi.w A b (i - 1)‖ := by
    rw [h.gamma_eq_norm hM (by omega), hi]
  have hqi : toScaled hM (q (i + 1)) = Arnoldi.vec A b i := by
    rw [h.q_eq _ (by omega), map_smul, hi, hγ]
    rcases i with _ | i
    · simp [vec_zero']
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
      rw [Arnoldi.vec_succ_eq]
      simp
  refine ⟨hqi, hγ, ?_⟩
  have hc := Lanczos.coe_alpha b hA i
  simp only [RCLike.ofReal_real_eq_id, id] at hc
  rw [hc, h.rho_eq _ (by omega), real_inner_comm, ← inner_scaledOp_toScaled, real_inner_comm, hqi]
  rfl

/-- **Algorithm 10.1.1** of [cartis2022evaluation], identification with the Lanczos process. Let $H$
be symmetric, $M$ symmetric positive definite, and consider a run of Algorithm 10.1.1. In the
$M$-inner product space, $y_{j+1}$ is $M^{-1} g$ for $j = 0$, and the unnormalized Lanczos
vector `Arnoldi.w` at index $j - 1$ of $M^{-1} H$ from $M^{-1} g$ for $j \ge 1$. -/
theorem toScaled_y (hH : H.IsHermitian) (hM : M.PosDef) (j : ℕ) :
    toScaled hM (y (j + 1)) =
      if j = 0 then scaledGrad hM g
      else Arnoldi.w (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
        (j - 1) := by
  set A := (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
  set b := scaledGrad hM g
  have hA : A.IsSymmetric := isSymmetric_scaledOp hH
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | i
    · rw [ite_eq_left rfl, h.y_eq 1 le_rfl, h.t_one]
      rfl
    · rw [h.y_succ hM (by omega : 1 ≤ i + 1), ite_eq_right (Nat.succ_ne_zero i),
        Nat.add_sub_cancel, map_sub, map_sub, map_smul, map_smul,
        ← scaledOp_toScaled]
      obtain ⟨hqi, -, hρi⟩ := h.step_of_y hH hM i (ih i (by omega))
      rw [hqi, hρi]
      rcases i with _ | i
      · rw [ite_eq_left rfl, map_zero, smul_zero, sub_zero, Arnoldi.w, Finset.sum_range_one]
        have hc := Lanczos.coe_alpha b hA 0
        simp only [RCLike.ofReal_real_eq_id, id] at hc
        rw [hc]
        rfl
      · rw [ite_eq_right (Nat.succ_ne_zero i)]
        obtain ⟨hqi', -, -⟩ := h.step_of_y hH hM i (ih i (by omega))
        obtain ⟨-, hγi, -⟩ := h.step_of_y hH hM (i + 1) (ih (i + 1) (by omega))
        rw [hqi', hγi, ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel]
        have hw := Lanczos.w_succ_eq b hA i
        simp only [RCLike.ofReal_real_eq_id, id] at hw
        rw [hw]
        rfl

/-- **Algorithm 10.1.1** of [cartis2022evaluation] computes the Lanczos vectors. Let $H$ be
symmetric and $M$ symmetric positive definite. In every run, the computed vector $q_k$ is the
Lanczos vector $q_k$ of (10.1.3) for every $k \ge 1$, that is,
`CartisGouldToint.Chapter10.lanczosVec hM H g (k - 1)`. -/
theorem q_eq_lanczosVec (hH : H.IsHermitian) (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) :
    q k = lanczosVec hM H g (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  apply (toScaled hM).injective
  rw [toScaled_lanczosVec, Nat.add_sub_cancel]
  exact (h.step_of_y hH hM j (h.toScaled_y hH hM j)).1

/-- **Equation (10.1.4)** of [cartis2022evaluation]. Let $H$ be symmetric and $M$ symmetric positive
definite. In every run of Algorithm 10.1.1, $\gamma_1 = \|g\|_{M^{-1}}$. -/
theorem gamma_one (hH : H.IsHermitian) (hM : M.PosDef) : γ 1 = mNorm M⁻¹ g := by
  rw [(h.step_of_y hH hM 0 (h.toScaled_y hH hM 0)).2.1, ite_eq_left rfl,
    mNorm_inv_eq_norm_scaledGrad hM]

/-- Let $H$ be symmetric and $M$ symmetric positive definite. In every run of Algorithm 10.1.1,
$\gamma_{k+1}$ is the off-diagonal Lanczos coefficient `Lanczos.beta` at the $0$-based index
$k - 1$, for $k \ge 1$. -/
theorem gamma_succ (hH : H.IsHermitian) (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) :
    γ (k + 1) =
      Lanczos.beta (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
        (k - 1) := by
  rw [(h.step_of_y hH hM k (h.toScaled_y hH hM k)).2.1, ite_eq_right (by omega)]
  rfl

/-- Let $H$ be symmetric and $M$ symmetric positive definite. In every run of Algorithm 10.1.1,
$\rho_k$ is the diagonal Lanczos coefficient `Lanczos.alpha` at the $0$-based index $k - 1$, for
$k \ge 1$. -/
theorem rho_eq_alpha (hH : H.IsHermitian) (hM : M.PosDef) {k : ℕ} (hk : 1 ≤ k) :
    ρ k = Lanczos.alpha (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) (scaledGrad hM g)
      (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact (h.step_of_y hH hM j (h.toScaled_y hH hM j)).2.2

end algorithm_10_1_1

/-- **Algorithm 10.1.1** of [cartis2022evaluation], properties of a run: (10.1.3)–(10.1.4),
(10.1.7), (10.2.1) and termination. Let $H$ be symmetric, $M$ symmetric positive definite and $1
\le k \le \operatorname{grade}(M^{-1} H, M^{-1} g)$, and consider any run of Algorithm 10.1.1.
Then:

* the columns of $Q_k$ are the computed vectors $q_1, \dots, q_k$;
* $Q_k^T M Q_k = I_k$;
* $Q_k^T H Q_k = T_k$, and $T_k$ is the symmetric tridiagonal matrix with diagonal
  $\rho_1, \dots, \rho_k$ and off-diagonal $\gamma_2, \dots, \gamma_k$;
* $Q_k^T g = \gamma_1 e_1$ with $\gamma_1 = \|g\|_{M^{-1}} > 0$, and $\gamma_i > 0$ for
  $2 \le i \le k$, so $T_k$ is unreduced;
* $H Q_k - M Q_k T_k = \gamma_{k+1} w_{k+1} e_k^T$ (10.2.1);
* the leading $(k-1) \times (k-1)$ block of $T_k$ is $T_{k-1}$ (10.1.7);
* $\gamma_{k+1} = 0$, so that the iteration stops after $k$ steps, if and only if
  $k = \operatorname{grade}(M^{-1} H, M^{-1} g)$.

**Typo.** The source prints the leading block of $T_k$ in (10.1.7) as $T_{k-1}^{-1}$. It is
$T_{k-1}$.

The grade is at most $n$ (`CartisGouldToint.Chapter10.gradeHM_le`), and at the grade
$\mathcal{K}_k$ is invariant under $M^{-1} H$
(`CartisGouldToint.Chapter10.krylovSpace_gradeHM_mem_invtSubmodule`). The tridiagonal matrix is
`Matrix.symTridiag`. -/
theorem algorithm_10_1_1_spec {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}
    {t y w q : ℕ → EuclideanSpace ℝ (Fin n)} {γ ρ : ℕ → ℝ} (hH : H.IsHermitian) (hM : M.PosDef)
    (h : algorithm_10_1_1 H M g t y w q γ ρ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ gradeHM H M g) :
    lanczosBasis hM H g k = Matrix.of (fun i (j : Fin k) => q (j + 1) i) ∧
    (lanczosBasis hM H g k)ᵀ * M * lanczosBasis hM H g k = 1 ∧
    ((lanczosBasis hM H g k)ᵀ * H * lanczosBasis hM H g k = lanczosTridiag hM H g k ∧
      lanczosTridiag hM H g k = symTridiag (fun i => ρ (i + 1)) (fun i => γ (i + 1)) k) ∧
    (toEuclideanLin (lanczosBasis hM H g k)ᵀ g = EuclideanSpace.single ⟨0, hk1⟩ (γ 1) ∧
      γ 1 = mNorm M⁻¹ g ∧ 0 < γ 1 ∧ ∀ i, 2 ≤ i → i ≤ k → 0 < γ i) ∧
    H * lanczosBasis hM H g k - M * lanczosBasis hM H g k * lanczosTridiag hM H g k =
      Matrix.of (fun a (j : Fin k) => if (j : ℕ) + 1 = k then γ (k + 1) * w (k + 1) a else 0) ∧
    (lanczosTridiag hM H g k).submatrix (Fin.castLE (Nat.sub_le k 1))
        (Fin.castLE (Nat.sub_le k 1)) = lanczosTridiag hM H g (k - 1) ∧
    (γ (k + 1) = 0 ↔ k = gradeHM H M g) := by
  set A := (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
  set b := scaledGrad hM g
  have hG : gradeHM H M g = Krylov.grade A b := gradeHM_eq hM
  have hb : b ≠ 0 := fun hb0 => by
    have : Krylov.grade A b = 0 := by rw [hb0]; exact Krylov.grade_zero A
    omega
  have hT : lanczosTridiag hM H g k = symTridiag (fun i => ρ (i + 1)) (fun i => γ (i + 1)) k := by
    rw [lanczosTridiag, Lanczos.tridiag_eq_symTridiag]
    ext i j
    rw [symTridiag_apply, symTridiag_apply, h.rho_eq_alpha hH hM (by omega : 1 ≤ (i : ℕ) + 1),
      Nat.add_sub_cancel]
    split_ifs with h1 h2 h3 <;> try rfl
    · rw [h.gamma_succ hH hM (by omega)]
    · rw [h.gamma_succ hH hM (by omega)]
  have hγpos : ∀ i, 2 ≤ i → i ≤ k → 0 < γ i := fun i hi2 hik => by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [h.gamma_succ hH hM (by omega)]
    refine lt_of_le_of_ne (Lanczos.beta_nonneg _ _ _) (Ne.symm ?_)
    rw [Ne, Lanczos.beta_eq_zero_iff]
    have := gradeHM_eq (H := H) (g := g) hM
    omega
  have hγ1 : γ 1 = mNorm M⁻¹ g := h.gamma_one hH hM
  refine ⟨?_, lanczosBasis_transpose_mul_M hM hk, ⟨lanczosBasis_transpose_mul_H hM hH, hT⟩,
    ⟨?_, hγ1, ?_, hγpos⟩, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.of_apply, lanczosBasis]
    rw [h.q_eq_lanczosVec hH hM (by omega), Nat.add_sub_cancel]
  · rw [hγ1]; exact lanczosGrad_eq hM hk1
  · rw [hγ1, mNorm_inv_eq_norm_scaledGrad hM]; exact norm_pos_iff.2 hb
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [lanczos_relation hM hH m]
    ext a j
    simp only [Matrix.of_apply, Nat.add_right_cancel_iff]
    rw [h.gamma_succ hH hM (by omega), Nat.add_sub_cancel, h.w_eq_M hM (by omega),
      h.q_eq_lanczosVec hH hM (by omega), Nat.add_sub_cancel]
    simp [Fin.ext_iff]
  · rw [lanczosTridiag, lanczosTridiag, Lanczos.tridiag_eq_symTridiag,
      Lanczos.tridiag_eq_symTridiag,
      symTridiag_submatrix_castLE]
  · rw [h.gamma_succ hH hM hk1, Lanczos.beta_eq_zero_iff, ← hG]
    omega

/-! ### The hard case (Section 10.1.2) -/

section HardCase

variable {H M : Matrix (Fin n) (Fin n) ℝ} {g : EuclideanSpace ℝ (Fin n)}

/-- For $M$ positive definite and $\mu \in \mathbb{R}$, the generalized eigenvectors $v$ with
$H v = \mu M v$ are, in the $M$-inner product space, the eigenvectors of the scaled operator
$M^{-1} H$ for $\mu$. -/
theorem map_toScaled_ker (hM : M.PosDef) (μ : ℝ) :
    (LinearMap.ker (toEuclideanLin (H - μ • M))).map
        (toScaled hM : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ScaledSpace hM) =
      Module.End.eigenspace (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM) μ := by
  ext x
  obtain ⟨v, rfl⟩ := (toScaled hM).surjective x
  rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, scaledOp_toScaled, ← map_smul]
  constructor
  · rintro ⟨u, hu, huv⟩
    rw [LinearEquiv.coe_coe] at huv
    rw [← (toScaled hM).injective huv]
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.sub_apply, sub_eq_zero, map_smul,
      LinearMap.smul_apply] at hu
    rw [hu, map_smul, toEuclideanLin_nonsing_inv_mul_apply hM.isUnit]
  · intro hv
    refine ⟨v, ?_, rfl⟩
    have hv' := congrArg (toEuclideanLin M) ((toScaled hM).injective hv)
    rw [toEuclideanLin_mul_nonsing_inv_apply hM.isUnit, map_smul] at hv'
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, hv',
      sub_self]

/-- **Section 10.1.2** of [cartis2022evaluation], the hard case defeats the Krylov subspaces. Let
$H$ be symmetric, $M$ symmetric positive definite, and $\lambda_1$ the leftmost eigenvalue of
the pencil $(H, M)$. Suppose the hard-case condition: $\langle v, g \rangle = 0$ for every $v$
with $H v = \lambda_1 M v$. Then:

* every $\mathcal{K}_k$ is $M$-orthogonal to the eigenspace of $\lambda_1$:
  $\langle v, M s \rangle = 0$ for all $s \in \mathcal{K}_k$ and all $v$ with
  $H v = \lambda_1 M v$;
* $\operatorname{grade}(M^{-1} H, M^{-1} g) + i_1 \le n$, where
  $i_1 = \dim \ker(H - \lambda_1 M)$ is the multiplicity of $\lambda_1$;
* every global minimizer of the trust-region or the regularization subproblem (10.1.1) on
  $\mathcal{K}_k$ is $M$-orthogonal to the eigenspace of $\lambda_1$.

So the Krylov subspaces lie in the span of the generalized eigenvectors for the other
eigenvalues. -/
theorem krylov_hardCase_10_1_2 (hH : H.IsHermitian) (hM : M.PosDef)
    (hhard : ∀ v, toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v → ⟪v, g⟫ = 0) :
    (∀ k, ∀ s ∈ krylovSpace H M g k, ∀ v,
        toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v →
          ⟪v, toEuclideanLin M s⟫ = 0) ∧
      gradeHM H M g + Module.finrank ℝ
          (LinearMap.ker (toEuclideanLin (H - leftmostPencil hH hM • M))) ≤ n ∧
      (∀ k Δ s, IsTRSubspaceSolution g H M Δ (krylovSpace H M g k) s → ∀ v,
        toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v →
          ⟪v, toEuclideanLin M s⟫ = 0) ∧
      (∀ k σ r s, IsRegSubspaceSolution g H M σ r (krylovSpace H M g k) s → ∀ v,
        toEuclideanLin H v = leftmostPencil hH hM • toEuclideanLin M v →
          ⟪v, toEuclideanLin M s⟫ = 0) := by
  set A := (scaledOp H hM : ScaledSpace hM →ₗ[ℝ] ScaledSpace hM)
  set b := scaledGrad hM g
  set μ := leftmostPencil hH hM
  set E₁ := Module.End.eigenspace A μ
  have hA : A.IsSymmetric := isSymmetric_scaledOp hH
  have hmemE : ∀ v, toEuclideanLin H v = μ • toEuclideanLin M v → toScaled hM v ∈ E₁ := by
    intro v hv
    rw [show E₁ = _ from (map_toScaled_ker hM μ).symm]
    refine ⟨v, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, hv,
      sub_self]
  -- `b ⟂ E₁` and `E₁ᗮ` is invariant
  have hb : b ∈ E₁ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [show E₁ = _ from (map_toScaled_ker hM μ).symm] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, LinearMap.sub_apply, sub_eq_zero, map_smul,
      LinearMap.smul_apply] at hv
    rw [LinearEquiv.coe_coe, inner_toScaled_scaledGrad]
    exact hhard v hv
  have hinv : E₁ᗮ ∈ Module.End.invtSubmodule A := by
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro e he
    rw [← hA, (Module.End.mem_eigenspace_iff.1 he), inner_smul_left, hx e he, mul_zero]
  have hfull : Krylov.fullSubspace A b ≤ E₁ᗮ :=
    Krylov.fullSubspace_le_of_mem_invtSubmodule A b hinv hb
  have hK : ∀ k, ∀ s ∈ krylovSpace H M g k, ∀ v,
      toEuclideanLin H v = μ • toEuclideanLin M v → ⟪v, toEuclideanLin M s⟫ = 0 := by
    intro k s hs v hv
    have hs' := hfull (Krylov.subspace_le_fullSubspace A b k ((toScaled_mem_krylov_iff hM).2 hs))
    have := (Submodule.mem_orthogonal _ _).1 hs' _ (hmemE v hv)
    rw [inner_toScaled] at this
    rw [← isSymmetric_toEuclideanLin_iff.2 hM.isHermitian v s]
    exact this
  refine ⟨hK, ?_, fun k Δ s hs => hK k s hs.1, fun k σ r s hs => hK k s hs.1⟩
  -- the grade
  have h1 : gradeHM H M g ≤ Module.finrank ℝ E₁ᗮ := by
    rw [gradeHM_eq hM]
    exact Submodule.finrank_mono hfull
  have h2 := Submodule.finrank_add_finrank_orthogonal E₁
  have h3 : Module.finrank ℝ E₁ =
      Module.finrank ℝ (LinearMap.ker (toEuclideanLin (H - μ • M))) := by
    rw [show E₁ = _ from (map_toScaled_ker hM μ).symm, LinearEquiv.finrank_map_eq]
  rw [finrank_scaledSpace, Fintype.card_fin] at h2
  omega

end HardCase

end CartisGouldToint.Chapter10
