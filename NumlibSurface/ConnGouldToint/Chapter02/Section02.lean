/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Matrix.SVD

/-!
# Conn, Gould and Toint, Section 2.2: Eigenvalues and eigenvectors

This module formalizes Section 2.2 of [conn2000trust]. For a square matrix $A$, an eigenpair
$(u, \mu)$ has $u \neq 0$ and $Au = \mu u$. A real symmetric matrix $H$ has a spectral decomposition
$H = U \Lambda U^T$ with $U$ orthogonal and $\Lambda$ the diagonal matrix of its eigenvalues, and
every real matrix $A$ has a singular value decomposition $A = U \Sigma V^T$. The section bounds the
eigenvalues of $H$ by Rayleigh quotients and by Gershgorin discs, defines generalized eigenpairs of
a pencil, and shows that $x = V \Sigma^+ U^T b$ is the minimum-norm least-squares solution of
$Ax = b$.

The proofs specialize Mathlib's spectral theorem `Matrix.IsHermitian.spectral_theorem` and
Gershgorin theorem `eigenvalue_mem_ball`, and the backbone modules `Numlib.Eigen.MinMax` and
`Numlib.LinearAlgebra.Matrix.SVD`.

## Main definitions

* Equation (2.2.1), `ConnGouldToint.Chapter02.IsEigenpair`: $u \neq 0$ and $Au = \mu u$.
* Equation (2.2.3), `ConnGouldToint.Chapter02.symmetricAbs`: the matrix $|H| = U |\Lambda| U^T$.
* Equation (2.2.7), `ConnGouldToint.Chapter02.IsGeneralizedEigenpair`: $u \neq 0$ and $Au = \mu Bu$.

## Main results

* Equation (2.2.2), `ConnGouldToint.Chapter02.spectral_decomposition_2_2_2`: a real symmetric matrix
  is $U \Lambda U^T$ with $U$ orthogonal.
* Equation (2.2.4), `ConnGouldToint.Chapter02.singular_value_decomposition_2_2_4`: a real matrix is
  $U \Sigma V^T$ with $U$, $V$ orthogonal and nonnegative, nonincreasing singular values.
* Equation (2.2.5), `ConnGouldToint.Chapter02.rayleigh_bounds_2_2_5`: the Rayleigh quotient of a
  nonzero vector lies between the least and the greatest eigenvalue.
* Prose before (2.2.6), `ConnGouldToint.Chapter02.gershgorin_union`: every eigenvalue lies in the
  union of the Gershgorin discs.
* Prose before (2.2.6), `ConnGouldToint.Chapter02.gershgorin_intersection_counterexample`: an
  eigenvalue need not lie in every Gershgorin disc.
* Equation (2.2.6), `ConnGouldToint.Chapter02.gershgorin_bounds_2_2_6`: the Gershgorin intervals
  bound the least and the greatest eigenvalue of a real symmetric matrix.
* Equation (2.2.8), `ConnGouldToint.Chapter02.svd_solution_2_2_8`: $V \Sigma^+ U^T b$ solves every
  consistent system $Ax = b$.
* Equation (2.2.8), `ConnGouldToint.Chapter02.svd_leastSquares_2_2_8`: $V \Sigma^+ U^T b$ is a
  least-squares solution of minimum norm.

## Conventions

* Matrices are indexed by `Fin n`.
* Let `hH : H.IsHermitian` for a real symmetric matrix $H$. Its eigenvalues $\lambda_i$ are
  `hH.eigenvalues`, and $\lambda_{\min}$ and $\lambda_{\max}$ are their infimum and supremum.
* Singular values are a function `σ : ℕ → ℝ`, and the matrix `Matrix.rectDiagonal σ` is $\Sigma$.
  The values $\sigma_i$ with $i \ge \min\{m, n\}$ are not entries of $\Sigma$.

## Deviations from the source

* **Prose before (2.2.6)** (correction). The source places each eigenvalue in the intersection of
  the Gershgorin discs. It lies in their union, and a diagonal $2 \times 2$ matrix has an eigenvalue
  outside one disc. See `ConnGouldToint.Chapter02.gershgorin_union` and
  `ConnGouldToint.Chapter02.gershgorin_intersection_counterexample`.
-/

open Matrix
open scoped Matrix

namespace ConnGouldToint.Chapter02

variable {m n : ℕ}

/-- **Equation (2.2.1)** of [conn2000trust]. Let $A \in \mathbb{K}^{n \times n}$ over a field
$\mathbb{K}$. A vector $u \in \mathbb{K}^n$ and a scalar $\mu \in \mathbb{K}$ form an
**eigenpair** of $A$ if $u \neq 0$ and $Au = \mu u$. -/
def IsEigenpair {𝕜 : Type*} [Field 𝕜] (A : Matrix (Fin n) (Fin n) 𝕜)
    (u : Fin n → 𝕜) (μ : 𝕜) : Prop :=
  u ≠ 0 ∧ A *ᵥ u = μ • u

/-- **Equation (2.2.2)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric with
eigenvalues $\lambda_1, \dots, \lambda_n$. Then there is an orthogonal matrix
$U \in \mathbb{R}^{n \times n}$ with
$$H = U \Lambda U^T, \qquad \Lambda = \operatorname{diag}(\lambda_1, \dots, \lambda_n).$$

The eigenvalues are `hH.eigenvalues`, and "orthogonal" is membership in `Matrix.unitaryGroup`.
The proof uses `Matrix.IsHermitian.spectral_theorem`. -/
theorem spectral_decomposition_2_2_2 {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℝ, H = U * diagonal hH.eigenvalues * Uᵀ := by
  refine ⟨hH.eigenvectorUnitary, hH.eigenvectorUnitary.property, ?_⟩
  simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    using hH.spectral_theorem

/-- **Equation (2.2.3)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric with
spectral decomposition $H = U \Lambda U^T$. The **absolute value** of $H$ is
$$|H| = U |\Lambda| U^T, \qquad |\Lambda| = \operatorname{diag}(|\lambda_1|, \dots,
  |\lambda_n|).$$

The orthogonal matrix $U$ is `hH.eigenvectorUnitary`, whose columns are the eigenvectors that
Mathlib chooses. -/
noncomputable def symmetricAbs {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) :
    Matrix (Fin n) (Fin n) ℝ :=
  (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
    diagonal (fun i => |hH.eigenvalues i|) * (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ

/-- **Equation (2.2.4)** of [conn2000trust] (singular value decomposition). Let
$A \in \mathbb{R}^{m \times n}$. Then there are orthogonal matrices
$U \in \mathbb{R}^{m \times m}$ and $V \in \mathbb{R}^{n \times n}$ and numbers
$\sigma_0 \ge \sigma_1 \ge \dots \ge 0$ with
$$A = U \Sigma V^T,$$
where $\Sigma \in \mathbb{R}^{m \times n}$ has the entries $\Sigma_{ii} = \sigma_i$ for
$i < \min\{m, n\}$ and zero entries elsewhere.

The sequence $\sigma$ is a nonincreasing nonnegative function `σ : ℕ → ℝ`, and $\Sigma$ is
`Matrix.rectDiagonal σ`. -/
theorem singular_value_decomposition_2_2_4 (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U ∈ Matrix.unitaryGroup (Fin m) ℝ, ∃ V ∈ Matrix.unitaryGroup (Fin n) ℝ,
      ∃ σ : ℕ → ℝ, Antitone σ ∧ (∀ i, 0 ≤ σ i) ∧
        A = U * (Matrix.rectDiagonal σ : Matrix (Fin m) (Fin n) ℝ) * Vᵀ := by
  obtain ⟨U, σ, V, h⟩ := A.exists_isSVD
  exact ⟨U, h.mem_unitaryGroup_left, V, h.mem_unitaryGroup_right, σ, h.antitone, h.nonneg,
    by simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h.eq_mul_mul_star⟩

/-- **Equation (2.2.5)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric with
$n \ge 1$, and let $p \in \mathbb{R}^n$ be nonzero. Then the Rayleigh quotient of $p$ lies
between the least and the greatest eigenvalue of $H$:
$$\lambda_{\min}(H) \le \frac{p^T H p}{p^T p} \le \lambda_{\max}(H).$$

The dimension is $n + 1$ in the Lean statement, so that the eigenvalues form a nonempty family.
The quotient is `ContinuousLinearMap.rayleighQuotient` of `Matrix.toEuclideanLin H`, and
$\lambda_{\min}$ and $\lambda_{\max}$ are the infimum and the supremum of `hH.eigenvalues`. -/
theorem rayleigh_bounds_2_2_5 {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : H.IsHermitian) {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ≠ 0) :
    (⨅ i, hH.eigenvalues i) ≤ H.toEuclideanLin.rayleighQuotient p ∧
      H.toEuclideanLin.rayleighQuotient p ≤ ⨆ i, hH.eigenvalues i := by
  let hT := isSymmetric_toEuclideanLin_iff.mpr hH
  have hr : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) =
      Fintype.card (Fin (n + 1)) := finrank_euclideanSpace
  have he (i : Fin (Fintype.card (Fin (n + 1)))) :
      hT.eigenvalues hr i = hH.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) i) := by
    simp [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀]
  refine ⟨hT.le_rayleighQuotient_of_forall hr (fun i => ?_) hp,
    hT.rayleighQuotient_le_of_forall hr (fun i => ?_) hp⟩
  · rw [he]
    exact ciInf_le (Set.finite_range _).bddBelow _
  · rw [he]
    exact le_ciSup (Set.finite_range _).bddAbove _

/-- **Section 2.2** of [conn2000trust], the prose before (2.2.6) (Gershgorin's disc theorem). Let
$A \in \mathbb{C}^{n \times n}$, and let $(u, \mu)$ be an eigenpair of $A$. Then $\mu$ lies in
at least one Gershgorin disc: there is an index $i$ with
$$|\mu - a_{ii}| \le \sum_{j \neq i} |a_{ij}|.$$

**Correction.** The source places each eigenvalue in the intersection of the discs. The correct
statement is the union, as here.
`ConnGouldToint.Chapter02.gershgorin_intersection_counterexample` shows that the intersection
claim is false.

The proof uses Mathlib's `eigenvalue_mem_ball`. -/
theorem gershgorin_union {A : Matrix (Fin n) (Fin n) ℂ} {u : Fin n → ℂ} {μ : ℂ}
    (h : IsEigenpair A u μ) :
    ∃ i, μ ∈ Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖) :=
  eigenvalue_mem_ball (Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 (by simpa [toLin'_apply] using h.2), h.1⟩)

/-- **Section 2.2** of [conn2000trust], the prose before (2.2.6), counterexample. There is a matrix
$A \in \mathbb{C}^{2 \times 2}$ with an eigenpair $(u, \mu)$ such that $\mu$ does not lie in
every Gershgorin disc of $A$, that is, $|\mu - a_{ii}| > \sum_{j \neq i} |a_{ij}|$ for some $i$.

This refutes the intersection claim of the source; see
`ConnGouldToint.Chapter02.gershgorin_union`. The witness is $A = \operatorname{diag}(0, 1)$ with
$u = e_1$ and $\mu = 0$: the second disc is the single point $1$. -/
theorem gershgorin_intersection_counterexample :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (u : Fin 2 → ℂ) (μ : ℂ),
      IsEigenpair A u μ ∧
        ¬ ∀ i, μ ∈ Metric.closedBall (A i i) (∑ j ∈ Finset.univ.erase i, ‖A i j‖) := by
  let d : Fin 2 → ℂ := ![0, 1]
  refine ⟨diagonal d, ![1, 0], 0, ⟨?_, ?_⟩, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 2)
    simp at h0
  · funext i
    rw [mulVec_diagonal]
    fin_cases i <;> simp [d]
  · intro h
    have h1 := h (1 : Fin 2)
    have hr : (∑ j ∈ Finset.univ.erase (1 : Fin 2),
        ‖(diagonal d) (1 : Fin 2) j‖) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      simp [Matrix.diagonal_apply_ne d (Finset.mem_erase.1 hj).1.symm]
    rw [hr, Metric.closedBall_zero, Set.mem_singleton_iff] at h1
    simp [d] at h1

/-- **Equation (2.2.6)** of [conn2000trust]. Let $H \in \mathbb{R}^{n \times n}$ be symmetric with
$n \ge 1$, and let $r_i = \sum_{j \neq i} |h_{ij}|$. Then
$$\min_i (h_{ii} - r_i) \le \lambda_{\min}(H) \le \lambda_{\max}(H) \le \max_i (h_{ii} + r_i).$$

The dimension is $n + 1$ in the Lean statement. The numbers $\lambda_{\min}$ and
$\lambda_{\max}$ are the infimum and the supremum of `hH.eigenvalues`. The proof applies
Gershgorin's theorem to each eigenvector. -/
theorem gershgorin_bounds_2_2_6 {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hH : H.IsHermitian) :
    let r (i : Fin (n + 1)) := ∑ j ∈ Finset.univ.erase i, |H i j|
    (⨅ i, H i i - r i) ≤ (⨅ i, hH.eigenvalues i) ∧
      (⨅ i, hH.eigenvalues i) ≤ (⨆ i, hH.eigenvalues i) ∧
      (⨆ i, hH.eigenvalues i) ≤ ⨆ i, H i i + r i := by
  dsimp only
  have hg (j : Fin (n + 1)) : ∃ i, |hH.eigenvalues j - H i i| ≤
      ∑ k ∈ Finset.univ.erase i, |H i k| := by
    have hne : ⇑(hH.eigenvectorBasis j) ≠ 0 := by
      intro h
      have hz : hH.eigenvectorBasis j = 0 := by
        ext i
        exact congrFun h i
      have hnorm := hH.eigenvectorBasis.norm_eq_one j
      simp [hz] at hnorm
    obtain ⟨i, hi⟩ := eigenvalue_mem_ball (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by
        simpa [toLin'_apply] using hH.mulVec_eigenvectorBasis j), hne⟩)
    exact ⟨i, by simpa [Metric.mem_closedBall, Real.dist_eq, Real.norm_eq_abs] using hi⟩
  refine ⟨le_ciInf fun j => ?_, ?_, ciSup_le fun j => ?_⟩
  · obtain ⟨i, hi⟩ := hg j
    exact (ciInf_le (Set.finite_range _).bddBelow i).trans (by linarith [(abs_le.1 hi).1])
  · exact (ciInf_le (Set.finite_range _).bddBelow 0).trans
      (le_ciSup (Set.finite_range _).bddAbove 0)
  · obtain ⟨i, hi⟩ := hg j
    exact (show hH.eigenvalues j ≤ _ from by linarith [(abs_le.1 hi).2]).trans
      (le_ciSup (Set.finite_range _).bddAbove i)

/-- **Equation (2.2.7)** of [conn2000trust]. Let $A, B \in \mathbb{K}^{n \times n}$ over a field
$\mathbb{K}$. A vector $u \in \mathbb{K}^n$ and a scalar $\mu \in \mathbb{K}$ form a
**generalized eigenpair** of the pencil $(A, B)$ if $u \neq 0$ and $Au = \mu Bu$. -/
def IsGeneralizedEigenpair {𝕜 : Type*} [Field 𝕜] (A B : Matrix (Fin n) (Fin n) 𝕜)
    (u : Fin n → 𝕜) (μ : 𝕜) : Prop :=
  u ≠ 0 ∧ A *ᵥ u = μ • (B *ᵥ u)

/-- **Equation (2.2.8)** of [conn2000trust], consistent systems. Let $A = U \Sigma V^T$ be a
singular value decomposition of $A \in \mathbb{R}^{m \times n}$, and let $b \in \mathbb{R}^m$ be
in the range of $A$. Then $x = V \Sigma^+ U^T b$ solves $Ax = b$, where
$\Sigma^+ \in \mathbb{R}^{n \times m}$ has the entries $1 / \sigma_i$ on the diagonal, with
$1 / 0 = 0$.

The decomposition is `Matrix.IsSVD A U σ V`. The matrix $\Sigma^+$ is
`Matrix.rectDiagonal fun i => (σ i)⁻¹`; Lean's convention $0^{-1} = 0$ gives the zero entries
that $\Sigma^+$ requires. -/
theorem svd_solution_2_2_8 {A : Matrix (Fin m) (Fin n) ℝ} {U V σ}
    (h : Matrix.IsSVD A U σ V) {b : Fin m → ℝ} (hb : ∃ x, A *ᵥ x = b) :
    A *ᵥ ((V * (Matrix.rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) * Uᵀ) *ᵥ b) =
      b := by
  have hp : A.pinv = V * (Matrix.rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) * Uᵀ :=
    by simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h.pinv_eq
  obtain ⟨x, rfl⟩ := hb
  rw [← hp, mulVec_mulVec, mulVec_mulVec, A.mul_pinv_mul_self]

/-- **Equation (2.2.8)** of [conn2000trust], least squares. Let $A = U \Sigma V^T$ be a singular
value decomposition of $A \in \mathbb{R}^{m \times n}$, let $b \in \mathbb{R}^m$, and let
$x = V \Sigma^+ U^T b$. Then

* $\|Ax - b\|_2 \le \|Ay - b\|_2$ for every $y \in \mathbb{R}^n$, and
* $\|x\|_2 \le \|y\|_2$ for every solution $y$ of the normal equations $A^T A y = A^T b$.

The system need not be consistent. The solutions of the normal equations are the least-squares
solutions, so $x$ is the least-squares solution of minimum norm. The matrix $\Sigma^+$ is as in
`ConnGouldToint.Chapter02.svd_solution_2_2_8`. The proof identifies $V \Sigma^+ U^T$ with the
pseudoinverse `Matrix.pinv`. -/
theorem svd_leastSquares_2_2_8 {A : Matrix (Fin m) (Fin n) ℝ} {U V σ}
    (h : Matrix.IsSVD A U σ V) (b : EuclideanSpace ℝ (Fin m)) :
    let x := Matrix.toEuclideanLin
      (V * (Matrix.rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) * Uᵀ) b
    (∀ y, ‖A.toEuclideanLin x - b‖ ≤ ‖A.toEuclideanLin y - b‖) ∧
      (∀ y, (Aᵀ * A).toEuclideanLin y = Aᵀ.toEuclideanLin b → ‖x‖ ≤ ‖y‖) := by
  have hp : A.pinv = V * (Matrix.rectDiagonal fun i => (σ i)⁻¹ : Matrix (Fin n) (Fin m) ℝ) * Uᵀ :=
    by simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using h.pinv_eq
  dsimp only
  rw [← hp]
  refine ⟨A.norm_toEuclideanLin_pinv_sub_le b, fun y hy => ?_⟩
  exact A.norm_pinv_le_of_normalEquations b (by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hy)

end ConnGouldToint.Chapter02
