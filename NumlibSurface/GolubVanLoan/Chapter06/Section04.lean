/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.PrincipalAngles
import Numlib.LinearAlgebra.Matrix.Polar
import Numlib.LinearAlgebra.Matrix.Procrustes
import NumlibSurface.GolubVanLoan.Chapter01.Section01
import NumlibSurface.GolubVanLoan.Chapter02.Section05
import NumlibSurface.GolubVanLoan.Chapter05.Section02
import NumlibSurface.GolubVanLoan.Chapter05.Section04
import NumlibSurface.GolubVanLoan.Chapter06.Section03

/-!
# Golub and Van Loan, Section 6.4: Subspace computations with the SVD

This module formalizes §6.4 of [golub2013matrix], which uses the SVD to compare and combine
subspaces. §6.4.1 solves the orthogonal Procrustes problem (6.4.1): for
$A, B \in \mathbb{R}^{m \times p}$, minimize $\|A - BQ\|_F$ over orthogonal $Q$. If
$U^T (B^T A) V = \Sigma$ is an SVD, then $Q = UV^T$ is a minimizer (Algorithm 6.4.1), and an SVD
$A = U \Sigma V^T$ gives the polar decomposition $A = (UV^T)(V \Sigma V^T)$. §6.4.2 computes an
orthonormal basis of $\operatorname{null}(A) \cap \operatorname{null}(B)$ from two SVDs (Theorem
6.4.1, Algorithm 6.4.2). §6.4.3 defines the principal angles $0 \le \theta_1 \le \dots \le \theta_q
\le \pi/2$ and the principal vectors between two subspaces $F$ and $G$ (6.4.3), shows that the
cosines $\cos\theta_i$ are the singular values of $Q_A^T Q_B$ for orthonormal bases $Q_A$ and $Q_B$,
and computes them by Algorithm 6.4.3. §6.4.4 shows that the principal vectors with
$\cos\theta_i = 1$ span $\operatorname{ran}(A) \cap \operatorname{ran}(B)$ (Theorem 6.4.2).

The proofs specialize `Numlib.LinearAlgebra.Matrix.Procrustes`, `Numlib.LinearAlgebra.Matrix.Polar`
and `Numlib.Analysis.InnerProductSpace.PrincipalAngles`, together with Mathlib's
`Submodule.map_comap_eq` and the subspace distance `GolubVanLoan.Chapter02.subspaceDist` of §2.5.

## Main definitions

* Algorithm 6.4.1, `GolubVanLoan.Chapter06.algorithm_6_4_1`: the orthogonal Procrustes problem.
* Algorithm 6.4.2, `GolubVanLoan.Chapter06.algorithm_6_4_2`: the intersection of null spaces.
* Algorithm 6.4.3, `GolubVanLoan.Chapter06.algorithm_6_4_3`: principal angles and vectors.

## Main results

* §6.4.1, `GolubVanLoan.Chapter06.procrustes_iff_trace`: for orthogonal $Q$, $\|A - BQ\|_F^2 =
  \|A\|_F^2 + \|B\|_F^2 - 2\operatorname{tr}(Q^T B^T A)$, so (6.4.1) is the maximization of
  $\operatorname{tr}(Q^T B^T A)$.
* Equation (6.4.2), `GolubVanLoan.Chapter06.equation_6_4_2`: $\operatorname{tr}(C_1^T C_2) =
  \operatorname{tr}(C_2^T C_1)$.
* §6.4.1, `GolubVanLoan.Chapter06.procrustes_solution`: $\operatorname{tr}(Q^T B^T A) \le \sum_i
  \sigma_i$, with equality at $Q = UV^T$, which solves (6.4.1).
* §6.4.1, `GolubVanLoan.Chapter06.procrustes_solution_of_isPolarDecomposition`: the orthogonal polar
  factor of $B^T A$ solves (6.4.1).
* Algorithm 6.4.1, `GolubVanLoan.Chapter06.algorithm_6_4_1_spec`: in exact arithmetic the algorithm
  returns a solution of (6.4.1).
* §6.4.1, `GolubVanLoan.Chapter06.polar_of_svd`: $A = (UV^T)(V \Sigma V^T)$ is a polar
  decomposition.
* Theorem 6.4.1, `GolubVanLoan.Chapter06.theorem_6_4_1`: the columns of $ZW$ form an orthonormal
  basis of $\operatorname{null}(A) \cap \operatorname{null}(B)$.
* §6.4.2, `GolubVanLoan.Chapter06.range_trailingColumns_eq_ker`: the trailing right singular vectors
  $V_A(:, r{+}1{:}n)$ span $\operatorname{null}(A)$.
* Algorithm 6.4.2, `GolubVanLoan.Chapter06.algorithm_6_4_2_spec`: in exact arithmetic the algorithm
  returns an orthonormal basis of $\operatorname{null}(A) \cap \operatorname{null}(B)$.
* Equation (6.4.3), `GolubVanLoan.Chapter06.equation_6_4_3`: the recursive definition of the
  principal angles and vectors is well posed.
* §6.4.3, `GolubVanLoan.Chapter06.principalAngle_mono`: $0 \le \theta_1 \le \dots \le \theta_q \le
  \pi/2$.
* §6.4.3, `GolubVanLoan.Chapter06.dist_eq_sin_principalAngle`: for subspaces of equal dimension $p$,
  $\operatorname{dist}(F, G) = \sqrt{1 - \cos(\theta_p)^2} = \sin(\theta_p)$.
* §6.4.3, `GolubVanLoan.Chapter06.singularValues_transpose_mul_eq_cosPrincipalAngle`: the singular
  values of $Q_A^T Q_B$ are the cosines $\cos\theta_i$, and they lie in $[0, 1]$.
* Equation (6.4.6), `GolubVanLoan.Chapter06.equation_6_4_6`: $(Q_A u)^T (Q_B v) = \sum_i \sigma_i
  (y_i^T u)(z_i^T v)$.
* §6.4.3, `GolubVanLoan.Chapter06.isPrincipalVectors_of_isSVD`: the SVD of $Q_A^T Q_B$ gives the
  principal angles and vectors.
* Algorithm 6.4.3, `GolubVanLoan.Chapter06.algorithm_6_4_3_spec`: in exact arithmetic the algorithm
  returns the cosines of the principal angles and principal vectors.
* Theorem 6.4.2, `GolubVanLoan.Chapter06.theorem_6_4_2`: $\operatorname{ran}(A) \cap
  \operatorname{ran}(B) = \operatorname{span}\{f_1, \dots, f_s\} = \operatorname{span}\{g_1, \dots,
  g_s\}$.

## Conventions

* Matrices are real and indices are 0-based. A subspace of $\mathbb{R}^m$ is a
  `Submodule ℝ (EuclideanSpace ℝ (Fin m))`. The range of $A$ is
  `LinearMap.range (toEuclideanLin A)`, and its null space is `LinearMap.ker (toEuclideanLin A)`.
  The null spaces of Theorem 6.4.1 and Algorithm 6.4.2 are those of `Matrix.mulVecLin`, which needs
  no Euclidean structure.
* "The columns of $Z$ are orthonormal" is `Zᵀ * Z = 1`.
* The Frobenius norm is the scoped `Matrix.Norms.Frobenius` norm, and the 2-norm is the scoped
  `Matrix.Norms.L2Operator` norm. Each is opened in the declarations that use it.
* An SVD is `Matrix.IsSVD A U σ V`, which says $U^T A V = \Sigma$ with the sorted diagonal $\sigma$.
* The principal angles and vectors are `Submodule.cosPrincipalAngle`, `Submodule.principalAngle` and
  `Submodule.IsPrincipalVectors`. They are 0-based: $\theta_{i+1}$ is
  `Submodule.principalAngle F G i`.

## Implementation notes

* Algorithms 6.4.1–6.4.3 follow the algorithm conventions of the library. The matrix products are
  `GolubVanLoan.Chapter01.algorithm_1_1_5`, which rounds every product and sum with `rnd`. The step
  "Compute the SVD" belongs to Chapter 8 and is a monadic parameter `svd`; the exact-arithmetic
  theorems assume that it returns an SVD.
* In Algorithm 6.4.2, the ranks $r = \operatorname{rank}(A)$ and $q = \operatorname{rank}(C)$ are
  the numbers of nonzero computed singular values, found by comparisons on the values the program
  holds. The column ranges are `GolubVanLoan.Chapter06.trailingColumns` of §6.3.
* In Algorithm 6.4.3, the thin QR factorizations are the Householder QR
  `GolubVanLoan.Chapter05.algorithm_5_2_1`. The orthogonal factor is accumulated forward from the
  returned reflector data by `GolubVanLoan.Chapter05.forwardAccumulation` and
  `GolubVanLoan.Chapter05.storedReflectors`, and its first columns (`Matrix.firstColumns`) are kept.

## Deviations from the source

* **§6.4.1, polar factor** (generalization). The orthogonal polar factor of $B^T A$ is a
  Procrustes minimizer for arbitrary $A$ and $B$. The source discusses the special case $B=I$.
  See `GolubVanLoan.Chapter06.procrustes_solution_of_isPolarDecomposition`.
* **Algorithm 6.4.2** (reading). Exact comparisons of computed singular values give the rank.
  The trivial intersection returns a zero-column matrix. See
  `GolubVanLoan.Chapter06.algorithm_6_4_2`.
* **Equation (6.4.3) and §6.4.3** (generalization). The recursive characterization includes the
  empty family. The cosine and singular-value equality is zero-extended beyond the available
  pairs and permits either dimension order. See `GolubVanLoan.Chapter06.equation_6_4_3` and
  `GolubVanLoan.Chapter06.singularValues_transpose_mul_eq_cosPrincipalAngle`.
* **Theorem 6.4.2** (reading). The initial run of unit cosines can be empty or include all
  indices. See `GolubVanLoan.Chapter06.theorem_6_4_2`.
* **Algorithm 6.4.3** (typo). The heading says that the algorithm computes the cosines of the
  principal angles $\theta_1 \ge \dots \ge \theta_q$. The order is reversed: the cosines decrease
  and the angles increase. See `GolubVanLoan.Chapter06.algorithm_6_4_3`.
* **§6.4.3** (typo). The source says that the subspaces lie in $\mathbb{R}^m$ but takes
  $A \in \mathbb{R}^{n \times p}$. The library takes $A \in \mathbb{R}^{m \times p}$. See
  `GolubVanLoan.Chapter06.algorithm_6_4_3`.
* **§6.4.3** (typo). The source writes "$v = Q_B z_1 = g_1$" where it means $g_1 = Q_B z_1$. See
  `GolubVanLoan.Chapter06.isPrincipalVectors_of_isSVD`.
* **Equation (6.4.6)** (generalization). The source states the identity for unit vectors $u$ and
  $v$. It holds for all $u$ and $v$. See `GolubVanLoan.Chapter06.equation_6_4_6`.
* **Theorem 6.4.2** (generalization). The source states the theorem for the principal vectors
  computed by Algorithm 6.4.3. It holds for any principal vectors of
  $(\operatorname{ran}(A), \operatorname{ran}(B))$. See `GolubVanLoan.Chapter06.theorem_6_4_2`.
-/

open Matrix

namespace GolubVanLoan.Chapter06

variable {m p : ℕ}

/-! ### §6.4.1 Rotation of subspaces -/

section Procrustes

open scoped Matrix.Norms.Frobenius

/-- **Section 6.4.1** of [golub2013matrix], the Procrustes expansion. Let
$A, B \in \mathbb{R}^{m \times p}$ and let $Q \in \mathbb{R}^{p \times p}$ be orthogonal. Then
$$\|A - BQ\|_F^2 = \|A\|_F^2 + \|B\|_F^2 - 2 \operatorname{tr}(Q^T (B^T A)).$$ Thus (6.4.1) is
equivalent to the problem $\max_{Q^T Q = I_p} \operatorname{tr}(Q^T B^T A)$: the matrix $Q$
minimizes $\|A - BQ'\|_F$ over all orthogonal $Q'$ if and only if it maximizes
$\operatorname{tr}(Q'^T B^T A)$ over all orthogonal $Q'$. -/
theorem procrustes_iff_trace {A B : Matrix (Fin m) (Fin p) ℝ} {Q : Matrix (Fin p) (Fin p) ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin p) ℝ) :
    ‖A - B * Q‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * trace (Qᵀ * (Bᵀ * A)) ∧
      ((∀ Q' ∈ orthogonalGroup (Fin p) ℝ, ‖A - B * Q‖ ≤ ‖A - B * Q'‖) ↔
        ∀ Q' ∈ orthogonalGroup (Fin p) ℝ, trace (Q'ᵀ * (Bᵀ * A)) ≤ trace (Qᵀ * (Bᵀ * A))) := by
  have key : ∀ Q' ∈ orthogonalGroup (Fin p) ℝ,
      ‖A - B * Q'‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * trace (Q'ᵀ * (Bᵀ * A)) := fun Q' hQ' => by
    have := frobenius_norm_sub_mul_sq hQ' A B
    simpa [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using this
  refine ⟨key Q hQ, forall₂_congr fun Q' hQ' => ?_⟩
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, key Q hQ, key Q' hQ']
  constructor <;> intro h <;> linarith

/-- **Equation (6.4.2)** of [golub2013matrix]. If $C_1, C_2 \in \mathbb{R}^{m \times n}$, then
$$\operatorname{tr}(C_1^T C_2) = \operatorname{tr}(C_2^T C_1).$$
-/
theorem equation_6_4_2 {n : ℕ} (C₁ C₂ : Matrix (Fin m) (Fin n) ℝ) :
    trace (C₁ᵀ * C₂) = trace (C₂ᵀ * C₁) := by
  rw [← trace_transpose, transpose_mul, transpose_transpose]

/-- If $U^T C V = \Sigma$ is an SVD of $C \in \mathbb{R}^{p \times p}$, then
$\operatorname{tr}((UV^T)^T C) = \sum_i \sigma_i$. -/
private theorem trace_mul_transpose_mul_eq_sum {C U V : Matrix (Fin p) (Fin p) ℝ} {σ : ℕ → ℝ}
    (h : IsSVD C U σ V) : trace ((U * Vᵀ)ᵀ * C) = ∑ i : Fin p, σ i := by
  have hS := h.star_mul_mul
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hS
  rw [transpose_mul, transpose_transpose, Matrix.mul_assoc, trace_mul_comm, hS]
  simp [trace, rectDiagonal_apply]

/-- **Section 6.4.1** of [golub2013matrix], the solution of the Procrustes problem. Let
$A, B \in \mathbb{R}^{m \times p}$, and let $U^T (B^T A) V = \Sigma =
\operatorname{diag}(\sigma_1, \dots, \sigma_p)$ be an SVD of $B^T A$. Then:

* $\operatorname{tr}(Q^T B^T A) \le \sum_{i=1}^p \sigma_i$ for every orthogonal
  $Q \in \mathbb{R}^{p \times p}$;
* the bound is attained at $Q = UV^T$;
* $UV^T$ is orthogonal;
* $Q = UV^T$ solves (6.4.1): $\|A - BUV^T\|_F \le \|A - BQ\|_F$ for every orthogonal $Q$.

The source proves the bound with the orthogonal matrix $Z = V^T Q^T U$: $\operatorname{tr}(Q^T
B^T A) = \operatorname{tr}(Z \Sigma) = \sum_i z_{ii} \sigma_i \le \sum_i \sigma_i$. -/
theorem procrustes_solution {A B : Matrix (Fin m) (Fin p) ℝ} {U V : Matrix (Fin p) (Fin p) ℝ}
    {σ : ℕ → ℝ} (h : IsSVD (Bᵀ * A) U σ V) :
    (∀ Q ∈ orthogonalGroup (Fin p) ℝ, trace (Qᵀ * (Bᵀ * A)) ≤ ∑ i : Fin p, σ i) ∧
      trace ((U * Vᵀ)ᵀ * (Bᵀ * A)) = ∑ i : Fin p, σ i ∧
      U * Vᵀ ∈ orthogonalGroup (Fin p) ℝ ∧
      ∀ Q ∈ orthogonalGroup (Fin p) ℝ, ‖A - B * (U * Vᵀ)‖ ≤ ‖A - B * Q‖ := by
  have hsum : ∑ i : Fin p, σ i = ∑ i, (Bᵀ * A).colSingularValues i := by
    rw [← trace_mul_transpose_mul_eq_sum h]
    have := h.re_trace_mul_eq_sum
    simpa [conjTranspose_eq_transpose_of_trivial, transpose_mul] using this
  have hB : Bᴴ * A = Bᵀ * A := by rw [conjTranspose_eq_transpose_of_trivial]
  obtain ⟨hmem, hmin⟩ := frobenius_norm_sub_mul_le_of_isSVD (hB ▸ h)
  rw [conjTranspose_eq_transpose_of_trivial] at hmem hmin
  refine ⟨fun Q hQ => ?_, trace_mul_transpose_mul_eq_sum h, hmem, hmin⟩
  have hQt : Qᵀ ∈ unitaryGroup (Fin p) ℝ := by
    rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
    exact Unitary.star_mem hQ
  have := re_trace_mul_le_sum_colSingularValues (Bᵀ * A) hQt
  rw [hsum]
  simpa using this

/-- **Section 6.4.1** of [golub2013matrix], the Procrustes solution as a polar factor. Let
$A, B \in \mathbb{R}^{m \times p}$, and let $B^T A = Q_0 P$ be a polar decomposition. Then $Q_0$
is orthogonal and solves (6.4.1): $\|A - BQ_0\|_F \le \|A - BQ\|_F$ for every orthogonal
$Q \in \mathbb{R}^{p \times p}$.

The source remarks that for $B = I_p$ the problem (6.4.1) is related to the polar decomposition;
the statement holds for every $B$. A polar decomposition is `Matrix.IsPolarDecomposition`.

**Generalization.** The source relates the problem to the polar decomposition when $B=I$. The
orthogonal polar factor of $B^T A$ minimizes the objective for arbitrary $A$ and $B$. -/
theorem procrustes_solution_of_isPolarDecomposition {A B : Matrix (Fin m) (Fin p) ℝ}
    {Q₀ P : Matrix (Fin p) (Fin p) ℝ} (h : IsPolarDecomposition (Bᵀ * A) Q₀ P) :
    Q₀ ∈ orthogonalGroup (Fin p) ℝ ∧
      ∀ Q ∈ orthogonalGroup (Fin p) ℝ, ‖A - B * Q₀‖ ≤ ‖A - B * Q‖ := by
  have hB : Bᴴ * A = Bᵀ * A := by rw [conjTranspose_eq_transpose_of_trivial]
  exact frobenius_norm_sub_mul_le_of_isPolarDecomposition (hB ▸ h)

end Procrustes

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 6.4.1** of [golub2013matrix] (orthogonal Procrustes). Given $A$ and $B$ in
$\mathbb{R}^{m \times p}$, the algorithm finds an orthogonal $Q \in \mathbb{R}^{p \times p}$
such that $\|A - BQ\|_F$ is minimum.
```
C = BᵀA
Compute the SVD UᵀCV = Σ and save U and V.
Q = UVᵀ
```
The products are `GolubVanLoan.Chapter01.algorithm_1_1_5`, started from the zero matrix. The
step "Compute the SVD" is the parameter `svd`, which returns $(U, \sigma, V)$. -/
def algorithm_6_4_1
    (svd : Matrix (Fin p) (Fin p) ℝ →
      M (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin p) (Fin p) ℝ))
    (A B : Matrix (Fin m) (Fin p) ℝ) : M (Matrix (Fin p) (Fin p) ℝ) := do
  let C ← Chapter01.algorithm_1_1_5 rnd Bᵀ A 0
  let USV ← svd C
  Chapter01.algorithm_1_1_5 rnd USV.1 USV.2.2ᵀ 0

end Programs

section ProcrustesAlgorithm

open scoped Matrix.Norms.Frobenius

/-- **Algorithm 6.4.1** of [golub2013matrix], exact arithmetic. Let
$A, B \in \mathbb{R}^{m \times p}$, and let `svd` return an SVD of every matrix. Then the output
$Q$ of the algorithm is orthogonal, and $\|A - BQ\|_F \le \|A - BQ'\|_F$ for every orthogonal
$Q' \in \mathbb{R}^{p \times p}$.

The run is at `M := Id` with `rnd := pure`. -/
theorem algorithm_6_4_1_spec
    (svd : Matrix (Fin p) (Fin p) ℝ →
      Id (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin p) (Fin p) ℝ))
    (hsvd : ∀ C, IsSVD C (Id.run (svd C)).1 (Id.run (svd C)).2.1 (Id.run (svd C)).2.2)
    (A B : Matrix (Fin m) (Fin p) ℝ) :
    Id.run (algorithm_6_4_1 pure svd A B) ∈ orthogonalGroup (Fin p) ℝ ∧
      ∀ Q ∈ orthogonalGroup (Fin p) ℝ,
        ‖A - B * Id.run (algorithm_6_4_1 pure svd A B)‖ ≤ ‖A - B * Q‖ := by
  have e : Id.run (algorithm_6_4_1 pure svd A B) =
      (Id.run (svd (Bᵀ * A))).1 * (Id.run (svd (Bᵀ * A))).2.2ᵀ := by
    simp only [algorithm_6_4_1]
    change Id.run (Chapter01.algorithm_1_1_5 pure
      (Id.run (svd (Id.run (Chapter01.algorithm_1_1_5 pure Bᵀ A 0)))).1
      (Id.run (svd (Id.run (Chapter01.algorithm_1_1_5 pure Bᵀ A 0)))).2.2ᵀ 0) = _
    rw [Chapter01.algorithm_1_1_5_spec, Chapter01.algorithm_1_1_5_spec, zero_add, zero_add]
  rw [e]
  obtain ⟨-, -, h1, h2⟩ := procrustes_solution (hsvd (Bᵀ * A))
  exact ⟨h1, h2⟩

end ProcrustesAlgorithm

/-- **Section 6.4.1** of [golub2013matrix], the polar decomposition from the SVD. If
$A = U \Sigma V^T$ is an SVD of $A \in \mathbb{R}^{n \times n}$, then $$A = (UV^T)(V \Sigma
V^T)$$ is a polar decomposition of $A$: $UV^T$ is orthogonal and $V \Sigma V^T$ is symmetric
positive semidefinite.

A polar decomposition is `Matrix.IsPolarDecomposition`. -/
theorem polar_of_svd {n : ℕ} {A U V : Matrix (Fin n) (Fin n) ℝ} {σ : ℕ → ℝ}
    (h : IsSVD A U σ V) :
    IsPolarDecomposition A (U * Vᵀ) (V * diagonal (fun i : Fin n => σ i) * Vᵀ) ∧
      U * Vᵀ ∈ orthogonalGroup (Fin n) ℝ := by
  have hp := h.isPolarDecomposition_of_square
  simp only [conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq] at hp
  exact ⟨hp, hp.mem_unitaryGroup⟩

/-! ### §6.4.2 Intersection of null spaces -/

/-- **Theorem 6.4.1** of [golub2013matrix]. Suppose $A \in \mathbb{R}^{m \times n}$ and
$B \in \mathbb{R}^{p \times n}$. Let $Z = [z_1 \mid \dots \mid z_t] \in \mathbb{R}^{n \times t}$
have orthonormal columns that span $\operatorname{null}(A)$, and let $W = [w_1 \mid \dots \mid
w_q] \in \mathbb{R}^{t \times q}$ have orthonormal columns that span $\operatorname{null}(BZ)$.
Then the columns of $ZW$ are orthonormal and span $\operatorname{null}(A) \cap
\operatorname{null}(B)$, so they form an orthonormal basis of this intersection.

The null spaces and ranges are those of `Matrix.mulVecLin`. -/
theorem theorem_6_4_1 {n t q : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {B : Matrix (Fin p) (Fin n) ℝ}
    {Z : Matrix (Fin n) (Fin t) ℝ} {W : Matrix (Fin t) (Fin q) ℝ} (hZ : Zᵀ * Z = 1)
    (hZA : LinearMap.range Z.mulVecLin = LinearMap.ker A.mulVecLin) (hW : Wᵀ * W = 1)
    (hWB : LinearMap.range W.mulVecLin = LinearMap.ker (B * Z).mulVecLin) :
    (Z * W)ᵀ * (Z * W) = 1 ∧
      LinearMap.range (Z * W).mulVecLin =
        LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
  refine ⟨?_, ?_⟩
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Zᵀ, hZ, Matrix.one_mul, hW]
  · rw [mulVecLin_mul, LinearMap.range_comp, hWB, mulVecLin_mul, LinearMap.ker_comp,
      Submodule.map_comap_eq, hZA]

section NullSpaces

/-- Let $\sigma$ be nonincreasing and nonnegative, and let $i < k$. Then $\sigma_i \neq 0$ if and
only if $i$ is less than `GolubVanLoan.Chapter05.deltaRank k 0 σ`, the numerical rank (5.4.5) at
$\delta = 0$. So this numerical rank is the number of nonzero values among the first $k$. -/
private theorem ne_zero_iff_lt_deltaRank {σ : ℕ → ℝ} (hσ : Antitone σ) (h0 : ∀ i, 0 ≤ σ i)
    {k i : ℕ} (hi : i < k) : σ i ≠ 0 ↔ i < Chapter05.deltaRank k 0 σ := by
  obtain ⟨-, h1, h2⟩ := Chapter05.deltaRank_spec (n := k) (δ := 0) hσ
  constructor
  · intro h
    by_contra hle
    exact h (le_antisymm (h2 i (not_lt.1 hle) hi) (h0 i))
  · intro h
    exact (h1 i h).ne'

/-- **Section 6.4.2** of [golub2013matrix], the null space from an SVD. Let
$U_A^T A V_A = \operatorname{diag}(\sigma_i)$ be an SVD of $A \in \mathbb{R}^{m \times n}$, and
let $r$ be the number of nonzero values among $\sigma_1, \dots, \sigma_{\min(m,n)}$. Then the
columns of $V_A(:, r{+}1{:}n)$ span $\operatorname{null}(A)$.

The number $r$ is `GolubVanLoan.Chapter05.deltaRank (min m n) 0 σ`, the columns are
`GolubVanLoan.Chapter06.trailingColumns`, and the range and null space are those of
`Matrix.mulVecLin`. -/
theorem range_trailingColumns_eq_ker {n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {σ : ℕ → ℝ} {V : Matrix (Fin n) (Fin n) ℝ}
    (h : IsSVD A U σ V) :
    LinearMap.range (trailingColumns V (Chapter05.deltaRank (min m n) 0 σ)).mulVecLin =
      LinearMap.ker A.mulVecLin := by
  have hr := (Chapter05.deltaRank_spec (n := min m n) (δ := 0) h.antitone).1
  have hset : ∀ j : Fin n,
      (m ≤ (j : ℕ) ∨ σ j = 0) ↔ Chapter05.deltaRank (min m n) 0 σ ≤ j := by
    intro j
    have hjn := j.isLt
    by_cases hj : (j : ℕ) < min m n
    · have hiff := ne_zero_iff_lt_deltaRank h.antitone h.nonneg hj
      constructor
      · rintro (hm | hz)
        · exact absurd hj (by have := min_le_left m n; omega)
        · by_contra hlt
          exact hiff.2 (by omega) hz
      · intro hle
        right
        by_contra hne
        have := hiff.1 hne
        omega
    · constructor
      · intro _
        omega
      · intro _
        left
        omega
  rw [range_mulVecLin, h.ker_mulVecLin_eq_span]
  congr 1
  ext w
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨⟨Chapter05.deltaRank (min m n) 0 σ + j, by have := j.isLt; omega⟩,
      (hset _).2 (by simp), ?_⟩
    rfl
  · rintro ⟨j, hj, rfl⟩
    have hle := (hset j).1 hj
    refine ⟨⟨j - Chapter05.deltaRank (min m n) 0 σ, by have := j.isLt; omega⟩, ?_⟩
    funext k
    change V k ⟨Chapter05.deltaRank (min m n) 0 σ + (↑j - Chapter05.deltaRank (min m n) 0 σ), _⟩ =
      V k j
    congr 1
    exact Fin.ext (by rw [Fin.val_mk]; omega)

/-- A matrix with no columns has the zero range. -/
private theorem range_mulVecLin_eq_bot {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) (hk : k = 0) :
    LinearMap.range Y.mulVecLin = ⊥ := by
  subst hk
  rw [range_mulVecLin, Set.range_eq_empty, Submodule.span_empty]

/-- If $Y \in \mathbb{R}^{n \times s}$ has orthonormal columns that span a subspace $K$, then
$s = \dim K$. -/
private theorem eq_finrank_of_range_eq {n s : ℕ} {Y : Matrix (Fin n) (Fin s) ℝ}
    {K : Submodule ℝ (Fin n → ℝ)} (hY : Yᵀ * Y = 1) (hK : LinearMap.range Y.mulVecLin = K) :
    s = Module.finrank ℝ K := by
  have hinj : Function.Injective Y.mulVecLin := fun x y hxy => by
    have := congrArg (Yᵀ *ᵥ ·) hxy
    simpa only [mulVecLin_apply, mulVec_mulVec, hY, one_mulVec] using this
  rw [← hK, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 6.4.2** of [golub2013matrix] (intersection of null spaces). Given
$A \in \mathbb{R}^{m \times n}$ and $B \in \mathbb{R}^{p \times n}$, the algorithm computes an
integer $s$ and a matrix $Y = [y_1 \mid \dots \mid y_s]$ with orthonormal columns that span
$\operatorname{null}(A) \cap \operatorname{null}(B)$. If the intersection is trivial, then
$s = 0$.
```
Compute the SVD U_Aᵀ A V_A = diag(σ_i), save V_A, and set r = rank(A).
if r < n
    C = B V_A(:, r+1:n)
    Compute the SVD U_Cᵀ C V_C = diag(γ_i), save V_C, and set q = rank(C).
    if q < n − r
        s = n − r − q
        Y = V_A(:, r+1:n) V_C(:, q+1:n−r)
    else
        s = 0
    end
else
    s = 0
end
```
The two SVDs are the parameters `svdA` and `svdC`; `svdC` takes the number of columns as an
argument. The ranks are the numbers of nonzero computed singular values,
`GolubVanLoan.Chapter05.deltaRank` at $\delta = 0$. The products are
`GolubVanLoan.Chapter01.algorithm_1_1_5`. The output is the pair $(s, Y)$.

**Reading.** Rank is the count of computed singular values different from zero. A trivial
intersection returns the zero-column matrix. The source discusses numerical rank without
prescribing a threshold. -/
noncomputable def algorithm_6_4_2 {n : ℕ}
    (svdA : Matrix (Fin m) (Fin n) ℝ →
      M (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (svdC : ∀ k, Matrix (Fin p) (Fin k) ℝ →
      M (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin k) (Fin k) ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin p) (Fin n) ℝ) :
    M (Σ s : ℕ, Matrix (Fin n) (Fin s) ℝ) := do
  let SA ← svdA A
  let r := Chapter05.deltaRank (min m n) 0 SA.2.1
  if r < n then
    let C ← Chapter01.algorithm_1_1_5 rnd B (trailingColumns SA.2.2 r) 0
    let SC ← svdC (n - r) C
    let q := Chapter05.deltaRank (min p (n - r)) 0 SC.2.1
    if q < n - r then
      let Y ← Chapter01.algorithm_1_1_5 rnd (trailingColumns SA.2.2 r)
        (trailingColumns SC.2.2 q) 0
      pure ⟨n - r - q, Y⟩
    else pure ⟨0, 0⟩
  else pure ⟨0, 0⟩

end Programs

/-- If a subspace $K$ is trivial, then the output $(0, 0)$ meets the specification of Algorithm
6.4.2: its columns are orthonormal, span $K$, and their number is $\dim K$. -/
private theorem spec_of_eq_zero {n : ℕ} {K : Submodule ℝ (Fin n → ℝ)} (hK : K = ⊥) {s : ℕ}
    {Y : Matrix (Fin n) (Fin s) ℝ} (h : (⟨0, 0⟩ : Σ s : ℕ, Matrix (Fin n) (Fin s) ℝ) = ⟨s, Y⟩) :
    Yᵀ * Y = 1 ∧ LinearMap.range Y.mulVecLin = K ∧ s = Module.finrank ℝ K := by
  subst hK
  obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.1 h
  obtain rfl := eq_of_heq h'.symm
  exact ⟨Subsingleton.elim _ _, range_mulVecLin_eq_bot _ rfl, by simp⟩

/-- **Algorithm 6.4.2** of [golub2013matrix], exact arithmetic. Let $A \in \mathbb{R}^{m \times n}$
and $B \in \mathbb{R}^{p \times n}$, and let `svdA` and `svdC` return an SVD of every matrix. If
the algorithm returns $(s, Y)$, then $Y^T Y = I$, the columns of $Y$ span
$\operatorname{null}(A) \cap \operatorname{null}(B)$, and $s = \dim(\operatorname{null}(A) \cap
\operatorname{null}(B))$. In particular, $s = 0$ exactly when the intersection is trivial.

The run is at `M := Id` with `rnd := pure`. The null spaces are those of `Matrix.mulVecLin`. -/
theorem algorithm_6_4_2_spec {n : ℕ}
    (svdA : Matrix (Fin m) (Fin n) ℝ →
      Id (Matrix (Fin m) (Fin m) ℝ × (ℕ → ℝ) × Matrix (Fin n) (Fin n) ℝ))
    (svdC : ∀ k, Matrix (Fin p) (Fin k) ℝ →
      Id (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin k) (Fin k) ℝ))
    (hA : ∀ A', IsSVD A' (Id.run (svdA A')).1 (Id.run (svdA A')).2.1 (Id.run (svdA A')).2.2)
    (hC : ∀ k (C : Matrix (Fin p) (Fin k) ℝ),
      IsSVD C (Id.run (svdC k C)).1 (Id.run (svdC k C)).2.1 (Id.run (svdC k C)).2.2)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin p) (Fin n) ℝ) {s : ℕ}
    {Y : Matrix (Fin n) (Fin s) ℝ} (hY : Id.run (algorithm_6_4_2 pure svdA svdC A B) = ⟨s, Y⟩) :
    Yᵀ * Y = 1 ∧
      LinearMap.range Y.mulVecLin = LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin ∧
      s = Module.finrank ℝ ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) := by
  have hsA := hA A
  simp only [algorithm_6_4_2, Id.run_bind] at hY
  generalize Id.run (svdA A) = SA at hY hsA
  generalize hr : Chapter05.deltaRank (min m n) 0 SA.2.1 = r at hY
  have hZ := trailingColumns_transpose_mul_self hsA.mem_unitaryGroup_right r
  have hZA := range_trailingColumns_eq_ker hsA
  rw [hr] at hZA
  split_ifs at hY with h1
  · simp only [Id.run_bind, Chapter01.algorithm_1_1_5_spec, zero_add] at hY
    have hsC := hC (n - r) (B * trailingColumns SA.2.2 r)
    generalize Id.run (svdC (n - r) (B * trailingColumns SA.2.2 r)) = SC at hY hsC
    generalize hq : Chapter05.deltaRank (min p (n - r)) 0 SC.2.1 = q at hY
    have hW := trailingColumns_transpose_mul_self hsC.mem_unitaryGroup_right q
    have hWB := range_trailingColumns_eq_ker hsC
    rw [hq] at hWB
    obtain ⟨hZW, hK⟩ := theorem_6_4_1 hZ hZA hW hWB
    split_ifs at hY with h2
    · simp only [Id.run_bind, Chapter01.algorithm_1_1_5_spec, zero_add] at hY
      obtain ⟨rfl, h'⟩ := Sigma.mk.inj_iff.1 hY
      obtain rfl := eq_of_heq h'.symm
      exact ⟨hZW, hK, eq_finrank_of_range_eq hZW hK⟩
    · refine spec_of_eq_zero ?_ hY
      rw [← hK]
      exact range_mulVecLin_eq_bot _ (by omega)
  · refine spec_of_eq_zero ?_ hY
    rw [← hZA, range_mulVecLin_eq_bot _ (by omega), bot_inf_eq]

end NullSpaces

/-! ### §6.4.3 Angles between subspaces -/

section Angles

variable (F G : Submodule ℝ (EuclideanSpace ℝ (Fin m)))

/-- **Equation (6.4.3)** of [golub2013matrix]. Let $F$ and $G$ be subspaces of $\mathbb{R}^m$ with
$q = \dim G \le \dim F$. The principal angles $\theta_k$ between $F$ and $G$ and the principal
vectors $f_k, g_k$ are defined recursively by $$\cos(\theta_k) = f_k^T g_k = \max_{\substack{f
\in F,\ \|f\|_2 = 1 \\ f^T [f_1, \dots, f_{k-1}] = 0}} \ \max_{\substack{g \in G,\ \|g\|_2 = 1
\\ g^T [g_1, \dots, g_{k-1}] = 0}} f^T g.$$ The theorem says that this definition is well posed:

* principal vectors $f_1, \dots, f_q$ and $g_1, \dots, g_q$ exist;
* for any principal vectors, $\cos\theta_k$ is the maximum of the $k$-th step of the recursion,
  and it is attained at $(f_k, g_k)$;
* any sequence of unit vectors produced by the recursion satisfies $f_k^T g_k = \cos\theta_k$,
  so the recursion determines the angles whatever maximizers it chooses.

The cosines are `Submodule.cosPrincipalAngle`, the singular values of the projection onto $F$
restricted to $G$. Principal vectors are `Submodule.IsPrincipalVectors`: $g$ is an orthonormal
basis of $G$, $f$ is orthonormal in $F$, and the projection of $g_k$ onto $F$ is
$\cos\theta_k \, f_k$. A sequence produced by the recursion is
`Submodule.IsRecursivePrincipalVectors`.

**Generalization.** The recursive specification permits the empty list of angle and vector
pairs when $\dim G=0$. -/
theorem equation_6_4_3 (h : Module.finrank ℝ G ≤ Module.finrank ℝ F) :
    (∃ f g : Fin (Module.finrank ℝ G) → EuclideanSpace ℝ (Fin m), F.IsPrincipalVectors G f g) ∧
      (∀ {q : ℕ} {f g : Fin q → EuclideanSpace ℝ (Fin m)}, F.IsPrincipalVectors G f g →
        ∀ k : Fin q, IsGreatest {r : ℝ | ∃ u ∈ F, ∃ v ∈ G, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
          (∀ i < k, inner ℝ (f i) u = 0) ∧ (∀ i < k, inner ℝ (g i) v = 0) ∧ inner ℝ u v = r}
          (F.cosPrincipalAngle G k)) ∧
      ∀ {q : ℕ} {f g : Fin q → EuclideanSpace ℝ (Fin m)}, F.IsRecursivePrincipalVectors G f g →
        ∀ k : Fin q, inner ℝ (f k) (g k) = F.cosPrincipalAngle G k := by
  refine ⟨F.exists_isPrincipalVectors G h, fun hfg k => ?_, fun hfg k => ?_⟩
  · simpa using hfg.isGreatest_re_inner k
  · simpa using F.cosPrincipalAngle_eq_of_isRecursivePrincipalVectors G h hfg k

/-- **Section 6.4.3** of [golub2013matrix]. The principal angles between two subspaces $F$ and $G$
satisfy $$0 \le \theta_1 \le \dots \le \theta_q \le \pi/2.$$

The statement says that `Submodule.principalAngle F G` is monotone and that every value lies in
$[0, \pi/2]$. Beyond the dimension of $G$ the cosine is $0$ and the angle is $\pi/2$. -/
theorem principalAngle_mono :
    Monotone (F.principalAngle G) ∧ ∀ i, F.principalAngle G i ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨F.monotone_principalAngle G, F.principalAngle_mem_Icc G⟩

/-- **Section 6.4.3** of [golub2013matrix], the distance of subspaces of equal dimension. Let $F$
and $G$ be subspaces of $\mathbb{R}^m$ with $\dim F = \dim G = p \ge 1$. Then
$$\operatorname{dist}(F, G) = \sqrt{1 - \cos(\theta_p)^2} = \sin(\theta_p).$$

The distance is the subspace distance `GolubVanLoan.Chapter02.subspaceDist` of §2.5.3. The
hypothesis is stated as $\dim F = \dim G = q + 1$, and $\theta_p$ has the 0-based index $q$. -/
theorem dist_eq_sin_principalAngle {q : ℕ} (hF : Module.finrank ℝ F = q + 1)
    (hG : Module.finrank ℝ G = q + 1) :
    Chapter02.subspaceDist F G = Real.sqrt (1 - F.cosPrincipalAngle G q ^ 2) ∧
      Chapter02.subspaceDist F G = Real.sin (F.principalAngle G q) := by
  have h := F.gap_eq_sin_principalAngle G hF hG
  refine ⟨?_, h⟩
  rw [Chapter02.subspaceDist, h, Submodule.principalAngle, Real.sin_arccos]

end Angles

section Matrices

variable {q : ℕ}

open scoped Matrix.Norms.L2Operator in
/-- **Section 6.4.3** of [golub2013matrix], the singular values of $Q_A^T Q_B$. Let
$Q_A \in \mathbb{R}^{m \times p}$ and $Q_B \in \mathbb{R}^{m \times q}$ have orthonormal
columns, as the orthogonal factors of thin QR factorizations $A = Q_A R_A$ and $B = Q_B R_B$.
Then $\|Q_A^T Q_B\|_2 \le 1$, and for every $i$ the $i$-th singular value $\sigma_i$ of
$Q_A^T Q_B$ is the cosine $\cos(\theta_i)$ of the $i$-th principal angle between
$\operatorname{ran}(Q_A)$ and $\operatorname{ran}(Q_B)$, with $0 \le \sigma_i \le 1$.

The singular values are `LinearMap.singularValues` of `toEuclideanLin (QAᵀ * QB)`, 0-based, and
the equality holds for every index $i$.

**Generalization.** Either subspace may be the larger one. The equality uses the total
sequences of angle cosines and singular values, including their zero extension past the
available pairs. -/
theorem singularValues_transpose_mul_eq_cosPrincipalAngle {QA : Matrix (Fin m) (Fin p) ℝ}
    {QB : Matrix (Fin m) (Fin q) ℝ}
    (hA : QAᵀ * QA = 1) (hB : QBᵀ * QB = 1) :
    ‖QAᵀ * QB‖ ≤ 1 ∧ ∀ i : ℕ,
      (LinearMap.range (toEuclideanLin QA)).cosPrincipalAngle
          (LinearMap.range (toEuclideanLin QB)) i =
        (toEuclideanLin (QAᵀ * QB)).singularValues i ∧
      0 ≤ (toEuclideanLin (QAᵀ * QB)).singularValues i ∧
      (toEuclideanLin (QAᵀ * QB)).singularValues i ≤ 1 := by
  have hA' : QAᴴ * QA = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hB' : QBᴴ * QB = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  refine ⟨?_, fun i => ?_⟩
  · calc ‖QAᵀ * QB‖ ≤ ‖QAᵀ‖ * ‖QB‖ := l2_opNorm_mul _ _
      _ ≤ 1 * 1 := by
          rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]
          exact mul_le_mul (l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hA')
            (l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hB') (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have e := Submodule.cosPrincipalAngle_eq_singularValues hA' hB' i
    rw [conjTranspose_eq_transpose_of_trivial] at e
    refine ⟨e, ?_, ?_⟩
    · rw [← e]; exact Submodule.cosPrincipalAngle_nonneg _ _ i
    · rw [← e]; exact Submodule.cosPrincipalAngle_le_one _ _ i

/-- **Equation (6.4.6)** of [golub2013matrix]. Let $Q_A \in \mathbb{R}^{m \times p}$ and
$Q_B \in \mathbb{R}^{m \times q}$ with $q \le p$, and let $Y^T (Q_A^T Q_B) Z = \Sigma$ be an SVD
with $Y = [y_1 \mid \dots \mid y_p]$ and $Z = [z_1 \mid \dots \mid z_q]$. Then for all
$u \in \mathbb{R}^p$ and $v \in \mathbb{R}^q$, with $f = Q_A u$ and $g = Q_B v$, $$f^T g = u^T
(Q_A^T Q_B) v = (Y^T u)^T \Sigma (Z^T v) = \sum_{i=1}^q \sigma_i (y_i^T u)(z_i^T v).$$

**Generalization.** The source takes unit vectors $f \in F$ and $g \in G$, written as
$f = Q_A u$ and $g = Q_B v$ with unit vectors $u$ and $v$. The identity holds for all $u$ and
$v$, and it needs no hypothesis on the columns of $Q_A$ and $Q_B$. -/
theorem equation_6_4_6 {QA : Matrix (Fin m) (Fin p) ℝ} {QB : Matrix (Fin m) (Fin q) ℝ}
    (hqp : q ≤ p) {Y : Matrix (Fin p) (Fin p) ℝ} {σ : ℕ → ℝ} {Z : Matrix (Fin q) (Fin q) ℝ}
    (h : IsSVD (QAᵀ * QB) Y σ Z) (u : Fin p → ℝ) (v : Fin q → ℝ) :
    (QA *ᵥ u) ⬝ᵥ (QB *ᵥ v) =
      ∑ i : Fin q, σ i * (Y.col (Fin.castLE hqp i) ⬝ᵥ u) * (Z.col i ⬝ᵥ v) := by
  have hC := h.eq_mul_mul_star
  simp only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, id_eq] at hC
  rw [← vecMul_transpose, dotProduct_mulVec, vecMul_vecMul, hC, ← vecMul_vecMul, ← vecMul_vecMul,
    ← dotProduct_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hS : (u ᵥ* Y ᵥ* (rectDiagonal σ : Matrix (Fin p) (Fin q) ℝ)) j =
      (u ᵥ* Y) (Fin.castLE hqp j) * σ j := by
    rw [vecMul, dotProduct, Finset.sum_eq_single (Fin.castLE hqp j)]
    · simp [rectDiagonal_apply]
    · intro i _ hi
      rw [rectDiagonal_apply, ite_eq_right (fun hij => hi (Fin.ext (by simpa using hij))),
        mul_zero]
    · simp
  rw [hS]
  have e1 : (u ᵥ* Y) (Fin.castLE hqp j) = Y.col (Fin.castLE hqp j) ⬝ᵥ u := by
    simp only [vecMul, dotProduct, col_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have e2 : (Zᵀ *ᵥ v) j = Z.col j ⬝ᵥ v := by
    simp only [mulVec, dotProduct, col_apply, transpose_apply]
  rw [e1, e2]
  ring

end Matrices

section PrincipalAnglesAlgorithm

variable {q : ℕ}

section Programs

variable {M : Type → Type} [Monad M] (rnd : ℝ → M ℝ)

/-- **Algorithm 6.4.3** of [golub2013matrix] (principal angles and vectors). Given
$A \in \mathbb{R}^{m \times p}$ and $B \in \mathbb{R}^{m \times q}$ with $p \ge q$, each with
linearly independent columns, the algorithm computes the cosines of the principal angles
$\theta_1 \le \dots \le \theta_q$ between $\operatorname{ran}(A)$ and $\operatorname{ran}(B)$.
The vectors $f_1, \dots, f_q$ and $g_1, \dots, g_q$ are the associated principal vectors.
```
Compute the thin QR factorizations A = Q_A R_A and B = Q_B R_B.
C = Q_Aᵀ Q_B
Compute the SVD YᵀCZ = diag(cos(θ_k)).
Q_A Y(:, 1:q) = [f₁ | ⋯ | f_q]
Q_B Z(:, 1:q) = [g₁ | ⋯ | g_q]
```

**Typo.** The source writes the angles as $\theta_1 \ge \dots \ge \theta_q$. The order is
reversed because the cosines decrease and the angles increase. The source gives the ambient
space as $\mathbb{R}^m$ and the dimensions of $A$ as $n \times p$. The algorithm takes
$A \in \mathbb{R}^{m \times p}$.

The thin QR factorizations are the Householder QR `GolubVanLoan.Chapter05.algorithm_5_2_1`. The
orthogonal factor is accumulated forward from the returned reflector data and the returned
$\beta$ by `GolubVanLoan.Chapter05.forwardAccumulation` and
`GolubVanLoan.Chapter05.storedReflectors`, and its first $p$ (or $q$) columns are kept. The
products are `GolubVanLoan.Chapter01.algorithm_1_1_5`, and the step "Compute the SVD" is the
parameter `svd`. The output is the diagonal that `svd` returns and the matrices
$[f_1 \mid \dots \mid f_q]$ and $[g_1 \mid \dots \mid g_q]$. The shape conditions
$q \le p \le m$, which follow from the independence of the columns, are explicit arguments. -/
noncomputable def algorithm_6_4_3
    (svd : Matrix (Fin p) (Fin q) ℝ →
      M (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin q) (Fin q) ℝ))
    (hqp : q ≤ p) (hpm : p ≤ m) (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin q) ℝ) :
    M ((ℕ → ℝ) × Matrix (Fin m) (Fin q) ℝ × Matrix (Fin m) (Fin q) ℝ) := do
  let RA ← Chapter05.algorithm_5_2_1 rnd A
  let QA ← Chapter05.forwardAccumulation rnd (Chapter05.storedReflectors RA.1 RA.2)
  let RB ← Chapter05.algorithm_5_2_1 rnd B
  let QB ← Chapter05.forwardAccumulation rnd (Chapter05.storedReflectors RB.1 RB.2)
  let C ← Chapter01.algorithm_1_1_5 rnd (firstColumns QA hpm)ᵀ
    (firstColumns QB (hqp.trans hpm)) 0
  let S ← svd C
  let F ← Chapter01.algorithm_1_1_5 rnd (firstColumns QA hpm) (firstColumns S.1 hqp) 0
  let G ← Chapter01.algorithm_1_1_5 rnd (firstColumns QB (hqp.trans hpm)) S.2.2 0
  pure (S.2.1, F, G)

end Programs

/-- If $N^T N = I$, then the columns of $N$ are orthonormal vectors of Euclidean space. -/
private theorem orthonormal_toLp_col {k : ℕ} {N : Matrix (Fin m) (Fin k) ℝ} (hN : Nᵀ * N = 1) :
    Orthonormal ℝ fun j => (WithLp.toLp 2 (N.col j) : EuclideanSpace ℝ (Fin m)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrFun (congrFun hN i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [col_apply, mul_comm]

/-- If the range of $N$ is contained in the range of $N'$ as maps on coordinate vectors, then the
same holds for the Euclidean operators of $N$ and $N'$. -/
private theorem range_toEuclideanLin_le_of_range_mulVecLin_le {k l : ℕ}
    {N : Matrix (Fin m) (Fin k) ℝ} {N' : Matrix (Fin m) (Fin l) ℝ}
    (h : LinearMap.range N.mulVecLin ≤ LinearMap.range N'.mulVecLin) :
    LinearMap.range (toEuclideanLin N) ≤ LinearMap.range (toEuclideanLin N') := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := h ⟨WithLp.ofLp x, rfl⟩
  refine ⟨WithLp.toLp 2 y, ?_⟩
  rw [toEuclideanLin_toLp, toEuclideanLin_apply]
  exact congrArg _ hy

/-- Let $N = QR$ be a QR factorization of $N \in \mathbb{R}^{m \times k}$ with linearly independent
columns. Then the first $k$ columns of $Q$ span the range of $N$. -/
private theorem range_toEuclideanLin_firstColumns {k : ℕ} {N : Matrix (Fin m) (Fin k) ℝ}
    {Q : Matrix (Fin m) (Fin m) ℝ} {R : Matrix (Fin m) (Fin k) ℝ} (h : IsQR N Q R) (hkm : k ≤ m)
    (hN : LinearIndependent ℝ Nᵀ) :
    LinearMap.range (toEuclideanLin (firstColumns Q hkm)) = LinearMap.range (toEuclideanLin N) := by
  have hr : LinearMap.range (firstColumns Q hkm).mulVecLin = LinearMap.range N.mulVecLin := by
    rw [range_mulVecLin, range_mulVecLin]
    exact h.span_firstColumns_eq hkm hN
  exact le_antisymm (range_toEuclideanLin_le_of_range_mulVecLin_le hr.le)
    (range_toEuclideanLin_le_of_range_mulVecLin_le hr.ge)

/-- **Section 6.4.3** of [golub2013matrix], the SVD step of Algorithm 6.4.3. Let
$Q_A \in \mathbb{R}^{m \times p}$ and $Q_B \in \mathbb{R}^{m \times q}$ have orthonormal
columns, with $q \le p$, and let $F = \operatorname{ran}(Q_A)$ and
$G = \operatorname{ran}(Q_B)$. Let $Y^T (Q_A^T Q_B) Z = \Sigma = \operatorname{diag}(\sigma_1,
\dots, \sigma_q)$ be an SVD. Then $\sigma_k = \cos(\theta_k)$ for $k = 1, \dots, q$, and the
columns $f_k$ of $Q_A Y(:, 1{:}q)$ and $g_k$ of $Q_B Z$ are principal vectors of $(F, G)$.

**Typo.** The source writes "$v = Q_B z_1 = g_1$" where it means $g_1 = Q_B z_1$.

Principal vectors are `Submodule.IsPrincipalVectors`. The statement specializes
`Submodule.cosPrincipalAngle_eq_of_isSVD` and `Submodule.isPrincipalVectors_of_isSVD`. -/
theorem isPrincipalVectors_of_isSVD {QA : Matrix (Fin m) (Fin p) ℝ}
    {QB : Matrix (Fin m) (Fin q) ℝ} (hA : QAᵀ * QA = 1) (hB : QBᵀ * QB = 1) (hqp : q ≤ p)
    {F G : Submodule ℝ (EuclideanSpace ℝ (Fin m))} (hF : LinearMap.range (toEuclideanLin QA) = F)
    (hG : LinearMap.range (toEuclideanLin QB) = G)
    {Y : Matrix (Fin p) (Fin p) ℝ} {σ : ℕ → ℝ} {Z : Matrix (Fin q) (Fin q) ℝ}
    (h : IsSVD (QAᵀ * QB) Y σ Z) :
    (∀ k < q, σ k = F.cosPrincipalAngle G k) ∧
    F.IsPrincipalVectors G
      (fun k => (WithLp.toLp 2 ((QA * firstColumns Y hqp).col k) : EuclideanSpace ℝ (Fin m)))
      (fun k => (WithLp.toLp 2 ((QB * Z).col k) : EuclideanSpace ℝ (Fin m))) := by
  subst hF hG
  have hA' : QAᴴ * QA = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hB' : QBᴴ * QB = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have h' : IsSVD (QAᴴ * QB) Y σ Z := by rwa [conjTranspose_eq_transpose_of_trivial]
  exact ⟨fun k hk => (Submodule.cosPrincipalAngle_eq_of_isSVD hA' hB' h' (by omega) hk).symm,
    Submodule.isPrincipalVectors_of_isSVD hA' hB' hqp h'⟩

/-- **Algorithm 6.4.3** of [golub2013matrix], exact arithmetic. Let $A \in \mathbb{R}^{m \times p}$
and $B \in \mathbb{R}^{m \times q}$ with $q \le p \le m$ have linearly independent columns, and
let `svd` return an SVD of every matrix. If the algorithm returns $(c, F, G)$, then
$c_k = \cos(\theta_k)$ for $k = 1, \dots, q$, and the columns of $F$ and $G$ are principal
vectors of $(\operatorname{ran}(A), \operatorname{ran}(B))$: they are orthonormal, they lie in
the two ranges, and the projection of $g_k$ onto $\operatorname{ran}(A)$ is
$\cos(\theta_k) f_k$.

The run is at `M := Id` with `rnd := pure`. The Householder QR factorizations of Chapter 5 need
no further hypothesis. The index $k$ is 0-based in the Lean statement.

**Correction.** Correct cosines and vectors, ordering fixed via the SVD.
-/
theorem algorithm_6_4_3_spec
    (svd : Matrix (Fin p) (Fin q) ℝ →
      Id (Matrix (Fin p) (Fin p) ℝ × (ℕ → ℝ) × Matrix (Fin q) (Fin q) ℝ))
    (hsvd : ∀ C, IsSVD C (Id.run (svd C)).1 (Id.run (svd C)).2.1 (Id.run (svd C)).2.2)
    (hqp : q ≤ p) (hpm : p ≤ m) {A : Matrix (Fin m) (Fin p) ℝ} {B : Matrix (Fin m) (Fin q) ℝ}
    (hA : LinearIndependent ℝ Aᵀ) (hB : LinearIndependent ℝ Bᵀ) :
    (∀ k < q, (Id.run (algorithm_6_4_3 pure svd hqp hpm A B)).1 k =
      (LinearMap.range (toEuclideanLin A)).cosPrincipalAngle
        (LinearMap.range (toEuclideanLin B)) k) ∧
    (LinearMap.range (toEuclideanLin A)).IsPrincipalVectors (LinearMap.range (toEuclideanLin B))
      (fun k => (WithLp.toLp 2 ((Id.run (algorithm_6_4_3 pure svd hqp hpm A B)).2.1.col k) :
        EuclideanSpace ℝ (Fin m)))
      (fun k => (WithLp.toLp 2 ((Id.run (algorithm_6_4_3 pure svd hqp hpm A B)).2.2.col k) :
        EuclideanSpace ℝ (Fin m))) := by
  have hqm := hqp.trans hpm
  obtain ⟨hQRA, -⟩ := Chapter05.algorithm_5_2_1_spec hpm A
  obtain ⟨hQRB, -⟩ := Chapter05.algorithm_5_2_1_spec hqm B
  set QA := Chapter05.factoredQ (Id.run (Chapter05.algorithm_5_2_1 pure A)).2
    (Id.run (Chapter05.algorithm_5_2_1 pure A)).1 with hQA
  set QB := Chapter05.factoredQ (Id.run (Chapter05.algorithm_5_2_1 pure B)).2
    (Id.run (Chapter05.algorithm_5_2_1 pure B)).1 with hQB
  have hrun : Id.run (algorithm_6_4_3 pure svd hqp hpm A B) =
      ((Id.run (svd ((firstColumns QA hpm)ᵀ * firstColumns QB hqm))).2.1,
        firstColumns QA hpm *
          firstColumns (Id.run (svd ((firstColumns QA hpm)ᵀ * firstColumns QB hqm))).1 hqp,
        firstColumns QB hqm *
          (Id.run (svd ((firstColumns QA hpm)ᵀ * firstColumns QB hqm))).2.2) := by
    simp only [algorithm_6_4_3, Id.run_bind, Chapter05.forwardAccumulation_spec,
      Chapter01.algorithm_1_1_5_spec, zero_add]
    rfl
  rw [hrun]
  have h1 := hQRA.conjTranspose_firstColumns_mul_self hpm
  have h2 := hQRB.conjTranspose_firstColumns_mul_self hqm
  rw [conjTranspose_eq_transpose_of_trivial] at h1 h2
  exact isPrincipalVectors_of_isSVD h1 h2 hqp (range_toEuclideanLin_firstColumns hQRA hpm hA)
    (range_toEuclideanLin_firstColumns hQRB hqm hB)
    (hsvd ((firstColumns QA hpm)ᵀ * firstColumns QB hqm))

end PrincipalAnglesAlgorithm

/-! ### §6.4.4 Intersection of subspaces -/

/-- **Theorem 6.4.2** of [golub2013matrix]. Let $A \in \mathbb{R}^{m \times p}$ and
$B \in \mathbb{R}^{m \times q}$, and let $f_1, \dots, f_q$ and $g_1, \dots, g_q$ be principal
vectors of $(\operatorname{ran}(A), \operatorname{ran}(B))$, with principal angles $\theta_i$.
If the index $s$ is defined by $$1 = \cos(\theta_1) = \dots = \cos(\theta_s) >
\cos(\theta_{s+1}),$$ then $$\operatorname{ran}(A) \cap \operatorname{ran}(B) =
\operatorname{span}\{f_1, \dots, f_s\} = \operatorname{span}\{g_1, \dots, g_s\}.$$

**Generalization.** The source takes the $\theta_i$, $f_i$ and $g_i$ computed by Algorithm
6.4.3. The theorem holds for any principal vectors, which is what Algorithm 6.4.3 computes.

The index $s$ is given by the condition that $\cos(\theta_{i+1}) = 1$ if and only if $i < s$,
for every 0-based $i < q$. The one-line proof in the source ("if $\cos(\theta_i) = 1$, then
$f_i = g_i$") gives only the inclusion $\supseteq$; the backbone proves both inclusions.

**Reading.** The finite-index test includes $s=0$ and $s=q$. It requires no reference to a
$(q+1)$st principal angle when all the cosines equal one. -/
theorem theorem_6_4_2 {q : ℕ} {A : Matrix (Fin m) (Fin p) ℝ} {B : Matrix (Fin m) (Fin q) ℝ}
    {f g : Fin q → EuclideanSpace ℝ (Fin m)}
    (hfg : (LinearMap.range (toEuclideanLin A)).IsPrincipalVectors
      (LinearMap.range (toEuclideanLin B)) f g) {s : ℕ}
    (hs : ∀ i : Fin q, (LinearMap.range (toEuclideanLin A)).cosPrincipalAngle
      (LinearMap.range (toEuclideanLin B)) i = 1 ↔ (i : ℕ) < s) :
    LinearMap.range (toEuclideanLin A) ⊓ LinearMap.range (toEuclideanLin B) =
        Submodule.span ℝ (f '' {i : Fin q | (i : ℕ) < s}) ∧
      LinearMap.range (toEuclideanLin A) ⊓ LinearMap.range (toEuclideanLin B) =
        Submodule.span ℝ (g '' {i : Fin q | (i : ℕ) < s}) := by
  have hset : {i : Fin q | (LinearMap.range (toEuclideanLin A)).cosPrincipalAngle
      (LinearMap.range (toEuclideanLin B)) i = 1} = {i : Fin q | (i : ℕ) < s} := Set.ext hs
  have h1 := hfg.inf_eq_span
  rw [hset] at h1
  refine ⟨h1, h1.trans ?_⟩
  congr 1
  refine Set.image_congr fun i hi => ?_
  exact hfg.eq_of_cosPrincipalAngle_eq_one ((hs i).2 hi)

end GolubVanLoan.Chapter06
