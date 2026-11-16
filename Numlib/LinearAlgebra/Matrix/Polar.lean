/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Matrix.Polar` (beside `Mathlib.Analysis.Matrix.Order`, whose
`CFC.sqrt` it uses), or a C⋆-algebraic polar decomposition once Mathlib has one.
-/
import Mathlib.Analysis.Matrix.Order
import Numlib.Analysis.Matrix.OperatorNorm

/-!
# The polar decomposition of a matrix

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. A **polar decomposition** of
$A \in \mathbb{K}^{m \times n}$ is a factorization $A = U P$ in which
$U \in \mathbb{K}^{m \times n}$ has orthonormal columns, $U^H U = I$, and
$P \in \mathbb{K}^{n \times n}$ is positive semidefinite. It is the matrix analogue of the
factorization $z = e^{i\theta} |z|$ of a complex number. The module follows Theorem 9.4.1 and §6.4.1
of [golub2013matrix]. A polar decomposition exists whenever $A$ has at least as many rows as
columns, and the symmetric factor is always $P = (A^H A)^{1/2}$. For a nonsingular square $A$ the
decomposition is unique.

The polar factor also solves a nearness problem, (8.1.7) of [golub2013matrix]: if
$\|X^H X - I\|_2 \le \tau < 1$, the polar factor $Q$ of $X$ has orthonormal columns, the same range
as $X$, and $\|Q - X\|_2 \le \tau$.

## Main definitions

* `Matrix.IsPolarDecomposition`: the predicate that $A = U P$ with $U^H U = I$ and $P$ positive
  semidefinite.

## Main results

* `Matrix.IsSVD.isPolarDecomposition`: an SVD $W^H A V = \Sigma$ with $n \le m$ gives the polar
  decomposition $A = (W_1 V^H)(V \Sigma_1 V^H)$, where $W_1$ consists of the first $n$ columns of
  $W$.
* `Matrix.exists_isPolarDecomposition`: every $A \in \mathbb{K}^{m \times n}$ with $n \le m$ has a
  polar decomposition (Theorem 9.4.1 of [golub2013matrix]).
* `Matrix.exists_isPolarDecomposition_conjTranspose`: every $A \in \mathbb{K}^{m \times n}$ with
  $m \le n$ has a left polar decomposition $A = P V^H$.
* `Matrix.IsPolarDecomposition.eq_cfcSqrt`: the symmetric factor is $P = (A^H A)^{1/2}$.
* `Matrix.IsPolarDecomposition.eq_cfcAbs`: for square $A$, the symmetric factor is the absolute
  value $|A| = (A^H A)^{1/2}$.
* `Matrix.IsPolarDecomposition.eq_mul_inv_cfcSqrt`: if $A^H A$ is positive definite, the orthonormal
  factor is $U = A (A^H A)^{-1/2}$.
* `Matrix.IsPolarDecomposition.unique`: a nonsingular square matrix has only one polar
  decomposition.
* `Matrix.IsPolarDecomposition.l2_opNorm_sub_le`: if $X = Q P$ is a polar decomposition, then
  $\|Q - X\|_2 \le \|X^H X - I\|_2$.
* `Matrix.exists_orthonormal_cols_norm_sub_le`: the **nearest orthonormal block**, (8.1.7) of
  [golub2013matrix], as stated in the summary.

## Implementation notes

* Statements about "the polar factor" take a hypothesis `Matrix.IsPolarDecomposition A U P` instead
  of a chosen factorization, as `Matrix.IsSVD` does for the singular value decomposition. The reason
  is that the orthonormal factor is not unique for a singular $A$.
* The orthogonal Procrustes problem (`Numlib.LinearAlgebra.Matrix.Procrustes`) and the matrix
  functions of `Numlib.Analysis.Matrix.Function.Polar` are stated through
  `Matrix.IsPolarDecomposition`.
* `Matrix.IsSVD.isPolarDecomposition` is the only place in the library where the polar factors are
  built from singular vectors. The existence theorem for arbitrary finite index types reindexes to
  `Fin` and uses it.
* The square root and the absolute value are Mathlib's continuous functional calculus `CFC.sqrt` and
  `CFC.abs` for the matrix order of the scope `MatrixOrder`.
* In the section on the nearest orthonormal block, $\|\cdot\|_2$ is the operator norm induced by the
  Euclidean vector norm, the scoped instance `Matrix.Norms.L2Operator`, or `Matrix.lpOpNorm 2`.
-/

open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

section Def

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- A **polar decomposition**: for $A, U \in \mathbb{K}^{m \times n}$ and
$P \in \mathbb{K}^{n \times n}$, the triple $(A, U, P)$ is a polar decomposition if
$$U^H U = I, \qquad P \text{ is positive semidefinite}, \qquad A = U P.$$

This is the factorization of Theorem 9.4.1 of [golub2013matrix]. The structure is a
specification and does not choose the factors. For square $A$ the factor $U$ is unitary
(`Matrix.IsPolarDecomposition.mem_unitaryGroup`). -/
structure IsPolarDecomposition (A U : Matrix m n 𝕜) (P : Matrix n n 𝕜) : Prop where
  /-- The orthonormal factor has orthonormal columns: $U^H U = I$. -/
  conjTranspose_mul_self : Uᴴ * U = 1
  /-- The symmetric factor $P$ is positive semidefinite. -/
  posSemidef : P.PosSemidef
  /-- The factorization $A = U P$. -/
  eq_mul : A = U * P

namespace IsPolarDecomposition

variable {A U : Matrix m n 𝕜} {P : Matrix n n 𝕜}

/-- The symmetric factor $P$ of a polar decomposition $A = U P$ is Hermitian. -/
theorem isHermitian (h : IsPolarDecomposition A U P) : P.IsHermitian :=
  h.posSemidef.isHermitian

/-- If $A = U P$ is a polar decomposition, then $A^H A = P^2$. -/
theorem conjTranspose_mul_self_eq (h : IsPolarDecomposition A U P) : Aᴴ * A = P * P := by
  rw [h.eq_mul, conjTranspose_mul, h.isHermitian.eq, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ,
    h.conjTranspose_mul_self, Matrix.one_mul]

open scoped MatrixOrder in
/-- **The symmetric polar factor is $(A^H A)^{1/2}$**: if $A = U P$ is a polar decomposition of
$A \in \mathbb{K}^{m \times n}$, then
$$P = (A^H A)^{1/2},$$
the unique positive semidefinite square root of $A^H A$.

This is stated in §9.4.3 of [golub2013matrix]. The square root is `CFC.sqrt`. The proof uses
$A^H A = P^2$ and $(P^2)^{1/2} = P$ for a positive semidefinite $P$. -/
theorem eq_cfcSqrt (h : IsPolarDecomposition A U P) : P = CFC.sqrt (Aᴴ * A) := by
  rw [h.conjTranspose_mul_self_eq]
  exact (CFC.sqrt_mul_self P h.posSemidef.nonneg).symm

/-- If $A = U P$ is a polar decomposition and $A^H A$ is invertible, then $P$ is invertible. -/
theorem isUnit_of_isUnit_conjTranspose_mul_self (h : IsPolarDecomposition A U P)
    (hA : IsUnit (Aᴴ * A)) : IsUnit P := by
  rw [h.conjTranspose_mul_self_eq, isUnit_iff_isUnit_det, det_mul] at hA
  exact (isUnit_iff_isUnit_det P).2 (isUnit_of_mul_isUnit_left hA)

open scoped MatrixOrder in
/-- **The orthonormal factor of a matrix of full column rank**: if $A = U P$ is a polar
decomposition of $A \in \mathbb{K}^{m \times n}$ and $A^H A$ is positive definite, then
$$U = A \, \bigl((A^H A)^{1/2}\bigr)^{-1}.$$

This is the statement of §9.4.3 of [golub2013matrix] that "if $\operatorname{rank}(A) = n$, then
$U = A (A^T A)^{-1/2}$". The square root is `CFC.sqrt`. -/
theorem eq_mul_inv_cfcSqrt (h : IsPolarDecomposition A U P) (hA : (Aᴴ * A).PosDef) :
    U = A * (CFC.sqrt (Aᴴ * A))⁻¹ := by
  have hP := h.isUnit_of_isUnit_conjTranspose_mul_self hA.isUnit
  rw [← h.eq_cfcSqrt, h.eq_mul, Matrix.mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det P).1 hP), Matrix.mul_one]

/-- A polar decomposition is preserved by reindexing: if $A = U P$ is a polar decomposition and
$e_1 \colon m \simeq m'$, $e_2 \colon n \simeq n'$ are bijections, then the reindexed matrices
form a polar decomposition, with $e_1$ on the rows of $A$ and $U$, and $e_2$ on their columns
and on both indices of $P$. -/
theorem reindex {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq n']
    (h : IsPolarDecomposition A U P) (e₁ : m ≃ m') (e₂ : n ≃ n') :
    IsPolarDecomposition (reindex e₁ e₂ A) (reindex e₁ e₂ U) (reindex e₂ e₂ P) where
  conjTranspose_mul_self := by
    rw [conjTranspose_reindex, reindex_apply, reindex_apply, submatrix_mul_equiv,
      h.conjTranspose_mul_self, submatrix_one_equiv]
  posSemidef := h.posSemidef.submatrix _
  eq_mul := by
    rw [h.eq_mul, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]

/-- **The left polar decomposition**: let $A \in \mathbb{K}^{n \times m}$,
$V \in \mathbb{K}^{m \times n}$ and $P \in \mathbb{K}^{n \times n}$. If $A^H = V P$ is a polar
decomposition of the adjoint, then
$$A = P V^H,$$
where $V^H$ has orthonormal rows and $P$ is positive semidefinite. -/
theorem eq_mul_conjTranspose {A : Matrix n m 𝕜} {V : Matrix m n 𝕜}
    (h : IsPolarDecomposition Aᴴ V P) : A = P * Vᴴ := by
  rw [← conjTranspose_conjTranspose A, h.eq_mul, conjTranspose_mul, h.isHermitian.eq]

end IsPolarDecomposition

namespace IsPolarDecomposition

variable {A U P : Matrix n n 𝕜}

/-- For a square matrix $A \in \mathbb{K}^{n \times n}$ with polar decomposition $A = U P$, the
orthonormal factor $U$ is unitary. -/
theorem mem_unitaryGroup (h : IsPolarDecomposition A U P) : U ∈ unitaryGroup n 𝕜 :=
  mem_unitaryGroup_iff'.2 (by rw [star_eq_conjTranspose]; exact h.conjTranspose_mul_self)

open scoped MatrixOrder in
/-- For a square matrix $A \in \mathbb{K}^{n \times n}$ with polar decomposition $A = U P$, the
symmetric factor is the absolute value of $A$:
$$P = |A| = (A^* A)^{1/2}.$$

The absolute value is Mathlib's `CFC.abs A`, which is `CFC.sqrt (star A * A)`. -/
theorem eq_cfcAbs (h : IsPolarDecomposition A U P) : P = CFC.abs A := by
  rw [CFC.abs, star_eq_conjTranspose]
  exact h.eq_cfcSqrt

/-- For a nonsingular square matrix $A$ with polar decomposition $A = U P$, the symmetric factor $P$
is invertible. -/
theorem isUnit (h : IsPolarDecomposition A U P) (hA : IsUnit A) : IsUnit P := by
  rw [isUnit_iff_isUnit_det, h.eq_mul, det_mul] at hA
  exact (isUnit_iff_isUnit_det P).2 (isUnit_of_mul_isUnit_right hA)

/-- **Uniqueness of the polar decomposition of a nonsingular matrix**: let
$A \in \mathbb{K}^{n \times n}$ be invertible. If $A = U P$ and $A = U' P'$ are polar
decompositions, then
$$U = U' \quad \text{and} \quad P = P'.$$

This is Problem P9.4.8 of [golub2013matrix]. Both symmetric factors are $(A^H A)^{1/2}$
(`Matrix.IsPolarDecomposition.eq_cfcSqrt`), and then $U = A P^{-1} = U'$. -/
theorem unique {U' P' : Matrix n n 𝕜} (hA : IsUnit A) (h : IsPolarDecomposition A U P)
    (h' : IsPolarDecomposition A U' P') : U = U' ∧ P = P' := by
  have hPP : P = P' := h.eq_cfcSqrt.trans h'.eq_cfcSqrt.symm
  refine ⟨?_, hPP⟩
  have hP := (isUnit_iff_isUnit_det P).1 (h.isUnit hA)
  have h1 : U * P = U' * P := by rw [← h.eq_mul, h'.eq_mul, hPP]
  calc U = U * P * P⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one]
    _ = U' := by rw [h1, Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one]

end IsPolarDecomposition

end Def

/-! ### Existence, from the singular value decomposition -/

section SVD

variable {m n : ℕ}

variable {A : Matrix (Fin m) (Fin n) 𝕜} {W : Matrix (Fin m) (Fin m) 𝕜} {σ : ℕ → ℝ}
  {V : Matrix (Fin n) (Fin n) 𝕜}

/-- **The polar decomposition from an SVD**: let $n \le m$, let $A \in \mathbb{K}^{m \times n}$, and
let $W^H A V = \Sigma$ be a singular value decomposition, with $W \in \mathbb{K}^{m \times m}$
and $V \in \mathbb{K}^{n \times n}$ unitary and singular values
$\sigma_0 \ge \sigma_1 \ge \dots \ge 0$. Let $W_1 \in \mathbb{K}^{m \times n}$ consist of the
first $n$ columns of $W$. Then
$$A = (W_1 V^H) \bigl(V \operatorname{diag}(\sigma_0, \dots, \sigma_{n-1}) V^H\bigr)$$
is a polar decomposition.

This is the proof of Theorem 9.4.1 of [golub2013matrix], and §6.4.1 of the source:
"$A = U \Sigma V^T$ gives $A = (U V^T)(V \Sigma V^T)$". The SVD is `Matrix.IsSVD A W σ V`, and
$W_1$ is `W.submatrix id (Fin.castLE hnm)`. -/
theorem IsSVD.isPolarDecomposition (h : IsSVD A W σ V) (hnm : n ≤ m) :
    IsPolarDecomposition A (W.submatrix id (Fin.castLE hnm) * Vᴴ)
      (V * diagonal (fun i : Fin n => ((σ i : ℝ) : 𝕜)) * Vᴴ) where
  conjTranspose_mul_self := by
    have hV : V * Vᴴ = 1 := by
      rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 h.mem_unitaryGroup_right
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ Vᴴ,
      conjTranspose_submatrix_castLE_mul_self hnm h.mem_unitaryGroup_left, Matrix.one_mul, hV]
  posSemidef := by
    refine PosSemidef.mul_mul_conjTranspose_same ?_ V
    exact posSemidef_diagonal_iff.2 fun i => RCLike.ofReal_nonneg.2 (h.nonneg i)
  eq_mul := by
    have hV : Vᴴ * V = 1 := by
      rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 h.mem_unitaryGroup_right
    conv_lhs => rw [h.eq_mul_mul_star, mul_rectDiagonal_eq_submatrix_mul_diagonal hnm,
      star_eq_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]

/-- **The polar decomposition from an SVD of a square matrix**: if $W^H A V = \Sigma$ is a singular
value decomposition of $A \in \mathbb{K}^{n \times n}$, with singular values
$\sigma_0, \dots, \sigma_{n-1}$, then
$$A = (W V^H) \bigl(V \operatorname{diag}(\sigma_0, \dots, \sigma_{n-1}) V^H\bigr)$$
is a polar decomposition. -/
theorem IsSVD.isPolarDecomposition_of_square {A W V : Matrix (Fin n) (Fin n) 𝕜}
    (h : IsSVD A W σ V) :
    IsPolarDecomposition A (W * Vᴴ) (V * diagonal (fun i : Fin n => ((σ i : ℝ) : 𝕜)) * Vᴴ) := by
  simpa using h.isPolarDecomposition le_rfl

end SVD

section Exists

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Existence of the polar decomposition**: let $m$ and $n$ be finite index types with
$|n| \le |m|$. Every $A \in \mathbb{K}^{m \times n}$ has a polar decomposition $A = U P$, with
$U^H U = I$ and $P$ positive semidefinite.

This is Theorem 9.4.1 of [golub2013matrix]. The proof reindexes $A$ to `Fin`, takes an SVD, and
applies `Matrix.IsSVD.isPolarDecomposition`. -/
theorem exists_isPolarDecomposition (A : Matrix m n 𝕜) (h : Fintype.card n ≤ Fintype.card m) :
    ∃ U P, IsPolarDecomposition A U P := by
  set e₁ := Fintype.equivFin m
  set e₂ := Fintype.equivFin n
  obtain ⟨W, σ, V, hs⟩ := exists_isSVD (reindex e₁ e₂ A)
  have hp := (hs.isPolarDecomposition h).reindex e₁.symm e₂.symm
  rw [← reindex_symm, Equiv.symm_apply_apply] at hp
  exact ⟨_, _, hp⟩

omit [DecidableEq n] in
/-- **The left polar decomposition of a wide matrix**: let $m$ and $n$ be finite index types with
$|m| \le |n|$. For every $A \in \mathbb{K}^{m \times n}$ there are
$V \in \mathbb{K}^{n \times m}$ and $P \in \mathbb{K}^{m \times m}$ such that $A^H = V P$ is a
polar decomposition. Equivalently, $A = P V^H$
(`Matrix.IsPolarDecomposition.eq_mul_conjTranspose`), where $V^H$ has orthonormal rows and
$P = (A A^H)^{1/2}$ is positive semidefinite.

This is §9.4.3 of [golub2013matrix] applied to $A^H$, as in Problem P9.4.11 of the source. -/
theorem exists_isPolarDecomposition_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜)
    (h : Fintype.card m ≤ Fintype.card n) : ∃ V P, IsPolarDecomposition Aᴴ V P :=
  exists_isPolarDecomposition Aᴴ h

end Exists

/-! ### The nearest orthonormal block -/

section Nearest

variable {n r : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

open scoped Matrix.Norms.L2Operator

/-- For $s \ge 0$, $|1 - s| \le |1 - s^2|$. -/
private theorem abs_one_sub_le_abs_one_sub_sq {s : ℝ} (hs : 0 ≤ s) : |1 - s| ≤ |1 - s * s| := by
  rw [show 1 - s * s = (1 - s) * (1 + s) by ring, abs_mul]
  exact le_mul_of_one_le_right (abs_nonneg _) (by rw [abs_of_nonneg (by linarith)]; linarith)

/-- For a positive semidefinite $P \in \mathbb{K}^{r \times r}$,
$$\|I - P\|_2 \le \|I - P^2\|_2.$$
In an eigenbasis of $P$ the two matrices are diagonal with the entries $1 - s$ and $1 - s^2$,
where $s \ge 0$ runs over the eigenvalues of $P$. -/
theorem PosSemidef.l2_opNorm_one_sub_le {P : Matrix r r 𝕜} (hP : P.PosSemidef) :
    ‖1 - P‖ ≤ ‖1 - P * P‖ := by
  set u := hP.isHermitian.eigenvectorUnitary
  set φ := Unitary.conjStarAlgAut 𝕜 (Matrix r r 𝕜) u
  set s := hP.isHermitian.eigenvalues
  have hφ : ∀ M, ‖φ M‖ = ‖M‖ := fun M => by
    rw [Unitary.conjStarAlgAut_apply]
    exact l2_opNorm_unitary_mul_mul_unitary u.2 M (Unitary.star_mem u.2)
  have hPd : P = φ (diagonal (RCLike.ofReal ∘ s)) := hP.isHermitian.spectral_theorem
  have h1 : 1 - P = φ (diagonal fun i => ((1 - s i : ℝ) : 𝕜)) := by
    rw [hPd, ← map_one φ, ← map_sub, ← diagonal_one, diagonal_sub]
    congr 2
    funext i
    simp
  have h2 : 1 - P * P = φ (diagonal fun i => ((1 - s i * s i : ℝ) : 𝕜)) := by
    rw [hPd, ← map_one φ, ← map_mul, ← map_sub, ← diagonal_one, diagonal_mul_diagonal,
      diagonal_sub]
    congr 2
    funext i
    simp
  rw [h1, h2, hφ, hφ, l2_opNorm_diagonal, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  refine le_trans ?_ (norm_le_pi_norm _ i)
  simp only [RCLike.norm_ofReal]
  exact abs_one_sub_le_abs_one_sub_sq (hP.eigenvalues_nonneg i)

omit [DecidableEq n] in
/-- **The polar factor is the nearest orthonormal block, quantitatively**: let
$X, Q \in \mathbb{K}^{n \times r}$ and $P \in \mathbb{K}^{r \times r}$. If $X = Q P$ is a polar
decomposition, then
$$\|Q - X\|_2 \le \|X^H X - I\|_2.$$

This is (8.1.7) of [golub2013matrix]. The proof writes $Q - X = Q (I - P)$, uses that $Q$ is an
isometry, and applies $\|I - P\|_2 \le \|I - P^2\|_2 = \|I - X^H X\|_2$. -/
theorem IsPolarDecomposition.l2_opNorm_sub_le {X Q : Matrix n r 𝕜} {P : Matrix r r 𝕜}
    (h : IsPolarDecomposition X Q P) : ‖Q - X‖ ≤ ‖Xᴴ * X - 1‖ := by
  have hQ : Q - X = Q * (1 - P) := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← h.eq_mul]
  rw [hQ, l2_opNorm_mul_of_conjTranspose_mul_self_eq_one h.conjTranspose_mul_self,
    h.conjTranspose_mul_self_eq, ← norm_neg (P * P - 1), neg_sub]
  exact h.posSemidef.l2_opNorm_one_sub_le

omit [DecidableEq n] in
/-- **The nearest orthonormal block**: let $n$ and $r$ be finite index types with $|r| \le |n|$, and
let $X \in \mathbb{K}^{n \times r}$ and $\tau \in \mathbb{R}$ satisfy
$$\|X^H X - I\|_2 \le \tau < 1.$$
Then there is $Q \in \mathbb{K}^{n \times r}$ with $Q^H Q = I$,
$\operatorname{ran} Q = \operatorname{ran} X$ and $\|Q - X\|_2 \le \tau$.

This is (8.1.7) of [golub2013matrix], in the proof of Theorem 8.1.16. The source derives the
bound with the intermediate step $1 - \sigma_r^2 = \tau$, which holds only when the smallest
singular value is the one farthest from $1$; the conclusion does not need it.

The matrix $Q$ is the polar factor of $X$ (`Matrix.IsPolarDecomposition.l2_opNorm_sub_le`). The
bound $\tau < 1$ makes $X^H X$ invertible, hence $P$ invertible, so $Q = X P^{-1}$ and $X = Q P$
have the same range. The norm is `Matrix.lpOpNorm 2`, and the ranges are those of the linear
maps `Matrix.toLin' Q` and `Matrix.toLin' X`. -/
theorem exists_orthonormal_cols_norm_sub_le (X : Matrix n r 𝕜)
    (hcard : Fintype.card r ≤ Fintype.card n) {τ : ℝ} (hX : lpOpNorm 2 (Xᴴ * X - 1) ≤ τ)
    (hτ : τ < 1) :
    ∃ Q : Matrix n r 𝕜, Qᴴ * Q = 1 ∧
      LinearMap.range (toLin' Q) = LinearMap.range (toLin' X) ∧ lpOpNorm 2 (Q - X) ≤ τ := by
  obtain ⟨Q, P, h⟩ := exists_isPolarDecomposition X hcard
  rw [lpOpNorm_two] at hX
  refine ⟨Q, h.conjTranspose_mul_self, ?_, ?_⟩
  · have hG : IsUnit (Xᴴ * X) := by
      -- the Neumann series in the normed ring of `‖·‖₂`
      have h1 : ‖1 - Xᴴ * X‖ < 1 := by rw [norm_sub_rev]; exact hX.trans_lt hτ
      simpa using (Units.oneSub _ h1).isUnit
    have hP := (isUnit_iff_isUnit_det P).1 (h.isUnit_of_isUnit_conjTranspose_mul_self hG)
    have hQX : Q = X * P⁻¹ := by
      rw [h.eq_mul, Matrix.mul_assoc, mul_nonsing_inv _ hP, Matrix.mul_one]
    refine le_antisymm ?_ ?_
    · rw [hQX, toLin'_mul]
      exact LinearMap.range_comp_le_range _ _
    · conv_lhs => rw [h.eq_mul]
      rw [toLin'_mul]
      exact LinearMap.range_comp_le_range _ _
  · rw [lpOpNorm_two]
    exact h.l2_opNorm_sub_le.trans hX

end Nearest

end Matrix
