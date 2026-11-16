/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.LinearAlgebra.Matrix.Bidiagonal
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Matrix.Schur
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section07

/-!
# Quarteroni, Sacco and Saleri, Section 5.8: Computing the eigenvectors and the SVD of a matrix

This module formalizes Section 5.8 of [quarteroni2000numerical], which computes eigenvectors and the
singular value decomposition from the reduced forms of the earlier sections. Inverse iteration on
the Hessenberg form $H = Q^H A Q$ gives an approximate eigenvector $q$ of $H$, and $x = Qq$ is the
eigenvector of $A$ (Section 5.8.1). For a simple eigenvalue $\lambda = t_{kk}$ of the Schur form
$T$, a triangular solve (5.56) gives an eigenvector $y$ of $T$, and $x = Qy$ is an eigenvector of
$A$ (Section 5.8.2). The Golub–Kahan–Reinsch algorithm of Section 5.8.3 first reduces
$A \in \mathbb{R}^{m \times n}$, $m \ge n$, to the form $\mathcal{U}^T A \mathcal{V} =
\begin{bmatrix} B \\ 0 \end{bmatrix}$ with $B$ upper bidiagonal (5.57), and then computes the SVD of
$B$. The proofs specialize `Numlib.Eigen.PowerMethod` (inverse iteration commutes with a unitary
change of coordinates), `Numlib.LinearAlgebra.Matrix.Schur` (the eigenvector of a simple eigenvalue
of a triangular matrix), `Numlib.LinearAlgebra.Matrix.Bidiagonal` and
`Numlib.LinearAlgebra.Matrix.SVD`, and use the inverse iteration
`QuarteroniSaccoSaleri.Chapter05.inverseIterate` of Section 5.3.

## Main definitions

* Section 5.8.3, `QuarteroniSaccoSaleri.Chapter05.padBlock`: the block matrix
  $\operatorname{diag}(W, I_{m-n}) \in \mathbb{R}^{m \times m}$.

## Main results

* Section 5.8.1, `QuarteroniSaccoSaleri.Chapter05.inverseIterate_conj`: inverse iteration on
  $H = Q^H A Q$ from $Q^H q^{(0)}$ gives $Q^H q^{(k)}$, where $q^{(k)}$ are the inverse iterates of
  $A$.
* Equation (5.56), `QuarteroniSaccoSaleri.Chapter05.equation_5_56`: the eigenvector of a simple
  eigenvalue of an upper triangular $T$, and its transport $x = Qy$ to $A = Q T Q^H$.
* Equation (5.57), `QuarteroniSaccoSaleri.Chapter05.equation_5_57`: the Golub–Kahan
  bidiagonalization $\mathcal{U}^T A \mathcal{V} = \begin{bmatrix} B \\ 0 \end{bmatrix}$.
* Section 5.8.3, `QuarteroniSaccoSaleri.Chapter05.golubKahan_svd`: the SVD of $A$ from the SVD
  $\mathcal{W}^T B \mathcal{Z} = \Sigma$ of the bidiagonal factor.

## Conventions

* The Hessenberg inverse iteration of Section 5.8.1 is stated for the inverse iteration (5.28) of
  Section 5.3, over $\mathbb{R}$ or $\mathbb{C}$ (`RCLike 𝕜`), with $H = Q^H A Q$ for a unitary $Q$.
  In the real setting of the book, $Q$ is orthogonal and $Q^H = Q^T$. As in (5.28), the shift is not
  an eigenvalue of $A$, so that the linear systems of the iteration are solvable.
* The Schur form of Section 5.8.2 is complex: $T \in \mathbb{C}^{n \times n}$ is upper triangular.
  The vector $y$ of (5.56) is `Matrix.IsUpperTriangular.schurEigenvector T k`, and the leading block
  $T_{11}$ of order $k$ is `T.submatrix (Fin.castLE _) (Fin.castLE _)`.
* The bidiagonalization (5.57) is real, for $A \in \mathbb{R}^{m \times n}$ with $m \ge n$. "Upper
  bidiagonal" is `Matrix.IsUpperBidiagonal`.

## Deviations from the source

* **The iterative phase of the Golub–Kahan–Reinsch algorithm, Section 5.8.3** (reading). The source
  describes the iteration only by its limit; the theorem states the existence of that limit, which
  is the SVD of $B$, and claims nothing about the iteration. See
  `QuarteroniSaccoSaleri.Chapter05.golubKahan_svd`.

## Not formalized

* **Section 5.8.3, the backward stability of the Golub–Kahan–Reinsch algorithm.** The source claims
  that the singular values computed in floating-point arithmetic with unit roundoff $u$ are the
  exact singular values of a matrix $A + \delta A$ with $\|\delta A\|_2 \le C_{mn} u \|A\|_2$. It
  quotes this without proof, does not give $C_{mn}$, and says that $C_{mn}$ depends on $m$, $n$ and
  $u$. A constant that may depend on $u$ makes the inequality empty, because every $\delta A$
  satisfies it for a large enough $C_{mn}(u)$. A correct statement needs an explicit constant that
  does not depend on $u$. Since the number of sweeps of the iterative phase is unbounded, it must
  also fix a number $s$ of sweeps and read $\|\delta A\| \le (c_1 + c_2 s) u \|A\|$, or else be
  about the exact limit. The module `Numlib.FloatingPoint.Householder` gives the rounding model of
  Householder transformations and their accumulation ([higham2002accuracy], Lemmas 19.1–19.3), but a
  rounding model of the computed bidiagonalization, of the computed implicit-shift QR step on a
  bidiagonal matrix, and of the deflation criterion are not available.
-/

open Matrix

namespace QuarteroniSaccoSaleri.Chapter05

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-! ### Section 5.8.1: the Hessenberg inverse iteration -/

/-- **Section 5.8.1** of [quarteroni2000numerical], the Hessenberg inverse iteration. Let
$A, Q \in \mathbb{K}^{n \times n}$ with $Q$ unitary, so that $H = Q^H A Q$ (the Hessenberg form
of $A$, with $Q^T A Q$ for a real orthogonal $Q$). Let $\mu \in \mathbb{K}$ not be an eigenvalue
of $A$, and let $q^{(0)} \in \mathbb{K}^n$ be a unit vector. Then for every $k$, the $k$-th
iterate of the inverse iteration (5.28) with shift $\mu$ applied to $H$ from $Q^H q^{(0)}$ is
$Q^H q^{(k)}$, where $q^{(k)}$ is the $k$-th inverse iterate of $A$ from $q^{(0)}$. Hence an
approximate eigenvector $q$ of $H$ gives the approximate eigenvector $x = Qq$ of $A$.

The iteration is `QuarteroniSaccoSaleri.Chapter05.inverseIterate`, and the vector $Q^H v$ is
`toEuclideanLin Qᴴ v`. The proof specializes `Krylov.inverseIterate_conj_linearIsometryEquiv`,
through `QuarteroniSaccoSaleri.Chapter05.inverseIterate_eq_krylov` on both sides. -/
theorem inverseIterate_conj {A Q : Matrix (Fin n) (Fin n) 𝕜}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) 𝕜) {μ : 𝕜} (hμ : μ ∉ spectrum 𝕜 A)
    {q₀ : EuclideanSpace 𝕜 (Fin n)} (hq₀ : ‖q₀‖ = 1) (k : ℕ) :
    inverseIterate (Qᴴ * A * Q) μ (toEuclideanLin Qᴴ q₀) k =
      toEuclideanLin Qᴴ (inverseIterate A μ q₀ k) := by
  set U := unitaryLinearIsometryEquiv hQ with hU
  have hμ' : μ ∉ spectrum 𝕜 (Qᴴ * A * Q) := by rwa [spectrum_conjTranspose_mul_mul hQ]
  have hq₀' : ‖toEuclideanLin Qᴴ q₀‖ = 1 := by
    rw [← unitaryLinearIsometryEquiv_symm_apply hQ, LinearIsometryEquiv.norm_map, hq₀]
  have hconj : U.symm.toLinearEquiv.conj (toEuclideanLin A) = toEuclideanLin (Qᴴ * A * Q) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conj_apply_apply, toEuclideanLin_mul_apply, toEuclideanLin_mul_apply]
    change U.symm (toEuclideanLin A (U.symm.symm x)) = _
    rw [LinearIsometryEquiv.symm_symm, hU, unitaryLinearIsometryEquiv_symm_apply,
      unitaryLinearIsometryEquiv_apply]
  rw [inverseIterate_eq_krylov hμ' hq₀' k, inverseIterate_eq_krylov hμ hq₀ k, ← hconj,
    ← unitaryLinearIsometryEquiv_symm_apply hQ, ← unitaryLinearIsometryEquiv_symm_apply hQ]
  exact Krylov.inverseIterate_conj_linearIsometryEquiv U (toEuclideanLin A) μ q₀ k

/-! ### Section 5.8.2: eigenvectors from the Schur form -/

/-- **Equation (5.56)** of [quarteroni2000numerical], the eigenvector of a simple eigenvalue from
the Schur form. Let $T \in \mathbb{C}^{n \times n}$ be upper triangular (the Schur form
$Q^H A Q = T$ of $A$), and let $\lambda = t_{kk}$ be a simple eigenvalue: $t_{ii} \neq \lambda$
for $i \neq k$. Partition $$T = \begin{bmatrix} T_{11} & v & T_{13} \\ 0 & \lambda & w^T \\ 0 &
0 & T_{33} \end{bmatrix}$$ around row $k$, with $T_{11}$ of order $k - 1$. Let
$y = (y_1, 1, 0)$, where $y_1$ solves the triangular system $(T_{11} - \lambda I) y_1 = -v$ of
(5.56). Then $y_k = 1$, $y_i = 0$ for $i > k$, the leading entries of $y$ are
$y_1 = -(T_{11} - \lambda I)^{-1} v$, $y \neq 0$, and $$T y = \lambda y.$$ Moreover, for every
unitary $Q \in \mathbb{C}^{n \times n}$, the vector $x = Qy$ satisfies
$(Q T Q^H) x = \lambda x$.

Indices are 0-based, so $T_{11}$ is the leading block of order `k`,
`T.submatrix (Fin.castLE _) (Fin.castLE _)`. The vector $y$ is
`Matrix.IsUpperTriangular.schurEigenvector T k`. The proof specializes
`Matrix.IsUpperTriangular.mulVec_schurEigenvector`, which needs only $t_{ii} \neq \lambda$ for
$i < k$, and `Matrix.mulVec_conj_eq_smul_of_mulVec_eq_smul`. -/
theorem equation_5_56 {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.IsUpperTriangular) {k : Fin n}
    (hk : ∀ i, i ≠ k → T i i ≠ T k k) :
    let y := IsUpperTriangular.schurEigenvector T k
    y k = 1 ∧ (∀ i, k < i → y i = 0) ∧
      (∀ (i : Fin n) (h : (i : ℕ) < k), y i =
        -(((T.submatrix (Fin.castLE k.isLt.le) (Fin.castLE k.isLt.le) - T k k • 1)⁻¹ *ᵥ
          fun j => T (Fin.castLE k.isLt.le j) k) ⟨i, h⟩)) ∧
      T *ᵥ y = T k k • y ∧ y ≠ 0 ∧
      ∀ Q : Matrix (Fin n) (Fin n) ℂ, Q ∈ Matrix.unitaryGroup (Fin n) ℂ →
        (Q * T * Qᴴ) *ᵥ (Q *ᵥ y) = T k k • (Q *ᵥ y) := by
  intro y
  have hy : T *ᵥ y = T k k • y :=
    hT.mulVec_schurEigenvector fun i hi => hk i hi.ne
  refine ⟨IsUpperTriangular.schurEigenvector_apply_self T k,
    fun i hi => IsUpperTriangular.schurEigenvector_apply_of_lt T hi, fun i h => ?_, hy,
    IsUpperTriangular.schurEigenvector_ne_zero T k, fun Q hQ => ?_⟩
  · change (if h : (i : ℕ) < k then _ else _) = _
    rw [dite_eq_left h]
  · have hQQ : Q * Qᴴ = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.mp hQ
    have hu : IsUnit Qᴴ :=
      isUnit_of_mem_unitaryGroup (by rw [← star_eq_conjTranspose]; exact Unitary.star_mem hQ)
    have hinv : (Qᴴ)⁻¹ = Q := inv_eq_left_inv hQQ
    have h := mulVec_conj_eq_smul_of_mulVec_eq_smul hu hy
    rwa [hinv] at h

/-! ### Section 5.8.3: the Golub–Kahan bidiagonalization -/

/-- **Equation (5.57)** of [quarteroni2000numerical] (Golub–Kahan bidiagonalization), the direct
phase of the Golub–Kahan–Reinsch algorithm. Let $A \in \mathbb{R}^{m \times n}$ with $n \le m$.
There are orthogonal matrices $\mathcal{U} \in \mathbb{R}^{m \times m}$ and
$\mathcal{V} \in \mathbb{R}^{n \times n}$ such that $$\mathcal{U}^T A \mathcal{V} =
\begin{bmatrix} B \\ 0 \end{bmatrix},$$ that is, the rows $n + 1, \dots, m$ of
$\mathcal{U}^T A \mathcal{V}$ vanish, and its leading $n \times n$ block $B$ is upper
bidiagonal.

Indices are 0-based, so the zero rows are those with index at least `n`. The proof specializes
`Matrix.exists_unitary_mul_mul_unitary_isUpperBidiagonal`, which uses Householder reflectors
alternately on the two sides. -/
theorem equation_5_57 {m : ℕ} (h : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ U ∈ Matrix.orthogonalGroup (Fin m) ℝ, ∃ V ∈ Matrix.orthogonalGroup (Fin n) ℝ,
      (∀ (i : Fin m) (j : Fin n), n ≤ (i : ℕ) → (Uᵀ * A * V) i j = 0) ∧
        ((Uᵀ * A * V).submatrix (Fin.castLE h) id).IsUpperBidiagonal := by
  obtain ⟨U, hU, V, hV, h0, hB⟩ := exists_unitary_mul_mul_unitary_isUpperBidiagonal h A
  rw [conjTranspose_eq_transpose_of_trivial] at h0 hB
  exact ⟨U, hU, V, hV, h0, hB⟩

/-! ### Section 5.8.3: the iterative phase, the SVD from the bidiagonal form -/

/-- The bijection $\{0, \dots, n - 1\} \sqcup \{0, \dots, m - n - 1\} \to \{0, \dots, m - 1\}$ for
$n \le m$ that identifies the block index of $\begin{bmatrix} B \\ 0 \end{bmatrix}$ with the row
index: it maps $k$ in the first part to $k$, and $k$ in the second part to $n + k$. It is the
backbone's `Matrix.blockEquiv`. -/
def blockEquiv {m : ℕ} (h : n ≤ m) : Fin n ⊕ Fin (m - n) ≃ Fin m :=
  Matrix.blockEquiv h

/-- The bijection `QuarteroniSaccoSaleri.Chapter05.blockEquiv h` maps $k$ in the first part to the
row index $k$. -/
theorem coe_blockEquiv_inl {m : ℕ} (h : n ≤ m) (k : Fin n) :
    (blockEquiv h (Sum.inl k) : ℕ) = k := by
  simp [blockEquiv]

/-- The bijection `QuarteroniSaccoSaleri.Chapter05.blockEquiv h` maps $k$ in the second part to the
row index $n + k$. -/
theorem coe_blockEquiv_inr {m : ℕ} (h : n ≤ m) (k : Fin (m - n)) :
    (blockEquiv h (Sum.inr k) : ℕ) = n + k := by
  simp [blockEquiv]

/-- **Section 5.8.3** of [quarteroni2000numerical], the block matrix
$\operatorname{diag}(W, I_{m-n})$. For $W \in \mathbb{R}^{n \times n}$ and $n \le m$, it is the
matrix in $\mathbb{R}^{m \times m}$ with $W$ in the leading $n \times n$ block, the identity
$I_{m-n}$ in the trailing block, and zero elsewhere.

The blocks are placed by `QuarteroniSaccoSaleri.Chapter05.blockEquiv`. -/
def padBlock {m : ℕ} (h : n ≤ m) (W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (fromBlocks W 0 0 (1 : Matrix (Fin (m - n)) (Fin (m - n)) ℝ)).submatrix (blockEquiv h).symm
    (blockEquiv h).symm

/-- If $W \in \mathbb{R}^{n \times n}$ is orthogonal, then $\operatorname{diag}(W, I_{m-n})$ is
orthogonal. -/
theorem padBlock_mem_orthogonalGroup {m : ℕ} (h : n ≤ m) {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : W ∈ orthogonalGroup (Fin n) ℝ) : padBlock h W ∈ orthogonalGroup (Fin m) ℝ := by
  rw [mem_orthogonalGroup_iff'] at hW ⊢
  rw [padBlock, transpose_submatrix, submatrix_mul_equiv, fromBlocks_transpose, transpose_zero,
    transpose_zero, transpose_one, fromBlocks_multiply]
  simp only [hW, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, Matrix.mul_one,
    fromBlocks_one, submatrix_one_equiv]

/-- **Section 5.8.3** of [quarteroni2000numerical], the iterative phase: the SVD of $A$ from its
bidiagonalization. Let $A \in \mathbb{R}^{m \times n}$ with $n \le m$, and let
$\mathcal{U} \in \mathbb{R}^{m \times m}$ and $\mathcal{V} \in \mathbb{R}^{n \times n}$ be
orthogonal matrices such that the rows $n + 1, \dots, m$ of $\mathcal{U}^T A \mathcal{V}$
vanish, as in (5.57). Let $B$ be the leading $n \times n$ block of
$\mathcal{U}^T A \mathcal{V}$. Then there are orthogonal matrices $\mathcal{W}, \mathcal{Z} \in
\mathbb{R}^{n \times n}$ and numbers $\sigma_1, \sigma_2, \dots$ such that $$\mathcal{W}^T B
\mathcal{Z} = \Sigma = \operatorname{diag}(\sigma_1, \dots, \sigma_n),$$ the matrices $U =
\mathcal{U} \operatorname{diag}(\mathcal{W}, I_{m-n})$ and $V = \mathcal{V} \mathcal{Z}$ are
orthogonal, and $$U^T A V = \begin{bmatrix} \Sigma \\ 0 \end{bmatrix}.$$

**Reading.** The source describes the iterative phase, the QR iteration on $B$, only by its
limit $\mathcal{W}^T B \mathcal{Z} = \Sigma$. The theorem states the existence of this limit,
which is the SVD of the square matrix $B$ (Property 1.7), and claims nothing about the iteration
that produces $\mathcal{W}$ and $\mathcal{Z}$. The theorem does not assume that $B$ is
bidiagonal.

The matrix $\Sigma$ is `Matrix.rectDiagonal σ` in both shapes, for a sequence `σ : ℕ → ℝ`
(0-based). The proof takes for `σ` the singular values of $B$, through the backbone
`Matrix.exists_svd`; the statement only asserts that some `σ` exists. The assembly is the block
computation $\operatorname{diag}(\mathcal{W}, I)^T \begin{bmatrix} B \\ 0 \end{bmatrix}
\mathcal{Z} = \begin{bmatrix} \mathcal{W}^T B \mathcal{Z} \\ 0 \end{bmatrix}$, with
$\operatorname{diag}(\mathcal{W}, I)$ the matrix `QuarteroniSaccoSaleri.Chapter05.padBlock h W`.
The rounding-error bound $\|\delta A\|_2 \le C_{mn} u \|A\|_2$ that the source quotes after the
algorithm is not formalized. -/
theorem golubKahan_svd {m : ℕ} (h : n ≤ m) (A : Matrix (Fin m) (Fin n) ℝ)
    {𝒰 : Matrix (Fin m) (Fin m) ℝ} (h𝒰 : 𝒰 ∈ orthogonalGroup (Fin m) ℝ)
    {𝒱 : Matrix (Fin n) (Fin n) ℝ} (h𝒱 : 𝒱 ∈ orthogonalGroup (Fin n) ℝ)
    (h0 : ∀ (i : Fin m) (j : Fin n), n ≤ (i : ℕ) → (𝒰ᵀ * A * 𝒱) i j = 0) :
    ∃ W ∈ orthogonalGroup (Fin n) ℝ, ∃ Z ∈ orthogonalGroup (Fin n) ℝ, ∃ σ : ℕ → ℝ,
      Wᵀ * (𝒰ᵀ * A * 𝒱).submatrix (Fin.castLE h) id * Z = rectDiagonal σ ∧
      𝒰 * padBlock h W ∈ orthogonalGroup (Fin m) ℝ ∧ 𝒱 * Z ∈ orthogonalGroup (Fin n) ℝ ∧
      (𝒰 * padBlock h W)ᵀ * A * (𝒱 * Z) = rectDiagonal σ := by
  set M := 𝒰ᵀ * A * 𝒱 with hM
  set B := M.submatrix (Fin.castLE h) id with hB
  obtain ⟨W, hW, Z, hZ, hsvd⟩ := exists_svd B
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hsvd
  set σ : ℕ → ℝ := fun i => ((toEuclideanLin B).singularValues i : ℝ) with hσ
  have hsvd' : Wᵀ * B * Z = rectDiagonal σ := by
    rw [hsvd]
    exact rectDiagonal_congr fun i _ _ => by simp [hσ]
  refine ⟨W, hW, Z, hZ, σ, hsvd', mul_mem h𝒰 (padBlock_mem_orthogonalGroup h hW), mul_mem h𝒱 hZ,
    ?_⟩
  -- `M = (B; 0)` in block form
  set e := blockEquiv h with he
  have hMblock : M = (fromRows B (0 : Matrix (Fin (m - n)) (Fin n) ℝ)).submatrix e.symm id := by
    ext i j
    obtain ⟨s, rfl⟩ := e.surjective i
    rw [submatrix_apply, Equiv.symm_apply_apply, id]
    cases s with
    | inl k =>
      rw [fromRows_apply_inl, hB, submatrix_apply, id]
      congr 1
    | inr k =>
      rw [fromRows_apply_inr, Matrix.zero_apply]
      exact h0 _ j (by rw [coe_blockEquiv_inr]; exact Nat.le_add_right n k)
  -- the assembly `diag(W, I)ᵀ (B; 0) Z = (Wᵀ B Z; 0)`
  have hassemble : (𝒰 * padBlock h W)ᵀ * A * (𝒱 * Z) = (padBlock h W)ᵀ * M * Z := by
    rw [transpose_mul, hM]
    simp only [Matrix.mul_assoc]
  have hX : ∀ X : Matrix (Fin n ⊕ Fin (m - n)) (Fin n) ℝ,
      X.submatrix e.symm id * Z = (X * Z).submatrix e.symm id := fun X =>
    (submatrix_mul X Z e.symm id id Function.bijective_id).symm
  rw [hassemble, hMblock, padBlock, transpose_submatrix, submatrix_mul_equiv, fromBlocks_transpose,
    transpose_zero, transpose_zero, transpose_one, fromBlocks_mul_fromRows]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [← he, hX, fromRows_mul, hsvd', Matrix.zero_mul]
  ext i j
  obtain ⟨s, rfl⟩ := e.surjective i
  rw [submatrix_apply, Equiv.symm_apply_apply, id, rectDiagonal_apply]
  cases s with
  | inl k =>
    rw [fromRows_apply_inl, rectDiagonal_apply, coe_blockEquiv_inl]
  | inr k =>
    rw [fromRows_apply_inr, Matrix.zero_apply, coe_blockEquiv_inr]
    have : n + (k : ℕ) ≠ j := by have := j.isLt; omega
    rw [ite_eq_right this]

end QuarteroniSaccoSaleri.Chapter05
