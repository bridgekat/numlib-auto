/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.LinearAlgebra.Sparse.Pattern
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section07

/-!
# Quarteroni, Sacco and Saleri, Section 3.9: Sparse matrices

This module formalizes Section 3.9 of [quarteroni2000numerical]. The sparsity pattern of a square
matrix $A$ is described by its oriented graph $G(A)$, with an arrow from $i$ to $j$ when
$a_{ij} \neq 0$, and by its envelope $E(A)$ of (3.59), the strictly lower positions of each row from
its first nonzero entry to the diagonal. For a symmetric positive definite matrix, the fill-in of
the Cholesky factor stays inside the envelope (3.60). Substructuring splits the unknowns into
interior and interface groups: eliminating the interior unknowns leaves a system on the Schur
complement (3.62)–(3.63), which for a symmetric positive definite matrix is no worse conditioned
than the original system (Remark 3.6).

The proofs specialize the backbone modules `Numlib.LinearAlgebra.Sparse.Pattern` (the adjacency
digraph `Matrix.adjDigraph`), `Numlib.LinearAlgebra.Matrix.LU` (the envelope `Matrix.envelope` and
its preservation `Matrix.IsLU.envelope_eq`), `Numlib.LinearAlgebra.Matrix.Cholesky` and
`Numlib.LinearAlgebra.Matrix.SchurComplement` (the block factorization
`Matrix.fromBlocks_eq_mul_schurComplement` behind substructuring).

## Main definitions

* Section 3.9, `QuarteroniSaccoSaleri.Chapter03.adjacencyGraph`: the oriented graph $G(A)$.
* (3.59), `QuarteroniSaccoSaleri.Chapter03.equation_3_59`: the envelope $E(A)$.

## Main results

* Section 3.9, `QuarteroniSaccoSaleri.Chapter03.adjacencyGraph_adj`: $G(A)$ has an arrow from $i$ to
  $j$ if and only if $a_{ij} \neq 0$.
* (3.59), `QuarteroniSaccoSaleri.Chapter03.equation_3_59_iff`: the membership in $E(A)$ spelled out
  with $m_i(A)$.
* (3.60), `QuarteroniSaccoSaleri.Chapter03.equation_3_60`: $E(A) = E(H + H^T)$ for the Cholesky
  factor $H$ of $A$.
* (3.62)–(3.63), `QuarteroniSaccoSaleri.Chapter03.equation_3_63`: substructuring reduces the system
  to the interface system on the Schur complement.
* Remark 3.6, `QuarteroniSaccoSaleri.Chapter03.remark_3_6_schur`: the Schur complement of a
  three-block matrix, and the equivalent interface system.
* Remark 3.6, `QuarteroniSaccoSaleri.Chapter03.remark_3_6_cond`: $K_2(S) \le K_2(A)$ for symmetric
  positive definite $A$.

## Conventions

* The oriented graph $G(A)$ of a square matrix is `Matrix.adjDigraph A`, a `Digraph (Fin n)` with an
  arrow $i \to j$ if and only if $a_{ij} \neq 0$, and a loop at $i$ if and only if $a_{ii} \neq 0$.
  The book defines $G(A)$ also for a rectangular $A \in \mathbb{R}^{m \times n}$, on $\max(m, n)$
  vertices; the section uses only square matrices, and only these are covered.
* The envelope $E(A)$ of (3.59), which the book calls the "convex hull", is `Matrix.envelope A`, a
  set of index pairs. The book's $m_i(A) = i - \min\{j < i : a_{ij} \neq 0\}$ appears in
  `QuarteroniSaccoSaleri.Chapter03.equation_3_59_iff`.
* Block systems are written with `Matrix.fromBlocks` over sum index types. The first substructure
  system (3.62) is `fromBlocks A₁₁ A₁₃ A₁₃ᵀ A₃₃'` on `m₁ ⊕ m₃`. The three-block matrix of Remark 3.6
  is `fromBlocks (fromBlocks A₁₁ 0 0 A₂₂) (fromRows A₁₃ A₂₃) (fromCols A₁₃ᵀ A₂₃ᵀ) A₃₃` on
  `(m₁ ⊕ m₂) ⊕ m₃`.
* The Schur complement of a two-block matrix `fromBlocks B E F C` is $C - FB^{-1}E$, which is
  `Matrix.schurComplement`.

## Deviations from the source

* **Adjacency graph** (scope). The source allows rectangular matrices. The graph and its edge
  characterization here use square matrices.
* **Remark 3.6** (scope). The condition-number comparison allows a general positive definite
  matrix with the stated partition.

## Not formalized

* **The Cuthill–McKee and nested dissection reorderings** (Sections 3.9.1 and 3.9.3), which state no
  theorem.
* **The operation count (3.61)**, for which there is no cost model.
* **Remark 3.5**, which is prose.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### The graph of a matrix and the envelope -/

/-- **Section 3.9** of [quarteroni2000numerical], the **oriented graph** $G(A)$ of
$A \in \mathbb{R}^{n \times n}$. Its vertices are the indices $1, \ldots, n$, and a path
directed from $i$ to $j$ exists if and only if $a_{ij} \neq 0$. For $a_{ii} \neq 0$, the path
from $i$ to itself is a loop.

The graph is `Matrix.adjDigraph A`.

**Scope.** The source allows rectangular matrices and indexes the vertices up to the larger
dimension. This definition treats square matrices. -/
def adjacencyGraph (A : Matrix (Fin n) (Fin n) ℝ) : Digraph (Fin n) := adjDigraph A

/-- **Section 3.9** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$. The graph
$G(A)$ has an arrow from $i$ to $j$ if and only if $a_{ij} \neq 0$.

The proof uses `Matrix.adjDigraph_adj`.

**Scope.** This characterization is for the square-matrix version of the graph. -/
theorem adjacencyGraph_adj (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (adjacencyGraph A).Adj i j ↔ A i j ≠ 0 :=
  adjDigraph_adj

/-- **Equation (3.59)** of [quarteroni2000numerical], the **envelope** of
$A \in \mathbb{R}^{n \times n}$, which the book calls its "convex hull". With
$$m_i(A) = i - \min\{j < i : a_{ij} \neq 0\},$$
the envelope is
$$E(A) = \{(i, j) : 0 < i - j \le m_i(A)\},$$
the strictly lower positions of each row from its first nonzero entry to the diagonal.

The envelope is `Matrix.envelope A`. The membership is spelled out in
`QuarteroniSaccoSaleri.Chapter03.equation_3_59_iff`.

**Reading.** Empty lower row support contributes no envelope entries.
-/
def equation_3_59 (A : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n × Fin n) := envelope A

/-- **Equation (3.59)** of [quarteroni2000numerical], spelled out. Let
$A \in \mathbb{R}^{n \times n}$. A pair $(i, j)$ is in $E(A)$ if and only if the set
$\{j_0 < i : a_{ij_0} \neq 0\}$ is nonempty and
$$0 < i - j \le m_i(A) = i - \min\{j_0 < i : a_{ij_0} \neq 0\}.$$
A row whose strictly lower part is zero contributes nothing to the envelope.

**Reading.** Spells out the empty-support convention absent from the formula.
-/
theorem equation_3_59_iff (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (i, j) ∈ equation_3_59 A ↔
      ∃ h : (univ.filter fun j₀ => j₀ < i ∧ A i j₀ ≠ 0).Nonempty,
        0 < (i : ℕ) - j ∧
          (i : ℕ) - j ≤ i - (univ.filter fun j₀ => j₀ < i ∧ A i j₀ ≠ 0).min' h := by
  change (j < i ∧ ∃ j₀ ≤ j, A i j₀ ≠ 0) ↔ _
  constructor
  · rintro ⟨hji, j₀, hj₀, hA⟩
    have hmem : j₀ ∈ univ.filter fun j₀ => j₀ < i ∧ A i j₀ ≠ 0 :=
      mem_filter.2 ⟨mem_univ _, hj₀.trans_lt hji, hA⟩
    refine ⟨⟨j₀, hmem⟩, ?_, ?_⟩
    · have := Fin.lt_def.1 hji
      omega
    · have h1 := Fin.le_def.1 ((Finset.min'_le _ _ hmem).trans hj₀)
      have h2 := Fin.lt_def.1 hji
      omega
  · rintro ⟨h, h1, h2⟩
    obtain ⟨hmin, hA⟩ := (mem_filter.1 (Finset.min'_mem _ h)).2
    have hmin' := Fin.lt_def.1 hmin
    refine ⟨Fin.lt_def.2 (by omega), _, Fin.le_def.2 (by omega), hA⟩

/-- Two matrices with the same strictly lower zero pattern have the same envelope. -/
private theorem envelope_congr {B C : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j : Fin n, j < i → (B i j = 0 ↔ C i j = 0)) : envelope B = envelope C := by
  ext ⟨i, j⟩
  simp only [envelope, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hij, j₀, hj₀, hne⟩ <;> refine ⟨hij, j₀, hj₀, ?_⟩
  · exact fun h0 => hne ((h i j₀ (hj₀.trans_lt hij)).2 h0)
  · exact fun h0 => hne ((h i j₀ (hj₀.trans_lt hij)).1 h0)

/-- **Equation (3.60)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$ be
symmetric positive definite, with Cholesky factor $H$ (Theorem 3.6, $A = H^T H$). Then
$$E(A) = E(H + H^T).$$
So the fill-in is confined within the envelope of $A$, and it reaches the boundary of the
envelope.

The book compares the fill-in of $H$ with $A$ through $E(H + H^T)$. The strictly lower part of
$H + H^T$ is that of $H^T = LD^{1/2}$, where $L$ is the unit lower factor of Theorem 3.4, and
$E(L) = E(A)$ is `Matrix.IsLU.envelope_eq`. -/
theorem equation_3_60 {A H : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hH : IsCholesky A H) :
    equation_3_59 A = equation_3_59 (H + Hᵀ) := by
  have hLU := hH.isLU
  rw [conjTranspose_eq_transpose_of_trivial] at hLU
  have henv := hLU.envelope_eq hA.isUnit_strictLeadingPrincipalSubmatrix
  change envelope A = envelope (H + Hᵀ)
  rw [← henv]
  refine envelope_congr fun i j hji => ?_
  rw [mul_diagonal, transpose_apply, Matrix.add_apply, hH.isUpperTriangular hji, zero_add,
    transpose_apply, mul_eq_zero, inv_eq_zero, or_iff_left (hH.diag_ne_zero j)]

/-! ### Substructuring and the Schur complement -/

section Substructuring

variable {m₁ m₂ m₃ : ℕ}

/-- Two functions `Sum.elim f g` and `Sum.elim f' g'` are equal if and only if $f = f'$ and
$g = g'$. -/
private theorem sum_elim_eq_iff {α β γ : Type*} {f f' : α → γ} {g g' : β → γ} :
    Sum.elim f g = Sum.elim f' g' ↔ f = f' ∧ g = g' := by
  rw [funext_iff, Sum.forall, funext_iff, funext_iff]
  rfl

/-- Let $B$ be nonsingular. The two-block system
$$\begin{bmatrix} B & E \\ F & C \end{bmatrix} \begin{bmatrix} x_1 \\ x_3 \end{bmatrix} =
  \begin{bmatrix} b_1 \\ b_3 \end{bmatrix}$$
is equivalent to the Schur complement system $(C - FB^{-1}E) x_3 = b_3 - FB^{-1} b_1$ together
with $Bx_1 = b_1 - Ex_3$. -/
private theorem fromBlocks_mulVec_eq_iff {l o : Type*} [Fintype l] [Fintype o] [DecidableEq l]
    {B : Matrix l l ℝ} {E : Matrix l o ℝ} {F : Matrix o l ℝ} {C : Matrix o o ℝ}
    (hB : IsUnit B) (x₁ b₁ : l → ℝ) (x₃ b₃ : o → ℝ) :
    fromBlocks B E F C *ᵥ Sum.elim x₁ x₃ = Sum.elim b₁ b₃ ↔
      (fromBlocks B E F C).schurComplement *ᵥ x₃ = b₃ - F *ᵥ (B⁻¹ *ᵥ b₁) ∧
        B *ᵥ x₁ = b₁ - E *ᵥ x₃ := by
  have hBd := (isUnit_iff_isUnit_det B).1 hB
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, sum_elim_eq_iff,
    schurComplement_fromBlocks]
  have key : B *ᵥ x₁ = b₁ - E *ᵥ x₃ ↔ x₁ = B⁻¹ *ᵥ (b₁ - E *ᵥ x₃) := by
    constructor
    · intro h
      rw [← h, mulVec_mulVec, nonsing_inv_mul _ hBd, one_mulVec]
    · intro h
      rw [h, mulVec_mulVec, mul_nonsing_inv _ hBd, one_mulVec]
  constructor
  · rintro ⟨h1, h3⟩
    have h1' : B *ᵥ x₁ = b₁ - E *ᵥ x₃ := by rw [← h1, add_sub_cancel_right]
    refine ⟨?_, h1'⟩
    rw [key.1 h1'] at h3
    rw [← h3]
    simp only [sub_mulVec, mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc]
    abel
  · rintro ⟨h3, h1⟩
    refine ⟨by rw [h1, sub_add_cancel], ?_⟩
    rw [key.1 h1]
    simp only [sub_mulVec, mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc] at h3 ⊢
    rw [eq_sub_iff_add_eq] at h3
    rw [← h3]
    abel

/-- **Equations (3.62)–(3.63)** of [quarteroni2000numerical], decomposition into substructures.
Consider the system of the first substructure
$$\begin{bmatrix} A_{11} & A_{13} \\ A_{13}^T & A_{33}' \end{bmatrix} \begin{bmatrix} x_1 \\ x_3
  \end{bmatrix} = \begin{bmatrix} b_1 \\ b_3 \end{bmatrix},$$
with $A_{11} \in \mathbb{R}^{m_1 \times m_1}$, $A_{13} \in \mathbb{R}^{m_1 \times m_3}$ and
$A_{33}' \in \mathbb{R}^{m_3 \times m_3}$, and let $A_{11} = H_{11}^T H_{11}$ with $H_{11}$
nonsingular. Let $H_{21} = H_{11}^{-T} A_{13}$ and $c_1 = H_{11}^{-T} b_1$. Then
$$H_{21}^T H_{21} = A_{13}^T A_{11}^{-1} A_{13}, \qquad H_{21}^T c_1 = A_{13}^T A_{11}^{-1}
  b_1,$$
and $A_{33}''' = A_{33}' - H_{21}^T H_{21}$ is the Schur complement of the block matrix. The
system is equivalent to the interface system $A_{33}''' x_3 = b_3'''$ with
$b_3''' = b_3 - H_{21}^T c_1$, together with $A_{11} x_1 = b_1 - A_{13} x_3$, which gives $x_1$
once $x_3$ is known.

The matrix $A_{33}'$ is the argument `A₃₃`. The proof uses `Matrix.schurComplement` and
`Matrix.fromBlocks_eq_mul_schurComplement`. -/
theorem equation_3_63 {A₁₁ H₁₁ : Matrix (Fin m₁) (Fin m₁) ℝ} (hH : IsUnit H₁₁)
    (hA₁₁ : A₁₁ = H₁₁ᵀ * H₁₁) (A₁₃ : Matrix (Fin m₁) (Fin m₃) ℝ)
    (A₃₃ : Matrix (Fin m₃) (Fin m₃) ℝ) (x₁ b₁ : Fin m₁ → ℝ) (x₃ b₃ : Fin m₃ → ℝ) :
    (H₁₁ᵀ⁻¹ * A₁₃)ᵀ * (H₁₁ᵀ⁻¹ * A₁₃) = A₁₃ᵀ * A₁₁⁻¹ * A₁₃ ∧
    (H₁₁ᵀ⁻¹ * A₁₃)ᵀ *ᵥ (H₁₁ᵀ⁻¹ *ᵥ b₁) = A₁₃ᵀ *ᵥ (A₁₁⁻¹ *ᵥ b₁) ∧
    (fromBlocks A₁₁ A₁₃ A₁₃ᵀ A₃₃).schurComplement = A₃₃ - (H₁₁ᵀ⁻¹ * A₁₃)ᵀ * (H₁₁ᵀ⁻¹ * A₁₃) ∧
    (fromBlocks A₁₁ A₁₃ A₁₃ᵀ A₃₃ *ᵥ Sum.elim x₁ x₃ = Sum.elim b₁ b₃ ↔
      (A₃₃ - (H₁₁ᵀ⁻¹ * A₁₃)ᵀ * (H₁₁ᵀ⁻¹ * A₁₃)) *ᵥ x₃ =
          b₃ - (H₁₁ᵀ⁻¹ * A₁₃)ᵀ *ᵥ (H₁₁ᵀ⁻¹ *ᵥ b₁) ∧
        A₁₁ *ᵥ x₁ = b₁ - A₁₃ *ᵥ x₃) := by
  have hHt : IsUnit H₁₁ᵀ := (isUnit_transpose H₁₁).2 hH
  have hA₁₁inv : A₁₁⁻¹ = H₁₁⁻¹ * H₁₁ᵀ⁻¹ := by
    rw [hA₁₁, Matrix.mul_inv_rev]
  have hkey : (H₁₁ᵀ⁻¹ * A₁₃)ᵀ * H₁₁ᵀ⁻¹ = A₁₃ᵀ * A₁₁⁻¹ := by
    rw [transpose_mul, transpose_nonsing_inv, transpose_transpose, hA₁₁inv, Matrix.mul_assoc]
  have hA₁₁u : IsUnit A₁₁ := by rw [hA₁₁]; exact hHt.mul hH
  have h1 : (H₁₁ᵀ⁻¹ * A₁₃)ᵀ * (H₁₁ᵀ⁻¹ * A₁₃) = A₁₃ᵀ * A₁₁⁻¹ * A₁₃ := by
    rw [← Matrix.mul_assoc, hkey]
  have h2 : (H₁₁ᵀ⁻¹ * A₁₃)ᵀ *ᵥ (H₁₁ᵀ⁻¹ *ᵥ b₁) = A₁₃ᵀ *ᵥ (A₁₁⁻¹ *ᵥ b₁) := by
    rw [mulVec_mulVec, hkey, mulVec_mulVec]
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [schurComplement_fromBlocks, h1]
  · rw [fromBlocks_mulVec_eq_iff hA₁₁u, schurComplement_fromBlocks, h1, h2, mulVec_mulVec]

/-- **Remark 3.6** of [quarteroni2000numerical], the Schur complement. Let
$$A = \begin{bmatrix} A_{11} & 0 & A_{13} \\ 0 & A_{22} & A_{23} \\ A_{13}^T & A_{23}^T & A_{33}
  \end{bmatrix}$$
with $A_{11}$ and $A_{22}$ nonsingular. Then the Schur complement of the leading $2 \times 2$
block diagonal part is
$$S = A_{33} - A_{13}^T A_{11}^{-1} A_{13} - A_{23}^T A_{22}^{-1} A_{23},$$
and the system $Ax = b$ is equivalent to the interface system
$$S x_3 = b_3 - A_{13}^T A_{11}^{-1} b_1 - A_{23}^T A_{22}^{-1} b_2$$
together with the two systems of reduced size $A_{11} x_1 = b_1 - A_{13} x_3$ and
$A_{22} x_2 = b_2 - A_{23} x_3$.

The proof uses `Matrix.fromBlocks_eq_mul_schurComplement`, and Mathlib's
`Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff` inverts the block diagonal. -/
theorem remark_3_6_schur {A₁₁ : Matrix (Fin m₁) (Fin m₁) ℝ} {A₂₂ : Matrix (Fin m₂) (Fin m₂) ℝ}
    (h₁₁ : IsUnit A₁₁) (h₂₂ : IsUnit A₂₂) (A₁₃ : Matrix (Fin m₁) (Fin m₃) ℝ)
    (A₂₃ : Matrix (Fin m₂) (Fin m₃) ℝ) (A₃₃ : Matrix (Fin m₃) (Fin m₃) ℝ) (x₁ b₁ : Fin m₁ → ℝ)
    (x₂ b₂ : Fin m₂ → ℝ) (x₃ b₃ : Fin m₃ → ℝ) :
    Matrix.schurComplement
        (fromBlocks (fromBlocks A₁₁ 0 0 A₂₂) (fromRows A₁₃ A₂₃) (fromCols A₁₃ᵀ A₂₃ᵀ) A₃₃) =
        A₃₃ - A₁₃ᵀ * A₁₁⁻¹ * A₁₃ - A₂₃ᵀ * A₂₂⁻¹ * A₂₃ ∧
      (fromBlocks (fromBlocks A₁₁ 0 0 A₂₂) (fromRows A₁₃ A₂₃) (fromCols A₁₃ᵀ A₂₃ᵀ) A₃₃ *ᵥ
          Sum.elim (Sum.elim x₁ x₂) x₃ = Sum.elim (Sum.elim b₁ b₂) b₃ ↔
        (A₃₃ - A₁₃ᵀ * A₁₁⁻¹ * A₁₃ - A₂₃ᵀ * A₂₂⁻¹ * A₂₃) *ᵥ x₃ =
            b₃ - A₁₃ᵀ *ᵥ (A₁₁⁻¹ *ᵥ b₁) - A₂₃ᵀ *ᵥ (A₂₂⁻¹ *ᵥ b₂) ∧
          A₁₁ *ᵥ x₁ = b₁ - A₁₃ *ᵥ x₃ ∧ A₂₂ *ᵥ x₂ = b₂ - A₂₃ *ᵥ x₃) := by
  have hBinv : (fromBlocks A₁₁ 0 0 A₂₂)⁻¹ = fromBlocks A₁₁⁻¹ 0 0 A₂₂⁻¹ := by
    rw [inv_fromBlocks_zero₁₂_of_isUnit_iff _ _ _ (iff_of_true h₁₁ h₂₂), Matrix.mul_zero,
      Matrix.zero_mul, neg_zero]
  have hBu : IsUnit (fromBlocks A₁₁ 0 0 A₂₂) := by
    rw [isUnit_iff_isUnit_det, det_fromBlocks_zero₁₂]
    exact ((isUnit_iff_isUnit_det _).1 h₁₁).mul ((isUnit_iff_isUnit_det _).1 h₂₂)
  have hS : (fromBlocks (fromBlocks A₁₁ 0 0 A₂₂) (fromRows A₁₃ A₂₃) (fromCols A₁₃ᵀ A₂₃ᵀ)
      A₃₃).schurComplement = A₃₃ - A₁₃ᵀ * A₁₁⁻¹ * A₁₃ - A₂₃ᵀ * A₂₂⁻¹ * A₂₃ := by
    rw [schurComplement_fromBlocks, hBinv, fromCols_mul_fromBlocks, Matrix.mul_zero,
      Matrix.mul_zero, add_zero, zero_add, fromCols_mul_fromRows, sub_sub]
  refine ⟨hS, ?_⟩
  rw [fromBlocks_mulVec_eq_iff hBu, hS, hBinv]
  have e1 : fromCols A₁₃ᵀ A₂₃ᵀ *ᵥ (fromBlocks A₁₁⁻¹ 0 0 A₂₂⁻¹ *ᵥ Sum.elim b₁ b₂) =
      A₁₃ᵀ *ᵥ (A₁₁⁻¹ *ᵥ b₁) + A₂₃ᵀ *ᵥ (A₂₂⁻¹ *ᵥ b₂) := by
    rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec,
      Matrix.zero_mulVec, add_zero, zero_add, fromCols_mulVec_sumElim]
  have e2 : fromBlocks A₁₁ 0 0 A₂₂ *ᵥ Sum.elim x₁ x₂ = Sum.elim b₁ b₂ - fromRows A₁₃ A₂₃ *ᵥ x₃ ↔
      A₁₁ *ᵥ x₁ = b₁ - A₁₃ *ᵥ x₃ ∧ A₂₂ *ᵥ x₂ = b₂ - A₂₃ *ᵥ x₃ := by
    rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec,
      Matrix.zero_mulVec, add_zero, zero_add, fromRows_mulVec]
    have hsub : Sum.elim b₁ b₂ - Sum.elim (A₁₃ *ᵥ x₃) (A₂₃ *ᵥ x₃) =
        Sum.elim (b₁ - A₁₃ *ᵥ x₃) (b₂ - A₂₃ *ᵥ x₃) := by
      ext (k | k) <;> rfl
    rw [hsub, sum_elim_eq_iff]
  rw [e1, e2, sub_sub b₃]

open scoped Matrix.Norms.L2Operator in
/-- **Remark 3.6** of [quarteroni2000numerical], the conditioning of the interface system. Let $A$
be a symmetric positive definite matrix partitioned into $3 \times 3$ blocks, and let $S$ be the
Schur complement of its leading $2 \times 2$ block part. Then the system on $S$ is no more ill
conditioned than the system on $A$:
$$K_2(S) \le K_2(A).$$

Here $K_2$ is `NormedRing.condNumber` for Mathlib's scoped `L2Operator` matrix norm. It is the
chapter's `QuarteroniSaccoSaleri.Chapter03.condNumber 2` transported to a sum index type
(`QuarteroniSaccoSaleri.Chapter03.condNumber_two_eq`). The theorem holds for every symmetric
positive definite $A$ on this index type, and `QuarteroniSaccoSaleri.Chapter03.remark_3_6_schur`
identifies $S$ with $A_{33} - A_{13}^T A_{11}^{-1} A_{13} - A_{23}^T A_{22}^{-1} A_{23}$ when
$A$ has the shape of Remark 3.6. The proof specializes
`Matrix.PosDef.condNumber_schurComplement_le`, which is Axelsson's Lemma 3.12 without
interlacing: $0 \le S \le A_{33}$ in the Loewner order gives $\|S\|_2 \le \|A\|_2$, and
$S^{-1} = (A^{-1})_{33}$ gives $\|S^{-1}\|_2 \le \|A^{-1}\|_2$, because a principal submatrix
has the smaller spectral norm.

**Scope.** The bound applies to any positive definite matrix with the indicated partition,
including nonzero off-diagonal interactions between the first two blocks. -/
theorem remark_3_6_cond
    {A : Matrix ((Fin m₁ ⊕ Fin m₂) ⊕ Fin m₃) ((Fin m₁ ⊕ Fin m₂) ⊕ Fin m₃) ℝ} (hA : A.PosDef) :
    NormedRing.condNumber A.schurComplement ≤ NormedRing.condNumber A := by
  rw [NormedRing.condNumber, NormedRing.condNumber, ← nonsing_inv_eq_ringInverse,
    ← nonsing_inv_eq_ringInverse]
  exact hA.condNumber_schurComplement_le

end Substructuring

end QuarteroniSaccoSaleri.Chapter03
