/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Sparse.Pattern

/-!
# Diagonally dominant matrices

Let $A = (a_{ij})$ be a square matrix over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. The matrix $A$
is **strictly diagonally dominant by rows** if $\sum_{j \ne i} |a_{ij}| < |a_{ii}|$ for every row
$i$, and **weakly diagonally dominant by rows** if $\sum_{j \ne i} |a_{ij}| \le |a_{ii}|$ for every
row $i$; the column forms sum over $i \ne j$ in each column $j$. The matrix $A$ is **irreducibly
diagonally dominant** if it is irreducible, weakly dominant in every row, and strictly dominant in
at least one row. This module proves the nonsingularity theorems for these matrices, following
[saad2003iterative] Definition 4.5, Theorem 4.7 and Corollary 4.8, [kress1998numerical] (4.4)–(4.5)
and Theorem 4.7, and [quarteroni2000numerical] Definition 1.24.

Besides nonsingularity, the module proves that a Hermitian strictly dominant matrix with positive
diagonal is positive definite, that dominance with a margin $\delta$ gives $\delta \|x\| \le \|Ax\|$
in the $1$-norm and the $\infty$-norm (Varah's bound), and that one step of Gaussian elimination
preserves weak dominance.

## Main definitions

* `Matrix.IsStrictDiagDominant`, `Matrix.IsStrictColDiagDominant`: strict diagonal dominance by rows
  and by columns.
* `Matrix.IsDiagDominant`, `Matrix.IsColDiagDominant`: weak diagonal dominance by rows and by
  columns, [quarteroni2000numerical] Definition 1.24; the strict and the irreducible forms both
  imply it.
* `Matrix.IsAbsDiagDominant`: weak row dominance with the absolute value of a lattice-ordered group
  in place of the norm, for the ordered fields of floating-point analyses.
* `Matrix.IsIrreduciblyDiagDominant`, `Matrix.IsIrreduciblyColDiagDominant`: irreducible diagonal
  dominance by rows and by columns, [saad2003iterative] Definition 4.5.

## Main results

* `Matrix.IsStrictDiagDominant.isUnit`, `Matrix.IsStrictColDiagDominant.isUnit`: a strictly
  diagonally dominant matrix is nonsingular.
* `Matrix.IsStrictDiagDominant.isUnit_diagPart`: the diagonal part of a strictly row dominant matrix
  is nonsingular.
* `Matrix.IsPatternIrreducible.norm_diag_eq_of_mulVec_eq_zero`: if $B$ is weakly row dominant, has a
  nonzero entry wherever an irreducible $A$ has one off the diagonal, and has a nonzero kernel
  vector, then every row of $B$ satisfies $\sum_{j \ne i} |b_{ij}| = |b_{ii}|$.
* `Matrix.IsPatternIrreducible.isUnit_of_dominant`, `Matrix.IsIrreduciblyDiagDominant.isUnit`: an
  irreducibly diagonally dominant matrix is nonsingular, [saad2003iterative] Corollary 4.8.
* `Matrix.IsPatternIrreducible.norm_sub_eq_of_mem_frontier`: an eigenvalue of an irreducible matrix
  on the boundary of the union of the Gershgorin discs lies on the boundary of every disc,
  [saad2003iterative] Theorem 4.7.
* `Matrix.IsStrictDiagDominant.posDef`: a Hermitian strictly row dominant matrix with positive
  diagonal is positive definite ([quarteroni2000numerical] §1.12).
* `Matrix.mul_sum_norm_le_sum_norm_mulVec_of_colDiagDominantMargin`,
  `Matrix.mul_sup_norm_le_sup_norm_mulVec_of_diagDominantMargin`: dominance with a margin $\delta$
  by columns gives $\delta \|x\|_1 \le \|Ax\|_1$, and by rows gives
  $\delta \|x\|_\infty \le \|Ax\|_\infty$; hence $\|A^{-1}\| \le 1/\delta$ in the induced norm
  ([golub2013matrix] Theorem 4.1.2 and its row form).
* `Matrix.IsColDiagDominant.schurComplementSingle`, `Matrix.IsDiagDominant.schurComplementSingle`:
  one step of Gaussian elimination preserves weak column and weak row dominance
  ([higham2002accuracy] Theorem 13.8 with $1 \times 1$ blocks).
* `Matrix.IsDiagDominant.diag_ne_zero_of_isUnit`: a nonsingular weakly row dominant matrix has no
  zero on its diagonal.
* `Matrix.isStrictDiagDominant_complexify`, `Matrix.isIrreduciblyDiagDominant_complexify`,
  `Matrix.isPatternIrreducible_complexify`: the complexification of a real matrix keeps all three
  properties.

## Proof outline

The irreducible theory rests on one argument. Let $Bx = 0$ with $x \ne 0$, and let $i$ be a row
where $|x_i|$ is maximal. Then weak dominance in row $i$ must hold with equality, and
$|x_j| = |x_i|$ at every $j$ with $b_{ij} \ne 0$. Along the strongly connected graph of $A$, the
maximum, and with it the equality, spreads to every row. A strictly dominant row then excludes a
kernel vector, and a boundary point of the Gershgorin discs gives such a $B = \mu I - A$.

## Implementation notes

* This is the matrix-analytic layer only: nothing here mentions a splitting or an iteration. The
  convergence of the Jacobi and Gauss–Seidel iterations for these matrices, the explicit
  $\|\cdot\|_\infty$ contraction constants and the Gershgorin arguments for pencils are in
  `Numlib.Stationary.DiagDominant`, which builds on this module and on
  `Numlib.Stationary.Splitting`. With this split, `Numlib.LinearAlgebra.Matrix.MMatrix` and the LU
  factorization can name the dominance predicates without importing the theory of stationary
  iterations.
* The entries are measured with the norm of an `RCLike` field, which is the absolute value or the
  modulus. Irreducibility is `Matrix.IsPatternIrreducible` of `Numlib.LinearAlgebra.Sparse.Pattern`,
  the strong connectivity of the graph of nonzero entries.
* The irreducible results are stated for a matrix $B$ dominated off the diagonal by an irreducible
  $A$, because the convergence proofs apply them to a pencil (the matrix with its diagonal, or its
  lower triangle, scaled by an eigenvalue) and not to the matrix itself.
* The margin results take the hypothesis $\delta \le |a_{jj}| - \sum_{i \ne j} |a_{ij}|$ directly,
  not a dominance predicate.
* The two Schur complement results are the two facts behind the existence of the LU factorization of
  a nonsingular diagonally dominant matrix ([quarteroni2000numerical] Property 3.2,
  [higham2002accuracy] Theorem 9.9) in `Numlib.LinearAlgebra.Matrix.LU`.
* `Matrix.isPatternIrreducible_complexify` is here, and not in `Numlib.LinearAlgebra.Sparse.Pattern`
  or `Numlib.LinearAlgebra.Matrix.Complexify`, because this is the first module that imports both.
-/

open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Spectrum

variable {K : Type*} [Field K]

/-- Let $M$ be a square matrix over a field $K$. Every point $\mu$ of the spectrum of $M$ is an
eigenvalue: there is a vector $x \ne 0$ with $(\mu I - M) x = 0$. -/
theorem exists_mulVec_eq_zero_of_mem_spectrum {M : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K M) : ∃ x ≠ 0, (μ • (1 : Matrix n n K) - M) *ᵥ x = 0 := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not] at hμ
  exact Matrix.exists_mulVec_eq_zero_iff.mpr hμ

end Spectrum

variable {𝕜 : Type*} [RCLike 𝕜]

section Strict

/-- A square matrix $A$ over $\mathbb{K}$ is **strictly diagonally dominant by rows** if $$\sum_{j
\ne i} |a_{ij}| < |a_{ii}| \quad \text{for every row } i.$$
-/
def IsStrictDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖

/-- A square matrix $A$ over $\mathbb{K}$ is **strictly diagonally dominant by columns** if
$$\sum_{i \ne j} |a_{ij}| < |a_{jj}| \quad \text{for every column } j.$$
-/
def IsStrictColDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ j, ∑ i ∈ Finset.univ.erase j, ‖A i j‖ < ‖A j j‖

/-- A square matrix $A$ is strictly diagonally dominant by columns if and only if $A^T$ is strictly
diagonally dominant by rows.

This holds by definition. Along it, the column criterion for the Jacobi iteration follows from
the row criterion. -/
theorem IsStrictColDiagDominant.transpose_iff (A : Matrix n n 𝕜) :
    A.transpose.IsStrictDiagDominant ↔ A.IsStrictColDiagDominant := Iff.rfl

/-- If $A$ is strictly diagonally dominant by rows, then $a_{ii} \ne 0$ for every $i$, since
$|a_{ii}|$ is greater than a sum of nonnegative numbers. -/
theorem IsStrictDiagDominant.diag_ne_zero {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) (i : n) :
    A i i ≠ 0 :=
  norm_pos_iff.mp (lt_of_le_of_lt (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hA i))

/-- If $A$ is strictly diagonally dominant by rows, then its diagonal part
$\operatorname{diag}(a_{11}, \dots, a_{nn})$ is nonsingular.

So the Jacobi, Gauss–Seidel and SOR splittings of $A$ (`Numlib.Stationary.Splitting`) are
defined. Every convergence statement about them carries this hypothesis. -/
theorem IsStrictDiagDominant.isUnit_diagPart {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) :
    IsUnit (diagPart A) :=
  (isUnit_diagPart_iff A).mpr hA.diag_ne_zero

/-- A square matrix $A$ over $\mathbb{K}$ that is strictly diagonally dominant by rows is
nonsingular. This is Theorem 4.6 of [saad2003iterative]; see also [kress1998numerical].

The proof is Mathlib's `Matrix.det_ne_zero_of_sum_row_lt_diag`. -/
theorem IsStrictDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) :
    IsUnit A :=
  (isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr (det_ne_zero_of_sum_row_lt_diag hA))

/-- A square matrix $A$ over $\mathbb{K}$ that is strictly diagonally dominant by columns is
nonsingular.

The transpose of $A$ is strictly dominant by rows, and $\det A^T = \det A$. -/
theorem IsStrictColDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsStrictColDiagDominant) :
    IsUnit A := by
  have h := ((IsStrictColDiagDominant.transpose_iff A).mpr hA).isUnit
  rwa [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det] at h

end Strict

section Irreducible

/-- A square matrix $A$ over $\mathbb{K}$ is **irreducibly diagonally dominant** (by rows) if it is
irreducible, $\sum_{j \ne i} |a_{ij}| \le |a_{ii}|$ for every row $i$, and
$\sum_{j \ne i} |a_{ij}| < |a_{ii}|$ for at least one row $i$. This is Definition 4.5 of
[saad2003iterative].

Under this hypothesis the Gershgorin argument still gives nonsingularity, and the Jacobi and
Gauss–Seidel iterations still converge, with strict dominance in one row instead of all rows.
Irreducibility is `Matrix.IsPatternIrreducible`: the graph of the nonzero entries is strongly
connected. -/
structure IsIrreduciblyDiagDominant (A : Matrix n n 𝕜) : Prop where
  /-- The graph of the nonzero entries of $A$ is strongly connected. -/
  irreducible : A.IsPatternIrreducible
  /-- Every row satisfies $\sum_{j \ne i} |a_{ij}| \le |a_{ii}|$. -/
  dominant : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ‖A i i‖
  /-- At least one row satisfies $\sum_{j \ne i} |a_{ij}| < |a_{ii}|$. -/
  exists_strict : ∃ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖

/-- A square matrix $A$ is **irreducibly diagonally dominant by columns** if $A^T$ is irreducibly
diagonally dominant by rows. This is the column form of Definition 4.5 of [saad2003iterative]. -/
def IsIrreduciblyColDiagDominant (A : Matrix n n 𝕜) : Prop := Aᵀ.IsIrreduciblyDiagDominant

/-- Let $A, B \in \mathbb{K}^{n \times n}$, let $A$ be irreducible, and let $b_{ij} \ne 0$ whenever
$i \ne j$ and $a_{ij} \ne 0$. Suppose that $\sum_{j \ne i} |b_{ij}| \le |b_{ii}|$ for every row
$i$, and that $Bx = 0$ for some $x \ne 0$. Then every row of $B$ is an equality row:
$$|b_{ii}| = \sum_{j \ne i} |b_{ij}| \quad \text{for every } i.$$ This is the form of
[saad2003iterative] Theorem 4.7 that its applications use.

At a row $i$ where $|x_i|$ is maximal, weak dominance must be an equality, and the maximum is
attained again at every $j$ with $b_{ij} \ne 0$. The strong connectivity of $A$ carries the
maximum, and so the equality, to every row. -/
theorem IsPatternIrreducible.norm_diag_eq_of_mulVec_eq_zero {A B : Matrix n n 𝕜}
    (hA : A.IsPatternIrreducible) (hAB : ∀ i j, i ≠ j → A i j ≠ 0 → B i j ≠ 0)
    (hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖B i j‖ ≤ ‖B i i‖)
    {x : n → 𝕜} (hx : x ≠ 0) (hBx : B *ᵥ x = 0) (i : n) :
    ‖B i i‖ = ∑ j ∈ Finset.univ.erase i, ‖B i j‖ := by
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  have hne : Nonempty n := ⟨j₀⟩
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty fun j => ‖x j‖ with hM
  have hle : ∀ j, ‖x j‖ ≤ M := fun j => Finset.le_sup' (fun j => ‖x j‖) (Finset.mem_univ j)
  have hMpos : 0 < M := lt_of_lt_of_le (norm_pos_iff.mpr hj₀) (hle j₀)
  -- the row relation at an index where the maximum modulus is attained
  have hkey : ∀ k, ‖x k‖ = M →
      ‖B k k‖ = (∑ j ∈ Finset.univ.erase k, ‖B k j‖) ∧
        ∀ j ∈ Finset.univ.erase k, B k j ≠ 0 → ‖x j‖ = M := by
    intro k hxk
    have hrow : (∑ j ∈ Finset.univ.erase k, B k j * x j) + B k k * x k = 0 := by
      have hk := congrFun hBx k
      rw [mulVec, dotProduct] at hk
      simpa using (Finset.sum_erase_add Finset.univ (fun j => B k j * x j)
        (Finset.mem_univ k)).trans (by simpa using hk)
    have h1 : ‖B k k‖ * M ≤ ∑ j ∈ Finset.univ.erase k, ‖B k j‖ * ‖x j‖ := by
      have heq : B k k * x k = -∑ j ∈ Finset.univ.erase k, B k j * x j := by
        linear_combination hrow
      calc ‖B k k‖ * M = ‖B k k * x k‖ := by rw [norm_mul, hxk]
        _ = ‖∑ j ∈ Finset.univ.erase k, B k j * x j‖ := by rw [heq, norm_neg]
        _ ≤ ∑ j ∈ Finset.univ.erase k, ‖B k j * x j‖ := norm_sum_le _ _
        _ = ∑ j ∈ Finset.univ.erase k, ‖B k j‖ * ‖x j‖ := by
            exact Finset.sum_congr rfl fun j _ => norm_mul _ _
    have h2 : ∀ j ∈ Finset.univ.erase k, ‖B k j‖ * ‖x j‖ ≤ ‖B k j‖ * M :=
      fun j _ => mul_le_mul_of_nonneg_left (hle j) (norm_nonneg _)
    have h3 : ∑ j ∈ Finset.univ.erase k, ‖B k j‖ * ‖x j‖ ≤
        (∑ j ∈ Finset.univ.erase k, ‖B k j‖) * M := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum h2
    have h4 : ‖B k k‖ = ∑ j ∈ Finset.univ.erase k, ‖B k j‖ := by
      refine le_antisymm ?_ (hdom k)
      exact le_of_mul_le_mul_right (h1.trans h3) hMpos
    refine ⟨h4, fun j hj hBkj => ?_⟩
    have h5 : ∑ j ∈ Finset.univ.erase k, ‖B k j‖ * ‖x j‖ =
        ∑ j ∈ Finset.univ.erase k, ‖B k j‖ * M := by
      refine le_antisymm (Finset.sum_le_sum h2) ?_
      rw [← Finset.sum_mul, ← h4]
      exact h1
    have h6 := (Finset.sum_eq_sum_iff_of_le h2).mp h5 j hj
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hBkj) h6
  -- the maximum is attained everywhere, by irreducibility
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun j => ‖x j‖
  have hall : ∀ j, ‖x j‖ = M := by
    refine hA.forall_of_closed (P := fun j => ‖x j‖ = M) (fun a b ha hab => ?_) (hM.trans hk₀).symm
    rcases eq_or_ne a b with rfl | hab'
    · exact ha
    · exact (hkey a ha).2 b (Finset.mem_erase.mpr ⟨hab'.symm, Finset.mem_univ b⟩)
        (hAB a b hab' hab)
  exact (hkey i (hall i)).1

/-- Let $A, B \in \mathbb{K}^{n \times n}$, let $A$ be irreducible, and let $b_{ij} \ne 0$ whenever
$i \ne j$ and $a_{ij} \ne 0$. If $\sum_{j \ne i} |b_{ij}| \le |b_{ii}|$ for every row $i$, with
strict inequality for at least one row, then $B$ is nonsingular. With $B = A$ this is
**Corollary 4.8** of [saad2003iterative].

A nonzero kernel vector would make every row an equality row, by
`Matrix.IsPatternIrreducible.norm_diag_eq_of_mulVec_eq_zero`, against the strict row. The
general $B$ is the form that the convergence proofs of `Numlib.Stationary.DiagDominant` use. -/
theorem IsPatternIrreducible.isUnit_of_dominant {A B : Matrix n n 𝕜} (hA : A.IsPatternIrreducible)
    (hAB : ∀ i j, i ≠ j → A i j ≠ 0 → B i j ≠ 0)
    (hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖B i j‖ ≤ ‖B i i‖)
    (hstrict : ∃ i, ∑ j ∈ Finset.univ.erase i, ‖B i j‖ < ‖B i i‖) : IsUnit B := by
  obtain ⟨i, hi⟩ := hstrict
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨x, hx, hBx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hi.ne' (hA.norm_diag_eq_of_mulVec_eq_zero hAB hdom hx hBx i)

/-- An irreducibly diagonally dominant matrix is nonsingular. This is Corollary 4.8 of
[saad2003iterative]. -/
theorem IsIrreduciblyDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsIrreduciblyDiagDominant) :
    IsUnit A :=
  hA.irreducible.isUnit_of_dominant (fun _ _ _ hij => hij) hA.dominant hA.exists_strict

/-- If $A$ is irreducibly diagonally dominant, then $a_{ii} \ne 0$ for every $i$.

For $n \ge 2$, a zero diagonal entry would force its whole row to vanish, which irreducibility
forbids. For $n = 1$, the strict row is the diagonal entry itself. -/
theorem IsIrreduciblyDiagDominant.diag_ne_zero {A : Matrix n n 𝕜}
    (hA : A.IsIrreduciblyDiagDominant) (i : n) : A i i ≠ 0 := by
  intro h0
  have hzero : ∀ j, A i j = 0 := by
    have hsum := hA.dominant i
    rw [h0, norm_zero] at hsum
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => norm_nonneg (A i j)).mp
      (le_antisymm hsum (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    intro j
    rcases eq_or_ne j i with rfl | hj
    · exact h0
    · exact norm_eq_zero.mp (hall j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))
  have hsub : ∀ j : n, j = i :=
    hA.irreducible.forall_of_closed (P := fun j => j = i)
      (fun a b ha hab => absurd (hzero b) (ha ▸ hab)) rfl
  obtain ⟨k, hk⟩ := hA.exists_strict
  rw [show Finset.univ.erase k = (∅ : Finset n) from Finset.eq_empty_of_forall_notMem fun j hj =>
    (Finset.ne_of_mem_erase hj) ((hsub j).trans (hsub k).symm), Finset.sum_empty, hsub k, h0,
    norm_zero] at hk
  exact lt_irrefl 0 hk

/-- If $A$ is irreducibly diagonally dominant, then its diagonal part is nonsingular, so the Jacobi,
Gauss–Seidel and SOR splittings of $A$ are defined. -/
theorem IsIrreduciblyDiagDominant.isUnit_diagPart {A : Matrix n n 𝕜}
    (hA : A.IsIrreduciblyDiagDominant) : IsUnit (diagPart A) :=
  (isUnit_diagPart_iff A).mpr hA.diag_ne_zero

end Irreducible

section Weak

/-- A square matrix $A$ over $\mathbb{K}$ is **weakly diagonally dominant by rows** if $$\sum_{j \ne
i} |a_{ij}| \le |a_{ii}| \quad \text{for every row } i.$$ This is Definition 1.24 of
[quarteroni2000numerical].

It is the field `Matrix.IsIrreduciblyDiagDominant.dominant` as a separate predicate. -/
def IsDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ‖A i i‖

/-- A square matrix $A$ over $\mathbb{K}$ is **weakly diagonally dominant by columns** if $$\sum_{i
\ne j} |a_{ij}| \le |a_{jj}| \quad \text{for every column } j.$$ This is Definition 1.24 of
[quarteroni2000numerical]. -/
def IsColDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ j, ∑ i ∈ Finset.univ.erase j, ‖A i j‖ ≤ ‖A j j‖

/-- Let $R$ be an additive commutative group with a lattice structure, so that $|a| = a \sqcup -a$
is defined. A square matrix $A$ over $R$ is **weakly diagonally dominant by rows, measured with
the absolute value**, if $\sum_{j \ne i} |a_{ij}| \le |a_{ii}|$ for every row $i$
([quarteroni2000numerical] Definition 1.24).

This is `Matrix.IsDiagDominant`, which uses the norm of an `RCLike` field, for the ordered
fields of floating-point analyses. Over $\mathbb{R}$ the two agree
(`Matrix.isDiagDominant_iff_isAbsDiagDominant`). -/
def IsAbsDiagDominant {m R : Type*} [Fintype m] [DecidableEq m] [Lattice R] [AddCommGroup R]
    (A : Matrix m m R) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ |A i i|

/-- Let $R$ be an additive commutative group with a lattice structure. A square matrix $A$ over $R$
is weakly diagonally dominant by rows with the absolute value if and only if
$\sum_{j \ne i} |a_{ij}| \le |a_{ii}|$ for every row $i$. -/
theorem isAbsDiagDominant_iff {m R : Type*} [Fintype m] [DecidableEq m] [Lattice R]
    [AddCommGroup R] {A : Matrix m m R} :
    A.IsAbsDiagDominant ↔ ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ |A i i| := Iff.rfl

/-- A real square matrix is weakly diagonally dominant by rows with the norm if and only if it is so
with the absolute value. -/
theorem isDiagDominant_iff_isAbsDiagDominant {A : Matrix n n ℝ} :
    A.IsDiagDominant ↔ A.IsAbsDiagDominant := Iff.rfl

variable {A : Matrix n n 𝕜}

/-- A square matrix $A$ is strictly diagonally dominant by rows if and only if
$\sum_{j \ne i} |a_{ij}| < |a_{ii}|$ for every row $i$. -/
theorem isStrictDiagDominant_iff :
    A.IsStrictDiagDominant ↔ ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖ := Iff.rfl

/-- A square matrix $A$ is strictly diagonally dominant by columns if and only if
$\sum_{j \ne i} |a_{ji}| < |a_{ii}|$ for every column $i$. -/
theorem isStrictColDiagDominant_iff :
    A.IsStrictColDiagDominant ↔ ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A j i‖ < ‖A i i‖ := Iff.rfl

/-- A square matrix $A$ is weakly diagonally dominant by rows if and only if
$\sum_{j \ne i} |a_{ij}| \le |a_{ii}|$ for every row $i$. -/
theorem isDiagDominant_iff :
    A.IsDiagDominant ↔ ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ‖A i i‖ := Iff.rfl

/-- A square matrix $A$ is weakly diagonally dominant by columns if and only if
$\sum_{j \ne i} |a_{ji}| \le |a_{ii}|$ for every column $i$. -/
theorem isColDiagDominant_iff :
    A.IsColDiagDominant ↔ ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A j i‖ ≤ ‖A i i‖ := Iff.rfl

/-- The transpose $A^T$ is weakly diagonally dominant by rows if and only if $A$ is weakly
diagonally dominant by columns. -/
theorem IsColDiagDominant.transpose_iff : Aᵀ.IsDiagDominant ↔ A.IsColDiagDominant := Iff.rfl

/-- The transpose $A^T$ is weakly diagonally dominant by columns if and only if $A$ is weakly
diagonally dominant by rows. -/
theorem IsDiagDominant.transpose_iff : Aᵀ.IsColDiagDominant ↔ A.IsDiagDominant := Iff.rfl

/-- A strictly row diagonally dominant matrix is weakly row diagonally dominant. -/
theorem IsStrictDiagDominant.isDiagDominant (hA : A.IsStrictDiagDominant) : A.IsDiagDominant :=
  fun i => (hA i).le

/-- A strictly column diagonally dominant matrix is weakly column diagonally dominant. -/
theorem IsStrictColDiagDominant.isColDiagDominant (hA : A.IsStrictColDiagDominant) :
    A.IsColDiagDominant := fun j => (hA j).le

/-- An irreducibly diagonally dominant matrix is weakly row diagonally dominant. -/
theorem IsIrreduciblyDiagDominant.isDiagDominant (hA : A.IsIrreduciblyDiagDominant) :
    A.IsDiagDominant := hA.dominant

/-- If $A$ is weakly diagonally dominant by rows and $a_{ii} = 0$, then $a_{ij} = 0$ for every $j$.
-/
theorem IsDiagDominant.apply_eq_zero_of_diag_eq_zero (hA : A.IsDiagDominant) {i : n}
    (hi : A i i = 0) (j : n) : A i j = 0 := by
  rcases eq_or_ne j i with rfl | hj
  · exact hi
  have hsum := hA i
  rw [hi, norm_zero] at hsum
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => norm_nonneg (A i j)).mp
    (le_antisymm hsum (Finset.sum_nonneg fun _ _ => norm_nonneg _))
  exact norm_eq_zero.mp (hall j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))

/-- If $A$ is weakly diagonally dominant by rows and nonsingular, then $a_{ii} \ne 0$ for every $i$.

A zero diagonal entry would force a zero row. This is the remark in parentheses in the proof of
[higham2002accuracy] Theorem 9.9. -/
theorem IsDiagDominant.diag_ne_zero_of_isUnit (hA : A.IsDiagDominant) (hu : IsUnit A) (i : n) :
    A i i ≠ 0 := fun hi =>
  ((isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det A).mp hu)))
    (det_eq_zero_of_row_eq_zero i (hA.apply_eq_zero_of_diag_eq_zero hi))

/-- If $A$ is weakly diagonally dominant by columns and nonsingular, then $a_{ii} \ne 0$ for every
$i$. -/
theorem IsColDiagDominant.diag_ne_zero_of_isUnit (hA : A.IsColDiagDominant) (hu : IsUnit A)
    (i : n) : A i i ≠ 0 :=
  (IsColDiagDominant.transpose_iff.mpr hA).diag_ne_zero_of_isUnit ((isUnit_transpose A).mpr hu) i

end Weak

/-! ### Lower bounds for $Ax$ under dominance with a margin -/

section Margin

variable {A : Matrix n n 𝕜}

/-- For every row $i$, $|a_{ii}| |x_i| \le |(Ax)_i| + \sum_{j \ne i} |a_{ij}| |x_j|$. -/
private theorem norm_diag_mul_le (A : Matrix n n 𝕜) (x : n → 𝕜) (i : n) :
    ‖A i i‖ * ‖x i‖ ≤ ‖(A *ᵥ x) i‖ + ∑ j ∈ Finset.univ.erase i, ‖A i j‖ * ‖x j‖ := by
  have h : A i i * x i = (A *ᵥ x) i - ∑ j ∈ Finset.univ.erase i, A i j * x j := by
    rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring
  rw [← norm_mul, h]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans_eq ?_))
  simp only [norm_mul]

/-- Let $A \in \mathbb{K}^{n \times n}$ and $\delta \in \mathbb{R}$, and suppose that
$\delta \le |a_{jj}| - \sum_{i \ne j} |a_{ij}|$ for every column $j$. Then for every
$x \in \mathbb{K}^n$, $$\delta \sum_j |x_j| \le \sum_i |(Ax)_i|,$$ that is,
$\delta \|x\|_1 \le \|Ax\|_1$. This is the core of the proof of [golub2013matrix] Theorem 4.1.2.

It gives $\|A^{-1}\|_1 \le 1/\delta$ for $\delta > 0$. The proof sums the bounds $|a_{ii} x_i|
\le |(Ax)_i| + \sum_{j \ne i} |a_{ij} x_j|$ over the rows and regroups the off-diagonal double
sum by columns. -/
theorem mul_sum_norm_le_sum_norm_mulVec_of_colDiagDominantMargin {δ : ℝ}
    (hδ : ∀ j, δ ≤ ‖A j j‖ - ∑ i ∈ Finset.univ.erase j, ‖A i j‖) (x : n → 𝕜) :
    δ * ∑ j, ‖x j‖ ≤ ∑ i, ‖(A *ᵥ x) i‖ := by
  have hoff : ∑ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ * ‖x j‖
      = ∑ j, (∑ i ∈ Finset.univ.erase j, ‖A i j‖) * ‖x j‖ := by
    simp_rw [Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  have hrow := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => norm_diag_mul_le A x i
  rw [Finset.sum_add_distrib, hoff] at hrow
  calc δ * ∑ j, ‖x j‖ = ∑ j, δ * ‖x j‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ j, (‖A j j‖ - ∑ i ∈ Finset.univ.erase j, ‖A i j‖) * ‖x j‖ :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hδ j) (norm_nonneg _)
    _ ≤ ∑ i, ‖(A *ᵥ x) i‖ := by
        simp_rw [sub_mul, Finset.sum_sub_distrib]
        linarith

/-- Let $A \in \mathbb{K}^{n \times n}$ and $\delta \in \mathbb{R}$, and suppose that
$\delta \le |a_{ii}| - \sum_{j \ne i} |a_{ij}|$ for every row $i$. Then for every
$x \in \mathbb{K}^n$, $$\delta \|x\|_\infty \le \|Ax\|_\infty.$$ This is [golub2013matrix]
P4.1.2, Varah's bound (1975).

The norm is the supremum norm of `n → 𝕜`. It gives $\|A^{-1}\|_\infty \le 1/\delta$ for
$\delta > 0$. At an index $j$ where $|x_j|$ is largest, $|(Ax)_j| \ge |a_{jj}| |x_j| - \sum_{k
\ne j} |a_{jk}| |x_k| \ge \delta |x_j|$. -/
theorem mul_sup_norm_le_sup_norm_mulVec_of_diagDominantMargin {δ : ℝ}
    (hδ : ∀ i, δ ≤ ‖A i i‖ - ∑ j ∈ Finset.univ.erase i, ‖A i j‖) (x : n → 𝕜) :
    δ * ‖x‖ ≤ ‖A *ᵥ x‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Subsingleton.elim x 0]
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun k => ‖x k‖) Finset.univ_nonempty
  have hxj : ‖x‖ = ‖x j‖ :=
    le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => hj k (Finset.mem_univ k))
      (norm_le_pi_norm x j)
  have hoff : ∑ k ∈ Finset.univ.erase j, ‖A j k‖ * ‖x k‖
      ≤ (∑ k ∈ Finset.univ.erase j, ‖A j k‖) * ‖x j‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (hj k (Finset.mem_univ k)) (norm_nonneg _)
  rw [hxj]
  calc δ * ‖x j‖ ≤ (‖A j j‖ - ∑ k ∈ Finset.univ.erase j, ‖A j k‖) * ‖x j‖ :=
        mul_le_mul_of_nonneg_right (hδ j) (norm_nonneg _)
    _ ≤ ‖(A *ᵥ x) j‖ := by linarith [norm_diag_mul_le A x j]
    _ ≤ ‖A *ᵥ x‖ := norm_le_pi_norm _ j

end Margin

section Gershgorin

/-- **Theorem 4.7** of [saad2003iterative]. Let $A \in \mathbb{C}^{n \times n}$ be irreducible, and
let $\mu$ be an eigenvalue of $A$ on the boundary of the union of the Gershgorin discs $\{z :
|z - a_{ii}| \le \sum_{j \ne i} |a_{ij}|\}$. Then $\mu$ lies on the boundary of every disc:
$$|\mu - a_{ii}| = \sum_{j \ne i} |a_{ij}| \quad \text{for every } i.$$

A point on the boundary of the union lies outside every open disc. This is the weak dominance
hypothesis of `Matrix.IsPatternIrreducible.norm_diag_eq_of_mulVec_eq_zero` for $B = \mu I - A$. -/
theorem IsPatternIrreducible.norm_sub_eq_of_mem_frontier {A : Matrix n n ℂ}
    (hA : A.IsPatternIrreducible) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A)
    (hfr : μ ∈ frontier (⋃ i, Metric.closedBall (A i i)
      (∑ j ∈ Finset.univ.erase i, ‖A i j‖))) (i : n) :
    ‖μ - A i i‖ = ∑ j ∈ Finset.univ.erase i, ‖A i j‖ := by
  have hBapp : ∀ k j, (μ • (1 : Matrix n n ℂ) - A) k j = if k = j then μ - A k k else -A k j := by
    intro k j
    rcases eq_or_ne k j with rfl | hkj
    · simp
    · simp [Matrix.one_apply_ne hkj, hkj]
  have hBnorm : ∀ k j, k ≠ j → ‖(μ • (1 : Matrix n n ℂ) - A) k j‖ = ‖A k j‖ := fun k j hkj => by
    rw [hBapp, ite_eq_right hkj, norm_neg]
  have hBdiag : ∀ k, ‖(μ • (1 : Matrix n n ℂ) - A) k k‖ = ‖μ - A k k‖ := fun k => by
    rw [hBapp, ite_eq_left rfl]
  have hsum : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖(μ • (1 : Matrix n n ℂ) - A) k j‖ =
      ∑ j ∈ Finset.univ.erase k, ‖A k j‖ :=
    fun k => Finset.sum_congr rfl fun j hj => hBnorm k j (Finset.ne_of_mem_erase hj).symm
  have hnotint : μ ∉ interior (⋃ k, Metric.closedBall (A k k)
      (∑ j ∈ Finset.univ.erase k, ‖A k j‖)) := hfr.2
  have hge : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖(μ • (1 : Matrix n n ℂ) - A) k j‖ ≤
      ‖(μ • (1 : Matrix n n ℂ) - A) k k‖ := by
    intro k
    rw [hsum, hBdiag]
    by_contra hlt
    refine hnotint (interior_maximal (Metric.ball_subset_closedBall.trans
      (Set.subset_iUnion (fun k => Metric.closedBall (A k k)
        (∑ j ∈ Finset.univ.erase k, ‖A k j‖)) k)) Metric.isOpen_ball ?_)
    rw [Metric.mem_ball, dist_eq_norm]
    exact not_le.mp hlt
  obtain ⟨x, hx, hBx⟩ := exists_mulVec_eq_zero_of_mem_spectrum hμ
  have hkey := hA.norm_diag_eq_of_mulVec_eq_zero
    (fun k j hkj hAkj => by rw [hBapp, ite_eq_right hkj]; simpa using hAkj) hge hx hBx i
  rwa [hBdiag, hsum] at hkey

end Gershgorin

section PosDef

variable {A : Matrix n n 𝕜}

/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian and strictly diagonally dominant by rows, with
$\operatorname{Re} a_{ii} > 0$ for every $i$. Then $A$ is positive definite. This is stated for
real symmetric matrices in [quarteroni2000numerical] §1.12, after Definition 1.24.

By Gershgorin's theorem every eigenvalue lies in a disc with centre some $a_{kk} > 0$ and radius
$\sum_{j \ne k} |a_{kj}| < a_{kk}$, so it is positive. A Hermitian matrix with positive
eigenvalues is positive definite. -/
theorem IsStrictDiagDominant.posDef (hA : A.IsHermitian) (hd : A.IsStrictDiagDominant)
    (hpos : ∀ i, 0 < RCLike.re (A i i)) : A.PosDef := by
  rw [hA.posDef_iff_eigenvalues_pos]
  intro i
  have hev : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i : 𝕜) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⇑(hA.eigenvectorBasis i)) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, toLin'_apply, hA.mulVec_eigenvectorBasis,
        RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    · exact fun h => hA.eigenvectorBasis.orthonormal.ne_zero i ((WithLp.ofLp_eq_zero 2).mp h)
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  have hlt := hk.trans_lt (hd k)
  rw [← hA.coe_re_apply_self k, ← RCLike.ofReal_sub, RCLike.norm_ofReal, RCLike.norm_ofReal,
    abs_of_pos (hpos k)] at hlt
  have := (abs_lt.mp hlt).1
  linarith

/-- Let $A \in \mathbb{K}^{n \times n}$ be Hermitian and weakly diagonally dominant by rows, with
$\operatorname{Re} a_{ii} \ge 0$ for every $i$. Then $A$ is positive semidefinite.

By Gershgorin's theorem every eigenvalue lies in a disc with centre some $a_{kk} \ge 0$ and
radius $\sum_{j \ne k} |a_{kj}| \le a_{kk}$, so it is nonnegative. This is the weak form of
`Matrix.IsStrictDiagDominant.posDef`. With nonsingularity
(`Matrix.PosSemidef.posDef_iff_isUnit`) it gives positive definiteness. -/
theorem IsDiagDominant.posSemidef (hA : A.IsHermitian) (hd : A.IsDiagDominant)
    (hpos : ∀ i, 0 ≤ RCLike.re (A i i)) : A.PosSemidef := by
  rw [hA.posSemidef_iff_eigenvalues_nonneg, Pi.le_def]
  intro i
  have hev : Module.End.HasEigenvalue (Matrix.toLin' A) (hA.eigenvalues i : 𝕜) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⇑(hA.eigenvectorBasis i)) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, toLin'_apply, hA.mulVec_eigenvectorBasis,
        RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    · exact fun h => hA.eigenvectorBasis.orthonormal.ne_zero i ((WithLp.ofLp_eq_zero 2).mp h)
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
  rw [Metric.mem_closedBall, dist_eq_norm] at hk
  have hle := hk.trans (hd k)
  rw [← hA.coe_re_apply_self k, ← RCLike.ofReal_sub, RCLike.norm_ofReal, RCLike.norm_ofReal,
    abs_of_nonneg (hpos k)] at hle
  have h := (abs_le.mp hle).1
  simp only [Pi.zero_apply]
  linarith

end PosDef

section Complexify

variable {A : Matrix n n ℝ}

/-- If a real square matrix $A$ is strictly diagonally dominant by rows, then its complexification
is strictly diagonally dominant by rows, because complexification keeps every entrywise absolute
value. -/
theorem isStrictDiagDominant_complexify (h : A.IsStrictDiagDominant) :
    (complexify A).IsStrictDiagDominant := by
  intro i
  simpa using h i

/-- If a real square matrix $A$ is strictly diagonally dominant by columns, then its
complexification is strictly diagonally dominant by columns. -/
theorem isStrictColDiagDominant_complexify (h : A.IsStrictColDiagDominant) :
    (complexify A).IsStrictColDiagDominant := by
  intro j
  simpa using h j

omit [Fintype n] [DecidableEq n] in
/-- If a real square matrix $A$ is irreducible, then its complexification is irreducible, because
complexification keeps every entrywise absolute value. -/
theorem isPatternIrreducible_complexify (h : A.IsPatternIrreducible) :
    (complexify A).IsPatternIrreducible := by
  have hmap : (complexify A).map (fun x : ℂ => ‖x‖) = A.map fun x : ℝ => ‖x‖ := by
    ext i j; simp [complexify]
  change Matrix.IsIrreducible ((complexify A).map fun x : ℂ => ‖x‖)
  rw [hmap]
  exact h

/-- If a real square matrix $A$ is irreducibly diagonally dominant, then its complexification is
irreducibly diagonally dominant. -/
theorem isIrreduciblyDiagDominant_complexify (h : A.IsIrreduciblyDiagDominant) :
    (complexify A).IsIrreduciblyDiagDominant where
  irreducible := isPatternIrreducible_complexify h.irreducible
  dominant i := by simpa using h.dominant i
  exists_strict := by
    obtain ⟨i, hi⟩ := h.exists_strict
    exact ⟨i, by simpa using hi⟩

end Complexify

section Schur

variable {K : Type*} [Field K]

variable {A : Matrix n n 𝕜}

/-- For a predicate $p$ on $n$, a function $f : n \to \mathbb{R}$ and an element $j$ of the subtype
$\{i \mid p(i)\}$, the sum of $f$ over the subtype without $j$ equals the sum of $f$ over
$\{i \mid p(i)\} \setminus \{j\}$ in $n$. -/
theorem sum_erase_subtype_eq {p : n → Prop} [DecidablePred p] (j : {i // p i}) (f : n → ℝ) :
    ∑ i ∈ (Finset.univ : Finset {i // p i}).erase j, f i =
      ∑ i ∈ (Finset.univ.filter p).erase j.1, f i := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ j),
    Finset.sum_erase_eq_sub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩),
    Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun i => by simp) f]

/-- Let $A$ be weakly diagonally dominant by columns, let $a_{pp} \ne 0$, and let $j \ne p$. Then
column $j$ of the matrix with entries $a_{ij} - a_{ip} a_{pp}^{-1} a_{pj}$, restricted to the
rows $i \ne p$, is weakly dominated by its diagonal entry: $$\sum_{i \ne p, j} |a_{ij} - a_{ip}
a_{pp}^{-1} a_{pj}| \le |a_{jj} - a_{jp} a_{pp}^{-1} a_{pj}|.$$

This is `Matrix.IsColDiagDominant.schurComplementSingle` before the reindexing
([higham2002accuracy] Theorem 13.8 with $1 \times 1$ blocks; Wilkinson). -/
theorem IsColDiagDominant.sum_norm_sub_le (hA : A.IsColDiagDominant) {p j : n} (hp : A p p ≠ 0)
    (hj : j ≠ p) :
    ∑ i ∈ (Finset.univ.erase p).erase j, ‖A i j - A i p * (A p p)⁻¹ * A p j‖ ≤
      ‖A j j - A j p * (A p p)⁻¹ * A p j‖ := by
  set T := (Finset.univ.erase p).erase j with hT
  have ha : 0 < ‖A p p‖ := norm_pos_iff.mpr hp
  set a := ‖A p p‖
  set x := ‖A p j‖
  set y := ‖A j p‖
  set t := x / a with ht
  have hat : a * t = x := by rw [ht, mul_div_cancel₀ _ ha.ne']
  -- the two dominance inequalities, restricted to `T`
  have hSj : (∑ i ∈ T, ‖A i j‖) + x ≤ ‖A j j‖ := by
    have h := hA j
    rw [← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_univ p⟩),
      Finset.erase_right_comm] at h
    exact h
  have hSp : (∑ i ∈ T, ‖A i p‖) + y ≤ a := by
    have h := hA p
    rw [← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)] at h
    exact h
  have hnorm : ∀ i, ‖A i p * (A p p)⁻¹ * A p j‖ = ‖A i p‖ * t := fun i => by
    rw [norm_mul, norm_mul, norm_inv, ht, mul_assoc, div_eq_inv_mul]
  have hterm : ∀ i, ‖A i j - A i p * (A p p)⁻¹ * A p j‖ ≤ ‖A i j‖ + ‖A i p‖ * t := fun i =>
    (norm_sub_le _ _).trans_eq (by rw [hnorm])
  calc ∑ i ∈ T, ‖A i j - A i p * (A p p)⁻¹ * A p j‖
      ≤ ∑ i ∈ T, (‖A i j‖ + ‖A i p‖ * t) := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i ∈ T, ‖A i j‖) + (∑ i ∈ T, ‖A i p‖) * t := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ (‖A j j‖ - x) + (a - y) * t := by
        gcongr
        · linarith
        · linarith
    _ = ‖A j j‖ - y * t := by rw [sub_mul, hat]; ring
    _ = ‖A j j‖ - ‖A j p * (A p p)⁻¹ * A p j‖ := by rw [hnorm]
    _ ≤ ‖A j j - A j p * (A p p)⁻¹ * A p j‖ := norm_sub_norm_le _ _

/-- Let $A$ be weakly diagonally dominant by columns and let $a_{pp} \ne 0$. Then the Schur
complement of the pivot $a_{pp}$, the matrix with entries $a_{ij} - a_{ip} a_{pp}^{-1} a_{pj}$
for $i, j \ne p$, is weakly diagonally dominant by columns. So one step of Gaussian elimination
preserves weak column dominance ([higham2002accuracy] Theorem 13.8 with $1 \times 1$ blocks;
Wilkinson).

This lemma gives the existence of an LU factorization for column dominant matrices and the bound
$2$ on their growth factor. The Schur complement is `Matrix.schurComplementSingle`. -/
theorem IsColDiagDominant.schurComplementSingle (hA : A.IsColDiagDominant) {p : n}
    (hp : A p p ≠ 0) : (A.schurComplementSingle p).IsColDiagDominant := by
  intro j
  simp only [schurComplementSingle_apply]
  refine (sum_erase_subtype_eq j fun i => ‖A i j - A i p * (A p p)⁻¹ * A p j‖).trans_le ?_
  rw [Finset.filter_ne']
  exact hA.sum_norm_sub_le hp j.2

/-- Let $A$ be weakly diagonally dominant by rows and let $a_{pp} \ne 0$. Then the Schur complement
of the pivot $a_{pp}$ (`Matrix.schurComplementSingle`) is weakly diagonally dominant by rows.

The transpose of the Schur complement is the Schur complement of the transpose. -/
theorem IsDiagDominant.schurComplementSingle (hA : A.IsDiagDominant) {p : n} (hp : A p p ≠ 0) :
    (A.schurComplementSingle p).IsDiagDominant := by
  rw [← IsDiagDominant.transpose_iff, schurComplementSingle_transpose]
  exact (IsDiagDominant.transpose_iff.mpr hA).schurComplementSingle hp

end Schur

end Matrix
