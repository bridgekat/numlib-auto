import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearAlgebra.Matrix.SchurComplement
import Numlib.LinearAlgebra.Sparse.Pattern

/-!
# Diagonally dominant matrices

Strict (row / column) diagonal dominance and irreducible diagonal dominance, and the
nonsingularity theorems they carry ([saad2003iterative] Definition 4.5, Theorem 4.7 and
Corollary 4.8; [kress1998numerical] (4.4)–(4.5) and Theorem 4.7; [quarteroni2000numerical]
Definition 1.24).  This is the matrix-analytic layer only: nothing here mentions a splitting or an
iteration.  The convergence of the Jacobi and Gauss–Seidel iterations for these matrices, the
explicit `‖·‖_∞` contraction constants and the Gershgorin pencil arguments are in
`Numlib/Stationary/DiagDominant.lean`, which builds on this module and on
`Numlib/Stationary/Splitting.lean`.  The split lets the foundation modules —
`Numlib/LinearAlgebra/Matrix/MMatrix.lean`, the LU factorization — name the dominance predicates
without importing the theory of stationary iterations.

## Main definitions

* `Matrix.IsStrictDiagDominant`, `Matrix.IsStrictColDiagDominant`: `∑_{j ≠ i} |a_ij| < |a_ii|` for
  every row `i`, and the same by columns.
* `Matrix.IsDiagDominant`, `Matrix.IsColDiagDominant`: the weak forms `∑_{j ≠ i} |a_ij| ≤ |a_ii|`
  of [quarteroni2000numerical] Definition 1.24, which the strict and the irreducible forms both
  imply.
* `Matrix.IsIrreduciblyDiagDominant`, `Matrix.IsIrreduciblyColDiagDominant`: [saad2003iterative]
  Definition 4.5, the irreducible relaxation — weak dominance in every row, strict dominance in at
  least one, and a strongly connected nonzero pattern (`Matrix.IsPatternIrreducible` of
  `Numlib/LinearAlgebra/Sparse/Pattern.lean`).

## Main results

* `Matrix.IsStrictDiagDominant.isUnit`, `Matrix.IsStrictColDiagDominant.isUnit`: strictly
  diagonally dominant matrices are nonsingular (Mathlib's `Matrix.det_ne_zero_of_sum_row_lt_diag`,
  the Gershgorin form), with `Matrix.IsStrictDiagDominant.isUnit_diagPart` for the diagonal part.
* `Matrix.IsPatternIrreducible.norm_diag_eq_of_mulVec_eq_zero`: the engine of the irreducible
  theory.  At a row where the modulus of a kernel vector is maximal, weak dominance is forced to be
  an equality, and the maximum then propagates along the adjacency graph to every row.
  `Matrix.IsPatternIrreducible.isUnit_of_dominant` and `Matrix.IsIrreduciblyDiagDominant.isUnit`
  are [saad2003iterative] Corollary 4.8, and
  `Matrix.IsPatternIrreducible.norm_sub_eq_of_mem_frontier` is his Theorem 4.7 — an eigenvalue of
  an irreducible matrix on the boundary of the union of the Gershgorin discs lies on the boundary
  of every disc.  The engine is stated for a matrix `B` dominated off the diagonal by an
  irreducible `A`, because the convergence proofs apply it to a *pencil* (the matrix with its
  diagonal, or its lower triangle, scaled by an eigenvalue) rather than to the matrix itself.
* `Matrix.IsStrictDiagDominant.posDef`: a Hermitian strictly row dominant matrix with positive
  diagonal is positive definite ([quarteroni2000numerical] §1.12), by Gershgorin's theorem.
* `Matrix.IsStrictColDiagDominant.mul_sum_norm_le_sum_norm_mulVec` and
  `Matrix.IsStrictDiagDominant.mul_sup_norm_le_sup_norm_mulVec`: dominance with a margin `δ`
  bounds `A x` from below, `δ ‖x‖₁ ≤ ‖A x‖₁` for columns and `δ ‖x‖_∞ ≤ ‖A x‖_∞` for rows, which
  is `‖A⁻¹‖ ≤ 1 / δ` in the corresponding induced norm ([golub2013matrix] Theorem 4.1.2 and its
  row twin, Varah's bound).
* `Matrix.IsColDiagDominant.schurComplementSingle`, `Matrix.IsDiagDominant.schurComplementSingle`:
  one step of Gaussian elimination (`Matrix.schurComplementSingle` of
  `Numlib/LinearAlgebra/Matrix/SchurComplement.lean`) preserves weak column and weak row dominance
  ([higham2002accuracy] Theorem 13.8 with `1 × 1` blocks; Wilkinson), and a nonsingular weakly
  dominant matrix has a nowhere-zero diagonal (`Matrix.IsDiagDominant.diag_ne_zero_of_isUnit`).
  These are the two facts behind the existence of the LU factorization of a nonsingular
  diagonally dominant matrix ([quarteroni2000numerical] Property 3.2, [higham2002accuracy]
  Theorem 9.9) in `Numlib/LinearAlgebra/Matrix/LU.lean`.
* `Matrix.isStrictDiagDominant_complexify`, `Matrix.isIrreduciblyDiagDominant_complexify`,
  `Matrix.isPatternIrreducible_complexify`: complexification changes no entrywise absolute value,
  so it preserves all three notions.  The last is here, rather than in
  `Numlib/LinearAlgebra/Sparse/Pattern.lean` or `Numlib/LinearAlgebra/Matrix/Complexify.lean`,
  because this is the first module that imports both.
-/

open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Spectrum

variable {K : Type*} [Field K]

/-- A point of the spectrum of a matrix is an eigenvalue: it comes with a nonzero vector in the
kernel of the resolvent. -/
theorem exists_mulVec_eq_zero_of_mem_spectrum {M : Matrix n n K} {μ : K}
    (hμ : μ ∈ spectrum K M) : ∃ x ≠ 0, (μ • (1 : Matrix n n K) - M) *ᵥ x = 0 := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not] at hμ
  exact Matrix.exists_mulVec_eq_zero_iff.mpr hμ

end Spectrum

variable {𝕜 : Type*} [RCLike 𝕜]

section Strict

/-- Row strict diagonal dominance: `∑_{j ≠ i} |a_ij| < |a_ii|` for every row `i`. -/
def IsStrictDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖

/-- Column strict diagonal dominance: `∑_{i ≠ j} |a_ij| < |a_jj|` for every column `j`. -/
def IsStrictColDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ j, ∑ i ∈ Finset.univ.erase j, ‖A i j‖ < ‖A j j‖

/-- Column dominance of `A` is row dominance of `Aᵀ`; true by definition, and the bridge along which
the column-dominance criterion for Jacobi is deduced from the row one. -/
theorem IsStrictColDiagDominant.transpose_iff (A : Matrix n n 𝕜) :
    A.transpose.IsStrictDiagDominant ↔ A.IsStrictColDiagDominant := Iff.rfl

/-- A strictly row diagonally dominant matrix has no zero on its diagonal: `|a_ii|` strictly exceeds
a sum of norms, hence is positive. -/
theorem IsStrictDiagDominant.diag_ne_zero {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) (i : n) :
    A i i ≠ 0 :=
  norm_pos_iff.mp (lt_of_le_of_lt (Finset.sum_nonneg fun _ _ => norm_nonneg _) (hA i))

/-- The diagonal part of a strictly row diagonally dominant matrix is invertible, so the Jacobi,
Gauss–Seidel and SOR splittings of such a matrix (`Numlib/Stationary/Splitting.lean`)
are all defined; this is the hypothesis every convergence statement about them carries. -/
theorem IsStrictDiagDominant.isUnit_diagPart {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) :
    IsUnit (diagPart A) :=
  (isUnit_diagPart_iff A).mpr hA.diag_ne_zero

/-- Strictly diagonally dominant matrices are invertible ([saad2003iterative], Theorem 4.6; also
[kress1998numerical]).  Mathlib: `Matrix.det_ne_zero_of_sum_row_lt_diag`. -/
theorem IsStrictDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsStrictDiagDominant) :
    IsUnit A :=
  (isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr (det_ne_zero_of_sum_row_lt_diag hA))

/-- Strictly column diagonally dominant matrices are invertible: the transpose is strictly row
dominant, and a matrix and its transpose have the same determinant. -/
theorem IsStrictColDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsStrictColDiagDominant) :
    IsUnit A := by
  have h := ((IsStrictColDiagDominant.transpose_iff A).mpr hA).isUnit
  rwa [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det] at h

end Strict

section Irreducible

/-- [saad2003iterative] *irreducibly diagonally dominant* matrices (Definition 4.5): irreducible,
weakly row diagonally dominant, and strictly dominant in at least one row.  This is the hypothesis
under which the Gershgorin argument still gives nonsingularity and convergence of Jacobi and
Gauss–Seidel, with strict dominance in a single row instead of in all of them. -/
structure IsIrreduciblyDiagDominant (A : Matrix n n 𝕜) : Prop where
  /-- The adjacency graph of the nonzero pattern is strongly connected. -/
  irreducible : A.IsPatternIrreducible
  /-- Every row is weakly diagonally dominant. -/
  dominant : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ‖A i i‖
  /-- At least one row is strictly diagonally dominant. -/
  exists_strict : ∃ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖

/-- The column form of [saad2003iterative] Definition 4.5: `A` is irreducibly diagonally dominant by
columns when its transpose is by rows. -/
def IsIrreduciblyColDiagDominant (A : Matrix n n 𝕜) : Prop := Aᵀ.IsIrreduciblyDiagDominant

/-- **[saad2003iterative] Theorem 4.7**, in the form its applications use.  Let `A` be irreducible
and let `B` have a nonzero entry wherever `A` has one off the diagonal.  If `B` is weakly diagonally
dominant and annihilates a nonzero vector, then every row of `B` is an equality row.

At a row `i` where `|x_i|` is maximal, weak dominance is forced to be an equality, and the maximum
is attained again at every `j` with `b_ij ≠ 0`; the strong connectivity of `A` then propagates the
maximum, hence the equality, to every row. -/
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

/-- **[saad2003iterative] Corollary 4.8**: an irreducible matrix that is weakly diagonally dominant,
with strict dominance in at least one row, is nonsingular.  A vector in its kernel would make every
row an equality row by `Matrix.IsPatternIrreducible.norm_diag_eq_of_mulVec_eq_zero`, against the
strict row.  Stated for a matrix `B` dominated off the diagonal by an irreducible `A`, which is how
the convergence proofs of `Numlib/Stationary/DiagDominant.lean` use it. -/
theorem IsPatternIrreducible.isUnit_of_dominant {A B : Matrix n n 𝕜} (hA : A.IsPatternIrreducible)
    (hAB : ∀ i j, i ≠ j → A i j ≠ 0 → B i j ≠ 0)
    (hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖B i j‖ ≤ ‖B i i‖)
    (hstrict : ∃ i, ∑ j ∈ Finset.univ.erase i, ‖B i j‖ < ‖B i i‖) : IsUnit B := by
  obtain ⟨i, hi⟩ := hstrict
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨x, hx, hBx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hi.ne' (hA.norm_diag_eq_of_mulVec_eq_zero hAB hdom hx hBx i)

/-- An irreducibly diagonally dominant matrix is nonsingular ([saad2003iterative], Corollary 4.8).
-/
theorem IsIrreduciblyDiagDominant.isUnit {A : Matrix n n 𝕜} (hA : A.IsIrreduciblyDiagDominant) :
    IsUnit A :=
  hA.irreducible.isUnit_of_dominant (fun _ _ _ hij => hij) hA.dominant hA.exists_strict

/-- An irreducibly diagonally dominant matrix has no zero on its diagonal: a zero diagonal entry
would force its whole row to vanish, which an irreducible matrix of size at least two forbids, while
for a matrix of size one the strict row is the diagonal entry itself. -/
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

/-- The diagonal part of an irreducibly diagonally dominant matrix is invertible, so the Jacobi,
Gauss–Seidel and SOR splittings of such a matrix are defined. -/
theorem IsIrreduciblyDiagDominant.isUnit_diagPart {A : Matrix n n 𝕜}
    (hA : A.IsIrreduciblyDiagDominant) : IsUnit (diagPart A) :=
  (isUnit_diagPart_iff A).mpr hA.diag_ne_zero

end Irreducible

section Weak

/-- Weak row diagonal dominance ([quarteroni2000numerical] Definition 1.24):
`∑_{j ≠ i} |a_ij| ≤ |a_ii|` for every row `i`. This is the `dominant` field of
`Matrix.IsIrreduciblyDiagDominant`, factored out. -/
def IsDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ‖A i i‖

/-- Weak column diagonal dominance ([quarteroni2000numerical] Definition 1.24):
`∑_{i ≠ j} |a_ij| ≤ |a_jj|` for every column `j`. -/
def IsColDiagDominant (A : Matrix n n 𝕜) : Prop :=
  ∀ j, ∑ i ∈ Finset.univ.erase j, ‖A i j‖ ≤ ‖A j j‖

variable {A : Matrix n n 𝕜}

/-- The row form of strict diagonal dominance, unfolded. -/
theorem isStrictDiagDominant_iff :
    A.IsStrictDiagDominant ↔ ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < ‖A i i‖ := Iff.rfl

/-- The column form of strict diagonal dominance, unfolded. -/
theorem isStrictColDiagDominant_iff :
    A.IsStrictColDiagDominant ↔ ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A j i‖ < ‖A i i‖ := Iff.rfl

/-- Weak row dominance, unfolded. -/
theorem isDiagDominant_iff :
    A.IsDiagDominant ↔ ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ‖A i i‖ := Iff.rfl

/-- Weak column dominance, unfolded. -/
theorem isColDiagDominant_iff :
    A.IsColDiagDominant ↔ ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A j i‖ ≤ ‖A i i‖ := Iff.rfl

/-- Weak column dominance of `A` is weak row dominance of `Aᵀ`. -/
theorem IsColDiagDominant.transpose_iff : Aᵀ.IsDiagDominant ↔ A.IsColDiagDominant := Iff.rfl

/-- Weak row dominance of `A` is weak column dominance of `Aᵀ`. -/
theorem IsDiagDominant.transpose_iff : Aᵀ.IsColDiagDominant ↔ A.IsDiagDominant := Iff.rfl

/-- Strict row dominance is weak row dominance. -/
theorem IsStrictDiagDominant.isDiagDominant (hA : A.IsStrictDiagDominant) : A.IsDiagDominant :=
  fun i => (hA i).le

/-- Strict column dominance is weak column dominance. -/
theorem IsStrictColDiagDominant.isColDiagDominant (hA : A.IsStrictColDiagDominant) :
    A.IsColDiagDominant := fun j => (hA j).le

/-- Irreducible row dominance is weak row dominance. -/
theorem IsIrreduciblyDiagDominant.isDiagDominant (hA : A.IsIrreduciblyDiagDominant) :
    A.IsDiagDominant := hA.dominant

/-- A zero diagonal entry of a weakly row dominant matrix forces its whole row to vanish. -/
theorem IsDiagDominant.apply_eq_zero_of_diag_eq_zero (hA : A.IsDiagDominant) {i : n}
    (hi : A i i = 0) (j : n) : A i j = 0 := by
  rcases eq_or_ne j i with rfl | hj
  · exact hi
  have hsum := hA i
  rw [hi, norm_zero] at hsum
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => norm_nonneg (A i j)).mp
    (le_antisymm hsum (Finset.sum_nonneg fun _ _ => norm_nonneg _))
  exact norm_eq_zero.mp (hall j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))

/-- A nonsingular weakly row dominant matrix has a nowhere-zero diagonal: a zero diagonal entry
forces a zero row (the parenthesis in the proof of [higham2002accuracy] Theorem 9.9). -/
theorem IsDiagDominant.diag_ne_zero_of_isUnit (hA : A.IsDiagDominant) (hu : IsUnit A) (i : n) :
    A i i ≠ 0 := fun hi =>
  ((isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det A).mp hu)))
    (det_eq_zero_of_row_eq_zero i (hA.apply_eq_zero_of_diag_eq_zero hi))

/-- A nonsingular weakly column dominant matrix has a nowhere-zero diagonal. -/
theorem IsColDiagDominant.diag_ne_zero_of_isUnit (hA : A.IsColDiagDominant) (hu : IsUnit A)
    (i : n) : A i i ≠ 0 :=
  (IsColDiagDominant.transpose_iff.mpr hA).diag_ne_zero_of_isUnit ((isUnit_transpose A).mpr hu) i

end Weak

/-! ### Lower bounds for `A x` under dominance with a margin -/

section Margin

variable {A : Matrix n n 𝕜}

/-- The diagonal term of `(A x)_i` is bounded by the row: `‖a_ii x_i‖ ≤ ‖(A x)_i‖ + ∑_{j ≠ i}
‖a_ij‖ ‖x_j‖`. -/
private theorem norm_diag_mul_le (A : Matrix n n 𝕜) (x : n → 𝕜) (i : n) :
    ‖A i i‖ * ‖x i‖ ≤ ‖(A *ᵥ x) i‖ + ∑ j ∈ Finset.univ.erase i, ‖A i j‖ * ‖x j‖ := by
  have h : A i i * x i = (A *ᵥ x) i - ∑ j ∈ Finset.univ.erase i, A i j * x j := by
    rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring
  rw [← norm_mul, h]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans_eq ?_))
  simp only [norm_mul]

/-- **Column dominance with a margin bounds `A x` from below in the `1`-norm** ([golub2013matrix]
Theorem 4.1.2, the heart of its proof): if `δ ≤ |a_jj| - ∑_{i ≠ j} |a_ij|` for every column `j`,
then `δ ∑ⱼ |x_j| ≤ ∑ᵢ |(A x)_i|`. The diagonal terms `|a_ii x_i| ≤ |(A x)_i| + ∑_{j ≠ i} |a_ij x_j|`
are summed over the rows, and the off-diagonal double sum is regrouped by columns. The bound
`‖A⁻¹‖₁ ≤ 1 / δ` follows. -/
theorem IsStrictColDiagDominant.mul_sum_norm_le_sum_norm_mulVec {δ : ℝ}
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

/-- **Row dominance with a margin bounds `A x` from below in the `∞`-norm** ([golub2013matrix]
P4.1.2; Varah 1975): if `δ ≤ |a_ii| - ∑_{j ≠ i} |a_ij|` for every row `i`, then
`δ ‖x‖_∞ ≤ ‖A x‖_∞`, the sup norms of `n → 𝕜`. At an index `j` where `|x_j|` is largest,
`|(A x)_j| ≥ |a_jj| |x_j| - ∑_{k ≠ j} |a_jk| |x_k| ≥ δ |x_j|`. The bound `‖A⁻¹‖_∞ ≤ 1 / δ`
follows. -/
theorem IsStrictDiagDominant.mul_sup_norm_le_sup_norm_mulVec {δ : ℝ}
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

/-- **[saad2003iterative] Theorem 4.7**: if `A` is irreducible and an eigenvalue of `A` lies on the
boundary of the union of the Gershgorin discs, then it lies on the boundary of *every* disc, that is
`‖μ - a_ii‖ = ∑_{j ≠ i} ‖a_ij‖` for every `i`.  Being on the boundary of the union means being
outside every open disc, which is the weak dominance hypothesis of
`Matrix.IsPatternIrreducible.norm_diag_eq_of_mulVec_eq_zero` for the resolvent `μ 1 - A`. -/
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

/-- A Hermitian, strictly row diagonally dominant matrix with positive diagonal is positive
definite ([quarteroni2000numerical] §1.12, after Definition 1.24, for real symmetric matrices).
By Gershgorin's theorem every eigenvalue lies in a disc centred at some `a_kk > 0` of radius
`∑_{j ≠ k} |a_kj| < a_kk`, hence is positive; a Hermitian matrix with positive eigenvalues is
positive definite. -/
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

/-- A Hermitian, weakly row diagonally dominant matrix with nonnegative diagonal is positive
semidefinite: by Gershgorin's theorem every eigenvalue lies in a disc centred at some `a_kk ≥ 0`
of radius `∑_{j ≠ k} |a_kj| ≤ a_kk`, hence is nonnegative. It is the weak companion of
`Matrix.IsStrictDiagDominant.posDef`; combined with nonsingularity
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

/-- The complexification of a real strictly row diagonally dominant matrix is strictly row
diagonally dominant: complexification preserves every entrywise absolute value. -/
theorem isStrictDiagDominant_complexify (h : A.IsStrictDiagDominant) :
    (complexify A).IsStrictDiagDominant := by
  intro i
  simpa using h i

/-- The complexification of a real strictly column diagonally dominant matrix is strictly column
diagonally dominant. -/
theorem isStrictColDiagDominant_complexify (h : A.IsStrictColDiagDominant) :
    (complexify A).IsStrictColDiagDominant := by
  intro j
  simpa using h j

omit [Fintype n] [DecidableEq n] in
/-- Complexification changes no entrywise absolute value, so it preserves irreducibility of the
nonzero pattern. -/
theorem isPatternIrreducible_complexify (h : A.IsPatternIrreducible) :
    (complexify A).IsPatternIrreducible := by
  have hmap : (complexify A).map (fun x : ℂ => ‖x‖) = A.map fun x : ℝ => ‖x‖ := by
    ext i j; simp [complexify]
  change Matrix.IsIrreducible ((complexify A).map fun x : ℂ => ‖x‖)
  rw [hmap]
  exact h

/-- Complexification preserves irreducible diagonal dominance. -/
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

/-- A sum over a subtype with one element removed, as a sum over the ambient type. -/
theorem sum_erase_subtype_eq {p : n → Prop} [DecidablePred p] (j : {i // p i}) (f : n → ℝ) :
    ∑ i ∈ (Finset.univ : Finset {i // p i}).erase j, f i =
      ∑ i ∈ (Finset.univ.filter p).erase j.1, f i := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ j),
    Finset.sum_erase_eq_sub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩),
    Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun i => by simp) f]

/-- The one-step Schur complement of a weakly column dominant matrix, before the reindexing: for
`j ≠ p` the column `j` of `A i j - A i p (A p p)⁻¹ A p j` is dominated by its diagonal entry
([higham2002accuracy] Theorem 13.8 with `1 × 1` blocks; Wilkinson). -/
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
  have ht0 : 0 ≤ t := div_nonneg (norm_nonneg _) ha.le
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

/-- One step of Gaussian elimination preserves weak column dominance ([higham2002accuracy]
Theorem 13.8 with `1 × 1` blocks; Wilkinson): the Schur complement at a nonzero pivot of a
weakly column dominant matrix is weakly column dominant. This is the lemma behind the existence
of an LU factorization for column dominant matrices and the bound `2` on their growth factor. -/
theorem IsColDiagDominant.schurComplementSingle (hA : A.IsColDiagDominant) {p : n}
    (hp : A p p ≠ 0) : (A.schurComplementSingle p).IsColDiagDominant := by
  intro j
  simp only [schurComplementSingle_apply]
  refine (sum_erase_subtype_eq j fun i => ‖A i j - A i p * (A p p)⁻¹ * A p j‖).trans_le ?_
  rw [Finset.filter_ne']
  exact hA.sum_norm_sub_le hp j.2

/-- One step of Gaussian elimination preserves weak row dominance: the transpose of the Schur
complement is the Schur complement of the transpose. -/
theorem IsDiagDominant.schurComplementSingle (hA : A.IsDiagDominant) {p : n} (hp : A p p ≠ 0) :
    (A.schurComplementSingle p).IsDiagDominant := by
  rw [← IsDiagDominant.transpose_iff, schurComplementSingle_transpose]
  exact (IsDiagDominant.transpose_iff.mpr hA).schurComplementSingle hp

end Schur

end Matrix
