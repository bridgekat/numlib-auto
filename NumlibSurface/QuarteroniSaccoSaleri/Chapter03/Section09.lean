import Mathlib.Data.Matrix.ColumnRowPartitioned
import Numlib.LinearAlgebra.Sparse.Pattern
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section07

/-!
# Quarteroni–Sacco–Saleri §3.9: sparse matrices

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.9, over the backbone `Numlib/LinearAlgebra/Sparse/Pattern` (the
adjacency digraph `Matrix.adjDigraph` of a matrix), `Numlib/LinearAlgebra/Matrix/LU` (the
envelope `Matrix.envelope` and its preservation `Matrix.IsLU.envelope_eq`),
`Numlib/LinearAlgebra/Matrix/Cholesky` and `Numlib/LinearAlgebra/Matrix/SchurComplement` (the
block factorization `Matrix.fromBlocks_eq_mul_schurComplement` behind substructuring).

## Conventions

The oriented graph `G(A)` of a square matrix is the backbone's `Matrix.adjDigraph A`, a
`Digraph (Fin n)` with an arrow `i → j` iff `a_ij ≠ 0` (a loop at `i` iff `a_ii ≠ 0`). The
envelope (the book's "convex hull") `E(A)` of (3.59) is `Matrix.envelope A`, a set of index pairs;
the book's `m_i(A) = i - min {j < i : a_ij ≠ 0}` is spelled out in `equation_3_59_iff`. Block
systems are written with `Matrix.fromBlocks` over sum index types: the first substructure
system (3.62) is `fromBlocks A₁₁ A₁₃ A₁₃ᵀ A₃₃'` on `m₁ ⊕ m₃`, and the three-block matrix of
Remark 3.6 is `fromBlocks (fromBlocks A₁₁ 0 0 A₂₂) (fromRows A₁₃ A₂₃) (fromCols A₁₃ᵀ A₂₃ᵀ) A₃₃`
on `(m₁ ⊕ m₂) ⊕ m₃`; the Schur complement of a two-block matrix is `Matrix.schurComplement`,
`C - F B⁻¹ E` for `fromBlocks B E F C`.

## Contents

* `adjacencyGraph`, `adjacencyGraph_adj` — the graph `G(A)`.
* `equation_3_59`, `equation_3_59_iff`, `equation_3_60` — the envelope and the confinement of
  fill-in.
* `equation_3_63`, `remark_3_6_schur` — substructuring and the Schur complement system.
* `remark_3_6_cond` — `K₂(S) ≤ K₂(A)` for symmetric positive definite `A`.

The Cuthill–McKee and nested dissection reorderings (§3.9.1, §3.9.3) state no theorem, the
operation count (3.61) has no cost model, and Remark 3.5 is prose.

## Readings

The book defines `G(A)` for a rectangular `A ∈ ℝ^{m×n}` on `max(m, n)` vertices; the section
uses only square matrices, which is what is stated. In (3.60) the fill-in of the Cholesky
factor `H` is compared with `A` through `E(H + Hᵀ)`: the strictly lower part of `H + Hᵀ` is that
of `Hᵀ = L D^{1/2}`, whose pattern is that of the unit lower factor `L` of Theorem 3.4.
-/

open Finset Matrix

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### The graph of a matrix and the envelope -/

/-- **§3.9, the oriented graph `G(A)`** of `A ∈ ℝ^{n×n}`: the vertices are the indices
`1, …, n`, and a path directed from `i` to `j` exists iff `a_ij ≠ 0`; for `a_ii ≠ 0` the path
from `i` to itself is a loop. It is the backbone's `Matrix.adjDigraph A`. -/
def adjacencyGraph (A : Matrix (Fin n) (Fin n) ℝ) : Digraph (Fin n) := adjDigraph A

/-- The paths of `G(A)` are the nonzero entries of `A` (backbone `Matrix.adjDigraph_adj`). -/
theorem adjacencyGraph_adj (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (adjacencyGraph A).Adj i j ↔ A i j ≠ 0 :=
  adjDigraph_adj

/-- **(3.59), the envelope** (the book's "convex hull") of `A`: with
`m_i(A) = i - min {j < i : a_ij ≠ 0}`, `E(A) = {(i, j) : 0 < i - j ≤ m_i(A)}`, the strictly
lower positions of each row from its first nonzero entry to the diagonal. It is the backbone's
`Matrix.envelope A`; `equation_3_59_iff` spells the membership out. -/
def equation_3_59 (A : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n × Fin n) := envelope A

/-- **(3.59), spelled out.** `(i, j) ∈ E(A)` iff the set `{j₀ < i : a_{i j₀} ≠ 0}` is nonempty
and `0 < i - j ≤ m_i(A) = i - min {j₀ < i : a_{i j₀} ≠ 0}`; a row whose strict lower part
vanishes contributes nothing to the envelope. -/
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

/-- **(3.60).** For a symmetric positive definite `A` with Cholesky factor `H` (Theorem 3.6,
`A = Hᵀ H`), `E(A) = E(H + Hᵀ)`: fill-in is confined within the envelope of `A`, and reaches its
boundary. The strictly lower part of `H + Hᵀ` is that of `Hᵀ = L D^{1/2}`, `L` the unit lower
factor of Theorem 3.4, and `E(L) = E(A)` is the backbone's `Matrix.IsLU.envelope_eq`. -/
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

/-- Two `Sum.elim`s agree iff their halves do. -/
private theorem sum_elim_eq_iff {α β γ : Type*} {f f' : α → γ} {g g' : β → γ} :
    Sum.elim f g = Sum.elim f' g' ↔ f = f' ∧ g = g' := by
  rw [funext_iff, Sum.forall, funext_iff, funext_iff]
  rfl

/-- The two-block system `[[B, E], [F, C]] [x₁; x₃] = [b₁; b₃]` with `B` nonsingular is
equivalent to the Schur complement system `(C - F B⁻¹ E) x₃ = b₃ - F B⁻¹ b₁` together with
`B x₁ = b₁ - E x₃`. -/
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

/-- **(3.62)–(3.63), decomposition into substructures.** For the system of the first
substructure `[[A₁₁, A₁₃], [A₁₃ᵀ, A₃₃']] [x₁; x₃] = [b₁; b₃]` with `A₁₁ = H₁₁ᵀ H₁₁` (`H₁₁`
nonsingular), let `H₂₁ = H₁₁⁻ᵀ A₁₃` and `c₁ = H₁₁⁻ᵀ b₁`. Then `H₂₁ᵀ H₂₁ = A₁₃ᵀ A₁₁⁻¹ A₁₃` and
`H₂₁ᵀ c₁ = A₁₃ᵀ A₁₁⁻¹ b₁`, so eliminating `x₁` leaves the interface system with matrix
`A₃₃‴ = A₃₃' - H₂₁ᵀ H₂₁` — the Schur complement of the block matrix — and right-hand side
`b₃‴ = b₃ - H₂₁ᵀ c₁`; once it is solved, `x₁` follows from `A₁₁ x₁ = b₁ - A₁₃ x₃` (backbone
`Matrix.schurComplement`, `Matrix.fromBlocks_eq_mul_schurComplement`). -/
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

/-- **Remark 3.6, the Schur complement.** For the block matrix
`A = [[A₁₁, 0, A₁₃], [0, A₂₂, A₂₃], [A₁₃ᵀ, A₂₃ᵀ, A₃₃]]` with `A₁₁`, `A₂₂` nonsingular, the Schur
complement is `S = A₃₃ - A₁₃ᵀ A₁₁⁻¹ A₁₃ - A₂₃ᵀ A₂₂⁻¹ A₂₃`, and the system `A x = b` is equivalent
to the interface system `S x₃ = b₃ - A₁₃ᵀ A₁₁⁻¹ b₁ - A₂₃ᵀ A₂₂⁻¹ b₂` followed by the two systems of
reduced size `A₁₁ x₁ = b₁ - A₁₃ x₃`, `A₂₂ x₂ = b₂ - A₂₃ x₃` (backbone
`Matrix.fromBlocks_eq_mul_schurComplement`; Mathlib's `Matrix.inv_fromBlocks_zero₁₂_of_isUnit_iff`
inverts the block diagonal). -/
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
/-- **Remark 3.6, the conditioning of the interface system.** If the block matrix `A` is symmetric
and positive definite, then the system on the Schur complement `S` is no more ill conditioned than
the original one on `A`: `K₂(S) ≤ K₂(A)` (backbone
`Matrix.PosDef.condNumber_schurComplement_le`, whose proof is Axelsson's Lemma 3.12 without
interlacing — `0 ≤ S ≤ A₃₃` in the Loewner order gives `‖S‖₂ ≤ ‖A‖₂`, and `S⁻¹ = (A⁻¹)₃₃` gives
`‖S⁻¹‖₂ ≤ ‖A⁻¹‖₂`, a principal submatrix having the smaller spectral norm). Here `K₂` is
`NormedRing.condNumber` in Mathlib's scoped `L2Operator` matrix norm, which is the chapter's
`condNumber 2` transported to a sum index type (`condNumber_two_eq`), and `remark_3_6_schur`
identifies `A.schurComplement` with `A₃₃ - A₁₃ᵀ A₁₁⁻¹ A₁₃ - A₂₃ᵀ A₂₂⁻¹ A₂₃`. -/
theorem remark_3_6_cond
    {A : Matrix ((Fin m₁ ⊕ Fin m₂) ⊕ Fin m₃) ((Fin m₁ ⊕ Fin m₂) ⊕ Fin m₃) ℝ} (hA : A.PosDef) :
    NormedRing.condNumber A.schurComplement ≤ NormedRing.condNumber A := by
  rw [NormedRing.condNumber, NormedRing.condNumber, ← nonsing_inv_eq_ringInverse,
    ← nonsing_inv_eq_ringInverse]
  exact hA.condNumber_schurComplement_le

end Substructuring

end QuarteroniSaccoSaleri.Chapter03
