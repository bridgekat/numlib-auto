import Numlib.LinearAlgebra.Matrix.MMatrix
import Numlib.LinearAlgebra.Matrix.PerronFrobenius
import Numlib.LinearSolve.Stationary.Splitting
import NumlibSurface.SaadSparse.Common

/-!
# §1.10 Nonnegative matrices, M-matrices

Section 1.10 of Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
SIAM, 2003: the entrywise order (Definition 1.23) and its calculus (Proposition 1.24,
Proposition 1.26, Corollary 1.27), the Perron–Frobenius theorem (Theorem 1.25), the monotonicity
of the spectral radius (Theorem 1.28), the nonnegative Neumann criterion (Theorem 1.29), and
M-matrices (Definition 1.30, Theorems 1.31–1.33).

Saad's `A ≥ O` and `B ≥ A` are the **entrywise** order, `Matrix.EntrywiseNonneg` and
`Matrix.EntrywiseLE` (notation `≤ₑ`) of `Numlib/LinearAlgebra/Matrix/Order.lean` — not Mathlib's
`≤` on matrices, which is the Loewner order.  Definition 1.23 is that pair of predicates and
Definition 1.30 is `Matrix.IsMMatrix` of `Numlib/LinearAlgebra/Matrix/MMatrix.lean`, so neither
gets a declaration of its own here.  Saad's `ρ(A)` for a real matrix is
`Matrix.complexSpectralRadius A`, the spectral radius of the complexification: `spectrum ℝ` of a
real matrix is not the spectral radius.

Two clauses of the book are weaker here than in print.

* Theorem 1.25 calls the Perron eigenvalue *simple*.  Only **geometric** simplicity is proved
  (`theorem_1_25_simple`); algebraic simplicity needs the derivative of the characteristic
  polynomial through the adjugate, which nothing else in the corpus wants.  The book's clause that
  `ρ(A)` is *positive* is likewise not claimed.
* Theorems 1.31–1.33 are stated with the Jacobi iteration matrix written out as `1 - D⁻¹ A`;
  `theorem_1_31_jacobi` identifies it with the iteration operator of the Jacobi splitting of
  `Numlib/LinearSolve/Stationary/Splitting.lean`, which is the form §4.1 uses.

Saad's Problem P-1.33 asks whether clause (4) of Definition 1.30 — the nonnegativity of the
inverse — is redundant in the way Theorem 1.32 shows clause (1) to be.  It is not, and the answer
gets no declaration because it is a counterexample rather than a theorem: `!![1, -2; -2, 1]` has
positive diagonal entries, nonpositive off-diagonal entries and determinant `-3`, and its inverse
`!![-1/3, -2/3; -2/3, -1/3]` is entrywise negative.
-/

open Matrix

open scoped SaadSparse Matrix

namespace SaadSparse.Ch01

variable {n : ℕ}

/-! ### The entrywise order (Definition 1.23, Propositions 1.24 and 1.26, Corollary 1.27) -/

open scoped Matrix.Norms.Operator in
/-- **Saad Proposition 1.24**, the calculus of the entrywise order of Definition 1.23, in the
book's five clauses: (1) the order is reflexive, antisymmetric and transitive; (2) sums and
products of nonnegative matrices are nonnegative; (3) so are powers; (4) the order is preserved by
transposition; and (5) the induced norms `‖·‖₁` (the maximum absolute column sum, so the
`Matrix.Norms.Operator` norm of the transpose) and `‖·‖_∞` (the maximum absolute row sum) are
monotone on nonnegative matrices.

Every clause is a restatement of `Numlib/LinearAlgebra/Matrix/Order.lean` or of
`Numlib/LinearAlgebra/Matrix/PerronFrobenius.lean`, except clause (4), which is one line.  The
`2`-norm form of clause (5) is Problem P-1.28, stated separately as `problem_1_28` because the
Euclidean operator norm is a *different* scoped instance on the same type. -/
theorem proposition_1_24 :
    (∀ A : Matrix (Fin n) (Fin n) ℝ, A ≤ₑ A) ∧
      (∀ A B : Matrix (Fin n) (Fin n) ℝ, A ≤ₑ B → B ≤ₑ A → A = B) ∧
      (∀ A B C : Matrix (Fin n) (Fin n) ℝ, A ≤ₑ B → B ≤ₑ C → A ≤ₑ C) ∧
      (∀ A B : Matrix (Fin n) (Fin n) ℝ, A.EntrywiseNonneg → B.EntrywiseNonneg →
        (A + B).EntrywiseNonneg ∧ (A * B).EntrywiseNonneg) ∧
      (∀ (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ), A.EntrywiseNonneg → (A ^ k).EntrywiseNonneg) ∧
      (∀ A B : Matrix (Fin n) (Fin n) ℝ, A ≤ₑ B → Aᵀ ≤ₑ Bᵀ) ∧
      (∀ A B : Matrix (Fin n) (Fin n) ℝ, A.EntrywiseNonneg → A ≤ₑ B →
        ‖Aᵀ‖ ≤ ‖Bᵀ‖ ∧ ‖A‖ ≤ ‖B‖) :=
  ⟨EntrywiseLE.refl,
    fun _ _ hAB hBA => hAB.antisymm hBA,
    fun _ _ _ hAB hBC => hAB.trans hBC,
    fun _ _ hA hB => ⟨hA.add hB, hA.mul hB⟩,
    fun _ k hA => hA.pow k,
    fun _ _ hAB i j => hAB j i,
    fun _ _ hA hAB => ⟨EntrywiseLE.linfty_opNorm_transpose_le hA hAB,
      EntrywiseLE.linfty_opNorm_le hA hAB⟩⟩

open scoped Matrix.Norms.L2Operator in
/-- **Saad Problem P-1.28**: the Euclidean operator norm is monotone on nonnegative matrices too,
`O ≤ A ≤ B → ‖A‖₂ ≤ ‖B‖₂`.  This is the `2`-norm clause of Proposition 1.24;
`Matrix.EntrywiseLE.l2_opNorm_le` of `Numlib/LinearAlgebra/Matrix/PerronFrobenius.lean`. -/
theorem problem_1_28 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.EntrywiseNonneg) (hAB : A ≤ₑ B) :
    ‖A‖ ≤ ‖B‖ :=
  EntrywiseLE.l2_opNorm_le hA hAB

/-- **Saad Proposition 1.26**: the entrywise order is compatible with multiplication by a
nonnegative matrix on either side.  `Matrix.EntrywiseLE.mul_of_entrywiseNonneg_left` and its
right twin. -/
theorem proposition_1_26 {A B C : Matrix (Fin n) (Fin n) ℝ} (hC : C.EntrywiseNonneg)
    (hAB : A ≤ₑ B) : C * A ≤ₑ C * B ∧ A * C ≤ₑ B * C :=
  ⟨EntrywiseLE.mul_of_entrywiseNonneg_left hC hAB,
    EntrywiseLE.mul_of_entrywiseNonneg_right hC hAB⟩

/-- **Saad Corollary 1.27**, (1.42): powers are monotone on nonnegative matrices,
`O ≤ A ≤ B → A ^ k ≤ B ^ k`.  `Matrix.EntrywiseLE.pow`, whose proof is the book's induction
(1.43)–(1.44). -/
theorem corollary_1_27 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.EntrywiseNonneg) (hAB : A ≤ₑ B)
    (k : ℕ) : A ^ k ≤ₑ B ^ k :=
  EntrywiseLE.pow hA hAB k

/-! ### The Perron–Frobenius theorem (Theorem 1.25) -/

/-- **Saad Theorem 1.25**, the Perron–Frobenius theorem, which the book states without proof: an
entrywise nonnegative irreducible real matrix has `ρ(A)` as an eigenvalue, with an eigenvector all
of whose entries are positive.  This is
`Matrix.IsIrreducible.exists_pos_hasEigenvector_complexSpectralRadius` of
`Numlib/LinearAlgebra/Matrix/PerronFrobenius.lean`.

Irreducibility is Mathlib's `Matrix.IsIrreducible`: entrywise nonnegative, with the quiver of the
positive entries strongly connected, which is Saad's §1.10 notion read through the adjacency graph
of §3.3.4.  The simplicity clause is `theorem_1_25_simple`. -/
theorem theorem_1_25 [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsIrreducible) :
    Module.End.HasEigenvalue A.mulVecLin A.complexSpectralRadius.toReal ∧
      ∃ x : Fin n → ℝ, (∀ i, 0 < x i) ∧ A *ᵥ x = A.complexSpectralRadius.toReal • x := by
  obtain ⟨x, hpos, hx⟩ := hA.exists_pos_hasEigenvector_complexSpectralRadius
  refine ⟨Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, ?_⟩, x, hpos, hx⟩
  · rw [Module.End.mem_eigenspace_iff, mulVecLin_apply]
    exact hx
  · intro h
    exact absurd (congrFun h (Classical.arbitrary (Fin n))) (hpos _).ne'

/-- **Saad Theorem 1.25**, the simplicity clause, in its geometric form: the Perron eigenvalue of
an irreducible nonnegative matrix has a one-dimensional eigenspace.
`Matrix.IsIrreducible.finrank_eigenspace_complexSpectralRadius_eq_one`.  *Algebraic* simplicity,
which is what "simple" means in the book, is not proved: it needs the derivative of the
characteristic polynomial through the adjugate. -/
theorem theorem_1_25_simple [NeZero n] {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsIrreducible) :
    Module.finrank ℝ
        (Module.End.eigenspace A.mulVecLin A.complexSpectralRadius.toReal) = 1 :=
  hA.finrank_eigenspace_complexSpectralRadius_eq_one

/-! ### The spectral radius of a nonnegative matrix (Theorems 1.28 and 1.29) -/

/-- **Saad Theorem 1.28**, (1.45)–(1.46): the spectral radius is monotone on nonnegative
matrices, `O ≤ A ≤ B → ρ(A) ≤ ρ(B)`.  `Matrix.complexSpectralRadius_le_of_entrywiseLE`, whose
proof is the book's: Gelfand's formula applied to Corollary 1.27 and clause (5) of Proposition
1.24. -/
theorem theorem_1_28 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.EntrywiseNonneg) (hAB : A ≤ₑ B) :
    A.complexSpectralRadius ≤ B.complexSpectralRadius :=
  complexSpectralRadius_le_of_entrywiseLE hA hAB

/-- **Saad Theorem 1.29**, with (1.47): for an entrywise nonnegative `B`, `ρ(B) < 1` if and only
if `I - B` is nonsingular with an entrywise nonnegative inverse.
`Matrix.EntrywiseNonneg.complexSpectralRadius_lt_one_iff`.  This is the theorem Theorem 4.4 and
the M-matrix characterizations below rest on. -/
theorem theorem_1_29 {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.EntrywiseNonneg) :
    B.complexSpectralRadius < 1 ↔ IsUnit (1 - B) ∧ (1 - B)⁻¹.EntrywiseNonneg :=
  hB.complexSpectralRadius_lt_one_iff

/-! ### M-matrices (Definition 1.30, Theorems 1.31–1.33) -/

section MMatrix

variable {A : Matrix (Fin n) (Fin n) ℝ}

/-- A diagonal matrix with nonnegative diagonal is entrywise nonnegative. -/
private theorem entrywiseNonneg_diagonal {d : Fin n → ℝ} (hd : ∀ i, 0 ≤ d i) :
    (diagonal d).EntrywiseNonneg := by
  refine entrywiseNonneg_iff.2 fun i j => ?_
  by_cases h : i = j
  · subst h; rw [diagonal_apply_eq]; exact hd i
  · rw [diagonal_apply_ne _ h]

/-- The inverse of the diagonal part, entry by entry.  `Matrix.inv_diagonal` inverts the diagonal
in the Pi ring and is useless without `IsUnit`, so the inverse is identified by exhibiting a right
inverse instead. -/
private theorem inv_diagPart_eq (hd : ∀ i, A i i ≠ 0) :
    (diagPart A)⁻¹ = diagonal fun i => (A i i)⁻¹ := by
  have hD : diagPart A = diagonal A.diag := rfl
  refine inv_eq_right_inv ?_
  rw [hD, diagonal_mul_diagonal, ← diagonal_one]
  refine congrArg diagonal (funext fun i => ?_)
  simpa only [Pi.mul_apply, Pi.one_apply, diag_apply] using mul_inv_cancel₀ (hd i)

/-- The entries of the Jacobi iteration matrix `B = I - D⁻¹ A`. -/
private theorem jacobiMatrix_apply (hd : ∀ i, A i i ≠ 0) (i j : Fin n) :
    (1 - (diagPart A)⁻¹ * A) i j = (if i = j then 1 else 0) - (A i i)⁻¹ * A i j := by
  rw [Matrix.sub_apply, one_apply, inv_diagPart_eq hd, diagonal_mul]

/-- The Jacobi iteration matrix of a matrix with positive diagonal and nonpositive off-diagonal
entries is entrywise nonnegative: this is what makes Theorem 1.29 applicable to it. -/
private theorem entrywiseNonneg_jacobiMatrix (hd : ∀ i, 0 < A i i)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) : (1 - (diagPart A)⁻¹ * A).EntrywiseNonneg := by
  refine entrywiseNonneg_iff.2 fun i j => ?_
  rw [jacobiMatrix_apply (fun i => (hd i).ne') i j]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, inv_mul_cancel₀ (hd i).ne', sub_self]
  · rw [ite_eq_right h, zero_sub, neg_nonneg]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (hd i).le) (hoff i j h)

/-- **Saad Theorem 1.31**: a real matrix with positive diagonal and nonpositive off-diagonal
entries is an M-matrix exactly when its Jacobi iteration matrix `B = I - D⁻¹ A` has spectral
radius below `1`.

The proof is the book's.  Those two sign conditions are exactly what makes `B` entrywise
nonnegative, so Theorem 1.29 applies to it, and `I - B = D⁻¹ A` factors `A = D (I - B)` with `D`
and `D⁻¹` nonnegative: `A` is nonsingular with a nonnegative inverse if and only if `I - B` is. -/
theorem theorem_1_31 (hd : ∀ i, 0 < A i i) (hoff : ∀ i j, i ≠ j → A i j ≤ 0) :
    A.IsMMatrix ↔ (1 - (diagPart A)⁻¹ * A).complexSpectralRadius < 1 := by
  have hdne : ∀ i, A i i ≠ 0 := fun i => (hd i).ne'
  have hDunit : IsUnit (diagPart A) := (isUnit_diagPart_iff A).2 hdne
  have hDdet : IsUnit (diagPart A).det := (isUnit_iff_isUnit_det _).1 hDunit
  have hDnn : (diagPart A).EntrywiseNonneg :=
    entrywiseNonneg_diagonal (d := A.diag) fun i => (hd i).le
  have hDinvnn : ((diagPart A)⁻¹).EntrywiseNonneg := by
    rw [inv_diagPart_eq hdne]
    exact entrywiseNonneg_diagonal fun i => inv_nonneg.2 (hd i).le
  have hsub : 1 - (1 - (diagPart A)⁻¹ * A) = (diagPart A)⁻¹ * A := sub_sub_cancel _ _
  rw [theorem_1_29 (entrywiseNonneg_jacobiMatrix hd hoff), hsub]
  constructor
  · intro hA
    refine ⟨(isUnit_nonsing_inv_iff.2 hDunit).mul hA.isUnit, ?_⟩
    have hinv : ((diagPart A)⁻¹ * A)⁻¹ = A⁻¹ * diagPart A := by
      rw [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hDdet]
    rw [hinv]
    exact hA.inv_entrywiseNonneg.mul hDnn
  · rintro ⟨hu, hnn⟩
    have hAeq : A = diagPart A * ((diagPart A)⁻¹ * A) := by
      rw [← Matrix.mul_assoc, mul_nonsing_inv _ hDdet, Matrix.one_mul]
    refine ⟨hoff, hAeq ▸ hDunit.mul hu, ?_⟩
    have hAinv : A⁻¹ = ((diagPart A)⁻¹ * A)⁻¹ * (diagPart A)⁻¹ := by
      conv_lhs => rw [hAeq]
      rw [Matrix.mul_inv_rev]
    rw [hAinv]
    exact hnn.mul hDinvnn

/-- The matrix `I - D⁻¹ A` of Theorem 1.31 is the iteration operator of the Jacobi splitting
`A = D - (E + F)` of `Numlib/LinearSolve/Stationary/Splitting.lean`, which is the form §4.1 uses.
Read with `Matrix.jacobiSplitting_iterationOperator`, this makes the M-matrix hypothesis of
Chapter 4 checkable from the sign pattern of `A` alone. -/
theorem theorem_1_31_jacobi (h : IsUnit (diagPart A)) :
    (jacobiSplitting A h).iterationOperator = 1 - (diagPart A)⁻¹ * A := by
  have hm : (jacobiSplitting A h).m = diagPart A := rfl
  rw [Stationary.Splitting.iterationOperator, hm, ← nonsing_inv_eq_ringInverse]

/-- **Saad Theorem 1.32**: clause (1) of Definition 1.30 follows from the other three.  A
nonsingular real matrix with nonpositive off-diagonal entries and an entrywise nonnegative inverse
has positive diagonal entries, is therefore an M-matrix, and therefore has a convergent Jacobi
iteration matrix.

The diagonal clause is `Matrix.IsMMatrix.diag_pos`, whose proof is the book's: reading
`(A A⁻¹) i i = 1` entrywise, every off-diagonal term is nonpositive, so `A i i * A⁻¹ i i ≥ 1` and
both factors are positive. -/
theorem theorem_1_32 (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hu : IsUnit A)
    (hinv : A⁻¹.EntrywiseNonneg) :
    (∀ i, 0 < A i i) ∧ A.IsMMatrix ∧ (1 - (diagPart A)⁻¹ * A).complexSpectralRadius < 1 :=
  have hA : A.IsMMatrix := ⟨hoff, hu, hinv⟩
  ⟨hA.diag_pos, hA, (theorem_1_31 hA.diag_pos hoff).1 hA⟩

/-- **Saad Theorem 1.33**: an M-matrix stays an M-matrix when its entries are increased, as long
as the off-diagonal entries stay nonpositive.

The book's chain of entrywise inequalities between the two Jacobi matrices,
`I - D_B⁻¹ B ≤ I - D_A⁻¹ A`, holds entry by entry because `A i j ≤ B i j ≤ 0` off the diagonal
while `0 < A i i ≤ B i i` on it, so the reciprocals go the other way.  Theorem 1.28 then compares
the spectral radii and Theorem 1.31 is applied twice. -/
theorem theorem_1_33 {B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix) (hAB : A ≤ₑ B)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) : B.IsMMatrix := by
  have hdA : ∀ i, 0 < A i i := hA.diag_pos
  have hdB : ∀ i, 0 < B i i := fun i => lt_of_lt_of_le (hdA i) (hAB i i)
  refine (theorem_1_31 hdB hoff).2 (lt_of_le_of_lt (theorem_1_28
    (entrywiseNonneg_jacobiMatrix hdB hoff) ?_) ((theorem_1_31 hdA hA.offDiag_nonpos).1 hA))
  intro i j
  rw [jacobiMatrix_apply (fun i => (hdB i).ne') i j, jacobiMatrix_apply (fun i => (hdA i).ne') i j]
  by_cases h : i = j
  · subst h
    rw [inv_mul_cancel₀ (hdA i).ne', inv_mul_cancel₀ (hdB i).ne']
  · rw [ite_eq_right h, zero_sub, zero_sub, neg_le_neg_iff]
    calc (A i i)⁻¹ * A i j
        ≤ (A i i)⁻¹ * B i j := mul_le_mul_of_nonneg_left (hAB i j) (inv_nonneg.2 (hdA i).le)
      _ ≤ (B i i)⁻¹ * B i j :=
          mul_le_mul_of_nonpos_right (inv_anti₀ (hdA i) (hAB i i)) (hoff i j h)

end MMatrix

end SaadSparse.Ch01
