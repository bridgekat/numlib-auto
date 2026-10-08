import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.LeastSquares
import NumlibSurface.QuarteroniSaccoSaleri.Chapter03.Section03

/-!
# Quarteroni–Sacco–Saleri §3.4: other types of factorization

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §3.4, over the backbone `Numlib/LinearAlgebra/Matrix/LU` (the
`L D Mᵀ` and `L D Lᵀ` factorizations, `Matrix.IsLDM`), `Numlib/LinearAlgebra/Matrix/Cholesky`
(the Cholesky factorization `Matrix.IsCholesky`, its uniqueness and the recurrence
`Matrix.cholesky`), `Numlib/FloatingPoint/LU` (its backward error), `Numlib/LinearAlgebra/Matrix/QR`
and `Numlib/LinearAlgebra/Matrix/LeastSquares` (the full and the reduced QR factorization,
`Matrix.IsQR`, uniqueness `Matrix.IsThinQR.unique`) and Mathlib's Gram–Schmidt process with
`Numlib/Analysis/InnerProductSpace/GramSchmidt`.

## Conventions

The `L D Mᵀ` factorization is the backbone's `Matrix.IsLDM A L D M`: `L` and `M` unit lower
triangular (so that `Mᵀ` is unit upper triangular), `D` diagonal and `L D Mᵀ = A`; the `L D Lᵀ`
factorization is `IsLDM A L D L`. The Cholesky factorization `A = Hᵀ H` of Theorem 3.6 is
`Matrix.IsCholesky A H` — `H` upper triangular with positive diagonal and `Hᴴ H = A`, which over
`ℝ` reads `Hᵀ H = A` (`theorem_3_6_iff`); the recurrence (3.45) computes the *lower* factor `Hᵀ`
as `Matrix.cholesky A`. "Symmetric positive definite" is Mathlib's `Matrix.PosDef` over `ℝ`,
which includes the symmetry.

A matrix `A ∈ ℝ^{m×n}` is `Matrix (Fin m) (Fin n) ℝ`; its columns as vectors of `ℝᵐ` with the
Euclidean norm are `columns A j = toLp 2 (Aᵀ j) : EuclideanSpace ℝ (Fin m)`, and "`A` has rank
`n`" (full column rank) is `LinearIndependent ℝ Aᵀ`. The full QR factorization of Definition 3.1
is the backbone's `Matrix.IsQR A Q R` (`Q` orthogonal, `R` upper trapezoidal), the reduced factors
`Q̃ = Q(1:m, 1:n)` and `R̃ = R(1:n, 1:n)` of (3.48) are `Matrix.firstColumns Q h` and
`Matrix.firstRows R h` for `h : n ≤ m`, and a reduced factorization is a pair `Q̃`, `R̃` with
`A = Q̃ R̃`, `Q̃ᵀ Q̃ = 1` and `R̃` upper triangular. The Gram–Schmidt vectors `q_k` of (3.49) are
Mathlib's `gramSchmidt ℝ x k`, the normalized ones `q̃_k` are `gramSchmidtNormed ℝ x k`, and the
reduced factors they produce are the backbone's `Matrix.gramSchmidtQ A` and `Matrix.gramSchmidtR A`
(`Matrix.isThinQR_gramSchmidtQ`); the modified sweep is the backbone's
`InnerProductSpace.modifiedGramSchmidtSweep`. The book's scalar
product `(x, y)` is `inner ℝ y x`, which over `ℝ` is `inner ℝ x y`.

Rounding-error statements are in the relational model `m : FloatingPoint.RoundingModel ℝ` of
`Numlib/FloatingPoint/Model`; the computed Cholesky factor is an admissible
`FloatingPoint.RoundsCholesky m A H̃`, the recurrence (3.45) with every product, running
difference, square root and division rounded once.

## Contents

* `theorem_3_5`, `ldl_of_isSymm`, `ldl_hilbert_three` — §3.4.1 and the `L D Lᵀ` factorization.
* `theorem_3_6`, `theorem_3_6_iff`, `equation_3_45`, `cholesky_backward_error` — §3.4.2.
* `definition_3_1`, `definition_3_1_iff`, `property_3_3`, `property_3_3_unique`,
  `property_3_3_cholesky`, `property_3_3_diag_ne_zero_iff`, `property_3_3_range` — §3.4.3, the
  QR factorization.
* `columns`, `equation_3_49`, `modifiedGramSchmidt_eq` — Gram–Schmidt and its modified form.

Example 3.4 (a numerical comparison of the two Gram–Schmidt variants) and Programs 7–8 are not
nodes; the operation counts are prose.

## Readings and errata

Theorem 3.5 says "all the principal minors" of `A` are nonzero; its proof uses the *leading*
principal minors, of orders `1, …, n` (the last one for `D` to be invertible), and that is the
hypothesis stated. Property 3.3 claims a *unique* reduced factorization `A = Q̃ R̃`; as printed it
is unique only up to a diagonal matrix of signs (`Q̃ D`, `D R̃`), and the uniqueness holds once
the diagonal of `R̃` is normalized positive — which the last clause, `R̃` being the Cholesky
factor of `Aᵀ A`, presupposes; `property_3_3_unique` states it so. The book quotes Wilkinson's
normwise bound `‖δA‖₂ ≤ 8 n (n + 1) u ‖A‖₂` for the computed Cholesky factor; the surface states
the componentwise bound of [higham2002accuracy] Theorem 10.3, `|δA| ≤ γ_{n+1} |H̃ᵀ| |H̃|`, and
Wilkinson's constant is not reproduced.
-/

open Finset Matrix InnerProductSpace WithLp

namespace QuarteroniSaccoSaleri.Chapter03

variable {n : ℕ}

/-! ### §3.4.1: the `L D Mᵀ` factorization, Theorem 3.5 -/

/-- **Theorem 3.5.** If all the (leading) principal minors of `A ∈ ℝ^{n×n}` are nonzero then
there exist a unique diagonal matrix `D`, a unique unit lower triangular matrix `L` and a unique
unit upper triangular matrix `Mᵀ` such that `A = L D Mᵀ` (backbone `Matrix.existsUnique_isLDM`).
The book says "all the principal minors"; its proof uses the leading ones, of orders `1, …, n`. -/
theorem theorem_3_5 {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ k, (A.leadingPrincipalSubmatrix k).det ≠ 0) :
    ∃! LDM : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
      IsLDM A LDM.1 LDM.2.1 LDM.2.2 :=
  existsUnique_isLDM <| isUnit_strictLeadingPrincipalSubmatrix_of_forall_isUnit fun k =>
    (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))

/-- **§3.4.2, the `L D Lᵀ` factorization.** When `A` is symmetric (and its leading principal
minors are nonzero) the `L D Mᵀ` factorization has `M = L`, so `A = L D Lᵀ`; and if `A` is also
positive definite the diagonal entries of `D` are positive (backbone `Matrix.IsLDM.eq_of_isSymm`,
`Matrix.IsLDM.diag_pos_of_posDef`). -/
theorem ldl_of_isSymm {A : Matrix (Fin n) (Fin n) ℝ} (hs : A.IsSymm)
    (hA : ∀ k, (A.leadingPrincipalSubmatrix k).det ≠ 0) :
    (∀ L D M, IsLDM A L D M → M = L) ∧ (∃ L D, IsLDM A L D L) ∧
      (A.PosDef → ∀ L D, IsLDM A L D L → ∀ i, 0 < D i i) := by
  have hA' : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k) :=
    isUnit_strictLeadingPrincipalSubmatrix_of_forall_isUnit fun k =>
      (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hA k))
  refine ⟨fun L D M h => h.eq_of_isSymm hs hA', ?_, fun hpd L D h i => h.diag_pos_of_posDef hpd i⟩
  obtain ⟨⟨L, D, M⟩, h, -⟩ := existsUnique_isLDM hA'
  have h' : IsLDM A L D M := h
  exact ⟨L, D, h'.eq_of_isSymm hs hA' ▸ h'⟩

/-- **§3.4.2, the display for `H₃`.** The Hilbert matrix of order `3` has the `L D Lᵀ`
factorization `H₃ = [1, 0, 0; 1/2, 1, 0; 1/3, 1, 1] diag(1, 1/12, 1/180) [1, 1/2, 1/3; 0, 1, 1;
0, 0, 1]`. -/
theorem ldl_hilbert_three :
    hilbert ℝ 3 = !![1, 0, 0; 1/2, 1, 0; 1/3, 1, 1] * diagonal ![1, 1/12, 1/180] *
      !![1, 1/2, 1/3; 0, 1, 1; 0, 0, 1] := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [hilbert] <;> norm_num

/-! ### §3.4.2: the Cholesky factorization, Theorem 3.6 -/

section Cholesky

variable {A H : Matrix (Fin n) (Fin n) ℝ}

/-- The backbone's `Matrix.IsCholesky A H` over `ℝ` is the book's (3.44): `H` upper triangular
with positive diagonal entries and `A = Hᵀ H`. -/
theorem theorem_3_6_iff :
    IsCholesky A H ↔ H.IsUpperTriangular ∧ (∀ i, 0 < H i i) ∧ Hᵀ * H = A := by
  constructor
  · intro h
    refine ⟨h.isUpperTriangular, h.diag_pos, ?_⟩
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact h.conjTranspose_mul_self
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [conjTranspose_eq_transpose_of_trivial]; exact h3⟩

/-- **Theorem 3.6, (3.44).** Let `A ∈ ℝ^{n×n}` be symmetric and positive definite. Then there
exists a unique upper triangular matrix `H` with positive diagonal entries such that `A = Hᵀ H`,
the Cholesky factorization (backbone `Matrix.existsUnique_isCholesky`). -/
theorem theorem_3_6 (hA : A.PosDef) :
    ∃! H : Matrix (Fin n) (Fin n) ℝ, H.IsUpperTriangular ∧ (∀ i, 0 < H i i) ∧ Hᵀ * H = A := by
  simpa only [theorem_3_6_iff] using existsUnique_isCholesky hA

/-- **(3.45), the Cholesky recurrence.** The entries `h_ij` of the lower factor `Hᵀ` are computed
by `h₁₁ = √a₁₁` and, for `i = 2, …, n`, `h_ij = (a_ij - ∑_{k<j} h_ik h_jk) / h_jj` for
`j = 1, …, i - 1` and `h_ii = (a_ii - ∑_{k<i} h_ik²)^{1/2}`: this is the backbone's total function
`Matrix.cholesky A` (`Matrix.cholesky_apply_of_lt`, `Matrix.cholesky_apply_self`), which for a
symmetric positive definite `A` is the transpose of the factor `H` of Theorem 3.6
(`Matrix.isCholesky_cholesky`). -/
theorem equation_3_45 [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) :
    cholesky A 0 0 = √(A 0 0) ∧
    (∀ i j, j < i →
      cholesky A i j = (A i j - ∑ k with k < j, cholesky A i k * cholesky A j k) / cholesky A j j) ∧
    (∀ i, cholesky A i i = √(A i i - ∑ k with k < i, cholesky A i k ^ 2)) ∧
    (∀ i j, i < j → cholesky A i j = 0) ∧
    (A.PosDef → IsCholesky A (cholesky A)ᵀ) := by
  have hself : ∀ i, cholesky A i i = √(A i i - ∑ k with k < i, cholesky A i k ^ 2) := by
    intro i
    rw [cholesky_apply_self]
    simp [Real.norm_eq_abs, sq_abs]
  refine ⟨?_, fun i j hij => ?_, hself, fun i j hij => cholesky_apply_of_gt A hij, fun hA => ?_⟩
  · rw [hself, Finset.sum_eq_zero fun k hk =>
      absurd (mem_filter.1 hk).2 (not_lt.2 (Fin.zero_le k)), sub_zero]
  · rw [cholesky_apply_of_lt A hij]
    simp
  · rw [← conjTranspose_eq_transpose_of_trivial]
    exact isCholesky_cholesky hA

open FloatingPoint in
/-- **§3.4.2, stability of the Cholesky recurrence.** The factor `H̃` computed by (3.45) in
floating-point arithmetic with unit roundoff `u`, `(n + 1) u < 1` (an admissible
`FloatingPoint.RoundsCholesky m A H̃` of a symmetric `A`, with nonzero computed diagonal),
satisfies `H̃ᵀ H̃ = A + δA` with `|δA| ≤ ((n + 1) u / (1 - (n + 1) u)) |H̃ᵀ| |H̃|` entrywise
(backbone `FloatingPoint.exists_roundsCholesky_eq_add`, [higham2002accuracy] Theorem 10.3). The
book quotes Wilkinson's normwise `‖δA‖₂ ≤ 8 n (n + 1) u ‖A‖₂`, which is not reproduced. -/
theorem cholesky_backward_error {m : RoundingModel ℝ} (hn : ((n + 1 : ℕ) : ℝ) * m.u < 1)
    (hA : A.IsSymm) {Ht : Matrix (Fin n) (Fin n) ℝ} (h : RoundsCholesky m A Ht)
    (hd : ∀ i, Ht i i ≠ 0) :
    ∃ δA : Matrix (Fin n) (Fin n) ℝ,
      δA.abs ≤ₑ ((n + 1 : ℕ) * m.u / (1 - (n + 1 : ℕ) * m.u)) • (Htᵀ.abs * Ht.abs) ∧
        Htᵀ * Ht = A + δA := by
  have hu : m.u < 1 := by
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    nlinarith [m.u_nonneg]
  obtain ⟨δA, hδA, hLU⟩ := exists_roundsCholesky_eq_add hu (by rwa [Fintype.card_fin]) hA h hd
  refine ⟨δA, ?_, hLU⟩
  rwa [Fintype.card_fin, gamma_def] at hδA

end Cholesky

/-! ### §3.4.3: the QR factorization, Definition 3.1 and Property 3.3 -/

section QR

variable {m : ℕ}

/-- **Definition 3.1.** A matrix `A ∈ ℝ^{m×n}`, `m ≥ n`, *admits a QR factorization* if there
exist an orthogonal matrix `Q ∈ ℝ^{m×m}` and an upper trapezoidal matrix `R ∈ ℝ^{m×n}`, with
null rows from the `(n + 1)`-th on, such that `A = Q R` (3.46): the backbone's
`Matrix.IsQR A Q R`, spelled out in `definition_3_1_iff`. -/
def definition_3_1 (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ Q R, IsQR A Q R

/-- **Definition 3.1, spelled out**, and its existence: `A` admits a QR factorization iff there
are `Q` orthogonal and `R` vanishing below the diagonal (hence with null rows from the
`(n + 1)`-th on) with `A = Q R`; and every matrix does, by Householder triangularization
(backbone `Matrix.exists_isQR`, `Matrix.exists_unitary_mul_upperTriangular`). -/
theorem definition_3_1_iff (A : Matrix (Fin m) (Fin n) ℝ) :
    (definition_3_1 A ↔ ∃ Q ∈ orthogonalGroup (Fin m) ℝ, ∃ R : Matrix (Fin m) (Fin n) ℝ,
      (∀ (i : Fin m) (j : Fin n), (j : ℕ) < i → R i j = 0) ∧
        (∀ i : Fin m, n ≤ i → ∀ j, R i j = 0) ∧ A = Q * R) ∧
      definition_3_1 A := by
  refine ⟨⟨?_, ?_⟩, exists_isQR A⟩
  · rintro ⟨Q, R, h⟩
    exact ⟨Q, h.mem_unitaryGroup, R, h.apply_eq_zero, fun i hi j => h.apply_eq_zero_of_le hi j,
      h.mul_eq.symm⟩
  · rintro ⟨Q, hQ, R, hR, -, hA⟩
    exact ⟨Q, R, hQ, hR, hA.symm⟩

variable {A : Matrix (Fin m) (Fin n) ℝ} {Q : Matrix (Fin m) (Fin m) ℝ}
variable {R : Matrix (Fin m) (Fin n) ℝ}

/-- **Property 3.3, existence, (3.47)–(3.48).** Let `A ∈ ℝ^{m×n}` (of rank `n`, `n ≤ m`) have a
QR factorization `A = Q R`. Then the submatrices `Q̃ = Q(1:m, 1:n)` and `R̃ = R(1:n, 1:n)` give the
reduced factorization `A = Q̃ R̃`, where `Q̃` has orthonormal columns (`Q̃ᵀ Q̃ = I`) and `R̃` is
upper triangular (backbone `Matrix.IsQR.isThinQR`); the rank hypothesis is not needed for this
part. -/
theorem property_3_3 (h : IsQR A Q R) (hnm : n ≤ m) :
    A = firstColumns Q hnm * firstRows R hnm ∧
      (firstColumns Q hnm)ᵀ * firstColumns Q hnm = 1 ∧ (firstRows R hnm).IsUpperTriangular := by
  obtain ⟨h1, h2, h3⟩ := h.isThinQR hnm
  refine ⟨h1.symm, ?_, h3⟩
  rwa [conjTranspose_eq_transpose_of_trivial] at h2

/-- **Property 3.3, uniqueness.** A reduced factorization `A = Q̃ R̃` with `Q̃ᵀ Q̃ = I` and `R̃`
upper triangular with *positive diagonal* is unique: two such factorizations coincide (backbone
`Matrix.IsThinQR.unique`). As printed, without the sign normalization, uniqueness fails
(`Q̃ D`, `D R̃` for a diagonal `D` of signs); the normalization is implicit in the book, whose
`R̃` "coincides with the Cholesky factor" of `Aᵀ A`. -/
theorem property_3_3_unique {Q₁ Q₂ : Matrix (Fin m) (Fin n) ℝ} {R₁ R₂ : Matrix (Fin n) (Fin n) ℝ}
    (h₁ : A = Q₁ * R₁) (h₂ : A = Q₂ * R₂) (hQ₁ : Q₁ᵀ * Q₁ = 1) (hQ₂ : Q₂ᵀ * Q₂ = 1)
    (hR₁ : R₁.IsUpperTriangular) (hR₂ : R₂.IsUpperTriangular) (hd₁ : ∀ j, 0 < R₁ j j)
    (hd₂ : ∀ j, 0 < R₂ j j) : Q₁ = Q₂ ∧ R₁ = R₂ :=
  IsThinQR.unique ⟨h₁.symm, by rwa [conjTranspose_eq_transpose_of_trivial], hR₁⟩
    ⟨h₂.symm, by rwa [conjTranspose_eq_transpose_of_trivial], hR₂⟩ hd₁ hd₂

/-- **Property 3.3, the last clause.** If `A` has full rank `n` then `Aᵀ A` is symmetric
positive definite, and the triangular factor `R̃` (with positive diagonal) of a reduced
factorization `A = Q̃ R̃` is its Cholesky factor `H`: `Aᵀ A = R̃ᵀ Q̃ᵀ Q̃ R̃ = R̃ᵀ R̃` (backbone
`Matrix.posDef_conjTranspose_mul_self_of_linearIndependent`,
`Matrix.cholesky_conjTranspose_mul_self_of_qr`). -/
theorem property_3_3_cholesky (hA : LinearIndependent ℝ Aᵀ) {Qt : Matrix (Fin m) (Fin n) ℝ}
    {Rt : Matrix (Fin n) (Fin n) ℝ} (h : A = Qt * Rt) (hQ : Qtᵀ * Qt = 1)
    (hR : Rt.IsUpperTriangular) (hd : ∀ j, 0 < Rt j j) :
    (Aᵀ * A).PosDef ∧ IsCholesky (Aᵀ * A) Rt ∧ cholesky (Aᵀ * A) = Rtᵀ := by
  have hQ' : Qtᴴ * Qt = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  refine ⟨?_, ?_, ?_⟩
  · rw [← conjTranspose_eq_transpose_of_trivial]
    exact posDef_conjTranspose_mul_self_of_linearIndependent hA
  · rw [← conjTranspose_eq_transpose_of_trivial]
    exact isCholesky_conjTranspose_mul_self_of_qr h hQ' hR hd
  · rw [← conjTranspose_eq_transpose_of_trivial, ← conjTranspose_eq_transpose_of_trivial]
    exact cholesky_conjTranspose_mul_self_of_qr h hQ' hR hd

/-- **§3.4.3, after (3.49): "the diagonal entries of `R̃` are all nonzero only if `A` has full
rank"**, and conversely: for a reduced factorization `A = Q̃ R̃` from a QR factorization of `A`,
the diagonal of `R̃` has no zero iff the columns of `A` are linearly independent (backbone
`Matrix.IsQR.firstRows_diag_ne_zero_of_linearIndependent`; conversely `R̃` is then nonsingular
and `A = Q̃ R̃` is injective on vectors). -/
theorem property_3_3_diag_ne_zero_iff (h : IsQR A Q R) (hnm : n ≤ m) :
    (∀ j, firstRows R hnm j j ≠ 0) ↔ LinearIndependent ℝ Aᵀ := by
  refine ⟨fun hd => ?_, h.firstRows_diag_ne_zero_of_linearIndependent hnm⟩
  have hR : IsUnit (firstRows R hnm) :=
    (h.isUpperTriangular_firstRows hnm).isUnit_iff.2 hd
  have hQ : Function.Injective (firstColumns Q hnm).mulVec := by
    intro x y hxy
    have := congrArg ((firstColumns Q hnm)ᵀ *ᵥ ·) hxy
    simpa [mulVec_mulVec, (property_3_3 h hnm).2.1] using this
  rw [show Aᵀ = A.col from rfl, ← mulVec_injective_iff, ← h.firstColumns_mul_firstRows hnm]
  intro x y hxy
  simp only [← mulVec_mulVec] at hxy
  exact mulVec_injective_iff_isUnit.2 hR (hQ hxy)

/-- **Property 3.3, the range clause.** If `A` has full rank `n`, the column vectors of `Q̃` form
an orthonormal basis of `range(A)`, the column space of `A`: `Q̃ᵀ Q̃ = I` and
`span (columns of Q̃) = span (columns of A)` (backbone `Matrix.IsQR.span_firstColumns_eq`). -/
theorem property_3_3_range (h : IsQR A Q R) (hnm : n ≤ m) (hA : LinearIndependent ℝ Aᵀ) :
    (firstColumns Q hnm)ᵀ * firstColumns Q hnm = 1 ∧
      Submodule.span ℝ (Set.range (firstColumns Q hnm)ᵀ) = Submodule.span ℝ (Set.range Aᵀ) :=
  ⟨(property_3_3 h hnm).2.1, h.span_firstColumns_eq hnm hA⟩

end QR

/-! ### §3.4.3: Gram–Schmidt orthogonalization, (3.49), and its modified form -/

section GramSchmidt

variable {m : ℕ}

/-- The columns `a₁, …, aₙ` of `A ∈ ℝ^{m×n}` as vectors of `ℝᵐ` with the Euclidean norm. -/
noncomputable def columns (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) : EuclideanSpace ℝ (Fin m) :=
  toLp 2 (Aᵀ j)

/-- **(3.49), the Gram–Schmidt orthogonalization.** Starting from linearly independent vectors
`x₁, …, xₙ` of `ℝᵐ`, the vectors `q₁ = x₁`, `q_{k+1} = x_{k+1} - ∑_{i≤k} ((q_i, x_{k+1}) /
(q_i, q_i)) q_i` (Mathlib's `gramSchmidt ℝ x`) are mutually orthogonal and nonzero; the
normalized vectors `q̃_k = q_k / ‖q_k‖₂` (`gramSchmidtNormed ℝ x`) are orthonormal and satisfy
`q_{k+1} = x_{k+1} - ∑_{j≤k} (q̃_j, x_{k+1}) q̃_j`; and for the columns `a_j` of a full-rank
`A ∈ ℝ^{m×n}` the `q̃_j` are the columns of the `Q̃` of the reduced factorization (3.47), with
`R̃ = Q̃ᵀ A` (backbone `Matrix.isThinQR_gramSchmidtQ`, which by `property_3_3_unique` is *the*
reduced factorization with positive diagonal). Mathlib's `gramSchmidt_def''`,
`gramSchmidt_orthogonal`, `gramSchmidtNormed_orthonormal`. -/
theorem equation_3_49 [NeZero n] (x : Fin n → EuclideanSpace ℝ (Fin m))
    (hx : LinearIndependent ℝ x) (A : Matrix (Fin m) (Fin n) ℝ) (hA : LinearIndependent ℝ Aᵀ) :
    gramSchmidt ℝ x 0 = x 0 ∧
    (∀ k, gramSchmidt ℝ x k = x k - ∑ i ∈ Iio k,
      (inner ℝ (gramSchmidt ℝ x i) (x k) / inner ℝ (gramSchmidt ℝ x i) (gramSchmidt ℝ x i)) •
        gramSchmidt ℝ x i) ∧
    (∀ i j, i ≠ j → inner ℝ (gramSchmidt ℝ x i) (gramSchmidt ℝ x j) = 0) ∧
    (∀ k, gramSchmidt ℝ x k ≠ 0) ∧
    (∀ k, gramSchmidtNormed ℝ x k = ‖gramSchmidt ℝ x k‖⁻¹ • gramSchmidt ℝ x k) ∧
    Orthonormal ℝ (gramSchmidtNormed ℝ x) ∧
    (∀ k, gramSchmidt ℝ x k = x k - ∑ j ∈ Iio k,
      inner ℝ (gramSchmidtNormed ℝ x j) (x k) • gramSchmidtNormed ℝ x j) ∧
    (∀ j, (gramSchmidtQ A).col j = ofLp (gramSchmidtNormed ℝ (columns A) j)) ∧
    gramSchmidtR A = (gramSchmidtQ A)ᵀ * A ∧
    A = gramSchmidtQ A * gramSchmidtR A ∧ (gramSchmidtQ A)ᵀ * gramSchmidtQ A = 1 ∧
      (gramSchmidtR A).IsUpperTriangular ∧ ∀ j, 0 < gramSchmidtR A j j := by
  have hdef : ∀ k, gramSchmidt ℝ x k = x k - ∑ i ∈ Iio k,
      (inner ℝ (gramSchmidt ℝ x i) (x k) / inner ℝ (gramSchmidt ℝ x i) (gramSchmidt ℝ x i)) •
        gramSchmidt ℝ x i := by
    intro k
    have := gramSchmidt_def'' ℝ x k
    simp only [RCLike.ofReal_real_eq_id, id, ← real_inner_self_eq_norm_sq] at this
    exact eq_sub_iff_add_eq.2 this.symm
  have hne : ∀ k, gramSchmidt ℝ x k ≠ 0 := fun k => gramSchmidt_ne_zero k hx
  have hqr : A = gramSchmidtQ A * gramSchmidtR A ∧ (gramSchmidtQ A)ᵀ * gramSchmidtQ A = 1 ∧
      (gramSchmidtR A).IsUpperTriangular ∧ ∀ j, 0 < gramSchmidtR A j j := by
    have h := isThinQR_gramSchmidtQ hA
    exact ⟨h.mul_eq.symm, by simpa using h.conjTranspose_mul_self, h.isUpperTriangular,
      gramSchmidtR_apply_self_pos hA⟩
  refine ⟨?_, hdef, fun i j hij => gramSchmidt_orthogonal ℝ x hij, hne, fun k => ?_,
    gramSchmidtNormed_orthonormal hx, fun k => ?_, fun j => rfl, ?_, hqr⟩
  · rw [hdef, Finset.sum_eq_zero fun i hi =>
      absurd (Finset.mem_Iio.1 hi) (not_lt.2 (Fin.zero_le i)), sub_zero]
  · rw [gramSchmidtNormed]
    simp
  · rw [hdef k]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gramSchmidtNormed, inner_smul_left, smul_smul, real_inner_self_eq_norm_sq]
    simp only [RCLike.ofReal_real_eq_id, id, conj_trivial]
    congr 1
    field_simp [hne i]
  · ext i j
    rw [gramSchmidtR, of_apply, mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    exact Finset.sum_congr rfl fun r _ => by simp [gramSchmidtQ, mul_comm]

/-- **§3.4.3, the modified Gram–Schmidt method.** At step `k + 1`, the projections of `a_{k+1}`
along `q̃₁, …, q̃_k` are subtracted one after the other, each computed on the current vector
(`InnerProductSpace.modifiedGramSchmidtSweep`); the resulting vector `a^{(k)}_{k+1}` coincides
with the vector `q_{k+1}` of the standard Gram–Schmidt process, since by the orthogonality of
`q̃₁, …, q̃_k`, `a^{(k)}_{k+1} = a_{k+1} - ∑_{j≤k} (q̃_j, a_{k+1}) q̃_j` (backbone
`InnerProductSpace.modifiedGramSchmidt_eq_gramSchmidt`, through
`InnerProductSpace.modifiedGramSchmidtSweep_eq_sub_sum` and (3.49)). The vectors `a_1, a_2, …`
are a sequence `x : ℕ → ℝᵐ`; a finite family is one padded arbitrarily, the statement at step `k`
reading only `x 0, …, x k`. -/
theorem modifiedGramSchmidt_eq (x : ℕ → EuclideanSpace ℝ (Fin m)) (k : ℕ) :
    modifiedGramSchmidtSweep ℝ (gramSchmidtNormed ℝ x) (x k) k = gramSchmidt ℝ x k :=
  modifiedGramSchmidt_eq_gramSchmidt ℝ x k

end GramSchmidt

end QuarteroniSaccoSaleri.Chapter03
