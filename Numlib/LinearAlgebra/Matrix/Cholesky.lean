/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Cholesky` beside `Mathlib.Analysis.Matrix.LDL`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Matrix.PosDef
import Numlib.Direct.Substitution
import Numlib.LinearAlgebra.Matrix.LU

/-!
# The Cholesky factorization and positive definite matrices

The Cholesky factorization `A = Hᴴ H` of a Hermitian positive definite matrix, with `H` upper
triangular of positive diagonal, as a specification `Matrix.IsCholesky A H`; its existence and
uniqueness ([quarteroni2000numerical] Theorem 3.6, [higham2002accuracy] Theorem 10.1); the
recurrence computing it as a total function `Matrix.cholesky`; Sylvester's criterion and the other
characterizations of positive definiteness of [quarteroni2000numerical] Property 1.18; the entry
bounds of positive (semi)definite matrices; and the bridge to Mathlib's `Matrix.LDL`.

## Main definitions

* `Matrix.IsCholesky A H`: `H` is upper triangular with positive diagonal and `Hᴴ * H = A`.
* `Matrix.cholesky A`: the lower triangular factor `Hᴴ` computed by the recurrence
  [quarteroni2000numerical] (3.45), as one total function on a finite linear order
  (`Matrix.choleskyAux` is its well-founded recursion).

## Main results

* `Matrix.exists_isCholesky`, `Matrix.IsCholesky.unique`, `Matrix.existsUnique_isCholesky`:
  [quarteroni2000numerical] Theorem 3.6. Existence goes through the `L D Lᴴ` factorization
  obtained from `Matrix.existsUnique_isLDM` of `Numlib/LinearAlgebra/Matrix/LU`
  (`Matrix.exists_isLDM_conjTranspose_of_posDef`), `H = D^{1/2} Lᴴ`; uniqueness is the uniqueness
  of the LU factorization `A = (Hᴴ D⁻¹) (D H)`, `D = diag H` (`Matrix.IsCholesky.isLU`).
* `Matrix.IsCholesky.posDef`: the converse, `Hᴴ H` is positive definite for nonsingular `H`.
* `Matrix.cholesky_eq_of_isCholesky`, `Matrix.isCholesky_cholesky`: the recurrence (3.45) computes
  the factor. As for the Doolittle recurrence, no bordering induction is needed: the recurrence
  restates the entrywise identities `Matrix.IsCholesky.apply_eq_sum` satisfied by *any* Cholesky
  factor, so the computed entries agree with it by strong induction along the order of `min i j`.
* `Matrix.posDef_iff_forall_det_leadingPrincipalSubmatrix_pos`: Sylvester's criterion,
  [quarteroni2000numerical] Property 1.18 (3), through the pivots of the `L D Lᴴ` factorization as
  ratios of consecutive leading minors (`Matrix.IsLU.diag_upper_eq_div_leadingPrincipalMinor`).
* `Matrix.posDef_iff_exists_isUnit_conjTranspose_mul_self` (Property 1.18 (4)),
  `Matrix.posDef_iff_forall_principalSubmatrix_eigenvalues_pos` (Property 1.18 (2)).
* `Matrix.PosSemidef.norm_apply_sq_le_mul_re_diag`,
  `Matrix.PosSemidef.norm_apply_le_add_re_diag_div_two`,
  `Matrix.PosSemidef.norm_apply_le_max_re_diag` (with its definite case
  `Matrix.PosDef.norm_apply_le_max_re_diag`): `|a_ij|² ≤ a_ii a_jj`, hence
  `|a_ij| ≤ (a_ii + a_jj) / 2`, so the entry of largest modulus of a positive semidefinite matrix is
  diagonal ([quarteroni2000numerical] §1.12, [golub2013matrix] (4.2.12)–(4.2.14)).
* `Matrix.LDL.lower_isUnitLowerTriangular` (the TODO of `Mathlib/Analysis/Matrix/LDL.lean`),
  `Matrix.LDL.diagEntries_pos`, `Matrix.isLDM_ldl`, `Matrix.LDL.lower_eq_of_isLDM`: Mathlib's `LDL`
  factors are the unique `L D Lᴴ` factors of `Numlib/LinearAlgebra/Matrix/LU`.
* `Matrix.isCholesky_conjTranspose_mul_self_of_qr`, `Matrix.cholesky_conjTranspose_mul_self_of_qr`:
  the triangular factor of a reduced QR factorization `X = Q R` is the Cholesky factor of `Xᴴ X`
  ([quarteroni2000numerical] Property 3.3, last clause).

## Implementation notes

The index type is `[Fintype n] [LinearOrder n]` throughout; only the section on Mathlib's `LDL`
adds the `[LocallyFiniteOrderBot n]` that `Matrix.LDL.lower` demands, and nothing else depends on
it — existence of the Cholesky factor is proved through the LU theory instead. The scalars are
`[RCLike 𝕜]` with `open scoped ComplexOrder`, so that `Matrix.PosDef` and "`0 < H i i`" make sense
over `ℂ` as over `ℝ`; the `L D Mᵀ` factorization of `LU.lean` is used in the Hermitian form
`M = Lᴴᵀ`, whose transpose is `Lᴴ`. A `2 × 2` principal minor is read as a submatrix along
`![i, j] : Fin 2 → n` (`Matrix.PosSemidef.submatrix`, `Matrix.det_fin_two`).

## References

* [quarteroni2000numerical] §1.12, §3.4.2, §3.4.3.
* [higham2002accuracy] §10.1.
-/

open Finset
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [LinearOrder n] {𝕜 : Type*} [RCLike 𝕜]

/-! ### Entry bounds of positive (semi)definite matrices -/

section Entries

variable {A : Matrix n n 𝕜}

omit [Fintype n] [LinearOrder n] in
/-- The `2 × 2` principal minor of a positive semidefinite matrix is nonnegative:
`‖a_ij‖² ≤ a_ii a_jj` ([quarteroni2000numerical] §1.12). -/
theorem PosSemidef.norm_apply_sq_le_mul_re_diag (hA : A.PosSemidef) (i j : n) :
    ‖A i j‖ ^ 2 ≤ RCLike.re (A i i) * RCLike.re (A j j) := by
  classical
  have h := (hA.submatrix ![i, j]).det_nonneg
  rw [det_fin_two] at h
  simp only [submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← hA.1.apply j i, RCLike.star_def, RCLike.mul_conj, ← hA.1.coe_re_apply_self i,
    ← hA.1.coe_re_apply_self j, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, ← RCLike.ofReal_sub,
    RCLike.ofReal_nonneg, sub_nonneg] at h
  exact h

omit [Fintype n] [LinearOrder n] in
/-- Every entry of a positive semidefinite matrix is bounded in modulus by the mean of the two
diagonal entries in its row and column, `‖a_ij‖ ≤ (a_ii + a_jj) / 2` ([golub2013matrix] (4.2.12)):
`‖a_ij‖² ≤ a_ii a_jj ≤ ((a_ii + a_jj) / 2)²`. -/
theorem PosSemidef.norm_apply_le_add_re_diag_div_two (hA : A.PosSemidef) (i j : n) :
    ‖A i j‖ ≤ (RCLike.re (A i i) + RCLike.re (A j j)) / 2 := by
  have hi : 0 ≤ RCLike.re (A i i) := (RCLike.nonneg_iff.1 hA.diag_nonneg).1
  have hj : 0 ≤ RCLike.re (A j j) := (RCLike.nonneg_iff.1 hA.diag_nonneg).1
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  refine (hA.norm_apply_sq_le_mul_re_diag i j).trans ?_
  nlinarith [sq_nonneg (RCLike.re (A i i) - RCLike.re (A j j))]

omit [Fintype n] [LinearOrder n] in
/-- Every entry of a positive semidefinite matrix is bounded in modulus by the larger of the two
diagonal entries in its row and column, so the entry of largest modulus lies on the diagonal
([golub2013matrix] (4.2.14)). -/
theorem PosSemidef.norm_apply_le_max_re_diag (hA : A.PosSemidef) (i j : n) :
    ‖A i j‖ ≤ max (RCLike.re (A i i)) (RCLike.re (A j j)) :=
  (hA.norm_apply_le_add_re_diag_div_two i j).trans (by
    linarith [le_max_left (RCLike.re (A i i)) (RCLike.re (A j j)),
      le_max_right (RCLike.re (A i i)) (RCLike.re (A j j))])

omit [Fintype n] [LinearOrder n] in
/-- Every entry of a positive definite matrix is bounded in modulus by the larger of the two
diagonal entries in its row and column, so the entry of largest modulus lies on the diagonal
([quarteroni2000numerical] §1.12, after Property 1.18); the definite case of
`Matrix.PosSemidef.norm_apply_le_max_re_diag`. -/
theorem PosDef.norm_apply_le_max_re_diag (hA : A.PosDef) (i j : n) :
    ‖A i j‖ ≤ max (RCLike.re (A i i)) (RCLike.re (A j j)) :=
  hA.posSemidef.norm_apply_le_max_re_diag i j

end Entries

/-! ### Leading principal submatrices of a positive definite matrix -/

section Leading

variable {A : Matrix n n 𝕜} (hA : A.PosDef)
include hA

omit [Fintype n] in
/-- The leading principal submatrices of a positive definite matrix are positive definite. -/
theorem PosDef.leadingPrincipalSubmatrix (k : n) : (A.leadingPrincipalSubmatrix k).PosDef :=
  hA.submatrix Subtype.val_injective

omit [Fintype n] in
/-- The strict leading principal submatrices of a positive definite matrix are positive
definite. -/
theorem PosDef.strictLeadingPrincipalSubmatrix (k : n) :
    (A.strictLeadingPrincipalSubmatrix k).PosDef :=
  hA.submatrix Subtype.val_injective

/-- The leading principal minors of a positive definite matrix are positive. -/
theorem PosDef.det_leadingPrincipalSubmatrix_pos (k : n) :
    0 < (A.leadingPrincipalSubmatrix k).det :=
  (hA.leadingPrincipalSubmatrix k).det_pos

/-- The leading principal submatrices of a positive definite matrix are nonsingular. -/
theorem PosDef.isUnit_leadingPrincipalSubmatrix (k : n) :
    IsUnit (A.leadingPrincipalSubmatrix k) :=
  (hA.leadingPrincipalSubmatrix k).isUnit

/-- The strict leading principal submatrices of a positive definite matrix are nonsingular. -/
theorem PosDef.isUnit_strictLeadingPrincipalSubmatrix (k : n) :
    IsUnit (A.strictLeadingPrincipalSubmatrix k) :=
  (hA.strictLeadingPrincipalSubmatrix k).isUnit

end Leading

/-! ### The Hermitian `L D Lᴴ` factorization -/

section LDLstar

omit [Fintype n] in
/-- The conjugate transpose of a lower triangular matrix is upper triangular. -/
theorem IsLowerTriangular.conjTranspose_isUpperTriangular {L : Matrix n n 𝕜}
    (hL : L.IsLowerTriangular) : Lᴴ.IsUpperTriangular := fun i j hij => by
  rw [conjTranspose_apply, hL (i := j) (j := i) (OrderDual.toDual_lt_toDual.2 hij), star_zero]

omit [Fintype n] in
/-- The conjugate transpose of an upper triangular matrix is lower triangular. -/
theorem IsUpperTriangular.conjTranspose_isLowerTriangular {U : Matrix n n 𝕜}
    (hU : U.IsUpperTriangular) : Uᴴ.IsLowerTriangular := fun i j hij => by
  rw [conjTranspose_apply, hU (i := j) (j := i) (OrderDual.toDual_lt_toDual.1 hij), star_zero]

omit [Fintype n] in
/-- The entrywise conjugate `Lᴴᵀ` of a unit lower triangular matrix is unit lower triangular. -/
theorem IsUnitLowerTriangular.conjTranspose_transpose {L : Matrix n n 𝕜}
    (hL : L.IsUnitLowerTriangular) : Lᴴᵀ.IsUnitLowerTriangular where
  isLowerTriangular i j hij := by
    rw [transpose_apply, conjTranspose_apply, hL.isLowerTriangular (i := i) (j := j) hij, star_zero]
  diag_eq_one i := by rw [transpose_apply, conjTranspose_apply, hL.diag_eq_one, star_one]

variable {A L D M : Matrix n n 𝕜}

/-- The conjugate transpose of an `L D Mᵀ` factorization is the `L D Mᵀ` factorization
`Aᴴ = Mᴴᵀ Dᴴ (Lᴴᵀ)ᵀ`. -/
theorem IsLDM.conjTranspose (h : IsLDM A L D M) : IsLDM Aᴴ Mᴴᵀ Dᴴ Lᴴᵀ where
  isUnitLowerTriangular_left := h.isUnitLowerTriangular_right.conjTranspose_transpose
  isDiag := h.isDiag.conjTranspose
  isUnitLowerTriangular_right := h.isUnitLowerTriangular_left.conjTranspose_transpose
  mul_eq := by
    rw [← h.mul_eq, conjTranspose_mul, conjTranspose_mul, transpose_transpose,
      conjTranspose_transpose, transpose_conjTranspose, Matrix.mul_assoc]

/-- For a Hermitian matrix with nonsingular strict leading principal submatrices, the `L D Mᵀ`
factorization is Hermitian: `M = Lᴴᵀ` (so that `Mᵀ = Lᴴ`) and `D` is real. The conjugate transpose
of the factorization is a second factorization of `A`, and `Matrix.existsUnique_isLDM` identifies
the two. -/
theorem IsLDM.eq_of_isHermitian (h : IsLDM A L D M) (hA : A.IsHermitian)
    (hlead : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) : M = Lᴴᵀ ∧ D = Dᴴ := by
  have h' := h.conjTranspose
  rw [hA.eq] at h'
  obtain ⟨LDM₀, -, huniq⟩ := existsUnique_isLDM hlead
  have := (huniq (Mᴴᵀ, Dᴴ, Lᴴᵀ) h').trans (huniq (L, D, M) h).symm
  simp only [Prod.mk.injEq] at this
  obtain ⟨hL, hD, -⟩ := this
  refine ⟨?_, hD.symm⟩
  rw [← hL]
  ext i j
  simp only [transpose_apply, conjTranspose_apply, star_star]

/-- The Hermitian `L D Lᴴ` factorization of a Hermitian matrix with nonsingular strict leading
principal submatrices ([golub2013matrix] Theorem 4.1.3; unique by `Matrix.existsUnique_isLDM`),
from `Matrix.existsUnique_isLDM`. -/
theorem exists_isLDM_conjTranspose_of_isHermitian (hA : A.IsHermitian)
    (hlead : ∀ k, IsUnit (A.strictLeadingPrincipalSubmatrix k)) : ∃ L D, IsLDM A L D Lᴴᵀ := by
  obtain ⟨⟨L, D, M⟩, h, -⟩ := existsUnique_isLDM hlead
  obtain ⟨hM, -⟩ := h.eq_of_isHermitian hA hlead
  exact ⟨L, D, hM ▸ h⟩

/-- A matrix `A = L D Lᴴ` with `L` unit lower triangular is positive definite exactly when the
diagonal of `D` is positive: `A` is congruent to `D`. -/
theorem IsLDM.posDef_iff (h : IsLDM A L D Lᴴᵀ) : A.PosDef ↔ ∀ i, 0 < D i i := by
  have hU : IsUnit Lᴴ := (isUnit_conjTranspose _).2 h.isUnitLowerTriangular_left.isUnit
  have hL : L * D * Lᴴ = star Lᴴ * D * Lᴴ := by
    rw [star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [← h.mul_eq, transpose_transpose, hL, Matrix.IsUnit.posDef_star_left_conjugate_iff hU]
  conv_lhs => rw [← h.isDiag.diagonal_diag]
  rw [posDef_diagonal_iff]
  rfl

/-- The pivots of the `L D Lᴴ` factorization of a Hermitian matrix are positive when the leading
principal minors are positive: `d_k = det A(≤ k) / det A(< k)`, by strong induction along the
order (`det A(< k)` is the product of the earlier pivots). -/
theorem IsLDM.diag_pos_of_forall_det_pos (h : IsLDM A L D M)
    (hpos : ∀ k, 0 < (A.leadingPrincipalSubmatrix k).det) (k : n) : 0 < D k k := by
  have hLU := h.isLU
  have hdiag : ∀ k, (D * Mᵀ) k k = D k k := fun k => by
    rw [h.isDiag.isUpperTriangular.mul_apply_self
      h.isUnitLowerTriangular_right.isLowerTriangular.transpose_isUpperTriangular, transpose_apply,
      h.isUnitLowerTriangular_right.diag_eq_one, mul_one]
  suffices ∀ k, 0 < (D * Mᵀ) k k by rw [← hdiag]; exact this k
  intro k
  induction k using WellFoundedLT.induction with
  | ind k ih =>
  have hlt : 0 < (A.strictLeadingPrincipalSubmatrix k).det := by
    rw [hLU.det_strictLeadingPrincipalSubmatrix]
    exact Finset.prod_pos fun i hi => ih i (mem_filter.1 hi).2
  rw [hLU.diag_upper_eq_div_leadingPrincipalMinor hlt.ne']
  exact div_pos (hpos k) hlt

/-- A positive definite matrix has an `L D Lᴴ` factorization with positive pivots
([quarteroni2000numerical] §3.4.2). -/
theorem exists_isLDM_conjTranspose_of_posDef (hA : A.PosDef) :
    ∃ L D, IsLDM A L D Lᴴᵀ ∧ ∀ i, 0 < D i i := by
  obtain ⟨L, D, h⟩ :=
    exists_isLDM_conjTranspose_of_isHermitian hA.1 hA.isUnit_strictLeadingPrincipalSubmatrix
  exact ⟨L, D, h, h.posDef_iff.1 hA⟩

end LDLstar

/-! ### Sylvester's criterion -/

section Sylvester

variable {A : Matrix n n 𝕜}

/-- **Sylvester's criterion**, [quarteroni2000numerical] Property 1.18 (3): a Hermitian matrix is
positive definite if and only if all its leading principal minors are positive. Forwards, every
leading principal submatrix of a positive definite matrix is positive definite, so its determinant
is positive. Backwards, the leading principal submatrices are nonsingular, so `A = L D Lᴴ`
(`Matrix.exists_isLDM_conjTranspose_of_isHermitian`); the pivots `d_k = det A(≤ k) / det A(< k)`
are positive (`Matrix.IsLDM.diag_pos_of_forall_det_pos`), and `A` is congruent to `D`. -/
theorem posDef_iff_forall_det_leadingPrincipalSubmatrix_pos (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ k, 0 < (A.leadingPrincipalSubmatrix k).det := by
  refine ⟨fun h k => h.det_leadingPrincipalSubmatrix_pos k, fun hpos => ?_⟩
  have hlead : ∀ k, IsUnit (A.leadingPrincipalSubmatrix k) := fun k =>
    (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hpos k).ne')
  obtain ⟨L, D, h⟩ := exists_isLDM_conjTranspose_of_isHermitian hA
    (isUnit_strictLeadingPrincipalSubmatrix_of_forall_isUnit hlead)
  exact h.posDef_iff.2 (h.diag_pos_of_forall_det_pos hpos)

omit [Fintype n] in
/-- [quarteroni2000numerical] Property 1.18 (2): a Hermitian matrix is positive definite if and
only if the eigenvalues of all its principal submatrices are positive. Forwards, every principal
submatrix is positive definite; backwards, the principal submatrix along `univ` is a reindexing of
`A` itself. -/
theorem posDef_iff_forall_principalSubmatrix_eigenvalues_pos [Finite n] (hA : A.IsHermitian) :
    A.PosDef ↔
      ∀ (s : Finset n) (i : s), 0 < (hA.submatrix (Subtype.val : s → n)).eigenvalues i := by
  cases nonempty_fintype n
  constructor
  · intro h s i
    exact (h.submatrix Subtype.val_injective).eigenvalues_pos i
  · intro h
    have hsub : (A.submatrix (Subtype.val : {x // x ∈ (univ : Finset n)} → n)
        Subtype.val).PosDef :=
      (hA.submatrix _).posDef_iff_eigenvalues_pos.2 (h univ)
    have := hsub.submatrix (e := fun i : n => (⟨i, mem_univ i⟩ : {x // x ∈ (univ : Finset n)}))
      fun i j hij => Subtype.mk.inj hij
    rwa [submatrix_submatrix, show (Subtype.val ∘ fun i : n =>
      (⟨i, mem_univ i⟩ : {x // x ∈ (univ : Finset n)})) = id from rfl, submatrix_id_id] at this

end Sylvester

/-! ### The Cholesky specification -/

/-- `IsCholesky A H`: `H` is upper triangular with positive (real) diagonal and `Hᴴ * H = A`, the
Cholesky factorization `A = Hᴴ H` of [quarteroni2000numerical] Theorem 3.6 ((3.44); Higham writes
`A = Rᴴ R`). Theorems about "the Cholesky factor" are theorems about any `H` satisfying it, and
`Matrix.IsCholesky.unique` says there is only one. -/
structure IsCholesky (A H : Matrix n n 𝕜) : Prop where
  /-- The factor is upper triangular. -/
  isUpperTriangular : H.IsUpperTriangular
  /-- The diagonal of the factor is positive. -/
  diag_pos : ∀ i, 0 < H i i
  /-- The factor multiplies to `A`. -/
  conjTranspose_mul_self : Hᴴ * H = A

namespace IsCholesky

variable {A H : Matrix n n 𝕜} (h : IsCholesky A H)
include h

/-- The diagonal of a Cholesky factor has no zero. -/
theorem diag_ne_zero (i : n) : H i i ≠ 0 := (h.diag_pos i).ne'

/-- The diagonal of a Cholesky factor is real. -/
theorem star_diag (i : n) : star (H i i) = H i i :=
  RCLike.conj_eq_iff_im.2 (RCLike.pos_iff.1 (h.diag_pos i)).2

/-- The diagonal of a Cholesky factor is the cast of its real part. -/
theorem coe_re_diag (i : n) : (RCLike.re (H i i) : 𝕜) = H i i :=
  RCLike.conj_eq_iff_re.1 (h.star_diag i)

/-- A Cholesky factor is nonsingular. -/
theorem isUnit : IsUnit H :=
  (isUnit_iff_forall_diag_ne_zero_of_isUpperTriangular h.isUpperTriangular).2 h.diag_ne_zero

/-- **The converse of [quarteroni2000numerical] Theorem 3.6** (and Property 1.18 (4)): a matrix
with a Cholesky factorization is positive definite, since `Hᴴ H` is positive definite for a
nonsingular `H`. -/
theorem posDef : A.PosDef :=
  h.conjTranspose_mul_self ▸
    PosDef.conjTranspose_mul_self H (mulVec_injective_iff_isUnit.2 h.isUnit)

/-- A matrix with a Cholesky factorization is Hermitian. -/
theorem isHermitian : A.IsHermitian := h.posDef.isHermitian

/-- The entries of `A = Hᴴ H`: `a_ij = ∑_{k ≤ min i j} h̄_ki h_kj`, since `H` vanishes below the
diagonal. -/
theorem apply_eq_sum (i j : n) :
    A i j = ∑ k ∈ univ.filter (· ≤ min i j), star (H k i) * H k j := by
  rw [← h.conjTranspose_mul_self, mul_apply]
  simp only [conjTranspose_apply]
  refine (Finset.sum_filter_of_ne fun k _ hk => ?_).symm
  rw [le_min_iff]
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  rcases hcon with hik | hjk
  · exact hk (by rw [h.isUpperTriangular hik, star_zero, zero_mul])
  · exact hk (by rw [h.isUpperTriangular hjk, mul_zero])

/-- The off-diagonal identity of the Cholesky recurrence, [quarteroni2000numerical] (3.45), first
line: for `j < i`, `h̄_ji h_jj = a_ij - ∑_{k < j} h̄_ki h_kj`. -/
theorem star_apply_mul_diag_eq {i j : n} (hij : j < i) :
    star (H j i) * H j j = A i j - ∑ k ∈ univ.filter (· < j), star (H k i) * H k j := by
  rw [h.apply_eq_sum, min_eq_right hij.le, sum_filter_le_eq_add, add_sub_cancel_left]

/-- The diagonal identity of the Cholesky recurrence, [quarteroni2000numerical] (3.45), second
line: `h_ii² = a_ii - ∑_{k < i} ‖h_ki‖²`, so `h_ii = √(a_ii - ∑_{k < i} ‖h_ki‖²)`. -/
theorem re_diag_eq_sqrt (i : n) :
    RCLike.re (H i i) =
      Real.sqrt (RCLike.re (A i i) - ∑ k ∈ univ.filter (· < i), ‖H k i‖ ^ 2) := by
  have hsum : A i i = ((∑ k ∈ univ.filter (· < i), ‖H k i‖ ^ 2 : ℝ) : 𝕜) +
      ((‖H i i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [h.apply_eq_sum, min_self, sum_filter_le_eq_add, RCLike.ofReal_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by
        rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
    · rw [RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
  have hre : RCLike.re (A i i) - ∑ k ∈ univ.filter (· < i), ‖H k i‖ ^ 2 = ‖H i i‖ ^ 2 := by
    rw [hsum, map_add, RCLike.ofReal_re, RCLike.ofReal_re, add_sub_cancel_left]
  rw [hre, Real.sqrt_sq (norm_nonneg _)]
  conv_rhs => rw [← h.coe_re_diag i]
  rw [RCLike.norm_ofReal, abs_of_pos (RCLike.pos_iff.1 (h.diag_pos i)).1]

/-- A Cholesky factorization is the LU factorization `A = (Hᴴ D⁻¹) (D H)` with `D = diag H`. -/
theorem isLU : IsLU A (Hᴴ * diagonal fun i => (H i i)⁻¹) (diagonal (fun i => H i i) * H) where
  isUnitLowerTriangular := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [mul_diagonal, conjTranspose_apply,
        h.isUpperTriangular (OrderDual.toDual_lt_toDual.1 hij), star_zero, zero_mul]
    · rw [mul_diagonal, conjTranspose_apply, h.star_diag, mul_inv_cancel₀ (h.diag_ne_zero i)]
  isUpperTriangular := (blockTriangular_diagonal _).mul h.isUpperTriangular
  mul_eq := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (h.diag_ne_zero _), diagonal_one, Matrix.one_mul,
      h.conjTranspose_mul_self]

/-- **Uniqueness of the Cholesky factorization** ([quarteroni2000numerical] Theorem 3.6,
[higham2002accuracy] Theorem 10.1): two Cholesky factors of a matrix coincide. Both give LU
factorizations `A = (Hᴴ D⁻¹) (D H)` of a positive definite matrix, which are unique
(`Matrix.IsLU.unique`); the diagonal of `D H` is `h_ii²`, which determines the positive `h_ii`, and
then `H = D⁻¹ (D H)`. -/
theorem unique {H₂ : Matrix n n 𝕜} (h₂ : IsCholesky A H₂) : H = H₂ := by
  obtain ⟨-, hU⟩ := h.isLU.unique h₂.isLU h.posDef.isUnit_strictLeadingPrincipalSubmatrix
  have hdiag : ∀ i, H i i = H₂ i i := fun i => by
    have := congrFun (congrFun hU i) i
    rw [diagonal_mul, diagonal_mul, ← sq, ← sq] at this
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 this with h' | h'
    · exact h'
    · have h1 := h.diag_pos i
      rw [h'] at h1
      have h2 := add_pos h1 (h₂.diag_pos i)
      rw [neg_add_cancel] at h2
      exact absurd h2 (lt_irrefl _)
  ext i j
  have := congrFun (congrFun hU i) j
  rw [diagonal_mul, diagonal_mul, hdiag i] at this
  exact mul_left_cancel₀ (h₂.diag_ne_zero i) this

end IsCholesky

/-! ### Existence of the Cholesky factorization -/

section Existence

variable {A : Matrix n n 𝕜}

/-- **Existence of the Cholesky factorization** ([quarteroni2000numerical] Theorem 3.6,
[higham2002accuracy] Theorem 10.1): a positive definite matrix `A = L D Lᴴ` has the Cholesky
factor `H = D^{1/2} Lᴴ`, upper triangular with the positive diagonal `√d_i`. -/
theorem exists_isCholesky (hA : A.PosDef) : ∃ H, IsCholesky A H := by
  obtain ⟨L, D, h, hD⟩ := exists_isLDM_conjTranspose_of_posDef hA
  set s : n → 𝕜 := fun i => ((Real.sqrt (RCLike.re (D i i)) : ℝ) : 𝕜) with hs
  have hre : ∀ i, 0 < RCLike.re (D i i) := fun i => (RCLike.pos_iff.1 (hD i)).1
  have hss : ∀ i, s i * s i = D i i := fun i => by
    rw [hs, ← RCLike.ofReal_mul, Real.mul_self_sqrt (hre i).le]
    exact RCLike.conj_eq_iff_re.1 (RCLike.conj_eq_iff_im.2 (RCLike.pos_iff.1 (hD i)).2)
  have hstar : star s = s := funext fun i => by simp [hs]
  refine ⟨diagonal s * Lᴴ, (blockTriangular_diagonal _).mul
    h.isUnitLowerTriangular_left.isLowerTriangular.conjTranspose_isUpperTriangular, fun i => ?_, ?_⟩
  · rw [diagonal_mul, conjTranspose_apply, h.isUnitLowerTriangular_left.diag_eq_one, star_one,
      mul_one, hs]
    exact RCLike.ofReal_pos.2 (Real.sqrt_pos.2 (hre i))
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, hstar,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s), diagonal_mul_diagonal, ← h.mul_eq,
      transpose_transpose, Matrix.mul_assoc]
    congr 2
    conv_rhs => rw [← h.isDiag.diagonal_diag]
    exact congrArg _ (funext hss)

/-- **[quarteroni2000numerical] Theorem 3.6**, [higham2002accuracy] Theorem 10.1: a positive
definite matrix has exactly one Cholesky factorization. -/
theorem existsUnique_isCholesky (hA : A.PosDef) : ∃! H, IsCholesky A H := by
  obtain ⟨H, h⟩ := exists_isCholesky hA
  exact ⟨H, h, fun H' h' => h'.unique h⟩

/-- [quarteroni2000numerical] Property 1.18 (4): a matrix is positive definite if and only if it
is `Hᴴ H` for a nonsingular `H`. Neither direction needs the matrix to be assumed Hermitian. -/
theorem posDef_iff_exists_isUnit_conjTranspose_mul_self :
    A.PosDef ↔ ∃ H : Matrix n n 𝕜, IsUnit H ∧ Hᴴ * H = A := by
  constructor
  · intro hA
    obtain ⟨H, h⟩ := exists_isCholesky hA
    exact ⟨H, h.isUnit, h.conjTranspose_mul_self⟩
  · rintro ⟨H, hH, rfl⟩
    exact PosDef.conjTranspose_mul_self H (mulVec_injective_iff_isUnit.2 hH)

end Existence

/-! ### The Cholesky recurrence -/

/-- The Cholesky recurrence, [quarteroni2000numerical] (3.45), as one total function on a finite
linear order, in the lower triangular indexing of the book's `h_ij` (the entries of `Hᴴ`):
`choleskyAux A i j = (A i j - ∑_{k < j} h_ik h̄_jk) / h_jj` for `j < i`,
`choleskyAux A i i = √(re a_ii - ∑_{k < i} ‖h_ik‖²)` and `0` above the diagonal. The recursion is
well founded on the number of indices below `min i j`, the off-diagonal entries after the diagonal
one at the same level, exactly as `Matrix.luPacked`; off the positive definite cone it computes
junk (`√` of a negative number is `0`, `x / 0 = 0`), and `Matrix.isCholesky_cholesky` says when
the result is the Cholesky factor. -/
noncomputable def choleskyAux (A : Matrix n n 𝕜) : n → n → 𝕜
  | i, j =>
    if j < i then
      (A i j - ∑ k ∈ (univ.filter (· < j)).attach, choleskyAux A i k * star (choleskyAux A j k)) /
        choleskyAux A j j
    else if i = j then
      ((Real.sqrt (RCLike.re (A i i) -
        ∑ k ∈ (univ.filter (· < i)).attach, ‖choleskyAux A i k‖ ^ 2) : ℝ) : 𝕜)
    else 0
termination_by i j => (#{k | k < min i j}, if j < i then 1 else 0)
decreasing_by
  all_goals first
    | -- the calls `choleskyAux A j k` and `choleskyAux A i k` below the diagonal, `k < j < i`
      (have hr : (k : n) < j := (mem_filter.1 k.2).2
       have hji : j < i := ‹j < i›
       first
         | rw [min_eq_right hr.le, min_eq_right hji.le]
         | rw [min_eq_right (hr.trans hji).le, min_eq_right hji.le]
       exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr))
    | -- the call `choleskyAux A j j`, at the same level
      (have hji : j < i := ‹j < i›
       rw [min_self, min_eq_right hji.le]
       refine Prod.Lex.right _ ?_
       simp [hji])
    | -- the diagonal branch, `k < i = j`
      (have hr : (k : n) < i := (mem_filter.1 k.2).2
       have hij : i = j := ‹i = j›
       subst hij
       rw [min_eq_right hr.le, min_self]
       exact Prod.Lex.left _ _ (card_filter_lt_lt_of_lt hr))

/-- The lower triangular Cholesky factor `Hᴴ` computed by the recurrence
[quarteroni2000numerical] (3.45) (`Matrix.choleskyAux`), as a matrix. -/
noncomputable def cholesky (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  of fun i j => choleskyAux A i j

section Recurrence

variable (A : Matrix n n 𝕜)

/-- The Cholesky recurrence below the diagonal, [quarteroni2000numerical] (3.45), first line. -/
theorem cholesky_apply_of_lt {i j : n} (hij : j < i) :
    cholesky A i j =
      (A i j - ∑ k ∈ univ.filter (· < j), cholesky A i k * star (cholesky A j k)) /
        cholesky A j j := by
  simp only [cholesky, of_apply]
  rw [choleskyAux, ite_eq_left hij,
    Finset.sum_attach (univ.filter (· < j)) fun k => choleskyAux A i k * star (choleskyAux A j k)]

/-- The Cholesky recurrence on the diagonal, [quarteroni2000numerical] (3.45), second line. -/
theorem cholesky_apply_self (i : n) :
    cholesky A i i =
      ((Real.sqrt (RCLike.re (A i i) - ∑ k ∈ univ.filter (· < i), ‖cholesky A i k‖ ^ 2) : ℝ) :
        𝕜) := by
  simp only [cholesky, of_apply]
  rw [choleskyAux, ite_eq_right (lt_irrefl i), ite_eq_left rfl,
    Finset.sum_attach (univ.filter (· < i)) fun k => ‖choleskyAux A i k‖ ^ 2]

/-- The Cholesky recurrence vanishes above the diagonal. -/
theorem cholesky_apply_of_gt {i j : n} (hij : i < j) : cholesky A i j = 0 := by
  simp only [cholesky, of_apply]
  rw [choleskyAux, ite_eq_right (not_lt.2 hij.le), ite_eq_right hij.ne]

/-- The computed Cholesky factor is lower triangular. -/
theorem isLowerTriangular_cholesky : (cholesky A).IsLowerTriangular := fun _ _ hij =>
  cholesky_apply_of_gt A (OrderDual.toDual_lt_toDual.1 hij)

variable {A}

/-- **Correctness of the Cholesky recurrence** ([quarteroni2000numerical] (3.45), and the second
half of its Theorem 3.6): the recurrence computes `Hᴴ` for any Cholesky factor `H` of `A`. The
recurrence equations are the entrywise identities `Matrix.IsCholesky.star_apply_mul_diag_eq` and
`Matrix.IsCholesky.re_diag_eq_sqrt` satisfied by every Cholesky factor, so the computed entries
agree with `Hᴴ` by strong induction along the order of `min i j`, the diagonal entry at each level
before the entries below it. -/
theorem cholesky_eq_of_isCholesky {H : Matrix n n 𝕜} (h : IsCholesky A H) : cholesky A = Hᴴ := by
  suffices ∀ m i j, min i j = m → cholesky A i j = Hᴴ i j from
    Matrix.ext fun i j => this _ i j rfl
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  -- the diagonal entry at level `m`
  have hdiag : ∀ i, i = m → cholesky A i i = Hᴴ i i := by
    rintro i rfl
    rw [cholesky_apply_self, conjTranspose_apply, h.star_diag, ← h.coe_re_diag, h.re_diag_eq_sqrt]
    congr 3
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := (mem_filter.1 hk).2
    rw [ih k hk' i k (min_eq_right hk'.le), conjTranspose_apply, norm_star]
  intro i j hm
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [cholesky_apply_of_gt A hij, conjTranspose_apply, h.isUpperTriangular hij, star_zero]
  · exact hdiag i (by rw [min_self] at hm; exact hm)
  · have hjm : j = m := (min_eq_right hij.le).symm.trans hm
    rw [cholesky_apply_of_lt A hij, hdiag j hjm, conjTranspose_apply, h.star_diag,
      div_eq_iff (h.diag_ne_zero j), conjTranspose_apply, h.star_apply_mul_diag_eq hij]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := (mem_filter.1 hk).2
    have hkm : k < m := hjm ▸ hk'
    rw [ih k hkm i k (min_eq_right (hk'.trans hij).le), ih k hkm j k (min_eq_right hk'.le),
      conjTranspose_apply, conjTranspose_apply, star_star]

/-- **The Cholesky recurrence computes the Cholesky factor** ([quarteroni2000numerical] (3.45)):
for a positive definite `A`, `(cholesky A)ᴴ` is the Cholesky factor of `A`. -/
theorem isCholesky_cholesky (hA : A.PosDef) : IsCholesky A (cholesky A)ᴴ := by
  obtain ⟨H, h⟩ := exists_isCholesky hA
  rw [cholesky_eq_of_isCholesky h, conjTranspose_conjTranspose]
  exact h

/-- Every implementation of the Cholesky factorization computes `Matrix.cholesky`: the recurrence
of Program 7, the `L D Lᴴ` route and the QR route of Property 3.3 of [quarteroni2000numerical]
all produce the unique factor. -/
theorem cholesky_conjTranspose_eq_of_isCholesky {H : Matrix n n 𝕜} (h : IsCholesky A H) :
    (cholesky A)ᴴ = H := by
  rw [cholesky_eq_of_isCholesky h, conjTranspose_conjTranspose]

end Recurrence

/-! ### The QR route -/

section QR

variable {m : Type*} [Fintype m]

/-- [quarteroni2000numerical] Property 3.3, last clause: if `X = Q R` with `Qᴴ Q = 1` and `R`
upper triangular with positive diagonal (a reduced QR factorization, `Matrix.exists_qr`), then `R`
is the Cholesky factor of `Xᴴ X`, since `Xᴴ X = Rᴴ Qᴴ Q R = Rᴴ R`. -/
theorem isCholesky_conjTranspose_mul_self_of_qr {X Q : Matrix m n 𝕜} {R : Matrix n n 𝕜}
    (hX : X = Q * R) (hQ : Qᴴ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) :
    IsCholesky (Xᴴ * X) R where
  isUpperTriangular := hR
  diag_pos := hd
  conjTranspose_mul_self := by
    rw [hX, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, hQ, Matrix.one_mul]

/-- The triangular factor of a reduced QR factorization of `X` is the factor computed by the
Cholesky recurrence on `Xᴴ X` ([quarteroni2000numerical] Property 3.3, §3.4.3). -/
theorem cholesky_conjTranspose_mul_self_of_qr {X Q : Matrix m n 𝕜} {R : Matrix n n 𝕜}
    (hX : X = Q * R) (hQ : Qᴴ * Q = 1) (hR : R.IsUpperTriangular) (hd : ∀ i, 0 < R i i) :
    cholesky (Xᴴ * X) = Rᴴ :=
  cholesky_eq_of_isCholesky (isCholesky_conjTranspose_mul_self_of_qr hX hQ hR hd)

end QR

/-! ### Mathlib's `LDL` factorization -/

section LDL

open InnerProductSpace

variable [LocallyFiniteOrderBot n] {S : Matrix n n 𝕜} (hS : S.PosDef)
include hS

/-- The Gram–Schmidt matrix `LDL.lowerInv` has unit diagonal: the `i`-th vector is `e_i` minus a
combination of the earlier ones, which vanish at the coordinate `i`. -/
theorem LDL.lowerInv_apply_self (i : n) : LDL.lowerInv hS i i = 1 := by
  have h := congrFun (@gramSchmidt_def'' 𝕜 (n → 𝕜) _ (Sᵀ.toNormedAddCommGroup hS.transpose)
    (Sᵀ.toInnerProductSpace hS.transpose.posSemidef) n _ _ _ (Pi.basisFun 𝕜 n) i) i
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_zero (fun k hk => ?_), add_zero,
    Pi.basisFun_apply, Pi.single_eq_same] at h
  · exact h.symm
  · rw [Pi.smul_apply]
    exact smul_eq_zero_of_right _
      (LDL.isLowerTriangular_lowerInv hS (OrderDual.toDual_lt_toDual.2 (Finset.mem_Iio.1 hk)))

/-- The Gram–Schmidt matrix `LDL.lowerInv` is unit lower triangular. -/
theorem LDL.lowerInv_isUnitLowerTriangular : (LDL.lowerInv hS).IsUnitLowerTriangular :=
  ⟨LDL.isLowerTriangular_lowerInv hS, LDL.lowerInv_apply_self hS⟩

/-- The `L` of Mathlib's `LDL` factorization is unit lower triangular (the TODO of
`Mathlib/Analysis/Matrix/LDL.lean`): it is the inverse of the unit lower triangular
`LDL.lowerInv`. -/
theorem LDL.lower_isUnitLowerTriangular : (LDL.lower hS).IsUnitLowerTriangular :=
  (LDL.lowerInv_isUnitLowerTriangular hS).inv

/-- The diagonal entries of Mathlib's `LDL` factorization are positive: each is the quadratic form
of `S` at a row of the invertible matrix `LDL.lowerInv`. -/
theorem LDL.diagEntries_pos (i : n) : 0 < LDL.diagEntries hS i := by
  have hx : star (LDL.lowerInv hS i) ≠ 0 := fun h0 => by
    have := congrFun h0 i
    rw [Pi.star_apply, LDL.lowerInv_apply_self, star_one, Pi.zero_apply] at this
    exact one_ne_zero this
  have := hS.dotProduct_mulVec_pos hx
  rw [LDL.diagEntries, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  exact this

/-- Mathlib's `LDL` factorization is an `L D Mᵀ` factorization in the Hermitian form `M = Lᴴᵀ`,
`L D Lᴴ = S`. -/
theorem isLDM_ldl : IsLDM S (LDL.lower hS) (LDL.diag hS) (LDL.lower hS)ᴴᵀ where
  isUnitLowerTriangular_left := LDL.lower_isUnitLowerTriangular hS
  isDiag := isDiag_diagonal _
  isUnitLowerTriangular_right := (LDL.lower_isUnitLowerTriangular hS).conjTranspose_transpose
  mul_eq := by rw [transpose_transpose, LDL.lower_conj_diag]

/-- Mathlib's `LDL` factors are the unique `L D Lᴴ` factors of a positive definite matrix. -/
theorem LDL.lower_eq_of_isLDM {L D : Matrix n n 𝕜} (h : IsLDM S L D Lᴴᵀ) :
    LDL.lower hS = L ∧ LDL.diag hS = D := by
  obtain ⟨LDM₀, -, huniq⟩ := existsUnique_isLDM hS.isUnit_strictLeadingPrincipalSubmatrix
  have := (huniq (LDL.lower hS, LDL.diag hS, (LDL.lower hS)ᴴᵀ) (isLDM_ldl hS)).trans
    (huniq (L, D, Lᴴᵀ) h).symm
  simp only [Prod.mk.injEq] at this
  exact ⟨this.1, this.2.1⟩

end LDL

end Matrix
