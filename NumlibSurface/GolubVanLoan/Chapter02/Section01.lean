import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Numlib.Eigen.MinMax
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.Rank
import Numlib.LinearAlgebra.Matrix.SVD
import Numlib.LinearAlgebra.Matrix.Similar

/-!
# Golub–Van Loan §2.1: basic ideas from linear algebra

Surface file for Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th edition
[golub2013matrix], §2.1, a review of linear algebra: range, null space and rank (§2.1.2), the
inverse identities (2.1.1)–(2.1.3), the Sherman–Morrison–Woodbury formula (2.1.4) and its rank-one
case (2.1.5), orthogonality (§2.1.5, Theorem 2.1.1), the determinant (§2.1.6), eigenvalues,
similarity and diagonalizability (§2.1.7), the symmetric Schur decomposition (2.1.6) and the
Rayleigh characterizations (2.1.7)–(2.1.8) of the extreme eigenvalues.

## Conventions

Matrices are `Matrix (Fin m) (Fin n) ℝ`, 0-based; §2.1.7 is over `ℂ` as in the book.
`ran(A)` and `null(A)` are `LinearMap.range` and `LinearMap.ker` of `Matrix.toEuclideanLin A`, so
that orthogonal complements are those of `EuclideanSpace ℝ (Fin n)`. The eigenvalues
`λ₁(A) ≥ ⋯ ≥ λₙ(A)` of a symmetric `A` (over `ℝ`, `A.IsHermitian` is `Aᵀ = A`) are the backbone's
`Matrix.IsHermitian.sortedEigenvalues`, 0-based: `λ_{k+1}(A) = hA.sortedEigenvalues k`. The book's
`A⁻¹` of a nonsingular `A` is Mathlib's `A⁻¹`, whose junk value `0` at a singular `A` makes (2.1.1)
and (2.1.2) unconditional.

## Sources

The proofs delegate to Mathlib (rank–nullity, `Matrix.mul_inv_rev`, the determinant, the
characteristic polynomial, the spectral theorem) and to the backbone modules
`Numlib/LinearAlgebra/Matrix/{Rank,NonsingularInverse,Similar}` and `Numlib/Eigen/MinMax`.
§2.1.1 (independence, span, basis, dimension) is Mathlib's vocabulary and §2.1.8 fixes a notation
only; neither has a declaration here.
-/

open Matrix

namespace GolubVanLoan.Chapter02

variable {m n : ℕ}

/-! ### §2.1.2 Range, null space and rank -/

/-- The rank of `A` is the dimension of `ran(A) = LinearMap.range (toEuclideanLin A)`. -/
private theorem rank_eq_finrank_range_toEuclideanLin (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank = Module.finrank ℝ (LinearMap.range (toEuclideanLin A)) := by
  rw [rank_eq_finrank_range_toLin _ (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  rfl

/-- **§2.1.2, rank–nullity and the column space.** For `A ∈ ℝ^{m×n}`,
`dim(null(A)) + rank(A) = n`; `ran(A) = span{a₁, …, aₙ}` for the columns `aⱼ`; and the rank is the
maximal number of independent columns, or of rows. -/
theorem finrank_ker_add_rank (A : Matrix (Fin m) (Fin n) ℝ) :
    Module.finrank ℝ (LinearMap.ker (toEuclideanLin A)) + A.rank = n ∧
      LinearMap.range A.mulVecLin = Submodule.span ℝ (Set.range A.col) ∧
      A.rank = Module.finrank ℝ (Submodule.span ℝ (Set.range A.col)) ∧
      A.rank = Module.finrank ℝ (Submodule.span ℝ (Set.range A.row)) := by
  refine ⟨?_, Matrix.range_mulVecLin A, A.rank_eq_finrank_span_cols, A.rank_eq_finrank_span_row⟩
  rw [rank_eq_finrank_range_toEuclideanLin, add_comm,
    LinearMap.finrank_range_add_finrank_ker, finrank_euclideanSpace_fin]

/-- **§2.1.2, rank deficiency.** `A ∈ ℝ^{m×n}` is *rank deficient* if
`rank(A) < min{m, n}`. -/
def IsRankDeficient (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  A.rank < min m n

/-! ### §2.1.3–2.1.4 The inverse and the Sherman–Morrison–Woodbury formula -/

/-- **(2.1.1)**: the inverse of a product is the reverse product of the inverses,
`(AB)⁻¹ = B⁻¹ A⁻¹`. -/
theorem equation_2_1_1 (A B : Matrix (Fin n) (Fin n) ℝ) : (A * B)⁻¹ = B⁻¹ * A⁻¹ :=
  Matrix.mul_inv_rev A B

/-- **(2.1.2)**: the transpose of the inverse is the inverse of the transpose,
`(A⁻¹)ᵀ = (Aᵀ)⁻¹ ≡ A⁻ᵀ`. -/
theorem equation_2_1_2 (A : Matrix (Fin n) (Fin n) ℝ) : (A⁻¹)ᵀ = (Aᵀ)⁻¹ :=
  Matrix.transpose_nonsing_inv A

/-- **(2.1.3)**: for nonsingular `A` and `B`, `B⁻¹ = A⁻¹ - B⁻¹ (B - A) A⁻¹`, which "shows how the
inverse changes if the matrix changes". -/
theorem equation_2_1_3 {A B : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) (hB : IsUnit B) :
    B⁻¹ = A⁻¹ - B⁻¹ * (B - A) * A⁻¹ := by
  have hA' := (isUnit_iff_isUnit_det A).1 hA
  have hB' := (isUnit_iff_isUnit_det B).1 hB
  rw [Matrix.mul_sub, Matrix.sub_mul, nonsing_inv_mul B hB', Matrix.one_mul, Matrix.mul_assoc,
    mul_nonsing_inv A hA', Matrix.mul_one, sub_sub_cancel]

/-- **(2.1.4), the Sherman–Morrison–Woodbury formula.** For `A ∈ ℝ^{n×n}` and `U, V ∈ ℝ^{n×k}`,
if `A` and `I + Vᵀ A⁻¹ U` are nonsingular then so is `A + U Vᵀ`, and
`(A + U Vᵀ)⁻¹ = A⁻¹ - A⁻¹ U (I + Vᵀ A⁻¹ U)⁻¹ Vᵀ A⁻¹`: a rank-`k` correction of a matrix is a
rank-`k` correction of its inverse. -/
theorem equation_2_1_4 {k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A)
    (U V : Matrix (Fin n) (Fin k) ℝ) (hW : IsUnit (1 + Vᵀ * A⁻¹ * U)) :
    IsUnit (A + U * Vᵀ) ∧
      (A + U * Vᵀ)⁻¹ = A⁻¹ - A⁻¹ * U * (1 + Vᵀ * A⁻¹ * U)⁻¹ * Vᵀ * A⁻¹ := by
  have hA' := (isUnit_iff_isUnit_det A).1 hA
  refine ⟨?_, ?_⟩
  · rw [isUnit_iff_isUnit_det, det_add_mul U Vᵀ hA']
    exact hA'.mul ((isUnit_iff_isUnit_det _).1 hW)
  · have h := add_mul_mul_mul_inv_eq_sub_of_isUnit_one_add hA U 1 Vᵀ (by rwa [Matrix.one_mul])
    simpa only [Matrix.mul_one, Matrix.one_mul] using h

/-- **(2.1.5), the Sherman–Morrison formula**, the case `k = 1` of (2.1.4): if `A` is nonsingular
and `α = 1 + vᵀ A⁻¹ u ≠ 0`, then `A + u vᵀ` is nonsingular and
`(A + u vᵀ)⁻¹ = A⁻¹ - (1/α) A⁻¹ u vᵀ A⁻¹`. -/
theorem equation_2_1_5 {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) {u v : Fin n → ℝ}
    (hα : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    IsUnit (A + vecMulVec u v) ∧
      (A + vecMulVec u v)⁻¹
        = A⁻¹ - (1 / (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))) • (A⁻¹ * vecMulVec u v * A⁻¹) := by
  refine ⟨isUnit_add_vecMulVec hA hα, ?_⟩
  rw [inv_add_vecMulVec hA hα, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

/-! ### §2.1.5 Orthogonality -/

/-- **§2.1.5**: `ran(A)⊥ = null(Aᵀ)`. -/
theorem orthogonal_range_eq_ker_transpose (A : Matrix (Fin m) (Fin n) ℝ) :
    (LinearMap.range (toEuclideanLin A))ᗮ = LinearMap.ker (toEuclideanLin Aᵀ) := by
  rw [LinearMap.orthogonal_range, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_eq_transpose_of_trivial]

/-- **§2.1.5, complementary column blocks.** If `V ∈ ℝ^{n×n}` is orthogonal and the column
selections `f : Fin r → Fin n`, `g : Fin s → Fin n` are injective, disjoint and together exhaust
the `n` columns (`r + s = n`), then `ran(V(:, f))⊥ = ran(V(:, g))`: the note after Theorem 2.1.1,
and the block form used in §2.5. `ran(V(:, g)) ⊆ null(V(:, f)ᵀ)` since `V(:, f)ᵀ V(:, g) = 0`, and
both sides have dimension `s`. -/
theorem orthogonal_range_submatrix_eq {r s : ℕ} {V : Matrix (Fin n) (Fin n) ℝ}
    (hV : V ∈ orthogonalGroup (Fin n) ℝ) {f : Fin r → Fin n} {g : Fin s → Fin n}
    (hf : Function.Injective f) (hg : Function.Injective g) (hfg : ∀ a b, f a ≠ g b)
    (hrs : r + s = n) :
    (LinearMap.range (toEuclideanLin (V.submatrix id f)))ᗮ =
      LinearMap.range (toEuclideanLin (V.submatrix id g)) := by
  have hVV : Vᵀ * V = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hV
  have hrank : ∀ {k : ℕ} (e : Fin k → Fin n), Function.Injective e →
      Module.finrank ℝ (LinearMap.range (toEuclideanLin (V.submatrix id e))) = k := by
    intro k e he
    have h1 : (V.submatrix id e)ᵀ * V.submatrix id e = 1 := by
      rw [transpose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id, hVV]
      exact submatrix_one e he
    rw [← rank_eq_finrank_range_toEuclideanLin, ← rank_transpose_mul_self, h1, rank_one,
      Fintype.card_fin]
  have hzero : (V.submatrix id f)ᵀ * V.submatrix id g = 0 := by
    rw [transpose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id, hVV]
    ext a b
    simp [one_apply, hfg a b]
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [orthogonal_range_eq_ker_transpose, LinearMap.range_le_ker_iff, ← toEuclideanLin_mul,
      hzero, map_zero]
  · have h := (LinearMap.range (toEuclideanLin (V.submatrix id f))).finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin, hrank f hf] at h
    rw [hrank g hg]
    omega

/-- **Theorem 2.1.1.** If `V₁ ∈ ℝ^{n×r}` has orthonormal columns (`V₁ᵀ V₁ = I`), then there is
`V₂ ∈ ℝ^{n×(n-r)}` such that `V = [V₁ | V₂]` is orthogonal, and `ran(V₁)⊥ = ran(V₂)`. Here
`r ≤ n` follows from the hypothesis, and `[V₁ | V₂]` is `Matrix.fromCols V₁ V₂` read on
`Fin n = Fin (r + (n - r))`. The backbone's orthonormal completion
`Matrix.exists_mem_unitaryGroup_submatrix_eq` (orthonormal-basis extension, where the book
defers to QR). -/
theorem theorem_2_1_1 {r : ℕ} (V₁ : Matrix (Fin n) (Fin r) ℝ) (hV₁ : V₁ᵀ * V₁ = 1) :
    ∃ (hr : r ≤ n) (V₂ : Matrix (Fin n) (Fin (n - r)) ℝ),
      (fromCols V₁ V₂).submatrix id (finSumFinEquiv.symm ∘ Fin.cast (Nat.add_sub_of_le hr).symm)
          ∈ orthogonalGroup (Fin n) ℝ ∧
        (LinearMap.range (toEuclideanLin V₁))ᗮ = LinearMap.range (toEuclideanLin V₂) := by
  have hr : r ≤ n := by
    have h1 : V₁.rank = r := by
      rw [← rank_transpose_mul_self, hV₁, rank_one, Fintype.card_fin]
    have h2 := V₁.rank_le_card_height
    rwa [h1, Fintype.card_fin] at h2
  have hV₁' : V₁ᴴ * V₁ = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  obtain ⟨U, hU, hUV⟩ := exists_mem_unitaryGroup_submatrix_eq V₁ hV₁' (Fin.castLEEmb hr)
  have hUV' : U.submatrix id (Fin.castLE hr) = V₁ := hUV
  set g : Fin (n - r) → Fin n := Fin.cast (Nat.add_sub_of_le hr) ∘ Fin.natAdd r with hg
  have hg_inj : Function.Injective g := fun a b h => by
    have := congrArg Fin.val h
    simp only [hg, Function.comp_apply, Fin.val_cast, Fin.val_natAdd] at this
    exact Fin.ext (by omega)
  refine ⟨hr, U.submatrix id g, ?_, ?_⟩
  · convert hU using 1
    ext i k
    obtain ⟨k', rfl⟩ : ∃ k', Fin.cast (Nat.add_sub_of_le hr) k' = k :=
      ⟨Fin.cast (Nat.add_sub_of_le hr).symm k, by simp⟩
    induction k' using Fin.addCases with
    | left a =>
      simp only [submatrix_apply, id, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
        finSumFinEquiv_symm_apply_castAdd, fromCols_apply_inl, ← hUV']
      congr 1
    | right b =>
      simp only [submatrix_apply, id, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
        finSumFinEquiv_symm_apply_natAdd, fromCols_apply_inr, hg]
  · rw [← hUV']
    refine orthogonal_range_submatrix_eq hU (Fin.castLE_injective hr) hg_inj (fun a b h => ?_)
      (Nat.add_sub_of_le hr)
    have := congrArg Fin.val h
    simp only [hg, Function.comp_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_castLE] at this
    omega

/-! ### §2.1.6 The determinant -/

/-- **§2.1.6, the determinant.** The cofactor expansion along the first row
`det(A) = ∑ⱼ (-1)^{j+1} a_{1j} det(A_{1j})` (0-based: `(-1)^j`, with `A_{1j}` the submatrix without
the first row and the `j`-th column), and the properties `det(AB) = det(A) det(B)`,
`det(Aᵀ) = det(A)`, `det(cA) = cⁿ det(A)`, and `det(A) ≠ 0` iff `A` is nonsingular. -/
theorem determinant_properties (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (A B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    C.det = ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * C 0 j * (C.submatrix Fin.succ j.succAbove).det ∧
      (A * B).det = A.det * B.det ∧ Aᵀ.det = A.det ∧ (c • A).det = c ^ n * A.det ∧
      (A.det ≠ 0 ↔ IsUnit A) := by
  refine ⟨det_succ_row_zero C, det_mul A B, det_transpose A, ?_, ?_⟩
  · rw [det_smul, Fintype.card_fin]
  · rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-! ### §2.1.7 Eigenvalues and eigenvectors -/

/-- **§2.1.7, eigenvalues.** For `A ∈ ℂ^{n×n}` the eigenvalues are the zeros of the characteristic
polynomial, `λ(A) = {x : det(A - xI) = 0}`; `λ ∈ λ(A)` iff `A x = λ x` for some `x ≠ 0`; and "every
`n`-by-`n` matrix has `n` eigenvalues": the characteristic polynomial has `n` roots, counted with
multiplicity. -/
theorem mem_spectrum_iff_det_sub_eq_zero (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ) :
    (x ∈ spectrum ℂ A ↔ (A - x • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0) ∧
      (x ∈ spectrum ℂ A ↔ ∃ v ≠ 0, A *ᵥ v = x • v) ∧
      A.charpoly.roots.card = n := by
  have hdet : x ∈ spectrum ℂ A ↔ (A - x • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, ← neg_sub, IsUnit.neg_iff,
      isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet, ← exists_mulVec_eq_zero_iff]
    refine exists_congr fun v => and_congr_right fun _ => ?_
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]
  · rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- **§2.1.7, similarity.** If `X` is nonsingular and `B = X⁻¹ A X`, then `A` and `B` are similar
and have exactly the same eigenvalues (indeed the same characteristic polynomial). -/
theorem isSimilar_spectrum_eq (A X : Matrix (Fin n) (Fin n) ℂ) (hX : IsUnit X) :
    (X⁻¹ * A * X).charpoly = A.charpoly ∧ spectrum ℂ (X⁻¹ * A * X) = spectrum ℂ A := by
  have h : (X⁻¹ * A * X).charpoly = A.charpoly := (IsSimilar.charpoly_eq ⟨X, hX, rfl⟩).symm
  refine ⟨h, Set.ext fun x => ?_⟩
  rw [mem_spectrum_iff_isRoot_charpoly, mem_spectrum_iff_isRoot_charpoly, h]

/-- **§2.1.7, diagonalizability.** If `A ∈ ℂ^{n×n}` has `n` independent eigenvectors
`A xᵢ = λᵢ xᵢ`, then `X = [x₁ | ⋯ | xₙ]` is nonsingular and `X⁻¹ A X = diag(λ₁, …, λₙ)`. -/
theorem diagonalizable_of_linearIndependent_eigenvectors (A : Matrix (Fin n) (Fin n) ℂ)
    (x : Fin n → Fin n → ℂ) (μ : Fin n → ℂ) (hx : LinearIndependent ℂ x)
    (hAx : ∀ i, A *ᵥ x i = μ i • x i) :
    IsUnit (Matrix.of x)ᵀ ∧ ((Matrix.of x)ᵀ)⁻¹ * A * (Matrix.of x)ᵀ = diagonal μ := by
  have hX : IsUnit (Matrix.of x)ᵀ := Matrix.linearIndependent_cols_iff_isUnit.1 hx
  have hd : IsUnit ((Matrix.of x)ᵀ).det := (isUnit_iff_isUnit_det _).1 hX
  have hAX : A * (Matrix.of x)ᵀ = (Matrix.of x)ᵀ * diagonal μ := by
    ext i j
    have h := congrFun (hAx j) i
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [show ((Matrix.of x)ᵀ) i j = x j i from rfl, mul_comm]
    exact h
  refine ⟨hX, ?_⟩
  rw [Matrix.mul_assoc, hAX, ← Matrix.mul_assoc, nonsing_inv_mul _ hd, Matrix.one_mul]

/-! ### (2.1.6)–(2.1.8) Symmetric matrices -/

/-- The eigenvalues of a symmetric operator do not depend on how the dimension is spelled. -/
private theorem eigenvalues_cast {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {a b : ℕ}
    (ha : Module.finrank ℝ E = a) (hb : Module.finrank ℝ E = b) (i : Fin a) :
    hT.eigenvalues ha i = hT.eigenvalues hb (Fin.cast (ha.symm.trans hb) i) := by
  obtain rfl : a = b := ha.symm.trans hb
  rfl

/-- The sorted eigenvalues of a symmetric matrix are those of `toEuclideanLin A`, indexed by
`Fin n`. -/
private theorem sortedEigenvalues_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (k : Fin n) :
    hA.sortedEigenvalues k =
      (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin k := by
  rw [IsHermitian.sortedEigenvalues_apply, IsHermitian.eigenvalues₀, eigenvalues_cast]
  rfl

/-- **(2.1.6), the symmetric Schur decomposition.** For symmetric `A ∈ ℝ^{n×n}` there is an
orthogonal `Q` with `Qᵀ A Q = diag(λ₁, …, λₙ)`, the eigenvalues in the book's decreasing order. -/
theorem equation_2_1_6 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ Q ∈ orthogonalGroup (Fin n) ℝ, Qᵀ * A * Q = diagonal hA.sortedEigenvalues := by
  set U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  have hU : Uᵀ * A * U = diagonal hA.eigenvalues := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [U, Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using h
  have hUU : Uᵀ * U = 1 := by
    simpa [U, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  set e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _)
  set σ : Fin n ≃ Fin n := (finCongr (Fintype.card_fin n).symm).trans e
  have hσ : hA.eigenvalues ∘ σ = hA.sortedEigenvalues := by
    funext k
    simp [σ, e, IsHermitian.eigenvalues, IsHermitian.sortedEigenvalues_apply]
  have hconj : ∀ M : Matrix (Fin n) (Fin n) ℝ,
      (U.submatrix id σ)ᵀ * M * U.submatrix id σ = (Uᵀ * M * U).submatrix σ σ := fun M => by
    rw [transpose_submatrix, ← submatrix_id_id M, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id]
  refine ⟨U.submatrix id σ, (mem_orthogonalGroup_iff' (Fin n) ℝ).2 ?_, ?_⟩
  · have h := hconj 1
    rwa [Matrix.mul_one, Matrix.mul_one, hUU, submatrix_one_equiv] at h
  · rw [hconj, hU, submatrix_diagonal_equiv, hσ]

/-- The Rayleigh quotient of `toEuclideanLin A` at a vector is the book's `xᵀ A x / xᵀ x`. -/
private theorem rayleighQuotient_toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (toEuclideanLin A).rayleighQuotient (WithLp.toLp 2 x) = x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x) := by
  rw [LinearMap.rayleighQuotient, ← real_inner_self_eq_norm_sq, RCLike.re_to_real,
    EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- **(2.1.7)**: the largest eigenvalue of a symmetric `A` is the maximum of the Rayleigh quotient,
`λ_max(A) = max_{x ≠ 0} xᵀ A x / xᵀ x`. -/
theorem equation_2_1_7 {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian) :
    IsGreatest {r : ℝ | ∃ x : Fin (n + 1) → ℝ, x ≠ 0 ∧ r = x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x)}
      (hA.sortedEigenvalues 0) := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := finrank_euclideanSpace_fin
  rw [sortedEigenvalues_eq]
  refine ⟨⟨WithLp.ofLp (hT.eigenvectorBasis hn 0), ?_, ?_⟩, ?_⟩
  · simpa using hT.eigenvectorBasis_ne_zero hn 0
  · rw [← rayleighQuotient_toEuclideanLin, WithLp.toLp_ofLp, hT.rayleighQuotient_eigenvectorBasis]
  · rintro r ⟨x, hx, rfl⟩
    rw [← rayleighQuotient_toEuclideanLin]
    exact (hT.rayleighQuotient_mem_Icc hn (by simpa using hx)).2

/-- **(2.1.8)**: the smallest eigenvalue of a symmetric `A` is the minimum of the Rayleigh
quotient, `λ_min(A) = min_{x ≠ 0} xᵀ A x / xᵀ x`. -/
theorem equation_2_1_8 {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hA : A.IsHermitian) :
    IsLeast {r : ℝ | ∃ x : Fin (n + 1) → ℝ, x ≠ 0 ∧ r = x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x)}
      (hA.sortedEigenvalues (Fin.last n)) := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := finrank_euclideanSpace_fin
  rw [sortedEigenvalues_eq]
  refine ⟨⟨WithLp.ofLp (hT.eigenvectorBasis hn (Fin.last n)), ?_, ?_⟩, ?_⟩
  · simpa using hT.eigenvectorBasis_ne_zero hn (Fin.last n)
  · rw [← rayleighQuotient_toEuclideanLin, WithLp.toLp_ofLp, hT.rayleighQuotient_eigenvectorBasis]
  · rintro r ⟨x, hx, rfl⟩
    rw [← rayleighQuotient_toEuclideanLin]
    exact (hT.rayleighQuotient_mem_Icc hn (by simpa using hx)).1

end GolubVanLoan.Chapter02
