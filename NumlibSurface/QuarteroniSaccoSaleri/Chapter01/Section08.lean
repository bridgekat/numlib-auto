import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Similar
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section07

/-!
# Quarteroni–Sacco–Saleri §1.8: similarity transformations

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §1.8. Similarity (Definition 1.14) is the backbone's
`Matrix.IsSimilar A B` (`B = C⁻¹ A C` for a nonsingular `C`) and unitary similarity
`Matrix.IsUnitarilySimilar A B` (`B = Uᴴ A U` for a unitary `U`), from
`Numlib/LinearAlgebra/Matrix/Similar`. The Schur decomposition (Property 1.5) is
`Matrix.exists_unitary_conj_upperTriangular` of `Numlib/LinearAlgebra/Matrix/Schur`, its
consequences for Hermitian and normal matrices come from Mathlib's
`Matrix.IsHermitian.spectral_theorem` and the backbone's `Matrix.IsStarNormal.spectral_theorem`
(`Numlib/Eigen/Normal`), and the Jordan canonical form (Property 1.6) with its principal-vector
recursion (1.8) from `Numlib/LinearAlgebra/Matrix/Jordan`.

## Contents

* `definition_1_14`, `charpoly_eq_of_isSimilar`, `spectrum_mul_comm` — similarity, its invariants,
  `σ(AB) ∖ {0} = σ(BA) ∖ {0}`.
* `property_1_5`, `property_1_5_hermitian`, `property_1_5_diagonalizable_iff`,
  `property_1_5_normal`, `property_1_5_commute` — the Schur decomposition and its three
  consequences.
* `property_1_6`, `property_1_6_diagonalizable_iff_nondefective`, `equation_1_8`,
  `example_1_6` — the Jordan canonical form, "diagonalizable iff nondefective", the principal
  vectors, and the worked `6 × 6` example.

## Conventions

The Jordan form `diag(J_{k₁}(λ₁), …, J_{k_l}(λ_l))` is the backbone's `Matrix.jordanForm e μ`, a
block diagonal matrix indexed by the sigma type `(i : Fin l) × Fin (e i)`; a matrix of order `n`
in that form is `reindex σ σ (jordanForm e μ)` for an equivalence `σ` of the sigma type with
`Fin n`, and the book's column `x_j` of `X` is `Xᵀ (σ ⟨i, j⟩)`. Property 1.6 groups the blocks by
eigenvalue, as the backbone statement does; Example 1.6 lists them consecutively, along
`finSigmaFinEquiv`.
-/

open Finset Matrix Polynomial
open scoped ENNReal NNReal

namespace QuarteroniSaccoSaleri.Chapter01

variable {n : ℕ}

/-! ### Definition 1.14 and the invariants of similarity -/

/-- **Definition 1.14.** For a nonsingular `C` of the same order as `A`, the matrices `A` and
`C⁻¹ A C` are *similar*, and `A ↦ C⁻¹ A C` is a *similarity transformation*; they are *unitarily
similar* when `C` is unitary (`Matrix.IsSimilar`, `Matrix.IsUnitarilySimilar`). Unitary
similarity implies similarity, and both relations are equivalence relations. -/
theorem definition_1_14 (A B : Matrix (Fin n) (Fin n) ℂ) :
    (IsSimilar A B ↔ ∃ C : Matrix (Fin n) (Fin n) ℂ, IsUnit C ∧ B = C⁻¹ * A * C) ∧
      (IsUnitarilySimilar A B ↔ ∃ U ∈ unitaryGroup (Fin n) ℂ, B = star U * A * U) ∧
      (IsUnitarilySimilar A B → IsSimilar A B) ∧
      (IsSimilar A A ∧ (IsSimilar A B → IsSimilar B A) ∧
        ∀ C, IsSimilar A B → IsSimilar B C → IsSimilar A C) :=
  ⟨Iff.rfl, Iff.rfl, IsUnitarilySimilar.isSimilar,
    IsSimilar.refl A, IsSimilar.symm, fun _ h₁ h₂ => h₁.trans h₂⟩

/-- **§1.8, similar matrices share the spectrum.** Two similar matrices have the same
characteristic polynomial and the same spectrum (backbone `Matrix.IsSimilar.charpoly_eq`), and
if `(λ, x)` is an eigenpair of `A` then `(λ, C⁻¹ x)` is one of `C⁻¹ A C`, since
`(C⁻¹ A C) C⁻¹ x = C⁻¹ A x = λ C⁻¹ x` (`Matrix.IsSimilar.mulVec_eq_smul`). -/
theorem charpoly_eq_of_isSimilar {A B : Matrix (Fin n) (Fin n) ℂ} (h : IsSimilar A B) :
    A.charpoly = B.charpoly ∧ spectrum ℂ A = spectrum ℂ B ∧
      ∀ (C : Matrix (Fin n) (Fin n) ℂ), IsUnit C → B = C⁻¹ * A * C →
        ∀ (μ : ℂ) (x : Fin n → ℂ), A *ᵥ x = μ • x → B *ᵥ (C⁻¹ *ᵥ x) = μ • (C⁻¹ *ᵥ x) := by
  refine ⟨h.charpoly_eq, Set.ext fun μ => ?_,
    fun C hC hB μ x hx => IsSimilar.mulVec_eq_smul hC hB hx⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
    h.charpoly_eq]

-- TODO(backbone): belongs beside `spectralRadius_smul` in
-- `Numlib/Analysis/Normed/Algebra/SpectralRadius`.
/-- The spectral radius does not see the eigenvalue `0`: `ρ(a)` is the supremum of `‖λ‖₊` over
`σ(a) ∖ {0}`, since `‖0‖₊ = 0` contributes nothing to a supremum in `ℝ≥0∞`. -/
theorem spectralRadius_eq_iSup_diff_singleton_zero {𝕜 B : Type*} [NormedField 𝕜] [Ring B]
    [Algebra 𝕜 B] (a : B) :
    spectralRadius 𝕜 a = ⨆ μ ∈ spectrum 𝕜 a \ {0}, (‖μ‖₊ : ℝ≥0∞) := by
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun μ hμ =>
    le_iSup₂ (f := fun μ (_ : μ ∈ spectrum 𝕜 a) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞)) μ hμ.1)
  rcases eq_or_ne μ 0 with rfl | h0
  · simp
  · exact le_iSup₂ (f := fun μ (_ : μ ∈ spectrum 𝕜 a \ {0}) => ((‖μ‖₊ : ℝ≥0) : ℝ≥0∞)) μ ⟨hμ, h0⟩

/-- **§1.8, the spectra of `AB` and `BA`.** For `A ∈ ℂ^{n×m}` and `B ∈ ℂ^{m×n}` the products `AB`
and `BA` are not similar, but `σ(AB) ∖ {0} = σ(BA) ∖ {0}`: they share the spectrum apart from
null eigenvalues, since `λᵐ p_{AB}(λ) = λⁿ p_{BA}(λ)` (Mathlib's `Matrix.charpoly_mul_comm'`);
consequently `ρ(AB) = ρ(BA)`. -/
theorem spectrum_mul_comm {m : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ) :
    spectrum ℂ (A * B) \ {0} = spectrum ℂ (B * A) \ {0} ∧
      spectralRadius ℂ (A * B) = spectralRadius ℂ (B * A) := by
  have hset : spectrum ℂ (A * B) \ {0} = spectrum ℂ (B * A) \ {0} := by
    ext μ
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Matrix.mem_spectrum_iff_isRoot_charpoly]
    constructor
    · rintro ⟨h, hμ⟩
      refine ⟨?_, hμ⟩
      have := congrArg (eval μ) (charpoly_mul_comm' A B)
      rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_X, h.eq_zero, mul_zero, eq_comm,
        mul_eq_zero] at this
      exact IsRoot.def.2 (this.resolve_left (pow_ne_zero _ hμ))
    · rintro ⟨h, hμ⟩
      refine ⟨?_, hμ⟩
      have := congrArg (eval μ) (charpoly_mul_comm' A B)
      rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_X, h.eq_zero, mul_zero, mul_eq_zero] at this
      exact IsRoot.def.2 (this.resolve_left (pow_ne_zero _ hμ))
  exact ⟨hset, by rw [spectralRadius_eq_iSup_diff_singleton_zero,
    spectralRadius_eq_iSup_diff_singleton_zero, hset]⟩

/-! ### Property 1.5: the Schur decomposition -/

/-- **Property 1.5 (Schur decomposition).** Given `A ∈ ℂ^{n×n}` there is a unitary `U` with
`U⁻¹ A U = Uᴴ A U = T` upper triangular, whose diagonal entries `λᵢ` are the eigenvalues of `A`:
`p_A = ∏ᵢ (λ - tᵢᵢ)` and `σ(A) = {tᵢᵢ}`. Every matrix is thus unitarily similar to an upper
triangular matrix (backbone `Matrix.exists_unitary_conj_upperTriangular`). -/
theorem property_1_5 (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U ∈ unitaryGroup (Fin n) ℂ, U⁻¹ = star U ∧ (star U * A * U).IsUpperTriangular ∧
      IsUnitarilySimilar A (star U * A * U) ∧
      A.charpoly = ∏ i, (X - C ((star U * A * U) i i)) ∧
      spectrum ℂ A = Set.range fun i => (star U * A * U) i i := by
  obtain ⟨U, hU, hT, hp⟩ := exists_unitary_conj_upperTriangular A
  refine ⟨U, hU, inv_eq_left_inv (mem_unitaryGroup_iff'.1 hU), hT, ⟨U, hU, rfl⟩, hp, ?_⟩
  rw [(charpoly_eq_of_isSimilar (IsUnitarilySimilar.isSimilar ⟨U, hU, rfl⟩)).2.1,
    (spectrum_of_isTriangular (star U * A * U) 0).1 hT]

/-- A Hermitian upper triangular matrix is diagonal: the entries below the diagonal vanish and
those above are their conjugates. -/
theorem IsHermitian.isDiag_of_isUpperTriangular {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.IsHermitian) (hU : T.IsUpperTriangular) : T.IsDiag := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · rw [← hT.apply i j, hU h, star_zero]
  · exact hU h

/-- **§1.8, consequence 1 of the Schur decomposition.** Every Hermitian matrix is unitarily
similar to a *real* diagonal matrix, `Uᴴ A U = Λ = diag(λ₁, …, λₙ)` — so every Schur
decomposition of a Hermitian matrix is diagonal — with `U = hA.eigenvectorUnitary` and
`λ = hA.eigenvalues` (Mathlib's `Matrix.IsHermitian.spectral_theorem`); then `A U = U Λ`, that
is, `A uᵢ = λᵢ uᵢ` for the columns `uᵢ` of `U`, which are the eigenvectors of `A`; they are
orthonormal (`hA.eigenvectorBasis`) and generate the whole space `ℂⁿ`. -/
theorem property_1_5_hermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * A * hA.eigenvectorUnitary =
        diagonal (fun i => (hA.eigenvalues i : ℂ)) ∧
      (∀ U ∈ unitaryGroup (Fin n) ℂ, (star U * A * U).IsUpperTriangular →
        (star U * A * U).IsDiag) ∧
      A * hA.eigenvectorUnitary =
        hA.eigenvectorUnitary * diagonal (fun i => (hA.eigenvalues i : ℂ)) ∧
      (∀ i, A *ᵥ (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᵀ i =
        (hA.eigenvalues i : ℂ) • (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᵀ i) ∧
      (∀ i, (hA.eigenvectorBasis i : Fin n → ℂ) =
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᵀ i) ∧
      Orthonormal ℂ hA.eigenvectorBasis ∧
      Submodule.span ℂ (Set.range hA.eigenvectorBasis) = ⊤ := by
  have hdiag : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * A * hA.eigenvectorUnitary
      = diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rwa [Unitary.conjStarAlgAut_star_apply] at h
  have hU := hA.eigenvectorUnitary.2
  refine ⟨hdiag, fun U hU hT => IsHermitian.isDiag_of_isUpperTriangular
    (isHermitian_conjTranspose_mul_mul U hA) hT, ?_, fun i => ?_,
    fun i => (hA.eigenvectorUnitary_transpose_apply i).symm,
    hA.eigenvectorBasis.orthonormal, ?_⟩
  · rw [← hdiag, ← Matrix.mul_assoc, ← Matrix.mul_assoc, (mem_unitaryGroup_iff.1 hU),
      Matrix.one_mul]
  · rw [hA.eigenvectorUnitary_transpose_apply, hA.mulVec_eigenvectorBasis,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  · rw [← OrthonormalBasis.coe_toBasis, hA.eigenvectorBasis.toBasis.span_eq]

/-- **§1.8, consequence 1, last sentence.** A matrix `A` of order `n` is similar to a diagonal
matrix `D` iff the eigenvectors of `A` form a basis for `ℂⁿ` (backbone
`Matrix.isSimilar_diagonal_iff_exists_basis_eigenvectors`). -/
theorem property_1_5_diagonalizable_iff (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ d : Fin n → ℂ, IsSimilar A (diagonal d)) ↔
      ∃ (d : Fin n → ℂ) (v : Fin n → Fin n → ℂ), LinearIndependent ℂ v ∧
        ∀ j, A *ᵥ v j = d j • v j :=
  isSimilar_diagonal_iff_exists_basis_eigenvectors A

/-- **§1.8, consequence 2 of the Schur decomposition.** A matrix `A ∈ ℂ^{n×n}` is normal iff it
is unitarily similar to a diagonal matrix (backbone `Matrix.IsStarNormal.spectral_theorem`); as a
consequence a normal matrix admits the *spectral decomposition* `A = U Λ Uᴴ = ∑ᵢ λᵢ uᵢ uᵢᴴ` with
`U` unitary and `Λ` diagonal (`Matrix.IsStarNormal.eq_sum_smul_vecMulVec`). -/
theorem property_1_5_normal (A : Matrix (Fin n) (Fin n) ℂ) :
    (IsStarNormal A ↔ ∃ d : Fin n → ℂ, IsUnitarilySimilar A (diagonal d)) ∧
      (IsStarNormal A → ∃ U ∈ unitaryGroup (Fin n) ℂ, ∃ d : Fin n → ℂ,
        star U * A * U = diagonal d ∧ A = U * diagonal d * star U ∧
          A = ∑ i, d i • vecMulVec (Uᵀ i) (star (Uᵀ i))) := by
  refine ⟨?_, fun hA => ?_⟩
  · rw [IsStarNormal.spectral_theorem]
    exact ⟨fun ⟨U, hU, d, hd⟩ => ⟨d, U, hU, hd.symm⟩, fun ⟨d, U, hU, hd⟩ => ⟨U, hU, d, hd.symm⟩⟩
  · obtain ⟨U, hU, d, hd, hsum⟩ := hA.eq_sum_smul_vecMulVec
    refine ⟨U, hU, d, hd, ?_, hsum⟩
    rw [← hd, Matrix.mul_assoc, Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU, Matrix.mul_one,
      ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU, Matrix.one_mul]

/-- **§1.8, consequence 3 of the Schur decomposition.** Let `A` and `B` be normal and commuting;
then there is a unitary `U` diagonalizing both, `Uᴴ A U = diag(λ)`, `Uᴴ B U = diag(ξ)`, so that
`Uᴴ (A + B) U = diag(λ + ξ)`: the generic eigenvalue `μᵢ` of `A + B` is the sum `λᵢ + ξᵢ` of the
eigenvalues of `A` and `B` associated with the same eigenvector `uᵢ` (backbone
`Matrix.IsStarNormal.exists_unitary_conj_diagonal_of_commute`). -/
theorem property_1_5_commute {A B : Matrix (Fin n) (Fin n) ℂ} (hA : IsStarNormal A)
    (hB : IsStarNormal B) (hAB : A * B = B * A) :
    ∃ U ∈ unitaryGroup (Fin n) ℂ, ∃ d e : Fin n → ℂ,
      star U * A * U = diagonal d ∧ star U * B * U = diagonal e ∧
        star U * (A + B) * U = diagonal (d + e) ∧
        ∀ i, (A + B) *ᵥ Uᵀ i = (d i + e i) • Uᵀ i := by
  obtain ⟨U, hU, d, e, hd, he⟩ := hA.exists_unitary_conj_diagonal_of_commute hB hAB
  have hsum : star U * (A + B) * U = diagonal (d + e) := by
    rw [Matrix.mul_add, Matrix.add_mul, hd, he, diagonal_add]
    rfl
  refine ⟨U, hU, d, e, hd, he, hsum, fun i => ?_⟩
  have hcol : (A + B) * U = U * diagonal (d + e) := by
    rw [← hsum, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU,
      Matrix.one_mul]
  have hl : ((A + B) * U)ᵀ i = (A + B) *ᵥ Uᵀ i := by
    ext r; simp [Matrix.mul_apply, mulVec, dotProduct]
  have hr : (U * diagonal (d + e))ᵀ i = (d i + e i) • Uᵀ i := by
    ext r; simp [mul_diagonal, mul_comm]
  rw [← hl, hcol, hr]

/-! ### Property 1.6: the Jordan canonical form -/

/-- **Property 1.6 (canonical Jordan form).** Every square matrix `A` is transformed by a
nonsingular `X` into a block diagonal matrix `X⁻¹ A X = J = diag(J_{k₁}(λ₁), …, J_{k_l}(λ_l))`,
the `λⱼ` being the eigenvalues of `A` and `J_k(λ) ∈ ℂ^{k×k}` the *Jordan block* with `λ` on the
diagonal and `1` on the superdiagonal (`J_1(λ) = λ`). Backbone
`Matrix.exists_conj_blockDiagonal'_jordanForm`: the blocks are grouped by eigenvalue — one outer
block per distinct eigenvalue `ν i`, itself a `Matrix.jordanForm` all of whose blocks carry
`ν i` — every block has positive size, and the range of `ν` is exactly the spectrum of `A`. -/
theorem property_1_6 (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ (q : ℕ) (ν : Fin q → ℂ) (d : Fin q → ℕ) (e : ∀ i : Fin q, Fin (d i) → ℕ)
      (σ : ((i : Fin q) × (j : Fin (d i)) × Fin (e i j)) ≃ Fin n),
      Function.Injective ν ∧ (∀ μ, μ ∈ spectrum ℂ A ↔ μ ∈ Set.range ν) ∧ (∀ i j, 0 < e i j) ∧
        IsSimilar A (reindex σ σ (blockDiagonal' fun i => jordanForm (e i) fun _ => ν i))) ∧
      ∀ (k : ℕ) (μ : ℂ) (i j : Fin k),
        jordanBlock k μ i j = if i = j then μ else if (i : ℕ) + 1 = j then 1 else 0 := by
  obtain ⟨q, ν, d, e, σ, P, hinj, heig, hpos, hP, hPA⟩ := exists_conj_blockDiagonal'_jordanForm A
  exact ⟨⟨q, ν, d, e, σ, hinj, fun μ => (mem_spectrum_iff_exists_mulVec_eq_smul A μ).trans (heig μ),
    hpos, P, hP, hPA.symm⟩, fun k μ i j => jordanBlock_apply i j⟩

/-- **§1.8, after Property 1.6.** A matrix can be diagonalized by a similarity transformation iff
it is nondefective — for this reason nondefective matrices are called *diagonalizable* — and in
particular normal matrices are diagonalizable. Backbone
`Matrix.isSimilar_diagonal_iff_forall_finrank_eigenspace_eq_rootMultiplicity`: since the
geometric multiplicity never exceeds the algebraic one (`finrank_eigenspace_le_rootMultiplicity`),
"no eigenvalue is defective" is the equality of the two multiplicities at every eigenvalue. -/
theorem property_1_6_diagonalizable_iff_nondefective (A : Matrix (Fin n) (Fin n) ℂ) :
    ((∃ d : Fin n → ℂ, IsSimilar A (diagonal d)) ↔ ¬ IsDefective A) ∧
      (IsStarNormal A → ∃ d : Fin n → ℂ, IsSimilar A (diagonal d)) := by
  refine ⟨?_, fun hA => ?_⟩
  · rw [isSimilar_diagonal_iff_forall_finrank_eigenspace_eq_rootMultiplicity, IsDefective]
    push Not
    constructor
    · exact fun h μ _ => (h μ).ge
    · intro h μ
      by_cases hμ : μ ∈ spectrum ℂ A
      · exact le_antisymm (finrank_eigenspace_le_rootMultiplicity A μ) (h μ hμ)
      · rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ
        rw [rootMultiplicity_eq_zero hμ]
        exact Nat.eq_zero_of_le_zero
          ((finrank_eigenspace_le_rootMultiplicity A μ).trans (rootMultiplicity_eq_zero hμ).le)
  · obtain ⟨d, hd⟩ := (property_1_5_normal A).1.1 hA
    exact ⟨d, hd.isSimilar⟩

/-- The column `c` of a matrix reindexed by `σ.symm` is the column `σ c` of the original,
composed with `σ`. -/
private theorem transpose_reindex_symm_apply {ι : Type*} (X : Matrix (Fin n) (Fin n) ℂ)
    (σ : ι ≃ Fin n) (c : ι) : (reindex σ.symm σ.symm X)ᵀ c = Xᵀ (σ c) ∘ σ := rfl

/-- A matrix reindexed by `σ.symm` acts on a reindexed vector as the original matrix does. -/
private theorem reindex_symm_mulVec {ι : Type*} [Fintype ι] (M : Matrix (Fin n) (Fin n) ℂ)
    (σ : ι ≃ Fin n) (v : Fin n → ℂ) :
    reindex σ.symm σ.symm M *ᵥ (v ∘ σ) = (M *ᵥ v) ∘ σ := by
  rw [reindex_apply, Equiv.symm_symm, submatrix_mulVec_equiv]
  congr 2
  ext r
  simp

/-- **(1.8), the principal vectors.** Partition `X` by columns, `X = (x₁, …, xₙ)`, where
`X⁻¹ A X = J` is a Jordan form — `reindex σ σ (jordanForm e μ)` for an equivalence `σ` of the
block indices `(i, j)` with `Fin n`, so that the column of `X` at position `j` of the `i`-th
block is `Xᵀ (σ ⟨i, j⟩)`. Then the `kᵢ` columns associated with the block `J_{kᵢ}(λᵢ)` satisfy
`A x_l = λᵢ x_l` for the first of them and `A x_j = λᵢ x_j + x_{j-1}` for the following
`kᵢ - 1`: these are the *principal vectors* or *generalized eigenvectors* of `A` (backbone
`Matrix.mulVec_eq_of_conj_jordanForm`, transported along `σ`). -/
theorem equation_1_8 {ι : Type*} [Finite ι] [DecidableEq ι] {e : ι → ℕ} {μ : ι → ℂ}
    {A X : Matrix (Fin n) (Fin n) ℂ} (σ : ((i : ι) × Fin (e i)) ≃ Fin n) (hX : IsUnit X)
    (h : X⁻¹ * A * X = reindex σ σ (jordanForm e μ)) :
    (∀ (i : ι) (h0 : 0 < e i),
        A *ᵥ Xᵀ (σ ⟨i, ⟨0, h0⟩⟩) = μ i • Xᵀ (σ ⟨i, ⟨0, h0⟩⟩)) ∧
      ∀ (i : ι) (j : ℕ) (hj : j + 1 < e i),
        A *ᵥ Xᵀ (σ ⟨i, ⟨j + 1, hj⟩⟩) =
          μ i • Xᵀ (σ ⟨i, ⟨j + 1, hj⟩⟩) + Xᵀ (σ ⟨i, ⟨j, by omega⟩⟩) := by
  cases nonempty_fintype ι
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      reindex σ.symm σ.symm M = reindexAlgEquiv ℂ ℂ σ.symm M := fun _ => rfl
  have hX' : IsUnit (reindex σ.symm σ.symm X) := by rw [key]; exact hX.map _
  have h' : (reindex σ.symm σ.symm X)⁻¹ * reindex σ.symm σ.symm A * reindex σ.symm σ.symm X
      = jordanForm e μ := by
    rw [inv_reindex, key, key, key, ← map_mul, ← map_mul, ← key, h, ← reindex_symm,
      Equiv.symm_apply_apply]
  obtain ⟨h0, hsucc⟩ := mulVec_eq_of_conj_jordanForm hX' h'
  refine ⟨fun i hi => funext fun r => ?_, fun i j hj => funext fun r => ?_⟩
  · have := congrFun (h0 i hi) (σ.symm r)
    simp only [transpose_reindex_symm_apply, reindex_symm_mulVec] at this
    simpa using this
  · have := congrFun (hsucc i j hj) (σ.symm r)
    simp only [transpose_reindex_symm_apply, reindex_symm_mulVec] at this
    simpa using this

/-! ### Example 1.6 -/

/-- The matrix `A` of Example 1.6. -/
def example_1_6_A : Matrix (Fin 6) (Fin 6) ℚ :=
  !![7/4, 3/4, -1/4, -1/4, -1/4, 1/4;
     0, 2, 0, 0, 0, 0;
     -1/2, -1/2, 5/2, 1/2, -1/2, 1/2;
     -1/2, -1/2, -1/2, 5/2, 1/2, 1/2;
     -1/4, -1/4, -1/4, -1/4, 11/4, 1/4;
     -3/2, -1/2, -1/2, 1/2, 1/2, 7/2]

/-- The Jordan canonical form `J = diag(J₂(2), J₃(3), J₁(2))` of Example 1.6. -/
def example_1_6_J : Matrix (Fin 6) (Fin 6) ℚ :=
  !![2, 1, 0, 0, 0, 0; 0, 2, 0, 0, 0, 0; 0, 0, 3, 1, 0, 0; 0, 0, 0, 3, 1, 0;
     0, 0, 0, 0, 3, 0; 0, 0, 0, 0, 0, 2]

/-- The transforming matrix `X` of Example 1.6. -/
def example_1_6_X : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1; 1, 1, 1, 1, 1, 1]

/-- The inverse `X⁻¹ = ¼ [[4 I - E, e], [eᵀ, -1]]` of the matrix `X` of Example 1.6 (`E` the
`5 × 5` matrix of ones, `e` the vector of ones), from the Schur complement `1 - eᵀ e = -4`. -/
def example_1_6_Xinv : Matrix (Fin 6) (Fin 6) ℚ :=
  !![3/4, -1/4, -1/4, -1/4, -1/4, 1/4;
     -1/4, 3/4, -1/4, -1/4, -1/4, 1/4;
     -1/4, -1/4, 3/4, -1/4, -1/4, 1/4;
     -1/4, -1/4, -1/4, 3/4, -1/4, 1/4;
     -1/4, -1/4, -1/4, -1/4, 3/4, 1/4;
     1/4, 1/4, 1/4, 1/4, 1/4, -1/4]

/-- The layout of the three Jordan blocks of Example 1.6, of sizes `2, 3, 1`, consecutively along
the diagonal of a `6 × 6` matrix. -/
def example_1_6_equiv : ((i : Fin 3) × Fin (![2, 3, 1] i)) ≃ Fin 6 :=
  finSigmaFinEquiv.trans (finCongr (by decide))

/-- **Example 1.6.** For the `6 × 6` matrix `A` of the example, `A X = X J` with `X`
nonsingular (`X⁻¹` is `example_1_6_Xinv`), so `X⁻¹ A X = J`, and `J` is the Jordan form
`diag(J₂(2), J₃(3), J₁(2))` — `jordanForm ![2, 3, 1] ![2, 3, 2]` laid out consecutively — in
which two different Jordan blocks belong to the same eigenvalue `2`. The displayed checks of
(1.8) for the block of `λ₂ = 3`, in `0`-based columns: `A x₂ = (0, 0, 3, 0, 0, 3)ᵀ = 3 x₂`,
`A x₃ = (0, 0, 1, 3, 0, 4)ᵀ = 3 x₃ + x₂` and `A x₄ = (0, 0, 0, 1, 3, 4)ᵀ = 3 x₄ + x₃`. All the
identities are rational computations, checked by the kernel. -/
theorem example_1_6 :
    example_1_6_A * example_1_6_X = example_1_6_X * example_1_6_J ∧
      example_1_6_X * example_1_6_Xinv = 1 ∧ IsUnit example_1_6_X ∧
      example_1_6_X⁻¹ = example_1_6_Xinv ∧
      example_1_6_X⁻¹ * example_1_6_A * example_1_6_X = example_1_6_J ∧
      example_1_6_J =
        reindex example_1_6_equiv example_1_6_equiv (jordanForm ![2, 3, 1] ![2, 3, 2]) ∧
      (example_1_6_A *ᵥ example_1_6_Xᵀ 2 = ![0, 0, 3, 0, 0, 3] ∧
        example_1_6_A *ᵥ example_1_6_Xᵀ 2 = (3 : ℚ) • example_1_6_Xᵀ 2) ∧
      (example_1_6_A *ᵥ example_1_6_Xᵀ 3 = ![0, 0, 1, 3, 0, 4] ∧
        example_1_6_A *ᵥ example_1_6_Xᵀ 3 = (3 : ℚ) • example_1_6_Xᵀ 3 + example_1_6_Xᵀ 2) ∧
      (example_1_6_A *ᵥ example_1_6_Xᵀ 4 = ![0, 0, 0, 1, 3, 4] ∧
        example_1_6_A *ᵥ example_1_6_Xᵀ 4 = (3 : ℚ) • example_1_6_Xᵀ 4 + example_1_6_Xᵀ 3) := by
  have hAX : example_1_6_A * example_1_6_X = example_1_6_X * example_1_6_J := by decide +kernel
  have hXY : example_1_6_X * example_1_6_Xinv = 1 := by decide +kernel
  have hX : IsUnit example_1_6_X :=
    (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse hXY)
  refine ⟨hAX, hXY, hX, inv_eq_right_inv hXY, ?_, by decide +kernel,
    ⟨by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel⟩,
    ⟨by decide +kernel, by decide +kernel⟩⟩
  rw [Matrix.mul_assoc, hAX, ← Matrix.mul_assoc,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hX), Matrix.one_mul]

end QuarteroniSaccoSaleri.Chapter01
