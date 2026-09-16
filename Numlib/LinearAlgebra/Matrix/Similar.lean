/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Similar`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Numlib.LinearAlgebra.Matrix.Rank

/-!
# Similar matrices

Two square matrices `A` and `B` are **similar** when `B = C⁻¹ * A * C` for some invertible `C`:
`Matrix.IsSimilar A B`. Similarity is an equivalence relation, and the invariants of a matrix under
it — the characteristic polynomial, hence the spectrum with algebraic multiplicities; the nullity,
hence the geometric multiplicities and the indices of the eigenvalues — are what the canonical
forms (diagonal, Jordan, Schur) are canonical for. Mathlib carries the invariance of the
characteristic polynomial as `Matrix.charpoly_units_conj` but has no name for the relation.

## Main definitions

* `Matrix.IsSimilar A B`: `∃ C, IsUnit C ∧ B = C⁻¹ * A * C`, over a commutative ring.
* `Matrix.IsUnitarilySimilar A B`: `∃ U ∈ unitaryGroup n R, B = star U * A * U`, over a
  commutative star ring; it implies similarity (`Matrix.IsUnitarilySimilar.isSimilar`).

## Main results

* `Matrix.IsSimilar.refl`, `Matrix.IsSimilar.symm`, `Matrix.IsSimilar.trans`: similarity is an
  equivalence relation.
* `Matrix.IsSimilar.charpoly_eq`: similar matrices have the same characteristic polynomial.
* `Matrix.IsSimilar.mulVec_eq_smul`: the eigenvectors of `A` are transported to those of
  `C⁻¹ * A * C` by `C⁻¹`.
* `Matrix.IsSimilar.pow`, `Matrix.IsSimilar.sub_smul_one`: similarity survives powers and shifts,
  with the same `C`.
* `Matrix.IsSimilar.finrank_ker_mulVecLin_eq`: over a field, similar matrices have null spaces of
  the same dimension; with the two preceding results, every eigenvalue then has the same geometric
  multiplicity and the same index for `A` and for `B`.
* `Matrix.isSimilar_diagonal_iff_exists_basis_eigenvectors`,
  `Matrix.isSimilar_diagonal_iff_iSup_eigenspace_eq_top`: a matrix over a field is similar to a
  diagonal matrix exactly when it has a basis of eigenvectors, that is, when its eigenspaces span.
* `Matrix.isSimilar_diagonal_iff_forall_finrank_eigenspace_eq_rootMultiplicity`: over an
  algebraically closed field, exactly when no eigenvalue is defective — every geometric
  multiplicity equals the algebraic one.

## Implementation notes

The witness is on the right, `B = C⁻¹ * A * C`, the convention of Quarteroni–Sacco–Saleri; Saad's
`A = X B X⁻¹` is the same relation with the same witness `X = C`. The definition and the
algebraic lemmas are stated over a commutative ring, where `Matrix.inv` is the adjugate inverse
and `IsUnit C` is the nonsingularity hypothesis; the statements about dimensions of null spaces
and about eigenspaces are over a field.

## References

* Saad, *Iterative Methods for Sparse Linear Systems*, §1.8.
* Quarteroni–Sacco–Saleri, *Numerical Mathematics*, Definition 1.14.

## TODO

The invariance of the spectrum, determinant, trace and rank as separate statements
(`Matrix.rank_conj` of `Numlib/LinearAlgebra/Matrix/Rank` is the rank), and the nonvanishing
`C⁻¹ *ᵥ x ≠ 0` of the transported eigenvector.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R]

/-- Two square matrices are *similar* when `B = C⁻¹ * A * C` for some nonsingular `C`; the phrase
"there is a nonsingular matrix `C` such that …" is the `IsUnit C` here. -/
def IsSimilar (A B : Matrix n n R) : Prop := ∃ C : Matrix n n R, IsUnit C ∧ B = C⁻¹ * A * C

/-- Similarity is reflexive. -/
@[refl]
theorem IsSimilar.refl (A : Matrix n n R) : IsSimilar A A :=
  ⟨1, isUnit_one, by simp⟩

/-- Similarity is symmetric. -/
@[symm]
theorem IsSimilar.symm {A B : Matrix n n R} (h : IsSimilar A B) : IsSimilar B A := by
  obtain ⟨C, hC, rfl⟩ := h
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  refine ⟨C⁻¹, Matrix.isUnit_nonsing_inv_iff.2 hC, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv C hd]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv C hd, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv C hd, Matrix.one_mul]

/-- Similarity is transitive. -/
@[trans]
theorem IsSimilar.trans {A B C : Matrix n n R} (hAB : IsSimilar A B) (hBC : IsSimilar B C) :
    IsSimilar A C := by
  obtain ⟨X, hX, rfl⟩ := hAB
  obtain ⟨Y, hY, rfl⟩ := hBC
  refine ⟨X * Y, hX.mul hY, ?_⟩
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

/-- Similar matrices have the same eigenvalues, with the eigenvectors transported by `C⁻¹`: if
`B = C⁻¹ * A * C` and `A x = μ x`, then `B (C⁻¹ x) = μ (C⁻¹ x)`. This is the content one draws
from the definition. -/
theorem IsSimilar.mulVec_eq_smul {A B C : Matrix n n R} (hC : IsUnit C) (hAB : B = C⁻¹ * A * C)
    {μ : R} {x : n → R} (hx : A *ᵥ x = μ • x) :
    B *ᵥ (C⁻¹ *ᵥ x) = μ • (C⁻¹ *ᵥ x) := by
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  have h1 : B * C⁻¹ = C⁻¹ * A := by
    rw [hAB, Matrix.mul_assoc, Matrix.mul_nonsing_inv C hd, Matrix.mul_one]
  calc B *ᵥ (C⁻¹ *ᵥ x) = (B * C⁻¹) *ᵥ x := by rw [Matrix.mulVec_mulVec]
    _ = (C⁻¹ * A) *ᵥ x := by rw [h1]
    _ = C⁻¹ *ᵥ (A *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    _ = C⁻¹ *ᵥ (μ • x) := by rw [hx]
    _ = μ • (C⁻¹ *ᵥ x) := by rw [Matrix.mulVec_smul]

/-- Similar matrices have the same characteristic polynomial, so the eigenvalues of `A` and `B`
agree with their algebraic multiplicities. -/
theorem IsSimilar.charpoly_eq {A B : Matrix n n R} (h : IsSimilar A B) :
    A.charpoly = B.charpoly := by
  obtain ⟨C, hC, rfl⟩ := h
  have h1 := Matrix.charpoly_units_conj' hC.unit A
  rwa [IsUnit.unit_spec, eq_comm] at h1

/-- Similarity survives subtracting a scalar from both matrices: `C⁻¹ (A - c I) C = B - c I`. -/
theorem IsSimilar.sub_smul_one {A B : Matrix n n R} (h : IsSimilar A B) (c : R) :
    IsSimilar (A - c • 1) (B - c • 1) := by
  obtain ⟨C, hC, rfl⟩ := h
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  refine ⟨C, hC, ?_⟩
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.nonsing_inv_mul C hd]

/-- Similar matrices have similar powers, with the same transforming matrix. -/
theorem IsSimilar.pow {A B : Matrix n n R} (h : IsSimilar A B) (k : ℕ) :
    IsSimilar (A ^ k) (B ^ k) := by
  obtain ⟨C, hC, rfl⟩ := h
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  refine ⟨C, hC, ?_⟩
  induction k with
  | zero => simp [Matrix.nonsing_inv_mul C hd]
  | succ k ih =>
      rw [pow_succ, pow_succ, ih]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc C C⁻¹, Matrix.mul_nonsing_inv C hd, Matrix.one_mul]

end CommRing

section Field

variable {K : Type*} [Field K]

/-- Similar matrices have null spaces of the same dimension, because they have the same rank. With
`Matrix.IsSimilar.sub_smul_one` and `Matrix.IsSimilar.pow` this says that similar matrices give
every eigenvalue the same geometric multiplicity and the same index, as
`Matrix.IsSimilar.charpoly_eq` says they give it the same algebraic multiplicity. -/
theorem IsSimilar.finrank_ker_mulVecLin_eq {A B : Matrix n n K} (h : IsSimilar A B) :
    Module.finrank K (LinearMap.ker A.mulVecLin)
      = Module.finrank K (LinearMap.ker B.mulVecLin) := by
  obtain ⟨C, hC, rfl⟩ := h
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  rw [← Matrix.finrank_ker_mulVecLin_conj (Matrix.isUnit_nonsing_inv_iff.2 hC) (A := A),
    Matrix.nonsing_inv_nonsing_inv C hd]

/-- A matrix is *diagonalizable* — similar to a diagonal matrix — exactly when it has a basis of
eigenvectors, a linearly independent family of eigenvectors indexed by `n`. Both directions read
the relation `A C = C D` column by column: the columns of the transforming matrix `C` are the
eigenvectors, and `C` is nonsingular exactly when they are independent. -/
theorem isSimilar_diagonal_iff_exists_basis_eigenvectors (A : Matrix n n K) :
    (∃ d : n → K, IsSimilar A (Matrix.diagonal d)) ↔
      ∃ (d : n → K) (v : n → n → K), LinearIndependent K v ∧ ∀ j, A *ᵥ v j = d j • v j := by
  constructor
  · rintro ⟨d, C, hC, hA⟩
    have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
    have hAC : A * C = C * Matrix.diagonal d := by
      rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv C hd,
        Matrix.one_mul]
    refine ⟨d, C.col, Matrix.linearIndependent_cols_iff_isUnit.2 hC, fun j => ?_⟩
    funext i
    have h := congrFun (congrFun hAC i) j
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    change ∑ k, A i k * C k j = d j * C i j
    rw [h]
    exact mul_comm _ _
  · rintro ⟨d, v, hv, hvA⟩
    have hC : IsUnit ((Matrix.of v)ᵀ) := Matrix.linearIndependent_cols_iff_isUnit.1 hv
    have hd : IsUnit ((Matrix.of v)ᵀ).det := (Matrix.isUnit_iff_isUnit_det _).1 hC
    have hAC : A * (Matrix.of v)ᵀ = (Matrix.of v)ᵀ * Matrix.diagonal d := by
      ext i j
      have h := congrFun (hvA j) i
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      rw [show ((Matrix.of v)ᵀ) i j = v j i from rfl, mul_comm]
      exact h
    exact ⟨d, (Matrix.of v)ᵀ, hC, by
      rw [Matrix.mul_assoc, hAC, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd,
        Matrix.one_mul]⟩

/-- Diagonalizability is exactly the statement that the eigenspaces span:
`Matrix.isSimilar_diagonal_iff_exists_basis_eigenvectors` transported to the operator
`A.mulVecLin`. -/
theorem isSimilar_diagonal_iff_iSup_eigenspace_eq_top (A : Matrix n n K) :
    (∃ d : n → K, IsSimilar A (Matrix.diagonal d)) ↔
      (⨆ μ : K, Module.End.eigenspace A.mulVecLin μ) = ⊤ := by
  rw [isSimilar_diagonal_iff_exists_basis_eigenvectors]
  constructor
  · rintro ⟨d, v, hv, hvA⟩
    have hcard : Fintype.card n = Module.finrank K (n → K) :=
      (Module.finrank_fintype_fun_eq_card K).symm
    have hspan : Submodule.span K (Set.range v) = ⊤ :=
      hv.span_eq_top_of_card_eq_finrank' hcard
    refine top_le_iff.1 ?_
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (d j) (Module.End.mem_eigenspace_iff.2 (hvA j))
  · intro hsup
    obtain ⟨b, hbsub, hbspan, hbind⟩ :=
      exists_linearIndependent K (⋃ μ : K, (Module.End.eigenspace A.mulVecLin μ : Set (n → K)))
    have hbtop : Submodule.span K b = ⊤ := by
      rw [hbspan, ← Submodule.iSup_eq_span]
      exact hsup
    have hbas : Module.Basis b K (n → K) :=
      Module.Basis.mk hbind (by rw [Subtype.range_coe, hbtop])
    have hfin : Fintype b := FiniteDimensional.fintypeBasisIndex hbas
    have hcard : Fintype.card b = Fintype.card n := by
      rw [← Module.finrank_eq_card_basis hbas, Module.finrank_fintype_fun_eq_card]
    have hchoice : ∀ x : b, ∃ μ : K, (x : n → K) ∈ Module.End.eigenspace A.mulVecLin μ := by
      intro x
      simpa using hbsub x.2
    choose dd hdd using hchoice
    obtain ⟨e⟩ : Nonempty (b ≃ n) := ⟨Fintype.equivOfCardEq hcard⟩
    refine ⟨fun j => dd (e.symm j), fun j => (e.symm j : n → K),
      hbind.comp _ e.symm.injective, fun j => ?_⟩
    exact Module.End.mem_eigenspace_iff.1 (hdd (e.symm j))

/-- The spectrum of an endomorphism with a basis of eigenvectors `b i`, `f (b i) = lam i • b i`, is
the set of the `lam i`: in the basis `b` the endomorphism is the diagonal matrix of the `lam i`,
whose spectrum is `Set.range lam`. This is the operator form of
`Matrix.isSimilar_diagonal_iff_exists_basis_eigenvectors`. -/
theorem _root_.Module.End.spectrum_eq_range_of_basis {E : Type*} [AddCommGroup E] [Module K E]
    {ι : Type*} [Finite ι] {f : Module.End K E} (b : Module.Basis ι K E) {lam : ι → K}
    (hb : ∀ i, f (b i) = lam i • b i) : spectrum K f = Set.range lam := by
  cases nonempty_fintype ι
  classical
  have hmat : LinearMap.toMatrixAlgEquiv b f = diagonal lam := by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply, hb, map_smul, Finsupp.smul_apply, b.repr_self,
      Finsupp.single_apply, diagonal_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv b), hmat, spectrum_diagonal]

end Field

/-! ### Unitary similarity -/

section Unitary

variable {R : Type*} [CommRing R] [StarRing R]

/-- Two square matrices are *unitarily similar* when `B = Uᴴ A U` for some unitary `U`
([quarteroni2000numerical] Definition 1.14, second sentence). This is the relation the Schur,
spectral and normal theorems produce. -/
def IsUnitarilySimilar (A B : Matrix n n R) : Prop := ∃ U ∈ unitaryGroup n R, B = star U * A * U

/-- Unitarily similar matrices are similar: `U⁻¹ = Uᴴ` for a unitary `U`. -/
theorem IsUnitarilySimilar.isSimilar {A B : Matrix n n R} (h : IsUnitarilySimilar A B) :
    IsSimilar A B := by
  obtain ⟨U, hU, rfl⟩ := h
  refine ⟨U, ⟨⟨U, star U, mem_unitaryGroup_iff.1 hU, mem_unitaryGroup_iff'.1 hU⟩, rfl⟩, ?_⟩
  rw [inv_eq_left_inv (mem_unitaryGroup_iff'.1 hU)]

/-- Unitary similarity is reflexive. -/
@[refl]
theorem IsUnitarilySimilar.refl (A : Matrix n n R) : IsUnitarilySimilar A A :=
  ⟨1, one_mem _, by simp⟩

/-- Unitary similarity is symmetric. -/
@[symm]
theorem IsUnitarilySimilar.symm {A B : Matrix n n R} (h : IsUnitarilySimilar A B) :
    IsUnitarilySimilar B A := by
  obtain ⟨U, hU, rfl⟩ := h
  refine ⟨star U, Unitary.star_mem hU, ?_⟩
  rw [star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU,
    Matrix.one_mul, Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU, Matrix.mul_one]

/-- Unitary similarity is transitive. -/
@[trans]
theorem IsUnitarilySimilar.trans {A B C : Matrix n n R} (hAB : IsUnitarilySimilar A B)
    (hBC : IsUnitarilySimilar B C) : IsUnitarilySimilar A C := by
  obtain ⟨U, hU, rfl⟩ := hAB
  obtain ⟨V, hV, rfl⟩ := hBC
  refine ⟨U * V, mul_mem hU hV, ?_⟩
  rw [star_mul]
  simp only [Matrix.mul_assoc]

end Unitary

/-! ### Diagonalizability and defective eigenvalues -/

section Defective

variable {K : Type*} [Field K]

/-- **A matrix is diagonalizable if and only if it is nondefective** ([quarteroni2000numerical]
§1.8, after Property 1.6): over an algebraically closed field, `A` is similar to a diagonal
matrix exactly when every eigenvalue has geometric multiplicity equal to its algebraic
multiplicity. The generalized eigenspaces of `A` are independent and span (Mathlib's
`Module.End.iSup_maxGenEigenspace_eq_top`), each has the algebraic multiplicity as dimension
(`LinearMap.finrank_maxGenEigenspace_eq`), and diagonalizability is the spanning of the
eigenspaces themselves (`Matrix.isSimilar_diagonal_iff_iSup_eigenspace_eq_top`); the two
spannings agree exactly when each eigenspace fills its generalized eigenspace, which is the
equality of the two multiplicities. -/
theorem isSimilar_diagonal_iff_forall_finrank_eigenspace_eq_rootMultiplicity [IsAlgClosed K]
    (A : Matrix n n K) :
    (∃ d : n → K, IsSimilar A (diagonal d)) ↔
      ∀ μ : K, Module.finrank K (Module.End.eigenspace A.mulVecLin μ)
        = A.charpoly.rootMultiplicity μ := by
  rw [isSimilar_diagonal_iff_iSup_eigenspace_eq_top]
  have hfin : ∀ μ, Module.finrank K (Module.End.maxGenEigenspace A.mulVecLin μ)
      = A.charpoly.rootMultiplicity μ := fun μ => by
    rw [LinearMap.finrank_maxGenEigenspace_eq, charpoly_mulVecLin]
  have hle : ∀ μ, Module.End.eigenspace A.mulVecLin μ
      ≤ Module.End.maxGenEigenspace A.mulVecLin μ :=
    fun μ => Module.End.eigenspace_le_maxGenEigenspace
  constructor
  · intro htop μ
    rw [← hfin]
    have heq : Module.End.eigenspace A.mulVecLin μ
        = Module.End.maxGenEigenspace A.mulVecLin μ := by
      refine le_antisymm (hle μ) fun x hx => ?_
      -- `x` splits into an eigenvector for `μ` and a part in the other generalized eigenspaces
      have hx' : x ∈ Module.End.eigenspace A.mulVecLin μ
          ⊔ ⨆ (ν) (_ : ν ≠ μ), Module.End.maxGenEigenspace A.mulVecLin ν := by
        have hsup : (⊤ : Submodule K (n → K)) ≤ Module.End.eigenspace A.mulVecLin μ
            ⊔ ⨆ (ν) (_ : ν ≠ μ), Module.End.maxGenEigenspace A.mulVecLin ν := by
          rw [← htop]
          refine iSup_le fun ν => ?_
          by_cases hν : ν = μ
          · subst hν
            exact le_sup_left
          · exact le_sup_of_le_right (le_iSup₂_of_le ν hν (hle ν))
        exact hsup Submodule.mem_top
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      have hzμ : z ∈ Module.End.maxGenEigenspace A.mulVecLin μ := by
        simpa using Submodule.sub_mem _ hx (hle μ hy)
      have hz0 : z = 0 :=
        Submodule.disjoint_def.1
          (iSupIndep_def.1 (Module.End.independent_maxGenEigenspace A.mulVecLin) μ) z hzμ hz
      rw [hz0, add_zero]
      exact hy
    rw [heq]
  · intro h
    have heq : ∀ μ, Module.End.eigenspace A.mulVecLin μ
        = Module.End.maxGenEigenspace A.mulVecLin μ :=
      fun μ => Submodule.eq_of_le_of_finrank_eq (hle μ) (by rw [h, hfin])
    simp_rw [heq]
    exact Module.End.iSup_maxGenEigenspace_eq_top A.mulVecLin

end Defective

end Matrix
