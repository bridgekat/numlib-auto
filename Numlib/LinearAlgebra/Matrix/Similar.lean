/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Similar`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Star.UnitaryStarAlgAut
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

Let $R$ be a commutative ring and $n$ a finite index set. Two matrices $A, B \in R^{n \times n}$ are
**similar** if $B = C^{-1} A C$ for some invertible $C \in R^{n \times n}$. Similarity is an
equivalence relation. Similar matrices have the same characteristic polynomial, hence the same
eigenvalues with the same algebraic multiplicities. Over a field, similar matrices also have null
spaces of the same dimension, hence every eigenvalue has the same geometric multiplicity and the
same index for both. These invariants are what the canonical forms (diagonal, Jordan, Schur) are
canonical for. The definitions follow [quarteroni2000numerical] Definition 1.14 and
[saad2003iterative] §1.8.

The module also defines unitary similarity, $B = U^H A U$ with $U$ unitary. It characterizes the
matrices that are similar to a diagonal matrix: over a field, they are the matrices with a basis of
eigenvectors, and over an algebraically closed field, they are the matrices with no defective
eigenvalue.

## Main definitions

* `Matrix.IsSimilar`: $A$ and $B$ are similar if $B = C^{-1} A C$ for an invertible $C$.
* `Matrix.IsUnitarilySimilar`: $A$ and $B$ are unitarily similar if $B = U^H A U$ for a unitary $U$.
  This implies similarity (`Matrix.IsUnitarilySimilar.isSimilar`).

## Main results

* `Matrix.IsSimilar.refl`, `Matrix.IsSimilar.symm`, `Matrix.IsSimilar.trans`: similarity is an
  equivalence relation.
* `Matrix.IsSimilar.charpoly_eq`, `Matrix.IsSimilar.spectrum_eq`: similar matrices have the same
  characteristic polynomial and the same spectrum.
* `Matrix.IsSimilar.mulVec_eq_smul`: if $B = C^{-1} A C$ and $Ax = \mu x$, then
  $B (C^{-1} x) = \mu C^{-1} x$.
* `Matrix.IsSimilar.pow`, `Matrix.IsSimilar.sub_smul_one`: if $A$ and $B$ are similar, then so are
  $A^k$ and $B^k$, and so are $A - cI$ and $B - cI$, with the same transforming matrix.
* `Matrix.isSimilar_mul_comm_of_isUnit`: $PQ$ and $QP$ are similar when $Q$ is invertible.
* `Matrix.IsSimilar.finrank_ker_mulVecLin_eq`: over a field, similar matrices have null spaces of
  the same dimension.
* `Matrix.isSimilar_diagonal_iff_exists_basis_eigenvectors`,
  `Matrix.isSimilar_diagonal_iff_iSup_eigenspace_eq_top`: a matrix over a field is similar to a
  diagonal matrix if and only if it has a basis of eigenvectors, that is, if and only if its
  eigenspaces span the whole space.
* `Matrix.isSimilar_diagonal_iff_forall_finrank_eigenspace_eq_rootMultiplicity`: over an
  algebraically closed field, a matrix is similar to a diagonal matrix if and only if every
  eigenvalue has equal geometric and algebraic multiplicities.
* `Matrix.isUnit_det_sub_smul_one_of_notMem_spectrum`: if $\mu$ is not an eigenvalue of $A$, then
  $A - \mu I$ is nonsingular.

## Implementation notes

* The witness is on the right, $B = C^{-1} A C$, as in [quarteroni2000numerical]. The relation
  $A = X B X^{-1}$ of [saad2003iterative] is the same relation with the same witness $X = C$.
* The definition and the algebraic lemmas are stated over a commutative ring, where `Matrix.inv` is
  the adjugate inverse and `IsUnit C` is the nonsingularity hypothesis. The statements about
  dimensions of null spaces and about eigenspaces are over a field.
* Mathlib has the invariance of the characteristic polynomial as `Matrix.charpoly_units_conj`, but
  no name for the relation.
* The invariance of the rank is `Matrix.rank_conj` in `Numlib.LinearAlgebra.Matrix.Rank`. The
  invariance of the determinant and of the trace, and the fact that the transported eigenvector
  $C^{-1} x$ is nonzero, are not stated here.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R]

/-- Let $R$ be a commutative ring. Two matrices $A, B \in R^{n \times n}$ are **similar** if there
is a nonsingular matrix $C \in R^{n \times n}$ with
$$B = C^{-1} A C.$$

The nonsingularity hypothesis is `IsUnit C`, and the inverse is `Matrix.inv`. -/
def IsSimilar (A B : Matrix n n R) : Prop := ∃ C : Matrix n n R, IsUnit C ∧ B = C⁻¹ * A * C

/-- Similarity is reflexive: every square matrix $A$ is similar to itself. -/
@[refl]
theorem IsSimilar.refl (A : Matrix n n R) : IsSimilar A A :=
  ⟨1, isUnit_one, by simp⟩

/-- Similarity is symmetric: if $A$ is similar to $B$, then $B$ is similar to $A$. -/
@[symm]
theorem IsSimilar.symm {A B : Matrix n n R} (h : IsSimilar A B) : IsSimilar B A := by
  obtain ⟨C, hC, rfl⟩ := h
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  refine ⟨C⁻¹, Matrix.isUnit_nonsing_inv_iff.2 hC, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv C hd]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv C hd, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv C hd, Matrix.one_mul]

/-- Similarity is transitive: if $A$ is similar to $B$ and $B$ is similar to $C$, then $A$ is
similar to $C$. -/
@[trans]
theorem IsSimilar.trans {A B C : Matrix n n R} (hAB : IsSimilar A B) (hBC : IsSimilar B C) :
    IsSimilar A C := by
  obtain ⟨X, hX, rfl⟩ := hAB
  obtain ⟨Y, hY, rfl⟩ := hBC
  refine ⟨X * Y, hX.mul hY, ?_⟩
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

/-- Let $A, B, C \in R^{n \times n}$ with $C$ invertible and $B = C^{-1} A C$. If $\mu \in R$ and
$x \in R^n$ satisfy $Ax = \mu x$, then
$$B (C^{-1} x) = \mu \, C^{-1} x.$$
So $C^{-1}$ carries the eigenvectors of $A$ to eigenvectors of $B$ for the same eigenvalues.

The theorem takes the witness $C$ and the equation $B = C^{-1} A C$ directly, not a proof of
`Matrix.IsSimilar A B`. It does not state that $C^{-1} x$ is nonzero. -/
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

/-- If $A, B \in R^{n \times n}$ are similar, then they have the same characteristic polynomial.
Hence $A$ and $B$ have the same eigenvalues with the same algebraic multiplicities. -/
theorem IsSimilar.charpoly_eq {A B : Matrix n n R} (h : IsSimilar A B) :
    A.charpoly = B.charpoly := by
  obtain ⟨C, hC, rfl⟩ := h
  have h1 := Matrix.charpoly_units_conj' hC.unit A
  rwa [IsUnit.unit_spec, eq_comm] at h1

/-- If $A, B \in R^{n \times n}$ are similar, then they have the same spectrum in $R$.

The proof is the invariance of the spectrum under conjugation by a unit,
`spectrum.units_conjugate'`. -/
theorem IsSimilar.spectrum_eq {A B : Matrix n n R} (h : IsSimilar A B) :
    spectrum R A = spectrum R B := by
  obtain ⟨C, hC, rfl⟩ := h
  have h1 := spectrum.units_conjugate' (R := R) (a := A) (u := hC.unit)
  rwa [coe_units_inv, IsUnit.unit_spec, eq_comm] at h1

/-- If $A, B \in R^{n \times n}$ are similar, then $A - cI$ and $B - cI$ are similar for every
$c \in R$, with the same transforming matrix: $C^{-1} (A - cI) C = B - cI$. -/
theorem IsSimilar.sub_smul_one {A B : Matrix n n R} (h : IsSimilar A B) (c : R) :
    IsSimilar (A - c • 1) (B - c • 1) := by
  obtain ⟨C, hC, rfl⟩ := h
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  refine ⟨C, hC, ?_⟩
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.nonsing_inv_mul C hd]

/-- If $A, B \in R^{n \times n}$ are similar, then $A^k$ and $B^k$ are similar for every
$k \in \mathbb{N}$, with the same transforming matrix. -/
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

/-- Let $P, Q \in R^{n \times n}$ with $Q$ invertible. Then $PQ$ and $QP$ are similar, since
$QP = Q (PQ) Q^{-1}$. -/
theorem isSimilar_mul_comm_of_isUnit {P Q : Matrix n n R} (hQ : IsUnit Q) :
    IsSimilar (P * Q) (Q * P) := by
  refine ⟨Q⁻¹, (isUnit_nonsing_inv_iff).2 hQ, ?_⟩
  have hd := (isUnit_iff_isUnit_det Q).1 hQ
  rw [nonsing_inv_nonsing_inv Q hd, Matrix.mul_assoc, Matrix.mul_assoc,
    mul_nonsing_inv Q hd, Matrix.mul_one]

end CommRing

section Field

variable {K : Type*} [Field K]

/-- Let $K$ be a field. If $A, B \in K^{n \times n}$ are similar, then their null spaces have the
same dimension:
$$\dim \ker A = \dim \ker B.$$

The null space of $A$ is the kernel of `A.mulVecLin`. The proof uses that similar matrices have
the same rank. Together with `Matrix.IsSimilar.sub_smul_one` and `Matrix.IsSimilar.pow`, the
theorem shows that similar matrices give every eigenvalue the same geometric multiplicity and
the same index, as `Matrix.IsSimilar.charpoly_eq` shows that they give it the same algebraic
multiplicity. -/
theorem IsSimilar.finrank_ker_mulVecLin_eq {A B : Matrix n n K} (h : IsSimilar A B) :
    Module.finrank K (LinearMap.ker A.mulVecLin)
      = Module.finrank K (LinearMap.ker B.mulVecLin) := by
  obtain ⟨C, hC, rfl⟩ := h
  have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  rw [← Matrix.finrank_ker_mulVecLin_conj (Matrix.isUnit_nonsing_inv_iff.2 hC) (A := A),
    Matrix.nonsing_inv_nonsing_inv C hd]

/-- Let $K$ be a field and $A \in K^{n \times n}$. Then $A$ is **diagonalizable**, that is, similar
to a diagonal matrix $\operatorname{diag}(d)$ for some $d \in K^n$, if and only if there are
$d \in K^n$ and linearly independent vectors $v_j \in K^n$, $j \in n$, with
$$A v_j = d_j v_j \quad \text{for all } j.$$

Both directions read the relation $AC = C \operatorname{diag}(d)$ column by column: the columns
of the transforming matrix $C$ are the eigenvectors, and $C$ is nonsingular exactly when they
are linearly independent. -/
theorem isSimilar_diagonal_iff_exists_basis_eigenvectors (A : Matrix n n K) :
    (∃ d : n → K, IsSimilar A (Matrix.diagonal d)) ↔
      ∃ (d : n → K) (v : n → n → K), LinearIndependent K v ∧ ∀ j, A *ᵥ v j = d j • v j := by
  constructor
  · rintro ⟨d, C, hC, hA⟩
    have hd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
    have hAC : A * C = C * Matrix.diagonal d := by
      rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv C hd,
        Matrix.one_mul]
    refine ⟨d, C.col, Matrix.linearIndependent_col_iff_isUnit.2 hC, fun j => ?_⟩
    funext i
    have h := congrFun (congrFun hAC i) j
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    simp only [Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    change ∑ k, A i k * C k j = d j * C i j
    rw [h]
    exact mul_comm _ _
  · rintro ⟨d, v, hv, hvA⟩
    have hC : IsUnit ((Matrix.of v)ᵀ) := Matrix.linearIndependent_col_iff_isUnit.1 hv
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

/-- Let $K$ be a field and $A \in K^{n \times n}$. Then $A$ is similar to a diagonal matrix if and
only if the eigenspaces of $A$ span $K^n$:
$$\sum_{\mu \in K} \ker (A - \mu I) = K^n.$$

The eigenspaces are those of the linear map `A.mulVecLin`, and the sum of subspaces is their
supremum. The proof transports `Matrix.isSimilar_diagonal_iff_exists_basis_eigenvectors` to this
linear map. -/
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

/-- Let $K$ be a field, $E$ a vector space over $K$, and $f$ a linear map from $E$ to $E$. Let
$(b_i)_{i \in \iota}$ be a basis of $E$ indexed by a finite type $\iota$, and let
$\lambda_i \in K$ satisfy $f(b_i) = \lambda_i b_i$ for all $i$. Then the spectrum of $f$ is the
set $\{\lambda_i : i \in \iota\}$.

In the basis $b$, the map $f$ is the diagonal matrix of the $\lambda_i$, whose spectrum is the
set of its diagonal entries. This is the operator form of
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

/-- Let $K$ be a field and $A \in K^{n \times n}$. If $\mu \in K$ is not in the spectrum of $A$,
then $\det (A - \mu I)$ is a unit, so $A - \mu I$ is nonsingular. -/
theorem isUnit_det_sub_smul_one_of_notMem_spectrum {A : Matrix n n K} {μ : K}
    (h : μ ∉ spectrum K A) : IsUnit (A - μ • 1).det := by
  rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det] at h
  rw [show A - μ • 1 = -(μ • 1 - A) by abel, det_neg]
  exact (isUnit_one.neg.pow _).mul h

end Field

/-! ### Unitary similarity -/

section Unitary

variable {R : Type*} [CommRing R] [StarRing R]

/-- Let $R$ be a commutative ring with a star operation. Two matrices $A, B \in R^{n \times n}$ are
**unitarily similar** if there is a unitary matrix $U \in R^{n \times n}$ with
$$B = U^H A U.$$
This is the second sentence of [quarteroni2000numerical] Definition 1.14.

The unitary matrices are `Matrix.unitaryGroup n R`, and $U^H$ is `star U`. This is the relation
that the Schur, spectral and normal theorems produce. -/
def IsUnitarilySimilar (A B : Matrix n n R) : Prop := ∃ U ∈ unitaryGroup n R, B = star U * A * U

/-- If $A, B \in R^{n \times n}$ are unitarily similar, then they are similar, because
$U^{-1} = U^H$ for a unitary matrix $U$. -/
theorem IsUnitarilySimilar.isSimilar {A B : Matrix n n R} (h : IsUnitarilySimilar A B) :
    IsSimilar A B := by
  obtain ⟨U, hU, rfl⟩ := h
  refine ⟨U, ⟨⟨U, star U, mem_unitaryGroup_iff.1 hU, mem_unitaryGroup_iff'.1 hU⟩, rfl⟩, ?_⟩
  rw [inv_eq_left_inv (mem_unitaryGroup_iff'.1 hU)]

/-- Unitary similarity is reflexive: every square matrix $A$ is unitarily similar to itself. -/
@[refl]
theorem IsUnitarilySimilar.refl (A : Matrix n n R) : IsUnitarilySimilar A A :=
  ⟨1, one_mem _, by simp⟩

/-- Unitary similarity is symmetric: if $A$ is unitarily similar to $B$, then $B$ is unitarily
similar to $A$. -/
@[symm]
theorem IsUnitarilySimilar.symm {A B : Matrix n n R} (h : IsUnitarilySimilar A B) :
    IsUnitarilySimilar B A := by
  obtain ⟨U, hU, rfl⟩ := h
  refine ⟨star U, Unitary.star_mem hU, ?_⟩
  rw [star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU,
    Matrix.one_mul, Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU, Matrix.mul_one]

/-- Unitary similarity is transitive: if $A$ is unitarily similar to $B$ and $B$ is unitarily
similar to $C$, then $A$ is unitarily similar to $C$. -/
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

/-- Let $K$ be an algebraically closed field and $A \in K^{n \times n}$. Then $A$ is similar to a
diagonal matrix if and only if $A$ is **nondefective**: for every $\mu \in K$, the geometric
multiplicity of $\mu$ equals its algebraic multiplicity,
$$\dim \ker (A - \mu I) = \operatorname{mult}_\mu (p_A),$$
where $p_A$ is the characteristic polynomial of $A$ and $\operatorname{mult}_\mu$ is the
multiplicity of $\mu$ as a root. This is the statement in [quarteroni2000numerical] §1.8, after
Property 1.6.

For $\mu$ not an eigenvalue, both sides are $0$. The kernel is the eigenspace of `A.mulVecLin`,
and the multiplicity is `Polynomial.rootMultiplicity`. The generalized eigenspaces of $A$ span
$K^n$ (`Module.End.iSup_maxGenEigenspace_eq_top`) and have the algebraic multiplicities as
dimensions (`LinearMap.finrank_maxGenEigenspace_eq`), and diagonalizability is the spanning of
the eigenspaces (`Matrix.isSimilar_diagonal_iff_iSup_eigenspace_eq_top`); the two spannings
agree exactly when every eigenspace fills its generalized eigenspace. -/
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

section Unitary

variable {R : Type*} [CommRing R] [StarRing R]

/-- Let $R$ be a commutative ring with a star operation, let $Q \in R^{n \times n}$ be unitary, and
let $A \in R^{n \times n}$. Then for every $k \in \mathbb{N}$,
$$(Q^H A Q)^k = Q^H A^k Q.$$

Conjugation by a unitary matrix is a star-algebra automorphism (`Unitary.conjStarAlgAut`), so it
commutes with powers. -/
theorem conj_pow_of_mem_unitaryGroup {Q : Matrix n n R} (hQ : Q ∈ unitaryGroup n R)
    (A : Matrix n n R) (k : ℕ) : (star Q * A * Q) ^ k = star Q * A ^ k * Q := by
  simpa using (map_pow (Unitary.conjStarAlgAut R (Matrix n n R) (star ⟨Q, hQ⟩)) A k).symm

end Unitary

end Matrix
