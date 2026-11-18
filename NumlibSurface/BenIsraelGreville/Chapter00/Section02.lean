/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Similar
import NumlibSurface.BenIsraelGreville.Chapter00.Section01
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Matrices and linear transformations

Section 0.2 of [benIsrael2003generalized] introduces the coordinate conventions
for matrices and linear transformations. It describes adjoints, orthogonal
complements, Hermitian spectra, and singular value decompositions.

## Deviations from the source

* **Section 0.2.6** (correction). The diagonal identity for complex vectors
  already implies that the matrix is Hermitian. The printed counterexample
  satisfies that identity on real vectors.
* **Equation (30)** (typo). The list of eigenvalues of $AA^H$ has length
  equal to the number of rows of $A$.
-/

namespace BenIsraelGreville.Chapter00

open Matrix
open scoped InnerProductSpace

/-- **Section 0.2.1** of [benIsrael2003generalized]. An element of $Q_{k,n}$
is an increasing sequence of $k$ indices among $n$. -/
abbrev IndexSequence (k n : ℕ) := Fin k ↪o Fin n

/-- **Section 0.2.1** of [benIsrael2003generalized]. Select the rows and columns
of a matrix in increasing order. -/
abbrev submatrix {K : Type*} {m n r c : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (rows : IndexSequence r m) (cols : IndexSequence c n) : Matrix (Fin r) (Fin c) K :=
  A.submatrix rows cols

/-- A rectangular diagonal matrix vanishes away from its main diagonal. -/
def IsRectDiagonal {K : Type*} [Zero K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) : Prop :=
  ∀ i j, i.val ≠ j.val → A i j = 0

/-- A rectangular upper triangular matrix vanishes below the main diagonal. -/
def IsRectUpperTriangular {K : Type*} [Zero K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) : Prop :=
  ∀ i j, j.val < i.val → A i j = 0

/-- A rectangular lower triangular matrix vanishes above the main diagonal. -/
def IsRectLowerTriangular {K : Type*} [Zero K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) : Prop :=
  ∀ i j, i.val < j.val → A i j = 0

section MatrixDefinitions

variable {m n : Type*}

/-- **Section 0.2.1** of [benIsrael2003generalized]. Transposition exchanges
the row and column indices. -/
theorem transpose_apply (A : Matrix m n ℂ) (i : n) (j : m) : Aᵀ i j = A j i :=
  rfl

/-- **Section 0.2.1** of [benIsrael2003generalized]. The conjugate transpose
exchanges the row and column indices and conjugates the entry. -/
theorem conjTranspose_apply (A : Matrix m n ℂ) (i : n) (j : m) :
    Aᴴ i j = star (A j i) :=
  rfl

/-- **Section 0.2.1** of [benIsrael2003generalized]. A complex square matrix
is Hermitian precisely when it is equal to its conjugate transpose. -/
theorem isHermitian_iff (A : Matrix n n ℂ) : A.IsHermitian ↔ A = Aᴴ :=
  eq_comm

/-- **Section 0.2.1** of [benIsrael2003generalized]. A real square matrix
is symmetric precisely when it is equal to its transpose. -/
theorem isSymm_iff (A : Matrix n n ℝ) : A.IsSymm ↔ A = Aᵀ :=
  eq_comm

variable [Fintype n]

/-- **Section 0.2.1** of [benIsrael2003generalized]. A square matrix is normal
precisely when it commutes with its conjugate transpose. -/
theorem isStarNormal_iff (A : Matrix n n ℂ) : IsStarNormal A ↔ A * Aᴴ = Aᴴ * A :=
  ⟨fun h => h.star_comm_self.eq.symm, fun h => ⟨h.symm⟩⟩

variable [DecidableEq n]

/-- **Section 0.2.1** of [benIsrael2003generalized]. A complex matrix is
unitary precisely when its conjugate transpose is its inverse. -/
theorem mem_unitary_iff (A : Matrix n n ℂ) :
    A ∈ Matrix.unitaryGroup n ℂ ↔ IsUnit A ∧ Aᴴ = A⁻¹ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  constructor
  · intro h
    exact ⟨isUnit_iff_exists_inv.mpr ⟨_, h⟩, (Matrix.inv_eq_right_inv h).symm⟩
  · rintro ⟨hu, he⟩
    exact he.symm ▸ Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hu)

/-- **Section 0.2.1** of [benIsrael2003generalized]. A real matrix is
orthogonal precisely when its transpose is its inverse. -/
theorem orthogonal_iff (A : Matrix n n ℝ) :
    A ∈ Matrix.orthogonalGroup n ℝ ↔ IsUnit A ∧ Aᵀ = A⁻¹ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  constructor
  · intro h
    exact ⟨isUnit_iff_exists_inv.mpr ⟨_, h⟩, (Matrix.inv_eq_right_inv h).symm⟩
  · rintro ⟨hu, he⟩
    exact he.symm ▸ Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hu)

end MatrixDefinitions

section LinearTransformations

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]

/-- **Section 0.2.2** of [benIsrael2003generalized]. A map is linear if it
preserves a scalar multiple plus an addend. -/
def IsLinear (T : U → V) : Prop :=
  ∀ (a : K) (u v : U), T (a • u + v) = a • T u + T v

/-- The source linearity criterion is equivalent to the existence of a
linear map with the specified action. -/
theorem isLinear_iff_exists_linearMap (T : U → V) :
    IsLinear (K := K) T ↔ ∃ f : U →ₗ[K] V, ⇑f = T := by
  constructor
  · intro h
    have hzero : T 0 = 0 := by
      have h' := h (1 : K) 0 0
      simp only [one_smul, zero_add] at h'
      exact add_left_cancel (h'.symm.trans (add_zero _).symm)
    let f : U →ₗ[K] V := {
      toFun := T
      map_add' := fun x y => by simpa only [one_smul] using h 1 x y
      map_smul' := fun a x => by simpa only [RingHom.id_apply, add_zero, hzero] using h a x 0 }
    exact ⟨f, rfl⟩
  · rintro ⟨f, rfl⟩ a u v
    simp

/-- **Section 0.2.2** of [benIsrael2003generalized]. Addition and scalar
multiplication of transformations are pointwise. The zero and identity
transformations act by zero and the identity, respectively. -/
theorem linearMap_arithmetic (S T : U →ₗ[K] V) (a : K) (u : U) :
    (S + T) u = S u + T u ∧ (a • S) u = a • S u ∧
      (0 : U →ₗ[K] V) u = 0 ∧ (LinearMap.id : U →ₗ[K] U) u = u :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Section 0.2.3** of [benIsrael2003generalized]. The range of a
transformation is the set of its images. -/
theorem mem_range_iff_exists (T : U →ₗ[K] V) (v : V) :
    v ∈ LinearMap.range T ↔ ∃ u, T u = v :=
  Iff.rfl

/-- **Section 0.2.3** of [benIsrael2003generalized]. The inverse image of
a point is the set of points mapped to it. -/
theorem mem_fiber_iff (T : U →ₗ[K] V) (u : U) (v : V) :
    u ∈ (T ⁻¹' {v}) ↔ T u = v :=
  Iff.rfl

/-- **Section 0.2.3** of [benIsrael2003generalized]. The null space is the
inverse image of zero. -/
theorem mem_ker_iff (T : U →ₗ[K] V) (u : U) :
    u ∈ LinearMap.ker T ↔ T u = 0 :=
  LinearMap.mem_ker

/-- **Section 0.2.4** of [benIsrael2003generalized]. Injectivity means that
each point in the range has a unique preimage. -/
theorem injective_iff_unique_preimage (T : U →ₗ[K] V) :
    Function.Injective T ↔ ∀ v ∈ LinearMap.range T, ∃! u, T u = v := by
  constructor
  · rintro h v ⟨u, rfl⟩
    exact ⟨u, rfl, fun w hw => h hw⟩
  · intro h u w huw
    obtain ⟨z, _, hz⟩ := h (T w) ⟨w, rfl⟩
    exact (hz u huw).trans (hz w rfl).symm

/-- **Section 0.2.4** of [benIsrael2003generalized]. A transformation is
onto exactly when its range is the whole codomain. -/
theorem surjective_iff_range_eq_top (T : U →ₗ[K] V) :
    Function.Surjective T ↔ LinearMap.range T = ⊤ :=
  LinearMap.range_eq_top.symm

/-- **Equations (17a)–(17b)** of [benIsrael2003generalized], Chapter 0.
A transformation is bijective precisely when it has a two-sided linear inverse. -/
theorem bijective_iff_exists_inverse (T : U →ₗ[K] V) :
    Function.Bijective T ↔ ∃ S : V →ₗ[K] U, S.comp T = LinearMap.id ∧ T.comp S = LinearMap.id := by
  constructor
  · intro h
    let e := LinearEquiv.ofBijective T h
    exact ⟨e.symm.toLinearMap, LinearMap.ext e.symm_apply_apply, LinearMap.ext e.apply_symm_apply⟩
  · rintro ⟨S, hL, hR⟩
    have hLeft : Function.LeftInverse S T := fun x => LinearMap.congr_fun hL x
    have hRight : Function.RightInverse S T := fun y => LinearMap.congr_fun hR y
    exact ⟨hLeft.injective, hRight.surjective⟩

/-- **Equations (18)–(19)** of [benIsrael2003generalized], Chapter 0.
The columns of the representing matrix are the coordinates of the
images of the domain basis vectors. -/
theorem existsUnique_matrix_representation {m n : Type*} [Fintype m] [Finite n]
    (T : U →ₗ[K] V) (u : Module.Basis n K U) (v : Module.Basis m K V) :
    ∃! A : Matrix m n K, ∀ j, T (u j) = ∑ i, A i j • v i := by
  classical
  let := Fintype.ofFinite n
  refine ⟨T.toMatrix u v, fun j => ?_, fun A hA => ?_⟩
  · simpa only [LinearMap.toMatrix_apply] using (v.sum_repr (T (u j))).symm
  · ext i j
    simpa [LinearMap.toMatrix_apply, Finsupp.single_apply, eq_comm] using
      (congrArg (fun x => v.repr x i) (hA j)).symm

/-- **Equation (20a)** of [benIsrael2003generalized], Chapter 0.
A vector is in the matrix range exactly when it is of the form $Ax$. -/
theorem mem_matrixRange_iff {m n : Type*} [Fintype n] (A : Matrix m n K) (y : m → K) :
    y ∈ LinearMap.range A.mulVecLin ↔ ∃ x, A *ᵥ x = y :=
  Iff.rfl

/-- **Equation (20b)** of [benIsrael2003generalized], Chapter 0.
The matrix null space consists of vectors sent to zero. -/
theorem mem_matrixNullSpace_iff {m n : Type*} [Fintype n] (A : Matrix m n K) (x : n → K) :
    x ∈ LinearMap.ker A.mulVecLin ↔ A *ᵥ x = 0 :=
  LinearMap.mem_ker

end LinearTransformations

section Adjoint

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **Equation (21)** of [benIsrael2003generalized], Chapter 0. Moving
a matrix to the other slot of the inner product conjugate-transposes it. -/
theorem inner_mulVec_eq (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ m) :
    inner ℂ y (A.toEuclideanLin x) = inner ℂ (Aᴴ.toEuclideanLin y) x := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]

/-- **Equation (22)** of [benIsrael2003generalized], Chapter 0. A Hermitian
matrix acts by a self-adjoint map for the standard inner product. -/
theorem isHermitian_iff_inner (A : Matrix n n ℂ) :
    A.IsHermitian ↔ ∀ x y, inner ℂ y (A.toEuclideanLin x) = inner ℂ (A.toEuclideanLin y) x := by
  rw [← Matrix.isSymmetric_toEuclideanLin_iff]
  exact ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

/-- **Section 0.2.6** of [benIsrael2003generalized]. Over the complex field,
the diagonal equality suffices for a matrix to be Hermitian. -/
theorem isHermitian_iff_inner_diag (A : Matrix n n ℂ) :
    A.IsHermitian ↔ ∀ x, inner ℂ x (A.toEuclideanLin x) = inner ℂ (A.toEuclideanLin x) x := by
  constructor
  · intro h x
    exact (isHermitian_iff_inner A).mp h x x
  · intro h
    have hSym := (LinearMap.isSymmetric_iff_inner_map_self_real A.toEuclideanLin).mpr
      fun x => (inner_conj_symm _ _).trans (h x)
    exact (isHermitian_iff_inner A).mpr fun x y => (hSym y x).symm

/-- **Equation (23)** of [benIsrael2003generalized], Chapter 0. The adjoint
is the unique map that satisfies the inner product identity. -/
theorem adjoint_unique {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) :
    ∃! S : F →ₗ[ℂ] E, ∀ x y, inner ℂ y (T x) = inner ℂ (S y) x := by
  refine ⟨T.adjoint, fun x y => (LinearMap.adjoint_inner_left T x y).symm, fun S h => ?_⟩
  exact (LinearMap.eq_adjoint_iff S T).mpr fun y x => (h x y).symm

omit [DecidableEq n] in
/-- **Equation (24)** of [benIsrael2003generalized], Chapter 0.
The orthogonal complement of a subspace consists of vectors orthogonal
to every member of the subspace. -/
theorem mem_orthogonal_iff (L : Submodule ℂ (EuclideanSpace ℂ n)) (x : EuclideanSpace ℂ n) :
    x ∈ Lᗮ ↔ ∀ y ∈ L, inner ℂ y x = 0 :=
  L.mem_orthogonal x

omit [DecidableEq n] in
/-- **Equation (25)** of [benIsrael2003generalized], Chapter 0.
A complex coordinate subspace and its orthogonal complement are complementary. -/
theorem isCompl_orthogonal (L : Submodule ℂ (EuclideanSpace ℂ n)) : IsCompl L Lᗮ :=
  L.isCompl_orthogonal

omit [DecidableEq n] in
/-- **Section 0.2.8** of [benIsrael2003generalized]. Two orthogonal
subspaces that span the space are complementary. -/
theorem isCompl_of_le_orthogonal_of_sup_eq_top (L M : Submodule ℂ (EuclideanSpace ℂ n))
    (hM : M ≤ Lᗮ) (hTop : L ⊔ M = ⊤) : IsCompl L M :=
  ⟨L.isCompl_orthogonal.disjoint.mono_right hM, codisjoint_iff.mpr hTop⟩

/-- **Theorem 1** of [benIsrael2003generalized], Chapter 0.
The range of a matrix and the kernel of its conjugate transpose
are orthogonal complements, as are the range of its conjugate transpose
and its kernel. -/
theorem theorem_1 (A : Matrix m n ℂ) :
    A.toEuclideanLin.ker = Aᴴ.toEuclideanLin.rangeᗮ ∧
      Aᴴ.toEuclideanLin.ker = A.toEuclideanLin.rangeᗮ := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact ⟨by rw [LinearMap.orthogonal_range, LinearMap.adjoint_adjoint],
    A.toEuclideanLin.orthogonal_range.symm⟩

end Adjoint

section Norms

/-- **Conditions (M1)–(M3)** of [benIsrael2003generalized], Chapter 0.
A matrix norm is a vector norm on the space of matrices. -/
abbrev IsMatrixNorm {m n : Type*} (f : Matrix m n ℂ → ℝ) : Prop :=
  IsVectorNorm f

/-- **Condition (M4)** of [benIsrael2003generalized], Chapter 0. A family
of matrix norms is multiplicative when it is submultiplicative on every
compatible product. -/
def IsMultiplicativeMatrixNorm (f : ∀ m n : ℕ, Matrix (Fin m) (Fin n) ℂ → ℝ) : Prop :=
  (∀ m n, IsMatrixNorm (f m n)) ∧
    ∀ m n d (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin n) (Fin d) ℂ),
      f m d (A * B) ≤ f m n A * f n d B

/-- **Exercise 35** of [benIsrael2003generalized], Chapter 0. A matrix norm
is consistent with vector norms if it bounds the amplification of the
vector norm by the matrix. -/
def areConsistentNorms {m n : Type*} [Fintype n] (f : Matrix m n ℂ → ℝ)
    (g : (n → ℂ) → ℝ) (h : (m → ℂ) → ℝ) : Prop :=
  IsMatrixNorm f ∧ IsVectorNorm g ∧ IsVectorNorm h ∧ ∀ A x, h (A *ᵥ x) ≤ f A * g x

/-- **Exercise 40** of [benIsrael2003generalized], Chapter 0. A unitarily
invariant matrix norm is invariant under multiplying by unitary factors. -/
def isUnitarilyInvariantNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (f : Matrix m n ℂ → ℝ) : Prop :=
  IsMatrixNorm f ∧ ∀ A (U : Matrix m m ℂ) (V : Matrix n n ℂ),
    U ∈ Matrix.unitaryGroup m ℂ → V ∈ Matrix.unitaryGroup n ℂ → f (U * A * V) = f A

end Norms

section Spectrum

open Module.End

variable {n : Type*} [Fintype n]

/-- **Equation (28)** of [benIsrael2003generalized], Chapter 0. A nonzero
vector is an eigenvector when multiplication by the matrix scales it. -/
theorem hasEigenvector_iff_mulVec_eq (A : Matrix n n ℂ) (lam : ℂ) (x : n → ℂ) :
    HasEigenvector A.mulVecLin lam x ↔ A *ᵥ x = lam • x ∧ x ≠ 0 := by
  rw [hasEigenvector_iff, mem_eigenspace_iff, Matrix.mulVecLin_apply]

/-- **Equation (29)** of [benIsrael2003generalized], Chapter 0. An
eigenspace consists of all vectors satisfying the eigenvector equation. -/
theorem mem_eigenspace_iff_mulVec_eq (A : Matrix n n ℂ) (lam : ℂ) (x : n → ℂ) :
    x ∈ eigenspace A.mulVecLin lam ↔ A *ᵥ x = lam • x :=
  mem_eigenspace_iff

/-- **Section 0.2.10** of [benIsrael2003generalized]. The geometric
multiplicity of a scalar is the dimension of its eigenspace. -/
noncomputable def geometricMultiplicity (A : Matrix n n ℂ) (lam : ℂ) : ℕ :=
  Module.finrank ℂ (eigenspace A.mulVecLin lam)

variable [DecidableEq n]

/-- **Section 0.2.10** of [benIsrael2003generalized]. The spectrum of a
matrix is the set of scalars for which it has a nonzero eigenvector. -/
theorem spectrum_eq_setOf_hasEigenvalue (A : Matrix n n ℂ) :
    spectrum ℂ A = {lam | ∃ x : n → ℂ, A *ᵥ x = lam • x ∧ x ≠ 0} := by
  ext lam
  change lam ∈ spectrum ℂ A ↔ ∃ x : n → ℂ, A *ᵥ x = lam • x ∧ x ≠ 0
  rw [← Matrix.hasEigenvalue_toEuclideanLin_iff]
  constructor
  · intro h
    obtain ⟨x, hx, h0⟩ := h.exists_hasEigenvector
    rw [mem_eigenspace_iff] at hx
    refine ⟨WithLp.ofLp x, ?_, (WithLp.ofLp_eq_zero 2).ne.mpr h0⟩
    simpa using congrArg WithLp.ofLp hx
  · rintro ⟨x, hx, h0⟩
    refine hasEigenvalue_of_hasEigenvector (x := WithLp.toLp 2 x)
      ⟨?_, (WithLp.toLp_eq_zero 2).ne.mpr h0⟩
    rw [mem_eigenspace_iff, Matrix.toEuclideanLin_toLp, hx]
    rfl

/-- **Section 0.2.11(a)** of [benIsrael2003generalized]. Every eigenvalue
of a Hermitian matrix is real. -/
theorem hermitian_eigenvalue_real {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {lam : ℂ} (hlam : lam ∈ spectrum ℂ A) : star lam = lam :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).conj_eigenvalue_eq_self
    ((Matrix.hasEigenvalue_toEuclideanLin_iff A lam).mpr hlam)

/-- **Section 0.2.11(b)** of [benIsrael2003generalized]. Eigenspaces of
a Hermitian matrix for distinct eigenvalues are orthogonal. -/
theorem hermitian_eigenvectors_orthogonal {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {lam μ : ℂ} (hne : lam ≠ μ) {x y : EuclideanSpace ℂ n}
    (hx : x ∈ eigenspace A.toEuclideanLin lam) (hy : y ∈ eigenspace A.toEuclideanLin μ) :
    inner ℂ x y = 0 :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).orthogonalFamily_eigenspaces hne
    ⟨x, hx⟩ ⟨y, hy⟩

/-- **Section 0.2.11(c)** of [benIsrael2003generalized]. A Hermitian
matrix has an orthonormal basis of eigenvectors. -/
theorem hermitian_exists_orthonormal_eigenbasis {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (lam : n → ℝ),
      ∀ i, A.toEuclideanLin (b i) = (lam i : ℂ) • b i := by
  refine ⟨hA.eigenvectorBasis, hA.eigenvalues, fun i => ?_⟩
  apply WithLp.ofLp_injective 2
  simpa using hA.mulVec_eigenvectorBasis i

/-- **Section 0.2.11(d)** of [benIsrael2003generalized]. The $i$th
eigenvalue is the largest quadratic form on unit vectors orthogonal to
the earlier eigenvectors in the descending order. -/
theorem hermitian_rayleigh_recursion {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (i : Fin (Fintype.card n)) :
    let h := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    let hn : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace
    IsGreatest {c : ℝ | ∃ x : EuclideanSpace ℂ n, ‖x‖ = 1 ∧
      (∀ j < i, inner ℂ (h.eigenvectorBasis hn j) x = 0) ∧
        RCLike.re (inner ℂ (A.toEuclideanLin x) x) = c} (h.eigenvalues hn i) := by
  intro h hn
  have hMax := h.isGreatest_rayleighQuotient_orthogonal hn i
  let b := h.eigenvectorBasis hn
  have hb : ‖b i‖ = 1 := b.orthonormal.1 i
  constructor
  · refine ⟨b i, hb, fun j hj => b.inner_eq_zero hj.ne, ?_⟩
    rw [← LinearMap.rayleighQuotient_of_norm_eq_one A.toEuclideanLin hb]
    exact h.rayleighQuotient_eigenvectorBasis hn i
  · rintro _ ⟨x, hx, horth, rfl⟩
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    exact hMax.2 ⟨x, hx0, horth, LinearMap.rayleighQuotient_of_norm_eq_one _ hx⟩

open scoped ComplexOrder in
/-- **Section 0.2.12** of [benIsrael2003generalized]. A Hermitian matrix
is positive semidefinite if its quadratic form is nonnegative. -/
theorem posSemidef_iff_inner {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ x : EuclideanSpace ℂ n, 0 ≤ inner ℂ x (A.toEuclideanLin x) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec, and_iff_right hA]
  constructor
  · intro h x
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h (WithLp.ofLp x)
  · intro h x
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h (WithLp.toLp 2 x)

open scoped ComplexOrder in
/-- **Section 0.2.12** of [benIsrael2003generalized]. A Hermitian matrix
is positive semidefinite precisely when its eigenvalues are nonnegative. -/
theorem posSemidef_iff_eigenvalues_nonneg {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ i, 0 ≤ hA.eigenvalues i :=
  hA.posSemidef_iff_eigenvalues_nonneg

open scoped ComplexOrder in
/-- **Section 0.2.12** of [benIsrael2003generalized]. A Hermitian matrix
is positive definite if its quadratic form is positive off zero. -/
theorem posDef_iff_inner {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ x : EuclideanSpace ℂ n, x ≠ 0 → 0 < inner ℂ x (A.toEuclideanLin x) := by
  rw [Matrix.posDef_iff_dotProduct_mulVec, and_iff_right hA]
  constructor
  · intro h x hx
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      h ((WithLp.ofLp_eq_zero 2).ne.mpr hx)
  · intro h x hx
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      h (WithLp.toLp 2 x) ((WithLp.toLp_eq_zero 2).ne.mpr hx)

open scoped ComplexOrder in
/-- **Section 0.2.12** of [benIsrael2003generalized]. A Hermitian matrix
is positive definite precisely when its eigenvalues are positive. -/
theorem posDef_iff_eigenvalues_pos {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ i, 0 < hA.eigenvalues i :=
  hA.posDef_iff_eigenvalues_pos

end Spectrum

section SingularValues

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Section 0.2.13** of [benIsrael2003generalized]. The singular values
are indexed in descending order up to the rank of the matrix. -/
noncomputable def singularValues (A : Matrix m n ℂ) (i : Fin A.rank) : ℝ :=
  A.sortedSingularValues i

private theorem sortedSingularValues_eq_sqrt {A : Matrix m n ℂ}
    (i : Fin (Fintype.card n)) :
    A.sortedSingularValues i =
      Real.sqrt ((isHermitian_conjTranspose_mul_self A).eigenvalues₀ i) := by
  classical
  have hn : Module.finrank ℂ (EuclideanSpace ℂ n) = Fintype.card n := finrank_euclideanSpace
  have hGram :
      A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin = (Aᴴ * A).toEuclideanLin := by
    rw [Matrix.toEuclideanLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [Matrix.sortedSingularValues, LinearMap.singularValues_fin A.toEuclideanLin hn]
  congr 1
  have hEig : A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues hn =
      (isHermitian_conjTranspose_mul_self A).eigenvalues₀ := by
    rw [Matrix.IsHermitian.eigenvalues₀,
      LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff, hGram]
  exact congrFun hEig i

/-- **Equation (31b)** of [benIsrael2003generalized], Chapter 0.
Each positive singular value is the square root of the corresponding
eigenvalue of $A^HA$ in the descending eigenvalue list. -/
theorem singularValues_eq_sqrt_eigenvalues_gram (A : Matrix m n ℂ) (i : Fin A.rank) :
    singularValues A i = Real.sqrt ((isHermitian_conjTranspose_mul_self A).eigenvalues₀
      (Fin.castLE A.rank_le_card_width i)) :=
  sortedSingularValues_eq_sqrt (Fin.castLE A.rank_le_card_width i)

/-- **Equation (31a)** of [benIsrael2003generalized], Chapter 0.
Each positive singular value is the square root of the corresponding
eigenvalue of $AA^H$ in the descending eigenvalue list. -/
theorem singularValues_eq_sqrt_eigenvalues_adjoint_gram [DecidableEq m]
    (A : Matrix m n ℂ) (i : Fin A.rank) :
    singularValues A i = Real.sqrt ((isHermitian_mul_conjTranspose_self A).eigenvalues₀
      (Fin.castLE A.rank_le_card_height i)) := by
  have h := sortedSingularValues_eq_sqrt (A := Aᴴ) (Fin.castLE A.rank_le_card_height i)
  simpa [singularValues, Matrix.sortedSingularValues_conjTranspose] using h

/-- **Equation (32)** of [benIsrael2003generalized], Chapter 0.
The singular values form a positive, nonincreasing list. -/
theorem singularValues_antitone_pos (A : Matrix m n ℂ) :
    Antitone (singularValues A) ∧ ∀ i, 0 < singularValues A i := by
  refine ⟨fun _ _ hij => A.sortedSingularValues_antitone hij, fun i => ?_⟩
  exact (A.sortedSingularValues_nonneg i).lt_of_ne'
    ((A.sortedSingularValues_eq_zero_iff_rank_le i).not.mpr (not_le.mpr i.isLt))

omit [DecidableEq n] in
open scoped ComplexOrder in
/-- **Equation (30)** of [benIsrael2003generalized], Chapter 0. In the sorted
list for $AA^H$, the first rank-many eigenvalues are positive and the rest
are zero. -/
theorem adjoint_gram_eigenvalues_ordered [DecidableEq m] (A : Matrix m n ℂ) :
    let eig := (isHermitian_mul_conjTranspose_self A).eigenvalues₀
    Antitone eig ∧ ∀ i, (0 < eig i ↔ i.val < A.rank) ∧ (eig i = 0 ↔ A.rank ≤ i.val) := by
  classical
  intro eig
  refine ⟨Matrix.IsHermitian.eigenvalues₀_antitone _, fun i => ?_⟩
  have he : Real.sqrt (eig i) = A.sortedSingularValues i := by
    simpa using (sortedSingularValues_eq_sqrt (A := Aᴴ) i).symm
  have hpos : 0 < eig i ↔ i.val < A.rank := by
    rw [← Real.sqrt_pos, he]
    exact ⟨fun h => not_le.mp fun hr =>
      h.ne' ((A.sortedSingularValues_eq_zero_iff_rank_le i).mpr hr),
      fun hr => (A.sortedSingularValues_nonneg i).lt_of_ne'
        ((A.sortedSingularValues_eq_zero_iff_rank_le i).not.mpr (not_le.mpr hr))⟩
  have hnn : 0 ≤ eig i := by
    let h := posSemidef_self_mul_conjTranspose A
    have heq := h.eigenvalues_nonneg (Fintype.equivOfCardEq (Fintype.card_fin _) i)
    simpa [eig, Matrix.IsHermitian.eigenvalues] using heq
  exact ⟨hpos, ⟨fun hz => not_lt.mp fun hr => (hpos.mpr hr).ne' hz,
    fun hr => le_antisymm (not_lt.mp fun h => (not_lt_of_ge hr) (hpos.mp h)) hnn⟩⟩

end SingularValues

private theorem exists_orthonormalBasis_of_gram
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (T : E →ₗ[ℂ] F) {r d : ℕ} (hr : Module.finrank ℂ T.range = r)
    (hd : Module.finrank ℂ F = d) (hrd : r ≤ d)
    (σ : Fin r → ℝ) (hσ : ∀ i, 0 < σ i) (u : Fin r → E) (hu : Orthonormal ℂ u)
    (hEig : ∀ i, T.adjoint (T (u i)) = (σ i : ℂ) ^ 2 • u i) :
    let agrees (b : OrthonormalBasis (Fin d) ℂ F) :=
      ∀ i : Fin r, b (Fin.castLE hrd i) = (σ i : ℂ)⁻¹ • T (u i)
    (∃ b, agrees b) ∧
      ∀ b, agrees b →
        (∀ i : Fin r, T (T.adjoint (b (Fin.castLE hrd i))) =
            (σ i : ℂ) ^ 2 • b (Fin.castLE hrd i)) ∧
          (∀ i : Fin d, r ≤ i.val → T (T.adjoint (b i)) = 0) := by
  intro agrees
  let w (i : Fin r) := (σ i : ℂ)⁻¹ • T (u i)
  have hw : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    have hInner : inner ℂ (T (u i)) (T (u j)) =
        (σ j : ℂ) ^ 2 * inner ℂ (u i) (u j) := by
      rw [← LinearMap.adjoint_inner_right, hEig j, inner_smul_right]
    simp only [w, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal, hInner, hu]
    split_ifs with hij
    · subst j
      have hne : (σ i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hσ i).ne'
      field_simp
    · simp
  have hSpan : Submodule.span ℂ (Set.range w) = T.range := by
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact T.range.smul_mem _ ⟨u i, rfl⟩
    · rw [finrank_span_eq_card hw.linearIndependent, Fintype.card_fin, hr]
  constructor
  · let s : Set (Fin d) := {i | i.val < r}
    let f (j : Fin d) : F := if h : j.val < r then w ⟨j.val, h⟩ else 0
    have hf : Orthonormal ℂ (s.domRestrict f) := by
      let g (j : s) : Fin r := ⟨j.1.val, j.2⟩
      have hg : Function.Injective g := fun a b h =>
        Subtype.ext (Fin.ext (congrArg (fun i : Fin r => i.val) h))
      convert hw.comp g hg using 1
      funext j
      exact dite_eq_left j.2
    obtain ⟨b, hb⟩ := hf.exists_orthonormalBasis_extension_of_card_eq
      (hd.trans (Fintype.card_fin d).symm)
    refine ⟨b, fun i => ?_⟩
    exact (hb (Fin.castLE hrd i) i.isLt).trans (dite_eq_left i.isLt)
  · intro b hb
    constructor
    · intro i
      rw [hb i, map_smul, hEig i]
      simp only [map_smul, smul_comm ((σ i : ℂ) ^ 2)]
    · intro j hj
      have hOrtho : T.range ≤ (ℂ ∙ b j)ᗮ := by
        rw [← hSpan, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        change w i ∈ (ℂ ∙ b j)ᗮ
        rw [← show b (Fin.castLE hrd i) = w i from hb i]
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        refine b.inner_eq_zero fun he => ?_
        exact (not_lt_of_ge hj) (congrArg Fin.val he ▸ i.isLt)
      have hz : b j ∈ T.adjoint.ker := by
        rw [← T.orthogonal_range, Submodule.mem_orthogonal']
        exact fun y hy => Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hOrtho hy)
      rw [LinearMap.mem_ker.mp hz, map_zero]

private theorem finrank_matrix_range {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Module.finrank ℂ A.toEuclideanLin.range = A.rank := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact (A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).symm

open scoped ComplexOrder in
/-- **Equations (33)–(35)** of [benIsrael2003generalized], Chapter 0.
The normalized adjoint images of the positive eigenvectors of $AA^H$ can
be completed to an orthonormal eigenbasis of $A^HA$. Every orthonormal
completion has the stated eigenvalues and has zero eigenvalues on its tail. -/
theorem gram_eigenbasis_of_adjoint_gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m)))
    (hEig : ∀ i : Fin A.rank, (A * Aᴴ).toEuclideanLin (u (Fin.castLE A.rank_le_height i)) =
      (singularValues A i : ℂ) ^ 2 • u (Fin.castLE A.rank_le_height i)) :
    let agrees (v : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :=
      ∀ i : Fin A.rank, v (Fin.castLE A.rank_le_width i) =
        (singularValues A i : ℂ)⁻¹ • Aᴴ.toEuclideanLin (u (Fin.castLE A.rank_le_height i))
    (∃ v, agrees v) ∧ ∀ v, agrees v →
      (∀ i : Fin A.rank, (Aᴴ * A).toEuclideanLin (v (Fin.castLE A.rank_le_width i)) =
        (singularValues A i : ℂ) ^ 2 • v (Fin.castLE A.rank_le_width i)) ∧
      (∀ j : Fin n, A.rank ≤ j.val → (Aᴴ * A).toEuclideanLin (v j) = 0) := by
  have hr : Module.finrank ℂ Aᴴ.toEuclideanLin.range = A.rank := by
    rw [finrank_matrix_range, rank_conjTranspose]
  simp only [Matrix.toEuclideanLin_mul_apply] at hEig ⊢
  simpa only [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_conjTranspose] using
    exists_orthonormalBasis_of_gram Aᴴ.toEuclideanLin hr finrank_euclideanSpace_fin
      A.rank_le_width (singularValues A) (singularValues_antitone_pos A).2
      (fun i => u (Fin.castLE A.rank_le_height i))
      (u.orthonormal.comp _ (Fin.castLE_injective _))
      (by simpa only [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        conjTranspose_conjTranspose] using hEig)

/-- **Equation (36)** of [benIsrael2003generalized], Chapter 0.
The normalized images of the positive eigenvectors of $A^HA$ can be completed
to an orthonormal eigenbasis of $AA^H$. Every completion has zero eigenvalues
on the added vectors. -/
theorem adjoint_gram_eigenbasis_of_gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (v : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hEig : ∀ i : Fin A.rank, (Aᴴ * A).toEuclideanLin (v (Fin.castLE A.rank_le_width i)) =
      (singularValues A i : ℂ) ^ 2 • v (Fin.castLE A.rank_le_width i)) :
    let agrees (u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))) :=
      ∀ i : Fin A.rank, u (Fin.castLE A.rank_le_height i) =
        (singularValues A i : ℂ)⁻¹ • A.toEuclideanLin (v (Fin.castLE A.rank_le_width i))
    (∃ u, agrees u) ∧ ∀ u, agrees u →
      (∀ i : Fin A.rank, (A * Aᴴ).toEuclideanLin (u (Fin.castLE A.rank_le_height i)) =
        (singularValues A i : ℂ) ^ 2 • u (Fin.castLE A.rank_le_height i)) ∧
      (∀ j : Fin m, A.rank ≤ j.val → (A * Aᴴ).toEuclideanLin (u j) = 0) := by
  simp only [Matrix.toEuclideanLin_mul_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    at hEig ⊢
  exact exists_orthonormalBasis_of_gram A.toEuclideanLin (finrank_matrix_range A)
    finrank_euclideanSpace_fin A.rank_le_height (singularValues A)
    (singularValues_antitone_pos A).2 _ (v.orthonormal.comp _ (Fin.castLE_injective _)) hEig

section Equivalences

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **Equations (37)–(38)** of [benIsrael2003generalized], Chapter 0.
For a unitary right factor, the two forms of a singular value
decomposition are equivalent. -/
theorem mul_right_eq_left_mul_diagonal_iff_svd
    (A D : Matrix m n ℂ) (U : Matrix m m ℂ) (V : Matrix n n ℂ)
    (hV : V ∈ Matrix.unitaryGroup n ℂ) :
    A * V = U * D ↔ A = U * D * Vᴴ := by
  have hL : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hR : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  constructor
  · intro h
    rw [← h, Matrix.mul_assoc, hR, Matrix.mul_one]
  · intro h
    rw [h, Matrix.mul_assoc (U * D), hL, Matrix.mul_one]

/-- **Exercise 19** of [benIsrael2003generalized], Chapter 0. Similarity is
conjugation by an invertible matrix. -/
theorem isSimilar_iff (A B : Matrix n n ℂ) :
    A.IsSimilar B ↔ ∃ P : Matrix n n ℂ, IsUnit P ∧ B = P⁻¹ * A * P :=
  Iff.rfl

/-- **Exercise 25** of [benIsrael2003generalized], Chapter 0. Two matrices
are equivalent if invertible factors on both sides carry one to the other. -/
def equivalentMatrices [DecidableEq m] (A B : Matrix m n ℂ) : Prop :=
  ∃ (P : Matrix m m ℂ) (Q : Matrix n n ℂ), IsUnit P ∧ IsUnit Q ∧ B = P * A * Q

end Equivalences

/-- **Equations (37)–(38)** of [benIsrael2003generalized], Chapter 0.
The factors of a singular value decomposition are unitary, and their
rectangular diagonal matrix contains the singular values followed by zeros. -/
def isSVD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ V ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    A = U * (Matrix.rectDiagonal (fun i => (A.sortedSingularValues i : ℂ)) :
      Matrix (Fin m) (Fin n) ℂ) * Vᴴ

/-- A matrix has a singular value decomposition with its singular values
in descending order on the diagonal. -/
theorem exists_singularValueDecomposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ U V, isSVD A U V := by
  obtain ⟨U, hU, V, hV, h⟩ := A.exists_svd
  exact ⟨U, V, hU, hV, Matrix.eq_mul_mul_star_of_star_mul_mul_eq hU hV h⟩

/-- **Exercise 20** of [benIsrael2003generalized], Chapter 0. Every square
complex matrix is unitarily similar to an upper triangular matrix. -/
theorem exists_unitary_upperTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, IsRectUpperTriangular (Uᴴ * A * U) := by
  obtain ⟨U, hU, hTri, _⟩ := A.exists_unitary_conj_upperTriangular
  exact ⟨U, hU, fun i j hij => hTri (show j < i from hij)⟩

/-- **Equation (40)** of [benIsrael2003generalized], Chapter 0. Every
matrix admits a QR factorization with unitary $Q$ and upper triangular $R$. -/
theorem exists_qr_factorization {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ (Q : Matrix (Fin m) (Fin m) ℂ) (R : Matrix (Fin m) (Fin n) ℂ),
      Q ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ IsRectUpperTriangular R ∧ A = Q * R := by
  obtain ⟨Q, R, h⟩ := A.exists_isQR
  exact ⟨Q, R, h.mem_unitaryGroup, h.apply_eq_zero, h.mul_eq.symm⟩

section Convergence

open Filter
open scoped Topology Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Exercise 41** of [benIsrael2003generalized], Chapter 0. The spectral
radius is the supremum of the moduli of the eigenvalues. -/
noncomputable abbrev spectralRadius (A : Matrix n n ℂ) : ℝ :=
  (_root_.spectralRadius ℂ A).toReal

/-- **Equation (58)** of [benIsrael2003generalized], Chapter 0. The
spectral radius is the greatest modulus attained by an eigenvalue. -/
theorem spectralRadius_eq_max [Nonempty n] (A : Matrix n n ℂ) :
    IsGreatest ((fun c : ℂ => ‖c‖) '' spectrum ℂ A) (spectralRadius A) := by
  obtain ⟨c, hc, hρ, hmax⟩ := A.exists_norm_eq_spectralRadius (spectrum.nonempty A)
  have he : spectralRadius A = ‖c‖ := by simp [spectralRadius, hρ]
  exact ⟨⟨c, hc, he.symm⟩, fun a ⟨z, hz, ha⟩ => ha ▸ he.symm ▸ hmax z hz⟩

/-- **Equation (60)** of [benIsrael2003generalized], Chapter 0.
Taking powers commutes with the spectral radius. -/
theorem spectralRadius_pow [Nonempty n] (A : Matrix n n ℂ) (k : ℕ) :
    spectralRadius (A ^ k) = spectralRadius A ^ k := by
  rw [spectralRadius, _root_.spectralRadius_pow, ENNReal.toReal_pow]

/-- **Equation (61)** of [benIsrael2003generalized], Chapter 0.
The operator $2$-norm equals the square root of either Gram spectral radius. -/
theorem opNorm_eq_sqrt_gram_spectralRadius {m : Type*} [Fintype m]
    (A : Matrix m n ℂ) :
    ‖A‖ = Real.sqrt (spectralRadius (Aᴴ * A)) ∧
      ‖A‖ = Real.sqrt (spectralRadius (A * Aᴴ)) := by
  classical
  constructor
  · rw [spectralRadius, ← A.l2_opNorm_sq_eq_spectralRadius_conjTranspose_mul_self]
    simp [ENNReal.toReal_pow]
  · rw [spectralRadius, ← A.l2_opNorm_sq_eq_spectralRadius_self_mul_conjTranspose]
    simp [ENNReal.toReal_pow]

/-- **Equation (62)** of [benIsrael2003generalized], Chapter 0.
A Hermitian matrix has operator $2$-norm equal to its spectral radius. -/
theorem opNorm_eq_spectralRadius_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖A‖ = spectralRadius A := by
  rw [spectralRadius, hA.isSelfAdjoint.spectralRadius_eq_nnnorm]
  rfl

/-- **Exercise 45** of [benIsrael2003generalized], Chapter 0. A matrix
is convergent if its powers tend to zero. -/
def isConvergent (A : Matrix n n ℂ) : Prop :=
  Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0)

/-- **Exercise 45** of [benIsrael2003generalized], Chapter 0. The powers
converge to zero precisely when the spectral radius is below one. -/
theorem isConvergent_iff_spectralRadius_lt_one [Nonempty n] (A : Matrix n n ℂ) :
    isConvergent A ↔ spectralRadius A < 1 := by
  rw [isConvergent, ← spectralRadius_lt_one_iff_tendsto_pow, spectralRadius, ← ENNReal.toReal_one,
    ENNReal.toReal_lt_toReal (spectrum.spectralRadius_ne_top A) ENNReal.one_ne_top]

/-- **Equation (65)** of [benIsrael2003generalized], Chapter 0.
The powers tend to zero precisely when their Neumann series is summable. -/
theorem summable_pow_iff_isConvergent [Nonempty n] (A : Matrix n n ℂ) :
    Summable (fun k : ℕ => A ^ k) ↔ isConvergent A :=
  (summable_pow_iff_spectralRadius_lt_one A).trans (spectralRadius_lt_one_iff_tendsto_pow A)

/-- **Equation (65)** of [benIsrael2003generalized], Chapter 0.
The sum of powers of a convergent matrix is the inverse of $I-A$. -/
theorem hasSum_pow_inv_one_sub [Nonempty n] (A : Matrix n n ℂ) (hA : isConvergent A) :
    HasSum (fun k : ℕ => A ^ k) (1 - A)⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  exact hasSum_pow_inverse_one_sub_of_spectralRadius_lt_one
    ((spectralRadius_lt_one_iff_tendsto_pow A).mpr hA)

/-- **Equation (66)** of [benIsrael2003generalized], Chapter 0.
The alternating sum of powers of a convergent matrix is the inverse of $I+A$. -/
theorem hasSum_alternating_pow_inv_one_add [Nonempty n]
    (A : Matrix n n ℂ) (hA : isConvergent A) :
    HasSum (fun k : ℕ => ((-1 : ℂ) ^ k) • A ^ k) (1 + A)⁻¹ := by
  have hNeg : _root_.spectralRadius ℂ (-A) = _root_.spectralRadius ℂ A := by
    simpa using spectralRadius_smul (-1 : ℂ) A
  have h := (spectralRadius_lt_one_iff_tendsto_pow A).mpr hA
  have hConv := (spectralRadius_lt_one_iff_tendsto_pow (-A)).mp (hNeg ▸ h)
  convert hasSum_pow_inv_one_sub (-A) hConv using 1
  · funext k
    simpa only [neg_one_smul] using (smul_pow (-1 : ℂ) A k).symm
  · rw [sub_neg_eq_add]

end Convergence

end BenIsraelGreville.Chapter00
