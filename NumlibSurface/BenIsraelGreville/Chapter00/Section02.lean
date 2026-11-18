/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Matrix.SingularValues
import Numlib.Eigen.Normal
import Numlib.LinearAlgebra.Matrix.Charpoly
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Jordan
import Numlib.LinearAlgebra.Matrix.Triangular
import Numlib.LinearAlgebra.Matrix.LeastSquares
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.Analysis.Normed.Algebra.SpectralRadius
import Numlib.LinearAlgebra.Matrix.Schur
import Numlib.LinearAlgebra.Matrix.Similar
import NumlibSurface.BenIsraelGreville.Chapter00.Section01
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Polynomial.DegreeLT
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
* **Exercise 17** (correction). Matrix rows index the output basis and
  columns index the input basis.
* **Exercise 29** (correction). The rotation has a one-dimensional
  eigenspace for $i$ and has no nonzero real eigenvector.
* **Exercise 31** (correction). The partial-sum basis starts with the
  constant polynomial $1$. The displayed left-acting array is transposed
  in column coordinates.
* **Exercise 36** (correction). On the closed unit ball the maximized
  expression is the norm of the image, which is defined at zero.
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

section CoordinatesExercises

open Matrix Module
open scoped InnerProductSpace

section CoordinateChanges

variable {K E F G i j k : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [AddCommGroup G] [Module K G]
  [Fintype i] [Fintype j] [Fintype k] [DecidableEq i] [DecidableEq j] [DecidableEq k]

/-- **Exercise 14** of [benIsrael2003generalized], Chapter 0. The range and
zero fiber are the carriers of subspaces of the codomain and domain. -/
theorem range_ker_submodule (T : E →ₗ[K] F) :
    (↑T.range : Set F) = Set.range T ∧ (↑T.ker : Set E) = T ⁻¹' {0} := by
  exact ⟨rfl, Set.ext fun _ => LinearMap.mem_ker⟩

omit [DecidableEq k] in
/-- **Exercise 26** of [benIsrael2003generalized], Chapter 0. Composition is
linear, and its matrix is the product in compatible bases. -/
theorem toMatrix_comp (e : Basis i K E) (f : Basis j K F) (g : Basis k K G)
    (A : F →ₗ[K] G) (B : E →ₗ[K] F) :
    (A.comp B).toMatrix e g = A.toMatrix f g * B.toMatrix e f :=
  LinearMap.toMatrix_comp e f g A B

/-- **Exercise 27** of [benIsrael2003generalized], Chapter 0. The identity
transformation is represented by the identity matrix in any common basis. -/
theorem toMatrix_id (e : Basis i K E) : (LinearMap.id : E →ₗ[K] E).toMatrix e e = 1 :=
  LinearMap.toMatrix_id e

/-- **Exercise 28** of [benIsrael2003generalized], Chapter 0. The inverse
transformation is represented by the inverse matrix in the reversed bases. -/
theorem toMatrix_inverse (e : Basis i K E) (f : Basis i K F) (A : E ≃ₗ[K] F) :
    A.symm.toLinearMap.toMatrix f e = (A.toLinearMap.toMatrix e f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← LinearMap.toMatrix_comp, LinearEquiv.comp_symm, LinearMap.toMatrix_id]

/-- **Exercise 18**, Equations (43)–(45), of [benIsrael2003generalized],
Chapter 0. The new basis determines one nonsingular coordinate matrix,
and its inverse expresses the old basis in the new one. -/
theorem existsUnique_changeOfBasis (e e' : Basis i K E) :
    ∃! S : Matrix i i K,
      IsUnit S ∧ (∀ j, e' j = ∑ i, S i j • e i) ∧
        ∀ j, e j = ∑ i, S⁻¹ i j • e' i := by
  have hS : e.toMatrix e' * e'.toMatrix e = 1 := e.toMatrix_mul_toMatrix_flip e'
  refine ⟨e.toMatrix e', ⟨isUnit_iff_exists_inv.mpr ⟨_, hS⟩, ?_, ?_⟩, ?_⟩
  · intro j
    exact (e.sum_toMatrix_smul_self e' j).symm
  · intro j
    rw [Matrix.inv_eq_right_inv hS]
    exact (e'.sum_toMatrix_smul_self e j).symm
  · rintro S ⟨-, h, -⟩
    ext i j
    have he := congrArg (fun x => e.repr x i) (h j)
    simpa [Basis.toMatrix_apply, Finsupp.single_apply, eq_comm] using he.symm

/-- **Exercise 24**, Equation (48), of [benIsrael2003generalized], Chapter 0.
The new representing matrix is obtained by the inverse output coordinate
change on the left and the input coordinate change on the right. -/
theorem toMatrix_changeOfBases (e e' : Basis i K E) (f f' : Basis j K F) (A : E →ₗ[K] F) :
    A.toMatrix e' f' = (f.toMatrix f')⁻¹ * A.toMatrix e f * e.toMatrix e' := by
  rw [Matrix.inv_eq_right_inv (f.toMatrix_mul_toMatrix_flip f')]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e' e f' f A).symm

private theorem exists_basis_change_eq (e : Basis i K E)
    (S : Matrix i i K) (hS : IsUnit S) : ∃ e' : Basis i K E, e.toMatrix e' = S := by
  let u := Matrix.toLinearEquiv e S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  refine ⟨e.map u, ?_⟩
  have he : (e.map u : i → E) = u.toLinearMap ∘ e := by
    funext j
    simp
  rw [he, ← LinearMap.toMatrix_eq_basisToMatrix]
  exact LinearMap.toMatrix_toLin e e S

end CoordinateChanges

section OrthonormalCoordinates

variable {E F i j : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [Fintype i] [Fintype j] [DecidableEq i] [DecidableEq j]

omit [DecidableEq j] in
/-- **Exercise 16(a)** of [benIsrael2003generalized], Chapter 0. The entry
is the inner product with the output basis vector in the conjugate-linear
slot, consistent with the source's opposite inner-product convention. -/
theorem toMatrix_orthonormalBasis_apply (u : OrthonormalBasis i ℂ E)
    (v : OrthonormalBasis j ℂ F) (A : E →ₗ[ℂ] F) (row : j) (col : i) :
    A.toMatrix u.toBasis v.toBasis row col = ⟪v row, A (u col)⟫_ℂ := by
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  rfl

/-- **Exercise 16(b)** of [benIsrael2003generalized], Chapter 0. The adjoint
is represented by the conjugate transpose in the reversed orthonormal bases. -/
theorem adjoint_toMatrix_orthonormalBasis [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (u : OrthonormalBasis i ℂ E) (v : OrthonormalBasis j ℂ F) (A : E →ₗ[ℂ] F) :
    A.adjoint.toMatrix v.toBasis u.toBasis = (A.toMatrix u.toBasis v.toBasis)ᴴ :=
  LinearMap.toMatrix_adjoint u v A

private theorem exists_orthonormalBasis_change_eq (e : OrthonormalBasis i ℂ E)
    (S : Matrix i i ℂ) (hS : S ∈ Matrix.unitaryGroup i ℂ) :
    ∃ e' : OrthonormalBasis i ℂ E, e.toBasis.toMatrix e'.toBasis = S := by
  let q := (EuclideanSpace.basisFun i ℂ).map
    ((Matrix.unitaryLinearIsometryEquiv hS).trans e.repr.symm)
  refine ⟨q, ?_⟩
  ext a b
  rw [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  change (e.repr (q b)) a = _
  simp only [q, OrthonormalBasis.map_apply, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, Matrix.unitaryLinearIsometryEquiv_apply]
  change (WithLp.ofLp (toEuclideanLin S (EuclideanSpace.basisFun i ℂ b))) a = _
  rw [Matrix.ofLp_toEuclideanLin, EuclideanSpace.basisFun_apply, PiLp.ofLp_single,
    Matrix.mulVec_single_one]
  rfl

/-- **Exercise 17**, Equation (42), of [benIsrael2003generalized], Chapter 0.
The rectangular diagonal representation has the output dimension as its
row count, and the positive singular values come first. -/
theorem exists_orthonormalBasis_toMatrix_rectDiagonal {m n : ℕ}
    (u : OrthonormalBasis (Fin n) ℂ E) (v : OrthonormalBasis (Fin m) ℂ F) (A : E →ₗ[ℂ] F) :
    let M := A.toMatrix u.toBasis v.toBasis
    ∃ u' : OrthonormalBasis (Fin n) ℂ E, ∃ v' : OrthonormalBasis (Fin m) ℂ F,
      A.toMatrix u'.toBasis v'.toBasis =
        (Matrix.rectDiagonal (fun k => (M.sortedSingularValues k : ℂ)) :
          Matrix (Fin m) (Fin n) ℂ) ∧
      Antitone M.sortedSingularValues ∧
      (∀ k < M.rank, 0 < M.sortedSingularValues k) ∧
      ∀ k, M.rank ≤ k → M.sortedSingularValues k = 0 := by
  intro M
  obtain ⟨S, hS, T, hT, he⟩ := M.exists_svd
  obtain ⟨v', hv⟩ := exists_orthonormalBasis_change_eq v S hS
  obtain ⟨u', hu⟩ := exists_orthonormalBasis_change_eq u T hT
  refine ⟨u', v', ?_, M.sortedSingularValues_antitone, ?_, ?_⟩
  · rw [toMatrix_changeOfBases, hv, hu, ← (mem_unitary_iff S).mp hS |>.2]
    exact he
  · intro k hk
    exact lt_of_le_of_ne (M.sortedSingularValues_nonneg k)
      (Ne.symm ((M.sortedSingularValues_eq_zero_iff_rank_le k).not.mpr (not_le.mpr hk)))
  · intro k hk
    exact (M.sortedSingularValues_eq_zero_iff_rank_le k).mpr hk

end OrthonormalCoordinates

section MatrixEquivalence

variable {i j : Type*} [Fintype i] [Fintype j] [DecidableEq i] [DecidableEq j]

/-- **Exercise 25**, Equation (49), of [benIsrael2003generalized], Chapter 0.
Equivalent matrices describe one linear map using two pairs of bases. -/
theorem equivalentMatrices_iff_toMatrix (M N : Matrix j i ℂ) :
    equivalentMatrices M N ↔
      ∃ (A : EuclideanSpace ℂ i →ₗ[ℂ] EuclideanSpace ℂ j)
        (u u' : Basis i ℂ (EuclideanSpace ℂ i)) (v v' : Basis j ℂ (EuclideanSpace ℂ j)),
        A.toMatrix u v = M ∧ A.toMatrix u' v' = N := by
  constructor
  · rintro ⟨P, Q, hP, hQ, hN⟩
    let u := (EuclideanSpace.basisFun i ℂ).toBasis
    let v := (EuclideanSpace.basisFun j ℂ).toBasis
    let A := Matrix.toLin u v M
    obtain ⟨u', hu⟩ := exists_basis_change_eq u Q hQ
    obtain ⟨v', hv⟩ := exists_basis_change_eq v P⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hP)
    have he : A.toMatrix u v = M := LinearMap.toMatrix_toLin _ _ _
    refine ⟨A, u, u', v, v', he, ?_⟩
    let := hP.invertible
    rw [toMatrix_changeOfBases, hu, hv, Matrix.inv_inv_of_invertible, he, ← hN]
  · rintro ⟨A, u, u', v, v', hM, hN⟩
    let := v.invertibleToMatrix v'
    let := u.invertibleToMatrix u'
    refine ⟨(v.toMatrix v')⁻¹, u.toMatrix u',
      Matrix.isUnit_nonsing_inv_iff.mpr (isUnit_of_invertible _), isUnit_of_invertible _, ?_⟩
    rw [← hN, toMatrix_changeOfBases, hM]

/-- **Exercise 19**, Equation (46), of [benIsrael2003generalized], Chapter 0.
Similar matrices represent one endomorphism in two bases. -/
theorem isSimilar_iff_toMatrix (M N : Matrix i i ℂ) :
    M.IsSimilar N ↔
      ∃ (A : EuclideanSpace ℂ i →ₗ[ℂ] EuclideanSpace ℂ i)
        (u v : Basis i ℂ (EuclideanSpace ℂ i)), A.toMatrix u u = M ∧ A.toMatrix v v = N := by
  rw [isSimilar_iff]
  constructor
  · rintro ⟨S, hS, hN⟩
    let u := (EuclideanSpace.basisFun i ℂ).toBasis
    let A := Matrix.toLin u u M
    obtain ⟨v, hv⟩ := exists_basis_change_eq u S hS
    have he : A.toMatrix u u = M := LinearMap.toMatrix_toLin _ _ _
    refine ⟨A, u, v, he, ?_⟩
    rw [toMatrix_changeOfBases, hv, he, ← hN]
  · rintro ⟨A, u, v, hM, hN⟩
    let := u.invertibleToMatrix v
    exact ⟨u.toMatrix v, isUnit_of_invertible _, by
      rw [← hN, toMatrix_changeOfBases, hM]⟩

/-- Orthogonal-coordinate version of **Exercise 25**, for unitary changes. -/
theorem unitarilyEquivalent_iff_toMatrix (M N : Matrix j i ℂ) :
    (∃ S ∈ Matrix.unitaryGroup j ℂ, ∃ T ∈ Matrix.unitaryGroup i ℂ, N = Sᴴ * M * T) ↔
      ∃ (A : EuclideanSpace ℂ i →ₗ[ℂ] EuclideanSpace ℂ j)
        (u u' : OrthonormalBasis i ℂ (EuclideanSpace ℂ i))
        (v v' : OrthonormalBasis j ℂ (EuclideanSpace ℂ j)),
        A.toMatrix u.toBasis v.toBasis = M ∧ A.toMatrix u'.toBasis v'.toBasis = N := by
  constructor
  · rintro ⟨S, hS, T, hT, hN⟩
    let u := EuclideanSpace.basisFun i ℂ
    let v := EuclideanSpace.basisFun j ℂ
    let A := Matrix.toLin u.toBasis v.toBasis M
    obtain ⟨u', hu⟩ := exists_orthonormalBasis_change_eq u T hT
    obtain ⟨v', hv⟩ := exists_orthonormalBasis_change_eq v S hS
    have he : A.toMatrix u.toBasis v.toBasis = M := LinearMap.toMatrix_toLin _ _ _
    refine ⟨A, u, u', v, v', he, ?_⟩
    rw [toMatrix_changeOfBases, hv, hu, ← (mem_unitary_iff S).mp hS |>.2, he, ← hN]
  · rintro ⟨A, u, u', v, v', hM, hN⟩
    have hS : v.toBasis.toMatrix v'.toBasis ∈ Matrix.unitaryGroup j ℂ :=
      v.toMatrix_orthonormalBasis_mem_unitary v'
    have hT : u.toBasis.toMatrix u'.toBasis ∈ Matrix.unitaryGroup i ℂ :=
      u.toMatrix_orthonormalBasis_mem_unitary u'
    refine ⟨v.toBasis.toMatrix v'.toBasis, hS, u.toBasis.toMatrix u'.toBasis, hT, ?_⟩
    rw [← hN, toMatrix_changeOfBases u.toBasis u'.toBasis v.toBasis v'.toBasis A,
      ← (mem_unitary_iff _).mp hS |>.2, hM]

/-- Orthonormal-coordinate version of **Exercise 19**, with one change
of basis on both sides. -/
theorem isUnitarilySimilar_iff_toMatrix (M N : Matrix i i ℂ) :
    M.IsUnitarilySimilar N ↔
      ∃ (A : EuclideanSpace ℂ i →ₗ[ℂ] EuclideanSpace ℂ i)
        (u v : OrthonormalBasis i ℂ (EuclideanSpace ℂ i)),
        A.toMatrix u.toBasis u.toBasis = M ∧ A.toMatrix v.toBasis v.toBasis = N := by
  constructor
  · rintro ⟨S, hS, hN⟩
    let u := EuclideanSpace.basisFun i ℂ
    let A := Matrix.toLin u.toBasis u.toBasis M
    obtain ⟨v, hv⟩ := exists_orthonormalBasis_change_eq u S hS
    have he : A.toMatrix u.toBasis u.toBasis = M := LinearMap.toMatrix_toLin _ _ _
    refine ⟨A, u, v, he, ?_⟩
    rw [toMatrix_changeOfBases, hv, ← (mem_unitary_iff S).mp hS |>.2, he]
    simpa only [Matrix.star_eq_conjTranspose] using hN.symm
  · rintro ⟨A, u, v, hM, hN⟩
    have hu : u.toBasis.toMatrix v.toBasis ∈ Matrix.unitaryGroup i ℂ :=
      u.toMatrix_orthonormalBasis_mem_unitary v
    refine ⟨u.toBasis.toMatrix v.toBasis, hu, ?_⟩
    rw [← hN, toMatrix_changeOfBases u.toBasis v.toBasis u.toBasis v.toBasis A,
      ← (mem_unitary_iff _).mp hu |>.2, hM, Matrix.star_eq_conjTranspose]

end MatrixEquivalence

end CoordinatesExercises

section PolynomialsExercises

open Matrix Module Polynomial
open scoped Polynomial

/-- **Exercise 15**, Equation (41), of [benIsrael2003generalized], Chapter 0.
The subspace of real polynomials of degree at most $n$. -/
noncomputable abbrev polynomialDegreeSpace (n : ℕ) : Submodule ℝ ℝ[X] :=
  Polynomial.degreeLT ℝ (n + 1)

/-- Membership in the degree-bounded subspace is the polynomial degree bound. -/
@[simp]
theorem mem_polynomialDegreeSpace {p : ℝ[X]} {n : ℕ} :
    p ∈ polynomialDegreeSpace n ↔ p.degree ≤ n := by
  change p ∈ Polynomial.degreeLT ℝ (n + 1) ↔ _
  rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE]

/-- The ordered monomial basis of the degree-bounded polynomial space. -/
noncomputable abbrev polynomialMonomialBasis (n : ℕ) :
    Basis (Fin (n + 1)) ℝ (polynomialDegreeSpace n) :=
  Polynomial.degreeLT.basis ℝ (n + 1)

/-- **Exercise 15(a)–(b)** of [benIsrael2003generalized], Chapter 0.
The space has dimension $n+1$, with monomial basis and coefficient
coordinates. -/
theorem polynomialDegreeSpace_basis (n : ℕ) :
    Module.finrank ℝ (polynomialDegreeSpace n) = n + 1 ∧
      (∀ j, (polynomialMonomialBasis n j : ℝ[X]) = X ^ (j : ℕ)) ∧
      ∀ (p : polynomialDegreeSpace n) j, (polynomialMonomialBasis n).repr p j = p.val.coeff j := by
  exact ⟨(Module.finrank_eq_card_basis (polynomialMonomialBasis n)).trans (Fintype.card_fin _),
    fun j => Polynomial.degreeLT.basis_val j, fun p j => Polynomial.degreeLT.basis_repr j p⟩

/-- **Exercise 15(a)** of [benIsrael2003generalized], Chapter 0.
Addition and scalar multiplication act coefficientwise in the bounded
polynomial space. -/
theorem polynomialDegreeSpace_coeff_arithmetic (n : ℕ) (p q : polynomialDegreeSpace n)
    (c : ℝ) (k : ℕ) :
    ((p + q : polynomialDegreeSpace n) : ℝ[X]).coeff k = p.val.coeff k + q.val.coeff k ∧
      ((c • p : polynomialDegreeSpace n) : ℝ[X]).coeff k = c * p.val.coeff k := by
  exact ⟨Polynomial.coeff_add _ _ _, Polynomial.coeff_smul _ _ _⟩

/-- The polynomial derivative on the space with bounded degree. -/
noncomputable def polynomialBoundedDerivative (n : ℕ) :
    polynomialDegreeSpace (n + 1) →ₗ[ℝ] polynomialDegreeSpace n :=
  (Polynomial.derivative.comp (polynomialDegreeSpace (n + 1)).subtype).codRestrict
    (polynomialDegreeSpace n) fun p => by
      have hp : (p : ℝ[X]).degree < ↑(n + 1 + 1) := Polynomial.mem_degreeLT.mp p.prop
      apply Polynomial.mem_degreeLT.mpr
      rw [Polynomial.degree_lt_iff_coeff_zero] at hp ⊢
      intro k hk
      change (Polynomial.derivative p.val).coeff k = 0
      rw [Polynomial.coeff_derivative, hp (k + 1) (by omega), zero_mul]

/-- Coercing the bounded derivative gives the ordinary polynomial derivative. -/
@[simp]
theorem polynomialBoundedDerivative_coe (n : ℕ) (p : polynomialDegreeSpace (n + 1)) :
    (polynomialBoundedDerivative n p : ℝ[X]) = Polynomial.derivative p.val :=
  rfl

private noncomputable def integratedCoefficients (n : ℕ) :
    polynomialDegreeSpace n →ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun p := Fin.cases 0 (fun j : Fin (n + 1) => p.val.coeff j / ((j : ℝ) + 1))
  map_add' p q := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · simp [add_div]
  map_smul' c p := by
    ext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · simp [smul_eq_mul, mul_div_assoc]

/-- The polynomial antiderivative whose constant coefficient is zero.
Each source coefficient is divided by the new exponent. -/
noncomputable def polynomialBoundedIntegral (n : ℕ) :
    polynomialDegreeSpace n →ₗ[ℝ] polynomialDegreeSpace (n + 1) :=
  (Polynomial.degreeLTEquiv ℝ (n + 2)).symm.toLinearMap.comp (integratedCoefficients n)

private theorem integratedCoefficients_eq (n : ℕ) (p : polynomialDegreeSpace n)
    (j : Fin (n + 2)) :
    (polynomialBoundedIntegral n p).val.coeff j = integratedCoefficients n p j :=
  congrFun ((Polynomial.degreeLTEquiv ℝ (n + 2)).apply_symm_apply
    (integratedCoefficients n p)) j

/-- The bounded antiderivative has zero constant coefficient. -/
@[simp]
theorem coeff_polynomialBoundedIntegral_zero (n : ℕ) (p : polynomialDegreeSpace n) :
    (polynomialBoundedIntegral n p).val.coeff 0 = 0 := by
  simpa [integratedCoefficients] using integratedCoefficients_eq n p 0

/-- The antiderivative divides the previous coefficient by the new degree. -/
@[simp]
theorem coeff_polynomialBoundedIntegral_succ (n : ℕ) (p : polynomialDegreeSpace n)
    (k : ℕ) :
    (polynomialBoundedIntegral n p).val.coeff (k + 1) = p.val.coeff k / ((k : ℝ) + 1) := by
  by_cases hk : k < n + 1
  · simpa [integratedCoefficients] using integratedCoefficients_eq n p (Fin.succ ⟨k, hk⟩)
  · have hp := (Polynomial.degree_lt_iff_coeff_zero _ _).mp (Polynomial.mem_degreeLT.mp p.prop)
    have hi := (Polynomial.degree_lt_iff_coeff_zero _ _).mp
      (Polynomial.mem_degreeLT.mp (polynomialBoundedIntegral n p).prop)
    rw [hi _ (by omega), hp _ (by omega), zero_div]

private theorem boundedDerivative_integral (n : ℕ) (p : polynomialDegreeSpace n) :
    polynomialBoundedDerivative n (polynomialBoundedIntegral n p) = p := by
  apply Subtype.ext
  ext k
  rw [polynomialBoundedDerivative_coe, Polynomial.coeff_derivative,
    coeff_polynomialBoundedIntegral_succ]
  exact div_mul_cancel₀ _ (by positivity)

private theorem boundedIntegral_derivative (n : ℕ) (p : polynomialDegreeSpace (n + 1)) :
    (polynomialBoundedIntegral n (polynomialBoundedDerivative n p) : ℝ[X]) =
      p.val - Polynomial.C (p.val.coeff 0) := by
  ext k
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_polynomialBoundedIntegral_succ, polynomialBoundedDerivative_coe,
      Polynomial.coeff_derivative, Polynomial.coeff_sub, Polynomial.coeff_C_succ, sub_zero]
    exact mul_div_cancel_right₀ (p.val.coeff (k + 1)) (by positivity : (k : ℝ) + 1 ≠ 0)

private theorem boundedDerivative_matrix_entries (n : ℕ) (i : Fin (n + 1)) (j : Fin (n + 2)) :
    (polynomialBoundedDerivative n).toMatrix (polynomialMonomialBasis (n + 1))
        (polynomialMonomialBasis n) i j =
      if (j : ℕ) = (i : ℕ) + 1 then (i : ℝ) + 1 else 0 := by
  simp [LinearMap.toMatrix_apply, Polynomial.coeff_derivative, Polynomial.coeff_X_pow, eq_comm]

private theorem boundedIntegral_matrix_entries (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (polynomialBoundedIntegral n).toMatrix (polynomialMonomialBasis n)
        (polynomialMonomialBasis (n + 1)) i j =
      if (i : ℕ) = (j : ℕ) + 1 then ((j : ℝ) + 1)⁻¹ else 0 := by
  refine Fin.cases ?_ (fun l => ?_) i
  · simp [LinearMap.toMatrix_apply]
  · simp only [LinearMap.toMatrix_apply, Polynomial.degreeLT.basis_repr, Fin.val_succ,
      coeff_polynomialBoundedIntegral_succ, Polynomial.degreeLT.basis_val, Polynomial.coeff_X_pow,
      Nat.add_right_cancel_iff]
    by_cases h : (l : ℕ) = (j : ℕ)
    · simp [h, one_div]
    · simp [h]

/-- **Exercise 15(b)** of [benIsrael2003generalized], Chapter 0.
The derivative is onto, its kernel consists of the constants, and its
monomial matrix has superdiagonal $1,2,\dots,n+1$. -/
theorem polynomialDerivative_toMatrix (n : ℕ) :
    Function.Surjective (polynomialBoundedDerivative n) ∧
      (∀ p : polynomialDegreeSpace (n + 1),
        p ∈ (polynomialBoundedDerivative n).ker ↔ ∃ c : ℝ, p.val = Polynomial.C c) ∧
      ∀ i j, (polynomialBoundedDerivative n).toMatrix (polynomialMonomialBasis (n + 1))
          (polynomialMonomialBasis n) i j =
        if (j : ℕ) = (i : ℕ) + 1 then (i : ℝ) + 1 else 0 := by
  refine ⟨fun p => ⟨_, boundedDerivative_integral n p⟩, ?_, boundedDerivative_matrix_entries n⟩
  intro p
  rw [LinearMap.mem_ker]
  constructor
  · intro hp
    refine ⟨p.val.coeff 0, ?_⟩
    have h := boundedIntegral_derivative n p
    rw [hp, map_zero, Submodule.coe_zero] at h
    exact sub_eq_zero.mp h.symm
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    rw [polynomialBoundedDerivative_coe, hc, Polynomial.derivative_C, Submodule.coe_zero]

/-- **Exercise 15(c)** of [benIsrael2003generalized], Chapter 0.
Integration with zero constant is injective, has the subspace of
zero-constant polynomials as range, and is represented by the reciprocal
subdiagonal in monomial coordinates. -/
theorem polynomialIntegral_toMatrix (n : ℕ) :
    Function.Injective (polynomialBoundedIntegral n) ∧
      (∀ p : polynomialDegreeSpace (n + 1),
        p ∈ (polynomialBoundedIntegral n).range ↔ p.val.coeff 0 = 0) ∧
      ∀ i j, (polynomialBoundedIntegral n).toMatrix (polynomialMonomialBasis n)
          (polynomialMonomialBasis (n + 1)) i j =
        if (i : ℕ) = (j : ℕ) + 1 then ((j : ℝ) + 1)⁻¹ else 0 := by
  refine ⟨(show Function.LeftInverse (polynomialBoundedDerivative n)
    (polynomialBoundedIntegral n) from boundedDerivative_integral n).injective,
    ?_, boundedIntegral_matrix_entries n⟩
  intro p
  constructor
  · rintro ⟨q, rfl⟩
    exact coeff_polynomialBoundedIntegral_zero n q
  · intro hp
    refine ⟨polynomialBoundedDerivative n p, Subtype.ext ?_⟩
    rw [boundedIntegral_derivative, hp, map_zero, sub_zero]

/-- **Exercise 15(d)** of [benIsrael2003generalized], Chapter 0.
Differentiating after integration gives the identity matrix. The reverse
product preserves the positive-degree coefficients and sets the constant
coefficient to zero. -/
theorem polynomialDerivative_integral_compositions (n : ℕ) :
    let U := polynomialMonomialBasis n
    let V := polynomialMonomialBasis (n + 1)
    let D := (polynomialBoundedDerivative n).toMatrix V U
    let I := (polynomialBoundedIntegral n).toMatrix U V
    D * I = 1 ∧
      I * D = diagonal (fun i : Fin (n + 2) => if (i : ℕ) = 0 then 0 else 1) ∧
      ∀ p : polynomialDegreeSpace (n + 1),
        (polynomialBoundedIntegral n (polynomialBoundedDerivative n p) : ℝ[X]) =
          p.val - Polynomial.C (p.val.coeff 0) := by
  intro U V D I
  refine ⟨?_, ?_, boundedIntegral_derivative n⟩
  · change (polynomialBoundedDerivative n).toMatrix V U *
      (polynomialBoundedIntegral n).toMatrix U V = 1
    rw [← LinearMap.toMatrix_comp, show (polynomialBoundedDerivative n).comp
      (polynomialBoundedIntegral n) = LinearMap.id from
      LinearMap.ext (boundedDerivative_integral n), LinearMap.toMatrix_id]
  · change (polynomialBoundedIntegral n).toMatrix U V *
      (polynomialBoundedDerivative n).toMatrix V U = _
    rw [← LinearMap.toMatrix_comp]
    ext i j
    rw [LinearMap.toMatrix_apply]
    change (polynomialBoundedIntegral n (polynomialBoundedDerivative n (V j))).val.coeff i = _
    rw [boundedIntegral_derivative, Polynomial.coeff_sub, Polynomial.coeff_C]
    simp only [V, Polynomial.degreeLT.basis_val, Polynomial.coeff_X_pow]
    by_cases hi : i = 0
    · subst i
      simp [Matrix.diagonal_apply]
      split_ifs with h <;> simp [h]
    · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      by_cases hij : i = j
      · subst j
        simp [hi, hi']
      · have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
        simp [hi', hval, hij]

section PartialSums

/-- The source's partial sums as columns in the monomial basis. Its transpose
is the coefficient array acting on the vertical list of monomials in the book. -/
def polynomialPartialSumChange (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of (fun i j => if i ≤ j then 1 else 0)

private theorem isUnit_polynomialPartialSumChange_det (n : ℕ) :
    IsUnit (polynomialPartialSumChange n).det := by
  have h : (polynomialPartialSumChange n).IsUpperTriangular := by
    intro i j hij
    exact ite_eq_right (not_le.mpr hij)
  rw [Matrix.det_of_isUpperTriangular h]
  simp [polynomialPartialSumChange]

/-- The ordered basis $1,1+X,\ldots,1+X+\cdots+X^n$. -/
noncomputable def polynomialPartialSumBasis (n : ℕ) :
    Basis (Fin (n + 1)) ℝ (polynomialDegreeSpace n) :=
  (polynomialMonomialBasis n).map
    (Matrix.toLinearEquiv (polynomialMonomialBasis n) (polynomialPartialSumChange n)
      (isUnit_polynomialPartialSumChange_det n))

private theorem toMatrix_polynomialPartialSumBasis (n : ℕ) :
    (polynomialMonomialBasis n).toMatrix (polynomialPartialSumBasis n) =
      polynomialPartialSumChange n := by
  let b := polynomialMonomialBasis n
  let S := Matrix.toLinearEquiv b (polynomialPartialSumChange n)
    (isUnit_polynomialPartialSumChange_det n)
  have he : (b.map S : Fin (n + 1) → polynomialDegreeSpace n) = S.toLinearMap ∘ b := by
    funext j
    simp
  change b.toMatrix (b.map S) = _
  rw [he, ← LinearMap.toMatrix_eq_basisToMatrix]
  exact LinearMap.toMatrix_toLin b b _

private theorem coeff_polynomialPartialSumBasis (n : ℕ) (j : Fin (n + 1)) (k : ℕ) :
    (polynomialPartialSumBasis n j : ℝ[X]).coeff k = if k ≤ (j : ℕ) then 1 else 0 := by
  by_cases hk : k < n + 1
  · let i : Fin (n + 1) := ⟨k, hk⟩
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => M i j)
      (toMatrix_polynomialPartialSumBasis n)
    exact h
  · rw [(Polynomial.degree_lt_iff_coeff_zero _ _).mp
      (Polynomial.mem_degreeLT.mp (polynomialPartialSumBasis n j).prop) k (by omega)]
    exact (ite_eq_right (by omega : ¬ k ≤ (j : ℕ))).symm

/-- The coordinates in the partial-sum basis are successive differences of
the monomial coefficients, with the coefficient beyond the degree bound zero. -/
theorem polynomialPartialSumBasis_repr (n : ℕ) (p : polynomialDegreeSpace n)
    (i : Fin (n + 1)) :
    (polynomialPartialSumBasis n).repr p i = p.val.coeff i - p.val.coeff ((i : ℕ) + 1) := by
  let b := polynomialPartialSumBasis n
  let D := (Polynomial.lcoeff ℝ i - Polynomial.lcoeff ℝ ((i : ℕ) + 1)).comp
    (polynomialDegreeSpace n).subtype
  have h : b.coord i = D := by
    apply b.ext
    intro j
    change b.repr (b j) i = (b j).val.coeff i - (b j).val.coeff ((i : ℕ) + 1)
    rw [Basis.repr_self, Finsupp.single_apply, coeff_polynomialPartialSumBasis,
      coeff_polynomialPartialSumBasis]
    by_cases hij : i = j
    · subst j
      simp
    · by_cases hlt : i < j
      · have hij' : (i : ℕ) + 1 ≤ (j : ℕ) := hlt
        simp [Ne.symm hij, (Nat.le_succ _).trans hij', hij']
      · have hji : ¬ (i : ℕ) ≤ (j : ℕ) := by
          exact fun hle => hij (le_antisymm hle (not_lt.mp hlt))
        simp [Ne.symm hij, hji, show ¬ (i : ℕ) + 1 ≤ (j : ℕ) by omega]
  exact LinearMap.congr_fun h p

/-- **Exercise 31(a)** of [benIsrael2003generalized], Chapter 0. The basis
includes the constant partial sum and has the stated triangular change matrix. -/
theorem polynomial_partialSum_basis (n : ℕ) :
    (∀ j, (polynomialPartialSumBasis n j : ℝ[X]) =
      ∑ k ∈ Finset.range ((j : ℕ) + 1), (X : ℝ[X]) ^ k) ∧
      (polynomialMonomialBasis n).toMatrix (polynomialPartialSumBasis n) =
        polynomialPartialSumChange n := by
  refine ⟨?_, toMatrix_polynomialPartialSumBasis n⟩
  intro j
  ext k
  rw [coeff_polynomialPartialSumBasis, Polynomial.finsetSum_coeff]
  simp [Polynomial.coeff_X_pow, Finset.mem_range]

private theorem toMatrix_polynomialPartialSum_change {a b : ℕ}
    (f : polynomialDegreeSpace a →ₗ[ℝ] polynomialDegreeSpace b) :
    f.toMatrix (polynomialPartialSumBasis a) (polynomialPartialSumBasis b) =
      (polynomialPartialSumChange b)⁻¹ *
        f.toMatrix (polynomialMonomialBasis a) (polynomialMonomialBasis b) *
        polynomialPartialSumChange a := by
  rw [← toMatrix_polynomialPartialSumBasis a, ← toMatrix_polynomialPartialSumBasis b,
    Matrix.inv_eq_right_inv
      ((polynomialMonomialBasis b).toMatrix_mul_toMatrix_flip (polynomialPartialSumBasis b))]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (polynomialPartialSumBasis a)
    (polynomialMonomialBasis a) (polynomialPartialSumBasis b) (polynomialMonomialBasis b) f).symm

/-- **Exercise 31(b)** of [benIsrael2003generalized], Chapter 0. The entries
of differentiation in the partial-sum bases are successive differences,
and the matrices obey Equation (48). -/
theorem polynomialDerivative_toMatrix_partialSum (n : ℕ) :
    let D := (polynomialBoundedDerivative n).toMatrix (polynomialPartialSumBasis (n + 1))
      (polynomialPartialSumBasis n)
    (∀ i j, D i j =
      (if (i : ℕ) + 1 ≤ (j : ℕ) then (i : ℝ) + 1 else 0) -
      (if (i : ℕ) + 2 ≤ (j : ℕ) then (i : ℝ) + 2 else 0)) ∧
      D = (polynomialPartialSumChange n)⁻¹ *
        (polynomialBoundedDerivative n).toMatrix (polynomialMonomialBasis (n + 1))
          (polynomialMonomialBasis n) * polynomialPartialSumChange (n + 1) := by
  refine ⟨?_, toMatrix_polynomialPartialSum_change _⟩
  intro i j
  rw [LinearMap.toMatrix_apply, polynomialPartialSumBasis_repr]
  simp only [polynomialBoundedDerivative_coe, Polynomial.coeff_derivative,
    coeff_polynomialPartialSumBasis]
  push_cast
  have h₁ : (i : ℕ) + 1 + 1 = (i : ℕ) + 2 := by omega
  rw [h₁]
  split_ifs <;> ring

private theorem coeff_boundedIntegral_partialSum (n : ℕ) (j : Fin (n + 1)) (k : ℕ) :
    (polynomialBoundedIntegral n (polynomialPartialSumBasis n j)).val.coeff k =
      if 0 < k ∧ k ≤ (j : ℕ) + 1 then (k : ℝ)⁻¹ else 0 := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [coeff_polynomialBoundedIntegral_succ,
      coeff_polynomialPartialSumBasis, Nat.zero_lt_succ, true_and, Nat.add_le_add_iff_right,
      Nat.cast_add, Nat.cast_one]
    split_ifs <;> simp [one_div]

/-- **Exercise 31(c)** of [benIsrael2003generalized], Chapter 0. The entries
of integration in the partial-sum bases are successive differences of
reciprocal coefficients, and the matrices obey Equation (48). -/
theorem polynomialIntegral_toMatrix_partialSum (n : ℕ) :
    let I := (polynomialBoundedIntegral n).toMatrix (polynomialPartialSumBasis n)
      (polynomialPartialSumBasis (n + 1))
    (∀ i j, I i j =
      (if 0 < (i : ℕ) ∧ (i : ℕ) ≤ (j : ℕ) + 1 then (i : ℝ)⁻¹ else 0) -
      (if (i : ℕ) ≤ (j : ℕ) then ((i : ℝ) + 1)⁻¹ else 0)) ∧
      I = (polynomialPartialSumChange (n + 1))⁻¹ *
        (polynomialBoundedIntegral n).toMatrix (polynomialMonomialBasis n)
          (polynomialMonomialBasis (n + 1)) * polynomialPartialSumChange n := by
  refine ⟨?_, toMatrix_polynomialPartialSum_change _⟩
  intro i j
  rw [LinearMap.toMatrix_apply, polynomialPartialSumBasis_repr,
    coeff_boundedIntegral_partialSum, coeff_boundedIntegral_partialSum]
  simp

end PartialSums

end PolynomialsExercises

section ProjectionExercises

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- **Exercise 32** of [benIsrael2003generalized], Chapter 0. For complementary
subspaces the component of each vector in the first space is linear in the
vector. The component and the complementary remainder specify the map uniquely. -/
theorem projection_isLinear (L M : Submodule ℂ E) (h : IsCompl L M) :
    ∃! P : E →ₗ[ℂ] E, ∀ x, P x ∈ L ∧ x - P x ∈ M := by
  refine ⟨L.projection M h, fun x => ⟨Submodule.projection_apply_mem h x,
    Submodule.sub_projection_mem h x⟩, ?_⟩
  intro P hP
  ext x
  apply sub_eq_zero.mp
  refine Submodule.disjoint_def.mp h.disjoint _
    (L.sub_mem (hP x).1 (Submodule.projection_apply_mem h x)) ?_
  have he : P x - L.projection M h x = (x - L.projection M h x) - (x - P x) := by abel
  rw [he]
  exact M.sub_mem (Submodule.sub_projection_mem h x) (hP x).2

/-- **Exercise 33** of [benIsrael2003generalized], Chapter 0. The fixed space
of a projection along a complement is its range, and the projection is idempotent. -/
theorem projection_idempotent (L M : Submodule ℂ E) (h : IsCompl L M) :
    (∀ x, L.projection M h x = x ↔ x ∈ L) ∧ IsIdempotentElem (L.projection M h) :=
  ⟨Submodule.projection_eq_self_iff h, Submodule.isIdempotentElem_projection h⟩

end ProjectionExercises

section MatrixNormResults

open Matrix
open scoped ENNReal

section MatrixNormExercises

private theorem isVectorNorm_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] :
    IsVectorNorm (norm : V → ℝ) := ⟨norm_nonneg, fun _ => norm_eq_zero, norm_smul, norm_add_le⟩

private theorem isVectorNorm_of_seminorm {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : Seminorm ℂ V) (hp : ∀ x, p x = 0 → x = 0) : IsVectorNorm p :=
  ⟨apply_nonneg p, fun x => ⟨hp x, fun hx => hx ▸ map_zero p⟩, map_smul_eq_mul p,
    map_add_le_add p⟩

private def IsVectorNorm.toSeminorm {V : Type*} [AddCommGroup V] [Module ℂ V]
    {p : V → ℝ} (hp : IsVectorNorm p) : Seminorm ℂ V where
  toFun := p
  map_zero' := hp.map_zero
  add_le' := hp.triangle
  neg' x := by simpa using hp.smul (-1) x
  smul' := hp.smul

open scoped Matrix.Norms.Frobenius in
/-- **Exercise 34**, Equation (50), of [benIsrael2003generalized]. The
Frobenius norm is the square root of the real trace of the column Gramian. -/
theorem frobenius_norm_eq_sqrt_trace {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ‖A‖ = Real.sqrt (trace (Aᴴ * A)).re := by
  have h : (trace (Aᴴ * A)).re = ‖A‖ ^ 2 := by
    rw [← frobenius_norm_sq_eq_trace]
    rfl
  rw [h, Real.sqrt_sq (norm_nonneg _)]

open scoped Matrix.Norms.Frobenius in
/-- **Exercise 34** of [benIsrael2003generalized]. The Frobenius norm
satisfies the four matrix norm conditions, including submultiplicativity. -/
theorem frobenius_isMultiplicativeMatrixNorm :
    IsMultiplicativeMatrixNorm (fun m n (A : Matrix (Fin m) (Fin n) ℂ) => ‖A‖) := by
  refine ⟨fun _ _ => isVectorNorm_norm, ?_⟩
  intro m n p A B
  exact (frobenius_norm_mul_le_lpOpNorm_two_mul A B).trans
    (mul_le_mul_of_nonneg_right (l2_opNorm_le_frobenius_norm A) (norm_nonneg _))

open scoped Matrix.Norms.Elementwise in
/-- **Exercise 34**, Equation (51), of [benIsrael2003generalized]. The
entry maximum norm takes the largest absolute entry, with value zero for an empty matrix. -/
noncomputable def entryMaxNorm {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ := ‖A‖

open scoped Matrix.Norms.Elementwise in
/-- The elementwise maximum is the maximum of the two finite index sets. -/
theorem entryMaxNorm_eq_sup {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    entryMaxNorm A = ↑(Finset.univ.sup fun i : m => Finset.univ.sup fun j : n => ‖A i j‖₊) := by
  exact Matrix.norm_eq_sup_sup_nnnorm A

open scoped Matrix.Norms.Elementwise in
/-- The entry maximum satisfies the vector norm axioms on the space of matrices. -/
theorem isMatrixNorm_entryMaxNorm {m n : Type*} [Fintype m] [Fintype n] :
    IsMatrixNorm (entryMaxNorm : Matrix m n ℂ → ℝ) := isVectorNorm_norm

/-- In the entry maximum norm the two-by-two all-ones matrix violates
submultiplicativity, completing **Exercise 34**. -/
theorem entryMaxNorm_not_submultiplicative :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, entryMaxNorm A * entryMaxNorm A < entryMaxNorm (A * A) := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := of fun _ _ => 1
  have hA : entryMaxNorm A = 1 := by
    simp [entryMaxNorm_eq_sup, A, Finset.sup_const Finset.univ_nonempty]
  have hAA : A * A = of (fun _ _ => (2 : ℂ)) := by
    ext i j
    norm_num [A, Matrix.mul_apply, Fin.sum_univ_two]
  have hB : entryMaxNorm (A * A) = 2 := by
    rw [hAA, entryMaxNorm_eq_sup]
    simp [Finset.sup_const Finset.univ_nonempty]
  exact ⟨A, by
    rw [hA, hB]
    norm_num⟩

/-- **Exercise 35**, Equation (53), of [benIsrael2003generalized]. A
pair of vector norms induces a norm on rectangular matrices. The unit-ball
and ratio formulas agree when the input norm is definite. -/
noncomputable abbrev inducedMatrixNorm {m n : Type*} [Fintype n]
    (q : Seminorm ℂ (m → ℂ)) (p : Seminorm ℂ (n → ℂ)) (A : Matrix m n ℂ) : ℝ := inducedNorm q p A

/-- The induced norm is the supremum of norm ratios over nonzero vectors. -/
theorem inducedMatrixNorm_eq_iSup_div {m n : Type*} [Fintype m] [Fintype n]
    (q : Seminorm ℂ (m → ℂ)) (p : Seminorm ℂ (n → ℂ)) (hp : ∀ x, p x = 0 → x = 0)
    (A : Matrix m n ℂ) :
    inducedMatrixNorm q p A = ⨆ x : {x : n → ℂ // x ≠ 0}, q (A *ᵥ x) / p x :=
  inducedNorm_eq_iSup_div (q := q) (p := p) hp A

/-- The induced matrix norm is consistent and least among consistent norms. -/
theorem inducedMatrixNorm_consistent_le {m n : Type*} [Fintype m] [Fintype n]
    (q : Seminorm ℂ (m → ℂ)) (p : Seminorm ℂ (n → ℂ)) (hq : ∀ y, q y = 0 → y = 0)
    (hp : ∀ x, p x = 0 → x = 0) :
    areConsistentNorms (inducedMatrixNorm q p) p q ∧
      ∀ N : Matrix m n ℂ → ℝ, areConsistentNorms N p q → ∀ A, inducedMatrixNorm q p A ≤ N A := by
  refine ⟨⟨isVectorNorm_of_seminorm (inducedSeminorm q p hp)
    (fun A => (inducedNorm_eq_zero_iff (q := q) (p := p) hq hp A).mp),
    isVectorNorm_of_seminorm p hp, isVectorNorm_of_seminorm q hq,
    isConsistent_inducedNorm (q := q) (p := p) hp⟩, ?_⟩
  intro N hN A
  exact inducedNorm_le_of_isConsistent hN.2.2.2 A (hN.1.nonneg A)

/-- The induced norms are submultiplicative for every compatible product. -/
theorem inducedMatrixNorm_mul_le {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    (r : Seminorm ℂ (l → ℂ)) (q : Seminorm ℂ (m → ℂ)) (p : Seminorm ℂ (n → ℂ))
    (hq : ∀ y, q y = 0 → y = 0) (hp : ∀ x, p x = 0 → x = 0)
    (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    inducedMatrixNorm r p (A * B) ≤ inducedMatrixNorm r q A * inducedMatrixNorm q p B :=
  inducedNorm_mul_le (q := q) (p := p) r hp hq A B

/-- **Exercise 36**, Equation (55), of [benIsrael2003generalized].
Both the unit sphere and closed unit ball have the same attained maximum
of the image norm. The ball formula uses the image norm also at zero. -/
theorem inducedMatrixNorm_eq_max {m n : Type*} [Fintype m] [Fintype n] [Nonempty n]
    (q : Seminorm ℂ (m → ℂ)) (p : Seminorm ℂ (n → ℂ)) (hp : ∀ x, p x = 0 → x = 0)
    (A : Matrix m n ℂ) :
    let S := inducedMatrixNorm q p A
    (∃ x, p x = 1 ∧ q (A *ᵥ x) = S) ∧ ∀ x, p x ≤ 1 → q (A *ᵥ x) ≤ S := by
  obtain ⟨x, hx, hval⟩ := exists_inducedNorm_eq (q := q) (p := p) hp A
  exact ⟨⟨x, hx, hval.symm⟩, fun _ hh => le_inducedNorm hp A hh⟩

/-- **Exercise 37** of [benIsrael2003generalized]. A submultiplicative
square matrix norm admits a consistent vector norm. -/
theorem exists_consistentVectorNorm {n : Type*} [Fintype n] [Nonempty n]
    (N : Matrix n n ℂ → ℝ) (hN : IsMatrixNorm N)
    (hMul : ∀ A B, N (A * B) ≤ N A * N B) :
    ∃ p : Seminorm ℂ (n → ℂ), areConsistentNorms N p p := by
  let y : n → ℂ := fun _ => 1
  have hy : y ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h (Classical.arbitrary n))
  obtain ⟨p, hc, hp⟩ := exists_isConsistent_of_mul_le hN.toSeminorm hMul hy
  have hz := hp (fun A => (hN.eq_zero_iff A).mp)
  exact ⟨p, hN, isVectorNorm_of_seminorm p hz, isVectorNorm_of_seminorm p hz, hc⟩

open scoped Matrix.Norms.Operator in
/-- **Exercise 38**, Equations (56)–(56.2), of [benIsrael2003generalized].
The induced $p$-norm attains its maximum on the $p$-unit sphere. Its special
cases are the largest column sum, the largest row sum, and the spectral norm. -/
theorem inducedLpMatrixNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    [Nonempty n] (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix m n ℂ) :
    ((∃ x, lpSeminorm p x = 1 ∧ lpSeminorm p (A *ᵥ x) = lpOpNorm p A) ∧
      ∀ x, lpSeminorm p x ≤ 1 → lpSeminorm p (A *ᵥ x) ≤ lpOpNorm p A) ∧
    lpOpNorm 1 A = ↑(Finset.univ.sup fun j : n => ∑ i : m, ‖A i j‖₊) ∧
    lpOpNorm ⊤ A = ↑(Finset.univ.sup fun i : m => ∑ j : n, ‖A i j‖₊) ∧
    lpOpNorm 2 A = Real.sqrt (spectralRadius (Aᴴ * A)) := by
  refine ⟨?_, lpOpNorm_one_eq_sup_sum_norm A, (lpOpNorm_top A).trans (linfty_opNorm_def A), ?_⟩
  · rw [lpOpNorm_eq_inducedNorm]
    exact inducedMatrixNorm_eq_max _ _ (lpSeminorm_definite p) A
  · rw [lpOpNorm_two]
    exact (opNorm_eq_sqrt_gram_spectralRadius A).1

/-- **Exercise 39**, Equation (57), of [benIsrael2003generalized].
In positive dimension, the identity has induced norm one, and any
consistent matrix norm assigns it a value at least one. -/
theorem consistentMatrixNorm_one {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (p : Seminorm ℂ (n → ℂ)) (hp : ∀ x, p x = 0 → x = 0)
    (N : Matrix n n ℂ → ℝ) (hN : areConsistentNorms N p p) :
    inducedMatrixNorm p p (1 : Matrix n n ℂ) = 1 ∧ 1 ≤ N 1 := by
  have h := inducedNorm_one (p := p) hp
  refine ⟨h, h ▸ ?_⟩
  exact inducedNorm_le_of_isConsistent hN.2.2.2 1 (hN.1.nonneg 1)

open scoped Matrix.Norms.Frobenius in
/-- **Exercise 40** of [benIsrael2003generalized]. Both the Frobenius and
spectral norms are unchanged by left and right unitary factors. -/
theorem frobenius_opNorm_unitarilyInvariant {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    isUnitarilyInvariantNorm (norm : Matrix m n ℂ → ℝ) ∧
      isUnitarilyInvariantNorm (lpOpNorm 2 : Matrix m n ℂ → ℝ) := by
  refine ⟨⟨isVectorNorm_norm, fun A _ _ hU hV => frobenius_norm_unitary_mul_mul_unitary hU A hV⟩,
    ?_⟩
  refine ⟨?_, fun A _ _ hU hV => ?_⟩
  · have he : (lpOpNorm 2 : Matrix m n ℂ → ℝ) =
        inducedMatrixNorm (lpSeminorm 2) (lpSeminorm 2) :=
      funext (lpOpNorm_eq_inducedNorm 2)
    rw [he]
    exact (inducedMatrixNorm_consistent_le _ _ (lpSeminorm_definite 2)
      (lpSeminorm_definite 2)).1.1
  · simp only [lpOpNorm_two]
    exact l2_opNorm_unitary_mul_mul_unitary hU A hV

/-- **Exercise 41**, Equation (59), of [benIsrael2003generalized]. Every
submultiplicative matrix norm bounds the spectral radius. -/
theorem spectralRadius_le_matrixNorm {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (N : Matrix n n ℂ → ℝ) (hN : IsMatrixNorm N) (hMul : ∀ A B, N (A * B) ≤ N A * N B)
    (A : Matrix n n ℂ) : spectralRadius A ≤ N A := by
  obtain ⟨p, hp⟩ := exists_consistentVectorNorm N hN hMul
  have h := spectralRadius_le_of_isConsistent
    (fun x => (hp.2.1.eq_zero_iff x).mp) hp.2.2.2 A
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal (hN.nonneg A))

/-- **Exercise 42** of [benIsrael2003generalized]. Submultiplicative
matrix norms approximate the spectral radius of any prescribed square matrix
arbitrarily closely. The witnesses may be taken to be induced norms. -/
theorem exists_matrixNorm_le_spectralRadius_add {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Matrix n n ℂ → ℝ, IsMatrixNorm N ∧ (∀ B C, N (B * C) ≤ N B * N C) ∧
      N A ≤ spectralRadius A + ε := by
  obtain ⟨p, hp, h⟩ := exists_inducedNorm_le_spectralRadius_add A hε
  refine ⟨inducedMatrixNorm p p, (inducedMatrixNorm_consistent_le p p hp hp).1.1, ?_, h⟩
  exact inducedMatrixNorm_mul_le p p p hp hp

end MatrixNormExercises

end MatrixNormResults

section SteinExercises

open Matrix Filter
open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

private theorem summable_conjTranspose_pow_mul_pow (A : Matrix n n ℂ) (hA : isConvergent A) :
    Summable (fun k : ℕ => (A ^ k)ᴴ * A ^ k) := by
  have hρ := (spectralRadius_lt_one_iff_tendsto_pow A).mpr hA
  obtain ⟨r, hrA, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hρ
  obtain ⟨C, _, hC⟩ := exists_norm_pow_le_of_spectralRadius_lt A hrA
  have hr' : (r : ℝ) < 1 := by exact_mod_cast ENNReal.coe_lt_one_iff.mp hr
  have hr₂ : (r : ℝ) ^ 2 < 1 := by nlinarith [r.coe_nonneg]
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (sq_nonneg (r : ℝ)) hr₂).mul_left (C ^ 2)) fun k => ?_
  have hk : ‖(A ^ k)ᴴ‖ = ‖A ^ k‖ := by
    simpa only [lpOpNorm_two] using lpOpNorm_two_conjTranspose (A ^ k)
  calc
    ‖(A ^ k)ᴴ * A ^ k‖ ≤ ‖A ^ k‖ ^ 2 := by
      simpa only [hk, pow_two] using norm_mul_le ((A ^ k)ᴴ) (A ^ k)
    _ ≤ (C * (r : ℝ) ^ k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hC k) 2
    _ = C ^ 2 * ((r : ℝ) ^ 2) ^ k := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]

private theorem exists_stein_eq_one (A : Matrix n n ℂ) (hA : isConvergent A) :
    ∃ H : Matrix n n ℂ, H.PosDef ∧ H - Aᴴ * H * A = 1 := by
  let G (k : ℕ) : Matrix n n ℂ := (A ^ k)ᴴ * A ^ k
  have hG : Summable G := summable_conjTranspose_pow_mul_pow A hA
  let S := ∑' k : ℕ, G (k + 1)
  let H := ∑' k : ℕ, G k
  have htail : Summable (fun k : ℕ => G (k + 1)) := (summable_nat_add_iff 1).mpr hG
  have hS : S.PosSemidef := by
    apply Matrix.posSemidef_is_closed.mem_of_tendsto htail.hasSum
    filter_upwards [] with s
    exact posSemidef_sum s fun k _ => posSemidef_conjTranspose_mul_self _
  have hH : H = 1 + S := by
    simpa [G, H, S] using hG.tsum_eq_zero_add
  have hAHA : Aᴴ * H * A = S := by
    change Aᴴ * (∑' k, G k) * A = _
    calc
      _ = ∑' k, Aᴴ * G k * A := ((hG.hasSum.mul_left Aᴴ).mul_right A).tsum_eq.symm
      _ = ∑' k, G (k + 1) := by
        apply tsum_congr
        intro k
        simp only [G, pow_succ, conjTranspose_mul, Matrix.mul_assoc]
  exact ⟨H, hH ▸ PosDef.one.add_posSemidef hS, by rw [hAHA, hH, add_sub_cancel_right]⟩

omit [Nonempty n] in
private theorem norm_eigenvalue_lt_one_of_stein {A H : Matrix n n ℂ} (hH : H.PosDef)
    (hD : (H - Aᴴ * H * A).PosDef) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) : ‖μ‖ < 1 := by
  have he : Module.End.HasEigenvalue A.mulVecLin μ := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    exact (Matrix.spectrum_toLin' A).symm ▸ hμ
  obtain ⟨x, hx⟩ := he.exists_hasEigenvector
  obtain ⟨hAx, hx0⟩ := (hasEigenvector_iff_mulVec_eq A μ x).mp hx
  have h₁ : 0 < (star x ⬝ᵥ (H *ᵥ x)).re := (Complex.lt_def.mp (hH.dotProduct_mulVec_pos hx0)).1
  have hg : star x ⬝ᵥ ((Aᴴ * H * A) *ᵥ x) =
      (‖μ‖ ^ 2 : ℝ) • (star x ⬝ᵥ (H *ᵥ x)) := by
    calc
      _ = star (A *ᵥ x) ⬝ᵥ (H *ᵥ (A *ᵥ x)) := by
        simp only [star_mulVec, dotProduct_mulVec, vecMul_vecMul]
      _ = _ := by
        rw [hAx, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_smul]
        change (μ * (starRingEnd ℂ) μ) • _ = _
        rw [Complex.mul_conj', ← Complex.ofReal_pow]
        rfl
  have h₂ := hD.dotProduct_mulVec_pos hx0
  rw [sub_mulVec, dotProduct_sub, hg] at h₂
  have h₂' := (Complex.lt_def.mp h₂).1
  change 0 < (star x ⬝ᵥ (H *ᵥ x) - (‖μ‖ ^ 2 : ℝ) • (star x ⬝ᵥ (H *ᵥ x))).re at h₂'
  rw [Complex.sub_re, Complex.smul_re, smul_eq_mul] at h₂'
  by_contra! h
  have hp := mul_le_mul_of_nonneg_right (one_le_pow₀ h (n := 2)) h₁.le
  linarith

/-- **Exercise 48** of [benIsrael2003generalized], Chapter 0. Stein's
criterion for convergence is the existence of a positive definite matrix
whose difference from its congruence by $A$ is positive definite. -/
theorem isConvergent_iff_exists_stein_posDef (A : Matrix n n ℂ) :
    isConvergent A ↔ ∃ H : Matrix n n ℂ, H.PosDef ∧ (H - Aᴴ * H * A).PosDef := by
  constructor
  · intro hA
    obtain ⟨H, hH, he⟩ := exists_stein_eq_one A hA
    exact ⟨H, hH, he ▸ PosDef.one⟩
  · rintro ⟨H, hH, hD⟩
    apply (isConvergent_iff_spectralRadius_lt_one A).mpr
    obtain ⟨μ, hμ, hρ⟩ := (spectralRadius_eq_max A).1
    rw [← hρ]
    exact norm_eigenvalue_lt_one_of_stein hH hD hμ

end SteinExercises

section ApproximateTriangularSimilarity

open Matrix

/-- **Exercise 21** of [benIsrael2003generalized]. Perron's approximate
diagonalization makes the total magnitude of the off-diagonal entries
arbitrarily small by similarity with an upper triangular matrix. -/
theorem exists_similar_upperTriangular_sum_norm_offDiag_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, A.IsSimilar B ∧ B.IsUpperTriangular ∧
      (∑ i, ∑ j, if i ≠ j then ‖B i j‖ else 0) ≤ ε := by
  obtain ⟨U, hU, htri, _⟩ := exists_unitary_conj_upperTriangular A
  let T := star U * A * U
  let total : ℝ := ∑ i, ∑ j, ‖T i j‖
  have htotal : 0 ≤ total := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => norm_nonneg _
  let δ := min 1 (ε / (1 + total))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδle : δ ≤ 1 := min_le_left _ _
  have hδ₀ : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  let d : Fin n → ℂ := fun i => (δ : ℂ) ^ i.val
  let D := Matrix.diagonal d
  let Dinv := Matrix.diagonal fun i => (d i)⁻¹
  have hD : IsUnit D := isUnit_diagonal.mpr
    (Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr (pow_ne_zero _ hδ₀))
  have hDinv : D⁻¹ = Dinv := by
    apply Matrix.inv_eq_left_inv
    rw [show Dinv * D = Matrix.diagonal (fun i => (d i)⁻¹ * d i) from
      diagonal_mul_diagonal _ _]
    simp [d, hδ₀]
  let B := D⁻¹ * T * D
  have hentry (i j : Fin n) : B i j = (d i)⁻¹ * T i j * d j := by
    change (D⁻¹ * T * D) i j = _
    rw [hDinv, show D = diagonal d from rfl, mul_diagonal, diagonal_mul]
  have hupper : B.IsUpperTriangular := by
    intro i j hij
    have hzero : T i j = 0 := htri hij
    rw [hentry, hzero, mul_zero, zero_mul]
  refine ⟨B, (IsUnitarilySimilar.isSimilar ⟨U, hU, rfl⟩).trans ⟨D, hD, rfl⟩,
    hupper, ?_⟩
  have hbound (i j : Fin n) : (if i ≠ j then ‖B i j‖ else 0) ≤ δ * ‖T i j‖ := by
    by_cases heq : i = j
    · simp [heq, mul_nonneg hδ.le (norm_nonneg _)]
    rw [ite_eq_left heq]
    rcases lt_or_gt_of_ne heq with hij | hji
    · have hform : B i j = (δ : ℂ) ^ (j.val - i.val) * T i j := by
        rw [hentry, pow_sub₀ _ hδ₀ hij.le]
        dsimp [d]
        ring
      have hexp : 1 ≤ j.val - i.val := by omega
      have hpow : δ ^ (j.val - i.val) ≤ δ := by
        rw [show j.val - i.val = (j.val - i.val - 1) + 1 by omega, pow_succ]
        exact mul_le_of_le_one_left hδ.le (pow_le_one₀ hδ.le hδle)
      rw [hform, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
      exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    · rw [hupper hji, norm_zero]
      exact mul_nonneg hδ.le (norm_nonneg _)
  calc
    _ ≤ ∑ i, ∑ j, δ * ‖T i j‖ := Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hbound i j
    _ = δ * total := by simp [total, Finset.mul_sum]
    _ ≤ ε := by
      have h := (le_div_iff₀ (show 0 < 1 + total by linarith)).mp
        (min_le_right (1 : ℝ) (ε / (1 + total)))
      nlinarith

end ApproximateTriangularSimilarity

section SpectralExercises

open Matrix
open scoped InnerProductSpace

/-- **Exercise 12** of [benIsrael2003generalized]. A subspace of dimension greater than
that of another subspace has a nonzero intersection with its orthogonal complement. -/
theorem inf_orthogonal_ne_bot_of_finrank_lt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (L M : Submodule ℂ E) (h : Module.finrank ℂ M < Module.finrank ℂ L) :
    L ⊓ Mᗮ ≠ ⊥ := by
  intro hbot
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq L Mᗮ
  rw [hbot, finrank_bot, add_zero] at hdim
  have horth := M.finrank_add_finrank_orthogonal
  have hle := (L ⊔ Mᗮ).finrank_le
  omega

/-- **Exercise 22(a)** of [benIsrael2003generalized]. A complex matrix is normal exactly
when it is unitarily similar to a diagonal matrix. -/
theorem isStarNormal_iff_unitary_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    IsStarNormal A ↔ ∃ d : n → ℂ, A.IsUnitarilySimilar (Matrix.diagonal d) := by
  rw [Matrix.IsStarNormal.spectral_theorem]
  constructor
  · rintro ⟨U, hU, d, hd⟩
    exact ⟨d, U, hU, by simpa only [star_eq_conjTranspose] using hd.symm⟩
  · rintro ⟨d, U, hU, hd⟩
    exact ⟨U, hU, d, by simpa only [star_eq_conjTranspose] using hd.symm⟩

/-- **Exercise 22(b)** of [benIsrael2003generalized]. A complex matrix is Hermitian
exactly when it is unitarily similar to a real diagonal matrix. -/
theorem isHermitian_iff_unitary_real_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    A.IsHermitian ↔ ∃ d : n → ℝ,
      A.IsUnitarilySimilar (Matrix.diagonal (fun i => (d i : ℂ))) := by
  constructor
  · intro hA
    exact ⟨hA.eigenvalues, hA.eigenvectorUnitary, hA.eigenvectorUnitary.property,
      hA.star_eigenvectorUnitary_mul_mul.symm⟩
  · rintro ⟨d, h⟩
    obtain ⟨U, _, hA⟩ := h.symm
    rw [hA, star_eq_conjTranspose]
    exact isHermitian_conjTranspose_mul_mul U
      (isHermitian_diagonal_iff.mpr fun i => Complex.conj_ofReal (d i))

/-- **Exercise 30(a1, a2)** of [benIsrael2003generalized]. The spectrum and geometric
multiplicities are intrinsic under changes of a single basis. -/
theorem intrinsic_matrixProperties {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (h : A.IsSimilar B) :
    spectrum ℂ A = spectrum ℂ B ∧ ∀ lam, geometricMultiplicity A lam =
      geometricMultiplicity B lam := by
  refine ⟨h.spectrum_eq, fun lam => ?_⟩
  rw [geometricMultiplicity, geometricMultiplicity, eigenspace_mulVecLin_eq_ker,
    eigenspace_mulVecLin_eq_ker]
  exact (h.sub_smul_one lam).finrank_ker_mulVecLin_eq

/-- **Exercise 30(b1)** of [benIsrael2003generalized]. The rank is intrinsic under
independent changes of basis in the domain and codomain. -/
theorem intrinsic_matrixRank {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A B : Matrix m n ℂ}
    (h : equivalentMatrices A B) : A.rank = B.rank := by
  obtain ⟨S, T, hS, hT, rfl⟩ := h
  rw [rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det T).mp hT),
    rank_mul_eq_right_of_isUnit_det _ _
      ((isUnit_iff_isUnit_det S).mp hS)]

/-- **Exercise 29** of [benIsrael2003generalized], corrected. The $i$-eigenspace
of the printed rotation is the complex line generated by $(1,i)$, with
geometric multiplicity one. -/
theorem rotation_geometricMultiplicity :
    let A : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
    Module.End.eigenspace A.mulVecLin Complex.I = ℂ ∙ (![1, Complex.I] : Fin 2 → ℂ) ∧
      geometricMultiplicity A Complex.I = 1 := by
  intro A
  have hspace : Module.End.eigenspace A.mulVecLin Complex.I =
      ℂ ∙ (![1, Complex.I] : Fin 2 → ℂ) := by
    ext x
    rw [mem_eigenspace_iff_mulVec_eq, Submodule.mem_span_singleton]
    constructor
    · intro hx
      have hx₁ : x 1 = Complex.I * x 0 := by
        simpa [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hx (0 : Fin 2)
      refine ⟨x 0, ?_⟩
      funext i
      fin_cases i
      · simp
      · change x 0 * Complex.I = x 1
        rw [mul_comm, hx₁]
    · rintro ⟨z, rfl⟩
      rw [mulVec_smul, smul_comm Complex.I z]
      apply congrArg (z • ·)
      funext i
      fin_cases i <;> simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.I_mul_I]
  refine ⟨hspace, ?_⟩
  rw [geometricMultiplicity, hspace, finrank_span_singleton]
  intro h
  have h0 := congrFun h (0 : Fin 2)
  simp at h0

/-- **Exercise 29** of [benIsrael2003generalized], corrected. The printed
rotation has no nonzero real eigenvector for a real eigenvalue. -/
theorem rotation_mulVec_eq_smul_real {lam : ℝ} {x : Fin 2 → ℝ}
    (h : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x = lam • x) :
    x = 0 := by
  have h₀ : x 1 = lam * x 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h (0 : Fin 2)
  have h₁ : -(x 0) = lam * x 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun h (1 : Fin 2)
  have hx : x 0 = 0 := by
    rw [h₀] at h₁
    have hp : (lam ^ 2 + 1) * x 0 = 0 := by linear_combination -h₁
    exact (mul_eq_zero.mp hp).resolve_left (by positivity)
  funext i
  fin_cases i
  · exact hx
  · simp [h₀, hx]

/-- **Exercise 29** of [benIsrael2003generalized], corrected. The printed
rotation has no nonzero real eigenvector even after complexification. -/
theorem rotation_mulVec_eq_smul_real_vector {lam : ℂ} {x : Fin 2 → ℝ}
    (h : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (fun i => (x i : ℂ)) =
      lam • (fun i => (x i : ℂ))) : x = 0 := by
  apply rotation_mulVec_eq_smul_real (lam := lam.re)
  funext i
  have hi := congrArg Complex.re (congrFun h i)
  fin_cases i <;>
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_re] using hi

/-- **Exercise 30(a3, b2, b3)** of [benIsrael2003generalized]. Coordinate
eigenspaces, coordinate kernels, and the sum of squared entry magnitudes can
change under similarity. -/
theorem exists_similar_ne_eigenspace_ker_sum_norm_sq :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A.IsSimilar B ∧
      Module.End.eigenspace A.mulVecLin 0 ≠ Module.End.eigenspace B.mulVecLin 0 ∧
      LinearMap.ker A.mulVecLin ≠ LinearMap.ker B.mulVecLin ∧
      (∑ i, ∑ j, ‖A i j‖ ^ 2) ≠ ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
  let B : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 2, 0]
  let S : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 2, 0]
  have hdet : IsUnit S.det := by
    rw [isUnit_iff_ne_zero, Matrix.det_fin_two]
    norm_num [S]
  have hAB : A * S = S * B := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, B, S, Matrix.mul_apply, Fin.sum_univ_two]
  have hsim : A.IsSimilar B := by
    refine ⟨S, (isUnit_iff_isUnit_det S).mpr hdet, ?_⟩
    rw [Matrix.mul_assoc, hAB, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul S hdet, Matrix.one_mul]
  let x : Fin 2 → ℂ := ![1, 0]
  have hx : x ∈ LinearMap.ker A.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    fin_cases i <;> simp [A, x, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hnx : x ∉ LinearMap.ker B.mulVecLin := by
    intro h
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    have h₁ := congrFun h (1 : Fin 2)
    norm_num [B, x, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h₁
  have hk : LinearMap.ker A.mulVecLin ≠ LinearMap.ker B.mulVecLin := fun h => hnx (h ▸ hx)
  refine ⟨A, B, hsim, by simpa only [Module.End.eigenspace_zero] using hk, hk, ?_⟩
  norm_num [A, B, Fin.sum_univ_two]

/-- **Exercise 23** of [benIsrael2003generalized]. In any dimension at least two,
the printed quarter-turn extended by zero has a nonreal complex eigenvalue.
Thus no real triangular matrix is similar to it. -/
theorem exists_not_realTriangularizable {n : ℕ} (hn : 2 ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      ¬∃ B : Matrix (Fin n) (Fin n) ℝ, A.IsSimilar B ∧
        (B.IsUpperTriangular ∨ B.IsLowerTriangular) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j =>
    if i = a then Pi.single (M := fun _ => ℝ) b 1 j
    else if i = b then Pi.single (M := fun _ => ℝ) a (-1) j else 0
  let x : Fin n → ℂ := Pi.single a 1 + Pi.single b Complex.I
  have hxa : x a = 1 := by simp [x, hab]
  have hxb : x b = Complex.I := by simp [x, hab.symm]
  have hx : x ≠ 0 := fun h => by simp [h] at hxa
  have hxEq : A.complexify *ᵥ x = Complex.I • x := by
    funext i
    by_cases ha : i = a
    · subst i
      simp [A, Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite Complex.ofReal,
        hxa, hxb, ite_mul, Finset.sum_ite_eq']
    by_cases hb : i = b
    · subst i
      simp [A, Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite Complex.ofReal,
        hxa, hxb, ite_mul, Finset.sum_ite_eq', ha, Complex.I_mul_I]
    · simp [A, x, Matrix.mulVec, dotProduct, Pi.single_apply, ha, hb]
  have hA : Complex.I ∈ spectrum ℂ A.complexify := by
    rw [spectrum_eq_setOf_hasEigenvalue]
    exact ⟨x, hxEq, hx⟩
  refine ⟨A, ?_⟩
  rintro ⟨B, hsim, htri⟩
  have hchar : A.complexify.charpoly = B.complexify.charpoly := by
    rw [Matrix.charpoly_complexify, Matrix.charpoly_complexify, hsim.charpoly_eq]
  have hB : Complex.I ∈ spectrum ℂ B.complexify := by
    simpa only [Matrix.mem_spectrum_iff_isRoot_charpoly, hchar] using hA
  have hspec : spectrum ℂ B.complexify = Set.range (fun i => ((B i i : ℝ) : ℂ)) := by
    rcases htri with hu | hl
    · exact (show B.complexify.IsUpperTriangular from
        fun i j h => by simp [hu h]).spectrum_eq
    · exact (show B.complexify.IsLowerTriangular from
        fun i j h => by simp [hl h]).spectrum_eq
  rw [hspec] at hB
  obtain ⟨i, hi⟩ := hB
  have him := congrArg Complex.im hi
  simp at him

end SpectralExercises

section ThinQRExercises

open Matrix
open scoped InnerProductSpace

private theorem fin_val_le_of_orderEmbedding {r n : ℕ} (e : Fin r ↪o Fin n) (i : Fin r) :
    i.val ≤ (e i).val := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i hi =>
      have hlt : (e i.castSucc).val < (e i.succ).val :=
        e.strictMono Fin.castSucc_lt_succ
      simp only [Fin.val_castSucc, Fin.val_succ] at *
      omega

/-- **Exercise 13, Equation (39)** of [benIsrael2003generalized]. Keep the
nonzero Gram–Schmidt residuals in their original order. Their normalized
columns span the range, and the retained coefficient rows give an upper
triangular factor with full row rank. -/
theorem exists_thin_qr_factorization_of_gramSchmidt {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ (e : Fin A.rank ↪o Fin n) (Q : Matrix (Fin m) (Fin A.rank) ℂ)
      (R : Matrix (Fin A.rank) (Fin n) ℂ),
      Set.range e = {j | gramSchmidtResidual A j ≠ 0} ∧
      Q = (gramSchmidtQ A).submatrix id e ∧
      R = (gramSchmidtR A).submatrix e id ∧
      Qᴴ * Q = 1 ∧ LinearMap.range Q.toEuclideanLin = LinearMap.range A.toEuclideanLin ∧
      IsRectUpperTriangular R ∧ R.rank = A.rank ∧ A = Q * R := by
  classical
  let f (j : Fin n) : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (A.col j)
  let g := InnerProductSpace.gramSchmidtNormed ℂ f
  let s : Finset (Fin n) := Finset.univ.filter fun j => g j ≠ 0
  have hs (j : Fin n) : j ∈ s ↔ g j ≠ 0 := by simp [s]
  have hs_residual (j : Fin n) : g j ≠ 0 ↔ gramSchmidtResidual A j ≠ 0 := by
    have hg : g j = 0 ↔ InnerProductSpace.gramSchmidt ℂ f j = 0 := by
      rw [show g j = (‖InnerProductSpace.gramSchmidt ℂ f j‖ : ℂ)⁻¹ •
          InnerProductSpace.gramSchmidt ℂ f j from rfl, smul_eq_zero]
      simp
    rw [ne_eq, hg, ← toLp_gramSchmidtResidual, WithLp.toLp_eq_zero]
  have he_on {r : ℕ} (e : Fin r ↪o Fin n) (he : Set.range e = (s : Set (Fin n))) :
      Orthonormal ℂ (g ∘ e) := by
    let j (i : Fin r) : {k | g k ≠ 0} :=
      ⟨e i, (hs (e i)).mp (show e i ∈ (s : Set (Fin n)) from he ▸ ⟨i, rfl⟩)⟩
    exact (InnerProductSpace.gramSchmidtNormed_orthonormal' f).comp j
      (fun i k h => e.injective (congrArg Subtype.val h))
  have he_span {r : ℕ} (e : Fin r ↪o Fin n) (he : Set.range e = (s : Set (Fin n))) :
      Submodule.span ℂ (Set.range (g ∘ e)) = LinearMap.range A.toEuclideanLin := by
    rw [range_toEuclideanLin_eq_span_col, ← InnerProductSpace.span_gramSchmidt ℂ f,
      ← InnerProductSpace.span_gramSchmidtNormed_range (𝕜 := ℂ) f]
    apply le_antisymm
    · exact Submodule.span_mono fun _ ⟨i, hi⟩ => ⟨e i, hi⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases hgi : g i = 0
      · change g i ∈ _
        rw [hgi]
        exact Submodule.zero_mem _
      have his : i ∈ Set.range e := he.symm ▸ (show i ∈ (s : Set (Fin n)) from (hs i).mpr hgi)
      obtain ⟨j, rfl⟩ := his
      exact Submodule.subset_span ⟨j, rfl⟩
  let e₀ := s.orderEmbOfFin rfl
  have he₀ := s.range_orderEmbOfFin rfl
  have hcard : s.card = A.rank := by
    calc
      _ = Module.finrank ℂ (Submodule.span ℂ (Set.range (g ∘ e₀))) := by
        rw [finrank_span_eq_card (he_on e₀ he₀).linearIndependent, Fintype.card_fin]
      _ = A.rank := by rw [he_span e₀ he₀, finrank_range_toEuclideanLin]
  let e := s.orderEmbOfFin hcard
  have he := s.range_orderEmbOfFin hcard
  let Q := (gramSchmidtQ A).submatrix id e
  let R := (gramSchmidtR A).submatrix e id
  have hcols (i : Fin A.rank) : WithLp.toLp 2 (Q.col i) = g (e i) :=
    toLp_col_gramSchmidtQ A (e i)
  have hQ : Qᴴ * Q = 1 := by
    rw [conjTranspose_mul_self_eq_one_iff_orthonormal,
      show (fun i : Fin A.rank => WithLp.toLp 2 (Q.col i)) = g ∘ e from funext hcols]
    exact he_on e he
  have hspan : LinearMap.range Q.toEuclideanLin = LinearMap.range A.toEuclideanLin := by
    rw [range_toEuclideanLin_eq_span_col]
    simp only [hcols]
    exact he_span e he
  have hR : R = Qᴴ * A := by
    ext i j
    change gramSchmidtR A (e i) j = (Qᴴ * A) i j
    rw [gramSchmidtR_apply, Matrix.mul_apply, dotProduct_comm, dotProduct]
    rfl
  have hA : A = Q * R := by
    rw [hR, ← Matrix.mul_assoc]
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro x
    rw [Matrix.toEuclideanLin_mul_apply, toEuclideanLin_mul_conjTranspose_eq_starProjection hQ]
    have hx : A.toEuclideanLin x ∈ LinearMap.range A.toEuclideanLin := ⟨x, rfl⟩
    rw [← hspan] at hx
    exact ((LinearMap.range Q.toEuclideanLin).starProjection_eq_self_iff.mpr hx).symm
  refine ⟨e, Q, R, ?_, rfl, rfl, hQ, hspan, ?_, ?_, hA⟩
  · rw [he]
    ext j
    exact (hs j).trans (hs_residual j)
  · intro i j hij
    have he_lt : j.val < (e i).val := lt_of_lt_of_le hij (fin_val_le_of_orderEmbedding e i)
    exact gramSchmidtR_apply_of_lt A he_lt
  · refine le_antisymm R.rank_le_height ?_
    calc
      A.rank = (Q * R).rank := congrArg Matrix.rank hA
      _ ≤ R.rank := rank_mul_le_right Q R

/-- **Exercise 13, Equation (40)** of [benIsrael2003generalized]. The thin
orthonormal factor extends to a unitary factor with trailing columns spanning
the kernel of the adjoint of the original matrix. The additional rows of the
upper triangular factor are zero. -/
theorem exists_qr_completion_of_thin_qr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (Q : Matrix (Fin m) (Fin A.rank) ℂ) (R : Matrix (Fin A.rank) (Fin n) ℂ)
    (hQ : Qᴴ * Q = 1) (hspan : LinearMap.range Q.toEuclideanLin =
      LinearMap.range A.toEuclideanLin) (hR : IsRectUpperTriangular R) (hA : A = Q * R) :
    ∃ (U : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin m) (Fin n) ℂ),
      U ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ firstColumns U A.rank_le_height = Q ∧
      LinearMap.range (lastColumns U (Nat.sub_le m A.rank)).toEuclideanLin =
        LinearMap.ker (Aᴴ).toEuclideanLin ∧
      firstRows S A.rank_le_height = R ∧ lastRows S (Nat.sub_le m A.rank) = 0 ∧
      IsRectUpperTriangular S ∧ A = U * S := by
  classical
  have hle : A.rank ≤ m := A.rank_le_height
  let f (j : Fin m) : EuclideanSpace ℂ (Fin m) :=
    if hj : j.val < A.rank then WithLp.toLp 2 (Q.col ⟨j.val, hj⟩) else 0
  let s : Set (Fin m) := {j | j.val < A.rank}
  have hon : Orthonormal ℂ (s.domRestrict f) := by
    let e (j : s) : Fin A.rank := ⟨j.1.val, j.2⟩
    have he : Function.Injective e := fun i j hij =>
      Subtype.ext (Fin.ext (congrArg (fun k : Fin A.rank => k.val) hij))
    convert (conjTranspose_mul_self_eq_one_iff_orthonormal.mp hQ).comp e he using 1
    funext j
    exact dite_eq_left j.2
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    ((finrank_euclideanSpace : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) =
      Fintype.card (Fin m)))
  let U : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => WithLp.ofLp (b j) i
  have hU₁ : Uᴴ * U = 1 := conjTranspose_mul_self_eq_one_iff_orthonormal.mpr b.orthonormal
  have hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ := mem_unitaryGroup_iff'.mpr hU₁
  have hfirst : firstColumns U hle = Q := by
    ext i j
    have hj : (Fin.castLE hle j).val < A.rank := j.isLt
    have hbj := hb (Fin.castLE hle j) hj
    change WithLp.ofLp (b (Fin.castLE hle j)) i = Q i j
    rw [hbj]
    simp [f, j.isLt]
  let Z := lastColumns U (Nat.sub_le m A.rank)
  have hsplit : A.rank + (m - A.rank) = m := Nat.add_sub_of_le hle
  have hZ₁ : Zᴴ * Z = 1 := conjTranspose_lastColumns_mul_lastColumns hU₁ _
  have hQZ : Qᴴ * Z = 0 := by
    rw [← hfirst]
    exact conjTranspose_firstColumns_mul_lastColumns hU₁ _ _ hsplit.le
  have hZdim : Module.finrank ℂ (LinearMap.range Z.toEuclideanLin) = m - A.rank := by
    rw [finrank_range_toEuclideanLin]
    have hr := rank_mul_le_right Zᴴ Z
    rw [hZ₁, rank_one, Fintype.card_fin] at hr
    exact le_antisymm Z.rank_le_width hr
  have horth : LinearMap.range Z.toEuclideanLin = (LinearMap.range A.toEuclideanLin)ᗮ := by
    apply Submodule.eq_of_le_of_finrank_le
    · rw [← hspan, LinearMap.orthogonal_range, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      rintro x ⟨y, rfl⟩
      rw [LinearMap.mem_ker, ← Matrix.toEuclideanLin_mul_apply, hQZ]
      simp
    · have hd := (LinearMap.range A.toEuclideanLin).finrank_add_finrank_orthogonal
      rw [finrank_range_toEuclideanLin, finrank_euclideanSpace, Fintype.card_fin] at hd
      rw [hZdim]
      omega
  let S : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun i j =>
    if hi : i.val < A.rank then R ⟨i.val, hi⟩ j else 0
  have hS₁ : firstRows S hle = R := by
    ext i j
    change (if hi : i.val < A.rank then R ⟨i.val, hi⟩ j else 0) = R i j
    rw [dite_eq_left i.isLt]
  have hS₂ : lastRows S (Nat.sub_le m A.rank) = 0 := by
    ext i j
    change (if hi : m - (m - A.rank) + i.val < A.rank then
      R ⟨m - (m - A.rank) + i.val, hi⟩ j else 0) = 0
    rw [dite_eq_right (by omega)]
  refine ⟨U, S, hU, hfirst, ?_, hS₁, hS₂, ?_, ?_⟩
  · rw [horth, LinearMap.orthogonal_range, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  · intro i j hij
    change (if hi : i.val < A.rank then R ⟨i.val, hi⟩ j else 0) = 0
    split
    · exact hR _ _ hij
    · rfl
  · rw [← firstColumns_mul_firstRows_add_lastColumns_mul_lastRows U S
      hle (Nat.sub_le m A.rank) hsplit, hfirst, hS₁, hS₂, Matrix.mul_zero, add_zero]
    exact hA

end ThinQRExercises

end BenIsraelGreville.Chapter00
