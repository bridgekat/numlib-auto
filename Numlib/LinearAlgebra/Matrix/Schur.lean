/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Schur`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Rank
import Numlib.Data.Fin.Sum
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.Similar

/-!
# The Schur triangulation

**Schur's theorem** states that a linear operator on a finite-dimensional inner product space over
an algebraically closed field is upper triangular in some *orthonormal* basis. Hence a square
complex matrix $A$ is unitarily similar to an upper triangular matrix: $A = Q R Q^H$ with $Q$
unitary and $R$ upper triangular. The diagonal of $R$ lists the eigenvalues of $A$ with their
algebraic multiplicities, because conjugation does not change the characteristic polynomial and the
characteristic polynomial of a triangular matrix is $\prod_i (X - r_{ii})$. The hypothesis that the
field is algebraically closed is needed: over $\mathbb{R}$ the statement is false, as a plane
rotation shows. This is the triangulation of [saad2003iterative], Theorem 1.9, and
[saad2011numerical], Theorem 1.5, and its basis vectors are the *Schur vectors* that deflation
techniques for non-normal matrices use.

The file also proves the Schur form with the eigenvalues in a prescribed order along the diagonal,
the reduction to block triangular form from a known invariant subspace, the characterization of
normal matrices as those with a diagonal Schur form, the splitting of a Hermitian matrix by an
invariant subspace, and the computation of an eigenvector of a triangular matrix by one triangular
solve.

## Main definitions

* `Matrix.IsUpperTriangular.schurEigenvector`: the vector $(-(T_{11} - \lambda I)^{-1} v, 1, 0)$
  built from an upper triangular matrix $T$ and a diagonal entry $\lambda = t_{kk}$, as in
  [quarteroni2000numerical], §5.8.2, (5.56).

## Main results

* `LinearMap.exists_orthonormalBasis_upperTriangular`: the operator form, an orthonormal basis in
  which the matrix of the operator is upper triangular.
* `LinearMap.exists_orthonormalBasis_forall_mem_span`: the same basis described by its flag: each
  initial segment of the basis spans an invariant subspace.
* `Matrix.exists_unitary_conj_upperTriangular`: the matrix form, $Q^H A Q$ upper triangular for a
  unitary $Q$, with the characteristic polynomial of $A$ equal to the product of the
  $X - (Q^H A Q)_{ii}$.
* `Matrix.exists_unitary_conj_upperTriangular_diag_eq`: the Schur form with the eigenvalues in any
  prescribed order along the diagonal ([golub2013matrix], Theorem 7.1.3).
* `Matrix.exists_unitary_conj_fromBlocks_of_mul_eq_mul`: the reduction to block upper triangular
  form from a known invariant subspace ([golub2013matrix], Lemma 7.1.2).
* `Matrix.isStarNormal_iff_strictUpper_eq_zero`: a matrix is normal if and only if its Schur form is
  diagonal ([golub2013matrix], §9.3.2). It follows from
  `Matrix.IsUpperTriangular.eq_diagonal_of_isStarNormal` and the unitary invariance
  `Matrix.isStarNormal_star_mul_mul_iff`.
* `Matrix.IsHermitian.conjTranspose_mul_mul_fromCols_eq_fromBlocks` and
  `Matrix.IsHermitian.charpoly_eq_mul_of_mul_eq_mul`: an invariant subspace of a Hermitian matrix
  splits it into two diagonal blocks, and splits its spectrum ([golub2013matrix], Theorem 8.1.9).
* `Matrix.mulVec_star_conj_eq_smul_of_mulVec_eq_smul`: a unitary similarity carries eigenvectors to
  eigenvectors, which carries an eigenvector of the triangular factor back to $A$.
* `Matrix.IsUpperTriangular.mulVec_schurEigenvector`: the vector
  `Matrix.IsUpperTriangular.schurEigenvector` is an eigenvector of $T$ when $\lambda$ is not a
  diagonal entry above row $k$.

## Proof outline

The proof of Schur's theorem is an induction on the dimension. It passes to the orthogonal
complement of an eigenvector of the **adjoint**: if $A^* w = \nu w$, then $w^\perp$ is invariant
under $A$, because $\langle w, Ay \rangle = \langle A^* w, y \rangle = \bar\nu \langle w, y
\rangle$. The complement of an eigenvector of $A$ itself is in general not invariant. The new basis
vector is put at the end of the basis, which is where an invariant hyperplane puts it.

## Implementation notes

* The field is an `RCLike` field with `[IsAlgClosed 𝕜]`, which in practice means $\mathbb{C}$. Only
  the existence of an eigenvalue, `Module.End.exists_eigenvalue`, uses that the field is
  algebraically closed. The prescribed-order form
  `Matrix.exists_unitary_conj_upperTriangular_diag_eq` instead assumes that the characteristic
  polynomial splits, and so also holds over $\mathbb{R}$.
* The inductive step restricts the operator with `LinearMap.restrict` and appends the new basis
  vector with `Fin.snoc`. With an eigenvector of $A$ itself the complement would not be invariant,
  and the induction would have to carry the compression of $A$ to the complement and its orthogonal
  projection.
* The Schur form is written `star Q * A * Q` with `Q ∈ Matrix.unitaryGroup n 𝕜`.
-/

open Module Submodule

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Let $A$ be a linear operator on a finite-dimensional inner product space $E$, and let $w \in E$
satisfy $A^* w = \nu w$. If $y$ is orthogonal to $w$, then $Ay$ is orthogonal to $w$. That is,
the orthogonal complement of an eigenvector of the adjoint is invariant under $A$.

The reason is that $\langle w, Ay \rangle = \langle A^* w, y \rangle = \bar\nu \langle w, y
\rangle = 0$. -/
theorem mem_orthogonal_singleton_of_adjoint_apply_eq_smul {A : E →ₗ[𝕜] E} {w : E} {ν : 𝕜}
    (hw : A.adjoint w = ν • w) {y : E} (hy : y ∈ (𝕜 ∙ w)ᗮ) : A y ∈ (𝕜 ∙ w)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy ⊢
  rw [← LinearMap.adjoint_inner_left A y w, hw, inner_smul_left, hy, mul_zero]

/-- Schur's theorem in the form that the induction produces: for every operator $A$ on an
$n$-dimensional space there is an orthonormal basis $b$ with $\langle b_i, A b_j \rangle = 0$
for all $j < i$. -/
private theorem exists_orthonormalBasis_forall_inner_eq_zero (𝕜 : Type*) [RCLike 𝕜]
    [IsAlgClosed 𝕜] (n : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E],
      finrank 𝕜 E = n → ∀ A : E →ₗ[𝕜] E, ∃ b : OrthonormalBasis (Fin n) 𝕜 E,
        ∀ i j : Fin n, j < i → (inner 𝕜 (b i) (A (b j)) : 𝕜) = 0 := by
  induction n with
  | zero => exact fun {E} _ _ _ hE A => ⟨(stdOrthonormalBasis 𝕜 E).reindex (finCongr hE),
      fun i => i.elim0⟩
  | succ n ih =>
    intro E _ _ _ hE A
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    obtain ⟨ν, hν⟩ := Module.End.exists_eigenvalue (LinearMap.adjoint A)
    obtain ⟨x, hxe, hx0⟩ := hν.exists_hasEigenvector
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx0
    have hwn : ‖((‖x‖ : 𝕜))⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x),
        inv_mul_cancel₀ hxn]
    set w : E := ((‖x‖ : 𝕜))⁻¹ • x with hwdef
    have hw0 : w ≠ 0 := fun h => by simp [h] at hwn
    have hAw : LinearMap.adjoint A w = ν • w := by
      rw [hwdef, map_smul, Module.End.mem_eigenspace_iff.1 hxe, smul_comm]
    have hinv : ∀ y ∈ (𝕜 ∙ w)ᗮ, A y ∈ (𝕜 ∙ w)ᗮ := fun _ hy =>
      mem_orthogonal_singleton_of_adjoint_apply_eq_smul hAw hy
    have hrank : finrank 𝕜 ((𝕜 ∙ w)ᗮ : Submodule 𝕜 E) = n := by
      have h1 : finrank 𝕜 (𝕜 ∙ w) = 1 := finrank_span_singleton hw0
      have h2 := Submodule.finrank_add_finrank_orthogonal (K := (𝕜 ∙ w)) (E := E)
      omega
    obtain ⟨c, hc⟩ := ih (E := (𝕜 ∙ w)ᗮ) hrank (A.restrict hinv)
    set f : Fin (n + 1) → E := Fin.snoc (α := fun _ => E) (fun i => (c i : E)) w with hf
    have hcast : ∀ i : Fin n, f i.castSucc = (c i : E) := fun i => by
      simp [hf, Fin.snoc_castSucc]
    have hlast : f (Fin.last n) = w := by simp [hf]
    have hon : Orthonormal 𝕜 f := by
      constructor
      · refine Fin.lastCases ?_ ?_
        · rw [hlast]; exact hwn
        · intro i; rw [hcast]; exact c.orthonormal.1 i
      · intro i j hij
        revert hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact fun h => absurd rfl h
          | cast j =>
            intro _
            rw [hlast, hcast, inner_eq_zero_symm]
            exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (c j).2
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            intro _
            rw [hcast, hlast]
            exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (c i).2
          | cast j =>
            intro hij
            rw [hcast, hcast, ← Submodule.coe_inner]
            exact c.orthonormal.2 fun h => hij (by rw [h])
    have hcard : Fintype.card (Fin (n + 1)) = finrank 𝕜 E := by simp [hE]
    refine ⟨(basisOfOrthonormalOfCardEqFinrank hon hcard).toOrthonormalBasis (by simpa using hon),
      ?_⟩
    intro i j hji
    rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hji (lt_irrefl _)
      | cast j =>
        rw [hlast, hcast]
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hinv _ (c j).2)
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hji (Fin.not_lt.2 (Fin.le_last _))
      | cast j =>
        rw [hcast, hcast, show A (c j : E) = ((A.restrict hinv) (c j) : E) from rfl,
          ← Submodule.coe_inner]
        exact hc i j (by simpa using hji)

variable [IsAlgClosed 𝕜]

/-- **Schur's theorem**, operator form. Let $E$ be an inner product space of finite dimension $n$
over an algebraically closed field $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, and let
$A : E \to E$ be linear. Then there is an orthonormal basis $b_0, \dots, b_{n-1}$ of $E$ in
which the matrix of $A$ is upper triangular.

The proof is an induction on the dimension through the orthogonal complement of an eigenvector
of the adjoint, which is an invariant hyperplane
(`LinearMap.mem_orthogonal_singleton_of_adjoint_apply_eq_smul`). This is Theorem 1.9 of
[saad2003iterative]. -/
theorem exists_orthonormalBasis_upperTriangular {n : ℕ} (hn : finrank 𝕜 E = n) (A : E →ₗ[𝕜] E) :
    ∃ b : OrthonormalBasis (Fin n) 𝕜 E,
      (LinearMap.toMatrix b.toBasis b.toBasis A).IsUpperTriangular := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_forall_inner_eq_zero 𝕜 n hn A
  refine ⟨b, fun i j hji => ?_⟩
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  exact hb i j hji

/-- Let $E$ be an inner product space of finite dimension $n$ over an algebraically closed field
$\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, and let $A : E \to E$ be linear. Then there is an
orthonormal basis $b_0, \dots, b_{n-1}$ of $E$ such that
$$A b_j \in \operatorname{span}\{b_0, \dots, b_j\} \qquad \text{for every } j.$$
Each initial segment of the basis therefore spans an $A$-invariant subspace. These vectors are
the **Schur vectors** of $A$. -/
theorem exists_orthonormalBasis_forall_mem_span {n : ℕ} (hn : finrank 𝕜 E = n) (A : E →ₗ[𝕜] E) :
    ∃ b : OrthonormalBasis (Fin n) 𝕜 E,
      ∀ j : Fin n, A (b j) ∈ Submodule.span 𝕜 (b '' Set.Iic j) := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_forall_inner_eq_zero 𝕜 n hn A
  refine ⟨b, fun j => ?_⟩
  have key : ∀ y : E, (∀ i : Fin n, j < i → (inner 𝕜 (b i) y : 𝕜) = 0) →
      y ∈ Submodule.span 𝕜 (b '' Set.Iic j) := by
    intro y hy
    have hsum : ∑ i ∈ Finset.Iic j, (inner 𝕜 (b i) y : 𝕜) • b i = y := by
      conv_rhs => rw [← b.sum_repr' y]
      exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        rw [hy i (by simpa using hi), zero_smul]
    rw [← hsum]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, by simpa using hi, rfl⟩)
  exact key _ fun i hi => hb i j hi

end LinearMap

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {𝕜 : Type*} [RCLike 𝕜]
  [IsAlgClosed 𝕜]

open Polynomial in
/-- **Schur's theorem**, matrix form. Let $A \in \mathbb{K}^{n \times n}$, where
$\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$ is algebraically closed, that is,
$\mathbb{K} = \mathbb{C}$. Then there is a unitary $Q$ such that $R = Q^H A Q$ is upper
triangular and
$$\chi_A(X) = \prod_i (X - r_{ii}).$$
The diagonal of $R$ thus lists the eigenvalues of $A$ with their algebraic multiplicities.

The index type `n` has a linear order, which defines "upper triangular". The second claim holds
because conjugation does not change the characteristic polynomial, and the characteristic
polynomial of a triangular matrix is the product of $X - r_{ii}$. This is Theorem 1.9 of
[saad2003iterative] and Theorem 1.5 of [saad2011numerical]. -/
theorem exists_unitary_conj_upperTriangular (A : Matrix n n 𝕜) :
    ∃ Q ∈ unitaryGroup n 𝕜, (star Q * A * Q).IsUpperTriangular ∧
      A.charpoly = ∏ i, (X - C ((star Q * A * Q) i i)) := by
  classical
  obtain ⟨e, -⟩ : ∃ e : Fin (Fintype.card n) ≃o n, True := ⟨monoEquivOfFin n rfl, trivial⟩
  obtain ⟨b₀, hb₀⟩ := LinearMap.exists_orthonormalBasis_upperTriangular
    (𝕜 := 𝕜) (E := EuclideanSpace 𝕜 n) (n := Fintype.card n) (by simp) (Matrix.toEuclideanLin A)
  obtain ⟨b, hbdef⟩ : ∃ b : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n),
      b = b₀.reindex e.toEquiv := ⟨_, rfl⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n),
      v₀ = EuclideanSpace.basisFun n 𝕜 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix n n 𝕜, Q = v₀.toBasis.toMatrix b.toBasis := ⟨_, rfl⟩
  have hQu : Q ∈ unitaryGroup n 𝕜 := by
    rw [hQdef, OrthonormalBasis.coe_toBasis]
    exact v₀.toMatrix_orthonormalBasis_mem_unitary b
  have hA : LinearMap.toMatrix v₀.toBasis v₀.toBasis (Matrix.toEuclideanLin A) = A := by
    rw [hv₀, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  have hstar : b.toBasis.toMatrix v₀.toBasis = star Q := by
    have h1 : b.toBasis.toMatrix v₀.toBasis * Q = 1 := by
      rw [hQdef]; exact Module.Basis.toMatrix_mul_toMatrix_flip _ _
    calc b.toBasis.toMatrix v₀.toBasis
        = b.toBasis.toMatrix v₀.toBasis * (Q * star Q) := by
          rw [mem_unitaryGroup_iff.1 hQu, mul_one]
      _ = star Q := by rw [← mul_assoc, h1, one_mul]
  have hconj : star Q * A * Q
      = LinearMap.toMatrix b.toBasis b.toBasis (Matrix.toEuclideanLin A) := by
    conv_lhs => rw [← hA, ← hstar, hQdef]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b.toBasis v₀.toBasis
      b.toBasis v₀.toBasis (Matrix.toEuclideanLin A)
  have htri : (star Q * A * Q).IsUpperTriangular := by
    rw [hconj]
    intro i j hji
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, hbdef]
    have h := hb₀ (i := e.symm i) (j := e.symm j) (e.symm.lt_iff_lt.2 hji)
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply] at h
    simpa using h
  refine ⟨Q, hQu, htri, ?_⟩
  rw [← charpoly_of_isUpperTriangular _ htri, mul_assoc, charpoly_mul_comm, mul_assoc,
    mem_unitaryGroup_iff.1 hQu, mul_one]

end Matrix

namespace Matrix

/-! ### Similarity moves eigenvectors -/

section Conj

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Similarity moves eigenvectors.** Let $A, U \in R^{n \times n}$ over a commutative ring $R$,
with $U$ invertible. If $Ax = \mu x$, then
$$(U^{-1} A U)(U^{-1} x) = \mu \, U^{-1} x.$$
This is Exercise 5.9 of [quarteroni2000numerical]. -/
theorem mulVec_conj_eq_smul_of_mulVec_eq_smul {R : Type*} [CommRing R] {A U : Matrix n n R}
    (hU : IsUnit U) {μ : R} {x : n → R} (hx : A *ᵥ x = μ • x) :
    (U⁻¹ * A * U) *ᵥ (U⁻¹ *ᵥ x) = μ • (U⁻¹ *ᵥ x) :=
  IsSimilar.mulVec_eq_smul hU rfl hx

/-- Let $A, U \in R^{n \times n}$ over a commutative ring $R$ with an involution, with $U$ unitary.
If $Ax = \mu x$, then
$$(U^H A U)(U^H x) = \mu \, U^H x.$$

This is the unitary form of `Matrix.mulVec_conj_eq_smul_of_mulVec_eq_smul`. It carries an
eigenvector $y$ of the Hessenberg or Schur form of $A$ back to the eigenvector $x = U y$ of $A$. -/
theorem mulVec_star_conj_eq_smul_of_mulVec_eq_smul {R : Type*} [CommRing R] [StarRing R]
    {A U : Matrix n n R} (hU : U ∈ unitaryGroup n R) {μ : R} {x : n → R} (hx : A *ᵥ x = μ • x) :
    (star U * A * U) *ᵥ (star U *ᵥ x) = μ • (star U *ᵥ x) := by
  rw [mulVec_mulVec, Matrix.mul_assoc, mem_unitaryGroup_iff.1 hU, Matrix.mul_one, ← mulVec_mulVec,
    hx, mulVec_smul]

end Conj

/-! ### Eigenvectors from the Schur form -/

section SchurEigenvector

variable {K : Type*} [Field K] {N : ℕ}

namespace IsUpperTriangular

/-- Let $T \in K^{N \times N}$ over a field $K$ and let $0 \le k < N$, with $\lambda = t_{kk}$.
Partition $T$ around row and column $k$ as
$$T = \begin{bmatrix} T_{11} & v & T_{13} \\ * & \lambda & w^T \\ * & * & T_{33} \end{bmatrix},
  \qquad T_{11} \in K^{k \times k}.$$
The **Schur eigenvector** of $T$ for $k$ is
$$y = \begin{bmatrix} -(T_{11} - \lambda I)^{-1} v \\ 1 \\ 0 \end{bmatrix}.$$

This is the eigenvector of [quarteroni2000numerical], §5.8.2, (5.56). The definition applies to
every $T$ and $k$, because the inverse is `Matrix.inv`, which is $0$ for a singular matrix; then
the first $k$ entries are $0$. The vector is an eigenvector when $T$ is upper triangular and
$\lambda$ is not a diagonal entry of $T_{11}$
(`Matrix.IsUpperTriangular.mulVec_schurEigenvector`). -/
noncomputable def schurEigenvector (T : Matrix (Fin N) (Fin N) K) (k : Fin N) : Fin N → K :=
  fun i =>
    if h : (i : ℕ) < k then
      -(((T.submatrix (Fin.castLE k.isLt.le) (Fin.castLE k.isLt.le) - T k k • 1)⁻¹
        *ᵥ fun j => T (Fin.castLE k.isLt.le j) k) ⟨i, h⟩)
    else if i = k then 1 else 0

/-- The entry $k$ of the Schur eigenvector `Matrix.IsUpperTriangular.schurEigenvector T k` is $1$.
-/
@[simp]
theorem schurEigenvector_apply_self (T : Matrix (Fin N) (Fin N) K) (k : Fin N) :
    schurEigenvector T k k = 1 := by
  simp [schurEigenvector]

/-- For $k < i$, the entry $i$ of the Schur eigenvector
`Matrix.IsUpperTriangular.schurEigenvector T k` is $0$. -/
theorem schurEigenvector_apply_of_lt (T : Matrix (Fin N) (Fin N) K) {k i : Fin N} (h : k < i) :
    schurEigenvector T k i = 0 := by
  have h1 : ¬ ((i : ℕ) < k) := not_lt.2 (Fin.le_def.1 h.le)
  rw [schurEigenvector, dite_eq_right h1, ite_eq_right h.ne']

/-- The Schur eigenvector `Matrix.IsUpperTriangular.schurEigenvector T k` is nonzero, because its
entry $k$ is $1$. -/
theorem schurEigenvector_ne_zero (T : Matrix (Fin N) (Fin N) K) (k : Fin N) :
    schurEigenvector T k ≠ 0 := fun h => by
  simpa using congrFun h k

/-- For upper triangular $T$, $k \le N$ and a scalar $c$, the leading $k \times k$ block of $T$
minus $cI$ is upper triangular. -/
private theorem isUpperTriangular_submatrix_castLE_sub {T : Matrix (Fin N) (Fin N) K}
    (hT : T.IsUpperTriangular) {k : ℕ} (hk : k ≤ N) (c : K) :
    (T.submatrix (Fin.castLE hk) (Fin.castLE hk) - c • 1).IsUpperTriangular := by
  intro i j hji
  rw [Matrix.sub_apply, submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
    ite_eq_right (fun h : i = j => absurd h (ne_of_gt hji)), smul_zero, sub_zero]
  exact hT (Fin.lt_def.2 (by simp only [id, Fin.val_castLE]; exact Fin.lt_def.1 hji))

/-- **The Schur eigenvector is an eigenvector.** Let $T \in K^{N \times N}$ be upper triangular over
a field $K$, and let $0 \le k < N$ with $t_{ii} \neq t_{kk}$ for all $i < k$. Then $y$ =
`Matrix.IsUpperTriangular.schurEigenvector T k` satisfies
$$T y = t_{kk} \, y.$$

This is (5.56) of [quarteroni2000numerical], §5.8.2. Only the diagonal entries above row $k$
must differ from $t_{kk}$. Rows below $k$ vanish on both sides, row $k$ reads $\lambda \cdot 1$,
and the rows above $k$ are the triangular system $(T_{11} - \lambda I) y_1 = -v$ that defines
$y_1$. Together with `Matrix.mulVec_star_conj_eq_smul_of_mulVec_eq_smul` and
`Matrix.exists_unitary_conj_upperTriangular`, this gives an eigenvector $x = Q y$ of $A$ for
each simple eigenvalue from its Schur form. -/
theorem mulVec_schurEigenvector {T : Matrix (Fin N) (Fin N) K}
    (hT : T.IsUpperTriangular) {k : Fin N} (hk : ∀ i, i < k → T i i ≠ T k k) :
    T *ᵥ schurEigenvector T k = T k k • schurEigenvector T k := by
  obtain ⟨hle, -⟩ : ∃ hle : (k : ℕ) ≤ N, True := ⟨k.isLt.le, trivial⟩
  obtain ⟨T₁₁, hT₁₁⟩ : ∃ T₁₁ : Matrix (Fin k) (Fin k) K,
    T₁₁ = T.submatrix (Fin.castLE hle) (Fin.castLE hle) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin k → K, v = fun j => T (Fin.castLE hle j) k := ⟨_, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : Fin k → K, y₁ = -((T₁₁ - T k k • 1)⁻¹ *ᵥ v) := ⟨_, rfl⟩
  have hy : ∀ (i : Fin N) (h : (i : ℕ) < k), schurEigenvector T k i = y₁ ⟨i, h⟩ := by
    intro i h
    rw [schurEigenvector, dite_eq_left h, hy₁, hT₁₁, hv]
    rfl
  -- `T₁₁ - λ` is nonsingular: upper triangular with nonzero diagonal
  have hdet : IsUnit (T₁₁ - T k k • 1).det := by
    rw [hT₁₁]
    refine (isUpperTriangular_submatrix_castLE_sub hT hle _).isUnit_det_of_diag_ne_zero fun i => ?_
    rw [Matrix.sub_apply, submatrix_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
    exact sub_ne_zero.2 (hk _ (by simp [Fin.lt_def]))
  have hsys : T₁₁ *ᵥ y₁ = T k k • y₁ - v := by
    have h := congrArg (fun z => (T₁₁ - T k k • 1) *ᵥ z) hy₁
    simp only [mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec, sub_mulVec,
      smul_mulVec, one_mulVec] at h
    funext i
    have := congrFun h i
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linear_combination this
  funext i
  rw [mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < k)]
  -- the indices at and below `k`: only `j = k` survives
  have htail : ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < k),
      T i j * schurEigenvector T k j = T i k := by
    rw [Finset.sum_eq_single k]
    · rw [schurEigenvector_apply_self, mul_one]
    · intro j hj hjk
      have hkj : k < j := lt_of_le_of_ne (Fin.le_def.2 (not_lt.1 (Finset.mem_filter.1 hj).2))
        (Ne.symm hjk)
      rw [schurEigenvector_apply_of_lt T hkj, mul_zero]
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ k, lt_irrefl (k : ℕ)⟩) h
  -- the indices above `k`: the leading block
  have hhead : ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < k),
      T i j * schurEigenvector T k j = ∑ j : Fin k, T i (Fin.castLE hle j) * y₁ j := by
    rw [Finset.sum_filter, ← Fin.sum_castLE_eq_sum_ite hle]
    exact Finset.sum_congr rfl fun j _ => by rw [hy _ (by simp)]; rfl
  rw [htail, hhead]
  rcases lt_trichotomy i k with hik | rfl | hik
  · -- a row above `k`: the defining system
    have hik' : (i : ℕ) < k := Fin.lt_def.1 hik
    have h1 : ∑ j : Fin k, T i (Fin.castLE hle j) * y₁ j = (T₁₁ *ᵥ y₁) ⟨i, hik'⟩ := by
      rw [mulVec_apply_eq_sum, hT₁₁]
      exact Finset.sum_congr rfl fun j _ => by rw [submatrix_apply]; rfl
    have h2 : T i k = v ⟨i, hik'⟩ := by rw [hv]; rfl
    rw [h1, hsys, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hy i hik', h2]
    ring
  · -- the row `k` itself: only the diagonal entry
    have h0 : ∑ j, T i (Fin.castLE hle j) * y₁ j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [hT (by simp [Fin.lt_def]), zero_mul]
    rw [h0, zero_add, schurEigenvector_apply_self, mul_one]
  · -- a row below `k`: everything vanishes
    have h0 : ∑ j : Fin k, T i (Fin.castLE hle j) * y₁ j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [hT (by simp only [id, Fin.lt_def, Fin.val_castLE]; omega), zero_mul]
    rw [h0, zero_add, hT hik, schurEigenvector_apply_of_lt T hik, mul_zero]

end IsUpperTriangular

end SchurEigenvector

end Matrix

/-! ### Normal matrices and invariant subspaces of Hermitian matrices -/

namespace Matrix

section Normal

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {𝕜 : Type*} [RCLike 𝕜]

/-- **A normal upper triangular matrix is diagonal.** Let $T \in \mathbb{K}^{n \times n}$ over
$\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$ be upper triangular and normal, $T^H T = T T^H$.
Then $T = \operatorname{diag}(t_{11}, \dots, t_{nn})$.

The proof is a strong induction along the order of the index type. The $(i, i)$ entries of
$T^H T = T T^H$ give $\sum_{k \le i} |t_{ki}|^2 = \sum_{k \ge i} |t_{ik}|^2$. The entries above
row $i$ in column $i$ vanish by induction, so $\sum_{k > i} |t_{ik}|^2 = 0$. -/
theorem IsUpperTriangular.eq_diagonal_of_isStarNormal {T : Matrix n n 𝕜}
    (hT : T.IsUpperTriangular) (hN : IsStarNormal T) : T = diagonal fun i => T i i := by
  have hcomm : star T * T = T * star T := hN.star_comm_self.eq
  have hrow : ∀ i j, i < j → T i j = 0 := by
    intro i
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      intro j hij
      have hii := congrFun (congrFun hcomm i) i
      simp only [Matrix.mul_apply, star_apply, RCLike.star_def] at hii
      have hL : ∑ k, (starRingEnd 𝕜) (T k i) * T k i = (starRingEnd 𝕜) (T i i) * T i i := by
        refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
        rcases lt_or_gt_of_ne hk with h | h
        · rw [ih k h i h, mul_zero]
        · rw [hT h, mul_zero]
      rw [hL, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hii
      have hS : ∑ k ∈ Finset.univ.erase i, T i k * (starRingEnd 𝕜) (T i k) = 0 := by
        linear_combination (-1 : 𝕜) * hii
      have hsum : ∑ k ∈ Finset.univ.erase i, ‖T i k‖ ^ 2 = 0 := by
        have : ((∑ k ∈ Finset.univ.erase i, ‖T i k‖ ^ 2 : ℝ) : 𝕜) = 0 := by
          push_cast
          rw [← hS]
          exact Finset.sum_congr rfl fun k _ => (RCLike.mul_conj _).symm
        exact_mod_cast this
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖T i k‖)).mp hsum j
        (Finset.mem_erase.mpr ⟨hij.ne', Finset.mem_univ _⟩)
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hrow i j h, diagonal_apply_ne _ h.ne]
  · rw [diagonal_apply_eq]
  · rw [hT h, diagonal_apply_ne _ h.ne']

/-- Let $T \in \mathbb{K}^{n \times n}$ over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$ be lower
triangular and normal. Then $T$ is diagonal, $T = \operatorname{diag}(t_{11}, \dots, t_{nn})$.

The conjugate transpose $T^H$ is upper triangular and normal, so
`Matrix.IsUpperTriangular.eq_diagonal_of_isStarNormal` applies. -/
theorem IsLowerTriangular.eq_diagonal_of_isStarNormal {T : Matrix n n 𝕜}
    (hT : T.IsLowerTriangular) (hN : IsStarNormal T) : T = diagonal fun i => T i i := by
  have hU : (star T).IsUpperTriangular := fun i j hij => by
    rw [star_apply, hT (i := j) (j := i) hij, star_zero]
  have h := congrArg star (hU.eq_diagonal_of_isStarNormal inferInstance)
  rw [star_star] at h
  conv_lhs => rw [h]
  rw [star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1
  funext i
  simp

omit [LinearOrder n] in
/-- Let $A, Q \in \mathbb{K}^{n \times n}$ over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, with
$Q$ unitary. Then $Q^H A Q$ is normal if and only if $A$ is normal.

Conjugation by a unitary matrix is a $*$-automorphism (`Unitary.conjStarAlgAut`), and
$*$-homomorphisms preserve normality. -/
theorem isStarNormal_star_mul_mul_iff {A Q : Matrix n n 𝕜} (hQ : Q ∈ unitaryGroup n 𝕜) :
    IsStarNormal (star Q * A * Q) ↔ IsStarNormal A := by
  have key : ∀ {B P : Matrix n n 𝕜}, P ∈ unitaryGroup n 𝕜 → IsStarNormal B →
      IsStarNormal (star P * B * P) := fun {B P} hP _ => by
    simpa using IsStarNormal.map (Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) (star ⟨P, hP⟩)) B
  refine ⟨fun h => ?_, key hQ⟩
  have := key (Unitary.star_mem hQ) h
  rwa [star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mem_unitaryGroup_iff.1 hQ,
    Matrix.one_mul, Matrix.mul_assoc, mem_unitaryGroup_iff.1 hQ, Matrix.mul_one] at this

/-- **Normality is diagonality of the Schur form.** Let $A, Q \in \mathbb{K}^{n \times n}$ over
$\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, with $Q$ unitary and $T = Q^H A Q$ upper
triangular. Then $A$ is normal if and only if $T$ is diagonal:
$$A^H A = A A^H \iff T = \operatorname{diag}(t_{11}, \dots, t_{nn}).$$
Equivalently, $A$ is normal if and only if the strictly upper triangular part of $T$ vanishes.
This is [golub2013matrix], §9.3.2 and Problem P7.1.1.

The direction from right to left holds because a diagonal matrix is normal and normality is a
unitary invariant (`Matrix.isStarNormal_star_mul_mul_iff`). The direction from left to right is
`Matrix.IsUpperTriangular.eq_diagonal_of_isStarNormal`. The proof is elementary: it uses neither
the spectral theorem nor the Frobenius norm. -/
theorem isStarNormal_iff_strictUpper_eq_zero {A Q : Matrix n n 𝕜} (hQ : Q ∈ unitaryGroup n 𝕜)
    (hT : (star Q * A * Q).IsUpperTriangular) :
    IsStarNormal A ↔ star Q * A * Q = diagonal fun i => (star Q * A * Q) i i := by
  rw [← isStarNormal_star_mul_mul_iff hQ]
  refine ⟨hT.eq_diagonal_of_isStarNormal, fun h => ⟨?_⟩⟩
  rw [h]
  change star (diagonal _) * diagonal _ = diagonal _ * star (diagonal _)
  rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

end Normal

section HermitianSplit

variable {n r s : Type*} [Fintype n] [Fintype r] [Fintype s] [DecidableEq n] [DecidableEq r]
  [DecidableEq s] {𝕜 : Type*} [RCLike 𝕜]

omit [Fintype s] [DecidableEq n] in
/-- **An invariant subspace of a Hermitian matrix splits it.** Let $A \in \mathbb{K}^{n \times n}$
be Hermitian, over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$. Let $Q = [Q_1 \; Q_2]$ with
$Q_1 \in \mathbb{K}^{n \times r}$ and $Q_2 \in \mathbb{K}^{n \times s}$ have orthonormal
columns, $Q^H Q = I$, and suppose that $A Q_1 = Q_1 M$ for some $M \in \mathbb{K}^{r \times r}$.
Then
$$Q^H A Q = \begin{bmatrix} Q_1^H A Q_1 & 0 \\ 0 & Q_2^H A Q_2 \end{bmatrix}.$$
This is [golub2013matrix], Theorem 8.1.9 and (8.1.1), and the Hermitian counterpart of Lemma
7.1.2.

The block $Q_2^H A Q_1 = Q_2^H Q_1 M$ vanishes by orthogonality, and $Q_1^H A Q_2$ is its
conjugate transpose. This is the matrix form of
`LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule`. -/
theorem IsHermitian.conjTranspose_mul_mul_fromCols_eq_fromBlocks {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {Q₁ : Matrix n r 𝕜} {Q₂ : Matrix n s 𝕜}
    (hQ : (fromCols Q₁ Q₂)ᴴ * fromCols Q₁ Q₂ = 1) {M : Matrix r r 𝕜} (hAQ : A * Q₁ = Q₁ * M) :
    (fromCols Q₁ Q₂)ᴴ * A * fromCols Q₁ Q₂ =
      Matrix.fromBlocks (Q₁ᴴ * A * Q₁) 0 0 (Q₂ᴴ * A * Q₂) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, ← fromBlocks_one,
    fromBlocks_inj] at hQ
  have h21 : Q₂ᴴ * A * Q₁ = 0 := by
    rw [Matrix.mul_assoc, hAQ, ← Matrix.mul_assoc, hQ.2.2.1, Matrix.zero_mul]
  have h12 : Q₁ᴴ * A * Q₂ = 0 := by
    have h : (Q₂ᴴ * A * Q₁)ᴴ = Q₁ᴴ * A * Q₂ := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
    rw [← h, h21, conjTranspose_zero]
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols, h12,
    h21]

/-- **The spectrum of a Hermitian matrix split by an invariant subspace.** Let
$A \in \mathbb{K}^{n \times n}$ be Hermitian, over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$.
Let $Q = [Q_1 \; Q_2]$ with $Q_1 \in \mathbb{K}^{n \times r}$ and
$Q_2 \in \mathbb{K}^{n \times s}$ be unitary, $Q^H Q = I$ and $Q Q^H = I$, and suppose that
$A Q_1 = Q_1 M$ for some $M \in \mathbb{K}^{r \times r}$. Then
$$\chi_A = \chi_{Q_1^H A Q_1} \, \chi_{Q_2^H A Q_2}.$$
The eigenvalues of $A$, with multiplicities, are therefore those of the two blocks together.
This is [golub2013matrix], Theorem 8.1.9.

The similarity between matrices indexed by `n` and by `r ⊕ s` is `Matrix.charpoly_mul_comm'`.
The two index types have the same size because $Q$ has full rank as a map in both directions. -/
theorem IsHermitian.charpoly_eq_mul_of_mul_eq_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {Q₁ : Matrix n r 𝕜} {Q₂ : Matrix n s 𝕜} (hQ : (fromCols Q₁ Q₂)ᴴ * fromCols Q₁ Q₂ = 1)
    (hQ' : fromCols Q₁ Q₂ * (fromCols Q₁ Q₂)ᴴ = 1) {M : Matrix r r 𝕜} (hAQ : A * Q₁ = Q₁ * M) :
    A.charpoly = (Q₁ᴴ * A * Q₁).charpoly * (Q₂ᴴ * A * Q₂).charpoly := by
  set Q := fromCols Q₁ Q₂
  have hcard : Fintype.card (r ⊕ s) = Fintype.card n := by
    have h1 : Fintype.card (r ⊕ s) ≤ Fintype.card n := by
      calc Fintype.card (r ⊕ s) = (Qᴴ * Q).rank := by rw [hQ, rank_one]
        _ ≤ Qᴴ.rank := rank_mul_le_left _ _
        _ ≤ Fintype.card n := rank_le_card_width _
    have h2 : Fintype.card n ≤ Fintype.card (r ⊕ s) := by
      calc Fintype.card n = (Q * Qᴴ).rank := by rw [hQ', rank_one]
        _ ≤ Q.rank := rank_mul_le_left _ _
        _ ≤ Fintype.card (r ⊕ s) := rank_le_card_width _
    omega
  have hsim := charpoly_mul_comm' Qᴴ (A * Q)
  rw [Matrix.mul_assoc A, hQ', Matrix.mul_one, hcard, ← Matrix.mul_assoc] at hsim
  have hc : (Qᴴ * A * Q).charpoly = A.charpoly :=
    mul_left_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) hsim
  rw [← hc, hA.conjTranspose_mul_mul_fromCols_eq_fromBlocks hQ hAQ, charpoly_fromBlocks_zero₁₂]

end HermitianSplit


/-! ### Reduction to block triangular form by a known invariant subspace -/

section InvariantBlock

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℕ}

/-- Let $A \in \mathbb{K}^{(p+q) \times (p+q)}$, $B \in \mathbb{K}^{p \times p}$ and
$X \in \mathbb{K}^{(p+q) \times p}$ over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, with
$AX = XB$ and $\operatorname{rank} X = p$. Then there are a unitary $Q$ and blocks
$T_{11} \in \mathbb{K}^{p \times p}$, $T_{12} \in \mathbb{K}^{p \times q}$,
$T_{22} \in \mathbb{K}^{q \times q}$ such that
$$Q^H A Q = \begin{bmatrix} T_{11} & T_{12} \\ 0 & T_{22} \end{bmatrix}$$
and $T_{11}$ is similar to $B$. In particular the eigenvalues of $B$ are eigenvalues of $A$.
This is Lemma 7.1.2 of [golub2013matrix].

The blocks of $Q^H A Q$ are read through `finSumFinEquiv`. The proof takes a unitary $P$ with
$PX = \begin{bmatrix} R_1 \\ 0 \end{bmatrix}$ and $R_1$ upper triangular
(`Matrix.exists_unitary_mul_upperTriangular`), and sets $Q = P^H$. Then $T = Q^H A Q$ satisfies
$T_{21} R_1 = 0$ and $T_{11} R_1 = R_1 B$, and $R_1$ is nonsingular because $X$ has full column
rank. -/
theorem exists_unitary_conj_fromBlocks_of_mul_eq_mul {A : Matrix (Fin (p + q)) (Fin (p + q)) 𝕜}
    {B : Matrix (Fin p) (Fin p) 𝕜} {X : Matrix (Fin (p + q)) (Fin p) 𝕜} (hAX : A * X = X * B)
    (hX : X.rank = p) :
    ∃ Q ∈ unitaryGroup (Fin (p + q)) 𝕜, ∃ (T₁₁ : Matrix (Fin p) (Fin p) 𝕜)
      (T₁₂ : Matrix (Fin p) (Fin q) 𝕜) (T₂₂ : Matrix (Fin q) (Fin q) 𝕜),
      (star Q * A * Q).reindex finSumFinEquiv.symm finSumFinEquiv.symm =
        Matrix.fromBlocks T₁₁ T₁₂ 0 T₂₂ ∧ IsSimilar B T₁₁ := by
  classical
  obtain ⟨P, hP, hPX⟩ := exists_unitary_mul_upperTriangular X
  have hPP : star P * P = 1 := mem_unitaryGroup_iff'.mp hP
  set e : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm
  set T := P * A * star P with hT
  set Y := P * X with hY
  set T' := T.reindex e e
  set R₁ : Matrix (Fin p) (Fin p) 𝕜 := fun i j => Y (Fin.castAdd q i) j
  -- `T Y = Y B`
  have hTY : T * Y = Y * B := by
    simp only [hT, hY, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star P) P X, hPP, Matrix.one_mul, hAX]
  -- the lower rows of `Y` vanish
  have hYlow : ∀ (k : Fin q) (j : Fin p), Y (Fin.natAdd p k) j = 0 := fun k j =>
    hPX _ _ (by simp only [Fin.val_natAdd]; omega)
  -- the rows of `T Y = Y B` in block form
  have hrow : ∀ (x : Fin p ⊕ Fin q) (j : Fin p),
      ∑ i, T' x (Sum.inl i) * R₁ i j = (Y * B) (e.symm x) j := fun x j => by
    rw [← hTY, Matrix.mul_apply, ← e.symm.sum_comp, Fintype.sum_sum_type]
    simp only [e, Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, hYlow,
      mul_zero, Finset.sum_const_zero, add_zero]
    rfl
  -- `R₁` is nonsingular: `X` has full column rank
  have hinj : ∀ v, X *ᵥ v = 0 → v = 0 := by
    have hker := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
    rw [← rank, hX, Module.finrank_fin_fun] at hker
    have h0 : Module.finrank 𝕜 (LinearMap.ker X.mulVecLin) = 0 := by omega
    exact ker_mulVecLin_eq_bot_iff.mp (Submodule.finrank_eq_zero.mp h0)
  have hR₁ : IsUnit R₁ := by
    refine mulVec_injective_iff_isUnit.mp fun v w hvw => ?_
    rw [← sub_eq_zero] at hvw ⊢
    rw [← mulVec_sub] at hvw
    apply hinj
    have hYv : Y *ᵥ (v - w) = 0 := by
      ext i
      refine Fin.addCases (fun i => ?_) (fun k => ?_) i
      · exact congrFun hvw i
      · simp [mulVec, dotProduct, hYlow]
    have := congrArg (star P *ᵥ ·) hYv
    simpa [hY, mulVec_mulVec, ← Matrix.mul_assoc, hPP] using this
  have hRinv : R₁ * R₁⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hR₁)
  -- the blocks
  have h21 : T'.toBlocks₂₁ * R₁ = 0 := by
    ext k j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    have := hrow (Sum.inr k) j
    simp only [e, Equiv.symm_symm, finSumFinEquiv_apply_right] at this
    rw [Matrix.mul_apply] at this
    simpa [toBlocks₂₁, hYlow] using this
  have h11 : T'.toBlocks₁₁ * R₁ = R₁ * B := by
    ext i j
    rw [Matrix.mul_apply]
    have := hrow (Sum.inl i) j
    simp only [e, Equiv.symm_symm, finSumFinEquiv_apply_left] at this
    exact this
  have h21' : T'.toBlocks₂₁ = 0 := by
    rw [← Matrix.mul_one T'.toBlocks₂₁, ← hRinv, ← Matrix.mul_assoc, h21, Matrix.zero_mul]
  refine ⟨star P, Unitary.star_mem hP, T'.toBlocks₁₁, T'.toBlocks₁₂, T'.toBlocks₂₂, ?_, ?_⟩
  · rw [star_star, ← h21', fromBlocks_toBlocks]
  · refine ⟨R₁⁻¹, (isUnit_nonsing_inv_iff).mpr hR₁, ?_⟩
    rw [nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hR₁), ← h11, Matrix.mul_assoc,
      hRinv, Matrix.mul_one]

end InvariantBlock


/-! ### The Schur form with a prescribed order of the eigenvalues -/

section PrescribedOrder

variable {𝕜 : Type*} [RCLike 𝕜]

open Polynomial in
/-- **Schur's theorem with the eigenvalues in a prescribed order.** Let
$A \in \mathbb{K}^{N \times N}$ over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$, and let
$\mu_0, \dots, \mu_{N-1} \in \mathbb{K}$ be its eigenvalues with multiplicity in any order, in
the sense that
$$\chi_A(X) = \prod_{i} (X - \mu_i).$$
Then there is a unitary $Q$ such that $Q^H A Q$ is upper triangular with
$(Q^H A Q)_{ii} = \mu_i$ for every $i$. This is Theorem 7.1.3 of [golub2013matrix], which says
that "$Q$ can be chosen so that the eigenvalues $\lambda_i$ appear in any order along the
diagonal".

Over $\mathbb{R}$ the hypothesis says that the characteristic polynomial splits. The proof is an
induction on $N$. An eigenvector for $\mu_0$ spans an invariant line, which
`Matrix.exists_unitary_conj_fromBlocks_of_mul_eq_mul` splits off as the block $[\mu_0]$. The
characteristic polynomial of the trailing block is the rest of the product, and the induction
hypothesis orders its diagonal. -/
theorem exists_unitary_conj_upperTriangular_diag_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (μ : Fin N → 𝕜) (hμ : A.charpoly = ∏ i, (X - C (μ i))) :
    ∃ Q ∈ unitaryGroup (Fin N) 𝕜, (star Q * A * Q).IsUpperTriangular ∧
      ∀ i, (star Q * A * Q) i i = μ i := by
  classical
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨1, one_mem _, fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨N, rfl⟩ : ∃ N', N = 1 + N' := ⟨N - 1, by omega⟩
  have h0 : (Fin.castAdd N (0 : Fin 1) : Fin (1 + N)) = 0 := Fin.ext rfl
  -- an eigenvector for `μ 0`
  have hroot : (scalar (Fin (1 + N)) (μ 0) - A).det = 0 := by
    rw [← eval_charpoly, hμ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
  obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr hroot
  have hAx : A *ᵥ x = μ 0 • x := by
    rw [sub_mulVec, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec, one_mulVec,
      sub_eq_zero] at hx
    exact hx.symm
  set Xc : Matrix (Fin (1 + N)) (Fin 1) 𝕜 := replicateCol (Fin 1) x with hXdef
  have hAX : A * Xc = Xc * (μ 0 • (1 : Matrix (Fin 1) (Fin 1) 𝕜)) := by
    rw [hXdef, ← replicateCol_mulVec, hAx, Matrix.mul_smul, Matrix.mul_one, replicateCol_smul]
  have hrank : Xc.rank = 1 := by
    refine le_antisymm ((rank_le_card_width Xc).trans (by simp)) (Nat.one_le_iff_ne_zero.mpr ?_)
    intro h0'
    rw [rank, Submodule.finrank_eq_zero] at h0'
    have hmem : Xc.mulVecLin (fun _ => 1) ∈ LinearMap.range Xc.mulVecLin :=
      LinearMap.mem_range_self _ _
    rw [h0', Submodule.mem_bot] at hmem
    apply hx0
    ext i
    simpa [hXdef, mulVec, dotProduct] using congrFun hmem i
  obtain ⟨Q, hQ, T₁₁, T₁₂, T₂₂, hblk, C', hC', hT₁₁⟩ :=
    exists_unitary_conj_fromBlocks_of_mul_eq_mul hAX hrank
  have hT₁₁' : T₁₁ = μ 0 • 1 := by
    rw [hT₁₁, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      nonsing_inv_mul C' ((isUnit_iff_isUnit_det C').mp hC')]
  -- the characteristic polynomial of the trailing block
  have hQQ : star Q * Q = 1 := mem_unitaryGroup_iff'.mp hQ
  have hcp : A.charpoly = (X - C (μ 0)) * T₂₂.charpoly := by
    have hsim : IsSimilar A (star Q * A * Q) :=
      ⟨Q, (isUnit_iff_isUnit_det Q).mpr
        (isUnit_det_of_right_inverse (mem_unitaryGroup_iff.mp hQ)), by rw [inv_eq_left_inv hQQ]⟩
    rw [hsim.charpoly_eq, ← charpoly_reindex finSumFinEquiv.symm, hblk,
      charpoly_fromBlocks_zero₂₁, hT₁₁', smul_one_eq_diagonal, charpoly_diagonal,
      Fin.prod_univ_one]
  have hμ' : T₂₂.charpoly = ∏ k : Fin N, (X - C (μ (Fin.natAdd 1 k))) := by
    rw [hcp, Fin.prod_univ_add, Fin.prod_univ_one, h0] at hμ
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) hμ
  obtain ⟨Q₂, hQ₂, htri₂, hdiag₂⟩ := ih N (by omega) T₂₂ (fun k => μ (Fin.natAdd 1 k)) hμ'
  -- the combined unitary
  set e : Fin (1 + N) ≃ Fin 1 ⊕ Fin N := finSumFinEquiv.symm
  set S : Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) 𝕜 := Matrix.fromBlocks 1 0 0 Q₂ with hSdef
  have hstarS : star S = Matrix.fromBlocks 1 0 0 (star Q₂) := by
    rw [hSdef, star_eq_conjTranspose, fromBlocks_conjTranspose, conjTranspose_one,
      conjTranspose_zero, conjTranspose_zero, star_eq_conjTranspose]
  have hre : ∀ M N' : Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) 𝕜,
      M.reindex e.symm e.symm * N'.reindex e.symm e.symm = (M * N').reindex e.symm e.symm :=
    fun M N' => by simp only [reindex_apply, Equiv.symm_symm, submatrix_mul_equiv]
  have hSu : S.reindex e.symm e.symm ∈ unitaryGroup (Fin (1 + N)) 𝕜 := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_reindex,
      ← star_eq_conjTranspose, hre, hstarS, hSdef, fromBlocks_multiply,
      mem_unitaryGroup_iff.mp hQ₂]
    simp [fromBlocks_one]
  have hAQ : star Q * A * Q = (Matrix.fromBlocks T₁₁ T₁₂ 0 T₂₂).reindex e.symm e.symm := by
    rw [← hblk]
    simp [reindex_apply]
  have hkey : star (Q * S.reindex e.symm e.symm) * A * (Q * S.reindex e.symm e.symm) =
      (Matrix.fromBlocks T₁₁ (T₁₂ * Q₂) 0 (star Q₂ * T₂₂ * Q₂)).reindex e.symm e.symm := by
    have hstarR : star (S.reindex e.symm e.symm) = (star S).reindex e.symm e.symm := by
      rw [star_eq_conjTranspose, conjTranspose_reindex, star_eq_conjTranspose]
    rw [star_mul, hstarR,
      show (star S).reindex e.symm e.symm * star Q * A * (Q * S.reindex e.symm e.symm) =
        (star S).reindex e.symm e.symm * (star Q * A * Q) * S.reindex e.symm e.symm by
        simp only [Matrix.mul_assoc],
      hAQ, hre, hre, hstarS, hSdef, fromBlocks_multiply, fromBlocks_multiply]
    simp
  refine ⟨Q * S.reindex e.symm e.symm, mul_mem hQ hSu, ?_, fun i => ?_⟩
  · intro i j hji
    rw [hkey, reindex_apply, submatrix_apply]
    simp only [Equiv.symm_symm]
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left b =>
        dsimp only [id] at hji ⊢
        have := a.isLt
        have := b.isLt
        exact absurd hji (by simp only [Fin.lt_def, Fin.val_castAdd]; omega)
      | right l =>
        dsimp only [id] at hji ⊢
        have := a.isLt
        exact absurd hji (by simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]; omega)
    | right k =>
      induction j using Fin.addCases with
      | left b =>
        rw [show e (Fin.natAdd 1 k) = Sum.inr k from finSumFinEquiv_symm_apply_natAdd k,
          show e (Fin.castAdd N b) = Sum.inl b from finSumFinEquiv_symm_apply_castAdd b,
          fromBlocks_apply₂₁, Matrix.zero_apply]
      | right l =>
        dsimp only [id] at hji
        rw [show e (Fin.natAdd 1 k) = Sum.inr k from finSumFinEquiv_symm_apply_natAdd k,
          show e (Fin.natAdd 1 l) = Sum.inr l from finSumFinEquiv_symm_apply_natAdd l,
          fromBlocks_apply₂₂]
        refine htri₂ (show l < k from ?_)
        rw [Fin.lt_def] at hji ⊢
        simp only [Fin.val_natAdd] at hji
        omega
  · rw [hkey, reindex_apply, submatrix_apply]
    simp only [Equiv.symm_symm]
    induction i using Fin.addCases with
    | left a =>
      have ha : a = 0 := Subsingleton.elim a 0
      subst ha
      rw [show e (Fin.castAdd N 0) = Sum.inl 0 from finSumFinEquiv_symm_apply_castAdd 0,
        fromBlocks_apply₁₁, hT₁₁', Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, h0]
    | right k =>
      rw [show e (Fin.natAdd 1 k) = Sum.inr k from finSumFinEquiv_symm_apply_natAdd k,
        fromBlocks_apply₂₂]
      exact hdiag₂ k

end PrescribedOrder

end Matrix
