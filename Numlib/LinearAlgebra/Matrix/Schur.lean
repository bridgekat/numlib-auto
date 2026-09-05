/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Schur`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Sort
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The Schur triangulation

**Schur's theorem**: an operator on a finite-dimensional inner product space over an algebraically
closed field is upper triangular in some *orthonormal* basis, and a square matrix over such a field
is therefore unitarily similar to an upper triangular matrix, `A = Q R Qᴴ` with `Q` unitary. The
diagonal of `R` then carries the eigenvalues of `A` with their multiplicities, since the
characteristic polynomial of a triangular matrix is the product of `X - r_ii` and conjugation does
not change it.

This is the classical triangulation of Saad, *Iterative Methods for Sparse Linear
Systems*[^saad-iterative] (Theorem 1.9) and Saad, *Numerical Methods for Large Eigenvalue
Problems*[^saad-eigenvalue] (Theorem 1.5), the source of the *Schur vectors* that deflation
techniques for non-normal matrices work with.

## Main results

* `LinearMap.exists_orthonormalBasis_upperTriangular`: the operator form, an orthonormal basis in
  which the matrix of `A` is `Matrix.IsUpperTriangular`.
* `LinearMap.exists_orthonormalBasis_forall_mem_span`: the same basis described by its flag, each
  initial segment spanning an `A`-invariant subspace.
* `Matrix.exists_unitary_conj_upperTriangular`: the matrix form, `star Q * A * Q` upper triangular
  for a unitary `Q`, with the diagonal of the triangular factor listing the roots of the
  characteristic polynomial.

## Implementation notes

The induction is on the dimension, and it descends through the orthogonal complement of an
eigenvector **of the adjoint**: if `A† w = ν w` then `(𝕜 ∙ w)ᗮ` is invariant under `A`, because
`⟪w, A y⟫ = ⟪A† w, y⟫ = conj ν ⟪w, y⟫`. Descending through an eigenvector of `A` itself would leave
a complement that is *not* invariant, and would force the compression `P A|_W` and its orthogonal
projector into the induction. With the adjoint the inductive step needs only
`LinearMap.restrict`, and the new basis vector is appended at the *end* by `Fin.snoc`, which is
where an invariant hyperplane puts it.

Only `Module.End.exists_eigenvalue` uses `[IsAlgClosed 𝕜]`; over `ℝ` the statement is false, as a
plane rotation shows.

## References

[^saad-iterative]: Yousef Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition,
  SIAM, 2003.
[^saad-eigenvalue]: Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, 2nd edition,
  SIAM, 2011.
-/

open Module Submodule

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The orthogonal complement of an eigenvector of the adjoint is invariant under the operator:
`⟪w, A y⟫ = ⟪A† w, y⟫ = conj ν ⟪w, y⟫` vanishes with `⟪w, y⟫`. -/
theorem mem_orthogonal_singleton_of_adjoint_apply_eq_smul {A : E →ₗ[𝕜] E} {w : E} {ν : 𝕜}
    (hw : A.adjoint w = ν • w) {y : E} (hy : y ∈ (𝕜 ∙ w)ᗮ) : A y ∈ (𝕜 ∙ w)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy ⊢
  rw [← LinearMap.adjoint_inner_left A y w, hw, inner_smul_left, hy, mul_zero]

/-- Schur's theorem in the form the induction produces: an orthonormal basis in which the matrix
entries of `A` below the diagonal, `⟪b i, A (b j)⟫` for `j < i`, all vanish. The space is
quantified inside the statement because the induction descends to a hyperplane of it. -/
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

/-- **Schur's theorem**, operator form: an operator on a finite-dimensional inner product space
over an algebraically closed field has an orthonormal basis in which its matrix is upper
triangular. The proof is an induction on the dimension through the orthogonal complement of an
eigenvector of the adjoint, which is an invariant hyperplane. -/
theorem exists_orthonormalBasis_upperTriangular {n : ℕ} (hn : finrank 𝕜 E = n) (A : E →ₗ[𝕜] E) :
    ∃ b : OrthonormalBasis (Fin n) 𝕜 E,
      (LinearMap.toMatrix b.toBasis b.toBasis A).IsUpperTriangular := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_forall_inner_eq_zero 𝕜 n hn A
  refine ⟨b, fun i j hji => ?_⟩
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  exact hb i j hji

/-- The Schur basis described by its flag: each initial segment `b 0, …, b j` spans an
`A`-invariant subspace, which is what makes the matrix of `A` upper triangular. These are the
*Schur vectors* of `A`. -/
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
/-- **Schur's theorem**, matrix form: a square matrix over an algebraically closed `RCLike` field —
that is, over `Complex` — is unitarily similar to an upper triangular matrix, `star Q * A * Q = R`
with `Q` unitary and `R` upper triangular. The diagonal of `R` lists the eigenvalues of `A` with
their multiplicities, in the sense that the characteristic polynomial of `A` is the product of the
`X - r_ii`: conjugation leaves the characteristic polynomial alone, and that of a triangular matrix
is read off its diagonal. -/
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
