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

This is the classical triangulation of [saad2003iterative] (Theorem 1.9) and [saad2011numerical]
(Theorem 1.5), the source of the *Schur vectors* that deflation techniques for non-normal matrices
work with.

## Main results

* `LinearMap.exists_orthonormalBasis_upperTriangular`: the operator form, an orthonormal basis in
  which the matrix of `A` is `Matrix.IsUpperTriangular`.
* `LinearMap.exists_orthonormalBasis_forall_mem_span`: the same basis described by its flag, each
  initial segment spanning an `A`-invariant subspace.
* `Matrix.exists_unitary_conj_upperTriangular`: the matrix form, `star Q * A * Q` upper triangular
  for a unitary `Q`, with the diagonal of the triangular factor listing the roots of the
  characteristic polynomial.
* `Matrix.mulVec_star_conj_eq_smul_of_mulVec_eq_smul`: similarity moves eigenvectors, which is how
  an eigenvector of the triangular factor is carried back to `A`.
* `Matrix.IsUpperTriangular.schurEigenvector` and
  `Matrix.IsUpperTriangular.mulVec_schurEigenvector`: the eigenvector of an upper triangular
  matrix for a simple diagonal entry, by one triangular solve ([quarteroni2000numerical] §5.8.2,
  (5.56)).

## Implementation notes

The induction is on the dimension, and it descends through the orthogonal complement of an
eigenvector **of the adjoint**: if `A† w = ν w` then `(𝕜 ∙ w)ᗮ` is invariant under `A`, because `⟪w,
A y⟫ = ⟪A† w, y⟫ = conj ν ⟪w, y⟫`. Descending through an eigenvector of `A` itself would leave a
complement that is *not* invariant, and would force the compression `P A|_W` and its orthogonal
projector into the induction. With the adjoint the inductive step needs only `LinearMap.restrict`,
and the new basis vector is appended at the *end* by `Fin.snoc`, which is where an invariant
hyperplane puts it.

Only `Module.End.exists_eigenvalue` uses `[IsAlgClosed 𝕜]`; over `ℝ` the statement is false, as a
plane rotation shows.
-/

open Module Submodule

namespace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The orthogonal complement of an eigenvector of the adjoint is invariant under the operator: `⟪w,
A y⟫ = ⟪A† w, y⟫ = conj ν ⟪w, y⟫` vanishes with `⟪w, y⟫`. -/
theorem mem_orthogonal_singleton_of_adjoint_apply_eq_smul {A : E →ₗ[𝕜] E} {w : E} {ν : 𝕜}
    (hw : A.adjoint w = ν • w) {y : E} (hy : y ∈ (𝕜 ∙ w)ᗮ) : A y ∈ (𝕜 ∙ w)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy ⊢
  rw [← LinearMap.adjoint_inner_left A y w, hw, inner_smul_left, hy, mul_zero]

/-- Schur's theorem in the form the induction produces: an orthonormal basis in which the matrix
entries of `A` below the diagonal, `⟪b i, A (b j)⟫` for `j < i`, all vanish. The space is quantified
inside the statement because the induction descends to a hyperplane of it. -/
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

/-- **Schur's theorem**, operator form: an operator on a finite-dimensional inner product space over
an algebraically closed field has an orthonormal basis in which its matrix is upper triangular. The
proof is an induction on the dimension through the orthogonal complement of an eigenvector of the
adjoint, which is an invariant hyperplane. -/
theorem exists_orthonormalBasis_upperTriangular {n : ℕ} (hn : finrank 𝕜 E = n) (A : E →ₗ[𝕜] E) :
    ∃ b : OrthonormalBasis (Fin n) 𝕜 E,
      (LinearMap.toMatrix b.toBasis b.toBasis A).IsUpperTriangular := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_forall_inner_eq_zero 𝕜 n hn A
  refine ⟨b, fun i j hji => ?_⟩
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  exact hb i j hji

/-- The Schur basis described by its flag: each initial segment `b 0, …, b j` spans an `A`-invariant
subspace, which is what makes the matrix of `A` upper triangular. These are the *Schur vectors* of
`A`. -/
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

namespace Matrix

/-! ### Similarity moves eigenvectors -/

section Conj

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Similarity moves eigenvectors** ([quarteroni2000numerical] Exercise 5.9): if `A x = μ x` and
`U` is nonsingular then `(U⁻¹ A U)(U⁻¹ x) = μ (U⁻¹ x)`. -/
theorem mulVec_conj_eq_smul_of_mulVec_eq_smul {R : Type*} [CommRing R] {A U : Matrix n n R}
    (hU : IsUnit U) {μ : R} {x : n → R} (hx : A *ᵥ x = μ • x) :
    (U⁻¹ * A * U) *ᵥ (U⁻¹ *ᵥ x) = μ • (U⁻¹ *ᵥ x) := by
  rw [mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hU),
    Matrix.mul_one, ← mulVec_mulVec, hx, mulVec_smul]

/-- The unitary form of `Matrix.mulVec_conj_eq_smul_of_mulVec_eq_smul`: if `A x = μ x` and `U` is
unitary then `(Uᴴ A U)(Uᴴ x) = μ (Uᴴ x)`. This is how an eigenvector of the Hessenberg or Schur
form of `A` is carried back to `A`, `x = U y`. -/
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

/-- The eigenvector of an upper triangular matrix `T` for a *simple* diagonal entry `λ = T k k`,
read off the Schur form as in [quarteroni2000numerical] §5.8.2, (5.56): with `T` partitioned around
row `k` as `[T₁₁ v T₁₃; 0 λ wᵀ; 0 0 T₃₃]`, the vector is `(-(T₁₁ - λ I)⁻¹ v, 1, 0)`. It is defined
for every `T` and `k` through `Matrix.inv`, and is an eigenvector when `λ` is not a diagonal
entry of `T₁₁` (`Matrix.IsUpperTriangular.mulVec_schurEigenvector`). -/
noncomputable def schurEigenvector (T : Matrix (Fin N) (Fin N) K) (k : Fin N) : Fin N → K :=
  fun i =>
    if h : (i : ℕ) < k then
      -(((T.submatrix (Fin.castLE k.isLt.le) (Fin.castLE k.isLt.le) - T k k • 1)⁻¹
        *ᵥ fun j => T (Fin.castLE k.isLt.le j) k) ⟨i, h⟩)
    else if i = k then 1 else 0

/-- The `k`-th entry of the Schur eigenvector is `1`. -/
@[simp]
theorem schurEigenvector_apply_self (T : Matrix (Fin N) (Fin N) K) (k : Fin N) :
    schurEigenvector T k k = 1 := by
  simp [schurEigenvector]

/-- The Schur eigenvector vanishes below the row `k`. -/
theorem schurEigenvector_apply_of_lt (T : Matrix (Fin N) (Fin N) K) {k i : Fin N} (h : k < i) :
    schurEigenvector T k i = 0 := by
  have h1 : ¬ ((i : ℕ) < k) := not_lt.2 (Fin.le_def.1 h.le)
  rw [schurEigenvector, dite_eq_right h1, ite_eq_right h.ne']

/-- The Schur eigenvector is nonzero, its `k`-th entry being `1`. -/
theorem schurEigenvector_ne_zero (T : Matrix (Fin N) (Fin N) K) (k : Fin N) :
    schurEigenvector T k ≠ 0 := fun h => by
  simpa using congrFun h k

/-- A sum over the indices below `k` is a sum over `Fin k`. -/
private theorem sum_filter_lt_eq_sum_castLE {k : ℕ} (hk : k ≤ N) (g : Fin N → K) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < k), g j
      = ∑ j : Fin k, g (Fin.castLE hk j) := by
  rw [show (∑ j : Fin k, g (Fin.castLE hk j)) = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hk), g j from
    (Finset.sum_map Finset.univ (Fin.castLEEmb hk) g).symm]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
  constructor
  · intro hj
    exact ⟨⟨j, hj⟩, Fin.ext rfl⟩
  · rintro ⟨i, rfl⟩
    exact i.isLt

/-- The leading block of an upper triangular matrix, shifted by a scalar, is upper triangular. -/
private theorem isUpperTriangular_submatrix_castLE_sub {T : Matrix (Fin N) (Fin N) K}
    (hT : T.IsUpperTriangular) {k : ℕ} (hk : k ≤ N) (c : K) :
    (T.submatrix (Fin.castLE hk) (Fin.castLE hk) - c • 1).IsUpperTriangular := by
  intro i j hji
  rw [sub_apply, submatrix_apply, smul_apply, one_apply,
    ite_eq_right (fun h : i = j => absurd h (ne_of_gt hji)), smul_zero, sub_zero]
  exact hT (Fin.lt_def.2 (by simp only [id, Fin.val_castLE]; exact Fin.lt_def.1 hji))

/-- **The Schur eigenvector is an eigenvector** ([quarteroni2000numerical] §5.8.2, (5.56)): for
`T` upper triangular and a diagonal entry `λ = T k k` that is not repeated above row `k`,
`T y = λ y` for `y = schurEigenvector T k`. Rows below `k` vanish on both sides, row `k` reads
`λ · 1`, and the rows above `k` are the triangular system `(T₁₁ - λ I) y₁ = -v` that defines `y₁`.
Together with `Matrix.mulVec_star_conj_eq_smul_of_mulVec_eq_smul` and
`Matrix.exists_unitary_conj_upperTriangular` this computes an eigenvector `x = Q y` of `A` for each
simple eigenvalue from its Schur form. -/
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
    rw [hT₁₁, det_of_isUpperTriangular (isUpperTriangular_submatrix_castLE_sub hT hle _)]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    rw [sub_apply, submatrix_apply, smul_apply, one_apply_eq, smul_eq_mul, mul_one]
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
    rw [sum_filter_lt_eq_sum_castLE hle]
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
