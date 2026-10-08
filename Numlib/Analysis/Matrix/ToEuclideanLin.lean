/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.UnitaryEquiv

/-!
# Matrices as operators on `EuclideanSpace`

Glue between `Matrix m n 𝕜` and `Matrix.toEuclideanLin A : EuclideanSpace 𝕜 n →ₗ EuclideanSpace 𝕜 m`
used by every matrix-level surface statement: multiplicativity, powers, adjoint = conjugate
transpose, eigenvalues, and the `‖A‖₂ = ‖toEuclideanLin A‖` identification. (Symmetric ↔ Hermitian
is Mathlib's `Matrix.isSymmetric_toEuclideanLin_iff`, and its one-directional form for a symmetric
matrix over a trivial-star field — the real symmetric case — is
`Matrix.IsSymm.isSymmetric_toEuclideanLin` here; `Matrix.PosDef` ↔ symmetric coercive is
`Matrix.posDef_iff_isSymmetricCoercive`; reading a Krylov subspace of `toEuclideanLin A` as a span
of columns is `Matrix.krylov_subspace_toEuclideanLin` in `Numlib.Krylov.ToEuclideanLin`, which this
module cannot depend on.)

Everything that makes sense for a rectangular matrix is stated for one, over arbitrary `Fintype`
index types: composition `toEuclideanLin (A * B) = toEuclideanLin A ∘ₗ toEuclideanLin B` and its
applied form, the adjoint identities `⟪Aᴴ y, x⟫ = ⟪y, A x⟫` and `⟪x, Aᴴ y⟫ = ⟪A x, y⟫` (with their
real forms for `Aᵀ`, `Matrix.toEuclideanLin_transpose_inner_left` and `_right`, and the real inner
product of coordinate vectors `EuclideanSpace.inner_toLp_toLp_real`), and the
coordinate identifications `WithLp.ofLp (toEuclideanLin A x) = A *ᵥ WithLp.ofLp x` and
`toEuclideanLin A (WithLp.toLp 2 v) = WithLp.toLp 2 (A *ᵥ v)`, which are `rfl` but are what `rw`
needs to move between the operator picture and `Matrix.mulVec`.

It also contains the fact that a unitary matrix acts as an isometry of `EuclideanSpace`,
`‖U *ᵥ v‖₂ = ‖v‖₂`: transport `U` along the star algebra equivalence `Matrix.toEuclideanCLM`
and use that a unitary continuous linear endomorphism of a Hilbert space preserves the norm
(`ContinuousLinearMap.norm_map_of_mem_unitary`).

Five further groups of glue, each of which is otherwise re-proved wherever a matrix statement is
transported to the operator picture:

* the *applied* forms of the linear-equivalence laws, `toEuclideanLin (A - B) v =
  toEuclideanLin A v - toEuclideanLin B v` and its companions for `0`, `1`, `-` and `•`, which are
  `map_sub` and friends followed by the pointwise definition of the operations on linear maps;
* *inversion*, `toEuclideanCLM A⁻¹ = Ring.inverse (toEuclideanCLM A)` for an invertible `A`,
  reconciling Mathlib's junk-valued `Matrix.inv` with `Ring.inverse` on the operator algebra,
  together with the two cancellations `toEuclideanLin A (toEuclideanLin A⁻¹ z) = z` and
  `toEuclideanLin A⁻¹ (toEuclideanLin A z) = z` it gives;
* the *shift* `A + r I` of a matrix by a multiple of the identity, the shape of a resolvent and of
  every regularized or shifted system, whose image is the shift `toEuclideanCLM A + r • 1` of the
  operator;
* *column spaces*: `ran A` is the span of the columns (`Matrix.range_toEuclideanLin_eq_span_col`),
  `Qᴴ Q = 1` says the columns are orthonormal
  (`Matrix.conjTranspose_mul_self_eq_one_iff_orthonormal`), the two column blocks of a unitary
  `[Q_α Q_β]` span orthogonal complements (`Matrix.range_eq_orthogonal_of_fromCols`, and
  `Matrix.range_submatrix_eq_orthogonal` for complementary column selections), a unitary `V`
  carries `ran M` to `ran (V M)` isometrically
  (`Matrix.range_mul_eq_map_of_mul_conjTranspose_eq_one`), and orthonormal columns span a space of
  their number (`Matrix.finrank_range_of_conjTranspose_mul_self_eq_one`);
* *injectivity* of `Matrix.toEuclideanCLM` for the coercion its applications use
  (`Matrix.toEuclideanCLM_injective`), because `StarAlgEquiv.injective` speaks about the underlying
  ring equivalence and leaves a goal phrased in `toRingEquiv`.
-/

/-- The real inner product of two coordinate vectors is their dot product: Mathlib's
`EuclideanSpace.inner_toLp_toLp` with the trivial star dropped and the factors in order. -/
theorem EuclideanSpace.inner_toLp_toLp_real {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ ι) (WithLp.toLp 2 v) = u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The identity matrix acts as the identity operator. -/
@[simp]
theorem toEuclideanLin_one : toEuclideanLin (1 : Matrix n n 𝕜) = LinearMap.id :=
  toLpLin_one 2

/-- Matrix multiplication is composition of the operators, for rectangular matrices as well; on
square ones it makes `toEuclideanLin` a morphism of algebras and not merely a linear map. -/
theorem toEuclideanLin_mul {m o : Type*} [Fintype o] [DecidableEq o] (A : Matrix m n 𝕜)
    (B : Matrix n o 𝕜) : toEuclideanLin (A * B) = toEuclideanLin A ∘ₗ toEuclideanLin B :=
  toLpLin_mul_same 2 A B

/-- Applying a product of matrices is applying them one after the other: the applied form of
`Matrix.toEuclideanLin_mul`. -/
theorem toEuclideanLin_mul_apply {m o : Type*} [Fintype o] [DecidableEq o] (A : Matrix m n 𝕜)
    (B : Matrix n o 𝕜) (x : EuclideanSpace 𝕜 o) :
    toEuclideanLin (A * B) x = toEuclideanLin A (toEuclideanLin B x) := by
  rw [toEuclideanLin_mul, LinearMap.comp_apply]

/-- Powers of a matrix act as powers of the operator; this is what lets a Krylov subspace of a
matrix be read as a Krylov subspace of `toEuclideanLin A`. -/
theorem toEuclideanLin_pow (A : Matrix n n 𝕜) (k : ℕ) :
    toEuclideanLin (A ^ k) = toEuclideanLin A ^ k :=
  toLpLin_pow 2 A k

/-- `p(A)` as an operator is `p` of the operator: `Matrix.toEuclideanLin` is an algebra map. -/
theorem toEuclideanLin_aeval (A : Matrix n n 𝕜) (p : Polynomial 𝕜) :
    toEuclideanLin (Polynomial.aeval A p) = Polynomial.aeval (toEuclideanLin A) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def, map_smul, toEuclideanLin_pow]

/-- The algebraic multiplicity of an eigenvalue of a matrix, the multiplicity of `μ` as a root of
the characteristic polynomial, is the dimension of the generalized eigenspace of
`toEuclideanLin A`: Mathlib's `LinearMap.finrank_maxGenEigenspace_eq` read through
`Matrix.charpoly_toLin`. -/
theorem finrank_maxGenEigenspace_toEuclideanLin (A : Matrix n n 𝕜) (μ : 𝕜) :
    Module.finrank 𝕜 (Module.End.maxGenEigenspace (toEuclideanLin A) μ) =
      A.charpoly.rootMultiplicity μ := by
  rw [LinearMap.finrank_maxGenEigenspace_eq, toEuclideanLin_eq_toLin_orthonormal, charpoly_toLin]

/-- The adjoint of `toEuclideanLin A` is `toEuclideanLin Aᴴ`. -/
theorem toEuclideanLin_conjTranspose {m : Type*} [Fintype m] [DecidableEq m] (A : Matrix m n 𝕜) :
    toEuclideanLin Aᴴ = LinearMap.adjoint (toEuclideanLin A) :=
  toEuclideanLin_conjTranspose_eq_adjoint A

/-- `⟪Aᴴ y, x⟫ = ⟪y, A x⟫`: the conjugate transpose moves across the inner product as the adjoint
does (`LinearMap.adjoint_inner_left`). -/
theorem toEuclideanLin_conjTranspose_inner_left {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    inner 𝕜 (toEuclideanLin Aᴴ y) x = inner 𝕜 y (toEuclideanLin A x) := by
  rw [toEuclideanLin_conjTranspose, LinearMap.adjoint_inner_left]

/-- `⟪x, Aᴴ y⟫ = ⟪A x, y⟫`: the conjugate transpose moves across the inner product as the adjoint
does (`LinearMap.adjoint_inner_right`). -/
theorem toEuclideanLin_conjTranspose_inner_right {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    inner 𝕜 x (toEuclideanLin Aᴴ y) = inner 𝕜 (toEuclideanLin A x) y := by
  rw [toEuclideanLin_conjTranspose, LinearMap.adjoint_inner_right]

/-- Over a field with trivial star (`ℝ`), the adjoint of `toEuclideanLin A` is `toEuclideanLin Aᵀ`,
for rectangular matrices too: `Matrix.toEuclideanLin_conjTranspose` with `Aᴴ = Aᵀ`. -/
theorem toEuclideanLin_transpose_eq_adjoint [TrivialStar 𝕜] {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m n 𝕜) :
    toEuclideanLin Aᵀ = LinearMap.adjoint (toEuclideanLin A) := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose]

/-- `⟪Aᵀ y, x⟫ = ⟪y, A x⟫` over a field with trivial star: the real form of
`Matrix.toEuclideanLin_conjTranspose_inner_left`. -/
theorem toEuclideanLin_transpose_inner_left [TrivialStar 𝕜] {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    inner 𝕜 (toEuclideanLin Aᵀ y) x = inner 𝕜 y (toEuclideanLin A x) := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_inner_left]

/-- `⟪x, Aᵀ y⟫ = ⟪A x, y⟫` over a field with trivial star: the real form of
`Matrix.toEuclideanLin_conjTranspose_inner_right`. -/
theorem toEuclideanLin_transpose_inner_right [TrivialStar 𝕜] {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 m) :
    inner 𝕜 x (toEuclideanLin Aᵀ y) = inner 𝕜 (toEuclideanLin A x) y := by
  rw [← conjTranspose_eq_transpose_of_trivial, toEuclideanLin_conjTranspose_inner_right]

/-- A symmetric matrix over a field with trivial star — a real symmetric matrix, in practice —
acts as a symmetric operator on `EuclideanSpace`. This is the direction of Mathlib's
`Matrix.isSymmetric_toEuclideanLin_iff` that a real statement needs, with the symmetric-is-Hermitian
step (`Matrix.isHermitian_iff_isSymm`) already taken. -/
theorem IsSymm.isSymmetric_toEuclideanLin [TrivialStar 𝕜] {A : Matrix n n 𝕜} (hA : A.IsSymm) :
    (toEuclideanLin A).IsSymmetric :=
  isSymmetric_toEuclideanLin_iff.mpr (isHermitian_iff_isSymm.mpr hA)

/-- Eigenvalues of the operator are the eigenvalues of the matrix. -/
theorem hasEigenvalue_toEuclideanLin_iff (A : Matrix n n 𝕜) (μ : 𝕜) :
    Module.End.HasEigenvalue (toEuclideanLin A) μ ↔ μ ∈ spectrum 𝕜 A := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, spectrum_toLpLin]

/-- For Hermitian `A`, the eigenvalues of `toEuclideanLin A` are Mathlib's
`Matrix.IsHermitian.eigenvalues`. -/
theorem IsHermitian.hasEigenvalue_toEuclideanLin_iff {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (μ : 𝕜) : Module.End.HasEigenvalue (toEuclideanLin A) μ ↔ ∃ i, (hA.eigenvalues i : 𝕜) = μ := by
  rw [Matrix.hasEigenvalue_toEuclideanLin_iff, hA.spectrum_eq_image_range]
  simp [eq_comm]

/-- The quadratic-form bounds of a Hermitian matrix are its extreme eigenvalues. -/
theorem IsHermitian.isSymmetricBoundedBy_toEuclideanLin {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (h : ∀ i, hA.eigenvalues i ∈ Set.Icc lmin lmax) :
    (toEuclideanLin A).IsSymmetricBoundedBy lmin lmax := by
  refine (LinearMap.IsSymmetric.isSymmetricBoundedBy_iff_forall_hasEigenvalue
    (isSymmetric_toEuclideanLin_iff.mpr hA) lmin lmax).mpr fun μ hμ => ?_
  obtain ⟨i, rfl⟩ := (hA.hasEigenvalue_toEuclideanLin_iff μ).mp hμ
  simpa using h i

section Coordinates

/-! ### Coordinates

`Matrix.toEuclideanLin A` is `Matrix.mulVec` transported along `WithLp.toLp 2` / `WithLp.ofLp`, for
a rectangular `A` as well as a square one. The identifications are definitional, and are stated so
that `rw` and `simp only` can pass between the operator picture and the coordinate one in either
direction. -/

variable {m : Type*}

/-- `Matrix.toEuclideanLin` in coordinates: under `WithLp.ofLp`, the action of a matrix on a
Euclidean vector is `Matrix.mulVec`. -/
theorem ofLp_toEuclideanLin (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    WithLp.ofLp (toEuclideanLin A x) = A *ᵥ WithLp.ofLp x := rfl

/-- `Matrix.toEuclideanLin` in coordinates, in the `WithLp.toLp` direction. -/
theorem toEuclideanLin_toLp (A : Matrix m n 𝕜) (v : n → 𝕜) :
    toEuclideanLin A (WithLp.toLp 2 v) = WithLp.toLp 2 (A *ᵥ v) := rfl

/-- `Matrix.toEuclideanLin` unfolded on an arbitrary vector. -/
theorem toEuclideanLin_apply (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    toEuclideanLin A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

omit [Fintype n] [DecidableEq n] in
/-- `V y = ∑ y_j • (column j of V)`: moving between the book's `V_m y` and the backbone's
`∑ y_j • vec j`. -/
theorem toEuclideanLin_apply_eq_sum [Fintype m] [DecidableEq m] (V : Matrix n m 𝕜) (y : m → 𝕜) :
    toEuclideanLin V (WithLp.toLp 2 y) =
      ∑ j, y j • (WithLp.toLp 2 (Vᵀ j) : EuclideanSpace 𝕜 n) := by
  ext i
  simp [toLpLin_apply, mulVec, dotProduct, mul_comm]

end Coordinates

section Columns

/-! ### Ranges and orthonormality of columns -/

variable {m : Type*}

omit [Fintype n] [DecidableEq n] in
/-- The range of `toEuclideanLin M` is the span of the columns of `M`. -/
theorem range_toEuclideanLin_eq_span_col [Fintype m] [DecidableEq m] (M : Matrix n m 𝕜) :
    LinearMap.range (toEuclideanLin M) =
      Submodule.span 𝕜 (Set.range fun j => WithLp.toLp 2 (M.col j)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hx := toEuclideanLin_apply_eq_sum M (WithLp.ofLp x)
    simp only [WithLp.toLp_ofLp] at hx
    rw [hx]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨WithLp.toLp 2 (Pi.single j 1), by rw [toEuclideanLin_toLp, mulVec_single_one]⟩

omit [Fintype n] [DecidableEq n] in
/-- The column space of a one-column matrix is the line through its column. -/
theorem range_toEuclideanLin_replicateCol [Fintype m] [DecidableEq m] [Nonempty m] (x : n → 𝕜) :
    LinearMap.range (toEuclideanLin (replicateCol m x)) = 𝕜 ∙ WithLp.toLp 2 x := by
  rw [range_toEuclideanLin_eq_span_col]
  have h : (fun j : m => WithLp.toLp 2 ((replicateCol m x).col j)) = fun _ => WithLp.toLp 2 x :=
    rfl
  rw [h, Set.range_const]

omit [DecidableEq n] in
/-- `Qᴴ Q = 1` iff the columns of `Q` are orthonormal in `EuclideanSpace`. -/
theorem conjTranspose_mul_self_eq_one_iff_orthonormal [DecidableEq m] {Q : Matrix n m 𝕜} :
    Qᴴ * Q = 1 ↔ Orthonormal 𝕜 fun j => WithLp.toLp 2 (Q.col j) := by
  rw [orthonormal_iff_ite, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, one_apply, mul_apply]
  rfl

omit [DecidableEq n] in
/-- `Qᴴ r = 0` iff `r` is orthogonal to the columns of `Q`. -/
theorem conjTranspose_mulVec_eq_zero_iff {Q : Matrix n m 𝕜} {r : n → 𝕜} :
    Qᴴ *ᵥ r = 0 ↔ ∀ j, inner 𝕜 (WithLp.toLp 2 (Q.col j)) (WithLp.toLp 2 r) = 0 := by
  rw [funext_iff]
  refine forall_congr' fun j => ?_
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rfl

/-- For a unitary `Q = [Q_α Q_β]` split into two column blocks, `ran Q_β = (ran Q_α)ᗮ`. -/
theorem range_eq_orthogonal_of_fromCols {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s]
    [DecidableEq s] {Qα : Matrix n r 𝕜} {Qβ : Matrix n s 𝕜}
    (hQ : (fromCols Qα Qβ)ᴴ * fromCols Qα Qβ = 1)
    (hQ' : fromCols Qα Qβ * (fromCols Qα Qβ)ᴴ = 1) :
    LinearMap.range (toEuclideanLin Qβ) = (LinearMap.range (toEuclideanLin Qα))ᗮ := by
  have hαβ : Qαᴴ * Qβ = 0 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
      ← fromBlocks_one] at hQ
    exact (fromBlocks_inj.1 hQ).2.1
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromCols_mul_fromRows] at hQ'
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨z, rfl⟩
    rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← toEuclideanLin_mul_apply, hαβ, map_zero, LinearMap.zero_apply, inner_zero_right]
  · intro x hx
    have h0 : toEuclideanLin Qαᴴ x = 0 := by
      rw [toEuclideanLin_conjTranspose_eq_adjoint]
      refine ext_inner_left 𝕜 fun z => ?_
      rw [LinearMap.adjoint_inner_right, inner_zero_right]
      exact (Submodule.mem_orthogonal _ _).1 hx _ ⟨z, rfl⟩
    refine ⟨toEuclideanLin Qβᴴ x, ?_⟩
    have h := congrArg (fun M => toEuclideanLin M x) hQ'
    simp only [map_add, LinearMap.add_apply, toEuclideanLin_mul_apply, h0, map_zero, zero_add,
      toLpLin_one, LinearMap.id_apply] at h
    exact h

/-- **Complementary column selections of a unitary matrix span orthogonal complements**: if
`Sum.elim f g` is a bijection onto the columns of a unitary `V`, then
`ran V(:, g) = (ran V(:, f))ᗮ` ([golub2013matrix] §2.1.5, after Theorem 2.1.1). The selections
put side by side are `V` with its columns permuted, so this is
`Matrix.range_eq_orthogonal_of_fromCols`. -/
theorem range_submatrix_eq_orthogonal {r s : Type*} [Fintype r] [DecidableEq r] [Fintype s]
    [DecidableEq s] {V : Matrix n n 𝕜} (hV : V ∈ unitaryGroup n 𝕜) {f : r → n} {g : s → n}
    (hfg : Function.Bijective (Sum.elim f g)) :
    LinearMap.range (toEuclideanLin (V.submatrix id g))
      = (LinearMap.range (toEuclideanLin (V.submatrix id f)))ᗮ := by
  have hW : fromCols (V.submatrix id f) (V.submatrix id g)
      = V.submatrix id (Equiv.ofBijective _ hfg) := by
    ext i (j | j) <;> rfl
  refine range_eq_orthogonal_of_fromCols ?_ ?_ <;> rw [hW]
  · rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
      ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hV, submatrix_one_equiv]
  · rw [conjTranspose_submatrix, submatrix_mul_equiv, ← star_eq_conjTranspose,
      mem_unitaryGroup_iff.1 hV, submatrix_id_id]

end Columns

open scoped Matrix.Norms.L2Operator in
/-- The `2`-operator norm of a matrix is the operator norm of `toEuclideanLin A`. -/
theorem l2_opNorm_eq_norm_toEuclideanLin (A : Matrix n n 𝕜) :
    ‖A‖ = ‖LinearMap.toContinuousLinearMap (toEuclideanLin A)‖ :=
  l2_opNorm_def A

section Unitary

variable {U : Matrix n n 𝕜}

/-- A unitary matrix becomes a unitary operator on `EuclideanSpace 𝕜 n`. -/
theorem toEuclideanCLM_mem_unitary (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) U ∈
      unitary (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) := by
  rw [Unitary.mem_iff] at hU ⊢
  refine ⟨?_, ?_⟩
  · rw [← map_star, ← map_mul, hU.1, map_one]
  · rw [← map_star, ← map_mul, hU.2, map_one]

/-- A unitary matrix acts as an isometry of `EuclideanSpace 𝕜 n`. -/
theorem norm_toEuclideanCLM_apply_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (x : EuclideanSpace 𝕜 n) : ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) U x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (toEuclideanCLM_mem_unitary hU) x

/-- A unitary matrix preserves the Euclidean norm: `‖U *ᵥ v‖₂ = ‖v‖₂`. -/
theorem norm_toLp_mulVec_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup n 𝕜) (v : n → 𝕜) :
    ‖(WithLp.toLp 2 (U *ᵥ v) : EuclideanSpace 𝕜 n)‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace 𝕜 n)‖ := by
  rw [← toEuclideanCLM_toLp U v]
  exact norm_toEuclideanCLM_apply_of_mem_unitaryGroup hU _

/-- A unitary matrix preserves Euclidean inner products. -/
theorem inner_toLp_mulVec_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup n 𝕜) (v w : n → 𝕜) :
    inner 𝕜 (WithLp.toLp 2 (U *ᵥ v) : EuclideanSpace 𝕜 n)
        (WithLp.toLp 2 (U *ᵥ w) : EuclideanSpace 𝕜 n) =
      inner 𝕜 (WithLp.toLp 2 v : EuclideanSpace 𝕜 n) (WithLp.toLp 2 w : EuclideanSpace 𝕜 n) := by
  rw [← toEuclideanCLM_toLp U v, ← toEuclideanCLM_toLp U w]
  exact ContinuousLinearMap.inner_map_map_of_mem_unitary (toEuclideanCLM_mem_unitary hU) _ _

/-- A unitary matrix acts isometrically on `EuclideanSpace`, in the `toEuclideanLin` form. -/
theorem norm_toEuclideanLin_apply_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (x : EuclideanSpace 𝕜 n) : ‖toEuclideanLin U x‖ = ‖x‖ := by
  rw [toEuclideanLin_apply, norm_toLp_mulVec_of_mem_unitaryGroup hU]

/-- A unitary matrix is a unit, with inverse `star Q`. -/
theorem isUnit_of_mem_unitaryGroup (hU : U ∈ Matrix.unitaryGroup n 𝕜) : IsUnit U :=
  ⟨⟨U, star U, mem_unitaryGroup_iff.mp hU, mem_unitaryGroup_iff'.mp hU⟩, rfl⟩

/-- The similarity `Uᴴ A U` by a unitary matrix does not change the spectrum. -/
theorem spectrum_conjTranspose_mul_mul {A : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    spectrum 𝕜 (Uᴴ * A * U) = spectrum 𝕜 A := by
  have hu : IsUnit U := isUnit_of_mem_unitaryGroup hU
  have hinv : U⁻¹ = Uᴴ :=
    inv_eq_left_inv (conjTranspose_mul_self_of_mem_unitaryGroup hU)
  have h := spectrum.units_conjugate' (R := 𝕜) (a := A) (u := hu.unit)
  rwa [coe_units_inv, IsUnit.unit_spec, hinv] at h

/-- A unitary matrix `U` as a linear isometry equivalence of `EuclideanSpace 𝕜 n`, acting as
`toEuclideanLin U`, with inverse `toEuclideanLin Uᴴ`. -/
noncomputable def unitaryLinearIsometryEquiv (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    EuclideanSpace 𝕜 n ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 n :=
  Unitary.linearIsometryEquiv ⟨toEuclideanCLM (n := n) (𝕜 := 𝕜) U, toEuclideanCLM_mem_unitary hU⟩

/-- The isometry of a unitary matrix acts as the matrix. -/
theorem unitaryLinearIsometryEquiv_apply (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (x : EuclideanSpace 𝕜 n) : unitaryLinearIsometryEquiv hU x = toEuclideanLin U x := rfl

/-- The inverse of the isometry of a unitary matrix acts as its conjugate transpose. -/
theorem unitaryLinearIsometryEquiv_symm_apply (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (x : EuclideanSpace 𝕜 n) : (unitaryLinearIsometryEquiv hU).symm x = toEuclideanLin Uᴴ x := by
  change (star (toEuclideanCLM (n := n) (𝕜 := 𝕜) U)) x = _
  rw [← map_star, star_eq_conjTranspose]
  rfl

end Unitary

section Isometry

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A matrix `V` with orthonormal columns, `Vᴴ V = 1`, acts as a linear isometry
`EuclideanSpace 𝕜 m →ₗᵢ EuclideanSpace 𝕜 n`. -/
noncomputable def toEuclideanLinearIsometry {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1) :
    EuclideanSpace 𝕜 m →ₗᵢ[𝕜] EuclideanSpace 𝕜 n where
  toLinearMap := toEuclideanLin V
  norm_map' y := by
    have h : inner 𝕜 (toEuclideanLin V y) (toEuclideanLin V y) = inner 𝕜 y y := by
      rw [← toEuclideanLin_conjTranspose_inner_left, ← Matrix.toEuclideanLin_mul_apply, hV,
        toEuclideanLin_one, LinearMap.id_apply]
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← inner_self_eq_norm_sq (𝕜 := 𝕜),
      ← inner_self_eq_norm_sq (𝕜 := 𝕜), h]

/-- The isometry of `Matrix.toEuclideanLinearIsometry` acts as `toEuclideanLin V`. -/
@[simp]
theorem toEuclideanLinearIsometry_apply {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1)
    (y : EuclideanSpace 𝕜 m) : toEuclideanLinearIsometry hV y = toEuclideanLin V y := rfl

/-- A matrix `V` with `Vᴴ V = 1` and `V Vᴴ = 1` (a unitary matrix whose rows and columns are
indexed by different types) acts as a linear isometry equivalence
`EuclideanSpace 𝕜 m ≃ₗᵢ EuclideanSpace 𝕜 n`. -/
noncomputable def toEuclideanLinearIsometryEquiv {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1)
    (hV' : V * Vᴴ = 1) : EuclideanSpace 𝕜 m ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 n :=
  LinearIsometryEquiv.ofSurjective (toEuclideanLinearIsometry hV) fun y =>
    ⟨toEuclideanLin Vᴴ y, by
      rw [toEuclideanLinearIsometry_apply, ← toEuclideanLin_mul_apply, hV', toEuclideanLin_one,
        LinearMap.id_apply]⟩

/-- The isometry equivalence of `Matrix.toEuclideanLinearIsometryEquiv` acts as
`toEuclideanLin V`. -/
@[simp]
theorem toEuclideanLinearIsometryEquiv_apply {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1)
    (hV' : V * Vᴴ = 1) (y : EuclideanSpace 𝕜 m) :
    toEuclideanLinearIsometryEquiv hV hV' y = toEuclideanLin V y := rfl

/-- **Column spaces under a unitary change of coordinates**: for `V` with `Vᴴ V = 1` and
`V Vᴴ = 1`, `ran (V M)` is the image of `ran M` under the isometry equivalence `V`, so metric
quantities of column spaces (gaps, angles, distances) are unchanged by `M ↦ V M`. -/
theorem range_mul_eq_map_of_mul_conjTranspose_eq_one {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1)
    (hV' : V * Vᴴ = 1) {k : Type*} [Fintype k] [DecidableEq k] (M : Matrix m k 𝕜) :
    LinearMap.range (toEuclideanLin (V * M)) =
      (LinearMap.range (toEuclideanLin M)).map
        ((toEuclideanLinearIsometryEquiv hV hV').toLinearEquiv :
          EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 n) := by
  rw [toEuclideanLin_mul, LinearMap.range_comp]
  rfl

omit [DecidableEq n] in
/-- The range of a matrix with orthonormal columns has dimension the number of columns. -/
theorem finrank_range_of_conjTranspose_mul_self_eq_one {V : Matrix n m 𝕜} (hV : Vᴴ * V = 1) :
    Module.finrank 𝕜 (LinearMap.range (toEuclideanLin V)) = Fintype.card m := by
  classical
  rw [LinearMap.finrank_range_of_inj (f := toEuclideanLin V)
    (toEuclideanLinearIsometry hV).injective, finrank_euclideanSpace]

end Isometry

section Applied

/-! ### The applied forms of the linear-equivalence laws

`Matrix.toEuclideanLin` is a linear equivalence, so `map_zero`, `map_neg`, `map_sub` and `map_smul`
apply to it; each of the lemmas below is one of those followed by the pointwise definition of the
corresponding operation on linear maps, in the form in which a proof about a vector wants it. -/

variable {m : Type*}

/-- The zero matrix sends every vector to `0`. -/
theorem toEuclideanLin_zero_apply (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (0 : Matrix m n 𝕜) v = 0 := by
  rw [map_zero]; rfl

/-- The negated matrix acts as the negated operator. -/
theorem toEuclideanLin_neg_apply (A : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (-A) v = -toEuclideanLin A v := by
  rw [map_neg]; rfl

/-- A difference of matrices acts as the difference of the operators. -/
theorem toEuclideanLin_sub_apply (A B : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (A - B) v = toEuclideanLin A v - toEuclideanLin B v := by
  rw [map_sub]; rfl

/-- A scalar multiple of a matrix acts as the scalar multiple of the operator. -/
theorem toEuclideanLin_smul_apply (r : 𝕜) (A : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (r • A) v = r • toEuclideanLin A v := by
  rw [map_smul]; rfl

end Applied

/-- The identity matrix fixes every vector; the applied form of `Matrix.toEuclideanLin_one`. -/
theorem toEuclideanLin_one_apply (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin (1 : Matrix n n 𝕜) v = v := by
  rw [toEuclideanLin_one]; rfl

/-- `Matrix.toEuclideanCLM` is injective: two matrices that act as the same operator on
`EuclideanSpace` are equal.  This is the injectivity of a star algebra equivalence, stated for the
coercion its applications use; `StarAlgEquiv.injective` is stated for the underlying ring
equivalence instead, and a goal closed by it comes out phrased in `toRingEquiv`. -/
theorem toEuclideanCLM_injective :
    Function.Injective (toEuclideanCLM (n := n) (𝕜 := 𝕜)) := fun _ _ h => by
  simpa using congrArg (toEuclideanCLM (n := n) (𝕜 := 𝕜)).symm h

section Inverse

/-! ### Inversion

Mathlib's `Matrix.inv` is a junk-valued inverse, defined for every square matrix and equal to `0`
on a singular one, whereas the operator algebra `EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n` has
the junk-valued `Ring.inverse` of a monoid. The two agree under `Matrix.toEuclideanCLM` on
invertible matrices, which is all that is ever needed; on singular ones both sides are `0` for
`Matrix.inv` and `Ring.inverse` alike, but the operator side does not know that its argument came
from a matrix, so the hypothesis stays. -/

/-- A star algebra equivalence carries `Ring.inverse` to `Ring.inverse`: the image of the inverse of
an invertible matrix is the inverse of its image. -/
theorem toEuclideanCLM_ringInverse {A : Matrix n n 𝕜} (hA : IsUnit A) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (Ring.inverse A)
      = Ring.inverse (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := by
  have hu : IsUnit (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := hA.map _
  refine hu.mul_left_cancel ?_
  rw [← map_mul, Ring.mul_inverse_cancel _ hA, map_one, Ring.mul_inverse_cancel _ hu]

/-- The operator of the inverse of an invertible matrix is the inverse operator, with Mathlib's
junk-valued `Matrix.inv` on the left and `Ring.inverse` on the right. -/
theorem toEuclideanCLM_nonsing_inv {A : Matrix n n 𝕜} (hA : IsUnit A) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) A⁻¹
      = Ring.inverse (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := by
  rw [nonsing_inv_eq_ringInverse, toEuclideanCLM_ringInverse hA]

/-- For a nonsingular `M`, `toEuclideanLin M` is a unit of `Module.End` with `Ring.inverse` equal
to `toEuclideanLin M⁻¹`: the `Module.End` form of `Matrix.toEuclideanCLM_nonsing_inv`. -/
theorem ringInverse_toEuclideanLin {M : Matrix n n 𝕜} (hM : IsUnit M) :
    IsUnit (toEuclideanLin M) ∧ Ring.inverse (toEuclideanLin M) = toEuclideanLin M⁻¹ := by
  have hdet := (isUnit_iff_isUnit_det M).mp hM
  let u : (Module.End 𝕜 (EuclideanSpace 𝕜 n))ˣ :=
    ⟨toEuclideanLin M, toEuclideanLin M⁻¹,
      by rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, mul_nonsing_inv M hdet,
        toEuclideanLin_one, Module.End.one_eq_id],
      by rw [Module.End.mul_eq_comp, ← toEuclideanLin_mul, nonsing_inv_mul M hdet,
        toEuclideanLin_one, Module.End.one_eq_id]⟩
  exact ⟨⟨u, rfl⟩, Ring.inverse_unit u⟩

/-- Applying an invertible matrix undoes applying its inverse, on `EuclideanSpace`: the applied
form of `Matrix.mul_nonsing_inv`. -/
theorem toEuclideanLin_mul_nonsing_inv_apply {A : Matrix n n 𝕜} (hA : IsUnit A)
    (z : EuclideanSpace 𝕜 n) : toEuclideanLin A (toEuclideanLin A⁻¹ z) = z := by
  rw [← toEuclideanLin_mul_apply, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA),
    toEuclideanLin_one_apply]

/-- Applying the inverse of an invertible matrix undoes applying the matrix, on `EuclideanSpace`:
the applied form of `Matrix.nonsing_inv_mul`. -/
theorem toEuclideanLin_nonsing_inv_mul_apply {A : Matrix n n 𝕜} (hA : IsUnit A)
    (z : EuclideanSpace 𝕜 n) : toEuclideanLin A⁻¹ (toEuclideanLin A z) = z := by
  rw [← toEuclideanLin_mul_apply, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA),
    toEuclideanLin_one_apply]

/-- A nonsingular matrix acts surjectively. -/
theorem range_toEuclideanLin_eq_top_of_isUnit {S : Matrix n n 𝕜} (hS : IsUnit S) :
    LinearMap.range (toEuclideanLin S) = ⊤ :=
  LinearMap.range_eq_top.2 fun z => ⟨_, toEuclideanLin_mul_nonsing_inv_apply hS z⟩

end Inverse

section Shift

/-! ### Shifts by a multiple of the identity

The shift `A + r I` is the shape of a resolvent, of a regularized system and of the half-steps of an
alternating-direction sweep; its image under `Matrix.toEuclideanCLM` is the corresponding shift of
the operator. -/

/-- The shift `A + r I` of a matrix acts as the shift `toEuclideanCLM A + r • 1` of the operator. -/
theorem toEuclideanCLM_add_smul_one (A : Matrix n n 𝕜) (r : 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (A + r • 1)
      = toEuclideanCLM (n := n) (𝕜 := 𝕜) A + r • 1 := by
  rw [map_add, map_smul, map_one]

/-- The shift `A - r I` of a matrix acts as the shift `toEuclideanCLM A - r • 1` of the operator. -/
theorem toEuclideanCLM_sub_smul_one (A : Matrix n n 𝕜) (r : 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (A - r • 1)
      = toEuclideanCLM (n := n) (𝕜 := 𝕜) A - r • 1 := by
  rw [map_sub, map_smul, map_one]

/-- A nonsingular shift `A + r I` gives an invertible shifted operator. -/
theorem isUnit_toEuclideanCLM_add_smul_one {A : Matrix n n 𝕜} {r : 𝕜}
    (hA : IsUnit (A + r • (1 : Matrix n n 𝕜))) :
    IsUnit (toEuclideanCLM (n := n) (𝕜 := 𝕜) A + r • 1) := by
  have h := hA.map (toEuclideanCLM (n := n) (𝕜 := 𝕜))
  rwa [toEuclideanCLM_add_smul_one] at h

end Shift

section RankOne

open WithLp

/-- The outer product `u vᵀ` acts on `EuclideanSpace ℝ n` as the rank-one operator
`w ↦ ⟪v, w⟫ u`. -/
theorem toEuclideanCLM_vecMulVec (u v : n → ℝ) :
    toEuclideanCLM (𝕜 := ℝ) (vecMulVec u v)
      = InnerProductSpace.rankOne ℝ (toLp 2 u) (toLp 2 v) := by
  ext w i
  simp [ofLp_toEuclideanCLM, InnerProductSpace.rankOne_apply,
    EuclideanSpace.inner_eq_star_dotProduct, vecMulVec_mulVec, dotProduct_comm, mul_comm]

end RankOne

section Complexify

/-! ### Real matrices as operators on `EuclideanSpace ℂ n`

A real matrix reaches the complex Hilbert-space theory (self-adjointness, coercivity, the
spectral radius) through `Matrix.complexify` and `Matrix.toEuclideanCLM`; a real vector is read in
`EuclideanSpace ℂ n` through `Matrix.toEuclideanComplex`. -/

/-- A real vector as a vector of `EuclideanSpace ℂ n`. -/
def toEuclideanComplex (e : n → ℝ) : EuclideanSpace ℂ n := WithLp.toLp 2 fun i => (e i : ℂ)

omit [Fintype n] [DecidableEq n] in
/-- A real vector is zero iff its complex Euclidean image is. -/
theorem toEuclideanComplex_eq_zero_iff {e : n → ℝ} : toEuclideanComplex e = 0 ↔ e = 0 := by
  constructor
  · intro h
    ext i
    have := congrFun (congrArg WithLp.ofLp h) i
    simpa [toEuclideanComplex] using this
  · rintro rfl
    ext i
    simp [toEuclideanComplex]

/-- The Euclidean operator of the complexification of `A` acts on a real vector as `A` does. -/
theorem toEuclideanCLM_complexify_toEuclideanComplex (A : Matrix n n ℝ) (e : n → ℝ) :
    toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) (toEuclideanComplex e)
      = toEuclideanComplex (A *ᵥ e) := by
  rw [toEuclideanComplex, toEuclideanCLM_toLp, complexify_mulVec_ofReal]
  rfl

/-- The quadratic form of the Euclidean operator of `complexify A` at a real vector is the real
quadratic form `(A e) ⬝ e`. -/
theorem re_inner_toEuclideanCLM_complexify_toEuclideanComplex (A : Matrix n n ℝ) (e : n → ℝ) :
    RCLike.re (inner ℂ (toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A) (toEuclideanComplex e))
      (toEuclideanComplex e)) = (A *ᵥ e) ⬝ᵥ e := by
  rw [toEuclideanCLM_complexify_toEuclideanComplex, toEuclideanComplex, toEuclideanComplex,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

/-- The Euclidean operator of a real symmetric matrix is a symmetric operator. -/
theorem IsHermitian.isSymmetric_toEuclideanCLM_complexify {X : Matrix n n ℝ}
    (hX : X.IsHermitian) :
    ((toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify X) :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin]
  exact isSymmetric_toEuclideanLin_iff.mpr ((isHermitian_complexify_iff X).mpr hX)

/-- The Euclidean operator of a real positive definite matrix is symmetric coercive. -/
theorem PosDef.isSymmetricCoercive_toEuclideanCLM_complexify {X : Matrix n n ℝ}
    (hX : X.PosDef) :
    ((toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify X) :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetricCoercive := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin]
  exact (posDef_iff_isSymmetricCoercive _).mp (posDef_complexify_iff.mpr hX)

/-- The real spectrum of the Euclidean operator of a complexified real matrix is the real
spectrum of the matrix. -/
theorem spectrum_real_toEuclideanCLM_complexify (A : Matrix n n ℝ) :
    spectrum ℝ (toEuclideanCLM (n := n) (𝕜 := ℂ) (complexify A)) = spectrum ℝ A := by
  ext t
  rw [← spectrum.algebraMap_mem_iff ℂ, AlgEquiv.spectrum_eq (toEuclideanCLM (n := n) (𝕜 := ℂ)),
    Complex.coe_algebraMap, ofReal_mem_spectrum_complexify_iff]

end Complexify

end Matrix
