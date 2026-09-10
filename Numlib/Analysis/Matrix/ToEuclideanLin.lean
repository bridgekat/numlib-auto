/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import Numlib.Analysis.InnerProductSpace.Coercive

/-!
# Matrices as operators on `EuclideanSpace`

Glue between `Matrix n n 𝕜` and `Matrix.toEuclideanLin A : EuclideanSpace 𝕜 n →ₗ EuclideanSpace 𝕜 n`
used by every matrix-level surface statement: multiplicativity, powers, adjoint = conjugate
transpose, eigenvalues, and the `‖A‖₂ = ‖toEuclideanLin A‖` identification. (Symmetric ↔ Hermitian
is Mathlib's `Matrix.isSymmetric_toEuclideanLin_iff`, `Matrix.PosDef` ↔ symmetric coercive is
`Matrix.posDef_iff_isSymmetricCoercive`; reading a Krylov subspace of `toEuclideanLin A` as a span
of columns is `Matrix.krylov_subspace_toEuclideanLin` in `Numlib.Krylov.ToEuclideanLin`, which this
module cannot depend on.)

It also contains the fact that a unitary matrix acts as an isometry of `EuclideanSpace`,
`‖U *ᵥ v‖₂ = ‖v‖₂`: transport `U` along the star algebra equivalence `Matrix.toEuclideanCLM`
and use that a unitary continuous linear endomorphism of a Hilbert space preserves the norm
(`ContinuousLinearMap.norm_map_of_mem_unitary`).

Three further groups of glue, each of which is otherwise re-proved wherever a matrix statement is
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
  operator.
-/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The identity matrix acts as the identity operator. -/
@[simp]
theorem toEuclideanLin_one : toEuclideanLin (1 : Matrix n n 𝕜) = LinearMap.id :=
  toLpLin_one 2

/-- Matrix multiplication is composition of the operators, so `toEuclideanLin` is a morphism of
algebras and not merely a linear map. -/
theorem toEuclideanLin_mul (A B : Matrix n n 𝕜) :
    toEuclideanLin (A * B) = toEuclideanLin A ∘ₗ toEuclideanLin B :=
  toLpLin_mul_same 2 A B

/-- Powers of a matrix act as powers of the operator; this is what lets a Krylov subspace of a
matrix be read as a Krylov subspace of `toEuclideanLin A`. -/
theorem toEuclideanLin_pow (A : Matrix n n 𝕜) (k : ℕ) :
    toEuclideanLin (A ^ k) = toEuclideanLin A ^ k :=
  toLpLin_pow 2 A k

/-- The adjoint of `toEuclideanLin A` is `toEuclideanLin Aᴴ`. -/
theorem toEuclideanLin_conjTranspose (A : Matrix n n 𝕜) :
    toEuclideanLin Aᴴ = LinearMap.adjoint (toEuclideanLin A) :=
  toEuclideanLin_conjTranspose_eq_adjoint A

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

omit [Fintype n] [DecidableEq n] in
/-- `V y = ∑ y_j • (column j of V)`: moving between the book's `V_m y` and the backbone's
`∑ y_j • vec j`. -/
theorem toEuclideanLin_apply_eq_sum {m : Type*} [Fintype m] [DecidableEq m] (V : Matrix n m 𝕜)
    (y : m → 𝕜) :
    toEuclideanLin V (WithLp.toLp 2 y) =
      ∑ j, y j • (WithLp.toLp 2 (Vᵀ j) : EuclideanSpace 𝕜 n) := by
  ext i
  simp [toLpLin_apply, mulVec, dotProduct, mul_comm]

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

end Unitary

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

/-- Applying an invertible matrix undoes applying its inverse, on `EuclideanSpace`: the applied
form of `Matrix.mul_nonsing_inv`. -/
theorem toEuclideanLin_mul_nonsing_inv_apply {A : Matrix n n 𝕜} (hA : IsUnit A)
    (z : EuclideanSpace 𝕜 n) : toEuclideanLin A (toEuclideanLin A⁻¹ z) = z := by
  have h : toEuclideanLin A (toEuclideanLin A⁻¹ z) = toEuclideanLin (A * A⁻¹) z := by
    rw [toEuclideanLin_mul]; rfl
  rw [h, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA), toEuclideanLin_one_apply]

/-- Applying the inverse of an invertible matrix undoes applying the matrix, on `EuclideanSpace`:
the applied form of `Matrix.nonsing_inv_mul`. -/
theorem toEuclideanLin_nonsing_inv_mul_apply {A : Matrix n n 𝕜} (hA : IsUnit A)
    (z : EuclideanSpace 𝕜 n) : toEuclideanLin A⁻¹ (toEuclideanLin A z) = z := by
  have h : toEuclideanLin A⁻¹ (toEuclideanLin A z) = toEuclideanLin (A⁻¹ * A) z := by
    rw [toEuclideanLin_mul]; rfl
  rw [h, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA), toEuclideanLin_one_apply]

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

end Matrix
