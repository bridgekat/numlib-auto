/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Krylov.Subspace
import Numlib.Analysis.InnerProductSpace.Coercive
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Matrices as operators on `EuclideanSpace`

Glue between `Matrix n n 𝕜` and `Matrix.toEuclideanLin A : EuclideanSpace 𝕜 n →ₗ EuclideanSpace 𝕜 n`
used by every matrix-level surface statement: multiplicativity, powers, adjoint = conjugate
transpose, eigenvalues, Krylov subspaces as spans of columns, and the `‖A‖₂ = ‖toEuclideanLin A‖`
identification. (Symmetric ↔ Hermitian is Mathlib's `Matrix.isSymmetric_toEuclideanLin_iff`,
`Matrix.PosDef` ↔ symmetric coercive is `Matrix.posDef_iff_isSymmetricCoercive`.)
-/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

@[simp]
theorem toEuclideanLin_one : toEuclideanLin (1 : Matrix n n 𝕜) = LinearMap.id :=
  toLpLin_one 2

theorem toEuclideanLin_mul (A B : Matrix n n 𝕜) :
    toEuclideanLin (A * B) = toEuclideanLin A ∘ₗ toEuclideanLin B :=
  toLpLin_mul_same 2 A B

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

/-- Krylov subspaces of a matrix are spanned by the columns `A^i v`. -/
theorem krylov_subspace_toEuclideanLin (A : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n) (m : ℕ) :
    Krylov.subspace (toEuclideanLin A) v m =
      Submodule.span 𝕜 (Set.range fun i : Fin m => toEuclideanLin (A ^ (i : ℕ)) v) := by
  simp only [Krylov.subspace, toEuclideanLin_pow]

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

end Matrix
