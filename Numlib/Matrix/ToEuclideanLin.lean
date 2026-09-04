/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Matrix`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Krylov.Subspace
import Numlib.InnerProductSpace.Coercive
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
theorem toEuclideanLin_one : toEuclideanLin (1 : Matrix n n 𝕜) = LinearMap.id := by
  sorry

theorem toEuclideanLin_mul (A B : Matrix n n 𝕜) :
    toEuclideanLin (A * B) = toEuclideanLin A ∘ₗ toEuclideanLin B := by
  sorry

theorem toEuclideanLin_pow (A : Matrix n n 𝕜) (k : ℕ) :
    toEuclideanLin (A ^ k) = toEuclideanLin A ^ k := by
  sorry

/-- The adjoint of `toEuclideanLin A` is `toEuclideanLin Aᴴ`. -/
theorem toEuclideanLin_conjTranspose (A : Matrix n n 𝕜) :
    toEuclideanLin Aᴴ = LinearMap.adjoint (toEuclideanLin A) := by
  sorry

/-- Eigenvalues of the operator are the eigenvalues of the matrix. -/
theorem hasEigenvalue_toEuclideanLin_iff (A : Matrix n n 𝕜) (μ : 𝕜) :
    Module.End.HasEigenvalue (toEuclideanLin A) μ ↔ μ ∈ spectrum 𝕜 A := by
  sorry

/-- For Hermitian `A`, the eigenvalues of `toEuclideanLin A` are Mathlib's
`Matrix.IsHermitian.eigenvalues`. -/
theorem IsHermitian.hasEigenvalue_toEuclideanLin_iff {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (μ : 𝕜) : Module.End.HasEigenvalue (toEuclideanLin A) μ ↔ ∃ i, (hA.eigenvalues i : 𝕜) = μ := by
  sorry

/-- The quadratic-form bounds of a Hermitian matrix are its extreme eigenvalues. -/
theorem IsHermitian.isSymmetricBoundedBy_toEuclideanLin {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {lmin lmax : ℝ} (h : ∀ i, hA.eigenvalues i ∈ Set.Icc lmin lmax) :
    (toEuclideanLin A).IsSymmetricBoundedBy lmin lmax := by
  sorry

/-- Krylov subspaces of a matrix are spanned by the columns `A^i v`. -/
theorem krylov_subspace_toEuclideanLin (A : Matrix n n 𝕜) (v : EuclideanSpace 𝕜 n) (m : ℕ) :
    Krylov.subspace (toEuclideanLin A) v m =
      Submodule.span 𝕜 (Set.range fun i : Fin m => toEuclideanLin (A ^ (i : ℕ)) v) := by
  sorry

omit [Fintype n] [DecidableEq n] in
/-- `V y = ∑ y_j • (column j of V)`: moving between the book's `V_m y` and the backbone's
`∑ y_j • vec j`. -/
theorem toEuclideanLin_apply_eq_sum {m : Type*} [Fintype m] [DecidableEq m] (V : Matrix n m 𝕜)
    (y : m → 𝕜) :
    toEuclideanLin V (WithLp.toLp 2 y) =
      ∑ j, y j • (WithLp.toLp 2 (Vᵀ j) : EuclideanSpace 𝕜 n) := by
  sorry

open scoped Matrix.Norms.L2Operator in
/-- The `2`-operator norm of a matrix is the operator norm of `toEuclideanLin A`. -/
theorem l2_opNorm_eq_norm_toEuclideanLin (A : Matrix n n 𝕜) :
    ‖A‖ = ‖LinearMap.toContinuousLinearMap (toEuclideanLin A)‖ := by
  sorry

end Matrix
