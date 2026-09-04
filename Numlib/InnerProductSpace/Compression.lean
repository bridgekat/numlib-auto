/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Projection`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Module.AEval

/-!
# Compression of an operator to a subspace

`compression A K = P_K ∘ A ∘ ι_K : K →ₗ K` (the "section" of `A` on `K`, Saad Prop 6.3 /
Saad-eig §4.3). Rayleigh–Ritz for eigenproblems and the Arnoldi/Lanczos matrices `H_m`, `T_m`
for linear systems are both the compression to a Krylov subspace, and Céa's `‖A‖/c` and
Saad-eig's `γ = ‖P_K A (1 - P_K)‖` are its two error constants.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Compression through an arbitrary projector `Q : E →ₗ K` onto `K` (`Q x = x` on `K`):
`Q ∘ A ∘ ι_K` (oblique Rayleigh–Ritz, Saad-eig §4.3; Saad Prop 6.3 for any projector). The
orthogonal case is `compression` (`compression.eq_compressionBy`). -/
def compressionBy {K : Submodule 𝕜 E} (Q : E →ₗ[𝕜] K) (A : E →ₗ[𝕜] E) : K →ₗ[𝕜] K :=
  Q.comp (A.comp K.subtype)

namespace compressionBy

variable {K : Submodule 𝕜 E} (Q : E →ₗ[𝕜] K) (hQ : ∀ x : K, Q x = x) (A : E →ₗ[𝕜] E)
include hQ

/-- Saad Prop 6.3 (first part): if `A^i x ∈ K` for all `i ≤ deg p` then `p(A_K) x = p(A) x`. -/
theorem aeval_apply_of_forall_pow_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i ≤ p.natDegree, (A ^ i) (x : E) ∈ K) :
    (aeval (compressionBy Q A) p x : E) = aeval A p (x : E) := by
  sorry

/-- Saad Prop 6.3 (second part): if `A^i x ∈ K` for all `i < deg p` then `Q (p(A) x) = p(A_K) x`. -/
theorem apply_aeval_of_forall_pow_lt_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i < p.natDegree, (A ^ i) (x : E) ∈ K) :
    Q (aeval A p (x : E)) = aeval (compressionBy Q A) p x := by
  sorry

end compressionBy

/-- The compression `P_K A|_K` of `A` to a subspace with an orthogonal projection. -/
noncomputable def compression (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    K →ₗ[𝕜] K :=
  (K.orthogonalProjectionOnto : E →ₗ[𝕜] K).comp (A.comp K.subtype)

namespace compression

variable (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

theorem eq_compressionBy :
    compression A K = compressionBy (K.orthogonalProjectionOnto : E →ₗ[𝕜] K) A := rfl

/-- Saad Prop 6.3 for the orthogonal compression: `p(A_K) x = p(A) x` when the Krylov sequence of
`x` up to degree `deg p` stays in `K` (e.g. `K = 𝒦_{m+1}(A, x)`, `deg p ≤ m`). -/
theorem aeval_apply_of_forall_pow_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i ≤ p.natDegree, (A ^ i) (x : E) ∈ K) :
    (aeval (compression A K) p x : E) = aeval A p (x : E) := by
  sorry

theorem inner_apply (x y : K) : inner 𝕜 (compression A K x) y = inner 𝕜 (A x) (y : E) := by
  sorry

theorem inner_apply' (x y : K) : inner 𝕜 x (compression A K y) = inner 𝕜 (x : E) (A y) := by
  sorry

theorem isSymmetric (hA : A.IsSymmetric) : (compression A K).IsSymmetric := by
  sorry

/-- Matrix of the compression in an orthonormal basis of `K` is `⟪v i, A (v j)⟫`. -/
theorem toMatrix_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 K) :
    LinearMap.toMatrix b.toBasis b.toBasis (compression A K) =
      Matrix.of fun i j => inner 𝕜 (b i : E) (A (b j)) := by
  sorry

/-- On an `A`-invariant subspace the compression is the restriction. -/
theorem apply_of_invt (hK : K ∈ Module.End.invtSubmodule A) (x : K) :
    (compression A K x : E) = A x := by
  sorry

/-- Residual identity behind Saad-eig Thm 4.3: for `u ∈ E`,
`(A_K - λ) P_K u = P_K (A - λ) (1 - P_K) u` whenever `(A - λ) u = 0`. -/
theorem apply_sub_smul_orthogonalProjection {u : E} {μ : 𝕜} (hu : A u = μ • u) :
    (compression A K (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : E) =
      K.starProjection (A (u - K.starProjection u)) := by
  sorry

end compression
