/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.InnerProductSpace.Projection`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Compression of an operator to a subspace

`compression A K = P_K ∘ A ∘ ι_K : K →ₗ K`, the "section" of `A` on `K`. Rayleigh–Ritz for
eigenproblems and the Arnoldi/Lanczos matrices `H_m`, `T_m` for linear systems are both the
compression to a Krylov subspace, and its two error constants are Céa's `‖A‖/c` and the
Rayleigh–Ritz constant `γ = ‖P_K A (1 - P_K)‖`.

## Main definitions

* `compressionBy Q A`, the compression through an arbitrary projector `Q : E →ₗ[𝕜] K` onto `K`;
* `compression A K`, the compression through the orthogonal projection, which
  `compression.eq_compressionBy` identifies with the previous one.

## Main statements

* `compressionBy.aeval_apply_of_forall_pow_mem` and
  `compressionBy.apply_aeval_of_forall_pow_lt_mem`: polynomials of the compression agree with
  polynomials of `A` as long as the orbit stays in `K`, which is what makes a Krylov subspace the
  natural `K`;
* `compression.inner_apply`, the Galerkin characterization, and `compression.isSymmetric`, the
  symmetry it gives;
* `compression.apply_sub_smul_orthogonalProjection`, the residual identity behind the
  Rayleigh–Ritz eigenvalue error bounds of [Saad, *Numerical Methods for Large Eigenvalue
  Problems*][saad2011numerical], Thm 4.3.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Compression through an arbitrary projector `Q : E →ₗ K` onto `K` (`Q x = x` on `K`):
`Q ∘ A ∘ ι_K`, the oblique Rayleigh–Ritz compression. The orthogonal case is `compression`
(`compression.eq_compressionBy`). -/
def compressionBy {K : Submodule 𝕜 E} (Q : E →ₗ[𝕜] K) (A : E →ₗ[𝕜] E) : K →ₗ[𝕜] K :=
  Q.comp (A.comp K.subtype)

namespace compressionBy

variable {K : Submodule 𝕜 E} (Q : E →ₗ[𝕜] K) (hQ : ∀ x : K, Q x = x) (A : E →ₗ[𝕜] E)
include hQ

/-- A projector onto `K` fixes the elements of `K`. -/
private theorem coe_apply_of_mem {z : E} (hz : z ∈ K) : (Q z : E) = z :=
  congrArg Subtype.val (hQ ⟨z, hz⟩)

/-- Powers of the compression agree with powers of `A` as long as the orbit stays in `K`. -/
private theorem coe_pow_apply {x : K} (i : ℕ) (hx : ∀ j ≤ i, (A ^ j) (x : E) ∈ K) :
    (((compressionBy Q A) ^ i) x : E) = (A ^ i) (x : E) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi := ih fun j hj => hx j (hj.trans (Nat.le_succ i))
    have hstep : A ((A ^ i) (x : E)) = (A ^ (i + 1)) (x : E) := by rw [pow_succ' A i]; rfl
    rw [pow_succ' (compressionBy Q A) i]
    change (Q (A ((((compressionBy Q A) ^ i) x : K) : E)) : E) = _
    rw [hi, hstep]
    exact coe_apply_of_mem Q hQ (hx (i + 1) le_rfl)

/-- The projector of a power of `A` is the corresponding power of the compression, as long as
the orbit stays in `K` up to one step before. -/
private theorem apply_pow (i : ℕ) {x : K} (hx : ∀ j < i, (A ^ j) (x : E) ∈ K) :
    Q ((A ^ i) (x : E)) = ((compressionBy Q A) ^ i) x := by
  cases i with
  | zero => simpa using hQ x
  | succ i =>
    have hi := coe_pow_apply Q hQ A i fun j hj => hx j (Nat.lt_succ_of_le hj)
    have hstep : A ((A ^ i) (x : E)) = (A ^ (i + 1)) (x : E) := by rw [pow_succ' A i]; rfl
    rw [pow_succ' (compressionBy Q A) i]
    change _ = Q (A ((((compressionBy Q A) ^ i) x : K) : E))
    rw [hi, hstep]

/-- Polynomials of the compression agree with polynomials of `A`: if `A^i x ∈ K` for all
`i ≤ deg p` then `p(A_K) x = p(A) x`. -/
theorem aeval_apply_of_forall_pow_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i ≤ p.natDegree, (A ^ i) (x : E) ∈ K) :
    (aeval (compressionBy Q A) p x : E) = aeval A p (x : E) := by
  simp only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    SetLike.val_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [coe_pow_apply Q hQ A i fun j hj =>
    hx j (hj.trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))]

/-- One degree less is enough after projecting: if `A^i x ∈ K` for all `i < deg p` then
`Q (p(A) x) = p(A_K) x`. -/
theorem apply_aeval_of_forall_pow_lt_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i < p.natDegree, (A ^ i) (x : E) ∈ K) :
    Q (aeval A p (x : E)) = aeval (compressionBy Q A) p x := by
  simp only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [apply_pow Q hQ A i fun j hj =>
    hx j (hj.trans_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))]

end compressionBy

/-- The compression `P_K A|_K` of `A` to a subspace with an orthogonal projection. -/
noncomputable def compression (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    K →ₗ[𝕜] K :=
  (K.orthogonalProjectionOnto : E →ₗ[𝕜] K).comp (A.comp K.subtype)

namespace compression

variable (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]

/-- The orthogonal compression is the oblique one taken through the orthogonal projector, so
every result about `compressionBy` applies to it. -/
theorem eq_compressionBy :
    compression A K = compressionBy (K.orthogonalProjectionOnto : E →ₗ[𝕜] K) A := rfl

/-- The orthogonal projection fixes the elements of `K`. -/
private theorem orthogonalProjectionOnto_eq_self :
    ∀ x : K, (K.orthogonalProjectionOnto : E →ₗ[𝕜] K) x = x :=
  K.orthogonalProjectionOnto_mem_subspace_eq_self

/-- The orthogonal compression: `p(A_K) x = p(A) x` when the Krylov sequence of `x` up to
degree `deg p` stays in `K` (e.g. `K = 𝒦_{m+1}(A, x)`, `deg p ≤ m`). -/
theorem aeval_apply_of_forall_pow_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i ≤ p.natDegree, (A ^ i) (x : E) ∈ K) :
    (aeval (compression A K) p x : E) = aeval A p (x : E) :=
  compressionBy.aeval_apply_of_forall_pow_mem _ (orthogonalProjectionOnto_eq_self K) A p hx

/-- On `K` the compression carries the same sesquilinear form as `A`: the projection is
invisible against a test vector taken from `K`. This is the Galerkin (Rayleigh–Ritz)
characterization of the compression, and the source of its symmetry and its bounds. -/
theorem inner_apply (x y : K) : inner 𝕜 (compression A K x) y = inner 𝕜 (A x) (y : E) := by
  have h := K.starProjection_inner_eq_zero (A (x : E)) (y : E) y.2
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

/-- `compression.inner_apply` with the compression in the second argument. -/
theorem inner_apply' (x y : K) : inner 𝕜 x (compression A K y) = inner 𝕜 (x : E) (A y) := by
  rw [← inner_conj_symm x (compression A K y), inner_apply, inner_conj_symm]

/-- The compression of a symmetric operator is symmetric: the Rayleigh–Ritz matrix of a
Hermitian operator is Hermitian. -/
theorem isSymmetric (hA : A.IsSymmetric) : (compression A K).IsSymmetric := fun x y => by
  rw [inner_apply, inner_apply', hA]

/-- Matrix of the compression in an orthonormal basis of `K` is `⟪v i, A (v j)⟫`. -/
theorem toMatrix_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 K) :
    LinearMap.toMatrix b.toBasis b.toBasis (compression A K) =
      Matrix.of fun i j => inner 𝕜 (b i : E) (A (b j)) := by
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, b.repr_apply_apply]
  exact inner_apply' A K (b i) (b j)

/-- On an `A`-invariant subspace the compression is the restriction. -/
theorem apply_of_invt (hK : K ∈ Module.End.invtSubmodule A) (x : K) :
    (compression A K x : E) = A x :=
  congrArg Subtype.val (K.orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨A (x : E), (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hK _ x.2⟩)

/-- Residual identity behind the Rayleigh–Ritz eigenvalue error bounds (Saad, *Numerical Methods
for Large Eigenvalue Problems*, Thm 4.3): for `u ∈ E`,
`(A_K - λ) P_K u = -P_K (A - λ) (1 - P_K) u` whenever `(A - λ) u = 0`. It bounds the residual of
the Ritz pair `(λ, P_K u)` by the part of an exact eigenvector `u` that `K` fails to capture.

Note the sign: `P_K A P_K u - λ P_K u = P_K A (P_K - 1) u`, so the right-hand side of the
display in Saad Thm 4.3 carries a minus sign (it does not matter for the norm estimates that
use this identity). -/
theorem apply_sub_smul_orthogonalProjection {u : E} {μ : 𝕜} (hu : A u = μ • u) :
    (compression A K (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : E) =
      -K.starProjection (A (u - K.starProjection u)) := by
  have hp : A (K.starProjection u) = μ • u - A (u - K.starProjection u) := by
    rw [map_sub, ← hu]; abel
  change K.starProjection (A (K.starProjection u)) - μ • K.starProjection u = _
  rw [hp, map_sub, map_smul]
  abel

end compression
