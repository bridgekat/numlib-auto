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

/-- Saad Prop 6.3 (first part): if `A^i x ∈ K` for all `i ≤ deg p` then `p(A_K) x = p(A) x`. -/
theorem aeval_apply_of_forall_pow_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i ≤ p.natDegree, (A ^ i) (x : E) ∈ K) :
    (aeval (compressionBy Q A) p x : E) = aeval A p (x : E) := by
  simp only [aeval_eq_sum_range, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    SetLike.val_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [coe_pow_apply Q hQ A i fun j hj =>
    hx j (hj.trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))]

/-- Saad Prop 6.3 (second part): if `A^i x ∈ K` for all `i < deg p` then `Q (p(A) x) = p(A_K) x`. -/
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

theorem eq_compressionBy :
    compression A K = compressionBy (K.orthogonalProjectionOnto : E →ₗ[𝕜] K) A := rfl

/-- The orthogonal projection fixes the elements of `K`. -/
private theorem orthogonalProjectionOnto_eq_self :
    ∀ x : K, (K.orthogonalProjectionOnto : E →ₗ[𝕜] K) x = x :=
  K.orthogonalProjectionOnto_mem_subspace_eq_self

/-- Saad Prop 6.3 for the orthogonal compression: `p(A_K) x = p(A) x` when the Krylov sequence of
`x` up to degree `deg p` stays in `K` (e.g. `K = 𝒦_{m+1}(A, x)`, `deg p ≤ m`). -/
theorem aeval_apply_of_forall_pow_mem (p : 𝕜[X]) {x : K}
    (hx : ∀ i ≤ p.natDegree, (A ^ i) (x : E) ∈ K) :
    (aeval (compression A K) p x : E) = aeval A p (x : E) :=
  compressionBy.aeval_apply_of_forall_pow_mem _ (orthogonalProjectionOnto_eq_self K) A p hx

theorem inner_apply (x y : K) : inner 𝕜 (compression A K x) y = inner 𝕜 (A x) (y : E) := by
  have h := K.starProjection_inner_eq_zero (A (x : E)) (y : E) y.2
  rw [inner_sub_left, sub_eq_zero] at h
  exact h.symm

theorem inner_apply' (x y : K) : inner 𝕜 x (compression A K y) = inner 𝕜 (x : E) (A y) := by
  rw [← inner_conj_symm x (compression A K y), inner_apply, inner_conj_symm]

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

/-- Residual identity behind Saad-eig Thm 4.3: for `u ∈ E`,
`(A_K - λ) P_K u = -P_K (A - λ) (1 - P_K) u` whenever `(A - λ) u = 0`.

Note the sign: `P_K A P_K u - λ P_K u = P_K A (P_K - 1) u`, so the right-hand side of the
usual textbook display carries a minus sign (it does not matter for the norm estimates that
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
