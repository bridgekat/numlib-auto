import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Krylov.Arnoldi
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Order.Filter.Extr

/-!
# Rayleigh–Ritz approximation

A *Ritz pair* of `A` on a subspace `K` is a pair `(θ, u)` with `u ∈ K`, `u ≠ 0` and the residual
`A u - θ • u` orthogonal to `K`. This is the eigenvalue twin of the Galerkin condition for a
linear system: `Krylov.IsRitzPair` is to `Module.End.HasEigenvector` what `IsGalerkin` is to
`A x = b`, and both are conditions on the same object, the compression `compression A K` of
`Numlib.Analysis.InnerProductSpace.Projection.Compression`. Accordingly
`Krylov.isRitzPair_iff_hasEigenvector` says that a Ritz pair is exactly an eigenpair of the
compression, and needs no more than an inner product and an orthogonal projection onto `K` — no
finite dimension, no completeness. The Petrov–Galerkin version `Krylov.IsObliqueRitzPair`, with a
test space `L` distinct from the trial space `K`, is the eigenpair condition for the oblique
compression `compressionBy Q A` through any projector `Q` onto `K` along `Lᗮ`.

Two consequences are proved here.

* Exactness (`Krylov.IsRitzPair.hasEigenvector_of_invt`): on an `A`-invariant `K` a Ritz pair is
  an exact eigenpair, because its residual then lies in `K ⊓ Kᗮ = ⊥`.
* The a priori residual bound (`Krylov.compression_residual_le` and its companion): with the
  coupling constant `γ = ‖P_K A (1 - P_K)‖` and an exact eigenpair `(μ, u)` of `A`, the Ritz
  residual of `P_K u` is controlled by the part of `u` that `K` fails to capture. The constant
  enters as a hypothesis `‖P_K (A x)‖ ≤ γ ‖x‖` for `x ∈ Kᗮ`, so the statement applies to an
  unbounded `A` and to a `γ` obtained by other means than an operator norm — for a symmetric `A`
  compressed to a Krylov subspace `γ` is the single Hessenberg entry `h_{m+1,m}`. When `A` is
  bounded and `γ` really is the operator norm,
  `Krylov.norm_starProjection_apply_le_opNorm` supplies the hypothesis.

The last two results are the Arnoldi specializations. `Arnoldi.charpoly_compression_isMinOn` is
the optimality of the characteristic polynomial of the Hessenberg matrix: it minimizes `‖p(A) b‖`
over monic `p` of degree `m`, because Cayley–Hamilton makes `p(A) b` orthogonal to the Krylov
subspace while every competitor differs from it by an element of that subspace.
`Arnoldi.norm_ritz_residual_eq` is the cheap residual that makes the Arnoldi method practical:
for an eigenpair `(θ, y)` of the Hessenberg matrix the residual norm of the Ritz vector `V_m y`
is `h_{m+1,m} |y_m|`, one already-computed number times one entry of the small eigenvector, with
no operation on the large space at all. Both hold past breakdown: the first up to and including
the step at which the process terminates, the second with no hypothesis at all.

## References

Every result here is from Saad, *Numerical Methods for Large Eigenvalue
Problems*[^saad-eigenvalue]: §4.3 for the Ritz pairs, for the exactness on an invariant subspace
(Prop 4.3, with the remark preceding Thm 4.7 for the oblique case) and for the residual bounds
with `γ` (Thm 4.3, whose oblique companion is Thm 4.7); §6.1–6.2 for the optimality of the
characteristic polynomial (Thm 6.1, resting on the polynomial compression identity Prop 6.4 that
`Numlib.Analysis.InnerProductSpace.Projection.Compression` proves) and for the cheap Arnoldi
residual (Prop 6.8).

[^saad-eigenvalue]: Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, 2nd edition,
  SIAM, 2011.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Krylov

/-! ### Ritz pairs and oblique Ritz pairs -/

/-- Oblique (Petrov–Galerkin) Ritz pair: `u` is a nonzero element of the trial space `K` whose
residual `A u - θ • u` is orthogonal to the test space `L`.  For `L = K` this is `IsRitzPair`,
and `isObliqueRitzPair_iff_hasEigenvector` identifies it with an eigenpair of the oblique
compression `compressionBy Q A` through any projector `Q` onto `K` along `Lᗮ`. -/
structure IsObliqueRitzPair (A : E →ₗ[𝕜] E) (K L : Submodule 𝕜 E) (θ : 𝕜) (u : E) : Prop where
  /-- The Ritz vector lies in the trial space. -/
  mem : u ∈ K
  /-- A Ritz vector is nonzero, as an eigenvector must be. -/
  ne_zero : u ≠ 0
  /-- Petrov–Galerkin condition: the residual is orthogonal to the test space. -/
  residual_mem_orthogonal : A u - θ • u ∈ Lᗮ

/-- Ritz pair of `A` on `K`: a nonzero `u ∈ K` whose residual `A u - θ • u` is orthogonal to `K`
itself.  These are exactly the eigenpairs of the compression `compression A K`
(`isRitzPair_iff_hasEigenvector`), so `θ` is a Ritz value and `u` a Ritz vector. -/
structure IsRitzPair (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E) (θ : 𝕜) (u : E) : Prop where
  /-- The Ritz vector lies in the subspace. -/
  mem : u ∈ K
  /-- A Ritz vector is nonzero, as an eigenvector must be. -/
  ne_zero : u ≠ 0
  /-- Galerkin condition: the residual is orthogonal to the subspace. -/
  residual_mem_orthogonal : A u - θ • u ∈ Kᗮ

variable {A : E →ₗ[𝕜] E} {K L : Submodule 𝕜 E} {θ : 𝕜} {u : E}

/-- A Ritz pair is the oblique Ritz pair whose test space is the trial space. -/
theorem IsRitzPair.isObliqueRitzPair (h : IsRitzPair A K θ u) : IsObliqueRitzPair A K K θ u :=
  ⟨h.mem, h.ne_zero, h.residual_mem_orthogonal⟩

/-- An oblique Ritz pair whose test space is the trial space is a Ritz pair. -/
theorem IsObliqueRitzPair.isRitzPair (h : IsObliqueRitzPair A K K θ u) : IsRitzPair A K θ u :=
  ⟨h.mem, h.ne_zero, h.residual_mem_orthogonal⟩

/-- The Galerkin case `L = K` of the Petrov–Galerkin condition is the Ritz condition. -/
theorem isRitzPair_iff_isObliqueRitzPair :
    IsRitzPair A K θ u ↔ IsObliqueRitzPair A K K θ u :=
  ⟨IsRitzPair.isObliqueRitzPair, IsObliqueRitzPair.isRitzPair⟩

/-- An oblique Ritz pair is exactly an eigenvector of the oblique compression `compressionBy Q A`
of `Numlib.Analysis.InnerProductSpace.Projection.Compression`, for any projector `Q : E →ₗ K`
onto the trial space (`Q x = x` on `K`) whose kernel is the orthogonal complement `Lᗮ` of the
test space.  Such a `Q` exists exactly when `K ⊓ Lᗮ = ⊥`, by
`LinearMap.existsUnique_isIdempotentElem_of_inf_orthogonal_eq_bot`, and the projectors
`V (Wᴴ V)⁻¹ Wᴴ` built from bases of `K` and `L` are the concrete instances. -/
theorem isObliqueRitzPair_iff_hasEigenvector (A : E →ₗ[𝕜] E) {K L : Submodule 𝕜 E}
    {Q : E →ₗ[𝕜] K} (hQ : ∀ x : K, Q x = x) (hker : LinearMap.ker Q = Lᗮ) (θ : 𝕜) (u : K) :
    IsObliqueRitzPair A K L θ (u : E) ↔ Module.End.HasEigenvector (compressionBy Q A) θ u := by
  have key : compressionBy Q A u = θ • u ↔ A (u : E) - θ • (u : E) ∈ Lᗮ := by
    rw [← hker, LinearMap.mem_ker, map_sub, map_smul, hQ u, sub_eq_zero]
    exact Iff.rfl
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, key]
  exact ⟨fun h => ⟨h.residual_mem_orthogonal, fun h0 => h.ne_zero (Submodule.coe_eq_zero.2 h0)⟩,
    fun h => ⟨u.2, fun h0 => h.2 (Submodule.coe_eq_zero.1 h0), h.1⟩⟩

/-- A Ritz pair is exactly an eigenvector of the compression `compression A K`: the Rayleigh–Ritz
condition on `E` and the eigenvalue problem on the subspace `K` are the same statement.  The Ritz
vector is written `(u : E)` on the left and `u : K` on the right; `IsRitzPair.hasEigenvector` and
`isRitzPair_of_hasEigenvector` are the two directions in the forms that avoid producing the
coercion by hand. -/
theorem isRitzPair_iff_hasEigenvector (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (θ : 𝕜) (u : K) :
    IsRitzPair A K θ (u : E) ↔ Module.End.HasEigenvector (compression A K) θ u := by
  rw [isRitzPair_iff_isObliqueRitzPair, compression.eq_compressionBy]
  exact isObliqueRitzPair_iff_hasEigenvector A
    K.orthogonalProjectionOnto_mem_subspace_eq_self
    (by ext x; exact Submodule.orthogonalProjectionOnto_eq_zero_iff) θ u

/-- Forward direction of `isRitzPair_iff_hasEigenvector`, starting from a Ritz vector in `E`. -/
theorem IsRitzPair.hasEigenvector [K.HasOrthogonalProjection] (h : IsRitzPair A K θ u) :
    Module.End.HasEigenvector (compression A K) θ ⟨u, h.mem⟩ :=
  (isRitzPair_iff_hasEigenvector A K θ ⟨u, h.mem⟩).1 h

/-- A Ritz value is an eigenvalue of the compression; this is what makes the Ritz values of a
finite-dimensional `K` computable as the spectrum of a small matrix. -/
theorem IsRitzPair.hasEigenvalue [K.HasOrthogonalProjection] (h : IsRitzPair A K θ u) :
    Module.End.HasEigenvalue (compression A K) θ :=
  Module.End.hasEigenvalue_of_hasEigenvector h.hasEigenvector

/-- Converse direction of `isRitzPair_iff_hasEigenvector`, starting from an eigenvector of the
compression. -/
theorem isRitzPair_of_hasEigenvector (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (θ : 𝕜) {u : K}
    (h : Module.End.HasEigenvector (compression A K) θ u) : IsRitzPair A K θ (u : E) :=
  (isRitzPair_iff_hasEigenvector A K θ u).2 h

/-- Exactness on invariant subspaces, oblique form (Saad, *Numerical Methods for Large Eigenvalue
Problems*, the remark that precedes the oblique residual bound): if the trial space `K` is
`A`-invariant then every oblique Ritz pair on it is an exact eigenpair, *whatever* the test space
`L` — the residual lies in `K` because `K` is invariant and in `Lᗮ` by the Petrov–Galerkin
condition, and `K ⊓ Lᗮ = ⊥` is exactly the nondegeneracy condition under which the oblique
projector onto `K` along `Lᗮ` exists at all. -/
theorem IsObliqueRitzPair.hasEigenvector_of_invt (h : IsObliqueRitzPair A K L θ u)
    (hK : K ∈ Module.End.invtSubmodule A) (hKL : K ⊓ Lᗮ = ⊥) :
    Module.End.HasEigenvector A θ u := by
  refine ⟨Module.End.mem_eigenspace_iff.2 ?_, h.ne_zero⟩
  have hmem : A u - θ • u ∈ K ⊓ Lᗮ :=
    ⟨Submodule.sub_mem _ ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).1 hK _ h.mem)
      (Submodule.smul_mem _ _ h.mem), h.residual_mem_orthogonal⟩
  rw [hKL, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

/-- Exactness on invariant subspaces (Saad, *Numerical Methods for Large Eigenvalue Problems*):
if `K` is `A`-invariant then every Ritz pair of `A` on `K` is an exact eigenpair of `A`.  The
residual then lies in `K` as well as in `Kᗮ`, hence is zero; no orthogonal projection onto `K`
and no finite dimension are involved. -/
theorem IsRitzPair.hasEigenvector_of_invt (h : IsRitzPair A K θ u)
    (hK : K ∈ Module.End.invtSubmodule A) : Module.End.HasEigenvector A θ u :=
  h.isObliqueRitzPair.hasEigenvector_of_invt hK K.inf_orthogonal_eq_bot

/-- A Ritz value on an `A`-invariant subspace is an eigenvalue of `A` itself. -/
theorem IsRitzPair.hasEigenvalue_of_invt (h : IsRitzPair A K θ u)
    (hK : K ∈ Module.End.invtSubmodule A) : Module.End.HasEigenvalue A θ :=
  Module.End.hasEigenvalue_of_hasEigenvector (h.hasEigenvector_of_invt hK)

/-! ### The residual bound with the coupling constant `γ` -/

/-- The compression of `A` to `K`, evaluated at the orthogonal projection of `u`, written without
the subtype: `(A_K - μ) P_K u = P_K A P_K u - μ P_K u`. -/
private theorem coe_compression_sub_smul (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (μ : 𝕜) (u : E) :
    ((compression A K (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : K) : E)
      = K.starProjection (A (K.starProjection u)) - μ • K.starProjection u := rfl

/-- A bounded `A` satisfies the coupling hypothesis of `compression_residual_le` with
`γ = ‖P_K A (1 - P_K)‖`, the constant of Saad, *Numerical Methods for Large Eigenvalue Problems*.
The residual bounds themselves take `γ` as a hypothesis rather than as this operator norm, so
that they apply to an unbounded `A` and to the sharper values of `γ` that a particular `K`
provides — for a symmetric `A` and a Krylov subspace built by the Arnoldi process `γ` is one
Hessenberg entry, `Arnoldi.starProjection_apply_vec` being the adjoint statement. -/
theorem norm_starProjection_apply_le_opNorm (A : E →L[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] {x : E} (hx : x ∈ Kᗮ) :
    ‖K.starProjection (A x)‖
      ≤ ‖K.starProjection ∘L (A ∘L (1 - K.starProjection))‖ * ‖x‖ := by
  have hfix : (1 - K.starProjection) x = x := by
    rw [sub_apply, one_apply_eq_self, Submodule.starProjection_apply,
      Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hx, Submodule.coe_zero, sub_zero]
  calc ‖K.starProjection (A x)‖
      = ‖(K.starProjection ∘L (A ∘L (1 - K.starProjection))) x‖ := by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hfix]
    _ ≤ ‖K.starProjection ∘L (A ∘L (1 - K.starProjection))‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _

/-- Residual bound for the Ritz pair produced by an exact eigenpair (Saad, *Numerical Methods for
Large Eigenvalue Problems*): if `A u = μ • u` and the coupling `P_K A` is bounded by `γ` on `Kᗮ`,
then `‖(A_K - μ) P_K u‖ ≤ γ ‖(1 - P_K) u‖`.  So a subspace that captures `u` well carries a Ritz
pair with a small residual, and the whole error analysis of Rayleigh–Ritz reduces to estimating
the distance from `u` to `K`.

The proof is one line from the residual identity
`compression.apply_sub_smul_orthogonalProjection`, which says that the left-hand side is
`-P_K (A ((1 - P_K) u))`.  No hypothesis of finite dimension, completeness, symmetry, or
normalization of `u` is used; both sides are homogeneous of degree one in `u`. -/
theorem compression_residual_le {A : E →ₗ[𝕜] E} {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    {γ : ℝ} (hγ : ∀ x ∈ Kᗮ, ‖K.starProjection (A x)‖ ≤ γ * ‖x‖) {μ : 𝕜} {u : E}
    (hu : A u = μ • u) :
    ‖(compression A K (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : E)‖
      ≤ γ * ‖u - K.starProjection u‖ := by
  rw [compression.apply_sub_smul_orthogonalProjection A K hu, norm_neg]
  exact hγ _ (K.sub_starProjection_mem_orthogonal u)

/-- The residual of the *whole* eigenvector, rather than of its projection: under the hypotheses
of `compression_residual_le`, `‖(A_K - μ) u‖ ≤ √(|μ|² + γ²) ‖(1 - P_K) u‖`, where `A_K` is read as
the operator `P_K A P_K` on the whole space.  The extra `|μ|²` is exactly the term `-μ (1 - P_K) u`,
which is orthogonal to the residual of `compression_residual_le`, so the constant `√(|μ|² + γ²)`
is what the Pythagorean identity gives and cannot be improved by this argument. -/
theorem compression_residual_le' {A : E →ₗ[𝕜] E} {K : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    {γ : ℝ} (hγ : ∀ x ∈ Kᗮ, ‖K.starProjection (A x)‖ ≤ γ * ‖x‖) {μ : 𝕜} {u : E}
    (hu : A u = μ • u) :
    ‖K.starProjection (A (K.starProjection u)) - μ • u‖
      ≤ Real.sqrt (‖μ‖ ^ 2 + γ ^ 2) * ‖u - K.starProjection u‖ := by
  have hle : ‖K.starProjection (A (K.starProjection u)) - μ • K.starProjection u‖
      ≤ γ * ‖u - K.starProjection u‖ := by
    rw [← coe_compression_sub_smul A K μ u]
    exact compression_residual_le hγ hu
  have hrmem : K.starProjection (A (K.starProjection u)) - μ • K.starProjection u ∈ K :=
    Submodule.sub_mem _ (K.starProjection_apply_mem _)
      (Submodule.smul_mem _ _ (K.starProjection_apply_mem u))
  have hqmem : (-μ) • (u - K.starProjection u) ∈ Kᗮ :=
    Submodule.smul_mem _ _ (K.sub_starProjection_mem_orthogonal u)
  have hsplit : K.starProjection (A (K.starProjection u)) - μ • u
      = (K.starProjection (A (K.starProjection u)) - μ • K.starProjection u)
        + (-μ) • (u - K.starProjection u) := by module
  have hpyth : ‖K.starProjection (A (K.starProjection u)) - μ • u‖ ^ 2
      = ‖K.starProjection (A (K.starProjection u)) - μ • K.starProjection u‖ ^ 2
        + ‖μ‖ ^ 2 * ‖u - K.starProjection u‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.inner_right_of_mem_orthogonal hrmem hqmem), norm_smul, norm_neg]
    ring
  have hb : (0 : ℝ) ≤ ‖u - K.starProjection u‖ := norm_nonneg _
  have hsq : ‖K.starProjection (A (K.starProjection u)) - μ • u‖ ^ 2
      ≤ (Real.sqrt (‖μ‖ ^ 2 + γ ^ 2) * ‖u - K.starProjection u‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [hpyth, hle, norm_nonneg
      (K.starProjection (A (K.starProjection u)) - μ • K.starProjection u)]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

end Krylov

namespace Arnoldi

open Krylov

variable (A : E →ₗ[𝕜] E) (b : E)

/-! ### Optimality of the characteristic polynomial of the Hessenberg matrix -/

/-- A vector orthogonal to every Arnoldi vector of `𝒦_m` is orthogonal to `𝒦_m`. -/
private theorem mem_orthogonal_of_forall_inner_vec {m : ℕ} {x : E}
    (h : ∀ i < m, inner 𝕜 (vec A b i) x = (0 : 𝕜)) : x ∈ (subspace A b m)ᗮ := by
  rw [← span_vec]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem y hy => obtain ⟨i, hi, rfl⟩ := hy; exact h i hi
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
  | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]

/-- From `a² ≤ c²` with `c` nonnegative to `a ≤ c`. -/
private theorem le_of_sq_le_sq {a c : ℝ} (hc : 0 ≤ c) (h : a ^ 2 ≤ c ^ 2) : a ≤ c := by
  nlinarith

section Charpoly

variable [FiniteDimensional 𝕜 (fullSubspace A b)]

/-- Cayley–Hamilton on the compression: the characteristic polynomial `p` of the compression of
`A` to `𝒦_m` satisfies `p(A) b ⟂ 𝒦_m`.  It is `p(A_K) b = 0` read back on `E` through
`compressionBy.apply_aeval_of_forall_pow_lt_mem`, which needs the Krylov vectors only up to
`A^{m-1} b` and so does not require `𝒦_m` to be `A`-invariant. -/
theorem aeval_charpoly_mem_orthogonal {m : ℕ} (hm : m ≤ grade A b) :
    aeval A (LinearMap.charpoly (compression A (subspace A b m))) b ∈ (subspace A b m)ᗮ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · refine (Submodule.mem_orthogonal _ _).2 fun w hw => ?_
    rw [subspace_zero, Submodule.mem_bot] at hw
    rw [hw, inner_zero_left]
  have hdeg : (LinearMap.charpoly (compression A (subspace A b m))).natDegree = m := by
    rw [LinearMap.charpoly_natDegree, finrank_subspace, min_eq_left hm]
  have hb : b ∈ subspace A b m := self_mem_subspace A b hm0
  have h := compressionBy.apply_aeval_of_forall_pow_lt_mem
    ((subspace A b m).orthogonalProjectionOnto : E →ₗ[𝕜] subspace A b m)
    (subspace A b m).orthogonalProjectionOnto_mem_subspace_eq_self A
    (LinearMap.charpoly (compression A (subspace A b m)))
    (x := ⟨b, hb⟩) fun i hi => pow_apply_mem_subspace A b (hdeg ▸ hi)
  rw [← compression.eq_compressionBy, LinearMap.aeval_self_charpoly, LinearMap.zero_apply] at h
  rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
  exact h

/-- Saad, *Numerical Methods for Large Eigenvalue Problems*: the characteristic polynomial of the
compression of `A` to `𝒦_m(A, b)` — equivalently, of the Arnoldi matrix `H_m`, by
`Arnoldi.hessenbergSq_eq_toMatrix_compression` — minimizes `‖p(A) b‖` over all monic polynomials
`p` of degree `m`.

The proof is a best-approximation argument in `𝒦_m`: the characteristic polynomial `c` satisfies
`c(A) b ⟂ 𝒦_m` by `aeval_charpoly_mem_orthogonal`, while any competing monic `p` of degree `m`
differs from `c` by a polynomial of degree `< m`, so `p(A) b - c(A) b ∈ 𝒦_m`.  The two components
are orthogonal and the Pythagorean identity gives `‖c(A) b‖ ≤ ‖p(A) b‖`.  The bound holds up to
and including `m = grade A b`, where the minimum value is `0`.

The hypothesis `m ≤ grade A b` is the one the source leaves implicit by speaking of "the"
characteristic polynomial of `V_mᴴ A V_m` for an orthonormal basis `V_m` of `𝒦_m` with `m`
columns: that basis exists exactly when `dim 𝒦_m = m`, which is `m ≤ grade A b`.  It is needed
here for the same reason, since the degree of the characteristic polynomial is `dim 𝒦_m`, and
past the grade the competitor set contains polynomials of a degree the compression cannot
reach. -/
theorem charpoly_compression_isMinOn {m : ℕ} (hm : m ≤ grade A b) :
    IsMinOn (fun p : 𝕜[X] => ‖aeval A p b‖) {p : 𝕜[X] | p.Monic ∧ p.natDegree = m}
      (LinearMap.charpoly (compression A (subspace A b m))) := by
  set c := LinearMap.charpoly (compression A (subspace A b m)) with hc
  have hcm : c.Monic := LinearMap.charpoly_monic _
  have hcd : c.natDegree = m := by
    rw [hc, LinearMap.charpoly_natDegree, finrank_subspace, min_eq_left hm]
  refine isMinOn_iff.2 fun p hp => ?_
  obtain ⟨hpm, hpd⟩ := hp
  have hdegp : p.degree = (m : ℕ) := hpd ▸ degree_eq_natDegree hpm.ne_zero
  have hdegc : c.degree = (m : ℕ) := hcd ▸ degree_eq_natDegree hcm.ne_zero
  have hlt : (p - c).degree < (m : ℕ) := by
    rw [← hdegp]
    exact degree_sub_lt_left (hdegp.trans hdegc.symm) hpm.ne_zero
      (by rw [hpm.leadingCoeff, hcm.leadingCoeff])
  have hmem : aeval A (p - c) b ∈ subspace A b m := aeval_apply_mem_subspace A b hlt
  have hsplit : aeval A p b = aeval A c b + aeval A (p - c) b := by
    rw [map_sub, LinearMap.sub_apply]
    abel
  have hpyth : ‖aeval A p b‖ ^ 2 = ‖aeval A c b‖ ^ 2 + ‖aeval A (p - c) b‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.inner_left_of_mem_orthogonal hmem (aeval_charpoly_mem_orthogonal A b hm))
  have hnn := sq_nonneg ‖aeval A (p - c) b‖
  exact le_of_sq_le_sq (norm_nonneg _) (by nlinarith)

end Charpoly

/-! ### The cheap Arnoldi residual -/

/-- Coordinates of a Ritz vector: `⟪v_i, V_m y⟫ = y_i` below the grade. -/
private theorem inner_vec_sum [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) (y : Fin m → 𝕜) (i : Fin m) :
    inner 𝕜 (vec A b i) (∑ j, y j • vec A b j) = y i := by
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
      norm_vec_eq_one_of_lt_grade A b (i.2.trans_le hm)]
    simp
  · intro j _ hj
    rw [inner_smul_right, inner_vec_eq_zero A b fun h => hj (Fin.val_injective h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The Hessenberg matrix is the matrix of `A` in the Arnoldi coordinates:
`⟪v_i, A (V_m y)⟫ = (H_m y)_i`. -/
private theorem inner_vec_apply_sum {m : ℕ} (y : Fin m → 𝕜) (i : Fin m) :
    inner 𝕜 (vec A b i) (A (∑ j, y j • vec A b j))
      = (hessenbergSq A b m).mulVec y i := by
  rw [map_sum, inner_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right, hessenbergSq, Matrix.of_apply, coeff, mul_comm]

/-- Saad, *Numerical Methods for Large Eigenvalue Problems*: an eigenpair `(θ, y)` of the Arnoldi
matrix `H_m` yields the Ritz pair `(θ, V_m y)` of `A` on `𝒦_m`.  It is the Rayleigh–Ritz
condition tested against the Arnoldi vectors, which span `𝒦_m` and, below the grade, are
orthonormal, so that `⟪v_i, V_m y⟫ = y_i` and `⟪v_i, A (V_m y)⟫ = (H_m y)_i`.  This is what makes
the residual formula below a statement about Ritz pairs. -/
theorem isRitzPair_of_mulVec_eq_smul [FiniteDimensional 𝕜 (fullSubspace A b)] {m : ℕ}
    (hm : m ≤ grade A b) {y : Fin m → 𝕜} (hy0 : y ≠ 0) {θ : 𝕜}
    (h : (hessenbergSq A b m).mulVec y = θ • y) :
    IsRitzPair A (subspace A b m) θ (∑ j, y j • vec A b j) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy0
  refine ⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (vec_mem_subspace_of_lt A b j.2),
    fun h0 => hi ?_, mem_orthogonal_of_forall_inner_vec A b fun k hk => ?_⟩
  · rw [← inner_vec_sum A b hm y i, h0, inner_zero_right]
    rfl
  · rw [inner_sub_right, inner_smul_right, inner_vec_apply_sum A b y ⟨k, hk⟩,
      inner_vec_sum A b hm y ⟨k, hk⟩, h]
    simp

/-- The last row of the rectangular Hessenberg matrix has a single nonzero entry. -/
private theorem hessenberg_mulVec_last (m : ℕ) (y : Fin (m + 1) → 𝕜) :
    (hessenberg A b (m + 1)).mulVec y (Fin.last (m + 1))
      = coeff A b (m + 1) m * y (Fin.last m) := by
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_single (Fin.last m) (fun j _ hj => ?_) fun h =>
    absurd (Finset.mem_univ (Fin.last m)) h
  rw [hessenberg, Matrix.of_apply, Fin.val_last,
    coeff_eq_zero_of_lt A b (Nat.succ_lt_succ (Fin.val_lt_last hj)), zero_mul]

/-- The rows of the rectangular Hessenberg matrix above the last are the rows of the square
one. -/
private theorem hessenberg_mulVec_castSucc (m : ℕ) (y : Fin (m + 1) → 𝕜) (i : Fin (m + 1)) :
    (hessenberg A b (m + 1)).mulVec y i.castSucc = (hessenbergSq A b (m + 1)).mulVec y i := by
  simp [Matrix.mulVec, dotProduct, hessenberg, hessenbergSq]

/-- Saad, *Numerical Methods for Large Eigenvalue Problems*: for an eigenpair `(θ, y)` of the
Arnoldi matrix `H_m` the residual of the Ritz vector `ũ = V_m y` is a single Arnoldi vector,
`(A - θ) ũ = h_{m+1,m} y_m v_{m+1}`.  Everything but the last row of the Arnoldi relation
`A V_m = V_{m+1} H̄_m` is cancelled by the eigenvalue equation, and the last row of `H̄_m` has the
single entry `h_{m+1,m}` by the Hessenberg structure.  No hypothesis on the grade is needed:
after breakdown both `v_{m+1}` and `h_{m+1,m}` are `0`. -/
theorem apply_sub_smul_sum_eq (m : ℕ) (y : Fin (m + 1) → 𝕜) (θ : 𝕜)
    (hy : (hessenbergSq A b (m + 1)).mulVec y = θ • y) :
    A (∑ j, y j • vec A b j) - θ • ∑ j, y j • vec A b j
      = (coeff A b (m + 1) m * y (Fin.last m)) • vec A b (m + 1) := by
  have hsum := apply_sum A b (m + 1) y
  rw [Fin.sum_univ_castSucc (n := m + 1), hessenberg_mulVec_last A b m y] at hsum
  have hrow : ∀ i : Fin (m + 1), (hessenberg A b (m + 1)).mulVec y i.castSucc = θ * y i := by
    intro i
    rw [hessenberg_mulVec_castSucc A b m y i, hy]
    rfl
  rw [hsum]
  have hcast : ∀ i : Fin (m + 1),
      (hessenberg A b (m + 1)).mulVec y i.castSucc • vec A b (i.castSucc : ℕ)
        = θ • (y i • vec A b (i : ℕ)) := by
    intro i
    rw [hrow i, mul_smul]
    rfl
  rw [Finset.sum_congr rfl fun i _ => hcast i, ← Finset.smul_sum]
  abel

/-- Saad, *Numerical Methods for Large Eigenvalue Problems*: the cheap Arnoldi residual.  For an
eigenpair `(θ, y)` of the Arnoldi matrix `H_m`, the residual norm of the Ritz vector
`ũ = V_m y` is `‖(A - θ) ũ‖ = h_{m+1,m} |y_m|` — the product of one subdiagonal Hessenberg entry
with the last coordinate of the small eigenvector.  It costs nothing to evaluate, which is what
makes a restarted Arnoldi method practical: the accuracy of a Ritz pair is known without ever
forming `ũ`.

The hypothesis is the eigenvalue equation of the small matrix; `isRitzPair_of_mulVec_eq_smul`
says that below the grade it is exactly the statement that `(θ, ũ)` is a Ritz pair of `A` on
`𝒦_m`.  The identity holds past breakdown as well, both sides being `0` there. -/
theorem norm_ritz_residual_eq (m : ℕ) (y : Fin (m + 1) → 𝕜) (θ : 𝕜)
    (hy : (hessenbergSq A b (m + 1)).mulVec y = θ • y) :
    ‖A (∑ j, y j • vec A b j) - θ • ∑ j, y j • vec A b j‖
      = ‖coeff A b (m + 1) m‖ * ‖y (Fin.last m)‖ := by
  rw [apply_sub_smul_sum_eq A b m y θ hy, norm_smul, norm_mul]
  rcases eq_or_ne (vec A b (m + 1)) 0 with h0 | h0
  · rw [coeff, h0, inner_zero_left]
    simp
  · rw [norm_vec_eq_one_of_ne_zero A b h0, mul_one]

end Arnoldi
