import Numlib.Analysis.InnerProductSpace.Projection.Angle
import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Eigen.MinMax
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

Two consequences need nothing beyond the definitions.

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
* The same bound for an *oblique* compression `A_m = Q A P_K`
  (`Krylov.compressionBy_residual_le` and `Krylov.compressionBy_residual_le'`): the search space
  `K` is projected onto by an arbitrary projector `Q`, while the distance to `u` is still measured
  orthogonally, which is what keeps the right-hand side `‖(1 - P_K) u‖`. The constant is a bound
  on `Q (A - μ)` and not on `Q A`: unlike `P_K (1 - P_K)`, the composite `Q (1 - P_K)` need not
  vanish, so the shift does not drop out of the residual identity.

When `A` is symmetric the picture sharpens, and this is where the module meets Courant–Fischer in
`Numlib.Eigen.MinMax` and the angle vocabulary of
`Numlib.Analysis.InnerProductSpace.Projection.Angle`. Everything below is stated with the angles
`K.sinAngle u` and `K.tanAngle u` of an eigenvector `u` to the subspace it is approximated from,
and with `(𝕜 ∙ ũ).sinAngle u` for the angle between `u` and a Ritz vector `ũ`;
`Submodule.sinAngle_span_singleton_comm` is what makes the latter a symmetric notion.

* A Ritz value is the Rayleigh quotient of its Ritz vector
  (`Krylov.IsRitzPair.rayleighQuotient_eq`), it is real for a symmetric `A`
  (`Krylov.IsRitzPair.conj_eq`), and it therefore lies between the extreme eigenvalues of `A`
  (`Krylov.IsRitzPair.mem_Icc`).
* **The variational characterization of the Ritz values**
  (`LinearMap.IsSymmetric.isGreatest_eigenvalues_compression`): the `i`-th Ritz value is the
  max–min value of the Rayleigh quotient of `A` over the `(i + 1)`-dimensional subspaces *of `K`*.
  It is Courant–Fischer applied to the compression and read back on `E`, which is possible because
  the Rayleigh quotient of `compression A K` at `y : K` is the Rayleigh quotient of `A` at `y`
  (`Krylov.rayleighQuotient_compression`).
* **Cauchy interlacing** (`LinearMap.IsSymmetric.eigenvalues_compression_le`): the `i`-th Ritz
  value is at most the `i`-th eigenvalue of `A`, both sorted decreasingly, because the max–min
  over the subspaces of `K` ranges over fewer competitors than the max–min over all subspaces
  of `E`. `LinearMap.IsSymmetric.eigenvalues_compression_mono` is the same argument between two
  nested approximation spaces: every Ritz value increases when the space grows, which is why
  expanding the space in Davidson's method can only help.
* **The error of the largest Ritz value** (`LinearMap.IsSymmetric.ritz_value_error_le`):
  `0 ≤ λ₁ - θ₁ ≤ C tan²θ(u₁, K)` for an eigenvector `u₁` of the largest eigenvalue `λ₁`. The left
  inequality is interlacing; the right one combines
  `LinearMap.IsSymmetric.abs_sub_rayleighQuotient_starProjection_le`, which bounds the error of
  the Rayleigh quotient at `P_K u₁` alone, with the fact that this quotient is at most the largest
  Ritz value. The constant `C` bounds the quadratic form of `A - λ₁`, which is the house form of
  `‖A - λ₁‖` in this library; `Krylov.abs_re_inner_sub_le_opNorm` is the operator-norm reading.
* **The error of the `i`-th Ritz value**
  (`LinearMap.IsSymmetric.ritz_value_error_le_of_forall_inner_eq_zero`): the same statement at a
  general index, `0 ≤ λ_i - θ_i ≤ C (‖u_i - y‖/‖y‖)²` for any nonzero `y ∈ K` orthogonal to the
  first `i` Ritz vectors. What replaces the projection `P_K u₁` of the leading case is a
  competitor for Rayleigh's *recursive* characterization of the `i`-th eigenvalue of the
  compression, and the underlying estimate,
  `LinearMap.IsSymmetric.abs_sub_rayleighQuotient_le`, holds for an arbitrary competitor. Saad's
  own display is the case `y = P_K u_i - P_W u_i` with `W` the span of the leading Ritz vectors,
  where `Submodule.norm_sub_sub_starProjection_sq` evaluates the numerator as
  `‖(1 - P_K) u_i‖² + ‖P_W u_i‖²`.
* **The error of the Ritz vector** (`LinearMap.IsSymmetric.sin_angle_ritzVector_le`): there is a
  Ritz vector `ũ` for a given Ritz value `θ` with
  `sin θ(u, ũ) ≤ √(1 + γ²/δ²) sin θ(u, K)`, where `γ` is the coupling constant above and `δ`
  bounds `‖(A_K - λ) z‖` from below by `δ ‖z‖` on the part of `K` orthogonal to the `θ`-eigenspace
  of the compression. That hypothesis is the separation of `λ` from the *other* Ritz values, and
  `LinearMap.IsSymmetric.mul_norm_le_norm_sub_smul` derives it from exactly that separation.
  `LinearMap.IsSymmetric.abs_ritz_value_sub_le` closes the loop by bounding `|θ - λ|` by
  `C sin²θ(u, ũ)`.

A word on `γ`. The constant of `Krylov.compression_residual_le` and of the vector bound is
`‖P_K A (1 - P_K)‖`, *not* `‖(1 - P_K) A P_K‖`. For a Krylov subspace built by the Arnoldi process
the second of the two is the single Hessenberg entry `h_{m+1,m}`, and the two agree exactly when
`A` is symmetric, each being then the adjoint of the other. So `γ = h_{m+1,m}` may be used
throughout the symmetric results below, and may *not* be used by a nonsymmetric consumer of
`Krylov.compression_residual_le`.

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
with `γ` (Thm 4.3, whose oblique companion is Thm 4.7); §4.3.2 for the Hermitian bounds — the
variational characterization of the Ritz values and the interlacing that follows from it (Prop
4.4 and Cor 4.1), the error of the Rayleigh quotient at `P_K u` and of the largest Ritz value
(Lemma 4.1 and Thm 4.5), and the error of the Ritz vector with the reverse bound on the Ritz
value (Thm 4.6 and Prop 4.5); §6.1–6.2 for the optimality of the characteristic polynomial (Thm
6.1, resting on the polynomial compression identity Prop 6.4 that
`Numlib.Analysis.InnerProductSpace.Projection.Compression` proves) and for the cheap Arnoldi
residual (Prop 6.8). The Courant–Fischer theorem the Hermitian bounds rest on is Thm 1.9 of the
same book, proved in `Numlib.Eigen.MinMax`.

Saad states Thm 4.5 for every index, with the leading Ritz vectors projected out; the general
index is `LinearMap.IsSymmetric.ritz_value_error_le_of_forall_inner_eq_zero`, which takes the
competitor as data rather than constructing it from a spectral projector, and the case `i = 1`
is `LinearMap.IsSymmetric.ritz_value_error_le`, where the projection is the identity. Thm 4.6 is
stated as Saad states it, as the existence of *some* Ritz vector for the given Ritz value — the
one produced is the projection of `P_K u` onto the `θ`-eigenspace of the compression, and when
that projection vanishes the bound is vacuous, its right-hand side being then at least `1`.

[^saad-eigenvalue]: Yousef Saad, *Numerical Methods for Large Eigenvalue Problems*, 2nd edition,
  SIAM, 2011.
-/

open Polynomial

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

/-! ### Projections and angles

Four facts about `Submodule.starProjection` and about the angles of
`Numlib.Analysis.InnerProductSpace.Projection.Angle` that the Hermitian bounds below need. -/

/-- Pythagoras against the best approximation: for `v ∈ K` the error `u - v` splits into the
error `u - P_K u` of the orthogonal projection, which lies in `Kᗮ`, and the vector `P_K u - v`,
which lies in `K`.  Taking `v = 0` recovers the usual splitting of `‖u‖ ^ 2`, and the identity is
the reason `P_K u` is the best approximation of `u` from `K`. -/
theorem norm_sub_sq_eq_add_of_mem (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (u : E) {v : E}
    (hv : v ∈ K) :
    ‖u - v‖ ^ 2 = ‖u - K.starProjection u‖ ^ 2 + ‖K.starProjection u - v‖ ^ 2 := by
  have h1 : u - v = (u - K.starProjection u) + (K.starProjection u - v) := by abel
  have h2 : inner 𝕜 (u - K.starProjection u) (K.starProjection u - v) = (0 : 𝕜) :=
    Submodule.inner_left_of_mem_orthogonal
      (Submodule.sub_mem _ (K.starProjection_apply_mem u) hv)
      (K.sub_starProjection_mem_orthogonal u)
  rw [h1]
  simp only [pow_two]
  exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h2

/-- The orthogonal projection onto the line through `v` sends `u` to `v` itself exactly when `u`
and `v` have the same inner product against `v`.  This is how a vector is recognised as the
projection of another one onto its own line, which is what turns the Ritz vector produced by
`LinearMap.IsSymmetric.sin_angle_ritzVector_le` into an angle. -/
theorem starProjection_span_singleton_eq_self {v u : E}
    (h : inner 𝕜 v u = inner 𝕜 v v) : (𝕜 ∙ v).starProjection u = v :=
  Submodule.eq_starProjection_of_mem_orthogonal (Submodule.mem_span_singleton_self v)
    (Submodule.mem_orthogonal_singleton_iff_inner_right.2 (by rw [inner_sub_right, h, sub_self]))

/-- The cosine of the angle from a vector to the line through another one is the normalized
inner product: on lines, `Submodule.cosAngle` is the ordinary cosine between two vectors. -/
theorem cosAngle_span_singleton {v : E} (hv : v ≠ 0) (w : E) :
    (𝕜 ∙ v).cosAngle w = ‖inner 𝕜 v w‖ / (‖v‖ * ‖w‖) := by
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  rw [cosAngle, starProjection_singleton 𝕜 w, norm_smul, norm_div, RCLike.norm_ofReal,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖v‖ ^ 2)]
  field_simp

/-- The angle between two vectors is symmetric.  Mathlib has no angle between a vector and a
subspace, so this is the statement that the one-sided `Submodule.sinAngle` does specialize to a
symmetric notion on lines; it is what lets the eigenvector bound and the eigenvalue bound below
be written with the same `sin θ(u, ũ)`. -/
theorem sinAngle_span_singleton_comm {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    (𝕜 ∙ v).sinAngle w = (𝕜 ∙ w).sinAngle v := by
  have hnorm : ‖inner 𝕜 v w‖ = ‖inner 𝕜 w v‖ := by
    rw [← inner_conj_symm v w, RCLike.norm_conj]
  have hcos : (𝕜 ∙ v).cosAngle w = (𝕜 ∙ w).cosAngle v := by
    rw [cosAngle_span_singleton hv, cosAngle_span_singleton hw, hnorm, mul_comm ‖w‖ ‖v‖]
  have h1 := (𝕜 ∙ v).cosAngle_sq_add_sinAngle_sq hw
  have h2 := (𝕜 ∙ w).cosAngle_sq_add_sinAngle_sq hv
  rw [hcos] at h1
  exact (pow_left_inj₀ (sinAngle_nonneg _ _) (sinAngle_nonneg _ _) two_ne_zero).1 (by linarith)

/-- Stripping from `u` its best approximation from `K` *outside* a subspace `W ≤ K` splits the
error orthogonally: `‖u - (P_K u - P_W u)‖² = ‖u - P_K u‖² + ‖P_W u‖²`.

This is the estimate behind Saad's Theorem 4.5 for a general index, where `W` is the span of the
Ritz vectors already computed and `P_K u - P_W u` is the competitor orthogonal to them.  Saad
states it as an inequality; it is an equality, because `P_W` annihilates `u - P_K u`. -/
theorem norm_sub_sub_starProjection_sq (W K : Submodule 𝕜 E) [W.HasOrthogonalProjection]
    [K.HasOrthogonalProjection] (hWK : W ≤ K) (u : E) :
    ‖u - (K.starProjection u - W.starProjection u)‖ ^ 2
      = ‖u - K.starProjection u‖ ^ 2 + ‖W.starProjection u‖ ^ 2 := by
  have hsplit : u - (K.starProjection u - W.starProjection u)
      = (u - K.starProjection u) + W.starProjection u := by module
  have horth : inner 𝕜 (u - K.starProjection u) (W.starProjection u) = (0 : 𝕜) :=
    Submodule.inner_left_of_mem_orthogonal (hWK (W.starProjection_apply_mem u))
      (K.sub_starProjection_mem_orthogonal u)
  rw [hsplit]
  simp only [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth]

end Submodule

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

/-! ### A Ritz value is a Rayleigh quotient -/

/-- The Galerkin condition as a scalar equation: testing the residual against the Ritz vector
itself gives `⟪u, A u⟫ = θ ‖u‖ ^ 2`, so the Ritz vector determines the Ritz value. -/
theorem IsRitzPair.inner_self_apply (h : IsRitzPair A K θ u) :
    inner 𝕜 u (A u) = θ * ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
  have h0 := (Submodule.mem_orthogonal K _).1 h.residual_mem_orthogonal u h.mem
  rw [inner_sub_right, inner_smul_right, sub_eq_zero, inner_self_eq_norm_sq_to_K,
    ← RCLike.ofReal_pow] at h0
  exact h0

/-- `IsRitzPair.inner_self_apply` with the operator in the first argument of the inner product,
which is the order the Rayleigh quotient uses. -/
theorem IsRitzPair.inner_apply_self (h : IsRitzPair A K θ u) :
    inner 𝕜 (A u) u = (starRingEnd 𝕜) θ * ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← inner_conj_symm (A u) u, h.inner_self_apply, map_mul, RCLike.conj_ofReal]

/-- The quadratic form of `A` at a Ritz vector is `re θ ‖u‖ ^ 2`. -/
theorem IsRitzPair.re_inner_apply_self (h : IsRitzPair A K θ u) :
    RCLike.re (inner 𝕜 (A u) u) = RCLike.re θ * ‖u‖ ^ 2 := by
  rw [h.inner_apply_self, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im, RCLike.ofReal_re,
    RCLike.ofReal_im]
  ring

/-- A Ritz value is the Rayleigh quotient of its Ritz vector.  No symmetry is needed: the
Galerkin condition alone forces it, which is why a Rayleigh–Ritz procedure computes a Ritz value
as a Rayleigh quotient. -/
theorem IsRitzPair.rayleighQuotient_eq (h : IsRitzPair A K θ u) :
    A.rayleighQuotient u = RCLike.re θ := by
  have hn : (0 : ℝ) < ‖u‖ ^ 2 := by
    have := h.ne_zero
    positivity
  rw [LinearMap.rayleighQuotient, h.re_inner_apply_self, mul_div_assoc,
    div_self (ne_of_gt hn), mul_one]

/-- A Ritz value of a symmetric operator is real, as an eigenvalue of the symmetric compression
must be.  Over `𝕜 = ℝ` this is vacuous; over `ℂ` it is what makes the bounds below, which compare
`θ` with real eigenvalues, statements about `θ` itself. -/
theorem IsRitzPair.conj_eq (hA : A.IsSymmetric) (h : IsRitzPair A K θ u) :
    (starRingEnd 𝕜) θ = θ := by
  have hn : ((‖u‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    simpa using pow_ne_zero 2 (norm_ne_zero_iff.2 h.ne_zero)
  refine mul_right_cancel₀ hn ?_
  rw [← h.inner_apply_self, hA u u, h.inner_self_apply]

/-- The Rayleigh quotient of the compression at `y : K` is the Rayleigh quotient of `A` at `y`:
the projection is invisible against a test vector taken from `K`.  This is what makes the
variational characterizations of the Ritz values and of the eigenvalues of `A` comparable, and it
is the whole content of Cauchy interlacing. -/
theorem rayleighQuotient_compression (A : E →ₗ[𝕜] E) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (y : K) :
    (compression A K).rayleighQuotient y = A.rayleighQuotient (y : E) := by
  rw [LinearMap.rayleighQuotient, LinearMap.rayleighQuotient, compression.inner_apply]
  rfl

/-- Every Ritz value of a symmetric `A` lies between the extreme eigenvalues of `A`, because it
is a Rayleigh quotient of `A` and `LinearMap.IsSymmetric.rayleighQuotient_mem_Icc` traps those.
The sharper statement, that the `i`-th Ritz value is at most the `i`-th eigenvalue, is
`LinearMap.IsSymmetric.eigenvalues_compression_le`. -/
theorem IsRitzPair.mem_Icc [FiniteDimensional 𝕜 E] {n : ℕ} (hA : A.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n + 1) (h : IsRitzPair A K θ u) :
    RCLike.re θ ∈ Set.Icc (hA.eigenvalues hn (Fin.last n)) (hA.eigenvalues hn 0) := by
  rw [← h.rayleighQuotient_eq]
  exact hA.rayleighQuotient_mem_Icc hn h.ne_zero

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

/-! ### The oblique residual bounds

An oblique projection method takes a search subspace `K` and a test subspace `L`, and its
compression is `A_m = Q_K^L A P_K` for the projector `Q_K^L` onto `K` along `Lᗮ`
(Saad, *Numerical Methods for Large Eigenvalue Problems*, §4.3.3).  Composing with the
*orthogonal* `P_K` on the right is what makes `A_m` vanish on `Kᗮ`, so that the a priori bounds
are again in terms of `‖(1 - P_K) u‖`.  Only the projector `Q` is oblique here; the distance from
`u` to `K` is still measured orthogonally. -/

/-- The oblique residual identity: for any projector `Q` onto `K` and an exact eigenpair
`(μ, u)`, `(A_m - μ) P_K u = -Q (A - μ) (1 - P_K) u`.

Unlike the orthogonal case (`compression.apply_sub_smul_orthogonalProjection`) the shift `μ` does
not drop out of the right-hand side, because `Q (1 - P_K)` need not vanish when `Q` is oblique.
That is why the constant of `Krylov.compressionBy_residual_le` is a bound on `Q (A - μ)` and not
on `Q A`. -/
theorem compressionBy_apply_sub_smul_orthogonalProjection {A : E →ₗ[𝕜] E} {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {Q : E →ₗ[𝕜] K} (hQ : ∀ x : K, Q x = x) {μ : 𝕜} {u : E}
    (hu : A u = μ • u) :
    (compressionBy Q A (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : E)
      = -(Q (A (u - K.starProjection u) - μ • (u - K.starProjection u)) : E) := by
  have hQP : (Q (K.starProjection u) : E) = K.starProjection u :=
    congrArg Subtype.val (hQ ⟨_, K.starProjection_apply_mem u⟩)
  have harg : A (u - K.starProjection u) - μ • (u - K.starProjection u)
      = -(A (K.starProjection u) - μ • K.starProjection u) := by
    rw [map_sub, hu]; module
  rw [harg]
  simp only [map_neg, map_sub, map_smul, Submodule.coe_neg, Submodule.coe_sub,
    Submodule.coe_smul, hQP, neg_neg]
  rfl

/-- **The oblique residual bound** (Saad, *Numerical Methods for Large Eigenvalue Problems*,
Thm 4.7, first inequality): with `Q` a projector onto `K` and `γ` bounding `Q (A - μ)` on `Kᗮ`,
the Ritz pair `(μ, P_K u)` of the oblique compression `A_m = Q A P_K` has residual
`‖(A_m - μ) P_K u‖ ≤ γ ‖(1 - P_K) u‖`.

The twin of `Krylov.compression_residual_le`, with the constant supplied as a hypothesis in the
same style; taking `Q = P_K` recovers that theorem, since `P_K (A - μ) x = P_K (A x)` for
`x ∈ Kᗮ`. -/
theorem compressionBy_residual_le {A : E →ₗ[𝕜] E} {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {Q : E →ₗ[𝕜] K} (hQ : ∀ x : K, Q x = x) {γ : ℝ} {μ : 𝕜}
    (hγ : ∀ x ∈ Kᗮ, ‖(Q (A x - μ • x) : E)‖ ≤ γ * ‖x‖) {u : E} (hu : A u = μ • u) :
    ‖(compressionBy Q A (K.orthogonalProjectionOnto u) - μ • K.orthogonalProjectionOnto u : E)‖
      ≤ γ * ‖u - K.starProjection u‖ := by
  rw [compressionBy_apply_sub_smul_orthogonalProjection hQ hu, norm_neg]
  exact hγ _ (K.sub_starProjection_mem_orthogonal u)

/-- **The oblique residual bound for the whole eigenvector** (Saad, *Numerical Methods for Large
Eigenvalue Problems*, Thm 4.7, second inequality): `‖(A_m - μ) u‖ ≤ √(|μ|² + γ²) ‖(1 - P_K) u‖`.

`A_m = Q A P_K` kills `Kᗮ`, so `(A_m - μ) u = (A_m - μ) P_K u - μ (1 - P_K) u`, and the two terms
lie in `K` and in `Kᗮ`; Pythagoras gives the constant, exactly as in
`Krylov.compression_residual_le'`. -/
theorem compressionBy_residual_le' {A : E →ₗ[𝕜] E} {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {Q : E →ₗ[𝕜] K} (hQ : ∀ x : K, Q x = x) {γ : ℝ} {μ : 𝕜}
    (hγ : ∀ x ∈ Kᗮ, ‖(Q (A x - μ • x) : E)‖ ≤ γ * ‖x‖) {u : E} (hu : A u = μ • u) :
    ‖(compressionBy Q A (K.orthogonalProjectionOnto u) : E) - μ • u‖
      ≤ Real.sqrt (‖μ‖ ^ 2 + γ ^ 2) * ‖u - K.starProjection u‖ := by
  set v : E := (compressionBy Q A (K.orthogonalProjectionOnto u) : E) with hv
  have hcoe : (compressionBy Q A (K.orthogonalProjectionOnto u)
      - μ • K.orthogonalProjectionOnto u : E) = v - μ • K.starProjection u := rfl
  have hle : ‖v - μ • K.starProjection u‖ ≤ γ * ‖u - K.starProjection u‖ := by
    rw [← hcoe]; exact compressionBy_residual_le hQ hγ hu
  have hrmem : v - μ • K.starProjection u ∈ K :=
    Submodule.sub_mem _ (compressionBy Q A (K.orthogonalProjectionOnto u)).2
      (Submodule.smul_mem _ _ (K.starProjection_apply_mem u))
  have hqmem : (-μ) • (u - K.starProjection u) ∈ Kᗮ :=
    Submodule.smul_mem _ _ (K.sub_starProjection_mem_orthogonal u)
  have hsplit : v - μ • u
      = (v - μ • K.starProjection u) + (-μ) • (u - K.starProjection u) := by module
  have hpyth : ‖v - μ • u‖ ^ 2
      = ‖v - μ • K.starProjection u‖ ^ 2 + ‖μ‖ ^ 2 * ‖u - K.starProjection u‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      (Submodule.inner_right_of_mem_orthogonal hrmem hqmem), norm_smul, norm_neg]
    ring
  have hsq : ‖v - μ • u‖ ^ 2 ≤ (Real.sqrt (‖μ‖ ^ 2 + γ ^ 2) * ‖u - K.starProjection u‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [hpyth, hle, norm_nonneg (v - μ • K.starProjection u),
      norm_nonneg (u - K.starProjection u)]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h

/-! ### The shifted quadratic form

The Hermitian bounds all read a difference of an eigenvalue and a Rayleigh quotient as the
quadratic form of `A - λ`, and their hypothesis is a bound on that form.  These are the three
facts about it that the proofs use. -/

/-- The quadratic form of `A - λ` in real form. -/
private theorem re_inner_sub (A : E →ₗ[𝕜] E) (lam : ℝ) (x : E) :
    RCLike.re (inner 𝕜 (A x) x - (lam : 𝕜) * inner 𝕜 x x)
      = RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2 := by
  rw [map_sub, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul,
    RCLike.ofReal_re]

/-- Adding a multiple of an eigenvector of `A` for the real eigenvalue `lam` does not change the
quadratic form of `A - lam`, since that form has the eigenvector in its kernel and `A - lam` is
symmetric. -/
private theorem inner_shift_add (hA : A.IsSymmetric) {lam : ℝ} (hu : A u = (lam : 𝕜) • u)
    (x : E) (c : 𝕜) :
    inner 𝕜 (A (x + c • u)) (x + c • u) - (lam : 𝕜) * inner 𝕜 (x + c • u) (x + c • u)
      = inner 𝕜 (A x) x - (lam : 𝕜) * inner 𝕜 x x := by
  have h1 : inner 𝕜 (A u) x = (lam : 𝕜) * inner 𝕜 u x := by
    rw [hu, inner_smul_left, RCLike.conj_ofReal]
  have h2 : inner 𝕜 (A x) u = (lam : 𝕜) * inner 𝕜 x u := by
    rw [hA x u, hu, inner_smul_right]
  have h3 : inner 𝕜 (A u) u = (lam : 𝕜) * inner 𝕜 u u := by
    rw [hu, inner_smul_left, RCLike.conj_ofReal]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, h1, h2, h3]
  ring

/-- The quadratic form of `A - lam` is even. -/
private theorem inner_shift_neg (A : E →ₗ[𝕜] E) (lam : ℝ) (x : E) :
    inner 𝕜 (A (-x)) (-x) - (lam : 𝕜) * inner 𝕜 (-x) (-x)
      = inner 𝕜 (A x) x - (lam : 𝕜) * inner 𝕜 x x := by
  simp

/-- The quadratic form of `A - lam` at `u - w` and at `w` agree, for an eigenvector `u`. -/
private theorem inner_sub_shift (hA : A.IsSymmetric) {lam : ℝ} (hu : A u = (lam : 𝕜) • u)
    (w : E) :
    inner 𝕜 (A (u - w)) (u - w) - (lam : 𝕜) * inner 𝕜 (u - w) (u - w)
      = inner 𝕜 (A w) w - (lam : 𝕜) * inner 𝕜 w w := by
  have h1 := inner_shift_add hA hu (-w) 1
  rw [show -w + (1 : 𝕜) • u = u - w by module] at h1
  rw [h1, inner_shift_neg]

/-- An `A` bounded in operator norm satisfies the quadratic-form hypothesis of the Hermitian
bounds with `C = ‖A - λ‖`, by Cauchy–Schwarz.  As with `γ`, the bounds themselves take `C` as a
hypothesis rather than as this operator norm, so that they apply to an unbounded `A` and to a
sharper `C` obtained by other means; this is the same choice
`Numlib.Eigen.MinMax` makes for Weyl's inequality. -/
theorem abs_re_inner_sub_le_opNorm (A : E →L[𝕜] E) (lam : ℝ) (x : E) :
    |RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2|
      ≤ ‖A - (lam : 𝕜) • (1 : E →L[𝕜] E)‖ * ‖x‖ ^ 2 := by
  have hx : inner 𝕜 ((A - (lam : 𝕜) • (1 : E →L[𝕜] E)) x) x
      = inner 𝕜 (A x) x - (lam : 𝕜) * inner 𝕜 x x := by
    simp [inner_sub_left, inner_smul_left, RCLike.conj_ofReal]
  have hre : RCLike.re (inner 𝕜 ((A - (lam : 𝕜) • (1 : E →L[𝕜] E)) x) x)
      = RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2 := by
    rw [hx, map_sub, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul,
      RCLike.ofReal_re]
  rw [← hre]
  calc |RCLike.re (inner 𝕜 ((A - (lam : 𝕜) • (1 : E →L[𝕜] E)) x) x)|
      ≤ ‖inner 𝕜 ((A - (lam : 𝕜) • (1 : E →L[𝕜] E)) x) x‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖(A - (lam : 𝕜) • (1 : E →L[𝕜] E)) x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖A - (lam : 𝕜) • (1 : E →L[𝕜] E)‖ * ‖x‖) * ‖x‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖A - (lam : 𝕜) • (1 : E →L[𝕜] E)‖ * ‖x‖ ^ 2 := by ring

end Krylov

namespace LinearMap.IsSymmetric

open Krylov

/-! ### The Hermitian bounds

For a symmetric `A` the Ritz values are the max–min values of the Rayleigh quotient over the
subspaces of `K`, which is Courant–Fischer applied to the compression, and the errors of both the
Ritz values and the Ritz vectors are controlled by the angle between the exact eigenvector and
`K`.  These are the sharp bounds of the Rayleigh–Ritz procedure. -/

/-- **Courant–Fischer for the Ritz values**: the `i`-th Ritz value of a symmetric `A` on `K` is
the max–min value of the Rayleigh quotient *of `A`* over the `(i + 1)`-dimensional subspaces of
`K`.  It is Courant–Fischer applied to the compression, restated on `E`: the Rayleigh quotient of
`compression A K` at `y : K` is that of `A` at `y` (`Krylov.rayleighQuotient_compression`), and
the `(i + 1)`-dimensional subspaces of `K` correspond to those of the subtype under
`Submodule.map K.subtype` and `Submodule.comap K.subtype`.

Stated as an `IsGreatest` over an explicit set of reals, following
`LinearMap.IsSymmetric.isGreatest_eigenvalues`, which the `iSup`/`iInf` forms would decorate with
a junk value. -/
theorem isGreatest_eigenvalues_compression [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (K : Submodule 𝕜 E) {m : ℕ} (hm : Module.finrank 𝕜 K = m) (i : Fin m) :
    IsGreatest {c : ℝ | ∃ S : Submodule 𝕜 E, S ≤ K ∧ Module.finrank 𝕜 S = (i : ℕ) + 1 ∧
        ∀ x ∈ S, x ≠ 0 → c ≤ A.rayleighQuotient x}
      ((compression.isSymmetric A K hA).eigenvalues hm i) := by
  obtain ⟨⟨S, hS, hb⟩, hub⟩ := (compression.isSymmetric A K hA).isGreatest_eigenvalues hm i
  constructor
  · refine ⟨S.map K.subtype, ?_, ?_, ?_⟩
    · rintro x ⟨y, -, rfl⟩
      exact y.2
    · rw [Submodule.finrank_map_subtype_eq, hS]
    · rintro x ⟨y, hy, rfl⟩ hx0
      rw [Submodule.subtype_apply, ← rayleighQuotient_compression A K y]
      exact hb y hy fun h => hx0 (by rw [h]; rfl)
  · rintro c ⟨T, hTK, hTdim, hTb⟩
    refine hub ⟨T.comap K.subtype, ?_, ?_⟩
    · rw [(Submodule.comapSubtypeEquivOfLe hTK).finrank_eq, hTdim]
    · intro y hy hy0
      rw [rayleighQuotient_compression A K y]
      exact hTb _ hy fun h => hy0 (Subtype.ext h)

/-- **Cauchy interlacing**, from below: for a symmetric `A` on a finite-dimensional space and any
subspace `K`, the `i`-th eigenvalue of the compression `compression A K` — that is, the `i`-th
Ritz value — is at most the `i`-th eigenvalue of `A`, both families being sorted decreasingly.

It is `isGreatest_eigenvalues_compression` against `LinearMap.IsSymmetric.isGreatest_eigenvalues`:
the max–min defining the `i`-th Ritz value ranges over the `(i + 1)`-dimensional subspaces of `K`,
that defining the `i`-th eigenvalue of `A` over all of them, and the first family is contained in
the second, so any bound witnessed inside `K` is a competitor for `A`.

`hmn` only supplies the index cast, and is discharged from `Submodule.finrank_le`. -/
theorem eigenvalues_compression_le [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (K : Submodule 𝕜 E) {n m : ℕ} (hn : Module.finrank 𝕜 E = n) (hm : Module.finrank 𝕜 K = m)
    (hmn : m ≤ n) (i : Fin m) :
    (compression.isSymmetric A K hA).eigenvalues hm i ≤ hA.eigenvalues hn (Fin.castLE hmn i) := by
  obtain ⟨⟨S, -, hS, hb⟩, -⟩ := hA.isGreatest_eigenvalues_compression K hm i
  exact (hA.isGreatest_eigenvalues hn (Fin.castLE hmn i)).2 ⟨S, hS, hb⟩

/-- **The Ritz values increase with the subspace**, which is the mechanism behind the
convergence of Davidson's method (Saad, *Numerical Methods for Large Eigenvalue Problems*,
Thm 8.1): enlarging the approximation space can only improve every Ritz value, both families
being sorted decreasingly.

It is `isGreatest_eigenvalues_compression` twice: the max–min for `K` ranges over the
`(i + 1)`-dimensional subspaces of `K`, that for `K'` over those of `K'`, and the first family is
contained in the second, so a bound witnessed inside `K` is a competitor inside `K'`.  Cauchy
interlacing `eigenvalues_compression_le` is the extreme case `K' = ⊤`, proved the same way. -/
theorem eigenvalues_compression_mono [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {K K' : Submodule 𝕜 E} (hKK' : K ≤ K') {m m' : ℕ} (hm : Module.finrank 𝕜 K = m)
    (hm' : Module.finrank 𝕜 K' = m') (hmm' : m ≤ m') (i : Fin m) :
    (compression.isSymmetric A K hA).eigenvalues hm i
      ≤ (compression.isSymmetric A K' hA).eigenvalues hm' (Fin.castLE hmm' i) := by
  obtain ⟨⟨S, hSK, hS, hb⟩, -⟩ := hA.isGreatest_eigenvalues_compression K hm i
  refine (hA.isGreatest_eigenvalues_compression K' hm' (Fin.castLE hmm' i)).2
    ⟨S, hSK.trans hKK', ?_, hb⟩
  simpa using hS

/-- If `W` sits inside the `θ`-eigenspace of a symmetric `T` and `T - lam` is bounded below by
`δ` on `Wᗮ`, then `δ ‖y - P_W y‖ ≤ ‖(T - lam) y‖` for *every* `y`, not only for `y ∈ Wᗮ`.

The component of `y` in `W` contributes `(θ - lam) P_W y`, which is orthogonal to the
contribution `(T - lam)(y - P_W y)` of the other component, because `W` is `T`-invariant and `T`
is symmetric, so `Wᗮ` is `T`-invariant too.  Pythagoras then discards the `W` term.  This is the
step of Saad's eigenvector bound that turns a small residual into a small angle to the eigenspace
of the nearest Ritz value. -/
theorem mul_norm_sub_starProjection_le {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {W : Submodule 𝕜 E}
    [W.HasOrthogonalProjection] {θ lam δ : ℝ} (hW : ∀ q ∈ W, T q = (θ : 𝕜) • q)
    (hδ : ∀ z ∈ Wᗮ, δ * ‖z‖ ≤ ‖T z - (lam : 𝕜) • z‖) (y : E) :
    δ * ‖y - W.starProjection y‖ ≤ ‖T y - (lam : 𝕜) • y‖ := by
  have hpW : W.starProjection y ∈ W := W.starProjection_apply_mem y
  have hyp : y - W.starProjection y ∈ Wᗮ := W.sub_starProjection_mem_orthogonal y
  have hinv : T (y - W.starProjection y) - (lam : 𝕜) • (y - W.starProjection y) ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal]
    intro q hq
    have hqz : inner 𝕜 q (y - W.starProjection y) = (0 : 𝕜) :=
      (Submodule.mem_orthogonal W _).1 hyp q hq
    have h1 : inner 𝕜 q (T (y - W.starProjection y)) = (0 : 𝕜) := by
      rw [← hT q (y - W.starProjection y), hW q hq, inner_smul_left, hqz, mul_zero]
    rw [inner_sub_right, inner_smul_right, h1, hqz, mul_zero, sub_zero]
  have hsplit : T y - (lam : 𝕜) • y
      = ((θ : 𝕜) - (lam : 𝕜)) • W.starProjection y
        + (T (y - W.starProjection y) - (lam : 𝕜) • (y - W.starProjection y)) := by
    rw [map_sub, hW _ hpW, sub_smul]
    module
  have horth : inner 𝕜 (((θ : 𝕜) - (lam : 𝕜)) • W.starProjection y)
      (T (y - W.starProjection y) - (lam : 𝕜) • (y - W.starProjection y)) = (0 : 𝕜) :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.smul_mem _ _ hpW) hinv
  have hnorm : ‖T y - (lam : 𝕜) • y‖ ^ 2
      = ‖((θ : 𝕜) - (lam : 𝕜)) • W.starProjection y‖ ^ 2
        + ‖T (y - W.starProjection y) - (lam : 𝕜) • (y - W.starProjection y)‖ ^ 2 := by
    rw [hsplit]
    simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hlow := hδ _ hyp
  nlinarith [norm_nonneg (T y - (lam : 𝕜) • y),
    norm_nonneg (T (y - W.starProjection y) - (lam : 𝕜) • (y - W.starProjection y)),
    sq_nonneg ‖((θ : 𝕜) - (lam : 𝕜)) • W.starProjection y‖,
    norm_nonneg (y - W.starProjection y)]

/-- The lower bound `mul_norm_sub_starProjection_le` asks for, from the separation of `lam` from
the eigenvalues of `T` other than `θ`.  Expanded in an eigenvector basis, `(T - lam) z` has
coordinates `(θ_i - lam) c_i`, and `z ⟂ ker (T - θ)` kills the coordinates with `θ_i = θ`, so
every surviving one is scaled by at least `δ`.

For `T = compression A K` this says exactly what Saad's `δ` is: the distance from the exact
eigenvalue `lam` to the set of Ritz values other than `θ`. -/
theorem mul_norm_le_norm_sub_smul [FiniteDimensional 𝕜 E] {n : ℕ} {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {θ lam δ : ℝ} (hδ0 : 0 ≤ δ)
    (hsep : ∀ i : Fin n, hT.eigenvalues hn i ≠ θ → δ ≤ |hT.eigenvalues hn i - lam|)
    {z : E} (hz : z ∈ (Module.End.eigenspace T (θ : 𝕜))ᗮ) :
    δ * ‖z‖ ≤ ‖T z - (lam : 𝕜) • z‖ := by
  have hrepr : ∀ i, ‖(hT.eigenvectorBasis hn).repr (T z - (lam : 𝕜) • z) i‖
      = |hT.eigenvalues hn i - lam| * ‖(hT.eigenvectorBasis hn).repr z i‖ := by
    intro i
    have h1 : (hT.eigenvectorBasis hn).repr (T z - (lam : 𝕜) • z) i
        = ((hT.eigenvalues hn i - lam : ℝ) : 𝕜) * (hT.eigenvectorBasis hn).repr z i := by
      rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, inner_sub_right,
        inner_smul_right, ← hT (hT.eigenvectorBasis hn i) z, hT.apply_eigenvectorBasis,
        inner_smul_left, RCLike.conj_ofReal, RCLike.ofReal_sub]
      ring
    rw [h1, norm_mul, RCLike.norm_ofReal]
  have hzero : ∀ i, hT.eigenvalues hn i = θ → (hT.eigenvectorBasis hn).repr z i = 0 := by
    intro i hi
    have hbi : hT.eigenvectorBasis hn i ∈ Module.End.eigenspace T (θ : 𝕜) :=
      Module.End.mem_eigenspace_iff.2 (by rw [hT.apply_eigenvectorBasis, hi])
    rw [OrthonormalBasis.repr_apply_apply]
    exact (Submodule.mem_orthogonal _ z).1 hz _ hbi
  have hsq : (δ * ‖z‖) ^ 2 ≤ ‖T z - (lam : 𝕜) • z‖ ^ 2 := by
    rw [mul_pow, hT.norm_sq_eq_sum_norm_repr_sq hn z,
      hT.norm_sq_eq_sum_norm_repr_sq hn (T z - (lam : 𝕜) • z), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hrepr i, mul_pow]
    by_cases hi : hT.eigenvalues hn i = θ
    · rw [hzero i hi]
      simp
    · have h := hsep i hi
      have habs : (0 : ℝ) ≤ |hT.eigenvalues hn i - lam| := abs_nonneg _
      have hsq2 : δ ^ 2 ≤ |hT.eigenvalues hn i - lam| ^ 2 := by nlinarith [h, hδ0, habs]
      exact mul_le_mul_of_nonneg_right hsq2 (sq_nonneg _)
  have hstep := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (mul_nonneg hδ0 (norm_nonneg z)), Real.sqrt_sq (norm_nonneg _)] at hstep

/-- **Saad's Lemma 4.2**: for a symmetric `A`, an eigenpair `(lam, u)` and any nonzero competitor
`y`, the Rayleigh quotient at `y` differs from `lam` by at most `C (‖u - y‖/‖y‖)²`, where `C`
bounds the quadratic form of `A - lam` (Saad, *Numerical Methods for Large Eigenvalue Problems*,
Lemma 4.1 for `y = P_K u` and Lemma 4.2 in general).

The mechanism is that the quadratic form of `A - lam` has `u` in its kernel and is symmetric, so
it takes the same value at `y` as at `u - y`:
`⟪(A - lam) y, y⟫ = ⟪(A - lam)(u - y), (u - y)⟫`.  Dividing by `‖y‖²` gives the ratio.  Nothing
here is special to a projection: the whole Rayleigh–Ritz eigenvalue analysis is this lemma
applied to a competitor chosen inside the approximation space. -/
theorem abs_sub_rayleighQuotient_le {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {lam C : ℝ}
    (hC : ∀ x : E, |RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2| ≤ C * ‖x‖ ^ 2)
    {u : E} (hu : A u = (lam : 𝕜) • u) {y : E} (hy : y ≠ 0) :
    |lam - A.rayleighQuotient y| ≤ C * (‖u - y‖ / ‖y‖) ^ 2 := by
  have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hvpos : (0 : ℝ) < ‖y‖ ^ 2 := by positivity
  have key : RCLike.re (inner 𝕜 (A y) y) - lam * ‖y‖ ^ 2
      = RCLike.re (inner 𝕜 (A (u - y)) (u - y)) - lam * ‖u - y‖ ^ 2 := by
    rw [← re_inner_sub A lam y, ← re_inner_sub A lam (u - y), inner_sub_shift hA hu y]
  have hrw : lam - A.rayleighQuotient y
      = (lam * ‖y‖ ^ 2 - RCLike.re (inner 𝕜 (A y) y)) / ‖y‖ ^ 2 := by
    rw [LinearMap.rayleighQuotient, sub_div, mul_div_assoc, div_self (ne_of_gt hvpos), mul_one]
  have hcancel : C * (‖u - y‖ / ‖y‖) ^ 2 * ‖y‖ ^ 2 = C * ‖u - y‖ ^ 2 := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hvpos, div_le_iff₀ hvpos, hcancel, abs_sub_comm, key]
  exact hC _

/-- The error of the Rayleigh quotient at the projection of an eigenvector: for a symmetric `A`,
an eigenpair `(lam, u)` and a subspace `K` that captures some of `u`,
`|lam - μ_A(P_K u)| ≤ C tan²θ(u, K)`, where `C` bounds the quadratic form of `A - lam`.

The identity behind it is that `(A - lam) P_K u = -(A - lam)(1 - P_K) u`, so that testing against
`P_K u` and using the symmetry of `A - lam` and `(A - lam) u = 0` moves the whole quadratic form
onto the part of `u` that `K` misses:
`⟪(A - lam) P_K u, P_K u⟫ = ⟪(A - lam)(1 - P_K) u, (1 - P_K) u⟫`.  Dividing by `‖P_K u‖ ^ 2` turns
`‖(1 - P_K) u‖ ^ 2 / ‖P_K u‖ ^ 2` into `tan²θ(u, K)`.

The hypothesis `P_K u ≠ 0` is genuine, and not only because `tanAngle` is junk there: with `u`
orthogonal to `K` the left-hand side is `|lam|` and the right-hand side is `0`. -/
theorem abs_sub_rayleighQuotient_starProjection_le {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] {lam C : ℝ}
    (hC : ∀ x : E, |RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2| ≤ C * ‖x‖ ^ 2)
    {u : E} (hu : A u = (lam : 𝕜) • u) (hPu : K.starProjection u ≠ 0) :
    |lam - A.rayleighQuotient (K.starProjection u)| ≤ C * K.tanAngle u ^ 2 := by
  have h := hA.abs_sub_rayleighQuotient_le hC hu hPu
  rwa [← K.tanAngle_mul_norm hPu, mul_div_assoc, div_self (norm_ne_zero_iff.2 hPu), mul_one] at h

/-- The error of the largest Ritz value: for a symmetric `A` with largest eigenvalue `λ₁` and an
eigenvector `u` for it, the largest Ritz value `θ₁` on `K` satisfies
`0 ≤ λ₁ - θ₁ ≤ C tan²θ(u, K)`, with `C` bounding the quadratic form of `A - λ₁`.

The lower bound is `eigenvalues_compression_le` at `i = 0`.  For the upper bound, `P_K u` is a
nonzero element of `K`, so the Rayleigh quotient of `A` there is at most `θ₁`, and
`abs_sub_rayleighQuotient_starProjection_le` bounds `λ₁` minus that quotient.  So a subspace whose
angle to `u` is small carries a Ritz value close to `λ₁`, at a rate quadratic in the angle. -/
theorem ritz_value_error_le [FiniteDimensional 𝕜 E] {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {K : Submodule 𝕜 E} {n m : ℕ} (hn : Module.finrank 𝕜 E = n + 1)
    (hm : Module.finrank 𝕜 K = m + 1) {C : ℝ}
    (hC : ∀ x : E, |RCLike.re (inner 𝕜 (A x) x) - hA.eigenvalues hn 0 * ‖x‖ ^ 2| ≤ C * ‖x‖ ^ 2)
    {u : E} (hu : A u = ((hA.eigenvalues hn 0 : ℝ) : 𝕜) • u) (hPu : K.starProjection u ≠ 0) :
    hA.eigenvalues hn 0 - (compression.isSymmetric A K hA).eigenvalues hm 0
      ∈ Set.Icc 0 (C * K.tanAngle u ^ 2) := by
  have hmn : m + 1 ≤ n + 1 := by
    have h := Submodule.finrank_le (R := 𝕜) K
    rw [hm, hn] at h
    exact h
  have hz : Fin.castLE hmn (0 : Fin (m + 1)) = (0 : Fin (n + 1)) := by ext; simp
  have hycoe : ((K.orthogonalProjectionOnto u : K) : E) = K.starProjection u := rfl
  have hy0 : (K.orthogonalProjectionOnto u : K) ≠ 0 := fun h => hPu (by rw [← hycoe, h]; rfl)
  have h1 : A.rayleighQuotient (K.starProjection u)
      ≤ (compression.isSymmetric A K hA).eigenvalues hm 0 := by
    have h := ((compression.isSymmetric A K hA).rayleighQuotient_mem_Icc hm hy0).2
    rwa [rayleighQuotient_compression A K _, hycoe] at h
  have h2 := (abs_le.1 (hA.abs_sub_rayleighQuotient_starProjection_le K hC hu hPu)).2
  have h3 := hA.eigenvalues_compression_le K hn hm hmn 0
  rw [hz] at h3
  exact ⟨by linarith, by linarith⟩

/-- **The error of the `i`-th Ritz value** (Saad, *Numerical Methods for Large Eigenvalue
Problems*, Thm 4.5): if `y` is a nonzero vector of `K` orthogonal to the first `i` Ritz vectors,
then `0 ≤ λ_i - θ_i ≤ C (‖u_i - y‖/‖y‖)²`, with `u_i` an eigenvector of `A` for `λ_i` and `C`
bounding the quadratic form of `A - λ_i`.

The lower bound is Cauchy interlacing.  For the upper bound, `y` competes in Rayleigh's recursive
characterization of the `i`-th eigenvalue of the compression
(`isGreatest_rayleighQuotient_orthogonal`), so its Rayleigh quotient is at most `θ_i`, and
`abs_sub_rayleighQuotient_le` bounds `λ_i` minus that quotient.  Only the orthogonality to the
previous Ritz vectors is used, which is what the name records; `ritz_value_error_le` is the case
`i = 0`, where the condition is empty and `y = P_K u` is the natural competitor.

Saad's own display is the case `y = P_K u_i - P_W u_i` for `W` the span of the Ritz vectors
already computed: `Submodule.norm_sub_sub_starProjection_sq` evaluates the numerator there as
`‖(1 - P_K) u_i‖² + ‖P_W u_i‖²`, which is his `‖(I - P_K)u_i‖² + ‖Q̃_i u_i‖²`. -/
theorem ritz_value_error_le_of_forall_inner_eq_zero [FiniteDimensional 𝕜 E]
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {K : Submodule 𝕜 E} {n m : ℕ}
    (hn : Module.finrank 𝕜 E = n) (hm : Module.finrank 𝕜 K = m) (hmn : m ≤ n) (i : Fin m)
    {C : ℝ}
    (hC : ∀ x : E, |RCLike.re (inner 𝕜 (A x) x)
      - hA.eigenvalues hn (Fin.castLE hmn i) * ‖x‖ ^ 2| ≤ C * ‖x‖ ^ 2)
    {u : E} (hu : A u = ((hA.eigenvalues hn (Fin.castLE hmn i) : ℝ) : 𝕜) • u)
    {y : E} (hyK : y ∈ K) (hy0 : y ≠ 0)
    (hyorth : ∀ j : Fin m, j < i →
      inner 𝕜 ((((compression.isSymmetric A K hA).eigenvectorBasis hm j : K) : E)) y = (0 : 𝕜)) :
    hA.eigenvalues hn (Fin.castLE hmn i) - (compression.isSymmetric A K hA).eigenvalues hm i
      ∈ Set.Icc 0 (C * (‖u - y‖ / ‖y‖) ^ 2) := by
  have hysub : (⟨y, hyK⟩ : K) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have h1 : A.rayleighQuotient y ≤ (compression.isSymmetric A K hA).eigenvalues hm i := by
    have hmem := ((compression.isSymmetric A K hA).isGreatest_rayleighQuotient_orthogonal hm i).2
      ⟨⟨y, hyK⟩, hysub, fun j hj => hyorth j hj, rfl⟩
    rwa [rayleighQuotient_compression A K ⟨y, hyK⟩] at hmem
  have h2 := (abs_le.1 (hA.abs_sub_rayleighQuotient_le hC hu hy0)).2
  have h3 := hA.eigenvalues_compression_le K hn hm hmn i
  exact ⟨by linarith, by linarith⟩

/-- The error of the Ritz vector: for a symmetric `A`, an eigenpair `(lam, u)` and a Ritz value
`θ` on `K`, there is a Ritz vector `w` for `θ` with
`sin θ(u, w) ≤ √(1 + γ² / δ²) sin θ(u, K)`.  Here `γ` is the coupling constant of
`Krylov.compression_residual_le` and `δ` bounds `‖(A_K - lam) z‖` from below by `δ ‖z‖ ` on the
part of `K` orthogonal to the `θ`-eigenspace of the compression; by
`mul_norm_le_norm_sub_smul` that hypothesis is the separation of `lam` from the Ritz values other
than `θ`.  So an approximation subspace at a small angle to an eigenvector contains a Ritz vector
at a comparably small angle to it, provided the corresponding Ritz value is well separated.

The Ritz vector produced is the projection `w` of `P_K u` onto the `θ`-eigenspace of the
compression, for which `P_{𝕜 ∙ w} u = w`, so that `‖u - w‖ ^ 2` splits by Pythagoras into
`‖u - P_K u‖ ^ 2`, the part `K` misses, and `‖P_K u - w‖ ^ 2`, which the residual bound and the
separation bound together control by `(γ / δ) ‖u - P_K u‖`.  Where that projection vanishes the
inequality is vacuous — its right-hand side is then at least `1` — and any Ritz vector for `θ`
serves, which is why the statement is an existence and why `θ` is assumed to be a Ritz value. -/
theorem sin_angle_ritzVector_le {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {K : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 K] {γ δ θ lam : ℝ} (hδ0 : 0 < δ)
    (hγ : ∀ x ∈ Kᗮ, ‖K.starProjection (A x)‖ ≤ γ * ‖x‖)
    (hθ : Module.End.HasEigenvalue (compression A K) (θ : 𝕜))
    (hδ : ∀ z ∈ (Module.End.eigenspace (compression A K) (θ : 𝕜))ᗮ,
      δ * ‖z‖ ≤ ‖compression A K z - (lam : 𝕜) • z‖)
    {u : E} (hu : A u = (lam : 𝕜) • u) (hu0 : u ≠ 0) :
    ∃ w : E, IsRitzPair A K (θ : 𝕜) w ∧
      (𝕜 ∙ w).sinAngle u ≤ Real.sqrt (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u := by
  have hupos : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hR : (0 : ℝ) ≤ 1 + γ ^ 2 / δ ^ 2 := by positivity
  have hres : ‖compression A K (K.orthogonalProjectionOnto u)
      - (lam : 𝕜) • K.orthogonalProjectionOnto u‖ ≤ γ * ‖u - K.starProjection u‖ := by
    have h := compression_residual_le hγ hu
    have hcast : (compression A K (K.orthogonalProjectionOnto u) : E)
        - (lam : 𝕜) • ((K.orthogonalProjectionOnto u : K) : E)
        = ((compression A K (K.orthogonalProjectionOnto u)
          - (lam : 𝕜) • K.orthogonalProjectionOnto u : K) : E) := rfl
    rw [hcast, Submodule.norm_coe] at h
    exact h
  have haux := (compression.isSymmetric A K hA).mul_norm_sub_starProjection_le
    (W := Module.End.eigenspace (compression A K) (θ : 𝕜)) (θ := θ) (lam := lam) (δ := δ)
    (fun _q hq => Module.End.mem_eigenspace_iff.1 hq) hδ (K.orthogonalProjectionOnto u)
  set W := Module.End.eigenspace (compression A K) (θ : 𝕜) with hWdef
  set y : K := K.orthogonalProjectionOnto u with hydef
  set p : K := W.starProjection y with hpdef
  have hkey : δ * ‖y - p‖ ≤ γ * ‖u - K.starProjection u‖ := haux.trans hres
  have hsqkey : ‖y - p‖ ^ 2 * δ ^ 2 ≤ γ ^ 2 * ‖u - K.starProjection u‖ ^ 2 := by
    nlinarith [hkey, mul_nonneg hδ0.le (norm_nonneg (y - p)), norm_nonneg (y - p),
      norm_nonneg (u - K.starProjection u)]
  have hsin : K.sinAngle u * ‖u‖ = ‖u - K.starProjection u‖ := K.sinAngle_mul_norm u
  have hcoe : ‖y - p‖ = ‖K.starProjection u - (p : E)‖ := by
    rw [← Submodule.norm_coe (y - p)]
    rfl
  have hdiv : ‖K.starProjection u - (p : E)‖ ^ 2
      ≤ γ ^ 2 / δ ^ 2 * ‖u - K.starProjection u‖ ^ 2 := by
    rw [← hcoe, div_mul_eq_mul_div, le_div_iff₀ hδ2]
    exact hsqkey
  have hnn : 0 ≤ Real.sqrt (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u :=
    mul_nonneg (Real.sqrt_nonneg _) (Submodule.sinAngle_nonneg K u)
  have hprod : (Real.sqrt (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u) ^ 2
      = (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hR]
  rcases eq_or_ne p 0 with hp0 | hp0
  · obtain ⟨q, hq⟩ := hθ.exists_hasEigenvector
    refine ⟨(q : E), isRitzPair_of_hasEigenvector A K (θ : 𝕜) hq,
      (Submodule.sinAngle_le_one _ _).trans ?_⟩
    have hpy : ‖K.starProjection u‖ ^ 2 + ‖u - K.starProjection u‖ ^ 2 = ‖u‖ ^ 2 :=
      K.norm_starProjection_sq_add_norm_sub_sq u
    have h0 : ‖K.starProjection u - (p : E)‖ = ‖K.starProjection u‖ := by
      rw [hp0]
      simp
    have h1 : (1 : ℝ) ≤ (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u ^ 2 := by
      have e2 : K.sinAngle u ^ 2 * ‖u‖ ^ 2 = ‖u - K.starProjection u‖ ^ 2 := by
        rw [← mul_pow, hsin]
      rw [h0] at hdiv
      nlinarith [hdiv, hpy, e2, hupos]
    have hstep := Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ (Real.sqrt (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u) ^ 2 by
        rw [hprod]; exact h1)
    rwa [Real.sqrt_one, Real.sqrt_sq hnn] at hstep
  · have hpW : p ∈ W := W.starProjection_apply_mem y
    refine ⟨(p : E), isRitzPair_of_hasEigenvector A K (θ : 𝕜) ⟨hpW, hp0⟩, ?_⟩
    have hyE : ((y : K) : E) = K.starProjection u := rfl
    have hyperp : y - p ∈ Wᗮ := W.sub_starProjection_mem_orthogonal y
    have hpy : inner 𝕜 p y = inner 𝕜 p p := by
      have h := Submodule.inner_right_of_mem_orthogonal hpW hyperp
      rw [inner_sub_right, sub_eq_zero] at h
      exact h
    have hinner : inner 𝕜 ((p : K) : E) u = inner 𝕜 ((p : K) : E) ((p : K) : E) := by
      have h := Submodule.inner_right_of_mem_orthogonal p.2 (K.sub_starProjection_mem_orthogonal u)
      rw [inner_sub_right, sub_eq_zero] at h
      rw [h, ← hyE]
      simp only [← Submodule.coe_inner]
      exact hpy
    have hproj : (𝕜 ∙ ((p : K) : E)).starProjection u = ((p : K) : E) :=
      Submodule.starProjection_span_singleton_eq_self hinner
    have hnormeq : (𝕜 ∙ ((p : K) : E)).sinAngle u * ‖u‖ = ‖u - ((p : K) : E)‖ := by
      rw [Submodule.sinAngle_mul_norm, hproj]
    have hpyth : ‖u - ((p : K) : E)‖ ^ 2
        = ‖u - K.starProjection u‖ ^ 2 + ‖K.starProjection u - ((p : K) : E)‖ ^ 2 :=
      K.norm_sub_sq_eq_add_of_mem u p.2
    have hsqle : (𝕜 ∙ ((p : K) : E)).sinAngle u ^ 2
        ≤ (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u ^ 2 := by
      have e1 : (𝕜 ∙ ((p : K) : E)).sinAngle u ^ 2 * ‖u‖ ^ 2 = ‖u - ((p : K) : E)‖ ^ 2 := by
        rw [← mul_pow, hnormeq]
      have e2 : K.sinAngle u ^ 2 * ‖u‖ ^ 2 = ‖u - K.starProjection u‖ ^ 2 := by
        rw [← mul_pow, hsin]
      nlinarith [hdiv, e1, e2, hupos, hpyth]
    have hb : (𝕜 ∙ ((p : K) : E)).sinAngle u ^ 2
        ≤ (Real.sqrt (1 + γ ^ 2 / δ ^ 2) * K.sinAngle u) ^ 2 := by
      rw [hprod]
      exact hsqle
    have hstep := Real.sqrt_le_sqrt hb
    rwa [Real.sqrt_sq (Submodule.sinAngle_nonneg _ _), Real.sqrt_sq hnn] at hstep

/-- The reverse bound: a Ritz pair `(θ, w)` of a symmetric `A` and an eigenpair `(lam, u)`
satisfy `|θ - lam| ≤ C sin²θ(u, w)`, with `C` bounding the quadratic form of `A - lam`.  So the
Ritz value is accurate to second order in the angle between the Ritz vector and the eigenvector,
which is why a Rayleigh–Ritz eigenvalue is much better than its eigenvector.

The proof is the same trick as `abs_sub_rayleighQuotient_starProjection_le`: since `(A - lam) u`
vanishes and `A - lam` is symmetric, the quadratic form of `A - lam` is unchanged by subtracting
any multiple of `u`, so `(θ - lam) ‖w‖ ^ 2` may be evaluated at `w - P_{𝕜 ∙ u} w`, whose norm is
`sin θ(u, w) ‖w‖`.

Chained with `sin_angle_ritzVector_le` this bounds `|θ - lam|` by
`C (1 + γ² / δ²) sin²θ(u, K)`. -/
theorem abs_ritz_value_sub_le {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {lam C : ℝ}
    (hC : ∀ x : E, |RCLike.re (inner 𝕜 (A x) x) - lam * ‖x‖ ^ 2| ≤ C * ‖x‖ ^ 2)
    {u w : E} (hu : A u = (lam : 𝕜) • u) (hu0 : u ≠ 0) {θ : ℝ}
    (h : IsRitzPair A K (θ : 𝕜) w) :
    |θ - lam| ≤ C * (𝕜 ∙ w).sinAngle u ^ 2 := by
  have hw0 : w ≠ 0 := h.ne_zero
  have hwpos : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
  rw [← Submodule.sinAngle_span_singleton_comm hu0 hw0]
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, c • u = (𝕜 ∙ u).starProjection w :=
    Submodule.mem_span_singleton.1 ((𝕜 ∙ u).starProjection_apply_mem w)
  have hxnorm : ‖w - (𝕜 ∙ u).starProjection w‖ = (𝕜 ∙ u).sinAngle w * ‖w‖ :=
    ((𝕜 ∙ u).sinAngle_mul_norm w).symm
  have hQ : RCLike.re (inner 𝕜 (A (w - (𝕜 ∙ u).starProjection w)) (w - (𝕜 ∙ u).starProjection w))
      - lam * ‖w - (𝕜 ∙ u).starProjection w‖ ^ 2
      = RCLike.re (inner 𝕜 (A w) w) - lam * ‖w‖ ^ 2 := by
    rw [← re_inner_sub A lam (w - (𝕜 ∙ u).starProjection w), ← re_inner_sub A lam w, ← hc,
      show w - c • u = w + (-c) • u by module, inner_shift_add hA hu w (-c)]
  have hQw : RCLike.re (inner 𝕜 (A w) w) - lam * ‖w‖ ^ 2 = (θ - lam) * ‖w‖ ^ 2 := by
    rw [h.re_inner_apply_self, RCLike.ofReal_re]
    ring
  have hbound := hC (w - (𝕜 ∙ u).starProjection w)
  rw [hQ, hQw, abs_mul, abs_of_pos hwpos, hxnorm, mul_pow] at hbound
  refine le_of_mul_le_mul_right ?_ hwpos
  calc |θ - lam| * ‖w‖ ^ 2 ≤ C * ((𝕜 ∙ u).sinAngle w ^ 2 * ‖w‖ ^ 2) := hbound
    _ = C * (𝕜 ∙ u).sinAngle w ^ 2 * ‖w‖ ^ 2 := by ring

end LinearMap.IsSymmetric

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
