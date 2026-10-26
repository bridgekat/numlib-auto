import Numlib.Analysis.InnerProductSpace.Projection.Compression
import Numlib.Krylov.Lanczos
import Numlib.Krylov.Monotonicity
import Numlib.Optimization.Subproblem.Multiplier

/-!
# Subproblems restricted to Krylov subspaces

Let `H` be a symmetric operator on a finite-dimensional real inner product space `E` and `g : E`.
Krylov methods for the trust-region and regularization subproblems ([cartis2022evaluation]
§10.1–10.3; the GLTR/GLRT methods of Gould–Lucidi–Roma–Toint and Cartis–Gould–Toint) replace
the subproblem by its restriction to the Krylov subspaces `𝒦_k = 𝒦_k(H, g)` ((10.1.1)). This file
develops the structure of the restricted problems.

**Restriction.** A problem restricted to a subspace `K` is the unrestricted problem for the
compressed data `(P_K g, P_K H|_K)` on the inner product space `K`
(`isMinOn_subspace_iff_compression`, `isMinOn_regModel_subspace_iff_compression`), so the whole
theory of the full subproblems (optimality conditions, multipliers, secular equation) applies to
the restricted ones. The first-order condition of a restricted problem says that the gradient
`g + H s + λ s` is orthogonal to `K` (`galerkin_of_isMinOn_regModel_subspace`,
`IsTrustRegionMultiplier.galerkin_of_compressionL`).

**No hard case.** `g` is a cyclic vector of the compression of `H` to `𝒦_k`
(`Krylov.subspace_compression_eq_top`), so no eigenvector of the compression is orthogonal to `g`
(`Krylov.inner_ne_zero_of_compression_eigen`) and the restricted multipliers are strictly to the
right of the least Ritz value (`krylov_no_hardCase`): the hard case of §8.3 never occurs in a
Krylov subspace (§10.2.1, citing Gould–Lucidi–Roma–Toint, Thms 5.3 and 5.5).

**Monotonicity.** Restricted solutions on nested Krylov subspaces grow in norm and multiplier
(Lemmas 10.2.1 and 10.3.1: `krylov_multiplier_mono_regularization`,
`krylov_multiplier_mono_trustRegion`). The proof combines the secular characterization of the
multiplier (`le_secular_iff_of_regularization`, `le_secular_iff_of_trustRegion`) with Steihaug's
theorem that Galerkin (CG) iterates of a positive semidefinite consistent system grow in norm up
to the minimum-norm solution (`Krylov.IsGalerkinIterate.norm_le_of_isPositive`); comparing `𝒦_k`
with `𝒦_ℓ` is the same argument inside the space `𝒦_ℓ` (`galerkin_compressionL_of_le`).

**Lanczos coordinates.** In the Lanczos basis `qⱼ = Arnoldi.vec H g j` of `𝒦_{m+1}` the
compression is the tridiagonal `T_{m+1} = Lanczos.tridiag H g (m + 1)` and the gradient is
`‖g‖ e₀`; the Lanczos relation gives the residual identity (B.10.1)
(`krylov_lanczos_coordinates`).

## Main definitions

* `Subproblem.compressionL H K`: the compression `P_K H|_K` as a continuous linear map on `K`.

## Main statements

* `Subproblem.isMinOn_subspace_iff_compression`,
  `Subproblem.isMinOn_regModel_subspace_iff_compression`: the restriction principle.
* `Subproblem.krylov_no_hardCase`: no hard case on Krylov subspaces.
* `Subproblem.krylov_multiplier_mono_regularization`: Lemma 10.2.1.
* `Subproblem.krylov_multiplier_mono_trustRegion`: Lemma 10.3.1.
* `Subproblem.krylov_lanczos_coordinates`: (10.1.3)–(10.1.6), (10.2.1), (B.10.1).
* `Krylov.IsGalerkinIterate.norm_le_of_isPositive`: Galerkin iterates of a positive semidefinite
  system `A x = b` are no longer than any solution.

## Implementation notes

The scaling norm `‖·‖_M` of the book is the norm of `E` (see
`Numlib.Optimization.Subproblem.Matrix`), and the Krylov subspaces `𝒦(M⁻¹ H, M⁻¹ g)` are those of
the operator `M⁻¹ H`, symmetric in the `M`-inner product. Lanczos indices are `0`-based: the
book's `q_{j+1}`, `γ_{j+1}` are `Arnoldi.vec H g j`, `Lanczos.beta H g (j - 1)`, and its `γ₁`
is `‖g‖`. The book states the monotonicity lemmas for `1 ≤ k ≤ ℓ ≤ grade(H, g)`; the bound
`ℓ ≤ grade` is not needed.
-/

open Set Metric Krylov
open scoped RealInnerProductSpace

namespace Subproblem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Restriction to a subspace -/

section Compression

variable (H : E →L[ℝ] E) (K : Submodule ℝ E)

/-- The compression `P_K H|_K : K →L[ℝ] K` of `H` to the subspace `K`, as a continuous linear map
(`compression` is its underlying linear map). -/
noncomputable def compressionL : K →L[ℝ] K :=
  LinearMap.toContinuousLinearMap (compression (H : E →ₗ[ℝ] E) K)

/-- The underlying linear map of `compressionL H K` is `compression H K`. -/
@[simp]
theorem coe_compressionL : ((compressionL H K : K →L[ℝ] K) : K →ₗ[ℝ] K) =
    compression (H : E →ₗ[ℝ] E) K := rfl

variable {H K}

/-- The compression carries the bilinear form of `H`: `⟪P_K H x, y⟫ = ⟪H x, y⟫` for `x, y ∈ K`. -/
theorem inner_compressionL_left (x y : K) : ⟪compressionL H K x, y⟫ = ⟪H x, (y : E)⟫ :=
  compression.inner_apply (H : E →ₗ[ℝ] E) K x y

/-- The compression carries the bilinear form of `H`: `⟪x, P_K H y⟫ = ⟪x, H y⟫` for `x, y ∈ K`. -/
theorem inner_compressionL_right (x y : K) : ⟪x, compressionL H K y⟫ = ⟪(x : E), H y⟫ :=
  compression.inner_apply' (H : E →ₗ[ℝ] E) K x y

/-- The compression of a symmetric operator is symmetric. -/
theorem isSymmetric_compressionL (hH : (H : E →ₗ[ℝ] E).IsSymmetric) :
    ((compressionL H K : K →L[ℝ] K) : K →ₗ[ℝ] K).IsSymmetric :=
  compression.isSymmetric _ K hH

/-- The projected gradient against a vector of `K`: `⟪P_K g, y⟫ = ⟪g, y⟫`. -/
theorem inner_orthogonalProjectionOnto_left (g : E) (y : K) :
    ⟪K.orthogonalProjectionOnto g, y⟫ = ⟪g, (y : E)⟫ := by
  rw [Submodule.coe_inner, Submodule.coe_orthogonalProjectionOnto_apply,
    K.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.2 y.2]

/-- The model of the compressed data is the model of `H` on `K`. -/
theorem quadModel_compressionL (g : E) (y : K) :
    quadModel (K.orthogonalProjectionOnto g) (compressionL H K) y = quadModel g H y := by
  rw [quadModel, quadModel, inner_orthogonalProjectionOnto_left, inner_compressionL_right]

/-- The regularized model of the compressed data is the regularized model on `K`. -/
theorem regModel_compressionL (g : E) (σ r : ℝ) (y : K) :
    regModel (K.orthogonalProjectionOnto g) (compressionL H K) σ r y = regModel g H σ r y := by
  rw [regModel, regModel, quadModel_compressionL, Submodule.norm_coe]

/-- **Restriction principle for the trust-region subproblem.** A point `s ∈ K` minimizes the
model over `K ∩ {‖s‖ ≤ Δ}` iff it minimizes the model of the compressed data
`(P_K g, P_K H|_K)` over the ball of `K`. -/
theorem isMinOn_subspace_iff_compression {g : E} {Δ : ℝ} {s : E} (hs : s ∈ K) :
    IsMinOn (quadModel g H) ((K : Set E) ∩ closedBall 0 Δ) s ↔
      IsMinOn (quadModel (K.orthogonalProjectionOnto g) (compressionL H K)) (closedBall 0 Δ)
        (⟨s, hs⟩ : K) := by
  simp only [isMinOn_iff, mem_inter_iff, mem_closedBall_zero_iff, SetLike.mem_coe,
    quadModel_compressionL]
  exact ⟨fun h y hy => h y ⟨y.2, hy⟩, fun h x ⟨hx, hxΔ⟩ => h ⟨x, hx⟩ hxΔ⟩

/-- **Restriction principle for the regularization subproblem.** A point `s ∈ K` minimizes the
regularized model over `K` iff it globally minimizes the regularized model of the compressed data
`(P_K g, P_K H|_K)` on `K`. -/
theorem isMinOn_regModel_subspace_iff_compression {g : E} {σ r : ℝ} {s : E} (hs : s ∈ K) :
    IsMinOn (regModel g H σ r) (K : Set E) s ↔
      IsMinOn (regModel (K.orthogonalProjectionOnto g) (compressionL H K) σ r) univ
        (⟨s, hs⟩ : K) := by
  simp only [isMinOn_iff, mem_univ, SetLike.mem_coe, regModel_compressionL, true_imp_iff]
  exact ⟨fun h y => h y y.2, fun h x hx => h ⟨x, hx⟩⟩

/-- The gradient of the shifted compressed model against a vector of `K` is the gradient of the
shifted model of `H`: `⟪P_K g + P_K H s + μ s, v⟫ = ⟪g + H s + μ s, v⟫` for `s, v ∈ K`. -/
theorem inner_orthogonalProjectionOnto_add_compressionL {g : E} {μ : ℝ} {s : E} (hs : s ∈ K)
    (v : K) :
    ⟪K.orthogonalProjectionOnto g + compressionL H K ⟨s, hs⟩ + μ • (⟨s, hs⟩ : K), v⟫ =
      ⟪g + H s + μ • s, (v : E)⟫ := by
  simp only [inner_add_left, inner_smul_left, inner_compressionL_left,
    inner_orthogonalProjectionOnto_left]
  rw [Submodule.coe_inner]

/-- The shifted system of the compressed data is the Galerkin condition on `K`:
`(P_K H|_K + μ) s = -P_K g` iff `g + H s + μ s ⟂ K`. -/
theorem compressionL_shifted_iff {g : E} {μ : ℝ} {s : E} (hs : s ∈ K) :
    (compressionL H K + μ • (1 : K →L[ℝ] K)) ⟨s, hs⟩ = -K.orthogonalProjectionOnto g ↔
      ∀ v ∈ K, ⟪g + H s + μ • s, v⟫ = 0 := by
  have key : ∀ v : K, ⟪(compressionL H K + μ • (1 : K →L[ℝ] K)) ⟨s, hs⟩ +
      K.orthogonalProjectionOnto g, v⟫ = ⟪g + H s + μ • s, (v : E)⟫ := fun v => by
    rw [add_comm]
    simp only [add_apply, smul_apply, one_apply_eq_self, ← add_assoc]
    exact inner_orthogonalProjectionOnto_add_compressionL hs v
  rw [← add_eq_zero_iff_eq_neg]
  refine ⟨fun h v hv => by rw [← key ⟨v, hv⟩, h, inner_zero_left], fun h => ?_⟩
  exact inner_self_eq_zero.1 ((key _).trans (h _ (Submodule.coe_mem _)))

variable {g : E} {σ r Δ μ : ℝ} {s : E}

/-- **First-order conditions on a subspace, regularization.** If `s ∈ K` minimizes the regularized
model over `K` (`σ > 0`, `r > 2`, `H` symmetric) and `λ = σ ‖s‖^{r-2}`, then the gradient
`g + H s + λ s` is orthogonal to `K` and the compressed `P_K H|_K + λ` is positive
semidefinite. -/
theorem galerkin_of_isMinOn_regModel_subspace (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hσ : 0 < σ)
    (hr : 2 < r) (hs : s ∈ K) (hmin : IsMinOn (regModel g H σ r) (K : Set E) s) :
    (∀ v ∈ K, ⟪g + H s + (σ * ‖s‖ ^ (r - 2)) • s, v⟫ = 0) ∧
      ((compressionL H K + (σ * ‖s‖ ^ (r - 2)) • (1 : K →L[ℝ] K) : K →L[ℝ] K) :
        K →ₗ[ℝ] K).IsPositive := by
  obtain ⟨hshift, hpos⟩ := (isMinOn_regModel_iff (isSymmetric_compressionL hH) hσ hr).1
    ((isMinOn_regModel_subspace_iff_compression hs).1 hmin)
  have hn : ‖(⟨s, hs⟩ : K)‖ = ‖s‖ := rfl
  rw [hn] at hshift hpos
  exact ⟨(compressionL_shifted_iff hs).1 hshift, hpos⟩

/-- **First-order conditions on a subspace, trust region.** If `μ` is a trust-region multiplier of
`s ∈ K` for the compressed data `(P_K g, P_K H|_K)`, then the gradient `g + H s + μ s` is
orthogonal to `K`. -/
theorem IsTrustRegionMultiplier.galerkin_of_compressionL (hs : s ∈ K)
    (h : IsTrustRegionMultiplier (K.orthogonalProjectionOnto g) (compressionL H K) Δ ⟨s, hs⟩ μ) :
    ∀ v ∈ K, ⟪g + H s + μ • s, v⟫ = 0 :=
  (compressionL_shifted_iff hs).1 h.shifted

end Compression

/-! ### Krylov subspaces of a compression -/

section KrylovCompression

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  (A : F →ₗ[𝕜] F) {b : F} {m : ℕ} [(Krylov.subspace A b m).HasOrthogonalProjection]

/-- On `W = 𝒦_m(A, b)`, the powers of the compression applied to `b` are the powers of `A` applied
to `b`, up to `A^{m-1} b`. -/
theorem _root_.Krylov.coe_compression_pow_apply (hb : b ∈ Krylov.subspace A b m) {i : ℕ}
    (hi : i < m) :
    (((compression A (Krylov.subspace A b m)) ^ i) ⟨b, hb⟩ : F) = (A ^ i) b := by
  have h := compression.aeval_apply_of_forall_pow_mem A (Krylov.subspace A b m)
    (Polynomial.X ^ i) (x := ⟨b, hb⟩) fun j hj =>
      Krylov.pow_apply_mem_subspace A b
        ((hj.trans_eq (Polynomial.natDegree_X_pow i)).trans_lt hi)
  simpa [Polynomial.aeval_X_pow] using h

/-- **Krylov subspaces of the compression to a Krylov subspace.** For `k ≤ m`, the `k`-th Krylov
subspace of `b` for the compression of `A` to `W = 𝒦_m(A, b)` is `𝒦_k(A, b)`, seen in `W`. -/
theorem _root_.Krylov.map_subspace_compression (hb : b ∈ Krylov.subspace A b m) {k : ℕ}
    (hk : k ≤ m) :
    (Krylov.subspace (compression A (Krylov.subspace A b m)) ⟨b, hb⟩ k).map
      (Krylov.subspace A b m).subtype = Krylov.subspace A b k := by
  rw [Krylov.subspace_eq_span_image_Iio (compression A _) _ k, Submodule.map_span,
    Krylov.subspace_eq_span_image_Iio A b k, Set.image_image]
  refine congrArg _ (Set.image_congr fun i hi => ?_)
  exact coe_compression_pow_apply A hb ((Set.mem_Iio.1 hi).trans_le hk)

/-- Membership form of `map_subspace_compression`. -/
theorem _root_.Krylov.mem_subspace_compression_iff (hb : b ∈ Krylov.subspace A b m) {k : ℕ}
    (hk : k ≤ m) (x : Krylov.subspace A b m) :
    x ∈ Krylov.subspace (compression A (Krylov.subspace A b m)) ⟨b, hb⟩ k ↔
      (x : F) ∈ Krylov.subspace A b k := by
  rw [← map_subspace_compression A hb hk, Submodule.mem_map]
  refine ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => ?_⟩
  rwa [← Subtype.ext hyx]

/-- **`b` is a cyclic vector of the compression to `𝒦_m(A, b)`**: its Krylov space for the
compression is the whole of `𝒦_m(A, b)`. -/
theorem _root_.Krylov.subspace_compression_eq_top (hb : b ∈ Krylov.subspace A b m) :
    Krylov.subspace (compression A (Krylov.subspace A b m)) ⟨b, hb⟩ m = ⊤ :=
  eq_top_iff.2 fun x _ => (mem_subspace_compression_iff A hb le_rfl x).2 x.2

/-- **No eigenvector of the compression to a Krylov subspace is orthogonal to the starting
vector.** If `A` is symmetric and `v ∈ 𝒦_m(A, b)` is an eigenvector of the compression, then
`⟪v, b⟫ ≠ 0`: `b` is cyclic, and an eigenvector orthogonal to `b` is orthogonal to all the
`P A|^i b = A^i b`. In the Lanczos basis this is the classical fact that the eigenvectors of an
unreduced symmetric tridiagonal matrix have a nonzero first component. -/
theorem _root_.Krylov.inner_ne_zero_of_compression_eigen (hA : A.IsSymmetric)
    (hb : b ∈ Krylov.subspace A b m)
    {v : Krylov.subspace A b m} {θ : 𝕜} (hv : compression A (Krylov.subspace A b m) v = θ • v)
    (hv0 : v ≠ 0) : inner 𝕜 (v : F) b ≠ 0 := by
  intro h0
  set C := compression A (Krylov.subspace A b m)
  have hC : C.IsSymmetric := compression.isSymmetric A _ hA
  have hpow : ∀ i : ℕ, (C ^ i) v = θ ^ i • v := fun i => by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, ← pow_succ]
  have hsub : Krylov.subspace C ⟨b, hb⟩ m ≤ (𝕜 ∙ v)ᗮ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
      ← (hC.pow (i : ℕ)) v, hpow, inner_smul_left, Submodule.coe_inner]
    simp [h0]
  rw [subspace_compression_eq_top A hb] at hsub
  have hvv := hsub (Submodule.mem_top (x := v))
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hvv
  exact hv0 hvv

end KrylovCompression

/-! ### The hard case and the Galerkin comparison, on an abstract space -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {T : F →L[ℝ] F}

/-- **No hard case.** If `h` is not orthogonal to any eigenvector of `T` for its least eigenvalue
`λ₁`, then every `μ` with `T + μ ⪰ 0` and `(T + μ) s = -h` satisfies `μ > -λ₁`: at `μ = -λ₁` an
eigenvector `v` would give `⟪v, h⟫ = -⟪(T + μ) v, s⟫ = 0`. -/
theorem neg_leftmost_lt_of_shifted [Nontrivial F] (hT : (T : F →ₗ[ℝ] F).IsSymmetric) {h s : F}
    {μ : ℝ} (hcyc : ∀ v : F, T v = leftmost hT • v → v ≠ 0 → ⟪v, h⟫ ≠ 0)
    (hpos : ((T + μ • 1 : F →L[ℝ] F) : F →ₗ[ℝ] F).IsPositive)
    (hs : (T + μ • (1 : F →L[ℝ] F)) s = -h) : -leftmost hT < μ := by
  refine lt_of_le_of_ne ((isPositive_add_smul_iff (hH := hT) μ).1 hpos) fun heq => ?_
  obtain ⟨v, hv⟩ := (hasEigenvalue_leftmost (hH := hT)).exists_hasEigenvector
  have hTv : T v = leftmost hT • v := by
    simpa using Module.End.mem_eigenspace_iff.1 hv.1
  have hker : (T + μ • (1 : F →L[ℝ] F)) v = 0 := by
    rw [add_apply, hTv, smul_apply, one_apply_eq_self, ← heq, ← add_smul, add_neg_cancel,
      zero_smul]
  refine hcyc v hTv hv.2 ?_
  have hsym := ContinuousLinearMap.isSymmetric_add_smul_one hT μ v s
  simp only [ContinuousLinearMap.coe_coe] at hsym
  rw [← neg_neg h, ← hs, inner_neg_right, ← hsym, hker, inner_zero_left, neg_zero]

/-- **Steihaug's monotonicity for semidefinite consistent systems.** Let `A` be positive
semidefinite and `A z = b`. Then every Galerkin iterate `x` of `A x = b` on a Krylov subspace
`𝒦_k(A, b)` (from `x₀ = 0`) is no longer than `z`: `‖x‖ ≤ ‖z‖`.

On `W = (ker A)ᗮ`, which is `A`-invariant and contains `b`, `A` is positive definite, so the
Galerkin iterates are the CG iterates of the restricted system, whose norms increase
(`Krylov.IsGalerkinIterate.norm_monotone`) up to the exact solution `y ∈ W` reached at the grade;
and `y` is the minimum-norm solution of `A y = b`. -/
theorem _root_.Krylov.IsGalerkinIterate.norm_le_of_isPositive {A : F →ₗ[ℝ] F} (hA : A.IsPositive)
    {b z x : F} {k : ℕ} (hx : IsGalerkinIterate A b 0 k x) (hz : A z = b) : ‖x‖ ≤ ‖z‖ := by
  set W := (LinearMap.ker A)ᗮ with hWdef
  have hWinv : ∀ u ∈ W, A u ∈ W := fun u hu => by
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro v hv
    rw [← hA.isSymmetric v u, LinearMap.mem_ker.1 hv, inner_zero_left]
  have hbW : b ∈ W := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [← hz, ← hA.isSymmetric v z, LinearMap.mem_ker.1 hv, inner_zero_left]
  set A' : W →ₗ[ℝ] W := A.restrict hWinv with hA'def
  have hA'apply : ∀ w : W, (A' w : F) = A w := fun w => rfl
  have hA' : A'.IsSymmetricCoercive := by
    refine ⟨fun u v => ?_, (LinearMap.isCoercive_iff_forall_pos A').2 fun w hw => ?_⟩
    · rw [Submodule.coe_inner, Submodule.coe_inner, hA'apply, hA'apply, hA.isSymmetric]
    · rw [RCLike.re_to_real, Submodule.coe_inner, hA'apply]
      refine lt_of_le_of_ne (hA.inner_nonneg_left _) fun h0 => hw ?_
      have hAw := hA.apply_eq_zero_of_inner_eq_zero h0.symm
      have hwW : (w : F) ∈ (LinearMap.ker A)ᗮ := w.2
      rw [Submodule.mem_orthogonal] at hwW
      exact Subtype.ext (inner_self_eq_zero.1 (hwW _ (LinearMap.mem_ker.2 hAw)))
  set b' : W := ⟨b, hbW⟩
  have hsemi : Function.Semiconj W.subtype A' A := fun w => rfl
  have hmap : ∀ j, (Krylov.subspace A' b' j).map W.subtype = Krylov.subspace A b j :=
    fun j => Krylov.map_subspace_of_semiconj hsemi b' j
  have hmem : ∀ j (w : W), w ∈ Krylov.subspace A' b' j ↔ (w : F) ∈ Krylov.subspace A b j := by
    intro j w
    rw [← hmap j, Submodule.mem_map]
    refine ⟨fun hw => ⟨w, hw, rfl⟩, fun ⟨y, hy, hyw⟩ => ?_⟩
    rwa [← Subtype.ext hyw]
  have hxK : x ∈ Krylov.subspace A b k := by simpa using hx.mem
  obtain ⟨x', hx'K, hx'x⟩ := (Submodule.mem_map.1 ((hmap k).symm ▸ hxK))
  have hx'x : (x' : F) = x := hx'x
  have hgal' : IsGalerkinIterate A' b' 0 k x' := by
    refine ⟨by simpa using hx'K, ?_⟩
    simp only [map_zero, sub_zero]
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hv' : (v : F) ∈ Krylov.subspace A b k := (hmem k v).1 hv
    have horth := hx.orth
    simp only [map_zero, sub_zero, Submodule.mem_orthogonal] at horth
    rw [Submodule.coe_inner, Submodule.coe_sub, hA'apply, hx'x]
    exact horth _ hv'
  have hex : ∀ j, ∃! y, IsGalerkinIterate A' b' 0 j y := fun j =>
    existsUnique_isGalerkinIterate_of_isCoercive hA'.isCoercive b' 0 j
  choose xs hxs using fun j => (hex j).exists
  have hxsk : xs k = x' := (hex k).unique (hxs k) hgal'
  set N := max k (Krylov.grade A' (b' - A' 0))
  have hy : A' (xs N) = b' := (hxs N).apply_eq_of_grade_le (le_max_right _ _)
  have hle : ‖xs k‖ ≤ ‖xs N‖ :=
    Krylov.IsGalerkinIterate.norm_monotone hA' hxs (le_max_left _ _)
  set y : F := (xs N : F)
  have hAy : A y = b := congrArg Subtype.val hy
  have hyW : y ∈ W := (xs N).2
  have hzy : z - y ∈ LinearMap.ker A := by rw [LinearMap.mem_ker, map_sub, hz, hAy, sub_self]
  have horth : ⟪y, z - y⟫ = 0 := by
    rw [hWdef, Submodule.mem_orthogonal] at hyW
    rw [real_inner_comm]; exact hyW _ hzy
  have hyz : ‖y‖ ≤ ‖z‖ := by
    have h2 : ‖z‖ * ‖z‖ = ‖y‖ * ‖y‖ + ‖z - y‖ * ‖z - y‖ := by
      have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y (z - y) horth
      rwa [add_sub_cancel] at this
    nlinarith [norm_nonneg y, norm_nonneg z, mul_self_nonneg ‖z - y‖]
  calc ‖x‖ = ‖xs k‖ := by rw [hxsk, ← hx'x]; rfl
    _ ≤ ‖y‖ := hle
    _ ≤ ‖z‖ := hyz

omit [FiniteDimensional ℝ F] in
/-- The Krylov subspaces of `T + μ` from `-h` are those of `T` from `h`. -/
theorem subspace_add_smul_neg (T : F →L[ℝ] F) (μ : ℝ) (h : F) (k : ℕ) :
    Krylov.subspace ((T + μ • 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) (-h) k =
      Krylov.subspace (T : F →ₗ[ℝ] F) h k := by
  have hT : ((T + μ • 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) =
      (T : F →ₗ[ℝ] F) + algebraMap ℝ (Module.End ℝ F) μ := by
    ext x; simp [Module.algebraMap_end_apply]
  rw [hT, Krylov.subspace_add_algebraMap, ← neg_one_smul ℝ h,
    Krylov.subspace_smul_of_ne_zero _ _ (by norm_num : (-1 : ℝ) ≠ 0)]

omit [FiniteDimensional ℝ F] in
/-- A point `s ∈ 𝒦_k(T, h)` with `h + T s + μ s ⟂ 𝒦_k(T, h)` is the `k`-th Galerkin iterate of
`(T + μ) x = -h` from `x₀ = 0`. -/
theorem isGalerkinIterate_of_inner_eq_zero {h s : F} {μ : ℝ} {k : ℕ}
    (hs : s ∈ Krylov.subspace (T : F →ₗ[ℝ] F) h k)
    (hgal : ∀ v ∈ Krylov.subspace (T : F →ₗ[ℝ] F) h k, ⟪h + T s + μ • s, v⟫ = 0) :
    IsGalerkinIterate ((T + μ • 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) (-h) 0 k s := by
  simp only [IsGalerkinIterate, map_zero, sub_zero, subspace_add_smul_neg]
  refine ⟨by rwa [sub_zero], (Submodule.mem_orthogonal _ _).2 fun v hv => ?_⟩
  have h0 := hgal v hv
  rw [real_inner_comm] at h0
  have e : -h - ((T + μ • 1 : F →L[ℝ] F) : F →ₗ[ℝ] F) s = -(h + T s + μ • s) := by
    simp only [ContinuousLinearMap.coe_coe, add_apply, smul_apply, one_apply_eq_self]; abel
  rw [e, inner_neg_right, h0, neg_zero]

/-- **Galerkin points are shorter than shifted solutions.** If `T + μ ⪰ 0`, `(T + μ) z = -h`,
and `s ∈ 𝒦_k(T, h)` satisfies `h + T s + μ s ⟂ 𝒦_k(T, h)`, then `‖s‖ ≤ ‖z‖`. -/
theorem norm_le_of_inner_eq_zero {h s z : F} {μ : ℝ} {k : ℕ}
    (hpos : ((T + μ • 1 : F →L[ℝ] F) : F →ₗ[ℝ] F).IsPositive)
    (hz : (T + μ • (1 : F →L[ℝ] F)) z = -h) (hs : s ∈ Krylov.subspace (T : F →ₗ[ℝ] F) h k)
    (hgal : ∀ v ∈ Krylov.subspace (T : F →ₗ[ℝ] F) h k, ⟪h + T s + μ • s, v⟫ = 0) : ‖s‖ ≤ ‖z‖ :=
  (isGalerkinIterate_of_inner_eq_zero hs hgal).norm_le_of_isPositive hpos hz

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The norm is monotone in the regularization multiplier `σ ‖s‖^{r-2}` (`σ > 0`, `r > 2`). -/
theorem norm_le_norm_of_mul_rpow_le {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) {s t : F}
    (h : σ * ‖s‖ ^ (r - 2) ≤ σ * ‖t‖ ^ (r - 2)) : ‖s‖ ≤ ‖t‖ :=
  (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) (by linarith)).1
    (le_of_mul_le_mul_left h hσ)

variable (hT : (T : F →ₗ[ℝ] F).IsSymmetric) {h : F} {k : ℕ}
include hT

/-- **Multiplier comparison, regularization** (core of Lemma 10.2.1). Let `σ > 0`, `r > 2`,
`s ∈ 𝒦_k(T, h)` with `h + T s + λ s ⟂ 𝒦_k(T, h)` for `λ = σ ‖s‖^{r-2}` (the first-order condition
of the regularization subproblem restricted to `𝒦_k(T, h)`), and `s*` a global minimizer of the
regularized model. Then `λ ≤ λ* = σ ‖s*‖^{r-2}` and `‖s‖ ≤ ‖s*‖`.

If `λ ≤ λₛ` this is `λₛ ≤ λ*`. Otherwise `T + λ ≻ 0`, `s` is a Galerkin point of
`(T + λ) x = -h`, so `‖s‖ ≤ ‖s(λ)‖`, i.e. `(λ/σ)^{2/(r-2)} ≤ π(λ)`, and `λ ≤ λ*` by
`le_secular_iff_of_regularization` (which covers the hard case for `s*`). -/
theorem regMultiplier_le_of_inner_eq_zero {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) {s sstar : F}
    (hs : s ∈ Krylov.subspace (T : F →ₗ[ℝ] F) h k)
    (hgal : ∀ v ∈ Krylov.subspace (T : F →ₗ[ℝ] F) h k,
      ⟪h + T s + (σ * ‖s‖ ^ (r - 2)) • s, v⟫ = 0)
    (hmin : IsMinOn (regModel h T σ r) univ sstar) :
    σ * ‖s‖ ^ (r - 2) ≤ σ * ‖sstar‖ ^ (r - 2) ∧ ‖s‖ ≤ ‖sstar‖ := by
  have hle : σ * ‖s‖ ^ (r - 2) ≤ σ * ‖sstar‖ ^ (r - 2) := by
    by_cases hth : σ * ‖s‖ ^ (r - 2) ≤ shiftThreshold hT
    · exact hth.trans (shiftThreshold_le_of_isMinOn_regModel (hH := hT) hσ hr hmin).1
    push Not at hth
    have hlam : -leftmost hT < σ * ‖s‖ ^ (r - 2) := neg_leftmost_le_shiftThreshold.trans_lt hth
    refine (le_secular_iff_of_regularization (hH := hT) hσ hr hmin hth).1 ?_
    rw [← norm_sq_eq_rpow hσ hr s, secular]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_of_inner_eq_zero
      (isPositive_add_smul_of_le hlam.le) (step_spec (hH := hT) hlam).1 hs hgal) 2
  exact ⟨hle, norm_le_norm_of_mul_rpow_le hσ hr hle⟩

/-- **Multiplier comparison, trust region** (core of Lemma 10.3.1). Let `Δ > 0`,
`s ∈ 𝒦_k(T, h)` with `‖s‖ ≤ Δ`, `μ ≥ 0`, `μ (‖s‖ - Δ) = 0` and `h + T s + μ s ⟂ 𝒦_k(T, h)` (the
first-order conditions of the trust-region subproblem restricted to `𝒦_k(T, h)`), and let `s*` be
a global solution with multiplier `μ*`. Then `μ ≤ μ*` and `‖s‖ ≤ ‖s*‖`.

If `μ > λₛ` then `‖s‖ = Δ` and `Δ ≤ ‖s(μ)‖` as in `regMultiplier_le_of_inner_eq_zero`. For the
norms, if `μ < μ*` then `‖s*‖ = Δ`; if `μ = μ*`, `s` is a Galerkin point of the semidefinite
consistent system `(T + μ*) x = -h` solved by `s*`, so `‖s‖ ≤ ‖s*‖`
(`Krylov.IsGalerkinIterate.norm_le_of_isPositive`; this includes the singular interior case). -/
theorem trMultiplier_le_of_inner_eq_zero {Δ μ μstar : ℝ} (hΔ : 0 < Δ) {s sstar : F}
    (hs : s ∈ Krylov.subspace (T : F →ₗ[ℝ] F) h k) (hsΔ : ‖s‖ ≤ Δ) (hμ : 0 ≤ μ)
    (hc : μ * (‖s‖ - Δ) = 0)
    (hgal : ∀ v ∈ Krylov.subspace (T : F →ₗ[ℝ] F) h k, ⟪h + T s + μ • s, v⟫ = 0)
    (hstar : IsTrustRegionMultiplier h T Δ sstar μstar) (hsstar : ‖sstar‖ ≤ Δ) :
    μ ≤ μstar ∧ ‖s‖ ≤ ‖sstar‖ := by
  have hle : μ ≤ μstar := by
    by_cases hth : μ ≤ shiftThreshold hT
    · exact hth.trans (shiftThreshold_le_of_isTrustRegionMultiplier (hH := hT) hstar).1
    push Not at hth
    have hlam : -leftmost hT < μ := neg_leftmost_le_shiftThreshold.trans_lt hth
    have hsn : ‖s‖ = Δ := by
      have hμ0 : μ ≠ 0 := (shiftThreshold_nonneg.trans_lt hth).ne'
      linarith [(mul_eq_zero.1 hc).resolve_left hμ0]
    refine (le_secular_iff_of_trustRegion (hH := hT) hΔ hstar hsstar hth).1 ?_
    rw [← hsn, secular]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_of_inner_eq_zero
      (isPositive_add_smul_of_le hlam.le) (step_spec (hH := hT) hlam).1 hs hgal) 2
  refine ⟨hle, ?_⟩
  rcases hle.lt_or_eq with hlt | rfl
  · rw [hstar.norm_eq_of_pos (hμ.trans_lt hlt)]; exact hsΔ
  · exact norm_le_of_inner_eq_zero hstar.isPositive hstar.shifted hs hgal

end Abstract

/-! ### Subproblems on Krylov subspaces -/

section Krylov

variable {H : E →L[ℝ] E} {g : E}

/-- `𝒦ₕ[k]` is the Krylov subspace `𝒦_k(H, g)` of the operator `H` and the gradient `g`. -/
local notation "𝒦ₕ[" k "]" => 𝒦[(H : E →ₗ[ℝ] E), g] k

omit [FiniteDimensional ℝ E] in
/-- The starting vector lies in every nontrivial Krylov subspace. -/
theorem mem_krylov (H : E →L[ℝ] E) (g : E) {k : ℕ} (hk : 1 ≤ k) :
    g ∈ 𝒦[(H : E →ₗ[ℝ] E), g] k :=
  Krylov.self_mem_subspace _ g hk

omit [FiniteDimensional ℝ E] in
/-- On a nontrivial Krylov subspace the projected gradient is the gradient. -/
theorem orthogonalProjectionOnto_krylov {k : ℕ} (hk : 1 ≤ k) :
    (𝒦ₕ[k]).orthogonalProjectionOnto g = ⟨g, mem_krylov H g hk⟩ :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨g, mem_krylov H g hk⟩ : _)

/-- **The nested Krylov subspaces inside `𝒦_ℓ`.** For `k ≤ ℓ`, `1 ≤ ℓ`, the `k`-th Krylov subspace
of the compressed data `(P g, P H|)` on `𝒦_ℓ = 𝒦_ℓ(H, g)` is `𝒦_k(H, g)`. -/
theorem mem_subspace_compressionL_iff {k ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ)
    (v : 𝒦ₕ[ℓ]) :
    v ∈ Krylov.subspace (compressionL H (𝒦ₕ[ℓ]) : 𝒦ₕ[ℓ] →ₗ[ℝ] _)
        ((𝒦ₕ[ℓ]).orthogonalProjectionOnto g) k ↔
      (v : E) ∈ 𝒦ₕ[k] := by
  rw [coe_compressionL, orthogonalProjectionOnto_krylov hℓ]
  exact mem_subspace_compression_iff _ _ hkℓ v

/-- **Transport of a restricted first-order condition into a larger Krylov subspace.** If
`s ∈ 𝒦_k` and `g + H s + μ s ⟂ 𝒦_k`, then for `k ≤ ℓ` the point `s` of `𝒦_ℓ` satisfies the
same condition for the compressed data `(P g, P H|)` on `𝒦_ℓ` and its own Krylov subspace
`𝒦_k(P H|, P g) = 𝒦_k`. -/
theorem galerkin_compressionL_of_le {k ℓ : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) {s : E} {μ : ℝ}
    (hs : s ∈ 𝒦ₕ[k])
    (hgal : ∀ v ∈ 𝒦ₕ[k], ⟪g + H s + μ • s, v⟫ = 0) :
    (⟨s, Krylov.subspace_mono _ g hkℓ hs⟩ : 𝒦ₕ[ℓ]) ∈
        Krylov.subspace (compressionL H (𝒦ₕ[ℓ]) : 𝒦ₕ[ℓ] →ₗ[ℝ] _)
          ((𝒦ₕ[ℓ]).orthogonalProjectionOnto g) k ∧
      ∀ v ∈ Krylov.subspace (compressionL H (𝒦ₕ[ℓ]) : 𝒦ₕ[ℓ] →ₗ[ℝ] _)
          ((𝒦ₕ[ℓ]).orthogonalProjectionOnto g) k,
        ⟪(𝒦ₕ[ℓ]).orthogonalProjectionOnto g +
          compressionL H _ ⟨s, Krylov.subspace_mono _ g hkℓ hs⟩ +
            μ • (⟨s, Krylov.subspace_mono _ g hkℓ hs⟩ : 𝒦ₕ[ℓ]),
          v⟫ = 0 := by
  have hℓ : 1 ≤ ℓ := hk.trans hkℓ
  refine ⟨(mem_subspace_compressionL_iff hℓ hkℓ _).2 hs, fun v hv => ?_⟩
  rw [inner_orthogonalProjectionOnto_add_compressionL]
  exact hgal _ ((mem_subspace_compressionL_iff hℓ hkℓ v).1 hv)

/-- **No hard case on Krylov subspaces** ([cartis2022evaluation] §10.2.1, citing
Gould–Lucidi–Roma–Toint, Thms 5.3 and 5.5). Let `H` be symmetric, `g ≠ 0`, `k ≥ 1`, and let
`P H|` be the compression of `H` to `𝒦_k = 𝒦_k(H, g)`, with least eigenvalue `θ₁`. Then
(i) `g` (that is, `P g`) is a cyclic vector of `P H|`: its Krylov space is all of `𝒦_k`;
(ii) no eigenvector of `P H|` is orthogonal to `g` (in the Lanczos basis: every eigenvector of
the unreduced tridiagonal `T_k` has a nonzero first component);
(iii) every `μ` with `P H| + μ ⪰ 0` and `(P H| + μ) s = -P g` satisfies `μ > -θ₁`, i.e.
`P H| + μ` is positive definite: the hard case cannot occur for the restricted subproblems.
No condition `k ≤ grade(H, g)` is needed. -/
theorem krylov_no_hardCase (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {k : ℕ}
    (hk : 1 ≤ k) :
    Krylov.subspace (compressionL H 𝒦ₕ[k] : 𝒦ₕ[k] →ₗ[ℝ] _)
        ((𝒦ₕ[k]).orthogonalProjectionOnto g) k = ⊤ ∧
      (∀ (v : 𝒦ₕ[k]) (θ : ℝ), compressionL H 𝒦ₕ[k] v = θ • v → v ≠ 0 → ⟪(v : E), g⟫ ≠ 0) ∧
      ∀ (μ : ℝ) (s : 𝒦ₕ[k]),
        ((compressionL H 𝒦ₕ[k] + μ • 1 : 𝒦ₕ[k] →L[ℝ] 𝒦ₕ[k]) : 𝒦ₕ[k] →ₗ[ℝ] 𝒦ₕ[k]).IsPositive →
        (compressionL H 𝒦ₕ[k] + μ • (1 : 𝒦ₕ[k] →L[ℝ] 𝒦ₕ[k])) s =
          -(𝒦ₕ[k]).orthogonalProjectionOnto g →
        -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) < μ := by
  have hgK := mem_krylov H g hk
  have heig : ∀ (v : 𝒦ₕ[k]) (θ : ℝ), compressionL H 𝒦ₕ[k] v = θ • v → v ≠ 0 →
      ⟪(v : E), g⟫ ≠ 0 := fun v θ hv hv0 =>
    inner_ne_zero_of_compression_eigen (H : E →ₗ[ℝ] E) hH hgK hv hv0
  refine ⟨?_, heig, fun μ s hpos hs => ?_⟩
  · rw [coe_compressionL, orthogonalProjectionOnto_krylov hk]
    exact subspace_compression_eq_top _ hgK
  · have : Nontrivial 𝒦ₕ[k] := ⟨⟨⟨g, hgK⟩, 0, fun h => hg (congrArg Subtype.val h)⟩⟩
    refine neg_leftmost_lt_of_shifted _ (fun v hv hv0 => ?_) hpos hs
    rw [real_inner_comm, inner_orthogonalProjectionOnto_left, real_inner_comm]
    exact heig v _ hv hv0

/-- **The restricted regularization multiplier is to the right of the Ritz threshold.** If `s`
minimizes the regularized model over `𝒦_k` (`g ≠ 0`, `k ≥ 1`), then its multiplier
`λₖ = σ ‖s‖^{r-2}` satisfies `λₖ > -θ₁` (`θ₁` the least eigenvalue of the compression `P H|`),
and `s` is the step of the compressed data at `λₖ` ((10.2.2) with `T_k + λₖ` positive
definite). -/
theorem neg_leftmost_lt_of_isMinOn_regModel_krylov (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (hg : g ≠ 0) {σ r : ℝ} (hσ : 0 < σ) (hr : 2 < r) {k : ℕ} (hk : 1 ≤ k) {s : E}
    (hs : s ∈ 𝒦ₕ[k]) (hmin : IsMinOn (regModel g H σ r) (𝒦ₕ[k] : Set E) s) :
    -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) < σ * ‖s‖ ^ (r - 2) ∧
      (⟨s, hs⟩ : 𝒦ₕ[k]) =
        step ((𝒦ₕ[k]).orthogonalProjectionOnto g) (compressionL H _) (σ * ‖s‖ ^ (r - 2)) := by
  obtain ⟨hshift, hpos⟩ := (isMinOn_regModel_iff (isSymmetric_compressionL hH) hσ hr).1
    ((isMinOn_regModel_subspace_iff_compression hs).1 hmin)
  have hlt := (krylov_no_hardCase hH hg hk).2.2 _ _ hpos hshift
  exact ⟨hlt, (step_spec hlt).2 _ hshift⟩

/-- **The restricted trust-region multiplier is to the right of the Ritz threshold.** If `μ` is a
trust-region multiplier of `s ∈ 𝒦_k` for the compressed data (`g ≠ 0`, `k ≥ 1`), then
`μ > -θ₁` and `s` is the step of the compressed data at `μ`. -/
theorem neg_leftmost_lt_of_isTrustRegionMultiplier_krylov (hH : (H : E →ₗ[ℝ] E).IsSymmetric)
    (hg : g ≠ 0) {Δ μ : ℝ} {k : ℕ} (hk : 1 ≤ k) {s : E} (hs : s ∈ 𝒦ₕ[k])
    (h : IsTrustRegionMultiplier ((𝒦ₕ[k]).orthogonalProjectionOnto g) (compressionL H _) Δ
      ⟨s, hs⟩ μ) :
    -leftmost (isSymmetric_compressionL (K := 𝒦ₕ[k]) hH) < μ ∧
      (⟨s, hs⟩ : 𝒦ₕ[k]) = step ((𝒦ₕ[k]).orthogonalProjectionOnto g) (compressionL H _) μ := by
  have hlt := (krylov_no_hardCase hH hg hk).2.2 _ _ h.isPositive h.shifted
  exact ⟨hlt, (step_spec hlt).2 _ h.shifted⟩

/-- **Lemma 10.2.1** (nested Krylov solutions of the regularization subproblem increase in norm;
[cartis2022evaluation] Lemma 10.2.1). Let `H` be symmetric, `σ > 0`, `r > 2`, and for
`1 ≤ k ≤ ℓ` let `sₖ`, `sℓ` minimize the regularized model `m^R` over the Krylov subspaces
`𝒦_k = 𝒦_k(H, g)`, `𝒦_ℓ`, with multipliers `λₖ = σ ‖sₖ‖^{r-2}`, `λℓ = σ ‖sℓ‖^{r-2}`, and let `s*`
be a global minimizer with `λ* = σ ‖s*‖^{r-2}`. Then `λₖ ≤ λℓ ≤ λ*` and `‖sₖ‖ ≤ ‖sℓ‖ ≤ ‖s*‖`.

The comparison of `sℓ` with `s*` is `regMultiplier_le_of_inner_eq_zero` in `E`; that of `sₖ` with
`sℓ` is the same lemma inside the space `𝒦_ℓ`, where `sℓ` is a global minimizer of the compressed
problem and `𝒦_k` is the `k`-th Krylov subspace of the compressed data. -/
theorem krylov_multiplier_mono_regularization (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {σ r : ℝ}
    (hσ : 0 < σ) (hr : 2 < r) {k ℓ : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) {sk sl sstar : E}
    (hsk : sk ∈ 𝒦ₕ[k])
    (hmink : IsMinOn (regModel g H σ r) (𝒦ₕ[k] : Set E) sk)
    (hsl : sl ∈ 𝒦ₕ[ℓ])
    (hminl : IsMinOn (regModel g H σ r) (𝒦ₕ[ℓ] : Set E) sl)
    (hmin : IsMinOn (regModel g H σ r) univ sstar) :
    (σ * ‖sk‖ ^ (r - 2) ≤ σ * ‖sl‖ ^ (r - 2) ∧ σ * ‖sl‖ ^ (r - 2) ≤ σ * ‖sstar‖ ^ (r - 2)) ∧
      ‖sk‖ ≤ ‖sl‖ ∧ ‖sl‖ ≤ ‖sstar‖ := by
  have h2 := regMultiplier_le_of_inner_eq_zero hH hσ hr hsl
    (galerkin_of_isMinOn_regModel_subspace hH hσ hr hsl hminl).1 hmin
  obtain ⟨hmem, hgal⟩ := galerkin_compressionL_of_le hk hkℓ hsk
    (galerkin_of_isMinOn_regModel_subspace hH hσ hr hsk hmink).1
  have h1 := regMultiplier_le_of_inner_eq_zero (isSymmetric_compressionL hH) hσ hr hmem hgal
    ((isMinOn_regModel_subspace_iff_compression hsl).1 hminl)
  exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩

/-- **Lemma 10.3.1** (nested Krylov solutions of the trust-region subproblem increase in norm;
[cartis2022evaluation] Lemma 10.3.1). Let `H` be symmetric, `Δ > 0`, and for `1 ≤ k ≤ ℓ` let
`sₖ ∈ 𝒦_k`, `sℓ ∈ 𝒦_ℓ` be feasible (`‖·‖ ≤ Δ`) with trust-region multipliers `λₖ`, `λℓ` for the
subproblems restricted to `𝒦_k`, `𝒦_ℓ` (multipliers of the compressed data, equivalently global
solutions of the restricted problems by `isMinOn_subspace_iff_compression` and
`isMinOn_closedBall_iff`), and let `s*` be a feasible step with multiplier `λ*` for the full
problem. Then `λₖ ≤ λℓ ≤ λ*` and `‖sₖ‖ ≤ ‖sℓ‖ ≤ ‖s*‖`. -/
theorem krylov_multiplier_mono_trustRegion (hH : (H : E →ₗ[ℝ] E).IsSymmetric) {Δ : ℝ}
    (hΔ : 0 < Δ) {k ℓ : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ) {sk sl sstar : E} {μk μl μstar : ℝ}
    (hsk : sk ∈ 𝒦ₕ[k]) (hskΔ : ‖sk‖ ≤ Δ)
    (hmk : IsTrustRegionMultiplier ((𝒦ₕ[k]).orthogonalProjectionOnto g)
      (compressionL H _) Δ ⟨sk, hsk⟩ μk)
    (hsl : sl ∈ 𝒦ₕ[ℓ]) (hslΔ : ‖sl‖ ≤ Δ)
    (hml : IsTrustRegionMultiplier ((𝒦ₕ[ℓ]).orthogonalProjectionOnto g)
      (compressionL H _) Δ ⟨sl, hsl⟩ μl)
    (hstar : IsTrustRegionMultiplier g H Δ sstar μstar) (hsstar : ‖sstar‖ ≤ Δ) :
    (μk ≤ μl ∧ μl ≤ μstar) ∧ ‖sk‖ ≤ ‖sl‖ ∧ ‖sl‖ ≤ ‖sstar‖ := by
  have h2 := trMultiplier_le_of_inner_eq_zero hH hΔ hsl hslΔ hml.nonneg hml.complementarity
    (hml.galerkin_of_compressionL hsl) hstar hsstar
  obtain ⟨hmem, hgal⟩ := galerkin_compressionL_of_le hk hkℓ hsk (hmk.galerkin_of_compressionL hsk)
  have h1 := trMultiplier_le_of_inner_eq_zero (isSymmetric_compressionL hH) hΔ hmem hskΔ
    hmk.nonneg hmk.complementarity hgal hml hslΔ
  exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩

end Krylov

/-! ### Lanczos coordinates -/

section Lanczos

open Matrix

variable {H : E →L[ℝ] E} {g : E}

/-- The Lanczos vectors `q j = Arnoldi.vec H g j` (`0`-based; the book's `q_{j+1}`). -/
local notation "𝐪" => Arnoldi.vec (H : E →ₗ[ℝ] E) g

/-- The Lanczos tridiagonal matrices `T_m = Lanczos.tridiag H g m`. -/
local notation "𝐓" => Lanczos.tridiag (H : E →ₗ[ℝ] E) g

/-- The Lanczos off-diagonal coefficients `β j = Lanczos.beta H g j` (the book's `γ_{j+2}`). -/
local notation "𝛃" => Lanczos.beta (H : E →ₗ[ℝ] E) g

omit [FiniteDimensional ℝ E] in
/-- **The shifted Lanczos relation** ((10.2.1)): for `Q y = ∑ⱼ yⱼ qⱼ` (`j < m + 1`),
`H (Q y) + μ Q y = Q ((T_{m+1} + μ) y) + β_m y_m q_{m+1}`. -/
theorem lanczos_apply_add_smul (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (m : ℕ) (y : Fin (m + 1) → ℝ)
    (μ : ℝ) :
    H (∑ j, y j • 𝐪 j) + μ • ∑ j, y j • 𝐪 j =
      ∑ i : Fin (m + 1),
          ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ y) i • 𝐪 i +
        (𝛃 m * y (Fin.last m)) • 𝐪 (m + 1) := by
  have h1 := Lanczos.apply_sum g hH m y
  simp only [ContinuousLinearMap.coe_coe, Algebra.algebraMap_self, RingHom.coe_id,
    Matrix.map_id, RCLike.ofReal_real_eq_id, id] at h1
  rw [h1, Finset.smul_sum, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
    smul_smul]
  abel

omit [FiniteDimensional ℝ E] in
/-- The gradient in the Lanczos basis: `g = ‖g‖ q₀` ((10.1.3)–(10.1.4), `γ₁ = ‖g‖`). -/
theorem eq_sum_single_vec (hg : g ≠ 0) (m : ℕ) :
    g = ∑ i : Fin (m + 1), (Pi.single 0 ‖g‖ : Fin (m + 1) → ℝ) i • 𝐪 i := by
  rw [Finset.sum_eq_single (0 : Fin (m + 1)) (fun i _ hi => by rw [Pi.single_eq_of_ne hi,
    zero_smul]) (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, Fin.val_zero,
    Arnoldi.vec_zero _ _ hg, smul_smul, RCLike.ofReal_real_eq_id, id,
    mul_inv_cancel₀ (norm_ne_zero_iff.2 hg), one_smul]

/-- Coordinates in the Lanczos basis below the grade: `⟪qᵢ, ∑ⱼ yⱼ qⱼ⟫ = yᵢ`. -/
theorem inner_vec_sum {m : ℕ} (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g)
    (y : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : ⟪𝐪 i, ∑ j, y j • 𝐪 j⟫ = y i := by
  simp only [inner_sum, inner_smul_right]
  rw [Finset.sum_eq_single i (fun j _ hj => by
    rw [Arnoldi.inner_vec_eq_zero _ _ (fun h => hj (Fin.ext h).symm), mul_zero])
    (fun h => absurd (Finset.mem_univ _) h), real_inner_self_eq_norm_sq,
    Arnoldi.norm_vec_eq_one_of_lt_grade _ _ (i.2.trans_le hm), one_pow, mul_one]

omit [FiniteDimensional ℝ E] in
/-- The next Lanczos vector is orthogonal to `𝒦_{m+1}`: `⟪q_{m+1}, ∑ⱼ yⱼ qⱼ⟫ = 0`. -/
theorem inner_vec_succ_sum (m : ℕ) (y : Fin (m + 1) → ℝ) :
    ⟪𝐪 (m + 1), ∑ j : Fin (m + 1), y j • 𝐪 j⟫ = 0 := by
  simp only [inner_sum, inner_smul_right]
  exact Finset.sum_eq_zero fun j _ => by
    rw [Arnoldi.inner_vec_eq_zero _ _ (by have := j.2; omega), mul_zero]

/-- The Lanczos basis is orthonormal below the grade: `⟪Q x, Q y⟫ = x ⬝ y`. -/
theorem inner_sum_vec_sum {m : ℕ} (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g)
    (x y : Fin (m + 1) → ℝ) : ⟪∑ i, x i • 𝐪 i, ∑ j, y j • 𝐪 j⟫ = x ⬝ᵥ y := by
  simp only [sum_inner, inner_smul_left, inner_vec_sum hm, dotProduct, conj_trivial]

omit [FiniteDimensional ℝ E] in
/-- Every element of `𝒦_{m+1}` is the combination of the Lanczos vectors with its own Lanczos
coordinates `ȳⱼ = ⟪qⱼ, s⟫`. -/
theorem eq_sum_inner_vec {m : ℕ} {s : E} (hs : s ∈ 𝒦[(H : E →ₗ[ℝ] E), g] (m + 1)) :
    s = ∑ j : Fin (m + 1), ⟪𝐪 j, s⟫ • 𝐪 j := by
  conv_lhs => rw [Arnoldi.eq_sum_inner_smul_vec _ _ hs]
  exact (Fin.sum_univ_eq_sum_range (fun j => ⟪𝐪 j, s⟫ • 𝐪 j) (m + 1)).symm

/-- `‖(β_m c) q_{m+1}‖ = β_m |c|` for `m + 1 ≤ grade`: `q_{m+1}` is a unit vector below the grade,
and `β_m = 0` at the grade. -/
theorem norm_beta_smul_vec_succ (m : ℕ) (c : ℝ) :
    ‖(𝛃 m * c) • 𝐪 (m + 1)‖ = 𝛃 m * |c| := by
  rcases lt_or_ge (m + 1) (Krylov.grade (H : E →ₗ[ℝ] E) g) with hlt | hge
  · rw [norm_smul, Arnoldi.norm_vec_eq_one_of_lt_grade _ _ hlt, mul_one, Real.norm_eq_abs,
      abs_mul, abs_of_nonneg (Lanczos.beta_nonneg _ _ _)]
  · rw [(Lanczos.beta_eq_zero_iff g m).2 hge]; simp

/-- **Lanczos coordinates** ([cartis2022evaluation] (10.1.3)–(10.1.6), (10.2.1), (B.10.1)). Let
`g ≠ 0`, `m + 1 ≤ grade(H, g)`, `qⱼ` the Lanczos vectors, `T = T_{m+1}` the Lanczos tridiagonal
matrix, `β_m` the next off-diagonal coefficient, and `Q y = ∑ⱼ yⱼ qⱼ`. Then for all `x, y` and
`μ`:
(i) `g + H (Q y) + μ Q y = Q ((T + μ) y + ‖g‖ e₀) + β_m y_m q_{m+1}`;
(ii) `Q` is an isometry: `⟪Q x, Q y⟫ = x ⬝ y`;
(iii) `Q` carries the quadratic form: `⟪Q x, H (Q y) + μ Q y⟫ = x ⬝ (T + μ) y`;
(iv) if `(T + μ) y = -‖g‖ e₀` ((10.2.2)) then `‖g + H (Q y) + μ Q y‖ = β_m |y_m|` ((B.10.1)). -/
theorem krylov_lanczos_coordinates (hH : (H : E →ₗ[ℝ] E).IsSymmetric) (hg : g ≠ 0) {m : ℕ}
    (hm : m + 1 ≤ Krylov.grade (H : E →ₗ[ℝ] E) g) (x y : Fin (m + 1) → ℝ) (μ : ℝ) :
    (g + H (∑ j, y j • 𝐪 j) + μ • ∑ j, y j • 𝐪 j =
      ∑ i : Fin (m + 1), ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ y +
          (Pi.single 0 ‖g‖ : Fin (m + 1) → ℝ)) i • 𝐪 i + (𝛃 m * y (Fin.last m)) • 𝐪 (m + 1)) ∧
    ⟪∑ i, x i • 𝐪 i, ∑ j, y j • 𝐪 j⟫ = x ⬝ᵥ y ∧
    ⟪∑ i, x i • 𝐪 i, H (∑ j, y j • 𝐪 j) + μ • ∑ j, y j • 𝐪 j⟫ =
      x ⬝ᵥ ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ y) ∧
    ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ y =
        -(Pi.single 0 ‖g‖ : Fin (m + 1) → ℝ) →
      ‖g + H (∑ j, y j • 𝐪 j) + μ • ∑ j, y j • 𝐪 j‖ = 𝛃 m * |y (Fin.last m)|) := by
  have hrel := lanczos_apply_add_smul (g := g) hH m y μ
  have hi : g + H (∑ j, y j • 𝐪 j) + μ • ∑ j, y j • 𝐪 j =
      ∑ i : Fin (m + 1), ((𝐓 (m + 1) + μ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) *ᵥ y +
          (Pi.single 0 ‖g‖ : Fin (m + 1) → ℝ)) i • 𝐪 i + (𝛃 m * y (Fin.last m)) • 𝐪 (m + 1) := by
    rw [add_assoc, hrel]
    conv_lhs => arg 1; rw [eq_sum_single_vec (H := H) hg m]
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  refine ⟨hi, inner_sum_vec_sum hm x y, ?_, fun hT => ?_⟩
  · rw [hrel, inner_add_right, inner_sum_vec_sum hm, real_inner_smul_right, real_inner_comm,
      inner_vec_succ_sum, mul_zero, add_zero]
  · rw [hi, hT, neg_add_cancel]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
    exact norm_beta_smul_vec_succ m _

end Lanczos

end Subproblem
