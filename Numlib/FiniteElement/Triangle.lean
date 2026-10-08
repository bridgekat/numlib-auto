import Numlib.Analysis.PDE.Elliptic.Spectral
import Numlib.FiniteElement.Interpolation
import Numlib.Variational.Galerkin

/-!
# The finite element method on triangulations: convergence and error estimates

The a priori error of the Galerkin method on finite element spaces over a regular family of
triangulations of a plane domain: Céa's lemma (`IsGalerkinSolution.norm_sub_le`) with the
interpolant `v_h = Π_h u` as competitor, and the global interpolation estimate
`Triangulation.sobolevNorm_sub_globalInterp_le` at `m = 1`. The one-dimensional counterpart is
`Numlib/Variational/FiniteElementInterval.lean`.

The setting is the backbone's: a subspace `V ⊆ H¹(Ω)` (`SobolevEuclidean 2 1 2 Ω`), a bounded
coercive form `a : SesqForm ℝ V` (`SesqForm.IsBoundedWith`, `SesqForm.IsCoerciveWith`), and Galerkin
solutions `IsGalerkinSolution a ℓ V_h u_h` on subspaces `V_h ⊆ V`. The finite element space enters
only through `Π_h u ∈ V_h`, a hypothesis; for `V = H¹₀(Ω)` and `V_h` the continuous piecewise
polynomials vanishing on `∂Ω` (`Triangulation.polySpaceZero`) it is
`LagrangeElement.exists_mem_polySpaceZero_globalInterp`. The regularity of the solution is read on
a representative `ũ` continuous up to the boundary, as in the interpolation estimates.

## Main results

* `FiniteElement.norm_sub_le_of_isGalerkinSolution` — `‖u − u_h‖_V ≤ c h^k |u|_{k+1,Ω}` for an
  element reproducing `ℙ_k`, conforming on a regular family of triangulations.
* `FiniteElement.tendsto_norm_sub_of_isGalerkinSolution` — `‖u − u_h‖_V → 0` along the family,
  when `u` is approximated in `V` by functions of `H^{k+1}(Ω) ∩ C(Ω̄)` with interpolants in `V_h`.
* `FiniteElement.norm_sub_le_of_isGalerkinSolution_dirichletForm` — the Poisson problem
  `−Δu = f`, `u = 0` on `∂Ω`, on a polygon with the `ℙ_k` Lagrange element:
  `‖u − u_h‖_{H¹₀} ≤ (M/α₀) C h^s ‖u‖_{s+1,Ω}`, `1 ≤ s ≤ k`, with `M = 1` and
  `α₀ = (1 + (2R)²)⁻¹` for `Ω ⊆ B(0, R)`.

## References

* [han2009theoretical] Theorem 10.4.1, Example 10.4.2.
* [quarteroni2000numerical] Property 12.2, (12.96).
-/

open Filter MeasureTheory Set TopologicalSpace EuclideanSpace Topology Metric
open scoped ENNReal

namespace FiniteElement

local notation "𝔼₂" => EuclideanSpace ℝ (Fin 2)

/-! ### Norms of `H¹(Ω)` against the tensor Sobolev norm -/

/-- The norm of `H¹(Ω)` (the multi-index space `SobolevEuclidean N 1 2 Ω`) is bounded by the
tensor Sobolev norm `‖·‖_{1,Ω}` of the function, up to a constant depending on the dimension
only: `SobolevMultiIndex.ofReal_norm_le_sobolevNorm` in real form. -/
theorem exists_norm_le_sobolevNorm {N : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin N))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : SobolevEuclidean N 1 2 Ω,
      ‖w‖ ≤ C * (sobolevNorm (SobolevMultiIndex.fn w) 1 2 Ω volume).toReal := by
  obtain ⟨C₂, hC₂fin, hC₂⟩ : ∃ C₂ : ℝ≥0∞, C₂ ≠ ⊤ ∧ ∀ w : SobolevEuclidean N 1 2 Ω,
      ENNReal.ofReal ‖w‖ ≤ C₂ * sobolevNorm (SobolevMultiIndex.fn w) 1 2 Ω volume :=
    ⟨_, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top⟩,
      fun w ↦ SobolevMultiIndex.ofReal_norm_le_sobolevNorm (by simp) w⟩
  refine ⟨C₂.toReal, ENNReal.toReal_nonneg, fun w ↦ ?_⟩
  have hfin : sobolevNorm (SobolevMultiIndex.fn w) 1 2 Ω volume ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_
      ((SobolevMultiIndex.memSobolev_fn w).sobolevNorm_le_sum_sobolevSeminorm (by simp))
    exact ENNReal.sum_ne_top.2 fun n _ ↦ ((SobolevMultiIndex.memSobolev_fn w).mono_order
      (by exact_mod_cast Nat.lt_succ_iff.1 n.2)).sobolevSeminorm_ne_top
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC₂fin hfin) (hC₂ w)
  rwa [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul] at h

/-- The distance in a subspace `V ⊆ H¹(Ω)` between two elements is bounded by the tensor
Sobolev norm of the difference of (representatives of) their functions. -/
theorem norm_sub_le_of_fn_ae_eq {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} {C : ℝ}
    (hC : ∀ w : SobolevEuclidean N 1 2 Ω,
      ‖w‖ ≤ C * (sobolevNorm (SobolevMultiIndex.fn w) 1 2 Ω volume).toReal)
    {V : Submodule ℝ (SobolevEuclidean N 1 2 Ω)} (w wh : V) {w' g : EuclideanSpace ℝ (Fin N) → ℝ}
    (hw : SobolevMultiIndex.fn (w : SobolevEuclidean N 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] w')
    (hwh : SobolevMultiIndex.fn (wh : SobolevEuclidean N 1 2 Ω)
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] g) :
    ‖w - wh‖ ≤ C * (sobolevNorm (w' - g) 1 2 Ω volume).toReal := by
  have hfn : SobolevMultiIndex.fn
      ((w : SobolevEuclidean N 1 2 Ω) - (wh : SobolevEuclidean N 1 2 Ω))
      =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N)))] w' - g := by
    refine (SobolevMultiIndex.fn_sub _ _).trans ?_
    filter_upwards [hw, hwh] with x h1 h2
    simp only [Pi.sub_apply, h1, h2]
  have h := hC ((w : SobolevEuclidean N 1 2 Ω) - (wh : SobolevEuclidean N 1 2 Ω))
  rw [sobolevNorm_congr_ae hfn] at h
  exact h

/-- The global interpolation estimate at `m = 1`, in real form:
`‖v − Π_h v‖_{1,Ω} ≤ c h^k |v|_{k+1,Ω}`. -/
theorem toReal_sobolevNorm_sub_globalInterp_le {k : ℕ} {I : ℕ} {xhat : Fin I → 𝔼₂}
    {φhat : Fin I → 𝔼₂ → ℝ} {Ω : Opens 𝔼₂} {𝒯 : Triangulation Ω} {c : ℝ} (hc : 0 ≤ c)
    {v : 𝔼₂ → ℝ} (hv : MemSobolev v (k + 1) 2 Ω volume)
    (h : sobolevNorm (v - 𝒯.globalInterp xhat φhat v) 1 2 Ω volume
      ≤ ENNReal.ofReal (c * 𝒯.meshSize ^ (k + 1 - 1)) * sobolevSeminorm v (k + 1) 2 Ω volume) :
    (sobolevNorm (v - 𝒯.globalInterp xhat φhat v) 1 2 Ω volume).toReal
      ≤ c * 𝒯.meshSize ^ k * (sobolevSeminorm v (k + 1) 2 Ω volume).toReal := by
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    hv.sobolevSeminorm_ne_top) h
  rwa [ENNReal.toReal_mul, Nat.add_sub_cancel,
    ENNReal.toReal_ofReal (mul_nonneg hc (pow_nonneg 𝒯.meshSize_nonneg k))] at h'

/-! ### The error estimate and the convergence -/

/-- **The finite element error estimate** ([han2009theoretical] Theorem 10.4.1, (10.4.4)). Let
`V ⊆ H¹(Ω)` be a subspace carrying a bounded, coercive form `a`, let `{𝒯_h}` be a regular family
of triangulations of `Ω` with mesh parameters at most `H`, and let the finite element be the
reference triangle with nodes `x̂ᵢ ∈ K̂̄`, `C¹` shape functions and the polynomial invariance
`ℙ_k(K̂) ⊆ X̂`, `k ≥ 1`, conforming on every `𝒯_h`. Then there is a constant `c` such that for
every solution `u ∈ V` of `a(u, v) = ℓ(v)` and every family of Galerkin solutions `u_h` on
subspaces `V_h ⊆ V` containing the interpolants `Π_h u`, if `u ∈ H^{k+1}(Ω)` (read on its
representative `ũ`, continuous up to the boundary) then

  `‖u − u_h‖_V ≤ c h^k |u|_{k+1,Ω}`.

Céa's lemma with `v_h = Π_h u` (`IsGalerkinSolution.norm_sub_le`), then the interpolation
estimate at `m = 1` (`Triangulation.sobolevNorm_sub_globalInterp_le`), with the norm of
`V ⊆ H¹(Ω)` compared to the tensor norm by `exists_norm_le_sobolevNorm`. -/
theorem norm_sub_le_of_isGalerkinSolution {k : ℕ} (hk : 1 ≤ k) {I : ℕ} (xhat : Fin I → 𝔼₂)
    (φhat : Fin I → 𝔼₂ → ℝ) (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂))
    (hφ : ∀ i, ContDiff ℝ 1 (φhat i))
    (hP : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ referenceTriangle, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H)
    (hconf : ∀ i, (𝒯 i).IsConformingElement xhat φhat)
    {V : Submodule ℝ (SobolevEuclidean 2 1 2 Ω)} {a : SesqForm ℝ V} {M c₀ : ℝ}
    (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsCoerciveWith c₀) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (ℓ : V →L[ℝ] ℝ) (u : V), (∀ v, a u v = ℓ v) →
      ∀ (Vh : ι → Submodule ℝ V) (uh : ι → V), (∀ i, IsGalerkinSolution a ℓ (Vh i) (uh i)) →
      ∀ ũ : 𝔼₂ → ℝ,
        SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ →
        MemSobolev ũ (k + 1) 2 Ω volume → ContinuousOn ũ (closure (Ω : Set 𝔼₂)) →
        (∀ i, ∃ w ∈ Vh i, SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω)
          =ᵐ[volume.restrict (Ω : Set 𝔼₂)] (𝒯 i).globalInterp xhat φhat ũ) →
        ∀ i, ‖u - uh i‖
          ≤ c * (𝒯 i).meshSize ^ k * (sobolevSeminorm ũ (k + 1) 2 Ω volume).toReal := by
  have h10 := Triangulation.sobolevNorm_sub_globalInterp_le (m := 1) le_rfl hk xhat φhat hx hφ hP
    hreg hH hconf
  obtain ⟨c₁, hc₁, hest⟩ := h10
  have hCC := exists_norm_le_sobolevNorm Ω
  obtain ⟨C, hC0, hC⟩ := hCC
  refine ⟨max (M / c₀) 0 * (C * c₁), by positivity,
    fun ℓ u hu Vh uh huh ũ hũ hũk hũc hint i ↦ ?_⟩
  obtain ⟨w, hw, hfw⟩ := hint i
  have hcea := IsGalerkinSolution.norm_sub_le hc₀ hM ha (huh i) hu hw
  have h1 := norm_sub_le_of_fn_ae_eq hC u w hũ hfw
  have h2 := toReal_sobolevNorm_sub_globalInterp_le hc₁ hũk (hest i ũ hũk hũc)
  have hS0 : 0 ≤ (sobolevSeminorm ũ (k + 1) 2 Ω volume).toReal := ENNReal.toReal_nonneg
  have hh0 : 0 ≤ (𝒯 i).meshSize := (𝒯 i).meshSize_nonneg
  calc ‖u - uh i‖ ≤ M / c₀ * ‖u - w‖ := hcea
    _ ≤ max (M / c₀) 0 * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max (M / c₀) 0
          * (C * (c₁ * (𝒯 i).meshSize ^ k * (sobolevSeminorm ũ (k + 1) 2 Ω volume).toReal)) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0)
    _ = _ := by ring

/-- **Convergence of the finite element method** ([han2009theoretical] Theorem 10.4.1, the
convergence): under the assumptions of `norm_sub_le_of_isGalerkinSolution`, if the solution
`u ∈ V` can be approximated in `V` by functions in `H^{k+1}(Ω) ∩ C(Ω̄)` whose interpolants lie in
the `V_h`, then `‖u − u_h‖_V → 0` along the family. The family is indexed by an arbitrary filter,
so the `ε`-argument of `IsGalerkinSolution.tendsto` is redone. -/
theorem tendsto_norm_sub_of_isGalerkinSolution {k : ℕ} (hk : 1 ≤ k) {I : ℕ} (xhat : Fin I → 𝔼₂)
    (φhat : Fin I → 𝔼₂ → ℝ) (hx : ∀ i, xhat i ∈ closure (referenceTriangle : Set 𝔼₂))
    (hφ : ∀ i, ContDiff ℝ 1 (φhat i))
    (hP : ∀ q : MvPolynomial (Fin 2) ℝ, q.totalDegree ≤ k →
      ∀ x ∈ referenceTriangle, Approximation.nodalInterp xhat φhat
        (fun y ↦ MvPolynomial.eval (fun i ↦ y i) q) x = MvPolynomial.eval (fun i ↦ x i) q)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H)
    (hconf : ∀ i, (𝒯 i).IsConformingElement xhat φhat)
    {V : Submodule ℝ (SobolevEuclidean 2 1 2 Ω)} {a : SesqForm ℝ V} {M c₀ : ℝ}
    (hM : a.IsBoundedWith M) (hc₀ : 0 < c₀) (ha : a.IsCoerciveWith c₀) {ℓ : V →L[ℝ] ℝ}
    {u : V} (hu : ∀ v, a u v = ℓ v) {Vh : ι → Submodule ℝ V} {uh : ι → V}
    (huh : ∀ i, IsGalerkinSolution a ℓ (Vh i) (uh i))
    (hdense : ∀ ε > 0, ∃ (w : V) (w' : 𝔼₂ → ℝ), ‖u - w‖ < ε ∧
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] w' ∧
      MemSobolev w' (k + 1) 2 Ω volume ∧ ContinuousOn w' (closure (Ω : Set 𝔼₂)) ∧
      ∀ i, ∃ wh ∈ Vh i, SobolevMultiIndex.fn (wh : SobolevEuclidean 2 1 2 Ω)
        =ᵐ[volume.restrict (Ω : Set 𝔼₂)] (𝒯 i).globalInterp xhat φhat w') :
    Tendsto (fun i ↦ ‖u - uh i‖) l (𝓝 0) := by
  have h10 := Triangulation.sobolevNorm_sub_globalInterp_le (m := 1) le_rfl hk xhat φhat hx hφ hP
    hreg hH hconf
  obtain ⟨c₁, hc₁, hest⟩ := h10
  have hCC := exists_norm_le_sobolevNorm Ω
  obtain ⟨C, hC0, hC⟩ := hCC
  have hmesh : Tendsto (fun i ↦ (𝒯 i).meshSize) l (𝓝 0) :=
    ((isRegularFamily_range_K_iff l 𝒯).1 hreg).2
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M', hM'0, hMM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ M / c₀ ≤ M' := ⟨max (M / c₀) 0, le_max_right _ _,
    le_max_left _ _⟩
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ M' * (2 * δ) < ε := by
    refine ⟨ε / (2 * (M' + 1)), by positivity, ?_⟩
    rw [mul_div_assoc', mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨w, w', hw, hfw, hw'k, hw'c, hwh⟩ := hdense δ hδ
  -- the interpolation error of `w'` tends to zero with the mesh parameter
  have hev : ∀ᶠ i in l,
      C * (c₁ * (𝒯 i).meshSize ^ k * (sobolevSeminorm w' (k + 1) 2 Ω volume).toReal) < δ := by
    have ht : Tendsto (fun i ↦ C * (c₁ * (𝒯 i).meshSize ^ k
        * (sobolevSeminorm w' (k + 1) 2 Ω volume).toReal)) l
        (𝓝 (C * (c₁ * (0 : ℝ) ^ k * (sobolevSeminorm w' (k + 1) 2 Ω volume).toReal))) :=
      (((hmesh.pow k).const_mul c₁).mul_const _).const_mul C
    rw [zero_pow (by omega), mul_zero, zero_mul, mul_zero] at ht
    exact ht.eventually_lt_const hδ
  filter_upwards [hev] with i hi
  obtain ⟨wh, hwh', hfwh⟩ := hwh i
  have hcea := IsGalerkinSolution.norm_sub_le hc₀ hM ha (huh i) hu hwh'
  have h1 := norm_sub_le_of_fn_ae_eq hC w wh hfw hfwh
  have h2 := toReal_sobolevNorm_sub_globalInterp_le hc₁ hw'k (hest i w' hw'k hw'c)
  have hwwh : ‖w - wh‖ < δ :=
    (h1.trans (mul_le_mul_of_nonneg_left h2 hC0)).trans_lt hi
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖u - uh i‖ ≤ M / c₀ * ‖u - wh‖ := hcea
    _ ≤ M' * ‖u - wh‖ := mul_le_mul_of_nonneg_right hMM' (norm_nonneg _)
    _ ≤ M' * (‖u - w‖ + ‖w - wh‖) := by
        gcongr
        exact norm_sub_le_norm_sub_add_norm_sub u w wh
    _ ≤ M' * (δ + δ) := by gcongr
    _ = M' * (2 * δ) := by ring
    _ < ε := hδε

/-! ### The Poisson problem with the `ℙ_k` Lagrange element -/

/-- The Dirichlet form restricted to `H¹₀(Ω)` is bounded with `M = 1`. -/
theorem dirichletForm_restrict_isBoundedWith (Ω : Opens 𝔼₂) :
    ((Elliptic.dirichletForm Ω).restrict (SobolevEuclideanZero 2 1 2 Ω)).IsBoundedWith 1 :=
  fun u v ↦ Elliptic.dirichletForm_isBoundedWith Ω u v

/-- **The finite element error for the Poisson problem** ([han2009theoretical] Example 10.4.2,
[quarteroni2000numerical] Property 12.2, (12.96)). Let `u ∈ H¹₀(Ω)` solve
`∫_Ω ∇u · ∇v = ∫_Ω f v` for all `v ∈ H¹₀(Ω)` (`Elliptic.dirichletForm`, `Elliptic.load`), on a
polygon `Ω ⊆ B(0, R)` triangulated by a regular family `{𝒯_h}` (mesh parameters at most `H`,
`∂Ω` a union of element edges), and let `u_h` be the Galerkin solutions on the spaces
`V_h = Triangulation.polySpaceZero 2 k` of continuous piecewise polynomials of degree at most
`k ≥ 1` vanishing on `∂Ω`. If `u ∈ H^{s+1}(Ω)` for some `1 ≤ s ≤ k`, read on a representative `ũ`
continuous up to the boundary with `ũ = 0` on `∂Ω`, then

  `‖u − u_h‖_{H¹₀(Ω)} ≤ (M/α₀) C h^s ‖u‖_{s+1,Ω}`,

with `M = 1` the continuity constant of the form and `α₀ = (1 + (2R)²)⁻¹` its coercivity constant
on `H¹₀(Ω)` (Poincaré), and `C` independent of `h`, `f` and `u`. It is
`norm_sub_le_of_isGalerkinSolution` with the `ℙ_k` Lagrange element, whose interpolant `Π_h ũ`
lies in `V_h` (`LagrangeElement.exists_mem_polySpaceZero_globalInterp`), and the seminorm bounded
by the norm. -/
theorem norm_sub_le_of_isGalerkinSolution_dirichletForm {k s : ℕ} (hs : 1 ≤ s) (hsk : s ≤ k)
    {Ω : Opens 𝔼₂} {ι : Type*} {l : Filter ι} {𝒯 : ι → Triangulation Ω}
    (hreg : IsRegularFamily l fun i ↦ Set.range (𝒯 i).K)
    {H : ℝ} (hH : ∀ i, (𝒯 i).meshSize ≤ H) (hedge : ∀ i, (𝒯 i).FrontierSubsetEdges)
    {R : ℝ} (hR : 0 ≤ R) (hΩ : (Ω : Set 𝔼₂) ⊆ ball 0 R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼₂)))
      (u : SobolevEuclideanZero 2 1 2 Ω),
      (∀ v : SobolevEuclideanZero 2 1 2 Ω, Elliptic.dirichletForm Ω u v = Elliptic.load Ω f v) →
      ∀ uh : ι → SobolevEuclideanZero 2 1 2 Ω,
        (∀ i, IsGalerkinSolution
          ((Elliptic.dirichletForm Ω).restrict (SobolevEuclideanZero 2 1 2 Ω))
          ((Elliptic.load Ω f).comp (SobolevEuclideanZero 2 1 2 Ω).subtypeL)
          ((𝒯 i).polySpaceZero 2 k) (uh i)) →
        ∀ ũ : 𝔼₂ → ℝ,
          SobolevMultiIndex.fn (u : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)] ũ →
          MemSobolev ũ (s + 1) 2 Ω volume → ContinuousOn ũ (closure (Ω : Set 𝔼₂)) →
          EqOn ũ 0 (frontier (Ω : Set 𝔼₂)) →
          ∀ i, ‖u - uh i‖ ≤ (1 / (1 + (2 * R) ^ 2)⁻¹) * C * (𝒯 i).meshSize ^ s
            * (sobolevNorm ũ (s + 1) 2 Ω volume).toReal := by
  have hk0 : 0 < k := by omega
  have hpos : (0 : ℝ) < (1 + (2 * R) ^ 2)⁻¹ := by positivity
  have h10 := norm_sub_le_of_isGalerkinSolution (k := s) hs
    (LagrangeElement.node k) (LagrangeElement.shape k)
    (LagrangeElement.node_mem_closure hk0)
    (fun i ↦ (LagrangeElement.contDiff_shape k i).of_le (by simp))
    (fun q hq x _ ↦ LagrangeElement.nodalInterp_eval hk0 q (hq.trans hsk) x)
    hreg hH (fun i ↦ LagrangeElement.isConformingElement hk0 (𝒯 i))
    (dirichletForm_restrict_isBoundedWith Ω) hpos
    (Elliptic.dirichletForm_restrict_isCoerciveWith (d := 1) Ω hR hΩ)
  obtain ⟨c, hc0, hc⟩ := h10
  refine ⟨c / (1 + (2 * R) ^ 2), by positivity, fun f u hu uh huh ũ hũ hũk hũc hũ0 i ↦ ?_⟩
  have hint : ∀ i, ∃ w ∈ (𝒯 i).polySpaceZero 2 k,
      SobolevMultiIndex.fn (w : SobolevEuclidean 2 1 2 Ω) =ᵐ[volume.restrict (Ω : Set 𝔼₂)]
        (𝒯 i).globalInterp (LagrangeElement.node k) (LagrangeElement.shape k) ũ := fun i ↦
    LagrangeElement.exists_mem_polySpaceZero_globalInterp hk0 (𝒯 i) 2 (by simp) (hedge i) hũ0
  have h := hc ((Elliptic.load Ω f).comp (SobolevEuclideanZero 2 1 2 Ω).subtypeL) u hu
    (fun i ↦ (𝒯 i).polySpaceZero 2 k) uh huh ũ hũ hũk hũc hint i
  refine h.trans ?_
  -- the seminorm is bounded by the norm, and `(M/α₀) C = c`
  have hfin : sobolevNorm ũ (s + 1) 2 Ω volume ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (hũk.sobolevNorm_le_sum_sobolevSeminorm (by simp))
    exact ENNReal.sum_ne_top.2 fun n _ ↦
      (hũk.mono_order (by exact_mod_cast Nat.lt_succ_iff.1 n.2)).sobolevSeminorm_ne_top
  have hle : (sobolevSeminorm ũ (s + 1) 2 Ω volume).toReal
      ≤ (sobolevNorm ũ (s + 1) 2 Ω volume).toReal :=
    ENNReal.toReal_mono hfin
      (eLpNorm_weakIteratedFDeriv_le_sobolevNorm (by simp) (by simp) le_rfl)
  have hh0 : 0 ≤ (𝒯 i).meshSize := (𝒯 i).meshSize_nonneg
  have hα : (0 : ℝ) < 1 + (2 * R) ^ 2 := by positivity
  have hcc : 1 / (1 + (2 * R) ^ 2)⁻¹ * (c / (1 + (2 * R) ^ 2)) = c := by
    field_simp
  rw [hcc]
  gcongr

end FiniteElement
