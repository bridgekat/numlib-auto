import NumlibSurface.Brezis.Chapter09.Section05

/-!
# Brezis §9.7: The maximum principle

Surface file for Haim Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, Universitext, Springer, 2011, §9.7, on a general open subset `Ω` of
`ℝ^N = EuclideanSpace ℝ (Fin N)` with Lebesgue measure: Theorem 9.27 (the maximum principle for
the Dirichlet problem of `-Δu + u = f`, by Stampacchia's truncation), Corollary 9.28, Remark 27
(the classical proof, for the Laplacian and for a general elliptic operator),
Proposition 9.29 (general second-order elliptic operators with `a₀ ≥ 0`) and Proposition 9.30
(the Neumann problem). Everything delegates to `Numlib/Analysis/PDE/Elliptic/MaximumPrinciple`.

## Conventions

* The book writes `sup_Γ u` and `sup_Ω f` with "sup = essential sup". The surface states the
  bounds with an explicit `K`: "`u ≤ K` on `Γ` and `f ≤ K` a.e. on `Ω` give `u ≤ K` on `Ω`", which
  is the book's statement when `K < ∞` and vacuous otherwise; the `iInf`/`iSup` displays of (71),
  (74), (80), (81) are the same statements read at `K = sup …`.
* "`u ∈ H^1(Ω) ∩ C(Ω̄)`" is `u : hSpace N Ω` with a representative `ũ` continuous on `closure Ω`;
  the conclusions "`u ≤ K` in `Ω`" hold at every point of `Ω` for `ũ`. The footnotes 35, 37, 38
  ("the assumption `u ∈ C(Ω̄)` can be removed if `u ∈ H^1_0(Ω)`") are the `_of_mem_zero` variants,
  whose conclusions are almost everywhere.
* The weak equations (70), (78), (82) are written with the book's integrals
  (`partialDeriv`, `fn`) and bridged to the backbone's forms by `forall_laplaceForm_eq_load_iff`
  and `forall_generalForm_zero_drift_eq_load_iff`.
* Proposition 9.29 is proved by the book only for `a_i ≡ 0`; the drift-free case is
  `proposition_9_29_zero_drift` (with `_inf_zero_drift`, `_sup_inf_zero_drift` for (80), (81)),
  and the general statement waits for the backbone's Gilbarg–Trudinger route. The constancy
  argument of footnote 39 needs `N ≥ 1`, which is carried as `N ≠ 0`.

## Main results

* `theorem_9_27`, `theorem_9_27_of_mem_zero`, `corollary_9_28`, `corollary_9_28_bound`,
  `corollary_9_28_zero_load`, `corollary_9_28_zero_boundary`.
* `remark_9_27` (the Laplacian), `remark_9_27_general` (the general elliptic operator).
* `proposition_9_29_zero_drift`, `proposition_9_29_zero_drift_of_mem_zero`,
  `proposition_9_29_inf_zero_drift`, `proposition_9_29_sup_inf_zero_drift`; the general-drift
  `proposition_9_29`, `proposition_9_29_inf`, `proposition_9_29_sup_inf` wait for the backbone.
* `proposition_9_30`.
-/

open Filter MeasureTheory Metric Set Topology TopologicalSpace Laplacian
open scoped ContDiff Distributions ENNReal NNReal

namespace Brezis.Chapter09

section MaximumPrinciple

variable {N : ℕ}

/-- The book's `ℝ^N`. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

variable {Ω : Opens (EuclideanSpace ℝ (Fin N))}

/-! ### The weak equations in the backbone's terms -/

/-- **The weak equation (70) (resp. (82)) in the backbone's terms**: for a subspace `V` of
`H^1(Ω)` (`H^1_0(Ω)` for (70), `H^1(Ω)` for (82)), `∫_Ω ∇u · ∇φ + ∫_Ω u φ = ∫_Ω f φ` for all
`φ ∈ V` if and only if `laplaceForm Ω u φ = load Ω f φ` for all `φ ∈ V`. -/
theorem forall_laplaceForm_eq_load_iff (u : hSpace N Ω) (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼)))
    (V : Submodule ℝ (hSpace N Ω)) :
    (∀ φ ∈ V, (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x) ↔
      ∀ φ ∈ V, Elliptic.laplaceForm Ω u φ = Elliptic.load Ω f φ := by
  simp only [laplaceForm_apply_two, Elliptic.load_apply]

/-- **The form (41) without drift is the left-hand side of (78) with `a_i = 0`**:
`generalForm Ω A 0 a₀ u v = ∫_Ω ∑ᵢⱼ a_ij ∂ᵢu ∂ⱼv + ∫_Ω a₀ u v`. -/
theorem generalForm_zero_drift_apply (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) (u v : hSpace N Ω) :
    Elliptic.generalForm Ω A 0 a₀ u v
      = (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv v j x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn v x := by
  rw [generalForm_apply_three]
  have hzero : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), ∀ i,
      ((0 : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) i : 𝔼 → ℝ) x = 0 := by
    filter_upwards [Lp.coeFn_zero ℝ ⊤ (volume.restrict (Ω : Set 𝔼))] with x hx i
    simpa only [Pi.zero_apply] using hx
  have e2 : ∫ x in (Ω : Set 𝔼),
      ∑ i, ((0 : Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) i : 𝔼 → ℝ) x
        * partialDeriv u i x * SobolevMultiIndex.fn v x = ∫ x in (Ω : Set 𝔼), (0 : ℝ) :=
    integral_congr_ae (hzero.mono fun x hx ↦ by simp only [hx, zero_mul,
      Finset.sum_const_zero])
  rw [e2, integral_zero, add_zero]

/-- **The weak equation (78) with `a_i = 0` in the backbone's terms**:
`∫_Ω ∑ᵢⱼ a_ij ∂ᵢu ∂ⱼφ + ∫_Ω a₀ u φ = ∫_Ω f φ` for all `φ ∈ H^1_0(Ω)` if and only if
`generalForm Ω A 0 a₀ u φ = load Ω f φ` for all `φ ∈ H^1_0(Ω)`. -/
theorem forall_generalForm_zero_drift_eq_load_iff
    (A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼)))
    (a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) (u : hSpace N Ω)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) :
    (∀ φ ∈ hZeroSpace N Ω,
        (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
          + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
          = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x) ↔
      ∀ φ ∈ hZeroSpace N Ω, Elliptic.generalForm Ω A 0 a₀ u φ = Elliptic.load Ω f φ := by
  simp only [generalForm_zero_drift_apply, Elliptic.load_apply]

/-! ### Theorem 9.27 -/

/-- **Theorem 9.27 (maximum principle for the Dirichlet problem).** Let `Ω` be a general open
subset of `ℝ^N`. Assume that `f ∈ L²(Ω)` and `u ∈ H^1(Ω) ∩ C(Ω̄)` (a representative `ũ`
continuous on `closure Ω`) satisfy `∫_Ω ∇u · ∇φ + ∫_Ω u φ = ∫_Ω f φ` for all `φ ∈ H^1_0(Ω)` (70).
Then for all `x ∈ Ω`, `min {inf_Γ u, inf_Ω f} ≤ u(x) ≤ max {sup_Γ u, sup_Ω f}` (71): for every
`K₁ ≥ ũ` on `Γ` and `K₂ ≥ f` a.e. on `Ω`, `ũ x ≤ max {K₁, K₂}`, and for every `K₁ ≤ ũ` on `Γ` and
`K₂ ≤ f` a.e. on `Ω`, `min {K₁, K₂} ≤ ũ x`. The backbone's `Elliptic.le_max_of_isWeakSolution`
and `Elliptic.ge_of_ge_frontier` — Stampacchia's truncation `G(u − K')`
(`exists_stampacchiaTruncation`, placed in `H^1(Ω)` by Proposition 9.5 and in `H^1_0(Ω)` by
Theorem 9.17), for both cases
`|Ω| < ∞` and `|Ω| = ∞` of the book's proof. The proof's "proceed as in the proof of Theorem
8.18" refers to the one-dimensional maximum principle, which is Theorem 8.19. -/
theorem theorem_9_27 {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) :
    (∀ K₁ K₂ : ℝ, (∀ x ∈ frontier (Ω : Set 𝔼), ũ x ≤ K₁) →
      (∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), f x ≤ K₂) → ∀ x ∈ Ω, ũ x ≤ max K₁ K₂) ∧
    (∀ K₁ K₂ : ℝ, (∀ x ∈ frontier (Ω : Set 𝔼), K₁ ≤ ũ x) →
      (∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), K₂ ≤ f x) → ∀ x ∈ Ω, min K₁ K₂ ≤ ũ x) := by
  have heq := (forall_laplaceForm_eq_load_iff u f _).1 hu
  refine ⟨fun K₁ K₂ hΓ hf ↦ Elliptic.le_max_of_isWeakSolution heq hũ hc hΓ hf,
    fun K₁ K₂ hΓ hf ↦ ?_⟩
  exact Elliptic.ge_of_ge_frontier heq hũ hc (K := min K₁ K₂)
    (fun x hx ↦ (min_le_left _ _).trans (hΓ x hx))
    (hf.mono fun x hx ↦ (min_le_right _ _).trans hx)

/-- **Theorem 9.27, footnote 35: for `u ∈ H^1_0(Ω)` the assumption `u ∈ C(Ω̄)` can be removed.**
If `u ∈ H^1_0(Ω)` satisfies (70), then `f ≤ K` a.e. with `K ≥ 0` gives `u ≤ K` a.e. on `Ω`, and
`K ≤ f` a.e. with `K ≤ 0` gives `K ≤ u` a.e. on `Ω` — the boundary value `0` of `u` replacing
`sup_Γ u` (resp. `inf_Γ u`). The backbone's `Elliptic.le_of_mem_zero` and
`Elliptic.ge_of_mem_zero`, where the truncations `G(u − K')` lie in `H^1_0(Ω)` by the chain rule
on `W_0^{1,p}`. -/
theorem theorem_9_27_of_mem_zero {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu0 : u ∈ hZeroSpace N Ω)
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x) :
    (∀ K : ℝ, 0 ≤ K → (∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), f x ≤ K) →
      ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), SobolevMultiIndex.fn u x ≤ K) ∧
    (∀ K : ℝ, K ≤ 0 → (∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), K ≤ f x) →
      ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), K ≤ SobolevMultiIndex.fn u x) := by
  have heq := (forall_laplaceForm_eq_load_iff u f _).1 hu
  exact ⟨fun K hK hf ↦ Elliptic.le_of_mem_zero hu0 heq hK hf,
    fun K hK hf ↦ Elliptic.ge_of_mem_zero hu0 heq hK hf⟩

/-! ### Corollary 9.28 -/

/-- **Corollary 9.28, (73).** Let `f ∈ L²(Ω)` and `u ∈ H^1(Ω) ∩ C(Ω̄)` satisfy (70). Then
`[u ≥ 0 on Γ and f ≥ 0 in Ω] ⇒ [u ≥ 0 in Ω]`. The backbone's
`Elliptic.nonneg_of_nonneg_frontier` (Theorem 9.27's lower bound with `K = 0`). -/
theorem corollary_9_28 {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ f x) : ∀ x ∈ Ω, 0 ≤ ũ x :=
  Elliptic.nonneg_of_nonneg_frontier ((forall_laplaceForm_eq_load_iff u f _).1 hu) hũ hc hΓ hf

/-- **Corollary 9.28, (74).** Under the hypotheses of Corollary 9.28,
`‖u‖_{L^∞(Ω)} ≤ max {‖u‖_{L^∞(Γ)}, ‖f‖_{L^∞(Ω)}}`: if `|ũ| ≤ K₁` on `Γ` and `|f| ≤ K₂` a.e. on `Ω`
then `|ũ| ≤ max {K₁, K₂}` on `Ω`. The backbone's `Elliptic.abs_le_max_of_isWeakSolution`
(Theorem 9.27's two bounds). -/
theorem corollary_9_28_bound {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) {K₁ K₂ : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), |ũ x| ≤ K₁)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), |f x| ≤ K₂) : ∀ x ∈ Ω, |ũ x| ≤ max K₁ K₂ :=
  Elliptic.abs_le_max_of_isWeakSolution ((forall_laplaceForm_eq_load_iff u f _).1 hu) hũ hc hΓ hf

/-- **Corollary 9.28, "in particular, if `f = 0` in `Ω` then `‖u‖_{L^∞(Ω)} ≤ ‖u‖_{L^∞(Γ)}`"**:
for `f = 0`, `|ũ| ≤ K` on `Γ` (`K ≥ 0`) gives `|ũ| ≤ K` on `Ω`. The backbone's
`Elliptic.abs_le_of_load_eq_zero`. -/
theorem corollary_9_28_zero_load {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) {K : ℝ} (hK : 0 ≤ K)
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), |ũ x| ≤ K) : ∀ x ∈ Ω, |ũ x| ≤ K :=
  Elliptic.abs_le_of_load_eq_zero ((forall_laplaceForm_eq_load_iff u 0 _).1 hu) hũ hc hK hΓ

/-- **Corollary 9.28, "in particular, if `u = 0` on `Γ` then `‖u‖_{L^∞(Ω)} ≤ ‖f‖_{L^∞(Ω)}`"**:
for `ũ = 0` on `Γ`, `|f| ≤ K` a.e. on `Ω` (`K ≥ 0`) gives `|ũ| ≤ K` on `Ω`. The backbone's
`Elliptic.abs_le_of_eqOn_zero_frontier`. -/
theorem corollary_9_28_zero_boundary {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (hΓ : EqOn ũ 0 (frontier (Ω : Set 𝔼))) {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), |f x| ≤ K) : ∀ x ∈ Ω, |ũ x| ≤ K :=
  Elliptic.abs_le_of_eqOn_zero_frontier ((forall_laplaceForm_eq_load_iff u f _).1 hu) hũ hc hΓ hK
    hf

/-! ### Remark 27: the classical proof -/

/-- **Remark 27, the classical proof of Theorem 9.27 for the Laplacian.** If `Ω` is bounded and
`u ∈ C(Ω̄) ∩ C²(Ω)` is a classical solution of `-Δu + u = f` in `Ω` (76) with `f ≤ K` on `Ω` and
`u ≤ K` on `Γ`, then `u ≤ K` on `Ω`: let `x₀ ∈ Ω̄` be a point where `u` attains its maximum on
`Ω̄`; if `x₀ ∈ Γ` then `u(x₀) ≤ sup_Γ u ≤ K`, and if `x₀ ∈ Ω` then `∇u(x₀) = 0` and
`∂²u/∂xᵢ²(x₀) ≤ 0`, so `Δu(x₀) ≤ 0` and `u(x₀) = f(x₀) + Δu(x₀) ≤ f(x₀) ≤ K`. The backbone's
`Elliptic.le_of_classical_laplacian` (`IsLocalMax.laplacian_nonpos`). -/
theorem remark_9_27 (hb : Bornology.IsBounded (Ω : Set 𝔼)) {u f : 𝔼 → ℝ}
    (hc : ContinuousOn u (closure (Ω : Set 𝔼))) (hu : ContDiffOn ℝ 2 u Ω)
    (heq : ∀ x ∈ Ω, -Δ u x + u x = f x) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), u x ≤ K)
    (hf : ∀ x ∈ Ω, f x ≤ K) : ∀ x ∈ Ω, u x ≤ K :=
  Elliptic.le_of_classical_laplacian hb hc hu heq hΓ hf

/-- **Remark 27, the general operator.** "This method has the advantage that it applies to general
second-order elliptic equations": the conclusion of Theorem 9.27 holds for classical solutions
`u ∈ C(Ω̄) ∩ C²(Ω)` of `-∑ᵢⱼ ∂ⱼ(a_ij ∂ᵢu) + ∑ᵢ a_i ∂ᵢu + u = f` in a bounded `Ω` (77), with
`a_ij ∈ C¹(Ω)` symmetric satisfying the ellipticity condition (36) and any `a_i` (their
continuity plays no role, the first-order term vanishing at a critical point): `u ≤ K` on `Γ`
and `f ≤ K` on `Ω` give `u ≤ K` on `Ω`. At an interior maximum `x₀`, `∇u(x₀) = 0` and
`∑ a_ij(x₀) ∂ᵢ∂ⱼu(x₀) ≤ 0` (78) — "by a change of coordinates one can reduce this to the case in
which the matrix `a_ij(x₀)` is diagonal" — so `u(x₀) = f(x₀) + ∑ a_ij(x₀) ∂ᵢ∂ⱼu(x₀) ≤ f(x₀) ≤ K`.
The backbone's `Elliptic.le_of_classical` (with the square root of `a(x₀)` in place of its
diagonalization); the remark's last sentence, the same for *weak* solutions of (77)
(Gilbarg–Trudinger), is not restated. -/
theorem remark_9_27_general (hb : Bornology.IsBounded (Ω : Set 𝔼)) {u f : 𝔼 → ℝ}
    (hc : ContinuousOn u (closure (Ω : Set 𝔼))) (hu : ContDiffOn ℝ 2 u Ω)
    {a : Fin N → Fin N → 𝔼 → ℝ} (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (hsymm : ∀ i j, a i j = a j i) {α : ℝ} (hell : ellipticityCondition Ω a α)
    {b : Fin N → 𝔼 → ℝ}
    (heq : ∀ x ∈ Ω, -(∑ i, ∑ j, fderiv ℝ (fun y ↦ a i j y * fderiv ℝ u y
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1))
      + (∑ i, b i x * fderiv ℝ u x (EuclideanSpace.single i 1)) + u x = f x)
    {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), u x ≤ K) (hf : ∀ x ∈ Ω, f x ≤ K) :
    ∀ x ∈ Ω, u x ≤ K :=
  Elliptic.le_of_classical hb hc hu (fun i j ↦ (ha i j).differentiableOn one_ne_zero) hsymm
    (fun x hx ξ ↦ (mul_nonneg hell.1.le (sq_nonneg _)).trans (hell.2 x hx ξ)) heq hΓ hf

/-! ### Proposition 9.29, the drift-free case -/

variable {A : Fin N → Fin N → Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))}
  {a₀ : Lp ℝ ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))))} {α : ℝ}

/-- **Proposition 9.29, (79), in the case `a_i ≡ 0` the book proves.** Suppose that the functions
`a_ij ∈ L^∞(Ω)` satisfy the ellipticity condition (36) (`Elliptic.IsUniformlyElliptic`, almost
everywhere) and that `a₀ ∈ L^∞(Ω)` with `a₀ ≥ 0` in `Ω`. Let `f ∈ L²(Ω)` and
`u ∈ H^1(Ω) ∩ C(Ω̄)` be such that `∫_Ω ∑ᵢⱼ a_ij ∂ᵢu ∂ⱼφ + ∫_Ω a₀ u φ = ∫_Ω f φ` for all
`φ ∈ H^1_0(Ω)` (78 with `a_i = 0`). Then `[u ≥ 0 on Γ and f ≥ 0 in Ω] ⇒ [u ≥ 0 in Ω]`. The
backbone's `Elliptic.nonneg_of_nonneg_frontier_general_zero_drift`: the book's proof of (79')
tests (78) with `φ = G(u)`, uses ellipticity to get `∫ |∇u|² G'(u) ≤ 0`, and the auxiliary
`H(t) = ∫₀ᵗ √G'` with footnote 39 (`SobolevMultiIndexZero.eq_zero_of_gradient_eq_zero`: a
`W_0^{1,p}` function with zero gradient vanishes, by Proposition 9.18 and Remark 7). Needs
`N ≥ 1`. -/
theorem proposition_9_29_zero_drift (hN : N ≠ 0) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ a₀ x)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), 0 ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ f x) : ∀ x ∈ Ω, 0 ≤ ũ x :=
  Elliptic.nonneg_of_nonneg_frontier_general_zero_drift hN hA ha₀
    ((forall_generalForm_zero_drift_eq_load_iff A a₀ u f).1 hu) hũ hc hΓ hf

/-- **Proposition 9.29, (79), footnote 38: for `u ∈ H^1_0(Ω)` the assumption `u ∈ C(Ω̄)` can be
removed** (drift-free case): `f ≥ 0` a.e. in `Ω` gives `u ≥ 0` a.e. in `Ω`. The backbone's
`Elliptic.nonneg_of_mem_zero_general_zero_drift`. -/
theorem proposition_9_29_zero_drift_of_mem_zero (hN : N ≠ 0)
    (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (ha₀ : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ a₀ x)
    {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω} (hu0 : u ∈ hZeroSpace N Ω)
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + ∫ x in (Ω : Set 𝔼), a₀ x * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ f x) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ SobolevMultiIndex.fn u x :=
  Elliptic.nonneg_of_mem_zero_general_zero_drift hN hA ha₀ hu0
    ((forall_generalForm_zero_drift_eq_load_iff A a₀ u f).1 hu) hf

/-- **Proposition 9.29, (80), in the case `a_i ≡ 0`.** Suppose moreover that `a₀ ≡ 0` and that
`Ω` is bounded. Then `[f ≥ 0 in Ω] ⇒ [u ≥ inf_Γ u in Ω]`: `u ≥ K` on `Γ` gives `u ≥ K` in `Ω`.
The backbone's `Elliptic.ge_of_ge_frontier_general_zero_drift`, from (79) applied to `u − K`,
which satisfies (78) because `a₀ = 0` and the constant `K` is in `H^1(Ω)` for bounded `Ω`. -/
theorem proposition_9_29_inf_zero_drift (hN : N ≠ 0) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))}
    {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) {K : ℝ} (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), K ≤ ũ x)
    (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), 0 ≤ f x) : ∀ x ∈ Ω, K ≤ ũ x :=
  Elliptic.ge_of_ge_frontier_general_zero_drift hN hA hb.measure_lt_top.ne
    ((forall_generalForm_zero_drift_eq_load_iff A 0 u f).1 hu) hũ hc hΓ hf

/-- **Proposition 9.29, (81), in the case `a_i ≡ 0`.** If `a₀ ≡ 0`, `Ω` is bounded and `f = 0` in
`Ω`, then `inf_Γ u ≤ u ≤ sup_Γ u` in `Ω`: `K₁ ≤ u ≤ K₂` on `Γ` gives `K₁ ≤ u ≤ K₂` in `Ω` — (80)
for `u` and for `−u`. The backbone's `Elliptic.mem_Icc_of_frontier_general_zero_drift`. -/
theorem proposition_9_29_sup_inf_zero_drift (hN : N ≠ 0) (hA : Elliptic.IsUniformlyElliptic Ω A α)
    (hb : Bornology.IsBounded (Ω : Set 𝔼)) {u : hSpace N Ω}
    (hu : ∀ φ ∈ hZeroSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, ∑ j, A i j x * partialDeriv u i x * partialDeriv φ j x)
        + ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ ⊤ (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), (0 : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))) x
          * SobolevMultiIndex.fn φ x)
    {ũ : 𝔼 → ℝ} (hũ : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) {K₁ K₂ : ℝ}
    (hΓ : ∀ x ∈ frontier (Ω : Set 𝔼), K₁ ≤ ũ x ∧ ũ x ≤ K₂) :
    ∀ x ∈ Ω, K₁ ≤ ũ x ∧ ũ x ≤ K₂ :=
  Elliptic.mem_Icc_of_frontier_general_zero_drift hN hA hb.measure_lt_top.ne
    ((forall_generalForm_zero_drift_eq_load_iff A 0 u 0).1 hu) hũ hc hΓ

/-! ### Proposition 9.30 -/

/-- **Proposition 9.30 (maximum principle for the Neumann problem).** Let `f ∈ L²(Ω)` and
`u ∈ H^1(Ω)` be such that `∫_Ω ∇u · ∇φ + ∫_Ω u φ = ∫_Ω f φ` for all `φ ∈ H^1(Ω)`. Then
`inf_Ω f ≤ u(x) ≤ sup_Ω f` for a.e. `x ∈ Ω` (82): if `K₁ ≤ f ≤ K₂` a.e. on `Ω` then
`K₁ ≤ u ≤ K₂` a.e. on `Ω`. The backbone's `Elliptic.le_of_neumann` and `Elliptic.ge_of_neumann`
(the truncation engine with the test space `H^1(Ω)`; "analogous to the proof of
Theorem 9.27"). -/
theorem proposition_9_30 {f : Lp ℝ 2 (volume.restrict (Ω : Set 𝔼))} {u : hSpace N Ω}
    (hu : ∀ φ : hSpace N Ω,
      (∫ x in (Ω : Set 𝔼), ∑ i, partialDeriv u i x * partialDeriv φ i x)
        + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x * SobolevMultiIndex.fn φ x
        = ∫ x in (Ω : Set 𝔼), f x * SobolevMultiIndex.fn φ x)
    {K₁ K₂ : ℝ} (hf : ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)), K₁ ≤ f x ∧ f x ≤ K₂) :
    ∀ᵐ x ∂(volume.restrict (Ω : Set 𝔼)),
      K₁ ≤ SobolevMultiIndex.fn u x ∧ SobolevMultiIndex.fn u x ≤ K₂ := by
  have heq := (forall_laplaceForm_eq_load_iff u f ⊤).1 fun φ _ ↦ hu φ
  have h1 := Elliptic.ge_of_neumann (fun φ ↦ heq φ Submodule.mem_top) (hf.mono fun x hx ↦ hx.1)
  have h2 := Elliptic.le_of_neumann (fun φ ↦ heq φ Submodule.mem_top) (hf.mono fun x hx ↦ hx.2)
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩

end MaximumPrinciple

end Brezis.Chapter09
