/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Boundary.Divergence
import Numlib.Analysis.Sobolev.Boundary.GraphMeasure
import Numlib.Analysis.Sobolev.Boundary.Trace
import Numlib.Analysis.Sobolev.Compactness

/-!
# The divergence theorem, the boundary data and the trace of a bounded $C^1$ domain

Let $\Omega \subseteq \mathbb{R}^N$, $N = d + 1$, be a bounded $C^1$ domain in the graph sense
(`IsContDiffDomain 1 Ω`), with the surface measure $\sigma$ and the outward unit normal $\nu$ of
`Numlib.Analysis.Sobolev.Boundary.GraphMeasure`. This module proves the divergence theorem
$$\int_\Omega \operatorname{div} F \, dx = \int_{\partial\Omega} \langle F, \nu \rangle \, d\sigma
  \qquad \text{for } F \in C^1(\overline{\Omega}),$$
and so makes $(\sigma, \nu)$ a `BoundaryData` of $\Omega$. It constructs a transversal field, and
with the density theorems of `Numlib.Analysis.Sobolev.Boundary.Density` it obtains the trace family
of `Numlib.Analysis.Sobolev.Boundary.Trace`: the trace $W^{1,p}(\Omega) \to L^p(\sigma)$ for
$1 \le p < \infty$ and Green's formula. With Rellich's theorem
(`Numlib.Analysis.Sobolev.Compactness`), the trace is a compact operator for $1 < p < \infty$.
Through `IsContDiffChartDomain.isContDiffDomain`, the same holds for a bounded $C^1$ domain in the
chart sense of [brezis2011functional], §9.2.

The results are those of [han2009theoretical], §7.3 (Theorem 7.3.10) and §7.6, of
[grisvard2011elliptic], Theorems 1.5.1.3 and 1.5.3.1, of Nečas, *Direct Methods in the Theory of
Elliptic Equations*, Chapter 2, §4, and of [brezis2011functional], §9.5, Example 4, and Comments on
Chapter 9. The surface modules use this module for Theorem 7.3.10, Proposition 7.6.1 and Examples
11.1.2 to 11.3.11 of [han2009theoretical] on a $C^1$ domain, and for Example 4 of §9.5 and the
Neumann boundary condition of Theorem 9.26 of [brezis2011functional].

## Main results

* `IsBoundaryGraphAt.integral_div_eq_graphMeasure`: the divergence theorem on one graph chart, with
  the surface measure of the chart.
* `GraphAtlas.integral_div_eq`, `IsContDiffDomain.integral_div_eq`: the divergence theorem on a
  bounded $C^1$ domain.
* `IsContDiffDomain.boundaryData`, `IsContDiffChartDomain.boundaryData`: the boundary data of a
  bounded $C^1$ domain.
* `IsContDiffDomain.exists_transversalField`, `IsContDiffDomain.hasTransversalField`: a $C^1$ field
  $w$ with compact support and $\langle w, \nu \rangle \ge 1$ almost everywhere on $\partial\Omega$.
* `IsContDiffDomain.traceFamily`, `IsContDiffDomain.traceL`, `IsContDiffDomain.green`: the trace
  theorem and Green's formula on a bounded $C^1$ domain.
* `IsContDiffDomain.isCompactOperator_traceL`: the trace is a compact operator for $1 < p < \infty$.

## Proof outline

Take a graph atlas of $\Omega$ with a partition of unity $\theta_0 + \sum_i \theta_i = 1$. Then
$F = \theta_0 F + \sum_i \theta_i F$ on $\Omega$, and the divergence is additive on differentiable
fields. The interior piece $\theta_0 F$ vanishes near $\partial\Omega$. The compact set
$\operatorname{tsupport} \theta_0 \cap \overline{\Omega}$ lies in $\Omega$, so it carries a smooth
cut-off $\chi$ with support in $\Omega$. The field $H = (\chi \theta_0) F$ is a $C^1$ field on all
of $\mathbb{R}^N$ with compact support, it equals $\theta_0 F$ on $\Omega$, and
$\operatorname{div} H = 0$ outside $\Omega$, so $\int_\Omega \operatorname{div}(\theta_0 F) = \int
\operatorname{div} H = 0$. Each chart piece $\theta_i F$ has support in its chart ball, so the local
divergence theorem of `Numlib.Analysis.Sobolev.Boundary.Divergence` applies to it. In terms of the
chart measure $\sigma_i$ it reads $\int_\Omega \operatorname{div}(\theta_i F) = \int \langle
\theta_i F, \nu_i \rangle \, d\sigma_i$, because the density $\sqrt{1 + |\nabla g_i|^2}$ of
$\sigma_i$ cancels the normalization of the chart normal $\nu_i$. The measure $\sigma_i$ is carried
by $\partial\Omega \cap B(x_i, r_i)$, where $\nu_i$ is the normal of the atlas. The atlas measure
$\sigma = \sum_i \theta_i \sigma_i$ recombines the pieces. The divergence of a field in
$C^1(\overline{\Omega})$ is integrable on $\Omega$, because its derivative is bounded on the bounded
set $\Omega$.

The transversal field is $w = c \sum_i \theta_i T_i^{-1}(-e_N)$, the partition of unity applied to
the downward directions of the charts. In the frame $T_i$ the outward normal is
$(\nabla g_i, -1)/\sqrt{1 + |\nabla g_i|^2}$, so $\langle T_i^{-1}(-e_N), \nu \rangle = 1/\sqrt{1 +
|\nabla g_i|^2} \ge 1/c$ on $\partial\Omega \cap B(x_i, r_i)$, where $c$ bounds the densities on the
bounded parameter domains. Hence $\langle w, \nu \rangle \ge \sum_i \theta_i = 1$ on
$\partial\Omega$.

## Implementation notes

* The divergence theorem is stated for $F \in C^1(\overline{\Omega})$, that is,
  `ContinuousOn F (closure Ω)` and `ContDiffOnClosure ℝ 1 F Ω`
  (`Numlib.Analysis.Calculus.ContDiffOnClosure`). This is the regularity of the Green formulas of
  the books. The case $F \in C^1(\mathbb{R}^N)$ is the corollary
  `BoundaryData.integral_div_eq_of_contDiff`.
* The proof uses no Piola identity, no area formula and no Hausdorff measure.
* The divergence theorem is proved for every graph atlas (`GraphAtlas.integral_div_eq`) and then
  specialized to the atlas that defines $\sigma$ and $\nu$.

## Not formalized

Korn's second inequality and the mixed displacement–traction problem of linear elasticity (Nečas and
Hlaváček; Duvaut and Lions; [han2009theoretical], §8.5, the remark on $V$-ellipticity after
(8.5.15)) are not formalized. The surface module `NumlibSurface.AtkinsonHan.Chapter08.Section05`
records the same gap from the side of elasticity. Three statements are missing.

* **The space $[H^1(\Omega)]^N$ and the mixed space $V$.** The space $[H^1(\Omega)]^N$ as a Hilbert
  space, and the mixed space $V$ of (8.5.13) of [han2009theoretical]. The type would be `PiLp 2 fun
  _ : Fin N ↦ SobolevEuclidean N 1 2 Ω`, the $\ell^2$ product of $N$ copies of $H^1(\Omega)$ with
  $\|v\|^2 = \sum_i \|v_i\|^2$. On it, the partial derivatives $v \mapsto \partial_j v_i$ and the
  linearized strain $\varepsilon(v)_{ij} = \frac12 (\partial_j v_i + \partial_i v_j)$ are continuous
  linear maps into $L^2(\Omega)$; they extend `SobolevEuclideanZeroVec.partialL` and
  `SobolevEuclideanZeroVec.strainL` of `Numlib.Analysis.Sobolev.Korn` from the subspace
  $[H^1_0(\Omega)]^N$. The trace is taken componentwise with `IsContDiffDomain.traceFamily`, and $V$
  is the subspace of the fields whose trace vanishes $\sigma$-almost everywhere on a
  measurable $\Gamma_D \subseteq \partial\Omega$; it is closed because the trace is continuous.
  Everything that this item needs exists; it is not written because the two theorems below are
  missing.
* **Korn's second inequality.** On a bounded $C^1$ domain $\Omega$ there is a $C$ with
  $\|v\|_{H^1}^2 \le C (\|v\|_{L^2}^2 + \|\varepsilon(v)\|_{L^2}^2)$ for every
  $v \in [H^1(\Omega)]^N$. On $[H^1_0(\Omega)]^N$ the sharper inequality without the $L^2$ term is
  `SobolevEuclideanZeroVec.korn_first`, which needs no regularity of $\Omega$. On $[H^1(\Omega)]^N$
  the boundary terms of its two integrations by parts do not vanish. The standard proof (Duvaut and
  Lions, Nečas) writes $\partial_j \partial_k v_i = \partial_j \varepsilon_{ik} + \partial_k
  \varepsilon_{ij} - \partial_i \varepsilon_{jk}$ in $H^{-1}(\Omega)$ and uses **Lions's lemma**: on
  a bounded Lipschitz domain, a distribution $f$ with $f \in H^{-1}(\Omega)$ and
  $\nabla f \in H^{-1}(\Omega)^N$ lies in $L^2(\Omega)$, with $\|f\|_{L^2} \le C (\|f\|_{H^{-1}} +
  \|\nabla f\|_{H^{-1}})$. Lions's lemma is proved with a right inverse of the divergence
  (Bogovskiĭ) or with the Nečas inequality $\|f\|_{L^2} \le C \|\nabla f\|_{H^{-1}}$ on $L^2_0$, and
  neither is in Mathlib or in this library. The alternatives are not easier: the integral
  representation of Kondratiev and Oleĭnik works only for star-shaped domains, and the Fourier proof
  on $\mathbb{R}^N$ needs a $C^1$ extension operator that commutes with $\varepsilon$, which does
  not exist. The space $H^{-1}(\Omega)$ as the dual of $H^1_0(\Omega)$ with its norm is available
  (`SobolevEuclideanZero.exists_dual_repr` of `Numlib.Analysis.Sobolev.Zero`). The trace is not what
  is missing: with `IsContDiffDomain.traceFamily` every statement of this section can be stated.
* **$V$-ellipticity of the elasticity form.** Let $\Omega$ be bounded, $C^1$ and connected, and let
  $\Gamma_D \subseteq \partial\Omega$ be measurable with $\sigma(\Gamma_D) > 0$. Then there is a $C$
  with $\|v\|_{H^1}^2 \le C \|\varepsilon(v)\|_{L^2}^2$ for every $v \in V$. This is the missing
  step of Theorem 8.5.1 of [han2009theoretical]. It follows from Korn's second inequality by
  contradiction. A sequence $v_n \in V$ with $\|v_n\| = 1$ and $\varepsilon(v_n) \to 0$ has a
  subsequence that converges in $L^2$ by Rellich's theorem on the extension domain
  (`SobolevEuclidean.isCompactEmbedding_fnL`), hence in $H^1$ by Korn's second inequality, to some
  $v \in V$ with $\|v\| = 1$ and $\varepsilon(v) = 0$. On a connected domain the kernel of
  $\varepsilon$ consists of the infinitesimal rigid motions $x \mapsto a + Wx$ with $W$ skew: the
  identity above makes every second derivative vanish, and the result of
  `Numlib.Analysis.Sobolev.DenyLions` that $|u|_{2,p} = 0$ forces a polynomial of degree at most $1$
  makes $v$ affine. The last step needs care. An affine map that vanishes on a set of positive
  surface measure need not be zero, because its zero set can be a hyperplane, and a $C^1$ boundary
  can contain a flat face of positive measure in a hyperplane. The step holds because $W$ is skew:
  the zero set of a nonzero infinitesimal rigid motion is an affine subspace of even codimension at
  least $2$ (a point for $N = 2$, a line for $N = 3$), and an affine subspace of dimension at most
  $N - 2$ is $\sigma$-null on a $C^1$ hypersurface. This nullity follows from
  `IsContDiffDomain.boundaryMeasure_restrict_ball`, since the preimage of such a subspace under a
  graph parametrization over $\mathbb{R}^{N-1}$ is Lebesgue-null. This statement depends only on
  Korn's second inequality.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace NNReal Topology

noncomputable section

/-!
### The interior piece of the divergence theorem

If $\theta$ vanishes near $\partial\Omega$, then $\int_\Omega \operatorname{div}(\theta F) = 0$.
-/

/-- **The interior piece of the divergence theorem.** Let $\Omega \subseteq \mathbb{R}^N$ be open
and bounded, let $\theta \colon \mathbb{R}^N \to \mathbb{R}$ be $C^1$ with
$\operatorname{tsupport} \theta$ disjoint from $\partial\Omega$, and let
$F \colon \mathbb{R}^N \to \mathbb{R}^N$ be $C^1$ on $\Omega$. Then
$$\int_\Omega \operatorname{div}(\theta F) \, dx = 0.$$

The compact set $K = \operatorname{tsupport} \theta \cap \overline{\Omega}$ lies in $\Omega$
(`inter_closure_subset_of_disjoint_frontier`). A smooth cut-off $\chi$ equal to $1$ on $K$ with
support in $\Omega$ (`IsCompact.exists_contDiff_eqOn_one`) makes $H = (\chi \theta) F$ a $C^1$
field on $\mathbb{R}^N$ with compact support. It equals $\theta F$ on $\Omega$ and has
$\operatorname{div} H = 0$ outside $\Omega$, so $\int_\Omega \operatorname{div}(\theta F) = \int
\operatorname{div} H = 0$ by `EuclideanSpace.integral_div_eq_zero_of_hasCompactSupport`. -/
theorem EuclideanSpace.integral_div_smul_eq_zero_of_disjoint_tsupport_frontier {N : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin N))} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {θ : EuclideanSpace ℝ (Fin N) → ℝ} (hθ : ContDiff ℝ 1 θ)
    (hθΩ : Disjoint (tsupport θ) (frontier Ω))
    {F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} (hF : ContDiffOn ℝ 1 F Ω) :
    ∫ y in Ω, EuclideanSpace.div (fun y ↦ θ y • F y) y = 0 := by
  have hK : IsCompact (tsupport θ ∩ closure Ω) :=
    (isClosed_tsupport θ).isCompact_inter_closure_of_isBounded hb
  have hKΩ : tsupport θ ∩ closure Ω ⊆ Ω := inter_closure_subset_of_disjoint_frontier hΩ hθΩ
  obtain ⟨χ, hχ, hχ1, hχs, -⟩ := hK.exists_contDiff_eqOn_one hΩ hKΩ
  set H : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
    fun y ↦ (χ y * θ y) • F y with hHdef
  have hHeq : ∀ y ∈ Ω, H y = θ y • F y := fun y hy ↦ by
    by_cases hyθ : y ∈ tsupport θ
    · simp [hHdef, hχ1 ⟨hyθ, subset_closure hy⟩]
    · simp [hHdef, image_eq_zero_of_notMem_tsupport hyθ]
  have hHs : tsupport H ⊆ tsupport χ :=
    (tsupport_smul_subset_left _ _).trans tsupport_mul_subset_left
  have hHd : ContDiff ℝ 1 H := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Ω
    · exact ((hχ.of_le (by simp)).contDiffAt.mul hθ.contDiffAt).smul
        (hF.contDiffAt (hΩ.mem_nhds hy))
    · have hyχ : y ∉ tsupport χ := fun h ↦ hy (hχs h)
      have : H =ᶠ[𝓝 y] fun _ ↦ 0 := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hyχ] with z hz
        simp [hHdef, image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq this
  have hHc : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact hb.isCompact_closure
      ((subset_tsupport H).trans (hHs.trans (hχs.trans subset_closure)))
  have hdiv0 : ∀ y, y ∉ Ω → EuclideanSpace.div H y = 0 := fun y hy ↦ by
    have : fderiv ℝ H y = 0 :=
      fderiv_of_notMem_tsupport ℝ fun h ↦ hy (hχs (hHs h))
    simp [EuclideanSpace.div, this]
  calc ∫ y in Ω, EuclideanSpace.div (fun y ↦ θ y • F y) y
      = ∫ y in Ω, EuclideanSpace.div H y := by
        refine setIntegral_congr_fun hΩ.measurableSet fun y hy ↦ ?_
        have : (fun y ↦ θ y • F y) =ᶠ[𝓝 y] H := by
          filter_upwards [hΩ.mem_nhds hy] with z hz
          exact (hHeq z hz).symm
        simp only [EuclideanSpace.div, this.fderiv_eq]
    _ = ∫ y, EuclideanSpace.div H y :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ hdiv0 y hy
    _ = 0 :=
        EuclideanSpace.integral_div_eq_zero_of_hasCompactSupport (hHd.differentiable one_ne_zero)
          hHc ((hHd.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport
            (hHc.fderiv (𝕜 := ℝ)))

/-! ### The local divergence theorem in surface-measure form -/

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

/-- **The divergence theorem on a graph chart, with the surface measure.** Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be open, let $T$ be a rigid motion of $\mathbb{R}^{d+1}$,
let $g \colon \mathbb{R}^d \to \mathbb{R}$ be $C^1$, and assume that
$$\Omega \cap B(x_0, r) = B(x_0, r) \cap T^{-1}(\{y : g(y') < y_N\}).$$
Let $F \in C^1(\overline{\Omega})$ with $\operatorname{tsupport} F \subseteq B(x_0, r)$. Then
$$\int_\Omega \operatorname{div} F \, dx = \int \langle F, \nu_{T,g} \rangle \, d\sigma_{T,g},$$
where $\nu_{T,g}$ is the chart normal `EuclideanSpace.graphNormal T g` and $\sigma_{T,g}$ is the
chart measure `EuclideanSpace.graphMeasure T g` on the parameter domain
`EuclideanSpace.graphDomain T g x₀ r`.

The right side of `IsBoundaryGraphAt.integral_div_eq_of_tsupport_subset` is $\int \langle
F(\gamma(x')), T^{-1}(\nabla g(x'), -1) \rangle \, dx'$, where $\gamma$ is the graph
parametrization `EuclideanSpace.graphParam T g`. By `EuclideanSpace.integral_graphMeasure`, the
surface integral is $\int \sqrt{1 + |\nabla g|^2} \, \langle F(\gamma(x')),
\nu_{T,g}(\gamma(x')) \rangle \, dx'$ over the parameter domain, and the density cancels the
normalization of the normal. The integrand vanishes outside the parameter domain, because $F$
vanishes outside the ball. -/
theorem IsBoundaryGraphAt.integral_div_eq_graphMeasure {g : 𝔼' → ℝ} {Ω : Set 𝔼} (hΩ : IsOpen Ω)
    {x₀ : 𝔼} {r : ℝ} (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) (hg : ContDiff ℝ 1 g)
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    {F : 𝔼 → 𝔼} (hFs : tsupport F ⊆ Metric.ball x₀ r) (hF₀ : ContinuousOn F (closure Ω))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ y in Ω, EuclideanSpace.div F y
      = ∫ x, ⟪F x, EuclideanSpace.graphNormal T g x⟫_ℝ
          ∂(EuclideanSpace.graphMeasure T g (EuclideanSpace.graphDomain T g x₀ r)) := by
  set μ := EuclideanSpace.graphMeasure T g (EuclideanSpace.graphDomain T g x₀ r) with hμdef
  -- the graph measure is carried by `∂Ω ∩ B ⊆ closure Ω`, where `F` is continuous
  have hμc : ∀ᵐ x ∂μ, x ∈ closure Ω := by
    filter_upwards [EuclideanSpace.ae_mem_image_graphMeasure (T := T) hg.continuous
      (EuclideanSpace.measurableSet_graphDomain hg.continuous x₀ r)] with x hx
    rw [IsBoundaryGraphAt.graphParam_image_graphDomain hg.continuous h] at hx
    exact frontier_subset_closure hx.1
  have hFm : AEStronglyMeasurable F μ := by
    have := hF₀.aestronglyMeasurable (μ := μ) isClosed_closure.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hμc] at this
  have hm : AEStronglyMeasurable (fun x ↦ ⟪F x, EuclideanSpace.graphNormal T g x⟫_ℝ) μ :=
    hFm.inner (EuclideanSpace.continuous_graphNormal hg).aestronglyMeasurable
  rw [hμdef, EuclideanSpace.integral_graphMeasure hg _ hm,
    IsBoundaryGraphAt.integral_div_eq_of_tsupport_subset hΩ T hg h hFs hF₀ hF₁]
  -- the integrand vanishes off the parameter domain
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x' hx' ↦ ?_]
  · refine integral_congr_ae (Eventually.of_forall fun x' ↦ ?_)
    simp only [EuclideanSpace.graphNormal, EuclideanSpace.init_apply_graphParam,
      real_inner_smul_right, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (EuclideanSpace.graphDensity_ne_zero x'), one_mul]
    rfl
  · have : F (EuclideanSpace.graphParam T g x') = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem ↦ hx' (hFs hmem)
    rw [this, inner_zero_left, smul_zero]

/-! ### The divergence theorem for an atlas -/

namespace GraphAtlas

variable {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} (a : GraphAtlas Ω)

/-- **The chart piece of the divergence theorem.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open
with a graph atlas, let $\theta_i$ be the partition function of the $i$-th chart, $\sigma_i$ the
measure of the $i$-th chart, and $\nu$ the normal of the atlas. For
$F \in C^1(\overline{\Omega})$,
$$\int_\Omega \operatorname{div}(\theta_i F) \, dx = \int \theta_i \langle F, \nu \rangle \,
  d\sigma_i.$$

The piece $\theta_i F$ has support in the chart ball, so
`IsBoundaryGraphAt.integral_div_eq_graphMeasure` applies. The measure $\sigma_i$ is carried by
$\partial\Omega \cap B(x_i, r_i)$, where the chart normal is the normal of the atlas
(`GraphAtlas.normal_eq_graphNormal`). -/
theorem integral_div_smul_θ_eq (hΩ : IsOpen Ω) {F : 𝔼 → 𝔼} (hF₀ : ContinuousOn F (closure Ω))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) (i : Fin a.k) :
    ∫ y in Ω, EuclideanSpace.div (fun y ↦ a.θ i y • F y) y
      = ∫ x, a.θ i x • ⟪F x, a.normal x⟫_ℝ ∂(a.localMeasure i) := by
  have hGs : tsupport (fun y ↦ a.θ i y • F y) ⊆ Metric.ball (a.x i) (a.r i) :=
    (tsupport_smul_subset_left _ _).trans (a.tsupport_θ_subset i)
  have hG₀ : ContinuousOn (fun y ↦ a.θ i y • F y) (closure Ω) :=
    (a.contDiff_θ i).continuous.continuousOn.smul hF₀
  have hG₁ : ContDiffOnClosure ℝ 1 (fun y ↦ a.θ i y • F y) Ω :=
    (((a.contDiff_θ i).of_le (by simp)).contDiffOn.contDiffOnClosure hΩ).smul hΩ hF₁
  rw [IsBoundaryGraphAt.integral_div_eq_graphMeasure hΩ (a.T i) (a.contDiff_g i)
    (a.inter_ball_eq i) hGs hG₀ hG₁, a.localMeasure_eq]
  refine integral_congr_ae ?_
  filter_upwards [EuclideanSpace.ae_mem_image_graphMeasure (T := a.T i) (a.contDiff_g i).continuous
    (EuclideanSpace.measurableSet_graphDomain (a.contDiff_g i).continuous (a.x i) (a.r i))]
    with x hx
  rw [IsBoundaryGraphAt.graphParam_image_graphDomain (a.contDiff_g i).continuous
    (a.inter_ball_eq i)] at hx
  rw [a.normal_eq_graphNormal hx.1 hx.2, real_inner_smul_left, smul_eq_mul]

/-- **The divergence theorem for a graph atlas.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open
and bounded, with a graph atlas whose measure is $\sigma$ and whose normal is $\nu$. For
$F \in C^1(\overline{\Omega})$,
$$\int_\Omega \operatorname{div} F \, dx = \int \langle F, \nu \rangle \, d\sigma.$$

The partition of unity splits $F = \theta_0 F + \sum_i \theta_i F$ on $\Omega$. The interior
piece integrates to zero
(`EuclideanSpace.integral_div_smul_eq_zero_of_disjoint_tsupport_frontier`), each chart piece is
$\int \theta_i \langle F, \nu \rangle \, d\sigma_i$ (`GraphAtlas.integral_div_smul_θ_eq`), and
the atlas measure recombines the pieces (`GraphAtlas.integral_measure_eq_sum`). -/
theorem integral_div_eq (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {F : 𝔼 → 𝔼}
    (hF₀ : ContinuousOn F (closure Ω)) (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ y in Ω, EuclideanSpace.div F y = ∫ x, ⟪F x, a.normal x⟫_ℝ ∂a.measure := by
  have hθ₁ : ∀ i, ContDiffOnClosure ℝ 1 (a.θ i) Ω := fun i ↦
    ((a.contDiff_θ i).of_le (by simp)).contDiffOn.contDiffOnClosure hΩ
  have hθ₀₁ : ContDiffOnClosure ℝ 1 a.θ₀ Ω :=
    (a.contDiff_θ₀.of_le (by simp)).contDiffOn.contDiffOnClosure hΩ
  obtain ⟨G, hGdef⟩ : ∃ G : Fin a.k → 𝔼 → 𝔼, G = fun i y ↦ a.θ i y • F y := ⟨_, rfl⟩
  obtain ⟨G₀, hG₀def⟩ : ∃ G₀ : 𝔼 → 𝔼, G₀ = fun y ↦ a.θ₀ y • F y := ⟨_, rfl⟩
  have hG₁ : ∀ i, ContDiffOnClosure ℝ 1 (G i) Ω := fun i ↦ by
    rw [hGdef]; exact (hθ₁ i).smul hΩ hF₁
  have hG₀₁ : ContDiffOnClosure ℝ 1 G₀ Ω := by
    rw [hG₀def]; exact hθ₀₁.smul hΩ hF₁
  -- pointwise decomposition of `div F` on `Ω`
  have hdiv : ∀ y ∈ Ω, EuclideanSpace.div F y
      = EuclideanSpace.div G₀ y + ∑ i, EuclideanSpace.div (G i) y := fun y hy ↦ by
    have hF' : DifferentiableAt ℝ F y :=
      (hF₁.1.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hy)
    have hd : ∀ i, DifferentiableAt ℝ (G i) y := fun i ↦ by
      rw [hGdef]; exact ((a.contDiff_θ i).differentiable (by simp) y).smul hF'
    have hd₀ : DifferentiableAt ℝ G₀ y := by
      rw [hG₀def]; exact (a.contDiff_θ₀.differentiable (by simp) y).smul hF'
    have hFeq : F = G₀ + fun y ↦ ∑ i, G i y := by
      funext z
      simp only [hGdef, hG₀def, Pi.add_apply, ← Finset.sum_smul, ← add_smul, a.θ₀_add_sum_θ,
        one_smul]
    conv_lhs => rw [hFeq]
    rw [EuclideanSpace.div_add hd₀ (DifferentiableAt.fun_sum fun i _ ↦ hd i),
      EuclideanSpace.div_finset_sum _ fun i _ ↦ hd i]
  have hint₀ : IntegrableOn (EuclideanSpace.div G₀) Ω := hG₀₁.integrableOn_div hΩ hb
  have hint : ∀ i, IntegrableOn (EuclideanSpace.div (G i)) Ω := fun i ↦
    (hG₁ i).integrableOn_div hΩ hb
  rw [setIntegral_congr_fun hΩ.measurableSet hdiv,
    integral_add hint₀ (integrable_finsetSum _ fun i _ ↦ hint i),
    integral_finsetSum _ fun i _ ↦ hint i]
  -- the interior piece vanishes
  have h₀ : ∫ y in Ω, EuclideanSpace.div G₀ y = 0 := by
    rw [hG₀def]
    exact EuclideanSpace.integral_div_smul_eq_zero_of_disjoint_tsupport_frontier hΩ hb
      (a.contDiff_θ₀.of_le (by simp)) a.disjoint_tsupport_θ₀ hF₁.1
  -- the chart pieces
  have hpiece : ∀ i, ∫ y in Ω, EuclideanSpace.div (G i) y
      = ∫ x, a.θ i x • ⟪F x, a.normal x⟫_ℝ ∂(a.localMeasure i) := fun i ↦ by
    rw [hGdef]
    exact a.integral_div_smul_θ_eq hΩ hF₀ hF₁ i
  simp_rw [h₀, hpiece, zero_add]
  -- the atlas measure recombines
  have hint' : Integrable (fun x ↦ ⟪F x, a.normal x⟫_ℝ) a.measure :=
    a.integrable_of_continuousOn ((hF₀.mono frontier_subset_closure).inner a.continuousOn_normal)
  exact (a.integral_measure_eq_sum hint').symm

end GraphAtlas

/-! ### The divergence theorem, the boundary data and the transversal field of a $C^1$ domain -/

namespace IsContDiffDomain

section Set

variable {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hΩ : IsContDiffDomain 1 Ω)
  (hb : Bornology.IsBounded Ω)

/-- **The divergence theorem on a bounded $C^1$ domain.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be
a bounded $C^1$ domain, with the surface measure $\sigma$ (`IsContDiffDomain.boundaryMeasure`)
and the outward unit normal $\nu$ (`IsContDiffDomain.outwardNormal`). For
$F \in C^1(\overline{\Omega})$,
$$\int_\Omega \operatorname{div} F \, dx = \int \langle F, \nu \rangle \, d\sigma.$$
This is Gauss's formula of [han2009theoretical], §7.6, Theorem 1.5.3.1 of [grisvard2011elliptic]
for classical fields, and Example 4 of §9.5 of [brezis2011functional].

The hypothesis $F \in C^1(\overline{\Omega})$ is `ContinuousOn F (closure Ω)` together with
`ContDiffOnClosure ℝ 1 F Ω`. The proof is `GraphAtlas.integral_div_eq` for the atlas that
defines $\sigma$ and $\nu$. -/
theorem integral_div_eq {F : 𝔼 → 𝔼} (hF₀ : ContinuousOn F (closure Ω))
    (hF₁ : ContDiffOnClosure ℝ 1 F Ω) :
    ∫ x in Ω, EuclideanSpace.div F x
      = ∫ x, ⟪F x, hΩ.outwardNormal hb x⟫_ℝ ∂(hΩ.boundaryMeasure hb) :=
  (hΩ.graphAtlas hb).integral_div_eq hΩ.isOpen hb hF₀ hF₁

/-- Let $T$ be a rigid motion of $\mathbb{R}^{d+1}$, let $g \colon \mathbb{R}^d \to \mathbb{R}$, and
let $x \in \mathbb{R}^{d+1}$. The downward direction $T^{-1}(-e_N)$ of the chart and the chart
normal $\nu_{T,g}(x)$ satisfy
$$\langle T^{-1}(-e_N), \nu_{T,g}(x) \rangle = \frac{1}{\sqrt{1 + |\nabla g((Tx)')|^2}}.$$
In the frame $T$ the normal is $(\nabla g, -1)/\sqrt{1 + |\nabla g|^2}$.

Here $T^{-1}$ is the inverse of the linear part of $T$, and the right side is the inverse of
`EuclideanSpace.graphDensity`. -/
theorem inner_symm_neg_single_last_graphNormal (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) (g : 𝔼' → ℝ) (x : 𝔼) :
    ⟪T.linearIsometryEquiv.symm (-EuclideanSpace.single (Fin.last d) (1 : ℝ)),
        EuclideanSpace.graphNormal T g x⟫_ℝ
      = (EuclideanSpace.graphDensity g (EuclideanSpace.init (T x)))⁻¹ := by
  rw [EuclideanSpace.graphNormal, real_inner_smul_right, LinearIsometryEquiv.inner_map_map,
    inner_neg_left, EuclideanSpace.inner_single_left, EuclideanSpace.snocLast_apply_last]
  simp

/-- **A bounded $C^1$ domain has a transversal field.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
bounded $C^1$ domain with the surface measure $\sigma$ and the outward unit normal $\nu$. Then
there is a $C^1$ field $w \colon \mathbb{R}^{d+1} \to \mathbb{R}^{d+1}$ with compact support
such that $\langle w, \nu \rangle \ge 1$ $\sigma$-almost everywhere.

The field is $w = c \sum_i \theta_i T_i^{-1}(-e_N)$ for the atlas that defines $\sigma$, where
$c \ge 1$ bounds the densities $\sqrt{1 + |\nabla g_i|^2}$ on the bounded parameter domains. On
$\partial\Omega \cap B(x_i, r_i)$ the normal is the chart normal, and $\langle T_i^{-1}(-e_N),
\nu \rangle = 1/\sqrt{1 + |\nabla g_i|^2} \ge 1/c$ by
`IsContDiffDomain.inner_symm_neg_single_last_graphNormal`. So
$\langle w, \nu \rangle \ge \sum_i \theta_i = 1$ on $\partial\Omega$. -/
theorem exists_transversalField :
    ∃ w : 𝔼 → 𝔼, ContDiff ℝ 1 w ∧ HasCompactSupport w ∧
      ∀ᵐ x ∂(hΩ.boundaryMeasure hb), 1 ≤ ⟪w x, hΩ.outwardNormal hb x⟫_ℝ := by
  set a := hΩ.graphAtlas hb with ha
  -- a common bound `c ≥ 1` on the densities of the charts over their parameter domains
  have hbd : ∀ i : Fin a.k, ∃ M, ∀ x' ∈ a.graphDomain i,
      EuclideanSpace.graphDensity (a.g i) x' ≤ M := fun i ↦ by
    obtain ⟨M, hM⟩ := (EuclideanSpace.isBounded_graphDomain (T := a.T i) (g := a.g i) (a.x i)
      (a.r i)).isCompact_closure.exists_bound_of_continuousOn
      (EuclideanSpace.continuous_graphDensity (a.contDiff_g i)).continuousOn
    exact ⟨M, fun x' hx' ↦ (le_abs_self _).trans (hM x' (subset_closure hx'))⟩
  choose M hM using hbd
  obtain ⟨c₀, hc₀⟩ := (Set.finite_range M).bddAbove
  set c := max c₀ 1 with hcdef
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMc : ∀ i, M i ≤ c := fun i ↦ (hc₀ ⟨i, rfl⟩).trans (le_max_left _ _)
  -- the downward direction of each chart
  set v : Fin a.k → 𝔼 := fun i ↦
    (a.T i).linearIsometryEquiv.symm (-EuclideanSpace.single (Fin.last d) (1 : ℝ)) with hvdef
  refine ⟨fun x ↦ c • ∑ i, a.θ i x • v i, ?_, ?_, ?_⟩
  · have h1 : ∀ i, ContDiff ℝ 1 (a.θ i) := fun i ↦ (a.contDiff_θ i).of_le (by simp)
    have h2 : ContDiff ℝ 1 fun x ↦ ∑ i, a.θ i x • v i :=
      ContDiff.sum fun i _ ↦ (h1 i).smul_const (v i)
    exact h2.const_smul c
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_iUnion fun i ↦ a.hasCompactSupport_θ i) fun x hx ↦ ?_
    by_contra hnot
    simp only [mem_iUnion, not_exists] at hnot
    refine hx ?_
    simp only [Function.mem_support, ne_eq] at hx ⊢
    rw [Finset.sum_eq_zero fun i _ ↦ by rw [image_eq_zero_of_notMem_tsupport (hnot i), zero_smul],
      smul_zero]
  · filter_upwards [hΩ.ae_mem_frontier_boundaryMeasure hb] with x hx
    have key : ∀ i, a.θ i x * c⁻¹ ≤ a.θ i x * ⟪v i, hΩ.outwardNormal hb x⟫_ℝ := fun i ↦ by
      by_cases hθ : a.θ i x = 0
      · simp [hθ]
      · have hxB : x ∈ Metric.ball (a.x i) (a.r i) := by
          by_contra hB
          exact hθ (a.θ_eq_zero i hB)
        refine mul_le_mul_of_nonneg_left ?_ (a.θ_nonneg i x)
        rw [hΩ.outwardNormal_eq_graphNormal_atlas hb hx hxB, hvdef,
          inner_symm_neg_single_last_graphNormal]
        have hx' : EuclideanSpace.init (a.T i x) ∈ a.graphDomain i := by
          change EuclideanSpace.graphParam (a.T i) (a.g i) (EuclideanSpace.init (a.T i x))
            ∈ Metric.ball (a.x i) (a.r i)
          rw [EuclideanSpace.graphParam_eq_of_mem_frontier (a.contDiff_g i).continuous
            (EuclideanSpace.mem_frontier_preimage_epigraph_of_mem_frontier
              (a.contDiff_g i).continuous (a.inter_ball_eq i) hx hxB)]
          exact hxB
        exact inv_anti₀ (EuclideanSpace.graphDensity_pos _) ((hM i _ hx').trans (hMc i))
    calc (1 : ℝ) = c * ∑ i, a.θ i x * c⁻¹ := by
          rw [← Finset.sum_mul, a.sum_θ hx, one_mul, mul_inv_cancel₀ hc.ne']
      _ ≤ c * ∑ i, a.θ i x * ⟪v i, hΩ.outwardNormal hb x⟫_ℝ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ key i) hc.le
      _ = ⟪c • ∑ i, a.θ i x • v i, hΩ.outwardNormal hb x⟫_ℝ := by
          rw [real_inner_smul_left, sum_inner]
          simp_rw [real_inner_smul_left]

end Set

section Opens

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- **The boundary data of a bounded $C^1$ domain.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
bounded $C^1$ domain. The surface measure `IsContDiffDomain.boundaryMeasure`, the outward unit
normal `IsContDiffDomain.outwardNormal`, and the divergence theorem
`IsContDiffDomain.integral_div_eq` form a `BoundaryData` of $\Omega$.

The theorems on $C^1$ domains use `hΩ.boundaryData hb`. They compute with the descriptions on a
chart ball, `IsContDiffDomain.boundaryMeasure_restrict_ball` and
`IsContDiffDomain.outwardNormal_eq_graphNormal`. -/
def boundaryData : BoundaryData Ω where
  σ := hΩ.boundaryMeasure hb
  ν := hΩ.outwardNormal hb
  isBounded := hb
  isFiniteMeasure := hΩ.isFiniteMeasure_boundaryMeasure hb
  measure_compl_frontier := hΩ.boundaryMeasure_compl_frontier hb
  aestronglyMeasurable_ν := hΩ.aestronglyMeasurable_outwardNormal hb
  ae_norm_ν := hΩ.ae_norm_outwardNormal hb
  integral_div_eq := fun _ hF₀ hF₁ ↦ hΩ.integral_div_eq hb hF₀ hF₁

/-- The surface measure of the boundary data of a bounded $C^1$ domain is
`IsContDiffDomain.boundaryMeasure`. -/
@[simp]
theorem boundaryData_σ : (hΩ.boundaryData hb).σ = hΩ.boundaryMeasure hb := rfl

/-- The normal of the boundary data of a bounded $C^1$ domain is `IsContDiffDomain.outwardNormal`.
-/
@[simp]
theorem boundaryData_ν : (hΩ.boundaryData hb).ν = hΩ.outwardNormal hb := rfl

/-- **The boundary data of a bounded $C^1$ domain have a transversal field**: a $C^1$ field $w$ with
compact support and $\langle w, \nu \rangle \ge 1$ $\sigma$-almost everywhere.

This is `IsContDiffDomain.exists_transversalField`. It is the hypothesis of the trace
construction of Nečas in `Numlib.Analysis.Sobolev.Boundary.Trace`. -/
theorem hasTransversalField : (hΩ.boundaryData hb).HasTransversalField :=
  hΩ.exists_transversalField hb

/-! ### The trace theorem on a bounded $C^1$ domain -/

/-- **The trace theorem on a bounded $C^1$ domain.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
bounded $C^1$ domain with the surface measure $\sigma$ and the outward unit normal $\nu$. This
is a trace family of its boundary data: for every $1 \le p < \infty$ a bounded linear trace
$W^{1,p}(\Omega) \to L^p(\sigma)$ that maps a function continuous on $\overline{\Omega}$ to its
restriction, together with Green's formula. This is Theorem 7.3.10(a) and (b) of
[han2009theoretical] with the Lipschitz domain replaced by a $C^1$ domain, Theorem 1.5.1.3 of
[grisvard2011elliptic] with values in $L^p(\Gamma)$, and item 7 of the Comments on Chapter 9 of
[brezis2011functional].

The family is `BoundaryData.traceFamily` of `Numlib.Analysis.Sobolev.Boundary.Trace`, applied to
the transversal field `IsContDiffDomain.hasTransversalField` and to the density theorems of
`Numlib.Analysis.Sobolev.Boundary.Density`: a bounded $C^1$ graph domain has the segment
property. -/
def traceFamily : (hΩ.boundaryData hb).TraceFamily :=
  BoundaryData.traceFamily _ (hΩ.hasTransversalField hb) (fun _ _ hp ↦ hΩ.hasSmoothDensity hp)
    fun _ _ hp ↦ hΩ.hasUniformSmoothDensity hb hp

/-- **The trace operator of a bounded $C^1$ domain.** For $1 \le p < \infty$, this is the bounded
linear trace $T \colon W^{1,p}(\Omega) \to L^p(\sigma)$ of `IsContDiffDomain.traceFamily`. -/
abbrev traceL (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] Lp ℝ p (hΩ.boundaryMeasure hb) :=
  (hΩ.traceFamily hb).traceL p hp

/-- For $1 \le p < \infty$, the trace operator of `IsContDiffDomain.traceFamily` is the trace
operator `BoundaryData.traceL` that the transversal field gives for the boundary data of
$\Omega$. -/
theorem traceFamily_traceL (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (hΩ.traceFamily hb).traceL p hp
      = (hΩ.boundaryData hb).traceL (hΩ.hasTransversalField hb) p hp :=
  rfl

/-- **The trace of a function continuous up to the boundary is its restriction.** Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain and let $1 \le p < \infty$. Let
$u \in W^{1,p}(\Omega)$, and let $\tilde u$ be continuous on $\overline{\Omega}$ with
$u = \tilde u$ almost everywhere on $\Omega$. Then $Tu = \tilde u$ $\sigma$-almost everywhere.
This is Theorem 7.3.10(a) of [han2009theoretical].

The function of $u$ is `SobolevMultiIndex.fn u`. -/
theorem traceL_ae_eq_of_continuousOn (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : SobolevEuclidean (d + 1) 1 p Ω) {ũ : 𝔼 → ℝ}
    (hu : SobolevMultiIndex.fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) :
    (hΩ.traceL hb p hp u : 𝔼 → ℝ) =ᵐ[hΩ.boundaryMeasure hb] ũ :=
  (hΩ.traceFamily hb).traceL_ae_eq p hp u ũ hu hc

/-- **Green's formula on a bounded $C^1$ domain.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
bounded $C^1$ domain with the surface measure $\sigma$ and the outward unit normal $\nu$, and
let $1 < p, q < \infty$ with $1/p + 1/q = 1$. For $u \in W^{1,p}(\Omega)$,
$v \in W^{1,q}(\Omega)$ and every coordinate $i$,
$$\int_\Omega \partial_i u \, v \, dx + \int_\Omega u \, \partial_i v \, dx = \int (Tu)(Tv) \,
  \nu_i \, d\sigma.$$
This is Theorem 1.5.3.1 of [grisvard2011elliptic], (7.6.1) and (7.6.3) of [han2009theoretical],
and item 7(iii) of the Comments on Chapter 9 of [brezis2011functional].

The weak derivative $\partial_i u$ is `SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)`.
The exponents are finite and Hölder conjugate, so both are greater than $1$. -/
theorem green (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (u : SobolevEuclidean (d + 1) 1 p Ω)
    (v : SobolevEuclidean (d + 1) 1 q Ω) (i : Fin (d + 1)) :
    (∫ x in (Ω : Set 𝔼),
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x
          * SobolevMultiIndex.fn v x)
      + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x
          * (SobolevMultiIndex.weakDeriv v (MultiIndexLE.single i) : 𝔼 → ℝ) x
      = ∫ x, (hΩ.traceL hb p hp u : 𝔼 → ℝ) x * (hΩ.traceL hb q hq v : 𝔼 → ℝ) x
          * hΩ.outwardNormal hb x i ∂(hΩ.boundaryMeasure hb) :=
  (hΩ.traceFamily hb).green p q hp hq u v i

/-- **Green's formula against a test function of class $C^1$.** Let
$\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain and let $1 \le p < \infty$. For
$u \in W^{1,p}(\Omega)$, a $C^1$ function $\varphi \colon \mathbb{R}^{d+1} \to \mathbb{R}$ with
compact support, and every coordinate $i$,
$$\int_\Omega \partial_i u \, \varphi \, dx + \int_\Omega u \, \partial_i \varphi \, dx = \int
  (Tu) \, \varphi \, \nu_i \, d\sigma.$$
-/
theorem green_contDiff (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : SobolevEuclidean (d + 1) 1 p Ω)
    {φ : 𝔼 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (i : Fin (d + 1)) :
    (∫ x in (Ω : Set 𝔼),
        (SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * φ x)
      + ∫ x in (Ω : Set 𝔼), SobolevMultiIndex.fn u x
          * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, (hΩ.traceL hb p hp u : 𝔼 → ℝ) x * φ x * hΩ.outwardNormal hb x i
          ∂(hΩ.boundaryMeasure hb) :=
  (hΩ.traceFamily hb).green_contDiff p hp u φ hφ hφc i

/-- **$W_0^{1,p}(\Omega)$ lies in the kernel of the trace.** Let $\Omega \subseteq \mathbb{R}^{d+1}$
be a bounded $C^1$ domain and let $1 \le p < \infty$. If $u \in W_0^{1,p}(\Omega)$, then
$Tu = 0$. This is the easy half of item 7(ii) of the Comments on Chapter 9 of
[brezis2011functional]. -/
theorem traceL_eq_zero_of_mem_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p Ω) :
    hΩ.traceL hb p hp u = 0 :=
  (hΩ.traceFamily hb).traceL_eq_zero_of_mem_zero hp hu

/-- **The trace is compact.** Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain and
let $1 < p < \infty$. Then the trace $T \colon W^{1,p}(\Omega) \to L^p(\sigma)$ is a compact
operator. This is Theorem 7.3.10(c) of [han2009theoretical] for $p > 1$.

The proof combines the sharp inequality of Nečas (`BoundaryData.isCompactOperator_traceL`) with
Rellich's theorem `SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one`, which for $p \neq 1$
needs no restriction on the dimension. The hypothesis $1 < p$ is necessary: the trace
$W^{1,1}(\Omega) \to L^1(\partial\Omega)$ is onto (Gagliardo), so it is not compact. The source
states the compactness for $1 \le p$, which is an error. -/
theorem isCompactOperator_traceL (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsCompactOperator (hΩ.traceL hb p hp) := by
  refine BoundaryData.isCompactOperator_traceL _ (hΩ.hasTransversalField hb) p hp hp1
    (hΩ.hasSmoothDensity hp) ?_
  lift p to ℝ≥0 using hp
  refine SobolevEuclidean.isCompactEmbedding_fnL_of_ne_one hΩ.isContDiffChartDomain hb
    (Or.inl fun h ↦ hp1.ne' ?_)
  rw [h]
  rfl

end Opens

end IsContDiffDomain

/-! ### Chart domains in the sense of Brezis, through the graph domains -/

namespace IsContDiffChartDomain

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (h : IsContDiffChartDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- **The boundary data of a bounded $C^1$ chart domain.** Let $\Omega \subseteq \mathbb{R}^{d+1}$
be bounded and of class $C^1$ by local charts in the sense of §9.2 of [brezis2011functional].
These are the boundary data `IsContDiffDomain.boundaryData` of $\Omega$ as a graph domain, which
it is by the implicit function theorem (`IsContDiffChartDomain.isContDiffDomain`). -/
def boundaryData : BoundaryData Ω :=
  (h.isContDiffDomain le_rfl WithTop.one_ne_top).boundaryData hb

/-- **The trace theorem on a bounded $C^1$ chart domain.** Let $\Omega \subseteq \mathbb{R}^{d+1}$
be bounded and of class $C^1$ by local charts. This is the trace family
`IsContDiffDomain.traceFamily` of $\Omega$ as a graph domain, for the boundary data
`IsContDiffChartDomain.boundaryData`. -/
def traceFamily : (h.boundaryData hb).TraceFamily :=
  (h.isContDiffDomain le_rfl WithTop.one_ne_top).traceFamily hb

end IsContDiffChartDomain

end
