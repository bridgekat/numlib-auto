/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Function.Jacobian
import Numlib.Analysis.Calculus.Deriv.Slope
import Numlib.Analysis.Sobolev.Boundary.Data
import Numlib.Analysis.Sobolev.Boundary.Gram
import Numlib.Topology.MetricSpace.Bounded

/-!
# The surface measure and the outward normal of a bounded $C^1$ domain

Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded $C^1$ domain in the graph sense of
`IsContDiffDomain 1 Ω` (Definition 7.2.1 of [han2009theoretical]). This file builds the surface
measure $\sigma$ on $\partial\Omega$ and the outward unit normal $\nu$ from graph charts and a
partition of unity, and characterizes both chart by chart. A **graph chart** at $(x_0, r)$ is a
rigid motion $T$ of $\mathbb{R}^{d+1}$, with linear part $L$, and a $C^1$ function
$g : \mathbb{R}^d \to \mathbb{R}$ with $\Omega \cap B(x_0, r) = B(x_0, r) \cap T^{-1}(\{y :
y_{d+1} > g(y')\})$. Its parametrization $\Phi(x') = T^{-1}(x', g(x'))$ maps the open bounded set
$D = \Phi^{-1}(B(x_0, r)) \subseteq \mathbb{R}^d$ onto $\partial\Omega \cap B(x_0, r)$. The local
surface measure is the image under $\Phi$ of the measure $\sqrt{1 + |\nabla g|^2} \, dx'$ on $D$,
and the local outward normal at $x$ is
$$\nu(x) = \frac{L^{-1}(\nabla g(x'), -1)}{\sqrt{1 + |\nabla g(x')|^2}}, \qquad x' = (T x)'.$$

A **graph atlas** of $\Omega$ is a finite family of graph charts whose balls cover $\partial\Omega$,
together with a smooth partition of unity $\theta_0 + \sum_i \theta_i = 1$ subordinate to the balls,
with $\theta_0$ vanishing near $\partial\Omega$, as in Lemma 9.3 of [brezis2011functional]. Its
measure is $\sum_i \theta_i \sigma_i$, and its normal is $\nu_i$ on the $i$-th ball. Restricted to
the ball of *any* graph chart of $\Omega$, the atlas measure is the local measure of that chart, and
the atlas normal on $\partial\Omega$ is the normal of that chart. So the measure and the normal do
not depend on the atlas. Every bounded $C^1$ domain has an atlas, and
`IsContDiffDomain.boundaryMeasure` and `IsContDiffDomain.outwardNormal` are the measure and the
normal of a chosen one.

## Main definitions

* `EuclideanSpace.graphParam`, `EuclideanSpace.graphDomain`, `EuclideanSpace.graphDensity`,
  `EuclideanSpace.graphMeasure`, `EuclideanSpace.graphNormal`, `EuclideanSpace.graphTransition`: the
  parametrization, the parameter domain, the surface element, the local surface measure, the local
  normal of a graph chart, and the transition between two charts.
* `GraphAtlas`, `GraphAtlas.measure`, `GraphAtlas.normal`: a graph atlas with a partition of unity,
  and its surface measure and normal.
* `IsContDiffDomain.graphAtlas`, `IsContDiffDomain.boundaryMeasure`,
  `IsContDiffDomain.outwardNormal`: a chosen atlas of a bounded $C^1$ domain, and the surface
  measure and outward unit normal of the domain.

## Main results

* `EuclideanSpace.integral_graphMeasure`: the integral against the local measure is $\int_s
  \sqrt{1 + |\nabla g(x')|^2} \, f(\Phi(x')) \, dx'$.
* `EuclideanSpace.graphNormal_outward`: the local normal points out of the region above the graph.
* `EuclideanSpace.graphDensity_graphTransition`: the surface elements of two charts differ by the
  factor $|\det D\psi|$ of the transition $\psi$.
* `EuclideanSpace.graphMeasure_eq_of_eq`, `EuclideanSpace.graphNormal_eq_of_eq`: two charts that
  describe the same set on an open set give the same local measure and the same normal there.
* `GraphAtlas.measure_restrict_ball`, `IsContDiffDomain.boundaryMeasure_restrict_ball`: the surface
  measure restricted to any chart ball is the local measure of the chart.
* `GraphAtlas.measure_eq`: the atlas measure does not depend on the atlas.
* `IsContDiffDomain.boundaryMeasure_pos_of_isOpen`: every open set that meets $\partial\Omega$ has
  positive surface measure.
* `IsContDiffDomain.outwardNormal_eq_graphNormal`: on $\partial\Omega$ the outward normal is the
  normal of any chart.

## Proof outline

On the overlap of two charts, the transition $\psi = (T_2 \Phi_1)'$ is a $C^1$ injection between
open subsets of $\mathbb{R}^d$ with $\Phi_1 = \Phi_2 \circ \psi$. The surface element of a chart is
the Gram factor of $D\Phi$ (`EuclideanSpace.graphDensity_eq_gram`), so the identity
$\operatorname{gram}(L A) = \operatorname{gram}(L) \, |\det A|$ of
`Numlib.Analysis.Sobolev.Boundary.Gram` shows that the surface elements transform by $|\det D\psi|$.
The change of variables formula then gives equality of the two local measures on the overlap. The
two normals are unit vectors orthogonal to the common tangent space, so $\nu_2 = \pm \nu_1$, by a
direct computation in the frame of the first chart; both point outward, which excludes the minus
sign. On a chart ball, the partition of unity glues the restrictions of the local measures back to
the local measure of that chart, which gives the chart characterization of the atlas measure.

## Implementation notes

* The sign of the normal: $\Omega$ lies above the graph, the function $\varphi(y) = g(y') - y_{d+1}$
  is negative on $\Omega$, and its gradient $(\nabla g, -1)$ points out of $\Omega$. The normal
  $(-\nabla\varphi, 1)$ of [grisvard2011elliptic] §1.5.1 is the one for a region *below* the graph.
  `EuclideanSpace.graphNormal_outward` proves that the sign is correct.
* The normal is a function on all of $\mathbb{R}^{d+1}$. The local normal at $x$ is computed from
  $x' = (Tx)'$ for every $x$, and the atlas normal is $0$ outside the chart balls.
* No Hausdorff measure enters. The identity of $\sigma$ with the $d$-dimensional Hausdorff measure
  restricted to $\partial\Omega$ (the area formula) is not proved here.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace Topology

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

namespace EuclideanSpace

/-! ### The graph parametrization -/

variable (T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  (g : EuclideanSpace ℝ (Fin d) → ℝ)

/-- **The parametrization of the graph of $g$ in the frame of the rigid motion $T$**: for a rigid
motion $T$ of $\mathbb{R}^{d+1}$ and $g : \mathbb{R}^d \to \mathbb{R}$,
$$\Phi(x') = T^{-1}(x', g(x')), \qquad x' \in \mathbb{R}^d.$$

When $g$ is continuous, $\Phi$ maps $\mathbb{R}^d$ onto the boundary of
$T^{-1}(\{y : y_{d+1} > g(y')\})$, the region above the graph in the frame $T$
(`EuclideanSpace.graphParam_mem_frontier_epigraph`,
`EuclideanSpace.graphParam_eq_of_mem_frontier`). -/
def graphParam (x' : 𝔼') : 𝔼 := T.symm (snocLast x' (g x'))

variable {T g}

/-- The first $d$ coordinates of $T \Phi(x')$ are $x'$. -/
@[simp]
theorem init_apply_graphParam (x' : 𝔼') : init (T (graphParam T g x')) = x' := by
  simp [graphParam]

/-- The last coordinate of $T \Phi(x')$ is $g(x')$. -/
@[simp]
theorem apply_graphParam_last (x' : 𝔼') : T (graphParam T g x') (Fin.last d) = g x' := by
  simp [graphParam]

/-- The graph parametrization $\Phi$ is injective. -/
theorem graphParam_injective : Function.Injective (graphParam T g) := fun x y h ↦ by
  have := congrArg (fun z ↦ init (T z)) h
  simpa using this

/-- If $g$ is continuous, every point $\Phi(x')$ lies on the boundary of the region
$T^{-1}(\{y : y_{d+1} > g(y')\})$. -/
theorem graphParam_mem_frontier_epigraph (hg : Continuous g) (x' : 𝔼') :
    graphParam T g x' ∈ frontier (T ⁻¹' epigraph g) := by
  rw [frontier_preimage_epigraph hg]
  simp

/-- If $g$ is continuous, every point $x$ of the boundary of $T^{-1}(\{y : y_{d+1} > g(y')\})$ is
the parametrization of its first coordinates in the frame $T$: $x = \Phi((Tx)')$. -/
theorem graphParam_eq_of_mem_frontier (hg : Continuous g) {x : 𝔼}
    (hx : x ∈ frontier (T ⁻¹' epigraph g)) : graphParam T g (init (T x)) = x := by
  rw [frontier_preimage_epigraph hg] at hx
  have hx' : T x (Fin.last d) = g (init (T x)) := hx
  rw [graphParam, ← hx', snocLast_init_last, AffineIsometryEquiv.symm_apply_apply]

/-- If $g$ is continuous, the graph parametrization $\Phi$ is continuous. -/
theorem continuous_graphParam (hg : Continuous g) : Continuous (graphParam T g) := by
  unfold graphParam
  exact T.symm.continuous.comp (continuous_snocLast.comp (continuous_id.prodMk hg))

/-- If $g$ is of class $C^n$, the graph parametrization $\Phi$ is of class $C^n$. -/
theorem contDiff_graphParam {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (graphParam T g) := by
  unfold graphParam
  refine (contDiff_affineIsometryEquiv T.symm).comp ?_
  change ContDiff ℝ n fun x' ↦ (lastInitL d).symm (g x', x')
  exact (lastInitL d).symm.contDiff.comp (hg.prodMk contDiff_id)

/-- If $g$ is continuous, the graph parametrization $\Phi$ is a measurable embedding, because it is
continuous and injective on a Polish space. -/
theorem measurableEmbedding_graphParam (hg : Continuous g) :
    MeasurableEmbedding (graphParam T g) :=
  (continuous_graphParam hg).measurableEmbedding graphParam_injective

/-- **The derivative of the graph parametrization.** If $g$ has derivative $\ell$ at $x'$, then
$\Phi$ has derivative $v \mapsto L^{-1}(v, \ell v)$ at $x'$, where $L$ is the linear part of
$T$.

The derivative is the composition of `T.linearIsometryEquiv.symm` with
`EuclideanSpace.snocLastL ℓ`. -/
theorem hasFDerivAt_graphParam {x' : 𝔼'} {ℓ : 𝔼' →L[ℝ] ℝ} (hg : HasFDerivAt g ℓ x') :
    HasFDerivAt (graphParam T g)
      ((T.linearIsometryEquiv.symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼) ∘L snocLastL ℓ) x' := by
  have h1 : HasFDerivAt (fun x' : 𝔼' ↦ snocLast x' (g x')) (snocLastL ℓ) x' := by
    change HasFDerivAt (fun x' : 𝔼' ↦ (lastInitL d).symm (g x', x')) _ x'
    exact (lastInitL d).symm.hasFDerivAt.comp x' (hg.prodMk (hasFDerivAt_id x'))
  have h2 := (T.symm.hasFDerivAt (snocLast x' (g x'))).comp x' h1
  rwa [AffineIsometryEquiv.linearIsometryEquiv_symm] at h2

/-- If $g$ is differentiable at $x'$, the derivative of $\Phi$ at $x'$ is
$v \mapsto L^{-1}(v, Dg(x') v)$, where $L$ is the linear part of $T$. -/
theorem fderiv_graphParam {x' : 𝔼'} (hg : DifferentiableAt ℝ g x') :
    fderiv ℝ (graphParam T g) x'
      = (T.linearIsometryEquiv.symm.toContinuousLinearEquiv : 𝔼 →L[ℝ] 𝔼) ∘L
        snocLastL (fderiv ℝ g x') :=
  (hasFDerivAt_graphParam hg.hasFDerivAt).fderiv

/-- If $g$ is differentiable at $x'$, the derivative of $\Phi$ at $x'$ is injective: its composition
with $y \mapsto (L y)'$ is the identity. -/
theorem injective_fderiv_graphParam {x' : 𝔼'} (hg : DifferentiableAt ℝ g x') :
    Function.Injective (fderiv ℝ (graphParam T g) x') := by
  rw [fderiv_graphParam hg]
  intro v w h
  have := congrArg (fun z ↦ init (T.linearIsometryEquiv z)) h
  simpa using this

/-! ### The chart domain -/

variable (T g) in
/-- **The parameter domain of a graph chart**: the set $D = \Phi^{-1}(B(x_0, r)) \subseteq
\mathbb{R}^d$ of parameters whose points lie in the chart ball. -/
def graphDomain (x₀ : 𝔼) (r : ℝ) : Set 𝔼' := graphParam T g ⁻¹' Metric.ball x₀ r

/-- If $g$ is continuous, the parameter domain $\Phi^{-1}(B(x_0, r))$ is open. -/
theorem isOpen_graphDomain (hg : Continuous g) (x₀ : 𝔼) (r : ℝ) :
    IsOpen (graphDomain T g x₀ r) :=
  Metric.isOpen_ball.preimage (continuous_graphParam hg)

/-- If $g$ is continuous, the parameter domain $\Phi^{-1}(B(x_0, r))$ is measurable. -/
theorem measurableSet_graphDomain (hg : Continuous g) (x₀ : 𝔼) (r : ℝ) :
    MeasurableSet (graphDomain T g x₀ r) :=
  (isOpen_graphDomain hg x₀ r).measurableSet

/-- The parameter domain $\Phi^{-1}(B(x_0, r))$ is bounded: on it,
$\|x'\| \le \|T\Phi(x')\| < \|T x_0\| + r$. -/
theorem isBounded_graphDomain (x₀ : 𝔼) (r : ℝ) : Bornology.IsBounded (graphDomain T g x₀ r) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨‖T x₀‖ + r, fun x' hx' ↦ ?_⟩
  have h1 : dist (T (graphParam T g x')) (T x₀) < r := by
    rw [T.dist_map]; exact hx'
  calc ‖x'‖ = ‖init (T (graphParam T g x'))‖ := by rw [init_apply_graphParam]
    _ ≤ ‖T (graphParam T g x')‖ := norm_init_le _
    _ ≤ ‖T x₀‖ + ‖T (graphParam T g x') - T x₀‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖T x₀‖ + r := by rw [← dist_eq_norm]; linarith

/-- If $g$ is continuous, $\Phi$ maps the parameter domain $\Phi^{-1}(B(x_0, r))$ onto the part
$\partial(T^{-1}(\{y : y_{d+1} > g(y')\})) \cap B(x_0, r)$ of the boundary of the rotated region
inside the ball. -/
theorem graphParam_image_graphDomain (hg : Continuous g) (x₀ : 𝔼) (r : ℝ) :
    graphParam T g '' graphDomain T g x₀ r = frontier (T ⁻¹' epigraph g) ∩ Metric.ball x₀ r := by
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨graphParam_mem_frontier_epigraph hg x', hx'⟩
  · rintro ⟨hx, hxB⟩
    refine ⟨init (T x), ?_, graphParam_eq_of_mem_frontier hg hx⟩
    change graphParam T g (init (T x)) ∈ Metric.ball x₀ r
    rwa [graphParam_eq_of_mem_frontier hg hx]

end EuclideanSpace

/-- **The parametrization of a graph chart covers $\partial\Omega \cap B(x_0, r)$.** Let
$\Omega \subseteq \mathbb{R}^{d+1}$, let $T$ be a rigid motion, and let
$g : \mathbb{R}^d \to \mathbb{R}$ be continuous with $\Omega \cap B(x_0, r) = B(x_0, r) \cap
T^{-1}(\{y : y_{d+1} > g(y')\})$. Then the parametrization $\Phi$ maps the parameter domain
$\Phi^{-1}(B(x_0, r))$ onto $\partial\Omega \cap B(x_0, r)$. -/
theorem IsBoundaryGraphAt.graphParam_image_graphDomain {g : 𝔼' → ℝ} (hg : Continuous g)
    {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {Ω : Set 𝔼} {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g) :
    EuclideanSpace.graphParam T g '' EuclideanSpace.graphDomain T g x₀ r
      = frontier Ω ∩ Metric.ball x₀ r := by
  rw [EuclideanSpace.graphParam_image_graphDomain hg, IsBoundaryGraphAt.frontier_inter_ball hg h,
    EuclideanSpace.frontier_preimage_epigraph hg, inter_comm]


namespace EuclideanSpace

variable {T : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1))}
  {g : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### The surface element $\sqrt{1 + |\nabla g|^2}$ -/

variable (g) in
/-- **The surface element of the graph of $g$**: the function
$$x' \mapsto \sqrt{1 + \|\nabla g(x')\|^2}$$
on $\mathbb{R}^d$. It is the density with which the parametrization $\Phi$ carries Lebesgue
measure of $\mathbb{R}^d$ to the graph: it is the Gram factor of $D\Phi$ in every frame $T$
(`EuclideanSpace.graphDensity_eq_gram`). -/
def graphDensity (x' : 𝔼') : ℝ := Real.sqrt (1 + ‖gradient g x'‖ ^ 2)

/-- The surface element is at least $1$. -/
theorem one_le_graphDensity (x' : 𝔼') : 1 ≤ graphDensity g x' := by
  rw [graphDensity, Real.le_sqrt zero_le_one (by positivity)]
  nlinarith [sq_nonneg ‖gradient g x'‖]

/-- The surface element is positive. -/
theorem graphDensity_pos (x' : 𝔼') : 0 < graphDensity g x' :=
  zero_lt_one.trans_le (one_le_graphDensity x')

/-- The surface element is nonzero. -/
theorem graphDensity_ne_zero (x' : 𝔼') : graphDensity g x' ≠ 0 :=
  (graphDensity_pos x').ne'

/-- If $g$ is of class $C^1$, the surface element is continuous. -/
theorem continuous_graphDensity (hg : ContDiff ℝ 1 g) : Continuous (graphDensity g) := by
  have h := continuous_gradient hg
  unfold graphDensity
  fun_prop

/-- **The surface element does not depend on the frame.** If $g$ is differentiable at $x'$, then for
every rigid motion $T$ the surface element $\sqrt{1 + \|\nabla g(x')\|^2}$ is the volume scaling
factor `EuclideanSpace.gram` of the derivative of $\Phi$ at $x'$.

The proof is `EuclideanSpace.gram_isometry_comp` and `EuclideanSpace.gram_snocLastL`. -/
theorem graphDensity_eq_gram (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) {x' : 𝔼'} (hg : DifferentiableAt ℝ g x') :
    graphDensity g x' = gram (fderiv ℝ (graphParam T g) x') := by
  rw [fderiv_graphParam hg, gram_isometry_comp, gram_snocLastL, graphDensity, norm_gradient_eq]

/-! ### The local surface measure -/

variable (T g) in
/-- **The local surface measure of a graph piece**: for $s \subseteq \mathbb{R}^d$, the image under
$\Phi$ of the measure with density $\sqrt{1 + |\nabla g|^2}$ with respect to Lebesgue measure on
$s$:
$$\sigma_s(A) = \int_{s \cap \Phi^{-1}(A)} \sqrt{1 + |\nabla g(x')|^2} \, dx'.$$
The formula holds for measurable $A$ and continuous $g$ (`EuclideanSpace.graphMeasure_apply`). -/
def graphMeasure (s : Set 𝔼') : Measure 𝔼 :=
  Measure.map (graphParam T g)
    ((volume.restrict s).withDensity fun x' ↦ ENNReal.ofReal (graphDensity g x'))

/-- If $g$ is of class $C^1$, the surface element, as a function with values in $[0, \infty]$, is
measurable. -/
theorem measurable_ofReal_graphDensity (hg : ContDiff ℝ 1 g) :
    Measurable fun x' ↦ ENNReal.ofReal (graphDensity g x') :=
  ENNReal.measurable_ofReal.comp (continuous_graphDensity hg).measurable

/-- If $g$ is continuous and $A \subseteq \mathbb{R}^{d+1}$ is measurable, the local surface measure
of $A$ is the weighted Lebesgue measure of its preimage:
$$\sigma_s(A) = \int_{s \cap \Phi^{-1}(A)} \sqrt{1 + |\nabla g(x')|^2} \, dx'.$$
-/
theorem graphMeasure_apply (hg : Continuous g) (s : Set 𝔼') {A : Set 𝔼} (hA : MeasurableSet A) :
    graphMeasure T g s A
      = ∫⁻ x' in s ∩ graphParam T g ⁻¹' A, ENNReal.ofReal (graphDensity g x') := by
  rw [graphMeasure, Measure.map_apply (continuous_graphParam hg).measurable hA,
    withDensity_apply _ (hA.preimage (continuous_graphParam hg).measurable),
    Measure.restrict_restrict (hA.preimage (continuous_graphParam hg).measurable), inter_comm]

/-- If $g$ is continuous and $A$ is measurable, the restriction of the local surface measure
$\sigma_s$ to $A$ is the local surface measure over $s \cap \Phi^{-1}(A)$. -/
theorem graphMeasure_restrict (hg : Continuous g) (s : Set 𝔼') {A : Set 𝔼} (hA : MeasurableSet A) :
    (graphMeasure T g s).restrict A = graphMeasure T g (s ∩ graphParam T g ⁻¹' A) := by
  rw [graphMeasure, graphMeasure, Measure.restrict_map (continuous_graphParam hg).measurable hA,
    restrict_withDensity (hA.preimage (continuous_graphParam hg).measurable),
    Measure.restrict_restrict (hA.preimage (continuous_graphParam hg).measurable), inter_comm]

/-- If $g$ is continuous and $t \subseteq \mathbb{R}^d$ is measurable, the restriction of the local
surface measure $\sigma_s$ to $\Phi(t)$ is the local surface measure over $s \cap t$. -/
theorem graphMeasure_restrict_image (hg : Continuous g) (s : Set 𝔼') {t : Set 𝔼'}
    (ht : MeasurableSet t) :
    (graphMeasure T g s).restrict (graphParam T g '' t) = graphMeasure T g (s ∩ t) := by
  rw [graphMeasure_restrict hg s ((measurableEmbedding_graphParam hg).measurableSet_image.2 ht),
    preimage_image_eq _ graphParam_injective]

/-- If $g$ is continuous and $s$ is measurable, the local surface measure $\sigma_s$ is carried by
the parametrized piece: $\sigma_s(\Phi(s)^c) = 0$. -/
theorem graphMeasure_compl_image (hg : Continuous g) {s : Set 𝔼'} (hs : MeasurableSet s) :
    graphMeasure T g s (graphParam T g '' s)ᶜ = 0 := by
  rw [graphMeasure_apply hg s ((measurableEmbedding_graphParam hg).measurableSet_image.2 hs).compl,
    preimage_compl, preimage_image_eq _ graphParam_injective, inter_compl_self,
    Measure.restrict_empty, lintegral_zero_measure]

/-- If $g$ is continuous and $s$ is measurable, $\sigma_s$-almost every point lies in $\Phi(s)$. -/
theorem ae_mem_image_graphMeasure (hg : Continuous g) {s : Set 𝔼'} (hs : MeasurableSet s) :
    ∀ᵐ x ∂(graphMeasure T g s), x ∈ graphParam T g '' s :=
  (measure_eq_zero_iff_ae_notMem.1 (graphMeasure_compl_image hg hs)).mono fun _ h ↦ not_not.1 h

/-- If $g$ is continuous and $s \subseteq t$, then $\sigma_s \le \sigma_t$. -/
theorem graphMeasure_mono_set (hg : Continuous g) {s t : Set 𝔼'} (hst : s ⊆ t) :
    graphMeasure T g s ≤ graphMeasure T g t := by
  refine Measure.map_mono ?_ (continuous_graphParam hg).measurable
  refine Measure.le_iff.2 fun A hA ↦ ?_
  rw [withDensity_apply _ hA, withDensity_apply _ hA]
  exact lintegral_mono' (Measure.restrict_mono le_rfl (Measure.restrict_mono hst le_rfl)) le_rfl

/-- If $g$ is of class $C^1$ and $s \subseteq \mathbb{R}^d$ is bounded, the surface element has a
finite integral over $s$. -/
theorem lintegral_ofReal_graphDensity_lt_top (hg : ContDiff ℝ 1 g) {s : Set 𝔼'}
    (hs : Bornology.IsBounded s) :
    ∫⁻ x' in s, ENNReal.ofReal (graphDensity g x') < ⊤ := by
  obtain ⟨C, hC⟩ := hs.isCompact_closure.exists_bound_of_continuousOn
    (continuous_graphDensity hg).continuousOn
  calc ∫⁻ x' in s, ENNReal.ofReal (graphDensity g x')
      ≤ ∫⁻ x' in closure s, ENNReal.ofReal (graphDensity g x') :=
        lintegral_mono_set subset_closure
    _ ≤ ∫⁻ _ in closure s, ENNReal.ofReal C := by
        refine setLIntegral_mono' isClosed_closure.measurableSet fun x' hx' ↦ ?_
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC x' hx'))
    _ = ENNReal.ofReal C * volume (closure s) := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs.isCompact_closure.measure_lt_top

/-- If $g$ is of class $C^1$ and $s \subseteq \mathbb{R}^d$ is bounded, the local surface measure
$\sigma_s$ is finite. -/
theorem isFiniteMeasure_graphMeasure (hg : ContDiff ℝ 1 g) {s : Set 𝔼'}
    (hs : Bornology.IsBounded s) : IsFiniteMeasure (graphMeasure T g s) := by
  rw [graphMeasure]
  have : IsFiniteMeasure
      ((volume.restrict s).withDensity fun x' ↦ ENNReal.ofReal (graphDensity g x')) :=
    isFiniteMeasure_withDensity (lintegral_ofReal_graphDensity_lt_top hg hs).ne
  infer_instance

/-- **The Lebesgue integral against the local surface measure.** If $g$ is of class $C^1$, then for
every $s \subseteq \mathbb{R}^d$ and every $f : \mathbb{R}^{d+1} \to [0, \infty]$,
$$\int f \, d\sigma_s = \int_s \sqrt{1 + |\nabla g(x')|^2} \, f(\Phi(x')) \, dx'.$$
-/
theorem lintegral_graphMeasure (hg : ContDiff ℝ 1 g) (s : Set 𝔼') (f : 𝔼 → ℝ≥0∞) :
    ∫⁻ x, f x ∂(graphMeasure T g s)
      = ∫⁻ x' in s, ENNReal.ofReal (graphDensity g x') * f (graphParam T g x') := by
  rw [graphMeasure, (measurableEmbedding_graphParam hg.continuous).lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_ofReal_graphDensity hg)
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  rfl

/-- **The integral against the local surface measure.** Let $g$ be of class $C^1$, let
$s \subseteq \mathbb{R}^d$, let $G$ be a real normed space, and let $f : \mathbb{R}^{d+1} \to G$
be almost everywhere strongly measurable for $\sigma_s$. Then
$$\int f \, d\sigma_s = \int_s \sqrt{1 + |\nabla g(x')|^2} \, f(\Phi(x')) \, dx'.$$
-/
theorem integral_graphMeasure (hg : ContDiff ℝ 1 g) (s : Set 𝔼') {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : 𝔼 → G}
    (hf : AEStronglyMeasurable f (graphMeasure T g s)) :
    ∫ x, f x ∂(graphMeasure T g s)
      = ∫ x' in s, graphDensity g x' • f (graphParam T g x') := by
  rw [graphMeasure, integral_map (continuous_graphParam hg.continuous).aemeasurable hf]
  have hm : Measurable fun x' ↦ (graphDensity g x').toNNReal :=
    (continuous_graphDensity hg).measurable.real_toNNReal
  have h := integral_withDensity_eq_integral_smul (μ := volume.restrict s) hm
    (fun x' ↦ f (graphParam T g x'))
  simp only [ENNReal.ofReal] at h ⊢
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun x' ↦ ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (graphDensity_pos x').le]

/-! ### The outward normal of a graph chart -/

variable (T g) in
/-- **The outward unit normal of the region above the graph of $g$ in the frame $T$**: for
$x \in \mathbb{R}^{d+1}$, read as the point of the graph with parameters $x' = (Tx)'$,
$$\nu(x) = \frac{L^{-1}(\nabla g(x'), -1)}{\sqrt{1 + |\nabla g(x')|^2}},$$
where $L$ is the linear part of $T$.

The region is $\{x : (Tx)_{d+1} > g((Tx)')\}$. The function $\varphi(y) = g(y') - y_{d+1}$ is
negative on it, and its gradient $(\nabla g, -1)$ points where $\varphi$ grows, that is out of
the region (`EuclideanSpace.graphNormal_outward`). The normal $(-\nabla\varphi, 1)$ of
[grisvard2011elliptic] §1.5.1 is the one for the region *below* the graph. The normal is defined
at every $x$, and depends on $x$ only through $(Tx)'$. -/
def graphNormal (x : 𝔼) : 𝔼 :=
  (graphDensity g (init (T x)))⁻¹ •
    T.linearIsometryEquiv.symm (snocLast (gradient g (init (T x))) (-1))

/-- The normal $\nu(x)$ is a unit vector, for every $x$. -/
theorem norm_graphNormal (x : 𝔼) : ‖graphNormal T g x‖ = 1 := by
  rw [graphNormal, norm_smul, norm_inv, LinearIsometryEquiv.norm_map, norm_snocLast_neg_one,
    Real.norm_eq_abs, abs_of_pos (graphDensity_pos _)]
  exact inv_mul_cancel₀ (graphDensity_ne_zero _)

/-- If $g$ is of class $C^1$, the normal $\nu$ is continuous. -/
theorem continuous_graphNormal (hg : ContDiff ℝ 1 g) : Continuous (graphNormal T g) := by
  have h1 := continuous_graphDensity hg
  have h2 := continuous_gradient hg
  have h3 : Continuous (init : 𝔼 → 𝔼') := continuous_init
  have h4 : Continuous T := T.continuous
  have h5 := (continuous_snocLast (d := d))
  have h6 := T.linearIsometryEquiv.symm.continuous
  unfold graphNormal
  refine Continuous.smul (Continuous.inv₀ (h1.comp (h3.comp h4)) fun x ↦ graphDensity_ne_zero _) ?_
  exact h6.comp (h5.comp ((h2.comp (h3.comp h4)).prodMk continuous_const))

/-- The normal $\nu(x)$ depends on $x$ only through $(Tx)'$: if $(Tx)' = (Ty)'$, then
$\nu(x) = \nu(y)$. -/
theorem graphNormal_eq_of_init_eq {x y : 𝔼} (h : init (T x) = init (T y)) :
    graphNormal T g x = graphNormal T g y := by
  simp only [graphNormal, h]

/-- **Tangency.** If $g$ is differentiable at $x'$, the normal at $\Phi(x')$ is orthogonal to the
range of the derivative of $\Phi$ at $x'$: for every $v \in \mathbb{R}^d$,
$$\bigl\langle \nu(\Phi(x')), D\Phi(x') v \bigr\rangle = 0.$$

Indeed $\langle L^{-1}(\nabla g, -1), L^{-1}(v, Dg \, v) \rangle = \langle \nabla g, v \rangle -
Dg \, v = 0$. -/
theorem inner_graphNormal_fderiv_graphParam {x' : 𝔼'} (hg : DifferentiableAt ℝ g x') (v : 𝔼') :
    ⟪graphNormal T g (graphParam T g x'), fderiv ℝ (graphParam T g) x' v⟫_ℝ = 0 := by
  rw [fderiv_graphParam hg, graphNormal, init_apply_graphParam, inner_smul_left]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.inner_map_map,
    snocLastL_apply, inner_snocLast, inner_gradient_eq_fderiv]
  ring

/-- The point $x + t\nu$ in the frame $T$, for $x = \Phi(x')$ and $\nu$ the normal at $x$: with
$c = \sqrt{1 + |\nabla g(x')|^2}$,
$$T(x + t\nu) = \bigl(x' + (t/c) \nabla g(x'), \; g(x') - t/c\bigr).$$
-/
theorem apply_graphParam_add_smul_graphNormal (x' : 𝔼') (t : ℝ) :
    T (graphParam T g x' + t • graphNormal T g (graphParam T g x'))
      = snocLast (x' + (t * (graphDensity g x')⁻¹) • gradient g x')
          (g x' - t * (graphDensity g x')⁻¹) := by
  have h1 : ∀ (p w : 𝔼), T (p + w) = T.linearIsometryEquiv w + T p := fun p w ↦ by
    have := T.map_vadd p w
    rwa [vadd_eq_add, vadd_eq_add, add_comm w p] at this
  rw [h1, graphNormal, init_apply_graphParam, map_smul, map_smul,
    LinearIsometryEquiv.apply_symm_apply, graphParam, AffineIsometryEquiv.apply_symm_apply]
  ext i
  induction i using Fin.lastCases
  · simp only [PiLp.add_apply, PiLp.smul_apply, snocLast_apply_last, smul_eq_mul]
    ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, snocLast_apply_castSucc, smul_eq_mul]
    ring

/-- **The normal points out of the region above the graph.** Let $g$ be of class $C^1$, let
$x' \in \mathbb{R}^d$, and let $x = \Phi(x')$ with normal $\nu$ at $x$. Then for all
sufficiently small $t > 0$,
$$x + t\nu \notin T^{-1}(\{y : y_{d+1} > g(y')\}) \quad \text{and} \quad x - t\nu \in T^{-1}(\{y
  : y_{d+1} > g(y')\}).$$

In the frame $T$, the point $x + t\nu$ lies in the region if and only if $h(t) = g(x' + (t/c)
\nabla g(x')) - g(x') + t/c < 0$, where $c = \sqrt{1 + |\nabla g(x')|^2}$. Here $h(0) = 0$ and
$h'(0) = (\|\nabla g(x')\|^2 + 1)/c > 0$. -/
theorem graphNormal_outward (hg : ContDiff ℝ 1 g) (x' : 𝔼') :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      graphParam T g x' + t • graphNormal T g (graphParam T g x') ∉ T ⁻¹' epigraph g ∧
      graphParam T g x' - t • graphNormal T g (graphParam T g x') ∈ T ⁻¹' epigraph g := by
  set c := graphDensity g x' with hcdef
  set a := gradient g x' with hadef
  have hc : 0 < c := graphDensity_pos x'
  let h : ℝ → ℝ := fun t ↦ g (x' + (t * c⁻¹) • a) - g x' + t * c⁻¹
  have hmem : ∀ t : ℝ, graphParam T g x' + t • graphNormal T g (graphParam T g x')
      ∈ T ⁻¹' epigraph g ↔ h t < 0 := fun t ↦ by
    rw [mem_preimage, apply_graphParam_add_smul_graphNormal, snocLast_mem_epigraph]
    simp only [h]
    constructor <;> intro h <;> linarith
  have hline : HasDerivAt (fun t : ℝ ↦ x' + (t * c⁻¹) • a) (c⁻¹ • a) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const c⁻¹).smul_const a).const_add x'
    simpa using this
  have hg1 : HasDerivAt (fun t : ℝ ↦ g (x' + (t * c⁻¹) • a)) (fderiv ℝ g x' (c⁻¹ • a)) 0 := by
    have hgd : HasFDerivAt g (fderiv ℝ g x') (x' + ((0 : ℝ) * c⁻¹) • a) := by
      simpa using (hg.differentiable one_ne_zero x').hasFDerivAt
    exact hgd.comp_hasDerivAt 0 hline
  have hh : HasDerivAt h (c⁻¹ * ‖a‖ ^ 2 + c⁻¹) 0 := by
    have := (hg1.sub_const (g x')).add ((hasDerivAt_id (0 : ℝ)).mul_const c⁻¹)
    refine this.congr_deriv ?_
    rw [map_smul, smul_eq_mul, ← inner_gradient_eq_fderiv, ← hadef, real_inner_self_eq_norm_sq,
      one_mul]
  have hpos : 0 < c⁻¹ * ‖a‖ ^ 2 + c⁻¹ := by positivity
  have h0 : h 0 = 0 := by simp [h]
  filter_upwards [eventually_pos_and_neg_of_hasDerivAt_pos hh hpos h0] with t ⟨ht1, ht2⟩
  refine ⟨fun hmem' ↦ ?_, ?_⟩
  · rw [hmem] at hmem'
    linarith
  · rw [sub_eq_add_neg, ← neg_smul, hmem]
    exact ht2

end EuclideanSpace


namespace EuclideanSpace

/-! ### The transition between two graph charts -/

variable (T₁ : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  (g₁ : EuclideanSpace ℝ (Fin d) → ℝ)
  (T₂ : EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))

/-- **The transition between two graph charts**: for rigid motions $T_1, T_2$ and
$g_1 : \mathbb{R}^d \to \mathbb{R}$, the map
$$\psi(x') = \bigl(T_2 \Phi_1(x')\bigr)',$$
which gives the parameters in the second chart of the point with parameters $x'$ in the first
chart. Here $\Phi_1$ is the parametrization of the first chart.

Let $g_1, g_2$ be continuous, let $V$ be open, and let both charts describe the same set on $V$:
$V \cap T_1^{-1}(\{y_{d+1} > g_1(y')\}) = V \cap T_2^{-1}(\{y_{d+1} > g_2(y')\})$. Then $\psi$
is a bijection from $\Phi_1^{-1}(V)$ onto $\Phi_2^{-1}(V)$ with $\Phi_2 \circ \psi = \Phi_1$
there (`EuclideanSpace.graphParam_graphTransition`), and it is of class $C^1$ when $g_1$ is. -/
def graphTransition (x' : 𝔼') : 𝔼' := init (T₂ (graphParam T₁ g₁ x'))

variable {T₁ g₁ T₂} {g₂ : EuclideanSpace ℝ (Fin d) → ℝ} {V : Set (EuclideanSpace ℝ (Fin (d + 1)))}

/-- If $g_1$ is of class $C^n$, the transition $\psi$ is of class $C^n$. -/
theorem contDiff_graphTransition {n : WithTop ℕ∞} (hg₁ : ContDiff ℝ n g₁) :
    ContDiff ℝ n (graphTransition T₁ g₁ T₂) :=
  contDiff_init.comp ((contDiff_affineIsometryEquiv T₂).comp (contDiff_graphParam hg₁))

/-- If $g_1$ is continuous, the transition $\psi$ is continuous. -/
theorem continuous_graphTransition (hg₁ : Continuous g₁) :
    Continuous (graphTransition T₁ g₁ T₂) :=
  continuous_init.comp (T₂.continuous.comp (continuous_graphParam hg₁))

/-- Let $V$ be open, and let two charts describe the same set on $V$: $V \cap T_1^{-1}(\{y_{d+1} >
g_1(y')\}) = V \cap T_2^{-1}(\{y_{d+1} > g_2(y')\})$. Then the boundaries of the two regions
agree in $V$. -/
theorem frontier_inter_eq_of_inter_eq (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) :
    frontier (T₁ ⁻¹' epigraph g₁) ∩ V = frontier (T₂ ⁻¹' epigraph g₂) ∩ V := by
  have h1 : frontier (T₁ ⁻¹' epigraph g₁) ∩ V = frontier (V ∩ T₁ ⁻¹' epigraph g₁) ∩ V := by
    rw [inter_comm V, frontier_inter_open_inter hV]
  have h2 : frontier (T₂ ⁻¹' epigraph g₂) ∩ V = frontier (V ∩ T₂ ⁻¹' epigraph g₂) ∩ V := by
    rw [inter_comm V, frontier_inter_open_inter hV]
  rw [h1, h2, hΩ]

/-- **The transition reparametrizes.** Let $g_1, g_2$ be continuous, let $V$ be open, and let the
two charts describe the same set on $V$. Then $\Phi_2(\psi(x')) = \Phi_1(x')$ for every
$x' \in \Phi_1^{-1}(V)$. -/
theorem graphParam_graphTransition (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) {x' : 𝔼'}
    (hx' : x' ∈ graphParam T₁ g₁ ⁻¹' V) :
    graphParam T₂ g₂ (graphTransition T₁ g₁ T₂ x') = graphParam T₁ g₁ x' := by
  have h : graphParam T₁ g₁ x' ∈ frontier (T₂ ⁻¹' epigraph g₂) ∩ V := by
    rw [← frontier_inter_eq_of_inter_eq hV hΩ]
    exact ⟨graphParam_mem_frontier_epigraph hg₁ x', hx'⟩
  exact graphParam_eq_of_mem_frontier hg₂ h.1

/-- Let $g_1, g_2$ be continuous, let $V$ be open, and let the two charts describe the same set on
$V$. Then the transition $\psi$ maps $\Phi_1^{-1}(V)$ into $\Phi_2^{-1}(V)$. -/
theorem graphTransition_mapsTo (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) :
    MapsTo (graphTransition T₁ g₁ T₂) (graphParam T₁ g₁ ⁻¹' V) (graphParam T₂ g₂ ⁻¹' V) :=
  fun x' hx' ↦ by
    change graphParam T₂ g₂ (graphTransition T₁ g₁ T₂ x') ∈ V
    rw [graphParam_graphTransition hg₁ hg₂ hV hΩ hx']
    exact hx'

/-- Let $g_1, g_2$ be continuous, let $V$ be open, and let the two charts describe the same set on
$V$. Then the transition $\psi$ is injective on $\Phi_1^{-1}(V)$. -/
theorem graphTransition_injOn (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) :
    InjOn (graphTransition T₁ g₁ T₂) (graphParam T₁ g₁ ⁻¹' V) := fun x' hx' y' hy' h ↦ by
  apply graphParam_injective (T := T₁) (g := g₁)
  rw [← graphParam_graphTransition hg₁ hg₂ hV hΩ hx', h,
    graphParam_graphTransition hg₁ hg₂ hV hΩ hy']

/-- Let $g_1, g_2$ be continuous, let $V$ be open, and let the two charts describe the same set on
$V$. Then the transition from the second chart to the first is a right inverse of $\psi$ on
$\Phi_2^{-1}(V)$: $\psi(\psi_{21}(y')) = y'$ for $y' \in \Phi_2^{-1}(V)$, where $\psi_{21}$ is
the transition from the second chart to the first. -/
theorem graphTransition_graphTransition (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) {y' : 𝔼'}
    (hy' : y' ∈ graphParam T₂ g₂ ⁻¹' V) :
    graphTransition T₁ g₁ T₂ (graphTransition T₂ g₂ T₁ y') = y' := by
  rw [graphTransition, graphParam_graphTransition hg₂ hg₁ hV hΩ.symm hy', init_apply_graphParam]

/-- Let $g_1, g_2$ be continuous, let $V$ be open, and let the two charts describe the same set on
$V$. Then the transition $\psi$ maps $\Phi_1^{-1}(V)$ onto $\Phi_2^{-1}(V)$. -/
theorem graphTransition_image (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) :
    graphTransition T₁ g₁ T₂ '' (graphParam T₁ g₁ ⁻¹' V) = graphParam T₂ g₂ ⁻¹' V := by
  refine Subset.antisymm (graphTransition_mapsTo hg₁ hg₂ hV hΩ).image_subset fun y' hy' ↦ ?_
  exact ⟨graphTransition T₂ g₂ T₁ y', graphTransition_mapsTo hg₂ hg₁ hV hΩ.symm hy',
    graphTransition_graphTransition hg₁ hg₂ hV hΩ hy'⟩

/-- **The chain rule across the transition.** Let $g_1, g_2$ be of class $C^1$, let $V$ be open, and
let the two charts describe the same set on $V$. Then for every $x' \in \Phi_1^{-1}(V)$,
$$D\Phi_1(x') = D\Phi_2(\psi(x')) \circ D\psi(x').$$
-/
theorem fderiv_graphParam_comp (hg₁ : ContDiff ℝ 1 g₁) (hg₂ : ContDiff ℝ 1 g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) {x' : 𝔼'}
    (hx' : x' ∈ graphParam T₁ g₁ ⁻¹' V) :
    fderiv ℝ (graphParam T₁ g₁) x'
      = fderiv ℝ (graphParam T₂ g₂) (graphTransition T₁ g₁ T₂ x') ∘L
        fderiv ℝ (graphTransition T₁ g₁ T₂) x' := by
  have hD : graphParam T₁ g₁ ⁻¹' V ∈ 𝓝 x' :=
    (hV.preimage (continuous_graphParam hg₁.continuous)).mem_nhds hx'
  have heq : graphParam T₁ g₁ =ᶠ[𝓝 x'] graphParam T₂ g₂ ∘ graphTransition T₁ g₁ T₂ := by
    filter_upwards [hD] with y' hy'
    exact (graphParam_graphTransition hg₁.continuous hg₂.continuous hV hΩ hy').symm
  rw [heq.fderiv_eq]
  exact fderiv_comp x' ((contDiff_graphParam hg₂).differentiable one_ne_zero _)
    ((contDiff_graphTransition hg₁).differentiable one_ne_zero _)

/-- **The surface elements of two charts.** Let $g_1, g_2$ be of class $C^1$, let $V$ be open, and
let the two charts describe the same set on $V$. Then for every $x' \in \Phi_1^{-1}(V)$,
$$\sqrt{1 + |\nabla g_1(x')|^2} = \sqrt{1 + |\nabla g_2(\psi(x'))|^2} \, \bigl|\det
  D\psi(x')\bigr|.$$

This is the identity $\operatorname{gram} D(\Phi_2 \circ \psi) = (\operatorname{gram} D\Phi_2
\circ \psi) \, |\det D\psi|$ of `EuclideanSpace.gram_comp`. -/
theorem graphDensity_graphTransition (hg₁ : ContDiff ℝ 1 g₁) (hg₂ : ContDiff ℝ 1 g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) {x' : 𝔼'}
    (hx' : x' ∈ graphParam T₁ g₁ ⁻¹' V) :
    graphDensity g₁ x' = graphDensity g₂ (graphTransition T₁ g₁ T₂ x') *
      |LinearMap.det (fderiv ℝ (graphTransition T₁ g₁ T₂) x' : 𝔼' →ₗ[ℝ] 𝔼')| := by
  rw [graphDensity_eq_gram T₁ (hg₁.differentiable one_ne_zero _),
    graphDensity_eq_gram T₂ (hg₂.differentiable one_ne_zero _),
    fderiv_graphParam_comp hg₁ hg₂ hV hΩ hx', gram_comp]

/-! ### Chart independence of the local measure -/

/-- **The local surface measure does not depend on the chart.** Let $g_1, g_2$ be of class $C^1$,
let $V$ be open, and let the two charts describe the same set on $V$. Then the local surface
measures over the preimages of $V$ agree:
$$\sigma^{(1)}_{\Phi_1^{-1}(V)} = \sigma^{(2)}_{\Phi_2^{-1}(V)}.$$

The proof is the change of variables
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` along the transition, together
with `EuclideanSpace.graphDensity_graphTransition`. -/
theorem graphMeasure_eq_of_eq (hg₁ : ContDiff ℝ 1 g₁) (hg₂ : ContDiff ℝ 1 g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) :
    graphMeasure T₁ g₁ (graphParam T₁ g₁ ⁻¹' V) = graphMeasure T₂ g₂ (graphParam T₂ g₂ ⁻¹' V) := by
  have hc₁ := hg₁.continuous
  have hc₂ := hg₂.continuous
  have hψ := contDiff_graphTransition (T₁ := T₁) (T₂ := T₂) hg₁
  ext A hA
  rw [graphMeasure_apply hc₁ _ hA, graphMeasure_apply hc₂ _ hA]
  set s := graphParam T₁ g₁ ⁻¹' V ∩ graphParam T₁ g₁ ⁻¹' A with hsdef
  have hs : MeasurableSet s :=
    (hV.preimage (continuous_graphParam hc₁)).measurableSet.inter
      (hA.preimage (continuous_graphParam hc₁).measurable)
  have himage : graphParam T₂ g₂ ⁻¹' V ∩ graphParam T₂ g₂ ⁻¹' A
      = graphTransition T₁ g₁ T₂ '' s := by
    ext y'
    constructor
    · rintro ⟨hy'V, hy'A⟩
      refine ⟨graphTransition T₂ g₂ T₁ y', ⟨graphTransition_mapsTo hc₂ hc₁ hV hΩ.symm hy'V, ?_⟩,
        graphTransition_graphTransition hc₁ hc₂ hV hΩ hy'V⟩
      change graphParam T₁ g₁ (graphTransition T₂ g₂ T₁ y') ∈ A
      rwa [graphParam_graphTransition hc₂ hc₁ hV hΩ.symm hy'V]
    · rintro ⟨x', ⟨hx'V, hx'A⟩, rfl⟩
      refine ⟨graphTransition_mapsTo hc₁ hc₂ hV hΩ hx'V, ?_⟩
      change graphParam T₂ g₂ (graphTransition T₁ g₁ T₂ x') ∈ A
      rwa [graphParam_graphTransition hc₁ hc₂ hV hΩ hx'V]
  rw [himage, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x' _ ↦ (hψ.differentiable one_ne_zero x').hasFDerivAt.hasFDerivWithinAt)
    ((graphTransition_injOn hc₁ hc₂ hV hΩ).mono inter_subset_left)]
  refine setLIntegral_congr_fun hs fun x' hx' ↦ ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm,
    ← graphDensity_graphTransition hg₁ hg₂ hV hΩ hx'.1]

/-! ### Chart independence of the normal -/

/-- Let $a \in \mathbb{R}^d$ and $z \in \mathbb{R}^{d+1}$. If $z$ is orthogonal to every vector
$(v, \langle a, v \rangle)$, $v \in \mathbb{R}^d$, and to $(a, -1)$, then $z = 0$. -/
theorem eq_zero_of_inner_snocLast_eq_zero {a : 𝔼'} {z : 𝔼}
    (h1 : ∀ v, ⟪z, snocLast v ⟪a, v⟫_ℝ⟫_ℝ = 0) (h2 : ⟪z, snocLast a (-1)⟫_ℝ = 0) : z = 0 := by
  have hz : z = snocLast (init z) (z (Fin.last d)) := (snocLast_init_last z).symm
  set w := init z
  set s := z (Fin.last d)
  rw [hz] at h1 h2
  simp only [inner_snocLast] at h1 h2
  have h3 : w + s • a = 0 := by
    have := h1 (w + s • a)
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial]
      at this ⊢
    linear_combination this
  have h4 : w = -(s • a) := eq_neg_of_add_eq_zero_left h3
  rw [h4, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq] at h2
  simp only [conj_trivial] at h2
  have h5 : s * (‖a‖ ^ 2 + 1) = 0 := by linarith
  have hs : s = 0 := by
    rcases mul_eq_zero.1 h5 with h | h
    · exact h
    · nlinarith [sq_nonneg ‖a‖]
  rw [hz, hs, h4, hs, zero_smul, neg_zero]
  ext i
  induction i using Fin.lastCases <;> simp

/-- **The normal does not depend on the chart.** Let $g_1, g_2$ be of class $C^1$, let $V$ be open,
and let the two charts describe the same set on $V$. Then at every point $x$ of $V$ on the
boundary of $T_1^{-1}(\{y_{d+1} > g_1(y')\})$, the two normals agree: $\nu_1(x) = \nu_2(x)$.

Both normals are unit vectors orthogonal to the tangent space of the first chart
(`EuclideanSpace.inner_graphNormal_fderiv_graphParam`, `EuclideanSpace.fderiv_graphParam_comp`).
So $\nu_2 = \langle \nu_2, \nu_1 \rangle \nu_1$ by
`EuclideanSpace.eq_zero_of_inner_snocLast_eq_zero` in the first frame, with
$\langle \nu_2, \nu_1 \rangle = \pm 1$. The sign $-1$ would put $x + t\nu_1 = x - t\nu_2$ both
inside and outside the set for small $t > 0$ (`EuclideanSpace.graphNormal_outward` for each
chart). -/
theorem graphNormal_eq_of_eq (hg₁ : ContDiff ℝ 1 g₁) (hg₂ : ContDiff ℝ 1 g₂) (hV : IsOpen V)
    (hΩ : V ∩ T₁ ⁻¹' epigraph g₁ = V ∩ T₂ ⁻¹' epigraph g₂) {x : 𝔼}
    (hx : x ∈ frontier (T₁ ⁻¹' epigraph g₁) ∩ V) :
    graphNormal T₁ g₁ x = graphNormal T₂ g₂ x := by
  have hc₁ := hg₁.continuous
  have hc₂ := hg₂.continuous
  set x₁ := init (T₁ x) with hx₁def
  have hxeq : graphParam T₁ g₁ x₁ = x := graphParam_eq_of_mem_frontier hc₁ hx.1
  have hx₁ : x₁ ∈ graphParam T₁ g₁ ⁻¹' V := by
    change graphParam T₁ g₁ x₁ ∈ V
    rw [hxeq]; exact hx.2
  have hxeq₂ : graphParam T₂ g₂ (graphTransition T₁ g₁ T₂ x₁) = x := by
    rw [graphParam_graphTransition hc₁ hc₂ hV hΩ hx₁, hxeq]
  set ν₁ := graphNormal T₁ g₁ x with hν₁
  set ν₂ := graphNormal T₂ g₂ x with hν₂
  -- both normals are orthogonal to the tangent space of chart 1
  have horth₁ : ∀ v, ⟪ν₁, fderiv ℝ (graphParam T₁ g₁) x₁ v⟫_ℝ = 0 := fun v ↦ by
    rw [hν₁, ← hxeq]
    exact inner_graphNormal_fderiv_graphParam (hg₁.differentiable one_ne_zero _) v
  have horth₂ : ∀ v, ⟪ν₂, fderiv ℝ (graphParam T₁ g₁) x₁ v⟫_ℝ = 0 := fun v ↦ by
    rw [hν₂, ← hxeq₂, fderiv_graphParam_comp hg₁ hg₂ hV hΩ hx₁, ContinuousLinearMap.comp_apply]
    exact inner_graphNormal_fderiv_graphParam (hg₂.differentiable one_ne_zero _) _
  -- hence `ν₂ = ⟪ν₂, ν₁⟫ ν₁`
  set c := ⟪ν₂, ν₁⟫_ℝ with hcdef
  have hν₁' : T₁.linearIsometryEquiv.symm (snocLast (gradient g₁ x₁) (-1))
      = graphDensity g₁ x₁ • ν₁ := by
    rw [hν₁, graphNormal, ← hx₁def, smul_smul, mul_inv_cancel₀ (graphDensity_ne_zero _), one_smul]
  have hz : T₁.linearIsometryEquiv (ν₂ - c • ν₁) = 0 := by
    refine eq_zero_of_inner_snocLast_eq_zero (a := gradient g₁ x₁) (fun v ↦ ?_) ?_
    · have hD : fderiv ℝ (graphParam T₁ g₁) x₁ v
          = T₁.linearIsometryEquiv.symm (snocLast v ⟪gradient g₁ x₁, v⟫_ℝ) := by
        rw [fderiv_graphParam (hg₁.differentiable one_ne_zero _), inner_gradient_eq_fderiv]
        rfl
      rw [← LinearIsometryEquiv.inner_map_map T₁.linearIsometryEquiv.symm,
        LinearIsometryEquiv.symm_apply_apply, ← hD, inner_sub_left, inner_smul_left, horth₁,
        horth₂]
      simp
    · rw [← LinearIsometryEquiv.inner_map_map T₁.linearIsometryEquiv.symm,
        LinearIsometryEquiv.symm_apply_apply, hν₁', inner_smul_right, inner_sub_left,
        inner_smul_left, real_inner_self_eq_norm_sq, norm_graphNormal, ← hcdef]
      simp
  have hν₂c : ν₂ = c • ν₁ := by
    have := (LinearIsometryEquiv.map_eq_zero_iff _).1 hz
    exact sub_eq_zero.1 this
  -- `|c| = 1`
  have hc1 : |c| = 1 := by
    have := norm_graphNormal (T := T₂) (g := g₂) x
    rw [← hν₂, hν₂c, norm_smul, norm_graphNormal, mul_one, Real.norm_eq_abs] at this
    exact this
  rcases abs_eq (zero_le_one) |>.1 hc1 with hc | hc
  · rw [hν₂c, hc, one_smul]
  -- the case `c = -1` contradicts the outward orientation of both normals
  exfalso
  have hout₁ := graphNormal_outward (T := T₁) hg₁ x₁
  have hout₂ := graphNormal_outward (T := T₂) hg₂ (graphTransition T₁ g₁ T₂ x₁)
  rw [hxeq] at hout₁
  rw [hxeq₂] at hout₂
  have hV' : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • ν₁ ∈ V := by
    have ht : Tendsto (fun t : ℝ ↦ x + t • ν₁) (𝓝[>] 0) (𝓝 x) := by
      have : Tendsto (fun t : ℝ ↦ x + t • ν₁) (𝓝 0) (𝓝 (x + (0 : ℝ) • ν₁)) :=
        tendsto_const_nhds.add (tendsto_id.smul_const ν₁)
      rw [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact ht.eventually (hV.mem_nhds hx.2)
  obtain ⟨t, ⟨h1, _⟩, ⟨_, h2⟩, h3⟩ := (hout₁.and (hout₂.and hV')).exists
  apply h1
  have h4 : x - t • ν₂ = x + t • ν₁ := by
    rw [hν₂c, hc, neg_one_smul, smul_neg, sub_neg_eq_add]
  rw [h4] at h2
  have h5 : x + t • ν₁ ∈ V ∩ T₂ ⁻¹' epigraph g₂ := ⟨h3, h2⟩
  rw [← hΩ] at h5
  exact h5.2

end EuclideanSpace


/-! ### Atlases: finitely many graph charts with a partition of unity -/

/-- **A finite graph atlas of $\Omega \subseteq \mathbb{R}^{d+1}$ with a subordinate partition of
unity**, the data from which the surface measure and the outward normal are built. It consists
of $k$ balls $B(x_i, r_i)$ with centres on $\partial\Omega$ and $r_i > 0$ that cover
$\partial\Omega$, such that in each ball $\Omega$ is the region above the graph of a $C^1$
function $g_i$ in the frame of a rigid motion $T_i$, and of smooth functions
$\theta_0, \theta_i$ with values in $[0, 1]$ and $\theta_0 + \sum_i \theta_i = 1$, where each
$\theta_i$ has compact support inside its ball and the support of $\theta_0$ is disjoint from
$\partial\Omega$.

The partition of unity is that of Lemma 9.3 of [brezis2011functional]. The function $\theta_0$
is needed by the proof of the divergence theorem, so that $\theta_0 F$ has compact support
inside $\Omega$. -/
structure GraphAtlas (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))) where
  /-- The number $k$ of charts. -/
  k : ℕ
  /-- The centres $x_i$ of the chart balls. -/
  x : Fin k → EuclideanSpace ℝ (Fin (d + 1))
  /-- The radii $r_i$ of the chart balls. -/
  r : Fin k → ℝ
  /-- The rigid motions $T_i$ of the charts. -/
  T : Fin k → (EuclideanSpace ℝ (Fin (d + 1)) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
  /-- The graph functions $g_i : \mathbb{R}^d \to \mathbb{R}$ of the charts. -/
  g : Fin k → (EuclideanSpace ℝ (Fin d) → ℝ)
  /-- The interior piece $\theta_0$ of the partition of unity. -/
  θ₀ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ
  /-- The pieces $\theta_i$ of the partition of unity subordinate to the balls. -/
  θ : Fin k → EuclideanSpace ℝ (Fin (d + 1)) → ℝ
  /-- Each centre $x_i$ lies on $\partial\Omega$. -/
  x_mem_frontier : ∀ i, x i ∈ frontier Ω
  /-- Each radius $r_i$ is positive. -/
  r_pos : ∀ i, 0 < r i
  /-- Each graph function $g_i$ is of class $C^1$. -/
  contDiff_g : ∀ i, ContDiff ℝ 1 (g i)
  /-- In each ball, $\Omega$ is the region above the graph of $g_i$ in the frame $T_i$: $\Omega \cap
  B(x_i, r_i) = B(x_i, r_i) \cap T_i^{-1}(\{y : y_{d+1} > g_i(y')\})$. -/
  inter_ball_eq : ∀ i, Ω ∩ Metric.ball (x i) (r i)
    = Metric.ball (x i) (r i) ∩ T i ⁻¹' EuclideanSpace.epigraph (g i)
  /-- The balls cover $\partial\Omega$. -/
  frontier_subset : frontier Ω ⊆ ⋃ i, Metric.ball (x i) (r i)
  /-- The interior piece $\theta_0$ is of class $C^\infty$. -/
  contDiff_θ₀ : ContDiff ℝ ∞ θ₀
  /-- Each piece $\theta_i$ is of class $C^\infty$. -/
  contDiff_θ : ∀ i, ContDiff ℝ ∞ (θ i)
  /-- The interior piece $\theta_0$ takes values in $[0, 1]$. -/
  θ₀_mem_Icc : ∀ y, θ₀ y ∈ Icc (0 : ℝ) 1
  /-- Each piece $\theta_i$ takes values in $[0, 1]$. -/
  θ_mem_Icc : ∀ i y, θ i y ∈ Icc (0 : ℝ) 1
  /-- The pieces sum to one: $\theta_0 + \sum_i \theta_i = 1$ everywhere. -/
  θ₀_add_sum_θ : ∀ y, θ₀ y + ∑ i, θ i y = 1
  /-- Each piece $\theta_i$ has compact support. -/
  hasCompactSupport_θ : ∀ i, HasCompactSupport (θ i)
  /-- The support of each piece $\theta_i$ lies in the ball $B(x_i, r_i)$. -/
  tsupport_θ_subset : ∀ i, tsupport (θ i) ⊆ Metric.ball (x i) (r i)
  /-- The support of the interior piece $\theta_0$ is disjoint from $\partial\Omega$. -/
  disjoint_tsupport_θ₀ : Disjoint (tsupport θ₀) (frontier Ω)

namespace GraphAtlas

variable {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))} (a : GraphAtlas Ω)

/-- The interior piece $\theta_0$ vanishes on $\partial\Omega$. -/
theorem θ₀_eq_zero {y : 𝔼} (hy : y ∈ frontier Ω) : a.θ₀ y = 0 :=
  image_eq_zero_of_notMem_tsupport (disjoint_right.1 a.disjoint_tsupport_θ₀ hy)

/-- On $\partial\Omega$ the pieces subordinate to the balls sum to one: $\sum_i \theta_i(y) = 1$ for
$y \in \partial\Omega$. -/
theorem sum_θ {y : 𝔼} (hy : y ∈ frontier Ω) : ∑ i, a.θ i y = 1 := by
  have := a.θ₀_add_sum_θ y
  rwa [a.θ₀_eq_zero hy, zero_add] at this

/-- The piece $\theta_i$ vanishes outside the ball $B(x_i, r_i)$. -/
theorem θ_eq_zero (i : Fin a.k) {y : 𝔼} (hy : y ∉ Metric.ball (a.x i) (a.r i)) : a.θ i y = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hy (a.tsupport_θ_subset i h)

/-- Each piece $\theta_i$ is nonnegative. -/
theorem θ_nonneg (i : Fin a.k) (y : 𝔼) : 0 ≤ a.θ i y := (a.θ_mem_Icc i y).1

/-- Each piece $\theta_i$ is at most $1$. -/
theorem θ_le_one (i : Fin a.k) (y : 𝔼) : a.θ i y ≤ 1 := (a.θ_mem_Icc i y).2

/-- Each piece $\theta_i$, as a function with values in $[0, \infty]$, is measurable. -/
theorem measurable_ofReal_θ (i : Fin a.k) : Measurable fun y ↦ ENNReal.ofReal (a.θ i y) :=
  ENNReal.measurable_ofReal.comp (a.contDiff_θ i).continuous.measurable

/-- Every point of $\partial\Omega$ lies in some chart ball $B(x_i, r_i)$. -/
theorem exists_mem_ball {y : 𝔼} (hy : y ∈ frontier Ω) : ∃ i, y ∈ Metric.ball (a.x i) (a.r i) :=
  mem_iUnion.1 (a.frontier_subset hy)

/-- If $\Omega$ has a graph atlas, then $\partial\Omega$ is compact: it is closed and covered by
finitely many balls. -/
theorem isCompact_frontier (a : GraphAtlas Ω) : IsCompact (frontier Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    ((Bornology.isBounded_iUnion.2 fun _ ↦ Metric.isBounded_ball).subset a.frontier_subset)

/-- The parameter domain $D_i = \Phi_i^{-1}(B(x_i, r_i))$ of the $i$-th chart, where $\Phi_i$ is the
parametrization of that chart. -/
def graphDomain (i : Fin a.k) : Set 𝔼' :=
  EuclideanSpace.graphDomain (a.T i) (a.g i) (a.x i) (a.r i)

/-- The parameter domain of the $i$-th chart is $\Phi_i^{-1}(B(x_i, r_i))$. -/
theorem graphDomain_eq (i : Fin a.k) :
    a.graphDomain i = EuclideanSpace.graphParam (a.T i) (a.g i) ⁻¹' Metric.ball (a.x i) (a.r i) :=
  rfl

/-- The local surface measure $\sigma_i$ of the $i$-th chart, over its parameter domain $D_i$. -/
def localMeasure (i : Fin a.k) : Measure 𝔼 :=
  EuclideanSpace.graphMeasure (a.T i) (a.g i) (a.graphDomain i)

/-- The local surface measure of the $i$-th chart is `EuclideanSpace.graphMeasure` of the chart data
over its parameter domain. -/
theorem localMeasure_eq (i : Fin a.k) :
    a.localMeasure i = EuclideanSpace.graphMeasure (a.T i) (a.g i) (a.graphDomain i) :=
  rfl

/-- **The surface measure of the atlas**: the local surface measures glued by the partition of
unity,
$$\sigma = \sum_i \theta_i \, \sigma_i,$$
where $\theta_i \sigma_i$ is the measure with density $\theta_i$ with respect to $\sigma_i$. -/
def measure : Measure 𝔼 :=
  ∑ i, (a.localMeasure i).withDensity fun y ↦ ENNReal.ofReal (a.θ i y)

/-- The surface measure of the atlas is $\sum_i \theta_i \sigma_i$. -/
theorem measure_eq_sum :
    a.measure = ∑ i, (a.localMeasure i).withDensity fun y ↦ ENNReal.ofReal (a.θ i y) :=
  rfl

/-- The $i$-th local measure is carried by $\partial\Omega$: $\sigma_i((\partial\Omega)^c) = 0$. In
fact it is carried by $\partial\Omega \cap B(x_i, r_i)$. -/
theorem localMeasure_compl_frontier (i : Fin a.k) : a.localMeasure i (frontier Ω)ᶜ = 0 := by
  refine measure_mono_null (compl_subset_compl.2 ?_)
    (EuclideanSpace.graphMeasure_compl_image (a.contDiff_g i).continuous
      (EuclideanSpace.measurableSet_graphDomain (a.contDiff_g i).continuous _ _))
  rw [graphDomain, IsBoundaryGraphAt.graphParam_image_graphDomain (a.contDiff_g i).continuous
    (a.inter_ball_eq i)]
  exact inter_subset_left

instance isFiniteMeasure_localMeasure (i : Fin a.k) : IsFiniteMeasure (a.localMeasure i) :=
  EuclideanSpace.isFiniteMeasure_graphMeasure (a.contDiff_g i)
    (EuclideanSpace.isBounded_graphDomain _ _)

instance isFiniteMeasure_measure : IsFiniteMeasure a.measure := by
  unfold measure
  have : ∀ i : Fin a.k, IsFiniteMeasure ((a.localMeasure i).withDensity
      fun y ↦ ENNReal.ofReal (a.θ i y)) := fun i ↦ by
    refine isFiniteMeasure_withDensity (ne_of_lt ?_)
    calc ∫⁻ y, ENNReal.ofReal (a.θ i y) ∂(a.localMeasure i)
        ≤ ∫⁻ _, 1 ∂(a.localMeasure i) :=
          lintegral_mono fun y ↦ by
            simpa using ENNReal.ofReal_le_ofReal (a.θ_le_one i y)
      _ < ⊤ := by simp [measure_lt_top]
  infer_instance

/-- The surface measure of the atlas is carried by $\partial\Omega$:
$\sigma((\partial\Omega)^c) = 0$. -/
theorem measure_compl_frontier : a.measure (frontier Ω)ᶜ = 0 := by
  rw [measure, Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  exact withDensity_absolutelyContinuous _ _ (a.localMeasure_compl_frontier i)

/-- Almost every point for the surface measure of the atlas lies on $\partial\Omega$. -/
theorem ae_mem_frontier : ∀ᵐ y ∂a.measure, y ∈ frontier Ω :=
  (measure_eq_zero_iff_ae_notMem.1 a.measure_compl_frontier).mono fun _ h ↦ not_not.1 h

/-- Every function $f$ with values in a normed group that is continuous on $\partial\Omega$ is
integrable for the surface measure of the atlas. -/
theorem integrable_of_continuousOn {G : Type*} [NormedAddCommGroup G] {f : 𝔼 → G}
    (hf : ContinuousOn f (frontier Ω)) : Integrable f a.measure := by
  have := hf.integrableOn_compact (μ := a.measure) a.isCompact_frontier
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem a.ae_mem_frontier] at this

/-- Each term $\theta_i \sigma_i$ is at most the surface measure of the atlas. -/
theorem withDensity_localMeasure_le (i : Fin a.k) :
    (a.localMeasure i).withDensity (fun y ↦ ENNReal.ofReal (a.θ i y)) ≤ a.measure :=
  Finset.single_le_sum (f := fun j ↦ (a.localMeasure j).withDensity
    fun y ↦ ENNReal.ofReal (a.θ j y)) (fun _ _ ↦ bot_le) (Finset.mem_univ i)

/-- For $f$ integrable for the surface measure of the atlas, with values in a real normed space,
$$\int f \, d\sigma = \sum_i \int \theta_i \, f \, d\sigma_i.$$
-/
theorem integral_measure_eq_sum {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : 𝔼 → G}
    (hf : Integrable f a.measure) :
    ∫ y, f y ∂a.measure = ∑ i, ∫ y, a.θ i y • f y ∂(a.localMeasure i) := by
  rw [measure,
    integral_finsetSum_measure fun i _ ↦ hf.mono_measure (a.withDensity_localMeasure_le i)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hm : Measurable fun y ↦ (a.θ i y).toNNReal :=
    (a.contDiff_θ i).continuous.measurable.real_toNNReal
  have h1 := integral_withDensity_eq_integral_smul (μ := a.localMeasure i) hm f
  simp only [ENNReal.ofReal] at h1 ⊢
  rw [h1]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (a.θ_nonneg i _)]

/-- **The integral against the atlas measure, in the parameters of the charts.** For $f$ integrable
for the surface measure of the atlas, with values in a real normed space,
$$\int f \, d\sigma = \sum_i \int_{D_i} \sqrt{1 + |\nabla g_i(x')|^2} \; \theta_i(\Phi_i(x')) \,
  f(\Phi_i(x')) \, dx',$$
where $\Phi_i$ is the parametrization and $D_i$ the parameter domain of the $i$-th chart. -/
theorem integral_measure {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : 𝔼 → G}
    (hf : Integrable f a.measure) :
    ∫ y, f y ∂a.measure = ∑ i, ∫ x' in a.graphDomain i,
      (EuclideanSpace.graphDensity (a.g i) x' *
        a.θ i (EuclideanSpace.graphParam (a.T i) (a.g i) x')) •
          f (EuclideanSpace.graphParam (a.T i) (a.g i) x') := by
  rw [a.integral_measure_eq_sum hf]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hm : Measurable fun y ↦ (a.θ i y).toNNReal :=
    (a.contDiff_θ i).continuous.measurable.real_toNNReal
  have h2 : AEStronglyMeasurable (fun y ↦ a.θ i y • f y) (a.localMeasure i) := by
    have := (hf.mono_measure (a.withDensity_localMeasure_le i)).aestronglyMeasurable
    simp only [ENNReal.ofReal] at this
    have h3 := (aestronglyMeasurable_withDensity_iff hm).1 this
    simpa only [NNReal.smul_def, Real.coe_toNNReal _ (a.θ_nonneg i _)] using h3
  rw [localMeasure, EuclideanSpace.integral_graphMeasure (a.contDiff_g i) _ h2]
  refine setIntegral_congr_fun (EuclideanSpace.measurableSet_graphDomain (a.contDiff_g i).continuous
    _ _) fun x' _ ↦ ?_
  simp only [smul_smul]

/-- **The partition of unity glues a measure carried by $\partial\Omega$ back to itself.** For every
measure $\mu$ on $\mathbb{R}^{d+1}$ with $\mu((\partial\Omega)^c) = 0$,
$$\sum_i \theta_i \, \mu|_{B(x_i, r_i)} = \mu.$$

This is the step behind the chart characterization of the atlas measure and its independence of
the atlas. -/
theorem sum_withDensity_restrict_eq {μ : Measure 𝔼} (hμ : μ (frontier Ω)ᶜ = 0) :
    ∑ i, (μ.restrict (Metric.ball (a.x i) (a.r i))).withDensity (fun y ↦ ENNReal.ofReal (a.θ i y))
      = μ := by
  have h1 : ∀ i, (μ.restrict (Metric.ball (a.x i) (a.r i))).withDensity
      (fun y ↦ ENNReal.ofReal (a.θ i y)) = μ.withDensity fun y ↦ ENNReal.ofReal (a.θ i y) := by
    intro i
    rw [← restrict_withDensity measurableSet_ball]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have h0 : (μ.withDensity fun y ↦ ENNReal.ofReal (a.θ i y)) (Metric.ball (a.x i) (a.r i))ᶜ
        = 0 := by
      rw [withDensity_apply _ measurableSet_ball.compl]
      exact setLIntegral_eq_zero measurableSet_ball.compl fun y hy ↦ by simp [a.θ_eq_zero i hy]
    exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun _ h ↦ not_not.1 h
  simp_rw [h1]
  have h2 : (∑ i, μ.withDensity fun y ↦ ENNReal.ofReal (a.θ i y))
      = μ.withDensity fun y ↦ ∑ i, ENNReal.ofReal (a.θ i y) := by
    ext A hA
    rw [Measure.finsetSum_apply, withDensity_apply _ hA,
      lintegral_finsetSum _ fun i _ ↦ a.measurable_ofReal_θ i]
    exact Finset.sum_congr rfl fun i _ ↦ withDensity_apply _ hA
  rw [h2]
  have h3 : (fun y ↦ ∑ i, ENNReal.ofReal (a.θ i y)) =ᵐ[μ] 1 := by
    have hμ' : ∀ᵐ y ∂μ, y ∈ frontier Ω :=
      (measure_eq_zero_iff_ae_notMem.1 hμ).mono fun _ h ↦ not_not.1 h
    filter_upwards [hμ'] with y hy
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ a.θ_nonneg i y, a.sum_θ hy]
    simp
  rw [withDensity_congr_ae h3, withDensity_one]

/-- **The chart characterization of the atlas measure.** Let $(T, g)$ be any graph chart of $\Omega$
at $(x_0, r)$: $g$ of class $C^1$ and $\Omega \cap B(x_0, r) = B(x_0, r) \cap T^{-1}(\{y :
y_{d+1} > g(y')\})$. Then the restriction of the atlas measure to $B(x_0, r)$ is the local
surface measure of the chart over its parameter domain $\Phi^{-1}(B(x_0, r))$.

Each local measure restricted to $B(x_0, r)$ is the local measure of the chart restricted to the
ball of the atlas chart (`EuclideanSpace.graphMeasure_eq_of_eq` on the intersection of the
balls), and the partition of unity glues these pieces
(`GraphAtlas.sum_withDensity_restrict_eq`). -/
theorem measure_restrict_ball {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g : 𝔼' → ℝ} (hg : ContDiff ℝ 1 g) {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g) :
    a.measure.restrict (Metric.ball x₀ r)
      = EuclideanSpace.graphMeasure T g (EuclideanSpace.graphDomain T g x₀ r) := by
  set ν := EuclideanSpace.graphMeasure T g (EuclideanSpace.graphDomain T g x₀ r) with hνdef
  have hν : ν (frontier Ω)ᶜ = 0 := by
    refine measure_mono_null (compl_subset_compl.2 ?_)
      (EuclideanSpace.graphMeasure_compl_image hg.continuous
        (EuclideanSpace.measurableSet_graphDomain hg.continuous _ _))
    rw [IsBoundaryGraphAt.graphParam_image_graphDomain hg.continuous h]
    exact inter_subset_left
  have hkey : ∀ i, (a.localMeasure i).restrict (Metric.ball x₀ r)
      = ν.restrict (Metric.ball (a.x i) (a.r i)) := by
    intro i
    rw [localMeasure, hνdef,
      EuclideanSpace.graphMeasure_restrict (a.contDiff_g i).continuous _ measurableSet_ball,
      EuclideanSpace.graphMeasure_restrict hg.continuous _ measurableSet_ball,
      graphDomain_eq, EuclideanSpace.graphDomain, ← preimage_inter, ← preimage_inter,
      inter_comm (Metric.ball x₀ r)]
    exact EuclideanSpace.graphMeasure_eq_of_eq (a.contDiff_g i) hg
      (Metric.isOpen_ball.inter Metric.isOpen_ball)
      (EuclideanSpace.inter_inter_preimage_epigraph_eq (a.inter_ball_eq i) h)
  calc a.measure.restrict (Metric.ball x₀ r)
      = ∑ i, ((a.localMeasure i).withDensity fun y ↦ ENNReal.ofReal (a.θ i y)).restrict
          (Metric.ball x₀ r) := by
        rw [measure]
        ext A hA
        simp only [Measure.restrict_apply hA, Measure.finsetSum_apply]
    _ = ∑ i, ((a.localMeasure i).restrict (Metric.ball x₀ r)).withDensity
          fun y ↦ ENNReal.ofReal (a.θ i y) := by
        simp_rw [restrict_withDensity measurableSet_ball]
    _ = ∑ i, (ν.restrict (Metric.ball (a.x i) (a.r i))).withDensity
          fun y ↦ ENNReal.ofReal (a.θ i y) := by
        simp_rw [hkey]
    _ = ν := a.sum_withDensity_restrict_eq hν

/-- **A measure carried by $\partial\Omega$ that agrees with the local measures on the atlas balls
is the atlas measure.** If $\mu((\partial\Omega)^c) = 0$ and $\mu|_{B(x_i, r_i)} = \sigma_i$ for
every $i$, then $\mu = \sigma$. -/
theorem measure_eq_of_forall_restrict_ball {μ : Measure 𝔼} (hμ : μ (frontier Ω)ᶜ = 0)
    (h : ∀ i, μ.restrict (Metric.ball (a.x i) (a.r i)) = a.localMeasure i) : μ = a.measure := by
  rw [measure_eq_sum]
  simp_rw [← h]
  exact (a.sum_withDensity_restrict_eq hμ).symm

/-- **The atlas measure does not depend on the atlas**: two graph atlases of $\Omega$ have the same
surface measure. -/
theorem measure_eq (a a' : GraphAtlas Ω) : a.measure = a'.measure :=
  a'.measure_eq_of_forall_restrict_ball a.measure_compl_frontier fun i ↦
    a.measure_restrict_ball (a'.contDiff_g i) (a'.inter_ball_eq i)

/-! ### The normal of an atlas -/

open Classical in
/-- **The outward normal of the atlas**: at a point $y$ in some chart ball, the normal
`EuclideanSpace.graphNormal` of one such chart, chosen; at a point in no chart ball, $0$.

On $\partial\Omega$ the value does not depend on the chosen chart
(`GraphAtlas.normal_eq_graphNormal`). -/
def normal (y : 𝔼) : 𝔼 :=
  if h : ∃ i, y ∈ Metric.ball (a.x i) (a.r i) then
    EuclideanSpace.graphNormal (a.T (Classical.choose h)) (a.g (Classical.choose h)) y
  else 0

/-- On $\partial\Omega \cap B(x_i, r_i)$ the atlas normal is the normal of the $i$-th chart,
whichever chart the definition chose (`EuclideanSpace.graphNormal_eq_of_eq`). -/
theorem normal_eq_graphNormal {y : 𝔼} (hy : y ∈ frontier Ω) {i : Fin a.k}
    (hi : y ∈ Metric.ball (a.x i) (a.r i)) :
    a.normal y = EuclideanSpace.graphNormal (a.T i) (a.g i) y := by
  have h : ∃ i, y ∈ Metric.ball (a.x i) (a.r i) := ⟨i, hi⟩
  rw [normal, dite_eq_left h]
  set j := Classical.choose h
  have hj : y ∈ Metric.ball (a.x j) (a.r j) := Classical.choose_spec h
  refine EuclideanSpace.graphNormal_eq_of_eq (a.contDiff_g j) (a.contDiff_g i)
    (Metric.isOpen_ball.inter Metric.isOpen_ball)
    (EuclideanSpace.inter_inter_preimage_epigraph_eq (a.inter_ball_eq j) (a.inter_ball_eq i))
    ⟨?_, hj, hi⟩
  exact EuclideanSpace.mem_frontier_preimage_epigraph_of_mem_frontier (a.contDiff_g j).continuous
    (a.inter_ball_eq j) hy hj

/-- **The chart characterization of the atlas normal.** Let $(T, g)$ be any graph chart of $\Omega$
at $(x_0, r)$: $g$ of class $C^1$ and $\Omega \cap B(x_0, r) = B(x_0, r) \cap T^{-1}(\{y :
y_{d+1} > g(y')\})$. Then at every $y \in \partial\Omega \cap B(x_0, r)$, the atlas normal is
the normal of the chart $(T, g)$. -/
theorem normal_eq_graphNormal_of_inter_eq {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g : 𝔼' → ℝ} (hg : ContDiff ℝ 1 g)
    {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    {y : 𝔼} (hy : y ∈ frontier Ω) (hyB : y ∈ Metric.ball x₀ r) :
    a.normal y = EuclideanSpace.graphNormal T g y := by
  obtain ⟨i, hi⟩ := a.exists_mem_ball hy
  rw [a.normal_eq_graphNormal hy hi]
  refine EuclideanSpace.graphNormal_eq_of_eq (a.contDiff_g i) hg
    (Metric.isOpen_ball.inter Metric.isOpen_ball)
    (EuclideanSpace.inter_inter_preimage_epigraph_eq (a.inter_ball_eq i) h) ⟨?_, hi, hyB⟩
  exact EuclideanSpace.mem_frontier_preimage_epigraph_of_mem_frontier (a.contDiff_g i).continuous
    (a.inter_ball_eq i) hy hi

/-- **The atlas normal does not depend on the atlas** on $\partial\Omega$: two graph atlases of
$\Omega$ have the same normal at every point of $\partial\Omega$. -/
theorem normal_eq_of_mem_frontier (a a' : GraphAtlas Ω) {y : 𝔼} (hy : y ∈ frontier Ω) :
    a.normal y = a'.normal y := by
  obtain ⟨i, hi⟩ := a'.exists_mem_ball hy
  rw [a'.normal_eq_graphNormal hy hi]
  exact a.normal_eq_graphNormal_of_inter_eq (a'.contDiff_g i) (a'.inter_ball_eq i) hy hi

/-- The atlas normal is a unit vector at every point of $\partial\Omega$. -/
theorem norm_normal {y : 𝔼} (hy : y ∈ frontier Ω) : ‖a.normal y‖ = 1 := by
  obtain ⟨i, hi⟩ := a.exists_mem_ball hy
  rw [a.normal_eq_graphNormal hy hi, EuclideanSpace.norm_graphNormal]

/-- The atlas normal is continuous on $\partial\Omega$, because near each boundary point it is the
normal of one chart. -/
theorem continuousOn_normal : ContinuousOn a.normal (frontier Ω) := by
  intro y hy
  obtain ⟨i, hi⟩ := a.exists_mem_ball hy
  refine (EuclideanSpace.continuous_graphNormal
    (a.contDiff_g i)).continuousWithinAt.congr_of_eventuallyEq ?_ (a.normal_eq_graphNormal hy hi)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.isOpen_ball.mem_nhds hi),
    eventually_mem_nhdsWithin] with z hz1 hz2
  exact a.normal_eq_graphNormal hz2 hz1

/-- The atlas normal is a unit vector almost everywhere for the surface measure of the atlas. -/
theorem ae_norm_normal : ∀ᵐ y ∂a.measure, ‖a.normal y‖ = 1 :=
  a.ae_mem_frontier.mono fun _ hy ↦ a.norm_normal hy

/-- The atlas normal is almost everywhere strongly measurable for the surface measure of the atlas.
-/
theorem aestronglyMeasurable_normal : AEStronglyMeasurable a.normal a.measure := by
  have := a.continuousOn_normal.aestronglyMeasurable (μ := a.measure)
    isClosed_frontier.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem a.ae_mem_frontier] at this

end GraphAtlas

/-! ### The surface measure and the outward normal of a bounded $C^1$ domain -/

namespace IsContDiffDomain

variable {Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))}

/-- **A bounded $C^1$ domain has a graph atlas.** If $\Omega \subseteq \mathbb{R}^{d+1}$ is a
bounded $C^1$ domain, then $\Omega$ has a graph atlas.

The charts are the finite cover of `IsBoundaryOfClass.exists_finite_cover`, and the partition of
unity is that of `IsCompact.exists_contDiff_partitionOfUnity` on the compact set
$\partial\Omega$. -/
theorem exists_graphAtlas (hΩ : IsContDiffDomain 1 Ω) (hb : Bornology.IsBounded Ω) :
    Nonempty (GraphAtlas Ω) := by
  obtain ⟨s, hs, hcov⟩ := hΩ.isBoundaryOfClass.exists_finite_cover hb
  let e := s.equivFin
  have hq : ∀ i : Fin s.card, ∃ (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) (g : 𝔼' → ℝ), ContDiff ℝ 1 g ∧
      Ω ∩ Metric.ball (e.symm i).1.1 (e.symm i).1.2
        = Metric.ball (e.symm i).1.1 (e.symm i).1.2 ∩ T ⁻¹' EuclideanSpace.epigraph g :=
    fun i ↦ (hs _ (e.symm i).2).2.2
  choose T g hg hTg using hq
  have hcov' : frontier Ω ⊆ ⋃ i : Fin s.card, Metric.ball (e.symm i).1.1 (e.symm i).1.2 := by
    intro y hy
    obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.1 (hcov hy)
    refine mem_iUnion.2 ⟨e ⟨q, hq⟩, ?_⟩
    simpa using hyq
  have hK : IsCompact (frontier Ω) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hb.closure.subset frontier_subset_closure)
  obtain ⟨θ₀, θ, hθ₀, hθ, hθ₀I, hθI, hsum, hθc, hθs, hθ₀d⟩ :=
    hK.exists_contDiff_partitionOfUnity (fun i ↦ Metric.isOpen_ball) hcov'
  refine ⟨{ k := s.card
            x := fun i ↦ (e.symm i).1.1
            r := fun i ↦ (e.symm i).1.2
            T := T
            g := g
            θ₀ := θ₀
            θ := θ
            x_mem_frontier := fun i ↦ (hs _ (e.symm i).2).1
            r_pos := fun i ↦ (hs _ (e.symm i).2).2.1
            contDiff_g := hg
            inter_ball_eq := hTg
            frontier_subset := hcov'
            contDiff_θ₀ := hθ₀
            contDiff_θ := hθ
            θ₀_mem_Icc := hθ₀I
            θ_mem_Icc := hθI
            θ₀_add_sum_θ := hsum
            hasCompactSupport_θ := hθc
            tsupport_θ_subset := hθs
            disjoint_tsupport_θ₀ := hθ₀d }⟩

/-- **The chosen graph atlas** of a bounded $C^1$ domain.

Everything defined from it is characterized independently of the chart
(`IsContDiffDomain.boundaryMeasure_restrict_ball`,
`IsContDiffDomain.outwardNormal_eq_graphNormal`), so the choice does not matter. -/
def graphAtlas (hΩ : IsContDiffDomain 1 Ω) (hb : Bornology.IsBounded Ω) : GraphAtlas Ω :=
  Classical.choice (hΩ.exists_graphAtlas hb)

/-- **The surface measure of a bounded $C^1$ domain** $\Omega$: the measure
$\sum_i \theta_i \sigma_i$ of the chosen graph atlas.

By `GraphAtlas.measure_eq` it is the measure of every graph atlas of $\Omega$. By
`IsContDiffDomain.boundaryMeasure_restrict_ball`, on every chart ball it is the image of
$\sqrt{1 + |\nabla g|^2} \, dx'$ under the parametrization of the chart. -/
def boundaryMeasure (hΩ : IsContDiffDomain 1 Ω) (hb : Bornology.IsBounded Ω) : Measure 𝔼 :=
  (hΩ.graphAtlas hb).measure

/-- **The outward unit normal of a bounded $C^1$ domain** $\Omega$, as a function on
$\mathbb{R}^{d+1}$: the normal of the chosen graph atlas, which on each of its chart balls is
the normal of a chart and is $0$ outside them.

By `IsContDiffDomain.outwardNormal_eq_graphNormal` it is the normal of every graph chart at
every boundary point in the chart ball. -/
def outwardNormal (hΩ : IsContDiffDomain 1 Ω) (hb : Bornology.IsBounded Ω) : 𝔼 → 𝔼 :=
  (hΩ.graphAtlas hb).normal

variable (hΩ : IsContDiffDomain 1 Ω) (hb : Bornology.IsBounded Ω)

/-- The surface measure of $\Omega$ is the measure of the chosen graph atlas. -/
theorem boundaryMeasure_eq_graphAtlas_measure :
    hΩ.boundaryMeasure hb = (hΩ.graphAtlas hb).measure :=
  rfl

/-- The surface measure of $\Omega$ is the measure of every graph atlas of $\Omega$. -/
theorem boundaryMeasure_eq_measure (a : GraphAtlas Ω) : hΩ.boundaryMeasure hb = a.measure :=
  GraphAtlas.measure_eq _ a

/-- The outward normal of $\Omega$ is the normal of the chosen graph atlas. -/
theorem outwardNormal_eq_graphAtlas_normal : hΩ.outwardNormal hb = (hΩ.graphAtlas hb).normal :=
  rfl

instance isFiniteMeasure_boundaryMeasure : IsFiniteMeasure (hΩ.boundaryMeasure hb) :=
  GraphAtlas.isFiniteMeasure_measure _

/-- The surface measure is carried by $\partial\Omega$: $\sigma((\partial\Omega)^c) = 0$. -/
theorem boundaryMeasure_compl_frontier : hΩ.boundaryMeasure hb (frontier Ω)ᶜ = 0 :=
  GraphAtlas.measure_compl_frontier _

/-- Almost every point for the surface measure lies on $\partial\Omega$. -/
theorem ae_mem_frontier_boundaryMeasure : ∀ᵐ y ∂(hΩ.boundaryMeasure hb), y ∈ frontier Ω :=
  GraphAtlas.ae_mem_frontier _

/-- Every function $f$ with values in a normed group that is continuous on $\partial\Omega$ is
integrable for the surface measure of $\Omega$. -/
theorem integrable_boundaryMeasure_of_continuousOn {G : Type*} [NormedAddCommGroup G]
    {f : 𝔼 → G} (hf : ContinuousOn f (frontier Ω)) : Integrable f (hΩ.boundaryMeasure hb) :=
  GraphAtlas.integrable_of_continuousOn _ hf

/-- **The integral against the surface measure, in the charts of the chosen atlas.** Let
$(T_i, g_i, \theta_i)$ be the charts and the partition of unity of the chosen atlas, with
parametrizations $\Phi_i$ and parameter domains $D_i$. For $f$ integrable for the surface
measure, with values in a real normed space,
$$\int f \, d\sigma = \sum_i \int_{D_i} \sqrt{1 + |\nabla g_i(x')|^2} \; \theta_i(\Phi_i(x')) \,
  f(\Phi_i(x')) \, dx'.$$
-/
theorem integral_boundaryMeasure {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : 𝔼 → G}
    (hf : Integrable f (hΩ.boundaryMeasure hb)) :
    ∫ y, f y ∂(hΩ.boundaryMeasure hb) = ∑ i, ∫ x' in (hΩ.graphAtlas hb).graphDomain i,
      (EuclideanSpace.graphDensity ((hΩ.graphAtlas hb).g i) x' *
        (hΩ.graphAtlas hb).θ i
          (EuclideanSpace.graphParam ((hΩ.graphAtlas hb).T i) ((hΩ.graphAtlas hb).g i) x')) •
          f (EuclideanSpace.graphParam ((hΩ.graphAtlas hb).T i) ((hΩ.graphAtlas hb).g i) x') :=
  GraphAtlas.integral_measure _ hf

/-- For $f$ integrable for the surface measure, with values in a real normed space, $\int f \,
d\sigma = \sum_i \int \theta_i \, f \, d\sigma_i$, where the $\theta_i$ and the local measures
$\sigma_i$ are those of the chosen atlas. -/
theorem integral_boundaryMeasure_eq_sum {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : 𝔼 → G} (hf : Integrable f (hΩ.boundaryMeasure hb)) :
    ∫ y, f y ∂(hΩ.boundaryMeasure hb)
      = ∑ i, ∫ y, (hΩ.graphAtlas hb).θ i y • f y ∂((hΩ.graphAtlas hb).localMeasure i) :=
  GraphAtlas.integral_measure_eq_sum _ hf

/-- **The chart characterization of the surface measure.** Let $(T, g)$ be any graph chart of
$\Omega$ at $(x_0, r)$: $g$ of class $C^1$ and $\Omega \cap B(x_0, r) = B(x_0, r) \cap
T^{-1}(\{y : y_{d+1} > g(y')\})$. Then the restriction of the surface measure to $B(x_0, r)$ is
the local surface measure of the chart over $\Phi^{-1}(B(x_0, r))$, the image of
$\sqrt{1 + |\nabla g|^2} \, dx'$ under $\Phi$.

This theorem makes `IsContDiffDomain.boundaryMeasure` canonical, and it is the form in which the
surface measure is computed. -/
theorem boundaryMeasure_restrict_ball {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g : 𝔼' → ℝ} (hg : ContDiff ℝ 1 g)
    {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g) :
    (hΩ.boundaryMeasure hb).restrict (Metric.ball x₀ r)
      = EuclideanSpace.graphMeasure T g (EuclideanSpace.graphDomain T g x₀ r) :=
  GraphAtlas.measure_restrict_ball _ hg h

/-- **Composition with a chart respects equality almost everywhere on $\partial\Omega$.** Let $a$ be
any graph atlas of $\Omega$, with parametrizations $\Phi_i$ and parameter domains $D_i$. If two
real functions $f_1, f_2$ on $\mathbb{R}^{d+1}$ satisfy $f_1 = f_2$ almost everywhere for the
surface measure of $\Omega$, then $f_1 \circ \Phi_i = f_2 \circ \Phi_i$ almost everywhere on
$D_i$ for the Lebesgue measure.

On the chart ball, the surface measure is the image under $\Phi_i$ of a measure with positive
density with respect to Lebesgue measure on $D_i$
(`IsContDiffDomain.boundaryMeasure_restrict_ball`, `EuclideanSpace.graphDensity_pos`). This
makes a condition on $v \circ \Phi_i$ a condition on the class of $v$ in $L^p(\partial\Omega)$,
as in Definition 7.2.13 of [han2009theoretical]. -/
theorem ae_eq_comp_graphParam (a : GraphAtlas Ω) (i : Fin a.k) {f g : 𝔼 → ℝ}
    (h : f =ᵐ[hΩ.boundaryMeasure hb] g) :
    f ∘ EuclideanSpace.graphParam (a.T i) (a.g i)
      =ᵐ[volume.restrict (a.graphDomain i)] g ∘ EuclideanSpace.graphParam (a.T i) (a.g i) := by
  have h1 : f =ᵐ[(hΩ.boundaryMeasure hb).restrict (Metric.ball (a.x i) (a.r i))] g :=
    ae_restrict_of_ae h
  rw [hΩ.boundaryMeasure_restrict_ball hb (a.contDiff_g i) (a.inter_ball_eq i),
    EuclideanSpace.graphMeasure] at h1
  have h2 := h1.comp_tendsto (Measure.tendsto_ae_map
    (EuclideanSpace.continuous_graphParam (a.contDiff_g i).continuous).aemeasurable)
  rw [Filter.EventuallyEq, ae_withDensity_iff
    (EuclideanSpace.measurable_ofReal_graphDensity (a.contDiff_g i))] at h2
  exact h2.mono fun x hx ↦ hx (ENNReal.ofReal_pos.2 (EuclideanSpace.graphDensity_pos _)).ne'

/-- For every graph chart $(T, g)$ of $\Omega$ at $(x_0, r)$ with $g$ of class $C^1$, the surface
measure of the ball is the weighted Lebesgue measure of the parameter domain:
$$\sigma(B(x_0, r)) = \int_{\Phi^{-1}(B(x_0, r))} \sqrt{1 + |\nabla g(x')|^2} \, dx'.$$
-/
theorem boundaryMeasure_ball_eq_lintegral {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g : 𝔼' → ℝ} (hg : ContDiff ℝ 1 g)
    {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g) :
    hΩ.boundaryMeasure hb (Metric.ball x₀ r)
      = ∫⁻ x' in EuclideanSpace.graphDomain T g x₀ r,
          ENNReal.ofReal (EuclideanSpace.graphDensity g x') := by
  rw [← Measure.restrict_apply_univ, boundaryMeasure_restrict_ball hΩ hb hg h,
    EuclideanSpace.graphMeasure_apply hg.continuous _ MeasurableSet.univ, preimage_univ, inter_univ]

/-- **The surface measure has full support on $\partial\Omega$.** Every open set $U$ that meets
$\partial\Omega$ has positive surface measure.

In a chart at a common point, a small ball has measure at least the Lebesgue measure of its
parameter domain, which is open and nonempty, because the surface element is at least $1$. -/
theorem boundaryMeasure_pos_of_isOpen {U : Set 𝔼} (hU : IsOpen U)
    (hne : (U ∩ frontier Ω).Nonempty) : 0 < hΩ.boundaryMeasure hb U := by
  obtain ⟨x, hxU, hxF⟩ := hne
  obtain ⟨r, hr, T, g, hg, h⟩ := hΩ.isBoundaryOfClass x hxF
  replace hg : ContDiff ℝ 1 g := hg
  replace h : Ω ∩ Metric.ball x r = Metric.ball x r ∩ T ⁻¹' EuclideanSpace.epigraph g := h
  obtain ⟨r', hr', hr'U⟩ := Metric.isOpen_iff.1 hU x hxU
  set ρ := min r r' with hρdef
  have hρ : 0 < ρ := lt_min hr hr'
  have hρr : Metric.ball x ρ ⊆ Metric.ball x r := Metric.ball_subset_ball (min_le_left _ _)
  have hρU : Metric.ball x ρ ⊆ U := (Metric.ball_subset_ball (min_le_right _ _)).trans hr'U
  have h' : Ω ∩ Metric.ball x ρ = Metric.ball x ρ ∩ T ⁻¹' EuclideanSpace.epigraph g := by
    ext y
    have e := Set.ext_iff.1 h y
    simp only [mem_inter_iff] at e ⊢
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (e.1 ⟨h1, hρr h2⟩).2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(e.2 ⟨hρr h1, h2⟩).1, h1⟩
  have hne' : (EuclideanSpace.graphDomain T g x ρ).Nonempty := by
    refine ⟨EuclideanSpace.init (T x), ?_⟩
    change EuclideanSpace.graphParam T g (EuclideanSpace.init (T x)) ∈ Metric.ball x ρ
    rw [EuclideanSpace.graphParam_eq_of_mem_frontier hg.continuous
      (EuclideanSpace.mem_frontier_preimage_epigraph_of_mem_frontier hg.continuous h' hxF
        (Metric.mem_ball_self hρ))]
    exact Metric.mem_ball_self hρ
  calc 0 < volume (EuclideanSpace.graphDomain T g x ρ) :=
        (EuclideanSpace.isOpen_graphDomain hg.continuous x ρ).measure_pos volume hne'
    _ ≤ ∫⁻ x' in EuclideanSpace.graphDomain T g x ρ,
          ENNReal.ofReal (EuclideanSpace.graphDensity g x') := by
        rw [← setLIntegral_one]
        refine setLIntegral_mono' (EuclideanSpace.measurableSet_graphDomain hg.continuous x ρ)
          fun x' _ ↦ ?_
        simpa using ENNReal.ofReal_le_ofReal (EuclideanSpace.one_le_graphDensity (g := g) x')
    _ = hΩ.boundaryMeasure hb (Metric.ball x ρ) :=
        (boundaryMeasure_ball_eq_lintegral hΩ hb hg h').symm
    _ ≤ hΩ.boundaryMeasure hb U := measure_mono hρU

/-- If $\Omega$ is nonempty, its surface measure is positive: $\sigma(\mathbb{R}^{d+1}) > 0$. -/
theorem boundaryMeasure_univ_pos (hne : Ω.Nonempty) : 0 < hΩ.boundaryMeasure hb univ :=
  hΩ.boundaryMeasure_pos_of_isOpen hb isOpen_univ
    (by rw [univ_inter]; exact hb.frontier_nonempty hne)

/-- On $\partial\Omega \cap B(x_i, r_i)$ the outward normal is the normal of the $i$-th chart of the
chosen atlas. -/
theorem outwardNormal_eq_graphNormal_atlas {y : 𝔼} (hy : y ∈ frontier Ω)
    {i : Fin (hΩ.graphAtlas hb).k}
    (hi : y ∈ Metric.ball ((hΩ.graphAtlas hb).x i) ((hΩ.graphAtlas hb).r i)) :
    hΩ.outwardNormal hb y
      = EuclideanSpace.graphNormal ((hΩ.graphAtlas hb).T i) ((hΩ.graphAtlas hb).g i) y :=
  GraphAtlas.normal_eq_graphNormal _ hy hi

/-- **The chart characterization of the outward normal.** Let $(T, g)$ be any graph chart of
$\Omega$ at $(x_0, r)$: $g$ of class $C^1$ and $\Omega \cap B(x_0, r) = B(x_0, r) \cap
T^{-1}(\{y : y_{d+1} > g(y')\})$. Then at every $y \in \partial\Omega \cap B(x_0, r)$,
$$\nu(y) = \frac{L^{-1}(\nabla g(y'), -1)}{\sqrt{1 + |\nabla g(y')|^2}}, \qquad y' = (T y)',$$
where $L$ is the linear part of $T$; that is, $\nu(y)$ is `EuclideanSpace.graphNormal T g y`. -/
theorem outwardNormal_eq_graphNormal {T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼} {g : 𝔼' → ℝ} (hg : ContDiff ℝ 1 g)
    {x₀ : 𝔼} {r : ℝ}
    (h : Ω ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    {y : 𝔼} (hy : y ∈ frontier Ω) (hyB : y ∈ Metric.ball x₀ r) :
    hΩ.outwardNormal hb y = EuclideanSpace.graphNormal T g y :=
  GraphAtlas.normal_eq_graphNormal_of_inter_eq _ hg h hy hyB

/-- On $\partial\Omega$, the outward normal is the normal of every graph atlas of $\Omega$. -/
theorem outwardNormal_eq_normal (a : GraphAtlas Ω) {y : 𝔼} (hy : y ∈ frontier Ω) :
    hΩ.outwardNormal hb y = a.normal y :=
  GraphAtlas.normal_eq_of_mem_frontier _ a hy

/-- The outward normal is a unit vector at every point of $\partial\Omega$. -/
theorem norm_outwardNormal {y : 𝔼} (hy : y ∈ frontier Ω) : ‖hΩ.outwardNormal hb y‖ = 1 :=
  GraphAtlas.norm_normal _ hy

/-- The outward normal is continuous on $\partial\Omega$. -/
theorem continuousOn_outwardNormal : ContinuousOn (hΩ.outwardNormal hb) (frontier Ω) :=
  GraphAtlas.continuousOn_normal _

/-- The outward normal is a unit vector almost everywhere for the surface measure. -/
theorem ae_norm_outwardNormal : ∀ᵐ y ∂(hΩ.boundaryMeasure hb), ‖hΩ.outwardNormal hb y‖ = 1 :=
  GraphAtlas.ae_norm_normal _

/-- The outward normal is almost everywhere strongly measurable for the surface measure. -/
theorem aestronglyMeasurable_outwardNormal :
    AEStronglyMeasurable (hΩ.outwardNormal hb) (hΩ.boundaryMeasure hb) :=
  GraphAtlas.aestronglyMeasurable_normal _

end IsContDiffDomain

end
