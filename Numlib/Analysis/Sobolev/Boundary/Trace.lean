/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.MeanInequalities
import Numlib.Analysis.Normed.Operator.Embedding
import Numlib.Analysis.Sobolev.Boundary.Data
import Numlib.Analysis.Sobolev.Boundary.Density
import Numlib.Analysis.SpecialFunctions.Pow.Deriv
import Numlib.Data.ENNReal.Real

/-!
# The trace theorem from a transversal field

Let $\Omega \subseteq \mathbb{R}^N$ be a bounded open set with boundary data `BoundaryData Ω`: a
finite surface measure $\sigma$ carried by $\partial\Omega$, an outward unit normal $\nu$, and the
divergence theorem. A **transversal field** is a compactly supported $C^1$ vector field
$w : \mathbb{R}^N \to \mathbb{R}^N$ with $\langle w, \nu \rangle \ge 1$ $\sigma$-almost everywhere.
From a transversal field, this module constructs the trace operator
$T : W^{1,p}(\Omega) \to L^p(\sigma)$ for $1 \le p < \infty$ and proves its main properties. The
construction is Nečas's proof (*Direct Methods in the Theory of Elliptic Equations*, Chapter 2, §4);
see also Evans, *Partial Differential Equations*, §5.5, Theorem 1, [grisvard2011elliptic] Theorems
1.5.1.3 and 1.5.3.1, [han2009theoretical] §7.3 and §7.6, and the comments on Chapter 9 of
[brezis2011functional].

The central estimate is **Nečas's inequality**
$$\int |u|^p \, d\sigma \le C \Big( \int_\Omega |u|^p \, dx + \int_\Omega |u|^{p-1} |\nabla u| \, dx
  \Big), \qquad u \in C^1(\mathbb{R}^N),$$
with $C$ depending only on $w$ and $p$. It gives $\|u\|_{L^p(\sigma)} \le C'
\|u\|_{W^{1,p}(\Omega)}$, so restriction to $\partial\Omega$ is a bounded linear map on the subspace
of $W^{1,p}(\Omega)$ of restrictions of smooth compactly supported functions, and $T$ is its
continuous extension. When this subspace is dense, the module proves the trace inequality, the
identity $Tu = \tilde u$ on $\partial\Omega$ for a representative $\tilde u$ continuous up to the
boundary, the uniqueness of $T$, Green's formula $\int_\Omega \partial_i u \, v + \int_\Omega u \,
\partial_i v = \int Tu \, Tv \, \nu_i \, d\sigma$, and the compactness of $T$ for $1 < p < \infty$
when $W^{1,p}(\Omega) \to L^p(\Omega)$ is compact. The two concrete instances are the bounded $C^1$
domains (`Numlib.Analysis.Sobolev.Boundary.ContDiffDomain`) and the triangles
(`Numlib.Analysis.Sobolev.Boundary.PolygonTrace`). The characterization $\ker T = W_0^{1,p}(\Omega)$
is proved in `Numlib.Analysis.Sobolev.Boundary.Kernel`. The range of $T$, the fractional space
$W^{1-1/p,p}(\partial\Omega)$, is not treated.

## Main definitions

* `BoundaryData.HasTransversalField`: there is a compactly supported $C^1$ field $w$ with
  $\langle w, \nu \rangle \ge 1$ $\sigma$-almost everywhere.
* `BoundaryData.traceSmoothL`: restriction to $\partial\Omega$ on the smooth-representable elements
  of $W^{1,p}(\Omega)$, as a bounded operator into $L^p(\sigma)$.
* `BoundaryData.traceL`: the trace operator $T : W^{1,p}(\Omega) \to L^p(\sigma)$, the continuous
  extension of `BoundaryData.traceSmoothL`.
* `BoundaryData.traceFamily`: the trace operators at all finite exponents with their properties, as
  a `BoundaryData.TraceFamily`.

## Main results

* `BoundaryData.integral_abs_rpow_le_of_contDiff`: Nečas's inequality for $u \in C^1(\mathbb{R}^N)$.
* `BoundaryData.eLpNorm_le_of_contDiff`: $\|u\|_{L^p(\sigma)} \le C \|U\|_{W^{1,p}(\Omega)}$ for
  every $C^1$ representative $u$ of $U \in W^{1,p}(\Omega)$.
* `BoundaryData.norm_traceL_apply_le`: the trace inequality $\|Tu\|_{L^p(\sigma)} \le C
  \|u\|_{W^{1,p}(\Omega)}$.
* `BoundaryData.traceL_ae_eq_of_continuousOn`: the trace of a function continuous up to the boundary
  is its restriction to $\partial\Omega$.
* `BoundaryData.traceL_unique`: a bounded operator that restricts the smooth representatives is $T$.
* `BoundaryData.green_of_hasSmoothDensity`: Green's formula at finite conjugate exponents.
* `BoundaryData.green_contDiff_of_hasSmoothDensity`: Green's formula against a compactly supported
  $C^1$ test function, for $1 \le p < \infty$.
* `BoundaryData.integral_abs_traceL_rpow_le`: Nečas's inequality for $Tu$, $u \in W^{1,p}(\Omega)$.
* `BoundaryData.isCompactOperator_traceL`: $T$ is compact for $1 < p < \infty$ if the embedding
  $W^{1,p}(\Omega) \to L^p(\Omega)$ is compact.

## Proof outline

For $u \in C^1(\mathbb{R}^N)$ and $\varepsilon > 0$, apply the divergence theorem to the field
$\varphi_\varepsilon(u) w$, where $\varphi_\varepsilon(t) = (t^2 + \varepsilon^2)^{p/2} -
\varepsilon^p$ is a $C^1$ regularization of $|t|^p$. The boundary term dominates
$\int \varphi_\varepsilon(u) \, d\sigma$ because $\varphi_\varepsilon \ge 0$ and
$\langle w, \nu \rangle \ge 1$, and the divergence is bounded by the derivative estimates of
$\varphi_\varepsilon$. The limit $\varepsilon \to 0$ gives Nečas's inequality. The regularization
makes the case $p = 1$ work, where $|t|^p$ is not $C^1$. The properties of $T$ on $W^{1,p}(\Omega)$
follow from those on the smooth functions by density and continuity. For compactness, Nečas's
inequality bounds $\|T(u_n - u_m)\|_{L^p(\sigma)}$ by a quantity that tends to zero with
$\|u_n - u_m\|_{L^p(\Omega)}$ when $p > 1$ and $u_n - u_m$ stays bounded in $W^{1,p}(\Omega)$.

## Implementation notes

* The existence of a transversal field is a hypothesis of the construction and not a field of
  `BoundaryData`: a domain made of two triangles that meet at one vertex has no transversal field.
* `BoundaryData.traceL` is `ContinuousLinearMap.extend` of `BoundaryData.traceSmoothL` along the
  inclusion of `SobolevEuclidean.smoothRestrictions`. As for Mathlib's `extend`, the density
  hypothesis `SobolevEuclidean.HasSmoothDensity` enters the lemmas and not the definition. If the
  subspace is not dense, the extension is the zero operator.
* Density holds on bounded $C^1$ domains by [brezis2011functional] Corollary 9.8, and on sets with
  the segment property; see `Numlib.Analysis.Sobolev.Boundary.Density`. The restriction property
  also needs `SobolevEuclidean.HasUniformSmoothDensity`, approximation in $W^{1,p}(\Omega)$ and at
  the same time uniformly on $\overline{\Omega}$.
* [han2009theoretical] Theorem 7.3.10(c) states the compactness of the trace for $1 \le p < \infty$.
  At $p = 1$ the trace $W^{1,1}(\Omega) \to L^1(\partial\Omega)$ is onto (Gagliardo), so it is not
  compact. `BoundaryData.isCompactOperator_traceL` assumes $1 < p$.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal InnerProductSpace Topology

noncomputable section


section General

variable {N : ℕ}

end General

section Sobolev

variable {N : ℕ} {p : ℝ≥0∞} {Ω : Opens (EuclideanSpace ℝ (Fin N))}

open SobolevMultiIndex

end Sobolev

namespace BoundaryData

variable {N : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin N))} (B : BoundaryData Ω)

/-- The ambient space $\mathbb{R}^N$, written `𝔼` in this file. -/
local notation "𝔼" => EuclideanSpace ℝ (Fin N)

/-! ### Transversal fields -/

/-- Boundary data `B` of $\Omega$ **have a transversal field** if there is a compactly supported
vector field $w : \mathbb{R}^N \to \mathbb{R}^N$ of class $C^1$ such that $$\langle w(x), \nu(x)
\rangle \ge 1$$ for $\sigma$-almost every $x$.

The field points strictly outward along $\partial\Omega$. The normalization $\ge 1$ instead of
$> 0$ costs nothing on a compact boundary and saves a compactness argument. Bounded $C^1$
domains have a transversal field (`IsContDiffDomain.hasTransversalField`), and so do triangles
(`EuclideanSpace.triangle_hasTransversalField`, with $w(x) = c (x - x_0)$ near the triangle for
an interior point $x_0$). A domain made of two triangles that meet at one vertex has none.
Therefore the existence of a transversal field is a hypothesis of the trace construction and not
a field of `BoundaryData`. -/
def HasTransversalField : Prop :=
  ∃ w : 𝔼 → 𝔼, ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ ∀ᵐ x ∂B.σ, 1 ≤ ⟪w x, B.ν x⟫_ℝ

/-! ### Integrability for $\sigma$ and on $\Omega$ -/

include B in
/-- The restriction of Lebesgue measure to the bounded set $\Omega$ is a finite measure. -/
theorem isFiniteMeasure_volume_restrict : IsFiniteMeasure (volume.restrict (Ω : Set 𝔼)) :=
  MeasureTheory.isFiniteMeasure_restrict.2 B.isBounded.measure_lt_top.ne

/-- Let $G$ be a normed group. A function $f : \mathbb{R}^N \to G$ that is continuous on
$\overline{\Omega}$ lies in $L^p(\sigma)$ for every $p \in [0, \infty]$.

The set $\overline{\Omega}$ is compact, so $f$ is bounded on it, and $\sigma$ is a finite
measure carried by $\partial\Omega \subseteq \overline{\Omega}$. -/
theorem memLp_of_continuousOn {G : Type*} [NormedAddCommGroup G] {f : 𝔼 → G}
    (hf : ContinuousOn f (closure (Ω : Set 𝔼))) (p : ℝ≥0∞) : MemLp f p B.σ := by
  have hae : ∀ᵐ x ∂B.σ, x ∈ closure (Ω : Set 𝔼) :=
    B.ae_mem_frontier.mono fun x hx ↦ frontier_subset_closure hx
  have hm : AEStronglyMeasurable f B.σ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hf.aestronglyMeasurable isClosed_closure.measurableSet
  obtain ⟨C, hC⟩ := B.isBounded.isCompact_closure.exists_bound_of_continuousOn hf
  exact MemLp.of_bound hm C (hae.mono fun x hx ↦ hC x hx)

/-- Let $G$ be a normed group. A continuous function $f : \mathbb{R}^N \to G$ lies in $L^p(\sigma)$
for every $p \in [0, \infty]$. -/
theorem memLp_of_continuous {G : Type*} [NormedAddCommGroup G] {f : 𝔼 → G} (hf : Continuous f)
    (p : ℝ≥0∞) : MemLp f p B.σ :=
  B.memLp_of_continuousOn hf.continuousOn p

/-- Let $G$ be a normed group. A continuous function $f : \mathbb{R}^N \to G$ is integrable for
$\sigma$. -/
theorem integrable_of_continuous {G : Type*} [NormedAddCommGroup G] {f : 𝔼 → G}
    (hf : Continuous f) : Integrable f B.σ :=
  memLp_one_iff_integrable.1 (B.memLp_of_continuous hf 1)

include B in
/-- Let $G$ be a normed group. A continuous function $f : \mathbb{R}^N \to G$ is integrable on the
bounded set $\Omega$ for Lebesgue measure. -/
theorem integrableOn_of_continuous {G : Type*} [NormedAddCommGroup G]
    {f : 𝔼 → G} (hf : Continuous f) : IntegrableOn f (Ω : Set 𝔼) :=
  B.integrableOn_of_continuousOn hf.continuousOn

/-! ### Bump tests on the boundary -/

/-- A function $h : \mathbb{R}^N \to \mathbb{R}$ that is continuous on $\partial\Omega$ lies in
$L^\infty(\sigma)$. -/
theorem memLp_top_of_continuousOn_frontier {h : 𝔼 → ℝ}
    (hc : ContinuousOn h (frontier (Ω : Set 𝔼))) : MemLp h ⊤ B.σ := by
  have hm : AEStronglyMeasurable h B.σ := by
    rw [← Measure.restrict_eq_self_of_ae_mem B.ae_mem_frontier]
    exact hc.aestronglyMeasurable isClosed_frontier.measurableSet
  have hK : IsCompact (frontier (Ω : Set 𝔼)) :=
    B.isBounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  exact MemLp.of_bound hm C (B.ae_mem_frontier.mono fun x hx ↦ hC x hx)

open Metric in
/-- Suppose that $\sigma(U) > 0$ for every open set $U$ that meets $\partial\Omega$. Let
$h : \mathbb{R}^N \to \mathbb{R}$ be continuous on $\partial\Omega$, let
$x_0 \in \partial\Omega$, and let $c < h(x_0)$. Then there is a smooth compactly supported
function $\psi : \mathbb{R}^N \to \mathbb{R}$ with $0 \le \psi \le 1$ and $$c \int \psi \,
d\sigma < \int h \psi \, d\sigma.$$

The hypothesis on $\sigma$ holds on a bounded $C^1$ domain
(`IsContDiffDomain.boundaryMeasure_pos_of_isOpen`). The function $\psi$ is a smooth bump
supported in a ball around $x_0$ on which $h > (c + h(x_0))/2$. Its integral is positive because
a smaller ball around $x_0$ has positive measure. -/
theorem exists_bump_lt_integral_mul
    (hpos : ∀ U : Set 𝔼, IsOpen U → (U ∩ frontier (Ω : Set 𝔼)).Nonempty → 0 < B.σ U)
    {h : 𝔼 → ℝ} (hc : ContinuousOn h (frontier (Ω : Set 𝔼))) {x₀ : 𝔼}
    (hx₀ : x₀ ∈ frontier (Ω : Set 𝔼)) {c : ℝ} (hlt : c < h x₀) :
    ∃ ψ : 𝔼 → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧
      c * ∫ x, ψ x ∂B.σ < ∫ x, h x * ψ x ∂B.σ := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (c + h x₀) / 2 := ⟨_, rfl⟩
  have hcm : c < m := by rw [hm]; linarith
  have hmx : m < h x₀ := by rw [hm]; linarith
  -- a ball on which `h > m`, relative to `∂Ω`
  have hev : ∀ᶠ x in 𝓝[frontier (Ω : Set 𝔼)] x₀, m < h x :=
    (hc x₀ hx₀).eventually (lt_mem_nhds hmx)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  -- the bump
  let ψ : ContDiffBump x₀ := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, fun x ↦ ψ.nonneg, fun x ↦ ψ.le_one, ?_⟩
  have hψc : Continuous ψ := ψ.continuous
  have hIψ : Integrable (fun x ↦ ψ x) B.σ := B.integrable_of_continuous hψc
  have hIhψ : Integrable (fun x ↦ h x * ψ x) B.σ :=
    (B.memLp_top_of_continuousOn_frontier hc).integrable_mul (B.memLp_of_continuous hψc 1)
  -- `∫ ψ dσ > 0`
  have hpsi : 0 < ∫ x, ψ x ∂B.σ := by
    have h1 : B.σ.real (ball x₀ (r / 2)) ≤ ∫ x, ψ x ∂B.σ := by
      rw [← integral_indicator_one measurableSet_ball]
      refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_ball) hIψ
        fun x ↦ ?_
      by_cases hx : x ∈ ball x₀ (r / 2)
      · rw [indicator_of_mem hx]
        exact (ψ.one_of_mem_closedBall (ball_subset_closedBall hx)).ge
      · rw [indicator_of_notMem hx]
        exact ψ.nonneg
    refine lt_of_lt_of_le ?_ h1
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hpos _ isOpen_ball ⟨x₀, mem_ball_self (by positivity), hx₀⟩).ne'
      (measure_ne_top _ _)
  -- `∫ h ψ ≥ m ∫ ψ`
  have hle : m * ∫ x, ψ x ∂B.σ ≤ ∫ x, h x * ψ x ∂B.σ := by
    rw [← integral_const_mul]
    refine integral_mono_ae (hIψ.const_mul m) hIhψ ?_
    filter_upwards [B.ae_mem_frontier] with x hx
    by_cases hxb : x ∈ ball x₀ r
    · exact mul_le_mul_of_nonneg_right (hball ⟨hxb, hx⟩).le ψ.nonneg
    · rw [ψ.zero_of_le_dist (not_lt.1 fun h' ↦ hxb (mem_ball.2 h')), mul_zero, mul_zero]
  calc c * ∫ x, ψ x ∂B.σ < m * ∫ x, ψ x ∂B.σ := mul_lt_mul_of_pos_right hcm hpsi
    _ ≤ _ := hle

/-- Suppose that $\sigma(U) > 0$ for every open set $U$ that meets $\partial\Omega$. Let
$h : \mathbb{R}^N \to \mathbb{R}$ be continuous on $\partial\Omega$, with
$\int h \psi \, d\sigma = 0$ for every smooth compactly supported
$\psi : \mathbb{R}^N \to \mathbb{R}$. Then $h = 0$ on $\partial\Omega$.

If $h(x_0) \neq 0$ at a point $x_0 \in \partial\Omega$, the sign of $h$ persists on a small ball
around $x_0$, and the bump of `BoundaryData.exists_bump_lt_integral_mul` has a nonzero integral
against $h$. -/
theorem eqOn_zero_frontier_of_forall_integral_mul_eq_zero
    (hpos : ∀ U : Set 𝔼, IsOpen U → (U ∩ frontier (Ω : Set 𝔼)).Nonempty → 0 < B.σ U)
    {h : 𝔼 → ℝ} (hc : ContinuousOn h (frontier (Ω : Set 𝔼)))
    (hint : ∀ ψ : 𝔼 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ∫ x, h x * ψ x ∂B.σ = 0) :
    EqOn h 0 (frontier (Ω : Set 𝔼)) := by
  intro x₀ hx₀
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨ψ, hψ, hψc, -, -, hψi⟩ := B.exists_bump_lt_integral_mul hpos hc.neg hx₀
      (c := 0) (by simpa using hlt)
    have := hint ψ hψ hψc
    simp only [Pi.neg_apply, neg_mul, integral_neg, zero_mul] at hψi
    linarith
  · obtain ⟨ψ, hψ, hψc, -, -, hψi⟩ := B.exists_bump_lt_integral_mul hpos hc hx₀ (c := 0) hgt
    have := hint ψ hψ hψc
    rw [zero_mul] at hψi
    linarith

/-! ### Nečas's inequality -/

/-- Let $w : \mathbb{R}^N \to \mathbb{R}^N$ be a compactly supported $C^1$ field with
$\langle w, \nu \rangle \ge 1$ $\sigma$-almost everywhere, and with $\|w(x)\| \le M_0$ and
$\|Dw(x)\| \le M_1$ for all $x$. Let $p \ge 1$, let $\varepsilon > 0$, and let
$u : \mathbb{R}^N \to \mathbb{R}$ be of class $C^1$. With $\varphi_\varepsilon(t) = (t^2 +
\varepsilon^2)^{p/2} - \varepsilon^p$, $$\int \varphi_\varepsilon(u) \, d\sigma \le \max(N M_1,
p M_0) \Big( \int_\Omega (|u| + \varepsilon)^p \, dx + \int_\Omega (|u| + \varepsilon)^{p-1}
\|Du\| \, dx \Big).$$

This is the step of Nečas's inequality at a fixed $\varepsilon$. The function
$\varphi_\varepsilon$ is `Real.rpowReg p ε`, and $\|Du\|$ is the operator norm of
`fderiv ℝ u x`. The proof applies the divergence theorem to the field
$\varphi_\varepsilon(u) w$, whose divergence $\varphi_\varepsilon'(u) \langle \nabla u, w
\rangle + \varphi_\varepsilon(u) \operatorname{div} w$ is bounded by the derivative estimates of
`Real.rpowReg`. -/
theorem integral_rpowReg_le {w : 𝔼 → 𝔼} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w)
    (hwν : ∀ᵐ x ∂B.σ, 1 ≤ ⟪w x, B.ν x⟫_ℝ) {M₀ M₁ : ℝ} (hM₀ : ∀ x, ‖w x‖ ≤ M₀)
    (hM₁ : ∀ x, ‖fderiv ℝ w x‖ ≤ M₁) {p : ℝ} (hp : 1 ≤ p) {ε : ℝ} (hε : 0 < ε)
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u) :
    ∫ x, Real.rpowReg p ε (u x) ∂B.σ
      ≤ max (N * M₁) (p * M₀) * ((∫ x in (Ω : Set 𝔼), (|u x| + ε) ^ p)
        + ∫ x in (Ω : Set 𝔼), (|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hφ : ContDiff ℝ 1 (Real.rpowReg p ε) := Real.contDiff_rpowReg hε
  have hφu : ContDiff ℝ 1 (fun x ↦ Real.rpowReg p ε (u x)) := hφ.comp hu
  have hF : ContDiff ℝ 1 (fun x ↦ Real.rpowReg p ε (u x) • w x) := hφu.smul hw
  have hFc : HasCompactSupport (fun x ↦ Real.rpowReg p ε (u x) • w x) :=
    HasCompactSupport.smul_left (f := fun x ↦ Real.rpowReg p ε (u x)) hwc
  have hdiv := B.integral_div_eq_of_contDiff hF
  -- the boundary term dominates `∫ φ_ε(u) dσ`
  have h1 : ∫ x, Real.rpowReg p ε (u x) ∂B.σ
      ≤ ∫ x, ⟪Real.rpowReg p ε (u x) • w x, B.ν x⟫_ℝ ∂B.σ := by
    refine integral_mono_ae (B.integrable_of_continuous hφu.continuous) ?_
      (hwν.mono fun x hx ↦ ?_)
    · obtain ⟨K, hK⟩ := hF.continuous.bounded_above_of_compact_support hFc
      refine Integrable.of_bound (hF.continuous.aestronglyMeasurable.inner
        B.aestronglyMeasurable_ν) K (B.ae_norm_ν.mono fun x hx ↦ ?_)
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (by rw [hx, mul_one]; exact hK x)
    · dsimp only
      rw [real_inner_smul_left]
      exact le_mul_of_one_le_right (Real.rpowReg_nonneg hε hp0 _) hx
  -- the interior term, pointwise
  have hcont₁ : Continuous fun x ↦ (|u x| + ε) ^ p :=
    (hu.continuous.abs.add continuous_const).rpow_const fun x ↦ Or.inr hp0
  have hcont₂ : Continuous fun x ↦ (|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖ :=
    ((hu.continuous.abs.add continuous_const).rpow_const fun x ↦ Or.inr (by linarith)).mul
      (hu.continuous_fderiv one_ne_zero).norm
  have hdivc : Continuous (EuclideanSpace.div fun x ↦ Real.rpowReg p ε (u x) • w x) := by
    unfold EuclideanSpace.div
    exact continuous_finsetSum _ fun i _ ↦ (PiLp.continuous_apply 2 _ i).comp
      ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have h2 : ∫ x in (Ω : Set 𝔼), EuclideanSpace.div (fun x ↦ Real.rpowReg p ε (u x) • w x) x
      ≤ ∫ x in (Ω : Set 𝔼), max (N * M₁) (p * M₀)
        * ((|u x| + ε) ^ p + (|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) := by
    refine integral_mono (B.integrableOn_of_continuous hdivc)
      ((B.integrableOn_of_continuous (hcont₁.add hcont₂)).const_mul _) fun x ↦ ?_
    -- the product rule and the chain rule
    have hux : DifferentiableAt ℝ u x := (hu.differentiable one_ne_zero).differentiableAt
    have hwx : DifferentiableAt ℝ w x := (hw.differentiable one_ne_zero).differentiableAt
    have hφx : DifferentiableAt ℝ (fun x ↦ Real.rpowReg p ε (u x)) x :=
      (hφu.differentiable one_ne_zero).differentiableAt
    rw [EuclideanSpace.div_smul_fun hφx hwx]
    have hgrad : ⟪gradient (fun x ↦ Real.rpowReg p ε (u x)) x, w x⟫_ℝ
        = p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (w x) := by
      have hd : HasFDerivAt (fun x ↦ Real.rpowReg p ε (u x))
          ((p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1)) • fderiv ℝ u x) x :=
        (Real.hasDerivAt_rpowReg hε (u x)).comp_hasFDerivAt x hux.hasFDerivAt
      rw [gradient, InnerProductSpace.toDual_symm_apply, hd.fderiv]
      simp only [smul_apply, smul_eq_mul]
    rw [hgrad]
    have hA : |p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (w x)|
        ≤ p * M₀ * ((|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) := by
      rw [abs_mul]
      calc |p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1)| * |fderiv ℝ u x (w x)|
          ≤ p * (|u x| + ε) ^ (p - 1) * (‖fderiv ℝ u x‖ * M₀) := by
            refine mul_le_mul (Real.abs_deriv_rpowReg_le hε hp _) ?_ (abs_nonneg _)
              (by positivity)
            rw [← Real.norm_eq_abs]
            exact ((fderiv ℝ u x).le_opNorm _).trans
              (mul_le_mul_of_nonneg_left (hM₀ x) (norm_nonneg _))
        _ = p * M₀ * ((|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) := by ring
    have hB : |Real.rpowReg p ε (u x) * EuclideanSpace.div w x|
        ≤ N * M₁ * (|u x| + ε) ^ p := by
      rw [abs_mul, abs_of_nonneg (Real.rpowReg_nonneg hε hp0 _)]
      calc Real.rpowReg p ε (u x) * |EuclideanSpace.div w x|
          ≤ (|u x| + ε) ^ p * (N * ‖fderiv ℝ w x‖) :=
            mul_le_mul (Real.rpowReg_le hε hp0 _) (EuclideanSpace.abs_div_le w x)
              (abs_nonneg _) (by positivity)
        _ ≤ (|u x| + ε) ^ p * (N * M₁) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM₁ x) (by positivity))
              (by positivity)
        _ = N * M₁ * (|u x| + ε) ^ p := by ring
    have hmax₁ : p * M₀ ≤ max (N * M₁) (p * M₀) := le_max_right _ _
    have hmax₂ : N * M₁ ≤ max (N * M₁) (p * M₀) := le_max_left _ _
    have hnn₁ : 0 ≤ (|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖ := by positivity
    have hnn₂ : 0 ≤ (|u x| + ε) ^ p := by positivity
    calc p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (w x)
          + Real.rpowReg p ε (u x) * EuclideanSpace.div w x
        ≤ |p * u x * (u x ^ 2 + ε ^ 2) ^ (p / 2 - 1) * fderiv ℝ u x (w x)|
          + |Real.rpowReg p ε (u x) * EuclideanSpace.div w x| :=
          add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ p * M₀ * ((|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) + N * M₁ * (|u x| + ε) ^ p :=
          add_le_add hA hB
      _ ≤ max (N * M₁) (p * M₀) * ((|u x| + ε) ^ p
          + (|u x| + ε) ^ (p - 1) * ‖fderiv ℝ u x‖) := by
          nlinarith [mul_le_mul_of_nonneg_right hmax₁ hnn₁, mul_le_mul_of_nonneg_right hmax₂ hnn₂]
  rw [integral_const_mul, integral_add (B.integrableOn_of_continuous hcont₁)
    (B.integrableOn_of_continuous hcont₂)] at h2
  rw [hdiv] at h2
  exact h1.trans h2

/-- **Nečas's inequality** for $C^1$ functions. Let $w : \mathbb{R}^N \to \mathbb{R}^N$ be a
compactly supported $C^1$ field with $\langle w, \nu \rangle \ge 1$ $\sigma$-almost everywhere,
and with $\|w(x)\| \le M_0$ and $\|Dw(x)\| \le M_1$ for all $x$. Let $p \ge 1$ and let
$u : \mathbb{R}^N \to \mathbb{R}$ be of class $C^1$. Then $$\int |u|^p \, d\sigma \le \max(N
M_1, p M_0) \Big( \int_\Omega |u|^p \, dx + \int_\Omega |u|^{p-1} \|Du\| \, dx \Big).$$ This is
the inequality of Nečas, *Direct Methods in the Theory of Elliptic Equations*, Chapter 2, §4,
and step 1 of the proof of Theorem 1 in §5.5 of Evans, *Partial Differential Equations*, in the
form with a transversal field.

The function $u$ need not have compact support, because only its values on $\overline{\Omega}$
enter. The proof lets $\varepsilon = 1/(n+1) \to 0$ in `BoundaryData.integral_rpowReg_le`, with
dominated convergence on both sides. -/
theorem integral_abs_rpow_le_of_contDiff {w : 𝔼 → 𝔼} (hw : ContDiff ℝ 1 w)
    (hwc : HasCompactSupport w) (hwν : ∀ᵐ x ∂B.σ, 1 ≤ ⟪w x, B.ν x⟫_ℝ) {M₀ M₁ : ℝ}
    (hM₀ : ∀ x, ‖w x‖ ≤ M₀) (hM₁ : ∀ x, ‖fderiv ℝ w x‖ ≤ M₁) {p : ℝ} (hp : 1 ≤ p)
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u) :
    ∫ x, |u x| ^ p ∂B.σ
      ≤ max (N * M₁) (p * M₀) * ((∫ x in (Ω : Set 𝔼), |u x| ^ p)
        + ∫ x in (Ω : Set 𝔼), |u x| ^ (p - 1) * ‖fderiv ℝ u x‖) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have := B.isFiniteMeasure_volume_restrict
  -- the bounds on `u` and `∇u` on the compact `closure Ω`
  obtain ⟨K, hK⟩ := B.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hu.continuous.continuousOn
  obtain ⟨K', hK'⟩ := B.isBounded.isCompact_closure.exists_bound_of_continuousOn
    (hu.continuous_fderiv one_ne_zero).continuousOn
  have hK₁ : ∀ x ∈ closure (Ω : Set 𝔼), |u x| ≤ max K 0 := fun x hx ↦
    (Real.norm_eq_abs (u x) ▸ hK x hx).trans (le_max_left _ _)
  have hK₂ : ∀ x ∈ closure (Ω : Set 𝔼), ‖fderiv ℝ u x‖ ≤ max K' 0 := fun x hx ↦
    (hK' x hx).trans (le_max_left _ _)
  -- the sequence `ε n = 1/(n+1)`
  set ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hεle : ∀ n, ε n ≤ 1 := fun n ↦
    div_le_one_of_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by positivity)
  have hε0 : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, .of_forall hεpos⟩
  have hε0' : Tendsto ε atTop (𝓝 0) := hε0.mono_right nhdsWithin_le_nhds
  -- the boundary integrals converge
  have hL : Tendsto (fun n ↦ ∫ x, Real.rpowReg p (ε n) (u x) ∂B.σ) atTop
      (𝓝 (∫ x, |u x| ^ p ∂B.σ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (max K 0 + 1) ^ p)
      (fun n ↦ ((Real.contDiff_rpowReg (n := 1) (hεpos n)).continuous.comp
        hu.continuous).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ?_)
      (.of_forall fun x ↦ (Real.tendsto_rpowReg hp0 (u x)).comp hε0)
    filter_upwards [B.ae_mem_frontier] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpowReg_nonneg (hεpos n) hp0.le _)]
    exact (Real.rpowReg_le (hεpos n) hp0.le _).trans (Real.rpow_le_rpow (by positivity)
      (add_le_add (hK₁ x (frontier_subset_closure hx)) (hεle n)) hp0.le)
  -- the interior integrals converge
  have hR₁ : Tendsto (fun n ↦ ∫ x in (Ω : Set 𝔼), (|u x| + ε n) ^ p) atTop
      (𝓝 (∫ x in (Ω : Set 𝔼), |u x| ^ p)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (max K 0 + 1) ^ p)
      (fun n ↦ ((hu.continuous.abs.add continuous_const).rpow_const
        fun x ↦ Or.inr hp0.le).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ?_) (.of_forall fun x ↦ ?_)
    · filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact Real.rpow_le_rpow (by positivity)
        (add_le_add (hK₁ x (subset_closure hx)) (hεle n)) hp0.le
    · have h := (tendsto_const_nhds (x := |u x|)).add hε0'
      rw [add_zero] at h
      exact ((Real.continuous_rpow_const hp0.le).tendsto (|u x|)).comp h
  have hR₂ : Tendsto (fun n ↦ ∫ x in (Ω : Set 𝔼), (|u x| + ε n) ^ (p - 1) * ‖fderiv ℝ u x‖)
      atTop (𝓝 (∫ x in (Ω : Set 𝔼), |u x| ^ (p - 1) * ‖fderiv ℝ u x‖)) := by
    have hp1 : 0 ≤ p - 1 := by linarith
    refine tendsto_integral_of_dominated_convergence
      (fun _ ↦ (max K 0 + 1) ^ (p - 1) * max K' 0)
      (fun n ↦ (((hu.continuous.abs.add continuous_const).rpow_const fun x ↦ Or.inr hp1).mul
        (hu.continuous_fderiv one_ne_zero).norm).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ ?_) (.of_forall fun x ↦ ?_)
    · filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul (Real.rpow_le_rpow (by positivity)
        (add_le_add (hK₁ x (subset_closure hx)) (hεle n)) hp1) (hK₂ x (subset_closure hx))
        (norm_nonneg _) (by positivity)
    · have h := (tendsto_const_nhds (x := |u x|)).add hε0'
      rw [add_zero] at h
      exact (((Real.continuous_rpow_const hp1).tendsto (|u x|)).comp h).mul
        (tendsto_const_nhds (x := ‖fderiv ℝ u x‖))
  exact le_of_tendsto_of_tendsto' hL ((hR₁.add hR₂).const_mul _) fun n ↦
    B.integral_rpowReg_le hw hwc hwν hM₀ hM₁ hp (hεpos n) hu

/-! ### The trace inequality in the Sobolev norm -/

open SobolevMultiIndex

/-- **Trace inequality on the smooth functions.** Suppose that the boundary data have a transversal
field, and let $1 \le p < \infty$. Then there is a constant $C \ge 0$ such that
$$\|u\|_{L^p(\sigma)} \le C \|U\|_{W^{1,p}(\Omega)}$$ for every $U \in W^{1,p}(\Omega)$ and
every $C^1$ function $u : \mathbb{R}^N \to \mathbb{R}$ equal to $U$ almost everywhere on
$\Omega$. This is [han2009theoretical] Theorem 7.3.10(b) on the smooth functions.

The left side is `eLpNorm u p B.σ`. The proof combines Nečas's inequality
`BoundaryData.integral_abs_rpow_le_of_contDiff` with $\int_\Omega |u|^{p-1} \|Du\| \le
\int_\Omega |u|^p + \int_\Omega \|Du\|^p$ and $\int_\Omega \|Du\|^p \le N^p \|U\|^p$. -/
theorem eLpNorm_le_of_contDiff (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : SobolevEuclidean N 1 p Ω) (u : 𝔼 → ℝ), ContDiff ℝ 1 u →
      fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u → eLpNorm u p B.σ ≤ ENNReal.ofReal (C * ‖U‖) := by
  obtain ⟨w, hw, hwc, hwν⟩ := hw
  obtain ⟨M₀, hM₀⟩ := hw.continuous.bounded_above_of_compact_support hwc
  obtain ⟨M₁, hM₁⟩ :=
    (hw.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hwc.fderiv (𝕜 := ℝ))
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_ne_top hp
  have hP0 : 0 < p.toReal := zero_lt_one.trans_le hP1
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hC₀ : 0 ≤ max (N * M₁) (p.toReal * M₀) := le_max_of_le_right (by positivity)
  refine ⟨(max (N * M₁) (p.toReal * M₀) * (2 + (N : ℝ) ^ p.toReal)) ^ (1 / p.toReal),
    by positivity, fun U u hu hU ↦ ?_⟩
  have hnec := B.integral_abs_rpow_le_of_contDiff hw hwc hwν hM₀ hM₁ hP1 hu
  have h1 : ∫ x in (Ω : Set 𝔼), |u x| ^ p.toReal ≤ ‖U‖ ^ p.toReal := by
    rw [SobolevEuclidean.integral_abs_rpow_eq_norm_fnL hp U hU]
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_fnL_apply_le U) hP0.le
  have h3 := SobolevEuclidean.integral_norm_fderiv_rpow_le hp U hu hU
  have hcont₁ : Continuous fun x ↦ |u x| ^ p.toReal :=
    hu.continuous.abs.rpow_const fun x ↦ Or.inr hP0.le
  have hcont₃ : Continuous fun x ↦ ‖fderiv ℝ u x‖ ^ p.toReal :=
    (hu.continuous_fderiv one_ne_zero).norm.rpow_const fun x ↦ Or.inr hP0.le
  have h2 : ∫ x in (Ω : Set 𝔼), |u x| ^ (p.toReal - 1) * ‖fderiv ℝ u x‖
      ≤ (∫ x in (Ω : Set 𝔼), |u x| ^ p.toReal)
        + ∫ x in (Ω : Set 𝔼), ‖fderiv ℝ u x‖ ^ p.toReal := by
    rw [← integral_add (B.integrableOn_of_continuous hcont₁) (B.integrableOn_of_continuous hcont₃)]
    refine integral_mono (B.integrableOn_of_continuous
      ((hu.continuous.abs.rpow_const fun x ↦ Or.inr (by linarith)).mul
        (hu.continuous_fderiv one_ne_zero).norm))
      (B.integrableOn_of_continuous (hcont₁.add hcont₃)) fun x ↦ ?_
    exact Real.rpow_sub_one_mul_le_add (abs_nonneg _) (norm_nonneg _) hP1
  have htot : ∫ x, |u x| ^ p.toReal ∂B.σ
      ≤ max (N * M₁) (p.toReal * M₀) * (2 + (N : ℝ) ^ p.toReal) * ‖U‖ ^ p.toReal := by
    calc ∫ x, |u x| ^ p.toReal ∂B.σ
        ≤ max (N * M₁) (p.toReal * M₀) * ((∫ x in (Ω : Set 𝔼), |u x| ^ p.toReal)
          + ∫ x in (Ω : Set 𝔼), |u x| ^ (p.toReal - 1) * ‖fderiv ℝ u x‖) := hnec
      _ ≤ max (N * M₁) (p.toReal * M₀)
          * (‖U‖ ^ p.toReal + (‖U‖ ^ p.toReal + (N : ℝ) ^ p.toReal * ‖U‖ ^ p.toReal)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 (h2.trans (add_le_add h1 h3))) hC₀
      _ = max (N * M₁) (p.toReal * M₀) * (2 + (N : ℝ) ^ p.toReal) * ‖U‖ ^ p.toReal := by ring
  rw [(B.memLp_of_continuous hu.continuous p).eLpNorm_eq_integral_rpow_norm hp0 hp]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [Real.norm_eq_abs]
  calc (∫ x, |u x| ^ p.toReal ∂B.σ) ^ p.toReal⁻¹
      ≤ (max (N * M₁) (p.toReal * M₀) * (2 + (N : ℝ) ^ p.toReal) * ‖U‖ ^ p.toReal)
          ^ p.toReal⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun x ↦ by positivity) htot (by positivity)
    _ = (max (N * M₁) (p.toReal * M₀) * (2 + (N : ℝ) ^ p.toReal)) ^ (1 / p.toReal) * ‖U‖ := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (norm_nonneg _),
          mul_inv_cancel₀ hP0.ne', Real.rpow_one, one_div]

/-! ### The trace operator -/

/-- Let $u \in W^{1,p}(\Omega)$, and let $v_1, v_2 : \mathbb{R}^N \to \mathbb{R}$ be continuous on
$\overline{\Omega}$ and equal to $u$ almost everywhere on $\Omega$. Then $v_1 = v_2$
$\sigma$-almost everywhere.

The two functions agree on $\overline{\Omega}$
(`SobolevEuclidean.eqOn_closure_of_ae_eq_of_continuousOn`), and $\sigma$ is carried by
$\partial\Omega \subseteq \overline{\Omega}$. -/
theorem ae_eq_of_ae_eq_of_continuousOn {p : ℝ≥0∞} (u : SobolevEuclidean N 1 p Ω)
    {v₁ v₂ : 𝔼 → ℝ} (h₁ : fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v₁)
    (h₂ : fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v₂) (hc₁ : ContinuousOn v₁ (closure (Ω : Set 𝔼)))
    (hc₂ : ContinuousOn v₂ (closure (Ω : Set 𝔼))) : v₁ =ᵐ[B.σ] v₂ :=
  B.ae_mem_frontier.mono fun _ hx ↦
    SobolevEuclidean.eqOn_closure_of_ae_eq_of_continuousOn u h₁ h₂ hc₁ hc₂
      (frontier_subset_closure hx)

section SmoothTrace

variable (p : ℝ≥0∞)

/-- **Restriction to $\partial\Omega$** on the subspace `SobolevEuclidean.smoothRestrictions` of
$W^{1,p}(\Omega)$, as a linear map into $L^p(\sigma)$: it maps $u$ to the class in $L^p(\sigma)$
of its smooth representative `SobolevEuclidean.smoothRep u`.

The map is linear because two representatives that are continuous on $\overline{\Omega}$ agree
$\sigma$-almost everywhere (`BoundaryData.ae_eq_of_ae_eq_of_continuousOn`). -/
def traceSmooth : SobolevEuclidean.smoothRestrictions N p Ω →ₗ[ℝ] Lp ℝ p B.σ where
  toFun u := (B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep u) p).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr
      (B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep (u + v)) p)
      ((B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep u) p).add
        (B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep v) p))
      (B.ae_eq_of_ae_eq_of_continuousOn (u + v : SobolevEuclidean N 1 p Ω)
      (SobolevEuclidean.fn_ae_eq_smoothRep (u + v)) ?_
      (SobolevEuclidean.continuous_smoothRep _).continuousOn
      ((SobolevEuclidean.continuous_smoothRep u).add
        (SobolevEuclidean.continuous_smoothRep v)).continuousOn)
    exact (fn_add _ _).trans ((SobolevEuclidean.fn_ae_eq_smoothRep u).add
      (SobolevEuclidean.fn_ae_eq_smoothRep v))
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr
      (B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep (c • u)) p)
      ((B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep u) p).const_smul c)
      (B.ae_eq_of_ae_eq_of_continuousOn (c • u : SobolevEuclidean N 1 p Ω)
      (SobolevEuclidean.fn_ae_eq_smoothRep (c • u)) ?_
      (SobolevEuclidean.continuous_smoothRep _).continuousOn
      ((SobolevEuclidean.continuous_smoothRep u).const_smul c).continuousOn)
    exact (fn_smul _ _).trans ((SobolevEuclidean.fn_ae_eq_smoothRep u).const_smul c)

/-- The function of `BoundaryData.traceSmooth p u` equals the smooth representative
`SobolevEuclidean.smoothRep u` $\sigma$-almost everywhere. -/
theorem coeFn_traceSmooth (u : SobolevEuclidean.smoothRestrictions N p Ω) :
    (B.traceSmooth p u : 𝔼 → ℝ) =ᵐ[B.σ] SobolevEuclidean.smoothRep u :=
  MemLp.coeFn_toLp (B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep u) p)

end SmoothTrace

section TraceL

/-- **The constant of the trace inequality**: for boundary data with a transversal field and
$1 \le p < \infty$, a constant $C \ge 0$ with $\|u\|_{L^p(\sigma)} \le C
\|U\|_{W^{1,p}(\Omega)}$ for every $U \in W^{1,p}(\Omega)$ and every $C^1$ function $u$ equal to
$U$ almost everywhere on $\Omega$.

It is the constant chosen by `BoundaryData.eLpNorm_le_of_contDiff`, not the best constant. -/
def traceConst (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) : ℝ :=
  Classical.choose (B.eLpNorm_le_of_contDiff hw p hp)

/-- The trace constant `BoundaryData.traceConst` is nonnegative. -/
theorem traceConst_nonneg (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    0 ≤ B.traceConst hw p hp :=
  (Classical.choose_spec (B.eLpNorm_le_of_contDiff hw p hp)).1

/-- Suppose that the boundary data have a transversal field, and let $1 \le p < \infty$. For
$U \in W^{1,p}(\Omega)$ and a $C^1$ function $u$ equal to $U$ almost everywhere on $\Omega$,
$\|u\|_{L^p(\sigma)} \le C \|U\|_{W^{1,p}(\Omega)}$ with $C$ the constant
`BoundaryData.traceConst`. -/
theorem eLpNorm_le_traceConst_mul (hw : B.HasTransversalField) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (U : SobolevEuclidean N 1 p Ω) {u : 𝔼 → ℝ} (hu : ContDiff ℝ 1 u)
    (hU : fn U =ᵐ[volume.restrict (Ω : Set 𝔼)] u) :
    eLpNorm u p B.σ ≤ ENNReal.ofReal (B.traceConst hw p hp * ‖U‖) :=
  (Classical.choose_spec (B.eLpNorm_le_of_contDiff hw p hp)).2 U u hu hU

/-- **Restriction to $\partial\Omega$** on the subspace `SobolevEuclidean.smoothRestrictions` of
$W^{1,p}(\Omega)$, as a bounded operator into $L^p(\sigma)$, for boundary data with a
transversal field and $1 \le p < \infty$. It is the linear map `BoundaryData.traceSmooth`, with
operator norm at most `BoundaryData.traceConst`. -/
def traceSmoothL (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SobolevEuclidean.smoothRestrictions N p Ω →L[ℝ] Lp ℝ p B.σ :=
  (B.traceSmooth p).mkContinuous (B.traceConst hw p hp) fun u ↦ by
    change ‖(B.memLp_of_continuous (SobolevEuclidean.continuous_smoothRep u) p).toLp _‖ ≤ _
    rw [Lp.norm_toLp]
    have h := B.eLpNorm_le_traceConst_mul hw hp u (SobolevEuclidean.contDiff_smoothRep u |>.of_le
      (by simp)) (SobolevEuclidean.fn_ae_eq_smoothRep u)
    refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (B.traceConst_nonneg hw p hp) (norm_nonneg _))]
    rfl

/-- The function of `BoundaryData.traceSmoothL` applied to $u$ equals the smooth representative
`SobolevEuclidean.smoothRep u` $\sigma$-almost everywhere. -/
theorem coeFn_traceSmoothL (hw : B.HasTransversalField) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : SobolevEuclidean.smoothRestrictions N p Ω) :
    (B.traceSmoothL hw p hp u : 𝔼 → ℝ) =ᵐ[B.σ] SobolevEuclidean.smoothRep u :=
  B.coeFn_traceSmooth p u

/-- The operator norm of `BoundaryData.traceSmoothL` is at most `BoundaryData.traceConst`. -/
theorem norm_traceSmoothL_le (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) : ‖B.traceSmoothL hw p hp‖ ≤ B.traceConst hw p hp :=
  LinearMap.mkContinuous_norm_le _ (B.traceConst_nonneg hw p hp) _

/-- **The trace operator** $T : W^{1,p}(\Omega) \to L^p(\sigma)$ of boundary data with a transversal
field, for $1 \le p < \infty$. It is the continuous extension of the restriction to
$\partial\Omega$, `BoundaryData.traceSmoothL`, from the subspace
`SobolevEuclidean.smoothRestrictions` to all of $W^{1,p}(\Omega)$.

The extension is `ContinuousLinearMap.extend` along the inclusion of the subspace. It is the
trace when the subspace is dense, which is `SobolevEuclidean.HasSmoothDensity N p Ω`. If the
subspace is not dense, the extension is the zero operator. As for Mathlib's `extend`, the
density hypothesis enters the lemmas (`BoundaryData.traceL_ae_eq_of_contDiff`,
`BoundaryData.traceL_ae_eq_of_continuousOn`, `BoundaryData.traceL_unique`,
`BoundaryData.norm_traceL_le`) and not the definition. -/
def traceL (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SobolevEuclidean N 1 p Ω →L[ℝ] Lp ℝ p B.σ :=
  (B.traceSmoothL hw p hp).extend (SobolevEuclidean.smoothRestrictions N p Ω).subtypeL

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Suppose that the boundary data have a transversal field, that $1 \le p < \infty$, and that the
smooth-representable elements are dense in $W^{1,p}(\Omega)$
(`SobolevEuclidean.HasSmoothDensity`). For $u$ in the subspace
`SobolevEuclidean.smoothRestrictions`, the trace $Tu$ is `BoundaryData.traceSmoothL` applied to
$u$, the class of the restriction of its smooth representative. -/
theorem traceL_apply_of_mem (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) {u : SobolevEuclidean N 1 p Ω}
    (hu : u ∈ SobolevEuclidean.smoothRestrictions N p Ω) :
    B.traceL hw p hp u = B.traceSmoothL hw p hp ⟨u, hu⟩ :=
  ContinuousLinearMap.extend_eq (B.traceSmoothL hw p hp) hd.dense_smoothRestrictions.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing ⟨u, hu⟩

/-- **The trace of a smooth-representable element is its restriction.** Suppose that the boundary
data have a transversal field, that $1 \le p < \infty$, and that the smooth-representable
elements are dense in $W^{1,p}(\Omega)$. Let $u \in W^{1,p}(\Omega)$, and let
$v : \mathbb{R}^N \to \mathbb{R}$ be smooth with compact support and equal to $u$ almost
everywhere on $\Omega$. Then $Tu = v$ $\sigma$-almost everywhere. -/
theorem traceL_ae_eq_of_contDiff (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) (u : SobolevEuclidean N 1 p Ω)
    {v : 𝔼 → ℝ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (huv : fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v) :
    (B.traceL hw p hp u : 𝔼 → ℝ) =ᵐ[B.σ] v := by
  have hu : u ∈ SobolevEuclidean.smoothRestrictions N p Ω := ⟨v, hv, hvc, huv⟩
  rw [B.traceL_apply_of_mem hw hp hd hu]
  refine (B.coeFn_traceSmoothL hw hp ⟨u, hu⟩).trans ?_
  exact B.ae_eq_of_ae_eq_of_continuousOn u (SobolevEuclidean.fn_ae_eq_smoothRep ⟨u, hu⟩) huv
    (SobolevEuclidean.continuous_smoothRep _).continuousOn hv.continuous.continuousOn

/-- **The norm of the trace.** Suppose that the boundary data have a transversal field, that
$1 \le p < \infty$, and that the smooth-representable elements are dense in $W^{1,p}(\Omega)$.
Then the trace operator has norm $\|T\| \le C$, with $C$ the constant `BoundaryData.traceConst`.
This is the bound of [han2009theoretical] Theorem 7.3.10(b). -/
theorem norm_traceL_le (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) :
    ‖B.traceL hw p hp‖ ≤ B.traceConst hw p hp := by
  refine (ContinuousLinearMap.opNorm_extend_le (N := 1) _ hd.dense_smoothRestrictions.denseRange_val
    fun _ ↦ ?_).trans ?_
  · simp
  · rw [NNReal.coe_one, one_mul]
    exact B.norm_traceSmoothL_le hw p hp

/-- **The trace inequality.** Suppose that the boundary data have a transversal field, that
$1 \le p < \infty$, and that the smooth-representable elements are dense in $W^{1,p}(\Omega)$.
Then $$\|Tu\|_{L^p(\sigma)} \le C \|u\|_{W^{1,p}(\Omega)}$$ for every $u \in W^{1,p}(\Omega)$,
with $C$ the constant `BoundaryData.traceConst`. This is [han2009theoretical] Theorem 7.3.10(b). -/
theorem norm_traceL_apply_le (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) (u : SobolevEuclidean N 1 p Ω) :
    ‖B.traceL hw p hp u‖ ≤ B.traceConst hw p hp * ‖u‖ :=
  ((B.traceL hw p hp).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (B.norm_traceL_le hw hp hd) (norm_nonneg _))

/-- **Uniqueness of an operator that restricts the smooth representatives.** Let
$1 \le p \le \infty$, and suppose that the smooth-representable elements are dense in
$W^{1,p}(\Omega)$. Let $T, T' : W^{1,p}(\Omega) \to L^p(\sigma)$ be bounded operators with
$Tu = v$ and $T'u = v$ $\sigma$-almost everywhere whenever $u \in W^{1,p}(\Omega)$,
$v : \mathbb{R}^N \to \mathbb{R}$ is smooth with compact support, and $u = v$ almost everywhere
on $\Omega$. Then $T = T'$. -/
theorem ext_of_forall_ae_eq (hd : SobolevEuclidean.HasSmoothDensity N p Ω)
    {T T' : SobolevEuclidean N 1 p Ω →L[ℝ] Lp ℝ p B.σ}
    (hT : ∀ (u : SobolevEuclidean N 1 p Ω) (v : 𝔼 → ℝ), ContDiff ℝ ∞ v → HasCompactSupport v →
      fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v → (T u : 𝔼 → ℝ) =ᵐ[B.σ] v)
    (hT' : ∀ (u : SobolevEuclidean N 1 p Ω) (v : 𝔼 → ℝ), ContDiff ℝ ∞ v → HasCompactSupport v →
      fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v → (T' u : 𝔼 → ℝ) =ᵐ[B.σ] v) :
    T = T' := by
  have h : ⇑T = ⇑T' := Continuous.ext_on hd.dense_smoothRestrictions T.continuous T'.continuous
    fun u ⟨v, hv, hvc, huv⟩ ↦ Lp.ext ((hT u v hv hvc huv).trans (hT' u v hv hvc huv).symm)
  exact ContinuousLinearMap.ext fun u ↦ congrFun h u

/-- **Uniqueness of the trace.** Suppose that the boundary data have a transversal field, that
$1 \le p < \infty$, and that the smooth-representable elements are dense in $W^{1,p}(\Omega)$.
Let $T' : W^{1,p}(\Omega) \to L^p(\sigma)$ be a bounded operator with $T'u = v$ $\sigma$-almost
everywhere whenever $v : \mathbb{R}^N \to \mathbb{R}$ is smooth with compact support and equal
to $u \in W^{1,p}(\Omega)$ almost everywhere on $\Omega$. Then $T'$ is the trace operator
`BoundaryData.traceL`. -/
theorem traceL_unique (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω)
    {T' : SobolevEuclidean N 1 p Ω →L[ℝ] Lp ℝ p B.σ}
    (hT' : ∀ (u : SobolevEuclidean N 1 p Ω) (v : 𝔼 → ℝ), ContDiff ℝ ∞ v → HasCompactSupport v →
      fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] v → (T' u : 𝔼 → ℝ) =ᵐ[B.σ] v) :
    T' = B.traceL hw p hp :=
  B.ext_of_forall_ae_eq hd hT' fun u _ hv hvc huv ↦ B.traceL_ae_eq_of_contDiff hw hp hd u hv hvc huv

/-- **Two trace families agree.** Let $\mathcal{T}$ and $\mathcal{T}'$ be two trace families
(`BoundaryData.TraceFamily`) over the same boundary data, and let $1 \le p < \infty$ be an
exponent at which the smooth-representable elements are dense in $W^{1,p}(\Omega)$. Then the
trace operators of $\mathcal{T}$ and $\mathcal{T}'$ at $p$ are equal.

Both operators restrict the smooth representatives by the field
`BoundaryData.TraceFamily.traceL_ae_eq`, so `BoundaryData.ext_of_forall_ae_eq` applies. For a
convex polygon, this shows that the two constructions of the trace agree
(`Triangulation.traceFamily_of_convex_traceL`). -/
theorem TraceFamily.traceL_eq_of_hasSmoothDensity (𝒯 𝒯' : B.TraceFamily) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) : 𝒯.traceL p hp = 𝒯'.traceL p hp :=
  B.ext_of_forall_ae_eq hd
    (fun u v hv _ huv ↦ 𝒯.traceL_ae_eq p hp u v huv hv.continuous.continuousOn)
    (fun u v hv _ huv ↦ 𝒯'.traceL_ae_eq p hp u v huv hv.continuous.continuousOn)

/-- **The trace of a function continuous up to the boundary is its restriction.** Suppose that the
boundary data have a transversal field, that $1 \le p < \infty$, that the smooth-representable
elements are dense in $W^{1,p}(\Omega)$ (`SobolevEuclidean.HasSmoothDensity`), and that every
element of $W^{1,p}(\Omega)$ with a representative continuous on $\overline{\Omega}$ is a limit
of smooth functions in $W^{1,p}(\Omega)$ and uniformly on $\overline{\Omega}$
(`SobolevEuclidean.HasUniformSmoothDensity`). Let $u \in W^{1,p}(\Omega)$, and let
$\tilde u : \mathbb{R}^N \to \mathbb{R}$ be continuous on $\overline{\Omega}$ and equal to $u$
almost everywhere on $\Omega$. Then $Tu = \tilde u$ $\sigma$-almost everywhere. This is Evans,
*Partial Differential Equations*, §5.5, Theorem 1(ii), and [han2009theoretical] Theorem
7.3.10(a).

The approximants $v_n$ have the traces $v_n$ (`BoundaryData.traceL_ae_eq_of_contDiff`). These
traces converge to $Tu$ in $L^p(\sigma)$ because $T$ is continuous, and to $\tilde u$ because
$v_n \to \tilde u$ uniformly on $\overline{\Omega} \supseteq \partial\Omega$ and $\sigma$ is
finite. -/
theorem traceL_ae_eq_of_continuousOn (hw : B.HasTransversalField) (hp : p ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω)
    (hdu : SobolevEuclidean.HasUniformSmoothDensity N p Ω) (u : SobolevEuclidean N 1 p Ω)
    {ũ : 𝔼 → ℝ} (hu : fn u =ᵐ[volume.restrict (Ω : Set 𝔼)] ũ)
    (hc : ContinuousOn ũ (closure (Ω : Set 𝔼))) : (B.traceL hw p hp u : 𝔼 → ℝ) =ᵐ[B.σ] ũ := by
  obtain ⟨v, hv, hvc, ⟨w, hw', hwu⟩, hunif⟩ := hdu u ũ hu hc
  have hũ : MemLp ũ p B.σ := B.memLp_of_continuousOn hc p
  have h1 : Tendsto (fun n ↦ B.traceL hw p hp (w n)) atTop (𝓝 (B.traceL hw p hp u)) :=
    ((B.traceL hw p hp).continuous.tendsto u).comp hwu
  have h2 : Tendsto (fun n ↦ B.traceL hw p hp (w n)) atTop (𝓝 (hũ.toLp ũ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hMtop : B.σ univ ^ p.toReal⁻¹ ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
    set M := (B.σ univ ^ p.toReal⁻¹).toReal with hM
    have hδ : 0 < ε / (M + 1) := by positivity
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hunif _ hδ)
    refine ⟨n₀, fun n hn ↦ ?_⟩
    rw [Lp.dist_def]
    have hae : (⇑(B.traceL hw p hp (w n)) - ⇑(hũ.toLp ũ)) =ᵐ[B.σ] v n - ũ := by
      filter_upwards [B.traceL_ae_eq_of_contDiff hw hp hd (w n) (hv n) (hvc n) (hw' n),
        hũ.coeFn_toLp] with x hx hx'
      rw [Pi.sub_apply, Pi.sub_apply, hx, hx']
    calc (eLpNorm (⇑(B.traceL hw p hp (w n)) - ⇑(hũ.toLp ũ)) p B.σ).toReal
        = (eLpNorm (v n - ũ) p B.σ).toReal := by rw [eLpNorm_congr_ae hae]
      _ ≤ (B.σ univ ^ p.toReal⁻¹ * ENNReal.ofReal (ε / (M + 1))).toReal := by
          refine ENNReal.toReal_mono (ENNReal.mul_ne_top hMtop ENNReal.ofReal_ne_top) ?_
          refine eLpNorm_le_of_ae_bound
            ((hv n).continuous.aestronglyMeasurable.sub hũ.aestronglyMeasurable) ?_
          filter_upwards [B.ae_mem_frontier] with x hx
          rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm, ← Real.dist_eq]
          exact (hn₀ n hn x (frontier_subset_closure hx)).le
      _ = M * (ε / (M + 1)) := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le]
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  rw [tendsto_nhds_unique h1 h2]
  exact hũ.coeFn_toLp

end TraceL

/-! ### Green's formula by density -/

section Green

/-- **Green's formula for smooth-representable elements.** Suppose that the boundary data have a
transversal field, that $1 \le p, q < \infty$, and that the smooth-representable elements are
dense in $W^{1,p}(\Omega)$ and in $W^{1,q}(\Omega)$. Let $u \in W^{1,p}(\Omega)$ and
$v \in W^{1,q}(\Omega)$ be in the subspaces `SobolevEuclidean.smoothRestrictions`, and let $i$
be a coordinate index. Then $$\int_\Omega \partial_i u \, v \, dx + \int_\Omega u \, \partial_i
v \, dx = \int Tu \, Tv \, \nu_i \, d\sigma.$$

The exponents need not be conjugate. The formula is the classical Green formula
`BoundaryData.integral_fderiv_mul_add_eq` for the smooth representatives. -/
theorem green_of_mem_smoothRestrictions (hw : B.HasTransversalField) {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) (hd' : SobolevEuclidean.HasSmoothDensity N q Ω)
    {u : SobolevEuclidean N 1 p Ω} (hu : u ∈ SobolevEuclidean.smoothRestrictions N p Ω)
    {v : SobolevEuclidean N 1 q Ω} (hv : v ∈ SobolevEuclidean.smoothRestrictions N q Ω)
    (i : Fin N) :
    (∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * fn v x)
      + ∫ x in (Ω : Set 𝔼), fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼 → ℝ) x
      = ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * (B.traceL hw q hq v : 𝔼 → ℝ) x * B.ν x i ∂B.σ := by
  obtain ⟨ũ, hũ, hũc, huũ⟩ := hu
  obtain ⟨v', hv', hv'c, hvv'⟩ := hv
  have hũ1 : ContDiff ℝ 1 ũ := hũ.of_le (by simp)
  have hv'1 : ContDiff ℝ 1 v' := hv'.of_le (by simp)
  have h := B.integral_fderiv_mul_add_eq hũ1.continuous.continuousOn
    (hũ1.contDiffOn.contDiffOnClosure Ω.isOpen) hv'1.continuous.continuousOn
    (hv'1.contDiffOn.contDiffOnClosure Ω.isOpen) i
  have e1 : ∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * fn v x
      = ∫ x in (Ω : Set 𝔼), fderiv ℝ ũ x (EuclideanSpace.single i 1) * v' x := by
    refine integral_congr_ae ?_
    filter_upwards [SobolevEuclidean.weakDeriv_single_ae_eq_fderiv u hũ1 huũ i, hvv'] with x h1 h2
    rw [h1, h2]
  have e2 : ∫ x in (Ω : Set 𝔼), fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼 → ℝ) x
      = ∫ x in (Ω : Set 𝔼), ũ x * fderiv ℝ v' x (EuclideanSpace.single i 1) := by
    refine integral_congr_ae ?_
    filter_upwards [SobolevEuclidean.weakDeriv_single_ae_eq_fderiv v hv'1 hvv' i, huũ] with x h1 h2
    rw [h1, h2]
  have e3 : ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * (B.traceL hw q hq v : 𝔼 → ℝ) x * B.ν x i ∂B.σ
      = ∫ x, ũ x * v' x * B.ν x i ∂B.σ := by
    refine integral_congr_ae ?_
    filter_upwards [B.traceL_ae_eq_of_contDiff hw hp hd u hũ hũc huũ,
      B.traceL_ae_eq_of_contDiff hw hq hd' v hv' hv'c hvv'] with x h1 h2
    rw [h1, h2]
  rw [e1, e2, e3]
  exact h

/-- **Green's formula.** Suppose that the boundary data have a transversal field, that $p$ and $q$
are finite conjugate exponents, $1/p + 1/q = 1$ (so $1 < p, q < \infty$), and that the
smooth-representable elements are dense in $W^{1,p}(\Omega)$ and in $W^{1,q}(\Omega)$. Then for
$u \in W^{1,p}(\Omega)$, $v \in W^{1,q}(\Omega)$ and each coordinate index $i$, $$\int_\Omega
\partial_i u \, v \, dx + \int_\Omega u \, \partial_i v \, dx = \int Tu \, Tv \, \nu_i \,
d\sigma.$$ This is [han2009theoretical] Proposition 7.6.1 and (7.6.3), and
[grisvard2011elliptic] Theorem 1.5.3.1.

Both sides are continuous in $(u, v)$, and they agree on the dense set of smooth-representable
pairs (`BoundaryData.green_of_mem_smoothRestrictions`). -/
theorem green_of_hasSmoothDensity (hw : B.HasTransversalField) (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] [p.HolderConjugate q] (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hd : SobolevEuclidean.HasSmoothDensity N p Ω) (hd' : SobolevEuclidean.HasSmoothDensity N q Ω)
    (u : SobolevEuclidean N 1 p Ω) (v : SobolevEuclidean N 1 q Ω) (i : Fin N) :
    (∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * fn v x)
      + ∫ x in (Ω : Set 𝔼), fn u x * (weakDeriv v (MultiIndexLE.single i) : 𝔼 → ℝ) x
      = ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * (B.traceL hw q hq v : 𝔼 → ℝ) x * B.ν x i ∂B.σ := by
  refine (hd.dense_smoothRestrictions.prod hd'.dense_smoothRestrictions).induction
    (P := fun x : SobolevEuclidean N 1 p Ω × SobolevEuclidean N 1 q Ω ↦
      (∫ y in (Ω : Set 𝔼), (weakDeriv x.1 (MultiIndexLE.single i) : 𝔼 → ℝ) y * fn x.2 y)
        + ∫ y in (Ω : Set 𝔼), fn x.1 y * (weakDeriv x.2 (MultiIndexLE.single i) : 𝔼 → ℝ) y
        = ∫ y, (B.traceL hw p hp x.1 : 𝔼 → ℝ) y * (B.traceL hw q hq x.2 : 𝔼 → ℝ) y * B.ν y i
          ∂B.σ)
    (fun x hx ↦ B.green_of_mem_smoothRestrictions hw hp hq hd hd' hx.1 hx.2 i) ?_ (u, v)
  refine isClosed_eq ?_ ?_
  · have c1 : Continuous fun x : SobolevEuclidean N 1 p Ω × SobolevEuclidean N 1 q Ω ↦
        ∫ y in (Ω : Set 𝔼), (weakDeriv x.1 (MultiIndexLE.single i) : 𝔼 → ℝ) y * fn x.2 y :=
      (MeasureTheory.continuous_integral_mul_prod p q).comp
        (((weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
          (MultiIndexLE.single i)).continuous.comp continuous_fst).prodMk
          ((fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 q Ω volume).continuous.comp
            continuous_snd))
    have c2 : Continuous fun x : SobolevEuclidean N 1 p Ω × SobolevEuclidean N 1 q Ω ↦
        ∫ y in (Ω : Set 𝔼), fn x.1 y * (weakDeriv x.2 (MultiIndexLE.single i) : 𝔼 → ℝ) y :=
      (MeasureTheory.continuous_integral_mul_prod p q).comp
        (((fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).continuous.comp
          continuous_fst).prodMk
          ((weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 q Ω volume
            (MultiIndexLE.single i)).continuous.comp continuous_snd))
    exact c1.add c2
  · have c3 : Continuous fun x : SobolevEuclidean N 1 p Ω × SobolevEuclidean N 1 q Ω ↦
        ∫ y, (B.traceL hw p hp x.1 : 𝔼 → ℝ) y * (B.mulNormalL q i (B.traceL hw q hq x.2) : 𝔼 → ℝ) y
          ∂B.σ :=
      (MeasureTheory.continuous_integral_mul_prod p q).comp
        (((B.traceL hw p hp).continuous.comp continuous_fst).prodMk
          ((B.mulNormalL q i).continuous.comp ((B.traceL hw q hq).continuous.comp continuous_snd)))
    refine c3.congr fun x ↦ integral_congr_ae ?_
    filter_upwards [B.coeFn_mulNormalL q i (B.traceL hw q hq x.2)] with y hy
    rw [hy]
    ring

/-- **Green's formula against a $C^1$ test function.** Suppose that the boundary data have a
transversal field, that $1 \le p < \infty$, and that the smooth-representable elements are dense
in $W^{1,p}(\Omega)$. Let $u \in W^{1,p}(\Omega)$, let $\varphi : \mathbb{R}^N \to \mathbb{R}$
be of class $C^1$ with compact support, and let $i$ be a coordinate index. Then $$\int_\Omega
\partial_i u \, \varphi \, dx + \int_\Omega u \, \partial_i \varphi \, dx = \int Tu \, \varphi
\, \nu_i \, d\sigma.$$

Unlike `BoundaryData.green_of_hasSmoothDensity`, this holds at $p = 1$. Only $u$ is
approximated: the bounded functions $\varphi$, $\partial_i \varphi$ and $\varphi \nu_i$ lie in
$L^{p'}$ of the finite measures, with $p'$ the conjugate exponent ($p' = \infty$ at $p = 1$), so
every term is continuous in $u$. The derivative $\partial_i \varphi$ is
`fderiv ℝ φ x (EuclideanSpace.single i 1)`. -/
theorem green_contDiff_of_hasSmoothDensity (hw : B.HasTransversalField) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hd : SobolevEuclidean.HasSmoothDensity N p Ω)
    (u : SobolevEuclidean N 1 p Ω) {φ : 𝔼 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (i : Fin N) :
    (∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * φ x)
      + ∫ x in (Ω : Set 𝔼), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * φ x * B.ν x i ∂B.σ := by
  have : p.HolderConjugate (ENNReal.conjExponent p) :=
    ENNReal.HolderConjugate.conjExponent Fact.out
  have : Fact (1 ≤ ENNReal.conjExponent p) := ENNReal.fact_one_le_conjExponent
  have := B.isFiniteMeasure_volume_restrict
  -- the fixed factors as `L^{p'}` elements
  obtain ⟨K, hK⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨K', hK'⟩ :=
    (hφ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hφc.fderiv (𝕜 := ℝ))
  have hφq : MemLp φ (ENNReal.conjExponent p) (volume.restrict (Ω : Set 𝔼)) :=
    MemLp.of_bound hφ.continuous.aestronglyMeasurable K (.of_forall hK)
  have hdφq : MemLp (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) (ENNReal.conjExponent p)
      (volume.restrict (Ω : Set 𝔼)) :=
    MemLp.of_bound ((hφ.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).aestronglyMeasurable K' (.of_forall fun x ↦
        ((fderiv ℝ φ x).le_opNorm _).trans (by simpa using hK' x))
  have hφν : MemLp (fun x ↦ φ x * B.ν x i) (ENNReal.conjExponent p) B.σ := by
    exact MemLp.ae_eq (Eventually.of_forall fun x ↦ mul_comm (B.ν x i) (φ x))
      (B.memLp_ν_apply_mul (B.memLp_of_continuous hφ.continuous (ENNReal.conjExponent p)) i)
  -- the identity on the smooth-representable elements
  have key : ∀ u ∈ SobolevEuclidean.smoothRestrictions N p Ω,
      (∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * φ x)
        + ∫ x in (Ω : Set 𝔼), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
        = ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * φ x * B.ν x i ∂B.σ := by
    rintro u ⟨ũ, hũ, hũc, huũ⟩
    have hũ1 : ContDiff ℝ 1 ũ := hũ.of_le (by simp)
    have h := B.integral_fderiv_mul_add_eq hũ1.continuous.continuousOn
      (hũ1.contDiffOn.contDiffOnClosure Ω.isOpen) hφ.continuous.continuousOn
      (hφ.contDiffOn.contDiffOnClosure Ω.isOpen) i
    have e1 : ∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * φ x
        = ∫ x in (Ω : Set 𝔼), fderiv ℝ ũ x (EuclideanSpace.single i 1) * φ x := by
      refine integral_congr_ae ?_
      filter_upwards [SobolevEuclidean.weakDeriv_single_ae_eq_fderiv u hũ1 huũ i] with x h1
      rw [h1]
    have e2 : ∫ x in (Ω : Set 𝔼), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
        = ∫ x in (Ω : Set 𝔼), ũ x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      refine integral_congr_ae ?_
      filter_upwards [huũ] with x h1
      rw [h1]
    have e3 : ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * φ x * B.ν x i ∂B.σ
        = ∫ x, ũ x * φ x * B.ν x i ∂B.σ := by
      refine integral_congr_ae ?_
      filter_upwards [B.traceL_ae_eq_of_contDiff hw hp hd u hũ hũc huũ] with x h1
      rw [h1]
    rw [e1, e2, e3]
    exact h
  refine hd.dense_smoothRestrictions.induction (P := fun u : SobolevEuclidean N 1 p Ω ↦
    (∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * φ x)
      + ∫ x in (Ω : Set 𝔼), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1)
      = ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * φ x * B.ν x i ∂B.σ) key ?_ u
  refine isClosed_eq ?_ ?_
  · have c1 : Continuous fun u : SobolevEuclidean N 1 p Ω ↦
        ∫ x in (Ω : Set 𝔼), (weakDeriv u (MultiIndexLE.single i) : 𝔼 → ℝ) x * (hφq.toLp φ) x :=
      (MeasureTheory.continuous_integral_mul_prod p (ENNReal.conjExponent p)).comp
        ((weakDerivL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume
          (MultiIndexLE.single i)).continuous.prodMk continuous_const)
    have c2 : Continuous fun u : SobolevEuclidean N 1 p Ω ↦
        ∫ x in (Ω : Set 𝔼), fn u x * (hdφq.toLp _) x :=
      (MeasureTheory.continuous_integral_mul_prod p (ENNReal.conjExponent p)).comp
        ((fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).continuous.prodMk
          continuous_const)
    refine (c1.add c2).congr fun u ↦ ?_
    rw [Pi.add_apply]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [hφq.coeFn_toLp] with x hx
      rw [hx]
    · refine integral_congr_ae ?_
      filter_upwards [hdφq.coeFn_toLp] with x hx
      rw [hx]
  · have c3 : Continuous fun u : SobolevEuclidean N 1 p Ω ↦
        ∫ x, (B.traceL hw p hp u : 𝔼 → ℝ) x * (hφν.toLp _) x ∂B.σ :=
      (MeasureTheory.continuous_integral_mul_prod p (ENNReal.conjExponent p)).comp
        ((B.traceL hw p hp).continuous.prodMk continuous_const)
    refine c3.congr fun u ↦ integral_congr_ae ?_
    filter_upwards [hφν.coeFn_toLp] with x hx
    rw [hx, mul_assoc]

end Green

/-! ### The trace family -/

/-- **The trace family** of boundary data with a transversal field, when at every exponent
$1 \le p < \infty$ the smooth-representable elements are dense in $W^{1,p}(\Omega)$ and the
uniform approximation `SobolevEuclidean.HasUniformSmoothDensity` holds. Its trace operator at
$p$ is `BoundaryData.traceL`, its restriction property is
`BoundaryData.traceL_ae_eq_of_continuousOn`, and its Green formulas are
`BoundaryData.green_of_hasSmoothDensity` and `BoundaryData.green_contDiff_of_hasSmoothDensity`.

The trace families `IsContDiffDomain.traceFamily` and `EuclideanSpace.triangleTraceFamily` are
this construction with the density theorems of `Numlib.Analysis.Sobolev.Boundary.Density`. -/
def traceFamily (hw : B.HasTransversalField)
    (hd : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → SobolevEuclidean.HasSmoothDensity N p Ω)
    (hdu : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → SobolevEuclidean.HasUniformSmoothDensity N p Ω) :
    B.TraceFamily where
  traceL p _ hp := B.traceL hw p hp
  traceL_ae_eq p _ hp u _ hu hc := B.traceL_ae_eq_of_continuousOn hw hp (hd p hp) (hdu p hp) u hu hc
  green p q _ _ _ hp hq u v i :=
    B.green_of_hasSmoothDensity hw p q hp hq (hd p hp) (hd q hq) u v i
  green_contDiff p _ hp u _ hφ hφc i :=
    B.green_contDiff_of_hasSmoothDensity hw p hp (hd p hp) u hφ hφc i

/-- The trace operator of `BoundaryData.traceFamily` at the exponent $p$ is `BoundaryData.traceL` at
$p$. -/
@[simp]
theorem traceFamily_traceL (hw : B.HasTransversalField)
    (hd : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → SobolevEuclidean.HasSmoothDensity N p Ω)
    (hdu : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → SobolevEuclidean.HasUniformSmoothDensity N p Ω)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    (B.traceFamily hw hd hdu).traceL p hp = B.traceL hw p hp :=
  rfl

/-! ### Nečas's inequality for every $W^{1,p}$ function, and compactness of the trace -/

section Compact

/-- **Nečas's inequality for every $W^{1,p}$ function.** Suppose that the boundary data have a
transversal field, that $1 \le p < \infty$, and that the smooth-representable elements are dense
in $W^{1,p}(\Omega)$. Then there is a constant $C \ge 0$ such that $$\int |Tu|^p \, d\sigma \le
C \big( \|u\|_{L^p(\Omega)}^p + \|u\|_{L^p(\Omega)}^{p-1} \|\nabla u\|_{L^p(\Omega)} \big)$$ for
every $u \in W^{1,p}(\Omega)$. This is the estimate behind the compactness in
[han2009theoretical] Theorem 7.3.10(c).

The norm $\|u\|_{L^p(\Omega)}$ is the norm of `SobolevMultiIndex.fnL` applied to $u$, and
$\|\nabla u\|_{L^p(\Omega)}$ is `SobolevMultiIndex.gradNorm u`, the $\ell^p$ combination of the
$L^p$ norms of the partial derivatives. For smooth-representable $u$ the inequality is
`BoundaryData.integral_abs_rpow_le_of_contDiff` with Hölder's inequality on the mixed term
(`MeasureTheory.integral_norm_rpow_sub_one_mul_norm_le`). Both sides are continuous in $u$, and
the smooth-representable elements are dense. -/
theorem integral_abs_traceL_rpow_le (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hd : SobolevEuclidean.HasSmoothDensity N p Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevEuclidean N 1 p Ω,
      ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ
        ≤ C * (‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ p.toReal
          + ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ (p.toReal - 1)
            * gradNorm u) := by
  have hw₀ := hw
  obtain ⟨w, hw', hwc, hwν⟩ := hw₀
  obtain ⟨M₀, hM₀⟩ := hw'.continuous.bounded_above_of_compact_support hwc
  obtain ⟨M₁, hM₁⟩ :=
    (hw'.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hwc.fderiv (𝕜 := ℝ))
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_ne_top hp
  have hP0 : 0 < p.toReal := zero_lt_one.trans_le hP1
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hC₀ : 0 ≤ max (N * M₁) (p.toReal * M₀) := le_max_of_le_right (by positivity)
  refine ⟨max (N * M₁) (p.toReal * M₀) * (1 + N), by positivity, fun u ↦ ?_⟩
  -- the inequality on the smooth-representable elements
  have key : ∀ u ∈ SobolevEuclidean.smoothRestrictions N p Ω,
      ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ
        ≤ max (N * M₁) (p.toReal * M₀) * (1 + N)
          * (‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ p.toReal
            + ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ (p.toReal - 1)
              * gradNorm u) := by
    rintro u ⟨v, hv, hvc, huv⟩
    have hv1 : ContDiff ℝ 1 v := hv.of_le (by simp)
    have hnec := B.integral_abs_rpow_le_of_contDiff hw' hwc hwν hM₀ hM₁ hP1 hv1
    have e0 : ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ
        = ∫ x, |v x| ^ p.toReal ∂B.σ := by
      refine integral_congr_ae ?_
      filter_upwards [B.traceL_ae_eq_of_contDiff hw hp hd u hv hvc huv] with x hx
      rw [hx]
    have e1 := SobolevEuclidean.integral_abs_rpow_eq_norm_fnL hp u huv
    -- the mixed term by Hölder
    have e2 : ∫ x in (Ω : Set 𝔼), |v x| ^ (p.toReal - 1) * ‖fderiv ℝ v x‖
        = ∫ x in (Ω : Set 𝔼), ‖fn u x‖ ^ (p.toReal - 1) * ‖gradFn u x‖ := by
      refine integral_congr_ae ?_
      filter_upwards [huv, SobolevEuclidean.norm_fderiv_ae_eq_norm_gradFn u hv1 huv] with x h1 h2
      rw [h1, h2, Real.norm_eq_abs]
    have h2 := MeasureTheory.integral_norm_rpow_sub_one_mul_norm_le hp (memLp u) (memLp_gradFn u)
    have h3 := SobolevEuclidean.toReal_eLpNorm_gradFn_le hp u
    have hfn : (eLpNorm (fn u) p (volume.restrict (Ω : Set 𝔼))).toReal
        = ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ := by
      rw [Lp.norm_def, fnL_apply]
    rw [hfn] at h2
    set a := ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ with ha
    have hg0 : 0 ≤ gradNorm u := gradNorm_nonneg u
    calc ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ
        = ∫ x, |v x| ^ p.toReal ∂B.σ := e0
      _ ≤ max (N * M₁) (p.toReal * M₀) * ((∫ x in (Ω : Set 𝔼), |v x| ^ p.toReal)
          + ∫ x in (Ω : Set 𝔼), |v x| ^ (p.toReal - 1) * ‖fderiv ℝ v x‖) := hnec
      _ ≤ max (N * M₁) (p.toReal * M₀)
          * (a ^ p.toReal + a ^ (p.toReal - 1) * (N * gradNorm u)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add (le_of_eq e1) ?_) hC₀
          rw [e2]
          exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
      _ ≤ max (N * M₁) (p.toReal * M₀) * (1 + N)
          * (a ^ p.toReal + a ^ (p.toReal - 1) * gradNorm u) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hC₀
          have h4 : 0 ≤ a ^ p.toReal := by positivity
          have h5 : 0 ≤ a ^ (p.toReal - 1) * gradNorm u := by positivity
          nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  refine hd.dense_smoothRestrictions.induction (P := fun u : SobolevEuclidean N 1 p Ω ↦
    ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ
      ≤ max (N * M₁) (p.toReal * M₀) * (1 + N)
        * (‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ p.toReal
          + ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ ^ (p.toReal - 1)
            * gradNorm u)) key ?_ u
  -- closedness: both sides are continuous in `u`
  have hL : Continuous fun u : SobolevEuclidean N 1 p Ω ↦
      ∫ x, |(B.traceL hw p hp u : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ := by
    have h : Continuous fun u : SobolevEuclidean N 1 p Ω ↦ ‖B.traceL hw p hp u‖ ^ p.toReal :=
      (continuous_norm.comp (B.traceL hw p hp).continuous).rpow_const fun _ ↦ Or.inr hP0.le
    refine h.congr fun u ↦ ?_
    rw [Lp.norm_rpow_eq_integral hp0 hp]
    simp_rw [Real.norm_eq_abs]
  have hfnc : Continuous fun u : SobolevEuclidean N 1 p Ω ↦
      ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume u‖ :=
    continuous_norm.comp (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).continuous
  refine isClosed_le hL (continuous_const.mul ((hfnc.rpow_const fun _ ↦ Or.inr hP0.le).add
    ((hfnc.rpow_const fun _ ↦ Or.inr (by linarith)).mul SobolevEuclidean.continuous_gradNorm)))

/-- **Compactness of the trace.** Suppose that the boundary data have a transversal field, that
$1 < p < \infty$, that the smooth-representable elements are dense in $W^{1,p}(\Omega)$, and
that the embedding $W^{1,p}(\Omega) \to L^p(\Omega)$ is compact. Then the trace
$T : W^{1,p}(\Omega) \to L^p(\sigma)$ is a compact operator. This is [han2009theoretical]
Theorem 7.3.10(c) for $p > 1$.

The compactness of the embedding is the Rellich–Kondrachov theorem,
`SobolevEuclidean.isCompactEmbedding_fnL` on bounded $C^1$ chart domains. For a sequence in the
unit ball, a subsequence converges in $L^p(\Omega)$, and Nečas's inequality
`BoundaryData.integral_abs_traceL_rpow_le` gives $\|T(u_n - u_m)\| \le (C (t^p + 2
t^{p-1}))^{1/p}$ with $t = \|u_n - u_m\|_{L^p(\Omega)} \to 0$, so the traces form a Cauchy
sequence. [han2009theoretical] states (c) for $1 \le p < \infty$, but the hypothesis $p > 1$ is
necessary: at $p = 1$ the bound $C (t + 2)$ does not tend to zero, and the trace
$W^{1,1}(\Omega) \to L^1(\partial\Omega)$ is onto (Gagliardo), so it is not compact. -/
theorem isCompactOperator_traceL (hw : B.HasTransversalField) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hd : SobolevEuclidean.HasSmoothDensity N p Ω)
    (hR : IsCompactEmbedding
      (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).toLinearMap) :
    IsCompactOperator (B.traceL hw p hp) := by
  obtain ⟨C, hC0, hC⟩ := B.integral_abs_traceL_rpow_le hw p hp hd
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hP1 : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1
  have hP0 : 0 < p.toReal := zero_lt_one.trans hP1
  have hP1' : 0 < p.toReal - 1 := by linarith
  -- the modulus of continuity (`obtain` rather than `set`: `set` abstracts in typed hypotheses)
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
      ∀ t, g t = (C * (t ^ p.toReal + 2 * t ^ (p.toReal - 1))) ^ (1 / p.toReal) :=
    ⟨_, fun _ ↦ rfl⟩
  have hgc : Continuous g := by
    refine Continuous.congr ?_ fun t ↦ (hg t).symm
    exact (continuous_const.mul ((continuous_id.rpow_const fun _ ↦ Or.inr hP0.le).add
      (continuous_const.mul (continuous_id.rpow_const fun _ ↦ Or.inr hP1'.le)))).rpow_const
      fun _ ↦ Or.inr (by positivity)
  have hg0 : g 0 = 0 := by
    rw [hg, Real.zero_rpow hP0.ne', Real.zero_rpow hP1'.ne', mul_zero, add_zero, mul_zero,
      one_div, Real.zero_rpow (inv_ne_zero hP0.ne')]
  have hgt : Tendsto g (𝓝 0) (𝓝 (g 0)) := hgc.tendsto 0
  rw [hg0] at hgt
  -- the key estimate on the unit ball
  have key : ∀ a b : SobolevEuclidean N 1 p Ω, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      dist (B.traceL hw p hp a) (B.traceL hw p hp b)
        ≤ g (dist (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume a)
          (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume b)) := by
    intro a b ha hb
    rw [dist_eq_norm, dist_eq_norm, ← (B.traceL hw p hp).map_sub,
      ← (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume).map_sub]
    have hab := hC (a - b)
    have ht0 : 0 ≤ ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (a - b)‖ :=
      norm_nonneg _
    have hgrad : gradNorm (a - b) ≤ 2 :=
      (gradNorm_le_norm _).trans ((norm_sub_le _ _).trans (by linarith))
    have hTP : ‖B.traceL hw p hp (a - b)‖ ^ p.toReal
        = ∫ x, |(B.traceL hw p hp (a - b) : 𝔼 → ℝ) x| ^ p.toReal ∂B.σ := by
      rw [Lp.norm_rpow_eq_integral hp0 hp]
      simp_rw [Real.norm_eq_abs]
    calc ‖B.traceL hw p hp (a - b)‖ = (‖B.traceL hw p hp (a - b)‖ ^ p.toReal) ^ (1 / p.toReal) := by
          rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hP0.ne', Real.rpow_one]
      _ ≤ (C * (‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (a - b)‖ ^ p.toReal
          + 2 * ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (a - b)‖
            ^ (p.toReal - 1))) ^ (1 / p.toReal) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [hTP]
          refine hab.trans (mul_le_mul_of_nonneg_left ?_ hC0)
          have := mul_le_mul_of_nonneg_left hgrad (Real.rpow_nonneg ht0 (p.toReal - 1))
          linarith
      _ = g ‖fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (a - b)‖ := (hg _).symm
  -- the image of a sequence of the unit ball has a convergent subsequence
  refine isCompactOperator_of_forall_exists_subseq_tendsto (T := (B.traceL hw p hp).toLinearMap)
    fun v hv ↦ ?_
  obtain ⟨φ, w, hφ, hw'⟩ := hR.exists_subseq_tendsto v ⟨1, hv⟩
  have hcauchy : CauchySeq fun n ↦ B.traceL hw p hp (v (φ n)) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have hb : Tendsto (fun mn : ℕ × ℕ ↦
        dist (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (v (φ mn.1)))
          (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (v (φ mn.2))))
        atTop (𝓝 0) :=
      cauchySeq_iff_tendsto_dist_atTop_0.1 hw'.cauchySeq
    have hgb : Tendsto (fun mn : ℕ × ℕ ↦
        g (dist (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (v (φ mn.1)))
          (fnL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis 1 p Ω volume (v (φ mn.2)))))
        atTop (𝓝 0) := hgt.comp hb
    exact squeeze_zero (fun _ ↦ dist_nonneg)
      (fun mn ↦ key (v (φ mn.1)) (v (φ mn.2)) (hv _) (hv _)) hgb
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨φ, z, hφ, hz⟩


end Compact

end BoundaryData
