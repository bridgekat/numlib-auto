/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Sobolev.Boundary.ContDiffDomain
import Numlib.Analysis.Sobolev.Zero
import Numlib.MeasureTheory.Integral.Bochner.Basic
import Numlib.MeasureTheory.Integral.IntervalIntegral

/-!
# The kernel of the trace on a bounded $C^1$ domain

Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set with boundary of class $C^1$, and let
$1 \le p < \infty$. This module proves that the kernel of the trace operator $\gamma :
W^{1,p}(\Omega) \to L^p(\partial\Omega)$ of `Numlib.Analysis.Sobolev.Boundary.ContDiffDomain` is
$W^{1,p}_0(\Omega)$: $$\gamma u = 0 \iff u \in W^{1,p}_0(\Omega).$$ This is [brezis2011functional],
Comments on Chapter 9, 7(ii), and Evans, *Partial Differential Equations*, §5.5, Theorem 2. It is
also the identification $H^1_0(\Omega) = \{v \in H^1(\Omega) : \gamma v = 0\}$ behind Definition
7.2.9 of [han2009theoretical] and the mixed boundary value problems of its §8.5 and §11.4; see also
Theorem 7.3.11 of [han2009theoretical]. The inclusion $W^{1,p}_0(\Omega) \subseteq \ker \gamma$
holds for every trace family (`BoundaryData.TraceFamily.traceL_eq_zero_of_mem_zero`); this module
proves the converse.

The module also proves the strip estimate of Evans (§5.5, Theorem 2, estimate (17)), with the
constant $1$. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open, and suppose that after a rigid motion
$T$, the set $\Omega$ is the region above the graph of a continuous function
$g : \mathbb{R}^d \to \mathbb{R}$ inside the ball $B(x_0, r)$. For $y \in \mathbb{R}^{d+1}$ write
$y = (y', y_{d+1})$ with $y' \in \mathbb{R}^d$, and let $$S_\rho(t) = \Omega \cap B(x_0, \rho) \cap
\{x : (Tx)_{d+1} < g((Tx)') + t\}$$ be the strip of height $t$ above the boundary inside
$B(x_0, \rho)$. Then for every $u \in W^{1,p}_0(\Omega)$, every $t > 0$ and every $\rho$ with
$\rho + t \le r$, $$\int_{S_\rho(t)} |u|^p \le t^p \int_{S_r(t)} |\nabla u|^p.$$ On a bounded $C^1$
domain, the kernel theorem extends the estimate to every $u$ with $\gamma u = 0$. The module ends
with three consequences for the boundary seminorm $v \mapsto \int_U |\gamma v| \, d\sigma$.

## Main results

* `IsContDiffDomain.mem_zero_of_traceL_eq_zero`: on a bounded $C^1$ domain, a function in
  $W^{1,p}(\Omega)$ with zero trace lies in $W^{1,p}_0(\Omega)$.
* `IsContDiffDomain.traceL_eq_zero_iff_mem_zero`: on a bounded $C^1$ domain, $\gamma u = 0$ if and
  only if $u \in W^{1,p}_0(\Omega)$.
* `SobolevEuclideanZero.integral_strip_rpow_le`: the strip estimate for $u \in W^{1,p}_0(\Omega)$ on
  an open set with a continuous graph chart.
* `IsContDiffDomain.integral_strip_rpow_le_of_traceL_eq_zero`: the strip estimate for
  $u \in W^{1,p}(\Omega)$ with $\gamma u = 0$ on a bounded $C^1$ domain.
* `IsContDiffDomain.eq_zero_of_gradNorm_eq_zero_of_traceL_eq_zero`: on a bounded $C^1$ domain, a
  function in $W^{1,p}(\Omega)$ with zero gradient and zero trace is zero.

## Proof outline

The proof of $\ker \gamma \subseteq W^{1,p}_0(\Omega)$ follows Brezis, through Proposition 9.18 of
[brezis2011functional], and not the cut-off argument of Evans. Let $u \in W^{1,p}(\Omega)$ with
$\gamma u = 0$, and let $\bar u$ be the extension of $u$ by zero. Green's formula against a
compactly supported $C^1$ function $\varphi$ on $\mathbb{R}^{d+1}$ gives $\int_\Omega \partial_i u
\, \varphi + \int_\Omega u \, \partial_i \varphi = \int_{\partial\Omega} (\gamma u) \varphi \nu_i \,
d\sigma = 0$. Hence $\bar u$ has the extension by zero of $\partial_i u$ as weak derivative on
$\mathbb{R}^{d+1}$, and $\bar u \in W^{1,p}(\mathbb{R}^{d+1})$. The implication (iii) $\Rightarrow$
(i) of Proposition 9.18 then gives $u \in W^{1,p}_0(\Omega)$. No strip estimate, partition of unity
or cut-off sequence is used.

The strip estimate is first proved for a test function $\varphi$ on $\Omega$. In the frame of the
chart, $\psi = \varphi \circ T^{-1}$ vanishes on the graph of $g$ inside $B(Tx_0, r)$. On each
vertical line, $\psi(x', g(x') + s) = \int_0^s \partial_{d+1} \psi(x', g(x') + \tau) \, d\tau$.
Hölder's inequality in $\tau$ on an interval of length at most $t$, followed by integration in $s$
over an interval of length at most $t$, gives the factor $t^p$. Fubini's theorem in the last
coordinate and the rigid motion give the estimate for $\varphi$. Both sides of the estimate are
continuous in $u \in W^{1,p}(\Omega)$, and the test functions are dense in $W^{1,p}_0(\Omega)$; this
gives the estimate on $W^{1,p}_0(\Omega)$.

## Implementation notes

* The trace is `IsContDiffDomain.traceL`, with values in $L^p$ of the surface measure
  `IsContDiffDomain.boundaryMeasure`. A function $u \in W^{1,p}(\Omega)$ is
  `u : SobolevEuclidean (d + 1) 1 p Ω`, its function is `SobolevMultiIndex.fn u`, and
  $W^{1,p}_0(\Omega)$ is the submodule `SobolevEuclideanZero (d + 1) 1 p Ω`.
* The pointwise gradient is `SobolevMultiIndex.gradFn`, and $|\nabla u(x)|$ is its Euclidean norm.
* The rigid motion $T$ is an affine isometric equivalence `T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼`.
* For $y \in \mathbb{R}^{d+1}$, the last coordinate $y_{d+1}$ is `y (Fin.last d)`, and the vector
  $y'$ of the first $d$ coordinates is `EuclideanSpace.init y`.
* The estimate for test functions is stated with lower Lebesgue integrals in $[0, \infty]$, so that
  it needs no integrability hypothesis. The estimate on $W^{1,p}_0(\Omega)$ is stated with Bochner
  integrals; its continuity in $u$ uses `MeasureTheory.Lp.monoMeasureL` composed with
  `SobolevMultiIndex.fnL`, and the restricted gradient `SobolevEuclidean.gradFnL` of
  `Numlib.Analysis.Sobolev.Operators`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace NNReal Topology
open SobolevMultiIndex

noncomputable section

section General

end General

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (d + 1))
local notation "𝔼'" => EuclideanSpace ℝ (Fin d)

/-! ### The kernel of the trace -/

namespace IsContDiffDomain

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set of class $C^1$, let
$1 \le p < \infty$, and let $u \in W^{1,p}(\Omega)$ have trace $\gamma u = 0$. Then for every
coordinate $i$, the extension by zero $\bar u$ of $u$ has the extension by zero
$\overline{\partial_i u}$ of $\partial_i u$ as weak partial derivative in the direction $e_i$ on
all of $\mathbb{R}^{d+1}$: both functions are locally integrable, and $$\int_{\mathbb{R}^{d+1}}
\bar u \, \partial_i \varphi \, dx = -\int_{\mathbb{R}^{d+1}} \overline{\partial_i u} \, \varphi
\, dx$$ for every test function $\varphi \in C_c^\infty(\mathbb{R}^{d+1})$.

The partial derivative $\partial_i u$ is
`SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)`. The weak derivative is
`HasWeakIteratedLineDerivOn` along the one-element tuple $(e_i)$ on the whole space `⊤`. The
coordinate index $i$ runs over `Fin (d + 1)`. The proof applies Green's formula
`IsContDiffDomain.green_contDiff`, whose boundary term vanishes because $\gamma u = 0$. -/
theorem hasWeakIteratedLineDerivOn_indicator_of_traceL_eq_zero (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : hΩ.traceL hb p hp u = 0)
    (i : Fin (d + 1)) :
    HasWeakIteratedLineDerivOn ![EuclideanSpace.single i (1 : ℝ)]
      ((Ω : Set 𝔼).indicator (fn u))
      ((Ω : Set 𝔼).indicator (weakDeriv u (MultiIndexLE.single i))) ⊤ volume where
  locallyIntegrableOn :=
    ((SobolevMultiIndexZero.memLp_indicator_fn u).locallyIntegrable Fact.out).locallyIntegrableOn _
  locallyIntegrableOn_weakDeriv :=
    ((SobolevMultiIndexZero.memLp_indicator_weakDeriv u _).locallyIntegrable
      Fact.out).locallyIntegrableOn _
  integral_smul_eq φ := by
    have hG := hΩ.green_contDiff hb p hp u (φ.contDiff.of_le (by simp)) φ.hasCompactSupport i
    have h0 : ∫ x, (hΩ.traceL hb p hp u : 𝔼 → ℝ) x * φ x * hΩ.outwardNormal hb x i
        ∂(hΩ.boundaryMeasure hb) = 0 := by
      rw [hu]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [Lp.coeFn_zero ℝ p (hΩ.boundaryMeasure hb)] with x hx
      rw [hx, Pi.zero_apply, zero_mul, zero_mul]
    rw [h0] at hG
    have hΩm := Ω.isOpen.measurableSet
    simp only [Opens.coe_top, Measure.restrict_univ, iteratedFDeriv_one_apply,
      Matrix.cons_val_zero, smul_eq_mul, pow_one]
    have e1 : (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) * (Ω : Set 𝔼).indicator (fn u) x)
        = (Ω : Set 𝔼).indicator fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1) * fn u x := by
      funext x
      rw [Set.indicator_mul_right]
    have e2 : (fun x ↦ φ x * (Ω : Set 𝔼).indicator (weakDeriv u (MultiIndexLE.single i)) x)
        = (Ω : Set 𝔼).indicator fun x ↦ φ x * weakDeriv u (MultiIndexLE.single i) x := by
      funext x
      rw [Set.indicator_mul_right]
    rw [e1, e2, integral_indicator hΩm, integral_indicator hΩm]
    have e3 : ∫ x in (Ω : Set 𝔼), fderiv ℝ φ x (EuclideanSpace.single i 1) * fn u x
        = ∫ x in (Ω : Set 𝔼), fn u x * fderiv ℝ φ x (EuclideanSpace.single i 1) :=
      integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    have e4 : ∫ x in (Ω : Set 𝔼), φ x * weakDeriv u (MultiIndexLE.single i) x
        = ∫ x in (Ω : Set 𝔼), weakDeriv u (MultiIndexLE.single i) x * φ x :=
      integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)
    rw [e3, e4]
    linarith

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set of class $C^1$, let
$1 \le p < \infty$, and let $u \in W^{1,p}(\Omega)$ have trace $\gamma u = 0$. Then the
extension of $u$ by zero lies in $W^{1,p}(\mathbb{R}^{d+1})$.

This says that $u$ satisfies condition (iii) of Proposition 9.18 of [brezis2011functional]. The
membership is `MemSobolevMultiIndex` for the standard basis of $\mathbb{R}^{d+1}$, on the whole
space `⊤`, with respect to Lebesgue measure. It follows from
`IsContDiffDomain.hasWeakIteratedLineDerivOn_indicator_of_traceL_eq_zero` and from the $L^p$
membership of the extensions by zero of $u$ and of its partial derivatives. -/
theorem indicator_memSobolevMultiIndex_of_traceL_eq_zero (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : hΩ.traceL hb p hp u = 0) :
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis
      ((Ω : Set 𝔼).indicator (fn u)) 1 p ⊤ volume := by
  refine SobolevEuclidean.memSobolevMultiIndex_one_of_forall (Ω := ⊤) ?_
    (G := fun i ↦ (Ω : Set 𝔼).indicator (weakDeriv u (MultiIndexLE.single i))) (fun i ↦ ?_)
    fun i ↦ hΩ.hasWeakIteratedLineDerivOn_indicator_of_traceL_eq_zero hb p hp hu i
  · simpa only [Opens.coe_top, Measure.restrict_univ] using
      SobolevMultiIndexZero.memLp_indicator_fn u
  · simpa only [Opens.coe_top, Measure.restrict_univ] using
      SobolevMultiIndexZero.memLp_indicator_weakDeriv u (MultiIndexLE.single i)

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set of class $C^1$ and let
$1 \le p < \infty$. If $u \in W^{1,p}(\Omega)$ has trace $\gamma u = 0$, then
$u \in W^{1,p}_0(\Omega)$.

This is the inclusion $\ker \gamma \subseteq W^{1,p}_0(\Omega)$ of [brezis2011functional],
Comments on Chapter 9, 7(ii), and of Evans, *Partial Differential Equations*, §5.5, Theorem 2.
The extension of $u$ by zero lies in $W^{1,p}(\mathbb{R}^{d+1})$
(`IsContDiffDomain.indicator_memSobolevMultiIndex_of_traceL_eq_zero`). The implication (iii)
$\Rightarrow$ (i) of Proposition 9.18 of [brezis2011functional], which is
`SobolevEuclideanZero.mem_of_indicator_memSobolev` applied on the $C^1$ chart domain
`IsContDiffDomain.isContDiffChartDomain`, then gives an element of $W^{1,p}_0(\Omega)$ with the
same function as $u$. By `SobolevMultiIndex.ext_of_fn_ae_eq` this element is $u$. -/
theorem mem_zero_of_traceL_eq_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : hΩ.traceL hb p hp u = 0) :
    u ∈ SobolevEuclideanZero (d + 1) 1 p Ω := by
  obtain ⟨v, hv, hvu⟩ := SobolevEuclideanZero.mem_of_indicator_memSobolev hp
    hΩ.isContDiffChartDomain (hΩ.indicator_memSobolevMultiIndex_of_traceL_eq_zero hb p hp hu)
  rwa [SobolevMultiIndex.ext_of_fn_ae_eq hvu] at hv

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set of class $C^1$ and let
$1 \le p < \infty$. For $u \in W^{1,p}(\Omega)$, $$\gamma u = 0 \iff u \in W^{1,p}_0(\Omega).$$
That is, the kernel of the trace operator is $W^{1,p}_0(\Omega)$.

This is [brezis2011functional], Comments on Chapter 9, 7(ii). For $p = 2$ it is the
identification $H^1_0(\Omega) = \{v \in H^1(\Omega) : \gamma v = 0\}$ that [han2009theoretical]
uses. The two directions are `IsContDiffDomain.mem_zero_of_traceL_eq_zero` and
`IsContDiffDomain.traceL_eq_zero_of_mem_zero`. -/
theorem traceL_eq_zero_iff_mem_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (u : SobolevEuclidean (d + 1) 1 p Ω) :
    hΩ.traceL hb p hp u = 0 ↔ u ∈ SobolevEuclideanZero (d + 1) 1 p Ω :=
  ⟨hΩ.mem_zero_of_traceL_eq_zero hb p hp, hΩ.traceL_eq_zero_of_mem_zero hb p hp⟩

end IsContDiffDomain

/-! ### The strip estimate in the frame of a graph -/

namespace EuclideanSpace

/-- Let $\psi : \mathbb{R}^{d+1} \to \mathbb{R}$ be of class $C^1$, let
$g : \mathbb{R}^d \to \mathbb{R}$ be continuous, and let $c \in \mathbb{R}^{d+1}$. Let $t > 0$
and $\rho + t \le r$, and suppose that $\psi(y) = 0$ for every $y \in B(c, r)$ with
$y_{d+1} = g(y')$. Let $G_t = \{y : g(y') < y_{d+1} < g(y') + t\}$ be the strip of height $t$
above the graph of $g$. Then for every real $P \ge 1$, $$\int_{B(c, \rho) \cap G_t} |\psi|^P \le
t^P \int_{B(c, r) \cap G_t} |\partial_{d+1} \psi|^P.$$

The integrals are lower Lebesgue integrals in $[0, \infty]$. The derivative
$\partial_{d+1} \psi(y)$ is the derivative of $\psi$ at $y$ in the direction of the last basis
vector. The last coordinate $y_{d+1}$ is `y (Fin.last d)`, the vector $y'$ is
`EuclideanSpace.init y`, and the strip $G_t$ is `EuclideanSpace.graphStrip g t`. The proof uses
Fubini's theorem in the last coordinate (`EuclideanSpace.lintegral_lastInit`). If the vertical
line through $x'$ meets the small strip, then its foot $(x', g(x'))$ lies in $B(c, r)$, so
$\psi(x', g(x')) = 0$. The segments from the foot to the points of the small strip lie in the
large strip, and the one-variable estimate `lintegral_enorm_rpow_le_of_hasDerivAt` applies on
each line. -/
theorem lintegral_graphStrip_le {ψ : 𝔼 → ℝ} (hψ : ContDiff ℝ 1 ψ) {g : 𝔼' → ℝ}
    (hg : Continuous g) {c : 𝔼} {r ρ t : ℝ} (ht : 0 < t) (hρt : ρ + t ≤ r)
    (h0 : ∀ y ∈ Metric.ball c r, y (Fin.last d) = g (init y) → ψ y = 0) {P : ℝ} (hP : 1 ≤ P) :
    ∫⁻ y in Metric.ball c ρ ∩ graphStrip g t, ‖ψ y‖ₑ ^ P
      ≤ ENNReal.ofReal t ^ P * ∫⁻ y in Metric.ball c r ∩ graphStrip g t,
          ‖fderiv ℝ ψ y (single (Fin.last d) 1)‖ₑ ^ P := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hSρ : MeasurableSet (Metric.ball c ρ ∩ graphStrip g t) :=
    (Metric.isOpen_ball.inter (isOpen_graphStrip hg t)).measurableSet
  have hSr : MeasurableSet (Metric.ball c r ∩ graphStrip g t) :=
    (Metric.isOpen_ball.inter (isOpen_graphStrip hg t)).measurableSet
  have hF : Measurable fun y : 𝔼 ↦ ‖ψ y‖ₑ ^ P := hψ.continuous.measurable.enorm.pow_const _
  have hG : Measurable fun y : 𝔼 ↦ ‖fderiv ℝ ψ y (single (Fin.last d) 1)‖ₑ ^ P :=
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable.enorm.pow_const _
  rw [← lintegral_indicator hSρ, ← lintegral_indicator hSr,
    lintegral_lastInit _ (hF.indicator hSρ).aemeasurable,
    lintegral_lastInit _ (hG.indicator hSr).aemeasurable,
    ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hP0.le ENNReal.ofReal_ne_top)]
  refine lintegral_mono fun x' ↦ ?_
  have hline : Continuous fun s : ℝ ↦ snocLast x' s :=
    continuous_iff_continuousAt.2 fun s ↦ (hasDerivAt_snocLast x' s).continuousAt
  have hIm : MeasurableSet ((fun s : ℝ ↦ snocLast x' s) ⁻¹' (Metric.ball c ρ ∩ graphStrip g t)) :=
    hSρ.preimage hline.measurable
  have hJm : MeasurableSet ((fun s : ℝ ↦ snocLast x' s) ⁻¹' (Metric.ball c r ∩ graphStrip g t)) :=
    hSr.preimage hline.measurable
  have e1 : (fun s : ℝ ↦ (Metric.ball c ρ ∩ graphStrip g t).indicator
      (fun y ↦ ‖ψ y‖ₑ ^ P) (snocLast x' s))
      = ((fun s : ℝ ↦ snocLast x' s) ⁻¹' (Metric.ball c ρ ∩ graphStrip g t)).indicator
          fun s ↦ ‖ψ (snocLast x' s)‖ₑ ^ P := by
    funext s
    exact (Set.indicator_comp_right (fun s : ℝ ↦ snocLast x' s)).symm
  have e2 : (fun s : ℝ ↦ (Metric.ball c r ∩ graphStrip g t).indicator
      (fun y ↦ ‖fderiv ℝ ψ y (single (Fin.last d) 1)‖ₑ ^ P) (snocLast x' s))
      = ((fun s : ℝ ↦ snocLast x' s) ⁻¹' (Metric.ball c r ∩ graphStrip g t)).indicator
          fun s ↦ ‖fderiv ℝ ψ (snocLast x' s) (single (Fin.last d) 1)‖ₑ ^ P := by
    funext s
    exact (Set.indicator_comp_right (fun s : ℝ ↦ snocLast x' s)).symm
  simp only
  rw [e1, e2, lintegral_indicator hIm, lintegral_indicator hJm]
  -- the vertical line may miss the small strip
  by_cases hne : ((fun s : ℝ ↦ snocLast x' s) ⁻¹' (Metric.ball c ρ ∩ graphStrip g t)).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  obtain ⟨s₀, hs₀⟩ := hne
  -- the foot `(x', g x')` of the line lies in `B(c, r)`
  have hfoot : snocLast x' (g x') ∈ Metric.ball c r := by
    simp only [Set.mem_preimage, Set.mem_inter_iff, snocLast_mem_graphStrip] at hs₀
    have h1 : dist (snocLast x' (g x')) (snocLast x' s₀) < t := by
      rw [dist_eq_norm, norm_snocLast_sub_snocLast, abs_sub_comm,
        abs_of_pos (by linarith [hs₀.2.1])]
      linarith [hs₀.2.2]
    have h2 := hs₀.1
    rw [Metric.mem_ball] at h2 ⊢
    linarith [dist_triangle (snocLast x' (g x')) (snocLast x' s₀) c]
  refine lintegral_enorm_rpow_le_of_hasDerivAt (f := fun s ↦ ψ (snocLast x' s))
    (f' := fun s ↦ fderiv ℝ ψ (snocLast x' s) (single (Fin.last d) 1)) (a := g x') (fun s ↦ ?_) ?_
    ht ?_ ?_ ?_ ?_ hP
  · exact (hψ.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_snocLast x' s)
  · exact ((hψ.continuous_fderiv one_ne_zero).comp hline).clm_apply continuous_const
  · exact h0 _ hfoot (by simp)
  · intro s hs
    simp only [Set.mem_preimage, Set.mem_inter_iff, snocLast_mem_graphStrip] at hs
    exact hs.2
  · intro s hs
    simp only [Set.mem_preimage, Set.mem_inter_iff, snocLast_mem_graphStrip] at hs
    exact hs.2
  · intro s hs τ hτ
    simp only [Set.mem_preimage, Set.mem_inter_iff, snocLast_mem_graphStrip] at hs ⊢
    refine ⟨?_, hτ.1, by linarith [hτ.2, hs.2.2]⟩
    have h1 : dist (snocLast x' τ) (snocLast x' s) < t := by
      rw [dist_eq_norm, norm_snocLast_sub_snocLast, abs_sub_comm,
        abs_of_nonneg (by linarith [hτ.2])]
      linarith [hτ.1, hs.2.2]
    have h2 := hs.1
    rw [Metric.mem_ball] at h2 ⊢
    linarith [dist_triangle (snocLast x' τ) (snocLast x' s) c]

end EuclideanSpace

/-! ### The strip estimate on $W^{1,p}_0(\Omega)$ -/

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open, let $T$ be a rigid motion of
$\mathbb{R}^{d+1}$, let $g : \mathbb{R}^d \to \mathbb{R}$ be continuous, and let
$x_0 \in \mathbb{R}^{d+1}$ and $r \in \mathbb{R}$ satisfy $$\Omega \cap B(x_0, r) = B(x_0, r)
\cap T^{-1}\{y : g(y') < y_{d+1}\}.$$ Let $\varphi \in C_c^\infty(\Omega)$, $t > 0$,
$\rho + t \le r$ and $P \ge 1$. With $S_\rho(t) = \Omega \cap B(x_0, \rho) \cap \{x : (Tx)_{d+1}
< g((Tx)') + t\}$, $$\int_{S_\rho(t)} |\varphi|^P \le t^P \int_{S_r(t)} |\partial_e
\varphi|^P,$$ where $e = L^{-1} e_{d+1}$ is the upward direction of the chart, $L$ is the linear
part of $T$, and $\partial_e$ is the derivative in the direction $e$.

The integrals are lower Lebesgue integrals in $[0, \infty]$. The set $\{y : g(y') < y_{d+1}\}$
is `EuclideanSpace.epigraph g`, and $L$ is `T.linearIsometryEquiv`. The function
$\varphi \circ T^{-1}$ vanishes on the graph of $g$ inside $B(Tx_0, r)$
(`IsBoundaryGraphAt.frontier_inter_ball`). The rigid motion maps the small strip into
$B(Tx_0, \rho) \cap G_t$ and maps $B(Tx_0, r) \cap G_t$ into the large strip, and it preserves
Lebesgue measure; then `EuclideanSpace.lintegral_graphStrip_le` applies. -/
theorem TestFunction.lintegral_strip_le {Ω : Opens 𝔼} (φ : 𝓓(Ω, ℝ)) (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼)
    {g : 𝔼' → ℝ} (hg : Continuous g) {x₀ : 𝔼} {r ρ t : ℝ}
    (h : (Ω : Set 𝔼) ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    (ht : 0 < t) (hρt : ρ + t ≤ r) {P : ℝ} (hP : 1 ≤ P) :
    ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, ‖φ x‖ₑ ^ P
      ≤ ENNReal.ofReal t ^ P
        * ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
            ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖fderiv ℝ φ x (T.linearIsometryEquiv.symm (EuclideanSpace.single (Fin.last d) 1))‖ₑ
            ^ P := by
  have hψ : ContDiff ℝ 1 (φ ∘ T.symm) :=
    (φ.contDiff.of_le (by simp)).comp T.symm.toAffineIsometry.toContinuousAffineMap.contDiff
  have hTe := T.toHomeomorph.measurableEmbedding
  have hmp := T.measurePreserving
  -- the derivative of `φ ∘ T⁻¹` along `e_N`
  have hderiv : ∀ x, fderiv ℝ (φ ∘ T.symm) (T x) (EuclideanSpace.single (Fin.last d) 1)
      = fderiv ℝ φ x (T.linearIsometryEquiv.symm (EuclideanSpace.single (Fin.last d) 1)) := by
    intro x
    have h1 : HasFDerivAt φ (fderiv ℝ φ x) (T.symm (T x)) := by
      rw [T.symm_apply_apply]
      exact ((φ.contDiff.differentiable (by simp)) x).hasFDerivAt
    have h2 := h1.comp (T x) (T.symm.hasFDerivAt (T x))
    rw [h2.fderiv]
    rfl
  -- the two strips
  have hsub1 : (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
      ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}
      ⊆ T ⁻¹' (Metric.ball (T x₀) ρ ∩ EuclideanSpace.graphStrip g t) := by
    rintro x ⟨⟨hxΩ, hxρ⟩, hxt⟩
    have hxr : x ∈ Metric.ball x₀ r := Metric.ball_subset_ball (by linarith) hxρ
    have hx : x ∈ Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g := h ▸ ⟨hxΩ, hxr⟩
    refine ⟨?_, hx.2, hxt⟩
    rw [Metric.mem_ball, T.dist_map]
    exact hxρ
  have hsub2 : T ⁻¹' (Metric.ball (T x₀) r ∩ EuclideanSpace.graphStrip g t)
      ⊆ (Ω : Set 𝔼) ∩ Metric.ball x₀ r
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t} := by
    rintro x ⟨hxr, hx1, hx2⟩
    have hxr' : x ∈ Metric.ball x₀ r := by
      rw [Metric.mem_ball, T.dist_map] at hxr
      exact hxr
    have hx : x ∈ (Ω : Set 𝔼) ∩ Metric.ball x₀ r := h.symm ▸ ⟨hxr', hx1⟩
    exact ⟨hx, hx2⟩
  -- `φ ∘ T⁻¹` vanishes on the graph inside the ball
  have h0 : ∀ y ∈ Metric.ball (T x₀) r, y (Fin.last d) = g (EuclideanSpace.init y) →
      (φ ∘ T.symm) y = 0 := by
    intro y hy hyg
    have hfr : T.symm y ∈ frontier (Ω : Set 𝔼) := by
      have h2 := IsBoundaryGraphAt.frontier_inter_ball hg h
      have h3 : T.symm y ∈ Metric.ball x₀ r
          ∩ T ⁻¹' {y | y (Fin.last d) = g (EuclideanSpace.init y)} := by
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, ← T.dist_map, T.apply_symm_apply]
          exact hy
        · rw [Set.mem_preimage, T.apply_symm_apply]
          exact hyg
      rw [← h2] at h3
      exact h3.1
    exact φ.eq_zero_of_notMem fun hmem ↦ hfr.2 (by rwa [Ω.isOpen.interior_eq])
  have e1 : (fun x ↦ ‖φ x‖ₑ ^ P) = fun x ↦ ‖(φ ∘ T.symm) (T x)‖ₑ ^ P := by
    funext x
    simp
  calc ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, ‖φ x‖ₑ ^ P
      ≤ ∫⁻ x in T ⁻¹' (Metric.ball (T x₀) ρ ∩ EuclideanSpace.graphStrip g t),
          ‖(φ ∘ T.symm) (T x)‖ₑ ^ P := by
        rw [e1]
        exact lintegral_mono_set hsub1
    _ = ∫⁻ y in Metric.ball (T x₀) ρ ∩ EuclideanSpace.graphStrip g t, ‖(φ ∘ T.symm) y‖ₑ ^ P :=
        hmp.setLIntegral_comp_preimage_emb hTe (fun y ↦ ‖(φ ∘ T.symm) y‖ₑ ^ P) _
    _ ≤ ENNReal.ofReal t ^ P * ∫⁻ y in Metric.ball (T x₀) r ∩ EuclideanSpace.graphStrip g t,
          ‖fderiv ℝ (φ ∘ T.symm) y (EuclideanSpace.single (Fin.last d) 1)‖ₑ ^ P :=
        EuclideanSpace.lintegral_graphStrip_le hψ hg ht hρt h0 hP
    _ = ENNReal.ofReal t ^ P
        * ∫⁻ x in T ⁻¹' (Metric.ball (T x₀) r ∩ EuclideanSpace.graphStrip g t),
          ‖fderiv ℝ (φ ∘ T.symm) (T x) (EuclideanSpace.single (Fin.last d) 1)‖ₑ ^ P := by
        rw [hmp.setLIntegral_comp_preimage_emb hTe
          (fun y ↦ ‖fderiv ℝ (φ ∘ T.symm) y (EuclideanSpace.single (Fin.last d) 1)‖ₑ ^ P)]
    _ ≤ ENNReal.ofReal t ^ P
        * ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
            ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖fderiv ℝ φ x (T.linearIsometryEquiv.symm (EuclideanSpace.single (Fin.last d) 1))‖ₑ
            ^ P := by
        refine mul_le_mul' le_rfl ?_
        simp_rw [hderiv]
        exact lintegral_mono_set hsub2

/-- The **strip estimate** on $W^{1,p}_0(\Omega)$. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be open,
let $1 \le p < \infty$, and let $u \in W^{1,p}_0(\Omega)$. Let $T$ be a rigid motion of
$\mathbb{R}^{d+1}$, let $g : \mathbb{R}^d \to \mathbb{R}$ be continuous, and let
$x_0 \in \mathbb{R}^{d+1}$ and $r \in \mathbb{R}$ satisfy $\Omega \cap B(x_0, r) = B(x_0, r)
\cap T^{-1}\{y : g(y') < y_{d+1}\}$. Let $t > 0$ and $\rho + t \le r$. With $S_\rho(t) = \Omega
\cap B(x_0, \rho) \cap \{x : (Tx)_{d+1} < g((Tx)') + t\}$, $$\int_{S_\rho(t)} |u|^p \le t^p
\int_{S_r(t)} |\nabla u|^p.$$ This is estimate (17) in the proof of Evans, *Partial Differential
Equations*, §5.5, Theorem 2, with the constant $1$.

The integrals are Bochner integrals of `SobolevMultiIndex.fn u` and of the Euclidean norm of the
pointwise gradient `SobolevMultiIndex.gradFn u`. For a test function,
`TestFunction.lintegral_strip_le` applies, together with
$|\partial_e \varphi| \le |\nabla \varphi|$. Both sides are continuous in $u$ (through
`MeasureTheory.Lp.monoMeasureL` composed with `SobolevMultiIndex.fnL`, and through
`SobolevEuclidean.gradFnL`), and the test functions are dense in $W^{1,p}_0(\Omega)$
(`SobolevMultiIndexZero.exists_seq_testFunction_tendsto`). -/
theorem SobolevEuclideanZero.integral_strip_rpow_le {Ω : Opens 𝔼} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {u : SobolevEuclidean (d + 1) 1 p Ω} (hu : u ∈ SobolevEuclideanZero (d + 1) 1 p Ω)
    (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) {g : 𝔼' → ℝ} (hg : Continuous g) {x₀ : 𝔼} {r ρ t : ℝ}
    (h : (Ω : Set 𝔼) ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    (ht : 0 < t) (hρt : ρ + t ≤ r) :
    ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, |fn u x| ^ p.toReal
      ≤ t ^ p.toReal * ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
          ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖gradFn u x‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hP1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_ne_top hp
  have hP0 : 0 < p.toReal := zero_lt_one.trans_le hP1
  have hSρ : (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
      ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t} ⊆ Ω :=
    fun x hx ↦ hx.1.1
  have hSr : (Ω : Set 𝔼) ∩ Metric.ball x₀ r
      ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t} ⊆ Ω :=
    fun x hx ↦ hx.1.1
  -- the two sides as continuous functions of `u`
  obtain ⟨L, hL⟩ : ∃ L : SobolevEuclidean (d + 1) 1 p Ω →L[ℝ] Lp ℝ p (volume.restrict
      ((Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t})),
      L = Lp.monoMeasureL (Measure.restrict_mono hSρ le_rfl) ∘L
        fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume := ⟨_, rfl⟩
  have hLeq : ∀ v : SobolevEuclidean (d + 1) 1 p Ω, ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
      ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, |fn v x| ^ p.toReal
      = ‖L v‖ ^ p.toReal := by
    intro v
    rw [Lp.norm_rpow_eq_integral hp0 hp, hL]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_monoMeasureL (Measure.restrict_mono hSρ le_rfl)
      (fnL ℝ (EuclideanSpace.basisFun (Fin (d + 1)) ℝ).toBasis 1 p Ω volume v)] with x hx
    rw [ContinuousLinearMap.comp_apply, hx, fnL_apply, Real.norm_eq_abs]
  have hΓeq := fun v ↦ SobolevEuclidean.integral_norm_gradFn_rpow_eq hp hSr v
  simp_rw [hLeq, hΓeq]
  -- the estimate on the test functions
  obtain ⟨w, φ, hφ, hw⟩ := SobolevMultiIndexZero.exists_seq_testFunction_tendsto hu
  have key : ∀ n, ‖L (w n)‖ ^ p.toReal
      ≤ t ^ p.toReal * ‖SobolevEuclidean.gradFnL p Ω hSr (w n)‖ ^ p.toReal := by
    intro n
    rw [← hLeq, ← hΓeq]
    have h1 := TestFunction.lintegral_strip_le (φ n) T hg h ht hρt hP1
    have hφ1 : ContDiff ℝ 1 (φ n) := (φ n).contDiff.of_le (by simp)
    have hmS : AEStronglyMeasurable (fn (w n)) (volume.restrict ((Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t})) :=
      (memLp (w n)).aestronglyMeasurable.mono_measure (Measure.restrict_mono hSρ le_rfl)
    have hmG : AEStronglyMeasurable (gradFn (w n)) (volume.restrict ((Ω : Set 𝔼) ∩ Metric.ball x₀ r
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t})) :=
      (aestronglyMeasurable_gradFn (w n)).mono_measure (Measure.restrict_mono hSr le_rfl)
    have hG : MemLp (gradFn (w n)) p (volume.restrict ((Ω : Set 𝔼) ∩ Metric.ball x₀ r
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t})) :=
      (memLp_gradFn (w n)).mono_measure (Measure.restrict_mono hSr le_rfl)
    -- the function of the test function, and the vertical derivative against the gradient
    have e1 : ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, ‖(φ n) x‖ₑ ^ p.toReal
        = ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, ‖fn (w n) x‖ₑ ^ p.toReal := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hSρ (hφ n)] with x hx
      rw [hx]
    have e2 : ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖fderiv ℝ (φ n) x (T.linearIsometryEquiv.symm
            (EuclideanSpace.single (Fin.last d) 1))‖ₑ ^ p.toReal
        ≤ ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖gradFn (w n) x‖ₑ ^ p.toReal := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hSr
        (SobolevEuclidean.norm_fderiv_ae_eq_norm_gradFn (w n) hφ1 (hφ n))] with x hx
      refine ENNReal.rpow_le_rpow ?_ hP0.le
      rw [← ofReal_norm, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [LinearIsometryEquiv.norm_map, PiLp.norm_single, norm_one, mul_one]
      exact hx.le
    rw [e1] at h1
    have h2 := h1.trans (mul_le_mul' le_rfl e2)
    have e3 : ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, |fn (w n) x| ^ p.toReal
        = (∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖fn (w n) x‖ₑ ^ p.toReal).toReal := by
      rw [← MeasureTheory.integral_norm_rpow_eq_toReal_lintegral hmS hP0.le]
      simp only [Real.norm_eq_abs]
    rw [e3, MeasureTheory.integral_norm_rpow_eq_toReal_lintegral hmG hP0.le]
    calc (∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
          ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
            ‖fn (w n) x‖ₑ ^ p.toReal).toReal
        ≤ (ENNReal.ofReal t ^ p.toReal * ∫⁻ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
          ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
            ‖gradFn (w n) x‖ₑ ^ p.toReal).toReal := by
          refine ENNReal.toReal_mono (ENNReal.mul_ne_top
            (ENNReal.rpow_ne_top_of_nonneg hP0.le ENNReal.ofReal_ne_top)
            (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hG).ne) h2
      _ = _ := by
          rw [ENNReal.toReal_mul, ENNReal.ofReal_rpow_of_nonneg ht.le hP0.le,
            ENNReal.toReal_ofReal (by positivity)]
  -- pass to the limit
  refine le_of_tendsto_of_tendsto' (b := atTop) ?_ ?_ key
  · exact (((continuous_norm.comp L.continuous).rpow_const fun _ ↦ Or.inr hP0.le).tendsto u).comp
      hw
  · exact ((continuous_const.mul ((continuous_norm.comp
      (SobolevEuclidean.gradFnL p Ω hSr).continuous).rpow_const fun _ ↦ Or.inr hP0.le)).tendsto
        u).comp hw

/-- The strip estimate for a function with zero trace. Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a
bounded open set of class $C^1$, let $1 \le p < \infty$, and let $u \in W^{1,p}(\Omega)$ have
trace $\gamma u = 0$. Let $T$ be a rigid motion of $\mathbb{R}^{d+1}$, let
$g : \mathbb{R}^d \to \mathbb{R}$ be continuous, and let $x_0 \in \mathbb{R}^{d+1}$ and
$r \in \mathbb{R}$ satisfy $\Omega \cap B(x_0, r) = B(x_0, r) \cap T^{-1}\{y : g(y') <
y_{d+1}\}$. Let $t > 0$ and $\rho + t \le r$. With $S_\rho(t) = \Omega \cap B(x_0, \rho) \cap
\{x : (Tx)_{d+1} < g((Tx)') + t\}$, $$\int_{S_\rho(t)} |u|^p \le t^p \int_{S_r(t)} |\nabla
u|^p.$$ With $\rho = r/2$, this is the form of Evans, *Partial Differential Equations*, §5.5,
Theorem 2, estimate (17).

The function $u$ lies in $W^{1,p}_0(\Omega)$ by `IsContDiffDomain.mem_zero_of_traceL_eq_zero`,
so the estimate is `SobolevEuclideanZero.integral_strip_rpow_le`. -/
theorem IsContDiffDomain.integral_strip_rpow_le_of_traceL_eq_zero
    {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
    (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) {u : SobolevEuclidean (d + 1) 1 p Ω}
    (hu : hΩ.traceL hb p hp u = 0) (T : 𝔼 ≃ᵃⁱ[ℝ] 𝔼) {g : 𝔼' → ℝ} (hg : Continuous g) {x₀ : 𝔼}
    {r ρ t : ℝ}
    (h : (Ω : Set 𝔼) ∩ Metric.ball x₀ r = Metric.ball x₀ r ∩ T ⁻¹' EuclideanSpace.epigraph g)
    (ht : 0 < t) (hρt : ρ + t ≤ r) :
    ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ ρ
        ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t}, |fn u x| ^ p.toReal
      ≤ t ^ p.toReal * ∫ x in (Ω : Set 𝔼) ∩ Metric.ball x₀ r
          ∩ T ⁻¹' {y | y (Fin.last d) < g (EuclideanSpace.init y) + t},
          ‖gradFn u x‖ ^ p.toReal :=
  SobolevEuclideanZero.integral_strip_rpow_le hp (hΩ.mem_zero_of_traceL_eq_zero hb p hp hu) T hg
    h ht hρt

/-! ### Consequences for the boundary seminorm $v \mapsto \int_U |\gamma v| \, d\sigma$ -/

namespace IsContDiffDomain

variable {Ω : Opens (EuclideanSpace ℝ (Fin (d + 1)))}
  (hΩ : IsContDiffDomain 1 (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (d + 1)))))
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set of class $C^1$ with surface
measure $\sigma$, let $1 \le p < \infty$, and let $U \subseteq \mathbb{R}^{d+1}$ satisfy
$\sigma(U) > 0$. Let $v \in W^{1,p}(\Omega)$ be equal almost everywhere on $\Omega$ to a
constant $c \in \mathbb{R}$. If $\int_U |\gamma v| \, d\sigma = 0$, then $v = 0$.

The trace of the constant function is the constant
(`IsContDiffDomain.traceL_ae_eq_of_continuousOn`), so $\int_U |\gamma v| \, d\sigma = |c| \,
\sigma(U)$, and this forces $c = 0$. -/
theorem eq_zero_of_traceL_integral_abs_eq_zero
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))} (hU : 0 < hΩ.boundaryMeasure hb U)
    {v : SobolevEuclidean (d + 1) 1 p Ω} {c : ℝ}
    (hvc : fn v =ᵐ[volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (d + 1))))] fun _ ↦ c)
    (h0 : ∫ x in U, |(hΩ.traceL hb p hp v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x|
      ∂(hΩ.boundaryMeasure hb) = 0) : v = 0 := by
  have htr := hΩ.traceL_ae_eq_of_continuousOn hb p hp v hvc continuousOn_const
  have hint : ∫ x in U, |(hΩ.traceL hb p hp v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x|
      ∂(hΩ.boundaryMeasure hb) = (hΩ.boundaryMeasure hb).real U * |c| := by
    rw [integral_congr_ae ((ae_restrict_of_ae htr).mono fun x hx ↦ by rw [hx]), setIntegral_const,
      smul_eq_mul]
  have hpos : 0 < (hΩ.boundaryMeasure hb).real U := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hU.ne' (measure_ne_top _ _)
  rw [hint] at h0
  have hc0 : c = 0 := abs_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hpos.ne')
  refine SobolevMultiIndex.ext_of_fn_ae_eq (hvc.trans ?_)
  rw [hc0]
  exact SobolevMultiIndex.fn_zero.symm

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set of class $C^1$ with surface
measure $\sigma$, let $1 \le p < \infty$, and let $v \in W^{1,p}(\Omega)$. If
$\int_{\partial\Omega} |\gamma v| \, d\sigma = 0$, then $\gamma v = 0$ almost everywhere for
$\sigma$.

The integral is over the whole space, against the measure `IsContDiffDomain.boundaryMeasure`,
which is carried by $\partial\Omega$. -/
theorem traceL_ae_eq_zero_of_integral_abs_eq_zero {v : SobolevEuclidean (d + 1) 1 p Ω}
    (h0 : ∫ x, |(hΩ.traceL hb p hp v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x|
      ∂(hΩ.boundaryMeasure hb) = 0) :
    (hΩ.traceL hb p hp v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[hΩ.boundaryMeasure hb] 0 := by
  have hi : Integrable (fun x ↦ |(hΩ.traceL hb p hp v :
      EuclideanSpace ℝ (Fin (d + 1)) → ℝ) x|) (hΩ.boundaryMeasure hb) :=
    ((Lp.memLp _).integrable Fact.out).abs
  have := (integral_eq_zero_iff_of_nonneg (fun x ↦ abs_nonneg _) hi).1 h0
  filter_upwards [this] with x hx
  rw [Pi.zero_apply] at hx ⊢
  exact abs_eq_zero.1 hx

/-- Let $\Omega \subseteq \mathbb{R}^{d+1}$ be a bounded open set of class $C^1$, let
$1 \le p < \infty$, and let $v \in W^{1,p}(\Omega)$. If $\|\nabla v\|_{L^p(\Omega)} = 0$ and
$\gamma v = 0$, then $v = 0$. No connectedness of $\Omega$ is assumed.

This is hypothesis (H2)′ of the Deny–Lions theorem for the boundary seminorm in Example 7.3.15
of [han2009theoretical]. The gradient norm is `SobolevMultiIndex.gradNorm`. Since
$\gamma v = 0$, the function $v$ lies in $W^{1,p}_0(\Omega)$ by
`IsContDiffDomain.mem_zero_of_traceL_eq_zero`, and there Poincaré's inequality
`SobolevEuclideanZero.norm_le_gradNorm` bounds the norm of $v$ by its gradient norm. -/
theorem eq_zero_of_gradNorm_eq_zero_of_traceL_eq_zero {v : SobolevEuclidean (d + 1) 1 p Ω}
    (hv : gradNorm v = 0) (hγ : hΩ.traceL hb p hp v = 0) : v = 0 := by
  have hmem := hΩ.mem_zero_of_traceL_eq_zero hb p hp hγ
  obtain ⟨R, hR0, hR⟩ := hb.subset_ball_lt 0 0
  have hP := SobolevEuclideanZero.norm_le_gradNorm hp hR0.le hR ⟨v, hmem⟩
  change ‖v‖ ≤ _ * gradNorm v at hP
  rw [hv, mul_zero] at hP
  exact norm_le_zero_iff.1 hP

end IsContDiffDomain

end
