/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Convolution.Bochner`, beside `Mathlib.Analysis.Convolution`, whose
pointwise convolution this identifies with a Bochner integral valued in `L¹`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Numlib.Analysis.Convolution.Lp
import Numlib.MeasureTheory.Integral.SetIntegralCLM

/-!
# The convolution as a Bochner integral of translates

Let $G$ be an additive group with a right-invariant measure $\mu$, and let $\tau_y g = g(\cdot - y)$
denote the translate of a function $g$ by $y \in G$. For $f \in L^1(G)$ and $g \in L^1(G, F)$, the
convolution $(f \star g)(x) = \int f(y)\, g(x - y) \, d\mu(y)$ is, as an element of $L^1$, the
Bochner integral
$$f \star g = \int f(y) \, \tau_y g \, d\mu(y)$$
of the translates, taken in the Banach space $L^1(G, F)$. So a convolution is a continuous
superposition of translates. Mathlib defines `MeasureTheory.convolution` only pointwise, and this
module adds the reading as a Bochner integral.

This reading lets a bounded linear operator on $L^1$ pass through a convolution: an operator $S$
that commutes with every translation commutes with every convolution, $S(f \star g) = f \star S g$.
This is the rigorous form of the identity for shift-invariant linear systems in signal processing.
There it is usually justified by linearity and shift invariance alone. These do not suffice, because
a convolution is an integral and not a finite linear combination of translates, and the continuity
of $S$ is what carries the integral through. Compare L. Grafakos, *Classical Fourier Analysis*, 3rd
edition, Springer, 2014, §2.5, where the bounded operators that commute with translations are
characterized as convolution operators.

## Main definitions

* `MeasureTheory.Lp.translateₗᵢ`: the translation $\tau_y \colon g \mapsto g(\cdot - y)$ on
  $L^p(G, F)$, a linear isometry for a right-invariant measure.

## Main results

* `MeasureTheory.Lp.continuous_translateₗᵢ`: for $p \neq \infty$, the map $y \mapsto \tau_y g$ is
  continuous into $L^p$.
* `MeasureTheory.Lp.integrable_smul_translateₗᵢ`: for $f \in L^1$ and $p \neq \infty$, the
  $L^p$-valued function $y \mapsto f(y) \tau_y g$ is Bochner integrable.
* `MeasureTheory.Lp.coeFn_integral_smul_translateₗᵢ` and
  `MeasureTheory.Lp.integral_smul_translateₗᵢ_eq_toL1`: the $L^1$-valued integral
  $\int f(y) \tau_y g \, d\mu(y)$ is the class of the pointwise convolution $f \star g$.
* `MeasureTheory.Lp.convolutionCLM_eq_integral`: the same identity for the convolution operator with
  a real kernel.
* `MeasureTheory.Lp.coeFn_toL1_convolution_of_translateₗᵢ_comm`: a bounded linear operator $S$ on
  $L^1$ that commutes with every translation satisfies $S(f \star g) = f \star S g$.

## Proof outline

Two integrable functions that have the same integral over every measurable set of finite measure are
equal almost everywhere. The integral over a set $A$ is a bounded linear functional on $L^1$, so it
passes through the Bochner integral. On the pointwise side, Fubini's theorem exchanges the two
integrals, and the integrand is integrable on $A \times G$ because it is integrable on $G \times G$.

## Implementation notes

* With this sign convention, $\tau_y$ is the translation of harmonic analysis, so that $(f \star
  g)(x) = \int f(y) (\tau_y g)(x) \, d\mu(y)$. In contrast, `MeasureTheory.Lp.translate` in
  `Numlib.Analysis.Sobolev.Translate` is $u \mapsto u(\cdot + h)$ on an invariant open subset.
  `MeasureTheory.Lp.translateₗᵢ` is `MeasureTheory.Lp.compMeasurePreservingₗᵢ` along
  $x \mapsto x - y$.
* The set integral as a functional on $L^1$ is `MeasureTheory.L1.setIntegralCLM`, from
  `Numlib.MeasureTheory.Integral.SetIntegralCLM`. The almost-everywhere equality uses
  `MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq`, the exchange with the Bochner integral
  uses `ContinuousLinearMap.integral_comp_comm`, and the integrability on $A \times G$ is Mathlib's
  `Integrable.convolution_integrand` restricted to $A$.
* The core identity `MeasureTheory.Lp.coeFn_integral_smul_translateₗᵢ_of_integrable` needs only a
  right-invariant s-finite measure on a measurable group, and it takes the Bochner integrability of
  $y \mapsto f(y) \tau_y g$ as a hypothesis. This integrability is where topology enters: the strong
  measurability of $y \mapsto \tau_y g$ comes from the continuity of translation on $L^p$. The other
  statements therefore assume a Haar measure on a finite-dimensional real normed space.
* The statements are at $p = 1$, because the set integral is a bounded functional on $L^1$ with no
  finiteness condition on the set. The same argument gives the identity in $L^p$ for
  $1 \le p < \infty$, with the functional restricted to sets of finite measure and with Young's
  inequality (`MeasureTheory.MemLp.convolution`) in place of `Integrable.convolution_integrand`.
-/

open Filter Function MeasureTheory MeasureTheory.Measure Topology
open ContinuousLinearMap
open scoped Convolution ENNReal

namespace MeasureTheory

namespace Lp

/-! ### Translations on $L^p$ of a group -/

section Translate

variable (𝕜 : Type*) {G F : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd G]
  {μ : Measure G} [μ.IsAddRightInvariant] [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [NormedField 𝕜] [NormedSpace 𝕜 F]

variable (F p) in
/-- Let $G$ be a measurable additive group with a right-invariant measure $\mu$, let $F$ be a normed
space over a normed field $\mathbb{K}$, let $1 \le p \le \infty$, and let $y \in G$. The
**translation** by $y$ is the linear isometry
$$\tau_y \colon L^p(G, F) \to L^p(G, F), \qquad \tau_y g = g(\cdot - y).$$

It is the composition with the measure-preserving map $x \mapsto x - y$
(`MeasureTheory.Lp.compMeasurePreservingₗᵢ`). With this sign, $(f \star g)(x) = \int f(y)
(\tau_y g)(x) \, d\mu(y)$. -/
noncomputable def translateₗᵢ (y : G) : Lp F p μ →ₗᵢ[𝕜] Lp F p μ :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (· - y) (measurePreserving_sub_right μ y)

/-- For $g \in L^p(G, F)$, the translate $\tau_y g$ is equal to $x \mapsto g(x - y)$ almost
everywhere. -/
theorem coeFn_translateₗᵢ (y : G) (g : Lp F p μ) :
    translateₗᵢ 𝕜 F p y g =ᵐ[μ] fun x => g (x - y) :=
  Lp.coeFn_compMeasurePreserving g _

/-- If $g$ is in $L^p$, then the translate by $y$ of the class of $g$ is the class of
$x \mapsto g(x - y)$. -/
theorem translateₗᵢ_toLp (y : G) {g : G → F} (hg : MemLp g p μ) :
    translateₗᵢ 𝕜 F p y (hg.toLp g)
      = (hg.comp_measurePreserving (measurePreserving_sub_right μ y)).toLp (fun x => g (x - y)) :=
  rfl

/-- Translation preserves the norm: $\|\tau_y g\|_p = \|g\|_p$. -/
theorem norm_translateₗᵢ (y : G) (g : Lp F p μ) : ‖translateₗᵢ 𝕜 F p y g‖ = ‖g‖ :=
  (translateₗᵢ 𝕜 F p y).norm_map g

/-- Translation by $0$ is the identity: $\tau_0 g = g$. -/
theorem translateₗᵢ_zero (g : Lp F p μ) : translateₗᵢ 𝕜 F p (0 : G) g = g :=
  Lp.ext ((coeFn_translateₗᵢ 𝕜 0 g).trans (Eventually.of_forall fun x => by simp))

/-- Let $G$ be a measurable commutative additive group with a right-invariant measure. Then
translations compose: for all $y, z \in G$ and $g \in L^p(G, F)$,
$$\tau_y (\tau_z g) = \tau_{y + z} g.$$
-/
theorem translateₗᵢ_translateₗᵢ {G : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd G] {μ : Measure G} [μ.IsAddRightInvariant] (y z : G) (g : Lp F p μ) :
    translateₗᵢ 𝕜 F p y (translateₗᵢ 𝕜 F p z g) = translateₗᵢ 𝕜 F p (y + z) g := by
  refine Lp.ext ((coeFn_translateₗᵢ 𝕜 y _).trans ?_)
  filter_upwards [(measurePreserving_sub_right μ y).quasiMeasurePreserving.ae_eq_comp
    (coeFn_translateₗᵢ 𝕜 z g), coeFn_translateₗᵢ 𝕜 (y + z) g] with x hx hx'
  simp only [comp_apply] at hx
  rw [hx, hx', sub_sub]

end Translate

/-! ### Continuity of $y \mapsto \tau_y g$ and integrability of $y \mapsto f(y) \tau_y g$ -/

section Continuous

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F]

/-- Let $G$ be a finite-dimensional real normed space with a Haar measure $\mu$, let
$1 \le p < \infty$, and let $g \in L^p(G, F)$. Then the map $y \mapsto \tau_y g$ from $G$ to
$L^p(G, F)$ is continuous.

This is the **continuity of translation** on $L^p$. It is Mathlib's
`Continuous.compMeasurePreservingLp` for the continuous family of measure-preserving maps
$x \mapsto x - y$. -/
theorem continuous_translateₗᵢ (hp : p ≠ ∞) (g : Lp F p μ) :
    Continuous fun y : G => translateₗᵢ 𝕜 F p y g := by
  let Φ : C(G × G, G) := ⟨fun z => z.2 - z.1, by fun_prop⟩
  exact Continuous.compMeasurePreservingLp (f := fun _ => g) (g := fun y => Φ.curry y)
    continuous_const Φ.curry.continuous (fun y => measurePreserving_sub_right μ y) hp

variable {𝕜}

/-- Let $G$ be a finite-dimensional real normed space with a Haar measure $\mu$, let
$1 \le p < \infty$, let $f \colon G \to \mathbb{K}$ be integrable and let $g \in L^p(G, F)$.
Then the $L^p$-valued function $y \mapsto f(y) \, \tau_y g$ is Bochner integrable.

It is strongly measurable by the continuity of $y \mapsto \tau_y g$, and its norm is
$\|f(y)\| \, \|g\|_p$. -/
theorem integrable_smul_translateₗᵢ (hp : p ≠ ∞) {f : G → 𝕜} (hf : Integrable f μ)
    (g : Lp F p μ) : Integrable (fun y => f y • translateₗᵢ 𝕜 F p y g) μ := by
  refine Integrable.mono' (hf.norm.mul_const ‖g‖)
    (hf.aestronglyMeasurable.smul (continuous_translateₗᵢ 𝕜 hp g).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul, norm_translateₗᵢ]

end Continuous

/-! ### The convolution as a Bochner integral of translates -/

section Bochner

variable {G : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- **The convolution is the Bochner integral of the translates** (core form). Let $G$ be a
measurable additive group with measurable addition and negation, and with a right-invariant
s-finite measure $\mu$. Let $F$ be a real Banach space that is also a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Let $f \colon G \to \mathbb{K}$ be integrable and let
$g \in L^1(G, F)$. If the $L^1$-valued function $y \mapsto f(y) \, \tau_y g$ is Bochner
integrable, then its integral is, almost everywhere, the pointwise convolution:
$$\int f(y) \, \tau_y g \, d\mu(y) = f \star g, \qquad (f \star g)(x) = \int f(y) \, g(x - y) \,
  d\mu(y).$$

The convolution is `f ⋆[lsmul 𝕜 𝕜, μ] g`. Both sides are integrable and have the same integral
over every measurable set $A$ of finite measure. For the left side, the integral over $A$ is a
bounded functional on $L^1$ (`MeasureTheory.L1.setIntegralCLM`) and passes through the Bochner
integral. For the right side, this is Fubini's theorem on $A \times G$. -/
theorem coeFn_integral_smul_translateₗᵢ_of_integrable {f : G → 𝕜} (hf : Integrable f μ)
    (g : G →₁[μ] F) (hint : Integrable (fun y => f y • translateₗᵢ 𝕜 F 1 y g) μ) :
    ⇑(∫ y, f y • translateₗᵢ 𝕜 F 1 y g ∂μ) =ᵐ[μ] f ⋆[lsmul 𝕜 𝕜, μ] g := by
  have hg : Integrable g μ := L1.integrable_coeFn g
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _)
    (hf.integrable_convolution (lsmul 𝕜 𝕜) hg) fun A hA _ => ?_
  have h1 : ∫ x in A, (∫ y, f y • translateₗᵢ 𝕜 F 1 y g ∂μ) x ∂μ
      = ∫ y, f y • ∫ x in A, g (x - y) ∂μ ∂μ := by
    rw [← L1.setIntegralCLM_apply (𝕜 := 𝕜), ← (L1.setIntegralCLM 𝕜 A).integral_comp_comm hint]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [map_smul, L1.setIntegralCLM_apply]
    congr 1
    exact setIntegral_congr_ae hA ((coeFn_translateₗᵢ 𝕜 y g).mono fun x hx _ => hx)
  have h2 : ∫ x in A, (f ⋆[lsmul 𝕜 𝕜, μ] g) x ∂μ = ∫ y, f y • ∫ x in A, g (x - y) ∂μ ∂μ := by
    simp only [convolution_lsmul]
    have hprod : Integrable (fun z : G × G => f z.2 • g (z.1 - z.2)) ((μ.restrict A).prod μ) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact (hf.convolution_integrand (lsmul 𝕜 𝕜) hg (μ := μ) (ν := μ)).integrableOn
    rw [integral_integral_swap hprod]
    exact integral_congr_ae (Eventually.of_forall fun y => integral_smul _ _)
  rw [h1, h2]

end Bochner

section BochnerHaar

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- **The convolution is the Bochner integral of the translates.** Let $G$ be a finite-dimensional
real normed space with a Haar measure $\mu$, let $F$ be a real Banach space that is also a
normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $f \colon G \to \mathbb{K}$ be
integrable and let $g \in L^1(G, F)$. Then, almost everywhere,
$$\int f(y) \, \tau_y g \, d\mu(y) = f \star g,$$
where the left side is a Bochner integral in $L^1(G, F)$ and $(f \star g)(x) = \int f(y) \,
g(x - y) \, d\mu(y)$.

The integrability hypothesis of `MeasureTheory.Lp.coeFn_integral_smul_translateₗᵢ_of_integrable`
is supplied by `MeasureTheory.Lp.integrable_smul_translateₗᵢ`. -/
theorem coeFn_integral_smul_translateₗᵢ {f : G → 𝕜} (hf : Integrable f μ) (g : G →₁[μ] F) :
    ⇑(∫ y, f y • translateₗᵢ 𝕜 F 1 y g ∂μ) =ᵐ[μ] f ⋆[lsmul 𝕜 𝕜, μ] g :=
  coeFn_integral_smul_translateₗᵢ_of_integrable hf g
    (integrable_smul_translateₗᵢ ENNReal.one_ne_top hf g)

/-- Under the hypotheses of `MeasureTheory.Lp.coeFn_integral_smul_translateₗᵢ`, the Bochner integral
$\int f(y) \, \tau_y g \, d\mu(y)$ is equal in $L^1(G, F)$ to the class of the convolution
$f \star g$, written `f ⋆[lsmul 𝕜 𝕜, μ] g`. -/
theorem integral_smul_translateₗᵢ_eq_toL1 {f : G → 𝕜} (hf : Integrable f μ) (g : G →₁[μ] F) :
    ∫ y, f y • translateₗᵢ 𝕜 F 1 y g ∂μ
      = (hf.integrable_convolution (lsmul 𝕜 𝕜) (L1.integrable_coeFn g)).toL1 _ :=
  Lp.ext ((coeFn_integral_smul_translateₗᵢ hf g).trans (Integrable.coeFn_toL1 _).symm)

/-- Let $G$ be a finite-dimensional real normed space with a Haar measure $\mu$, let $F$ be a real
Banach space, let $K \colon G \to \mathbb{R}$ be integrable and let $g \in L^1(G, F)$. Then the
convolution operator with kernel $K$ on $L^1$ is the Bochner integral of the translates:
$$K \star g = \int K(y) \, \tau_y g \, d\mu(y).$$

The operator is `MeasureTheory.Lp.convolutionCLM F 1 hK`. -/
theorem convolutionCLM_eq_integral {K : G → ℝ} (hK : Integrable K μ) (g : G →₁[μ] F) :
    convolutionCLM F 1 hK g = ∫ y, K y • translateₗᵢ ℝ F 1 y g ∂μ :=
  Lp.ext ((coeFn_convolutionCLM hK g).trans (coeFn_integral_smul_translateₗᵢ hK g).symm)

/-- **A bounded operator on $L^1$ that commutes with the translations commutes with convolutions.**
Let $G$ be a finite-dimensional real normed space with a Haar measure $\mu$, let $F$ be a real
Banach space that is also a normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, and let
$S \colon L^1(G, F) \to L^1(G, F)$ be a continuous $\mathbb{K}$-linear map with
$S(\tau_y g) = \tau_y (S g)$ for all $y \in G$ and $g \in L^1(G, F)$. Then for every integrable
$f \colon G \to \mathbb{K}$ and every $g \in L^1(G, F)$,
$$S(f \star g) = f \star S g$$
almost everywhere.

On the left, $f \star g$ is the class in $L^1$ of the pointwise convolution. Read as the Bochner
integral $\int f(y) \, \tau_y g \, d\mu(y)$, the continuous linear map $S$ passes through the
integral (`ContinuousLinearMap.integral_comp_comm`) and commutes with each translate, and the
result is the Bochner form of $f \star S g$. -/
theorem coeFn_toL1_convolution_of_translateₗᵢ_comm (S : (G →₁[μ] F) →L[𝕜] (G →₁[μ] F))
    (hS : ∀ (y : G) (g : G →₁[μ] F), S (translateₗᵢ 𝕜 F 1 y g) = translateₗᵢ 𝕜 F 1 y (S g))
    {f : G → 𝕜} (hf : Integrable f μ) (g : G →₁[μ] F) :
    ⇑(S ((hf.integrable_convolution (lsmul 𝕜 𝕜) (L1.integrable_coeFn g)).toL1 _))
      =ᵐ[μ] f ⋆[lsmul 𝕜 𝕜, μ] (S g) := by
  rw [← integral_smul_translateₗᵢ_eq_toL1 hf g,
    ← S.integral_comp_comm (integrable_smul_translateₗᵢ ENNReal.one_ne_top hf g)]
  simp only [map_smul, hS]
  exact coeFn_integral_smul_translateₗᵢ hf (S g)

end BochnerHaar

end Lp

end MeasureTheory
