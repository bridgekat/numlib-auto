/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Mollification.lean` and `Numlib/Analysis/Sobolev/Density.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Operators
import Numlib.MeasureTheory.Function.LpSpace.Duality
import Numlib.Analysis.Calculus.ContDiffOnClosure

/-!
# Friedrichs' theorem and the characterizations of $W^{1,p}$

This module proves the results of §9.1 of [brezis2011functional] around Theorem 9.2 (Friedrichs):
Lemma 9.1, Theorem 9.2, Proposition 9.3, Remarks 2, 4(i) and 7, and the sentence of the proof of
Proposition 9.4 on $L^\infty$ bounds. It also proves the convergence of approximate identities in
$L^p$ that the proof of Proposition 9.18 in §9.4 of [brezis2011functional] needs. The setting is an
open set $\Omega$ of a finite-dimensional real normed space $E$ with an additive Haar measure $\mu$,
and functions $u \colon E \to F$ with values in a real Banach space $F$. A function
$w \colon E \to \mathcal{L}(E, F)$ is a weak derivative of $u$ on $\Omega$ if $u$ and $w$ are
locally integrable on $\Omega$ and
$$\int_\Omega \partial_y \varphi \, u \, d\mu = -\int_\Omega \varphi \, w(\cdot)\, y \, d\mu$$
for every test function $\varphi \in \mathcal{D}(\Omega)$ and every direction $y \in E$, where
$\partial_y \varphi(x) = D\varphi(x)\, y$. The space $W^{1,p}(\Omega)$ consists of the functions of
$L^p(\Omega)$ that have a weak derivative in $L^p(\Omega)$.

Lemma 9.1 says that convolution with a kernel $\rho \in L^1$ commutes with weak derivatives on the
whole space. Theorem 9.2 gives, for $u \in W^{1,p}(\Omega)$ and $1 \le p < \infty$, one sequence
$u_n \in C_c^\infty(E)$ with $u_n \to u$ in $L^p(\Omega)$ and $\nabla u_n \to \nabla u$ in
$L^p(\omega)$ for every $\omega$ with compact closure in $\Omega$. Proposition 9.3 characterizes
$W^{1,p}(\Omega)$, $1 < p \le \infty$, among the functions $u \in L^p(\Omega)$ by (ii) the bound
$|\int_\Omega \partial_y \varphi \, u| \le C \|y\| \|\varphi\|_{L^{p'}(\Omega)}$, and by (iii) the
translation estimate $\|u(\cdot + h) - u\|_{L^p(\omega)} \le C \|h\|$. Remarks 2 and 7 give regular
representatives: a $C^1$ representative when the weak derivative is continuous, a Lipschitz or
locally Lipschitz representative when the weak derivative is essentially bounded, and a constant
representative on a connected open set when the weak derivative vanishes.

## Main results

* `MeasureTheory.tendsto_eLpNorm_convolution_sub_of_tendsto_support`: if nonnegative kernels of
  integral $1$ have supports that shrink to the origin, then $\rho_i * f \to f$ in $L^p$ for
  $1 \le p < \infty$.
* `HasWeakIteratedLineDerivOn.convolution_of_integrable`,
  `HasWeakIteratedFDerivOn.convolution_of_integrable`, `MemSobolev.convolution_of_integrable`: Lemma
  9.1, $\partial(\rho * v) = \rho * \partial v$ for $\rho \in L^1$, with the norm bound
  `MemSobolev.sobolevNorm_convolution_le`.
* `MemSobolev.exists_seq_contDiff_hasCompactSupport_tendsto`,
  `MemSobolev.exists_seq_contDiff_hasCompactSupport_tendsto_of_ae_norm_le`: Theorem 9.2
  (Friedrichs), without and with the bound $\|u_n\|_\infty \le \|u\|_\infty$.
* `HasWeakFDerivOn.abs_integral_smul_fderiv_le`: Proposition 9.3, (i) $\Rightarrow$ (ii), with the
  constant $C = \|\nabla u\|_{L^p(\Omega)}$.
* `HasWeakFDerivOn.of_forall_abs_integral_smul_fderiv_le`,
  `MemSobolev.of_forall_enorm_integral_smul_fderiv_basis_le`: Proposition 9.3, (ii) $\Rightarrow$
  (i), for real-valued $u$ and $1 < p \le \infty$.
* `HasWeakFDerivOn.eLpNorm_sub_translate_le`, `HasWeakFDerivOn.eLpNorm_sub_translate_le_univ`,
  `MemSobolev.eLpNorm_sub_translate_le`, `SobolevEuclidean.eLpNorm_fn_sub_translate_le`: Proposition
  9.3, (i) $\Rightarrow$ (iii), $\|u(\cdot + h) - u\|_{L^p(\omega)} \le \|h\| \|\nabla
  u\|_{L^p(\Omega)}$ for $1 \le p < \infty$; `HasWeakFDerivOn.eLpNorm_sub_translate_le_top` is the
  same estimate at $p = \infty$.
* `abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le_of_norm_lt`,
  `abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le`: Proposition 9.3, (iii) $\Rightarrow$
  (ii), with the translation estimate for small translations, or for the translations whose segments
  stay in $\Omega$.
* `MemSobolev.of_tendsto_eLpNorm_of_eLpNorm_le`: Remark 4(i), an $L^p$ limit of functions with
  gradients bounded in $L^p$ lies in $W^{1,p}$, $1 < p \le \infty$.
* `HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm_of_ae_norm_le`: the local smooth
  approximation keeps an $L^\infty$ bound, as the proof of Proposition 9.4 uses.
* `HasWeakFDerivOn.exists_seq_contDiffBump_tendsto_ae`: near a compact set, mollifications of $u$
  have the mollified weak derivative as derivative and converge to $u$ almost everywhere.
* `HasWeakFDerivOn.exists_contDiffOn_ae_eq_of_continuousOn`: Remark 2, a function with continuous
  weak derivative has a $C^1$ representative.
* `HasWeakFDerivOn.exists_lipschitzOnWith_ae_eq_of_convex`,
  `HasWeakFDerivOn.exists_continuousOn_ae_eq_of_ae_norm_le`,
  `HasWeakFDerivOn.ae_eq_const_of_isPreconnected`: Remark 7, the $M$-Lipschitz representative on a
  convex open set, the continuous, locally $M$-Lipschitz representative on any open set, and the
  constancy of a function with vanishing weak derivative on a connected open set.

## Proof outline

Theorem 9.2 is proved without a Leibniz rule. The approximants are $\zeta_n (\rho_n * \bar u)$, with
$\bar u$ the extension of $u$ by zero, $\rho_n$ mollifiers and $\zeta_n$ cut-off functions. For a
given $\omega$ with compact closure in $\Omega$, the cut-off $\zeta_n$ equals $1$ on a neighbourhood
of $\omega$ for $n$ large, so on $\omega$ the gradient of the approximant is the mollified gradient.
The $L^p$ convergence of the approximants uses only $0 \le \zeta_n \le 1$ and the vanishing of the
$L^p$ mass outside large balls.

Proposition 9.3, (i) $\Rightarrow$ (iii), uses the local approximation on one relatively compact set
at a time instead of Theorem 9.2, and an exhaustion of $\omega$ extends the estimate to any open
$\omega$. The representatives of Remarks 2 and 7 share one construction: on a compact
$K \subseteq \Omega$, the mollifications of a truncation of $u$ have the mollified weak derivative
as derivative and, along a subsequence, converge to $u$ almost everywhere. The mean value theorem
transfers gradient bounds to increments, and uniform convergence of the derivatives transfers
continuity of the weak derivative to differentiability of the limit. Local representatives are glued
by `MeasureTheory.exists_continuousOn_ae_eq_of_forall_exists_ball`.

## Implementation notes

* A weak derivative is `HasWeakFDerivOn u w Ω μ`, from `Numlib.Analysis.Sobolev.WeakDeriv`.
  Membership in $W^{1,p}(\Omega)$ is `MemSobolev u 1 p Ω μ`, from `Numlib.Analysis.Sobolev.Domain`.
  A norm $\|g\|_{L^p(A)}$ is `eLpNorm g p (μ.restrict A)`, with values in $[0, \infty]$; for $g$
  with values in $\mathcal{L}(E, F)$ it is taken of the operator norm.
* The tools are the mollification theory of `Numlib.Analysis.Sobolev.Mollification` and the density
  theorems of `Numlib.Analysis.Sobolev.Density`. The whole-space case of Theorem 9.2 is
  `MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm` at order $1$, and the local
  approximation on one relatively compact open $\omega$ is
  `MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`.
* A set "$\omega \subset\subset \Omega$" is a set $V$ with `IsCompact (closure V)` and
  `closure V ⊆ Ω`. The condition $|h| < \operatorname{dist}(\omega, \partial\Omega)$ of the source
  is replaced by the condition that every segment $[x, x + h]$, $x \in \omega$, lies in $\Omega$.
* The results of Remark 7 are stated for real-valued functions, because McShane's extension
  `LipschitzOnWith.extend_real` is available there.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal Topology

noncomputable section

/-! ### Approximate identities converge in $L^p$ -/

section ApproximateIdentity

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {p : ℝ≥0∞} {f : G → F}

/-- Let $G$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, let $F$
be a real Banach space, and let $1 \le p < \infty$. Let $(\rho_i)$ be a family of functions
$G \to \mathbb{R}$, indexed along a filter $l$, such that each $\rho_i$ is nonnegative and
integrable with $\int \rho_i \, d\mu = 1$, and $\operatorname{supp} \rho_i$ lies in the closed
ball of radius $r_i$ about $0$, where $r_i \to 0$ along $l$. Then for every $f \in L^p(G; F)$,
$$\|\rho_i * f - f\|_{L^p} \to 0 \quad \text{along } l.$$

This is the case of `MeasureTheory.tendsto_eLpNorm_convolution_sub` in which the supports shrink
to $0$ through balls of radii $r_i \to 0$. The special case of normalized bumps is
`ContDiffBump.tendsto_eLpNorm_convolution_sub`. The general form is what the one-sided
mollifiers $\rho_n(x) = n^N \rho(nx)$, with $\operatorname{supp} \rho \subseteq \{1/2 < x_N <
1\}$, of the proof of Proposition 9.18, (iii) $\Rightarrow$ (i), in §9.4 of
[brezis2011functional] need. The convolution is `ρ i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f`. -/
theorem MeasureTheory.tendsto_eLpNorm_convolution_sub_of_tendsto_support {ι : Type*}
    {l : Filter ι} {ρ : ι → G → ℝ} {r : ι → ℝ} (hρ₀ : ∀ i t, 0 ≤ ρ i t)
    (hρ : ∀ i, Integrable (ρ i) μ) (hρ₁ : ∀ i, ∫ t, ρ i t ∂μ = 1)
    (hsupp : ∀ i, Function.support (ρ i) ⊆ closedBall 0 (r i)) (hr : Tendsto r l (𝓝 0))
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : MemLp f p μ) :
    Tendsto (fun i ↦ eLpNorm (ρ i ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f - f) p μ) l (𝓝 0) := by
  refine tendsto_eLpNorm_convolution_sub (Eventually.of_forall hρ₀) (Eventually.of_forall hρ)
    (Eventually.of_forall hρ₁) (tendsto_smallSets_iff.2 fun t ht ↦ ?_) hp hp' hf
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 ht
  filter_upwards [hr (Iio_mem_nhds hδ)] with i hi
  exact (hsupp i).trans ((closedBall_subset_ball hi).trans hδsub)

end ApproximateIdentity

/-! ### Proposition 9.3, (i) $\Rightarrow$ (ii) -/

section Characterization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {μ : Measure E} {u : E → F} {w : E → E →L[ℝ] F} {p q : ℝ≥0∞}

/-- Let $E$ be a separable real normed space with a measure $\mu$, let $\Omega \subseteq E$ be open,
and let $p, q \in [1, \infty]$ be Hölder conjugate. If $w$ is a weak derivative of
$u \colon E \to F$ on $\Omega$, then for every test function $\varphi \in \mathcal{D}(\Omega)$
and every $y \in E$,
$$\Big\| \int_\Omega \partial_y \varphi \, u \, d\mu \Big\| \le \|y\| \, \|w\|_{L^p(\Omega)} \,
  \|\varphi\|_{L^q(\Omega)}.$$

This is the implication (i) $\Rightarrow$ (ii) of Proposition 9.3 of [brezis2011functional],
which the source calls obvious, with the constant $C = \|\nabla u\|_{L^p(\Omega)}$. It holds for
$p = 1$ as well, as Remark 6 of the source says. The defining identity turns the integral into
$-\int_\Omega \varphi \, w(\cdot) y$, and Hölder's inequality bounds it. -/
theorem HasWeakFDerivOn.abs_integral_smul_fderiv_le (h : HasWeakFDerivOn u w Ω μ)
    [ENNReal.HolderConjugate p q] (φ : 𝓓(Ω, ℝ)) (y : E) :
    ‖∫ x in (Ω : Set E), fderiv ℝ φ x y • u x ∂μ‖ₑ
      ≤ ‖y‖ₑ * eLpNorm w p (μ.restrict (Ω : Set E)) * eLpNorm φ q (μ.restrict (Ω : Set E)) := by
  rw [h.integral_smul_eq φ y, enorm_neg]
  have hw : AEStronglyMeasurable w (μ.restrict (Ω : Set E)) :=
    h.locallyIntegrableOn_weakDeriv.aestronglyMeasurable
  have hwy : AEStronglyMeasurable (fun x ↦ w x y) (μ.restrict (Ω : Set E)) :=
    (ContinuousLinearMap.apply ℝ F y).continuous.comp_aestronglyMeasurable hw
  calc ‖∫ x in (Ω : Set E), φ x • w x y ∂μ‖ₑ
      ≤ eLpNorm φ q (μ.restrict (Ω : Set E)) * eLpNorm (fun x ↦ w x y) p (μ.restrict (Ω : Set E)) :=
        enorm_integral_smul_le_eLpNorm_mul_eLpNorm
    _ ≤ eLpNorm φ q (μ.restrict (Ω : Set E)) * (‖y‖ₑ * eLpNorm w p (μ.restrict (Ω : Set E))) := by
        gcongr
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p hwy (Eventually.of_forall fun x ↦ ?_)
        rw [mul_comm]
        exact (w x).le_opENorm y
    _ = ‖y‖ₑ * eLpNorm w p (μ.restrict (Ω : Set E)) * eLpNorm φ q (μ.restrict (Ω : Set E)) := by
        ring

end Characterization

section BoundedApprox

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {n : ℕ} {y : Fin n → E}
  {f w : E → F} {p : ℝ≥0∞}

/-- Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, let
$\Omega \subseteq E$ be open, let $y = (y_1, \dots, y_n)$ be a tuple of directions, and let
$1 \le p < \infty$. Let $w$ be a weak derivative of $f \colon E \to F$ along $y$ on $\Omega$,
with $f$ and $w$ locally in $L^p$ on $\Omega$, and let $M \ge 0$ with $\|f\| \le M$ almost
everywhere on $\Omega$. Let $V$ be an open set whose closure is compact and contained in
$\Omega$. Then there are functions $g_j \in C^\infty(E)$ such that $g_j$ and $\partial^y g_j$
lie in $L^p(V)$, $\|g_j(x)\| \le M$ for all $j$ and $x$, and
$$g_j \to f \quad \text{and} \quad \partial^y g_j \to w \quad \text{in } L^p(V).$$

This is the local approximation `HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm`
with the additional bound $\|g_j\| \le M$. It is the sentence "checking the proof of Theorem
9.2, we see easily that we have further $\|u_n\|_\infty \le \|u\|_\infty$" of the proof of
Proposition 9.4 in §9.1 of [brezis2011functional], in the local form that the product rule for
$L^p \times L^\infty$ needs. The approximants are mollifications of a truncation of $f$ by
nonnegative normalized bumps, and such a mollification never exceeds the essential bound of the
function (`ContDiffBump.norm_convolution_normed_le_of_ae_norm_le`). The derivative
$\partial^y g_j(x)$ is `iteratedFDeriv ℝ n (g j) x y`. -/
theorem HasWeakIteratedLineDerivOn.exists_seq_contDiff_tendsto_eLpNorm_of_ae_norm_le
    (h : HasWeakIteratedLineDerivOn y f w Ω μ) (hf : LocallyMemLpOn f p Ω μ)
    (hw : LocallyMemLpOn w p Ω μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖f x‖ ≤ M) {V : Set E} (hVo : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ (Ω : Set E)) :
    ∃ g : ℕ → E → F, (∀ j, ContDiff ℝ ∞ (g j)) ∧ (∀ j, MemLp (g j) p (μ.restrict V)) ∧
      (∀ j, MemLp (fun x ↦ iteratedFDeriv ℝ n (g j) x y) p (μ.restrict V)) ∧
      (∀ j x, ‖g j x‖ ≤ M) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ g j x - f x) p (μ.restrict V)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ iteratedFDeriv ℝ n (g j) x y - w x) p (μ.restrict V))
        atTop (𝓝 0) := by
  obtain ⟨g, hgs, hgp, hgdp, hgt, hgdt, hgM⟩ :=
    h.exists_seq_contDiff_tendsto_eLpNorm_and_norm_le hf hw hp hp' hVo hVc hVΩ
  exact ⟨g, hgs, hgp, hgdp, hgM M hM0 hM, hgt, hgdt⟩

end BoundedApprox

/-! ### Lemma 9.1: convolution with an integrable kernel -/

section Convolution

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {n : ℕ} {y : Fin n → E}
  {v w : E → F} {p q : ℝ≥0∞}

omit [CompleteSpace F] in
/-- Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, and let
$p, q \in [1, \infty]$ be Hölder conjugate. If $b \in L^q(E)$ and $\rho \in L^1(E)$ are
real-valued and $g \in L^p(E; F)$, then the function $(x, t) \mapsto b(x)\, \rho(t)\, g(x - t)$
is integrable on $E \times E$ for $\mu \otimes \mu$.

This is the integrability that justifies the two applications of Fubini's theorem in the proof
of Lemma 9.1 of [brezis2011functional]. Hölder's inequality in $x$ and the translation
invariance of $\mu$ bound the inner integral by $\|b\|_{L^q} \|g\|_{L^p}$, uniformly in $t$. -/
theorem MeasureTheory.integrable_smul_smul_sub_prod [ENNReal.HolderConjugate p q]
    {b ρ : E → ℝ} {g : E → F} (hb : MemLp b q μ) (hρ : Integrable ρ μ) (hg : MemLp g p μ) :
    Integrable (fun z : E × E ↦ b z.1 • ρ z.2 • g (z.1 - z.2)) (μ.prod μ) := by
  have hgm : AEStronglyMeasurable (fun z : E × E ↦ g (z.1 - z.2)) (μ.prod μ) :=
    AEStronglyMeasurable.comp_fst_sub_snd hg.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun z : E × E ↦ b z.1 • ρ z.2 • g (z.1 - z.2))
      (μ.prod μ) :=
    hb.aestronglyMeasurable.comp_fst.smul (hρ.aestronglyMeasurable.comp_snd.smul hgm)
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hinner : ∀ t, ∫⁻ x, ‖b x‖ₑ * ‖g (x - t)‖ₑ ∂μ ≤ eLpNorm b q μ * eLpNorm g p μ := by
    intro t
    calc ∫⁻ x, ‖b x‖ₑ * ‖g (x - t)‖ₑ ∂μ = ∫⁻ x, ‖(b • fun x ↦ g (x - t)) x‖ₑ ∂μ := by
          simp only [Pi.smul_apply', enorm_smul]
      _ ≤ eLpNorm (b • fun x ↦ g (x - t)) 1 μ := lintegral_enorm_le_eLpNorm_one
      _ ≤ eLpNorm b q μ * eLpNorm (fun x ↦ g (x - t)) p μ :=
          eLpNorm_smul_le_mul_eLpNorm_of_pos one_pos
      _ = eLpNorm b q μ * eLpNorm g p μ := by
          rw [show (fun x ↦ g (x - t)) = g ∘ (fun x ↦ x - t) from rfl,
            eLpNorm_comp_measurePreserving hg.aestronglyMeasurable
            (measurePreserving_sub_right μ t)]
  have hae : AEMeasurable (fun z : E × E ↦ ‖ρ z.2‖ₑ * (‖b z.1‖ₑ * ‖g (z.1 - z.2)‖ₑ)) (μ.prod μ) :=
    hρ.aestronglyMeasurable.comp_snd.enorm.mul
      (hb.aestronglyMeasurable.comp_fst.enorm.mul hgm.enorm)
  calc ∫⁻ z, ‖b z.1 • ρ z.2 • g (z.1 - z.2)‖ₑ ∂(μ.prod μ)
      = ∫⁻ z, ‖ρ z.2‖ₑ * (‖b z.1‖ₑ * ‖g (z.1 - z.2)‖ₑ) ∂(μ.prod μ) := by
        refine lintegral_congr fun z ↦ ?_
        rw [enorm_smul, enorm_smul]; ring
    _ = ∫⁻ t, ∫⁻ x, ‖ρ t‖ₑ * (‖b x‖ₑ * ‖g (x - t)‖ₑ) ∂μ ∂μ := lintegral_prod_symm _ hae
    _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ x, ‖b x‖ₑ * ‖g (x - t)‖ₑ ∂μ ∂μ := by
        refine lintegral_congr fun t ↦ ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top]
    _ ≤ ∫⁻ t, ‖ρ t‖ₑ * (eLpNorm b q μ * eLpNorm g p μ) ∂μ := by
        refine lintegral_mono fun t ↦ ?_
        gcongr
        exact hinner t
    _ = eLpNorm ρ 1 μ * (eLpNorm b q μ * eLpNorm g p μ) := by
        rw [lintegral_mul_const'' _ hρ.aestronglyMeasurable.enorm,
          eLpNorm_one_eq_lintegral_enorm hρ.aestronglyMeasurable]
    _ < ⊤ := ENNReal.mul_lt_top (memLp_one_iff_integrable.2 hρ).eLpNorm_lt_top
        (ENNReal.mul_lt_top hb.eLpNorm_lt_top hg.eLpNorm_lt_top)

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- The translate $z \mapsto \varphi(z + t)$ of a test function $\varphi$ on the whole space $E$, as
a test function on $E$. -/
def TestFunction.compAddRight (φ : 𝓓((⊤ : Opens E), F)) (t : E) : 𝓓((⊤ : Opens E), F) where
  toFun z := φ (z + t)
  contDiff' := φ.contDiff.comp (contDiff_id.add contDiff_const)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight t)
  tsupport_subset' := by simp

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- The translate `TestFunction.compAddRight φ t` is the function $z \mapsto \varphi(z + t)$. -/
@[simp]
theorem TestFunction.compAddRight_coe (φ : 𝓓((⊤ : Opens E), F)) (t : E) :
    (φ.compAddRight t : E → F) = fun z ↦ φ (z + t) :=
  rfl

omit [CompleteSpace F] in
/-- **Lemma 9.1** of [brezis2011functional], along a tuple of directions. Let $E$ be a
finite-dimensional real normed space with an additive Haar measure $\mu$, let
$y = (y_1, \dots, y_n)$ be a tuple of directions, and let $1 \le p \le \infty$. Let $w$ be a
weak derivative of $v \colon E \to F$ along $y$ on the whole space $E$, with
$v, w \in L^p(E; F)$, and let $\rho \in L^1(E)$ be real-valued. Then $\rho * w$ is a weak
derivative of $\rho * v$ along $y$ on $E$:
$$\partial^y (\rho * v) = \rho * \partial^y v.$$

The source proves Lemma 9.1 by "adapt the proof of Lemma 8.4", whose one-dimensional form is
Lemma 8.4; the statement for $W^{k,p}$ is `MemSobolev.convolution_of_integrable`. The kernel is
not a bump, so $\rho * v$ need not be smooth, and the identity is proved by Fubini's theorem:
$\int \partial^y \varphi \, (\rho * v) = \int \rho(t) \int \partial^y \varphi(x)\, v(x - t) \,
dx \, dt$, and the inner integral is the defining identity of the weak derivative of $v$, tested
against the translate $\varphi(\cdot + t)$ (`TestFunction.compAddRight`). Both interchanges are
justified by `MeasureTheory.integrable_smul_smul_sub_prod`. -/
theorem HasWeakIteratedLineDerivOn.convolution_of_integrable
    (h : HasWeakIteratedLineDerivOn y v w ⊤ μ) {ρ : E → ℝ} (hρ : Integrable ρ μ) (hp : 1 ≤ p)
    (hv : MemLp v p μ) (hw : MemLp w p μ) :
    HasWeakIteratedLineDerivOn y (ρ ⋆[lsmul ℝ ℝ, μ] v) (ρ ⋆[lsmul ℝ ℝ, μ] w) ⊤ μ where
  locallyIntegrableOn :=
    ((MemLp.convolution hp (memLp_one_iff_integrable.2 hρ) hv).locallyIntegrable hp
      |>.locallyIntegrableOn _)
  locallyIntegrableOn_weakDeriv :=
    ((MemLp.convolution hp (memLp_one_iff_integrable.2 hρ) hw).locallyIntegrable hp
      |>.locallyIntegrableOn _)
  integral_smul_eq φ := by
    have : ENNReal.HolderConjugate p (ENNReal.conjExponent p) :=
      ENNReal.HolderConjugate.conjExponent hp
    set q := ENNReal.conjExponent p with hq
    set a : E → ℝ := fun x ↦ iteratedFDeriv ℝ n (φ : E → ℝ) x y with hadef
    have ha : MemLp a q μ := (φ.iteratedFDerivApply n y).memLp q μ
    have hφq : MemLp (φ : E → ℝ) q μ := φ.memLp q μ
    -- the defining identity of the weak derivative, tested against the translate `φ (· + t)`
    have key : ∀ t : E, ∫ x, a x • v (x - t) ∂μ
        = (-1 : ℝ) ^ n • ∫ x, (φ : E → ℝ) x • w (x - t) ∂μ := by
      intro t
      have e1 : ∫ x, a x • v (x - t) ∂μ
          = ∫ s, iteratedFDeriv ℝ n (φ.compAddRight t : E → ℝ) s y • v s ∂μ := by
        rw [← integral_add_right_eq_self (fun x ↦ a x • v (x - t)) t]
        refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
        simp only [hadef, TestFunction.compAddRight_coe, add_sub_cancel_right,
          iteratedFDeriv_comp_add_right]
      have e2 : ∫ s, (φ.compAddRight t : E → ℝ) s • w s ∂μ
          = ∫ x, (φ : E → ℝ) x • w (x - t) ∂μ := by
        rw [← integral_add_right_eq_self (fun x ↦ (φ : E → ℝ) x • w (x - t)) t]
        refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
        simp only [TestFunction.compAddRight_coe, add_sub_cancel_right]
      rw [e1, h.integral_smul_eq' (φ.compAddRight t), e2]
    simp only [Opens.coe_top, Measure.restrict_univ]
    calc ∫ x, a x • (ρ ⋆[lsmul ℝ ℝ, μ] v) x ∂μ
        = ∫ x, ∫ t, a x • ρ t • v (x - t) ∂μ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          dsimp only
          simp only [convolution_def, lsmul_apply]
          rw [integral_smul]
      _ = ∫ t, ∫ x, a x • ρ t • v (x - t) ∂μ ∂μ :=
          integral_integral_swap (integrable_smul_smul_sub_prod ha hρ hv)
      _ = ∫ t, ρ t • ∫ x, a x • v (x - t) ∂μ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
          dsimp only
          rw [← integral_smul]
          exact integral_congr_ae (Eventually.of_forall fun x ↦ smul_comm _ _ _)
      _ = (-1 : ℝ) ^ n • ∫ t, ∫ x, (φ : E → ℝ) x • ρ t • w (x - t) ∂μ ∂μ := by
          rw [← integral_smul]
          refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
          dsimp only
          rw [key t, smul_comm, ← integral_smul]
          exact congrArg _ (integral_congr_ae (Eventually.of_forall fun x ↦ smul_comm _ _ _))
      _ = (-1 : ℝ) ^ n • ∫ x, ∫ t, (φ : E → ℝ) x • ρ t • w (x - t) ∂μ ∂μ := by
          exact congrArg _ (integral_integral_swap (integrable_smul_smul_sub_prod hφq hρ hw)).symm
      _ = (-1 : ℝ) ^ n • ∫ x, (φ : E → ℝ) x • (ρ ⋆[lsmul ℝ ℝ, μ] w) x ∂μ := by
          refine congrArg _ (integral_congr_ae (Eventually.of_forall fun x ↦ ?_))
          dsimp only
          simp only [convolution_def, lsmul_apply]
          rw [integral_smul]


omit [CompleteSpace F] in
/-- **Lemma 9.1** of [brezis2011functional], tensor form. Let $E$ be a finite-dimensional real
normed space with an additive Haar measure $\mu$, and let $1 \le p \le \infty$. Let
$W \colon E \to \mathcal{L}^n(E; F)$ be a weak derivative of order $n$ of $v \colon E \to F$ on
the whole space $E$, with $v, W \in L^p$, and let $\rho \in L^1(E)$ be real-valued. Then
$\rho * W$ is a weak derivative of order $n$ of $\rho * v$ on $E$.

Here $\mathcal{L}^n(E; F)$ is the space of continuous $n$-linear maps `E [×n]→L[ℝ] F`. Each
direction is `HasWeakIteratedLineDerivOn.convolution_of_integrable`. The convolution of $W$ and
its evaluation at a tuple $y$ agree at every point where the convolution $\rho * W$ exists,
which is almost every point. -/
theorem HasWeakIteratedFDerivOn.convolution_of_integrable {W : E → E [×n]→L[ℝ] F}
    (h : HasWeakIteratedFDerivOn n v W ⊤ μ) {ρ : E → ℝ} (hρ : Integrable ρ μ) (hp : 1 ≤ p)
    (hv : MemLp v p μ) (hW : MemLp W p μ) :
    HasWeakIteratedFDerivOn n (ρ ⋆[lsmul ℝ ℝ, μ] v) (ρ ⋆[lsmul ℝ ℝ, μ] W) ⊤ μ where
  locallyIntegrableOn :=
    ((MemLp.convolution hp (memLp_one_iff_integrable.2 hρ) hv).locallyIntegrable hp
      |>.locallyIntegrableOn _)
  locallyIntegrableOn_weakDeriv :=
    ((MemLp.convolution hp (memLp_one_iff_integrable.2 hρ) hW).locallyIntegrable hp
      |>.locallyIntegrableOn _)
  integral_smul_eq φ y := by
    have hline := (h.lineDeriv y).convolution_of_integrable hρ hp hv
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ E) F y).comp_memLp' hW)
    rw [hline.integral_smul_eq φ]
    refine congrArg _ (integral_congr_ae ?_)
    have hex : ∀ᵐ x ∂μ, ConvolutionExistsAt ρ W x (lsmul ℝ ℝ) μ :=
      (memLp_one_iff_integrable.2 hρ).ae_convolutionExistsAt hp hW
    filter_upwards [ae_restrict_of_ae hex] with x hx
    rw [convolution_def, convolution_def, ContinuousMultilinearMap.integral_apply hx]
    rfl

omit [CompleteSpace F] in
/-- **Lemma 9.1** of [brezis2011functional], for $W^{k,p}$. Let $E$ be a finite-dimensional real
normed space with an additive Haar measure $\mu$, let $k \in \mathbb{N}$ and
$1 \le p \le \infty$. If $v \in W^{k,p}(E; F)$ and $\rho \in L^1(E)$ is real-valued, then
$\rho * v \in W^{k,p}(E; F)$.

The weak derivatives of $\rho * v$ are the convolutions $\rho * \partial^n v$
(`HasWeakIteratedFDerivOn.convolution_of_integrable`), and they lie in $L^p$ by Young's
inequality. The source states the lemma for $W^{1,p}$; this version holds at every order. -/
theorem MemSobolev.convolution_of_integrable {k : ℕ} (hv : MemSobolev v k p ⊤ μ) {ρ : E → ℝ}
    (hρ : Integrable ρ μ) (hp : 1 ≤ p) : MemSobolev (ρ ⋆[lsmul ℝ ℝ, μ] v) k p ⊤ μ := by
  have hρ1 : MemLp ρ 1 μ := memLp_one_iff_integrable.2 hρ
  refine ⟨by simpa [Measure.restrict_coe_top] using MemLp.convolution hp hρ1 hv.memLp_top,
    fun m hm ↦ ?_⟩
  obtain ⟨W, hW, hWp⟩ := hv.exists_hasWeakIteratedFDerivOn hm
  rw [Measure.restrict_coe_top] at hWp
  exact ⟨_, hW.convolution_of_integrable hρ hp hv.memLp_top hWp,
    by simpa [Measure.restrict_coe_top] using MemLp.convolution hp hρ1 hWp⟩

/-- Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, let
$k \in \mathbb{N}$ and $1 \le p \le \infty$. If $v \in W^{k,p}(E; F)$ and $\rho \in L^1(E)$ is
real-valued, then
$$\|\rho * v\|_{W^{k,p}(E)} \le \|\rho\|_{L^1} \, \|v\|_{W^{k,p}(E)}.$$

The norm is `sobolevNorm`, built from the $L^p$ norms of the weak derivatives of orders
$0, \dots, k$. The proof is Young's inequality at each order. -/
theorem MemSobolev.sobolevNorm_convolution_le {k : ℕ} (hv : MemSobolev v k p ⊤ μ) {ρ : E → ℝ}
    (hρ : Integrable ρ μ) (hp : 1 ≤ p) :
    sobolevNorm (ρ ⋆[lsmul ℝ ℝ, μ] v) k p ⊤ μ ≤ eLpNorm ρ 1 μ * sobolevNorm v k p ⊤ μ := by
  have hterm : ∀ m ≤ k, eLpNorm (weakIteratedFDeriv m (ρ ⋆[lsmul ℝ ℝ, μ] v) ⊤ μ) p
      (μ.restrict ((⊤ : Opens E) : Set E))
      ≤ eLpNorm ρ 1 μ
        * eLpNorm (weakIteratedFDeriv m v ⊤ μ) p (μ.restrict ((⊤ : Opens E) : Set E)) := by
    intro m hm
    have hW := hv.hasWeakIteratedFDerivOn hm
    have hWp := hv.memLp_weakIteratedFDeriv hm
    rw [Measure.restrict_coe_top] at hWp
    rw [(hW.convolution_of_integrable hρ hp hv.memLp_top hWp).eLpNorm_weakIteratedFDeriv,
      Measure.restrict_coe_top]
    exact eLpNorm_convolution_lsmul_le hp hρ.aestronglyMeasurable hWp.aestronglyMeasurable
  rcases eq_or_ne p ⊤ with rfl | hp'
  · simp only [sobolevNorm, ↓reduceIte]
    rw [ENNReal.mul_iSup]
    exact iSup_mono fun m ↦ hterm m (Nat.lt_succ_iff.1 m.2)
  · have hP : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp'
    simp only [sobolevNorm, hp', ↓reduceIte]
    calc (∑ m : Fin (k + 1), eLpNorm (weakIteratedFDeriv m (ρ ⋆[lsmul ℝ ℝ, μ] v) ⊤ μ) p
            (μ.restrict ((⊤ : Opens E) : Set E)) ^ p.toReal) ^ (1 / p.toReal)
        ≤ (∑ m : Fin (k + 1), (eLpNorm ρ 1 μ * eLpNorm (weakIteratedFDeriv m v ⊤ μ) p
            (μ.restrict ((⊤ : Opens E) : Set E))) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr with m
          exact hterm m (Nat.lt_succ_iff.1 m.2)
      _ = eLpNorm ρ 1 μ * (∑ m : Fin (k + 1), eLpNorm (weakIteratedFDeriv m v ⊤ μ) p
            (μ.restrict ((⊤ : Opens E) : Set E)) ^ p.toReal) ^ (1 / p.toReal) := by
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hP.le, ← Finset.mul_sum,
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.toReal),
            ← ENNReal.rpow_mul, mul_one_div_cancel hP.ne', ENNReal.rpow_one]

end Convolution

/-! ### Theorem 9.2 (Friedrichs) -/

section Friedrichs

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {f : E → F}
  {w : E → E →L[ℝ] F} {p : ℝ≥0∞}

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] in
/-- For $g \colon E \to F$ and $x \in E$, the first iterated derivative $D^1 g(x)$ is the derivative
$Dg(x)$, read as a continuous $1$-linear map through `continuousMultilinearCurryFin1`. -/
theorem iteratedFDeriv_one_eq_symm_fderiv (g : E → F) (x : E) :
    iteratedFDeriv ℝ 1 g x = (continuousMultilinearCurryFin1 ℝ E F).symm (fderiv ℝ g x) :=
  iteratedFDeriv_one_eq_symm_fderiv' g x

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- Let $\Omega \subseteq E$ be open, let $\mu$ be a measure on $E$, and let
$f \in W^{1,p}(\Omega; F)$. Then $f$ has a weak derivative $w \colon E \to \mathcal{L}(E, F)$ on
$\Omega$ with $w \in L^p(\Omega)$.

This converts the weak derivative of order $1$ of `MemSobolev`, which takes values in the
$1$-linear maps, into one with values in $\mathcal{L}(E, F)$. -/
theorem MemSobolev.exists_hasWeakFDerivOn (hf : MemSobolev f 1 p Ω μ) :
    ∃ w : E → E →L[ℝ] F, HasWeakFDerivOn f w Ω μ ∧ MemLp w p (μ.restrict (Ω : Set E)) := by
  obtain ⟨W, hW, hWp⟩ := hf.exists_hasWeakIteratedFDerivOn (n := 1) le_rfl
  refine ⟨fun x ↦ continuousMultilinearCurryFin1 ℝ E F (W x), ?_,
    (continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
      |>.comp_memLp' hWp⟩
  unfold HasWeakFDerivOn
  convert hW using 2
  simp

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- Let $\Omega \subseteq E$ be open and let $\mu$ be a measure on $E$. If $f \in L^p(\Omega; F)$
has a weak derivative $w \in L^p(\Omega)$ on $\Omega$, then $f \in W^{1,p}(\Omega; F)$. -/
theorem HasWeakFDerivOn.memSobolev (h : HasWeakFDerivOn f w Ω μ)
    (hf : MemLp f p (μ.restrict (Ω : Set E))) (hw : MemLp w p (μ.restrict (Ω : Set E))) :
    MemSobolev f 1 p Ω μ := by
  refine ⟨hf, fun m hm ↦ ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by exact_mod_cast hm) with rfl | rfl
  · exact ⟨_, hasWeakIteratedFDerivOn_zero h.locallyIntegrableOn,
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
        |>.comp_memLp' hf⟩
  · exact ⟨_, h, (continuousMultilinearCurryFin1 ℝ E F).symm.toContinuousLinearEquiv
      |>.toContinuousLinearMap.comp_memLp' hw⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- Let $\Omega' \subseteq \Omega$ be open sets of $E$. A weak derivative of $f$ on $\Omega$ is a
weak derivative of $f$ on $\Omega'$. -/
theorem HasWeakFDerivOn.mono {Ω' : Opens E} (h : HasWeakFDerivOn f w Ω μ) (hΩ : Ω' ≤ Ω) :
    HasWeakFDerivOn f w Ω' μ :=
  HasWeakIteratedFDerivOn.mono h hΩ

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [μ.IsAddHaarMeasure] in
/-- Let $E$ be a finite-dimensional real normed space with a Borel measure $\mu$, let
$\Omega \subseteq E$ be open, and let $F$ be a real Banach space. If $w_1$ and $w_2$ are weak
derivatives of the same $f \colon E \to F$ on $\Omega$, then $w_1 = w_2$ almost everywhere on
$\Omega$. -/
theorem HasWeakFDerivOn.ae_eq [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F]
    {w₁ w₂ : E → E →L[ℝ] F} (h₁ : HasWeakFDerivOn f w₁ Ω μ) (h₂ : HasWeakFDerivOn f w₂ Ω μ) :
    ∀ᵐ x ∂μ, x ∈ (Ω : Set E) → w₁ x = w₂ x := by
  filter_upwards [HasWeakIteratedFDerivOn.ae_eq h₁ h₂] with x hx hxΩ
  exact (continuousMultilinearCurryFin1 ℝ E F).symm.injective (hx hxΩ)

/-- Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, let
$\Omega \subseteq E$ be open, let $1 \le p < \infty$, and let $f \in W^{1,p}(\Omega; F)$. Then
there is a sequence $u_n \in C^\infty(E)$ of functions with compact support with the following
three properties.

* $u_n \to f$ in $L^p(\Omega)$.
* For every weak derivative $w$ of $f$ on $\Omega$ and every set $V$ whose closure is compact
  and contained in $\Omega$, $\nabla u_n \to w$ in $L^p(V)$.
* For every $M \ge 0$ with $\|f\| \le M$ almost everywhere on $\Omega$, $\|u_n(x)\| \le M$ for
  all $n$ and all $x \in E$.

This is the construction of Theorem 9.2 (Friedrichs) of [brezis2011functional]. The functions
are $u_n = \zeta_n (\rho_n * \bar f)$, where $\bar f$ is the extension of $f$ by zero, $\rho_n$
are normalized bumps of radii tending to $0$, and $\zeta_n = \zeta(\cdot / (n + 1))$ are the
cut-off functions of footnote 5 of the source. The theorems
`MemSobolev.exists_seq_contDiff_hasCompactSupport_tendsto` and
`MemSobolev.exists_seq_contDiff_hasCompactSupport_tendsto_of_ae_norm_le` are its two readings. -/
theorem MemSobolev.exists_seq_contDiff_hasCompactSupport_tendsto_aux (hf : MemSobolev f 1 p Ω μ)
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    ∃ u : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      Tendsto (fun n ↦ eLpNorm (u n - f) p (μ.restrict (Ω : Set E))) atTop (𝓝 0) ∧
      (∀ w : E → E →L[ℝ] F, HasWeakFDerivOn f w Ω μ → ∀ V : Set E, IsCompact (closure V) →
        closure V ⊆ (Ω : Set E) →
        Tendsto (fun n ↦ eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p (μ.restrict V)) atTop (𝓝 0)) ∧
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂μ.restrict (Ω : Set E), ‖f x‖ ≤ M) → ∀ n x, ‖u n x‖ ≤ M := by
  obtain ⟨W, hW, hWp⟩ := hf.exists_hasWeakIteratedFDerivOn (n := 1) le_rfl
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  -- extension by zero of `f` and of its weak derivative
  set f' : E → F := (Ω : Set E).indicator f with hf'def
  set W' : E → E [×1]→L[ℝ] F := (Ω : Set E).indicator W with hW'def
  have hf'Lp : MemLp f' p μ := (memLp_indicator_iff_restrict hΩm.nullMeasurableSet).2 hf.memLp
  have hW'Lp : MemLp W' p μ := (memLp_indicator_iff_restrict hΩm.nullMeasurableSet).2 hWp
  have hf'loc : LocallyIntegrable f' μ := hf'Lp.locallyIntegrable hp
  have hint : HasWeakIteratedFDerivOn 1 f' W' Ω μ :=
    hW.congr_ae
      (Filter.eventually_of_mem (self_mem_ae_restrict hΩm)
        fun z hz ↦ (Set.indicator_of_mem hz f).symm)
      (Filter.eventually_of_mem (self_mem_ae_restrict hΩm)
        fun z hz ↦ (Set.indicator_of_mem hz W).symm)
  -- mollification
  obtain ⟨φ, hφ⟩ := exists_seq_contDiffBump_tendsto_rOut_zero E
  set v : ℕ → E → F := fun n ↦ (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] f' with hvdef
  have hvs : ∀ n, ContDiff ℝ ∞ (v n) := fun n ↦ hf'loc.contDiff_convolution_normed (φ n)
  have hvt : Tendsto (fun n ↦ eLpNorm (v n - f') p μ) atTop (𝓝 0) :=
    ContDiffBump.tendsto_eLpNorm_convolution_sub hφ hp hp' hf'Lp
  have hWt : Tendsto (fun n ↦ eLpNorm ((φ n).normed μ ⋆[lsmul ℝ ℝ, μ] W' - W') p μ) atTop (𝓝 0) :=
    ContDiffBump.tendsto_eLpNorm_convolution_sub hφ hp hp' hW'Lp
  -- cut-offs
  obtain ⟨η, hηs, hη1, hηsupp, hη01⟩ := exists_contDiff_eqOn_one_closedBall_one E
  set R : ℕ → ℝ := fun n ↦ (n : ℝ) + 1 with hRdef
  have hRpos : ∀ n, 0 < R n := fun n ↦ by positivity
  have hRt : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  set ζ : ℕ → E → ℝ := fun n x ↦ η ((R n)⁻¹ • x) with hζdef
  have hζs : ∀ n, ContDiff ℝ ∞ (ζ n) := fun n ↦ hηs.comp (contDiff_id.const_smul _)
  have hζ01 : ∀ n x, ζ n x ∈ Icc (0 : ℝ) 1 := fun n x ↦ hη01 _
  have hζ1 : ∀ n, ∀ x ∈ ball (0 : E) (R n), ζ n x = 1 := by
    intro n x hx
    refine hη1 (mem_closedBall_zero_iff.2 ?_)
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hRpos n), inv_mul_le_iff₀ (hRpos n),
      mul_one]
    exact (mem_ball_zero_iff.1 hx).le
  have hζc : ∀ n, HasCompactSupport (ζ n) := fun n ↦ by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R n)) fun x hx ↦ ?_
    have hnx : 2 * R n < ‖x‖ := by simpa [mem_closedBall, dist_eq_norm, not_le] using hx
    refine image_eq_zero_of_notMem_tsupport (f := η) (x := (R n)⁻¹ • x) fun hmem ↦ ?_
    have h := hηsupp hmem
    rw [mem_ball, dist_eq_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (hRpos n), inv_mul_lt_iff₀ (hRpos n)] at h
    linarith
  set u : ℕ → E → F := fun n x ↦ ζ n x • v n x with hudef
  have hus : ∀ n, ContDiff ℝ ∞ (u n) := fun n ↦ (hζs n).smul (hvs n)
  have huc : ∀ n, HasCompactSupport (u n) := fun n ↦ (hζc n).smul_right
  refine ⟨u, hus, huc, ?_, ?_, ?_⟩
  · -- convergence in `L^p(Ω)`
    have hcompl : Tendsto (fun n ↦ eLpNorm ((ball (0 : E) (R n))ᶜ.indicator f') p μ) atTop
        (𝓝 0) := hf'Lp.tendsto_eLpNorm_indicator_compl_ball hp' hRt
    have hsum : Tendsto (fun n ↦ eLpNorm (v n - f') p μ
        + eLpNorm ((ball (0 : E) (R n))ᶜ.indicator f') p μ) atTop (𝓝 0) := by
      simpa using hvt.add hcompl
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ zero_le) fun n ↦ ?_
    have hsplit : u n - f' = (fun x ↦ ζ n x • (v n x - f' x)) + fun x ↦ (ζ n x - 1) • f' x := by
      funext x
      simp only [hudef, Pi.sub_apply, Pi.add_apply, smul_sub, sub_smul, one_smul]
      abel
    have hm1 : AEStronglyMeasurable (fun x ↦ ζ n x • (v n x - f' x)) μ :=
      (hζs n).continuous.aestronglyMeasurable.smul
        ((hvs n).continuous.aestronglyMeasurable.sub hf'Lp.aestronglyMeasurable)
    have hm2 : AEStronglyMeasurable (fun x ↦ (ζ n x - 1) • f' x) μ :=
      ((hζs n).continuous.aestronglyMeasurable.sub aestronglyMeasurable_const).smul
        hf'Lp.aestronglyMeasurable
    calc eLpNorm (u n - f) p (μ.restrict (Ω : Set E))
        = eLpNorm (u n - f') p (μ.restrict (Ω : Set E)) := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [self_mem_ae_restrict hΩm] with x hx
          simp [hf'def, Set.indicator_of_mem hx]
      _ ≤ eLpNorm (u n - f') p μ := eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ eLpNorm (fun x ↦ ζ n x • (v n x - f' x)) p μ
            + eLpNorm (fun x ↦ (ζ n x - 1) • f' x) p μ := by
          rw [hsplit]; exact eLpNorm_add_le hp
      _ ≤ eLpNorm (v n - f') p μ + eLpNorm ((ball (0 : E) (R n))ᶜ.indicator f') p μ := by
          gcongr
          · refine eLpNorm_mono hm1 fun x ↦ ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hζ01 n x).1, Pi.sub_apply]
            exact mul_le_of_le_one_left (norm_nonneg _) (hζ01 n x).2
          · refine eLpNorm_mono hm2 fun x ↦ ?_
            by_cases hx : x ∈ ball (0 : E) (R n)
            · simp [hζ1 n x hx]
            · rw [Set.indicator_of_mem (show x ∈ (ball (0 : E) (R n))ᶜ from hx), norm_smul,
                Real.norm_eq_abs]
              refine mul_le_of_le_one_left (norm_nonneg _) (abs_le.2 ⟨?_, ?_⟩) <;>
                linarith [(hζ01 n x).1, (hζ01 n x).2]
  · -- convergence of the gradients on a relatively compact set
    intro w hw V hVc hVΩ
    have hw₀ : HasWeakFDerivOn f (fun x ↦ continuousMultilinearCurryFin1 ℝ E F (W x)) Ω μ := by
      unfold HasWeakFDerivOn; convert hW using 2; simp
    have hww₀ : ∀ᵐ x ∂μ.restrict V, w x = continuousMultilinearCurryFin1 ℝ E F (W x) := by
      have := hw.ae_eq hw₀
      exact ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVΩ)
        ((ae_restrict_iff' hΩm).2 this)
    obtain ⟨V', ε, -, hVV', hε, -, -, hV'ball⟩ :=
      hVc.exists_pos_forall_closedBall_subset Ω.isOpen hVΩ
    obtain ⟨r, hr⟩ := hVc.isBounded.subset_closedBall (0 : E)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (hφ.eventually (Iic_mem_nhds hε))
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (hRt.eventually (Ioi_mem_atTop r))
    have hkey : ∀ n ≥ max N₁ N₂, eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p (μ.restrict V)
        ≤ eLpNorm ((φ n).normed μ ⋆[lsmul ℝ ℝ, μ] W' - W') p μ := by
      intro n hn
      have hn₁ : (φ n).rOut ≤ ε := hN₁ n (le_of_max_le_left hn)
      have hn₂ : r < R n := hN₂ n (le_of_max_le_right hn)
      have hwm : AEStronglyMeasurable w (μ.restrict V) :=
        hw.locallyIntegrableOn_weakDeriv.aestronglyMeasurable.mono_measure
          (Measure.restrict_mono (subset_closure.trans hVΩ) le_rfl)
      refine le_trans (eLpNorm_mono_ae
        (((hus n).continuous_fderiv (by simp)).aestronglyMeasurable.sub hwm) ?_)
        (eLpNorm_mono_measure _ Measure.restrict_le_self)
      filter_upwards [hww₀, ae_restrict_of_ae_restrict_of_subset subset_closure
        (self_mem_ae_restrict hVc.isClosed.measurableSet)] with x hx hxV
      -- `u n = v n` near `x`
      have hxb : x ∈ ball (0 : E) (R n) :=
        mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 (hr hxV)).trans_lt hn₂)
      have hev : u n =ᶠ[𝓝 x] v n := by
        filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
        simp [hudef, hζ1 n y hy]
      -- the derivative of `v n` at `x` is the mollified weak derivative
      have hball : closedBall x (φ n).rOut ⊆ (Ω : Set E) :=
        (closedBall_subset_closedBall hn₁).trans (hV'ball x (hVV' hxV))
      have hder : iteratedFDeriv ℝ 1 (v n) x = ((φ n).normed μ ⋆[lsmul ℝ ℝ, μ] W') x :=
        hint.iteratedFDeriv_convolution (φ n).contDiff_normed
          (le_of_eq ((φ n).tsupport_normed_eq (μ := μ))) hball
      have hfder : fderiv ℝ (u n) x
          = continuousMultilinearCurryFin1 ℝ E F (((φ n).normed μ ⋆[lsmul ℝ ℝ, μ] W') x) := by
        rw [hev.fderiv_eq, ← hder, iteratedFDeriv_one_eq_symm_fderiv,
          LinearIsometryEquiv.apply_symm_apply]
      rw [hfder, hx, ← map_sub, LinearIsometryEquiv.norm_map, Pi.sub_apply, hW'def,
        Set.indicator_of_mem (hVΩ hxV) W]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hWt
      (Eventually.of_forall fun _ ↦ zero_le) (eventually_atTop.2 ⟨max N₁ N₂, hkey⟩)
  · -- the `L^∞` bound
    intro M hM0 hM n x
    have hf'M : ∀ᵐ z ∂μ, ‖f' z‖ ≤ M := by
      filter_upwards [(ae_restrict_iff' hΩm).1 hM] with z hz
      by_cases hzΩ : z ∈ (Ω : Set E)
      · rw [hf'def, Set.indicator_of_mem hzΩ]; exact hz hzΩ
      · rw [hf'def, Set.indicator_of_notMem hzΩ, norm_zero]; exact hM0
    calc ‖u n x‖ = |ζ n x| * ‖v n x‖ := by rw [hudef, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * M := by
          gcongr
          · exact abs_le.2 ⟨by linarith [(hζ01 n x).1], (hζ01 n x).2⟩
          · exact (φ n).norm_convolution_normed_le_of_ae_norm_le hf'M x
      _ = M := one_mul M

/-- The **Friedrichs theorem**. Let $E$ be a finite-dimensional real normed space with an additive
Haar measure $\mu$, let $\Omega \subseteq E$ be open, let $1 \le p < \infty$, and let
$f \in W^{1,p}(\Omega; F)$. Then there is a sequence $u_n \in C_c^\infty(E)$ with $u_n \to f$ in
$L^p(\Omega)$ and, for every weak derivative $w$ of $f$ on $\Omega$ and every set $V$ whose
closure is compact and contained in $\Omega$,
$$\nabla u_n \to w \quad \text{in } L^p(V).$$
This is Theorem 9.2 of [brezis2011functional].

One sequence serves all such $V$, which distinguishes the theorem from the local approximation
`MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`. Any two weak derivatives of $f$ agree almost
everywhere on $\Omega$ (`HasWeakFDerivOn.ae_eq`). The whole-space case of the theorem is
`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`. The sequence is
$\zeta_n (\rho_n * \bar f)$, with $\bar f$ the extension of $f$ by zero, $\rho_n$ normalized
bumps of radii $\varepsilon_n \to 0$, and $\zeta_n$ the cut-off functions of footnote 5 of the
source. On $V$, once $\varepsilon_n$ is below the distance from $\overline V$ to the complement
of $\Omega$, the identity $\nabla(\rho_n * \bar f) = \rho_n * \bar w$
(`HasWeakIteratedFDerivOn.iteratedFDeriv_convolution`) makes the gradients converge. The cut-off
is $1$ on a neighbourhood of $V$ for $n$ large, so no Leibniz rule is needed; this replaces the
argument of the source with the cut-off $\alpha$ and Remark 4(ii). -/
theorem MemSobolev.exists_seq_contDiff_hasCompactSupport_tendsto (hf : MemSobolev f 1 p Ω μ)
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    ∃ u : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      Tendsto (fun n ↦ eLpNorm (u n - f) p (μ.restrict (Ω : Set E))) atTop (𝓝 0) ∧
      ∀ w : E → E →L[ℝ] F, HasWeakFDerivOn f w Ω μ → ∀ V : Set E, IsCompact (closure V) →
        closure V ⊆ (Ω : Set E) →
        Tendsto (fun n ↦ eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p (μ.restrict V)) atTop
          (𝓝 0) := by
  obtain ⟨u, h₁, h₂, h₃, h₄, -⟩ := hf.exists_seq_contDiff_hasCompactSupport_tendsto_aux hp hp'
  exact ⟨u, h₁, h₂, h₃, h₄⟩

/-- The **Friedrichs theorem** with an $L^\infty$ bound. Let $E$ be a finite-dimensional real normed
space with an additive Haar measure $\mu$, let $\Omega \subseteq E$ be open, let
$1 \le p < \infty$, and let $f \in W^{1,p}(\Omega; F)$ with $\|f\| \le M$ almost everywhere on
$\Omega$ for some $M \ge 0$. Then there is a sequence $u_n \in C_c^\infty(E)$ with
$\|u_n(x)\| \le M$ for all $n$ and $x$, with $u_n \to f$ in $L^p(\Omega)$, and with
$\nabla u_n \to w$ in $L^p(V)$ for every weak derivative $w$ of $f$ on $\Omega$ and every set
$V$ whose closure is compact and contained in $\Omega$.

This is the sentence "checking the proof of Theorem 9.2, we see easily that we have further
$\|u_n\|_\infty \le \|u\|_\infty$" of the proof of Proposition 9.4 in §9.1 of
[brezis2011functional]. Mollification by a nonnegative normalized bump does not increase an
$L^\infty$ bound (`ContDiffBump.norm_convolution_normed_le_of_ae_norm_le`), and the cut-off
functions take values in $[0, 1]$. -/
theorem MemSobolev.exists_seq_contDiff_hasCompactSupport_tendsto_of_ae_norm_le
    (hf : MemSobolev f 1 p Ω μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖f x‖ ≤ M) :
    ∃ u : ℕ → E → F, (∀ n, ContDiff ℝ ∞ (u n)) ∧ (∀ n, HasCompactSupport (u n)) ∧
      (∀ n x, ‖u n x‖ ≤ M) ∧
      Tendsto (fun n ↦ eLpNorm (u n - f) p (μ.restrict (Ω : Set E))) atTop (𝓝 0) ∧
      ∀ w : E → E →L[ℝ] F, HasWeakFDerivOn f w Ω μ → ∀ V : Set E, IsCompact (closure V) →
        closure V ⊆ (Ω : Set E) →
        Tendsto (fun n ↦ eLpNorm (fun x ↦ fderiv ℝ (u n) x - w x) p (μ.restrict V)) atTop
          (𝓝 0) := by
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅⟩ := hf.exists_seq_contDiff_hasCompactSupport_tendsto_aux hp hp'
  exact ⟨u, h₁, h₂, h₅ M hM0 hM, h₃, h₄⟩

end Friedrichs

/-! ### Proposition 9.3, (ii) $\Rightarrow$ (i): the Riesz representation route -/

section TestFunctionLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {Ω : Opens E} {q : ℝ≥0∞} {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- The linear map $\mathcal{D}(\Omega) \to L^q(\Omega)$ that sends a real test function $\varphi$
on $\Omega$ to its class in $L^q(\Omega)$, for a measure $\mu$ that is finite on compact sets. -/
def TestFunction.toLpₗ (Ω : Opens E) (q : ℝ≥0∞) (μ : Measure E) [IsFiniteMeasureOnCompacts μ] :
    𝓓(Ω, ℝ) →ₗ[ℝ] Lp ℝ q (μ.restrict (Ω : Set E)) where
  toFun φ := ((φ.memLp q μ).restrict (Ω : Set E)).toLp φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `TestFunction.toLpₗ Ω q μ φ` is the class of the test function $\varphi$ in $L^q(\Omega)$. -/
@[simp]
theorem TestFunction.toLpₗ_apply (φ : 𝓓(Ω, ℝ)) :
    TestFunction.toLpₗ Ω q μ φ = ((φ.memLp q μ).restrict (Ω : Set E)).toLp φ :=
  rfl

end TestFunctionLp

section Riesz

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {u : E → ℝ} {p q : ℝ≥0∞}

/-- Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, let
$\Omega \subseteq E$ be open, and let $p, q \in [1, \infty]$ be Hölder conjugate with
$q < \infty$, that is, $1 < p \le \infty$. Let $u \in L^p(\Omega)$ be real-valued, let
$y \in E$, and let $C < \infty$ with
$$\Big| \int_\Omega \partial_y \varphi \, u \, d\mu \Big| \le C \|\varphi\|_{L^q(\Omega)}$$
for every test function $\varphi \in \mathcal{D}(\Omega)$. Then $u$ has a weak derivative
$w \in L^p(\Omega)$ along $y$ on $\Omega$.

This is the step "proceed as in the proof of Proposition 8.3" of the proof of Proposition 9.3,
(ii) $\Rightarrow$ (i), of [brezis2011functional], for one direction. The functional $\varphi
\mapsto \int_\Omega \partial_y \varphi \, u$ is bounded on the test functions for the norm of
$L^q(\Omega)$. The Hahn–Banach theorem extends it to $L^q(\Omega)$, and the Riesz representation
theorem `MeasureTheory.Lp.exists_forall_eq_integral` represents it by a function of
$L^p(\Omega)$. Density of the test functions is not needed. -/
theorem exists_hasWeakIteratedLineDerivOn_of_forall_enorm_integral_smul_fderiv_le
    [ENNReal.HolderConjugate p q] (hq : q ≠ ⊤) (hu : MemLp u p (μ.restrict (Ω : Set E)))
    (y : E) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ φ : 𝓓(Ω, ℝ), ‖∫ x in (Ω : Set E), fderiv ℝ φ x y • u x ∂μ‖ₑ
      ≤ C * eLpNorm φ q (μ.restrict (Ω : Set E))) :
    ∃ w : E → ℝ, HasWeakIteratedLineDerivOn ![y] u w Ω μ ∧ MemLp w p (μ.restrict (Ω : Set E)) := by
  have hp : 1 ≤ p := ENNReal.HolderConjugate.one_le p q
  have hq1 : 1 ≤ q := ENNReal.HolderConjugate.one_le q p
  have : Fact (1 ≤ p) := ⟨hp⟩
  have : Fact (1 ≤ q) := ⟨hq1⟩
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have huloc : LocallyIntegrableOn u Ω μ := hu.locallyIntegrableOn hp
  set ν : Measure E := μ.restrict (Ω : Set E) with hνdef
  -- the functional on the test functions
  set T₁ : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ :=
    ((TestFunction.integralAgainstBilinCLM (lsmul ℝ ℝ) μ u).comp
      (TestFunction.lineDerivCLM ℝ y : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ))).toLinearMap with hT₁def
  have hT₁ : ∀ φ : 𝓓(Ω, ℝ), T₁ φ = ∫ x in (Ω : Set E), fderiv ℝ φ x y • u x ∂μ := by
    intro φ
    simp only [hT₁def, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      TestFunction.integralAgainstBilinCLM_eq_integral huloc, lsmul_apply]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero]
    · refine setIntegral_congr_fun hΩm fun x _ ↦ ?_
      simp only [TestFunction.lineDerivCLM_apply, top_add, le_refl, ite_true]
      rw [(φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    · intro x hx
      rw [(TestFunction.lineDerivCLM ℝ y φ).eq_zero_of_notMem hx, zero_smul]
  set S : 𝓓(Ω, ℝ) →ₗ[ℝ] Lp ℝ q ν := TestFunction.toLpₗ Ω q μ with hSdef
  -- the functional vanishes on the kernel of `φ ↦ [φ]`
  have hker : LinearMap.ker S ≤ LinearMap.ker T₁ := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    have h0 : (φ : E → ℝ) =ᵐ[ν] 0 := by
      have h1 := ((φ.memLp q μ).restrict (Ω : Set E)).coeFn_toLp
      rw [show ((φ.memLp q μ).restrict (Ω : Set E)).toLp φ = S φ from rfl, hφ] at h1
      exact h1.symm.trans (Lp.coeFn_zero ℝ q ν)
    have hφ0 : EqOn (φ : E → ℝ) 0 (Ω : Set E) :=
      Measure.eqOn_open_of_ae_eq h0 Ω.isOpen φ.continuous.continuousOn continuousOn_const
    rw [hT₁]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
    have hev : (φ : E → ℝ) =ᶠ[𝓝 x] 0 :=
      Filter.eventually_of_mem (Ω.isOpen.mem_nhds hx) hφ0
    rw [hev.fderiv_eq]
    simp
  -- the induced functional on the image of the test functions, and its bound
  set T₀ : LinearMap.range S →ₗ[ℝ] ℝ :=
    ((LinearMap.ker S).liftQ T₁ hker).comp S.quotKerEquivRange.symm.toLinearMap with hT₀def
  have hT₀ : ∀ φ : 𝓓(Ω, ℝ), T₀ ⟨S φ, LinearMap.mem_range_self S φ⟩ = T₁ φ := by
    intro φ
    simp only [hT₀def, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  have hT₀bound : ∀ s : LinearMap.range S, ‖T₀ s‖ ≤ C.toReal * ‖s‖ := by
    rintro ⟨s, hs⟩
    obtain ⟨φ, rfl⟩ := LinearMap.mem_range.1 hs
    rw [hT₀, hT₁]
    change _ ≤ C.toReal * ‖S φ‖
    rw [show S φ = ((φ.memLp q μ).restrict (Ω : Set E)).toLp φ from rfl, Lp.norm_toLp,
      ← ENNReal.toReal_mul, ← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm]
    exact ENNReal.toReal_mono
      (ENNReal.mul_ne_top hC ((φ.memLp q μ).restrict (Ω : Set E)).eLpNorm_ne_top) (h φ)
  set T : LinearMap.range S →L[ℝ] ℝ :=
    LinearMap.mkContinuous T₀ C.toReal hT₀bound with hTdef
  -- Hahn–Banach and Riesz
  obtain ⟨G, hG, -⟩ := exists_extension_norm_eq (LinearMap.range S) T
  obtain ⟨v, hv⟩ := Lp.exists_forall_eq_integral (p := q) (q := p) (μ := ν) hq G
  refine ⟨-v, ⟨huloc, ((Lp.memLp v).neg.locallyIntegrableOn hp), fun φ ↦ ?_⟩,
    (Lp.memLp v).neg⟩
  have key : ∫ x in (Ω : Set E), fderiv ℝ φ x y • u x ∂μ
      = ∫ x in (Ω : Set E), v x * φ x ∂μ := by
    rw [← hT₁, ← hT₀ φ]
    change T ⟨S φ, LinearMap.mem_range_self S φ⟩ = _
    rw [← hG, hv]
    refine integral_congr_ae ?_
    filter_upwards [((φ.memLp q μ).restrict (Ω : Set E)).coeFn_toLp] with x hx
    exact congrArg _ hx
  simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero, pow_one]
  rw [key]
  simp only [Pi.neg_apply, smul_eq_mul, mul_neg, integral_neg, neg_one_mul, neg_neg]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ mul_comm _ _)


/-- **Proposition 9.3**, (ii) $\Rightarrow$ (i), with one bound for each vector of a basis. Let $E$
be a finite-dimensional real normed space with an additive Haar measure $\mu$, let
$\Omega \subseteq E$ be open, and let $p, q \in [1, \infty]$ be Hölder conjugate with
$q < \infty$, that is, $1 < p \le \infty$. Let $u \in L^p(\Omega)$ be real-valued, let $(b_i)$
be a basis of $E$, and let $C_i < \infty$ be constants with
$$\Big| \int_\Omega \partial_{b_i} \varphi \, u \, d\mu \Big| \le C_i
  \|\varphi\|_{L^q(\Omega)}$$
for every test function $\varphi \in \mathcal{D}(\Omega)$ and every $i$. Then
$u \in W^{1,p}(\Omega)$.

This is Proposition 9.3, (ii) $\Rightarrow$ (i), of [brezis2011functional] in the shape of the
source, with one inequality for each coordinate direction. Each direction is
`exists_hasWeakIteratedLineDerivOn_of_forall_enorm_integral_smul_fderiv_le`, and the multi-index
formulation `MemSobolevMultiIndex.memSobolev` assembles the gradient. -/
theorem MemSobolev.of_forall_enorm_integral_smul_fderiv_basis_le [ENNReal.HolderConjugate p q]
    (hq : q ≠ ⊤) (hu : MemLp u p (μ.restrict (Ω : Set E))) {ι : Type*} [LinearOrder ι]
    (b : Basis ι ℝ E) {C : ι → ℝ≥0∞} (hC : ∀ i, C i ≠ ⊤)
    (h : ∀ (φ : 𝓓(Ω, ℝ)) (i : ι), ‖∫ x in (Ω : Set E), fderiv ℝ φ x (b i) • u x ∂μ‖ₑ
      ≤ C i * eLpNorm φ q (μ.restrict (Ω : Set E))) :
    MemSobolev u 1 p Ω μ := by
  classical
  have : Finite ι := Module.Finite.finite_basis b
  have := Fintype.ofFinite ι
  have hp : 1 ≤ p := ENNReal.HolderConjugate.one_le p q
  choose w hw hwp using fun i ↦
    exists_hasWeakIteratedLineDerivOn_of_forall_enorm_integral_smul_fderiv_le hq hu (b i) (hC i)
      (h · i)
  refine MemSobolevMultiIndex.memSobolev (b := b) ⟨hu, fun α hα ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single (⟨α, hα⟩ : MultiIndexLE ι 1) with h0 | ⟨i, hi⟩
  · obtain rfl : α = 0 := congrArg Subtype.val h0
    exact ⟨u, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
      (hu.locallyIntegrableOn hp), hu⟩
  · obtain rfl : α = Pi.single i 1 := congrArg Subtype.val hi
    exact ⟨w i, (hw i).of_perm (multiIndexTuple_single_perm (b : ι → E) i).symm, hwp i⟩

/-- **Proposition 9.3**, (ii) $\Rightarrow$ (i). Let $E$ be a finite-dimensional real normed space
with an additive Haar measure $\mu$, let $\Omega \subseteq E$ be open, and let
$p, q \in [1, \infty]$ be Hölder conjugate with $q < \infty$, that is, $1 < p \le \infty$. Let
$u \in L^p(\Omega)$ be real-valued, and let $C < \infty$ with
$$\Big| \int_\Omega \partial_y \varphi \, u \, d\mu \Big| \le C \|y\| \,
  \|\varphi\|_{L^q(\Omega)}$$
for every test function $\varphi \in \mathcal{D}(\Omega)$ and every $y \in E$. Then
$u \in W^{1,p}(\Omega)$.

This is Proposition 9.3, (ii) $\Rightarrow$ (i), of [brezis2011functional], in a form without a
choice of directions. It is the converse of `HasWeakFDerivOn.abs_integral_smul_fderiv_le`, and
it follows from `MemSobolev.of_forall_enorm_integral_smul_fderiv_basis_le`. The conclusion is
membership in $W^{1,p}(\Omega)$; the weak derivative itself is given by
`MemSobolev.exists_hasWeakFDerivOn`. -/
theorem HasWeakFDerivOn.of_forall_abs_integral_smul_fderiv_le [ENNReal.HolderConjugate p q]
    (hq : q ≠ ⊤) (hu : MemLp u p (μ.restrict (Ω : Set E))) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∀ (φ : 𝓓(Ω, ℝ)) (y : E), ‖∫ x in (Ω : Set E), fderiv ℝ φ x y • u x ∂μ‖ₑ
      ≤ C * ‖y‖ₑ * eLpNorm φ q (μ.restrict (Ω : Set E))) :
    MemSobolev u 1 p Ω μ :=
  MemSobolev.of_forall_enorm_integral_smul_fderiv_basis_le hq hu (Module.finBasis ℝ E)
    (C := fun i ↦ C * ‖Module.finBasis ℝ E i‖ₑ) (fun _ ↦ ENNReal.mul_ne_top hC enorm_ne_top)
    fun φ i ↦ h φ (Module.finBasis ℝ E i)

/-- **Remark 4(i)** of [brezis2011functional], second sentence. Let $E$ be a finite-dimensional real
normed space with an additive Haar measure $\mu$, let $\Omega \subseteq E$ be open, and let
$p, q \in [1, \infty]$ be Hölder conjugate with $q < \infty$, that is, $1 < p \le \infty$. Let
$u_n \in L^p(\Omega)$ be real-valued functions with weak derivatives $w_n$ on $\Omega$ such that
$\|w_n\|_{L^p(\Omega)} \le M$ for all $n$, for some $M < \infty$. If $f \in L^p(\Omega)$ and
$u_n \to f$ in $L^p(\Omega)$, then $f \in W^{1,p}(\Omega)$.

This answers the "why?" of Remark 4(i) in Chapter 9 of the source. The bound (ii) of Proposition
9.3 holds for each $u_n$ with the constant $M$ (`HasWeakFDerivOn.abs_integral_smul_fderiv_le`),
passes to the limit by Hölder's inequality
(`MeasureTheory.tendsto_integral_mul_of_tendsto_eLpNorm`), and then (ii) $\Rightarrow$ (i)
applies to $f$. The first sentence of the remark, with convergent gradients, is
`hasWeakIteratedFDerivOn_of_tendsto_eLpNorm`. -/
theorem MemSobolev.of_tendsto_eLpNorm_of_eLpNorm_le [ENNReal.HolderConjugate p q] (hq : q ≠ ⊤)
    {u : ℕ → E → ℝ} {w : ℕ → E → E →L[ℝ] ℝ} {f : E → ℝ}
    (hu : ∀ n, MemLp (u n) p (μ.restrict (Ω : Set E))) (hw : ∀ n, HasWeakFDerivOn (u n) (w n) Ω μ)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hwM : ∀ n, eLpNorm (w n) p (μ.restrict (Ω : Set E)) ≤ M)
    (hf : MemLp f p (μ.restrict (Ω : Set E)))
    (hlim : Tendsto (fun n ↦ eLpNorm (u n - f) p (μ.restrict (Ω : Set E))) atTop (𝓝 0)) :
    MemSobolev f 1 p Ω μ := by
  refine HasWeakFDerivOn.of_forall_abs_integral_smul_fderiv_le hq hf hM fun φ y ↦ ?_
  have hφq : MemLp (fun x ↦ fderiv ℝ φ x y) q (μ.restrict (Ω : Set E)) :=
    ((φ.fderivApply y).memLp q μ).restrict _
  have hconv : Tendsto (fun n ↦ ∫ x in (Ω : Set E), fderiv ℝ φ x y • u n x ∂μ) atTop
      (𝓝 (∫ x in (Ω : Set E), fderiv ℝ φ x y • f x ∂μ)) := by
    simp only [smul_eq_mul]
    exact tendsto_integral_mul_of_tendsto_eLpNorm hu hf hφq hlim
  refine le_of_tendsto ((continuous_enorm.tendsto _).comp hconv) (Eventually.of_forall fun n ↦ ?_)
  calc ‖∫ x in (Ω : Set E), fderiv ℝ φ x y • u n x ∂μ‖ₑ
      ≤ ‖y‖ₑ * eLpNorm (w n) p (μ.restrict (Ω : Set E)) * eLpNorm φ q (μ.restrict (Ω : Set E)) :=
        (hw n).abs_integral_smul_fderiv_le φ y
    _ ≤ ‖y‖ₑ * M * eLpNorm φ q (μ.restrict (Ω : Set E)) := by gcongr; exact hwM n
    _ = M * ‖y‖ₑ * eLpNorm φ q (μ.restrict (Ω : Set E)) := by ring

end Riesz

/-! ### Proposition 9.3, (i) $\Rightarrow$ (iii): the translation estimate -/

section Translation

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → F}
  {w : E → E →L[ℝ] F} {p : ℝ≥0∞}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Let $\mu$ be an additive Haar measure on $E$, let $G \colon E \to [0, \infty]$, let $a \in E$,
and let $A, s \subseteq E$ be measurable with $x + a \in s$ for every $x \in A$. Then
$$\int_A G(x + a) \, d\mu(x) \le \int_s G \, d\mu.$$
-/
theorem MeasureTheory.lintegral_comp_add_right_restrict_le (G : E → ℝ≥0∞) (a : E) {A s : Set E}
    (hA : MeasurableSet A) (hs : MeasurableSet s) (hAs : ∀ x ∈ A, x + a ∈ s) :
    ∫⁻ x in A, G (x + a) ∂μ ≤ ∫⁻ y in s, G y ∂μ := by
  calc ∫⁻ x in A, G (x + a) ∂μ = ∫⁻ x, A.indicator (fun x ↦ G (x + a)) x ∂μ :=
        (lintegral_indicator hA _).symm
    _ ≤ ∫⁻ x, s.indicator G (x + a) ∂μ := by
        refine lintegral_mono fun x ↦ ?_
        by_cases hx : x ∈ A
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hAs x hx)]
        · rw [Set.indicator_of_notMem hx]; exact zero_le
    _ = ∫⁻ y, s.indicator G y ∂μ := lintegral_add_right_eq_self (s.indicator G) a
    _ = ∫⁻ y in s, G y ∂μ := lintegral_indicator hs _

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Let $\mu$ be an additive Haar measure on $E$, let $a \in E$, and let $A, s \subseteq E$ be
measurable with $x + a \in s$ for every $x \in A$. If $f$ is almost everywhere strongly
measurable on $s$, then $x \mapsto f(x + a)$ is almost everywhere strongly measurable on $A$. -/
theorem MeasureTheory.aestronglyMeasurable_comp_add_right_restrict {f : E → F} (a : E)
    {A s : Set E} (hA : MeasurableSet A) (hs : MeasurableSet s) (hAs : ∀ x ∈ A, x + a ∈ s)
    (hf : AEStronglyMeasurable f (μ.restrict s)) :
    AEStronglyMeasurable (fun x ↦ f (x + a)) (μ.restrict A) := by
  have h1 : AEStronglyMeasurable (s.indicator f) μ :=
    (aestronglyMeasurable_indicator_iff hs).2 hf
  have h2 : AEStronglyMeasurable (fun x ↦ s.indicator f (x + a)) μ :=
    h1.comp_measurePreserving (measurePreserving_add_right μ a)
  refine (h2.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [self_mem_ae_restrict hA] with x hx
  exact Set.indicator_of_mem (hAs x hx) f

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Let $\mu$ be an additive Haar measure on $E$, let $p < \infty$, let $a \in E$, and let
$A, s \subseteq E$ be measurable with $x + a \in s$ for every $x \in A$. If $f$ is almost
everywhere strongly measurable on $s$, then
$$\|f(\cdot + a)\|_{L^p(A)} \le \|f\|_{L^p(s)}.$$
-/
theorem MeasureTheory.eLpNorm_comp_add_right_restrict_le (hp' : p ≠ ⊤) {f : E → F} (a : E)
    {A s : Set E} (hA : MeasurableSet A) (hs : MeasurableSet s) (hAs : ∀ x ∈ A, x + a ∈ s)
    (hf : AEStronglyMeasurable f (μ.restrict s)) :
    eLpNorm (fun x ↦ f (x + a)) p (μ.restrict A) ≤ eLpNorm f p (μ.restrict s) := by
  have hfa : AEStronglyMeasurable (fun x ↦ f (x + a)) (μ.restrict A) :=
    aestronglyMeasurable_comp_add_right_restrict a hA hs hAs hf
  rcases eq_or_ne p 0 with rfl | hp₀
  · rw [eLpNorm_exponent_zero hfa]; exact zero_le
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp'
  refine (ENNReal.rpow_le_rpow_iff hP).1 ?_
  rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm hp₀ hp' hfa,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm hp₀ hp' hf]
  exact lintegral_comp_add_right_restrict_le (fun y ↦ ‖f y‖ₑ ^ p.toReal) a hA hs hAs

/-- The translation estimate for a $C^1$ function. Let $E$ be a finite-dimensional real normed space
with an additive Haar measure $\mu$, let $1 \le p < \infty$, and let $g \colon E \to F$ be
continuously differentiable. Let $A, s \subseteq E$ be measurable and $h \in E$ such that
$x + th \in s$ for every $x \in A$ and $t \in [0, 1]$. Then
$$\|g(\cdot + h) - g\|_{L^p(A)} \le \|h\| \, \|Dg\|_{L^p(s)}.$$

This is the smooth case of the proof of Proposition 9.3, (i) $\Rightarrow$ (iii), of
[brezis2011functional]. The proof uses the identity $g(x + h) - g(x) = \int_0^1 Dg(x + th)\, h
\, dt$, Jensen's inequality on $[0, 1]$, Fubini's theorem and the translation invariance of
$\mu$. -/
theorem ContDiff.eLpNorm_sub_translate_le {g : E → F} (hg : ContDiff ℝ 1 g) (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) {A s : Set E} (hA : MeasurableSet A) (hs : MeasurableSet s) (h : E)
    (hseg : ∀ x ∈ A, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ s) :
    eLpNorm (fun x ↦ g (x + h) - g x) p (μ.restrict A)
      ≤ ‖h‖ₑ * eLpNorm (fderiv ℝ g) p (μ.restrict s) := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp'
  have hP1 : (1 : ℝ) ≤ p.toReal := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hp' hp
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hgc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  set G : E → ℝ≥0∞ := fun y ↦ ‖fderiv ℝ g y‖ₑ ^ p.toReal with hGdef
  have hGc : Continuous G := ENNReal.continuous_rpow_const.comp (continuous_enorm.comp hgc)
  -- the pointwise estimate, by the fundamental theorem of calculus and Jensen
  have hpt : ∀ x, ‖g (x + h) - g x‖ₑ ^ p.toReal
      ≤ ‖h‖ₑ ^ p.toReal * ∫⁻ t in Ioc (0 : ℝ) 1, G (x + t • h) := by
    intro x
    have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ g (x + t • h)) (fderiv ℝ g (x + t • h) h) t := by
      intro t
      have := (hgd (x + t • h)).hasFDerivAt.comp_hasDerivAt t
        (((hasDerivAt_id t).smul_const h).const_add x)
      simpa [Function.comp_def] using this
    have hc : Continuous fun t : ℝ ↦ fderiv ℝ g (x + t • h) :=
      hgc.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hftc : g (x + h) - g x = ∫ t in (0 : ℝ)..1, fderiv ℝ g (x + t • h) h := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
        ((hc.clm_apply continuous_const).intervalIntegrable _ _)]
      simp
    have hmeasG : AEMeasurable (fun t : ℝ ↦ ‖fderiv ℝ g (x + t • h)‖ₑ * ‖h‖ₑ)
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (hc.measurable.enorm.mul_const _).aemeasurable
    calc ‖g (x + h) - g x‖ₑ ^ p.toReal
        = ‖∫ t in Ioc (0 : ℝ) 1, fderiv ℝ g (x + t • h) h‖ₑ ^ p.toReal := by
          rw [hftc, intervalIntegral.integral_of_le zero_le_one]
      _ ≤ (∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ g (x + t • h)‖ₑ * ‖h‖ₑ) ^ p.toReal := by
          gcongr
          refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t ↦ ?_)
          exact (fderiv ℝ g (x + t • h)).le_opENorm h
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, (‖fderiv ℝ g (x + t • h)‖ₑ * ‖h‖ₑ) ^ p.toReal := by
          have := ENNReal.rpow_lintegral_mul_le hP1 (μ := volume.restrict (Ioc (0 : ℝ) 1))
            (w := fun _ ↦ 1) aemeasurable_const hmeasG
          simpa [Real.volume_Ioc] using this
      _ = ‖h‖ₑ ^ p.toReal * ∫⁻ t in Ioc (0 : ℝ) 1, G (x + t • h) := by
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hP.le, hGdef]
          rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hP.le enorm_ne_top),
            mul_comm]
  -- integrate over `A`, exchange the integrals, translate
  have hcont : Continuous fun z : E × ℝ ↦ G (z.1 + z.2 • h) :=
    hGc.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hswap : ∫⁻ x in A, (∫⁻ t in Ioc (0 : ℝ) 1, G (x + t • h)) ∂μ
      = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in A, G (x + t • h) ∂μ :=
    lintegral_lintegral_swap hcont.measurable.aemeasurable
  have hinner : ∀ t ∈ Icc (0 : ℝ) 1, ∫⁻ x in A, G (x + t • h) ∂μ ≤ ∫⁻ y in s, G y ∂μ :=
    fun t ht ↦ lintegral_comp_add_right_restrict_le G (t • h) hA hs fun x hx ↦ hseg x hx t ht
  have hmeas₁ : AEStronglyMeasurable (fun x ↦ g (x + h) - g x) (μ.restrict A) :=
    ((hg.continuous.comp (continuous_id.add continuous_const)).sub hg.continuous)
      |>.aestronglyMeasurable
  refine (ENNReal.rpow_le_rpow_iff hP).1 ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hP.le, ← lintegral_rpow_enorm_eq_rpow_eLpNorm hp₀ hp' hmeas₁,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm hp₀ hp' hgc.aestronglyMeasurable]
  calc ∫⁻ x in A, ‖g (x + h) - g x‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x in A, (‖h‖ₑ ^ p.toReal * ∫⁻ t in Ioc (0 : ℝ) 1, G (x + t • h)) ∂μ :=
        lintegral_mono hpt
    _ = ‖h‖ₑ ^ p.toReal * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in A, G (x + t • h) ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hP.le enorm_ne_top), hswap]
    _ ≤ ‖h‖ₑ ^ p.toReal * ∫⁻ _t in Ioc (0 : ℝ) 1, ∫⁻ y in s, G y ∂μ := by
        exact mul_le_mul' le_rfl
          (setLIntegral_mono measurable_const fun t ht ↦ hinner t (Ioc_subset_Icc_self ht))
    _ = ‖h‖ₑ ^ p.toReal * ∫⁻ y in s, G y ∂μ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]


/-- **Proposition 9.3**, (i) $\Rightarrow$ (iii), the translation estimate. Let $E$ be a
finite-dimensional real normed space with an additive Haar measure $\mu$, let
$\Omega \subseteq E$ be open, and let $1 \le p < \infty$. Let $w$ be a weak derivative of
$u \colon E \to F$ on $\Omega$ with $u, w \in L^p(\Omega)$. Let $V \subseteq E$ be open and
$a \in E$ such that $x + ta \in \Omega$ for every $x \in V$ and $t \in [0, 1]$. Then
$$\|u(\cdot + a) - u\|_{L^p(V)} \le \|a\| \, \|w\|_{L^p(\Omega)}.$$

This is Proposition 9.3, (i) $\Rightarrow$ (iii), of [brezis2011functional]. The condition on
the segments replaces the condition $|h| < \operatorname{dist}(\omega, \partial\Omega)$ of the
source. The proof follows the source, with the local approximation in place of Theorem 9.2. On a
relatively compact piece $U$ of $V$, the segments sweep out a compact subset of $\Omega$; on an
open neighbourhood $W$ of this subset, `MemSobolev.exists_seq_contDiff_tendsto_eLpNorm` gives
smooth $g_i \to u$ with $\nabla g_i \to w$ in $L^p(W)$. The smooth estimate
`ContDiff.eLpNorm_sub_translate_le` on $U$ passes to the limit, and an exhaustion of $V$ by such
pieces finishes the proof (`MeasureTheory.eLpNorm_restrict_iUnion_le`). -/
theorem HasWeakFDerivOn.eLpNorm_sub_translate_le (h : HasWeakFDerivOn u w Ω μ)
    (hu : MemLp u p (μ.restrict (Ω : Set E))) (hw : MemLp w p (μ.restrict (Ω : Set E)))
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) {V : Set E} (hV : IsOpen V) (a : E)
    (hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + t • a ∈ (Ω : Set E)) :
    eLpNorm (fun x ↦ u (x + a) - u x) p (μ.restrict V)
      ≤ ‖a‖ₑ * eLpNorm w p (μ.restrict (Ω : Set E)) := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hf : MemSobolev u 1 p Ω μ := h.memSobolev hu hw
  -- an exhaustion of `V`
  obtain ⟨U, hUc, hUsucc, hUV⟩ := (⟨V, hV⟩ : Opens E).exists_exhaustion
  have hUmono : Monotone fun n ↦ (U n : Set E) :=
    monotone_nat_of_le_succ fun n ↦ subset_closure.trans (hUsucc n)
  have hUV' : ∀ n, (U n : Set E) ⊆ V := fun n ↦ by
    have := Set.subset_iUnion (fun n ↦ (U n : Set E)) n
    rwa [hUV] at this
  rw [show V = ⋃ n, (U n : Set E) from hUV.symm]
  refine eLpNorm_restrict_iUnion_le hUmono.directed_le hp₀ hp' fun n ↦ ?_
  have hKV : closure (U n : Set E) ⊆ V := (hUsucc n).trans (hUV' (n + 1))
  -- the compact set swept out by the segments, and an open neighbourhood of it in `Ω`
  obtain ⟨K, hKdef⟩ : ∃ K : Set E,
      K = (fun z : E × ℝ ↦ z.1 + z.2 • a) '' (closure (U n : Set E) ×ˢ Icc (0 : ℝ) 1) := ⟨_, rfl⟩
  have hKc : IsCompact K := hKdef ▸
    ((hUc n).prod isCompact_Icc).image (continuous_fst.add (continuous_snd.smul continuous_const))
  have hKΩ : K ⊆ (Ω : Set E) := by
    rw [hKdef]
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact hseg x (hKV hx) t ht
  obtain ⟨W, -, hWo, hKW, -, hWc, hWΩ, -⟩ := hKc.exists_pos_forall_closedBall_subset Ω.isOpen hKΩ
  have hUW : ∀ x ∈ (U n : Set E), ∀ t ∈ Icc (0 : ℝ) 1, x + t • a ∈ W := fun x hx t ht ↦
    hKW (hKdef ▸ ⟨(x, t), ⟨subset_closure hx, ht⟩, rfl⟩)
  have hUnW : (U n : Set E) ⊆ W := fun x hx ↦ by
    simpa using hUW x hx 0 ⟨le_rfl, zero_le_one⟩
  have hUaW : ∀ x ∈ (U n : Set E), x + a ∈ W := fun x hx ↦ by
    simpa using hUW x hx 1 ⟨zero_le_one, le_rfl⟩
  have hWm : MeasurableSet W := hWo.measurableSet
  have hUm : MeasurableSet (U n : Set E) := (U n).isOpen.measurableSet
  have hWΩ' : W ⊆ (Ω : Set E) := subset_closure.trans hWΩ
  have huW : AEStronglyMeasurable u (μ.restrict W) :=
    hu.aestronglyMeasurable.mono_measure (Measure.restrict_mono hWΩ' le_rfl)
  have hwW : AEStronglyMeasurable w (μ.restrict W) :=
    hw.aestronglyMeasurable.mono_measure (Measure.restrict_mono hWΩ' le_rfl)
  -- smooth approximation on `W`
  obtain ⟨g, hgs, hgt, hgd⟩ := hf.exists_seq_contDiff_tendsto_eLpNorm hp hp' hWo hWc hWΩ
  have hgd' : Tendsto (fun i ↦ eLpNorm (fun x ↦ fderiv ℝ (g i) x - w x) p (μ.restrict W)) atTop
      (𝓝 0) := by
    refine (hgd 1 le_rfl).congr fun i ↦ ?_
    refine eLpNorm_congr_norm_ae
      (((hgs i).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable.sub
        ((hf.memLp_weakIteratedFDeriv le_rfl).aestronglyMeasurable.mono_measure
          (Measure.restrict_mono hWΩ' le_rfl)))
      (((hgs i).continuous_fderiv (by simp)).aestronglyMeasurable.sub hwW) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWΩ'
      ((ae_restrict_iff' hΩm).2 h.weakIteratedFDeriv_ae_eq)] with x hx
    rw [Pi.sub_apply, hx, iteratedFDeriv_one_eq_symm_fderiv, ← map_sub,
      LinearIsometryEquiv.norm_map]
  -- the estimate for the approximants, and the limit
  have key : ∀ i, eLpNorm (fun x ↦ u (x + a) - u x) p (μ.restrict (U n : Set E))
      ≤ eLpNorm (u - g i) p (μ.restrict W)
        + ‖a‖ₑ * (eLpNorm (fun x ↦ fderiv ℝ (g i) x - w x) p (μ.restrict W)
          + eLpNorm w p (μ.restrict W))
        + eLpNorm (g i - u) p (μ.restrict W) := by
    intro i
    obtain ⟨A, hAdef⟩ : ∃ A : E → F, A = fun x ↦ (u - g i) (x + a) := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B : E → F, B = fun x ↦ g i (x + a) - g i x := ⟨_, rfl⟩
    obtain ⟨C, hCdef⟩ : ∃ C : E → F, C = g i - u := ⟨_, rfl⟩
    have hsplit : (fun x ↦ u (x + a) - u x) = A + B + C := by
      funext x
      simp only [hAdef, hBdef, hCdef, Pi.add_apply, Pi.sub_apply]
      abel
    obtain ⟨D, hDdef⟩ : ∃ D : E → E →L[ℝ] F, D = fun x ↦ fderiv ℝ (g i) x - w x := ⟨_, rfl⟩
    have hgrad : eLpNorm (fderiv ℝ (g i)) p (μ.restrict W)
        ≤ eLpNorm D p (μ.restrict W) + eLpNorm w p (μ.restrict W) := by
      refine le_of_eq_of_le ?_ (eLpNorm_add_le_of_norm hp)
      congr 1
      funext x
      simp [hDdef]
    have h1a : eLpNorm (A + B + C) p (μ.restrict (U n : Set E))
        ≤ eLpNorm (A + B) p (μ.restrict (U n : Set E)) + eLpNorm C p (μ.restrict (U n : Set E)) :=
      eLpNorm_add_le_of_norm hp
    have h1b : eLpNorm (A + B) p (μ.restrict (U n : Set E))
        ≤ eLpNorm A p (μ.restrict (U n : Set E)) + eLpNorm B p (μ.restrict (U n : Set E)) :=
      eLpNorm_add_le_of_norm hp
    have h1 : eLpNorm (A + B + C) p (μ.restrict (U n : Set E))
        ≤ eLpNorm A p (μ.restrict (U n : Set E)) + eLpNorm B p (μ.restrict (U n : Set E))
          + eLpNorm C p (μ.restrict (U n : Set E)) :=
      h1a.trans (add_le_add h1b le_rfl)
    have h2 : eLpNorm A p (μ.restrict (U n : Set E)) ≤ eLpNorm (u - g i) p (μ.restrict W) := by
      rw [hAdef]
      exact eLpNorm_comp_add_right_restrict_le hp' a hUm hWm hUaW
        (huW.sub (hgs i).continuous.aestronglyMeasurable)
    have h3 : eLpNorm B p (μ.restrict (U n : Set E))
        ≤ ‖a‖ₑ * eLpNorm (fderiv ℝ (g i)) p (μ.restrict W) := by
      rw [hBdef]
      exact ((hgs i).of_le (by simp)).eLpNorm_sub_translate_le hp hp' hUm hWm a hUW
    have h4 : eLpNorm C p (μ.restrict (U n : Set E)) ≤ eLpNorm (g i - u) p (μ.restrict W) := by
      rw [hCdef]
      exact eLpNorm_mono_measure _ (Measure.restrict_mono hUnW le_rfl)
    rw [hsplit, ← hDdef]
    calc eLpNorm (A + B + C) p (μ.restrict (U n : Set E))
        ≤ eLpNorm A p (μ.restrict (U n : Set E)) + eLpNorm B p (μ.restrict (U n : Set E))
          + eLpNorm C p (μ.restrict (U n : Set E)) := h1
      _ ≤ eLpNorm (u - g i) p (μ.restrict W)
          + ‖a‖ₑ * eLpNorm (fderiv ℝ (g i)) p (μ.restrict W)
          + eLpNorm (g i - u) p (μ.restrict W) := add_le_add (add_le_add h2 h3) h4
      _ ≤ eLpNorm (u - g i) p (μ.restrict W)
          + ‖a‖ₑ * (eLpNorm D p (μ.restrict W) + eLpNorm w p (μ.restrict W))
          + eLpNorm (g i - u) p (μ.restrict W) :=
        add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hgrad)) le_rfl
  have hgt' : Tendsto (fun i ↦ eLpNorm (u - g i) p (μ.restrict W)) atTop (𝓝 0) := by
    simpa only [eLpNorm_sub_comm] using hgt
  have hlim : Tendsto (fun i ↦ eLpNorm (u - g i) p (μ.restrict W)
      + ‖a‖ₑ * (eLpNorm (fun x ↦ fderiv ℝ (g i) x - w x) p (μ.restrict W)
        + eLpNorm w p (μ.restrict W))
      + eLpNorm (g i - u) p (μ.restrict W)) atTop
      (𝓝 (0 + ‖a‖ₑ * (0 + eLpNorm w p (μ.restrict W)) + 0)) :=
    (hgt'.add (ENNReal.Tendsto.const_mul (hgd'.add tendsto_const_nhds)
      (Or.inr enorm_ne_top))).add hgt
  refine (ge_of_tendsto' hlim key).trans ?_
  simp only [zero_add, add_zero]
  exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono hWΩ' le_rfl))

/-- **Proposition 9.3**, (i) $\Rightarrow$ (iii), on the whole space. Let $E$ be a
finite-dimensional real normed space with an additive Haar measure $\mu$, and let
$1 \le p < \infty$. If $w$ is a weak derivative of $u \colon E \to F$ on $E$ with
$u, w \in L^p(E)$, then for every $a \in E$
$$\|u(\cdot + a) - u\|_{L^p} \le \|a\| \, \|w\|_{L^p}.$$

This is the case $V = \Omega = E$ of `HasWeakFDerivOn.eLpNorm_sub_translate_le`, in which every
segment stays in $\Omega$. -/
theorem HasWeakFDerivOn.eLpNorm_sub_translate_le_univ (h : HasWeakFDerivOn u w ⊤ μ)
    (hu : MemLp u p μ) (hw : MemLp w p μ) (hp : 1 ≤ p) (hp' : p ≠ ⊤) (a : E) :
    eLpNorm (fun x ↦ u (x + a) - u x) p μ ≤ ‖a‖ₑ * eLpNorm w p μ := by
  have := h.eLpNorm_sub_translate_le (by simpa using hu) (by simpa using hw) hp hp' isOpen_univ a
    (fun _ _ _ _ ↦ by simp)
  simpa using this

/-- **Proposition 9.3**, (i) $\Rightarrow$ (iii), for $W^{1,p}(E)$. Let $E$ be a finite-dimensional
real normed space with an additive Haar measure $\mu$, and let $1 \le p < \infty$. For
$u \in W^{1,p}(E; F)$ and every $a \in E$,
$$\|u(\cdot + a) - u\|_{L^p} \le \|a\| \, \|\nabla u\|_{L^p},$$
where $\nabla u$ is the chosen weak derivative `weakIteratedFDeriv 1 u ⊤ μ`.

This is the uniform translation estimate that the Kolmogorov–Riesz–Fréchet theorem needs for a
bounded set of $W^{1,p}$. -/
theorem MemSobolev.eLpNorm_sub_translate_le (hf : MemSobolev u 1 p ⊤ μ) (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) (a : E) :
    eLpNorm (fun x ↦ u (x + a) - u x) p μ ≤ ‖a‖ₑ * eLpNorm (weakIteratedFDeriv 1 u ⊤ μ) p μ := by
  obtain ⟨w, hw, hwp⟩ := hf.exists_hasWeakFDerivOn
  rw [Measure.restrict_coe_top] at hwp
  refine (hw.eLpNorm_sub_translate_le_univ hf.memLp_top hwp hp hp' a).trans (le_of_eq ?_)
  congr 1
  refine eLpNorm_congr_norm_ae hwp.aestronglyMeasurable
    (by simpa using (hf.memLp_weakIteratedFDeriv le_rfl).aestronglyMeasurable) ?_
  filter_upwards [hw.weakIteratedFDeriv_ae_eq] with x hx
  rw [hx (by simp), LinearIsometryEquiv.norm_map]

end Translation

/-! ### The translation estimate on $W^{1,p}(\mathbb{R}^N)$ -/

section Euclidean

open SobolevMultiIndex

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let $G$ be a real normed space. The operator norm of a continuous linear map
$L \colon \mathbb{R}^N \to G$ on the Euclidean space is at most the sum of the norms of its
values on the standard basis vectors:
$$\|L\| \le \sum_{i} \|L e_i\|.$$
-/
theorem ContinuousLinearMap.norm_le_sum_norm_apply_single {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : EuclideanSpace ℝ (Fin N) →L[ℝ] G) :
    ‖L‖ ≤ ∑ i, ‖L (EuclideanSpace.single i 1)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) fun z ↦ ?_
  have hz : z = ∑ i, z i • EuclideanSpace.single i 1 := by
    have := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr z
    simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using this.symm
  calc ‖L z‖ = ‖∑ i, z i • L (EuclideanSpace.single i 1)‖ := by
        conv_lhs => rw [hz, map_sum]
        simp only [map_smul]
    _ ≤ ∑ i, ‖z i • L (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖z‖ * ‖L (EuclideanSpace.single i 1)‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le z i) (norm_nonneg _)
    _ = (∑ i, ‖L (EuclideanSpace.single i 1)‖) * ‖z‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- Let $1 \le p \le \infty$ and $u \in W^{1,p}(\mathbb{R}^N)$. If $w$ is a weak derivative of $u$
on $\mathbb{R}^N$, then
$$\|w\|_{L^p} \le \sum_{i=1}^N \|\partial_i u\|_{L^p}.$$

Here $\partial_i u$ is the weak partial derivative `SobolevMultiIndex.weakDeriv u
(MultiIndexLE.single i)`. The proof bounds the operator norm of $w(x)$ by the sum of the norms
of its values on the standard basis (`ContinuousLinearMap.norm_le_sum_norm_apply_single`). -/
theorem SobolevEuclidean.eLpNorm_le_sum_of_hasWeakFDerivOn (u : SobolevEuclidean N 1 p ⊤)
    {w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hw : HasWeakFDerivOn (fn u) w ⊤ volume) :
    eLpNorm w p volume ≤ ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ := by
  classical
  have hp : 1 ≤ p := Fact.out
  have hwm : AEStronglyMeasurable w volume :=
    (locallyIntegrableOn_univ.1 (by simpa using hw.locallyIntegrableOn_weakDeriv)
      |>.aestronglyMeasurable)
  -- the components of `w` are the partial derivatives
  have hcomp : ∀ i, (fun x ↦ w x (EuclideanSpace.single i 1))
      =ᵐ[volume] weakDeriv u (MultiIndexLE.single i) := by
    intro i
    have h1 := (hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis :
        Fin N → EuclideanSpace ℝ (Fin N)) i)
    have h2 : HasWeakIteratedLineDerivOn ![EuclideanSpace.single i 1] (fn u)
        (fun x ↦ w x (EuclideanSpace.single i 1)) ⊤ volume := by
      have := HasWeakIteratedFDerivOn.lineDeriv hw ![EuclideanSpace.single i 1]
      simpa using this
    have h3 := HasWeakIteratedLineDerivOn.ae_eq h2 (by simpa using h1)
    filter_upwards [h3] with x hx
    exact hx (by simp)
  -- the pointwise bound, almost everywhere
  have hbound : ∀ᵐ x ∂volume, ‖w x‖ ≤ ‖∑ i, ‖weakDeriv u (MultiIndexLE.single i) x‖‖ := by
    have hall : ∀ᵐ x ∂volume, ∀ i, w x (EuclideanSpace.single i 1)
        = weakDeriv u (MultiIndexLE.single i) x := ae_all_iff.2 hcomp
    filter_upwards [hall] with x hx
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    refine (w x).norm_le_sum_norm_apply_single.trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hx i]
  calc eLpNorm w p volume
      ≤ eLpNorm (fun x ↦ ∑ i, ‖weakDeriv u (MultiIndexLE.single i) x‖) p volume :=
        eLpNorm_mono_ae hwm hbound
    _ = eLpNorm (∑ i, fun x ↦ ‖weakDeriv u (MultiIndexLE.single i) x‖) p volume := by
        congr 1
        funext x
        simp only [Finset.sum_apply]
    _ ≤ ∑ i, eLpNorm (fun x ↦ ‖weakDeriv u (MultiIndexLE.single i) x‖) p volume :=
        eLpNorm_sum_le_of_norm hp
    _ = ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hm : AEStronglyMeasurable (weakDeriv u (MultiIndexLE.single i) : _ → ℝ) volume := by
          simpa only [Measure.restrict_coe_top] using
            Lp.aestronglyMeasurable (weakDeriv u (MultiIndexLE.single i))
        rw [eLpNorm_norm _ hm, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
          eLpNorm_restrict_coe_top]

/-- **Proposition 9.3**, (i) $\Rightarrow$ (iii), on $W^{1,p}(\mathbb{R}^N)$. Let $1 \le p < \infty$
and $u \in W^{1,p}(\mathbb{R}^N)$. Then for every $a \in \mathbb{R}^N$
$$\|u(\cdot + a) - u\|_{L^p} \le \|a\| \sum_{i=1}^N \|\partial_i u\|_{L^p}.$$

This is the estimate $\|\tau_h u - u\|_{L^p(\mathbb{R}^N)} \le |h| \, \|\nabla
u\|_{L^p(\mathbb{R}^N)}$ of [brezis2011functional], with the gradient measured by the $\ell^1$
sum of its components; the operator norm of the derivative is at most this sum
(`ContinuousLinearMap.norm_le_sum_norm_apply_single`). It is the uniform translation estimate
that the Kolmogorov–Riesz–Fréchet theorem needs for a bounded set of $W^{1,p}(\mathbb{R}^N)$.
The form with the gradient norm is `SobolevEuclidean.eLpNorm_fn_sub_translate_le_gradNorm`. -/
theorem SobolevEuclidean.eLpNorm_fn_sub_translate_le (hp' : p ≠ ⊤) (u : SobolevEuclidean N 1 p ⊤)
    (a : EuclideanSpace ℝ (Fin N)) :
    eLpNorm (fun x ↦ fn u (x + a) - fn u x) p volume
      ≤ ‖a‖ₑ * ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖ := by
  classical
  have hp : 1 ≤ p := Fact.out
  have hf : MemSobolev (fn u) 1 p ⊤ volume := (memSobolevMultiIndex u).memSobolev
  obtain ⟨w, hw, hwp⟩ := hf.exists_hasWeakFDerivOn
  rw [Measure.restrict_coe_top] at hwp
  refine (hw.eLpNorm_sub_translate_le_univ hf.memLp_top hwp hp hp' a).trans
    (mul_le_mul' le_rfl ?_)
  exact SobolevEuclidean.eLpNorm_le_sum_of_hasWeakFDerivOn u hw

/-- **Proposition 9.3**, (i) $\Rightarrow$ (iii), on $W^{1,p}(\mathbb{R}^N)$, with the gradient
norm. Let $1 \le p < \infty$ and $u \in W^{1,p}(\mathbb{R}^N)$. Then for every
$a \in \mathbb{R}^N$
$$\|u(\cdot + a) - u\|_{L^p} \le N \, \|a\| \, \|\nabla u\|,$$
where $\|\nabla u\| = (\sum_i \|\partial_i u\|_{L^p}^p)^{1/p}$ is
`SobolevMultiIndex.gradNorm u`.

The factor $N$ comes from the comparison of the $\ell^1$ sum of the components with their
$\ell^p$ norm. -/
theorem SobolevEuclidean.eLpNorm_fn_sub_translate_le_gradNorm (hp' : p ≠ ⊤)
    (u : SobolevEuclidean N 1 p ⊤) (a : EuclideanSpace ℝ (Fin N)) :
    eLpNorm (fun x ↦ fn u (x + a) - fn u x) p volume
      ≤ N * ‖a‖ₑ * ENNReal.ofReal (gradNorm u) := by
  refine (SobolevEuclidean.eLpNorm_fn_sub_translate_le hp' u a).trans ?_
  calc ‖a‖ₑ * ∑ i, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single i)‖
      ≤ ‖a‖ₑ * ∑ _i : Fin N, ENNReal.ofReal (gradNorm u) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ ↦
          ENNReal.ofReal_le_ofReal (norm_weakDeriv_single_le_gradNorm u i))
    _ = N * ‖a‖ₑ * ENNReal.ofReal (gradNorm u) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Euclidean

/-! ### Proposition 9.3, (iii) $\Rightarrow$ (ii) -/

section DifferenceQuotient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → F} {p q : ℝ≥0∞}

/-- **Proposition 9.3**, (iii) $\Rightarrow$ (ii), for small translations. Let $E$ be a
finite-dimensional real normed space with an additive Haar measure $\mu$, let
$\Omega \subseteq E$ be open, and let $p, q \in [1, \infty]$ be Hölder conjugate. Let
$u \in L^p(\Omega; F)$ and $C \in [0, \infty]$. Assume that for every open $V$ whose closure is
compact and contained in $\Omega$ there is $\delta > 0$ such that
$$\|u(\cdot + a) - u\|_{L^p(V)} \le C \|a\| \quad \text{for all } a \in E \text{ with } \|a\| <
  \delta.$$
Then for every test function $\varphi \in \mathcal{D}(\Omega)$ and every $y \in E$,
$$\Big\| \int_\Omega \partial_y \varphi \, u \, d\mu \Big\| \le C \|y\| \,
  \|\varphi\|_{L^q(\Omega)}.$$

This is Proposition 9.3, (iii) $\Rightarrow$ (ii), of [brezis2011functional], for any
$1 \le p \le \infty$. The radius $\delta$ plays the role of
$\operatorname{dist}(\omega, \partial\Omega)$ in the source. With
$V \supseteq \operatorname{supp} \varphi$, the change of variables $\int_\Omega (u(\cdot + ty) -
u) \varphi = \int_\Omega u (\varphi(\cdot - ty) - \varphi)$ and Hölder's inequality bound the
difference quotients $\int_\Omega u (\varphi(\cdot - ty) - \varphi)/t$ by
$C \|y\| \|\varphi\|_{L^q}$ for small $t$. As $t \to 0$ they converge to
$-\int_\Omega u \, \partial_y \varphi$ by dominated convergence. -/
theorem abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le_of_norm_lt
    [ENNReal.HolderConjugate p q] (hu : MemLp u p (μ.restrict (Ω : Set E))) {C : ℝ≥0∞}
    (h : ∀ V : Set E, IsOpen V → IsCompact (closure V) → closure V ⊆ (Ω : Set E) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ a : E, ‖a‖ < δ →
        eLpNorm (fun x ↦ u (x + a) - u x) p (μ.restrict V) ≤ C * ‖a‖ₑ)
    (φ : 𝓓(Ω, ℝ)) (y : E) :
    ‖∫ x in (Ω : Set E), fderiv ℝ φ x y • u x ∂μ‖ₑ
      ≤ C * ‖y‖ₑ * eLpNorm φ q (μ.restrict (Ω : Set E)) := by
  have hp : 1 ≤ p := ENNReal.HolderConjugate.one_le p q
  have huloc : LocallyIntegrableOn u Ω μ := hu.locallyIntegrableOn hp
  -- two relatively compact open neighbourhoods of the support of `φ`
  obtain ⟨W, -, hWo, hφW, -, hWc, hWΩ, -⟩ :=
    φ.hasCompactSupport.exists_pos_forall_closedBall_subset Ω.isOpen φ.tsupport_subset
  obtain ⟨V, ε, hVo, hφV, hε, hVc, hVW, hVball⟩ :=
    φ.hasCompactSupport.exists_pos_forall_closedBall_subset hWo hφW
  have hVΩ : closure V ⊆ (Ω : Set E) := hVW.trans (subset_closure.trans hWΩ)
  have hWΩ' : W ⊆ (Ω : Set E) := subset_closure.trans hWΩ
  -- the translation estimate on `V`, for translations of norm `< δ₀`
  obtain ⟨δ₀, hδ₀, hV⟩ := h V hVo hVc hVΩ
  -- the translated test function is supported in `W` for small translations
  have hsupp : ∀ a : E, ‖a‖ ≤ ε → ∀ x, x ∉ W → (φ : E → ℝ) (x - a) = 0 := by
    intro a ha x hx
    by_contra hne
    have hmem : x - a ∈ tsupport φ := subset_tsupport _ hne
    refine hx (hVball (x - a) (hφV hmem) ?_)
    simpa [mem_closedBall, dist_eq_norm, norm_neg] using ha
  -- a bound on the gradient of `φ`
  obtain ⟨M, hM⟩ := (φ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (φ.contDiff.continuous_fderiv (by simp))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hlip : ∀ x z : E, ‖(φ : E → ℝ) z - φ x‖ ≤ M * ‖z - x‖ := fun x z ↦
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun _ _ ↦ (φ.contDiff.differentiable
      (by simp)).differentiableAt) (fun x _ ↦ hM x) convex_univ (mem_univ x) (mem_univ z)
  -- the difference quotients and their bound
  set Q : ℝ → E → ℝ := fun t x ↦ t⁻¹ * ((φ : E → ℝ) (x - t • y) - φ x) with hQdef
  have hQbound : ∀ t : ℝ, t ≠ 0 → ‖t • y‖ ≤ ε → ‖t • y‖ < δ₀ →
      ‖∫ x in (Ω : Set E), Q t x • u x ∂μ‖ₑ
        ≤ C * ‖y‖ₑ * eLpNorm φ q (μ.restrict (Ω : Set E)) := by
    intro t ht hty htδ
    have htrans := hV (t • y) htδ
    -- the change of variables
    have h1 : Integrable (fun x ↦ (φ : E → ℝ) (x - t • y) • u x) μ := by
      refine LocallyIntegrableOn.integrable_smul_left_of_tsupport_subset huloc
        (φ.continuous.comp (continuous_id.sub continuous_const))
        (φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight (t • y))) ?_
      refine (closure_minimal (fun x hx ↦ ?_) hWc.isClosed).trans hWΩ
      by_contra hxW
      exact hx (hsupp (t • y) hty x fun hw ↦ hxW (subset_closure hw))
    have h2 : Integrable (fun x ↦ (φ : E → ℝ) x • u x) μ := φ.integrable_smul huloc
    have h4 : Integrable (fun x ↦ (φ : E → ℝ) x • u (x + t • y)) μ := by
      have := (measurePreserving_add_right μ (t • y)).integrable_comp_of_integrable h1
      simpa [Function.comp_def, add_sub_cancel_right] using this
    have h3 : ∫ x in (Ω : Set E), (φ : E → ℝ) (x - t • y) • u x ∂μ
        = ∫ x in (Ω : Set E), (φ : E → ℝ) x • u (x + t • y) ∂μ := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          rw [hsupp (t • y) hty x fun hxW ↦ hx (hWΩ' hxW), zero_smul],
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          rw [φ.eq_zero_of_notMem hx, zero_smul],
        ← integral_add_right_eq_self (fun x ↦ (φ : E → ℝ) (x - t • y) • u x) (t • y)]
      simp only [add_sub_cancel_right]
    have hI : ∫ x in (Ω : Set E), ((φ : E → ℝ) (x - t • y) - φ x) • u x ∂μ
        = ∫ x in (Ω : Set E), (φ : E → ℝ) x • (u (x + t • y) - u x) ∂μ := by
      simp only [sub_smul, smul_sub]
      rw [integral_sub h1.integrableOn h2.integrableOn, integral_sub h4.integrableOn
        h2.integrableOn, h3]
    -- Hölder's inequality on `V`, then the hypothesis
    have hV' : ∫ x in (Ω : Set E), (φ : E → ℝ) x • (u (x + t • y) - u x) ∂μ
        = ∫ x in V, (φ : E → ℝ) x • (u (x + t • y) - u x) ∂μ := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          rw [φ.eq_zero_of_notMem hx, zero_smul],
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          rw [image_eq_zero_of_notMem_tsupport fun hm ↦ hx (hφV hm), zero_smul]]
    have hHolder : ‖∫ x in V, (φ : E → ℝ) x • (u (x + t • y) - u x) ∂μ‖ₑ
        ≤ eLpNorm φ q (μ.restrict (Ω : Set E)) * (C * ‖t • y‖ₑ) :=
      enorm_integral_smul_le_eLpNorm_mul_eLpNorm.trans
        (mul_le_mul' (eLpNorm_mono_measure _ (Measure.restrict_mono (subset_closure.trans hVΩ)
          le_rfl)) htrans)
    have ht0 : ‖t‖ₑ ≠ 0 := by simpa using ht
    calc ‖∫ x in (Ω : Set E), Q t x • u x ∂μ‖ₑ
        = ‖t⁻¹‖ₑ * ‖∫ x in (Ω : Set E), ((φ : E → ℝ) (x - t • y) - φ x) • u x ∂μ‖ₑ := by
          simp only [hQdef, mul_smul]
          rw [integral_smul, enorm_smul]
      _ ≤ ‖t⁻¹‖ₑ * (eLpNorm φ q (μ.restrict (Ω : Set E)) * (C * ‖t • y‖ₑ)) := by
          rw [hI, hV']
          exact mul_le_mul' le_rfl hHolder
      _ = (‖t‖ₑ⁻¹ * ‖t‖ₑ) * (C * ‖y‖ₑ * eLpNorm φ q (μ.restrict (Ω : Set E))) := by
          rw [enorm_inv ht, enorm_smul]
          ring
      _ = C * ‖y‖ₑ * eLpNorm φ q (μ.restrict (Ω : Set E)) := by
          rw [ENNReal.inv_mul_cancel ht0 enorm_ne_top, one_mul]
  -- the sequence of difference quotients, and its limit by dominated convergence
  set δ : ℝ := min ε (δ₀ / 2) / (‖y‖ + 1) with hδdef
  have hδ : 0 < δ := by positivity
  set t : ℕ → ℝ := fun n ↦ δ / (n + 1) with htdef
  have htpos : ∀ n, 0 < t n := fun n ↦ by positivity
  have htmin : ∀ n, ‖t n • y‖ ≤ min ε (δ₀ / 2) := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (htpos n)]
    have h1 : t n ≤ δ := by
      rw [htdef]
      exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have h2 : δ * ‖y‖ ≤ min ε (δ₀ / 2) := by
      rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg y, lt_min hε (half_pos hδ₀)]
    exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg y)).trans h2
  have htε : ∀ n, ‖t n • y‖ ≤ ε := fun n ↦ (htmin n).trans (min_le_left _ _)
  have htδ : ∀ n, ‖t n • y‖ < δ₀ := fun n ↦
    ((htmin n).trans (min_le_right _ _)).trans_lt (half_lt_self hδ₀)
  have ht0 : Tendsto t atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have ht0' : Tendsto t atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨ht0, Eventually.of_forall fun n ↦ (htpos n).ne'⟩
  set K : Set E := closure W with hKdef
  have hKm : MeasurableSet K := hWc.isClosed.measurableSet
  have hQcont : ∀ s : ℝ, Continuous (Q s) := fun s ↦
    continuous_const.mul ((φ.continuous.comp (continuous_id.sub continuous_const)).sub
      φ.continuous)
  have hlim : Tendsto (fun n ↦ ∫ x in (Ω : Set E), Q (t n) x • u x ∂μ) atTop
      (𝓝 (∫ x in (Ω : Set E), (-(fderiv ℝ φ x y)) • u x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ M * ‖y‖ * ‖K.indicator u x‖)
      (fun n ↦ (hQcont (t n)).aestronglyMeasurable.smul hu.aestronglyMeasurable) ?_
      (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · exact (((integrable_indicator_iff hKm).2 (huloc.integrableOn_compact_subset hWΩ hWc)).norm
        |>.const_mul _).mono_measure Measure.restrict_le_self
    · -- the domination
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, norm_smul, hQdef]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        simp only [Real.norm_eq_abs, abs_mul, abs_inv]
        calc |t n|⁻¹ * |(φ : E → ℝ) (x - t n • y) - φ x|
            ≤ |t n|⁻¹ * (M * ‖x - t n • y - x‖) :=
              mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hlip x (x - t n • y))
                (by positivity)
          _ = M * ‖y‖ := by
              rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
              field_simp [(htpos n).ne']
      · have hxW : x ∉ W := fun hxW ↦ hx (subset_closure hxW)
        have hQ0 : Q (t n) x = 0 := by
          simp only [hQdef, hsupp (t n • y) (htε n) x hxW,
            image_eq_zero_of_notMem_tsupport fun hm ↦ hxW (hφW hm), sub_zero, mul_zero]
        rw [hQ0, zero_smul, norm_zero]
        exact mul_nonneg (mul_nonneg hM0 (norm_nonneg _)) (norm_nonneg _)
    · -- the pointwise limit
      refine Tendsto.smul_const ?_ (u x)
      have hd : HasDerivAt (fun s : ℝ ↦ (φ : E → ℝ) (x - s • y)) (fderiv ℝ φ x (-y)) 0 := by
        have := ((φ.contDiff.differentiable (by simp)) (x - (0 : ℝ) • y)).hasFDerivAt
          |>.comp_hasDerivAt (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const y).const_sub x)
        simpa [Function.comp_def] using this
      have := (hasDerivAt_iff_tendsto_slope.1 hd).comp ht0'
      rw [map_neg] at this
      refine this.congr fun n ↦ ?_
      simp [slope_def_module, hQdef]
  have hfinal : ‖∫ x in (Ω : Set E), (-(fderiv ℝ φ x y)) • u x ∂μ‖ₑ
      ≤ C * ‖y‖ₑ * eLpNorm φ q (μ.restrict (Ω : Set E)) :=
    le_of_tendsto' ((continuous_enorm.tendsto _).comp hlim) fun n ↦
      hQbound (t n) (htpos n).ne' (htε n) (htδ n)
  simpa only [neg_smul, integral_neg, enorm_neg] using hfinal

/-- **Proposition 9.3**, (iii) $\Rightarrow$ (ii), for the translations whose segments stay in
$\Omega$. Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$,
let $\Omega \subseteq E$ be open, and let $p, q \in [1, \infty]$ be Hölder conjugate. Let
$u \in L^p(\Omega; F)$ and $C \in [0, \infty]$. Assume that for every open $V$ whose closure is
compact and contained in $\Omega$, and every $a \in E$ with $x + ta \in \Omega$ for all
$x \in V$ and $t \in [0, 1]$,
$$\|u(\cdot + a) - u\|_{L^p(V)} \le C \|a\|.$$
Then for every test function $\varphi \in \mathcal{D}(\Omega)$ and every $y \in E$,
$$\Big\| \int_\Omega \partial_y \varphi \, u \, d\mu \Big\| \le C \|y\| \,
  \|\varphi\|_{L^q(\Omega)}.$$

This is Proposition 9.3, (iii) $\Rightarrow$ (ii), of [brezis2011functional]. The hypothesis is
the conclusion of `HasWeakFDerivOn.eLpNorm_sub_translate_le`. The proof reduces to
`abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le_of_norm_lt`: the segments of length
less than $\varepsilon$ from $V$ stay in $\Omega$, for the $\varepsilon$ of
`IsCompact.exists_pos_forall_closedBall_subset`. -/
theorem abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le [ENNReal.HolderConjugate p q]
    (hu : MemLp u p (μ.restrict (Ω : Set E))) {C : ℝ≥0∞}
    (h : ∀ V : Set E, IsOpen V → IsCompact (closure V) → closure V ⊆ (Ω : Set E) → ∀ a : E,
      (∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + t • a ∈ (Ω : Set E)) →
      eLpNorm (fun x ↦ u (x + a) - u x) p (μ.restrict V) ≤ C * ‖a‖ₑ)
    (φ : 𝓓(Ω, ℝ)) (y : E) :
    ‖∫ x in (Ω : Set E), fderiv ℝ φ x y • u x ∂μ‖ₑ
      ≤ C * ‖y‖ₑ * eLpNorm φ q (μ.restrict (Ω : Set E)) := by
  refine abs_integral_smul_fderiv_le_of_eLpNorm_sub_translate_le_of_norm_lt hu
    (fun V hVo hVc hVΩ ↦ ?_) φ y
  obtain ⟨V', ε, -, hVV', hε, -, -, hball⟩ := hVc.exists_pos_forall_closedBall_subset Ω.isOpen hVΩ
  refine ⟨ε, hε, fun a ha ↦ h V hVo hVc hVΩ a fun x hx t ht ↦ hball x (hVV' (subset_closure hx)) ?_⟩
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans ha.le

end DifferenceQuotient

/-! ### Mollification near a compact set, with almost everywhere convergence -/

section Core

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → F}
  {w : E → E →L[ℝ] F} {p : ℝ≥0∞}

/-- Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, let
$\Omega \subseteq E$ be open, let $w$ be a weak derivative of $u \colon E \to F$ on $\Omega$,
and let $K \subseteq \Omega$ be compact. Then there are a compact set $C \subseteq \Omega$ and
normalized bumps $\rho_j$ with outer radii $r_j \to 0$ such that the following hold for every
$j$, with $g_j = \rho_j * (\mathbf{1}_C u)$ the mollification of the truncation of $u$ to $C$.

* For every $x \in K$, the closed ball of radius $r_j$ about $x$ lies in the interior of $C$.
* $g_j$ is smooth.
* For every $x \in K$, $Dg_j(x) = (\rho_j * (\mathbf{1}_C w))(x)$.
* $g_j(x) \to u(x)$ as $j \to \infty$, for almost every $x \in K$.

This is the common core of the $L^\infty$ translation estimate
`HasWeakFDerivOn.eLpNorm_sub_translate_le_top` and of the representatives of Remarks 2 and 7 of
Chapter 9 of [brezis2011functional]. The normalized bump $\rho_j$ is `(φ j).normed μ`. The
derivative identity is `HasWeakIteratedFDerivOn.iteratedFDeriv_convolution`. The almost
everywhere convergence comes from an almost everywhere convergent subsequence of a sequence that
converges in $L^1$ (`MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`). -/
theorem HasWeakFDerivOn.exists_seq_contDiffBump_tendsto_ae (h : HasWeakFDerivOn u w Ω μ)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ (Ω : Set E)) :
    ∃ (C : Set E) (φ : ℕ → ContDiffBump (0 : E)), IsCompact C ∧ C ⊆ (Ω : Set E) ∧
      Tendsto (fun j ↦ (φ j).rOut) atTop (𝓝 0) ∧
      (∀ j, ∀ x ∈ K, closedBall x (φ j).rOut ⊆ interior C) ∧
      (∀ j, ContDiff ℝ ∞ ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] C.indicator u)) ∧
      (∀ j, ∀ x ∈ K, fderiv ℝ ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] C.indicator u) x
        = ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] C.indicator w) x) ∧
      ∀ᵐ x ∂μ.restrict K, Tendsto (fun j ↦ ((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] C.indicator u) x)
        atTop (𝓝 (u x)) := by
  obtain ⟨W, -, hWo, hKW, -, hWc, hWΩ, -⟩ := hK.exists_pos_forall_closedBall_subset Ω.isOpen hKΩ
  obtain ⟨V, ε, -, hKV, hε, -, -, hVball⟩ := hK.exists_pos_forall_closedBall_subset hWo hKW
  obtain ⟨C, hCdef⟩ : ∃ C : Set E, C = closure W := ⟨_, rfl⟩
  have hCc : IsCompact C := hCdef ▸ hWc
  have hCΩ : C ⊆ (Ω : Set E) := hCdef ▸ hWΩ
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hWC : W ⊆ interior C := hCdef ▸ interior_maximal subset_closure hWo
  -- the truncations
  have hu' : Integrable (C.indicator u) μ :=
    (integrable_indicator_iff hCm).2 (h.locallyIntegrableOn.integrableOn_compact_subset hCΩ hCc)
  have hint : HasWeakFDerivOn (C.indicator u) (C.indicator w) ⟨interior C, isOpen_interior⟩ μ :=
    (HasWeakIteratedFDerivOn.mono h (interior_subset.trans hCΩ)).congr_ae
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ (Set.indicator_of_mem (interior_subset hz) u).symm)
      (Filter.eventually_of_mem (self_mem_ae_restrict isOpen_interior.measurableSet)
        fun z hz ↦ by simp [Set.indicator_of_mem (interior_subset hz)])
  -- the bumps
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : ℕ → ContDiffBump (0 : E), ∀ j, (φ₀ j).rOut = ε / (j + 2) :=
    ⟨fun j ↦ ⟨ε / (2 * (j + 2)), ε / (j + 2), by positivity, by
      apply div_lt_div_of_pos_left hε (by positivity)
      nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]⟩, fun j ↦ rfl⟩
  have hrOutle : ∀ j, (φ₀ j).rOut ≤ ε := fun j ↦ by
    rw [hφ₀, div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have htend : Tendsto (fun j ↦ (φ₀ j).rOut) atTop (𝓝 0) := by
    simp only [hφ₀]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hball : ∀ j, ∀ x ∈ K, closedBall x (φ₀ j).rOut ⊆ interior C := fun j x hx ↦
    ((closedBall_subset_closedBall (hrOutle j)).trans (hVball x (hKV hx))).trans hWC
  -- the derivative of the mollification on `K`
  have hderiv : ∀ j, ∀ x ∈ K, fderiv ℝ ((φ₀ j).normed μ ⋆[lsmul ℝ ℝ, μ] C.indicator u) x
      = ((φ₀ j).normed μ ⋆[lsmul ℝ ℝ, μ] C.indicator w) x := by
    intro j x hx
    have h1 := HasWeakIteratedFDerivOn.iteratedFDeriv_convolution hint (φ₀ j).contDiff_normed
      (le_of_eq ((φ₀ j).tsupport_normed_eq (μ := μ))) (hball j x hx)
    rw [iteratedFDeriv_one_eq_symm_fderiv] at h1
    apply (continuousMultilinearCurryFin1 ℝ E F).symm.injective
    have key := (continuousMultilinearCurryFin1 ℝ E F).symm.toContinuousLinearEquiv
      |>.integral_comp_comm (μ := μ) (fun t ↦ (φ₀ j).normed μ t • C.indicator w (x - t))
    simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] at key
    rw [h1, convolution_def, convolution_def]
    simp only [lsmul_apply, ← LinearIsometryEquiv.map_smul]
    exact key
  -- the almost everywhere convergent subsequence
  have hL1 : Tendsto (fun j ↦ eLpNorm ((φ₀ j).normed μ ⋆[lsmul ℝ ℝ, μ] C.indicator u
      - C.indicator u) 1 μ) atTop (𝓝 0) :=
    ContDiffBump.tendsto_eLpNorm_convolution_sub htend le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.2 hu')
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero hL1).exists_seq_tendsto_ae
  refine ⟨C, fun k ↦ φ₀ (ns k), hCc, hCΩ, htend.comp hns.tendsto_atTop, fun k ↦ hball (ns k),
    fun k ↦ hu'.locallyIntegrable.contDiff_convolution_normed (φ₀ (ns k)),
    fun k ↦ hderiv (ns k), ?_⟩
  filter_upwards [ae_restrict_of_ae hae, self_mem_ae_restrict hK.isClosed.measurableSet]
    with x hx hxK
  rwa [Set.indicator_of_mem (hWC (hKW hxK) |> interior_subset) u] at hx


/-- **Proposition 9.3**, (i) $\Rightarrow$ (iii), at $p = \infty$. Let $E$ be a finite-dimensional
real normed space with an additive Haar measure $\mu$, let $\Omega \subseteq E$ be open, and let
$w$ be a weak derivative of $u \colon E \to F$ on $\Omega$. Let $V \subseteq E$ be open and
$a \in E$ such that $x + ta \in \Omega$ for every $x \in V$ and $t \in [0, 1]$. Then
$$\|u(\cdot + a) - u\|_{L^\infty(V)} \le \|a\| \, \|w\|_{L^\infty(\Omega)}.$$

No integrability of $u$ beyond local integrability on $\Omega$ is needed. This is the case
$p = \infty$ of Proposition 9.3, (i) $\Rightarrow$ (iii), of [brezis2011functional], proved
directly and not as a limit $p \to \infty$. On a relatively compact piece of $V$, the
mollifications of `HasWeakFDerivOn.exists_seq_contDiffBump_tendsto_ae` have gradients bounded by
$\|w\|_{L^\infty}$ along the segments. The mean value theorem bounds their increments by
$\|w\|_{L^\infty} \|a\|$, and the bound passes to $u$ at almost every point where the
mollifications converge at both $x$ and $x + a$. -/
theorem HasWeakFDerivOn.eLpNorm_sub_translate_le_top (h : HasWeakFDerivOn u w Ω μ) {V : Set E}
    (hV : IsOpen V) (a : E) (hseg : ∀ x ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, x + t • a ∈ (Ω : Set E)) :
    eLpNorm (fun x ↦ u (x + a) - u x) ⊤ (μ.restrict V)
      ≤ ‖a‖ₑ * eLpNorm w ⊤ (μ.restrict (Ω : Set E)) := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne (eLpNorm w ⊤ (μ.restrict (Ω : Set E))) ⊤ with htop | hne
  · rw [htop, ENNReal.mul_top (by simpa using ha)]
    exact le_top
  set M : ℝ := (eLpNorm w ⊤ (μ.restrict (Ω : Set E))).toReal with hMdef
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hwm : AEStronglyMeasurable w (μ.restrict (Ω : Set E)) :=
    h.locallyIntegrableOn_weakDeriv.aestronglyMeasurable
  have hne' : eLpNormEssSup w (μ.restrict (Ω : Set E)) ≠ ⊤ := by
    rwa [← eLpNorm_exponent_top hwm]
  have hwM : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖w x‖ ≤ M := by
    filter_upwards [enorm_ae_le_eLpNormEssSup w (μ.restrict (Ω : Set E))] with x hx
    rw [hMdef, eLpNorm_exponent_top hwm, ← ENNReal.ofReal_le_iff_le_toReal hne', ofReal_norm]
    exact hx
  -- the almost everywhere bound on an exhaustion of `V`
  obtain ⟨U, hUc, hUsucc, hUV⟩ := (⟨V, hV⟩ : Opens E).exists_exhaustion
  have hUV' : ∀ n, (U n : Set E) ⊆ V := fun n ↦ by
    have := Set.subset_iUnion (fun n ↦ (U n : Set E)) n
    rwa [hUV] at this
  have hae : ∀ n, ∀ᵐ x ∂μ.restrict (U n : Set E), ‖u (x + a) - u x‖ ≤ M * ‖a‖ := by
    intro n
    have hKV : closure (U n : Set E) ⊆ V := (hUsucc n).trans (hUV' (n + 1))
    obtain ⟨K, hKdef⟩ : ∃ K : Set E,
        K = (fun z : E × ℝ ↦ z.1 + z.2 • a) '' (closure (U n : Set E) ×ˢ Icc (0 : ℝ) 1) :=
      ⟨_, rfl⟩
    have hKc : IsCompact K := hKdef ▸ ((hUc n).prod isCompact_Icc).image
      (continuous_fst.add (continuous_snd.smul continuous_const))
    have hKΩ : K ⊆ (Ω : Set E) := by
      rw [hKdef]
      rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact hseg x (hKV hx) t ht
    have hUK : ∀ x ∈ (U n : Set E), ∀ t ∈ Icc (0 : ℝ) 1, x + t • a ∈ K := fun x hx t ht ↦
      hKdef ▸ ⟨(x, t), ⟨subset_closure hx, ht⟩, rfl⟩
    have hsegK : ∀ x ∈ (U n : Set E), segment ℝ x (x + a) ⊆ K := by
      intro x hx
      rw [segment_eq_image']
      rintro _ ⟨t, ht, rfl⟩
      simpa using hUK x hx t ht
    obtain ⟨C, φ, hCc, hCΩ, -, -, hgs, hgd, hgt⟩ := h.exists_seq_contDiffBump_tendsto_ae hKc hKΩ
    -- the gradient bound on `K`
    have hwC : ∀ᵐ z ∂μ, ‖C.indicator w z‖ ≤ M := by
      filter_upwards [(ae_restrict_iff' hΩm).1 hwM] with z hz
      by_cases hzC : z ∈ C
      · rw [Set.indicator_of_mem hzC]; exact hz (hCΩ hzC)
      · rw [Set.indicator_of_notMem hzC, norm_zero]; exact hM0
    have hgrad : ∀ j, ∀ z ∈ K,
        ‖fderiv ℝ ((φ j).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] C.indicator u) z‖ ≤ M :=
      fun j z hz ↦ by
        rw [hgd j z hz]
        exact (φ j).norm_convolution_normed_le_of_ae_norm_le hwC z
    -- the mean value theorem along the segment, for the mollifications
    have hmvt : ∀ j, ∀ x ∈ (U n : Set E),
        ‖((φ j).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] C.indicator u) (x + a)
          - ((φ j).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] C.indicator u) x‖ ≤ M * ‖a‖ := by
      intro j x hx
      have := Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ ↦ ((hgs j).differentiable (by simp)).differentiableAt)
        (fun z hz ↦ hgrad j z (hsegK x hx hz)) (convex_segment x (x + a))
        (left_mem_segment ℝ x (x + a)) (right_mem_segment ℝ x (x + a))
      simpa using this
    -- pass to the limit at the points where both `x` and `x + a` are good
    have hae' : ∀ᵐ x ∂μ, x + a ∈ K →
        Tendsto (fun j ↦ ((φ j).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] C.indicator u)
          (x + a)) atTop (𝓝 (u (x + a))) :=
      (measurePreserving_add_right μ a).quasiMeasurePreserving.ae
        ((ae_restrict_iff' hKc.isClosed.measurableSet).1 hgt)
    have hUKsub : (U n : Set E) ⊆ K := fun x hx ↦ by
      simpa using hUK x hx 0 ⟨le_rfl, zero_le_one⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUKsub hgt, ae_restrict_of_ae hae',
      self_mem_ae_restrict (U n).isOpen.measurableSet] with x hx hxa hxU
    have hxaK : x + a ∈ K := by simpa using hUK x hxU 1 ⟨zero_le_one, le_rfl⟩
    exact le_of_tendsto ((hxa hxaK).sub hx).norm (Eventually.of_forall fun j ↦ hmvt j x hxU)
  have hall : ∀ᵐ x ∂μ.restrict V, ‖u (x + a) - u x‖ ≤ M * ‖a‖ := by
    rw [show V = ⋃ n, (U n : Set E) from hUV.symm, ae_restrict_iUnion_iff]
    exact hae
  have hVΩ : V ⊆ (Ω : Set E) := fun x hx ↦ by simpa using hseg x hx 0 ⟨le_rfl, zero_le_one⟩
  have hum : AEStronglyMeasurable u (μ.restrict (Ω : Set E)) :=
    h.locallyIntegrableOn.aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun x ↦ u (x + a) - u x) (μ.restrict V) :=
    (aestronglyMeasurable_comp_add_right_restrict a hV.measurableSet hΩm
      (fun x hx ↦ by simpa using hseg x hx 1 ⟨zero_le_one, le_rfl⟩) hum).sub
      (hum.mono_measure (Measure.restrict_mono hVΩ le_rfl))
  rw [eLpNorm_exponent_top hm]
  refine (eLpNormEssSup_le_of_ae_bound hall).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hM0, hMdef, ENNReal.ofReal_toReal hne, ofReal_norm, mul_comm]

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Gluing of local continuous representatives. Let $E$ be a finite-dimensional real normed space
with an additive Haar measure $\mu$, let $\Omega \subseteq E$ be open, and let $P$ be a property
of a function on a ball. Assume that every $x \in \Omega$ has a ball $B(x, r) \subseteq \Omega$,
$r > 0$, and a function $g$ with the property $P$ on $B(x, r)$, continuous on $B(x, r)$, with
$u = g$ almost everywhere on $B(x, r)$. Then there is a function $v$, continuous on $\Omega$,
with $u = v$ almost everywhere on $\Omega$, such that every $x \in \Omega$ has a ball
$B(x, r) \subseteq \Omega$, $r > 0$, and a function $g$ with the property $P$ on $B(x, r)$ and
$v = g$ on $B(x, r)$.

Two continuous functions that agree almost everywhere on an open set agree on it
(`MeasureTheory.Measure.eqOn_open_of_ae_eq`), so the local representatives are compatible.
Countably many of the balls cover $\Omega$ (`TopologicalSpace.isOpen_iUnion_countable`), so the
local null sets combine into one null set. -/
theorem MeasureTheory.exists_continuousOn_ae_eq_of_forall_exists_ball {u : E → F}
    (P : (E → F) → Set E → Prop)
    (hP : ∀ x ∈ (Ω : Set E), ∃ r > 0, ball x r ⊆ (Ω : Set E) ∧ ∃ g : E → F, P g (ball x r) ∧
      ContinuousOn g (ball x r) ∧ u =ᵐ[μ.restrict (ball x r)] g) :
    ∃ v : E → F, ContinuousOn v Ω ∧ u =ᵐ[μ.restrict (Ω : Set E)] v ∧
      ∀ x ∈ (Ω : Set E), ∃ r > 0, ball x r ⊆ (Ω : Set E) ∧
        ∃ g : E → F, P g (ball x r) ∧ EqOn v g (ball x r) := by
  choose! r hr hrΩ g hPg hgc hug using hP
  -- the representatives agree on the overlaps of their balls
  have hagree : ∀ x ∈ (Ω : Set E), ∀ y ∈ ball x (r x), g y y = g x y := by
    intro x hx y hy
    have hyΩ : y ∈ (Ω : Set E) := hrΩ x hx hy
    have hB : IsOpen (ball x (r x) ∩ ball y (r y)) := isOpen_ball.inter isOpen_ball
    have hA : u =ᵐ[μ.restrict (ball x (r x) ∩ ball y (r y))] g y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hug y hyΩ)
    have hB' : u =ᵐ[μ.restrict (ball x (r x) ∩ ball y (r y))] g x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hug x hx)
    have hae : g y =ᵐ[μ.restrict (ball x (r x) ∩ ball y (r y))] g x := hA.symm.trans hB'
    exact Measure.eqOn_open_of_ae_eq hae hB ((hgc y hyΩ).mono inter_subset_right)
      ((hgc x hx).mono inter_subset_left) ⟨hy, mem_ball_self (hr y hyΩ)⟩
  refine ⟨fun x ↦ g x x, ?_, ?_, fun x hx ↦ ⟨r x, hr x hx, hrΩ x hx, g x, hPg x hx,
    fun y hy ↦ hagree x hx y hy⟩⟩
  · -- continuity
    intro x hx
    refine ((hgc x hx).continuousAt (isOpen_ball.mem_nhds (mem_ball_self (hr x hx))))
      |>.congr_of_eventuallyEq ?_ |>.continuousWithinAt
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (hr x hx))] with y hy
    exact hagree x hx y hy
  · -- almost everywhere equality, through a countable subcover
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : (Ω : Set E) ↦ ball (x : E) (r x)) (fun _ ↦ isOpen_ball)
    have hcover : (Ω : Set E) ⊆ ⋃ x ∈ T, ball (x : E) (r x) := by
      rw [hTU]
      intro y hy
      exact mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (hr y hy)⟩
    refine ae_restrict_of_ae_restrict_of_subset hcover ((ae_restrict_biUnion_iff _ hTc _).2
      fun x _ ↦ ?_)
    filter_upwards [hug x x.2, self_mem_ae_restrict measurableSet_ball] with y hy hyx
    rw [hy]
    exact (hagree x x.2 y hyx).symm

end Core

/-! ### Remark 7: Lipschitz and continuous representatives of $W^{1,\infty}$ -/

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {u : E → ℝ} {w : E → E →L[ℝ] ℝ}

/-- Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, and let
$\Omega \subseteq E$ be a convex open set. Let $w$ be a weak derivative of
$u \colon E \to \mathbb{R}$ on $\Omega$, and let $M \ge 0$ with $\|w\| \le M$ almost everywhere
on $\Omega$. Then for almost every $x \in \Omega$ and almost every $y \in \Omega$,
$$|u(x) - u(y)| \le M \|x - y\|.$$

The mollifications of `HasWeakFDerivOn.exists_seq_contDiffBump_tendsto_ae`, taken on the compact
set swept out by the segments between points of a relatively compact piece of $\Omega$, are
$M$-Lipschitz along these segments by the mean value theorem, and they converge to $u$ almost
everywhere. -/
theorem HasWeakFDerivOn.ae_ae_norm_sub_le_of_convex (h : HasWeakFDerivOn u w Ω μ)
    (hΩ : Convex ℝ (Ω : Set E)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖w x‖ ≤ M) :
    ∀ᵐ x ∂μ.restrict (Ω : Set E), ∀ᵐ y ∂μ.restrict (Ω : Set E), ‖u x - u y‖ ≤ M * ‖x - y‖ := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  obtain ⟨U, hUc, hUsucc, hUV⟩ := Ω.exists_exhaustion
  have hUmono : Monotone fun n ↦ (U n : Set E) :=
    monotone_nat_of_le_succ fun n ↦ subset_closure.trans (hUsucc n)
  have hUΩ : ∀ n, (U n : Set E) ⊆ Ω := fun n ↦ by
    have := Set.subset_iUnion (fun n ↦ (U n : Set E)) n
    rwa [hUV] at this
  -- the compact sets swept out by the segments between points of `closure (U n)`
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → Set E, ∀ n,
      K n = (fun z : (E × E) × ℝ ↦ z.1.1 + z.2 • (z.1.2 - z.1.1)) ''
        ((closure (U n : Set E) ×ˢ closure (U n : Set E)) ×ˢ Icc (0 : ℝ) 1) := ⟨_, fun _ ↦ rfl⟩
  have hKc : ∀ n, IsCompact (K n) := fun n ↦ (hKdef n) ▸
    (((hUc n).prod (hUc n)).prod isCompact_Icc).image
      ((continuous_fst.comp continuous_fst).add (continuous_snd.smul
        ((continuous_snd.comp continuous_fst).sub (continuous_fst.comp continuous_fst))))
  have hclΩ : ∀ n, closure (U n : Set E) ⊆ Ω := fun n ↦ (hUsucc n).trans (hUΩ (n + 1))
  have hKΩ : ∀ n, K n ⊆ (Ω : Set E) := fun n ↦ by
    rw [hKdef n]
    rintro _ ⟨⟨⟨x, y⟩, t⟩, ⟨⟨hx, hy⟩, ht⟩, rfl⟩
    exact hΩ.add_smul_sub_mem (hclΩ n hx) (hclΩ n hy) ht
  have hsegK : ∀ n, ∀ x ∈ closure (U n : Set E), ∀ y ∈ closure (U n : Set E),
      segment ℝ x y ⊆ K n := by
    intro n x hx y hy
    rw [segment_eq_image', hKdef n]
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨((x, y), t), ⟨⟨hx, hy⟩, ht⟩, rfl⟩
  have hUK : ∀ n, (U n : Set E) ⊆ K n := fun n x hx ↦ by
    simpa using hsegK n x (subset_closure hx) x (subset_closure hx) (left_mem_segment ℝ x x)
  -- the bound on each `K n`
  have hae : ∀ n, ∀ᵐ x ∂μ, x ∈ (U n : Set E) → ∀ᵐ y ∂μ, y ∈ (U n : Set E) →
      ‖u x - u y‖ ≤ M * ‖x - y‖ := by
    intro n
    obtain ⟨C, φ, hCc, hCΩ, -, -, hgs, hgd, hgt⟩ :=
      h.exists_seq_contDiffBump_tendsto_ae (hKc n) (hKΩ n)
    have hwC : ∀ᵐ z ∂μ, ‖C.indicator w z‖ ≤ M := by
      filter_upwards [(ae_restrict_iff' hΩm).1 hM] with z hz
      by_cases hzC : z ∈ C
      · rw [Set.indicator_of_mem hzC]; exact hz (hCΩ hzC)
      · rw [Set.indicator_of_notMem hzC, norm_zero]; exact hM0
    have hgrad : ∀ j, ∀ z ∈ K n,
        ‖fderiv ℝ ((φ j).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] C.indicator u) z‖ ≤ M :=
      fun j z hz ↦ by
        rw [hgd j z hz]
        exact (φ j).norm_convolution_normed_le_of_ae_norm_le hwC z
    have hmvt : ∀ j, ∀ x ∈ K n, ∀ y ∈ K n, segment ℝ x y ⊆ K n →
        ‖((φ j).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] C.indicator u) x
          - ((φ j).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] C.indicator u) y‖
          ≤ M * ‖x - y‖ := fun j x _ y _ hseg ↦
      Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ ↦ ((hgs j).differentiable (by simp)).differentiableAt)
        (fun z hz ↦ hgrad j z (hseg hz)) (convex_segment x y) (right_mem_segment ℝ x y)
        (left_mem_segment ℝ x y)
    have hgt' := (ae_restrict_iff' (hKc n).isClosed.measurableSet).1 hgt
    filter_upwards [hgt'] with x hx hxU
    filter_upwards [hgt'] with y hy hyU
    have hseg : segment ℝ x y ⊆ K n :=
      hsegK n x (subset_closure hxU) y (subset_closure hyU)
    exact le_of_tendsto ((hx (hUK n hxU)).sub (hy (hUK n hyU))).norm
      (Eventually.of_forall fun j ↦ hmvt j x (hUK n hxU) y (hUK n hyU) hseg)
  -- assembling the pieces of the exhaustion
  rw [ae_restrict_iff' hΩm]
  filter_upwards [ae_all_iff.2 hae] with x hx hxΩ
  obtain ⟨n₀, hn₀⟩ : ∃ n, x ∈ (U n : Set E) := by
    rw [← hUV] at hxΩ
    exact mem_iUnion.1 hxΩ
  have hx' : ∀ n, ∀ᵐ y ∂μ, x ∈ (U n : Set E) → y ∈ (U n : Set E) →
      ‖u x - u y‖ ≤ M * ‖x - y‖ := fun n ↦ by
    by_cases hxn : x ∈ (U n : Set E)
    · filter_upwards [hx n hxn] with y hy
      exact fun _ ↦ hy
    · exact Eventually.of_forall fun y hxn' ↦ absurd hxn' hxn
  rw [ae_restrict_iff' hΩm]
  filter_upwards [ae_all_iff.2 hx'] with y hy hyΩ
  obtain ⟨m, hm⟩ : ∃ n, y ∈ (U n : Set E) := by
    rw [← hUV] at hyΩ
    exact mem_iUnion.1 hyΩ
  exact hy (max n₀ m) (hUmono (le_max_left n₀ m) hn₀) (hUmono (le_max_right n₀ m) hm)


/-- **Remark 7** of [brezis2011functional], convex case. Let $E$ be a finite-dimensional real normed
space with an additive Haar measure $\mu$, and let $\Omega \subseteq E$ be a convex open set.
Let $w$ be a weak derivative of $u \colon E \to \mathbb{R}$ on $\Omega$, and let $M \ge 0$ with
$\|w\| \le M$ almost everywhere on $\Omega$. Then there is a function $v$ with $u = v$ almost
everywhere on $\Omega$ that is $M$-Lipschitz on $\Omega$.

This is the case of Remark 7 in Chapter 9 of the source that says "if $\Omega$ is convex then
$\operatorname{dist}_\Omega(x, y) = |x - y|$". The almost everywhere bound
`HasWeakFDerivOn.ae_ae_norm_sub_le_of_convex` is a true Lipschitz bound on the set $G$ of full
measure of the points $x$ for which $|u(x) - u(y)| \le M \|x - y\|$ for almost every $y$: two
such points are compared through a common good point $y$ arbitrarily close to one of them.
McShane's extension `LipschitzOnWith.extend_real` then gives $v$. The Lipschitz constant is
`Real.toNNReal M`. -/
theorem HasWeakFDerivOn.exists_lipschitzOnWith_ae_eq_of_convex (h : HasWeakFDerivOn u w Ω μ)
    (hΩ : Convex ℝ (Ω : Set E)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖w x‖ ≤ M) :
    ∃ v : E → ℝ, u =ᵐ[μ.restrict (Ω : Set E)] v ∧ LipschitzOnWith (Real.toNNReal M) v Ω := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hae := h.ae_ae_norm_sub_le_of_convex hΩ hM0 hM
  -- the good points
  obtain ⟨G, hGdef⟩ : ∃ G : Set E, G = {x | x ∈ (Ω : Set E) ∧
      ∀ᵐ y ∂μ.restrict (Ω : Set E), ‖u x - u y‖ ≤ M * ‖x - y‖} := ⟨_, rfl⟩
  have hG : ∀ᵐ x ∂μ.restrict (Ω : Set E), x ∈ G := by
    filter_upwards [hae, self_mem_ae_restrict hΩm] with x hx hxΩ
    rw [hGdef]
    exact ⟨hxΩ, hx⟩
  -- `u` is Lipschitz on the good points
  have hlip : LipschitzOnWith (Real.toNNReal M) u G := by
    refine lipschitzOnWith_iff_dist_le_mul.2 fun x hx x' hx' ↦ ?_
    rw [hGdef] at hx hx'
    obtain ⟨hxΩ, hx⟩ := hx
    obtain ⟨hx'Ω, hx'⟩ := hx'
    rw [Real.coe_toNNReal M hM0, dist_eq_norm, dist_eq_norm]
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    set η : ℝ := ε / (2 * M + 1) with hηdef
    have hη : 0 < η := by positivity
    -- a common good point `y` near `x`
    have hpos : (μ.restrict (Ω : Set E)) (ball x η) ≠ 0 := by
      rw [Measure.restrict_apply measurableSet_ball]
      exact (isOpen_ball.inter Ω.isOpen).measure_ne_zero μ ⟨x, mem_ball_self hη, hxΩ⟩
    obtain ⟨y, hyx, hy, hy'⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae (hx.and hx'))
    have hyx' : ‖x - y‖ < η := by rwa [mem_ball, dist_comm, dist_eq_norm] at hyx
    calc ‖u x - u x'‖ = ‖(u x - u y) - (u x' - u y)‖ := by congr 1; abel
      _ ≤ ‖u x - u y‖ + ‖u x' - u y‖ := norm_sub_le _ _
      _ ≤ M * ‖x - y‖ + M * ‖x' - y‖ := add_le_add hy hy'
      _ ≤ M * η + M * (‖x' - x‖ + η) := by
          gcongr
          calc ‖x' - y‖ = ‖(x' - x) + (x - y)‖ := by congr 1; abel
            _ ≤ ‖x' - x‖ + ‖x - y‖ := norm_add_le _ _
            _ ≤ ‖x' - x‖ + η := by gcongr
      _ = M * ‖x - x'‖ + 2 * M * η := by rw [norm_sub_rev x' x]; ring
      _ ≤ M * ‖x - x'‖ + ε := by
          gcongr
          rw [hηdef, mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
  obtain ⟨v, hv, huv⟩ := hlip.extend_real
  refine ⟨v, ?_, hv.lipschitzOnWith⟩
  filter_upwards [hG] with x hx
  exact huv hx

/-- **Remark 7** of [brezis2011functional], first sentence, on any open set. Let $E$ be a
finite-dimensional real normed space with an additive Haar measure $\mu$, and let
$\Omega \subseteq E$ be open. Let $w$ be a weak derivative of $u \colon E \to \mathbb{R}$ on
$\Omega$, and let $M \ge 0$ with $\|w\| \le M$ almost everywhere on $\Omega$. Then there is a
function $v$, continuous on $\Omega$, with $u = v$ almost everywhere on $\Omega$, such that
every point of $\Omega$ has a ball $B \subseteq \Omega$ about it on which $v$ is $M$-Lipschitz.

In particular, a function of $W^{1,\infty}(\Omega)$ has a continuous representative. The proof
applies the convex case `HasWeakFDerivOn.exists_lipschitzOnWith_ae_eq_of_convex` on each ball
and glues the results by `MeasureTheory.exists_continuousOn_ae_eq_of_forall_exists_ball`. -/
theorem HasWeakFDerivOn.exists_continuousOn_ae_eq_of_ae_norm_le (h : HasWeakFDerivOn u w Ω μ)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖w x‖ ≤ M) :
    ∃ v : E → ℝ, ContinuousOn v Ω ∧ u =ᵐ[μ.restrict (Ω : Set E)] v ∧
      ∀ x ∈ (Ω : Set E), ∃ r > 0, ball x r ⊆ (Ω : Set E) ∧
        LipschitzOnWith (Real.toNNReal M) v (ball x r) := by
  obtain ⟨v, hvc, huv, hloc⟩ := exists_continuousOn_ae_eq_of_forall_exists_ball
    (μ := μ) (Ω := Ω) (u := u) (fun g s ↦ LipschitzOnWith (Real.toNNReal M) g s) fun x hx ↦ by
      obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
      have hle : (⟨ball x r, isOpen_ball⟩ : Opens E) ≤ Ω := hrΩ
      obtain ⟨g, hug, hg⟩ := (h.mono hle).exists_lipschitzOnWith_ae_eq_of_convex
        (convex_ball x r) hM0 (ae_restrict_of_ae_restrict_of_subset hrΩ hM)
      exact ⟨r, hr, hrΩ, g, hg, hg.continuousOn, hug⟩
  refine ⟨v, hvc, huv, fun x hx ↦ ?_⟩
  obtain ⟨r, hr, hrΩ, g, hg, hvg⟩ := hloc x hx
  refine ⟨r, hr, hrΩ, lipschitzOnWith_iff_dist_le_mul.2 fun a ha b hb ↦ ?_⟩
  rw [hvg ha, hvg hb]
  exact lipschitzOnWith_iff_dist_le_mul.1 hg a ha b hb

/-- **Remark 7** of [brezis2011functional], last sentence. Let $E$ be a finite-dimensional real
normed space with an additive Haar measure $\mu$, and let $\Omega \subseteq E$ be a preconnected
open set. If $w$ is a weak derivative of $u \colon E \to \mathbb{R}$ on $\Omega$ and $w = 0$
almost everywhere on $\Omega$, then there is $c \in \mathbb{R}$ with $u = c$ almost everywhere
on $\Omega$.

A preconnected set is a connected set or the empty set. On a general open set, the result
applies to each connected component. The continuous representative of
`HasWeakFDerivOn.exists_continuousOn_ae_eq_of_ae_norm_le` with $M = 0$ is locally constant on
$\Omega$, hence constant on the connected set $\Omega$. This is the first-order case of the fact
that a vanishing seminorm $|v|_{k,p,\Omega} = 0$ on a connected open set forces $v$ to be a
polynomial of degree less than $k$. -/
theorem HasWeakFDerivOn.ae_eq_const_of_isPreconnected (h : HasWeakFDerivOn u w Ω μ)
    (hw : w =ᵐ[μ.restrict (Ω : Set E)] 0) (hΩ : IsPreconnected (Ω : Set E)) :
    ∃ c : ℝ, u =ᵐ[μ.restrict (Ω : Set E)] fun _ ↦ c := by
  have hM : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖w x‖ ≤ 0 := by
    filter_upwards [hw] with x hx
    rw [hx]; simp
  obtain ⟨v, -, huv, hloc⟩ := h.exists_continuousOn_ae_eq_of_ae_norm_le le_rfl hM
  -- `v` is locally constant on `Ω`
  have hconst : ∀ x ∈ (Ω : Set E), ∃ r > 0, ball x r ⊆ (Ω : Set E) ∧
      ∀ y ∈ ball x r, v y = v x := by
    intro x hx
    obtain ⟨r, hr, hrΩ, hlip⟩ := hloc x hx
    refine ⟨r, hr, hrΩ, fun y hy ↦ ?_⟩
    have := lipschitzOnWith_iff_dist_le_mul.1 hlip y hy x (mem_ball_self hr)
    simpa [dist_le_zero] using this
  rcases (Ω : Set E).eq_empty_or_nonempty with hemp | ⟨x₀, hx₀⟩
  · refine ⟨0, ?_⟩
    unfold Filter.EventuallyEq
    rw [hemp, Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot
  refine ⟨v x₀, huv.trans (Filter.eventually_of_mem (self_mem_ae_restrict Ω.isOpen.measurableSet)
    fun x hx ↦ ?_)⟩
  -- the clopen argument
  choose! r hr hrΩ hvr using hconst
  by_contra hne
  have hA : IsOpen (⋃ y ∈ {y | y ∈ (Ω : Set E) ∧ v y = v x₀}, ball y (r y)) :=
    isOpen_biUnion fun _ _ ↦ isOpen_ball
  have hB : IsOpen (⋃ y ∈ {y | y ∈ (Ω : Set E) ∧ v y ≠ v x₀}, ball y (r y)) :=
    isOpen_biUnion fun _ _ ↦ isOpen_ball
  obtain ⟨z, hzΩ, hzA, hzB⟩ := hΩ _ _ hA hB
    (fun y hy ↦ by
      by_cases hvy : v y = v x₀
      · exact Or.inl (mem_biUnion (x := y) ⟨hy, hvy⟩ (mem_ball_self (hr y hy)))
      · exact Or.inr (mem_biUnion (x := y) ⟨hy, hvy⟩ (mem_ball_self (hr y hy))))
    ⟨x₀, hx₀, mem_biUnion (x := x₀) ⟨hx₀, rfl⟩ (mem_ball_self (hr x₀ hx₀))⟩
    ⟨x, hx, mem_biUnion (x := x) ⟨hx, hne⟩ (mem_ball_self (hr x hx))⟩
  obtain ⟨y, ⟨hyΩ, hy⟩, hzy⟩ := mem_iUnion₂.1 hzA
  obtain ⟨y', ⟨hy'Ω, hy'⟩, hzy'⟩ := mem_iUnion₂.1 hzB
  exact hy' ((hvr y' hy'Ω z hzy').symm.trans ((hvr y hyΩ z hzy).trans hy))

end Lipschitz

/-! ### Remark 2: the $C^1$ representative of a function with continuous weak derivative -/

section ContDiffRep

open ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → F}
  {w : E → E →L[ℝ] F}

/-- Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, and let
$\Omega \subseteq E$ be open. Let $w$ be a weak derivative of $u \colon E \to F$ on $\Omega$
that is continuous on $\Omega$, and let $x_0 \in \Omega$. Then there are $r > 0$ with
$B(x_0, r) \subseteq \Omega$ and a function $G$, continuous on $B(x_0, r)$, with $u = G$ almost
everywhere on $B(x_0, r)$, such that $G$ is differentiable at every $y \in B(x_0, r)$ with
derivative $w(y)$.

This is the local form of the converse statement of Remark 2 of Chapter 9 of
[brezis2011functional]. On a closed ball $K$ about $x_0$, the mollifications $g_j$ of
`HasWeakFDerivOn.exists_seq_contDiffBump_tendsto_ae` have derivatives $\rho_j * w$ that converge
uniformly to $w$ (`ContDiffBump.dist_normed_convolution_le` and the uniform continuity of $w$ on
a compact neighbourhood). They converge at one point $x_1$ of the ball, so they converge
uniformly on a ball about $x_1$ (`uniformCauchySeqOn_ball_of_fderiv`) to a function whose
derivative is $w$ (`hasFDerivAt_of_tendstoUniformlyOn`). This function agrees almost everywhere
with $u$, because both are limits of the $g_j$. -/
theorem HasWeakFDerivOn.exists_ball_hasFDerivAt_ae_eq_of_continuousOn (h : HasWeakFDerivOn u w Ω μ)
    (hw : ContinuousOn w Ω) {x₀ : E} (hx₀ : x₀ ∈ (Ω : Set E)) :
    ∃ r > 0, ball x₀ r ⊆ (Ω : Set E) ∧ ∃ G : E → F, (∀ y ∈ ball x₀ r, HasFDerivAt G (w y) y) ∧
      ContinuousOn G (ball x₀ r) ∧ u =ᵐ[μ.restrict (ball x₀ r)] G := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x₀ hx₀
  set r : ℝ := ε / 4 with hrdef
  have hr : 0 < r := by positivity
  have hKΩ : closedBall x₀ (3 * r) ⊆ (Ω : Set E) :=
    (closedBall_subset_ball (by rw [hrdef]; linarith)).trans hεΩ
  obtain ⟨C, φ, hCc, hCΩ, hrOut, hball, hgs, hgd, hgt⟩ :=
    h.exists_seq_contDiffBump_tendsto_ae (isCompact_closedBall x₀ (3 * r)) hKΩ
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hKC : closedBall x₀ (3 * r) ⊆ C := fun x hx ↦
    interior_subset (hball 0 x hx (mem_closedBall_self (φ 0).rOut_pos.le))
  set g : ℕ → E → F := fun j ↦ (φ j).normed μ ⋆[lsmul ℝ ℝ, μ] C.indicator u with hgdef
  -- the derivatives converge uniformly on the closed ball
  have hunif : TendstoUniformlyOn (fun j y ↦ fderiv ℝ (g j) y) w atTop (closedBall x₀ (3 * r)) := by
    refine Metric.tendstoUniformlyOn_iff.2 fun η hη ↦ ?_
    obtain ⟨δ, hδ, hδw⟩ := Metric.uniformContinuousOn_iff.1
      (hCc.uniformContinuousOn_of_continuous (hw.mono hCΩ)) (η / 2) (by positivity)
    have hmg : AEStronglyMeasurable (C.indicator w) μ :=
      (aestronglyMeasurable_indicator_iff hCm).2
        (h.locallyIntegrableOn_weakDeriv.integrableOn_compact_subset hCΩ hCc).aestronglyMeasurable
    filter_upwards [hrOut.eventually (Iio_mem_nhds hδ)] with j hj y hy
    rw [hgd j y hy]
    have hyC : y ∈ C := hKC hy
    have key : dist (((φ j).normed μ ⋆[lsmul ℝ ℝ, μ] C.indicator w) y) (C.indicator w y)
        ≤ η / 2 := by
      refine (φ j).dist_normed_convolution_le hmg fun z hz ↦ ?_
      have hzC : z ∈ C := interior_subset (hball j y hy (ball_subset_closedBall hz))
      rw [Set.indicator_of_mem hzC, Set.indicator_of_mem hyC]
      exact (hδw z hzC y hyC ((mem_ball.1 hz).trans hj)).le
    rw [Set.indicator_of_mem hyC] at key
    rw [dist_comm]
    exact key.trans_lt (by linarith)
  -- a point of the small ball at which the mollifications converge
  obtain ⟨x₁, hx₁, hx₁t⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (isOpen_ball.measure_ne_zero μ ⟨x₀, mem_ball_self hr⟩)
    (ae_restrict_of_ae_restrict_of_subset
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hgt)
  have hBK : ball x₁ (2 * r) ⊆ closedBall x₀ (3 * r) := fun y hy ↦ by
    rw [mem_closedBall]
    calc dist y x₀ ≤ dist y x₁ + dist x₁ x₀ := dist_triangle _ _ _
      _ ≤ 2 * r + r := add_le_add (mem_ball.1 hy).le (mem_ball.1 hx₁).le
      _ = 3 * r := by ring
  have hx₀B : ball x₀ r ⊆ ball x₁ (2 * r) := fun y hy ↦ by
    rw [mem_ball]
    calc dist y x₁ ≤ dist y x₀ + dist x₀ x₁ := dist_triangle _ _ _
      _ < r + r := add_lt_add (mem_ball.1 hy) (by rw [dist_comm]; exact mem_ball.1 hx₁)
      _ = 2 * r := by ring
  have hderiv : ∀ j, ∀ y ∈ ball x₁ (2 * r), HasFDerivAt (g j) (fderiv ℝ (g j) y) y := fun j y _ ↦
    ((hgs j).differentiable (by simp)).differentiableAt.hasFDerivAt
  -- uniform convergence of the mollifications on the ball about `x₁`
  have hcauchy : UniformCauchySeqOn g atTop (ball x₁ (2 * r)) :=
    uniformCauchySeqOn_ball_of_fderiv (hunif.uniformCauchySeqOn.mono hBK) hderiv hx₁t.cauchy_map
  have hlim : ∀ y ∈ ball x₁ (2 * r), ∃ z, Tendsto (fun j ↦ g j y) atTop (𝓝 z) := fun y hy ↦
    cauchy_map_iff_exists_tendsto.1 (hcauchy.cauchy_map hy)
  choose! G hG using hlim
  have hGderiv : ∀ y ∈ ball x₁ (2 * r), HasFDerivAt G (w y) y := fun y hy ↦
    hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hunif.mono hBK) hderiv hG hy
  refine ⟨r, hr, (ball_subset_closedBall.trans (closedBall_subset_closedBall
    (by linarith))).trans hKΩ, G, fun y hy ↦ hGderiv y (hx₀B hy),
    fun y hy ↦ (hGderiv y (hx₀B hy)).continuousAt.continuousWithinAt, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (hx₀B.trans hBK) hgt,
    self_mem_ae_restrict measurableSet_ball] with y hy hyB
  exact tendsto_nhds_unique hy (hG y (hx₀B hyB))

/-- **Remark 2** of [brezis2011functional], converse statement. Let $E$ be a finite-dimensional real
normed space with an additive Haar measure $\mu$, and let $\Omega \subseteq E$ be open. If $w$
is a weak derivative of $u \colon E \to F$ on $\Omega$ and $w$ is continuous on $\Omega$, then
there is a function $v$ of class $C^1$ on $\Omega$ with $u = v$ almost everywhere on $\Omega$
and $Dv(x) = w(x)$ at every $x \in \Omega$.

This is the sentence "conversely, one can show that …" of Remark 2 in Chapter 9 of the source.
In particular, a function of $W^{1,p}(\Omega)$ whose weak derivative is continuous on $\Omega$
has a $C^1$ representative. The derivative identity is `HasFDerivAt v (w x) x`. The local
representatives of `HasWeakFDerivOn.exists_ball_hasFDerivAt_ae_eq_of_continuousOn` are glued by
`MeasureTheory.exists_continuousOn_ae_eq_of_forall_exists_ball`. The result also produces the
$C^k$ representatives of the Sobolev embedding theorems. -/
theorem HasWeakFDerivOn.exists_contDiffOn_ae_eq_of_continuousOn (h : HasWeakFDerivOn u w Ω μ)
    (hw : ContinuousOn w Ω) :
    ∃ v : E → F, ContDiffOn ℝ 1 v Ω ∧ u =ᵐ[μ.restrict (Ω : Set E)] v ∧
      ∀ x ∈ (Ω : Set E), HasFDerivAt v (w x) x := by
  obtain ⟨v, -, huv, hloc⟩ := exists_continuousOn_ae_eq_of_forall_exists_ball (μ := μ) (Ω := Ω)
    (u := u) (fun G s ↦ ∀ y ∈ s, HasFDerivAt G (w y) y) fun x hx ↦ by
      obtain ⟨r, hr, hrΩ, G, hG, hGc, huG⟩ := h.exists_ball_hasFDerivAt_ae_eq_of_continuousOn hw hx
      exact ⟨r, hr, hrΩ, G, hG, hGc, huG⟩
  have hvd : ∀ x ∈ (Ω : Set E), HasFDerivAt v (w x) x := by
    intro x hx
    obtain ⟨r, hr, -, G, hG, hvG⟩ := hloc x hx
    refine (hG x (mem_ball_self hr)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with y hy
    exact hvG hy
  refine ⟨v, ?_, huv, hvd⟩
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen Ω.isOpen]
  refine ⟨fun x hx ↦ (hvd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hw.congr fun x hx ↦ (hvd x hx).fderiv

end ContDiffRep
