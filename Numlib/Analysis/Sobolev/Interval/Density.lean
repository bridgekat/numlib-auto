/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Interval/Basic.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Friedrichs
import Numlib.Analysis.Sobolev.Interval.Extension

/-!
# Density of smooth compactly supported functions in $W^{1,p}(I)$

Let $I \subseteq \mathbb{R}$ be a nonempty open interval and let $1 \le p < \infty$. The density
theorem says that the restrictions to $I$ of the functions of $C_c^\infty(\mathbb{R})$ are dense in
$W^{1,p}(I)$. This is Theorem 8.7 of [brezis2011functional]. The theorem fails at $p = \infty$: a
uniform limit of $C^1$ functions has a continuous derivative, but a function of $W^{1,\infty}(I)$
need not. Therefore every density statement here assumes $p < \infty$.

The module also proves Lemma 8.4 of [brezis2011functional]: for $\rho \in L^1(\mathbb{R})$ and
$v \in W^{1,p}(\mathbb{R})$, $1 \le p \le \infty$, the convolution $\rho * v$ lies in
$W^{1,p}(\mathbb{R})$ and $(\rho * v)' = \rho * v'$. Finally it compares the space
`SobolevIntervalLp` with the formulation of Sobolev spaces on open subsets of a normed space in
`Numlib.Analysis.Sobolev.Domain` (`MemSobolev`, `sobolevNorm`), in which the $k$-th weak derivative
is a $k$-linear map. The two formulations have the same functions and the same norm in dimension
one.

## Main results

* `HasWeakFDerivOn.hasWeakDerivOn` and `HasWeakDerivOn.hasWeakFDerivOn`: on the line, a weak
  derivative $w$ of $f$ is the same as the weak derivative $x \mapsto (t \mapsto t\,w(x))$ in the
  sense of linear maps.
* `memSobolevIntervalLp_iff_memSobolev`: a function lies in $W^{m,p}(I)$ in one formulation if and
  only if it lies in it in the other.
* `SobolevIntervalLp.sobolevNorm_eq`: the norm of $u \in W^{1,p}(I)$ is the Sobolev norm
  `sobolevNorm` of its function.
* `SobolevIntervalLp.exists_seq_contDiff_hasCompactSupport_tendsto`: every $u \in W^{1,p}(I)$,
  $1 \le p < \infty$, is the limit in $W^{1,p}(I)$ of restrictions to $I$ of functions of
  $C_c^\infty(\mathbb{R})$ (Theorem 8.7 of [brezis2011functional]).
* `SobolevIntervalLp.dense_contDiff_hasCompactSupport`: the same statement as the density of a set.
* `SobolevIntervalLp.hasWeakDerivOn_convolution` and
  `SobolevIntervalLp.memSobolevIntervalLp_convolution`: $(\rho * v)' = \rho * v'$ and
  $\rho * v \in W^{1,p}(\mathbb{R})$ for $\rho \in L^1(\mathbb{R})$ and $v \in W^{1,p}(\mathbb{R})$
  (Lemma 8.4 of [brezis2011functional]).

## Proof outline

The density theorem is not proved again by the mollification and cut-off argument of
[brezis2011functional]. That argument proves the density theorem on the whole space, which is
`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`. Here $u \in W^{1,p}(I)$ is extended
to $Pu \in W^{1,p}(\mathbb{R})$ by the extension operator `SobolevIntervalLp.extensionCLM` (Theorem
8.6 of [brezis2011functional]). The whole-space theorem approximates $Pu$ by functions of
$C_c^\infty(\mathbb{R})$, and restriction to $I$ (`SobolevMultiIndex.restrictL`) does not increase
the norm. The comparison of the norms is `SobolevIntervalLp.sobolevNorm_eq`.

Lemma 8.4 is the one-dimensional case of Lemma 9.1 of [brezis2011functional],
`HasWeakIteratedLineDerivOn.convolution_of_integrable`. The density theorem does not use it.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal Topology

noncomputable section

/-! ### The two formulations of the first weak derivative on the line -/

section Bridge

variable {I : Opens ℝ} {f w : ℝ → ℝ}

/-- Let $I \subseteq \mathbb{R}$ be open and let $f : \mathbb{R} \to \mathbb{R}$. If a family of
linear maps $W(x) : \mathbb{R} \to \mathbb{R}$ is a weak derivative of $f$ on $I$ in the sense
of linear maps (`HasWeakFDerivOn`), then $x \mapsto W(x)(1)$ is a weak derivative of $f$ on $I$
in the sense of `HasWeakDerivOn`. -/
theorem HasWeakFDerivOn.hasWeakDerivOn {W : ℝ → ℝ →L[ℝ] ℝ} (h : HasWeakFDerivOn f W I volume) :
    HasWeakDerivOn f (fun x ↦ W x 1) I := by
  have := h.lineDeriv (fun _ : Fin 1 ↦ (1 : ℝ))
  simpa only [continuousMultilinearCurryFin1_symm_apply] using this

/-- Let $I \subseteq \mathbb{R}$ be open. If $w$ is a weak derivative of $f$ on $I$
(`HasWeakDerivOn`), then $x \mapsto (t \mapsto t\,w(x))$ is a weak derivative of $f$ on $I$ in
the sense of linear maps (`HasWeakFDerivOn`).

On $\mathbb{R}$ the Fréchet derivative of a test function $\varphi$ in the direction $v$ is
$v\,\varphi'$, which gives the identification. -/
theorem HasWeakDerivOn.hasWeakFDerivOn (h : HasWeakDerivOn f w I) :
    HasWeakFDerivOn f (fun x ↦ ContinuousLinearMap.toSpanSingleton ℝ (w x)) I volume := by
  obtain ⟨h1, h2, h3⟩ := hasWeakDerivOn_iff.1 h
  refine hasWeakFDerivOn_iff.2 ⟨h1, ?_, fun φ v ↦ ?_⟩
  · exact h2.comp_continuousLinearMap
      (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  · have e1 : ∀ x, fderiv ℝ φ x v • f x = v * (deriv φ x * f x) := fun x ↦ by
      rw [fderiv_eq_smul_deriv, smul_eq_mul, smul_eq_mul, mul_assoc]
    have e2 : ∀ x, φ x • ContinuousLinearMap.toSpanSingleton ℝ (w x) v = v * (φ x * w x) :=
      fun x ↦ by rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, smul_eq_mul]; ring
    simp only [e1, e2, integral_const_mul, h3 φ, mul_neg]

/-- **The two formulations of $W^{m,p}(I)$ agree.** Let $I \subseteq \mathbb{R}$ be open,
$m \in \mathbb{N}$ and $p \in [0, \infty]$. Then `MemSobolevIntervalLp f m p I` holds if and
only if `MemSobolev f m p I volume` holds: a function $f$ lies in $W^{m,p}(I)$ in one
formulation if and only if it lies in $W^{m,p}(I)$ in the other.

`MemSobolevIntervalLp` is the multi-index formulation on the one-element basis of $\mathbb{R}$.
`MemSobolev` collects the weak derivatives of order $k$ into $k$-linear maps. -/
theorem memSobolevIntervalLp_iff_memSobolev {m : ℕ} {p : ℝ≥0∞} :
    MemSobolevIntervalLp f m p I ↔ MemSobolev f m p I volume :=
  (memSobolev_iff_memSobolevMultiIndex (Module.Basis.singleton Unit ℝ)).symm

end Bridge

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {I : Opens ℝ} {m : ℕ}

/-- Let $I \subseteq \mathbb{R}$ be open. For $u \in W^{m,p}(I)$, the function of $u$ lies in
$W^{m,p}(I)$ in the sense of `MemSobolev`. -/
theorem memSobolev_fn (u : SobolevIntervalLp m p I) : MemSobolev (fn u) m p I volume :=
  memSobolevIntervalLp_iff_memSobolev.1 (memSobolevIntervalLp_fn u)

/-- Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$ and $u \in W^{m,p}(I)$. The weak
derivative of order $0$ of the function of $u$ that `weakIteratedFDeriv` chooses is that
function itself, read as a $0$-linear map, almost everywhere on $I$. -/
theorem weakIteratedFDeriv_zero_ae_eq [Fact (1 ≤ p)] (u : SobolevIntervalLp m p I) :
    weakIteratedFDeriv 0 (fn u) I volume =ᵐ[volume.restrict (I : Set ℝ)]
      fun x ↦ (continuousMultilinearCurryFin0 ℝ ℝ ℝ).symm (fn u x) :=
  (ae_restrict_iff' I.isOpen.measurableSet).2
    (hasWeakIteratedFDerivOn_zero (μ := volume)
      ((memLp_deriv u 0).locallyIntegrableOn Fact.out)).weakIteratedFDeriv_ae_eq

/-- Let $I \subseteq \mathbb{R}$ be open and $u \in W^{m+1,p}(I)$. The weak derivative of order $1$
of the function of $u$ that `weakIteratedFDeriv` chooses is, almost everywhere on $I$, the
linear map $t \mapsto t\,u'(x)$, read as a $1$-linear map. -/
theorem weakIteratedFDeriv_one_ae_eq (u : SobolevIntervalLp (m + 1) p I) :
    weakIteratedFDeriv 1 (fn u) I volume =ᵐ[volume.restrict (I : Set ℝ)]
      fun x ↦ (continuousMultilinearCurryFin1 ℝ ℝ ℝ).symm
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv u 1 x)) :=
  (ae_restrict_iff' I.isOpen.measurableSet).2
    (HasWeakDerivOn.hasWeakFDerivOn (hasWeakDerivOn_deriv_succ u 0)).weakIteratedFDeriv_ae_eq

/-- Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$, $u \in W^{1,p}(I)$ and
$j \in \{0, 1\}$. The $L^p(I)$ norm of the weak derivative of order $j$ of the function of $u$
that `weakIteratedFDeriv` chooses is $\|u^{(j)}\|_{L^p(I)}$. -/
theorem eLpNorm_weakIteratedFDeriv_eq [Fact (1 ≤ p)] (u : SobolevIntervalLp 1 p I) (j : Fin 2) :
    eLpNorm (weakIteratedFDeriv j (fn u) I volume) p (volume.restrict (I : Set ℝ))
      = ‖deriv u j‖ₑ := by
  rw [Lp.enorm_def]
  have hmeas : AEStronglyMeasurable (weakIteratedFDeriv j (fn u) I volume)
      (volume.restrict (I : Set ℝ)) :=
    ((memSobolev_fn u).memLp_weakIteratedFDeriv (Fin.is_le j)).aestronglyMeasurable
  refine eLpNorm_congr_norm_ae hmeas (Lp.aestronglyMeasurable _) ?_
  fin_cases j
  · filter_upwards [weakIteratedFDeriv_zero_ae_eq u] with x hx
    rw [hx, LinearIsometryEquiv.norm_map]
    rfl
  · filter_upwards [weakIteratedFDeriv_one_ae_eq u] with x hx
    rw [hx, LinearIsometryEquiv.norm_map, ContinuousLinearMap.norm_toSpanSingleton]
    rfl

variable [Fact (1 ≤ p)]

/-- **The norm of $W^{m,p}(I)$ for $p < \infty$.** Let $I \subseteq \mathbb{R}$ be open,
$1 \le p < \infty$ and $u \in W^{m,p}(I)$. Then
$$\|u\|_{W^{m,p}(I)} = \Big(\sum_{j=0}^{m} \|u^{(j)}\|_{L^p(I)}^p\Big)^{1/p}.$$

The identity is stated for the extended norms in `ℝ≥0∞`. -/
theorem enorm_eq_sum (hp : p ≠ ⊤) (u : SobolevIntervalLp m p I) :
    ‖u‖ₑ = (∑ j : Fin (m + 1), ‖deriv u j‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [← ofReal_norm, norm_eq_sum hp,
    ← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity) (by positivity),
    ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity]
  refine congrArg (· ^ (1 / p.toReal)) (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ofReal_norm]

omit [Fact (1 ≤ p)] in
/-- **The norm of $W^{m,\infty}(I)$.** Let $I \subseteq \mathbb{R}$ be open and
$u \in W^{m,\infty}(I)$. Then
$$\|u\|_{W^{m,\infty}(I)} = \max_{0 \le j \le m} \|u^{(j)}\|_{L^\infty(I)}.$$

The identity is stated for the extended norms in `ℝ≥0∞`. -/
theorem enorm_eq_iSup (u : SobolevIntervalLp m ⊤ I) :
    ‖u‖ₑ = ⨆ j : Fin (m + 1), ‖deriv u j‖ₑ := by
  have hne : (⨆ j : Fin (m + 1), ‖deriv u j‖ₑ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑ j : Fin (m + 1), ‖deriv u j‖ₑ) ?_ ?_
    · exact ENNReal.sum_ne_top.2 fun _ _ ↦ enorm_ne_top
    · exact iSup_le fun j ↦ Finset.single_le_sum (f := fun j ↦ ‖deriv u j‖ₑ)
        (fun _ _ ↦ zero_le) (Finset.mem_univ j)
  rw [← ofReal_norm, norm_eq_ciSup, ← ENNReal.ofReal_toReal hne,
    ENNReal.toReal_iSup fun _ ↦ enorm_ne_top]
  simp only [toReal_enorm]

/-- Let $I \subseteq \mathbb{R}$ be open, $1 \le p \le \infty$ and $u \in W^{1,p}(I)$. The norm of
$u$ in `SobolevIntervalLp 1 p I` equals the Sobolev norm `sobolevNorm` of the function of $u$ in
the formulation of `Numlib.Analysis.Sobolev.Domain`.

In dimension one the derivative of $u$ at $x$ in that formulation is the linear map
$t \mapsto t\,u'(x)$, whose operator norm is $|u'(x)|$. Therefore the two $\ell^p$ sums of
$L^p(I)$ norms (the two maxima at $p = \infty$) agree term by term. The identity is stated for
the extended norm in `ℝ≥0∞`. -/
theorem sobolevNorm_eq (u : SobolevIntervalLp 1 p I) :
    sobolevNorm (fn u) 1 p I volume = ‖u‖ₑ := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · simp only [sobolevNorm, ↓reduceIte, enorm_eq_iSup]
    exact iSup_congr fun j ↦ eLpNorm_weakIteratedFDeriv_eq u j
  · simp only [sobolevNorm, hp, ↓reduceIte, enorm_eq_sum hp]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by rw [eLpNorm_weakIteratedFDeriv_eq u j]

/-! ### Theorem 8.7: density of $C_c^\infty(\mathbb{R})$ in $W^{1,p}(I)$ -/

/-- Let $1 \le p < \infty$, let $I \subseteq \mathbb{R}$ be a nonempty open interval and let
$u \in W^{1,p}(I)$. Then there are functions $g_n \in C_c^\infty(\mathbb{R})$ and elements
$v_n \in W^{1,p}(I)$ such that $v_n = g_n$ almost everywhere on $I$ for every $n$ and
$$v_n \to u \quad \text{in } W^{1,p}(I).$$
This is the **density theorem**, Theorem 8.7 of [brezis2011functional].

The extension $Pu \in W^{1,p}(\mathbb{R})$ of $u$ (`SobolevIntervalLp.extensionCLM`, Theorem 8.6
of [brezis2011functional]) is approximated in $W^{1,p}(\mathbb{R})$ by functions of
$C_c^\infty(\mathbb{R})$ (`MemSobolev.exists_seq_hasCompactSupport_tendsto_sobolevNorm`, the
mollification and cut-off argument). The Sobolev norm there is the norm of `SobolevIntervalLp`
by `SobolevIntervalLp.sobolevNorm_eq`, and restriction to $I$ (`SobolevMultiIndex.restrictL`)
does not increase the norm. The hypothesis that $I$ is an interval is
`(I : Set ℝ).OrdConnected`. -/
theorem exists_seq_contDiff_hasCompactSupport_tendsto (hI : (I : Set ℝ).OrdConnected)
    (hne : (I : Set ℝ).Nonempty) (hp : p ≠ ⊤) (u : SobolevIntervalLp 1 p I) :
    ∃ g : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      ∃ v : ℕ → SobolevIntervalLp 1 p I,
        (∀ n, fn (v n) =ᵐ[volume.restrict (I : Set ℝ)] g n) ∧ Tendsto v atTop (𝓝 u) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨P, hP⟩ : ∃ P : SobolevIntervalLp 1 p I →L[ℝ] SobolevIntervalLp 1 p ⊤,
      P = extensionCLM hI hne := ⟨_, rfl⟩
  have hPfn : ∀ w, fn (P w) =ᵐ[volume.restrict (I : Set ℝ)] fn w := by
    intro w
    rw [hP]
    exact fn_extensionCLM hI hne w
  obtain ⟨g, hgs, hgc, hgt⟩ :=
    (memSobolev_fn (P u)).exists_seq_hasCompactSupport_tendsto_sobolevNorm hp1 hp
  choose V hV using fun n ↦ (hgs n).exists_sobolevMultiIndex_of_hasCompactSupport
    (b := Module.Basis.singleton Unit ℝ) (p := p) (Ω := (⊤ : Opens ℝ)) (μ := volume) (hgc n)
  obtain ⟨R, hR⟩ : ∃ R : SobolevIntervalLp 1 p ⊤ →L[ℝ] SobolevIntervalLp 1 p I,
      R = SobolevMultiIndex.restrictL ℝ (Module.Basis.singleton Unit ℝ) 1 p volume
        (le_top : I ≤ ⊤) := ⟨_, rfl⟩
  have hRfn : ∀ w, fn (R w) =ᵐ[volume.restrict (I : Set ℝ)] fn w := by
    intro w
    rw [hR]
    exact SobolevMultiIndex.fn_restrictL _ _
  have hRle : ∀ w, ‖R w‖ ≤ ‖w‖ := by
    intro w
    rw [hR]
    exact SobolevMultiIndex.norm_restrictL_apply_le _ _
  refine ⟨g, hgs, hgc, fun n ↦ R (V n), fun n ↦ ?_, ?_⟩
  · exact (hRfn _).trans (ae_mono (Measure.restrict_mono le_top le_rfl) (hV n))
  · have hRPu : R (P u) = u := SobolevMultiIndex.ext_of_fn_ae_eq ((hRfn _).trans (hPfn u))
    rw [← hRPu, tendsto_iff_norm_sub_tendsto_zero]
    have hsub : ∀ n, sobolevNorm (fn (V n - P u)) 1 p ⊤ volume
        = sobolevNorm (g n - fn (P u)) 1 p ⊤ volume := fun n ↦
      sobolevNorm_congr_ae ((SobolevMultiIndex.fn_sub _ _).trans
        ((hV n).sub (EventuallyEq.refl _ _)))
    have hbound : ∀ n, ‖R (V n) - R (P u)‖
        ≤ (sobolevNorm (g n - fn (P u)) 1 p ⊤ volume).toReal := by
      intro n
      rw [← map_sub, ← hsub n, sobolevNorm_eq, toReal_enorm]
      exact hRle _
    refine squeeze_zero (fun _ ↦ norm_nonneg _) hbound ?_
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hgt
    simpa [Function.comp_def] using this

/-- Let $1 \le p < \infty$ and let $I \subseteq \mathbb{R}$ be a nonempty open interval. The set of
$v \in W^{1,p}(I)$ that agree almost everywhere on $I$ with some $g \in C_c^\infty(\mathbb{R})$
is dense in $W^{1,p}(I)$. This is Theorem 8.7 of [brezis2011functional], in the form of the
density of a set. -/
theorem dense_contDiff_hasCompactSupport (hI : (I : Set ℝ).OrdConnected)
    (hne : (I : Set ℝ).Nonempty) (hp : p ≠ ⊤) :
    Dense {v : SobolevIntervalLp 1 p I | ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      fn v =ᵐ[volume.restrict (I : Set ℝ)] g} := fun u ↦ by
  obtain ⟨g, hgs, hgc, v, hv, hvt⟩ := exists_seq_contDiff_hasCompactSupport_tendsto hI hne hp u
  exact mem_closure_of_tendsto hvt (Eventually.of_forall fun n ↦ ⟨g n, hgs n, hgc n, hv n⟩)

/-! ### Lemma 8.4: convolution with an integrable kernel -/

/-- Let $1 \le p \le \infty$, $v \in W^{1,p}(\mathbb{R})$ and $\rho \in L^1(\mathbb{R})$. Then
$\rho * v'$ is a weak derivative of $\rho * v$ on $\mathbb{R}$. This is Lemma 8.4 of
[brezis2011functional].

The convolution is `ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] fn v`, and $\mathbb{R}$ is the open set
`⊤`. The statement is the one-dimensional case of Lemma 9.1 of [brezis2011functional],
`HasWeakIteratedLineDerivOn.convolution_of_integrable`, which is proved by Fubini's theorem
rather than by the approximation of $\rho$ by continuous kernels of compact support in
[brezis2011functional]. -/
theorem hasWeakDerivOn_convolution (v : SobolevIntervalLp 1 p ⊤) {ρ : ℝ → ℝ}
    (hρ : Integrable ρ) :
    HasWeakDerivOn (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] fn v)
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] deriv v 1) ⊤ :=
  (hasWeakDerivOn_fn v).convolution_of_integrable hρ Fact.out
    (memLp_restrict_top_iff.1 (memLp_deriv v 0)) (memLp_restrict_top_iff.1 (memLp_deriv v 1))

/-- Let $1 \le p \le \infty$, $v \in W^{1,p}(\mathbb{R})$ and $\rho \in L^1(\mathbb{R})$. Then
$\rho * v \in W^{1,p}(\mathbb{R})$. This is Lemma 8.4 of [brezis2011functional], membership
part.

The functions $\rho * v$ and $\rho * v'$ lie in $L^p(\mathbb{R})$ by Young's inequality, and
$\rho * v'$ is the weak derivative of $\rho * v$ by
`SobolevIntervalLp.hasWeakDerivOn_convolution`. -/
theorem memSobolevIntervalLp_convolution (v : SobolevIntervalLp 1 p ⊤) {ρ : ℝ → ℝ}
    (hρ : Integrable ρ) :
    MemSobolevIntervalLp (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] fn v) 1 p ⊤ :=
  memSobolevIntervalLp_iff_memSobolev.2 ((memSobolev_fn v).convolution_of_integrable hρ Fact.out)

end SobolevIntervalLp

end
