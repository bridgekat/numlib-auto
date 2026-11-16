/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Mollification.lean` and `Numlib/Analysis/Sobolev/Cutoff.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Chart
import Numlib.Analysis.Sobolev.Friedrichs

/-!
# Calculus rules for Sobolev functions

Let $E$ be a finite-dimensional real normed space with an additive Haar measure $\mu$, and let
$\Omega \subseteq E$ be open. This module proves the calculus rules of $W^{1,p}(\Omega)$ in §9.1 of
[brezis2011functional]: the product rule for two bounded functions (Proposition 9.4), the chain rule
$\partial(G \circ u) = G'(u) \, \partial u$ for $G \in C^1(\mathbb{R})$ with $G(0) = 0$ and $G'$
bounded (Proposition 9.5), and the change of variables $u \mapsto u \circ H$ under a $C^1$
diffeomorphism $H$ with bounded Jacobians (Proposition 9.6), with the identity
$$\partial(u \circ H)(y) = \partial u(H(y)) \circ DH(y).$$
It also proves the change of variables at every order, for affine maps and for diffeomorphisms whose
inverse is of class $C^k$, and it shows that the positive part $u^+ = \max(u, 0)$ of a $W^{1,p}$
function lies in $W^{1,p}$, with $\partial_i u^+ = 1_{\{u > 0\}} \, \partial_i u$.

The change of variables rests on the transport of $L^p$ norms, $\|f \circ H\|_{L^p(A)} \le D^{1/p}
\|f\|_{L^p(H(A))}$ for a bound $D$ on $|\det DH^{-1}|$, which comes from Mathlib's change of
variables formula for the Lebesgue integral. Step (b) of the proof of Theorem 9.7 of
[brezis2011functional] (the extension theorem) uses this change of variables. The module also
defines the truncation functions of Stampacchia's method from the proof of Theorem 9.27 of
[brezis2011functional], and the auxiliary function of the proof of Proposition 9.29 there.

## Main definitions

* `SobolevMultiIndex.compDiffeo`, `SobolevMultiIndex.compDiffeoL`: the change of variables
  $u \mapsto u \circ H$ from $W^{1,p}(\Omega)$ to $W^{1,p}(\Omega')$, as a function and as a bounded
  linear map.
* `SobolevEuclidean.compDiffeoL`: the same bounded linear map for open subsets of $\mathbb{R}^N$.
* `sqCutoff`: a $C^1$ function that equals $t^2$ on $[-M, M]$ and has a derivative bounded by $2M$.
* `posPartApprox`: the $C^1$ approximation $G_\varepsilon(s) = \sqrt{\max(s, 0)^2 + \varepsilon^2} -
  \varepsilon$ of the positive part.
* `IsStampacchiaTruncation`: the conditions on a truncation function $G$ of Stampacchia's method.
* `stampacchiaTruncation`, `stampacchiaTruncationSqrt`: the truncation
  $G(s) = \int_0^s \min(\max(t, 0), 1) \, dt$ and the function $H(s) = \int_0^s \sqrt{G'(t)} \, dt$.
* `ContinuousLinearEquiv.affineHomeomorph`: the affine map $x \mapsto Tx + c$ as a homeomorphism.

## Main results

* `ContinuousLinearMap.exists_abs_det_le_mul_norm_pow`: $|\det L| \le C \|L\|^N$ for every linear
  map $L$ of $E$, with $N = \dim E$.
* `IsDiffeoOnWithBoundedJacobian.eLpNorm_comp_le`, `IsDiffeoOnWithBoundedJacobian.memLp_comp`: the
  transport of $L^p$ norms and of $L^p$ membership under a diffeomorphism with bounded Jacobians.
* `HasWeakFDerivOn.comp_diffeoOn`: the identity of Proposition 9.6 for a locally integrable function
  with a locally integrable weak derivative.
* `MemSobolev.comp_diffeoOn`: Proposition 9.6, $u \circ H \in W^{1,p}(\Omega')$ for
  $u \in W^{1,p}(\Omega)$.
* `MemSobolevMultiIndex.comp_diffeoOn_of_order`: $w \circ J \in W^{k,p}(\Omega)$ for
  $w \in W^{k,p}(\Omega')$, when the inverse $J$ of the diffeomorphism is of class $C^k$ near
  $\overline{\Omega}$.
* `SobolevMultiIndex.exists_hasWeakFDerivOn_fn`: an element $u$ of $W^{1,p}(\Omega)$ has a weak
  derivative $w$ with $\|w\|_{L^p} \le C_b \sum_i \|\partial_i u\|_{L^p}$.
* `HasWeakIteratedLineDerivOn.contDiff_comp'`: the identity of Proposition 9.5, without hypotheses
  on the exponent.
* `HasWeakIteratedLineDerivOn.mul_of_ae_norm_le`, `MemSobolevMultiIndex.mul_of_ae_norm_le`:
  Proposition 9.4, the product rule for bounded functions.
* `MemSobolevMultiIndex.contDiff_comp`: Proposition 9.5.
* `MemSobolevMultiIndex.posPart`: $u^+ \in W^{1,p}(\Omega)$ for $u \in W^{1,p}(\Omega)$.
* `HasWeakIteratedFDerivOn.comp_affineEquiv`: the affine change of variables for weak derivatives of
  every order.

## Proof outline

The identity of Proposition 9.6 is local. On an open set $\omega'$ with compact closure in
$\Omega'$, the function $u$ is approximated in $W^{1,1}$ of a neighbourhood of
$H(\overline{\omega'})$ by smooth functions, the classical chain rule holds for the approximants,
the transport of $L^1$ norms carries the convergence to $\omega'$, and the weak derivative is closed
under $L^1$ limits. So the identity needs no $L^p$ hypothesis. Proposition 9.4 follows from the
chain rule by the polarization identity $uv = \frac{1}{2}((u + v)^2 - u^2 - v^2)$: the square of a
function bounded by $M$ is its composition with `sqCutoff`. This replaces the approximation argument
of the source at the endpoint $L^p \times L^\infty$. The positive part is the limit
$\varepsilon \to 0$ of the chain rule for $G_\varepsilon$, by dominated convergence.

## Implementation notes

* The statements on functions are over a finite-dimensional real normed space $E$ with an additive
  Haar measure $\mu$. The change of variables is for a map $H : E \to E$ of the same space, because
  Mathlib's Jacobian formula is stated for this case and the charts of
  `Numlib.Analysis.Sobolev.Chart` have this form. The hypotheses on $H$ are the structure
  `IsDiffeoOnWithBoundedJacobian` of `Numlib.Analysis.Sobolev.Chart`. A chart restricted to $Q_+$
  satisfies them.
* The bounded linear maps follow the pattern of `Numlib.Analysis.Sobolev.Operators`: first the
  membership and the bound for functions, then `MemSobolevMultiIndex.exists_sobolevMultiIndex` and
  `SobolevMultiIndex.ext_of_fn_ae_eq`. The bound by the operator norm of a bundled map is
  `ContinuousLinearMap.le_opNorm`. Only the $L^p$ bound on the function is stated separately,
  because the extension theorem uses it.
* A first derivative appears in two forms: as a tensor $w : E \to \mathcal{L}(E, F)$
  (`HasWeakFDerivOn`), and as the partial derivatives $\partial_i u = w(\cdot)(b_i)$ along a basis
  $b$ (`SobolevMultiIndex`). `SobolevMultiIndex.exists_hasWeakFDerivOn_fn` compares the two.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

noncomputable section

/-! ### The determinant is bounded by a power of the norm -/

section Det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The determinant of a linear map is bounded by a constant times a power of its norm: there is
$C \ge 0$ such that
$$|\det L| \le C \|L\|^N$$
for every continuous linear map $L : E \to E$, where $N = \dim E$.

The determinant is continuous, so it is bounded on the unit ball of the finite-dimensional space
of linear maps, and it is homogeneous of degree $N$. -/
theorem ContinuousLinearMap.exists_abs_det_le_mul_norm_pow :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : E →L[ℝ] E, |L.det| ≤ C * ‖L‖ ^ finrank ℝ E := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) 1).exists_bound_of_continuousOn
    ContinuousLinearMap.continuous_det.continuousOn
  refine ⟨max C 1, zero_le_one.trans (le_max_right _ _), fun L ↦ ?_⟩
  rcases eq_or_ne L 0 with rfl | hL
  · have h0 : (0 : E →L[ℝ] E).det = (0 : ℝ) ^ finrank ℝ E := by
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero]
    rw [h0, norm_zero, abs_pow, abs_zero]
    exact le_mul_of_one_le_left (pow_nonneg le_rfl _) (le_max_right _ _)
  · have hn : 0 < ‖L‖ := norm_pos_iff.2 hL
    have hunit : ‖L‖⁻¹ • L ∈ closedBall (0 : E →L[ℝ] E) 1 := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 := hC _ hunit
    have hdet : L.det = ‖L‖ ^ finrank ℝ E * (‖L‖⁻¹ • L).det := by
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul]
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn.ne', one_pow, one_mul]
    rw [hdet, abs_mul, abs_pow, abs_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).symm.trans_le
      (h1.trans (le_max_left _ _))) (pow_nonneg (norm_nonneg _) _)

end Det

/-! ### Transport of $L^p$ norms under a diffeomorphism with bounded Jacobians -/

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {H Hinv : E → E} {s t : Set E} {M : ℝ}

namespace IsDiffeoOnWithBoundedJacobian

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with bounded Jacobians. The image $H(A)$ of an
open set $A \subseteq s$ is open. -/
theorem isOpen_image (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E} (hA : IsOpen A)
    (hAs : A ⊆ s) : IsOpen (H '' A) :=
  (h.restrict hA hAs).isOpen_target

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with bounded Jacobians. For $A \subseteq s$,
the image $H(A)$ lies in $t$. -/
theorem image_subset (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E} (hAs : A ⊆ s) :
    H '' A ⊆ t :=
  (h.bijOn.mapsTo.mono_left hAs).image_subset

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with bounded Jacobians and inverse $H^{-1}$
(`Hinv`). For $A \subseteq s$, $H^{-1}(H(A)) = A$. -/
theorem invFun_image_image (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E}
    (hAs : A ⊆ s) : Hinv '' (H '' A) = A :=
  (h.invOn.1.mono hAs).image_image

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with bounded Jacobians and inverse $H^{-1}$.
For $A \subseteq t$ and $x \in A$, the map $H^{-1}$ has the derivative $DH^{-1}(x)$ at $x$
within $A$.

Here $DH^{-1}(x)$ is the ordinary derivative `fderiv ℝ Hinv x`. -/
theorem hasFDerivWithinAt_invFun (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E}
    (hAt : A ⊆ t) {x : E} (hx : x ∈ A) : HasFDerivWithinAt Hinv (fderiv ℝ Hinv x) A x :=
  ((h.contDiffOn_invFun.differentiableOn one_ne_zero).differentiableAt
    (h.isOpen_target.mem_nhds (hAt hx))).hasFDerivAt.hasFDerivWithinAt

omit [MeasurableSpace E] [BorelSpace E] in
/-- Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with bounded Jacobians and inverse $H^{-1}$.
There is $D \ge 0$ with $|\det DH^{-1}(x)| \le D$ for every $x \in t$.

The bound follows from the bound on $\|DH^{-1}\|$ and
`ContinuousLinearMap.exists_abs_det_le_mul_norm_pow`. -/
theorem exists_abs_det_fderiv_invFun_le (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ t, |(fderiv ℝ Hinv x).det| ≤ D := by
  obtain ⟨C, hC0, hC⟩ := ContinuousLinearMap.exists_abs_det_le_mul_norm_pow (E := E)
  refine ⟨C * max M 0 ^ finrank ℝ E, by positivity, fun x hx ↦ (hC _).trans ?_⟩
  gcongr
  exact (h.norm_fderiv_invFun_le x hx).trans (le_max_left _ _)

/-- Almost everywhere statements pull back along a diffeomorphism. Let $H$ be a $C^1$ diffeomorphism
of $s$ onto $t$ with bounded Jacobians, and let $A \subseteq s$ be open. If a property $P$ holds
for $\mu$-almost every $x \in H(A)$, then $P(H(y))$ holds for $\mu$-almost every $y \in A$.

The inverse $H^{-1}$ is differentiable on $t$, so it maps null sets to null sets. -/
theorem ae_comp (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E} (hA : IsOpen A)
    (hAs : A ⊆ s) {P : E → Prop} (hP : ∀ᵐ x ∂μ.restrict (H '' A), P x) :
    ∀ᵐ y ∂μ.restrict A, P (H y) := by
  rw [ae_iff, Measure.restrict_apply' (h.isOpen_image hA hAs).measurableSet] at hP
  rw [ae_iff, Measure.restrict_apply' hA.measurableSet]
  refine measure_mono_null ?_ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
    ((h.contDiffOn_invFun.differentiableOn one_ne_zero).mono
      (inter_subset_right.trans (h.image_subset hAs))) hP)
  rintro y ⟨hy, hyA⟩
  exact ⟨H y, ⟨hy, mem_image_of_mem H hyA⟩, h.invOn.1 (hAs hyA)⟩

/-- Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with bounded Jacobians, and let
$A \subseteq s$ be open. If $f$ is almost everywhere strongly measurable on $H(A)$, then
$f \circ H$ is almost everywhere strongly measurable on $A$. -/
theorem aestronglyMeasurable_comp (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E}
    (hA : IsOpen A) (hAs : A ⊆ s) {F : Type*} [TopologicalSpace F]
    {f : E → F} (hf : AEStronglyMeasurable f (μ.restrict (H '' A))) :
    AEStronglyMeasurable (fun y ↦ f (H y)) (μ.restrict A) := by
  obtain ⟨g, hg, hfg⟩ := hf
  have hH : AEMeasurable H (μ.restrict A) :=
    (h.contDiffOn.continuousOn.mono hAs).aemeasurable hA.measurableSet
  have hfg' : (fun y ↦ f (H y)) =ᵐ[μ.restrict A] fun y ↦ g (H y) := h.ae_comp hA hAs hfg
  exact ((hg.aestronglyMeasurable (μ := (μ.restrict A).map H)).comp_aemeasurable hH).congr
    hfg'.symm

/-- **Transport of the Lebesgue integral.** Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with
bounded Jacobians and inverse $H^{-1}$, let $|\det DH^{-1}(x)| \le D$ for all $x \in t$, and let
$A \subseteq s$ be open. Then for every function $g : E \to [0, \infty]$,
$$\int_A g(H(y)) \, d\mu(y) \le D \int_{H(A)} g \, d\mu.$$

The factor $D$ is `ENNReal.ofReal D`. The proof applies Mathlib's change of variables formula
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` to $H^{-1}$ on $H(A)$. -/
theorem lintegral_comp_le (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {D : ℝ}
    (hD : ∀ x ∈ t, |(fderiv ℝ Hinv x).det| ≤ D) {A : Set E} (hA : IsOpen A) (hAs : A ⊆ s)
    (g : E → ℝ≥0∞) : ∫⁻ y in A, g (H y) ∂μ ≤ ENNReal.ofReal D * ∫⁻ x in H '' A, g x ∂μ := by
  have hB : MeasurableSet (H '' A) := (h.isOpen_image hA hAs).measurableSet
  have hBt : H '' A ⊆ t := h.image_subset hAs
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hB
    (fun x hx ↦ h.hasFDerivWithinAt_invFun hBt hx) (h.invOn.2.injOn.mono hBt) fun y ↦ g (H y)
  rw [h.invFun_image_image hAs] at key
  rw [key, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem hB] with x hx
  rw [h.invOn.2 (hBt hx)]
  gcongr
  exact hD x (hBt hx)

/-- **Transport of $L^p$ norms under a diffeomorphism with bounded Jacobians.** Let $H$ be a $C^1$
diffeomorphism of $s$ onto $t$ with bounded Jacobians and inverse $H^{-1}$, let
$|\det DH^{-1}(x)| \le D$ for all $x \in t$, and let $A \subseteq s$ be open. If $f : E \to F$
is almost everywhere strongly measurable on $H(A)$, then for every $p \in [0, \infty]$
$$\|f \circ H\|_{L^p(A)} \le D^{1/p} \|f\|_{L^p(H(A))}.$$
This is the transport of $L^p$ norms in footnote 6 of Proposition 9.6 of [brezis2011functional].

The constant is `ENNReal.ofReal D ^ (1 / p.toReal)`. The exponent `1 / p.toReal` is $0$ at
$p = \infty$, so there the constant is $1$ and the statement is the transport of essential
bounds. -/
theorem eLpNorm_comp_le (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {D : ℝ}
    (hD : ∀ x ∈ t, |(fderiv ℝ Hinv x).det| ≤ D) {A : Set E} (hA : IsOpen A) (hAs : A ⊆ s)
    {F : Type*} [NormedAddCommGroup F] {f : E → F}
    (hf : AEStronglyMeasurable f (μ.restrict (H '' A))) (p : ℝ≥0∞) :
    eLpNorm (fun y ↦ f (H y)) p (μ.restrict A)
      ≤ ENNReal.ofReal D ^ (1 / p.toReal) * eLpNorm f p (μ.restrict (H '' A)) := by
  have hf' := h.aestronglyMeasurable_comp hA hAs hf
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hf']
    exact zero_le
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [eLpNorm_exponent_top hf', eLpNorm_exponent_top hf, ENNReal.toReal_top, div_zero,
      ENNReal.rpow_zero, one_mul]
    exact eLpNormEssSup_le_of_ae_enorm_bound (h.ae_comp hA hAs (ae_le_eLpNormEssSup (f := f)))
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf',
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf,
      ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    exact h.lintegral_comp_le hD hA hAs fun x ↦ ‖f x‖ₑ ^ p.toReal

/-- Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with bounded Jacobians and inverse $H^{-1}$,
let $|\det DH^{-1}(x)| \le D$ for all $x \in t$, and let $A \subseteq s$ be open. If
$f \in L^p(H(A))$, then $f \circ H \in L^p(A)$. -/
theorem memLp_comp (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {D : ℝ}
    (hD : ∀ x ∈ t, |(fderiv ℝ Hinv x).det| ≤ D) {A : Set E} (hA : IsOpen A) (hAs : A ⊆ s)
    {F : Type*} [NormedAddCommGroup F] {f : E → F} {p : ℝ≥0∞}
    (hf : MemLp f p (μ.restrict (H '' A))) : MemLp (fun y ↦ f (H y)) p (μ.restrict A) :=
  (h.eLpNorm_comp_le hD hA hAs hf.aestronglyMeasurable p).trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) hf)

/-- Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with bounded Jacobians. If $f$ is locally
integrable on $t$, then $f \circ H$ is locally integrable on $s$. -/
theorem locallyIntegrableOn_comp (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M)
    {F : Type*} [NormedAddCommGroup F] {f : E → F} (hf : LocallyIntegrableOn f t μ) :
    LocallyIntegrableOn (fun y ↦ f (H y)) s μ := by
  obtain ⟨D, -, hD⟩ := h.exists_abs_det_fderiv_invFun_le
  intro y hy
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 h.isOpen_source y hy
  have hcb : closedBall y (ε / 2) ⊆ s := (closedBall_subset_ball (half_lt_self hε)).trans hεs
  refine ⟨ball y (ε / 2), nhdsWithin_le_nhds (ball_mem_nhds y (half_pos hε)), ?_⟩
  have hK : IsCompact (H '' closedBall y (ε / 2)) :=
    (isCompact_closedBall y (ε / 2)).image_of_continuousOn (h.contDiffOn.continuousOn.mono hcb)
  have hint : IntegrableOn f (H '' closedBall y (ε / 2)) μ :=
    hf.integrableOn_compact_subset (h.image_subset hcb) hK
  exact memLp_one_iff_integrable.1 (h.memLp_comp hD isOpen_ball (ball_subset_closedBall.trans hcb)
    (memLp_one_iff_integrable.2 (hint.mono_set (image_mono ball_subset_closedBall))))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [μ.IsAddHaarMeasure] in
/-- Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with bounded Jacobians, let $A \subseteq s$ be
open, and let $g : E \to \mathcal{L}(E, F)$. If $g \circ H$ is almost everywhere strongly
measurable on $A$, then so is $y \mapsto g(H(y)) \circ DH(y)$. This holds for every measure
$\mu$. -/
theorem aestronglyMeasurable_comp_fderiv
    (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E} (hA : IsOpen A) (hAs : A ⊆ s)
    {g : E → E →L[ℝ] F} (hg : AEStronglyMeasurable (fun y ↦ g (H y)) (μ.restrict A)) :
    AEStronglyMeasurable (fun y ↦ (g (H y)).comp (fderiv ℝ H y)) (μ.restrict A) :=
  (ContinuousLinearMap.compL ℝ E E F).continuous₂.comp_aestronglyMeasurable₂ hg
    (((h.contDiffOn.continuousOn_fderiv_of_isOpen h.isOpen_source le_rfl).mono
      hAs).aestronglyMeasurable hA.measurableSet)

omit [μ.IsAddHaarMeasure] in
/-- **The Jacobian factor costs at most $M$ in $L^p$.** Let $H$ be a $C^1$ diffeomorphism of $s$
onto $t$ with Jacobians bounded by $M$, let $A \subseteq s$ be open, and let
$g : E \to \mathcal{L}(E, F)$ with $g \circ H$ almost everywhere strongly measurable on $A$.
Then for every $p \in [0, \infty]$
$$\|y \mapsto g(H(y)) \circ DH(y)\|_{L^p(A)} \le M \|g \circ H\|_{L^p(A)}.$$
This holds for every measure $\mu$.

The factor $M$ is `ENNReal.ofReal M`. -/
theorem eLpNorm_comp_fderiv_le
    (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E} (hA : IsOpen A) (hAs : A ⊆ s)
    {g : E → E →L[ℝ] F} (hg : AEStronglyMeasurable (fun y ↦ g (H y)) (μ.restrict A))
    (p : ℝ≥0∞) :
    eLpNorm (fun y ↦ (g (H y)).comp (fderiv ℝ H y)) p (μ.restrict A)
      ≤ ENNReal.ofReal M * eLpNorm (fun y ↦ g (H y)) p (μ.restrict A) := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (h.aestronglyMeasurable_comp_fderiv hA hAs hg) ?_ p
  filter_upwards [ae_restrict_mem hA.measurableSet] with y hy
  calc ‖(g (H y)).comp (fderiv ℝ H y)‖ ≤ ‖g (H y)‖ * ‖fderiv ℝ H y‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖g (H y)‖ * M := by gcongr; exact h.norm_fderiv_le y (hAs hy)
    _ = M * ‖g (H y)‖ := mul_comm _ _

/-- Let $H$ be a $C^1$ diffeomorphism of $s$ onto $t$ with bounded Jacobians. If
$g : E \to \mathcal{L}(E, F)$ is locally integrable on $t$, then $y \mapsto g(H(y)) \circ DH(y)$
is locally integrable on $s$. -/
theorem locallyIntegrableOn_comp_fderiv (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M)
    {g : E → E →L[ℝ] F} (hg : LocallyIntegrableOn g t μ) :
    LocallyIntegrableOn (fun y ↦ (g (H y)).comp (fderiv ℝ H y)) s μ := by
  have hgH := h.locallyIntegrableOn_comp hg
  intro y hy
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 h.isOpen_source y hy
  have hbs : ball y ε ⊆ s := hεs
  obtain ⟨u, hu, hint⟩ := hgH y hy
  obtain ⟨u', hu', hu'u⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hu
  obtain ⟨δ, hδ, hδu'⟩ := Metric.mem_nhds_iff.1 hu'
  refine ⟨ball y (min ε δ), nhdsWithin_le_nhds (ball_mem_nhds y (lt_min hε hδ)), ?_⟩
  have hbε : ball y (min ε δ) ⊆ s := (ball_subset_ball (min_le_left _ _)).trans hbs
  have hbu : ball y (min ε δ) ⊆ u := fun z hz ↦
    hu'u ⟨hδu' (ball_subset_ball (min_le_right _ _) hz), hbε hz⟩
  have hint' : MemLp (fun z ↦ g (H z)) 1 (μ.restrict (ball y (min ε δ))) :=
    memLp_one_iff_integrable.2 (hint.mono_set hbu)
  refine memLp_one_iff_integrable.1 ?_
  refine (h.eLpNorm_comp_fderiv_le isOpen_ball hbε hint'.aestronglyMeasurable 1).trans_lt ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint'

end IsDiffeoOnWithBoundedJacobian

end Transport

/-! ### Locality, and local membership in $W^{1,1}$ -/

section Locality

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {μ : Measure E}
  {n : ℕ} {f : E → F} {w : E → E [×n]→L[ℝ] F}

/-- **Locality of the weak derivative.** Let $f$ and $w$ be locally integrable on $\Omega$. If $w$
is an $n$-th weak derivative of $f$ on every open set $\Omega'$ whose closure is compact and
contained in $\Omega$, then $w$ is an $n$-th weak derivative of $f$ on $\Omega$. This holds for
every measure $\mu$.

This is the counterpart of `HasWeakIteratedLineDerivOn.of_forall_isCompact_closure_subset` for
`HasWeakIteratedFDerivOn`, whose weak derivative takes values in the continuous $n$-linear maps. -/
theorem HasWeakIteratedFDerivOn.of_forall_isCompact_closure_subset
    (hf : LocallyIntegrableOn f Ω μ) (hw : LocallyIntegrableOn w Ω μ)
    (h : ∀ Ω' : Opens E, IsCompact (closure (Ω' : Set E)) → closure (Ω' : Set E) ⊆ Ω →
      HasWeakIteratedFDerivOn n f w Ω' μ) :
    HasWeakIteratedFDerivOn n f w Ω μ where
  locallyIntegrableOn := hf
  locallyIntegrableOn_weakDeriv := hw
  integral_smul_eq φ y := by
    obtain ⟨V, -, hVo, hφV, -, hVc, hVΩ, -⟩ :=
      φ.hasCompactSupport.exists_pos_forall_closedBall_subset Ω.isOpen φ.tsupport_subset
    have key := (h ⟨V, hVo⟩ hVc hVΩ).integral_smul_eq'
      ⟨φ, φ.contDiff, φ.hasCompactSupport, hφV⟩ y
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • f x ∂μ
        = ∫ x, iteratedFDeriv ℝ n φ x y • f x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [show iteratedFDeriv ℝ n (φ : E → ℝ) x y = 0 from
          (φ.iteratedFDerivApply n y).eq_zero_of_notMem hx, zero_smul]
    have e2 : ∫ x in (Ω : Set E), φ x • w x y ∂μ = ∫ x, φ x • w x y ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [φ.eq_zero_of_notMem hx, zero_smul]
    rw [e1, e2]
    exact key

omit [FiniteDimensional ℝ E] in
/-- Let $w$ be a first-order weak derivative of $u$ on $\Omega$, and let $V$ be an open set whose
closure is compact and contained in $\Omega$. Then $u \in W^{1,1}(V)$.

Both $u$ and $w$ are integrable on compact subsets of $\Omega$. -/
theorem HasWeakFDerivOn.memSobolev_one_of_isCompact_closure_subset {u : E → F}
    {w : E → E →L[ℝ] F} (hu : HasWeakFDerivOn u w Ω μ) {V : Set E} (hVo : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) : MemSobolev u 1 1 ⟨V, hVo⟩ μ := by
  have hVΩ' : V ⊆ Ω := subset_closure.trans hVΩ
  have hul : IntegrableOn u V μ :=
    (hu.locallyIntegrableOn.integrableOn_compact_subset hVΩ hVc).mono_set subset_closure
  have hwl : IntegrableOn w V μ :=
    (hu.locallyIntegrableOn_weakDeriv.integrableOn_compact_subset hVΩ hVc).mono_set
      subset_closure
  refine ⟨memLp_one_iff_integrable.2 hul, fun n hn ↦ ?_⟩
  have hn' : n ≤ 1 := by exact_mod_cast hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn' with rfl | rfl
  · exact ⟨_, hasWeakIteratedFDerivOn_zero (Ω := ⟨V, hVo⟩) hul.locallyIntegrableOn,
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
        |>.comp_memLp' (memLp_one_iff_integrable.2 hul)⟩
  · exact ⟨_, HasWeakIteratedFDerivOn.mono hu hVΩ',
      (continuousMultilinearCurryFin1 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
        |>.comp_memLp' (memLp_one_iff_integrable.2 hwl)⟩

end Locality

/-! ### Proposition 9.6: the change of variables identity -/

section ChangeOfVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {H Hinv : E → E} {Ω' Ω : Opens E} {M : ℝ} {u : E → F} {w : E → E →L[ℝ] F}

/-- **Change of variables for the weak derivative.** Let $F$ be a Banach space, let $H$ be a $C^1$
diffeomorphism of $\Omega'$ onto $\Omega$ with bounded Jacobians, and let $w$ be a first-order
weak derivative of $u : E \to F$ on $\Omega$. Then $u \circ H$ has on $\Omega'$ the first-order
weak derivative
$$y \mapsto w(H(y)) \circ DH(y).$$
In coordinates this is $\partial_j (u \circ H)(y) = \sum_i \partial_i u(H(y)) \, \partial_j
H_i(y)$, the identity of Proposition 9.6 of [brezis2011functional].

Only local integrability of $u$ and $w$ is assumed, because the identity is local. The proof
approximates $u$ by smooth functions near the compact image of each relatively compact open
subset of $\Omega'$ (`MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`), applies the classical
chain rule and the transport of $L^1$ norms (`IsDiffeoOnWithBoundedJacobian.eLpNorm_comp_le`),
and passes to the limit (`hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one`). This is the proof of
the source with this local approximation in place of Theorem 9.2, and the same locality covers
the case $p = \infty$. -/
theorem HasWeakFDerivOn.comp_diffeoOn (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (hu : HasWeakFDerivOn u w Ω μ) :
    HasWeakFDerivOn (fun y ↦ u (H y)) (fun y ↦ (w (H y)).comp (fderiv ℝ H y)) Ω' μ := by
  obtain ⟨D, -, hD⟩ := h.exists_abs_det_fderiv_invFun_le
  have hul : LocallyIntegrableOn (fun y ↦ u (H y)) Ω' μ :=
    h.locallyIntegrableOn_comp hu.locallyIntegrableOn
  have hwl : LocallyIntegrableOn (fun y ↦ (w (H y)).comp (fderiv ℝ H y)) Ω' μ :=
    h.locallyIntegrableOn_comp_fderiv hu.locallyIntegrableOn_weakDeriv
  obtain ⟨e, he⟩ : ∃ e : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (E [×1]→L[ℝ] F),
    e = (continuousMultilinearCurryFin1 ℝ E F).symm := ⟨_, rfl⟩
  have hu1 : HasWeakIteratedFDerivOn 1 u (fun x ↦ e (w x)) Ω μ := by rw [he]; exact hu
  have hwl' : LocallyIntegrableOn (fun y ↦ e ((w (H y)).comp (fderiv ℝ H y))) Ω' μ :=
    hwl.comp_continuousLinearMap e.toContinuousLinearEquiv.toContinuousLinearMap
  change HasWeakIteratedFDerivOn 1 (fun y ↦ u (H y))
    (fun y ↦ (continuousMultilinearCurryFin1 ℝ E F).symm ((w (H y)).comp (fderiv ℝ H y))) Ω' μ
  rw [← he]
  refine HasWeakIteratedFDerivOn.of_forall_isCompact_closure_subset hul hwl'
    fun ω' hω'c hω'Ω' ↦ ?_
  have hω' : (ω' : Set E) ⊆ Ω' := subset_closure.trans hω'Ω'
  -- the compact image of `ω'` and two relatively compact neighbourhoods of it in `Ω`
  have hK : IsCompact (H '' closure (ω' : Set E)) :=
    hω'c.image_of_continuousOn (h.contDiffOn.continuousOn.mono hω'Ω')
  have hKΩ : H '' closure (ω' : Set E) ⊆ Ω := h.image_subset hω'Ω'
  obtain ⟨V₁, -, hV₁o, hKV₁, -, hV₁c, hV₁Ω, -⟩ :=
    hK.exists_pos_forall_closedBall_subset Ω.isOpen hKΩ
  obtain ⟨V, -, hVo, hKV, -, hVc, hVV₁, -⟩ := hK.exists_pos_forall_closedBall_subset hV₁o hKV₁
  have hV₁Ω' : V₁ ⊆ Ω := subset_closure.trans hV₁Ω
  have hVV₁' : V ⊆ V₁ := subset_closure.trans hVV₁
  have hω'V : H '' (ω' : Set E) ⊆ V := (image_mono subset_closure).trans hKV
  have hω'V₁ : H '' (ω' : Set E) ⊆ V₁ := hω'V.trans hVV₁'
  -- the smooth approximants of `u` on `V`
  have hmem : MemSobolev u 1 1 ⟨V₁, hV₁o⟩ μ :=
    hu.memSobolev_one_of_isCompact_closure_subset hV₁o hV₁c hV₁Ω
  obtain ⟨g, hgs, hgt, hgdt⟩ :=
    hmem.exists_seq_contDiff_tendsto_eLpNorm le_rfl ENNReal.one_ne_top hVo hVc hVV₁
  obtain ⟨wV, hwV⟩ : ∃ wV, wV = weakIteratedFDeriv 1 u ⟨V₁, hV₁o⟩ μ := ⟨_, rfl⟩
  have hwVae : ∀ᵐ x ∂μ.restrict (H '' (ω' : Set E)), wV x = e (w x) := by
    filter_upwards [ae_restrict_of_ae (hu1.mono (Ω' := ⟨V₁, hV₁o⟩) hV₁Ω').weakIteratedFDeriv_ae_eq,
      ae_restrict_mem (h.isOpen_image ω'.isOpen hω').measurableSet] with x hx hxω'
    rw [hwV]
    exact hx (hω'V₁ hxω')
  have hwVm : AEStronglyMeasurable wV (μ.restrict (H '' (ω' : Set E))) := by
    rw [hwV]
    exact (hmem.memLp_weakIteratedFDeriv le_rfl).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hω'V₁ le_rfl)
  have hgdt' : Tendsto (fun i ↦ eLpNorm (iteratedFDeriv ℝ 1 (g i) - wV) 1 (μ.restrict V)) atTop
      (𝓝 0) := by
    rw [hwV]
    exact hgdt 1 le_rfl
  -- the classical identity for the approximants
  have hclaim : ∀ i, HasWeakIteratedFDerivOn 1 (fun y ↦ g i (H y))
      (fun y ↦ e ((fderiv ℝ (g i) (H y)).comp (fderiv ℝ H y))) ω' μ := by
    intro i
    have hc : ContDiffOn ℝ 1 (fun y ↦ g i (H y)) ω' :=
      ((hgs i).of_le (by simp)).comp_contDiffOn (h.contDiffOn.mono hω')
    refine (ContDiffOn.hasWeakIteratedFDerivOn hc le_rfl).congr_ae (EventuallyEq.refl _ _) ?_
    filter_upwards [ae_restrict_mem ω'.isOpen.measurableSet] with y hy
    rw [iteratedFDeriv_one_eq_symm_fderiv, he]
    congr 1
    exact fderiv_comp y ((hgs i).differentiable (by simp) _)
      ((h.contDiffOn.differentiableOn one_ne_zero).differentiableAt
        (Ω'.isOpen.mem_nhds (hω' hy)))
  refine hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one hclaim (hul.mono_set hω')
    (hwl'.mono_set hω') ?_ ?_
  · -- `g i ∘ H → u ∘ H` in `L^1(ω')`
    have hbound : ∀ i, eLpNorm ((fun y ↦ g i (H y)) - fun y ↦ u (H y)) 1 (μ.restrict ω')
        ≤ ENNReal.ofReal D * eLpNorm (g i - u) 1 (μ.restrict V) := by
      intro i
      have hm : AEStronglyMeasurable (g i - u) (μ.restrict (H '' (ω' : Set E))) :=
        (hgs i).continuous.aestronglyMeasurable.sub
          (hu.locallyIntegrableOn.aestronglyMeasurable.mono_measure
            (Measure.restrict_mono (hω'V₁.trans hV₁Ω') le_rfl))
      have := h.eLpNorm_comp_le hD ω'.isOpen hω' hm 1
      simp only [ENNReal.toReal_one, div_one, ENNReal.rpow_one] at this
      refine this.trans ?_
      gcongr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (?_ : Tendsto (fun i ↦ ENNReal.ofReal D * eLpNorm (g i - u) 1 (μ.restrict V)) atTop (𝓝 0))
      (fun _ ↦ zero_le) hbound
    simpa using ENNReal.Tendsto.const_mul hgt (Or.inr ENNReal.ofReal_ne_top)
  · -- the derivatives converge in `L^1(ω')`
    have hUm : ∀ i, AEStronglyMeasurable
        (fun y ↦ e ((fderiv ℝ (g i) (H y)).comp (fderiv ℝ H y))) (μ.restrict ω') := fun i ↦
      (hclaim i).locallyIntegrableOn_weakDeriv.aestronglyMeasurable
    have hWm : AEStronglyMeasurable
        (fun y ↦ e ((w (H y)).comp (fderiv ℝ H y))) (μ.restrict ω') :=
      (hwl'.mono_set hω').aestronglyMeasurable
    have hbound : ∀ i, eLpNorm ((fun y ↦ e ((fderiv ℝ (g i) (H y)).comp (fderiv ℝ H y)))
          - fun y ↦ e ((w (H y)).comp (fderiv ℝ H y))) 1 (μ.restrict ω')
        ≤ ENNReal.ofReal M * (ENNReal.ofReal D
          * eLpNorm (iteratedFDeriv ℝ 1 (g i) - wV) 1 (μ.restrict V)) := by
      intro i
      have hm : AEStronglyMeasurable (iteratedFDeriv ℝ 1 (g i) - wV)
          (μ.restrict (H '' (ω' : Set E))) :=
        ((hgs i).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable.sub hwVm
      have h1 : eLpNorm ((fun y ↦ e ((fderiv ℝ (g i) (H y)).comp (fderiv ℝ H y)))
            - fun y ↦ e ((w (H y)).comp (fderiv ℝ H y))) 1 (μ.restrict ω')
          ≤ ENNReal.ofReal M
            * eLpNorm (fun y ↦ (iteratedFDeriv ℝ 1 (g i) - wV) (H y)) 1 (μ.restrict ω') := by
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hUm i).sub hWm) ?_ 1
        filter_upwards [ae_restrict_mem ω'.isOpen.measurableSet, h.ae_comp ω'.isOpen hω' hwVae]
          with y hy hyw
        rw [Pi.sub_apply, ← map_sub, e.norm_map, ← ContinuousLinearMap.sub_comp, Pi.sub_apply,
          hyw, iteratedFDeriv_one_eq_symm_fderiv, ← he, ← map_sub, e.norm_map]
        calc ‖(fderiv ℝ (g i) (H y) - w (H y)).comp (fderiv ℝ H y)‖
            ≤ ‖fderiv ℝ (g i) (H y) - w (H y)‖ * ‖fderiv ℝ H y‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖fderiv ℝ (g i) (H y) - w (H y)‖ * M := by
              gcongr; exact h.norm_fderiv_le y (hω' hy)
          _ = M * ‖fderiv ℝ (g i) (H y) - w (H y)‖ := mul_comm _ _
      refine h1.trans ?_
      gcongr
      have := h.eLpNorm_comp_le hD ω'.isOpen hω' hm 1
      simp only [ENNReal.toReal_one, div_one, ENNReal.rpow_one] at this
      refine this.trans ?_
      gcongr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (?_ : Tendsto (fun i ↦ ENNReal.ofReal M * (ENNReal.ofReal D
        * eLpNorm (iteratedFDeriv ℝ 1 (g i) - wV) 1 (μ.restrict V))) atTop (𝓝 0))
      (fun _ ↦ zero_le) hbound
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.const_mul hgdt' (Or.inr ENNReal.ofReal_ne_top))
      (Or.inr ENNReal.ofReal_ne_top)

end ChangeOfVariables

/-! ### Proposition 9.6: membership -/

section Membership

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {H Hinv : E → E} {Ω' Ω : Opens E} {M : ℝ} {p : ℝ≥0∞}

/-- Let $H$ be a $C^1$ diffeomorphism of $\Omega'$ onto $\Omega$ with bounded Jacobians. If a
property $P$ holds almost everywhere on $\Omega$, then $P(H(y))$ holds for almost every
$y \in \Omega'$. -/
theorem IsDiffeoOnWithBoundedJacobian.ae_comp_restrict
    (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) {P : E → Prop}
    (hP : ∀ᵐ x ∂μ.restrict (Ω : Set E), P x) : ∀ᵐ y ∂μ.restrict (Ω' : Set E), P (H y) :=
  h.ae_comp Ω'.isOpen subset_rfl (by rw [h.bijOn.image_eq]; exact hP)

/-- **Change of variables in $W^{1,p}$.** Let $F$ be a Banach space, let $H$ be a $C^1$
diffeomorphism of $\Omega'$ onto $\Omega$ with bounded Jacobians, and let $p \in [0, \infty]$.
If $u \in W^{1,p}(\Omega)$, then $u \circ H \in W^{1,p}(\Omega')$. This is Proposition 9.6 of
[brezis2011functional].

The source states the result for $1 \le p \le \infty$. The statement here has no condition on
$p$, because the identity `HasWeakFDerivOn.comp_diffeoOn` needs only local integrability. The
$L^p$ memberships come from `IsDiffeoOnWithBoundedJacobian.memLp_comp` and the Jacobian bound. -/
theorem MemSobolev.comp_diffeoOn {u : E → F} (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (hu : MemSobolev u 1 p Ω μ) : MemSobolev (fun y ↦ u (H y)) 1 p Ω' μ := by
  obtain ⟨D, -, hD⟩ := h.exists_abs_det_fderiv_invFun_le
  have hΩ' : H '' (Ω' : Set E) = Ω := h.bijOn.image_eq
  obtain ⟨w, hw, hwp⟩ := hu.exists_hasWeakIteratedFDerivOn (n := 1) le_rfl
  obtain ⟨e, he⟩ : ∃ e : (E [×1]→L[ℝ] F) ≃ₗᵢ[ℝ] (E →L[ℝ] F),
    e = continuousMultilinearCurryFin1 ℝ E F := ⟨_, rfl⟩
  have hw' : HasWeakFDerivOn u (fun x ↦ e (w x)) Ω μ := by
    unfold HasWeakFDerivOn
    rw [he]
    simpa using hw
  have hcomp := hw'.comp_diffeoOn h
  have hmemu : MemLp (fun y ↦ u (H y)) p (μ.restrict Ω') :=
    h.memLp_comp hD Ω'.isOpen subset_rfl (by rw [hΩ']; exact hu.memLp)
  have hmemw : MemLp (fun y ↦ e (w (H y))) p (μ.restrict Ω') :=
    h.memLp_comp hD Ω'.isOpen subset_rfl (by
      rw [hΩ']
      exact e.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hwp)
  have hmemW : MemLp (fun y ↦ (e (w (H y))).comp (fderiv ℝ H y)) p (μ.restrict Ω') :=
    (h.eLpNorm_comp_fderiv_le Ω'.isOpen subset_rfl (g := fun x ↦ e (w x))
      hmemw.aestronglyMeasurable p).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmemw)
  refine ⟨hmemu, fun n hn ↦ ?_⟩
  have hn' : n ≤ 1 := by exact_mod_cast hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn' with rfl | rfl
  · exact ⟨_, hasWeakIteratedFDerivOn_zero hcomp.locallyIntegrableOn,
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
        |>.comp_memLp' hmemu⟩
  · exact ⟨_, hcomp,
      (continuousMultilinearCurryFin1 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
        |>.comp_memLp' hmemW⟩

end Membership

/-!
### The tensor weak derivative of an element of the multi-index space

The bounded linear maps below are built from identities for the tensor derivative
(`HasWeakFDerivOn`), while the norm of `SobolevMultiIndex` is the $\ell^p$ sum of the norms of the
partial derivatives $\partial_i u = w(\cdot)(b_i)$. The comparison $\|w\| \le C_b \sum_i \|w(b_i)\|$
(`Module.Basis.opNorm_le`) bounds the tensor by the partial derivatives.
-/

section TensorDerivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E}

namespace SobolevMultiIndex

/-- **The tensor weak derivative of an element of $W^{1,p}(\Omega)$.** Let $F$ be a Banach space,
let $b = (b_i)_{i \in \iota}$ be a basis of $E$, let $p \ge 1$, and let $u \in W^{1,p}(\Omega)$
in the multi-index formulation over $b$, with partial derivatives $\partial_i u$. There is
$w : E \to \mathcal{L}(E, F)$ such that $w$ is a first-order weak derivative of $u$ on $\Omega$,
$w \in L^p(\Omega)$, $w(x)(b_i) = \partial_i u(x)$ for every $i$ and almost every
$x \in \Omega$, and
$$\|w\|_{L^p(\Omega)} \le C_b \sum_{i \in \iota} \|\partial_i u\|_{L^p(\Omega)},$$
where $C_b$ is $|\iota|$ times the norm of the coordinate map $E \to \mathbb{R}^\iota$ of $b$.

The function of $u$ is `SobolevMultiIndex.fn u`, the partial derivative $\partial_i u$ is
`SobolevMultiIndex.weakDeriv u (MultiIndexLE.single i)`, and the coordinate map is
`b.equivFunL`. The constant $C_b$ is the one of `Module.Basis.opNorm_le`. -/
theorem exists_hasWeakFDerivOn_fn (u : SobolevMultiIndex F b 1 p Ω μ) :
    ∃ w : E → E →L[ℝ] F, HasWeakFDerivOn (fn u) w Ω μ ∧ MemLp w p (μ.restrict (Ω : Set E)) ∧
      (∀ i, (fun x ↦ w x (b i)) =ᵐ[μ.restrict (Ω : Set E)] weakDeriv u (MultiIndexLE.single i)) ∧
      eLpNorm w p (μ.restrict (Ω : Set E))
        ≤ ENNReal.ofReal (Fintype.card ι • ‖b.equivFunL.toContinuousLinearMap‖)
          * ∑ i, eLpNorm (weakDeriv u (MultiIndexLE.single i)) p (μ.restrict (Ω : Set E)) := by
  obtain ⟨w, hw, hwp⟩ :=
    (memSobolevMultiIndex u).memSobolev.exists_hasWeakIteratedFDerivOn (n := 1) le_rfl
  obtain ⟨e, he⟩ : ∃ e : (E [×1]→L[ℝ] F) ≃ₗᵢ[ℝ] (E →L[ℝ] F),
    e = continuousMultilinearCurryFin1 ℝ E F := ⟨_, rfl⟩
  have hw' : HasWeakFDerivOn (fn u) (fun x ↦ e (w x)) Ω μ := by
    unfold HasWeakFDerivOn
    rw [he]
    simpa using hw
  have hwp' : MemLp (fun x ↦ e (w x)) p (μ.restrict (Ω : Set E)) :=
    e.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hwp
  have hi : ∀ i, (fun x ↦ e (w x) (b i)) =ᵐ[μ.restrict (Ω : Set E)]
      weakDeriv u (MultiIndexLE.single i) := by
    intro i
    have h1 := (hasWeakIteratedLineDerivOn u (MultiIndexLE.single i)).of_perm
      (multiIndexTuple_single_perm (b : ι → E) i)
    have h2 := (hw' : HasWeakIteratedFDerivOn 1 (fn u) _ Ω μ).lineDeriv ![b i]
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).2 (h2.ae_eq h1)] with x hx
    simpa using hx
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = Fintype.card ι • ‖b.equivFunL.toContinuousLinearMap‖ :=
    ⟨_, rfl⟩
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  have hnorm : ∀ᵐ x ∂μ.restrict (Ω : Set E),
      ‖e (w x)‖ ≤ Cb * ∑ i, ‖weakDeriv u (MultiIndexLE.single i) x‖ := by
    filter_upwards [ae_all_iff.2 hi] with x hx
    rw [hCb]
    refine b.opNorm_le (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) fun i ↦ ?_
    calc ‖e (w x) (b i)‖ = ‖weakDeriv u (MultiIndexLE.single i) x‖ := by rw [hx i]
      _ ≤ ∑ j, ‖weakDeriv u (MultiIndexLE.single j) x‖ :=
          Finset.single_le_sum (f := fun j ↦ ‖weakDeriv u (MultiIndexLE.single j) x‖)
            (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
  refine ⟨fun x ↦ e (w x), hw', hwp', hi, ?_⟩
  rw [← hCb]
  calc eLpNorm (fun x ↦ e (w x)) p (μ.restrict (Ω : Set E))
      ≤ eLpNorm (Cb • fun x ↦ ∑ i, ‖weakDeriv u (MultiIndexLE.single i) x‖) p
          (μ.restrict (Ω : Set E)) :=
        eLpNorm_mono_ae_real hwp'.aestronglyMeasurable hnorm
    _ = ENNReal.ofReal Cb * eLpNorm (fun x ↦ ∑ i, ‖weakDeriv u (MultiIndexLE.single i) x‖) p
          (μ.restrict (Ω : Set E)) := by
        rw [eLpNorm_const_smul, Real.enorm_of_nonneg hCb0]
    _ ≤ ENNReal.ofReal Cb
          * ∑ i, eLpNorm (weakDeriv u (MultiIndexLE.single i)) p (μ.restrict (Ω : Set E)) := by
        gcongr
        have heq : (fun x ↦ ∑ i, ‖weakDeriv u (MultiIndexLE.single i) x‖)
            = ∑ i, fun x ↦ ‖weakDeriv u (MultiIndexLE.single i) x‖ := by
          funext x
          simp
        rw [heq]
        refine (eLpNorm_sum_le Fact.out).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ ↦
          eLpNorm_norm _ (Lp.memLp (weakDeriv u (MultiIndexLE.single i))).aestronglyMeasurable

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- **A bound on the norm of $W^{1,p}(\Omega')$ from bounds on the function and the partial
derivatives.** Let $p \ge 1$, let $u \in W^{1,p}(\Omega)$ and $v \in W^{1,p}(\Omega')$ in the
multi-index formulation over a basis $(b_i)_{i \in \iota}$, and let $A, B \in [0, \infty)$. If
$\|v\|_{L^p(\Omega')} \le A \|u\|_{L^p(\Omega)}$ and $\|\partial_i v\|_{L^p(\Omega')} \le B
\sum_j \|\partial_j u\|_{L^p(\Omega)}$ for every $i$, then
$$\|v\| \le (A + |\iota|^2 B) \, \|u\|.$$

This is the bound on the constants that the bounded linear maps built from an identity for the
tensor derivative share. The numbers $A$ and $B$ are finite elements of `ℝ≥0∞`. -/
theorem norm_le_mul_norm_of_eLpNorm_le {Ω' : Opens E} (v : SobolevMultiIndex F b 1 p Ω' μ)
    (u : SobolevMultiIndex F b 1 p Ω μ) {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (h0 : eLpNorm (fn v) p (μ.restrict (Ω' : Set E))
      ≤ A * eLpNorm (fn u) p (μ.restrict (Ω : Set E)))
    (hi : ∀ i, eLpNorm (weakDeriv v (MultiIndexLE.single i)) p (μ.restrict (Ω' : Set E))
      ≤ B * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p (μ.restrict (Ω : Set E))) :
    ‖v‖ ≤ (A.toReal + Fintype.card ι * (Fintype.card ι * B.toReal)) * ‖u‖ := by
  have hsum : ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p (μ.restrict (Ω : Set E))
      ≤ Fintype.card ι * ENNReal.ofReal ‖u‖ := by
    calc ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p (μ.restrict (Ω : Set E))
        = ∑ j, ENNReal.ofReal ‖weakDeriv u (MultiIndexLE.single j)‖ :=
          Finset.sum_congr rfl fun j _ ↦ by
            rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      _ ≤ ∑ _j : ι, ENNReal.ofReal ‖u‖ :=
          Finset.sum_le_sum fun j _ ↦ ENNReal.ofReal_le_ofReal (norm_weakDeriv_le u _)
      _ = Fintype.card ι * ENNReal.ofReal ‖u‖ := by simp
  have h0r : ‖weakDeriv v 0‖ ≤ A.toReal * ‖u‖ := by
    have h0' : eLpNorm (weakDeriv v 0) p (μ.restrict (Ω' : Set E))
        ≤ A * eLpNorm (weakDeriv u 0) p (μ.restrict (Ω : Set E)) := h0
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hA (Lp.eLpNorm_ne_top _)) h0'
    rw [ENNReal.toReal_mul, ← Lp.norm_def, ← Lp.norm_def] at this
    exact this.trans (mul_le_mul_of_nonneg_left (norm_weakDeriv_le u 0) ENNReal.toReal_nonneg)
  have hir : ∀ i, ‖weakDeriv v (MultiIndexLE.single i)‖ ≤ Fintype.card ι * B.toReal * ‖u‖ := by
    intro i
    have h1 : eLpNorm (weakDeriv v (MultiIndexLE.single i)) p (μ.restrict (Ω' : Set E))
        ≤ B * (Fintype.card ι * ENNReal.ofReal ‖u‖) := by
      refine (hi i).trans ?_
      gcongr
    have hne : B * (Fintype.card ι * ENNReal.ofReal ‖u‖) ≠ ⊤ :=
      ENNReal.mul_ne_top hB (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
    have := ENNReal.toReal_mono hne h1
    rw [← Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (norm_nonneg _)] at this
    linarith [this]
  calc ‖v‖ ≤ ∑ β, ‖weakDeriv v β‖ := norm_le_sum_norm_weakDeriv v
    _ = ‖weakDeriv v 0‖ + ∑ i, ‖weakDeriv v (MultiIndexLE.single i)‖ :=
        MultiIndexLE.sum_univ_one _
    _ ≤ A.toReal * ‖u‖ + ∑ _i : ι, Fintype.card ι * B.toReal * ‖u‖ :=
        add_le_add h0r (Finset.sum_le_sum fun i _ ↦ hir i)
    _ = (A.toReal + Fintype.card ι * (Fintype.card ι * B.toReal)) * ‖u‖ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end SobolevMultiIndex

end TensorDerivative

/-! ### Proposition 9.6 on the typed spaces -/

section TypedCompDiffeo

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {μ : Measure E} [μ.IsAddHaarMeasure] {H Hinv : E → E} {Ω' Ω : Opens E} {M : ℝ}

omit [Fact (1 ≤ p)] in
/-- Let $F$ be a Banach space, let $b$ be a basis of $E$, and let $H$ be a $C^1$ diffeomorphism of
$\Omega'$ onto $\Omega$ with bounded Jacobians. If $u \in W^{1,p}(\Omega)$ in the multi-index
formulation over $b$, then $u \circ H \in W^{1,p}(\Omega')$. This is Proposition 9.6 of
[brezis2011functional] for `MemSobolevMultiIndex`, for every exponent $p$. -/
theorem MemSobolevMultiIndex.comp_diffeoOn {u : E → F}
    (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) (hu : MemSobolevMultiIndex b u 1 p Ω μ) :
    MemSobolevMultiIndex b (fun y ↦ u (H y)) 1 p Ω' μ :=
  (hu.memSobolev.comp_diffeoOn h).memSobolevMultiIndex

variable {N : ℕ} in
open SobolevMultiIndex in
/-- **$W^{k,p}$ is preserved by a $C^k$ diffeomorphism, at every order and exponent.** Let
$k \in \mathbb{N}$ and $1 \le p \le \infty$. Let $H$ be a $C^1$ diffeomorphism of an open set
$\Omega' \subseteq \mathbb{R}^N$ onto an open set $\Omega \subseteq \mathbb{R}^N$ with bounded
Jacobians and inverse $J$. Let $V$ be an open set on which $J$ is of class $C^k$, and let $K$ be
a compact set with $\Omega \subseteq K \subseteq V$. If $w \in W^{k,p}(\Omega')$, then
$w \circ J \in W^{k,p}(\Omega)$.

The Sobolev spaces are `MemSobolevMultiIndex` over the standard basis of $\mathbb{R}^N$ and
Lebesgue measure. The proof is by induction on $k$. It uses the chain rule $\partial_i (w \circ
J) = \sum_l (\partial_i J)_l \, (\partial_l w \circ J)$ (`HasWeakFDerivOn.comp_diffeoOn`), the
inductive hypothesis for $\partial_l w \circ J$, and the multiplier $(\partial_i J)_l$, which is
of class $C^{k-1}$ on $V$ and equals a compactly supported function on $\Omega$
(`MemSobolevMultiIndex.mul_of_isContDiffConstOffCompact`). The theorem
`Elliptic.memSobolevMultiIndex_comp_chart_of_order` of `Numlib.Analysis.PDE.Elliptic.Regularity`
is the same statement for $H^k$. This is the step "by returning to $\Omega \cap U_i$" in the
proof of Theorem 9.25 of [brezis2011functional], §9.6. -/
theorem MemSobolevMultiIndex.comp_diffeoOn_of_order (k : ℕ) :
    ∀ {H J : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)} {M : ℝ}
    {Ω' Ω : Opens (EuclideanSpace ℝ (Fin N))}, IsDiffeoOnWithBoundedJacobian H J Ω' Ω M →
    ∀ {V : Set (EuclideanSpace ℝ (Fin N))}, IsOpen V → ContDiffOn ℝ k J V →
    ∀ {K : Set (EuclideanSpace ℝ (Fin N))}, IsCompact K →
    (Ω : Set (EuclideanSpace ℝ (Fin N))) ⊆ K → K ⊆ V →
    ∀ {w : EuclideanSpace ℝ (Fin N) → ℝ},
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis w k p Ω' volume →
    MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis (fun x ↦ w (J x)) k p Ω
      volume := by
  induction k with
  | zero =>
    intro H J M Ω' Ω h V hV hJ K hK hΩK hKV w hw
    rw [memSobolevMultiIndex_zero_iff] at hw ⊢
    obtain ⟨D, -, hD⟩ := h.symm.exists_abs_det_fderiv_invFun_le
    refine h.symm.memLp_comp hD Ω.isOpen subset_rfl ?_
    rw [h.symm.bijOn.image_eq]
    exact hw
  | succ k ih =>
    intro H J M Ω' Ω h V hV hJ K hK hΩK hKV w hw
    -- the cut-off equal to `1` on `K` with support in `V`
    obtain ⟨χ, hχ, hχ1, hχc, hχV⟩ :=
      hK.exists_contDiff_eqOn_one_hasCompactSupport hV hKV
    -- the coefficients `c i l = (∂ᵢJ)_l`, `C^k` on `V`, and their compactly supported versions
    obtain ⟨c, hc⟩ : ∃ c : Fin N → Fin N → EuclideanSpace ℝ (Fin N) → ℝ,
      c = fun i l x ↦ fderiv ℝ J x (EuclideanSpace.single i 1) l := ⟨_, rfl⟩
    have hdJ : ContDiffOn ℝ k (fderiv ℝ J) V := hJ.fderiv_of_isOpen hV (m := k) (by norm_cast)
    have hcV : ∀ i l, ContDiffOn ℝ k (c i l) V := fun i l ↦ by
      rw [hc]
      exact (EuclideanSpace.proj l).contDiff.comp_contDiffOn (hdJ.clm_apply contDiffOn_const)
    have hmult : ∀ i l, IsContDiffConstOffCompact k fun x ↦ χ x * c i l x := fun i l ↦
      IsContDiffConstOffCompact.of_hasCompactSupport
        ((hχ.of_le (by simp)).mul_contDiffOn_of_tsupport_subset hV (hcV i l) hχV)
        hχc.mul_right
    -- `w ∈ W^{k,p}(Ω')`, its partial derivatives `g l ∈ W^{k,p}(Ω')`, and a tensor derivative `Dw`
    obtain ⟨hw1, hwd⟩ := memSobolevMultiIndex_succ_iff.1 hw
    choose g hg hgp using hwd
    simp only [EuclideanSpace.basisFun_toBasis_apply] at hg
    have hw1' : MemSobolevMultiIndex (EuclideanSpace.basisFun (Fin N) ℝ).toBasis w 1 p Ω' volume :=
      hw.mono_order (by omega)
    obtain ⟨u, hu⟩ : ∃ u : SobolevEuclidean N 1 p Ω',
      fn u =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] w :=
      hw1'.exists_sobolevMultiIndex
    obtain ⟨Dw, hDw, -, hDwi, -⟩ := exists_hasWeakFDerivOn_fn u
    have hDw' : HasWeakFDerivOn w Dw Ω' volume :=
      HasWeakIteratedFDerivOn.congr_ae hDw hu (EventuallyEq.refl _ _)
    have hDwg : ∀ l, (fun y ↦ Dw y (EuclideanSpace.single l 1))
        =ᵐ[volume.restrict (Ω' : Set (EuclideanSpace ℝ (Fin N)))] g l := by
      intro l
      have h1 := (SobolevEuclidean.hasWeakIteratedLineDerivOn_fn_single u l).congr_ae hu
        (EventuallyEq.refl _ _)
      have h2 := (ae_restrict_iff' Ω'.isOpen.measurableSet).2 (h1.ae_eq (hg l))
      have h3 := hDwi l
      rw [EuclideanSpace.basisFun_toBasis_apply] at h3
      exact h3.trans h2
    -- the composite: `W^{k,p}` by the inductive hypothesis, and the derivatives
    have hcomp := hDw'.comp_diffeoOn h.symm
    have hJk : ContDiffOn ℝ k J V := hJ.of_le (by exact_mod_cast Nat.le_succ k)
    refine memSobolevMultiIndex_succ_iff.2 ⟨ih h hV hJk hK hΩK hKV hw1, fun i ↦ ?_⟩
    rw [EuclideanSpace.basisFun_toBasis_apply]
    refine ⟨fun x ↦ ∑ l, χ x * c i l x * g l (J x), ?_, ?_⟩
    · have h1 := (hcomp : HasWeakIteratedFDerivOn 1 _ _ Ω volume).lineDeriv
        ![EuclideanSpace.single i 1]
      refine h1.congr_ae (EventuallyEq.refl _ _) ?_
      have hae : ∀ l, ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin N))),
          Dw (J x) (EuclideanSpace.single l 1) = g l (J x) := fun l ↦
        h.symm.ae_comp_restrict (hDwg l)
      filter_upwards [ae_all_iff.2 hae, self_mem_ae_restrict Ω.isOpen.measurableSet] with x hx hxΩ
      simp only [continuousMultilinearCurryFin1_symm_apply, Matrix.cons_val_zero,
        ContinuousLinearMap.comp_apply]
      rw [ContinuousLinearMap.apply_eq_sum_single (Dw (J x))
        (fderiv ℝ J x (EuclideanSpace.single i 1))]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [hx l, hc, hχ1 (hΩK hxΩ), Pi.one_apply, one_mul]
    · refine MemSobolevMultiIndex.sum_mul_of_isContDiffConstOffCompact Finset.univ
        (c := fun l x ↦ χ x * c i l x) (f := fun l x ↦ g l (J x)) (fun l _ ↦ hmult i l)
        fun l _ ↦ ?_
      exact ih h hV hJk hK hΩK hKV (hgp l)

namespace SobolevMultiIndex

/-- **The change of variables $u \mapsto u \circ H$ of $W^{1,p}$.** Let $F$ be a Banach space, let
$b$ be a basis of $E$, let $p \ge 1$, and let $H$ be a $C^1$ diffeomorphism of $\Omega'$ onto
$\Omega$ with bounded Jacobians. For $u \in W^{1,p}(\Omega)$, `SobolevMultiIndex.compDiffeo h u`
is the element of $W^{1,p}(\Omega')$ whose function is $u \circ H$. This is the map of
Proposition 9.6 of [brezis2011functional].

The element is chosen with `MemSobolevMultiIndex.comp_diffeoOn` and
`MemSobolevMultiIndex.exists_sobolevMultiIndex`. The map is linear and bounded, and
`SobolevMultiIndex.compDiffeoL` is its bundled form. -/
def compDiffeo (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (u : SobolevMultiIndex F b 1 p Ω μ) : SobolevMultiIndex F b 1 p Ω' μ :=
  ((memSobolevMultiIndex u).comp_diffeoOn h).exists_sobolevMultiIndex.choose

omit [Fact (1 ≤ p)] in
/-- The function of `SobolevMultiIndex.compDiffeo h u` equals $u \circ H$ almost everywhere on
$\Omega'$. -/
theorem fn_compDiffeo (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (u : SobolevMultiIndex F b 1 p Ω μ) :
    fn (compDiffeo h u) =ᵐ[μ.restrict (Ω' : Set E)] fun y ↦ fn u (H y) :=
  ((memSobolevMultiIndex u).comp_diffeoOn h).exists_sobolevMultiIndex.choose_spec

omit [Fact (1 ≤ p)] in
/-- The change of variables is additive: $(u + v) \circ H = u \circ H + v \circ H$ in
$W^{1,p}(\Omega')$. -/
theorem compDiffeo_add (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (u v : SobolevMultiIndex F b 1 p Ω μ) :
    compDiffeo h (u + v) = compDiffeo h u + compDiffeo h v := by
  refine ext_of_fn_ae_eq ?_
  have h1 : (fun y ↦ fn (u + v) (H y)) =ᵐ[μ.restrict (Ω' : Set E)]
      fun y ↦ fn u (H y) + fn v (H y) :=
    h.ae_comp_restrict (P := fun x ↦ fn (u + v) x = fn u x + fn v x) (fn_add u v)
  refine (fn_compDiffeo h (u + v)).trans (h1.trans ?_)
  refine EventuallyEq.trans ?_ (fn_add _ _).symm
  filter_upwards [fn_compDiffeo h u, fn_compDiffeo h v] with y hyu hyv
  rw [Pi.add_apply, hyu, hyv]

omit [Fact (1 ≤ p)] in
/-- The change of variables commutes with scalar multiplication: $(cu) \circ H = c \, (u \circ H)$
for $c \in \mathbb{R}$. -/
theorem compDiffeo_smul (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) (c : ℝ)
    (u : SobolevMultiIndex F b 1 p Ω μ) : compDiffeo h (c • u) = c • compDiffeo h u := by
  refine ext_of_fn_ae_eq ?_
  have h1 : (fun y ↦ fn (c • u) (H y)) =ᵐ[μ.restrict (Ω' : Set E)] fun y ↦ c • fn u (H y) :=
    h.ae_comp_restrict (P := fun x ↦ fn (c • u) x = c • fn u x) (fn_smul c u)
  refine (fn_compDiffeo h (c • u)).trans (h1.trans ?_)
  refine EventuallyEq.trans ?_ (fn_smul _ _).symm
  filter_upwards [fn_compDiffeo h u] with y hyu
  rw [Pi.smul_apply, hyu]

omit [Fact (1 ≤ p)] in
/-- **The $L^p$ bound on the change of variables.** Let $|\det DH^{-1}(x)| \le D$ for all
$x \in \Omega$. For $u \in W^{1,p}(\Omega)$,
$$\|u \circ H\|_{L^p(\Omega')} \le D^{1/p} \|u\|_{L^p(\Omega)}.$$

The constant is `ENNReal.ofReal D ^ (1 / p.toReal)`, which is $1$ at $p = \infty$. -/
theorem eLpNorm_fn_compDiffeo_le (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) {D : ℝ}
    (hD : ∀ x ∈ (Ω : Set E), |(fderiv ℝ Hinv x).det| ≤ D) (u : SobolevMultiIndex F b 1 p Ω μ) :
    eLpNorm (fn (compDiffeo h u)) p (μ.restrict (Ω' : Set E))
      ≤ ENNReal.ofReal D ^ (1 / p.toReal) * eLpNorm (fn u) p (μ.restrict (Ω : Set E)) := by
  rw [eLpNorm_congr_ae (fn_compDiffeo h u)]
  have := h.eLpNorm_comp_le hD Ω'.isOpen subset_rfl
    (f := fn u) (by rw [h.bijOn.image_eq]; exact (memLp u).aestronglyMeasurable) p
  rwa [h.bijOn.image_eq] at this

omit [Fact (1 ≤ p)] in
/-- Let $w$ be a first-order weak derivative of the function of $u \in W^{1,p}(\Omega)$ on $\Omega$.
For every $i$, the partial derivative of $u \circ H$ along $b_i$ is
$$\partial_i (u \circ H)(y) = w(H(y))\big(DH(y) \, b_i\big)$$
for almost every $y \in \Omega'$. -/
theorem weakDeriv_compDiffeo_single (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (u : SobolevMultiIndex F b 1 p Ω μ) {w : E → E →L[ℝ] F} (hw : HasWeakFDerivOn (fn u) w Ω μ)
    (i : ι) :
    weakDeriv (compDiffeo h u) (MultiIndexLE.single i) =ᵐ[μ.restrict (Ω' : Set E)]
      fun y ↦ w (H y) (fderiv ℝ H y (b i)) := by
  have h1 := (hasWeakIteratedLineDerivOn (compDiffeo h u) (MultiIndexLE.single i)).of_perm
    (multiIndexTuple_single_perm (b : ι → E) i)
  have h2 := (((hw.comp_diffeoOn h) : HasWeakIteratedFDerivOn 1 _ _ Ω' μ).lineDeriv
    ![b i]).congr_ae (fn_compDiffeo h u).symm (EventuallyEq.refl _ _)
  filter_upwards [(ae_restrict_iff' Ω'.isOpen.measurableSet).2 (h1.ae_eq h2)] with y hy
  simpa using hy

/-- **The change of variables is bounded on $W^{1,p}$.** There is a constant $C$ with $\|u \circ
H\|_{W^{1,p}(\Omega')} \le C \|u\|_{W^{1,p}(\Omega)}$ for every $u \in W^{1,p}(\Omega)$.

The constant depends on the Jacobian bound, the bound on $|\det DH^{-1}|$, the basis $b$ and
$p$. -/
theorem exists_norm_compDiffeo_le (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) :
    ∃ C : ℝ, ∀ u : SobolevMultiIndex F b 1 p Ω μ, ‖compDiffeo h u‖ ≤ C * ‖u‖ := by
  obtain ⟨D, -, hD⟩ := h.exists_abs_det_fderiv_invFun_le
  obtain ⟨Cp, hCp⟩ : ∃ Cp : ℝ≥0∞, Cp = ENNReal.ofReal D ^ (1 / p.toReal) := ⟨_, rfl⟩
  have hCp' : Cp ≠ ⊤ := by
    rw [hCp]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = Fintype.card ι • ‖b.equivFunL.toContinuousLinearMap‖ :=
    ⟨_, rfl⟩
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = max M 0 * ∑ i, ‖b i‖ := ⟨_, rfl⟩
  have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ≥0∞, B = ENNReal.ofReal Mb * Cp * ENNReal.ofReal Cb := ⟨_, rfl⟩
  have hB' : B ≠ ⊤ := by
    rw [hB]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCp') ENNReal.ofReal_ne_top
  refine ⟨_, fun u ↦ norm_le_mul_norm_of_eLpNorm_le (compDiffeo h u) u hCp' hB' ?_ fun i ↦ ?_⟩
  · rw [hCp]
    exact eLpNorm_fn_compDiffeo_le h hD u
  · obtain ⟨w, hw, hwp, -, hwn⟩ := exists_hasWeakFDerivOn_fn u
    rw [← hCb] at hwn
    have h1 : eLpNorm (weakDeriv (compDiffeo h u) (MultiIndexLE.single i)) p
        (μ.restrict (Ω' : Set E)) ≤ ENNReal.ofReal Mb * eLpNorm (fun y ↦ w (H y)) p
          (μ.restrict (Ω' : Set E)) := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.memLp _).aestronglyMeasurable ?_ p
      filter_upwards [weakDeriv_compDiffeo_single h u hw i,
        ae_restrict_mem Ω'.isOpen.measurableSet] with y hy hyΩ'
      rw [hy, hMb]
      calc ‖w (H y) (fderiv ℝ H y (b i))‖ ≤ ‖w (H y)‖ * ‖fderiv ℝ H y (b i)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖w (H y)‖ * (‖fderiv ℝ H y‖ * ‖b i‖) := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖w (H y)‖ * (max M 0 * ∑ j, ‖b j‖) := by
            gcongr
            · exact (h.norm_fderiv_le y hyΩ').trans (le_max_left _ _)
            · exact Finset.single_le_sum (f := fun j ↦ ‖b j‖) (fun _ _ ↦ norm_nonneg _)
                (Finset.mem_univ i)
        _ = max M 0 * (∑ j, ‖b j‖) * ‖w (H y)‖ := by ring
    have h2 : eLpNorm (fun y ↦ w (H y)) p (μ.restrict (Ω' : Set E))
        ≤ Cp * eLpNorm w p (μ.restrict (Ω : Set E)) := by
      rw [hCp]
      have := h.eLpNorm_comp_le hD Ω'.isOpen subset_rfl
        (f := w) (by rw [h.bijOn.image_eq]; exact hwp.aestronglyMeasurable) p
      rwa [h.bijOn.image_eq] at this
    calc eLpNorm (weakDeriv (compDiffeo h u) (MultiIndexLE.single i)) p (μ.restrict (Ω' : Set E))
        ≤ ENNReal.ofReal Mb * (Cp * (ENNReal.ofReal Cb
          * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p (μ.restrict (Ω : Set E)))) :=
          h1.trans (by gcongr; exact h2.trans (by gcongr))
      _ = B * ∑ j, eLpNorm (weakDeriv u (MultiIndexLE.single j)) p (μ.restrict (Ω : Set E)) := by
          rw [hB]; ring

variable (F b p μ) in
/-- The change of variables $u \mapsto u \circ H$ as a linear map from $W^{1,p}(\Omega)$ to
$W^{1,p}(\Omega')$. -/
def compDiffeoₗ (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) :
    SobolevMultiIndex F b 1 p Ω μ →ₗ[ℝ] SobolevMultiIndex F b 1 p Ω' μ where
  toFun := compDiffeo h
  map_add' := compDiffeo_add h
  map_smul' := compDiffeo_smul h

variable (F b p μ) in
/-- **Change of variables as a bounded linear map.** Let $F$ be a Banach space, let $b$ be a basis
of $E$, let $p \ge 1$, and let $H$ be a $C^1$ diffeomorphism of $\Omega'$ onto $\Omega$ with
bounded Jacobians. The map $u \mapsto u \circ H$ is a bounded linear map from $W^{1,p}(\Omega)$
to $W^{1,p}(\Omega')$. This is Proposition 9.6 of [brezis2011functional].

Its function is $u \circ H$ (`SobolevMultiIndex.fn_compDiffeoL`). If $|\det DH^{-1}(x)| \le D$
for all $x \in \Omega$, the $L^p$ norm of its function is at most $D^{1/p} \|u\|_{L^p(\Omega)}$
(`SobolevMultiIndex.eLpNorm_fn_compDiffeoL_le`). The "transfer" $v = u \circ H$ and the
"retransfer" $w = v^\star \circ H^{-1}$ in step (b) of the proof of the extension theorem
(Theorem 9.7 of [brezis2011functional]) are maps of this form. -/
def compDiffeoL (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) :
    SobolevMultiIndex F b 1 p Ω μ →L[ℝ] SobolevMultiIndex F b 1 p Ω' μ :=
  (compDiffeoₗ F b p μ h).mkContinuousOfExistsBound (exists_norm_compDiffeo_le h)

/-- `SobolevMultiIndex.compDiffeoL` agrees with `SobolevMultiIndex.compDiffeo`. -/
@[simp]
theorem compDiffeoL_apply (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (u : SobolevMultiIndex F b 1 p Ω μ) : compDiffeoL F b p μ h u = compDiffeo h u :=
  rfl

/-- The function of `SobolevMultiIndex.compDiffeoL F b p μ h u` equals $u \circ H$ almost everywhere
on $\Omega'$. -/
theorem fn_compDiffeoL (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (u : SobolevMultiIndex F b 1 p Ω μ) :
    fn (compDiffeoL F b p μ h u) =ᵐ[μ.restrict (Ω' : Set E)] fun y ↦ fn u (H y) :=
  fn_compDiffeo h u

/-- Let $|\det DH^{-1}(x)| \le D$ for all $x \in \Omega$. The bounded linear map
`SobolevMultiIndex.compDiffeoL` satisfies $\|u \circ H\|_{L^p(\Omega')} \le D^{1/p}
\|u\|_{L^p(\Omega)}$ for every $u \in W^{1,p}(\Omega)$. -/
theorem eLpNorm_fn_compDiffeoL_le (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) {D : ℝ}
    (hD : ∀ x ∈ (Ω : Set E), |(fderiv ℝ Hinv x).det| ≤ D) (u : SobolevMultiIndex F b 1 p Ω μ) :
    eLpNorm (fn (compDiffeoL F b p μ h u)) p (μ.restrict (Ω' : Set E))
      ≤ ENNReal.ofReal D ^ (1 / p.toReal) * eLpNorm (fn u) p (μ.restrict (Ω : Set E)) :=
  eLpNorm_fn_compDiffeo_le h hD u

/-- There is a finite constant $C$ such that the bounded linear map `SobolevMultiIndex.compDiffeoL`
satisfies $\|u \circ H\|_{L^p(\Omega')} \le C \|u\|_{L^p(\Omega)}$ for every
$u \in W^{1,p}(\Omega)$. -/
theorem exists_eLpNorm_fn_compDiffeoL_le (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u : SobolevMultiIndex F b 1 p Ω μ,
      eLpNorm (fn (compDiffeoL F b p μ h u)) p (μ.restrict (Ω' : Set E))
        ≤ C * eLpNorm (fn u) p (μ.restrict (Ω : Set E)) := by
  obtain ⟨D, -, hD⟩ := h.exists_abs_det_fderiv_invFun_le
  exact ⟨_, ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top,
    fun u ↦ eLpNorm_fn_compDiffeoL_le h hD u⟩

end SobolevMultiIndex

end TypedCompDiffeo

section Euclidean

variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {H Hinv : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
  {Ω' Ω : Opens (EuclideanSpace ℝ (Fin N))} {M : ℝ}

/-- **Change of variables on $W^{1,p}$ of an open subset of $\mathbb{R}^N$.** Let $p \ge 1$, and let
$H$ be a $C^1$ diffeomorphism of an open set $\Omega' \subseteq \mathbb{R}^N$ onto an open set
$\Omega \subseteq \mathbb{R}^N$ with bounded Jacobians. The map $u \mapsto u \circ H$ is a
bounded linear map from $W^{1,p}(\Omega)$ to $W^{1,p}(\Omega')$. This is Proposition 9.6 of
[brezis2011functional].

It is `SobolevMultiIndex.compDiffeoL` on `SobolevEuclidean N 1 p Ω`. Its function and its $L^p$
bound are given by `SobolevMultiIndex.fn_compDiffeoL` and
`SobolevMultiIndex.eLpNorm_fn_compDiffeoL_le`. -/
noncomputable abbrev SobolevEuclidean.compDiffeoL
    (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) :
    SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω' :=
  SobolevMultiIndex.compDiffeoL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p volume h

end Euclidean

/-!
### Propositions 9.4 and 9.5: products and compositions

The chain rule `HasWeakIteratedLineDerivOn.contDiff_comp` of `Numlib.Analysis.Sobolev.Mollification`
is local: it asks for $L^p_{\mathrm{loc}}$ membership for one finite $p$, and the local
integrability contained in the weak derivative is the case $p = 1$. So the identity of Proposition
9.5 of [brezis2011functional] holds without a hypothesis on the exponent
(`HasWeakIteratedLineDerivOn.contDiff_comp'`), and the locality argument of the source for
$p = \infty$ is not needed. Proposition 9.4 then follows from the chain rule by the polarization
identity $uv = \frac{1}{2}((u + v)^2 - u^2 - v^2)$. The square of a bounded function is its
composition with a $C^1$ function that equals $t^2$ on the range and has a bounded derivative
(`sqCutoff`). So no approximation argument is needed at the endpoint $L^p \times L^\infty$.
-/

section SqCutoff

/-- For $s \in \mathbb{R}$, $\int_0^s x \, dx = s^2 / 2$. -/
theorem intervalIntegral_id_mul_self_div_two (s : ℝ) : ∫ x in (0 : ℝ)..s, x = s * s / 2 := by
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x ↦ x * x / 2)
    (f' := fun x ↦ x) (a := 0) (b := s)
    (fun x _ ↦ (((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const 2).congr_deriv (by
      simp only [id]; ring)) (continuous_id.intervalIntegrable _ _)
  rw [this]; ring

/-- For $M \in \mathbb{R}$, `sqCutoff M` is the function
$$t \mapsto \int_0^t 2 \max(-M, \min(M, s)) \, ds.$$
It is of class $C^1$, it equals $t^2$ on $[-M, M]$, and for $M \ge 0$ its derivative is bounded
by $2M$.

It makes the square of a function bounded by $M$ a composition to which the chain rule of
Proposition 9.5 of [brezis2011functional] applies. -/
def sqCutoff (M t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, 2 * max (-M) (min M s)

/-- The integrand $s \mapsto 2 \max(-M, \min(M, s))$ of `sqCutoff` is continuous. -/
theorem continuous_sqCutoff_integrand (M : ℝ) : Continuous fun s : ℝ ↦ 2 * max (-M) (min M s) :=
  continuous_const.mul (continuous_const.max (continuous_const.min continuous_id))

/-- The derivative of `sqCutoff M` at $t$ is $2 \max(-M, \min(M, t))$. -/
theorem deriv_sqCutoff (M t : ℝ) : deriv (sqCutoff M) t = 2 * max (-M) (min M t) :=
  Continuous.deriv_integral _ (continuous_sqCutoff_integrand M) 0 t

/-- The function `sqCutoff M` is of class $C^1$. -/
theorem contDiff_sqCutoff (M : ℝ) : ContDiff ℝ 1 (sqCutoff M) := by
  refine contDiff_one_iff_deriv.2 ⟨fun t ↦ ?_, ?_⟩
  · exact ((continuous_sqCutoff_integrand M).integral_hasStrictDerivAt 0 t).hasDerivAt
      |>.differentiableAt
  · rw [funext (deriv_sqCutoff M)]
    exact continuous_sqCutoff_integrand M

/-- For $M \ge 0$, the derivative of `sqCutoff M` is bounded by $2M$ in absolute value. -/
theorem abs_deriv_sqCutoff_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : |deriv (sqCutoff M) t| ≤ 2 * M := by
  rw [deriv_sqCutoff, abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨le_max_left _ _, max_le (by linarith) ?_⟩) two_pos.le
  exact min_le_left _ _

/-- If $|t| \le M$, the derivative of `sqCutoff M` at $t$ is $2t$. -/
theorem deriv_sqCutoff_of_abs_le {M t : ℝ} (ht : |t| ≤ M) : deriv (sqCutoff M) t = 2 * t := by
  rw [deriv_sqCutoff, min_eq_right (abs_le.1 ht).2, max_eq_right (abs_le.1 ht).1]

/-- If $|t| \le M$, the value of `sqCutoff M` at $t$ is $t^2$. -/
theorem sqCutoff_of_abs_le {M t : ℝ} (ht : |t| ≤ M) : sqCutoff M t = t * t := by
  have h : ∀ s ∈ uIcc (0 : ℝ) t, 2 * max (-M) (min M s) = 2 * s := fun s hs ↦ by
    have hs' : |s| ≤ M := by
      rw [uIcc, mem_Icc] at hs
      rcases le_total 0 t with ht0 | ht0
      · rw [min_eq_left ht0, max_eq_right ht0] at hs
        rw [abs_of_nonneg hs.1]; exact hs.2.trans ((le_abs_self t).trans ht)
      · rw [min_eq_right ht0, max_eq_left ht0] at hs
        rw [abs_of_nonpos hs.2]; linarith [(abs_le.1 ht).1, hs.1]
    rw [min_eq_right (abs_le.1 hs').2, max_eq_right (abs_le.1 hs').1]
  unfold sqCutoff
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_const_mul,
    intervalIntegral_id_mul_self_div_two]
  ring

end SqCutoff

section ChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} {y : E}

/-- **The chain rule for weak derivatives, without hypotheses on the exponent.** Let
$v : E \to \mathbb{R}$ have the weak derivative $w$ along the direction $y$ on $\Omega$, and let
$f \in C^1(\mathbb{R})$ with $|f'| \le M$. Then $(f' \circ v) \, w$ is the weak derivative of
$f \circ v$ along $y$ on $\Omega$. This is the identity of Proposition 9.5 of
[brezis2011functional]. No condition $f(0) = 0$ is needed.

It is `HasWeakIteratedLineDerivOn.contDiff_comp` at $p = 1$, where the $L^1_{\mathrm{loc}}$
hypotheses are the local integrability contained in the weak derivative. The identity is local,
so the reduction of the case $p = \infty$ to $p < \infty$ in the proof of the source is not
needed. -/
theorem HasWeakIteratedLineDerivOn.contDiff_comp' {v w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] v w Ω μ) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ}
    (hM : ∀ t, |deriv f t| ≤ M) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ f (v x)) (fun x ↦ deriv f (v x) * w x) Ω μ :=
  h.contDiff_comp rfl hf hM le_rfl ENNReal.one_ne_top h.locallyIntegrableOn.locallyMemLpOn
    h.locallyIntegrableOn_weakDeriv.locallyMemLpOn

/-- **The square of a bounded weakly differentiable function.** Let $u : E \to \mathbb{R}$ have the
weak derivative $w$ along $y$ on $\Omega$, and let $|u| \le M$ almost everywhere on $\Omega$.
Then $2uw$ is the weak derivative of $u^2$ along $y$ on $\Omega$.

The proof applies the chain rule with `sqCutoff M`, which equals $t^2$ on the range of $u$. -/
theorem HasWeakIteratedLineDerivOn.mul_self_of_ae_abs_le {u w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) {M : ℝ}
    (hM : ∀ᵐ x ∂μ.restrict (Ω : Set E), |u x| ≤ M) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ u x * u x) (fun x ↦ 2 * u x * w x) Ω μ := by
  have hM' : ∀ᵐ x ∂μ.restrict (Ω : Set E), |u x| ≤ max M 0 :=
    hM.mono fun x hx ↦ hx.trans (le_max_left _ _)
  refine (h.contDiff_comp' (contDiff_sqCutoff (max M 0))
    (abs_deriv_sqCutoff_le (le_max_right _ _))).congr_ae ?_ ?_
  · filter_upwards [hM'] with x hx
    exact sqCutoff_of_abs_le hx
  · filter_upwards [hM'] with x hx
    rw [deriv_sqCutoff_of_abs_le hx]

/-- **The product rule for bounded functions.** Let $u, v : E \to \mathbb{R}$ have the weak
derivatives $w_u$ and $w_v$ along $y$ on $\Omega$, and let $|u| \le M$ and $|v| \le M$ almost
everywhere on $\Omega$. Then $w_u v + u w_v$ is the weak derivative of $uv$ along $y$ on
$\Omega$. This is the identity of Proposition 9.4 of [brezis2011functional].

By polarization, $uv = \frac{1}{2}((u + v)^2 - u^2 - v^2)$, and the square of a bounded function
is `HasWeakIteratedLineDerivOn.mul_self_of_ae_abs_le`. No $L^p$ hypothesis is needed. The
product rule `HasWeakIteratedLineDerivOn.mul` for conjugate exponents does not cover the
endpoint $L^p \times L^\infty$ of the source; the chain rule reaches it in place of the
approximation argument of the source. -/
theorem HasWeakIteratedLineDerivOn.mul_of_ae_norm_le {u wu v wv : E → ℝ}
    (hu : HasWeakIteratedLineDerivOn ![y] u wu Ω μ)
    (hv : HasWeakIteratedLineDerivOn ![y] v wv Ω μ) {M : ℝ}
    (hMu : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖u x‖ ≤ M)
    (hMv : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖v x‖ ≤ M) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ u x * v x) (fun x ↦ wu x * v x + u x * wv x) Ω μ := by
  have h1 := (hu.add hv).mul_self_of_ae_abs_le (M := 2 * M) (by
    filter_upwards [hMu, hMv] with x hx hy
    rw [Real.norm_eq_abs] at hx hy
    rw [Pi.add_apply]
    linarith [abs_add_le (u x) (v x)])
  have h2 := hu.mul_self_of_ae_abs_le (M := M) (hMu.mono fun x hx ↦ (Real.norm_eq_abs _).symm ▸ hx)
  have h3 := hv.mul_self_of_ae_abs_le (M := M) (hMv.mono fun x hx ↦ (Real.norm_eq_abs _).symm ▸ hx)
  refine (((h1.sub h2).sub h3).const_smul (1 / 2 : ℝ)).congr_ae (Eventually.of_forall fun x ↦ ?_)
    (Eventually.of_forall fun x ↦ ?_)
  · simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    ring
  · simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    ring

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E}

/-- **Composition with a $C^1$ function.** Let $p \in [1, \infty]$, let $b$ be a basis of $E$, and
let $u \in W^{1,p}(\Omega)$ in the multi-index formulation over $b$. Let $G \in C^1(\mathbb{R})$
with $G(0) = 0$ and $|G'| \le M$. Then $G \circ u \in W^{1,p}(\Omega)$. This is Proposition 9.5
of [brezis2011functional].

The weak derivatives are $(G' \circ u) \, \partial_i u$
(`HasWeakIteratedLineDerivOn.contDiff_comp'`). The $L^p$ memberships follow from
$|G(s)| \le M |s|$ and $|G'(u) \, \partial_i u| \le M |\partial_i u|$. -/
theorem MemSobolevMultiIndex.contDiff_comp {u : E → ℝ} (hp : 1 ≤ p)
    (hu : MemSobolevMultiIndex b u 1 p Ω μ) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0)
    {M : ℝ} (hM : ∀ t, |deriv G t| ≤ M) : MemSobolevMultiIndex b (fun x ↦ G (u x)) 1 p Ω μ := by
  have hGle : ∀ t, |G t| ≤ M * |t| := fun t ↦ by
    simpa [hG0] using abs_sub_le_mul_of_abs_deriv_le hG hM t 0
  have hum : AEStronglyMeasurable u (μ.restrict (Ω : Set E)) := hu.memLp.aestronglyMeasurable
  have hGu : MemLp (fun x ↦ G (u x)) p (μ.restrict (Ω : Set E)) :=
    hu.memLp.of_ae_norm_le_mul (hG.continuous.comp_aestronglyMeasurable hum)
      (Eventually.of_forall fun x ↦ hGle (u x))
  refine ⟨hGu, fun β hβ ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _ (hGu.locallyIntegrableOn hp),
      hGu⟩
  · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
    obtain ⟨w, hw, hwp⟩ := hu.2 (Pi.single i 1) (by simp)
    have hw' : HasWeakIteratedLineDerivOn ![b i] u w Ω μ :=
      hw.of_perm (multiIndexTuple_single_perm (b : ι → E) i)
    refine ⟨_, (hw'.contDiff_comp' hG hM).of_perm (multiIndexTuple_single_perm (b : ι → E) i).symm,
      hwp.of_ae_norm_le_mul (((hG.continuous_deriv le_rfl).comp_aestronglyMeasurable hum).mul
        hwp.aestronglyMeasurable) (c := M) (Eventually.of_forall fun x ↦ ?_)⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)

/-- **The product of two bounded functions of $W^{1,p}$.** Let $p \in [1, \infty]$, let $b$ be a
basis of $E$, and let $u, v \in W^{1,p}(\Omega)$ in the multi-index formulation over $b$, with
$|u| \le M$ and $|v| \le M$ almost everywhere on $\Omega$. Then $uv \in W^{1,p}(\Omega)$, and
$|uv| \le M^2$ almost everywhere on $\Omega$. This is Proposition 9.4 of [brezis2011functional].

The weak derivatives are $(\partial_i u) \, v + u \, (\partial_i v)$
(`HasWeakIteratedLineDerivOn.mul_of_ae_norm_le`). -/
theorem MemSobolevMultiIndex.mul_of_ae_norm_le {u v : E → ℝ} (hp : 1 ≤ p)
    (hu : MemSobolevMultiIndex b u 1 p Ω μ) (hv : MemSobolevMultiIndex b v 1 p Ω μ) {M : ℝ}
    (hMu : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖u x‖ ≤ M)
    (hMv : ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖v x‖ ≤ M) :
    MemSobolevMultiIndex b (fun x ↦ u x * v x) 1 p Ω μ ∧
      ∀ᵐ x ∂μ.restrict (Ω : Set E), ‖u x * v x‖ ≤ M * M := by
  have hum : AEStronglyMeasurable u (μ.restrict (Ω : Set E)) := hu.memLp.aestronglyMeasurable
  have hvm : AEStronglyMeasurable v (μ.restrict (Ω : Set E)) := hv.memLp.aestronglyMeasurable
  have habs : ∀ {f g : E → ℝ}, (∀ᵐ x ∂μ.restrict (Ω : Set E), ‖f x‖ ≤ M) →
      ∀ᵐ x ∂μ.restrict (Ω : Set E), |f x * g x| ≤ M * |g x| := fun hf ↦ hf.mono fun x hx ↦ by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).symm.trans_le hx) (abs_nonneg _)
  have huv : MemLp (fun x ↦ u x * v x) p (μ.restrict (Ω : Set E)) :=
    hv.memLp.of_ae_norm_le_mul (hum.mul hvm) (habs hMu)
  refine ⟨⟨huv, fun β hβ ↦ ?_⟩, ?_⟩
  · rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
    · obtain rfl : β = 0 := congrArg Subtype.val h0
      exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
        (huv.locallyIntegrableOn hp), huv⟩
    · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
      obtain ⟨wu, hwu, hwup⟩ := hu.2 (Pi.single i 1) (by simp)
      obtain ⟨wv, hwv, hwvp⟩ := hv.2 (Pi.single i 1) (by simp)
      have hwu' : HasWeakIteratedLineDerivOn ![b i] u wu Ω μ :=
        hwu.of_perm (multiIndexTuple_single_perm (b : ι → E) i)
      have hwv' : HasWeakIteratedLineDerivOn ![b i] v wv Ω μ :=
        hwv.of_perm (multiIndexTuple_single_perm (b : ι → E) i)
      refine ⟨_, (hwu'.mul_of_ae_norm_le hwv' hMu hMv).of_perm
        (multiIndexTuple_single_perm (b : ι → E) i).symm, ?_⟩
      have h1 : MemLp (fun x ↦ wu x * v x) p (μ.restrict (Ω : Set E)) :=
        hwup.of_ae_norm_le_mul (hwup.aestronglyMeasurable.mul hvm) ((habs hMv).mono fun x hx ↦ by
          rwa [mul_comm (wu x)])
      have h2 : MemLp (fun x ↦ u x * wv x) p (μ.restrict (Ω : Set E)) :=
        hwvp.of_ae_norm_le_mul (hum.mul hwvp.aestronglyMeasurable) (habs hMu)
      exact h1.add h2
  · filter_upwards [hMu, hMv] with x hx hy
    rw [norm_mul]
    exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

end ChainRule

/-!
### The positive part

The positive part $u^+ = \max(u, 0)$ of a $W^{1,p}$ function lies in $W^{1,p}$, with
$\partial_i u^+ = 1_{\{u > 0\}} \, \partial_i u$. This is Lemma 7.6 of Gilbarg and Trudinger,
*Elliptic Partial Differential Equations of Second Order*. The proof applies the chain rule to the
$C^1$ approximations $G_\varepsilon(s) = \sqrt{\max(s, 0)^2 + \varepsilon^2} - \varepsilon$ of
$s \mapsto \max(s, 0)$. Their derivatives $\max(s, 0) / \sqrt{\max(s, 0)^2 + \varepsilon^2}$ are
bounded by $1$ and tend to $1_{\{s > 0\}}$, and dominated convergence gives the limit
$\varepsilon \to 0$ in the defining identity.
-/

section PosPart

/-- The function `posSq` is $s \mapsto \int_0^s 2 \max(t, 0) \, dt$, which equals $\max(s, 0)^2$
(`posSq_eq`). The integral form shows that it is of class $C^1$. -/
def posSq (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, 2 * max t 0

/-- The integrand $t \mapsto 2 \max(t, 0)$ of `posSq` is continuous. -/
theorem continuous_posSq_integrand : Continuous fun t : ℝ ↦ 2 * max t 0 :=
  continuous_const.mul (continuous_id.max continuous_const)

/-- The function `posSq` has the derivative $2 \max(s, 0)$ at every $s \in \mathbb{R}$. -/
theorem hasDerivAt_posSq (s : ℝ) : HasDerivAt posSq (2 * max s 0) s :=
  (continuous_posSq_integrand.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- The function `posSq` is of class $C^1$. -/
theorem contDiff_posSq : ContDiff ℝ 1 posSq := by
  refine contDiff_one_iff_deriv.2 ⟨fun s ↦ (hasDerivAt_posSq s).differentiableAt, ?_⟩
  rw [funext fun s ↦ (hasDerivAt_posSq s).deriv]
  exact continuous_posSq_integrand

/-- For every $s \in \mathbb{R}$, the value of `posSq` at $s$ is $\max(s, 0)^2$. -/
theorem posSq_eq (s : ℝ) : posSq s = max s 0 * max s 0 := by
  unfold posSq
  rcases le_total s 0 with hs | hs
  · rw [max_eq_right hs, mul_zero]
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_ge hs] at ht
    simp [max_eq_right ht.2]
  · have hcongr : ∫ t in (0 : ℝ)..s, 2 * max t 0 = ∫ t in (0 : ℝ)..s, 2 * t :=
      intervalIntegral.integral_congr fun t ht ↦ by
        rw [uIcc_of_le hs] at ht
        simp [max_eq_left ht.1]
    rw [max_eq_left hs, hcongr, intervalIntegral.integral_const_mul,
      intervalIntegral_id_mul_self_div_two]
    ring

/-- The function `posSq` is nonnegative. -/
theorem posSq_nonneg (s : ℝ) : 0 ≤ posSq s := by
  rw [posSq_eq]; exact mul_self_nonneg _

/-- For every $s \in \mathbb{R}$, the square root of the value of `posSq` at $s$ is $\max(s, 0)$. -/
theorem sqrt_posSq (s : ℝ) : √(posSq s) = max s 0 := by
  rw [posSq_eq, Real.sqrt_mul_self (le_max_right _ _)]

/-- For $\varepsilon, s \in \mathbb{R}$, the approximation of the positive part
$$G_\varepsilon(s) = \sqrt{\max(s, 0)^2 + \varepsilon^2} - \varepsilon.$$
For $\varepsilon > 0$ it is of class $C^1$, and $G_\varepsilon(s) \to \max(s, 0)$ as
$\varepsilon \to 0$.

The square $\max(s, 0)^2$ is written as `posSq s`. -/
def posPartApprox (ε s : ℝ) : ℝ := √(posSq s + ε ^ 2) - ε

/-- For $\varepsilon \ge 0$, $G_\varepsilon(0) = 0$. -/
theorem posPartApprox_zero {ε : ℝ} (hε : 0 ≤ ε) : posPartApprox ε 0 = 0 := by
  simp [posPartApprox, posSq_eq, Real.sqrt_sq hε]

/-- For $\varepsilon > 0$ and $s \in \mathbb{R}$, $\max(s, 0)^2 + \varepsilon^2 > 0$, with
$\max(s, 0)^2$ written as `posSq s`. -/
theorem posSq_add_sq_pos {ε : ℝ} (hε : 0 < ε) (s : ℝ) : 0 < posSq s + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (posSq_nonneg s) (pow_pos hε 2)

/-- For $\varepsilon > 0$, the function $G_\varepsilon$ is of class $C^1$. -/
theorem contDiff_posPartApprox {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (posPartApprox ε) :=
  ((contDiff_posSq.add contDiff_const).sqrt fun s ↦ (posSq_add_sq_pos hε s).ne').sub
    contDiff_const

/-- For $\varepsilon > 0$, the derivative of $G_\varepsilon$ at $s$ is $\max(s, 0) / \sqrt{\max(s,
0)^2 + \varepsilon^2}$. -/
theorem deriv_posPartApprox {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    deriv (posPartApprox ε) s = max s 0 / √(posSq s + ε ^ 2) := by
  have h : HasDerivAt (posPartApprox ε) (2 * max s 0 / (2 * √(posSq s + ε ^ 2))) s :=
    (((hasDerivAt_posSq s).add_const (ε ^ 2)).sqrt (posSq_add_sq_pos hε s).ne').sub_const ε
  rw [h.deriv, mul_div_mul_left _ _ two_ne_zero]

/-- For $\varepsilon > 0$, the derivative of $G_\varepsilon$ takes values in $[0, 1]$. -/
theorem deriv_posPartApprox_mem_Icc {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    deriv (posPartApprox ε) s ∈ Icc (0 : ℝ) 1 := by
  rw [deriv_posPartApprox hε]
  have hpos : 0 < √(posSq s + ε ^ 2) := Real.sqrt_pos.2 (posSq_add_sq_pos hε s)
  refine ⟨div_nonneg (le_max_right _ _) hpos.le, (div_le_one hpos).2 ?_⟩
  calc max s 0 = √(posSq s) := (sqrt_posSq s).symm
    _ ≤ √(posSq s + ε ^ 2) := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))

/-- For $\varepsilon > 0$, the derivative of $G_\varepsilon$ is bounded by $1$ in absolute value. -/
theorem abs_deriv_posPartApprox_le {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    |deriv (posPartApprox ε) s| ≤ 1 :=
  abs_le.2 ⟨by linarith [(deriv_posPartApprox_mem_Icc hε s).1],
    (deriv_posPartApprox_mem_Icc hε s).2⟩

/-- For $\varepsilon \ge 0$ and $s \in \mathbb{R}$, $0 \le G_\varepsilon(s) \le \max(s, 0)$. -/
theorem posPartApprox_mem_Icc {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) :
    posPartApprox ε s ∈ Icc 0 (max s 0) := by
  unfold posPartApprox
  constructor
  · rw [sub_nonneg]
    calc ε = √(ε ^ 2) := (Real.sqrt_sq hε).symm
      _ ≤ √(posSq s + ε ^ 2) := Real.sqrt_le_sqrt (le_add_of_nonneg_left (posSq_nonneg s))
  · rw [sub_le_iff_le_add, ← sqrt_posSq s,
      Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) hε)]
    nlinarith [Real.sq_sqrt (posSq_nonneg s), Real.sqrt_nonneg (posSq s)]

/-- For $\varepsilon \ge 0$ and $s \in \mathbb{R}$, $|G_\varepsilon(s)| \le |s|$. -/
theorem abs_posPartApprox_le {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) : |posPartApprox ε s| ≤ |s| := by
  rw [abs_of_nonneg (posPartApprox_mem_Icc hε s).1]
  exact (posPartApprox_mem_Icc hε s).2.trans (max_le (le_abs_self s) (abs_nonneg s))

/-- For every $s \in \mathbb{R}$, $G_\varepsilon(s) \to \max(s, 0)$ as $\varepsilon \to 0$. -/
theorem tendsto_posPartApprox (s : ℝ) :
    Tendsto (fun ε ↦ posPartApprox ε s) (𝓝 0) (𝓝 (max s 0)) := by
  have hc : Continuous fun ε : ℝ ↦ posPartApprox ε s :=
    (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2))).sub continuous_id
  simpa [posPartApprox, sqrt_posSq] using hc.tendsto 0

/-- For every $s \in \mathbb{R}$, as $\varepsilon \to 0$,
$$\frac{\max(s, 0)}{\sqrt{\max(s, 0)^2 + \varepsilon^2}} \to \begin{cases} 1 & \text{if } s > 0,
  \\ 0 & \text{otherwise.} \end{cases}$$

For $\varepsilon > 0$ the quotient is the derivative of $G_\varepsilon$ at $s$
(`deriv_posPartApprox`). -/
theorem tendsto_deriv_posPartApprox (s : ℝ) :
    Tendsto (fun ε ↦ max s 0 / √(posSq s + ε ^ 2)) (𝓝 0) (𝓝 (if 0 < s then 1 else 0)) := by
  by_cases hs : 0 < s
  · rw [ite_eq_left hs]
    have hpos : ∀ ε : ℝ, 0 < posSq s + ε ^ 2 := fun ε ↦ by
      rw [posSq_eq, max_eq_left hs.le]; positivity
    have hc : Continuous fun ε : ℝ ↦ max s 0 / √(posSq s + ε ^ 2) :=
      continuous_const.div (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2)))
        fun ε ↦ (Real.sqrt_pos.2 (hpos ε)).ne'
    simpa [sqrt_posSq, max_eq_left hs.le, div_self hs.ne'] using hc.tendsto 0
  · rw [ite_eq_right hs, max_eq_right (not_lt.1 hs)]
    simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [BorelSpace E] {Ω : Opens E} {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} {y : E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] in
/-- If $u$ and $w$ are almost everywhere strongly measurable for a measure $\nu$, then so is
$1_{\{u > 0\}} \, w$. -/
theorem aestronglyMeasurable_indicator_pos {u w : E → ℝ} {ν : Measure E}
    (hu : AEStronglyMeasurable u ν) (hw : AEStronglyMeasurable w ν) :
    AEStronglyMeasurable ({x | 0 < u x}.indicator w) ν := by
  have h : {x | 0 < u x}.indicator w
      = fun x ↦ (Ioi (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (u x) * w x := by
    funext x
    by_cases hx : 0 < u x <;> simp [Set.indicator, hx]
  rw [h]
  exact ((measurable_const.indicator measurableSet_Ioi).comp_aemeasurable
    hu.aemeasurable).aestronglyMeasurable.mul hw

/-- **The positive part of a weakly differentiable function.** Let $u : E \to \mathbb{R}$ have the
weak derivative $w$ along $y$ on $\Omega$. Then $1_{\{u > 0\}} \, w$ is the weak derivative of
$u^+ = \max(u, 0)$ along $y$ on $\Omega$. This is the identity of Lemma 7.6 of Gilbarg and
Trudinger, *Elliptic Partial Differential Equations of Second Order*.

The proof applies the chain rule `HasWeakIteratedLineDerivOn.contDiff_comp'` to $G_\varepsilon$
and passes to the limit $\varepsilon \to 0$ by dominated convergence, with
$|G_\varepsilon(u)| \le |u|$ and $|G_\varepsilon'(u) \, w| \le |w|$. -/
theorem HasWeakIteratedLineDerivOn.posPart {u w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] u w Ω μ) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ max (u x) 0) ({x | 0 < u x}.indicator w) Ω μ := by
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℕ → ℝ, ε = fun n : ℕ ↦ 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by rw [hεdef]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := hεdef ▸ tendsto_one_div_add_atTop_nhds_zero_nat
  have hG : ∀ n, HasWeakIteratedLineDerivOn ![y] (fun x ↦ posPartApprox (ε n) (u x))
      (fun x ↦ deriv (posPartApprox (ε n)) (u x) * w x) Ω μ := fun n ↦
    h.contDiff_comp' (contDiff_posPartApprox (hεpos n)) (abs_deriv_posPartApprox_le (hεpos n))
  have hum : AEStronglyMeasurable u (μ.restrict (Ω : Set E)) :=
    h.locallyIntegrableOn.aestronglyMeasurable
  have hwm : AEStronglyMeasurable w (μ.restrict (Ω : Set E)) :=
    h.locallyIntegrableOn_weakDeriv.aestronglyMeasurable
  have hindm := aestronglyMeasurable_indicator_pos hum hwm
  have hind : ∀ x, {x | 0 < u x}.indicator w x = (if 0 < u x then 1 else 0) * w x := fun x ↦ by
    by_cases hx : 0 < u x <;> simp [Set.indicator, hx]
  refine ⟨?_, ?_, fun φ ↦ ?_⟩
  · have e : (fun x ↦ max (u x) 0) = (1 / 2 : ℝ) • (u + fun x ↦ ‖u x‖) := funext fun x ↦ by
      rw [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rcases le_total 0 (u x) with hx | hx
      · rw [max_eq_left hx, Real.norm_eq_abs, abs_of_nonneg hx]; ring
      · rw [max_eq_right hx, Real.norm_eq_abs, abs_of_nonpos hx]; ring
    rw [e]
    exact (h.locallyIntegrableOn.add h.locallyIntegrableOn.norm).smul _
  · intro x hx
    obtain ⟨t, ht, hwt⟩ := h.locallyIntegrableOn_weakDeriv x hx
    refine ⟨t ∩ Ω, inter_mem ht self_mem_nhdsWithin, ((hwt.mono_set inter_subset_left).norm.mono'
      (hindm.mono_measure (Measure.restrict_mono inter_subset_right le_rfl))
      (Eventually.of_forall fun z ↦ ?_))⟩
    exact norm_indicator_le_norm_self _ _
  · have key : ∀ n, ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![y] •
        posPartApprox (ε n) (u x) ∂μ
        = (-1 : ℝ) ^ 1 • ∫ x in (Ω : Set E), φ x • (deriv (posPartApprox (ε n)) (u x) * w x) ∂μ :=
      fun n ↦ (hG n).integral_smul_eq φ
    have hL : Tendsto (fun n ↦ ∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![y] •
        posPartApprox (ε n) (u x) ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![y] • max (u x) 0 ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun x ↦ ‖iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![y] • u x‖) (fun n ↦ ?_) ?_
        (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
      · exact (φ.iteratedFDerivApply 1 ![y]).contDiff.continuous.aestronglyMeasurable.smul
          ((contDiff_posPartApprox (hεpos n)).continuous.comp_aestronglyMeasurable hum)
      · exact ((h.integrable_smul (φ.iteratedFDerivApply 1 ![y])).integrableOn
          (s := (Ω : Set E))).norm
      · rw [norm_smul, norm_smul, Real.norm_eq_abs (posPartApprox _ _), Real.norm_eq_abs (u x)]
        exact mul_le_mul_of_nonneg_left (abs_posPartApprox_le (hεpos n).le _) (norm_nonneg _)
      · exact ((tendsto_posPartApprox (u x)).comp hεt).const_smul _
    have hR : Tendsto (fun n ↦ ∫ x in (Ω : Set E),
        φ x • (deriv (posPartApprox (ε n)) (u x) * w x) ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), φ x • {x | 0 < u x}.indicator w x ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖φ x • w x‖) (fun n ↦ ?_) ?_
        (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
      · exact φ.contDiff.continuous.aestronglyMeasurable.smul
          ((((contDiff_posPartApprox (hεpos n)).continuous_deriv le_rfl).comp_aestronglyMeasurable
            hum).mul hwm)
      · exact ((h.integrable_smul_weakDeriv φ).integrableOn (s := (Ω : Set E))).norm
      · rw [norm_smul, norm_smul, norm_mul, Real.norm_eq_abs (deriv _ _)]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact mul_le_of_le_one_left (norm_nonneg _) (abs_deriv_posPartApprox_le (hεpos n) _)
      · have e : ∀ n, deriv (posPartApprox (ε n)) (u x)
            = max (u x) 0 / √(posSq (u x) + ε n ^ 2) := fun n ↦ deriv_posPartApprox (hεpos n) _
        simp_rw [e, hind x]
        exact (((tendsto_deriv_posPartApprox (u x)).comp hεt).mul_const (w x)).const_smul _
    have hL' : Tendsto (fun n ↦ (-1 : ℝ) ^ 1 • ∫ x in (Ω : Set E),
        φ x • (deriv (posPartApprox (ε n)) (u x) * w x) ∂μ) atTop
        (𝓝 (∫ x in (Ω : Set E), iteratedFDeriv ℝ 1 (φ : E → ℝ) x ![y] • max (u x) 0 ∂μ)) := by
      simpa only [key] using hL
    exact tendsto_nhds_unique hL' (hR.const_smul _)

variable {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E}

/-- **The positive part of a $W^{1,p}$ function lies in $W^{1,p}$.** Let $p \in [1, \infty]$, let
$b$ be a basis of $E$, and let $u \in W^{1,p}(\Omega)$ in the multi-index formulation over $b$.
Then $u^+ = \max(u, 0) \in W^{1,p}(\Omega)$. This is Lemma 7.6 of Gilbarg and Trudinger,
*Elliptic Partial Differential Equations of Second Order*, and Theorem A.1 of Kinderlehrer and
Stampacchia.

The weak derivatives are $\partial_i u^+ = 1_{\{u > 0\}} \, \partial_i u$
(`HasWeakIteratedLineDerivOn.posPart`). The result shows that the obstacle set
$\{v \in H^1_0(\Omega) : v \ge \psi\}$ is nonempty. -/
theorem MemSobolevMultiIndex.posPart {u : E → ℝ} (hp : 1 ≤ p)
    (hu : MemSobolevMultiIndex b u 1 p Ω μ) :
    MemSobolevMultiIndex b (fun x ↦ max (u x) 0) 1 p Ω μ := by
  have hum : AEStronglyMeasurable u (μ.restrict (Ω : Set E)) := hu.memLp.aestronglyMeasurable
  have hpos : MemLp (fun x ↦ max (u x) 0) p (μ.restrict (Ω : Set E)) :=
    hu.memLp.of_le ((continuous_id.max continuous_const).comp_aestronglyMeasurable hum)
      (Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        exact abs_le.2 ⟨(neg_nonpos.2 (abs_nonneg _)).trans (le_max_right _ _),
          max_le (le_abs_self _) (abs_nonneg _)⟩)
  refine ⟨hpos, fun β hβ ↦ ?_⟩
  rcases MultiIndexLE.eq_zero_or_exists_eq_single ⟨β, hβ⟩ with h0 | ⟨i, hi⟩
  · obtain rfl : β = 0 := congrArg Subtype.val h0
    exact ⟨_, HasWeakIteratedLineDerivOn.of_length_eq_zero (by simp) _
      (hpos.locallyIntegrableOn hp), hpos⟩
  · obtain rfl : β = Pi.single i 1 := congrArg Subtype.val hi
    obtain ⟨w, hw, hwp⟩ := hu.2 (Pi.single i 1) (by simp)
    have hw' : HasWeakIteratedLineDerivOn ![b i] u w Ω μ :=
      hw.of_perm (multiIndexTuple_single_perm (b : ι → E) i)
    exact ⟨_, hw'.posPart.of_perm (multiIndexTuple_single_perm (b : ι → E) i).symm,
      hwp.of_le (aestronglyMeasurable_indicator_pos hum hwp.aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _)⟩

end PosPart

/-!
### Stampacchia's truncation

The truncation functions $G$ of Stampacchia's method satisfy conditions (i)–(iii) of the proof of
Theorem 9.27 of [brezis2011functional], §9.7: $G \in C^1(\mathbb{R})$ is nondecreasing, $G = 0$ on
$(-\infty, 0]$, $G > 0$ on $(0, \infty)$, and $G'$ is bounded. The function `stampacchiaTruncation`
is $s \mapsto \int_0^s \min(\max(t, 0), 1) \, dt$, and `stampacchiaTruncationSqrt` is the auxiliary
function $H(s) = \int_0^s \sqrt{G'(t)} \, dt$ of the proof of Proposition 9.29. The chain rule of
this module puts $G(u)$ in $W^{1,p}$, as it does for `posSq`.
-/

section Truncation

/-- The derivative of Stampacchia's truncation, $t \mapsto \min(\max(t, 0), 1)$. It is continuous,
takes values in $[0, 1]$, vanishes on $(-\infty, 0]$ and is positive on $(0, \infty)$. -/
def stampacchiaTruncationDeriv (t : ℝ) : ℝ := min (max t 0) 1

/-- The function $t \mapsto \min(\max(t, 0), 1)$ is continuous. -/
theorem continuous_stampacchiaTruncationDeriv : Continuous stampacchiaTruncationDeriv :=
  (continuous_id.max continuous_const).min continuous_const

/-- The function $t \mapsto \min(\max(t, 0), 1)$ is nonnegative. -/
theorem stampacchiaTruncationDeriv_nonneg (t : ℝ) : 0 ≤ stampacchiaTruncationDeriv t :=
  le_min (le_max_right _ _) zero_le_one

/-- The function $t \mapsto \min(\max(t, 0), 1)$ is at most $1$. -/
theorem stampacchiaTruncationDeriv_le_one (t : ℝ) : stampacchiaTruncationDeriv t ≤ 1 :=
  min_le_right _ _

/-- The function $t \mapsto \min(\max(t, 0), 1)$ vanishes for $t \le 0$. -/
theorem stampacchiaTruncationDeriv_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    stampacchiaTruncationDeriv t = 0 := by
  rw [stampacchiaTruncationDeriv, max_eq_right ht, min_eq_left zero_le_one]

/-- The function $t \mapsto \min(\max(t, 0), 1)$ is positive for $t > 0$. -/
theorem stampacchiaTruncationDeriv_pos {t : ℝ} (ht : 0 < t) : 0 < stampacchiaTruncationDeriv t :=
  lt_min (lt_max_of_lt_left ht) one_pos

/-- **Stampacchia's truncation** $G(s) = \int_0^s \min(\max(t, 0), 1) \, dt$. It is of class $C^1$,
$G = 0$ on $(-\infty, 0]$, $G(s) = s^2 / 2$ on $[0, 1]$ and $G(s) = s - 1/2$ on $[1, \infty)$,
with $0 \le G' \le 1$ and $G' > 0$ on $(0, \infty)$. It is the function $G$ of the proof of
Theorem 9.27 of [brezis2011functional], with conditions (i)–(iii) there for $M = 1$. -/
def stampacchiaTruncation (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, stampacchiaTruncationDeriv t

/-- Stampacchia's truncation $G$ has the derivative $\min(\max(s, 0), 1)$ at every
$s \in \mathbb{R}$. -/
theorem hasDerivAt_stampacchiaTruncation (s : ℝ) :
    HasDerivAt stampacchiaTruncation (stampacchiaTruncationDeriv s) s :=
  (continuous_stampacchiaTruncationDeriv.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- The derivative of Stampacchia's truncation $G$ at $s$ is $\min(\max(s, 0), 1)$. -/
theorem deriv_stampacchiaTruncation (s : ℝ) :
    deriv stampacchiaTruncation s = stampacchiaTruncationDeriv s :=
  (hasDerivAt_stampacchiaTruncation s).deriv

/-- Stampacchia's truncation $G$ is of class $C^1$, because its derivative $\min(\max(s, 0), 1)$ is
continuous. -/
theorem contDiff_stampacchiaTruncation : ContDiff ℝ 1 stampacchiaTruncation := by
  refine contDiff_one_iff_deriv.2
    ⟨fun s ↦ (hasDerivAt_stampacchiaTruncation s).differentiableAt, ?_⟩
  rw [funext deriv_stampacchiaTruncation]
  exact continuous_stampacchiaTruncationDeriv

/-- Stampacchia's truncation satisfies $G(s) = 0$ for $s \le 0$. -/
theorem stampacchiaTruncation_of_nonpos {s : ℝ} (hs : s ≤ 0) : stampacchiaTruncation s = 0 := by
  unfold stampacchiaTruncation
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun _ ht ↦ ?_).trans
    intervalIntegral.integral_zero
  rw [uIcc_of_ge hs] at ht
  exact stampacchiaTruncationDeriv_of_nonpos ht.2

/-- Stampacchia's truncation satisfies $G(s) > 0$ for $s > 0$. -/
theorem stampacchiaTruncation_pos {s : ℝ} (hs : 0 < s) : 0 < stampacchiaTruncation s :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    (continuous_stampacchiaTruncationDeriv.intervalIntegrable _ _)
    (fun _ ht ↦ stampacchiaTruncationDeriv_pos ht.1) hs

/-- Stampacchia's truncation is nonnegative. -/
theorem stampacchiaTruncation_nonneg (s : ℝ) : 0 ≤ stampacchiaTruncation s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [stampacchiaTruncation_of_nonpos hs]
  · exact (stampacchiaTruncation_pos hs).le

/-- Stampacchia's truncation $G$ is strictly increasing on $(0, \infty)$, where $G' > 0$. -/
theorem strictMonoOn_stampacchiaTruncation : StrictMonoOn stampacchiaTruncation (Ioi 0) :=
  strictMonoOn_of_deriv_pos (convex_Ioi 0) contDiff_stampacchiaTruncation.continuous.continuousOn
    fun s hs ↦ by
      rw [interior_Ioi] at hs
      rw [deriv_stampacchiaTruncation]
      exact stampacchiaTruncationDeriv_pos hs

/-- A function $G : \mathbb{R} \to \mathbb{R}$ is a **truncation function of Stampacchia's method**
with bound $M$ if $G \in C^1(\mathbb{R})$, $|G'| \le M$, $G' \ge 0$, $G = 0$ on $(-\infty, 0]$
and $G > 0$ on $(0, \infty)$. These are conditions (i)–(iii) of the proof of Theorem 9.27 of
[brezis2011functional].

This is the form that `Elliptic.le_of_forall_truncation_mem` of
`Numlib.Analysis.PDE.Elliptic.MaximumPrinciple` uses. The strict monotonicity on $(0, \infty)$
in the source is used only through $G > 0$ there. -/
structure IsStampacchiaTruncation (G : ℝ → ℝ) (M : ℝ) : Prop where
  /-- The function $G$ is of class $C^1$. -/
  contDiff : ContDiff ℝ 1 G
  /-- The derivative satisfies $|G'(s)| \le M$ for every $s$. -/
  abs_deriv_le : ∀ s, |deriv G s| ≤ M
  /-- The derivative satisfies $G'(s) \ge 0$ for every $s$. -/
  deriv_nonneg : ∀ s, 0 ≤ deriv G s
  /-- The function vanishes on $(-\infty, 0]$. -/
  eq_zero_of_nonpos : ∀ s, s ≤ 0 → G s = 0
  /-- The function is positive on $(0, \infty)$. -/
  pos_of_pos : ∀ s, 0 < s → 0 < G s

namespace IsStampacchiaTruncation

variable {G : ℝ → ℝ} {M : ℝ}

/-- A truncation function of Stampacchia's method is nonnegative. -/
theorem nonneg (hG : IsStampacchiaTruncation G M) (s : ℝ) : 0 ≤ G s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [hG.eq_zero_of_nonpos s hs]
  · exact (hG.pos_of_pos s hs).le

/-- A truncation function $G$ satisfies $t \, G(t) \ge 0$ for every $t \in \mathbb{R}$. -/
theorem mul_nonneg (hG : IsStampacchiaTruncation G M) (t : ℝ) : 0 ≤ t * G t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [hG.eq_zero_of_nonpos t ht, mul_zero]
  · exact _root_.mul_nonneg ht.le (hG.nonneg t)

/-- A truncation function $G$ satisfies $t \, G(t) = 0$ if and only if $t \le 0$. -/
theorem mul_eq_zero_iff (hG : IsStampacchiaTruncation G M) {t : ℝ} : t * G t = 0 ↔ t ≤ 0 := by
  constructor
  · intro h
    by_contra ht
    push Not at ht
    exact (_root_.mul_pos ht (hG.pos_of_pos t ht)).ne' h
  · intro ht
    rw [hG.eq_zero_of_nonpos t ht, mul_zero]

/-- A truncation function $G$ satisfies $G(0) = 0$. -/
theorem zero (hG : IsStampacchiaTruncation G M) : G 0 = 0 := hG.eq_zero_of_nonpos 0 le_rfl

/-- For a truncation function $G$ and every $K \in \mathbb{R}$, the shifted function
$t \mapsto G(t - K)$ is of class $C^1$. -/
theorem contDiff_sub (hG : IsStampacchiaTruncation G M) (K : ℝ) :
    ContDiff ℝ 1 fun t ↦ G (t - K) :=
  hG.contDiff.comp (contDiff_id.sub contDiff_const)

/-- For a truncation function $G$ with bound $M$ and every $K \in \mathbb{R}$, the derivative of
$t \mapsto G(t - K)$ is bounded by $M$ in absolute value. -/
theorem abs_deriv_sub_le (hG : IsStampacchiaTruncation G M) (K t : ℝ) :
    |deriv (fun t ↦ G (t - K)) t| ≤ M := by
  rw [deriv_comp_sub_const G K t]; exact hG.abs_deriv_le _

end IsStampacchiaTruncation

/-- Stampacchia's truncation $G(s) = \int_0^s \min(\max(t, 0), 1) \, dt$ is a truncation function
with bound $M = 1$. -/
theorem isStampacchiaTruncation_stampacchiaTruncation :
    IsStampacchiaTruncation stampacchiaTruncation 1 where
  contDiff := contDiff_stampacchiaTruncation
  abs_deriv_le s := by
    rw [deriv_stampacchiaTruncation, abs_of_nonneg (stampacchiaTruncationDeriv_nonneg s)]
    exact stampacchiaTruncationDeriv_le_one s
  deriv_nonneg s := by rw [deriv_stampacchiaTruncation]; exact stampacchiaTruncationDeriv_nonneg s
  eq_zero_of_nonpos _ hs := stampacchiaTruncation_of_nonpos hs
  pos_of_pos _ hs := stampacchiaTruncation_pos hs

/-- **The truncation function of Stampacchia's method exists.** There is $G \in C^1(\mathbb{R})$
with $|G'| \le 1$, $G' \ge 0$, $G = 0$ on $(-\infty, 0]$ and $G > 0$ on $(0, \infty)$, such that
$G$ is strictly increasing on $(0, \infty)$ and $G \ge 0$. It is the function of the proof of
Theorem 9.27 of [brezis2011functional], with conditions (i)–(iii) there for $M = 1$.

The function is `stampacchiaTruncation`. -/
theorem exists_stampacchiaTruncation :
    ∃ G : ℝ → ℝ, IsStampacchiaTruncation G 1 ∧ StrictMonoOn G (Ioi 0) ∧ ∀ s, 0 ≤ G s :=
  ⟨stampacchiaTruncation, isStampacchiaTruncation_stampacchiaTruncation,
    strictMonoOn_stampacchiaTruncation, stampacchiaTruncation_nonneg⟩

/-- **The auxiliary function $H(s) = \int_0^s \sqrt{G'(t)} \, dt$** of the proof of Proposition 9.29
of [brezis2011functional], for Stampacchia's truncation $G$, so that
$G'(t) = \min(\max(t, 0), 1)$. It is of class $C^1$ with $H' = \sqrt{G'}$, so that
$|\nabla H(u)|^2 = |\nabla u|^2 \, G'(u)$. -/
def stampacchiaTruncationSqrt (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, √(stampacchiaTruncationDeriv t)

/-- The function $t \mapsto \sqrt{\min(\max(t, 0), 1)}$ is continuous. -/
theorem continuous_sqrt_stampacchiaTruncationDeriv :
    Continuous fun t ↦ √(stampacchiaTruncationDeriv t) :=
  continuous_stampacchiaTruncationDeriv.sqrt

/-- The function $H$ of `stampacchiaTruncationSqrt` has the derivative $\sqrt{\min(\max(s, 0), 1)}$
at every $s \in \mathbb{R}$. -/
theorem hasDerivAt_stampacchiaTruncationSqrt (s : ℝ) :
    HasDerivAt stampacchiaTruncationSqrt (√(stampacchiaTruncationDeriv s)) s :=
  (continuous_sqrt_stampacchiaTruncationDeriv.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- The derivative of the function $H$ of `stampacchiaTruncationSqrt` at $s$ is
$\sqrt{\min(\max(s, 0), 1)}$. -/
theorem deriv_stampacchiaTruncationSqrt (s : ℝ) :
    deriv stampacchiaTruncationSqrt s = √(stampacchiaTruncationDeriv s) :=
  (hasDerivAt_stampacchiaTruncationSqrt s).deriv

/-- For the function $H$ of `stampacchiaTruncationSqrt` and Stampacchia's truncation $G$,
$H'(s)^2 = G'(s)$ for every $s \in \mathbb{R}$. -/
theorem sq_deriv_stampacchiaTruncationSqrt (s : ℝ) :
    deriv stampacchiaTruncationSqrt s ^ 2 = deriv stampacchiaTruncation s := by
  rw [deriv_stampacchiaTruncationSqrt, deriv_stampacchiaTruncation,
    Real.sq_sqrt (stampacchiaTruncationDeriv_nonneg s)]

/-- The function $H(s) = \int_0^s \sqrt{\min(\max(t, 0), 1)} \, dt$ is a truncation function with
bound $M = 1$. The square of its derivative is $\min(\max(s, 0), 1)$, the derivative of
`stampacchiaTruncation`. -/
theorem isStampacchiaTruncation_stampacchiaTruncationSqrt :
    IsStampacchiaTruncation stampacchiaTruncationSqrt 1 where
  contDiff := by
    refine contDiff_one_iff_deriv.2
      ⟨fun s ↦ (hasDerivAt_stampacchiaTruncationSqrt s).differentiableAt, ?_⟩
    rw [funext deriv_stampacchiaTruncationSqrt]
    exact continuous_sqrt_stampacchiaTruncationDeriv
  abs_deriv_le s := by
    rw [deriv_stampacchiaTruncationSqrt, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.2 (stampacchiaTruncationDeriv_le_one s)
  deriv_nonneg s := by rw [deriv_stampacchiaTruncationSqrt]; exact Real.sqrt_nonneg _
  eq_zero_of_nonpos s hs := by
    unfold stampacchiaTruncationSqrt
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun _ ht ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_ge hs] at ht
    simp [stampacchiaTruncationDeriv_of_nonpos ht.2]
  pos_of_pos s hs :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (continuous_sqrt_stampacchiaTruncationDeriv.intervalIntegrable _ _)
      (fun t ht ↦ Real.sqrt_pos.2 (stampacchiaTruncationDeriv_pos ht.1)) hs

end Truncation

/-! ### The affine change of variables at every order -/

section Affine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- For a continuous linear automorphism $T$ of $E$ and $c \in E$, the affine map $x \mapsto Tx + c$
as a homeomorphism of $E$, with inverse $y \mapsto T^{-1}(y - c)$. -/
def ContinuousLinearEquiv.affineHomeomorph (T : E ≃L[ℝ] E) (c : E) : E ≃ₜ E where
  toFun x := T x + c
  invFun y := T.symm (y - c)
  left_inv x := by simp
  right_inv y := by simp
  continuous_toFun := T.continuous.add continuous_const
  continuous_invFun := T.symm.continuous.comp (continuous_id.sub continuous_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The homeomorphism `T.affineHomeomorph c` maps $x$ to $Tx + c$. -/
@[simp]
theorem ContinuousLinearEquiv.affineHomeomorph_apply (T : E ≃L[ℝ] E) (c x : E) :
    T.affineHomeomorph c x = T x + c :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The inverse of `T.affineHomeomorph c` maps $y$ to $T^{-1}(y - c)$. -/
@[simp]
theorem ContinuousLinearEquiv.affineHomeomorph_symm_apply (T : E ≃L[ℝ] E) (c y : E) :
    (T.affineHomeomorph c).symm y = T.symm (y - c) :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- For a continuous linear automorphism $T$ of $E$ and $c \in E$, the affine map $x \mapsto Tx + c$
is a measurable embedding. -/
theorem measurableEmbedding_affine (T : E ≃L[ℝ] E) (c : E) :
    MeasurableEmbedding fun x : E ↦ T x + c :=
  (T.affineHomeomorph c).measurableEmbedding

/-- **The image of an additive Haar measure under an affine map.** Let $\mu$ be an additive Haar
measure on $E$, let $T$ be a continuous linear automorphism of $E$, and let $c \in E$. The image
of $\mu$ under $x \mapsto Tx + c$ is $|\det T|^{-1} \mu$. -/
theorem map_affine_addHaar (T : E ≃L[ℝ] E) (c : E) :
    μ.map (fun x ↦ T x + c) = ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| • μ := by
  have hdet : LinearMap.det (T : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  have h : (fun x : E ↦ T x + c) = (fun y ↦ y + c) ∘ ⇑(T : E →ₗ[ℝ] E) := by
    funext x; simp
  rw [h, ← Measure.map_map (measurable_add_const c)
    (by simpa using T.continuous.measurable : Measurable ⇑(T : E →ₗ[ℝ] E)),
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet,
    Measure.map_smul _ (measurable_add_const c).aemeasurable, map_add_right_eq_self]

/-- **The affine change of variables in a set integral.** Let $\mu$ be an additive Haar measure on
$E$, let $\Phi(x) = Tx + c$ for a continuous linear automorphism $T$ of $E$ and $c \in E$, let
$G$ be a real normed space, let $g : E \to G$ and let $s \subseteq E$. Then
$$\int_{\Phi^{-1}(s)} g(\Phi(x)) \, d\mu(x) = |\det T|^{-1} \int_s g \, d\mu.$$
-/
theorem setIntegral_comp_affine (T : E ≃L[ℝ] E) (c : E) {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : E → G) (s : Set E) :
    ∫ x in (fun x ↦ T x + c) ⁻¹' s, g (T x + c) ∂μ
      = (ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹|).toReal • ∫ y in s, g y ∂μ := by
  have hmp : MeasurePreserving (fun x ↦ T x + c) μ (μ.map fun x ↦ T x + c) :=
    ⟨(measurableEmbedding_affine T c).measurable, rfl⟩
  rw [hmp.setIntegral_preimage_emb (measurableEmbedding_affine T c), map_affine_addHaar,
    Measure.restrict_smul, integral_smul_measure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **An affine map is a diffeomorphism with bounded Jacobians.** Let $T$ be a continuous linear
automorphism of $E$, let $c \in E$, let $\Phi(x) = Tx + c$, and let $\Omega \subseteq E$ be
open. Then $\Phi$ is a $C^1$ diffeomorphism of $\Phi^{-1}(\Omega)$ onto $\Omega$ with inverse
$y \mapsto T^{-1}(y - c)$ and Jacobians bounded by $\max(\|T\|, \|T^{-1}\|)$. -/
theorem isDiffeoOnWithBoundedJacobian_affine (T : E ≃L[ℝ] E) (c : E) (Ω : Opens E) :
    IsDiffeoOnWithBoundedJacobian (fun x ↦ T x + c) (fun y ↦ T.symm (y - c))
      ((fun x ↦ T x + c) ⁻¹' Ω) Ω (max ‖(T : E →L[ℝ] E)‖ ‖(T.symm : E →L[ℝ] E)‖) where
  isOpen_source := Ω.isOpen.preimage (T.continuous.add continuous_const)
  isOpen_target := Ω.isOpen
  bijOn := ⟨fun x hx ↦ hx, fun x _ y _ hxy ↦ T.injective (add_right_cancel hxy),
    fun y hy ↦ ⟨T.symm (y - c), by simpa using hy, by simp⟩⟩
  invOn := ⟨fun x _ ↦ by simp, fun y _ ↦ by simp⟩
  contDiffOn := (T.contDiff.add contDiff_const).contDiffOn
  contDiffOn_invFun := (T.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn
  norm_fderiv_le := fun y _ ↦ by
    rw [(T.hasFDerivAt.add_const c).fderiv]
    exact le_max_left _ _
  norm_fderiv_invFun_le := fun x _ ↦ by
    have h : HasFDerivAt (fun y ↦ T.symm (y - c))
        ((T.symm : E →L[ℝ] E).comp (ContinuousLinearMap.id ℝ E)) x :=
      T.symm.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const c)
    rw [h.fderiv, ContinuousLinearMap.comp_id]
    exact le_max_right _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $\Phi(x) = Tx + c$ and let $\Psi(y) = T^{-1} y - T^{-1} c$ be its inverse. For every set
$s \subseteq E$, $\Psi^{-1}(\Phi^{-1}(s)) = s$. -/
theorem affine_symm_preimage_affine_preimage (T : E ≃L[ℝ] E) (c : E) (s : Set E) :
    (fun y ↦ T.symm y + -T.symm c) ⁻¹' ((fun x ↦ T x + c) ⁻¹' s) = s := by
  ext x
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $\Phi(x) = Tx + c$ and let $\Psi(y) = T^{-1} y - T^{-1} c$ be its inverse. For every set
$s \subseteq E$, the image $\Phi(s)$ is the preimage $\Psi^{-1}(s)$. -/
theorem affine_image_eq_affine_symm_preimage (T : E ≃L[ℝ] E) (c : E) (s : Set E) :
    (fun x ↦ T x + c) '' s = (fun y ↦ T.symm y + -T.symm c) ⁻¹' s := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨T.symm y + -T.symm c, hy, by simp⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $T$ be a continuous linear automorphism of $E$ and $c \in E$. The affine map
$x \mapsto Tx + c$ is a $C^1$ diffeomorphism of $E$ onto itself with inverse
$y \mapsto T^{-1}(y - c)$ and Jacobians bounded by $\max(\|T\|, \|T^{-1}\|)$.

The source and the target are the whole space, written as the open set `⊤`. -/
theorem isDiffeoOnWithBoundedJacobian_affine_top (T : E ≃L[ℝ] E) (c : E) :
    IsDiffeoOnWithBoundedJacobian (fun x ↦ T x + c) (fun y ↦ T.symm (y - c))
      ((⊤ : Opens E) : Set E) ((⊤ : Opens E) : Set E)
      (max ‖(T : E →L[ℝ] E)‖ ‖(T.symm : E →L[ℝ] E)‖) := by
  have h := isDiffeoOnWithBoundedJacobian_affine T c (⊤ : Opens E)
  rwa [show (fun x ↦ T x + c) ⁻¹' ((⊤ : Opens E) : Set E) = ((⊤ : Opens E) : Set E) by simp]
    at h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $\Phi(x) = Tx + c$, let $\Omega \subseteq E$ be open, and let $\Omega' = \Phi^{-1}(\Omega)$.
The inverse affine map $\Psi(y) = T^{-1} y - T^{-1} c$ is a $C^1$ diffeomorphism of $\Omega$
onto $\Omega'$ with inverse $x \mapsto T(x + T^{-1} c)$ and Jacobians bounded by
$\max(\|T^{-1}\|, \|T\|)$. -/
theorem isDiffeoOnWithBoundedJacobian_affine_symm {Ω Ω' : Opens E} (T : E ≃L[ℝ] E) (c : E)
    (hΩ' : (Ω' : Set E) = (fun x ↦ T x + c) ⁻¹' Ω) :
    IsDiffeoOnWithBoundedJacobian (fun y ↦ T.symm y + -T.symm c)
      (fun x ↦ T.symm.symm (x - -T.symm c)) (Ω : Set E) (Ω' : Set E)
      (max ‖(T.symm : E →L[ℝ] E)‖ ‖(T.symm.symm : E →L[ℝ] E)‖) := by
  have h := isDiffeoOnWithBoundedJacobian_affine T.symm (-T.symm c) Ω'
  rwa [show (fun y ↦ T.symm y + -T.symm c) ⁻¹' (Ω' : Set E) = (Ω : Set E) by
    rw [hΩ', affine_symm_preimage_affine_preimage]] at h

/-- **The affine change of variables at every order.** Let $\mu$ be an additive Haar measure on $E$,
let $w$ be an $n$-th weak derivative of $v : E \to F$ on $\Omega$, let $T$ be a continuous
linear automorphism of $E$, and let $c \in E$. Then $x \mapsto v(Tx + c)$ has on the open set
$\{x : Tx + c \in \Omega\}$ the $n$-th weak derivative
$$x \mapsto \big((z_1, \dots, z_n) \mapsto w(Tx + c)(Tz_1, \dots, Tz_n)\big).$$

Write $\Phi(x) = Tx + c$. The proof uses that $\varphi \circ \Phi^{-1}$ is a test function on
$\Omega$ for every test function $\varphi$ on $\Phi^{-1}(\Omega)$, that $D^n(\psi \circ
\Phi)(x)(z_1, \dots, z_n) = D^n \psi(\Phi(x))(Tz_1, \dots, Tz_n)$, and that the substitution
$x \mapsto \Phi(x)$ in the integrals (`setIntegral_comp_affine`) gives the same factor
$|\det T|^{-1}$ on both sides. This is the affine counterpart, at every order, of Proposition
9.6 of [brezis2011functional]. It serves the proof of Theorem 10.3.4 of [han2009theoretical]. -/
theorem HasWeakIteratedFDerivOn.comp_affineEquiv {n : ℕ} {v : E → F} {w : E → E [×n]→L[ℝ] F}
    {Ω : Opens E} (h : HasWeakIteratedFDerivOn n v w Ω μ) (T : E ≃L[ℝ] E) (c : E) :
    HasWeakIteratedFDerivOn n (fun x ↦ v (T x + c))
      (fun x ↦ (w (T x + c)).compContinuousLinearMap fun _ ↦ (T : E →L[ℝ] E))
      ⟨(fun x ↦ T x + c) ⁻¹' Ω, Ω.isOpen.preimage (T.continuous.add continuous_const)⟩ μ where
  locallyIntegrableOn :=
    (isDiffeoOnWithBoundedJacobian_affine T c Ω).locallyIntegrableOn_comp h.locallyIntegrableOn
  locallyIntegrableOn_weakDeriv :=
    ((isDiffeoOnWithBoundedJacobian_affine T c Ω).locallyIntegrableOn_comp
      h.locallyIntegrableOn_weakDeriv).comp_continuousLinearMap
      (ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ (T : E →L[ℝ] E))
  integral_smul_eq φ z := by
    have hF : ∀ x, T.symm (T x + c - c) = x := fun x ↦ by simp
    -- the transported test function `ψ = φ ∘ F⁻¹`
    obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(Ω, ℝ), ∀ y, ψ y = φ (T.symm (y - c)) := by
      refine ⟨⟨fun y ↦ φ (T.symm (y - c)),
        φ.contDiff.comp (T.symm.contDiff.comp (contDiff_id.sub contDiff_const)), ?_, ?_⟩,
        fun y ↦ rfl⟩
      · exact φ.hasCompactSupport.comp_homeomorph (T.affineHomeomorph c).symm
      · have key : tsupport (fun y ↦ φ (T.symm (y - c)))
            = (T.affineHomeomorph c).symm ⁻¹' tsupport φ := by
          rw [tsupport, tsupport, Homeomorph.preimage_closure,
            ← Function.support_comp_eq_preimage]
          rfl
        rw [key]
        intro y hy
        simpa using φ.tsupport_subset hy
    have hφ : (φ : E → ℝ) = fun x ↦ ψ (T x + c) := funext fun x ↦ by rw [hψ, hF]
    have hTz : ∀ x, iteratedFDeriv ℝ n (φ : E → ℝ) x z
        = iteratedFDeriv ℝ n (ψ : E → ℝ) (T x + c) fun i ↦ T (z i) := by
      intro x
      have e1 : (fun x ↦ ψ (T x + c)) = (fun u ↦ ψ (u + c)) ∘ ⇑(T : E →L[ℝ] E) := rfl
      have hψc : ContDiff ℝ ∞ fun u ↦ ψ (u + c) :=
        ψ.contDiff.comp (contDiff_id.add contDiff_const)
      rw [hφ, e1, ContinuousLinearMap.iteratedFDeriv_comp_right (T : E →L[ℝ] E) hψc x (by simp),
        ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_right]
      rfl
    have hL : ∫ x in (fun x ↦ T x + c) ⁻¹' (Ω : Set E),
        iteratedFDeriv ℝ n (ψ : E → ℝ) (T x + c) (fun i ↦ T (z i)) • v (T x + c) ∂μ
        = (ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹|).toReal •
          ∫ y in (Ω : Set E), iteratedFDeriv ℝ n (ψ : E → ℝ) y (fun i ↦ T (z i)) • v y ∂μ :=
      setIntegral_comp_affine (μ := μ) T c
        (fun y ↦ iteratedFDeriv ℝ n (ψ : E → ℝ) y (fun i ↦ T (z i)) • v y) Ω
    have hR : ∫ x in (fun x ↦ T x + c) ⁻¹' (Ω : Set E),
        ψ (T x + c) • w (T x + c) (fun i ↦ T (z i)) ∂μ
        = (ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹|).toReal •
          ∫ y in (Ω : Set E), ψ y • w y (fun i ↦ T (z i)) ∂μ :=
      setIntegral_comp_affine (μ := μ) T c (fun y ↦ ψ y • w y (fun i ↦ T (z i))) Ω
    have hid := h.integral_smul_eq ψ fun i ↦ T (z i)
    simp only [Opens.coe_mk, hTz]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, hφ]
    rw [hL, hR, hid, smul_comm]

end Affine
