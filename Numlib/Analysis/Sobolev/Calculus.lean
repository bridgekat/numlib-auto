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
# The calculus rules of `W^{1,p}(Ω)`

The calculus rules of Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
Equations*, §9.1: Proposition 9.4 (the product of two bounded `W^{1,p}` functions), Proposition
9.5 (composition with a `C^1` function with bounded derivative), Proposition 9.6 (change of
variables under a `C^1` diffeomorphism with bounded Jacobians), together with the affine change
of variables at every order and the positive part `u⁺`.

## Main results

* `IsDiffeoOnWithBoundedJacobian.eLpNorm_comp_le`, `.memLp_comp`: **transport of `L^p` norms
  under a diffeomorphism with bounded Jacobians**, `‖f ∘ H‖_{L^p(A)} ≤ D^{1/p} ‖f‖_{L^p(H(A))}`
  for a bound `D` on `|det Jac H⁻¹|`, by Mathlib's change of variables formula
  `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`; and
  `ContinuousLinearMap.exists_abs_det_le_mul_norm_pow`, the bound `|det L| ≤ C ‖L‖^N` that turns
  the Jacobian bound of the hypothesis bundle into a bound on the determinant;
* `HasWeakFDerivOn.comp_diffeoOn`: **Proposition 9.6, the identity**
  `∂(u ∘ H) = (∂u ∘ H) ∘ Jac H`, for a merely locally integrable `u` with a locally integrable
  weak derivative — the `L^p` hypotheses of the book are not needed for the identity, which is
  local: on a relatively compact open subset the function is approximated in `L^1` by smooth
  functions (`MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`), the classical chain rule applies
  to the approximants, and the weak derivative is closed under `L^1` limits
  (`hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one`);
* `MemSobolev.comp_diffeoOn` and `SobolevMultiIndex.compDiffeoL`: **Proposition 9.6** for
  `W^{1,p}(Ω)`, `1 ≤ p ≤ ∞`, as a membership statement and as a bounded linear map
  `W^{1,p}(Ω) → W^{1,p}(Ω')`, `u ↦ u ∘ H`, with the `L^p` bound on the function
  (`SobolevMultiIndex.eLpNorm_fn_compDiffeoL_le`); `SobolevEuclidean.compDiffeoL` is its
  instance on `ℝ^N`. These are the "transfer" and "retransfer" maps of the proof of the
  extension theorem;
* `SobolevMultiIndex.exists_hasWeakFDerivOn_fn`: the tensor weak derivative of an element of the
  multi-index space, with the bound `‖w‖_{L^p} ≤ C_b ∑ᵢ ‖∂ᵢ u‖_{L^p}` — the comparison
  "tensor norm ≤ multi-index norm" that every typed operator built from a tensor identity needs;
* `HasWeakIteratedLineDerivOn.mul_of_ae_norm_le`, `MemSobolevMultiIndex.mul_of_ae_norm_le`:
  **Proposition 9.4**, the product rule at the endpoint `L^p × L^∞`;
* `MemSobolevMultiIndex.contDiff_comp`: **Proposition 9.5**;
* `HasWeakIteratedFDerivOn.comp_affineEquiv`: the affine change of variables at every order;
* `MemSobolevMultiIndex.posPart`: the positive part of a `W^{1,p}` function.

## Design

Predicate-level statements are over a finite-dimensional real normed `E` with an additive Haar
measure `μ`; the change of variables is for a diffeomorphism `H : E → E` of the *same* space,
which is what Mathlib's Jacobian formula is stated for and what the charts of
`Numlib/Analysis/Sobolev/Chart.lean` are. The hypothesis bundle `IsDiffeoOnWithBoundedJacobian`
lives in `Chart.lean`; a chart restricted to `Q₊` is an instance.

The typed operators follow the pattern of `Numlib/Analysis/Sobolev/Cutoff.lean`: membership and
the bound at the predicate level, then `MemSobolevMultiIndex.exists_sobolevMultiIndex` and
`SobolevMultiIndex.ext_of_fn_ae_eq`. The operator norm of a bundled map is free
(`ContinuousLinearMap.le_opNorm`); only the `L^p` bound on the function is carried explicitly,
because the extension theorem states it separately.

## References

[brezis2011functional], §9.1, Propositions 9.4–9.6 and their proofs; §9.2, proof of Theorem 9.7,
step (b).
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

noncomputable section

/-! ### The determinant is bounded by a power of the norm -/

section Det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The determinant of a linear map is bounded by a constant times a power of its norm**:
there is `C` with `|det L| ≤ C ‖L‖^N` for every `L : E →L[ℝ] E`, `N = dim E`. The determinant
is continuous, hence bounded on the unit ball of the finite-dimensional space `E →L[ℝ] E`, and
homogeneous of degree `N`. -/
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

/-! ### Transport of `L^p` norms under a diffeomorphism with bounded Jacobians -/

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {H Hinv : E → E} {s t : Set E} {M : ℝ}

namespace IsDiffeoOnWithBoundedJacobian

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The image of an open subset of the source is open. -/
theorem isOpen_image (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E} (hA : IsOpen A)
    (hAs : A ⊆ s) : IsOpen (H '' A) := by
  have : H '' A = t ∩ Hinv ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h.bijOn.mapsTo (hAs hy), by rw [mem_preimage, h.invOn.1 (hAs hy)]; exact hy⟩
    · rintro ⟨hxt, hx⟩
      exact ⟨Hinv x, hx, h.invOn.2 hxt⟩
  rw [this]
  exact h.contDiffOn_invFun.continuousOn.isOpen_inter_preimage h.isOpen_target hA

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The image of a subset of the source lies in the target. -/
theorem image_subset (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E} (hAs : A ⊆ s) :
    H '' A ⊆ t :=
  (h.bijOn.mapsTo.mono_left hAs).image_subset

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `Hinv (H '' A) = A` for `A ⊆ s`. -/
theorem invFun_image_image (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E}
    (hAs : A ⊆ s) : Hinv '' (H '' A) = A :=
  (h.invOn.1.mono hAs).image_image

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The inverse is differentiable within any subset of the target, with the ordinary
derivative. -/
theorem hasFDerivWithinAt_invFun (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E}
    (hAt : A ⊆ t) {x : E} (hx : x ∈ A) : HasFDerivWithinAt Hinv (fderiv ℝ Hinv x) A x :=
  ((h.contDiffOn_invFun.differentiableOn one_ne_zero).differentiableAt
    (h.isOpen_target.mem_nhds (hAt hx))).hasFDerivAt.hasFDerivWithinAt

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The Jacobian bound gives a bound on the determinant** of the derivative of the inverse. -/
theorem exists_abs_det_fderiv_invFun_le (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ t, |(fderiv ℝ Hinv x).det| ≤ D := by
  obtain ⟨C, hC0, hC⟩ := ContinuousLinearMap.exists_abs_det_le_mul_norm_pow (E := E)
  refine ⟨C * max M 0 ^ finrank ℝ E, by positivity, fun x hx ↦ (hC _).trans ?_⟩
  gcongr
  exact (h.norm_fderiv_invFun_le x hx).trans (le_max_left _ _)

/-- **Almost everywhere statements pull back along the diffeomorphism**: a property holding
almost everywhere on `H '' A` holds at `H y` for almost every `y ∈ A`, because `Hinv` is
differentiable on the target and so maps null sets to null sets. -/
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

/-- Composition with the diffeomorphism preserves almost everywhere strong measurability. -/
theorem aestronglyMeasurable_comp (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E}
    (hA : IsOpen A) (hAs : A ⊆ s) {F : Type*} [TopologicalSpace F] [PseudoMetrizableSpace F]
    {f : E → F} (hf : AEStronglyMeasurable f (μ.restrict (H '' A))) :
    AEStronglyMeasurable (fun y ↦ f (H y)) (μ.restrict A) := by
  obtain ⟨g, hg, hfg⟩ := hf
  have hH : AEMeasurable H (μ.restrict A) :=
    (h.contDiffOn.continuousOn.mono hAs).aemeasurable hA.measurableSet
  have hfg' : (fun y ↦ f (H y)) =ᵐ[μ.restrict A] fun y ↦ g (H y) := h.ae_comp hA hAs hfg
  exact ((hg.aestronglyMeasurable (μ := (μ.restrict A).map H)).comp_aemeasurable hH).congr
    hfg'.symm

/-- **Transport of the Lebesgue integral**: for a bound `D` on `|det Jac Hinv|` on the target
and an open `A ⊆ s`, `∫_A g ∘ H ≤ D ∫_{H(A)} g`. This is Mathlib's change of variables formula
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` applied to `Hinv` on `H '' A`. -/
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

/-- **Transport of `L^p` norms under a diffeomorphism with bounded Jacobians**: for a bound `D`
on `|det Jac Hinv|` on the target and an open `A ⊆ s`,
`‖f ∘ H‖_{L^p(A)} ≤ D^{1/p} ‖f‖_{L^p(H(A))}`, for every `p` (at `p = ∞` the constant is `1` and
the statement is the transport of essential bounds). This is the `L^p` transport of
[brezis2011functional] Proposition 9.6, footnote 6. -/
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

/-- `L^p` membership transports along the diffeomorphism. -/
theorem memLp_comp (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {D : ℝ}
    (hD : ∀ x ∈ t, |(fderiv ℝ Hinv x).det| ≤ D) {A : Set E} (hA : IsOpen A) (hAs : A ⊆ s)
    {F : Type*} [NormedAddCommGroup F] {f : E → F} {p : ℝ≥0∞}
    (hf : MemLp f p (μ.restrict (H '' A))) : MemLp (fun y ↦ f (H y)) p (μ.restrict A) :=
  (h.eLpNorm_comp_le hD hA hAs hf.aestronglyMeasurable p).trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) hf)

/-- Composition with the diffeomorphism preserves local integrability. -/
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
/-- The composite `y ↦ (g (H y)) ∘ Jac H (y)` is almost everywhere strongly measurable on an
open `A ⊆ s` as soon as `g ∘ H` is. -/
theorem aestronglyMeasurable_comp_fderiv
    (h : IsDiffeoOnWithBoundedJacobian H Hinv s t M) {A : Set E} (hA : IsOpen A) (hAs : A ⊆ s)
    {g : E → E →L[ℝ] F} (hg : AEStronglyMeasurable (fun y ↦ g (H y)) (μ.restrict A)) :
    AEStronglyMeasurable (fun y ↦ (g (H y)).comp (fderiv ℝ H y)) (μ.restrict A) :=
  (ContinuousLinearMap.compL ℝ E E F).continuous₂.comp_aestronglyMeasurable₂ hg
    (((h.contDiffOn.continuousOn_fderiv_of_isOpen h.isOpen_source le_rfl).mono
      hAs).aestronglyMeasurable hA.measurableSet)

omit [μ.IsAddHaarMeasure] in
/-- **The Jacobian factor costs at most `M` in `L^p`**:
`‖(g ∘ H) ∘ Jac H‖_{L^p(A)} ≤ M ‖g ∘ H‖_{L^p(A)}`. -/
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

/-- Composition with the diffeomorphism, followed by the Jacobian, preserves local
integrability. -/
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

/-! ### Locality, and the local `W^{1,1}` membership -/

section Locality

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {μ : Measure E}
  {n : ℕ} {f : E → F} {w : E → E [×n]→L[ℝ] F}

/-- **Locality of the weak derivative**, tensor form: the counterpart of
`HasWeakIteratedLineDerivOn.of_forall_isCompact_closure_subset` for `HasWeakIteratedFDerivOn`. -/
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
/-- A function with a first-order weak derivative on `Ω` lies in `W^{1,1}` of every open set
with compact closure in `Ω`: both the function and the derivative are integrable on compact
subsets of `Ω`. -/
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

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The first iterated derivative is the uncurried first derivative. -/
theorem iteratedFDeriv_one_eq (f : E → F) (x : E) :
    iteratedFDeriv ℝ 1 f x = (continuousMultilinearCurryFin1 ℝ E F).symm (fderiv ℝ f x) := by
  ext m
  simp [iteratedFDeriv_one_apply]

/-- **Proposition 9.6 (change of variables), the identity**: for a `C^1` diffeomorphism
`H : Ω' → Ω` with bounded Jacobians and a first-order weak derivative `w` of `u` on `Ω`,
`u ∘ H` has the weak derivative `y ↦ (w (H y)) ∘ Jac H (y)` on `Ω'` — the book's
`∂_j (u ∘ H)(y) = ∑_i ∂_i u (H y) ∂_j H_i (y)` in tensor form. Only local integrability of `u`
and `w` is assumed, since the identity is local: on a relatively compact open `ω' ⋐ Ω'`, whose
image is a compact subset of `Ω`, `u` is approximated in `W^{1,1}` of a neighbourhood `V` of that
image by smooth functions `u_n` (`MemSobolev.exists_seq_contDiff_tendsto_eLpNorm`); the classical
chain rule gives the identity for `u_n ∘ H`; the transport of `L^1` norms
(`IsDiffeoOnWithBoundedJacobian.eLpNorm_comp_le`) gives `u_n ∘ H → u ∘ H` and
`(∂u_n ∘ H) ∘ Jac H → (w ∘ H) ∘ Jac H` in `L^1(ω')`; and the weak derivative is closed under `L^1`
limits (`hasWeakIteratedFDerivOn_of_tendsto_eLpNorm_one`). This is the proof of
[brezis2011functional] Proposition 9.6, with the local approximation in place of Theorem 9.2, and
the case `p = ∞` handled by the same locality. -/
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
    rw [iteratedFDeriv_one_eq, he]
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
          hyw, iteratedFDeriv_one_eq, ← he, ← map_sub, e.norm_map]
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

/-- Almost everywhere statements on `Ω` pull back to almost everywhere statements on `Ω'`
along the diffeomorphism `H : Ω' → Ω`. -/
theorem IsDiffeoOnWithBoundedJacobian.ae_comp_restrict
    (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) {P : E → Prop}
    (hP : ∀ᵐ x ∂μ.restrict (Ω : Set E), P x) : ∀ᵐ y ∂μ.restrict (Ω' : Set E), P (H y) :=
  h.ae_comp Ω'.isOpen subset_rfl (by rw [h.bijOn.image_eq]; exact hP)

/-- **Proposition 9.6 (change of variables), membership**: for a `C^1` diffeomorphism
`H : Ω' → Ω` with bounded Jacobians and `u ∈ W^{1,p}(Ω)`, `1 ≤ p ≤ ∞`, the composite
`u ∘ H` lies in `W^{1,p}(Ω')` ([brezis2011functional] Proposition 9.6). The identity is
`HasWeakFDerivOn.comp_diffeoOn`; the `L^p` memberships are the transport
`IsDiffeoOnWithBoundedJacobian.memLp_comp` and the Jacobian bound. -/
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

/-! ### The tensor weak derivative of an element of the multi-index space

The typed operators below are built from identities in tensor form (`HasWeakFDerivOn`), while
the norm of `SobolevMultiIndex` is the `ℓ^p` sum of the partial derivatives `∂ᵢ u = w(bᵢ)`. The
comparison `‖w‖ ≤ C_b ∑ᵢ ‖w (bᵢ)‖` (`Basis.opNorm_le`) is what bounds the tensor by the
multi-index data. -/

section TensorDerivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E}

namespace SobolevMultiIndex

/-- **The tensor weak derivative of `u ∈ W^{1,p}(Ω)`**, in the multi-index formulation: a
first-order weak derivative `w : E → E →L[ℝ] F` of `fn u` on `Ω`, in `L^p(Ω)`, whose values on the
basis vectors are the partial derivatives, `w x (b i) = ∂ᵢ u x` almost everywhere, and with
`‖w‖_{L^p(Ω)} ≤ C_b ∑ᵢ ‖∂ᵢ u‖_{L^p(Ω)}` for the constant `C_b` of `Basis.opNorm_le`. -/
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
/-- **A norm bound on `W^{1,p}(Ω')` from bounds on the function and the partial derivatives**:
if `‖v‖_{L^p(Ω')} ≤ A ‖u‖_{L^p(Ω)}` and `‖∂ᵢ v‖_{L^p(Ω')} ≤ B ∑ⱼ ‖∂ⱼ u‖_{L^p(Ω)}` for every `i`,
then `‖v‖ ≤ (A + card ι² B) ‖u‖`. This is the constant bookkeeping shared by the typed operators
built from a tensor identity. -/
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
/-- Proposition 9.6 in the multi-index formulation of `W^{1,p}`. -/
theorem MemSobolevMultiIndex.comp_diffeoOn {u : E → F}
    (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) (hu : MemSobolevMultiIndex b u 1 p Ω μ) :
    MemSobolevMultiIndex b (fun y ↦ u (H y)) 1 p Ω' μ :=
  (hu.memSobolev.comp_diffeoOn h).memSobolevMultiIndex

namespace SobolevMultiIndex

/-- **The change of variables `u ↦ u ∘ H` of Proposition 9.6 on the typed spaces**, as a
function: the element of `W^{1,p}(Ω')` whose function is `u ∘ H`
(`MemSobolevMultiIndex.comp_diffeoOn` and `MemSobolevMultiIndex.exists_sobolevMultiIndex`). It is
linear and bounded; `SobolevMultiIndex.compDiffeoL` is its bundled form. -/
def compDiffeo (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (u : SobolevMultiIndex F b 1 p Ω μ) : SobolevMultiIndex F b 1 p Ω' μ :=
  ((memSobolevMultiIndex u).comp_diffeoOn h).exists_sobolevMultiIndex.choose

/-- The function of `SobolevMultiIndex.compDiffeo h u` is `u ∘ H`. -/
theorem fn_compDiffeo (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (u : SobolevMultiIndex F b 1 p Ω μ) :
    fn (compDiffeo h u) =ᵐ[μ.restrict (Ω' : Set E)] fun y ↦ fn u (H y) :=
  ((memSobolevMultiIndex u).comp_diffeoOn h).exists_sobolevMultiIndex.choose_spec

/-- The change of variables is additive. -/
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

/-- The change of variables commutes with scalar multiplication. -/
theorem compDiffeo_smul (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) (c : ℝ)
    (u : SobolevMultiIndex F b 1 p Ω μ) : compDiffeo h (c • u) = c • compDiffeo h u := by
  refine ext_of_fn_ae_eq ?_
  have h1 : (fun y ↦ fn (c • u) (H y)) =ᵐ[μ.restrict (Ω' : Set E)] fun y ↦ c • fn u (H y) :=
    h.ae_comp_restrict (P := fun x ↦ fn (c • u) x = c • fn u x) (fn_smul c u)
  refine (fn_compDiffeo h (c • u)).trans (h1.trans ?_)
  refine EventuallyEq.trans ?_ (fn_smul _ _).symm
  filter_upwards [fn_compDiffeo h u] with y hyu
  rw [Pi.smul_apply, hyu]

/-- **The `L^p` bound on the change of variables**:
`‖u ∘ H‖_{L^p(Ω')} ≤ D^{1/p} ‖u‖_{L^p(Ω)}` for a bound `D` on `|det Jac H⁻¹|` on `Ω`. -/
theorem eLpNorm_fn_compDiffeo_le (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) {D : ℝ}
    (hD : ∀ x ∈ (Ω : Set E), |(fderiv ℝ Hinv x).det| ≤ D) (u : SobolevMultiIndex F b 1 p Ω μ) :
    eLpNorm (fn (compDiffeo h u)) p (μ.restrict (Ω' : Set E))
      ≤ ENNReal.ofReal D ^ (1 / p.toReal) * eLpNorm (fn u) p (μ.restrict (Ω : Set E)) := by
  rw [eLpNorm_congr_ae (fn_compDiffeo h u)]
  have := h.eLpNorm_comp_le hD Ω'.isOpen subset_rfl
    (f := fn u) (by rw [h.bijOn.image_eq]; exact (memLp u).aestronglyMeasurable) p
  rwa [h.bijOn.image_eq] at this

/-- The partial derivatives of `u ∘ H` are `(∂u ∘ H) (∂ᵢ H)`, in terms of a tensor weak
derivative `w` of `u`: `∂ᵢ (u ∘ H) (y) = w (H y) (Jac H (y) bᵢ)` almost everywhere on `Ω'`. -/
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

/-- **The change of variables is bounded on `W^{1,p}`**: `‖u ∘ H‖ ≤ C ‖u‖` for a constant
depending on the Jacobian bound, the determinant bound, the basis and `p`. -/
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
    have hwH : MemLp (fun y ↦ w (H y)) p (μ.restrict (Ω' : Set E)) :=
      h.memLp_comp hD Ω'.isOpen subset_rfl (by rw [h.bijOn.image_eq]; exact hwp)
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
/-- The change of variables `u ↦ u ∘ H` as a linear map `W^{1,p}(Ω) → W^{1,p}(Ω')`. -/
def compDiffeoₗ (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) :
    SobolevMultiIndex F b 1 p Ω μ →ₗ[ℝ] SobolevMultiIndex F b 1 p Ω' μ where
  toFun := compDiffeo h
  map_add' := compDiffeo_add h
  map_smul' := compDiffeo_smul h

variable (F b p μ) in
/-- **Proposition 9.6 as a bounded linear map `W^{1,p}(Ω) → W^{1,p}(Ω')`**, `u ↦ u ∘ H`, for a
`C^1` diffeomorphism `H : Ω' → Ω` with bounded Jacobians ([brezis2011functional] Proposition
9.6): its function is `u ∘ H` (`SobolevMultiIndex.fn_compDiffeoL`) and its `L^p` norm is bounded
by `D^{1/p} ‖u‖_{L^p(Ω)}` (`SobolevMultiIndex.eLpNorm_fn_compDiffeoL_le`). These are the
"transfer" `v = u ∘ H` and "retransfer" `w = v^⋆ ∘ H⁻¹` maps of the proof of the extension
theorem, step (b). -/
def compDiffeoL (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) :
    SobolevMultiIndex F b 1 p Ω μ →L[ℝ] SobolevMultiIndex F b 1 p Ω' μ :=
  (compDiffeoₗ F b p μ h).mkContinuousOfExistsBound (exists_norm_compDiffeo_le h)

/-- `SobolevMultiIndex.compDiffeoL` is `SobolevMultiIndex.compDiffeo`. -/
@[simp]
theorem compDiffeoL_apply (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (u : SobolevMultiIndex F b 1 p Ω μ) : compDiffeoL F b p μ h u = compDiffeo h u :=
  rfl

/-- The function of `SobolevMultiIndex.compDiffeoL h u` is `u ∘ H`. -/
theorem fn_compDiffeoL (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M)
    (u : SobolevMultiIndex F b 1 p Ω μ) :
    fn (compDiffeoL F b p μ h u) =ᵐ[μ.restrict (Ω' : Set E)] fun y ↦ fn u (H y) :=
  fn_compDiffeo h u

/-- The `L^p` bound on `SobolevMultiIndex.compDiffeoL`. -/
theorem eLpNorm_fn_compDiffeoL_le (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) {D : ℝ}
    (hD : ∀ x ∈ (Ω : Set E), |(fderiv ℝ Hinv x).det| ≤ D) (u : SobolevMultiIndex F b 1 p Ω μ) :
    eLpNorm (fn (compDiffeoL F b p μ h u)) p (μ.restrict (Ω' : Set E))
      ≤ ENNReal.ofReal D ^ (1 / p.toReal) * eLpNorm (fn u) p (μ.restrict (Ω : Set E)) :=
  eLpNorm_fn_compDiffeo_le h hD u

/-- The `L^p` bound on `SobolevMultiIndex.compDiffeoL`, with the constant existential. -/
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

/-- **Proposition 9.6 on `W^{1,p}(Ω) ⊆ ℝ^N`**, as a bounded linear map
`W^{1,p}(Ω) → W^{1,p}(Ω')`, `u ↦ u ∘ H`: `SobolevMultiIndex.compDiffeoL` on
`SobolevEuclidean N 1 p Ω`, with `SobolevMultiIndex.fn_compDiffeoL` and
`SobolevMultiIndex.eLpNorm_fn_compDiffeoL_le` for its function and its `L^p` bound. -/
noncomputable abbrev SobolevEuclidean.compDiffeoL
    (h : IsDiffeoOnWithBoundedJacobian H Hinv Ω' Ω M) :
    SobolevEuclidean N 1 p Ω →L[ℝ] SobolevEuclidean N 1 p Ω' :=
  SobolevMultiIndex.compDiffeoL ℝ (EuclideanSpace.basisFun (Fin N) ℝ).toBasis p volume h

end Euclidean

/-! ### Propositions 9.4 and 9.5: products and compositions

The chain rule `HasWeakIteratedLineDerivOn.contDiff_comp` of `Mollification.lean` is local: it
asks for `L^p_loc` memberships for one finite `p`, and the local integrability built into the weak
derivative is the case `p = 1`. So the identity of Proposition 9.5 holds without any exponent
hypothesis (`HasWeakIteratedLineDerivOn.contDiff_comp'`), and the locality argument by which the
book handles `p = ∞` is not needed. Proposition 9.4 is then read off the chain rule through the
polarization identity `u v = ½ ((u + v)² − u² − v²)`, the square of a bounded function being the
composition with a `C^1` function equal to `t²` on the range and with bounded derivative
(`sqCutoff`): no approximation argument at the endpoint `L^p × L^∞` is needed. -/

section SqCutoff

/-- `∫_0^s x dx = s²/2`. -/
theorem intervalIntegral_id_mul_self_div_two (s : ℝ) : ∫ x in (0 : ℝ)..s, x = s * s / 2 := by
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x ↦ x * x / 2)
    (f' := fun x ↦ x) (a := 0) (b := s)
    (fun x _ ↦ (((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const 2).congr_deriv (by
      simp only [id]; ring)) (continuous_id.intervalIntegrable _ _)
  rw [this]; ring

/-- The `C^1` function `t ↦ ∫_0^t 2 clamp_{[-M, M]}(s) ds`, equal to `t²` on `[-M, M]` and with
derivative bounded by `2M`. It is what makes the square of a function bounded by `M` a composition
to which Proposition 9.5 applies. -/
def sqCutoff (M t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, 2 * max (-M) (min M s)

/-- The integrand of `sqCutoff` is continuous. -/
theorem continuous_sqCutoff_integrand (M : ℝ) : Continuous fun s : ℝ ↦ 2 * max (-M) (min M s) :=
  continuous_const.mul (continuous_const.max (continuous_const.min continuous_id))

/-- The derivative of `sqCutoff M` is `2 clamp_{[-M, M]}`. -/
theorem deriv_sqCutoff (M t : ℝ) : deriv (sqCutoff M) t = 2 * max (-M) (min M t) :=
  Continuous.deriv_integral _ (continuous_sqCutoff_integrand M) 0 t

/-- `sqCutoff M` is `C^1`. -/
theorem contDiff_sqCutoff (M : ℝ) : ContDiff ℝ 1 (sqCutoff M) := by
  refine contDiff_one_iff_deriv.2 ⟨fun t ↦ ?_, ?_⟩
  · exact ((continuous_sqCutoff_integrand M).integral_hasStrictDerivAt 0 t).hasDerivAt
      |>.differentiableAt
  · rw [funext (deriv_sqCutoff M)]
    exact continuous_sqCutoff_integrand M

/-- The derivative of `sqCutoff M` is bounded by `2M`. -/
theorem abs_deriv_sqCutoff_le {M : ℝ} (hM : 0 ≤ M) (t : ℝ) : |deriv (sqCutoff M) t| ≤ 2 * M := by
  rw [deriv_sqCutoff, abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨le_max_left _ _, max_le (by linarith) ?_⟩) two_pos.le
  exact min_le_left _ _

/-- On `[-M, M]` the derivative of `sqCutoff M` is `2t`. -/
theorem deriv_sqCutoff_of_abs_le {M t : ℝ} (ht : |t| ≤ M) : deriv (sqCutoff M) t = 2 * t := by
  rw [deriv_sqCutoff, min_eq_right (abs_le.1 ht).2, max_eq_right (abs_le.1 ht).1]

/-- On `[-M, M]` the function `sqCutoff M` is `t²`. -/
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

/-- **The chain rule for weak derivatives, without exponent hypotheses**: for `f : ℝ → ℝ` of class
`C^1` with `|f'| ≤ M`, and `w` the weak derivative of `v` along `y` on `Ω`,
`(f' ∘ v) w` is the weak derivative of `f ∘ v` along `y`. This is
`HasWeakIteratedLineDerivOn.contDiff_comp` at `p = 1`, where the `L^1_loc` hypotheses are the
local integrability built into the weak derivative: the identity of [brezis2011functional]
Proposition 9.5 is local, and the reduction of the case `p = ∞` to `p < ∞` of the book's proof is
not needed. -/
theorem HasWeakIteratedLineDerivOn.contDiff_comp' {v w : E → ℝ}
    (h : HasWeakIteratedLineDerivOn ![y] v w Ω μ) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ}
    (hM : ∀ t, |deriv f t| ≤ M) :
    HasWeakIteratedLineDerivOn ![y] (fun x ↦ f (v x)) (fun x ↦ deriv f (v x) * w x) Ω μ :=
  h.contDiff_comp rfl hf hM le_rfl ENNReal.one_ne_top h.locallyIntegrableOn.locallyMemLpOn
    h.locallyIntegrableOn_weakDeriv.locallyMemLpOn

/-- **The square of a bounded weakly differentiable function**: if `w` is the weak derivative of
`u` along `y` on `Ω` and `|u| ≤ M` almost everywhere on `Ω`, then `2 u w` is the weak derivative
of `u²`. The chain rule with `sqCutoff M`, which is `t²` on the range of `u`. -/
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

/-- **Proposition 9.4, the identity**: for `u` and `v` weakly differentiable along `y` on `Ω`
with weak derivatives `wu`, `wv`, both bounded by `M` almost everywhere on `Ω`,
`wu v + u wv` is the weak derivative of `u v` along `y`. By polarization,
`u v = ½ ((u + v)² − u² − v²)`, and the square of a bounded function is
`HasWeakIteratedLineDerivOn.mul_self_of_ae_abs_le`. No `L^p` hypothesis is needed: the endpoint
`L^p × L^∞` of [brezis2011functional] Proposition 9.4, which the product rule
`HasWeakIteratedLineDerivOn.mul` for conjugate exponents does not cover, is reached through the
chain rule instead of the book's approximation argument. -/
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

/-- **Proposition 9.5** of [brezis2011functional] §9.1: for `G : ℝ → ℝ` of class `C^1` with
`G 0 = 0` and `|G'| ≤ M`, and `u ∈ W^{1,p}(Ω)`, `1 ≤ p ≤ ∞`, the composite `G ∘ u` lies in
`W^{1,p}(Ω)`; its weak derivatives are `(G' ∘ u) ∂_i u`
(`HasWeakIteratedLineDerivOn.contDiff_comp'`). The memberships are the bounds `|G s| ≤ M |s|`
and `|G'(u) ∂_i u| ≤ M |∂_i u|`. -/
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

/-- **Proposition 9.4** of [brezis2011functional] §9.1: for `u, v ∈ W^{1,p}(Ω) ∩ L^∞(Ω)`,
`1 ≤ p ≤ ∞`, both bounded by `M` almost everywhere on `Ω`, the product `u v` lies in
`W^{1,p}(Ω) ∩ L^∞(Ω)`, bounded by `M²`; its weak derivatives are `(∂_i u) v + u (∂_i v)`
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

/-! ### The positive part

The positive part `u⁺ = max u 0` of a `W^{1,p}` function is again in `W^{1,p}`, with
`∂_i u⁺ = {u > 0}.indicator (∂_i u)`: Gilbarg–Trudinger, *Elliptic Partial Differential Equations
of Second Order*, Lemma 7.6. The proof applies the chain rule to the `C^1` approximations
`G_ε(s) = √((max s 0)² + ε²) − ε` of `s ↦ max s 0`, whose derivatives `max s 0 / √((max s 0)² + ε²)`
are bounded by `1` and tend to `{s > 0}.indicator 1`, and passes to the limit `ε → 0` in the
defining identity by dominated convergence. -/

section PosPart

/-- `(max s 0)²`, written as `∫_0^s 2 max t 0 dt` so that it is visibly `C^1`. -/
def posSq (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, 2 * max t 0

/-- The integrand of `posSq` is continuous. -/
theorem continuous_posSq_integrand : Continuous fun t : ℝ ↦ 2 * max t 0 :=
  continuous_const.mul (continuous_id.max continuous_const)

/-- The derivative of `posSq` is `2 max s 0`. -/
theorem hasDerivAt_posSq (s : ℝ) : HasDerivAt posSq (2 * max s 0) s :=
  (continuous_posSq_integrand.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- `posSq` is `C^1`. -/
theorem contDiff_posSq : ContDiff ℝ 1 posSq := by
  refine contDiff_one_iff_deriv.2 ⟨fun s ↦ (hasDerivAt_posSq s).differentiableAt, ?_⟩
  rw [funext fun s ↦ (hasDerivAt_posSq s).deriv]
  exact continuous_posSq_integrand

/-- `posSq s = (max s 0)²`. -/
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

/-- `posSq` is nonnegative. -/
theorem posSq_nonneg (s : ℝ) : 0 ≤ posSq s := by
  rw [posSq_eq]; exact mul_self_nonneg _

/-- `√(posSq s) = max s 0`. -/
theorem sqrt_posSq (s : ℝ) : √(posSq s) = max s 0 := by
  rw [posSq_eq, Real.sqrt_mul_self (le_max_right _ _)]

/-- The `C^1` approximation `G_ε(s) = √((max s 0)² + ε²) − ε` of the positive part `max s 0`. -/
def posPartApprox (ε s : ℝ) : ℝ := √(posSq s + ε ^ 2) - ε

/-- `G_ε(0) = 0`. -/
theorem posPartApprox_zero {ε : ℝ} (hε : 0 ≤ ε) : posPartApprox ε 0 = 0 := by
  simp [posPartApprox, posSq_eq, Real.sqrt_sq hε]

/-- `posSq s + ε² > 0` for `ε > 0`. -/
theorem posSq_add_sq_pos {ε : ℝ} (hε : 0 < ε) (s : ℝ) : 0 < posSq s + ε ^ 2 :=
  add_pos_of_nonneg_of_pos (posSq_nonneg s) (pow_pos hε 2)

/-- `G_ε` is `C^1` for `ε > 0`. -/
theorem contDiff_posPartApprox {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (posPartApprox ε) :=
  ((contDiff_posSq.add contDiff_const).sqrt fun s ↦ (posSq_add_sq_pos hε s).ne').sub
    contDiff_const

/-- The derivative of `G_ε` is `max s 0 / √((max s 0)² + ε²)`. -/
theorem deriv_posPartApprox {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    deriv (posPartApprox ε) s = max s 0 / √(posSq s + ε ^ 2) := by
  have h : HasDerivAt (posPartApprox ε) (2 * max s 0 / (2 * √(posSq s + ε ^ 2))) s :=
    (((hasDerivAt_posSq s).add_const (ε ^ 2)).sqrt (posSq_add_sq_pos hε s).ne').sub_const ε
  rw [h.deriv, mul_div_mul_left _ _ two_ne_zero]

/-- The derivative of `G_ε` lies in `[0, 1]`. -/
theorem deriv_posPartApprox_mem_Icc {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    deriv (posPartApprox ε) s ∈ Icc (0 : ℝ) 1 := by
  rw [deriv_posPartApprox hε]
  have hpos : 0 < √(posSq s + ε ^ 2) := Real.sqrt_pos.2 (posSq_add_sq_pos hε s)
  refine ⟨div_nonneg (le_max_right _ _) hpos.le, (div_le_one hpos).2 ?_⟩
  calc max s 0 = √(posSq s) := (sqrt_posSq s).symm
    _ ≤ √(posSq s + ε ^ 2) := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))

/-- The derivative of `G_ε` is bounded by `1`. -/
theorem abs_deriv_posPartApprox_le {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    |deriv (posPartApprox ε) s| ≤ 1 :=
  abs_le.2 ⟨by linarith [(deriv_posPartApprox_mem_Icc hε s).1],
    (deriv_posPartApprox_mem_Icc hε s).2⟩

/-- `0 ≤ G_ε(s) ≤ max s 0`. -/
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

/-- `|G_ε(s)| ≤ |s|`. -/
theorem abs_posPartApprox_le {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) : |posPartApprox ε s| ≤ |s| := by
  rw [abs_of_nonneg (posPartApprox_mem_Icc hε s).1]
  exact (posPartApprox_mem_Icc hε s).2.trans (max_le (le_abs_self s) (abs_nonneg s))

/-- `G_ε(s) → max s 0` as `ε → 0`. -/
theorem tendsto_posPartApprox (s : ℝ) :
    Tendsto (fun ε ↦ posPartApprox ε s) (𝓝 0) (𝓝 (max s 0)) := by
  have hc : Continuous fun ε : ℝ ↦ posPartApprox ε s :=
    (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2))).sub continuous_id
  simpa [posPartApprox, sqrt_posSq] using hc.tendsto 0

/-- `G_ε'(s) → {s > 0}.indicator 1` as `ε → 0`. -/
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
/-- `{u > 0}.indicator w` is measurable when `u` and `w` are. -/
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

/-- **The positive part of a weakly differentiable function** (Gilbarg–Trudinger Lemma 7.6, the
identity): if `w` is the weak derivative of `u` along `y` on `Ω`, then `{u > 0}.indicator w` is
the weak derivative of `u⁺ = max u 0`. The chain rule for `G_ε(s) = √((max s 0)² + ε²) − ε`
(`HasWeakIteratedLineDerivOn.contDiff_comp'`) and dominated convergence as `ε → 0`, with
`|G_ε(u)| ≤ |u|` and `|G_ε'(u) w| ≤ |w|`. -/
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

/-- **The positive part of a `W^{1,p}` function lies in `W^{1,p}`** (Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Lemma 7.6; Kinderlehrer–Stampacchia
Theorem A.1): for `u ∈ W^{1,p}(Ω)`, `1 ≤ p ≤ ∞`, `u⁺ = max u 0 ∈ W^{1,p}(Ω)`, with
`∂_i u⁺ = {u > 0}.indicator (∂_i u)` (`HasWeakIteratedLineDerivOn.posPart`). This is what makes
the obstacle set `{v ∈ H¹₀(Ω) : v ≥ ψ}` nonempty. -/
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

/-! ### Stampacchia's truncation

The truncation functions `G` of Stampacchia's method ([brezis2011functional] §9.7, proof of
Theorem 9.27, conditions (i)–(iii)): `C¹`, nondecreasing, vanishing on `(-∞, 0]`, positive on
`(0, ∞)`, with bounded derivative. `stampacchiaTruncation` is `s ↦ ∫₀ˢ min (max t 0) 1 dt` and
`stampacchiaTruncationSqrt` the auxiliary `H = ∫₀ᵗ √G'` of Proposition 9.29; `G(u)` is placed in
`W^{1,p}` by the chain rule of this file, as `posSq` is. -/

section Truncation

/-- The derivative of Stampacchia's truncation: `t ↦ min (max t 0) 1`, continuous, with values in
`[0, 1]`, vanishing on `(-∞, 0]` and positive on `(0, ∞)`. -/
def stampacchiaTruncationDeriv (t : ℝ) : ℝ := min (max t 0) 1

theorem continuous_stampacchiaTruncationDeriv : Continuous stampacchiaTruncationDeriv :=
  (continuous_id.max continuous_const).min continuous_const

theorem stampacchiaTruncationDeriv_nonneg (t : ℝ) : 0 ≤ stampacchiaTruncationDeriv t :=
  le_min (le_max_right _ _) zero_le_one

theorem stampacchiaTruncationDeriv_le_one (t : ℝ) : stampacchiaTruncationDeriv t ≤ 1 :=
  min_le_right _ _

theorem stampacchiaTruncationDeriv_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    stampacchiaTruncationDeriv t = 0 := by
  rw [stampacchiaTruncationDeriv, max_eq_right ht, min_eq_left zero_le_one]

theorem stampacchiaTruncationDeriv_pos {t : ℝ} (ht : 0 < t) : 0 < stampacchiaTruncationDeriv t :=
  lt_min (lt_max_of_lt_left ht) one_pos

/-- **Stampacchia's truncation** `G(s) = ∫₀ˢ min (max t 0) 1 dt`: of class `C¹`, `G = 0` on
`(-∞, 0]`, `G(s) = s²/2` on `[0, 1]` and `G(s) = s − 1/2` on `[1, ∞)`, with `0 ≤ G' ≤ 1` and
`G' > 0` on `(0, ∞)`. It is the function `G` of the proof of [brezis2011functional] Theorem 9.27
(conditions (i)–(iii) there, with `M = 1`). -/
def stampacchiaTruncation (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, stampacchiaTruncationDeriv t

theorem hasDerivAt_stampacchiaTruncation (s : ℝ) :
    HasDerivAt stampacchiaTruncation (stampacchiaTruncationDeriv s) s :=
  (continuous_stampacchiaTruncationDeriv.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- The derivative of the truncation `G` is `min (max s 0) 1`. -/
theorem deriv_stampacchiaTruncation (s : ℝ) :
    deriv stampacchiaTruncation s = stampacchiaTruncationDeriv s :=
  (hasDerivAt_stampacchiaTruncation s).deriv

/-- The truncation `G` is `C¹`: its derivative `min (max s 0) 1` is continuous. -/
theorem contDiff_stampacchiaTruncation : ContDiff ℝ 1 stampacchiaTruncation := by
  refine contDiff_one_iff_deriv.2
    ⟨fun s ↦ (hasDerivAt_stampacchiaTruncation s).differentiableAt, ?_⟩
  rw [funext deriv_stampacchiaTruncation]
  exact continuous_stampacchiaTruncationDeriv

theorem stampacchiaTruncation_of_nonpos {s : ℝ} (hs : s ≤ 0) : stampacchiaTruncation s = 0 := by
  unfold stampacchiaTruncation
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun _ ht ↦ ?_).trans
    intervalIntegral.integral_zero
  rw [uIcc_of_ge hs] at ht
  exact stampacchiaTruncationDeriv_of_nonpos ht.2

theorem stampacchiaTruncation_pos {s : ℝ} (hs : 0 < s) : 0 < stampacchiaTruncation s :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    (continuous_stampacchiaTruncationDeriv.intervalIntegrable _ _)
    (fun _ ht ↦ stampacchiaTruncationDeriv_pos ht.1) hs

theorem stampacchiaTruncation_nonneg (s : ℝ) : 0 ≤ stampacchiaTruncation s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [stampacchiaTruncation_of_nonpos hs]
  · exact (stampacchiaTruncation_pos hs).le

/-- The truncation `G` is strictly increasing on `(0, ∞)`, where `G' > 0`. -/
theorem strictMonoOn_stampacchiaTruncation : StrictMonoOn stampacchiaTruncation (Ioi 0) :=
  strictMonoOn_of_deriv_pos (convex_Ioi 0) contDiff_stampacchiaTruncation.continuous.continuousOn
    fun s hs ↦ by
      rw [interior_Ioi] at hs
      rw [deriv_stampacchiaTruncation]
      exact stampacchiaTruncationDeriv_pos hs

/-- **The truncation functions of Stampacchia's method**: `G ∈ C¹(ℝ)` with `|G'| ≤ M`, `G' ≥ 0`,
`G = 0` on `(-∞, 0]` and `G > 0` on `(0, ∞)` — the conditions (i)–(iii) of the proof of
[brezis2011functional] Theorem 9.27 in the form the engine `Elliptic.le_of_forall_truncation_mem`
of `Numlib/Analysis/PDE/Elliptic/MaximumPrinciple.lean`
uses (strict monotonicity on `(0, ∞)` enters only through `G > 0` there). -/
structure IsStampacchiaTruncation (G : ℝ → ℝ) (M : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 G
  abs_deriv_le : ∀ s, |deriv G s| ≤ M
  deriv_nonneg : ∀ s, 0 ≤ deriv G s
  eq_zero_of_nonpos : ∀ s, s ≤ 0 → G s = 0
  pos_of_pos : ∀ s, 0 < s → 0 < G s

namespace IsStampacchiaTruncation

variable {G : ℝ → ℝ} {M : ℝ}

theorem nonneg (hG : IsStampacchiaTruncation G M) (s : ℝ) : 0 ≤ G s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [hG.eq_zero_of_nonpos s hs]
  · exact (hG.pos_of_pos s hs).le

/-- `t G(t) ≥ 0`. -/
theorem mul_nonneg (hG : IsStampacchiaTruncation G M) (t : ℝ) : 0 ≤ t * G t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [hG.eq_zero_of_nonpos t ht, mul_zero]
  · exact _root_.mul_nonneg ht.le (hG.nonneg t)

/-- `t G(t) = 0` exactly when `t ≤ 0`. -/
theorem mul_eq_zero_iff (hG : IsStampacchiaTruncation G M) {t : ℝ} : t * G t = 0 ↔ t ≤ 0 := by
  constructor
  · intro h
    by_contra ht
    push Not at ht
    exact (_root_.mul_pos ht (hG.pos_of_pos t ht)).ne' h
  · intro ht
    rw [hG.eq_zero_of_nonpos t ht, mul_zero]

theorem zero (hG : IsStampacchiaTruncation G M) : G 0 = 0 := hG.eq_zero_of_nonpos 0 le_rfl

/-- The shifted truncation `t ↦ G (t − K)` is `C¹` with the same derivative bound. -/
theorem contDiff_sub (hG : IsStampacchiaTruncation G M) (K : ℝ) :
    ContDiff ℝ 1 fun t ↦ G (t - K) :=
  hG.contDiff.comp (contDiff_id.sub contDiff_const)

theorem abs_deriv_sub_le (hG : IsStampacchiaTruncation G M) (K t : ℝ) :
    |deriv (fun t ↦ G (t - K)) t| ≤ M := by
  rw [deriv_comp_sub_const G K t]; exact hG.abs_deriv_le _

end IsStampacchiaTruncation

/-- The truncation `G s = ∫₀^s min (max t 0) 1 dt` is a Stampacchia truncation with `M = 1`. -/
theorem isStampacchiaTruncation_stampacchiaTruncation :
    IsStampacchiaTruncation stampacchiaTruncation 1 where
  contDiff := contDiff_stampacchiaTruncation
  abs_deriv_le s := by
    rw [deriv_stampacchiaTruncation, abs_of_nonneg (stampacchiaTruncationDeriv_nonneg s)]
    exact stampacchiaTruncationDeriv_le_one s
  deriv_nonneg s := by rw [deriv_stampacchiaTruncation]; exact stampacchiaTruncationDeriv_nonneg s
  eq_zero_of_nonpos _ hs := stampacchiaTruncation_of_nonpos hs
  pos_of_pos _ hs := stampacchiaTruncation_pos hs

/-- **The truncation function of Stampacchia's method exists**: a `G ∈ C¹(ℝ)` with `|G'| ≤ 1`,
`G' ≥ 0`, strictly increasing on `(0, ∞)`, `G = 0` on `(-∞, 0]` and `G ≥ 0` — the function of the
proof of [brezis2011functional] Theorem 9.27, conditions (i)–(iii) with `M = 1`
(`stampacchiaTruncation`). -/
theorem exists_stampacchiaTruncation :
    ∃ G : ℝ → ℝ, IsStampacchiaTruncation G 1 ∧ StrictMonoOn G (Ioi 0) ∧ ∀ s, 0 ≤ G s :=
  ⟨stampacchiaTruncation, isStampacchiaTruncation_stampacchiaTruncation,
    strictMonoOn_stampacchiaTruncation, stampacchiaTruncation_nonneg⟩

/-- **The auxiliary function `H(t) = ∫₀ᵗ √(G'(s)) ds`** of the proof of [brezis2011functional]
Proposition 9.29, for Stampacchia's truncation: `C¹` with `H' = √G'`, so that `|∇H(u)|² =
|∇u|² G'(u)`. -/
def stampacchiaTruncationSqrt (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, √(stampacchiaTruncationDeriv t)

theorem continuous_sqrt_stampacchiaTruncationDeriv :
    Continuous fun t ↦ √(stampacchiaTruncationDeriv t) :=
  continuous_stampacchiaTruncationDeriv.sqrt

theorem hasDerivAt_stampacchiaTruncationSqrt (s : ℝ) :
    HasDerivAt stampacchiaTruncationSqrt (√(stampacchiaTruncationDeriv s)) s :=
  (continuous_sqrt_stampacchiaTruncationDeriv.integral_hasStrictDerivAt 0 s).hasDerivAt

theorem deriv_stampacchiaTruncationSqrt (s : ℝ) :
    deriv stampacchiaTruncationSqrt s = √(stampacchiaTruncationDeriv s) :=
  (hasDerivAt_stampacchiaTruncationSqrt s).deriv

/-- `H'(s)² = G'(s)`. -/
theorem sq_deriv_stampacchiaTruncationSqrt (s : ℝ) :
    deriv stampacchiaTruncationSqrt s ^ 2 = deriv stampacchiaTruncation s := by
  rw [deriv_stampacchiaTruncationSqrt, deriv_stampacchiaTruncation,
    Real.sq_sqrt (stampacchiaTruncationDeriv_nonneg s)]

/-- The truncation `G s = ∫₀^s √(min (max t 0) 1) dt` is a Stampacchia truncation with `M = 1`;
its derivative squared is `min (max s 0) 1`, the derivative of `stampacchiaTruncation`. -/
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
/-- The affine map `x ↦ T x + c` as a homeomorphism, with inverse `y ↦ T⁻¹ (y − c)`. -/
def ContinuousLinearEquiv.affineHomeomorph (T : E ≃L[ℝ] E) (c : E) : E ≃ₜ E where
  toFun x := T x + c
  invFun y := T.symm (y - c)
  left_inv x := by simp
  right_inv y := by simp
  continuous_toFun := T.continuous.add continuous_const
  continuous_invFun := T.symm.continuous.comp (continuous_id.sub continuous_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `T.affineHomeomorph c x = T x + c`. -/
@[simp]
theorem ContinuousLinearEquiv.affineHomeomorph_apply (T : E ≃L[ℝ] E) (c x : E) :
    T.affineHomeomorph c x = T x + c :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `(T.affineHomeomorph c).symm y = T⁻¹ (y − c)`. -/
@[simp]
theorem ContinuousLinearEquiv.affineHomeomorph_symm_apply (T : E ≃L[ℝ] E) (c y : E) :
    (T.affineHomeomorph c).symm y = T.symm (y - c) :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- The affine map `x ↦ T x + c` is a measurable embedding. -/
theorem measurableEmbedding_affine (T : E ≃L[ℝ] E) (c : E) :
    MeasurableEmbedding fun x : E ↦ T x + c :=
  (T.affineHomeomorph c).measurableEmbedding

/-- **The pushforward of an additive Haar measure under an affine map** `x ↦ T x + c` is
`|det T|⁻¹ μ`. -/
theorem map_affine_addHaar (T : E ≃L[ℝ] E) (c : E) :
    μ.map (fun x ↦ T x + c) = ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| • μ := by
  have hdet : LinearMap.det (T : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero
  have h : (fun x : E ↦ T x + c) = (fun y ↦ y + c) ∘ ⇑(T : E →ₗ[ℝ] E) := by
    funext x; simp
  rw [h, ← Measure.map_map (measurable_add_const c)
    (by simpa using T.continuous.measurable : Measurable ⇑(T : E →ₗ[ℝ] E)),
    Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet,
    Measure.map_smul _ (measurable_add_const c).aemeasurable, map_add_right_eq_self]

/-- **The affine change of variables in a set integral**: for `F x = T x + c`,
`∫_{F⁻¹ s} g ∘ F = |det T|⁻¹ ∫_s g`. -/
theorem setIntegral_comp_affine (T : E ≃L[ℝ] E) (c : E) {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (g : E → G) (s : Set E) :
    ∫ x in (fun x ↦ T x + c) ⁻¹' s, g (T x + c) ∂μ
      = (ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹|).toReal • ∫ y in s, g y ∂μ := by
  have hmp : MeasurePreserving (fun x ↦ T x + c) μ (μ.map fun x ↦ T x + c) :=
    ⟨(measurableEmbedding_affine T c).measurable, rfl⟩
  rw [hmp.setIntegral_preimage_emb (measurableEmbedding_affine T c), map_affine_addHaar,
    Measure.restrict_smul, integral_smul_measure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **An affine equivalence is a diffeomorphism with bounded Jacobians** between the preimage of
an open set and the set. -/
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

/-- **The affine change of variables at every order**: for `T : E ≃L[ℝ] E`, `c : E` and
`HasWeakIteratedFDerivOn n v w Ω μ`, the composite `x ↦ v (T x + c)` has, on the preimage
`{x | T x + c ∈ Ω}`, the weak derivative of order `n` given by `x ↦ w (T x + c) ∘ (T, …, T)`.
The test function `φ ∘ F⁻¹` is a test function on `Ω`,
`∂^n (ψ ∘ F) x z = ∂^n ψ (F x) (T z, …, T z)` (`ContinuousLinearMap.iteratedFDeriv_comp_right`,
`iteratedFDeriv_comp_add_right`), and the substitution `x ↦ F x` in the integrals
(`setIntegral_comp_affine`) carries the same factor `|det T|⁻¹` on both sides. This is the
affine, all-orders sibling of Proposition 9.6, the "backbone lemma" of the route to Atkinson–Han's
Theorem 10.3.4. -/
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
