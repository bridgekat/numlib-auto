/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Calculus.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Calculus

/-!
# The affine change of variables in `L^p` and in `W^{m,p}`

For an affine bijection `F x = T x + c` of a finite-dimensional real normed space `E`, with
`T : E ≃L[ℝ] E`, and an additive Haar measure `μ`, this file transports `L^p` norms, `L^p`
membership, `W^{m,p}` membership and the top-order Sobolev seminorm along `F`, from an open set
`Ω` to its preimage `F⁻¹(Ω)`. It is the general content of Atkinson and Han, *Theoretical
Numerical Analysis: A Functional Analysis Framework*, 3rd edition, Theorem 10.3.4
(`[han2009theoretical]`), whose "reference element technique" rests on the two estimates

* (10.3.5) `|v ∘ F|_{m,p,F⁻¹Ω} ≤ ‖T‖^m |det T|^{-1/p} |v|_{m,p,Ω}`, and
* (10.3.6) `|v|_{m,p,Ω} ≤ ‖T⁻¹‖^m |det T|^{1/p} |v ∘ F|_{m,p,F⁻¹Ω}`,

the second being the first for `F⁻¹`. The seminorm here is the tensor seminorm `sobolevSeminorm`
of `Numlib/Analysis/Sobolev/Domain.lean`, the `L^p(Ω)` norm of the operator norm of the weak
derivative tensor of order `m`; for it the constants are exactly the ones displayed, with no
dimensional factor, because `∂^m (v ∘ F)(x) = ∂^m v (F x) ∘ (T, …, T)` has operator norm at most
`‖T‖^m ‖∂^m v (F x)‖` (`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`).

## Main definitions

* `affinePreimage T c Ω`: the open set `F⁻¹(Ω)`, as an element of `Opens E`.

## Main results

* `eLpNorm_comp_affine`: `‖f ∘ F‖_{L^p(F⁻¹A)} = |det T|^{-1/p} ‖f‖_{L^p(A)}` for every `p` and
  every measurable `A`, from the pushforward formula `map_affine_addHaar`; no measurability of `f`
  is needed (`MeasurableEmbedding.eLpNorm_map_measure`).
* `memLp_comp_affine`, `memSobolev_comp_affine`, `memSobolev_comp_affine_iff`: membership of
  `L^p` and of `W^{m,p}` transports along `F`, at every order `m : ℕ∞` and every exponent, the
  weak derivatives being `x ↦ ∂^n v (F x) ∘ (T, …, T)` (`HasWeakIteratedFDerivOn.comp_affineEquiv`).
* `sobolevSeminorm_comp_affine_le`: the estimate (10.3.5) for the tensor seminorm and every `p`.
* `ContinuousLinearEquiv.det_symm_eq_inv`: `det T⁻¹ = (det T)⁻¹`.
* `closure_affinePreimage`, `ContinuousOn.comp_affine_closure`: the closure of `F⁻¹(Ω)` is
  `F⁻¹(closure Ω)`, so a function continuous on `closure Ω` composes to one continuous on
  `closure (F⁻¹ Ω)` — the transport of the "continuous up to the boundary" hypothesis of the
  finite element interpolation estimates.

## References

`[han2009theoretical]` Theorem 10.3.4; the affine identity for the weak derivative is
`HasWeakIteratedFDerivOn.comp_affineEquiv` of `Numlib/Analysis/Sobolev/Calculus.lean`.
-/

open Filter MeasureTheory Set TopologicalSpace

open scoped ENNReal

noncomputable section

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {G : Type*} [NormedAddCommGroup G]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The open set `F⁻¹(Ω)` for the affine map `F x = T x + c`, as an open set. -/
abbrev affinePreimage (T : E ≃L[ℝ] E) (c : E) (Ω : Opens E) : Opens E :=
  ⟨(fun x ↦ T x + c) ⁻¹' Ω, Ω.isOpen.preimage (T.continuous.add continuous_const)⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Membership of the preimage, unfolded. -/
@[simp]
theorem mem_affinePreimage {T : E ≃L[ℝ] E} {c : E} {Ω : Opens E} {x : E} :
    x ∈ affinePreimage T c Ω ↔ T x + c ∈ Ω :=
  Iff.rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The inverse of the affine map `x ↦ T x + c` is `y ↦ T⁻¹ y + (-T⁻¹ c)`, and the preimage of
the preimage is the set itself. -/
theorem affinePreimage_symm (T : E ≃L[ℝ] E) (c : E) (Ω : Opens E) :
    affinePreimage T.symm (-T.symm c) (affinePreimage T c Ω) = Ω := by
  ext y
  simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The preimage of the image: if `F '' Ω̂ = Ω` for the affine bijection `F x = T x + c`, then
`Ω̂ = F⁻¹(Ω)`. -/
theorem affinePreimage_eq_of_image_eq (T : E ≃L[ℝ] E) (c : E) {Ωhat Ω : Opens E}
    (h : (fun x ↦ T x + c) '' Ωhat = Ω) : affinePreimage T c Ω = Ωhat := by
  ext x
  change T x + c ∈ (Ω : Set E) ↔ x ∈ (Ωhat : Set E)
  rw [← h]
  exact ⟨fun ⟨y, hy, hxy⟩ ↦ by rwa [← T.injective (add_right_cancel hxy)],
    fun hx ↦ ⟨x, hx, rfl⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The closure of `F⁻¹(Ω)` is `F⁻¹(closure Ω)`, `F` being a homeomorphism. -/
theorem closure_affinePreimage (T : E ≃L[ℝ] E) (c : E) (Ω : Opens E) :
    closure (affinePreimage T c Ω : Set E) = (fun x ↦ T x + c) ⁻¹' closure (Ω : Set E) :=
  ((T.affineHomeomorph c).preimage_closure Ω).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A function continuous on `closure Ω` composes with the affine map `F x = T x + c` to a
function continuous on `closure (F⁻¹ Ω)`. -/
theorem ContinuousOn.comp_affine_closure {v : E → G} {Ω : Opens E}
    (hv : ContinuousOn v (closure (Ω : Set E))) (T : E ≃L[ℝ] E) (c : E) :
    ContinuousOn (fun x ↦ v (T x + c)) (closure (affinePreimage T c Ω : Set E)) := by
  rw [closure_affinePreimage]
  exact hv.comp (T.continuous.add continuous_const).continuousOn (mapsTo_preimage _ _)

/-- **The affine change of variables in an `L^p` norm**: for `F x = T x + c`,
`‖f ∘ F‖_{L^p(F⁻¹ A)} = |det T|^{-1/p} ‖f‖_{L^p(A)}`, for every `p`, by the pushforward formula
`map_affine_addHaar`. -/
theorem eLpNorm_comp_affine (T : E ≃L[ℝ] E) (c : E) {A : Set E} (hA : MeasurableSet A)
    (f : E → G) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ f (T x + c)) p (μ.restrict ((fun x ↦ T x + c) ⁻¹' A))
      = ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal
        * eLpNorm f p (μ.restrict A) := by
  have hmeas : Measurable fun x ↦ T x + c := (measurableEmbedding_affine T c).measurable
  have h1 : (μ.restrict ((fun x ↦ T x + c) ⁻¹' A)).map (fun x ↦ T x + c)
      = ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| • μ.restrict A := by
    rw [← Measure.restrict_map hmeas hA, map_affine_addHaar, Measure.restrict_smul]
  rw [← smul_eq_mul, ← eLpNorm_smul_measure_of_ne_zero
    (by simp [(LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero]), ← h1,
    (measurableEmbedding_affine T c).eLpNorm_map_measure]
  rfl

/-- `L^p` membership transports along an affine map, onto the preimage. -/
theorem memLp_comp_affine (T : E ≃L[ℝ] E) (c : E) {A : Set E} (hA : MeasurableSet A)
    {f : E → G} {p : ℝ≥0∞} (hf : MemLp f p (μ.restrict A)) :
    MemLp (fun x ↦ f (T x + c)) p (μ.restrict ((fun x ↦ T x + c) ⁻¹' A)) := by
  rw [memLp_iff, eLpNorm_comp_affine T c hA]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    hf

/-- **Membership of `W^{m,p}` transports along an affine map** (the all-orders affine form of
`MemSobolev.comp_diffeoOn`): `v ∈ W^{m,p}(Ω)` gives `v ∘ F ∈ W^{m,p}(F⁻¹ Ω)` for `F x = T x + c`,
the weak derivatives being `x ↦ ∂^n v (F x) ∘ (T, …, T)`
(`HasWeakIteratedFDerivOn.comp_affineEquiv`). -/
theorem memSobolev_comp_affine [NormedSpace ℝ G] (T : E ≃L[ℝ] E) (c : E) {Ω : Opens E}
    {v : E → G} {m : ℕ∞} {p : ℝ≥0∞} (h : MemSobolev v m p Ω μ) :
    MemSobolev (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ := by
  refine ⟨memLp_comp_affine T c Ω.isOpen.measurableSet h.1, fun n hn ↦ ?_⟩
  obtain ⟨w, hw, hwp⟩ := h.2 n hn
  refine ⟨_, hw.comp_affineEquiv T c, ?_⟩
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    fun _ : Fin n ↦ (T : E →L[ℝ] E)).comp_memLp' (memLp_comp_affine T c Ω.isOpen.measurableSet hwp)

/-- **Membership of `W^{m,p}` is equivalent along an affine map.** -/
theorem memSobolev_comp_affine_iff [NormedSpace ℝ G] (T : E ≃L[ℝ] E) (c : E) {Ω : Opens E}
    {v : E → G} {m : ℕ∞} {p : ℝ≥0∞} :
    MemSobolev v m p Ω μ ↔ MemSobolev (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ := by
  refine ⟨memSobolev_comp_affine T c, fun h ↦ ?_⟩
  have := memSobolev_comp_affine T.symm (-T.symm c) h
  rw [affinePreimage_symm] at this
  simpa using this

/-- **The seminorm bound of the affine change of variables**, (10.3.5) of
`[han2009theoretical]` Theorem 10.3.4 for the tensor seminorm and every `p`:
`|v ∘ F|_{m,p,F⁻¹ Ω} ≤ ‖T‖^m |det T|^{-1/p} |v|_{m,p,Ω}`, since
`∂^m (v ∘ F) x = ∂^m v (F x) ∘ (T, …, T)` has norm at most `‖T‖^m ‖∂^m v (F x)‖`
(`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`) and the `L^p` norm transports with
the factor `|det T|^{-1/p}` (`eLpNorm_comp_affine`). -/
theorem sobolevSeminorm_comp_affine_le [NormedSpace ℝ G] [CompleteSpace G] (T : E ≃L[ℝ] E) (c : E)
    {Ω : Opens E} {v : E → G} {m : ℕ} {p : ℝ≥0∞} (h : MemSobolev v m p Ω μ) :
    sobolevSeminorm (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ
      ≤ ENNReal.ofReal (‖(T : E →L[ℝ] E)‖ ^ m)
        * (ENNReal.ofReal |(LinearMap.det (T : E →ₗ[ℝ] E))⁻¹| ^ (1 / p).toReal
          * sobolevSeminorm v m p Ω μ) := by
  obtain ⟨w, hw, hwp⟩ := h.2 m le_rfl
  have hw' := hw.comp_affineEquiv T c
  -- the chosen weak derivatives are `w` and its transport, almost everywhere
  have e1 : sobolevSeminorm v m p Ω μ = eLpNorm w p (μ.restrict Ω) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_)
    exact hw.weakIteratedFDeriv_ae_eq
  have e2 : sobolevSeminorm (fun x ↦ v (T x + c)) m p (affinePreimage T c Ω) μ
      = eLpNorm (fun x ↦ (w (T x + c)).compContinuousLinearMap fun _ ↦ (T : E →L[ℝ] E)) p
        (μ.restrict ((fun x ↦ T x + c) ⁻¹' Ω)) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' (affinePreimage T c Ω).isOpen.measurableSet).2 ?_)
    exact hw'.weakIteratedFDeriv_ae_eq
  rw [e1, e2, ← eLpNorm_comp_affine T c Ω.isOpen.measurableSet,
    ← Real.enorm_eq_ofReal (by positivity), ← eLpNorm_const_smul]
  refine eLpNorm_mono_ae ?_ (Eventually.of_forall fun x ↦ ?_)
  · exact ((ContinuousMultilinearMap.compContinuousLinearMapL fun _ : Fin m ↦
      (T : E →L[ℝ] E)).comp_memLp' (memLp_comp_affine T c Ω.isOpen.measurableSet hwp))
      |>.aestronglyMeasurable
  · simp only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) m)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The determinant of the inverse of a continuous linear equivalence is the inverse of its
determinant. -/
theorem ContinuousLinearEquiv.det_symm_eq_inv (T : E ≃L[ℝ] E) :
    LinearMap.det (T.symm : E →ₗ[ℝ] E) = (LinearMap.det (T : E →ₗ[ℝ] E))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← LinearMap.det_comp]
  have : (T.symm : E →ₗ[ℝ] E).comp (T : E →ₗ[ℝ] E) = LinearMap.id :=
    LinearMap.ext fun x ↦ T.symm_apply_apply x
  rw [this, LinearMap.det_id]

end Affine

end
