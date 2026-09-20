/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts`, whose
`integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable` this file relaxes.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Integration by parts for a function differentiable off a finite union of segments

Mathlib's integration by parts for line derivatives,
`integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`, asks the function `f` to be
differentiable in the direction `v` at every point of the support of the test factor `g`. The
finite element method needs it for a function that is only *piecewise* differentiable: a
continuous function on a triangulated plane domain which is `C¹` on each open triangle, and
whose derivative may jump across the edges. This file proves that version: `f` is continuous on
the support of `g` and has the line derivative `f'` there **off a finite union of segments**
`⋃ i, segment ℝ (P i) (Q i)`, and then

  `∫ B (f x) (g' x) = -∫ B (f' x) (g x)`

still holds (`integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_off_segments`).
The point is that the fundamental theorem of calculus on a line survives countably many
exceptional points (`MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`), and that a
segment of a space of dimension at least `2` meets almost every line parallel to `v` in at most
one point. So the proof is Mathlib's: a linear change of coordinates `L : E ≃L[ℝ] E' × ℝ` with
`L v = (0, 1)`, Fubini on `E' × ℝ`, and on each line `t ↦ (x, t)` the one-dimensional
integration by parts `integral_bilinear_hasDerivAt_right_eq_neg_left_of_countable`, whose
exceptional set is countable for almost every `x` (`subsingleton_setOf_mem_segment`).

## Main statements

* `integral_bilinear_hasDerivAt_right_eq_neg_left_of_countable` — integration by parts on `ℝ`
  for a function continuous on the support of the (compactly supported) test factor and
  differentiable there off a countable set.
* `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_off_segments` — the
  version in a finite-dimensional space of dimension at least `2`, for an additive Haar measure,
  with an exceptional set contained in a finite union of segments.
* `integral_fderiv_smul_eq_neg_smul_fderiv_of_integrable_off_segments` — its form for a
  Fréchet-differentiable `f` and a `C¹` scalar test factor `g`,
  `∫ (∂_v g) • f = -∫ g • (∂_v f)`, which is the integration by parts formula defining a weak
  derivative.

## Implementation notes

The hypothesis `2 ≤ finrank ℝ E` is needed: on the line a segment is an interval, and a
function continuous on an interval and differentiable off it need not satisfy the fundamental
theorem of calculus there. The exceptional set is written as a union of segments indexed by a
finite type rather than as a set of a given shape, because that is what the transport along `L`
preserves (`image_segment`) and what a triangulation produces (its edges).
-/

open MeasureTheory Measure Module Set Filter Topology

variable {F G W : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-! ### The line -/

/-- **Integration by parts on `ℝ` for a function differentiable off a countable set**, against a
compactly supported factor: `∫ B u v' = -∫ B u' v` when `u` is continuous on the support of `v`
and differentiable there off a countable set `s`, `v` is differentiable on the support of `u`
and has compact support, and both products are integrable. The function `B (u x) (v x)` is then
continuous, differentiable off `s` with derivative `B (u x) (v' x) + B (u' x) (v x)`, and
vanishes outside a compact interval, so the fundamental theorem of calculus off a countable set
gives that the integral of the derivative is zero. -/
theorem integral_bilinear_hasDerivAt_right_eq_neg_left_of_countable [CompleteSpace W]
    {u u' : ℝ → F} {v v' : ℝ → G} {B : F →L[ℝ] G →L[ℝ] W} {s : Set ℝ} (hs : s.Countable)
    (huc : ∀ x ∈ tsupport v, ContinuousAt u x)
    (hu : ∀ x ∈ tsupport v, x ∉ s → HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x) (hvs : HasCompactSupport v)
    (huv' : Integrable (fun x ↦ B (u x) (v' x))) (hu'v : Integrable (fun x ↦ B (u' x) (v x))) :
    ∫ x, B (u x) (v' x) = -∫ x, B (u' x) (v x) := by
  -- the support of `v` lies in the ball of radius `R`; `T = |R| + 1` is safely outside
  obtain ⟨R, hR⟩ := hvs.isBounded.subset_closedBall 0
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = |R| + 1 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  have hout : ∀ x, T ≤ |x| → x ∉ tsupport v := fun x hx hmem ↦ by
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_abs_self R]
  set h : ℝ → W := fun x ↦ B (u x) (v x) with hh
  set h' : ℝ → W := fun x ↦ B (u x) (v' x) + B (u' x) (v x) with hh'
  -- `h` and `h'` vanish off the support of `v`
  have hzero : ∀ x, x ∉ tsupport v → h x = 0 := fun x hx ↦ by
    simp [hh, image_eq_zero_of_notMem_tsupport hx]
  have h'zero : ∀ x, x ∉ tsupport v → h' x = 0 := fun x hx ↦ by
    by_cases hxu : x ∈ tsupport u
    · have : v' x = 0 := (hv x hxu).unique (HasDerivAt.of_notMem_tsupport hx)
      simp [hh', this, image_eq_zero_of_notMem_tsupport hx]
    · simp [hh', image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxu]
  -- `h` is continuous
  have hcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport v
    · by_cases hxu : x ∈ tsupport u
      · exact B.continuous₂.continuousAt.comp ((huc x hx).prodMk (hv x hxu).continuousAt)
      · have hev : h =ᶠ[𝓝 x] 0 := by
          filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hxu] with y hy
          simp [hh, image_eq_zero_of_notMem_tsupport hy]
        exact continuousAt_const.congr hev.symm
    · have hev : h =ᶠ[𝓝 x] 0 := by
        filter_upwards [(isClosed_tsupport v).isOpen_compl.mem_nhds hx] with y hy
        exact hzero y hy
      exact continuousAt_const.congr hev.symm
  -- `h'` is the derivative of `h` off `s`
  have hderiv : ∀ x, x ∉ s → HasDerivAt h (h' x) x := fun x hx ↦
    B.hasDerivAt_of_bilinear (fun hxv ↦ hu x hxv hx) (hv x)
  have hint : Integrable h' := huv'.add hu'v
  -- the fundamental theorem of calculus on `[-T, T]`
  have hftc : ∫ x in (-T)..T, h' x = h T - h (-T) :=
    integral_eq_of_hasDerivAt_off_countable_of_le h h' (by linarith) hs hcont.continuousOn
      (fun x hx ↦ hderiv x hx.2) hint.intervalIntegrable
  have hR1 : ∫ x, h' x = ∫ x in (-T)..T, h' x := by
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    refine h'zero x (hout x ?_)
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact hx.le
  have hzT : h T = 0 := hzero T (hout T (by rw [abs_of_pos hT0]))
  have hzT' : h (-T) = 0 := hzero (-T) (hout (-T) (by rw [abs_neg, abs_of_pos hT0]))
  have key : ∫ x, h' x = 0 := by rw [hR1, hftc, hzT, hzT', sub_zero]
  rw [hh', integral_add huv' hu'v] at key
  exact eq_neg_of_add_eq_zero_left key

/-! ### The product `E × ℝ` -/

section Prod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

omit [NormedSpace ℝ G] [NormedSpace ℝ E] [MeasurableSpace E] in
/-- Slicing a compactly supported function on `E × ℝ` at a point `x` of `E` gives a compactly
supported function on `ℝ`: `t ↦ (x, t)` is an isometry, hence a closed embedding. -/
theorem HasCompactSupport.comp_prodMk {g : E × ℝ → G} (hg : HasCompactSupport g) (x : E) :
    HasCompactSupport fun t ↦ g (x, t) :=
  hg.comp_isClosedEmbedding (Isometry.isClosedEmbedding fun t t' ↦ by
    simp [edist_dist, Prod.dist_eq])

omit [NormedSpace ℝ G] [MeasurableSpace E] in
/-- **A line meets a segment in at most one point**, unless the segment lies on the line: the
points `t` with `(x, t)` on the segment from `p` to `q` form a subsingleton when `x ≠ p.1`. If
`p.1 = q.1` the segment lies on the line `{(p.1, t)}` and misses `{(x, t)}`; otherwise the first
coordinate is injective along the segment. -/
theorem subsingleton_setOf_mem_segment {p q : E × ℝ} {x : E} (hp : x ≠ p.1) :
    {t : ℝ | (x, t) ∈ segment ℝ p q}.Subsingleton := by
  intro t ht t' ht'
  rw [Set.mem_ofPred_eq, segment_eq_image] at ht ht'
  obtain ⟨s, -, hs⟩ := ht
  obtain ⟨s', -, hs'⟩ := ht'
  have h1 := congrArg Prod.fst hs
  have h1' := congrArg Prod.fst hs'
  have h2 := congrArg Prod.snd hs
  have h2' := congrArg Prod.snd hs'
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at h1 h1' h2 h2'
  have hpq : p.1 ≠ q.1 := fun h ↦ hp (by rw [← h1, ← h, ← add_smul, sub_add_cancel, one_smul])
  have hss : s = s' := by
    have : (s - s') • (q.1 - p.1) = 0 := by
      rw [smul_sub, sub_smul, sub_smul]
      calc s • q.1 - s' • q.1 - (s • p.1 - s' • p.1)
          = ((1 - s) • p.1 + s • q.1) - ((1 - s') • p.1 + s' • q.1) := by module
        _ = 0 := by rw [h1, h1', sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd (sub_eq_zero.1 h).symm hpq
  rw [← h2, ← h2', hss]

/-- Integration by parts on `E × ℝ` in the direction `(0, 1)`, for a product measure, with an
exceptional set `S` that almost every line `t ↦ (x, t)` meets in a countable set: Fubini and the
one-dimensional statement on each line. -/
theorem integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_off_aux₁
    {μ : Measure E} [SigmaFinite μ] [CompleteSpace W]
    {f f' : E × ℝ → F} {g g' : E × ℝ → G} {B : F →L[ℝ] G →L[ℝ] W} {S : Set (E × ℝ)}
    (hS : ∀ᵐ x ∂μ, {t | (x, t) ∈ S}.Countable)
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) (μ.prod volume))
    (hfg' : Integrable (fun x ↦ B (f x) (g' x)) (μ.prod volume))
    (hfc : ∀ x ∈ tsupport g, ContinuousAt f x)
    (hf : ∀ x ∈ tsupport g, x ∉ S → HasLineDerivAt ℝ f (f' x) x (0, 1))
    (hg : ∀ x ∈ tsupport f, HasLineDerivAt ℝ g (g' x) x (0, 1)) (hgs : HasCompactSupport g) :
    ∫ x, B (f x) (g' x) ∂(μ.prod volume) = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := calc
  ∫ x, B (f x) (g' x) ∂(μ.prod volume)
    = ∫ x, (∫ t, B (f (x, t)) (g' (x, t))) ∂μ := integral_prod _ hfg'
  _ = ∫ x, (- ∫ t, B (f' (x, t)) (g (x, t))) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf'g.prod_right_ae, hfg'.prod_right_ae, hS] with x hf'gx hfg'x hSx
    apply integral_bilinear_hasDerivAt_right_eq_neg_left_of_countable hSx ?_ ?_ ?_
      (hgs.comp_prodMk x) hfg'x hf'gx
    · intro t ht
      have : (x, t) ∈ tsupport g :=
        tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) g (by fun_prop) ht
      exact (hfc _ this).comp (by fun_prop)
    · intro t ht hts
      have : (x, t) ∈ tsupport g :=
        tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) g (by fun_prop) ht
      convert! (hf (x, t) this hts).scomp_of_eq t
        ((hasDerivAt_id t).add (hasDerivAt_const t (-t))) (by simp) <;> simp
    · intro t ht
      have : (x, t) ∈ tsupport f :=
        tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) f (by fun_prop) ht
      convert! (hg (x, t) this).scomp_of_eq t
        ((hasDerivAt_id t).add (hasDerivAt_const t (-t))) (by simp) <;> simp
  _ = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := by rw [integral_neg, integral_prod _ hf'g]

variable [BorelSpace E] [FiniteDimensional ℝ E]

/-- Integration by parts on `E × ℝ` in the direction `(0, 1)`, for an additive Haar measure:
it is a multiple of the product of a Haar measure on `E` with Lebesgue measure. -/
theorem integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_off_aux₂
    [CompleteSpace W] {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]
    {f f' : E × ℝ → F} {g g' : E × ℝ → G} {B : F →L[ℝ] G →L[ℝ] W} {S : Set (E × ℝ)}
    (hS : ∀ᵐ x ∂(addHaar : Measure E), {t | (x, t) ∈ S}.Countable)
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) μ)
    (hfg' : Integrable (fun x ↦ B (f x) (g' x)) μ)
    (hfc : ∀ x ∈ tsupport g, ContinuousAt f x)
    (hf : ∀ x ∈ tsupport g, x ∉ S → HasLineDerivAt ℝ f (f' x) x (0, 1))
    (hg : ∀ x ∈ tsupport f, HasLineDerivAt ℝ g (g' x) x (0, 1)) (hgs : HasCompactSupport g) :
    ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ := by
  let ν : Measure E := addHaar
  have A : ν.prod volume = (addHaarScalarFactor (ν.prod volume) μ) • μ :=
    isAddLeftInvariant_eq_smul _ _
  have Hf'g : Integrable (fun x ↦ B (f' x) (g x)) (ν.prod volume) := by
    rw [A]; exact hf'g.smul_measure_nnreal
  have Hfg' : Integrable (fun x ↦ B (f x) (g' x)) (ν.prod volume) := by
    rw [A]; exact hfg'.smul_measure_nnreal
  rw [isAddLeftInvariant_eq_smul μ (ν.prod volume), integral_smul_nnreal_measure,
    integral_smul_nnreal_measure,
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_off_aux₁ hS Hf'g Hfg' hfc
      hf hg hgs, smul_neg]

end Prod

/-! ### The general statement -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Integration by parts for line derivatives, off a finite union of segments.** In a space
of dimension at least `2` with an additive Haar measure, if `f` is continuous on the support of
`g` and has the line derivative `f'` in the direction `v ≠ 0` there, except on a finite union
of segments, and `g` has the line derivative `g'` on the support of `f` and compact support,
then, both products being integrable,

  `∫ B (f x) (g' x) = -∫ B (f' x) (g x)`.

This is Mathlib's `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable` with the
exceptional set, and its proof: a linear change of coordinates `L : E ≃L[ℝ] E' × ℝ` sending `v`
to `(0, 1)`, then Fubini. Almost every line `t ↦ L⁻¹ (x, t)` meets each segment in at most one
point (`subsingleton_setOf_mem_segment`, the exceptional `x` being the first coordinates of the
images of the segments' endpoints, finitely many points of `E'`, a null set since `E'` is
nontrivial), so the one-dimensional integration by parts off a countable set applies on it. -/
theorem integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_off_segments
    [CompleteSpace W] (h2 : 2 ≤ finrank ℝ E) {f f' : E → F} {g g' : E → G} {v : E} (hv : v ≠ 0)
    {B : F →L[ℝ] G →L[ℝ] W} {ι : Type*} [Finite ι] {P Q : ι → E}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) μ) (hfg' : Integrable (fun x ↦ B (f x) (g' x)) μ)
    (hfc : ∀ x ∈ tsupport g, ContinuousAt f x)
    (hf : ∀ x ∈ tsupport g, x ∉ ⋃ i, segment ℝ (P i) (Q i) → HasLineDerivAt ℝ f (f' x) x v)
    (hg : ∀ x ∈ tsupport f, HasLineDerivAt ℝ g (g' x) x v) (hgs : HasCompactSupport g) :
    ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ := by
  have : Nontrivial E := nontrivial_iff.2 ⟨v, 0, hv⟩
  let n := finrank ℝ E
  let E' := Fin (n - 1) → ℝ
  have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨L, hL⟩ : ∃ L : E ≃L[ℝ] (E' × ℝ), L v = (0, 1) := by
    have : finrank ℝ (E' × ℝ) = n := by simpa [this, E'] using Nat.sub_add_cancel finrank_pos
    have L₀ : E ≃L[ℝ] (E' × ℝ) := (ContinuousLinearEquiv.ofFinrankEq this).symm
    obtain ⟨M, hM⟩ : ∃ M : (E' × ℝ) ≃L[ℝ] (E' × ℝ), M (L₀ v) = (0, 1) := by
      apply SeparatingDual.exists_continuousLinearEquiv_apply_eq
      · simpa using hv
      · simp
    exact ⟨L₀.trans M, by simp [hM]⟩
  let ν := Measure.map L μ
  suffices H : ∫ (x : E' × ℝ), (B (f (L.symm x))) (g' (L.symm x)) ∂ν =
      -∫ (x : E' × ℝ), (B (f' (L.symm x))) (g (L.symm x)) ∂ν by
    have : μ = Measure.map L.symm ν := by
      simp [ν, Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    have hL : IsClosedEmbedding L.symm := L.symm.toHomeomorph.isClosedEmbedding
    simpa [this, hL.integral_map] using H
  have L_emb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  -- the exceptional set, transported: a finite union of segments of `E' × ℝ`
  have hseg : ∀ i, L.symm ⁻¹' segment ℝ (P i) (Q i) = segment ℝ (L (P i)) (L (Q i)) := fun i ↦ by
    have : (L : E → E' × ℝ) '' segment ℝ (P i) (Q i) = segment ℝ (L (P i)) (L (Q i)) :=
      image_segment ℝ (L : E →ₗ[ℝ] E' × ℝ).toAffineMap (P i) (Q i)
    rw [← this]
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hy
      exact ⟨L.symm y, hy, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
  have hbad : ∀ᵐ x ∂(addHaar : Measure E'),
      {t | (x, t) ∈ L.symm ⁻¹' ⋃ i, segment ℝ (P i) (Q i)}.Countable := by
    have hfin : (Set.range fun i ↦ (L (P i)).1).Finite := Set.finite_range _
    have hnull : (addHaar : Measure E') (Set.range fun i ↦ (L (P i)).1) = 0 :=
      hfin.measure_zero _
    rw [ae_iff]
    refine measure_mono_null (fun x hx ↦ ?_) hnull
    simp only [Set.mem_ofPred_eq] at hx
    by_contra hx'
    apply hx
    rw [Set.preimage_iUnion]
    have : {t | (x, t) ∈ ⋃ i, L.symm ⁻¹' segment ℝ (P i) (Q i)}
        = ⋃ i, {t | (x, t) ∈ segment ℝ (L (P i)) (L (Q i))} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hseg]
    rw [this]
    refine Set.countable_iUnion fun i ↦ (subsingleton_setOf_mem_segment ?_).countable
    exact fun h ↦ hx' ⟨i, h.symm⟩
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_off_aux₂ hbad
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hf'g
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg'
  · intro x hx
    have h2x : L.symm x ∈ tsupport g :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage g L.symm.toHomeomorph) x).mp hx
    exact (hfc _ h2x).comp L.symm.continuous.continuousAt
  · intro x hx hxS
    have : f = (f ∘ L.symm) ∘ (L : E →ₗ[ℝ] (E' × ℝ)) := by ext y; simp
    have h2x : L.symm x ∈ tsupport g :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage g L.symm.toHomeomorph) x).mp hx
    specialize hf (L.symm x) h2x hxS
    rw [this] at hf
    convert! hf.of_comp using 1
    · simp
    · simp [← hL]
  · intro x hx
    have : g = (g ∘ L.symm) ∘ (L : E →ₗ[ℝ] (E' × ℝ)) := by ext y; simp
    have h2x : L.symm x ∈ tsupport f :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage f L.symm.toHomeomorph) x).mp hx
    specialize hg (L.symm x) h2x
    rw [this] at hg
    convert! hg.of_comp using 1
    · simp
    · simp [← hL]
  · exact hgs.comp_homeomorph L.symm.toHomeomorph

/-- **Integration by parts against a `C¹` scalar factor, off a finite union of segments**:
`∫ (∂_v g) • f = -∫ g • (∂_v f)` in a space of dimension at least `2`, when `f` is continuous
on the support of `g` and Fréchet differentiable there off a finite union of segments, with
derivative `f'`, `g` is `C¹` with compact support, and both products are integrable. This is
the integration by parts formula that defines a first-order weak derivative, for a function
that is only piecewise differentiable. The direction `v = 0` is trivial (both sides vanish). -/
theorem integral_fderiv_smul_eq_neg_smul_fderiv_of_integrable_off_segments [CompleteSpace F]
    (h2 : 2 ≤ finrank ℝ E) {f : E → F} {f' : E → E →L[ℝ] F} {g : E → ℝ} (v : E)
    {ι : Type*} [Finite ι] {P Q : ι → E}
    (hf'g : Integrable (fun x ↦ g x • f' x v) μ)
    (hfg' : Integrable (fun x ↦ fderiv ℝ g x v • f x) μ)
    (hfc : ∀ x ∈ tsupport g, ContinuousAt f x)
    (hf : ∀ x ∈ tsupport g, x ∉ ⋃ i, segment ℝ (P i) (Q i) → HasFDerivAt f (f' x) x)
    (hg : ContDiff ℝ 1 g) (hgs : HasCompactSupport g) :
    ∫ x, fderiv ℝ g x v • f x ∂μ = -∫ x, g x • f' x v ∂μ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_off_segments h2 hv
    (B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip) (f := f)
    (f' := fun x ↦ f' x v) (g := g) (g' := fun x ↦ fderiv ℝ g x v) (P := P) (Q := Q)
    (by simpa using hf'g) (by simpa using hfg') hfc
    (fun x hx hxS ↦ (hf x hx hxS).hasLineDerivAt v)
    (fun x _ ↦ ((hg.differentiable one_ne_zero) x).hasFDerivAt.hasLineDerivAt v) hgs
  simpa using key

end Main
