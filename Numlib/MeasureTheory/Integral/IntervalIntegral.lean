/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` and
`Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`, with the `Lp` lemmas beside
`Mathlib.MeasureTheory.Function.LpSpace.Basic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

/-!
# Interval integrals over `(a, b)`: glue

Small facts about functions on a compact interval `[a, b]` and their integrals over the open
interval `(a, b)`, none of which is about any particular numerical method:

* the endpoints do not matter: integrability on `(a, b)` gives integrability on `[a, b]` and
  interval integrability between any two points of it
  (`MeasureTheory.IntegrableOn.integrableOn_Icc_of_Ioo`,
  `MeasureTheory.IntegrableOn.intervalIntegrable_of_Ioo`), two functions agreeing on `(a, b)`, or
  almost everywhere on it, have the same interval integrals (`intervalIntegral.integral_congr_Ioo`,
  `intervalIntegral.integral_congr_ae_Ioo_of_mem`), and `∫_a^b F = ∫_{(a, b)} F`
  (`intervalIntegral.integral_eq_setIntegral_Ioo`);
* a function continuous on `[a, b]` is essentially bounded and square integrable on `(a, b)`
  (`ContinuousOn.memLp_top_restrict_Ioo`, `ContinuousOn.memLp_two_restrict_Ioo`), integrable
  against an `L²` function (`MeasureTheory.integrableOn_continuousOn_mul`), and determined on
  `[a, b]` by its class in `L²(a, b)` (`eqOn_Icc_of_ae_eq`); two norm bounds for `L²(a, b)`
  (`MeasureTheory.Lp.norm_le_sqrt_mul_of_ae_bound`, `MeasureTheory.Lp.norm_le_of_abs_le`);
* the primitive `x ↦ ∫_a^x w` of a function integrable on `(a, b)` is continuous on `[a, b]`
  (`intervalIntegral.continuousOn_integral_of_integrableOn_Ioo`) and, for `w` continuous, has right
  derivative `w` on `[a, b)` (`intervalIntegral.hasDerivWithinAt_integral_Ici`,
  `intervalIntegral.continuousOn_integral_Icc`);
* the **weighted mean value theorem** `∫_a^b K f = f(ξ) ∫_a^b K` for `K ≥ 0` and `f` continuous,
  with `ξ ∈ [a, b]` (`intervalIntegral.exists_integral_mul_eq_mul_integral`) and, when `∫ K > 0`,
  with `ξ` in the *open* interval (`intervalIntegral.exists_mem_Ioo_integral_mul_eq_mul_integral`),
  which is what the Peano-kernel error formulas of quadrature rules need, together with the
  positivity of the integral of a continuous nonnegative function positive somewhere inside
  (`intervalIntegral.integral_pos_of_continuousOn_of_nonneg`);
* an interval-integrable nonnegative weight is within any `L¹` distance of a continuous
  nonnegative function (`intervalIntegral.exists_continuous_nonneg_integral_abs_sub_le`), which is
  how an integral-form Gronwall lemma with an integrable weight follows from the continuous one.
-/

open Filter MeasureTheory Set Topology intervalIntegral
open scoped Interval

/-! ### Integrability on `(a, b)` and on `[a, b]` -/

section Integrability

variable {a b : ℝ} {w : ℝ → ℝ}

/-- A function integrable on `(a, b)` is integrable on `[a, b]`. -/
theorem MeasureTheory.IntegrableOn.integrableOn_Icc_of_Ioo (hw : IntegrableOn w (Ioo a b)) :
    IntegrableOn w (Icc a b) :=
  (integrableOn_Icc_iff_integrableOn_Ioo (f := w) (μ := volume) (a := a) (b := b) enorm_ne_top
    enorm_ne_top).2 hw

/-- A function integrable on `(a, b)` is interval integrable between any two points of
`[a, b]`. -/
theorem MeasureTheory.IntegrableOn.intervalIntegrable_of_Ioo (hw : IntegrableOn w (Ioo a b))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : IntervalIntegrable w volume x y :=
  (hw.integrableOn_Icc_of_Ioo.mono_set (uIcc_subset_Icc hx hy)).intervalIntegrable

/-- The antiderivative of a function integrable on `(a, b)` is continuous on `[a, b]`. -/
theorem intervalIntegral.continuousOn_integral_of_integrableOn_Ioo (hab : a ≤ b)
    (hw : IntegrableOn w (Ioo a b)) (c : ℝ) :
    ContinuousOn (fun x ↦ c + ∫ t in a..x, w t) (Icc a b) :=
  continuousOn_const.add (by
    simpa [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval
      (μ := volume) (f := w) (a := a) (b := b)
      (by simpa [uIcc_of_le hab] using hw.integrableOn_Icc_of_Ioo))

end Integrability

/-! ### The endpoints do not matter -/

namespace intervalIntegral

variable {a b : ℝ}

/-- Two functions agreeing on the open interval have the same interval integral. -/
theorem integral_congr_Ioo {g h : ℝ → ℝ} (hab : a ≤ b) (hgh : ∀ t ∈ Ioo a b, g t = h t) :
    ∫ t in a..b, g t = ∫ t in a..b, h t := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => hgh t ht

/-- Interval integrals between two points of `[a, b]` only see the integrand almost everywhere on
`(a, b)`. -/
theorem integral_congr_ae_Ioo_of_mem {f g : ℝ → ℝ}
    (h : f =ᵐ[volume.restrict (Ioo a b)] g) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∫ r in s..t, f r = ∫ r in s..t, g r := by
  refine intervalIntegral.integral_congr_ae ?_
  have ha : ∀ᵐ r : ℝ, r ≠ a := by simp [ae_iff, measure_singleton]
  have hb : ∀ᵐ r : ℝ, r ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 h, ha, hb] with r hr hra hrb hrI
  have hr' : r ∈ Icc a b := uIcc_subset_Icc hs ht (uIoc_subset_uIcc hrI)
  exact hr ⟨lt_of_le_of_ne hr'.1 (Ne.symm hra), lt_of_le_of_ne hr'.2 hrb⟩

/-- `∫_a^b F = ∫_{(a, b)} F`. -/
theorem integral_eq_setIntegral_Ioo (hab : a ≤ b) (F : ℝ → ℝ) :
    ∫ x in a..b, F x = ∫ x in Ioo a b, F x := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

end intervalIntegral

/-! ### Continuous functions on `[a, b]` in `Lp(a, b)` -/

section Lp

variable {a b : ℝ}

/-- Two functions continuous on `[a, b]` and almost everywhere equal on `(a, b)` agree on all of
`[a, b]`. -/
theorem eqOn_Icc_of_ae_eq (hab : a < b) {g₁ g₂ : ℝ → ℝ} (h₁ : ContinuousOn g₁ (Icc a b))
    (h₂ : ContinuousOn g₂ (Icc a b)) (h : g₁ =ᵐ[volume.restrict (Ioo a b)] g₂) :
    EqOn g₁ g₂ (Icc a b) :=
  Measure.eqOn_of_ae_eq (by rwa [← restrict_Ioo_eq_restrict_Icc (μ := volume)]) h₁ h₂
    (by rw [interior_Icc, closure_Ioo hab.ne])

/-- A function continuous on `[a, b]` is essentially bounded on `(a, b)`. -/
theorem ContinuousOn.memLp_top_restrict_Ioo {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) :
    MemLp g ⊤ (volume.restrict (Ioo a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact memLp_top_of_bound ((hg.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    C ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦
      hC x (Ioo_subset_Icc_self hx)))

/-- A function continuous on `[a, b]` lies in `L²(a, b)`. -/
theorem ContinuousOn.memLp_two_restrict_Ioo {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b)) :
    MemLp g 2 (volume.restrict (Ioo a b)) :=
  hg.memLp_top_restrict_Ioo.mono_exponent le_top

/-- A function continuous on `[a, b]` is `L²(a, b)`-integrable against an `L²` function. -/
theorem MeasureTheory.integrableOn_continuousOn_mul {g : ℝ → ℝ} (hg : ContinuousOn g (Icc a b))
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    IntegrableOn (fun x ↦ g x * f x) (Ioo a b) :=
  IntegrableOn.continuousOn_mul_of_subset hg ((Lp.memLp f).integrable one_le_two) isCompact_Icc
    measurableSet_Ioo Ioo_subset_Icc_self

/-- `‖f‖² = ∫_a^b |f|²` in `L²(a, b)`. -/
theorem norm_sq_eq_integral_sq (f : Lp ℝ 2 (volume.restrict (Ioo a b))) :
    ‖f‖ ^ 2 = ∫ x in Ioo a b, |f x| ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs]

/-- An `L²(a, b)` function bounded by `C` has norm at most `√(b - a) C`. -/
theorem MeasureTheory.Lp.norm_le_sqrt_mul_of_ae_bound (hab : a ≤ b)
    (f : Lp ℝ 2 (volume.restrict (Ioo a b))) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂(volume.restrict (Ioo a b)), |f x| ≤ C) : ‖f‖ ≤ Real.sqrt (b - a) * C := by
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, norm_sq_eq_integral_sq,
    mul_pow, Real.sq_sqrt (sub_nonneg.2 hab)]
  calc ∫ x in Ioo a b, |f x| ^ 2 ≤ ∫ _ in Ioo a b, C ^ 2 := by
        refine integral_mono_ae ?_ (integrableOn_const (by simp)) ?_
        · have := (Lp.memLp f).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
          simpa [Real.norm_eq_abs] using this
        · filter_upwards [h] with x hx
          exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    _ = (b - a) * C ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le hab, smul_eq_mul]

/-- An `L²(a, b)` function dominated almost everywhere by `c (|g| + d |h|)` has norm at most
`c (‖g‖ + d ‖h‖)`. -/
theorem MeasureTheory.Lp.norm_le_of_abs_le (f g h : Lp ℝ 2 (volume.restrict (Ioo a b))) {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hle : ∀ᵐ x ∂(volume.restrict (Ioo a b)), |f x| ≤ c * (|g x| + d * |h x|)) :
    ‖f‖ ≤ c * (‖g‖ + d * ‖h‖) := by
  set k : Lp ℝ 2 (volume.restrict (Ioo a b)) := c • (|g| + d • |h|) with hk
  have hfk : |f| ≤ |k| := by
    rw [← Lp.coeFn_le]
    filter_upwards [hle, Lp.coeFn_abs f, Lp.coeFn_abs k, Lp.coeFn_smul c (|g| + d • |h|),
      Lp.coeFn_add |g| (d • |h|), Lp.coeFn_smul d |h|, Lp.coeFn_abs g, Lp.coeFn_abs h]
      with x h1 h2 h3 h4 h5 h6 h7 h8
    rw [h2, h3, hk, h4, Pi.smul_apply, h5, Pi.add_apply, h6, Pi.smul_apply, h7, h8, smul_eq_mul,
      smul_eq_mul]
    refine h1.trans (le_abs_self _)
  calc ‖f‖ ≤ ‖k‖ := HasSolidNorm.solid hfk
    _ ≤ c * (‖g‖ + d * ‖h‖) := by
        rw [hk, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_abs_eq_norm, norm_smul, norm_abs_eq_norm, Real.norm_eq_abs, abs_of_nonneg hd]

end Lp

/-! ### Primitives, and the mean value theorems for integrals -/

namespace intervalIntegral

variable {a b t : ℝ} {K f : ℝ → ℝ}

/-- The fundamental theorem of calculus in the form a comparison argument on `Ico a b` needs: the
primitive `u ↦ ∫_a^u p` of a function continuous on `Icc a b` has right derivative `p t` at every
`t ∈ Ico a b`. -/
theorem hasDerivWithinAt_integral_Ici {p : ℝ → ℝ} (hp : ContinuousOn p (Icc a b))
    (ht : t ∈ Ico a b) : HasDerivWithinAt (fun u => ∫ s in a..u, p s) (p t) (Ici t) t := by
  have ht' : t ∈ Icc a b := Ico_subset_Icc_self ht
  have hint : IntervalIntegrable p volume a t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.1]
    exact (hp.mono (Icc_subset_Icc_right ht.2.le)).integrableOn_Icc
  have : Fact (t ∈ Icc a b) := ⟨ht'⟩
  have h : HasDerivWithinAt (fun u => ∫ s in a..u, p s) (p t) (Icc a b) t :=
    integral_hasDerivWithinAt_right hint
      (hp.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hp t ht')
  exact h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- The primitive `u ↦ ∫_a^u p` of a function continuous on `Icc a b` is continuous there. -/
theorem continuousOn_integral_Icc {p : ℝ → ℝ} (hp : ContinuousOn p (Icc a b)) :
    ContinuousOn (fun u => ∫ s in a..u, p s) (Icc a b) := by
  rcases le_or_gt a b with hab | hab
  · have h := continuousOn_primitive_interval (a := a) (b := b) (μ := volume) (f := p)
      (by rw [uIcc_of_le hab]; exact hp.integrableOn_Icc)
    rwa [uIcc_of_le hab] at h
  · simp [Icc_eq_empty_of_lt hab]

/-- **The weighted mean value theorem for integrals.** For `K ≥ 0` and `f` continuous on
`[a, b]`, `∫_a^b K f = f(ξ) ∫_a^b K` for some `ξ ∈ [a, b]`: the integral lies between the
extreme values of `f` times `∫ K`, and the intermediate value theorem supplies `ξ`. -/
theorem exists_integral_mul_eq_mul_integral (hab : a ≤ b) (hK : ContinuousOn K (Icc a b))
    (hf : ContinuousOn f (Icc a b)) (hKnn : ∀ t ∈ Icc a b, 0 ≤ K t) :
    ∃ ξ ∈ Icc a b, ∫ t in a..b, K t * f t = f ξ * ∫ t in a..b, K t := by
  have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab⟩
  obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  have hKf : IntervalIntegrable (fun t => K t * f t) volume a b :=
    (hK.mul hf).intervalIntegrable_of_Icc hab
  have hKc : ∀ c, IntervalIntegrable (fun t => K t * c) volume a b := fun c =>
    (hK.mul continuousOn_const).intervalIntegrable_of_Icc hab
  have hlow : f p * ∫ t in a..b, K t ≤ ∫ t in a..b, K t * f t := by
    have := integral_mono_on hab (hKc (f p)) hKf fun t ht =>
      mul_le_mul_of_nonneg_left (hmin ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  have hhigh : (∫ t in a..b, K t * f t) ≤ f q * ∫ t in a..b, K t := by
    have := integral_mono_on hab hKf (hKc (f q)) fun t ht =>
      mul_le_mul_of_nonneg_left (hmax ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  have hpq : uIcc p q ⊆ Icc a b := uIcc_subset_Icc hp hq
  obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_uIcc
    ((hf.mono hpq).mul continuousOn_const) (mem_uIcc_of_le hlow hhigh)
  exact ⟨ξ, hpq hξ, hξval.symm⟩

/-- A continuous nonnegative function on `[a, b]`, positive at an interior point, has a positive
integral. -/
theorem integral_pos_of_continuousOn_of_nonneg (hab : a < b) (hK : ContinuousOn K (Icc a b))
    (hKnn : ∀ t ∈ Icc a b, 0 ≤ K t) {c : ℝ} (hc : c ∈ Ioo a b) (hKc : 0 < K c) :
    0 < ∫ t in a..b, K t := by
  have hcont : ContinuousAt K c :=
    hK.continuousAt (Icc_mem_nhds hc.1 hc.2)
  obtain ⟨δ, hδ, hδpos⟩ : ∃ δ > 0, ∀ t, |t - c| < δ → 0 < K t := by
    have := (hcont.eventually (lt_mem_nhds hKc))
    rw [Metric.eventually_nhds_iff] at this
    obtain ⟨δ, hδ, h⟩ := this
    exact ⟨δ, hδ, fun t ht => h (by rwa [Real.dist_eq])⟩
  set ε := min δ (min (c - a) (b - c)) with hε
  have hε0 : 0 < ε := lt_min hδ (lt_min (by linarith [hc.1]) (by linarith [hc.2]))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεa : ε ≤ c - a := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ b - c := (min_le_right _ _).trans (min_le_right _ _)
  have hKint : IntervalIntegrable K volume a b := hK.intervalIntegrable_of_Icc hab.le
  have hsub : ∀ u v, a ≤ u → u ≤ v → v ≤ b → IntervalIntegrable K volume u v :=
    fun u v hu huv hv => hKint.mono_set
      (by rw [uIcc_of_le huv, uIcc_of_le hab.le]; exact Icc_subset_Icc hu hv)
  have h1 : IntervalIntegrable K volume a (c - ε) := hsub _ _ le_rfl (by linarith) (by linarith)
  have h2 : IntervalIntegrable K volume (c - ε) (c + ε) :=
    hsub _ _ (by linarith) (by linarith) (by linarith)
  have h3 : IntervalIntegrable K volume (c + ε) b := hsub _ _ (by linarith) (by linarith) le_rfl
  rw [← integral_add_adjacent_intervals (h1.trans h2) h3,
    ← integral_add_adjacent_intervals h1 h2]
  have hmid : 0 < ∫ t in c - ε..c + ε, K t := by
    refine intervalIntegral_pos_of_pos_on h2 (fun t ht => hδpos t ?_) (by linarith)
    rw [abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hleft : 0 ≤ ∫ t in a..c - ε, K t :=
    integral_nonneg (by linarith) fun t ht => hKnn t ⟨ht.1, by linarith [ht.2]⟩
  have hright : 0 ≤ ∫ t in c + ε..b, K t :=
    integral_nonneg (by linarith) fun t ht => hKnn t ⟨by linarith [ht.1], ht.2⟩
  linarith

/-- **The weighted mean value theorem, with `ξ` inside the open interval.** For `K ≥ 0` with
`∫_a^b K > 0` and `f` continuous, `∫ K f = f(ξ) ∫ K` with `ξ ∈ (a, b)`: if the mean value of `f`
lies strictly between its extreme values, the intermediate value theorem gives an interior `ξ`;
if it equals an extreme value, `f` takes that value wherever `K ≠ 0`, and `K ≠ 0` somewhere
inside because its integral is positive. -/
theorem exists_mem_Ioo_integral_mul_eq_mul_integral (hab : a < b)
    (hK : ContinuousOn K (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hKnn : ∀ t ∈ Icc a b, 0 ≤ K t) (hKpos : 0 < ∫ t in a..b, K t) :
    ∃ ξ ∈ Ioo a b, ∫ t in a..b, K t * f t = f ξ * ∫ t in a..b, K t := by
  set I : ℝ := ∫ t in a..b, K t with hI
  have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab.le⟩
  obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  have hKf : IntervalIntegrable (fun t => K t * f t) volume a b :=
    (hK.mul hf).intervalIntegrable_of_Icc hab.le
  have hKc : ∀ c, IntervalIntegrable (fun t => K t * c) volume a b := fun c =>
    (hK.mul continuousOn_const).intervalIntegrable_of_Icc hab.le
  have hlow : f p * I ≤ ∫ t in a..b, K t * f t := by
    have := integral_mono_on hab.le (hKc (f p)) hKf fun t ht =>
      mul_le_mul_of_nonneg_left (hmin ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  have hhigh : (∫ t in a..b, K t * f t) ≤ f q * I := by
    have := integral_mono_on hab.le hKf (hKc (f q)) fun t ht =>
      mul_le_mul_of_nonneg_left (hmax ht) (hKnn t ht)
    rwa [integral_mul_const, mul_comm] at this
  -- a continuous nonnegative function with zero integral vanishes inside
  have hvanish : ∀ g : ℝ → ℝ, ContinuousOn g (Icc a b) → (∀ t ∈ Icc a b, 0 ≤ g t) →
      (∫ t in a..b, g t) = 0 → ∀ t ∈ Ioo a b, g t = 0 := by
    intro g hgc hg hgint t ht
    by_contra hne
    have hpos : 0 < g t := lt_of_le_of_ne (hg t (Ioo_subset_Icc_self ht)) (Ne.symm hne)
    exact absurd hgint (integral_pos_of_continuousOn_of_nonneg hab hgc hg ht hpos).ne'
  -- `K` is nonzero at some interior point, because its integral is positive
  obtain ⟨ξ₀, hξ₀, hKξ₀⟩ : ∃ ξ ∈ Ioo a b, K ξ ≠ 0 := by
    by_contra hall
    push Not at hall
    have : (∫ t in a..b, K t) = 0 := by
      rw [integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
          fun t ht => hall t ht]
      simp
    exact absurd this hKpos.ne'
  -- an extreme value is attained where `K` does not vanish
  have hextreme : ∀ c, (∫ t in a..b, K t * f t) = f c * I → c ∈ Icc a b →
      ((∀ t ∈ Icc a b, f c ≤ f t) ∨ ∀ t ∈ Icc a b, f t ≤ f c) →
      ∃ ξ ∈ Ioo a b, ∫ t in a..b, K t * f t = f ξ * I := by
    intro c hc hcmem hext
    refine ⟨ξ₀, hξ₀, ?_⟩
    suffices hfξ : f ξ₀ = f c by rw [hfξ, hc]
    rcases hext with hext | hext
    · have e : (fun t => K t * (f t - f c)) = fun t => K t * f t - K t * f c := by
        funext t; ring
      have h := hvanish (fun t => K t * (f t - f c)) (hK.mul (hf.sub continuousOn_const))
        (fun t ht => mul_nonneg (hKnn t ht) (by linarith [hext t ht]))
        (by rw [e, integral_sub hKf (hKc (f c)), integral_mul_const, hc]; ring) ξ₀ hξ₀
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hKξ₀
      · linarith
    · have e : (fun t => K t * (f c - f t)) = fun t => K t * f c - K t * f t := by
        funext t; ring
      have h := hvanish (fun t => K t * (f c - f t)) (hK.mul (continuousOn_const.sub hf))
        (fun t ht => mul_nonneg (hKnn t ht) (by linarith [hext t ht]))
        (by rw [e, integral_sub (hKc (f c)) hKf, integral_mul_const, hc]; ring) ξ₀ hξ₀
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hKξ₀
      · linarith
  -- the mean value of `f` is either strictly between the extremes or one of them
  set μ : ℝ := (∫ t in a..b, K t * f t) / I with hμ
  have hμI : (∫ t in a..b, K t * f t) = μ * I := by
    rw [hμ, div_mul_cancel₀ _ hKpos.ne']
  have hpμ : f p ≤ μ := by rw [hμ, le_div_iff₀ hKpos]; exact hlow
  have hμq : μ ≤ f q := by rw [hμ, div_le_iff₀ hKpos]; exact hhigh
  rcases eq_or_lt_of_le hpμ with hpμ' | hpμ'
  · exact hextreme p (by rw [hμI, hpμ']) hp (Or.inl fun t ht => hmin ht)
  rcases eq_or_lt_of_le hμq with hμq' | hμq'
  · exact hextreme q (by rw [hμI, hμq']) hq (Or.inr fun t ht => hmax ht)
  -- strictly between: the intermediate value theorem on the open interval between `p` and `q`
  have hpq : p ≠ q := fun h => by rw [h] at hpμ'; linarith
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_Ioo hlt.le
      (hf.mono (Icc_subset_Icc hp.1 hq.2)) ⟨hpμ', hμq'⟩
    exact ⟨ξ, ⟨lt_of_le_of_lt hp.1 hξ.1, lt_of_lt_of_le hξ.2 hq.2⟩, by rw [hμI, hξval]⟩
  · obtain ⟨ξ, hξ, hξval⟩ := intermediate_value_Ioo' hlt.le
      (hf.mono (Icc_subset_Icc hq.1 hp.2)) ⟨hpμ', hμq'⟩
    exact ⟨ξ, ⟨lt_of_le_of_lt hq.1 hξ.1, lt_of_lt_of_le hξ.2 hp.2⟩, by rw [hμI, hξval]⟩

/-- The nonpositive-kernel form of `exists_mem_Ioo_integral_mul_eq_mul_integral`. -/
theorem exists_mem_Ioo_integral_mul_eq_mul_integral_of_nonpos (hab : a < b)
    (hK : ContinuousOn K (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hKnp : ∀ t ∈ Icc a b, K t ≤ 0) (hKneg : (∫ t in a..b, K t) < 0) :
    ∃ ξ ∈ Ioo a b, ∫ t in a..b, K t * f t = f ξ * ∫ t in a..b, K t := by
  have hKint : IntervalIntegrable K volume a b := hK.intervalIntegrable_of_Icc hab.le
  obtain ⟨ξ, hξ, h⟩ := exists_mem_Ioo_integral_mul_eq_mul_integral (K := fun t => -K t) hab
    hK.neg hf (fun t ht => neg_nonneg.2 (hKnp t ht)) (by rw [integral_neg]; linarith)
  refine ⟨ξ, hξ, ?_⟩
  have e : (fun t => -K t * f t) = fun t => -(K t * f t) := by funext t; ring
  rw [e, integral_neg, integral_neg] at h
  linarith

/-- The `L¹` distance from an interval-integrable weight to a continuous nonnegative function can
be made arbitrarily small: given `p` integrable on `a..b`, nonnegative on `Icc a b`, and `ε > 0`,
there is a continuous `q ≥ 0` with `∫ s in a..b, |p s - q s| ≤ ε`. From the density of
continuous functions in `L¹` (`Integrable.exists_hasCompactSupport_integral_sub_le`), applied to
the indicator of `Ioc a b`, and truncation at `0`, which does not increase the distance to a
nonnegative function. -/
theorem exists_continuous_nonneg_integral_abs_sub_le {p : ℝ → ℝ} (hab : a ≤ b)
    (hp : IntervalIntegrable p volume a b) (hp0 : ∀ t ∈ Icc a b, 0 ≤ p t) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ → ℝ, Continuous q ∧ (∀ s, 0 ≤ q s) ∧ ∫ s in a..b, |p s - q s| ≤ ε := by
  have hP : MeasureTheory.Integrable ((Ioc a b).indicator p) volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hp)
  obtain ⟨q₀, -, hq₀, hq₀c, hq₀i⟩ := hP.exists_hasCompactSupport_integral_sub_le hε
  refine ⟨fun s => max (q₀ s) 0, hq₀c.max continuous_const, fun s => le_max_right _ _, ?_⟩
  have hpI : MeasureTheory.IntegrableOn p (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hp
  have hqI : MeasureTheory.IntegrableOn (fun s => max (q₀ s) 0) (Ioc a b) volume :=
    (hq₀c.max continuous_const).integrableOn_Ioc
  calc ∫ s in a..b, |p s - max (q₀ s) 0|
      = ∫ s in Ioc a b, |p s - max (q₀ s) 0| := integral_of_le hab
    _ ≤ ∫ s in Ioc a b, ‖(Ioc a b).indicator p s - q₀ s‖ := by
        refine MeasureTheory.setIntegral_mono_on (hpI.sub hqI).abs
          (hP.sub hq₀i).norm.integrableOn measurableSet_Ioc fun s hs => ?_
        rw [Set.indicator_of_mem hs, Real.norm_eq_abs]
        have h0 : 0 ≤ p s := hp0 s (Ioc_subset_Icc_self hs)
        calc |p s - max (q₀ s) 0| = |max (p s) 0 - max (q₀ s) 0| := by rw [max_eq_left h0]
          _ ≤ |p s - q₀ s| := abs_max_sub_max_le_abs _ _ _
    _ ≤ ∫ s, ‖(Ioc a b).indicator p s - q₀ s‖ :=
        MeasureTheory.setIntegral_le_integral (hP.sub hq₀i).norm
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ε := hq₀

end intervalIntegral
