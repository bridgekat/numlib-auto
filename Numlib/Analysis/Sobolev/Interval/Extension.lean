/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Interval/Basic.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Interval.Basic

/-!
# The extension operator `W^{1,p}(I) → W^{1,p}(ℝ)`

The extension operator of [brezis2011functional] Theorem 8.6, for every exponent `1 ≤ p ≤ ∞` and
every nonempty open interval `I ⊆ ℝ`, bounded or not, together with Lemma 8.3 (a smooth cut-off
times the zero extension of a weakly differentiable function is weakly differentiable on the
larger interval).

## Main definitions

* `TopologicalSpace.Opens.Ioi a`, `TopologicalSpace.Opens.Iio b`, the half-lines as open sets;
* `SobolevIntervalLp.reflectFun c g`, the even reflection `x ↦ g (c + |x - c|)` of a function
  across the point `c`, and `SobolevIntervalLp.reflectDerivFun c w`, the odd reflection that is
  the derivative of the even one; `reflectFunIio`/`reflectDerivFunIio` are their mirror images;
* `SobolevIntervalLp.cutoffFun a b`, the Lipschitz cut-off equal to `1` on `(-∞, a]`, affine on
  `[a, b]` and `0` on `[b, ∞)`;
* the continuous linear maps `SobolevIntervalLp.reflectIoiCLM a : W^{1,p}(a, ∞) → W^{1,p}(ℝ)`,
  `reflectIioCLM b : W^{1,p}(-∞, b) → W^{1,p}(ℝ)` (extension by reflection),
  `cutoffIoiCLM hab : W^{1,p}(a, b) → W^{1,p}(a, ∞)` and `cutoffIioCLM hab` (multiplication by
  the cut-off and extension by zero), and `extensionIooCLM hab : W^{1,p}(a, b) → W^{1,p}(ℝ)`,
  their combination;
* `SobolevIntervalLp.extensionCLM hI hne : W^{1,p}(I) →L[ℝ] W^{1,p}(ℝ)`, **the extension
  operator** for an arbitrary nonempty open interval `I`.

## Main statements

* `HasWeakDerivOn.indicator_mul_of_tsupport_inter_subset` ([brezis2011functional] Lemma 8.3, in
  the general form `I ≤ J`): for `f` weakly differentiable on `I` and `η` smooth whose support
  meets `J` only inside `I`, the zero extension of `η f` to `J` has the weak derivative
  `η' f + η f'` there.
* `SobolevIntervalLp.memSobolevIntervalLp_reflectFun` (Theorem 8.6, the half-line case): the
  even reflection of the continuous representative of `u ∈ W^{1,p}(a, ∞)` lies in `W^{1,p}(ℝ)`,
  with weak derivative the odd reflection of `u'`, and both `L^p` norms at most doubled.
* `SobolevIntervalLp.memSobolevIntervalLp_cutoff_reflect` (Theorem 8.6, the bounded case): the
  extension of `u ∈ W^{1,p}(a, b)` agrees with `u` on `(a, b)` and satisfies
  `‖Pu‖_{L^p(ℝ)} ≤ 4 ‖u‖_{L^p(a, b)}` and
  `‖(Pu)'‖_{L^p(ℝ)} ≤ 4 (‖u'‖_{L^p(a, b)} + (b - a)⁻¹ ‖u‖_{L^p(a, b)})`.
* `SobolevIntervalLp.fn_extensionCLM`, `eLpNorm_fn_extensionCLM_le`,
  `eLpNorm_deriv_extensionCLM_le`, `norm_extensionCLM_le` (Theorem 8.6 (i)–(iii)):
  `P u = u` on `I`, `‖Pu‖_{L^p(ℝ)} ≤ 4 ‖u‖_{L^p(I)}`,
  `‖(Pu)'‖_{L^p(ℝ)} ≤ 4 (‖u'‖_{L^p(I)} + |I|⁻¹ ‖u‖_{L^p(I)})` with `|I|⁻¹ = 0` when `I` is
  unbounded, and `‖P‖ ≤ 8 (1 + |I|⁻¹)` in the norm of the type; `rep_extensionCLM`: the
  continuous representative of `Pu` is that of `u` on the closure of `I`.

## Design

The construction follows the book: reflection across the finite endpoint for a half-line, and for
a bounded interval `(a, b)` the splitting `u = η u + (1 - η) u` with a cut-off `η`, each piece
extended by zero to a half-line and then reflected. The cut-off is the *Lipschitz* function
`cutoffFun a b`, affine on `[a, b]` with `‖η'‖_∞ = 1/(b - a)`, rather than the `C¹` cut-off of
the book's figure: the product of a Lipschitz function with an absolutely continuous one is
absolutely continuous, so the calculus of `Mathlib.MeasureTheory.Function.AbsolutelyContinuous`
gives `(η ũ)' = η' ũ + η u'` and every piece is put into `W^{1,p}` by Lemma 8.2
(`MeasureTheory.LocallyIntegrableOn.hasWeakDerivOn_integral`) from an explicit integral
representation — no test-function computation is repeated — and the constants of the book's
footnote 6 (`4` and `4 (1 + 1/|I|)`) are reached exactly, which a `C¹` cut-off cannot do.

Every operator is built by one generic constructor, `SobolevIntervalLp.linearMapOfFun`, from a
pair of functions (the extension and its derivative) that are linear up to null sets, so that the
half-line and bounded cases share all the bookkeeping. The operator on an arbitrary interval is
obtained from the four shapes of an open interval
(`TopologicalSpace.Opens.eq_intervals_of_ordConnected`) through an existence statement
(`SobolevIntervalLp.exists_extensionCLM`) and `Classical.choose`, which avoids transporting
types along the equation `I = Opens.Ioi a`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Interval Topology

noncomputable section

/-! ### Half-lines as open sets -/

namespace TopologicalSpace.Opens

/-- The half-line `(a, ∞)` as an open set of `ℝ`. -/
def Ioi (a : ℝ) : Opens ℝ := ⟨Set.Ioi a, isOpen_Ioi⟩

/-- The half-line `(-∞, b)` as an open set of `ℝ`. -/
def Iio (b : ℝ) : Opens ℝ := ⟨Set.Iio b, isOpen_Iio⟩

/-- The underlying set of `Opens.Ioi a` is `Set.Ioi a`. -/
@[simp]
theorem coe_Ioi (a : ℝ) : (Opens.Ioi a : Set ℝ) = Set.Ioi a := rfl

/-- The underlying set of `Opens.Iio b` is `Set.Iio b`. -/
@[simp]
theorem coe_Iio (b : ℝ) : (Opens.Iio b : Set ℝ) = Set.Iio b := rfl

/-- The whole line is an interval. -/
theorem ordConnected_top : ((⊤ : Opens ℝ) : Set ℝ).OrdConnected := by
  rw [Opens.coe_top]; exact ordConnected_univ

/-- Every point lies in the closure of the whole line. -/
theorem mem_closure_top (x : ℝ) : x ∈ closure ((⊤ : Opens ℝ) : Set ℝ) := by
  rw [Opens.coe_top, closure_univ]; exact mem_univ x

end TopologicalSpace.Opens

/-! ### Lemma 8.3: a cut-off times a zero extension -/

section CutoffZeroExtension

variable {I J : Opens ℝ}

/-- The zero extension to `J ⊇ I` of a function locally integrable on `I` which vanishes off a
closed set `K` with `K ∩ J ⊆ I` is locally integrable on `J`: near a point of `I` it is the
function itself, near a point of `J \ I` it vanishes. -/
theorem locallyIntegrableOn_indicator_of_eqOn_zero {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g I) {K : Set ℝ} (hK : IsClosed K) (hKJ : K ∩ (J : Set ℝ) ⊆ I)
    (hgK : ∀ x ∉ K, g x = 0) : LocallyIntegrableOn ((I : Set ℝ).indicator g) J := by
  intro x hxJ
  by_cases hxI : x ∈ (I : Set ℝ)
  · obtain ⟨s, hs, hsi⟩ := hg x hxI
    refine ⟨s ∩ I, ?_, ?_⟩
    · have hI : (I : Set ℝ) ∈ 𝓝 x := I.isOpen.mem_nhds hxI
      rw [nhdsWithin_eq_nhds.2 hI] at hs
      exact inter_mem (nhdsWithin_le_nhds hs) (nhdsWithin_le_nhds hI)
    · refine (hsi.mono_set inter_subset_left).congr_fun_ae
        (ae_restrict_of_ae_restrict_of_subset inter_subset_right ?_)
      exact (ae_restrict_iff' I.isOpen.measurableSet).2 (Eventually.of_forall fun y hy ↦
        (indicator_of_mem hy g).symm)
  · have hxK : x ∉ K := fun h ↦ hxI (hKJ ⟨h, hxJ⟩)
    refine ⟨Kᶜ, nhdsWithin_le_nhds (hK.isOpen_compl.mem_nhds hxK), ?_⟩
    refine (integrableOn_zero : IntegrableOn (fun _ : ℝ ↦ (0 : ℝ)) Kᶜ volume).congr_fun
      (fun y hy ↦ ?_) hK.isOpen_compl.measurableSet
    by_cases hyI : y ∈ (I : Set ℝ)
    · rw [indicator_of_mem hyI, hgK y hy]
    · rw [indicator_of_notMem hyI]

/-- The product of a test function on `J` with a smooth function `η` whose support meets `J`
only inside `I ≤ J` is a test function on `I`. -/
def TestFunction.mulContDiffOfTSupportSubset (φ : 𝓓(J, ℝ)) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hsupp : tsupport η ∩ (J : Set ℝ) ⊆ I) : 𝓓(I, ℝ) where
  toFun x := η x * φ x
  contDiff' := hη.mul φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport.mul_left
  tsupport_subset' := by
    refine (subset_inter tsupport_mul_subset_left tsupport_mul_subset_right).trans ?_
    exact (inter_subset_inter_right _ φ.tsupport_subset).trans hsupp

/-- `TestFunction.mulContDiffOfTSupportSubset` as a function. -/
@[simp]
theorem TestFunction.mulContDiffOfTSupportSubset_coe (φ : 𝓓(J, ℝ)) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hsupp : tsupport η ∩ (J : Set ℝ) ⊆ I) :
    (φ.mulContDiffOfTSupportSubset hη hsupp : ℝ → ℝ) = fun x ↦ η x * φ x := rfl

/-- **A cut-off times a zero extension is weakly differentiable on the larger interval**
([brezis2011functional] Lemma 8.3, in the general form): let `I ≤ J` be open subsets of the line,
`w` the weak derivative of `f` on `I`, and `η` smooth with `tsupport η ∩ J ⊆ I`. Then the zero
extension to `J` of `η f` has the weak derivative `η' f + η w` on `J` (extended by zero as well).
For a test function `φ` on `J`, the product `η φ` is a test function on `I`, and
`∫_J 1_I η f φ' = ∫_I f ((η φ)' - η' φ) = -∫_I (w η + f η') φ`. The book's case is `I = (0, 1)`,
`J = (0, ∞)` and `η` the cut-off vanishing on `(3/4, ∞)`. -/
theorem HasWeakDerivOn.indicator_mul_of_tsupport_inter_subset (hIJ : I ≤ J) {f w : ℝ → ℝ}
    (h : HasWeakDerivOn f w I) {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hsupp : tsupport η ∩ (J : Set ℝ) ⊆ I) :
    HasWeakDerivOn ((I : Set ℝ).indicator fun x ↦ η x * f x)
      ((I : Set ℝ).indicator fun x ↦ deriv η x * f x + η x * w x) J := by
  have hη' : ContDiff ℝ ∞ (deriv η) := hη.iterate_deriv 1
  have hsupp' : tsupport (deriv η) ∩ (J : Set ℝ) ⊆ I :=
    (inter_subset_inter_left _ (tsupport_deriv_subset)).trans hsupp
  refine hasWeakDerivOn_iff.2 ⟨?_, ?_, fun φ ↦ ?_⟩
  · refine locallyIntegrableOn_indicator_of_eqOn_zero
      (h.locallyIntegrableOn.continuousOn_mul hη.continuous.continuousOn I.isOpen.isLocallyClosed)
      (isClosed_tsupport η) hsupp fun x hx ↦ ?_
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · refine locallyIntegrableOn_indicator_of_eqOn_zero
      ((h.locallyIntegrableOn.continuousOn_mul hη'.continuous.continuousOn
          I.isOpen.isLocallyClosed).add
        (h.locallyIntegrableOn_weakDeriv.continuousOn_mul hη.continuous.continuousOn
          I.isOpen.isLocallyClosed))
      (isClosed_tsupport η) hsupp fun x hx ↦ ?_
    rw [image_eq_zero_of_notMem_tsupport hx,
      image_eq_zero_of_notMem_tsupport fun h' ↦ hx (tsupport_deriv_subset h'), zero_mul, zero_mul,
      add_zero]
  -- the two test functions on `I`
  set ψ : 𝓓(I, ℝ) := φ.mulContDiffOfTSupportSubset hη hsupp with hψ
  set χ : 𝓓(I, ℝ) := φ.mulContDiffOfTSupportSubset hη' hsupp' with hχ
  have hIJ' : (J : Set ℝ) ∩ I = I := inter_eq_right.2 hIJ
  have hdψ : ∀ x, deriv ψ x = deriv η x * φ x + η x * deriv φ x := fun x ↦ by
    rw [hψ, TestFunction.mulContDiffOfTSupportSubset_coe]
    exact deriv_fun_mul (hη.differentiable (by simp) x) (φ.contDiff.differentiable (by simp) x)
  have i1 : IntegrableOn (fun x ↦ ψ x * w x) I := (h.integrable_smul_weakDeriv ψ).integrableOn
  have i2 : IntegrableOn (fun x ↦ χ x * f x) I := (h.integrable_smul χ).integrableOn
  have i3 : IntegrableOn (fun x ↦ deriv ψ x * f x) I := by
    simpa only [TestFunction.derivApply_coe, smul_eq_mul] using
      (h.integrable_smul (ψ.fderivApply 1)).integrableOn
  have key := h.integral_deriv_mul ψ
  simp_rw [← Set.indicator_mul_right]
  rw [setIntegral_indicator I.isOpen.measurableSet, hIJ',
    setIntegral_indicator I.isOpen.measurableSet, hIJ']
  have e1 : ∫ x in (I : Set ℝ), deriv φ x * (η x * f x)
      = (∫ x in (I : Set ℝ), deriv ψ x * f x) - ∫ x in (I : Set ℝ), χ x * f x := by
    refine Eq.trans ?_ (integral_sub i3 i2)
    refine setIntegral_congr_fun I.isOpen.measurableSet fun x _ ↦ ?_
    simp only [hdψ, hχ, TestFunction.mulContDiffOfTSupportSubset_coe]
    ring
  have e2 : ∫ x in (I : Set ℝ), φ x * (deriv η x * f x + η x * w x)
      = (∫ x in (I : Set ℝ), χ x * f x) + ∫ x in (I : Set ℝ), ψ x * w x := by
    refine Eq.trans ?_ (integral_add i2 i1)
    refine setIntegral_congr_fun I.isOpen.measurableSet fun x _ ↦ ?_
    simp only [hχ, hψ, TestFunction.mulContDiffOfTSupportSubset_coe]
    ring
  rw [e1, e2]
  linarith [key]

end CutoffZeroExtension


/-! ### Reflection across a point -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {c : ℝ}

/-- The even reflection across `c` of a function `g`: `x ↦ g (c + |x - c|)`, which is `g` on
`[c, ∞)` and `x ↦ g (2c - x)` on `(-∞, c]`. -/
def reflectFun (c : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := g (c + |x - c|)

/-- The odd reflection across `c` of a function `w`: `w` on `[c, ∞)` and `x ↦ -w (2c - x)` on
`(-∞, c)`. It is the derivative of the even reflection of a primitive of `w`
(`SobolevIntervalLp.reflectFun_eq_add_integral`). -/
def reflectDerivFun (c : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ := if c ≤ x then w x else -w (2 * c - x)

/-- The even reflection is the function itself to the right of `c`. -/
theorem reflectFun_of_le (g : ℝ → ℝ) {x : ℝ} (hx : c ≤ x) : reflectFun c g x = g x := by
  rw [reflectFun, abs_of_nonneg (sub_nonneg.2 hx), add_sub_cancel]

/-- The even reflection is the reflected function to the left of `c`. -/
theorem reflectFun_of_le' (g : ℝ → ℝ) {x : ℝ} (hx : x ≤ c) :
    reflectFun c g x = g (2 * c - x) := by
  rw [reflectFun, abs_of_nonpos (sub_nonpos.2 hx)]
  congr 1
  ring

/-- The odd reflection is the function itself to the right of `c`. -/
theorem reflectDerivFun_of_le (w : ℝ → ℝ) {x : ℝ} (hx : c ≤ x) : reflectDerivFun c w x = w x :=
  ite_eq_left hx

/-- The odd reflection is minus the reflected function to the left of `c`. -/
theorem reflectDerivFun_of_lt (w : ℝ → ℝ) {x : ℝ} (hx : x < c) :
    reflectDerivFun c w x = -w (2 * c - x) :=
  ite_eq_right (not_le.2 hx)

/-- The odd and the even reflection of a function have the same absolute value. -/
theorem abs_reflectDerivFun (w : ℝ → ℝ) (x : ℝ) :
    |reflectDerivFun c w x| = |reflectFun c w x| := by
  rcases le_or_gt c x with hx | hx
  · rw [reflectDerivFun_of_le w hx, reflectFun_of_le w hx]
  · rw [reflectDerivFun_of_lt w hx, reflectFun_of_le' w hx.le, abs_neg]

/-- The even reflection of a function continuous on `[c, ∞)` is continuous. -/
theorem continuous_reflectFun {g : ℝ → ℝ} (hg : ContinuousOn g (Ici c)) :
    Continuous (reflectFun c g) :=
  hg.comp_continuous (continuous_const.add (continuous_id.sub continuous_const).abs)
    fun _ ↦ mem_Ici.2 (le_add_of_nonneg_right (abs_nonneg _))

/-- The even reflection of a measurable function is measurable. -/
theorem measurable_reflectFun {g : ℝ → ℝ} (hg : Measurable g) : Measurable (reflectFun c g) :=
  hg.comp (continuous_const.add (continuous_id.sub continuous_const).abs).measurable

/-- The odd reflection of a measurable function is measurable. -/
theorem measurable_reflectDerivFun {w : ℝ → ℝ} (hw : Measurable w) :
    Measurable (reflectDerivFun c w) :=
  Measurable.ite measurableSet_Ici hw (hw.comp (measurable_const.sub measurable_id)).neg

/-- The odd reflection is additive, pointwise. -/
theorem reflectDerivFun_add (w₁ w₂ : ℝ → ℝ) (x : ℝ) :
    reflectDerivFun c (w₁ + w₂) x = reflectDerivFun c w₁ x + reflectDerivFun c w₂ x := by
  simp only [reflectDerivFun, Pi.add_apply]
  split_ifs <;> ring

/-- The odd reflection is homogeneous, pointwise. -/
theorem reflectDerivFun_smul (r : ℝ) (w : ℝ → ℝ) (x : ℝ) :
    reflectDerivFun c (r • w) x = r * reflectDerivFun c w x := by
  simp only [reflectDerivFun, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The odd reflection only sees the function up to a null set of `(c, ∞)`. -/
theorem reflectDerivFun_congr_ae {w₁ w₂ : ℝ → ℝ} (h : w₁ =ᵐ[volume.restrict (Ioi c)] w₂) :
    reflectDerivFun c w₁ =ᵐ[volume] reflectDerivFun c w₂ := by
  have h' : ∀ᵐ x : ℝ, x ∈ Ioi c → w₁ x = w₂ x := (ae_restrict_iff' measurableSet_Ioi).1 h
  have h'' : ∀ᵐ x : ℝ, 2 * c - x ∈ Ioi c → w₁ (2 * c - x) = w₂ (2 * c - x) :=
    (Measure.measurePreserving_sub_left volume (2 * c)).quasiMeasurePreserving.ae h'
  have hne : ∀ᵐ x : ℝ, x ≠ c := by simp [ae_iff, measure_singleton]
  filter_upwards [h', h'', hne] with x hx1 hx2 hxc
  rcases lt_or_gt_of_ne hxc with hlt | hgt
  · rw [reflectDerivFun_of_lt w₁ hlt, reflectDerivFun_of_lt w₂ hlt,
      hx2 (show c < 2 * c - x by linarith)]
  · rw [reflectDerivFun_of_le w₁ hgt.le, reflectDerivFun_of_le w₂ hgt.le, hx1 hgt]

/-- Composition with the reflection `x ↦ 2c - x`, which is measure preserving and maps
`(-∞, c]` onto `[c, ∞)`, preserves the `L^p` norm. -/
theorem eLpNorm_comp_sub_left_restrict_Iic (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable g (volume.restrict (Ici c))) :
    eLpNorm (fun x ↦ g (2 * c - x)) p (volume.restrict (Iic c))
      = eLpNorm g p (volume.restrict (Ici c)) := by
  have hmp : MeasurePreserving (fun x : ℝ ↦ 2 * c - x) volume volume :=
    Measure.measurePreserving_sub_left volume (2 * c)
  have hpre : (fun x : ℝ ↦ 2 * c - x) ⁻¹' Ici c = Iic c := by
    ext x
    simp only [mem_preimage, mem_Ici, mem_Iic]
    constructor <;> intro h <;> linarith
  rw [← hpre]
  exact eLpNorm_comp_measurePreserving hg (hmp.restrict_preimage measurableSet_Ici)

/-- **The `L^p` norm of an even reflection is at most twice the `L^p` norm on the half-line**:
`‖g (c + |· - c|)‖_{L^p(ℝ)} ≤ 2 ‖g‖_{L^p(c, ∞)}`, for every `1 ≤ p ≤ ∞`; each half-line
contributes the norm of `g` on `(c, ∞)`. -/
theorem eLpNorm_reflectFun_le [Fact (1 ≤ p)] {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi c))) :
    eLpNorm (reflectFun c g) p volume ≤ 2 * eLpNorm g p (volume.restrict (Ioi c)) := by
  have hIci : volume.restrict (Ici c) = volume.restrict (Ioi c) :=
    (Measure.restrict_congr_set Ioi_ae_eq_Ici).symm
  have hg' : AEStronglyMeasurable g (volume.restrict (Ici c)) := by rwa [hIci]
  set F := reflectFun c g with hF
  calc eLpNorm F p volume
      = eLpNorm ((Iic c).indicator F + (Iic c)ᶜ.indicator F) p volume := by
        rw [Set.indicator_self_add_compl]
    _ ≤ eLpNorm ((Iic c).indicator F) p volume + eLpNorm ((Iic c)ᶜ.indicator F) p volume :=
        eLpNorm_add_le Fact.out
    _ = eLpNorm F p (volume.restrict (Iic c)) + eLpNorm F p (volume.restrict (Ioi c)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iic, compl_Iic,
          eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi]
    _ = eLpNorm (fun x ↦ g (2 * c - x)) p (volume.restrict (Iic c))
          + eLpNorm g p (volume.restrict (Ioi c)) := by
        congr 1
        · refine eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_Iic).2
            (Eventually.of_forall fun x hx ↦ ?_))
          exact reflectFun_of_le' g hx
        · refine eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
            (Eventually.of_forall fun x hx ↦ ?_))
          exact reflectFun_of_le g (le_of_lt hx)
    _ = 2 * eLpNorm g p (volume.restrict (Ioi c)) := by
        rw [eLpNorm_comp_sub_left_restrict_Iic g hg', hIci, two_mul]

/-- The odd and the even reflection of a measurable function have the same `L^p` norm. -/
theorem eLpNorm_reflectDerivFun {w : ℝ → ℝ} (hw : Measurable w) :
    eLpNorm (reflectDerivFun c w) p volume = eLpNorm (reflectFun c w) p volume :=
  eLpNorm_congr_norm_ae (measurable_reflectDerivFun hw).aestronglyMeasurable
    (measurable_reflectFun hw).aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_reflectDerivFun])

/-- **The even reflection of a primitive is a primitive of the odd reflection**: if
`g y - g x = ∫_x^y w` for all `x, y ≥ c`, then `g (c + |x - c|) = g c + ∫_c^x w*` for every
`x ∈ ℝ`, `w*` the odd reflection of `w`; to the left of `c` this is the change of variables
`t ↦ 2c - t`. -/
theorem reflectFun_eq_add_integral {g w : ℝ → ℝ}
    (hg : ∀ x ∈ Ici c, ∀ y ∈ Ici c, g y - g x = ∫ t in x..y, w t) (x : ℝ) :
    reflectFun c g x = g c + ∫ t in c..x, reflectDerivFun c w t := by
  rcases le_or_gt c x with hx | hx
  · rw [reflectFun_of_le g hx, ← sub_eq_iff_eq_add', hg c self_mem_Ici x hx]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    exact (reflectDerivFun_of_le w ht.1).symm
  · rw [reflectFun_of_le' g hx.le, ← sub_eq_iff_eq_add', hg c self_mem_Ici (2 * c - x)
      (show c ≤ 2 * c - x by linarith)]
    have e : ∫ t in c..x, reflectDerivFun c w t = ∫ t in c..x, -w (2 * c - t) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hne : ∀ᵐ t : ℝ, t ≠ c := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with t htc ht
      rw [uIoc_of_ge hx.le] at ht
      exact reflectDerivFun_of_lt w (lt_of_le_of_ne ht.2 htc)
    have h2 : 2 * c - c = c := by ring
    rw [e, intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left (fun t ↦ w t),
      h2, intervalIntegral.integral_symm]

end SobolevIntervalLp


/-! ### Linear maps between Sobolev spaces given at the level of functions -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞}

/-- The data of a linear map `W^{1,p}(I) → W^{1,p}(J)` at the level of functions: to each
`u ∈ W^{1,p}(I)` a function `F u` on the line and its weak derivative `W u` on `J`, both in
`L^p(J)` and both linear in `u` up to null sets of `J`. `SobolevIntervalLp.MapData.toLinearMap`
turns it into the linear map `u ↦ (F u, W u)`. -/
structure MapData (p : ℝ≥0∞) (I J : Opens ℝ) where
  /-- The image function. -/
  F : SobolevIntervalLp 1 p I → ℝ → ℝ
  /-- The weak derivative of the image. -/
  W : SobolevIntervalLp 1 p I → ℝ → ℝ
  memLp_F : ∀ u, MemLp (F u) p (volume.restrict J)
  memLp_W : ∀ u, MemLp (W u) p (volume.restrict J)
  hasWeakDerivOn : ∀ u, HasWeakDerivOn (F u) (W u) J
  F_add : ∀ u v, F (u + v) =ᵐ[volume.restrict J] F u + F v
  F_smul : ∀ (r : ℝ) u, F (r • u) =ᵐ[volume.restrict J] r • F u
  W_add : ∀ u v, W (u + v) =ᵐ[volume.restrict J] W u + W v
  W_smul : ∀ (r : ℝ) u, W (r • u) =ᵐ[volume.restrict J] r • W u

namespace MapData

variable {I J : Opens ℝ} [Fact (1 ≤ p)] (d : MapData p I J)

/-- The image of `u` under the map described by `d`, as an element of `W^{1,p}(J)`: the pair
`(F u, W u)` read in `L^p(J)`. -/
def map (u : SobolevIntervalLp 1 p I) : SobolevIntervalLp 1 p J :=
  SobolevIntervalLp.mk ![(d.memLp_F u).toLp _, (d.memLp_W u).toLp _] fun j ↦ by
    have h0 : HasWeakIteratedDerivOn 0 ((d.memLp_F u).toLp _) ((d.memLp_F u).toLp _) J :=
      HasWeakIteratedLineDerivOn.of_length_eq_zero rfl _
        ((Lp.memLp _).locallyIntegrableOn (Ω := J) Fact.out)
    have h1 : HasWeakIteratedDerivOn 1 ((d.memLp_F u).toLp _) ((d.memLp_W u).toLp _) J :=
      (d.hasWeakDerivOn u).congr_ae (d.memLp_F u).coeFn_toLp.symm (d.memLp_W u).coeFn_toLp.symm
    fin_cases j
    · exact h0
    · exact h1

/-- The function of the image is `F u`. -/
@[simp]
theorem deriv_map_zero (u : SobolevIntervalLp 1 p I) :
    deriv (d.map u) 0 = (d.memLp_F u).toLp _ := rfl

/-- The weak derivative of the image is `W u`. -/
@[simp]
theorem deriv_map_one (u : SobolevIntervalLp 1 p I) :
    deriv (d.map u) 1 = (d.memLp_W u).toLp _ := rfl

/-- The function of the image agrees with `F u` off a null set of `J`. -/
theorem fn_map (u : SobolevIntervalLp 1 p I) : fn (d.map u) =ᵐ[volume.restrict J] d.F u :=
  (d.memLp_F u).coeFn_toLp

/-- The weak derivative of the image agrees with `W u` off a null set of `J`. -/
theorem coeFn_deriv_map_one (u : SobolevIntervalLp 1 p I) :
    ⇑(deriv (d.map u) 1) =ᵐ[volume.restrict J] d.W u :=
  (d.memLp_W u).coeFn_toLp

/-- The `L^p` norm of the function of the image. -/
theorem norm_deriv_map_zero (u : SobolevIntervalLp 1 p I) :
    ‖deriv (d.map u) 0‖ = (eLpNorm (d.F u) p (volume.restrict J)).toReal :=
  Lp.norm_toLp _ (d.memLp_F u)

/-- The `L^p` norm of the weak derivative of the image. -/
theorem norm_deriv_map_one (u : SobolevIntervalLp 1 p I) :
    ‖deriv (d.map u) 1‖ = (eLpNorm (d.W u) p (volume.restrict J)).toReal :=
  Lp.norm_toLp _ (d.memLp_W u)

/-- The map described by `d` as a linear map `W^{1,p}(I) → W^{1,p}(J)`. -/
def toLinearMap : SobolevIntervalLp 1 p I →ₗ[ℝ] SobolevIntervalLp 1 p J where
  toFun := d.map
  map_add' u v := ext fun j ↦ by
    fin_cases j
    · change (d.memLp_F (u + v)).toLp _ = (d.memLp_F u).toLp _ + (d.memLp_F v).toLp _
      rw [(d.memLp_F (u + v)).toLp_congr ((d.memLp_F u).add (d.memLp_F v)) (d.F_add u v),
        MemLp.toLp_add]
    · change (d.memLp_W (u + v)).toLp _ = (d.memLp_W u).toLp _ + (d.memLp_W v).toLp _
      rw [(d.memLp_W (u + v)).toLp_congr ((d.memLp_W u).add (d.memLp_W v)) (d.W_add u v),
        MemLp.toLp_add]
  map_smul' r u := ext fun j ↦ by
    fin_cases j
    · change (d.memLp_F (r • u)).toLp _ = r • (d.memLp_F u).toLp _
      rw [(d.memLp_F (r • u)).toLp_congr ((d.memLp_F u).const_smul r) (d.F_smul r u),
        MemLp.toLp_const_smul]
    · change (d.memLp_W (r • u)).toLp _ = r • (d.memLp_W u).toLp _
      rw [(d.memLp_W (r • u)).toLp_congr ((d.memLp_W u).const_smul r) (d.W_smul r u),
        MemLp.toLp_const_smul]

/-- `MapData.toLinearMap` is `MapData.map`. -/
@[simp]
theorem toLinearMap_apply (u : SobolevIntervalLp 1 p I) : d.toLinearMap u = d.map u := rfl

/-- The norm of the image is at most the sum of the `L^p` norms of `F u` and `W u`. -/
theorem norm_map_le (u : SobolevIntervalLp 1 p I) :
    ‖d.map u‖ ≤ (eLpNorm (d.F u) p (volume.restrict J)).toReal
      + (eLpNorm (d.W u) p (volume.restrict J)).toReal := by
  refine (norm_le_sum_norm_deriv _).trans_eq ?_
  rw [Fin.sum_univ_two, norm_deriv_map_zero, norm_deriv_map_one]

/-- The map described by `d` as a continuous linear map, given a bound
`‖F u‖_{L^p(J)} + ‖W u‖_{L^p(J)} ≤ C ‖u‖`. -/
def toCLM (C : ℝ) (hC : ∀ u, (eLpNorm (d.F u) p (volume.restrict J)).toReal
      + (eLpNorm (d.W u) p (volume.restrict J)).toReal ≤ C * ‖u‖) :
    SobolevIntervalLp 1 p I →L[ℝ] SobolevIntervalLp 1 p J :=
  d.toLinearMap.mkContinuous C fun u ↦ (d.norm_map_le u).trans (hC u)

/-- `MapData.toCLM` is `MapData.map`. -/
@[simp]
theorem toCLM_apply (C : ℝ) (hC : ∀ u, (eLpNorm (d.F u) p (volume.restrict J)).toReal
      + (eLpNorm (d.W u) p (volume.restrict J)).toReal ≤ C * ‖u‖) (u : SobolevIntervalLp 1 p I) :
    d.toCLM C hC u = d.map u := rfl

end MapData

/-- From a bound `eLpNorm f ≤ C * ‖x‖ₑ` in `ℝ≥0∞`, the real bound
`(eLpNorm f).toReal ≤ C * ‖x‖`. -/
theorem toReal_eLpNorm_le_of_le_mul_enorm {μ : Measure ℝ} {f : ℝ → ℝ} {E : Type*}
    [NormedAddCommGroup E] {x : E} {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm f p μ ≤ ENNReal.ofReal C * ‖x‖ₑ) : (eLpNorm f p μ).toReal ≤ C * ‖x‖ := by
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top) h).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, toReal_enorm]

end SobolevIntervalLp


/-! ### Theorem 8.6 on the half-line `(c, ∞)` -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {c : ℝ}

/-- The half-line `(c, ∞)` is an interval. -/
theorem ordConnected_coe_Ioi (c : ℝ) : ((Opens.Ioi c : Opens ℝ) : Set ℝ).OrdConnected :=
  ordConnected_Ioi

/-- The closure of the half-line `(c, ∞)` is `[c, ∞)`. -/
theorem closure_coe_Ioi (c : ℝ) : closure ((Opens.Ioi c : Opens ℝ) : Set ℝ) = Ici c := by
  rw [Opens.coe_Ioi, closure_Ioi]

/-- The continuous representative of `u ∈ W^{1,p}(c, ∞)` is continuous on `[c, ∞)`. -/
theorem continuousOn_rep_Ici (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    ContinuousOn (rep u) (Ici c) := by
  have := continuousOn_rep (ordConnected_coe_Ioi c) u
  rwa [closure_coe_Ioi] at this

/-- The fundamental theorem of calculus in `W^{1,p}(c, ∞)`, on `[c, ∞)`. -/
theorem rep_sub_rep_Ioi (u : SobolevIntervalLp 1 p (Opens.Ioi c)) {x y : ℝ} (hx : c ≤ x)
    (hy : c ≤ y) : rep u y - rep u x = ∫ t in x..y, deriv u 1 t :=
  rep_sub_rep (ordConnected_coe_Ioi c) u (by rw [closure_coe_Ioi]; exact hx)
    (by rw [closure_coe_Ioi]; exact hy)

/-- The `L^p(ℝ)` norm of the reflected representative of `u ∈ W^{1,p}(c, ∞)` is at most twice
the `L^p(c, ∞)` norm of `u`. -/
theorem eLpNorm_reflectFun_rep_le (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    eLpNorm (reflectFun c (rep u)) p volume ≤ 2 * ‖deriv u 0‖ₑ := by
  have hcont : ContinuousOn (rep u) (Ioi c) := (continuousOn_rep_Ici u).mono Ioi_subset_Ici_self
  refine (eLpNorm_reflectFun_le (hcont.aestronglyMeasurable measurableSet_Ioi)).trans_eq ?_
  rw [Lp.enorm_def, deriv_zero, eLpNorm_congr_ae (fn_ae_eq_rep (ordConnected_coe_Ioi c) u)]
  rfl

/-- The `L^p(ℝ)` norm of the odd reflection of `u'` is at most twice the `L^p(c, ∞)` norm of
`u'`. -/
theorem eLpNorm_reflectDerivFun_deriv_le (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    eLpNorm (reflectDerivFun c (deriv u 1)) p volume ≤ 2 * ‖deriv u 1‖ₑ := by
  rw [eLpNorm_reflectDerivFun (Lp.stronglyMeasurable _).measurable, Lp.enorm_def]
  exact eLpNorm_reflectFun_le (Lp.aestronglyMeasurable _)

/-- The reflected representative lies in `L^p(ℝ)`. -/
theorem memLp_reflectFun_rep (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    MemLp (reflectFun c (rep u)) p volume :=
  memLp_iff.2 ((eLpNorm_reflectFun_rep_le u).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofNat_lt_top enorm_lt_top))

/-- The odd reflection of `u'` lies in `L^p(ℝ)`. -/
theorem memLp_reflectDerivFun_deriv (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    MemLp (reflectDerivFun c (deriv u 1)) p volume :=
  memLp_iff.2 ((eLpNorm_reflectDerivFun_deriv_le u).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofNat_lt_top enorm_lt_top))

omit [Fact (1 ≤ p)] in
/-- Membership of `L^p(ℝ)` read over the restriction of Lebesgue measure to the whole line, the
measure of the type `SobolevIntervalLp m p ⊤`. -/
theorem memLp_restrict_top_iff {f : ℝ → ℝ} :
    MemLp f p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ↔ MemLp f p volume := by
  rw [Opens.coe_top, Measure.restrict_univ]

omit [Fact (1 ≤ p)] in
/-- Almost everywhere equality read over the restriction of Lebesgue measure to the whole line,
the measure of the type `SobolevIntervalLp m p ⊤`. -/
theorem eventuallyEq_restrict_top_iff {f g : ℝ → ℝ} :
    f =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] g ↔ f =ᵐ[volume] g := by
  rw [Opens.coe_top, Measure.restrict_univ]

/-- **The even reflection of a `W^{1,p}(c, ∞)` function has the odd reflection of its derivative
as weak derivative on `ℝ`**: with `ũ(x) = ũ(c) + ∫_c^x u*` for the odd reflection `u*` of `u'`
(`SobolevIntervalLp.reflectFun_eq_add_integral`), this is Lemma 8.2 on the whole line. -/
theorem hasWeakDerivOn_reflectFun_rep (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    HasWeakDerivOn (reflectFun c (rep u)) (reflectDerivFun c (deriv u 1)) ⊤ := by
  have hW : MemLp (reflectDerivFun c (deriv u 1)) p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    memLp_restrict_top_iff.2 (memLp_reflectDerivFun_deriv u)
  have h0 := (hW.locallyIntegrableOn Fact.out).hasWeakDerivOn_integral Opens.ordConnected_top
    (y₀ := c) (Set.mem_univ c) (rep u c)
  refine h0.congr_ae (Eventually.of_forall fun x ↦ ?_) (EventuallyEq.refl _ _)
  exact (reflectFun_eq_add_integral (fun x hx y hy ↦ rep_sub_rep_Ioi u hx hy) x).symm

/-- **Theorem 8.6 of [brezis2011functional], the half-line case**: for `u ∈ W^{1,p}(c, ∞)`,
`1 ≤ p ≤ ∞`, the even reflection `ũ(c + |x - c|)` of its continuous representative lies in
`W^{1,p}(ℝ)`, its weak derivative is the odd reflection of `u'`, and
`‖u*‖_{L^p(ℝ)} ≤ 2 ‖u‖_{L^p(c, ∞)}`, `‖(u*)'‖_{L^p(ℝ)} ≤ 2 ‖u'‖_{L^p(c, ∞)}`. -/
theorem memSobolevIntervalLp_reflectFun (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    MemSobolevIntervalLp (reflectFun c (rep u)) 1 p ⊤ ∧
      HasWeakDerivOn (reflectFun c (rep u)) (reflectDerivFun c (deriv u 1)) ⊤ ∧
      eLpNorm (reflectFun c (rep u)) p volume ≤ 2 * ‖deriv u 0‖ₑ ∧
      eLpNorm (reflectDerivFun c (deriv u 1)) p volume ≤ 2 * ‖deriv u 1‖ₑ :=
  ⟨memSobolevIntervalLp_one_iff.2 ⟨memLp_restrict_top_iff.2 (memLp_reflectFun_rep u), _,
    hasWeakDerivOn_reflectFun_rep u, memLp_restrict_top_iff.2 (memLp_reflectDerivFun_deriv u)⟩,
    hasWeakDerivOn_reflectFun_rep u, eLpNorm_reflectFun_rep_le u,
    eLpNorm_reflectDerivFun_deriv_le u⟩

/-- The reflected representative is linear in `u`, pointwise. -/
theorem reflectFun_rep_add (u v : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    reflectFun c (rep (u + v)) = reflectFun c (rep u) + reflectFun c (rep v) := by
  funext x
  exact rep_add (ordConnected_coe_Ioi c) u v (by
    rw [closure_coe_Ioi]; exact mem_Ici.2 (le_add_of_nonneg_right (abs_nonneg _)))

/-- The reflected representative is homogeneous in `u`, pointwise. -/
theorem reflectFun_rep_smul (r : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    reflectFun c (rep (r • u)) = r • reflectFun c (rep u) := by
  funext x
  exact rep_smul (ordConnected_coe_Ioi c) r u (by
    rw [closure_coe_Ioi]; exact mem_Ici.2 (le_add_of_nonneg_right (abs_nonneg _)))

omit [Fact (1 ≤ p)] in
/-- The odd reflection of `u'` is additive in `u`, almost everywhere. -/
theorem reflectDerivFun_deriv_add (u v : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    reflectDerivFun c (deriv (u + v) 1) =ᵐ[volume]
      reflectDerivFun c (deriv u 1) + reflectDerivFun c (deriv v 1) := by
  rw [deriv_add]
  refine (reflectDerivFun_congr_ae (Lp.coeFn_add _ _)).trans (Eventually.of_forall fun x ↦ ?_)
  exact reflectDerivFun_add _ _ x

omit [Fact (1 ≤ p)] in
/-- The odd reflection of `u'` is homogeneous in `u`, almost everywhere. -/
theorem reflectDerivFun_deriv_smul (r : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    reflectDerivFun c (deriv (r • u) 1) =ᵐ[volume] r • reflectDerivFun c (deriv u 1) := by
  rw [deriv_smul]
  refine (reflectDerivFun_congr_ae (Lp.coeFn_smul _ _)).trans (Eventually.of_forall fun x ↦ ?_)
  exact reflectDerivFun_smul r _ x

/-- The extension by reflection across `c`, as `SobolevIntervalLp.MapData`. -/
def reflectIoiData (c : ℝ) : MapData p (Opens.Ioi c) ⊤ where
  F u := reflectFun c (rep u)
  W u := reflectDerivFun c (deriv u 1)
  memLp_F u := memLp_restrict_top_iff.2 (memLp_reflectFun_rep u)
  memLp_W u := memLp_restrict_top_iff.2 (memLp_reflectDerivFun_deriv u)
  hasWeakDerivOn u := hasWeakDerivOn_reflectFun_rep u
  F_add u v := by rw [reflectFun_rep_add]
  F_smul r u := by rw [reflectFun_rep_smul]
  W_add u v := eventuallyEq_restrict_top_iff.2 (reflectDerivFun_deriv_add u v)
  W_smul r u := eventuallyEq_restrict_top_iff.2 (reflectDerivFun_deriv_smul r u)

/-- **The extension operator by reflection `W^{1,p}(c, ∞) → W^{1,p}(ℝ)`**
([brezis2011functional] Theorem 8.6, the case `I = (0, ∞)`): `u ↦ ũ(c + |x - c|)`, a continuous
linear map of norm at most `4`. -/
def reflectIoiCLM (c : ℝ) : SobolevIntervalLp 1 p (Opens.Ioi c) →L[ℝ] SobolevIntervalLp 1 p ⊤ :=
  (reflectIoiData c).toCLM 4 fun u ↦ by
    rw [Opens.coe_top, Measure.restrict_univ]
    have h0 := toReal_eLpNorm_le_of_le_mul_enorm (C := 2) zero_le_two
      (by rw [ENNReal.ofReal_ofNat]; exact eLpNorm_reflectFun_rep_le u)
    have h1 := toReal_eLpNorm_le_of_le_mul_enorm (C := 2) zero_le_two
      (by rw [ENNReal.ofReal_ofNat]; exact eLpNorm_reflectDerivFun_deriv_le u)
    have h2 := norm_deriv_le u 0
    have h3 := norm_deriv_le u 1
    change (eLpNorm (reflectFun c (rep u)) p volume).toReal
      + (eLpNorm (reflectDerivFun c (deriv u 1)) p volume).toReal ≤ 4 * ‖u‖
    linarith

/-- The function of the reflected element is the reflected representative. -/
theorem fn_reflectIoiCLM (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    fn (reflectIoiCLM c u) =ᵐ[volume] reflectFun c (rep u) :=
  eventuallyEq_restrict_top_iff.1 ((reflectIoiData c).fn_map u)

/-- The weak derivative of the reflected element is the odd reflection of `u'`. -/
theorem coeFn_deriv_reflectIoiCLM (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    ⇑(deriv (reflectIoiCLM c u) 1) =ᵐ[volume] reflectDerivFun c (deriv u 1) :=
  eventuallyEq_restrict_top_iff.1 ((reflectIoiData c).coeFn_deriv_map_one u)

/-- `‖Pu‖_{L^p(ℝ)} ≤ 2 ‖u‖_{L^p(c, ∞)}` for the reflection operator. -/
theorem norm_deriv_reflectIoiCLM_zero (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    ‖deriv (reflectIoiCLM c u) 0‖ ≤ 2 * ‖deriv u 0‖ := by
  rw [reflectIoiCLM, MapData.toCLM_apply, MapData.norm_deriv_map_zero, Opens.coe_top,
    Measure.restrict_univ]
  exact toReal_eLpNorm_le_of_le_mul_enorm (C := 2) zero_le_two
    (by rw [ENNReal.ofReal_ofNat]; exact eLpNorm_reflectFun_rep_le u)

/-- `‖(Pu)'‖_{L^p(ℝ)} ≤ 2 ‖u'‖_{L^p(c, ∞)}` for the reflection operator. -/
theorem norm_deriv_reflectIoiCLM_one (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    ‖deriv (reflectIoiCLM c u) 1‖ ≤ 2 * ‖deriv u 1‖ := by
  rw [reflectIoiCLM, MapData.toCLM_apply, MapData.norm_deriv_map_one, Opens.coe_top,
    Measure.restrict_univ]
  exact toReal_eLpNorm_le_of_le_mul_enorm (C := 2) zero_le_two
    (by rw [ENNReal.ofReal_ofNat]; exact eLpNorm_reflectDerivFun_deriv_le u)

/-- The continuous representative of the reflected element is the reflected representative,
everywhere on the line. -/
theorem rep_reflectIoiCLM (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    rep (reflectIoiCLM c u) = reflectFun c (rep u) := by
  funext x
  refine rep_eq_of_continuousOn Opens.ordConnected_top _
    (continuous_reflectFun (continuousOn_rep_Ici u)).continuousOn ?_ (Opens.mem_closure_top x)
  exact eventuallyEq_restrict_top_iff.2 (fn_reflectIoiCLM u)

/-- The reflected element restricts to `u` on `(c, ∞)`. -/
theorem fn_reflectIoiCLM_restrict (u : SobolevIntervalLp 1 p (Opens.Ioi c)) :
    fn (reflectIoiCLM c u) =ᵐ[volume.restrict (Opens.Ioi c : Set ℝ)] fn u := by
  have h1 : fn (reflectIoiCLM c u) =ᵐ[volume.restrict (Opens.Ioi c : Set ℝ)] reflectFun c (rep u) :=
    ae_restrict_of_ae (fn_reflectIoiCLM u)
  refine h1.trans ?_
  refine EventuallyEq.trans ?_ (fn_ae_eq_rep (ordConnected_coe_Ioi c) u).symm
  exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx ↦
    reflectFun_of_le _ (le_of_lt hx))

end SobolevIntervalLp


/-! ### Theorem 8.6 on the half-line `(-∞, c)` -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {c : ℝ}

/-- The even reflection across `c` of a function `g` defined to the left of `c`:
`x ↦ g (c - |x - c|)`, which is `g` on `(-∞, c]` and `x ↦ g (2c - x)` on `[c, ∞)`. -/
def reflectFunIio (c : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := g (c - |x - c|)

/-- The odd reflection across `c` of a function `w` defined to the left of `c`: `w` on
`(-∞, c]` and `x ↦ -w (2c - x)` on `(c, ∞)`. -/
def reflectDerivFunIio (c : ℝ) (w : ℝ → ℝ) (x : ℝ) : ℝ := if x ≤ c then w x else -w (2 * c - x)

/-- The even reflection is the function itself to the left of `c`. -/
theorem reflectFunIio_of_le (g : ℝ → ℝ) {x : ℝ} (hx : x ≤ c) : reflectFunIio c g x = g x := by
  rw [reflectFunIio, abs_of_nonpos (sub_nonpos.2 hx), neg_sub, sub_sub_cancel]

/-- The even reflection is the reflected function to the right of `c`. -/
theorem reflectFunIio_of_le' (g : ℝ → ℝ) {x : ℝ} (hx : c ≤ x) :
    reflectFunIio c g x = g (2 * c - x) := by
  rw [reflectFunIio, abs_of_nonneg (sub_nonneg.2 hx)]
  congr 1
  ring

/-- The odd reflection is the function itself to the left of `c`. -/
theorem reflectDerivFunIio_of_le (w : ℝ → ℝ) {x : ℝ} (hx : x ≤ c) :
    reflectDerivFunIio c w x = w x :=
  ite_eq_left hx

/-- The odd reflection is minus the reflected function to the right of `c`. -/
theorem reflectDerivFunIio_of_lt (w : ℝ → ℝ) {x : ℝ} (hx : c < x) :
    reflectDerivFunIio c w x = -w (2 * c - x) :=
  ite_eq_right (not_le.2 hx)

/-- The odd and the even reflection of a function have the same absolute value. -/
theorem abs_reflectDerivFunIio (w : ℝ → ℝ) (x : ℝ) :
    |reflectDerivFunIio c w x| = |reflectFunIio c w x| := by
  rcases le_or_gt x c with hx | hx
  · rw [reflectDerivFunIio_of_le w hx, reflectFunIio_of_le w hx]
  · rw [reflectDerivFunIio_of_lt w hx, reflectFunIio_of_le' w hx.le, abs_neg]

/-- The even reflection of a function continuous on `(-∞, c]` is continuous. -/
theorem continuous_reflectFunIio {g : ℝ → ℝ} (hg : ContinuousOn g (Iic c)) :
    Continuous (reflectFunIio c g) :=
  hg.comp_continuous (continuous_const.sub (continuous_id.sub continuous_const).abs)
    fun _ ↦ mem_Iic.2 (sub_le_self _ (abs_nonneg _))

/-- The even reflection of a measurable function is measurable. -/
theorem measurable_reflectFunIio {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (reflectFunIio c g) :=
  hg.comp (continuous_const.sub (continuous_id.sub continuous_const).abs).measurable

/-- The odd reflection of a measurable function is measurable. -/
theorem measurable_reflectDerivFunIio {w : ℝ → ℝ} (hw : Measurable w) :
    Measurable (reflectDerivFunIio c w) :=
  Measurable.ite measurableSet_Iic hw (hw.comp (measurable_const.sub measurable_id)).neg

/-- The odd reflection is additive, pointwise. -/
theorem reflectDerivFunIio_add (w₁ w₂ : ℝ → ℝ) (x : ℝ) :
    reflectDerivFunIio c (w₁ + w₂) x = reflectDerivFunIio c w₁ x + reflectDerivFunIio c w₂ x := by
  simp only [reflectDerivFunIio, Pi.add_apply]
  split_ifs <;> ring

/-- The odd reflection is homogeneous, pointwise. -/
theorem reflectDerivFunIio_smul (r : ℝ) (w : ℝ → ℝ) (x : ℝ) :
    reflectDerivFunIio c (r • w) x = r * reflectDerivFunIio c w x := by
  simp only [reflectDerivFunIio, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The odd reflection only sees the function up to a null set of `(-∞, c)`. -/
theorem reflectDerivFunIio_congr_ae {w₁ w₂ : ℝ → ℝ} (h : w₁ =ᵐ[volume.restrict (Iio c)] w₂) :
    reflectDerivFunIio c w₁ =ᵐ[volume] reflectDerivFunIio c w₂ := by
  have h' : ∀ᵐ x : ℝ, x ∈ Iio c → w₁ x = w₂ x := (ae_restrict_iff' measurableSet_Iio).1 h
  have h'' : ∀ᵐ x : ℝ, 2 * c - x ∈ Iio c → w₁ (2 * c - x) = w₂ (2 * c - x) :=
    (Measure.measurePreserving_sub_left volume (2 * c)).quasiMeasurePreserving.ae h'
  have hne : ∀ᵐ x : ℝ, x ≠ c := by simp [ae_iff, measure_singleton]
  filter_upwards [h', h'', hne] with x hx1 hx2 hxc
  rcases lt_or_gt_of_ne hxc with hlt | hgt
  · rw [reflectDerivFunIio_of_le w₁ hlt.le, reflectDerivFunIio_of_le w₂ hlt.le, hx1 hlt]
  · rw [reflectDerivFunIio_of_lt w₁ hgt, reflectDerivFunIio_of_lt w₂ hgt,
      hx2 (show 2 * c - x < c by linarith)]

/-- Composition with the reflection `x ↦ 2c - x`, which is measure preserving and maps
`[c, ∞)` onto `(-∞, c]`, preserves the `L^p` norm. -/
theorem eLpNorm_comp_sub_left_restrict_Ici (g : ℝ → ℝ)
    (hg : AEStronglyMeasurable g (volume.restrict (Iic c))) :
    eLpNorm (fun x ↦ g (2 * c - x)) p (volume.restrict (Ici c))
      = eLpNorm g p (volume.restrict (Iic c)) := by
  have hmp : MeasurePreserving (fun x : ℝ ↦ 2 * c - x) volume volume :=
    Measure.measurePreserving_sub_left volume (2 * c)
  have hpre : (fun x : ℝ ↦ 2 * c - x) ⁻¹' Iic c = Ici c := by
    ext x
    simp only [mem_preimage, mem_Ici, mem_Iic]
    constructor <;> intro h <;> linarith
  rw [← hpre]
  exact eLpNorm_comp_measurePreserving hg (hmp.restrict_preimage measurableSet_Iic)

/-- The `L^p` norm of an even reflection across `c` of a function on `(-∞, c)` is at most twice
its `L^p(-∞, c)` norm. -/
theorem eLpNorm_reflectFunIio_le [Fact (1 ≤ p)] {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Iio c))) :
    eLpNorm (reflectFunIio c g) p volume ≤ 2 * eLpNorm g p (volume.restrict (Iio c)) := by
  have hIic : volume.restrict (Iic c) = volume.restrict (Iio c) :=
    (Measure.restrict_congr_set Iio_ae_eq_Iic).symm
  have hg' : AEStronglyMeasurable g (volume.restrict (Iic c)) := by rwa [hIic]
  set F := reflectFunIio c g with hF
  calc eLpNorm F p volume
      = eLpNorm ((Ici c).indicator F + (Ici c)ᶜ.indicator F) p volume := by
        rw [Set.indicator_self_add_compl]
    _ ≤ eLpNorm ((Ici c).indicator F) p volume + eLpNorm ((Ici c)ᶜ.indicator F) p volume :=
        eLpNorm_add_le Fact.out
    _ = eLpNorm F p (volume.restrict (Ici c)) + eLpNorm F p (volume.restrict (Iio c)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici, compl_Ici,
          eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iio]
    _ = eLpNorm (fun x ↦ g (2 * c - x)) p (volume.restrict (Ici c))
          + eLpNorm g p (volume.restrict (Iio c)) := by
        congr 1
        · refine eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_Ici).2
            (Eventually.of_forall fun x hx ↦ ?_))
          exact reflectFunIio_of_le' g hx
        · refine eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_Iio).2
            (Eventually.of_forall fun x hx ↦ ?_))
          exact reflectFunIio_of_le g (le_of_lt hx)
    _ = 2 * eLpNorm g p (volume.restrict (Iio c)) := by
        rw [eLpNorm_comp_sub_left_restrict_Ici g hg', hIic, two_mul]

/-- The odd and the even reflection of a measurable function have the same `L^p` norm. -/
theorem eLpNorm_reflectDerivFunIio {w : ℝ → ℝ} (hw : Measurable w) :
    eLpNorm (reflectDerivFunIio c w) p volume = eLpNorm (reflectFunIio c w) p volume :=
  eLpNorm_congr_norm_ae (measurable_reflectDerivFunIio hw).aestronglyMeasurable
    (measurable_reflectFunIio hw).aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_reflectDerivFunIio])

/-- The even reflection of a primitive is a primitive of the odd reflection, on the left
half-line: if `g y - g x = ∫_x^y w` for all `x, y ≤ c`, then `g (c - |x - c|) = g c + ∫_c^x w*`
for every `x ∈ ℝ`. -/
theorem reflectFunIio_eq_add_integral {g w : ℝ → ℝ}
    (hg : ∀ x ∈ Iic c, ∀ y ∈ Iic c, g y - g x = ∫ t in x..y, w t) (x : ℝ) :
    reflectFunIio c g x = g c + ∫ t in c..x, reflectDerivFunIio c w t := by
  rcases le_or_gt x c with hx | hx
  · rw [reflectFunIio_of_le g hx, ← sub_eq_iff_eq_add', hg c self_mem_Iic x hx]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_ge hx] at ht
    exact (reflectDerivFunIio_of_le w ht.2).symm
  · rw [reflectFunIio_of_le' g hx.le, ← sub_eq_iff_eq_add', hg c self_mem_Iic (2 * c - x)
      (show 2 * c - x ≤ c by linarith)]
    have e : ∫ t in c..x, reflectDerivFunIio c w t = ∫ t in c..x, -w (2 * c - t) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
      rw [uIoc_of_le hx.le] at ht
      exact reflectDerivFunIio_of_lt w ht.1
    have h2 : 2 * c - c = c := by ring
    rw [e, intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left (fun t ↦ w t),
      h2, intervalIntegral.integral_symm]

variable [Fact (1 ≤ p)]

/-- The half-line `(-∞, c)` is an interval. -/
theorem ordConnected_coe_Iio (c : ℝ) : ((Opens.Iio c : Opens ℝ) : Set ℝ).OrdConnected :=
  ordConnected_Iio

/-- The closure of the half-line `(-∞, c)` is `(-∞, c]`. -/
theorem closure_coe_Iio (c : ℝ) : closure ((Opens.Iio c : Opens ℝ) : Set ℝ) = Iic c := by
  rw [Opens.coe_Iio, closure_Iio]

/-- The continuous representative of `u ∈ W^{1,p}(-∞, c)` is continuous on `(-∞, c]`. -/
theorem continuousOn_rep_Iic (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    ContinuousOn (rep u) (Iic c) := by
  have := continuousOn_rep (ordConnected_coe_Iio c) u
  rwa [closure_coe_Iio] at this

/-- The fundamental theorem of calculus in `W^{1,p}(-∞, c)`, on `(-∞, c]`. -/
theorem rep_sub_rep_Iio (u : SobolevIntervalLp 1 p (Opens.Iio c)) {x y : ℝ} (hx : x ≤ c)
    (hy : y ≤ c) : rep u y - rep u x = ∫ t in x..y, deriv u 1 t :=
  rep_sub_rep (ordConnected_coe_Iio c) u (by rw [closure_coe_Iio]; exact hx)
    (by rw [closure_coe_Iio]; exact hy)

/-- The `L^p(ℝ)` norm of the reflected representative of `u ∈ W^{1,p}(-∞, c)` is at most twice
the `L^p(-∞, c)` norm of `u`. -/
theorem eLpNorm_reflectFunIio_rep_le (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    eLpNorm (reflectFunIio c (rep u)) p volume ≤ 2 * ‖deriv u 0‖ₑ := by
  have hcont : ContinuousOn (rep u) (Iio c) := (continuousOn_rep_Iic u).mono Iio_subset_Iic_self
  refine (eLpNorm_reflectFunIio_le (hcont.aestronglyMeasurable measurableSet_Iio)).trans_eq ?_
  rw [Lp.enorm_def, deriv_zero, eLpNorm_congr_ae (fn_ae_eq_rep (ordConnected_coe_Iio c) u)]
  rfl

/-- The `L^p(ℝ)` norm of the odd reflection of `u'` is at most twice the `L^p(-∞, c)` norm of
`u'`. -/
theorem eLpNorm_reflectDerivFunIio_deriv_le (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    eLpNorm (reflectDerivFunIio c (deriv u 1)) p volume ≤ 2 * ‖deriv u 1‖ₑ := by
  rw [eLpNorm_reflectDerivFunIio (Lp.stronglyMeasurable _).measurable, Lp.enorm_def]
  exact eLpNorm_reflectFunIio_le (Lp.aestronglyMeasurable _)

/-- The reflected representative lies in `L^p(ℝ)`. -/
theorem memLp_reflectFunIio_rep (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    MemLp (reflectFunIio c (rep u)) p volume :=
  memLp_iff.2 ((eLpNorm_reflectFunIio_rep_le u).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofNat_lt_top enorm_lt_top))

/-- The odd reflection of `u'` lies in `L^p(ℝ)`. -/
theorem memLp_reflectDerivFunIio_deriv (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    MemLp (reflectDerivFunIio c (deriv u 1)) p volume :=
  memLp_iff.2 ((eLpNorm_reflectDerivFunIio_deriv_le u).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofNat_lt_top enorm_lt_top))

/-- The even reflection of a `W^{1,p}(-∞, c)` function has the odd reflection of its derivative
as weak derivative on `ℝ`. -/
theorem hasWeakDerivOn_reflectFunIio_rep (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    HasWeakDerivOn (reflectFunIio c (rep u)) (reflectDerivFunIio c (deriv u 1)) ⊤ := by
  have hW : MemLp (reflectDerivFunIio c (deriv u 1)) p
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
    memLp_restrict_top_iff.2 (memLp_reflectDerivFunIio_deriv u)
  have h0 := (hW.locallyIntegrableOn Fact.out).hasWeakDerivOn_integral Opens.ordConnected_top
    (y₀ := c) (Set.mem_univ c) (rep u c)
  refine h0.congr_ae (Eventually.of_forall fun x ↦ ?_) (EventuallyEq.refl _ _)
  exact (reflectFunIio_eq_add_integral (fun x hx y hy ↦ rep_sub_rep_Iio u hx hy) x).symm

/-- **Theorem 8.6 of [brezis2011functional], the left half-line case**: for
`u ∈ W^{1,p}(-∞, c)`, the even reflection `ũ(c - |x - c|)` of its continuous representative lies
in `W^{1,p}(ℝ)`, its weak derivative is the odd reflection of `u'`, and both `L^p` norms are at
most doubled. -/
theorem memSobolevIntervalLp_reflectFunIio (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    MemSobolevIntervalLp (reflectFunIio c (rep u)) 1 p ⊤ ∧
      HasWeakDerivOn (reflectFunIio c (rep u)) (reflectDerivFunIio c (deriv u 1)) ⊤ ∧
      eLpNorm (reflectFunIio c (rep u)) p volume ≤ 2 * ‖deriv u 0‖ₑ ∧
      eLpNorm (reflectDerivFunIio c (deriv u 1)) p volume ≤ 2 * ‖deriv u 1‖ₑ :=
  ⟨memSobolevIntervalLp_one_iff.2 ⟨memLp_restrict_top_iff.2 (memLp_reflectFunIio_rep u), _,
    hasWeakDerivOn_reflectFunIio_rep u,
    memLp_restrict_top_iff.2 (memLp_reflectDerivFunIio_deriv u)⟩,
    hasWeakDerivOn_reflectFunIio_rep u, eLpNorm_reflectFunIio_rep_le u,
    eLpNorm_reflectDerivFunIio_deriv_le u⟩

/-- The reflected representative is additive in `u`, pointwise. -/
theorem reflectFunIio_rep_add (u v : SobolevIntervalLp 1 p (Opens.Iio c)) :
    reflectFunIio c (rep (u + v)) = reflectFunIio c (rep u) + reflectFunIio c (rep v) := by
  funext x
  exact rep_add (ordConnected_coe_Iio c) u v (by
    rw [closure_coe_Iio]; exact mem_Iic.2 (sub_le_self _ (abs_nonneg _)))

/-- The reflected representative is homogeneous in `u`, pointwise. -/
theorem reflectFunIio_rep_smul (r : ℝ) (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    reflectFunIio c (rep (r • u)) = r • reflectFunIio c (rep u) := by
  funext x
  exact rep_smul (ordConnected_coe_Iio c) r u (by
    rw [closure_coe_Iio]; exact mem_Iic.2 (sub_le_self _ (abs_nonneg _)))

omit [Fact (1 ≤ p)] in
/-- The odd reflection of `u'` is additive in `u`, almost everywhere. -/
theorem reflectDerivFunIio_deriv_add (u v : SobolevIntervalLp 1 p (Opens.Iio c)) :
    reflectDerivFunIio c (deriv (u + v) 1) =ᵐ[volume]
      reflectDerivFunIio c (deriv u 1) + reflectDerivFunIio c (deriv v 1) := by
  rw [deriv_add]
  refine (reflectDerivFunIio_congr_ae (Lp.coeFn_add _ _)).trans
    (Eventually.of_forall fun x ↦ ?_)
  exact reflectDerivFunIio_add _ _ x

omit [Fact (1 ≤ p)] in
/-- The odd reflection of `u'` is homogeneous in `u`, almost everywhere. -/
theorem reflectDerivFunIio_deriv_smul (r : ℝ) (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    reflectDerivFunIio c (deriv (r • u) 1) =ᵐ[volume] r • reflectDerivFunIio c (deriv u 1) := by
  rw [deriv_smul]
  refine (reflectDerivFunIio_congr_ae (Lp.coeFn_smul _ _)).trans
    (Eventually.of_forall fun x ↦ ?_)
  exact reflectDerivFunIio_smul r _ x

/-- The extension by reflection across `c` from the left half-line, as
`SobolevIntervalLp.MapData`. -/
def reflectIioData (c : ℝ) : MapData p (Opens.Iio c) ⊤ where
  F u := reflectFunIio c (rep u)
  W u := reflectDerivFunIio c (deriv u 1)
  memLp_F u := memLp_restrict_top_iff.2 (memLp_reflectFunIio_rep u)
  memLp_W u := memLp_restrict_top_iff.2 (memLp_reflectDerivFunIio_deriv u)
  hasWeakDerivOn u := hasWeakDerivOn_reflectFunIio_rep u
  F_add u v := by rw [reflectFunIio_rep_add]
  F_smul r u := by rw [reflectFunIio_rep_smul]
  W_add u v := eventuallyEq_restrict_top_iff.2 (reflectDerivFunIio_deriv_add u v)
  W_smul r u := eventuallyEq_restrict_top_iff.2 (reflectDerivFunIio_deriv_smul r u)

/-- **The extension operator by reflection `W^{1,p}(-∞, c) → W^{1,p}(ℝ)`**
([brezis2011functional] Theorem 8.6, mirror image of the case `I = (0, ∞)`):
`u ↦ ũ(c - |x - c|)`, a continuous linear map of norm at most `4`. -/
def reflectIioCLM (c : ℝ) : SobolevIntervalLp 1 p (Opens.Iio c) →L[ℝ] SobolevIntervalLp 1 p ⊤ :=
  (reflectIioData c).toCLM 4 fun u ↦ by
    rw [Opens.coe_top, Measure.restrict_univ]
    have h0 := toReal_eLpNorm_le_of_le_mul_enorm (C := 2) zero_le_two
      (by rw [ENNReal.ofReal_ofNat]; exact eLpNorm_reflectFunIio_rep_le u)
    have h1 := toReal_eLpNorm_le_of_le_mul_enorm (C := 2) zero_le_two
      (by rw [ENNReal.ofReal_ofNat]; exact eLpNorm_reflectDerivFunIio_deriv_le u)
    have h2 := norm_deriv_le u 0
    have h3 := norm_deriv_le u 1
    change (eLpNorm (reflectFunIio c (rep u)) p volume).toReal
      + (eLpNorm (reflectDerivFunIio c (deriv u 1)) p volume).toReal ≤ 4 * ‖u‖
    linarith

/-- The function of the reflected element is the reflected representative. -/
theorem fn_reflectIioCLM (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    fn (reflectIioCLM c u) =ᵐ[volume] reflectFunIio c (rep u) :=
  eventuallyEq_restrict_top_iff.1 ((reflectIioData c).fn_map u)

/-- The weak derivative of the reflected element is the odd reflection of `u'`. -/
theorem coeFn_deriv_reflectIioCLM (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    ⇑(deriv (reflectIioCLM c u) 1) =ᵐ[volume] reflectDerivFunIio c (deriv u 1) :=
  eventuallyEq_restrict_top_iff.1 ((reflectIioData c).coeFn_deriv_map_one u)

/-- `‖Pu‖_{L^p(ℝ)} ≤ 2 ‖u‖_{L^p(-∞, c)}` for the reflection operator. -/
theorem norm_deriv_reflectIioCLM_zero (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    ‖deriv (reflectIioCLM c u) 0‖ ≤ 2 * ‖deriv u 0‖ := by
  rw [reflectIioCLM, MapData.toCLM_apply, MapData.norm_deriv_map_zero, Opens.coe_top,
    Measure.restrict_univ]
  exact toReal_eLpNorm_le_of_le_mul_enorm (C := 2) zero_le_two
    (by rw [ENNReal.ofReal_ofNat]; exact eLpNorm_reflectFunIio_rep_le u)

/-- `‖(Pu)'‖_{L^p(ℝ)} ≤ 2 ‖u'‖_{L^p(-∞, c)}` for the reflection operator. -/
theorem norm_deriv_reflectIioCLM_one (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    ‖deriv (reflectIioCLM c u) 1‖ ≤ 2 * ‖deriv u 1‖ := by
  rw [reflectIioCLM, MapData.toCLM_apply, MapData.norm_deriv_map_one, Opens.coe_top,
    Measure.restrict_univ]
  exact toReal_eLpNorm_le_of_le_mul_enorm (C := 2) zero_le_two
    (by rw [ENNReal.ofReal_ofNat]; exact eLpNorm_reflectDerivFunIio_deriv_le u)

/-- The continuous representative of the reflected element is the reflected representative,
everywhere on the line. -/
theorem rep_reflectIioCLM (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    rep (reflectIioCLM c u) = reflectFunIio c (rep u) := by
  funext x
  refine rep_eq_of_continuousOn Opens.ordConnected_top _
    (continuous_reflectFunIio (continuousOn_rep_Iic u)).continuousOn ?_ (Opens.mem_closure_top x)
  exact eventuallyEq_restrict_top_iff.2 (fn_reflectIioCLM u)

/-- The reflected element restricts to `u` on `(-∞, c)`. -/
theorem fn_reflectIioCLM_restrict (u : SobolevIntervalLp 1 p (Opens.Iio c)) :
    fn (reflectIioCLM c u) =ᵐ[volume.restrict (Opens.Iio c : Set ℝ)] fn u := by
  have h1 : fn (reflectIioCLM c u) =ᵐ[volume.restrict (Opens.Iio c : Set ℝ)]
      reflectFunIio c (rep u) := ae_restrict_of_ae (fn_reflectIioCLM u)
  refine h1.trans ?_
  refine EventuallyEq.trans ?_ (fn_ae_eq_rep (ordConnected_coe_Iio c) u).symm
  exact (ae_restrict_iff' measurableSet_Iio).2 (Eventually.of_forall fun x hx ↦
    reflectFunIio_of_le _ (le_of_lt hx))

end SobolevIntervalLp


/-! ### Integration by parts against an absolutely continuous factor -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

/-- **Integration by parts in `W^{1,p}(I)` against an absolutely continuous factor**: for `η`
absolutely continuous on `[x, y]` with `x, y ∈ Ī`, whose classical derivative is `η'` almost
everywhere on `I`, `∫_x^y (η' ũ + η u') = η(y) ũ(y) - η(x) ũ(x)`. This is Mathlib's product rule
for absolutely continuous functions applied to `η` and the continuous representative. -/
theorem integral_deriv_mul_rep_add_mul_deriv (hI : (I : Set ℝ).OrdConnected)
    (u : SobolevIntervalLp 1 p I) {η η' : ℝ → ℝ} {x y : ℝ} (hx : x ∈ closure (I : Set ℝ))
    (hy : y ∈ closure (I : Set ℝ)) (hη : AbsolutelyContinuousOnInterval η x y)
    (hη' : ∀ᵐ t, t ∈ (I : Set ℝ) → _root_.deriv η t = η' t) :
    ∫ t in x..y, (η' t * rep u t + η t * deriv u 1 t) = η y * rep u y - η x * rep u x := by
  rw [← hη.integral_deriv_mul_eq_sub (absolutelyContinuousOnInterval_rep hI u hx hy)]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_uIoc_of_ae_restrict hI ((ae_restrict_iff' I.isOpen.measurableSet).2 hη')
    hx hy, ae_uIoc_of_ae_restrict hI ((ae_restrict_iff' I.isOpen.measurableSet).2
    (ae_deriv_rep_eq hI u)) hx hy] with t h1 h2 ht
  rw [h1 ht, h2 ht]

end SobolevIntervalLp

/-! ### The Lipschitz cut-off -/

namespace SobolevIntervalLp

variable {a b : ℝ}

/-- The Lipschitz cut-off of the bounded interval `(a, b)`: `1` on `(-∞, a]`, affine from `1`
at `a` to `0` at `b`, and `0` on `[b, ∞)`; its derivative on `(a, b)` is `-1/(b - a)`. The
function `η` of the proof of [brezis2011functional] Theorem 8.6, made Lipschitz rather than
`C¹` so that `‖η'‖_∞ = 1/|I|` exactly. -/
def cutoffFun (a b : ℝ) (x : ℝ) : ℝ := min 1 (max 0 ((b - x) / (b - a)))

/-- The cut-off is `1` to the left of `a`. -/
theorem cutoffFun_of_le (hab : a < b) {x : ℝ} (hx : x ≤ a) : cutoffFun a b x = 1 := by
  have h1 : 1 ≤ (b - x) / (b - a) := by
    rw [le_div_iff₀ (sub_pos.2 hab)]; linarith
  rw [cutoffFun, max_eq_right (zero_le_one.trans h1), min_eq_left h1]

/-- The cut-off is affine on `[a, b]`. -/
theorem cutoffFun_of_mem (hab : a < b) {x : ℝ} (hx : x ∈ Icc a b) :
    cutoffFun a b x = (b - x) / (b - a) := by
  have h0 : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.2 hx.2) (sub_pos.2 hab).le
  have h1 : (b - x) / (b - a) ≤ 1 := by
    rw [div_le_iff₀ (sub_pos.2 hab)]; linarith [hx.1]
  rw [cutoffFun, max_eq_right h0, min_eq_right h1]

/-- The cut-off vanishes to the right of `b`. -/
theorem cutoffFun_of_le' (hab : a < b) {x : ℝ} (hx : b ≤ x) : cutoffFun a b x = 0 := by
  have h0 : (b - x) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [cutoffFun, max_eq_left h0, min_eq_right zero_le_one]

/-- The cut-off is nonnegative. -/
theorem cutoffFun_nonneg (x : ℝ) : 0 ≤ cutoffFun a b x :=
  le_min zero_le_one (le_max_left _ _)

/-- The cut-off is at most one. -/
theorem cutoffFun_le_one (x : ℝ) : cutoffFun a b x ≤ 1 := min_le_left _ _

/-- The cut-off is continuous. -/
theorem continuous_cutoffFun : Continuous (cutoffFun a b) := by
  unfold cutoffFun; fun_prop

/-- The cut-off is Lipschitz with constant `1/(b - a)`. -/
theorem lipschitzWith_cutoffFun (hab : a < b) :
    LipschitzWith ⟨(b - a)⁻¹, by positivity⟩ (cutoffFun a b) := by
  refine LipschitzWith.const_min (LipschitzWith.const_max ?_ 0) 1
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq, Real.dist_eq]
  change |(b - x) / (b - a) - (b - y) / (b - a)| ≤ (b - a)⁻¹ * |x - y|
  rw [← sub_div, abs_div, abs_of_pos (sub_pos.2 hab), show b - x - (b - y) = -(x - y) by ring,
    abs_neg, div_eq_inv_mul]

/-- The cut-off is absolutely continuous between any two points. -/
theorem absolutelyContinuousOnInterval_cutoffFun (hab : a < b) (x y : ℝ) :
    AbsolutelyContinuousOnInterval (cutoffFun a b) x y :=
  (lipschitzWith_cutoffFun hab).lipschitzOnWith.absolutelyContinuousOnInterval

/-- The derivative of the cut-off on `(a, b)` is `-1/(b - a)`. -/
theorem hasDerivAt_cutoffFun (hab : a < b) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (cutoffFun a b) (-(b - a)⁻¹) x := by
  have h : HasDerivAt (fun t ↦ (b - t) / (b - a)) (-1 / (b - a)) x :=
    ((hasDerivAt_id x).const_sub b).div_const (b - a)
  rw [neg_div, one_div] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  exact cutoffFun_of_mem hab (Ioo_subset_Icc_self ht)

/-- The derivative of the cut-off on `(a, b)` is `-1/(b - a)`. -/
theorem deriv_cutoffFun (hab : a < b) {x : ℝ} (hx : x ∈ Ioo a b) :
    _root_.deriv (cutoffFun a b) x = -(b - a)⁻¹ :=
  (hasDerivAt_cutoffFun hab hx).deriv

/-- The derivative of the complementary cut-off `1 - η` on `(a, b)` is `1/(b - a)`. -/
theorem deriv_one_sub_cutoffFun (hab : a < b) {x : ℝ} (hx : x ∈ Ioo a b) :
    _root_.deriv (fun t ↦ 1 - cutoffFun a b t) x = (b - a)⁻¹ := by
  rw [((hasDerivAt_cutoffFun hab hx).const_sub 1).deriv, neg_neg]

/-- The complementary cut-off `1 - η` is absolutely continuous between any two points. -/
theorem absolutelyContinuousOnInterval_one_sub_cutoffFun (hab : a < b) (x y : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ 1 - cutoffFun a b t) x y :=
  (contDiffOn_const (c := (1 : ℝ))).absolutelyContinuousOnInterval.sub
    (absolutelyContinuousOnInterval_cutoffFun hab x y)

end SobolevIntervalLp


/-! ### Theorem 8.6 on a bounded interval: the piece `η u` extended by zero to `(a, ∞)` -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {a b : ℝ}

/-- From a bound `eLpNorm f ≤ ‖x‖ₑ + k ‖y‖ₑ` in `ℝ≥0∞`, the real bound
`(eLpNorm f).toReal ≤ ‖x‖ + k ‖y‖`. -/
theorem toReal_eLpNorm_le_of_le_add {μ : Measure ℝ} {f : ℝ → ℝ} {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {x : E} {y : F} {k : ℝ} (hk : 0 ≤ k)
    (h : eLpNorm f p μ ≤ ‖x‖ₑ + ENNReal.ofReal k * ‖y‖ₑ) :
    (eLpNorm f p μ).toReal ≤ ‖x‖ + k * ‖y‖ := by
  have hfin : ENNReal.ofReal k * ‖y‖ₑ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨enorm_ne_top, hfin⟩) h).trans_eq ?_
  rw [ENNReal.toReal_add enorm_ne_top hfin, ENNReal.toReal_mul, ENNReal.toReal_ofReal hk,
    toReal_enorm, toReal_enorm]

/-- The bounded interval `(a, b)` is an interval. -/
theorem ordConnected_coe_Ioo (a b : ℝ) : ((Opens.Ioo a b : Opens ℝ) : Set ℝ).OrdConnected :=
  ordConnected_Ioo

/-- The closure of the bounded interval `(a, b)`, `a < b`, is `[a, b]`. -/
theorem closure_coe_Ioo (hab : a < b) : closure ((Opens.Ioo a b : Opens ℝ) : Set ℝ) = Icc a b := by
  rw [Opens.coe_Ioo, closure_Ioo hab.ne]

variable [Fact (1 ≤ p)]

/-- The continuous representative of `u ∈ W^{1,p}(a, b)` is continuous on `[a, b]`. -/
theorem continuousOn_rep_Icc (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ContinuousOn (rep u) (Icc a b) := by
  have := continuousOn_rep (ordConnected_coe_Ioo a b) u
  rwa [closure_coe_Ioo hab] at this

/-- The fundamental theorem of calculus in `W^{1,p}(a, b)`, on `[a, b]`. -/
theorem rep_sub_rep_Ioo (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : rep u y - rep u x = ∫ t in x..y, deriv u 1 t :=
  rep_sub_rep (ordConnected_coe_Ioo a b) u (by rw [closure_coe_Ioo hab]; exact hx)
    (by rw [closure_coe_Ioo hab]; exact hy)

/-- The continuous representative of a sum, on `[a, b]`. -/
theorem rep_add_Icc (hab : a < b) (u v : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : x ∈ Icc a b) : rep (u + v) x = rep u x + rep v x :=
  rep_add (ordConnected_coe_Ioo a b) u v (by rw [closure_coe_Ioo hab]; exact hx)

/-- The continuous representative of a scalar multiple, on `[a, b]`. -/
theorem rep_smul_Icc (hab : a < b) (r : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : x ∈ Icc a b) : rep (r • u) x = r * rep u x :=
  rep_smul (ordConnected_coe_Ioo a b) r u (by rw [closure_coe_Ioo hab]; exact hx)

/-- The first piece of the extension of `u ∈ W^{1,p}(a, b)`: the product `η ũ` of the cut-off
with the continuous representative, extended by zero to `(a, ∞)` (the cut-off vanishes on
`[b, ∞)`; the argument is clamped to `b` so that only values of `ũ` on `[a, b]` occur). -/
def cutoffIoiFun (a b : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) (x : ℝ) : ℝ :=
  cutoffFun a b x * rep u (min x b)

/-- The weak derivative of `cutoffIoiFun`: `η' ũ + η u'` on `(a, b)`, that is
`-(b - a)⁻¹ ũ + η u'`, and `0` elsewhere. -/
def cutoffIoiDeriv (a b : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) (x : ℝ) : ℝ :=
  (Ioo a b).indicator (fun t ↦ -(b - a)⁻¹ * rep u t + cutoffFun a b t * deriv u 1 t) x

omit [Fact (1 ≤ p)] in
/-- On `(a, b)`, `cutoffIoiFun` is `η ũ`. -/
theorem cutoffIoiFun_of_mem (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : x ∈ Ioo a b) : cutoffIoiFun a b u x = cutoffFun a b x * rep u x := by
  rw [cutoffIoiFun, min_eq_left hx.2.le]

omit [Fact (1 ≤ p)] in
/-- On `[b, ∞)`, `cutoffIoiFun` vanishes. -/
theorem cutoffIoiFun_of_le (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : b ≤ x) : cutoffIoiFun a b u x = 0 := by
  rw [cutoffIoiFun, cutoffFun_of_le' hab hx, zero_mul]

/-- `cutoffIoiFun` is continuous on `[a, ∞)`. -/
theorem continuousOn_cutoffIoiFun (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ContinuousOn (cutoffIoiFun a b u) (Ici a) := by
  refine continuous_cutoffFun.continuousOn.mul ?_
  refine (continuousOn_rep_Icc hab u).comp (continuous_id.min continuous_const).continuousOn
    fun x hx ↦ ?_
  exact ⟨le_min hx hab.le, min_le_right _ _⟩

/-- `‖η ũ‖_{L^p(a, ∞)} ≤ ‖u‖_{L^p(a, b)}`. -/
theorem eLpNorm_cutoffIoiFun_le (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    eLpNorm (cutoffIoiFun a b u) p (volume.restrict (Ioi a)) ≤ ‖deriv u 0‖ₑ := by
  have hmeas : AEStronglyMeasurable (cutoffIoiFun a b u) (volume.restrict (Ioo a b)) :=
    ((continuousOn_cutoffIoiFun hab u).mono
      (Ioo_subset_Icc_self.trans Icc_subset_Ici_self)).aestronglyMeasurable measurableSet_Ioo
  calc eLpNorm (cutoffIoiFun a b u) p (volume.restrict (Ioi a))
      = eLpNorm ((Ioo a b).indicator (cutoffIoiFun a b u)) p (volume.restrict (Ioi a)) := by
        refine eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
          (Eventually.of_forall fun x hx ↦ ?_))
        by_cases hxb : x < b
        · have hmem : x ∈ Ioo a b := ⟨hx, hxb⟩
          rw [indicator_of_mem hmem]
        · rw [indicator_of_notMem (fun h ↦ hxb h.2), cutoffIoiFun_of_le hab u (not_lt.1 hxb)]
    _ = eLpNorm (cutoffIoiFun a b u) p (volume.restrict (Ioo a b)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo,
          Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Ioi_self]
    _ ≤ eLpNorm (rep u) p (volume.restrict (Ioo a b)) := by
        refine eLpNorm_mono_ae hmeas ((ae_restrict_iff' measurableSet_Ioo).2
          (Eventually.of_forall fun x hx ↦ ?_))
        rw [cutoffIoiFun_of_mem u hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (cutoffFun_nonneg x)]
        exact mul_le_of_le_one_left (abs_nonneg _) (cutoffFun_le_one x)
    _ = ‖deriv u 0‖ₑ := by
        rw [Lp.enorm_def, deriv_zero, eLpNorm_congr_ae (fn_ae_eq_rep (ordConnected_coe_Ioo a b) u)]
        rfl

/-- `‖(η ũ)'‖_{L^p(a, ∞)} ≤ ‖u'‖_{L^p(a, b)} + (b - a)⁻¹ ‖u‖_{L^p(a, b)}`. -/
theorem eLpNorm_cutoffIoiDeriv_le (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    eLpNorm (cutoffIoiDeriv a b u) p (volume.restrict (Ioi a))
      ≤ ‖deriv u 1‖ₑ + ENNReal.ofReal (b - a)⁻¹ * ‖deriv u 0‖ₑ := by
  have hmeas : AEStronglyMeasurable (fun t ↦ cutoffFun a b t * deriv u 1 t)
      (volume.restrict (Ioo a b)) :=
    continuous_cutoffFun.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
  calc eLpNorm (cutoffIoiDeriv a b u) p (volume.restrict (Ioi a))
      = eLpNorm (fun t ↦ -(b - a)⁻¹ * rep u t + cutoffFun a b t * deriv u 1 t) p
          (volume.restrict (Ioo a b)) := by
        have e : cutoffIoiDeriv a b u = (Ioo a b).indicator
            (fun t ↦ -(b - a)⁻¹ * rep u t + cutoffFun a b t * deriv u 1 t) := rfl
        rw [e, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo,
          Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Ioi_self]
    _ ≤ eLpNorm (fun t ↦ -(b - a)⁻¹ * rep u t) p (volume.restrict (Ioo a b))
          + eLpNorm (fun t ↦ cutoffFun a b t * deriv u 1 t) p (volume.restrict (Ioo a b)) :=
        eLpNorm_add_le Fact.out
    _ ≤ ENNReal.ofReal (b - a)⁻¹ * eLpNorm (rep u) p (volume.restrict (Ioo a b))
          + eLpNorm (deriv u 1) p (volume.restrict (Ioo a b)) := by
        gcongr
        · rw [show (fun t ↦ -(b - a)⁻¹ * rep u t) = (-(b - a)⁻¹) • rep u from rfl,
            eLpNorm_const_smul, enorm_neg, Real.enorm_eq_ofReal (by positivity)]
        · refine eLpNorm_mono_ae hmeas (Eventually.of_forall fun t ↦ ?_)
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutoffFun_nonneg t)]
          exact mul_le_of_le_one_left (abs_nonneg _) (cutoffFun_le_one t)
    _ = ‖deriv u 1‖ₑ + ENNReal.ofReal (b - a)⁻¹ * ‖deriv u 0‖ₑ := by
        rw [Lp.enorm_def, Lp.enorm_def, deriv_zero,
          eLpNorm_congr_ae (fn_ae_eq_rep (ordConnected_coe_Ioo a b) u), add_comm]
        rfl

/-- `η ũ` lies in `L^p(a, ∞)`. -/
theorem memLp_cutoffIoiFun (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    MemLp (cutoffIoiFun a b u) p (volume.restrict (Opens.Ioi a : Set ℝ)) :=
  memLp_iff.2 ((eLpNorm_cutoffIoiFun_le hab u).trans_lt enorm_lt_top)

/-- `(η ũ)'` lies in `L^p(a, ∞)`. -/
theorem memLp_cutoffIoiDeriv (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    MemLp (cutoffIoiDeriv a b u) p (volume.restrict (Opens.Ioi a : Set ℝ)) :=
  memLp_iff.2 ((eLpNorm_cutoffIoiDeriv_le hab u).trans_lt (ENNReal.add_lt_top.2
    ⟨enorm_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top⟩))

/-- **`η ũ` is the primitive of `η' ũ + η u'` from `b`, on `(a, ∞)`**: on `[b, ∞)` both sides
vanish, and on `(a, b)` this is integration by parts for the Lipschitz cut-off against the
absolutely continuous representative (`SobolevIntervalLp.integral_deriv_mul_rep_add_mul_deriv`). -/
theorem cutoffIoiFun_eq_integral (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : a < x) : cutoffIoiFun a b u x = ∫ t in b..x, cutoffIoiDeriv a b u t := by
  rcases le_or_gt b x with hbx | hxb
  · rw [cutoffIoiFun_of_le hab u hbx]
    have h0 : ∀ t ∈ uIcc b x, cutoffIoiDeriv a b u t = 0 := fun t ht ↦ by
      rw [uIcc_of_le hbx] at ht
      exact indicator_of_notMem (fun h ↦ h.2.not_ge ht.1) _
    rw [intervalIntegral.integral_congr h0, intervalIntegral.integral_zero]
  · have hxI : x ∈ Icc a b := ⟨hx.le, hxb.le⟩
    rw [cutoffIoiFun_of_mem u ⟨hx, hxb⟩, intervalIntegral.integral_symm]
    have key := integral_deriv_mul_rep_add_mul_deriv (ordConnected_coe_Ioo a b) u
      (η := cutoffFun a b) (η' := fun _ ↦ -(b - a)⁻¹)
      (by rw [closure_coe_Ioo hab]; exact hxI)
      (by rw [closure_coe_Ioo hab]; exact right_mem_Icc.2 hab.le)
      (absolutelyContinuousOnInterval_cutoffFun hab x b)
      (Eventually.of_forall fun t ht ↦ deriv_cutoffFun hab ht)
    rw [cutoffFun_of_le' hab le_rfl, zero_mul, zero_sub] at key
    have e : ∫ t in x..b, cutoffIoiDeriv a b u t
        = ∫ t in x..b, (-(b - a)⁻¹ * rep u t + cutoffFun a b t * deriv u 1 t) := by
      refine intervalIntegral.integral_congr_ae ?_
      have hne : ∀ᵐ t : ℝ, t ≠ b := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with t htb ht
      rw [uIoc_of_le hxb.le] at ht
      exact indicator_of_mem (show t ∈ Ioo a b from ⟨hx.trans ht.1, lt_of_le_of_ne ht.2 htb⟩) _
    rw [e, key, neg_neg]

/-- **The first piece has the weak derivative `η' ũ + η u'` on `(a, ∞)`**: Lemma 8.2 applied
to the integral representation `cutoffIoiFun_eq_integral`. -/
theorem hasWeakDerivOn_cutoffIoiFun (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    HasWeakDerivOn (cutoffIoiFun a b u) (cutoffIoiDeriv a b u) (Opens.Ioi a) := by
  have h0 := ((memLp_cutoffIoiDeriv hab u).locallyIntegrableOn Fact.out).hasWeakDerivOn_integral
    (ordConnected_coe_Ioi a) (y₀ := b) (show b ∈ Set.Ioi a from hab) 0
  refine h0.congr_ae ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun x hx ↦ ?_)) (EventuallyEq.refl _ _)
  change 0 + ∫ t in b..x, cutoffIoiDeriv a b u t = cutoffIoiFun a b u x
  rw [zero_add]
  exact (cutoffIoiFun_eq_integral hab u hx).symm

/-- `cutoffIoiFun` is additive, on `[a, ∞)`. -/
theorem cutoffIoiFun_add (hab : a < b) (u v : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : a ≤ x) : cutoffIoiFun a b (u + v) x = cutoffIoiFun a b u x + cutoffIoiFun a b v x := by
  simp only [cutoffIoiFun]
  rw [rep_add_Icc hab u v ⟨le_min hx hab.le, min_le_right _ _⟩, mul_add]

/-- `cutoffIoiFun` is homogeneous, on `[a, ∞)`. -/
theorem cutoffIoiFun_smul (hab : a < b) (r : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : a ≤ x) : cutoffIoiFun a b (r • u) x = r * cutoffIoiFun a b u x := by
  simp only [cutoffIoiFun]
  rw [rep_smul_Icc hab r u ⟨le_min hx hab.le, min_le_right _ _⟩]
  ring

/-- `cutoffIoiDeriv` is additive, almost everywhere. -/
theorem cutoffIoiDeriv_add (hab : a < b) (u v : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    cutoffIoiDeriv a b (u + v) =ᵐ[volume] cutoffIoiDeriv a b u + cutoffIoiDeriv a b v := by
  have h1 : ∀ᵐ t : ℝ, t ∈ Ioo a b → (deriv (u + v) 1 : ℝ → ℝ) t = deriv u 1 t + deriv v 1 t := by
    rw [deriv_add]
    exact (ae_restrict_iff' measurableSet_Ioo).1 (Lp.coeFn_add _ _)
  filter_upwards [h1] with t ht
  simp only [cutoffIoiDeriv, Pi.add_apply]
  by_cases htI : t ∈ Ioo a b
  · simp only [indicator_of_mem htI]
    rw [ht htI, rep_add_Icc hab u v (Ioo_subset_Icc_self htI)]
    ring
  · simp only [indicator_of_notMem htI, add_zero]

/-- `cutoffIoiDeriv` is homogeneous, almost everywhere. -/
theorem cutoffIoiDeriv_smul (hab : a < b) (r : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    cutoffIoiDeriv a b (r • u) =ᵐ[volume] r • cutoffIoiDeriv a b u := by
  have h1 : ∀ᵐ t : ℝ, t ∈ Ioo a b → (deriv (r • u) 1 : ℝ → ℝ) t = r * deriv u 1 t := by
    rw [deriv_smul]
    exact (ae_restrict_iff' measurableSet_Ioo).1 (Lp.coeFn_smul _ _)
  filter_upwards [h1] with t ht
  simp only [cutoffIoiDeriv, Pi.smul_apply, smul_eq_mul]
  by_cases htI : t ∈ Ioo a b
  · simp only [indicator_of_mem htI]
    rw [ht htI, rep_smul_Icc hab r u (Ioo_subset_Icc_self htI)]
    ring
  · simp only [indicator_of_notMem htI, mul_zero]

/-- The first piece of the extension, `u ↦ η ũ` extended by zero to `(a, ∞)`, as
`SobolevIntervalLp.MapData`. -/
def cutoffIoiData (hab : a < b) : MapData p (Opens.Ioo a b) (Opens.Ioi a) where
  F := cutoffIoiFun a b
  W := cutoffIoiDeriv a b
  memLp_F u := memLp_cutoffIoiFun hab u
  memLp_W u := memLp_cutoffIoiDeriv hab u
  hasWeakDerivOn u := hasWeakDerivOn_cutoffIoiFun hab u
  F_add u v := (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun _ hx ↦
    cutoffIoiFun_add hab u v (le_of_lt hx))
  F_smul r u := (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun _ hx ↦
    cutoffIoiFun_smul hab r u (le_of_lt hx))
  W_add u v := ae_restrict_of_ae (cutoffIoiDeriv_add hab u v)
  W_smul r u := ae_restrict_of_ae (cutoffIoiDeriv_smul hab r u)

/-- **The first piece of the extension operator, `W^{1,p}(a, b) → W^{1,p}(a, ∞)`**: `u ↦ η ũ`
extended by zero, a continuous linear map of norm at most `2 + (b - a)⁻¹`. -/
def cutoffIoiCLM (hab : a < b) :
    SobolevIntervalLp 1 p (Opens.Ioo a b) →L[ℝ] SobolevIntervalLp 1 p (Opens.Ioi a) :=
  (cutoffIoiData hab).toCLM (2 + (b - a)⁻¹) fun u ↦ by
    have h0 := (ENNReal.toReal_mono enorm_ne_top (eLpNorm_cutoffIoiFun_le hab u)).trans_eq
      (toReal_enorm _)
    have h1 := toReal_eLpNorm_le_of_le_add (by positivity) (eLpNorm_cutoffIoiDeriv_le hab u)
    have h2 := norm_deriv_le u 0
    have h3 := norm_deriv_le u 1
    have h4 : 0 ≤ (b - a)⁻¹ := by positivity
    change (eLpNorm (cutoffIoiFun a b u) p (volume.restrict (Ioi a))).toReal
      + (eLpNorm (cutoffIoiDeriv a b u) p (volume.restrict (Ioi a))).toReal ≤ _
    nlinarith

/-- The function of the first piece is `η ũ` on `(a, ∞)`. -/
theorem fn_cutoffIoiCLM (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    fn (cutoffIoiCLM hab u) =ᵐ[volume.restrict (Opens.Ioi a : Set ℝ)] cutoffIoiFun a b u :=
  (cutoffIoiData hab).fn_map u

/-- `‖η ũ‖_{L^p(a, ∞)} ≤ ‖u‖_{L^p(a, b)}`. -/
theorem norm_deriv_cutoffIoiCLM_zero (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖deriv (cutoffIoiCLM hab u) 0‖ ≤ ‖deriv u 0‖ := by
  rw [cutoffIoiCLM, MapData.toCLM_apply, MapData.norm_deriv_map_zero]
  exact (ENNReal.toReal_mono enorm_ne_top (eLpNorm_cutoffIoiFun_le hab u)).trans_eq
    (toReal_enorm _)

/-- `‖(η ũ)'‖_{L^p(a, ∞)} ≤ ‖u'‖_{L^p(a, b)} + (b - a)⁻¹ ‖u‖_{L^p(a, b)}`. -/
theorem norm_deriv_cutoffIoiCLM_one (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖deriv (cutoffIoiCLM hab u) 1‖ ≤ ‖deriv u 1‖ + (b - a)⁻¹ * ‖deriv u 0‖ := by
  rw [cutoffIoiCLM, MapData.toCLM_apply, MapData.norm_deriv_map_one]
  exact toReal_eLpNorm_le_of_le_add (by positivity) (eLpNorm_cutoffIoiDeriv_le hab u)

end SobolevIntervalLp


/-! ### Theorem 8.6 on a bounded interval: the piece `(1 - η) u` extended by zero to `(-∞, b)` -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} {a b : ℝ}

/-- The second piece of the extension of `u ∈ W^{1,p}(a, b)`: the product `(1 - η) ũ` of the
complementary cut-off with the continuous representative, extended by zero to `(-∞, b)` (the
argument is clamped to `a` so that only values of `ũ` on `[a, b]` occur). -/
def cutoffIioFun (a b : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) (x : ℝ) : ℝ :=
  (1 - cutoffFun a b x) * rep u (max x a)

/-- The weak derivative of `cutoffIioFun`: `(b - a)⁻¹ ũ + (1 - η) u'` on `(a, b)` and `0`
elsewhere. -/
def cutoffIioDeriv (a b : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) (x : ℝ) : ℝ :=
  (Ioo a b).indicator (fun t ↦ (b - a)⁻¹ * rep u t + (1 - cutoffFun a b t) * deriv u 1 t) x

/-- On `(a, b)`, `cutoffIioFun` is `(1 - η) ũ`. -/
theorem cutoffIioFun_of_mem (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : x ∈ Ioo a b) : cutoffIioFun a b u x = (1 - cutoffFun a b x) * rep u x := by
  rw [cutoffIioFun, max_eq_left hx.1.le]

/-- On `(-∞, a]`, `cutoffIioFun` vanishes. -/
theorem cutoffIioFun_of_le (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : x ≤ a) : cutoffIioFun a b u x = 0 := by
  rw [cutoffIioFun, cutoffFun_of_le hab hx, sub_self, zero_mul]

variable [Fact (1 ≤ p)]

/-- `cutoffIioFun` is continuous on `(-∞, b]`. -/
theorem continuousOn_cutoffIioFun (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ContinuousOn (cutoffIioFun a b u) (Iic b) := by
  refine (continuous_const.sub continuous_cutoffFun).continuousOn.mul ?_
  refine (continuousOn_rep_Icc hab u).comp (continuous_id.max continuous_const).continuousOn
    fun x hx ↦ ?_
  exact ⟨le_max_right _ _, max_le hx hab.le⟩

/-- `‖(1 - η) ũ‖_{L^p(-∞, b)} ≤ ‖u‖_{L^p(a, b)}`. -/
theorem eLpNorm_cutoffIioFun_le (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    eLpNorm (cutoffIioFun a b u) p (volume.restrict (Iio b)) ≤ ‖deriv u 0‖ₑ := by
  have hmeas : AEStronglyMeasurable (cutoffIioFun a b u) (volume.restrict (Ioo a b)) :=
    ((continuousOn_cutoffIioFun hab u).mono
      (Ioo_subset_Icc_self.trans Icc_subset_Iic_self)).aestronglyMeasurable measurableSet_Ioo
  have h01 : ∀ x, 0 ≤ 1 - cutoffFun a b x := fun x ↦ sub_nonneg.2 (cutoffFun_le_one x)
  have h11 : ∀ x, 1 - cutoffFun a b x ≤ 1 := fun x ↦ by
    linarith [cutoffFun_nonneg (a := a) (b := b) x]
  calc eLpNorm (cutoffIioFun a b u) p (volume.restrict (Iio b))
      = eLpNorm ((Ioo a b).indicator (cutoffIioFun a b u)) p (volume.restrict (Iio b)) := by
        refine eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_Iio).2
          (Eventually.of_forall fun x hx ↦ ?_))
        by_cases hxa : a < x
        · have hmem : x ∈ Ioo a b := ⟨hxa, hx⟩
          rw [indicator_of_mem hmem]
        · rw [indicator_of_notMem (fun h ↦ hxa h.1), cutoffIioFun_of_le hab u (not_lt.1 hxa)]
    _ = eLpNorm (cutoffIioFun a b u) p (volume.restrict (Ioo a b)) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo,
          Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Iio_self]
    _ ≤ eLpNorm (rep u) p (volume.restrict (Ioo a b)) := by
        refine eLpNorm_mono_ae hmeas ((ae_restrict_iff' measurableSet_Ioo).2
          (Eventually.of_forall fun x hx ↦ ?_))
        rw [cutoffIioFun_of_mem u hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (h01 x)]
        exact mul_le_of_le_one_left (abs_nonneg _) (h11 x)
    _ = ‖deriv u 0‖ₑ := by
        rw [Lp.enorm_def, deriv_zero, eLpNorm_congr_ae (fn_ae_eq_rep (ordConnected_coe_Ioo a b) u)]
        rfl

/-- `‖((1 - η) ũ)'‖_{L^p(-∞, b)} ≤ ‖u'‖_{L^p(a, b)} + (b - a)⁻¹ ‖u‖_{L^p(a, b)}`. -/
theorem eLpNorm_cutoffIioDeriv_le (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    eLpNorm (cutoffIioDeriv a b u) p (volume.restrict (Iio b))
      ≤ ‖deriv u 1‖ₑ + ENNReal.ofReal (b - a)⁻¹ * ‖deriv u 0‖ₑ := by
  have hmeas : AEStronglyMeasurable (fun t ↦ (1 - cutoffFun a b t) * deriv u 1 t)
      (volume.restrict (Ioo a b)) :=
    (continuous_const.sub continuous_cutoffFun).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable _)
  have h01 : ∀ x, 0 ≤ 1 - cutoffFun a b x := fun x ↦ sub_nonneg.2 (cutoffFun_le_one x)
  have h11 : ∀ x, 1 - cutoffFun a b x ≤ 1 := fun x ↦ by
    linarith [cutoffFun_nonneg (a := a) (b := b) x]
  calc eLpNorm (cutoffIioDeriv a b u) p (volume.restrict (Iio b))
      = eLpNorm (fun t ↦ (b - a)⁻¹ * rep u t + (1 - cutoffFun a b t) * deriv u 1 t) p
          (volume.restrict (Ioo a b)) := by
        have e : cutoffIioDeriv a b u = (Ioo a b).indicator
            (fun t ↦ (b - a)⁻¹ * rep u t + (1 - cutoffFun a b t) * deriv u 1 t) := rfl
        rw [e, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioo,
          Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Iio_self]
    _ ≤ eLpNorm (fun t ↦ (b - a)⁻¹ * rep u t) p (volume.restrict (Ioo a b))
          + eLpNorm (fun t ↦ (1 - cutoffFun a b t) * deriv u 1 t) p (volume.restrict (Ioo a b)) :=
        eLpNorm_add_le Fact.out
    _ ≤ ENNReal.ofReal (b - a)⁻¹ * eLpNorm (rep u) p (volume.restrict (Ioo a b))
          + eLpNorm (deriv u 1) p (volume.restrict (Ioo a b)) := by
        gcongr
        · rw [show (fun t ↦ (b - a)⁻¹ * rep u t) = (b - a)⁻¹ • rep u from rfl,
            eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
        · refine eLpNorm_mono_ae hmeas (Eventually.of_forall fun t ↦ ?_)
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (h01 t)]
          exact mul_le_of_le_one_left (abs_nonneg _) (h11 t)
    _ = ‖deriv u 1‖ₑ + ENNReal.ofReal (b - a)⁻¹ * ‖deriv u 0‖ₑ := by
        rw [Lp.enorm_def, Lp.enorm_def, deriv_zero,
          eLpNorm_congr_ae (fn_ae_eq_rep (ordConnected_coe_Ioo a b) u), add_comm]
        rfl

/-- `(1 - η) ũ` lies in `L^p(-∞, b)`. -/
theorem memLp_cutoffIioFun (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    MemLp (cutoffIioFun a b u) p (volume.restrict (Opens.Iio b : Set ℝ)) :=
  memLp_iff.2 ((eLpNorm_cutoffIioFun_le hab u).trans_lt enorm_lt_top)

/-- `((1 - η) ũ)'` lies in `L^p(-∞, b)`. -/
theorem memLp_cutoffIioDeriv (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    MemLp (cutoffIioDeriv a b u) p (volume.restrict (Opens.Iio b : Set ℝ)) :=
  memLp_iff.2 ((eLpNorm_cutoffIioDeriv_le hab u).trans_lt (ENNReal.add_lt_top.2
    ⟨enorm_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top enorm_lt_top⟩))

/-- **`(1 - η) ũ` is the primitive of `(1 - η)' ũ + (1 - η) u'` from `a`, on `(-∞, b)`**. -/
theorem cutoffIioFun_eq_integral (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : x < b) : cutoffIioFun a b u x = ∫ t in a..x, cutoffIioDeriv a b u t := by
  rcases le_or_gt x a with hxa | hax
  · rw [cutoffIioFun_of_le hab u hxa]
    have h0 : ∀ t ∈ uIcc a x, cutoffIioDeriv a b u t = 0 := fun t ht ↦ by
      rw [uIcc_of_ge hxa] at ht
      exact indicator_of_notMem (fun h ↦ h.1.not_ge ht.2) _
    rw [intervalIntegral.integral_congr h0, intervalIntegral.integral_zero]
  · have hxI : x ∈ Icc a b := ⟨hax.le, hx.le⟩
    rw [cutoffIioFun_of_mem u ⟨hax, hx⟩]
    have key := integral_deriv_mul_rep_add_mul_deriv (ordConnected_coe_Ioo a b) u
      (η := fun t ↦ 1 - cutoffFun a b t) (η' := fun _ ↦ (b - a)⁻¹)
      (by rw [closure_coe_Ioo hab]; exact left_mem_Icc.2 hab.le)
      (by rw [closure_coe_Ioo hab]; exact hxI)
      (absolutelyContinuousOnInterval_one_sub_cutoffFun hab a x)
      (Eventually.of_forall fun t ht ↦ deriv_one_sub_cutoffFun hab ht)
    rw [cutoffFun_of_le hab le_rfl, sub_self, zero_mul, sub_zero] at key
    have e : ∫ t in a..x, cutoffIioDeriv a b u t
        = ∫ t in a..x, ((b - a)⁻¹ * rep u t + (1 - cutoffFun a b t) * deriv u 1 t) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
      rw [uIoc_of_le hax.le] at ht
      exact indicator_of_mem (show t ∈ Ioo a b from ⟨ht.1, ht.2.trans_lt hx⟩) _
    rw [e, key]

/-- **The second piece has the weak derivative `(1 - η)' ũ + (1 - η) u'` on `(-∞, b)`**. -/
theorem hasWeakDerivOn_cutoffIioFun (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    HasWeakDerivOn (cutoffIioFun a b u) (cutoffIioDeriv a b u) (Opens.Iio b) := by
  have h0 := ((memLp_cutoffIioDeriv hab u).locallyIntegrableOn Fact.out).hasWeakDerivOn_integral
    (ordConnected_coe_Iio b) (y₀ := a) (show a ∈ Set.Iio b from hab) 0
  refine h0.congr_ae ((ae_restrict_iff' measurableSet_Iio).2
    (Eventually.of_forall fun x hx ↦ ?_)) (EventuallyEq.refl _ _)
  change 0 + ∫ t in a..x, cutoffIioDeriv a b u t = cutoffIioFun a b u x
  rw [zero_add]
  exact (cutoffIioFun_eq_integral hab u hx).symm

/-- `cutoffIioFun` is additive, on `(-∞, b]`. -/
theorem cutoffIioFun_add (hab : a < b) (u v : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : x ≤ b) : cutoffIioFun a b (u + v) x = cutoffIioFun a b u x + cutoffIioFun a b v x := by
  simp only [cutoffIioFun]
  rw [rep_add_Icc hab u v ⟨le_max_right _ _, max_le hx hab.le⟩, mul_add]

/-- `cutoffIioFun` is homogeneous, on `(-∞, b]`. -/
theorem cutoffIioFun_smul (hab : a < b) (r : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) {x : ℝ}
    (hx : x ≤ b) : cutoffIioFun a b (r • u) x = r * cutoffIioFun a b u x := by
  simp only [cutoffIioFun]
  rw [rep_smul_Icc hab r u ⟨le_max_right _ _, max_le hx hab.le⟩]
  ring

/-- `cutoffIioDeriv` is additive, almost everywhere. -/
theorem cutoffIioDeriv_add (hab : a < b) (u v : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    cutoffIioDeriv a b (u + v) =ᵐ[volume] cutoffIioDeriv a b u + cutoffIioDeriv a b v := by
  have h1 : ∀ᵐ t : ℝ, t ∈ Ioo a b → (deriv (u + v) 1 : ℝ → ℝ) t = deriv u 1 t + deriv v 1 t := by
    rw [deriv_add]
    exact (ae_restrict_iff' measurableSet_Ioo).1 (Lp.coeFn_add _ _)
  filter_upwards [h1] with t ht
  simp only [cutoffIioDeriv, Pi.add_apply]
  by_cases htI : t ∈ Ioo a b
  · simp only [indicator_of_mem htI]
    rw [ht htI, rep_add_Icc hab u v (Ioo_subset_Icc_self htI)]
    ring
  · simp only [indicator_of_notMem htI, add_zero]

/-- `cutoffIioDeriv` is homogeneous, almost everywhere. -/
theorem cutoffIioDeriv_smul (hab : a < b) (r : ℝ) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    cutoffIioDeriv a b (r • u) =ᵐ[volume] r • cutoffIioDeriv a b u := by
  have h1 : ∀ᵐ t : ℝ, t ∈ Ioo a b → (deriv (r • u) 1 : ℝ → ℝ) t = r * deriv u 1 t := by
    rw [deriv_smul]
    exact (ae_restrict_iff' measurableSet_Ioo).1 (Lp.coeFn_smul _ _)
  filter_upwards [h1] with t ht
  simp only [cutoffIioDeriv, Pi.smul_apply, smul_eq_mul]
  by_cases htI : t ∈ Ioo a b
  · simp only [indicator_of_mem htI]
    rw [ht htI, rep_smul_Icc hab r u (Ioo_subset_Icc_self htI)]
    ring
  · simp only [indicator_of_notMem htI, mul_zero]

/-- The second piece of the extension, `u ↦ (1 - η) ũ` extended by zero to `(-∞, b)`, as
`SobolevIntervalLp.MapData`. -/
def cutoffIioData (hab : a < b) : MapData p (Opens.Ioo a b) (Opens.Iio b) where
  F := cutoffIioFun a b
  W := cutoffIioDeriv a b
  memLp_F u := memLp_cutoffIioFun hab u
  memLp_W u := memLp_cutoffIioDeriv hab u
  hasWeakDerivOn u := hasWeakDerivOn_cutoffIioFun hab u
  F_add u v := (ae_restrict_iff' measurableSet_Iio).2 (Eventually.of_forall fun _ hx ↦
    cutoffIioFun_add hab u v (le_of_lt hx))
  F_smul r u := (ae_restrict_iff' measurableSet_Iio).2 (Eventually.of_forall fun _ hx ↦
    cutoffIioFun_smul hab r u (le_of_lt hx))
  W_add u v := ae_restrict_of_ae (cutoffIioDeriv_add hab u v)
  W_smul r u := ae_restrict_of_ae (cutoffIioDeriv_smul hab r u)

/-- **The second piece of the extension operator, `W^{1,p}(a, b) → W^{1,p}(-∞, b)`**:
`u ↦ (1 - η) ũ` extended by zero, a continuous linear map of norm at most `2 + (b - a)⁻¹`. -/
def cutoffIioCLM (hab : a < b) :
    SobolevIntervalLp 1 p (Opens.Ioo a b) →L[ℝ] SobolevIntervalLp 1 p (Opens.Iio b) :=
  (cutoffIioData hab).toCLM (2 + (b - a)⁻¹) fun u ↦ by
    have h0 := (ENNReal.toReal_mono enorm_ne_top (eLpNorm_cutoffIioFun_le hab u)).trans_eq
      (toReal_enorm _)
    have h1 := toReal_eLpNorm_le_of_le_add (by positivity) (eLpNorm_cutoffIioDeriv_le hab u)
    have h2 := norm_deriv_le u 0
    have h3 := norm_deriv_le u 1
    have h4 : 0 ≤ (b - a)⁻¹ := by positivity
    change (eLpNorm (cutoffIioFun a b u) p (volume.restrict (Iio b))).toReal
      + (eLpNorm (cutoffIioDeriv a b u) p (volume.restrict (Iio b))).toReal ≤ _
    nlinarith

/-- The function of the second piece is `(1 - η) ũ` on `(-∞, b)`. -/
theorem fn_cutoffIioCLM (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    fn (cutoffIioCLM hab u) =ᵐ[volume.restrict (Opens.Iio b : Set ℝ)] cutoffIioFun a b u :=
  (cutoffIioData hab).fn_map u

/-- `‖(1 - η) ũ‖_{L^p(-∞, b)} ≤ ‖u‖_{L^p(a, b)}`. -/
theorem norm_deriv_cutoffIioCLM_zero (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖deriv (cutoffIioCLM hab u) 0‖ ≤ ‖deriv u 0‖ := by
  rw [cutoffIioCLM, MapData.toCLM_apply, MapData.norm_deriv_map_zero]
  exact (ENNReal.toReal_mono enorm_ne_top (eLpNorm_cutoffIioFun_le hab u)).trans_eq
    (toReal_enorm _)

/-- `‖((1 - η) ũ)'‖_{L^p(-∞, b)} ≤ ‖u'‖_{L^p(a, b)} + (b - a)⁻¹ ‖u‖_{L^p(a, b)}`. -/
theorem norm_deriv_cutoffIioCLM_one (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖deriv (cutoffIioCLM hab u) 1‖ ≤ ‖deriv u 1‖ + (b - a)⁻¹ * ‖deriv u 0‖ := by
  rw [cutoffIioCLM, MapData.toCLM_apply, MapData.norm_deriv_map_one]
  exact toReal_eLpNorm_le_of_le_add (by positivity) (eLpNorm_cutoffIioDeriv_le hab u)

end SobolevIntervalLp


/-! ### Theorem 8.6 on a bounded interval -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {a b : ℝ}

/-- **The extension operator on a bounded interval, `W^{1,p}(a, b) → W^{1,p}(ℝ)`**
([brezis2011functional] Theorem 8.6, the bounded case): `u = η u + (1 - η) u`, the first piece
extended by zero to `(a, ∞)` and reflected across `a`, the second extended by zero to `(-∞, b)`
and reflected across `b`. -/
def extensionIooCLM (hab : a < b) :
    SobolevIntervalLp 1 p (Opens.Ioo a b) →L[ℝ] SobolevIntervalLp 1 p ⊤ :=
  (reflectIoiCLM a).comp (cutoffIoiCLM hab) + (reflectIioCLM b).comp (cutoffIioCLM hab)

/-- The extension operator on a bounded interval, unfolded. -/
theorem extensionIooCLM_apply (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    extensionIooCLM hab u = reflectIoiCLM a (cutoffIoiCLM hab u)
      + reflectIioCLM b (cutoffIioCLM hab u) := rfl

/-- **The extension of `u ∈ W^{1,p}(a, b)` restricts to `u`** (Theorem 8.6 (i), bounded
case): on `(a, b)` the two pieces are `η ũ` and `(1 - η) ũ`. -/
theorem fn_extensionIooCLM (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    fn (extensionIooCLM hab u) =ᵐ[volume.restrict (Opens.Ioo a b : Set ℝ)] fn u := by
  have h1 : fn (reflectIoiCLM a (cutoffIoiCLM hab u))
      =ᵐ[volume.restrict (Ioo a b)] cutoffIoiFun a b u :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self
      ((fn_reflectIoiCLM_restrict _).trans (fn_cutoffIoiCLM hab u))
  have h2 : fn (reflectIioCLM b (cutoffIioCLM hab u))
      =ᵐ[volume.restrict (Ioo a b)] cutoffIioFun a b u :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Iio_self
      ((fn_reflectIioCLM_restrict _).trans (fn_cutoffIioCLM hab u))
  have h3 : fn (extensionIooCLM hab u) =ᵐ[volume.restrict (Ioo a b)]
      fn (reflectIoiCLM a (cutoffIoiCLM hab u)) + fn (reflectIioCLM b (cutoffIioCLM hab u)) :=
    ae_restrict_of_ae (eventuallyEq_restrict_top_iff.1 (SobolevMultiIndex.fn_add _ _))
  refine (h3.trans (h1.add h2)).trans ?_
  refine EventuallyEq.trans ?_ (fn_ae_eq_rep (ordConnected_coe_Ioo a b) u).symm
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx ↦ ?_)
  simp only [Pi.add_apply]
  rw [cutoffIoiFun_of_mem u hx, cutoffIioFun_of_mem u hx]
  ring

/-- **Theorem 8.6 (ii), bounded case**: `‖Pu‖_{L^p(ℝ)} ≤ 4 ‖u‖_{L^p(a, b)}`. -/
theorem norm_deriv_extensionIooCLM_zero (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖deriv (extensionIooCLM hab u) 0‖ ≤ 4 * ‖deriv u 0‖ := by
  rw [extensionIooCLM_apply, deriv_add]
  have h1 := (norm_deriv_reflectIoiCLM_zero (cutoffIoiCLM hab u)).trans
    (mul_le_mul_of_nonneg_left (norm_deriv_cutoffIoiCLM_zero hab u) zero_le_two)
  have h2 := (norm_deriv_reflectIioCLM_zero (cutoffIioCLM hab u)).trans
    (mul_le_mul_of_nonneg_left (norm_deriv_cutoffIioCLM_zero hab u) zero_le_two)
  linarith [norm_add_le (deriv (reflectIoiCLM a (cutoffIoiCLM hab u)) 0)
    (deriv (reflectIioCLM b (cutoffIioCLM hab u)) 0)]

/-- **Theorem 8.6 (iii), bounded case, with the constant of footnote 6**:
`‖(Pu)'‖_{L^p(ℝ)} ≤ 4 (‖u'‖_{L^p(a, b)} + (b - a)⁻¹ ‖u‖_{L^p(a, b)})`. -/
theorem norm_deriv_extensionIooCLM_one (hab : a < b) (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    ‖deriv (extensionIooCLM hab u) 1‖ ≤ 4 * (‖deriv u 1‖ + (b - a)⁻¹ * ‖deriv u 0‖) := by
  rw [extensionIooCLM_apply, deriv_add]
  have h1 := (norm_deriv_reflectIoiCLM_one (cutoffIoiCLM hab u)).trans
    (mul_le_mul_of_nonneg_left (norm_deriv_cutoffIoiCLM_one hab u) zero_le_two)
  have h2 := (norm_deriv_reflectIioCLM_one (cutoffIioCLM hab u)).trans
    (mul_le_mul_of_nonneg_left (norm_deriv_cutoffIioCLM_one hab u) zero_le_two)
  linarith [norm_add_le (deriv (reflectIoiCLM a (cutoffIoiCLM hab u)) 1)
    (deriv (reflectIioCLM b (cutoffIioCLM hab u)) 1)]

/-- **Theorem 8.6 of [brezis2011functional], the bounded case**: for `a < b`, `1 ≤ p ≤ ∞` and
`u ∈ W^{1,p}(a, b)`, the extension `Pu ∈ W^{1,p}(ℝ)` built from the Lipschitz cut-off `η`
(`η ũ` extended by zero to `(a, ∞)` and reflected across `a`, plus `(1 - η) ũ` extended by zero to
`(-∞, b)` and reflected across `b`) agrees with `u` on `(a, b)` and satisfies
`‖Pu‖_{L^p(ℝ)} ≤ 4 ‖u‖_{L^p(a, b)}` and
`‖(Pu)'‖_{L^p(ℝ)} ≤ 4 (‖u'‖_{L^p(a, b)} + (b - a)⁻¹ ‖u‖_{L^p(a, b)})`, the constants of the
book's footnote 6, which the Lipschitz cut-off attains. -/
theorem memSobolevIntervalLp_cutoff_reflect (hab : a < b)
    (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) :
    fn (extensionIooCLM hab u) =ᵐ[volume.restrict (Opens.Ioo a b : Set ℝ)] fn u ∧
      ‖deriv (extensionIooCLM hab u) 0‖ ≤ 4 * ‖deriv u 0‖ ∧
      ‖deriv (extensionIooCLM hab u) 1‖ ≤ 4 * (‖deriv u 1‖ + (b - a)⁻¹ * ‖deriv u 0‖) :=
  ⟨fn_extensionIooCLM hab u, norm_deriv_extensionIooCLM_zero hab u,
    norm_deriv_extensionIooCLM_one hab u⟩

end SobolevIntervalLp

/-! ### Theorem 8.6 on an arbitrary open interval -/

namespace SobolevIntervalLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

/-- **Existence of the extension operator** ([brezis2011functional] Theorem 8.6): on every
nonempty open interval `I`, bounded or not, there is a continuous linear map
`P : W^{1,p}(I) → W^{1,p}(ℝ)` with `P u = u` on `I`, `‖Pu‖_{L^p(ℝ)} ≤ 4 ‖u‖_{L^p(I)}` and
`‖(Pu)'‖_{L^p(ℝ)} ≤ 4 (‖u'‖_{L^p(I)} + |I|⁻¹ ‖u‖_{L^p(I)})`, where `|I|⁻¹ = 0` when `I` is
unbounded. By cases on the shape of `I`: the identity on `ℝ`, reflection on a half-line, the
cut-off construction on a bounded interval. -/
theorem exists_extensionCLM (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty) :
    ∃ P : SobolevIntervalLp 1 p I →L[ℝ] SobolevIntervalLp 1 p ⊤,
      (∀ u, fn (P u) =ᵐ[volume.restrict (I : Set ℝ)] fn u) ∧
      (∀ u, ‖deriv (P u) 0‖ ≤ 4 * ‖deriv u 0‖) ∧
      (∀ u, ‖deriv (P u) 1‖ ≤ 4 * (‖deriv u 1‖ + (volume (I : Set ℝ)).toReal⁻¹ * ‖deriv u 0‖)) := by
  have hk : 0 ≤ (volume (I : Set ℝ)).toReal⁻¹ := by positivity
  rcases I.eq_intervals_of_ordConnected hI with h | h | ⟨a, h⟩ | ⟨b, h⟩ | ⟨a, b, hab, h⟩
  · exact absurd hne (by rw [h]; exact Set.not_nonempty_empty)
  · obtain rfl : I = ⊤ := Opens.ext (h.trans Opens.coe_top.symm)
    refine ⟨ContinuousLinearMap.id ℝ _, fun u ↦ EventuallyEq.refl _ _, fun u ↦ ?_, fun u ↦ ?_⟩
    · change ‖deriv u 0‖ ≤ 4 * ‖deriv u 0‖
      linarith [norm_nonneg (deriv u 0)]
    · change ‖deriv u 1‖ ≤ _
      nlinarith [norm_nonneg (deriv u 1), norm_nonneg (deriv u 0)]
  · obtain rfl : I = Opens.Ioi a := Opens.ext h
    refine ⟨reflectIoiCLM a, fun u ↦ fn_reflectIoiCLM_restrict u, fun u ↦ ?_, fun u ↦ ?_⟩
    · linarith [norm_deriv_reflectIoiCLM_zero u, norm_nonneg (deriv u 0)]
    · nlinarith [norm_deriv_reflectIoiCLM_one u, norm_nonneg (deriv u 1), norm_nonneg (deriv u 0)]
  · obtain rfl : I = Opens.Iio b := Opens.ext h
    refine ⟨reflectIioCLM b, fun u ↦ fn_reflectIioCLM_restrict u, fun u ↦ ?_, fun u ↦ ?_⟩
    · linarith [norm_deriv_reflectIioCLM_zero u, norm_nonneg (deriv u 0)]
    · nlinarith [norm_deriv_reflectIioCLM_one u, norm_nonneg (deriv u 1), norm_nonneg (deriv u 0)]
  · obtain rfl : I = Opens.Ioo a b := Opens.ext h
    refine ⟨extensionIooCLM hab, fun u ↦ fn_extensionIooCLM hab u,
      fun u ↦ norm_deriv_extensionIooCLM_zero hab u, fun u ↦ ?_⟩
    have e : (volume ((Opens.Ioo a b : Opens ℝ) : Set ℝ)).toReal⁻¹ = (b - a)⁻¹ := by
      rw [Opens.coe_Ioo, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.2 hab.le)]
    rw [e]
    exact norm_deriv_extensionIooCLM_one hab u

/-- **The extension operator `P : W^{1,p}(I) → W^{1,p}(ℝ)`** of [brezis2011functional] Theorem
8.6, for `1 ≤ p ≤ ∞` and a nonempty open interval `I`: a continuous linear map with
`P u = u` on `I` (`SobolevIntervalLp.fn_extensionCLM`), `‖Pu‖_{L^p(ℝ)} ≤ 4 ‖u‖_{L^p(I)}`
(`norm_deriv_extensionCLM_zero_le`),
`‖(Pu)'‖_{L^p(ℝ)} ≤ 4 (‖u'‖_{L^p(I)} + |I|⁻¹ ‖u‖_{L^p(I)})`
(`norm_deriv_extensionCLM_one_le`, with `|I|⁻¹ := (volume I).toReal⁻¹`, which is `0` for an
unbounded `I`) and `‖P‖ ≤ 8 (1 + |I|⁻¹)` (`norm_extensionCLM_le`). It is chosen among the
operators `SobolevIntervalLp.exists_extensionCLM` provides; for a half-line it is
`reflectIoiCLM`/`reflectIioCLM` and for a bounded interval `extensionIooCLM`, up to that choice. -/
def extensionCLM (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty) :
    SobolevIntervalLp 1 p I →L[ℝ] SobolevIntervalLp 1 p ⊤ :=
  Classical.choose (exists_extensionCLM hI hne)

/-- **Theorem 8.6 (i)**: the extension restricts to the function on `I`. -/
theorem fn_extensionCLM (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty)
    (u : SobolevIntervalLp 1 p I) :
    fn (extensionCLM hI hne u) =ᵐ[volume.restrict (I : Set ℝ)] fn u :=
  (Classical.choose_spec (exists_extensionCLM hI hne)).1 u

/-- **Theorem 8.6 (ii)**: `‖Pu‖_{L^p(ℝ)} ≤ 4 ‖u‖_{L^p(I)}`. -/
theorem norm_deriv_extensionCLM_zero_le (hI : (I : Set ℝ).OrdConnected)
    (hne : (I : Set ℝ).Nonempty) (u : SobolevIntervalLp 1 p I) :
    ‖deriv (extensionCLM hI hne u) 0‖ ≤ 4 * ‖deriv u 0‖ :=
  (Classical.choose_spec (exists_extensionCLM hI hne)).2.1 u

/-- **Theorem 8.6 (iii)**, with the constant of footnote 6:
`‖(Pu)'‖_{L^p(ℝ)} ≤ 4 (‖u'‖_{L^p(I)} + |I|⁻¹ ‖u‖_{L^p(I)})`, `|I|⁻¹ = 0` for unbounded `I`. -/
theorem norm_deriv_extensionCLM_one_le (hI : (I : Set ℝ).OrdConnected)
    (hne : (I : Set ℝ).Nonempty) (u : SobolevIntervalLp 1 p I) :
    ‖deriv (extensionCLM hI hne u) 1‖
      ≤ 4 * (‖deriv u 1‖ + (volume (I : Set ℝ)).toReal⁻¹ * ‖deriv u 0‖) :=
  (Classical.choose_spec (exists_extensionCLM hI hne)).2.2 u

/-- **The operator norm of the extension operator**: `‖P‖ ≤ 8 (1 + |I|⁻¹)` in the norm of the
type, from (ii) and (iii). -/
theorem norm_extensionCLM_le (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty) :
    ‖(extensionCLM hI hne : SobolevIntervalLp 1 p I →L[ℝ] SobolevIntervalLp 1 p ⊤)‖
      ≤ 8 * (1 + (volume (I : Set ℝ)).toReal⁻¹) := by
  have hk : 0 ≤ (volume (I : Set ℝ)).toReal⁻¹ := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  have h0 := norm_deriv_extensionCLM_zero_le hI hne u
  have h1 := norm_deriv_extensionCLM_one_le hI hne u
  have h2 := norm_deriv_le u 0
  have h3 := norm_deriv_le u 1
  have h4 : ‖extensionCLM hI hne u‖ ≤ ‖deriv (extensionCLM hI hne u) 0‖
      + ‖deriv (extensionCLM hI hne u) 1‖ := by
    refine (norm_le_sum_norm_deriv _).trans_eq ?_
    rw [Fin.sum_univ_two]
  nlinarith [norm_nonneg u]

/-- **The continuous representative of the extension is the representative of `u` on the closure
of `I`**: `rep (Pu)` is continuous on the whole line and agrees with `u` almost everywhere on
`I`, so it is the representative by uniqueness (`SobolevIntervalLp.rep_eq_of_continuousOn`). -/
theorem rep_extensionCLM (hI : (I : Set ℝ).OrdConnected) (hne : (I : Set ℝ).Nonempty)
    (u : SobolevIntervalLp 1 p I) :
    EqOn (rep (extensionCLM hI hne u)) (rep u) (closure (I : Set ℝ)) := by
  have hcont : ContinuousOn (rep (extensionCLM hI hne u)) (closure (I : Set ℝ)) :=
    (continuousOn_rep Opens.ordConnected_top (extensionCLM hI hne u)).mono
      fun x _ ↦ Opens.mem_closure_top x
  have hae : fn u =ᵐ[volume.restrict (I : Set ℝ)] rep (extensionCLM hI hne u) :=
    (fn_extensionCLM hI hne u).symm.trans (ae_restrict_of_ae (eventuallyEq_restrict_top_iff.1
      (fn_ae_eq_rep Opens.ordConnected_top _)))
  exact (rep_eq_of_continuousOn hI u hcont hae).symm

end SobolevIntervalLp

end
