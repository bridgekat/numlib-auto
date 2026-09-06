import Numlib.Analysis.Wavelet.Haar

/-!
# Multiresolution analysis

A *multiresolution analysis* of `L²(ℝ)` is a ladder of closed subspaces `V j`, `j : ℤ`, generated
by the dilates and integer translates of a single *scaling function* `φ`. This module states the
definition as a bundled predicate, derives the orthonormal system of each level and the scaling
equation, and shows that the Haar system of `Numlib/Analysis/Wavelet/Haar` is an instance.

## Main definitions

* `MeasureTheory.Lp.translationₗᵢ a` is translation, `f ↦ (x ↦ f (x + a))`, as a linear isometry
  of `L²(ℝ)`; it is `MeasureTheory.Lp.compMeasurePreservingₗᵢ` along `x ↦ x + a`, which is measure
  preserving. Dilation, which is not measure preserving, is
  `MeasureTheory.Lp.dilationₗᵢ` of `Numlib/Analysis/Wavelet/Haar`.
* `scalingSystem φ j k` is `2 ^ (j / 2) φ (2 ^ j x - k)`, the dilate by `2 ^ j` of the translate
  of `φ` by `k`, and `translates φ k = scalingSystem φ 0 k` up to the identification of the
  dilation by `1` with the identity.
* `IsMultiresolutionAnalysis V φ` is Atkinson–Han's Definition 4.5.1[^atkinson-han]. Two of its
  clauses depart from the book's phrasing, and deliberately. *Shift invariance* is stated as
  orthonormality of the translates together with `V 0` being the closed span of them, rather than
  as "the translates are an orthonormal basis of `V 0`": the two are equivalent, the former is
  what a construction proves, and `Orthonormal.hilbertBasisTopologicalClosure` turns it into a
  `HilbertBasis` on demand. *Scale invariance* is
  stated as `V j = (V 0).map (dilation (2 ^ j))` rather than as the equivalence
  `f ∈ V j ↔ dilation (2 ^ (-j)) f ∈ V 0`, because that is the form a construction proves and the
  form under which images of spans compute.

## Main statements

* `IsMultiresolutionAnalysis.orthonormal_scaled` is Proposition 4.5.2: the system of level `j` is
  orthonormal, and with `IsMultiresolutionAnalysis.eq_topologicalClosure_span_scalingSystem` it is
  a Hilbert basis of `V j`.
* `IsMultiresolutionAnalysis.hasSum_scalingEquation` is the scaling equation: `φ` is the sum of
  its level-`1` coefficients against the level-`1` system.
* `Haar.isMultiresolutionAnalysis` is the Haar instance. Its scaling coefficients are computed in
  `NumlibSurface.AtkinsonHan.Chapter04.haar_scalingCoeff`, in the surface rather than here, because
  the book states them and nothing in this layer consumes them yet.

The construction of a scaling function from a sequence of dilation coefficients, the wavelet of
Atkinson–Han (4.5.4) and Daubechies' compactly supported families are not developed: the book
states them without proof, and the standard arguments need conditions on `φ̂` that Mathlib has no
vocabulary for.

## References

[^atkinson-han]: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional
  Analysis Framework*, 3rd edition, Springer, 2009. (Definition 4.5.1, Proposition 4.5.2,
  (4.5.1)–(4.5.3).)
-/

open scoped ENNReal

noncomputable section

namespace MeasureTheory.Lp

/-! ### Translation of `L²(ℝ)` -/

/-- Translation of `L²(ℝ)` by `a`: `f ↦ (x ↦ f (x + a))`, a linear isometry, since `x ↦ x + a`
preserves the Lebesgue measure. -/
def translationₗᵢ (a : ℝ) :
    Lp ℝ 2 (volume : Measure ℝ) →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  compMeasurePreservingₗᵢ ℝ (fun x : ℝ => x + a) (measurePreserving_add_right volume a)

theorem translationₗᵢ_apply (a : ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    translationₗᵢ a f =ᵐ[volume] fun x => f (x + a) :=
  coeFn_compMeasurePreserving _ _

@[simp]
theorem translationₗᵢ_zero (f : Lp ℝ 2 (volume : Measure ℝ)) : translationₗᵢ 0 f = f := by
  refine Lp.ext ?_
  filter_upwards [translationₗᵢ_apply 0 f] with x hx
  rw [hx, add_zero]

/-- The translate of `r` times the indicator of `s` is `r` times the indicator of the translated
set `(fun x => x + a) ⁻¹' s`. -/
theorem translationₗᵢ_indicatorConstLp (a : ℝ) {s : Set ℝ} (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) (r : ℝ) :
    translationₗᵢ a (indicatorConstLp 2 hs hμs r)
      = indicatorConstLp 2 (hs.preimage (measurable_add_const a))
          (by rw [(measurePreserving_add_right volume a).measure_preimage
                hs.nullMeasurableSet]; exact hμs) r := by
  refine Lp.ext ?_
  filter_upwards [translationₗᵢ_apply a (indicatorConstLp 2 hs hμs r),
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := r)).comp_tendsto
      (measurePreserving_add_right volume a).quasiMeasurePreserving.tendsto_ae,
    indicatorConstLp_coeFn (p := 2) (hs := hs.preimage (measurable_add_const a))
      (hμs := by rw [(measurePreserving_add_right volume a).measure_preimage
        hs.nullMeasurableSet]; exact hμs) (c := r)] with x hx hx2 hx3
  simp only [Function.comp_apply] at hx2
  rw [hx, hx2, hx3]
  by_cases hxs : x + a ∈ s
  · rw [Set.indicator_of_mem hxs,
      Set.indicator_of_mem (show x ∈ (fun x : ℝ => x + a) ⁻¹' s from hxs)]
  · rw [Set.indicator_of_notMem hxs,
      Set.indicator_of_notMem (show x ∉ (fun x : ℝ => x + a) ⁻¹' s from hxs)]

end MeasureTheory.Lp

open MeasureTheory

/-! ### The system generated by a scaling function -/

/-- The integer translates `φ (· - k)` of a scaling function. -/
def translates (φ : Lp ℝ 2 (volume : Measure ℝ)) (k : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  Lp.translationₗᵢ (-(k : ℝ)) φ

/-- The system generated by a scaling function: `scalingSystem φ j k` is
`2 ^ (j / 2) φ (2 ^ j x - k)`, the dilate by `2 ^ j` of the `k`-th translate of `φ`. -/
def scalingSystem (φ : Lp ℝ 2 (volume : Measure ℝ)) (j k : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  Lp.dilationₗᵢ ((2 : ℝ) ^ j) (zpow_ne_zero j two_ne_zero) (translates φ k)

theorem scalingSystem_eq_dilation (φ : Lp ℝ 2 (volume : Measure ℝ)) (j : ℤ) :
    scalingSystem φ j = ⇑(Lp.dilationₗᵢ ((2 : ℝ) ^ j) (zpow_ne_zero j two_ne_zero)) ∘
      translates φ := rfl

@[simp]
theorem scalingSystem_zero (φ : Lp ℝ 2 (volume : Measure ℝ)) :
    scalingSystem φ 0 = translates φ := by
  funext k
  unfold scalingSystem
  refine Lp.ext ?_
  filter_upwards [Lp.dilationₗᵢ_apply ((2 : ℝ) ^ (0 : ℤ)) (zpow_ne_zero 0 two_ne_zero)
    (translates φ k)] with x hx
  rw [hx, zpow_zero, one_mul, abs_one, Real.one_rpow, one_mul]

/-! ### The definition -/

/-- **A multiresolution analysis of `L²(ℝ)`**: a ladder `V : ℤ → Submodule ℝ (L²(ℝ))` of scaling
spaces generated by the dilates and integer translates of a scaling function `φ`.

The five clauses are shift invariance (here: the translates of `φ` are orthonormal and span `V 0`
densely), scale invariance, nesting, density and separation.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009, Definition 4.5.1. -/
structure IsMultiresolutionAnalysis (V : ℤ → Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ)))
    (φ : Lp ℝ 2 (volume : Measure ℝ)) : Prop where
  /-- The integer translates of the scaling function are orthonormal. -/
  orthonormal_translates : Orthonormal ℝ (translates φ)
  /-- `V 0` is the closed span of the integer translates of the scaling function. -/
  eq_topologicalClosure_span :
    V 0 = (Submodule.span ℝ (Set.range (translates φ))).topologicalClosure
  /-- Scale invariance: `V j` is the image of `V 0` under the dilation by `2 ^ j`. -/
  eq_map_dilation : ∀ j : ℤ, V j = (V 0).map
    (Lp.dilationₗᵢ ((2 : ℝ) ^ j) (zpow_ne_zero j two_ne_zero)).toLinearEquiv.toLinearMap
  /-- Nesting: each scaling space sits inside the next. -/
  le_succ : ∀ j : ℤ, V j ≤ V (j + 1)
  /-- Density: the union of the scaling spaces is dense in `L²(ℝ)`. -/
  topologicalClosure_iSup : (⨆ j : ℤ, V j).topologicalClosure = ⊤
  /-- Separation: the scaling spaces meet in `0`. -/
  iInf_eq_bot : (⨅ j : ℤ, V j) = ⊥

namespace IsMultiresolutionAnalysis

variable {V : ℤ → Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ))} {φ : Lp ℝ 2 (volume : Measure ℝ)}

/-- The image of the closure of a subspace under a surjective linear isometry is the closure of
the image. -/
private theorem map_topologicalClosure
    (D : Lp ℝ 2 (volume : Measure ℝ) ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure ℝ))
    (K : Submodule ℝ (Lp ℝ 2 (volume : Measure ℝ))) :
    K.topologicalClosure.map D.toLinearEquiv.toLinearMap
      = (K.map D.toLinearEquiv.toLinearMap).topologicalClosure := by
  refine SetLike.ext' ?_
  rw [Submodule.map_coe, Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe,
    Submodule.map_coe]
  exact D.toHomeomorph.image_closure _

/-- **The scaling system of every level is orthonormal.** The level-`j` system is the image of
the level-`0` system under the unitary dilation by `2 ^ j`.

Together with `IsMultiresolutionAnalysis.eq_topologicalClosure_span_scalingSystem` this is
Atkinson–Han's Proposition 4.5.2, that `{2 ^ (j/2) φ (2 ^ j x - k)}` is an orthonormal basis of
`V j`; `IsMultiresolutionAnalysis.hilbertBasis` is that basis.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009, Proposition 4.5.2. -/
theorem orthonormal_scaled (h : IsMultiresolutionAnalysis V φ) (j : ℤ) :
    Orthonormal ℝ (scalingSystem φ j) := by
  rw [scalingSystem_eq_dilation]
  exact h.orthonormal_translates.comp_linearIsometryEquiv _

/-- Each scaling space is the closed span of the scaling system of its level. -/
theorem eq_topologicalClosure_span_scalingSystem (h : IsMultiresolutionAnalysis V φ) (j : ℤ) :
    V j = (Submodule.span ℝ (Set.range (scalingSystem φ j))).topologicalClosure := by
  have himg : (Lp.dilationₗᵢ ((2 : ℝ) ^ j)
      (zpow_ne_zero j two_ne_zero)).toLinearEquiv.toLinearMap ''
        Set.range (translates φ) = Set.range (scalingSystem φ j) := by
    rw [← Set.range_comp]
    rfl
  rw [h.eq_map_dilation j, h.eq_topologicalClosure_span, map_topologicalClosure,
    Submodule.map_span, himg]

theorem scalingSystem_mem (h : IsMultiresolutionAnalysis V φ) (j k : ℤ) :
    scalingSystem φ j k ∈ V j := by
  rw [h.eq_topologicalClosure_span_scalingSystem j]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self k))

/-- **Every element of `V j` is the sum of its coefficients against the level-`j` scaling
system.** With `IsMultiresolutionAnalysis.orthonormal_scaled` this is the content of
Atkinson–Han's Proposition 4.5.2: the system is an orthonormal basis of `V j`.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009, Proposition 4.5.2. -/
theorem hasSum_inner_smul (h : IsMultiresolutionAnalysis V φ) (j : ℤ)
    {f : Lp ℝ 2 (volume : Measure ℝ)} (hf : f ∈ V j) :
    HasSum (fun k : ℤ => (inner ℝ (scalingSystem φ j k) f) • scalingSystem φ j k) f := by
  have hmem : ∀ k : ℤ, scalingSystem φ j k ∈
      (Submodule.span ℝ (Set.range (scalingSystem φ j))).topologicalClosure := fun k =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self k))
  have hfK : f ∈ (Submodule.span ℝ (Set.range (scalingSystem φ j))).topologicalClosure := by
    rw [← h.eq_topologicalClosure_span_scalingSystem j]; exact hf
  set b := (h.orthonormal_scaled j).hilbertBasisTopologicalClosure with hbdef
  have hbcoe : ∀ k : ℤ,
      ((b k : (Submodule.span ℝ (Set.range (scalingSystem φ j))).topologicalClosure) :
        Lp ℝ 2 (volume : Measure ℝ)) = scalingSystem φ j k := by
    intro k
    simp only [hbdef, Orthonormal.hilbertBasisTopologicalClosure]
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    rfl
  have hsum := (b.hasSum_repr ⟨f, hfK⟩).mapL
    (Submodule.span ℝ (Set.range (scalingSystem φ j))).topologicalClosure.subtypeL
  refine hsum.congr_fun fun k => ?_
  rw [ContinuousLinearMap.map_smul, Submodule.subtypeL_apply, hbcoe k,
    HilbertBasis.repr_apply_apply, Submodule.coe_inner, hbcoe k]

/-- The scaling function lies in `V 0`. -/
theorem mem_zero (h : IsMultiresolutionAnalysis V φ) : φ ∈ V 0 := by
  have h0 : translates φ 0 = φ := by
    rw [translates, Int.cast_zero, neg_zero]
    exact Lp.translationₗᵢ_zero φ
  rw [h.eq_topologicalClosure_span]
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨0, h0⟩)

/-- **The scaling equation.** In a multiresolution analysis the scaling function is the sum of the
level-`1` system against its own level-`1` coefficients `p k = ⟪√2 φ (2 · - k), φ⟫`: `φ` lies in
`V 0 ≤ V 1`, and is expanded in the orthonormal system of `V 1`.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009, (4.5.1)–(4.5.3). -/
theorem hasSum_scalingEquation (h : IsMultiresolutionAnalysis V φ) :
    HasSum (fun k : ℤ => (inner ℝ (scalingSystem φ 1 k) φ) • scalingSystem φ 1 k) φ :=
  h.hasSum_inner_smul 1 (h.le_succ 0 h.mem_zero)

end IsMultiresolutionAnalysis

/-! ### The Haar system -/

namespace Haar

/-- The level-`0` Haar scaling functions are the integer translates of the unit step
`φ = 1_[0,1)`. -/
theorem translates_scalingFun_zero (k : ℤ) :
    translates (scalingFun 0 0) k = scalingFun 0 k := by
  have hset : (fun x : ℝ => x + -(k : ℝ)) ⁻¹' dyadic 0 0 = dyadic 0 k := by
    ext x
    simp only [dyadic, Set.mem_preimage, Set.mem_Ico, neg_zero, zpow_zero, mul_one,
      Int.cast_zero, zero_add]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [translates, scalingFun_zero_zero, Lp.translationₗᵢ_indicatorConstLp,
    indicatorConstLp_congr_set _ _ (measurableSet_dyadic 0 k) (volume_dyadic_ne_top 0 k) hset,
    scalingFun]
  norm_num

/-- **The Haar system is a multiresolution analysis**, with scaling function the unit step
`φ = 1_[0,1)`. Its five clauses are the five parts of Atkinson–Han's Theorem 4.4.1 proved in
`Numlib/Analysis/Wavelet/Haar`.

Reference: Kendall Atkinson and Weimin Han, *Theoretical Numerical Analysis: A Functional Analysis
Framework*, 3rd edition, Springer, 2009, §4.5. -/
theorem isMultiresolutionAnalysis : IsMultiresolutionAnalysis V (scalingFun 0 0) where
  orthonormal_translates := by
    have := orthonormal_scalingFun 0
    rwa [← funext translates_scalingFun_zero] at this
  eq_topologicalClosure_span := by
    rw [funext translates_scalingFun_zero]
    rfl
  eq_map_dilation := V_eq_map_dilation
  le_succ := V_le_V_succ
  topologicalClosure_iSup := topologicalClosure_iSup_V
  iInf_eq_bot := iInf_V_eq_bot

end Haar
