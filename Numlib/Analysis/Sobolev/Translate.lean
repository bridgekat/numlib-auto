import Numlib.Analysis.Sobolev.Operators

/-!
# Translations of Sobolev functions on an invariant open set

For an open set `Ω` of a normed space `E` invariant under the translation by `h`
(`IsTranslationInvariant Ω h`: `x + h ∈ Ω ↔ x ∈ Ω`) and a right-invariant measure `μ`, the
translation `u ↦ u(· + h)` is an isometry of `L^p(Ω)` and of `W^{k,p}(Ω)` that commutes with
the weak derivatives and preserves `W_0^{k,p}(Ω)`. This is the machinery behind the method of
translations of L. Nirenberg for the regularity of elliptic equations
([brezis2011functional] §9.6, on the whole space and on the half space `{x_N > 0}`, invariant
under the tangential translations), and behind the translation invariance of the whole-line
problems of [brezis2011functional] §8.4.

## Main definitions and statements

* `IsTranslationInvariant Ω h` and its API (`neg`, `add`, `zero`, `univ`, `smul_mem`,
  `IsTranslationInvariant.measurePreserving`: the translation preserves `μ.restrict Ω`).
* `LocallyIntegrableOn.comp_add_right`, `MeasureTheory.MemLp.comp_add_right`: the translate of
  a locally integrable, respectively `L^p(Ω)`, function is one.
* `TestFunction.compAddRightOn`: the translate of a test function on `Ω` is a test function on
  `Ω`; `integral_smul_comp_add_right`: the change of variables `x ↦ x + h` in an integral over
  `Ω` against a test function.
* `HasWeakIteratedLineDerivOn.comp_add_right`: **translation commutes with the weak
  derivative**.
* `MeasureTheory.Lp.translate F p hΩ : Lp F p (μ.restrict Ω) →ₗᵢ[ℝ] Lp F p (μ.restrict Ω)`, the
  translation `u ↦ u(· + h)` on `L^p(Ω)`, with `Lp.coeFn_translate`, `Lp.translate_neg_translate`
  (`τ_{−h} ∘ τ_h = 1`) and the adjointness `Lp.inner_translate` in `L²(Ω)`. Note the sign: the
  whole-space translation `MeasureTheory.Lp.translateₗᵢ` of `Numlib.Analysis.Convolution.Bochner`
  is `g ↦ g(· − y)`, the convention of harmonic analysis, so `Lp.translateₗᵢ 𝕜 F p (−h)` is this
  `Lp.translate` on `Ω = ⊤`.
* `SobolevMultiIndex.translateL F b k p μ hΩ : W^{k,p}(Ω) →ₗᵢ[ℝ] W^{k,p}(Ω)`, the translation on
  `W^{k,p}(Ω)`, with `weakDeriv_translateL` (the weak derivatives of the translate are the
  translates of the weak derivatives), `fn_translateL`, and `translateL_mem_zero`:
  **`W_0^{k,p}(Ω)` is invariant under the translations that leave `Ω` invariant**
  ([brezis2011functional] §9.6, (54)).

## Design

Everything is stated for a general normed space `E` (finite-dimensional where `W^{k,p}(Ω)` is
involved), a general target `F` and a right-invariant measure `μ`, with the invariance of `Ω`
as an explicit hypothesis rather than a property of a named domain; the half space and the
whole space are instances. The difference quotients `D_h = (τ_h − 1)/|h|` built on these
isometries, being the tool of one proof, live with it in
`Numlib/Analysis/PDE/Elliptic/Regularity.lean`.
-/

open Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology InnerProductSpace

noncomputable section

/-! ### Open sets invariant under a translation -/

section Invariant

variable {E : Type*} [AddGroup E]

/-- `IsTranslationInvariant Ω h` says that the set `Ω` is invariant under the translation by `h`:
`x + h ∈ Ω ↔ x ∈ Ω`. The whole space is invariant under every translation, and the half space
`{x_N > 0}` under the tangential ones (`h_N = 0`); this is what the method of translations of
[brezis2011functional] §9.6 needs of the domain. -/
def IsTranslationInvariant (Ω : Set E) (h : E) : Prop := ∀ x, x + h ∈ Ω ↔ x ∈ Ω

namespace IsTranslationInvariant

variable {Ω : Set E} {h : E}

/-- The translate of a point of an invariant set lies in the set. -/
theorem mem (hΩ : IsTranslationInvariant Ω h) {x : E} (hx : x ∈ Ω) : x + h ∈ Ω := (hΩ x).2 hx

/-- The preimage of an invariant set under the translation is the set. -/
theorem preimage_eq (hΩ : IsTranslationInvariant Ω h) : (· + h) ⁻¹' Ω = Ω :=
  Set.ext fun x ↦ hΩ x

/-- A set invariant under the translation by `h` is invariant under the translation by `-h`. -/
theorem neg (hΩ : IsTranslationInvariant Ω h) : IsTranslationInvariant Ω (-h) := fun x ↦ by
  have := hΩ (x + -h)
  rw [neg_add_cancel_right] at this
  exact this.symm

/-- The whole space is invariant under every translation. -/
theorem univ (h : E) : IsTranslationInvariant (univ : Set E) h := fun _ ↦ Iff.rfl

/-- Every set is invariant under the translation by `0`. -/
theorem zero (Ω : Set E) : IsTranslationInvariant Ω 0 := fun x ↦ by rw [add_zero]

/-- A set invariant under two translations is invariant under their sum. -/
theorem add {h' : E} (hΩ : IsTranslationInvariant Ω h) (hΩ' : IsTranslationInvariant Ω h') :
    IsTranslationInvariant Ω (h + h') := fun x ↦ by
  rw [← add_assoc, hΩ', hΩ]

end IsTranslationInvariant

end Invariant

section InvariantSmul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A set invariant under all the translations `t • y` contains the lines `x + ℝ y` through its
points. -/
theorem IsTranslationInvariant.smul_mem {Ω : Set E} {y : E}
    (hΩ : ∀ t : ℝ, IsTranslationInvariant Ω (t • y)) {x : E} (hx : x ∈ Ω) (t : ℝ) :
    x + t • y ∈ Ω :=
  (hΩ t).mem hx

end InvariantSmul

/-! ### Translations of locally integrable functions and of test functions -/

section Translate

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
  {Ω : Opens E} {h : E}

omit [NormedSpace ℝ E] in
/-- The translation by `h` preserves `μ.restrict Ω` when `Ω` is invariant under it. -/
theorem IsTranslationInvariant.measurePreserving [μ.IsAddRightInvariant]
    (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    MeasurePreserving (· + h) (μ.restrict (Ω : Set E)) (μ.restrict (Ω : Set E)) := by
  have := (measurePreserving_add_right μ h).restrict_preimage Ω.isOpen.measurableSet
  rwa [hΩ.preimage_eq] at this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A translate of a locally integrable function on an invariant open set is locally integrable
there. -/
theorem LocallyIntegrableOn.comp_add_right [μ.IsAddRightInvariant] [ProperSpace E] {u : E → F}
    (hu : LocallyIntegrableOn u Ω μ) (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    LocallyIntegrableOn (fun x ↦ u (x + h)) Ω μ := by
  rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu ⊢
  intro k hk hkc
  have hk' : (· + h) '' k ⊆ (Ω : Set E) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hΩ.mem (hk hx)
  have := hu ((· + h) '' k) hk' (hkc.image (continuous_id.add continuous_const))
  exact ((measurePreserving_add_right μ h).integrableOn_image
    (MeasurableEquiv.addRight h).measurableEmbedding).1 this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A translate of an `L^p(Ω)` function on an invariant open set is in `L^p(Ω)`, with the same
norm. -/
theorem MeasureTheory.MemLp.comp_add_right [μ.IsAddRightInvariant] {u : E → F} {p : ℝ≥0∞}
    (hu : MemLp u p (μ.restrict (Ω : Set E))) (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    MemLp (fun x ↦ u (x + h)) p (μ.restrict (Ω : Set E)) :=
  hu.comp_measurePreserving hΩ.measurePreserving

/-- The translate `x ↦ φ (x + h)` of a test function on an open set invariant under the
translation by `h`, as a test function on the same set. -/
def TestFunction.compAddRightOn (φ : 𝓓(Ω, F)) (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    𝓓(Ω, F) where
  toFun x := φ (x + h)
  contDiff' := φ.contDiff.comp (contDiff_id.add contDiff_const)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight h)
  tsupport_subset' := by
    have : tsupport (fun x ↦ φ (x + h)) = (Homeomorph.addRight h) ⁻¹' tsupport φ := by
      rw [tsupport, tsupport, (Homeomorph.addRight h).preimage_closure]
      rfl
    rw [this]
    intro x hx
    exact (hΩ x).1 (φ.tsupport_subset hx)

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem TestFunction.compAddRightOn_coe (φ : 𝓓(Ω, F))
    (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    (φ.compAddRightOn hΩ : E → F) = fun x ↦ φ (x + h) :=
  rfl

/-- The change of variables `x ↦ x + h` in an integral over an invariant open set, for an
integrand that is the product of a test function and a locally integrable function:
`∫_Ω ψ(x) u(x + h) dx = ∫_Ω ψ(x − h) u(x) dx`. -/
theorem integral_smul_comp_add_right [μ.IsAddRightInvariant] (u : E → F)
    (hΩ : IsTranslationInvariant (Ω : Set E) h) (ψ : 𝓓(Ω, ℝ)) :
    ∫ x in (Ω : Set E), ψ x • u (x + h) ∂μ = ∫ x in (Ω : Set E), ψ (x - h) • u x ∂μ := by
  have e1 : ∫ x in (Ω : Set E), ψ x • u (x + h) ∂μ = ∫ x, ψ x • u (x + h) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [ψ.eq_zero_of_notMem hx, zero_smul]
  have e2 : ∫ x in (Ω : Set E), ψ (x - h) • u x ∂μ = ∫ x, ψ (x - h) • u x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      have := (ψ.compAddRightOn hΩ.neg).eq_zero_of_notMem hx
      simp only [TestFunction.compAddRightOn_coe, ← sub_eq_add_neg] at this
      rw [this, zero_smul]
  rw [e1, e2, ← integral_add_right_eq_self (fun x ↦ ψ (x - h) • u x) h]
  simp only [add_sub_cancel_right]

end Translate

/-! ### The translation commutes with the weak derivative -/

section WeakDerivTranslate

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
  [μ.IsAddRightInvariant] {Ω : Opens E} {h : E}

/-- **Translation commutes with the weak derivative** on an invariant open set: if `w` is a weak
derivative of `u` along the tuple `y` on `Ω`, then `w(· + h)` is one of `u(· + h)`. The test
function `φ` is traded for its translate `φ(· − h)`, a test function on `Ω` again. -/
theorem HasWeakIteratedLineDerivOn.comp_add_right {n : ℕ} {y : Fin n → E} {u w : E → F}
    (hu : HasWeakIteratedLineDerivOn y u w Ω μ) (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    HasWeakIteratedLineDerivOn y (fun x ↦ u (x + h)) (fun x ↦ w (x + h)) Ω μ where
  locallyIntegrableOn := LocallyIntegrableOn.comp_add_right hu.locallyIntegrableOn hΩ
  locallyIntegrableOn_weakDeriv :=
    LocallyIntegrableOn.comp_add_right hu.locallyIntegrableOn_weakDeriv hΩ
  integral_smul_eq φ := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(Ω, ℝ), (ψ : E → ℝ) = fun x ↦ φ (x - h) :=
      ⟨φ.compAddRightOn hΩ.neg, by simp [sub_eq_add_neg]⟩
    have hψd : ∀ x, iteratedFDeriv ℝ n (ψ : E → ℝ) x y
        = iteratedFDeriv ℝ n (φ : E → ℝ) (x - h) y := fun x ↦ by
      rw [hψ, iteratedFDeriv_comp_sub']
    have e1 : ∫ x in (Ω : Set E), iteratedFDeriv ℝ n φ x y • u (x + h) ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n ψ x y • u x ∂μ := by
      have := integral_smul_comp_add_right (μ := μ) u hΩ (φ.iteratedFDerivApply n y)
      simp only [TestFunction.iteratedFDerivApply_apply] at this
      rw [this]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hψd])
    have e2 : ∫ x in (Ω : Set E), φ x • w (x + h) ∂μ = ∫ x in (Ω : Set E), ψ x • w x ∂μ := by
      rw [integral_smul_comp_add_right (μ := μ) w hΩ φ]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hψ])
    rw [e1, e2, hu.integral_smul_eq ψ]

end WeakDerivTranslate

/-! ### Translations on `L^p(Ω)` -/

namespace MeasureTheory.Lp

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} [μ.IsAddRightInvariant]
  {Ω : Opens E} {h : E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (F p) in
/-- **Translation by `h` on `L^p(Ω)`**, `u ↦ u(· + h)`, for an open set `Ω` invariant under the
translation: a linear isometry, by the translation invariance of the measure
(`MeasureTheory.Lp.compMeasurePreservingₗᵢ`). -/
def translate (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    Lp F p (μ.restrict (Ω : Set E)) →ₗᵢ[ℝ] Lp F p (μ.restrict (Ω : Set E)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (· + h) hΩ.measurePreserving

/-- `translate hΩ u` is `u(· + h)` almost everywhere on `Ω`. -/
theorem coeFn_translate (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : Lp F p (μ.restrict (Ω : Set E))) :
    translate F p hΩ u =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ u (x + h) :=
  Lp.coeFn_compMeasurePreserving u hΩ.measurePreserving

/-- Translating by `h` and then by `−h` is the identity on `L^p(Ω)`. -/
theorem translate_neg_translate (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : Lp F p (μ.restrict (Ω : Set E))) :
    translate F p hΩ.neg (translate F p hΩ u) = u := by
  refine Lp.ext ?_
  have h1 := coeFn_translate hΩ.neg (translate F p hΩ u)
  have h2 := hΩ.neg.measurePreserving.quasiMeasurePreserving.ae_eq_comp (coeFn_translate hΩ u)
  refine h1.trans (h2.trans (Eventually.of_forall fun x ↦ ?_))
  simp

/-- **Adjointness of the translations in `L²(Ω)`**: `⟪τ_h u, v⟫ = ⟪u, τ_{−h} v⟫`, by the change of
variables `x ↦ x − h`. -/
theorem inner_translate (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u v : Lp ℝ 2 (μ.restrict (Ω : Set E))) :
    ⟪translate ℝ 2 hΩ u, v⟫_ℝ = ⟪u, translate ℝ 2 hΩ.neg v⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  have e1 : ∫ x, ⟪translate ℝ 2 hΩ u x, v x⟫_ℝ ∂(μ.restrict (Ω : Set E))
      = ∫ x, u (x + h) * v x ∂(μ.restrict (Ω : Set E)) := by
    refine integral_congr_ae ((coeFn_translate hΩ u).mono fun x hx ↦ ?_)
    simp [hx, mul_comm]
  have e2 : ∫ x, ⟪u x, translate ℝ 2 hΩ.neg v x⟫_ℝ ∂(μ.restrict (Ω : Set E))
      = ∫ x, u x * v (x + -h) ∂(μ.restrict (Ω : Set E)) := by
    refine integral_congr_ae ((coeFn_translate hΩ.neg v).mono fun x hx ↦ ?_)
    simp [hx, mul_comm]
  rw [e1, e2, ← hΩ.measurePreserving.integral_comp (MeasurableEquiv.addRight h).measurableEmbedding
    (fun x ↦ u x * v (x + -h))]
  simp only [add_neg_cancel_right]

end MeasureTheory.Lp

/-! ### Translations on `W^{k,p}(Ω)` -/

namespace SobolevMultiIndex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} [Fintype ι] [LinearOrder ι] {b : Basis ι ℝ E} {k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens E} {μ : Measure E} [μ.IsAddRightInvariant] {h : E}

variable (F b k p μ) in
/-- The family of the translates of the weak derivatives of `u ∈ W^{k,p}(Ω)`, as an element of
the ambient `ℓ^p` product. -/
def translateTuple (hΩ : IsTranslationInvariant (Ω : Set E) h) (u : SobolevMultiIndex F b k p Ω μ) :
    SobolevMultiIndexTuple F ι k p Ω μ :=
  WithLp.toLp p fun α ↦ Lp.translate F p hΩ (weakDeriv u α)

/-- The translated family lies in `W^{k,p}(Ω)`: translation commutes with the weak derivatives
(`HasWeakIteratedLineDerivOn.comp_add_right`). -/
theorem translateTuple_mem (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : SobolevMultiIndex F b k p Ω μ) :
    translateTuple F b k p μ hΩ u ∈ SobolevMultiIndex F b k p Ω μ := fun α ↦
  ((hasWeakIteratedLineDerivOn u α).comp_add_right hΩ).congr_ae
    (Lp.coeFn_translate hΩ (weakDeriv u 0)).symm (Lp.coeFn_translate hΩ (weakDeriv u α)).symm

variable (F b k p μ) in
/-- **Translation by `h` as a linear isometry of `W^{k,p}(Ω)`**, for an open set `Ω` invariant
under the translation: every weak derivative is translated
(`HasWeakIteratedLineDerivOn.comp_add_right`), and each `L^p(Ω)` norm is preserved. This is the
map `u ↦ τ_h u` of [brezis2011functional] §9.6, and the invariance of `H^1_0(ℝ^N_+)` under the
tangential translations is `SobolevMultiIndex.translateL_mem_zero`. -/
def translateL (hΩ : IsTranslationInvariant (Ω : Set E) h) :
    SobolevMultiIndex F b k p Ω μ →ₗᵢ[ℝ] SobolevMultiIndex F b k p Ω μ where
  toLinearMap :=
    { toFun := fun u ↦ ⟨translateTuple F b k p μ hΩ u, translateTuple_mem hΩ u⟩
      map_add' := fun u v ↦ Subtype.ext (PiLp.ext fun α ↦ by
        exact map_add (Lp.translate F p hΩ) (weakDeriv u α) (weakDeriv v α))
      map_smul' := fun c u ↦ Subtype.ext (PiLp.ext fun α ↦ by
        exact map_smul (Lp.translate F p hΩ) c (weakDeriv u α)) }
  norm_map' u := by
    rw [← Submodule.norm_coe, ← Submodule.norm_coe]
    refine le_antisymm (PiLp.norm_le_norm_of_forall_norm_le fun α ↦ ?_)
      (PiLp.norm_le_norm_of_forall_norm_le fun α ↦ ?_)
    · exact (LinearIsometry.norm_map _ _).le
    · exact (LinearIsometry.norm_map _ _).symm.le

/-- The weak derivatives of the translate are the translates of the weak derivatives, as elements
of `L^p(Ω)`. -/
theorem weakDeriv_translateL (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : SobolevMultiIndex F b k p Ω μ) (α : MultiIndexLE ι k) :
    weakDeriv (translateL F b k p μ hΩ u) α = Lp.translate F p hΩ (weakDeriv u α) :=
  rfl

/-- The function of the translate is the translate of the function, almost everywhere on `Ω`. -/
theorem fn_translateL (hΩ : IsTranslationInvariant (Ω : Set E) h)
    (u : SobolevMultiIndex F b k p Ω μ) :
    fn (translateL F b k p μ hΩ u) =ᵐ[μ.restrict (Ω : Set E)] fun x ↦ fn u (x + h) :=
  Lp.coeFn_translate hΩ (weakDeriv u 0)

/-- **`W_0^{k,p}(Ω)` is invariant under the translations that leave `Ω` invariant**
([brezis2011functional] §9.6, (54): "`H^1_0(Ω)` is invariant under tangential translations"):
the translate of a test function on `Ω` is a test function on `Ω`, and the translation is
continuous on `W^{k,p}(Ω)`, so it preserves the closure of the test functions. -/
theorem translateL_mem_zero (hΩ : IsTranslationInvariant (Ω : Set E) h)
    {u : SobolevMultiIndex F b k p Ω μ} (hu : u ∈ SobolevMultiIndexZero F b k p Ω μ) :
    translateL F b k p μ hΩ u ∈ SobolevMultiIndexZero F b k p Ω μ := by
  have hT : ∀ v ∈ testFunctions F b k p Ω μ,
      translateL F b k p μ hΩ v ∈ testFunctions F b k p Ω μ := by
    rintro v ⟨φ, hφ⟩
    refine ⟨φ.compAddRightOn hΩ, (fn_translateL hΩ v).trans ?_⟩
    rw [TestFunction.compAddRightOn_coe]
    exact hΩ.measurePreserving.quasiMeasurePreserving.ae_eq_comp hφ
  have hmem : u ∈ closure (testFunctions F b k p Ω μ : Set (SobolevMultiIndex F b k p Ω μ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hu
  change translateL F b k p μ hΩ u ∈ (SobolevMultiIndexZero F b k p Ω μ : Set _)
  rw [SobolevMultiIndexZero, Submodule.topologicalClosure_coe]
  refine closure_mono (image_subset_iff.2 hT) ?_
  exact image_closure_subset_closure_image (translateL F b k p μ hΩ).continuous ⟨u, hmem, rfl⟩

end SobolevMultiIndex

/-! ### Translation to a translated domain

The translation `u ↦ u(· + h)` carries `W^{1,p}(Ω)` to `W^{1,p}(Ω − h)`, with the weak
derivatives translated. The sections above treat an open set invariant under the translation;
this one is the version for `Ω' = (· + h) ⁻¹' Ω`, the translated domain, which the density of
smooth functions on a segment-property domain needs. -/

section TranslatePreimage

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
  {Ω Ω' : Opens E} {h : E}

/-- The translate `x ↦ φ (x - h)` of a test function on `Ω' = Ω − h`, as a test function on
`Ω`. -/
def TestFunction.compSubRightOfPreimage (φ : 𝓓(Ω', F))
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) : 𝓓(Ω, F) where
  toFun x := φ (x - h)
  contDiff' := φ.contDiff.comp (contDiff_id.sub contDiff_const)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight h)
  tsupport_subset' := by
    have : tsupport (fun x ↦ φ (x - h)) = (Homeomorph.subRight h) ⁻¹' tsupport φ := by
      rw [tsupport, tsupport, (Homeomorph.subRight h).preimage_closure]
      rfl
    rw [this]
    intro x hx
    have := φ.tsupport_subset hx
    rw [hΩ'] at this
    simpa using this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The translate of a function locally integrable on `Ω` is locally integrable on `Ω − h`. -/
theorem LocallyIntegrableOn.comp_add_right_of_preimage [μ.IsAddRightInvariant] [ProperSpace E]
    {u : E → F} (hu : LocallyIntegrableOn u Ω μ)
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    LocallyIntegrableOn (fun x ↦ u (x + h)) Ω' μ := by
  rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed] at hu
  rw [locallyIntegrableOn_iff Ω'.isOpen.isLocallyClosed]
  intro k hk hkc
  have hk' : (· + h) '' k ⊆ (Ω : Set E) := by
    rintro _ ⟨x, hx, rfl⟩
    have := hk hx
    rw [hΩ'] at this
    exact this
  have := hu ((· + h) '' k) hk' (hkc.image (continuous_id.add continuous_const))
  exact ((measurePreserving_add_right μ h).integrableOn_image
    (MeasurableEquiv.addRight h).measurableEmbedding).1 this

omit [NormedSpace ℝ E] in
/-- The translation `x ↦ x + h` carries `μ.restrict (Ω − h)` to `μ.restrict Ω`. -/
theorem measurePreserving_add_right_restrict_of_preimage [μ.IsAddRightInvariant]
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    MeasurePreserving (· + h) (μ.restrict (Ω' : Set E)) (μ.restrict (Ω : Set E)) := by
  have := (measurePreserving_add_right μ h).restrict_preimage Ω.isOpen.measurableSet
  rwa [← hΩ'] at this

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The translate of an `L^p(Ω)` function lies in `L^p(Ω − h)`. -/
theorem MeasureTheory.MemLp.comp_add_right_of_preimage [μ.IsAddRightInvariant] {u : E → F}
    {p : ℝ≥0∞} (hu : MemLp u p (μ.restrict (Ω : Set E)))
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    MemLp (fun x ↦ u (x + h)) p (μ.restrict (Ω' : Set E)) :=
  hu.comp_measurePreserving (measurePreserving_add_right_restrict_of_preimage hΩ')

/-- The change of variables `x ↦ x + h` from `Ω − h` to `Ω`, against a test function on `Ω − h`:
`∫_{Ω − h} ψ(x) u(x + h) dx = ∫_Ω ψ(x − h) u(x) dx`. -/
theorem integral_smul_comp_add_right_of_preimage [μ.IsAddRightInvariant] (u : E → F)
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) (ψ : 𝓓(Ω', ℝ)) :
    ∫ x in (Ω' : Set E), ψ x • u (x + h) ∂μ = ∫ x in (Ω : Set E), ψ (x - h) • u x ∂μ := by
  have e1 : ∫ x in (Ω' : Set E), ψ x • u (x + h) ∂μ = ∫ x, ψ x • u (x + h) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [ψ.eq_zero_of_notMem hx, zero_smul]
  have e2 : ∫ x in (Ω : Set E), ψ (x - h) • u x ∂μ = ∫ x, ψ (x - h) • u x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      have := (ψ.compSubRightOfPreimage hΩ').eq_zero_of_notMem hx
      exact by rw [show ψ (x - h) = 0 from this, zero_smul]
  rw [e1, e2, ← integral_add_right_eq_self (fun x ↦ ψ (x - h) • u x) h]
  simp only [add_sub_cancel_right]

/-- **Translation commutes with the weak derivative, from `Ω` to `Ω − h`**: if `w` is a weak
derivative of `u` along the tuple `y` on `Ω`, then `w(· + h)` is one of `u(· + h)` on `Ω − h`.
The test function `φ` on `Ω − h` is traded for its translate `φ(· − h)`, a test function on
`Ω`. -/
theorem HasWeakIteratedLineDerivOn.comp_add_right_of_preimage [μ.IsAddRightInvariant]
    [ProperSpace E] {n : ℕ} {y : Fin n → E} {u w : E → F}
    (hu : HasWeakIteratedLineDerivOn y u w Ω μ)
    (hΩ' : (Ω' : Set E) = (fun x ↦ x + h) ⁻¹' Ω) :
    HasWeakIteratedLineDerivOn y (fun x ↦ u (x + h)) (fun x ↦ w (x + h)) Ω' μ where
  locallyIntegrableOn := LocallyIntegrableOn.comp_add_right_of_preimage hu.locallyIntegrableOn hΩ'
  locallyIntegrableOn_weakDeriv :=
    LocallyIntegrableOn.comp_add_right_of_preimage hu.locallyIntegrableOn_weakDeriv hΩ'
  integral_smul_eq φ := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : 𝓓(Ω, ℝ), (ψ : E → ℝ) = fun x ↦ φ (x - h) :=
      ⟨φ.compSubRightOfPreimage hΩ', rfl⟩
    have hψd : ∀ x, iteratedFDeriv ℝ n (ψ : E → ℝ) x y
        = iteratedFDeriv ℝ n (φ : E → ℝ) (x - h) y := fun x ↦ by
      rw [hψ, iteratedFDeriv_comp_sub']
    have e1 : ∫ x in (Ω' : Set E), iteratedFDeriv ℝ n φ x y • u (x + h) ∂μ
        = ∫ x in (Ω : Set E), iteratedFDeriv ℝ n ψ x y • u x ∂μ := by
      have := integral_smul_comp_add_right_of_preimage (μ := μ) u hΩ' (φ.iteratedFDerivApply n y)
      simp only [TestFunction.iteratedFDerivApply_apply] at this
      rw [this]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hψd])
    have e2 : ∫ x in (Ω' : Set E), φ x • w (x + h) ∂μ = ∫ x in (Ω : Set E), ψ x • w x ∂μ := by
      rw [integral_smul_comp_add_right_of_preimage (μ := μ) w hΩ' φ]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [hψ])
    rw [e1, e2, hu.integral_smul_eq ψ]

end TranslatePreimage


/-- The support of `x ↦ θ (x + h)` lies in the translate of the support of `θ`. -/
theorem tsupport_comp_add_right_subset {E : Type*} [NormedAddCommGroup E] {θ : E → ℝ} (h : E) :
    tsupport (fun x ↦ θ (x + h)) ⊆ (fun x ↦ x + h) ⁻¹' tsupport θ :=
  closure_minimal (fun y hy ↦ subset_closure (by simpa [Function.support] using hy))
    ((isClosed_tsupport θ).preimage (continuous_add_const h))

end
