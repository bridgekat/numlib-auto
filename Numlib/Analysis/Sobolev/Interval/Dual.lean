/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Distribution.Sobolev`, beside the material of
`Numlib/Analysis/Sobolev/Interval/Basic.lean`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Numlib.Analysis.Sobolev.Interval.Zero

/-!
# The dual space `W^{-1,p'}(I)` of `W_0^{1,p}(I)`

The dual of `W_0^{1,p}(I)`, [brezis2011functional] §8.3, "The dual space of `W_0^{1,p}(I)`": the
notation `W^{-1,p'}(I)`, the inclusions `W_0^{1,p} ⊆ L² ⊆ W^{-1,p'}` (continuous, injective,
with dense ranges), the representation of Proposition 8.14 and Remark 21
(`⟨F, u⟩ = ∫ f₀ u + ∫ f₁ u'` with `f₀, f₁ ∈ L^{p'}(I)`) and Remark 19 (its non-uniqueness).

## Main definitions and statements

* `SobolevIntervalLpDual p I := StrongDual ℝ (SobolevIntervalLpZero 1 p I)`, the space
  `W^{-1,p'}(I)`, `H^{-1}(I)` at `p = 2`; a Banach space.
* `SobolevIntervalLpZero.toL2` (`p ≤ 2`, any interval) and `SobolevIntervalLpZero.toL2OfBounded`
  (bounded interval, any `p`): the inclusion `W_0^{1,p}(I) ⊆ L²(I)`, injective
  (`toL2_injective`, `toL2OfBounded_injective`) and with dense range (`denseRange_toL2`,
  `denseRange_toL2OfBounded`, `p < ∞`).
* `SobolevIntervalLpDual.ofL2`, `ofL2OfBounded`: the inclusion `L²(I) ⊆ W^{-1,p'}(I)`,
  `f ↦ (u ↦ ∫_I f u)`, the transpose of the previous one through the self-duality of `L²`;
  injective (`ofL2_injective`, `p < ∞`) and with dense range for `1 < p < ∞`
  (`denseRange_ofL2`, `denseRange_ofL2OfBounded`, by the reflexivity of `W_0^{1,p}(I)`). At
  `p = 2` these are the book's `H_0^1 ⊆ L² ⊆ H^{-1}`.
* `SobolevIntervalLp.exists_repr_strongDual` (**Remark 21**): for `1 ≤ p < ∞`, every continuous
  linear functional on `W^{1,p}(I)` is `u ↦ ∫_I f₀ u + ∫_I f₁ u'` for some `f₀, f₁ ∈ L^{p'}(I)`,
  with `‖F‖ = ‖(f₀, f₁)‖_{ℓ^{p'}}`;
  `SobolevIntervalLpDual.exists_repr` (**Proposition 8.14**): the same for functionals on
  `W_0^{1,p}(I)`, and `SobolevIntervalLpDual.exists_repr_of_bounded`: on a bounded interval
  `f₀ = 0` can be taken.
* `SobolevIntervalLpDual.repr_not_unique` (**Remark 19**): the pair `(f₀, f₁)` is not unique —
  `(f₀ + g', f₁ + g)` represents the same functional for every test function `g`.

## Design

* The norm identity of Proposition 8.14 is stated for the norm the type carries: `W^{1,p}(I)`
  sits isometrically in the `ℓ^p` product `PiLp p (Fin 2 → L^p(I))`, so the dual norm of the
  representing pair is its `ℓ^{p'}` norm, `(‖f₀‖_{p'}^{p'} + ‖f₁‖_{p'}^{p'})^{1/p'}`
  (`max (‖f₀‖_∞) (‖f₁‖_∞)` at `p = 1`, where the type's norm is the book's sum norm and this is
  the book's identity). The general step is the duality of a finite `ℓ^p` product,
  `PiLp.norm_strongDual_eq`.
* The inclusion `W_0^{1,p}(I) ⊆ L²(I)` is `SobolevIntervalLp.toLp` (Remark 12) when `p ≤ 2` and
  `SobolevIntervalLp.toLpOfBounded` on a bounded interval, restricted to `W_0^{1,p}(I)`; the
  properties of `L² ⊆ W^{-1,p'}` are proved once for any inclusion `T : W_0^{1,p}(I) →L L²(I)`
  whose values are the functions (`SobolevIntervalLpDual.ofL2Of T`), and specialized.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Topology

noncomputable section

/-! ### The space `W^{-1,p'}(I)` -/

/-- **The dual space `W^{-1,p'}(I)` of `W_0^{1,p}(I)`** ([brezis2011functional] §8.3, Notation),
`H^{-1}(I)` at `p = 2`: the strong dual of `SobolevIntervalLpZero 1 p I`. A Banach space, being
a dual. -/
abbrev SobolevIntervalLpDual (p : ℝ≥0∞) [Fact (1 ≤ p)] (I : Opens ℝ) : Type :=
  StrongDual ℝ (SobolevIntervalLpZero 1 p I)

/-! ### The inclusion `W_0^{1,p}(I) ⊆ L²(I)` -/

namespace SobolevIntervalLpZero

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

open SobolevIntervalLp

variable (p I) in
/-- **The inclusion `W_0^{1,p}(I) ⊆ L²(I)` for `p ≤ 2`** ([brezis2011functional] §8.3, the
inclusions `W_0^{1,p} ⊆ L² ⊆ W^{-1,p'}` on an unbounded interval, `1 ≤ p ≤ 2`): the inclusion
`W^{1,p}(I) ⊆ L²(I)` of Remark 12 restricted to `W_0^{1,p}(I)`. -/
def toL2 (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ)) :=
  (SobolevIntervalLp.toLp p hI hp).comp (SobolevIntervalLpZero 1 p I).subtypeL

/-- The inclusion into `L²(I)` is the function, almost everywhere. -/
theorem coeFn_toL2 (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) (u : SobolevIntervalLpZero 1 p I) :
    ⇑(toL2 p I hI hp u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I) := by
  rw [toL2, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact coeFn_toLp hI hp u

variable {a b : ℝ}

variable (p) in
/-- **The inclusion `W_0^{1,p}(a, b) ⊆ L²(a, b)`** on a bounded interval, every `1 ≤ p ≤ ∞`
([brezis2011functional] §8.3, the inclusions `W_0^{1,p} ⊆ L² ⊆ W^{-1,p'}` on a bounded
interval): `SobolevIntervalLp.toLpOfBounded` restricted to `W_0^{1,p}(a, b)`. -/
def toL2OfBounded (hab : a < b) :
    SobolevIntervalLpZero 1 p (Opens.Ioo a b) →L[ℝ] Lp ℝ 2 (volume.restrict (Ioo a b)) :=
  (SobolevIntervalLp.toLpOfBounded p hab 2).comp
    (SobolevIntervalLpZero 1 p (Opens.Ioo a b)).subtypeL

/-- The inclusion into `L²(a, b)` is the function, almost everywhere. -/
theorem coeFn_toL2OfBounded (hab : a < b) (u : SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
    ⇑(toL2OfBounded p hab u) =ᵐ[volume.restrict (Ioo a b)]
      fn (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) := by
  rw [toL2OfBounded, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact coeFn_toLpOfBounded hab 2 (u : SobolevIntervalLp 1 p (Opens.Ioo a b))

/-- An inclusion `W_0^{1,p}(I) → L²(I)` whose values are the functions is injective: two
elements with the same function are equal (`SobolevMultiIndex.ext_of_fn_ae_eq`). -/
theorem injective_of_coeFn_ae_eq (T : SobolevIntervalLpZero 1 p I →L[ℝ]
      Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (hT : ∀ u, ⇑(T u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I)) :
    Function.Injective T := by
  intro u v huv
  refine Subtype.ext (SobolevMultiIndex.ext_of_fn_ae_eq ?_)
  refine (hT u).symm.trans ?_
  rw [huv]
  exact hT v

/-- `W_0^{1,p}(I) ⊆ L²(I)` is injective. -/
theorem toL2_injective (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    Function.Injective (toL2 p I hI hp) :=
  injective_of_coeFn_ae_eq _ (coeFn_toL2 hI hp)

/-- `W_0^{1,p}(a, b) ⊆ L²(a, b)` is injective. -/
theorem toL2OfBounded_injective (hab : a < b) : Function.Injective (toL2OfBounded p hab) :=
  injective_of_coeFn_ae_eq _ (coeFn_toL2OfBounded hab)

/-- An inclusion `W_0^{1,p}(I) → L²(I)` whose values are the functions has dense range: its range
contains the test functions, which are dense in `L²(I)`
(`MeasureTheory.Lp.dense_contDiff_tsupport_subset`). -/
theorem denseRange_of_coeFn_ae_eq (T : SobolevIntervalLpZero 1 p I →L[ℝ]
      Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (hT : ∀ u, ⇑(T u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I)) :
    DenseRange T := by
  refine (Lp.dense_contDiff_tsupport_subset (F := ℝ) (μ := volume) (p := 2) I.isOpen
    ENNReal.ofNat_ne_top).mono ?_
  rintro f ⟨g, hfg, hgc, hgs, hgI⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓(I, ℝ), (φ : ℝ → ℝ) = g := ⟨⟨g, hgs, hgc, hgI⟩, rfl⟩
  refine ⟨⟨TestFunction.toSobolevIntervalLp p φ, TestFunction.toSobolevIntervalLp_mem (p := p) φ⟩,
    ?_⟩
  refine Lp.ext ((hT _).trans ?_)
  refine (TestFunction.fn_toSobolevIntervalLp_ae_eq (p := p) φ).trans ?_
  rw [hφ]
  exact hfg.symm

/-- **`W_0^{1,p}(I) ⊆ L²(I)` has dense range**, `1 ≤ p ≤ 2`. -/
theorem denseRange_toL2 (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    DenseRange (toL2 p I hI hp) :=
  denseRange_of_coeFn_ae_eq _ (coeFn_toL2 hI hp)

/-- **`W_0^{1,p}(a, b) ⊆ L²(a, b)` has dense range**, `1 ≤ p ≤ ∞`. -/
theorem denseRange_toL2OfBounded (hab : a < b) : DenseRange (toL2OfBounded p hab) :=
  denseRange_of_coeFn_ae_eq _ (coeFn_toL2OfBounded hab)

end SobolevIntervalLpZero

/-! ### The inclusion `L²(I) ⊆ W^{-1,p'}(I)` -/

namespace SobolevIntervalLpDual

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

open SobolevIntervalLp

/-- **The inclusion `L²(I) ⊆ W^{-1,p'}(I)` along an inclusion `T : W_0^{1,p}(I) → L²(I)`**:
`f ↦ (u ↦ ∫_I f (T u))`, the transpose of `T` composed with the self-duality of `L²(I)`
(the `L^p`–`L^q` pairing `MeasureTheory.Lp.toDualCLM` at `p = q = 2`). -/
def ofL2Of (T : SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ))) :
    Lp ℝ 2 (volume.restrict (I : Set ℝ)) →L[ℝ] SobolevIntervalLpDual p I :=
  ((ContinuousLinearMap.compL ℝ (SobolevIntervalLpZero 1 p I)
    (Lp ℝ 2 (volume.restrict (I : Set ℝ))) ℝ).flip T).comp
    (Lp.toDualCLM ℝ 2 2 (volume.restrict (I : Set ℝ)))

/-- `ofL2Of T f u = ∫_I f (T u)`. -/
theorem ofL2Of_apply (T : SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (f : Lp ℝ 2 (volume.restrict (I : Set ℝ))) (u : SobolevIntervalLpZero 1 p I) :
    ofL2Of T f u = ∫ x in (I : Set ℝ), f x * T u x := by
  simp only [ofL2Of, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, Lp.toDualCLM_apply]

/-- `ofL2Of T f u = ∫_I f u` when `T` is an inclusion whose values are the functions. -/
theorem ofL2Of_apply_eq_integral_mul_fn
    (T : SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (hT : ∀ u, ⇑(T u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I))
    (f : Lp ℝ 2 (volume.restrict (I : Set ℝ))) (u : SobolevIntervalLpZero 1 p I) :
    ofL2Of T f u = ∫ x in (I : Set ℝ), f x * fn (u : SobolevIntervalLp 1 p I) x := by
  rw [ofL2Of_apply]
  exact integral_congr_ae ((hT u).mono fun x hx ↦ by simp only [hx])

/-- **`L²(I) ⊆ W^{-1,p'}(I)` is injective**: a function of `L²(I)` whose integral against every
test function vanishes is zero. -/
theorem ofL2Of_injective
    (T : SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (hT : ∀ u, ⇑(T u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I)) :
    Function.Injective (ofL2Of T) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf ↦ ?_
  have hloc : LocallyIntegrableOn (⇑f) I (volume.restrict (I : Set ℝ)) :=
    ((Lp.memLp f).locallyIntegrable one_le_two).locallyIntegrableOn _
  have key := I.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hgs hgc hgI ↦ ?_
  · refine Lp.ext ?_
    filter_upwards [key, ae_restrict_mem I.isOpen.measurableSet, Lp.coeFn_zero ℝ 2
      (volume.restrict (I : Set ℝ))] with x hx hxI hx0
    rw [hx hxI, hx0]
    rfl
  · obtain ⟨φ, hφ⟩ : ∃ φ : 𝓓(I, ℝ), (φ : ℝ → ℝ) = g := ⟨⟨g, hgs, hgc, hgI⟩, rfl⟩
    have h1 := DFunLike.congr_fun hf
      ⟨TestFunction.toSobolevIntervalLp p φ, TestFunction.toSobolevIntervalLp_mem (p := p) φ⟩
    rw [ofL2Of_apply_eq_integral_mul_fn T hT, zero_apply] at h1
    rw [← h1, ← hφ]
    refine integral_congr_ae
      ((TestFunction.fn_toSobolevIntervalLp_ae_eq (p := p) φ).mono fun x hx ↦ ?_)
    simp only [smul_eq_mul, mul_comm, hx]

/-- **`L²(I) ⊆ W^{-1,p'}(I)` has dense range for `1 < p < ∞`**: a functional on `W^{-1,p'}(I)`
vanishing on the range is, by the reflexivity of `W_0^{1,p}(I)`
(`SobolevMultiIndexZero.instIsReflexive`), evaluation at some `v ∈ W_0^{1,p}(I)`, so
`∫_I f v = 0` for all `f ∈ L²(I)`, in particular for `f = T v`, so `T v = 0` and `v = 0`; a
closed proper subspace would be separated from a point by a nonzero functional
(`Submodule.exists_dual_eq_zero_of_notMem`). -/
theorem denseRange_ofL2Of [Fact (1 < p)] [Fact (p ≠ ⊤)]
    (T : SobolevIntervalLpZero 1 p I →L[ℝ] Lp ℝ 2 (volume.restrict (I : Set ℝ)))
    (hT : ∀ u, ⇑(T u) =ᵐ[volume.restrict I] fn (u : SobolevIntervalLp 1 p I)) :
    DenseRange (ofL2Of T) := by
  have hTinj := SobolevIntervalLpZero.injective_of_coeFn_ae_eq T hT
  obtain ⟨M, hM⟩ : ∃ M : Submodule ℝ (SobolevIntervalLpDual p I),
      M = (LinearMap.range (ofL2Of T : Lp ℝ 2 (volume.restrict (I : Set ℝ)) →ₗ[ℝ]
        SobolevIntervalLpDual p I)).topologicalClosure := ⟨_, rfl⟩
  have hMtop : M = ⊤ := by
    by_contra hne
    obtain ⟨z, -, hz⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
    obtain ⟨Λ, -, hΛ0, hΛz⟩ :=
      M.exists_dual_eq_zero_of_notMem (hM ▸ Submodule.isClosed_topologicalClosure _) hz
    obtain ⟨v, rfl⟩ := NormedSpace.surjective_inclusionInDoubleDual (𝕜 := ℝ) Λ
    have hv : ∀ f : Lp ℝ 2 (volume.restrict (I : Set ℝ)), ofL2Of T f v = 0 := fun f ↦ by
      have := hΛ0 (ofL2Of T f) (hM ▸ Submodule.le_topologicalClosure _ ⟨f, rfl⟩)
      rwa [NormedSpace.dual_def] at this
    have hTv : T v = 0 := by
      have h := hv (T v)
      rw [ofL2Of_apply] at h
      have h2 : ∫ x in (I : Set ℝ), (T v) x * (T v) x = ‖T v‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp [pow_two])
      rw [h2] at h
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
    have hv0 : v = 0 := hTinj (hTv.trans (map_zero T).symm)
    apply hΛz
    rw [hv0, map_zero]
    rfl
  have hrange : Set.range (ofL2Of T) = ((LinearMap.range (ofL2Of T :
      Lp ℝ 2 (volume.restrict (I : Set ℝ)) →ₗ[ℝ] SobolevIntervalLpDual p I)) : Set _) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  rw [DenseRange, hrange, Submodule.dense_iff_topologicalClosure_eq_top, ← hM, hMtop]

variable (p I) in
/-- **The inclusion `L²(I) ⊆ W^{-1,p'}(I)` for `p ≤ 2`**: `f ↦ (u ↦ ∫_I f u)`, the transpose of
`SobolevIntervalLpZero.toL2` through the self-duality of `L²(I)`
([brezis2011functional] §8.3, the inclusions `W_0^{1,p} ⊆ L² ⊆ W^{-1,p'}`). -/
def ofL2 (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    Lp ℝ 2 (volume.restrict (I : Set ℝ)) →L[ℝ] SobolevIntervalLpDual p I :=
  ofL2Of (SobolevIntervalLpZero.toL2 p I hI hp)

/-- `ofL2 f u = ∫_I f u`. -/
theorem ofL2_apply (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2)
    (f : Lp ℝ 2 (volume.restrict (I : Set ℝ))) (u : SobolevIntervalLpZero 1 p I) :
    ofL2 p I hI hp f u = ∫ x in (I : Set ℝ), f x * fn (u : SobolevIntervalLp 1 p I) x :=
  ofL2Of_apply_eq_integral_mul_fn _ (SobolevIntervalLpZero.coeFn_toL2 hI hp) f u

/-- `L²(I) ⊆ W^{-1,p'}(I)` is injective. -/
theorem ofL2_injective (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    Function.Injective (ofL2 p I hI hp) :=
  ofL2Of_injective _ (SobolevIntervalLpZero.coeFn_toL2 hI hp)

/-- **`L²(I) ⊆ W^{-1,p'}(I)` has dense range** for `1 < p ≤ 2`. -/
theorem denseRange_ofL2 [Fact (1 < p)] (hI : (I : Set ℝ).OrdConnected) (hp : p ≤ 2) :
    DenseRange (ofL2 p I hI hp) :=
  have : Fact (p ≠ ⊤) := ⟨ne_top_of_le_ne_top ENNReal.ofNat_ne_top hp⟩
  denseRange_ofL2Of _ (SobolevIntervalLpZero.coeFn_toL2 hI hp)

variable {a b : ℝ}

variable (p) in
/-- **The inclusion `L²(a, b) ⊆ W^{-1,p'}(a, b)`** on a bounded interval, every `1 ≤ p ≤ ∞`:
`f ↦ (u ↦ ∫_a^b f u)`, the transpose of `SobolevIntervalLpZero.toL2OfBounded`. -/
def ofL2OfBounded (hab : a < b) :
    Lp ℝ 2 (volume.restrict (Ioo a b)) →L[ℝ] SobolevIntervalLpDual p (Opens.Ioo a b) :=
  ofL2Of (SobolevIntervalLpZero.toL2OfBounded p hab)

/-- `ofL2OfBounded f u = ∫_a^b f u`. -/
theorem ofL2OfBounded_apply (hab : a < b) (f : Lp ℝ 2 (volume.restrict (Ioo a b)))
    (u : SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
    ofL2OfBounded p hab f u
      = ∫ x in Ioo a b, f x * fn (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) x :=
  ofL2Of_apply_eq_integral_mul_fn _ (SobolevIntervalLpZero.coeFn_toL2OfBounded hab) f u

/-- `L²(a, b) ⊆ W^{-1,p'}(a, b)` is injective. -/
theorem ofL2OfBounded_injective (hab : a < b) :
    Function.Injective (ofL2OfBounded p hab) :=
  ofL2Of_injective _ (SobolevIntervalLpZero.coeFn_toL2OfBounded hab)

/-- **`L²(a, b) ⊆ W^{-1,p'}(a, b)` has dense range** for `1 < p < ∞`
([brezis2011functional] §8.3, "dense injections when `1 < p < ∞`"). -/
theorem denseRange_ofL2OfBounded [Fact (1 < p)] [Fact (p ≠ ⊤)] (hab : a < b) :
    DenseRange (ofL2OfBounded p hab) :=
  denseRange_ofL2Of _ (SobolevIntervalLpZero.coeFn_toL2OfBounded hab)

end SobolevIntervalLpDual

/-! ### The dual of a finite `ℓ^p` product -/

namespace PiLp

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)]
  [∀ i, NormedSpace ℝ (X i)] {p : ℝ≥0∞}

variable (p) in
/-- The inclusion of the `i`-th factor into the `ℓ^p` product, as a continuous linear map. -/
def singleL (i : ι) : X i →L[ℝ] PiLp p X :=
  (continuousLinearEquiv p ℝ X).symm.toContinuousLinearMap.comp (ContinuousLinearMap.single ℝ X i)

/-- `singleL p i b` is `PiLp.single p i b`. -/
theorem singleL_apply (i : ι) (b : X i) : singleL p i b = single p i b := rfl

variable [Fintype ι] [Fact (1 ≤ p)]

/-- The inclusion of a factor is isometric. -/
theorem norm_singleL_apply (i : ι) (b : X i) : ‖singleL p i b‖ = ‖b‖ := by
  rw [singleL_apply, ← coe_nnnorm, nnnorm_single, coe_nnnorm]

/-- The inclusion of a factor has norm at most `1`. -/
theorem norm_singleL_le (i : ι) : ‖singleL p (X := X) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b ↦ by
    rw [norm_singleL_apply, one_mul]

omit [Fact (1 ≤ p)] in
/-- Every element of the product is the sum of its coordinates. -/
theorem sum_singleL_apply (x : PiLp p X) : ∑ i, singleL p i (x i) = x := by
  refine (continuousLinearEquiv p ℝ X).injective ?_
  rw [map_sum]
  simp only [singleL, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  exact Finset.univ_sum_single _

omit [Fact (1 ≤ p)] in
/-- A functional on the product is the sum of its restrictions to the factors. -/
theorem strongDual_apply_eq_sum (Φ : StrongDual ℝ (PiLp p X)) (x : PiLp p X) :
    Φ x = ∑ i, Φ.comp (singleL p i) (x i) := by
  conv_lhs => rw [← sum_singleL_apply x]
  rw [map_sum]
  rfl

/-- The restriction of a functional to a factor has norm at most that of the functional. -/
theorem norm_strongDual_comp_singleL_le (Φ : StrongDual ℝ (PiLp p X)) (i : ι) :
    ‖Φ.comp (singleL p i)‖ ≤ ‖Φ‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left (norm_singleL_le (p := p) i) (norm_nonneg Φ))

/-- **The dual of a finite `ℓ^p` product, `1 ≤ p < ∞`**: the norm of a functional `Φ` on
`PiLp p X` is the `ℓ^q` norm of the tuple of the norms of its restrictions `Φ ∘ single i` to the
factors, `q` the conjugate exponent — `(∑ ‖Φ ∘ single i‖^q)^{1/q}` for `1 < p < ∞`,
`max ‖Φ ∘ single i‖` for `p = 1`. The upper bound is Hölder's inequality for finite sums; the
lower bound tests `Φ` against `(‖Φ ∘ single i‖^{q - 1} y i)_i` with `y i` almost extremal for
`Φ ∘ single i`. -/
theorem norm_strongDual_eq {q : ℝ≥0∞} [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤)
    (Φ : StrongDual ℝ (PiLp p X)) :
    ‖Φ‖ = ‖(WithLp.toLp q fun i ↦ ‖Φ.comp (singleL p i)‖ : PiLp q fun _ : ι ↦ ℝ)‖ := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ∀ i, StrongDual ℝ (X i), ∀ i, ψ i = Φ.comp (singleL p i) :=
    ⟨_, fun _ ↦ rfl⟩
  have hψle : ∀ i, ‖ψ i‖ ≤ ‖Φ‖ := fun i ↦ by rw [hψ]; exact norm_strongDual_comp_singleL_le Φ i
  have hΦx : ∀ x : PiLp p X, Φ x = ∑ i, ψ i (x i) := fun x ↦ by
    simp only [hψ]; exact strongDual_apply_eq_sum Φ x
  have hnorm : ∀ i, ‖(‖ψ i‖)‖ = ‖ψ i‖ := fun i ↦ Real.norm_of_nonneg (norm_nonneg _)
  simp only [← hψ]
  rcases eq_or_ne q ⊤ with rfl | hq
  · -- `p = 1`: the sup norm of the tuple
    have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).1 rfl
    subst hp1
    rw [norm_eq_ciSup]
    simp only [hnorm]
    rcases isEmpty_or_nonempty ι with hι | hι
    · rw [Real.iSup_of_isEmpty]
      refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x ↦ ?_) (norm_nonneg _)
      rw [hΦx, Finset.univ_eq_empty, Finset.sum_empty, norm_zero, zero_mul]
    refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (Real.iSup_nonneg fun i ↦
      norm_nonneg _) fun x ↦ ?_) (ciSup_le hψle)
    rw [hΦx, norm_eq_sum (by simp)]
    simp only [ENNReal.toReal_one, Real.rpow_one, div_one]
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    refine ((ψ i).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact le_ciSup (Finite.bddAbove_range fun i ↦ ‖ψ i‖) i
  · -- `1 < p < ∞`
    have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq (p := p) (q := q)
    have hqp := hpq.symm
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = p.toReal := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = q.toReal := ⟨_, rfl⟩
    rw [← hP, ← hQ] at hpq hqp
    have hP1 : 1 < P := hpq.lt
    have hQ1 : 1 < Q := hqp.lt
    have hP0 : 0 < P := zero_lt_one.trans hP1
    have hQ0 : 0 < Q := zero_lt_one.trans hQ1
    rw [norm_eq_sum (by rw [← hQ]; exact hQ0), ← hQ]
    simp only [hnorm]
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, ‖ψ i‖ ^ Q := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    rw [← hS]
    refine le_antisymm ?_ ?_
    · -- Hölder's inequality
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg hS0 _) fun x ↦ ?_
      rw [hΦx, norm_eq_sum (by rw [← hP]; exact hP0), ← hP, hS]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ ↦ (ψ i).le_opNorm (x i)).trans ?_
      have := Real.inner_le_Lp_mul_Lq Finset.univ (fun i ↦ ‖ψ i‖) (fun i ↦ ‖x i‖) hqp
      simpa only [abs_norm] using this
    · -- the extremal argument
      rcases hS0.eq_or_lt with hS0' | hSpos
      · rw [← hS0', Real.zero_rpow (by positivity)]
        exact norm_nonneg _
      obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ i, ‖ψ i‖ ^ (Q - 1) := ⟨_, rfl⟩
      have hT0 : 0 ≤ T := hT ▸ Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _
      have hSP : 0 < S ^ (1 / P) := Real.rpow_pos_of_pos hSpos _
      -- the key estimate: `S - δ T ≤ ‖Φ‖ S^{1/P}` for every `δ > 0`
      have key : ∀ δ : ℝ, 0 < δ → S - δ * T ≤ ‖Φ‖ * S ^ (1 / P) := by
        intro δ hδ
        -- almost extremal vectors for the `ψ i`
        have hy : ∀ i, ∃ y : X i, ‖y‖ ≤ 1 ∧ ‖ψ i‖ - δ ≤ ψ i y := by
          intro i
          rcases eq_or_ne (ψ i) 0 with h0 | h0
          · exact ⟨0, by simp, by rw [h0]; simp; linarith⟩
          obtain ⟨x, hx1, hx2⟩ := (ψ i).exists_lt_apply_of_lt_opNorm (r := ‖ψ i‖ - δ)
            (by linarith)
          obtain ⟨c, hc1, hc2⟩ : ∃ c : ℝ, |c| = 1 ∧ c * ψ i x = ‖ψ i x‖ := by
            rcases le_or_gt 0 (ψ i x) with h | h
            · exact ⟨1, abs_one, by rw [one_mul, Real.norm_of_nonneg h]⟩
            · exact ⟨-1, by rw [abs_neg, abs_one], by rw [neg_one_mul, Real.norm_of_nonpos h.le]⟩
          refine ⟨c • x, ?_, ?_⟩
          · rw [norm_smul, Real.norm_eq_abs, hc1, one_mul]; exact hx1.le
          · rw [map_smul, smul_eq_mul, hc2]; exact hx2.le
        choose y hy1 hy2 using hy
        obtain ⟨x, hx⟩ : ∃ x : PiLp p X, x = WithLp.toLp p fun i ↦ ‖ψ i‖ ^ (Q - 1) • y i :=
          ⟨_, rfl⟩
        have hxi : ∀ i, x i = ‖ψ i‖ ^ (Q - 1) • y i := fun i ↦ by rw [hx]
        -- `Φ x ≥ S - δ T`
        have hlow : S - δ * T ≤ Φ x := by
          rw [hΦx, hS, hT, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [hxi, map_smul, smul_eq_mul]
          have e : ‖ψ i‖ ^ Q = ‖ψ i‖ ^ (Q - 1) * ‖ψ i‖ := by
            rw [← Real.rpow_add_one' (norm_nonneg _) (by linarith), sub_add_cancel]
          rw [e]
          nlinarith [hy2 i, Real.rpow_nonneg (norm_nonneg (ψ i)) (Q - 1)]
        -- `‖x‖ ≤ S^{1/P}`
        have hup : ‖x‖ ≤ S ^ (1 / P) := by
          rw [norm_eq_sum (by rw [← hP]; exact hP0), ← hP, hS]
          refine Real.rpow_le_rpow (Finset.sum_nonneg fun i _ ↦ by positivity)
            (Finset.sum_le_sum fun i _ ↦ ?_) (by positivity)
          rw [hxi, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
            Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _),
            ← Real.rpow_mul (norm_nonneg _), hqp.sub_one_mul_conj]
          exact mul_le_of_le_one_right (Real.rpow_nonneg (norm_nonneg _) _)
            (Real.rpow_le_one (norm_nonneg _) (hy1 i) hP0.le)
        calc S - δ * T ≤ Φ x := hlow
          _ ≤ ‖Φ x‖ := le_abs_self _
          _ ≤ ‖Φ‖ * ‖x‖ := Φ.le_opNorm x
          _ ≤ ‖Φ‖ * S ^ (1 / P) := mul_le_mul_of_nonneg_left hup (norm_nonneg _)
      -- let `δ → 0`
      have hSle : S ≤ ‖Φ‖ * S ^ (1 / P) := by
        rcases hT0.eq_or_lt with hT0' | hTpos
        · have := key 1 one_pos
          rwa [← hT0', mul_zero, sub_zero] at this
        refine le_of_forall_pos_le_add fun ε hε ↦ ?_
        have := key (ε / T) (div_pos hε hTpos)
        rwa [div_mul_cancel₀ _ hTpos.ne', sub_le_iff_le_add] at this
      -- `S^{1/Q} = S / S^{1/P}`
      have hexp : S ^ (1 / Q) = S / S ^ (1 / P) := by
        rw [one_div, one_div, ← hpq.one_sub_inv, Real.rpow_sub hSpos, Real.rpow_one]
      rw [hexp, div_le_iff₀ hSP]
      exact hSle

end PiLp

/-! ### Proposition 8.14 and Remark 21: the representation of functionals -/

/-- The norm of an element of a finite `ℓ^p` product is the norm of the real tuple of the norms of
its coordinates. -/
theorem PiLp.norm_eq_norm_toLp_norm {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, NormedAddCommGroup (X i)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (x : PiLp q X) :
    ‖x‖ = ‖(WithLp.toLp q fun i ↦ ‖x i‖ : PiLp q fun _ : ι ↦ ℝ)‖ := by
  rcases eq_or_ne q ⊤ with rfl | hq
  · simp only [PiLp.norm_eq_ciSup, norm_norm]
  · have hq0 : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq
    simp only [PiLp.norm_eq_sum hq0, norm_norm]

section Repr

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] {I : Opens ℝ}

namespace SobolevIntervalLp

/-- **Remark 21 of [brezis2011functional], Chapter 8** (with the norm identity of Proposition
8.14): for `1 ≤ p < ∞`, `q` the conjugate exponent and a continuous linear functional `F` on
`W^{1,p}(I)`, there are `f₀, f₁ ∈ L^q(I)` — the pair `f` — with
`F u = ∫_I f₀ u + ∫_I f₁ u'` for every `u ∈ W^{1,p}(I)` and `‖F‖ = ‖f‖`, the `ℓ^q` norm of the
pair. `W^{1,p}(I)` is a closed subspace of the `ℓ^p` product of two copies of `L^p(I)`; `F`
extends to the product with the same norm (Hahn–Banach, `exists_extension_norm_eq`), the
restrictions of the extension to the two factors are represented by `f₀, f₁` through the Riesz
representation theorem (`MeasureTheory.Lp.exists_forall_eq_integral`), and the norm of a
functional on an `ℓ^p` product is the `ℓ^q` norm of the norms of its restrictions
(`PiLp.norm_strongDual_eq`). -/
theorem exists_repr_strongDual [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤)
    (F : StrongDual ℝ (SobolevIntervalLp 1 p I)) :
    ∃ f : PiLp q (fun _ : Fin 2 ↦ Lp ℝ q (volume.restrict (I : Set ℝ))),
      (∀ u, F u = (∫ x in (I : Set ℝ), f 0 x * fn u x)
        + ∫ x in (I : Set ℝ), f 1 x * deriv u 1 x) ∧ ‖F‖ = ‖f‖ := by
  classical
  have hq1 : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_extension_norm_eq
    (SobolevMultiIndex ℝ (Module.Basis.singleton Unit ℝ) 1 p I volume) F
  -- the restrictions of the extension to the two factors, and their representatives
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MultiIndexLE Unit 1 → StrongDual ℝ (Lp ℝ p (volume.restrict (I : Set ℝ))),
      ∀ α, ψ α = Φ.comp (PiLp.singleL p α) := ⟨_, fun _ ↦ rfl⟩
  choose g hg using fun α ↦ Lp.exists_forall_eq_integral (q := q) hp (ψ α)
  have hnorm : ∀ α, ‖ψ α‖ = ‖g α‖ := fun α ↦ by
    have : ψ α = Lp.toDualCLM ℝ p q (volume.restrict (I : Set ℝ)) (g α) :=
      ContinuousLinearMap.ext fun h ↦ by rw [hg, Lp.toDualCLM_apply]
    rw [this, Lp.norm_toDualCLM_apply]
  refine ⟨WithLp.toLp q fun j ↦ g (derivIndex 1 j), fun u ↦ ?_, ?_⟩
  · rw [← hΦ u, PiLp.strongDual_apply_eq_sum]
    simp only [← hψ, hg]
    rw [← (derivIndexEquiv 1).sum_comp, Fin.sum_univ_two]
    rfl
  · rw [← hΦn, PiLp.norm_strongDual_eq (q := q) hp,
      PiLp.norm_eq_norm_toLp_norm (WithLp.toLp q fun j ↦ g (derivIndex 1 j))]
    simp only [← hψ, hnorm]
    exact ((LinearIsometryEquiv.piLpCongrLeft q ℝ ℝ (derivIndexEquiv 1).symm).norm_map
      (WithLp.toLp q fun α ↦ ‖g α‖)).symm

end SobolevIntervalLp

namespace SobolevIntervalLpDual

open SobolevIntervalLp

/-- **Proposition 8.14 of [brezis2011functional]**: for `1 ≤ p < ∞`, `q` the conjugate exponent
and `F ∈ W^{-1,q}(I)`, there are `f₀, f₁ ∈ L^q(I)` — the pair `f` — with
`⟨F, u⟩ = ∫_I f₀ u + ∫_I f₁ u'` for every `u ∈ W_0^{1,p}(I)` and `‖F‖ = ‖f‖`, the `ℓ^q` norm
of the pair (the book's `max (‖f₀‖, ‖f₁‖)` for its sum norm, which is the norm of the type at
`p = 1`). `F` extends from the closed subspace `W_0^{1,p}(I)` to `W^{1,p}(I)` with the same norm
(`exists_extension_norm_eq`), and Remark 21 (`SobolevIntervalLp.exists_repr_strongDual`)
represents the extension. -/
theorem exists_repr [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤) (F : SobolevIntervalLpDual p I) :
    ∃ f : PiLp q (fun _ : Fin 2 ↦ Lp ℝ q (volume.restrict (I : Set ℝ))),
      (∀ u : SobolevIntervalLpZero 1 p I,
        F u = (∫ x in (I : Set ℝ), f 0 x * fn (u : SobolevIntervalLp 1 p I) x)
          + ∫ x in (I : Set ℝ), f 1 x * deriv (u : SobolevIntervalLp 1 p I) 1 x) ∧ ‖F‖ = ‖f‖ := by
  obtain ⟨G, hG, hGn⟩ := exists_extension_norm_eq (SobolevIntervalLpZero 1 p I) F
  obtain ⟨f, hf, hfn⟩ := exists_repr_strongDual (q := q) hp G
  exact ⟨f, fun u ↦ by rw [← hG u, hf], hGn.symm.trans hfn⟩

variable {a b : ℝ}

/-- **Proposition 8.14 of [brezis2011functional], bounded interval**: for `a < b`, `1 ≤ p < ∞`,
`q` the conjugate exponent and `F ∈ W^{-1,q}(a, b)`, there is `f₁ ∈ L^q(a, b)` with
`⟨F, u⟩ = ∫_a^b f₁ u'` for every `u ∈ W_0^{1,p}(a, b)` ("when `I` is bounded we can take
`f₀ = 0`"). By Poincaré's inequality (Proposition 8.13,
`SobolevIntervalLpZero.norm_le_mul_norm_deriv`) `u ↦ u'` is injective on `W_0^{1,p}(a, b)` with
`‖u‖ ≤ C ‖u'‖_p`, so `F ∘ (u ↦ u')⁻¹` is a bounded functional on the range of `u ↦ u'` in
`L^p(a, b)`; it extends to `L^p(a, b)` and is represented by `f₁`. -/
theorem exists_repr_of_bounded [ENNReal.HolderConjugate p q] (hp : p ≠ ⊤) (hab : a < b)
    (F : SobolevIntervalLpDual p (Opens.Ioo a b)) :
    ∃ f₁ : Lp ℝ q (volume.restrict (Ioo a b)), ∀ u : SobolevIntervalLpZero 1 p (Opens.Ioo a b),
      F u = ∫ x in Ioo a b, f₁ x * deriv (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) 1 x := by
  have hq1 : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevIntervalLpZero 1 p (Opens.Ioo a b),
      ‖(u : SobolevIntervalLp 1 p (Opens.Ioo a b))‖
        ≤ C * ‖deriv (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) 1‖ :=
    ⟨(b - a) / p.toReal ^ p.toReal⁻¹ + 1, by
      have := poincareConst_nonneg (p := p) hab.le
      linarith, fun u ↦ SobolevIntervalLpZero.norm_le_mul_norm_deriv hab u.2⟩
  -- the derivative `u ↦ u'` on `W_0^{1,p}(a, b)`, injective by Poincaré's inequality
  obtain ⟨D, hD⟩ : ∃ D : SobolevIntervalLpZero 1 p (Opens.Ioo a b) →ₗ[ℝ]
      Lp ℝ p (volume.restrict ((Opens.Ioo a b : Opens ℝ) : Set ℝ)),
      ∀ u, D u = deriv (u : SobolevIntervalLp 1 p (Opens.Ioo a b)) 1 :=
    ⟨(derivL 1 p (Opens.Ioo a b) 1 : SobolevIntervalLp 1 p (Opens.Ioo a b) →ₗ[ℝ]
      Lp ℝ p (volume.restrict ((Opens.Ioo a b : Opens ℝ) : Set ℝ))).comp
        (SobolevIntervalLpZero 1 p (Opens.Ioo a b)).subtype,
      fun u ↦ derivL_apply 1 (u : SobolevIntervalLp 1 p (Opens.Ioo a b))⟩
  have hDinj : Function.Injective D := by
    intro u v huv
    have h1 : ‖(u - v : SobolevIntervalLpZero 1 p (Opens.Ioo a b))‖ = 0 := by
      refine le_antisymm ((hC (u - v)).trans_eq ?_) (norm_nonneg _)
      rw [Submodule.coe_sub, deriv_sub, ← hD u, ← hD v, huv, sub_self, norm_zero, mul_zero]
    exact sub_eq_zero.1 (norm_eq_zero.1 h1)
  -- the functional `F ∘ D⁻¹` on the range of `D`, bounded by `C ‖F‖`
  obtain ⟨e, he⟩ : ∃ e : SobolevIntervalLpZero 1 p (Opens.Ioo a b) ≃ₗ[ℝ] LinearMap.range D,
      e = LinearEquiv.ofInjective D hDinj := ⟨_, rfl⟩
  have he_apply : ∀ u, (e u : Lp ℝ p (volume.restrict ((Opens.Ioo a b : Opens ℝ) : Set ℝ)))
      = D u := fun u ↦ by
    rw [he]; rfl
  obtain ⟨G, hG⟩ : ∃ G : LinearMap.range D →ₗ[ℝ] ℝ, G = (F : _ →ₗ[ℝ] ℝ).comp e.symm.toLinearMap :=
    ⟨_, rfl⟩
  have hGle : ∀ r : LinearMap.range D, ‖G r‖ ≤ C * ‖F‖ * ‖r‖ := by
    intro r
    rw [hG, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, ContinuousLinearMap.coe_coe]
    refine (F.le_opNorm _).trans ?_
    have h1 := hC (e.symm r)
    rw [← hD, ← he_apply, LinearEquiv.apply_symm_apply] at h1
    change ‖F‖ * ‖((e.symm r : SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
      SobolevIntervalLp 1 p (Opens.Ioo a b))‖ ≤ C * ‖F‖ * ‖r‖
    calc ‖F‖ * ‖((e.symm r : SobolevIntervalLpZero 1 p (Opens.Ioo a b)) :
          SobolevIntervalLp 1 p (Opens.Ioo a b))‖ ≤ ‖F‖ * (C * ‖r‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = C * ‖F‖ * ‖r‖ := by ring
  obtain ⟨Ĝ, hĜ, -⟩ := exists_extension_norm_eq (LinearMap.range D)
    (G.mkContinuous (C * ‖F‖) hGle)
  obtain ⟨f₁, hf₁⟩ := Lp.exists_forall_eq_integral (q := q) hp Ĝ
  refine ⟨f₁, fun u ↦ ?_⟩
  have h1 := hĜ (e u)
  rw [hf₁, LinearMap.mkContinuous_apply, hG, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply, he_apply, hD] at h1
  exact h1.symm

end SobolevIntervalLpDual

/-! ### Remark 19: the representation is not unique -/

namespace SobolevIntervalLpDual

open SobolevIntervalLp

omit [Fact (1 ≤ p)] in
/-- **Remark 19 of [brezis2011functional], Chapter 8**: the pair `(f₀, f₁)` representing a
functional on `W_0^{1,p}(I)` (or on `W^{1,p}(I)`) is not unique — for every test function `g` on
`I`, the pairs `(f₀, f₁)` and `(f₀ + g', f₁ + g)` define the same functional, since
`∫_I g' u = −∫_I g u'` for `u ∈ W^{1,p}(I)` (the definition of the weak derivative). -/
theorem repr_not_unique [ENNReal.HolderConjugate p q] {f₀ f₁ : ℝ → ℝ}
    (hf₀ : MemLp f₀ q (volume.restrict I)) (hf₁ : MemLp f₁ q (volume.restrict I)) (g : 𝓓(I, ℝ))
    (u : SobolevIntervalLp 1 p I) :
    (∫ x in (I : Set ℝ), (f₀ x + deriv g x) * fn u x)
        + ∫ x in (I : Set ℝ), (f₁ x + g x) * deriv u 1 x
      = (∫ x in (I : Set ℝ), f₀ x * fn u x) + ∫ x in (I : Set ℝ), f₁ x * deriv u 1 x := by
  have h := (hasWeakDerivOn_fn u).integral_deriv_mul g
  have hu0 : MemLp (fn u) p (volume.restrict I) := memLp_deriv u 0
  have hu1 : MemLp (deriv u 1) p (volume.restrict I) := memLp_deriv u 1
  have hi0 : Integrable (fun x ↦ f₀ x * fn u x) (volume.restrict I) := hf₀.integrable_mul hu0
  have hi1 : Integrable (fun x ↦ f₁ x * deriv u 1 x) (volume.restrict I) := hf₁.integrable_mul hu1
  have hg0 : Integrable (fun x ↦ deriv g x * fn u x) (volume.restrict I) := by
    have := ((hasWeakDerivOn_fn u).integrable_smul (g.fderivApply 1)).restrict (s := I)
    simpa only [TestFunction.derivApply_coe, smul_eq_mul] using this
  have hg1 : Integrable (fun x ↦ g x * deriv u 1 x) (volume.restrict I) := by
    have := ((hasWeakDerivOn_fn u).integrable_smul_weakDeriv g).restrict (s := I)
    simpa only [smul_eq_mul] using this
  have e1 : ∫ x in (I : Set ℝ), (f₀ x + deriv g x) * fn u x
      = (∫ x in (I : Set ℝ), f₀ x * fn u x) + ∫ x in (I : Set ℝ), deriv g x * fn u x := by
    rw [← integral_add hi0 hg0]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  have e2 : ∫ x in (I : Set ℝ), (f₁ x + g x) * deriv u 1 x
      = (∫ x in (I : Set ℝ), f₁ x * deriv u 1 x) + ∫ x in (I : Set ℝ), g x * deriv u 1 x := by
    rw [← integral_add hi1 hg1]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [e1, e2, h]
  ring

end SobolevIntervalLpDual

end Repr

end
