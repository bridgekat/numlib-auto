/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Convolution.Bochner`, beside `Mathlib.Analysis.Convolution`, whose
pointwise convolution this identifies with a Bochner integral valued in `L¹`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Numlib.Analysis.Convolution.Lp
import Numlib.MeasureTheory.Integral.SetIntegralCLM

/-!
# The convolution as a Bochner integral of translates

For `f ∈ L¹(G)` and `g ∈ L¹(G, F)` the convolution `(f ⋆ g) x = ∫ y, f y • g (x - y) ∂μ` is, as an
element of `L¹`, the *vector-valued* integral `∫ y, f y • τ_y g ∂μ` of the translates
`τ_y g = g (· - y)`, an integral taken in the Banach space `L¹(G, F)`: a convolution is a
continuous superposition of translates. Mathlib defines `MeasureTheory.convolution` pointwise only,
and this file supplies the Bochner-integral reading, which is what lets a bounded linear operator
on `L¹` pass through a convolution: an operator that commutes with every translation commutes
with every convolution, `S (f ⋆ g) = f ⋆ S g`
(`MeasureTheory.Lp.coeFn_toL1_convolution_of_translateₗᵢ_comm`). The last statement is the
rigorous form of the "shift-invariant linear system" identity of signal processing, where it is
usually justified by linearity and shift invariance alone; those do not suffice, since a
convolution is an integral and not a finite linear combination of translates, and continuity of
`S` is what carries the integral through (compare L. Grafakos, *Classical Fourier Analysis*, 3rd
edition, Springer, 2014, §2.5, where the bounded operators commuting with translations are
characterized as convolution operators).

## Main definitions

* `MeasureTheory.L1.setIntegralCLM 𝕜 A`: the integral over a set, `u ↦ ∫ x in A, u x ∂μ`, as a
  bounded linear functional on `L¹`.
* `MeasureTheory.Lp.translateₗᵢ 𝕜 F p y`: the translation `τ_y : g ↦ g (· - y)` on `Lp F p μ`,
  a linear isometry for a right-invariant measure (`MeasureTheory.Lp.compMeasurePreservingₗᵢ`
  along `x ↦ x - y`). Note the sign: this is the translation of harmonic analysis, so that
  `(f ⋆ g) x = ∫ y, f y • (τ_y g) x ∂μ`; `MeasureTheory.Lp.translate` (in
  `Numlib.Analysis.Sobolev.Translate`) is `u ↦ u (· + h)` on an invariant open subset.

## Main results

* `MeasureTheory.Lp.continuous_translateₗᵢ`: `y ↦ τ_y g` is continuous into `Lp F p μ` for
  `p ≠ ∞`, over a Haar measure on a finite-dimensional real normed space (Mathlib's
  `Continuous.compMeasurePreservingLp`).
* `MeasureTheory.Lp.integrable_smul_translateₗᵢ`: for `f ∈ L¹`, the `Lp`-valued function
  `y ↦ f y • τ_y g` is Bochner integrable.
* `MeasureTheory.Lp.coeFn_integral_smul_translateₗᵢ` and
  `MeasureTheory.Lp.integral_smul_translateₗᵢ_eq_toL1`: the `L¹`-valued integral
  `∫ y, f y • τ_y g ∂μ` is the class of the pointwise convolution `f ⋆[lsmul 𝕜 𝕜, μ] g`.
  `MeasureTheory.Lp.convolutionCLM_eq_integral` is the same for the convolution operator with a
  real kernel.
* `MeasureTheory.Lp.coeFn_toL1_convolution_of_translateₗᵢ_comm`: a bounded linear operator
  `S` on `L¹` commuting with every translation commutes with every convolution,
  `S (f ⋆ g) = f ⋆ S g`.

## Implementation notes

The identity between the Bochner integral and the pointwise convolution is proved through the
set integrals: two integrable functions with the same integral over every measurable set of
finite measure agree almost everywhere (`MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq`).
The set integral is a bounded functional on `L¹`, so it passes through the Bochner integral
(`ContinuousLinearMap.integral_comp_comm`), and on the pointwise side Fubini's theorem swaps the
two integrals, the integrability on `A × G` being Mathlib's `Integrable.convolution_integrand`
restricted to `A`. The core identity `coeFn_integral_smul_translateₗᵢ_of_integrable` asks only
for a right-invariant s-finite measure on a measurable group and takes the Bochner integrability
of `y ↦ f y • τ_y g` as a hypothesis; that integrability is where topology enters, since the
strong measurability of `y ↦ τ_y g` comes from the continuity of translation on `Lp`, and the
unprimed statements assume a Haar measure on a finite-dimensional real normed space.

The statements are at `p = 1` because the set-integral functional is bounded on `L¹` without a
finiteness condition on the set; the same argument gives the `Lᵖ` identity for `1 ≤ p < ∞` with
the functional restricted to sets of finite measure and Young's inequality
(`MeasureTheory.MemLp.convolution`) in place of `Integrable.convolution_integrand`.
-/

open Filter Function MeasureTheory MeasureTheory.Measure Topology
open ContinuousLinearMap
open scoped Convolution ENNReal

namespace MeasureTheory

namespace Lp

/-! ### Translations on `Lᵖ` of a group -/

section Translate

variable (𝕜 : Type*) {G F : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd G]
  {μ : Measure G} [μ.IsAddRightInvariant] [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [NormedField 𝕜] [NormedSpace 𝕜 F]

variable (F p) in
/-- **Translation by `y` on `Lp F p μ`**, `τ_y : g ↦ g (· - y)`, as a linear isometry: the
composition with the measure-preserving map `x ↦ x - y`
(`MeasureTheory.Lp.compMeasurePreservingₗᵢ`). With this sign, `(f ⋆ g) x = ∫ y, f y • (τ_y g) x`.
-/
noncomputable def translateₗᵢ (y : G) : Lp F p μ →ₗᵢ[𝕜] Lp F p μ :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (· - y) (measurePreserving_sub_right μ y)

/-- `τ_y g` is `g (· - y)` almost everywhere. -/
theorem coeFn_translateₗᵢ (y : G) (g : Lp F p μ) :
    translateₗᵢ 𝕜 F p y g =ᵐ[μ] fun x => g (x - y) :=
  Lp.coeFn_compMeasurePreserving g _

/-- The translation of the class of `g` is the class of `g (· - y)`. -/
theorem translateₗᵢ_toLp (y : G) {g : G → F} (hg : MemLp g p μ) :
    translateₗᵢ 𝕜 F p y (hg.toLp g)
      = (hg.comp_measurePreserving (measurePreserving_sub_right μ y)).toLp (fun x => g (x - y)) :=
  rfl

/-- Translation preserves the `Lᵖ` norm. -/
theorem norm_translateₗᵢ (y : G) (g : Lp F p μ) : ‖translateₗᵢ 𝕜 F p y g‖ = ‖g‖ :=
  (translateₗᵢ 𝕜 F p y).norm_map g

/-- Translation by `0` is the identity. -/
theorem translateₗᵢ_zero (g : Lp F p μ) : translateₗᵢ 𝕜 F p (0 : G) g = g :=
  Lp.ext ((coeFn_translateₗᵢ 𝕜 0 g).trans (Eventually.of_forall fun x => by simp))

/-- Translations compose: `τ_y (τ_z g) = τ_{y + z} g` on a commutative group. -/
theorem translateₗᵢ_translateₗᵢ {G : Type*} [MeasurableSpace G] [AddCommGroup G]
    [MeasurableAdd G] {μ : Measure G} [μ.IsAddRightInvariant] (y z : G) (g : Lp F p μ) :
    translateₗᵢ 𝕜 F p y (translateₗᵢ 𝕜 F p z g) = translateₗᵢ 𝕜 F p (y + z) g := by
  refine Lp.ext ((coeFn_translateₗᵢ 𝕜 y _).trans ?_)
  filter_upwards [(measurePreserving_sub_right μ y).quasiMeasurePreserving.ae_eq_comp
    (coeFn_translateₗᵢ 𝕜 z g), coeFn_translateₗᵢ 𝕜 (y + z) g] with x hx hx'
  simp only [comp_apply] at hx
  rw [hx, hx', sub_sub]

end Translate

/-! ### Continuity of `y ↦ τ_y g`, and the Bochner integrability of `y ↦ f y • τ_y g` -/

section Continuous

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F]

/-- **Continuity of translation on `Lᵖ`**, as a map `y ↦ τ_y g` into `Lp F p μ`, for `p ≠ ∞`:
Mathlib's `Continuous.compMeasurePreservingLp` for the continuous family of measure-preserving
maps `x ↦ x - y`. -/
theorem continuous_translateₗᵢ (hp : p ≠ ∞) (g : Lp F p μ) :
    Continuous fun y : G => translateₗᵢ 𝕜 F p y g := by
  let Φ : C(G × G, G) := ⟨fun z => z.2 - z.1, by fun_prop⟩
  exact Continuous.compMeasurePreservingLp (f := fun _ => g) (g := fun y => Φ.curry y)
    continuous_const Φ.curry.continuous (fun y => measurePreserving_sub_right μ y) hp

variable {𝕜}

/-- For `f ∈ L¹` and `g ∈ Lᵖ`, `p ≠ ∞`, the `Lᵖ`-valued function `y ↦ f y • τ_y g` is Bochner
integrable: it is strongly measurable by the continuity of `y ↦ τ_y g`, and its norm is
`‖f y‖ * ‖g‖`. -/
theorem integrable_smul_translateₗᵢ (hp : p ≠ ∞) {f : G → 𝕜} (hf : Integrable f μ)
    (g : Lp F p μ) : Integrable (fun y => f y • translateₗᵢ 𝕜 F p y g) μ := by
  refine Integrable.mono' (hf.norm.mul_const ‖g‖)
    (hf.aestronglyMeasurable.smul (continuous_translateₗᵢ 𝕜 hp g).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul, norm_translateₗᵢ]

end Continuous

/-! ### The convolution as a Bochner integral of translates -/

section Bochner

variable {G : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd₂ G] [MeasurableNeg G]
  {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- **The convolution is the Bochner integral of the translates** (core form): for `f ∈ L¹(G)`
and `g ∈ L¹(G, F)`, if `y ↦ f y • τ_y g` is Bochner integrable as an `L¹`-valued function, then
its integral `∫ y, f y • τ_y g ∂μ ∈ L¹` is the class of the pointwise convolution
`(f ⋆ g) x = ∫ y, f y • g (x - y) ∂μ`.

Both sides are integrable and have the same integral over every measurable set `A` of finite
measure: on the left because the set integral is a bounded functional on `L¹`
(`MeasureTheory.L1.setIntegralCLM`) which passes through the Bochner integral, on the right by
Fubini's theorem on `A × G`. -/
theorem coeFn_integral_smul_translateₗᵢ_of_integrable {f : G → 𝕜} (hf : Integrable f μ)
    (g : G →₁[μ] F) (hint : Integrable (fun y => f y • translateₗᵢ 𝕜 F 1 y g) μ) :
    ⇑(∫ y, f y • translateₗᵢ 𝕜 F 1 y g ∂μ) =ᵐ[μ] f ⋆[lsmul 𝕜 𝕜, μ] g := by
  have hg : Integrable g μ := L1.integrable_coeFn g
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _)
    (hf.integrable_convolution (lsmul 𝕜 𝕜) hg) fun A hA _ => ?_
  have h1 : ∫ x in A, (∫ y, f y • translateₗᵢ 𝕜 F 1 y g ∂μ) x ∂μ
      = ∫ y, f y • ∫ x in A, g (x - y) ∂μ ∂μ := by
    rw [← L1.setIntegralCLM_apply (𝕜 := 𝕜), ← (L1.setIntegralCLM 𝕜 A).integral_comp_comm hint]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [map_smul, L1.setIntegralCLM_apply]
    congr 1
    exact setIntegral_congr_ae hA ((coeFn_translateₗᵢ 𝕜 y g).mono fun x hx _ => hx)
  have h2 : ∫ x in A, (f ⋆[lsmul 𝕜 𝕜, μ] g) x ∂μ = ∫ y, f y • ∫ x in A, g (x - y) ∂μ ∂μ := by
    simp only [convolution_lsmul]
    have hprod : Integrable (fun z : G × G => f z.2 • g (z.1 - z.2)) ((μ.restrict A).prod μ) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact (hf.convolution_integrand (lsmul 𝕜 𝕜) hg (μ := μ) (ν := μ)).integrableOn
    rw [integral_integral_swap hprod]
    exact integral_congr_ae (Eventually.of_forall fun y => integral_smul _ _)
  rw [h1, h2]

end Bochner

section BochnerHaar

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- **The convolution is the Bochner integral of the translates**: for `f ∈ L¹(G)` and
`g ∈ L¹(G, F)` over a Haar measure on a finite-dimensional real normed space, the `L¹`-valued
integral `∫ y, f y • τ_y g ∂μ` is, almost everywhere, the pointwise convolution
`(f ⋆ g) x = ∫ y, f y • g (x - y) ∂μ`. -/
theorem coeFn_integral_smul_translateₗᵢ {f : G → 𝕜} (hf : Integrable f μ) (g : G →₁[μ] F) :
    ⇑(∫ y, f y • translateₗᵢ 𝕜 F 1 y g ∂μ) =ᵐ[μ] f ⋆[lsmul 𝕜 𝕜, μ] g :=
  coeFn_integral_smul_translateₗᵢ_of_integrable hf g
    (integrable_smul_translateₗᵢ ENNReal.one_ne_top hf g)

/-- **The convolution is the Bochner integral of the translates**, as an equality in `L¹`:
`∫ y, f y • τ_y g ∂μ` is the `L¹` class of `f ⋆[lsmul 𝕜 𝕜, μ] g`. -/
theorem integral_smul_translateₗᵢ_eq_toL1 {f : G → 𝕜} (hf : Integrable f μ) (g : G →₁[μ] F) :
    ∫ y, f y • translateₗᵢ 𝕜 F 1 y g ∂μ
      = (hf.integrable_convolution (lsmul 𝕜 𝕜) (L1.integrable_coeFn g)).toL1 _ :=
  Lp.ext ((coeFn_integral_smul_translateₗᵢ hf g).trans (Integrable.coeFn_toL1 _).symm)

/-- The convolution operator `MeasureTheory.Lp.convolutionCLM` with an integrable real kernel
`K`, on `L¹`, is the Bochner integral of the translates: `K ⋆ g = ∫ y, K y • τ_y g ∂μ`. -/
theorem convolutionCLM_eq_integral {K : G → ℝ} (hK : Integrable K μ) (g : G →₁[μ] F) :
    convolutionCLM F 1 hK g = ∫ y, K y • translateₗᵢ ℝ F 1 y g ∂μ :=
  Lp.ext ((coeFn_convolutionCLM hK g).trans (coeFn_integral_smul_translateₗᵢ hK g).symm)

/-- **A bounded operator on `L¹` commuting with the translations commutes with convolutions**:
if `S : L¹(G, F) →L[𝕜] L¹(G, F)` satisfies `S (τ_y g) = τ_y (S g)` for every `y` and `g`, then
`S (f ⋆ g) = f ⋆ S g` almost everywhere, for every `f ∈ L¹(G)` and `g ∈ L¹(G, F)`. Reading
`f ⋆ g` as the Bochner integral `∫ y, f y • τ_y g ∂μ`, the continuous linear `S` passes through
the integral (`ContinuousLinearMap.integral_comp_comm`), commutes with each translate, and the
result is the Bochner form of `f ⋆ S g`. -/
theorem coeFn_toL1_convolution_of_translateₗᵢ_comm (S : (G →₁[μ] F) →L[𝕜] (G →₁[μ] F))
    (hS : ∀ (y : G) (g : G →₁[μ] F), S (translateₗᵢ 𝕜 F 1 y g) = translateₗᵢ 𝕜 F 1 y (S g))
    {f : G → 𝕜} (hf : Integrable f μ) (g : G →₁[μ] F) :
    ⇑(S ((hf.integrable_convolution (lsmul 𝕜 𝕜) (L1.integrable_coeFn g)).toL1 _))
      =ᵐ[μ] f ⋆[lsmul 𝕜 𝕜, μ] (S g) := by
  rw [← integral_smul_translateₗᵢ_eq_toL1 hf g,
    ← S.integral_comp_comm (integrable_smul_translateₗᵢ ENNReal.one_ne_top hf g)]
  simp only [map_smul, hS]
  exact coeFn_integral_smul_translateₗᵢ hf (S g)

end BochnerHaar

end Lp

end MeasureTheory
