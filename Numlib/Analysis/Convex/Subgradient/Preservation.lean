import Numlib.Analysis.Convex.Duality.Ops
import Numlib.Analysis.Convex.Operations.Closed
import Numlib.Analysis.Convex.Duality.Relint
import Numlib.Analysis.Convex.Recession.Closedness
import Numlib.Analysis.Convex.Subgradient.StrictlyConvex

/-!
# Preservation of essential smoothness

Essential smoothness survives infimal convolution and the image under a linear map, under the
usual exactness hypotheses. Both are one argument. Essential smoothness of `f` is essential
*strict* convexity of `f*`; the dual operation on the conjugate side is a sum, for `□`, or
composition with the transpose, for the image; the subdifferential calculus puts the domain of the
subdifferential of that dual object inside `dom ∂f*`; and strict convexity there survives adding a
convex function or precomposing with an injective linear map. Read backwards, the same duality
returns essential smoothness.

## Main results

* `StrictConvexOnFn.add_convexFn`, `StrictConvexOnFn.compLin` — a strictly convex summand makes a
  sum strictly convex, and strict convexity pulls back along an injective linear map.
* `IsExactSum.essentiallySmooth_infConv` — infimal convolution (Corollary 26.3.2 in [^1]).
* `IsExactImage.essentiallySmooth_mapLin` — linear images (Corollary 26.3.3 in [^1]). Each has an
  `_of_relint` variant asking `ri (dom f₁*) ∩ ri (dom f₂*) ≠ ∅`, resp. `∃ y*, A' y* ∈ ri (dom f*)`.

## Implementation notes

The linear-image result instantiates the exactness interface for the *transpose* `A'`, because the
identity used is `A f = (f* A')*`; surjectivity of `A` enters only through injectivity of `A'`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §26.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### Strict convexity under addition and under precomposition -/

section StrictConvexOps

variable {E G : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
  {f g : E → EReal} {C : Set E}

/-- A strictly convex summand makes the sum strictly convex. Both functions must be finite on `C`:
the strict inequality for `f` is vacuous where `f x = ⊤`, while the one being proved for `f + g`
is not. -/
theorem StrictConvexOnFn.add_convexFn (hC : Convex ℝ C) (hsc : StrictConvexOnFn f C)
    (hg : ConvexFn g) (hpf : Proper f) (hpg : Proper g) (hCf : C ⊆ dom f) (hCg : C ⊆ dom g) :
    StrictConvexOnFn (f + g) C := by
  intro x hx y hy hne a b ha hb hab
  have hz : a • x + b • y ∈ C := hC hx hy ha.le hb.le hab
  have hstrict := hsc hx hy hne ha hb hab
  have hconv := (convexFn_iff_le hpg.ne_bot).1 hg x y a b ha hb hab
  have hcf : ∀ ⦃z : E⦄, z ∈ C → f z = ((f z).toReal : EReal) := fun z hzC =>
    (EReal.coe_toReal (mem_dom.1 (hCf hzC)).ne (hpf.ne_bot z)).symm
  have hcg : ∀ ⦃z : E⦄, z ∈ C → g z = ((g z).toReal : EReal) := fun z hzC =>
    (EReal.coe_toReal (mem_dom.1 (hCg hzC)).ne (hpg.ne_bot z)).symm
  rw [hcf hx, hcf hy, hcf hz] at hstrict
  rw [hcg hx, hcg hy, hcg hz] at hconv
  rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, hcf hx, hcf hy, hcf hz, hcg hx, hcg hy, hcg hz]
  simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff,
    EReal.coe_le_coe_iff] at hstrict hconv ⊢
  linarith

/-- The same with the summands the other way round. -/
theorem ConvexFn.add_strictConvexOnFn (hC : Convex ℝ C) (hf : ConvexFn f)
    (hsc : StrictConvexOnFn g C) (hpf : Proper f) (hpg : Proper g) (hCf : C ⊆ dom f)
    (hCg : C ⊆ dom g) : StrictConvexOnFn (f + g) C := by
  rw [add_comm]
  exact StrictConvexOnFn.add_convexFn hC hsc hf hpg hpf hCg hCf

/-- Strict convexity pulls back along an injective linear map. -/
theorem StrictConvexOnFn.compLin {A : G →ₗ[ℝ] E} {D : Set G} (h : StrictConvexOnFn f (A '' D))
    (hinj : Function.Injective A) : StrictConvexOnFn (compLin f A) D := by
  intro x hx y hy hne a b ha hb hab
  have hlt := h ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ (fun hc => hne (hinj hc)) ha hb hab
  simpa only [compLin_apply, map_add, map_smul] using hlt

end StrictConvexOps

/-! ### Infimal convolution -/

section InfConv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f₁ f₂ : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- The conjugate-side content: if `g₁` is essentially strictly convex and `g₁ + g₂` adds exactly,
then `g₁ + g₂` is essentially strictly convex. The sum rule for subdifferentials puts
`dom ∂(g₁ + g₂)` inside `dom ∂g₁`. -/
theorem IsExactSum.essentiallyStrictlyConvex_add {g₁ g₂ : E → EReal}
    (h : IsExactSum (innerₗ E) g₁ g₂) (hg₂ : ConvexFn g₂)
    (hesc : EssentiallyStrictlyConvex (B := innerₗ E) g₁) :
    EssentiallyStrictlyConvex (B := innerₗ E) (g₁ + g₂) := by
  intro C hC hCsub
  have hCdom : C ⊆ dom (g₁ + g₂) := hCsub.trans (domSubgradient_subset_dom h.proper_add)
  rw [dom_add h.proper_left.ne_bot h.proper_right.ne_bot] at hCdom
  refine StrictConvexOnFn.add_convexFn hC (hesc hC fun z hz => ?_) hg₂ h.proper_left
    h.proper_right (fun z hz => (hCdom hz).1) fun z hz => (hCdom hz).2
  obtain ⟨v, hv⟩ := hCsub hz
  rw [h.subgradient_add z] at hv
  obtain ⟨v₁, hv₁, -, -, -⟩ := hv
  exact ⟨v₁, hv₁⟩

/-- If `f₁` is essentially smooth and the conjugates `f₁*` and `f₂*` add exactly, then `f₁ □ f₂` is
essentially smooth: it is the conjugate of `f₁* + f₂*`. -/
theorem IsExactSum.essentiallySmooth_infConv
    (h : IsExactSum (innerₗ E) (conj (innerₗ E) f₁) (conj (innerₗ E) f₂))
    (h₁ : ClosedProperConvexFn f₁) (h₂ : ClosedProperConvexFn f₂)
    (hes : EssentiallySmooth f₁) : EssentiallySmooth (infConv f₁ f₂) := by
  have hsum : ClosedProperConvexFn (conj (innerₗ E) f₁ + conj (innerₗ E) f₂) :=
    ClosedProperConvexFn.add ⟨convexFn_conj _ f₁, closedFn_conj, proper_conj h₁⟩
      ⟨convexFn_conj _ f₂, closedFn_conj, proper_conj h₂⟩ h.proper_add.dom_nonempty
  have hinf : conj (innerₗ E) (conj (innerₗ E) f₁ + conj (innerₗ E) f₂) = infConv f₁ f₂ := by
    rw [h.conj_add, conj_conj_innerL h₁.convex h₁.closed, conj_conj_innerL h₂.convex h₂.closed]
  rw [← hinf]
  refine (essentiallySmooth_conj_iff_essentiallyStrictlyConvex hsum.convex hsum.proper
    hsum.closed).2 (h.essentiallyStrictlyConvex_add (convexFn_conj _ f₂) ?_)
  exact (essentiallyStrictlyConvex_conj_iff_essentiallySmooth h₁.convex h₁.proper h₁.closed).2 hes

/-- The same under the classical hypothesis: a common relative interior point of `dom f₁*` and
`dom f₂*` supplies the exactness. -/
theorem essentiallySmooth_infConv_of_relint (h₁ : ClosedProperConvexFn f₁)
    (h₂ : ClosedProperConvexFn f₂) (hes : EssentiallySmooth f₁) {y₀ : E}
    (hy₁ : y₀ ∈ ri (dom (conj (innerₗ E) f₁))) (hy₂ : y₀ ∈ ri (dom (conj (innerₗ E) f₂))) :
    EssentiallySmooth (infConv f₁ f₂) :=
  IsExactSum.essentiallySmooth_infConv
    (IsExactSum.of_relint (convexFn_conj _ f₁) (proper_conj h₁) (convexFn_conj _ f₂)
      (proper_conj h₂) hy₁ hy₂) h₁ h₂ hes

end InfConv

/-! ### Linear images -/

section Image

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {f : E → EReal} {A : E →ₗ[ℝ] G} {A' : G →ₗ[ℝ] E}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- An onto linear map has an injective transpose. -/
theorem injective_of_isAdjointPair_of_surjective (hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A)
    (hsurj : Function.Surjective A) : Function.Injective A' := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y
  have h := hA y x
  rw [LinearMap.mem_ker.1 hy, map_zero, LinearMap.zero_apply, hx] at h
  have h2 : ‖y‖ ^ 2 = 0 := by simpa using h.symm
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg y])

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- The conjugate-side content: if `g` is essentially strictly convex, `A'` is injective and `g`
pulls back exactly along `A'`, then `g A'` is essentially strictly convex. The chain rule makes
`dom ∂(g A')` the preimage of `dom ∂g`. -/
theorem IsExactImage.essentiallyStrictlyConvex_compLin {g : E → EReal}
    {hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A}
    (h : IsExactImage (innerₗ G) (innerₗ E) A' A hA g) (hinj : Function.Injective A')
    (hesc : EssentiallyStrictlyConvex (B := innerₗ E) g) :
    EssentiallyStrictlyConvex (B := innerₗ G) (compLin g A') := by
  intro C hC hCsub
  refine StrictConvexOnFn.compLin (hesc (hC.linear_image A') fun z hz => ?_) hinj
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨v, hv⟩ := hCsub hy
  rw [h.subgradient_compLin y] at hv
  obtain ⟨w, hw, -⟩ := hv
  exact ⟨w, hw⟩

/-- If `f` is essentially smooth, `A'` is injective, and `f*` pulls back exactly along `A'`, then
the image `A f` is essentially smooth: it is the conjugate of `f* A'`. -/
theorem IsExactImage.essentiallySmooth_mapLin {hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A}
    (h : IsExactImage (innerₗ G) (innerₗ E) A' A hA (conj (innerₗ E) f))
    (hf : ClosedProperConvexFn f) (hes : EssentiallySmooth f) (hinj : Function.Injective A') :
    EssentiallySmooth (mapLin A f) := by
  have hk : ClosedProperConvexFn (compLin (conj (innerₗ E) f) A') :=
    ⟨convexFn_compLin A' (convexFn_conj _ f),
      closedFn_compLin closedFn_conj A'.continuous_of_finiteDimensional, h.proper_compLin⟩
  have himg : conj (innerₗ G) (compLin (conj (innerₗ E) f) A') = mapLin A f := by
    rw [h.conj_compLin, conj_conj_innerL hf.convex hf.closed]
  rw [← himg]
  refine (essentiallySmooth_conj_iff_essentiallyStrictlyConvex hk.convex hk.proper hk.closed).2
    (h.essentiallyStrictlyConvex_compLin hinj ?_)
  exact (essentiallyStrictlyConvex_conj_iff_essentiallySmooth hf.convex hf.proper hf.closed).2 hes

/-- The same under the classical hypotheses: `A` onto and some `y₀` with `A' y₀ ∈ ri (dom f*)`.
The first gives injectivity of the transpose, the second the exactness. -/
theorem essentiallySmooth_mapLin_of_relint (hA : IsAdjointPair (innerₗ G) (innerₗ E) A' A)
    (hf : ClosedProperConvexFn f) (hes : EssentiallySmooth f) (hsurj : Function.Surjective A)
    {y₀ : G} (hy₀ : A' y₀ ∈ ri (dom (conj (innerₗ E) f))) :
    EssentiallySmooth (mapLin A f) :=
  IsExactImage.essentiallySmooth_mapLin
    (IsExactImage.of_relint_closed hA ⟨convexFn_conj _ f, closedFn_conj, proper_conj hf⟩ hy₀) hf hes
    (injective_of_isAdjointPair_of_surjective hA hsurj)

end Image

end ConvexAnalysis
