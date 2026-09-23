import Mathlib.Analysis.Calculus.Gradient.Basic
import Numlib.Analysis.Convex.Subdifferential.Legendre
import Numlib.Analysis.Convex.Subdifferential.StrictlyConvex

/-!
# Convex functions of Legendre type

A closed proper convex function is *of Legendre type* when it is essentially smooth and strictly
convex on the interior `C` of its effective domain — equivalently, when `∂f` is a one-to-one
mapping. The property is self-dual: `f` is of Legendre type exactly when `f*` is, and then `∇f` is
a bijection of `C` onto `C* = int (dom f*)`, continuous in both directions, with `∇f* = (∇f)⁻¹`.
For an essentially smooth function the domain `D` of the Legendre conjugate is `dom ∂f*`, and so is
squeezed between `ri (dom f*)` and `dom f*`. In general `D` is not convex, which is why the squeeze
cannot be improved to an equality.

## Main definitions

* `gradientRange f` — the set `D = ∇f(C)`, as a set of *vectors*.
* `LegendreType f` — `f` is essentially smooth and strictly convex on `int (dom f)`.

## Main results

* `hasGradientAtFn_toDual_iff_mem_subdifferential` — for an essentially smooth `f`, being *the*
  gradient at `x` and being *a* subgradient at `x` say the same thing. Everything else here is that
  equivalence combined with the inversion `∂f* = (∂f)⁻¹`.
* `gradientRange_eq_domSubdifferential_convexConj`,
  `relint_convexDom_convexConj_subset_gradientRange`, `gradientRange_subset_convexDom_convexConj` —
  `D = dom ∂f*`, therefore `ri (dom f*) ⊆ D ⊆ dom f*`.
* `legendreType_convexConj_iff`, `bijOn_gradient_of_legendreType`,
  `continuousOn_gradient_interior_convexDom` — the Legendre duality ([rockafellar1970convex] Theorem
  26.5).
* `bijOn_gradient_univ_iff`, `convexConj_finite_of_bijOn_gradient_univ` — for a finite
  differentiable convex function, `∇f` is a bijection of `E` onto itself exactly when `f` is
  strictly convex with `dom f* = E`, and then `f*` is a function of the same kind.

## Implementation notes

`legendreDom f` lives in `StrongDual ℝ E`, but it has to be compared with `dom ∂f*`, whose elements
are *vectors* for the self-pairing `innerₗ E`. `gradientRange` is `legendreDom` carried back across
the Riesz isometry, so that the comparison is an equality of sets in `E`.

## References

* [rockafellar1970convex] §26.
-/

namespace ConvexAnalysis

open scoped RealInnerProductSpace

section LegendreType

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x v : E} {f' : StrongDual ℝ E}

/-! ### The range of the gradient mapping, in vector form -/

/-- The domain `D = ∇f(C)` of the Legendre conjugate, as a set of *vectors*: the preimage of
`legendreDom f` under the Riesz isometry. -/
def gradientRange (f : E → EReal) : Set E :=
  {v | ∃ x, HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x}

@[simp] theorem mem_gradientRange :
    v ∈ gradientRange f ↔ ∃ x, HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x := Iff.rfl

theorem mem_gradientRange_iff_mem_legendreDom :
    v ∈ gradientRange f ↔ InnerProductSpace.toDual ℝ E v ∈ legendreDom f := Iff.rfl

theorem HasGradientAtFn.mem_gradientRange
    (h : HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x) : v ∈ gradientRange f := ⟨x, h⟩

/-- Mathlib's `gradient` of the real trace is `∇f`. -/
theorem HasGradientAtFn.gradient_toReal_eq (h : HasGradientAtFn f f' x) :
    gradient (fun w => (f w).toReal) x = (InnerProductSpace.toDual ℝ E).symm f' := by
  unfold gradient
  rw [h.fderiv_toReal_eq]

/-- At a point of differentiability, `gradient (fun w => (f w).toReal)` really is a gradient. -/
theorem DifferentiableAtFn.hasGradientAtFn_gradient (h : DifferentiableAtFn f x) :
    HasGradientAtFn f (InnerProductSpace.toDual ℝ E (gradient (fun w => (f w).toReal) x)) x := by
  obtain ⟨g, hg⟩ := h
  rw [hg.gradient_toReal_eq, LinearIsometryEquiv.apply_symm_apply]
  exact hg

/-! ### The domain of the Legendre conjugate -/

/-- For an essentially smooth function, gradients and subgradients coincide. On the interior of the
effective domain a lone subgradient is the gradient; off it, both sides are impossible. -/
theorem hasGradientAtFn_toDual_iff_mem_subdifferential (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (hes : EssentiallySmooth f) :
    HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x ↔ v ∈ subdifferential (innerₗ E) f x := by
  constructor
  · intro h
    rw [subdifferential_innerL_eq_singleton hf h, LinearIsometryEquiv.symm_apply_apply]
    exact Set.mem_singleton v
  · intro h
    by_cases hx : x ∈ interior (convexDom f)
    · rw [subdifferential_eq_singleton_of_essentiallySmooth hf hes hx, Set.mem_singleton_iff] at h
      subst h
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact (hes.differentiableAtFn hx).hasGradientAtFn_fderiv
    · rw [subdifferential_eq_empty_of_essentiallySmooth hf hp hcl hes hx] at h
      exact absurd h (Set.notMem_empty v)

/-- For an essentially smooth closed proper convex function the domain `D` of the Legendre
conjugate is exactly `dom ∂f*`, the set where `f*` has a subgradient. -/
theorem gradientRange_eq_domSubdifferential_convexConj (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (hes : EssentiallySmooth f) :
    gradientRange f = domSubdifferential (innerₗ E) (convexConj (innerₗ E) f) := by
  ext w
  rw [mem_gradientRange, mem_domSubdifferential, Set.nonempty_def]
  refine exists_congr fun z => ?_
  rw [hasGradientAtFn_toDual_iff_mem_subdifferential hf hp hcl hes]
  exact (mem_subdifferential_convexConj_innerL_iff hf hcl z w).symm

/-- `ri (dom f*) ⊆ D`: a closed proper convex function has a subgradient at every point of the
relative interior of its effective domain, applied to `f*`. -/
theorem relint_convexDom_convexConj_subset_gradientRange (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hes : EssentiallySmooth f) :
    ri (convexDom (convexConj (innerₗ E) f)) ⊆ gradientRange f := by
  rw [gradientRange_eq_domSubdifferential_convexConj hf hp hcl hes]
  exact fun w hw =>
    subdifferential_nonempty_of_mem_relint_convexDom (convexFn_convexConj _ f)
        (properConvex_convexConj ⟨hf, hcl, hp⟩) hw

/-- `D ⊆ dom f*`: a point carrying a subgradient of `f*` is a point where `f*` is finite. -/
theorem gradientRange_subset_convexDom_convexConj (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hes : EssentiallySmooth f) : gradientRange f ⊆ convexDom (convexConj (innerₗ E) f) := by
  rw [gradientRange_eq_domSubdifferential_convexConj hf hp hcl hes]
  exact domSubdifferential_subset_convexDom (properConvex_convexConj ⟨hf, hcl, hp⟩)

/-- The Legendre conjugate `g` — which is `f*` restricted to `D` — is strictly convex on every
convex subset of `D`. -/
theorem strictConvexOnFn_convexConj_of_subset_gradientRange (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (hes : EssentiallySmooth f) {C : Set E} (hC : Convex ℝ C)
    (hCsub : C ⊆ gradientRange f) : StrictConvexOnFn (convexConj (innerₗ E) f) C :=
  (essentiallyStrictlyConvex_convexConj_iff_essentiallySmooth hf hp hcl).2 hes hC
    (by rw [← gradientRange_eq_domSubdifferential_convexConj hf hp hcl hes]; exact hCsub)

/-! ### Functions of Legendre type -/

/-- A convex function of Legendre type: essentially smooth, and strictly convex on the interior of
its effective domain. Classically the property belongs to the pair `(C, f)`, `C = int (dom f)`. -/
def LegendreType (f : E → EReal) : Prop :=
  EssentiallySmooth f ∧ StrictConvexOnFn f (interior (convexDom f))

/-- A closed proper convex function is of Legendre type exactly when `∂f` is a one-to-one
mapping: at most one subgradient at each point, and no subgradient shared by two points. -/
theorem legendreType_iff_subdifferential_injective (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) :
    LegendreType f ↔
      ((∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton) ∧
        ∀ x₁ x₂ : E, x₁ ≠ x₂ →
          Disjoint (subdifferential (innerₗ E) f x₁) (subdifferential (innerₗ E) f x₂)) :=
  (subdifferential_injective_iff hf hp hcl).symm

/-- Being of Legendre type is self-dual: `f*` is of Legendre type exactly when `f` is. Both sides
become single-valuedness and injectivity of a subdifferential, and inverting the subdifferential
swaps those two conditions. -/
theorem legendreType_convexConj_iff (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f) :
    LegendreType (convexConj (innerₗ E) f) ↔ LegendreType f := by
  rw [legendreType_iff_subdifferential_injective (convexFn_convexConj _ f)
      (properConvex_convexConj ⟨hf, hcl, hp⟩)
      closedConvex_convexConj,
    legendreType_iff_subdifferential_injective hf hp hcl,
    subsingleton_subdifferential_convexConj_iff hf hcl,
        pairwise_disjoint_subdifferential_convexConj_iff hf hcl,
    and_comm]

theorem LegendreType.convexConj (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hleg : LegendreType f) : LegendreType (ConvexAnalysis.convexConj (innerₗ E) f) :=
  (legendreType_convexConj_iff hf hp hcl).2 hleg

/-- `∇f* = (∇f)⁻¹`: `v` is the gradient of `f` at `x` exactly when `x` is that of `f*` at `v`. -/
theorem hasGradientAtFn_convexConj_iff (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hleg : LegendreType f) :
    HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x ↔
      HasGradientAtFn (convexConj (innerₗ E) f) (InnerProductSpace.toDual ℝ E x) v := by
  rw [hasGradientAtFn_toDual_iff_mem_subdifferential hf hp hcl hleg.1,
    hasGradientAtFn_toDual_iff_mem_subdifferential (convexFn_convexConj _ f)
        (properConvex_convexConj ⟨hf, hcl, hp⟩)
      closedConvex_convexConj (hleg.convexConj hf hp hcl).1,
    mem_subdifferential_convexConj_innerL_iff hf hcl]

/-- `∇f` maps `C = int (dom f)` onto `C* = int (dom f*)`. -/
theorem gradientRange_eq_interior_convexDom_convexConj (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hleg : LegendreType f) : gradientRange f = interior (convexDom (convexConj (innerₗ E) f)) := by
  rw [gradientRange_eq_domSubdifferential_convexConj hf hp hcl hleg.1,
    domSubdifferential_eq_interior_convexDom_of_essentiallySmooth (convexFn_convexConj _ f)
      (properConvex_convexConj ⟨hf, hcl, hp⟩) closedConvex_convexConj (hleg.convexConj hf hp hcl).1]

/-- Two points with the same gradient are equal, when `f` is of Legendre type: both are gradients
of `f*` at the common value, and a gradient is unique. -/
theorem eq_of_hasGradientAtFn_of_legendreType (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hleg : LegendreType f) {x₁ x₂ : E}
    (h₁ : HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x₁)
    (h₂ : HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x₂) : x₁ = x₂ := by
  rw [hasGradientAtFn_convexConj_iff hf hp hcl hleg] at h₁ h₂
  have h := h₁.fderiv_toReal_eq.symm.trans h₂.fderiv_toReal_eq
  exact (InnerProductSpace.toDual ℝ E).injective h

/-- `∇f` is a one-to-one mapping of `C` onto `C*`. -/
theorem bijOn_gradient_of_legendreType (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hleg : LegendreType f) :
    Set.BijOn (gradient fun w => (f w).toReal) (interior (convexDom f))
      (interior (convexDom (convexConj (innerₗ E) f))) := by
  have hrange := gradientRange_eq_interior_convexDom_convexConj hf hp hcl hleg
  refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ h => ?_, fun w hw => ?_⟩
  · rw [← hrange]
    exact (hleg.1.differentiableAtFn hz).hasGradientAtFn_gradient.mem_gradientRange
  · refine eq_of_hasGradientAtFn_of_legendreType hf hp hcl hleg
      (v := gradient (fun w => (f w).toReal) z₁)
      (hleg.1.differentiableAtFn hz₁).hasGradientAtFn_gradient ?_
    rw [h]
    exact (hleg.1.differentiableAtFn hz₂).hasGradientAtFn_gradient
  · rw [← hrange] at hw
    obtain ⟨z, hz⟩ := hw
    exact ⟨z, hz.mem_interior_convexDom, by
      rw [hz.gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]⟩

/-- `∇f*` undoes `∇f` on `C`. -/
theorem gradient_convexConj_gradient (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hleg : LegendreType f) (hx : x ∈ interior (convexDom f)) :
    gradient (fun w => (convexConj (innerₗ E) f w).toReal)
      (gradient (fun w => (f w).toReal) x) = x := by
  have hgrad := (hleg.1.differentiableAtFn hx).hasGradientAtFn_gradient
  rw [hasGradientAtFn_convexConj_iff hf hp hcl hleg] at hgrad
  rw [hgrad.gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]

/-- `∇f` undoes `∇f*` on `C*`. -/
theorem gradient_gradient_convexConj (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hleg : LegendreType f) (hv : v ∈ interior (convexDom (convexConj (innerₗ E) f))) :
    gradient (fun w => (f w).toReal)
      (gradient (fun w => (convexConj (innerₗ E) f w).toReal) v) = v := by
  have hgleg := hleg.convexConj hf hp hcl
  have hgrad := (hgleg.1.differentiableAtFn hv).hasGradientAtFn_gradient
  rw [← hasGradientAtFn_convexConj_iff hf hp hcl hleg] at hgrad
  rw [hgrad.gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]

/-! ### Continuity of the gradient mapping -/

/-- `∇f` is continuous where `f` is differentiable, with the gradient read as a vector. -/
theorem continuousOn_gradient_toReal (hf : ConvexFn f) (hp : ProperConvex f) :
    ContinuousOn (gradient fun w => (f w).toReal) {z | DifferentiableAtFn f z} :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    (continuousOn_fderiv_toReal hf hp)

/-- For an essentially smooth `f`, `∇f` is continuous on `int (dom f)`. Applied to `f` and to `f*`,
this gives continuity of `∇f` and of its inverse `∇f*`. -/
theorem continuousOn_gradient_interior_convexDom (hf : ConvexFn f) (hp : ProperConvex f)
    (hes : EssentiallySmooth f) :
    ContinuousOn (gradient fun w => (f w).toReal) (interior (convexDom f)) :=
  (continuousOn_gradient_toReal hf hp).mono fun _ hz => hes.differentiableAtFn hz

/-! ### Finite differentiable convex functions -/

omit [FiniteDimensional ℝ E] in
/-- A convex function that is finite and differentiable everywhere is essentially smooth: condition
(c) is vacuous, because every point lies in `interior (dom f) = E`. -/
theorem essentiallySmooth_of_convexDom_eq_univ (hdom : convexDom f = Set.univ)
    (hdiff : ∀ z : E, DifferentiableAtFn f z) : EssentiallySmooth f where
  interior_convexDom_nonempty := by rw [hdom, interior_univ]; exact Set.univ_nonempty
  differentiableAtFn := fun z _ => hdiff z
  tendsto_norm_fderiv := fun z hz => absurd (by rw [hdom, interior_univ]; trivial) hz

/-- A proper convex function that is finite everywhere is closed. -/
theorem closedConvex_of_convexDom_eq_univ (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) :
    ClosedConvex f :=
  hf.closedConvex_of_convexDom_eq_coe hp (M := (⊤ : AffineSubspace ℝ E))
    (by rw [hdom, AffineSubspace.top_coe])

/-- For a convex function that is finite and differentiable everywhere, `∇f` maps `E` one-to-one
onto `E` exactly when `f` is strictly convex and `dom f*` is all of `E`. The second condition is
*co-finiteness*; the recession function does not appear here, so the equation is stated directly.
-/
theorem bijOn_gradient_univ_iff (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ)
    (hdiff : ∀ z : E, DifferentiableAtFn f z) :
    Set.BijOn (gradient fun w => (f w).toReal) Set.univ Set.univ ↔
      StrictConvexOnFn f Set.univ ∧ convexDom (convexConj (innerₗ E) f) = Set.univ := by
  have hcl : ClosedConvex f := closedConvex_of_convexDom_eq_univ hf hp hdom
  have hes : EssentiallySmooth f := essentiallySmooth_of_convexDom_eq_univ hdom hdiff
  have hint : interior (convexDom f) = Set.univ := by rw [hdom, interior_univ]
  constructor
  · intro hbij
    -- Injectivity of `∇f` is injectivity of `∂f`, since the two relations agree.
    have hinj : ∀ x₁ x₂ : E, x₁ ≠ x₂ →
        Disjoint (subdifferential (innerₗ E) f x₁) (subdifferential (innerₗ E) f x₂) := by
      intro x₁ x₂ hne
      rw [Set.disjoint_left]
      intro w hw₁ hw₂
      rw [← hasGradientAtFn_toDual_iff_mem_subdifferential hf hp hcl hes] at hw₁ hw₂
      exact hne (hbij.injOn (Set.mem_univ x₁) (Set.mem_univ x₂)
        (by rw [hw₁.gradient_toReal_eq, hw₂.gradient_toReal_eq]))
    have hleg : LegendreType f :=
      (subdifferential_injective_iff hf hp hcl).1
        ⟨subsingleton_subdifferential_of_essentiallySmooth hf hp hcl hes, hinj⟩
    refine ⟨by rw [← hint]; exact hleg.2, ?_⟩
    have hrange := gradientRange_eq_interior_convexDom_convexConj hf hp hcl hleg
    have huniv : gradientRange f = Set.univ := by
      refine Set.eq_univ_of_forall fun w => ?_
      obtain ⟨z, -, hz⟩ := hbij.surjOn (Set.mem_univ w)
      refine ⟨z, ?_⟩
      rw [← hz]
      exact (hdiff z).hasGradientAtFn_gradient
    rw [hrange] at huniv
    exact Set.eq_univ_of_univ_subset (huniv.ge.trans interior_subset)
  · rintro ⟨hsc, hdc⟩
    have hleg : LegendreType f := ⟨hes, by rw [hint]; exact hsc⟩
    have hbij := bijOn_gradient_of_legendreType hf hp hcl hleg
    rwa [hint, hdc, interior_univ] at hbij

/-- When `∇f` is a one-to-one mapping of `E` onto itself, `f*` is again a finite, differentiable,
strictly convex function whose own conjugate domain is everything. The hypotheses are therefore
self-dual. -/
theorem convexConj_finite_of_bijOn_gradient_univ (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) (hdiff : ∀ z : E, DifferentiableAtFn f z)
    (hbij : Set.BijOn (gradient fun w => (f w).toReal) Set.univ Set.univ) :
    convexDom (convexConj (innerₗ E) f) = Set.univ ∧
      (∀ z : E, DifferentiableAtFn (convexConj (innerₗ E) f) z) ∧
      StrictConvexOnFn (convexConj (innerₗ E) f) Set.univ := by
  obtain ⟨hsc, hdc⟩ := (bijOn_gradient_univ_iff hf hp hdom hdiff).1 hbij
  have hcl : ClosedConvex f := closedConvex_of_convexDom_eq_univ hf hp hdom
  have hes : EssentiallySmooth f := essentiallySmooth_of_convexDom_eq_univ hdom hdiff
  have hint : interior (convexDom f) = Set.univ := by rw [hdom, interior_univ]
  have hgleg := (LegendreType.convexConj (f := f) hf hp hcl ⟨hes, by rw [hint]; exact hsc⟩)
  have hintc : interior (convexDom (convexConj (innerₗ E) f)) = Set.univ :=
      by rw [hdc, interior_univ]
  exact ⟨hdc, fun z => hgleg.1.differentiableAtFn (by rw [hintc]; trivial),
    by rw [← hintc]; exact hgleg.2⟩

end LegendreType

end ConvexAnalysis
