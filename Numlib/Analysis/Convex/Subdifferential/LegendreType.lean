/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Numlib.Analysis.Convex.Subdifferential.Legendre
import Numlib.Analysis.Convex.Subdifferential.StrictlyConvex

/-!
# Convex functions of Legendre type

Let $E$ be a finite-dimensional real inner product space, let $f \colon E \to [-\infty, +\infty]$ be
a closed proper convex function, and let $C = \operatorname{int}(\operatorname{dom} f)$. The
function $f$ is **of Legendre type** if it is essentially smooth and strictly convex on $C$;
equivalently, $\partial f$ is a one-to-one mapping. The property is self-dual: $f$ is of Legendre
type if and only if $f^*$ is. Then $\nabla f$ is a bijection of $C$ onto $C^* =
\operatorname{int}(\operatorname{dom} f^*)$, continuous in both directions, with
$\nabla f^* = (\nabla f)^{-1}$. This is Theorem 26.5 of [rockafellar1970convex].

For an essentially smooth $f$, the domain $D = \nabla f(C)$ of the Legendre conjugate is
$\operatorname{dom} \partial f^*$. Therefore $\operatorname{ri}(\operatorname{dom} f^*) \subseteq D
\subseteq \operatorname{dom} f^*$. In general $D$ is not convex, and this is why the two inclusions
cannot be improved to an equality.

## Main definitions

* `ConvexAnalysis.gradientRange`: the set $D$ of all gradients of $f$, as a set of vectors of $E$.
* `ConvexAnalysis.LegendreType`: $f$ is essentially smooth and strictly convex on
  $\operatorname{int}(\operatorname{dom} f)$.

## Main results

* `ConvexAnalysis.hasGradientAtFn_toDual_iff_mem_subdifferential`: for an essentially smooth closed
  proper convex $f$, $v$ is the gradient of $f$ at $x$ if and only if $v$ is a subgradient of $f$ at
  $x$. The other results combine this equivalence with $\partial f^* = (\partial f)^{-1}$.
* `ConvexAnalysis.gradientRange_eq_domSubdifferential_convexConj`:
  $D = \operatorname{dom} \partial f^*$.
* `ConvexAnalysis.relint_convexDom_convexConj_subset_gradientRange`,
  `ConvexAnalysis.gradientRange_subset_convexDom_convexConj`: $\operatorname{ri}(\operatorname{dom}
  f^*) \subseteq D \subseteq \operatorname{dom} f^*$.
* `ConvexAnalysis.legendreType_convexConj_iff`: $f^*$ is of Legendre type if and only if $f$ is
  ([rockafellar1970convex], Theorem 26.5).
* `ConvexAnalysis.bijOn_gradient_of_legendreType`: for $f$ of Legendre type, $\nabla f$ is a
  bijection of $C$ onto $C^*$ ([rockafellar1970convex], Theorem 26.5).
* `ConvexAnalysis.continuousOn_gradient_interior_convexDom`: for an essentially smooth $f$,
  $\nabla f$ is continuous on $C$ ([rockafellar1970convex], Theorem 26.5).
* `ConvexAnalysis.bijOn_gradient_univ_iff`: for a convex function that is finite and differentiable
  on all of $E$, $\nabla f$ is a bijection of $E$ onto $E$ if and only if $f$ is strictly convex and
  $\operatorname{dom} f^* = E$.
* `ConvexAnalysis.convexConj_finite_of_bijOn_gradient_univ`: under these conditions, $f^*$ is again
  finite, differentiable and strictly convex on all of $E$.

## Implementation notes

* `ConvexAnalysis.legendreDom f` is a set in `StrongDual ℝ E`, but it is compared with
  $\operatorname{dom} \partial f^*$, whose elements are vectors of $E$ for the pairing `innerₗ E`.
  `ConvexAnalysis.gradientRange` is `ConvexAnalysis.legendreDom` carried back across the Riesz
  isometry `InnerProductSpace.toDual`, so that the comparison is an equality of sets in $E$.
* The gradient mapping $\nabla f$ is Mathlib's `gradient` of the real-valued function
  `fun w => (f w).toReal`.
-/

namespace ConvexAnalysis

open scoped RealInnerProductSpace

section LegendreType

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x v : E} {f' : StrongDual ℝ E}

/-! ### The range of the gradient mapping, in vector form -/

/-- The **domain of the Legendre conjugate**, as a set of vectors: the set of $v \in E$ such that,
for some $x \in E$, $f$ has at $x$ the gradient that corresponds to $v$ under the Riesz
isomorphism. This is the preimage of `ConvexAnalysis.legendreDom f` under
`InnerProductSpace.toDual`. -/
def gradientRange (f : E → EReal) : Set E :=
  {v | ∃ x, HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x}

/-- A vector $v$ is in `ConvexAnalysis.gradientRange f` if and only if $f$ has the gradient
`InnerProductSpace.toDual ℝ E v` at some point. -/
@[simp] theorem mem_gradientRange :
    v ∈ gradientRange f ↔ ∃ x, HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x := Iff.rfl

/-- A vector $v$ is in `ConvexAnalysis.gradientRange f` if and only if its Riesz image is in
`ConvexAnalysis.legendreDom f`. -/
theorem mem_gradientRange_iff_mem_legendreDom :
    v ∈ gradientRange f ↔ InnerProductSpace.toDual ℝ E v ∈ legendreDom f := Iff.rfl

/-- If $f$ has the gradient `InnerProductSpace.toDual ℝ E v` at $x$, then $v$ is in
`ConvexAnalysis.gradientRange f`. -/
theorem HasGradientAtFn.mem_gradientRange
    (h : HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x) : v ∈ gradientRange f := ⟨x, h⟩

/-- If $f$ has the gradient $f'$ at $x$, then Mathlib's `gradient` of the real-valued function
`fun w => (f w).toReal` at $x$ is the vector that corresponds to $f'$ under the Riesz
isomorphism. -/
theorem HasGradientAtFn.gradient_toReal_eq (h : HasGradientAtFn f f' x) :
    gradient (fun w => (f w).toReal) x = (InnerProductSpace.toDual ℝ E).symm f' := by
  unfold gradient
  rw [h.fderiv_toReal_eq]

/-- If $f$ is differentiable at $x$, then $f$ has at $x$ the gradient that corresponds to the vector
`gradient (fun w => (f w).toReal) x`. -/
theorem DifferentiableAtFn.hasGradientAtFn_gradient (h : DifferentiableAtFn f x) :
    HasGradientAtFn f (InnerProductSpace.toDual ℝ E (gradient (fun w => (f w).toReal) x)) x := by
  obtain ⟨g, hg⟩ := h
  rw [hg.gradient_toReal_eq, LinearIsometryEquiv.apply_symm_apply]
  exact hg

/-! ### The domain of the Legendre conjugate -/

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f \colon E \to [-\infty, +\infty]$ be a closed proper convex function that is essentially
smooth. Then for all $x, v \in E$, the function $f$ has the gradient $v$ at $x$ if and only if
$$v \in \partial f(x).$$

On the interior of $\operatorname{dom} f$ the only subgradient is the gradient. Outside the
interior, both sides are false. The gradient $v$ is `InnerProductSpace.toDual ℝ E v`, and the
subgradients are taken for the pairing `innerₗ E`. -/
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

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f \colon E \to [-\infty, +\infty]$ be a closed proper convex function that is essentially
smooth. Then the domain of the Legendre conjugate is the set of points where $f^*$ has a
subgradient:
$$D = \operatorname{dom} \partial f^*.$$

Here $D$ is `ConvexAnalysis.gradientRange f`, and the conjugate and the subgradients are taken
for the pairing `innerₗ E`. -/
theorem gradientRange_eq_domSubdifferential_convexConj (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (hes : EssentiallySmooth f) :
    gradientRange f = domSubdifferential (innerₗ E) (convexConj (innerₗ E) f) := by
  ext w
  rw [mem_gradientRange, mem_domSubdifferential, Set.nonempty_def]
  refine exists_congr fun z => ?_
  rw [hasGradientAtFn_toDual_iff_mem_subdifferential hf hp hcl hes]
  exact (mem_subdifferential_convexConj_innerL_iff hf hcl z w).symm

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f \colon E \to [-\infty, +\infty]$ be a closed proper convex function that is essentially
smooth. Then
$$\operatorname{ri}(\operatorname{dom} f^*) \subseteq D,$$
where $D$ is `ConvexAnalysis.gradientRange f`.

The closed proper convex function $f^*$ has a subgradient at every point of the relative
interior of its effective domain. -/
theorem relint_convexDom_convexConj_subset_gradientRange (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hes : EssentiallySmooth f) :
    ri (convexDom (convexConj (innerₗ E) f)) ⊆ gradientRange f := by
  rw [gradientRange_eq_domSubdifferential_convexConj hf hp hcl hes]
  exact fun w hw =>
    subdifferential_nonempty_of_mem_relint_convexDom (convexFn_convexConj _ f)
        (properConvex_convexConj ⟨hf, hcl, hp⟩) hw

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f \colon E \to [-\infty, +\infty]$ be a closed proper convex function that is essentially
smooth. Then
$$D \subseteq \operatorname{dom} f^*,$$
where $D$ is `ConvexAnalysis.gradientRange f`: a point where $f^*$ has a subgradient is a point
where $f^*$ is finite. -/
theorem gradientRange_subset_convexDom_convexConj (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hes : EssentiallySmooth f) : gradientRange f ⊆ convexDom (convexConj (innerₗ E) f) := by
  rw [gradientRange_eq_domSubdifferential_convexConj hf hp hcl hes]
  exact domSubdifferential_subset_convexDom (properConvex_convexConj ⟨hf, hcl, hp⟩)

/-- Let $f$ be a closed proper convex function that is essentially smooth, and let $C$ be a convex
subset of $D$, the domain of the Legendre conjugate. Then $f^*$ is strictly convex on $C$. So
the Legendre conjugate, which is the restriction of $f^*$ to $D$, is strictly convex on every
convex subset of $D$. -/
theorem strictConvexOnFn_convexConj_of_subset_gradientRange (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (hes : EssentiallySmooth f) {C : Set E} (hC : Convex ℝ C)
    (hCsub : C ⊆ gradientRange f) : StrictConvexOnFn (convexConj (innerₗ E) f) C :=
  (essentiallyStrictlyConvex_convexConj_iff_essentiallySmooth hf hp hcl).2 hes hC
    (by rw [← gradientRange_eq_domSubdifferential_convexConj hf hp hcl hes]; exact hCsub)

/-! ### Functions of Legendre type -/

/-- A function $f \colon E \to [-\infty, +\infty]$ is **of Legendre type** if it is essentially
smooth and strictly convex on $\operatorname{int}(\operatorname{dom} f)$.

In [rockafellar1970convex] the property belongs to the pair $(C, f)$ with
$C = \operatorname{int}(\operatorname{dom} f)$. -/
def LegendreType (f : E → EReal) : Prop :=
  EssentiallySmooth f ∧ StrictConvexOnFn f (interior (convexDom f))

/-- A closed proper convex function $f$ is of Legendre type if and only if $\partial f$ is a
one-to-one mapping: $\partial f(z)$ has at most one element for every $z$, and $\partial f(x_1)
\cap \partial f(x_2) = \emptyset$ whenever $x_1 \neq x_2$. -/
theorem legendreType_iff_subdifferential_injective (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) :
    LegendreType f ↔
      ((∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton) ∧
        ∀ x₁ x₂ : E, x₁ ≠ x₂ →
          Disjoint (subdifferential (innerₗ E) f x₁) (subdifferential (innerₗ E) f x₂)) :=
  (subdifferential_injective_iff hf hp hcl).symm

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f \colon E \to [-\infty, +\infty]$ be a closed proper convex function. Then
$$f^* \text{ is of Legendre type} \iff f \text{ is of Legendre type}.$$
This is part of Theorem 26.5 of [rockafellar1970convex].

By `ConvexAnalysis.legendreType_iff_subdifferential_injective`, each side says that a
subdifferential is single-valued and one-to-one. The inversion
$\partial f^* = (\partial f)^{-1}$ exchanges these two conditions. The conjugate is taken for
the pairing `innerₗ E`. -/
theorem legendreType_convexConj_iff (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f) :
    LegendreType (convexConj (innerₗ E) f) ↔ LegendreType f := by
  rw [legendreType_iff_subdifferential_injective (convexFn_convexConj _ f)
      (properConvex_convexConj ⟨hf, hcl, hp⟩)
      closedConvex_convexConj,
    legendreType_iff_subdifferential_injective hf hp hcl,
    subsingleton_subdifferential_convexConj_iff hf hcl,
        pairwise_disjoint_subdifferential_convexConj_iff hf hcl,
    and_comm]

/-- If a closed proper convex function $f$ is of Legendre type, then so is $f^*$. -/
theorem LegendreType.convexConj (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hleg : LegendreType f) : LegendreType (ConvexAnalysis.convexConj (innerₗ E) f) :=
  (legendreType_convexConj_iff hf hp hcl).2 hleg

/-- Let $f$ be a closed proper convex function of Legendre type. Then $f$ has the gradient $v$ at
$x$ if and only if $f^*$ has the gradient $x$ at $v$. This is $\nabla f^* = (\nabla f)^{-1}$. -/
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

/-- Let $f$ be a closed proper convex function of Legendre type. Then the set of gradients of $f$ is
$\operatorname{int}(\operatorname{dom} f^*)$: $\nabla f$ maps
$C = \operatorname{int}(\operatorname{dom} f)$ onto $C^* = \operatorname{int}(\operatorname{dom}
f^*)$. -/
theorem gradientRange_eq_interior_convexDom_convexConj (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hleg : LegendreType f) : gradientRange f = interior (convexDom (convexConj (innerₗ E) f)) := by
  rw [gradientRange_eq_domSubdifferential_convexConj hf hp hcl hleg.1,
    domSubdifferential_eq_interior_convexDom_of_essentiallySmooth (convexFn_convexConj _ f)
      (properConvex_convexConj ⟨hf, hcl, hp⟩) closedConvex_convexConj (hleg.convexConj hf hp hcl).1]

/-- Let $f$ be a closed proper convex function of Legendre type. If $f$ has the same gradient $v$ at
$x_1$ and at $x_2$, then $x_1 = x_2$: both are gradients of $f^*$ at $v$, and a gradient is
unique. -/
theorem eq_of_hasGradientAtFn_of_legendreType (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hleg : LegendreType f) {x₁ x₂ : E}
    (h₁ : HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x₁)
    (h₂ : HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x₂) : x₁ = x₂ := by
  rw [hasGradientAtFn_convexConj_iff hf hp hcl hleg] at h₁ h₂
  have h := h₁.fderiv_toReal_eq.symm.trans h₂.fderiv_toReal_eq
  exact (InnerProductSpace.toDual ℝ E).injective h

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f \colon E \to [-\infty, +\infty]$ be a closed proper convex function of Legendre type. Then
the gradient mapping $\nabla f$ is a bijection
$$\nabla f \colon \operatorname{int}(\operatorname{dom} f) \to
  \operatorname{int}(\operatorname{dom} f^*).$$
This is part of Theorem 26.5 of [rockafellar1970convex].

The gradient mapping is Mathlib's `gradient` of the real-valued function
`fun w => (f w).toReal`, and the conjugate is taken for the pairing `innerₗ E`. -/
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

/-- Let $f$ be a closed proper convex function of Legendre type. Then $\nabla f^*(\nabla f(x)) = x$
for every $x \in \operatorname{int}(\operatorname{dom} f)$. -/
theorem gradient_convexConj_gradient (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hleg : LegendreType f) (hx : x ∈ interior (convexDom f)) :
    gradient (fun w => (convexConj (innerₗ E) f w).toReal)
      (gradient (fun w => (f w).toReal) x) = x := by
  have hgrad := (hleg.1.differentiableAtFn hx).hasGradientAtFn_gradient
  rw [hasGradientAtFn_convexConj_iff hf hp hcl hleg] at hgrad
  rw [hgrad.gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]

/-- Let $f$ be a closed proper convex function of Legendre type. Then $\nabla f(\nabla f^*(v)) = v$
for every $v \in \operatorname{int}(\operatorname{dom} f^*)$. -/
theorem gradient_gradient_convexConj (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hleg : LegendreType f) (hv : v ∈ interior (convexDom (convexConj (innerₗ E) f))) :
    gradient (fun w => (f w).toReal)
      (gradient (fun w => (convexConj (innerₗ E) f w).toReal) v) = v := by
  have hgleg := hleg.convexConj hf hp hcl
  have hgrad := (hgleg.1.differentiableAtFn hv).hasGradientAtFn_gradient
  rw [← hasGradientAtFn_convexConj_iff hf hp hcl hleg] at hgrad
  rw [hgrad.gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]

/-! ### Continuity of the gradient mapping -/

/-- Let $f$ be a proper convex function. Then the gradient mapping $\nabla f$, with the gradient
read as a vector, is continuous on the set of points where $f$ is differentiable. -/
theorem continuousOn_gradient_toReal (hf : ConvexFn f) (hp : ProperConvex f) :
    ContinuousOn (gradient fun w => (f w).toReal) {z | DifferentiableAtFn f z} :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
    (continuousOn_fderiv_toReal hf hp)

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f \colon E \to [-\infty, +\infty]$ be a proper convex function that is essentially smooth. Then
the gradient mapping $\nabla f$ is continuous on $\operatorname{int}(\operatorname{dom} f)$.
This is part of Theorem 26.5 of [rockafellar1970convex].

Applied to $f$ and to $f^*$, the result gives the continuity of $\nabla f$ and of its inverse
$\nabla f^*$. The gradient mapping is Mathlib's `gradient` of the real-valued function
`fun w => (f w).toReal`. -/
theorem continuousOn_gradient_interior_convexDom (hf : ConvexFn f) (hp : ProperConvex f)
    (hes : EssentiallySmooth f) :
    ContinuousOn (gradient fun w => (f w).toReal) (interior (convexDom f)) :=
  (continuousOn_gradient_toReal hf hp).mono fun _ hz => hes.differentiableAtFn hz

/-! ### Finite differentiable convex functions -/

omit [FiniteDimensional ℝ E] in
/-- A function $f \colon E \to [-\infty, +\infty]$ with $\operatorname{dom} f = E$ that is
differentiable at every point of $E$ is essentially smooth. Condition (c) of essential
smoothness holds vacuously, because every point is in
$\operatorname{int}(\operatorname{dom} f) = E$. -/
theorem essentiallySmooth_of_convexDom_eq_univ (hdom : convexDom f = Set.univ)
    (hdiff : ∀ z : E, DifferentiableAtFn f z) : EssentiallySmooth f where
  interior_convexDom_nonempty := by rw [hdom, interior_univ]; exact Set.univ_nonempty
  differentiableAtFn := fun z _ => hdiff z
  tendsto_norm_fderiv := fun z hz => absurd (by rw [hdom, interior_univ]; trivial) hz

/-- Let $E$ be a finite-dimensional real inner product space. A proper convex function
$f \colon E \to [-\infty, +\infty]$ with $\operatorname{dom} f = E$ is closed. -/
theorem closedConvex_of_convexDom_eq_univ (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) :
    ClosedConvex f :=
  hf.closedConvex_of_convexDom_eq_coe hp (M := (⊤ : AffineSubspace ℝ E))
    (by rw [hdom, AffineSubspace.top_coe])

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f \colon E \to [-\infty, +\infty]$ be a proper convex function that is finite and
differentiable at every point of $E$. Then $\nabla f$ is a bijection of $E$ onto $E$ if and only
if
$$f \text{ is strictly convex on } E \quad \text{and} \quad \operatorname{dom} f^* = E.$$

The second condition is co-finiteness of $f$. It is stated directly as
$\operatorname{dom} f^* = E$, without the recession function. The gradient mapping is Mathlib's
`gradient` of the real-valued function `fun w => (f w).toReal`, and the conjugate is taken for
the pairing `innerₗ E`. -/
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

/-- Let $E$ be a finite-dimensional real inner product space, and let
$f \colon E \to [-\infty, +\infty]$ be a proper convex function that is finite and
differentiable at every point of $E$, such that $\nabla f$ is a bijection of $E$ onto $E$. Then
$f^*$ is finite at every point of $E$, differentiable at every point of $E$, and strictly convex
on $E$.

So $f^*$ satisfies the same hypotheses as $f$, and the situation is self-dual. -/
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
