/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.Reconstruction

/-!
# Essential smoothness

Let $E$ be a finite-dimensional real inner product space, let $f : E \to [-\infty, +\infty]$ be
convex, and let $C = \operatorname{int}(\operatorname{dom} f)$. The function $f$ is **essentially
smooth** when (a) $C$ is nonempty, (b) $f$ is differentiable at every point of $C$, and (c)
$\|\nabla f(x_i)\| \to \infty$ for every sequence $(x_i)$ in $C$ that converges to a point outside
$C$. For a closed proper convex function, this holds exactly when the subdifferential is
single-valued, that is, when every $\partial f(x)$ has at most one element. In that case
$\partial f(x) = \{\nabla f(x)\}$ for $x \in C$ and $\partial f(x) = \emptyset$ otherwise, so the
multivalued map $\partial f$ carries exactly the information of the classical gradient map. This
makes the Legendre transformation work. The presentation follows [rockafellar1970convex], §26.

## Main definitions

* `ConvexAnalysis.EssentiallySmooth`: conditions (a), (b) and (c).

## Main results

* `ConvexAnalysis.domSubdifferential_eq_interior_convexDom_of_essentiallySmooth`: for an essentially
  smooth closed proper convex function, $\operatorname{dom} \partial f =
  \operatorname{int}(\operatorname{dom} f)$.
* `ConvexAnalysis.subsingleton_subdifferential_iff_essentiallySmooth`: a closed proper convex
  function is essentially smooth if and only if its subdifferential is single-valued. This is
  Theorem 26.1 of [rockafellar1970convex].

## Implementation notes

* Condition (c) is stated at every point outside $C$, while [rockafellar1970convex] states it at the
  boundary points of $C$. A sequence in $C$ can converge only to a point of the closure of $C$, and
  $C$ is open, so the two forms agree. The form used here avoids a proof that the point is a
  boundary point at every use.
* The gradient is the Fréchet derivative `fderiv ℝ (fun z => (f z).toReal)`, an element of
  `StrongDual ℝ E`. The subdifferential for the pairing `innerₗ E` is a set of vectors, so gradients
  are compared with subgradients through the Riesz isomorphism `InnerProductSpace.toDual ℝ E`.
-/

namespace ConvexAnalysis

open Filter Metric Topology

section EssentiallySmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- **Essential smoothness.** Let $E$ be a finite-dimensional real inner product space, let
$f : E \to [-\infty, +\infty]$, and let $C = \operatorname{int}(\operatorname{dom} f)$. Then $f$
is **essentially smooth** if

* (a) $C$ is nonempty;
* (b) $f$ is differentiable at every point of $C$;
* (c) for every point $z \notin C$ and every sequence $(z_i)$ in $C$ with $z_i \to z$,
  $\|\nabla f(z_i)\| \to \infty$.

A convex function that is finite and differentiable on all of $E$ is essentially smooth, since
then condition (c) holds vacuously.

Condition (c) is stated for all points outside $C$, not only for boundary points of $C$; the two
forms agree because $C$ is open. The norm in (c) is the operator norm of
`fderiv ℝ (fun w => (f w).toReal) (zs i)`, and differentiability is
`ConvexAnalysis.DifferentiableAtFn`. -/
structure EssentiallySmooth (f : E → EReal) : Prop where
  /-- Condition (a): the interior of the effective domain is nonempty. -/
  interior_convexDom_nonempty : (interior (convexDom f)).Nonempty
  /-- Condition (b): $f$ is differentiable at every interior point of its effective domain. -/
  differentiableAtFn : ∀ ⦃z : E⦄, z ∈ interior (convexDom f) → DifferentiableAtFn f z
  /-- Condition (c): for every point $z$ outside $\operatorname{int}(\operatorname{dom} f)$ and
  every sequence $(z_i)$ in $\operatorname{int}(\operatorname{dom} f)$ with $z_i \to z$,
  $\|\nabla f(z_i)\| \to \infty$. -/
  tendsto_norm_fderiv : ∀ ⦃z : E⦄, z ∉ interior (convexDom f) → ∀ zs : ℕ → E,
    (∀ i, zs i ∈ interior (convexDom f)) → Tendsto zs atTop (𝓝 z) →
      Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop

/-- Let $f$ be convex and essentially smooth, and let
$x \in \operatorname{int}(\operatorname{dom} f)$. Then the gradient is the only subgradient at
$x$: $\partial f(x) = \{\nabla f(x)\}$, where $\nabla f(x)$ is the vector that represents the
Fréchet derivative. -/
theorem subdifferential_eq_singleton_of_essentiallySmooth (hf : ConvexFn f)
    (hes : EssentiallySmooth f) (hx : x ∈ interior (convexDom f)) :
    subdifferential (innerₗ E) f x
      = {(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun w => (f w).toReal) x)} :=
  subdifferential_innerL_eq_singleton hf
    (DifferentiableAtFn.hasGradientAtFn_fderiv (hes.differentiableAtFn hx))

/-- Let $f$ be closed, proper, convex and essentially smooth, and let $x \notin
\operatorname{int}(\operatorname{dom} f)$. Then $\partial f(x) = \emptyset$.

A subgradient at $x$ would give a sequence of gradients that converges, and condition (c)
excludes this. -/
theorem subdifferential_eq_empty_of_essentiallySmooth (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (hes : EssentiallySmooth f) (hx : x ∉ interior (convexDom f)) :
    subdifferential (innerₗ E) f x = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨v, hv⟩
  -- A subgradient is built from limits of gradients, by convex hull and normal cone.
  rw [subdifferential_eq_closure_convexHull_gradientLimits_add_normalCone hf hp hcl
    hes.interior_convexDom_nonempty] at hv
  obtain ⟨a, ha, _, _, _⟩ := hv
  have hSne : (gradientLimits f x).Nonempty := by
    rcases (gradientLimits f x).eq_empty_or_nonempty with hempty | hne
    · rw [hempty, convexHull_empty, closure_empty] at ha
      exact absurd ha (Set.notMem_empty a)
    · exact hne
  obtain ⟨w, xs, vs, hxs, hgrad, hvs⟩ := hSne
  -- The gradients are eventually bounded, contradicting (c).
  have hint : ∀ i, xs i ∈ interior (convexDom f) := fun i => (hgrad i).mem_interior_convexDom
  have hfd : ∀ i, fderiv ℝ (fun z => (f z).toReal) (xs i) = InnerProductSpace.toDual ℝ E (vs i) :=
    fun i => (hgrad i).fderiv_toReal_eq
  have hnorm : ∀ i, ‖fderiv ℝ (fun z => (f z).toReal) (xs i)‖ = ‖vs i‖ := fun i => by
    rw [hfd i, LinearIsometryEquiv.norm_map]
  have htop := hes.tendsto_norm_fderiv hx xs hint hxs
  rw [tendsto_congr hnorm] at htop
  exact not_tendsto_atTop_of_tendsto_nhds (hvs.norm) htop

/-- Let $E$ be a finite-dimensional real inner product space, and let $f : E \to [-\infty, +\infty]$
be closed, proper, convex and essentially smooth. Then the domain of the subdifferential is the
interior of the effective domain:
$$\operatorname{dom} \partial f = \operatorname{int}(\operatorname{dom} f).$$
-/
theorem domSubdifferential_eq_interior_convexDom_of_essentiallySmooth (hf : ConvexFn f)
    (hp : ProperConvex f)
    (hcl : ClosedConvex f) (hes : EssentiallySmooth f) :
    domSubdifferential (innerₗ E) f = interior (convexDom f) := by
  ext z
  rw [mem_domSubdifferential]
  constructor
  · intro hne
    by_contra hz
    rw [subdifferential_eq_empty_of_essentiallySmooth hf hp hcl hes hz] at hne
    exact absurd hne (Set.not_nonempty_empty)
  · intro hz
    rw [subdifferential_eq_singleton_of_essentiallySmooth hf hes hz]
    exact Set.singleton_nonempty _

/-- Let $f$ be closed, proper, convex and essentially smooth. Then $\partial f(x)$ has at most one
element, for every $x \in E$. -/
theorem subsingleton_subdifferential_of_essentiallySmooth (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (hes : EssentiallySmooth f) (x : E) :
    (subdifferential (innerₗ E) f x).Subsingleton := by
  by_cases hx : x ∈ interior (convexDom f)
  · rw [subdifferential_eq_singleton_of_essentiallySmooth hf hes hx]
    exact Set.subsingleton_singleton
  · rw [subdifferential_eq_empty_of_essentiallySmooth hf hp hcl hes hx]
    exact Set.subsingleton_empty

/-- Let $f$ be proper and convex, and let $\partial f(z)$ have at most one element for every $z$.
Then $f$ is differentiable at every point $x \in \operatorname{ri}(\operatorname{dom} f)$.

A subgradient exists at every point of $\operatorname{ri}(\operatorname{dom} f)$,
single-valuedness makes it the only one, and a unique subgradient is a gradient. -/
theorem differentiableAtFn_of_subsingleton_subdifferential (hf : ConvexFn f) (hp : ProperConvex f)
    (h : ∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton) (hx : x ∈ ri (convexDom f)) :
    DifferentiableAtFn f x := by
  obtain ⟨v, hv⟩ := subdifferential_nonempty_of_mem_relint_convexDom (B := innerₗ E) hf hp hx
  exact ⟨_, hasGradientAtFn_toDual_of_subdifferential_eq_singleton hf hp
    (Set.eq_singleton_iff_unique_mem.2 ⟨hv, fun z hz => h x hz hv⟩)⟩

/-- Let $f$ be closed, proper and convex, and let $\partial f(z)$ have at most one element for every
$z$. Then $f$ is essentially smooth.

Conditions (a) and (b) hold because a gradient exists only at interior points, which forces
$\operatorname{ri}(\operatorname{dom} f) = \operatorname{int}(\operatorname{dom} f)$. Condition
(c) holds because a bounded subsequence of gradients would converge to a subgradient at the
limit point. -/
theorem essentiallySmooth_of_subsingleton_subdifferential (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) (h : ∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton) :
    EssentiallySmooth f := by
  have hri : ∀ ⦃z : E⦄, z ∈ ri (convexDom f) → z ∈ interior (convexDom f) := fun z hz =>
    (differentiableAtFn_of_subsingleton_subdifferential hf hp h
        hz).choose_spec.mem_interior_convexDom
  have hne : (interior (convexDom f)).Nonempty := by
    obtain ⟨z, hz⟩ := Convex.relint_nonempty hf.convex_convexDom hp.convexDom_nonempty
    exact ⟨z, hri hz⟩
  refine ⟨hne, fun z hz => differentiableAtFn_of_subsingleton_subdifferential hf hp h
    (Convex.interior_subset_relint hz), ?_⟩
  intro z hz zs hzs hlim
  by_contra hcon
  -- A bounded subsequence of gradients.
  obtain ⟨b, hb⟩ := not_forall.1 (tendsto_atTop.not.1 hcon)
  obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_of_frequently_atTop (Filter.not_eventually.1 hb)
  set vs : ℕ → E := fun i => (InnerProductSpace.toDual ℝ E).symm
    (fderiv ℝ (fun w => (f w).toReal) (zs i)) with hvsdef
  have hgrad : ∀ i, HasGradientAtFn f (InnerProductSpace.toDual ℝ E (vs i)) (zs i) := fun i => by
    rw [hvsdef, LinearIsometryEquiv.apply_symm_apply]
    exact DifferentiableAtFn.hasGradientAtFn_fderiv
      (differentiableAtFn_of_subsingleton_subdifferential hf hp h
        (Convex.interior_subset_relint (hzs i)))
  have hvsb : ∀ n, vs (φ n) ∈ closedBall (0 : E) b := fun n => by
    rw [mem_closedBall_zero_iff, hvsdef, LinearIsometryEquiv.norm_map]
    exact (not_le.1 (hφb n)).le
  -- Its limit is a subgradient at `z`, so `f` is differentiable at `z` and `z` is interior.
  obtain ⟨w, _, ψ, hψ, hψlim⟩ := (isCompact_closedBall (0 : E) b).tendsto_subseq hvsb
  have hmem : w ∈ gradientLimits f z :=
    ⟨fun n => zs (φ (ψ n)), fun n => vs (φ (ψ n)), hlim.comp (hφ.comp hψ).tendsto_atTop,
      fun n => hgrad (φ (ψ n)), hψlim⟩
  have hsub : w ∈ subdifferential (innerₗ E) f z :=
    gradientLimits_subset_subdifferential hf hp hcl hmem
  exact hz (hasGradientAtFn_toDual_of_subdifferential_eq_singleton hf hp
    (Set.eq_singleton_iff_unique_mem.2 ⟨hsub, fun u hu => h z hu hsub⟩)).mem_interior_convexDom

/-- Let $E$ be a finite-dimensional real inner product space, and let $f : E \to [-\infty, +\infty]$
be closed, proper and convex. Then $\partial f$ is single-valued, that is, $\partial f(z)$ has
at most one element for every $z \in E$, if and only if $f$ is essentially smooth.

This is Theorem 26.1 of [rockafellar1970convex]. The subdifferential is taken for the inner
product `innerₗ E`. -/
theorem subsingleton_subdifferential_iff_essentiallySmooth (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f) :
    (∀ z : E, (subdifferential (innerₗ E) f z).Subsingleton) ↔ EssentiallySmooth f :=
  ⟨essentiallySmooth_of_subsingleton_subdifferential hf hp hcl,
    subsingleton_subdifferential_of_essentiallySmooth hf hp hcl⟩

end EssentiallySmooth

end ConvexAnalysis
