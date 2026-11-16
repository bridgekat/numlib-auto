/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Rademacher
import Numlib.Analysis.Convex.Subdifferential.Convergence
import Numlib.Analysis.Convex.Subdifferential.Gradient
import Numlib.Analysis.Convex.Subdifferential.Uniqueness

/-!
# Almost everywhere differentiability of a convex function

Let $E$ be a finite-dimensional real normed space and let $f \colon E \to [-\infty, +\infty]$ be a
proper convex function with effective domain $\operatorname{dom} f = \{x : f(x) < +\infty\}$. This
module proves that $f$ is differentiable at almost every point of
$\operatorname{int}(\operatorname{dom} f)$ for every Haar measure on $E$, that the points of
differentiability are dense in $\operatorname{int}(\operatorname{dom} f)$, and, when $E$ is an inner
product space, that the gradient map $x \mapsto \nabla f(x)$ is continuous on the set of points of
differentiability. This is Theorem 25.5 of [rockafellar1970convex]. As a corollary, in each fixed
direction $y$ the two-sided directional derivative $f'(x; y) = -f'(x; -y)$ exists at almost every
point of $\operatorname{int}(\operatorname{dom} f)$.

The module also relates the two pairings that the library uses on a real inner product space $E$:
the inner product of $E$ with itself, for which subgradients are vectors, and the canonical pairing
of $E$ with its continuous dual, for which subgradients and gradients are functionals. By the Riesz
representation $v \mapsto \langle v, \cdot \rangle$ the two give the same subdifferentials and
conjugates. Finally, it computes the normal cone to the closed unit ball at a point of the unit
sphere.

## Main results

* `ConvexAnalysis.HasGradientAtFn.hasFDerivAt_toReal`: a gradient $f'$ of $f$ at $x$ is a Fréchet
  derivative at $x$ of the real function $z \mapsto f(z)$.
* `ConvexAnalysis.hasGradientAtFn_of_hasFDerivAt_toReal`: conversely, at a point of
  $\operatorname{int}(\operatorname{dom} f)$, a Fréchet derivative of $z \mapsto f(z)$ is a gradient
  of $f$.
* `ConvexAnalysis.exists_lipschitzOnWith_ball`: $f$ is Lipschitz on an open ball around each point
  of $\operatorname{int}(\operatorname{dom} f)$.
* `ConvexAnalysis.ae_differentiableAtFn`: $f$ is differentiable at almost every point of
  $\operatorname{int}(\operatorname{dom} f)$.
* `ConvexAnalysis.measure_diff_twoSided_dirDeriv`: for each direction $y$, the equation
  $f'(x; y) = -f'(x; -y)$ holds at almost every $x \in \operatorname{int}(\operatorname{dom} f)$.
* `ConvexAnalysis.interior_convexDom_subset_closure_differentiableAtFn`: the points of
  differentiability are dense in $\operatorname{int}(\operatorname{dom} f)$.
* `ConvexAnalysis.topDualPairing_flip_toDual`,
  `ConvexAnalysis.convexConj_innerL_eq_convexConj_topDualPairing` and
  `ConvexAnalysis.mem_subdifferential_innerL_iff`: the two pairings of an inner product space give
  the same pairing values, conjugates and subgradients, up to the Riesz map.
* `ConvexAnalysis.subdifferential_innerL_eq_singleton`: at a point of differentiability, the
  subdifferential for the inner product is the single vector that represents the gradient.
* `ConvexAnalysis.continuousOn_fderiv_toReal`: the gradient map is continuous on the set of points
  of differentiability.
* `ConvexAnalysis.continuousOn_fderiv_of_convexOn`: a finite convex function that is differentiable
  on an open convex set is continuously differentiable there.
* `ConvexAnalysis.normalCone_innerₗ_closedBall`: the normal cone to the closed unit ball at a point
  $x$ with $\|x\| = 1$ is the ray $\{\lambda x : \lambda \ge 0\}$.

## Proof outline

Rademacher's theorem from Mathlib does the analysis, and convexity supplies only the local Lipschitz
constants. Convexity gives a Lipschitz constant on each compact subset of the relative interior of
$\operatorname{dom} f$, and `ConvexAnalysis.exists_lipschitzOnWith_ball` shrinks a closed ball to an
open one, on which differentiability within the ball is differentiability. The density statement
uses no measure in its statement: a nonempty open set has positive Haar measure, so it is not
contained in a null set.

The classical proof goes the other way. It proves the existence of the two-sided directional
derivative in a fixed direction first, by a Fubini argument over lines, and then obtains full
differentiability from the coordinate directions. With Rademacher's theorem, differentiability comes
first, and it gives the two-sided derivative in every direction at once.

## Implementation notes

* The function $f$ takes values in `EReal`. A gradient of $f$ at $x$
  (`ConvexAnalysis.HasGradientAtFn`) is the derivative at $x$ of a real function that agrees with
  $f$ near $x$. The results here compare it with Mathlib's `fderiv` of the real function
  `fun z => (f z).toReal`.
* Results stated for the pairing `innerₗ E` have vectors as subgradients, and gradients are elements
  of `StrongDual ℝ E`. The Riesz map `InnerProductSpace.toDual ℝ E` translates between the two.
-/

namespace ConvexAnalysis

open Filter MeasureTheory Metric Topology
open scoped NNReal

/-! ### Differentiability through the real trace -/

section RealTrace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal}
  {f' : StrongDual ℝ E} {x : E}

omit [NormedSpace ℝ E] in
/-- Let $f \colon E \to [-\infty, +\infty]$ be proper and let
$x \in \operatorname{int}(\operatorname{dom} f)$. Then on a neighbourhood of $x$, $f$ is equal
to the coercion of the real function $z \mapsto f(z)$, called the **real trace** of $f$, which
is `fun z => (f z).toReal`. -/
theorem eventuallyEq_coe_toReal (hp : ProperConvex f) (hx : x ∈ interior (convexDom f)) :
    f =ᶠ[𝓝 x] fun z => (((f z).toReal : ℝ) : EReal) := by
  filter_upwards [isOpen_interior.mem_nhds hx] with z hz
  exact (EReal.coe_toReal (mem_convexDom.1 (interior_subset hz)).ne (hp.ne_bot z)).symm

/-- Let $E$ be a real normed space and $f \colon E \to [-\infty, +\infty]$. If $f$ has the gradient
$f'$ at $x$, then the real trace $z \mapsto f(z)$ of $f$ has the Fréchet derivative $f'$ at $x$.

The real trace is `fun z => (f z).toReal`, and the gradient is `ConvexAnalysis.HasGradientAtFn`.
No convexity is needed. -/
theorem HasGradientAtFn.hasFDerivAt_toReal (h : HasGradientAtFn f f' x) :
    HasFDerivAt (fun z => (f z).toReal) f' x := by
  obtain ⟨g, hfg, hd⟩ := h
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hfg] with z hz
  rw [hz, EReal.toReal_coe]

/-- Let $E$ be a real normed space, let $f \colon E \to [-\infty, +\infty]$ be proper, and let
$x \in \operatorname{int}(\operatorname{dom} f)$. If the real trace $z \mapsto f(z)$ of $f$ has
the Fréchet derivative $f'$ at $x$, then $f$ has the gradient $f'$ at $x$.

The real trace is `fun z => (f z).toReal`. The hypothesis on $x$ makes $f$ equal to its real
trace near $x$, by `ConvexAnalysis.eventuallyEq_coe_toReal`. -/
theorem hasGradientAtFn_of_hasFDerivAt_toReal (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f))
    (hd : HasFDerivAt (fun z => (f z).toReal) f' x) : HasGradientAtFn f f' x :=
  ⟨_, eventuallyEq_coe_toReal hp hx, hd⟩

/-- Let $f \colon E \to [-\infty, +\infty]$ be proper and let
$x \in \operatorname{int}(\operatorname{dom} f)$. Then $f$ has the gradient $f'$ at $x$ if and
only if the real trace $z \mapsto f(z)$ of $f$ has the Fréchet derivative $f'$ at $x$. -/
theorem hasGradientAtFn_iff_hasFDerivAt_toReal (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) :
    HasGradientAtFn f f' x ↔ HasFDerivAt (fun z => (f z).toReal) f' x :=
  ⟨HasGradientAtFn.hasFDerivAt_toReal, hasGradientAtFn_of_hasFDerivAt_toReal hp hx⟩

/-- Let $f \colon E \to [-\infty, +\infty]$ be proper and let
$x \in \operatorname{int}(\operatorname{dom} f)$. Then $f$ is differentiable at $x$ if and only
if its real trace $z \mapsto f(z)$ is Fréchet differentiable at $x$. -/
theorem differentiableAtFn_iff_differentiableAt_toReal (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) :
    DifferentiableAtFn f x ↔ DifferentiableAt ℝ (fun z => (f z).toReal) x :=
  ⟨fun ⟨_, h⟩ => h.hasFDerivAt_toReal.differentiableAt,
    fun h => ⟨_, hasGradientAtFn_of_hasFDerivAt_toReal hp hx h.hasFDerivAt⟩⟩

/-- If $f$ has the gradient $f'$ at $x$, then Mathlib's `fderiv` of the real trace $z \mapsto f(z)$
at $x$ is $f'$. -/
theorem HasGradientAtFn.fderiv_toReal_eq (h : HasGradientAtFn f f' x) :
    fderiv ℝ (fun z => (f z).toReal) x = f' :=
  h.hasFDerivAt_toReal.fderiv

/-- If $f$ is differentiable at $x$, then the `fderiv` of its real trace $z \mapsto f(z)$ at $x$ is
a gradient of $f$ at $x$. This gives a name to the gradient $\nabla f(x)$. -/
theorem DifferentiableAtFn.hasGradientAtFn_fderiv (h : DifferentiableAtFn f x) :
    HasGradientAtFn f (fderiv ℝ (fun z => (f z).toReal) x) x := by
  obtain ⟨f', hf'⟩ := h
  rw [hf'.fderiv_toReal_eq]
  exact hf'

end RealTrace

/-! ### Differentiability almost everywhere -/

section Rademacher

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E}

/-- Let $E$ be a finite-dimensional real normed space, let $f \colon E \to [-\infty, +\infty]$ be a
proper convex function, and let $x \in \operatorname{int}(\operatorname{dom} f)$. Then there is
$r > 0$ such that the open ball $B(x, r)$ is contained in
$\operatorname{int}(\operatorname{dom} f)$ and the real trace $z \mapsto f(z)$ is Lipschitz on
$B(x, r)$ with some constant $K \ge 0$.

An open ball is what Rademacher's theorem needs, because differentiability within an open set is
differentiability. -/
theorem exists_lipschitzOnWith_ball (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) :
    ∃ r > 0, ball x r ⊆ interior (convexDom f) ∧
      ∃ K : ℝ≥0, LipschitzOnWith K (fun z => (f z).toReal) (ball x r) := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith_of_isCompact hp (isCompact_closedBall x (r / 2))
    (((closedBall_subset_ball (by linarith)).trans hsub).trans interior_subset_intrinsicInterior)
  exact ⟨r / 2, by linarith, (ball_subset_ball (by linarith)).trans hsub,
    K, hK.mono ball_subset_closedBall⟩

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Let $E$ be a finite-dimensional real normed space with a Haar measure $\mu$, and let
$f \colon E \to [-\infty, +\infty]$ be a proper convex function. Then for $\mu$-almost every
$z$, if $z \in \operatorname{int}(\operatorname{dom} f)$, then $f$ is differentiable at $z$.

This is the almost-everywhere part of Theorem 25.5 of [rockafellar1970convex]. The proof applies
Mathlib's Rademacher theorem to the real trace on the balls of
`ConvexAnalysis.exists_lipschitzOnWith_ball`. -/
theorem ae_differentiableAtFn (hf : ConvexFn f) (hp : ProperConvex f) :
    ∀ᵐ z ∂μ, z ∈ interior (convexDom f) → DifferentiableAtFn f z := by
  choose! r hr hball K hK using fun z (hz : z ∈ interior (convexDom f)) =>
    exists_lipschitzOnWith_ball hf hp hz
  obtain ⟨T, hTc, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun p : interior (convexDom f) => ball (p : E) (r p)) fun _ => isOpen_ball
  have hcover : ∀ z ∈ interior (convexDom f), ∃ p ∈ T, z ∈ ball ((p : E)) (r p) := by
    intro z hz
    have hmem : z ∈ ⋃ p : interior (convexDom f), ball ((p : E)) (r p) :=
      Set.mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hr z hz)⟩
    rw [← hTeq] at hmem
    simpa using hmem
  have hae : ∀ᵐ z ∂μ, ∀ p ∈ T, z ∈ ball ((p : E)) (r p) →
      DifferentiableWithinAt ℝ (fun w => (f w).toReal) (ball ((p : E)) (r p)) z :=
    (ae_ball_iff hTc).2 fun p _ => (hK (p : E) p.2).ae_differentiableWithinAt_of_mem
  filter_upwards [hae] with z hz hzU
  obtain ⟨p, hpT, hzp⟩ := hcover z hzU
  exact (differentiableAtFn_iff_differentiableAt_toReal hp hzU).2
    ((hz p hpT hzp).differentiableAt (isOpen_ball.mem_nhds hzp))

/-- Let $E$ be a finite-dimensional real normed space with a Haar measure $\mu$, and let $f$ be a
proper convex function on $E$. The set of points of $\operatorname{int}(\operatorname{dom} f)$
at which $f$ is not differentiable has $\mu$-measure zero. -/
theorem measure_diff_differentiableAtFn (hf : ConvexFn f) (hp : ProperConvex f) :
    μ (interior (convexDom f) \ {z | DifferentiableAtFn f z}) = 0 := by
  have hae := ae_differentiableAtFn (μ := μ) hf hp
  rw [ae_iff] at hae
  refine measure_mono_null (fun z hz => ?_) hae
  change ¬(z ∈ interior (convexDom f) → DifferentiableAtFn f z)
  exact fun hcon => hz.2 (hcon hz.1)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Let $E$ be a real normed space, let $f$ be a convex function on $E$, and let $f$ be
differentiable at $x$. Then for every direction $y$ the two-sided directional derivative exists:
$f'(x; y) = -f'(x; -y)$. Both sides are equal to the value of the gradient at $y$.

The one-sided directional derivative $f'(x; y)$ is `ConvexAnalysis.dirDeriv`. -/
theorem twoSided_dirDeriv_of_differentiableAtFn (hf : ConvexFn f)
    (h : DifferentiableAtFn f x) (y : E) : dirDeriv f x y = -dirDeriv f x (-y) := by
  obtain ⟨f', hf'⟩ := h
  rw [hf'.dirDeriv_eq hf, hf'.dirDeriv_eq hf, map_neg, EReal.coe_neg, neg_neg]

/-- Let $E$ be a finite-dimensional real normed space with a Haar measure $\mu$, let $f$ be a proper
convex function on $E$, and let $y \in E$. Then the set of points
$x \in \operatorname{int}(\operatorname{dom} f)$ at which
$$f'(x; y) \neq -f'(x; -y)$$
has $\mu$-measure zero. That is, in the fixed direction $y$ the two-sided directional derivative
exists almost everywhere in $\operatorname{int}(\operatorname{dom} f)$.

Classically this statement comes first and full differentiability is derived from it. Here it is
a consequence of `ConvexAnalysis.ae_differentiableAtFn`, which gives the two-sided derivative in
every direction at once. -/
theorem measure_diff_twoSided_dirDeriv (hf : ConvexFn f) (hp : ProperConvex f) (y : E) :
    μ (interior (convexDom f) \ {z | dirDeriv f z y = -dirDeriv f z (-y)}) = 0 := by
  refine measure_mono_null (fun z hz => ?_) (measure_diff_differentiableAtFn (μ := μ) hf hp)
  obtain ⟨hzU, hzy⟩ := hz
  exact Set.mem_sdiff_of_mem hzU fun hzd =>
    hzy (twoSided_dirDeriv_of_differentiableAtFn hf hzd y)

end Rademacher

section Dense

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- Let $E$ be a finite-dimensional real normed space and let $f$ be a proper convex function on
$E$. Then every point of $\operatorname{int}(\operatorname{dom} f)$ is in the closure of the set
of points at which $f$ is differentiable.

This is the density part of Theorem 25.5 of [rockafellar1970convex]. The statement contains no
measure, but the proof uses a Haar measure: a nonempty open set has positive measure, so it is
not contained in the null set of `ConvexAnalysis.measure_diff_differentiableAtFn`. -/
theorem interior_convexDom_subset_closure_differentiableAtFn (hf : ConvexFn f)
    (hp : ProperConvex f) :
    interior (convexDom f) ⊆ closure {z | DifferentiableAtFn f z} := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let w := Module.Basis.ofVectorSpace ℝ E
  intro x hx
  refine mem_closure_iff.2 fun V hV hxV => ?_
  by_contra hne
  have hsub : V ∩ interior (convexDom f)
      ⊆ interior (convexDom f) \ {z | DifferentiableAtFn f z} := by
    rintro z ⟨hzV, hzU⟩
    exact ⟨hzU, fun hzD => hne ⟨z, hzV, hzD⟩⟩
  have hpos : 0 < w.addHaar (V ∩ interior (convexDom f)) :=
    (hV.inter isOpen_interior).measure_pos _ ⟨x, hxV, hx⟩
  exact hpos.ne' (measure_mono_null hsub (measure_diff_differentiableAtFn hf hp))

end Dense

/-! ### Continuity of the gradient -/

section GradientContinuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {f' : StrongDual ℝ E}

/-- Let $E$ be a real inner product space and let $x, v \in E$. Pairing $x$ with the functional
$\langle v, \cdot \rangle$ in the canonical pairing of $E$ with its continuous dual gives the
inner product $\langle x, v \rangle$.

The functional $\langle v, \cdot \rangle$ is `InnerProductSpace.toDual ℝ E v`, the canonical
pairing is `(topDualPairing ℝ E).flip`, and the inner product is `innerₗ E`. The other bridge
results of this section follow from this identity. -/
theorem topDualPairing_flip_toDual (x v : E) :
    (topDualPairing ℝ E).flip x (InnerProductSpace.toDual ℝ E v) = (innerₗ E) x v := by
  simp [innerₗ_apply_apply, real_inner_comm]

/-- Let $E$ be a real inner product space, let $f \colon E \to [-\infty, +\infty]$ and let
$v \in E$. The conjugate of $f$ for the inner product, evaluated at $v$, is equal to the
conjugate of $f$ for the canonical pairing with the dual, evaluated at the functional
$\langle v, \cdot \rangle$:
$$\sup_x \big( \langle x, v \rangle - f(x) \big) = \sup_x \big( \langle v, x \rangle - f(x)
  \big).$$

The conjugate is `ConvexAnalysis.convexConj`, the pairings are `innerₗ E` and
`(topDualPairing ℝ E).flip`, and the functional is `InnerProductSpace.toDual ℝ E v`. This
carries results about conjugates proved on a normed space with the pairing
$\langle x, y \rangle = y(x)$ over to `convexConj (innerₗ E)`. -/
theorem convexConj_innerL_eq_convexConj_topDualPairing (f : E → EReal) (v : E) :
    convexConj (innerₗ E) f v
        = convexConj (topDualPairing ℝ E).flip f (InnerProductSpace.toDual ℝ E v) := by
  simp only [convexConj_apply]
  exact iSup_congr fun x => by rw [topDualPairing_flip_toDual x v]

/-- Let $E$ be a real inner product space and $f \colon E \to [-\infty, +\infty]$. A vector $v$ is a
subgradient of $f$ at $x$ for the inner product if and only if the functional
$\langle v, \cdot \rangle$ is a subgradient of $f$ at $x$ for the canonical pairing of $E$ with
its continuous dual.

The pairings are `innerₗ E` and `(topDualPairing ℝ E).flip`, and the functional is
`InnerProductSpace.toDual ℝ E v`. -/
theorem mem_subdifferential_innerL_iff {v : E} :
    v ∈ subdifferential (innerₗ E) f x ↔
      InnerProductSpace.toDual ℝ E v ∈ subdifferential (topDualPairing ℝ E).flip f x := by
  simp only [mem_subdifferential]
  exact forall_congr' fun z => by rw [← topDualPairing_flip_toDual (z - x) v]

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be a convex function on $E$
with the gradient $f'$ at $x$. Then the subdifferential of $f$ at $x$ for the inner product is
the single vector that represents $f'$:
$$\partial f(x) = \{\nabla f(x)\}.$$

The vector is `(InnerProductSpace.toDual ℝ E).symm f'`, and the subdifferential is taken for the
pairing `innerₗ E`. -/
theorem subdifferential_innerL_eq_singleton (hf : ConvexFn f) (h : HasGradientAtFn f f' x) :
    subdifferential (innerₗ E) f x = {(InnerProductSpace.toDual ℝ E).symm f'} := by
  ext v
  rw [mem_subdifferential_innerL_iff, h.subdifferential_eq hf, Set.mem_singleton_iff,
    Set.mem_singleton_iff]
  exact ⟨fun hv => by rw [← hv, LinearIsometryEquiv.symm_apply_apply],
    fun hv => by rw [hv, LinearIsometryEquiv.apply_symm_apply]⟩

/-- Let $E$ be a finite-dimensional real inner product space and
$f \colon E \to [-\infty, +\infty]$. If the subdifferential of $f$ at $x$ for the inner product
is $\{v\}$, then the subdifferential of $f$ at $x$ for the canonical pairing with the dual is
$\{\langle v, \cdot \rangle\}$. -/
theorem subdifferential_topDualPairing_eq_singleton {v : E}
    (h : subdifferential (innerₗ E) f x = {v}) :
    subdifferential (topDualPairing ℝ E).flip f x = {InnerProductSpace.toDual ℝ E v} := by
  ext g
  rw [Set.mem_singleton_iff]
  constructor
  · intro hg
    have hmem : (InnerProductSpace.toDual ℝ E).symm g ∈ subdifferential (innerₗ E) f x := by
      rw [mem_subdifferential_innerL_iff, LinearIsometryEquiv.apply_symm_apply]
      exact hg
    rw [h, Set.mem_singleton_iff] at hmem
    rw [← hmem, LinearIsometryEquiv.apply_symm_apply]
  · rintro rfl
    exact mem_subdifferential_innerL_iff.1 (by rw [h]; rfl)

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be a proper convex function
on $E$. If the subdifferential of $f$ at $x$ for the inner product is $\{v\}$, then $f$ has the
gradient $\langle v, \cdot \rangle$ at $x$. -/
theorem hasGradientAtFn_toDual_of_subdifferential_eq_singleton (hf : ConvexFn f)
    (hp : ProperConvex f)
    {v : E} (h : subdifferential (innerₗ E) f x = {v}) :
    HasGradientAtFn f (InnerProductSpace.toDual ℝ E v) x :=
  hasGradientAtFn_of_subdifferential_eq_singleton hf hp
    (subdifferential_topDualPairing_eq_singleton h)

/-- Let $E$ be a finite-dimensional real inner product space and let $f$ be a proper convex function
on $E$. Then the gradient map $x \mapsto \nabla f(x)$ is continuous on the set of points at
which $f$ is differentiable.

This is the continuity part of Theorem 25.5 of [rockafellar1970convex]. The gradient map is the
`fderiv` of the real trace `fun w => (f w).toReal`, with values in `StrongDual ℝ E`. The proof
is the upper semicontinuity of $\partial f$ in the case where all the subdifferentials involved
are singletons. -/
theorem continuousOn_fderiv_toReal (hf : ConvexFn f) (hp : ProperConvex f) :
    ContinuousOn (fderiv ℝ fun w => (f w).toReal) {z | DifferentiableAtFn f z} := by
  set g := fderiv ℝ fun w => (f w).toReal with hgdef
  have hgrad : ∀ z ∈ {z | DifferentiableAtFn f z}, HasGradientAtFn f (g z) z := fun _ hz =>
    DifferentiableAtFn.hasGradientAtFn_fderiv hz
  intro x hx
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hev := eventually_nhds_subdifferential_subset_add_closedBall hf hp
    (hgrad x hx).mem_interior_convexDom (half_pos hε)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hzsub hzD
  have hzz : (InnerProductSpace.toDual ℝ E).symm (g z) ∈ subdifferential (innerₗ E) f z := by
    rw [subdifferential_innerL_eq_singleton hf (hgrad z hzD)]
    rfl
  have hmem := hzsub hzz
  rw [subdifferential_innerL_eq_singleton hf (hgrad x hx)] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [Set.mem_singleton_iff] at ha
  subst ha
  rw [mem_closedBall_zero_iff] at hb
  have hnorm : ‖(InnerProductSpace.toDual ℝ E).symm (g z)
      - (InnerProductSpace.toDual ℝ E).symm (g x)‖ ≤ ε / 2 := by
    rw [← hab, add_sub_cancel_left]
    exact hb
  calc dist (g z) (g x)
      = ‖(InnerProductSpace.toDual ℝ E).symm (g z)
        - (InnerProductSpace.toDual ℝ E).symm (g x)‖ := by
        rw [dist_eq_norm, ← (InnerProductSpace.toDual ℝ E).symm.norm_map (g z - g x), map_sub]
    _ ≤ ε / 2 := hnorm
    _ < ε := half_lt_self hε

/-- Let $E$ be a finite-dimensional real inner product space, let $C \subseteq E$ be a nonempty open
set, and let $g \colon E \to \mathbb{R}$ be convex on $C$ and differentiable on $C$. Then the
derivative of $g$ is continuous on $C$, so $g$ is continuously differentiable on $C$.

The convexity hypothesis is Mathlib's `ConvexOn ℝ C g`, which includes the convexity of $C$. The
proof applies `ConvexAnalysis.continuousOn_fderiv_toReal` to the extension of $g$ by $+\infty$
outside $C$. Since $C$ is open, this extension has the same gradients as $g$ on $C$. -/
theorem continuousOn_fderiv_of_convexOn {C : Set E} {g : E → ℝ} (hC : IsOpen C)
    (hne : C.Nonempty) (hg : ConvexOn ℝ C g) (hd : DifferentiableOn ℝ g C) :
    ContinuousOn (fderiv ℝ g) C := by
  set f : E → EReal := convexRestrict C fun z => ((g z : ℝ) : EReal) with hfdef
  have hcf : ConvexFn f := (convexOn_iff_convexFn C g).1 hg
  have hdom : convexDom f = C := by
    ext z
    by_cases hz : z ∈ C <;> simp [hfdef, hz]
  have hp : ProperConvex f := ⟨by rw [hdom]; exact hne, fun z => by
    by_cases hz : z ∈ C <;> simp [hfdef, hz]⟩
  have hint : interior (convexDom f) = C := by rw [hdom, hC.interior_eq]
  have hgrad : ∀ z ∈ C, HasGradientAtFn f (fderiv ℝ g z) z := fun z hz => by
    refine ⟨g, ?_, ((hd z hz).differentiableAt (hC.mem_nhds hz)).hasFDerivAt⟩
    filter_upwards [hC.mem_nhds hz] with w hw
    simp [hfdef, hw]
  have hsub : C ⊆ {z | DifferentiableAtFn f z} := fun z hz => ⟨_, hgrad z hz⟩
  exact ((continuousOn_fderiv_toReal hcf hp).mono hsub).congr fun z hz =>
    (HasGradientAtFn.fderiv_toReal_eq (hgrad z hz)).symm

end GradientContinuity

/-! ### The normal cone to the unit ball -/

section NormalCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let $E$ be a real inner product space and let $x \in E$ with $\|x\| = 1$. The normal cone to the
closed unit ball $B$ at $x$ is the ray through $x$:
$$N_B(x) = \{\lambda x : \lambda \ge 0\}.$$

The normal cone is taken for the pairing `innerₗ E`. This result turns the optimality condition
at a maximizer over the ball into the eigenvalue condition $\lambda x \in \partial f(x)$. Both
inclusions are the case of equality in the Cauchy–Schwarz inequality, so $E$ need not be
finite-dimensional or complete. -/
theorem normalCone_innerₗ_closedBall {x : E} (hx : ‖x‖ = 1) :
    normalCone (innerₗ E) (closedBall (0 : E) 1) x
      = {y : E | ∃ lam : ℝ, 0 ≤ lam ∧ y = lam • x} := by
  have hxx : (inner ℝ x x : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_mul_norm, hx, mul_one]
  ext y
  simp only [mem_normalCone, Set.mem_ofPred_eq, map_sub, LinearMap.sub_apply, sub_nonpos,
    mem_closedBall, dist_zero_right, innerₗ_apply_apply]
  constructor
  · intro hy
    rcases eq_or_ne y 0 with rfl | hy0
    · exact ⟨0, le_rfl, by simp⟩
    have hn0 : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hmem : ‖(‖y‖⁻¹ : ℝ) • y‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hn0)]
    have hkey := hy _ hmem
    rw [real_inner_smul_left, real_inner_self_eq_norm_mul_norm, inv_mul_eq_div, mul_div_assoc,
      div_self (ne_of_gt hn0), mul_one] at hkey
    have hcs : (inner ℝ x y : ℝ) ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
    have heq : (inner ℝ x y : ℝ) = ‖x‖ * ‖y‖ := by
      rw [hx, one_mul] at hcs ⊢
      exact le_antisymm hcs hkey
    have hsm : ‖y‖ • x = ‖x‖ • y := inner_eq_norm_mul_iff_real.1 heq
    rw [hx, one_smul] at hsm
    exact ⟨‖y‖, hn0.le, hsm.symm⟩
  · rintro ⟨lam, hlam, rfl⟩ z hz
    have hcs : (inner ℝ z x : ℝ) ≤ ‖z‖ * ‖x‖ := real_inner_le_norm z x
    rw [hx, mul_one] at hcs
    simp only [real_inner_smul_right]
    rw [hxx]
    nlinarith

end NormalCone

end ConvexAnalysis
