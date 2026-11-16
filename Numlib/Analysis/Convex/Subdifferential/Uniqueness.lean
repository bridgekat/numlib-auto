/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Analysis.Convex.Subdifferential.Convergence
import Numlib.Analysis.Convex.Subdifferential.Gradient

/-!
# A unique subgradient forces differentiability

Let $E$ be a finite-dimensional real normed space and let $f \colon E \to [-\infty, +\infty]$ be a
proper convex function. Then $f$ is differentiable at $x$ if and only if it has exactly one
subgradient at $x$, and this subgradient is then the gradient $\nabla f(x)$. This is Theorem 25.1 of
[rockafellar1970convex]. The forward direction is
`ConvexAnalysis.subdifferential_eq_singleton_of_hasFDerivAt`, and this module proves the converse.
With it, the descriptions of the exposed points of the epigraph of $f^*$ and of a support set by
single-point subdifferentials become descriptions by gradients, as in §23 and §25 of
[rockafellar1970convex].

The main step, which the proof in [rockafellar1970convex] passes over, is that a unique subgradient
puts $x$ in $\operatorname{int}(\operatorname{dom} f)$. If $\partial f(x) = \{y_0\}$, there is no
nonzero normal direction to $\operatorname{dom} f$ at $x$, and in finite dimensions a convex set is
a neighbourhood of every point at which its normal cone is trivial. At an interior point, the
directional derivative $f'(x; \cdot)$ is finite in every direction, so it is continuous and closed.
Then the support-function formula, which in general gives only the closure of $f'(x; \cdot)$, gives
$f'(x; \cdot)$ itself, and this function is linear.

## Main results

* `ConvexAnalysis.mem_interior_convexDom_of_subdifferential_eq_singleton`: if $\partial f(x)$ is a
  single point, then $x \in \operatorname{int}(\operatorname{dom} f)$.
* `ConvexAnalysis.hasGradientAtFn_iff_subdifferential_eq_singleton`: $f$ has the gradient $f'$ at
  $x$ if and only if $\partial f(x) = \{f'\}$.
* `ConvexAnalysis.differentiableAtFn_iff_exists_subdifferential_eq_singleton`: $f$ is differentiable
  at $x$ if and only if $\partial f(x)$ is a single point.
* `ConvexAnalysis.hasGradientAtFn_convexCl_iff`: $\operatorname{cl} f$ and $f$ have the same
  gradients at the same points.
* `ConvexAnalysis.mem_exposedPoints_epi_convexConj_iff_hasGradientAtFn`: the exposed points of the
  epigraph of $f^*$ are the points $(\nabla f(x), f^*(\nabla f(x)))$ at which $f$ is differentiable.
* `ConvexAnalysis.mem_exposedPoints_supportSet_iff_hasGradientAtFn`: for a positively homogeneous
  $f$, the exposed points of the set supported by $f$ are the gradients of $f$.

## Implementation notes

* Subgradients are taken for a pairing $\langle \cdot, \cdot \rangle$ of $E$ with a real vector
  space $F$. Where the gradient appears, the pairing is the canonical pairing
  `(topDualPairing ℝ E).flip` of $E$ with its continuous dual, so that subgradients and gradients
  are both elements of `StrongDual ℝ E`.
* The exposed-point results hold for a proper convex $f$ that need not be closed. They reduce to
  $\operatorname{cl} f$, which has the same conjugate and the same gradients. Only the gradient
  forms transfer in this way: $\partial f = \partial(\operatorname{cl} f)$ fails at relative
  boundary points of $\operatorname{dom} f$, so the subgradient forms
  `ConvexAnalysis.mem_exposedPoints_epi_convexConj_iff` and
  `ConvexAnalysis.mem_exposedPoints_supportSet_iff` keep their hypothesis that the function is
  closed.
-/

open Set

namespace ConvexAnalysis

/-! ### The interior step -/

section Interior

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y₀ : F}

include B in
/-- Let $E$ be a finite-dimensional real normed space, let $\langle \cdot, \cdot \rangle$ be a
compatible pairing of $E$ with a real vector space $F$, and let $f$ be a proper convex function
on $E$. If $\partial f(x) = \{y_0\}$, then $x \in \operatorname{int}(\operatorname{dom} f)$.

A compatible pairing (`ConvexAnalysis.IsCompatiblePairing`) is continuous in its first argument,
and every continuous linear functional on $E$ is $\langle \cdot, y \rangle$ for some $y \in F$.
A unique subgradient leaves no room for a nonzero normal direction to $\operatorname{dom} f$ at
$x$, and in finite dimensions a convex set is a neighbourhood of every point at which its normal
cone is trivial. -/
theorem mem_interior_convexDom_of_subdifferential_eq_singleton [IsCompatiblePairing B]
    (hf : ConvexFn f)
    (hp : ProperConvex f) (h : subdifferential B f x = {y₀}) : x ∈ interior (convexDom f) := by
  have hy₀ : y₀ ∈ subdifferential B f x := by rw [h]; rfl
  exact mem_interior_of_normalCone_eq_zero
      hf.convex_convexDom (mem_convexDom_of_mem_subdifferential hp hy₀)
    (normalCone_convexDom_eq_zero_of_subdifferential_eq_singleton h)

end Interior

/-! ### The converse half -/

section Converse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y₀ : F}

/-- Let $E$ be a finite-dimensional real normed space, let $f$ be a proper convex function on $E$
and let $x \in \operatorname{int}(\operatorname{dom} f)$. Then the directional derivative
$y \mapsto f'(x; y)$ is a closed function. It is finite in every direction, so it is a finite
convex function on $E$ and therefore continuous. This removes the closure from the
support-function formula for $f'(x; \cdot)$. -/
theorem closedConvex_dirDeriv_of_mem_interior_convexDom (hf : ConvexFn f) (hp : ProperConvex f)
    (hx : x ∈ interior (convexDom f)) : ClosedConvex (dirDeriv f x) := by
  have hri : x ∈ ri (convexDom f) := Convex.interior_subset_relint hx
  have hgp : ProperConvex (dirDeriv f x) := properConvex_dirDeriv_of_mem_relint_convexDom hf hp hri
  have hgc : ConvexFn (dirDeriv f x) :=
    convexFn_dirDeriv hf (mem_convexDom.1 (interior_subset hx)).ne (hp.ne_bot x)
  have hdom : convexDom (dirDeriv f x) = univ :=
    (convexDom_dirDeriv_eq_univ_iff_mem_interior_convexDom hf hp hri).2 hx
  exact (closedConvex_iff_lowerSemicontinuous hgp.ne_bot).2
    (hgc.continuous_of_convexDom_eq_univ hgp hdom).lowerSemicontinuous

/-- Let $E$ be a finite-dimensional real normed space, let $\langle \cdot, \cdot \rangle$ be a
compatible pairing of $E$ with $F$, and let $f$ be a proper convex function on $E$. If
$\partial f(x) = \{y_0\}$, then $f$ has the gradient $\langle \cdot, y_0 \rangle$ at $x$.

The functional $\langle \cdot, y_0 \rangle$ is `ConvexAnalysis.evalCLM B y₀`. Properness
replaces the usual hypothesis that $f(x)$ is finite. This is weaker only in appearance: where
$f(x) = -\infty$, every element of $F$ is a subgradient. -/
theorem hasGradientAtFn_evalCLM_of_subdifferential_eq_singleton [IsCompatiblePairing B]
    (hf : ConvexFn f) (hp : ProperConvex f) (h : subdifferential B f x = {y₀}) :
    HasGradientAtFn f (evalCLM B y₀) x := by
  have hint := mem_interior_convexDom_of_subdifferential_eq_singleton hf hp h
  have ht : f x ≠ ⊤ := (mem_convexDom.1 (interior_subset hint)).ne
  have hb : f x ≠ ⊥ := hp.ne_bot x
  have hcl : convexCl (dirDeriv f x) = dirDeriv f x :=
      closedConvex_dirDeriv_of_mem_interior_convexDom hf hp hint
  have heq : dirDeriv f x = fun v => ((B v y₀ : ℝ) : EReal) :=
    hcl.symm.trans (convexCl_dirDeriv_eq_of_subdifferential_eq_singleton hf ht hb h)
  exact hasGradientAtFn_of_dirDeriv_eq hf ht hb fun v => congrFun heq v

end Converse

/-! ### The equivalence in full -/

section Full

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {f' : StrongDual ℝ E}

/-- Let $E$ be a finite-dimensional real normed space and let $f$ be a proper convex function on
$E$. If $\partial f(x) = \{f'\}$ for the canonical pairing of $E$ with its continuous dual, then
$f$ has the gradient $f'$ at $x$. -/
theorem hasGradientAtFn_of_subdifferential_eq_singleton (hf : ConvexFn f) (hp : ProperConvex f)
    (h : subdifferential (topDualPairing ℝ E).flip f x = {f'}) : HasGradientAtFn f f' x :=
  hasGradientAtFn_evalCLM_of_subdifferential_eq_singleton (B := (topDualPairing ℝ E).flip) hf hp h

/-- Let $E$ be a finite-dimensional real normed space, let $f \colon E \to [-\infty, +\infty]$ be a
proper convex function, let $x \in E$ and let $f'$ be a continuous linear functional on $E$.
Then $f$ has the gradient $f'$ at $x$ if and only if
$$\partial f(x) = \{f'\}.$$

This is Theorem 25.1 of [rockafellar1970convex]. The subdifferential is taken for the canonical
pairing `(topDualPairing ℝ E).flip` of $E$ with its continuous dual. The forward direction is
`ConvexAnalysis.subdifferential_eq_singleton_of_hasFDerivAt`, and the converse is
`ConvexAnalysis.hasGradientAtFn_of_subdifferential_eq_singleton`. -/
theorem hasGradientAtFn_iff_subdifferential_eq_singleton (hf : ConvexFn f) (hp : ProperConvex f) :
    HasGradientAtFn f f' x ↔ subdifferential (topDualPairing ℝ E).flip f x = {f'} :=
  ⟨fun h => h.subdifferential_eq hf, hasGradientAtFn_of_subdifferential_eq_singleton hf hp⟩

/-- Let $E$ be a finite-dimensional real normed space and let $f$ be a proper convex function on
$E$. Then $f$ is differentiable at $x$ if and only if there is a continuous linear functional
$y$ on $E$ with $\partial f(x) = \{y\}$.

The subdifferential is taken for the canonical pairing `(topDualPairing ℝ E).flip`. This is
`ConvexAnalysis.hasGradientAtFn_iff_subdifferential_eq_singleton` without a name for the
gradient. -/
theorem differentiableAtFn_iff_exists_subdifferential_eq_singleton (hf : ConvexFn f)
    (hp : ProperConvex f) :
    DifferentiableAtFn f x ↔
      ∃ y : StrongDual ℝ E, subdifferential (topDualPairing ℝ E).flip f x = {y} :=
  exists_congr fun _ => hasGradientAtFn_iff_subdifferential_eq_singleton hf hp

end Full

/-! ### The gradients of $\operatorname{cl} f$ -/

section Closure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {f' : StrongDual ℝ E}

/-- Let $f$ be a convex function and let $x \in \operatorname{int}(\operatorname{dom} f)$. Then
$\operatorname{cl} f$ is equal to $f$ on a neighbourhood of $x$, since
$\operatorname{int}(\operatorname{dom} f)$ is open and is contained in the relative interior of
$\operatorname{dom} f$. -/
theorem ConvexFn.convexCl_eventuallyEq_of_mem_interior_convexDom (hf : ConvexFn f)
    (hx : x ∈ interior (convexDom f)) : convexCl f =ᶠ[nhds x] f := by
  filter_upwards [isOpen_interior.mem_nhds hx] with z hz
  exact hf.convexCl_eq_of_mem_relint_convexDom
      (Convex.interior_subset_relint hz)

/-- Let $E$ be a finite-dimensional real normed space, let $f$ be a proper convex function on $E$,
let $x \in E$ and let $f'$ be a continuous linear functional on $E$. Then $\operatorname{cl} f$
has the gradient $f'$ at $x$ if and only if $f$ has the gradient $f'$ at $x$. So the closure
operation changes no gradient and creates no new one.

The closure $\operatorname{cl} f$ is `ConvexAnalysis.convexCl f`. If $f$ has a gradient at $x$,
then $x \in \operatorname{int}(\operatorname{dom} f)$, where the two functions are equal near
$x$. For the converse, a gradient of $\operatorname{cl} f$ at $x$ gives only $x \in
\operatorname{int}(\operatorname{dom}(\operatorname{cl} f))$, and
`ConvexAnalysis.ConvexFn.interior_convexDom_convexCl` shows that this set is
$\operatorname{int}(\operatorname{dom} f)$. -/
theorem hasGradientAtFn_convexCl_iff (hf : ConvexFn f) (hp : ProperConvex f) :
    HasGradientAtFn (convexCl f) f' x ↔ HasGradientAtFn f f' x := by
  constructor
  · intro h
    have hx : x ∈ interior (convexDom f) := by
      rw [← hf.interior_convexDom_convexCl hp]
      exact HasGradientAtFn.mem_interior_convexDom h
    obtain ⟨g, hfg, hd⟩ := h
    exact ⟨g, (hf.convexCl_eventuallyEq_of_mem_interior_convexDom hx).symm.trans hfg, hd⟩
  · intro h
    have hx : x ∈ interior (convexDom f) := HasGradientAtFn.mem_interior_convexDom h
    obtain ⟨g, hfg, hd⟩ := h
    exact ⟨g, (hf.convexCl_eventuallyEq_of_mem_interior_convexDom hx).trans hfg, hd⟩

/-- Let $f$ be a proper convex function on a finite-dimensional real normed space. Then
$\operatorname{cl} f$ is differentiable at $x$ if and only if $f$ is differentiable at $x$. -/
theorem differentiableAtFn_convexCl_iff (hf : ConvexFn f) (hp : ProperConvex f) :
    DifferentiableAtFn (convexCl f) x ↔ DifferentiableAtFn f x :=
  exists_congr fun _ => hasGradientAtFn_convexCl_iff hf hp

end Closure

/-! ### Exposed points without closedness -/

section ClosureExposedEpi

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- Let $E$ be a finite-dimensional real normed space, let $\langle \cdot, \cdot \rangle$ be a
compatible pairing of $E$ with $F$, let $f$ be a proper convex function on $E$ and let
$y \in F$. Then there is $x$ with $\partial(\operatorname{cl} f)(x) = \{y\}$ if and only if
there is $x$ with $\partial f(x) = \{y\}$.

The two subdifferentials are equal wherever $(\operatorname{cl} f)(x) = f(x)$, and a
single-point subdifferential puts $x$ in the relative interior of $\operatorname{dom} f$, where
the two functions are equal. -/
theorem exists_subdifferential_convexCl_eq_singleton_iff [IsCompatiblePairing B] (hf : ConvexFn f)
    (hp : ProperConvex f) {y : F} :
    (∃ x : E, subdifferential B (convexCl f) x = {y}) ↔ ∃ x : E, subdifferential B f x = {y} := by
  have key : ∀ x : E,
      x ∈ interior (convexDom f) → subdifferential B (convexCl f) x = subdifferential B f x :=
    fun x hx => Set.ext fun _ => mem_subdifferential_convexCl_iff
      (hf.convexCl_eq_of_mem_relint_convexDom (Convex.interior_subset_relint hx))
  constructor
  · rintro ⟨x, hx⟩
    have hint : x ∈ interior (convexDom f) := by
      rw [← hf.interior_convexDom_convexCl hp]
      exact mem_interior_convexDom_of_subdifferential_eq_singleton (convexFn_convexCl hf)
          (hf.properConvex_convexCl hp)
        hx
    exact ⟨x, (key x hint).symm.trans hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (key x (mem_interior_convexDom_of_subdifferential_eq_singleton hf hp hx)).trans hx⟩

variable [TopologicalSpace F]

/-- Let $E$ be a finite-dimensional real normed space, let $\langle \cdot, \cdot \rangle$ be a
pairing of $E$ with a real vector space $F$ that carries a topology, such that both the pairing
and its flip are compatible, and let $f$ be a proper convex function on $E$. Then
$(y, \mu) \in F \times \mathbb{R}$ is an exposed point of the epigraph of $f^*$ if and only if
$f^*(y) = \mu$ and there is $x$ with $\partial f(x) = \{y\}$.

The function $f$ need not be closed. Since $(\operatorname{cl} f)^* = f^*$ and
`ConvexAnalysis.exists_subdifferential_convexCl_eq_singleton_iff` holds, the result follows from
`ConvexAnalysis.mem_exposedPoints_epi_convexConj_iff` for the closed function
$\operatorname{cl} f$. -/
theorem mem_exposedPoints_epi_convexConj_iff_of_properConvex [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hf : ConvexFn f) (hp : ProperConvex f) {y : F} {μ : ℝ} :
    (y, μ) ∈ (epi (convexConj B f)).exposedPoints ℝ ↔
      convexConj B f y = (μ : EReal) ∧ ∃ x : E, subdifferential B f x = {y} := by
  rw [← convexConj_convexCl (B := B) f,
    mem_exposedPoints_epi_convexConj_iff (convexFn_convexCl hf) (hf.properConvex_convexCl hp)
        (closedConvex_convexCl f)]
  exact and_congr_right fun _ => exists_subdifferential_convexCl_eq_singleton_iff hf hp

end ClosureExposedEpi

section ClosureExposedSupport

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {g : F → EReal}

/-- Let $F$ be a finite-dimensional real normed space, let $\langle \cdot, \cdot \rangle$ be a
pairing of a real vector space $E$ that carries a topology with $F$, such that both the pairing
and its flip are compatible, and let $g$ be a positively homogeneous proper convex function on
$F$. Then $z \in E$ is an exposed point of the set $\{z : \langle z, y \rangle \le g(y) \text{
for all } y\}$ supported by $g$ if and only if there is $y \in F$ with $\partial g(y) = \{z\}$.

The set is `ConvexAnalysis.supportSet B.flip g`, and $\partial g$ is taken for the pairing
`B.flip`. The function $g$ need not be closed: $\operatorname{cl} g$ supports the same set and
is again positively homogeneous. -/
theorem mem_exposedPoints_supportSet_iff_of_properConvex [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] (hgh : PosHomogeneous g) (hgc : ConvexFn g) (hgp : ProperConvex g)
    {z : E} :
    z ∈ (supportSet B.flip g).exposedPoints ℝ ↔ ∃ y : F, subdifferential B.flip g y = {z} := by
  obtain ⟨w, hw⟩ := hgp.convexDom_nonempty
  have hne : ∃ y, g y ≠ ⊤ := ⟨w, (mem_convexDom.1 hw).ne⟩
  have hph := posHomogeneous_convexCl hgh
  rw [← supportSet_convexCl (B := B) hgh hne,
    mem_exposedPoints_supportSet_iff (B := B) hph (convexFn_convexCl hgc)
    (hgc.properConvex_convexCl hgp) (closedConvex_convexCl g)]
  exact exists_subdifferential_convexCl_eq_singleton_iff hgc hgp

end ClosureExposedSupport

/-! ### Exposed points in differentiability form -/

section Exposed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- Let $E$ be a finite-dimensional real normed space, let $f$ be a proper convex function on $E$,
let $y$ be a continuous linear functional on $E$ and let $\mu \in \mathbb{R}$. Then $(y, \mu)$
is an exposed point of the epigraph of $f^*$ if and only if $f^*(y) = \mu$ and there is $x$ at
which $f$ has the gradient $y$. So the exposed points of the epigraph of $f^*$ are the points
$(\nabla f(x), f^*(\nabla f(x)))$ at which $f$ is differentiable.

The conjugate is taken for the canonical pairing `(topDualPairing ℝ E).flip`. The function $f$
need not be closed. -/
theorem mem_exposedPoints_epi_convexConj_iff_hasGradientAtFn (hf : ConvexFn f) (hp : ProperConvex f)
    {y : StrongDual ℝ E} {μ : ℝ} :
    (y, μ) ∈ (epi (convexConj (topDualPairing ℝ E).flip f)).exposedPoints ℝ ↔
      convexConj (topDualPairing ℝ E).flip f y = (μ : EReal) ∧ ∃ x : E, HasGradientAtFn f y x := by
  rw [mem_exposedPoints_epi_convexConj_iff_of_properConvex hf hp]
  exact and_congr_right fun _ =>
    exists_congr fun _ => (hasGradientAtFn_iff_subdifferential_eq_singleton hf hp).symm

/-- Let $E$ be a finite-dimensional real normed space and let $f$ be a positively homogeneous proper
convex function on $E$. Then a continuous linear functional $z$ on $E$ is an exposed point of
the set $\{z : z(x) \le f(x) \text{ for all } x\}$ supported by $f$ if and only if there is
$y \in E$ at which $f$ has the gradient $z$.

The set is `ConvexAnalysis.supportSet (topDualPairing ℝ E).flip f`. The function $f$ need not be
closed. -/
theorem mem_exposedPoints_supportSet_iff_hasGradientAtFn (hgh : PosHomogeneous f) (hgc : ConvexFn f)
    (hgp : ProperConvex f) {z : StrongDual ℝ E} :
    z ∈ (supportSet (topDualPairing ℝ E).flip f).exposedPoints ℝ ↔
      ∃ y : E, HasGradientAtFn f z y := by
  rw [mem_exposedPoints_supportSet_iff_of_properConvex (B := topDualPairing ℝ E) hgh hgc hgp]
  exact exists_congr fun _ => (hasGradientAtFn_iff_subdifferential_eq_singleton hgc hgp).symm

end Exposed

end ConvexAnalysis
