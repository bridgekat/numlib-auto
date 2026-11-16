/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.Gradient

/-!
# The Legendre transformation

Let $E$ be a real normed space, and let $f \colon E \to [-\infty, +\infty]$ be a convex function
that is differentiable on an open set $C$. The **Legendre conjugate** of $f$ is the pair $(D, g)$,
where $D = \nabla f(C)$ is the image of the gradient mapping and
$$g(y) = \langle x, y \rangle - f(x) \qquad \text{for any } x \text{ with } \nabla f(x) = y.$$
The value $g(y)$ does not depend on the choice of $x$, because $g$ is the restriction of the Fenchel
conjugate $f^*$ to $D$ (Theorem 26.4 of [rockafellar1970convex]). In particular
$D \subseteq \operatorname{dom} f^*$.

## Main definitions

* `ConvexAnalysis.legendreDom`: the set $D$ of all gradients of $f$.

## Main results

* `ConvexAnalysis.convexConj_eq_of_hasGradientAtFn`: $f^*(\nabla f(x)) = \langle x, \nabla f(x)
  \rangle - f(x)$. This is the formula for $g$ and, at the same time, the proof that $g$ is well
  defined ([rockafellar1970convex], Theorem 26.4).
* `ConvexAnalysis.legendreDom_subset_convexDom_convexConj`: $D \subseteq \operatorname{dom} f^*$.

## Implementation notes

* There is no separate definition of $g$. The formula $y \mapsto \langle (\nabla f)^{-1}(y), y
  \rangle - f((\nabla f)^{-1}(y))$ needs a choice function, and it would then have to be proved
  equal to $f^*$ on $D$. `ConvexAnalysis.convexConj_eq_of_hasGradientAtFn` is this equality without
  the detour.
* Gradients are elements of `StrongDual ℝ E`, and the conjugate is taken for the pairing of $E$ with
  `StrongDual ℝ E`, so $\langle x, y \rangle = y(x)$.
-/

open Set Filter Topology

namespace ConvexAnalysis

section Legendre

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → EReal} {x : E}
  {y : StrongDual ℝ E}

/-- If $f \colon E \to [-\infty, +\infty]$ has a gradient at $x$, then $f(x)$ is a real number. -/
theorem HasGradientAtFn.exists_coe (h : HasGradientAtFn f y x) :
    ∃ r : ℝ, f x = ((r : ℝ) : EReal) := by
  obtain ⟨g, hfg, -⟩ := h
  exact ⟨g x, hfg.self_of_nhds⟩

/-- Let $f \colon E \to [-\infty, +\infty]$ be convex, and let $f$ have the gradient $y$ at $x$.
Then Fenchel's inequality holds with equality at $(x, y)$:
$$f(x) + f^*(y) = y(x).$$
-/
theorem HasGradientAtFn.add_convexConj_eq (hf : ConvexFn f) (h : HasGradientAtFn f y x) :
    f x + convexConj (topDualPairing ℝ E).flip f y = ((y x : ℝ) : EReal) :=
  (h.proper hf).mem_subdifferential_iff_add_convexConj_eq.1 (h.mem_subdifferential hf)

/-- Let $E$ be a real normed space, let $f \colon E \to [-\infty, +\infty]$ be convex, let $f$ have
the gradient $y \in E^*$ at $x$, and let $f(x) = r \in \mathbb{R}$. Then
$$f^*(y) = y(x) - r.$$
So the Legendre conjugate $g(y) = \langle x, y \rangle - f(x)$ at $y = \nabla f(x)$ is the
Fenchel conjugate $f^*(y)$. This is Theorem 26.4 of [rockafellar1970convex].

The conjugate is taken for the pairing of $E$ with `StrongDual ℝ E`. -/
theorem convexConj_eq_of_hasGradientAtFn (hf : ConvexFn f) (h : HasGradientAtFn f y x) {r : ℝ}
    (hr : f x = ((r : ℝ) : EReal)) :
    convexConj (topDualPairing ℝ E).flip f y = ((y x - r : ℝ) : EReal) :=
  EReal.eq_coe_sub_of_add_coe_eq_coe (by rw [add_comm, ← hr]; exact h.add_convexConj_eq hf)

/-- Let $f \colon E \to [-\infty, +\infty]$ be convex, and let $f$ have the same gradient $y$ at
$x_1$ and at $x_2$, with $f(x_1) = r_1$ and $f(x_2) = r_2$ real. Then
$y(x_1) - r_1 = y(x_2) - r_2$: both are $f^*(y)$. So the Legendre conjugate is well defined even
when $\nabla f$ is not one-to-one. -/
theorem sub_eq_sub_of_hasGradientAtFn (hf : ConvexFn f) {x₁ x₂ : E} {r₁ r₂ : ℝ}
    (h₁ : HasGradientAtFn f y x₁) (h₂ : HasGradientAtFn f y x₂)
    (hr₁ : f x₁ = ((r₁ : ℝ) : EReal)) (hr₂ : f x₂ = ((r₂ : ℝ) : EReal)) :
    y x₁ - r₁ = y x₂ - r₂ := by
  have he : ((y x₁ - r₁ : ℝ) : EReal) = ((y x₂ - r₂ : ℝ) : EReal) := by
    rw [← convexConj_eq_of_hasGradientAtFn hf h₁ hr₁, ← convexConj_eq_of_hasGradientAtFn hf h₂ hr₂]
  exact_mod_cast he

/-- The **domain of the Legendre conjugate** of $f \colon E \to [-\infty, +\infty]$: the set $D$ of
all $y \in E^*$ such that $f$ has the gradient $y$ at some $x \in E$.

Every gradient is attained at an interior point of $\operatorname{dom} f$
(`ConvexAnalysis.HasGradientAtFn.mem_interior_convexDom`), so the definition needs no condition
that $x$ be interior. -/
def legendreDom (f : E → EReal) : Set (StrongDual ℝ E) := {y | ∃ x, HasGradientAtFn f y x}

/-- A functional $y$ is in the domain of the Legendre conjugate of $f$ if and only if $f$ has the
gradient $y$ at some point. -/
theorem mem_legendreDom_iff : y ∈ legendreDom f ↔ ∃ x, HasGradientAtFn f y x := Iff.rfl

/-- If $f$ has the gradient $y$ at $x$, then $y$ is in the domain of the Legendre conjugate of $f$.
-/
theorem HasGradientAtFn.mem_legendreDom (h : HasGradientAtFn f y x) : y ∈ legendreDom f := ⟨x, h⟩

/-- Every $y$ in the domain of the Legendre conjugate of $f$ is the gradient of $f$ at some point of
the interior of $\operatorname{dom} f$. -/
theorem exists_mem_interior_convexDom_of_mem_legendreDom (hy : y ∈ legendreDom f) :
    ∃ x ∈ interior (convexDom f), HasGradientAtFn f y x := by
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx.mem_interior_convexDom, hx⟩

/-- Let $E$ be a real normed space, and let $f \colon E \to [-\infty, +\infty]$ be convex. Then
every gradient of $f$ is a point where $f^*$ is finite:
$$D \subseteq \operatorname{dom} f^*,$$
where $D$ is the domain of the Legendre conjugate (`ConvexAnalysis.legendreDom`).

The conjugate is taken for the pairing of $E$ with `StrongDual ℝ E`. -/
theorem legendreDom_subset_convexDom_convexConj (hf : ConvexFn f) :
    legendreDom f ⊆ convexDom (convexConj (topDualPairing ℝ E).flip f) := by
  rintro y ⟨x, hx⟩
  obtain ⟨r, hr⟩ := hx.exists_coe
  rw [mem_convexDom, convexConj_eq_of_hasGradientAtFn hf hx hr]
  exact EReal.coe_lt_top _

end Legendre

end ConvexAnalysis
