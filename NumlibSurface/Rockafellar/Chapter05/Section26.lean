/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.BoundaryDirDeriv
import Numlib.Analysis.Convex.Subdifferential.Cofinite
import Numlib.Analysis.Convex.Subdifferential.Preservation
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar, Section 26: The Legendre transformation

This module formalizes Section 26 of [rockafellar1970convex], on the classical Legendre
transformation and the sense in which it is the conjugacy correspondence $f \mapsto f^*$, restricted
to the functions whose subdifferential is a one-to-one mapping. A proper convex function $f$ on
$\mathbb{R}^n$ is essentially smooth if $C = \operatorname{int}(\operatorname{dom} f)$ is non-empty,
$f$ is differentiable on $C$, and $|\nabla f(x_i)| \to +\infty$ along every sequence in $C$ that
converges to a boundary point of $C$. It is essentially strictly convex if it is strictly convex on
every convex subset of $\operatorname{dom} \partial f$. For a closed proper convex $f$, the mapping
$\partial f$ is single-valued exactly when $f$ is essentially smooth (Theorem 26.1), $f$ is
essentially strictly convex exactly when $f^*$ is essentially smooth (Theorem 26.3), and
$\partial f$ is one-to-one exactly when $f$ is both (Corollary 26.3.1).

For a function $f$ that is differentiable on $C$, the Legendre conjugate of $(C, f)$ is the pair
$(D, g)$ with $D = \nabla f(C)$ and $g(x^*) = \langle (\nabla f)^{-1}(x^*), x^* \rangle - f((\nabla
f)^{-1}(x^*))$. It is well defined, and $g$ is the restriction of $f^*$ to $D$ (Theorem 26.4). For a
convex function of Legendre type the Legendre transformation is a symmetric one-to-one
correspondence, and $\nabla f^*$ is the inverse of $\nabla f$ (Theorem 26.5). Theorem 26.6 and Lemma
26.7 treat finite differentiable convex functions on $\mathbb{R}^n$. All eleven numbered results of
the section are formalized, together with its three counterexamples on $\mathbb{R}^2$ (pp. 253, 254
and 257). The proofs specialize the backbone modules
`Numlib.Analysis.Convex.Subdifferential.EssentiallySmooth`,
`Numlib.Analysis.Convex.Subdifferential.LegendreType`,
`Numlib.Analysis.Convex.Subdifferential.BoundaryDirDeriv`,
`Numlib.Analysis.Convex.Subdifferential.Cofinite` and
`Numlib.Analysis.Convex.Subdifferential.Preservation`.

## Main definitions

* Section 26 (p. 251), `Rockafellar.SingleValued`, `Rockafellar.inverseMap` and
  `Rockafellar.OneToOne`: single-valued multivalued mappings, the inverse $\rho^{-1}$ of a
  multivalued mapping $\rho$, and one-to-one mappings.
* Section 26 (p. 251), `Rockafellar.EssentiallySmoothBook`: essential smoothness, with condition (c)
  at the boundary points of $C$ as in the source.
* Lemma 26.2, `Rockafellar.EssentiallySmoothDir`: essential smoothness with condition (c) replaced
  by the directional condition (c′).
* Section 26 (p. 253), `Rockafellar.essStrictlyConvexFn`: the first counterexample, which the source
  calls essentially strictly convex, but which is not strictly convex on $\operatorname{dom} f$.
* Section 26 (p. 254), `Rockafellar.strictOnRelintFn`, with `Rockafellar.nonnegAxis` and
  `Rockafellar.openQuadrant`: the second counterexample, strictly convex on
  $\operatorname{ri}(\operatorname{dom} f)$ but not essentially strictly convex.
* Section 26 (p. 256), `Rockafellar.legendreDomain`: the domain $D = \nabla f(C)$ of the Legendre
  conjugate.
* Section 26 (p. 257), `Rockafellar.halfPlaneFn`, with `Rockafellar.parabola` and
  `Rockafellar.parabolaPoint`: the third counterexample, $\xi_1^2/4\xi_2$ on the open upper
  half-plane.

## Main results

* Theorem 26.1, `Rockafellar.theorem_26_1`, `Rockafellar.theorem_26_1_gradient`,
  `Rockafellar.theorem_26_1_empty` and `Rockafellar.theorem_26_1_domSubdifferential`: for a closed
  proper convex $f$, $\partial f$ is single-valued if and only if $f$ is essentially smooth, and
  then $\partial f(x) = \{\nabla f(x)\}$ on $\operatorname{int}(\operatorname{dom} f)$ and
  $\partial f(x) = \emptyset$ elsewhere.
* Lemma 26.2, `Rockafellar.lemma_26_2` and `Rockafellar.lemma_26_2_at`: in the definition of
  essential smoothness, condition (c) may be replaced by condition (c′).
* Section 26 (p. 253), `Rockafellar.essStrictlyConvexFn_not_strictConvexOn_convexDom`: the first
  counterexample is not strictly convex on $\operatorname{dom} f$.
* Section 26 (p. 254), `Rockafellar.strictConvexOnFn_strictOnRelintFn` and
  `Rockafellar.strictOnRelintFn_not_essentiallyStrictlyConvex`: the second counterexample is
  strictly convex on $\operatorname{ri}(\operatorname{dom} f)$ but not essentially strictly convex.
* Theorem 26.3, `Rockafellar.theorem_26_3` and `Rockafellar.theorem_26_3'`: a closed proper convex
  $f$ is essentially strictly convex if and only if $f^*$ is essentially smooth.
* Corollary 26.3.1, `Rockafellar.corollary_26_3_1`: $\partial f$ is one-to-one if and only if $f$ is
  strictly convex on $\operatorname{int}(\operatorname{dom} f)$ and essentially smooth.
* Corollary 26.3.2, `Rockafellar.corollary_26_3_2`: the infimal convolution $f_1 \square f_2$ is
  essentially smooth if $f_1$ is and $\operatorname{ri}(\operatorname{dom} f_1^*) \cap
  \operatorname{ri}(\operatorname{dom} f_2^*) \neq \emptyset$.
* Corollary 26.3.3, `Rockafellar.corollary_26_3_3`: the image $Af$ of an essentially smooth $f$
  under a linear map $A$ onto $\mathbb{R}^m$ is essentially smooth if $A^* y^* \in
  \operatorname{ri}(\operatorname{dom} f^*)$ for some $y^*$.
* Theorem 26.4, `Rockafellar.theorem_26_4_wellDefined`, `Rockafellar.theorem_26_4_eq` and
  `Rockafellar.theorem_26_4_subset_dom_conj`: the Legendre conjugate $(D, g)$ is well defined,
  $D \subseteq \operatorname{dom} f^*$, and $g$ is the restriction of $f^*$ to $D$.
* Corollary 26.4.1, `Rockafellar.corollary_26_4_1_dom`,
  `Rockafellar.corollary_26_4_1_relint_subset`, `Rockafellar.corollary_26_4_1_subset_dom`,
  `Rockafellar.corollary_26_4_1_eq` and `Rockafellar.corollary_26_4_1_strictConvexOn`: for an
  essentially smooth closed proper convex $f$, $D = \operatorname{dom} \partial f^*$,
  $\operatorname{ri}(\operatorname{dom} f^*) \subseteq D \subseteq \operatorname{dom} f^*$, and $g$
  is strictly convex on every convex subset of $D$.
* Section 26 (p. 257), `Rockafellar.legendreDomain_halfPlaneFn`,
  `Rockafellar.not_convex_legendreDomain_halfPlaneFn` and
  `Rockafellar.not_essentiallySmooth_halfPlaneFn`: for the third counterexample $D$ is the parabola
  $\xi_2^* = -(\xi_1^*)^2$, which is not convex, and condition (c) fails.
* Section 26 (p. 258), `Rockafellar.legendreType_iff`: a closed proper convex $f$ is of Legendre
  type if and only if $\partial f$ is one-to-one.
* Theorem 26.5, `Rockafellar.theorem_26_5` and the declarations
  `Rockafellar.theorem_26_5_legendreDomain` to `Rockafellar.theorem_26_5_gradient_gradient_conj`:
  $(C, f)$ is of Legendre type if and only if $(C^*, f^*)$ is, and then each is the Legendre
  conjugate of the other and $\nabla f$ is a homeomorphism from $C$ onto $C^*$ with inverse
  $\nabla f^*$.
* Theorem 26.6, `Rockafellar.theorem_26_6`, `Rockafellar.theorem_26_6_conj` and
  `Rockafellar.theorem_26_6_apply`: for a finite differentiable convex $f$ on $\mathbb{R}^n$,
  $\nabla f$ is one-to-one from $\mathbb{R}^n$ onto itself if and only if $f$ is strictly convex and
  co-finite, and then $f^*$ has the same properties and is the Legendre conjugate of $f$.
* Lemma 26.7, `Rockafellar.lemma_26_7`: a finite differentiable convex $f$ is co-finite if and only
  if $|\nabla f(x_i)| \to +\infty$ whenever $|x_i| \to +\infty$.

## Conventions

* A multivalued mapping $\rho$ from $\mathbb{R}^n$ to $\mathbb{R}^n$ is a function
  `Rn n → Set (Rn n)`.
* The gradient $\nabla f(x)$ is Mathlib's `gradient` of the real trace `fun z => (f z).toReal` of
  $f$. At a point where $f$ is differentiable it is the gradient of $f$.
* Essential smoothness is `ConvexAnalysis.EssentiallySmooth`, essential strict convexity is
  `ConvexAnalysis.EssentiallyStrictlyConvex`, strict convexity on a set is
  `ConvexAnalysis.StrictConvexOnFn`, and co-finiteness is `ConvexAnalysis.Cofinite`.
* A convex function of Legendre type $(C, f)$ is `ConvexAnalysis.LegendreType f`, with
  $C = \operatorname{int}(\operatorname{dom} f)$.
* The set $\operatorname{dom} \partial f = \{x \mid \partial f(x) \neq \emptyset\}$ is
  `ConvexAnalysis.domSubdifferential`.
* The relative interior $\operatorname{ri}$ is Mathlib's `intrinsicInterior ℝ`.
* The infimal convolution $f_1 \square f_2$ is `ConvexAnalysis.infConv f₁ f₂`.
* A point $x$ of $\mathbb{R}^2$ is written $(\xi_1, \xi_2)$. Its coordinates are `x 0` and `x 1`.

## Implementation notes

* The backbone's `ConvexAnalysis.EssentiallySmooth` quantifies condition (c) over the points outside
  $C$, while the source quantifies it over the boundary points of $C$. The two conditions agree by
  `Rockafellar.essentiallySmooth_iff_book`. Both `Rockafellar.EssentiallySmoothBook` and
  `Rockafellar.EssentiallySmoothDir` are given, because a limit-of-gradients argument produces
  condition (c), while condition (c′) is easier to check for a concrete $f$.
* There is no involution lemma for the Legendre transformation. The source states (p. 258) that the
  Legendre conjugate of the Legendre conjugate need not be the original function. Theorem 26.5 says
  when it is, and `Rockafellar.not_convex_legendreDomain_halfPlaneFn` shows that its hypothesis
  cannot be dropped.
* In Corollary 26.3.3 the hypothesis that $A$ maps $\mathbb{R}^n$ onto $\mathbb{R}^m$ is used only
  through the injectivity of $A^*$, as the proof in the source says.

## Deviations from the source

* **Section 26, essential smoothness** (reading). `Rockafellar.EssentiallySmoothBook` isolates
  the three defining conditions as a predicate on arbitrary functions.
* **Theorem 26.1**, interior formula (generalization). The subdifferential at an interior
  point of an essentially smooth convex function is its gradient singleton without closedness.
* **Lemma 26.2** (reading). Lean assumes closedness, as in the proof. It uses the limit in
  (c′) without recording monotonicity and extends the pointwise equivalence to any $x$.
* **Section 26, Legendre domain** (reading). The definition uses the domain interior and the
  total gradient of the real trace. The source starts from a differentiable function on $C$.
* **Theorem 26.4** (generalization). The source assumes that $f$ is closed and proper and that $f$
  is differentiable on a non-empty $C$. The well-definedness of $g$ and the formula $g = f^*$ on $D$
  need only convexity, and the inclusion $D \subseteq \operatorname{dom} f^*$ needs in addition only
  differentiability on $C$. See `Rockafellar.theorem_26_4_wellDefined`,
  `Rockafellar.theorem_26_4_eq` and `Rockafellar.theorem_26_4_subset_dom_conj`.
* **Corollary 26.4.1**, value formula (generalization). The equality on $D$ needs no
  closedness. See `Rockafellar.corollary_26_4_1_eq`.
* **Section 26, upper-half-plane example** (reading). The source gives a real-valued formula
  on the open upper half-plane. Lean extends it by $+\infty$ elsewhere.
* **Theorem 26.5** (reading). The source says closed convex function, and its proof needs a closed
  proper convex function. Here $f$ is assumed proper. The forward value formula and
  continuity of $\nabla f$ need no closedness. See `Rockafellar.theorem_26_5`.
* **Theorem 26.6**, value formula (generalization). The formula at $\nabla f(x)$ holds without
  bijectivity of the gradient. See `Rockafellar.theorem_26_6_apply`.

## Not formalized

* **Example of p. 253, first claim.** The claim that the function is essentially strictly convex,
  and in fact essentially smooth.
-/

open Filter Set Topology

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ} {f : Rn n → EReal}

/-! ### Multivalued mappings -/

/-- **Section 26** of [rockafellar1970convex], p. 251, definition of a single-valued mapping. A
multivalued mapping $\rho$ from $\mathbb{R}^n$ to $\mathbb{R}^n$ is **single-valued** if
$\rho(x)$ has at most one element for each $x$.

The effective domain $\{x \mid \rho(x) \neq \emptyset\}$ need not be all of $\mathbb{R}^n$. -/
def SingleValued (ρ : Rn n → Set (Rn n)) : Prop := ∀ x, (ρ x).Subsingleton

/-- **Section 26** of [rockafellar1970convex], p. 251, definition of the inverse mapping. The
**inverse** of a multivalued mapping $\rho$ is the multivalued mapping
$$\rho^{-1}(x^*) = \{x \mid x^* \in \rho(x)\}.$$
-/
def inverseMap (ρ : Rn n → Set (Rn n)) : Rn n → Set (Rn n) := fun y => {x | y ∈ ρ x}

/-- For a multivalued mapping $\rho$, $x \in \rho^{-1}(y)$ if and only if $y \in \rho(x)$. -/
@[simp] theorem mem_inverseMap {ρ : Rn n → Set (Rn n)} {x y : Rn n} :
    x ∈ inverseMap ρ y ↔ y ∈ ρ x := Iff.rfl

/-- **Section 26** of [rockafellar1970convex], p. 251, definition of a one-to-one mapping. A
multivalued mapping $\rho$ is **one-to-one** if both $\rho$ and $\rho^{-1}$ are single-valued.

Equivalently, the graph of $\rho$ contains neither two different pairs with the same first
component nor two different pairs with the same second component. -/
def OneToOne (ρ : Rn n → Set (Rn n)) : Prop := SingleValued ρ ∧ SingleValued (inverseMap ρ)

/-- For a multivalued mapping $\rho$, the inverse $\rho^{-1}$ is single-valued if and only if
$\rho(x_1)$ and $\rho(x_2)$ are disjoint for all $x_1 \neq x_2$. This is the form in which the
injectivity theorems of the backbone are stated. -/
theorem singleValued_inverseMap_iff {ρ : Rn n → Set (Rn n)} :
    SingleValued (inverseMap ρ) ↔ ∀ x₁ x₂ : Rn n, x₁ ≠ x₂ → Disjoint (ρ x₁) (ρ x₂) := by
  constructor
  · intro h x₁ x₂ hne
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    exact hne (h y hy₁ hy₂)
  · intro h y x₁ hx₁ x₂ hx₂
    by_contra hne
    exact Set.disjoint_left.1 (h x₁ x₂ hne) hx₁ hx₂

/-- A multivalued mapping $\rho$ is one-to-one if and only if each $\rho(x)$ has at most one element
and $\rho(x_1) \cap \rho(x_2) = \emptyset$ for all $x_1 \neq x_2$. This relates one-to-one
mappings to the injectivity statements of the backbone. -/
theorem oneToOne_iff {ρ : Rn n → Set (Rn n)} :
    OneToOne ρ ↔ (∀ x, (ρ x).Subsingleton) ∧ ∀ x₁ x₂ : Rn n, x₁ ≠ x₂ → Disjoint (ρ x₁) (ρ x₂) :=
  and_congr_right' singleValued_inverseMap_iff

/-!
### Essential smoothness

A proper convex function $f$ is **essentially smooth** (p. 251) if the following conditions hold for
$C = \operatorname{int}(\operatorname{dom} f)$.

* (a) $C$ is not empty.
* (b) $f$ is differentiable throughout $C$.
* (c) $|\nabla f(x_i)| \to +\infty$ whenever $x_1, x_2, \dots$ is a sequence in $C$ converging to a
  boundary point of $C$.
-/

/-- **Section 26** of [rockafellar1970convex], p. 251, definition of essential smoothness. A
function $f$ on $\mathbb{R}^n$ satisfies conditions (a), (b) and (c) if
$C = \operatorname{int}(\operatorname{dom} f)$ is non-empty, $f$ is differentiable at every
point of $C$, and for every boundary point $z$ of $C$ and every sequence $(z_i)$ in $C$ with
$z_i \to z$,
$$\|\nabla f(z_i)\| \to +\infty.$$

Condition (c) is quantified over the boundary points of $C$, as in the source. The norm
$\|\nabla f(z_i)\|$ is the operator norm of the Fréchet derivative of the real trace of $f$,
which is the Euclidean norm of the gradient. The backbone's `ConvexAnalysis.EssentiallySmooth`
is the same condition by `Rockafellar.essentiallySmooth_iff_book`.

**Reading.** The source uses essential smoothness for proper convex functions. Lean defines
the three conditions independently of properness and convexity. -/
def EssentiallySmoothBook (f : Rn n → EReal) : Prop :=
  (interior (convexDom f)).Nonempty ∧
    (∀ ⦃z : Rn n⦄, z ∈ interior (convexDom f) → DifferentiableAtFn f z) ∧
    ∀ ⦃z : Rn n⦄, z ∈ frontier (interior (convexDom f)) → ∀ zs : ℕ → Rn n,
      (∀ i, zs i ∈ interior (convexDom f)) → Tendsto zs atTop (𝓝 z) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop

/-- For a function $f$ on $\mathbb{R}^n$, `ConvexAnalysis.EssentiallySmooth f` holds if and only if
`Rockafellar.EssentiallySmoothBook f` holds. The backbone quantifies condition (c) over the
points outside $C = \operatorname{int}(\operatorname{dom} f)$, and the source over the boundary
points of $C$. Since $C$ is open, its boundary is $\operatorname{cl} C \setminus C$, and a point
outside $C$ that is the limit of a sequence in $C$ lies on the boundary. -/
theorem essentiallySmooth_iff_book : EssentiallySmooth f ↔ EssentiallySmoothBook f := by
  have hfr : frontier (interior (convexDom f))
      = closure (interior (convexDom f)) \ interior (convexDom f) :=
    isOpen_interior.frontier_eq
  constructor
  · rintro ⟨hne, hdiff, hc⟩
    refine ⟨hne, hdiff, fun z hz => ?_⟩
    rw [hfr] at hz
    exact hc hz.2
  · rintro ⟨hne, hdiff, hc⟩
    refine ⟨hne, hdiff, fun z hz zs hzs hlim => ?_⟩
    refine hc ?_ zs hzs hlim
    rw [hfr]
    exact ⟨mem_closure_of_tendsto hlim (Eventually.of_forall hzs), hz⟩

/-! ### Theorem 26.1 -/

/-- **Theorem 26.1** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$. Then $\partial f$ is a single-valued mapping if and only if $f$ is essentially
smooth.

Essential smoothness is `ConvexAnalysis.EssentiallySmooth`, which agrees with the definition of
the source by `Rockafellar.essentiallySmooth_iff_book`. -/
theorem theorem_26_1 (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f) :
    SingleValued (subdifferential (pairing n) f) ↔ EssentiallySmooth f :=
  subsingleton_subdifferential_iff_essentiallySmooth hf hp hcl

/-- **Theorem 26.1** of [rockafellar1970convex], the clause on interior points. Let $f$ be an
essentially smooth convex function on $\mathbb{R}^n$, and let
$x \in \operatorname{int}(\operatorname{dom} f)$. Then $\partial f(x)$ consists of the vector
$\nabla f(x)$ alone.

**Generalization.** The formula holds without closedness. Properness follows from convexity
and differentiability at the interior point. -/
theorem theorem_26_1_gradient (hf : ConvexFn f) (hes : EssentiallySmooth f) {x : Rn n}
    (hx : x ∈ interior (convexDom f)) :
    subdifferential (pairing n) f x = {gradient (fun w => (f w).toReal) x} := by
  have h := subdifferential_eq_singleton_of_essentiallySmooth hf hes hx
  rwa [show (InnerProductSpace.toDual ℝ (Rn n)).symm (fderiv ℝ (fun w => (f w).toReal) x)
      = gradient (fun w => (f w).toReal) x from rfl] at h

/-- **Theorem 26.1** of [rockafellar1970convex], the clause on the other points. Let $f$ be an
essentially smooth closed proper convex function on $\mathbb{R}^n$, and let $x \notin
\operatorname{int}(\operatorname{dom} f)$. Then $\partial f(x) = \emptyset$. This is the
substantial half: it makes $\partial f$ an ordinary function on
$\operatorname{int}(\operatorname{dom} f)$, with no values elsewhere. -/
theorem theorem_26_1_empty (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hes : EssentiallySmooth f) {x : Rn n} (hx : x ∉ interior (convexDom f)) :
    subdifferential (pairing n) f x = ∅ :=
  subdifferential_eq_empty_of_essentiallySmooth hf hp hcl hes hx

/-- **Theorem 26.1** of [rockafellar1970convex], both clauses on the domain of $\partial f$ as one
equation. Let $f$ be an essentially smooth closed proper convex function on $\mathbb{R}^n$. Then
$$\operatorname{dom} \partial f = \operatorname{int}(\operatorname{dom} f),$$
where $\operatorname{dom} \partial f = \{x \mid \partial f(x) \neq \emptyset\}$. -/
theorem theorem_26_1_domSubdifferential (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hes : EssentiallySmooth f) :
    domSubdifferential (pairing n) f = interior (convexDom f) :=
  domSubdifferential_eq_interior_convexDom_of_essentiallySmooth hf hp hcl hes

/-! ### Lemma 26.2 -/

/-- **Lemma 26.2** of [rockafellar1970convex], conditions (a), (b) and (c′). A function $f$ on
$\mathbb{R}^n$ satisfies these conditions if $C = \operatorname{int}(\operatorname{dom} f)$ is
non-empty, $f$ is differentiable at every point of $C$, and
$$f'(x + \lambda(a - x); a - x) \to -\infty \quad \text{as } \lambda \downarrow 0$$
for every $a \in C$ and every $x \notin C$.

The source writes $\downarrow -\infty$ in (c′), which also records that the left side is
non-decreasing in $\lambda$. This holds for every convex $f$, so only the limit appears here.
The source states (c′) for the boundary points $x$ of $C$. Here it is required at every
$x \notin C$. By `Rockafellar.lemma_26_2_at`, (c′) holds at every point outside
$\operatorname{cl} C$, where (c) holds vacuously.

**Reading.** Uses the directional-derivative limit at all exterior points. Monotonicity follows from
convexity.
-/
def EssentiallySmoothDir (f : Rn n → EReal) : Prop :=
  (interior (convexDom f)).Nonempty ∧
    (∀ ⦃z : Rn n⦄, z ∈ interior (convexDom f) → DifferentiableAtFn f z) ∧
    ∀ x ∉ interior (convexDom f), ∀ a ∈ interior (convexDom f),
      Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥)

/-- **Lemma 26.2** of [rockafellar1970convex], at a single point. Let $f$ be a closed proper convex
function on $\mathbb{R}^n$ that satisfies (a) and (b), let $a \in C =
\operatorname{int}(\operatorname{dom} f)$, and let $x \in \mathbb{R}^n$. Then condition (c) at
$x$, that $\|\nabla f(z_i)\| \to +\infty$ for every sequence $(z_i)$ in $C$ with $z_i \to x$,
holds if and only if
$$f'(x + \lambda(a - x); a - x) \to -\infty \quad \text{as } \lambda \downarrow 0.$$
Both conditions say that $f$ has no subgradient at $x$.

**Reading.** The source restricts $x$ to the boundary of $C$. Lean permits all $x$ and
assumes closedness, as in the proof. -/
theorem lemma_26_2_at (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hne : (interior (convexDom f)).Nonempty)
    (hdiff : ∀ ⦃z : Rn n⦄, z ∈ interior (convexDom f) → DifferentiableAtFn f z)
    {a : Rn n} (ha : a ∈ interior (convexDom f)) (x : Rn n) :
    (∀ zs : ℕ → Rn n, (∀ i, zs i ∈ interior (convexDom f)) → Tendsto zs atTop (𝓝 x) →
        Tendsto (fun i => ‖fderiv ℝ (fun w => (f w).toReal) (zs i)‖) atTop atTop)
      ↔ Tendsto (fun t : ℝ => dirDeriv f (x + t • (a - x)) (a - x)) (𝓝[>] 0) (𝓝 ⊥) :=
  tendsto_norm_fderiv_iff_tendsto_dirDeriv hf hp hcl hne hdiff ha x

/-- **Lemma 26.2** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$. Then $f$ is essentially smooth if and only if it satisfies conditions (a), (b)
and (c′). That is, in the definition of essential smoothness, condition (c) may be replaced by
condition (c′).

The two definitions are `ConvexAnalysis.EssentiallySmooth` and
`Rockafellar.EssentiallySmoothDir`.

**Reading.** The source starts with (a) and (b) and assumes closedness in the proof. Lean
includes (a) and (b) on both sides and assumes closedness in the statement. -/
theorem lemma_26_2 (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f) :
    EssentiallySmooth f ↔ EssentiallySmoothDir f := by
  constructor
  · intro hes
    refine ⟨hes.interior_convexDom_nonempty, hes.differentiableAtFn, ?_⟩
    exact (essentiallySmooth_iff_tendsto_dirDeriv hf hp hcl hes.interior_convexDom_nonempty
      hes.differentiableAtFn).1 hes
  · rintro ⟨hne, hdiff, hc⟩
    exact (essentiallySmooth_iff_tendsto_dirDeriv hf hp hcl hne hdiff).2 hc

/-!
### Essential strict convexity

A real-valued function is **strictly convex on $C$** (p. 253) if the convexity inequality between
two different points of $C$ is strict. A proper convex function on $\mathbb{R}^n$ is **essentially
strictly convex** if it is strictly convex on every convex subset of
$\operatorname{dom} \partial f$. These are the backbone's `ConvexAnalysis.StrictConvexOnFn` and
`ConvexAnalysis.EssentiallyStrictlyConvex`, whose definitions are those of the source. The two
warnings of the source about the definition are the counterexamples below.
-/

/-!
### Coordinates on $\mathbb{R}^2$

The three counterexamples of the section are functions on $\mathbb{R}^2$. The following facts about
coordinates are used in their proofs.
-/

private theorem sub_apply_two (u v : Rn 2) (i : Fin 2) : (u - v) i = u i - v i := rfl

/-- Two vectors of $\mathbb{R}^2$ with the same two coordinates are equal. -/
private theorem ext_two {u v : Rn 2} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- A function on $\mathbb{R}^2$ that vanishes on the non-negative $\xi_1$-axis is not strictly
convex on any set that contains $(1, 0)$ and $(2, 0)$, since $(3/2, 0)$ is their midpoint. -/
private theorem not_strictConvexOnFn_of_axis {g : Rn 2 → EReal} {C : Set (Rn 2)}
    (h1 : (WithLp.toLp 2 ![(1 : ℝ), 0] : Rn 2) ∈ C)
    (h2 : (WithLp.toLp 2 ![(2 : ℝ), 0] : Rn 2) ∈ C)
    (hg : ∀ t : ℝ, 0 ≤ t → g (WithLp.toLp 2 ![t, 0]) = 0) : ¬ StrictConvexOnFn g C := by
  intro h
  have hne : (WithLp.toLp 2 ![(1 : ℝ), 0] : Rn 2) ≠ WithLp.toLp 2 ![(2 : ℝ), 0] := by
    intro hc
    have hco : (WithLp.toLp 2 ![(1 : ℝ), 0] : Rn 2) 0 = (WithLp.toLp 2 ![(2 : ℝ), 0] : Rn 2) 0 :=
      congrArg (fun w : Rn 2 => w 0) hc
    have hnum : (1 : ℝ) = 2 := hco
    norm_num at hnum
  have hlt := h h1 h2 hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  have hmid : ((1/2 : ℝ) • (WithLp.toLp 2 ![(1 : ℝ), 0] : Rn 2)
      + (1/2 : ℝ) • (WithLp.toLp 2 ![(2 : ℝ), 0] : Rn 2)) = WithLp.toLp 2 ![(3/2 : ℝ), 0] :=
    ext_two (by change (1/2 : ℝ) * 1 + (1/2 : ℝ) * 2 = 3/2; norm_num)
      (by change (1/2 : ℝ) * 0 + (1/2 : ℝ) * 0 = 0; norm_num)
  rw [hmid, hg 1 zero_le_one, hg 2 (by norm_num), hg (3/2) (by norm_num)] at hlt
  simp at hlt

/-!
### The counterexample of p. 253

The first warning of the source: a closed proper convex function that is essentially strictly convex
need not be strictly convex on all of $\operatorname{dom} f$.
-/

/-- **Section 26** of [rockafellar1970convex], p. 253, the first counterexample. The function $f$ on
$\mathbb{R}^2$ is
$$f(\xi_1, \xi_2) = \begin{cases} \xi_2^2/2\xi_1 - 2\xi_2^{1/2} & \text{if } \xi_1 > 0,\ \xi_2
  \ge 0, \\ 0 & \text{if } \xi_1 = 0 = \xi_2, \\ +\infty & \text{otherwise.} \end{cases}$$

The source claims that $f$ is essentially strictly convex, and in fact essentially smooth, but
not strictly convex on $\operatorname{dom} f$, because it vanishes on the whole non-negative
$\xi_1$-axis. Only the second claim is formalized, as
`Rockafellar.essStrictlyConvexFn_not_strictConvexOn_convexDom`.

The first two cases are one formula: at the origin the real expression is $0/0 - 2\sqrt{0}$,
which is $0$ in Lean because division by $0$ gives $0$. -/
noncomputable def essStrictlyConvexFn (x : Rn 2) : EReal :=
  ⨅ _ : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0),
    ((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ) : EReal)

/-- On its effective domain, where $\xi_1 > 0$ and $\xi_2 \ge 0$ or $\xi_1 = \xi_2 = 0$, the example
of p. 253 takes the value $\xi_2^2/2\xi_1 - 2\sqrt{\xi_2}$. -/
theorem essStrictlyConvexFn_of_mem {x : Rn 2}
    (h : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0)) :
    essStrictlyConvexFn x = ((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ) : EReal) :=
  iInf_pos h

/-- The example of p. 253 vanishes on the non-negative $\xi_1$-axis: $f(t, 0) = 0$ for every
$t \ge 0$. This is the observation of the source. -/
theorem essStrictlyConvexFn_axis {t : ℝ} (ht : 0 ≤ t) :
    essStrictlyConvexFn (WithLp.toLp 2 ![t, 0]) = 0 := by
  have e0 : (WithLp.toLp 2 ![t, 0] : Rn 2) 0 = t := rfl
  have e1 : (WithLp.toLp 2 ![t, 0] : Rn 2) 1 = 0 := rfl
  have hc : (0 < (WithLp.toLp 2 ![t, 0] : Rn 2) 0 ∧ 0 ≤ (WithLp.toLp 2 ![t, 0] : Rn 2) 1)
      ∨ ((WithLp.toLp 2 ![t, 0] : Rn 2) 0 = 0 ∧ (WithLp.toLp 2 ![t, 0] : Rn 2) 1 = 0) := by
    rw [e0, e1]
    rcases eq_or_lt_of_le ht with he | hlt
    · exact Or.inr ⟨he.symm, rfl⟩
    · exact Or.inl ⟨hlt, le_rfl⟩
  rw [essStrictlyConvexFn_of_mem hc, e0, e1]
  norm_num

/-- The non-negative $\xi_1$-axis lies in the effective domain of the example of p. 253. -/
theorem essStrictlyConvexFn_mem_convexDom {t : ℝ} (ht : 0 ≤ t) :
    (WithLp.toLp 2 ![t, 0] : Rn 2) ∈ convexDom essStrictlyConvexFn := by
  rw [mem_convexDom, essStrictlyConvexFn_axis ht]
  exact lt_top_iff_ne_top.2 (by simp)

/-- **Section 26** of [rockafellar1970convex], p. 253. The example of p. 253 is not strictly convex
on $\operatorname{dom} f$: it vanishes on the non-negative $\xi_1$-axis, which is a convex
subset of $\operatorname{dom} f$. This separates essential strict convexity from strict
convexity on the effective domain. -/
theorem essStrictlyConvexFn_not_strictConvexOn_convexDom :
    ¬ StrictConvexOnFn essStrictlyConvexFn (convexDom essStrictlyConvexFn) :=
  not_strictConvexOnFn_of_axis (essStrictlyConvexFn_mem_convexDom zero_le_one)
    (essStrictlyConvexFn_mem_convexDom (by norm_num)) fun _ ht => essStrictlyConvexFn_axis ht

/-!
### The counterexample of p. 254

The second warning of the source: a closed proper convex function can be strictly convex on
$\operatorname{ri}(\operatorname{dom} f)$ and still fail to be essentially strictly convex. The
reason is that $\operatorname{dom} \partial f$ can be larger than
$\operatorname{ri}(\operatorname{dom} f)$ and can contain a convex set on which $f$ is constant.
-/

/-- **Section 26** of [rockafellar1970convex], p. 254, the second counterexample. The function $f$
on $\mathbb{R}^2$ is
$$f(\xi_1, \xi_2) = \begin{cases} \xi_2^2/2\xi_1 + \xi_2^2 & \text{if } \xi_1 > 0,\ \xi_2 \ge 0,
  \\ 0 & \text{if } \xi_1 = 0 = \xi_2, \\ +\infty & \text{otherwise.} \end{cases}$$

The source claims that $\operatorname{ri}(\operatorname{dom} f)$ is the open positive quadrant,
on which $f$ is strictly convex, while $\operatorname{dom} \partial f$ also contains the whole
non-negative $\xi_1$-axis, on which $f$ is constant. So $f$ is not essentially strictly convex.
Both claims are proved, as `Rockafellar.strictConvexOnFn_strictOnRelintFn` and
`Rockafellar.strictOnRelintFn_not_essentiallyStrictlyConvex`.

As for `Rockafellar.essStrictlyConvexFn`, the first two cases are one formula, because $0/0 = 0$
in Lean. -/
noncomputable def strictOnRelintFn (x : Rn 2) : EReal :=
  ⨅ _ : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0),
    ((x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 : ℝ) : EReal)

/-- On its effective domain the example of p. 254 takes the value $\xi_2^2/2\xi_1 + \xi_2^2$. -/
theorem strictOnRelintFn_of_mem {x : Rn 2}
    (h : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0)) :
    strictOnRelintFn x = ((x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 : ℝ) : EReal) :=
  iInf_pos h

/-- Outside its effective domain the example of p. 254 takes the value $+\infty$. -/
theorem strictOnRelintFn_of_not_mem {x : Rn 2}
    (h : ¬ ((0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0))) : strictOnRelintFn x = ⊤ :=
  iInf_neg h

/-- The example of p. 254 is non-negative everywhere. So $0$ is a subgradient at every point where
it vanishes. -/
theorem strictOnRelintFn_nonneg (x : Rn 2) : 0 ≤ strictOnRelintFn x := by
  by_cases h : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0)
  · rw [strictOnRelintFn_of_mem h]
    have hr : (0 : ℝ) ≤ x 1 ^ 2 / (2 * x 0) + x 1 ^ 2 := by
      rcases h with ⟨h0, -⟩ | ⟨-, h1⟩
      · have hq : (0 : ℝ) ≤ x 1 ^ 2 / (2 * x 0) := div_nonneg (sq_nonneg _) (by linarith)
        nlinarith [sq_nonneg (x 1)]
      · rw [h1]
        norm_num
    exact_mod_cast hr
  · rw [strictOnRelintFn_of_not_mem h]
    exact le_top

/-- The non-negative $\xi_1$-axis $\{(\xi_1, \xi_2) \in \mathbb{R}^2 \mid \xi_1 \ge 0,\ \xi_2 =
0\}$, the convex set on which the example of p. 254 is constant. -/
def nonnegAxis : Set (Rn 2) := {x : Rn 2 | 0 ≤ x 0 ∧ x 1 = 0}

/-- The non-negative $\xi_1$-axis is convex, so it is admissible in the definition of essential
strict convexity. -/
theorem convex_nonnegAxis : Convex ℝ nonnegAxis := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  constructor
  · change 0 ≤ a * x 0 + b * y 0
    nlinarith
  · change a * x 1 + b * y 1 = 0
    rw [hx1, hy1]
    ring

/-- The example of p. 254 vanishes on the non-negative $\xi_1$-axis. -/
theorem strictOnRelintFn_eq_zero_of_mem {x : Rn 2} (hx : x ∈ nonnegAxis) :
    strictOnRelintFn x = 0 := by
  obtain ⟨h0, h1⟩ := hx
  have hc : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0) := by
    rcases eq_or_lt_of_le h0 with he | hlt
    · exact Or.inr ⟨he.symm, h1⟩
    · exact Or.inl ⟨hlt, le_of_eq h1.symm⟩
  rw [strictOnRelintFn_of_mem hc, h1]
  norm_num

/-- For the example of p. 254, $0$ is a subgradient at every point of the non-negative $\xi_1$-axis,
because the function is non-negative and vanishes on the axis. So the whole axis lies in
$\operatorname{dom} \partial f$. This is the observation of the source that
$\operatorname{dom} \partial f$ is larger than $\operatorname{ri}(\operatorname{dom} f)$ here. -/
theorem zero_mem_subdifferential_strictOnRelintFn {x : Rn 2} (hx : x ∈ nonnegAxis) :
    (0 : Rn 2) ∈ subdifferential (pairing 2) strictOnRelintFn x := by
  intro z
  have h0 : ((pairing 2 (z - x)) (0 : Rn 2) : ℝ) = 0 := map_zero _
  rw [strictOnRelintFn_eq_zero_of_mem hx, h0]
  simpa using strictOnRelintFn_nonneg z

/-- The example of p. 254 vanishes at $(t, 0)$ for every $t \ge 0$. -/
theorem strictOnRelintFn_axis {t : ℝ} (ht : 0 ≤ t) :
    strictOnRelintFn (WithLp.toLp 2 ![t, 0]) = 0 :=
  strictOnRelintFn_eq_zero_of_mem ⟨ht, rfl⟩

/-- **Section 26** of [rockafellar1970convex], p. 254. The example of p. 254 is not essentially
strictly convex: the non-negative $\xi_1$-axis is a convex subset of
$\operatorname{dom} \partial f$ on which the function is constant. -/
theorem strictOnRelintFn_not_essentiallyStrictlyConvex :
    ¬ EssentiallyStrictlyConvex (B := pairing 2) strictOnRelintFn := by
  intro h
  have hsub : nonnegAxis ⊆ domSubdifferential (pairing 2) strictOnRelintFn :=
    fun _ hx => ⟨0, zero_mem_subdifferential_strictOnRelintFn hx⟩
  refine not_strictConvexOnFn_of_axis (C := nonnegAxis) ⟨zero_le_one, rfl⟩
    ⟨by norm_num, rfl⟩ (fun _ ht => strictOnRelintFn_axis ht) ?_
  exact h convex_nonnegAxis hsub

/-!
### The example of p. 254 is strictly convex on $\operatorname{ri}(\operatorname{dom} f)$

This is the other half of the claim of the source, and it is what makes the example separate the two
conditions. Here $\operatorname{ri}(\operatorname{dom} f)$ is the open positive quadrant. Strict
convexity there follows from the weighted Cauchy–Schwarz inequality
$(au + bv)^2/(as + bt) \le au^2/s + bv^2/t$ together with $(au + bv)^2 \le au^2 + bv^2$ for
$a + b = 1$. At any two distinct points of the quadrant one of the two inequalities is strict.
-/

/-- The open positive quadrant $\{(\xi_1, \xi_2) \in \mathbb{R}^2 \mid \xi_1 > 0,\ \xi_2 > 0\}$,
which is $\operatorname{ri}(\operatorname{dom} f)$ for the example of p. 254. -/
def openQuadrant : Set (Rn 2) := {x : Rn 2 | 0 < x 0 ∧ 0 < x 1}

/-- The open positive quadrant is an open subset of $\mathbb{R}^2$. -/
theorem isOpen_openQuadrant : IsOpen openQuadrant :=
  (isOpen_lt continuous_const (continuous_coord 0)).inter
    (isOpen_lt continuous_const (continuous_coord 1))

/-- The effective domain of the example of p. 254 is $\{(\xi_1, \xi_2) \mid \xi_1 > 0,\ \xi_2 \ge
0\} \cup \{(0, 0)\}$. -/
theorem convexDom_strictOnRelintFn :
    convexDom strictOnRelintFn = {x : Rn 2 | (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0)} := by
  ext x
  by_cases h : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0)
  · simp only [mem_convexDom, strictOnRelintFn_of_mem h, Set.mem_ofPred_eq]
    exact ⟨fun _ => h, fun _ => EReal.coe_lt_top _⟩
  · simp only [mem_convexDom, strictOnRelintFn_of_not_mem h, Set.mem_ofPred_eq, lt_self_iff_false]
    exact ⟨fun hc => absurd hc not_false, fun hc => absurd hc h⟩

private theorem openQuadrant_subset_convexDom : openQuadrant ⊆ convexDom strictOnRelintFn := by
  rintro x ⟨h0, h1⟩
  rw [convexDom_strictOnRelintFn]
  exact Or.inl ⟨h0, h1.le⟩

/-- For the example of p. 254, $\operatorname{ri}(\operatorname{dom} f)$ is the open positive
quadrant. The domain has non-empty interior, so its relative interior is its interior. The
interior is the quadrant, because every point of the domain with $\xi_2 = 0$ has points with
$\xi_2 < 0$ arbitrarily close to it. -/
theorem relint_convexDom_strictOnRelintFn : ri (convexDom strictOnRelintFn) = openQuadrant := by
  have hpt : (WithLp.toLp 2 ![(1 : ℝ), 1] : Rn 2) ∈ openQuadrant := ⟨one_pos, one_pos⟩
  have htop : affineSpan ℝ (convexDom strictOnRelintFn) = ⊤ :=
    top_unique <| (isOpen_openQuadrant.affineSpan_eq_top ⟨_, hpt⟩).ge.trans
      (affineSpan_mono ℝ openQuadrant_subset_convexDom)
  rw [intrinsicInterior_eq_interior htop]
  refine Set.Subset.antisymm (fun x hx => ?_)
    (interior_maximal openQuadrant_subset_convexDom isOpen_openQuadrant)
  have hnn : ∀ y : Rn 2, y ∈ convexDom strictOnRelintFn → 0 ≤ y 1 := by
    intro y hy
    rw [convexDom_strictOnRelintFn] at hy
    rcases hy with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact h.ge
  have hnorm : ‖(WithLp.toLp 2 ![(0 : ℝ), 1] : Rn 2)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hd : dist (x + (-(ε / 2)) • (WithLp.toLp 2 ![(0 : ℝ), 1] : Rn 2)) x = ε / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
      abs_of_nonpos (by linarith), neg_neg]
  have hmem := hball (by rw [Metric.mem_ball, hd]; linarith)
  have hcoord : (x + (-(ε / 2)) • (WithLp.toLp 2 ![(0 : ℝ), 1] : Rn 2)) 1 = x 1 - ε / 2 := by
    change x 1 + -(ε / 2) * (1 : ℝ) = x 1 - ε / 2
    ring
  have hle := hnn _ (interior_subset hmem)
  rw [hcoord] at hle
  have hx1 : 0 < x 1 := by linarith
  have hxD := interior_subset hx
  rw [convexDom_strictOnRelintFn] at hxD
  rcases hxD with ⟨h0, -⟩ | ⟨-, h1⟩
  · exact ⟨h0, hx1⟩
  · exact absurd h1 hx1.ne'

/-- The weighted Cauchy–Schwarz identity: for $s, t, a, b > 0$, the gap in
$(au + bv)^2/(as + bt) \le au^2/s + bv^2/t$ is $ab(ut - vs)^2/(st(as + bt))$. -/
private theorem engel_key {s t u v a b : ℝ} (hs : 0 < s) (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) :
    a * (u ^ 2 / s) + b * (v ^ 2 / t) - (a * u + b * v) ^ 2 / (a * s + b * t)
      = a * b * (u * t - v * s) ^ 2 / (s * t * (a * s + b * t)) := by
  have hw : 0 < a * s + b * t := by positivity
  field_simp
  ring

private theorem engel_le {s t u v a b : ℝ} (hs : 0 < s) (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) :
    (a * u + b * v) ^ 2 / (a * s + b * t) ≤ a * (u ^ 2 / s) + b * (v ^ 2 / t) := by
  have hkey := engel_key (u := u) (v := v) hs ht ha hb
  have hnn : 0 ≤ a * b * (u * t - v * s) ^ 2 / (s * t * (a * s + b * t)) := by positivity
  linarith

private theorem engel_lt {s t u v a b : ℝ} (hs : 0 < s) (ht : 0 < t) (ha : 0 < a) (hb : 0 < b)
    (hne : u * t ≠ v * s) :
    (a * u + b * v) ^ 2 / (a * s + b * t) < a * (u ^ 2 / s) + b * (v ^ 2 / t) := by
  have hkey := engel_key (u := u) (v := v) hs ht ha hb
  have hsq : 0 < (u * t - v * s) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hne)))
  have hw : 0 < s * t * (a * s + b * t) := by positivity
  have hpos : 0 < a * b * (u * t - v * s) ^ 2 / (s * t * (a * s + b * t)) :=
    div_pos (by positivity) hw
  linarith

/-- For $a + b = 1$, the gap in $(au + bv)^2 \le au^2 + bv^2$ is $ab(u - v)^2$. -/
private theorem sq_combo_key {u v a b : ℝ} (hab : a + b = 1) :
    a * u ^ 2 + b * v ^ 2 - (a * u + b * v) ^ 2 = a * b * (u - v) ^ 2 := by
  linear_combination (-(a * u ^ 2 + b * v ^ 2)) * hab

/-- **Section 26** of [rockafellar1970convex], p. 254, the positive half. The example of p. 254 is
strictly convex on $\operatorname{ri}(\operatorname{dom} f)$, the open positive quadrant. With
`Rockafellar.strictOnRelintFn_not_essentiallyStrictlyConvex`, this is the point of the example.

Neither summand of $\xi_2^2/2\xi_1 + \xi_2^2$ is strictly convex on the quadrant: the first is
positively homogeneous, hence affine along every ray from the origin, and the second does not
depend on $\xi_1$. So no sum rule applies. The sum is strictly convex because the two summands
are affine along different directions. -/
theorem strictConvexOnFn_strictOnRelintFn :
    StrictConvexOnFn strictOnRelintFn (ri (convexDom strictOnRelintFn)) := by
  rw [relint_convexDom_strictOnRelintFn]
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ hxy a b ha hb hab
  have hzc0 : (a • x + b • y : Rn 2) 0 = a * x 0 + b * y 0 := rfl
  have hzc1 : (a • x + b • y : Rn 2) 1 = a * x 1 + b * y 1 := rfl
  have hz0 : 0 < a * x 0 + b * y 0 := by positivity
  have hz1 : 0 < a * x 1 + b * y 1 := by positivity
  have hxm : (0 < x 0 ∧ 0 ≤ x 1) ∨ (x 0 = 0 ∧ x 1 = 0) := Or.inl ⟨hx0, hx1.le⟩
  have hym : (0 < y 0 ∧ 0 ≤ y 1) ∨ (y 0 = 0 ∧ y 1 = 0) := Or.inl ⟨hy0, hy1.le⟩
  have hzm : (0 < (a • x + b • y : Rn 2) 0 ∧ 0 ≤ (a • x + b • y : Rn 2) 1)
      ∨ ((a • x + b • y : Rn 2) 0 = 0 ∧ (a • x + b • y : Rn 2) 1 = 0) :=
    Or.inl ⟨by rw [hzc0]; exact hz0, by rw [hzc1]; exact hz1.le⟩
  rw [strictOnRelintFn_of_mem hxm, strictOnRelintFn_of_mem hym, strictOnRelintFn_of_mem hzm,
    hzc0, hzc1, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
    EReal.coe_lt_coe_iff]
  have hden : a * (2 * x 0) + b * (2 * y 0) = 2 * (a * x 0 + b * y 0) := by ring
  have hexp : a * (x 1 ^ 2 / (2 * x 0) + x 1 ^ 2) + b * (y 1 ^ 2 / (2 * y 0) + y 1 ^ 2)
      = (a * (x 1 ^ 2 / (2 * x 0)) + b * (y 1 ^ 2 / (2 * y 0)))
        + (a * x 1 ^ 2 + b * y 1 ^ 2) := by ring
  have hx0' : (0 : ℝ) < 2 * x 0 := by linarith
  have hy0' : (0 : ℝ) < 2 * y 0 := by linarith
  have hsq := sq_combo_key (u := x 1) (v := y 1) hab
  rw [hexp]
  rcases eq_or_ne (x 1) (y 1) with h1 | h1
  · have hx0y0 : x 0 ≠ y 0 := fun h => hxy (ext_two h h1)
    have hne : x 1 * (2 * y 0) ≠ y 1 * (2 * x 0) := by
      rw [h1]
      intro hcon
      exact hx0y0 (by linarith [mul_left_cancel₀ hy1.ne' hcon, h1])
    have hA := engel_lt (u := x 1) (v := y 1) hx0' hy0' ha hb hne
    rw [hden] at hA
    have hB : (a * x 1 + b * y 1) ^ 2 ≤ a * x 1 ^ 2 + b * y 1 ^ 2 := by
      nlinarith [sq_nonneg (x 1 - y 1), mul_pos ha hb]
    linarith
  · have hA := engel_le (u := x 1) (v := y 1) hx0' hy0' ha hb
    rw [hden] at hA
    have hB : (a * x 1 + b * y 1) ^ 2 < a * x 1 ^ 2 + b * y 1 ^ 2 := by
      have hsq0 : 0 < (x 1 - y 1) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 h1)))
      nlinarith [mul_pos ha hb]
    linarith

/-! ### Theorem 26.3 -/

/-- **Theorem 26.3** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$. Then $f$ is essentially strictly convex if and only if its conjugate $f^*$ is
essentially smooth.

Essential strict convexity is `ConvexAnalysis.EssentiallyStrictlyConvex` for the pairing
`Rockafellar.pairing n`. -/
theorem theorem_26_3 (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f) :
    EssentiallyStrictlyConvex (B := pairing n) f ↔ EssentiallySmooth (convexConj (pairing n) f) :=
  (essentiallySmooth_convexConj_iff_essentiallyStrictlyConvex hf hp hcl).symm

/-- **Theorem 26.3** of [rockafellar1970convex], with the roles of $f$ and $f^*$ exchanged. Let $f$
be a closed proper convex function on $\mathbb{R}^n$. Then $f^*$ is essentially strictly convex
if and only if $f$ is essentially smooth.

Corollaries 26.3.2 and 26.3.3 use this form. -/
theorem theorem_26_3' (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f) :
    EssentiallyStrictlyConvex (B := pairing n) (convexConj (pairing n) f) ↔ EssentiallySmooth f :=
  essentiallyStrictlyConvex_convexConj_iff_essentiallySmooth hf hp hcl

/-! ### Corollary 26.3.1 -/

/-- **Corollary 26.3.1** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$. Then $\partial f$ is a one-to-one mapping if and only if $f$ is strictly convex
on $\operatorname{int}(\operatorname{dom} f)$ and essentially smooth. -/
theorem corollary_26_3_1 (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f) :
    OneToOne (subdifferential (pairing n) f) ↔
      (StrictConvexOnFn f (interior (convexDom f)) ∧ EssentiallySmooth f) :=
  oneToOne_iff.trans ((subdifferential_injective_iff hf hp hcl).trans and_comm)

/-! ### Corollaries 26.3.2 and 26.3.3: preservation of essential smoothness -/

/-- **Corollary 26.3.2** of [rockafellar1970convex]. Let $f_1$ and $f_2$ be closed proper convex
functions on $\mathbb{R}^n$ such that $f_1$ is essentially smooth and
$$\operatorname{ri}(\operatorname{dom} f_1^*) \cap \operatorname{ri}(\operatorname{dom} f_2^*)
  \neq \emptyset.$$
Then the infimal convolution $f_1 \square f_2$ is essentially smooth.

The infimal convolution is `ConvexAnalysis.infConv f₁ f₂`. -/
theorem corollary_26_3_2 {f₁ f₂ : Rn n → EReal} (h₁ : ClosedProperConvexFn f₁)
    (h₂ : ClosedProperConvexFn f₂) (hes : EssentiallySmooth f₁)
    (hri :
        (ri (convexDom (convexConj (pairing n) f₁)) ∩
            ri (convexDom (convexConj (pairing n) f₂))).Nonempty) :
    EssentiallySmooth (infConv f₁ f₂) := by
  obtain ⟨y₀, hy₁, hy₂⟩ := hri
  exact essentiallySmooth_infConv_of_relint h₁ h₂ hes hy₁ hy₂

/-- **Corollary 26.3.3** of [rockafellar1970convex]. Let $g$ be an essentially smooth closed proper
convex function on $\mathbb{R}^n$, and let $A$ be a linear transformation from $\mathbb{R}^n$
onto $\mathbb{R}^m$. Suppose that there is a $y^* \in \mathbb{R}^m$ with $A^* y^* \in
\operatorname{ri}(\operatorname{dom} g^*)$. Then the convex function $Ag$ on $\mathbb{R}^m$,
$$(Ag)(y) = \inf\{g(x) \mid Ax = y\},$$
is essentially smooth.

The source calls the function $f$. The adjoint $A^*$ is `LinearMap.adjoint A`, and $Ag$ is
`ConvexAnalysis.mapLin A g`. The surjectivity of $A$ is used only to make $A^*$ injective, as
the proof in the source says. -/
theorem corollary_26_3_3 {m : ℕ} {g : Rn n → EReal} (hg : ClosedProperConvexFn g)
    (hes : EssentiallySmooth g) (A : Rn n →ₗ[ℝ] Rn m) (hsurj : Function.Surjective A) {y : Rn m}
    (hy : LinearMap.adjoint A y ∈ ri (convexDom (convexConj (pairing n) g))) :
    EssentiallySmooth (mapLin A g) := by
  have hA : IsAdjointPair (innerₗ (Rn m)) (innerₗ (Rn n)) (LinearMap.adjoint A) A := by
    have h := isAdjointPair_adjoint (LinearMap.adjoint A)
    rwa [LinearMap.adjoint_adjoint] at h
  exact essentiallySmooth_mapLin_of_relint hA hg hes hsurj hy

/-!
### The Legendre conjugate

For a differentiable real-valued function $f$ on an open set $C \subseteq \mathbb{R}^n$, the
**Legendre conjugate** of $(C, f)$ (p. 256) is the pair $(D, g)$ with $D = \nabla f(C)$ and
$$g(x^*) = \langle (\nabla f)^{-1}(x^*), x^* \rangle - f((\nabla f)^{-1}(x^*)).$$
The mapping $\nabla f$ need not be one-to-one for $g$ to be well defined. It suffices that
$\langle x, x^* \rangle - f(x)$ has the same value for every $x$ with $\nabla f(x) = x^*$, which is
the first clause of Theorem 26.4.
-/

/-- **Section 26** of [rockafellar1970convex], p. 256, the domain of the Legendre conjugate. For a
function $f$ on $\mathbb{R}^n$, the set $D$ is the image of
$C = \operatorname{int}(\operatorname{dom} f)$ under the gradient mapping:
$$D = \{\nabla f(x) \mid x \in C\}.$$

The gradient is Mathlib's `gradient` of the real trace `fun z => (f z).toReal`. Where $f$ is
differentiable, it is the gradient of $f$.

**Reading.** The source starts with a differentiable real-valued function on an open set $C$.
Lean uses $C = \operatorname{int}(\operatorname{dom} f)$ and defines the image even without
differentiability on $C$. -/
noncomputable def legendreDomain (f : Rn n → EReal) : Set (Rn n) :=
  gradient (fun w => (f w).toReal) '' interior (convexDom f)

/-- Suppose that $f$ is differentiable at every point of
$C = \operatorname{int}(\operatorname{dom} f)$, which is condition (b). Then $D$ is the
backbone's `ConvexAnalysis.gradientRange f`, the set of all gradients $\nabla f(x)$ at points
$x$ where $f$ is differentiable. The reason is that every gradient is attained at a point of $C$
(Corollary 25.1.1), and on $C$ Mathlib's `gradient` of the real trace is the gradient of $f$. -/
theorem legendreDomain_eq_gradientRange
    (hdiff : ∀ ⦃z : Rn n⦄, z ∈ interior (convexDom f) → DifferentiableAtFn f z) :
    legendreDomain f = gradientRange f := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hdiff hz).hasGradientAtFn_gradient.mem_gradientRange
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.mem_interior_convexDom, by
      rw [hz.gradient_toReal_eq, LinearIsometryEquiv.symm_apply_apply]⟩

/-! ### Theorem 26.4 -/

/-- **Theorem 26.4** of [rockafellar1970convex], first clause. Let $f$ be a convex function on
$\mathbb{R}^n$, and let $x_1, x_2, v \in \mathbb{R}^n$ with $\nabla f(x_1) = v$ and
$\nabla f(x_2) = v$. Then
$$\langle x_1, v \rangle - f(x_1) = \langle x_2, v \rangle - f(x_2).$$
So the Legendre conjugate $(D, g)$ of $(C, f)$ is well defined: the value
$\langle x, x^* \rangle - f(x)$ does not depend on the choice of $x$ in $(\nabla f)^{-1}(x^*)$.

**Generalization.** The source states the theorem for a closed proper convex $f$ such that
$C = \operatorname{int}(\operatorname{dom} f)$ is non-empty and $f$ is differentiable on $C$.
Only convexity is needed: the clause follows from Theorem 23.5 at each of the two points.

The gradient condition is `ConvexAnalysis.HasGradientAtFn` for the functional
`InnerProductSpace.toDual ℝ (Rn n) v`, and $f(x_i)$ is the real number `(f xᵢ).toReal`. -/
theorem theorem_26_4_wellDefined (hf : ConvexFn f) {v x₁ x₂ : Rn n}
    (h₁ : HasGradientAtFn f (InnerProductSpace.toDual ℝ (Rn n) v) x₁)
    (h₂ : HasGradientAtFn f (InnerProductSpace.toDual ℝ (Rn n) v) x₂) :
    pairing n x₁ v - (f x₁).toReal = pairing n x₂ v - (f x₂).toReal := by
  obtain ⟨r₁, hr₁⟩ := h₁.exists_coe
  obtain ⟨r₂, hr₂⟩ := h₂.exists_coe
  have h := sub_eq_sub_of_hasGradientAtFn hf h₁ h₂ hr₁ hr₂
  rw [toDual_apply_eq_pairing, toDual_apply_eq_pairing] at h
  rw [hr₁, hr₂]
  simpa using h

/-- **Theorem 26.4** of [rockafellar1970convex], second and third clauses. Let $f$ be a convex
function on $\mathbb{R}^n$ with $\nabla f(x) = v$. Then
$$f^*(v) = \langle x, v \rangle - f(x).$$
So $D \subseteq \operatorname{dom} f^*$, and $g$ is the restriction of $f^*$ to $D$.

**Generalization.** The source assumes that $f$ is closed and proper and that $f$ is
differentiable on a non-empty $C$. Only convexity of $f$ is needed. -/
theorem theorem_26_4_eq (hf : ConvexFn f) {v x : Rn n}
    (h : HasGradientAtFn f (InnerProductSpace.toDual ℝ (Rn n) v) x) :
    convexConj (pairing n) f v = ((pairing n x v - (f x).toReal : ℝ) : EReal) := by
  obtain ⟨r, hr⟩ := h.exists_coe
  have hval := convexConj_eq_of_hasGradientAtFn hf h hr
  rw [convexConj_innerL_eq_convexConj_topDualPairing, hval, toDual_apply_eq_pairing, hr]
  simp

/-- **Theorem 26.4** of [rockafellar1970convex], the inclusion $D \subseteq \operatorname{dom} f^*$.
Let $f$ be a convex function on $\mathbb{R}^n$ that is differentiable at every point of
$\operatorname{int}(\operatorname{dom} f)$. Then $D \subseteq \operatorname{dom} f^*$.

**Generalization.** The source assumes that $f$ is closed and proper and that
$C = \operatorname{int}(\operatorname{dom} f)$ is non-empty. Only convexity and
differentiability on $C$ are used. -/
theorem theorem_26_4_subset_dom_conj (hf : ConvexFn f)
    (hdiff : ∀ ⦃z : Rn n⦄, z ∈ interior (convexDom f) → DifferentiableAtFn f z) :
    legendreDomain f ⊆ convexDom (convexConj (pairing n) f) := by
  rw [legendreDomain_eq_gradientRange hdiff]
  rintro v ⟨x, hx⟩
  rw [mem_convexDom, theorem_26_4_eq hf hx]
  exact EReal.coe_lt_top _

/-! ### Corollary 26.4.1 -/

/-- **Corollary 26.4.1** of [rockafellar1970convex], first clause. Let $f$ be an essentially smooth
closed proper convex function on $\mathbb{R}^n$. Then the domain $D$ of the Legendre conjugate
of $f$ is
$$D = \{x^* \mid \partial f^*(x^*) \neq \emptyset\} = \operatorname{dom} \partial f^*.$$
-/
theorem corollary_26_4_1_dom (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hes : EssentiallySmooth f) :
    legendreDomain f = domSubdifferential (pairing n) (convexConj (pairing n) f) := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn]
  exact gradientRange_eq_domSubdifferential_convexConj hf hp hcl hes

/-- **Corollary 26.4.1** of [rockafellar1970convex], the lower inclusion. Let $f$ be an essentially
smooth closed proper convex function on $\mathbb{R}^n$. Then
$\operatorname{ri}(\operatorname{dom} f^*) \subseteq D$.

With `Rockafellar.corollary_26_4_1_subset_dom`, this shows that $D$ is almost convex. -/
theorem corollary_26_4_1_relint_subset (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hes : EssentiallySmooth f) : ri (convexDom (convexConj (pairing n) f)) ⊆ legendreDomain f := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn]
  exact relint_convexDom_convexConj_subset_gradientRange hf hp hcl hes

/-- **Corollary 26.4.1** of [rockafellar1970convex], the upper inclusion. Let $f$ be an essentially
smooth closed proper convex function on $\mathbb{R}^n$. Then
$D \subseteq \operatorname{dom} f^*$. -/
theorem corollary_26_4_1_subset_dom (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hes : EssentiallySmooth f) : legendreDomain f ⊆ convexDom (convexConj (pairing n) f) := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn]
  exact gradientRange_subset_convexDom_convexConj hf hp hcl hes

/-- **Corollary 26.4.1** of [rockafellar1970convex], the formula for $g$. Let $f$ be an essentially
smooth convex function on $\mathbb{R}^n$, and let
$x \in \operatorname{int}(\operatorname{dom} f)$. Then
$$f^*(\nabla f(x)) = \langle x, \nabla f(x) \rangle - f(x),$$
so $g$ is the restriction of $f^*$ to $D$.

**Generalization.** The formula holds without closedness. Properness follows from convexity
and differentiability at $x$. -/
theorem corollary_26_4_1_eq (hf : ConvexFn f) (hes : EssentiallySmooth f) {x : Rn n}
    (hx : x ∈ interior (convexDom f)) :
    convexConj (pairing n) f (gradient (fun w => (f w).toReal) x)
      = ((pairing n x (gradient (fun w => (f w).toReal) x) - (f x).toReal : ℝ) : EReal) :=
  theorem_26_4_eq hf (hes.differentiableAtFn hx).hasGradientAtFn_gradient

/-- **Corollary 26.4.1** of [rockafellar1970convex], last clause. Let $f$ be an essentially smooth
closed proper convex function on $\mathbb{R}^n$, and let $C$ be a convex subset of $D$. Then
$f^*$ is strictly convex on $C$. Since $g = f^*$ on $D$, it follows that $g$ is strictly convex
on every convex subset of $D$.

This is the essential strict convexity of $f^*$, which Theorem 26.3 gives from the essential
smoothness of $f$. -/
theorem corollary_26_4_1_strictConvexOn (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hes : EssentiallySmooth f) {C : Set (Rn n)} (hC : Convex ℝ C) (hCsub : C ⊆ legendreDomain f) :
    StrictConvexOnFn (convexConj (pairing n) f) C := by
  rw [legendreDomain_eq_gradientRange hes.differentiableAtFn] at hCsub
  exact strictConvexOnFn_convexConj_of_subset_gradientRange hf hp hcl hes hC hCsub

/-!
### The counterexample of p. 257: the parabola

On p. 257 the source shows that, for a differentiable convex function on a non-empty open convex set
$C$ that fails condition (c), the domain $D$ of the Legendre conjugate need not be almost convex.
The example is $f(\xi_1, \xi_2) = \xi_1^2/4\xi_2$ on the open upper half-plane, for which $D$ is the
parabola $\xi_2^* = -(\xi_1^*)^2$. Without condition (c) the inclusions
$\operatorname{ri}(\operatorname{dom} f^*) \subseteq D \subseteq \operatorname{dom} f^*$ of
Corollary 26.4.1 fail, and $D$ need not even be convex.
-/

/-- The point $(a, -a^2)$ of $\mathbb{R}^2$, a point of the parabola of p. 257. -/
noncomputable def parabolaPoint (a : ℝ) : Rn 2 := WithLp.toLp 2 ![a, -a ^ 2]

/-- The first coordinate of the point $(a, -a^2)$ is $a$. -/
@[simp] theorem parabolaPoint_zero (a : ℝ) : parabolaPoint a 0 = a := rfl

/-- The second coordinate of the point $(a, -a^2)$ is $-a^2$. -/
@[simp] theorem parabolaPoint_one (a : ℝ) : parabolaPoint a 1 = -a ^ 2 := rfl

/-- For $a = 0$ the point $(a, -a^2)$ is the origin. -/
theorem parabolaPoint_zero_eq : parabolaPoint 0 = 0 :=
  ext_two (by norm_num) (by norm_num)

/-- **Section 26** of [rockafellar1970convex], p. 257. The parabola
$$P = \{(\xi_1^*, \xi_2^*) \in \mathbb{R}^2 \mid \xi_2^* = -(\xi_1^*)^2\}.$$
-/
def parabola : Set (Rn 2) := {w : Rn 2 | w 1 = -(w 0) ^ 2}

/-- A point $(\xi_1^*, \xi_2^*)$ lies on the parabola $P$ if and only if $\xi_2^* = -(\xi_1^*)^2$.
-/
theorem mem_parabola {w : Rn 2} : w ∈ parabola ↔ w 1 = -(w 0) ^ 2 := Iff.rfl

/-- **Section 26** of [rockafellar1970convex], p. 257, the third counterexample. The function $f$ on
$\mathbb{R}^2$ is
$$f(\xi_1, \xi_2) = \begin{cases} \xi_1^2/4\xi_2 & \text{if } \xi_2 > 0, \\ +\infty &
  \text{otherwise,} \end{cases}$$
so that $C = \operatorname{int}(\operatorname{dom} f)$ is the open upper half-plane.

**Reading.** The source defines $f$ on $C$. Lean assigns $+\infty$ off $C$. -/
noncomputable def halfPlaneFn (x : Rn 2) : EReal :=
  ⨅ _ : 0 < x 1, ((x 0 ^ 2 / (4 * x 1) : ℝ) : EReal)

/-- For $\xi_2 > 0$ the example of p. 257 takes the value $\xi_1^2/4\xi_2$. -/
theorem halfPlaneFn_of_pos {x : Rn 2} (hx : 0 < x 1) :
    halfPlaneFn x = ((x 0 ^ 2 / (4 * x 1) : ℝ) : EReal) := iInf_pos hx

/-- For $\xi_2 \le 0$ the Lean extension of the example of p. 257 takes the value $+\infty$.

**Reading.** These points are outside the domain of the real-valued function in the source. -/
theorem halfPlaneFn_of_nonpos {x : Rn 2} (hx : ¬ 0 < x 1) : halfPlaneFn x = ⊤ := iInf_neg hx

/-- The example of p. 257 never takes the value $-\infty$. -/
theorem halfPlaneFn_ne_bot (x : Rn 2) : halfPlaneFn x ≠ ⊥ := by
  by_cases hx : 0 < x 1
  · rw [halfPlaneFn_of_pos hx]; exact EReal.coe_ne_bot _
  · rw [halfPlaneFn_of_nonpos hx]; exact top_ne_bot

/-- The effective domain of the example of p. 257 is the open upper half-plane
$\{(\xi_1, \xi_2) \mid \xi_2 > 0\}$. -/
theorem convexDom_halfPlaneFn : convexDom halfPlaneFn = {x : Rn 2 | 0 < x 1} := by
  ext x
  rw [mem_convexDom]
  by_cases hx : 0 < x 1
  · simp [halfPlaneFn_of_pos hx, hx]
  · simp [halfPlaneFn_of_nonpos hx, hx]

/-- For the example of p. 257, $C = \operatorname{int}(\operatorname{dom} f)$ is the open upper
half-plane, as in the source. -/
theorem interior_convexDom_halfPlaneFn : interior (convexDom halfPlaneFn) =
    {x : Rn 2 | 0 < x 1} := by
  rw [convexDom_halfPlaneFn]
  exact IsOpen.interior_eq (isOpen_lt continuous_const (by fun_prop))

/-- The example of p. 257 is convex. A square divided by a positive linear function is jointly
convex: for points $\xi$, $\eta$ of the open upper half-plane and $a, b > 0$ with $a + b = 1$,
the gap $a f(\xi) + b f(\eta) - f(a\xi + b\eta)$ is $ab(\xi_1\eta_2 - \eta_1\xi_2)^2 /
4\xi_2\eta_2(a\xi_2 + b\eta_2)$. -/
theorem convexFn_halfPlaneFn : ConvexFn halfPlaneFn := by
  refine (convexFn_iff_le halfPlaneFn_ne_bot).2 fun x y a b ha hb hab => ?_
  by_cases hx : 0 < x 1
  · by_cases hy : 0 < y 1
    · have h0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := rfl
      have h1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := rfl
      have hz : 0 < (a • x + b • y) 1 := by rw [h1]; positivity
      rw [halfPlaneFn_of_pos hx, halfPlaneFn_of_pos hy, halfPlaneFn_of_pos hz, h0, h1,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_le_coe_iff]
      have hx0 : x 1 ≠ 0 := ne_of_gt hx
      have hy0 : y 1 ≠ 0 := ne_of_gt hy
      have hs : 0 < a * x 1 + b * y 1 := by positivity
      have hs0 : a * x 1 + b * y 1 ≠ 0 := ne_of_gt hs
      have hid : a * (x 0 ^ 2 / (4 * x 1)) + b * (y 0 ^ 2 / (4 * y 1))
            - (a * x 0 + b * y 0) ^ 2 / (4 * (a * x 1 + b * y 1))
          = a * b * (x 0 * y 1 - y 0 * x 1) ^ 2
              / (4 * (x 1 * y 1 * (a * x 1 + b * y 1))) := by
        field_simp
        ring
      have hnn : 0 ≤ a * b * (x 0 * y 1 - y 0 * x 1) ^ 2
          / (4 * (x 1 * y 1 * (a * x 1 + b * y 1))) := by positivity
      linarith
    · rw [halfPlaneFn_of_nonpos hy, EReal.coe_mul_top_of_pos hb,
        EReal.add_top_of_ne_bot (EReal.coe_mul_ne_bot ha.le (halfPlaneFn_ne_bot x))]
      exact le_top
  · rw [halfPlaneFn_of_nonpos hx, EReal.coe_mul_top_of_pos ha,
      EReal.top_add_of_ne_bot (EReal.coe_mul_ne_bot hb.le (halfPlaneFn_ne_bot y))]
    exact le_top

/-- The example of p. 257 is a proper function. -/
theorem properConvex_halfPlaneFn : ProperConvex halfPlaneFn := by
  refine ⟨⟨WithLp.toLp 2 ![0, 1], ?_⟩, halfPlaneFn_ne_bot⟩
  rw [mem_convexDom, halfPlaneFn_of_pos (x := WithLp.toLp 2 ![0, 1]) (by norm_num)]
  exact EReal.coe_lt_top _

/-- Let $x = (\xi_1, \xi_2)$ with $\xi_2 > 0$. A vector $u = (u_1, u_2)$ is a subgradient at $x$ of
the example of p. 257 if and only if $u_2 = -u_1^2$ and $\xi_1 = 2u_1\xi_2$.

Both directions come from the completed square $\xi_1^2/4\xi_2 - u_1\xi_1 - u_2\xi_2 = (\xi_1 -
2u_1\xi_2)^2/4\xi_2 - \xi_2(u_1^2 + u_2)$, whose infimum over the ray $(2su_1, s)$, $s > 0$, is
$-s(u_1^2 + u_2)$. Tests at $s = \xi_2$, $s = \xi_2 + 1$ and $s = \xi_2/2$ give both conditions. -/
theorem mem_subdifferential_halfPlaneFn_iff {x u : Rn 2} (hx : 0 < x 1) :
    u ∈ subdifferential (pairing 2) halfPlaneFn x ↔ u 1 = -(u 0) ^ 2 ∧ x 0 = 2 * u 0 * x 1 := by
  constructor
  · intro h
    have key : ∀ s : ℝ, 0 < s →
        x 0 ^ 2 / (4 * x 1) - u 0 * x 0 - u 1 * x 1 ≤ -(s * (u 0 ^ 2 + u 1)) := by
      intro s hs
      have hzs : (0 : ℝ) < (WithLp.toLp 2 ![2 * s * u 0, s] : Rn 2) 1 := hs
      have hle := h (WithLp.toLp 2 ![2 * s * u 0, s] : Rn 2)
      rw [halfPlaneFn_of_pos hx, halfPlaneFn_of_pos hzs, pairing_two] at hle
      rw [sub_apply_two, sub_apply_two, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at hle
      have e0 : (WithLp.toLp 2 ![2 * s * u 0, s] : Rn 2) 0 = 2 * s * u 0 := rfl
      have e1 : (WithLp.toLp 2 ![2 * s * u 0, s] : Rn 2) 1 = s := rfl
      rw [e0, e1] at hle
      have hrs : (2 * s * u 0) ^ 2 / (4 * s) = s * u 0 ^ 2 := by
        field_simp
        ring
      rw [hrs] at hle
      nlinarith [hle]
    have hK : 0 ≤ (x 0 - 2 * u 0 * x 1) ^ 2 / (4 * x 1) := by positivity
    have hid : x 0 ^ 2 / (4 * x 1) - u 0 * x 0 - u 1 * x 1
        = (x 0 - 2 * u 0 * x 1) ^ 2 / (4 * x 1) - x 1 * (u 0 ^ 2 + u 1) := by
      have hx0 : x 1 ≠ 0 := ne_of_gt hx
      field_simp
      ring
    have h1 := key (x 1) hx
    have h2 := key (x 1 + 1) (by linarith)
    have h3 := key (x 1 / 2) (by linarith)
    rw [hid] at h1 h2 h3
    have hd : u 0 ^ 2 + u 1 = 0 := by nlinarith [hK, hx]
    have hKz : (x 0 - 2 * u 0 * x 1) ^ 2 / (4 * x 1) = 0 := by nlinarith [hK, hd]
    refine ⟨by linarith, ?_⟩
    have hx0 : x 1 ≠ 0 := ne_of_gt hx
    have hsq : (x 0 - 2 * u 0 * x 1) ^ 2 = 0 := by
      field_simp at hKz
      simpa using hKz
    have hz := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  · rintro ⟨hu1, hu0⟩ z
    by_cases hz : 0 < z 1
    · rw [halfPlaneFn_of_pos hx, halfPlaneFn_of_pos hz, pairing_two, sub_apply_two,
        sub_apply_two, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hz4 : (0 : ℝ) < 4 * z 1 := by linarith
      have hxval : x 0 ^ 2 / (4 * x 1) = u 0 ^ 2 * x 1 := by
        have hx0 : x 1 ≠ 0 := ne_of_gt hx
        rw [hu0]
        field_simp
        ring
      rw [hxval, hu0, hu1, le_div_iff₀ hz4]
      nlinarith [sq_nonneg (z 0 - 2 * u 0 * z 1)]
    · rw [halfPlaneFn_of_nonpos hz]
      exact le_top

/-- On the open upper half-plane, the subdifferential of the example of p. 257 at
$x = (\xi_1, \xi_2)$ is the single vector $(\xi_1/2\xi_2, -\xi_1^2/4\xi_2^2)$, which lies on the
parabola $P$. -/
theorem subdifferential_halfPlaneFn {x : Rn 2} (hx : 0 < x 1) :
    subdifferential (pairing 2) halfPlaneFn x = {parabolaPoint (x 0 / (2 * x 1))} := by
  have hx0 : x 1 ≠ 0 := ne_of_gt hx
  ext u
  rw [mem_subdifferential_halfPlaneFn_iff hx, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hu1, hu0⟩
    have hu : u 0 = x 0 / (2 * x 1) := by field_simp; linarith
    exact ext_two (by rw [parabolaPoint_zero, hu]) (by rw [parabolaPoint_one, hu1, hu])
  · rintro rfl
    refine ⟨by rw [parabolaPoint_zero, parabolaPoint_one], ?_⟩
    rw [parabolaPoint_zero]
    field_simp

/-- The example of p. 257 is differentiable at every point $x = (\xi_1, \xi_2)$ with $\xi_2 > 0$,
and its gradient there is $(\xi_1/2\xi_2, -\xi_1^2/4\xi_2^2)$, its unique subgradient (Theorem
25.1). -/
theorem hasGradientAtFn_halfPlaneFn {x : Rn 2} (hx : 0 < x 1) :
    HasGradientAtFn halfPlaneFn
      (InnerProductSpace.toDual ℝ (Rn 2) (parabolaPoint (x 0 / (2 * x 1)))) x :=
  hasGradientAtFn_toDual_of_subdifferential_eq_singleton convexFn_halfPlaneFn
      properConvex_halfPlaneFn
    (subdifferential_halfPlaneFn hx)

/-- The example of p. 257 is differentiable at every point of
$C = \operatorname{int}(\operatorname{dom} f)$. -/
theorem differentiableAtFn_halfPlaneFn ⦃z : Rn 2⦄ (hz : z ∈ interior (convexDom halfPlaneFn)) :
    DifferentiableAtFn halfPlaneFn z := by
  rw [interior_convexDom_halfPlaneFn] at hz
  exact ⟨_, hasGradientAtFn_halfPlaneFn hz⟩

/-- **Section 26** of [rockafellar1970convex], p. 257. For the example of p. 257, the set
`ConvexAnalysis.gradientRange` of all gradients is the parabola $P$. As $x$ runs over the open
upper half-plane, $\xi_1/2\xi_2$ runs over all of $\mathbb{R}$, and the second coordinate of the
gradient is minus the square of the first. -/
theorem gradientRange_halfPlaneFn : gradientRange halfPlaneFn = parabola := by
  ext v
  constructor
  · rintro ⟨x, hx⟩
    have hxi : x ∈ interior (convexDom halfPlaneFn) := hx.mem_interior_convexDom
    rw [interior_convexDom_halfPlaneFn] at hxi
    have hsing := subdifferential_innerL_eq_singleton convexFn_halfPlaneFn hx
    rw [LinearIsometryEquiv.symm_apply_apply] at hsing
    have hv : v ∈ subdifferential (pairing 2) halfPlaneFn x := by
      rw [hsing]
      exact Set.mem_singleton v
    exact ((mem_subdifferential_halfPlaneFn_iff hxi).1 hv).1
  · intro hv
    refine ⟨WithLp.toLp 2 ![v 0, 1 / 2], ?_⟩
    have hx1 : (0 : ℝ) < (WithLp.toLp 2 ![v 0, 1 / 2] : Rn 2) 1 := by norm_num
    have h := hasGradientAtFn_halfPlaneFn hx1
    have e0 : (WithLp.toLp 2 ![v 0, 1 / 2] : Rn 2) 0 = v 0 := rfl
    have e1 : (WithLp.toLp 2 ![v 0, 1 / 2] : Rn 2) 1 = 1 / 2 := rfl
    have hpt : parabolaPoint ((WithLp.toLp 2 ![v 0, 1 / 2] : Rn 2) 0
        / (2 * (WithLp.toLp 2 ![v 0, 1 / 2] : Rn 2) 1)) = v := by
      refine ext_two ?_ ?_
      · rw [parabolaPoint_zero, e0, e1]
        norm_num
      · rw [parabolaPoint_one, mem_parabola.1 hv, e0, e1]
        norm_num
    rwa [hpt] at h

/-- **Section 26** of [rockafellar1970convex], p. 257. For the example of p. 257, the domain $D$ of
the Legendre conjugate is the parabola $P$. -/
theorem legendreDomain_halfPlaneFn : legendreDomain halfPlaneFn = parabola := by
  rw [legendreDomain_eq_gradientRange differentiableAtFn_halfPlaneFn]
  exact gradientRange_halfPlaneFn

/-- The parabola $P$ is not convex: $(0, 0)$ and $(1, -1)$ lie on $P$, and their midpoint
$(1/2, -1/2)$ does not, since $-1/2 \neq -1/4$. -/
theorem not_convex_parabola : ¬ Convex ℝ parabola := by
  intro h
  have h0 : parabolaPoint 0 ∈ parabola := by
    rw [mem_parabola, parabolaPoint_zero, parabolaPoint_one]
  have h1 : parabolaPoint 1 ∈ parabola := by
    rw [mem_parabola, parabolaPoint_zero, parabolaPoint_one]
  have hm := h h0 h1 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  rw [mem_parabola] at hm
  have e0 : ((1/2 : ℝ) • parabolaPoint 0 + (1/2 : ℝ) • parabolaPoint 1) 0 = 1/2 := by
    change (1/2 : ℝ) * parabolaPoint 0 0 + (1/2 : ℝ) * parabolaPoint 1 0 = 1/2
    rw [parabolaPoint_zero, parabolaPoint_zero]
    norm_num
  have e1 : ((1/2 : ℝ) • parabolaPoint 0 + (1/2 : ℝ) • parabolaPoint 1) 1 = -(1/2) := by
    change (1/2 : ℝ) * parabolaPoint 0 1 + (1/2 : ℝ) * parabolaPoint 1 1 = -(1/2)
    rw [parabolaPoint_one, parabolaPoint_one]
    norm_num
  rw [e0, e1] at hm
  norm_num at hm

/-- **Section 26** of [rockafellar1970convex], p. 257, the point of the example. For the example of
p. 257, a differentiable convex function on a non-empty open convex set that fails condition
(c), the domain $D$ of the Legendre conjugate is not convex. So it is not almost convex in the
sense of Corollary 26.4.1. -/
theorem not_convex_legendreDomain_halfPlaneFn : ¬ Convex ℝ (legendreDomain halfPlaneFn) := by
  rw [legendreDomain_halfPlaneFn]
  exact not_convex_parabola

/-- **Section 26** of [rockafellar1970convex], p. 257, last sentence: condition (c) fails for the
example of p. 257 at the origin. Along the sequence $(0, 1/(i+1))$, which lies in $C$ and
converges to the origin, the gradient is $0$. So its norm does not tend to $+\infty$, and the
example is not essentially smooth.

This is why Corollary 26.4.1 does not apply to the example, and why
`Rockafellar.not_convex_legendreDomain_halfPlaneFn` does not contradict that corollary. -/
theorem not_essentiallySmooth_halfPlaneFn : ¬ EssentiallySmooth halfPlaneFn := by
  intro hes
  set e : Rn 2 := WithLp.toLp 2 ![0, 1] with he
  set zs : ℕ → Rn 2 := fun i => (1 / (i + 1 : ℝ)) • e with hzsdef
  have hcoord : ∀ i : ℕ, zs i 1 = 1 / (i + 1 : ℝ) := by
    intro i
    change (1 / (i + 1 : ℝ)) * (1 : ℝ) = 1 / (i + 1 : ℝ)
    ring
  have hcoord0 : ∀ i : ℕ, zs i 0 = 0 := by
    intro i
    change (1 / (i + 1 : ℝ)) * (0 : ℝ) = 0
    ring
  have hpos : ∀ i : ℕ, (0 : ℝ) < zs i 1 := by
    intro i
    rw [hcoord i]
    positivity
  have hmem : ∀ i, zs i ∈ interior (convexDom halfPlaneFn) := by
    intro i
    rw [interior_convexDom_halfPlaneFn]
    exact hpos i
  have hout : (0 : Rn 2) ∉ interior (convexDom halfPlaneFn) := by
    rw [interior_convexDom_halfPlaneFn]
    intro hc
    have hlt : (0 : ℝ) < (0 : Rn 2) 1 := hc
    simp at hlt
  have hlim : Tendsto zs atTop (𝓝 (0 : Rn 2)) := by
    have hc : Tendsto (fun i : ℕ => (1 / (i + 1 : ℝ))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hcs := hc.smul_const e
    rwa [zero_smul] at hcs
  have htop := hes.tendsto_norm_fderiv hout zs hmem hlim
  have hzero : ∀ i, ‖fderiv ℝ (fun w => (halfPlaneFn w).toReal) (zs i)‖ = 0 := by
    intro i
    have hg := hasGradientAtFn_halfPlaneFn (hpos i)
    rw [hg.fderiv_toReal_eq]
    have hpt : parabolaPoint (zs i 0 / (2 * zs i 1)) = 0 := by
      rw [hcoord0 i, zero_div]
      exact parabolaPoint_zero_eq
    rw [hpt, map_zero, norm_zero]
  rw [tendsto_congr hzero] at htop
  exact not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds htop

/-!
### Functions of Legendre type

A pair $(C, f)$, with $C$ open and convex and $f$ strictly convex on $C$, that satisfies conditions
(a), (b) and (c) is a **convex function of Legendre type** (p. 258). Since
$C = \operatorname{int}(\operatorname{dom} f)$ is determined by $f$, this is the backbone's
`ConvexAnalysis.LegendreType f`. By Corollary 26.3.1 it holds exactly when $\partial f$ is
one-to-one.
-/

/-- **Section 26** of [rockafellar1970convex], p. 258, the remark after the definition of Legendre
type. Let $f$ be a closed proper convex function on $\mathbb{R}^n$. Then the restriction of $f$
to $C = \operatorname{int}(\operatorname{dom} f)$ is a convex function of Legendre type if and
only if $\partial f$ is one-to-one. -/
theorem legendreType_iff (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f) :
    LegendreType f ↔ OneToOne (subdifferential (pairing n) f) :=
  (legendreType_iff_subdifferential_injective hf hp hcl).trans oneToOne_iff.symm

/-! ### Theorem 26.5 -/

/-- **Theorem 26.5** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$, and let $C = \operatorname{int}(\operatorname{dom} f)$ and $C^* =
\operatorname{int}(\operatorname{dom} f^*)$. Then $(C, f)$ is a convex function of Legendre type
if and only if $(C^*, f^*)$ is.

**Reading.** The source says closed convex function. Its proof needs a closed proper convex
function, so $f$ is assumed proper here. Nothing is lost: an improper closed convex function is
$+\infty$ everywhere or $-\infty$ on $\operatorname{cl}(\operatorname{dom} f)$, so it is
differentiable at no point.

The other assertions of the theorem are `Rockafellar.theorem_26_5_legendreDomain` to
`Rockafellar.theorem_26_5_gradient_gradient_conj`. -/
theorem theorem_26_5 (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f) :
    LegendreType f ↔ LegendreType (convexConj (pairing n) f) :=
  (legendreType_convexConj_iff hf hp hcl).symm

/-- **Theorem 26.5** of [rockafellar1970convex], the domain of the Legendre conjugate. Let $f$ be a
closed proper convex function of Legendre type on $\mathbb{R}^n$. Then the domain $D$ of the
Legendre conjugate of $(C, f)$ is $C^* = \operatorname{int}(\operatorname{dom} f^*)$. With
`Rockafellar.theorem_26_5_conj_apply`, this says that $(C^*, f^*)$ is the Legendre conjugate of
$(C, f)$. -/
theorem theorem_26_5_legendreDomain (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hleg : LegendreType f) :
    legendreDomain f = interior (convexDom (convexConj (pairing n) f)) := by
  rw [legendreDomain_eq_gradientRange hleg.1.differentiableAtFn]
  exact gradientRange_eq_interior_convexDom_convexConj hf hp hcl hleg

/-- **Theorem 26.5** of [rockafellar1970convex], the values of the Legendre conjugate. Let $f$ be a
convex function of Legendre type on $\mathbb{R}^n$, and let $x \in C$. Then
$$f^*(\nabla f(x)) = \langle x, \nabla f(x) \rangle - f(x).$$

**Generalization.** This formula holds without closedness. -/
theorem theorem_26_5_conj_apply (hf : ConvexFn f) (hleg : LegendreType f) {x : Rn n}
    (hx : x ∈ interior (convexDom f)) :
    convexConj (pairing n) f (gradient (fun w => (f w).toReal) x)
      = ((pairing n x (gradient (fun w => (f w).toReal) x) - (f x).toReal : ℝ) : EReal) :=
  corollary_26_4_1_eq hf hleg.1 hx

/-- **Theorem 26.5** of [rockafellar1970convex], the domain of the converse. Let $f$ be a closed
proper convex function of Legendre type on $\mathbb{R}^n$. Then the domain of the Legendre
conjugate of $(C^*, f^*)$ is $C$. This is the involution property of the Legendre
transformation. It holds only for functions of Legendre type; see
`Rockafellar.not_convex_legendreDomain_halfPlaneFn`. -/
theorem theorem_26_5_legendreDomain_conj (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hleg : LegendreType f) :
    legendreDomain (convexConj (pairing n) f) = interior (convexDom f) := by
  have hgleg := hleg.convexConj hf hp hcl
  have h :=
      theorem_26_5_legendreDomain (convexFn_convexConj _ f) (properConvex_convexConj ⟨hf, hcl, hp⟩)
    closedConvex_convexConj hgleg
  rwa [convexConj_convexConj_innerL hf hcl] at h

/-- **Theorem 26.5** of [rockafellar1970convex], the values of the converse. Let $f$ be a closed
proper convex function of Legendre type on $\mathbb{R}^n$, and let $v \in C^*$. Then
$$f(\nabla f^*(v)) = \langle v, \nabla f^*(v) \rangle - f^*(v).$$
So $(C, f)$ is in turn the Legendre conjugate of $(C^*, f^*)$. Again this holds only for
functions of Legendre type. -/
theorem theorem_26_5_apply (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hleg : LegendreType f) {v : Rn n} (hv : v ∈ interior (convexDom (convexConj (pairing n) f))) :
    f (gradient (fun w => (convexConj (pairing n) f w).toReal) v)
      = ((pairing n v (gradient (fun w => (convexConj (pairing n) f w).toReal) v)
          - (convexConj (pairing n) f v).toReal : ℝ) : EReal) := by
  have hgleg := hleg.convexConj hf hp hcl
  have h := corollary_26_4_1_eq (convexFn_convexConj (pairing n) f) hgleg.1 hv
  rwa [convexConj_convexConj_innerL hf hcl] at h

/-- **Theorem 26.5** of [rockafellar1970convex], the gradient mapping. Let $f$ be a closed proper
convex function of Legendre type on $\mathbb{R}^n$. Then $\nabla f$ is a one-to-one mapping from
the open convex set $C$ onto the open convex set $C^*$. -/
theorem theorem_26_5_bijOn (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hleg : LegendreType f) :
    Set.BijOn (gradient fun w => (f w).toReal) (interior (convexDom f))
      (interior (convexDom (convexConj (pairing n) f))) :=
  bijOn_gradient_of_legendreType hf hp hcl hleg

/-- **Theorem 26.5** of [rockafellar1970convex], continuity of $\nabla f$. Let $f$ be a proper
convex function of Legendre type on $\mathbb{R}^n$. Then $\nabla f$ is continuous on $C$.

**Generalization.** This continuity holds without closedness. -/
theorem theorem_26_5_continuousOn (hf : ConvexFn f) (hp : ProperConvex f) (hleg : LegendreType f) :
    ContinuousOn (gradient fun w => (f w).toReal) (interior (convexDom f)) :=
  continuousOn_gradient_interior_convexDom hf hp hleg.1

/-- **Theorem 26.5** of [rockafellar1970convex], continuity of $\nabla f^*$. Let $f$ be a closed
proper convex function of Legendre type on $\mathbb{R}^n$. Then $\nabla f^*$ is continuous on
$C^*$. With `Rockafellar.theorem_26_5_continuousOn`, this says that $\nabla f$ is continuous in
both directions. -/
theorem theorem_26_5_continuousOn_conj (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hleg : LegendreType f) :
    ContinuousOn (gradient fun w => (convexConj (pairing n) f w).toReal)
      (interior (convexDom (convexConj (pairing n) f))) :=
  continuousOn_gradient_interior_convexDom (convexFn_convexConj _ f)
      (properConvex_convexConj ⟨hf, hcl, hp⟩)
    (hleg.convexConj hf hp hcl).1

/-- **Theorem 26.5** of [rockafellar1970convex], $\nabla f^* = (\nabla f)^{-1}$, first composite.
Let $f$ be a closed proper convex function of Legendre type on $\mathbb{R}^n$, and let
$x \in C$. Then $\nabla f^*(\nabla f(x)) = x$. -/
theorem theorem_26_5_gradient_conj (hf : ConvexFn f) (hp : ProperConvex f) (hcl : ClosedConvex f)
    (hleg : LegendreType f) {x : Rn n} (hx : x ∈ interior (convexDom f)) :
    gradient (fun w => (convexConj (pairing n) f w).toReal)
        (gradient (fun w => (f w).toReal) x) = x :=
  gradient_convexConj_gradient hf hp hcl hleg hx

/-- **Theorem 26.5** of [rockafellar1970convex], $\nabla f^* = (\nabla f)^{-1}$, second composite.
Let $f$ be a closed proper convex function of Legendre type on $\mathbb{R}^n$, and let
$v \in C^*$. Then $\nabla f(\nabla f^*(v)) = v$. -/
theorem theorem_26_5_gradient_gradient_conj (hf : ConvexFn f) (hp : ProperConvex f)
    (hcl : ClosedConvex f)
    (hleg : LegendreType f) {v : Rn n} (hv : v ∈ interior (convexDom (convexConj (pairing n) f))) :
    gradient (fun w => (f w).toReal)
        (gradient (fun w => (convexConj (pairing n) f w).toReal) v) = v :=
  gradient_gradient_convexConj hf hp hcl hleg hv

/-! ### Theorem 26.6 -/

/-- **Theorem 26.6** of [rockafellar1970convex]. Let $f$ be a finite differentiable convex function
on $\mathbb{R}^n$. Then $\nabla f$ is a one-to-one mapping from $\mathbb{R}^n$ onto itself if
and only if $f$ is strictly convex and co-finite.

A finite function is a proper function with $\operatorname{dom} f = \mathbb{R}^n$. Co-finiteness
is `ConvexAnalysis.Cofinite`: $f$ is closed, proper and convex, and its recession function is
$+\infty$ in every direction $y \neq 0$. -/
theorem theorem_26_6 (hf : ConvexFn f) (hp : ProperConvex f) (hdom : convexDom f = Set.univ)
    (hdiff : ∀ z : Rn n, DifferentiableAtFn f z) :
    Set.BijOn (gradient fun w => (f w).toReal) Set.univ Set.univ ↔
      (StrictConvexOnFn f Set.univ ∧ Cofinite f) := by
  have hcl : ClosedConvex f := closedConvex_of_convexDom_eq_univ hf hp hdom
  rw [bijOn_gradient_univ_iff hf hp hdom hdiff,
    ← cofinite_iff_convexDom_convexConj_eq_univ (B := pairing n) ⟨hf, hcl, hp⟩]

/-- **Theorem 26.6** of [rockafellar1970convex], the concluding clauses. Let $f$ be a finite
differentiable convex function on $\mathbb{R}^n$ such that $\nabla f$ is a one-to-one mapping
from $\mathbb{R}^n$ onto itself. Then $f^*$ is also finite and differentiable on $\mathbb{R}^n$,
and it is strictly convex and co-finite. -/
theorem theorem_26_6_conj (hf : ConvexFn f) (hp : ProperConvex f) (hdom : convexDom f = Set.univ)
    (hdiff : ∀ z : Rn n, DifferentiableAtFn f z)
    (hbij : Set.BijOn (gradient fun w => (f w).toReal) Set.univ Set.univ) :
    convexDom (convexConj (pairing n) f) = Set.univ ∧
      (∀ z : Rn n, DifferentiableAtFn (convexConj (pairing n) f) z) ∧
      StrictConvexOnFn (convexConj (pairing n) f) Set.univ
          ∧ Cofinite (convexConj (pairing n) f) := by
  have hcl : ClosedConvex f := closedConvex_of_convexDom_eq_univ hf hp hdom
  obtain ⟨hdc, hdiffc, hscc⟩ := convexConj_finite_of_bijOn_gradient_univ hf hp hdom hdiff hbij
  refine ⟨hdc, hdiffc, hscc, ?_⟩
  have hcpc : ClosedProperConvexFn (convexConj (pairing n) f) :=
    ⟨convexFn_convexConj _ f, closedConvex_convexConj, properConvex_convexConj ⟨hf, hcl, hp⟩⟩
  rw [cofinite_iff_convexDom_convexConj_eq_univ (B := pairing n) hcpc,
      convexConj_convexConj_innerL hf hcl]
  exact hdom

/-- **Theorem 26.6** of [rockafellar1970convex], the formula for $f^*$. Let $f$ be a convex function
on $\mathbb{R}^n$ that is differentiable at every point. Then for every $x \in \mathbb{R}^n$
$$f^*(\nabla f(x)) = \langle x, \nabla f(x) \rangle - f(x).$$
When $\nabla f$ is one-to-one from $\mathbb{R}^n$ onto itself, this says that $f^*$ is the
Legendre conjugate of $f$: $f^*(x^*) = \langle (\nabla f)^{-1}(x^*), x^* \rangle - f((\nabla
f)^{-1}(x^*))$ for every $x^*$.

**Generalization.** The displayed formula at $\nabla f(x)$ holds without gradient
bijectivity. -/
theorem theorem_26_6_apply (hf : ConvexFn f) (hdiff : ∀ z : Rn n, DifferentiableAtFn f z)
    (x : Rn n) :
    convexConj (pairing n) f (gradient (fun w => (f w).toReal) x)
      = ((pairing n x (gradient (fun w => (f w).toReal) x) - (f x).toReal : ℝ) : EReal) :=
  theorem_26_4_eq hf (hdiff x).hasGradientAtFn_gradient

/-! ### Lemma 26.7 -/

/-- **Lemma 26.7** of [rockafellar1970convex]. Let $f$ be a finite differentiable convex function on
$\mathbb{R}^n$. Then $f$ is co-finite if and only if $|\nabla f(x_i)| \to +\infty$ for every
sequence $(x_i)$ in $\mathbb{R}^n$ with $|x_i| \to +\infty$.

A finite function is a proper function with $\operatorname{dom} f = \mathbb{R}^n$. -/
theorem lemma_26_7 (hf : ConvexFn f) (hp : ProperConvex f) (hdom : convexDom f = Set.univ)
    (hdiff : ∀ z : Rn n, DifferentiableAtFn f z) :
    Cofinite f ↔ ∀ xs : ℕ → Rn n, Tendsto (fun i => ‖xs i‖) atTop atTop →
      Tendsto (fun i => ‖gradient (fun w => (f w).toReal) (xs i)‖) atTop atTop :=
  cofinite_iff_forall_tendsto_norm_gradient_atTop hf hp hdom hdiff

end Rockafellar
