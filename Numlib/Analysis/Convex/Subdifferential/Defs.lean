/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.EReal.Inv
import Mathlib.Basic.Rel
import Numlib.Analysis.Convex.Duality.Support

/-!
# Subgradients, normal cones and directional derivatives

Let $E$ and $F$ be real vector spaces paired by a bilinear form $\langle x, y \rangle$, and let
$f : E \to [-\infty, +\infty]$. A **subgradient** of $f$ at $x$ is a vector $y \in F$ such that the
affine function $z \mapsto f(x) + \langle z - x, y \rangle$ minorizes $f$:
$$f(z) \ge f(x) + \langle z - x, y \rangle \quad \text{for all } z \in E.$$
When $f(x)$ is finite, this says that the graph of the affine function is a non-vertical supporting
hyperplane to $\operatorname{epi} f$ at $(x, f(x))$. The set of subgradients is the
**subdifferential** $\partial f(x)$. The definition is algebraic, a system of weak linear
inequalities, one for each $z$, and no topology enters until the closure of $f$ does. The module
also defines the normal cone $N_C(x)$ of a set $C$ and the one-sided directional derivative
$f'(x; y)$, and develops the elementary theory of all three. The presentation follows
[rockafellar1970convex], §23.

## Main definitions

* `ConvexAnalysis.subdifferential`: the subdifferential $\partial f(x) \subseteq F$.
* `ConvexAnalysis.subgradientRel`: the graph $\{(x, y) \mid y \in \partial f(x)\}$ of the
  multivalued map $\partial f$.
* `ConvexAnalysis.domSubdifferential`: the set $\operatorname{dom} \partial f$ of points where
  $\partial f(x)$ is nonempty.
* `ConvexAnalysis.normalCone`, `ConvexAnalysis.normalPointedCone`: the normal cone $N_C(x) = \{y
  \mid \langle z - x, y \rangle \le 0 \text{ for all } z \in C\}$, as a set and as a pointed convex
  cone.
* `ConvexAnalysis.superdifferential`: the set of supergradients of a concave function.
* `ConvexAnalysis.dirDeriv`: the directional derivative $f'(x; y) = \inf_{\lambda > 0} (f(x +
  \lambda y) - f(x)) / \lambda$.

## Main results

* `ConvexAnalysis.ProperConvex.mem_subdifferential_tfae`: for proper $f$, the conditions
  $y \in \partial f(x)$, "$\langle \cdot, y \rangle - f$ attains its supremum at $x$",
  $f(x) + f^*(y) \le \langle x, y \rangle$ and $f(x) + f^*(y) = \langle x, y \rangle$ are
  equivalent. This is Theorem 23.5 of [rockafellar1970convex]. All implications except the one back
  from the last condition hold for every $f$.
* `ConvexAnalysis.subgradientRel_convexConj_eq_inv`: for closed convex $f$, the graph of
  $\partial f^*$ is the inverse of the graph of $\partial f$.
* `ConvexAnalysis.subdifferential_convexCl`: $\partial (\operatorname{cl} f)(x) = \partial f(x)$
  wherever $\partial f(x)$ is nonempty.
* `ConvexAnalysis.subdifferential_indicatorFn`: $\partial \delta(\cdot \mid C)(x) = N_C(x)$ for
  $x \in C$.
* `ConvexAnalysis.subdifferential_supportFn`: the subgradients of $\delta^*(\cdot \mid C)$ at $y$
  are the maximizers of $\langle \cdot, y \rangle$ over $C$.
* `ConvexAnalysis.monotoneOn_sub_div`, `ConvexAnalysis.posHomogeneous_dirDeriv`,
  `ConvexAnalysis.convexFn_dirDeriv`: the difference quotient is nondecreasing in the step, and
  $f'(x; \cdot)$ is positively homogeneous and convex.
* `ConvexAnalysis.mem_subdifferential_iff_le_dirDeriv`, `ConvexAnalysis.convexConj_dirDeriv`,
  `ConvexAnalysis.convexCl_dirDeriv`: $y \in \partial f(x)$ exactly when
  $\langle \cdot, y \rangle \le f'(x; \cdot)$, and $\operatorname{cl} f'(x; \cdot)$ is the support
  function of $\partial f(x)$. This is Theorem 23.2 of [rockafellar1970convex].
* `ConvexAnalysis.properConvex_of_mem_subdifferential`: a function with a subgradient at a point
  where it is finite is proper.

## Implementation notes

* $\partial f$ is available both pointwise and as a relation (`SetRel E F`). The monotonicity and
  Legendre theory is about the graph, and with `ConvexAnalysis.subgradientRel` the inversion reads
  literally as $\partial (f^*) = (\partial f)^{-1}$.
* $\partial f(x)$ is not bundled as a convex set. Convexity holds with no hypothesis, but closedness
  needs a continuous pairing, and a bundled object would carry that hypothesis as data. $N_C(x)$ is
  bundled as a pointed cone, because it is a cone for every $C$ and $x$.
* The pairing is a bilinear map `B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ`. The value `B x y` is written
  $\langle x, y \rangle$. The conjugate $f^*$ is `ConvexAnalysis.convexConj B f`, a function on $F$.
* The directional derivative is meaningful only where $f(x)$ is finite. In `EReal`,
  $+\infty - (+\infty) = -\infty$, so off $\operatorname{dom} f$ the difference quotient is
  $-\infty$ in every direction and $f'(x; 0) = 0$ fails. Statements that use a value of
  $f'(x; \cdot)$ therefore assume $f(x) \ne +\infty$ and $f(x) \ne -\infty$. Positive homogeneity is
  the exception, because it is a reindexing of the infimum.
-/

open Set

namespace ConvexAnalysis

/-! ### Definitions -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **subdifferential** of $f : E \to [-\infty, +\infty]$ at $x$ with respect to the pairing
$\langle \cdot, \cdot \rangle$ is the set of $y \in F$ that satisfy the **subgradient
inequality**
$$f(z) \ge f(x) + \langle z - x, y \rangle \quad \text{for all } z \in E.$$

When $f(x)$ is finite, $y$ is a subgradient exactly when the graph of the affine function
$z \mapsto f(x) + \langle z - x, y \rangle$ is a non-vertical supporting hyperplane to
$\operatorname{epi} f$ at $(x, f(x))$. The sum $f(x) + \langle z - x, y \rangle$ is taken in
`EReal`. -/
def subdifferential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) : Set F :=
  {y | ∀ z, f x + ((B (z - x) y : ℝ) : EReal) ≤ f z}

/-- The **graph of the subdifferential**: the multivalued map
$\partial f : x \mapsto \partial f(x)$, as the relation $\{(x, y) \in E \times F \mid y \in
\partial f(x)\}$.

The monotonicity and duality theory is about this relation, and conjugation inverts it
(`ConvexAnalysis.subgradientRel_convexConj_eq_inv`). -/
def subgradientRel (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : SetRel E F :=
  {p | p.2 ∈ subdifferential B f p.1}

/-- The **normal cone** to a set $C \subseteq E$ at $x \in E$ is the set of $y \in F$ that make a
non-acute angle with every direction from $x$ into $C$:
$$N_C(x) = \{y \in F \mid \langle z - x, y \rangle \le 0 \text{ for all } z \in C\}.$$

The definition applies to every $x$, also to $x \notin C$. A definition as
$\partial \delta(\cdot \mid C)(x)$ would make it empty for $x \notin C$. With this definition
$N_C(x)$ is a pointed cone with no hypothesis, and the price is the hypothesis $x \in C$ in
`ConvexAnalysis.subdifferential_indicatorFn`. -/
def normalCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) (x : E) : Set F :=
  {y | ∀ z ∈ C, B (z - x) y ≤ 0}

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {C : Set E} {x : E} {y : F}

/-- Membership in the subdifferential: $y \in \partial f(x)$ if and only if
$f(x) + \langle z - x, y \rangle \le f(z)$ for all $z$. -/
@[simp] theorem mem_subdifferential :
    y ∈ subdifferential B f x ↔ ∀ z, f x + ((B (z - x) y : ℝ) : EReal) ≤ f z := Iff.rfl

/-- $(x, y)$ lies in the graph of $\partial f$ if and only if $y \in \partial f(x)$. -/
@[simp] theorem mem_subgradientRel : (x, y) ∈ subgradientRel B f ↔ y ∈ subdifferential B f x :=
  Iff.rfl

/-- Membership in the normal cone: $y \in N_C(x)$ if and only if $\langle z - x, y \rangle \le 0$
for all $z \in C$. -/
@[simp] theorem mem_normalCone : y ∈ normalCone B C x ↔ ∀ z ∈ C, B (z - x) y ≤ 0 := Iff.rfl

/-- The normal cone $N_C(x)$ as a pointed convex cone in $F$. It contains $0$ and is closed under
addition and under multiplication by nonnegative scalars, for every set $C$ and every point $x$. -/
def normalPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) (x : E) : PointedCone ℝ F where
  carrier := normalCone B C x
  zero_mem' z _ := by simp
  add_mem' {y₁ y₂} h₁ h₂ z hz := by
    rw [map_add]
    exact add_nonpos (h₁ z hz) (h₂ z hz)
  smul_mem' c y h z hz := by
    rw [LinearMap.map_smul_of_tower]
    exact smul_nonpos_of_nonneg_of_nonpos c.2 (h z hz)

/-- The underlying set of `ConvexAnalysis.normalPointedCone B C x` is $N_C(x)$. -/
@[simp] theorem coe_normalPointedCone (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (C : Set E) (x : E) :
    (normalPointedCone B C x : Set F) = normalCone B C x := rfl

/-- The subdifferential $\partial f(x)$ is a convex subset of $F$, for every $f$ and $x$. It is an
intersection of half-spaces of $F$, one for each $z$. -/
theorem convex_subdifferential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    Convex ℝ (subdifferential B f x) := by
  intro y₁ h₁ y₂ h₂ a b ha hb hab z
  have key : ∀ p q : ℝ, f x + (p : EReal) ≤ f z → q ≤ p → f x + (q : EReal) ≤ f z :=
    fun _ _ hp hqp => le_trans (add_le_add le_rfl (mod_cast hqp)) hp
  simp only [mem_subdifferential, map_add, map_smul, smul_eq_mul] at h₁ h₂ ⊢
  rcases le_total (B (z - x) y₁) (B (z - x) y₂) with h | h
  · refine key _ _ (h₂ z) ?_
    have h1 : a * B (z - x) y₁ ≤ a * B (z - x) y₂ := mul_le_mul_of_nonneg_left h ha
    have h2 : a * B (z - x) y₂ + b * B (z - x) y₂ = B (z - x) y₂ := by rw [← add_mul, hab, one_mul]
    linarith
  · refine key _ _ (h₁ z) ?_
    have h1 : b * B (z - x) y₂ ≤ b * B (z - x) y₁ := mul_le_mul_of_nonneg_left h hb
    have h2 : a * B (z - x) y₁ + b * B (z - x) y₁ = B (z - x) y₁ := by rw [← add_mul, hab, one_mul]
    linarith

/-- Let $f$ be proper. If $f$ has a subgradient at $x$, then $x \in \operatorname{dom} f$.

If $f(x) = +\infty$, the subgradient inequality would give $f(z) = +\infty$ for every $z$, which
properness excludes. -/
theorem mem_convexDom_of_mem_subdifferential (hp : ProperConvex f)
    (hy : y ∈ subdifferential B f x) :
    x ∈ convexDom f := by
  obtain ⟨z₀, hz₀⟩ := hp.convexDom_nonempty
  refine mem_convexDom.2 (lt_top_iff_ne_top.2 fun htop => ?_)
  have hle := hy z₀
  rw [htop, EReal.top_add_coe] at hle
  exact absurd (top_le_iff.1 hle) (mem_convexDom.1 hz₀).ne

/-- The **domain of the subdifferential**: $\operatorname{dom} \partial f = \{x \in E \mid \partial
f(x) \ne \emptyset\}$, the set of points at which $f$ has at least one subgradient. -/
def domSubdifferential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : Set E :=
  {x | (subdifferential B f x).Nonempty}

/-- $x \in \operatorname{dom} \partial f$ if and only if $\partial f(x)$ is nonempty. -/
@[simp] theorem mem_domSubdifferential :
    x ∈ domSubdifferential B f ↔ (subdifferential B f x).Nonempty := Iff.rfl

/-- For proper $f$, $\operatorname{dom} \partial f \subseteq \operatorname{dom} f$: a subgradient at
$x$ forces $f(x) < +\infty$. -/
theorem domSubdifferential_subset_convexDom
    (hp : ProperConvex f) : domSubdifferential B f ⊆ convexDom f := by
  rintro z ⟨y, hy⟩
  exact mem_convexDom_of_mem_subdifferential hp hy

end Defs

/-! ### Subgradients, conjugates and Fenchel's inequality -/

section Conj

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y : F}

/-- $y \in \partial f(x)$ if and only if $\langle \cdot, y \rangle - f$ attains its supremum at $x$:
$$\langle z, y \rangle - f(z) \le \langle x, y \rangle - f(x) \quad \text{for all } z \in E.$$
The statement holds for every $f$. -/
theorem mem_subdifferential_iff_forall_sub_le :
    y ∈ subdifferential B f x ↔ ∀ z, ((B z y : ℝ) : EReal) - f z ≤ ((B x y : ℝ) : EReal) - f x := by
  refine forall_congr' fun z => ?_
  rw [EReal.coe_sub_le_comm, EReal.coe_sub_coe_sub, map_sub, LinearMap.sub_apply, add_comm]

/-- $y \in \partial f(x)$ if and only if $f^*(y) \le \langle x, y \rangle - f(x)$, since the
supremum of $\langle \cdot, y \rangle - f$ is $f^*(y)$. The statement holds for every $f$. -/
theorem mem_subdifferential_iff_convexConj_le :
    y ∈ subdifferential B f x ↔ convexConj B f y ≤ ((B x y : ℝ) : EReal) - f x := by
  rw [mem_subdifferential_iff_forall_sub_le, convexConj_apply, iSup_le_iff]

/-- For every $f : E \to [-\infty, +\infty]$, $x \in E$ and $y \in F$,
$$y \in \partial f(x) \iff f^*(y) = \langle x, y \rangle - f(x).$$

This is equality in Fenchel's inequality, written in a form that never meets the undefined sum
$\infty - \infty$. The subtraction is the subtraction of `EReal`. -/
theorem mem_subdifferential_iff_convexConj_eq :
    y ∈ subdifferential B f x ↔ convexConj B f y = ((B x y : ℝ) : EReal) - f x :=
  ⟨fun h => le_antisymm (mem_subdifferential_iff_convexConj_le.1 h) (sub_le_convexConj B f x y),
    fun h => mem_subdifferential_iff_convexConj_le.2 h.le⟩

/-! ### Supergradients: the superdifferential of a concave function -/

/-- The **superdifferential** of $g : E \to [-\infty, +\infty]$ at $x$ with respect to the pairing
is the set of $y \in F$ with
$$g(z) \le g(x) + \langle z - x, y \rangle \quad \text{for all } z \in E.$$

This is `ConvexAnalysis.subdifferential` with the inequality reversed. [rockafellar1970convex]
writes $\partial g(x)$ for it when $g$ is concave. No concavity is assumed in the definition. -/
def superdifferential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (g : E → EReal) (x : E) : Set F :=
  {y | ∀ z, g z ≤ g x + ((B (z - x) y : ℝ) : EReal)}

variable {g : E → EReal}

/-- Membership in the superdifferential: $y$ is a supergradient of $g$ at $x$ if and only if
$g(z) \le g(x) + \langle z - x, y \rangle$ for all $z$. -/
@[simp] theorem mem_superdifferential :
    y ∈ superdifferential B g x ↔ ∀ z, g z ≤ g x + ((B (z - x) y : ℝ) : EReal) := Iff.rfl

/-- **The sign rule** for supergradients. For every $g : E \to [-\infty, +\infty]$, $x \in E$ and
$y \in F$, $y$ is a supergradient of $g$ at $x$ if and only if $-y$ is a subgradient of $-g$ at
$x$. -/
theorem mem_superdifferential_iff_neg_mem_subdifferential_neg :
    y ∈ superdifferential B g x ↔ -y ∈ subdifferential B (fun z => -(g z)) x := by
  refine forall_congr' fun z => ?_
  have hcoe : ((B (z - x) (-y) : ℝ) : EReal) = -((B (z - x) y : ℝ) : EReal) := by
    rw [map_neg, EReal.coe_neg]
  have hsum : -(g x) + -((B (z - x) y : ℝ) : EReal)
      = -(g x + ((B (z - x) y : ℝ) : EReal)) := by
    have h : -(g x + ((B (z - x) y : ℝ) : EReal)) = -(g x) + -((B (z - x) y : ℝ) : EReal) :=
      EReal.neg_add (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))
    exact h.symm
  change _ ↔ -(g x) + ((B (z - x) (-y) : ℝ) : EReal) ≤ -(g z)
  rw [hcoe, hsum, EReal.neg_le_neg_iff]

/-- $-y$ is a supergradient of $g$ at $x$ if and only if $y$ is a subgradient of $-g$ at $x$. -/
theorem neg_mem_superdifferential_iff :
    -y ∈ superdifferential B g x ↔ y ∈ subdifferential B (fun z => -(g z)) x := by
  rw [mem_superdifferential_iff_neg_mem_subdifferential_neg, neg_neg]

/-- $y$ is a supergradient of $g$ at $x$ if and only if $\langle \cdot, y \rangle - g$ attains its
infimum at $x$: $\langle x, y \rangle - g(x) \le \langle z, y \rangle - g(z)$ for all $z$. The
statement holds for every $g$. -/
theorem mem_superdifferential_iff_forall_le_sub :
    y ∈ superdifferential B g x ↔
      ∀ z, ((B x y : ℝ) : EReal) - g x ≤ ((B z y : ℝ) : EReal) - g z := by
  refine forall_congr' fun z => ?_
  rw [EReal.le_coe_sub_comm, EReal.coe_sub_coe_sub, map_sub, LinearMap.sub_apply,
    add_comm (g x)]

/-- $y$ is a supergradient of $g$ at $x$ if and only if $\langle x, y \rangle - g(x) \le g_*(y)$,
where $g_*$ is the concave conjugate `ConvexAnalysis.concaveConj`. The statement holds for every
$g$. -/
theorem mem_superdifferential_iff_le_concaveConj :
    y ∈ superdifferential B g x ↔ ((B x y : ℝ) : EReal) - g x ≤ concaveConj B g y := by
  rw [mem_superdifferential_iff_forall_le_sub, concaveConj_apply, le_iInf_iff]

/-- For every $g : E \to [-\infty, +\infty]$, $x \in E$ and $y \in F$, $y$ is a supergradient of $g$
at $x$ if and only if
$$g_*(y) = \langle x, y \rangle - g(x),$$
where $g_*(y) = \inf_z (\langle z, y \rangle - g(z))$ is the concave conjugate.

The concave conjugate is `ConvexAnalysis.concaveConj`. -/
theorem mem_superdifferential_iff_concaveConj_eq :
    y ∈ superdifferential B g x ↔ concaveConj B g y = ((B x y : ℝ) : EReal) - g x :=
  ⟨fun h => le_antisymm (concaveConj_le_sub B g x y)
      (mem_superdifferential_iff_le_concaveConj.1 h),
    fun h => mem_superdifferential_iff_le_concaveConj.2 h.ge⟩

/-- The superdifferential of $g$ at $x$ is a convex subset of $F$, for every $g$. -/
theorem convex_superdifferential : Convex ℝ (superdifferential B g x) := by
  have h : Convex ℝ (subdifferential B (fun z => -(g z)) x) :=
    convex_subdifferential B (fun z => -(g z)) x
  intro y₁ h₁ y₂ h₂ a b ha hb hab
  rw [mem_superdifferential_iff_neg_mem_subdifferential_neg] at h₁ h₂ ⊢
  have hneg : -(a • y₁ + b • y₂) = a • (-y₁) + b • (-y₂) := by
    rw [neg_add, smul_neg, smul_neg]
  rw [hneg]
  exact h h₁ h₂ ha hb hab

/-! ### Further conjugate criteria for subgradients -/

/-- $y \in \partial f(x)$ if and only if $f(x) + f^*(y) \le \langle x, y \rangle$. The statement
holds for every $f$: the addition of a real number is an order isomorphism of `EReal`, so no
$\infty - \infty$ arises. -/
theorem mem_subdifferential_iff_add_convexConj_le :
    y ∈ subdifferential B f x ↔ f x + convexConj B f y ≤ ((B x y : ℝ) : EReal) := by
  rw [mem_subdifferential_iff_convexConj_le, EReal.le_sub_iff_add_le
    (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)), add_comm]

/-- Let $f$ be proper. Then $y \in \partial f(x)$ if and only if **Fenchel's inequality** holds with
equality at $(x, y)$: $f(x) + f^*(y) = \langle x, y \rangle$.

Properness is needed. For $f \equiv +\infty$ every $y$ is a subgradient at every $x$, but
$f^* \equiv -\infty$, so $f(x) + f^*(y) = -\infty \ne \langle x, y \rangle$ (in `EReal`,
$+\infty + (-\infty) = -\infty$). -/
theorem ProperConvex.mem_subdifferential_iff_add_convexConj_eq (hp : ProperConvex f) :
    y ∈ subdifferential B f x ↔ f x + convexConj B f y = ((B x y : ℝ) : EReal) := by
  rw [mem_subdifferential_iff_add_convexConj_le]
  exact ⟨fun h => le_antisymm h (hp.le_add_convexConj x y), fun h => h.le⟩

/-- **Equivalent forms of subgradient membership.** Let $f : E \to [-\infty, +\infty]$ be proper,
$x \in E$ and $y \in F$. Then the following conditions are equivalent:

* (a) $y \in \partial f(x)$;
* (b) $\langle \cdot, y \rangle - f$ attains its supremum at $x$, that is, $\langle z, y
  \rangle - f(z) \le \langle x, y \rangle - f(x)$ for all $z$;
* (c) $f(x) + f^*(y) \le \langle x, y \rangle$;
* (d) $f(x) + f^*(y) = \langle x, y \rangle$.

This is Theorem 23.5 of [rockafellar1970convex], in the part that concerns $f$ alone. Convexity
of $f$ is not used. Properness is used only for the implication from (d) back to (a). -/
theorem ProperConvex.mem_subdifferential_tfae (hp : ProperConvex f) (x : E) (y : F) :
    List.TFAE [y ∈ subdifferential B f x,
      ∀ z, ((B z y : ℝ) : EReal) - f z ≤ ((B x y : ℝ) : EReal) - f x,
      f x + convexConj B f y ≤ ((B x y : ℝ) : EReal),
      f x + convexConj B f y = ((B x y : ℝ) : EReal)] := by
  tfae_have 1 ↔ 2 := mem_subdifferential_iff_forall_sub_le
  tfae_have 1 ↔ 3 := mem_subdifferential_iff_add_convexConj_le
  tfae_have 1 ↔ 4 := hp.mem_subdifferential_iff_add_convexConj_eq
  tfae_finish

/-- If $f^{**}(x) = f(x)$, then $x \in \partial f^*(y)$ if and only if $y \in \partial f(x)$. Here
$\partial f^*$ is taken with respect to the flipped pairing on $F \times E$. For a closed proper
convex $f$ the hypothesis holds at every $x$. -/
theorem mem_subdifferential_convexConj_iff (h : convexBiconj B f x = f x) :
    x ∈ subdifferential B.flip (convexConj B f) y ↔ y ∈ subdifferential B f x := by
  have h' : convexConj B.flip (convexConj B f) x = f x := h
  rw [mem_subdifferential_iff_add_convexConj_le, mem_subdifferential_iff_add_convexConj_le,
    LinearMap.flip_apply, h', add_comm]

/-- If $f$ has a subgradient at $x$, then $f^{**}(x) = f(x)$. Neither topology nor convexity is
needed. -/
theorem convexBiconj_eq_of_mem_subdifferential
    (hy : y ∈ subdifferential B f x) : convexBiconj B f x = f x := by
  refine le_antisymm (convexBiconj_le B f x) ?_
  have h := sub_le_convexConj B.flip (convexConj B f) y x
  rwa [LinearMap.flip_apply, mem_subdifferential_iff_convexConj_eq.1 hy, EReal.coe_sub_coe_sub,
      sub_self,
    EReal.coe_zero, zero_add] at h

/-- Let $f : E \to [-\infty, +\infty]$, and let $x \in E$ with $f(x)$ finite. If $f$ has a
subgradient $y$ at $x$, then $f$ is proper.

The subgradient inequality gives a finite affine minorant of $f$, which excludes the value
$-\infty$, and $x \in \operatorname{dom} f$. Properness here is `ConvexAnalysis.ProperConvex`,
which does not include convexity. -/
theorem properConvex_of_mem_subdifferential (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    (hy : y ∈ subdifferential B f x) : ProperConvex f := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  refine ⟨⟨x, lt_top_iff_ne_top.2 ht⟩, fun z hz => ?_⟩
  have h := hy z
  rw [hr, hz, ← EReal.coe_add] at h
  exact EReal.coe_ne_bot _ (le_bot_iff.1 h)

/-- If $f(x)$ is finite and $\partial f(x)$ is nonempty, then $f$ is proper. -/
theorem properConvex_of_subdifferential_nonempty (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    (h : (subdifferential B f x).Nonempty) : ProperConvex f :=
  h.elim fun _ hy => properConvex_of_mem_subdifferential ht hb hy

/-- A proper function has no subgradients off its effective domain: if
$x \notin \operatorname{dom} f$, then $\partial f(x) = \emptyset$. -/
theorem subdifferential_eq_empty_of_notMem_convexDom (hp : ProperConvex f) (hx : x ∉ convexDom f) :
    subdifferential B f x = ∅ := by
  obtain ⟨z, hz⟩ := hp.convexDom_nonempty
  have hfx : f x = ⊤ := by
    by_contra hc
    exact hx (lt_top_iff_ne_top.2 hc)
  refine eq_empty_of_forall_notMem fun y hy => absurd (hy z) (not_le.2 ?_)
  rw [hfx, EReal.top_add_coe]
  exact hz

end Conj

/-! ### Indicator functions, normal cones and polar cones -/

section Indicator

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {C : Set E} {x : E} {y : F}

/-- Let $C \subseteq E$ and $x \in C$. The subdifferential of the indicator function of $C$ at $x$
is the normal cone:
$$\partial \delta(\cdot \mid C)(x) = N_C(x).$$
-/
theorem subdifferential_indicatorFn (hx : x ∈ C) :
    subdifferential B (indicatorFn C) x = normalCone B C x := by
  ext y
  simp only [mem_subdifferential, indicatorFn_of_mem hx, zero_add, mem_normalCone]
  refine ⟨fun h z hz => ?_, fun h z => ?_⟩
  · have hz' := h z
    rw [indicatorFn_of_mem hz] at hz'
    exact_mod_cast hz'
  · by_cases hz : z ∈ C
    · rw [indicatorFn_of_mem hz]
      exact_mod_cast h z hz
    · rw [indicatorFn_of_notMem hz]
      exact le_top

/-- If $C$ is nonempty and $x \notin C$, then $\delta(\cdot \mid C)$ has no subgradient at $x$. -/
theorem subdifferential_indicatorFn_of_notMem (hC : C.Nonempty) (hx : x ∉ C) :
    subdifferential B (indicatorFn C) x = ∅ :=
  subdifferential_eq_empty_of_notMem_convexDom ⟨by rwa [convexDom_indicatorFn],
      indicatorFn_ne_bot C⟩
    (by rwa [convexDom_indicatorFn])

/-- For nonempty $C$, $y \in \partial \delta(\cdot \mid C)(x)$ if and only if $x \in C$ and
$y \in N_C(x)$. -/
theorem mem_subdifferential_indicatorFn_iff (hC : C.Nonempty) :
    y ∈ subdifferential B (indicatorFn C) x ↔ x ∈ C ∧ y ∈ normalCone B C x := by
  by_cases hx : x ∈ C
  · rw [subdifferential_indicatorFn hx]
    exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  · rw [subdifferential_indicatorFn_of_notMem hC hx]
    exact ⟨fun h => absurd h (notMem_empty y), fun h => absurd h.1 hx⟩

/-- Let $K \subseteq E$ be a pointed convex cone. Then $y \in \partial \delta(\cdot \mid K)(x)$ if
and only if $x \in K$, $y$ lies in the polar cone $K^\circ = N_K(0)$, and
$\langle x, y \rangle = 0$.

The classical proof assumes $K$ closed and uses $\delta(\cdot \mid K)^* = \delta(\cdot \mid
K^\circ)$. The direct proof puts $z = 0$ and $z = 2x$ into the subgradient inequality and needs
no topology, so $K$ is arbitrary here. -/
theorem mem_subdifferential_indicatorFn_pointedCone (K : PointedCone ℝ E) :
    y ∈ subdifferential B (indicatorFn (K : Set E)) x ↔
      x ∈ K ∧ y ∈ normalCone B (K : Set E) 0 ∧ B x y = 0 := by
  rw [mem_subdifferential_indicatorFn_iff ⟨0, K.zero_mem⟩]
  simp only [mem_normalCone, sub_zero, SetLike.mem_coe]
  constructor
  · rintro ⟨hx, h⟩
    have h0 : B (0 - x) y ≤ 0 := h 0 K.zero_mem
    have h2 : B (x + x - x) y ≤ 0 := h (x + x) (K.add_mem hx hx)
    rw [zero_sub, map_neg, LinearMap.neg_apply] at h0
    rw [add_sub_cancel_right] at h2
    have hzero : B x y = 0 := le_antisymm h2 (by linarith)
    refine ⟨hx, fun z hz => ?_, hzero⟩
    have hz' := h z hz
    rwa [map_sub, LinearMap.sub_apply, hzero, sub_zero] at hz'
  · rintro ⟨hx, hpol, hzero⟩
    refine ⟨hx, fun z hz => ?_⟩
    rw [map_sub, LinearMap.sub_apply, hzero, sub_zero]
    exact hpol z hz

end Indicator

/-! ### Closedness of the subdifferential -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ}

omit [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] in
/-- For $u \in [-\infty, +\infty]$, the map $t \mapsto u + t$ from $\mathbb{R}$ to
$[-\infty, +\infty]$ is continuous.

The map $v \mapsto u + v$ on all of $[-\infty, +\infty]$ is not continuous when $u = +\infty$,
because $+\infty + (-\infty) = -\infty$ in `EReal`. The restriction to real arguments avoids
this. -/
theorem continuous_add_coe (u : EReal) : Continuous fun t : ℝ => u + (t : EReal) := by
  induction u with
  | bot => simpa only [EReal.bot_add] using continuous_const
  | coe r =>
    have h : Continuous fun t : ℝ => (r + t : ℝ) := by fun_prop
    simpa only [← EReal.coe_add] using continuous_coe_real_ereal.comp' h
  | top => simpa only [EReal.top_add_coe] using continuous_const

/-- Let $F$ carry a topology in which every linear functional
$\langle z, \cdot \rangle : F \to \mathbb{R}$ is continuous. Then $\partial f(x)$ is closed in
$F$, for every $f$ and $x$.

The hypothesis is `ConvexAnalysis.IsContinuousPairing B.flip`. It holds in $\mathbb{R}^n$, and
it is also a hypothesis of `ConvexAnalysis.closedConvex_convexConj`. -/
theorem isClosed_subdifferential [IsContinuousPairing B.flip] (f : E → EReal) (x : E) :
    IsClosed (subdifferential B f x) := by
  rw [show subdifferential B f x = ⋂ z : E, {y | f x + ((B (z - x) y : ℝ) : EReal) ≤ f z} from
    Set.ext fun y => by simp]
  exact isClosed_iInter fun z =>
    isClosed_Iic.preimage ((continuous_add_coe (f x)).comp (continuous_pairing B.flip (z - x)))

end Closed

/-! ### The directional derivative -/

section DirDeriv

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x y : E}

/-- The **one-sided directional derivative** of $f : E \to [-\infty, +\infty]$ at $x$ in the
direction $y$:
$$f'(x; y) = \inf_{\lambda > 0} \frac{f(x + \lambda y) - f(x)}{\lambda}.$$

For convex $f$ with $f(x)$ finite, the difference quotient is nondecreasing in $\lambda$
(`ConvexAnalysis.monotoneOn_sub_div`), so the infimum is the limit as $\lambda \downarrow 0$,
the classical definition. The arithmetic is that of `EReal`. If $f(x) = +\infty$, the quotient
is $-\infty$ for every $\lambda$, so $f'(x; y) = -\infty$ in every direction. -/
noncomputable def dirDeriv (f : E → EReal) (x y : E) : EReal :=
  ⨅ a ∈ Set.Ioi (0 : ℝ), (f (x + a • y) - f x) / (a : EReal)

/-- The defining formula: $f'(x; y) = \inf_{\lambda > 0} (f(x + \lambda y) - f(x)) / \lambda$. -/
theorem dirDeriv_apply (f : E → EReal) (x y : E) :
    dirDeriv f x y = ⨅ a ∈ Set.Ioi (0 : ℝ), (f (x + a • y) - f x) / (a : EReal) := rfl

/-- The directional derivative is a lower bound for every difference quotient: $f'(x; y) \le (f(x +
\lambda y) - f(x)) / \lambda$ for every $\lambda > 0$. -/
theorem dirDeriv_le (f : E → EReal) (x y : E) {a : ℝ} (ha : 0 < a) :
    dirDeriv f x y ≤ (f (x + a • y) - f x) / (a : EReal) :=
  iInf₂_le (f := fun (b : ℝ) (_ : b ∈ Set.Ioi (0 : ℝ)) => (f (x + b • y) - f x) / (b : EReal)) a ha

/-- If $c \le (f(x + \lambda y) - f(x)) / \lambda$ for every $\lambda > 0$, then $c \le f'(x; y)$.
-/
theorem le_dirDeriv {c : EReal} (h : ∀ a : ℝ, 0 < a → c ≤ (f (x + a • y) - f x) / (a : EReal)) :
    c ≤ dirDeriv f x y :=
  le_iInf₂ (f := fun (b : ℝ) (_ : b ∈ Set.Ioi (0 : ℝ)) => (f (x + b • y) - f x) / (b : EReal)) h

/-- $f'(x; y) < c$ if and only if $(f(x + \lambda y) - f(x)) / \lambda < c$ for some $\lambda > 0$.
-/
theorem dirDeriv_lt_iff {c : EReal} :
    dirDeriv f x y < c ↔ ∃ a : ℝ, 0 < a ∧ (f (x + a • y) - f x) / (a : EReal) < c := by
  simp only [dirDeriv, iInf_lt_iff, Set.mem_Ioi, exists_prop]

/-- If $f(x)$ is finite, then $f'(x; 0) = 0$. -/
theorem dirDeriv_zero (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : dirDeriv f x 0 = 0 := by
  have h : ∀ a : ℝ, 0 < a → (f (x + a • (0 : E)) - f x) / (a : EReal) = 0 := fun a _ => by
    rw [smul_zero, add_zero, EReal.sub_self ht hb, EReal.zero_div]
  exact le_antisymm ((dirDeriv_le f x 0 one_pos).trans (h 1 one_pos).le)
    (le_dirDeriv fun a ha => (h a ha).ge)

/-- For every $f : E \to [-\infty, +\infty]$ and $x \in E$, the directional derivative
$f'(x; \cdot)$ is positively homogeneous: $f'(x; c y) = c \, f'(x; y)$ for all $c > 0$ and
$y \in E$.

Unlike the other basic properties of $f'(x; \cdot)$, this one needs no hypothesis, because it is
the reindexing $\lambda \mapsto \lambda c$ of the defining infimum. Positive homogeneity is
`ConvexAnalysis.PosHomogeneous`. -/
theorem posHomogeneous_dirDeriv (f : E → EReal) (x : E) : PosHomogeneous (dirDeriv f x) := by
  intro c hc y
  have hterm : ∀ a : ℝ, 0 < a →
      (f (x + a • (c • y)) - f x) / (a : EReal)
        = (c : EReal) * ((f (x + (a * c) • y) - f x) / ((a * c : ℝ) : EReal)) := by
    intro a _
    rw [smul_smul, div_eq_mul_inv, div_eq_mul_inv, ← EReal.coe_inv, ← EReal.coe_inv,
      ← mul_assoc, mul_comm (c : EReal) _, mul_assoc, ← EReal.coe_mul,
      show c * (a * c)⁻¹ = a⁻¹ from by field_simp]
  rw [dirDeriv_apply, dirDeriv_apply, iInf_subtype', iInf_subtype', EReal.coe_mul_iInf hc]
  refine le_antisymm (le_iInf fun b => ?_) (le_iInf fun a => ?_)
  · have hb : (0 : ℝ) < (b : ℝ) / c := div_pos b.2 hc
    refine le_trans (iInf_le _ (⟨(b : ℝ) / c, hb⟩ : Set.Ioi (0 : ℝ))) ?_
    rw [hterm _ hb, div_mul_cancel₀ (b : ℝ) hc.ne']
  · rw [hterm _ a.2]
    exact iInf_le _ (⟨(a : ℝ) * c, mul_pos a.2 hc⟩ : Set.Ioi (0 : ℝ))

/-- Let $f : E \to [-\infty, +\infty]$ be convex and let $f(x) = r$ be a real number. Then for every
$y \in E$ the difference quotient
$$\lambda \mapsto \frac{f(x + \lambda y) - f(x)}{\lambda}$$
is nondecreasing on $(0, \infty)$.

This makes the infimum that defines `ConvexAnalysis.dirDeriv` the limit as
$\lambda \downarrow 0$. -/
theorem monotoneOn_sub_div (hf : ConvexFn f) {r : ℝ} (hr : f x = (r : EReal)) (y : E) :
    MonotoneOn (fun a : ℝ => (f (x + a • y) - f x) / (a : EReal)) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hbne : b ≠ 0 := hb.ne'
  simp only [hr]
  refine EReal.le_of_forall_coe_le fun s hs => ?_
  rw [EReal.sub_div_le_coe_iff hb] at hs
  rw [EReal.sub_div_le_coe_iff ha]
  have ht0 : (0 : ℝ) ≤ a / b := (div_pos ha hb).le
  have ht1 : (0 : ℝ) ≤ 1 - a / b := by
    have : a / b ≤ 1 := (div_le_one hb).2 hab
    linarith
  have hvec : (1 - a / b) • x + (a / b) • (x + b • y) = x + a • y := by
    rw [smul_add, smul_smul, div_mul_cancel₀ a hbne, sub_smul, one_smul]
    abel
  have hcomb := hf.epi_combo (le_of_eq hr) hs ht1 ht0 (by ring)
  have hscal : (1 - a / b) * r + a / b * (r + s * b) = r + s * a := by field_simp; ring
  rw [hvec, hscal] at hcomb
  exact hcomb

/-- Let $f$ be convex, let $f(x) = r$ be real, and let $m$ be a real number with $f'(x; y) < m$.
Then there is $\lambda_0 > 0$ such that $f(x + \lambda y) \le r + m \lambda$ for all
$\lambda \in (0, \lambda_0]$. -/
theorem exists_le_of_dirDeriv_lt (hf : ConvexFn f) {r : ℝ} (hr : f x = (r : EReal)) {y : E}
    {m : ℝ} (h : dirDeriv f x y < (m : EReal)) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ → f (x + a • y) ≤ ((r + m * a : ℝ) : EReal) := by
  obtain ⟨a₀, ha₀, hlt⟩ := dirDeriv_lt_iff.1 h
  refine ⟨a₀, ha₀, fun a ha hle => ?_⟩
  rw [← EReal.sub_div_le_coe_iff ha, ← hr]
  exact le_trans (monotoneOn_sub_div hf hr y ha ha₀ hle) hlt.le

/-- Let $f : E \to [-\infty, +\infty]$ be convex, and let $f(x)$ be finite. Then $f'(x; \cdot)$ is a
convex function on $E$. -/
theorem convexFn_dirDeriv (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    ConvexFn (dirDeriv f x) := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  refine convexFn_of_epi_combo fun y₁ y₂ μ ν h₁ h₂ s t hs ht' hst => ?_
  rcases hs.eq_or_lt with hs0 | hs0
  · subst hs0
    have : t = 1 := by linarith
    subst this
    simpa using h₂
  rcases ht'.eq_or_lt with ht0 | ht0
  · subst ht0
    have : s = 1 := by linarith
    subst this
    simpa using h₁
  refine EReal.le_of_forall_lt_iff_le.1 fun p hp => le_of_lt ?_
  replace hp := EReal.coe_lt_coe_iff.1 hp
  obtain ⟨e, he, hesum⟩ : ∃ e : ℝ, 0 < e ∧ s * μ + t * ν + e = p - e :=
    ⟨(p - (s * μ + t * ν)) / 2, by linarith, by ring⟩
  have h1 : dirDeriv f x y₁ < ((μ + e : ℝ) : EReal) :=
    lt_of_le_of_lt h₁ (mod_cast lt_add_of_pos_right μ he)
  have h2 : dirDeriv f x y₂ < ((ν + e : ℝ) : EReal) :=
    lt_of_le_of_lt h₂ (mod_cast lt_add_of_pos_right ν he)
  obtain ⟨a₁, ha₁, H₁⟩ := exists_le_of_dirDeriv_lt hf hr h1
  obtain ⟨a₂, ha₂, H₂⟩ := exists_le_of_dirDeriv_lt hf hr h2
  have ha : 0 < min a₁ a₂ := lt_min ha₁ ha₂
  have hA := H₁ _ ha (min_le_left a₁ a₂)
  have hB := H₂ _ ha (min_le_right a₁ a₂)
  have hvec : s • (x + min a₁ a₂ • y₁) + t • (x + min a₁ a₂ • y₂)
      = x + min a₁ a₂ • (s • y₁ + t • y₂) := by
    match_scalars
    · linear_combination hst
    · ring
    · ring
  have hcomb := hf.epi_combo hA hB hs ht' hst
  rw [hvec, show s * (r + (μ + e) * min a₁ a₂) + t * (r + (ν + e) * min a₁ a₂)
      = r + (p - e) * min a₁ a₂ from by
    linear_combination (r + min a₁ a₂ * e) * hst + min a₁ a₂ * hesum] at hcomb
  calc dirDeriv f x (s • y₁ + t • y₂)
      ≤ (f (x + min a₁ a₂ • (s • y₁ + t • y₂)) - f x) / ((min a₁ a₂ : ℝ) : EReal) :=
        dirDeriv_le _ _ _ ha
    _ ≤ ((p - e : ℝ) : EReal) := by
        rw [hr]
        exact (EReal.sub_div_le_coe_iff ha _).2 hcomb
    _ < (p : EReal) := mod_cast sub_lt_self p he

/-- Let $f$ be convex with $f(x)$ finite. Then $-f'(x; -y) \le f'(x; y)$ for every $y$.

No hypothesis $f'(x; \cdot) \ne -\infty$ appears, although
`ConvexAnalysis.PosHomogeneous.neg_le` has one. The value $-\infty$ does occur for
$f'(x; \cdot)$. -/
theorem neg_dirDeriv_neg_le (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) (y : E) :
    -dirDeriv f x (-y) ≤ dirDeriv f x y := by
  have hconv := convexFn_dirDeriv hf ht hb
  have hzero := dirDeriv_zero ht hb
  have main : ∀ m n : ℝ, dirDeriv f x (-y) ≤ (m : EReal) → dirDeriv f x y ≤ (n : EReal) →
      (0 : ℝ) ≤ m + n := by
    intro m n hm hn
    have hc := hconv.epi_combo hm hn (a := 1 / 2) (b := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num)
    rw [show ((1 : ℝ) / 2) • (-y) + ((1 : ℝ) / 2) • y = (0 : E) from by
      rw [smul_neg, neg_add_cancel], hzero, ← EReal.coe_zero,
      EReal.coe_le_coe_iff] at hc
    linarith
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨n, hn1, hn2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have h3 : dirDeriv f x (-y) < ((-n : ℝ) : EReal) := by
    rw [EReal.coe_neg]
    exact EReal.lt_neg_comm.1 hn2
  obtain ⟨m, hm1, hm2⟩ := EReal.exists_between_coe_real h3
  replace hm2 := EReal.coe_lt_coe_iff.1 hm2
  have := main m n hm1.le hn1.le
  linarith

end DirDeriv

/-! ### The subdifferential and the directional derivative -/

section DirDerivSubdifferential

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E} {y : F}

/-- Let $f : E \to [-\infty, +\infty]$, and let $x \in E$ with $f(x)$ finite. Then
$y \in \partial f(x)$ if and only if
$$\langle v, y \rangle \le f'(x; v) \quad \text{for all } v \in E.$$

This is part of Theorem 23.2 of [rockafellar1970convex]. Neither convexity of $f$ nor the
monotonicity of the difference quotient is used. -/
theorem mem_subdifferential_iff_le_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    y ∈ subdifferential B f x ↔ ∀ v : E, ((B v y : ℝ) : EReal) ≤ dirDeriv f x v := by
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hb (lt_top_iff_ne_top.2 ht)
  constructor
  · intro h v
    refine le_dirDeriv fun a ha => ?_
    rw [hr, EReal.coe_le_sub_div_iff ha]
    have hv := h (x + a • v)
    rw [add_sub_cancel_left, hr, ← EReal.coe_add, map_smul, LinearMap.smul_apply,
      smul_eq_mul] at hv
    rwa [mul_comm (B v y) a]
  · intro h z
    have h1 := dirDeriv_le f x (z - x) one_pos
    rw [one_smul, show x + (z - x) = z from by abel] at h1
    have h2 := (h (z - x)).trans h1
    rw [hr, EReal.coe_le_sub_div_iff one_pos, mul_one, EReal.coe_add] at h2
    rw [hr]
    exact h2

/-- If $f(x)$ is finite, then the set $\{y \mid \langle v, y \rangle \le f'(x; v) \text{ for all }
v\}$ (`ConvexAnalysis.supportSet`) of $f'(x; \cdot)$ is $\partial f(x)$. -/
theorem supportSet_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    supportSet B (dirDeriv f x) = subdifferential B f x :=
  Set.ext fun _ => (mem_subdifferential_iff_le_dirDeriv ht hb).symm

/-- Let $f : E \to [-\infty, +\infty]$, and let $x \in E$ with $f(x)$ finite. Then the conjugate of
$f'(x; \cdot)$ is the indicator function of $\partial f(x)$:
$$(f'(x; \cdot))^* = \delta(\cdot \mid \partial f(x)).$$

Neither convexity of $f$ nor any topology is needed. -/
theorem convexConj_dirDeriv (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    convexConj B (dirDeriv f x) = indicatorFn (subdifferential B f x) := by
  rw [convexConj_eq_indicatorFn_of_posHomogeneous (posHomogeneous_dirDeriv f x)
      ⟨0, by rw [dirDeriv_zero ht hb]; simp⟩,
    supportSet_dirDeriv ht hb]

end DirDerivSubdifferential

/-!
### Conjugate subdifferentials, and the closure of the directional derivative

The results of this section use the Fenchel–Moreau theorem, so they carry the hypotheses on the
pairing of `ConvexAnalysis.convexBiconj_eq_convexCl`.
-/

section FenchelMoreau

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}
  {x : E} {y : F}

/-- Let $E$ be a topological additive group, and let every $\langle \cdot, y \rangle$ be continuous
on $E$. If $(\operatorname{cl} f)(x) = f(x)$, then $\partial (\operatorname{cl} f)(x) = \partial
f(x)$.

The proof uses `ConvexAnalysis.convexConj_convexCl`. -/
theorem mem_subdifferential_convexCl_iff [IsContinuousPairing B] (hx : convexCl f x = f x) :
    y ∈ subdifferential B (convexCl f) x ↔ y ∈ subdifferential B f x := by
  rw [mem_subdifferential_iff_convexConj_le, mem_subdifferential_iff_convexConj_le,
      convexConj_convexCl, hx]

variable [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- Let $E$ be a locally convex topological vector space whose pairing with $F$ is compatible with
the topology (`ConvexAnalysis.IsCompatiblePairing`). If $f$ is closed and convex, then
$x \in \partial f^*(y)$ if and only if $y \in \partial f(x)$. -/
theorem mem_subdifferential_convexConj_iff_of_closedConvex [IsCompatiblePairing B] (hf : ConvexFn f)
    (hc : ClosedConvex f) :
    x ∈ subdifferential B.flip (convexConj B f) y ↔ y ∈ subdifferential B f x :=
  mem_subdifferential_convexConj_iff (congrFun (convexBiconj_eq_self hf hc) x)

/-- Let $E$ be a locally convex topological vector space whose pairing with $F$ is compatible with
the topology, and let $f : E \to [-\infty, +\infty]$ be closed and convex. Then $\partial f^*$
is the inverse of $\partial f$ as a multivalued map: the graph of $\partial f^*$ is the set of
pairs $(y, x)$ with $(x, y)$ in the graph of $\partial f$.

The subdifferential $\partial f^*$ is taken with respect to the flipped pairing `B.flip`, and
the inverse is `SetRel.inv`. A compatible pairing is `ConvexAnalysis.IsCompatiblePairing`: every
$\langle \cdot, y \rangle$ is continuous on $E$, and every continuous linear functional on $E$
has this form. -/
theorem subgradientRel_convexConj_eq_inv [IsCompatiblePairing B] (hf : ConvexFn f)
    (hc : ClosedConvex f) :
    subgradientRel B.flip (convexConj B f) = (subgradientRel B f).inv := by
  ext ⟨y, x⟩
  simp only [SetRel.mem_inv, mem_subgradientRel]
  exact mem_subdifferential_convexConj_iff_of_closedConvex hf hc

/-- For a convex $f$ that has a subgradient at $x$, $(\operatorname{cl} f)(x) = f(x)$. The pairing
is compatible with the locally convex topology of $E$. -/
theorem convexCl_eq_of_mem_subdifferential [IsCompatiblePairing B] (hf : ConvexFn f)
    (hy : y ∈ subdifferential B f x) : convexCl f x = f x := by
  rw [← congrFun (convexBiconj_eq_convexCl (B := B) hf) x]
  exact convexBiconj_eq_of_mem_subdifferential hy

/-- Let $E$ be a locally convex topological vector space whose pairing with $F$ is compatible with
the topology, and let $f : E \to [-\infty, +\infty]$ be convex. If $\partial f(x)$ is nonempty,
then
$$\partial (\operatorname{cl} f)(x) = \partial f(x).$$

A compatible pairing is `ConvexAnalysis.IsCompatiblePairing`. -/
theorem subdifferential_convexCl [IsCompatiblePairing B] (hf : ConvexFn f)
    (hy : y ∈ subdifferential B f x) : subdifferential B (convexCl f) x = subdifferential B f x :=
  Set.ext fun _ => mem_subdifferential_convexCl_iff (convexCl_eq_of_mem_subdifferential hf hy)

/-- Let $C \subseteq E$ be nonempty, closed and convex, with the pairing compatible with the locally
convex topology of $E$. The subgradients at $y$ of the conjugate $\delta(\cdot \mid C)^*$ are
the points of $C$ at which $\langle \cdot, y \rangle$ attains its maximum over $C$:
$$\partial \delta(\cdot \mid C)^*(y) = \{x \in C \mid \langle z, y \rangle \le \langle x, y
  \rangle \text{ for all } z \in C\}.$$
-/
theorem subdifferential_convexConj_indicatorFn [IsCompatiblePairing B] {C : Set E} (hC : IsClosed C)
    (hCc : Convex ℝ C) (hCne : C.Nonempty) (y : F) :
    subdifferential B.flip (convexConj B (indicatorFn C)) y = {x ∈ C | ∀ z ∈ C, B z y ≤ B x y} := by
  ext x
  have hbi := congrFun (convexBiconj_eq_self (B := B) (convexFn_indicatorFn.2 hCc)
    (closedConvex_indicatorFn hC)) x
  rw [mem_subdifferential_convexConj_iff hbi, mem_subdifferential_indicatorFn_iff hCne,
      Set.mem_sep_iff]
  refine and_congr_right fun _ => ?_
  simp only [mem_normalCone]
  exact forall₂_congr fun z _ => by rw [map_sub, LinearMap.sub_apply, sub_nonpos]

/-- Let $E$ be a locally convex topological vector space whose pairing with $F$ is compatible with
the topology, and let $C \subseteq E$ be nonempty, closed and convex. Then the subdifferential
of the support function $\delta^*(\cdot \mid C)$ at $y \in F$ is the set of points of $C$ at
which $\langle \cdot, y \rangle$ attains its maximum over $C$:
$$\partial \delta^*(\cdot \mid C)(y) = \{x \in C \mid \langle z, y \rangle \le \langle x, y
  \rangle \text{ for all } z \in C\}.$$

The support function is `ConvexAnalysis.supportFn`, and the subdifferential is taken with
respect to the flipped pairing `B.flip`. -/
theorem subdifferential_supportFn [IsCompatiblePairing B] {C : Set E} (hC : IsClosed C)
    (hCc : Convex ℝ C) (hCne : C.Nonempty) (y : F) :
    subdifferential B.flip (supportFn B C) y = {x ∈ C | ∀ z ∈ C, B z y ≤ B x y} := by
  rw [supportFn_eq_convexConj_indicatorFn]
  exact subdifferential_convexConj_indicatorFn hC hCc hCne y

/-- Let $E$ be a locally convex topological vector space whose pairing with $F$ is compatible with
the topology, let $f : E \to [-\infty, +\infty]$ be convex, and let $f(x)$ be finite. Then the
closure of $f'(x; \cdot)$ is the support function of $\partial f(x)$:
$$\operatorname{cl} f'(x; \cdot) = \delta^*(\cdot \mid \partial f(x)), \qquad \text{that is,}
  \qquad (\operatorname{cl} f'(x; \cdot))(v) = \sup_{y \in \partial f(x)} \langle v, y
  \rangle.$$

This is part of Theorem 23.2 of [rockafellar1970convex]. The proof combines
`ConvexAnalysis.convexConj_dirDeriv` with the Fenchel–Moreau theorem. -/
theorem convexCl_dirDeriv [IsCompatiblePairing B] (hf : ConvexFn f) (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    convexCl (dirDeriv f x) = supportFn B.flip (subdifferential B f x) := by
  rw [supportFn_eq_convexConj_indicatorFn, ← convexConj_dirDeriv ht hb]
  exact (convexBiconj_eq_convexCl (convexFn_dirDeriv hf ht hb)).symm

end FenchelMoreau

end ConvexAnalysis
