/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Subdifferential.Bounded
import Numlib.Analysis.Convex.Subdifferential.Convergence
import Numlib.Analysis.Convex.Subdifferential.Integral
import Numlib.Analysis.Convex.Subdifferential.Primitive
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar, Section 24: Differential continuity and monotonicity

This module formalizes Section 24 of [rockafellar1970convex]: the continuity and monotonicity
properties of the subdifferential mapping $\partial f$ of a convex function $f$. On the real line,
the right and left derivatives $f'_+$ and $f'_-$ of a closed proper convex function are
nondecreasing, interlaced and one-sidedly continuous, and $\partial f(x) = [f'_-(x), f'_+(x)]$
(Theorem 24.1). Every nondecreasing function is, up to its jumps, the derivative of a closed proper
convex function, unique up to an additive constant (Theorem 24.2), and the graphs of the mappings
$\partial f$ on the line are exactly the complete nondecreasing curves in $\mathbb{R}^2$ (Theorem
24.3).

On $\mathbb{R}^n$, the graph of $\partial f$ is closed (Theorem 24.4), directional derivatives are
upper semicontinuous jointly in the point and the direction, also along a convergent sequence of
functions (Theorem 24.5 and Corollary 24.5.1) and along an approach to a boundary point of
$\operatorname{dom} f$ (Theorem 24.6), and $\partial f$ is locally bounded on
$\operatorname{int}(\operatorname{dom} f)$ (Theorem 24.7). A multivalued mapping is contained in
some $\partial f$ if and only if it is cyclically monotone (Theorem 24.8), and the mappings
$\partial f$ are exactly the maximal cyclically monotone mappings (Theorem 24.9). The source warns
that maximality among the cyclically monotone mappings is not maximality among the monotone
mappings: Corollary 31.5.2, the maximal monotonicity of $\partial f$, does not follow from Theorem
24.9 together with the fact that a cyclically monotone mapping is monotone. On the line the two
classes coincide. The proofs specialize `Numlib.Analysis.Convex.Subdifferential.Primitive`,
`Numlib.Analysis.Convex.Subdifferential.Convergence`,
`Numlib.Analysis.Convex.Subdifferential.Bounded` and
`Numlib.Analysis.Convex.Subdifferential.Integral`.

## Main definitions

* `Rockafellar.IsCompleteNonDecreasingCurve`: a complete nondecreasing curve in $\mathbb{R}^2$, a
  maximal totally ordered subset for the coordinatewise order.
* `Rockafellar.subdifferentialNormal`: the set $\partial f(x)_y$ of subgradients
  $x^* \in \partial f(x)$ at which $y$ is normal to $\partial f(x)$.

## Main results

* Theorem 24.1, `Rockafellar.theorem_24_1_monotone_rightDeriv`,
  `Rockafellar.theorem_24_1_monotone_leftDeriv`, `Rockafellar.theorem_24_1_finite_iff`,
  `Rockafellar.theorem_24_1_chain`, `Rockafellar.theorem_24_1_tendsto_rightDeriv_Ioi`,
  `Rockafellar.theorem_24_1_tendsto_rightDeriv_Iio`,
  `Rockafellar.theorem_24_1_tendsto_leftDeriv_Ioi`,
  `Rockafellar.theorem_24_1_tendsto_leftDeriv_Iio`: $f'_+$ and $f'_-$ are nondecreasing, finite
  exactly on $\operatorname{int}(\operatorname{dom} f)$, interlaced, and one-sidedly continuous.
* `Rockafellar.theorem_24_1_subdifferential`: the remark after Theorem 24.1, $\partial f(x) = \{x^*
  \mid f'_-(x) \le x^* \le f'_+(x)\}$.
* Theorem 24.2, `Rockafellar.theorem_24_2`, `Rockafellar.theorem_24_2_exists`,
  `Rockafellar.theorem_24_2_unique`: a nondecreasing $\varphi$ finite somewhere satisfies
  $f'_- \le \varphi \le f'_+$ for a closed proper convex $f$, unique up to an additive constant.
* Corollary 24.2.1, `Rockafellar.corollary_24_2_1_rightDeriv`,
  `Rockafellar.corollary_24_2_1_leftDeriv`: $f(y) - f(x) = \int_x^y f'_+(t)\,dt = \int_x^y
  f'_-(t)\,dt$ on $\operatorname{int}(\operatorname{dom} f)$.
* Theorem 24.3, `Rockafellar.theorem_24_3`, `Rockafellar.theorem_24_3_unique`,
  `Rockafellar.theorem_24_3_subgradientRel_eq_monotoneCurve`, `Rockafellar.theorem_24_3_swap`: the
  graphs of the mappings $\partial f$ on the line are exactly the complete nondecreasing curves.
* `Rockafellar.isCompleteNonDecreasingCurve_iff_exists_monotone`: the two descriptions of a complete
  nondecreasing curve in the source agree.
* Theorem 24.4, `Rockafellar.theorem_24_4`, `Rockafellar.theorem_24_4_seq`: the graph of
  $\partial f$ is closed.
* Theorem 24.5, `Rockafellar.theorem_24_5_lt`, `Rockafellar.theorem_24_5_limsup`,
  `Rockafellar.theorem_24_5_subdifferential`: if $f_i \to f$ pointwise on an open convex set, then
  $\limsup_i f_i'(x_i; y_i) \le f'(x; y)$, and subgradients of $f_i$ near $x$ are near
  $\partial f(x)$.
* Corollary 24.5.1, `Rockafellar.corollary_24_5_1_upperSemicontinuous`,
  `Rockafellar.corollary_24_5_1_subdifferential`: $f'(x; y)$ is upper semicontinuous on
  $\operatorname{int}(\operatorname{dom} f) \times \mathbb{R}^n$, and $\partial f$ is upper
  semicontinuous there.
* Theorem 24.6, `Rockafellar.theorem_24_6_lt`, `Rockafellar.theorem_24_6_limsup`,
  `Rockafellar.theorem_24_6_subdifferential`: the analogue of Theorem 24.5 along an approach to a
  point of $\operatorname{dom} f$ in a direction $y$.
* Theorem 24.7, `Rockafellar.theorem_24_7_bound`, `Rockafellar.theorem_24_7_nonempty`,
  `Rockafellar.theorem_24_7_isCompact`, `Rockafellar.theorem_24_7_isClosed`,
  `Rockafellar.theorem_24_7_isBounded`: for compact $S \subseteq
  \operatorname{int}(\operatorname{dom} f)$, $\partial f(S)$ is compact and $f$ is Lipschitz on $S$.
* Theorem 24.8, `Rockafellar.theorem_24_8`, `Rockafellar.theorem_24_8_of_isCyclicallyMonotone`: a
  mapping is contained in the subdifferential of a closed proper convex function if and only if it
  is cyclically monotone.
* Theorem 24.9, `Rockafellar.theorem_24_9`, `Rockafellar.theorem_24_9_subgradientRel`,
  `Rockafellar.theorem_24_9_unique`: the subdifferentials of closed proper convex functions are
  exactly the maximal cyclically monotone mappings.

## Conventions

* Theorems 24.1–24.3 are about functions on the real line. They are stated over `ℝ` itself, not over
  `Rockafellar.Rn 1`, because one-sided derivatives, nondecreasing functions and subsets of
  $\mathbb{R}^2$ are objects of real analysis. The pairing on the line is `innerₗ ℝ`, which is
  multiplication.
* Theorems 24.4–24.9 are stated over `Rockafellar.Rn n` with the pairing `Rockafellar.pairing n`.
* $f'_+$ and $f'_-$ are `ConvexAnalysis.rightDeriv` and `ConvexAnalysis.leftDeriv`. Their
  definitions contain the extension of the source: $f'_+(x) = +\infty$ when no point of
  $\operatorname{dom} f$ lies to the right of $x$, and $f'_-(x) = -\infty$ when no point of
  $\operatorname{dom} f$ lies to the left of $x$. Where $f$ is finite, $f'_+(x) = f'(x; 1)$ and
  $f'_-(x) = -f'(x; -1)$.

## Implementation notes

* A complete nondecreasing curve is defined by its order-theoretic description, as Mathlib's
  `IsMaxChain (· ≤ ·)` on `ℝ × ℝ`. The source introduces it by the formula $\Gamma = \{(x, x^*) \mid
  \varphi_-(x) \le x^* \le \varphi_+(x)\}$ for a nondecreasing $\varphi$ that is not everywhere
  infinite; this set is `ConvexAnalysis.monotoneCurve φ`, and
  `Rockafellar.isCompleteNonDecreasingCurve_iff_exists_monotone` proves that the two descriptions
  agree.
* A multivalued mapping is a `SetRel`, identified with its graph, and the graph of $\partial f$ is
  `ConvexAnalysis.subgradientRel`. Theorem 24.9 is about maximal cyclic monotonicity only. Plain
  monotonicity of $\partial f$ is `Rockafellar.isMonotoneRel_subgradientRel_rn`, and no result here
  relates the two maximality notions on $\mathbb{R}^n$.

## Deviations from the source

* **Theorem 24.1** (generalization). Monotonicity, finiteness and the interlacing inequalities hold
  without closedness of $f$, and the finiteness clause is an equivalence. See
  `Rockafellar.theorem_24_1_finite_iff`.
* **Remark after Theorem 24.1** (generalization). The formula for $\partial f(x)$ needs only
  properness of $f$. See `Rockafellar.theorem_24_1_subdifferential`.
* **Theorem 24.5** (generalization). The sequence approaching $x \in C$ may start outside
  $C$, since it is eventually in the open set. See `Rockafellar.theorem_24_5_limsup` and
  `Rockafellar.theorem_24_5_subdifferential`.
* **Theorem 24.6** (generalization). Closedness of $f$ is not assumed. See
  `Rockafellar.theorem_24_6_lt`.
* **Section 24, subdifferential supporting sets** (generalization). The set
  $\partial f(x)_y$ and its maximizer description are defined for arbitrary $f,x,y$.
  See `Rockafellar.subdifferentialNormal` and `Rockafellar.subdifferentialNormal_eq_sep`.
* **Theorem 24.7** (reading). The Lipschitz constant is some bound $\alpha$ on the subgradients over
  $S$, not necessarily $\sup\{|x^*| \mid x^* \in \partial f(S)\}$. See
  `Rockafellar.theorem_24_7_bound`.
* **Theorem 24.7** (generalization). The bounds need no closedness of $f$. Nonemptiness of
  $\partial f(S)$ also needs no compactness of $S$, and the compactness conclusion allows
  empty $S$.
* **Section 24, monotonicity of the subdifferential** (generalization). Properness suffices
  without convexity. See `Rockafellar.isMonotoneRel_subgradientRel_rn`.

## Not formalized

* **Theorem 24.2, the integral formula.** The source gives $f$ as $f(x) = \int_a^x \varphi(t)\,dt$;
  the formal statement gives the existence and uniqueness of $f$ without this formula.
-/

open Set Filter Topology
open scoped Pointwise RealInnerProductSpace

namespace Rockafellar

open ConvexAnalysis

/-! ### Theorem 24.1: the one-sided derivatives on the line -/

section OneDim

variable {f : ℝ → EReal}

/-- **Theorem 24.1** of [rockafellar1970convex], monotonicity of $f'_+$. Let $f$ be a proper convex
function on $\mathbb{R}$. Then $f'_+$ is a nondecreasing function on $\mathbb{R}$.

**Generalization.** The source assumes that $f$ is closed. Closedness is not needed for this
clause or for the next three: the interlacing inequalities are inequalities between difference
quotients. -/
theorem theorem_24_1_monotone_rightDeriv (hf : ConvexFn f) (hp : ProperConvex f) :
    Monotone (rightDeriv f) :=
  monotone_rightDeriv hf hp

/-- **Theorem 24.1** of [rockafellar1970convex], monotonicity of $f'_-$. Let $f$ be a proper convex
function on $\mathbb{R}$. Then $f'_-$ is a nondecreasing function on $\mathbb{R}$.

**Generalization.** The source assumes that $f$ is closed. This is not needed. -/
theorem theorem_24_1_monotone_leftDeriv (hf : ConvexFn f) (hp : ProperConvex f) :
    Monotone (leftDeriv f) :=
  monotone_leftDeriv hf hp

/-- **Theorem 24.1** of [rockafellar1970convex], finiteness. Let $f$ be a proper convex function on
$\mathbb{R}$, and let $x \in \mathbb{R}$. Then $f'_-(x) > -\infty$ and $f'_+(x) < +\infty$ if
and only if $x \in \operatorname{int}(\operatorname{dom} f)$.

**Generalization.** The source assumes that $f$ is closed, and says that $f'_+$ and $f'_-$ are
finite on $\operatorname{int}(\operatorname{dom} f)$. Closedness is not needed, and the
equivalence says also that finiteness characterizes $\operatorname{int}(\operatorname{dom} f)$. -/
theorem theorem_24_1_finite_iff (hf : ConvexFn f) (hp : ProperConvex f) {x : ℝ} :
    (⊥ < leftDeriv f x ∧ rightDeriv f x < ⊤) ↔ x ∈ interior (convexDom f) :=
  bot_lt_leftDeriv_and_rightDeriv_lt_top_iff hf hp

/-- **Theorem 24.1** of [rockafellar1970convex], the interlacing inequalities. Let $f$ be a proper
convex function on $\mathbb{R}$, and let $z_1 < x < z_2$. Then
$$f'_+(z_1) \le f'_-(x) \le f'_+(x) \le f'_-(z_2).$$

**Generalization.** The source assumes that $f$ is closed. This is not needed. -/
theorem theorem_24_1_chain (hf : ConvexFn f) (hp : ProperConvex f) {z₁ x z₂ : ℝ} (h₁ : z₁ < x)
    (h₂ : x < z₂) :
    rightDeriv f z₁ ≤ leftDeriv f x ∧ leftDeriv f x ≤ rightDeriv f x ∧
      rightDeriv f x ≤ leftDeriv f z₂ :=
  ⟨rightDeriv_le_leftDeriv hp h₁, leftDeriv_le_rightDeriv hf hp x, rightDeriv_le_leftDeriv hp h₂⟩

/-- **Theorem 24.1** of [rockafellar1970convex], first limit formula. Let $f$ be a closed proper
convex function on $\mathbb{R}$, and let $x \in \mathbb{R}$. Then
$$\lim_{z \downarrow x} f'_+(z) = f'_+(x).$$

The limit is taken in $[-\infty, +\infty]$. Closedness is necessary for this formula and the
other three: for the proper convex function $f$ with $f(0) = 1$, $f = 0$ on $(0, \infty)$ and
$f = +\infty$ on $(-\infty, 0)$, $f'_+(0) = -\infty$, while $f'_+ = 0$ to the right of $0$. -/
theorem theorem_24_1_tendsto_rightDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) :=
  tendsto_rightDeriv_nhdsWithin_Ioi hf x

/-- **Theorem 24.1** of [rockafellar1970convex], second limit formula. Let $f$ be a closed proper
convex function on $\mathbb{R}$, and let $x \in \mathbb{R}$. Then
$$\lim_{z \uparrow x} f'_+(z) = f'_-(x).$$
-/
theorem theorem_24_1_tendsto_rightDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (rightDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) :=
  tendsto_rightDeriv_nhdsWithin_Iio hf x

/-- **Theorem 24.1** of [rockafellar1970convex], third limit formula. Let $f$ be a closed proper
convex function on $\mathbb{R}$, and let $x \in \mathbb{R}$. Then
$$\lim_{z \downarrow x} f'_-(z) = f'_+(x).$$
-/
theorem theorem_24_1_tendsto_leftDeriv_Ioi (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[>] x) (𝓝 (rightDeriv f x)) :=
  tendsto_leftDeriv_nhdsWithin_Ioi hf x

/-- **Theorem 24.1** of [rockafellar1970convex], fourth limit formula. Let $f$ be a closed proper
convex function on $\mathbb{R}$, and let $x \in \mathbb{R}$. Then
$$\lim_{z \uparrow x} f'_-(z) = f'_-(x).$$
-/
theorem theorem_24_1_tendsto_leftDeriv_Iio (hf : ClosedProperConvexFn f) (x : ℝ) :
    Tendsto (leftDeriv f) (𝓝[<] x) (𝓝 (leftDeriv f x)) :=
  tendsto_leftDeriv_nhdsWithin_Iio hf x

/-- **Section 24** of [rockafellar1970convex], the remark after Theorem 24.1. Let $f$ be a proper
function on $\mathbb{R}$, and let $x \in \mathbb{R}$. Then
$$\partial f(x) = \{x^* \in \mathbb{R} \mid f'_-(x) \le x^* \le f'_+(x)\}.$$

**Generalization.** Only properness of $f$ is needed. -/
theorem theorem_24_1_subdifferential (hp : ProperConvex f) (x : ℝ) :
    subdifferential (innerₗ ℝ) f x
      = {y : ℝ | leftDeriv f x ≤ (y : EReal) ∧ (y : EReal) ≤ rightDeriv f x} :=
  Set.ext fun _ => mem_subdifferential_iff_le_rightDeriv hp

end OneDim

/-! ### Theorem 24.2 and Corollary 24.2.1: the primitive of a nondecreasing function -/

section Primitive

variable {φ : ℝ → EReal}

/-- **Theorem 24.2** of [rockafellar1970convex], existence. Let
$\varphi : \mathbb{R} \to [-\infty, +\infty]$ be nondecreasing and finite at some point $a$, and
let
$$\varphi_-(x) = \lim_{z \uparrow x} \varphi(z) = \sup_{z < x} \varphi(z), \qquad \varphi_+(x) =
  \lim_{z \downarrow x} \varphi(z) = \inf_{z > x} \varphi(z).$$
Then there is a closed proper convex function $f$ on $\mathbb{R}$ with $f'_- = \varphi_-$ and
$f'_+ = \varphi_+$.

The source gives $f$ as $\int_a^x \varphi(t)\,dt$. Here $f$ is constructed from the curve
$\Gamma(\varphi)$, which is a maximal monotone relation. -/
theorem theorem_24_2_exists (hφ : Monotone φ) {a : ℝ} (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤) :
    ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧
      (∀ x, leftDeriv f x = ⨆ z ∈ Iio x, φ z) ∧ (∀ x, rightDeriv f x = ⨅ z ∈ Ioi x, φ z) :=
  exists_closedProperConvexFn_leftDeriv_eq_rightDeriv_eq hφ hb ht

/-- **Theorem 24.2** of [rockafellar1970convex], uniqueness. Let
$\varphi : \mathbb{R} \to [-\infty, +\infty]$, and let $f$ and $g$ be closed proper convex
functions on $\mathbb{R}$ with $f'_- \le \varphi \le f'_+$ and $g'_- \le \varphi \le g'_+$. Then
there is $\alpha \in \mathbb{R}$ with $g = f + \alpha$.

The two pairs of inequalities force $\partial f = \partial g$, and the subdifferential
determines a closed proper convex function up to an additive constant. -/
theorem theorem_24_2_unique {f g : ℝ → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) (hf₁ : ∀ x, leftDeriv f x ≤ φ x) (hf₂ : ∀ x, φ x ≤ rightDeriv f x)
    (hg₁ : ∀ x, leftDeriv g x ≤ φ x) (hg₂ : ∀ x, φ x ≤ rightDeriv g x) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  exists_eq_add_coe_of_le_le hf hg hf₁ hf₂ hg₁ hg₂

/-- **Theorem 24.2** of [rockafellar1970convex]. Let $\varphi : \mathbb{R} \to [-\infty, +\infty]$
be nondecreasing and finite at some point $a$. Then there is a closed proper convex function $f$
on $\mathbb{R}$ with
$$f'_-(x) \le \varphi(x) \le f'_+(x) \quad \text{for every } x,$$
and every closed proper convex function $g$ with the same property is $g = f + \alpha$ for some
$\alpha \in \mathbb{R}$.

The source also gives the formula $f(x) = \int_a^x \varphi(t)\,dt$, which is not part of this
statement. -/
theorem theorem_24_2 (hφ : Monotone φ) {a : ℝ} (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤) :
    ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧ (∀ x, leftDeriv f x ≤ φ x) ∧
      (∀ x, φ x ≤ rightDeriv f x) ∧
      ∀ g : ℝ → EReal, ClosedProperConvexFn g → (∀ x, leftDeriv g x ≤ φ x) →
        (∀ x, φ x ≤ rightDeriv g x) → ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  exists_closedProperConvexFn_forall_le_le hφ hb ht

/-- **Corollary 24.2.1** of [rockafellar1970convex], for $f'_+$. Let $f$ be a proper convex function
on $\mathbb{R}$, and let $x, y \in \operatorname{int}(\operatorname{dom} f)$. Then
$$f(y) - f(x) = \int_x^y f'_+(t)\,dt.$$

The values $f(x)$, $f(y)$ and $f'_+(t)$ are real numbers here and are read through
`EReal.toReal`. The integrand is the derivative of a function that is convex and finite on an
open interval, so this is the fundamental theorem of calculus and needs no theory of monotone
functions. -/
theorem corollary_24_2_1_rightDeriv {f : ℝ → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    {x y : ℝ}
    (hx : x ∈ interior (convexDom f)) (hy : y ∈ interior (convexDom f)) :
    (f y).toReal - (f x).toReal = ∫ t in x..y, (rightDeriv f t).toReal :=
  sub_eq_intervalIntegral_rightDeriv hf hp hx hy

/-- **Corollary 24.2.1** of [rockafellar1970convex], for $f'_-$. Let $f$ be a proper convex function
on $\mathbb{R}$, and let $x, y \in \operatorname{int}(\operatorname{dom} f)$. Then
$$f(y) - f(x) = \int_x^y f'_-(t)\,dt.$$

The two one-sided derivatives differ only on the set of jumps of $f'_+$, which is countable and
hence a null set. -/
theorem corollary_24_2_1_leftDeriv {f : ℝ → EReal} (hf : ConvexFn f) (hp : ProperConvex f) {x y : ℝ}
    (hx : x ∈ interior (convexDom f)) (hy : y ∈ interior (convexDom f)) :
    (f y).toReal - (f x).toReal = ∫ t in x..y, (leftDeriv f t).toReal :=
  sub_eq_intervalIntegral_leftDeriv hf hp hx hy

end Primitive

/-! ### Theorem 24.3: the complete nondecreasing curves -/

section Curve

variable {Γ : Set (ℝ × ℝ)}

/-- **Section 24** of [rockafellar1970convex], complete nondecreasing curve. A subset $\Gamma$ of
$\mathbb{R}^2$ is a **complete nondecreasing curve** if it is a maximal totally ordered subset
for the coordinatewise partial order: any two points of $\Gamma$ are comparable, and no strictly
larger set has this property.

The source introduces the notion by the formula $\Gamma = \{(x, x^*) \mid \varphi_-(x) \le x^*
\le \varphi_+(x)\}$ and then states this description as equivalent; the equivalence is
`Rockafellar.isCompleteNonDecreasingCurve_iff_exists_monotone`. -/
def IsCompleteNonDecreasingCurve (Γ : Set (ℝ × ℝ)) : Prop :=
  IsMaxChain (· ≤ ·) Γ

/-- A subset of $\mathbb{R}^2$ is a complete nondecreasing curve if and only if it is a maximal
monotone relation on $\mathbb{R}$.

Monotonicity of a relation on $\mathbb{R}$ is the condition that its graph is totally ordered.
The only difference is that `IsChain` does not test a point against itself, and reflexivity of
$\le$ fills this gap. -/
theorem isCompleteNonDecreasingCurve_iff_isMaximalMonotoneRel :
    IsCompleteNonDecreasingCurve Γ ↔ IsMaximalMonotoneRel (innerₗ ℝ) Γ := by
  have hchain : ∀ σ : Set (ℝ × ℝ), IsChain (· ≤ ·) σ ↔ IsMonotoneRel (innerₗ ℝ) σ := by
    intro σ
    rw [isMonotoneRel_iff_forall_le_or_le]
    refine ⟨fun h p hp q hq => ?_, fun h => fun p hp q hq _ => h p hp q hq⟩
    rcases eq_or_ne p q with rfl | hne
    · exact Or.inl le_rfl
    · exact h hp hq hne
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨(hchain Γ).1 h₁, fun σ hσ hsub => ((h₂ ((hchain σ).2 hσ) hsub) ▸ subset_rfl : σ ⊆ Γ)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨(hchain Γ).2 h₁, fun σ hσ hsub =>
      Subset.antisymm hsub (h₂ σ ((hchain σ).1 hσ) hsub)⟩

/-- **Section 24** of [rockafellar1970convex], the defining formula. Let
$\varphi : \mathbb{R} \to [-\infty, +\infty]$ be nondecreasing and finite at some point $a$.
Then the set
$$\Gamma(\varphi) = \{(x, x^*) \mid \varphi_-(x) \le x^* \le \varphi_+(x)\}$$
is a complete nondecreasing curve.

The maximality of $\Gamma(\varphi)$ gives the function of Theorem 24.2. -/
theorem isCompleteNonDecreasingCurve_monotoneCurve {φ : ℝ → EReal} (hφ : Monotone φ) {a : ℝ}
    (hb : φ a ≠ ⊥) (ht : φ a ≠ ⊤) : IsCompleteNonDecreasingCurve (monotoneCurve φ) :=
  isCompleteNonDecreasingCurve_iff_isMaximalMonotoneRel.2
    (isMaximalMonotoneRel_monotoneCurve hφ hb ht)

/-- **Theorem 24.3** of [rockafellar1970convex]. A subset $\Gamma$ of $\mathbb{R}^2$ is a complete
nondecreasing curve if and only if $\Gamma$ is the graph of $\partial f$ for some closed proper
convex function $f$ on $\mathbb{R}$. -/
theorem theorem_24_3 :
    IsCompleteNonDecreasingCurve Γ ↔
      ∃ f : ℝ → EReal, ClosedProperConvexFn f ∧ Γ = subgradientRel (innerₗ ℝ) f := by
  rw [isCompleteNonDecreasingCurve_iff_isMaximalMonotoneRel]
  exact isMaximalMonotoneRel_iff_exists_closedProperConvexFn

/-- **Section 24** of [rockafellar1970convex], the converse of the defining formula. Every complete
nondecreasing curve $\Gamma$ is $\Gamma(\varphi) = \{(x, x^*) \mid \varphi_-(x) \le x^* \le
\varphi_+(x)\}$ for some nondecreasing $\varphi : \mathbb{R} \to [-\infty, +\infty]$ that is
finite at some point.

The proof uses Theorem 24.3 to write $\Gamma$ as the graph of $\partial f$. Then $\varphi$ is
$f'_+$ with its value at one relative interior point of $\operatorname{dom} f$ replaced by a
subgradient there. -/
theorem exists_monotone_monotoneCurve_eq (h : IsCompleteNonDecreasingCurve Γ) :
    ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ a, φ a ≠ ⊥ ∧ φ a ≠ ⊤) ∧ Γ = monotoneCurve φ := by
  obtain ⟨f, hf, rfl⟩ := theorem_24_3.1 h
  exact exists_monotone_ne_bot_ne_top_monotoneCurve_eq hf

/-- **Section 24** of [rockafellar1970convex]. The two descriptions of a complete nondecreasing
curve agree: a subset $\Gamma$ of $\mathbb{R}^2$ is a maximal totally ordered subset if and only
if $\Gamma = \{(x, x^*) \mid \varphi_-(x) \le x^* \le \varphi_+(x)\}$ for some nondecreasing
$\varphi : \mathbb{R} \to [-\infty, +\infty]$ that is finite at some point.

The source states the equivalence without proof, directly after the defining formula. -/
theorem isCompleteNonDecreasingCurve_iff_exists_monotone :
    IsCompleteNonDecreasingCurve Γ ↔
      ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ a, φ a ≠ ⊥ ∧ φ a ≠ ⊤) ∧ Γ = monotoneCurve φ := by
  refine ⟨exists_monotone_monotoneCurve_eq, ?_⟩
  rintro ⟨φ, hφ, ⟨a, hb, ht⟩, hΓ⟩
  rw [hΓ]
  exact isCompleteNonDecreasingCurve_monotoneCurve hφ hb ht

/-- **Theorem 24.3** of [rockafellar1970convex], uniqueness. Let $f$ and $g$ be closed proper convex
functions on $\mathbb{R}$ such that the graphs of $\partial f$ and $\partial g$ are equal. Then
there is $\alpha \in \mathbb{R}$ with $g = f + \alpha$.

The backbone result that this specializes needs only the inclusion
$\partial f \subseteq \partial g$, which is the form that the maximality argument of Theorem
24.9 uses. -/
theorem theorem_24_3_unique {f g : ℝ → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : subgradientRel (innerₗ ℝ) f = subgradientRel (innerₗ ℝ) g) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) := by
  have : IsCompatiblePairing ((innerₗ ℝ).flip) := by rw [flip_innerₗ]; infer_instance
  exact eq_add_coe_of_subgradientRel_subset hf hg h.subset

/-- **Theorem 24.3** of [rockafellar1970convex], the curve of a subdifferential. Let $f$ be a closed
proper convex function on $\mathbb{R}$. Then the graph of $\partial f$ is
$$\{(x, x^*) \mid (f'_+)_-(x) \le x^* \le (f'_+)_+(x)\},$$
the curve $\Gamma(\varphi)$ of the nondecreasing function $\varphi = f'_+$. -/
theorem theorem_24_3_subgradientRel_eq_monotoneCurve {f : ℝ → EReal} (hf : ClosedProperConvexFn f) :
    subgradientRel (innerₗ ℝ) f = monotoneCurve (rightDeriv f) :=
  subgradientRel_eq_monotoneCurve_rightDeriv hf

/-- **Section 24** of [rockafellar1970convex], the remark after Theorem 24.3. If $\Gamma$ is a
complete nondecreasing curve, then so is $\Gamma^* = \{(x^*, x) \mid (x, x^*) \in \Gamma\}$.

The source proves this by conjugacy, as $\Gamma^*$ is the graph of $\partial f^*$. In the
order-theoretic description it is immediate, because the exchange of coordinates is an order
isomorphism of $\mathbb{R} \times \mathbb{R}$. -/
theorem theorem_24_3_swap (h : IsCompleteNonDecreasingCurve Γ) :
    IsCompleteNonDecreasingCurve (Prod.swap '' Γ) := by
  have hswap : ∀ p q : ℝ × ℝ, p.swap ≤ q.swap ↔ p ≤ q := fun p q => by
    simp only [Prod.le_def, Prod.fst_swap, Prod.snd_swap]
    exact and_comm
  have hchain : ∀ σ : Set (ℝ × ℝ), IsChain (· ≤ ·) σ → IsChain (· ≤ ·) (Prod.swap '' σ) := by
    rintro σ hσ _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hpq : p ≠ q := fun h => hne (by rw [h])
    rcases hσ hp hq hpq with hle | hle
    · exact Or.inl ((hswap p q).2 hle)
    · exact Or.inr ((hswap q p).2 hle)
  refine ⟨hchain Γ h.1, fun t ht hsub => ?_⟩
  have hpre : Γ ⊆ Prod.swap '' t := by
    rintro p hp
    exact ⟨p.swap, hsub ⟨p, hp, rfl⟩, by simp⟩
  have hEq : Γ = Prod.swap '' t := h.2 (hchain t ht) hpre
  rw [hEq, ← Set.image_comp]
  simp

end Curve

/-! ### Theorem 24.4: the graph of $\partial f$ is closed -/

section GraphClosed

variable {n : ℕ} {f : Rn n → EReal}

/-- **Theorem 24.4** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$. Then the graph of $\partial f$ is a closed subset of
$\mathbb{R}^n \times \mathbb{R}^n$.

The proof does not use convexity, and uses closedness of $f$ only through lower semicontinuity:
the graph is written as an intersection of preimages of $\operatorname{epi} f$. The proof of the
source uses Theorem 23.5 and the conjugate. -/
theorem theorem_24_4 (hf : ClosedProperConvexFn f) : IsClosed (subgradientRel (pairing n) f) :=
  isClosed_subgradientRel continuous_inner hf.proper hf.lowerSemicontinuous

/-- **Theorem 24.4** of [rockafellar1970convex], in the words of the source. Let $f$ be a closed
proper convex function on $\mathbb{R}^n$, and let $x_i^* \in \partial f(x_i)$ for
$i = 1, 2, \dots$ with $x_i \to x$ and $x_i^* \to x^*$. Then $x^* \in \partial f(x)$. -/
theorem theorem_24_4_seq (hf : ClosedProperConvexFn f) {xs ys : ℕ → Rn n} {x y : Rn n}
    (hmem : ∀ i, ys i ∈ subdifferential (pairing n) f (xs i)) (hx : Tendsto xs atTop (𝓝 x))
    (hy : Tendsto ys atTop (𝓝 y)) : y ∈ subdifferential (pairing n) f x := by
  have hp : Tendsto (fun i => ((xs i, ys i) : Rn n × Rn n)) atTop (𝓝 (x, y)) := by
    rw [nhds_prod_eq]
    exact hx.prodMk hy
  exact (theorem_24_4 hf).mem_of_tendsto hp (Filter.Eventually.of_forall hmem)

end GraphClosed

/-! ### Theorem 24.5 and Corollary 24.5.1: convergence of directional derivatives -/

section Convergence

variable {n : ℕ} {C : Set (Rn n)} {f : ℕ → Rn n → EReal} {g : Rn n → EReal}

/-- A convex function that is finite on a nonempty open set $C$ is proper, and
$C \subseteq \operatorname{dom} f$ (Theorem 7.2). -/
private theorem properConvex_of_finite_on_isOpen {g : Rn n → EReal} (hg : ConvexFn g)
    (hC : IsOpen C)
    (hfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤) {x : Rn n}
        (hx : x ∈ C) : ProperConvex g ∧ C ⊆ convexDom g := by
  have hCdom : C ⊆ convexDom g := fun z hz => mem_convexDom.2 (lt_top_iff_ne_top.2 (hfin z hz).2)
  refine ⟨?_, hCdom⟩
  by_contra hp
  have hxi : x ∈ interior (convexDom g) := hC.subset_interior_iff.2 hCdom hx
  exact (hfin x hx).1 (hg.eq_bot_of_mem_relint_convexDom hp
    (Convex.interior_subset_relint hxi))

/-- **Theorem 24.5** of [rockafellar1970convex], first assertion, without the limit superior. Let
$C \subseteq \mathbb{R}^n$ be open and convex, let $f$ be a convex function on $\mathbb{R}^n$
that is finite on $C$, and let $f_1, f_2, \dots$ be convex functions on $\mathbb{R}^n$ that are
finite on $C$ and converge pointwise to $f$ on $C$. Let $x \in C$, and let $x_i \to x$ and
$y_i \to y$. Then for every real $\mu > f'(x; y)$ there is $i_0$ with $f_i'(x_i; y_i) < \mu$ for
every $i \ge i_0$.

This is the inequality $\limsup_i f_i'(x_i; y_i) \le f'(x; y)$, with the limit superior replaced
by its defining property; `Rockafellar.theorem_24_5_limsup` is the inequality itself. In the
Lean statement the sequence is `f` and the limit is `g`.

**Generalization.** The book places every $x_i$ in $C$. Convergence to $x$ in the open set
$C$ already gives eventual membership, which suffices for the bound. -/
theorem theorem_24_5_lt (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfin : ∀ i, ∀ z ∈ C, f i z ≠ ⊥ ∧ f i z ≠ ⊤) (hg : ConvexFn g)
    (hgfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤)
    (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) {x : Rn n}
    (hx : x ∈ C) {xs : ℕ → Rn n} (hxs : Tendsto xs atTop (𝓝 x)) {y : Rn n} {ys : ℕ → Rn n}
    (hys : Tendsto ys atTop (𝓝 y)) {μ : ℝ} (hμ : dirDeriv g x y < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv (f i) (xs i) (ys i) < (μ : EReal) := by
  obtain ⟨hgp, hgC⟩ := properConvex_of_finite_on_isOpen hg hC hgfin hx
  have h := fun i => properConvex_of_finite_on_isOpen (hf i) hC (hfin i) hx
  exact eventually_dirDeriv_lt hC hCc hf (fun i => (h i).1) (fun i => (h i).2) hg hgp hgC hconv hx
    hxs hys hμ

/-- **Theorem 24.5** of [rockafellar1970convex], first assertion. Let $C \subseteq \mathbb{R}^n$ be
open and convex, let $f$ be a convex function on $\mathbb{R}^n$ that is finite on $C$, and let
$f_1, f_2, \dots$ be convex functions on $\mathbb{R}^n$ that are finite on $C$ and converge
pointwise to $f$ on $C$. Let $x \in C$, and let $x_i \to x$ and $y_i \to y$. Then
$$\limsup_{i \to \infty} f_i'(x_i; y_i) \le f'(x; y).$$

Equality can fail: $f_i(x) = |x|^{p_i}$ with $p_i \downarrow 1$ converges pointwise to $|x|$ on
$\mathbb{R}$, with $f_i'(0; 1) = 0$ for every $i$ and $f'(0; 1) = 1$. In the Lean statement the
sequence is `f` and the limit is `g`.

**Generalization.** The book assumes $x_i \in C$ for every $i$. Eventual membership follows
from $x_i \to x \in C$ and openness. -/
theorem theorem_24_5_limsup (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfin : ∀ i, ∀ z ∈ C, f i z ≠ ⊥ ∧ f i z ≠ ⊤) (hg : ConvexFn g)
    (hgfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤)
    (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) {x : Rn n}
    (hx : x ∈ C) {xs : ℕ → Rn n} (hxs : Tendsto xs atTop (𝓝 x)) {y : Rn n} {ys : ℕ → Rn n}
    (hys : Tendsto ys atTop (𝓝 y)) :
    limsup (fun i => dirDeriv (f i) (xs i) (ys i)) atTop ≤ dirDeriv g x y := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨μ, hμ₁, hμ₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hev : ∀ᶠ i in atTop, dirDeriv (f i) (xs i) (ys i) ≤ (μ : EReal) :=
    (theorem_24_5_lt hC hCc hf hfin hg hgfin hconv hx hxs hys hμ₁).mono fun _ h => h.le
  exact le_trans (limsup_le_of_le (h := hev)) hμ₂.le

/-- **Theorem 24.5** of [rockafellar1970convex], second assertion. Let $C$, $f$, $f_1, f_2, \dots$
and $x_i \to x \in C$ be as in the first assertion. Then for every $\varepsilon > 0$ there is an
index $i_0$ with
$$\partial f_i(x_i) \subseteq \partial f(x) + \varepsilon B \quad \text{for every } i \ge i_0,$$
where $B$ is the closed Euclidean unit ball.

**Generalization.** The $x_i$ need only be eventually in $C$, which follows from convergence
and openness. -/
theorem theorem_24_5_subdifferential (hC : IsOpen C) (hCc : Convex ℝ C) (hf : ∀ i, ConvexFn (f i))
    (hfin : ∀ i, ∀ z ∈ C, f i z ≠ ⊥ ∧ f i z ≠ ⊤) (hg : ConvexFn g)
    (hgfin : ∀ z ∈ C, g z ≠ ⊥ ∧ g z ≠ ⊤)
    (hconv : ∀ z ∈ C, Tendsto (fun i => f i z) atTop (𝓝 (g z))) {x : Rn n}
    (hx : x ∈ C) {xs : ℕ → Rn n} (hxs : Tendsto xs atTop (𝓝 x)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subdifferential (pairing n) (f i) (xs i)
      ⊆ subdifferential (pairing n) g x + Metric.closedBall (0 : Rn n) ε := by
  obtain ⟨hgp, hgC⟩ := properConvex_of_finite_on_isOpen hg hC hgfin hx
  have h := fun i => properConvex_of_finite_on_isOpen (hf i) hC (hfin i) hx
  exact eventually_subdifferential_subset_add_closedBall hC hCc hf (fun i => (h i).1)
    (fun i => (h i).2) hg hgp hgC hconv hx hxs hε

/-- **Corollary 24.5.1** of [rockafellar1970convex], first assertion. Let $f$ be a proper convex
function on $\mathbb{R}^n$. Then $(x, y) \mapsto f'(x; y)$ is upper semicontinuous at every
point of $\operatorname{int}(\operatorname{dom} f) \times \mathbb{R}^n$.

This is Theorem 24.5 for a constant sequence. It cannot be improved to continuity in $x$,
although $f'(x; y)$ is continuous in $y$ for each fixed
$x \in \operatorname{int}(\operatorname{dom} f)$. -/
theorem corollary_24_5_1_upperSemicontinuous {f : Rn n → EReal} (hf : ConvexFn f)
    (hfp : ProperConvex f)
    {x : Rn n} (hx : x ∈ interior (convexDom f)) (y : Rn n) :
    UpperSemicontinuousAt (fun p : Rn n × Rn n => dirDeriv f p.1 p.2) (x, y) :=
  upperSemicontinuousAt_dirDeriv hf hfp hx y

/-- **Corollary 24.5.1** of [rockafellar1970convex], second assertion. Let $f$ be a proper convex
function on $\mathbb{R}^n$, let $x \in \operatorname{int}(\operatorname{dom} f)$, and let
$\varepsilon > 0$. Then there is $\delta > 0$ with
$$\partial f(z) \subseteq \partial f(x) + \varepsilon B \quad \text{for every } z \text{ with }
  |z - x| < \delta,$$
where $B$ is the closed Euclidean unit ball. -/
theorem corollary_24_5_1_subdifferential {f : Rn n → EReal} (hf : ConvexFn f) (hfp : ProperConvex f)
    {x : Rn n} (hx : x ∈ interior (convexDom f)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.ball x δ, subdifferential (pairing n) f z
      ⊆ subdifferential (pairing n) f x + Metric.closedBall (0 : Rn n) ε := by
  obtain ⟨δ, hδ, hmem⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhds_subdifferential_subset_add_closedBall hf hfp hx hε)
  exact ⟨δ, hδ, fun z hz => hmem (by simpa [Metric.mem_ball] using hz)⟩

end Convergence

/-! ### Theorem 24.6: approach to a point of $\operatorname{dom} f$ along a direction -/

section Boundary

variable {n : ℕ} {f : Rn n → EReal} {x y : Rn n}

/-- **Section 24** of [rockafellar1970convex], the set $\partial f(x)_y$. For a function $f$ on
$\mathbb{R}^n$ and $x, y \in \mathbb{R}^n$, $\partial f(x)_y$ is the set of
$x^* \in \partial f(x)$ such that $y$ is normal to $\partial f(x)$ at $x^*$.

Equivalently, it is the face of $\partial f(x)$ exposed by $y$; see
`Rockafellar.subdifferentialNormal_eq_sep`.

**Generalization.** The book uses this set with the hypotheses of Theorem 24.6. The Lean
definition admits any function and any point and direction. -/
def subdifferentialNormal (f : Rn n → EReal) (x y : Rn n) : Set (Rn n) :=
  {v ∈ subdifferential (pairing n) f x |
    y ∈ normalCone (pairing n) (subdifferential (pairing n) f x) v}

/-- For a function $f$ on $\mathbb{R}^n$ and $x, y \in \mathbb{R}^n$, the set $\partial f(x)_y$
consists of the points $x^* \in \partial f(x)$ at which $\langle y, \cdot \rangle$ attains its
maximum over $\partial f(x)$.

**Generalization.** The maximizer description also holds without the hypotheses of
Theorem 24.6. -/
theorem subdifferentialNormal_eq_sep (f : Rn n → EReal) (x y : Rn n) :
    subdifferentialNormal f x y
      = {v ∈ subdifferential (pairing n) f x |
          ∀ w ∈ subdifferential (pairing n) f x, ⟪y, w⟫ ≤ ⟪y, v⟫} := by
  have key : ∀ w : Rn n, pairing n w y = ⟪y, w⟫ := fun w => by
    rw [pairing_apply]; exact real_inner_comm _ _
  ext v
  simp only [subdifferentialNormal, Set.mem_sep_iff, mem_normalCone, map_sub, LinearMap.sub_apply,
    sub_nonpos, key]

/-- **Theorem 24.6** of [rockafellar1970convex], first assertion, without the limit superior. Let
$f$ be a proper convex function on $\mathbb{R}^n$, and let $x \in \operatorname{dom} f$. Let
$x_1, x_2, \dots$ be points of $\operatorname{dom} f$ different from $x$, with $x_i \to x$ and
$$\frac{x_i - x}{|x_i - x|} \to y.$$
Assume that $f'(x; y) > -\infty$ and that $x + \alpha y \in
\operatorname{int}(\operatorname{dom} f)$ for some $\alpha > 0$. Let $f'(x; y; z)$ be the
directional derivative at $y$ in the direction $z$ of the function $f'(x; \cdot)$. Then for
every $z$ and every real $\mu > f'(x; y; z)$ there is $i_0$ with $f'(x_i; z) < \mu$ for every
$i \ge i_0$.

**Generalization.** The source assumes that $f$ is closed. This is not needed: the proof
replaces the vanishing step $|x_i - x|$ by a fixed larger step, and so uses only the continuity
of $f$ at interior points.

The second-order derivative $f'(x; y; z)$ is `dirDeriv (dirDeriv f x) y z`. -/
theorem theorem_24_6_lt (hf : ConvexFn f) (hfp : ProperConvex f) (hx : x ∈ convexDom f)
    {xs : ℕ → Rn n}
    (hxsdom : ∀ i, xs i ∈ convexDom f) (hxsne : ∀ i, xs i ≠ x) (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y)) (hy : dirDeriv f x y ≠ ⊥)
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (convexDom f)) {z : Rn n} {μ : ℝ}
    (hμ : dirDeriv (dirDeriv f x) y z < (μ : EReal)) :
    ∀ᶠ i in atTop, dirDeriv f (xs i) z < (μ : EReal) :=
  eventually_dirDeriv_lt_of_tendsto_dir hf hfp hx hxsdom hxsne hxs hdir hy hα hαy hμ

/-- **Theorem 24.6** of [rockafellar1970convex], first assertion. Let $f$, $x$, $(x_i)$, $y$ and
$\alpha$ be as in `Rockafellar.theorem_24_6_lt`. Then for every $z \in \mathbb{R}^n$,
$$\limsup_{i \to \infty} f'(x_i; z) \le f'(x; y; z).$$

**Generalization.** The source assumes that $f$ is closed. This is not needed. -/
theorem theorem_24_6_limsup (hf : ConvexFn f) (hfp : ProperConvex f) (hx : x ∈ convexDom f)
    {xs : ℕ → Rn n}
    (hxsdom : ∀ i, xs i ∈ convexDom f) (hxsne : ∀ i, xs i ≠ x) (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y)) (hy : dirDeriv f x y ≠ ⊥)
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (convexDom f)) (z : Rn n) :
    limsup (fun i => dirDeriv f (xs i) z) atTop ≤ dirDeriv (dirDeriv f x) y z := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  obtain ⟨μ, hμ₁, hμ₂⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hev : ∀ᶠ i in atTop, dirDeriv f (xs i) z ≤ (μ : EReal) :=
    (theorem_24_6_lt hf hfp hx hxsdom hxsne hxs hdir hy hα hαy hμ₁).mono fun _ h => h.le
  exact le_trans (limsup_le_of_le (h := hev)) hμ₂.le

/-- **Theorem 24.6** of [rockafellar1970convex], second assertion. Let $f$, $x$, $(x_i)$, $y$ and
$\alpha$ be as in `Rockafellar.theorem_24_6_lt`. Then for every $\varepsilon > 0$ there is an
index $i_0$ with
$$\partial f(x_i) \subseteq \partial f(x)_y + \varepsilon B \quad \text{for every } i \ge i_0,$$
where $B$ is the closed Euclidean unit ball.

**Generalization.** The source assumes that $f$ is closed. This is not needed. -/
theorem theorem_24_6_subdifferential (hf : ConvexFn f) (hfp : ProperConvex f) (hx : x ∈ convexDom f)
    {xs : ℕ → Rn n} (hxsdom : ∀ i, xs i ∈ convexDom f) (hxsne : ∀ i, xs i ≠ x)
    (hxs : Tendsto xs atTop (𝓝 x))
    (hdir : Tendsto (fun i => ‖xs i - x‖⁻¹ • (xs i - x)) atTop (𝓝 y)) (hy : dirDeriv f x y ≠ ⊥)
    {α : ℝ} (hα : 0 < α) (hαy : x + α • y ∈ interior (convexDom f)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, subdifferential (pairing n) f (xs i)
      ⊆ subdifferentialNormal f x y + Metric.closedBall (0 : Rn n) ε := by
  rw [subdifferentialNormal_eq_sep]
  exact eventually_subdifferential_subset_exposed_add_closedBall hf hfp hx hxsdom hxsne hxs hdir hy
    hα hαy hε

end Boundary

/-! ### Theorem 24.7: local boundedness of $\partial f$ and the Lipschitz property -/

section Bounded

variable {n : ℕ} {f : Rn n → EReal} {S : Set (Rn n)}

/-- **Theorem 24.7** of [rockafellar1970convex], the bound. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $S$ be a compact subset of $\operatorname{int}(\operatorname{dom} f)$.
Then there is a real number $\alpha \ge 0$ such that

(i) $|x^*| \le \alpha$ for every $x^* \in \partial f(x)$ and every $x \in S$;

(ii) $f'(x; z) \le \alpha |z|$ for every $x \in S$ and every $z \in \mathbb{R}^n$;

(iii) $|f(y) - f(x)| \le \alpha |y - x|$ for all $x, y \in S$.

**Reading.** The source takes $\alpha = \sup\{|x^*| \mid x^* \in \partial f(S)\}$. The statement
here asserts existence of a common bound $\alpha$ for subgradients, derivatives and
Lipschitz continuity.

**Generalization.** For these bounds the book assumes $f$ closed and $S$ nonempty. The Lean
result allows nonclosed $f$ and empty compact $S$.

The Lipschitz condition is `LipschitzOnWith` for the real-valued function
`fun x => (f x).toReal` on $S$. -/
theorem theorem_24_7_bound (hf : ConvexFn f) (hp : ProperConvex f) (hS : IsCompact S)
    (hSD : S ⊆ interior (convexDom f)) :
    ∃ α : NNReal, LipschitzOnWith α (fun x => (f x).toReal) S ∧
      (∀ x ∈ S, ∀ v ∈ subdifferential (pairing n) f x, ‖v‖ ≤ (α : ℝ)) ∧
      ∀ x ∈ S, ∀ z : Rn n, dirDeriv f x z ≤ (((α : ℝ) * ‖z‖ : ℝ) : EReal) := by
  obtain ⟨α, hlip, hpair, hdir⟩ :=
    exists_lipschitz_forall_pairing_le_of_isCompact (B := pairing n) hf hp hS hSD
  refine ⟨α, hlip, fun x hx v hv => ?_, hdir⟩
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have h := hpair x hx v hv v
  rw [pairing_apply, real_inner_self_eq_norm_mul_norm] at h
  exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.2 hv0)

/-- **Theorem 24.7** of [rockafellar1970convex], nonemptiness. Let $f$ be a proper convex function
on $\mathbb{R}^n$, and let $S$ be a nonempty subset of
$\operatorname{int}(\operatorname{dom} f)$. Then
$$\partial f(S) = \bigcup \{\partial f(x) \mid x \in S\}$$
is nonempty.

**Generalization.** The book assumes $f$ closed and $S$ compact. Neither is necessary for
nonemptiness, which follows from Theorem 23.4 at any point of $S$. -/
theorem theorem_24_7_nonempty (hf : ConvexFn f) (hp : ProperConvex f) (hne : S.Nonempty)
    (hSD : S ⊆ interior (convexDom f)) : ((subgradientRel (pairing n) f).image S).Nonempty :=
  image_subgradientRel_nonempty hf hp hne hSD

/-- **Theorem 24.7** of [rockafellar1970convex], compactness. Let $f$ be a closed proper convex
function on $\mathbb{R}^n$, and let $S$ be a compact subset of
$\operatorname{int}(\operatorname{dom} f)$. Then $\partial f(S)$ is compact.

**Generalization.** The book assumes $S$ nonempty. Compactness also holds for empty $S$. -/
theorem theorem_24_7_isCompact (hf : ClosedProperConvexFn f) (hS : IsCompact S)
    (hSD : S ⊆ interior (convexDom f)) : IsCompact ((subgradientRel (pairing n) f).image S) :=
  isCompact_image_subgradientRel hf hS hSD

/-- **Theorem 24.7** of [rockafellar1970convex], closedness. Let $f$ be a closed proper convex
function on $\mathbb{R}^n$, and let $S$ be a compact subset of
$\operatorname{int}(\operatorname{dom} f)$. Then $\partial f(S)$ is closed.

**Generalization.** The book assumes $S$ nonempty. The conclusion also covers empty $S$. -/
theorem theorem_24_7_isClosed (hf : ClosedProperConvexFn f) (hS : IsCompact S)
    (hSD : S ⊆ interior (convexDom f)) : IsClosed ((subgradientRel (pairing n) f).image S) :=
  (theorem_24_7_isCompact hf hS hSD).isClosed

/-- **Theorem 24.7** of [rockafellar1970convex], boundedness. Let $f$ be a closed proper convex
function on $\mathbb{R}^n$, and let $S$ be a compact subset of
$\operatorname{int}(\operatorname{dom} f)$. Then $\partial f(S)$ is bounded.

**Generalization.** The book assumes $S$ nonempty. The conclusion also covers empty $S$. -/
theorem theorem_24_7_isBounded (hf : ClosedProperConvexFn f) (hS : IsCompact S)
    (hSD : S ⊆ interior (convexDom f)) :
    Bornology.IsBounded ((subgradientRel (pairing n) f).image S) :=
  (theorem_24_7_isCompact hf hS hSD).isBounded

end Bounded

/-!
### Theorems 24.8 and 24.9: cyclic monotonicity

A multivalued mapping $\rho$ from $\mathbb{R}^n$ to $\mathbb{R}^n$ is **cyclically monotone** if for
every finite cycle $(x_0, x_0^*), (x_1, x_1^*), \dots, (x_m, x_m^*)$ of pairs in its graph,
$$\langle x_1 - x_0, x_0^* \rangle + \langle x_2 - x_1, x_1^* \rangle + \dots + \langle x_0 - x_m,
  x_m^* \rangle \le 0.$$
This is `ConvexAnalysis.IsCyclicallyMonotone`.
-/

section Cyclic

variable {n : ℕ} {ρ : SetRel (Rn n) (Rn n)} {f : Rn n → EReal}

/-- The zero function is a closed proper convex function on $\mathbb{R}^n$; it makes Theorem 24.8
true for the empty mapping. -/
private theorem closedProperConvexFn_zero (n : ℕ) :
    ClosedProperConvexFn (affineFn (pairing n) 0 0) :=
  ⟨convexFn_affineFn 0 0, closedConvex_affineFn (continuous_pairing (pairing n) 0),
    properConvex_affineFn 0 0⟩

/-- **Theorem 24.8** of [rockafellar1970convex], sufficiency. Let $\rho$ be a cyclically monotone
multivalued mapping from $\mathbb{R}^n$ to $\mathbb{R}^n$. Then there is a closed proper convex
function $f$ on $\mathbb{R}^n$ such that $\rho \subseteq \partial f$.

The empty mapping is included. The proof of the source excludes it at the start. -/
theorem theorem_24_8_of_isCyclicallyMonotone (hρ : IsCyclicallyMonotone (pairing n) ρ) :
    ∃ f : Rn n → EReal, ClosedProperConvexFn f ∧ ρ ⊆ subgradientRel (pairing n) f := by
  rcases Set.eq_empty_or_nonempty ρ with rfl | hne
  · exact ⟨affineFn (pairing n) 0 0, closedProperConvexFn_zero n, Set.empty_subset _⟩
  obtain ⟨g, hconv, hclosed, hproper, hsub⟩ :=
    exists_convexFn_subgradientRel_of_isCyclicallyMonotone hρ hne
  exact ⟨g, ⟨hconv, hclosed, hproper⟩, hsub⟩

/-- **Theorem 24.8** of [rockafellar1970convex]. A multivalued mapping $\rho$ from $\mathbb{R}^n$ to
$\mathbb{R}^n$ is contained in the subdifferential $\partial f$ of some closed proper convex
function $f$ on $\mathbb{R}^n$ if and only if $\rho$ is cyclically monotone.

The mapping $\rho$ and the mapping $\partial f$ are compared through their graphs, as `SetRel`. -/
theorem theorem_24_8 :
    (∃ f : Rn n → EReal, ClosedProperConvexFn f ∧ ρ ⊆ subgradientRel (pairing n) f) ↔
      IsCyclicallyMonotone (pairing n) ρ :=
  ⟨fun ⟨_, hf, hsub⟩ => (isCyclicallyMonotone_subgradientRel hf.proper).mono hsub,
    theorem_24_8_of_isCyclicallyMonotone⟩

/-- **Theorem 24.9** of [rockafellar1970convex], one direction. Let $f$ be a closed proper convex
function on $\mathbb{R}^n$. Then $\partial f$ is a maximal cyclically monotone mapping: it is
cyclically monotone, and no strictly larger mapping is cyclically monotone.

This is a statement about maximal cyclic monotonicity, not about maximal monotonicity. -/
theorem theorem_24_9_subgradientRel (hf : ClosedProperConvexFn f) :
    IsMaximalCyclicallyMonotone (pairing n) (subgradientRel (pairing n) f) :=
  isMaximalCyclicallyMonotone_subgradientRel hf

/-- **Theorem 24.9** of [rockafellar1970convex]. A multivalued mapping $\rho$ from $\mathbb{R}^n$ to
$\mathbb{R}^n$ is maximal cyclically monotone if and only if $\rho = \partial f$ for some closed
proper convex function $f$ on $\mathbb{R}^n$. -/
theorem theorem_24_9 :
    IsMaximalCyclicallyMonotone (pairing n) ρ ↔
      ∃ f : Rn n → EReal, ClosedProperConvexFn f ∧ ρ = subgradientRel (pairing n) f :=
  isMaximalCyclicallyMonotone_iff_exists_closedProperConvexFn

/-- **Theorem 24.9** of [rockafellar1970convex], uniqueness. Let $f$ and $g$ be closed proper convex
functions on $\mathbb{R}^n$ with $\partial f = \partial g$. Then there is
$\alpha \in \mathbb{R}$ with $g = f + \alpha$.

The backbone result that this specializes needs only the inclusion
$\partial f \subseteq \partial g$. -/
theorem theorem_24_9_unique {g : Rn n → EReal} (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g)
    (h : subgradientRel (pairing n) f = subgradientRel (pairing n) g) :
    ∃ α : ℝ, ∀ x, g x = f x + (α : EReal) :=
  eq_add_coe_of_subgradientRel_subset hf hg h.subset

/-- **Section 24** of [rockafellar1970convex]. Let $f$ be a proper function on $\mathbb{R}^n$. Then
$\partial f$ is a monotone mapping: $\langle x_1 - x_2, x_1^* - x_2^* \rangle \ge 0$ whenever
$x_1^* \in \partial f(x_1)$ and $x_2^* \in \partial f(x_2)$.

This is the case $m = 1$ of cyclic monotonicity.

**Generalization.** The book assumes $f$ proper convex. Properness suffices for the
two-point subgradient inequality. -/
theorem isMonotoneRel_subgradientRel_rn (hp : ProperConvex f) :
    IsMonotoneRel (pairing n) (subgradientRel (pairing n) f) :=
  isMonotoneRel_subgradientRel hp

/-- **Section 24** of [rockafellar1970convex]. A multivalued mapping from $\mathbb{R}$ to
$\mathbb{R}$ is monotone if and only if it is cyclically monotone.

The source derives this from Theorems 24.3 and 24.9. The proof here rotates a cycle so that the
pair with the largest value of $x + x^*$ comes first, and then deletes this pair. For $n > 1$
the equivalence is false: a linear mapping with matrix $Q$ is monotone as soon as the symmetric
part of $Q$ is positive semidefinite, but cyclically monotone only if $Q$ is symmetric. -/
theorem isMonotoneRel_iff_isCyclicallyMonotone_line {σ : SetRel ℝ ℝ} :
    IsMonotoneRel (innerₗ ℝ) σ ↔ IsCyclicallyMonotone (innerₗ ℝ) σ :=
  ⟨IsMonotoneRel.isCyclicallyMonotone, IsCyclicallyMonotone.isMonotoneRel⟩

end Cyclic

end Rockafellar
