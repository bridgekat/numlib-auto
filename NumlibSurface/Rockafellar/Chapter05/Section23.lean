/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Numlib.Analysis.Convex.Extremum.Perturbation
import Numlib.Analysis.Convex.Polyhedral.Duality
import Numlib.Analysis.Convex.Recession.ConeHull
import Numlib.Analysis.Convex.Subdifferential.Approx
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Analysis.Convex.Subdifferential.Existence
import NumlibSurface.Rockafellar.Chapter03.Section16
import NumlibSurface.Rockafellar.Chapter04.Section19

/-!
# Rockafellar, Section 23: Directional derivatives and subgradients

This module formalizes Section 23 of [rockafellar1970convex]: the one-sided directional derivative
$f'(x; y)$ of a convex function $f$ on $\mathbb{R}^n$, the subdifferential $\partial f(x)$, and the
relations between them. A vector $x^*$ is a **subgradient** of $f$ at $x$ if
$f(z) \ge f(x) + \langle z - x, x^* \rangle$ for every $z$, and $\partial f(x)$ is the set of
subgradients. The central facts are that $x^* \in \partial f(x)$ if and only if
$f'(x; y) \ge \langle y, x^* \rangle$ for every $y$ (Theorem 23.2), that $f'(x; \cdot)$ is the
support function of $\partial f(x)$ for $x \in \operatorname{ri}(\operatorname{dom} f)$ (Theorem
23.4), and that
$$x^* \in \partial f(x) \iff f(x) + f^*(x^*) = \langle x, x^* \rangle$$
for proper $f$ (Theorem 23.5), so that $\partial f^*$ is the inverse of $\partial f$ for closed $f$
(Corollary 23.5.1).

The second half of the section gives the calculus of subgradients: $\varepsilon$-subgradients
(Theorem 23.6), normals to level sets (Theorem 23.7), the sum rule $\partial(f_1 + \dots + f_m)(x) =
\partial f_1(x) + \dots + \partial f_m(x)$ (Theorem 23.8), the chain rule
$\partial(hA)(x) = A^* \partial h(Ax)$ (Theorem 23.9), and the polyhedral case, in which no
qualification is needed (Theorem 23.10). The proofs specialize the modules
`Numlib.Analysis.Convex.Subdifferential.Calculus`,
`Numlib.Analysis.Convex.Subdifferential.Existence` and
`Numlib.Analysis.Convex.Subdifferential.Approx`.

## Main definitions

* `Rockafellar.nonsmoothMaxFn`: the example $f(\xi_1, \xi_2) = \max\{1 - \xi_1^{1/2}, |\xi_2|\}$ for
  $\xi_1 \ge 0$, $+\infty$ for $\xi_1 < 0$, of p. 218, for which $\operatorname{dom} \partial f$ is
  not convex.

## Main results

* Theorem 23.1, `Rockafellar.theorem_23_1_monotone`, `Rockafellar.theorem_23_1_iInf`,
  `Rockafellar.theorem_23_1_posHomogeneous`, `Rockafellar.theorem_23_1_convex`,
  `Rockafellar.theorem_23_1_zero`, `Rockafellar.theorem_23_1_neg_le`: the difference quotient is
  nondecreasing, and $f'(x; \cdot)$ is a positively homogeneous convex function with $f'(x; 0) = 0$
  and $-f'(x; -y) \le f'(x; y)$.
* Theorem 23.2, `Rockafellar.theorem_23_2`, `Rockafellar.theorem_23_2_closure`:
  $x^* \in \partial f(x)$ if and only if $f'(x; \cdot) \ge \langle \cdot, x^* \rangle$, and the
  closure of $f'(x; \cdot)$ is the support function of $\partial f(x)$.
* Theorem 23.3, `Rockafellar.theorem_23_3_proper`, `Rockafellar.theorem_23_3_two_sided`,
  `Rockafellar.theorem_23_3_relint`: a function with a subgradient at a point where it is finite is
  proper; without a subgradient, $f'(x; \cdot)$ takes the value $-\infty$.
* Theorem 23.4, `Rockafellar.theorem_23_4_notMem_dom`, `Rockafellar.theorem_23_4_nonempty`,
  `Rockafellar.theorem_23_4_proper`, `Rockafellar.theorem_23_4_closed`,
  `Rockafellar.theorem_23_4_supportFn`, `Rockafellar.theorem_23_4_isBounded_iff`,
  `Rockafellar.theorem_23_4_finite_iff`: a proper convex function has subgradients on
  $\operatorname{ri}(\operatorname{dom} f)$, where $f'(x; \cdot) = \delta^*(\cdot \mid \partial
  f(x))$.
* Theorem 23.5, `Rockafellar.theorem_23_5_a`, `Rockafellar.theorem_23_5_b`,
  `Rockafellar.theorem_23_5_c`, `Rockafellar.theorem_23_5_d`, `Rockafellar.theorem_23_5_a_star`,
  `Rockafellar.theorem_23_5_b_star`, `Rockafellar.theorem_23_5_a_star_star`: the equivalent
  conditions for $x^* \in \partial f(x)$, among them $f(x) + f^*(x^*) = \langle x, x^* \rangle$.
* Corollary 23.5.1, `Rockafellar.corollary_23_5_1`, `Rockafellar.corollary_23_5_1_mem`: for closed
  convex $f$, $\partial f^*$ is the inverse of $\partial f$.
* Corollary 23.5.2, `Rockafellar.corollary_23_5_2_clFn`,
  `Rockafellar.corollary_23_5_2_subdifferential`: at a point where $\partial f(x) \ne \emptyset$,
  $(\operatorname{cl} f)(x) = f(x)$ and $\partial(\operatorname{cl} f)(x) = \partial f(x)$.
* Corollary 23.5.3, `Rockafellar.corollary_23_5_3`: $\partial \delta^*(x^* \mid C)$ is the set of
  points of $C$ at which $\langle \cdot, x^* \rangle$ attains its maximum over $C$.
* Corollary 23.5.4, `Rockafellar.corollary_23_5_4`, `Rockafellar.corollary_23_5_4_inv`:
  $x^* \in \partial \delta(x \mid K)$ if and only if $x \in K$, $x^* \in K^\circ$ and
  $\langle x, x^* \rangle = 0$.
* Theorem 23.6, `Rockafellar.theorem_23_6`: $f'(x; y)$ is the limit of
  $\delta^*(y \mid \partial_\varepsilon f(x))$ as $\varepsilon \downarrow 0$.
* Theorem 23.7, `Rockafellar.theorem_23_7`: the normal cone to $\{z \mid f(z) \le f(x)\}$ at $x$ is
  the closure of the cone generated by $\partial f(x)$, when $f$ does not attain its minimum at $x$.
* Corollary 23.7.1, `Rockafellar.corollary_23_7_1`, `Rockafellar.corollary_23_7_1_smul`: for
  $x \in \operatorname{int}(\operatorname{dom} f)$ no closure is needed.
* Theorem 23.8, `Rockafellar.theorem_23_8`, `Rockafellar.theorem_23_8_subset`,
  `Rockafellar.theorem_23_8_polyhedral`: the sum rule under the relative interior condition and
  under the polyhedral condition.
* Corollary 23.8.1, `Rockafellar.corollary_23_8_1`, `Rockafellar.corollary_23_8_1_subset`: the
  normal cone to an intersection is the sum of the normal cones.
* Theorem 23.9, `Rockafellar.theorem_23_9`, `Rockafellar.theorem_23_9_subset`,
  `Rockafellar.theorem_23_9_polyhedral`: the chain rule $\partial(hA)(x) = A^* \partial h(Ax)$.
* Theorem 23.10, `Rockafellar.theorem_23_10_nonempty`, `Rockafellar.theorem_23_10_polyhedral`,
  `Rockafellar.theorem_23_10_dirDeriv_polyhedral`, `Rockafellar.theorem_23_10_dirDeriv_proper`,
  `Rockafellar.theorem_23_10_supportFn`: a polyhedral convex function has a polyhedral
  subdifferential at every point where it is finite, and $f'(x; \cdot) = \delta^*(\cdot \mid
  \partial f(x))$ there.

## Proof outline

Most results apply earlier parts of the source. Theorem 23.2 is Corollary 13.2.1 applied to
$f'(x; \cdot)$. Theorem 23.4 is Theorem 7.2 together with Corollary 7.4.2. Theorem 23.8 follows from
Theorem 16.4, and Theorem 23.9 from Theorem 16.3.

## Notation

* $f'(x; y)$: `ConvexAnalysis.dirDeriv f x y`.
* $\partial f(x)$: `ConvexAnalysis.subdifferential (Rockafellar.pairing n) f x`.
* The multivalued mapping $\partial f$: its graph `ConvexAnalysis.subgradientRel
  (Rockafellar.pairing n) f`.
* $N_C(x)$: `ConvexAnalysis.normalCone (Rockafellar.pairing n) C x`.
* $\partial_\varepsilon f(x)$: `ConvexAnalysis.epsSubdifferential (Rockafellar.pairing n) ε f x`.
* $\delta^*(\cdot \mid C)$: `ConvexAnalysis.supportFn (Rockafellar.pairing n) C`.
* $\delta(\cdot \mid C)$: `ConvexAnalysis.indicatorFn C`.
* $f^*$: `ConvexAnalysis.convexConj (Rockafellar.pairing n) f`.
* $\operatorname{cl} f$: `ConvexAnalysis.convexCl f`.

## Implementation notes

* `ConvexAnalysis.dirDeriv f x y` is defined as $\inf_{\lambda > 0} [f(x + \lambda y) - f(x)] /
  \lambda$. The source defines $f'(x; y)$ as the limit as $\lambda \downarrow 0$;
  `Rockafellar.theorem_23_1_monotone` shows that the two agree for convex $f$ finite at $x$.
* The normal cone `ConvexAnalysis.normalCone` is $\{y \mid \langle z - x, y \rangle \le 0 \text{ for
  every } z \in C\}$ for every $x$, and always contains $0$. The source defines
  $N_C(x) = \partial \delta(x \mid C)$, which is empty for $x \notin C$. The two agree for
  $x \in C$.
* The graph of $\partial f$ is a `SetRel`, so the inverse mapping of Corollary 23.5.1 is
  `SetRel.inv`.
* "$f$ is finite at $x$" is the pair of hypotheses `f x ≠ ⊤` and `f x ≠ ⊥`, or the hypothesis
  `f x = r` for a real `r`. The predicate `ConvexAnalysis.ProperConvex` says only that $f$ is
  proper; convexity is the separate hypothesis `ConvexAnalysis.ConvexFn`.

## Deviations from the source

* **Theorem 23.1** (generalization). Positive homogeneity of $f'(x; \cdot)$ holds for every $f$ and
  $x$, and $f'(x; 0) = 0$ holds without convexity. See `Rockafellar.theorem_23_1_posHomogeneous` and
  `Rockafellar.theorem_23_1_zero`.
* **Theorem 23.2** (generalization). The equivalence holds without convexity of $f$. See
  `Rockafellar.theorem_23_2`.
* **Theorem 23.4**, first assertion (generalization). $\partial f(x) = \emptyset$ for
  $x \notin \operatorname{dom} f$ holds for every proper $f$. See
  `Rockafellar.theorem_23_4_notMem_dom`.
* **Theorem 23.5** (generalization). Conditions (a), (b) and (c) are equivalent for every $f$, and
  (d) needs only properness, not convexity. See `Rockafellar.theorem_23_5_b`.
* **Corollary 23.5.1** (generalization). The source assumes $f$ closed proper convex; properness is
  not needed. See `Rockafellar.corollary_23_5_1`.
* **Corollary 23.5.2** (generalization). Properness is not needed. See
  `Rockafellar.corollary_23_5_2_clFn` and `Rockafellar.corollary_23_5_2_subdifferential`.
* **Corollary 23.5.4** (generalization). The source assumes $K$ nonempty and closed; neither
  hypothesis is needed. See `Rockafellar.corollary_23_5_4`.
* **Corollary 23.8.1** (reading). The hypothesis $x \in C_i$ is added, because the normal cone of
  the library is defined at every point and the source's $N_C(x) = \partial \delta(x \mid C)$ is
  empty off $C$. See `Rockafellar.corollary_23_8_1`.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {m n : ℕ}

/-! ### Theorem 23.1: the one-sided directional derivative -/

/-- **Theorem 23.1** of [rockafellar1970convex], monotonicity of the difference quotient. Let $f$ be
a convex function on $\mathbb{R}^n$, let $x$ be a point where $f$ is finite, and let
$y \in \mathbb{R}^n$. Then the difference quotient
$$\lambda \mapsto \frac{f(x + \lambda y) - f(x)}{\lambda}$$
is nondecreasing on $\lambda > 0$.

Therefore the limit as $\lambda \downarrow 0$ in the definition of the source equals the infimum
over $\lambda > 0$ that defines `ConvexAnalysis.dirDeriv`. The quotient is formed in `EReal`. -/
theorem theorem_23_1_monotone {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (y : Rn n) :
    MonotoneOn (fun a : ℝ => (f (x + a • y) - f x) / (a : EReal)) (Ioi 0) :=
  monotoneOn_sub_div hf hr y

/-- **Theorem 23.1** of [rockafellar1970convex], the infimum formula. For every function $f$ on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$ and all $x, y \in \mathbb{R}^n$,
$$f'(x; y) = \inf_{\lambda > 0} \frac{f(x + \lambda y) - f(x)}{\lambda}.$$

In the library this formula is the definition of `ConvexAnalysis.dirDeriv`. -/
theorem theorem_23_1_iInf (f : Rn n → EReal) (x y : Rn n) :
    dirDeriv f x y = ⨅ a ∈ Ioi (0 : ℝ), (f (x + a • y) - f x) / (a : EReal) :=
  dirDeriv_apply f x y

/-- **Theorem 23.1** of [rockafellar1970convex], positive homogeneity. For every function $f$ on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$ and every $x$, the function $f'(x; \cdot)$ is
positively homogeneous: $f'(x; \lambda y) = \lambda f'(x; y)$ for every $\lambda > 0$ and every
$y$.

**Generalization.** The source assumes that $f$ is convex and finite at $x$. Neither hypothesis
is needed, because the claim is a change of variable in the infimum. -/
theorem theorem_23_1_posHomogeneous (f : Rn n → EReal) (x : Rn n) :
    PosHomogeneous (dirDeriv f x) :=
  posHomogeneous_dirDeriv f x

/-- **Theorem 23.1** of [rockafellar1970convex], convexity. Let $f$ be a convex function on
$\mathbb{R}^n$, and let $x$ be a point where $f$ is finite. Then $y \mapsto f'(x; y)$ is a
convex function.

At a point $x \notin \operatorname{dom} f$ the difference quotient is $-\infty$ in every
direction, because $(+\infty) - (+\infty) = -\infty$ in `EReal`. -/
theorem theorem_23_1_convex {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) : ConvexFn (dirDeriv f x) :=
  convexFn_dirDeriv hf ht hb

/-- **Theorem 23.1** of [rockafellar1970convex], value at the origin. Let $f$ be a function on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and let $x$ be a point where $f$ is finite.
Then $f'(x; 0) = 0$.

**Generalization.** The source assumes that $f$ is convex. This is not needed. -/
theorem theorem_23_1_zero {f : Rn n → EReal} {x : Rn n} (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    dirDeriv f x 0 = 0 :=
  dirDeriv_zero ht hb

/-- **Theorem 23.1** of [rockafellar1970convex], last assertion. Let $f$ be a convex function on
$\mathbb{R}^n$, and let $x$ be a point where $f$ is finite. Then $-f'(x; -y) \le f'(x; y)$ for
every $y \in \mathbb{R}^n$. -/
theorem theorem_23_1_neg_le {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) (y : Rn n) : -dirDeriv f x (-y) ≤ dirDeriv f x y :=
  neg_dirDeriv_neg_le hf ht hb y

/-! ### Theorem 23.2: subgradients and directional derivatives -/

/-- **Theorem 23.2** of [rockafellar1970convex]. Let $f$ be a function on $\mathbb{R}^n$ with values
in $[-\infty, +\infty]$, and let $x$ be a point where $f$ is finite. Then $x^*$ is a subgradient
of $f$ at $x$ if and only if
$$f'(x; y) \ge \langle y, x^* \rangle \quad \text{for every } y \in \mathbb{R}^n.$$

**Generalization.** The source assumes that $f$ is convex. This is not needed: the subgradient
inequality and the inequality for the infimum of the difference quotients are two forms of the
same family of inequalities.

The subgradient $x^*$ is `y`, and the direction $y$ is `v`. -/
theorem theorem_23_2 {f : Rn n → EReal} {x : Rn n} (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) {y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      ∀ v : Rn n, ((pairing n v y : ℝ) : EReal) ≤ dirDeriv f x v :=
  mem_subdifferential_iff_le_dirDeriv ht hb

/-- **Theorem 23.2** of [rockafellar1970convex], second assertion. Let $f$ be a convex function on
$\mathbb{R}^n$, and let $x$ be a point where $f$ is finite. Then the closure of the convex
function $f'(x; \cdot)$ is the support function of the closed convex set $\partial f(x)$:
$$\operatorname{cl} f'(x; \cdot) = \delta^*(\cdot \mid \partial f(x)).$$
-/
theorem theorem_23_2_closure {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) :
    convexCl (dirDeriv f x) = supportFn (pairing n) (subdifferential (pairing n) f x) := by
  have h := convexCl_dirDeriv (B := pairing n) hf ht hb
  rwa [flip_pairing] at h

/-! ### Theorem 23.3: when subgradients exist -/

/-- **Theorem 23.3** of [rockafellar1970convex], first assertion. Let $f$ be a function on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and let $x$ be a point where $f$ is finite.
If $\partial f(x) \ne \emptyset$, then $f$ is proper.

A subgradient gives an affine minorant of $f$, so $f$ never takes the value $-\infty$. -/
theorem theorem_23_3_proper {f : Rn n → EReal} {x : Rn n} (ht : f x ≠ ⊤) (hb : f x ≠ ⊥)
    (h : (subdifferential (pairing n) f x).Nonempty) : ProperConvex f :=
  properConvex_of_subdifferential_nonempty ht hb h

/-- **Theorem 23.3** of [rockafellar1970convex], second assertion. Let $f$ be a convex function on
$\mathbb{R}^n$, let $x$ be a point where $f$ is finite, and assume $\partial f(x) = \emptyset$.
Then there is $y \in \mathbb{R}^n$ with
$$f'(x; y) = -f'(x; -y) = -\infty.$$

The equation $-f'(x; -y) = -\infty$ is stated as $f'(x; -y) = +\infty$. -/
theorem theorem_23_3_two_sided {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) (hsub : subdifferential (pairing n) f x = ∅) :
    ∃ y : Rn n, dirDeriv f x y = ⊥ ∧ dirDeriv f x (-y) = ⊤ :=
  exists_dirDeriv_eq_bot_and_dirDeriv_neg_eq_top hf ht hb hsub

/-- **Theorem 23.3** of [rockafellar1970convex], last assertion. Let $f$ be a convex function on
$\mathbb{R}^n$, let $x$ be a point where $f$ is finite, and assume $\partial f(x) = \emptyset$.
Then $f'(x; z - x) = -\infty$ for every $z \in \operatorname{ri}(\operatorname{dom} f)$. -/
theorem theorem_23_3_relint {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} (ht : f x ≠ ⊤)
    (hb : f x ≠ ⊥) (hsub : subdifferential (pairing n) f x = ∅) {z : Rn n}
        (hz : z ∈ ri (convexDom f)) :
    dirDeriv f x (z - x) = ⊥ :=
  dirDeriv_eq_bot_of_subdifferential_eq_empty hf ht hb hsub hz

/-! ### Theorem 23.4: existence, closedness and boundedness -/

/-- **Theorem 23.4** of [rockafellar1970convex], first assertion. Let $f$ be a proper function on
$\mathbb{R}^n$. Then $\partial f(x) = \emptyset$ for every $x \notin \operatorname{dom} f$.

**Generalization.** The source assumes that $f$ is a proper convex function. Convexity is not
needed. -/
theorem theorem_23_4_notMem_dom {f : Rn n → EReal} (hp : ProperConvex f) {x : Rn n}
    (hx : x ∉ convexDom f) :
    subdifferential (pairing n) f x = ∅ :=
  subdifferential_eq_empty_of_notMem_convexDom hp hx

/-- **Theorem 23.4** of [rockafellar1970convex], existence. Let $f$ be a proper convex function on
$\mathbb{R}^n$. Then $\partial f(x) \ne \emptyset$ for every
$x \in \operatorname{ri}(\operatorname{dom} f)$. -/
theorem theorem_23_4_nonempty {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f) {x : Rn n}
    (hx : x ∈ ri (convexDom f)) : (subdifferential (pairing n) f x).Nonempty :=
  subdifferential_nonempty_of_mem_relint_convexDom hf hp hx

/-- **Theorem 23.4** of [rockafellar1970convex], properness of the directional derivative. Let $f$
be a proper convex function on $\mathbb{R}^n$, and let
$x \in \operatorname{ri}(\operatorname{dom} f)$. Then $f'(x; \cdot)$ is proper. -/
theorem theorem_23_4_proper {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f) {x : Rn n}
    (hx : x ∈ ri (convexDom f)) : ProperConvex (dirDeriv f x) :=
  properConvex_dirDeriv_of_mem_relint_convexDom hf hp hx

/-- **Theorem 23.4** of [rockafellar1970convex], closedness of the directional derivative. Let $f$
be a proper convex function on $\mathbb{R}^n$, and let
$x \in \operatorname{ri}(\operatorname{dom} f)$. Then $f'(x; \cdot)$ is closed. -/
theorem theorem_23_4_closed {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f) {x : Rn n}
    (hx : x ∈ ri (convexDom f)) : ClosedConvex (dirDeriv f x) :=
  closedConvex_dirDeriv_of_mem_relint_convexDom hf hp hx

/-- **Theorem 23.4** of [rockafellar1970convex], the support function formula. Let $f$ be a proper
convex function on $\mathbb{R}^n$, and let $x \in \operatorname{ri}(\operatorname{dom} f)$. Then
for every $y \in \mathbb{R}^n$,
$$f'(x; y) = \sup\{\langle y, x^* \rangle \mid x^* \in \partial f(x)\} = \delta^*(y \mid
  \partial f(x)).$$

Because $f'(x; \cdot)$ is already closed at such $x$, no closure appears, unlike in Theorem
23.2. -/
theorem theorem_23_4_supportFn {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f) {x : Rn n}
    (hx : x ∈ ri (convexDom f)) :
    dirDeriv f x = supportFn (pairing n) (subdifferential (pairing n) f x) := by
  have h := dirDeriv_eq_supportFn_of_mem_relint_convexDom (B := pairing n) hf hp hx
  rwa [flip_pairing] at h

/-- **Theorem 23.4** of [rockafellar1970convex], boundedness. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $x \in \operatorname{ri}(\operatorname{dom} f)$. Then $\partial f(x)$ is
bounded if and only if $x \in \operatorname{int}(\operatorname{dom} f)$.

The source states that $\partial f(x)$ is nonempty and bounded if and only if
$x \in \operatorname{int}(\operatorname{dom} f)$. The statement here assumes
$x \in \operatorname{ri}(\operatorname{dom} f)$, where $\partial f(x)$ is nonempty by
`Rockafellar.theorem_23_4_nonempty`; it says nothing about points outside
$\operatorname{ri}(\operatorname{dom} f)$. -/
theorem theorem_23_4_isBounded_iff {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    {x : Rn n} (hx : x ∈ ri (convexDom f)) :
    Bornology.IsBounded (subdifferential (pairing n) f x) ↔ x ∈ interior (convexDom f) :=
  isBounded_subdifferential_iff_mem_interior_convexDom hf hp hx

/-- **Theorem 23.4** of [rockafellar1970convex], last clause. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $x \in \operatorname{ri}(\operatorname{dom} f)$. Then
$f'(x; y) < +\infty$ for every $y \in \mathbb{R}^n$ if and only if
$x \in \operatorname{int}(\operatorname{dom} f)$.

The source says that $f'(x; y)$ is finite for every $y$ when
$x \in \operatorname{int}(\operatorname{dom} f)$. Here "finite" is the condition
$\operatorname{dom} f'(x; \cdot) = \mathbb{R}^n$; the value $-\infty$ is excluded by
`Rockafellar.theorem_23_4_proper`. -/
theorem theorem_23_4_finite_iff {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    {x : Rn n}
    (hx : x ∈ ri (convexDom f)) : convexDom (dirDeriv f x) = univ ↔ x ∈ interior (convexDom f) :=
  convexDom_dirDeriv_eq_univ_iff_mem_interior_convexDom hf hp hx

/-!
### The set $\operatorname{dom} \partial f$ need not be convex

By Theorem 23.4, the set $\operatorname{dom} \partial f$ of points at which a proper convex function
has a subgradient lies between $\operatorname{ri}(\operatorname{dom} f)$ and $\operatorname{dom} f$.
The source observes on p. 218 that it need not be convex, and gives the example below.
-/

/-- **Section 23** of [rockafellar1970convex], the example of p. 218. The function on $\mathbb{R}^2$
$$f(\xi_1, \xi_2) = \max\{g(\xi_1), |\xi_2|\}, \qquad g(\xi_1) = \begin{cases} 1 - \xi_1^{1/2} &
  \text{if } \xi_1 \ge 0, \\ +\infty & \text{if } \xi_1 < 0. \end{cases}$$
Its effective domain is the closed right half-plane $\xi_1 \ge 0$. It has a subgradient at every
point of that half-plane except the points of the relative interior of the segment between
$(0, 1)$ and $(0, -1)$, so $\operatorname{dom} \partial f$ is not convex.

The coordinates $\xi_1, \xi_2$ are `x 0` and `x 1`. -/
noncomputable def nonsmoothMaxFn : Rn 2 → EReal :=
  ConvexAnalysis.convexRestrict {x : Rn 2 | 0 ≤ x 0}
    fun x => ((max (1 - Real.sqrt (x 0)) |x 1| : ℝ) : EReal)

private theorem convexOn_nonsmoothMax :
    ConvexOn ℝ {x : Rn 2 | 0 ≤ x 0} fun x => max (1 - Real.sqrt (x 0)) |x 1| := by
  have hconv : Convex ℝ {x : Rn 2 | 0 ≤ x 0} := by
    intro u hu v hv a b ha hb _
    have hu' : (0 : ℝ) ≤ u 0 := hu
    have hv' : (0 : ℝ) ≤ v 0 := hv
    have hcoord : (a • u + b • v) 0 = a * u 0 + b * v 0 := by simp
    change (0 : ℝ) ≤ (a • u + b • v) 0
    rw [hcoord]
    positivity
  refine ⟨hconv, fun u hu v hv a b ha hb hab => ?_⟩
  have hu' : (0 : ℝ) ≤ u 0 := hu
  have hv' : (0 : ℝ) ≤ v 0 := hv
  have hc0 : (a • u + b • v) 0 = a * u 0 + b * v 0 := by simp
  have hc1 : (a • u + b • v) 1 = a * u 1 + b * v 1 := by simp
  have hsqrt : a * Real.sqrt (u 0) + b * Real.sqrt (v 0)
      ≤ Real.sqrt (a * u 0 + b * v 0) := by
    have h := Real.strictConcaveOn_sqrt.concaveOn.2 (Set.mem_Ici.2 hu') (Set.mem_Ici.2 hv') ha hb
      hab
    simpa using h
  have habs : |a * u 1 + b * v 1| ≤ a * |u 1| + b * |v 1| := by
    calc |a * u 1 + b * v 1| ≤ |a * u 1| + |b * v 1| := abs_add_le _ _
      _ = a * |u 1| + b * |v 1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  simp only [hc0, hc1, smul_eq_mul]
  refine max_le ?_ ?_
  · have hexp : a * (1 - Real.sqrt (u 0)) + b * (1 - Real.sqrt (v 0))
        = 1 - (a * Real.sqrt (u 0) + b * Real.sqrt (v 0)) := by linear_combination hab
    have hstep : 1 - Real.sqrt (a * u 0 + b * v 0)
        ≤ a * (1 - Real.sqrt (u 0)) + b * (1 - Real.sqrt (v 0)) := by
      rw [hexp]; linarith
    exact hstep.trans (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb))
  · exact habs.trans (add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hb))

private theorem convexFn_nonsmoothMaxFn : ConvexFn nonsmoothMaxFn :=
  (convexOn_iff_convexFn _ _).1 convexOn_nonsmoothMax

private theorem nonsmoothMaxFn_of_nonneg {x : Rn 2} (hx : 0 ≤ x 0) :
    nonsmoothMaxFn x = ((max (1 - Real.sqrt (x 0)) |x 1| : ℝ) : EReal) :=
  ConvexAnalysis.convexRestrict_of_mem hx

private theorem nonsmoothMaxFn_of_neg {x : Rn 2} (hx : ¬ 0 ≤ x 0) : nonsmoothMaxFn x = ⊤ :=
  ConvexAnalysis.convexRestrict_of_notMem hx

private noncomputable def upperPoint : Rn 2 := WithLp.toLp 2 ![(0 : ℝ), 1]

private noncomputable def lowerPoint : Rn 2 := WithLp.toLp 2 ![(0 : ℝ), -1]

private theorem mem_subdifferential_upperPoint :
    upperPoint ∈ subdifferential (pairing 2) nonsmoothMaxFn upperPoint := by
  have h0 : upperPoint 0 = (0 : ℝ) := rfl
  have h1 : upperPoint 1 = (1 : ℝ) := rfl
  have hval : nonsmoothMaxFn upperPoint = ((1 : ℝ) : EReal) := by
    rw [nonsmoothMaxFn_of_nonneg (by rw [h0]), h0, h1]
    norm_num
  intro z
  rw [hval, pairing_two]
  simp only [PiLp.sub_apply, h0, h1]
  by_cases hz : 0 ≤ z 0
  · rw [nonsmoothMaxFn_of_nonneg hz]
    have : (1 : ℝ) + ((z 0 - 0) * 0 + (z 1 - 1) * 1) ≤ max (1 - Real.sqrt (z 0)) |z 1| := by
      have := le_max_right (1 - Real.sqrt (z 0)) |z 1|
      have hle : z 1 ≤ |z 1| := le_abs_self _
      linarith
    exact_mod_cast this
  · rw [nonsmoothMaxFn_of_neg hz]
    exact le_top

private theorem mem_subdifferential_lowerPoint :
    lowerPoint ∈ subdifferential (pairing 2) nonsmoothMaxFn lowerPoint := by
  have h0 : lowerPoint 0 = (0 : ℝ) := rfl
  have h1 : lowerPoint 1 = (-1 : ℝ) := rfl
  have hval : nonsmoothMaxFn lowerPoint = ((1 : ℝ) : EReal) := by
    rw [nonsmoothMaxFn_of_nonneg (by rw [h0]), h0, h1]
    norm_num
  intro z
  rw [hval, pairing_two]
  simp only [PiLp.sub_apply, h0, h1]
  by_cases hz : 0 ≤ z 0
  · rw [nonsmoothMaxFn_of_nonneg hz]
    have : (1 : ℝ) + ((z 0 - 0) * 0 + (z 1 - -1) * -1) ≤ max (1 - Real.sqrt (z 0)) |z 1| := by
      have := le_max_right (1 - Real.sqrt (z 0)) |z 1|
      have hle : -z 1 ≤ |z 1| := neg_le_abs _
      linarith
    exact_mod_cast this
  · rw [nonsmoothMaxFn_of_neg hz]
    exact le_top

/-- The function `Rockafellar.nonsmoothMaxFn` is finite at the origin, but its difference quotient
in the direction $(1, 0)$ behaves like $-\lambda^{-1/2}$, so $f'(0; (1, 0)) = -\infty$ and
$\partial f(0) = \emptyset$. -/
private theorem subdifferential_nonsmoothMaxFn_zero :
    subdifferential (pairing 2) nonsmoothMaxFn 0 = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  have hz0 : (0 : Rn 2) 0 = (0 : ℝ) := rfl
  have hz1 : (0 : Rn 2) 1 = (0 : ℝ) := rfl
  have hval : nonsmoothMaxFn 0 = ((1 : ℝ) : EReal) := by
    rw [nonsmoothMaxFn_of_nonneg (by rw [hz0]), hz0, hz1]
    norm_num
  set t : ℝ := 1 / (|y 0| + 1) with htdef
  have habs : (0 : ℝ) ≤ |y 0| := abs_nonneg _
  have hpos : (0 : ℝ) < |y 0| + 1 := by linarith
  have ht0 : 0 < t := by rw [htdef]; positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hpos]
    linarith
  set z : Rn 2 := WithLp.toLp 2 ![t ^ 2, (0 : ℝ)] with hzdef
  have hz0' : z 0 = t ^ 2 := rfl
  have hz1' : z 1 = (0 : ℝ) := rfl
  have hsq : Real.sqrt (z 0) = t := by rw [hz0', Real.sqrt_sq ht0.le]
  have hzval : nonsmoothMaxFn z = ((1 - t : ℝ) : EReal) := by
    rw [nonsmoothMaxFn_of_nonneg (by rw [hz0']; positivity), hsq, hz1']
    have : max (1 - t) |(0 : ℝ)| = 1 - t := by
      rw [abs_zero]
      exact max_eq_left (by linarith)
    rw [this]
  have hsub := hy z
  rw [hval, hzval, pairing_two] at hsub
  simp only [PiLp.sub_apply, hz0, hz1, hz0', hz1'] at hsub
  have hreal : (1 : ℝ) + ((t ^ 2 - 0) * y 0 + (0 - 0) * y 1) ≤ 1 - t := by exact_mod_cast hsub
  have hkey : t * y 0 ≤ -1 := by
    have h2 : t ^ 2 * y 0 ≤ -t := by nlinarith
    nlinarith [ht0]
  have hbound : -1 < t * y 0 := by
    have h1 : -(t * |y 0|) ≤ t * y 0 := by
      have := neg_abs_le (y 0)
      nlinarith [ht0.le]
    have h2 : t * |y 0| < 1 := by
      rw [htdef, div_mul_eq_mul_div, one_mul, div_lt_one hpos]
      linarith
    linarith
  linarith

/-- **Section 23** of [rockafellar1970convex], p. 218. For the proper convex function $f$ of
`Rockafellar.nonsmoothMaxFn`, the set $\operatorname{dom} \partial f$ of points at which $f$ has
a subgradient is not convex.

The set contains $(0, 1)$ and $(0, -1)$ but not their midpoint $(0, 0)$. This is why Theorem
23.4 can only place $\operatorname{dom} \partial f$ between
$\operatorname{ri}(\operatorname{dom} f)$ and $\operatorname{dom} f$. -/
theorem notConvex_domSubdifferential_nonsmoothMaxFn :
    ¬ Convex ℝ (domSubdifferential (pairing 2) nonsmoothMaxFn) := by
  intro hconv
  have hup : upperPoint ∈ domSubdifferential (pairing 2) nonsmoothMaxFn :=
    ⟨upperPoint, mem_subdifferential_upperPoint⟩
  have hlow : lowerPoint ∈ domSubdifferential (pairing 2) nonsmoothMaxFn :=
    ⟨lowerPoint, mem_subdifferential_lowerPoint⟩
  have hmid := hconv hup hlow (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  have hzero : (1/2 : ℝ) • upperPoint + (1/2 : ℝ) • lowerPoint = (0 : Rn 2) := by
    ext j
    fin_cases j <;> simp [upperPoint, lowerPoint]
  rw [hzero] at hmid
  obtain ⟨y, hy⟩ := hmid
  rw [subdifferential_nonsmoothMaxFn_zero] at hy
  exact hy

/-- The function `Rockafellar.nonsmoothMaxFn` is convex and proper, so the example of p. 218 has the
properties that the source claims. -/
theorem properConvex_convexFn_nonsmoothMaxFn : ConvexFn nonsmoothMaxFn
    ∧ ProperConvex nonsmoothMaxFn := by
  refine ⟨convexFn_nonsmoothMaxFn, ⟨⟨0, ?_⟩, fun x => ?_⟩⟩
  · have hz0 : (0 : Rn 2) 0 = (0 : ℝ) := rfl
    rw [mem_convexDom, nonsmoothMaxFn_of_nonneg (by rw [hz0])]
    exact EReal.coe_lt_top _
  · by_cases hx : 0 ≤ x 0
    · rw [nonsmoothMaxFn_of_nonneg hx]
      exact EReal.coe_ne_bot _
    · rw [nonsmoothMaxFn_of_neg hx]
      exact top_ne_bot

/-! ### Theorem 23.5: the four conditions, and the three starred ones -/

/-- **Theorem 23.5** of [rockafellar1970convex], condition (a). Let $f$ be a function on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and let $x, x^* \in \mathbb{R}^n$. Then
$x^* \in \partial f(x)$ if and only if
$$f(z) \ge f(x) + \langle z - x, x^* \rangle \quad \text{for every } z \in \mathbb{R}^n.$$

This is the definition of the subdifferential. It is stated separately so that the conditions of
the theorem form one list. The subgradient $x^*$ is `y`. -/
theorem theorem_23_5_a {f : Rn n → EReal} {x y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      ∀ z : Rn n, f x + ((pairing n (z - x) y : ℝ) : EReal) ≤ f z :=
  mem_subdifferential

/-- **Theorem 23.5** of [rockafellar1970convex], condition (b). Let $f$ be a function on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and let $x, x^* \in \mathbb{R}^n$. Then
$x^* \in \partial f(x)$ if and only if the function $z \mapsto \langle z, x^* \rangle - f(z)$
attains its supremum at $z = x$:
$$\langle z, x^* \rangle - f(z) \le \langle x, x^* \rangle - f(x) \quad \text{for every } z.$$

**Generalization.** The source states Theorem 23.5 for a proper convex function. Conditions (a),
(b) and (c) are equivalent for every $f$, because (b) is the subgradient inequality with the
terms moved to the other side. -/
theorem theorem_23_5_b {f : Rn n → EReal} {x y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      ∀ z : Rn n, ((pairing n z y : ℝ) : EReal) - f z ≤ ((pairing n x y : ℝ) : EReal) - f x :=
  mem_subdifferential_iff_forall_sub_le

/-- **Theorem 23.5** of [rockafellar1970convex], condition (c). Let $f$ be a function on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and let $x, x^* \in \mathbb{R}^n$. Then
$x^* \in \partial f(x)$ if and only if
$$f(x) + f^*(x^*) \le \langle x, x^* \rangle.$$

The supremum in (b) is $f^*(x^*)$, so this is (b) in another form, and no hypothesis on $f$ is
needed. See the generalization paragraph of `Rockafellar.theorem_23_5_b`. -/
theorem theorem_23_5_c {f : Rn n → EReal} {x y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      f x + convexConj (pairing n) f y ≤ ((pairing n x y : ℝ) : EReal) :=
  mem_subdifferential_iff_add_convexConj_le

/-- **Theorem 23.5** of [rockafellar1970convex], condition (d). Let $f$ be a proper function on
$\mathbb{R}^n$, and let $x, x^* \in \mathbb{R}^n$. Then $x^* \in \partial f(x)$ if and only if
$$f(x) + f^*(x^*) = \langle x, x^* \rangle.$$

**Generalization.** The source assumes that $f$ is proper and convex. Convexity is not needed.
Properness is needed: Fenchel's inequality $\langle x, x^* \rangle \le f(x) + f^*(x^*)$ is false
for $f \equiv +\infty$, because $(+\infty) + (-\infty) = -\infty$ in `EReal`. -/
theorem theorem_23_5_d {f : Rn n → EReal} (hp : ProperConvex f) {x y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      f x + convexConj (pairing n) f y = ((pairing n x y : ℝ) : EReal) :=
  hp.mem_subdifferential_iff_add_convexConj_eq

/-- **Theorem 23.5** of [rockafellar1970convex], condition (a*). Let $f$ be a convex function on
$\mathbb{R}^n$, and let $x$ be a point with $(\operatorname{cl} f)(x) = f(x)$. Then for every
$x^* \in \mathbb{R}^n$,
$$x \in \partial f^*(x^*) \iff x^* \in \partial f(x).$$

For convex $f$ the condition $(\operatorname{cl} f)(x) = f(x)$ is the condition
$f^{**}(x) = f(x)$ of the Fenchel–Moreau theorem. -/
theorem theorem_23_5_a_star {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n}
    (hx : convexCl f x = f x) {y : Rn n} :
    x ∈ subdifferential (pairing n) (convexConj (pairing n) f) y ↔
      y ∈ subdifferential (pairing n) f x := by
  have hbi : convexBiconj (pairing n) f x = f x := by rw [convexBiconj_eq_convexCl hf]; exact hx
  have h := mem_subdifferential_convexConj_iff (B := pairing n) (f := f) (x := x) (y := y) hbi
  rwa [flip_pairing] at h

/-- **Theorem 23.5** of [rockafellar1970convex], condition (b*). Let $f$ be a convex function on
$\mathbb{R}^n$, and let $x$ be a point with $(\operatorname{cl} f)(x) = f(x)$. Then
$x^* \in \partial f(x)$ if and only if the function
$z^* \mapsto \langle x, z^* \rangle - f^*(z^*)$ attains its supremum at $z^* = x^*$:
$$\langle x, z^* \rangle - f^*(z^*) \le \langle x, x^* \rangle - f^*(x^*) \quad \text{for every
  } z^*.$$
-/
theorem theorem_23_5_b_star {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n}
    (hx : convexCl f x = f x) {y : Rn n} :
    y ∈ subdifferential (pairing n) f x ↔
      ∀ w : Rn n, ((pairing n x w : ℝ) : EReal) - convexConj (pairing n) f w
        ≤ ((pairing n x y : ℝ) : EReal) - convexConj (pairing n) f y := by
  rw [← theorem_23_5_a_star hf hx, theorem_23_5_b]
  exact forall_congr' fun w => by rw [pairing_comm w x, pairing_comm y x]

/-- **Theorem 23.5** of [rockafellar1970convex], condition (a**). Let $f$ be a function on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and let $x$ be a point with
$(\operatorname{cl} f)(x) = f(x)$. Then $x^* \in \partial(\operatorname{cl} f)(x)$ if and only
if $x^* \in \partial f(x)$. -/
theorem theorem_23_5_a_star_star {f : Rn n → EReal} {x : Rn n} (hx : convexCl f x = f x)
    {y : Rn n} :
    y ∈ subdifferential (pairing n) (convexCl f) x ↔ y ∈ subdifferential (pairing n) f x :=
  mem_subdifferential_convexCl_iff hx

/-- **Corollary 23.5.1** of [rockafellar1970convex]. Let $f$ be a closed convex function on
$\mathbb{R}^n$. Then the multivalued mapping $\partial f^*$ is the inverse of $\partial f$:
$x \in \partial f^*(x^*)$ if and only if $x^* \in \partial f(x)$.

**Generalization.** The source assumes that $f$ is a closed proper convex function. Properness
is not needed.

The source gives no proof. The corollary follows from the equivalence of (a) and (a*) in Theorem
23.5, whose hypothesis $(\operatorname{cl} f)(x) = f(x)$ holds at every $x$ for closed $f$. The
graphs of the mappings are `ConvexAnalysis.subgradientRel`, and the inverse is `SetRel.inv`. -/
theorem corollary_23_5_1 {f : Rn n → EReal} (hf : ConvexFn f) (hc : ClosedConvex f) :
    subgradientRel (pairing n) (convexConj (pairing n) f) = (subgradientRel (pairing n) f).inv := by
  have h := subgradientRel_convexConj_eq_inv (B := pairing n) hf hc
  rwa [flip_pairing] at h

/-- **Corollary 23.5.1** of [rockafellar1970convex], pointwise form. Let $f$ be a closed convex
function on $\mathbb{R}^n$. Then for all $x, x^* \in \mathbb{R}^n$, $x \in \partial f^*(x^*)$ if
and only if $x^* \in \partial f(x)$. -/
theorem corollary_23_5_1_mem {f : Rn n → EReal} (hf : ConvexFn f) (hc : ClosedConvex f)
    {x y : Rn n} :
    x ∈ subdifferential (pairing n) (convexConj (pairing n) f) y ↔
      y ∈ subdifferential (pairing n) f x := by
  have h :=
      mem_subdifferential_convexConj_iff_of_closedConvex (B := pairing n) (x := x) (y := y) hf hc
  rwa [flip_pairing] at h

/-- **Corollary 23.5.2** of [rockafellar1970convex], first assertion. Let $f$ be a convex function
on $\mathbb{R}^n$. If $\partial f(x) \ne \emptyset$, then $(\operatorname{cl} f)(x) = f(x)$.

**Generalization.** The source assumes that $f$ is proper. This is not needed. -/
theorem corollary_23_5_2_clFn {f : Rn n → EReal} (hf : ConvexFn f) {x y : Rn n}
    (hy : y ∈ subdifferential (pairing n) f x) : convexCl f x = f x :=
  convexCl_eq_of_mem_subdifferential hf hy

/-- **Corollary 23.5.2** of [rockafellar1970convex], second assertion. Let $f$ be a convex function
on $\mathbb{R}^n$. If $\partial f(x) \ne \emptyset$, then $\partial(\operatorname{cl} f)(x) =
\partial f(x)$.

**Generalization.** The source assumes that $f$ is proper. This is not needed. -/
theorem corollary_23_5_2_subdifferential {f : Rn n → EReal} (hf : ConvexFn f) {x y : Rn n}
    (hy : y ∈ subdifferential (pairing n) f x) :
    subdifferential (pairing n) (convexCl f) x = subdifferential (pairing n) f x :=
  subdifferential_convexCl hf hy

/-- **Corollary 23.5.3** of [rockafellar1970convex]. Let $C$ be a nonempty closed convex set in
$\mathbb{R}^n$, and let $x^* \in \mathbb{R}^n$. Then $\partial \delta^*(x^* \mid C)$ is the set
of points $x \in C$ at which the linear function $\langle \cdot, x^* \rangle$ attains its
maximum over $C$:
$$\partial \delta^*(x^* \mid C) = \{x \in C \mid \langle z, x^* \rangle \le \langle x, x^*
  \rangle \text{ for every } z \in C\}.$$

The set may be empty. -/
theorem corollary_23_5_3 {C : Set (Rn n)} (hC : IsClosed C) (hCc : Convex ℝ C)
    (hCne : C.Nonempty) (y : Rn n) :
    subdifferential (pairing n) (supportFn (pairing n) C) y
      = {x ∈ C | ∀ z ∈ C, pairing n z y ≤ pairing n x y} := by
  have h := subdifferential_supportFn (B := pairing n) hC hCc hCne y
  rwa [flip_pairing] at h

private theorem normalCone_zero (C : Set (Rn n)) :
    normalCone (pairing n) C 0 = polarCone (pairing n) C := by
  ext y
  simp only [mem_normalCone, mem_polarCone, sub_zero]

/-- **Corollary 23.5.4** of [rockafellar1970convex]. Let $K$ be a convex cone in $\mathbb{R}^n$
containing the origin. Then $x^* \in \partial \delta(x \mid K)$ if and only if
$$x \in K, \qquad x^* \in K^\circ, \qquad \langle x, x^* \rangle = 0.$$

**Generalization.** The source assumes that $K$ is nonempty and closed. Neither hypothesis is
needed. The source derives the corollary from $\delta(\cdot \mid K)^* = \delta(\cdot \mid
K^\circ)$, which needs closedness, but the subgradient inequality at $z = 0$ and $z = x + x$
gives the result directly.

The cone $K$ is a `PointedCone`, which always contains the origin. -/
theorem corollary_23_5_4 (K : PointedCone ℝ (Rn n)) {x y : Rn n} :
    y ∈ subdifferential (pairing n) (indicatorFn (K : Set (Rn n))) x ↔
      x ∈ K ∧ y ∈ polarCone (pairing n) (K : Set (Rn n)) ∧ pairing n x y = 0 := by
  rw [mem_subdifferential_indicatorFn_pointedCone, normalCone_zero]

/-- **Corollary 23.5.4** of [rockafellar1970convex], duality. Let $K$ be a closed convex cone in
$\mathbb{R}^n$ containing the origin. Then $x^* \in \partial \delta(x \mid K)$ if and only if
$x \in \partial \delta(x^* \mid K^\circ)$.

Both sides reduce to the three conditions of `Rockafellar.corollary_23_5_4` once
$K^{\circ\circ} = K$ (Theorem 14.1) identifies the polar of $K^\circ$ with $K$. Closedness is
used only for this identification. -/
theorem corollary_23_5_4_inv {K : PointedCone ℝ (Rn n)} (hK : IsClosed (K : Set (Rn n)))
    {x y : Rn n} :
    y ∈ subdifferential (pairing n) (indicatorFn (K : Set (Rn n))) x ↔
      x ∈ subdifferential (pairing n)
        (indicatorFn (polarPointedCone (pairing n) (K : Set (Rn n)) : Set (Rn n))) y := by
  have hbi : polarCone (pairing n) (polarCone (pairing n) (K : Set (Rn n)))
      = (K : Set (Rn n)) := by
    have h := polarCone_polarCone_pointedCone (B := pairing n) K hK
    rwa [flip_pairing] at h
  rw [corollary_23_5_4, corollary_23_5_4 (polarPointedCone (pairing n) (K : Set (Rn n)))]
  rw [coe_polarPointedCone, hbi]
  constructor
  · rintro ⟨hx, hy, h0⟩
    exact ⟨hy, hx, by rw [pairing_comm]; exact h0⟩
  · rintro ⟨hy, hx, h0⟩
    exact ⟨hx, hy, by rw [pairing_comm]; exact h0⟩

/-! ### Theorem 23.6: $\varepsilon$-subgradients -/

/-- **Section 23** of [rockafellar1970convex], before Theorem 23.6. Let $f$ be a function on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$, and let $x$ be a point where $f$ is finite.
Then for every $\varepsilon \in \mathbb{R}$ the set
$$\partial_\varepsilon f(x) = \{x^* \mid f(z) \ge f(x) + \langle z - x, x^* \rangle -
  \varepsilon \text{ for every } z\}$$
is closed and convex.

The set is $\{x^* \mid h^*(x^*) \le \varepsilon\}$ for $h(y) = f(x + y) - f(x)$. -/
theorem epsSubdifferential_convex_closed {f : Rn n → EReal} {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (ε : ℝ) :
    Convex ℝ (epsSubdifferential (pairing n) ε f x) ∧
      IsClosed (epsSubdifferential (pairing n) ε f x) :=
  ⟨convex_epsSubdifferential hr ε, isClosed_epsSubdifferential hr ε⟩

/-- **Section 23** of [rockafellar1970convex], before Theorem 23.6. For every function $f$ on
$\mathbb{R}^n$ with values in $[-\infty, +\infty]$ and every $x$, the intersection of the sets
$\partial_\varepsilon f(x)$ over $\varepsilon > 0$ is $\partial f(x)$. -/
theorem epsSubdifferential_iInter (f : Rn n → EReal) (x : Rn n) :
    ⋂ ε ∈ Ioi (0 : ℝ), epsSubdifferential (pairing n) ε f x = subdifferential (pairing n) f x :=
  iInter_epsSubdifferential (pairing n) f x

/-- **Theorem 23.6** of [rockafellar1970convex]. Let $f$ be a closed proper convex function on
$\mathbb{R}^n$, and let $x$ be a point where $f$ is finite. Then for every $y \in \mathbb{R}^n$,
$$f'(x; y) = \lim_{\varepsilon \downarrow 0} \delta^*(y \mid \partial_\varepsilon f(x)).$$

The sets $\partial_\varepsilon f(x)$ increase with $\varepsilon$, so the limit is written as the
infimum over $\varepsilon > 0$. "Closed" is the hypothesis that the epigraph of $f$ is closed,
which for a proper convex function is the same condition. -/
theorem theorem_23_6 {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    (hc : IsClosed (epi f)) {x : Rn n} {r : ℝ} (hr : f x = (r : EReal)) (v : Rn n) :
    ⨅ ε ∈ Ioi (0 : ℝ), supportFn (pairing n) (epsSubdifferential (pairing n) ε f x) v
      = dirDeriv f x v := by
  have h := dirDeriv_eq_iInf_supportFn_epsSubdifferential (B := pairing n) hf hp hc hr v
  simpa only [flip_pairing] using h

/-! ### Theorem 23.7: normals to a level set -/

/-- **Theorem 23.7** of [rockafellar1970convex]. Let $f$ be a convex function on $\mathbb{R}^n$, let
$x$ be a point where $f$ is finite and $\partial f(x) \ne \emptyset$, and assume that $f$ does
not attain its minimum at $x$: $\inf_z f(z) < f(x)$. Then the normal cone to
$C = \{z \mid f(z) \le f(x)\}$ at $x$ is the closure of the convex cone generated by
$\partial f(x)$:
$$N_C(x) = \operatorname{cl} \operatorname{cone} \partial f(x).$$

The source assumes $f$ proper. Here properness is not a hypothesis: it follows from
$\partial f(x) \ne \emptyset$ by Theorem 23.3. The cone generated by $\partial f(x)$ is
`PointedCone.hull`, which contains the origin. -/
theorem theorem_23_7 {f : Rn n → EReal} (hf : ConvexFn f) {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (hinf : ⨅ z, f z < (r : EReal))
    (hne : (subdifferential (pairing n) f x).Nonempty) :
    normalCone (pairing n) {z | f z ≤ (r : EReal)} x
      = closure ((PointedCone.hull ℝ (subdifferential (pairing n) f x) : Set (Rn n))) :=
  normalCone_setOf_le_eq_closure_coe_hull_subdifferential hf hr hinf hne

/-- **Corollary 23.7.1** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $x \in \operatorname{int}(\operatorname{dom} f)$ be a point at which $f$
does not attain its minimum. Then the normal cone to $C = \{z \mid f(z) \le f(x)\}$ at $x$ is
the convex cone generated by $\partial f(x)$, without closure.

The closure is not needed because $\partial f(x)$ is then nonempty, closed, bounded and does not
contain the origin, so Corollary 9.6.1 applies. -/
theorem corollary_23_7_1 {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    {x : Rn n} {r : ℝ}
    (hr : f x = (r : EReal)) (hinf : ⨅ z, f z < (r : EReal)) (hx : x ∈ interior (convexDom f)) :
    normalCone (pairing n) {z | f z ≤ (r : EReal)} x
      = (PointedCone.hull ℝ (subdifferential (pairing n) f x) : Set (Rn n)) :=
  normalCone_setOf_le_eq_coe_hull_subdifferential_of_mem_interior_convexDom hf hp hr hinf hx

/-- **Corollary 23.7.1** of [rockafellar1970convex], in the words of the source. Let $f$ be a proper
convex function on $\mathbb{R}^n$, and let $x \in \operatorname{int}(\operatorname{dom} f)$ be a
point at which $f$ does not attain its minimum. Then $x^*$ is normal to
$C = \{z \mid f(z) \le f(x)\}$ at $x$ if and only if $x^* \in \lambda \partial f(x)$ for some
$\lambda \ge 0$.

The convex cone generated by a nonempty convex set is the union of its nonnegative multiples
(Corollary 9.6.1), and $\partial f(x)$ is nonempty here. -/
theorem corollary_23_7_1_smul {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f) {x : Rn n}
    {r : ℝ} (hr : f x = (r : EReal)) (hinf : ⨅ z, f z < (r : EReal))
    (hx : x ∈ interior (convexDom f)) {y : Rn n} :
    y ∈ normalCone (pairing n) {z | f z ≤ (r : EReal)} x ↔
      ∃ a : ℝ, 0 ≤ a ∧ y ∈ a • subdifferential (pairing n) f x := by
  have hri : x ∈ ri (convexDom f) := interior_subset_intrinsicInterior hx
  obtain ⟨y₀, hy₀⟩ := theorem_23_4_nonempty hf hp hri
  rw [corollary_23_7_1 hf hp hr hinf hx,
    mem_coe_hull_iff_of_convex (convex_subdifferential (pairing n) f x)]
  constructor
  · rintro (rfl | ⟨t, ht, hmem⟩)
    · exact ⟨0, le_rfl, ⟨y₀, hy₀, by simp⟩⟩
    · exact ⟨t, ht.le, hmem⟩
  · rintro ⟨a, ha, hmem⟩
    rcases eq_or_lt_of_le ha with rfl | ha'
    · obtain ⟨w, -, hw⟩ := hmem
      exact Or.inl (by rw [← hw]; simp)
    · exact Or.inr ⟨a, ha', hmem⟩

/-! ### Theorem 23.8: the sum rule -/

/-- **Theorem 23.8** of [rockafellar1970convex], the inclusion. For all functions $f_1, \dots, f_m$
on $\mathbb{R}^n$ with values in $[-\infty, +\infty]$ and every $x$,
$$\partial f_1(x) + \dots + \partial f_m(x) \subseteq \partial(f_1 + \dots + f_m)(x).$$

No hypothesis is needed: the $m$ subgradient inequalities add. -/
theorem theorem_23_8_subset {ι : Type*} (s : Finset ι) (f : ι → Rn n → EReal) (x : Rn n) :
    ∑ i ∈ s, subdifferential (pairing n) (f i) x ⊆ subdifferential (pairing n) (∑ i ∈ s, f i) x :=
  subdifferential_finsetSum_subset (pairing n) s f x

/-- **Theorem 23.8** of [rockafellar1970convex]. Let $f_1, \dots, f_m$, $m \ge 1$, be proper convex
functions on $\mathbb{R}^n$, and assume that the sets
$\operatorname{ri}(\operatorname{dom} f_i)$, $i = 1, \dots, m$, have a point in common. Then for
every $x \in \mathbb{R}^n$,
$$\partial(f_1 + \dots + f_m)(x) = \partial f_1(x) + \dots + \partial f_m(x).$$

The functions are indexed by a nonempty finite set `s`. The proof does not use induction on $m$:
the qualification condition is used once, through the $m$-ary form of Theorem 16.4. The
alternative proof of the source (p. 220) is more elementary, by proper separation of
$\{(x, \mu) \mid \mu \ge f_1(x)\}$ from $\{(x, \mu) \mid \mu \le -f_2(x)\}$ in
$\mathbb{R}^{n+1}$, but it reduces to $m = 2$ by induction. -/
theorem theorem_23_8 {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → Rn n → EReal}
    (hf : ∀ i ∈ s, ConvexFn (f i)) (hpf : ∀ i ∈ s, ProperConvex (f i)) {x₀ : Rn n}
    (hx₀ : ∀ i ∈ s, x₀ ∈ ri (convexDom (f i))) (x : Rn n) :
    subdifferential (pairing n) (∑ i ∈ s, f i) x = ∑ i ∈ s, subdifferential (pairing n) (f i) x :=
  (IsExactFinsetSum.of_relint hs hf hpf hx₀).subdifferential_finsetSum x

/-- **Theorem 23.8** of [rockafellar1970convex], the polyhedral case. Let $f_1, \dots, f_m$,
$m \ge 1$, be proper convex functions on $\mathbb{R}^n$ such that $f_1, \dots, f_k$ are
polyhedral, and assume that the sets
$$\operatorname{dom} f_1, \ \dots, \ \operatorname{dom} f_k, \
  \operatorname{ri}(\operatorname{dom} f_{k+1}), \ \dots, \ \operatorname{ri}(\operatorname{dom}
  f_m)$$
have a point in common. Then $\partial(f_1 + \dots + f_m)(x) = \partial f_1(x) + \dots +
\partial f_m(x)$ for every $x \in \mathbb{R}^n$.

The index sets $\{1, \dots, k\}$ and $\{k + 1, \dots, m\}$ are `t` and `u`. The proof uses
Theorem 20.1. The alternative proof of the source does not cover this case. -/
theorem theorem_23_8_polyhedral {ι : Type*} {s t u : Finset ι} (hs : s.Nonempty)
    (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u) {f : ι → Rn n → EReal}
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, ProperConvex (f i)) {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ convexDom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (convexDom (f i))) (x : Rn n) :
    subdifferential (pairing n) (∑ i ∈ s, f i) x = ∑ i ∈ s, subdifferential (pairing n) (f i) x :=
  (IsExactFinsetSum.of_polyhedral hs hdisj hmem hpoly hconv hpf hxt hxu).subdifferential_finsetSum x

/-! ### Corollary 23.8.1: normals to an intersection -/

private theorem biInter_cons {ι : Type*} {i : ι} {t : Finset ι} (hi : i ∉ t)
    (C : ι → Set (Rn n)) : (⋂ j ∈ Finset.cons i t hi, C j) = C i ∩ ⋂ j ∈ t, C j := by
  ext z
  simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_cons]
  constructor
  · intro hz
    exact ⟨hz i (Or.inl rfl), fun j hj => hz j (Or.inr hj)⟩
  · rintro ⟨h₁, h₂⟩ j (rfl | hj)
    · exact h₁
    · exact h₂ j hj

/-- **Corollary 23.8.1** of [rockafellar1970convex], the inclusion. For all sets $C_1, \dots, C_m$
in $\mathbb{R}^n$ and every $x \in \mathbb{R}^n$, the sum of the normal cones $N_{C_i}(x)$ is
contained in the normal cone to $C_1 \cap \dots \cap C_m$ at $x$.

The normal cone is `ConvexAnalysis.normalCone`, which is defined at every point, and no
hypothesis is needed. -/
theorem corollary_23_8_1_subset {ι : Type*} (C : ι → Set (Rn n)) (x : Rn n) :
    ∀ s : Finset ι,
      ∑ i ∈ s, normalCone (pairing n) (C i) x ⊆ normalCone (pairing n) (⋂ i ∈ s, C i) x := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro y hy
      simp only [Finset.sum_empty, Set.mem_zero] at hy
      subst hy
      simp
  | cons i t hi ih =>
      rw [Finset.sum_cons, biInter_cons hi C]
      exact (Set.add_subset_add_left ih).trans (normalCone_add_subset (pairing n) (C i) _ x)

/-- **Corollary 23.8.1** of [rockafellar1970convex]. Let $C_1, \dots, C_m$, $m \ge 1$, be convex
sets in $\mathbb{R}^n$ whose relative interiors have a point in common, and let
$x \in C_1 \cap \dots \cap C_m$. Then
$$N(x \mid C_1 \cap \dots \cap C_m) = N(x \mid C_1) + \dots + N(x \mid C_m).$$

**Reading.** The source does not assume $x \in C_i$. Its normal cone
$N_C(x) = \partial \delta(x \mid C)$ is empty for $x \notin C$, while
`ConvexAnalysis.normalCone` is defined at every point and always contains $0$. The two agree
exactly on $C$, so the hypothesis $x \in C_i$ cannot be removed from this statement.

This is the case of indicator functions in Theorem 23.8. -/
theorem corollary_23_8_1 {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {C : ι → Set (Rn n)}
    (hC : ∀ i ∈ s, Convex ℝ (C i)) {x₀ : Rn n} (hx₀ : ∀ i ∈ s, x₀ ∈ ri (C i)) {x : Rn n}
    (hx : ∀ i ∈ s, x ∈ C i) :
    normalCone (pairing n) (⋂ i ∈ s, C i) x = ∑ i ∈ s, normalCone (pairing n) (C i) x := by
  have hconv : ∀ i ∈ s, ConvexFn (indicatorFn (C i)) :=
    fun i hi => convexFn_indicatorFn.2 (hC i hi)
  have hprop : ∀ i ∈ s, ProperConvex (indicatorFn (C i)) := fun i hi =>
    ⟨⟨x, by rw [convexDom_indicatorFn]; exact hx i hi⟩, indicatorFn_ne_bot (C i)⟩
  have hri : ∀ i ∈ s, x₀ ∈ ri (convexDom (indicatorFn (C i))) := by
    intro i hi
    rw [convexDom_indicatorFn]
    exact hx₀ i hi
  have hsum := theorem_23_8 hs hconv hprop hri x
  rw [indicatorFn_finsetSum C s,
    subdifferential_indicatorFn (Set.mem_iInter₂.2 hx)] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun i hi => subdifferential_indicatorFn (hx i hi)

/-! ### Theorem 23.9: composition with a linear transformation -/

/-- **Theorem 23.9** of [rockafellar1970convex], the inclusion. Let
$A : \mathbb{R}^n \to \mathbb{R}^m$ be linear, let $h$ be a function on $\mathbb{R}^m$ with
values in $[-\infty, +\infty]$, and let $f(x) = h(Ax)$. Then for every $x$,
$$A^* \partial h(Ax) \subseteq \partial f(x).$$

No hypothesis on $h$ is needed; the proof uses only the adjointness of $A^*$. -/
theorem theorem_23_9_subset (A : Rn n →ₗ[ℝ] Rn m) (h : Rn m → EReal) (x : Rn n) :
    LinearMap.adjoint A '' subdifferential (pairing m) h (A x)
      ⊆ subdifferential (pairing n) (compLin h A) x :=
  image_subdifferential_subset (isAdjointPair_adjoint A) h x

/-- **Theorem 23.9** of [rockafellar1970convex]. Let $A : \mathbb{R}^n \to \mathbb{R}^m$ be linear,
let $h$ be a proper convex function on $\mathbb{R}^m$, and let $f(x) = h(Ax)$. If the range of
$A$ contains a point of $\operatorname{ri}(\operatorname{dom} h)$, then for every
$x \in \mathbb{R}^n$,
$$\partial f(x) = A^* \partial h(Ax).$$

The proof applies Theorem 23.5 to the conjugacy formula of Theorem 16.3. The transpose $A^*$ is
`LinearMap.adjoint A`, and $f$ is `ConvexAnalysis.compLin h A`. -/
theorem theorem_23_9 (A : Rn n →ₗ[ℝ] Rn m) {h : Rn m → EReal} (hh : ConvexFn h)
    (hp : ProperConvex h)
    {x₀ : Rn n} (hx₀ : A x₀ ∈ ri (convexDom h)) (x : Rn n) :
    subdifferential (pairing n) (compLin h A) x
      = LinearMap.adjoint A '' subdifferential (pairing m) h (A x) :=
  (IsExactImage.of_relint (isAdjointPair_adjoint A) hh hp hx₀).subdifferential_compLin x

/-- **Theorem 23.9** of [rockafellar1970convex], the polyhedral case. Let
$A : \mathbb{R}^n \to \mathbb{R}^m$ be linear, let $h$ be a proper polyhedral convex function on
$\mathbb{R}^m$, and let $f(x) = h(Ax)$. If the range of $A$ meets $\operatorname{dom} h$, then
$\partial f(x) = A^* \partial h(Ax)$ for every $x \in \mathbb{R}^n$.

The proof follows the source: Theorem 16.3 through Corollary 19.3.1. -/
theorem theorem_23_9_polyhedral (A : Rn n →ₗ[ℝ] Rn m) {h : Rn m → EReal} (hh : PolyhedralFn h)
    (hp : ProperConvex h) {x₀ : Rn n} (hx₀ : A x₀ ∈ convexDom h) (x : Rn n) :
    subdifferential (pairing n) (compLin h A) x
      = LinearMap.adjoint A '' subdifferential (pairing m) h (A x) :=
  (IsExactImage.of_polyhedral (isAdjointPair_adjoint A) hh hp hx₀).subdifferential_compLin x

/-! ### Theorem 23.10: the polyhedral case -/

/-- **Theorem 23.10** of [rockafellar1970convex], existence. Let $f$ be a polyhedral convex function
on $\mathbb{R}^n$, and let $x$ be a point where $f$ is finite. Then
$\partial f(x) \ne \emptyset$.

No relative interior condition is needed: the cone generated by
$\operatorname{epi} f - (x, f(x))$ is polyhedral, hence closed (Corollary 19.7.1), so
$f'(x; \cdot)$ is already closed. -/
theorem theorem_23_10_nonempty {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : (subdifferential (pairing n) f x).Nonempty :=
  subdifferential_nonempty_of_polyhedralFn hf ht hb

/-- **Theorem 23.10** of [rockafellar1970convex], polyhedrality of the subdifferential. Let $f$ be a
polyhedral convex function on $\mathbb{R}^n$, and let $x$ be a point where $f$ is finite. Then
$\partial f(x)$ is a polyhedral convex set. -/
theorem theorem_23_10_polyhedral {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : Polyhedral (subdifferential (pairing n) f x) :=
  polyhedral_subdifferential_of_polyhedralFn hf ht hb

/-- **Theorem 23.10** of [rockafellar1970convex], polyhedrality of the directional derivative. Let
$f$ be a polyhedral convex function on $\mathbb{R}^n$, and let $x$ be a point where $f$ is
finite. Then $f'(x; \cdot)$ is a polyhedral convex function. -/
theorem theorem_23_10_dirDeriv_polyhedral {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : PolyhedralFn (dirDeriv f x) :=
  polyhedralFn_dirDeriv hf ht hb

/-- **Theorem 23.10** of [rockafellar1970convex], properness of the directional derivative. Let $f$
be a polyhedral convex function on $\mathbb{R}^n$, and let $x$ be a point where $f$ is finite.
Then $f'(x; \cdot)$ is proper.

The reason in the source: $f'(x; 0) = 0$, and a polyhedral convex function that takes the value
$-\infty$ somewhere has no finite values. -/
theorem theorem_23_10_dirDeriv_proper {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) : ProperConvex (dirDeriv f x) :=
  properConvex_dirDeriv_of_polyhedralFn hf ht hb

/-- **Theorem 23.10** of [rockafellar1970convex], the support function formula. Let $f$ be a
polyhedral convex function on $\mathbb{R}^n$, and let $x$ be a point where $f$ is finite. Then
$f'(x; \cdot) = \delta^*(\cdot \mid \partial f(x))$, with no closure operation. -/
theorem theorem_23_10_supportFn {f : Rn n → EReal} (hf : PolyhedralFn f) {x : Rn n}
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    dirDeriv f x = supportFn (pairing n) (subdifferential (pairing n) f x) := by
  have h := dirDeriv_eq_supportFn_of_polyhedralFn (B := pairing n) hf ht hb
  rwa [flip_pairing] at h

end Rockafellar
