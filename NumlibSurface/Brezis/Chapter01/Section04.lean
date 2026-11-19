/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Continuity
import Numlib.Analysis.Convex.Extremum.Fenchel
import NumlibSurface.Brezis.Chapter01.Section03

/-!
# Brezis, Section 1.4: A quick introduction to the theory of conjugate convex functions

This module formalizes Section 1.4 of [brezis2011functional] for a real normed space $E$ with dual
$E^\star$ and the pairing $\langle f, x \rangle = f(x)$. A function
$\varphi : E \to (-\infty, +\infty]$ has the domain $D(\varphi) = \{x : \varphi(x) < +\infty\}$ and
the epigraph $\operatorname{epi} \varphi = \{[x, \lambda] \in E \times \mathbb{R} : \varphi(x) \le
\lambda\}$. Its conjugate is the function $\varphi^\star : E^\star \to (-\infty, +\infty]$,
$$\varphi^\star(f) = \sup_{x \in E} \{\langle f, x \rangle - \varphi(x)\},$$
which is convex and lower semicontinuous and satisfies Young's inequality $\langle f, x \rangle \le
\varphi(x) + \varphi^\star(f)$. If $\varphi$ is convex, lower semicontinuous and
$\varphi \not\equiv +\infty$, then $\varphi^\star \not\equiv +\infty$ (Proposition 1.10), and
$\varphi^{\star\star} = \varphi$ (Theorem 1.11, Fenchel–Moreau). The Fenchel–Rockafellar theorem
(Theorem 1.12) gives
$$\inf_{x \in E} \{\varphi(x) + \psi(x)\} = \max_{f \in E^\star} \{-\varphi^\star(-f) -
  \psi^\star(f)\}$$
for convex $\varphi$ and $\psi$ when $\varphi$ is continuous at a point of
$D(\varphi) \cap D(\psi)$. Examples 1 to 4 compute conjugates of the norm and of indicator
functions, and derive formulas for the distance to a convex set and to a subspace.

The proofs specialize the backbone convex analysis library, the modules
`Numlib.Analysis.Convex.Duality.Conjugate`, `Numlib.Analysis.Convex.Duality.Continuity` and
`Numlib.Analysis.Convex.Extremum.Fenchel`, read over the pairing of $E$ with $E^\star$.

## Main definitions

* Section 1.4, the domain, `Brezis.Chapter01.mem_domain_iff`: $D(\varphi)$ is the backbone
  `ConvexAnalysis.convexDom`.
* Section 1.4, the epigraph, `Brezis.Chapter01.mem_epigraph_iff`: $\operatorname{epi} \varphi$ is
  the backbone `ConvexAnalysis.epi`.
* Section 1.4, definition of lower semicontinuity, `Brezis.Chapter01.lowerSemicontinuous_iff`: every
  sublevel set $[\varphi \le \lambda]$ is closed.
* Section 1.4, definition of a convex function, `Brezis.Chapter01.convexFn_iff`: the inequality
  $\varphi(tx + (1-t)y) \le t\varphi(x) + (1-t)\varphi(y)$.
* Section 1.4, the scalar product of the duality, `Brezis.Chapter01.dualPairing`:
  $\langle f, x \rangle = f(x)$.
* Section 1.4, definition of the conjugate function, `Brezis.Chapter01.conjugate`:
  $\varphi^\star(f) = \sup_x \{\langle f, x \rangle - \varphi(x)\}$.
* Section 1.4, definition of the biconjugate, `Brezis.Chapter01.biconjugate`:
  $\varphi^{\star\star}(x) = \sup_f \{\langle f, x \rangle - \varphi^\star(f)\}$ for $x \in E$.

## Main results

* Section 1.4, `Brezis.Chapter01.conjugate_convexFn`: $\varphi^\star$ is convex.
* Section 1.4, `Brezis.Chapter01.conjugate_lowerSemicontinuous`: $\varphi^\star$ is lower
  semicontinuous.
* Remark 7, `Brezis.Chapter01.remark_1_7`: Young's inequality (11), $\langle f, x \rangle \le
  \varphi(x) + \varphi^\star(f)$.
* Remark 7, `Brezis.Chapter01.remark_1_7_classical`: the classical Young inequality (12),
  $ab \le a^p/p + b^{p'}/p'$.
* Proposition 1.10, `Brezis.Chapter01.proposition_1_10`: if $\varphi$ is convex, lower
  semicontinuous and $\varphi \not\equiv +\infty$, then $\varphi^\star \not\equiv +\infty$.
* Proposition 1.10, `Brezis.Chapter01.proposition_1_10_affine`: such a $\varphi$ is bounded below by
  a continuous affine function.
* Theorem 1.11, `Brezis.Chapter01.theorem_1_11`: if $\varphi$ is convex, lower semicontinuous and
  $\varphi \not\equiv +\infty$, then $\varphi^{\star\star} = \varphi$ (Fenchel–Moreau).
* Example 1, `Brezis.Chapter01.example_1_1_conj`: the conjugate of the norm is the indicator
  function of the closed unit ball of $E^\star$.
* Example 1, `Brezis.Chapter01.example_1_1_biconj`: $\|x\| = \varphi^{\star\star}(x) = \sup_{\|f\|
  \le 1} \langle f, x \rangle$.
* Example 2, `Brezis.Chapter01.example_1_2_convexFn_iff`: $I_K$ is convex if and only if $K$ is
  convex.
* Example 2, `Brezis.Chapter01.example_1_2_lowerSemicontinuous_iff`: $I_K$ is lower semicontinuous
  if and only if $K$ is closed.
* Example 2, `Brezis.Chapter01.example_1_2_conj`: $(I_M)^\star = I_{M^\perp}$ for a linear subspace
  $M$.
* Example 2, `Brezis.Chapter01.example_1_2_biconj`: $(I_M)^{\star\star} = I_{(M^\perp)^\perp}$.
* Example 2, `Brezis.Chapter01.example_1_2_orthogonal`: $(M^\perp)^\perp = M$ for a closed linear
  subspace $M$.
* Theorem 1.12, `Brezis.Chapter01.theorem_1_12`: $\inf_x \{\varphi(x) + \psi(x)\} = \sup_f
  \{-\varphi^\star(-f) - \psi^\star(f)\}$ (Fenchel–Rockafellar).
* Theorem 1.12, `Brezis.Chapter01.theorem_1_12_max`: the supremum in Theorem 1.12 is attained.
* Lemma 1.4, `Brezis.Chapter01.lemma_1_4_convex`: the interior of a convex set is convex.
* Lemma 1.4, `Brezis.Chapter01.lemma_1_4`: if $C$ is convex and
  $\operatorname{Int} C \neq \emptyset$, then $\overline{C} = \overline{\operatorname{Int} C}$.
* Example 3, `Brezis.Chapter01.example_1_3`: formula (19), $\operatorname{dist}(x_0, K) =
  \max_{\|f\| \le 1} \{\langle f, x_0 \rangle - I_K^\star(f)\}$.
* Example 3, `Brezis.Chapter01.example_1_3_submodule`: $\operatorname{dist}(x_0, M) = \max_{f \in
  M^\perp,\ \|f\| \le 1} \langle f, x_0 \rangle$.
* Example 3, `Brezis.Chapter01.example_1_3_submodule_of_example_1_3`: the same formula, derived from
  (19).
* Example 4, `Brezis.Chapter01.example_1_4`: $\inf_{x \in M} \varphi(x) = -\min_{f \in M^\perp}
  \varphi^\star(f)$ for a convex continuous $\varphi$.

## Conventions

* A function $\varphi : E \to (-\infty, +\infty]$ is `φ : E → EReal` with `∀ x, φ x ≠ ⊥`. The
  condition $\varphi \not\equiv +\infty$ is `(ConvexAnalysis.convexDom φ).Nonempty`. The two
  conditions together are `ConvexAnalysis.ProperConvex φ`.
* "Lower semicontinuous" is Mathlib's `LowerSemicontinuous`. For a function that never takes the
  value $-\infty$, it is the backbone `ConvexAnalysis.ClosedConvex`, by
  `ConvexAnalysis.closedConvex_iff_lowerSemicontinuous`.
* "Convex" is the backbone `ConvexAnalysis.ConvexFn`, convexity of the epigraph.
* The indicator function $I_K$ of a set $K$ ($0$ on $K$, $+\infty$ off $K$) is
  `ConvexAnalysis.indicatorFn K`.

## Implementation notes

* The pairing is `Brezis.Chapter01.dualPairing E`, which is `(topDualPairing ℝ E).flip`, with $E$ on
  the left as `ConvexAnalysis.convexConj` requires. The conjugate is
  `ConvexAnalysis.convexConj (dualPairing E) φ`. The biconjugate, restricted to $E$, is
  `ConvexAnalysis.convexBiconj (dualPairing E) φ`. For this reason `ConvexAnalysis.convexBiconj`
  uses the flipped pairing and not a second copy of the pairing: iterating the conjugate would give
  a function on $E^{\star\star}$.
* The instance `ConvexAnalysis.instIsCompatiblePairingTopDual` makes $E$ compatibly paired with
  $E^\star$ in its own norm topology. Hence the Fenchel–Moreau theorem
  `ConvexAnalysis.convexBiconj_eq_convexCl_topDual` applies with no reflexivity assumption, as in
  the source. The constraint qualification of Theorem 1.12 is the backbone
  `ConvexAnalysis.IsExactSum.of_continuousAt`.
* The elementary facts that the section lists on lower semicontinuous and convex functions are not
  numbered results. They are Mathlib's `lowerSemicontinuous_iff_isClosed_epigraph`,
  `LowerSemicontinuous.add`, `lowerSemicontinuous_iSup` and `LowerSemicontinuousOn.exists_isMinOn`,
  and the backbone's `ConvexAnalysis.ConvexFn.convex_le`, `ConvexAnalysis.convexFn_add_coe` and
  `ConvexAnalysis.convexFn_iSup`.
* The source defines $\varphi^\star$ only for $\varphi \not\equiv +\infty$. The backbone defines
  `ConvexAnalysis.convexConj` for every $\varphi$, and $\varphi^\star \equiv -\infty$ exactly when
  $\varphi \equiv +\infty$ (`ConvexAnalysis.convexConj_eq_bot_iff`). The hypothesis
  $\varphi \not\equiv +\infty$ appears where it is needed.

## Deviations from the source

* **Domain, epigraph and lower semicontinuity** (generalization). The formulas also permit function
  values of $-\infty$. See `Brezis.Chapter01.mem_domain_iff`, `Brezis.Chapter01.mem_epigraph_iff`
  and `Brezis.Chapter01.lowerSemicontinuous_iff`.
* **Conjugacy and biconjugacy** (generalization). The definitions accept every extended-real-valued
  function, and the conjugate remains convex and lower semicontinuous. See
  `Brezis.Chapter01.conjugate`, `Brezis.Chapter01.biconjugate`,
  `Brezis.Chapter01.conjugate_convexFn` and `Brezis.Chapter01.conjugate_lowerSemicontinuous`.
* **Example 2, indicator functions** (generalization). The convexity and lower semicontinuity
  criteria include the empty set. See `Brezis.Chapter01.example_1_2_convexFn_iff` and
  `Brezis.Chapter01.example_1_2_lowerSemicontinuous_iff`.

## Not formalized

* **Remark 7, last clause (Exercise 1.18(h)).** Inequality (12) is the case $\varphi(t) = |t|^p/p$
  of (11) on $E = \mathbb{R}$.
* **Remark 8.** It is a discussion.
-/

open ConvexAnalysis Metric Set

namespace Brezis.Chapter01

/-! ### Lower semicontinuous and convex functions -/

/-- **Section 1.4** of [brezis2011functional], the domain. For a function
$\varphi : E \to [-\infty, +\infty]$, the **domain** of $\varphi$ is
$$D(\varphi) = \{x \in E : \varphi(x) < +\infty\}.$$

**Generalization.** The source excludes values of $-\infty$. The comparison with $+\infty$
also applies at those values, which are included in the domain.

The domain is the backbone `ConvexAnalysis.convexDom φ`, and the theorem states its membership
criterion. -/
theorem mem_domain_iff {E : Type*} (φ : E → EReal) (x : E) : x ∈ convexDom φ ↔ φ x < ⊤ :=
  mem_convexDom

/-- **Section 1.4** of [brezis2011functional], the epigraph. For a function
$\varphi : E \to [-\infty, +\infty]$, the **epigraph** of $\varphi$ is
$$\operatorname{epi} \varphi = \{[x, \lambda] \in E \times \mathbb{R} : \varphi(x) \le
  \lambda\}.$$

**Generalization.** The source excludes values of $-\infty$. For a point with value $-\infty$,
every real height is in the epigraph above that point.

The epigraph is the backbone `ConvexAnalysis.epi φ`, a subset of $E \times \mathbb{R}$: as in
footnote 5 of the source, $\lambda$ does not take the value $+\infty$. -/
theorem mem_epigraph_iff {E : Type*} (φ : E → EReal) (x : E) (l : ℝ) :
    (x, l) ∈ epi φ ↔ φ x ≤ (l : EReal) :=
  mk_mem_epi

/-- **Section 1.4** of [brezis2011functional], definition of lower semicontinuity. Let $E$ be a
topological space. A function $\varphi : E \to [-\infty, +\infty]$ is **lower semicontinuous**
if and only if for every $\lambda \in \mathbb{R}$ the sublevel set
$$[\varphi \le \lambda] = \{x \in E : \varphi(x) \le \lambda\}$$
is closed.

**Generalization.** The source excludes values of $-\infty$. Closedness of all real sublevel
sets also characterizes lower semicontinuity for fully extended-real-valued functions. -/
theorem lowerSemicontinuous_iff {E : Type*} [TopologicalSpace E] (φ : E → EReal) :
    LowerSemicontinuous φ ↔ ∀ l : ℝ, IsClosed {x | φ x ≤ (l : EReal)} :=
  lowerSemicontinuous_iff_isClosed_le

/-- **Section 1.4** of [brezis2011functional], definition of a convex function. Let $E$ be a real
vector space and $\varphi : E \to (-\infty, +\infty]$. Then $\varphi$ is **convex** if and only
if
$$\varphi(tx + (1-t)y) \le t\varphi(x) + (1-t)\varphi(y) \quad \text{for all } x, y \in E,\ t
  \in (0, 1).$$

The notion of the source is the backbone `ConvexAnalysis.ConvexFn`, convexity of the epigraph,
which is the first of the elementary facts of the section on convex functions. The hypothesis
that $\varphi$ never takes the value $-\infty$ is `∀ x, φ x ≠ ⊥`. -/
theorem convexFn_iff {E : Type*} [AddCommGroup E] [Module ℝ E] {φ : E → EReal}
    (hφ : ∀ x, φ x ≠ ⊥) :
    ConvexFn φ ↔ ∀ x y (t : ℝ), 0 < t → t < 1 →
      φ (t • x + (1 - t) • y) ≤ (t : EReal) * φ x + ((1 - t : ℝ) : EReal) * φ y := by
  rw [convexFn_iff_le hφ]
  constructor
  · intro h x y t ht ht1
    exact h x y t (1 - t) ht (by linarith) (by ring)
  · intro h x y a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    exact h x y a ha (by linarith)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The conjugate function -/

/-- **Section 1.4** of [brezis2011functional], the scalar product of the duality between $E^\star$
and $E$: $\langle f, x \rangle = f(x)$ for $x \in E$ and $f \in E^\star$.

It is written with $E$ on the left, as `ConvexAnalysis.convexConj` requires, so that
`dualPairing E x f = f x`. It is an `abbrev` of `(topDualPairing ℝ E).flip`, so that the
backbone instances `ConvexAnalysis.instIsCompatiblePairingTopDual` ($E$ compatibly paired with
$E^\star$ in its norm topology) and `ConvexAnalysis.instIsContinuousPairingTopDualNorm`
($E^\star$ continuously paired with $E$ in the norm topology of $E^\star$) apply to it. -/
noncomputable abbrev dualPairing (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E →ₗ[ℝ] StrongDual ℝ E →ₗ[ℝ] ℝ :=
  (topDualPairing ℝ E).flip

/-- The pairing `Brezis.Chapter01.dualPairing E` sends $x \in E$ and $f \in E^\star$ to $f(x)$. -/
@[simp] theorem dualPairing_apply (x : E) (f : StrongDual ℝ E) : dualPairing E x f = f x := rfl

/-- The flip of `Brezis.Chapter01.dualPairing E` is Mathlib's `topDualPairing ℝ E`, which sends
$f \in E^\star$ and $x \in E$ to $f(x)$. -/
theorem flip_dualPairing : (dualPairing E).flip = topDualPairing ℝ E := rfl

/-- **Section 1.4** of [brezis2011functional], definition of the conjugate function. Let $E$ be a
real normed space and $\varphi : E \to [-\infty, +\infty]$. The **conjugate function**
$\varphi^\star : E^\star \to [-\infty, +\infty]$ is
$$\varphi^\star(f) = \sup_{x \in E} \{\langle f, x \rangle - \varphi(x)\}.$$

**Generalization.** The source requires values in $(-\infty, +\infty]$ and at least one finite
value. The supremum defines the conjugate for every extended-real-valued function. It is
identically $-\infty$ when $\varphi$ is identically $+\infty$, and a value $\varphi(x) = -\infty$
makes the conjugate identically $+\infty$.

The definition is `ConvexAnalysis.convexConj (Brezis.Chapter01.dualPairing E) φ`. Later results
assume $\varphi \not\equiv +\infty$ where needed. -/
noncomputable def conjugate (φ : E → EReal) : StrongDual ℝ E → EReal :=
  convexConj (dualPairing E) φ

/-- The conjugate `Brezis.Chapter01.conjugate φ` is the backbone conjugate
`ConvexAnalysis.convexConj` with respect to the pairing `Brezis.Chapter01.dualPairing E`. -/
theorem conjugate_eq_convexConj (φ : E → EReal) : conjugate φ = convexConj (dualPairing E) φ := rfl

/-- **Section 1.4** of [brezis2011functional], the conjugate formula. For every $f \in E^\star$,
$\varphi^\star(f) = \sup_{x \in E} \{f(x) - \varphi(x)\}$, with the supremum and the subtraction
in $[-\infty, +\infty]$.

**Generalization.** The function may take either infinite value, as in
`Brezis.Chapter01.conjugate`. -/
theorem conjugate_apply (φ : E → EReal) (f : StrongDual ℝ E) :
    conjugate φ f = ⨆ x, ((f x : ℝ) : EReal) - φ x := rfl

/-- **Section 1.4** of [brezis2011functional], convexity of the conjugate. For every function
$\varphi : E \to [-\infty, +\infty]$, the conjugate $\varphi^\star$ is convex on $E^\star$.

**Generalization.** The source assumes that $\varphi$ has a finite value and never takes
$-\infty$. In the additional cases the conjugate is a constant infinite function, which still
has a convex epigraph. -/
theorem conjugate_convexFn (φ : E → EReal) : ConvexFn (conjugate φ) :=
  convexFn_convexConj _ _

/-- **Section 1.4** of [brezis2011functional], lower semicontinuity of the conjugate. For every
function $\varphi : E \to [-\infty, +\infty]$, the conjugate $\varphi^\star$ is lower
semicontinuous in the norm topology of $E^\star$.

**Generalization.** The source assumes that $\varphi$ has a finite value and never takes
$-\infty$. In the additional cases the conjugate is a constant infinite function, which is
also lower semicontinuous.

As in the source, $\varphi^\star$ is the upper envelope of the continuous affine functions
$f \mapsto \langle f, x \rangle - \varphi(x)$, and the fourth elementary fact of the section
applies. -/
theorem conjugate_lowerSemicontinuous (φ : E → EReal) : LowerSemicontinuous (conjugate φ) :=
  (closedConvex_convexConj (B := dualPairing E) (f := φ)).lowerSemicontinuous

/-- **Remark 7** of [brezis2011functional], Young's inequality (11). Let $E$ be a real normed space
and let $\varphi : E \to (-\infty, +\infty]$ with $\varphi \not\equiv +\infty$. Then
$$\langle f, x \rangle \le \varphi(x) + \varphi^\star(f) \quad \text{for all } x \in E,\ f \in
  E^\star.$$

The source calls this obvious from the definition of $\varphi^\star$. In $[-\infty, +\infty]$,
the two hypotheses $\varphi(x) \neq -\infty$ and $\varphi \not\equiv +\infty$ keep the
right-hand side from being $-\infty$. -/
theorem remark_1_7 {φ : E → EReal} (hφ : ∀ x, φ x ≠ ⊥) (hdom : (convexDom φ).Nonempty) (x : E)
    (f : StrongDual ℝ E) : ((f x : ℝ) : EReal) ≤ φ x + conjugate φ f :=
  le_add_convexConj (B := dualPairing E) (hφ x) hdom f

/-- **Remark 7** of [brezis2011functional], the classical Young inequality (12). Let $a, b \ge 0$,
let $1 < p < \infty$, and let $p'$ satisfy $1/p + 1/p' = 1$. Then
$$ab \le \frac{a^p}{p} + \frac{b^{p'}}{p'}.$$

The powers are real powers `Real.rpow`. The source obtains (12) from (11) for
$\varphi(t) = |t|^p/p$ on $E = \mathbb{R}$ (Exercise 1.18(h)); that derivation is not
formalized. -/
theorem remark_1_7_classical {a b p p' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 < p)
    (hpp' : 1 / p + 1 / p' = 1) : a * b ≤ a ^ p / p + b ^ p' / p' :=
  Real.young_inequality_of_nonneg ha hb
    (Real.holderConjugate_iff.2 ⟨hp, by simpa only [one_div] using hpp'⟩)

/-! ### Proposition 1.10 and Theorem 1.11 -/

/-- **Proposition 1.10** of [brezis2011functional]. Let $E$ be a real normed space and let
$\varphi : E \to (-\infty, +\infty]$ be convex and lower semicontinuous with
$\varphi \not\equiv +\infty$. Then $\varphi^\star \not\equiv +\infty$, that is,
$D(\varphi^\star)$ is nonempty. -/
theorem proposition_1_10 {φ : E → EReal} (hφ : ConvexFn φ) (hl : LowerSemicontinuous φ)
    (hbot : ∀ x, φ x ≠ ⊥) (hdom : (convexDom φ).Nonempty) : (convexDom (conjugate φ)).Nonempty :=
  ((properConvex_convexConj_iff (B := dualPairing E) hφ
    ((closedConvex_iff_lowerSemicontinuous hbot).2 hl)).2 ⟨hdom, hbot⟩).convexDom_nonempty

/-- **Proposition 1.10** of [brezis2011functional], the "in particular" clause. Let $E$ be a real
normed space and let $\varphi : E \to (-\infty, +\infty]$ be convex and lower semicontinuous
with $\varphi \not\equiv +\infty$. Then $\varphi$ is bounded below by a continuous affine
function: there are $f \in E^\star$ and $C \in \mathbb{R}$ such that
$$\varphi(x) \ge \langle f, x \rangle - C \quad \text{for all } x \in E.$$
-/
theorem proposition_1_10_affine {φ : E → EReal} (hφ : ConvexFn φ) (hl : LowerSemicontinuous φ)
    (hbot : ∀ x, φ x ≠ ⊥) (hdom : (convexDom φ).Nonempty) :
    ∃ (f : StrongDual ℝ E) (c : ℝ), ∀ x, ((f x - c : ℝ) : EReal) ≤ φ x := by
  obtain ⟨f, c, hfc⟩ := exists_affine_le_of_closed_proper
    ⟨hφ, (closedConvex_iff_lowerSemicontinuous hbot).2 hl, ⟨hdom, hbot⟩⟩
  exact ⟨f, c, fun x => by rw [EReal.coe_sub]; exact hfc x⟩

/-- **Section 1.4** of [brezis2011functional], definition of the biconjugate. Let $E$ be a real
normed space and $\varphi : E \to [-\infty, +\infty]$. The **biconjugate** of $\varphi$,
restricted to $E$ as in the source before Theorem 1.11, is
$$\varphi^{\star\star}(x) = \sup_{f \in E^\star} \{\langle f, x \rangle - \varphi^\star(f)\}
  \quad \text{for } x \in E.$$

**Generalization.** The source starts with a conjugate of a function that never takes
$-\infty$ and has a finite value. The same formula applies to every extended-real-valued input.

It is the backbone `ConvexAnalysis.convexBiconj (dualPairing E) φ`, which is
`ConvexAnalysis.convexConj (topDualPairing ℝ E) (Brezis.Chapter01.conjugate φ)`. To iterate the
conjugate would give a function on $E^{\star\star}$. For this reason
`ConvexAnalysis.convexBiconj` takes the conjugate with respect to the flipped pairing the second
time. -/
noncomputable def biconjugate (φ : E → EReal) : E → EReal :=
  convexBiconj (dualPairing E) φ

/-- The biconjugate `Brezis.Chapter01.biconjugate φ` is the conjugate of
`Brezis.Chapter01.conjugate φ` with respect to Mathlib's pairing `topDualPairing ℝ E` of
$E^\star$ with $E$. -/
theorem biconjugate_eq_convexConj (φ : E → EReal) :
    biconjugate φ = convexConj (topDualPairing ℝ E) (conjugate φ) := rfl

/-- **Section 1.4** of [brezis2011functional], the biconjugate formula. For every $x \in E$,
$\varphi^{\star\star}(x) = \sup_{f \in E^\star} \{f(x) - \varphi^\star(f)\}$, with the supremum
and the subtraction in $[-\infty, +\infty]$.

**Generalization.** The function may take either infinite value, as in
`Brezis.Chapter01.biconjugate`. -/
theorem biconjugate_apply (φ : E → EReal) (x : E) :
    biconjugate φ x = ⨆ f : StrongDual ℝ E, ((f x : ℝ) : EReal) - conjugate φ f := rfl

/-- **Theorem 1.11** of [brezis2011functional] (Fenchel–Moreau). Let $E$ be a real normed space and
let $\varphi : E \to (-\infty, +\infty]$ be convex and lower semicontinuous with
$\varphi \not\equiv +\infty$. Then
$$\varphi^{\star\star} = \varphi.$$

No reflexivity is needed: $E$ is compatibly paired with $E^\star$ in its own norm topology
(`ConvexAnalysis.instIsCompatiblePairingTopDual`). The backbone theorem
`ConvexAnalysis.convexBiconj_eq_convexCl_topDual` does not need $\varphi \not\equiv +\infty$: if
$\varphi \equiv +\infty$, then $\varphi^\star \equiv -\infty$ and
$\varphi^{\star\star} \equiv +\infty = \varphi$. The hypothesis is kept as the source states it,
and the proof does not use it. -/
theorem theorem_1_11 {φ : E → EReal} (hφ : ConvexFn φ) (hl : LowerSemicontinuous φ)
    (hbot : ∀ x, φ x ≠ ⊥) (_hdom : (convexDom φ).Nonempty) : biconjugate φ = φ :=
  convexBiconj_eq_self (B := dualPairing E) hφ ((closedConvex_iff_lowerSemicontinuous hbot).2 hl)

/-! ### Example 1: the norm -/

/-- **Example 1** of [brezis2011functional], the conjugate of the norm. Let $E$ be a real normed
space and $\varphi(x) = \|x\|$. Then
$$\varphi^\star(f) = \begin{cases} 0 & \text{if } \|f\| \le 1, \\ +\infty & \text{if } \|f\| >
  1, \end{cases}$$
that is, $\varphi^\star$ is the indicator function of the closed unit ball of $E^\star$.

The indicator function is `ConvexAnalysis.indicatorFn`. -/
theorem example_1_1_conj :
    conjugate (fun x : E => (‖x‖ : EReal)) = indicatorFn (closedBall (0 : StrongDual ℝ E) 1) := by
  funext f
  rw [conjugate_apply]
  by_cases hf : ‖f‖ ≤ 1
  · rw [indicatorFn_of_mem (mem_closedBall_zero_iff.2 hf)]
    refine le_antisymm (iSup_le fun x => ?_) (le_iSup_of_le 0 (by simp))
    rw [← EReal.coe_sub, ← EReal.coe_zero, EReal.coe_le_coe_iff, sub_nonpos]
    calc f x ≤ ‖f x‖ := Real.le_norm_self _
      _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := one_mul _
  · rw [indicatorFn_of_notMem fun h => hf (mem_closedBall_zero_iff.1 h)]
    rw [not_le] at hf
    -- a direction along which `f x - ‖x‖ > 0`; scaling it sends the supremum to `+∞`
    obtain ⟨x, hx1, hfx⟩ := f.exists_lt_apply_of_lt_opNorm hf
    obtain ⟨y, hy⟩ : ∃ y : E, ‖y‖ < f y := by
      rcases le_or_gt 0 (f x) with h | h
      · exact ⟨x, hx1.trans (by rwa [Real.norm_eq_abs, abs_of_nonneg h] at hfx)⟩
      · refine ⟨-x, ?_⟩
        rw [norm_neg, map_neg]
        exact hx1.trans (by rwa [Real.norm_eq_abs, abs_of_neg h] at hfx)
    have hd : 0 < f y - ‖y‖ := sub_pos.2 hy
    refine top_unique (le_of_forall_lt fun b hb => ?_)
    obtain ⟨r, hr, -⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    set t : ℝ := (|r| + 1) / (f y - ‖y‖) with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) hd.le
    refine lt_of_lt_of_le ?_ (le_iSup (fun x : E => ((f x : ℝ) : EReal) - (‖x‖ : EReal)) (t • y))
    rw [map_smul, norm_smul, Real.norm_of_nonneg ht0, smul_eq_mul, ← EReal.coe_sub]
    refine lt_of_lt_of_le hr (EReal.coe_le_coe_iff.2 ?_)
    rw [← mul_sub, ht, div_mul_cancel₀ _ hd.ne']
    exact (le_abs_self r).trans (by linarith)

/-- **Example 1** of [brezis2011functional], the biconjugate of the norm. Let $E$ be a real normed
space and $\varphi(x) = \|x\|$. For every $x \in E$,
$$\varphi^{\star\star}(x) = \sup_{\|f\| \le 1} \langle f, x \rangle \quad \text{and} \quad
  \|x\| = \sup_{\|f\| \le 1} \langle f, x \rangle.$$

The second identity follows from Theorem 1.11, since $\varphi$ is convex and continuous; the
source notes that "we obtain again part of Corollary 1.4". `Brezis.Chapter01.corollary_1_4`
states the supremum of $|\langle f, x \rangle|$; the two suprema agree because the unit ball is
symmetric. -/
theorem example_1_1_biconj (x : E) :
    biconjugate (fun x : E => (‖x‖ : EReal)) x =
        ⨆ f ∈ closedBall (0 : StrongDual ℝ E) 1, ((f x : ℝ) : EReal) ∧
      (‖x‖ : EReal) = ⨆ f ∈ closedBall (0 : StrongDual ℝ E) 1, ((f x : ℝ) : EReal) := by
  have h : biconjugate (fun x : E => (‖x‖ : EReal)) x =
      ⨆ f ∈ closedBall (0 : StrongDual ℝ E) 1, ((f x : ℝ) : EReal) := by
    rw [biconjugate_apply, example_1_1_conj]
    refine iSup_congr fun f => ?_
    by_cases hf : f ∈ closedBall (0 : StrongDual ℝ E) 1
    · rw [iSup_pos hf, indicatorFn_of_mem hf, sub_zero]
    · rw [iSup_neg hf, indicatorFn_of_notMem hf, EReal.sub_top]
  refine ⟨h, ?_⟩
  have h11 := theorem_1_11 (φ := fun x : E => (‖x‖ : EReal))
    (convexOn_norm (convex_univ : Convex ℝ (univ : Set E))).convexFn_coe
    (EReal.continuous_coe_iff.2 continuous_norm).lowerSemicontinuous
    (fun x => EReal.coe_ne_bot ‖x‖) ⟨0, EReal.coe_lt_top _⟩
  exact (congrFun h11 x).symm.trans h

/-! ### Example 2: indicator functions and orthogonals -/

/-- **Example 2** of [brezis2011functional], convexity of an indicator function. Let $E$ be a real
normed space and $K \subseteq E$. The indicator function $I_K$, equal to $0$ on $K$ and to
$+\infty$ off $K$, is convex if and only if $K$ is convex.

**Generalization.** The source assumes $K$ is nonempty. For the empty set both $K$ and the
epigraph of its indicator are empty and hence convex.

The indicator function is the backbone `ConvexAnalysis.indicatorFn K`. It is not the
characteristic function $\chi_K$. -/
theorem example_1_2_convexFn_iff (K : Set E) : ConvexFn (indicatorFn K) ↔ Convex ℝ K :=
  convexFn_indicatorFn

omit [NormedSpace ℝ E] in
/-- **Example 2** of [brezis2011functional], lower semicontinuity of an indicator function. Let $E$
be a normed group and $K \subseteq E$. The indicator function $I_K$ is lower semicontinuous if
and only if $K$ is closed.

**Generalization.** The source takes a nonempty set in a real normed space. The criterion
uses only closedness of $K$ in the underlying topology. It also holds for the empty set,
whose indicator is constantly $+\infty$. -/
theorem example_1_2_lowerSemicontinuous_iff (K : Set E) :
    LowerSemicontinuous (indicatorFn K) ↔ IsClosed K := by
  refine ⟨fun hl => ?_, fun hK => (closedConvex_indicatorFn hK).lowerSemicontinuous⟩
  have hK : {x | indicatorFn K x ≤ ((0 : ℝ) : EReal)} = K := by
    ext x
    by_cases hx : x ∈ K <;> simp [hx]
  rw [← hK]
  exact (lowerSemicontinuous_iff _).1 hl 0

/-- The polar cones of the convex analysis library are the orthogonals of Section 1.3 of
[brezis2011functional]. Let $E$ be a real normed space. For a linear subspace $M \subseteq E$,
the polar cone $\{f \in E^\star : \langle f, x \rangle \le 0 \ \forall x \in M\}$ is $M^\perp$.
For a linear subspace $N \subseteq E^\star$, the polar cone $\{x \in E : \langle f, x \rangle
\le 0 \ \forall f \in N\}$ is $N^\perp$.

The polar cones are `ConvexAnalysis.polarCone` with respect to `Brezis.Chapter01.dualPairing E`
and to `topDualPairing ℝ E`. -/
theorem polarCone_dualPairing_eq :
    (∀ M : Submodule ℝ E,
        polarCone (dualPairing E) (M : Set E) =
          (M.strongDualAnnihilator : Set (StrongDual ℝ E))) ∧
      ∀ N : Submodule ℝ (StrongDual ℝ E),
        polarCone (topDualPairing ℝ E) (N : Set (StrongDual ℝ E)) =
          (N.strongDualCoannihilator : Set E) := by
  constructor
  · intro M
    rw [polarCone_coe_submodule']
    ext f
    simp only [SetLike.mem_coe, Submodule.mem_strongDualAnnihilator, dualPairing_apply]
    exact Iff.rfl
  · intro N
    rw [polarCone_coe_submodule']
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_strongDualCoannihilator, topDualPairing_apply]
    exact Iff.rfl

/-- **Example 2** of [brezis2011functional], the conjugate of the indicator function of a subspace.
Let $E$ be a real normed space and $M \subseteq E$ a linear subspace. Then
$$(I_M)^\star = I_{M^\perp}.$$
-/
theorem example_1_2_conj (M : Submodule ℝ E) :
    conjugate (indicatorFn (M : Set E)) =
      indicatorFn (M.strongDualAnnihilator : Set (StrongDual ℝ E)) := by
  rw [conjugate_eq_convexConj,
    convexConj_indicatorFn_eq_indicatorFn_polarCone (isCone_coe_submodule M)
      ⟨0, M.zero_mem⟩, polarCone_dualPairing_eq.1 M]

/-- **Example 2** of [brezis2011functional], the biconjugate of the indicator function of a
subspace. Let $E$ be a real normed space and $M \subseteq E$ a linear subspace. Then
$$(I_M)^{\star\star} = I_{(M^\perp)^\perp}.$$
-/
theorem example_1_2_biconj (M : Submodule ℝ E) :
    biconjugate (indicatorFn (M : Set E)) =
      indicatorFn (M.strongDualAnnihilator.strongDualCoannihilator : Set E) := by
  rw [biconjugate_eq_convexConj, example_1_2_conj,
    convexConj_indicatorFn_eq_indicatorFn_polarCone (isCone_coe_submodule _)
      ⟨0, Submodule.zero_mem _⟩, polarCone_dualPairing_eq.2]

/-- **Example 2** of [brezis2011functional], the conclusion. Let $E$ be a real normed space and
$M \subseteq E$ a closed linear subspace. Then
$$(M^\perp)^\perp = M.$$

The source obtains this from $(I_M)^{\star\star} = I_M$ (Theorem 1.11) and remarks that "Theorem
1.11 can be viewed as a counterpart of Proposition 1.9"; `Brezis.Chapter01.proposition_1_9`
states $(M^\perp)^\perp = \overline{M}$. The proof follows the source: it reads
`Brezis.Chapter01.example_1_2_biconj` through `Brezis.Chapter01.theorem_1_11`. -/
theorem example_1_2_orthogonal {M : Submodule ℝ E} (hM : IsClosed (M : Set E)) :
    M.strongDualAnnihilator.strongDualCoannihilator = M := by
  have h := theorem_1_11 (convexFn_indicatorFn.2 M.convex)
    ((example_1_2_lowerSemicontinuous_iff (M : Set E)).2 hM) (indicatorFn_ne_bot _)
    ⟨0, by rw [convexDom_indicatorFn]; exact M.zero_mem⟩
  rw [example_1_2_biconj] at h
  have h' := congrArg convexDom h
  rw [convexDom_indicatorFn, convexDom_indicatorFn] at h'
  exact SetLike.coe_injective h'

/-! ### Theorem 1.12 -/

/-- **Theorem 1.12** of [brezis2011functional] (Fenchel–Rockafellar), the duality. Let $E$ be a real
normed space and let $\varphi, \psi : E \to (-\infty, +\infty]$ be convex. Assume that there is
$x_0 \in D(\varphi) \cap D(\psi)$ such that $\varphi$ is continuous at $x_0$. Then
$$\inf_{x \in E} \{\varphi(x) + \psi(x)\} = \sup_{f \in E^\star} \{-\varphi^\star(-f) -
  \psi^\star(f)\}.$$

The infimum, the supremum and the arithmetic are in $[-\infty, +\infty]$. The source treats the
case where the infimum is $-\infty$ separately; this formulation includes it. The proof uses the
constraint qualification `ConvexAnalysis.IsExactSum.of_continuousAt`. -/
theorem theorem_1_12 {φ ψ : E → EReal} (hφ : ConvexFn φ) (hψ : ConvexFn ψ)
    (hφb : ∀ x, φ x ≠ ⊥) (hψb : ∀ x, ψ x ≠ ⊥) {x₀ : E} (hx₀φ : x₀ ∈ convexDom φ)
        (hx₀ψ : x₀ ∈ convexDom ψ)
    (hcont : ContinuousAt φ x₀) :
    (⨅ x, φ x + ψ x) = ⨆ f : StrongDual ℝ E, -(conjugate φ (-f)) - conjugate ψ f := by
  have hex : IsExactSum (dualPairing E) φ ψ :=
    IsExactSum.of_continuousAt hφ ⟨⟨x₀, hx₀φ⟩, hφb⟩ hψ ⟨⟨x₀, hx₀ψ⟩, hψb⟩ hx₀φ hx₀ψ hcont
  have h1 : (⨅ x, φ x + ψ x) = -(convexConj (dualPairing E) (φ + ψ) 0) :=
    iInf_eq_neg_convexConj_zero (dualPairing E) (φ + ψ)
  rw [h1, hex.convexConj_add_apply 0, EReal.neg_iInf]
  refine iSup_congr fun f => ?_
  rw [zero_sub]
  exact EReal.neg_add (Or.inl (hex.convexConj_left_ne_bot (-f)))
      (Or.inr (hex.convexConj_right_ne_bot f))

/-- **Theorem 1.12** of [brezis2011functional] (Fenchel–Rockafellar), the attainment. Under the
hypotheses of `Brezis.Chapter01.theorem_1_12`, the supremum is a maximum: there is
$f \in E^\star$ with
$$-\varphi^\star(-f) - \psi^\star(f) = \inf_{x \in E} \{\varphi(x) + \psi(x)\} \quad \text{and}
  \quad \varphi^\star(-f) + \psi^\star(f) = -\inf_{x \in E} \{\varphi(x) + \psi(x)\}.$$

The second identity is the last expression of the source, $\inf (\varphi + \psi) = -\min_f
\{\varphi^\star(-f) + \psi^\star(f)\}$, at the same $f$. -/
theorem theorem_1_12_max {φ ψ : E → EReal} (hφ : ConvexFn φ) (hψ : ConvexFn ψ)
    (hφb : ∀ x, φ x ≠ ⊥) (hψb : ∀ x, ψ x ≠ ⊥) {x₀ : E} (hx₀φ : x₀ ∈ convexDom φ)
        (hx₀ψ : x₀ ∈ convexDom ψ)
    (hcont : ContinuousAt φ x₀) :
    ∃ f : StrongDual ℝ E, -(conjugate φ (-f)) - conjugate ψ f = (⨅ x, φ x + ψ x) ∧
      conjugate φ (-f) + conjugate ψ f = -(⨅ x, φ x + ψ x) := by
  have hex : IsExactSum (dualPairing E) φ ψ :=
    IsExactSum.of_continuousAt hφ ⟨⟨x₀, hx₀φ⟩, hφb⟩ hψ ⟨⟨x₀, hx₀ψ⟩, hψb⟩ hx₀φ hx₀ψ hcont
  have h1 : (⨅ x, φ x + ψ x) = -(convexConj (dualPairing E) (φ + ψ) 0) :=
    iInf_eq_neg_convexConj_zero (dualPairing E) (φ + ψ)
  obtain ⟨y₁, y₂, hy, hval⟩ := hex.exists_convexConj_add_eq 0
  obtain rfl : y₁ = -y₂ := eq_neg_of_add_eq_zero_left hy
  refine ⟨y₂, ?_, ?_⟩
  · rw [h1, ← hval,
      EReal.neg_add (Or.inl (hex.convexConj_left_ne_bot (-y₂)))
          (Or.inr (hex.convexConj_right_ne_bot y₂))]
    rfl
  · rw [h1, neg_neg]
    exact hval

/-- **Lemma 1.4** of [brezis2011functional], first clause. Let $E$ be a real normed space. If
$C \subseteq E$ is convex, then $\operatorname{Int} C$ is convex. -/
theorem lemma_1_4_convex {C : Set E} (hC : Convex ℝ C) : Convex ℝ (interior C) :=
  hC.interior

/-- **Lemma 1.4** of [brezis2011functional]. Let $E$ be a real normed space and let $C \subseteq E$
be convex with $\operatorname{Int} C \neq \emptyset$. Then
$$\overline{C} = \overline{\operatorname{Int} C}.$$

The source refers to Exercise 1.7 for the proof. -/
theorem lemma_1_4 {C : Set E} (hC : Convex ℝ C) (hne : (interior C).Nonempty) :
    closure C = closure (interior C) :=
  (hC.closure_interior_eq_closure_of_nonempty_interior hne).symm

/-! ### Examples 3 and 4 -/

/-- The conjugate of $x \mapsto \|x - x_0\|$ at $-f$ is
$I_{B_{E^\star}}(f) - \langle f, x_0 \rangle$, where $B_{E^\star}$ is the closed unit ball of
$E^\star$. -/
private theorem conjugate_norm_sub_neg (x₀ : E) (f : StrongDual ℝ E) :
    conjugate (fun x : E => (‖x - x₀‖ : EReal)) (-f) =
      indicatorFn (closedBall (0 : StrongDual ℝ E) 1) f - ((f x₀ : ℝ) : EReal) := by
  have h := convexConj_comp_sub (dualPairing E) (fun x : E => (‖x‖ : EReal)) x₀ (-f)
  rw [conjugate_eq_convexConj, h, ← conjugate_eq_convexConj, example_1_1_conj, dualPairing_apply,
    neg_apply, EReal.coe_neg, ← sub_eq_add_neg]
  congr 1
  by_cases hf : f ∈ closedBall (0 : StrongDual ℝ E) 1
  · rw [indicatorFn_of_mem hf, indicatorFn_of_mem (by simpa using hf)]
  · rw [indicatorFn_of_notMem hf, indicatorFn_of_notMem (by simpa using hf)]

/-- **Example 3** of [brezis2011functional], formula (19). Let $E$ be a real normed space, let
$K \subseteq E$ be a nonempty convex set, and let $x_0 \in E$. Then
$$\operatorname{dist}(x_0, K) = \inf_{x \in K} \|x - x_0\| = \max_{f \in E^\star,\ \|f\| \le 1}
  \{\langle f, x_0 \rangle - I_K^\star(f)\}.$$
That is, the distance is the infimum, it is the supremum over the closed unit ball of $E^\star$,
and the supremum is attained.

The distance is Mathlib's `Metric.infDist x₀ K`, and the identities are in $[-\infty, +\infty]$.
As in the source, the proof applies Theorem 1.12 with $\varphi(x) = \|x - x_0\|$ and
$\psi = I_K$. -/
theorem example_1_3 {K : Set E} (hK : Convex ℝ K) (hne : K.Nonempty) (x₀ : E) :
    ((infDist x₀ K : ℝ) : EReal) = ⨅ x ∈ K, (‖x - x₀‖ : EReal) ∧
      ((infDist x₀ K : ℝ) : EReal) =
        ⨆ f ∈ closedBall (0 : StrongDual ℝ E) 1,
          ((f x₀ : ℝ) : EReal) - conjugate (indicatorFn K) f ∧
      ∃ f : StrongDual ℝ E, ‖f‖ ≤ 1 ∧
        ((f x₀ : ℝ) : EReal) - conjugate (indicatorFn K) f = ((infDist x₀ K : ℝ) : EReal) := by
  set φ : E → EReal := fun x => (‖x - x₀‖ : EReal) with hφ
  -- the distance as the book's infimum
  have hA : ((infDist x₀ K : ℝ) : EReal) = ⨅ x ∈ K, (‖x - x₀‖ : EReal) := by
    have hinf : infDist x₀ K = sInf ((fun x => ‖x - x₀‖) '' K) := by
      rw [infDist_eq_iInf, sInf_image']
      exact iInf_congr fun y => by rw [dist_comm, dist_eq_norm]
    have hbdd : BddBelow ((fun x => ‖x - x₀‖) '' K) :=
      ⟨0, by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg _⟩
    rw [hinf, EReal.coe_sInf_of_bddBelow (hne.image _) hbdd, iInf_image]
  -- the constrained infimum as an unconstrained one
  have hB : (⨅ x ∈ K, (‖x - x₀‖ : EReal)) = ⨅ x, φ x + indicatorFn K x :=
    iInf_mem_eq_iInf_add_indicatorFn φ K fun _ => EReal.coe_ne_bot _
  -- the hypotheses of Theorem 1.12
  have hφc : ConvexFn φ := by
    have h : ConvexOn ℝ univ fun x : E => ‖x - x₀‖ := by
      simpa only [dist_eq_norm] using convexOn_dist x₀ (convex_univ (𝕜 := ℝ) (E := E))
    exact h.convexFn_coe
  have hφcont : Continuous φ :=
    EReal.continuous_coe_iff.2 (continuous_id.sub continuous_const).norm
  obtain ⟨x₁, hx₁⟩ := hne
  have hx₁ψ : x₁ ∈ convexDom (indicatorFn K) := by rw [convexDom_indicatorFn]; exact hx₁
  -- the dual side, term by term
  have hC : ∀ f : StrongDual ℝ E, -(conjugate φ (-f)) - conjugate (indicatorFn K) f =
      ⨆ _ : f ∈ closedBall (0 : StrongDual ℝ E) 1,
        ((f x₀ : ℝ) : EReal) - conjugate (indicatorFn K) f := by
    intro f
    rw [hφ, conjugate_norm_sub_neg]
    by_cases hf : f ∈ closedBall (0 : StrongDual ℝ E) 1
    · rw [iSup_pos hf, indicatorFn_of_mem hf, zero_sub, neg_neg]
    · rw [iSup_neg hf, indicatorFn_of_notMem hf, EReal.top_sub_coe, EReal.neg_top, EReal.bot_sub]
  refine ⟨hA, ?_, ?_⟩
  · rw [hA, hB, theorem_1_12 hφc (convexFn_indicatorFn.2 hK) (fun _ => EReal.coe_ne_bot _)
      (indicatorFn_ne_bot _) (EReal.coe_lt_top _) hx₁ψ hφcont.continuousAt]
    exact iSup_congr hC
  · obtain ⟨f, hf, -⟩ := theorem_1_12_max hφc (convexFn_indicatorFn.2 hK)
      (fun _ => EReal.coe_ne_bot _) (indicatorFn_ne_bot _) (EReal.coe_lt_top _) hx₁ψ
      hφcont.continuousAt
    rw [hC f, ← hB, ← hA] at hf
    by_cases h1 : f ∈ closedBall (0 : StrongDual ℝ E) 1
    · rw [iSup_pos h1] at hf
      exact ⟨f, mem_closedBall_zero_iff.1 h1, hf⟩
    · rw [iSup_neg h1] at hf
      exact absurd hf.symm (EReal.coe_ne_bot _)

/-- **Example 3** of [brezis2011functional], the case of a subspace. Let $E$ be a real normed space,
$M \subseteq E$ a linear subspace, and $x_0 \in E$. Then
$$\operatorname{dist}(x_0, M) = \max_{f \in M^\perp,\ \|f\| \le 1} \langle f, x_0 \rangle.$$
That is, the supremum of $\langle f, x_0 \rangle$ over the $f \in M^\perp$ with $\|f\| \le 1$ is
$\operatorname{dist}(x_0, M)$, and it is attained.

The statement is in $\mathbb{R}$. The proof uses the backbone Hahn–Banach argument in the
quotient $E / \overline{M}$. The source derives the formula from (19) with
$(I_M)^\star = I_{M^\perp}$; that derivation is
`Brezis.Chapter01.example_1_3_submodule_of_example_1_3`. -/
theorem example_1_3_submodule (M : Submodule ℝ E) (x₀ : E) :
    infDist x₀ M = sSup ((fun f : StrongDual ℝ E => f x₀) ''
        {f | f ∈ M.strongDualAnnihilator ∧ ‖f‖ ≤ 1}) ∧
      ∃ f ∈ M.strongDualAnnihilator, ‖f‖ ≤ 1 ∧ f x₀ = infDist x₀ M := by
  obtain ⟨f, hfM, hf1, hfx⟩ := M.exists_mem_strongDualAnnihilator_norm_le_one_apply_eq_infDist x₀
  rw [RCLike.ofReal_real_eq_id, id] at hfx
  have hgreat : IsGreatest ((fun f : StrongDual ℝ E => f x₀) ''
      {f | f ∈ M.strongDualAnnihilator ∧ ‖f‖ ≤ 1}) (infDist x₀ M) := by
    refine ⟨⟨f, ⟨hfM, hf1⟩, hfx⟩, ?_⟩
    rintro _ ⟨g, ⟨hgM, hg1⟩, rfl⟩
    exact (Real.le_norm_self _).trans
      (Submodule.norm_apply_le_infDist_of_mem_strongDualAnnihilator hgM hg1 x₀)
  exact ⟨hgreat.csSup_eq.symm, f, hfM, hf1, hfx⟩

/-- **Example 3** of [brezis2011functional], the case of a subspace, derived from (19) as in the
source. Let $E$ be a real normed space, $M \subseteq E$ a linear subspace, and $x_0 \in E$. Then
$$\operatorname{dist}(x_0, M) = \max_{f \in M^\perp,\ \|f\| \le 1} \langle f, x_0 \rangle,$$
with the supremum taken in $[-\infty, +\infty]$, and the maximum is attained.

The proof reads formula (19) for $K = M$ through $(I_M)^\star = I_{M^\perp}$
(`Brezis.Chapter01.example_1_2_conj`). `Brezis.Chapter01.example_1_3_submodule` is the same
statement in $\mathbb{R}$, proved by the backbone Hahn–Banach argument. -/
theorem example_1_3_submodule_of_example_1_3 (M : Submodule ℝ E) (x₀ : E) :
    ((infDist x₀ M : ℝ) : EReal) =
        ⨆ f ∈ {f : StrongDual ℝ E | f ∈ M.strongDualAnnihilator ∧ ‖f‖ ≤ 1},
          ((f x₀ : ℝ) : EReal) ∧
      ∃ f ∈ M.strongDualAnnihilator, ‖f‖ ≤ 1 ∧ ((f x₀ : ℝ) : EReal) = infDist x₀ M := by
  obtain ⟨-, h19, f, hf1, hfx⟩ := example_1_3 M.convex ⟨0, M.zero_mem⟩ x₀
  rw [example_1_2_conj] at h19 hfx
  constructor
  · rw [h19]
    refine iSup_congr fun g => ?_
    by_cases hg1 : g ∈ closedBall (0 : StrongDual ℝ E) 1
    · rw [iSup_pos hg1]
      by_cases hgM : g ∈ M.strongDualAnnihilator
      · rw [iSup_pos (show g ∈ {f : StrongDual ℝ E | f ∈ M.strongDualAnnihilator ∧ ‖f‖ ≤ 1} from
          ⟨hgM, mem_closedBall_zero_iff.1 hg1⟩), indicatorFn_of_mem (SetLike.mem_coe.2 hgM),
          sub_zero]
      · rw [iSup_neg (show g ∉ {f : StrongDual ℝ E | f ∈ M.strongDualAnnihilator ∧ ‖f‖ ≤ 1} from
          fun h => hgM h.1), indicatorFn_of_notMem (fun h => hgM (SetLike.mem_coe.1 h)),
          EReal.sub_top]
    · rw [iSup_neg hg1, iSup_neg (show g ∉ {f : StrongDual ℝ E | f ∈ M.strongDualAnnihilator ∧
        ‖f‖ ≤ 1} from fun h => hg1 (mem_closedBall_zero_iff.2 h.2))]
  · by_cases hfM : f ∈ M.strongDualAnnihilator
    · rw [indicatorFn_of_mem (SetLike.mem_coe.2 hfM), sub_zero] at hfx
      exact ⟨f, hfM, hf1, hfx⟩
    · rw [indicatorFn_of_notMem (fun h => hfM (SetLike.mem_coe.1 h)), EReal.sub_top] at hfx
      exact absurd hfx.symm (EReal.coe_ne_bot _)

/-- **Example 4** of [brezis2011functional]. Let $E$ be a real normed space, let
$\varphi : E \to \mathbb{R}$ be convex and continuous, and let $M \subseteq E$ be a linear
subspace. Then
$$\inf_{x \in M} \varphi(x) = -\min_{f \in M^\perp} \varphi^\star(f).$$
That is, the identity holds with the infimum over $M^\perp$, and this infimum is attained.

The identities are in $[-\infty, +\infty]$. The proof applies Theorem 1.12 with $\psi = I_M$, in
the backbone subspace form `ConvexAnalysis.iInf_mem_submodule_eq_neg_iInf_mem_polarCone`. -/
theorem example_1_4 {φ : E → ℝ} (hφ : ConvexOn ℝ univ φ) (hc : Continuous φ)
    (M : Submodule ℝ E) :
    (⨅ x ∈ M, ((φ x : ℝ) : EReal)) =
        -(⨅ f ∈ M.strongDualAnnihilator, conjugate (fun x => ((φ x : ℝ) : EReal)) f) ∧
      ∃ f ∈ M.strongDualAnnihilator, conjugate (fun x => ((φ x : ℝ) : EReal)) f =
        ⨅ g ∈ M.strongDualAnnihilator, conjugate (fun x => ((φ x : ℝ) : EReal)) g := by
  have hex : IsExactSum (dualPairing E) (fun x => ((φ x : ℝ) : EReal)) (indicatorFn (M : Set E)) :=
    IsExactSum.of_continuousAt hφ.convexFn_coe (properConvex_coe φ)
        (convexFn_indicatorFn.2 M.convex)
      (properConvex_indicatorFn.2 ⟨0, M.zero_mem⟩) (x₀ := 0) (EReal.coe_lt_top _)
      (by rw [convexDom_indicatorFn]; exact M.zero_mem) (EReal.continuous_coe_iff.2 hc).continuousAt
  have hpol := polarCone_dualPairing_eq.1 M
  constructor
  · have h := iInf_mem_submodule_eq_neg_iInf_mem_polarCone hex
    rw [hpol] at h
    exact h
  · have h := exists_mem_neg_polarCone_convexConj_eq_iInf hex (isCone_coe_submodule M)
      ⟨0, M.zero_mem⟩
    rw [neg_polarCone_coe_submodule, hpol] at h
    exact h

end Brezis.Chapter01
