/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Continuity
import Numlib.Analysis.Convex.Convergence
import Numlib.Analysis.Convex.Operations.Basic
import Numlib.Analysis.Convex.Simplicial
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar, Section 10: Continuity of convex functions

This module formalizes §10 of [rockafellar1970convex]: the situations in which a convex function is
automatically upper semicontinuous, and hence continuous, together with the theory of
equi-Lipschitzian families and of convergence that follows from them. A convex function is
continuous relative to every relatively open convex subset of its effective domain, and upper
semicontinuous relative to every locally simplicial subset. A proper convex function is Lipschitzian
relative to every closed bounded subset of $\operatorname{ri}(\operatorname{dom} f)$, and a finite
convex function on $\mathbb{R}^n$ is uniformly continuous exactly when its recession function is
finite. A pointwise bounded family of finite convex functions on a relatively open convex set is
uniformly bounded and equi-Lipschitzian on closed bounded subsets, so that pointwise convergence on
a dense subset is uniform convergence on closed bounded subsets. The proofs specialize
`Numlib.Analysis.Convex.Continuity`, `Numlib.Analysis.Convex.Convergence` and
`Numlib.Analysis.Convex.Simplicial`.

All 13 numbered results of §10 are formalized. The section is entirely finite-dimensional: every
result rests somewhere on Theorem 6.2, that a nonempty convex set has a nonempty relative interior.

## Main definitions

* Section 10, `Rockafellar.continuousOn_iff_continuous_restrict_rn`: continuity relative to $S$ is
  Mathlib's `ContinuousOn f S`, which is continuity of the restriction of $f$ to $S$.
* Section 10, `Rockafellar.LipschitzianOn`: a real function $f$ is Lipschitzian relative to $S$ if
  $|f(y) - f(x)| \le \alpha \|y - x\|$ for all $x, y \in S$ and some $\alpha \ge 0$;
  `Rockafellar.lipschitzianOn_iff` relates it to Mathlib's `LipschitzOnWith`.
* Section 10, `Rockafellar.EquiLipschitzianOn`: a family is equi-Lipschitzian relative to $S$ if one
  $\alpha$ serves every member; `Rockafellar.equiLipschitzianOn_iff` gives one constant in `ℝ≥0` for
  the whole family.
* Section 10, `Rockafellar.PointwiseBoundedOn` and `Rockafellar.UniformlyBoundedOn`: a family is
  pointwise bounded on $S$ if its values at each point of $S$ are bounded, and uniformly bounded on
  $S$ if one bound serves all points and all members; `Rockafellar.pointwiseBoundedOn_iff` and
  `Rockafellar.uniformlyBoundedOn_iff` restate both.

## Main results

* Theorem 10.1, `Rockafellar.theorem_10_1`: a convex function is continuous relative to any
  relatively open convex subset of its effective domain.
* Corollary 10.1.1, `Rockafellar.corollary_10_1_1`: a convex function finite on all of
  $\mathbb{R}^n$ is continuous.
* Theorem 10.2, `Rockafellar.theorem_10_2` and `Rockafellar.theorem_10_2_closed`: a convex function
  is upper semicontinuous relative to any locally simplicial subset of $\operatorname{dom} f$, and
  continuous there if it is closed.
* Theorem 10.3, `Rockafellar.theorem_10_3` and `Rockafellar.theorem_10_3_unique`: a finite convex
  function on $\operatorname{ri} C$ that is bounded above on bounded subsets has a unique continuous
  convex extension to a locally simplicial convex set $C$.
* Theorem 10.4, `Rockafellar.theorem_10_4`: a proper convex function is Lipschitzian relative to any
  closed bounded subset of $\operatorname{ri}(\operatorname{dom} f)$.
* Theorem 10.5, `Rockafellar.theorem_10_5` and `Rockafellar.theorem_10_5_lipschitzian`: a finite
  convex function on $\mathbb{R}^n$ is uniformly continuous if and only if $f0^+$ is finite
  everywhere, and then it is Lipschitzian.
* Corollary 10.5.1, `Rockafellar.corollary_10_5_1`: a finite convex function is Lipschitzian if
  $\liminf_{\lambda \to \infty} f(\lambda y)/\lambda < \infty$ for every $y$.
* Corollary 10.5.2, `Rockafellar.corollary_10_5_2`: a finite convex function below a finite
  Lipschitzian convex function is Lipschitzian.
* Theorem 10.6, `Rockafellar.theorem_10_6` and `Rockafellar.theorem_10_6_ab`: a pointwise bounded
  family of finite convex functions on a relatively open convex set $C$ is uniformly bounded and
  equi-Lipschitzian on each closed bounded subset of $C$.
* Theorem 10.7, `Rockafellar.theorem_10_7` and `Rockafellar.theorem_10_7_dense`: a function on
  $C \times T$ that is convex in $x$ and continuous in $t$ is jointly continuous.
* Theorem 10.8, `Rockafellar.theorem_10_8`: pointwise convergence of finite convex functions on a
  dense subset of a relatively open convex set $C$ implies convergence on $C$ to a finite convex
  function, uniform on closed bounded subsets.
* Corollary 10.8.1, `Rockafellar.corollary_10_8_1`: if $\limsup_i f_i(x) \le f(x)$ on $C$, then
  $f_i \le f + \varepsilon$ on each closed bounded subset for all large $i$.
* Theorem 10.9, `Rockafellar.theorem_10_9`: a sequence of finite convex functions that is bounded at
  each point of a dense subset has a subsequence that converges uniformly on closed bounded subsets.

## Implementation notes

* A finite convex function on a set $C$ is Mathlib's real-valued `ConvexOn ℝ C`, and a relatively
  open set is one with $\operatorname{ri} C = C$. A finite convex function on $\mathbb{R}^n$ is a
  convex `f : Rockafellar.Rn n → EReal` that is proper and has
  $\operatorname{dom} f = \mathbb{R}^n$.
* The Lipschitz conditions concern real values, so the statements about an `EReal`-valued $f$ use
  the real function `fun x => (f x).toReal`. This function agrees with $f$ on $\operatorname{dom} f$
  when $f$ is proper.
* Locally simplicial sets are `ConvexAnalysis.LocallySimplicial`, the definition of the book without
  change.
* `Rockafellar.corollary_10_5_1` states the condition $\liminf_{\lambda \to \infty} f(\lambda
  y)/\lambda < \infty$ as: for some $c$, $f(\lambda y) \le c \lambda$ for arbitrarily large
  $\lambda$. This gives the same condition because $\lambda$ is eventually positive and $c$
  can be chosen strictly above the limit inferior.
* `Rockafellar.theorem_10_2` has no extra hypothesis. The proof of the book triangulates a simplex
  around an interior point, a step that the book calls intuitively obvious and does not prove. Here
  upper semicontinuity relative to a simplex is proved at every point of the simplex by a direct
  estimate in barycentric coordinates, so no result that uses Theorem 10.2 depends on an unproved
  step.

## Deviations from the source

* **Theorem 10.3**, existence (reading). The Lean result assumes $C$ nonempty and gives the
  closed proper convex ambient extension constructed in the proof. If $C$ is empty, its
  restricted extension is the empty function.
* **Theorem 10.3**, uniqueness (generalization). Agreement on $\operatorname{ri} C$ implies
  agreement on $C$ for any two continuous restrictions, without convexity of the functions or
  local simpliciality of $C$. See `Rockafellar.theorem_10_3_unique`.
* **Theorem 10.6**, hypotheses (a) and (b) (generalization). Boundedness replaces finiteness of
  the pointwise supremum and infimum, which also admits the empty family. Hypothesis (a) uses
  density as described below. See `Rockafellar.theorem_10_6_ab`.

## Not formalized

* **Theorem 10.6**, hypothesis (a) in the form of the book, $\operatorname{conv}(\operatorname{cl}
  C') \supseteq C$. `Rockafellar.theorem_10_6_ab` assumes the stronger condition
  $\operatorname{cl} C' \supseteq C$.
-/

open Filter Topology
open scoped NNReal

namespace Rockafellar

open ConvexAnalysis

/-! ### The definitions of Section 10 -/

/-- **Section 10** of [rockafellar1970convex], continuity relative to a set (page 82 of the book).
Let $f : \mathbb{R}^n \to [-\infty, +\infty]$ and $S \subseteq \mathbb{R}^n$. Then $f$ is
continuous at every point of $S$ relative to $S$ if and only if the restriction of $f$ to $S$ is
a continuous function.

The book defines continuity relative to $S$ by the restriction. The left side is Mathlib's
`ContinuousOn`, and the equivalence is a Mathlib lemma. -/
theorem continuousOn_iff_continuous_restrict_rn {n : ℕ} (f : Rn n → EReal) (S : Set (Rn n)) :
    ContinuousOn f S ↔ Continuous (S.domRestrict f) :=
  continuousOn_iff_continuous_domRestrict

/-- **Section 10** of [rockafellar1970convex], Lipschitzian functions (page 86 of the book). A real
function $f$ on $\mathbb{R}^n$ is **Lipschitzian relative to** $S \subseteq \mathbb{R}^n$ if
there is a real $\alpha \ge 0$ such that
$$|f(y) - f(x)| \le \alpha \|y - x\| \quad \text{for all } x, y \in S.$$
-/
def LipschitzianOn {n : ℕ} (f : Rn n → ℝ) (S : Set (Rn n)) : Prop :=
  ∃ α : ℝ, 0 ≤ α ∧ ∀ y ∈ S, ∀ x ∈ S, |f y - f x| ≤ α * ‖y - x‖

/-- **Section 10** of [rockafellar1970convex], equi-Lipschitzian families (page 88 of the book). A
family $\{f_i \mid i \in I\}$ of real functions on $\mathbb{R}^n$ is **equi-Lipschitzian
relative to** $S \subseteq \mathbb{R}^n$ if there is a real $\alpha \ge 0$ such that
$$|f_i(y) - f_i(x)| \le \alpha \|y - x\| \quad \text{for all } i \in I \text{ and all } x, y \in
  S.$$
-/
def EquiLipschitzianOn {n : ℕ} {ι : Type*} (f : ι → Rn n → ℝ) (S : Set (Rn n)) : Prop :=
  ∃ α : ℝ, 0 ≤ α ∧ ∀ i, ∀ y ∈ S, ∀ x ∈ S, |f i y - f i x| ≤ α * ‖y - x‖

/-- **Section 10** of [rockafellar1970convex], pointwise bounded families (page 88 of the book). A
family $\{f_i \mid i \in I\}$ of real functions on $\mathbb{R}^n$ is **pointwise bounded on**
$S \subseteq \mathbb{R}^n$ if, for each $x \in S$, the set of real numbers
$\{f_i(x) \mid i \in I\}$ is bounded. -/
def PointwiseBoundedOn {n : ℕ} {ι : Type*} (f : ι → Rn n → ℝ) (S : Set (Rn n)) : Prop :=
  ∀ x ∈ S, Bornology.IsBounded (Set.range fun i => f i x)

/-- **Section 10** of [rockafellar1970convex], uniformly bounded families (page 88 of the book). A
family $\{f_i \mid i \in I\}$ of real functions on $\mathbb{R}^n$ is **uniformly bounded on**
$S \subseteq \mathbb{R}^n$ if there are real numbers $\alpha_1$ and $\alpha_2$ such that
$$\alpha_1 \le f_i(x) \le \alpha_2 \quad \text{for all } x \in S \text{ and all } i \in I.$$
-/
def UniformlyBoundedOn {n : ℕ} {ι : Type*} (f : ι → Rn n → ℝ) (S : Set (Rn n)) : Prop :=
  ∃ α₁ α₂ : ℝ, ∀ x ∈ S, ∀ i, α₁ ≤ f i x ∧ f i x ≤ α₂

/-- Let $f$ be a real function on $\mathbb{R}^n$ and $S \subseteq \mathbb{R}^n$. Then $f$ is
Lipschitzian relative to $S$ if and only if there is a constant $K \ge 0$ with
`LipschitzOnWith K f S`, that is, $|f(y) - f(x)| \le K \|y - x\|$ for all $x, y \in S$. -/
theorem lipschitzianOn_iff {n : ℕ} {f : Rn n → ℝ} {S : Set (Rn n)} :
    LipschitzianOn f S ↔ ∃ K : ℝ≥0, LipschitzOnWith K f S := by
  constructor
  · rintro ⟨α, hα, h⟩
    refine ⟨α.toNNReal, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal α hα]
    exact h x hx y hy
  · rintro ⟨K, hK⟩
    refine ⟨K, K.coe_nonneg, fun y hy x hx => ?_⟩
    have h := hK.dist_le_mul y hy x hx
    rwa [Real.dist_eq, dist_eq_norm] at h

/-- Let $\{f_i \mid i \in I\}$ be a family of real functions on $\mathbb{R}^n$ and
$S \subseteq \mathbb{R}^n$. Then the family is equi-Lipschitzian relative to $S$ if and only if
there is one constant $K \ge 0$ with `LipschitzOnWith K (f i) S` for every $i \in I$. -/
theorem equiLipschitzianOn_iff {n : ℕ} {ι : Type*} {f : ι → Rn n → ℝ} {S : Set (Rn n)} :
    EquiLipschitzianOn f S ↔ ∃ K : ℝ≥0, ∀ i, LipschitzOnWith K (f i) S := by
  constructor
  · rintro ⟨α, hα, h⟩
    refine ⟨α.toNNReal, fun i => LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal α hα]
    exact h i x hx y hy
  · rintro ⟨K, hK⟩
    refine ⟨K, K.coe_nonneg, fun i y hy x hx => ?_⟩
    have h := (hK i).dist_le_mul y hy x hx
    rwa [Real.dist_eq, dist_eq_norm] at h

/-- Let $\{f_i \mid i \in I\}$ be a family of real functions on $\mathbb{R}^n$ and
$S \subseteq \mathbb{R}^n$. Then the family is pointwise bounded on $S$ if and only if, for each
$x \in S$, the set $\{f_i(x) \mid i \in I\}$ is bounded below and bounded above.

This two-sided form is the form of the hypotheses of the backbone. -/
theorem pointwiseBoundedOn_iff {n : ℕ} {ι : Type*} {f : ι → Rn n → ℝ} {S : Set (Rn n)} :
    PointwiseBoundedOn f S ↔ ∀ x ∈ S, BddBelow (Set.range fun i => f i x) ∧
      BddAbove (Set.range fun i => f i x) :=
  forall₂_congr fun _ _ => isBounded_iff_bddBelow_bddAbove

/-- Let $\{f_i \mid i \in I\}$ be a family of real functions on $\mathbb{R}^n$ and
$S \subseteq \mathbb{R}^n$. Then the family is uniformly bounded on $S$ if and only if there is
a real $M \ge 0$ with $|f_i(x)| \le M$ for all $i \in I$ and all $x \in S$.

This form is the form of the conclusions of the backbone. -/
theorem uniformlyBoundedOn_iff {n : ℕ} {ι : Type*} {f : ι → Rn n → ℝ} {S : Set (Rn n)} :
    UniformlyBoundedOn f S ↔ ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ S, |f i x| ≤ M := by
  constructor
  · rintro ⟨α₁, α₂, h⟩
    refine ⟨max |α₁| |α₂|, le_trans (abs_nonneg α₁) (le_max_left _ _), fun i x hx => ?_⟩
    obtain ⟨h₁, h₂⟩ := h x hx i
    refine abs_le.2 ⟨?_, ?_⟩
    · have hm : |α₁| ≤ max |α₁| |α₂| := le_max_left _ _
      have hn : -|α₁| ≤ α₁ := neg_abs_le α₁
      linarith
    · have hm : |α₂| ≤ max |α₁| |α₂| := le_max_right _ _
      have hn : α₂ ≤ |α₂| := le_abs_self α₂
      linarith
  · rintro ⟨M, -, hM⟩
    exact ⟨-M, M, fun x hx i => abs_le.1 (hM i x hx)⟩

/-! ### Theorem 10.1 -/

/-- **Theorem 10.1** of [rockafellar1970convex]. Let $f$ be a convex function on $\mathbb{R}^n$, and
let $C$ be a relatively open convex set in $\operatorname{dom} f$. Then $f$ is continuous
relative to $C$.

In particular $f$ is continuous relative to $\operatorname{ri}(\operatorname{dom} f)$, which is
the form that Corollary 10.1.1 and Theorem 10.4 use. Improper $f$ is not excluded. Continuity is
in the topology of $[-\infty, +\infty]$, and "relatively open" is $\operatorname{ri} C = C$. -/
theorem theorem_10_1 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) {C : Set (Rn n)}
    (hC : Convex ℝ C) (hCro : ri C = C) (hCdom : C ⊆ convexDom f) : ContinuousOn f C := by
  have hg : ConvexFn (convexRestrict C f) := hf.convexRestrict hC
  have hdom : convexDom (convexRestrict C f) = C := by
    ext x
    constructor
    · intro hx
      by_contra hxC
      rw [mem_convexDom, convexRestrict_of_notMem hxC] at hx
      exact absurd hx (lt_irrefl _)
    · intro hx
      rw [mem_convexDom, convexRestrict_of_mem hx]
      exact mem_convexDom.1 (hCdom hx)
  have hri : ri (convexDom (convexRestrict C f)) = C := by rw [hdom, hCro]
  by_cases hp : ProperConvex (convexRestrict C f)
  · have hcont : ContinuousOn (convexRestrict C f) C := by
      have h := hg.continuousOn_relint_convexDom hp
      rwa [hri] at h
    exact hcont.congr fun x hx => (convexRestrict_of_mem hx).symm
  · have hconst : ContinuousOn (fun _ : Rn n => (⊥ : EReal)) C := continuousOn_const
    refine hconst.congr fun x hx => ?_
    have hx' : x ∈ ri (convexDom (convexRestrict C f)) := by rw [hri]; exact hx
    have hbot := hg.eq_bot_of_mem_relint_convexDom hp hx'
    rwa [convexRestrict_of_mem hx] at hbot

/-! ### Corollary 10.1.1 -/

/-- **Corollary 10.1.1** of [rockafellar1970convex]. A convex function $f$ finite on all of
$\mathbb{R}^n$ is necessarily continuous.

"Finite on all of $\mathbb{R}^n$" is $\operatorname{dom} f = \mathbb{R}^n$ together with
properness, which gives $f > -\infty$. -/
theorem corollary_10_1_1 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) : Continuous f :=
  hf.continuous_of_convexDom_eq_univ hp hdom

/-! ### Theorem 10.2 -/

/-- **Theorem 10.2** of [rockafellar1970convex]. Let $f$ be a convex function on $\mathbb{R}^n$, and
let $S$ be any locally simplicial subset of $\operatorname{dom} f$. Then $f$ is upper
semicontinuous relative to $S$.

Improper $f$ is not excluded. The proof of the book triangulates a simplex around an interior
point, a step that it calls intuitively obvious and does not prove. The proof here instead
obtains upper semicontinuity relative to a simplex at every point of the simplex by a direct
estimate in barycentric coordinates. -/
theorem theorem_10_2 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) {S : Set (Rn n)}
    (hS : LocallySimplicial S) (hSdom : S ⊆ convexDom f) : UpperSemicontinuousOn f S :=
  hf.upperSemicontinuousOn_of_locallySimplicial hS hSdom

/-- **Theorem 10.2** of [rockafellar1970convex], second assertion. Let $f$ be a closed convex
function on $\mathbb{R}^n$, and let $S$ be any locally simplicial subset of
$\operatorname{dom} f$. Then $f$ is continuous relative to $S$. -/
theorem theorem_10_2_closed {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hcl : ClosedConvex f)
    {S : Set (Rn n)} (hS : LocallySimplicial S) (hSdom : S ⊆ convexDom f) : ContinuousOn f S :=
  hf.continuousOn_of_locallySimplicial (ClosedConvex.lowerSemicontinuous hcl) hS hSdom

/-! ### Theorem 10.3 -/

/-- **Theorem 10.3** of [rockafellar1970convex]. Let $C$ be a nonempty locally simplicial convex set
in $\mathbb{R}^n$, and let $f$ be a finite convex function on $\operatorname{ri} C$ which is
bounded above on every bounded subset of $\operatorname{ri} C$. Then $f$ can be extended to a
continuous finite convex function on the whole of $C$: there is a closed proper convex function
$g$ on $\mathbb{R}^n$ with $g = f$ on $\operatorname{ri} C$, $C \subseteq \operatorname{dom} g$,
and $g$ continuous relative to $C$.

A finite convex function on $\operatorname{ri} C$ is a convex
$f : \mathbb{R}^n \to [-\infty, +\infty]$ with $f > -\infty$ everywhere and
$\operatorname{dom} f = \operatorname{ri} C$; this is how §4 reads a function given only on a
set. The proof takes $g = \operatorname{cl} f$. Uniqueness of the extension is
`Rockafellar.theorem_10_3_unique`.

**Reading.** The book allows arbitrary locally simplicial convex $C$. The Lean result assumes
$C$ nonempty and gives the closed proper convex ambient extension constructed in the proof.
For empty $C$, the extension restricted to $C$ is the empty function. -/
theorem theorem_10_3 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) (hCls : LocallySimplicial C)
    (hne : C.Nonempty) {f : Rn n → EReal} (hf : ConvexFn f) (hbot : ∀ x, f x ≠ ⊥)
    (hdom : convexDom f = ri C)
    (hbdd : ∀ S ⊆ ri C, Bornology.IsBounded S → ∃ c : ℝ, ∀ x ∈ S, f x ≤ (c : EReal)) :
    ∃ g : Rn n → EReal, ConvexFn g ∧ ClosedConvex g ∧ ProperConvex g ∧ Set.EqOn g f (ri C) ∧
      C ⊆ convexDom g ∧ ContinuousOn g C :=
  exists_closedConvex_continuousOn_of_locallySimplicial hC hCls hne hf hbot hdom hbdd

/-- **Theorem 10.3** of [rockafellar1970convex], uniqueness. Let $C$ be a convex set in
$\mathbb{R}^n$, and let $g_1, g_2 : \mathbb{R}^n \to [-\infty, +\infty]$ be continuous relative
to $C$ with $g_1 = g_2$ on $\operatorname{ri} C$. Then $g_1 = g_2$ on $C$.

**Generalization.** The book states uniqueness for finite convex extensions on a locally
simplicial convex set. Here continuity relative to $C$ suffices because
$C \subseteq \operatorname{cl}(\operatorname{ri} C)$. -/
theorem theorem_10_3_unique {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) {g₁ g₂ : Rn n → EReal}
    (h₁ : ContinuousOn g₁ C) (h₂ : ContinuousOn g₂ C) (h : Set.EqOn g₁ g₂ (ri C)) :
    Set.EqOn g₁ g₂ C :=
  eqOn_of_continuousOn_of_eqOn_relint hC h₁ h₂ h

/-! ### Theorem 10.4 -/

/-- **Theorem 10.4** of [rockafellar1970convex]. Let $f$ be a proper convex function on
$\mathbb{R}^n$, and let $S$ be any closed bounded subset of
$\operatorname{ri}(\operatorname{dom} f)$. Then $f$ is Lipschitzian relative to $S$.

The Lipschitz condition concerns real values, so the statement is about the real function
`fun x => (f x).toReal`, which agrees with $f$ on $\operatorname{dom} f$ because $f$ is proper. -/
theorem theorem_10_4 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    {S : Set (Rn n)} (hScl : IsClosed S) (hSb : Bornology.IsBounded S)
        (hSri : S ⊆ ri (convexDom f)) :
    LipschitzianOn (fun x => (f x).toReal) S :=
  lipschitzianOn_iff.2
    (hf.exists_lipschitzOnWith_of_isCompact hp (Metric.isCompact_of_isClosed_isBounded hScl hSb)
      hSri)

/-! ### Theorem 10.5 -/

/-- **Theorem 10.5** of [rockafellar1970convex]. Let $f$ be a finite convex function on
$\mathbb{R}^n$. In order that $f$ be uniformly continuous relative to $\mathbb{R}^n$, it is
necessary and sufficient that the recession function $f0^+$ be finite everywhere.

"Finite everywhere" is stated as $(f0^+)(y) < +\infty$ for every $y$; the condition
$(f0^+)(y) > -\infty$ follows from properness of $f$. Uniform continuity is about the real
function `fun x => (f x).toReal`. -/
theorem theorem_10_5 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) :
    (UniformContinuous fun x => (f x).toReal) ↔ ∀ y, recessionFn f y ≠ ⊤ :=
  hf.uniformContinuous_toReal_iff hp hdom

/-- **Theorem 10.5** of [rockafellar1970convex], second assertion. Let $f$ be a finite convex
function on $\mathbb{R}^n$ such that $(f0^+)(y) < +\infty$ for every $y$. Then $f$ is
Lipschitzian relative to $\mathbb{R}^n$.

The book gives the constant $\alpha = \sup\{(f0^+)(z) \mid \|z\| = 1\}$. The statement here
asserts only that some constant exists. -/
theorem theorem_10_5_lipschitzian {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) (hrec : ∀ y, recessionFn f y ≠ ⊤) :
    LipschitzianOn (fun x => (f x).toReal) Set.univ := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzWith_of_recessionFn_ne_top hp hdom hrec
  exact lipschitzianOn_iff.2 ⟨K, hK.lipschitzOnWith⟩

/-! ### Corollary 10.5.1 -/

/-- **Corollary 10.5.1** of [rockafellar1970convex]. Let $f$ be a finite convex function on
$\mathbb{R}^n$ such that
$$\liminf_{\lambda \to \infty} \frac{f(\lambda y)}{\lambda} < \infty \quad \text{for every }
  y.$$
Then $f$ is Lipschitzian relative to $\mathbb{R}^n$.

The condition on the $\liminf$ is stated as: for every $y$ there is a real $c$ with
$f(\lambda y) \le c \lambda$ for arbitrarily large $\lambda$. This avoids a convention for the
quotient in `EReal`. The two conditions agree because the quotient is nondecreasing in $\lambda$
(Theorem 8.5). -/
theorem corollary_10_5_1 {n : ℕ} {f : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ)
    (h : ∀ y : Rn n, ∃ c : ℝ, ∃ᶠ a : ℝ in atTop, f (a • y) ≤ ((c * a : ℝ) : EReal)) :
    LipschitzianOn (fun x => (f x).toReal) Set.univ := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzWith_of_frequently_le hp hdom h
  exact lipschitzianOn_iff.2 ⟨K, hK.lipschitzOnWith⟩

/-! ### Corollary 10.5.2 -/

/-- **Corollary 10.5.2** of [rockafellar1970convex]. Let $f$ and $g$ be finite convex functions on
$\mathbb{R}^n$ such that $g$ is Lipschitzian relative to $\mathbb{R}^n$ and $f(x) \le g(x)$ for
every $x$. Then $f$ is Lipschitzian relative to $\mathbb{R}^n$.

Convexity of $g$ is a hypothesis so that the statement is the one of the book; the proof uses
only that $g$ is finite and Lipschitzian. -/
theorem corollary_10_5_2 {n : ℕ} {f g : Rn n → EReal} (hf : ConvexFn f) (hp : ProperConvex f)
    (hdom : convexDom f = Set.univ) (_hg : ConvexFn g) (hgp : ProperConvex g)
        (hgdom : convexDom g = Set.univ)
    (hglip : LipschitzianOn (fun x => (g x).toReal) Set.univ) (hle : ∀ x, f x ≤ g x) :
    LipschitzianOn (fun x => (f x).toReal) Set.univ := by
  obtain ⟨K, hK⟩ := lipschitzianOn_iff.1 hglip
  rw [lipschitzOnWith_univ] at hK
  obtain ⟨K', hK'⟩ := hf.exists_lipschitzWith_of_le_lipschitz hp hdom hK fun x => by
    rw [coe_toReal_of_convexDom_eq_univ hgp hgdom x]; exact hle x
  exact lipschitzianOn_iff.2 ⟨K', hK'.lipschitzOnWith⟩

/-! ### Theorem 10.6 -/

/-- **Theorem 10.6** of [rockafellar1970convex]. Let $C$ be a relatively open convex set in
$\mathbb{R}^n$, and let $\{f_i \mid i \in I\}$ be an arbitrary collection of convex functions
finite and pointwise bounded on $C$. Let $S$ be any closed bounded subset of $C$. Then
$\{f_i \mid i \in I\}$ is uniformly bounded on $S$ and equi-Lipschitzian relative to $S$.

"Relatively open" is $\operatorname{ri} C = C$, and "finite and convex on $C$" is Mathlib's
real-valued `ConvexOn ℝ C`, which matches the collection of the book. The index set $I$ may be
empty. -/
theorem theorem_10_6 {n : ℕ} {ι : Type*} {C : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C)
    {f : ι → Rn n → ℝ} (hf : ∀ i, ConvexOn ℝ C (f i)) (hbdd : PointwiseBoundedOn f C)
    {S : Set (Rn n)} (hScl : IsClosed S) (hSb : Bornology.IsBounded S) (hSC : S ⊆ C) :
    UniformlyBoundedOn f S ∧ EquiLipschitzianOn f S := by
  have hbdd' : ∀ x ∈ ri C, Bornology.IsBounded (Set.range fun i => f i x) := by
    rw [hCro]; exact hbdd
  have hSC' : S ⊆ ri C := by rw [hCro]; exact hSC
  obtain ⟨hub, hlip⟩ := exists_forall_abs_le_and_lipschitzOnWith_of_isCompact_relint hC hf hbdd'
    (Metric.isCompact_of_isClosed_isBounded hScl hSb) hSC'
  exact ⟨uniformlyBoundedOn_iff.2 hub, equiLipschitzianOn_iff.2 hlip⟩

/-- **Theorem 10.6** of [rockafellar1970convex], weakened hypotheses. Let $C$ be a relatively open
convex set in $\mathbb{R}^n$, and let $\{f_i \mid i \in I\}$ be a collection of finite convex
functions on $C$. Suppose that

(a) there is a subset $C'$ of $C$ with $\operatorname{cl} C' \supseteq C$ such that
$\{f_i(x) \mid i \in I\}$ is bounded above for each $x \in C'$, and

(b) there is at least one $x \in C$ at which $\{f_i(x) \mid i \in I\}$ is bounded below.

Let $S$ be any closed bounded subset of $C$. Then $\{f_i \mid i \in I\}$ is uniformly bounded on
$S$ and equi-Lipschitzian relative to $S$.

The book's condition (a) asks only $\operatorname{conv}(\operatorname{cl} C') \supseteq C$,
while the Lean statement assumes $\operatorname{cl} C' \supseteq C$.

**Generalization.** For both hypotheses, boundedness replaces finiteness of the corresponding
pointwise supremum or infimum. These agree for nonempty families, and the Lean boundedness
conditions also apply to the empty family. -/
theorem theorem_10_6_ab {n : ℕ} {ι : Type*} {C C' : Set (Rn n)} (hC : Convex ℝ C)
    (hCro : ri C = C) {f : ι → Rn n → ℝ} (hf : ∀ i, ConvexOn ℝ C (f i)) (hC'sub : C' ⊆ C)
    (hdense : C ⊆ closure C') (hab : ∀ x ∈ C', BddAbove (Set.range fun i => f i x))
    (hbe : ∃ z ∈ C, BddBelow (Set.range fun i => f i z))
    {S : Set (Rn n)} (hScl : IsClosed S) (hSb : Bornology.IsBounded S) (hSC : S ⊆ C) :
    UniformlyBoundedOn f S ∧ EquiLipschitzianOn f S := by
  have hC'ri : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hdense' : ri C ⊆ closure C' := by rw [hCro]; exact hdense
  have hbe' : ∃ z ∈ ri C, BddBelow (Set.range fun i => f i z) := by rw [hCro]; exact hbe
  have hSC' : S ⊆ ri C := by rw [hCro]; exact hSC
  have hS : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  exact ⟨uniformlyBoundedOn_iff.2
      (exists_forall_abs_le_of_isCompact_relint hC hf hC'ri hdense' hab hbe' hS hSC'),
    equiLipschitzianOn_iff.2
      (exists_forall_lipschitzOnWith_of_isCompact_relint hC hf hC'ri hdense' hab hbe' hS hSC')⟩

/-! ### Theorem 10.7 -/

/-- **Theorem 10.7** of [rockafellar1970convex]. Let $C$ be a relatively open convex set in
$\mathbb{R}^n$, let $T$ be any locally compact topological space, and let $f$ be a real-valued
function on $C \times T$ such that $f(x, t)$ is convex in $x$ for each $t$ and continuous in $t$
for each $x$. Then $f$ is continuous on $C \times T$, that is, jointly continuous in $x$ and
$t$.

The function is `F : Rockafellar.Rn n × T → ℝ`, and $T$ is a type, so the conclusion is
continuity on `C ×ˢ Set.univ`. -/
theorem theorem_10_7 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C) {T : Type*}
    [TopologicalSpace T] [LocallyCompactSpace T] {F : Rn n × T → ℝ}
    (hconv : ∀ t : T, ConvexOn ℝ C fun x => F (x, t))
    (hcont : ∀ x ∈ C, Continuous fun t => F (x, t)) :
    ContinuousOn F (C ×ˢ (Set.univ : Set T)) := by
  have hsub : C ⊆ ri C := by rw [hCro]
  have hdense : ri C ⊆ closure C := by rw [hCro]; exact subset_closure
  have h := continuousOn_prod_of_convexOn_relint (C' := C) hC hconv hsub hdense hcont
  rwa [hCro] at h

/-- **Theorem 10.7** of [rockafellar1970convex], weakened hypothesis. In Theorem 10.7 it is enough
that $f(x, t)$ be continuous in $t$ for each $x$ in some subset $C'$ of $C$ with
$\operatorname{cl} C' \supseteq C$.

The proof specializes `ConvexAnalysis.continuousOn_prod_of_convexOn_relint`. -/
theorem theorem_10_7_dense {n : ℕ} {C C' : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C)
    {T : Type*} [TopologicalSpace T] [LocallyCompactSpace T] {F : Rn n × T → ℝ}
    (hconv : ∀ t : T, ConvexOn ℝ C fun x => F (x, t)) (hC'sub : C' ⊆ C)
    (hdense : C ⊆ closure C') (hcont : ∀ x ∈ C', Continuous fun t => F (x, t)) :
    ContinuousOn F (C ×ˢ (Set.univ : Set T)) := by
  have hsub : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hdense' : ri C ⊆ closure C' := by rw [hCro]; exact hdense
  have h := continuousOn_prod_of_convexOn_relint hC hconv hsub hdense' hcont
  rwa [hCro] at h

/-! ### Theorem 10.8 -/

/-- **Theorem 10.8** of [rockafellar1970convex]. Let $C$ be a relatively open convex set in
$\mathbb{R}^n$, and let $f_1, f_2, \dots$ be a sequence of finite convex functions on $C$.
Suppose that the sequence converges pointwise on a subset $C'$ of $C$ with
$\operatorname{cl} C' \supseteq C$. Then there is a finite convex function $f$ on $C$ such that
$f_i(x) \to f(x)$ for every $x \in C$, and the convergence is uniform on each closed bounded
subset of $C$. -/
theorem theorem_10_8 {n : ℕ} {C C' : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C)
    {f : ℕ → Rn n → ℝ} (hf : ∀ i, ConvexOn ℝ C (f i)) (hC'sub : C' ⊆ C)
    (hdense : C ⊆ closure C')
    (hcv : ∀ x ∈ C', ∃ L : ℝ, Tendsto (fun i => f i x) atTop (𝓝 L)) :
    ∃ g : Rn n → ℝ, ConvexOn ℝ C g ∧ (∀ x ∈ C, Tendsto (fun i => f i x) atTop (𝓝 (g x))) ∧
      ∀ ⦃S : Set (Rn n)⦄, IsClosed S → Bornology.IsBounded S → S ⊆ C →
        TendstoUniformlyOn f g atTop S := by
  have hsub : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hdense' : ri C ⊆ closure C' := by rw [hCro]; exact hdense
  obtain ⟨g, hgc, hgt, hgu⟩ := exists_tendstoUniformlyOn_of_dense_relint hC hf hsub hdense' hcv
  rw [hCro] at hgc hgt hgu
  exact ⟨g, hgc, hgt, fun S hScl hSb hSC =>
    hgu (Metric.isCompact_of_isClosed_isBounded hScl hSb) hSC⟩

/-! ### Corollary 10.8.1 -/

/-- **Corollary 10.8.1** of [rockafellar1970convex]. Let $f$ be a finite convex function on a
relatively open convex set $C$ in $\mathbb{R}^n$, and let $f_1, f_2, \dots$ be finite convex
functions on $C$ with
$$\limsup_{i \to \infty} f_i(x) \le f(x) \quad \text{for every } x \in C.$$
Then for each closed bounded subset $S$ of $C$ and each $\varepsilon > 0$ there is an index
$i_0$ such that $f_i(x) \le f(x) + \varepsilon$ for all $i \ge i_0$ and all $x \in S$.

The hypothesis on the $\limsup$ is stated as: for every $x \in C$ and every $\delta > 0$,
eventually $f_i(x) \le f(x) + \delta$. This is its meaning for a real sequence. The function $f$
is `g`. -/
theorem corollary_10_8_1 {n : ℕ} {C : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C)
    {f : ℕ → Rn n → ℝ} (hf : ∀ i, ConvexOn ℝ C (f i)) {g : Rn n → ℝ} (hg : ConvexOn ℝ C g)
    (hle : ∀ x ∈ C, ∀ δ > 0, ∀ᶠ i in atTop, f i x ≤ g x + δ)
    {S : Set (Rn n)} (hScl : IsClosed S) (hSb : Bornology.IsBounded S) (hSC : S ⊆ C)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ i in atTop, ∀ x ∈ S, f i x ≤ g x + ε := by
  have hle' : ∀ x ∈ ri C, ∀ δ > 0, ∀ᶠ i in atTop, f i x ≤ g x + δ := by rw [hCro]; exact hle
  have hSC' : S ⊆ ri C := by rw [hCro]; exact hSC
  exact eventually_forall_le_add_of_eventually_le_relint hC hf hg hle'
    (Metric.isCompact_of_isClosed_isBounded hScl hSb) hSC' hε

/-! ### Theorem 10.9 -/

/-- **Theorem 10.9** of [rockafellar1970convex]. Let $C$ be a relatively open convex set in
$\mathbb{R}^n$, and let $f_1, f_2, \dots$ be a sequence of finite convex functions on $C$.
Suppose that the values $f_i(x)$ are bounded for each point $x$ of a subset $C'$ of $C$ with
$\operatorname{cl} C' \supseteq C$. Then there is a subsequence that converges pointwise on $C$
to some finite convex function $f$ on $C$, uniformly on each closed bounded subset of $C$.

The subsequence is given by a strictly increasing map $\varphi : \mathbb{N} \to \mathbb{N}$, and
the limit function is `g`. -/
theorem theorem_10_9 {n : ℕ} {C C' : Set (Rn n)} (hC : Convex ℝ C) (hCro : ri C = C)
    {f : ℕ → Rn n → ℝ} (hf : ∀ i, ConvexOn ℝ C (f i)) (hC'sub : C' ⊆ C)
    (hdense : C ⊆ closure C') (hbdd : PointwiseBoundedOn f C') :
    ∃ (φ : ℕ → ℕ) (g : Rn n → ℝ), StrictMono φ ∧ ConvexOn ℝ C g ∧
      (∀ x ∈ C, Tendsto (fun i => f (φ i) x) atTop (𝓝 (g x))) ∧
      ∀ ⦃S : Set (Rn n)⦄, IsClosed S → Bornology.IsBounded S → S ⊆ C →
        TendstoUniformlyOn (fun i => f (φ i)) g atTop S := by
  have hsub : C' ⊆ ri C := by rw [hCro]; exact hC'sub
  have hdense' : ri C ⊆ closure C' := by rw [hCro]; exact hdense
  obtain ⟨φ, g, hφ, hgc, hgt, hgu⟩ :=
    exists_subseq_tendstoUniformlyOn_relint hC hf hsub hdense' hbdd
  rw [hCro] at hgc hgt hgu
  exact ⟨φ, g, hφ, hgc, hgt, fun S hScl hSb hSC =>
    hgu (Metric.isCompact_of_isClosed_isBounded hScl hSb) hSC⟩

end Rockafellar
