/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Homogeneous

/-!
# Support functions

Let $B$ be a bilinear pairing of real vector spaces $E$ and $F$, written
$\langle x, y \rangle = B(x, y)$. The **support function** of a set $s \subseteq E$ is the function
on $F$
$$\delta^*(y \mid s) = \sup \{\langle x, y \rangle \mid x \in s\},$$
with values in the extended reals. It describes all the closed half-spaces that contain $s$, since
$s \subseteq \{x \mid \langle x, y \rangle \le c\}$ exactly when $\delta^*(y \mid s) \le c$. Support
functions are the conjugates of indicator functions, so every property of $\delta^*(\cdot \mid s)$
is inherited from the conjugate in `Numlib.Analysis.Convex.Duality.Conjugate`. The presentation
follows §13 of [rockafellar1970convex].

The main theorem is a correspondence: the support functions of the nonempty convex sets are exactly
the closed proper positively homogeneous convex functions, and the two classes are in bijection. The
support function lives on the other side of the pairing: for $s \subseteq E$ it is a function on
$F$. The correspondence asks that a function on $F$ be closed and that the set that it supports be
closed in $E$, so it needs a topology and a compatible pairing on both sides.

## Main definitions

* `ConvexAnalysis.supportFn`: the support function $\delta^*(\cdot \mid s)$.
* `ConvexAnalysis.supportSet`: the set $\{y \mid \langle x, y \rangle \le f(x) \text{ for all }
  x\}$, whose support function is $f$ when $f$ is closed, proper, positively homogeneous and convex.
  It inverts the correspondence.
* `ConvexAnalysis.supportEquiv`: the correspondence as a bijection between the nonempty closed
  convex subsets of $E$ and the closed proper positively homogeneous convex functions on $F$.

## Main results

* `ConvexAnalysis.supportFn_eq_convexConj_indicatorFn`: the support function is the conjugate of the
  indicator function, $\delta^*(\cdot \mid s) = (\delta(\cdot \mid s))^*$.
* `ConvexAnalysis.mem_closure_convexHull_iff_le_supportFn`:
  $x \in \operatorname{cl}(\operatorname{conv} s)$ if and only if
  $\langle x, y \rangle \le \delta^*(y \mid s)$ for every $y$ (Theorem 13.1 of
  [rockafellar1970convex]).
* `ConvexAnalysis.convexConj_supportFn`, `ConvexAnalysis.exists_supportFn_iff`,
  `ConvexAnalysis.supportEquiv`: the indicator function and the support function of a closed convex
  set are conjugate, and the correspondence above (Theorem 13.2 of [rockafellar1970convex]).
  `ConvexAnalysis.exists_supportFn_finite_iff` is the form in which bounded sets correspond to
  finite functions.
* `ConvexAnalysis.convexCl_eq_supportFn_of_posHomogeneous`: the closure of a positively homogeneous
  convex function is a support function. `ConvexAnalysis.supportSet_convexCl` is the consequence
  that closure does not change the set supported.
* `ConvexAnalysis.convexConj_eq_indicatorFn_of_posHomogeneous`: the conjugate of a positively
  homogeneous function that is not identically $+\infty$ is an indicator function.
* `ConvexAnalysis.supportFn_singleton`, `ConvexAnalysis.supportFn_union`,
  `ConvexAnalysis.supportFn_convexHull`, `ConvexAnalysis.supportFn_closure`,
  `ConvexAnalysis.supportFn_smul`, `ConvexAnalysis.supportFn_add`: the support functions of the
  basic constructions.

## Proof outline

The conjugate of a positively homogeneous function is an indicator function. Reindexing the supremum
that defines $f^*$ along $x \mapsto ax$ gives $f^*(y) = a f^*(y)$ for every $a > 0$, so $f^*(y)$ is
$0$, $+\infty$ or $-\infty$, and $-\infty$ is excluded as soon as $f$ is not identically $+\infty$.
No topology is used, so the correspondence needs no separation theory beyond what biconjugation
already uses.

## Implementation notes

* The finite form of the correspondence needs closedness. The classical deduction that a finite
  positively homogeneous convex function is a support function uses the fact that a finite convex
  function on $\mathbb{R}^n$ is closed. This fact is false in infinite dimensions: a discontinuous
  linear functional is finite, convex and positively homogeneous, is not closed, and is the support
  function of no set. Therefore `ConvexAnalysis.exists_supportFn_finite_iff` assumes that the
  function is closed. It reads "bounded" as "$\langle \cdot, y \rangle$ is bounded above on the set,
  for each $y$", which is what the classical proof uses.
-/

open Set Pointwise

namespace ConvexAnalysis

/-! ### The support function -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The **support function** of a set $s \subseteq E$ with respect to the pairing $B$ is the
function $\delta^*(\cdot \mid s) : F \to [-\infty, +\infty]$,
$$\delta^*(y \mid s) = \sup \{\langle x, y \rangle \mid x \in s\}.$$

It is $-\infty$ everywhere when $s$ is empty. The notation $\delta^*$ is justified by
`ConvexAnalysis.supportFn_eq_convexConj_indicatorFn`: the support function is the conjugate of
the indicator function of $s$. -/
noncomputable def supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) : F → EReal :=
  fun y => ⨆ x ∈ s, ((B x y : ℝ) : EReal)

variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s t : Set E} {x : E} {y : F}

/-- The support function takes at $y$ the value $\sup_{x \in s} \langle x, y \rangle$. -/
theorem supportFn_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) (y : F) :
    supportFn B s y = ⨆ x ∈ s, ((B x y : ℝ) : EReal) := rfl

/-- **Support functions are conjugates of indicators.** For every set $s \subseteq E$,
$$\delta^*(\cdot \mid s) = (\delta(\cdot \mid s))^*,$$
where $\delta(\cdot \mid s)$ is $0$ on $s$ and $+\infty$ elsewhere, and the conjugate is taken
with respect to $B$.

Because of this identity, most properties of $\delta^*(\cdot \mid s)$ in this module are
properties of a conjugate, taken from `Numlib.Analysis.Convex.Duality.Conjugate`. -/
theorem supportFn_eq_convexConj_indicatorFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    supportFn B s = convexConj B (indicatorFn s) := by
  funext y
  rw [convexConj_apply]
  refine iSup_congr fun x => ?_
  by_cases hx : x ∈ s
  · rw [iSup_pos hx, indicatorFn_of_mem hx, sub_zero]
  · rw [iSup_neg hx, indicatorFn_of_notMem hx, EReal.sub_top]

/-- If $x \in s$, then $\langle x, y \rangle \le \delta^*(y \mid s)$ for every $y \in F$. -/
theorem le_supportFn (hx : x ∈ s) (y : F) : ((B x y : ℝ) : EReal) ≤ supportFn B s y :=
  le_iSup₂ (f := fun x (_ : x ∈ s) => ((B x y : ℝ) : EReal)) x hx

/-- For an extended real $c$, $\delta^*(y \mid s) \le c$ if and only if $\langle x, y \rangle \le c$
for every $x \in s$. -/
theorem supportFn_le_iff {c : EReal} :
    supportFn B s y ≤ c ↔ ∀ x ∈ s, ((B x y : ℝ) : EReal) ≤ c := iSup₂_le_iff

/-- **The closed half-spaces that contain $s$.** For a real number $c$, $\delta^*(y \mid s) \le c$
if and only if $\langle x, y \rangle \le c$ for every $x \in s$, that is, if and only if $s
\subseteq \{x \mid \langle x, y \rangle \le c\}$. -/
theorem supportFn_le_coe_iff {c : ℝ} :
    supportFn B s y ≤ (c : EReal) ↔ ∀ x ∈ s, B x y ≤ c := by
  rw [supportFn_le_iff]
  exact forall₂_congr fun _ _ => EReal.coe_le_coe_iff

/-- $\delta^*(y \mid s) \le 0$ if and only if $\langle x, y \rangle \le 0$ for every $x \in s$. This
is the level $0$ of `ConvexAnalysis.supportFn_le_coe_iff`, where a polar cone is cut out. -/
theorem supportFn_le_zero_iff : supportFn B s y ≤ 0 ↔ ∀ x ∈ s, B x y ≤ 0 := by
  rw [← EReal.coe_zero, supportFn_le_coe_iff]

/-- $0 < \delta^*(y \mid s)$ if and only if $\langle x, y \rangle > 0$ for some $x \in s$. -/
theorem zero_lt_supportFn_iff : 0 < supportFn B s y ↔ ∃ x ∈ s, 0 < B x y := by
  rw [supportFn_apply, ← EReal.coe_zero]
  simp only [lt_iSup_iff, exists_prop, EReal.coe_lt_coe_iff]

/-- The support function is monotone in the set: if $s \subseteq t$, then $\delta^*(\cdot \mid s)
\le \delta^*(\cdot \mid t)$. -/
theorem supportFn_mono (h : s ⊆ t) : supportFn B s ≤ supportFn B t :=
  fun _ => iSup₂_le fun _ hx => le_supportFn (h hx) _

/-- The support function of the empty set is the constant $-\infty$. -/
@[simp] theorem supportFn_empty (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    supportFn B (∅ : Set E) = fun _ => (⊥ : EReal) := by
  funext y; simp [supportFn]

/-- The support function of a single point $x \in E$ is the linear function
$y \mapsto \langle x, y \rangle$:
$$\delta^*(y \mid \{x\}) = \langle x, y \rangle.$$
-/
@[simp] theorem supportFn_singleton (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : E) :
    supportFn B {x} = fun y => ((B x y : ℝ) : EReal) := by
  funext y; simp [supportFn]

/-- The support function of a union is the pointwise maximum of the support functions: for all
$s, t \subseteq E$,
$$\delta^*(\cdot \mid s \cup t) = \max\{\delta^*(\cdot \mid s), \delta^*(\cdot \mid t)\}.$$
-/
theorem supportFn_union (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s t : Set E) :
    supportFn B (s ∪ t) = supportFn B s ⊔ supportFn B t := by
  funext y
  rw [Pi.sup_apply, supportFn_apply, supportFn_apply, supportFn_apply, iSup_union]

/-- The support function of the union of a family $(u_i)$ of sets is the pointwise supremum of the
support functions: $\delta^*(y \mid \bigcup_i u_i) = \sup_i \delta^*(y \mid u_i)$. -/
theorem supportFn_iUnion {ι : Sort*} (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (u : ι → Set E) :
    supportFn B (⋃ i, u i) = fun y => ⨆ i, supportFn B (u i) y := by
  funext y
  rw [supportFn_apply, iSup_iUnion]
  rfl

/-- The support function of a nonempty set never takes the value $-\infty$. -/
theorem supportFn_ne_bot (hs : s.Nonempty) (y : F) : supportFn B s y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hs
  exact fun hc => absurd (hc ▸ le_supportFn (B := B) hx y) (by simp)

/-- The support function of a nonempty set vanishes at the origin: $\delta^*(0 \mid s) = 0$. -/
@[simp] theorem supportFn_zero (hs : s.Nonempty) : supportFn B s 0 = 0 := by
  obtain ⟨x, hx⟩ := hs
  refine le_antisymm (iSup₂_le fun z _ => ?_) ?_
  · rw [map_zero]; rfl
  · have h := le_supportFn (B := B) hx (0 : F)
    rwa [map_zero, EReal.coe_zero] at h

/-- The support function of a nonempty set is a proper convex function: it takes a value below
$+\infty$ somewhere and never takes the value $-\infty$. -/
theorem properConvex_supportFn (hs : s.Nonempty) : ProperConvex (supportFn B s) :=
  ⟨⟨0, by rw [mem_convexDom, supportFn_zero hs]; exact lt_top_iff_ne_top.2 (by simp)⟩,
    supportFn_ne_bot hs⟩

/-- **The effective domain of a support function is the barrier cone** of $s$: the set of $y \in F$
for which $\langle \cdot, y \rangle$ is bounded above on $s$,
$$\operatorname{dom} \delta^*(\cdot \mid s) = \{y \in F \mid \exists c \in \mathbb{R},\ \langle
  x, y \rangle \le c \text{ for all } x \in s\}.$$
-/
theorem convexDom_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    convexDom (supportFn B s) = {y : F | ∃ c : ℝ, ∀ x ∈ s, B x y ≤ c} := by
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨c, hc, -⟩ := EReal.lt_iff_exists_real_btwn.1 (hy : supportFn B s y < ⊤)
    exact ⟨c, supportFn_le_coe_iff.1 hc.le⟩
  · obtain ⟨c, hc⟩ := hy
    exact lt_of_le_of_lt (supportFn_le_coe_iff.2 hc) (EReal.coe_lt_top c)

/-- $\delta^*(y \mid s) < +\infty$ if and only if $\langle \cdot, y \rangle$ is bounded above on
$s$. -/
theorem supportFn_lt_top_iff : supportFn B s y < ⊤ ↔ ∃ c : ℝ, ∀ x ∈ s, B x y ≤ c := by
  rw [← mem_convexDom, convexDom_supportFn]
  exact Iff.rfl

/-!
### Convexity and positive homogeneity

Both properties are inherited: convexity from the conjugate, and positive homogeneity by reindexing
the supremum.
-/

/-- **The support function of any set is convex**, since it is a conjugate. -/
theorem convexFn_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) : ConvexFn (supportFn B s) := by
  rw [supportFn_eq_convexConj_indicatorFn]; exact convexFn_convexConj B _

/-- **The support function of any set is positively homogeneous**:
$\delta^*(ay \mid s) = a\, \delta^*(y \mid s)$ for every $a > 0$ and $y \in F$. -/
theorem posHomogeneous_supportFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    PosHomogeneous (supportFn B s) := by
  intro a ha y
  simp only [supportFn]
  rw [EReal.coe_mul_iSup ha]
  refine iSup_congr fun x => ?_
  rw [EReal.coe_mul_iSup ha]
  refine iSup_congr fun _ => ?_
  rw [map_smul, smul_eq_mul, EReal.coe_mul]

/-- **Support functions are subadditive.** For a nonempty set $s$ and all $y_1, y_2 \in F$,
$$\delta^*(y_1 + y_2 \mid s) \le \delta^*(y_1 \mid s) + \delta^*(y_2 \mid s).$$
This holds because a positively homogeneous convex function is subadditive. -/
theorem supportFn_add_le (hs : s.Nonempty) (y₁ y₂ : F) :
    supportFn B s (y₁ + y₂) ≤ supportFn B s y₁ + supportFn B s y₂ :=
  ((posHomogeneous_supportFn B s).convexFn_iff_subadditive (supportFn_ne_bot hs)).1
    (convexFn_supportFn B s) y₁ y₂

/-- **A closed half-space of the pairing is convex**, in the form with an extended-real bound: for
$y \in F$ and $M \in [-\infty, +\infty]$, the set $\{x \in E \mid \langle x, y \rangle \le M\}$
is convex. -/
theorem convex_setOf_pairing_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (y : F) (M : EReal) :
    Convex ℝ {x : E | ((B x y : ℝ) : EReal) ≤ M} := by
  have h := (convexFn_affineFn (B := B) y 0).convex_le M
  simpa only [affineFn_apply, EReal.coe_zero, sub_zero] using h

/-- **The support function does not change under the convex hull.** For every set $s \subseteq E$,
$$\delta^*(\cdot \mid \operatorname{conv} s) = \delta^*(\cdot \mid s).$$
-/
theorem supportFn_convexHull (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Set E) :
    supportFn B (convexHull ℝ s) = supportFn B s := by
  funext y
  refine le_antisymm (iSup₂_le fun x hx => ?_) (supportFn_mono (subset_convexHull ℝ s) y)
  exact convexHull_min (fun z hz => le_supportFn hz y)
    (convex_setOf_pairing_le B y (supportFn B s y)) hx

/-- **The support function of a positive multiple of a set.** Let $a > 0$ and $s \subseteq E$. Then
for every $y \in F$,
$$\delta^*(y \mid as) = a\, \delta^*(y \mid s).$$
-/
theorem supportFn_smul (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) {a : ℝ} (ha : 0 < a) (s : Set E) (y : F) :
    supportFn B (a • s) y = (a : EReal) * supportFn B s y := by
  rw [supportFn_apply, supportFn_apply, EReal.coe_mul_iSup ha, ← Set.image_smul, iSup_image]
  refine iSup_congr fun z => ?_
  rw [EReal.coe_mul_iSup ha]
  refine iSup_congr fun _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, EReal.coe_mul]

/-- **The support function of a sum of sets is the sum of the support functions.** For all
$s, t \subseteq E$,
$$\delta^*(\cdot \mid s + t) = \delta^*(\cdot \mid s) + \delta^*(\cdot \mid t),$$
with the extended-real addition in which $-\infty + (+\infty) = -\infty$.

There is no hypothesis, unlike the corresponding statement for a sum of functions. A support
function takes the value $-\infty$ only on the empty set, so a sum $-\infty + (+\infty)$ arises
only when $s$ or $t$ is empty. Then $s + t$ is empty, and both sides are $-\infty$. -/
theorem supportFn_add (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s t : Set E) :
    supportFn B (s + t) = supportFn B s + supportFn B t := by
  funext y
  calc supportFn B (s + t) y
      = ⨆ a ∈ s, ⨆ b ∈ t, ((B (a + b) y : ℝ) : EReal) := by
        rw [supportFn_apply, ← Set.image2_add, iSup_image2]
    _ = ⨆ a ∈ s, ⨆ b ∈ t, (((B b y : ℝ) : EReal) + ((B a y : ℝ) : EReal)) := by
        refine iSup_congr fun a => iSup_congr fun _ => iSup_congr fun b => iSup_congr fun _ => ?_
        rw [map_add, LinearMap.add_apply, ← EReal.coe_add, add_comm]
    _ = ⨆ a ∈ s, (((B a y : ℝ) : EReal) + supportFn B t y) := by
        refine iSup_congr fun a => iSup_congr fun _ => ?_
        rw [supportFn_apply, ← EReal.biSup_add_coe, add_comm]
    _ = supportFn B s y + supportFn B t y := by
        rw [← EReal.biSup_add_of_ne_bot (u := fun a => ((B a y : ℝ) : EReal))
          fun a _ => EReal.coe_ne_bot _]
        rfl

end Defs

/-!
### Conjugates of positively homogeneous functions

This is the mechanism behind the rest of the module, and it needs no topology. Reindexing the
supremum that defines $f^*$ along $x \mapsto ax$ shows that $f^*(y)$ is fixed by every positive
scalar.
-/

section PosHom

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal}

/-- The set $\{y \in F \mid \langle x, y \rangle \le f(x) \text{ for all } x \in E\}$ for a function
$f : E \to [-\infty, +\infty]$.

When $f$ is closed, proper, convex and positively homogeneous, this is the set whose support
function is $f$ (`ConvexAnalysis.supportFn_supportSet`). In general it is the set where
$f^* \le 0$, and it is the set that $f^*$ indicates when $f$ is positively homogeneous and not
identically $+\infty$. -/
def supportSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : Set F :=
  {y | ∀ x, ((B x y : ℝ) : EReal) ≤ f x}

/-- A point $y$ lies in the support set of $f$ if and only if $\langle x, y \rangle \le f(x)$ for
every $x \in E$. -/
@[simp] theorem mem_supportSet {y : F} :
    y ∈ supportSet B f ↔ ∀ x, ((B x y : ℝ) : EReal) ≤ f x := Iff.rfl

/-- The support set of $f$ is the zero sublevel set of the conjugate: $\{y \mid \langle x, y \rangle
\le f(x) \ \forall x\} = \{y \mid f^*(y) \le 0\}$. -/
theorem supportSet_eq_setOf_convexConj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    supportSet B f = {y | convexConj B f y ≤ 0} := by
  ext y
  change (∀ x, ((B x y : ℝ) : EReal) ≤ f x) ↔ convexConj B f y ≤ 0
  rw [show ((0 : EReal)) = ((0 : ℝ) : EReal) from EReal.coe_zero.symm, convexConj_le_coe_iff,
    Pi.le_def]
  exact forall_congr' fun x => by rw [affineFn_apply, EReal.coe_zero, sub_zero]

/-- The support set of every function $f : E \to [-\infty, +\infty]$ is convex. -/
theorem convex_supportSet (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : Convex ℝ (supportSet B f) := by
  rw [supportSet_eq_setOf_convexConj_le]
  exact (convexFn_convexConj B f).convex_le 0

/-- **The conjugate of a positively homogeneous function is fixed by every positive scalar.** If
$f(ax) = a f(x)$ for all $a > 0$ and $x$, then $f^*(y) = a f^*(y)$ for every $a > 0$ and
$y \in F$.

This is the substance of the relation between positive homogeneity of $f$ and of $f^*$. The
proof reindexes the supremum that defines $f^*$. -/
theorem convexConj_smul_eq_self (hf : PosHomogeneous f) {a : ℝ} (ha : 0 < a) (y : F) :
    convexConj B f y = (a : EReal) * convexConj B f y := by
  by_cases hb : ∃ x, f x = ⊥
  · obtain ⟨x₀, hx₀⟩ := hb
    rw [convexConj_of_eq_bot hx₀]
    exact (EReal.coe_mul_top_of_pos ha).symm
  push Not at hb
  have hterm : ∀ x : E, ((B (a • x) y : ℝ) : EReal) - f (a • x)
      = (a : EReal) * (((B x y : ℝ) : EReal) - f x) := by
    intro x
    rw [hf a ha x, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rcases eq_or_ne (f x) ⊤ with h | h
    · rw [h, EReal.coe_mul_top_of_pos ha, EReal.sub_top, EReal.sub_top,
        EReal.coe_mul_bot_of_pos ha]
    · obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hb x) (lt_top_iff_ne_top.2 h)
      rw [hr, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_sub,
        ← EReal.coe_mul]
      congr 1
      ring
  have hsurj : Function.Surjective fun x : E => a • x := fun z =>
    ⟨a⁻¹ • z, smul_inv_smul₀ ha.ne' z⟩
  have hre : (⨆ x : E, (((B (a • x) y : ℝ) : EReal) - f (a • x))) = convexConj B f y :=
    hsurj.iSup_comp fun z => ((B z y : ℝ) : EReal) - f z
  calc convexConj B f y = ⨆ x : E, (((B (a • x) y : ℝ) : EReal) - f (a • x)) := hre.symm
    _ = ⨆ x : E, (a : EReal) * (((B x y : ℝ) : EReal) - f x) := iSup_congr hterm
    _ = (a : EReal) * convexConj B f y := (EReal.coe_mul_iSup ha _).symm

/-- **The conjugate of a positively homogeneous function is an indicator function.** Let
$f : E \to [-\infty, +\infty]$ be positively homogeneous, and let $f(x) \neq +\infty$ for some
$x$. Then
$$f^* = \delta(\cdot \mid S), \qquad S = \{y \in F \mid \langle x, y \rangle \le f(x) \text{ for
  all } x \in E\}.$$

With `ConvexAnalysis.supportFn_eq_convexConj_indicatorFn`, this is the duality between positive
homogeneity and indicator functions on which gauges and polarity rest. The hypothesis that $f$
is not identically $+\infty$ is necessary: the conjugate of the constant $+\infty$ is the
constant $-\infty$, which is not an indicator function. -/
theorem convexConj_eq_indicatorFn_of_posHomogeneous (hf : PosHomogeneous f) (hne : ∃ x, f x ≠ ⊤) :
    convexConj B f = indicatorFn (supportSet B f) := by
  funext y
  have hval : convexConj B f y = 0 ∨ convexConj B f y = ⊤ := by
    rcases EReal.eq_zero_or_eq_top_or_eq_bot (a := 2) (by norm_num)
      (convexConj_smul_eq_self hf (by norm_num : (0 : ℝ) < 2) y).symm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨x₀, hx₀⟩ := hne
      exact absurd (convexConj_eq_bot_iff.1 h x₀) hx₀
  have hiff : y ∈ supportSet B f ↔ convexConj B f y ≤ 0 := by
    rw [supportSet_eq_setOf_convexConj_le]; exact Iff.rfl
  by_cases hy : y ∈ supportSet B f
  · rw [indicatorFn_of_mem hy]
    rcases hval with h | h
    · exact h
    · exact absurd (hiff.1 hy) (by rw [h]; simp)
  · rw [indicatorFn_of_notMem hy]
    rcases hval with h | h
    · exact absurd (hiff.2 h.le) hy
    · exact h

end PosHom

/-! ### Closedness of the support function -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B.flip] {s : Set E}

/-- Let $F$ carry a topology for which every functional $\langle x, \cdot \rangle$ is continuous.
Then the support function of every set $s \subseteq E$ is lower semicontinuous on $F$. -/
theorem lowerSemicontinuous_supportFn : LowerSemicontinuous (supportFn B s) := by
  rw [supportFn_eq_convexConj_indicatorFn]; exact lowerSemicontinuous_convexConj

variable [IsTopologicalAddGroup F]

/-- **The support function of any set is a closed convex function.** Let $F$ be a topological
additive group for which every functional $\langle x, \cdot \rangle$ is continuous. Then
$\delta^*(\cdot \mid s)$ is closed for every set $s \subseteq E$, since it is a conjugate. -/
theorem closedConvex_supportFn : ClosedConvex (supportFn B s) := by
  rw [supportFn_eq_convexConj_indicatorFn]; exact closedConvex_convexConj

end Closed

/-! ### The closure of the set -/

section ContinuousPairing

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsContinuousPairing B] {s : Set E}

/-- Let $E$ carry a topology for which every functional $\langle \cdot, y \rangle$ is continuous.
For $y \in F$ and $M \in [-\infty, +\infty]$, the set
$\{x \in E \mid \langle x, y \rangle \le M\}$ is closed. -/
theorem isClosed_setOf_pairing_le (y : F) (M : EReal) :
    IsClosed {x : E | ((B x y : ℝ) : EReal) ≤ M} :=
  isClosed_Iic.preimage (EReal.continuous_coe_iff.2 (continuous_pairing B y))

/-- **The support function does not change under closure.** Let $E$ carry a topology for which every
functional $\langle \cdot, y \rangle$ is continuous. Then for every set $s \subseteq E$,
$$\delta^*(\cdot \mid \operatorname{cl} s) = \delta^*(\cdot \mid s).$$
-/
theorem supportFn_closure (s : Set E) : supportFn B (closure s) = supportFn B s := by
  funext y
  refine le_antisymm (iSup₂_le fun x hx => ?_) (supportFn_mono subset_closure y)
  exact closure_minimal (fun z hz => le_supportFn hz y)
    (isClosed_setOf_pairing_le y (supportFn B s y)) hx

/-- Let $E$ carry a topology for which every functional $\langle \cdot, y \rangle$ is continuous.
For every function $g : F \to [-\infty, +\infty]$, the set $\{x \in E \mid \langle x, y \rangle
\le g(y) \text{ for all } y \in F\}$ is closed. -/
theorem isClosed_supportSet (g : F → EReal) : IsClosed (supportSet B.flip g) := by
  rw [supportSet_eq_setOf_convexConj_le,
    show ((0 : EReal)) = ((0 : ℝ) : EReal) from EReal.coe_zero.symm]
  exact lowerSemicontinuous_iff_isClosed_le.1 (lowerSemicontinuous_convexConj (B := B.flip)) 0

end ContinuousPairing

/-! ### The closed convex hull -/

section ClosedConvexHull

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B]

/-- **Points of the closed convex hull.** Let $E$ be a locally convex real topological vector space,
and let the pairing be compatible with the topology of $E$: every functional
$\langle \cdot, y \rangle$ is continuous, and every continuous linear functional on $E$ has this
form. Then for every set $s \subseteq E$ and every $x \in E$,
$$x \in \operatorname{cl}(\operatorname{conv} s) \iff \langle x, y \rangle \le \delta^*(y \mid
  s) \text{ for every } y \in F.$$

So a point lies in the closed convex hull of $s$ if and only if it satisfies every weak linear
inequality that the support function of $s$ records. This is Theorem 13.1 of
[rockafellar1970convex]. The proof uses strong separation. -/
theorem mem_closure_convexHull_iff_le_supportFn (s : Set E) (x : E) :
    x ∈ closure (convexHull ℝ s) ↔ ∀ y : F, ((B x y : ℝ) : EReal) ≤ supportFn B s y := by
  rw [← closure_convexHull_eq_iInter_halfspaces s]
  simp only [Set.mem_iInter, Set.mem_ofPred]
  constructor
  · intro h y
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨c, hc₁, hc₂⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hbnd : ∀ z ∈ s, evalCLM B y z ≤ c := supportFn_le_coe_iff.1 hc₁.le
    have hx := h (evalCLM B y) c hbnd
    rw [evalCLM_apply] at hx
    exact absurd hc₂ (not_lt.2 (by exact_mod_cast hx))
  · intro h g c hg
    obtain ⟨y, hy⟩ := exists_pairing_eq B g
    have hsup : supportFn B s y ≤ (c : EReal) :=
      supportFn_le_coe_iff.2 fun z hz => hy z ▸ hg z hz
    rw [hy x]
    exact_mod_cast (h y).trans hsup

/-- **Closed convex hulls are ordered by their support functions.** Let $E$ be a locally convex real
topological vector space with a compatible pairing. For all sets $s, t \subseteq E$,
$$\operatorname{cl}(\operatorname{conv} s) \subseteq \operatorname{cl}(\operatorname{conv} t)
  \iff \delta^*(\cdot \mid s) \le \delta^*(\cdot \mid t).$$
-/
theorem closure_convexHull_subset_iff_supportFn_le (s t : Set E) :
    closure (convexHull ℝ s) ⊆ closure (convexHull ℝ t) ↔ supportFn B s ≤ supportFn B t := by
  constructor
  · intro h y
    have h' := supportFn_mono (B := B) h y
    rwa [supportFn_closure, supportFn_convexHull, supportFn_closure,
      supportFn_convexHull] at h'
  · intro h x hx
    rw [mem_closure_convexHull_iff_le_supportFn (B := B)] at hx ⊢
    exact fun y => (hx y).trans (h y)

end ClosedConvexHull

/-!
### The closure of a positively homogeneous convex function

Here only the space $F$ carries a topology: the results are the biconjugation theorem
`ConvexAnalysis.convexBiconj_eq_convexCl` for the flipped pairing.
-/

section PosHomClosure

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B.flip] {g : F → EReal}

/-- **The closure of a positively homogeneous convex function is a support function.** Let $F$ be a
locally convex real topological vector space, and let the flipped pairing be compatible with the
topology of $F$: every functional $\langle x, \cdot \rangle$ is continuous, and every continuous
linear functional on $F$ has this form. Let $g : F \to [-\infty, +\infty]$ be positively
homogeneous and convex, with $g(y) \neq +\infty$ for some $y$. Then the closure of $g$ is the
support function of the set
$$S = \{x \in E \mid \langle x, y \rangle \le g(y) \text{ for all } y \in F\}:$$
$$\operatorname{cl} g = \delta^*(\cdot \mid S).$$

The improper case is included: if $g$ takes the value $-\infty$, then $S$ is empty and both
sides are the constant $-\infty$. -/
theorem convexCl_eq_supportFn_of_posHomogeneous
    (hg : PosHomogeneous g) (hconv : ConvexFn g) (hne : ∃ y, g y ≠ ⊤) :
    convexCl g = supportFn B (supportSet B.flip g) := by
  rw [supportFn_eq_convexConj_indicatorFn,
    ← convexConj_eq_indicatorFn_of_posHomogeneous (B := B.flip) hg hne]
  exact (convexBiconj_eq_convexCl (B := B.flip) hconv).symm

omit [LocallyConvexSpace ℝ F] in
/-- **The closure of a positively homogeneous function supports the same set.** Let $F$ be a real
topological vector space, and let the flipped pairing be compatible with the topology of $F$.
Let $g : F \to [-\infty, +\infty]$ be positively homogeneous, with $g(y) \neq +\infty$ for some
$y$. Then
$$\{x \in E \mid \langle x, y \rangle \le (\operatorname{cl} g)(y) \ \forall y\} = \{x \in E
  \mid \langle x, y \rangle \le g(y) \ \forall y\}.$$

Neither convexity of $g$ nor local convexity of $F$ is needed. The proof notes that the
conjugates of $g$ and of $\operatorname{cl} g$ agree and are both indicator functions, so the
two sets that they indicate agree. -/
theorem supportSet_convexCl (hg : PosHomogeneous g) (hne : ∃ y, g y ≠ ⊤) :
    supportSet B.flip (convexCl g) = supportSet B.flip g := by
  obtain ⟨w, hw⟩ := hne
  have hne' : ∃ y, convexCl g y ≠ ⊤ := ⟨w, fun h => hw (top_le_iff.1 (h ▸ convexCl_le g w))⟩
  have h₁ := convexConj_eq_indicatorFn_of_posHomogeneous (B := B.flip) hg ⟨w, hw⟩
  have h₂ :=
      convexConj_eq_indicatorFn_of_posHomogeneous (B := B.flip) (posHomogeneous_convexCl hg) hne'
  rw [convexConj_convexCl, h₁] at h₂
  rw [← convexDom_indicatorFn (supportSet B.flip (convexCl g)), ← h₂, convexDom_indicatorFn]

/-- **A closed positively homogeneous convex function is a support function.** Let $F$ be a locally
convex real topological vector space with a compatible flipped pairing. Let
$g : F \to [-\infty, +\infty]$ be positively homogeneous, convex and closed, with
$g(y) \neq +\infty$ for some $y$. Then $g$ is the support function of $\{x \in E \mid \langle x,
y \rangle \le g(y) \text{ for all } y \in F\}$. -/
theorem supportFn_supportSet (hg : PosHomogeneous g) (hconv : ConvexFn g) (hcl : ClosedConvex g)
    (hne : ∃ y, g y ≠ ⊤) : supportFn B (supportSet B.flip g) = g :=
  (convexCl_eq_supportFn_of_posHomogeneous hg hconv hne).symm.trans hcl

/-- Let $F$ be a locally convex real topological vector space with a compatible flipped pairing, and
let $g : F \to [-\infty, +\infty]$ be a positively homogeneous closed proper convex function.
Then the set $\{x \in E \mid \langle x, y \rangle \le g(y) \text{ for all } y \in F\}$ is
nonempty. -/
theorem nonempty_supportSet (hg : PosHomogeneous g) (hcpc : ClosedProperConvexFn g) :
    (supportSet B.flip g).Nonempty := by
  obtain ⟨y₀, hy₀⟩ := hcpc.proper.convexDom_nonempty
  have hg' := supportFn_supportSet (B := B) hg hcpc.convex hcpc.closed ⟨y₀, hy₀.ne⟩
  rcases (supportSet B.flip g).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, supportFn_empty] at hg'
    exact absurd (congrFun hg' y₀).symm (hcpc.proper.ne_bot y₀)
  · exact hne

end PosHomClosure

/-!
### Sets and their support functions, in bijection

Both spaces carry topologies that are compatible with the pairing, as for the conjugacy
correspondence `ConvexAnalysis.convexConjEquiv`.
-/

section SupportCorrespondence

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Set E} {g : F → EReal}

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- **The indicator function and the support function of a closed convex set are conjugate.** Let
$E$ be a locally convex real topological vector space, and let the pairing be compatible with
the topology of $E$. Let $s \subseteq E$ be closed and convex. Then the conjugate of
$\delta^*(\cdot \mid s)$ with respect to the flipped pairing is the indicator function of $s$:
$$\bigl(\delta^*(\cdot \mid s)\bigr)^* = \delta(\cdot \mid s).$$
This is part of Theorem 13.2 of [rockafellar1970convex].

The conjugacy in the other direction holds for every set and is
`ConvexAnalysis.supportFn_eq_convexConj_indicatorFn`. -/
theorem convexConj_supportFn [IsCompatiblePairing B] (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    convexConj B.flip (supportFn B s) = indicatorFn s := by
  rw [supportFn_eq_convexConj_indicatorFn]
  change convexBiconj B (indicatorFn s) = indicatorFn s
  rw [convexBiconj_eq_convexCl (convexFn_indicatorFn.2 hs₁), convexCl_indicatorFn, hs₂.closure_eq]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- Let $E$ be a locally convex real topological vector space with a compatible pairing, and let
$s \subseteq E$ be convex. Then the conjugate of $\delta^*(\cdot \mid s)$ with respect to the
flipped pairing is the indicator function of the closure of $s$:
$$\bigl(\delta^*(\cdot \mid s)\bigr)^* = \delta(\cdot \mid \operatorname{cl} s).$$

This form is used to conclude that a set is closed, since the effective domain of the left side
is $\operatorname{cl} s$. -/
theorem convexConj_supportFn_of_convex [IsCompatiblePairing B] (hs₁ : Convex ℝ s) :
    convexConj B.flip (supportFn B s) = indicatorFn (closure s) := by
  rw [supportFn_eq_convexConj_indicatorFn]
  change convexBiconj B (indicatorFn s) = indicatorFn (closure s)
  rw [convexBiconj_eq_convexCl (convexFn_indicatorFn.2 hs₁), convexCl_indicatorFn]

omit [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- **A closed convex set is recovered from its support function.** Let $E$ be a locally convex real
topological vector space with a compatible pairing, and let $s \subseteq E$ be closed and
convex. Then
$$\{x \in E \mid \langle x, y \rangle \le \delta^*(y \mid s) \text{ for all } y \in F\} = s.$$
-/
theorem supportSet_supportFn [IsCompatiblePairing B] (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) :
    supportSet B.flip (supportFn B s) = s := by
  ext x
  simp only [mem_supportSet, LinearMap.flip_apply]
  rw [← mem_closure_convexHull_iff_le_supportFn, hs₁.convexHull_eq, hs₂.closure_eq]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- **Characterization of support functions.** Let $E$ carry a topology for which every functional
$\langle \cdot, y \rangle$ is continuous. Let $F$ be a locally convex real topological vector
space, and let the flipped pairing be compatible with the topology of $F$. For a function
$g : F \to [-\infty, +\infty]$, the following are equivalent:
* $g = \delta^*(\cdot \mid C)$ for some nonempty closed convex set $C \subseteq E$;
* $g$ is a closed proper convex function and is positively homogeneous.

This is part of Theorem 13.2 of [rockafellar1970convex]. The statement uses nonempty closed
convex sets. Nonempty convex sets give the same functions, since the support function changes
neither under closure nor under the convex hull, and with closed convex sets the correspondence
is one-to-one (`ConvexAnalysis.supportEquiv`). -/
theorem exists_supportFn_iff [IsContinuousPairing B] [IsCompatiblePairing B.flip] :
    (∃ C : Set E, C.Nonempty ∧ Convex ℝ C ∧ IsClosed C ∧ g = supportFn B C) ↔
      (ClosedProperConvexFn g ∧ PosHomogeneous g) := by
  constructor
  · rintro ⟨C, hne, -, -, rfl⟩
    exact ⟨⟨convexFn_supportFn B C, closedConvex_supportFn, properConvex_supportFn hne⟩,
      posHomogeneous_supportFn B C⟩
  · rintro ⟨hcpc, hph⟩
    obtain ⟨y₀, hy₀⟩ := hcpc.proper.convexDom_nonempty
    have hg : supportFn B (supportSet B.flip g) = g :=
      supportFn_supportSet hph hcpc.convex hcpc.closed ⟨y₀, hy₀.ne⟩
    exact ⟨supportSet B.flip g, nonempty_supportSet hph hcpc,
      convex_supportSet B.flip g, isClosed_supportSet g, hg.symm⟩

/-- **The support function correspondence as a bijection.** Let $E$ and $F$ be locally convex real
topological vector spaces, and let the pairing and the flipped pairing be compatible with their
topologies. Then $C \mapsto \delta^*(\cdot \mid C)$ is a bijection from the nonempty closed
convex subsets of $E$ onto the closed proper positively homogeneous convex functions on $F$. The
inverse sends $g$ to $\{x \in E \mid \langle x, y \rangle \le g(y) \text{ for all } y \in F\}$.

This is the restriction of the conjugacy correspondence `ConvexAnalysis.convexConjEquiv` along
the embedding $C \mapsto \delta(\cdot \mid C)$ of sets into functions and to the positively
homogeneous functions. -/
noncomputable def supportEquiv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [IsCompatiblePairing B]
    [IsCompatiblePairing B.flip] :
    {C : Set E // C.Nonempty ∧ Convex ℝ C ∧ IsClosed C} ≃
      {g : F → EReal // ClosedProperConvexFn g ∧ PosHomogeneous g} where
  toFun C := ⟨supportFn B C.1, ⟨convexFn_supportFn B C.1, closedConvex_supportFn,
    properConvex_supportFn C.2.1⟩, posHomogeneous_supportFn B C.1⟩
  invFun g := ⟨supportSet B.flip g.1, nonempty_supportSet g.2.2 g.2.1,
    convex_supportSet B.flip g.1, isClosed_supportSet g.1⟩
  left_inv C := Subtype.ext (supportSet_supportFn C.2.2.1 C.2.2.2)
  right_inv g := Subtype.ext <| by
    obtain ⟨y₀, hy₀⟩ := g.2.1.proper.convexDom_nonempty
    exact supportFn_supportSet g.2.2 g.2.1.convex g.2.1.closed ⟨y₀, hy₀.ne⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- **Characterization of finite support functions.** Let $E$ carry a topology for which every
functional $\langle \cdot, y \rangle$ is continuous. Let $F$ be a locally convex real
topological vector space, and let the flipped pairing be compatible with the topology of $F$.
For a function $g : F \to [-\infty, +\infty]$, the following are equivalent:
* $g = \delta^*(\cdot \mid C)$ for some nonempty set $C \subseteq E$ on which every functional
  $\langle \cdot, y \rangle$ is bounded above;
* $g$ takes only finite values, and is convex, closed and positively homogeneous.

This is the finite form of Theorem 13.2 of [rockafellar1970convex]. The classical statement has
no closedness hypothesis. Closedness is needed outside finite dimensions, where a discontinuous
linear functional is finite, convex and positively homogeneous but not closed. -/
theorem exists_supportFn_finite_iff [IsContinuousPairing B] [IsCompatiblePairing B.flip] :
    (∃ C : Set E, C.Nonempty ∧ (∀ y : F, ∃ c : ℝ, ∀ x ∈ C, B x y ≤ c) ∧ g = supportFn B C) ↔
      ((∀ y, g y ≠ ⊥) ∧ (∀ y, g y ≠ ⊤) ∧ ConvexFn g ∧ ClosedConvex g ∧ PosHomogeneous g) := by
  constructor
  · rintro ⟨C, hne, hbdd, rfl⟩
    exact ⟨supportFn_ne_bot hne, fun y => (supportFn_lt_top_iff.2 (hbdd y)).ne,
      convexFn_supportFn B C, closedConvex_supportFn, posHomogeneous_supportFn B C⟩
  · rintro ⟨hb, ht, hconv, hcl, hph⟩
    have hp : ProperConvex g := ⟨⟨0, lt_top_iff_ne_top.2 (ht 0)⟩, hb⟩
    obtain ⟨C, hne, -, -, hg⟩ :=
      (exists_supportFn_iff (B := B)).2 ⟨⟨hconv, hcl, hp⟩, hph⟩
    refine ⟨C, hne, fun y => supportFn_lt_top_iff.1 ?_, hg⟩
    rw [← hg]
    exact lt_top_iff_ne_top.2 (ht y)

end SupportCorrespondence

end ConvexAnalysis
