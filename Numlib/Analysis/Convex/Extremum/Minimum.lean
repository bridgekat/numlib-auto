/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Polyhedral.Function
import Numlib.Analysis.Convex.Polyhedral.Recession
import Numlib.Analysis.Convex.Recession.Closedness
import Numlib.Analysis.Convex.Recession.Conjugate
import Numlib.Analysis.Convex.Subdifferential.Approx
import Numlib.Analysis.Convex.Subdifferential.Calculus
import Numlib.Analysis.Convex.Subdifferential.Existence
import Numlib.Analysis.Convex.Subdifferential.Uniqueness

/-!
# The minimum of a convex function

Let $f$ be a function on a real vector space $E$ with values in $[-\infty, +\infty]$, and let $E$ be
paired with $F$ by $\langle x, y \rangle$. The **minimum set** of $f$ is
$\{x \mid f(x) \le f(z) \text{ for all } z\}$. A point $x$ minimizes $f$ exactly when
$0 \in \partial f(x)$: this is the subgradient inequality at $y = 0$, and it is why subgradients are
the main tool here. Dually, $\inf f = -f^*(0)$ with no hypothesis on $f$. For a closed proper convex
$f$ the minimum set is $\partial f^*(0)$, so every question about minimizers becomes a question
about the conjugate near the origin. The presentation follows §27 of [rockafellar1970convex].

Existence comes from recession. In finite dimension, a closed proper convex function with no
direction of recession has compact level sets and attains its infimum. This extends to minimization
over a closed convex set, with a weaker hypothesis when the set is polyhedral.

## Main definitions

* `ConvexAnalysis.argmin`: the minimum set $\{x \mid f(x) \le f(z) \text{ for all } z\}$.
* `ConvexAnalysis.argmax`: the maximum set $\{x \mid g(z) \le g(x) \text{ for all } z\}$.

## Main results

* `ConvexAnalysis.mem_argmin_iff_zero_mem_subdifferential`: $x$ minimizes $f$ exactly when
  $0 \in \partial f(x)$.
* `ConvexAnalysis.convexConj_apply_zero` (in `Numlib.Analysis.Convex.Duality.Level`),
  `ConvexAnalysis.argmin_eq_subdifferential_convexConj_zero`,
  `ConvexAnalysis.iInf_ne_bot_and_argmin_eq_empty_iff`,
  `ConvexAnalysis.argmin_nonempty_and_isBounded_iff_zero_mem_interior_convexDom_convexConj`,
  `ConvexAnalysis.supportFn_setOf_le`,
  `ConvexAnalysis.argmin_eq_singleton_iff_hasGradientAtFn_convexConj_zero`,
  `ConvexAnalysis.supportFn_argmin`,
  `ConvexAnalysis.recessionCone_setOf_le_eq_polarCone_convexDom_convexConj`,
  `ConvexAnalysis.iInf_supportFn_setOf_le`: the minimum set and the optimal value in terms of the
  conjugate at the origin. These are clauses (a)–(h) of Theorem 27.1 of [rockafellar1970convex].
* `ConvexAnalysis.isCompact_setOf_le`: a nonempty level set of a closed proper convex function with
  no direction of recession is compact.
* `ConvexAnalysis.argmin_nonempty_of_recessionConeFn_eq_zero`,
  `ConvexAnalysis.isCompact_argmin_of_recessionConeFn_eq_zero`,
  `ConvexAnalysis.exists_pos_forall_exists_mem_argmin_dist_lt`: the existence of a minimizer, and
  well-posedness of the minimum. This is Theorem 27.2 of [rockafellar1970convex].
* `ConvexAnalysis.tendsto_infDist_argmin`, `ConvexAnalysis.tendsto_of_argmin_eq_singleton`: the
  behaviour of minimizing nets.
* `ConvexAnalysis.exists_forall_le_of_recessionConeFn_inter_eq_zero`,
  `ConvexAnalysis.exists_forall_le_of_inter_subset_constancySpace_inter_linealitySpace`,
  `ConvexAnalysis.exists_forall_le_of_polyhedral_of_inter_subset_constancySpace`: attainment of the
  infimum over a closed convex set, in a basic, a general and a polyhedral form. This is Theorem
  27.3 of [rockafellar1970convex].
* `ConvexAnalysis.argmin_nonempty_of_polyhedralFn`: a polyhedral convex function that is bounded
  below attains its infimum.
* `ConvexAnalysis.le_of_mem_subdifferential_of_neg_mem_normalCone`,
  `ConvexAnalysis.exists_mem_subdifferential_neg_mem_normalCone`: the optimality condition for
  minimization over a convex set, sufficiency and necessity.
* `ConvexAnalysis.argmin_sepSum`, `ConvexAnalysis.convexDom_sepSum`: a **separable** objective
  $x \mapsto \sum_i h_i(x_i)$ on a finite product is minimized coordinatewise. This is the
  *decomposition principle*.

## Implementation notes

* The minimum set is defined as $\{x \mid f(x) \le f(z) \text{ for all } z\}$ and not as
  `IsMinOn f Set.univ`, because this form unfolds to the subgradient inequality at $y = 0$.
  `ConvexAnalysis.mem_argmin_iff_isMinOn` relates it to Mathlib.
* The necessity of the optimality condition is stated with the hypothesis
  `ConvexAnalysis.IsExactSum B h (indicatorFn C)`. Both hypotheses of the source give this
  exactness.
* The results on minimizing sequences are stated for an arbitrary filter, where the source uses
  sequences. The exception is `ConvexAnalysis.isBounded_range_of_tendsto_iInf`, whose conclusion is
  about the range of a sequence.
* The two level-set formulas of clause (i) of Theorem 27.1 of [rockafellar1970convex] are in
  `Numlib.Analysis.Convex.Duality.Level`.
-/

open Set Pointwise

namespace ConvexAnalysis

/-! ### The minimum set -/

section Defs

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {x : E}

/-- Let $f$ be a function on $E$ with values in $[-\infty, +\infty]$. The **minimum set** of $f$ is
the set of points where $f$ attains its infimum:
$$\operatorname{argmin} f = \{x \mid f(x) \le f(z) \text{ for all } z\}.$$

This is the set $\operatorname{lev}_{\inf f} f$ of [rockafellar1970convex]. If the infimum is
not attained, the set is empty. -/
def argmin (f : E → EReal) : Set E := {x | ∀ z, f x ≤ f z}

omit [AddCommGroup E] [Module ℝ E] in
/-- A point $x$ is in the minimum set of $f$ if and only if $f(x) \le f(z)$ for all $z$. -/
theorem mem_argmin_iff : x ∈ argmin f ↔ ∀ z, f x ≤ f z := Iff.rfl

omit [AddCommGroup E] [Module ℝ E] in
/-- A point $x$ is in the minimum set of $f$ if and only if $f$ attains its minimum over the whole
space at $x$, in the sense of Mathlib's `IsMinOn`. -/
theorem mem_argmin_iff_isMinOn : x ∈ argmin f ↔ IsMinOn f Set.univ x := by
  rw [isMinOn_univ_iff]
  exact Iff.rfl

omit [AddCommGroup E] [Module ℝ E] in
/-- A point $x$ is in the minimum set of $f$ if and only if $f(x) \le \inf_z f(z)$. -/
theorem mem_argmin_iff_le_iInf : x ∈ argmin f ↔ f x ≤ ⨅ z, f z := le_iInf_iff.symm

omit [AddCommGroup E] [Module ℝ E] in
/-- If $a$ is in the minimum set of $f$, then $\inf_z f(z) = f(a)$. -/
theorem iInf_eq_of_mem_argmin {a : E} (ha : a ∈ argmin f) : (⨅ z, f z) = f a :=
  le_antisymm (iInf_le _ _) (mem_argmin_iff_le_iInf.1 ha)

omit [AddCommGroup E] [Module ℝ E] in
/-- A point $x$ is in the minimum set of $f$ if and only if $f(x) = \inf_z f(z)$.

This is the form to use when an optimal value is identified with an infimum, such as
$(\inf F)(0)$. -/
theorem mem_argmin_iff_eq_iInf : x ∈ argmin f ↔ f x = ⨅ z, f z :=
  ⟨fun h => (iInf_eq_of_mem_argmin h).symm, fun h => mem_argmin_iff_le_iInf.2 h.le⟩

omit [AddCommGroup E] [Module ℝ E] in
/-- If $a$ is in the minimum set of $f$ and $f(a) = \mu$ is a real number, then the minimum set is
the level set
$$\operatorname{argmin} f = \{z \mid f(z) \le \mu\}.$$
This is the notation $\operatorname{lev}_{\inf f} f$ of [rockafellar1970convex]. -/
theorem argmin_eq_setOf_le {a : E} (ha : a ∈ argmin f) {μ : ℝ} (hμ : f a = (μ : EReal)) :
    argmin f = {z : E | f z ≤ (μ : EReal)} := by
  ext z
  constructor
  · intro hz
    rw [← hμ]
    exact hz a
  · intro hz w
    rw [Set.mem_ofPred_eq, ← hμ] at hz
    exact le_trans hz (ha w)

/-- Let $g$ be a function on $E$ with values in $[-\infty, +\infty]$. The **maximum set** of $g$ is
the set of points where $g$ attains its supremum:
$$\operatorname{argmax} g = \{x \mid g(z) \le g(x) \text{ for all } z\}.$$

This is the counterpart of `ConvexAnalysis.argmin` for concave functions. It is the set of
optimal solutions of a concave program. -/
def argmax (g : E → EReal) : Set E := {x | ∀ z, g z ≤ g x}

omit [AddCommGroup E] [Module ℝ E] in
/-- A point $x$ is in the maximum set of $g$ if and only if $g(z) \le g(x)$ for all $z$. -/
theorem mem_argmax_iff {g : E → EReal} : x ∈ argmax g ↔ ∀ z, g z ≤ g x := Iff.rfl

omit [AddCommGroup E] [Module ℝ E] in
/-- A point $x$ is in the maximum set of $g$ if and only if $g(x) = \sup_z g(z)$.

This is the counterpart of `ConvexAnalysis.mem_argmin_iff_eq_iInf`. It is the step from "$v$ is
an optimal solution of the concave program $(P^*)$", a family of inequalities, to an equation
with the dual optimal value, which is a supremum. -/
theorem mem_argmax_iff_eq_iSup {g : E → EReal} : x ∈ argmax g ↔ g x = ⨆ z, g z :=
  ⟨fun h => le_antisymm (le_iSup g x) (iSup_le h), fun h z => by rw [h]; exact le_iSup g z⟩

omit [AddCommGroup E] [Module ℝ E] in
/-- The maximum set of $g$ is the minimum set of $-g$. -/
theorem argmax_eq_argmin_neg (g : E → EReal) : argmax g = argmin fun z => -(g z) :=
  Set.ext fun _ => forall_congr' fun _ => EReal.neg_le_neg_iff.symm

/-- Let $E$ and $F$ be real vector spaces paired by $B$, and let $f$ be a function on $E$ with
values in $[-\infty, +\infty]$. Then $x$ is in the minimum set of $f$ if and only if
$$0 \in \partial f(x).$$

The subdifferential is taken with respect to $B$. The equivalence is the definition of a
subgradient at $y = 0$. -/
theorem mem_argmin_iff_zero_mem_subdifferential (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (x : E) :
    x ∈ argmin f ↔ (0 : F) ∈ subdifferential B f x := by
  constructor
  · intro h z; simpa using h z
  · intro h z; simpa using h z

/-- For every function $f$ on $E$, the infimum is minus the conjugate at the origin:
$$\inf_x f(x) = -f^*(0).$$
-/
theorem iInf_eq_neg_convexConj_zero (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    (⨅ x, f x) = -(convexConj B f 0) := by
  rw [convexConj_apply_zero, neg_neg]

/-- For every function $f$ on $E$, the origin is in the effective domain of $f^*$ if and only if $f$
is bounded below, that is, $\inf_x f(x) > -\infty$. -/
theorem zero_mem_convexDom_convexConj_iff (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) :
    (0 : F) ∈ convexDom (convexConj B f) ↔ (⊥ : EReal) < ⨅ x, f x := by
  rw [mem_convexDom, convexConj_apply_zero, lt_top_iff_ne_top, bot_lt_iff_ne_bot, ne_eq, ne_eq,
    EReal.neg_eq_top_iff]

/-- The minimum set of a convex function is convex. -/
theorem convex_argmin (hf : ConvexFn f) : Convex ℝ (argmin f) := by
  rcases eq_or_ne (argmin f) ∅ with hE | hE
  · rw [hE]; exact convex_empty
  · obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hE
    have hset : argmin f = {z : E | f z ≤ f a} := by
      ext z
      exact ⟨fun hz => hz a, fun hz w => le_trans hz (ha w)⟩
    rw [hset]
    exact hf.convex_le _

/-- **The minimum set under a surjection.** Let $e \colon \alpha \to \beta$ be surjective and let
$g$ be a function on $\beta$ with values in $[-\infty, +\infty]$. Then the minimum set of
$x \mapsto g(e(x))$ is the preimage under $e$ of the minimum set of $g$.

Surjectivity is the only hypothesis that the proof uses. With `ConvexAnalysis.argmin_sepSum`,
this gives the decomposition principle. -/
theorem argmin_comp_of_surjective {α β : Type*} {g : β → EReal} {e : α → β}
    (he : Function.Surjective e) : argmin (fun x => g (e x)) = e ⁻¹' argmin g := by
  ext x
  exact ⟨fun hx w => by obtain ⟨z, rfl⟩ := he w; exact hx z, fun hx z => hx (e z)⟩

end Defs

/-!
### Separable sums on a finite product

A **separable** objective $x \mapsto \sum_i h_i(x_i)$ on a finite product $\prod_i E_i$ has its
minimum set and its effective domain given coordinatewise. This is the content of the *decomposition
principle*: once a Kuhn–Tucker vector has reduced a program to the minimization of
$h_1 + \dots + h_s$ over $C_1 \times \dots \times C_s$, the problem splits into $s$ independent
problems. Both statements are about the product itself. No isometry with $\mathbb{R}^n$, no relative
interior and no linear structure is used, since the minimum set and the effective domain depend only
on the order.
-/

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*} {h : ∀ i, E i → EReal}

/-- **The effective domain of a separable sum is the product of the effective domains.** Let $\iota$
be a finite index set and let $h_i$ be a function on $E_i$ with values in $[-\infty, +\infty]$
for each $i \in \iota$. If no $h_i$ takes the value $-\infty$, then
$$\operatorname{dom} \Bigl(x \mapsto \sum_i h_i(x_i)\Bigr) = \prod_i \operatorname{dom} h_i.$$

The hypothesis cannot be dropped: since $-\infty + (+\infty) = -\infty$ in `EReal`, a sum can be
finite while a summand is $+\infty$, and then the inclusion $\subseteq$ fails. The inclusion
$\supseteq$ holds without the hypothesis. -/
theorem convexDom_sepSum (hb : ∀ i (z : E i), h i z ≠ ⊥) :
    convexDom (fun x : ∀ i, E i => ∑ i, h i (x i)) = univ.pi fun i => convexDom (h i) := by
  ext x
  constructor
  · intro hx i _
    exact lt_top_iff_ne_top.2
      (EReal.forall_ne_top_of_sum_ne_top _ _ (fun j _ => hb j (x j))
        (lt_top_iff_ne_top.1 hx) i (Finset.mem_univ i))
  · intro hx
    choose c hc using fun j =>
      EReal.exists_coe_of_ne_bot_of_lt_top (hb j (x j)) (hx j (mem_univ j))
    have hsum : ∑ j, h j (x j) = ((∑ j, c j : ℝ) : EReal) := by
      rw [EReal.coe_sum]
      exact Finset.sum_congr rfl fun j _ => hc j
    change ∑ j, h j (x j) < ⊤
    rw [hsum]
    exact EReal.coe_lt_top _

/-- **A separable sum is minimized coordinatewise.** Let $\iota$ be a finite index set and let $h_i$
be a proper function on $E_i$ for each $i \in \iota$. Then the minimum set of
$x \mapsto \sum_i h_i(x_i)$ on $\prod_i E_i$ is the product of the minimum sets of the $h_i$:
$$\operatorname{argmin} \Bigl(x \mapsto \sum_i h_i(x_i)\Bigr) = \prod_i \operatorname{argmin}
  h_i.$$

The inclusion $\supseteq$ needs no hypothesis. The inclusion $\subseteq$ needs every $h_i$
proper, and both parts of properness are used: a point of every effective domain makes every
$h_j(x_j)$ finite, and this finiteness allows the terms with $j \neq i$ to be cancelled on both
sides, since addition in `EReal` is not cancellative. Without such points the statement is
false: for $\iota = \{0, 1\}$ with $h_0 \equiv +\infty$ and $h_1$ the identity on $\mathbb{R}$,
the left side is the whole space and the right side is empty. -/
theorem argmin_sepSum (hp : ∀ i, ProperConvex (h i)) :
    argmin (fun x : ∀ i, E i => ∑ i, h i (x i)) = univ.pi fun i => argmin (h i) := by
  classical
  ext x
  refine ⟨fun hx i _ z => ?_, fun hx z => Finset.sum_le_sum fun i _ => hx i (mem_univ i) (z i)⟩
  -- a common domain point certifies that the value at `x` is finite
  choose y hy using fun j => (hp j).convexDom_nonempty
  choose r hr using fun j =>
    EReal.exists_coe_of_ne_bot_of_lt_top ((hp j).ne_bot (y j)) (hy j)
  have hxle : ∑ j, h j (x j) ≤ ((∑ j, r j : ℝ) : EReal) := by
    rw [EReal.coe_sum]
    exact (hx y).trans (le_of_eq (Finset.sum_congr rfl fun j _ => hr j))
  have hxdom : x ∈ convexDom fun w : ∀ i, E i => ∑ j, h j (w j) :=
    lt_of_le_of_lt hxle (EReal.coe_lt_top _)
  have hxpi := (convexDom_sepSum fun j z => (hp j).ne_bot z).subset hxdom
  choose c hc using fun j =>
    EReal.exists_coe_of_ne_bot_of_lt_top ((hp j).ne_bot (x j)) (hxpi j (mem_univ j))
  -- off the `i`-th coordinate the sum is a real, so it cancels
  have hrest : ∑ j ∈ Finset.univ.erase i, h j (x j)
      = ((∑ j ∈ Finset.univ.erase i, c j : ℝ) : EReal) := by
    rw [EReal.coe_sum]
    exact Finset.sum_congr rfl fun j _ => hc j
  have hupdsum : ∑ j ∈ Finset.univ.erase i, h j (Function.update x i z j)
      = ∑ j ∈ Finset.univ.erase i, h j (x j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hupd : ∑ j, h j (x j) ≤ ∑ j, h j (Function.update x i z j) :=
    hx (Function.update x i z)
  rw [← Finset.add_sum_erase _ (fun j => h j (x j)) (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => h j (Function.update x i z j)) (Finset.mem_univ i),
    Function.update_self, hupdsum, hrest] at hupd
  exact (EReal.addLECancellable_coe _).add_le_add_iff_right.1 hupd

end Pi

/-! ### The minimum set as a subdifferential of the conjugate -/

section FenchelMoreau

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal}

/-- **The minimum set of a closed convex function is $\partial f^*(0)$.** Let $E$ be a real locally
convex space paired with $F$ by $B$ such that every continuous linear functional on $E$ has the
form $\langle \cdot, y \rangle$, and let $f$ be a closed convex function on $E$. Then
$$\operatorname{argmin} f = \partial f^*(0),$$
where the subdifferential of $f^*$ is taken with respect to the flipped pairing and is a subset
of $E$. In particular, the infimum of $f$ is attained exactly when $f^*$ is subdifferentiable at
the origin. This is part of Theorem 27.1 of [rockafellar1970convex].

The equality is the subgradient inequality for $f^*$ at the origin, where the Fenchel–Moreau
theorem turns $f^{**}$ back into $f$. -/
theorem argmin_eq_subdifferential_convexConj_zero (hf : ConvexFn f) (hc : ClosedConvex f) :
    argmin f = subdifferential B.flip (convexConj B f) 0 := by
  ext x
  have hbi : convexConj B.flip (convexConj B f) x = f x := congrFun (convexBiconj_eq_self hf hc) x
  have hpair : ((B.flip 0 x : ℝ) : EReal) = 0 := by simp
  rw [mem_argmin_iff_le_iInf, iInf_eq_neg_convexConj_zero B,
      mem_subdifferential_iff_add_convexConj_le, hbi,
    hpair, ← EReal.le_sub_iff_add_le (.inr (by simp)) (.inr (by simp)), zero_sub,
    EReal.le_neg]

/-- Let $E$ be a real locally convex space paired with $F$ by $B$ such that every continuous linear
functional on $E$ has the form $\langle \cdot, y \rangle$, and let $f$ be a closed proper convex
function on $E$. Then every nonempty level set $\{z \mid f(z) \le \alpha\}$ with $\alpha$ real
has the same recession cone, the polar of $\operatorname{dom} f^*$:
$$0^+ \{z \mid f(z) \le \alpha\} = \{x \mid \langle x, y \rangle \le 0 \text{ for all } y \in
  \operatorname{dom} f^*\}.$$
This is part of Theorem 27.1 of [rockafellar1970convex]. -/
theorem recessionCone_setOf_le_eq_polarCone_convexDom_convexConj (hf : ConvexFn f)
    (hc : ClosedConvex f)
    (hp : ProperConvex f) {α : ℝ} (hne : {z : E | f z ≤ (α : EReal)}.Nonempty) :
    recessionCone {z : E | f z ≤ (α : EReal)} = polarCone B.flip (convexDom (convexConj B f)) := by
  rw [recessionCone_setOf_le hf (ClosedProperConvexFn.isClosed_epi ⟨hf, hc, hp⟩) hne,
    recessionConeFn_eq_polarCone_convexDom_convexConj (B := B) ⟨hf, hc, hp⟩]

/-- Under the hypotheses of
`ConvexAnalysis.recessionCone_setOf_le_eq_polarCone_convexDom_convexConj`, let the infimum of
$f$ be attained at $a$ with a real value $f(a) = \mu$. Then the recession cone of the minimum
set is the polar of $\operatorname{dom} f^*$, because the minimum set is the level set at $\mu$. -/
theorem recessionCone_argmin_eq_polarCone_convexDom_convexConj (hf : ConvexFn f)
    (hc : ClosedConvex f)
    (hp : ProperConvex f) {a : E} (ha : a ∈ argmin f) {μ : ℝ} (hμ : f a = (μ : EReal)) :
    recessionCone (argmin f) = polarCone B.flip (convexDom (convexConj B f)) := by
  rw [argmin_eq_setOf_le ha hμ]
  exact recessionCone_setOf_le_eq_polarCone_convexDom_convexConj hf hc hp ⟨a, le_of_eq hμ⟩

end FenchelMoreau

/-! ### Minimising over a convex set -/

section Optimality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {h : E → EReal} {C : Set E} {x : E} {y : F}

/-- **Sufficiency of the optimality condition.** Let $E$ and $F$ be real vector spaces paired by
$B$, let $h$ be a function on $E$ with values in $[-\infty, +\infty]$, and let $C \subseteq E$.
If some $y \in \partial h(x)$ has $-y$ in the normal cone of $C$ at $x$, then
$$h(x) \le h(z) \qquad \text{for all } z \in C.$$

No hypothesis is needed: the subgradient inequality and the inequality that defines the normal
cone add up. The normal cone is `ConvexAnalysis.normalCone`, which is defined also for
$x \notin C$; the result then says that $h(x)$ is a lower bound for $h$ on $C$. -/
theorem le_of_mem_subdifferential_of_neg_mem_normalCone (hy : y ∈ subdifferential B h x)
    (hn : -y ∈ normalCone B C x) {z : E} (hz : z ∈ C) : h x ≤ h z := by
  have h2 : B (z - x) (-y) ≤ 0 := hn z hz
  rw [map_neg, neg_nonpos] at h2
  calc h x ≤ h x + ((B (z - x) y : ℝ) : EReal) :=
        le_add_of_nonneg_right (by exact_mod_cast h2)
    _ ≤ h z := hy z

omit [AddCommGroup E] [Module ℝ E] in
/-- Let $h$ be proper, let $x \in C$, and let $h(x) \le h(z)$ for all $z \in C$. Then $x$ is in the
minimum set of $h + \delta(\cdot \mid C)$, where $\delta(\cdot \mid C)$ is the indicator
function of $C$. So minimizing $h$ over $C$ is minimizing $h + \delta(\cdot \mid C)$ over the
whole space. -/
theorem mem_argmin_add_indicatorFn_of_forall (hp : ProperConvex h) (hx : x ∈ C)
    (hmin : ∀ z ∈ C, h x ≤ h z) : x ∈ argmin (h + indicatorFn C) := by
  intro z
  by_cases hzC : z ∈ C
  · simpa [indicatorFn_of_mem hx, indicatorFn_of_mem hzC] using hmin z hzC
  · have hrhs : (h + indicatorFn C) z = ⊤ := by
      rw [Pi.add_apply, indicatorFn_of_notMem hzC]
      exact EReal.add_top_of_ne_bot (hp.ne_bot z)
    rw [hrhs]
    exact le_top

omit [AddCommGroup E] [Module ℝ E] in
/-- If $x \in C$ is in the minimum set of $h + \delta(\cdot \mid C)$, then $h(x) \le h(z)$ for all
$z \in C$. This is the converse of `ConvexAnalysis.mem_argmin_add_indicatorFn_of_forall`. -/
theorem forall_le_of_mem_argmin_add_indicatorFn (hx : x ∈ argmin (h + indicatorFn C))
    (hxC : x ∈ C) {z : E} (hz : z ∈ C) : h x ≤ h z := by
  have hle := hx z
  rwa [Pi.add_apply, Pi.add_apply, indicatorFn_of_mem hxC, indicatorFn_of_mem hz, add_zero,
    add_zero] at hle

/-- **Necessity of the optimality condition.** Let $E$ and $F$ be real vector spaces paired by $B$,
let $h$ be a function on $E$, and let $C \subseteq E$ be such that the sum
$h + \delta(\cdot \mid C)$ is exact (`ConvexAnalysis.IsExactSum`). If $x \in C$ and
$h(x) \le h(z)$ for all $z \in C$, then there is a $y \in \partial h(x)$ such that $-y$ is in
the normal cone of $C$ at $x$.

The two hypotheses of the source are two ways to obtain this exactness. -/
theorem exists_mem_subdifferential_neg_mem_normalCone (hex : IsExactSum B h (indicatorFn C))
    (hx : x ∈ C) (hmin : ∀ z ∈ C, h x ≤ h z) :
    ∃ y ∈ subdifferential B h x, -y ∈ normalCone B C x := by
  have hzero : (0 : F) ∈ subdifferential B (h + indicatorFn C) x :=
    (mem_argmin_iff_zero_mem_subdifferential B _ x).1
      (mem_argmin_add_indicatorFn_of_forall hex.properConvex_left hx hmin)
  rw [hex.subdifferential_add x, subdifferential_indicatorFn hx] at hzero
  obtain ⟨y, hy, n, hn, hsum⟩ := hzero
  have hs : y + n = 0 := hsum
  have hny : -y = n := by
    rw [eq_comm, eq_neg_iff_add_eq_zero, add_comm]
    exact hs
  exact ⟨y, hy, hny ▸ hn⟩

end Optimality

/-! ### Existence of a minimiser -/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **The level set that carries the existence argument.** Let $E$ be a finite-dimensional real
normed space and let $f$ be a closed proper convex function on $E$ with no direction of
recession, $0^+ f = \{0\}$. Then every nonempty level set $\{z \mid f(z) \le \alpha\}$ with
$\alpha$ real is compact.

Only the forward direction is stated here. -/
theorem isCompact_setOf_le (hf : ConvexFn f) (hc : ClosedConvex f) (hp : ProperConvex f)
    (hrec : recessionConeFn f = {0}) {α : ℝ} (hne : {z : E | f z ≤ (α : EReal)}.Nonempty) :
    IsCompact {z : E | f z ≤ (α : EReal)} := by
  have hlsc : LowerSemicontinuous f := (closedConvex_iff_lowerSemicontinuous hp.ne_bot).1 hc
  have hepi : IsClosed (epi f) := lowerSemicontinuous_iff_isClosed_epi.1 hlsc
  refine (isCompact_iff_recessionCone_eq_zero (hf.convex_le _)
    (lowerSemicontinuous_iff_isClosed_le.1 hlsc α) hne).2 ?_
  rw [recessionCone_setOf_le hf hepi hne]
  exact hrec

/-- Let $E$ be a finite-dimensional real normed space and let $f$ be a closed proper convex function
on $E$ with no direction of recession, $0^+ f = \{0\}$. Then $f$ attains its infimum: the
minimum set of $f$ is nonempty. This is part of Theorem 27.2 of [rockafellar1970convex].

A nonempty level set of $f$ is closed and compact, so the lower semicontinuous $f$ attains a
minimum on it, and outside this level set $f$ is larger. -/
theorem argmin_nonempty_of_recessionConeFn_eq_zero (hf : ConvexFn f) (hc : ClosedConvex f)
    (hp : ProperConvex f) (hrec : recessionConeFn f = {0}) : (argmin f).Nonempty := by
  have hlsc : LowerSemicontinuous f := (closedConvex_iff_lowerSemicontinuous hp.ne_bot).1 hc
  obtain ⟨x₀, hx₀⟩ := hp.convexDom_nonempty
  obtain ⟨α, hα⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot x₀) (mem_convexDom.1 hx₀)
  set L : Set E := {z : E | f z ≤ (α : EReal)} with hL
  have hLne : L.Nonempty := ⟨x₀, le_of_eq hα⟩
  obtain ⟨a, haL, hamin⟩ := LowerSemicontinuousOn.exists_isMinOn hLne
    (isCompact_setOf_le hf hc hp hrec hLne) (hlsc.lowerSemicontinuousOn L)
  refine ⟨a, fun z => ?_⟩
  by_cases hzL : z ∈ L
  · exact isMinOn_iff.1 hamin z hzL
  · exact le_trans haL (le_of_lt (not_le.1 hzL))

/-- Let $E$ be a finite-dimensional real normed space and let $f$ be a closed proper convex function
on $E$ with no direction of recession, $0^+ f = \{0\}$. Then the minimum set of $f$ is compact.
This is part of Theorem 27.2 of [rockafellar1970convex].

With `ConvexAnalysis.argmin_nonempty_of_recessionConeFn_eq_zero` and
`ConvexAnalysis.convex_argmin`, the minimum set is a nonempty compact convex set. -/
theorem isCompact_argmin_of_recessionConeFn_eq_zero (hf : ConvexFn f) (hc : ClosedConvex f)
    (hp : ProperConvex f) (hrec : recessionConeFn f = {0}) : IsCompact (argmin f) := by
  obtain ⟨a, ha⟩ := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
    (lt_of_le_of_lt (ha _) (mem_convexDom.1 hp.convexDom_nonempty.choose_spec))
  have hset : argmin f = {z : E | f z ≤ (μ : EReal)} := by
    ext z
    constructor
    · intro hz; exact le_trans (hz a) (le_of_eq hμ)
    · intro hz w; exact le_trans (hμ ▸ hz) (ha w)
  rw [hset]
  exact isCompact_setOf_le hf hc hp hrec ⟨a, le_of_eq hμ⟩

/-- Let $E$ be a finite-dimensional real normed space and let $f$ be a closed proper convex function
on $E$ with no direction of recession. Then the infimum of $f$ is a real number. -/
theorem exists_iInf_eq_coe (hf : ConvexFn f) (hc : ClosedConvex f) (hp : ProperConvex f)
    (hrec : recessionConeFn f = {0}) : ∃ μ : ℝ, (⨅ z, f z) = (μ : EReal) := by
  obtain ⟨a, ha⟩ := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
  obtain ⟨x₀, hx₀⟩ := hp.convexDom_nonempty
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
    (lt_of_le_of_lt (ha x₀) (mem_convexDom.1 hx₀))
  exact ⟨μ, by rw [iInf_eq_of_mem_argmin ha, hμ]⟩

/-- **Well-posedness of the minimum.** Let $E$ be a finite-dimensional real normed space and let $f$
be a closed proper convex function on $E$ with no direction of recession, $0^+ f = \{0\}$. Then
for every $\varepsilon > 0$ there is a $\delta > 0$ such that every $x$ with
$$f(x) \le \inf f + \delta$$
is at distance less than $\varepsilon$ from some point of the minimum set. This is part of
Theorem 27.2 of [rockafellar1970convex].

The proof applies the extreme value theorem once, to the compact set $\{f \le \inf f + 1\}
\setminus (M + \varepsilon \operatorname{int} B)$, where $M$ is the minimum set and $B$ is the
unit ball. This replaces the nested-compactness argument of the source. -/
theorem exists_pos_forall_exists_mem_argmin_dist_lt (hf : ConvexFn f) (hc : ClosedConvex f)
    (hp : ProperConvex f) (hrec : recessionConeFn f = {0}) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, f x ≤ (⨅ z, f z) + (δ : EReal) → ∃ z ∈ argmin f, dist x z < ε := by
  have hlsc : LowerSemicontinuous f := (closedConvex_iff_lowerSemicontinuous hp.ne_bot).1 hc
  obtain ⟨a, ha⟩ := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
  obtain ⟨x₀, hx₀⟩ := hp.convexDom_nonempty
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
    (lt_of_le_of_lt (ha x₀) (mem_convexDom.1 hx₀))
  have hinf : (⨅ z, f z) = (μ : EReal) := by rw [iInf_eq_of_mem_argmin ha, hμ]
  set U : Set E := ⋃ w ∈ argmin f, Metric.ball w ε with hUdef
  have hUopen : IsOpen U := isOpen_biUnion fun w _ => Metric.isOpen_ball
  have hmemU : ∀ x : E, x ∈ U ↔ ∃ z ∈ argmin f, dist x z < ε := by
    intro x
    simp [hUdef, Metric.mem_ball]
  have haL : a ∈ {z : E | f z ≤ ((μ + 1 : ℝ) : EReal)} := by
    rw [Set.mem_ofPred_eq, hμ]
    exact_mod_cast (by linarith : μ ≤ μ + 1)
  have hLcomp : IsCompact {z : E | f z ≤ ((μ + 1 : ℝ) : EReal)} :=
    isCompact_setOf_le hf hc hp hrec ⟨a, haL⟩
  set K : Set E := {z : E | f z ≤ ((μ + 1 : ℝ) : EReal)} \ U with hKdef
  have hKcomp : IsCompact K := by
    rw [hKdef, Set.sdiff_eq]
    exact hLcomp.inter_right (isClosed_compl_iff.2 hUopen)
  have hfinish : ∀ d : ℝ, 0 < d → d ≤ 1 →
      (∀ x : E, x ∈ K → ¬ f x ≤ ((μ + d : ℝ) : EReal)) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x, f x ≤ (⨅ z, f z) + (δ : EReal) → ∃ z ∈ argmin f, dist x z < ε := by
    intro d hd0 hd1 hout
    refine ⟨d, hd0, fun x hx => ?_⟩
    rw [hinf, ← EReal.coe_add] at hx
    have hxL : x ∈ {z : E | f z ≤ ((μ + 1 : ℝ) : EReal)} :=
      le_trans hx (by exact_mod_cast (by linarith : μ + d ≤ μ + 1))
    refine (hmemU x).1 ?_
    by_contra hxU
    exact hout x ⟨hxL, hxU⟩ hx
  rcases Set.eq_empty_or_nonempty K with hKe | hKne
  · exact hfinish 1 one_pos le_rfl fun x hxK => absurd hxK (by rw [hKe]; exact Set.notMem_empty x)
  · obtain ⟨b, hbK, hbmin⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hKne hKcomp (hlsc.lowerSemicontinuousOn K)
    have hbnot : b ∉ argmin f := fun hb => hbK.2 ((hmemU b).2 ⟨b, hb, by simpa using hε⟩)
    obtain ⟨w, hw⟩ : ∃ w, f w < f b := by
      by_contra hcon
      push Not at hcon
      exact hbnot fun z => hcon z
    have hμb : (μ : EReal) < f b := lt_of_le_of_lt (by rw [← hμ]; exact ha w) hw
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot b)
      (lt_of_le_of_lt hbK.1 (EReal.coe_lt_top (μ + 1)))
    have hμr : μ < r := by
      rw [hr] at hμb
      exact_mod_cast hμb
    refine hfinish (min 1 ((r - μ) / 2)) (lt_min one_pos (by linarith)) (min_le_left _ _) ?_
    intro x hxK hxle
    have hble : ((r : ℝ) : EReal) ≤ ((μ + min 1 ((r - μ) / 2) : ℝ) : EReal) := by
      rw [← hr]
      exact le_trans (isMinOn_iff.1 hbmin x hxK) hxle
    rw [EReal.coe_le_coe_iff] at hble
    have hhalf : min 1 ((r - μ) / 2) ≤ (r - μ) / 2 := min_le_right _ _
    linarith

/-- **Minimizing nets approach the minimum set.** Let $E$ be a finite-dimensional real normed space
and let $f$ be a closed proper convex function on $E$ with no direction of recession,
$0^+ f = \{0\}$. Let $(u_i)$ be a net along a filter $l$ with $f(u_i) \to \inf f$. Then the
distance from $u_i$ to the minimum set tends to $0$.

The filter is arbitrary. The filter `Filter.atTop` on $\mathbb{N}$ gives the result for
sequences. -/
theorem tendsto_infDist_argmin (hf : ConvexFn f) (hc : ClosedConvex f) (hp : ProperConvex f)
    (hrec : recessionConeFn f = {0}) {ι : Type*} {l : Filter ι} {u : ι → E}
    (hu : Filter.Tendsto (fun i => f (u i)) l (nhds (⨅ z, f z))) :
    Filter.Tendsto (fun i => Metric.infDist (u i) (argmin f)) l (nhds 0) := by
  obtain ⟨μ, hμ⟩ := exists_iInf_eq_coe hf hc hp hrec
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hmain⟩ := exists_pos_forall_exists_mem_argmin_dist_lt hf hc hp hrec hε
  have hlt : (⨅ z, f z) < (⨅ z, f z) + (δ : EReal) := by
    rw [hμ, ← EReal.coe_add]
    exact_mod_cast (by linarith : μ < μ + δ)
  filter_upwards [hu (Iio_mem_nhds hlt)] with i hi
  obtain ⟨z, hz, hdz⟩ := hmain (u i) (le_of_lt hi)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
  exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hz) hdz

/-- Under the hypotheses of `ConvexAnalysis.tendsto_infDist_argmin`, every cluster point of a
minimizing net $(u_i)$ is in the minimum set. -/
theorem mem_argmin_of_mapClusterPt (hf : ConvexFn f) (hc : ClosedConvex f) (hp : ProperConvex f)
    (hrec : recessionConeFn f = {0}) {ι : Type*} {l : Filter ι} {u : ι → E}
    (hu : Filter.Tendsto (fun i => f (u i)) l (nhds (⨅ z, f z))) {x : E}
    (hx : MapClusterPt x l u) : x ∈ argmin f := by
  obtain ⟨μ, hμ⟩ := exists_iInf_eq_coe hf hc hp hrec
  have hMcomp : IsCompact (argmin f) := isCompact_argmin_of_recessionConeFn_eq_zero hf hc hp hrec
  have hMne : (argmin f).Nonempty := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
  refine (hMcomp.isClosed.mem_iff_infDist_zero hMne).2 ?_
  have key : ∀ ε : ℝ, 0 < ε → Metric.infDist x (argmin f) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hmain⟩ :=
      exists_pos_forall_exists_mem_argmin_dist_lt hf hc hp hrec (half_pos hε)
    have hlt : (⨅ z, f z) < (⨅ z, f z) + (δ : EReal) := by
      rw [hμ, ← EReal.coe_add]
      exact_mod_cast (by linarith : μ < μ + δ)
    have hV : {z : E | f z < (⨅ z, f z) + (δ : EReal)} ∈ Filter.map u l :=
      hu (Iio_mem_nhds hlt)
    obtain ⟨y, hy1, hy2⟩ :=
      clusterPt_iff_nonempty.1 hx (Metric.ball_mem_nhds x (half_pos hε)) hV
    obtain ⟨z, hz, hdz⟩ := hmain y (le_of_lt hy2)
    have hxy : dist x y < ε / 2 := by rwa [Metric.mem_ball, dist_comm] at hy1
    have hyz : Metric.infDist y (argmin f) ≤ dist y z := Metric.infDist_le_dist_of_mem hz
    calc Metric.infDist x (argmin f) ≤ Metric.infDist y (argmin f) + dist x y :=
          Metric.infDist_le_infDist_add_dist
      _ < ε := by linarith
  rcases lt_or_ge 0 (Metric.infDist x (argmin f)) with hpos | hnonpos
  · exact absurd (key _ hpos) (lt_irrefl _)
  · exact le_antisymm hnonpos Metric.infDist_nonneg

/-- Let $E$ be a finite-dimensional real normed space and let $f$ be a closed proper convex function
on $E$ with no direction of recession. Then every minimizing sequence $(u_n)$, with
$f(u_n) \to \inf f$, is bounded. -/
theorem isBounded_range_of_tendsto_iInf (hf : ConvexFn f) (hc : ClosedConvex f)
    (hp : ProperConvex f)
    (hrec : recessionConeFn f = {0}) {u : ℕ → E}
    (hu : Filter.Tendsto (fun i => f (u i)) Filter.atTop (nhds (⨅ z, f z))) :
    Bornology.IsBounded (Set.range u) := by
  have hMcomp : IsCompact (argmin f) := isCompact_argmin_of_recessionConeFn_eq_zero hf hc hp hrec
  have hMne : (argmin f).Nonempty := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
  obtain ⟨R, hR⟩ := hMcomp.isBounded.subset_closedBall (0 : E)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (Metric.tendsto_nhds.1 (tendsto_infDist_argmin hf hc hp hrec hu) 1 one_pos)
  have hsub : ∀ i, N ≤ i → u i ∈ Metric.closedBall (0 : E) (R + 1) := by
    intro i hi
    obtain ⟨w, hw, hdw⟩ := hMcomp.exists_infDist_eq_dist hMne (u i)
    have h1 : Metric.infDist (u i) (argmin f) < 1 := by
      have h2 := hN i hi
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg] at h2
    have h3 : dist (u i) w < 1 := by rwa [← hdw]
    have h4 : dist w 0 ≤ R := Metric.mem_closedBall.1 (hR hw)
    rw [Metric.mem_closedBall]
    calc dist (u i) 0 ≤ dist (u i) w + dist w 0 := dist_triangle _ _ _
      _ ≤ R + 1 := by linarith
  have hsplit : Set.range u ⊆ (u '' Set.Iio N) ∪ Metric.closedBall (0 : E) (R + 1) := by
    rintro _ ⟨i, rfl⟩
    rcases lt_or_ge i N with hi | hi
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr (hsub i hi)
  exact Bornology.IsBounded.subset
    (((Set.finite_Iio N).image u).isBounded.union Metric.isBounded_closedBall) hsplit

/-- Let $E$ be a finite-dimensional real normed space and let $f$ be a closed proper convex function
on $E$ whose minimum set is a single point $\{a\}$. Then every minimizing net $(u_i)$ along a
filter $l$, with $f(u_i) \to \inf f$, converges to $a$.

No recession hypothesis is needed: a minimum set with one point is a level set, and a bounded
nonempty level set forces the recession cone to be $\{0\}$. -/
theorem tendsto_of_argmin_eq_singleton (hf : ConvexFn f) (hc : ClosedConvex f) (hp : ProperConvex f)
    {a : E} (hM : argmin f = {a}) {ι : Type*} {l : Filter ι} {u : ι → E}
    (hu : Filter.Tendsto (fun i => f (u i)) l (nhds (⨅ z, f z))) :
    Filter.Tendsto u l (nhds a) := by
  have haM : a ∈ argmin f := by rw [hM]; exact Set.mem_singleton a
  obtain ⟨x₀, hx₀⟩ := hp.convexDom_nonempty
  obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
    (lt_of_le_of_lt (haM x₀) (mem_convexDom.1 hx₀))
  have hlsc : LowerSemicontinuous f := (closedConvex_iff_lowerSemicontinuous hp.ne_bot).1 hc
  have hne : {z : E | f z ≤ (μ : EReal)}.Nonempty := ⟨a, le_of_eq hμ⟩
  have hrec : recessionConeFn f = {0} := by
    rw [← recessionCone_setOf_le hf (lowerSemicontinuous_iff_isClosed_epi.1 hlsc) hne,
      ← argmin_eq_setOf_le haM hμ, hM, recessionCone_singleton]
  have hlim := tendsto_infDist_argmin hf hc hp hrec hu
  rw [hM] at hlim
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Metric.infDist_singleton] using hlim

end Existence

/-! ### Minimising over a closed convex set -/

section Constrained

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → EReal} {C : Set E}

omit [FiniteDimensional ℝ E] in
/-- The indicator function of a nonempty closed convex set is a closed proper convex function. -/
theorem closedProperConvexFn_indicatorFn (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty) :
    ClosedProperConvexFn (indicatorFn C) :=
  ⟨convexFn_indicatorFn.2 hC, closedConvex_indicatorFn hCc,
    ⟨by rw [convexDom_indicatorFn]; exact hCne, indicatorFn_ne_bot C⟩⟩

omit [FiniteDimensional ℝ E] in
/-- Let $h$ be a closed proper convex function on a real normed space $E$ and let $C$ be a nonempty
closed convex set such that $h + \delta(\cdot \mid C)$ is finite somewhere. Then the directions
of recession of $h + \delta(\cdot \mid C)$ are the directions of recession common to $h$ and
$C$:
$$0^+ (h + \delta(\cdot \mid C)) = 0^+ h \cap 0^+ C.$$

This is the recession formula for a sum, applied to an indicator function. The recession
function of $\delta(\cdot \mid C)$ is $\delta(\cdot \mid 0^+ C)$, which is $0$ on $0^+ C$ and
$+\infty$ outside it. -/
theorem recessionConeFn_add_indicatorFn (hh : ClosedProperConvexFn h) (hC : Convex ℝ C)
    (hCc : IsClosed C) (hCne : C.Nonempty) (hne : (convexDom (h + indicatorFn C)).Nonempty) :
    recessionConeFn (h + indicatorFn C) = recessionConeFn h ∩ recessionCone C := by
  have hsum := recessionFn_add hh (closedProperConvexFn_indicatorFn hC hCc hCne) hne
  ext y
  rw [Set.mem_inter_iff, mem_recessionConeFn, mem_recessionConeFn, hsum, Pi.add_apply,
    recessionFn_indicatorFn hCne]
  by_cases hy : y ∈ recessionCone C
  · rw [indicatorFn_of_mem hy, add_zero]
    simp [hy]
  · rw [indicatorFn_of_notMem hy,
      EReal.add_top_of_ne_bot (recessionFn_ne_bot hh.proper y)]
    simp [hy]

/-- **Attainment over a closed convex set.** Let $E$ be a finite-dimensional real normed space, let
$h$ be a closed proper convex function on $E$, and let $C \subseteq E$ be a nonempty closed
convex set such that $h$ and $C$ have no common direction of recession:
$$0^+ h \cap 0^+ C = \{0\}.$$
Then $h$ attains its infimum over $C$: there is an $x \in C$ with $h(x) \le h(z)$ for all
$z \in C$. This is part of Theorem 27.3 of [rockafellar1970convex].

The directions of recession of $h + \delta(\cdot \mid C)$ are the common ones, so the
unconstrained existence theorem applies. When $\operatorname{dom} h \cap C = \emptyset$, the
function $h$ is $+\infty$ on all of $C$ and every point of $C$ is a minimizer. -/
theorem exists_forall_le_of_recessionConeFn_inter_eq_zero (hh : ClosedProperConvexFn h)
    (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : recessionConeFn h ∩ recessionCone C = {0}) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z := by
  by_cases hne : (convexDom (h + indicatorFn C)).Nonempty
  · have hsum : ClosedProperConvexFn (h + indicatorFn C) :=
      hh.add (closedProperConvexFn_indicatorFn hC hCc hCne) hne
    obtain ⟨x, hx⟩ := argmin_nonempty_of_recessionConeFn_eq_zero hsum.convex hsum.closed
      hsum.proper (by rw [recessionConeFn_add_indicatorFn hh hC hCc hCne hne]; exact hrec)
    obtain ⟨w, hw⟩ := hne
    have hxdom : x ∈ convexDom (h + indicatorFn C) :=
        mem_convexDom.2 (lt_of_le_of_lt (hx w) (mem_convexDom.1 hw))
    rw [convexDom_add hh.proper.ne_bot (indicatorFn_ne_bot C), convexDom_indicatorFn] at hxdom
    exact ⟨x, hxdom.2, fun z hz => forall_le_of_mem_argmin_add_indicatorFn hx hxdom.2 hz⟩
  · obtain ⟨x, hx⟩ := hCne
    refine ⟨x, hx, fun z hz => ?_⟩
    have hempty : convexDom h ∩ C = ∅ := by
      rw [← convexDom_indicatorFn C, ← convexDom_add hh.proper.ne_bot (indicatorFn_ne_bot C)]
      exact Set.not_nonempty_iff_eq_empty.1 hne
    have hz' : h z = ⊤ := by
      by_contra hcon
      exact Set.eq_empty_iff_forall_notMem.1 hempty z
        ⟨mem_convexDom.2 (lt_top_iff_ne_top.2 hcon), hz⟩
    rw [hz']
    exact le_top

/-- Let $E$ be a finite-dimensional real normed space, let $h$ and $g_i$ (for $i$ in an arbitrary
index set) be closed proper convex functions on $E$, and let the system $g_i(x) \le 0$ for all
$i$ have a solution. If $h$ and the $g_i$ have no common direction of recession,
$$0^+ h \cap \bigcap_i 0^+ g_i = \{0\},$$
then $h$ attains its infimum subject to the constraints $g_i(x) \le 0$. -/
theorem exists_forall_le_of_forall_le_zero {ι : Type*} {g : ι → E → EReal}
    (hh : ClosedProperConvexFn h) (hg : ∀ i, ClosedProperConvexFn (g i))
    (hCne : {x : E | ∀ i, g i x ≤ 0}.Nonempty)
    (hrec : recessionConeFn h ∩ ⋂ i, recessionConeFn (g i) = {0}) :
    ∃ x, (∀ i, g i x ≤ 0) ∧ ∀ z, (∀ i, g i z ≤ 0) → h x ≤ h z := by
  obtain ⟨x₀, hx₀⟩ := hCne
  have hCeq : {x : E | ∀ i, g i x ≤ 0} = ⋂ i, {z : E | g i z ≤ ((0 : ℝ) : EReal)} := by
    ext z
    simp
  have hconv : ∀ i, Convex ℝ {z : E | g i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    (hg i).convex.convex_le _
  have hclosed : ∀ i, IsClosed {z : E | g i z ≤ ((0 : ℝ) : EReal)} := fun i =>
    lowerSemicontinuous_iff_isClosed_le.1 (hg i).lowerSemicontinuous 0
  have hx₀' : x₀ ∈ ⋂ i, {z : E | g i z ≤ ((0 : ℝ) : EReal)} := hCeq ▸ hx₀
  have hCrec : recessionCone {x : E | ∀ i, g i x ≤ 0} = ⋂ i, recessionConeFn (g i) := by
    rw [hCeq, recessionCone_iInter hconv hclosed ⟨x₀, hx₀'⟩]
    exact Set.iInter_congr fun i =>
      recessionCone_setOf_le (hg i).convex (hg i).isClosed_epi ⟨x₀, Set.mem_iInter.1 hx₀' i⟩
  obtain ⟨x, hxC, hmin⟩ := exists_forall_le_of_recessionConeFn_inter_eq_zero hh
    (by rw [hCeq]; exact convex_iInter hconv) (by rw [hCeq]; exact isClosed_iInter hclosed)
    ⟨x₀, hx₀⟩ (by rw [hCrec]; exact hrec)
  exact ⟨x, hxC, hmin⟩

end Constrained

/-!
### The polyhedral refinement

For a polyhedral set $C$ the recession hypothesis becomes weaker: instead of "$h$ and $C$ have no
common direction of recession" it is "every common direction of recession is a direction in which
$h$ is constant". The source derives this from Helly's theorem. The proof here projects $E$ along
the constancy space of $h$. This does not change $h$, and it reduces the common recession cone to
$\{0\}$. Polyhedrality of $C$ is used once: a linear map commutes with taking the recession cone of
a polyhedral set, and this fails for other sets.
-/

section ConstancyReduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → EReal} {C : Set E}

omit [FiniteDimensional ℝ E] in
/-- If $x - y$ is in the constancy space of $h$, then $h(x) = h(y)$.

This is `ConvexAnalysis.mem_constancySpace_iff_forall_eq` read as a statement about a pair of
points instead of a direction. -/
theorem eq_of_sub_mem_constancySpace {x y : E} (hxy : x - y ∈ constancySpace h) : h x = h y := by
  have hxy' : y + (1 : ℝ) • (x - y) = x := by rw [one_smul]; abel
  have hval := (mem_constancySpace_iff_forall_eq.1 hxy) y 1
  rwa [hxy'] at hval

omit [FiniteDimensional ℝ E] in
/-- **Every subspace is the kernel of a linear projection.** Let $M$ be a subspace of a real normed
space $E$. Then there are a linear map $A \colon E \to E$ and a subspace $N$ such that
$x - Ax \in M$ for all $x$, $Ay = 0$ for all $y \in M$, $Ax \in N$ for all $x$, and $Ay = y$ for
all $y \in N$.

This is how an argument that passes to the quotient by a subspace stays inside $E$. A function
that is constant along $M$ does not change under $A$. -/
theorem exists_linearProj (M : Submodule ℝ E) :
    ∃ (A : E →ₗ[ℝ] E) (N : Submodule ℝ E), (∀ x, x - A x ∈ M) ∧ (∀ y ∈ M, A y = 0) ∧
      (∀ x, A x ∈ N) ∧ ∀ y ∈ N, A y = y := by
  obtain ⟨N, hN⟩ := Submodule.exists_isCompl M
  refine ⟨(LinearMap.id : E →ₗ[ℝ] E) - M.projection N hN, N, fun x => ?_, fun y hy => ?_,
    fun x => ?_, fun y hy => ?_⟩
  · have hval : x - ((LinearMap.id : E →ₗ[ℝ] E) - M.projection N hN) x
        = M.projection N hN x := by simp
    rw [hval, ← Submodule.coe_projectionOnto_apply]
    exact (M.projectionOnto N hN x).2
  · have hfix : M.projection N hN y = y := by
      rw [← Submodule.coe_projectionOnto_apply, Submodule.projectionOnto_apply_of_mem_left hN hy]
    simp [hfix]
  · have hval : ((LinearMap.id : E →ₗ[ℝ] E) - M.projection N hN) x = x - M.projection N hN x := by
      simp
    rw [hval, ← Submodule.projectionOnto_apply_eq_zero_iff hN, map_sub,
      Submodule.projectionOnto_projection hN, sub_self]
  · have hzero : M.projection N hN y = 0 := by
      rw [← Submodule.coe_projectionOnto_apply, Submodule.projectionOnto_apply_of_mem_right hN hy,
        Submodule.coe_zero]
    simp [hzero]

/-- **Attainment over a closed convex set, general form.** Let $E$ be a finite-dimensional real
normed space, let $h$ be a closed proper convex function on $E$, and let $C \subseteq E$ be a
nonempty closed convex set. Suppose that every direction of recession common to $h$ and $C$ is
both a direction in which $h$ is constant and a direction of linearity of $C$:
$$0^+ h \cap 0^+ C \subseteq (\text{constancy space of } h) \cap (\text{lineality space of }
  C).$$
Then $h$ attains its infimum over $C$. This is part of Theorem 27.3 of [rockafellar1970convex].

The common recession cone can now be any such subspace, not only $\{0\}$. The proof projects
along the intersection of `ConvexAnalysis.constancySubmodule h` and
`ConvexAnalysis.linealitySubmodule C`, under which the image of $C$ is $C \cap N$. -/
theorem exists_forall_le_of_inter_subset_constancySpace_inter_linealitySpace
    (hh : ClosedProperConvexFn h) (hC : Convex ℝ C) (hCc : IsClosed C) (hCne : C.Nonempty)
    (hrec : recessionConeFn h ∩ recessionCone C ⊆ constancySpace h ∩ linealitySpace C) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z := by
  obtain ⟨A, N, hsub, hA0, hAN, hAfix⟩ :=
    exists_linearProj (constancySubmodule h ⊓ linealitySubmodule C)
  have hsubc : ∀ x, x - A x ∈ constancySpace h := fun x =>
    mem_constancySubmodule.1 (Submodule.mem_inf.1 (hsub x)).1
  have hsubl : ∀ x, x - A x ∈ linealitySpace C := fun x =>
    mem_linealitySubmodule.1 (Submodule.mem_inf.1 (hsub x)).2
  have hmemC : ∀ x ∈ C, A x ∈ C := by
    intro x hx
    have hneg : -(x - A x) ∈ recessionCone C := (mem_linealitySpace.1 (hsubl x)).2
    have := add_mem_of_mem_recessionCone hneg hx
    rwa [show x + -(x - A x) = A x by abel] at this
  have himg : A '' C = C ∩ (N : Set E) := by
    refine Set.Subset.antisymm ?_ fun y hy => ⟨y, hy.1, hAfix y hy.2⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hmemC x hx, hAN x⟩
  obtain ⟨x₀, hx₀⟩ := hCne
  have hne : (C ∩ (N : Set E)).Nonempty := ⟨A x₀, hmemC x₀ hx₀, hAN x₀⟩
  have hrecimg : recessionCone (A '' C) = recessionCone C ∩ (N : Set E) := by
    rw [himg, recessionCone_inter hC hCc N.convex N.closed_of_finiteDimensional hne,
      recessionCone_coe_submodule]
  have hrec' : recessionConeFn h ∩ recessionCone (A '' C) = {0} := by
    refine Set.Subset.antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨hy1, hy2⟩ := hy
      rw [hrecimg] at hy2
      obtain ⟨hy2C, hy2N⟩ := hy2
      have hyM : y ∈ constancySubmodule h ⊓ linealitySubmodule C := by
        obtain ⟨hc, hl⟩ := hrec ⟨hy1, hy2C⟩
        exact Submodule.mem_inf.2 ⟨mem_constancySubmodule.2 hc, mem_linealitySubmodule.2 hl⟩
      have h1 : A y = 0 := hA0 y hyM
      have h2 : A y = y := hAfix y hy2N
      exact Set.mem_singleton_iff.2 (by rw [← h2, h1])
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨recessionFn_apply_zero_le h, zero_mem_recessionCone _⟩
  have hCimgconv : Convex ℝ (A '' C) := by rw [himg]; exact hC.inter N.convex
  have hCimgcl : IsClosed (A '' C) := by
    rw [himg]; exact hCc.inter N.closed_of_finiteDimensional
  obtain ⟨x', hx'C, hx'min⟩ := exists_forall_le_of_recessionConeFn_inter_eq_zero hh
    hCimgconv hCimgcl ⟨A x₀, ⟨x₀, hx₀, rfl⟩⟩ hrec'
  obtain ⟨x, hxC, rfl⟩ := hx'C
  refine ⟨x, hxC, fun z hz => ?_⟩
  rw [eq_of_sub_mem_constancySpace (hsubc x), eq_of_sub_mem_constancySpace (hsubc z)]
  exact hx'min (A z) ⟨z, hz, rfl⟩

/-- **Attainment over a polyhedral set.** Let $E$ be a finite-dimensional real normed space, let $h$
be a closed proper convex function on $E$, and let $C \subseteq E$ be a nonempty polyhedral
convex set. Suppose that every direction of recession common to $h$ and $C$ is a direction in
which $h$ is constant:
$$0^+ h \cap 0^+ C \subseteq \text{constancy space of } h.$$
Then $h$ attains its infimum over $C$. This is part of Theorem 27.3 of [rockafellar1970convex].

Polyhedrality of $C$ is needed for the weaker hypothesis. On $\mathbb{R}^2$ take
$h(x_1, x_2) = x_2$ and the closed convex set $C = \{x \mid x_1 \ge x_2^2\}$. The common
recession cone is $\{(a, 0) \mid a \ge 0\}$, along which $h$ is constant, but
$\inf_C h = -\infty$. The proof replaces $C$ by its image under a projection that annihilates
the constancy space of $h$. The image is polyhedral, $h$ is constant on the fibres, and the
common recession cone becomes $\{0\}$. -/
theorem exists_forall_le_of_polyhedral_of_inter_subset_constancySpace
    (hh : ClosedProperConvexFn h) (hC : Polyhedral C) (hCne : C.Nonempty)
    (hrec : recessionConeFn h ∩ recessionCone C ⊆ constancySpace h) :
    ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z := by
  obtain ⟨A, -, hsub', hA0, -, -⟩ := exists_linearProj (constancySubmodule h)
  have hsub : ∀ x, x - A x ∈ constancySpace h := fun x => mem_constancySubmodule.1 (hsub' x)
  have hCimg : Polyhedral (A '' C) := hC.image A
  have hCimgne : (A '' C).Nonempty := hCne.image A
  have hrec' : recessionConeFn h ∩ recessionCone (A '' C) = {0} := by
    refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨hy1, hy2⟩ := hy
      rw [hC.recessionCone_image hCne A] at hy2
      obtain ⟨y', hy', rfl⟩ := hy2
      have hdrec : y' - A y' ∈ recessionConeFn h := (mem_constancySpace.1 (hsub y')).1
      have hy'rec : y' ∈ recessionConeFn h := by
        have hadd : A y' + (y' - A y') ∈ recessionConeFn h :=
          (recessionPointedConeFn h).add_mem hy1 hdrec
        have heq : A y' + (y' - A y') = y' := by abel
        rwa [heq] at hadd
      exact Set.mem_singleton_iff.2
        (hA0 y' (mem_constancySubmodule.2 (hrec ⟨hy'rec, hy'⟩)))
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨recessionFn_apply_zero_le h, zero_mem_recessionCone _⟩
  obtain ⟨x', hx'C, hx'min⟩ := exists_forall_le_of_recessionConeFn_inter_eq_zero hh
    hCimg.convex hCimg.isClosed hCimgne hrec'
  obtain ⟨x, hxC, rfl⟩ := hx'C
  refine ⟨x, hxC, fun z hz => ?_⟩
  rw [eq_of_sub_mem_constancySpace (hsub x), eq_of_sub_mem_constancySpace (hsub z)]
  exact hx'min (A z) ⟨z, hz, rfl⟩

/-- Let $E$ be a finite-dimensional real normed space, let $h$ be a closed proper convex function on
$E$ such that every direction of recession of $h$ is a direction in which $h$ is affine (the
recession cone is in the lineality space of $h$), and let $C$ be a nonempty polyhedral convex
set on which $h$ is bounded below by a real number. Then $h$ attains its infimum over $C$.

This hypothesis is weaker than the constancy hypothesis of
`ConvexAnalysis.exists_forall_le_of_polyhedral_of_inter_subset_constancySpace`, and the lower
bound on $C$ is the price. A direction of recession $y$ in which $h$ is affine has slope
$\nu = (h0^+)(y) \le 0$, and a lower bound along the half-lines of $C$ in this direction forces
$\nu = 0$, which is constancy. The lower bound cannot be dropped: $h(x_1, x_2) = x_1$ on
$\mathbb{R}^2$ is affine in every direction, and its infimum over $C = \{x \mid x_2 = 0\}$ is
$-\infty$. The hypothesis holds for every affine or convex quadratic $h$, and whenever
$\operatorname{dom} h^*$ is affine. -/
theorem exists_forall_le_of_polyhedral_of_recessionConeFn_subset_linealitySpaceFn
    (hh : ClosedProperConvexFn h) (hC : Polyhedral C) (hCne : C.Nonempty)
    (hrec : recessionConeFn h ⊆ linealitySpaceFn h) {β : ℝ}
    (hbdd : ∀ x ∈ C, (β : EReal) ≤ h x) : ∃ x ∈ C, ∀ z ∈ C, h x ≤ h z := by
  rcases Set.eq_empty_or_nonempty (C ∩ convexDom h) with hemp | ⟨x₀, hx₀C, hx₀⟩
  · obtain ⟨x, hx⟩ := hCne
    have htop : ∀ z ∈ C, h z = ⊤ := fun z hz => by
      by_contra hcon
      exact (Set.eq_empty_iff_forall_notMem.1 hemp z) ⟨hz, lt_top_iff_ne_top.2 hcon⟩
    exact ⟨x, hx, fun z hz => by rw [htop x hx, htop z hz]⟩
  · refine exists_forall_le_of_polyhedral_of_inter_subset_constancySpace hh hC hCne ?_
    rintro y ⟨hy1, hy2⟩
    exact mem_constancySpace_of_mem_linealitySpaceFn hh.proper hy1 (hrec hy1) hx₀
      fun a ha => hbdd _ (hy2 x₀ hx₀C a ha)

/-- Let $E$ be a finite-dimensional real normed space and let $h$ be a closed proper convex function
on $E$ whose recession cone consists of directions in which $h$ is constant (equivalently, the
recession cone is a subspace). Then $h$ attains its infimum.

This is the unconstrained case of the polyhedral refinement. The case of the subspace $\{0\}$ is
existence with no direction of recession. -/
theorem argmin_nonempty_of_recessionConeFn_subset_constancySpace (hh : ClosedProperConvexFn h)
    (hrec : recessionConeFn h ⊆ constancySpace h) : (argmin h).Nonempty := by
  obtain ⟨x, -, hx⟩ := exists_forall_le_of_polyhedral_of_inter_subset_constancySpace hh
    polyhedral_univ ⟨0, Set.mem_univ 0⟩ fun y hy => hrec hy.1
  exact ⟨x, mem_argmin_iff.2 fun z => hx z (Set.mem_univ z)⟩

end ConstancyReduction


/-! ### Polyhedral minimisation -/

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- **A polyhedral convex function that is bounded below attains its infimum.** Let $E$ be a
finite-dimensional real normed space and let $f$ be a polyhedral convex function on $E$ with
$\inf f > -\infty$. Then the minimum set of $f$ is nonempty.

Neither closedness nor properness is assumed. In the finitely generated description
$\operatorname{epi} f = \operatorname{conv} P + \operatorname{cone} D$, a lower bound forces
every generating direction to point upward, so the vertical coordinate is minimized at one of
the finitely many generating points. -/
theorem argmin_nonempty_of_polyhedralFn (hf : PolyhedralFn f) (hbdd : ⊥ < ⨅ x, f x) :
    (argmin f).Nonempty := by
  classical
  have hbot : ∀ x, f x ≠ ⊥ := by
    intro x hx
    have hle : (⨅ z, f z) ≤ (⊥ : EReal) := by rw [← hx]; exact iInf_le f x
    exact absurd hle (not_le.2 hbdd)
  rcases eq_top_or_lt_top (⨅ x, f x) with htop | htop
  · refine ⟨0, fun z => ?_⟩
    have hz : f z = ⊤ := by
      refine top_le_iff.1 ?_
      rw [← htop]
      exact iInf_le f z
    rw [hz]
    exact le_top
  obtain ⟨β, hβ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (ne_of_gt hbdd) htop
  have hβle : ∀ x, (β : EReal) ≤ f x := by
    intro x
    rw [← hβ]
    exact iInf_le f x
  obtain ⟨P, D, hPD⟩ := Polyhedral.finitelyGenerated (hf : Polyhedral (epi f))
  -- the epigraph is non-empty, so there is at least one generating point
  have hepine : (epi f).Nonempty := by
    obtain ⟨x, hx⟩ := iInf_lt_iff.1 htop
    obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot x) hx
    exact ⟨(x, r), mk_mem_epi.2 (le_of_eq hr)⟩
  have hPne : (P : Finset (E × ℝ)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty P with rfl | hne
    · exfalso
      rw [hPD] at hepine
      simp only [Finset.coe_empty, convexHull_empty, Set.empty_add] at hepine
      exact hepine.ne_empty rfl
    · exact hne
  obtain ⟨p₀, hp₀⟩ := hPne
  have hmem_epi : ∀ p ∈ P, (p : E × ℝ) ∈ epi f := by
    intro p hp
    rw [hPD]
    exact ⟨p, subset_convexHull ℝ _ (by exact_mod_cast hp), 0, Submodule.zero_mem _, by simp⟩
  -- every generating direction points upward
  have hDnonneg : ∀ d ∈ D, (0 : ℝ) ≤ (d : E × ℝ).2 := by
    intro d hd
    by_contra hneg
    push Not at hneg
    have hβp₀ : (β : EReal) ≤ (p₀.2 : EReal) := le_trans (hβle p₀.1) (hmem_epi p₀ hp₀)
    have hβp₀' : β ≤ p₀.2 := by exact_mod_cast hβp₀
    have hdne : d.2 ≠ 0 := ne_of_lt hneg
    have htpos : 0 < (p₀.2 - β + 1) / (-d.2) := div_pos (by linarith) (by linarith)
    have hmemd : ((p₀.2 - β + 1) / (-d.2)) • (d : E × ℝ) ∈
        (PointedCone.hull ℝ (D : Set (E × ℝ)) : Set (E × ℝ)) :=
      Submodule.smul_mem _ (⟨(p₀.2 - β + 1) / (-d.2), htpos.le⟩ : {c : ℝ // 0 ≤ c})
        (PointedCone.subset_hull (by exact_mod_cast hd))
    have hsum : (p₀ : E × ℝ) + ((p₀.2 - β + 1) / (-d.2)) • (d : E × ℝ) ∈ epi f := by
      rw [hPD]
      exact ⟨p₀, subset_convexHull ℝ _ (by exact_mod_cast hp₀), _, hmemd, rfl⟩
    have hval : ((p₀ : E × ℝ) + ((p₀.2 - β + 1) / (-d.2)) • (d : E × ℝ)).2
        = p₀.2 + ((p₀.2 - β + 1) / (-d.2)) * d.2 := rfl
    have hle := le_trans (hβle _) hsum
    rw [hval] at hle
    have hle' : β ≤ p₀.2 + ((p₀.2 - β + 1) / (-d.2)) * d.2 := by exact_mod_cast hle
    have hcancel : ((p₀.2 - β + 1) / (-d.2)) * d.2 = -(p₀.2 - β + 1) := by
      field_simp
    rw [hcancel] at hle'
    linarith
  have hBall : ∀ b ∈ (PointedCone.hull ℝ (D : Set (E × ℝ)) : Set (E × ℝ)),
      (0 : ℝ) ≤ (b : E × ℝ).2 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem z hz => exact hDnonneg z (by exact_mod_cast hz)
    | zero => exact le_refl 0
    | add z w _ _ hz hw =>
        have hadd : ((z + w : E × ℝ)).2 = z.2 + w.2 := rfl
        rw [hadd]
        linarith
    | smul c z _ hz =>
        have hc : (0 : ℝ) ≤ (c : ℝ) := c.2
        have hval : ((c • z : E × ℝ)).2 = (c : ℝ) * z.2 := rfl
        rw [hval]
        exact mul_nonneg hc hz
  -- the vertical coordinate is minimised over the generating points
  obtain ⟨pm, hpmP, hpmmin⟩ := P.exists_min_image (fun p : E × ℝ => p.2) ⟨p₀, hp₀⟩
  have hlow : ∀ q ∈ epi f, pm.2 ≤ (q : E × ℝ).2 := by
    intro q hq
    rw [hPD] at hq
    obtain ⟨a, ha, b, hb, hab⟩ := hq
    have hA : pm.2 ≤ a.2 := by
      have hsub : convexHull ℝ (P : Set (E × ℝ)) ⊆ {z : E × ℝ | pm.2 ≤ z.2} :=
        convexHull_min (fun p hp => hpmmin p (by exact_mod_cast hp))
          (convex_halfSpace_ge (LinearMap.isLinear (LinearMap.snd ℝ E ℝ)) pm.2)
      exact hsub ha
    have hB : (0 : ℝ) ≤ b.2 := hBall b hb
    have hq2 : (q : E × ℝ).2 = a.2 + b.2 := by rw [← hab]; rfl
    rw [hq2]
    linarith
  refine ⟨pm.1, fun z => ?_⟩
  have h1 : f pm.1 ≤ (pm.2 : EReal) := hmem_epi pm hpmP
  rcases eq_top_or_lt_top (f z) with hz | hz
  · rw [hz]
    exact le_top
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hbot z) hz
  have hzepi : ((z, r) : E × ℝ) ∈ epi f := mk_mem_epi.2 (le_of_eq hr)
  have hmr : pm.2 ≤ r := hlow _ hzepi
  calc f pm.1 ≤ (pm.2 : EReal) := h1
    _ ≤ (r : EReal) := by exact_mod_cast hmr
    _ = f z := hr.symm

/-- Let $E$ be a finite-dimensional real normed space, let $f$ be a polyhedral convex function on
$E$, and let $C$ be a nonempty polyhedral convex set with $\inf_{x \in C} f(x) > -\infty$. Then
$f$ attains its infimum over $C$.

The restriction of $f$ to $C$ cuts the epigraph by the vertical prism over $C$, so the
restriction is again polyhedral. The source derives this from the affine-recession form
`ConvexAnalysis.exists_forall_le_of_polyhedral_of_recessionConeFn_subset_linealitySpaceFn`, and
hence from Helly's theorem; this argument needs neither. -/
theorem exists_forall_le_of_polyhedralFn_of_polyhedral (hf : PolyhedralFn f) {C : Set E}
    (hC : Polyhedral C) (hCne : C.Nonempty) (hbdd : ⊥ < ⨅ x ∈ C, f x) :
    ∃ x ∈ C, ∀ z ∈ C, f x ≤ f z := by
  classical
  set g : E → EReal := fun x => ⨅ _ : x ∈ C, f x with hgdef
  have hgin : ∀ x ∈ C, g x = f x := fun x hx => iInf_pos hx
  have hgout : ∀ x ∉ C, g x = ⊤ := fun x hx => iInf_neg hx
  have hgpoly : PolyhedralFn g := by
    have hepi : epi g = epi f ∩ (C ×ˢ (Set.univ : Set ℝ)) := by
      ext p
      rw [mem_epi, Set.mem_inter_iff, mem_epi, Set.mem_prod]
      by_cases hx : p.1 ∈ C
      · rw [hgin _ hx]
        simp [hx]
      · rw [hgout _ hx, top_le_iff]
        simp [hx]
    change Polyhedral (epi g)
    rw [hepi]
    exact Polyhedral.inter hf (Polyhedral.prod hC polyhedral_univ)
  obtain ⟨x, hx⟩ := argmin_nonempty_of_polyhedralFn hgpoly hbdd
  by_cases hxC : x ∈ C
  · refine ⟨x, hxC, fun z hz => ?_⟩
    have h := hx z
    rwa [hgin _ hxC, hgin _ hz] at h
  · obtain ⟨x₀, hx₀⟩ := hCne
    refine ⟨x₀, hx₀, fun z hz => ?_⟩
    have h := hx z
    rw [hgout _ hxC, hgin _ hz, top_le_iff] at h
    rw [h]
    exact le_top

end Polyhedral

/-!
### The conjugate at the origin

Three properties of $f^*$ near the origin: the interior of $\operatorname{dom} f^*$ controls the
boundedness of the minimum set, and the support functions of the level sets are obtained from $f^*$
by homogenization and by a limit of directional derivatives.
-/

section ConjugateAtZero

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : E → EReal}

omit [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space and $F$ a finite-dimensional real normed space, paired by $B$
such that the pairing represents the continuous linear functionals on both spaces, and let $f$
be a closed proper convex function on $E$. Then the origin is in the interior of
$\operatorname{dom} f^*$ if and only if $f$ has no direction of recession, $0^+ f = \{0\}$.

The recession cone of $f$ is the polar of $\operatorname{dom} f^*$, which is $\{0\}$ exactly in
this case. -/
theorem zero_mem_interior_convexDom_convexConj_iff_recessionConeFn_eq_zero (hf : ConvexFn f)
    (hc : ClosedConvex f)
    (hp : ProperConvex f) :
    (0 : F) ∈ interior (convexDom (convexConj B f)) ↔ recessionConeFn f = {(0 : E)} := by
  rw [zero_mem_interior_iff_polarCone_eq_zero (B := B) (convexFn_convexConj B f).convex_convexDom
      (properConvex_convexConj ⟨hf, hc, hp⟩).convexDom_nonempty,
    ← recessionConeFn_eq_polarCone_convexDom_convexConj (B := B) ⟨hf, hc, hp⟩]

omit [FiniteDimensional ℝ E] in
/-- Under the hypotheses of
`ConvexAnalysis.zero_mem_interior_convexDom_convexConj_iff_recessionConeFn_eq_zero`, the origin
is in the relative interior of $\operatorname{dom} f^*$ if and only if every direction of
recession of $f$ is a direction in which $f$ is constant.

The relative-interior criterion for $\operatorname{dom} f^*$, at the origin, reduces to the
inclusion of $0^+ f$ in the constancy space of $f$. -/
theorem zero_mem_relint_convexDom_convexConj_iff_recessionConeFn_subset_constancySpace
    (hf : ConvexFn f)
    (hc : ClosedConvex f) (hp : ProperConvex f) :
    (0 : F) ∈ ri (convexDom (convexConj B f)) ↔ recessionConeFn f ⊆ constancySpace f := by
  rw [mem_relint_convexDom_convexConj_iff (B := B) ⟨hf, hc, hp⟩ 0]
  simp only [map_zero, EReal.coe_zero]
  constructor
  · rintro ⟨h1, h2⟩ y hy
    have hy0 : recessionFn f y = 0 := le_antisymm hy (h1 y)
    have hne : ¬ (-recessionFn f (-y) ≠ recessionFn f y) := fun hcon =>
      absurd (h2 y hcon) (by rw [hy0]; exact lt_irrefl 0)
    rw [not_ne_iff, hy0] at hne
    have hneg : recessionFn f (-y) = 0 := by
      rw [← neg_neg (recessionFn f (-y)), hne, neg_zero]
    exact mem_constancySpace.2 ⟨hy, le_of_eq hneg⟩
  · intro H
    have h1 : ∀ y : E, (0 : EReal) ≤ recessionFn f y := by
      intro y
      rcases le_or_gt (recessionFn f y) 0 with hle | hlt
      · have hneg : recessionFn f (-y) ≤ ((-(0 : ℝ) : ℝ) : EReal) := by
          simpa using (mem_constancySpace.1 (H (mem_recessionConeFn.2 hle))).2
        simpa using le_recessionFn_of_neg_le hp hneg
      · exact hlt.le
    refine ⟨h1, fun y hy => ?_⟩
    rcases (h1 y).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hyrec : y ∈ recessionConeFn f := mem_recessionConeFn.2 (le_of_eq heq.symm)
      have hneg0 : recessionFn f (-y) = 0 :=
        le_antisymm (mem_constancySpace.1 (H hyrec)).2 (h1 (-y))
      exact hy (by rw [hneg0, ← heq, neg_zero])

/-- Let $E$ and $F$ be finite-dimensional real normed spaces, paired by $B$ such that the pairing
represents the continuous linear functionals on both spaces, and let $f$ be a closed proper
convex function on $E$. Then the minimum set of $f$ is nonempty and bounded if and only if the
origin is in the interior of $\operatorname{dom} f^*$. This is part of Theorem 27.1 of
[rockafellar1970convex].

Both directions go through the condition that $f$ has no direction of recession: a bounded
nonempty level set has the recession cone $\{0\}$, and this condition gives a minimizer. -/
theorem argmin_nonempty_and_isBounded_iff_zero_mem_interior_convexDom_convexConj (hf : ConvexFn f)
    (hc : ClosedConvex f) (hp : ProperConvex f) :
    ((argmin f).Nonempty ∧ Bornology.IsBounded (argmin f))
      ↔ (0 : F) ∈ interior (convexDom (convexConj B f)) := by
  rw [zero_mem_interior_convexDom_convexConj_iff_recessionConeFn_eq_zero (B := B) hf hc hp]
  have hlsc : LowerSemicontinuous f := (closedConvex_iff_lowerSemicontinuous hp.ne_bot).1 hc
  constructor
  · rintro ⟨⟨a, ha⟩, hbd⟩
    obtain ⟨x₀, hx₀⟩ := hp.convexDom_nonempty
    obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
      (lt_of_le_of_lt (ha x₀) (mem_convexDom.1 hx₀))
    have hset : argmin f = {z : E | f z ≤ (μ : EReal)} := argmin_eq_setOf_le ha hμ
    have hne : {z : E | f z ≤ (μ : EReal)}.Nonempty := ⟨a, le_of_eq hμ⟩
    have hbd' : Bornology.IsBounded {z : E | f z ≤ (μ : EReal)} := by rw [← hset]; exact hbd
    have hrec := (isBounded_iff_recessionCone_eq_zero (hf.convex_le _)
      (lowerSemicontinuous_iff_isClosed_le.1 hlsc μ) hne).1 hbd'
    rwa [recessionCone_setOf_le hf (lowerSemicontinuous_iff_isClosed_epi.1 hlsc) hne] at hrec
  · intro hrec
    exact ⟨argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec,
      (isCompact_argmin_of_recessionConeFn_eq_zero hf hc hp hrec).isBounded⟩

/-- Under the hypotheses of
`ConvexAnalysis.argmin_nonempty_and_isBounded_iff_zero_mem_interior_convexDom_convexConj`, some
level set $\{x \mid f(x) \le \alpha\}$ with $\alpha$ real is nonempty and bounded if and only if
the origin is in the interior of $\operatorname{dom} f^*$.

"Some level set" is as good as "every nonempty level set" here, since all nonempty level sets
have the recession cone of $f$. -/
theorem exists_setOf_le_nonempty_and_isBounded_iff_zero_mem_interior_convexDom_convexConj
    (hf : ConvexFn f)
    (hc : ClosedConvex f) (hp : ProperConvex f) :
    (∃ α : ℝ, {x : E | f x ≤ (α : EReal)}.Nonempty ∧
        Bornology.IsBounded {x : E | f x ≤ (α : EReal)})
      ↔ (0 : F) ∈ interior (convexDom (convexConj B f)) := by
  rw [zero_mem_interior_convexDom_convexConj_iff_recessionConeFn_eq_zero (B := B) hf hc hp]
  have hlsc : LowerSemicontinuous f := (closedConvex_iff_lowerSemicontinuous hp.ne_bot).1 hc
  constructor
  · rintro ⟨α, hne, hbd⟩
    have hrec := (isBounded_iff_recessionCone_eq_zero (hf.convex_le _)
      (lowerSemicontinuous_iff_isClosed_le.1 hlsc α) hne).1 hbd
    rwa [recessionCone_setOf_le hf (lowerSemicontinuous_iff_isClosed_epi.1 hlsc) hne] at hrec
  · intro hrec
    obtain ⟨a, ha⟩ := argmin_nonempty_of_recessionConeFn_eq_zero hf hc hp hrec
    obtain ⟨x₀, hx₀⟩ := hp.convexDom_nonempty
    obtain ⟨μ, hμ⟩ := EReal.exists_coe_of_ne_bot_of_lt_top (hp.ne_bot a)
      (lt_of_le_of_lt (ha x₀) (mem_convexDom.1 hx₀))
    refine ⟨μ, ⟨a, le_of_eq hμ⟩, ?_⟩
    rw [← argmin_eq_setOf_le ha hμ]
    exact (isCompact_argmin_of_recessionConeFn_eq_zero hf hc hp hrec).isBounded

include B in
/-- Let $E$ be a finite-dimensional real normed space paired with a finite-dimensional real normed
space $F$ such that the pairing represents the continuous linear functionals on both spaces, and
let $f$ be a closed proper convex function on $E$. Then the minimum set of $f$ is nonempty and
bounded if and only if some level set $\{x \mid f(x) \le \alpha\}$ with $\alpha$ real is
nonempty and bounded.

Both conditions say that $0 \in \operatorname{int}(\operatorname{dom} f^*)$. The result applies
to the objective function of a convex program. -/
theorem argmin_nonempty_and_isBounded_iff_exists_setOf_le (hf : ConvexFn f) (hc : ClosedConvex f)
    (hp : ProperConvex f) :
    ((argmin f).Nonempty ∧ Bornology.IsBounded (argmin f))
      ↔ ∃ α : ℝ, {x : E | f x ≤ (α : EReal)}.Nonempty ∧
          Bornology.IsBounded {x : E | f x ≤ (α : EReal)} :=
  (argmin_nonempty_and_isBounded_iff_zero_mem_interior_convexDom_convexConj (B := B) hf hc hp).trans
    (exists_setOf_le_nonempty_and_isBounded_iff_zero_mem_interior_convexDom_convexConj (B := B) hf
        hc hp).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsCompatiblePairing B]
  [IsCompatiblePairing B.flip] in
/-- Raising the conjugate by a real constant lowers the biconjugate by the same constant: the
conjugate of $y \mapsto f^*(y) + \alpha$ is $x \mapsto f^{**}(x) - \alpha$.

This is `ConvexAnalysis.convexConj_add_const` for the flipped pairing. -/
theorem convexConj_flip_convexConj_add_coe (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (α : ℝ) (x : E) :
    convexConj B.flip (fun y => convexConj B f y + (α : EReal)) x = convexBiconj B f x -
        (α : EReal) :=
  convexConj_add_const B.flip (convexConj B f) α x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Let $E$ and $F$ be real normed spaces, paired by $B$ such that the pairing represents the
continuous linear functionals on both spaces, and let $f$ be a closed convex function on $E$.
Then for each real $\alpha$, the support function of the level set $\{x \mid f(x) \le \alpha\}$
is the closure of the positively homogeneous convex function $k_\alpha$ generated by
$f^* + \alpha$:
$$\delta^*(\cdot \mid \{x \mid f(x) \le \alpha\}) = \operatorname{cl} k_\alpha.$$
This is part of Theorem 27.1 of [rockafellar1970convex].

The positively homogeneous function generated by a function is `ConvexAnalysis.posHomGen`. -/
theorem supportFn_setOf_le (hf : ConvexFn f) (hc : ClosedConvex f) (α : ℝ) :
    supportFn B {x : E | f x ≤ (α : EReal)}
      = convexCl (posHomGen fun y => convexConj B f y + (α : EReal)) := by
  rw [convexCl_posHomGen (B := B) fun y => convexConj B f y + (α : EReal)]
  congr 1
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, convexConj_flip_convexConj_add_coe,
    show convexBiconj B f x = f x from congrFun (convexBiconj_eq_self hf hc) x,
    EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot α))
      (.inl (EReal.coe_ne_top α)), zero_add]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Under the hypotheses of `ConvexAnalysis.supportFn_setOf_le`, let $f$ be proper and bounded
below, $f^*(0) \neq +\infty$. Then the support function of the minimum set of $f$ is the closure
of the directional derivative of $f^*$ at the origin:
$$\delta^*(\cdot \mid \operatorname{argmin} f) = \operatorname{cl} \bigl(f^{*\prime}(0;
  \cdot)\bigr).$$
This is part of Theorem 27.1 of [rockafellar1970convex]. -/
theorem supportFn_argmin (hf : ConvexFn f) (hc : ClosedConvex f) (hp : ProperConvex f)
    (hbdd : convexConj B f 0 ≠ ⊤) :
    supportFn B (argmin f) = convexCl (dirDeriv (convexConj B f) 0) := by
  rw [argmin_eq_subdifferential_convexConj_zero (B := B) hf hc,
    convexCl_dirDeriv (B := B.flip) (convexFn_convexConj B f)
        hbdd (convexConj_ne_bot hp.convexDom_nonempty 0),
    LinearMap.flip_flip]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsCompatiblePairing B.flip] in
/-- Let $E$ and $F$ be real normed spaces paired by $B$ such that every continuous linear functional
on $E$ has the form $\langle \cdot, y \rangle$, and let $f$ be a closed proper convex function
on $E$ whose infimum is a real number $\mu$. Then for every real $\varepsilon$, the
$\varepsilon$-subdifferential of $f^*$ at the origin is a level set of $f$:
$$\partial_\varepsilon f^*(0) = \{z \mid f(z) \le \mu + \varepsilon\}.$$

This follows from the Fenchel–Moreau theorem and $f^*(0) = -\inf f$. The condition
$z \in \partial_\varepsilon f^*(0)$ says that $\langle z, y \rangle - f^*(y) \le \inf f +
\varepsilon$ for every $y$, and the supremum of the left side over $y$ is $f^{**}(z) = f(z)$. -/
theorem epsSubdifferential_convexConj_zero (hf : ConvexFn f) (hc : ClosedConvex f)
    (hp : ProperConvex f)
    {μ : ℝ} (hμ : (⨅ x, f x) = (μ : EReal)) (ε : ℝ) :
    epsSubdifferential B.flip ε (convexConj B f) 0 = {z : E | f z ≤ ((μ + ε : ℝ) : EReal)} := by
  have hc0 : convexConj B f 0 = ((-μ : ℝ) : EReal) := by
    rw [convexConj_apply_zero, hμ, EReal.coe_neg]
  ext z
  rw [mem_epsSubdifferential, Set.mem_ofPred_eq]
  have hstep : ∀ y : F, (convexConj B f 0 + ((B.flip (y - 0) z : ℝ) : EReal)
        ≤ convexConj B f y + (ε : EReal))
      ↔ (((B.flip y z : ℝ) : EReal) - convexConj B f y ≤ ((μ + ε : ℝ) : EReal)) := fun y => by
    rw [sub_zero, hc0, coe_add_le_add_coe_iff,
      EReal.sub_le_iff_le_add (.inl (convexConj_ne_bot hp.convexDom_nonempty y))
        (.inr (EReal.coe_ne_bot _)),
      add_comm (((μ + ε : ℝ) : EReal)) (convexConj B f y), show ε - -μ = μ + ε from by ring]
  simp only [hstep]
  have hbi : (⨆ y : F, ((B.flip y z : ℝ) : EReal) - convexConj B f y) = f z := by
    rw [← convexConj_apply]
    exact congrFun (convexBiconj_eq_self hf hc) z
  rw [← iSup_le_iff, hbi]

omit [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space and $F$ a finite-dimensional real normed space, paired by $B$
such that the pairing represents the continuous linear functionals on both spaces, and let $f$
be a closed proper convex function on $E$ whose infimum is a real number $\mu$. Then for every
$y \in F$,
$$\inf_{\varepsilon > 0} \delta^*(y \mid \{z \mid f(z) \le \mu + \varepsilon\}) = f^{*\prime}(0;
  y).$$
So as the level decreases to the infimum, the support functions of the level sets converge to
the directional derivative of $f^*$ at the origin. This is part of Theorem 27.1 of
[rockafellar1970convex].

The $\varepsilon$-subdifferentials of $f^*$ at the origin are these level sets
(`ConvexAnalysis.epsSubdifferential_convexConj_zero`). The limit is an infimum because
$\varepsilon \mapsto \partial_\varepsilon f^*(0)$ is monotone. -/
theorem iInf_supportFn_setOf_le (hf : ConvexFn f) (hc : ClosedConvex f) (hp : ProperConvex f)
    {μ : ℝ} (hμ : (⨅ x, f x) = (μ : EReal)) (y : F) :
    (⨅ ε ∈ Set.Ioi (0 : ℝ), supportFn B {z : E | f z ≤ ((μ + ε : ℝ) : EReal)} y)
      = dirDeriv (convexConj B f) 0 y := by
  have hcp : ProperConvex (convexConj B f) := properConvex_convexConj ⟨hf, hc, hp⟩
  have hc0 : convexConj B f 0 = ((-μ : ℝ) : EReal) := by
    rw [convexConj_apply_zero, hμ, EReal.coe_neg]
  have hepi : IsClosed (epi (convexConj B f)) :=
    ClosedProperConvexFn.isClosed_epi ⟨convexFn_convexConj B f, closedConvex_convexConj, hcp⟩
  rw [← dirDeriv_eq_iInf_supportFn_epsSubdifferential
      (B := B.flip) (convexFn_convexConj B f) hcp hepi
    hc0 y]
  refine iInf_congr fun ε => iInf_congr fun hε => ?_
  rw [epsSubdifferential_convexConj_zero hf hc hp hμ ε, LinearMap.flip_flip]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The infimum of a proper function is never $+\infty$, since the function is less than $+\infty$
at some point.

With `ConvexAnalysis.convexConj_ne_bot`, this is why finiteness needs only one inequality on
each side in `ConvexAnalysis.iInf_ne_bot_and_argmin_eq_empty_iff`. -/
theorem iInf_ne_top (hp : ProperConvex f) : (⨅ x, f x) ≠ ⊤ := by
  obtain ⟨x₀, hx₀⟩ := hp.convexDom_nonempty
  exact (lt_of_le_of_lt (iInf_le _ x₀) (mem_convexDom.1 hx₀)).ne

omit [FiniteDimensional ℝ E] in
/-- Let $E$ be a real normed space and $F$ a finite-dimensional real normed space, paired by $B$
such that the pairing represents the continuous linear functionals on both spaces, and let $f$
be a closed proper convex function on $E$. Then the infimum of $f$ is finite but not attained if
and only if $f^*(0)$ is finite and $f^{*\prime}(0; y) = -\infty$ for some $y$:
$$\bigl(\inf f \neq -\infty \text{ and } \operatorname{argmin} f = \emptyset\bigr) \iff
  \bigl(f^*(0) \neq +\infty \text{ and } f^{*\prime}(0; y) = -\infty \text{ for some }
  y\bigr).$$
This is part of Theorem 27.1 of [rockafellar1970convex].

Only one bound appears on each side, because $f^*(0) \neq -\infty$ and $\inf f \neq +\infty$
hold for every proper $f$. -/
theorem iInf_ne_bot_and_argmin_eq_empty_iff (hf : ConvexFn f) (hc : ClosedConvex f)
    (hp : ProperConvex f) :
    ((⨅ x, f x) ≠ ⊥ ∧ argmin f = ∅)
      ↔ (convexConj B f 0 ≠ ⊤ ∧ ∃ y : F, dirDeriv (convexConj B f) 0 y = ⊥) := by
  have hb : convexConj B f 0 ≠ ⊥ := convexConj_ne_bot hp.convexDom_nonempty 0
  have hiff : (⨅ x, f x) ≠ ⊥ ↔ convexConj B f 0 ≠ ⊤ := by
    rw [convexConj_apply_zero, ne_eq, ne_eq, EReal.neg_eq_top_iff]
  rw [hiff, and_congr_right_iff]
  intro ht
  rw [argmin_eq_subdifferential_convexConj_zero (B := B) hf hc,
    subdifferential_eq_empty_iff_exists_dirDeriv_eq_bot (B := B.flip)
        (convexFn_convexConj B f) ht hb]

end ConjugateAtZero

/-!
### A unique minimizer is a gradient of the conjugate

The minimum set is $\partial f^*(0)$, and a subdifferential is a single point exactly at a point of
differentiability. The results below combine the two. No reflexivity is needed: the subdifferential
is that of $f^*$ with respect to the flipped pairing, a subset of $E$.
-/

section UniqueMinimiser

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] [IsCompatiblePairing B.flip] {f : E → EReal}
  {x : E}

/-- **Necessity.** Let $E$ be a real normed space and $F$ a finite-dimensional real normed space,
paired by $B$ such that the pairing represents the continuous linear functionals on both spaces,
and let $f$ be a closed proper convex function on $E$. If the minimum set of $f$ is the single
point $x$, then $f^*$ is differentiable at the origin with gradient $\langle x, \cdot \rangle$:
$$\nabla f^*(0) = \langle x, \cdot \rangle.$$

The finite dimension is that of $F$, the space on which $f^*$ is defined, not that of $E$. The
gradient is in the sense of `ConvexAnalysis.HasGradientAtFn`, with the functional
`ConvexAnalysis.evalCLM B.flip x`. -/
theorem hasGradientAtFn_convexConj_zero_of_argmin_eq_singleton (hf : ConvexFn f)
    (hc : ClosedConvex f)
    (hp : ProperConvex f) (h : argmin f = {x}) :
    HasGradientAtFn (convexConj B f) (evalCLM B.flip x) 0 :=
  hasGradientAtFn_evalCLM_of_subdifferential_eq_singleton (B := B.flip) (convexFn_convexConj B f)
    (properConvex_convexConj ⟨hf, hc, hp⟩)
    (by rw [← argmin_eq_subdifferential_convexConj_zero (B := B) hf hc]; exact h)

omit [FiniteDimensional ℝ F] in
/-- **Sufficiency.** Let $E$ and $F$ be real normed spaces, paired by $B$ such that the pairing
represents the continuous linear functionals on both spaces, and let $f$ be a closed convex
function on $E$. If $f^*$ is differentiable at the origin with gradient
$\nabla f^*(0) = \langle x, \cdot \rangle$, then $x$ is the unique minimizer of $f$: the minimum
set of $f$ is $\{x\}$.

Properness of $f$ is not needed: differentiability of $f^*$ at the origin forces $f^*$ to be
proper, hence $f^*(0)$ finite, and this is all that the uniqueness argument uses. The argument
needs the pairing to separate points of $E$, which follows from the hypothesis on the pairing.
This is necessary: if $\langle x, \cdot \rangle = 0$ for some $x \neq 0$, then every level set
of $f = f^{**}$ is invariant under translation by $x$, and no minimum set is a single point.
Finite dimension of $F$ is not used here. -/
theorem argmin_eq_singleton_of_hasGradientAtFn_convexConj_zero (hf : ConvexFn f)
    (hc : ClosedConvex f)
    (h : HasGradientAtFn (convexConj B f) (evalCLM B.flip x) 0) : argmin f = {x} := by
  have hcf : ConvexFn (convexConj B f) := convexFn_convexConj B f
  have hprop : ProperConvex (convexConj B f) := HasGradientAtFn.proper hcf h
  rw [argmin_eq_subdifferential_convexConj_zero (B := B) hf hc]
  refine subdifferential_eq_singleton_of_dirDeriv_eq (B := B.flip)
    (injective_of_separatingDual B)
    ((mem_convexDom.1 (interior_subset (HasGradientAtFn.mem_interior_convexDom h))).ne)
        (hprop.ne_bot 0)
    fun v => ?_
  rw [HasGradientAtFn.dirDeriv_eq hcf h v]
  rfl

/-- Let $E$ be a real normed space and $F$ a finite-dimensional real normed space, paired by $B$
such that the pairing represents the continuous linear functionals on both spaces, and let $f$
be a closed proper convex function on $E$. Then the minimum set of $f$ is the single point $x$
if and only if $f^*$ is differentiable at the origin with gradient
$$\nabla f^*(0) = \langle x, \cdot \rangle.$$
This is part of Theorem 27.1 of [rockafellar1970convex]. -/
theorem argmin_eq_singleton_iff_hasGradientAtFn_convexConj_zero (hf : ConvexFn f)
    (hc : ClosedConvex f)
    (hp : ProperConvex f) : argmin f = {x}
        ↔ HasGradientAtFn (convexConj B f) (evalCLM B.flip x) 0 :=
  ⟨hasGradientAtFn_convexConj_zero_of_argmin_eq_singleton hf hc hp,
    argmin_eq_singleton_of_hasGradientAtFn_convexConj_zero hf hc⟩

/-- Under the hypotheses of
`ConvexAnalysis.argmin_eq_singleton_iff_hasGradientAtFn_convexConj_zero`, the infimum of $f$ is
attained at exactly one point if and only if $f^*$ is differentiable at the origin.

The step from the functional $\nabla f^*(0)$ to the vector $x \in E$ that represents it uses
that every continuous linear functional on $F$ has the form $\langle x, \cdot \rangle$. -/
theorem exists_argmin_eq_singleton_iff_differentiableAtFn_convexConj_zero (hf : ConvexFn f)
    (hc : ClosedConvex f) (hp : ProperConvex f) :
    (∃ x : E, argmin f = {x}) ↔ DifferentiableAtFn (convexConj B f) 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, hasGradientAtFn_convexConj_zero_of_argmin_eq_singleton hf hc hp hx⟩
  · rintro ⟨g, hg⟩
    obtain ⟨x, hx⟩ := IsCompatiblePairing.surjective_eval B.flip g
    exact ⟨x, argmin_eq_singleton_of_hasGradientAtFn_convexConj_zero hf hc (by rw [hx]; exact hg)⟩

end UniqueMinimiser

end ConvexAnalysis
