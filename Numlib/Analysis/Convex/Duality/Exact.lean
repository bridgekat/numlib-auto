/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Operations.InfConv
import Numlib.Analysis.Convex.Operations.Image

/-!
# Exact duality for sums and inverse images

Many duality results of convex analysis have the following form: if
$\operatorname{ri}(\operatorname{dom} f_1) \cap \dots \cap \operatorname{ri}(\operatorname{dom} f_m)
\ne \emptyset$, then a closure operation can be omitted, and the infimum that defines the dual
operation is attained. Examples are the conjugates of sums, of inverse images and of suprema, the
rules of subdifferential calculus, and the duality theorems of convex programming; see
[rockafellar1970convex], §16, §20, §23 and §31. The relative interior condition is one sufficient
condition among several. Others are polyhedral conditions, a continuity condition valid in every
topological vector space, and the Attouch–Brezis conditions in Banach spaces.

This module names the conclusion. Let $E$ and $F$ be real vector spaces paired by
$\langle x, y \rangle$. Two proper functions $f, g : E \to [-\infty, +\infty]$ **add exactly** if,
for every $y \in F$, the infimal convolution $(f^* \mathbin{\square} g^*)(y) = \inf_{y_1 + y_2 = y}
(f^*(y_1) + g^*(y_2))$ is attained and equals $(f + g)^*(y)$. A proper function $g$ **pulls back
exactly** along a linear map $A$ with transpose $A'$ if $(gA)^* = A' g^*$, with the infimum
$(A' g^*)(y) = \inf \{g^*(z) : A'z = y\}$ attained. The inequalities
$(f + g)^* \le f^* \mathbin{\square} g^*$ and $(gA)^* \le A' g^*$ hold with no hypothesis. The
sufficient conditions are proved in the modules that own their hypotheses:
`ConvexAnalysis.IsExactSum.of_relint` in `Numlib.Analysis.Convex.Duality.Relint`,
`ConvexAnalysis.IsExactSum.of_polyhedral` in `Numlib.Analysis.Convex.Polyhedral.Duality`, and
`ConvexAnalysis.IsExactSum.of_continuousAt` in `Numlib.Analysis.Convex.Duality.Continuity`.

## Main definitions

* `ConvexAnalysis.IsExactSum`: $f$ and $g$ add exactly: both are proper, and the infimal convolution
  that gives $(f + g)^*$ is attained.
* `ConvexAnalysis.IsExactFinsetSum`: the same for a finite family $(f_i)_{i \in s}$, the form that
  the $m$-ary results need.
* `ConvexAnalysis.IsExactImage`: $g$ pulls back exactly along $A$: $g$ is proper, and the infimum
  over the fibres of the transpose $A'$ that gives $(gA)^*$ is attained.

## Main results

* `ConvexAnalysis.convexConj_add_le_infConv`: $(f + g)^* \le f^* \mathbin{\square} g^*$, with no
  hypothesis.
* `ConvexAnalysis.convexConj_finsetSum_le_sum_toInfConvFn`: $(f_1 + \dots + f_m)^* \le f_1^*
  \mathbin{\square} \cdots \mathbin{\square} f_m^*$, with no hypothesis.
* `ConvexAnalysis.convexConj_compLin_le_mapLin`: $(gA)^* \le A' g^*$, with no hypothesis.
* `ConvexAnalysis.IsExactSum.convexConj_add`, `ConvexAnalysis.IsExactSum.exists_convexConj_add_eq`:
  if $f$ and $g$ add exactly, then $(f + g)^* = f^* \mathbin{\square} g^*$ and the infimal
  convolution is attained, as in Theorem 16.4 of [rockafellar1970convex].
* `ConvexAnalysis.IsExactFinsetSum.convexConj_finsetSum`: the same for a finite family.
* `ConvexAnalysis.IsExactImage.convexConj_compLin`,
  `ConvexAnalysis.IsExactImage.exists_convexConj_compLin_eq`: if $g$ pulls back exactly along $A$,
  then $(gA)^* = A' g^*$ and the infimum over the fibre is attained, as in Theorem 16.3 of
  [rockafellar1970convex].
* `ConvexAnalysis.IsExactFinsetSum.singleton`, `ConvexAnalysis.IsExactFinsetSum.cons`,
  `ConvexAnalysis.IsExactFinsetSum.of_split`: the family interface built from binary ones, which is
  how every $m$-ary constraint qualification is proved.
* `ConvexAnalysis.IsExactSum.properConvex_add`,
  `ConvexAnalysis.IsExactFinsetSum.properConvex_finsetSum`,
  `ConvexAnalysis.IsExactImage.properConvex_compLin`: the interfaces cannot hold when the effective
  domains do not meet.

## Implementation notes

* The equality of the conjugates is a theorem, not a field of the structures. The inequality
  $(f + g)^* \le f^* \mathbin{\square} g^*$ holds for all $f$ and $g$, and an interface that states
  the equality would be unsatisfiable in a case that looks harmless: when $\operatorname{dom} f \cap
  \operatorname{dom} g = \emptyset$, the conjugate $(f + g)^*$ is the constant $-\infty$, while the
  conjugate of a proper function never takes the value $-\infty$. The interface carries the
  attainment, in the field `exact_le`.
* The field `ConvexAnalysis.IsExactImage.exact_le` asks for a point of the fibre $\{z : A'z = y\}$
  only where $(gA)^*(y) < +\infty$. Without this condition the interface is unsatisfiable whenever
  $A'$ is not surjective: at a $y$ outside the range of $A'$ there is no point to give, while both
  sides of the identity are $+\infty$ there.
* The family interface is not an iterated binary one. The operation $\square$ does not preserve the
  property of never taking the value $-\infty$, so the binary bound cannot be iterated; what
  iterates is the construction `ConvexAnalysis.IsExactFinsetSum.cons`. The field `exact_le` asks for
  a splitting of every $y$, so the empty family adds exactly only if $F$ is trivial, just as two
  functions with disjoint effective domains do not add exactly.
* The sum $f + g$ is the pointwise sum in `EReal`, in which $(+\infty) + (-\infty) = -\infty$. No
  convexity is part of the interfaces.
-/

open Pointwise

namespace ConvexAnalysis

/-! ### Sums: the unconditional half -/

section Sum

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal} {y₁ y₂ : F} {c₁ c₂ : ℝ}

/-- Let $y_1, y_2 \in F$ and $c_1, c_2 \in \mathbb{R}$ with $f^*(y_1) \le c_1$ and
$g^*(y_2) \le c_2$. Then $$(f + g)^*(y_1 + y_2) \le c_1 + c_2.$$ Read through
`ConvexAnalysis.convexConj_le_coe_iff`, this says that an affine minorant of $f$ and one of $g$
add to an affine minorant of $f + g$. This is the whole unconditional content of the identity
for the conjugate of a sum. -/
theorem convexConj_add_le_coe_add (h₁ : convexConj B f y₁ ≤ (c₁ : EReal))
    (h₂ : convexConj B g y₂ ≤ (c₂ : EReal)) :
    convexConj B (f + g) (y₁ + y₂) ≤ ((c₁ + c₂ : ℝ) : EReal) := by
  rw [convexConj_le_coe_iff] at h₁ h₂ ⊢
  intro x
  have hsplit : affineFn B (y₁ + y₂) (c₁ + c₂) x
      = affineFn B y₁ c₁ x + affineFn B y₂ c₂ x := by
    rw [affineFn_eq_coe, affineFn_eq_coe, affineFn_eq_coe, ← EReal.coe_add]
    congr 1
    rw [map_add]
    ring
  rw [hsplit, Pi.add_apply]
  exact add_le_add (h₁ x) (h₂ x)

/-- For all $f, g : E \to [-\infty, +\infty]$, the Minkowski sum of the epigraphs of $f^*$ and $g^*$
is contained in the epigraph of $(f + g)^*$. -/
theorem epi_convexConj_add_epi_convexConj_subset (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) :
    epi (convexConj B f) + epi (convexConj B g) ⊆ epi (convexConj B (f + g)) := by
  rintro _ ⟨⟨y₁, c₁⟩, h₁, ⟨y₂, c₂⟩, h₂, rfl⟩
  rw [mk_mem_epi] at h₁ h₂
  simpa using convexConj_add_le_coe_add h₁ h₂

/-- **The conjugate of a sum is at most the infimal convolution of the conjugates.** For all
$f, g : E \to [-\infty, +\infty]$, $$(f + g)^* \le f^* \mathbin{\square} g^*.$$ No hypothesis is
needed.

The infimal convolution `ConvexAnalysis.infConv` is defined by addition of epigraphs. For
functions that never take the value $-\infty$ it is $(\varphi \mathbin{\square} \psi)(y) =
\inf_{y'} (\varphi(y - y') + \psi(y'))$. The reverse inequality is what
`ConvexAnalysis.IsExactSum` asks for, and what every constraint qualification supplies. -/
theorem convexConj_add_le_infConv (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) :
    convexConj B (f + g) ≤ infConv (convexConj B f) (convexConj B g) := by
  rw [infConv_def]
  exact subset_epi_iff_le_ofEpi.1 (epi_convexConj_add_epi_convexConj_subset B f g)

/-- Let $f$ and $g$ have nonempty effective domains. Then for all $y_1, y_2 \in F$, $$(f +
g)^*(y_1 + y_2) \le f^*(y_1) + g^*(y_2).$$ This pointwise form of
`ConvexAnalysis.convexConj_add_le_infConv` needs the hypothesis: if $f$ is the constant
$+\infty$ and $g$ takes the value $-\infty$ somewhere, then $(f + g)^*$ is the constant
$+\infty$, while $f^*(y_1) + g^*(y_2) = (-\infty) + (+\infty) = -\infty$. -/
theorem convexConj_add_le_add_convexConj (hf : (convexDom f).Nonempty) (hg : (convexDom g).Nonempty)
    (y₁ y₂ : F) :
    convexConj B (f + g) (y₁ + y₂) ≤ convexConj B f y₁ + convexConj B g y₂ := by
  rcases eq_or_ne (convexConj B f y₁) ⊤ with h₁ | h₁
  · rw [h₁, EReal.top_add_of_ne_bot (convexConj_ne_bot hg y₂)]
    exact le_top
  rcases eq_or_ne (convexConj B g y₂) ⊤ with h₂ | h₂
  · rw [h₂, EReal.add_top_of_ne_bot (convexConj_ne_bot hf y₁)]
    exact le_top
  obtain ⟨c₁, hc₁⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (convexConj_ne_bot hf y₁) (lt_top_iff_ne_top.2 h₁)
  obtain ⟨c₂, hc₂⟩ :=
    EReal.exists_coe_of_ne_bot_of_lt_top (convexConj_ne_bot hg y₂) (lt_top_iff_ne_top.2 h₂)
  rw [hc₁, hc₂, ← EReal.coe_add]
  exact convexConj_add_le_coe_add hc₁.le hc₂.le

end Sum

/-! ### Sums: the interface -/

section SumInterface

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- Two functions $f, g : E \to [-\infty, +\infty]$ **add exactly** with respect to the pairing if
both are proper and for every $y \in F$ there is a splitting $y = y_1 + y_2$ with $$f^*(y_1) +
g^*(y_2) \le (f + g)^*(y).$$ Then $(f + g)^* = f^* \mathbin{\square} g^*$, and the infimal
convolution is attained at every point (`ConvexAnalysis.IsExactSum.convexConj_add`,
`ConvexAnalysis.IsExactSum.exists_convexConj_add_eq`).

This is the conclusion that the relative interior, polyhedral and continuity conditions deliver.
Convexity is not part of the definition. -/
structure IsExactSum (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) : Prop where
  /-- The function $f$ is proper. -/
  properConvex_left : ProperConvex f
  /-- The function $g$ is proper. -/
  properConvex_right : ProperConvex g
  /-- For every $y \in F$ there are $y_1, y_2 \in F$ with $y_1 + y_2 = y$ and
  $f^*(y_1) + g^*(y_2) \le (f + g)^*(y)$. The reverse inequality is unconditional
  (`ConvexAnalysis.convexConj_add_le_infConv`), so this field is the whole content. -/
  exact_le : ∀ y : F, ∃ y₁ y₂ : F, y₁ + y₂ = y ∧
    convexConj B f y₁ + convexConj B g y₂ ≤ convexConj B (f + g) y

namespace IsExactSum

variable (h : IsExactSum B f g)
include h

/-- If $f$ and $g$ add exactly, then $f^*(y) \ne -\infty$ for every $y \in F$. -/
theorem convexConj_left_ne_bot (y : F) : convexConj B f y ≠ ⊥ :=
    convexConj_ne_bot h.properConvex_left.convexDom_nonempty y

/-- If $f$ and $g$ add exactly, then $g^*(y) \ne -\infty$ for every $y \in F$. -/
theorem convexConj_right_ne_bot (y : F) : convexConj B g y ≠ ⊥ :=
    convexConj_ne_bot h.properConvex_right.convexDom_nonempty y

/-- If $f$ and $g$ add exactly, then $g$ and $f$ add exactly. -/
theorem symm : IsExactSum B g f where
  properConvex_left := h.properConvex_right
  properConvex_right := h.properConvex_left
  exact_le y := by
    obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
    refine ⟨y₂, y₁, by rw [add_comm]; exact hy, ?_⟩
    rw [add_comm g f, add_comm (convexConj B g y₂)]
    exact hle

/-- **Exactly adding functions have meeting effective domains.** If $f$ and $g$ add exactly, then
$f + g$ is proper. In particular $\operatorname{dom} f \cap \operatorname{dom} g \ne \emptyset$,
so the interface cannot hold for functions with disjoint effective domains. -/
theorem properConvex_add : ProperConvex (f + g) := by
  have hb : convexConj B (f + g) 0 ≠ ⊥ := by
    obtain ⟨y₁, y₂, -, hle⟩ := h.exact_le 0
    intro hc
    rw [hc, le_bot_iff, EReal.add_eq_bot_iff] at hle
    exact hle.elim (h.convexConj_left_ne_bot y₁) (h.convexConj_right_ne_bot y₂)
  refine ⟨?_, fun x hx => ?_⟩
  · by_contra hd
    rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
    exact hb (convexConj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x)))
  · rw [Pi.add_apply, EReal.add_eq_bot_iff] at hx
    exact hx.elim (h.properConvex_left.ne_bot x) (h.properConvex_right.ne_bot x)

/-- If $f$ and $g$ add exactly, then $f^* \mathbin{\square} g^* \le (f + g)^*$. -/
theorem infConv_le_convexConj_add : infConv (convexConj B f) (convexConj B g)
    ≤ convexConj B (f + g) := by
  intro y
  obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
  refine le_trans ?_ hle
  subst hy
  simpa using infConv_le_add h.convexConj_left_ne_bot h.convexConj_right_ne_bot (y₁ + y₂) y₂

/-- **The conjugate of a sum.** If $f, g : E \to [-\infty, +\infty]$ add exactly, then $$(f + g)^* =
f^* \mathbin{\square} g^*.$$

This is the conclusion of Theorem 16.4 of [rockafellar1970convex]. There the hypothesis is a
relative interior condition, which implies exactness (`ConvexAnalysis.IsExactSum.of_relint`). -/
theorem convexConj_add : convexConj B (f + g) = infConv (convexConj B f) (convexConj B g) :=
  le_antisymm (convexConj_add_le_infConv B f g) h.infConv_le_convexConj_add

/-- If $f$ and $g$ add exactly, then for every $y \in F$, $$(f + g)^*(y) = \inf_{y' \in F}
\bigl(f^*(y - y') + g^*(y')\bigr).$$
-/
theorem convexConj_add_apply (y : F) :
    convexConj B (f + g) y = ⨅ y' : F, convexConj B f (y - y') + convexConj B g y' := by
  rw [h.convexConj_add]
  exact infConv_apply h.convexConj_left_ne_bot h.convexConj_right_ne_bot y

omit h in
/-- **The concave conjugate of a sum.** Let $g_1, g_2 : E \to [-\infty, +\infty]$ be such that
$-g_1$ and $-g_2$ add exactly. Then $$(g_1 + g_2)^* = g_1^* \mathbin{\square} g_2^*,$$ with the
concave conjugates and the supremal convolution.

This is the concave counterpart of `ConvexAnalysis.IsExactSum.convexConj_add`. The two
properness fields of the hypothesis say that each $g_i$ is finite somewhere and never takes the
value $+\infty$. The supremal convolution is `ConvexAnalysis.supConv`, defined as $\varphi
\mathbin{\square} \psi = -((-\varphi) \mathbin{\square} (-\psi))$; for functions that never take
the value $+\infty$ it is $(\varphi \mathbin{\square} \psi)(y) = \sup_{y_1 + y_2 = y}
(\varphi(y_1) + \psi(y_2))$. -/
theorem concaveConj_add {g₁ g₂ : E → EReal}
    (hex : IsExactSum B (fun x => -(g₁ x)) (fun x => -(g₂ x))) :
    concaveConj B (fun x => g₁ x + g₂ x) = supConv (concaveConj B g₁) (concaveConj B g₂) := by
  have hg₁ : ∀ x, g₁ x ≠ ⊤ := fun x hx => hex.properConvex_left.ne_bot x (by simp [hx])
  have hg₂ : ∀ x, g₂ x ≠ ⊤ := fun x hx => hex.properConvex_right.ne_bot x (by simp [hx])
  have hsum : (fun x => -(g₁ x + g₂ x)) = (fun x => -(g₁ x)) + (fun x => -(g₂ x)) :=
    funext fun x => (EReal.neg_add (.inr (hg₂ x)) (.inl (hg₁ x))).trans (sub_eq_add_neg _ _)
  funext v
  have step1 : concaveConj B (fun x => g₁ x + g₂ x) v
      = -(convexConj B ((fun x => -(g₁ x)) + (fun x => -(g₂ x))) (-v)) := by
    rw [← hsum]
    exact concaveConj_eq_neg_convexConj_neg B (fun x => g₁ x + g₂ x) v
  have step3 : infConv (convexConj B fun x => -(g₁ x)) (convexConj B fun x => -(g₂ x)) (-v)
      = infConv (fun w => -(concaveConj B g₁ w)) (fun w => -(concaveConj B g₂ w)) v := by
    have e₁ : (fun w => -(concaveConj B g₁ w)) = fun w => (convexConj B fun x => -(g₁ x)) (-w) :=
      funext fun w => neg_concaveConj B g₁ w
    have e₂ : (fun w => -(concaveConj B g₂ w)) = fun w => (convexConj B fun x => -(g₂ x)) (-w) :=
      funext fun w => neg_concaveConj B g₂ w
    rw [e₁, e₂]
    exact (infConv_comp_neg _ _ v).symm
  change concaveConj B (fun x => g₁ x + g₂ x) v
      = -(infConv (fun w => -(concaveConj B g₁ w)) (fun w => -(concaveConj B g₂ w)) v)
  rw [step1, hex.convexConj_add, step3]

/-- **The infimal convolution is attained.** If $f$ and $g$ add exactly, then for every $y \in F$
there are $y_1, y_2 \in F$ with $y_1 + y_2 = y$ and $$f^*(y_1) + g^*(y_2) = (f + g)^*(y).$$ This
is the half for which the constraint qualifications are needed. -/
theorem exists_convexConj_add_eq (y : F) :
    ∃ y₁ y₂ : F, y₁ + y₂ = y ∧ convexConj B f y₁ + convexConj B g y₂ = convexConj B (f + g) y := by
  obtain ⟨y₁, y₂, hy, hle⟩ := h.exact_le y
  refine ⟨y₁, y₂, hy, le_antisymm hle ?_⟩
  subst hy
  exact convexConj_add_le_add_convexConj h.properConvex_left.convexDom_nonempty
      h.properConvex_right.convexDom_nonempty y₁ y₂

end IsExactSum

end SumInterface

/-! ### Sums over a `Finset`: the unconditional half -/

section FinsetSum

variable {ι E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

omit [AddCommGroup E] [Module ℝ E] in
/-- Let $(f_i)_{i \in s}$ be a finite family of functions that never take the value $-\infty$. Then
$$\operatorname{dom} \sum_{i \in s} f_i = \bigcap_{i \in s} \operatorname{dom} f_i.$$
-/
theorem convexDom_finsetSum (hf : ∀ i ∈ s, ∀ x, f i x ≠ ⊥) :
    convexDom (∑ i ∈ s, f i) = ⋂ i ∈ s, convexDom (f i) := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty]
    ext x
    simp
  | cons i t hi ih =>
    have hbot : ∀ x, (∑ j ∈ t, f j) x ≠ ⊥ := fun x => by
      rw [Finset.sum_apply]
      exact EReal.sum_ne_bot fun j hj => hf j (by simp [hj]) x
    rw [Finset.sum_cons, convexDom_add (hf i (by simp)) hbot, ih fun j hj => hf j (by simp [hj])]
    ext x
    simp [Finset.mem_cons]

/-- Let $y_i \in F$ and $c_i \in \mathbb{R}$ with $f_i^*(y_i) \le c_i$ for all $i \in s$. Then
$$\Bigl(\sum_{i \in s} f_i\Bigr)^*\Bigl(\sum_{i \in s} y_i\Bigr) \le \sum_{i \in s} c_i.$$
-/
theorem convexConj_finsetSum_le_coe_sum {y : ι → F} {c : ι → ℝ}
    (h : ∀ i ∈ s, convexConj B (f i) (y i) ≤ (c i : EReal)) :
    convexConj B (∑ i ∈ s, f i) (∑ i ∈ s, y i) ≤ ((∑ i ∈ s, c i : ℝ) : EReal) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    rw [convexConj_le_coe_iff]
    intro x
    rw [affineFn_eq_coe]
    simp
  | cons i t hi ih =>
    simp only [Finset.sum_cons]
    exact convexConj_add_le_coe_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

/-- If every $f_i$ with $i \in s$ has nonempty effective domain, then for every family
$(y_i)_{i \in s}$ in $F$, $$\Bigl(\sum_{i \in s} f_i\Bigr)^*\Bigl(\sum_{i \in s} y_i\Bigr) \le
\sum_{i \in s} f_i^*(y_i).$$ The hypothesis keeps the right side from collapsing to $-\infty$
through a sum $(+\infty) + (-\infty)$. -/
theorem convexConj_finsetSum_le_sum_convexConj (hf : ∀ i ∈ s, (convexDom (f i)).Nonempty)
    (y : ι → F) :
    convexConj B (∑ i ∈ s, f i) (∑ i ∈ s, y i) ≤ ∑ i ∈ s, convexConj B (f i) (y i) := by
  rcases eq_or_ne (∑ i ∈ s, convexConj B (f i) (y i)) ⊤ with htop | htop
  · rw [htop]; exact le_top
  have hbot : ∀ i ∈ s, convexConj B (f i) (y i) ≠ ⊥ := fun i hi => convexConj_ne_bot (hf i hi) (y i)
  have hfin : ∀ i ∈ s, convexConj B (f i) (y i) ≠ ⊤ :=
    EReal.forall_ne_top_of_sum_ne_top s _ hbot htop
  have hci : ∀ i ∈ s,
      convexConj B (f i) (y i) = (((convexConj B (f i) (y i)).toReal : ℝ) : EReal) :=
    fun i hi => (EReal.coe_toReal (hfin i hi) (hbot i hi)).symm
  have hsum : ∑ i ∈ s, convexConj B (f i) (y i)
      = ((∑ i ∈ s, (convexConj B (f i) (y i)).toReal : ℝ) : EReal) := by
    rw [EReal.coe_sum]
    exact Finset.sum_congr rfl hci
  rw [hsum]
  exact convexConj_finsetSum_le_coe_sum fun i hi => (hci i hi).le

/-- **The conjugate of a finite sum is at most the infimal convolution of the conjugates.** For
every finite family $(f_i)_{i \in s}$ of functions $E \to [-\infty, +\infty]$, $$(f_1 + \dots +
f_m)^* \le f_1^* \mathbin{\square} \cdots \mathbin{\square} f_m^*.$$ No hypothesis is needed.
For the empty family the right side is the indicator function of $\{0\}$.

The $m$-fold infimal convolution is the sum in the commutative monoid
`ConvexAnalysis.InfConvFn F`, whose addition is $\square$ and whose zero is the indicator
function $\delta(\cdot \mid 0)$. No properness can be assumed at the intermediate stages, since
$\square$ does not preserve it; the induction uses `ConvexAnalysis.infConv_mono` and never the
infimum formula. -/
theorem convexConj_finsetSum_le_sum_toInfConvFn (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Finset ι)
    (f : ι → E → EReal) :
    convexConj B (∑ i ∈ s, f i) ≤ ofInfConvFn (∑ i ∈ s, toInfConvFn (convexConj B (f i))) := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty, ofInfConvFn_zero]
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · rw [indicatorFn_of_mem (s := ({0} : Set F)) (Set.mem_singleton_iff.2 rfl), convexConj_apply]
      refine iSup_le fun x => ?_
      simp
    · rw [indicatorFn_of_notMem (s := ({0} : Set F)) (by simpa using hy)]
      exact le_top
  | cons i t hi ih =>
    simp only [Finset.sum_cons, ofInfConvFn_add, ofInfConvFn_toInfConvFn]
    exact (convexConj_add_le_infConv B (f i) _).trans (infConv_mono le_rfl ih)

end FinsetSum

/-! ### Sums over a `Finset`: the interface -/

section FinsetSumInterface

variable {ι E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Finset ι} {f : ι → E → EReal}

/-- A finite family $(f_i)_{i \in s}$ of functions $E \to [-\infty, +\infty]$ **adds exactly** with
respect to the pairing if every $f_i$ is proper and for every $y \in F$ there is a family
$(y_i)_{i \in s}$ in $F$ with $\sum_{i \in s} y_i = y$ and $$\sum_{i \in s} f_i^*(y_i) \le
\Bigl(\sum_{i \in s} f_i\Bigr)^*(y).$$ Then $(f_1 + \dots + f_m)^* = f_1^* \mathbin{\square}
\cdots \mathbin{\square} f_m^*$, and the $m$-fold infimal convolution is attained at every
point.

`ConvexAnalysis.IsExactSum` is the case of two functions. Every consequence is proved once, for
the family. `ConvexAnalysis.IsExactFinsetSum.cons` and
`ConvexAnalysis.IsExactFinsetSum.of_split` build a family interface out of binary ones. The
empty family adds exactly only if $F$ is trivial. -/
structure IsExactFinsetSum (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (s : Finset ι) (f : ι → E → EReal) : Prop where
  /-- Every member $f_i$ with $i \in s$ is proper. -/
  proper : ∀ i ∈ s, ProperConvex (f i)
  /-- For every $y \in F$ there is a family $(y_i)_{i \in s}$ with $\sum_{i \in s} y_i = y$ and
  $\sum_{i \in s} f_i^*(y_i) \le (\sum_{i \in s} f_i)^*(y)$. The reverse inequality is
  unconditional (`ConvexAnalysis.convexConj_finsetSum_le_sum_toInfConvFn`), so this field is the
  whole content. -/
  exact_le : ∀ y : F, ∃ y' : ι → F, ∑ i ∈ s, y' i = y ∧
    ∑ i ∈ s, convexConj B (f i) (y' i) ≤ convexConj B (∑ i ∈ s, f i) y

namespace IsExactFinsetSum

variable (h : IsExactFinsetSum B s f)
include h

/-- If the family $(f_i)_{i \in s}$ adds exactly, then $\sum_{i \in s} f_i$ never takes the value
$-\infty$. -/
theorem finsetSum_ne_bot (x : E) : (∑ i ∈ s, f i) x ≠ ⊥ := by
  rw [Finset.sum_apply]
  exact EReal.sum_ne_bot fun i hi => (h.proper i hi).ne_bot x

/-- **Exactly adding families have meeting effective domains.** If the family $(f_i)_{i \in s}$ adds
exactly, then $\sum_{i \in s} f_i$ is proper. In particular the effective domains of the $f_i$
have a common point, as in the binary case `ConvexAnalysis.IsExactSum.properConvex_add`. -/
theorem properConvex_finsetSum : ProperConvex (∑ i ∈ s, f i) := by
  have hb : convexConj B (∑ i ∈ s, f i) 0 ≠ ⊥ := by
    obtain ⟨y', -, hle⟩ := h.exact_le 0
    intro hc
    rw [hc, le_bot_iff] at hle
    exact EReal.sum_ne_bot
      (fun i hi => convexConj_ne_bot (h.proper i hi).convexDom_nonempty (y' i)) hle
  refine ⟨?_, h.finsetSum_ne_bot⟩
  by_contra hd
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
  exact hb (convexConj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x)))

/-- If the family $(f_i)_{i \in s}$ adds exactly, then $f_1^* \mathbin{\square} \cdots
\mathbin{\square} f_m^* \le (f_1 + \dots + f_m)^*$. -/
theorem sum_toInfConvFn_le_convexConj_finsetSum :
    ofInfConvFn (∑ i ∈ s, toInfConvFn (convexConj B (f i))) ≤ convexConj B (∑ i ∈ s, f i) := by
  intro y
  obtain ⟨y', hy, hle⟩ := h.exact_le y
  refine le_trans ?_ hle
  rw [← hy]
  exact sum_toInfConvFn_le_sum
      (fun i hi x => convexConj_ne_bot (h.proper i hi).convexDom_nonempty x) y'

/-- **The conjugate of a finite sum.** If the family $(f_i)_{i \in s}$ adds exactly, then $$(f_1 +
\dots + f_m)^* = f_1^* \mathbin{\square} \cdots \mathbin{\square} f_m^*,$$ where the right side
is the sum in `ConvexAnalysis.InfConvFn F`. -/
theorem convexConj_finsetSum :
    convexConj B (∑ i ∈ s, f i) = ofInfConvFn (∑ i ∈ s, toInfConvFn (convexConj B (f i))) :=
  le_antisymm (convexConj_finsetSum_le_sum_toInfConvFn B s f)
      h.sum_toInfConvFn_le_convexConj_finsetSum

/-- **The $m$-fold infimal convolution is attained.** If the family $(f_i)_{i \in s}$ adds exactly,
then for every $y \in F$ there is a family $(y_i)_{i \in s}$ with $\sum_{i \in s} y_i = y$ and
$$\sum_{i \in s} f_i^*(y_i) = \Bigl(\sum_{i \in s} f_i\Bigr)^*(y).$$ So the infimum of
$f_1^*(y_1) + \dots + f_m^*(y_m)$ over $y_1 + \dots + y_m = y$ is attained. This is the half for
which the constraint qualifications are needed. -/
theorem exists_convexConj_finsetSum_eq (y : F) :
    ∃ y' : ι → F, ∑ i ∈ s, y' i = y ∧
      ∑ i ∈ s, convexConj B (f i) (y' i) = convexConj B (∑ i ∈ s, f i) y := by
  obtain ⟨y', hy, hle⟩ := h.exact_le y
  refine ⟨y', hy, le_antisymm hle ?_⟩
  rw [← hy]
  exact convexConj_finsetSum_le_sum_convexConj (fun i hi => (h.proper i hi).convexDom_nonempty) y'

end IsExactFinsetSum

/-- **A single proper function adds exactly.** If $f_i$ is proper, then the family
$(f_j)_{j \in \{i\}}$ adds exactly: there is nothing to split. This is the base case of every
$m$-ary constraint qualification. -/
theorem IsExactFinsetSum.singleton {i : ι} (hf : ProperConvex (f i)) :
    IsExactFinsetSum B ({i} : Finset ι) f where
  proper j hj := by rw [Finset.mem_singleton.1 hj]; exact hf
  exact_le y := ⟨fun _ => y, by simp, by simp⟩

/-- **Adjoining one summand.** Let $i \notin t$. If the family $(f_j)_{j \in t}$ adds exactly, and
$f_i$ and $\sum_{j \in t} f_j$ add exactly, then the family indexed by $t \cup \{i\}$ adds
exactly. This is the induction step of every $m$-ary constraint qualification. -/
theorem IsExactFinsetSum.cons {i : ι} {t : Finset ι} (hi : i ∉ t)
    (hbin : IsExactSum B (f i) (∑ j ∈ t, f j)) (ht : IsExactFinsetSum B t f) :
    IsExactFinsetSum B (Finset.cons i t hi) f := by
  classical
  refine ⟨fun j hj => ?_, fun y => ?_⟩
  · rcases Finset.mem_cons.1 hj with rfl | hj'
    · exact hbin.properConvex_left
    · exact ht.proper j hj'
  · obtain ⟨y₁, y₂, hy, hle⟩ := hbin.exact_le y
    obtain ⟨y', hy', hle'⟩ := ht.exact_le y₂
    obtain ⟨w, hwi, hwt⟩ : ∃ w : ι → F, w i = y₁ ∧ ∀ j ∈ t, w j = y' j :=
      ⟨Function.update y' i y₁, Function.update_self _ _ _,
        fun j hj => Function.update_of_ne (by rintro rfl; exact hi hj) _ _⟩
    refine ⟨w, ?_, ?_⟩
    · rw [Finset.sum_cons, hwi, Finset.sum_congr rfl hwt, hy', hy]
    · rw [Finset.sum_cons, Finset.sum_cons, hwi]
      have hcongr : ∑ j ∈ t, convexConj B (f j) (w j) = ∑ j ∈ t, convexConj B (f j) (y' j) :=
        Finset.sum_congr rfl fun j hj => by rw [hwt j hj]
      rw [hcongr]
      exact le_trans (add_le_add le_rfl hle') hle

/-- **Joining two exactly adding subfamilies.** Let $s$ be the disjoint union of $t$ and $u$. If the
families $(f_i)_{i \in t}$ and $(f_i)_{i \in u}$ add exactly, and $\sum_{i \in t} f_i$ and
$\sum_{i \in u} f_i$ add exactly, then the family $(f_i)_{i \in s}$ adds exactly.

The polyhedral proof uses this form, with $t$ the polyhedral indices and $u$ the others. The
union is stated pointwise, as $i \in s \iff i \in t \lor i \in u$, so that no `DecidableEq`
instance is needed. -/
theorem IsExactFinsetSum.of_split {t u : Finset ι} (hdisj : Disjoint t u)
    (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (ht : IsExactFinsetSum B t f) (hu : IsExactFinsetSum B u f)
    (hbin : IsExactSum B (∑ i ∈ t, f i) (∑ i ∈ u, f i)) :
    IsExactFinsetSum B s f := by
  classical
  have hsu : s = t ∪ u := Finset.ext fun i => by rw [hmem i, Finset.mem_union]
  subst hsu
  refine ⟨fun i hi => ?_, fun y => ?_⟩
  · rcases Finset.mem_union.1 hi with hi' | hi'
    · exact ht.proper i hi'
    · exact hu.proper i hi'
  · obtain ⟨y₁, y₂, hy, hle⟩ := hbin.exact_le y
    obtain ⟨a, ha, hlea⟩ := ht.exact_le y₁
    obtain ⟨b, hb, hleb⟩ := hu.exact_le y₂
    obtain ⟨w, hwt, hwu⟩ : ∃ w : ι → F, (∀ i ∈ t, w i = a i) ∧ ∀ i ∈ u, w i = b i :=
      ⟨fun i => if i ∈ t then a i else b i, fun i hi => by simp [hi],
        fun i hi => by simp [Finset.disjoint_right.1 hdisj hi]⟩
    refine ⟨w, ?_, ?_⟩
    · rw [Finset.sum_union hdisj, Finset.sum_congr rfl hwt, Finset.sum_congr rfl hwu, ha, hb, hy]
    · rw [Finset.sum_union hdisj, Finset.sum_union hdisj]
      have h₁ : ∑ i ∈ t, convexConj B (f i) (w i) = ∑ i ∈ t, convexConj B (f i) (a i) :=
        Finset.sum_congr rfl fun i hi => by rw [hwt i hi]
      have h₂ : ∑ i ∈ u, convexConj B (f i) (w i) = ∑ i ∈ u, convexConj B (f i) (b i) :=
        Finset.sum_congr rfl fun i hi => by rw [hwu i hi]
      rw [h₁, h₂]
      exact le_trans (add_le_add hlea hleb) hle

end FinsetSumInterface

/-! ### Images -/

section Image

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
variable {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {g : G → EReal}

/-- **The conjugate of an inverse image is at most the image of the conjugate.** Let $B'$ be a
second pairing, of real vector spaces $G$ and $H$, written $\langle \cdot, \cdot \rangle'$. Let
$A : E \to G$ and $A' : H \to F$ be linear maps with $\langle Ax, z \rangle' = \langle x, A'z
\rangle$ for all $x \in E$ and $z \in H$. Then for every $g : G \to [-\infty, +\infty]$,
$$(gA)^* \le A' g^*.$$ Here $(gA)(x) = g(Ax)$, the conjugate $g^*$ is taken with respect to
$B'$, and $(A'h)(y) = \inf \{h(z) : A'z = y\}$, which is $+\infty$ off the range of $A'$. No
other hypothesis is needed.

The inverse image is `ConvexAnalysis.compLin` and the image is `ConvexAnalysis.mapLin`. -/
theorem convexConj_compLin_le_mapLin (hA : IsAdjointPair B B' A A') (g : G → EReal) :
    convexConj B (compLin g A) ≤ mapLin A' (convexConj B' g) := by
  intro y
  refine le_mapLin fun z hz => ?_
  rw [convexConj_apply]
  refine iSup_le fun x => ?_
  rw [compLin_apply, ← hz, ← hA x z]
  exact sub_le_convexConj B' g (A x) z

/-- Let $A : E \to G$ and $A' : H \to F$ be linear maps with $\langle Ax, z \rangle' = \langle x,
A'z \rangle$. A function $g : G \to [-\infty, +\infty]$ **pulls back exactly** along $A$ if $g$
is proper and for every $y \in F$ with $(gA)^*(y) < +\infty$ there is $z \in H$ with $A'z = y$
and $$g^*(z) \le (gA)^*(y).$$ Then $(gA)^* = A' g^*$, and the infimum over the fibre
$\{z : A'z = y\}$ that defines $(A' g^*)(y)$ is attained wherever $(gA)^*(y) < +\infty$
(`ConvexAnalysis.IsExactImage.convexConj_compLin`,
`ConvexAnalysis.IsExactImage.exists_convexConj_compLin_eq`).

The transpose $A'$ and the proof `hA` of adjointness are data: between arbitrarily paired spaces
a linear map need not have an adjoint at all. -/
structure IsExactImage (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ)
    (A : E →ₗ[ℝ] G) (A' : H →ₗ[ℝ] F) (hA : IsAdjointPair B B' A A') (g : G → EReal) : Prop where
  /-- The function $g$ is proper. -/
  proper : ProperConvex g
  /-- For every $y \in F$ with $(gA)^*(y) < +\infty$ there is $z \in H$ with $A'z = y$ and
  $g^*(z) \le (gA)^*(y)$. The reverse inequality is unconditional
  (`ConvexAnalysis.convexConj_compLin_le_mapLin`).

  The condition $(gA)^*(y) < +\infty$ is necessary. Without it the field would ask for a point
  of the fibre $\{z : A'z = y\}$ for every $y$, and so would force $A'$ to be surjective. -/
  exact_le : ∀ y : F, convexConj B (compLin g A) y < ⊤ →
    ∃ z : H, A' z = y ∧ convexConj B' g z ≤ convexConj B (compLin g A) y

namespace IsExactImage

variable {hA : IsAdjointPair B B' A A'} (h : IsExactImage B B' A A' hA g)
include h

/-- **An exact inverse image is proper.** If $g$ pulls back exactly along $A$, then the inverse
image $gA$ is proper. In particular the range of $A$ meets the effective domain of $g$, so the
interface cannot hold when they are disjoint. -/
theorem properConvex_compLin : ProperConvex (compLin g A) := by
  have hb : convexConj B (compLin g A) 0 ≠ ⊥ := by
    intro hc
    obtain ⟨z, -, hle⟩ := h.exact_le 0 (by rw [hc]; exact bot_lt_top)
    rw [hc, le_bot_iff] at hle
    exact convexConj_ne_bot h.proper.convexDom_nonempty z hle
  refine ⟨?_, fun x => h.proper.ne_bot (A x)⟩
  by_contra hd
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hd
  exact hb (convexConj_eq_bot_iff.2 fun x => top_le_iff.1 (not_lt.1 (hd x)))

/-- If $g$ pulls back exactly along $A$, then $A' g^* \le (gA)^*$. -/
theorem mapLin_le_convexConj_compLin : mapLin A' (convexConj B' g) ≤ convexConj B (compLin g A) :=
    fun y => by
  rcases eq_top_or_lt_top (convexConj B (compLin g A) y) with hy | hy
  · rw [hy]; exact le_top
  obtain ⟨z, hz, hle⟩ := h.exact_le y hy
  exact (mapLin_le hz).trans hle

/-- **The conjugate of an inverse image.** If $g : G \to [-\infty, +\infty]$ pulls back exactly
along $A$, then $$(gA)^* = A' g^*.$$

This is the conclusion of Theorem 16.3 of [rockafellar1970convex]. -/
theorem convexConj_compLin : convexConj B (compLin g A) = mapLin A' (convexConj B' g) :=
  le_antisymm (convexConj_compLin_le_mapLin hA g) h.mapLin_le_convexConj_compLin

omit h in
/-- **The concave conjugate of an inverse image.** Let $g : G \to [-\infty, +\infty]$ be such that
$-g$ pulls back exactly along $A$. Then for every $y \in F$, $$(gA)^*(y) = \sup \{g^*(z) : z \in
H,\ A'z = y\},$$ with the concave conjugates of $gA$ and $g$.

This is the concave counterpart of `ConvexAnalysis.IsExactImage.convexConj_compLin`, with a
supremum where the convex statement has an infimum. Both reflections of the sign relation
`ConvexAnalysis.neg_concaveConj` are at work, so the fibre $A'z = -y$ becomes $A'z = y$. -/
theorem concaveConj_compLin (himg : IsExactImage B B' A A' hA fun w => -(g w)) (y : F) :
    concaveConj B (compLin g A) y = ⨆ z : H, ⨆ _ : A' z = y, concaveConj B' g z := by
  set k : H → EReal := convexConj B' (fun w => -(g w)) with hk
  have hneg : ∀ z : H, -(concaveConj B' g z) = k (-z) := fun z => neg_concaveConj B' g z
  have hmain : mapLin A' k (-y) = ⨅ z : H, ⨅ _ : A' z = y, k (-z) := by
    refine le_antisymm (le_iInf fun z => le_iInf fun hz => mapLin_le ?_) (le_mapLin fun w hw => ?_)
    · rw [map_neg, hz]
    · refine le_trans (iInf₂_le (f := fun z (_ : A' z = y) => k (-z)) (-w) ?_) (le_of_eq ?_)
      · rw [map_neg, hw, neg_neg]
      · rw [neg_neg]
  have hcomp : concaveConj B (compLin g A) y = -(mapLin A' k (-y)) := by
    rw [concaveConj_eq_neg_convexConj_neg]
    congr 1
    exact congrFun (himg.convexConj_compLin) (-y)
  rw [hcomp, hmain, EReal.neg_iInf]
  refine iSup_congr fun z => ?_
  rw [EReal.neg_iInf]
  exact iSup_congr fun _ => (hneg z).symm ▸ neg_neg _

/-- **The infimum over the fibre is attained.** If $g$ pulls back exactly along $A$ and
$(gA)^*(y) < +\infty$, then there is $z \in H$ with $A'z = y$ and $$g^*(z) = (gA)^*(y).$$ This
is the half for which the constraint qualifications are needed. -/
theorem exists_convexConj_compLin_eq {y : F} (hy : convexConj B (compLin g A) y < ⊤) :
    ∃ z : H, A' z = y ∧ convexConj B' g z = convexConj B (compLin g A) y := by
  obtain ⟨z, hz, hle⟩ := h.exact_le y hy
  exact ⟨z, hz, le_antisymm hle (h.convexConj_compLin ▸ mapLin_le hz)⟩

end IsExactImage

end Image

end ConvexAnalysis
