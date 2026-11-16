/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Duality.Conjugate
import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Extremum.Minimum

/-!
# Fenchel's duality theorem

Let $E$ and $F$ be real vector spaces in duality through a pairing $\langle x, y \rangle$, let
$f : E \to [-\infty, +\infty]$ be convex and let $g : E \to [-\infty, +\infty]$ be concave.
Minimizing $f - g$ is dual to maximizing $g^* - f^*$, where $f^*(y) = \sup_x \{\langle x, y
\rangle - f(x)\}$ is the convex conjugate and $g^*(y) = \inf_x \{\langle x, y \rangle - g(x)\}$ is
the concave conjugate. Weak duality $g^*(y) - f^*(y) \le f(x) - g(x)$ is Fenchel's inequality
applied twice and needs no hypothesis. **Fenchel's duality theorem**, Theorem 31.1 of
[rockafellar1970convex], states that
$$\inf_x \{f(x) - g(x)\} = \sup_y \{g^*(y) - f^*(y)\}$$
under a constraint qualification, with the supremum attained under condition (a) and the infimum
attained under condition (b) of the source.

This module also proves the version with a linear map $A$ between the two functions, $\inf (f - g
\circ A) = \sup (g^* - f^* \circ A')$ with $A'$ the adjoint of $A$. The Kuhn–Tucker conditions
$y \in \partial f(x)$ and $-y \in \partial(-g)(x)$ characterize a pair $(x, y)$ of optimal points.
In the special case of minimization over a convex cone $K$, the dual problem is to minimize $f^*$
over $K^* = -K^\circ$, and the two optimal values add to $0$. This follows [rockafellar1970convex],
§31.

## Main results

* `ConvexAnalysis.concaveConj_sub_convexConj_le_sub`: weak duality,
  $g^*(y) - f^*(y) \le f(x) - g(x)$.
* `ConvexAnalysis.fenchel_duality`, `ConvexAnalysis.exists_concaveConj_sub_convexConj_eq`: Fenchel's
  duality theorem under condition (a), with the supremum attained. This is Theorem 31.1 of
  [rockafellar1970convex].
* `ConvexAnalysis.fenchel_duality_of_closed`, `ConvexAnalysis.exists_sub_eq_iInf`: the same equality
  under condition (b), with the infimum attained.
* `ConvexAnalysis.fenchel_duality_comp`, `ConvexAnalysis.exists_concaveConj_sub_convexConj_comp_eq`:
  the version with a linear map, $\inf (f - g \circ A) = \sup (g^* - f^* \circ A')$, with the
  supremum attained.
* `ConvexAnalysis.sub_eq_concaveConj_sub_convexConj_iff`,
  `ConvexAnalysis.sub_comp_eq_concaveConj_sub_convexConj_iff`: the **Fenchel optimality
  conditions**, without and with the linear map.
* `ConvexAnalysis.iInf_sub_eq_iff_exists_kuhnTucker`,
  `ConvexAnalysis.iInf_sub_comp_eq_iff_exists_kuhnTucker`: under exact addition, $x$ is a minimizer
  if and only if the optimality conditions hold for some $y$.
* `ConvexAnalysis.iInf_mem_eq_neg_iInf_mem_neg_polarCone`: the **cone form**,
  $\inf_{x \in K} f(x) = -\inf_{y \in K^*} f^*(y)$.
* `ConvexAnalysis.exists_mem_neg_polarCone_convexConj_eq_iInf`,
  `ConvexAnalysis.exists_mem_eq_iInf_of_isExactSum_convexConj`: attainment in the cone form under
  conditions (a) and (b).
* `ConvexAnalysis.iInf_mem_submodule_eq_neg_iInf_mem_polarCone`: the cone form for a subspace $L$,
  where $K^*$ is the annihilator $L^\perp$.

## Notation

* $\partial f(x)$: the subdifferential `ConvexAnalysis.subdifferential B f x`, the set of $y$ with
  $f(x) + \langle z - x, y \rangle \le f(z)$ for all $z$.
* $K^\circ$: the polar cone `ConvexAnalysis.polarCone B K`, the set of $y$ with
  $\langle x, y \rangle \le 0$ for all $x \in K$. The cone $K^*$ of [rockafellar1970convex] is
  `-(polarCone B K)`.
* $\delta(\cdot \mid K)$: the indicator function `ConvexAnalysis.indicatorFn K`.

## Implementation notes

* The hypothesis of the theorems is `ConvexAnalysis.IsExactSum B f (-g)`: $f$ and $-g$ add exactly,
  that is, the conjugate of $f + (-g)$ is the infimal convolution of the conjugates, and the infimal
  convolution is attained. It is not a constraint qualification. Condition (a) of
  [rockafellar1970convex], $\operatorname{ri}(\operatorname{dom} f) \cap
  \operatorname{ri}(\operatorname{dom} g) \neq \emptyset$, condition (b) on the conjugates, and the
  two polyhedral weakenings of each all imply that $f$ and $-g$ add exactly. Thus the theorem is
  proved once and each variant is an instance. Condition (b) is condition (a) for the dual pair.
* The version with a linear map splits condition (a) of the source into two hypotheses:
  `ConvexAnalysis.IsExactSum` for the sum, and `ConvexAnalysis.IsExactImage` for the pullback along
  $A$.
* The linear map is `A : E →ₗ[ℝ] G` and its adjoint is `A' : H →ₗ[ℝ] F`, for pairings `B` of $E$
  with $F$ and `B'` of $G$ with $H$. The adjointness $\langle A x, z \rangle = \langle x, A' z
  \rangle$ is the hypothesis `ConvexAnalysis.IsAdjointPair B B' A A'`.
* Differences are taken in `EReal`, where $a - b = a + (-b)$ and $(+\infty) + (-\infty) = -\infty$.
  Weak duality holds with this convention without any hypothesis.
-/

namespace ConvexAnalysis

section Fenchel

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal}

/-- If $a \le p - b$ and $p - c \le d$ in $[-\infty, +\infty]$ with $p$ real, then
$a - d \le c - b$. -/
private theorem sub_le_sub_of_le_sub_of_sub_le {a b c d : EReal} {p : ℝ}
    (h1 : a ≤ (p : EReal) - b) (h2 : (p : EReal) - c ≤ d) : a - d ≤ c - b := by
  have hpb : ((p : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hpt : ((p : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have h3 : -d ≤ c - ((p : ℝ) : EReal) := by
    refine le_trans (EReal.neg_le_neg_iff.2 h2) (le_of_eq ?_)
    rw [EReal.neg_sub (.inl hpb) (.inl hpt), sub_eq_add_neg, add_comm]
  have hsum : a + -d ≤ (((p : ℝ) : EReal) - b) + (c - ((p : ℝ) : EReal)) := add_le_add h1 h3
  refine le_trans (le_of_eq (sub_eq_add_neg _ _)) (le_trans hsum (le_of_eq ?_))
  rw [sub_eq_add_neg ((p : ℝ) : EReal) b, sub_eq_add_neg c ((p : ℝ) : EReal),
    add_comm c (-((p : ℝ) : EReal)),
    add_add_add_comm ((p : ℝ) : EReal) (-b) (-((p : ℝ) : EReal)) c]
  have hpp : ((p : ℝ) : EReal) + -((p : ℝ) : EReal) = 0 := by
    rw [← EReal.coe_neg, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  rw [hpp, zero_add, add_comm (-b) c, sub_eq_add_neg]

/-- **Weak duality.** Let $f, g : E \to [-\infty, +\infty]$. Then for every $x \in E$ and $y \in F$,
$$g^*(y) - f^*(y) \le f(x) - g(x),$$
where $f^*$ is the convex conjugate of $f$ and $g^*$ is the concave conjugate of $g$.

No hypothesis is needed. The inequality is the sum of Fenchel's inequalities for $f$ and for
$g$. In both cases where $\infty - \infty$ occurs, the left side is $-\infty$. -/
theorem concaveConj_sub_convexConj_le_sub (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f g : E → EReal) (x : E)
    (y : F) :
    concaveConj B g y - convexConj B f y ≤ f x - g x :=
  sub_le_sub_of_le_sub_of_sub_le (concaveConj_le_sub B g x y) (sub_le_convexConj B f x y)

/-- **Fenchel's duality theorem.** Let $f, g : E \to [-\infty, +\infty]$ be such that $f$ and $-g$
add exactly. Then
$$\inf_x \bigl\{ f(x) - g(x) \bigr\} = \sup_y \bigl\{ g^*(y) - f^*(y) \bigr\}.$$

This is Theorem 31.1 of [rockafellar1970convex], with the constraint qualification replaced by
the hypothesis `ConvexAnalysis.IsExactSum B f (-g)`, which condition (a) implies. The proof
applies $\inf h = -h^*(0)$ to $h = f + (-g)$, and exact addition splits the conjugate of the sum
at the origin. -/
theorem fenchel_duality (hex : IsExactSum B f (-g)) :
    (⨅ x, f x - g x) = ⨆ y, concaveConj B g y - convexConj B f y := by
  have hex' : IsExactSum B f (fun x => -(g x)) := hex
  have hne : ∀ y : F, concaveConj B g y ≠ ⊤ := fun y hc =>
    hex'.convexConj_right_ne_bot (-y) (by rw [← neg_concaveConj B g y, hc, EReal.neg_top])
  have hprimal : (⨅ x, f x - g x) = -(convexConj B (f + fun x => -(g x)) 0) := by
    rw [← iInf_eq_neg_convexConj_zero B]
    exact iInf_congr fun x => by rw [Pi.add_apply, sub_eq_add_neg]
  have hdual : convexConj B (f + fun x => -(g x)) 0 = ⨅ y : F,
      convexConj B f y - concaveConj B g y := by
    rw [hex'.convexConj_add_apply 0, ← (neg_surjective (G := F)).iInf_comp]
    refine iInf_congr fun y => ?_
    rw [zero_sub, neg_neg, ← neg_concaveConj B g y, sub_eq_add_neg]
  rw [hprimal, hdual, EReal.neg_iInf]
  exact iSup_congr fun y => EReal.neg_sub_comm (.inl (hex'.convexConj_left_ne_bot y)) (.inr (hne y))

/-- **Attainment of the dual supremum.** If $f$ and $-g$ add exactly, then there is $y \in F$ with
$$g^*(y) - f^*(y) = \inf_x \bigl\{ f(x) - g(x) \bigr\}.$$
-/
theorem exists_concaveConj_sub_convexConj_eq (hex : IsExactSum B f (-g)) :
    ∃ y : F, concaveConj B g y - convexConj B f y = ⨅ x, f x - g x := by
  have hex' : IsExactSum B f (fun x => -(g x)) := hex
  have hne : ∀ y : F, concaveConj B g y ≠ ⊤ := fun y hc =>
    hex'.convexConj_right_ne_bot (-y) (by rw [← neg_concaveConj B g y, hc, EReal.neg_top])
  have hprimal : (⨅ x, f x - g x) = -(convexConj B (f + fun x => -(g x)) 0) := by
    rw [← iInf_eq_neg_convexConj_zero B]
    exact iInf_congr fun x => by rw [Pi.add_apply, sub_eq_add_neg]
  obtain ⟨y₁, y₂, hy, hval⟩ := hex'.exists_convexConj_add_eq 0
  have hy2 : y₂ = -y₁ := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hy
  subst hy2
  rw [← neg_concaveConj B g y₁, ← sub_eq_add_neg] at hval
  refine ⟨y₁, ?_⟩
  rw [hprimal, ← hval, EReal.neg_sub_comm (.inl (hex'.convexConj_left_ne_bot y₁)) (.inr (hne y₁))]

/-- If $f$ and $-g$ add exactly, then $\inf_x \{f(x) - g(x)\}$ is the greatest element of the set of
values $g^*(y) - f^*(y)$, $y \in F$. -/
theorem isGreatest_concaveConj_sub_convexConj (hex : IsExactSum B f (-g)) :
    IsGreatest (Set.range fun y => concaveConj B g y - convexConj B f y) (⨅ x, f x - g x) := by
  obtain ⟨y, hy⟩ := exists_concaveConj_sub_convexConj_eq hex
  refine ⟨⟨y, hy⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  rw [fenchel_duality hex]
  exact le_iSup (fun w : F => concaveConj B g w - convexConj B f w) z

end Fenchel

/-! ### A linear map between the two functions -/

section Comp

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {f : E → EReal} {g : G → EReal}

/-- **The dual program of the version with a linear map lives on $H$.** Let $A : E \to G$ and
$A' : H \to F$ be adjoint, let $-g$ pull back exactly along $A$, and let $f^*(y) > -\infty$ for
all $y$. Then
$$\sup_{y \in F} \bigl\{ (g \circ A)^*(y) - f^*(y) \bigr\} = \sup_{z \in H} \bigl\{ g^*(z) -
  f^*(A' z) \bigr\},$$
where $(g \circ A)^*$ and $g^*$ are concave conjugates.

The image rule for the concave conjugate writes each value on the left as a supremum over a
fiber of $A'$, and the two suprema combine into one over $H$. The result is used under both
conditions (a) and (b). -/
theorem iSup_concaveConj_compLin_sub_convexConj (hA : IsAdjointPair B B' A A')
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) (hb : ∀ y : F, convexConj B f y ≠ ⊥) :
    (⨆ y : F, concaveConj B (compLin g A) y - convexConj B f y)
      = ⨆ z : H, concaveConj B' g z - convexConj B f (A' z) := by
  have key : ∀ y : F, concaveConj B (compLin g A) y - convexConj B f y
      = ⨆ z : H, ⨆ _ : A' z = y, (concaveConj B' g z - convexConj B f (A' z)) := by
    intro y
    rw [himg.concaveConj_compLin y, EReal.iSup_sub_of_ne_bot _ (hb y)]
    refine iSup_congr fun z => ?_
    rw [EReal.iSup_sub_of_ne_bot _ (hb y)]
    exact iSup_congr fun hz => by rw [hz]
  refine le_antisymm (iSup_le fun y => ?_) (iSup_le fun z => ?_)
  · rw [key y]
    exact iSup_le fun w => iSup_le fun _ =>
      le_iSup (fun v : H => concaveConj B' g v - convexConj B f (A' v)) w
  · refine le_trans ?_
      (le_iSup (fun y : F => concaveConj B (compLin g A) y - convexConj B f y) (A' z))
    rw [key (A' z)]
    exact le_iSup₂
        (f := fun w (_ : A' w = A' z) => concaveConj B' g w - convexConj B f (A' w)) z rfl

/-- **Fenchel's duality theorem with a linear map.** Let $A : E \to G$ and $A' : H \to F$ be
adjoint, let $f : E \to [-\infty, +\infty]$ and $g : G \to [-\infty, +\infty]$, let $f$ and
$-(g \circ A)$ add exactly, and let $-g$ pull back exactly along $A$. Then
$$\inf_{x \in E} \bigl\{ f(x) - g(Ax) \bigr\} = \sup_{z \in H} \bigl\{ g^*(z) - f^*(A' z)
  \bigr\}.$$

The two hypotheses split condition (a) of the source in two:
$\operatorname{ri}(\operatorname{dom} f) \cap A^{-1}(\operatorname{ri}(\operatorname{dom} g))
\neq \emptyset$ implies both. Exact pullback is `ConvexAnalysis.IsExactImage`. -/
theorem fenchel_duality_comp (hA : IsAdjointPair B B' A A')
    (hex : IsExactSum B f fun x => -(g (A x)))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) :
    (⨅ x, f x - g (A x)) = ⨆ z : H, concaveConj B' g z - convexConj B f (A' z) := by
  have hex' : IsExactSum B f (-(compLin g A)) := hex
  have h31 : (⨅ x, f x - g (A x)) = ⨆ y : F, concaveConj B (compLin g A) y - convexConj B f y :=
    fenchel_duality hex'
  rw [h31]
  exact iSup_concaveConj_compLin_sub_convexConj hA himg hex'.convexConj_left_ne_bot

/-- **Attainment of the dual supremum with a linear map.** Under the hypotheses of
`ConvexAnalysis.fenchel_duality_comp`, there is $z \in H$ with
$$g^*(z) - f^*(A' z) = \inf_x \bigl\{ f(x) - g(Ax) \bigr\}.$$

The proof combines attainment in the duality over $F$ with attainment in the image rule over the
fiber of $A'$. The degenerate common value $-\infty$ is treated separately. -/
theorem exists_concaveConj_sub_convexConj_comp_eq (hA : IsAdjointPair B B' A A')
    (hex : IsExactSum B f fun x => -(g (A x)))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) :
    ∃ z : H, concaveConj B' g z - convexConj B f (A' z) = ⨅ x, f x - g (A x) := by
  have hex' : IsExactSum B f (-(compLin g A)) := hex
  rcases eq_or_ne (⨅ x, f x - g (A x)) ⊥ with hb | hb
  · have hle : concaveConj B' g 0 - convexConj B f (A' 0) ≤ ⨅ x, f x - g (A x) := by
      rw [fenchel_duality_comp hA hex himg]
      exact le_iSup (fun z : H => concaveConj B' g z - convexConj B f (A' z)) 0
    exact ⟨0, le_antisymm hle (by rw [hb]; exact bot_le)⟩
  obtain ⟨y, hy⟩ : ∃ y : F, concaveConj B (compLin g A) y - convexConj B f y = ⨅ x, f x - g (A x) :=
    exists_concaveConj_sub_convexConj_eq hex'
  have hyb : concaveConj B (compLin g A) y ≠ ⊥ := by
    intro hc
    exact hb (by rw [← hy, hc, sub_eq_add_neg, EReal.bot_add])
  have hlt : convexConj B (compLin (fun w => -(g w)) A) (-y) < ⊤ := by
    refine lt_of_le_of_ne le_top fun hc => hyb ?_
    rw [concaveConj_eq_neg_convexConj_neg]
    change -(convexConj B (compLin (fun w => -(g w)) A) (-y)) = ⊥
    rw [hc, EReal.neg_top]
  obtain ⟨z, hz, hzeq⟩ := himg.exists_convexConj_compLin_eq hlt
  refine ⟨-z, ?_⟩
  have hA'z : A' (-z) = y := by rw [map_neg, hz, neg_neg]
  have hval : concaveConj B' g (-z) = concaveConj B (compLin g A) y := by
    rw [concaveConj_eq_neg_convexConj_neg, neg_neg, hzeq, concaveConj_eq_neg_convexConj_neg]
    rfl
  rw [hA'z, hval, hy]

end Comp

/-! ### Condition (b): the closed case, with the infimum attained -/

section Closed

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f g : E → EReal}

/-- Let $E$ be a locally convex real topological vector space with a compatible pairing. Let $f$ be
a closed proper convex function, let $g$ be a closed proper concave function, and let $f^*$ and
$-g^*$ add exactly for the flipped pairing. Then
$$\inf_x \bigl\{ f(x) - g(x) \bigr\} = -\inf_y \bigl\{ f^*(y) - g^*(y) \bigr\}.$$
This is `ConvexAnalysis.fenchel_duality` for the pair $(f^*, g^*)$ and the flipped pairing. -/
theorem iInf_sub_eq_neg_iInf_convexConj_sub (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConcaveFn g)
    (hex : IsExactSum B.flip (convexConj B f) (-(concaveConj B g))) :
    (⨅ x, f x - g x) = -(⨅ y : F, convexConj B f y - concaveConj B g y) := by
  have hgt : ∀ x, g x ≠ ⊤ := hg.proper.ne_top
  have hbi : ∀ x, convexConj B.flip (convexConj B f) x = f x := fun x =>
    congrFun (convexBiconj_eq_self hf.convex hf.closed) x
  have hbc : ∀ x, concaveConj B.flip (concaveConj B g) x = g x := fun x =>
    congrFun (concaveBiconj_eq_self hg.concave hg.closed) x
  have hkey := fenchel_duality (B := B.flip) (f := convexConj B f) (g := concaveConj B g) hex
  rw [show (⨆ x : E, concaveConj B.flip (concaveConj B g) x - convexConj B.flip (convexConj B f) x)
        = ⨆ x : E, -(f x - g x) from
      iSup_congr fun x => by
        rw [hbi, hbc]
        exact (EReal.neg_sub_comm (.inl (hf.proper.ne_bot x)) (.inr (hgt x))).symm,
    ← EReal.neg_iInf] at hkey
  rw [hkey, neg_neg]

/-- **Fenchel's duality theorem under condition (b).** Let $E$ be a locally convex real topological
vector space with a compatible pairing. Let $f$ be a closed proper convex function, let $g$ be a
closed proper concave function, and let $f^*$ and $-g^*$ add exactly for the flipped pairing.
Then
$$\inf_x \bigl\{ f(x) - g(x) \bigr\} = \sup_y \bigl\{ g^*(y) - f^*(y) \bigr\}.$$

The equality is the same as under condition (a). Condition (b) gives attainment of the infimum,
by `ConvexAnalysis.exists_sub_eq_iInf`. -/
theorem fenchel_duality_of_closed (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConcaveFn g)
    (hex : IsExactSum B.flip (convexConj B f) (-(concaveConj B g))) :
    (⨅ x, f x - g x) = ⨆ y : F, concaveConj B g y - convexConj B f y := by
  have hdc : (concaveDom g).Nonempty := hg.proper.concaveDom_nonempty
  rw [iInf_sub_eq_neg_iInf_convexConj_sub hf hg hex, EReal.neg_iInf]
  exact iSup_congr fun y =>
    EReal.neg_sub_comm (.inl (convexConj_ne_bot hf.proper.convexDom_nonempty y))
      (.inr (concaveConj_ne_top hdc y))

/-- **Attainment of the primal infimum under condition (b).** Under the hypotheses of
`ConvexAnalysis.fenchel_duality_of_closed`, there is $x \in E$ with
$$f(x) - g(x) = \inf_z \bigl\{ f(z) - g(z) \bigr\}.$$
-/
theorem exists_sub_eq_iInf (hf : ClosedProperConvexFn f)
    (hg : ClosedProperConcaveFn g)
    (hex : IsExactSum B.flip (convexConj B f) (-(concaveConj B g))) :
    ∃ x : E, f x - g x = ⨅ z, f z - g z := by
  have hgt : ∀ x, g x ≠ ⊤ := hg.proper.ne_top
  have hbi : ∀ x, convexConj B.flip (convexConj B f) x = f x := fun x =>
    congrFun (convexBiconj_eq_self hf.convex hf.closed) x
  have hbc : ∀ x, concaveConj B.flip (concaveConj B g) x = g x := fun x =>
    congrFun (concaveBiconj_eq_self hg.concave hg.closed) x
  obtain ⟨x, hx⟩ := exists_concaveConj_sub_convexConj_eq (B := B.flip) (f := convexConj B f)
    (g := concaveConj B g) hex
  rw [hbi, hbc] at hx
  exact ⟨x, by rw [iInf_sub_eq_neg_iInf_convexConj_sub hf hg hex, ← hx,
    EReal.neg_sub_comm (.inr (hf.proper.ne_bot x)) (.inl (hgt x))]⟩

end Closed

/-! ### The version with a linear map under condition (b) -/

section CompClosed

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {f : E → EReal} {g : G → EReal}

/-- **Fenchel's duality theorem with a linear map under condition (b).** Let $E$ be a locally convex
real topological vector space with a compatible pairing, and let $A : E \to G$ and
$A' : H \to F$ be adjoint. Let $f$ be closed, proper and convex, let $g \circ A$ be closed,
proper and concave, let $f^*$ and $-(g \circ A)^*$ add exactly for the flipped pairing, and let
$-g$ pull back exactly along $A$. Then
$$\inf_x \bigl\{ f(x) - g(Ax) \bigr\} = \sup_{z \in H} \bigl\{ g^*(z) - f^*(A' z) \bigr\}.$$

Condition (a) gives attainment of the supremum. Condition (b) gives attainment of the infimum,
by `ConvexAnalysis.exists_sub_comp_eq_iInf`. -/
theorem fenchel_duality_comp_of_closed (hA : IsAdjointPair B B' A A')
    (hf : ClosedProperConvexFn f) (hgA : ClosedProperConcaveFn fun x => g (A x))
    (hex : IsExactSum B.flip (convexConj B f) (-(concaveConj B (compLin g A))))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) :
    (⨅ x, f x - g (A x)) = ⨆ z : H, concaveConj B' g z - convexConj B f (A' z) := by
  have h : (⨅ x, f x - g (A x)) = ⨆ y : F, concaveConj B (compLin g A) y - convexConj B f y :=
    fenchel_duality_of_closed hf hgA hex
  rw [h]
  exact iSup_concaveConj_compLin_sub_convexConj hA
      himg (convexConj_ne_bot hf.proper.convexDom_nonempty)

/-- Let $E$ be a locally convex real topological vector space with a compatible pairing. Let $f$ be
closed, proper and convex, let $g \circ A$ be closed, proper and concave, and let $f^*$ and
$-(g \circ A)^*$ add exactly for the flipped pairing. Then the infimum of $f - g \circ A$ is
attained: there is $x \in E$ with $f(x) - g(Ax) = \inf_z \{f(z) - g(Az)\}$. -/
theorem exists_sub_comp_eq_iInf (hf : ClosedProperConvexFn f)
    (hgA : ClosedProperConcaveFn fun x => g (A x))
    (hex : IsExactSum B.flip (convexConj B f) (-(concaveConj B (compLin g A)))) :
    ∃ x : E, f x - g (A x) = ⨅ z, f z - g (A z) :=
  exists_sub_eq_iInf hf hgA hex

end CompClosed

/-! ### The Fenchel optimality conditions -/

section Optimality

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f g : E → EReal} {x : E} {y : F}

/-- Let $a, b, c, d \in [-\infty, +\infty]$ with $a \neq -\infty$, $b \neq +\infty$,
$c \neq +\infty$ and $d \neq -\infty$. If $a - b = c - d$, then $a \neq +\infty$,
$b \neq -\infty$, $c \neq -\infty$ and $d \neq +\infty$. -/
private theorem finite_of_sub_eq {a b c d : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊥) (h : a - b = c - d) : a ≠ ⊤ ∧ b ≠ ⊥ ∧ c ≠ ⊥ ∧ d ≠ ⊤ := by
  induction a <;> induction b <;> induction c <;> induction d <;>
    simp_all [← EReal.coe_sub]

/-- Let $a, b, c, d, p \in [-\infty, +\infty]$ with $a \neq -\infty$, $b \neq +\infty$,
$c \neq +\infty$, $d \neq -\infty$, $p$ finite, $p \le a + d$ and $b + c \le p$. Then
$a - b = c - d$ if and only if $a + d = p$ and $b + c = p$. -/
private theorem sub_eq_sub_iff_of_le {a b c d p : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊥) (hp1 : p ≠ ⊥) (hp2 : p ≠ ⊤) (h1 : p ≤ a + d) (h2 : b + c ≤ p) :
    a - b = c - d ↔ a + d = p ∧ b + c = p := by
  obtain ⟨π, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hp1 (lt_top_iff_ne_top.2 hp2)
  constructor
  · intro h
    obtain ⟨hat, hbb, hcb, hdt⟩ := finite_of_sub_eq ha hb hc hd h
    obtain ⟨α, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top ha (lt_top_iff_ne_top.2 hat)
    obtain ⟨β, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbb (lt_top_iff_ne_top.2 hb)
    obtain ⟨γ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hc)
    obtain ⟨δ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hd (lt_top_iff_ne_top.2 hdt)
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_eq_coe_iff] at h
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff,
      EReal.coe_eq_coe_iff]
    constructor <;> linarith
  · rintro ⟨e1, e2⟩
    obtain ⟨hat, hdt⟩ := (EReal.add_ne_top_iff_ne_top₂ ha hd).1 (e1 ▸ EReal.coe_ne_top π)
    obtain ⟨hbb, hcb⟩ := EReal.add_ne_bot_iff.1 (e2 ▸ EReal.coe_ne_bot π)
    obtain ⟨α, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top ha (lt_top_iff_ne_top.2 hat)
    obtain ⟨β, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbb (lt_top_iff_ne_top.2 hb)
    obtain ⟨γ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hc)
    obtain ⟨δ, rfl⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hd (lt_top_iff_ne_top.2 hdt)
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at e1
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at e2
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    linarith

/-- **Equality in the concave Fenchel inequality.** Let $-g$ be proper. Then
$$-y \in \partial(-g)(x) \iff g(x) + g^*(y) = \langle x, y \rangle.$$

The source writes this as $x \in \partial g^*(y)$, with the superdifferential $-\partial(-g)$ of
a concave function. -/
theorem neg_mem_subdifferential_neg_iff_add_concaveConj_eq (hpg : ProperConvex fun z => -(g z)) :
    -y ∈ subdifferential B (fun z => -(g z)) x ↔
      g x + concaveConj B g y = ((B x y : ℝ) : EReal) := by
  have hgt : g x ≠ ⊤ := fun hc => hpg.ne_bot x (by rw [hc, EReal.neg_top])
  have hdc : (concaveDom g).Nonempty := by
    rw [concaveDom_eq_convexDom_neg]
    exact hpg.convexDom_nonempty
  have hct : concaveConj B g y ≠ ⊤ := concaveConj_ne_top hdc y
  have hpn : ((B x (-y) : ℝ) : EReal) = -((B x y : ℝ) : EReal) := by
    rw [map_neg, EReal.coe_neg]
  rw [hpg.mem_subdifferential_iff_add_convexConj_eq, ← neg_concaveConj B g y, hpn, ← sub_eq_add_neg,
    ← EReal.neg_add (.inr hct) (.inl hgt), neg_inj]

/-- **The Fenchel optimality conditions.** Let $f$ be proper and let $-g$ be proper. Then for
$x \in E$ and $y \in F$,
$$f(x) - g(x) = g^*(y) - f^*(y) \iff y \in \partial f(x) \text{ and } -y \in \partial(-g)(x).$$

By weak duality, the left side says that $x$ and $y$ are optimal for the two problems of
`ConvexAnalysis.fenchel_duality`. Both conditions on the right say that a Fenchel inequality
holds with equality. The equality $f(x) - g(x) = g^*(y) - f^*(y)$ forces the two inequalities
$\langle x, y \rangle \le f(x) + f^*(y)$ and $g(x) + g^*(y) \le \langle x, y \rangle$ to be
equalities. -/
theorem sub_eq_concaveConj_sub_convexConj_iff (hpf : ProperConvex f)
    (hpg : ProperConvex fun z => -(g z)) :
    f x - g x = concaveConj B g y - convexConj B f y ↔
      y ∈ subdifferential B f x ∧ -y ∈ subdifferential B (fun z => -(g z)) x := by
  have hgt : g x ≠ ⊤ := fun hc => hpg.ne_bot x (by rw [hc, EReal.neg_top])
  have hdc : (concaveDom g).Nonempty := by
    rw [concaveDom_eq_convexDom_neg]
    exact hpg.convexDom_nonempty
  rw [sub_eq_sub_iff_of_le (hpf.ne_bot x) hgt (concaveConj_ne_top hdc y)
      (convexConj_ne_bot hpf.convexDom_nonempty y) (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
      (le_add_convexConj (hpf.ne_bot x) hpf.convexDom_nonempty y) (add_concaveConj_le B g x y),
    hpf.mem_subdifferential_iff_add_convexConj_eq,
    neg_mem_subdifferential_neg_iff_add_concaveConj_eq hpg]

/-- If $f(x) - g(x) = g^*(y) - f^*(y)$, then $x$ minimizes $f - g$:
$\inf_z \{f(z) - g(z)\} = f(x) - g(x)$. Only weak duality is used. -/
theorem iInf_sub_eq_of_sub_eq (h : f x - g x = concaveConj B g y - convexConj B f y) :
    (⨅ z, f z - g z) = f x - g x :=
  le_antisymm (iInf_le _ x) (le_iInf fun z => by
    rw [h]; exact concaveConj_sub_convexConj_le_sub B f g z y)

/-- If $f(x) - g(x) = g^*(y) - f^*(y)$, then $y$ maximizes $g^* - f^*$:
$\sup_w \{g^*(w) - f^*(w)\} = g^*(y) - f^*(y)$. -/
theorem iSup_sub_eq_of_sub_eq (h : f x - g x = concaveConj B g y - convexConj B f y) :
    (⨆ w : F, concaveConj B g w - convexConj B f w) = concaveConj B g y - convexConj B f y :=
  le_antisymm (iSup_le fun w => by
      rw [← h]; exact concaveConj_sub_convexConj_le_sub B f g x w)
    (le_iSup (fun w : F => concaveConj B g w - convexConj B f w) y)

/-- **Minimizers are the points with a Kuhn–Tucker vector.** Let $f$ and $-g$ add exactly. Then
$x \in E$ minimizes $f - g$, that is, $\inf_z \{f(z) - g(z)\} = f(x) - g(x)$, if and only if
there is $y \in F$ with
$$y \in \partial f(x) \quad \text{and} \quad -y \in \partial(-g)(x).$$
-/
theorem iInf_sub_eq_iff_exists_kuhnTucker (hex : IsExactSum B f (-g)) (x : E) :
    (⨅ z, f z - g z) = f x - g x ↔
      ∃ y : F, y ∈ subdifferential B f x ∧ -y ∈ subdifferential B (fun z => -(g z)) x := by
  have hpf : ProperConvex f := hex.properConvex_left
  have hpg : ProperConvex fun z => -(g z) := hex.properConvex_right
  constructor
  · intro hmin
    obtain ⟨y, hy⟩ := exists_concaveConj_sub_convexConj_eq hex
    exact ⟨y, (sub_eq_concaveConj_sub_convexConj_iff hpf hpg).1 (hmin.symm.trans hy.symm)⟩
  · rintro ⟨y, hy⟩
    exact iInf_sub_eq_of_sub_eq ((sub_eq_concaveConj_sub_convexConj_iff hpf hpg).2 hy)

end Optimality

/-!
### Optimality conditions with a linear map

A pair $(x, z)$ is optimal for the problems $\inf (f - g \circ A)$ and $\sup (g^* - f^* \circ A')$
if and only if $A' z \in \partial f(x)$ and $Ax$ is in the superdifferential of $g^*$ at $z$. The
superdifferential of a concave function is $-\partial$ of its negative, so the second condition is
$-z \in \partial(-g)(Ax)$, and no new notion is needed.

These are the Kuhn–Tucker conditions for the pair of programs with a linear map.
-/

section OptimalityComp

variable {E F G H : Type*}
  [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G] [AddCommGroup H] [Module ℝ H]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {B' : G →ₗ[ℝ] H →ₗ[ℝ] ℝ}
  {A : E →ₗ[ℝ] G} {A' : H →ₗ[ℝ] F} {f : E → EReal} {g : G → EReal} {x : E} {z : H}

/-- **Weak duality with a linear map.** Let $A : E \to G$ and $A' : H \to F$ be adjoint. Then for
every $x \in E$ and $z \in H$,
$$g^*(z) - f^*(A' z) \le f(x) - g(Ax).$$
No other hypothesis is needed. -/
theorem concaveConj_sub_convexConj_comp_le_sub (hA : IsAdjointPair B B' A A') (x : E) (z : H) :
    concaveConj B' g z - convexConj B f (A' z) ≤ f x - g (A x) := by
  refine sub_le_sub_of_le_sub_of_sub_le (p := B x (A' z)) ?_ (sub_le_convexConj B f x (A' z))
  rw [← hA x z]
  exact concaveConj_le_sub B' g (A x) z

/-- **The Fenchel optimality conditions with a linear map.** Let $A : E \to G$ and $A' : H \to F$ be
adjoint, let $f$ be proper and let $-g$ be proper. Then for $x \in E$ and $z \in H$,
$$f(x) - g(Ax) = g^*(z) - f^*(A' z) \iff A' z \in \partial f(x) \text{ and } -z \in
  \partial(-g)(Ax).$$

The proof is the proof for $A = \mathrm{id}$, with the common finite value $\langle x, A' z
\rangle = \langle Ax, z \rangle$. -/
theorem sub_comp_eq_concaveConj_sub_convexConj_iff (hA : IsAdjointPair B B' A A')
    (hpf : ProperConvex f)
    (hpg : ProperConvex fun w => -(g w)) :
    f x - g (A x) = concaveConj B' g z - convexConj B f (A' z) ↔
      A' z ∈ subdifferential B f x ∧ -z ∈ subdifferential B' (fun w => -(g w)) (A x) := by
  have hgt : g (A x) ≠ ⊤ := fun hc => hpg.ne_bot (A x) (by rw [hc, EReal.neg_top])
  have hdc : (concaveDom g).Nonempty := by
    rw [concaveDom_eq_convexDom_neg]
    exact hpg.convexDom_nonempty
  have hp : ((B' (A x) z : ℝ) : EReal) = ((B x (A' z) : ℝ) : EReal) := by rw [hA x z]
  have h2 : g (A x) + concaveConj B' g z ≤ ((B x (A' z) : ℝ) : EReal) := by
    rw [← hp]
    exact add_concaveConj_le B' g (A x) z
  rw [sub_eq_sub_iff_of_le (hpf.ne_bot x) hgt (concaveConj_ne_top hdc z)
      (convexConj_ne_bot hpf.convexDom_nonempty (A' z)) (EReal.coe_ne_bot _)
      (EReal.coe_ne_top _)
      (le_add_convexConj (hpf.ne_bot x) hpf.convexDom_nonempty (A' z)) h2,
    hpf.mem_subdifferential_iff_add_convexConj_eq,
    neg_mem_subdifferential_neg_iff_add_concaveConj_eq (B := B') (g := g) (x := A x) (y := z) hpg,
    hp]

/-- Let $A$ and $A'$ be adjoint. If $f(x) - g(Ax) = g^*(z) - f^*(A' z)$, then $x$ minimizes
$f - g \circ A$. -/
theorem iInf_sub_comp_eq_of_sub_eq (hA : IsAdjointPair B B' A A')
    (h : f x - g (A x) = concaveConj B' g z - convexConj B f (A' z)) :
    (⨅ w, f w - g (A w)) = f x - g (A x) :=
  le_antisymm (iInf_le _ x) (le_iInf fun w => by
    rw [h]; exact concaveConj_sub_convexConj_comp_le_sub hA w z)

/-- Let $A$ and $A'$ be adjoint. If $f(x) - g(Ax) = g^*(z) - f^*(A' z)$, then $z$ maximizes
$w \mapsto g^*(w) - f^*(A' w)$. -/
theorem iSup_sub_comp_eq_of_sub_eq (hA : IsAdjointPair B B' A A')
    (h : f x - g (A x) = concaveConj B' g z - convexConj B f (A' z)) :
    (⨆ w : H, concaveConj B' g w - convexConj B f (A' w)) = concaveConj B' g z
        - convexConj B f (A' z) :=
  le_antisymm (iSup_le fun w => by
      rw [← h]; exact concaveConj_sub_convexConj_comp_le_sub hA x w)
    (le_iSup (fun w : H => concaveConj B' g w - convexConj B f (A' w)) z)

/-- **Minimizers with a linear map are the points with a Kuhn–Tucker vector.** Let $A : E \to G$ and
$A' : H \to F$ be adjoint, let $f$ and $-(g \circ A)$ add exactly, and let $-g$ pull back
exactly along $A$. Then $x \in E$ minimizes $f - g \circ A$ if and only if there is $z \in H$
with
$$A' z \in \partial f(x) \quad \text{and} \quad -z \in \partial(-g)(Ax).$$

The forward implication uses the attainment of the dual supremum to obtain $z$. The reverse
implication is weak duality. -/
theorem iInf_sub_comp_eq_iff_exists_kuhnTucker (hA : IsAdjointPair B B' A A')
    (hex : IsExactSum B f fun w => -(g (A w)))
    (himg : IsExactImage B B' A A' hA fun w => -(g w)) (x : E) :
    (⨅ w, f w - g (A w)) = f x - g (A x) ↔
      ∃ z : H, A' z ∈ subdifferential B f x ∧ -z ∈ subdifferential B' (fun w => -(g w)) (A x) := by
  have hpf : ProperConvex f := hex.properConvex_left
  have hpg : ProperConvex fun w => -(g w) := himg.proper
  constructor
  · intro hmin
    obtain ⟨z, hz⟩ := exists_concaveConj_sub_convexConj_comp_eq hA hex himg
    exact ⟨z, (sub_comp_eq_concaveConj_sub_convexConj_iff hA hpf hpg).1 (hmin.symm.trans hz.symm)⟩
  · rintro ⟨z, hz⟩
    exact iInf_sub_comp_eq_of_sub_eq
        hA ((sub_comp_eq_concaveConj_sub_convexConj_iff hA hpf hpg).2 hz)

end OptimalityComp

/-! ### Minimizing over a convex cone -/

section Cone

open Pointwise

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {f : E → EReal} {K : Set E} {x : E} {y : F}

/-- A vector $y$ is in $K^* = -K^\circ$ if and only if $\langle z, y \rangle \ge 0$ for all
$z \in K$. Negation of a set is a preimage, so $y \in -K^\circ$ means $-y \in K^\circ$. -/
theorem mem_neg_polarCone : y ∈ -(polarCone B K) ↔ ∀ z ∈ K, 0 ≤ B z y := by
  simp [Set.mem_neg, mem_polarCone, map_neg]

omit [Module ℝ F] in
/-- For a set $S$ and a point $w$, $\delta(w \mid -S) = \delta(-w \mid S)$. -/
private theorem indicatorFn_neg_set (S : Set F) (w : F) :
    indicatorFn (-S) w = indicatorFn S (-w) := by
  by_cases hw : -w ∈ S
  · rw [indicatorFn_of_mem (Set.mem_neg.2 hw), indicatorFn_of_mem hw]
  · rw [indicatorFn_of_notMem fun hc => hw (Set.mem_neg.1 hc), indicatorFn_of_notMem hw]

/-- Let $\varphi : \alpha \to [-\infty, +\infty]$ never take the value $-\infty$, and let
$S \subseteq \alpha$. Then $\inf_{z \in S} \varphi(z) = \inf_z \{\varphi(z) + \delta(z \mid
S)\}$. -/
theorem iInf_mem_eq_iInf_add_indicatorFn {α : Type*} (φ : α → EReal) (S : Set α)
    (hb : ∀ z, φ z ≠ ⊥) : (⨅ z ∈ S, φ z) = ⨅ z, (φ + indicatorFn S) z := by
  refine iInf_congr fun z => ?_
  by_cases hz : z ∈ S
  · rw [iInf_pos hz, Pi.add_apply, indicatorFn_of_mem hz, add_zero]
  · rw [iInf_neg hz, Pi.add_apply, indicatorFn_of_notMem hz]
    exact (EReal.add_top_of_ne_bot (hb z)).symm

/-- **The cone form, with indicator functions.** Let $K \subseteq E$ be a nonempty cone, and let $f$
and $\delta(\cdot \mid K)$ add exactly. Then
$$\inf_z \bigl\{ f(z) + \delta(z \mid K) \bigr\} = -\inf_w \bigl\{ f^*(w) + \delta(w \mid K^*)
  \bigr\}, \qquad K^* = -K^\circ.$$

The proof does not use the duality with $g = -\delta(\cdot \mid K)$. It applies
$\inf h = -h^*(0)$ to $h = f + \delta(\cdot \mid K)$, splits the conjugate of the sum at the
origin, and evaluates the conjugate of the indicator function. The term $0 - y$ of the splitting
is the change of sign from $K^\circ$ to $K^*$. -/
theorem iInf_add_indicatorFn_eq_neg_iInf_convexConj_add_indicatorFn
    (hex : IsExactSum B f (indicatorFn K)) (hK : IsCone K) (hne : K.Nonempty) :
    (⨅ z, (f + indicatorFn K) z) = -(⨅ w, (convexConj B f + indicatorFn (-(polarCone B K))) w) := by
  rw [iInf_eq_neg_convexConj_zero B, hex.convexConj_add_apply 0,
    ← (neg_surjective (G := F)).iInf_comp]
  congr 1
  refine iInf_congr fun w => ?_
  rw [Pi.add_apply, convexConj_indicatorFn_eq_indicatorFn_polarCone hK hne, zero_sub, neg_neg,
    indicatorFn_neg_set]

/-- **The cone form of Fenchel's duality theorem.** Let $K \subseteq E$ be a nonempty cone, and let
$f$ and the indicator function $\delta(\cdot \mid K)$ add exactly. Then
$$\inf_{x \in K} f(x) = -\inf_{y \in K^*} f^*(y), \qquad K^* = -K^\circ = \{y : \langle x, y
  \rangle \ge 0 \text{ for all } x \in K\}.$$

This is the special case $g = -\delta(\cdot \mid K)$ of Fenchel's duality theorem. A cone is
`ConvexAnalysis.IsCone`, a set closed under multiplication by positive scalars. -/
theorem iInf_mem_eq_neg_iInf_mem_neg_polarCone (hex : IsExactSum B f (indicatorFn K))
    (hK : IsCone K) (hne : K.Nonempty) :
    (⨅ z ∈ K, f z) = -(⨅ w ∈ -(polarCone B K), convexConj B f w) := by
  rw [iInf_mem_eq_iInf_add_indicatorFn f K hex.properConvex_left.ne_bot,
    iInf_mem_eq_iInf_add_indicatorFn (convexConj B f)
        _ (convexConj_ne_bot hex.properConvex_left.convexDom_nonempty)]
  exact iInf_add_indicatorFn_eq_neg_iInf_convexConj_add_indicatorFn hex hK hne

/-- **Weak duality for the cone program.** If $x \in K$ and $w \in K^*$, then $-f^*(w) \le f(x)$. -/
theorem neg_convexConj_le_of_mem_neg_polarCone (hxK : x ∈ K) {w : F} (hwK : w ∈ -(polarCone B K)) :
    -(convexConj B f w) ≤ f x := by
  have hle : -(f x) ≤ convexConj B f w := by
    refine le_trans (le_of_eq (zero_sub (f x)).symm) (le_trans ?_ (sub_le_convexConj B f x w))
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add (by exact_mod_cast mem_neg_polarCone.1 hwK x hxK) le_rfl
  rw [← EReal.neg_le_neg_iff, neg_neg] at hle
  exact hle

/-- Let $f$ be proper. If $f(x) + f^*(y) = 0$, then $-f^*(y) = f(x)$. -/
private theorem neg_convexConj_eq_of_add_eq_zero (hp : ProperConvex f)
    (hz : f x + convexConj B f y = 0) :
    -(convexConj B f y) = f x := by
  have hcb : convexConj B f y ≠ ⊥ := convexConj_ne_bot hp.convexDom_nonempty y
  have hfb : f x ≠ ⊥ := hp.ne_bot x
  have hft : f x ≠ ⊤ := fun hc => by
    rw [hc, EReal.top_add_of_ne_bot hcb] at hz
    exact absurd hz (by simp)
  have hct : convexConj B f y ≠ ⊤ := fun hc => by
    rw [hc, EReal.add_top_of_ne_bot hfb] at hz
    exact absurd hz (by simp)
  obtain ⟨r, hr⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hfb (lt_top_iff_ne_top.2 hft)
  obtain ⟨s, hs⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hcb (lt_top_iff_ne_top.2 hct)
  rw [hr, hs, ← EReal.coe_add] at hz
  rw [hs, hr, ← EReal.coe_neg, EReal.coe_eq_coe_iff]
  have : r + s = 0 := by exact_mod_cast hz
  linarith

/-- **Optimality conditions for the cone program.** Let $f$ be proper, $x \in K$ and $y \in K^*$.
Then
$$f(x) + f^*(y) = 0 \iff y \in \partial f(x) \text{ and } \langle x, y \rangle = 0.$$
These are the Fenchel optimality conditions for $g = -\delta(\cdot \mid K)$. -/
theorem add_convexConj_eq_zero_iff_mem_subdifferential_and_pairing_eq_zero (hp : ProperConvex f)
    (hxK : x ∈ K)
    (hyK : y ∈ -(polarCone B K)) :
    f x + convexConj B f y = 0 ↔ y ∈ subdifferential B f x ∧ (B x y : ℝ) = 0 := by
  have hxy : (0 : ℝ) ≤ B x y := mem_neg_polarCone.1 hyK x hxK
  rw [hp.mem_subdifferential_iff_add_convexConj_eq]
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, EReal.coe_zero]⟩
  have hle : ((B x y : ℝ) : EReal) ≤ 0 := h ▸ hp.le_add_convexConj x y
  have hzero : (B x y : ℝ) = 0 := le_antisymm (by exact_mod_cast hle) hxy
  exact ⟨by rw [h, hzero, EReal.coe_zero], hzero⟩

/-- If $y \in K^*$, $y \in \partial f(x)$ and $\langle x, y \rangle = 0$, then $f(x) \le f(z)$ for
all $z \in K$. The proof uses only these three conditions. -/
theorem forall_le_of_mem_subdifferential_of_pairing_eq_zero (hyK : y ∈ -(polarCone B K))
    (hy : y ∈ subdifferential B f x) (hxy : (B x y : ℝ) = 0) {z : E} (hz : z ∈ K) : f x ≤ f z := by
  have hzy : (0 : ℝ) ≤ B (z - x) y := by
    rw [map_sub, LinearMap.sub_apply, hxy, sub_zero]
    exact mem_neg_polarCone.1 hyK z hz
  exact le_trans (le_add_of_nonneg_right (by exact_mod_cast hzy)) (hy z)

/-- Let $f$ be proper and $x \in K$. If $y \in \partial f(x)$ and $\langle x, y \rangle = 0$, then
$f^*(y) \le f^*(w)$ for all $w \in K^*$. -/
theorem convexConj_le_convexConj_of_mem_subdifferential_of_pairing_eq_zero (hp : ProperConvex f)
    (hxK : x ∈ K)
    (hy : y ∈ subdifferential B f x) (hxy : (B x y : ℝ) = 0) {w : F} (hwK : w ∈ -(polarCone B K)) :
    convexConj B f y ≤ convexConj B f w := by
  have hsum : f x + convexConj B f y = 0 := by
    rw [hp.mem_subdifferential_iff_add_convexConj_eq.1 hy, hxy, EReal.coe_zero]
  have hxeq : -(convexConj B f y) = f x := neg_convexConj_eq_of_add_eq_zero hp hsum
  rw [← EReal.neg_le_neg_iff, hxeq]
  exact neg_convexConj_le_of_mem_neg_polarCone hxK hwK

/-! ### Attainment of the two infima -/

/-- **The dual value at the origin.** Let $K$ be a nonempty cone, and let $f$ and
$\delta(\cdot \mid K)$ add exactly. Then
$$\bigl(f + \delta(\cdot \mid K)\bigr)^*(0) = \inf_{w \in K^*} f^*(w).$$
This identity turns exact addition into attainment. -/
theorem convexConj_add_indicatorFn_zero_eq_iInf_mem_neg_polarCone
    (hex : IsExactSum B f (indicatorFn K)) (hK : IsCone K) (hne : K.Nonempty) :
    convexConj B (f + indicatorFn K) 0 = ⨅ w ∈ -(polarCone B K), convexConj B f w := by
  rw [convexConj_apply_zero, ← iInf_mem_eq_iInf_add_indicatorFn f K hex.properConvex_left.ne_bot,
    iInf_mem_eq_neg_iInf_mem_neg_polarCone hex hK hne, neg_neg]

/-- **Attainment of the dual infimum under condition (a).** Let $K \subseteq E$ be a nonempty cone,
and let $f$ and $\delta(\cdot \mid K)$ add exactly. Then there is $y \in K^*$ with
$$f^*(y) = \inf_{w \in K^*} f^*(w).$$

The point $y$ comes from the definition of exact addition: in the splitting $0 = y_1 + y_2$ at
the origin, $y_1 \in K^*$ is a minimizer, since the second conjugate is the indicator function
of $K^\circ$. In the degenerate case $y_2 \notin K^\circ$, the dual infimum is $+\infty$, and it
is attained at the origin. -/
theorem exists_mem_neg_polarCone_convexConj_eq_iInf (hex : IsExactSum B f (indicatorFn K))
    (hK : IsCone K) (hne : K.Nonempty) :
    ∃ y ∈ -(polarCone B K), convexConj B f y = ⨅ w ∈ -(polarCone B K), convexConj B f w := by
  obtain ⟨y₁, y₂, hsum, hle⟩ := hex.exact_le 0
  rw [convexConj_indicatorFn_eq_indicatorFn_polarCone hK hne,
    convexConj_add_indicatorFn_zero_eq_iInf_mem_neg_polarCone hex hK hne] at hle
  by_cases hy₂ : y₂ ∈ polarCone B K
  · have hy₁ : y₁ ∈ -(polarCone B K) := by
      rw [Set.mem_neg, neg_eq_of_add_eq_zero_right hsum]
      exact hy₂
    rw [indicatorFn_of_mem hy₂, add_zero] at hle
    exact ⟨y₁, hy₁, le_antisymm hle (iInf₂_le y₁ hy₁)⟩
  · rw [indicatorFn_of_notMem hy₂,
      EReal.add_top_of_ne_bot (hex.convexConj_left_ne_bot y₁)] at hle
    have h0 : (0 : F) ∈ -(polarCone B K) := zero_mem_neg_polarCone B K
    have htop : (⨅ w ∈ -(polarCone B K), convexConj B f w) = ⊤ := top_le_iff.1 hle
    have hge : (⨅ w ∈ -(polarCone B K), convexConj B f w) ≤ convexConj B f 0 := iInf₂_le (0 : F) h0
    rw [htop, top_le_iff] at hge
    exact ⟨0, h0, by rw [hge, htop]⟩

/-- Let $K$ be a nonempty cone, let $f$ and $\delta(\cdot \mid K)$ add exactly, and let the dual
infimum $\inf_{w \in K^*} f^*(w)$ be finite. Then
$$\inf_{x \in K} f(x) + \inf_{w \in K^*} f^*(w) = 0.$$
-/
theorem iInf_mem_add_iInf_mem_neg_polarCone_eq_zero (hex : IsExactSum B f (indicatorFn K))
    (hK : IsCone K) (hne : K.Nonempty)
    (hbot : (⨅ w ∈ -(polarCone B K), convexConj B f w) ≠ ⊥)
    (htop : (⨅ w ∈ -(polarCone B K), convexConj B f w) ≠ ⊤) :
    (⨅ z ∈ K, f z) + (⨅ w ∈ -(polarCone B K), convexConj B f w) = 0 := by
  obtain ⟨m, hm⟩ := EReal.exists_coe_of_ne_bot_of_lt_top hbot (lt_top_iff_ne_top.2 htop)
  rw [iInf_mem_eq_neg_iInf_mem_neg_polarCone hex hK hne, hm, ← EReal.coe_neg,
    ← EReal.coe_add, neg_add_cancel, EReal.coe_zero]

/-! ### Minimizing over a subspace -/

/-- For a subspace $L$ of $E$, the polar cone is closed under negation, so $-L^\circ = L^\circ$.
Both are the annihilator $L^\perp = \{y : \langle x, y \rangle = 0 \text{ for all } x \in L\}$. -/
theorem neg_polarCone_coe_submodule (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (M : Submodule ℝ E) :
    -(polarCone B (M : Set E)) = polarCone B (M : Set E) := by
  ext w
  rw [Set.mem_neg, polarCone_coe_submodule']
  refine ⟨fun h u hu => ?_, fun h u hu => ?_⟩
  · have hu' := h u hu
    rwa [map_neg, neg_eq_zero] at hu'
  · rw [map_neg, h u hu, neg_zero]

/-- **The subspace form of Fenchel's duality theorem.** Let $L$ be a subspace of $E$, and let $f$
and $\delta(\cdot \mid L)$ add exactly. Then
$$\inf_{x \in L} f(x) = -\inf_{y \in L^\perp} f^*(y).$$

Here $K^* = -L^\circ$ is equal to $L^\circ = L^\perp$. The subspace is `M : Submodule ℝ E`. -/
theorem iInf_mem_submodule_eq_neg_iInf_mem_polarCone {M : Submodule ℝ E}
    (hex : IsExactSum B f (indicatorFn (M : Set E))) :
    (⨅ z ∈ (M : Set E), f z) = -(⨅ w ∈ polarCone B (M : Set E), convexConj B f w) := by
  have h := iInf_mem_eq_neg_iInf_mem_neg_polarCone hex (isCone_coe_submodule M)
    ⟨0, M.zero_mem⟩
  rwa [neg_polarCone_coe_submodule] at h

/-- Let $L$ be a subspace of $E$, let $f$ be proper, $x \in L$ and $y \in L^\perp$. Then
$f(x) + f^*(y) = 0$ if and only if $y \in \partial f(x)$. The condition
$\langle x, y \rangle = 0$ holds automatically. -/
theorem add_convexConj_eq_zero_iff_mem_subdifferential_of_mem_submodule {M : Submodule ℝ E}
    (hp : ProperConvex f) (hxM : x ∈ M) (hyM : y ∈ polarCone B (M : Set E)) :
    f x + convexConj B f y = 0 ↔ y ∈ subdifferential B f x := by
  have hxy : (B x y : ℝ) = 0 := by
    rw [polarCone_coe_submodule'] at hyM
    exact hyM x hxM
  have hyK : y ∈ -(polarCone B (M : Set E)) := by
    rw [neg_polarCone_coe_submodule]
    exact hyM
  rw [add_convexConj_eq_zero_iff_mem_subdifferential_and_pairing_eq_zero hp hxM hyK]
  exact ⟨And.left, fun h => ⟨h, hxy⟩⟩

end Cone

/-!
### Attainment of the primal infimum

Attainment of the primal infimum is condition (b) of [rockafellar1970convex], which is condition (a)
for the dual pair. The result of the previous section is applied to $f^*$ and $K^*$, and the
identities $K^{**} = K$ (`ConvexAnalysis.neg_polarCone_neg_polarCone`) and $f^{**} = f$ (the
Fenchel–Moreau theorem) complete the argument. The bipolar identity is the reason for the
topological hypotheses of this section.
-/

section ConeClosed

open Pointwise

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} [IsCompatiblePairing B] {f : E → EReal} {K : Set E}

/-- **Attainment of the primal infimum under condition (b).** Let $E$ be a locally convex real
topological vector space with a compatible pairing. Let $f$ satisfy $f^{**} = f$, let
$K \subseteq E$ be a nonempty closed convex cone, and let $f^*$ and $\delta(\cdot \mid K^*)$ add
exactly for the flipped pairing. Then there is $x \in K$ with
$$f(x) = \inf_{z \in K} f(z).$$

The hypothesis $f^{**} = f$ is `ConvexAnalysis.convexBiconj B f = f`. It is a hypothesis and is
not derived, so that the statement needs no compatibility condition on the side of $F$. -/
theorem exists_mem_eq_iInf_of_isExactSum_convexConj (hbi : convexBiconj B f = f)
    (hex : IsExactSum B.flip (convexConj B f) (indicatorFn (-(polarCone B K))))
    (hconv : Convex ℝ K) (hK : IsCone K) (hne : K.Nonempty)
    (hcl : IsClosed K) :
    ∃ x ∈ K, f x = ⨅ z ∈ K, f z := by
  have hbi' : convexConj B.flip (convexConj B f) = f := hbi
  have h := exists_mem_neg_polarCone_convexConj_eq_iInf (B := B.flip) (K := -(polarCone B K)) hex
    (isCone_iff_smul_eq.2 (smul_neg_polarCone B K)) (neg_polarCone_nonempty B K)
  rwa [neg_polarCone_neg_polarCone hconv hK hne hcl, hbi'] at h

end ConeClosed

end ConvexAnalysis
