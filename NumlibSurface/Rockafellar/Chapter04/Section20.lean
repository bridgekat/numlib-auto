/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Polyhedral.Closedness
import Numlib.Analysis.Convex.Polyhedral.Simplicial
import NumlibSurface.Rockafellar.Chapter03.Section11
import NumlibSurface.Rockafellar.Chapter03.Section12
import NumlibSurface.Rockafellar.Chapter03.Section16

/-!
# Rockafellar, Section 20: Some applications of polyhedral convexity

This module formalizes §20 of [rockafellar1970convex]: the conjugacy formulas, separation theorems
and closedness conditions of Parts II and III, sharpened when some of the convex sets or functions
are polyhedral. All eight numbered results are formalized: Theorems 20.1–20.5 and Corollaries
20.1.1, 20.2.1 and 20.3.1, together with the computation for two polyhedral functions in the opening
paragraph of the section. The proofs specialize `Numlib.Analysis.Convex.Duality.Exact`,
`Numlib.Analysis.Convex.Polyhedral.Closedness` and `Numlib.Analysis.Convex.Polyhedral.Simplicial`,
and the surface modules for §11, §12 and §16.

Theorem 16.4 gives $(f_1 + \cdots + f_m)^* = f_1^* \mathbin{\square} \cdots \mathbin{\square}
f_m^*$, with attainment, when the sets $\operatorname{ri}(\operatorname{dom} f_i)$ have a common
point. Theorem 20.1 says that for a polyhedral summand $f_i$ the set $\operatorname{dom} f_i$ can
replace $\operatorname{ri}(\operatorname{dom} f_i)$ in this intersection; when all summands are
polyhedral, no relative interior appears. In the same way, a polyhedral set $C_1$ needs weaker
hypotheses for separation (Theorem 20.2) and for the closedness of $C_1 + C_2$ (Theorem 20.3).

## Main definitions

* Definition of a polyhedral convex set in the words of §19, `Rockafellar.IsPolyhedral`: an
  intersection of finitely many closed half-spaces $\{x \mid \langle x, b_i \rangle \le \beta_i\}$.
* Separation that does not contain the second set, `Rockafellar.SeparableProperlyNotContaining`: a
  hyperplane separates $C_1$ and $C_2$ properly and does not contain $C_2$.

## Main results

* The computation in the opening paragraph, `Rockafellar.theorem_20_1_pair_exact`,
  `Rockafellar.theorem_20_1_pair_attained`: $(f + g)^* = f^* \mathbin{\square} g^*$, with
  attainment, for proper polyhedral $f$ and $g$ with $\operatorname{dom} f \cap \operatorname{dom} g
  \neq \emptyset$.
* Theorem 20.1, `Rockafellar.theorem_20_1_exact`, `Rockafellar.theorem_20_1_attained`,
  `Rockafellar.theorem_20_1_exact_finset`, `Rockafellar.theorem_20_1_attained_finset`: the same
  formula when $f_1, \dots, f_k$ are polyhedral and $\operatorname{dom} f_1 \cap \cdots \cap
  \operatorname{dom} f_k \cap \operatorname{ri}(\operatorname{dom} f_{k+1}) \cap \cdots \cap
  \operatorname{ri}(\operatorname{dom} f_m) \neq \emptyset$.
* Corollary 20.1.1, `Rockafellar.corollary_20_1_1`, `Rockafellar.corollary_20_1_1_attained`,
  `Rockafellar.corollary_20_1_1_finset`, `Rockafellar.corollary_20_1_1_attained_finset`: under the
  dual condition on the conjugates, the infimal convolution of closed proper convex functions is
  closed proper convex, and its infimum is attained.
* Theorem 20.2, `Rockafellar.theorem_20_2`: for polyhedral $C_1$, a hyperplane separates $C_1$ and
  $C_2$ properly without containing $C_2$ if and only if
  $C_1 \cap \operatorname{ri} C_2 = \emptyset$.
* Corollary 20.2.1, `Rockafellar.corollary_20_2_1`: the same condition in terms of support
  functions.
* Theorem 20.3, `Rockafellar.theorem_20_3`: for polyhedral $C_1$ and closed $C_2$, the set
  $C_1 + C_2$ is closed under a recession condition.
* Corollary 20.3.1, `Rockafellar.corollary_20_3_1`: for polyhedral $C_1$ and closed $C_2$,
  disjointness and a recession condition give strong separation.
* Theorem 20.4, `Rockafellar.theorem_20_4`: a closed bounded set $C$ in the interior of a convex set
  $D$ lies in the interior of a polyhedral convex set $P \subseteq \operatorname{int} D$.
* Theorem 20.5, `Rockafellar.theorem_20_5`, `Rockafellar.theorem_20_5_polytope`: polyhedral convex
  sets and polytopes are locally simplicial.

## Proof outline

The asymmetry in Theorem 20.1 comes from two results of §7 on segments. A proper polyhedral convex
function is closed, so Corollary 7.5.1 needs only a point of $\operatorname{dom} f$, while Theorem
7.5 for a general convex function $g$ needs a point of $\operatorname{ri}(\operatorname{dom} g)$.

## Implementation notes

* The $m$-ary statements are proved for the whole family, not by induction from the binary ones. The
  family is indexed by a `Finset` `s` that is the disjoint union of the polyhedral indices `t` and
  the other indices `u`, stated by membership, so that no statement needs a `DecidableEq` instance.
* The common conclusion of Theorems 16.4 and 20.1 is the backbone predicate
  `ConvexAnalysis.IsExactSum` for two functions and `ConvexAnalysis.IsExactFinsetSum` for a finite
  family: the summands are proper, and the infimum that defines the infimal convolution of the
  conjugates is attained at every point.
* `Rockafellar.IsPolyhedral` quantifies over vectors $b_i$, as the source does. It agrees with the
  backbone notion `ConvexAnalysis.Polyhedral`, which quantifies over linear functionals, by
  `Rockafellar.isPolyhedral_iff_polyhedral`. A polyhedral convex function is
  `ConvexAnalysis.PolyhedralFn`.

## Deviations from the source

* **Theorem 20.4** (generalization). The source assumes $C$ non-empty and convex; neither hypothesis
  is needed. See `Rockafellar.theorem_20_4`.
-/

open Set Pointwise

namespace Rockafellar

open ConvexAnalysis

variable {n : ℕ}

/-! ### Polyhedral convex sets, in the words of the source -/

/-- **Section 19** of [rockafellar1970convex] (page 170), definition of a polyhedral convex set. A
set $C \subseteq \mathbb{R}^n$ is a **polyhedral convex set** if it is the intersection of
finitely many closed half-spaces
$$C = \{x \mid \langle x, b_i \rangle \le \beta_i,\ i = 1, \dots, m\}, \qquad b_i \in
  \mathbb{R}^n,\ \beta_i \in \mathbb{R}.$$

The statements below use this definition, and the proofs pass to `ConvexAnalysis.Polyhedral` by
`Rockafellar.isPolyhedral_iff_polyhedral`. -/
def IsPolyhedral (C : Set (Rn n)) : Prop :=
  ∃ s : Finset (Rn n × ℝ), C = {x | ∀ q ∈ s, pairing n x q.1 ≤ q.2}

/-- A set $C \subseteq \mathbb{R}^n$ is an intersection of finitely many half-spaces
$\{x \mid \langle x, b_i \rangle \le \beta_i\}$ given by vectors $b_i$ if and only if it is the
solution set of finitely many inequalities $\varphi_i(x) \le \beta_i$ given by linear
functionals $\varphi_i$. The round trip between vectors and functionals is `Rockafellar.linFn`
and `Rockafellar.exists_linFn`. -/
theorem isPolyhedral_iff_polyhedral {C : Set (Rn n)} : IsPolyhedral C ↔ Polyhedral C := by
  classical
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨s.image fun q => ((linFn q.1 : Rn n →ₗ[ℝ] ℝ), q.2), Set.ext fun x => ?_⟩
    constructor
    · refine fun hx => Finset.forall_mem_image.2 fun q hq => ?_
      change (linFn q.1) x ≤ q.2
      rw [linFn_apply]
      exact hx q hq
    · intro hx q hq
      have hq' : (linFn q.1) x ≤ q.2 := Finset.forall_mem_image.1 hx hq
      rwa [linFn_apply] at hq'
  · rintro ⟨s, rfl⟩
    have hrep : ∀ φ : Rn n →ₗ[ℝ] ℝ, ∃ b : Rn n, ∀ x, pairing n x b = φ x := by
      intro φ
      obtain ⟨b, hb⟩ := exists_linFn (LinearMap.toContinuousLinearMap φ)
      exact ⟨b, fun x => by rw [← linFn_apply, hb]; simp⟩
    choose rep hrep using hrep
    refine ⟨s.image fun q => (rep q.1, q.2), Set.ext fun x => ?_⟩
    constructor
    · refine fun hx => Finset.forall_mem_image.2 fun q hq => ?_
      change pairing n x (rep q.1) ≤ q.2
      rw [hrep]
      exact hx q hq
    · intro hx q hq
      have hq' : pairing n x (rep q.1) ≤ q.2 := Finset.forall_mem_image.1 hx hq
      rwa [hrep] at hq'

/-! ### Separation that does not contain the second set -/

/-- **Section 20** of [rockafellar1970convex] (page 181). The sets $C_1, C_2 \subseteq \mathbb{R}^n$
are **properly separable by a hyperplane not containing $C_2$** if there are
$b \in \mathbb{R}^n$ and $\beta \in \mathbb{R}$ such that the hyperplane
$\{x \mid \langle x, b \rangle = \beta\}$ separates $C_1$ and $C_2$ properly and does not
contain $C_2$.

The sides are as in §11: $C_1$ lies in the closed half-space
$\{x \mid \langle x, b \rangle \ge \beta\}$ and $C_2$ in the opposite one. Proper separation is
`Rockafellar.SeparatesProperlyRn`, which includes $b \neq 0$. -/
def SeparableProperlyNotContaining (C₁ C₂ : Set (Rn n)) : Prop :=
  ∃ (b : Rn n) (β : ℝ), SeparatesProperlyRn b β C₁ C₂ ∧ ¬ C₂ ⊆ {x | pairing n x b = β}

/-- Let $C_1, C_2 \subseteq \mathbb{R}^n$ be non-empty. Then $C_1$ and $C_2$ are properly separable
by a hyperplane not containing $C_2$ if and only if there are a continuous linear function $g$
and a number $c$ such that $g$ and $c$ separate $C_1$ and $C_2$ in the sense of
`ConvexAnalysis.Separates`, and $C_2$ is not contained in $\{x \mid g(x) = c\}$. -/
theorem separableProperlyNotContaining_iff_exists {C₁ C₂ : Set (Rn n)}
    (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty) :
    SeparableProperlyNotContaining C₁ C₂ ↔
      ∃ (g : Rn n →L[ℝ] ℝ) (c : ℝ), Separates g c C₁ C₂ ∧ ¬ C₂ ⊆ {x | g x = c} := by
  constructor
  · rintro ⟨b, β, ⟨-, hsep⟩, hns⟩
    refine ⟨-linFn b, -β, hsep.toSeparates.symm, fun hcon => hns fun x hx => ?_⟩
    simpa using hcon hx
  · rintro ⟨g, c, hsep, hns⟩
    have hprop : SeparatesProperly g c C₁ C₂ :=
      ⟨hsep, fun hcon => hns fun x hx => hcon (Set.mem_union_right _ hx)⟩
    obtain ⟨b, hb⟩ := exists_linFn (-g)
    have hb0 : b ≠ 0 := by
      intro hzero
      have hz : linFn b = 0 := linFn_eq_zero_iff.2 hzero
      rw [hb, neg_eq_zero] at hz
      exact hprop.ne_zero hne₁ hne₂ hz
    refine ⟨b, -c, ⟨hb0, by rw [hb]; exact hprop.symm⟩, fun hcon => hns fun x hx => ?_⟩
    have h : pairing n x b = -c := hcon hx
    rw [← linFn_apply, hb] at h
    simpa using h

/-! ### Theorem 20.1 and its corollary -/

/-- **Section 20** of [rockafellar1970convex] (page 179), the case of two polyhedral functions. Let
$f$ and $g$ be proper polyhedral convex functions on $\mathbb{R}^n$ with $\operatorname{dom} f
\cap \operatorname{dom} g \neq \emptyset$. Then
$$(f + g)^* = f^* \mathbin{\square} g^*.$$

No relative interior appears in the hypothesis. The source gives this computation without a
number, as the motivation for Theorem 20.1. -/
theorem theorem_20_1_pair_exact {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : ProperConvex f)
    (hg : PolyhedralFn g) (hpg : ProperConvex g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom f)
        (hxg : x₀ ∈ convexDom g) :
    convexConj (pairing n) (f + g)
        = infConv (convexConj (pairing n) f) (convexConj (pairing n) g) :=
  (IsExactSum.of_polyhedral_pair (B := pairing n) hf hpf hg hpg hxf hxg).convexConj_add

/-- **Section 20** of [rockafellar1970convex] (page 179), the case of two polyhedral functions,
attainment. Let $f$ and $g$ be proper polyhedral convex functions on $\mathbb{R}^n$ with
$\operatorname{dom} f \cap \operatorname{dom} g \neq \emptyset$. Then for every
$x^* \in \mathbb{R}^n$ there are $x_1^*, x_2^*$ with $x_1^* + x_2^* = x^*$ and
$$f^*(x_1^*) + g^*(x_2^*) = (f + g)^*(x^*),$$
so the infimum that defines $(f^* \mathbin{\square} g^*)(x^*)$ is attained. -/
theorem theorem_20_1_pair_attained {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : ProperConvex f)
    (hg : PolyhedralFn g) (hpg : ProperConvex g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom f)
        (hxg : x₀ ∈ convexDom g)
    (y : Rn n) :
    ∃ y₁ y₂ : Rn n, y₁ + y₂ = y ∧
      convexConj (pairing n) f y₁ + convexConj (pairing n) g y₂
          = convexConj (pairing n) (f + g) y :=
  (IsExactSum.of_polyhedral_pair (B := pairing n) hf hpf hg hpg hxf hxg).exists_convexConj_add_eq y

/-- **Theorem 20.1** of [rockafellar1970convex], two functions. Let $f$ and $g$ be proper convex
functions on $\mathbb{R}^n$ with $f$ polyhedral, and let $\operatorname{dom} f \cap
\operatorname{ri}(\operatorname{dom} g) \neq \emptyset$. Then
$$(f + g)^*(x^*) = (f^* \mathbin{\square} g^*)(x^*) = \inf \{f^*(x_1^*) + g^*(x_2^*) \mid
  x_1^* + x_2^* = x^*\}.$$

The polyhedral summand needs only a point of $\operatorname{dom} f$, and the other summand a
point of $\operatorname{ri}(\operatorname{dom} g)$. Compare `Rockafellar.theorem_16_4_exact`,
which needs a point of $\operatorname{ri}(\operatorname{dom} f) \cap
\operatorname{ri}(\operatorname{dom} g)$, and `Rockafellar.theorem_20_1_pair_exact`, which needs
no relative interior point. -/
theorem theorem_20_1_exact {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : ProperConvex f)
    (hg : ConvexFn g) (hpg : ProperConvex g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom f)
    (hxg : x₀ ∈ ri (convexDom g)) :
    convexConj (pairing n) (f + g)
        = infConv (convexConj (pairing n) f) (convexConj (pairing n) g) :=
  (IsExactSum.of_polyhedral (B := pairing n) hf hpf hg hpg hxf hxg).convexConj_add

/-- **Theorem 20.1** of [rockafellar1970convex], two functions, attainment. Let $f$ and $g$ be
proper convex functions on $\mathbb{R}^n$ with $f$ polyhedral, and let $\operatorname{dom} f
\cap \operatorname{ri}(\operatorname{dom} g) \neq \emptyset$. Then for every
$x^* \in \mathbb{R}^n$ there are $x_1^*, x_2^*$ with $x_1^* + x_2^* = x^*$ and
$$f^*(x_1^*) + g^*(x_2^*) = (f + g)^*(x^*),$$
so the infimum $\inf \{f^*(x_1^*) + g^*(x_2^*) \mid x_1^* + x_2^* = x^*\}$ is attained. -/
theorem theorem_20_1_attained {f g : Rn n → EReal} (hf : PolyhedralFn f) (hpf : ProperConvex f)
    (hg : ConvexFn g) (hpg : ProperConvex g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom f)
    (hxg : x₀ ∈ ri (convexDom g)) (y : Rn n) :
    ∃ y₁ y₂ : Rn n, y₁ + y₂ = y ∧
      convexConj (pairing n) f y₁ + convexConj (pairing n) g y₂
          = convexConj (pairing n) (f + g) y :=
  (IsExactSum.of_polyhedral (B := pairing n) hf hpf hg hpg hxf hxg).exists_convexConj_add_eq y

section Corollary_20_1_1

variable {f g : Rn n → EReal}

private theorem isExactSum_convexConj_of_polyhedral (hf : PolyhedralFn f)
    (hcf : ClosedProperConvexFn f) (hg : ClosedProperConvexFn g) {x₀ : Rn n}
    (hxf : x₀ ∈ convexDom (convexConj (pairing n) f))
        (hxg : x₀ ∈ ri (convexDom (convexConj (pairing n) g))) :
    IsExactSum (pairing n) (convexConj (pairing n) f) (convexConj (pairing n) g) :=
  IsExactSum.of_polyhedral (B := pairing n) (PolyhedralFn.convexConj hf)
      (properConvex_convexConj hcf)
    (convexFn_convexConj _ _) (properConvex_convexConj hg) hxf hxg

private theorem infConv_eq_convexConj_add_convexConj (hf : PolyhedralFn f)
    (hcf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom (convexConj (pairing n) f))
    (hxg : x₀ ∈ ri (convexDom (convexConj (pairing n) g))) :
    infConv f g = convexConj (pairing n) (convexConj (pairing n) f + convexConj (pairing n) g) := by
  have hff : convexConj (pairing n) (convexConj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hcf.convex]; exact hcf.closed
  have hgg : convexConj (pairing n) (convexConj (pairing n) g) = g := by
    rw [theorem_12_2_biconj hg.convex]; exact hg.closed
  rw [(isExactSum_convexConj_of_polyhedral hf hcf hg hxf hxg).convexConj_add, hff, hgg]

/-- **Corollary 20.1.1** of [rockafellar1970convex], two functions. Let $f$ and $g$ be closed proper
convex functions on $\mathbb{R}^n$ with $f$ polyhedral, and let $\operatorname{dom} f^* \cap
\operatorname{ri}(\operatorname{dom} g^*) \neq \emptyset$. Then the infimal convolution
$f \mathbin{\square} g$ is a closed proper convex function.

The proof is the one in the source: Theorem 20.1 applies to the conjugates, since $f^*$ is
polyhedral by Theorem 19.2, and the result follows by Theorem 12.2. -/
theorem corollary_20_1_1 (hf : PolyhedralFn f) (hcf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom (convexConj (pairing n) f))
    (hxg : x₀ ∈ ri (convexDom (convexConj (pairing n) g))) :
    ClosedProperConvexFn (infConv f g) := by
  have hexact := isExactSum_convexConj_of_polyhedral hf hcf hg hxf hxg
  rw [infConv_eq_convexConj_add_convexConj hf hcf hg hxf hxg]
  exact ⟨convexFn_convexConj _ _, closedConvex_convexConj, properConvex_convexConj_of_properConvex
    (ConvexFn.add (convexFn_convexConj _ _) (convexFn_convexConj _ _)
      (properConvex_convexConj hcf).ne_bot (properConvex_convexConj hg).ne_bot)
          hexact.properConvex_add⟩

/-- **Corollary 20.1.1** of [rockafellar1970convex], two functions, attainment. Let $f$ and $g$ be
closed proper convex functions on $\mathbb{R}^n$ with $f$ polyhedral, and let
$\operatorname{dom} f^* \cap \operatorname{ri}(\operatorname{dom} g^*) \neq \emptyset$. Then for
every $x$ there are $x_1, x_2$ with $x_1 + x_2 = x$ and
$f(x_1) + g(x_2) = (f \mathbin{\square} g)(x)$: the infimum that defines
$(f \mathbin{\square} g)(x)$ is attained. -/
theorem corollary_20_1_1_attained (hf : PolyhedralFn f) (hcf : ClosedProperConvexFn f)
    (hg : ClosedProperConvexFn g) {x₀ : Rn n} (hxf : x₀ ∈ convexDom (convexConj (pairing n) f))
    (hxg : x₀ ∈ ri (convexDom (convexConj (pairing n) g))) (x : Rn n) :
    ∃ x₁ x₂ : Rn n, x₁ + x₂ = x ∧ f x₁ + g x₂ = infConv f g x := by
  have hff : convexConj (pairing n) (convexConj (pairing n) f) = f := by
    rw [theorem_12_2_biconj hcf.convex]; exact hcf.closed
  have hgg : convexConj (pairing n) (convexConj (pairing n) g) = g := by
    rw [theorem_12_2_biconj hg.convex]; exact hg.closed
  obtain ⟨x₁, x₂, hsum, hval⟩ :=
    (isExactSum_convexConj_of_polyhedral hf hcf hg hxf hxg).exists_convexConj_add_eq x
  refine ⟨x₁, x₂, hsum, ?_⟩
  rw [infConv_eq_convexConj_add_convexConj hf hcf hg hxf hxg, ← hval, hff, hgg]

end Corollary_20_1_1

/-- **Theorem 20.1** of [rockafellar1970convex], $m$ functions. Let $f_1, \dots, f_m$ be proper
convex functions on $\mathbb{R}^n$ with $m \ge 1$, such that $f_1, \dots, f_k$ are polyhedral
and
$$\operatorname{dom} f_1 \cap \cdots \cap \operatorname{dom} f_k \cap
  \operatorname{ri}(\operatorname{dom} f_{k+1}) \cap \cdots \cap
  \operatorname{ri}(\operatorname{dom} f_m) \neq \emptyset.$$
Then
$$(f_1 + \cdots + f_m)^* = f_1^* \mathbin{\square} \cdots \mathbin{\square} f_m^*.$$

The functions are indexed by a non-empty `Finset` `s`. The set `t` stands for the indices
$1, \dots, k$ and the set `u` for the indices $k + 1, \dots, m$. Compare
`Rockafellar.theorem_16_4_exact_finset`, which needs a relative interior point of every domain. -/
theorem theorem_20_1_exact_finset {ι : Type*} {s t u : Finset ι} {f : ι → Rn n → EReal}
    (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, ProperConvex (f i)) {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ convexDom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (convexDom (f i))) :
    convexConj (pairing n) (∑ i ∈ s, f i)
      = ofInfConvFn (∑ i ∈ s, toInfConvFn (convexConj (pairing n) (f i))) :=
  (IsExactFinsetSum.of_polyhedral (B := pairing n) hs hdisj hmem hpoly hconv hpf hxt
    hxu).convexConj_finsetSum

/-- **Theorem 20.1** of [rockafellar1970convex], $m$ functions, attainment. Under the hypotheses of
`Rockafellar.theorem_20_1_exact_finset`, for every $x^* \in \mathbb{R}^n$ there are
$x_1^*, \dots, x_m^*$ with $x_1^* + \cdots + x_m^* = x^*$ and
$$f_1^*(x_1^*) + \cdots + f_m^*(x_m^*) = (f_1 + \cdots + f_m)^*(x^*).$$
-/
theorem theorem_20_1_attained_finset {ι : Type*} {s t u : Finset ι} {f : ι → Rn n → EReal}
    (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
    (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hconv : ∀ i ∈ u, ConvexFn (f i))
    (hpf : ∀ i ∈ s, ProperConvex (f i)) {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ convexDom (f i))
    (hxu : ∀ i ∈ u, x₀ ∈ ri (convexDom (f i))) (y : Rn n) :
    ∃ y' : ι → Rn n, ∑ i ∈ s, y' i = y ∧
      ∑ i ∈ s, convexConj (pairing n) (f i) (y' i) = convexConj (pairing n) (∑ i ∈ s, f i) y :=
  (IsExactFinsetSum.of_polyhedral (B := pairing n) hs hdisj hmem hpoly hconv hpf hxt
    hxu).exists_convexConj_finsetSum_eq y

section Corollary_20_1_1_finset

variable {ι : Type*} {s t u : Finset ι} {f : ι → Rn n → EReal}
variable (hs : s.Nonempty) (hdisj : Disjoint t u) (hmem : ∀ i, i ∈ s ↔ i ∈ t ∨ i ∈ u)
variable (hpoly : ∀ i ∈ t, PolyhedralFn (f i)) (hcf : ∀ i ∈ s, ClosedProperConvexFn (f i))
variable {x₀ : Rn n} (hxt : ∀ i ∈ t, x₀ ∈ convexDom (convexConj (pairing n) (f i)))
variable (hxu : ∀ i ∈ u, x₀ ∈ ri (convexDom (convexConj (pairing n) (f i))))

include hs hdisj hmem hpoly hcf hxt hxu

private theorem isExactFinsetSum_convexConj_of_polyhedral :
    IsExactFinsetSum (pairing n) s fun i => convexConj (pairing n) (f i) :=
  IsExactFinsetSum.of_polyhedral (B := pairing n) hs hdisj hmem
    (fun i hi => PolyhedralFn.convexConj (B := pairing n) (hpoly i hi))
    (fun i _ => convexFn_convexConj (pairing n) (f i))
        (fun i hi => properConvex_convexConj (hcf i hi)) hxt hxu

private theorem sum_toInfConvFn_eq_convexConj_finsetSum_convexConj :
    ofInfConvFn (∑ i ∈ s, toInfConvFn (f i))
      = convexConj (pairing n) (∑ i ∈ s, convexConj (pairing n) (f i)) := by
  have hbi : ∀ i ∈ s, convexConj (pairing n) (convexConj (pairing n) (f i)) = f i := fun i hi => by
    rw [theorem_12_2_biconj (hcf i hi).convex]; exact (hcf i hi).closed
  rw [(isExactFinsetSum_convexConj_of_polyhedral hs hdisj hmem hpoly hcf hxt
      hxu).convexConj_finsetSum]
  exact congrArg ofInfConvFn
    (Finset.sum_congr rfl fun i hi => congrArg toInfConvFn (hbi i hi).symm)

/-- **Corollary 20.1.1** of [rockafellar1970convex], $m$ functions. Let $f_1, \dots, f_m$ be closed
proper convex functions on $\mathbb{R}^n$ with $m \ge 1$, such that $f_1, \dots, f_k$ are
polyhedral and
$$\operatorname{dom} f_1^* \cap \cdots \cap \operatorname{dom} f_k^* \cap
  \operatorname{ri}(\operatorname{dom} f_{k+1}^*) \cap \cdots \cap
  \operatorname{ri}(\operatorname{dom} f_m^*) \neq \emptyset.$$
Then $f_1 \mathbin{\square} \cdots \mathbin{\square} f_m$ is a closed proper convex function.

The indexing is as in `Rockafellar.theorem_20_1_exact_finset`. -/
theorem corollary_20_1_1_finset :
    ClosedProperConvexFn (ofInfConvFn (∑ i ∈ s, toInfConvFn (f i))) := by
  have hx₀ : ∀ i ∈ s, x₀ ∈ convexDom (convexConj (pairing n) (f i)) := fun i hi =>
    (hmem i).1 hi |>.elim (fun h => hxt i h) fun h => intrinsicInterior_subset (hxu i h)
  obtain ⟨hconvsum, -, -⟩ :=
    properConvexFn_finsetSum (f := fun i => convexConj (pairing n) (f i))
      (fun i _ => convexFn_convexConj (pairing n) (f i))
          (fun i hi => properConvex_convexConj (hcf i hi)) hx₀
  rw [sum_toInfConvFn_eq_convexConj_finsetSum_convexConj hs hdisj hmem hpoly hcf hxt hxu]
  exact ⟨convexFn_convexConj _ _, closedConvex_convexConj,
      properConvex_convexConj_of_properConvex hconvsum
    (isExactFinsetSum_convexConj_of_polyhedral hs hdisj hmem hpoly hcf hxt
        hxu).properConvex_finsetSum⟩

/-- **Corollary 20.1.1** of [rockafellar1970convex], $m$ functions, attainment. Under the hypotheses
of `Rockafellar.corollary_20_1_1_finset`, for every $x \in \mathbb{R}^n$ there are
$x_1, \dots, x_m$ with $x_1 + \cdots + x_m = x$ and
$$f_1(x_1) + \cdots + f_m(x_m) = (f_1 \mathbin{\square} \cdots \mathbin{\square} f_m)(x).$$
-/
theorem corollary_20_1_1_attained_finset (x : Rn n) :
    ∃ x' : ι → Rn n, ∑ i ∈ s, x' i = x ∧
      ∑ i ∈ s, f i (x' i) = ofInfConvFn (∑ i ∈ s, toInfConvFn (f i)) x := by
  have hbi : ∀ i ∈ s, convexConj (pairing n) (convexConj (pairing n) (f i)) = f i := fun i hi => by
    rw [theorem_12_2_biconj (hcf i hi).convex]; exact (hcf i hi).closed
  obtain ⟨x', hx', hval⟩ :=
    (isExactFinsetSum_convexConj_of_polyhedral hs hdisj hmem hpoly hcf hxt
        hxu).exists_convexConj_finsetSum_eq
      x
  refine ⟨x', hx', ?_⟩
  rw [sum_toInfConvFn_eq_convexConj_finsetSum_convexConj hs hdisj hmem hpoly hcf hxt hxu, ← hval]
  exact Finset.sum_congr rfl fun i hi => congrArg (fun k => k (x' i)) (hbi i hi).symm

end Corollary_20_1_1_finset

/-! ### Theorem 20.2 and its corollary -/

/-- **Theorem 20.2** of [rockafellar1970convex]. Let $C_1$ and $C_2$ be non-empty convex sets in
$\mathbb{R}^n$ with $C_1$ polyhedral. There is a hyperplane that separates $C_1$ and $C_2$
properly and does not contain $C_2$ if and only if $C_1 \cap \operatorname{ri} C_2 = \emptyset$.

Compare Theorem 11.3, which needs $\operatorname{ri} C_1 \cap \operatorname{ri} C_2 = \emptyset$
and says nothing about containment; polyhedrality of $C_1$ gives both improvements. Convexity of
$C_1$ follows from polyhedrality and is not a separate hypothesis. -/
theorem theorem_20_2 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hne₂ : C₂.Nonempty) :
    SeparableProperlyNotContaining C₁ C₂ ↔ C₁ ∩ ri C₂ = ∅ := by
  rw [separableProperlyNotContaining_iff_exists hne₁ hne₂,
    exists_separates_not_subset_iff_disjoint_relint (isPolyhedral_iff_polyhedral.1 h₁) h₂ hne₂,
    Set.disjoint_iff_inter_eq_empty]

/-- **Corollary 20.2.1** of [rockafellar1970convex]. Let $C_1$ and $C_2$ be non-empty convex sets in
$\mathbb{R}^n$ with $C_1$ polyhedral. Then $C_1 \cap \operatorname{ri} C_2 \neq \emptyset$ if
and only if every $x^*$ with
$$\delta^*(x^* \mid C_1) \le -\delta^*(-x^* \mid C_2)$$
satisfies $\delta^*(x^* \mid C_1) = \delta^*(x^* \mid C_2)$.

The hypothesis on $x^*$ says that some hyperplane orthogonal to $x^*$ separates the two sets,
and the conclusion says that every such hyperplane contains $C_2$. -/
theorem corollary_20_2_1 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hne₂ : C₂.Nonempty) :
    (C₁ ∩ ri C₂).Nonempty ↔
      ∀ y : Rn n, supportFn (pairing n) C₁ y ≤ -supportFn (pairing n) C₂ (-y) →
        supportFn (pairing n) C₁ y = supportFn (pairing n) C₂ y :=
  nonempty_inter_relint_iff_forall_supportFn (B := pairing n)
    (isPolyhedral_iff_polyhedral.1 h₁) hne₁ h₂ hne₂

/-! ### Theorem 20.3 and its corollary -/

/-- **Theorem 20.3** of [rockafellar1970convex]. Let $C_1$ and $C_2$ be non-empty convex sets in
$\mathbb{R}^n$ with $C_1$ polyhedral and $C_2$ closed. Assume that every direction of recession
$v$ of $C_1$ with $-v \in 0^+ C_2$ is a direction in which $C_2$ is linear, that is,
$v \in 0^+ C_2$. Then $C_1 + C_2$ is closed.

Compare Corollary 9.1.1, which also needs such a $v$ to lie in the lineality space of $C_1$. -/
theorem theorem_20_3 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty)
    (hrec : ∀ v ∈ recessionCone C₁, -v ∈ recessionCone C₂ → v ∈ recessionCone C₂) :
    IsClosed (C₁ + C₂) :=
  isClosed_add_of_polyhedral (B := pairing n) (isPolyhedral_iff_polyhedral.1 h₁) hne₁ h₂ hcl₂
    hne₂ hrec

/-- **Corollary 20.3.1** of [rockafellar1970convex]. Let $C_1$ and $C_2$ be non-empty disjoint
convex sets in $\mathbb{R}^n$ with $C_1$ polyhedral and $C_2$ closed. Assume that every common
direction of recession $v \in 0^+ C_1 \cap 0^+ C_2$ is a direction in which $C_2$ is linear,
that is, $-v \in 0^+ C_2$. Then $C_1$ and $C_2$ can be separated strongly.

Compare Corollary 11.4.1, which excludes common directions of recession, and Corollary 19.3.3,
where both sets are polyhedral and no recession hypothesis is needed. -/
theorem corollary_20_3_1 {C₁ C₂ : Set (Rn n)} (h₁ : IsPolyhedral C₁) (hne₁ : C₁.Nonempty)
    (h₂ : Convex ℝ C₂) (hcl₂ : IsClosed C₂) (hne₂ : C₂.Nonempty) (hdisj : C₁ ∩ C₂ = ∅)
    (hrec : ∀ v ∈ recessionCone C₁, v ∈ recessionCone C₂ → -v ∈ recessionCone C₂) :
    SeparableStrongly C₁ C₂ := by
  rw [separableStrongly_iff_exists hne₁ hne₂]
  exact separatesStrongly_of_polyhedral_of_recession (B := pairing n)
    (isPolyhedral_iff_polyhedral.1 h₁) hne₁ h₂ hcl₂ hne₂
    (Set.disjoint_iff_inter_eq_empty.2 hdisj) hrec

/-! ### Theorems 20.4 and 20.5 -/

/-- **Theorem 20.4** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be closed and
bounded and let $D$ be convex with $C \subseteq \operatorname{int} D$. Then there is a
polyhedral convex set $P$ with $P \subseteq \operatorname{int} D$ and
$C \subseteq \operatorname{int} P$.

**Generalization.** The source also assumes $C$ non-empty and convex. Neither hypothesis is
used: the proof covers $C$ by finitely many polyhedral neighbourhoods and never forms a convex
combination of two points of $C$. -/
theorem theorem_20_4 {C D : Set (Rn n)} (hCcl : IsClosed C) (hCbdd : Bornology.IsBounded C)
    (hD : Convex ℝ D) (hCD : C ⊆ interior D) :
    ∃ P : Set (Rn n), IsPolyhedral P ∧ P ⊆ interior D ∧ C ⊆ interior P := by
  obtain ⟨P, hPpoly, hPD, hCP⟩ := exists_polyhedral_between hCcl hCbdd hD hCD
  exact ⟨P, isPolyhedral_iff_polyhedral.2 hPpoly, hPD, hCP⟩

/-- **Theorem 20.5** of [rockafellar1970convex]. Every polyhedral convex set in $\mathbb{R}^n$ is
locally simplicial: near each of its points it agrees with a finite union of simplices that it
contains.

The proof in the source is a short sketch that assumes the triangulation of a bounded
polyhedron. The proof here constructs the simplices: they are the convex hulls of the affinely
independent subsets of a finite generating set. Locally simplicial is
`ConvexAnalysis.LocallySimplicial`, the property to which the continuity theorems of §10 apply. -/
theorem theorem_20_5 {C : Set (Rn n)} (hC : IsPolyhedral C) : LocallySimplicial C :=
  Polyhedral.locallySimplicial (isPolyhedral_iff_polyhedral.1 hC)

/-- **Theorem 20.5** of [rockafellar1970convex], polytopes. The convex hull of a finite set of
points in $\mathbb{R}^n$ is locally simplicial. -/
theorem theorem_20_5_polytope (P : Finset (Rn n)) :
    LocallySimplicial (convexHull ℝ (P : Set (Rn n))) :=
  Polyhedral.locallySimplicial (polyhedral_convexHull_finset P)

end Rockafellar
