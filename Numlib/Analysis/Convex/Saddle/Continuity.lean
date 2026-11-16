/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Convergence
import Numlib.Analysis.Convex.Saddle.Kernel

/-!
# Continuity of finite saddle-functions

Let $U$ and $X$ be finite-dimensional real normed spaces, let $C \subseteq U$ and $D \subseteq X$ be
convex, and let $K : U \times X \to \mathbb{R}$ be concave-convex on $C \times D$: $K(\cdot, x)$ is
concave on $C$ for each $x \in D$, and $K(u, \cdot)$ is convex on $D$ for each $u \in C$. Then $K$
is Lipschitz on every product $S \times T$ of compact sets $S \subseteq \operatorname{ri} C$ and
$T \subseteq \operatorname{ri} D$, and hence continuous on
$\operatorname{ri} C \times \operatorname{ri} D$. A pointwise bounded family of such functions is
uniformly bounded and equi-Lipschitz on each such rectangle $S \times T$. The usual consequences
follow: pointwise convergence on a dense set implies uniform convergence on compact rectangles, a
bounded sequence has a subsequence that converges in this sense, and a function that is
concave-convex for each value of a parameter and continuous in the parameter is jointly continuous.
Each result is a statement about convex functions of one variable, applied once in each variable and
combined. The presentation follows [rockafellar1970convex], §35.

## Main results

* `ConvexAnalysis.exists_forall_abs_le_and_lipschitzOnWith_prod`: a pointwise bounded family of
  finite concave-convex functions, indexed by an arbitrary type, is uniformly bounded and
  equi-Lipschitz on compact rectangles in $\operatorname{ri} C \times \operatorname{ri} D$. This is
  Theorem 35.2 of [rockafellar1970convex], and the other results of the module rest on it.
* `ConvexAnalysis.ConcaveConvexOn.exists_lipschitzOnWith_of_isCompact`,
  `ConvexAnalysis.ConcaveConvexOn.exists_forall_abs_le_of_isCompact`,
  `ConvexAnalysis.ConcaveConvexOn.continuousOn`: a single finite concave-convex function is
  Lipschitz and bounded on compact rectangles, and continuous on
  $\operatorname{ri} C \times \operatorname{ri} D$.
* `ConvexAnalysis.continuousOn_prod_of_concaveConvexOn`,
  `ConvexAnalysis.continuousOn_prod_of_concaveConvexOn'`: joint continuity in a parameter from a
  locally compact space.
* `ConvexAnalysis.exists_tendstoUniformlyOn_prod_of_dense`,
  `ConvexAnalysis.tendstoUniformlyOn_prod_of_tendsto`: pointwise convergence on a dense set implies
  uniform convergence on compact rectangles.
* `ConvexAnalysis.exists_subseq_tendstoUniformlyOn_prod`: the Arzelà–Ascoli theorem for finite
  concave-convex functions.
* `ConvexAnalysis.exists_isCompact_mem_nhdsWithin_relint`,
  `ConvexAnalysis.exists_isCompact_collar_relint`: $\operatorname{ri} C$ is locally compact, and a
  compact subset of $\operatorname{ri} C$ has a compact relative collar.

## Implementation notes

* The hypothesis "concave-convex on $C \times D$" is `ConvexAnalysis.ConcaveConvexOn C D K`, defined
  in `Numlib.Analysis.Convex.Saddle.Defs`. The simple extensions of
  `Numlib.Analysis.Convex.Saddle.Kernel` take the same hypothesis.
* Everything is stated for arbitrary convex $C$ and $D$, with $\operatorname{ri} C$ and
  $\operatorname{ri} D$ written out. The customary form takes $C$ and $D$ relatively open, so that
  $\operatorname{ri} C = C$.
* The Lipschitz constant is $\alpha_1 + \alpha_2$, not $2(\alpha_1 + \alpha_2)$. The reason is that
  the metric of Mathlib on a product is the maximum of the two distances, so no factor is lost
  between the coordinate distances and the distance on the product.
* The convergence theorems take an arbitrary dense set $A \subseteq \operatorname{ri} C \times
  \operatorname{ri} D$, not only a product $C' \times D'$. The equi-Lipschitz step needs a product,
  but the diagonal extraction behind the Arzelà–Ascoli theorem produces a countable dense set that
  is not a product.
* Unlike the one-variable theory, these results cannot be transported from the case of the interior
  along a chart. The chart of $C \times D$ is not the product of the charts of $C$ and $D$, and the
  concave-convex hypothesis is a statement about the product structure. So the results are proved
  directly for the relative interior.
-/

open Set Filter Topology Metric
open scoped NNReal Pointwise

namespace ConvexAnalysis

/-!
### Negation

The one-variable results are stated for convex functions. The concave variable reaches them through
$-K$, and these lemmas carry the conclusions back.
-/

section Neg

variable {ι : Type*} {g : ι → ℝ}

/-- A family $(g_i)$ of real numbers is bounded above after negation, that is $\{-g_i\}$ is bounded
above, if and only if $\{g_i\}$ is bounded below. -/
theorem bddAbove_range_neg_iff : BddAbove (Set.range fun i => -g i) ↔ BddBelow (Set.range g) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact neg_le.1 (hb ⟨i, rfl⟩)⟩
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact neg_le_neg (hb ⟨i, rfl⟩)⟩

/-- A family $(g_i)$ of real numbers is bounded below after negation, that is $\{-g_i\}$ is bounded
below, if and only if $\{g_i\}$ is bounded above. -/
theorem bddBelow_range_neg_iff : BddBelow (Set.range fun i => -g i) ↔ BddAbove (Set.range g) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact le_neg.1 (hb ⟨i, rfl⟩)⟩
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact neg_le_neg (hb ⟨i, rfl⟩)⟩

variable {E : Type*} [PseudoMetricSpace E] {f : E → ℝ} {S : Set E} {k : ℝ≥0}

/-- If a real-valued function $f$ is Lipschitz with constant $k$ on $S$, then so is $-f$. -/
theorem LipschitzOnWith.negReal (h : LipschitzOnWith k f S) :
    LipschitzOnWith k (fun x => -f x) S := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hd : dist (-f x) (-f y) = dist (f x) (f y) := by
    rw [Real.dist_eq, Real.dist_eq, neg_sub_neg, abs_sub_comm]
  rw [hd]
  exact h.dist_le_mul x hx y hy

/-- A real-valued function $-f$ is Lipschitz with constant $k$ on $S$ if and only if $f$ is. -/
theorem lipschitzOnWith_neg_iff : LipschitzOnWith k (fun x => -f x) S ↔ LipschitzOnWith k f S :=
  ⟨fun h => by simpa only [neg_neg] using LipschitzOnWith.negReal h,
    fun h => LipschitzOnWith.negReal h⟩

end Neg

/-!
### Uniform bounds and equi-Lipschitz constants for a family

The main argument of the module applies one-variable pointwise boundedness four times: twice to
bound the family, once in each variable, and twice to make it equi-Lipschitz.
-/

section Family

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {ι : Type*} {C C' : Set U} {D D' : Set X} {K : ι → U × X → ℝ}

section Snd

variable [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ X] in
/-- If each $K_i$ of a family is concave-convex on $C \times D$ and $u \in C$, then each slice
$K_i(u, \cdot)$ is convex on $D$. -/
theorem convexOn_slice_snd (hK : ∀ i, ConcaveConvexOn C D (K i)) {u : U} (hu : u ∈ C) (i : ι) :
    ConvexOn ℝ D fun x => K i (u, x) :=
  (hK i).convex_snd u hu

/-- The first bounding step. Let $X$ be finite-dimensional, let $D \subseteq X$ be convex, and let
each $K_i : U \times X \to \mathbb{R}$ be concave-convex on $C \times D$. Let $D' \subseteq
\operatorname{ri} D \subseteq \operatorname{cl} D'$ and fix $u \in C$ such that
$\{K_i(u, x)\}_i$ is bounded for every $x \in D'$. Then for every compact
$T \subseteq \operatorname{ri} D$ there is $M \ge 0$ with $|K_i(u, x)| \le M$ for all $i$ and
all $x \in T$. This is the one-variable statement, in the second variable. -/
theorem exists_forall_abs_le_snd {u : U} (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) (hu : u ∈ C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ x ∈ T, |K i (u, x)| ≤ M := by
  rcases D'.eq_empty_or_nonempty with hD'e | ⟨z, hz⟩
  · rw [hD'e, closure_empty, subset_empty_iff] at hDdense
    rw [hDdense, subset_empty_iff] at hTD
    subst hTD
    exact ⟨0, le_rfl, fun i x hx => absurd hx (notMem_empty x)⟩
  exact exists_forall_abs_le_of_isCompact_relint hD (convexOn_slice_snd hK hu) hD' hDdense
    (fun x hx => (isBounded_iff_bddBelow_bddAbove.1 (hbdd x hx)).2)
    ⟨z, hD' hz, (isBounded_iff_bddBelow_bddAbove.1 (hbdd z hz)).1⟩ hT hTD

end Snd

section Fst

variable [FiniteDimensional ℝ U]

/-- The second bounding step. Let $U$ be finite-dimensional, let $C \subseteq U$ be convex, and let
each $K_i : U \times X \to \mathbb{R}$ be concave-convex on $C \times D$. Let $C' \subseteq
\operatorname{ri} C \subseteq \operatorname{cl} C'$ and fix $x \in D$ such that
$\{K_i(u, x)\}_i$ is bounded for every $u \in C'$. Then for every compact
$S \subseteq \operatorname{ri} C$ there is $M \ge 0$ with $|K_i(u, x)| \le M$ for all $i$ and
all $u \in S$. This is the one-variable statement in the first variable, applied to $-K_i$. -/
theorem exists_forall_abs_le_fst {x : X} (hC : Convex ℝ C)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hbdd : ∀ u ∈ C', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C) (hx : x ∈ D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ u ∈ S, |K i (u, x)| ≤ M := by
  rcases C'.eq_empty_or_nonempty with hC'e | ⟨z, hz⟩
  · rw [hC'e, closure_empty, subset_empty_iff] at hCdense
    rw [hCdense, subset_empty_iff] at hSC
    subst hSC
    exact ⟨0, le_rfl, fun i u hu => absurd hu (notMem_empty u)⟩
  obtain ⟨M, hM0, hM⟩ := exists_forall_abs_le_of_isCompact_relint hC
    (fun i => (hK i).convexOn_neg_fst hx) hC' hCdense
    (fun u hu => bddAbove_range_neg_iff.2 (isBounded_iff_bddBelow_bddAbove.1 (hbdd u hu)).1)
    ⟨z, hC' hz, bddBelow_range_neg_iff.2 (isBounded_iff_bddBelow_bddAbove.1 (hbdd z hz)).2⟩ hS hSC
  exact ⟨M, hM0, fun i u hu => by simpa only [abs_neg] using hM i u hu⟩

end Fst

/-! ### The two equi-Lipschitz halves -/

section EquiLipschitz

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ X]

/-- Let $U$ and $X$ be finite-dimensional, let $C$ and $D$ be convex, let each $K_i$ be
concave-convex on $C \times D$, and let $C' \subseteq \operatorname{ri} C \subseteq
\operatorname{cl} C'$ and $D' \subseteq \operatorname{ri} D \subseteq \operatorname{cl} D'$.
Suppose that $\{K_i(u, x)\}_i$ is bounded for every $(u, x) \in C' \times D'$. Then for compact
$S \subseteq \operatorname{ri} C$ and $T \subseteq \operatorname{ri} D$ there is $M \ge 0$ with
$|K_i(u, x)| \le M$ on $S \times T$ for all $i$, and there is $k \ge 0$ such that every
$K_i(\cdot, x)$ with $x \in T$ is Lipschitz with constant $k$ on $S$. -/
theorem exists_forall_abs_le_and_lipschitzOnWith_fst (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ u ∈ S, ∀ x ∈ T, |K i (u, x)| ≤ M) ∧
      ∃ k : ℝ≥0, ∀ i, ∀ x ∈ T, LipschitzOnWith k (fun u => K i (u, x)) S := by
  rcases C'.eq_empty_or_nonempty with hC'e | ⟨z, hz⟩
  · rw [hC'e, closure_empty, subset_empty_iff] at hCdense
    rw [hCdense, subset_empty_iff] at hSC
    subst hSC
    exact ⟨⟨0, le_rfl, fun i u hu => absurd hu (notMem_empty u)⟩,
      0, fun i x _ => by intro u hu; exact absurd hu (notMem_empty u)⟩
  -- the family of concave slices, indexed by `ι × ↑T`, read as convex functions through `-K`
  set g : ι × ↑T → U → ℝ := fun q u => -K q.1 (u, (q.2 : X)) with hg
  have hgconv : ∀ q, ConvexOn ℝ C (g q) := fun q =>
    (hK q.1).convexOn_neg_fst (intrinsicInterior_subset (hTD q.2.2))
  -- pointwise boundedness on `C'` is the first bounding step
  have hgbd : ∀ u ∈ C', ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ι × ↑T, |g q u| ≤ M := by
    intro u hu
    obtain ⟨M, hM0, hM⟩ := exists_forall_abs_le_snd (u := u) hD hK hD' hDdense
      (fun x hx => hbdd u hu x hx) hT hTD (intrinsicInterior_subset (hC' hu))
    exact ⟨M, hM0, fun q => by simpa only [hg, abs_neg] using hM q.1 (q.2 : X) q.2.2⟩
  have hab : ∀ u ∈ C', BddAbove (Set.range fun q : ι × ↑T => g q u) := by
    intro u hu
    obtain ⟨M, -, hM⟩ := hgbd u hu
    exact ⟨M, by rintro _ ⟨q, rfl⟩; exact (le_abs_self _).trans (hM q)⟩
  have hbe : ∃ w ∈ ri C, BddBelow (Set.range fun q : ι × ↑T => g q w) := by
    obtain ⟨M, -, hM⟩ := hgbd z hz
    exact ⟨z, hC' hz, -M, by rintro _ ⟨q, rfl⟩; exact neg_le_of_abs_le (hM q)⟩
  obtain ⟨M, hM0, hM⟩ :=
    exists_forall_abs_le_of_isCompact_relint hC hgconv hC' hCdense hab hbe hS hSC
  obtain ⟨k, hk⟩ :=
    exists_forall_lipschitzOnWith_of_isCompact_relint hC hgconv hC' hCdense hab hbe hS hSC
  refine ⟨⟨M, hM0, fun i u hu x hx => ?_⟩, k, fun i x hx => ?_⟩
  · simpa only [hg, abs_neg] using hM (i, ⟨x, hx⟩) u hu
  · exact lipschitzOnWith_neg_iff.1 (hk (i, ⟨x, hx⟩))

/-- Let $U$ and $X$ be finite-dimensional, let $C$ and $D$ be convex, let each $K_i$ be
concave-convex on $C \times D$, and let $C' \subseteq \operatorname{ri} C \subseteq
\operatorname{cl} C'$ and $D' \subseteq \operatorname{ri} D \subseteq \operatorname{cl} D'$.
Suppose that $\{K_i(u, x)\}_i$ is bounded for every $(u, x) \in C' \times D'$. Then for compact
$S \subseteq \operatorname{ri} C$ and $T \subseteq \operatorname{ri} D$ there is $k \ge 0$ such
that every $K_i(u, \cdot)$ with $u \in S$ is Lipschitz with constant $k$ on $T$. -/
theorem exists_forall_lipschitzOnWith_snd (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    ∃ k : ℝ≥0, ∀ i, ∀ u ∈ S, LipschitzOnWith k (fun x => K i (u, x)) T := by
  rcases D'.eq_empty_or_nonempty with hD'e | ⟨w, hw⟩
  · rw [hD'e, closure_empty, subset_empty_iff] at hDdense
    rw [hDdense, subset_empty_iff] at hTD
    subst hTD
    exact ⟨0, fun i u _ => by intro x hx; exact absurd hx (notMem_empty x)⟩
  set g : ι × ↑S → X → ℝ := fun q x => K q.1 ((q.2 : U), x) with hg
  have hgconv : ∀ q, ConvexOn ℝ D (g q) := fun q =>
    (hK q.1).convex_snd (q.2 : U) (intrinsicInterior_subset (hSC q.2.2))
  have hgbd : ∀ x ∈ D', ∃ M : ℝ, 0 ≤ M ∧ ∀ q : ι × ↑S, |g q x| ≤ M := by
    intro x hx
    obtain ⟨M, hM0, hM⟩ := exists_forall_abs_le_fst (x := x) hC hK hC' hCdense
      (fun u hu => hbdd u hu x hx) hS hSC (intrinsicInterior_subset (hD' hx))
    exact ⟨M, hM0, fun q => hM q.1 (q.2 : U) q.2.2⟩
  have hab : ∀ x ∈ D', BddAbove (Set.range fun q : ι × ↑S => g q x) := by
    intro x hx
    obtain ⟨M, -, hM⟩ := hgbd x hx
    exact ⟨M, by rintro _ ⟨q, rfl⟩; exact (le_abs_self _).trans (hM q)⟩
  have hbe : ∃ y ∈ ri D, BddBelow (Set.range fun q : ι × ↑S => g q y) := by
    obtain ⟨M, -, hM⟩ := hgbd w hw
    exact ⟨w, hD' hw, -M, by rintro _ ⟨q, rfl⟩; exact neg_le_of_abs_le (hM q)⟩
  obtain ⟨k, hk⟩ :=
    exists_forall_lipschitzOnWith_of_isCompact_relint hD hgconv hD' hDdense hab hbe hT hTD
  exact ⟨k, fun i u hu => hk (i, ⟨u, hu⟩)⟩

/-- Let $U$ and $X$ be finite-dimensional real normed spaces and let $C \subseteq U$ and
$D \subseteq X$ be convex. Let $(K_i)_{i \in I}$ be a family of functions
$U \times X \to \mathbb{R}$, each concave-convex on $C \times D$, with $I$ an arbitrary index
set. Let $C' \subseteq \operatorname{ri} C \subseteq \operatorname{cl} C'$ and $D' \subseteq
\operatorname{ri} D \subseteq \operatorname{cl} D'$, and suppose that the family is pointwise
bounded on $C' \times D'$: $\{K_i(u, x)\}_{i \in I}$ is bounded for every
$(u, x) \in C' \times D'$. Then for all compact sets $S \subseteq \operatorname{ri} C$ and
$T \subseteq \operatorname{ri} D$ the family is uniformly bounded and equi-Lipschitz on
$S \times T$: there are $M \ge 0$ and $k \ge 0$ such that for all $i \in I$
$$|K_i(p)| \le M \text{ for } p \in S \times T, \qquad |K_i(p) - K_i(q)|
  \le k \operatorname{dist}(p, q) \text{ for } p, q \in S \times T.$$
This is Theorem 35.2 of [rockafellar1970convex].

The source assumes that $C$ and $D$ are relatively open and that $\operatorname{conv}
(\operatorname{cl} (C' \times D')) \supseteq C \times D$. The form used here is $C' \subseteq
\operatorname{ri} C \subseteq \operatorname{cl} C'$ and likewise for $D$, and the choice
$C' = \operatorname{ri} C$, $D' = \operatorname{ri} D$ gives the main case. The distance on
$U \times X$ is the maximum of the distances of the coordinates. -/
theorem exists_forall_abs_le_and_lipschitzOnWith_prod (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ p ∈ S ×ˢ T, |K i p| ≤ M) ∧
      ∃ k : ℝ≥0, ∀ i, LipschitzOnWith k (K i) (S ×ˢ T) := by
  obtain ⟨⟨M, hM0, hM⟩, k₁, hk₁⟩ := exists_forall_abs_le_and_lipschitzOnWith_fst hC hD hK hC'
    hCdense hD' hDdense hbdd hS hSC hT hTD
  obtain ⟨k₂, hk₂⟩ :=
    exists_forall_lipschitzOnWith_snd hC hD hK hC' hCdense hD' hDdense hbdd hS hSC hT hTD
  refine ⟨⟨M, hM0, fun i p hp => hM i p.1 hp.1 p.2 hp.2⟩, k₁ + k₂, fun i => ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  have h₁ : dist (K i (p.1, q.2)) (K i (q.1, q.2)) ≤ (k₁ : ℝ) * dist p.1 q.1 :=
    (hk₁ i q.2 hq.2).dist_le_mul p.1 hp.1 q.1 hq.1
  have h₂ : dist (K i (p.1, p.2)) (K i (p.1, q.2)) ≤ (k₂ : ℝ) * dist p.2 q.2 :=
    (hk₂ i p.1 hp.1).dist_le_mul p.2 hp.2 q.2 hq.2
  have hd₁ : dist p.1 q.1 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd₂ : dist p.2 q.2 ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
  have htri : dist (K i p) (K i q)
      ≤ dist (K i (p.1, p.2)) (K i (p.1, q.2)) + dist (K i (p.1, q.2)) (K i (q.1, q.2)) :=
    dist_triangle _ _ _
  have hsum : (k₂ : ℝ) * dist p.2 q.2 + (k₁ : ℝ) * dist p.1 q.1
      ≤ ((k₁ + k₂ : ℝ≥0) : ℝ) * dist p q := by
    have e₁ : (k₁ : ℝ) * dist p.1 q.1 ≤ (k₁ : ℝ) * dist p q :=
      mul_le_mul_of_nonneg_left hd₁ k₁.coe_nonneg
    have e₂ : (k₂ : ℝ) * dist p.2 q.2 ≤ (k₂ : ℝ) * dist p q :=
      mul_le_mul_of_nonneg_left hd₂ k₂.coe_nonneg
    have : ((k₁ + k₂ : ℝ≥0) : ℝ) * dist p q = (k₁ : ℝ) * dist p q + (k₂ : ℝ) * dist p q := by
      push_cast
      ring
    linarith
  exact htri.trans ((add_le_add h₂ h₁).trans hsum)

end EquiLipschitz

/-! ### The single-function case -/

section Single

variable [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] {L : U × X → ℝ}

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, let $C \subseteq U$ and
$D \subseteq X$ be convex, and let $L : U \times X \to \mathbb{R}$ be concave-convex on
$C \times D$. Then for all compact sets $S \subseteq \operatorname{ri} C$ and
$T \subseteq \operatorname{ri} D$ there is $k \ge 0$ such that $L$ is Lipschitz with constant
$k$ on $S \times T$.

The proof applies `ConvexAnalysis.exists_forall_abs_le_and_lipschitzOnWith_prod` to the family
with one member. -/
theorem ConcaveConvexOn.exists_lipschitzOnWith_of_isCompact (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hL : ConcaveConvexOn C D L)
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    ∃ k : ℝ≥0, LipschitzOnWith k L (S ×ˢ T) := by
  obtain ⟨-, k, hk⟩ := exists_forall_abs_le_and_lipschitzOnWith_prod (K := fun _ : Unit => L)
    hC hD (fun _ => hL) (subset_refl _) subset_closure (subset_refl _) subset_closure
    (fun _ _ _ _ => (Set.finite_range _).isBounded) hS hSC hT hTD
  exact ⟨k, hk ()⟩

/-- Let $U$ and $X$ be finite-dimensional, let $C$ and $D$ be convex, and let
$L : U \times X \to \mathbb{R}$ be concave-convex on $C \times D$. Then for all compact sets
$S \subseteq \operatorname{ri} C$ and $T \subseteq \operatorname{ri} D$ there is $M \ge 0$ with
$|L(p)| \le M$ for all $p \in S \times T$. -/
theorem ConcaveConvexOn.exists_forall_abs_le_of_isCompact (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hL : ConcaveConvexOn C D L)
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ S ×ˢ T, |L p| ≤ M := by
  obtain ⟨⟨M, hM0, hM⟩, -⟩ := exists_forall_abs_le_and_lipschitzOnWith_prod (K := fun _ : Unit => L)
    hC hD (fun _ => hL) (subset_refl _) subset_closure (subset_refl _) subset_closure
    (fun _ _ _ _ => (Set.finite_range _).isBounded) hS hSC hT hTD
  exact ⟨M, hM0, hM ()⟩

end Single

end Family

/-!
### Compact relative neighbourhoods

The relative interior $\operatorname{ri} C$ is locally compact, because it is a translate of an open
subset of a finite-dimensional subspace. This turns "Lipschitz on every compact rectangle" into
"continuous".
-/

section LocallyCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- Let $E$ be a finite-dimensional real normed space and let $C \subseteq E$ be convex. Every point
$x \in \operatorname{ri} C$ has a compact neighbourhood relative to $\operatorname{ri} C$ inside
$\operatorname{ri} C$: there is a compact set $S \subseteq \operatorname{ri} C$ that is a
neighbourhood of $x$ in the subspace $\operatorname{ri} C$. -/
theorem exists_isCompact_mem_nhdsWithin_relint (hC : Convex ℝ C) {x : E} (hx : x ∈ ri C) :
    ∃ S : Set E, IsCompact S ∧ S ⊆ ri C ∧ S ∈ 𝓝[ri C] x := by
  obtain ⟨V, r, himg, hmaps, hid⟩ := exists_chart_retraction hC (intrinsicInterior_subset hx)
  have h0 : (0 : V) ∈ interior (chart C x V) := by
    have h := hmaps hx
    simpa using h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  have hsub : Metric.closedBall (0 : V) (ε / 2) ⊆ interior (chart C x V) := fun w hw =>
    hball (Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hw) (by linarith)))
  refine ⟨(fun w : V => x + (w : E)) '' Metric.closedBall (0 : V) (ε / 2),
    (isCompact_closedBall _ _).image (continuous_const.add continuous_subtype_val), ?_, ?_⟩
  · rw [himg]
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨(w : E), ⟨w, hsub hw, rfl⟩, rfl⟩
  · refine mem_nhdsWithin.2 ⟨Metric.ball x (ε / 2), Metric.isOpen_ball,
      Metric.mem_ball_self (by linarith), ?_⟩
    rintro y ⟨hyball, hyri⟩
    refine ⟨r (y - x), ?_, hid y hyri⟩
    have hcoe : ((r (y - x) : V) : E) = y - x := eq_sub_of_add_eq' (hid y hyri)
    rw [Metric.mem_closedBall, dist_zero_right, ← Submodule.norm_coe, hcoe, ← dist_eq_norm]
    exact (Metric.mem_ball.1 hyball).le

end LocallyCompact

/-! ### The continuity clause -/

section ContinuousOn

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C : Set U} {D : Set X} {L : U × X → ℝ}

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, let $C \subseteq U$ and
$D \subseteq X$ be convex, and let $L : U \times X \to \mathbb{R}$ be concave-convex on
$C \times D$. Then $L$ is continuous relative to
$\operatorname{ri} C \times \operatorname{ri} D$. Continuity is a local property,
$\operatorname{ri} C$ and $\operatorname{ri} D$ are locally compact, and $L$ is Lipschitz on
each compact rectangle. -/
theorem ConcaveConvexOn.continuousOn (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hL : ConcaveConvexOn C D L) : ContinuousOn L (ri C ×ˢ ri D) := by
  rintro ⟨u, x⟩ ⟨hu, hx⟩
  obtain ⟨S, hScpt, hSC, hSn⟩ := exists_isCompact_mem_nhdsWithin_relint hC hu
  obtain ⟨T, hTcpt, hTD, hTn⟩ := exists_isCompact_mem_nhdsWithin_relint hD hx
  obtain ⟨k, hk⟩ := hL.exists_lipschitzOnWith_of_isCompact hC hD hScpt hSC hTcpt hTD
  have hcw : ContinuousWithinAt L (S ×ˢ T) (u, x) :=
    hk.continuousOn.continuousWithinAt
      (Set.mem_prod.2 ⟨mem_of_mem_nhdsWithin hu hSn, mem_of_mem_nhdsWithin hx hTn⟩)
  exact hcw.mono_of_mem_nhdsWithin (nhdsWithin_prod hSn hTn)

end ContinuousOn

/-!
### The relative collar

The convergence and joint-continuity theorems need, for a compact set
$S \subseteq \operatorname{ri} C$, a slightly larger compact subset of $\operatorname{ri} C$ that
contains every point of $\operatorname{ri} C$ near $S$. The Mathlib lemma
`IsCompact.exists_cthickening_subset_open` does not apply: a closed $\varepsilon$-thickening of $S$
is not contained in $\operatorname{ri} C$, because points off the affine hull of $C$ are near $S$.
-/

section Collar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- Let $E$ be a finite-dimensional real normed space, let $C \subseteq E$ be convex, and let
$S \subseteq \operatorname{ri} C$ be compact. Then $S$ has a **relative collar**: there are
$\varepsilon > 0$ and a compact set $S'$ with $S \subseteq S' \subseteq \operatorname{ri} C$
such that every $y \in \operatorname{ri} C$ with $\operatorname{dist}(y, x) \le \varepsilon$ for
some $x \in S$ lies in $S'$.

This is the relative analogue of `IsCompact.exists_cthickening_subset_open`. It lets the proofs
of the one-variable convergence theorems for the interior run in the relative interior. -/
theorem exists_isCompact_collar_relint (hC : Convex ℝ C) {S : Set E}
    (hS : IsCompact S) (hSC : S ⊆ ri C) :
    ∃ (ε : ℝ) (S' : Set E), 0 < ε ∧ IsCompact S' ∧ S ⊆ S' ∧ S' ⊆ ri C ∧
      ∀ y ∈ ri C, ∀ x ∈ S, dist y x ≤ ε → y ∈ S' := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀S⟩
  · exact ⟨1, ∅, one_pos, isCompact_empty, subset_rfl, empty_subset _,
      fun _ _ x hx => absurd hx (notMem_empty x)⟩
  obtain ⟨V, r, himg, hmaps, hid⟩ :=
    exists_chart_retraction hC (intrinsicInterior_subset (hSC hx₀S))
  have hρc : Continuous fun x : E => (r (x - x₀) : V) :=
    r.continuous.comp (continuous_id.sub continuous_const)
  have hcoe : ∀ y ∈ ri C, ((r (y - x₀) : V) : E) = y - x₀ := fun y hy =>
    eq_sub_of_add_eq' (hid y hy)
  have hS₀ : IsCompact ((fun x : E => (r (x - x₀) : V)) '' S) := hS.image hρc
  have hS₀sub : (fun x : E => (r (x - x₀) : V)) '' S ⊆ interior (chart C x₀ V) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps (hSC hx)
  obtain ⟨ε, hε, hthick⟩ := hS₀.exists_cthickening_subset_open isOpen_interior hS₀sub
  have hmemri : ∀ z ∈ cthickening ε ((fun x : E => (r (x - x₀) : V)) '' S),
      x₀ + (z : E) ∈ ri C := by
    intro z hz
    rw [himg]
    exact ⟨(z : E), ⟨z, hthick hz, rfl⟩, rfl⟩
  refine ⟨ε, (fun z : V => x₀ + (z : E)) ''
      cthickening ε ((fun x : E => (r (x - x₀) : V)) '' S), hε,
    hS₀.cthickening.image (continuous_const.add continuous_subtype_val), ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨r (x - x₀), self_subset_cthickening _ ⟨x, hx, rfl⟩, hid x (hSC hx)⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hmemri z hz
  · intro y hy x hx hd
    refine ⟨r (y - x₀), ?_, hid y hy⟩
    refine mem_cthickening_of_dist_le _ (r (x - x₀)) ε _ ⟨x, hx, rfl⟩ ?_
    have hdV : dist (r (y - x₀) : V) (r (x - x₀) : V) = dist y x := by
      rw [Subtype.dist_eq, hcoe y hy, hcoe x (hSC hx), dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    rw [hdV]
    exact hd

end Collar

/-!
### Convergence

Both convergence theorems are the one-variable statements with the compact set replaced by a compact
rectangle. The family theorem supplies the equi-Lipschitz constant,
`ConvexAnalysis.exists_isCompact_collar_relint` the room to move in, and
`ConvexAnalysis.uniformCauchySeqOn_of_equiLipschitz` does the rest.
-/

section Convergence

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C C' : Set U} {D D' : Set X} {K : ℕ → U × X → ℝ}

/-- Let $U$ and $X$ be finite-dimensional, let $C$ and $D$ be convex, let $(K_i)_{i \in \mathbb{N}}$
be a sequence of functions concave-convex on $C \times D$, and let $C' \subseteq
\operatorname{ri} C \subseteq \operatorname{cl} C'$ and $D' \subseteq \operatorname{ri} D
\subseteq \operatorname{cl} D'$. Suppose that the sequence is pointwise bounded on
$C' \times D'$, and that $(K_i(p))_i$ is a Cauchy sequence for every $p$ in a set $A \subseteq
\operatorname{ri} C \times \operatorname{ri} D$ whose closure contains
$\operatorname{ri} C \times \operatorname{ri} D$. Then $(K_i)$ is uniformly Cauchy on
$S \times T$ for all compact sets $S \subseteq \operatorname{ri} C$ and
$T \subseteq \operatorname{ri} D$. This is the step common to both convergence theorems. -/
theorem uniformCauchySeqOn_prod_of_dense (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {A : Set (U × X)} (hA : A ⊆ ri C ×ˢ ri D) (hAdense : ri C ×ˢ ri D ⊆ closure A)
    (hcau : ∀ p ∈ A, CauchySeq fun i => K i p)
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    UniformCauchySeqOn K atTop (S ×ˢ T) := by
  obtain ⟨ε₁, S', hε₁, hS'cpt, hSS', hS'C, hcol₁⟩ := exists_isCompact_collar_relint hC hS hSC
  obtain ⟨ε₂, T', hε₂, hT'cpt, hTT', hT'D, hcol₂⟩ := exists_isCompact_collar_relint hD hT hTD
  obtain ⟨-, k, hk⟩ := exists_forall_abs_le_and_lipschitzOnWith_prod hC hD hK hC' hCdense hD'
    hDdense hbdd hS'cpt hS'C hT'cpt hT'D
  refine uniformCauchySeqOn_of_equiLipschitz (hS.prod hT) (Set.prod_mono hSS' hTT')
    (lt_min hε₁ hε₂) ?_ (fun p hp => hAdense ⟨hSC hp.1, hTD hp.2⟩) hk hcau
  rintro y hy x hx hd
  simp only [Prod.dist_eq] at hd
  obtain ⟨hy₁, hy₂⟩ := hA hy
  exact ⟨hcol₁ y.1 hy₁ x.1 hx.1 ((le_max_left _ _).trans (hd.trans (min_le_left _ _))),
    hcol₂ y.2 hy₂ x.2 hx.2 ((le_max_right _ _).trans (hd.trans (min_le_right _ _)))⟩

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, let $C \subseteq U$ and
$D \subseteq X$ be convex, and let $(K_i)_{i \in \mathbb{N}}$ be a sequence of functions
$U \times X \to \mathbb{R}$, each concave-convex on $C \times D$. Let $C' \subseteq
\operatorname{ri} C \subseteq \operatorname{cl} C'$ and $D' \subseteq \operatorname{ri} D
\subseteq \operatorname{cl} D'$, and suppose that $\{K_i(u, x)\}_i$ is bounded for every
$(u, x) \in C' \times D'$. Let $A \subseteq \operatorname{ri} C \times \operatorname{ri} D$ be a
set whose closure contains $\operatorname{ri} C \times \operatorname{ri} D$, and suppose that
$(K_i(p))_i$ converges for every $p \in A$. Then there is $L : U \times X \to \mathbb{R}$,
concave-convex on $\operatorname{ri} C \times \operatorname{ri} D$, such that $K_i(p) \to L(p)$
for every $p \in \operatorname{ri} C \times \operatorname{ri} D$, and the convergence is uniform
on $S \times T$ for all compact sets $S \subseteq \operatorname{ri} C$ and
$T \subseteq \operatorname{ri} D$.

The choice $A = C' \times D'$ gives the customary statement,
`ConvexAnalysis.exists_tendstoUniformlyOn_prod_of_dense'`. -/
theorem exists_tendstoUniformlyOn_prod_of_dense (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x)))
    {A : Set (U × X)} (hA : A ⊆ ri C ×ˢ ri D) (hAdense : ri C ×ˢ ri D ⊆ closure A)
    (hcv : ∀ p ∈ A, ∃ L : ℝ, Tendsto (fun i => K i p) atTop (𝓝 L)) :
    ∃ L : U × X → ℝ, ConcaveConvexOn (ri C) (ri D) L ∧
      (∀ p ∈ ri C ×ˢ ri D, Tendsto (fun i => K i p) atTop (𝓝 (L p))) ∧
      ∀ ⦃S : Set U⦄, IsCompact S → S ⊆ ri C → ∀ ⦃T : Set X⦄, IsCompact T → T ⊆ ri D →
        TendstoUniformlyOn K L atTop (S ×ˢ T) := by
  have hcau : ∀ p ∈ A, CauchySeq fun i => K i p := fun p hp => (hcv p hp).choose_spec.cauchySeq
  have key : ∀ S : Set U, IsCompact S → S ⊆ ri C → ∀ T : Set X, IsCompact T → T ⊆ ri D →
      UniformCauchySeqOn K atTop (S ×ˢ T) := fun S hS hSC T hT hTD =>
    uniformCauchySeqOn_prod_of_dense hC hD hK hC' hCdense hD' hDdense hbdd hA hAdense hcau
      hS hSC hT hTD
  have hcauP : ∀ p ∈ ri C ×ˢ ri D, CauchySeq fun i => K i p := by
    rintro ⟨u, x⟩ ⟨hu, hx⟩
    exact (key {u} isCompact_singleton (singleton_subset_iff.2 hu) {x} isCompact_singleton
      (singleton_subset_iff.2 hx)).cauchySeq ⟨rfl, rfl⟩
  have htend : ∀ p ∈ ri C ×ˢ ri D,
      Tendsto (fun i => K i p) atTop (𝓝 (limUnder atTop fun i => K i p)) :=
    fun p hp => (hcauP p hp).tendsto_limUnder
  refine ⟨fun p => limUnder atTop fun i => K i p, ⟨fun x hx => ⟨(Convex.relint hC), ?_⟩,
    fun u hu => ⟨(Convex.relint hD), ?_⟩⟩, htend, fun S hS hSC T hT hTD =>
      (key S hS hSC T hT hTD).tendstoUniformlyOn_of_tendsto fun p hp =>
        htend p ⟨hSC hp.1, hTD hp.2⟩⟩
  · intro u hu v hv a b ha hb hab
    refine le_of_tendsto_of_tendsto' (((htend (u, x) ⟨hu, hx⟩).const_mul a).add
      ((htend (v, x) ⟨hv, hx⟩).const_mul b))
      (htend (a • u + b • v, x) ⟨(Convex.relint hC) hu hv ha hb hab, hx⟩) fun i => ?_
    exact ((hK i).concave_fst x (intrinsicInterior_subset hx)).2 (intrinsicInterior_subset hu)
      (intrinsicInterior_subset hv) ha hb hab
  · intro x hx y hy a b ha hb hab
    refine le_of_tendsto_of_tendsto'
      (htend (u, a • x + b • y) ⟨hu, Convex.relint hD hx hy ha hb hab⟩)
      (((htend (u, x) ⟨hu, hx⟩).const_mul a).add ((htend (u, y) ⟨hu, hy⟩).const_mul b)) fun i => ?_
    exact ((hK i).convex_snd u (intrinsicInterior_subset hu)).2 (intrinsicInterior_subset hx)
      (intrinsicInterior_subset hy) ha hb hab

/-- Let $U$ and $X$ be finite-dimensional, let $C$ and $D$ be convex, let $(K_i)_{i \in \mathbb{N}}$
be a sequence of functions concave-convex on $C \times D$, and let $C' \subseteq
\operatorname{ri} C \subseteq \operatorname{cl} C'$ and $D' \subseteq \operatorname{ri} D
\subseteq \operatorname{cl} D'$. If $(K_i(u, x))_i$ converges for every
$(u, x) \in C' \times D'$, then there is $L$, concave-convex on
$\operatorname{ri} C \times \operatorname{ri} D$, such that $K_i \to L$ pointwise on
$\operatorname{ri} C \times \operatorname{ri} D$ and uniformly on $S \times T$ for all compact
sets $S \subseteq \operatorname{ri} C$ and $T \subseteq \operatorname{ri} D$. This is
`ConvexAnalysis.exists_tendstoUniformlyOn_prod_of_dense` with pointwise convergence on a product
of dense subsets. -/
theorem exists_tendstoUniformlyOn_prod_of_dense' (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hcv : ∀ u ∈ C', ∀ x ∈ D', ∃ L : ℝ, Tendsto (fun i => K i (u, x)) atTop (𝓝 L)) :
    ∃ L : U × X → ℝ, ConcaveConvexOn (ri C) (ri D) L ∧
      (∀ p ∈ ri C ×ˢ ri D, Tendsto (fun i => K i p) atTop (𝓝 (L p))) ∧
      ∀ ⦃S : Set U⦄, IsCompact S → S ⊆ ri C → ∀ ⦃T : Set X⦄, IsCompact T → T ⊆ ri D →
        TendstoUniformlyOn K L atTop (S ×ˢ T) := by
  refine exists_tendstoUniformlyOn_prod_of_dense hC hD hK hC' hCdense hD' hDdense
    (fun u hu x hx => isBounded_iff_bddBelow_bddAbove.2
      ⟨(hcv u hu x hx).choose_spec.bddBelow_range,
        (hcv u hu x hx).choose_spec.bddAbove_range⟩)
    (A := C' ×ˢ D') (Set.prod_mono hC' hD') ?_ fun p hp => hcv p.1 hp.1 p.2 hp.2
  rw [closure_prod_eq]
  exact Set.prod_mono hCdense hDdense

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, let $C \subseteq U$ and
$D \subseteq X$ be convex, and let $(K_i)_{i \in \mathbb{N}}$ be a sequence of functions
$U \times X \to \mathbb{R}$, each concave-convex on $C \times D$. If $K_i(p) \to L(p)$ for every
$p \in \operatorname{ri} C \times \operatorname{ri} D$, then $K_i \to L$ uniformly on
$S \times T$ for all compact sets $S \subseteq \operatorname{ri} C$ and
$T \subseteq \operatorname{ri} D$. -/
theorem tendstoUniformlyOn_prod_of_tendsto (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i)) {L : U × X → ℝ}
    (hL : ∀ p ∈ ri C ×ˢ ri D, Tendsto (fun i => K i p) atTop (𝓝 (L p)))
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    TendstoUniformlyOn K L atTop (S ×ˢ T) := by
  obtain ⟨L', -, hL', huc⟩ := exists_tendstoUniformlyOn_prod_of_dense' hC hD hK
    (subset_refl (ri C)) subset_closure (subset_refl (ri D)) subset_closure
    fun u hu x hx => ⟨L (u, x), hL (u, x) ⟨hu, hx⟩⟩
  exact (huc hS hSC hT hTD).congr_right fun p hp =>
    tendsto_nhds_unique (hL' p ⟨hSC hp.1, hTD hp.2⟩) (hL p ⟨hSC hp.1, hTD hp.2⟩)

/-- The **Arzelà–Ascoli theorem for saddle-functions**. Let $U$ and $X$ be finite-dimensional real
normed spaces, let $C \subseteq U$ and $D \subseteq X$ be convex, and let
$(K_i)_{i \in \mathbb{N}}$ be a sequence of functions $U \times X \to \mathbb{R}$, each
concave-convex on $C \times D$. Let $C' \subseteq \operatorname{ri} C \subseteq
\operatorname{cl} C'$ and $D' \subseteq \operatorname{ri} D \subseteq \operatorname{cl} D'$, and
suppose that $\{K_i(u, x)\}_i$ is bounded for every $(u, x) \in C' \times D'$. Then there are a
strictly increasing $\varphi : \mathbb{N} \to \mathbb{N}$ and a function
$L : U \times X \to \mathbb{R}$, concave-convex on
$\operatorname{ri} C \times \operatorname{ri} D$, such that $K_{\varphi(i)}(p) \to L(p)$ for
every $p \in \operatorname{ri} C \times \operatorname{ri} D$, uniformly on $S \times T$ for all
compact sets $S \subseteq \operatorname{ri} C$ and $T \subseteq \operatorname{ri} D$.

As in one variable, the subsequence comes from a countable dense subset of the product
$C' \times D'$, and this subset is not itself a product. This is why
`ConvexAnalysis.exists_tendstoUniformlyOn_prod_of_dense` is stated for a general dense set $A$. -/
theorem exists_subseq_tendstoUniformlyOn_prod (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hK : ∀ i, ConcaveConvexOn C D (K i))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hbdd : ∀ u ∈ C', ∀ x ∈ D', Bornology.IsBounded (Set.range fun i => K i (u, x))) :
    ∃ (φ : ℕ → ℕ) (L : U × X → ℝ), StrictMono φ ∧ ConcaveConvexOn (ri C) (ri D) L ∧
      (∀ p ∈ ri C ×ˢ ri D, Tendsto (fun i => K (φ i) p) atTop (𝓝 (L p))) ∧
      ∀ ⦃S : Set U⦄, IsCompact S → S ⊆ ri C → ∀ ⦃T : Set X⦄, IsCompact T → T ⊆ ri D →
        TendstoUniformlyOn (fun i => K (φ i)) L atTop (S ×ˢ T) := by
  have hprod : ri C ×ˢ ri D ⊆ closure (C' ×ˢ D') := by
    rw [closure_prod_eq]
    exact Set.prod_mono hCdense hDdense
  obtain ⟨A, hAsub, hAcnt, hAdense'⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (C' ×ˢ D')).exists_countable_dense_subset
  have hAdense : ri C ×ˢ ri D ⊆ closure A :=
    hprod.trans (closure_minimal hAdense' isClosed_closure)
  have hA : A ⊆ ri C ×ˢ ri D := hAsub.trans (Set.prod_mono hC' hD')
  have hbddA : ∀ p ∈ A, Bornology.IsBounded (Set.range fun i => K i p) := fun p hp => by
    have h := hAsub hp
    exact hbdd p.1 h.1 p.2 h.2
  obtain ⟨φ, hφ, hcv⟩ := exists_strictMono_tendsto_of_countable hAcnt hbddA
  obtain ⟨L, hLcc, hLtend, huc⟩ := exists_tendstoUniformlyOn_prod_of_dense hC hD
    (fun i => hK (φ i)) hC' hCdense hD' hDdense
    (fun u hu x hx => (hbdd u hu x hx).subset (by rintro _ ⟨i, rfl⟩; exact ⟨φ i, rfl⟩)) hA hAdense
    hcv
  exact ⟨φ, L, hφ, hLcc, hLtend, huc⟩

end Convergence

/-! ### Joint continuity in a parameter -/

section JointContinuity

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C C' : Set U} {D D' : Set X} {T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, let $C \subseteq U$ and
$D \subseteq X$ be convex, and let $T$ be a locally compact topological space. Let
$F : (U \times X) \times T \to \mathbb{R}$ be such that $F(\cdot, t)$ is concave-convex on
$C \times D$ for every $t \in T$. Let $C' \subseteq \operatorname{ri} C \subseteq
\operatorname{cl} C'$ and $D' \subseteq \operatorname{ri} D \subseteq \operatorname{cl} D'$, and
suppose that $t \mapsto F((u, x), t)$ is continuous for every $(u, x) \in C' \times D'$. Then
$F$ is jointly continuous relative to $(\operatorname{ri} C \times \operatorname{ri} D) \times
T$.

Continuity in $t$ is needed only at the points of the dense sets $C'$ and $D'$;
`ConvexAnalysis.continuousOn_prod_of_concaveConvexOn'` is the case $C' = \operatorname{ri} C$,
$D' = \operatorname{ri} D$. On a compact neighbourhood $T_0$ of $t_0$ the family
$\{F(\cdot, t) \mid t \in T_0\}$ is pointwise bounded on $C' \times D'$. So the family theorem
makes it equi-Lipschitz near $(u_0, x_0)$, and an estimate with four terms through a nearby
point gives the continuity. -/
theorem continuousOn_prod_of_concaveConvexOn (hC : Convex ℝ C) (hD : Convex ℝ D)
    {F : (U × X) × T → ℝ} (hF : ∀ t : T, ConcaveConvexOn C D fun p => F (p, t))
    (hC' : C' ⊆ ri C) (hCdense : ri C ⊆ closure C')
    (hD' : D' ⊆ ri D) (hDdense : ri D ⊆ closure D')
    (hcont : ∀ u ∈ C', ∀ x ∈ D', Continuous fun t => F ((u, x), t)) :
    ContinuousOn F ((ri C ×ˢ ri D) ×ˢ (univ : Set T)) := by
  rintro ⟨⟨u₀, x₀⟩, t₀⟩ ⟨⟨hu₀, hx₀⟩, -⟩
  obtain ⟨T₀, hT₀c, hT₀n⟩ := exists_compact_mem_nhds t₀
  have ht₀T₀ : t₀ ∈ T₀ := mem_of_mem_nhds hT₀n
  have hbdd : ∀ u ∈ C', ∀ x ∈ D',
      Bornology.IsBounded (Set.range fun t : T₀ => F ((u, x), (t : T))) := by
    intro u hu x hx
    obtain ⟨M, hM⟩ := hT₀c.exists_bound_of_continuousOn (hcont u hu x hx).continuousOn
    exact isBounded_iff_forall_norm_le.2 ⟨M, by rintro _ ⟨t, rfl⟩; exact hM (t : T) t.2⟩
  obtain ⟨S, hScpt, hSC, hSn⟩ := exists_isCompact_mem_nhdsWithin_relint hC hu₀
  obtain ⟨R, hRcpt, hRD, hRn⟩ := exists_isCompact_mem_nhdsWithin_relint hD hx₀
  obtain ⟨-, k, hk⟩ := exists_forall_abs_le_and_lipschitzOnWith_prod
    (K := fun t : T₀ => fun p : U × X => F (p, (t : T))) hC hD (fun t => hF (t : T))
    hC' hCdense hD' hDdense hbdd hScpt hSC hRcpt hRD
  have hknn : (0 : ℝ) ≤ (k : ℝ) := k.coe_nonneg
  obtain ⟨δ₁, hδ₁, hδ₁S⟩ := Metric.mem_nhdsWithin_iff.1 hSn
  obtain ⟨δ₂, hδ₂, hδ₂R⟩ := Metric.mem_nhdsWithin_iff.1 hRn
  have hq₀ : ((u₀, x₀) : U × X) ∈ S ×ˢ R :=
    ⟨mem_of_mem_nhdsWithin hu₀ hSn, mem_of_mem_nhdsWithin hx₀ hRn⟩
  rw [ContinuousWithinAt, nhdsWithin_prod_eq, nhdsWithin_univ, Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := min (min δ₁ δ₂) (ε / (4 * ((k : ℝ) + 1))) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (by positivity)
  have hkδ : (k : ℝ) * δ < ε / 4 := by
    have h1 : δ ≤ ε / (4 * ((k : ℝ) + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((k : ℝ) + 1))] at h1
    nlinarith [hδ]
  have hmem : ∀ q : U × X, q ∈ ri C ×ˢ ri D → dist q (u₀, x₀) < δ → q ∈ S ×ˢ R := by
    rintro ⟨u, x⟩ ⟨hu, hx⟩ hd
    rw [Prod.dist_eq] at hd
    exact ⟨hδ₁S ⟨mem_ball.2 (((le_max_left _ _).trans_lt hd).trans_le
        ((min_le_left _ _).trans (min_le_left _ _))), hu⟩,
      hδ₂R ⟨mem_ball.2 (((le_max_right _ _).trans_lt hd).trans_le
        ((min_le_left _ _).trans (min_le_right _ _))), hx⟩⟩
  obtain ⟨u₁, hu₁C', hu₁d⟩ := Metric.mem_closure_iff.1 (hCdense hu₀) δ hδ
  obtain ⟨x₁, hx₁D', hx₁d⟩ := Metric.mem_closure_iff.1 (hDdense hx₀) δ hδ
  have hq₁d : dist ((u₁, x₁) : U × X) (u₀, x₀) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (by rwa [dist_comm]) (by rwa [dist_comm])
  have hq₁ : ((u₁, x₁) : U × X) ∈ S ×ˢ R :=
    hmem _ ⟨hC' hu₁C', hD' hx₁D'⟩ hq₁d
  have hlip : ∀ t ∈ T₀, ∀ p ∈ S ×ˢ R, ∀ q ∈ S ×ˢ R,
      dist (F (p, t)) (F (q, t)) ≤ (k : ℝ) * dist p q :=
    fun t ht p hp q hq => (hk ⟨t, ht⟩).dist_le_mul p hp q hq
  have hnear : ∀ t ∈ T₀, dist (F (((u₁, x₁) : U × X), t)) (F (((u₀, x₀) : U × X), t)) < ε / 4 := by
    intro t ht
    refine lt_of_le_of_lt ((hlip t ht _ hq₁ _ hq₀).trans ?_) hkδ
    exact mul_le_mul_of_nonneg_left hq₁d.le hknn
  rw [Filter.eventually_prod_iff]
  refine ⟨fun q => q ∈ ri C ×ˢ ri D ∧ dist q (u₀, x₀) < δ,
    Filter.Eventually.and self_mem_nhdsWithin
      (eventually_nhdsWithin_of_eventually_nhds
        (Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun {_} h => h⟩)),
    fun t => t ∈ T₀ ∧ dist (F (((u₁, x₁) : U × X), t)) (F (((u₁, x₁) : U × X), t₀)) < ε / 4, ?_, ?_⟩
  · filter_upwards [hT₀n, Metric.tendsto_nhds.1 (hcont u₁ hu₁C' x₁ hx₁D').continuousAt (ε / 4)
      (by positivity)] with t h1 h2 using ⟨h1, h2⟩
  · rintro q ⟨hqW, hqd⟩ t ⟨htT₀, htd⟩
    have hqS : q ∈ S ×ˢ R := hmem q hqW hqd
    have h1 : dist (F (q, t)) (F (((u₀, x₀) : U × X), t)) < ε / 4 :=
      lt_of_le_of_lt ((hlip t htT₀ _ hqS _ hq₀).trans
        (mul_le_mul_of_nonneg_left hqd.le hknn)) hkδ
    have h2 : dist (F (((u₀, x₀) : U × X), t)) (F (((u₁, x₁) : U × X), t)) < ε / 4 := by
      rw [dist_comm]
      exact hnear t htT₀
    have h4 : dist (F (((u₁, x₁) : U × X), t₀)) (F (((u₀, x₀) : U × X), t₀)) < ε / 4 :=
      hnear t₀ ht₀T₀
    have htri := dist_triangle4 (F (q, t)) (F (((u₀, x₀) : U × X), t))
      (F (((u₁, x₁) : U × X), t)) (F (((u₀, x₀) : U × X), t₀))
    have htri' := dist_triangle (F (((u₁, x₁) : U × X), t)) (F (((u₁, x₁) : U × X), t₀))
      (F (((u₀, x₀) : U × X), t₀))
    linarith

/-- Let $U$ and $X$ be finite-dimensional real normed spaces, let $C \subseteq U$ and
$D \subseteq X$ be convex, and let $T$ be a locally compact topological space. Let
$F : (U \times X) \times T \to \mathbb{R}$ be such that $F(\cdot, t)$ is concave-convex on
$C \times D$ for every $t \in T$, and such that $t \mapsto F((u, x), t)$ is continuous for every
$(u, x) \in \operatorname{ri} C \times \operatorname{ri} D$. Then $F$ is jointly continuous
relative to $(\operatorname{ri} C \times \operatorname{ri} D) \times T$. -/
theorem continuousOn_prod_of_concaveConvexOn' (hC : Convex ℝ C) (hD : Convex ℝ D)
    {F : (U × X) × T → ℝ} (hF : ∀ t : T, ConcaveConvexOn C D fun p => F (p, t))
    (hcont : ∀ u ∈ ri C, ∀ x ∈ ri D, Continuous fun t => F ((u, x), t)) :
    ContinuousOn F ((ri C ×ˢ ri D) ×ˢ (univ : Set T)) :=
  continuousOn_prod_of_concaveConvexOn hC hD hF (subset_refl _) subset_closure
    (subset_refl _) subset_closure hcont

end JointContinuity

end ConvexAnalysis
