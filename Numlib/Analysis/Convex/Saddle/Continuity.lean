import Numlib.Analysis.Convex.Convergence
import Numlib.Analysis.Convex.Saddle.Kernel

/-!
# Continuity of finite saddle-functions

A finite concave-convex function on `C × D` is Lipschitz on every product of compact subsets of
`ri C` and `ri D`, hence continuous there; a pointwise bounded *family* of such functions is
uniformly bounded and equi-Lipschitz on such a rectangle; and the usual convergence and
Arzelà–Ascoli consequences follow. Each is a statement about convex functions of one variable,
applied once in each variable and combined.

## Main definitions

* `ConcaveConvexOn C D K` — `K : U × X → ℝ` is concave in its first argument on `C` for each point
  of `D` and convex in its second on `D` for each point of `C`. Its two fields are exactly the
  hypotheses the simple extensions of `Saddle/Kernel.lean` take.

## Main results

* `exists_forall_abs_le_and_lipschitzOnWith_prod` — a pointwise bounded family, indexed by an
  arbitrary type, is uniformly bounded and equi-Lipschitz (Theorem 35.2 in [^1]); the engine here.
* `ConcaveConvexOn.exists_lipschitzOnWith_of_isCompact`, `.exists_forall_abs_le_of_isCompact`,
  `.continuousOn` — the same for a single function, and continuity on `ri C × ri D`.
* `continuousOn_prod_of_concaveConvexOn`, `continuousOn_prod_of_concaveConvexOn'` — joint
  continuity in a parameter.
* `exists_tendstoUniformlyOn_prod_of_dense`, `tendstoUniformlyOn_prod_of_tendsto` — pointwise
  convergence on a dense set becomes uniform on compact rectangles, and
  `exists_subseq_tendstoUniformlyOn_prod` is the Arzelà–Ascoli form.
* `exists_isCompact_mem_nhdsWithin_relint`, `exists_isCompact_collar_relint` — `ri C` is locally
  compact, and a compact subset of it has a compact relative collar.
* `uniformCauchySeqOn_of_equiLipschitz` — the metric core of the convergence theorems, with the
  convexity stripped out.

## Implementation notes

Everything is stated for arbitrary convex `C` and `D`, with `ri C` and `ri D` written out; the
customary form takes them relatively open, where `ri C = C`. The Lipschitz constant is `α₁ + α₂`
rather than `2(α₁ + α₂)`, because Mathlib's product metric is the supremum metric and no factor is
paid passing between the coordinate distances and the distance on the product.

The convergence theorems take an arbitrary dense `A ⊆ ri C ×ˢ ri D` rather than a product
`C' ×ˢ D'`. The equi-Lipschitz input does need a product, but the diagonal extraction behind the
Arzelà–Ascoli statement produces a countable dense set that is not a product.

Unlike the one-variable theory, these results cannot be transported from the `interior` case along
a chart: the chart of `C ×ˢ D` is not the product of the charts of `C` and `D`, and it is the
product structure that the concave-convex hypothesis lives on. They are proved directly in `ri`.

## References

[^1]: R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §35.
-/

open Set Filter Topology Metric
open scoped NNReal Pointwise

namespace ConvexAnalysis

/-! ### Concave-convex functions on a rectangle -/

section Defs

variable {U X : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup X] [Module ℝ X]

/-- `K` is **concave-convex on `C × D`**: concave in its first argument on `C` for each point of
`D`, convex in its second on `D` for each point of `C`. The finite, set-relative form of
`ConcaveConvexFn`, and the hypothesis the continuity theory runs on. -/
structure ConcaveConvexOn (C : Set U) (D : Set X) (K : U × X → ℝ) : Prop where
  /-- `K (·, x)` is concave on `C` for every `x ∈ D`. -/
  concave_fst : ∀ x ∈ D, ConcaveOn ℝ C fun u => K (u, x)
  /-- `K (u, ·)` is convex on `D` for every `u ∈ C`. -/
  convex_snd : ∀ u ∈ C, ConvexOn ℝ D fun x => K (u, x)

variable {C : Set U} {D : Set X} {K : U × X → ℝ}

/-- The concave slice, as a family of *convex* functions: the form the convex lemmas consume. -/
theorem ConcaveConvexOn.convexOn_neg_fst (hK : ConcaveConvexOn C D K) {x : X} (hx : x ∈ D) :
    ConvexOn ℝ C fun u => -K (u, x) :=
  (hK.concave_fst x hx).neg

end Defs

/-! ### Negation

The one-variable results are stated for convex functions; the concave variable reaches them
through `-K`, and these lemmas carry the conclusions back. -/

section Neg

variable {ι : Type*} {g : ι → ℝ}

/-- A family of reals is bounded above iff its negation is bounded below. -/
theorem bddAbove_range_neg_iff : BddAbove (Set.range fun i => -g i) ↔ BddBelow (Set.range g) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact neg_le.1 (hb ⟨i, rfl⟩)⟩
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact neg_le_neg (hb ⟨i, rfl⟩)⟩

/-- A family of reals is bounded below iff its negation is bounded above. -/
theorem bddBelow_range_neg_iff : BddBelow (Set.range fun i => -g i) ↔ BddAbove (Set.range g) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact le_neg.1 (hb ⟨i, rfl⟩)⟩
  · rintro ⟨b, hb⟩
    exact ⟨-b, by rintro _ ⟨i, rfl⟩; exact neg_le_neg (hb ⟨i, rfl⟩)⟩

variable {E : Type*} [PseudoMetricSpace E] {f : E → ℝ} {S : Set E} {k : ℝ≥0}

/-- Negating a real-valued function does not change its Lipschitz constants. -/
theorem LipschitzOnWith.negReal (h : LipschitzOnWith k f S) :
    LipschitzOnWith k (fun x => -f x) S := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hd : dist (-f x) (-f y) = dist (f x) (f y) := by
    rw [Real.dist_eq, Real.dist_eq, neg_sub_neg, abs_sub_comm]
  rw [hd]
  exact h.dist_le_mul x hx y hy

/-- `-f` is Lipschitz on `S` exactly when `f` is. -/
theorem lipschitzOnWith_neg_iff : LipschitzOnWith k (fun x => -f x) S ↔ LipschitzOnWith k f S :=
  ⟨fun h => by simpa only [neg_neg] using LipschitzOnWith.negReal h,
    fun h => LipschitzOnWith.negReal h⟩

end Neg

/-! ### Uniform bounds and equi-Lipschitz constants for a family

The engine of the file: one-variable pointwise boundedness applied four times — twice to bound the
family, once in each variable, and twice to make it equi-Lipschitz. -/

section Family

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {ι : Type*} {C C' : Set U} {D D' : Set X} {K : ι → U × X → ℝ}

section Snd

variable [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ X] in
/-- The convex slices of a concave-convex family, at a point of `C`, as a family of convex
functions on `D`. -/
theorem convexOn_slice_snd (hK : ∀ i, ConcaveConvexOn C D (K i)) {u : U} (hu : u ∈ C) (i : ι) :
    ConvexOn ℝ D fun x => K i (u, x) :=
  (hK i).convex_snd u hu

/-- **The first bounding step**: for a fixed `u ∈ C'` the convex slices `K i (u, ·)` are uniformly
bounded on every compact `T ⊆ ri D`: the one-variable statement, in the second variable. -/
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

/-- **The second bounding step**: for a fixed `x ∈ D'` the concave slices `K i (·, x)` are uniformly
bounded on every compact `S ⊆ ri C`: the one-variable statement in the first variable, reached
through `-K`. -/
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

/-- **In the first variable**: the family is uniformly bounded on `S ×ˢ T` and equi-Lipschitz in
`u`, uniformly in `x ∈ T`. -/
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

/-- **In the second variable**: the family is equi-Lipschitz in `x`, uniformly in `u ∈ S`. -/
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

/-- A family of finite concave-convex functions on `C × D`, pointwise bounded on `C' × D'`, is
uniformly bounded and equi-Lipschitzian on `S ×ˢ T` for every compact `S ⊆ ri C` and `T ⊆ ri D`.

The customary hypothesis is `conv (cl (C' × D')) ⊇ C × D` for relatively open `C`, `D`; the form
used here is `C' ⊆ ri C ⊆ cl C'` and likewise for `D`, and `C' = ri C`, `D' = ri D` gives the
headline statement. -/
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

/-- A finite concave-convex function on `C × D` is Lipschitzian on every product of compact
subsets of `ri C` and `ri D`: the family statement at a one-element family. -/
theorem ConcaveConvexOn.exists_lipschitzOnWith_of_isCompact (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hL : ConcaveConvexOn C D L)
    {S : Set U} (hS : IsCompact S) (hSC : S ⊆ ri C)
    {T : Set X} (hT : IsCompact T) (hTD : T ⊆ ri D) :
    ∃ k : ℝ≥0, LipschitzOnWith k L (S ×ˢ T) := by
  obtain ⟨-, k, hk⟩ := exists_forall_abs_le_and_lipschitzOnWith_prod (K := fun _ : Unit => L)
    hC hD (fun _ => hL) (subset_refl _) subset_closure (subset_refl _) subset_closure
    (fun _ _ _ _ => (Set.finite_range _).isBounded) hS hSC hT hTD
  exact ⟨k, hk ()⟩

/-- A finite concave-convex function is bounded on every product of compact subsets of the
relative interiors. -/
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

/-! ### Compact relative neighbourhoods

`ri C` is locally compact — being a translate of an open subset of a finite-dimensional subspace —
which is what turns "Lipschitz on every compact rectangle" into "continuous". -/

section LocallyCompact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- **Every point of `ri C` has a compact relative neighbourhood inside `ri C`.** -/
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

/-- A finite concave-convex function on `C × D` is continuous relative to `ri C × ri D`.
Continuity is local, `ri C` and `ri D` are locally compact, and on a compact rectangle the function
is Lipschitz. -/
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

/-! ### The relative collar

The convergence and joint-continuity theorems need, for a compact `S ⊆ ri C`, a slightly larger
compact subset of `ri C` containing every point of `ri C` near `S`.
`IsCompact.exists_cthickening_subset_open` will not serve: `cthickening ε S ⊆ ri C` is false,
because points off the affine hull of `C` are near `S`. -/

section Collar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E}

/-- **A compact subset of `ri C` has a relative collar**: an `ε > 0` and a compact `S' ⊆ ri C`
containing `S` and every point of `ri C` within `ε` of `S`. The relative analogue of
`IsCompact.exists_cthickening_subset_open`, and what makes the `interior` proofs of the
one-variable convergence theorems run in `ri`. -/
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

/-! ### Equi-Lipschitz plus a dense Cauchy set

The metric core of the convergence theorems, with the convexity stripped out: on a compact `S`
carrying a collar `S'` on which the sequence is equi-Lipschitz, pointwise Cauchy behaviour on a
dense subset of `S` is already uniform Cauchy behaviour on `S`. -/

section UniformCauchy

variable {Ω : Type*} [PseudoMetricSpace Ω] {f : ℕ → Ω → ℝ} {A S S' : Set Ω} {ε : ℝ} {k : ℝ≥0}

/-- **Equi-Lipschitz on a collar plus pointwise Cauchy on a dense subset gives uniform Cauchy.**
`hcollar` is the only thing the ambient structure has to supply: every point of `A` within `ε` of
`S` must lie in `S'`, the set on which the family is equi-Lipschitz. In the `interior` setting
`S' = cthickening ε S`; in the relative setting it is `exists_isCompact_collar_relint`. -/
theorem uniformCauchySeqOn_of_equiLipschitz (hS : IsCompact S) (hSS' : S ⊆ S') (hε : 0 < ε)
    (hcollar : ∀ y ∈ A, ∀ x ∈ S, dist y x ≤ ε → y ∈ S')
    (hdense : S ⊆ closure A) (hlip : ∀ i, LipschitzOnWith k (f i) S')
    (hcau : ∀ z ∈ A, CauchySeq fun i => f i z) :
    UniformCauchySeqOn f atTop S := by
  classical
  rw [Metric.uniformCauchySeqOn_iff]
  intro δ hδ
  have hknn : (0 : ℝ) ≤ (k : ℝ) := k.coe_nonneg
  set ρ : ℝ := min ε (δ / (3 * ((k : ℝ) + 1))) with hρdef
  have hρ : 0 < ρ := lt_min hε (by positivity)
  have hkρ : (k : ℝ) * ρ < δ / 3 := by
    have h1 : ρ ≤ δ / (3 * ((k : ℝ) + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 3 * ((k : ℝ) + 1))] at h1
    nlinarith [hρ]
  have hcover : S ⊆ ⋃ z ∈ A ∩ S', ball z ρ := by
    intro x hx
    obtain ⟨z, hzA, hxz⟩ := Metric.mem_closure_iff.1 (hdense hx) ρ hρ
    refine mem_biUnion ⟨hzA, hcollar z hzA x hx ?_⟩ (by rwa [mem_ball])
    rw [dist_comm]
    exact hxz.le.trans (min_le_left _ _)
  obtain ⟨b, hbsub, hbfin, hbcover⟩ :=
    hS.elim_finite_subcover_image (fun z (_ : z ∈ A ∩ S') => isOpen_ball) hcover
  have hNex : ∀ z : Ω, ∃ N : ℕ, z ∈ b → ∀ m ≥ N, ∀ n ≥ N, dist (f m z) (f n z) < δ / 3 := by
    intro z
    by_cases hz : z ∈ b
    · obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hcau z (hbsub hz).1) (δ / 3) (by positivity)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose Nf hNf using hNex
  refine ⟨hbfin.toFinset.sup Nf, fun m hm n hn x hx => ?_⟩
  obtain ⟨z, hzb, hxz⟩ := mem_iUnion₂.1 (hbcover hx)
  have hNz : Nf z ≤ hbfin.toFinset.sup Nf := Finset.le_sup (hbfin.mem_toFinset.2 hzb)
  have hmid : dist (f m z) (f n z) < δ / 3 := hNf z hzb m (hNz.trans hm) n (hNz.trans hn)
  have hzS' : z ∈ S' := (hbsub hzb).2
  have hxS' : x ∈ S' := hSS' hx
  have hdxz : dist x z < ρ := by rwa [mem_ball] at hxz
  have hkd : (k : ℝ) * dist x z ≤ (k : ℝ) * ρ := by
    nlinarith [dist_nonneg (x := x) (y := z)]
  have hd1 : dist (f m x) (f m z) ≤ (k : ℝ) * dist x z := (hlip m).dist_le_mul x hxS' z hzS'
  have hd2 : dist (f n x) (f n z) ≤ (k : ℝ) * dist x z := (hlip n).dist_le_mul x hxS' z hzS'
  have htri := dist_triangle4 (f m x) (f m z) (f n z) (f n x)
  rw [dist_comm (f n z) (f n x)] at htri
  linarith

end UniformCauchy

/-! ### Convergence

Both are the one-variable statements with the compact set replaced by a compact *rectangle*: the
family theorem supplies the equi-Lipschitz constant, `exists_isCompact_collar_relint` the room to
move in, and `uniformCauchySeqOn_of_equiLipschitz` does the rest. -/

section Convergence

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C C' : Set U} {D D' : Set X} {K : ℕ → U × X → ℝ}

/-- **The uniform Cauchy property behind both convergence theorems**: a sequence of finite
concave-convex functions, pointwise bounded on `C' × D'` and pointwise Cauchy on a set `A` dense in
`ri C × ri D`, is uniformly Cauchy on every compact rectangle inside `ri C × ri D`. -/
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

/-- A sequence of finite concave-convex functions on `C × D`, whose values are bounded at every
point of a product `C' × D'` dense in `ri C × ri D` and convergent at every point of a dense
`A ⊆ ri C × ri D`, converges at every point of `ri C × ri D` to a finite concave-convex limit,
uniformly on every compact rectangle. Taking `A = C' ×ˢ D'` gives the customary statement. -/
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

/-- The same in its customary form: pointwise convergence on a *product* of dense subsets. -/
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

/-- With the limit supplied: pointwise convergence on all of `ri C × ri D` upgrades to uniform
convergence on compact rectangles. -/
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

/-- **Arzelà–Ascoli for saddle-functions**: a sequence of finite concave-convex functions on
`C × D` whose values are bounded at every point of a product `C' × D'` dense in `ri C × ri D` has a
subsequence converging, uniformly on every compact rectangle inside `ri C × ri D`, to a finite
concave-convex function.

As in one variable the subsequence comes from a countable dense subset of the *product* `C' ×ˢ D'`,
which is why `exists_tendstoUniformlyOn_prod_of_dense` is stated for a general dense `A`. -/
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
  rcases A.eq_empty_or_nonempty with rfl | hne
  · rw [closure_empty] at hAdense
    have hempty : ri C ×ˢ ri D = ∅ := Set.subset_empty_iff.1 hAdense
    refine ⟨id, fun _ => 0, strictMono_id,
      ⟨fun _ _ => concaveOn_const _ (Convex.relint hC),
        fun _ _ => convexOn_const _ (Convex.relint hD)⟩,
      fun p hp => absurd hp (hempty ▸ notMem_empty p), fun S hS hSC T hT hTD => ?_⟩
    have : S ×ˢ T = ∅ :=
      Set.subset_empty_iff.1 fun p hp => hempty ▸ Set.mem_prod.2 ⟨hSC hp.1, hTD hp.2⟩
    rw [this]
    exact fun u hu => Filter.Eventually.of_forall (by simp)
  obtain ⟨e, he⟩ := hAcnt.exists_eq_range hne
  have hmemA : ∀ n, e n ∈ A := fun n => he ▸ mem_range_self n
  have hBex : ∀ n, ∃ B : ℝ, ∀ i, |K i (e n)| ≤ B := by
    intro n
    obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hbddA (e n) (hmemA n))
    exact ⟨B, fun i => by simpa [Real.norm_eq_abs] using hB _ (mem_range_self i)⟩
  choose B hB using hBex
  have hKcpt : IsCompact (Set.pi univ fun n => Icc (-(B n)) (B n)) :=
    isCompact_univ_pi fun n => isCompact_Icc
  have hmem : ∀ i, (fun n => K i (e n)) ∈ Set.pi univ fun n => Icc (-(B n)) (B n) :=
    fun i n _ => Set.mem_Icc.2 (abs_le.1 (hB n i))
  obtain ⟨w, -, φ, hφ, hlim⟩ := hKcpt.isSeqCompact hmem
  have hptw : ∀ n, Tendsto (fun i => K (φ i) (e n)) atTop (𝓝 (w n)) :=
    fun n => tendsto_pi_nhds.1 hlim n
  obtain ⟨L, hLcc, hLtend, huc⟩ := exists_tendstoUniformlyOn_prod_of_dense hC hD
    (fun i => hK (φ i)) hC' hCdense hD' hDdense
    (fun u hu x hx => (hbdd u hu x hx).subset (by rintro _ ⟨i, rfl⟩; exact ⟨φ i, rfl⟩)) hA hAdense
    fun p hp => by
      rw [he] at hp
      obtain ⟨n, rfl⟩ := hp
      exact ⟨w n, hptw n⟩
  exact ⟨φ, L, hφ, hLcc, hLtend, huc⟩

end Convergence

/-! ### Joint continuity in a parameter -/

section JointContinuity

variable {U X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {C C' : Set U} {D D' : Set X} {T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]

/-- A real-valued function of `(u, x, t)` with `T` locally compact, concave-convex in `(u, x)`
for each `t` and continuous in `t` for each `(u, x)`, is *jointly* continuous relative to
`ri C × ri D × T`.

Continuity in `t` is only needed at the points of dense subsets `C'` and `D'`;
`continuousOn_prod_of_concaveConvexOn'` is the headline statement. On a compact neighbourhood `T₀`
of `t₀` the family `{F(·, t) | t ∈ T₀}` is pointwise bounded on `C' × D'`, so the family theorem
equi-Lipschitz near `(u₀, x₀)`, and a four-term estimate through a nearby point closes it. -/
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

/-- The same with continuity in the parameter assumed at *every* point of `ri C × ri D`. -/
theorem continuousOn_prod_of_concaveConvexOn' (hC : Convex ℝ C) (hD : Convex ℝ D)
    {F : (U × X) × T → ℝ} (hF : ∀ t : T, ConcaveConvexOn C D fun p => F (p, t))
    (hcont : ∀ u ∈ ri C, ∀ x ∈ ri D, Continuous fun t => F ((u, x), t)) :
    ContinuousOn F ((ri C ×ˢ ri D) ×ˢ (univ : Set T)) :=
  continuousOn_prod_of_concaveConvexOn hC hD hF (subset_refl _) subset_closure
    (subset_refl _) subset_closure hcont

end JointContinuity

end ConvexAnalysis
