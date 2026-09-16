import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import NumlibSurface.Rockafellar.Common.Euclidean

/-!
# Rockafellar, §3: The Algebra of Convex Sets

Operations that preserve convexity: scalar multiples, sums, convex combinations of a family of
sets, images and inverse images under linear maps, direct sums, partial addition, and the inverse
sum. All 9 numbered results of §3 are formalized.

## Main definitions

* `convexCombinations` — the union of all finite convex combinations `∑ λᵢ Cᵢ` of a family of
  sets, which is the right-hand side of Theorem 3.3.
* `partialAdd` — the **partial addition** of Theorem 3.6: add in the second argument, intersect in
  the first. The book describes the operation informally and fixes no symbol for it, so its
  commutativity, associativity and two extreme cases (`m = 0` is ordinary addition, `p = 0` is
  intersection) are proved here; §5 rests on them.
* `invSum` — Rockafellar's **inverse sum** `C₁ # C₂`. It has no backbone counterpart, so it comes
  with three bridges: `mem_invSum_iff_exists`, `invSum_eq_iUnion_singleton`, and
  `invSum_eq_partialAdd_coneLift`, the derivation from partial addition that Theorem 3.7's
  one-line proof appeals to.
* `coneLift` — the convex cone in `ℝⁿ⁺¹` with cross-section `C`, through which the book derives
  `#` from partial addition.

`λC`, `−C` and `C₁ + C₂` need no definition of their own: they are Mathlib's pointwise `a • s`,
`-s` and `s + t`, and the book's displayed formulas for them are those definitions on the nose.
`ℝᵐ⁺ᵖ` is `Rn m × Rn p` here, which is the shape in which §3 actually uses it — a vector of
`ℝᵐ⁺ᵖ` is written `(y, z)` throughout. `theorem_3_8_invSum` drops the convexity the book assumes,
its proof not using it; `theorem_3_8_add` keeps it.

## References

* [rockafellar1970convex] §3.
-/

namespace Rockafellar

open ConvexAnalysis
open scoped Pointwise

variable {n m p : ℕ}

/-! ### Scalar multiples, reflections and sums -/

/-- A non-empty symmetric convex set contains the origin: along with each `x` it contains `-x`,
hence the whole segment between them. -/
theorem zero_mem_of_neg_eq_self {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty)
    (hsym : -C = C) : (0 : Rn n) ∈ C := by
  obtain ⟨x, hx⟩ := hne
  have hneg : -x ∈ C := by rw [← hsym]; exact Set.neg_mem_neg.2 hx
  have h := hC hx hneg (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simpa using h

/-- **Theorem 3.1.** The sum `C₁ + C₂ = {x₁ + x₂ | x₁ ∈ C₁, x₂ ∈ C₂}` of two convex sets is
convex. -/
theorem theorem_3_1 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂) :
    Convex ℝ (C₁ + C₂) :=
  Convex.add h₁ h₂

/-- Additive inverses do not exist for sets with more than one point; the best one can say in
general is that `0 ∈ C + (-C)` when `C ≠ ∅`. -/
theorem zero_mem_add_neg {C : Set (Rn n)} (hne : C.Nonempty) : (0 : Rn n) ∈ C + -C := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, hx, -x, Set.neg_mem_neg.2 hx, by simp⟩

/-- **Theorem 3.2.** `(λ₁ + λ₂) C = λ₁ C + λ₂ C` for convex `C` and `λ₁, λ₂ ≥ 0`. This is the one
law of set algebra in §3 that depends on convexity: `⊆` holds for any `C`, and `⊇` is the
convexity relation `C ⊇ (λ₁/(λ₁+λ₂)) C + (λ₂/(λ₁+λ₂)) C` multiplied through by `λ₁ + λ₂`. -/
theorem theorem_3_2 {C : Set (Rn n)} (hC : Convex ℝ C) {l₁ l₂ : ℝ} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂) :
    (l₁ + l₂) • C = l₁ • C + l₂ • C :=
  Convex.add_smul hC h₁ h₂

/-- **Rockafellar, §3 (p. 17).** Convexity of `C` says `(1 - λ) C + λ C ⊆ C` for `0 < λ < 1`;
Theorem 3.2 is what upgrades that inclusion to an equality. -/
theorem smul_add_smul_self {C : Set (Rn n)} (hC : Convex ℝ C) {l : ℝ} (h₀ : 0 ≤ l)
    (h₁ : l ≤ 1) : (1 - l) • C + l • C = C := by
  rw [← theorem_3_2 hC (by linarith) h₀, sub_add_cancel, one_smul]

/-- **Rockafellar, §3 (p. 19).** `C + C = 2C` for convex `C`, the first consequence the book draws
from Theorem 3.2. -/
theorem add_self_eq_two_smul {C : Set (Rn n)} (hC : Convex ℝ C) : C + C = (2 : ℝ) • C := by
  rw [show (2:ℝ) = 1 + 1 by norm_num, theorem_3_2 hC zero_le_one zero_le_one, one_smul]

/-! ### Theorem 3.3: the convex hull of a union -/

/-- The right-hand side of **Theorem 3.3**: the union of all *finite convex
combinations* `λ₁ C_{i₁} + ⋯ + λ_m C_{i_m}` of the family `C`, taken over all non-negative choices
of the coefficients `λᵢ` of which only finitely many are non-zero and which add up to `1`. -/
def convexCombinations {I : Type*} (C : I → Set (Rn n)) : Set (Rn n) :=
  ⋃ (s : Finset I) (w : I → ℝ) (_ : ∀ i ∈ s, 0 ≤ w i) (_ : ∑ i ∈ s, w i = 1), ∑ i ∈ s, w i • C i

/-- Membership in `convexCombinations`, with the four nested unions unpacked. -/
theorem mem_convexCombinations {I : Type*} {C : I → Set (Rn n)} {x : Rn n} :
    x ∈ convexCombinations C ↔ ∃ (s : Finset I) (w : I → ℝ), (∀ i ∈ s, 0 ≤ w i) ∧
      (∑ i ∈ s, w i = 1) ∧ x ∈ ∑ i ∈ s, w i • C i := by
  simp only [convexCombinations, Set.mem_iUnion, exists_prop]

/-- Padding a finite combination of *sets* with zeros over a larger index set. This is where
non-emptiness of the `Cᵢ` is used: `0 • Cᵢ` is `{0}` only for non-empty `Cᵢ`. -/
private theorem sum_smul_extend {I : Type*} {C : I → Set (Rn n)} (hne : ∀ i, (C i).Nonempty)
    {s u : Finset I} (hsu : s ⊆ u) (w : I → ℝ) (hw : ∀ i ∈ u, i ∉ s → w i = 0) :
    ∑ i ∈ s, w i • C i = ∑ i ∈ u, w i • C i := by
  refine Finset.sum_subset hsu fun i hiu his => ?_
  rw [hw i hiu his, Set.zero_smul_set (hne i)]

/-- A point of a finite convex combination of non-empty sets, re-presented over any larger index
set: the weights are padded with zeros and a representative is chosen in each `Cᵢ`. -/
private theorem exists_rep_of_mem_sum {I : Type*} {C : I → Set (Rn n)} (hne : ∀ i, (C i).Nonempty)
    {s u : Finset I} (hsu : s ⊆ u) {w : I → ℝ} (hw₀ : ∀ i ∈ s, 0 ≤ w i)
    (hw₁ : ∑ i ∈ s, w i = 1) {x : Rn n} (hx : x ∈ ∑ i ∈ s, w i • C i) :
    ∃ (w' : I → ℝ) (z : I → Rn n), (∀ i, 0 ≤ w' i) ∧ (∑ i ∈ u, w' i = 1) ∧
      (∀ i ∈ u, z i ∈ C i) ∧ ∑ i ∈ u, w' i • z i = x := by
  classical
  obtain ⟨w', hzero, heq⟩ : ∃ w' : I → ℝ, (∀ i, i ∉ s → w' i = 0) ∧ ∀ i ∈ s, w' i = w i :=
    ⟨fun i => if i ∈ s then w i else 0, fun i hi => by simp [hi], fun i hi => by simp [hi]⟩
  have hzero' : ∀ i ∈ u, i ∉ s → w' i = 0 := fun i _ hi => hzero i hi
  have hx' : x ∈ ∑ i ∈ s, w' i • C i := by
    rwa [Finset.sum_congr rfl fun i hi => by rw [heq i hi]]
  rw [sum_smul_extend hne hsu w' hzero', Set.mem_finsetSum] at hx'
  obtain ⟨g, hg, hgx⟩ := hx'
  have hex : ∀ i ∈ u, ∃ y ∈ C i, w' i • y = g i := fun i hi => Set.mem_smul_set.1 (hg hi)
  choose! z hz hz' using hex
  refine ⟨w', z, ?_, ?_, hz, ?_⟩
  · intro i
    by_cases hi : i ∈ s
    · rw [heq i hi]; exact hw₀ i hi
    · rw [hzero i hi]
  · rw [← Finset.sum_subset hsu hzero', Finset.sum_congr rfl heq]; exact hw₁
  · rw [Finset.sum_congr rfl fun i hi => hz' i hi]; exact hgx

/-- Every finite convex combination of the `Cᵢ` lies in the convex hull of their union. -/
private theorem sum_smul_subset_convexHull {I : Type*} (C : I → Set (Rn n)) {s : Finset I}
    {w : I → ℝ} (hw₀ : ∀ i ∈ s, 0 ≤ w i) (hw₁ : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i • C i) ⊆ convexHull ℝ (⋃ i, C i) := by
  intro x hx
  rw [Set.mem_finsetSum] at hx
  obtain ⟨g, hg, hgx⟩ := hx
  have hex : ∀ i ∈ s, ∃ y ∈ C i, w i • y = g i := fun i hi => Set.mem_smul_set.1 (hg hi)
  choose! y hy hy' using hex
  rw [← hgx, Finset.sum_congr rfl fun i hi => (hy' i hi).symm]
  exact Convex.sum_mem (convex_convexHull ℝ _) hw₀ hw₁ fun i hi =>
    subset_convexHull ℝ _ (Set.mem_iUnion.2 ⟨i, hy i hi⟩)

/-- Each member of the family is itself a finite convex combination: take the single index with
coefficient `1`. -/
private theorem subset_convexCombinations {I : Type*} (C : I → Set (Rn n)) :
    (⋃ i, C i) ⊆ convexCombinations C := by
  classical
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
  refine mem_convexCombinations.2 ⟨{j}, fun i => if i = j then 1 else 0, ?_, by simp, ?_⟩
  · intro i _
    by_cases hi : i = j <;> simp [hi]
  · simpa using hj

/-- The set of finite convex combinations of a family of non-empty convex sets is convex. Two
combinations are compared over the union of their index sets, and the coefficientwise merge is
Theorem 3.2 applied in each `Cᵢ`. -/
private theorem convex_convexCombinations {I : Type*} {C : I → Set (Rn n)}
    (hC : ∀ i, Convex ℝ (C i)) (hne : ∀ i, (C i).Nonempty) :
    Convex ℝ (convexCombinations C) := by
  classical
  intro x hx y hy a b ha hb hab
  obtain ⟨s, w, hw₀, hw₁, hxs⟩ := mem_convexCombinations.1 hx
  obtain ⟨t, v, hv₀, hv₁, hyt⟩ := mem_convexCombinations.1 hy
  obtain ⟨w', xs, hw'₀, hw'₁, hxsC, hxsum⟩ :=
    exists_rep_of_mem_sum (u := s ∪ t) hne Finset.subset_union_left hw₀ hw₁ hxs
  obtain ⟨v', ys, hv'₀, hv'₁, hysC, hysum⟩ :=
    exists_rep_of_mem_sum (u := s ∪ t) hne Finset.subset_union_right hv₀ hv₁ hyt
  refine mem_convexCombinations.2 ⟨s ∪ t, fun i => a * w' i + b * v' i,
    fun i _ => add_nonneg (mul_nonneg ha (hw'₀ i)) (mul_nonneg hb (hv'₀ i)), ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw'₁, hv'₁]
    linarith
  · have hmem : ∀ i ∈ s ∪ t,
        (a * w' i) • xs i + (b * v' i) • ys i ∈ (a * w' i + b * v' i) • C i := by
      intro i hi
      rw [theorem_3_2 (hC i) (mul_nonneg ha (hw'₀ i)) (mul_nonneg hb (hv'₀ i))]
      exact Set.add_mem_add (Set.smul_mem_smul_set (hxsC i hi)) (Set.smul_mem_smul_set (hysC i hi))
    have hsum : ∑ i ∈ s ∪ t, ((a * w' i) • xs i + (b * v' i) • ys i) = a • x + b • y := by
      rw [Finset.sum_add_distrib]
      simp only [mul_smul]
      rw [← Finset.smul_sum, ← Finset.smul_sum, hxsum, hysum]
    rw [← hsum]
    exact Set.finsetSum_mem_finsetSum _ _ _ hmem

/-- **Theorem 3.3.** The convex hull of the union of a collection of non-empty convex sets `Cᵢ`
is `⋃ ∑ᵢ λᵢ Cᵢ`, the union over all non-negative coefficient families with finite support summing
to `1`. -/
theorem theorem_3_3 {I : Type*} {C : I → Set (Rn n)} (hC : ∀ i, Convex ℝ (C i))
    (hne : ∀ i, (C i).Nonempty) :
    convexHull ℝ (⋃ i, C i) = convexCombinations C := by
  refine Set.Subset.antisymm
    (convexHull_min (subset_convexCombinations C) (convex_convexCombinations hC hne)) ?_
  intro x hx
  obtain ⟨s, w, hw₀, hw₁, hxs⟩ := mem_convexCombinations.1 hx
  exact sum_smul_subset_convexHull C hw₀ hw₁ hxs

/-! ### Theorem 3.4: images and inverse images -/

/-- **Theorem 3.4** (first clause). The image `AC = {Ax | x ∈ C}` of a convex set under a linear
transformation is convex. -/
theorem theorem_3_4_image (A : Rn n →ₗ[ℝ] Rn m) {C : Set (Rn n)} (hC : Convex ℝ C) :
    Convex ℝ (A '' C) :=
  Convex.linear_image hC A

/-- **Theorem 3.4** (second clause). The inverse image `A⁻¹D = {x | Ax ∈ D}` of a convex set is
convex. The notation does not imply that `A` is invertible. -/
theorem theorem_3_4_preimage (A : Rn n →ₗ[ℝ] Rn m) {D : Set (Rn m)} (hD : Convex ℝ D) :
    Convex ℝ (A ⁻¹' D) :=
  Convex.linear_preimage hD A

/-- **Corollary 3.4.1.** The orthogonal projection of a convex set `C` on a subspace
`L` is another convex set: the projection assigns to each `x` the unique `y ∈ L` with `x - y ⊥ L`,
and that assignment is linear, so Theorem 3.4 applies. -/
theorem corollary_3_4_1 (L : Submodule ℝ (Rn n)) [L.HasOrthogonalProjection] {C : Set (Rn n)}
    (hC : Convex ℝ C) : Convex ℝ (L.starProjection '' C) :=
  Convex.is_linear_image hC
    ⟨fun x y => map_add L.starProjection x y, fun c x => map_smul L.starProjection c x⟩

/-! ### Theorem 3.5: the direct sum -/

/-- **Theorem 3.5.** The *direct sum* `C ⊕ D = {(y, z) | y ∈ C, z ∈ D}` of convex sets is convex.
`C ⊕ D` is Mathlib's `C ×ˢ D`, on `Rn m × Rn p` rather than `Rn (m + p)`. -/
theorem theorem_3_5 {C : Set (Rn m)} {D : Set (Rn p)} (hC : Convex ℝ C) (hD : Convex ℝ D) :
    Convex ℝ (C ×ˢ D) :=
  Convex.prod hC hD

/-- Each `x ∈ C + D` decomposes uniquely as `x = y + z` with `y ∈ C`, `z ∈ D` — the case in which
`C + D` is also called a *direct sum* — iff `(C - C) ∩ (D - D) = {0}`. The book states this
without proof. -/
theorem directSum_iff_unique {C D : Set (Rn n)} (hC : C.Nonempty) (hD : D.Nonempty) :
    (∀ y₁ ∈ C, ∀ z₁ ∈ D, ∀ y₂ ∈ C, ∀ z₂ ∈ D, y₁ + z₁ = y₂ + z₂ → y₁ = y₂ ∧ z₁ = z₂) ↔
      (C - C) ∩ (D - D) = {0} := by
  constructor
  · intro h
    refine Set.Subset.antisymm ?_ ?_
    · rintro u ⟨⟨c₁, hc₁, c₂, hc₂, hc⟩, ⟨d₁, hd₁, d₂, hd₂, hd⟩⟩
      have hc' : c₁ - c₂ = u := hc
      have hd' : d₁ - d₂ = u := hd
      have hcd : c₁ - c₂ = d₁ - d₂ := hc'.trans hd'.symm
      rw [sub_eq_sub_iff_add_eq_add] at hcd
      obtain ⟨he, -⟩ := h c₁ hc₁ d₂ hd₂ c₂ hc₂ d₁ hd₁ (hcd.trans (add_comm _ _))
      rw [Set.mem_singleton_iff, ← hc', he, sub_self]
    · obtain ⟨c, hc⟩ := hC
      obtain ⟨d, hd⟩ := hD
      rintro u hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact ⟨⟨c, hc, c, hc, sub_self c⟩, ⟨d, hd, d, hd, sub_self d⟩⟩
  · intro h y₁ hy₁ z₁ hz₁ y₂ hy₂ z₂ hz₂ hsum
    have hz : z₂ - z₁ = y₁ - y₂ := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm z₂ y₂]
      exact hsum.symm
    have hmem : y₁ - y₂ ∈ (C - C) ∩ (D - D) :=
      ⟨⟨y₁, hy₁, y₂, hy₂, rfl⟩, ⟨z₂, hz₂, z₁, hz₁, hz⟩⟩
    rw [h, Set.mem_singleton_iff, sub_eq_zero] at hmem
    refine ⟨hmem, ?_⟩
    rw [hmem] at hsum
    exact add_left_cancel hsum

/-! ### Theorem 3.6: partial addition -/

section PartialAdd

variable {Y Z : Type*}

/-- **Partial addition**, the operation of Theorem 3.6: `partialAdd C₁ C₂` is the set of `(y, z)`
for which there are `z₁, z₂` with `(y, z₁) ∈ C₁`, `(y, z₂) ∈ C₂` and `z₁ + z₂ = z`. The book
describes this in words as "adding in the `z` argument alone" and fixes no symbol for it; there is
one such operation for each decomposition of `ℝⁿ` into a direct sum of two subspaces. -/
def partialAdd [Add Z] (C₁ C₂ : Set (Y × Z)) : Set (Y × Z) :=
  {q | ∃ z₁ z₂, (q.1, z₁) ∈ C₁ ∧ (q.1, z₂) ∈ C₂ ∧ z₁ + z₂ = q.2}

/-- Membership in `partialAdd`, at an explicit pair. -/
@[simp] theorem mem_partialAdd [Add Z] {C₁ C₂ : Set (Y × Z)} {y : Y} {z : Z} :
    (y, z) ∈ partialAdd C₁ C₂ ↔ ∃ z₁ z₂, (y, z₁) ∈ C₁ ∧ (y, z₂) ∈ C₂ ∧ z₁ + z₂ = z :=
  Iff.rfl

/-- **Rockafellar, §3 (p. 20).** Partial addition is commutative. -/
theorem partialAdd_comm [AddCommMonoid Z] (C₁ C₂ : Set (Y × Z)) :
    partialAdd C₁ C₂ = partialAdd C₂ C₁ := by
  ext ⟨y, z⟩
  constructor <;> rintro ⟨z₁, z₂, h₁, h₂, h⟩ <;>
    exact ⟨z₂, z₁, h₂, h₁, by rw [add_comm]; exact h⟩

/-- **Rockafellar, §3 (p. 20).** Partial addition is associative. -/
theorem partialAdd_assoc [AddCommMonoid Z] (C₁ C₂ C₃ : Set (Y × Z)) :
    partialAdd (partialAdd C₁ C₂) C₃ = partialAdd C₁ (partialAdd C₂ C₃) := by
  ext ⟨y, z⟩
  constructor
  · rintro ⟨z₁₂, z₃, ⟨z₁, z₂, h₁, h₂, rfl⟩, h₃, h⟩
    exact ⟨z₁, z₂ + z₃, h₁, ⟨z₂, z₃, h₂, h₃, rfl⟩, by rw [← add_assoc]; exact h⟩
  · rintro ⟨z₁, z₂₃, h₁, ⟨z₂, z₃, h₂, h₃, rfl⟩, h⟩
    exact ⟨z₁ + z₂, z₃, ⟨z₁, z₂, h₁, h₂, rfl⟩, h₃, by rw [add_assoc]; exact h⟩

/-- **Rockafellar, §3 (p. 20), the extreme case `m = 0`.** When the first factor is trivial,
partial addition is ordinary addition of sets. -/
theorem partialAdd_eq_add [Add Y] [Add Z] [Subsingleton Y] (C₁ C₂ : Set (Y × Z)) :
    partialAdd C₁ C₂ = C₁ + C₂ := by
  ext ⟨y, z⟩
  constructor
  · rintro ⟨z₁, z₂, h₁, h₂, hz⟩
    refine ⟨(y, z₁), h₁, (y, z₂), h₂, ?_⟩
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨Subsingleton.elim _ _, hz⟩
  · rintro ⟨⟨y₁, z₁⟩, h₁, ⟨y₂, z₂⟩, h₂, hq⟩
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at hq
    refine ⟨z₁, z₂, ?_, ?_, hq.2⟩
    · rwa [Subsingleton.elim y y₁]
    · rwa [Subsingleton.elim y y₂]

/-- **Rockafellar, §3 (p. 20), the extreme case `p = 0`.** When the second factor is trivial,
partial addition is intersection. -/
theorem partialAdd_eq_inter [Add Z] [Subsingleton Z] (C₁ C₂ : Set (Y × Z)) :
    partialAdd C₁ C₂ = C₁ ∩ C₂ := by
  ext ⟨y, z⟩
  constructor
  · rintro ⟨z₁, z₂, h₁, h₂, -⟩
    exact ⟨by rwa [Subsingleton.elim z z₁], by rwa [Subsingleton.elim z z₂]⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨z, z, h₁, h₂, Subsingleton.elim _ _⟩

end PartialAdd

/-- **Theorem 3.6.** Let `C₁` and `C₂` be convex sets in `ℝᵐ⁺ᵖ`, and let `C` be the
set of vectors `x = (y, z)` such that there exist `z₁` and `z₂` with `(y, z₁) ∈ C₁`,
`(y, z₂) ∈ C₂` and `z₁ + z₂ = z`. Then `C` is a convex set in `ℝᵐ⁺ᵖ`. -/
theorem theorem_3_6 {C₁ C₂ : Set (Rn m × Rn p)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂) :
    Convex ℝ (partialAdd C₁ C₂) := by
  rintro ⟨y, z⟩ ⟨z₁, z₂, hz₁, hz₂, hz⟩ ⟨y', z'⟩ ⟨z₁', z₂', hz₁', hz₂', hz'⟩ a b ha hb hab
  refine ⟨a • z₁ + b • z₁', a • z₂ + b • z₂', ?_, ?_, ?_⟩
  · simpa [Prod.smul_mk, Prod.mk_add_mk] using h₁ hz₁ hz₁' ha hb hab
  · simpa [Prod.smul_mk, Prod.mk_add_mk] using h₂ hz₂ hz₂' ha hb hab
  · subst hz
    subst hz'
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_add]
    abel

/-- **Rockafellar, §3 (p. 20).** Ordinary addition of convex sets in `ℝⁿ` is the extreme case
`m = 0` of Theorem 3.6. -/
theorem theorem_3_6_add (C₁ C₂ : Set (Rn 0 × Rn p)) : partialAdd C₁ C₂ = C₁ + C₂ :=
  partialAdd_eq_add C₁ C₂

/-- **Rockafellar, §3 (p. 20).** Intersection of convex sets in `ℝⁿ` is the extreme case `p = 0`
of Theorem 3.6. -/
theorem theorem_3_6_inter (C₁ C₂ : Set (Rn m × Rn 0)) : partialAdd C₁ C₂ = C₁ ∩ C₂ :=
  partialAdd_eq_inter C₁ C₂

/-! ### Theorem 3.7: the inverse sum -/

/-- Rockafellar's **inverse sum** `C₁ # C₂ = ⋃ {(1 - λ) C₁ ∩ λ C₂ | 0 ≤ λ ≤ 1}`. The book obtains
it as the partial addition "in the `λ` argument alone" of the cones in `ℝⁿ⁺¹` corresponding to
`C₁` and `C₂`; that derivation is `invSum_eq_partialAdd_coneLift`. -/
def invSum (C₁ C₂ : Set (Rn n)) : Set (Rn n) :=
  ⋃ l ∈ Set.Icc (0 : ℝ) 1, ((1 - l) • C₁ ∩ l • C₂)

/-- Membership in `C₁ # C₂`, with the union over `λ ∈ [0, 1]` unpacked. -/
theorem mem_invSum {C₁ C₂ : Set (Rn n)} {x : Rn n} :
    x ∈ invSum C₁ C₂ ↔ ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ x ∈ (1 - l) • C₁ ∧ x ∈ l • C₂ := by
  simp only [invSum, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc, exists_prop, and_assoc]

/-- **Rockafellar, §3 (p. 21).** `C₁ # C₂` consists of all the vectors `x` which can be expressed
in the form `x = (1 - λ) x₁ = λ x₂` with `0 ≤ λ ≤ 1`, `x₁ ∈ C₁` and `x₂ ∈ C₂`. -/
theorem mem_invSum_iff_exists {C₁ C₂ : Set (Rn n)} {x : Rn n} :
    x ∈ invSum C₁ C₂ ↔ ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ ∃ x₁ ∈ C₁, ∃ x₂ ∈ C₂,
      x = (1 - l) • x₁ ∧ x = l • x₂ := by
  rw [mem_invSum]
  constructor
  · rintro ⟨l, hl₀, hl₁, ⟨x₁, hx₁, hex₁⟩, ⟨x₂, hx₂, hex₂⟩⟩
    exact ⟨l, hl₀, hl₁, x₁, hx₁, x₂, hx₂, hex₁.symm, hex₂.symm⟩
  · rintro ⟨l, hl₀, hl₁, x₁, hx₁, x₂, hx₂, he₁, he₂⟩
    exact ⟨l, hl₀, hl₁, ⟨x₁, hx₁, he₁.symm⟩, ⟨x₂, hx₂, he₂.symm⟩⟩

/-- Inverse addition is monotone in both arguments. -/
theorem invSum_mono {C₁ C₂ D₁ D₂ : Set (Rn n)} (h₁ : C₁ ⊆ D₁) (h₂ : C₂ ⊆ D₂) :
    invSum C₁ C₂ ⊆ invSum D₁ D₂ := by
  intro x hx
  obtain ⟨l, hl₀, hl₁, hxa, hxb⟩ := mem_invSum.1 hx
  exact mem_invSum.2 ⟨l, hl₀, hl₁, Set.smul_set_mono h₁ hxa, Set.smul_set_mono h₂ hxb⟩

/-- Inverse addition is pointwise, `C₁ # C₂ = {x₁ # x₂ | x₁ ∈ C₁, x₂ ∈ C₂}`, in parallel with the
formula for `C₁ + C₂`; `{x₁} # {x₂}` is non-empty exactly when `x₁` and `x₂` lie on a common ray
through the origin. -/
theorem invSum_eq_iUnion_singleton (C₁ C₂ : Set (Rn n)) :
    invSum C₁ C₂ = ⋃ x₁ ∈ C₁, ⋃ x₂ ∈ C₂, invSum {x₁} {x₂} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨l, hl₀, hl₁, x₁, hx₁, x₂, hx₂, he₁, he₂⟩ := mem_invSum_iff_exists.1 hx
    refine Set.mem_biUnion hx₁ (Set.mem_biUnion hx₂ ?_)
    exact mem_invSum_iff_exists.2 ⟨l, hl₀, hl₁, x₁, rfl, x₂, rfl, he₁, he₂⟩
  · refine Set.iUnion₂_subset fun x₁ hx₁ => Set.iUnion₂_subset fun x₂ hx₂ => ?_
    exact invSum_mono (Set.singleton_subset_iff.2 hx₁) (Set.singleton_subset_iff.2 hx₂)

/-- The inverse sum of two vectors on a common ray: `{α₁ e} # {α₂ e} = {[α₁α₂/(α₁+α₂)] e}` for
`α₁, α₂ ≥ 0`. The coefficient is stated as a product, not as the book's harmonic `(α₁⁻¹+α₂⁻¹)⁻¹`:
since `0⁻¹ = 0` in Lean the harmonic form evaluates to `α₂` at `α₁ = 0`, which is wrong, whereas
the product form is correct throughout (`0 / 0 = 0`). -/
theorem invSum_singleton_smul (e : Rn n) {a₁ a₂ : ℝ} (h₁ : 0 ≤ a₁) (h₂ : 0 ≤ a₂) :
    invSum ({a₁ • e} : Set (Rn n)) {a₂ • e} = {(a₁ * a₂ / (a₁ + a₂)) • e} := by
  have key : ∀ l : ℝ, (1 - l) • ({a₁ • e} : Set (Rn n)) = {((1 - l) * a₁) • e} := by
    intro l; rw [Set.smul_set_singleton, smul_smul]
  have key2 : ∀ l : ℝ, l • ({a₂ • e} : Set (Rn n)) = {(l * a₂) • e} := by
    intro l; rw [Set.smul_set_singleton, smul_smul]
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨l, hl₀, hl₁, hxa, hxb⟩ := mem_invSum.1 hx
    rw [key l, Set.mem_singleton_iff] at hxa
    rw [key2 l, Set.mem_singleton_iff] at hxb
    rw [Set.mem_singleton_iff, hxa]
    rcases eq_or_ne e 0 with rfl | he
    · simp
    · have heq : (1 - l) * a₁ = l * a₂ := smul_left_injective ℝ he (hxa.symm.trans hxb)
      congr 1
      rcases eq_or_lt_of_le (add_nonneg h₁ h₂) with hz | hz
      · have ha₁ : a₁ = 0 := by linarith
        have ha₂ : a₂ = 0 := by linarith
        simp [ha₁, ha₂]
      · rw [eq_div_iff (ne_of_gt hz)]
        linear_combination a₁ * heq
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rcases eq_or_lt_of_le (add_nonneg h₁ h₂) with hz | hz
    · have ha₁ : a₁ = 0 := by linarith
      have ha₂ : a₂ = 0 := by linarith
      refine mem_invSum.2 ⟨0, le_rfl, zero_le_one, ?_, ?_⟩
      · rw [key 0, Set.mem_singleton_iff, ha₁, ha₂]; simp
      · rw [key2 0, Set.mem_singleton_iff, ha₁, ha₂]; simp
    · refine mem_invSum.2 ⟨a₁ / (a₁ + a₂), div_nonneg h₁ hz.le,
        (div_le_one hz).2 (by linarith), ?_, ?_⟩
      · rw [key, Set.mem_singleton_iff]
        congr 1
        field_simp
        ring
      · rw [key2, Set.mem_singleton_iff]
        congr 1
        field_simp

/-- **Theorem 3.7.** The inverse sum `C₁ # C₂` of two convex sets is convex. -/
theorem theorem_3_7 {C₁ C₂ : Set (Rn n)} (h₁ : Convex ℝ C₁) (h₂ : Convex ℝ C₂) :
    Convex ℝ (invSum C₁ C₂) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨l, hl₀, hl₁, hxa, hxb⟩ := mem_invSum.1 hx
  obtain ⟨k, hk₀, hk₁, hya, hyb⟩ := mem_invSum.1 hy
  refine mem_invSum.2 ⟨a * l + b * k, by positivity, ?_, ?_, ?_⟩
  · nlinarith
  · have hsplit : 1 - (a * l + b * k) = a * (1 - l) + b * (1 - k) := by linear_combination -hab
    rw [hsplit, theorem_3_2 h₁ (by positivity) (by positivity)]
    refine Set.add_mem_add ?_ ?_
    · rw [mul_smul]; exact Set.smul_mem_smul_set hxa
    · rw [mul_smul]; exact Set.smul_mem_smul_set hya
  · rw [theorem_3_2 h₂ (by positivity) (by positivity)]
    refine Set.add_mem_add ?_ ?_
    · rw [mul_smul]; exact Set.smul_mem_smul_set hxb
    · rw [mul_smul]; exact Set.smul_mem_smul_set hyb

/-! ### The cone correspondence behind inverse addition -/

/-- **Rockafellar, §3 (p. 20).** The convex cone in `ℝⁿ⁺¹` associated with a convex set `C` in
`ℝⁿ`: the one generated by `{(x, 1) | x ∈ C}`, written here with the height in the *second*
coordinate so that partial addition in the height is `partialAdd`. -/
def coneLift (C : Set (Rn n)) : Set (Rn n × ℝ) := {q | 0 ≤ q.2 ∧ q.1 ∈ q.2 • C}

/-- Membership in `coneLift C`, at an explicit pair: `(x, λ)` is in the cone exactly when
`λ ≥ 0` and `x ∈ λ C`. -/
@[simp] theorem mem_coneLift {C : Set (Rn n)} {x : Rn n} {l : ℝ} :
    (x, l) ∈ coneLift C ↔ 0 ≤ l ∧ x ∈ l • C :=
  Iff.rfl

/-- `coneLift C` is exactly the union of the non-negative multiples of the cross-section
`{(x, 1) | x ∈ C}`, which is why it deserves the name "the cone generated by" that section. -/
theorem coneLift_eq_iUnion_smul (C : Set (Rn n)) :
    coneLift C = ⋃ l ∈ Set.Ici (0 : ℝ), l • ((fun x => (x, (1 : ℝ))) '' C) := by
  ext ⟨x, l⟩
  constructor
  · rintro ⟨hl, y, hy, hxy⟩
    have hl' : (0 : ℝ) ≤ l := hl
    have hxy' : l • y = x := hxy
    refine Set.mem_biUnion (Set.mem_Ici.2 hl') ⟨(y, (1 : ℝ)), ⟨y, hy, rfl⟩, ?_⟩
    change l • ((y, (1 : ℝ)) : Rn n × ℝ) = (x, l)
    rw [Prod.smul_mk, hxy', smul_eq_mul, mul_one]
  · intro hmem
    obtain ⟨k, hk, q, ⟨y, hy, rfl⟩, hqx⟩ := Set.mem_iUnion₂.1 hmem
    have h1 : k • y = x := congrArg Prod.fst hqx
    have h2 : k = l := by simpa using congrArg Prod.snd hqx
    subst h2
    exact ⟨Set.mem_Ici.1 hk, y, hy, h1⟩

/-- The cross-section of `coneLift C` at height `1` is `C` again: the correspondence `C ↦ K` of
the book is one-to-one. -/
@[simp] theorem coneLift_section_one (C : Set (Rn n)) :
    {x : Rn n | (x, (1 : ℝ)) ∈ coneLift C} = C := by
  ext x
  simp

/-- `coneLift C` contains the origin of `ℝⁿ⁺¹` whenever `C` is non-empty — the book's cones `K`
are exactly the ones "containing the origin". -/
theorem zero_mem_coneLift {C : Set (Rn n)} (hne : C.Nonempty) : (0 : Rn n × ℝ) ∈ coneLift C := by
  refine ⟨le_rfl, ?_⟩
  change (0 : Rn n) ∈ (0 : ℝ) • C
  rw [Set.zero_smul_set hne]
  exact Set.mem_zero.2 rfl

/-- `coneLift C` is closed under non-negative scaling. -/
theorem smul_mem_coneLift {C : Set (Rn n)} {q : Rn n × ℝ} (hq : q ∈ coneLift C) {c : ℝ}
    (hc : 0 ≤ c) : c • q ∈ coneLift C := by
  obtain ⟨hl, hx⟩ := hq
  refine ⟨mul_nonneg hc hl, ?_⟩
  have hmem : c • q.1 ∈ c • (q.2 • C) := Set.smul_mem_smul_set hx
  rw [← mul_smul] at hmem
  exact hmem

/-- `coneLift C` is a convex cone whenever `C` is convex. This, together with
`coneLift_eq_iUnion_smul`, is the "convex cone `K` in `ℝⁿ⁺¹` containing the origin and having a
cross-section identifiable with `C`" of the book. -/
theorem convex_coneLift {C : Set (Rn n)} (hC : Convex ℝ C) : Convex ℝ (coneLift C) := by
  rintro ⟨x, l⟩ ⟨hl, hx⟩ ⟨y, k⟩ ⟨hk, hy⟩ a b ha hb hab
  have hl' : (0 : ℝ) ≤ l := hl
  have hk' : (0 : ℝ) ≤ k := hk
  have hx' : x ∈ l • C := hx
  have hy' : y ∈ k • C := hy
  refine ⟨add_nonneg (mul_nonneg ha hl') (mul_nonneg hb hk'), ?_⟩
  have hsmul : a • x + b • y ∈ (a * l) • C + (b * k) • C := by
    refine Set.add_mem_add ?_ ?_
    · rw [mul_smul]; exact Set.smul_mem_smul_set hx'
    · rw [mul_smul]; exact Set.smul_mem_smul_set hy'
  rw [← theorem_3_2 hC (mul_nonneg ha hl') (mul_nonneg hb hk')] at hsmul
  exact hsmul

/-- The inverse sum is the partial addition "in the `λ` argument alone" of `coneLift C₁` and
`coneLift C₂`, read off at height `1`: the bridge between `invSum` and Theorem 3.6. -/
theorem invSum_eq_partialAdd_coneLift (C₁ C₂ : Set (Rn n)) :
    invSum C₁ C₂ = {x : Rn n | (x, (1 : ℝ)) ∈ partialAdd (coneLift C₁) (coneLift C₂)} := by
  ext x
  simp only [Set.mem_ofPred_eq, mem_partialAdd, mem_coneLift, mem_invSum]
  constructor
  · rintro ⟨l, hl₀, hl₁, hxa, hxb⟩
    exact ⟨1 - l, l, ⟨by linarith, hxa⟩, ⟨hl₀, hxb⟩, by ring⟩
  · rintro ⟨l₁, l₂, ⟨hl₁, hx₁⟩, ⟨hl₂, hx₂⟩, hsum⟩
    refine ⟨l₂, hl₂, by linarith, ?_, hx₂⟩
    rwa [show (1 : ℝ) - l₂ = l₁ by linarith]

/-! ### Theorem 3.8: cones -/

/-- A convex cone containing the origin is invariant under every positive scaling. -/
private theorem smul_eq_self_of_cone {K : Set (Rn n)} (hs : ∀ c : ℝ, 0 < c → c • K ⊆ K) {c : ℝ}
    (hc : 0 < c) : c • K = K := by
  refine Set.Subset.antisymm (hs c hc) ?_
  intro x hx
  refine ⟨c⁻¹ • x, hs c⁻¹ (by positivity) (Set.smul_mem_smul_set hx), ?_⟩
  change c • c⁻¹ • x = x
  rw [← mul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- **Theorem 3.8** (first equation). For convex cones `K₁`, `K₂` containing the origin,
`K₁ + K₂ = conv (K₁ ∪ K₂)`. -/
theorem theorem_3_8_add {K₁ K₂ : Set (Rn n)} (hc₁ : Convex ℝ K₁) (hc₂ : Convex ℝ K₂)
    (hs₁ : ∀ c : ℝ, 0 < c → c • K₁ ⊆ K₁) (hs₂ : ∀ c : ℝ, 0 < c → c • K₂ ⊆ K₂)
    (h0₁ : (0 : Rn n) ∈ K₁) (h0₂ : (0 : Rn n) ∈ K₂) :
    K₁ + K₂ = convexHull ℝ (K₁ ∪ K₂) := by
  have hsub₁ : K₁ ⊆ K₁ + K₂ := fun x hx => ⟨x, hx, 0, h0₂, by simp⟩
  have hsub₂ : K₂ ⊆ K₁ + K₂ := fun x hx => ⟨0, h0₁, x, hx, by simp⟩
  refine Set.Subset.antisymm ?_
    (convexHull_min (Set.union_subset hsub₁ hsub₂) (theorem_3_1 hc₁ hc₂))
  have hcone : (2 : ℝ) • convexHull ℝ (K₁ ∪ K₂) ⊆ convexHull ℝ (K₁ ∪ K₂) := by
    rw [← convexHull_smul]
    refine convexHull_mono ?_
    rw [Set.smul_set_union, smul_eq_self_of_cone hs₁ two_pos, smul_eq_self_of_cone hs₂ two_pos]
  rintro x ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  have hmid : (2 : ℝ)⁻¹ • x₁ + (2 : ℝ)⁻¹ • x₂ ∈ convexHull ℝ (K₁ ∪ K₂) :=
    convex_convexHull ℝ _ (subset_convexHull ℝ _ (Set.mem_union_left _ hx₁))
      (subset_convexHull ℝ _ (Set.mem_union_right _ hx₂)) (by norm_num) (by norm_num) (by norm_num)
  refine hcone ⟨_, hmid, ?_⟩
  change (2 : ℝ) • ((2 : ℝ)⁻¹ • x₁ + (2 : ℝ)⁻¹ • x₂) = x₁ + x₂
  rw [smul_add, ← mul_smul, ← mul_smul]
  norm_num

/-- **Theorem 3.8** (second equation). For cones `K₁`, `K₂` containing the origin,
`K₁ # K₂ = K₁ ∩ K₂`. Stated without the convexity the book carries over from the first equation:
closure under positive scaling and membership of the origin suffice. -/
theorem theorem_3_8_invSum {K₁ K₂ : Set (Rn n)} (hs₁ : ∀ c : ℝ, 0 < c → c • K₁ ⊆ K₁)
    (hs₂ : ∀ c : ℝ, 0 < c → c • K₂ ⊆ K₂) (h0₁ : (0 : Rn n) ∈ K₁) (h0₂ : (0 : Rn n) ∈ K₂) :
    invSum K₁ K₂ = K₁ ∩ K₂ := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨l, hl₀, hl₁, hxa, hxb⟩ := mem_invSum.1 hx
    rcases eq_or_lt_of_le hl₀ with hl | hl
    · rw [← hl, Set.zero_smul_set ⟨0, h0₂⟩, Set.mem_zero] at hxb
      rw [hxb]
      exact ⟨h0₁, h0₂⟩
    rcases eq_or_lt_of_le hl₁ with hl' | hl'
    · rw [hl', sub_self, Set.zero_smul_set ⟨0, h0₁⟩, Set.mem_zero] at hxa
      rw [hxa]
      exact ⟨h0₁, h0₂⟩
    · rw [smul_eq_self_of_cone hs₁ (by linarith)] at hxa
      rw [smul_eq_self_of_cone hs₂ hl] at hxb
      exact ⟨hxa, hxb⟩
  · intro x hx
    refine mem_invSum.2 ⟨1/2, by norm_num, by norm_num, ?_, ?_⟩
    · rw [show (1 : ℝ) - 1/2 = 1/2 by norm_num, smul_eq_self_of_cone hs₁ (by norm_num)]
      exact hx.1
    · rw [smul_eq_self_of_cone hs₂ (by norm_num)]
      exact hx.2

end Rockafellar
