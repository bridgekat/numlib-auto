/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.Convex.Homogeneous
import NumlibSurface.Rockafellar.Chapter01.Section01

/-!
# Rockafellar, Section 2: Convex sets and cones

This module formalizes Section 2 of [rockafellar1970convex]: convex sets, convex hulls and convex
combinations, the dimension of a convex set, cones, convex cones, and the smallest convex cone that
includes a set. A set $K \subseteq \mathbb{R}^n$ is a cone if $\lambda x \in K$ for all $x \in K$
and $\lambda > 0$; the origin may or may not belong to $K$. The dimension of a convex set $C$ is
`Rockafellar.dim` of Section 1, the dimension of the subspace parallel to $\operatorname{aff} C$.

All 13 numbered results of Section 2 are formalized. Most of them specialize the `Convex` and
`convexHull` API of Mathlib, and Theorem 2.6 is the backbone theorem
`ConvexAnalysis.convex_iff_add_mem_of_isCone`.

## Main definitions

* Definition of cone, `Rockafellar.IsCone`: a set closed under multiplication by positive scalars.
* Definition of positive linear combination, `Rockafellar.posCombinations`: the set of sums
  $\lambda_1 x_1 + \dots + \lambda_m x_m$ with $m \ge 1$, $\lambda_i > 0$ and $x_i \in S$.

## Main results

* Theorem 2.1, `Rockafellar.theorem_2_1`: the intersection of an arbitrary collection of convex sets
  is convex.
* Corollary 2.1.1, `Rockafellar.corollary_2_1_1`: the solution set of an arbitrary system of weak
  linear inequalities $\langle x, b_i \rangle \le \beta_i$ is convex.
* Theorem 2.2, `Rockafellar.theorem_2_2`: a set is convex if and only if it contains all convex
  combinations of its elements.
* Theorem 2.3, `Rockafellar.theorem_2_3`: $\operatorname{conv} S$ is the set of all convex
  combinations of elements of $S$.
* Corollary 2.3.1, `Rockafellar.corollary_2_3_1`: the convex hull of $\{b_0, \dots, b_m\}$ is the
  set of $\lambda_0 b_0 + \dots + \lambda_m b_m$ with $\lambda_i \ge 0$ and $\sum_i \lambda_i = 1$.
* Theorem 2.4, `Rockafellar.theorem_2_4`: the dimension of a non-empty convex set is the largest
  dimension of a simplex included in it.
* Theorem 2.5, `Rockafellar.theorem_2_5`: the intersection of an arbitrary collection of convex
  cones is a convex cone.
* Corollary 2.5.1, `Rockafellar.corollary_2_5_1`: the solution set of a homogeneous system of weak
  linear inequalities is a convex cone.
* Theorem 2.6, `Rockafellar.theorem_2_6`: a set is a convex cone if and only if it is closed under
  addition and multiplication by positive scalars.
* Corollary 2.6.1, `Rockafellar.corollary_2_6_1`: a set is a convex cone if and only if it contains
  all positive linear combinations of its elements.
* Corollary 2.6.2, `Rockafellar.corollary_2_6_2`: the positive linear combinations of $S$ form the
  smallest convex cone that includes $S$.
* Corollary 2.6.3, `Rockafellar.corollary_2_6_3`: for a convex set $C$, the set
  $\{\lambda x \mid \lambda > 0, x \in C\}$ is the smallest convex cone that includes $C$.
* Theorem 2.7, `Rockafellar.theorem_2_7_least`, `Rockafellar.theorem_2_7_sub`,
  `Rockafellar.theorem_2_7_aff`, `Rockafellar.theorem_2_7_greatest`: for a convex cone $K$ that
  contains $0$, the smallest subspace that contains $K$ is $K - K = \operatorname{aff} K$, and the
  largest subspace contained in $K$ is $(-K) \cap K$.

## Implementation notes

* `Rockafellar.IsCone` is not the Mathlib `PointedCone`, which contains $0$ by definition, because
  the cones of Corollaries 2.6.2 and 2.6.3 need not contain the origin. It is definitionally the
  backbone predicate `ConvexAnalysis.IsCone`. `Rockafellar.isCone_iff_smul_set_eq` gives the set
  form $\lambda K = K$ for all $\lambda > 0$, and `Rockafellar.toPointedCone` turns a convex cone
  that contains $0$, the setting of Theorem 2.7, into a `PointedCone`.
* A convex cone is the conjunction `Rockafellar.IsCone K ∧ Convex ℝ K`.
* The book states Theorem 2.7 in one sentence that asserts four facts. Each fact is a separate
  declaration.

## Deviations from the source

* **Theorem 2.4** (correction). The book states the theorem for every convex set $C$. For
  $C = \emptyset$ no simplex is included in $C$, and the maximum does not exist. The statement
  assumes that $C$ is non-empty. See `Rockafellar.theorem_2_4`.
-/

namespace Rockafellar

open ConvexAnalysis

open scoped Pointwise

variable {n : ℕ}

/-! ### Cones -/

/-- **Section 2** of [rockafellar1970convex], definition of cone. A set $K \subseteq \mathbb{R}^n$
is a **cone** if $\lambda x \in K$ for all $x \in K$ and all $\lambda > 0$.

The origin may or may not belong to a cone. So this is not the Mathlib `PointedCone`, which
contains $0$ by definition: Corollaries 2.6.2 and 2.6.3 give cones that need not contain the
origin. -/
def IsCone (K : Set (Rn n)) : Prop :=
  ∀ l : ℝ, 0 < l → ∀ x ∈ K, l • x ∈ K

/-- A set $K \subseteq \mathbb{R}^n$ is a cone if and only if $\lambda K = K$ for every
$\lambda > 0$.

Theorem 31.4 and `ConvexAnalysis.posHomogeneous_iff_isCone_epi` use this set form. The proof is
`ConvexAnalysis.isCone_iff_smul_eq`: `Rockafellar.IsCone` is definitionally the backbone
predicate `ConvexAnalysis.IsCone`, and the surface proofs use it in that form. -/
theorem isCone_iff_smul_set_eq (K : Set (Rn n)) : IsCone K ↔ ∀ a : ℝ, 0 < a → a • K = K :=
  ConvexAnalysis.isCone_iff_smul_eq

/-! ### Intersections: Theorems 2.1 and 2.5 -/

/-- **Theorem 2.1** of [rockafellar1970convex]. The intersection of an arbitrary collection
$\mathcal{C}$ of convex subsets of $\mathbb{R}^n$ is convex. -/
theorem theorem_2_1 (𝒞 : Set (Set (Rn n))) (h : ∀ C ∈ 𝒞, Convex ℝ C) : Convex ℝ (⋂₀ 𝒞) :=
  convex_sInter h

/-- **Corollary 2.1.1** of [rockafellar1970convex]. Let $b_i \in \mathbb{R}^n$ and
$\beta_i \in \mathbb{R}$ for $i$ in an arbitrary index set $I$. Then the solution set
$$\{x \in \mathbb{R}^n \mid \langle x, b_i \rangle \le \beta_i \text{ for all } i \in I\}$$
of the system of weak linear inequalities is convex. -/
theorem corollary_2_1_1 {ι : Type*} (b : ι → Rn n) (β : ι → ℝ) :
    Convex ℝ {x : Rn n | ∀ i, pairing n x (b i) ≤ β i} := by
  have hset : {x : Rn n | ∀ i, pairing n x (b i) ≤ β i}
      = ⋂₀ (Set.range fun i => {x : Rn n | pairing n x (b i) ≤ β i}) := by
    ext x
    simp
  rw [hset]
  refine theorem_2_1 _ ?_
  rintro _ ⟨i, rfl⟩
  exact convex_halfSpace_le (LinearMap.isLinear ((pairing n).flip (b i))) (β i)

/-- **Theorem 2.5** of [rockafellar1970convex]. The intersection of an arbitrary collection
$\mathcal{K}$ of convex cones in $\mathbb{R}^n$ is a convex cone. -/
theorem theorem_2_5 (𝒦 : Set (Set (Rn n))) (h : ∀ K ∈ 𝒦, IsCone K ∧ Convex ℝ K) :
    IsCone (⋂₀ 𝒦) ∧ Convex ℝ (⋂₀ 𝒦) :=
  ⟨fun l hl x hx K hK => (h K hK).1 l hl x (hx K hK), convex_sInter fun K hK => (h K hK).2⟩

/-- **Corollary 2.5.1** of [rockafellar1970convex]. Let $b_i \in \mathbb{R}^n$ for $i$ in an
arbitrary index set $I$. Then the solution set
$$\{x \in \mathbb{R}^n \mid \langle x, b_i \rangle \le 0 \text{ for all } i \in I\}$$
of the homogeneous system of weak linear inequalities is a convex cone. -/
theorem corollary_2_5_1 {ι : Type*} (b : ι → Rn n) :
    IsCone {x : Rn n | ∀ i, pairing n x (b i) ≤ 0} ∧
      Convex ℝ {x : Rn n | ∀ i, pairing n x (b i) ≤ 0} := by
  constructor
  · intro l hl x hx i
    have h := hx i
    have hlin : pairing n (l • x) (b i) = l * pairing n x (b i) := by
      simp
    rw [hlin]
    exact mul_nonpos_of_nonneg_of_nonpos hl.le h
  · exact corollary_2_1_1 b (fun _ => 0)

/-! ### Convex combinations: Theorems 2.2, 2.3 and 2.4 -/

/-- **Theorem 2.2** of [rockafellar1970convex]. A subset $C$ of $\mathbb{R}^n$ is convex if and only
if it contains all the convex combinations of its elements: for all $k \in \mathbb{N}$, all
$\lambda_1, \dots, \lambda_k \ge 0$ with $\lambda_1 + \dots + \lambda_k = 1$ and all
$x_1, \dots, x_k \in C$, the point $\lambda_1 x_1 + \dots + \lambda_k x_k$ belongs to $C$. -/
theorem theorem_2_2 (C : Set (Rn n)) :
    Convex ℝ C ↔ ∀ (k : ℕ) (l : Fin k → ℝ) (x : Fin k → Rn n), (∀ i, 0 ≤ l i) →
      ∑ i, l i = 1 → (∀ i, x i ∈ C) → ∑ i, l i • x i ∈ C := by
  constructor
  · intro hC k l x hl hsum hx
    exact hC.sum_mem (fun i _ => hl i) hsum fun i _ => hx i
  · intro h x hx y hy a c ha hc hac
    have hmem := h 2 ![a, c] ![x, y] (by intro i; fin_cases i <;> simpa)
      (by simp [Fin.sum_univ_two, hac]) (by intro i; fin_cases i <;> simpa)
    simpa [Fin.sum_univ_two] using hmem

/-- **Theorem 2.3** of [rockafellar1970convex]. For any $S \subseteq \mathbb{R}^n$,
$\operatorname{conv} S$ consists of all the convex combinations of elements of $S$:
$$\operatorname{conv} S = \Bigl\{\sum_{i=1}^{k} \lambda_i x_i \Bigm| k \in \mathbb{N},\
  \lambda_i \ge 0,\ \sum_{i=1}^{k} \lambda_i = 1,\ x_i \in S\Bigr\}.$$

The combinations are indexed by `Fin k`, so that the statement reads as the book's
$\lambda_1 x_1 + \dots + \lambda_m x_m$. -/
theorem theorem_2_3 (S : Set (Rn n)) :
    convexHull ℝ S = {z : Rn n | ∃ (k : ℕ) (l : Fin k → ℝ) (x : Fin k → Rn n),
      (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1 ∧ (∀ i, x i ∈ S) ∧ ∑ i, l i • x i = z} := by
  ext z
  constructor
  · intro hz
    obtain ⟨ι, _, w, y, hw₀, hw₁, hy, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hz
    refine ⟨Fintype.card ι, fun i => w ((Fintype.equivFin ι).symm i),
      fun i => y ((Fintype.equivFin ι).symm i), fun i => hw₀ _, ?_, fun i => hy _, ?_⟩
    · rw [Equiv.sum_comp (Fintype.equivFin ι).symm w]
      exact hw₁
    · rw [Equiv.sum_comp (Fintype.equivFin ι).symm fun j => w j • y j]
      exact hsum
  · rintro ⟨k, l, x, hl, hsum, hx, rfl⟩
    exact mem_convexHull_of_exists_fintype l x hl hsum hx rfl

/-- **Corollary 2.3.1** of [rockafellar1970convex]. The convex hull of a finite set
$\{b_0, \dots, b_m\} \subseteq \mathbb{R}^n$ consists of the vectors
$\lambda_0 b_0 + \dots + \lambda_m b_m$ with $\lambda_i \ge 0$ for all $i$ and
$\lambda_0 + \dots + \lambda_m = 1$.

The points are a family `b : Fin (k + 1) → Rn n`, so the number $m$ is `k`. -/
theorem corollary_2_3_1 {k : ℕ} (b : Fin (k + 1) → Rn n) :
    convexHull ℝ (Set.range b) = {z : Rn n | ∃ l : Fin (k + 1) → ℝ,
      (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1 ∧ ∑ i, l i • b i = z} := by
  classical
  ext z
  constructor
  · intro hz
    rw [convexHull_range_eq_exists_affineCombination] at hz
    obtain ⟨s, w, hw₀, hw₁, hcomb⟩ := hz
    refine ⟨fun i => if i ∈ s then w i else 0, fun i => ?_, ?_, ?_⟩
    · by_cases hi : i ∈ s
      · simpa [hi] using hw₀ i hi
      · simp [hi]
    · rw [Finset.sum_ite_mem, Finset.univ_inter]
      exact hw₁
    · have hsmul : ∀ i : Fin (k + 1), (if i ∈ s then w i else 0) • b i
          = if i ∈ s then w i • b i else 0 := by
        intro i
        by_cases hi : i ∈ s <;> simp [hi]
      rw [Finset.sum_congr rfl fun i _ => hsmul i, Finset.sum_ite_mem, Finset.univ_inter,
        ← Finset.affineCombination_eq_linear_combination s b w hw₁]
      exact hcomb
  · rintro ⟨l, hl, hsum, rfl⟩
    exact mem_convexHull_of_exists_fintype l b hl hsum (fun i => Set.mem_range_self i) rfl

/-- **Theorem 2.4** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be a non-empty convex
set. Then the dimension of $C$ is the maximum of the dimensions of the simplices included in
$C$: $\dim C$ is the greatest element of the set of the numbers $\dim (\operatorname{conv} b)$,
where $b$ ranges over the affinely independent sets with $\operatorname{conv} b \subseteq C$.

**Correction.** The book does not exclude $C = \emptyset$. For $C = \emptyset$ there is no
simplex in $C$, and the maximum does not exist. The statement assumes that $C$ is non-empty.

A simplex is the convex hull of an affinely independent set $b$. In $\mathbb{R}^n$ such a set is
finite, so the statement has no finiteness hypothesis. The dimension is `Rockafellar.dim`. -/
theorem theorem_2_4 {C : Set (Rn n)} (hC : Convex ℝ C) (hne : C.Nonempty) :
    IsGreatest {d : ℤ | ∃ b : Set (Rn n), AffineIndependent ℝ ((↑) : b → Rn n) ∧
      convexHull ℝ b ⊆ C ∧ d = dim (convexHull ℝ b)} (dim C) := by
  constructor
  · obtain ⟨t, hts, hspan, hai⟩ := exists_affineIndependent ℝ (Rn n) C
    have htne : t.Nonempty := by
      rcases Set.eq_empty_or_nonempty t with rfl | h
      · exfalso
        obtain ⟨a, ha⟩ := hne
        have hmem : a ∈ affineSpan ℝ (∅ : Set (Rn n)) := by
          rw [hspan]
          exact subset_affineSpan ℝ C ha
        rw [AffineSubspace.span_empty] at hmem
        exact hmem
      · exact h
    have hhullne : (convexHull ℝ t).Nonempty := htne.mono (subset_convexHull ℝ t)
    have hvs : vectorSpan ℝ (convexHull ℝ t) = vectorSpan ℝ C := by
      rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull, hspan]
    refine ⟨t, hai, convexHull_min hts hC, ?_⟩
    rw [dim_of_nonempty hhullne, dim_of_nonempty hne, hvs]
  · rintro d ⟨b, -, hbC, rfl⟩
    rcases Set.eq_empty_or_nonempty (convexHull ℝ b) with h | h
    · rw [h, dim_empty, dim_of_nonempty hne]
      omega
    · exact dim_le_dim_of_subset h hbC

/-! ### Convex cones: Theorems 2.6 and 2.7 -/

/-- **Theorem 2.6** of [rockafellar1970convex]. A subset $K$ of $\mathbb{R}^n$ is a convex cone if
and only if it is closed under addition and positive scalar multiplication: $x + y \in K$ for
all $x, y \in K$, and $\lambda x \in K$ for all $x \in K$ and $\lambda > 0$. -/
theorem theorem_2_6 (K : Set (Rn n)) :
    (IsCone K ∧ Convex ℝ K) ↔
      (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧ ∀ l : ℝ, 0 < l → ∀ x ∈ K, l • x ∈ K := by
  constructor
  · rintro ⟨hK, hconv⟩
    exact ⟨(convex_iff_add_mem_of_isCone hK).1 hconv, hK⟩
  · rintro ⟨hadd, hsmul⟩
    exact ⟨hsmul, (convex_iff_add_mem_of_isCone hsmul).2 hadd⟩

/-- **Section 2** of [rockafellar1970convex], definition of positive linear combination. The
**positive linear combinations** of a set $S \subseteq \mathbb{R}^n$ are the vectors
$\lambda_1 x_1 + \dots + \lambda_m x_m$ with $m \ge 1$, $\lambda_i > 0$ and $x_i \in S$ for all
$i$.

The terms are indexed by an arbitrary non-empty finite type instead of `Fin m`. Then the
concatenation of two combinations in Corollary 2.6.2 is indexed by a sum type. -/
def posCombinations (S : Set (Rn n)) : Set (Rn n) :=
  {z | ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (l : ι → ℝ) (x : ι → Rn n),
    (∀ i, 0 < l i) ∧ (∀ i, x i ∈ S) ∧ ∑ i, l i • x i = z}

/-- If $S \subseteq T \subseteq \mathbb{R}^n$, then every positive linear combination of elements of
$S$ is a positive linear combination of elements of $T$. -/
theorem posCombinations_mono {S T : Set (Rn n)} (h : S ⊆ T) :
    posCombinations S ⊆ posCombinations T := by
  rintro z ⟨ι, hf, hne, l, x, hl, hx, rfl⟩
  exact ⟨ι, hf, hne, l, x, hl, fun i => h (hx i), rfl⟩

/-- Every element of $S \subseteq \mathbb{R}^n$ is a positive linear combination of elements of $S$,
with one term. -/
theorem subset_posCombinations (S : Set (Rn n)) : S ⊆ posCombinations S := fun z hz =>
  ⟨PUnit, inferInstance, inferInstance, fun _ => 1, fun _ => z, fun _ => one_pos, fun _ => hz,
    by simp⟩

/-- **Corollary 2.6.1** of [rockafellar1970convex]. A subset $K$ of $\mathbb{R}^n$ is a convex cone
if and only if it contains all the positive linear combinations of its elements. -/
theorem corollary_2_6_1 (K : Set (Rn n)) :
    (IsCone K ∧ Convex ℝ K) ↔ posCombinations K ⊆ K := by
  constructor
  · rintro ⟨hK, hconv⟩
    have hadd := ((theorem_2_6 K).1 ⟨hK, hconv⟩).1
    rintro z ⟨ι, hf, hne, l, x, hl, hx, rfl⟩
    have key : ∀ s : Finset ι, s.Nonempty → ∑ i ∈ s, l i • x i ∈ K := by
      intro s hs
      induction hs using Finset.Nonempty.cons_induction with
      | singleton a => simpa using hK (l a) (hl a) (x a) (hx a)
      | cons a s ha hs ih =>
          rw [Finset.sum_cons]
          exact hadd _ (hK (l a) (hl a) (x a) (hx a)) _ ih
    obtain ⟨i₀⟩ := hne
    exact key Finset.univ ⟨i₀, Finset.mem_univ i₀⟩
  · intro h
    have hcone : IsCone K := fun l hl x hx =>
      h ⟨PUnit, inferInstance, inferInstance, fun _ => l, fun _ => x, fun _ => hl, fun _ => hx,
        by simp⟩
    refine ⟨hcone, ((theorem_2_6 K).2 ⟨?_, hcone⟩).2⟩
    intro x hx y hy
    refine h ⟨Fin 2, inferInstance, inferInstance, fun _ => 1, ![x, y], fun _ => one_pos, ?_, ?_⟩
    · intro i
      fin_cases i <;> simpa
    · simp [Fin.sum_univ_two]

/-- **Corollary 2.6.2** of [rockafellar1970convex]. Let $S \subseteq \mathbb{R}^n$. The set $K$ of
all positive linear combinations of elements of $S$ is the smallest convex cone which includes
$S$.

The cone $K$ need not contain the origin. The book's convex cone $\operatorname{cone} S$
generated by $S$ is $K$ with the origin adjoined. -/
theorem corollary_2_6_2 (S : Set (Rn n)) :
    IsLeast {K : Set (Rn n) | IsCone K ∧ Convex ℝ K ∧ S ⊆ K} (posCombinations S) := by
  have hcone : IsCone (posCombinations S) := by
    rintro a ha z ⟨ι, hf, hne, l, x, hl, hx, rfl⟩
    refine ⟨ι, hf, hne, fun i => a * l i, x, fun i => mul_pos ha (hl i), hx, ?_⟩
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  have hadd : ∀ z ∈ posCombinations S, ∀ w ∈ posCombinations S, z + w ∈ posCombinations S := by
    rintro _ ⟨ι₁, hf₁, hne₁, l₁, x₁, hl₁, hx₁, rfl⟩ _ ⟨ι₂, hf₂, hne₂, l₂, x₂, hl₂, hx₂, rfl⟩
    refine ⟨ι₁ ⊕ ι₂, inferInstance, inferInstance, Sum.elim l₁ l₂, Sum.elim x₁ x₂, ?_, ?_, ?_⟩
    · rintro (i | i) <;> simp [hl₁, hl₂]
    · rintro (i | i) <;> simp [hx₁, hx₂]
    · rw [Fintype.sum_sum_type]
      simp
  refine ⟨⟨hcone, ((theorem_2_6 _).2 ⟨hadd, hcone⟩).2, subset_posCombinations S⟩, ?_⟩
  rintro K ⟨hK, hKconv, hSK⟩
  exact (posCombinations_mono hSK).trans ((corollary_2_6_1 K).1 ⟨hK, hKconv⟩)

/-- **Corollary 2.6.3** of [rockafellar1970convex]. Let $C \subseteq \mathbb{R}^n$ be convex. Then
the set
$$K = \{\lambda x \mid \lambda > 0,\ x \in C\}$$
is the smallest convex cone which includes $C$. -/
theorem corollary_2_6_3 {C : Set (Rn n)} (hC : Convex ℝ C) :
    IsLeast {K : Set (Rn n) | IsCone K ∧ Convex ℝ K ∧ C ⊆ K}
      {z : Rn n | ∃ l : ℝ, 0 < l ∧ ∃ x ∈ C, l • x = z} := by
  have hcone : IsCone {z : Rn n | ∃ l : ℝ, 0 < l ∧ ∃ x ∈ C, l • x = z} := by
    rintro a ha z ⟨l, hl, x, hx, rfl⟩
    exact ⟨a * l, mul_pos ha hl, x, hx, by rw [mul_smul]⟩
  have hadd : ∀ z ∈ {z : Rn n | ∃ l : ℝ, 0 < l ∧ ∃ x ∈ C, l • x = z},
      ∀ w ∈ {z : Rn n | ∃ l : ℝ, 0 < l ∧ ∃ x ∈ C, l • x = z},
      z + w ∈ {z : Rn n | ∃ l : ℝ, 0 < l ∧ ∃ x ∈ C, l • x = z} := by
    rintro _ ⟨l₁, hl₁, x₁, hx₁, rfl⟩ _ ⟨l₂, hl₂, x₂, hx₂, rfl⟩
    have hs : (0 : ℝ) < l₁ + l₂ := by linarith
    refine ⟨l₁ + l₂, hs, (l₁ / (l₁ + l₂)) • x₁ + (l₂ / (l₁ + l₂)) • x₂,
      hC hx₁ hx₂ (by positivity) (by positivity) (by field_simp), ?_⟩
    rw [smul_add, smul_smul, smul_smul, show (l₁ + l₂) * (l₁ / (l₁ + l₂)) = l₁ by field_simp,
      show (l₁ + l₂) * (l₂ / (l₁ + l₂)) = l₂ by field_simp]
  refine ⟨⟨hcone, ((theorem_2_6 _).2 ⟨hadd, hcone⟩).2,
    fun x hx => ⟨1, one_pos, x, hx, one_smul _ x⟩⟩, ?_⟩
  rintro K ⟨hK, -, hCK⟩ _ ⟨l, hl, x, hx, rfl⟩
  exact hK l hl x (hCK hx)

/-- The Mathlib `PointedCone` of $\mathbb{R}^n$ whose underlying set is a convex cone $K$ that
contains $0$. A cone in the sense of [rockafellar1970convex] that is convex and contains $0$ is
exactly a `PointedCone`, and Theorem 2.7 uses this bridge. -/
def toPointedCone {K : Set (Rn n)} (hK : IsCone K) (hconv : Convex ℝ K) (h0 : (0 : Rn n) ∈ K) :
    PointedCone ℝ (Rn n) where
  carrier := K
  zero_mem' := h0
  add_mem' {x y} hx hy := ((theorem_2_6 K).1 ⟨hK, hconv⟩).1 x hx y hy
  smul_mem' c x hx := by
    have hc : ((c : ℝ)) • x ∈ K := by
      rcases eq_or_lt_of_le c.2 with hc0 | hc0
      · rw [← hc0, zero_smul]
        exact h0
      · exact hK _ hc0 x hx
    exact hc

/-- The underlying set of `Rockafellar.toPointedCone` is the convex cone it comes from. -/
@[simp] theorem coe_toPointedCone {K : Set (Rn n)} (hK : IsCone K) (hconv : Convex ℝ K)
    (h0 : (0 : Rn n) ∈ K) : (toPointedCone hK hconv h0 : Set (Rn n)) = K := rfl

/-- **Theorem 2.7** of [rockafellar1970convex], the largest subspace. Let $K \subseteq \mathbb{R}^n$
be a convex cone that contains $0$. Then $(-K) \cap K$ is a subspace, and it is the largest
subspace contained in $K$. -/
theorem theorem_2_7_greatest {K : Set (Rn n)} (hK : IsCone K) (hconv : Convex ℝ K)
    (h0 : (0 : Rn n) ∈ K) :
    ∃ L : Submodule ℝ (Rn n), (L : Set (Rn n)) = (-K) ∩ K ∧
      IsGreatest {L' : Submodule ℝ (Rn n) | (L' : Set (Rn n)) ⊆ K} L := by
  refine ⟨(toPointedCone hK hconv h0).lineal, ?_, ?_, ?_⟩
  · ext z
    rw [SetLike.mem_coe, PointedCone.mem_lineal]
    simp only [Set.mem_inter_iff, Set.mem_neg]
    exact and_comm
  · intro z hz
    exact (PointedCone.mem_lineal.1 hz).1
  · intro L' hL' z hz
    exact PointedCone.mem_lineal.2 ⟨hL' hz, hL' (L'.neg_mem hz)⟩

/-- **Theorem 2.7** of [rockafellar1970convex], the smallest subspace. For every
$K \subseteq \mathbb{R}^n$, the linear span of $K$ is the smallest subspace that contains $K$.

This part needs no hypothesis on $K$. -/
theorem theorem_2_7_least (K : Set (Rn n)) :
    IsLeast {L : Submodule ℝ (Rn n) | K ⊆ (L : Set (Rn n))} (Submodule.span ℝ K) :=
  ⟨Submodule.subset_span, fun _ hL => Submodule.span_le.2 hL⟩

/-- **Theorem 2.7** of [rockafellar1970convex], the smallest subspace as a difference set. Let
$K \subseteq \mathbb{R}^n$ be a convex cone that contains $0$. Then the linear span of $K$,
which is the smallest subspace that contains $K$ by `Rockafellar.theorem_2_7_least`, is $K - K$. -/
theorem theorem_2_7_sub {K : Set (Rn n)} (hK : IsCone K) (hconv : Convex ℝ K)
    (h0 : (0 : Rn n) ∈ K) : (Submodule.span ℝ K : Set (Rn n)) = K - K :=
  span_eq_sub_of_isCone hK hconv h0

/-- **Theorem 2.7** of [rockafellar1970convex], the smallest subspace as an affine hull. Let
$K \subseteq \mathbb{R}^n$ contain $0$. Then the linear span of $K$ is $\operatorname{aff} K$.

This is the last sentence of the book's proof: the affine hull of a set that contains $0$ is a
subspace, by Theorem 1.1. Only the hypothesis $0 \in K$ is needed. -/
theorem theorem_2_7_aff {K : Set (Rn n)} (h0 : (0 : Rn n) ∈ K) :
    (Submodule.span ℝ K : Set (Rn n)) = (affineSpan ℝ K : Set (Rn n)) :=
  (coe_affineSpan_of_zero_mem h0).symm

end Rockafellar
