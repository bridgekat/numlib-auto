import Numlib.Analysis.Convex.Homogeneous
import NumlibSurface.Rockafellar.Chapter01.Section01

/-!
# Rockafellar §2: convex sets and cones

Surface file for R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, 1970, §2:
convex sets, convex hulls and convex combinations; the dimension of a convex set; cones, convex
cones and the smallest convex cone including a set.

All 13 numbered results of §2 are formalized. The section is thin: eight of them are one-line
specialisations of Mathlib's `Convex`/`convexHull` API, and Theorem 2.6 is the backbone's
`convex_iff_add_mem_of_isCone` verbatim.

The dimension of a convex set is `dim` from §1: the dimension of the subspace parallel to `aff C`.

Theorem 2.7 is split into four declarations, because the book's single sentence asserts four
things.

## Main definitions

* `IsCone` — the book's *cone*: closed under **positive** scalar multiplication, with the origin
  free to belong or not. Deliberately not Mathlib's `PointedCone`, which contains `0` by
  definition; the cones produced by Corollaries 2.6.2 and 2.6.3 need not contain the origin.
  `isCone_iff_smul_set_eq` bridges to the backbone's `∀ a > 0, a • s = s`, and `toPointedCone`
  bridges to Mathlib when `0 ∈ K`, which is the hypothesis of Theorem 2.7.
* `posCombinations` — the *positive linear combinations* of a set, the object of Corollaries 2.6.1
  and 2.6.2.

## Main results

* `theorem_2_1`, `corollary_2_1_1` — an arbitrary intersection of convex sets is convex, so the
  solution set of any system of weak linear inequalities is convex.
* `theorem_2_2`, `theorem_2_3`, `corollary_2_3_1` — a set is convex exactly when it contains the
  convex combinations of its elements, and `conv S` is the set of those combinations.
* `theorem_2_4` — the dimension of a convex set is the largest dimension of a simplex inside it.
* `theorem_2_5`, `corollary_2_5_1` — the same as Theorem 2.1 for convex cones and homogeneous
  systems.
* `theorem_2_6`, `corollary_2_6_1` — a set is a convex cone exactly when it is closed under
  addition and positive scalar multiplication, equivalently under positive linear combinations.
* `corollary_2_6_2`, `corollary_2_6_3` — the smallest convex cone including a set: the positive
  linear combinations in general, and `{λx | λ > 0, x ∈ C}` for a convex `C`.
* `theorem_2_7_least`, `theorem_2_7_sub`, `theorem_2_7_aff`, `theorem_2_7_greatest` — for a convex
  cone `K` containing the origin, the smallest subspace containing it is `K - K = aff K` and the
  largest subspace contained in it is `(-K) ∩ K`.
-/

namespace Rockafellar

open ConvexAnalysis

open scoped Pointwise

variable {n : ℕ}

/-! ### Rockafellar's cones -/

/-- Rockafellar's **cone**: a subset of `ℝⁿ` closed under *positive* scalar multiplication, the
origin free to belong or not. Not Mathlib's `PointedCone`, which contains `0` by definition;
Corollaries 2.6.2 and 2.6.3 produce cones that need not contain the origin. -/
def IsCone (K : Set (Rn n)) : Prop :=
  ∀ l : ℝ, 0 < l → ∀ x ∈ K, l • x ∈ K

/-- `IsCone` in the backbone's spelling `∀ a > 0, a • s = s`, which is the hypothesis of
`smul_mem_iff_of_isCone` and `convex_iff_add_mem_of_isCone`. -/
theorem isCone_iff_smul_set_eq (K : Set (Rn n)) : IsCone K ↔ ∀ a : ℝ, 0 < a → a • K = K := by
  constructor
  · intro h a ha
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact h a ha x hx
    · intro x hx
      refine ⟨a⁻¹ • x, h a⁻¹ (by positivity) x hx, ?_⟩
      simp [smul_smul, mul_inv_cancel₀ ha.ne']
  · intro h l hl x hx
    rw [← h l hl]
    exact ⟨x, hx, rfl⟩

/-! ### Intersections: Theorems 2.1 and 2.5 -/

/-- **Theorem 2.1.** The intersection of an arbitrary collection of convex sets is convex. -/
theorem theorem_2_1 (𝒞 : Set (Set (Rn n))) (h : ∀ C ∈ 𝒞, Convex ℝ C) : Convex ℝ (⋂₀ 𝒞) :=
  convex_sInter h

/-- **Corollary 2.1.1.** The solution set `{x | ⟨x, bᵢ⟩ ≤ βᵢ for all i}` of an arbitrary system
of weak linear inequalities is convex. -/
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

/-- **Theorem 2.5.** The intersection of an arbitrary collection of convex cones is a convex
cone. -/
theorem theorem_2_5 (𝒦 : Set (Set (Rn n))) (h : ∀ K ∈ 𝒦, IsCone K ∧ Convex ℝ K) :
    IsCone (⋂₀ 𝒦) ∧ Convex ℝ (⋂₀ 𝒦) :=
  ⟨fun l hl x hx K hK => (h K hK).1 l hl x (hx K hK), convex_sInter fun K hK => (h K hK).2⟩

/-- **Corollary 2.5.1.** The solution set of a homogeneous system of weak linear inequalities is
a convex cone. -/
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

/-- **Theorem 2.2.** A subset of `ℝⁿ` is convex iff it contains all convex combinations of its
elements. -/
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

/-- **Theorem 2.3.** For any `S ⊆ ℝⁿ`, `conv S` consists of all convex combinations of elements
of `S`. Indexed by `Fin k`, so that the statement reads as the book's `λ₁x₁ + ⋯ + λ_m x_m`. -/
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

/-- **Corollary 2.3.1.** The convex hull of `{b₀, …, b_m}` is the set of `λ₀b₀ + ⋯ + λ_m b_m`
with `λᵢ ≥ 0` and `λ₀ + ⋯ + λ_m = 1`. -/
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

/-- **Theorem 2.4.** The dimension of a convex set `C` is the largest dimension of a simplex
included in `C`. A simplex is the convex hull of an affinely independent set, which in `ℝⁿ` is
automatically finite, so no finiteness hypothesis is carried. Needs `C` non-empty, which the book
does not say: for `C = ∅` there is no simplex at all, and the maximum does not exist. -/
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

/-- **Theorem 2.6.** A subset of `ℝⁿ` is a convex cone iff it is closed under addition and
positive scalar multiplication. -/
theorem theorem_2_6 (K : Set (Rn n)) :
    (IsCone K ∧ Convex ℝ K) ↔
      (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧ ∀ l : ℝ, 0 < l → ∀ x ∈ K, l • x ∈ K := by
  constructor
  · rintro ⟨hK, hconv⟩
    exact ⟨(convex_iff_add_mem_of_isCone ((isCone_iff_smul_set_eq K).1 hK)).1 hconv, hK⟩
  · rintro ⟨hadd, hsmul⟩
    exact ⟨hsmul, (convex_iff_add_mem_of_isCone ((isCone_iff_smul_set_eq K).1 hsmul)).2 hadd⟩

/-- Rockafellar's **positive linear combinations** of `S`: the sums `λ₁x₁ + ⋯ + λ_m x_m` with
`m ≥ 1`, every `λᵢ > 0` and every `xᵢ ∈ S`. The index is an arbitrary non-empty finite type rather
than `Fin (m+1)`, which makes the concatenation in Corollary 2.6.2 a `Sum`. -/
def posCombinations (S : Set (Rn n)) : Set (Rn n) :=
  {z | ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (l : ι → ℝ) (x : ι → Rn n),
    (∀ i, 0 < l i) ∧ (∀ i, x i ∈ S) ∧ ∑ i, l i • x i = z}

/-- Positive linear combinations are monotone in the set. -/
theorem posCombinations_mono {S T : Set (Rn n)} (h : S ⊆ T) :
    posCombinations S ⊆ posCombinations T := by
  rintro z ⟨ι, hf, hne, l, x, hl, hx, rfl⟩
  exact ⟨ι, hf, hne, l, x, hl, fun i => h (hx i), rfl⟩

/-- A one-term positive combination is the element itself. -/
theorem subset_posCombinations (S : Set (Rn n)) : S ⊆ posCombinations S := fun z hz =>
  ⟨PUnit, inferInstance, inferInstance, fun _ => 1, fun _ => z, fun _ => one_pos, fun _ => hz,
    by simp⟩

/-- **Corollary 2.6.1.** A subset of `ℝⁿ` is a convex cone iff it contains all positive linear
combinations of its elements. -/
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

/-- **Corollary 2.6.2.** The positive linear combinations of `S` form the smallest convex cone
including `S`. This cone need not contain the origin: it is the book's `cone S` only after the
origin is adjoined. -/
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

/-- **Corollary 2.6.3.** For a convex set `C`, the set `{λx | λ > 0, x ∈ C}` is the
smallest convex cone which includes `C`. -/
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

/-- A convex cone containing the origin, bundled as a Mathlib `PointedCone`. This is the bridge
Theorem 2.7 crosses: Rockafellar's cone plus `0 ∈ K` is exactly `PointedCone`. -/
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

/-- The carrier of `toPointedCone` is the set it came from. -/
@[simp] theorem coe_toPointedCone {K : Set (Rn n)} (hK : IsCone K) (hconv : Convex ℝ K)
    (h0 : (0 : Rn n) ∈ K) : (toPointedCone hK hconv h0 : Set (Rn n)) = K := rfl

/-- **Theorem 2.7**, second half: for a convex cone `K` containing `0` there is a largest
subspace contained in `K`, namely `(-K) ∩ K`. -/
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

/-- **Theorem 2.7**, first half: the smallest subspace containing a set is its
linear span. -/
theorem theorem_2_7_least (K : Set (Rn n)) :
    IsLeast {L : Submodule ℝ (Rn n) | K ⊆ (L : Set (Rn n))} (Submodule.span ℝ K) :=
  ⟨Submodule.subset_span, fun _ hL => Submodule.span_le.2 hL⟩

/-- **Theorem 2.7**, first half continued: for a convex cone `K` containing `0`, that
smallest subspace is `K - K`. -/
theorem theorem_2_7_sub {K : Set (Rn n)} (hK : IsCone K) (hconv : Convex ℝ K)
    (h0 : (0 : Rn n) ∈ K) : (Submodule.span ℝ K : Set (Rn n)) = K - K :=
  span_eq_sub_of_isCone ((isCone_iff_smul_set_eq K).1 hK) hconv h0

/-- **Theorem 2.7**, first half continued: that smallest subspace is `aff K`. This is
the last sentence of the book's proof — the affine hull of a set containing `0` is a subspace, by
Theorem 1.1. -/
theorem theorem_2_7_aff {K : Set (Rn n)} (h0 : (0 : Rn n) ∈ K) :
    (Submodule.span ℝ K : Set (Rn n)) = (affineSpan ℝ K : Set (Rn n)) :=
  (coe_affineSpan_of_zero_mem h0).symm

end Rockafellar
