import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Card

/-!
# Finite coordinate sparsity constraints

Sparsity is a coordinate support cardinality bound. Coordinates larger than a box radius
cannot be removed by a step in that box. Optional supports form a finite cardinality
selection problem with explicit linear objective weights.
-/

noncomputable section
open Set
namespace Optimization.SparseConstraints
variable {ι : Type*} [Fintype ι]

/-- The finite support of a real coordinate vector. -/
def supportIndices (x : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

/-- Support membership is precisely a nonzero coordinate. -/
@[simp] theorem mem_supportIndices {x : ι → ℝ} {i : ι} :
    i ∈ supportIndices x ↔ x i ≠ 0 := by classical simp [supportIndices]

/-- Vectors with at most `k` nonzero coordinates. -/
def sparseSet (k : ℕ) : Set (ι → ℝ) := {x | (supportIndices x).card ≤ k}

/-- The sparsity constraint is the support cardinality inequality. -/
@[simp] theorem mem_sparseSet {k : ℕ} {x : ι → ℝ} :
    x ∈ sparseSet k ↔ (supportIndices x).card ≤ k := Iff.rfl

/-- The zero vector is sparse for every nonnegative cardinality budget, including zero. -/
@[simp] theorem zero_mem_sparseSet (k : ℕ) : (0 : ι → ℝ) ∈ sparseSet k := by
  classical
  simp [sparseSet, supportIndices]

/-- A zero sparsity budget forces every coordinate to vanish. -/
@[simp] theorem mem_sparseSet_zero {x : ι → ℝ} : x ∈ sparseSet 0 ↔ x = 0 := by
  classical
  simp [sparseSet, supportIndices, Finset.filter_eq_empty_iff, funext_iff]

/-- A support cardinality bound is equivalent to vanishing outside a small finite support. -/
theorem mem_sparseSet_iff_exists {k : ℕ} {x : ι → ℝ} :
    x ∈ sparseSet k ↔ ∃ s : Finset ι, s.card ≤ k ∧ ∀ i ∉ s, x i = 0 := by
  classical
  constructor
  · intro h
    exact ⟨supportIndices x, h, fun i hi => by simpa using hi⟩
  · rintro ⟨s, hs, hx⟩
    exact (Finset.card_le_card (show supportIndices x ⊆ s from fun i hi => by
      by_contra hn
      exact (mem_supportIndices.mp hi) (hx i hn))).trans hs

/-- Sparsity constraints are closed finite unions of coordinate subspaces. -/
theorem isClosed_sparseSet (k : ℕ) : IsClosed (sparseSet (ι := ι) k) := by
  classical
  have heq : sparseSet (ι := ι) k =
      ⋃ s : {s : Finset ι // s.card ≤ k}, {x : ι → ℝ | ∀ i ∉ s.val, x i = 0} := by
    ext x
    simp only [mem_sparseSet_iff_exists, mem_iUnion, mem_ofPred_eq, Subtype.exists, exists_prop]
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro s
  simp_rw [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (continuous_apply i) continuous_const

/-- Coordinates whose absolute value strictly exceeds the box radius are mandatory. -/
def mandatoryIndices (x : ι → ℝ) (δ : ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => δ < |x i|)

/-- Strict inequality defines mandatory coordinates; equality at the boundary is optional. -/
@[simp] theorem mem_mandatoryIndices {x : ι → ℝ} {δ : ℝ} {i : ι} :
    i ∈ mandatoryIndices x δ ↔ δ < |x i| := by classical simp [mandatoryIndices]

/-- At radius zero the mandatory coordinates are exactly the original support. -/
@[simp] theorem mandatoryIndices_zero (x : ι → ℝ) : mandatoryIndices x 0 = supportIndices x := by
  classical
  ext i
  simp [abs_pos]

/-- A coordinate exactly on the box boundary is optional, even when its value is zero. -/
theorem not_mem_mandatoryIndices_of_abs_eq {x : ι → ℝ} {δ : ℝ} {i : ι}
    (hi : |x i| = δ) : i ∉ mandatoryIndices x δ := by simp [hi]

/-- At nonnegative radii every mandatory coordinate already belongs to the support. -/
theorem mandatoryIndices_subset_support {x : ι → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) :
    mandatoryIndices x δ ⊆ supportIndices x := by
  intro i hi
  apply mem_supportIndices.mpr
  intro hx
  have := mem_mandatoryIndices.mp hi
  simp only [hx, abs_zero] at this
  linarith

/-- A box-feasible displacement cannot remove any mandatory coordinate. -/
theorem mandatoryIndices_subset_support_add {x d : ι → ℝ} {δ : ℝ}
    (hd : ∀ i, |d i| ≤ δ) : mandatoryIndices x δ ⊆ supportIndices (x + d) := by
  intro i hi
  apply mem_supportIndices.mpr
  intro hz
  have he : d i = -x i := by simpa using (eq_neg_of_add_eq_zero_right hz)
  have hb := hd i
  rw [he, abs_neg] at hb
  exact (not_lt_of_ge hb) (mem_mandatoryIndices.mp hi)

/-- Any sparse point in the box must reserve cardinality for every mandatory coordinate. -/
theorem mandatory_card_le {x d : ι → ℝ} {δ : ℝ} {k : ℕ}
    (hd : ∀ i, |d i| ≤ δ) (hx : x + d ∈ sparseSet k) :
    (mandatoryIndices x δ).card ≤ k :=
  (Finset.card_le_card (mandatoryIndices_subset_support_add hd)).trans hx

/-- Optional coordinate gain relative to dropping that coordinate in a linear box problem. -/
def optionalWeight (x g : ι → ℝ) (δ : ℝ) (i : ι) : ℝ := δ * |g i| - x i * g i

/-- Optional supports avoid mandatory coordinates and respect the remaining cardinality budget. -/
def optionalSupports (x : ι → ℝ) (δ : ℝ) (k : ℕ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (fun s => Disjoint s (mandatoryIndices x δ) ∧
    s.card ≤ k - (mandatoryIndices x δ).card)

/-- Optional-support membership spells out the finite binary selection constraints. -/
@[simp] theorem mem_optionalSupports {x : ι → ℝ} {δ : ℝ} {k : ℕ} {s : Finset ι} :
    s ∈ optionalSupports x δ k ↔
      Disjoint s (mandatoryIndices x δ) ∧ s.card ≤ k - (mandatoryIndices x δ).card := by
  classical
  simp [optionalSupports]

/-- The finite optional-support search always contains the empty choice. -/
theorem optionalSupports_nonempty (x : ι → ℝ) (δ : ℝ) (k : ℕ) :
    (optionalSupports x δ k).Nonempty := by
  classical
  exact ⟨∅, by simp⟩

end Optimization.SparseConstraints
