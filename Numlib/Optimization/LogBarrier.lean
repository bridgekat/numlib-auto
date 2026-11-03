import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! # Boundary behavior of the logarithmic barrier -/

open Filter Metric
open scoped BigOperators Topology

namespace Optimization

variable {ι : Type*} [Fintype ι]

/-- The log barrier on the strictly positive orthant. -/
noncomputable def logBarrier (μ : ℝ) (x : ι → ℝ) : ℝ :=
  -μ * ∑ i, Real.log (x i)

/-- The closed nonnegative orthant. -/
def nonnegativeOrthant (ι : Type*) : Set (ι → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ici 0

omit [Fintype ι] in
/-- The boundary of the nonnegative orthant has a zero coordinate. -/
theorem mem_frontier_nonnegativeOrthant [Finite ι] {x : ι → ℝ} :
    x ∈ frontier (nonnegativeOrthant ι) ↔ (∀ i, 0 ≤ x i) ∧ ∃ i, x i = 0 := by
  classical
  have hclosed : IsClosed (nonnegativeOrthant ι) :=
    isClosed_set_pi fun _ _ ↦ isClosed_Ici
  rw [frontier, hclosed.closure_eq]
  unfold nonnegativeOrthant
  rw [interior_pi_set Set.finite_univ]
  simp only [Set.mem_sdiff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ici,
    interior_Ici, Set.mem_Ioi]
  constructor
  · rintro ⟨hn, hp⟩
    push Not at hp
    obtain ⟨i, hi⟩ := hp
    exact ⟨hn, i, le_antisymm hi (hn i)⟩
  · rintro ⟨hn, i, hi⟩
    exact ⟨hn, fun h ↦ (h i).ne' hi⟩

private theorem exists_coordinate_le_boundary_distance [Nonempty ι] {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) :
    ∃ i, x i ≤ infDist x (frontier (nonnegativeOrthant ι)) := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  have hfront : (frontier (nonnegativeOrthant ι)).Nonempty := by
    exact ⟨0, mem_frontier_nonnegativeOrthant.mpr ⟨fun _ ↦ le_rfl, i, rfl⟩⟩
  refine ⟨i, (le_infDist hfront).mpr fun y hy ↦ ?_⟩
  obtain ⟨-, j, hj⟩ := mem_frontier_nonnegativeOrthant.mp hy
  calc
    x i ≤ x j := hi j (Finset.mem_univ j)
    _ = dist (x j) (y j) := by rw [hj, Real.dist_eq, sub_zero, abs_of_pos (hx j)]
    _ ≤ dist x y := (dist_pi_le_iff dist_nonneg).mp le_rfl j

/-- The logarithmic barrier diverges along a uniformly bounded positive path whose
distance to the orthant boundary tends to zero. -/
theorem tendsto_logBarrier_of_bounded_of_infDist_frontier [Nonempty ι]
    {μ M : ℝ} (hμ : 0 < μ) {x : ℕ → ι → ℝ}
    (hx : ∀ n i, 0 < x n i) (hbounded : ∀ n i, x n i ≤ M)
    (ht : Tendsto (fun n ↦ infDist (x n) (frontier (nonnegativeOrthant ι))) atTop (𝓝 0)) :
    Tendsto (fun n ↦ logBarrier μ (x n)) atTop atTop := by
  classical
  let d (n : ℕ) := infDist (x n) (frontier (nonnegativeOrthant ι))
  let B := (Fintype.card ι : ℝ) * max 0 (Real.log M)
  have hd (n : ℕ) : 0 < d n := by
    obtain ⟨i, hi⟩ := exists_coordinate_le_boundary_distance (hx n)
    exact (hx n i).trans_le hi
  have hlog : Tendsto (fun n ↦ Real.log (d n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp <| tendsto_nhdsWithin_iff.mpr
      ⟨ht, Eventually.of_forall hd⟩
  have hsum (n : ℕ) : (∑ i, Real.log (x n i)) ≤ Real.log (d n) + B := by
    obtain ⟨i, hi⟩ := exists_coordinate_le_boundary_distance (hx n)
    have hothers : (∑ j ∈ Finset.univ.erase i, Real.log (x n j)) ≤ B := by
      calc
        _ ≤ ∑ _ ∈ Finset.univ.erase i, max 0 (Real.log M) :=
          Finset.sum_le_sum fun j _ ↦
            (Real.log_le_log (hx n j) (hbounded n j)).trans (le_max_right _ _)
        _ ≤ B := by
          simp only [Finset.sum_const, nsmul_eq_mul, B]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _)
            (le_max_left _ _)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact add_le_add hothers (Real.log_le_log (hx n i) hi) |>.trans_eq (add_comm _ _)
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_atBot.mp hlog (-b / μ - B)] with n hn
  have hs : (∑ i, Real.log (x n i)) ≤ -b / μ := by linarith [hsum n]
  have hs' := (le_div_iff₀ hμ).mp hs
  unfold logBarrier
  nlinarith only [hs']

end Optimization
