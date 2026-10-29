import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Finset.Nat

/-!
# Extrema over the orders `[1, q]`

The complexity bounds of the high-order methods ([cartis2022evaluation], Chapters 12–13) are
expressed through maxima and minima of order-indexed constants over `j ∈ [1, q]`:

* `finMax b u q = max(b, max_{j ∈ [1, q]} u_j)` and `finMin b u q = min(b, min_{j ∈ [1, q]} u_j)`,
  with a base value `b` (e.g. `L_f = finMax 1 L q`, `ε_min = finMin 1 ε q`);
* `epsMin q ε = min_{j ∈ [1, q]} ε_j` and `ordMax r κ = max_{i ∈ [1, r]} κ_i` (`0` when the range is
  empty), and `lipMax L q = max_{j ∈ [0, q]} L_j`.
-/

open scoped BigOperators

namespace Optimization

section FinMinMax

/-- `max(b, max_{j ∈ [1:q]} u_j)`: with `b = 1` and `u_j ≥ 1` this is the book's
`L_f = max_j L_{f,j}` ((12.2.6), (12.2.25)); with `b = 0` and `u_j ≥ 0` it is
`max_{j ∈ [1:q]} u_j` (as in (12.2.14)). -/
noncomputable def finMax (b : ℝ) (u : ℕ → ℝ) (q : ℕ) : ℝ :=
  (insert b ((Finset.Icc 1 q).image u)).max' (Finset.insert_nonempty _ _)

/-- `min(b, min_{j ∈ [1:q]} u_j)`: with `b = 1` and `u_j ≤ 1` this is the book's
`ε_min = min_j ε_j` ((12.2.7)) and `min_j ε_j^{π_j}`. -/
noncomputable def finMin (b : ℝ) (u : ℕ → ℝ) (q : ℕ) : ℝ :=
  (insert b ((Finset.Icc 1 q).image u)).min' (Finset.insert_nonempty _ _)

variable {b c : ℝ} {u : ℕ → ℝ} {q j : ℕ}

theorem le_finMax_left : b ≤ finMax b u q :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem le_finMax (hj : j ∈ Finset.Icc 1 q) : u j ≤ finMax b u q :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem u hj))

theorem finMax_le (hb : b ≤ c) (hu : ∀ j ∈ Finset.Icc 1 q, u j ≤ c) : finMax b u q ≤ c := by
  refine Finset.max'_le _ _ _ fun y hy => ?_
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact hb
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    exact hu j hj

/-- `finMax b u q` depends only on the values `u j`, `j ∈ [1 : q]`. -/
theorem finMax_congr {u u' : ℕ → ℝ} (h : ∀ j ∈ Finset.Icc 1 q, u j = u' j) :
    finMax b u q = finMax b u' q := by
  unfold finMax
  congr 2
  exact Finset.image_congr fun j hj => h j hj

/-- For `q ≥ 1` and `u_j ≥ b`, `finMax b u q` is the maximum of `u` over `[1:q]`. -/
theorem exists_finMax_eq (hq : 1 ≤ q) (hu : ∀ j ∈ Finset.Icc 1 q, b ≤ u j) :
    ∃ j ∈ Finset.Icc 1 q, finMax b u q = u j := by
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image (insert b ((Finset.Icc 1 q).image u)) id
    (Finset.insert_nonempty _ _)
  have hval : finMax b u q = y :=
    le_antisymm (finMax_le (hmax b (Finset.mem_insert_self _ _))
      fun j hj => hmax _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem u hj)))
      (Finset.le_max' _ _ hy)
  rcases Finset.mem_insert.1 hy with rfl | hy'
  · have h1 : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
    refine ⟨1, h1, le_antisymm ?_ (le_finMax h1)⟩
    rw [hval]; exact hu 1 h1
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy'
    exact ⟨j, hj, hval⟩

theorem finMin_le_left : finMin b u q ≤ b :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem finMin_le (hj : j ∈ Finset.Icc 1 q) : finMin b u q ≤ u j :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem u hj))

theorem le_finMin (hb : c ≤ b) (hu : ∀ j ∈ Finset.Icc 1 q, c ≤ u j) : c ≤ finMin b u q := by
  refine Finset.le_min' _ _ _ fun y hy => ?_
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact hb
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    exact hu j hj

/-- For `q ≥ 1` and `u_j ≤ b`, `finMin b u q` is the minimum of `u` over `[1:q]`. -/
theorem exists_finMin_eq (hq : 1 ≤ q) (hu : ∀ j ∈ Finset.Icc 1 q, u j ≤ b) :
    ∃ j ∈ Finset.Icc 1 q, finMin b u q = u j := by
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image (insert b ((Finset.Icc 1 q).image u)) id
    (Finset.insert_nonempty _ _)
  have hval : finMin b u q = y :=
    le_antisymm (Finset.min'_le _ _ hy) (le_finMin (hmin b (Finset.mem_insert_self _ _))
      fun j hj => hmin _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem u hj)))
  rcases Finset.mem_insert.1 hy with rfl | hy'
  · have h1 : 1 ∈ Finset.Icc 1 q := Finset.mem_Icc.2 ⟨le_rfl, hq⟩
    refine ⟨1, h1, le_antisymm (finMin_le h1) ?_⟩
    rw [hval]; exact hu 1 h1
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy'
    exact ⟨j, hj, hval⟩

/-- The minimum is positive when `b` and all `u_j` are. -/
theorem finMin_pos (hb : 0 < b) (hu : ∀ j ∈ Finset.Icc 1 q, 0 < u j) : 0 < finMin b u q := by
  have hy := Finset.min'_mem _ (Finset.insert_nonempty b ((Finset.Icc 1 q).image u))
  rw [finMin]
  rcases Finset.mem_insert.1 hy with h | h
  · rw [h]; exact hb
  · obtain ⟨j, hj, hj'⟩ := Finset.mem_image.1 h
    rw [← hj']; exact hu j hj

/-- A strict upper bound for `finMax`. -/
theorem finMax_lt (hb : b < c) (hu : ∀ j ∈ Finset.Icc 1 q, u j < c) : finMax b u q < c := by
  unfold finMax
  refine (Finset.max'_lt_iff _ _).2 fun y hy => ?_
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact hb
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    exact hu j hj

/-- `1/min(1, min_j u_j) ≤ 1 + ∑_j 1/u_j` for positive `u_j`. -/
theorem inv_finMin_one_le (hu : ∀ j ∈ Finset.Icc 1 q, 0 < u j) :
    (finMin 1 u q)⁻¹ ≤ 1 + ∑ j ∈ Finset.Icc 1 q, (u j)⁻¹ := by
  have hy := Finset.min'_mem _ (Finset.insert_nonempty (1 : ℝ) ((Finset.Icc 1 q).image u))
  have hnn : 0 ≤ ∑ j ∈ Finset.Icc 1 q, (u j)⁻¹ :=
    Finset.sum_nonneg fun j hj => (inv_pos.2 (hu j hj)).le
  rw [finMin]
  rcases Finset.mem_insert.1 hy with h | h
  · rw [h, inv_one]; linarith
  · obtain ⟨j, hj, hj'⟩ := Finset.mem_image.1 h
    rw [← hj']
    have := Finset.single_le_sum (f := fun j => (u j)⁻¹) (fun i hi => (inv_pos.2 (hu i hi)).le) hj
    linarith

end FinMinMax

/-- `L_f = finMax 1 L p ≥ 1`. -/
theorem one_le_finMax {L : ℕ → ℝ} {p : ℕ} : 1 ≤ finMax 1 L p := le_finMax_left

theorem finMax_one_pos {L : ℕ → ℝ} {p : ℕ} : 0 < finMax 1 L p :=
  one_pos.trans_le le_finMax_left

section Orders

variable {q : ℕ} {ε : ℕ → ℝ} {j : ℕ}

/-- The smallest tolerance `ε_min = min_{j ∈ [1, q]} ε_j` (`0` if `q = 0`). -/
noncomputable def epsMin (q : ℕ) (ε : ℕ → ℝ) : ℝ :=
  if h : (Finset.Icc 1 q).Nonempty then (Finset.Icc 1 q).inf' h ε else 0

/-- The largest value `max_{i ∈ [1, r]} κ_i` (`0` if `r = 0`), used for `κ_{∇,max}` and
`h_{k,max}`. -/
noncomputable def ordMax (r : ℕ) (κ : ℕ → ℝ) : ℝ :=
  if h : (Finset.Icc 1 r).Nonempty then (Finset.Icc 1 r).sup' h κ else 0

theorem epsMin_eq (hne : (Finset.Icc 1 q).Nonempty) : epsMin q ε = (Finset.Icc 1 q).inf' hne ε :=
  dite_eq_left_of_eq_true (eq_true hne)

theorem ordMax_eq (hne : (Finset.Icc 1 q).Nonempty) : ordMax q ε = (Finset.Icc 1 q).sup' hne ε :=
  dite_eq_left_of_eq_true (eq_true hne)

theorem epsMin_le (hj : j ∈ Finset.Icc 1 q) : epsMin q ε ≤ ε j := by
  rw [epsMin_eq ⟨j, hj⟩]
  exact Finset.inf'_le _ hj

theorem le_ordMax (hj : j ∈ Finset.Icc 1 q) : ε j ≤ ordMax q ε := by
  rw [ordMax_eq ⟨j, hj⟩]
  exact Finset.le_sup' _ hj

theorem exists_epsMin_eq (hq : 1 ≤ q) : ∃ j ∈ Finset.Icc 1 q, epsMin q ε = ε j := by
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' hne ε
  exact ⟨j, hj, by rw [epsMin_eq hne, he]⟩

theorem exists_ordMax_eq (hq : 1 ≤ q) : ∃ j ∈ Finset.Icc 1 q, ordMax q ε = ε j := by
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' hne ε
  exact ⟨j, hj, by rw [ordMax_eq hne, he]⟩

theorem le_epsMin_iff (hq : 1 ≤ q) {c : ℝ} : c ≤ epsMin q ε ↔ ∀ j ∈ Finset.Icc 1 q, c ≤ ε j := by
  refine ⟨fun h j hj => h.trans (epsMin_le hj), fun h => ?_⟩
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) hq
  exact he ▸ h j hj

theorem ordMax_le_iff (hq : 1 ≤ q) {c : ℝ} : ordMax q ε ≤ c ↔ ∀ j ∈ Finset.Icc 1 q, ε j ≤ c := by
  refine ⟨fun h j hj => (le_ordMax hj).trans h, fun h => ?_⟩
  obtain ⟨j, hj, he⟩ := exists_ordMax_eq (ε := ε) hq
  exact he ▸ h j hj

theorem epsMin_pos (hq : 1 ≤ q) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) : 0 < epsMin q ε := by
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) hq
  exact he ▸ hε j hj

theorem epsMin_le_one (hq : 1 ≤ q) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ≤ 1) : epsMin q ε ≤ 1 :=
  (epsMin_le (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)).trans (hε 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩))

theorem ordMax_nonneg (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) : 0 ≤ ordMax q ε := by
  by_cases hq : 1 ≤ q
  · obtain ⟨j, hj, he⟩ := exists_ordMax_eq (ε := ε) hq
    exact he ▸ hε j hj
  · have hne : ¬ (Finset.Icc 1 q).Nonempty := by
      rintro ⟨j, hj⟩
      exact hq ((Finset.mem_Icc.1 hj).1.trans (Finset.mem_Icc.1 hj).2)
    rw [ordMax, dite_eq_right_of_eq_false (eq_false hne)]

/-- Scaling all values by `c ≥ 0` scales the maximum. -/
theorem ordMax_mul (hq : 1 ≤ q) {c : ℝ} (hc : 0 ≤ c) (κ : ℕ → ℝ) :
    ordMax q (fun i => c * κ i) = c * ordMax q κ := by
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  refine le_antisymm ((ordMax_le_iff hq).2 fun i hi =>
    mul_le_mul_of_nonneg_left (le_ordMax hi) hc) ?_
  obtain ⟨j, hj, he⟩ := exists_ordMax_eq (ε := κ) hq
  rw [he]
  exact le_ordMax (ε := fun i => c * κ i) hj

/-- The values agree on `[1, q]`: same maximum. -/
theorem ordMax_congr {κ κ' : ℕ → ℝ} (h : ∀ i ∈ Finset.Icc 1 q, κ i = κ' i) :
    ordMax q κ = ordMax q κ' := by
  unfold ordMax
  split_ifs with hne
  · exact Finset.sup'_congr hne rfl h
  · rfl

/-- The largest Lipschitz constant `L_f = max_{j ∈ [0, q]} L_{f,j}` (13.1.23). -/
noncomputable def lipMax (L : ℕ → ℝ) (q : ℕ) : ℝ :=
  (Finset.range (q + 1)).sup' Finset.nonempty_range_add_one L

theorem le_lipMax {L : ℕ → ℝ} {i : ℕ} (hi : i ≤ q) : L i ≤ lipMax L q :=
  Finset.le_sup' L (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

end Orders

/-- For tolerances `ε_j ≤ 1` (`q ≥ 1`), the smallest tolerance is `finMin 1 ε q`. -/
theorem epsMin_eq_finMin {q : ℕ} {ε : ℕ → ℝ} (hq : 1 ≤ q) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ≤ 1) :
    epsMin q ε = finMin 1 ε q := by
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) hq
  refine le_antisymm (le_finMin (he ▸ hε j hj) fun i hi => epsMin_le hi) ?_
  rw [he]; exact finMin_le hj

/-- For nonnegative values, the largest value over `[1, r]` is `finMax 0 κ r`. -/
theorem ordMax_eq_finMax {r : ℕ} {κ : ℕ → ℝ} (hκ : ∀ i ∈ Finset.Icc 1 r, 0 ≤ κ i) :
    ordMax r κ = finMax 0 κ r :=
  le_antisymm (by
    by_cases hr : 1 ≤ r
    · obtain ⟨j, hj, he⟩ := exists_ordMax_eq (ε := κ) hr
      rw [he]; exact le_finMax hj
    · have hne : ¬ (Finset.Icc 1 r).Nonempty := fun ⟨j, hj⟩ =>
        hr ((Finset.mem_Icc.1 hj).1.trans (Finset.mem_Icc.1 hj).2)
      rw [ordMax, dite_eq_right_of_eq_false (eq_false hne)]; exact le_finMax_left)
    (finMax_le (ordMax_nonneg hκ) fun _ hi => le_ordMax hi)

end Optimization
