/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: a Mathlib file on real intervals. The file is about `ℝ`: the endpoints and nodes are
real numbers, although `mono`, `lt`, `left_le`, `le_right`, `Icc_subset` and `exists_mem_panel`
use only the linear order.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Partitions of a real interval

`IsIntervalPartition a b n x` says that the real nodes `x 0, …, x n` cut `[a, b] ⊆ ℝ` into `n`
panels: `a = x 0 < x 1 < ⋯ < x n = b` ([quarteroni2000numerical] Definition 8.1). It is the mesh
of the piecewise polynomial interpolation operators, the splines and the one-dimensional finite
elements.

## Main results

* `IsIntervalPartition.mono`, `IsIntervalPartition.lt`: the nodes are monotone, strictly, along the
  used range.
* `IsIntervalPartition.Icc_subset`: every panel lies in `[a, b]`.
* `IsIntervalPartition.exists_mem_panel`: every point of `[a, b]` lies in a panel.
* `IsIntervalPartition.node_eq_of_uniform`: the nodes of a uniform mesh are `a + i h`.
-/

open Set

variable {a b : ℝ} {n : ℕ} {x : ℕ → ℝ}

/-- The nodes of [quarteroni2000numerical] Definition 8.1: `a = x 0 < x 1 < ⋯ < x n = b`, `n`
panels and `n + 1` nodes; only `x 0, …, x n` are ever used. -/
structure IsIntervalPartition (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop where
  /-- Consecutive nodes increase. -/
  step : ∀ j < n, x j < x (j + 1)
  /-- The first node is `a`. -/
  first : x 0 = a
  /-- The last node is `b`. -/
  last : x n = b

namespace IsIntervalPartition

variable (hx : IsIntervalPartition a b n x)
include hx

/-- The nodes are monotone along the used range. -/
theorem mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) : x i ≤ x j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (ih (by omega)).trans (hx.step m (by omega)).le

/-- The nodes are strictly monotone along the used range. -/
theorem lt {i j : ℕ} (hij : i < j) (hj : j ≤ n) : x i < x j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  exact (hx.mono (by omega) (by omega)).trans_lt (hx.step m (by omega))

/-- `a ≤ x i` for `i ≤ n`. -/
theorem left_le {i : ℕ} (hi : i ≤ n) : a ≤ x i := hx.first ▸ hx.mono (Nat.zero_le i) hi

/-- `x i ≤ b` for `i ≤ n`. -/
theorem le_right {i : ℕ} (hi : i ≤ n) : x i ≤ b := hx.last ▸ hx.mono hi le_rfl

/-- The endpoints are ordered. -/
theorem le : a ≤ b := hx.last ▸ hx.left_le le_rfl

/-- The endpoints are strictly ordered when there is at least one panel. -/
theorem lt_of_pos (hn : 1 ≤ n) : a < b := hx.first ▸ hx.last ▸ hx.lt hn le_rfl

/-- A panel lies inside `[a, b]`. -/
theorem Icc_subset {i : ℕ} (hi : i < n) : Icc (x i) (x (i + 1)) ⊆ Icc a b :=
  Icc_subset_Icc (hx.left_le hi.le) (hx.le_right hi)

/-- Every point of `[a, b]` lies in a panel `[x (i - 1), x i]` with `1 ≤ i ≤ n`, which can be
chosen so that `x (i - 1) < t` unless `t = a` (and then `i = 1`). -/
theorem exists_mem_panel (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Icc a b) :
    ∃ i, 1 ≤ i ∧ i ≤ n ∧ t ∈ Icc (x (i - 1)) (x i) ∧ (x (i - 1) < t ∨ i = 1) := by
  classical
  set S : Finset ℕ := (Finset.range n).filter fun j => x j < t with hS
  rcases S.eq_empty_or_nonempty with hS0 | hS0
  · have hta : t = a := by
      refine le_antisymm ?_ ht.1
      by_contra h
      have : 0 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, by
        rw [hx.first]; exact lt_of_not_ge h⟩
      simp [hS0] at this
    refine ⟨1, le_rfl, hn, ⟨?_, ?_⟩, Or.inr rfl⟩
    · simpa [hx.first] using ht.1
    · rw [hta, ← hx.first]; exact (hx.step 0 hn).le
  · set m := S.max' hS0 with hm
    have hmS : m ∈ S := S.max'_mem _
    obtain ⟨hmr, hmt⟩ := Finset.mem_filter.mp hmS
    have hmn : m < n := Finset.mem_range.mp hmr
    refine ⟨m + 1, by omega, hmn, ⟨by simpa using hmt.le, ?_⟩, Or.inl (by simpa using hmt)⟩
    by_contra h
    push Not at h
    have hm1 : m + 1 < n := by
      by_contra h'
      have : m + 1 = n := by omega
      rw [this, hx.last] at h
      exact absurd ht.2 (not_le.mpr h)
    have := S.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm1, h⟩)
    omega

/-- **The nodes of a uniform mesh** are `x_i = a + i h`. -/
theorem node_eq_of_uniform {h : ℝ} (huni : ∀ j < n, x (j + 1) - x j = h) {i : ℕ} (hi : i ≤ n) :
    x i = a + i * h := by
  induction i with
  | zero => simp [hx.first]
  | succ m ih =>
      have hstep := huni m (by omega)
      have hm := ih (by omega)
      push_cast
      rw [show x (m + 1) = x m + h by linarith, hm]
      ring

end IsIntervalPartition
