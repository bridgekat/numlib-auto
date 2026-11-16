/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

A partition of an interval $[a, b] \subseteq \mathbb{R}$ into $n$ panels is a list of nodes
$x_0, \dots, x_n$ with $a = x_0 < x_1 < \dots < x_n = b$, as in Definition 8.1 of
[quarteroni2000numerical]. The panels are the subintervals $[x_{i-1}, x_i]$. Partitions are the
meshes of the piecewise polynomial interpolation operators, of the splines and of the
one-dimensional finite elements. This module defines partitions and proves the elementary facts
about the order of the nodes, the panels, and uniform meshes.

## Main definitions

* `IsIntervalPartition`: the nodes $x_0, \dots, x_n$ form a partition of $[a, b]$ into $n$ panels.

## Main results

* `IsIntervalPartition.mono`, `IsIntervalPartition.lt`: the nodes $x_0, \dots, x_n$ increase, and
  increase strictly.
* `IsIntervalPartition.Icc_subset`: every panel lies in $[a, b]$.
* `IsIntervalPartition.exists_mem_panel`: every point of $[a, b]$ lies in a panel.
* `IsIntervalPartition.node_eq_of_uniform`: the nodes of a uniform mesh with step $h$ are
  $x_i = a + ih$.

## Implementation notes

* The nodes are a sequence `x : ℕ → ℝ`. Only $x_0, \dots, x_n$ are used, and the later terms are
  arbitrary.
* The results `IsIntervalPartition.mono`, `IsIntervalPartition.lt`, `IsIntervalPartition.left_le`,
  `IsIntervalPartition.le_right`, `IsIntervalPartition.Icc_subset` and
  `IsIntervalPartition.exists_mem_panel` use only the linear order of $\mathbb{R}$.
-/

open Set

variable {a b : ℝ} {n : ℕ} {x : ℕ → ℝ}

/-- The real numbers $x_0, \dots, x_n$ form a **partition of $[a, b]$ into $n$ panels** if
$$a = x_0 < x_1 < \dots < x_n = b.$$
A partition into $n$ panels has $n + 1$ nodes. This is Definition 8.1 of
[quarteroni2000numerical].

The nodes are the first $n + 1$ terms of a sequence `x : ℕ → ℝ`. The later terms are not used. -/
structure IsIntervalPartition (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop where
  /-- Consecutive nodes increase: $x_j < x_{j+1}$ for every $j < n$. -/
  step : ∀ j < n, x j < x (j + 1)
  /-- The first node is $x_0 = a$. -/
  first : x 0 = a
  /-- The last node is $x_n = b$. -/
  last : x n = b

namespace IsIntervalPartition

variable (hx : IsIntervalPartition a b n x)
include hx

/-- Let $x_0, \dots, x_n$ be a partition of $[a, b]$. If $i \le j \le n$, then $x_i \le x_j$. -/
theorem mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) : x i ≤ x j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (ih (by omega)).trans (hx.step m (by omega)).le

/-- Let $x_0, \dots, x_n$ be a partition of $[a, b]$. If $i < j \le n$, then $x_i < x_j$. -/
theorem lt {i j : ℕ} (hij : i < j) (hj : j ≤ n) : x i < x j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  exact (hx.mono (by omega) (by omega)).trans_lt (hx.step m (by omega))

/-- Let $x_0, \dots, x_n$ be a partition of $[a, b]$. Then $a \le x_i$ for every $i \le n$. -/
theorem left_le {i : ℕ} (hi : i ≤ n) : a ≤ x i := hx.first ▸ hx.mono (Nat.zero_le i) hi

/-- Let $x_0, \dots, x_n$ be a partition of $[a, b]$. Then $x_i \le b$ for every $i \le n$. -/
theorem le_right {i : ℕ} (hi : i ≤ n) : x i ≤ b := hx.last ▸ hx.mono hi le_rfl

/-- If $[a, b]$ has a partition, then $a \le b$. -/
theorem le : a ≤ b := hx.last ▸ hx.left_le le_rfl

/-- If $[a, b]$ has a partition into $n \ge 1$ panels, then $a < b$. -/
theorem lt_of_pos (hn : 1 ≤ n) : a < b := hx.first ▸ hx.last ▸ hx.lt hn le_rfl

/-- Let $x_0, \dots, x_n$ be a partition of $[a, b]$. For every $i < n$, the panel $[x_i, x_{i+1}]$
lies in $[a, b]$. -/
theorem Icc_subset {i : ℕ} (hi : i < n) : Icc (x i) (x (i + 1)) ⊆ Icc a b :=
  Icc_subset_Icc (hx.left_le hi.le) (hx.le_right hi)

/-- Let $x_0, \dots, x_n$ be a partition of $[a, b]$ with $n \ge 1$, and let $t \in [a, b]$. Then
there is an index $i$ with $1 \le i \le n$ and $t \in [x_{i-1}, x_i]$, and $i$ can be chosen so
that $x_{i-1} < t$ or $i = 1$.

The last condition says that $t$ lies in the half-open panel $(x_{i-1}, x_i]$, unless $t = a$,
which lies in the first panel. -/
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

/-- Let $x_0, \dots, x_n$ be a partition of $[a, b]$ with constant step $h$, that is,
$x_{j+1} - x_j = h$ for every $j < n$. Then
$$x_i = a + ih \quad \text{for every } i \le n.$$
-/
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
