/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Finset.Nat

/-!
# Extrema of order-indexed constants

The complexity bounds of the high-order methods of [cartis2022evaluation], Chapters 12 and 13, use
maxima and minima of constants $u_j$ indexed by the orders $j \in \{1, \dots, q\}$. This file
defines these extrema and proves their elementary properties. The maximum and the minimum with a
base value $b$ are
$$\operatorname{finMax}(b, u, q) = \max\Big(b, \max_{1 \le j \le q} u_j\Big), \qquad
  \operatorname{finMin}(b, u, q) = \min\Big(b, \min_{1 \le j \le q} u_j\Big),$$
for example $L_f = \operatorname{finMax}(1, L, q)$ and $\varepsilon_{\min} =
\operatorname{finMin}(1, \varepsilon, q)$. Without a base value, $\varepsilon_{\min} = \min_{1 \le j
\le q} \varepsilon_j$ and $\max_{1 \le i \le r} \kappa_i$ take the value $0$ when the range of
orders is empty, and $L_f = \max_{0 \le j \le q} L_j$ is a maximum over the orders $0, \dots, q$.

## Main definitions

* `Optimization.finMax`: the maximum of a base value $b$ and of $u_1, \dots, u_q$.
* `Optimization.finMin`: the minimum of a base value $b$ and of $u_1, \dots, u_q$.
* `Optimization.epsMin`: the minimum $\min_{1 \le j \le q} \varepsilon_j$, with the value $0$ for
  $q = 0$.
* `Optimization.ordMax`: the maximum $\max_{1 \le i \le r} \kappa_i$, with the value $0$ for
  $r = 0$.
* `Optimization.lipMax`: the maximum $\max_{0 \le j \le q} L_j$.

## Main results

* `Optimization.one_le_finMax`: $\operatorname{finMax}(1, L, p) \ge 1$.
* `Optimization.epsMin_eq_finMin`: for $q \ge 1$ and $\varepsilon_j \le 1$, the two forms of
  $\varepsilon_{\min}$ agree.
* `Optimization.ordMax_eq_finMax`: for $\kappa_i \ge 0$, $\max_{1 \le i \le r} \kappa_i =
  \operatorname{finMax}(0, \kappa, r)$.
-/

open scoped BigOperators

namespace Optimization

/-! ### Maxima and minima with a base value -/

section FinMinMax

/-- The **maximum with base value** $b$ of $u_1, \dots, u_q$:
$$\operatorname{finMax}(b, u, q) = \max\Big(b, \max_{1 \le j \le q} u_j\Big).$$
For $q = 0$ the value is $b$.

With $b = 1$ and $u_j \ge 1$ this is the constant $L_f = \max_j L_{f,j}$ of (12.2.6) and
(12.2.25) of [cartis2022evaluation]. With $b = 0$ and $u_j \ge 0$ it is
$\max_{1 \le j \le q} u_j$, as in (12.2.14). -/
noncomputable def finMax (b : ℝ) (u : ℕ → ℝ) (q : ℕ) : ℝ :=
  (insert b ((Finset.Icc 1 q).image u)).max' (Finset.insert_nonempty _ _)

/-- The **minimum with base value** $b$ of $u_1, \dots, u_q$:
$$\operatorname{finMin}(b, u, q) = \min\Big(b, \min_{1 \le j \le q} u_j\Big).$$
For $q = 0$ the value is $b$.

With $b = 1$ and $u_j \le 1$ this is the tolerance $\varepsilon_{\min} = \min_j \varepsilon_j$
of (12.2.7) of [cartis2022evaluation], and also the minimum $\min_j \varepsilon_j^{\pi_j}$. -/
noncomputable def finMin (b : ℝ) (u : ℕ → ℝ) (q : ℕ) : ℝ :=
  (insert b ((Finset.Icc 1 q).image u)).min' (Finset.insert_nonempty _ _)

variable {b c : ℝ} {u : ℕ → ℝ} {q j : ℕ}

/-- The base value is at most the maximum: $b \le \operatorname{finMax}(b, u, q)$. -/
theorem le_finMax_left : b ≤ finMax b u q :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

/-- For $1 \le j \le q$, $u_j \le \operatorname{finMax}(b, u, q)$. -/
theorem le_finMax (hj : j ∈ Finset.Icc 1 q) : u j ≤ finMax b u q :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem u hj))

/-- If $b \le c$ and $u_j \le c$ for $1 \le j \le q$, then $\operatorname{finMax}(b, u, q) \le c$.
-/
theorem finMax_le (hb : b ≤ c) (hu : ∀ j ∈ Finset.Icc 1 q, u j ≤ c) : finMax b u q ≤ c := by
  refine Finset.max'_le _ _ _ fun y hy => ?_
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact hb
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    exact hu j hj

/-- The value $\operatorname{finMax}(b, u, q)$ depends only on $u_1, \dots, u_q$: if $u_j = u'_j$
for $1 \le j \le q$, then $\operatorname{finMax}(b, u, q) = \operatorname{finMax}(b, u', q)$. -/
theorem finMax_congr {u u' : ℕ → ℝ} (h : ∀ j ∈ Finset.Icc 1 q, u j = u' j) :
    finMax b u q = finMax b u' q := by
  unfold finMax
  congr 2
  exact Finset.image_congr fun j hj => h j hj

/-- If $q \ge 1$ and $b \le u_j$ for $1 \le j \le q$, then $\operatorname{finMax}(b, u, q) = u_j$
for some $j$ with $1 \le j \le q$. -/
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

/-- The minimum is at most the base value: $\operatorname{finMin}(b, u, q) \le b$. -/
theorem finMin_le_left : finMin b u q ≤ b :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

/-- For $1 \le j \le q$, $\operatorname{finMin}(b, u, q) \le u_j$. -/
theorem finMin_le (hj : j ∈ Finset.Icc 1 q) : finMin b u q ≤ u j :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem u hj))

/-- If $c \le b$ and $c \le u_j$ for $1 \le j \le q$, then $c \le \operatorname{finMin}(b, u, q)$.
-/
theorem le_finMin (hb : c ≤ b) (hu : ∀ j ∈ Finset.Icc 1 q, c ≤ u j) : c ≤ finMin b u q := by
  refine Finset.le_min' _ _ _ fun y hy => ?_
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact hb
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    exact hu j hj

/-- If $q \ge 1$ and $u_j \le b$ for $1 \le j \le q$, then $\operatorname{finMin}(b, u, q) = u_j$
for some $j$ with $1 \le j \le q$. -/
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

/-- If $b > 0$ and $u_j > 0$ for $1 \le j \le q$, then $\operatorname{finMin}(b, u, q) > 0$. -/
theorem finMin_pos (hb : 0 < b) (hu : ∀ j ∈ Finset.Icc 1 q, 0 < u j) : 0 < finMin b u q := by
  have hy := Finset.min'_mem _ (Finset.insert_nonempty b ((Finset.Icc 1 q).image u))
  rw [finMin]
  rcases Finset.mem_insert.1 hy with h | h
  · rw [h]; exact hb
  · obtain ⟨j, hj, hj'⟩ := Finset.mem_image.1 h
    rw [← hj']; exact hu j hj

/-- If $b < c$ and $u_j < c$ for $1 \le j \le q$, then $\operatorname{finMax}(b, u, q) < c$. -/
theorem finMax_lt (hb : b < c) (hu : ∀ j ∈ Finset.Icc 1 q, u j < c) : finMax b u q < c := by
  unfold finMax
  refine (Finset.max'_lt_iff _ _).2 fun y hy => ?_
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact hb
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    exact hu j hj

/-- If $u_j > 0$ for $1 \le j \le q$, then
$$\frac{1}{\operatorname{finMin}(1, u, q)} \le 1 + \sum_{j=1}^{q} \frac{1}{u_j}.$$
-/
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

/-- For every sequence $L$ and every $p$, the constant $L_f = \operatorname{finMax}(1, L, p)$
satisfies $L_f \ge 1$. -/
theorem one_le_finMax {L : ℕ → ℝ} {p : ℕ} : 1 ≤ finMax 1 L p := le_finMax_left

/-- For every sequence $L$ and every $p$, $\operatorname{finMax}(1, L, p) > 0$. -/
theorem finMax_one_pos {L : ℕ → ℝ} {p : ℕ} : 0 < finMax 1 L p :=
  one_pos.trans_le le_finMax_left

/-! ### Extrema over the orders without a base value -/

section Orders

variable {q : ℕ} {ε : ℕ → ℝ} {j : ℕ}

/-- The smallest tolerance $\varepsilon_{\min} = \min_{1 \le j \le q} \varepsilon_j$. For $q = 0$
the value is $0$. -/
noncomputable def epsMin (q : ℕ) (ε : ℕ → ℝ) : ℝ :=
  if h : (Finset.Icc 1 q).Nonempty then (Finset.Icc 1 q).inf' h ε else 0

/-- The largest value $\max_{1 \le i \le r} \kappa_i$. For $r = 0$ the value is $0$.

The Chapter 13 methods of [cartis2022evaluation] use it for the constants $\kappa_{\nabla,\max}$
and $h_{k,\max}$. -/
noncomputable def ordMax (r : ℕ) (κ : ℕ → ℝ) : ℝ :=
  if h : (Finset.Icc 1 r).Nonempty then (Finset.Icc 1 r).sup' h κ else 0

/-- If $q \ge 1$, then $\varepsilon_{\min}$ is the infimum of $\varepsilon_1, \dots, \varepsilon_q$,
as `Finset.inf'`. -/
theorem epsMin_eq (hne : (Finset.Icc 1 q).Nonempty) : epsMin q ε = (Finset.Icc 1 q).inf' hne ε :=
  dite_eq_left_of_eq_true (eq_true hne)

/-- If $q \ge 1$, then $\max_{1 \le i \le q} \varepsilon_i$ is the supremum of
$\varepsilon_1, \dots, \varepsilon_q$, as `Finset.sup'`. -/
theorem ordMax_eq (hne : (Finset.Icc 1 q).Nonempty) : ordMax q ε = (Finset.Icc 1 q).sup' hne ε :=
  dite_eq_left_of_eq_true (eq_true hne)

/-- For $1 \le j \le q$, $\varepsilon_{\min} \le \varepsilon_j$. -/
theorem epsMin_le (hj : j ∈ Finset.Icc 1 q) : epsMin q ε ≤ ε j := by
  rw [epsMin_eq ⟨j, hj⟩]
  exact Finset.inf'_le _ hj

/-- For $1 \le j \le q$, $\varepsilon_j \le \max_{1 \le i \le q} \varepsilon_i$. -/
theorem le_ordMax (hj : j ∈ Finset.Icc 1 q) : ε j ≤ ordMax q ε := by
  rw [ordMax_eq ⟨j, hj⟩]
  exact Finset.le_sup' _ hj

/-- If $q \ge 1$, then $\varepsilon_{\min} = \varepsilon_j$ for some $j$ with $1 \le j \le q$. -/
theorem exists_epsMin_eq (hq : 1 ≤ q) : ∃ j ∈ Finset.Icc 1 q, epsMin q ε = ε j := by
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' hne ε
  exact ⟨j, hj, by rw [epsMin_eq hne, he]⟩

/-- If $q \ge 1$, then $\max_{1 \le i \le q} \varepsilon_i = \varepsilon_j$ for some $j$ with
$1 \le j \le q$. -/
theorem exists_ordMax_eq (hq : 1 ≤ q) : ∃ j ∈ Finset.Icc 1 q, ordMax q ε = ε j := by
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_sup' hne ε
  exact ⟨j, hj, by rw [ordMax_eq hne, he]⟩

/-- If $q \ge 1$, then $c \le \varepsilon_{\min}$ if and only if $c \le \varepsilon_j$ for all $j$
with $1 \le j \le q$. -/
theorem le_epsMin_iff (hq : 1 ≤ q) {c : ℝ} : c ≤ epsMin q ε ↔ ∀ j ∈ Finset.Icc 1 q, c ≤ ε j := by
  refine ⟨fun h j hj => h.trans (epsMin_le hj), fun h => ?_⟩
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) hq
  exact he ▸ h j hj

/-- If $q \ge 1$, then $\max_{1 \le i \le q} \varepsilon_i \le c$ if and only if
$\varepsilon_j \le c$ for all $j$ with $1 \le j \le q$. -/
theorem ordMax_le_iff (hq : 1 ≤ q) {c : ℝ} : ordMax q ε ≤ c ↔ ∀ j ∈ Finset.Icc 1 q, ε j ≤ c := by
  refine ⟨fun h j hj => (le_ordMax hj).trans h, fun h => ?_⟩
  obtain ⟨j, hj, he⟩ := exists_ordMax_eq (ε := ε) hq
  exact he ▸ h j hj

/-- If $q \ge 1$ and $\varepsilon_j > 0$ for $1 \le j \le q$, then $\varepsilon_{\min} > 0$. -/
theorem epsMin_pos (hq : 1 ≤ q) (hε : ∀ j ∈ Finset.Icc 1 q, 0 < ε j) : 0 < epsMin q ε := by
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) hq
  exact he ▸ hε j hj

/-- If $q \ge 1$ and $\varepsilon_j \le 1$ for $1 \le j \le q$, then $\varepsilon_{\min} \le 1$. -/
theorem epsMin_le_one (hq : 1 ≤ q) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ≤ 1) : epsMin q ε ≤ 1 :=
  (epsMin_le (Finset.mem_Icc.2 ⟨le_rfl, hq⟩)).trans (hε 1 (Finset.mem_Icc.2 ⟨le_rfl, hq⟩))

/-- If $\varepsilon_j \ge 0$ for $1 \le j \le q$, then $\max_{1 \le i \le q} \varepsilon_i \ge 0$.
This also holds for $q = 0$, where the maximum is $0$. -/
theorem ordMax_nonneg (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j) : 0 ≤ ordMax q ε := by
  by_cases hq : 1 ≤ q
  · obtain ⟨j, hj, he⟩ := exists_ordMax_eq (ε := ε) hq
    exact he ▸ hε j hj
  · have hne : ¬ (Finset.Icc 1 q).Nonempty := by
      rintro ⟨j, hj⟩
      exact hq ((Finset.mem_Icc.1 hj).1.trans (Finset.mem_Icc.1 hj).2)
    rw [ordMax, dite_eq_right_of_eq_false (eq_false hne)]

/-- If $q \ge 1$ and $c \ge 0$, then $\max_{1 \le i \le q} c \kappa_i = c \max_{1 \le i \le q}
\kappa_i$. -/
theorem ordMax_mul (hq : 1 ≤ q) {c : ℝ} (hc : 0 ≤ c) (κ : ℕ → ℝ) :
    ordMax q (fun i => c * κ i) = c * ordMax q κ := by
  have hne : (Finset.Icc 1 q).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hq⟩⟩
  refine le_antisymm ((ordMax_le_iff hq).2 fun i hi =>
    mul_le_mul_of_nonneg_left (le_ordMax hi) hc) ?_
  obtain ⟨j, hj, he⟩ := exists_ordMax_eq (ε := κ) hq
  rw [he]
  exact le_ordMax (ε := fun i => c * κ i) hj

/-- The value $\max_{1 \le i \le q} \kappa_i$ depends only on $\kappa_1, \dots, \kappa_q$: if
$\kappa_i = \kappa'_i$ for $1 \le i \le q$, the two maxima are equal. -/
theorem ordMax_congr {κ κ' : ℕ → ℝ} (h : ∀ i ∈ Finset.Icc 1 q, κ i = κ' i) :
    ordMax q κ = ordMax q κ' := by
  unfold ordMax
  split_ifs with hne
  · exact Finset.sup'_congr hne rfl h
  · rfl

/-- The largest Lipschitz constant $L_f = \max_{0 \le j \le q} L_{f,j}$ of (13.1.23) of
[cartis2022evaluation]. -/
noncomputable def lipMax (L : ℕ → ℝ) (q : ℕ) : ℝ :=
  (Finset.range (q + 1)).sup' Finset.nonempty_range_add_one L

/-- For $i \le q$, $L_i \le \max_{0 \le j \le q} L_j$. -/
theorem le_lipMax {L : ℕ → ℝ} {i : ℕ} (hi : i ≤ q) : L i ≤ lipMax L q :=
  Finset.le_sup' L (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

end Orders

/-- If $q \ge 1$ and $\varepsilon_j \le 1$ for $1 \le j \le q$, then $\min_{1 \le j \le q}
\varepsilon_j = \operatorname{finMin}(1, \varepsilon, q)$. -/
theorem epsMin_eq_finMin {q : ℕ} {ε : ℕ → ℝ} (hq : 1 ≤ q) (hε : ∀ j ∈ Finset.Icc 1 q, ε j ≤ 1) :
    epsMin q ε = finMin 1 ε q := by
  obtain ⟨j, hj, he⟩ := exists_epsMin_eq (ε := ε) hq
  refine le_antisymm (le_finMin (he ▸ hε j hj) fun i hi => epsMin_le hi) ?_
  rw [he]; exact finMin_le hj

/-- If $\kappa_i \ge 0$ for $1 \le i \le r$, then $\max_{1 \le i \le r} \kappa_i =
\operatorname{finMax}(0, \kappa, r)$. -/
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
