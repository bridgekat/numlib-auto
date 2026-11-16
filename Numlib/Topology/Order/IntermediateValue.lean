/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The discrete mean value theorem

A weighted sum of values of a continuous function, with nonnegative weights, is a value of the
function times the sum of the weights. For $u$ continuous on $[a, b]$, points $x_j \in [a, b]$ and
weights $\delta_j \ge 0$, there is $\eta \in [a, b]$ with
$$\sum_j \delta_j \, u(x_j) = u(\eta) \sum_j \delta_j.$$
This is the *discrete mean value theorem*, Theorem 9.1 of [quarteroni2000numerical]. It turns a
quadrature error written as a sum of panel errors $\sum_j c \, f^{(k)}(\xi_j)$ into a single value
$m \, c \, f^{(k)}(\xi)$, which is a step of every composite error formula
(`Numlib.Approximation.NewtonCotes` and `Numlib.Analysis.SpecialFunctions.EulerMaclaurin`). The file
also gives the intermediate value theorem in the form used to locate roots: a continuous real
function that changes sign between $u < v$ has a root in $(u, v)$.

## Main results

* `ContinuousOn.exists_sum_mul_eq_mul_sum_of_ordConnected`: the discrete mean value theorem on an
  order-connected set, for a nonempty finite family of points.
* `ContinuousOn.exists_sum_mul_eq_mul_sum`: the discrete mean value theorem on $[a, b]$.
* `Continuous.exists_mem_Ioo_eq_zero_of_mul_neg`: if $F : \mathbb{R} \to \mathbb{R}$ is continuous,
  $u < v$ and $F(u) F(v) < 0$, then $F$ has a root in $(u, v)$.
* `ContinuousMap.exists_mem_Ioo_eq_zero_of_mul_neg`: the same for a continuous function on $[a, b]$.

## Proof outline

The weighted sum lies between $u(x_p) \sum_j \delta_j$ and $u(x_q) \sum_j \delta_j$, where $u(x_j)$
is smallest at $j = p$ and largest at $j = q$. The intermediate value theorem for
$y \mapsto u(y) \sum_j \delta_j$ on the interval between $x_p$ and $x_q$ gives $\eta$.

## Implementation notes

* The source states the theorem for weights that all have the same sign. The case of nonpositive
  weights is the nonnegative case applied to $-\delta$, so only the nonnegative case is stated.
* The domain is any densely ordered, conditionally complete linear order with the order topology.
  The codomain is any linearly ordered commutative semiring with an order-closed topology and
  continuous multiplication. In every use both are $\mathbb{R}$.
* The theorem is placed beside Mathlib's `intermediate_value_uIcc`, so that the analysis modules
  that use it do not import approximation theory.
-/

open Set

variable {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [DenselyOrdered α] {R : Type*} [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
  [TopologicalSpace R] [OrderClosedTopology R] [ContinuousMul R]

/-- The **discrete mean value theorem** on an order-connected set. Let $S$ be an order-connected set
(it contains $[x, y]$ whenever it contains $x$ and $y$), and let $u$ be continuous on $S$. Let
$(x_j)_{j \in \iota}$ be a nonempty finite family of points of $S$, and let $\delta_j \ge 0$ for
all $j$. Then there is $\eta \in S$ with
$$\sum_j \delta_j \, u(x_j) = u(\eta) \sum_j \delta_j.$$

The domain is a densely ordered, conditionally complete linear order with the order topology.
The codomain is a linearly ordered commutative semiring with an order-closed topology and
continuous multiplication. If $S$ is an open interval, then $\eta$ lies strictly inside it. -/
theorem ContinuousOn.exists_sum_mul_eq_mul_sum_of_ordConnected {S : Set α} (hS : S.OrdConnected)
    {u : α → R} (hu : ContinuousOn u S) {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → α}
    (hx : ∀ j, x j ∈ S) {δ : ι → R} (hδ : ∀ j, 0 ≤ δ j) :
    ∃ η ∈ S, ∑ j, δ j * u (x j) = u η * ∑ j, δ j := by
  obtain ⟨p, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun j => u (x j))
    Finset.univ_nonempty
  obtain ⟨q, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => u (x j))
    Finset.univ_nonempty
  have hlow : u (x p) * ∑ j, δ j ≤ ∑ j, δ j * u (x j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ j)) (hδ j)
  have hhigh : ∑ j, δ j * u (x j) ≤ u (x q) * ∑ j, δ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [mul_comm (u (x q))]
      exact mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j)) (hδ j)
  have hpq : uIcc (x p) (x q) ⊆ S := hS.uIcc_subset (hx p) (hx q)
  have hcont : ContinuousOn (fun t => u t * ∑ j, δ j) (uIcc (x p) (x q)) :=
    (hu.mono hpq).mul continuousOn_const
  obtain ⟨η, hη, hηval⟩ := intermediate_value_uIcc hcont (mem_uIcc_of_le hlow hhigh)
  exact ⟨η, hpq hη, hηval.symm⟩

/-- The **discrete mean value theorem**. Let $a \le b$, let $u$ be continuous on $[a, b]$, let
$(x_j)_{j \in \iota}$ be a finite family of points of $[a, b]$, and let $\delta_j \ge 0$ for all
$j$. Then there is $\eta \in [a, b]$ with
$$\sum_j \delta_j \, u(x_j) = u(\eta) \sum_j \delta_j.$$
This is Theorem 9.1 of [quarteroni2000numerical].

The family may be empty; then both sides are $0$ and every $\eta \in [a, b]$ works. For a
nonempty family this is the case $S = [a, b]$ of
`ContinuousOn.exists_sum_mul_eq_mul_sum_of_ordConnected`. -/
theorem ContinuousOn.exists_sum_mul_eq_mul_sum {a b : α} (hab : a ≤ b) {u : α → R}
    (hu : ContinuousOn u (Icc a b)) {ι : Type*} [Fintype ι] {x : ι → α}
    (hx : ∀ j, x j ∈ Icc a b) {δ : ι → R} (hδ : ∀ j, 0 ≤ δ j) :
    ∃ η ∈ Icc a b, ∑ j, δ j * u (x j) = u η * ∑ j, δ j := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨a, left_mem_Icc.2 hab, by simp⟩
  · exact hu.exists_sum_mul_eq_mul_sum_of_ordConnected ordConnected_Icc hx hδ

/-! ### Roots between two points of opposite sign -/

section Root

/-- Let $F : \mathbb{R} \to \mathbb{R}$ be continuous, and let $u < v$ with $F(u) F(v) < 0$. Then
there is $z \in (u, v)$ with $F(z) = 0$. -/
theorem Continuous.exists_mem_Ioo_eq_zero_of_mul_neg {F : ℝ → ℝ} (hF : Continuous F) {u v : ℝ}
    (huv : u < v) (h : F u * F v < 0) : ∃ z ∈ Set.Ioo u v, F z = 0 := by
  rcases mul_neg_iff.mp h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · obtain ⟨z, hz, hz0⟩ :=
      intermediate_value_Ioo' huv.le hF.continuousOn (Set.mem_Ioo.mpr ⟨hv, hu⟩)
    exact ⟨z, hz, hz0⟩
  · obtain ⟨z, hz, hz0⟩ :=
      intermediate_value_Ioo huv.le hF.continuousOn (Set.mem_Ioo.mpr ⟨hu, hv⟩)
    exact ⟨z, hz, hz0⟩

/-- The intermediate value theorem on $[a, b]$. Let $g : [a, b] \to \mathbb{R}$ be continuous, and
let $u, v \in [a, b]$ with $u < v$ and $g(u) g(v) < 0$. Then there is $z \in [a, b]$ with
$u < z < v$ and $g(z) = 0$. -/
theorem ContinuousMap.exists_mem_Ioo_eq_zero_of_mul_neg {a b : ℝ} {g : C(Icc a b, ℝ)}
    {u v : Icc a b}
    (huv : (u : ℝ) < v) (h : g u * g v < 0) :
    ∃ z : Icc a b, (u : ℝ) < z ∧ (z : ℝ) < v ∧ g z = 0 := by
  have hab : a ≤ b := u.2.1.trans u.2.2
  set G : ℝ → ℝ := IccExtend hab g with hG
  have hGu : G u = g u := IccExtend_val hab g u
  have hGv : G v = g v := IccExtend_val hab g v
  have hcont : ContinuousOn G (Icc (u : ℝ) v) :=
    (g.continuous.Icc_extend' (h := hab)).continuousOn
  have key : ∃ z ∈ Ioo (u : ℝ) v, G z = 0 := by
    rcases mul_neg_iff.mp h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' huv.le hcont
        (show (0 : ℝ) ∈ Ioo (G v) (G u) by rw [hGu, hGv]; exact ⟨hv, hu⟩)
      exact ⟨z, hz, hz0⟩
    · obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo huv.le hcont
        (show (0 : ℝ) ∈ Ioo (G u) (G v) by rw [hGu, hGv]; exact ⟨hu, hv⟩)
      exact ⟨z, hz, hz0⟩
  obtain ⟨z, hz, hz0⟩ := key
  have hzmem : z ∈ Icc a b := ⟨u.2.1.trans hz.1.le, hz.2.le.trans v.2.2⟩
  refine ⟨⟨z, hzmem⟩, hz.1, hz.2, ?_⟩
  rw [← hz0, hG, IccExtend_of_mem hab g hzmem]

end Root
