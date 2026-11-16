/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Convex.Combination
import Numlib.RingTheory.Polynomial.ShiftedPowers
import Numlib.Approximation.DividedDifference
import Numlib.Approximation.NewtonForm
import Numlib.Approximation.Spline

/-!
# B-splines

Let $x_0 \le x_1 \le x_2 \le \dots$ be a nondecreasing sequence of real knots. The normalized
B-spline $B_{i,k}$ of degree $k$ is defined by the Cox–de Boor recursion ((8.54) of
[quarteroni2000numerical]): $B_{i,0}$ is the indicator function of $[x_i, x_{i+1})$, and
$$B_{i,d+1}(t) = \omega_{i,d+1}(t)\, B_{i,d}(t) + \bigl(1 - \omega_{i+1,d+1}(t)\bigr)\,
  B_{i+1,d}(t), \qquad \omega_{i,d}(t) = \frac{t - x_i}{x_{i+d} - x_i},$$
with $\omega_{i,d} = 0$ when $x_{i+d} = x_i$. For distinct knots and $k \ge 1$, $B_{i,k}(t)$ is also
the scaled divided difference $(x_{i+k+1} - x_i)\, g[x_i, \dots, x_{i+k+1}]$ of the truncated power
$g(s) = (s - t)_+^k$, which is Definition 8.2 of [quarteroni2000numerical], with (8.51)–(8.53).

The file proves the support, nonnegativity, partition of unity, piecewise polynomial structure and
smoothness of the B-splines. On an extended knot sequence with $k$ further knots at each end, the
B-splines form a basis of the spline space of `Numlib.Approximation.Spline` ((8.55)–(8.56)). The
file also treats B-splines with coincident knots (Remark 8.3), the cubic B-spline on uniform knots
(Example 8.9), Boehm's knot insertion (Remark 8.4), and parametric B-spline curves with their
locality and convex-hull properties (§8.7.1). The presentation follows [quarteroni2000numerical],
with further material from chapters IX–XI of de Boor, *A Practical Guide to Splines*.

## Main definitions

* `BSpline.weight`: the Cox–de Boor weight $\omega_{i,d}$.
* `BSpline.bspline`: the normalized B-spline $B_{i,k}$ of degree $k$.
* `BSpline.nform`: the divided-difference form $(x_{i+k+1} - x_i)\, g[x_i, \dots, x_{i+k+1}]$ with
  $g(s) = (s - t)_+^k$.
* `BSpline.curve`: the parametric B-spline curve $t \mapsto \sum_{i < N} B_{i,k}(t)\, P_i$.
* `BSpline.insertKnot`, `BSpline.insertKnotWeight`, `BSpline.insertKnotCoeff`: the refined knot
  sequence, the weights and the new coefficients of Boehm's knot insertion.

## Main results

* `BSpline.bspline_eq_zero_of_notMem`, `BSpline.bspline_nonneg`, `BSpline.bspline_pos`,
  `BSpline.sum_bspline`, `BSpline.exists_eqOn_bspline`: $B_{i,k}$ vanishes outside
  $[x_i, x_{i+k+1})$, is nonnegative, and is positive on $(x_i, x_{i+k+1})$ for distinct knots; the
  B-splines sum to one; and $B_{i,k}$ is a polynomial of degree at most $k$ on each knot interval.
* `BSpline.bspline_eq_mul_newton_truncPow`, `BSpline.bspline_eq_sum_truncPow`: Definition 8.2 and
  (8.53) of [quarteroni2000numerical] as theorems, for distinct knots and $k \ge 1$.
* `BSpline.contDiff_bspline`, `BSpline.bspline_mem_splineSpace`: for distinct knots and $k \ge 1$,
  $B_{i,k}$ is of class $C^{k-1}$ and is a spline of degree $k$ and smoothness $C^{k-1}$.
* `BSpline.hasDerivAt_bspline`: the derivative of a B-spline away from the knots.
* `BSpline.linearIndependent_bspline`, `BSpline.exists_basis_bspline`: the B-splines form a basis of
  the spline space.
* `BSpline.exists_sum_C_mul_X_sub_C_pow_eq_zero_and_eqOn`, `BSpline.exists_eq_smul_bspline`:
  Schoenberg's characterization of $B_{i,k}$ as the unique, up to a scalar factor, $C^{k-1}$ spline
  of degree $k$ supported in $[x_i, x_{i+k+1}]$.
* `BSpline.bspline_apply_of_coincident_left`, `BSpline.bspline_apply_of_coincident_right`,
  `BSpline.bspline_apply_of_coincident`: B-splines with coincident knots.
* `BSpline.sum_smul_bspline_left`, `BSpline.sum_smul_bspline_right`: the endpoint values (8.57) of
  [quarteroni2000numerical] of a spline on knots of multiplicity $k + 1$ at the ends.
* `BSpline.bspline_uniform_cubic`: the cubic B-spline on uniform knots.
* `BSpline.bspline_eq_insert_comb`, `BSpline.sum_smul_bspline_insertKnot`: Boehm's knot insertion,
  for strictly increasing knots and a new knot in the interior of its knot interval.
* `BSpline.tendsto_bspline_of_tendsto`: a B-spline depends continuously on its knots when they are
  approached from below.
* `BSpline.bspline_eq_insert_comb_of_monotone`, `BSpline.sum_smul_bspline_insertKnot_of_monotone`:
  Boehm's knot insertion for nondecreasing knots and a new knot $y \in [x_j, x_{j+1})$, so that an
  existing knot may have its multiplicity raised.
* `BSpline.curve_mem_convexHull`, `BSpline.curve_update_eq_of_notMem`: the convex-hull and locality
  properties of B-spline curves.

## Proof outline

Schoenberg's characterization: a $C^{k-1}$ spline of degree $k$ supported in $[x_i, x_{i+k+1}]$ is
$\sum_{j \le m} c_j (t - x_{i+j})^k$ on the $m$-th knot interval, and the vanishing to the right of
$x_{i+k+1}$ puts $(c_j)$ in the kernel of $c \mapsto \sum_{j=0}^{k+1} c_j (X - x_{i+j})^k$. For
$k + 2$ distinct knots this kernel is one-dimensional, by a Vandermonde argument
(`Polynomial.linearIndependent_X_sub_C_pow` and
`Polynomial.exists_eq_smul_of_sum_C_mul_X_sub_C_pow_eq_zero` of
`Numlib.RingTheory.Polynomial.ShiftedPowers`).

Boehm's algorithm for nondecreasing knots: the divided-difference proof of the strictly increasing
case needs distinct knots. Both sides of the identity are limits of the strictly increasing case
along knots that approach the given ones from below, and `BSpline.tendsto_bspline_of_tendsto` passes
to the limit.

## Implementation notes

* The recursion is the definition because it makes sense for nondecreasing knots, coincident knots
  included, with the convention $0/0 = 0$ in the weights (`BSpline.weight`). The divided-difference
  form of Definition 8.2 of [quarteroni2000numerical] needs distinct knots, and it is the theorem
  `BSpline.bspline_eq_mul_newton_truncPow`.
* `BSpline.bspline x k i` is the B-spline $B_{i,k}$ of degree $k$, which [quarteroni2000numerical]
  writes $B_{i,k+1}$: the second index of the source is the order $k + 1$.
* The B-spline of degree $0$ is the indicator function of the half-open interval $[x_i, x_{i+1})$,
  so that the partition of unity holds at every point of $[x_k, x_{n+1})$. The closed interval in
  (8.54) of [quarteroni2000numerical] cannot be right at the shared knots.
* Knots are indexed by $\mathbb{N}$. The knots $x_{-k}, \dots, x_{n+k}$ of (8.55) of
  [quarteroni2000numerical] are shifted by $k$, so the data knots are
  $x_k = a < x_{k+1} < \dots < x_{n+k} = b$, and the $n + k$ basis B-splines are $B_{i,k}$ for
  $i < n + k$.
* Curves take values in an arbitrary real vector space `E`, and the control points are a sequence
  `P : ℕ → E`.
* The truncated power $(s - t)_+^k$ is `Quadrature.truncPow k s t`, and the divided difference
  $g[x_0, \dots, x_m]$ is `DividedDifference.newton`. The proofs use the recursion of divided
  differences, `DividedDifference.newton_succ`, and the Leibniz rule for an affine factor,
$$\bigl((\cdot - t)\, g\bigr)[x_0, \dots, x_{m+1}] = (x_0 - t)\, g[x_0, \dots, x_{m+1}] + g[x_1,
  \dots, x_{m+1}].$$
The Leibniz rule for an affine factor is proved in this file, privately, from the explicit sum that
defines `DividedDifference.newton`. It is a special case of the general Leibniz rule
`DividedDifference.newton_mul`.
-/

open Filter Polynomial Set
open scoped Topology

namespace BSpline

variable {x : ℕ → ℝ} {k i n d : ℕ} {t : ℝ}

/-- The Cox–de Boor weight
$$\omega_{i,d}(t) = \frac{t - x_i}{x_{i+d} - x_i},$$
taken to be $0$ for all $t$ when $x_{i+d} = x_i$ (de Boor's convention $0/0 = 0$). -/
noncomputable def weight (x : ℕ → ℝ) (i d : ℕ) (t : ℝ) : ℝ :=
  if x (i + d) = x i then 0 else (t - x i) / (x (i + d) - x i)

/-- **The normalized B-spline of degree $k$** on the knots $x_i, \dots, x_{i+k+1}$, defined by the
Cox–de Boor recursion ((8.54) of [quarteroni2000numerical]): $B_{i,0}$ is the indicator function
of $[x_i, x_{i+1})$, and
$$B_{i,d+1} = \omega_{i,d+1}\, B_{i,d} + (1 - \omega_{i+1,d+1})\, B_{i+1,d}.$$

The source writes $B_{i,k+1}$ for the B-spline of degree $k$, which is `BSpline.bspline x k i`.
The definition puts no condition on the knots. The results below assume that the knots are
nondecreasing or strictly increasing. -/
noncomputable def bspline (x : ℕ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, i, t => if t ∈ Ico (x i) (x (i + 1)) then 1 else 0
  | d + 1, i, t => weight x i (d + 1) t * bspline x d i t
      + (1 - weight x (i + 1) (d + 1) t) * bspline x d (i + 1) t

/-- The B-spline of degree $0$ is the indicator function of $[x_i, x_{i+1})$: $B_{i,0}(t) = 1$ for
$t \in [x_i, x_{i+1})$, and $B_{i,0}(t) = 0$ otherwise. -/
theorem bspline_zero (x : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    bspline x 0 i t = if t ∈ Ico (x i) (x (i + 1)) then 1 else 0 := rfl

/-- **The Cox–de Boor recursion** ((8.54) of [quarteroni2000numerical]): for all $d$, $i$ and $t$,
$$B_{i,d+1}(t) = \omega_{i,d+1}(t)\, B_{i,d}(t) + \bigl(1 - \omega_{i+1,d+1}(t)\bigr)\,
  B_{i+1,d}(t).$$
-/
theorem bspline_succ (x : ℕ → ℝ) (d i : ℕ) (t : ℝ) :
    bspline x (d + 1) i t = weight x i (d + 1) t * bspline x d i t
      + (1 - weight x (i + 1) (d + 1) t) * bspline x d (i + 1) t := rfl

/-- **Support**: for nondecreasing knots, $B_{i,k}(t) = 0$ for every $t \notin [x_i, x_{i+k+1})$. -/
theorem bspline_eq_zero_of_notMem (hx : Monotone x) (ht : t ∉ Ico (x i) (x (i + k + 1))) :
    bspline x k i t = 0 := by
  induction k generalizing i with
  | zero => simp [bspline_zero, ht]
  | succ d ih =>
    rw [bspline_succ]
    have h1 : t ∉ Ico (x i) (x (i + d + 1)) := fun h =>
      ht ⟨h.1, h.2.trans_le (hx (by omega))⟩
    have h2 : t ∉ Ico (x (i + 1)) (x (i + 1 + d + 1)) := fun h =>
      ht ⟨(hx (by omega)).trans h.1, by simpa [add_assoc, add_comm, add_left_comm] using h.2⟩
    rw [ih h1, ih h2, mul_zero, mul_zero, add_zero]

/-- For nondecreasing knots and $t \in [x_i, x_{i+d+1})$, the support of $B_{i,d}$, the weight
$\omega_{i,d+1}(t)$ lies in $[0, 1]$. -/
theorem weight_mem_Icc (hx : Monotone x) (ht : t ∈ Ico (x i) (x (i + d + 1))) :
    weight x i (d + 1) t ∈ Icc (0 : ℝ) 1 := by
  unfold weight
  split_ifs with h
  · exact ⟨le_rfl, zero_le_one⟩
  · have hpos : 0 < x (i + (d + 1)) - x i :=
      sub_pos.mpr (lt_of_le_of_ne (hx (by omega)) (Ne.symm h))
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hpos.le
    · rw [div_le_one hpos]
      have := ht.2
      rw [show i + d + 1 = i + (d + 1) by omega] at this
      linarith

/-- **Positivity** (§8.6.2 of [quarteroni2000numerical], where it is quoted from de Boor): for
nondecreasing knots, $B_{i,k}(t) \ge 0$ for all $i$, $k$ and $t$. -/
theorem bspline_nonneg (hx : Monotone x) : 0 ≤ bspline x k i t := by
  induction k generalizing i with
  | zero => rw [bspline_zero]; split_ifs <;> norm_num
  | succ d ih =>
    rw [bspline_succ]
    refine add_nonneg ?_ ?_
    · by_cases h : t ∈ Ico (x i) (x (i + d + 1))
      · exact mul_nonneg (weight_mem_Icc hx h).1 ih
      · rw [bspline_eq_zero_of_notMem hx h, mul_zero]
    · by_cases h : t ∈ Ico (x (i + 1)) (x (i + 1 + d + 1))
      · exact mul_nonneg (sub_nonneg.mpr (weight_mem_Icc hx h).2) ih
      · rw [bspline_eq_zero_of_notMem hx h, mul_zero]

/-- For nondecreasing knots, every point $t \in [x_0, x_{n+1})$ lies in exactly one half-open knot
interval $[x_i, x_{i+1})$ with $i \le n$, so $\sum_{i=0}^{n} B_{i,0}(t) = 1$. -/
theorem sum_bspline_zero (hx : Monotone x) (ht : t ∈ Ico (x 0) (x (n + 1))) :
    ∑ i ∈ Finset.range (n + 1), bspline x 0 i t = 1 := by
  classical
  set S : Finset ℕ := (Finset.range (n + 1)).filter fun i => x i ≤ t with hS
  have h0 : 0 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ht.1⟩
  set m := S.max' ⟨0, h0⟩ with hm
  obtain ⟨hmr, hmt⟩ := Finset.mem_filter.mp (S.max'_mem ⟨0, h0⟩)
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmr)
  have hlt : t < x (m + 1) := by
    by_contra h
    push Not at h
    have hm1 : m + 1 ≤ n := by
      by_contra h'
      have : m + 1 = n + 1 := by omega
      rw [this] at h
      exact absurd ht.2 (not_lt.mpr h)
    have := S.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩)
    omega
  have hmt' : x m ≤ t := hmt
  rw [Finset.sum_eq_single m]
  · simp [bspline_zero, hmt', hlt]
  · intro j hj hjm
    rw [bspline_zero, ite_eq_right]
    rintro ⟨hj1, hj2⟩
    rcases lt_or_gt_of_ne hjm with h | h
    · exact absurd (hmt.trans_lt hj2) (not_lt.mpr (hx (by omega)))
    · exact absurd (hj1.trans_lt hlt) (not_lt.mpr (hx (by omega)))
  · intro h
    exact absurd hmr h

/-- **Partition of unity** (§8.6.2 of [quarteroni2000numerical]): for nondecreasing knots and
$t \in [x_k, x_{n+1})$,
$$\sum_{i=0}^{n} B_{i,k}(t) = 1.$$

Each step of the recursion regroups the sum by the B-splines of degree $d$, whose coefficients
$\omega_{j,d+1} + (1 - \omega_{j,d+1})$ are $1$. The two boundary terms vanish for $t$ in this
range. -/
theorem sum_bspline (hx : Monotone x) (ht : t ∈ Ico (x k) (x (n + 1))) :
    ∑ i ∈ Finset.range (n + 1), bspline x k i t = 1 := by
  induction k with
  | zero => exact sum_bspline_zero hx ht
  | succ d ih =>
    have ht' : t ∈ Ico (x d) (x (n + 1)) := ⟨(hx (by omega)).trans ht.1, ht.2⟩
    have h0 : bspline x d 0 t = 0 :=
      bspline_eq_zero_of_notMem hx fun h => absurd h.2 (not_lt.mpr (by simpa using ht.1))
    have hN : bspline x d (n + 1) t = 0 :=
      bspline_eq_zero_of_notMem hx fun h => absurd h.1 (not_le.mpr ht.2)
    simp only [bspline_succ, Finset.sum_add_distrib]
    rw [Finset.sum_range_succ' (fun i => weight x i (d + 1) t * bspline x d i t),
      Finset.sum_range_succ (fun i => (1 - weight x (i + 1) (d + 1) t) * bspline x d (i + 1) t),
      h0, hN, mul_zero, mul_zero, add_zero, add_zero, ← Finset.sum_add_distrib]
    have : ∑ i ∈ Finset.range n, (weight x (i + 1) (d + 1) t * bspline x d (i + 1) t
        + (1 - weight x (i + 1) (d + 1) t) * bspline x d (i + 1) t)
        = ∑ i ∈ Finset.range n, bspline x d (i + 1) t :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [this, ← ih ht', Finset.sum_range_succ' (fun i => bspline x d i t), h0, add_zero]

/-- The Cox–de Boor weight as a polynomial in $t$: $(X - x_i)/(x_{i+d} - x_i)$, and $0$ when
$x_{i+d} = x_i$. -/
noncomputable def weightPoly (x : ℕ → ℝ) (i d : ℕ) : ℝ[X] :=
  if x (i + d) = x i then 0 else C (1 / (x (i + d) - x i)) * (X - C (x i))

/-- The weight polynomial evaluated at $t$ is the weight $\omega_{i,d}(t)$. -/
theorem eval_weightPoly (x : ℕ → ℝ) (i d : ℕ) (t : ℝ) :
    (weightPoly x i d).eval t = weight x i d t := by
  unfold weightPoly weight
  split_ifs <;> simp [div_eq_inv_mul]

/-- The weight polynomial has degree at most one. -/
theorem degree_weightPoly_le (x : ℕ → ℝ) (i d : ℕ) : (weightPoly x i d).degree ≤ 1 := by
  unfold weightPoly
  split_ifs
  · simp
  · exact (degree_mul_le _ _).trans (by
      calc (C (1 / (x (i + d) - x i))).degree + (X - C (x i)).degree ≤ 0 + 1 :=
            add_le_add degree_C_le (degree_X_sub_C_le _)
        _ = 1 := by simp)

/-- **Piecewise polynomial** (§8.6.2 of [quarteroni2000numerical]): for nondecreasing knots and
every $j$, there is a real polynomial $p$ of degree at most $k$ such that $B_{i,k} = p$ on the
knot interval $[x_j, x_{j+1})$. -/
theorem exists_eqOn_bspline (hx : Monotone x) (j : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn (bspline x k i) p.eval (Ico (x j) (x (j + 1))) := by
  induction k generalizing i with
  | zero =>
    refine ⟨C (if i = j then 1 else 0), degree_C_le.trans (by simp), fun t ht => ?_⟩
    change (if t ∈ Ico (x i) (x (i + 1)) then (1 : ℝ) else 0)
      = (C (if i = j then 1 else 0)).eval t
    rw [eval_C]
    by_cases hij : i = j
    · subst hij; simp [ht]
    · rw [ite_eq_right hij, ite_eq_right]
      rintro ⟨h1, h2⟩
      rcases lt_or_gt_of_ne hij with h | h
      · exact absurd (ht.1.trans_lt h2) (not_lt.mpr (hx (by omega)))
      · exact absurd (h1.trans_lt ht.2) (not_lt.mpr (hx (by omega)))
  | succ d ih =>
    obtain ⟨p, hpd, hpe⟩ := ih (i := i)
    obtain ⟨q, hqd, hqe⟩ := ih (i := i + 1)
    refine ⟨weightPoly x i (d + 1) * p + (1 - weightPoly x (i + 1) (d + 1)) * q, ?_, fun t ht => ?_⟩
    · refine (degree_add_le _ _).trans (max_le ?_ ?_)
      · refine (degree_mul_le _ _).trans ?_
        calc (weightPoly x i (d + 1)).degree + p.degree ≤ 1 + d :=
              add_le_add (degree_weightPoly_le _ _ _) hpd
          _ = ((d + 1 : ℕ) : WithBot ℕ) := by push_cast; ring
      · refine (degree_mul_le _ _).trans ?_
        calc (1 - weightPoly x (i + 1) (d + 1)).degree + q.degree ≤ 1 + d := by
              refine add_le_add ((degree_sub_le _ _).trans (max_le ?_ (degree_weightPoly_le _ _ _)))
                hqd
              exact degree_one_le.trans zero_le_one
          _ = ((d + 1 : ℕ) : WithBot ℕ) := by push_cast; ring
    · simp only [bspline_succ, eval_add, eval_mul, eval_sub, eval_one, eval_weightPoly, hpe ht,
        hqe ht]

/-- **Positivity on the open support**: for strictly increasing knots, $B_{i,k}(t) > 0$ for every
$t \in (x_i, x_{i+k+1})$.

The proof is by induction on $k$ through the Cox–de Boor recursion: one of the two terms has a
positive weight and a positive B-spline of degree $k - 1$, and the other term is nonnegative. -/
theorem bspline_pos (hx : StrictMono x) (ht : t ∈ Ioo (x i) (x (i + k + 1))) :
    0 < bspline x k i t := by
  induction k generalizing i with
  | zero =>
    rw [bspline_zero, ite_eq_left (Ioo_subset_Ico_self ht)]
    exact one_pos
  | succ d ih =>
    rw [bspline_succ]
    have hw1 : 0 ≤ weight x i (d + 1) t := by
      unfold weight
      split_ifs with h
      · exact le_rfl
      · exact div_nonneg (sub_nonneg.mpr ht.1.le)
          (sub_nonneg.mpr (hx.monotone (Nat.le_add_right _ _)))
    have hw2 : 0 ≤ 1 - weight x (i + 1) (d + 1) t := by
      unfold weight
      split_ifs with h
      · norm_num
      · have hlt : x (i + 1) < x (i + 1 + (d + 1)) := hx (by omega)
        rw [sub_nonneg, div_le_one (sub_pos.mpr hlt)]
        have : t < x (i + 1 + (d + 1)) := by
          simpa [add_assoc, add_comm, add_left_comm] using ht.2
        linarith
    rcases lt_or_ge t (x (i + d + 1)) with h1 | h1
    · -- the first term is positive
      have hB : 0 < bspline x d i t := ih ⟨ht.1, h1⟩
      have hw : 0 < weight x i (d + 1) t := by
        unfold weight
        have hlt : x i < x (i + (d + 1)) := hx (by omega)
        rw [ite_eq_right hlt.ne']
        exact div_pos (sub_pos.mpr ht.1) (sub_pos.mpr hlt)
      have := mul_nonneg hw2 (bspline_nonneg (k := d) (i := i + 1) (t := t) hx.monotone)
      nlinarith [mul_pos hw hB]
    · -- the second term is positive
      have hB : 0 < bspline x d (i + 1) t := by
        rcases Nat.eq_zero_or_pos d with rfl | hd
        · rw [bspline_zero, ite_eq_left]
          · exact one_pos
          · refine ⟨by simpa using h1, ?_⟩
            simpa [add_assoc, add_comm, add_left_comm] using ht.2
        · refine ih ⟨(hx (by omega : i + 1 < i + d + 1)).trans_le h1, ?_⟩
          simpa [add_assoc, add_comm, add_left_comm] using ht.2
      have hw : 0 < 1 - weight x (i + 1) (d + 1) t := by
        unfold weight
        have hlt : x (i + 1) < x (i + 1 + (d + 1)) := hx (by omega)
        rw [ite_eq_right hlt.ne', sub_pos, div_lt_one (sub_pos.mpr hlt)]
        have : t < x (i + 1 + (d + 1)) := by
          simpa [add_assoc, add_comm, add_left_comm] using ht.2
        linarith
      have := mul_nonneg hw1 (bspline_nonneg (k := d) (i := i) (t := t) hx.monotone)
      nlinarith [mul_pos hw hB]

/-!
### Divided differences of truncated powers

The recursion for divided differences is `DividedDifference.newton_succ`. The Leibniz rule for an
affine factor is proved here from the explicit sum that defines `DividedDifference.newton`. It is a
special case of the general Leibniz rule `DividedDifference.newton_mul`.
-/

section DividedDifference

open DividedDifference

/-- The weight $\prod_{j \neq i} (v_i - v_j)$ of the node $v_i$ in the Newton divided difference. -/
private def wt {m : ℕ} (v : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (v i - v j)

private theorem wt_ne_zero {m : ℕ} {v : Fin (m + 1) → ℝ} (hv : Function.Injective v)
    (i : Fin (m + 1)) : wt v i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hj =>
    sub_ne_zero.mpr fun h => Finset.ne_of_mem_erase hj (hv h).symm

private theorem newton_eq_sum_div {m : ℕ} (f : ℝ → ℝ) (v : Fin (m + 1) → ℝ) :
    newton f v = ∑ i, f (v i) / wt v i := rfl

private theorem prod_erase_eq_prod_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℝ)
    (a : ι) : ∏ j ∈ Finset.univ.erase a, g j = ∏ j, if j = a then 1 else g j := by
  rw [← Finset.prod_erase_mul Finset.univ (fun j => if j = a then 1 else g j) (Finset.mem_univ a),
    ite_eq_left rfl, mul_one]
  exact Finset.prod_congr rfl fun _ hj => by rw [ite_eq_right (Finset.ne_of_mem_erase hj)]

/-- The weight of the node $v_{i+1}$ is $(v_{i+1} - v_0)$ times its weight in the node sequence
$v_1, \dots, v_{m+1}$. -/
private theorem wt_succ {m : ℕ} (v : Fin (m + 2) → ℝ) (i : Fin (m + 1)) :
    wt v i.succ = (v i.succ - v 0) * wt (Fin.tail v) i := by
  simp only [wt, prod_erase_eq_prod_ite, Fin.prod_univ_succ, Fin.succ_inj, Fin.tail,
    (Fin.succ_ne_zero i).symm, ↓reduceIte]

/-- The weight of the node $v_i$, for $i \le m$, is $(v_i - v_{m+1})$ times its weight in the node
sequence $v_0, \dots, v_m$. -/
private theorem wt_castSucc {m : ℕ} (v : Fin (m + 2) → ℝ) (i : Fin (m + 1)) :
    wt v i.castSucc = (v i.castSucc - v (Fin.last (m + 1))) * wt (Fin.init v) i := by
  rw [wt, wt, prod_erase_eq_prod_ite, prod_erase_eq_prod_ite,
    Fin.prod_univ_castSucc
      (fun j : Fin (m + 2) => if j = i.castSucc then 1 else v i.castSucc - v j),
    ite_eq_right (Fin.castSucc_lt_last i).ne']
  simp only [Fin.castSucc_inj, Fin.init]
  ring

-- TODO(NewtonForm): the Leibniz rule `DividedDifference.newton_mul` with an affine first factor.
/-- **The Leibniz rule for an affine factor**: for distinct nodes $v_0, \dots, v_{m+1}$,
$\bigl((\cdot - t)\, g\bigr)[v_0, \dots, v_{m+1}] = (v_0 - t)\, g[v_0, \dots, v_{m+1}] + g[v_1,
\dots, v_{m+1}]$. -/
private theorem newton_sub_mul {m : ℕ} (g : ℝ → ℝ) (t : ℝ) {v : Fin (m + 2) → ℝ}
    (hv : Function.Injective v) :
    newton (fun s => (s - t) * g s) v = (v 0 - t) * newton g v + newton g (Fin.tail v) := by
  rw [newton_eq_sum_div, newton_eq_sum_div, newton_eq_sum_div, Finset.mul_sum]
  have htail : ∑ i : Fin (m + 1), g (Fin.tail v i) / wt (Fin.tail v) i
      = ∑ j : Fin (m + 2), g (v j) * (v j - v 0) / wt v j := by
    rw [Fin.sum_univ_succ (fun j : Fin (m + 2) => g (v j) * (v j - v 0) / wt v j)]
    simp only [sub_self, mul_zero, zero_div, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wt_succ, Fin.tail]
    have := wt_ne_zero hv i.succ
    have h2 : v i.succ - v 0 ≠ 0 :=
      sub_ne_zero.mpr fun h => absurd (hv h) (Fin.succ_ne_zero i)
    rw [wt_succ] at this
    have h3 : wt (Fin.tail v) i ≠ 0 := right_ne_zero_of_mul this
    field_simp
  rw [htail, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := wt_ne_zero hv j
  field_simp
  ring

end DividedDifference

/-- The truncated power of degree $k + 1$ factors as $(s - t)_+^{k+1} = (s - t)\, (s - t)_+^k$. -/
theorem truncPow_succ (k : ℕ) (s t : ℝ) :
    Quadrature.truncPow (k + 1) s t = (s - t) * Quadrature.truncPow k s t := by
  unfold Quadrature.truncPow
  split_ifs <;> ring

/-- **The divided-difference form of the B-spline** ((8.51) of [quarteroni2000numerical]): the value
at $t$ of
$$(x_{i+k+1} - x_i)\, g[x_i, \dots, x_{i+k+1}], \qquad g(s) = (s - t)_+^k.$$
For $k \ge 1$ and distinct knots it coincides with $B_{i,k}(t)$ (`BSpline.nform_eq_bspline`).
For $k = 0$ and $x_i \le x_{i+1}$ it is the indicator function of the half-open interval
$(x_i, x_{i+1}]$, which differs from $B_{i,0}$ at the knots.

The truncated power $(s - t)_+^k$ is `Quadrature.truncPow k s t`, and the divided difference is
`DividedDifference.newton`. The definition puts no condition on the knots. -/
noncomputable def nform (x : ℕ → ℝ) (k i : ℕ) (t : ℝ) : ℝ :=
  (x (i + k + 1) - x i) *
    DividedDifference.newton (fun s => Quadrature.truncPow k s t) fun j : Fin (k + 2) => x (i + j)

/-- For strictly increasing knots, the node sequence $x_i, \dots, x_{i+k+1}$ is injective. -/
theorem injective_nodes (hx : StrictMono x) (k i : ℕ) :
    Function.Injective fun j : Fin (k + 2) => x (i + j) := fun _ _ h =>
  Fin.ext (by simpa using hx.injective h)

/-- The Newton divided difference at the two nodes $x_i$ and $x_{i+1}$ is $g(x_i)/(x_i - x_{i+1}) +
g(x_{i+1})/(x_{i+1} - x_i)$. -/
theorem newton_two (g : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) :
    DividedDifference.newton g (fun j : Fin (0 + 2) => x (i + j))
      = g (x i) / (x i - x (i + 1)) + g (x (i + 1)) / (x (i + 1) - x i) := by
  simp only [DividedDifference.newton, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one]
  rw [show (Finset.univ.erase (0 : Fin (0 + 2))) = {1} from rfl,
    show (Finset.univ.erase (1 : Fin (0 + 2))) = {0} from rfl]
  simp

/-- For strictly increasing knots, the divided-difference form of degree $0$ is the indicator
function of $(x_i, x_{i+1}]$. -/
theorem nform_zero (hx : StrictMono x) (i : ℕ) (t : ℝ) :
    nform x 0 i t = if t ∈ Ioc (x i) (x (i + 1)) then 1 else 0 := by
  have hne : x (i + 1) - x i ≠ 0 := sub_ne_zero.mpr (hx (Nat.lt_succ_self i)).ne'
  have hne' : x i - x (i + 1) ≠ 0 := sub_ne_zero.mpr (hx (Nat.lt_succ_self i)).ne
  rw [nform, newton_two]
  simp only [add_zero, Quadrature.truncPow, pow_zero]
  by_cases h1 : t ≤ x i
  · have h2 : t ≤ x (i + 1) := h1.trans (hx (Nat.lt_succ_self i)).le
    rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right (fun h => absurd h.1 (not_lt.mpr h1))]
    field_simp
    ring
  · by_cases h2 : t ≤ x (i + 1)
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left ⟨lt_of_not_ge h1, h2⟩]
      field_simp
      ring
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (fun h => h2 h.2)]
      simp

/-- The node sequence $x_i, \dots, x_{i+d+2}$ without its first node is the node sequence
$x_{i+1}, \dots, x_{i+d+2}$. -/
theorem tail_nodes (x : ℕ → ℝ) (d i : ℕ) :
    Fin.tail (fun j : Fin (d + 3) => x (i + j)) = fun j : Fin (d + 2) => x (i + 1 + j) :=
  funext fun j => by simp only [Fin.tail, Fin.val_succ]; congr 1; omega

/-- The node sequence $x_i, \dots, x_{i+d+2}$ without its last node is the node sequence
$x_i, \dots, x_{i+d+1}$. -/
theorem init_nodes (x : ℕ → ℝ) (d i : ℕ) :
    Fin.init (fun j : Fin (d + 3) => x (i + j)) = fun j : Fin (d + 2) => x (i + j) :=
  funext fun j => by simp only [Fin.init, Fin.val_castSucc]

/-- **The Cox–de Boor recursion for the divided-difference form**: for strictly increasing knots,
the divided-difference form $N_{i,d}$ (`BSpline.nform x d i`) satisfies the recursion of the
B-splines,
$$N_{i,d+1}(t) = \omega_{i,d+1}(t)\, N_{i,d}(t) + \bigl(1 - \omega_{i+1,d+1}(t)\bigr)\,
  N_{i+1,d}(t).$$

This is (13)–(14) of chapter IX of de Boor, *A Practical Guide to Splines*. The proof uses
$(s - t)_+^{d+1} = (s - t)\,(s - t)_+^d$, the Leibniz rule for the affine factor and the
recursion for divided differences. -/
theorem nform_succ (hx : StrictMono x) (d i : ℕ) (t : ℝ) :
    nform x (d + 1) i t = weight x i (d + 1) t * nform x d i t
      + (1 - weight x (i + 1) (d + 1) t) * nform x d (i + 1) t := by
  have hv := injective_nodes hx (d + 1) i
  have hg : (fun s => Quadrature.truncPow (d + 1) s t)
      = fun s => (s - t) * Quadrature.truncPow d s t := funext fun s => truncPow_succ d s t
  have hrec := DividedDifference.newton_succ (fun s => Quadrature.truncPow d s t) hv
  have hleib := newton_sub_mul (fun s => Quadrature.truncPow d s t) t hv
  rw [tail_nodes, init_nodes] at hrec
  rw [tail_nodes] at hleib
  simp only [Fin.val_zero, add_zero, Fin.val_last] at hrec hleib
  have h1 : x (i + (d + 1 + 1)) - x i ≠ 0 :=
    sub_ne_zero.mpr (hx (by omega)).ne'
  have h2 : x (i + (d + 1)) - x i ≠ 0 := sub_ne_zero.mpr (hx (by omega)).ne'
  have h3 : x (i + 1 + (d + 1)) - x (i + 1) ≠ 0 := sub_ne_zero.mpr (hx (by omega)).ne'
  have h2' : ¬ x (i + (d + 1)) = x i := fun h => h2 (sub_eq_zero.mpr h)
  have h3' : ¬ x (i + 1 + (d + 1)) = x (i + 1) := fun h => h3 (sub_eq_zero.mpr h)
  simp only [nform, weight, ite_eq_right h2', ite_eq_right h3', hg, hleib, hrec,
    show i + (d + 1) + 1 = i + (d + 1 + 1) by omega, show i + d + 1 = i + (d + 1) by omega,
    show i + 1 + d + 1 = i + 1 + (d + 1) by omega]
  field_simp
  ring_nf

/-- For strictly increasing knots, the divided-difference form and the B-spline agree in degree $1$:
both are the hat function of the knots $x_i < x_{i+1} < x_{i+2}$. -/
theorem nform_one (hx : StrictMono x) (i : ℕ) (t : ℝ) : nform x 1 i t = bspline x 1 i t := by
  rw [nform_succ hx, bspline_succ, nform_zero hx, nform_zero hx, bspline_zero, bspline_zero]
  have h01 : x i < x (i + 1) := hx (by omega)
  have h12 : x (i + 1) < x (i + 1 + 1) := hx (by omega)
  have hw1 : weight x i 1 t = (t - x i) / (x (i + 1) - x i) := by
    simp [weight, h01.ne']
  have hw2 : weight x (i + 1) 1 t = (t - x (i + 1)) / (x (i + 1 + 1) - x (i + 1)) := by
    simp [weight, h12.ne']
  rw [hw1, hw2]
  simp only [mem_Ioc, mem_Ico]
  rcases lt_trichotomy t (x i) with h | rfl | h
  · simp [not_le.mpr h, not_lt.mpr h.le, not_le.mpr (h.trans h01), not_lt.mpr (h.trans h01).le]
  · simp [h01, not_lt.mpr h01.le]
  rcases lt_trichotomy t (x (i + 1)) with h' | rfl | h'
  · simp [h, h.le, h', h'.le, not_le.mpr h', not_lt.mpr h'.le]
  · simp [h, h12, div_self (sub_ne_zero.mpr h01.ne')]
  rcases lt_trichotomy t (x (i + 1 + 1)) with h'' | rfl | h''
  · simp [h, h', h'.le, h'', h''.le, not_le.mpr h', not_lt.mpr h'.le]
  · simp [h, h', not_le.mpr h', not_lt.mpr h'.le, div_self (sub_ne_zero.mpr h12.ne')]
  · simp [h, h', not_le.mpr h', not_lt.mpr h'.le, not_le.mpr h'', not_lt.mpr h''.le]

/-- For strictly increasing knots and $k \ge 1$, the B-spline $B_{i,k}$ of the Cox–de Boor recursion
is the divided-difference form: $B_{i,k}(t) = (x_{i+k+1} - x_i)\, g_t[x_i, \dots, x_{i+k+1}]$
with $g_t(s) = (s - t)_+^k$, for every $t$. This is Definition 8.2 of [quarteroni2000numerical],
stated as a theorem. -/
theorem nform_eq_bspline (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) :
    nform x k i = bspline x k i := by
  induction k, hk using Nat.le_induction generalizing i with
  | base => exact funext fun t => nform_one hx i t
  | succ d hd ih =>
    funext t
    rw [nform_succ hx, bspline_succ, ih i, ih (i + 1)]

/-- **The B-spline as a divided difference of a truncated power**: for strictly increasing knots,
$k \ge 1$, every $i$ and every $t \in \mathbb{R}$,
$$B_{i,k}(t) = (x_{i+k+1} - x_i)\, g[x_i, \dots, x_{i+k+1}], \qquad g(s) = (s - t)_+^k.$$
This is Definition 8.2 of [quarteroni2000numerical], with (8.51)–(8.52), where it is the
definition of the B-spline. -/
theorem bspline_eq_mul_newton_truncPow (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) (t : ℝ) :
    bspline x k i t = (x (i + k + 1) - x i) *
      DividedDifference.newton (fun s => Quadrature.truncPow k s t)
        (fun j : Fin (k + 2) => x (i + j)) :=
  (congrFun (nform_eq_bspline hx hk i) t).symm

/-- **The explicit form of the B-spline** ((8.53) of [quarteroni2000numerical]): for strictly
increasing knots, $k \ge 1$, every $i$ and every $t \in \mathbb{R}$,
$$B_{i,k}(t) = (x_{i+k+1} - x_i) \sum_{j=0}^{k+1} \frac{(x_{i+j} - t)_+^k}{\prod_{l \neq j}
  (x_{i+j} - x_{i+l})},$$
where the product is over $l \in \{0, \dots, k + 1\}$ with $l \neq j$. -/
theorem bspline_eq_sum_truncPow (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) (t : ℝ) :
    bspline x k i t = (x (i + k + 1) - x i) * ∑ j : Fin (k + 2),
      Quadrature.truncPow k (x (i + j)) t / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l)) :=
  bspline_eq_mul_newton_truncPow hx hk i t

/-! ### Smoothness and membership in the spline space -/

/-- For $c \in \mathbb{R}$ and $k \ge 1$, the function $t \mapsto (c - t)_+^k$ is of class
$C^{k-1}$. -/
theorem contDiff_truncPow_flip (c : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) fun t => Quadrature.truncPow k c t := by
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 1 := ⟨k - 1, by omega⟩
  have : (fun t => Quadrature.truncPow (s + 1) c t) = fun t => max (-t - -c) 0 ^ (s + 1) := by
    funext t
    unfold Quadrature.truncPow
    split_ifs with h
    · rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith), zero_pow (Nat.succ_ne_zero s)]
  rw [this, Nat.add_sub_cancel]
  exact (Spline.contDiff_max_sub_pow (-c) s).comp contDiff_neg

/-- **Smoothness at simple knots** (§8.6.2 of [quarteroni2000numerical]): for strictly increasing
knots and $k \ge 1$, $B_{i,k}$ is of class $C^{k-1}$ on $\mathbb{R}$.

The proof writes $B_{i,k}$ as a linear combination of the functions $t \mapsto (x_j - t)_+^k$. -/
theorem contDiff_bspline (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) :
    ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (bspline x k i) := by
  have : bspline x k i = fun t => (x (i + k + 1) - x i) * ∑ j : Fin (k + 2),
      Quadrature.truncPow k (x (i + j)) t / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l)) :=
    funext fun t => bspline_eq_sum_truncPow hx hk i t
  rw [this]
  exact contDiff_const.mul (ContDiff.sum fun j _ => (contDiff_truncPow_flip _ hk).div_const _)

/-- For strictly increasing knots and $k \ge 1$, on each closed knot interval $[x_j, x_{j+1}]$ the
B-spline $B_{i,k}$ agrees with a real polynomial of degree at most $k$. This extends
`BSpline.exists_eqOn_bspline` to the right endpoint by continuity. -/
theorem exists_eqOn_Icc_bspline (hx : StrictMono x) (hk : 1 ≤ k) (i j : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn (bspline x k i) p.eval (Icc (x j) (x (j + 1))) := by
  obtain ⟨p, hpd, hpe⟩ := exists_eqOn_bspline (k := k) (i := i) hx.monotone j
  refine ⟨p, hpd, hpe.of_subset_closure (contDiff_bspline hx hk i).continuous.continuousOn
    p.continuous.continuousOn Ico_subset_Icc_self ?_⟩
  rw [closure_Ico (hx (Nat.lt_succ_self j)).ne]

/-- **A B-spline is a spline** (§8.6.2 of [quarteroni2000numerical]): let the knots be strictly
increasing, let $k \ge 1$, and let $a, b \in \mathbb{R}$ and $n \in \mathbb{N}$. The restriction
of $B_{i,k}$ to $[a, b]$ lies in the spline space $S_k^{k-1}$ of degree $k$ and smoothness
$C^{k-1}$ on $[a, b]$ with the nodes $x_k, x_{k+1}, \dots, x_{n+k}$.

The intended case is that of the data knots $x_k = a < \dots < x_{n+k} = b$, but the statement
holds for all $a$ and $b$, because $B_{i,k}$ is of class $C^{k-1}$ on $\mathbb{R}$ and agrees
with a polynomial on every closed knot interval. The spline space is `Spline.splineSpace a b n
(fun j => x (j + k)) k (k - 1)`. -/
theorem bspline_mem_splineSpace {a b : ℝ} (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) :
    (ContinuousMap.mk _ (contDiff_bspline hx hk i).continuous).restrict (Icc a b) ∈
      Spline.splineSpace a b n (fun j => x (j + k)) k (k - 1) := by
  refine ⟨bspline x k i, (contDiff_bspline hx hk i).contDiffOn, fun _ => rfl, fun j hj => ?_⟩
  obtain ⟨p, hpd, hpe⟩ := exists_eqOn_Icc_bspline hx hk i (j + k)
  refine ⟨p, hpd, ?_⟩
  change EqOn _ _ (Icc (x (j + k)) (x (j + 1 + k)))
  rw [show j + 1 + k = j + k + 1 by omega]
  exact hpe

/-! ### The derivative recursion and linear independence -/

/-- For $c \in \mathbb{R}$ and $t \neq c$, the function $t \mapsto (c - t)_+^{k+1}$ has the
derivative $-(k + 1)\,(c - t)_+^k$ at $t$. -/
theorem hasDerivAt_truncPow_flip (c : ℝ) (k : ℕ) {t : ℝ} (ht : t ≠ c) :
    HasDerivAt (fun t => Quadrature.truncPow (k + 1) c t)
      (-((k : ℝ) + 1) * Quadrature.truncPow k c t) t := by
  rcases lt_or_gt_of_ne ht with h | h
  · have hev : (fun t => Quadrature.truncPow (k + 1) c t) =ᶠ[𝓝 t] fun t => (c - t) ^ (k + 1) := by
      filter_upwards [Iio_mem_nhds h] with u (hu : u < c)
      simp [Quadrature.truncPow, hu.le]
    have : Quadrature.truncPow k c t = (c - t) ^ k := by simp [Quadrature.truncPow, h.le]
    rw [this]
    have hd := (hasDerivAt_pow (k + 1) (c - t)).comp t ((hasDerivAt_id t).const_sub c)
    simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, mul_neg, mul_one] at hd
    exact hd.congr_of_eventuallyEq hev |>.congr_deriv (by ring)
  · have hev : (fun t => Quadrature.truncPow (k + 1) c t) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with u (hu : c < u)
      simp [Quadrature.truncPow, not_le.mpr hu]
    have : Quadrature.truncPow k c t = 0 := by simp [Quadrature.truncPow, not_le.mpr h]
    rw [this, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev

/-- For strictly increasing knots and a point $t$ that is not a knot, the divided-difference form of
every degree $k$ at $t$ equals $B_{i,k}(t)$, the case $k = 0$ included. -/
theorem nform_eq_bspline_of_ne (hx : StrictMono x) (ht : ∀ m, t ≠ x m) (k i : ℕ) :
    nform x k i t = bspline x k i t := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [nform_zero hx, bspline_zero]
    have h1 := ht i
    have h2 := ht (i + 1)
    simp only [mem_Ioc, mem_Ico]
    congr 1
    simp only [eq_iff_iff]
    constructor
    · rintro ⟨a, b⟩; exact ⟨a.le, lt_of_le_of_ne b h2⟩
    · rintro ⟨a, b⟩; exact ⟨lt_of_le_of_ne a (Ne.symm h1), b.le⟩
  · exact congrFun (nform_eq_bspline hx hk i) t

/-- **The derivative of a B-spline**: for strictly increasing knots and a point $t$ that is not a
knot, $B_{i,k+1}$ is differentiable at $t$ with
$$B_{i,k+1}'(t) = (k + 1) \Bigl(\frac{B_{i,k}(t)}{x_{i+k+1} - x_i} -
  \frac{B_{i+1,k}(t)}{x_{i+k+2} - x_{i+1}}\Bigr).$$
This is (12) of chapter X of de Boor, *A Practical Guide to Splines*. -/
theorem hasDerivAt_bspline (hx : StrictMono x) (ht : ∀ m, t ≠ x m) (k i : ℕ) :
    HasDerivAt (bspline x (k + 1) i)
      (((k : ℝ) + 1) * (bspline x k i t / (x (i + k + 1) - x i)
        - bspline x k (i + 1) t / (x (i + 1 + k + 1) - x (i + 1)))) t := by
  rw [← nform_eq_bspline hx (by omega) i, ← nform_eq_bspline_of_ne hx ht k i,
    ← nform_eq_bspline_of_ne hx ht k (i + 1)]
  have hv := injective_nodes hx (k + 1) i
  have hrec := DividedDifference.newton_succ (fun s => Quadrature.truncPow k s t) hv
  rw [tail_nodes, init_nodes] at hrec
  simp only [Fin.val_zero, add_zero, Fin.val_last] at hrec
  have h1 : x (i + (k + 1 + 1)) - x i ≠ 0 := sub_ne_zero.mpr (hx (by omega)).ne'
  have h2 : x (i + k + 1) - x i ≠ 0 := sub_ne_zero.mpr (hx (by omega)).ne'
  have h3 : x (i + 1 + k + 1) - x (i + 1) ≠ 0 := sub_ne_zero.mpr (hx (by omega)).ne'
  -- differentiate the explicit sum termwise
  have hsum : HasDerivAt (fun t => (x (i + (k + 1) + 1) - x i) * ∑ j : Fin (k + 1 + 2),
        Quadrature.truncPow (k + 1) (x (i + j)) t
          / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l)))
      ((x (i + (k + 1) + 1) - x i) * ∑ j : Fin (k + 1 + 2),
        (-((k : ℝ) + 1) * Quadrature.truncPow k (x (i + j)) t)
          / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l))) t := by
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun (j : Fin (k + 1 + 2)) t => Quadrature.truncPow (k + 1) (x (i + j)) t
        / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l)))
      (A' := fun j => (-((k : ℝ) + 1) * Quadrature.truncPow k (x (i + j)) t)
        / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l))) fun j _ => ?_)
    exact (hasDerivAt_truncPow_flip (x (i + j)) k (ht _)).div_const _
  have hfun : nform x (k + 1) i = fun t => (x (i + (k + 1) + 1) - x i) * ∑ j : Fin (k + 1 + 2),
      Quadrature.truncPow (k + 1) (x (i + j)) t
        / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l)) := rfl
  rw [hfun]
  refine hsum.congr_deriv ?_
  have : ∑ j : Fin (k + 1 + 2), (-((k : ℝ) + 1) * Quadrature.truncPow k (x (i + j)) t)
      / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l))
      = -((k : ℝ) + 1) * DividedDifference.newton (fun s => Quadrature.truncPow k s t)
          (fun j : Fin (k + 1 + 2) => x (i + j)) := by
    rw [DividedDifference.newton, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hrec, nform, nform, show i + (k + 1) + 1 = i + (k + 1 + 1) by omega]
  field_simp
  ring

/-- For strictly increasing knots, the points of the open knot interval $(x_j, x_{j+1})$ are not
knots. -/
theorem ne_of_mem_Ioo (hx : StrictMono x) {j : ℕ} (ht : t ∈ Ioo (x j) (x (j + 1))) (m : ℕ) :
    t ≠ x m := by
  intro h
  rcases le_or_gt m j with hm | hm
  · exact absurd (h ▸ ht.1) (not_lt.mpr (hx.monotone hm))
  · exact absurd (h ▸ ht.2) (not_lt.mpr (hx.monotone hm))

/-- For strictly increasing knots, the B-spline $B_{i,k}$ with $i + k + 1 \le j$ vanishes on
$(x_j, x_{j+1})$. -/
theorem bspline_eq_zero_of_add_le (hx : StrictMono x) {j : ℕ} (ht : t ∈ Ioo (x j) (x (j + 1)))
    (hi : i + k + 1 ≤ j) : bspline x k i t = 0 :=
  bspline_eq_zero_of_notMem hx.monotone fun h =>
    absurd h.2 (not_lt.mpr ((hx.monotone hi).trans ht.1.le))

/-- For strictly increasing knots, the B-spline $B_{i,k}$ with $j < i$ vanishes on $(x_j, x_{j+1})$.
-/
theorem bspline_eq_zero_of_lt (hx : StrictMono x) {j : ℕ} (ht : t ∈ Ioo (x j) (x (j + 1)))
    (hi : j < i) : bspline x k i t = 0 :=
  bspline_eq_zero_of_notMem hx.monotone fun h =>
    absurd h.1 (not_le.mpr (ht.2.trans_le (hx.monotone hi)))

/-- **Local linear independence**: let the knots be strictly increasing, and let $k \le j$. If a
combination $\sum_{i=0}^{j} c_i B_{i,k}$ vanishes on the knot interval $(x_j, x_{j+1})$, then
the coefficients $c_{j-k}, \dots, c_j$ of the $k + 1$ B-splines that do not vanish on that
interval are $0$.

This is Theorem IX.1 of de Boor, *A Practical Guide to Splines*. The proof is by induction on
$k$ through the derivative recursion: the derivative of the combination is a combination of
B-splines of one degree less, with coefficients proportional to $c_i - c_{i-1}$, so all the
coefficients are equal, and the partition of unity forces them to vanish. -/
theorem eq_zero_of_sum_mul_bspline_eq_zero (hx : StrictMono x) :
    ∀ (k j : ℕ), k ≤ j → ∀ c : ℕ → ℝ,
      (∀ t ∈ Ioo (x j) (x (j + 1)), ∑ i ∈ Finset.range (j + 1), c i * bspline x k i t = 0) →
      ∀ i, j - k ≤ i → i ≤ j → c i = 0 := by
  intro k
  induction k with
  | zero =>
    intro j _ c hsum i hi1 hi2
    obtain rfl : j = i := by omega
    have hmem : (x j + x (j + 1)) / 2 ∈ Ioo (x j) (x (j + 1)) := by
      have := hx (Nat.lt_succ_self j); constructor <;> linarith
    have := hsum _ hmem
    rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => ?_] at this
    · rw [zero_add, bspline_zero, ite_eq_left ⟨hmem.1.le, hmem.2⟩, mul_one] at this
      exact this
    · rw [bspline_eq_zero_of_add_le hx hmem (by simpa using Finset.mem_range.mp hi), mul_zero]
  | succ k ih =>
    intro j hkj c hsum
    have hkj' : k ≤ j := by omega
    have hIoo : ∀ t ∈ Ioo (x j) (x (j + 1)), Ioo (x j) (x (j + 1)) ∈ 𝓝 t := fun t ht =>
      Ioo_mem_nhds ht.1 ht.2
    -- the coefficient of `B_{i,k}` in the derivative
    set d : ℕ → ℝ := fun i => x (i + k + 1) - x i with hd
    have hdne : ∀ i, d i ≠ 0 := fun i => sub_ne_zero.mpr (hx (by omega)).ne'
    set c' : ℕ → ℝ := fun i => if i = 0 then 0 else c (i - 1) with hc'
    -- the derivative of the vanishing combination vanishes
    have hder : ∀ t ∈ Ioo (x j) (x (j + 1)),
        ∑ i ∈ Finset.range (j + 1), (c i - c' i) / d i * bspline x k i t = 0 := by
      intro t ht
      have hne := ne_of_mem_Ioo hx ht
      have h1 : HasDerivAt (fun t => ∑ i ∈ Finset.range (j + 1), c i * bspline x (k + 1) i t)
          (∑ i ∈ Finset.range (j + 1), c i * (((k : ℝ) + 1) * (bspline x k i t / d i
            - bspline x k (i + 1) t / d (i + 1)))) t :=
        HasDerivAt.fun_sum fun i _ => (hasDerivAt_bspline hx hne k i).const_mul (c i)
      have h2 : HasDerivAt (fun t => ∑ i ∈ Finset.range (j + 1), c i * bspline x (k + 1) i t) 0 t :=
        (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
          (Filter.eventually_of_mem (hIoo t ht) fun u hu => hsum u hu)
      have h3 := h1.unique h2
      -- regroup: `∑ c_i B_{i+1,k}/d_{i+1} = ∑ c'_i B_{i,k}/d_i` on the interval
      have hshift : ∑ i ∈ Finset.range (j + 1), c i * (bspline x k (i + 1) t / d (i + 1))
          = ∑ i ∈ Finset.range (j + 1), c' i * (bspline x k i t / d i) := by
        rw [Finset.sum_range_succ' (fun i => c' i * (bspline x k i t / d i)),
          show c' 0 * (bspline x k 0 t / d 0) = 0 by simp [hc'], add_zero,
          Finset.sum_range_succ (fun i => c i * (bspline x k (i + 1) t / d (i + 1))),
          bspline_eq_zero_of_lt hx ht (by omega), zero_div, mul_zero, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [hc']
      have h4 : ∑ i ∈ Finset.range (j + 1), c i * (((k : ℝ) + 1) * (bspline x k i t / d i
          - bspline x k (i + 1) t / d (i + 1)))
          = ((k : ℝ) + 1) * ∑ i ∈ Finset.range (j + 1), (c i - c' i) / d i * bspline x k i t := by
        rw [Finset.mul_sum]
        have : ∀ i, c i * (((k : ℝ) + 1)
              * (bspline x k i t / d i - bspline x k (i + 1) t / d (i + 1)))
            = ((k : ℝ) + 1) * (c i * (bspline x k i t / d i)
              - c i * (bspline x k (i + 1) t / d (i + 1))) :=
          fun i => by ring
        simp_rw [this, ← Finset.mul_sum, Finset.sum_sub_distrib, hshift, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have := hdne i
        field_simp
      rw [h4] at h3
      exact (mul_eq_zero.mp h3).resolve_left (by positivity)
    have hcoef := ih j hkj' _ hder
    -- hence the coefficients `c_i`, `j - k - 1 ≤ i ≤ j`, are all equal
    have heq : ∀ i, j - (k + 1) ≤ i → i ≤ j → c i = c (j - (k + 1)) := by
      intro i hi1 hi2
      induction i with
      | zero =>
        have : j - (k + 1) = 0 := by omega
        rw [this]
      | succ i ihi =>
        rcases Nat.lt_or_ge i (j - (k + 1)) with h | h
        · have : j - (k + 1) = i + 1 := by omega
          rw [this]
        · have h0 := hcoef (i + 1) (by omega) hi2
          rw [div_eq_zero_iff, or_iff_left (hdne _), sub_eq_zero] at h0
          rw [h0, hc']
          simp only [add_tsub_cancel_right, Nat.succ_ne_zero, ↓reduceIte]
          exact ihi h (by omega)
    -- the vanishing combination is `c_{j-k-1}` times the partition of unity
    have hmem : (x j + x (j + 1)) / 2 ∈ Ioo (x j) (x (j + 1)) := by
      have := hx (Nat.lt_succ_self j); constructor <;> linarith
    have hpu : ∑ i ∈ Finset.range (j + 1), bspline x (k + 1) i ((x j + x (j + 1)) / 2) = 1 :=
      sum_bspline hx.monotone ⟨(hx.monotone hkj).trans hmem.1.le, hmem.2⟩
    have hval := hsum _ hmem
    have hval' : ∑ i ∈ Finset.range (j + 1), c i * bspline x (k + 1) i ((x j + x (j + 1)) / 2)
        = c (j - (k + 1))
          * ∑ i ∈ Finset.range (j + 1), bspline x (k + 1) i ((x j + x (j + 1)) / 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rcases Nat.lt_or_ge i (j - (k + 1)) with h | h
      · rw [bspline_eq_zero_of_add_le hx hmem (by omega), mul_zero, mul_zero]
      · rw [heq i h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    rw [hval', hpu, mul_one] at hval
    intro i hi1 hi2
    rw [heq i hi1 hi2, hval]

/-- **Linear independence of the B-splines** ((8.56) of [quarteroni2000numerical]): for strictly
increasing knots and $n \ge 1$, the restrictions of the $n + k$ B-splines
$B_{0,k}, \dots, B_{n+k-1,k}$ to $[x_k, x_{n+k}]$ are linearly independent.

The proof uses the local linear independence on every knot interval. -/
theorem linearIndependent_bspline (hx : StrictMono x) (hn : 1 ≤ n) :
    LinearIndependent ℝ fun i : Fin (n + k) =>
      fun t : Icc (x k) (x (n + k)) => bspline x k i (t : ℝ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set c : ℕ → ℝ := fun i => if h : i < n + k then g ⟨i, h⟩ else 0 with hc
  -- on each knot interval the vanishing combination is a vanishing local combination
  have key : ∀ j, k ≤ j → j < n + k → ∀ i, j - k ≤ i → i ≤ j → c i = 0 := by
    intro j hkj hjn
    refine eq_zero_of_sum_mul_bspline_eq_zero hx k j hkj c fun t ht => ?_
    have ht' : t ∈ Icc (x k) (x (n + k)) :=
      ⟨(hx.monotone hkj).trans ht.1.le, ht.2.le.trans (hx.monotone (by omega))⟩
    have hval := congrFun hg ⟨t, ht'⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hval
    have h1 : ∑ i : Fin (n + k), g i * bspline x k i t
        = ∑ i ∈ Finset.range (n + k), c i * bspline x k i t := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => c i * bspline x k i t) (n + k)]
      exact Finset.sum_congr rfl fun i _ => by simp [hc, i.2]
    rw [← hval, h1]
    refine Finset.sum_subset (Finset.range_subset_range.mpr (show j + 1 ≤ n + k by omega))
      fun i hi hij => ?_
    rw [Finset.mem_range] at hi hij
    rw [bspline_eq_zero_of_lt hx ht (by omega), mul_zero]
  intro i
  have : c i = 0 := by
    rcases Nat.lt_or_ge i k with hi | hi
    · exact key k le_rfl (by omega) i (by omega) hi.le
    · exact key i hi i.2 i (Nat.sub_le i k) le_rfl
  simpa [hc, i.2] using this

/-- **The B-spline basis of the spline space** ((8.56) of [quarteroni2000numerical]): for strictly
increasing knots, $n \ge 1$ and $k \ge 1$, the restrictions of $B_{0,k}, \dots, B_{n+k-1,k}$ to
$[x_k, x_{n+k}]$ form a basis of the spline space $S_k^{k-1}$ of degree $k$ and smoothness
$C^{k-1}$ on $[x_k, x_{n+k}]$ with the nodes $x_k < x_{k+1} < \dots < x_{n+k}$. Thus every such
spline is $\sum_{i < n+k} c_i B_{i,k}$ on $[x_k, x_{n+k}]$ with unique coefficients $c_i$, its
B-spline coefficients.

The proof counts dimensions: the $n + k$ B-splines are linearly independent in a space of
dimension $n + k$. The spline space is `Spline.splineSpace (x k) (x (n + k)) n (fun j => x (j +
k)) k (k - 1)`. -/
theorem exists_basis_bspline (hx : StrictMono x) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ B : Module.Basis (Fin (n + k)) ℝ
      (Spline.splineSpace (x k) (x (n + k)) n (fun j => x (j + k)) k (k - 1)),
      ∀ (i : Fin (n + k)) (t : Icc (x k) (x (n + k))),
        (B i : C(Icc (x k) (x (n + k)), ℝ)) t = bspline x k i t := by
  have hp : IsIntervalPartition (x k) (x (n + k)) n fun j => x (j + k) :=
    ⟨fun j _ => hx (by omega), by simp, rfl⟩
  set v : Fin (n + k) → Spline.splineSpace (x k) (x (n + k)) n (fun j => x (j + k)) k (k - 1) :=
    fun i => ⟨(ContinuousMap.mk _ (contDiff_bspline hx hk i).continuous).restrict _,
      bspline_mem_splineSpace hx hk i⟩ with hv
  have hli : LinearIndependent ℝ v := by
    refine LinearIndependent.of_comp
      ((ContinuousMap.coeFnLinearMap ℝ).comp
        (Spline.splineSpace (x k) (x (n + k)) n (fun j => x (j + k)) k (k - 1)).subtype) ?_
    exact linearIndependent_bspline hx hn
  have hcard : Fintype.card (Fin (n + k)) = Module.finrank ℝ
      (Spline.splineSpace (x k) (x (n + k)) n (fun j => x (j + k)) k (k - 1)) := by
    rw [Fintype.card_fin, Spline.finrank_splineSpace hp hn (Nat.sub_le k 1)]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [show m + 1 - 1 = m from rfl, show m + 1 - m = 1 by omega]
    ring
  have : Nonempty (Fin (n + k)) := ⟨⟨0, by omega⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun i t => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

/-! ### Schoenberg's minimal-support characterization -/

/-- **The jump representation of a $C^{k-1}$ piecewise polynomial supported in $[x_i, x_{i+k+1}]$.**
Let the knots be strictly increasing and $k \ge 1$. Let $s : \mathbb{R} \to \mathbb{R}$ be of
class $C^{k-1}$, vanish outside $[x_i, x_{i+k+1}]$, and agree with a real polynomial of degree
at most $k$ on each knot interval $[x_j, x_{j+1}]$, $i \le j \le i + k$. Then there are
coefficients $c_0, \dots, c_{k+1}$ with
$$\sum_{j=0}^{k+1} c_j (X - x_{i+j})^k = 0$$
such that for every $m \le k$ and every $t \in [x_{i+m}, x_{i+m+1}]$
$$s(t) = \sum_{j=0}^{m} c_j (t - x_{i+j})^k.$$

In the proof, $c_j$ is the jump of the leading coefficient at $x_{i+j}$, and the polynomial
identity expresses that $s$ vanishes to the right of $x_{i+k+1}$. The jump at each knot is a
multiple of $(X - x_{i+j})^k$ because the difference of the two adjacent pieces has $C^{k-1}$
contact with zero there (`Spline.iterate_derivative_eval_eq_zero_of_eqOn`). -/
theorem exists_sum_C_mul_X_sub_C_pow_eq_zero_and_eqOn (hx : StrictMono x) (hk : 1 ≤ k)
    {s : ℝ → ℝ} (hs : ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) s)
    (h0 : ∀ t ∉ Icc (x i) (x (i + k + 1)), s t = 0)
    (hp : ∀ j, i ≤ j → j ≤ i + k →
      ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn s p.eval (Icc (x j) (x (j + 1)))) :
    ∃ c : ℕ → ℝ, (∑ j ∈ Finset.range (k + 2), C (c j) * (X - C (x (i + j))) ^ k = 0) ∧
      ∀ m ≤ k, ∀ t ∈ Icc (x (i + m)) (x (i + m + 1)),
        s t = ∑ j ∈ Finset.range (m + 1), c j * (t - x (i + j)) ^ k := by
  classical
  have hp' : ∀ j, ∃ p : ℝ[X], i ≤ j → j ≤ i + k →
      p.degree ≤ k ∧ EqOn s p.eval (Icc (x j) (x (j + 1))) := fun j =>
    if h : i ≤ j ∧ j ≤ i + k then (hp j h.1 h.2).imp fun _ hp' _ _ => hp'
    else ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose p hp using hp'
  -- the pieces: `q 0 = 0` left of `x_i`, `q (m + 1)` on `[x_{i+m}, x_{i+m+1}]`, `q (k + 2) = 0`
  set q : ℕ → ℝ[X] := fun m => if 1 ≤ m ∧ m ≤ k + 1 then p (i + m - 1) else 0 with hq
  have hq0 : q 0 = 0 := by simp [hq]
  have hqlast : q (k + 2) = 0 := by simp [hq]
  have hqsucc : ∀ m ≤ k, q (m + 1) = p (i + m) := by
    intro m hm
    simp only [hq, show 1 ≤ m + 1 ∧ m + 1 ≤ k + 1 from ⟨by omega, by omega⟩, and_self, ite_true,
      show i + (m + 1) - 1 = i + m by omega]
  have hqdeg : ∀ m, (q m).degree ≤ k := by
    intro m
    simp only [hq]
    split_ifs with h
    · exact (hp _ (by omega) (by omega)).1
    · simp
  -- the left neighbours of the knots
  set L : ℕ → ℝ := fun m => if m = 0 then x i - 1 else x (i + m - 1) with hL
  have hLlt : ∀ m, L m < x (i + m) := by
    intro m
    simp only [hL]
    split_ifs with h
    · subst h; simp
    · exact hx (by omega)
  -- `s` is `q m` on `(L m, x_{i+m})` and `q (m+1)` on `(x_{i+m}, x_{i+m+1})`
  have hleft : ∀ m ≤ k + 1, ∀ t ∈ Ioo (L m) (x (i + m)), s t = (q m).eval t := by
    intro m hm t ht
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [hq0, eval_zero]
      refine h0 t fun h => ?_
      simp only [hL, ite_true, add_zero] at ht
      exact absurd h.1 (not_le.mpr ht.2)
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [hqsucc m' (by omega)]
      simp only [hL, Nat.add_one_ne_zero, ite_false,
        show i + (m' + 1) - 1 = i + m' by omega] at ht
      exact (hp (i + m') (by omega) (by omega)).2 (Ioo_subset_Icc_self ht)
  have hright : ∀ m ≤ k + 1, ∀ t ∈ Ioo (x (i + m)) (x (i + m + 1)),
      s t = (q (m + 1)).eval t := by
    intro m hm t ht
    rcases Nat.lt_or_ge m (k + 1) with hmk | hmk
    · rw [hqsucc m (by omega)]
      exact (hp (i + m) (by omega) (by omega)).2 (Ioo_subset_Icc_self ht)
    · obtain rfl : m = k + 1 := by omega
      rw [hqlast, eval_zero]
      exact h0 t fun h => absurd h.2 (not_le.mpr ht.1)
  -- the jumps
  set c : ℕ → ℝ := fun m => (taylor (x (i + m)) (q (m + 1) - q m)).coeff k with hc
  have hjump : ∀ m ≤ k + 1, q (m + 1) - q m = C (c m) * (X - C (x (i + m))) ^ k := by
    intro m hm
    have hcontact : ∀ j ≤ k - 1, (derivative^[j] (q (m + 1) - q m)).eval (x (i + m)) = 0 := by
      intro j hj
      refine Spline.iterate_derivative_eval_eq_zero_of_eqOn (hLlt m) (hx (Nat.lt_succ_self _))
        (e := fun t => s t - (q m).eval t) (hs.contDiffOn.sub ((q m).contDiff_eval _).contDiffOn)
        (fun t ht => ?_) (fun t ht => ?_) hj
      · simp only [Pi.zero_apply, hleft m hm t ht, sub_self]
      · simp only [eval_sub, hright m hm t ht]
    have hnat : (q (m + 1) - q m).natDegree ≤ k :=
      natDegree_le_iff_degree_le.mpr ((degree_sub_le _ _).trans (max_le (hqdeg _) (hqdeg _)))
    refine Polynomial.funext fun t => ?_
    rw [Spline.eval_eq_sum_Ioc_of_iterate_derivative_eq_zero hnat hcontact t]
    have hIoc : Finset.Ioc (k - 1) k = {k} := by
      ext j; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
    rw [hIoc, Finset.sum_singleton, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_C]
  -- telescoping
  have htel : ∀ m ≤ k + 1,
      q (m + 1) = ∑ j ∈ Finset.range (m + 1), C (c j) * (X - C (x (i + j))) ^ k := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Finset.sum_range_one, ← hjump 0 (by omega), hq0, sub_zero]
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ, ← ih (by omega), ← hjump (m + 1) hm]
      ring
  refine ⟨c, ?_, fun m hm t ht => ?_⟩
  · rw [← htel (k + 1) le_rfl, hqlast]
  · rw [(hp (i + m) (by omega) (by omega)).2 ht, ← hqsucc m hm, htel m (by omega)]
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X]

/-- **Schoenberg's minimal-support characterization of the B-spline** (§8.6.2 of
[quarteroni2000numerical], quoting Schoenberg): let the knots be strictly increasing and
$k \ge 1$. If $s : \mathbb{R} \to \mathbb{R}$ is of class $C^{k-1}$, vanishes outside
$[x_i, x_{i+k+1}]$, and agrees with a real polynomial of degree at most $k$ on each knot
interval $[x_j, x_{j+1}]$, $i \le j \le i + k$, then $s = c\, B_{i,k}$ for some
$c \in \mathbb{R}$.

Both $s$ and $B_{i,k}$ have the representation of
`BSpline.exists_sum_C_mul_X_sub_C_pow_eq_zero_and_eqOn`, with coefficients in the kernel of
$c \mapsto \sum_{j=0}^{k+1} c_j (X - x_{i+j})^k$, which is one-dimensional
(`Polynomial.exists_eq_smul_of_sum_C_mul_X_sub_C_pow_eq_zero`). The coefficients of $B_{i,k}$
are not all zero, because $B_{i,k}$ is positive on $(x_i, x_{i+k+1})$ (`BSpline.bspline_pos`). -/
theorem exists_eq_smul_bspline (hx : StrictMono x) (hk : 1 ≤ k) {s : ℝ → ℝ}
    (hs : ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) s)
    (h0 : ∀ t ∉ Icc (x i) (x (i + k + 1)), s t = 0)
    (hp : ∀ j, i ≤ j → j ≤ i + k →
      ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn s p.eval (Icc (x j) (x (j + 1)))) :
    ∃ c : ℝ, s = c • bspline x k i := by
  classical
  obtain ⟨c, hc0, hcs⟩ := exists_sum_C_mul_X_sub_C_pow_eq_zero_and_eqOn hx hk hs h0 hp
  have hB0 : ∀ t ∉ Icc (x i) (x (i + k + 1)), bspline x k i t = 0 := fun t ht =>
    bspline_eq_zero_of_notMem hx.monotone fun h => ht (Ico_subset_Icc_self h)
  have hBp : ∀ j, i ≤ j → j ≤ i + k →
      ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn (bspline x k i) p.eval (Icc (x j) (x (j + 1))) := by
    intro j _ _
    exact exists_eqOn_Icc_bspline hx hk i j
  obtain ⟨c', hc'0, hc's⟩ :=
    exists_sum_C_mul_X_sub_C_pow_eq_zero_and_eqOn hx hk (contDiff_bspline hx hk i) hB0 hBp
  -- the B-spline's coefficients are not all zero
  have hne : (fun j : Fin (k + 2) => c' j) ≠ 0 := by
    intro hzero
    have hz : ∀ j < k + 2, c' j = 0 := fun j hj => congrFun hzero ⟨j, hj⟩
    set t := (x (i + k) + x (i + k + 1)) / 2 with ht
    have hlt := hx (Nat.lt_succ_self (i + k))
    have htm : t ∈ Ioo (x (i + k)) (x (i + k + 1)) :=
      ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
    have hpos : 0 < bspline x k i t :=
      bspline_pos hx ⟨(hx.monotone (Nat.le_add_right i k)).trans_lt htm.1, htm.2⟩
    rw [hc's k le_rfl t (Ioo_subset_Icc_self htm)] at hpos
    refine hpos.ne' (Finset.sum_eq_zero fun j hj => ?_)
    rw [hz j (by have := Finset.mem_range.mp hj; omega), zero_mul]
  have hinj : Function.Injective fun j : Fin (k + 2) => x (i + j) := fun a b h =>
    Fin.ext (by simpa using hx.injective h)
  obtain ⟨l, hl⟩ := exists_eq_smul_of_sum_C_mul_X_sub_C_pow_eq_zero hinj (c := fun j => c j)
    (c' := fun j => c' j)
    ((Fin.sum_univ_eq_sum_range (fun j => C (c j) * (X - C (x (i + j))) ^ k) (k + 2)).trans hc0)
    ((Fin.sum_univ_eq_sum_range (fun j => C (c' j) * (X - C (x (i + j))) ^ k) (k + 2)).trans hc'0)
    hne
  have hl' : ∀ j < k + 2, c j = l * c' j := fun j hj => by
    simpa using congrFun hl ⟨j, hj⟩
  refine ⟨l, funext fun t => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases ht : t ∈ Icc (x i) (x (i + k + 1))
  · have hpart : IsIntervalPartition (x i) (x (i + k + 1)) (k + 1) fun m => x (i + m) :=
      ⟨fun j _ => hx (by omega), rfl, rfl⟩
    obtain ⟨m, hm1, hmk, htm, -⟩ := hpart.exists_mem_panel (by omega) ht
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at htm
    rw [hcs m (by omega) t htm, hc's m (by omega) t htm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hl' j (by have := Finset.mem_range.mp hj; omega)]
    ring
  · rw [h0 t ht, hB0 t ht, mul_zero]

/-! ### Coincident knots -/

/-- **B-splines with $k + 1$ coincident knots at the left** (Remark 8.3 of
[quarteroni2000numerical]): if $x_i = x_{i+1} = \dots = x_{i+k} < x_{i+k+1}$, then for every
$t \in \mathbb{R}$
$$B_{i,k}(t) = \begin{cases} \Bigl(\dfrac{x_{i+k+1} - t}{x_{i+k+1} - x_i}\Bigr)^k & \text{if } t
  \in [x_i, x_{i+k+1}), \\ 0 & \text{otherwise.} \end{cases}$$

No other condition on the knots is needed. The source prints the closed interval
$[x_i, x_{i+k+1}]$. For $k \ge 1$ this makes no difference, because the formula gives $0$ at the
right end. -/
theorem bspline_apply_of_coincident_left (hcoin : ∀ j, i ≤ j → j ≤ i + k → x j = x i)
    (hlt : x i < x (i + k + 1)) (t : ℝ) :
    bspline x k i t = if t ∈ Ico (x i) (x (i + k + 1)) then
      ((x (i + k + 1) - t) / (x (i + k + 1) - x i)) ^ k else 0 := by
  induction k generalizing i with
  | zero => simp [bspline_zero]
  | succ d ih =>
    rw [bspline_succ]
    have h0 : weight x i (d + 1) t = 0 := by
      simp [weight, hcoin (i + (d + 1)) (by omega) (by omega)]
    have hi1 : x (i + 1) = x i := hcoin (i + 1) (by omega) (by omega)
    have hlt' : x (i + 1) < x (i + 1 + d + 1) := by
      rw [hi1, show i + 1 + d + 1 = i + (d + 1) + 1 by omega]; exact hlt
    have hne : x (i + 1 + (d + 1)) ≠ x (i + 1) := by
      rw [show i + 1 + (d + 1) = i + 1 + d + 1 by omega]; exact hlt'.ne'
    rw [ih (i := i + 1) (fun j hj1 hj2 => by
      rw [hcoin j (by omega) (by omega), hi1]) hlt', h0, zero_mul, zero_add]
    have hw : weight x (i + 1) (d + 1) t = (t - x i) / (x (i + (d + 1) + 1) - x i) := by
      unfold weight
      rw [ite_eq_right hne, hi1, show i + 1 + (d + 1) = i + (d + 1) + 1 by omega]
    rw [hw, hi1, show i + 1 + d + 1 = i + (d + 1) + 1 by omega]
    by_cases h : t ∈ Ico (x i) (x (i + (d + 1) + 1))
    · rw [ite_eq_left h, ite_eq_left h]
      have hpos : x (i + (d + 1) + 1) - x i ≠ 0 := sub_ne_zero.mpr hlt.ne'
      rw [pow_succ]
      field_simp
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- **B-splines with $k + 1$ coincident knots at the right** (Remark 8.3 of
[quarteroni2000numerical]): for nondecreasing knots with $x_i < x_{i+1} = \dots = x_{i+k+1}$ and
every $t \in \mathbb{R}$,
$$B_{i,k}(t) = \begin{cases} \Bigl(\dfrac{t - x_i}{x_{i+k+1} - x_i}\Bigr)^k & \text{if } t \in
  [x_i, x_{i+k+1}), \\ 0 & \text{otherwise.} \end{cases}$$
-/
theorem bspline_apply_of_coincident_right (hx : Monotone x)
    (hcoin : ∀ j, i + 1 ≤ j → j ≤ i + k + 1 → x j = x (i + k + 1)) (hlt : x i < x (i + k + 1))
    (t : ℝ) :
    bspline x k i t = if t ∈ Ico (x i) (x (i + k + 1)) then
      ((t - x i) / (x (i + k + 1) - x i)) ^ k else 0 := by
  induction k generalizing i with
  | zero => simp [bspline_zero]
  | succ d ih =>
    rw [bspline_succ]
    have hlast : x (i + d + 1) = x (i + (d + 1) + 1) := hcoin (i + d + 1) (by omega) (by omega)
    have hz : bspline x d (i + 1) t = 0 := by
      refine bspline_eq_zero_of_notMem hx fun h => ?_
      rw [hcoin (i + 1 + d + 1) (by omega) (by omega), hcoin (i + 1) (by omega) (by omega)] at h
      exact absurd h.2 (not_lt.mpr h.1)
    have hne : x (i + (d + 1)) ≠ x i := by
      rw [show i + (d + 1) = i + d + 1 by omega, hlast]; exact hlt.ne'
    rw [hz, mul_zero, add_zero, ih (i := i) (fun j hj1 hj2 => by
      rw [hcoin j (by omega) (by omega), hlast]) (by rw [hlast]; exact hlt)]
    have hw : weight x i (d + 1) t = (t - x i) / (x (i + (d + 1) + 1) - x i) := by
      unfold weight
      rw [ite_eq_right hne, show i + (d + 1) = i + d + 1 by omega, hlast,
        show i + d + 1 + 1 = i + (d + 1) + 1 by omega]
    rw [hw, hlast]
    by_cases h : t ∈ Ico (x i) (x (i + (d + 1) + 1))
    · rw [ite_eq_left h, ite_eq_left h, pow_succ]
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-- **Values at a knot of multiplicity $m + 1$**: for nondecreasing knots with
$x_0 = \dots = x_m < x_{m+1}$, every degree $d$ and every $i \le m$,
$$B_{i,d}(x_m) = \begin{cases} 1 & \text{if } i + d = m, \\ 0 & \text{otherwise.} \end{cases}$$
The proof goes through the recursion, since the weights $\omega_{i,d}(x_m)$ vanish for
$i \le m$. -/
theorem bspline_apply_of_coincident (hx : Monotone x) {m : ℕ} (hcoin : ∀ j ≤ m, x j = x m)
    (hlt : x m < x (m + 1)) :
    ∀ d i, i ≤ m → bspline x d i (x m) = if i + d = m then 1 else 0 := by
  intro d
  induction d with
  | zero =>
    intro i hi
    rw [bspline_zero, hcoin i hi]
    by_cases him : i = m
    · subst him; simp [hlt]
    · rw [hcoin (i + 1) (by omega)]
      simp [him]
  | succ d ih =>
    intro i hi
    rw [bspline_succ]
    have h0 : weight x i (d + 1) (x m) = 0 := by
      simp [weight, hcoin i hi]
    rw [h0, zero_mul, zero_add]
    by_cases him : i = m
    · subst him
      rw [bspline_eq_zero_of_notMem hx fun h => absurd h.1 (not_le.mpr hlt), mul_zero]
      simp
    · have h1 : weight x (i + 1) (d + 1) (x m) = 0 := by
        simp [weight, hcoin (i + 1) (by omega)]
      rw [h1, sub_zero, one_mul, ih (i + 1) (by omega)]
      simp only [show i + 1 + d = i + (d + 1) by omega]

/-- **The value at the left endpoint with $k + 1$ coincident knots** ((8.57) of
[quarteroni2000numerical], first half): for nondecreasing knots with
$x_0 = \dots = x_k < x_{k+1}$, for $n \ge 1$ and for all coefficients $c_i$,
$$\sum_{i=0}^{n+k-1} c_i B_{i,k}(x_k) = c_0.$$
-/
theorem sum_smul_bspline_left (hx : Monotone x) (hn : 1 ≤ n) (hcoin : ∀ j ≤ k, x j = x k)
    (hlt : x k < x (k + 1)) (c : ℕ → ℝ) :
    ∑ i ∈ Finset.range (n + k), c i * bspline x k i (x k) = c 0 := by
  rw [Finset.sum_eq_single 0]
  · rw [bspline_apply_of_coincident hx hcoin hlt k 0 (Nat.zero_le k)]; simp
  · intro i _ hi0
    rcases le_or_gt i k with hik | hik
    · rw [bspline_apply_of_coincident hx hcoin hlt k i hik, ite_eq_right (by omega), mul_zero]
    · rw [bspline_eq_zero_of_notMem hx fun h => absurd h.1 (not_le.mpr ((hlt.trans_le
        (hx hik)))), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ### The cubic B-spline on uniform knots -/

/-- **The cubic B-spline on uniform knots** (Example 8.9 of [quarteroni2000numerical]): let $h > 0$
and $x_j = x_0 + j h$ for all $j$. Then for every $t \in \mathbb{R}$, $6 h^3 B_{i,3}(t)$ equals
$$\begin{cases} (t - x_i)^3 & \text{if } t \in [x_i, x_{i+1}), \\ h^3 + 3h^2 (t - x_{i+1}) + 3h
  (t - x_{i+1})^2 - 3 (t - x_{i+1})^3 & \text{if } t \in [x_{i+1}, x_{i+2}), \\ h^3 + 3h^2
  (x_{i+3} - t) + 3h (x_{i+3} - t)^2 - 3 (x_{i+3} - t)^3 & \text{if } t \in [x_{i+2}, x_{i+3}),
  \\ (x_{i+4} - t)^3 & \text{if } t \in [x_{i+3}, x_{i+4}), \\ 0 & \text{otherwise.}
  \end{cases}$$
The proof unfolds the recursion three times on each of the four intervals. -/
theorem bspline_uniform_cubic {x₀ h : ℝ} (hh : 0 < h) (hx : ∀ j, x j = x₀ + j * h) (i : ℕ)
    (t : ℝ) :
    6 * h ^ 3 * bspline x 3 i t =
      if t ∈ Ico (x i) (x (i + 1)) then (t - x i) ^ 3
      else if t ∈ Ico (x (i + 1)) (x (i + 2)) then
        h ^ 3 + 3 * h ^ 2 * (t - x (i + 1)) + 3 * h * (t - x (i + 1)) ^ 2 - 3 * (t - x (i + 1)) ^ 3
      else if t ∈ Ico (x (i + 2)) (x (i + 3)) then
        h ^ 3 + 3 * h ^ 2 * (x (i + 3) - t) + 3 * h * (x (i + 3) - t) ^ 2 - 3 * (x (i + 3) - t) ^ 3
      else if t ∈ Ico (x (i + 3)) (x (i + 4)) then (x (i + 4) - t) ^ 3
      else 0 := by
  have hw : ∀ j d, 1 ≤ d → weight x j d t = (t - x j) / (d * h) := by
    intro j d hd
    have hne : x (j + d) - x j = d * h := by rw [hx, hx]; push_cast; ring
    have hpos : (0 : ℝ) < d * h := mul_pos (by exact_mod_cast hd) hh
    rw [weight, ite_eq_right (fun h' => by rw [h', sub_self] at hne; linarith), hne]
  simp only [bspline_succ, bspline_zero, Nat.reduceAdd, hw _ 3 (by norm_num),
    hw _ 2 (by norm_num), hw _ 1 le_rfl, mem_Ico, hx]
  push_cast
  ring_nf
  split_ifs <;> first | (exfalso; linarith) | (field_simp; ring)

/-! ### Parametric B-spline curves -/

section Curve

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **The parametric B-spline curve** (§8.7.1 of [quarteroni2000numerical]) of degree $k$ with the
control points $P_0, \dots, P_{N-1}$ in a real vector space $E$:
$$t \mapsto \sum_{i=0}^{N-1} B_{i,k}(t)\, P_i.$$
-/
noncomputable def curve (x : ℕ → ℝ) (k : ℕ) (P : ℕ → E) (N : ℕ) (t : ℝ) : E :=
  ∑ i ∈ Finset.range N, bspline x k i t • P i

/-- **The convex-hull property** (§8.7.1 of [quarteroni2000numerical], property 2): for
nondecreasing knots, $N \ge 1$ control points $P_0, \dots, P_{N-1}$ and $t \in [x_k, x_N)$, the
point of the curve at $t$ lies in the convex hull of $\{P_0, \dots, P_{N-1}\}$. The reason is
that the coefficients $B_{i,k}(t)$ are nonnegative and sum to one. -/
theorem curve_mem_convexHull (hx : Monotone x) (P : ℕ → E) {N : ℕ} (hN : 1 ≤ N)
    (ht : t ∈ Ico (x k) (x N)) : curve x k P N t ∈ convexHull ℝ (P '' Iio N) := by
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => bspline_nonneg hx) ?_
    fun i hi => subset_convexHull ℝ _ ⟨i, Finset.mem_range.mp hi, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact sum_bspline hx ht

/-- **Locality** (§8.7.1 of [quarteroni2000numerical], property 1): for nondecreasing knots, a
change of the control point $P_j$ changes the curve only on $[x_j, x_{j+k+1})$. That is, for
$t \notin [x_j, x_{j+k+1})$ and any $Q \in E$, the curve with $P_j$ replaced by $Q$ has the same
value at $t$ as the original curve, for any number $N$ of control points. -/
theorem curve_update_eq_of_notMem (hx : Monotone x) (P : ℕ → E) (j : ℕ) (Q : E) {N : ℕ}
    (ht : t ∉ Ico (x j) (x (j + k + 1))) :
    curve x k (Function.update P j Q) N t = curve x k P N t := by
  classical
  unfold curve
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : i = j
  · subst hij
    rw [bspline_eq_zero_of_notMem hx ht, zero_smul, zero_smul]
  · rw [Function.update_of_ne hij]

end Curve

/-- **The value at the right endpoint with $k + 1$ coincident knots** ((8.57) of
[quarteroni2000numerical], second half): for nondecreasing knots with $x_{n+k-1} < x_{n+k} =
x_{n+k+1} = \dots = x_{n+2k}$, for $n \ge 1$ and for all coefficients $c_i$,
$$\lim_{t \to x_{n+k}^-} \sum_{i=0}^{n+k-1} c_i B_{i,k}(t) = c_{n+k-1}.$$

With the half-open convention every $B_{i,k}$ vanishes at the endpoint $b = x_{n+k}$ itself, so
the endpoint value is the left limit. By the coincident-knot formula $B_{n+k-1,k}(t) \to 1$, and
by the partition of unity the other B-splines tend to $0$. -/
theorem sum_smul_bspline_right (hx : Monotone x) (hn : 1 ≤ n)
    (hcoin : ∀ j, n + k ≤ j → j ≤ n + 2 * k → x j = x (n + k))
    (hlt : x (n + k - 1) < x (n + k)) (c : ℕ → ℝ) :
    Tendsto (fun t => ∑ i ∈ Finset.range (n + k), c i * bspline x k i t) (𝓝[<] x (n + k))
      (𝓝 (c (n + k - 1))) := by
  set N := n + k - 1 with hN
  set b := x (n + k) with hb
  have hNk : N + k + 1 = n + 2 * k := by omega
  have hN1 : N + 1 = n + k := by omega
  have hmem : Ico (x N) b ∈ 𝓝[<] b := Ico_mem_nhdsLT hlt
  -- the last B-spline tends to `1`
  have hlast : ∀ t ∈ Ico (x N) b, bspline x k N t = ((t - x N) / (b - x N)) ^ k := by
    intro t ht
    rw [bspline_apply_of_coincident_right hx (i := N) (fun j hj1 hj2 => by
      rw [hcoin j (by omega) (by omega), hcoin (N + k + 1) (by omega) (by omega)]) (by
        rw [hNk, hcoin (n + 2 * k) (by omega) le_rfl]; exact hlt), hNk,
      hcoin (n + 2 * k) (by omega) le_rfl, ite_eq_left ht]
  have hB : Tendsto (fun t => bspline x k N t) (𝓝[<] b) (𝓝 1) := by
    have h1 : Tendsto (fun t => ((t - x N) / (b - x N)) ^ k) (𝓝[<] b)
        (𝓝 (((b - x N) / (b - x N)) ^ k)) :=
      (((continuous_id.sub continuous_const).div_const _).pow k).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    rw [div_self (sub_ne_zero.mpr hlt.ne'), one_pow] at h1
    exact h1.congr' (Filter.eventually_of_mem hmem fun t ht => (hlast t ht).symm)
  -- the partition of unity on `[x_N, b)`
  have hpu : ∀ t ∈ Ico (x N) b, ∑ i ∈ (Finset.range (n + k)).erase N, bspline x k i t
      = 1 - bspline x k N t := by
    intro t ht
    have ht2 : t < x (N + 1) := by rw [hN1]; exact ht.2
    have := sum_bspline (n := N) (k := k) hx (t := t) ⟨(hx (show k ≤ N by omega)).trans ht.1, ht2⟩
    rw [hN1] at this
    rw [← this, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (show N < n + k by omega))]
    ring
  -- split off the last term
  have hsplit : ∀ t, ∑ i ∈ Finset.range (n + k), c i * bspline x k i t
      = c N * bspline x k N t + ∑ i ∈ (Finset.range (n + k)).erase N, c i * bspline x k i t :=
    fun t => (Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega))).symm
  simp_rw [hsplit]
  have h0 : Tendsto (fun t => ∑ i ∈ (Finset.range (n + k)).erase N, c i * bspline x k i t)
      (𝓝[<] b) (𝓝 0) := by
    refine squeeze_zero_norm' (Filter.eventually_of_mem hmem fun t ht => ?_)
      (a := fun t => (∑ i ∈ (Finset.range (n + k)).erase N, |c i|) * (1 - bspline x k N t)) ?_
    · refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (bspline_nonneg hx)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [← hpu t ht]
      exact Finset.single_le_sum (f := fun j => bspline x k j t) (fun j _ => bspline_nonneg hx) hi
    · have := (tendsto_const_nhds (x := (1 : ℝ))).sub hB
      rw [sub_self] at this
      simpa using (tendsto_const_nhds (x := ∑ i ∈ (Finset.range (n + k)).erase N, |c i|)).mul this
  have := ((tendsto_const_nhds (x := c N)).mul hB).add h0
  simpa using this

/-! ### Continuity in the knots -/

/-- **B-splines depend continuously on their knots, approached from below.** Let $x$ be a
nondecreasing knot sequence, and let $X_1, X_2, \dots$ be nondecreasing knot sequences with
$X_n(m) < x_m$ for all $n$ and $m$, and $X_n(m) \to x_m$ as $n \to \infty$ for every $m$. Then
for all $k$, $i$ and $t$,
$$B^{X_n}_{i,k}(t) \to B^{x}_{i,k}(t) \qquad (n \to \infty),$$
where $B^{X}_{i,k}$ is the B-spline on the knots $X$.

The approach from below makes this true at every $t$, the knots included: the B-splines of
degree $0$ are eventually equal, because the half-open interval $[X_n(i), X_n(i+1))$ eventually
contains a given $t \in [x_i, x_{i+1})$ and never contains a $t \ge x_{i+1}$. In the Cox–de Boor
recursion the weight $\omega_{i,d+1}$ may fail to converge, exactly when $x_{i+d+1} = x_i$. But
then the B-spline that it multiplies has empty support and is eventually $0$, so the product
converges all the same. The theorem is used to pass from strictly increasing to nondecreasing
knots in Boehm's algorithm. -/
theorem tendsto_bspline_of_tendsto {X : ℕ → ℕ → ℝ} (hx : Monotone x) (hX : ∀ n, Monotone (X n))
    (hlt : ∀ n m, X n m < x m) (hto : ∀ m, Tendsto (fun n => X n m) atTop (𝓝 (x m)))
    (k i : ℕ) (t : ℝ) :
    Tendsto (fun n => bspline (X n) k i t) atTop (𝓝 (bspline x k i t)) := by
  induction k generalizing i with
  | zero =>
    rcases lt_or_ge t (x i) with h | h
    · have h0 : bspline x 0 i t = 0 := by
        rw [bspline_zero, ite_eq_right (fun hc => absurd hc.1 (not_le.2 h))]
      rw [h0]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [(hto i).eventually (eventually_gt_nhds h)] with n hn
      rw [bspline_zero, ite_eq_right (fun hc => absurd hc.1 (not_le.2 hn))]
    rcases lt_or_ge t (x (i + 1)) with h2 | h2
    · have h0 : bspline x 0 i t = 1 := by rw [bspline_zero, ite_eq_left ⟨h, h2⟩]
      rw [h0]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [(hto (i + 1)).eventually (eventually_gt_nhds h2)] with n hn
      exact ((bspline_zero (X n) i t).trans (ite_eq_left ⟨(hlt n i).le.trans h, hn⟩)).symm
    · have h0 : bspline x 0 i t = 0 := by
        rw [bspline_zero, ite_eq_right (fun hc => absurd hc.2 (not_lt.2 h2))]
      rw [h0]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards with n
      exact ((bspline_zero (X n) i t).trans
        (ite_eq_right (fun hc => absurd hc.2 (not_lt.2 ((hlt n (i + 1)).le.trans h2))))).symm
  | succ d ih =>
    have key : ∀ p : ℕ, Tendsto (fun n => weight (X n) p (d + 1) t * bspline (X n) d p t) atTop
        (𝓝 (weight x p (d + 1) t * bspline x d p t)) := by
      intro p
      by_cases hp : x (p + (d + 1)) = x p
      · have hw : weight x p (d + 1) t = 0 := by rw [weight, ite_eq_left hp]
        rw [hw, zero_mul]
        refine Tendsto.congr' ?_ tendsto_const_nhds
        have hev : ∀ᶠ n in atTop, t ∉ Ico (X n p) (X n (p + d + 1)) := by
          rcases lt_or_ge t (x p) with h | h
          · filter_upwards [(hto p).eventually (eventually_gt_nhds h)] with n hn
            exact fun hc => absurd hc.1 (not_le.2 hn)
          · filter_upwards with n
            refine fun hc => absurd hc.2 (not_lt.2 ?_)
            exact ((hlt n (p + d + 1)).le.trans (le_of_eq (show x (p + d + 1) = x p from hp))).trans
              h
        filter_upwards [hev] with n hn
        rw [bspline_eq_zero_of_notMem (hX n) hn, mul_zero]
      · have hlt' : x p < x (p + (d + 1)) := lt_of_le_of_ne (hx (by omega)) (Ne.symm hp)
        have hd : Tendsto (fun n => X n (p + (d + 1)) - X n p) atTop
            (𝓝 (x (p + (d + 1)) - x p)) := (hto _).sub (hto _)
        have hne : (x (p + (d + 1)) - x p) ≠ 0 := sub_ne_zero.2 (by linarith)
        have hwt : Tendsto (fun n => weight (X n) p (d + 1) t) atTop
            (𝓝 (weight x p (d + 1) t)) := by
          have hw : weight x p (d + 1) t = (t - x p) / (x (p + (d + 1)) - x p) := by
            rw [weight, ite_eq_right hp]
          have hq : Tendsto (fun n => (t - X n p) / (X n (p + (d + 1)) - X n p)) atTop
              (𝓝 ((t - x p) / (x (p + (d + 1)) - x p))) :=
            (tendsto_const_nhds.sub (hto p)).div hd hne
          rw [hw]
          refine hq.congr' ?_
          filter_upwards [hd.eventually (eventually_ne_nhds hne)] with n hn
          rw [weight, ite_eq_right (fun hc => hn (by rw [hc, sub_self]))]
        exact hwt.mul (ih p)
    have h1 := key i
    have h2 := (ih (i + 1)).sub (key (i + 1))
    simp only [bspline_succ, one_sub_mul]
    exact h1.add h2

/-! ### Knot insertion -/

/-- **Boehm's knot insertion** (Remark 8.4 of [quarteroni2000numerical]): the knot sequence $\hat x$
obtained by inserting a new knot $y$ after position $j$: $\hat x_i = x_i$ for $i \le j$,
$\hat x_{j+1} = y$, and $\hat x_i = x_{i-1}$ for $i > j + 1$. It is intended for
$y \in [x_j, x_{j+1})$, but the definition does not require this. -/
def insertKnot (x : ℕ → ℝ) (j : ℕ) (y : ℝ) (i : ℕ) : ℝ :=
  if i ≤ j then x i else if i = j + 1 then y else x (i - 1)

/-- The weights $\omega_i$ of Boehm's algorithm: $\omega_i = 1$ for $i + k \le j$,
$\omega_i = (y - x_i)/(x_{i+k} - x_i)$ for $j - k < i \le j$, and $\omega_i = 0$ for $i > j$. A
quotient with denominator $0$ is $0$. -/
noncomputable def insertKnotWeight (x : ℕ → ℝ) (k j : ℕ) (y : ℝ) (i : ℕ) : ℝ :=
  if i + k ≤ j then 1 else if i ≤ j then (y - x i) / (x (i + k) - x i) else 0

/-- **The new B-spline coefficients of Boehm's algorithm** (Remark 8.4 of
[quarteroni2000numerical]): $d_i = \omega_i c_i + (1 - \omega_i)\, c_{i-1}$, with the weights
$\omega_i$ of `BSpline.insertKnotWeight`. For $i = 0$ the index $i - 1$ is read as $0$, so
$d_0 = c_0$.

The source prints $c_i$ in place of $c_{i-1}$ in the second term. This is a misprint, and the
definition uses $c_{i-1}$. -/
noncomputable def insertKnotCoeff (x : ℕ → ℝ) (k j : ℕ) (y : ℝ) (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  insertKnotWeight x k j y i * c i + (1 - insertKnotWeight x k j y i) * c (i - 1)

/-- For nondecreasing knots and $y \in [x_j, x_{j+1})$, the refined knot sequence $\hat x$ is
nondecreasing. -/
theorem monotone_insertKnot (hx : Monotone x) {j : ℕ} {y : ℝ} (hy : y ∈ Ico (x j) (x (j + 1))) :
    Monotone (insertKnot x j y) := by
  refine monotone_nat_of_le_succ fun i => ?_
  unfold insertKnot
  by_cases h1 : i ≤ j
  · by_cases h2 : i + 1 ≤ j
    · rw [ite_eq_left h1, ite_eq_left h2]; exact hx (by omega)
    · have hij : i = j := by omega
      subst hij
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left rfl]; exact hy.1
  · by_cases h4 : i = j + 1
    · subst h4
      rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega),
        Nat.add_sub_cancel]
      exact hy.2.le
    · rw [ite_eq_right h1, ite_eq_right h4, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hx (by omega)

section KnotInsertion

variable {j : ℕ} {y : ℝ}

/-- For strictly increasing knots and $y \in (x_j, x_{j+1})$, the refined knot sequence $\hat x$ is
strictly increasing. -/
theorem strictMono_insertKnot (hx : StrictMono x) (hy : y ∈ Ioo (x j) (x (j + 1))) :
    StrictMono (insertKnot x j y) := by
  refine strictMono_nat_of_lt_succ fun m => ?_
  unfold insertKnot
  by_cases h1 : m ≤ j
  · by_cases h2 : m + 1 ≤ j
    · rw [ite_eq_left h1, ite_eq_left h2]; exact hx (by omega)
    · have hmj : m = j := by omega
      subst hmj
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left rfl]; exact hy.1
  · by_cases h4 : m = j + 1
    · subst h4
      rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right (by omega), ite_eq_right (by omega),
        Nat.add_sub_cancel]
      exact hy.2
    · rw [ite_eq_right h1, ite_eq_right h4, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hx (by omega)

/-- The index shift $\sigma_j$ with $\sigma_j(m) = m$ for $m \le j$ and $\sigma_j(m) = m + 1$ for
$m > j$, which identifies the original knots inside the refined sequence. -/
def insertShift (j m : ℕ) : ℕ := if m ≤ j then m else m + 1

/-- The index shift $\sigma_j$ is injective. -/
theorem insertShift_injective (j : ℕ) : Function.Injective (insertShift j) := by
  intro a b h
  unfold insertShift at h
  split_ifs at h <;> omega

/-- The refined sequence, read through the index shift, is the original one:
$\hat x_{\sigma_j(m)} = x_m$ for every $m$. -/
theorem insertKnot_insertShift (x : ℕ → ℝ) (j : ℕ) (y : ℝ) (m : ℕ) :
    insertKnot x j y (insertShift j m) = x m := by
  unfold insertKnot insertShift
  split_ifs <;> first | rfl | omega

/-- For a strictly increasing knot sequence $v$ and $k \ge 1$, the B-spline is a divided difference
over the index set $\{i, \dots, i + k + 1\}$:
$$B_{i,k}(t) = (v_{i+k+1} - v_i)\, g[v_i, \dots, v_{i+k+1}], \qquad g(s) = (s - t)_+^k.$$
The divided difference is `DividedDifference.newtonOn` over `Finset.Icc i (i + k + 1)`. -/
theorem bspline_eq_mul_newtonOn {v : ℕ → ℝ} (hv : StrictMono v) (hk : 1 ≤ k) (i : ℕ) (t : ℝ) :
    bspline v k i t = (v (i + k + 1) - v i) *
      DividedDifference.newtonOn (Finset.Icc i (i + k + 1)) v
        (fun s => Quadrature.truncPow k s t) := by
  rw [bspline_eq_mul_newton_truncPow hv hk i t,
    DividedDifference.newton_shift_eq_newtonOn v _ (k + 1) i, ← Nat.add_assoc]

/-- For $i \le j \le i + k$, the index shift $\sigma_j$ maps $\{i, \dots, i + k + 1\}$ onto
$\{i, \dots, i + k + 2\} \setminus \{j + 1\}$. -/
theorem map_insertShift (hij : i ≤ j) (hjk : j ≤ i + k) :
    (Finset.Icc i (i + k + 1)).map ⟨insertShift j, insertShift_injective j⟩
      = (Finset.Icc i (i + k + 2)).erase (j + 1) := by
  ext c
  simp only [Finset.mem_map, Finset.mem_Icc, Function.Embedding.coeFn_mk, Finset.mem_erase,
    insertShift]
  constructor
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
    split_ifs with h <;> omega
  · rintro ⟨hne, h1, h2⟩
    rcases le_or_gt c j with h | h
    · exact ⟨c, ⟨h1, by omega⟩, by rw [ite_eq_left h]⟩
    · exact ⟨c - 1, ⟨by omega, by omega⟩, by rw [ite_eq_right (by omega)]; omega⟩

/-- **Boehm's knot-insertion formula for one B-spline, when the new knot lies in its support**: let
the knots be strictly increasing, let $k \ge 1$, $y \in (x_j, x_{j+1})$ and $i \le j \le i + k$.
Then
$$B_{i,k} = \omega_i\, \hat B_{i,k} + (1 - \omega_{i+1})\, \hat B_{i+1,k},$$
where $\hat B$ are the B-splines on the refined knots $\hat x$ and $\omega$ are the weights of
`BSpline.insertKnotWeight`. -/
theorem bspline_eq_insert_comb_of_mem (hx : StrictMono x) (hk : 1 ≤ k)
    (hy : y ∈ Ioo (x j) (x (j + 1))) (hij : i ≤ j) (hjk : j ≤ i + k) (t : ℝ) :
    bspline x k i t
      = insertKnotWeight x k j y i * bspline (insertKnot x j y) k i t
        + (1 - insertKnotWeight x k j y (i + 1)) * bspline (insertKnot x j y) k (i + 1) t := by
  set Y := insertKnot x j y with hYdef
  set g : ℝ → ℝ := fun s => Quadrature.truncPow k s t with hg
  have hY : StrictMono Y := strictMono_insertKnot hx hy
  have hYr : Y i = x i := by rw [hYdef, insertKnot, ite_eq_left hij]
  have hYp : Y (j + 1) = y := by
    rw [hYdef, insertKnot, ite_eq_right (by omega), ite_eq_left rfl]
  have hYq : Y (i + k + 2) = x (i + k + 1) := by
    rw [hYdef, insertKnot, ite_eq_right (by omega), ite_eq_right (by omega)]
    congr 1
  have hxlt : x i < x (i + k + 1) := hx (by omega)
  have hsub : x (i + k + 1) - x i ≠ 0 := sub_ne_zero.2 (by linarith)
  set T : Finset ℕ := Finset.Icc i (i + k + 2) with hT
  have hpT : j + 1 ∈ T := by rw [hT]; simp only [Finset.mem_Icc]; omega
  have hqT : i + k + 2 ∈ T := by rw [hT]; simp only [Finset.mem_Icc]; omega
  have hrT : i ∈ T := by rw [hT]; simp only [Finset.mem_Icc]; omega
  set b : ℝ := (y - x i) / (x (i + k + 1) - x i) with hbdef
  have hb : Y (j + 1) = b * Y (i + k + 2) + (1 - b) * Y i := by
    rw [hYp, hYq, hYr, hbdef]
    field_simp
    ring
  -- the three divided differences
  have hkey := DividedDifference.newtonOn_erase_eq_affine_comb
    (hY.injective.injOn.mono (Set.subset_univ _) : Set.InjOn Y (T : Set ℕ)) hpT hqT hrT hb g
  -- identify the three index sets
  have hTq : T.erase (i + k + 2) = Finset.Icc i (i + k + 1) := by
    rw [hT, show i + k + 2 = (i + k + 1) + 1 from rfl, Finset.Icc_erase_right,
      Finset.Ico_add_one_right_eq_Icc]
  have hTr : T.erase i = Finset.Icc (i + 1) (i + k + 2) := by
    rw [hT, Finset.Icc_erase_left, Finset.Icc_add_one_left_eq_Ioc]
  have hTp : T.erase (j + 1) = (Finset.Icc i (i + k + 1)).map
      ⟨insertShift j, insertShift_injective j⟩ := (map_insertShift hij hjk).symm
  have hYx : Y ∘ insertShift j = x := funext fun m => insertKnot_insertShift x j y m
  have hleft : DividedDifference.newtonOn (T.erase (j + 1)) Y g
      = DividedDifference.newtonOn (Finset.Icc i (i + k + 1)) x g := by
    rw [hTp, DividedDifference.newtonOn_map]
    exact DividedDifference.newtonOn_congr (fun m _ => congrFun hYx m) g
  -- rewrite the three B-splines
  have hBx : bspline x k i t = (x (i + k + 1) - x i)
      * DividedDifference.newtonOn (Finset.Icc i (i + k + 1)) x g :=
    bspline_eq_mul_newtonOn hx hk i t
  have hBY : bspline Y k i t = (Y (i + k + 1) - Y i)
      * DividedDifference.newtonOn (T.erase (i + k + 2)) Y g := by
    rw [hTq]; exact bspline_eq_mul_newtonOn hY hk i t
  have hBY1 : bspline Y k (i + 1) t = (Y (i + k + 2) - Y (i + 1))
      * DividedDifference.newtonOn (T.erase i) Y g := by
    rw [hTr]
    have h := bspline_eq_mul_newtonOn hY hk (i + 1) t
    rwa [show i + 1 + k + 1 = i + k + 2 by omega] at h
  -- the two coefficient identities
  have hA : insertKnotWeight x k j y i * (Y (i + k + 1) - Y i) = y - x i := by
    rcases eq_or_lt_of_le hjk with hje | hjl
    · subst hje
      rw [insertKnotWeight, ite_eq_left le_rfl, hYr, one_mul,
        show Y (i + k + 1) = y by rw [hYdef, insertKnot, ite_eq_right (by omega), ite_eq_left rfl]]
    · have h1 : ¬ i + k ≤ j := by omega
      have h2 : Y (i + k + 1) = x (i + k) := by
        rw [hYdef, insertKnot, ite_eq_right (by omega), ite_eq_right (by omega)]
        congr 1
      have h3 : x (i + k) - x i ≠ 0 := sub_ne_zero.2 (hx (by omega)).ne'
      rw [insertKnotWeight, ite_eq_right h1, ite_eq_left hij, hYr, h2]
      field_simp
  have hB : (1 - insertKnotWeight x k j y (i + 1)) * (Y (i + k + 2) - Y (i + 1))
      = x (i + k + 1) - y := by
    rcases eq_or_lt_of_le hij with hje | hjl
    · have h1 : ¬ i + 1 + k ≤ j := by omega
      have h2 : ¬ i + 1 ≤ j := by omega
      have h5 : Y (i + 1) = y := by
        rw [hYdef, insertKnot, ite_eq_right h2, ite_eq_left (by omega)]
      rw [insertKnotWeight, ite_eq_right h1, ite_eq_right h2, sub_zero, one_mul, hYq, h5]
    · have h1 : ¬ i + 1 + k ≤ j := by omega
      have h2 : i + 1 ≤ j := hjl
      have h3 : Y (i + 1) = x (i + 1) := by rw [hYdef, insertKnot, ite_eq_left h2]
      have h4 : x (i + k + 1) - x (i + 1) ≠ 0 := sub_ne_zero.2 (hx (by omega)).ne'
      rw [insertKnotWeight, ite_eq_right h1, ite_eq_left h2, hYq, h3,
        show i + 1 + k = i + k + 1 by omega]
      field_simp
      ring
  rw [hBx, hBY, hBY1, ← hleft, hkey, ← mul_assoc, ← mul_assoc, hA, hB, hbdef]
  field_simp
  ring

/-- Boehm's formula when the new knot lies to the right of the support of $B_{i,k}$: for strictly
increasing knots, $k \ge 1$, $y \in (x_j, x_{j+1})$ and $i + k + 1 \le j$, the identity
$B_{i,k} = \omega_i\, \hat B_{i,k} + (1 - \omega_{i+1})\, \hat B_{i+1,k}$ holds. Here the
B-spline is unchanged: $B_{i,k} = \hat B_{i,k}$. -/
theorem bspline_eq_insert_comb_of_right (hx : StrictMono x) (hk : 1 ≤ k)
    (hy : y ∈ Ioo (x j) (x (j + 1))) (hji : i + k + 1 ≤ j) (t : ℝ) :
    bspline x k i t
      = insertKnotWeight x k j y i * bspline (insertKnot x j y) k i t
        + (1 - insertKnotWeight x k j y (i + 1)) * bspline (insertKnot x j y) k (i + 1) t := by
  set Y := insertKnot x j y with hYdef
  have hY : StrictMono Y := strictMono_insertKnot hx hy
  have h1 : insertKnotWeight x k j y i = 1 := by
    rw [insertKnotWeight, ite_eq_left (by omega)]
  have h2 : insertKnotWeight x k j y (i + 1) = 1 := by
    rw [insertKnotWeight, ite_eq_left (by omega)]
  have hcongr : ∀ m ∈ Finset.Icc i (i + k + 1), Y m = x m := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [hYdef, insertKnot, ite_eq_left (by omega)]
  rw [h1, h2, one_mul, sub_self, zero_mul, add_zero,
    bspline_eq_mul_newtonOn hY hk i t, bspline_eq_mul_newtonOn hx hk i t,
    DividedDifference.newtonOn_congr hcongr,
    hcongr (i + k + 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩),
    hcongr i (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)]

/-- Boehm's formula when the new knot lies to the left of the support of $B_{i,k}$: for strictly
increasing knots, $k \ge 1$, $y \in (x_j, x_{j+1})$ and $j < i$, the identity $B_{i,k} =
\omega_i\, \hat B_{i,k} + (1 - \omega_{i+1})\, \hat B_{i+1,k}$ holds. Here the B-spline is the
shifted one: $B_{i,k} = \hat B_{i+1,k}$. -/
theorem bspline_eq_insert_comb_of_left (hx : StrictMono x) (hk : 1 ≤ k)
    (hy : y ∈ Ioo (x j) (x (j + 1))) (hij : j < i) (t : ℝ) :
    bspline x k i t
      = insertKnotWeight x k j y i * bspline (insertKnot x j y) k i t
        + (1 - insertKnotWeight x k j y (i + 1)) * bspline (insertKnot x j y) k (i + 1) t := by
  set Y := insertKnot x j y with hYdef
  set g : ℝ → ℝ := fun s => Quadrature.truncPow k s t with hg
  have hY : StrictMono Y := strictMono_insertKnot hx hy
  have h1 : insertKnotWeight x k j y i = 0 := by
    rw [insertKnotWeight, ite_eq_right (by omega), ite_eq_right (by omega)]
  have h2 : insertKnotWeight x k j y (i + 1) = 0 := by
    rw [insertKnotWeight, ite_eq_right (by omega), ite_eq_right (by omega)]
  have hshift : ∀ m, i ≤ m → Y (m + 1) = x m := by
    intro m hm
    rw [hYdef, insertKnot, ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel]
  have hmap : (Finset.Icc i (i + k + 1)).map ⟨fun m => m + 1, add_left_injective 1⟩
      = Finset.Icc (i + 1) (i + k + 2) := by
    ext c
    simp only [Finset.mem_map, Finset.mem_Icc, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
      omega
    · rintro ⟨hc1, hc2⟩
      exact ⟨c - 1, ⟨by omega, by omega⟩, by omega⟩
  have hBY1 : bspline Y k (i + 1) t = (x (i + k + 1) - x i)
      * DividedDifference.newtonOn (Finset.Icc i (i + k + 1)) x g := by
    have h := bspline_eq_mul_newtonOn hY hk (i + 1) t
    rw [show i + 1 + k + 1 = i + k + 2 by omega, ← hmap, DividedDifference.newtonOn_map] at h
    rw [h]
    have hc : DividedDifference.newtonOn (Finset.Icc i (i + k + 1))
        (Y ∘ ⇑(⟨fun m => m + 1, add_left_injective 1⟩ : ℕ ↪ ℕ)) g
        = DividedDifference.newtonOn (Finset.Icc i (i + k + 1)) x g :=
      DividedDifference.newtonOn_congr (fun m hm => hshift m (Finset.mem_Icc.1 hm).1) g
    rw [hc, show i + k + 2 = (i + k + 1) + 1 from rfl, hshift (i + k + 1) (by omega),
      hshift i le_rfl]
  rw [h1, h2, zero_mul, zero_add, sub_zero, one_mul, hBY1, bspline_eq_mul_newtonOn hx hk i t]

/-- **Boehm's knot-insertion formula for one B-spline** (Remark 8.4 of [quarteroni2000numerical];
[Boehm, *Inserting new knots into B-spline curves*][boehm1980inserting]): for strictly
increasing knots, $k \ge 1$ and a new knot $y$ in the interior of the knot interval
$(x_j, x_{j+1})$,
$$B_{i,k} = \omega_i\, \hat B_{i,k} + (1 - \omega_{i+1})\, \hat B_{i+1,k}$$
for every $i$, where $\hat B$ are the B-splines on the refined knots `BSpline.insertKnot x j y`
and $\omega$ are the weights of `BSpline.insertKnotWeight`. -/
theorem bspline_eq_insert_comb (hx : StrictMono x) (hk : 1 ≤ k)
    (hy : y ∈ Ioo (x j) (x (j + 1))) (i : ℕ) (t : ℝ) :
    bspline x k i t
      = insertKnotWeight x k j y i * bspline (insertKnot x j y) k i t
        + (1 - insertKnotWeight x k j y (i + 1)) * bspline (insertKnot x j y) k (i + 1) t := by
  rcases lt_or_ge j i with h | h
  · exact bspline_eq_insert_comb_of_left hx hk hy h t
  · rcases le_or_gt j (i + k) with h2 | h2
    · exact bspline_eq_insert_comb_of_mem hx hk hy h h2 t
    · exact bspline_eq_insert_comb_of_right hx hk hy (by omega) t

/-- The Boehm weights converge with the knots when $x_j < x_{j+1}$, because the only knot-dependent
case $(y - x_i)/(x_{i+k} - x_i)$, for $i \le j < i + k$, has a denominator of at least
$x_{j+1} - x_j > 0$. -/
private theorem tendsto_insertKnotWeight {X : ℕ → ℕ → ℝ} {Z : ℕ → ℝ} (hx : Monotone x)
    (hto : ∀ m, Tendsto (fun n => X n m) atTop (𝓝 (x m))) (hZ : Tendsto Z atTop (𝓝 y))
    (hj : x j < x (j + 1)) (i : ℕ) :
    Tendsto (fun n => insertKnotWeight (X n) k j (Z n) i) atTop
      (𝓝 (insertKnotWeight x k j y i)) := by
  simp only [insertKnotWeight]
  split_ifs with h1 h2
  · exact tendsto_const_nhds
  · have hne : x (i + k) - x i ≠ 0 := by
      have h3 : x i ≤ x j := hx (by omega)
      have h4 : x (j + 1) ≤ x (i + k) := hx (by omega)
      exact sub_ne_zero.2 (by linarith)
    exact (hZ.sub (hto i)).div ((hto (i + k)).sub (hto i)) hne
  · exact tendsto_const_nhds

/-- Boehm's one-spline formula for nondecreasing knots follows from the strictly increasing case by
passing to the limit along knots $X_n$ and new knots $Z_n$ that approach $x$ and $y$ from below. -/
private theorem bspline_eq_insert_comb_of_limits {X : ℕ → ℕ → ℝ} {Z : ℕ → ℝ}
    (hx : Monotone x) (hk : 1 ≤ k) (hy : y ∈ Ico (x j) (x (j + 1)))
    (hXmono : ∀ n, StrictMono (X n)) (hXlt : ∀ n m, X n m < x m)
    (hXto : ∀ m, Tendsto (fun n => X n m) atTop (𝓝 (x m)))
    (hZmem : ∀ n, Z n ∈ Ioo (X n j) (X n (j + 1))) (hZlt : ∀ n, Z n < y)
    (hZto : Tendsto Z atTop (𝓝 y)) (i : ℕ) (t : ℝ) :
    bspline x k i t
      = insertKnotWeight x k j y i * bspline (insertKnot x j y) k i t
        + (1 - insertKnotWeight x k j y (i + 1)) * bspline (insertKnot x j y) k (i + 1) t := by
  have hj : x j < x (j + 1) := lt_of_le_of_lt hy.1 hy.2
  have hins1 : ∀ (v : ℕ → ℝ) (z : ℝ) {m : ℕ}, m ≤ j → insertKnot v j z m = v m :=
    fun v z _ h => by rw [insertKnot, ite_eq_left h]
  have hins2 : ∀ (v : ℕ → ℝ) (z : ℝ), insertKnot v j z (j + 1) = z :=
    fun v z => by rw [insertKnot, ite_eq_right (by omega), ite_eq_left rfl]
  have hins3 : ∀ (v : ℕ → ℝ) (z : ℝ) {m : ℕ}, j + 1 < m → insertKnot v j z m = v (m - 1) :=
    fun v z _ h => by rw [insertKnot, ite_eq_right (by omega), ite_eq_right (by omega)]
  set Y : ℕ → ℝ := insertKnot x j y with hYdef
  set W : ℕ → ℕ → ℝ := fun n => insertKnot (X n) j (Z n) with hWdef
  have hYmono : Monotone Y := monotone_insertKnot hx hy
  have hWmono : ∀ n, StrictMono (W n) := fun n => strictMono_insertKnot (hXmono n) (hZmem n)
  have hWlt : ∀ n m, W n m < Y m := by
    intro n m
    simp only [hWdef, hYdef]
    rcases lt_trichotomy m (j + 1) with h | h | h
    · rw [hins1 _ _ (show m ≤ j by omega), hins1 _ _ (show m ≤ j by omega)]
      exact hXlt n m
    · subst h
      rw [hins2, hins2]
      exact hZlt n
    · rw [hins3 _ _ h, hins3 _ _ h]
      exact hXlt n (m - 1)
  have hWto : ∀ m, Tendsto (fun n => W n m) atTop (𝓝 (Y m)) := by
    intro m
    simp only [hWdef, hYdef]
    rcases lt_trichotomy m (j + 1) with h | h | h
    · rw [hins1 _ _ (show m ≤ j by omega)]
      exact (hXto m).congr fun n => (hins1 _ _ (show m ≤ j by omega)).symm
    · subst h
      rw [hins2]
      exact hZto.congr fun n => (hins2 _ _).symm
    · rw [hins3 _ _ h]
      exact (hXto (m - 1)).congr fun n => (hins3 _ _ h).symm
  have hB := tendsto_bspline_of_tendsto hx (fun n => (hXmono n).monotone) hXlt hXto k i t
  have hBY := tendsto_bspline_of_tendsto hYmono (fun n => (hWmono n).monotone) hWlt hWto k i t
  have hBY1 :=
    tendsto_bspline_of_tendsto hYmono (fun n => (hWmono n).monotone) hWlt hWto k (i + 1) t
  have hw := tendsto_insertKnotWeight (k := k) hx hXto hZto hj i
  have hw1 := tendsto_insertKnotWeight (k := k) hx hXto hZto hj (i + 1)
  have hRHS : Tendsto (fun n => insertKnotWeight (X n) k j (Z n) i * bspline (W n) k i t
      + (1 - insertKnotWeight (X n) k j (Z n) (i + 1)) * bspline (W n) k (i + 1) t) atTop
      (𝓝 (insertKnotWeight x k j y i * bspline Y k i t
        + (1 - insertKnotWeight x k j y (i + 1)) * bspline Y k (i + 1) t)) :=
    (hw.mul hBY).add ((tendsto_const_nhds.sub hw1).mul hBY1)
  exact tendsto_nhds_unique
    (hB.congr fun n => bspline_eq_insert_comb (hXmono n) hk (hZmem n) i t) hRHS

/-- **Boehm's knot-insertion formula for one B-spline, for a new knot that need not be interior**
(Remark 8.4 of [quarteroni2000numerical]; [boehm1980inserting]): for nondecreasing knots,
$k \ge 1$ and a new knot $y \in [x_j, x_{j+1})$,
$$B_{i,k} = \omega_i\, \hat B_{i,k} + (1 - \omega_{i+1})\, \hat B_{i+1,k}$$
for every $i$. The case $y = x_j$, which raises the multiplicity of an existing knot, is
allowed.

The divided-difference proof of `BSpline.bspline_eq_insert_comb` needs distinct knots, and at
$y = x_j$ the refined sequence has a double knot. Here both sides are limits of the strictly
increasing case: the knots $X_n(m) = x_m - 2^{-m}(x_{j+1} - y)/(n + 1)$ are strictly increasing
and approach $x$ from below, the new knots $Z_n = y - (y - X_n(j))/(n + 2)$ lie in
$(X_n(j), X_n(j+1))$ and approach $y$ from below, and `BSpline.tendsto_bspline_of_tendsto`
passes to the limit. -/
theorem bspline_eq_insert_comb_of_monotone (hx : Monotone x) (hk : 1 ≤ k)
    (hy : y ∈ Ico (x j) (x (j + 1))) (i : ℕ) (t : ℝ) :
    bspline x k i t
      = insertKnotWeight x k j y i * bspline (insertKnot x j y) k i t
        + (1 - insertKnotWeight x k j y (i + 1)) * bspline (insertKnot x j y) k (i + 1) t := by
  have hD : (0 : ℝ) < x (j + 1) - y := sub_pos.2 hy.2
  set X : ℕ → ℕ → ℝ :=
    fun n m => x m - (1 / 2 : ℝ) ^ m * ((x (j + 1) - y) / ((n : ℝ) + 1)) with hXdef
  set Z : ℕ → ℝ := fun n => y - (y - X n j) / ((n : ℝ) + 2) with hZdef
  have hq : ∀ n : ℕ, (0 : ℝ) < (x (j + 1) - y) / ((n : ℝ) + 1) := fun n => by positivity
  have hpow : ∀ m : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ m := fun m => by positivity
  have hXlt : ∀ n m, X n m < x m := by
    intro n m
    have := mul_pos (hpow m) (hq n)
    simp only [hXdef]
    linarith
  have hXmono : ∀ n, StrictMono (X n) := by
    intro n
    refine strictMono_nat_of_lt_succ fun m => ?_
    have h1 : x m ≤ x (m + 1) := hx (by omega)
    have h2 := hpow m
    have h3 := hq n
    simp only [hXdef, pow_succ]
    nlinarith
  have hXto : ∀ m, Tendsto (fun n => X n m) atTop (𝓝 (x m)) := by
    have h0 : Tendsto (fun n : ℕ => (x (j + 1) - y) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (x (j + 1) - y)
      simpa [div_eq_mul_inv] using h
    intro m
    have h1 := tendsto_const_nhds (x := x m) |>.sub (h0.const_mul ((1 / 2 : ℝ) ^ m))
    simp only [hXdef]
    simpa using h1
  have hyX : ∀ n, X n j < y := fun n => lt_of_lt_of_le (hXlt n j) hy.1
  have hZlt : ∀ n, Z n < y := by
    intro n
    have h1 : (0 : ℝ) < (y - X n j) / ((n : ℝ) + 2) :=
      div_pos (by linarith [hyX n]) (by positivity)
    simp only [hZdef]
    linarith
  have hZ1 : ∀ n, X n j < Z n := by
    intro n
    have h1 : (0 : ℝ) < y - X n j := by linarith [hyX n]
    have h2 : (1 : ℝ) < (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have h3 := div_lt_self h1 h2
    simp only [hZdef]
    linarith
  have hZ2 : ∀ n, Z n < X n (j + 1) := by
    intro n
    have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h2 := hq n
    have h3 : (x (j + 1) - y) / ((n : ℝ) + 1) ≤ x (j + 1) - y :=
      div_le_self hD.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have h4 : y < X n (j + 1) := by
      simp only [hXdef, pow_succ]
      nlinarith [hpow j]
    exact lt_trans (hZlt n) h4
  have hZto : Tendsto Z atTop (𝓝 y) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h3 : Tendsto (fun n => (y - X n j) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      (tendsto_const_nhds.sub (hXto j)).div_atTop hden
    simp only [hZdef]
    simpa using tendsto_const_nhds (x := y) |>.sub h3
  exact bspline_eq_insert_comb_of_limits hx hk hy hXmono hXlt hXto
    (fun n => ⟨hZ1 n, hZ2 n⟩) hZlt hZto i t

/-- Given the one-spline identity of Boehm's algorithm for every index and $k \le j < N$, the spline
$\sum_{i < N} c_i B_{i,k}$ equals $\sum_{i < N+1} d_i \hat B_{i,k}$ with the Boehm coefficients
$d_i$, because these hypotheses give the boundary weights $\omega_0 = 1$ and $\omega_N = 0$. -/
private theorem sum_smul_bspline_insert_of_comb {Y : ℕ → ℝ}
    (hcomb : ∀ i, bspline x k i t = insertKnotWeight x k j y i * bspline Y k i t
      + (1 - insertKnotWeight x k j y (i + 1)) * bspline Y k (i + 1) t)
    (hkj : k ≤ j) {N : ℕ} (hjN : j < N) (c : ℕ → ℝ) :
    ∑ i ∈ Finset.range (N + 1), insertKnotCoeff x k j y c i * bspline Y k i t
      = ∑ i ∈ Finset.range N, c i * bspline x k i t := by
  set a : ℕ → ℝ := insertKnotWeight x k j y with ha
  have ha0 : a 0 = 1 := by rw [ha, insertKnotWeight, ite_eq_left (by omega)]
  have haN : a N = 0 := by
    rw [ha, insertKnotWeight, ite_eq_right (by omega), ite_eq_right (by omega)]
  have hL : ∑ i ∈ Finset.range (N + 1), insertKnotCoeff x k j y c i * bspline Y k i t
      = (∑ i ∈ Finset.range (N + 1), a i * c i * bspline Y k i t)
        + ∑ i ∈ Finset.range (N + 1), (1 - a i) * c (i - 1) * bspline Y k i t := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [insertKnotCoeff, ← ha]; ring
  have hL1 : ∑ i ∈ Finset.range (N + 1), a i * c i * bspline Y k i t
      = ∑ i ∈ Finset.range N, a i * c i * bspline Y k i t := by
    rw [Finset.sum_range_succ, haN, zero_mul, zero_mul, add_zero]
  have hL2 : ∑ i ∈ Finset.range (N + 1), (1 - a i) * c (i - 1) * bspline Y k i t
      = ∑ i ∈ Finset.range N, (1 - a (i + 1)) * c i * bspline Y k (i + 1) t := by
    rw [Finset.sum_range_succ' (fun i => (1 - a i) * c (i - 1) * bspline Y k i t) N, ha0,
      sub_self, zero_mul, zero_mul, add_zero]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_sub_cancel]
  have hR : ∑ i ∈ Finset.range N, c i * bspline x k i t
      = (∑ i ∈ Finset.range N, a i * c i * bspline Y k i t)
        + ∑ i ∈ Finset.range N, (1 - a (i + 1)) * c i * bspline Y k (i + 1) t := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcomb i]
    ring
  rw [hL, hL1, hL2, hR]

/-- **Knot insertion preserves the spline** (Remark 8.4 of [quarteroni2000numerical]): let the knots
be strictly increasing, let $k \ge 1$, and let the new knot $y$ lie in the interior of the knot
interval $(x_j, x_{j+1})$, with $k \le j < N$. Then for all coefficients $c_0, \dots, c_{N-1}$
and every $t \in \mathbb{R}$,
$$\sum_{i=0}^{N} d_i\, \hat B_{i,k}(t) = \sum_{i=0}^{N-1} c_i B_{i,k}(t),$$
where $\hat B$ are the B-splines on the refined knots and
$d_i = \omega_i c_i + (1 - \omega_i)\, c_{i-1}$ are the coefficients of
`BSpline.insertKnotCoeff`. -/
theorem sum_smul_bspline_insertKnot (hx : StrictMono x) (hk : 1 ≤ k)
    (hy : y ∈ Ioo (x j) (x (j + 1))) (hkj : k ≤ j) {N : ℕ} (hjN : j < N) (c : ℕ → ℝ) (t : ℝ) :
    ∑ i ∈ Finset.range (N + 1), insertKnotCoeff x k j y c i * bspline (insertKnot x j y) k i t
      = ∑ i ∈ Finset.range N, c i * bspline x k i t :=
  sum_smul_bspline_insert_of_comb (fun i => bspline_eq_insert_comb hx hk hy i t) hkj hjN c

/-- **Knot insertion preserves the spline, for a new knot that need not be interior** (Remark 8.4 of
[quarteroni2000numerical]): the identity of `BSpline.sum_smul_bspline_insertKnot` holds for
nondecreasing knots, $k \ge 1$ and a new knot $y \in [x_j, x_{j+1})$ with $k \le j < N$, for all
coefficients and every $t$. This is the range that the source states.

The case $y = x_j$ raises the multiplicity of an existing knot. The condition $x_j < x_{j+1}$,
which follows from $y \in [x_j, x_{j+1})$, says that the knot interval that receives the new
knot is nonempty. -/
theorem sum_smul_bspline_insertKnot_of_monotone (hx : Monotone x) (hk : 1 ≤ k)
    (hy : y ∈ Ico (x j) (x (j + 1))) (hkj : k ≤ j) {N : ℕ} (hjN : j < N) (c : ℕ → ℝ) (t : ℝ) :
    ∑ i ∈ Finset.range (N + 1), insertKnotCoeff x k j y c i * bspline (insertKnot x j y) k i t
      = ∑ i ∈ Finset.range N, c i * bspline x k i t :=
  sum_smul_bspline_insert_of_comb
    (fun i => bspline_eq_insert_comb_of_monotone hx hk hy i t) hkj hjN c

end KnotInsertion

end BSpline
