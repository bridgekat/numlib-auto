import Mathlib.Analysis.Convex.Combination
import Numlib.Approximation.DividedDifference
import Numlib.Approximation.NewtonForm
import Numlib.Approximation.Spline

/-!
# B-splines

The normalized B-splines `B_{i,k}` of degree `k` on a nondecreasing knot sequence `x : ℕ → ℝ`,
*defined* by the Cox–de Boor recursion ([quarteroni2000numerical] (8.54)) and *characterized*, at
distinct knots, as the scaled divided differences of the truncated power `s ↦ (s - t)_+^k`
([quarteroni2000numerical] Definition 8.2, (8.51)–(8.53)); their support, nonnegativity, partition
of unity, piecewise polynomial structure and smoothness; the B-spline basis of the spline space of
`Numlib/Approximation/Spline` on an extended knot sequence with `k` further knots at each end
((8.55)–(8.56)); B-splines with coincident knots (Remark 8.3), the cubic B-spline on uniform knots
(Example 8.9), Boehm's knot insertion (Remark 8.4), and parametric B-spline curves with their
locality and convex-hull properties (§8.7.1). References beyond the book: de Boor, *A Practical
Guide to Splines*, chapters IX–XI.

## Design

* The recursion is the definition because it makes sense for *nondecreasing* knots, coincident
  ones included, with the convention `0/0 = 0` in the weights
  `ω_{i,d}(t) = (t - x_i)/(x_{i+d} - x_i)` (`BSpline.weight`). The divided-difference form of
  Definition 8.2 needs distinct knots and is the theorem `BSpline.bspline_eq_mul_newton_truncPow`.
  `bspline x k i` is the book's `B_{i,k+1}` (their second index is the *order* `k + 1`).
* The degree-`0` B-spline is the indicator of the half-open `[x_i, x_{i+1})`, so that the partition
  of unity holds pointwise on `[x_k, x_{n+1})`; the book's closed interval in (8.54) cannot be right
  at the shared knots.
* Knots are indexed by `ℕ`; the book's `x_{-k}, …, x_{n+k}` of (8.55) are shifted by `k`, so the
  data knots are `x_k = a < x_{k+1} < ⋯ < x_{n+k} = b` and the `n + k` basis splines are
  `bspline x k i` for `i < n + k`.
* Curves take values in an arbitrary real vector space `E`; the control points are `P : ℕ → E`.

## Main results

* `BSpline.bspline_eq_zero_of_notMem`, `BSpline.bspline_nonneg`, `BSpline.bspline_pos`,
  `BSpline.sum_bspline`, `BSpline.exists_eqOn_bspline`: support, positivity, partition of unity,
  piecewise polynomial.
* `BSpline.bspline_eq_mul_newton_truncPow` and `BSpline.bspline_eq_sum_truncPow`: Definition 8.2
  and (8.53) as theorems, through the divided-difference form of the Cox–de Boor recursion.
* `BSpline.contDiff_bspline`, `BSpline.bspline_mem_splineSpace`,
  `BSpline.linearIndependent_bspline`, `BSpline.exists_basis_bspline`: smoothness `C^{k-1}` at
  simple knots and the B-spline basis of the spline space.
* `BSpline.linearIndependent_X_sub_C_pow`,
  `BSpline.exists_eq_smul_of_sum_C_mul_X_sub_C_pow_eq_zero`,
  `BSpline.exists_sum_C_mul_X_sub_C_pow_eq_zero_and_eqOn` and `BSpline.exists_eq_smul_bspline`:
  Schoenberg's characterization of `B_{i,k}` as the unique (up to a scalar) `C^{k-1}` spline of
  degree `k` supported in `[x_i, x_{i+k+1}]`, through the one-dimensional kernel of
  `c ↦ ∑_j c_j (X - x_j)^k` on `k + 2` distinct knots (a Vandermonde argument).
* `BSpline.bspline_apply_of_coincident_left`, `BSpline.bspline_apply_of_coincident_right`,
  `BSpline.sum_smul_bspline_left`, `BSpline.sum_smul_bspline_right`: coincident knots and the
  endpoint values (8.57); `BSpline.bspline_uniform_cubic`: Example 8.9.
* `BSpline.insertKnot`, `BSpline.insertKnotCoeff`, `BSpline.bspline_eq_insert_comb` and
  `BSpline.sum_smul_bspline_insertKnot`: Boehm's knot insertion, for strictly increasing knots
  and a new knot interior to its panel.
* `BSpline.tendsto_bspline_of_tendsto`, `BSpline.bspline_eq_insert_comb_of_monotone` and
  `BSpline.sum_smul_bspline_insertKnot_of_monotone`: continuity of a B-spline in knots approached
  from below, and Boehm's algorithm on the book's full range — nondecreasing knots and a new knot
  `y ∈ [x_j, x_{j+1})`, so that an existing knot may have its multiplicity raised.
* `BSpline.curve`, `BSpline.curve_mem_convexHull`, `BSpline.curve_update_eq_of_notMem`: parametric
  B-spline curves.

## Implementation notes

Two divided-difference identities — the recursion `f[x_0, …, x_{m+1}]
= (f[x_1, …, x_{m+1}] - f[x_0, …, x_m])/(x_{m+1} - x_0)` and the Leibniz rule for an affine factor
`((· - t) g)[x_0, …, x_{m+1}] = (x_0 - t) g[x_0, …, x_{m+1}] + g[x_1, …, x_{m+1}]` — are proved here
privately from the explicit sum defining `DividedDifference.newton`; they belong to
`Numlib/Approximation/NewtonForm` (`newton_succ`, `newton_mul`) and should be replaced by those once
that module exists.
-/

open Filter Polynomial Set
open scoped Topology

namespace BSpline

variable {x : ℕ → ℝ} {k i n d : ℕ} {t : ℝ}

/-- The Cox–de Boor weight `ω_{i,d}(t) = (t - x_i)/(x_{i+d} - x_i)`, taken to be `0` when the two
knots coincide (de Boor's convention `0/0 = 0`). -/
noncomputable def weight (x : ℕ → ℝ) (i d : ℕ) (t : ℝ) : ℝ :=
  if x (i + d) = x i then 0 else (t - x i) / (x (i + d) - x i)

/-- **The normalized B-spline of degree `k`** on the knots `x_i, …, x_{i+k+1}`, by the Cox–de Boor
recursion ([quarteroni2000numerical] (8.54)): `B_{i,0}` is the indicator of `[x_i, x_{i+1})` and
`B_{i,d+1} = ω_{i,d+1} B_{i,d} + (1 - ω_{i+1,d+1}) B_{i+1,d}`. The book's `B_{i,k+1}` (degree `k`)
is `bspline x k i`. -/
noncomputable def bspline (x : ℕ → ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, i, t => if t ∈ Ico (x i) (x (i + 1)) then 1 else 0
  | d + 1, i, t => weight x i (d + 1) t * bspline x d i t
      + (1 - weight x (i + 1) (d + 1) t) * bspline x d (i + 1) t

/-- The degree-`0` B-spline is the indicator of `[x_i, x_{i+1})`. -/
theorem bspline_zero (x : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    bspline x 0 i t = if t ∈ Ico (x i) (x (i + 1)) then 1 else 0 := rfl

/-- **The Cox–de Boor recursion** ([quarteroni2000numerical] (8.54)). -/
theorem bspline_succ (x : ℕ → ℝ) (d i : ℕ) (t : ℝ) :
    bspline x (d + 1) i t = weight x i (d + 1) t * bspline x d i t
      + (1 - weight x (i + 1) (d + 1) t) * bspline x d (i + 1) t := rfl

/-- **Support**: a B-spline vanishes outside `[x_i, x_{i+k+1})`. -/
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

/-- On the support of `B_{i,d}` the weight `ω_{i,d+1}` lies in `[0, 1]`. -/
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

/-- **Positivity** ([quarteroni2000numerical] §8.6.2, quoted from de Boor): `0 ≤ B_{i,k}(t)`. -/
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

/-- Every point of `[x_0, x_{n+1})` lies in exactly one half-open knot interval `[x_i, x_{i+1})`,
`i ≤ n`: the degree-`0` B-splines sum to one there. -/
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

/-- **Partition of unity** ([quarteroni2000numerical] §8.6.2): on `[x_k, x_{n+1})` the B-splines
`B_{0,k}, …, B_{n,k}` sum to one. Each step of the recursion regroups the sum by the degree-`d`
B-splines, whose coefficients `ω_{j,d+1} + (1 - ω_{j,d+1})` are `1`, the two boundary terms
vanishing on the range of `t`. -/
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

/-- The Cox–de Boor weight as a polynomial in `t`. -/
noncomputable def weightPoly (x : ℕ → ℝ) (i d : ℕ) : ℝ[X] :=
  if x (i + d) = x i then 0 else C (1 / (x (i + d) - x i)) * (X - C (x i))

/-- The weight polynomial evaluates to the weight. -/
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

/-- **Piecewise polynomial** ([quarteroni2000numerical] §8.6.2): on each knot interval a B-spline
of degree `k` is a polynomial of degree at most `k`. -/
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

/-- **Positivity on the open support**: for strictly increasing knots, `B_{i,k}(t) > 0` for every
`t ∈ (x_i, x_{i+k+1})`. By induction on `k` through the Cox–de Boor recursion: one of the two
terms has a positive weight and a positive B-spline of degree `k - 1`, the other is nonnegative. -/
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

/-! ### Divided differences of truncated powers

The two divided-difference identities used below are proved from the explicit sum defining
`DividedDifference.newton`; they are planned for `Numlib/Approximation/NewtonForm` (as
`DividedDifference.newton_succ` and the Leibniz rule `DividedDifference.newton_mul`) and should be
replaced by those once that module exists. -/

section DividedDifference

open DividedDifference

/-- The weight `∏_{j ≠ i} (v i - v j)` of the node `i` in the Newton divided difference. -/
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

/-- The weight of a node other than the first, relative to the weight in the tail sequence. -/
private theorem wt_succ {m : ℕ} (v : Fin (m + 2) → ℝ) (i : Fin (m + 1)) :
    wt v i.succ = (v i.succ - v 0) * wt (Fin.tail v) i := by
  simp only [wt, prod_erase_eq_prod_ite, Fin.prod_univ_succ, Fin.succ_inj, Fin.tail,
    (Fin.succ_ne_zero i).symm, ↓reduceIte]

/-- The weight of a node other than the last, relative to the weight in the initial sequence. -/
private theorem wt_castSucc {m : ℕ} (v : Fin (m + 2) → ℝ) (i : Fin (m + 1)) :
    wt v i.castSucc = (v i.castSucc - v (Fin.last (m + 1))) * wt (Fin.init v) i := by
  rw [wt, wt, prod_erase_eq_prod_ite, prod_erase_eq_prod_ite,
    Fin.prod_univ_castSucc
      (fun j : Fin (m + 2) => if j = i.castSucc then 1 else v i.castSucc - v j),
    ite_eq_right (Fin.castSucc_lt_last i).ne']
  simp only [Fin.castSucc_inj, Fin.init]
  ring

-- TODO(NewtonForm): this is `DividedDifference.newton_succ` of `Numlib/Approximation/NewtonForm`.
/-- **The recursion for divided differences**
`f[x_0, …, x_{m+1}] = (f[x_1, …, x_{m+1}] - f[x_0, …, x_m])/(x_{m+1} - x_0)`
([quarteroni2000numerical] (8.19)). -/
private theorem newton_succ {m : ℕ} (f : ℝ → ℝ) {v : Fin (m + 2) → ℝ} (hv : Function.Injective v) :
    newton f v
      = (newton f (Fin.tail v) - newton f (Fin.init v)) / (v (Fin.last (m + 1)) - v 0) := by
  have hne : v (Fin.last (m + 1)) - v 0 ≠ 0 :=
    sub_ne_zero.mpr fun h => absurd (hv h) (Fin.last_pos' (n := m + 1)).ne'
  rw [eq_div_iff hne, newton_eq_sum_div, newton_eq_sum_div, newton_eq_sum_div]
  have htail : ∑ i : Fin (m + 1), f (Fin.tail v i) / wt (Fin.tail v) i
      = ∑ j : Fin (m + 2), f (v j) * (v j - v 0) / wt v j := by
    rw [Fin.sum_univ_succ (fun j : Fin (m + 2) => f (v j) * (v j - v 0) / wt v j)]
    simp only [sub_self, mul_zero, zero_div, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wt_succ, Fin.tail]
    have := wt_ne_zero hv i.succ
    have h2 : v i.succ - v 0 ≠ 0 :=
      sub_ne_zero.mpr fun h => absurd (hv h) (Fin.succ_ne_zero i)
    rw [wt_succ] at this
    have h3 : wt (Fin.tail v) i ≠ 0 := right_ne_zero_of_mul this
    field_simp
  have hinit : ∑ i : Fin (m + 1), f (Fin.init v i) / wt (Fin.init v) i
      = ∑ j : Fin (m + 2), f (v j) * (v j - v (Fin.last (m + 1))) / wt v j := by
    rw [Fin.sum_univ_castSucc
      (fun j : Fin (m + 2) => f (v j) * (v j - v (Fin.last (m + 1))) / wt v j)]
    simp only [sub_self, mul_zero, zero_div, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [wt_castSucc, Fin.init]
    have := wt_ne_zero hv i.castSucc
    have h2 : v i.castSucc - v (Fin.last (m + 1)) ≠ 0 :=
      sub_ne_zero.mpr fun h => absurd (hv h) (Fin.castSucc_lt_last i).ne
    rw [wt_castSucc] at this
    have h3 : wt (Fin.init v) i ≠ 0 := right_ne_zero_of_mul this
    field_simp
  rw [htail, hinit, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := wt_ne_zero hv j
  field_simp
  ring

-- TODO(NewtonForm): the Leibniz rule `DividedDifference.newton_mul` with an affine first factor.
/-- **The Leibniz rule for an affine factor**:
`((· - t) g)[x_0, …, x_{m+1}] = (x_0 - t) g[x_0, …, x_{m+1}] + g[x_1, …, x_{m+1}]`. -/
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

/-- The truncated power of degree `k + 1` factors as `(s - t) (s - t)_+^k`. -/
theorem truncPow_succ (k : ℕ) (s t : ℝ) :
    Quadrature.truncPow (k + 1) s t = (s - t) * Quadrature.truncPow k s t := by
  unfold Quadrature.truncPow
  split_ifs <;> ring

/-- **The divided-difference form of the B-spline** ([quarteroni2000numerical] (8.51)):
`(x_{i+k+1} - x_i) g[x_i, …, x_{i+k+1}]` with `g(s) = (s - t)_+^k`. It coincides with
`bspline x k i t` for `1 ≤ k` at distinct knots (`nform_eq_bspline`); for `k = 0` it is the
indicator of the half-open `(x_i, x_{i+1}]`, which differs from `bspline x 0 i` at the knots. -/
noncomputable def nform (x : ℕ → ℝ) (k i : ℕ) (t : ℝ) : ℝ :=
  (x (i + k + 1) - x i) *
    DividedDifference.newton (fun s => Quadrature.truncPow k s t) fun j : Fin (k + 2) => x (i + j)

/-- The node sequence `x_i, …, x_{i+k+1}` of distinct knots is injective. -/
theorem injective_nodes (hx : StrictMono x) (k i : ℕ) :
    Function.Injective fun j : Fin (k + 2) => x (i + j) := fun _ _ h =>
  Fin.ext (by simpa using hx.injective h)

/-- The Newton divided difference at the two nodes `x_i, x_{i+1}`. -/
theorem newton_two (g : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) :
    DividedDifference.newton g (fun j : Fin (0 + 2) => x (i + j))
      = g (x i) / (x i - x (i + 1)) + g (x (i + 1)) / (x (i + 1) - x i) := by
  simp only [DividedDifference.newton, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one]
  rw [show (Finset.univ.erase (0 : Fin (0 + 2))) = {1} from rfl,
    show (Finset.univ.erase (1 : Fin (0 + 2))) = {0} from rfl]
  simp

/-- The degree-`0` divided-difference form is the indicator of `(x_i, x_{i+1}]`. -/
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

/-- The tail of the node sequence `x_i, …, x_{i+d+2}` is the node sequence starting at `i + 1`. -/
theorem tail_nodes (x : ℕ → ℝ) (d i : ℕ) :
    Fin.tail (fun j : Fin (d + 3) => x (i + j)) = fun j : Fin (d + 2) => x (i + 1 + j) :=
  funext fun j => by simp only [Fin.tail, Fin.val_succ]; congr 1; omega

/-- The initial segment of the node sequence `x_i, …, x_{i+d+2}` is the node sequence of one degree
less. -/
theorem init_nodes (x : ℕ → ℝ) (d i : ℕ) :
    Fin.init (fun j : Fin (d + 3) => x (i + j)) = fun j : Fin (d + 2) => x (i + j) :=
  funext fun j => by simp only [Fin.init, Fin.val_castSucc]

/-- **The Cox–de Boor recursion for the divided-difference form** (de Boor, *A Practical Guide to
Splines*, chapter IX, (13)–(14)): from `(s - t)_+^{d+1} = (s - t) (s - t)_+^d`, the Leibniz rule
for the affine factor and the recursion for divided differences. -/
theorem nform_succ (hx : StrictMono x) (d i : ℕ) (t : ℝ) :
    nform x (d + 1) i t = weight x i (d + 1) t * nform x d i t
      + (1 - weight x (i + 1) (d + 1) t) * nform x d (i + 1) t := by
  have hv := injective_nodes hx (d + 1) i
  have hg : (fun s => Quadrature.truncPow (d + 1) s t)
      = fun s => (s - t) * Quadrature.truncPow d s t := funext fun s => truncPow_succ d s t
  have hrec := newton_succ (fun s => Quadrature.truncPow d s t) hv
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

/-- The divided-difference form and the B-spline agree in degree `1`: both are the hat function of
the knots `x_i < x_{i+1} < x_{i+2}`. -/
theorem nform_one (hx : StrictMono x) (i : ℕ) (t : ℝ) : nform x 1 i t = bspline x 1 i t := by
  rw [nform_succ hx, bspline_succ, nform_zero hx, nform_zero hx, bspline_zero, bspline_zero]
  have h01 : x i < x (i + 1) := hx (by omega)
  have h12 : x (i + 1) < x (i + 1 + 1) := hx (by omega)
  have hw1 : weight x i 1 t = (t - x i) / (x (i + 1) - x i) := by
    simp [weight, h01.ne']
  have hw2 : weight x (i + 1) 1 t = (t - x (i + 1)) / (x (i + 1 + 1) - x (i + 1)) := by
    simp [weight, h12.ne']
  rw [hw1, hw2]
  have h02 : x i < x (i + 1 + 1) := h01.trans h12
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

/-- **Definition 8.2 as a theorem**: at distinct knots and `1 ≤ k`, the B-spline of the Cox–de
Boor recursion is the divided-difference form `(x_{i+k+1} - x_i) g[x_i, …, x_{i+k+1}]` with
`g(s) = (s - t)_+^k`. -/
theorem nform_eq_bspline (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) :
    nform x k i = bspline x k i := by
  induction k, hk using Nat.le_induction generalizing i with
  | base => exact funext fun t => nform_one hx i t
  | succ d hd ih =>
    funext t
    rw [nform_succ hx, bspline_succ, ih i, ih (i + 1)]

/-- **Definition 8.2** ([quarteroni2000numerical] (8.51)–(8.52)): for strictly increasing knots
and `1 ≤ k`, `B_{i,k}(t) = (x_{i+k+1} - x_i) g[x_i, …, x_{i+k+1}]` with `g(s) = (s - t)_+^k`. -/
theorem bspline_eq_mul_newton_truncPow (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) (t : ℝ) :
    bspline x k i t = (x (i + k + 1) - x i) *
      DividedDifference.newton (fun s => Quadrature.truncPow k s t)
        (fun j : Fin (k + 2) => x (i + j)) :=
  (congrFun (nform_eq_bspline hx hk i) t).symm

/-- **The explicit form of the B-spline** ([quarteroni2000numerical] (8.53)):
`B_{i,k}(t) = (x_{i+k+1} - x_i) ∑_{j=0}^{k+1} (x_{i+j} - t)_+^k / ∏_{l ≠ j} (x_{i+j} - x_{i+l})`. -/
theorem bspline_eq_sum_truncPow (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) (t : ℝ) :
    bspline x k i t = (x (i + k + 1) - x i) * ∑ j : Fin (k + 2),
      Quadrature.truncPow k (x (i + j)) t / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l)) :=
  bspline_eq_mul_newton_truncPow hx hk i t

/-! ### Smoothness and membership in the spline space -/

/-- `t ↦ (c - t)_+^k` is of class `C^{k-1}` for `1 ≤ k`. -/
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

/-- **Smoothness at simple knots** ([quarteroni2000numerical] §8.6.2): for strictly increasing
knots and `1 ≤ k`, `B_{i,k}` is of class `C^{k-1}` on `ℝ`, being a combination of the functions
`t ↦ (x_j - t)_+^k`. -/
theorem contDiff_bspline (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) :
    ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) (bspline x k i) := by
  have : bspline x k i = fun t => (x (i + k + 1) - x i) * ∑ j : Fin (k + 2),
      Quadrature.truncPow k (x (i + j)) t / ∏ l ∈ Finset.univ.erase j, (x (i + j) - x (i + l)) :=
    funext fun t => bspline_eq_sum_truncPow hx hk i t
  rw [this]
  exact contDiff_const.mul (ContDiff.sum fun j _ => (contDiff_truncPow_flip _ hk).div_const _)

/-- **A B-spline is a spline** ([quarteroni2000numerical] §8.6.2): for strictly increasing knots
with the data knots `x_k = a < ⋯ < x_{n+k} = b` and `1 ≤ k`, the restriction of `B_{i,k}` to
`[a, b]` lies in `S_k = S_k^{k-1}` of the partition `j ↦ x (j + k)`. -/
theorem bspline_mem_splineSpace {a b : ℝ} (hx : StrictMono x) (hk : 1 ≤ k) (i : ℕ) :
    (ContinuousMap.mk _ (contDiff_bspline hx hk i).continuous).restrict (Icc a b) ∈
      Spline.splineSpace a b n (fun j => x (j + k)) k (k - 1) := by
  refine ⟨bspline x k i, (contDiff_bspline hx hk i).contDiffOn, fun _ => rfl, fun j hj => ?_⟩
  obtain ⟨p, hpd, hpe⟩ := exists_eqOn_bspline (k := k) (i := i) hx.monotone (j + k)
  refine ⟨p, hpd, ?_⟩
  have hlt : x (j + k) < x (j + k + 1) := hx (Nat.lt_succ_self _)
  change EqOn _ _ (Icc (x (j + k)) (x (j + 1 + k)))
  rw [show j + 1 + k = j + k + 1 by omega]
  exact hpe.of_subset_closure (contDiff_bspline hx hk i).continuous.continuousOn
    p.continuous.continuousOn Ico_subset_Icc_self (by rw [closure_Ico hlt.ne])

/-! ### The derivative recursion and linear independence -/

/-- `t ↦ (c - t)_+^{k+1}` has derivative `-(k + 1) (c - t)_+^k` away from `c`. -/
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

/-- Away from the knots the divided-difference form of degree `0` is the B-spline of degree `0`. -/
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

/-- **The derivative of a B-spline** (de Boor, *A Practical Guide to Splines*, chapter X, (12)):
away from the knots,
`B_{i,k+1}' = (k + 1) (B_{i,k}/(x_{i+k+1} - x_i) - B_{i+1,k}/(x_{i+k+2} - x_{i+1}))`. -/
theorem hasDerivAt_bspline (hx : StrictMono x) (ht : ∀ m, t ≠ x m) (k i : ℕ) :
    HasDerivAt (bspline x (k + 1) i)
      (((k : ℝ) + 1) * (bspline x k i t / (x (i + k + 1) - x i)
        - bspline x k (i + 1) t / (x (i + 1 + k + 1) - x (i + 1)))) t := by
  rw [← nform_eq_bspline hx (by omega) i, ← nform_eq_bspline_of_ne hx ht k i,
    ← nform_eq_bspline_of_ne hx ht k (i + 1)]
  have hv := injective_nodes hx (k + 1) i
  have hrec := newton_succ (fun s => Quadrature.truncPow k s t) hv
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

/-- Points of the open knot interval `(x_j, x_{j+1})` are not knots. -/
theorem ne_of_mem_Ioo (hx : StrictMono x) {j : ℕ} (ht : t ∈ Ioo (x j) (x (j + 1))) (m : ℕ) :
    t ≠ x m := by
  intro h
  rcases le_or_gt m j with hm | hm
  · exact absurd (h ▸ ht.1) (not_lt.mpr (hx.monotone hm))
  · exact absurd (h ▸ ht.2) (not_lt.mpr (hx.monotone hm))

/-- A B-spline `B_{i,k}` with `i + k + 1 ≤ j` vanishes on `(x_j, x_{j+1})`. -/
theorem bspline_eq_zero_of_add_le (hx : StrictMono x) {j : ℕ} (ht : t ∈ Ioo (x j) (x (j + 1)))
    (hi : i + k + 1 ≤ j) : bspline x k i t = 0 :=
  bspline_eq_zero_of_notMem hx.monotone fun h =>
    absurd h.2 (not_lt.mpr ((hx.monotone hi).trans ht.1.le))

/-- A B-spline `B_{i,k}` with `j < i` vanishes on `(x_j, x_{j+1})`. -/
theorem bspline_eq_zero_of_lt (hx : StrictMono x) {j : ℕ} (ht : t ∈ Ioo (x j) (x (j + 1)))
    (hi : j < i) : bspline x k i t = 0 :=
  bspline_eq_zero_of_notMem hx.monotone fun h =>
    absurd h.1 (not_le.mpr (ht.2.trans_le (hx.monotone hi)))

/-- **Local linear independence** (de Boor, *A Practical Guide to Splines*, Theorem IX.1): if a
combination `∑_{i ≤ j} c_i B_{i,k}` of B-splines vanishes on the knot interval `(x_j, x_{j+1})`,
`k ≤ j`, then the coefficients of the `k + 1` B-splines `B_{j-k,k}, …, B_{j,k}` that live on that
interval vanish. By induction on `k` through the derivative recursion: the derivative of the
combination is a combination of degree-`k` B-splines with coefficients proportional to
`c_i - c_{i-1}`, so all the coefficients are equal, and the partition of unity forces them to
vanish. -/
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

/-- **Linear independence of the B-splines** ([quarteroni2000numerical] (8.56)): for strictly
increasing knots, the `n + k` B-splines `B_{0,k}, …, B_{n+k-1,k}` restricted to
`[x_k, x_{n+k}]` are linearly independent, by the local independence on every knot interval. -/
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

/-- **The B-spline basis of the spline space** ([quarteroni2000numerical] (8.56)): for strictly
increasing knots with `x_k = a < ⋯ < x_{n+k} = b`, the restrictions of `B_{0,k}, …, B_{n+k-1,k}` to
`[a, b]` form a basis of `S_k` of the partition `j ↦ x (j + k)`: `n + k` independent vectors in a
space of dimension `n + k`. Every spline is thus uniquely `∑_{i < n+k} c_i B_{i,k}` on `[a, b]`,
the `c_i` being its B-spline coefficients. -/
theorem exists_basis_bspline (hx : StrictMono x) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ B : Module.Basis (Fin (n + k)) ℝ
      (Spline.splineSpace (x k) (x (n + k)) n (fun j => x (j + k)) k (k - 1)),
      ∀ (i : Fin (n + k)) (t : Icc (x k) (x (n + k))),
        (B i : C(Icc (x k) (x (n + k)), ℝ)) t = bspline x k i t := by
  have hp : Spline.IsPartition (x k) (x (n + k)) n fun j => x (j + k) :=
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

/-- **The `k + 1` powers `(X - y_j)^k` at distinct points are linearly independent**: extracting
the coefficients of a vanishing combination gives the vanishing of the moments
`∑_j c_j (-y_j)^p`, `p ≤ k`, a Vandermonde system in the `c_j`. -/
theorem linearIndependent_X_sub_C_pow {K : Type*} [Field K] [CharZero K] {k : ℕ}
    {y : Fin (k + 1) → K} (hy : Function.Injective y) :
    LinearIndependent K fun j => (X - C (y j)) ^ k := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmom : ∀ p : Fin (k + 1), ∑ j, g j * (-y j) ^ (p : ℕ) = 0 := by
    intro p
    have h := congrArg (fun q : K[X] => q.coeff (k - p)) hg
    simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_zero] at h
    have hc : ∀ j, ((X - C (y j)) ^ k).coeff (k - p)
        = (-y j) ^ (p : ℕ) * (k.choose (k - p) : K) := by
      intro j
      rw [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
      congr 2
      have := p.2
      omega
    simp only [hc, ← mul_assoc, ← Finset.sum_mul] at h
    refine (mul_eq_zero.mp h).resolve_right ?_
    exact_mod_cast (Nat.choose_pos (Nat.sub_le k p)).ne'
  have hvm : Matrix.vecMul g (Matrix.vandermonde fun j => -y j) = 0 := by
    funext p
    simpa [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply] using hmom p
  have hdet : (Matrix.vandermonde fun j => -y j).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr (neg_injective.comp hy)
  exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hvm)

/-- **The kernel of `c ↦ ∑_j c_j (X - y_j)^k` on `k + 2` distinct points is one-dimensional**:
two vanishing combinations, the second nontrivial, are proportional. -/
theorem exists_eq_smul_of_sum_C_mul_X_sub_C_pow_eq_zero {K : Type*} [Field K] [CharZero K]
    {k : ℕ} {y : Fin (k + 2) → K} (hy : Function.Injective y) {c c' : Fin (k + 2) → K}
    (hc : ∑ j, C (c j) * (X - C (y j)) ^ k = 0)
    (hc' : ∑ j, C (c' j) * (X - C (y j)) ^ k = 0) (hne : c' ≠ 0) :
    ∃ l : K, c = l • c' := by
  obtain ⟨m, hm⟩ : ∃ m, c' m ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  refine ⟨c m / c' m, ?_⟩
  set d : Fin (k + 2) → K := c - (c m / c' m) • c' with hd
  have hdm : d m = 0 := by simp [hd, div_mul_cancel₀ _ hm]
  have hdsum : ∑ j, C (d j) * (X - C (y j)) ^ k = 0 := by
    simp only [hd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, C_sub, C_mul, sub_mul,
      Finset.sum_sub_distrib, hc, mul_assoc, ← Finset.mul_sum, hc', mul_zero, sub_zero]
  have hli := linearIndependent_X_sub_C_pow (hy.comp (Fin.succAbove_right_injective (p := m)))
  rw [Fintype.linearIndependent_iff] at hli
  have h0 : ∀ j, d (m.succAbove j) = 0 := by
    refine hli (fun j => d (m.succAbove j)) ?_
    rw [Fin.sum_univ_succAbove _ m, hdm, C_0, zero_mul, zero_add] at hdsum
    simpa only [smul_eq_C_mul, Function.comp] using hdsum
  have : d = 0 := by
    funext j
    rcases Fin.eq_self_or_eq_succAbove m j with rfl | ⟨j', rfl⟩
    · exact hdm
    · exact h0 j'
  exact sub_eq_zero.mp this

/-- **The jump representation of a `C^{k-1}` piecewise polynomial supported in
`[x_i, x_{i+k+1}]`**: if `s` is `C^{k-1}` on `ℝ`, vanishes outside `[x_i, x_{i+k+1}]` and is a
polynomial of degree at most `k` on each knot interval `[x_j, x_{j+1}]`, `i ≤ j ≤ i + k`, then on
`[x_{i+m}, x_{i+m+1}]` it is `∑_{j ≤ m} c_j (t - x_{i+j})^k`, where `c_j` is the jump of the
leading coefficient at `x_{i+j}`, and the vanishing to the right of `x_{i+k+1}` says
`∑_{j ≤ k+1} c_j (X - x_{i+j})^k = 0`. The jump at each knot is a multiple of `(X - x_j)^k`
because the difference of the adjacent pieces has `C^{k-1}` contact with zero there
(`Spline.iterate_derivative_eval_eq_zero_of_eqOn`). -/
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

/-- **Schoenberg's minimal-support characterization of the B-spline** ([quarteroni2000numerical]
§8.6.2, quoting Schoenberg): for strictly increasing knots and `1 ≤ k`, a function `s : ℝ → ℝ` of
class `C^{k-1}`, vanishing outside `[x_i, x_{i+k+1}]` and a polynomial of degree at most `k` on
each knot interval `[x_j, x_{j+1}]`, `i ≤ j ≤ i + k`, is a scalar multiple of `B_{i,k}`. Both `s`
and `B_{i,k}` are combinations `∑_{j ≤ m} c_j (t - x_{i+j})^k` on the `m`-th knot interval with
jump coefficients in the kernel of `c ↦ ∑_{j ≤ k+1} c_j (X - x_{i+j})^k`
(`exists_sum_C_mul_X_sub_C_pow_eq_zero_and_eqOn`), which is one-dimensional
(`exists_eq_smul_of_sum_C_mul_X_sub_C_pow_eq_zero`); the B-spline's coefficients are nonzero
because it is positive on `(x_i, x_{i+k+1})` (`bspline_pos`). -/
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
    obtain ⟨p, hpd, hpe⟩ := exists_eqOn_bspline (k := k) (i := i) hx.monotone j
    refine ⟨p, hpd, hpe.of_subset_closure (contDiff_bspline hx hk i).continuous.continuousOn
      p.continuous.continuousOn Ico_subset_Icc_self ?_⟩
    rw [closure_Ico (hx (Nat.lt_succ_self j)).ne]
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
  · have hpart : Spline.IsPartition (x i) (x (i + k + 1)) (k + 1) fun m => x (i + m) :=
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

/-- **B-splines with `k + 1` coincident knots at the left** ([quarteroni2000numerical] Remark 8.3):
if `x_i = ⋯ = x_{i+k} < x_{i+k+1}` then `B_{i,k}(t) = ((x_{i+k+1} - t)/(x_{i+k+1} - x_i))^k` on
`[x_i, x_{i+k+1})` and `0` elsewhere. (The book prints the closed interval, where the formula gives
`0` at the right end anyway.) -/
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

/-- **B-splines with `k + 1` coincident knots at the right** ([quarteroni2000numerical] Remark 8.3):
if `x_i < x_{i+1} = ⋯ = x_{i+k+1}` then `B_{i,k}(t) = ((t - x_i)/(x_{i+k+1} - x_i))^k` on
`[x_i, x_{i+k+1})` and `0` elsewhere. -/
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

/-- **Values at a knot of multiplicity `m + 1`**: if `x_0 = ⋯ = x_m < x_{m+1}` then
`B_{i,d}(x_m) = 1` when `i + d = m` and `0` for every other `i ≤ m`; through the recursion, since
the weights `ω_{i,d}(x_m)` vanish for `i ≤ m`. -/
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

/-- **The value at the left endpoint with `k + 1` coincident knots** ([quarteroni2000numerical]
(8.57), first half): if `x_0 = ⋯ = x_k < x_{k+1}` and `1 ≤ n` then
`∑_{i < n+k} c_i B_{i,k}(x_k) = c_0`. -/
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

/-- **The cubic B-spline on uniform knots** ([quarteroni2000numerical] Example 8.9): for
`x j = x₀ + j h` with `h > 0`, `6 h³ B_{i,3}(t)` is `(t - x_i)³` on `[x_i, x_{i+1})`,
`h³ + 3h²(t - x_{i+1}) + 3h(t - x_{i+1})² - 3(t - x_{i+1})³` on `[x_{i+1}, x_{i+2})`,
`h³ + 3h²(x_{i+3} - t) + 3h(x_{i+3} - t)² - 3(x_{i+3} - t)³` on `[x_{i+2}, x_{i+3})`,
`(x_{i+4} - t)³` on `[x_{i+3}, x_{i+4})`, and `0` elsewhere. The recursion unfolded three times on
each of the four intervals. -/
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

/-- **The parametric B-spline curve** ([quarteroni2000numerical] §8.7.1) with control points
`P_0, …, P_{N-1}`: `t ↦ ∑_{i < N} B_{i,k}(t) P_i`. -/
noncomputable def curve (x : ℕ → ℝ) (k : ℕ) (P : ℕ → E) (N : ℕ) (t : ℝ) : E :=
  ∑ i ∈ Finset.range N, bspline x k i t • P i

/-- **The convex-hull property** ([quarteroni2000numerical] §8.7.1, property 2): on the parameter
range `[x_k, x_N)` of a curve with `N` control points, the curve lies in the convex hull of its
control polygon, its coefficients being nonnegative and summing to one. -/
theorem curve_mem_convexHull (hx : Monotone x) (P : ℕ → E) {N : ℕ} (hN : 1 ≤ N)
    (ht : t ∈ Ico (x k) (x N)) : curve x k P N t ∈ convexHull ℝ (P '' Iio N) := by
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => bspline_nonneg hx) ?_
    fun i hi => subset_convexHull ℝ _ ⟨i, Finset.mem_range.mp hi, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact sum_bspline hx ht

/-- **Locality** ([quarteroni2000numerical] §8.7.1, property 1): moving the control point `P_j`
changes the curve only on `[x_j, x_{j+k+1})`. -/
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

/-- **The value at the right endpoint with `k + 1` coincident knots** ([quarteroni2000numerical]
(8.57), second half): if `x_{n+k-1} < x_{n+k} = ⋯ = x_{n+2k} = b` then
`∑_{i < n+k} c_i B_{i,k}(t) → c_{n+k-1}` as `t → b⁻`. With the half-open convention every
`B_{i,k}` vanishes *at* `b`, so the value is the left limit: `B_{n+k-1,k}(t) → 1` by the
coincident-knot formula, and the other B-splines tend to `0` by the partition of unity. -/
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

/-- **B-splines depend continuously on their knots, approached from below**: if the knot sequences
`X n` are nondecreasing, lie strictly below `x` and converge to it pointwise, then
`B^{X n}_{i,k}(t) → B^x_{i,k}(t)` for every fixed `t`.

Approaching from below is what makes this true at *every* `t`, the knots included: the degree-`0`
B-splines are eventually equal, because the half-open panel `[X n i, X n (i+1))` eventually contains
a given `t ∈ [x i, x (i+1))` and never contains a `t ≥ x (i+1)`. In the Cox-de Boor recursion the
weight `ω_{i,d+1}` may fail to converge — exactly when `x (i+d+1) = x i` — but then the B-spline it
multiplies has empty support and is eventually `0`, so the product converges all the same. Used to
pass from strictly increasing to merely nondecreasing knots in Boehm's algorithm. -/
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

/-- **Boehm's knot insertion** ([quarteroni2000numerical] Remark 8.4): the knot sequence with the
knot `y ∈ [x_j, x_{j+1})` inserted after position `j`: `y_i = x_i` for `i ≤ j`, `y_{j+1} = y`, and
`y_i = x_{i-1}` afterwards. -/
def insertKnot (x : ℕ → ℝ) (j : ℕ) (y : ℝ) (i : ℕ) : ℝ :=
  if i ≤ j then x i else if i = j + 1 then y else x (i - 1)

/-- The weights `ω_i` of Boehm's algorithm: `1` for `i + k ≤ j`, `(y - x_i)/(x_{i+k} - x_i)` for
`j - k < i ≤ j`, and `0` for `i > j`. -/
noncomputable def insertKnotWeight (x : ℕ → ℝ) (k j : ℕ) (y : ℝ) (i : ℕ) : ℝ :=
  if i + k ≤ j then 1 else if i ≤ j then (y - x i) / (x (i + k) - x i) else 0

/-- **The new B-spline coefficients of Boehm's algorithm** ([quarteroni2000numerical] Remark 8.4,
with the misprint `c_i` for `c_{i-1}` corrected): `d_i = ω_i c_i + (1 - ω_i) c_{i-1}`. -/
noncomputable def insertKnotCoeff (x : ℕ → ℝ) (k j : ℕ) (y : ℝ) (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  insertKnotWeight x k j y i * c i + (1 - insertKnotWeight x k j y i) * c (i - 1)

/-- The inserted knot sequence is nondecreasing. -/
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

/-- The inserted knot sequence is strictly increasing when the new knot is interior to its
panel. -/
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

/-- The index shift that identifies the original knots inside the inserted sequence. -/
def insertShift (j m : ℕ) : ℕ := if m ≤ j then m else m + 1

/-- The index shift is injective. -/
theorem insertShift_injective (j : ℕ) : Function.Injective (insertShift j) := by
  intro a b h
  unfold insertShift at h
  split_ifs at h <;> omega

/-- The inserted sequence, read through the index shift, is the original one. -/
theorem insertKnot_insertShift (x : ℕ → ℝ) (j : ℕ) (y : ℝ) (m : ℕ) :
    insertKnot x j y (insertShift j m) = x m := by
  unfold insertKnot insertShift
  split_ifs <;> first | rfl | omega

/-- The B-spline as a divided difference over the index interval. -/
theorem bspline_eq_mul_newtonOn {v : ℕ → ℝ} (hv : StrictMono v) (hk : 1 ≤ k) (i : ℕ) (t : ℝ) :
    bspline v k i t = (v (i + k + 1) - v i) *
      DividedDifference.newtonOn (Finset.Icc i (i + k + 1)) v
        (fun s => Quadrature.truncPow k s t) := by
  rw [bspline_eq_mul_newton_truncPow hv hk i t,
    DividedDifference.newton_shift_eq_newtonOn v _ (k + 1) i, ← Nat.add_assoc]

/-- Erasing the right endpoint of an index interval. -/
private theorem erase_Icc_top (i m : ℕ) :
    (Finset.Icc i (m + 1)).erase (m + 1) = Finset.Icc i m := by
  ext c
  simp only [Finset.mem_erase, Finset.mem_Icc]
  omega

/-- Erasing the left endpoint of an index interval. -/
private theorem erase_Icc_bot (i m : ℕ) : (Finset.Icc i m).erase i = Finset.Icc (i + 1) m := by
  ext c
  simp only [Finset.mem_erase, Finset.mem_Icc]
  omega

/-- The index shift carries the original index interval onto the inserted one with the new index
removed. -/
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

/-- **Boehm's knot-insertion formula for one B-spline**, in the main regime `i ≤ j ≤ i + k`
where the new knot falls inside the support of `B_{i,k}`. -/
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
    rw [hT, show i + k + 2 = (i + k + 1) + 1 from rfl, erase_Icc_top]
  have hTr : T.erase i = Finset.Icc (i + 1) (i + k + 2) := erase_Icc_bot _ _
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

/-- Boehm's formula when the new knot lies to the right of the support of `B_{i,k}`: the B-spline
is unchanged. -/
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

/-- Boehm's formula when the new knot lies to the left of the support of `B_{i,k}`: the B-spline is
the shifted one. -/
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

/-- **Boehm's knot-insertion formula for one B-spline** ([quarteroni2000numerical] Remark 8.4): for
strictly increasing knots, `1 ≤ k` and a new knot `y` interior to the panel `(x_j, x_{j+1})`,
`B_{i,k} = ω_i B̂_{i,k} + (1 - ω_{i+1}) B̂_{i+1,k}` with the weights `ω` of `insertKnotWeight`;
[Boehm, *Inserting new knots into B-spline curves*][boehm1980inserting]. -/
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

/-- The Boehm weights converge with the knots, provided the panel `(x_j, x_{j+1})` is nonempty:
the only knot-dependent branch is `(y - x_i)/(x_{i+k} - x_i)` for `i ≤ j < i + k`, whose
denominator is then bounded below by `x_{j+1} - x_j > 0`. -/
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

/-- Boehm's one-spline formula for a nondecreasing knot sequence, from the strictly increasing
case by passing to the limit along knots `X n` and inserted knots `Z n` that approach `x` and `y`
from below. -/
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

/-- **Boehm's knot-insertion formula for one B-spline, at a knot that need not be interior to its
panel** ([quarteroni2000numerical] Remark 8.4; [boehm1980inserting]): the identity
`B_{i,k} = ω_i B̂_{i,k} + (1 - ω_{i+1}) B̂_{i+1,k}` for a merely *nondecreasing* knot sequence and
a new knot `y ∈ [x_j, x_{j+1})`, so that `y = x_j` — raising the multiplicity of an existing knot —
is allowed.

The divided-difference proof of `bspline_eq_insert_comb` needs distinct knots, and at `y = x_j` the
refined sequence has a double knot. Instead both sides are limits of the strictly increasing case:
the knots `X n m = x_m - 2^{-m}(x_{j+1} - y)/(n+1)` are strictly increasing and approach `x` from
below, `Z n = y - (y - X n j)/(n+2)` lies in the panel `(X n j, X n (j+1))` and approaches `y` from
below, and `tendsto_bspline_of_tendsto` and `tendsto_insertKnotWeight` pass to the limit. -/
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

/-- The bookkeeping behind `sum_smul_bspline_insertKnot`: given the one-spline identity for every
index, the spline `∑_{i < N} c_i B_{i,k}` equals `∑_{i < N+1} d_i B̂_{i,k}` with the Boehm
coefficients `d_i`. The two hypotheses `k ≤ j` and `j < N` are what make the boundary weights
`ω_0 = 1` and `ω_N = 0`, so that the two shifted sums close up. -/
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

/-- **Knot insertion preserves the spline** ([quarteroni2000numerical] Remark 8.4): for strictly
increasing knots, `1 ≤ k` and a new knot `y` interior to the panel `(x_j, x_{j+1})` whose index
satisfies `k ≤ j < N`, the spline `∑_{i < N} c_i B_{i,k}` is `∑_{i < N + 1} d_i B̂_{i,k}` on the
refined knots, with the coefficients `d_i = ω_i c_i + (1 - ω_i) c_{i-1}` of `insertKnotCoeff`. -/
theorem sum_smul_bspline_insertKnot (hx : StrictMono x) (hk : 1 ≤ k)
    (hy : y ∈ Ioo (x j) (x (j + 1))) (hkj : k ≤ j) {N : ℕ} (hjN : j < N) (c : ℕ → ℝ) (t : ℝ) :
    ∑ i ∈ Finset.range (N + 1), insertKnotCoeff x k j y c i * bspline (insertKnot x j y) k i t
      = ∑ i ∈ Finset.range N, c i * bspline x k i t :=
  sum_smul_bspline_insert_of_comb (fun i => bspline_eq_insert_comb hx hk hy i t) hkj hjN c

/-- **Knot insertion preserves the spline, at a knot that need not be interior to its panel**
([quarteroni2000numerical] Remark 8.4): the same identity as `sum_smul_bspline_insertKnot` for a
merely *nondecreasing* knot sequence and a new knot `y ∈ [x_j, x_{j+1})`, which is the range the
book states. The case `y = x_j` raises the multiplicity of an existing knot; `x_j < x_{j+1}`, which
`hy` forces, is exactly the requirement that the panel receiving the knot be nonempty. -/
theorem sum_smul_bspline_insertKnot_of_monotone (hx : Monotone x) (hk : 1 ≤ k)
    (hy : y ∈ Ico (x j) (x (j + 1))) (hkj : k ≤ j) {N : ℕ} (hjN : j < N) (c : ℕ → ℝ) (t : ℝ) :
    ∑ i ∈ Finset.range (N + 1), insertKnotCoeff x k j y c i * bspline (insertKnot x j y) k i t
      = ∑ i ∈ Finset.range N, c i * bspline x k i t :=
  sum_smul_bspline_insert_of_comb
    (fun i => bspline_eq_insert_comb_of_monotone hx hk hy i t) hkj hjN c

end KnotInsertion

end BSpline
