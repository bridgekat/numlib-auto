import Mathlib.Analysis.Calculus.Taylor
import Numlib.Approximation.Interpolation
import Numlib.Approximation.Quadrature
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.Hessenberg

/-!
# Polynomial splines and interpolatory cubic splines

The spline space `S_k^r` of a partition `a = x_0 < x_1 < ⋯ < x_n = b`: the continuous functions on
`[a, b]` that are polynomials of degree at most `k` on every panel and of class `C^r` across the
breakpoints, with its truncated-power basis and its dimension `n (k - r) + r + 1`; and the
interpolatory cubic spline (`k = 3`, `r = 2`) built from its *moments* `M_i = s''(x_i)` through the
tridiagonal, strictly diagonally dominant M-continuity system, for the natural, clamped and
"prolonged" closures, with Holladay's minimum-norm property and the best-approximation property of
the clamped spline.

The material is [quarteroni2000numerical] §8.6–8.6.1 (Definition 8.1, (8.46)–(8.49), Property 8.2,
Exercises 8.10–8.11); de Boor, *A Practical Guide to Splines*, is the reference for what the book
quotes.

## Main definitions

* `Spline.IsPartition a b n x`: `a = x 0 < x 1 < ⋯ < x n = b`.
* `Spline.splineSpace a b n x k r : Submodule ℝ C(Icc a b, ℝ)`, the splines of degree `k` and
  smoothness `C^r`. The book's `S_k` is `r = k - 1`; its `X_h^k` (the range of the piecewise
  polynomial interpolation operator of `Numlib/Approximation/Interpolation`) is `r = 0`; and `r = k`
  gives back `polyLE (Icc a b) k`. Membership asks for a `C^r` function on `Icc a b` agreeing with
  the given continuous map there and with a polynomial of degree at most `k` on every panel, so no
  derivative of a function on the subtype is ever needed.
* `Spline.truncPowCM a b c s`, the truncated power `t ↦ (t - c)_+^s` as an element of
  `C(Icc a b, ℝ)`, and `Spline.truncPowFamily`, the monomials together with the truncated powers at
  the interior breakpoints.
* `Spline.panelCubic x f M i`, the cubic on the panel `[x (i-1), x i]` with prescribed end values
  `f (i-1), f i` and end second derivatives `M (i-1), M i` ((8.46) integrated twice);
  `Spline.panelGlue`, the function that is `Q i` on the `i`-th panel, and
  `Spline.cubicSplineFun n x f M`, the panel cubics glued.
* `Spline.momentMatrix n h lam0 mun` and `Spline.momentRhs n h f d0 dn`, the M-continuity system
  (8.47)–(8.48) with the closure rows `2 M_0 + λ_0 M_1 = d_0`, `μ_n M_{n-1} + 2 M_n = d_n`.
* `Spline.IsCubicSpline a b n x s` and `Spline.IsCubicInterp a b n x f s`, a `C²` piecewise cubic
  on `[a, b]`, respectively one interpolating the values `f i` at the nodes; `Spline.moment` and
  `Spline.HasClosure`.
* `Spline.cubicInterp n x f lam0 mun d0 dn`, the interpolatory cubic spline with a closure of type
  (8.48), with `Spline.naturalInterp` and `Spline.clampedInterp` as the two named cases, and
  `Spline.cardinalBasis`, the cardinal spline basis.

## Main results

* `Spline.linearIndependent_truncPow`, `Spline.span_truncPow_eq_splineSpace`,
  `Spline.finrank_splineSpace`, `Spline.exists_basis_truncPow`: the truncated-power basis and the
  dimension count.
* `Spline.moment_eq_of_contDiffOn` and `Spline.contDiffOn_cubicSplineFun`: the M-continuity system
  is necessary and sufficient for the glued panel cubics to be `C²`.
* `Spline.isStrictDiagDominant_momentMatrix`, `Spline.isUnit_momentMatrix`,
  `Spline.norm_le_norm_momentMatrix_mulVec`: the moment matrix is strictly diagonally dominant with
  `‖A⁻¹‖_∞ ≤ 1`.
* `Spline.existsUnique_isCubicInterp_of_closure`: existence and uniqueness of the interpolatory
  cubic spline with a closure of type (8.48); `Spline.existsUnique_isCubicInterp_periodic` and
  `Spline.existsUnique_isCubicInterp_notAKnot` for the periodic and the not-a-knot closures.
* `Spline.integral_sub_deriv2_mul_deriv2_eq_zero`, `Spline.holladay`, `Spline.holladay_eq_iff`,
  `Spline.holladay_clamped`, `Spline.integral_sq_sub_deriv2_clampedInterp_le`: Holladay's
  orthogonality identity and the minimum-norm and best-approximation properties.
* `Spline.norm_deriv2_sub_clampedInterp_le`, `Spline.norm_deriv2_sub_clampedInterp_le_of_mem`,
  `Spline.norm_deriv_sub_clampedInterp_le`, `Spline.norm_sub_clampedInterp_le`: for a `C⁴`
  function with `|f⁗| ≤ K` and panel lengths at most `h`, the moments of the clamped spline are
  within `(3/4) h² K` of `f''` at the nodes, and on all of `[a, b]` the clamped spline satisfies
  `|f'' - s''| ≤ (7/4) h² K`, `|f' - s'| ≤ (7/4) h³ K`, `|f - s| ≤ (7/8) h⁴ K`. The constants are
  not the sharp ones of Hall and Meyer.

## Implementation notes

Everything about cubic splines is stated for functions `ℝ → ℝ`. The glued function
`cubicSplineFun` continues the first and the last panel cubic outside `[a, b]`, so it is `C²` on
all of `ℝ` once the moment equations hold, and its derivatives at the nodes are ordinary
derivatives. An arbitrary interpolating spline `s` is only assumed `C²` on `Icc a b`, and its
moments are the within-derivatives `iteratedDerivWithin 2 s (Icc a b) (x i)`.
-/

open Filter Polynomial Set
open scoped Topology

namespace Spline

variable {a b : ℝ} {n k r : ℕ} {x : ℕ → ℝ}

/-! ### Partitions -/

/-- The nodes of [quarteroni2000numerical] Definition 8.1: `a = x 0 < x 1 < ⋯ < x n = b`, `n`
panels and `n + 1` nodes; only `x 0, …, x n` are ever used. -/
structure IsPartition (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop where
  /-- Consecutive nodes increase. -/
  step : ∀ j < n, x j < x (j + 1)
  /-- The first node is `a`. -/
  first : x 0 = a
  /-- The last node is `b`. -/
  last : x n = b

namespace IsPartition

variable (hx : IsPartition a b n x)
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

end IsPartition

/-- Real polynomial functions are smooth. -/
theorem _root_.Polynomial.contDiff_eval (P : ℝ[X]) (N : WithTop ℕ∞) :
    ContDiff ℝ N fun t : ℝ => P.eval t := by
  simpa only [coe_aeval_eq_eval] using P.contDiff_aeval (𝕜 := ℝ) N

/-! ### The spline space -/

/-- **The spline space** `S_k^r` of degree `k` and smoothness `C^r` on the partition
`a = x 0 < x 1 < ⋯ < x n = b` ([quarteroni2000numerical] Definition 8.1 with `r = k - 1`): the
continuous functions on `[a, b]` that are restrictions of a `C^r` function on `Icc a b` agreeing on
each panel `[x j, x (j + 1)]` with a polynomial of degree at most `k`. The book's `X_h^k` of §8.3 is
`r = 0`, and `r = k` gives the polynomials. -/
noncomputable def splineSpace (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (k r : ℕ) :
    Submodule ℝ C(Icc a b, ℝ) where
  carrier := {f | ∃ g : ℝ → ℝ, ContDiffOn ℝ r g (Icc a b) ∧ (∀ t : Icc a b, f t = g t) ∧
    ∀ j < n, ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn g p.eval (Icc (x j) (x (j + 1)))}
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, hf₁, hp₁⟩ ⟨g₂, hg₂, hf₂, hp₂⟩
    refine ⟨g₁ + g₂, hg₁.add hg₂, fun t => by simp [hf₁ t, hf₂ t], fun j hj => ?_⟩
    obtain ⟨p₁, hp₁d, hp₁e⟩ := hp₁ j hj
    obtain ⟨p₂, hp₂d, hp₂e⟩ := hp₂ j hj
    exact ⟨p₁ + p₂, (degree_add_le _ _).trans (max_le hp₁d hp₂d),
      fun t ht => by simp [hp₁e ht, hp₂e ht]⟩
  zero_mem' := ⟨0, contDiffOn_const, fun _ => rfl, fun _ _ => ⟨0, by simp, fun _ _ => by simp⟩⟩
  smul_mem' := by
    rintro c f ⟨g, hg, hf, hp⟩
    refine ⟨c • g, hg.const_smul c, fun t => by simp [hf t], fun j hj => ?_⟩
    obtain ⟨p, hpd, hpe⟩ := hp j hj
    exact ⟨c • p, (degree_smul_le _ _).trans hpd, fun t ht => by simp [hpe ht]⟩

/-- Membership of the spline space unfolded. -/
theorem mem_splineSpace_iff {f : C(Icc a b, ℝ)} :
    f ∈ splineSpace a b n x k r ↔ ∃ g : ℝ → ℝ, ContDiffOn ℝ r g (Icc a b) ∧
      (∀ t : Icc a b, f t = g t) ∧
      ∀ j < n, ∃ p : ℝ[X], p.degree ≤ k ∧ EqOn g p.eval (Icc (x j) (x (j + 1))) :=
  Iff.rfl

/-- A polynomial of degree at most `k` is a spline of every smoothness
("obviously, any polynomial of degree `k` on `[a, b]` is a spline"). -/
theorem polyLE_le_splineSpace (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (k r : ℕ) :
    polyLE (Icc a b) k ≤ splineSpace a b n x k r := by
  intro f hf
  obtain ⟨P, hPd, hPv⟩ := mem_polyLE_iff.mp hf
  exact ⟨P.eval, (P.contDiff_eval r).contDiffOn, hPv, fun _ _ => ⟨P, hPd, fun _ _ => rfl⟩⟩

/-- Smoother splines form a smaller space. -/
theorem splineSpace_anti_smoothness {r' : ℕ} (hrr : r ≤ r') :
    splineSpace a b n x k r' ≤ splineSpace a b n x k r := by
  rintro f ⟨g, hg, hf, hp⟩
  exact ⟨g, hg.of_le (by exact_mod_cast hrr), hf, hp⟩

/-- Splines of lower degree form a smaller space. -/
theorem splineSpace_mono_degree {k' : ℕ} (hkk : k ≤ k') :
    splineSpace a b n x k r ≤ splineSpace a b n x k' r := by
  rintro f ⟨g, hg, hf, hp⟩
  refine ⟨g, hg, hf, fun j hj => ?_⟩
  obtain ⟨p, hpd, hpe⟩ := hp j hj
  exact ⟨p, hpd.trans (by exact_mod_cast hkk), hpe⟩

/-! ### Truncated powers -/

/-- `t ↦ max (t - c) 0 ^ (s + 2)` has derivative `(s + 2) * max (t - c) 0 ^ (s + 1)` everywhere,
the point `c` included. -/
theorem hasDerivAt_max_sub_pow (c : ℝ) (s : ℕ) (t : ℝ) :
    HasDerivAt (fun t => max (t - c) 0 ^ (s + 2)) ((s + 2) * max (t - c) 0 ^ (s + 1)) t := by
  rcases lt_trichotomy t c with htc | rfl | htc
  · have h : (fun t => max (t - c) 0 ^ (s + 2)) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds htc] with u (hu : u < c)
      simp [max_eq_right (sub_nonpos.mpr hu.le)]
    rw [max_eq_right (sub_nonpos.mpr htc.le), zero_pow (Nat.succ_ne_zero s), mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq h
  · rw [sub_self, max_self, zero_pow (Nat.succ_ne_zero s), mul_zero,
      hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [add_sub_cancel_left, sub_self, max_self, zero_pow (Nat.succ_ne_zero _), sub_zero,
      smul_zero]
    have h1 : (fun h : ℝ => max h 0) =O[𝓝 0] fun h => h :=
      Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => by
        simp only [Real.norm_eq_abs, one_mul]
        rcases le_or_gt h 0 with hh | hh
        · simp [max_eq_right hh]
        · simp [max_eq_left hh.le])
    have h2 : (fun h : ℝ => max h 0 ^ (s + 1)) =o[𝓝 0] fun _ => (1 : ℝ) := by
      rw [Asymptotics.isLittleO_one_iff]
      have : Tendsto (fun h : ℝ => max h 0 ^ (s + 1)) (𝓝 0) (𝓝 (max 0 0 ^ (s + 1))) :=
        ((continuous_id.max continuous_const).pow _).tendsto 0
      simpa using this
    have := h1.mul_isLittleO h2
    simpa [pow_succ, mul_comm] using this
  · have h : (fun t => max (t - c) 0 ^ (s + 2)) =ᶠ[𝓝 t] fun t => (t - c) ^ (s + 2) := by
      filter_upwards [Ioi_mem_nhds htc] with u (hu : c < u)
      simp [max_eq_left (sub_nonneg.mpr hu.le)]
    rw [max_eq_left (sub_nonneg.mpr htc.le)]
    have := (hasDerivAt_pow (s + 2) (t - c)).comp t ((hasDerivAt_id t).sub_const c)
    simp only [Nat.cast_add, Nat.cast_ofNat, mul_one] at this
    exact this.congr_of_eventuallyEq h

/-- `t ↦ max (t - c) 0 ^ (s + 1)` is of class `C^s`: the truncated power `(t - c)_+^{s+1}` has
`s` continuous derivatives, its derivatives of order `≤ s` vanishing at `c` from both sides. -/
theorem contDiff_max_sub_pow (c : ℝ) (s : ℕ) :
    ContDiff ℝ s (fun t => max (t - c) 0 ^ (s + 1)) := by
  induction s with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact ((continuous_id.sub continuous_const).max continuous_const).pow 1
  | succ s ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t => (hasDerivAt_max_sub_pow c s t).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    have : deriv (fun t => max (t - c) 0 ^ (s + 1 + 1)) =
        fun t => ((s : ℝ) + 2) * max (t - c) 0 ^ (s + 1) :=
      funext fun t => (hasDerivAt_max_sub_pow c s t).deriv
    rw [this]
    exact contDiff_const.mul ih

/-- **The truncated power** `t ↦ (t - c)_+^s`, as a continuous function on `[a, b]`; it is written
`max (t - c) 0 ^ s`, which is `Quadrature.truncPow s t c` for `1 ≤ s` (`truncPowCM_apply_eq`), and
the constant `1` for `s = 0`. -/
noncomputable def truncPowCM (a b c : ℝ) (s : ℕ) : C(Icc a b, ℝ) :=
  ⟨fun t => max ((t : ℝ) - c) 0 ^ s,
    ((continuous_subtype_val.sub continuous_const).max continuous_const).pow s⟩

/-- The value of the truncated power. -/
@[simp]
theorem truncPowCM_apply (a b c : ℝ) (s : ℕ) (t : Icc a b) :
    truncPowCM a b c s t = max ((t : ℝ) - c) 0 ^ s := rfl

/-- For `1 ≤ s` the truncated power is `Quadrature.truncPow s t c = (t - c)_+^s`. -/
theorem truncPowCM_apply_eq (a b c : ℝ) {s : ℕ} (hs : 1 ≤ s) (t : Icc a b) :
    truncPowCM a b c s t = Quadrature.truncPow s t c := by
  rw [truncPowCM_apply, Quadrature.truncPow]
  split_ifs with h
  · rw [max_eq_left (sub_nonneg.mpr h)]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)), zero_pow (by omega)]

/-- The monomial `t ↦ t ^ i` as a continuous function on `[a, b]`. -/
noncomputable def monomialCM (a b : ℝ) (i : ℕ) : C(Icc a b, ℝ) :=
  ⟨fun t => (t : ℝ) ^ i, continuous_subtype_val.pow i⟩

/-- The value of the monomial. -/
@[simp]
theorem monomialCM_apply (a b : ℝ) (i : ℕ) (t : Icc a b) : monomialCM a b i t = (t : ℝ) ^ i := rfl

/-- The monomials of degree at most `k` are polynomials of degree at most `k`. -/
theorem monomialCM_mem_polyLE (a b : ℝ) {i : ℕ} (hi : i ≤ k) :
    monomialCM a b i ∈ polyLE (Icc a b) k :=
  mem_polyLE_iff.mpr ⟨X ^ i, (degree_X_pow_le i).trans (by exact_mod_cast hi), fun t => by simp⟩

/-- **A truncated power at an interior breakpoint is a spline**: `(t - x j)_+^s` with `r < s ≤ k`
and `0 < j < n` lies in `S_k^r`, being `C^{s-1}` (`contDiff_max_sub_pow`) and a polynomial on
either side of `x j`. -/
theorem truncPowCM_mem_splineSpace (hx : IsPartition a b n x) {j s : ℕ} (hjn : j < n) (hrs : r < s)
    (hsk : s ≤ k) : truncPowCM a b (x j) s ∈ splineSpace a b n x k r := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  refine ⟨fun t => max (t - x j) 0 ^ (s + 1),
    ((contDiff_max_sub_pow (x j) s).of_le (by exact_mod_cast (by omega : r ≤ s))).contDiffOn,
    fun t => rfl, fun i hi => ?_⟩
  rcases le_or_gt j i with hji | hij
  · refine ⟨(X - C (x j)) ^ (s + 1), (degree_pow_le _ _).trans ?_, fun t ht => ?_⟩
    · calc ((s + 1) • (X - C (x j)).degree : WithBot ℕ) ≤ (s + 1) • (1 : WithBot ℕ) :=
          nsmul_le_nsmul_right (degree_X_sub_C_le _) _
        _ = ((s + 1 : ℕ) : WithBot ℕ) := by simp
        _ ≤ k := by exact_mod_cast hsk
    · have : x j ≤ t := (hx.mono hji (by omega)).trans ht.1
      simp [max_eq_left (sub_nonneg.mpr this)]
  · refine ⟨0, by simp, fun t ht => ?_⟩
    have : t ≤ x j := ht.2.trans (hx.mono (by omega) hjn.le)
    simp [max_eq_right (sub_nonpos.mpr this)]

/-! ### The truncated-power basis

The family of [quarteroni2000numerical] Exercise 8.10: the monomials `1, t, …, t^k` together with
the truncated powers `(t - x_j)_+^s` at the interior breakpoints `x_1, …, x_{n-1}`, for the
exponents `r < s ≤ k`. Its index type has `(k + 1) + (n - 1) (k - r)` elements. -/

/-- The index type of the truncated-power family: a monomial exponent `i ≤ k`, or an interior
breakpoint `x (j + 1)` with an exponent `r + 1 + s ≤ k`. -/
abbrev TruncPowIndex (n k r : ℕ) : Type := Fin (k + 1) ⊕ (Fin (n - 1) × Fin (k - r))

/-- **The truncated-power family** of `S_k^r`: the monomial `t ^ i` at `Sum.inl i` and the
truncated power `(t - x (j + 1))_+^(r + 1 + s)` at `Sum.inr (j, s)`. -/
noncomputable def truncPowFamily (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (k r : ℕ) :
    TruncPowIndex n k r → C(Icc a b, ℝ)
  | Sum.inl i => monomialCM a b i
  | Sum.inr (j, s) => truncPowCM a b (x (j + 1)) (r + 1 + s)

/-- Every member of the truncated-power family is a spline. -/
theorem truncPowFamily_mem_splineSpace (hx : IsPartition a b n x) (i : TruncPowIndex n k r) :
    truncPowFamily a b n x k r i ∈ splineSpace a b n x k r := by
  rcases i with i | ⟨j, s⟩
  · exact polyLE_le_splineSpace a b n x k r (monomialCM_mem_polyLE a b (Nat.lt_succ_iff.mp i.2))
  · exact truncPowCM_mem_splineSpace hx (by have := j.2; omega) (by omega) (by have := s.2; omega)

/-- **Order-`r` contact of the pieces of a `C^r` function.** If `e` is `C^r` on `(u, w)`, vanishes
on `(u, v)` and agrees with the polynomial `d` on `(v, w)`, then the derivatives of `d` of order at
most `r` vanish at `v`: `e^{(m)}` is continuous on `(u, w)`, equal to `0` on the left of `v` and
to `d^{(m)}` on its right. -/
theorem iterate_derivative_eval_eq_zero_of_eqOn {u v w : ℝ} (huv : u < v) (hvw : v < w)
    {e : ℝ → ℝ} (he : ContDiffOn ℝ r e (Ioo u w)) (h0 : EqOn e 0 (Ioo u v)) {d : ℝ[X]}
    (hd : EqOn e d.eval (Ioo v w)) {m : ℕ} (hm : m ≤ r) : (derivative^[m] d).eval v = 0 := by
  have hcont : ContinuousOn (iteratedDeriv m e) (Ioo u w) :=
    (he.continuousOn_iteratedDerivWithin (by exact_mod_cast hm) isOpen_Ioo.uniqueDiffOn).congr
      (iteratedDerivWithin_of_isOpen isOpen_Ioo).symm
  have hv : v ∈ Ioo u w := ⟨huv, hvw⟩
  have hleft : Tendsto (iteratedDeriv m e) (𝓝[Ioo u v] v) (𝓝 (iteratedDeriv m e v)) :=
    (hcont v hv).tendsto.mono_left (nhdsWithin_mono _ (Ioo_subset_Ioo_right hvw.le))
  have hright : Tendsto (iteratedDeriv m e) (𝓝[Ioo v w] v) (𝓝 (iteratedDeriv m e v)) :=
    (hcont v hv).tendsto.mono_left (nhdsWithin_mono _ (Ioo_subset_Ioo_left huv.le))
  have hl0 : Tendsto (iteratedDeriv m e) (𝓝[Ioo u v] v) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [h0.iteratedDeriv_of_isOpen isOpen_Ioo m ht]
    cases m <;> simp
  have hr0 : Tendsto (iteratedDeriv m e) (𝓝[Ioo v w] v) (𝓝 ((derivative^[m] d).eval v)) := by
    have : Tendsto (fun t => (derivative^[m] d).eval t) (𝓝[Ioo v w] v)
        (𝓝 ((derivative^[m] d).eval v)) :=
      ((derivative^[m] d).continuous.tendsto v).mono_left nhdsWithin_le_nhds
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hd.iteratedDeriv_of_isOpen isOpen_Ioo m ht, Polynomial.iteratedDeriv_eval]
  have : (𝓝[Ioo u v] v).NeBot := by rw [nhdsWithin_Ioo_eq_nhdsLT huv]; infer_instance
  have : (𝓝[Ioo v w] v).NeBot := by rw [nhdsWithin_Ioo_eq_nhdsGT hvw]; infer_instance
  rw [← tendsto_nhds_unique hright hr0, tendsto_nhds_unique hleft hl0]

/-- A polynomial of degree at most `k` whose derivatives of order at most `r` vanish at `v` is
`∑_{r < s ≤ k} c_s (t - v)^s`, with `c_s` the coefficients of its Taylor expansion at `v`. -/
theorem eval_eq_sum_Ioc_of_iterate_derivative_eq_zero {d : ℝ[X]} (hd : d.natDegree ≤ k) {v : ℝ}
    (h0 : ∀ m ≤ r, (derivative^[m] d).eval v = 0) (t : ℝ) :
    d.eval t = ∑ s ∈ Finset.Ioc r k, (taylor v d).coeff s * (t - v) ^ s := by
  have hcoeff : ∀ m ≤ r, (taylor v d).coeff m = 0 := by
    intro m hm
    have h := congrArg (Polynomial.eval v) (congrFun (factorial_smul_hasseDeriv (R := ℝ) m) d)
    rw [LinearMap.smul_apply, eval_smul, nsmul_eq_mul, h0 m hm] at h
    rw [taylor_coeff]
    have hfac : ((m.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    exact (mul_eq_zero.mp h).resolve_left hfac
  rw [← taylor_eval_sub v, eval_eq_sum_range' (n := k + 1) (by rw [natDegree_taylor]; omega)]
  rw [← Finset.sum_filter_of_ne (p := fun s => r < s)]
  · congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  · intro s _ hs
    by_contra hrs
    exact hs (by rw [hcoeff s (not_lt.mp hrs), zero_mul])

/-- The coefficient extraction behind the independence argument: if
`∑_{s < N} c_s (X - C v)^(r + 1 + s) = 0` then every `c_s` vanishes. -/
theorem eq_zero_of_sum_C_mul_X_sub_C_pow_eq_zero {N : ℕ} {c : Fin N → ℝ} {v : ℝ}
    (h : ∑ s : Fin N, C (c s) * (X - C v) ^ (r + 1 + s) = 0) (s : Fin N) : c s = 0 := by
  have h' := congrArg (taylor v) h
  simp only [map_sum, taylor_mul, taylor_C, taylor_pow, map_sub, taylor_X, add_sub_cancel_right,
    map_zero] at h'
  have := congrArg (fun p => p.coeff (r + 1 + s)) h'
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
  rw [Finset.sum_eq_single s (fun s' _ hs' => by
      rw [ite_eq_right]; intro h; exact hs' (Fin.ext (by omega)))
    (fun h => absurd (Finset.mem_univ s) h), ite_eq_left rfl] at this
  exact this

/-- A polynomial vanishing on a nondegenerate interval is the zero polynomial. -/
theorem eq_zero_of_eval_eq_zero_on_Icc {p : ℝ[X]} {u v : ℝ} (huv : u < v)
    (h : ∀ t ∈ Icc u v, p.eval t = 0) : p = 0 :=
  p.eq_zero_of_infinite_isRoot ((Icc_infinite huv).mono fun t ht => h t ht)

/-- **The truncated powers are linearly independent** ([quarteroni2000numerical] Exercise 8.10, the
independence half): on the first panel only the monomials survive, so their coefficients vanish;
then, panel by panel, only the truncated powers at breakpoints to the left survive, and the
coefficients of the powers at the newest breakpoint vanish because `(t - x_j)^s`, `r < s ≤ k`, are
independent polynomials. -/
theorem linearIndependent_truncPow (hx : IsPartition a b n x) (hn : 1 ≤ n) :
    LinearIndependent ℝ (truncPowFamily a b n x k r) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- the vanishing combination as a real function
  have hval : ∀ t : Icc a b, ∑ i : Fin (k + 1), g (Sum.inl i) * (t : ℝ) ^ (i : ℕ) +
      ∑ j : Fin (n - 1), ∑ s : Fin (k - r),
        g (Sum.inr (j, s)) * max ((t : ℝ) - x (j + 1)) 0 ^ (r + 1 + s) = 0 := by
    intro t
    have := congrArg (fun f : C(Icc a b, ℝ) => f t) hg
    simp only [ContinuousMap.coe_zero, Pi.zero_apply, Fintype.sum_sum_type,
      Fintype.sum_prod_type] at this
    simpa [truncPowFamily] using this
  -- truncated powers at breakpoints to the right of a point vanish there
  have hvan : ∀ (i : ℕ) (j : Fin (n - 1)) (s : Fin (k - r)) (t : ℝ), i ≤ n → t ≤ x i →
      i ≤ (j : ℕ) + 1 → max (t - x (j + 1)) 0 ^ (r + 1 + s) = 0 := by
    intro i j s t hi ht hij
    rw [max_eq_right (sub_nonpos.mpr (ht.trans (hx.mono hij (by have := j.2; omega)))),
      zero_pow (by omega)]
  -- the monomial coefficients vanish
  have hmono : ∀ i, g (Sum.inl i) = 0 := by
    have hpoly : (∑ i : Fin (k + 1), C (g (Sum.inl i)) * X ^ (i : ℕ)) = 0 := by
      refine eq_zero_of_eval_eq_zero_on_Icc (hx.step 0 hn) fun t ht => ?_
      have ht' : t ∈ Icc a b := hx.Icc_subset hn ht
      have h0 : ∑ i : Fin (k + 1), g (Sum.inl i) * t ^ (i : ℕ) + ∑ j : Fin (n - 1),
          ∑ s : Fin (k - r), g (Sum.inr (j, s)) * max (t - x (j + 1)) 0 ^ (r + 1 + s) = 0 :=
        hval ⟨t, ht'⟩
      have hz : ∑ j : Fin (n - 1), ∑ s : Fin (k - r),
          g (Sum.inr (j, s)) * max (t - x (j + 1)) 0 ^ (r + 1 + s) = 0 :=
        Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun s _ => by
          rw [hvan 1 j s t hn (by simpa using ht.2) (by omega), mul_zero]
      rw [hz, add_zero] at h0
      simpa only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] using h0
    intro i
    have := congrArg (fun p => p.coeff (i : ℕ)) hpoly
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single i (fun i' _ hi' => by
        rw [ite_eq_right]; intro h; exact hi' (Fin.ext h.symm))
      (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl] at this
    exact this
  -- the truncated-power coefficients vanish, breakpoint by breakpoint
  have htrunc : ∀ m : ℕ, ∀ j : Fin (n - 1), (j : ℕ) ≤ m → ∀ s, g (Sum.inr (j, s)) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro j hjm s
    have hj : (j : ℕ) + 1 < n := by have := j.2; omega
    have hpoly : (∑ s : Fin (k - r), C (g (Sum.inr (j, s))) * (X - C (x (j + 1))) ^ (r + 1 + s))
        = 0 := by
      refine eq_zero_of_eval_eq_zero_on_Icc (hx.step (j + 1) hj) fun t ht => ?_
      have ht' : t ∈ Icc a b := hx.Icc_subset hj ht
      have h0 : ∑ i : Fin (k + 1), g (Sum.inl i) * t ^ (i : ℕ) + ∑ j : Fin (n - 1),
          ∑ s : Fin (k - r), g (Sum.inr (j, s)) * max (t - x (j + 1)) 0 ^ (r + 1 + s) = 0 :=
        hval ⟨t, ht'⟩
      simp only [hmono, zero_mul, Finset.sum_const_zero, zero_add] at h0
      rw [Finset.sum_eq_single j] at h0
      · simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
        rw [← h0]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [max_eq_left (sub_nonneg.mpr ht.1)]
      · intro j' _ hj'
        rcases lt_or_gt_of_ne (fun h => hj' (Fin.ext h)) with h | h
        · refine Finset.sum_eq_zero fun s _ => ?_
          rw [ih j' (by omega) j' le_rfl s, zero_mul]
        · refine Finset.sum_eq_zero fun s _ => ?_
          rw [hvan (j + 2) j' s t (by omega) (by simpa [add_assoc] using ht.2) (by omega),
            mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    exact eq_zero_of_sum_C_mul_X_sub_C_pow_eq_zero hpoly s
  rintro (i | ⟨j, s⟩)
  · exact hmono i
  · exact htrunc j j le_rfl s

/-- Reindexing a sum over `Ioc r k` by `s ↦ r + 1 + s` over `Fin (k - r)`. -/
theorem sum_Ioc_eq_sum_fin (F : ℕ → ℝ) :
    ∑ s ∈ Finset.Ioc r k, F s = ∑ s : Fin (k - r), F (r + 1 + s) := by
  have : Finset.Ioc r k = Finset.Ico (r + 1) (k + 1) := by
    ext s; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [this, Finset.sum_Ico_eq_sum_range, Fin.sum_univ_eq_sum_range (fun s => F (r + 1 + s)),
    Nat.succ_sub_succ_eq_sub]

/-- **The truncated powers span the spline space** ([quarteroni2000numerical] Exercise 8.10, the
spanning half): a spline is its first panel polynomial `p_0` plus, at each interior breakpoint
`x_j`, the difference `p_j - p_{j-1}` of the two adjacent panel polynomials, which has order-`r`
contact with zero at `x_j` (`iterate_derivative_eval_eq_zero_of_eqOn`) and is therefore a
combination of `(t - x_j)^s`, `r < s ≤ k`, which continued by zero to the left is a combination of
the truncated powers. -/
theorem span_truncPow_eq_splineSpace (hx : IsPartition a b n x) (hn : 1 ≤ n) :
    Submodule.span ℝ (Set.range (truncPowFamily a b n x k r)) = splineSpace a b n x k r := by
  classical
  refine le_antisymm (Submodule.span_le.mpr ?_) fun f hf => ?_
  · rintro _ ⟨i, rfl⟩
    exact truncPowFamily_mem_splineSpace hx i
  obtain ⟨g, hg, hf, hp⟩ := hf
  have hp' : ∀ j, ∃ p : ℝ[X], j < n → p.degree ≤ k ∧ EqOn g p.eval (Icc (x j) (x (j + 1))) :=
    fun j => if h : j < n then (hp j h).imp fun _ hp' _ => hp' else ⟨0, fun h' => absurd h' h⟩
  choose p hp using hp'
  -- the coefficients
  set c : TruncPowIndex n k r → ℝ := fun i => match i with
    | Sum.inl i => (p 0).coeff i
    | Sum.inr (j, s) => (taylor (x (j + 1)) (p (j + 1) - p j)).coeff (r + 1 + s) with hc
  have hdeg : ∀ j < n, (p j).natDegree ≤ k := fun j hj =>
    natDegree_le_of_degree_le (hp j hj).1
  -- the differences of adjacent panel polynomials as sums of shifted powers
  have hdiff : ∀ j : Fin (n - 1), ∀ t, (p (j + 1) - p j).eval t =
      ∑ s : Fin (k - r), c (Sum.inr (j, s)) * (t - x (j + 1)) ^ (r + 1 + s) := by
    intro j t
    have hj : (j : ℕ) + 1 < n := by have := j.2; omega
    rw [eval_eq_sum_Ioc_of_iterate_derivative_eq_zero (k := k) (r := r)
      ((natDegree_sub_le _ _).trans (max_le (hdeg _ hj) (hdeg _ (by omega)))), sum_Ioc_eq_sum_fin]
    intro m hm
    refine iterate_derivative_eval_eq_zero_of_eqOn (e := fun t => g t - (p j).eval t)
      (hx.step j (by omega)) (hx.step (j + 1) hj) ?_ ?_ ?_ hm
    · exact (hg.mono (Ioo_subset_Icc_self.trans
        (Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right (by omega))))).sub
        ((p j).contDiff_eval _).contDiffOn
    · intro t ht
      simp [(hp j (by omega)).2 (Ioo_subset_Icc_self ht)]
    · intro t ht
      simp [(hp (j + 1) hj).2 (Ioo_subset_Icc_self ht)]
  -- the claimed representation
  have hrep : f = ∑ i, c i • truncPowFamily a b n x k r i := by
    ext t
    obtain ⟨i, hi1, hin, hti, -⟩ := hx.exists_mem_panel hn t.2
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    simp only [add_tsub_cancel_right] at hti
    have hmn : m < n := by omega
    rw [hf t, (hp m hmn).2 hti]
    have hrhs : (∑ i, c i • truncPowFamily a b n x k r i) t =
        ∑ i : Fin (k + 1), c (Sum.inl i) * (t : ℝ) ^ (i : ℕ) + ∑ j : Fin (n - 1),
          ∑ s : Fin (k - r), c (Sum.inr (j, s)) * max ((t : ℝ) - x (j + 1)) 0 ^ (r + 1 + s) := by
      simp [Fintype.sum_sum_type, Fintype.sum_prod_type, truncPowFamily]
    rw [hrhs]
    -- the monomial part is `p 0`
    have h0 : ∑ i : Fin (k + 1), c (Sum.inl i) * (t : ℝ) ^ (i : ℕ) = (p 0).eval (t : ℝ) := by
      rw [eval_eq_sum_range' (n := k + 1) (by have := hdeg 0 hn; omega),
        Fin.sum_univ_eq_sum_range (fun i => (p 0).coeff i * (t : ℝ) ^ i)]
    -- the truncated part telescopes
    have h1 : ∑ j : Fin (n - 1), ∑ s : Fin (k - r),
        c (Sum.inr (j, s)) * max ((t : ℝ) - x (j + 1)) 0 ^ (r + 1 + s) =
        ∑ j ∈ Finset.range m, ((p (j + 1)).eval (t : ℝ) - (p j).eval (t : ℝ)) := by
      have : ∀ j : Fin (n - 1), ∑ s : Fin (k - r),
          c (Sum.inr (j, s)) * max ((t : ℝ) - x (j + 1)) 0 ^ (r + 1 + s) =
          if (j : ℕ) < m then (p (j + 1)).eval (t : ℝ) - (p j).eval (t : ℝ) else 0 := by
        intro j
        split_ifs with hjm
        · rw [← eval_sub, hdiff j]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [max_eq_left (sub_nonneg.mpr ((hx.mono (by omega) hmn.le).trans hti.1))]
        · refine Finset.sum_eq_zero fun s _ => ?_
          rw [max_eq_right (sub_nonpos.mpr (hti.2.trans (hx.mono (by omega)
            (by have := j.2; omega)))), zero_pow (by omega), mul_zero]
      simp_rw [this]
      rw [Fin.sum_univ_eq_sum_range (fun j => if j < m then (p (j + 1)).eval (t : ℝ) -
        (p j).eval (t : ℝ) else 0) (n - 1), ← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [h0, h1, Finset.sum_range_sub (fun j => (p j).eval (t : ℝ)) m]
    ring
  rw [hrep]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The number of truncated-power basis functions. -/
theorem card_truncPowIndex (hn : 1 ≤ n) (hrk : r ≤ k) :
    Fintype.card (TruncPowIndex n k r) = n * (k - r) + r + 1 := by
  simp only [TruncPowIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, k = r + d := ⟨k - r, by omega⟩
  simp only [add_tsub_cancel_right, add_tsub_cancel_left]
  ring

/-- **The dimension of the spline space** ([quarteroni2000numerical] Definition 8.1,
`dim S_k = n + k`, and (8.43)): `dim S_k^r = n (k - r) + r + 1`; for `r = k - 1` this is `n + k`,
for `r = 0` it is `n k + 1`. -/
theorem finrank_splineSpace (hx : IsPartition a b n x) (hn : 1 ≤ n) (hrk : r ≤ k) :
    Module.finrank ℝ (splineSpace a b n x k r) = n * (k - r) + r + 1 := by
  rw [← span_truncPow_eq_splineSpace hx hn, finrank_span_eq_card (linearIndependent_truncPow hx hn),
    card_truncPowIndex hn hrk]

/-- The spline space of a partition is finite-dimensional. -/
theorem finiteDimensional_splineSpace (hx : IsPartition a b n x) (hn : 1 ≤ n) :
    FiniteDimensional ℝ (splineSpace a b n x k r) := by
  rw [← span_truncPow_eq_splineSpace hx hn]
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- **The truncated-power basis of `S_k`** ([quarteroni2000numerical] Exercise 8.10): a basis of
`S_k = S_k^{k-1}` indexed by `Fin (n + k)` whose first `k + 1` vectors are the monomials
`1, t, …, t^k` and whose remaining `n - 1` vectors are the truncated powers `(t - x_j)_+^k`,
`j = 1, …, n - 1`. -/
theorem exists_basis_truncPow (hx : IsPartition a b n x) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ B : Module.Basis (Fin (n + k)) ℝ (splineSpace a b n x k (k - 1)),
      (∀ i : Fin (n + k), (i : ℕ) ≤ k → ∀ t : Icc a b,
        (B i : C(Icc a b, ℝ)) t = (t : ℝ) ^ (i : ℕ)) ∧
      ∀ i : Fin (n + k), k < i → ∀ t : Icc a b,
        (B i : C(Icc a b, ℝ)) t = Quadrature.truncPow k (t : ℝ) (x (i - k)) := by
  classical
  set φ : TruncPowIndex n k (k - 1) → Fin (n + k) := fun i => match i with
    | Sum.inl i => ⟨i, by have := i.2; omega⟩
    | Sum.inr (j, _) => ⟨k + 1 + j, by have := j.2; omega⟩ with hφ
  have hφb : Function.Bijective φ := by
    constructor
    · rintro (i | ⟨j, s⟩) (i' | ⟨j', s'⟩) h <;> simp only [hφ, Fin.mk.injEq] at h
      · exact congrArg Sum.inl (Fin.ext h)
      · omega
      · omega
      · have hs : s = s' := Fin.ext (by have := s.2; have := s'.2; omega)
        rw [hs, show j = j' from Fin.ext (by omega)]
    · intro i
      by_cases hi : (i : ℕ) ≤ k
      · exact ⟨Sum.inl ⟨i, by omega⟩, Fin.ext rfl⟩
      · exact ⟨Sum.inr (⟨i - k - 1, by have := i.2; omega⟩, ⟨0, by omega⟩), Fin.ext (by
          simp only [hφ]; omega)⟩
  set e : TruncPowIndex n k (k - 1) ≃ Fin (n + k) := Equiv.ofBijective φ hφb with he
  set B₀ := Module.Basis.span (linearIndependent_truncPow (k := k) (r := k - 1) hx hn) with hB₀
  set B := (B₀.map (LinearEquiv.ofEq _ _ (span_truncPow_eq_splineSpace hx hn))).reindex e with hB
  have hBval : ∀ i, (B i : C(Icc a b, ℝ)) = truncPowFamily a b n x k (k - 1) (e.symm i) := by
    intro i
    rw [hB, Module.Basis.reindex_apply, Module.Basis.map_apply, hB₀, Module.Basis.span_apply]
    rfl
  refine ⟨B, fun i hi t => ?_, fun i hi t => ?_⟩
  · have : e.symm i = Sum.inl ⟨i, by omega⟩ := by
      rw [Equiv.symm_apply_eq]; exact Fin.ext rfl
    rw [hBval, this]
    rfl
  · have : e.symm i = Sum.inr (⟨i - k - 1, by have := i.2; omega⟩, ⟨0, by omega⟩) := by
      rw [Equiv.symm_apply_eq]
      exact Fin.ext (by simp only [he, Equiv.ofBijective_apply, hφ]; omega)
    rw [hBval, this]
    change truncPowCM a b (x (i - k - 1 + 1)) (k - 1 + 1 + 0) t = _
    rw [show i - k - 1 + 1 = i - k by omega, show k - 1 + 1 + 0 = k by omega]
    exact truncPowCM_apply_eq a b _ hk t

/-! ### Gluing functions along a partition

A function given panel by panel — `Q i` on the panel `[x (i - 1), x i]`, `1 ≤ i ≤ n` — is glued
by `panelGlue`, which selects the panel through `panelIndex`. The first and the last panels are
extended to `-∞` and `+∞` (`extPanel`), so that the glued function is defined and locally a panel
function everywhere on `ℝ`, not only on `[a, b]`: derivatives at the nodes are then ordinary
derivatives, and the smoothness of the glued function follows from the agreement of the panel
functions at the interior nodes (`hasDerivAt_panelGlue`, `continuous_panelGlue`). -/

/-- The index of the panel containing `t`: `i` when `x (i - 1) ≤ t < x i` for `1 ≤ i < n`, `1`
below `x 1`, and `n` from `x (n - 1)` on. -/
noncomputable def panelIndex (n : ℕ) (x : ℕ → ℝ) (t : ℝ) : ℕ :=
  1 + ((Finset.Ico 1 n).filter fun j => x j ≤ t).card

/-- The function equal to `Q i` on the panel `[x (i - 1), x i]`. -/
noncomputable def panelGlue {E : Type*} (n : ℕ) (x : ℕ → ℝ) (Q : ℕ → ℝ → E) (t : ℝ) : E :=
  Q (panelIndex n x t) t

/-- The `i`-th panel, extended to `-∞` when `i = 1` and to `+∞` when `i = n`. -/
def extPanel (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : Set ℝ :=
  {t | (1 < i → x (i - 1) ≤ t) ∧ (i < n → t ≤ x i)}

/-- Membership of the extended panel. -/
theorem mem_extPanel_iff {i : ℕ} {t : ℝ} :
    t ∈ extPanel n x i ↔ (1 < i → x (i - 1) ≤ t) ∧ (i < n → t ≤ x i) := Iff.rfl

/-- A closed panel lies in its extension. -/
theorem Icc_subset_extPanel (i : ℕ) : Icc (x (i - 1)) (x i) ⊆ extPanel n x i :=
  fun _ ht => ⟨fun _ => ht.1, fun _ => ht.2⟩

/-- The panel index of a point of the `i`-th half-open panel is `i`. -/
theorem panelIndex_eq (hx : IsPartition a b n x) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) {t : ℝ}
    (ht1 : 1 < i → x (i - 1) ≤ t) (ht2 : i < n → t < x i) : panelIndex n x t = i := by
  classical
  have : ((Finset.Ico 1 n).filter fun j => x j ≤ t) = Finset.Ico 1 i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hj1, hjn⟩, hjt⟩
      refine ⟨hj1, ?_⟩
      by_contra h
      have hin' : i < n := lt_of_le_of_lt (not_lt.mp h) hjn
      exact absurd ((hx.mono (not_lt.mp h) hjn.le).trans hjt) (not_le.mpr (ht2 hin'))
    · rintro ⟨hj1, hji⟩
      exact ⟨⟨hj1, by omega⟩, (hx.mono (by omega) (by omega)).trans (ht1 (by omega))⟩
  rw [panelIndex, this, Nat.card_Ico]
  omega

/-- On the `i`-th extended panel the glued function is `Q i`, provided the panel functions agree
at the interior nodes. -/
theorem panelGlue_eq_of_mem (hx : IsPartition a b n x) {Q : ℕ → ℝ → ℝ}
    (hQ : ∀ i, 1 ≤ i → i < n → Q i (x i) = Q (i + 1) (x i)) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {t : ℝ} (ht : t ∈ extPanel n x i) : panelGlue n x Q t = Q i t := by
  by_cases h : i < n ∧ t = x i
  · obtain ⟨hin', rfl⟩ := h
    rw [panelGlue, panelIndex_eq hx (i := i + 1) (by omega) hin' (fun _ => by simp)
      (fun h => by simpa using hx.step i hin'), hQ i hi1 hin']
  · rw [panelGlue, panelIndex_eq hx hi1 hin ht.1 fun hin' =>
      lt_of_le_of_ne (ht.2 hin') fun h' => h ⟨hin', h'⟩]

/-- Every real number has an extended panel that is a neighbourhood of it, or is an interior node
`x i` with the union of the two adjacent extended panels a neighbourhood of it. -/
theorem IsPartition.exists_extPanel_mem_nhds (hx : IsPartition a b n x) (hn : 1 ≤ n) (t : ℝ) :
    ∃ i, 1 ≤ i ∧ i ≤ n ∧ t ∈ extPanel n x i ∧ (extPanel n x i ∈ 𝓝 t ∨
      (t = x i ∧ i < n ∧ extPanel n x i ∪ extPanel n x (i + 1) ∈ 𝓝 t)) := by
  rcases le_or_gt t a with hta | hat
  · refine ⟨1, le_rfl, hn, ⟨fun h => absurd h (lt_irrefl _), fun _ => hta.trans ?_⟩, Or.inl ?_⟩
    · exact hx.first ▸ (hx.step 0 hn).le
    · refine mem_of_superset (Iio_mem_nhds (hta.trans_lt (hx.first ▸ hx.step 0 hn))) ?_
      exact fun s hs => ⟨fun h => absurd h (lt_irrefl _), fun _ => le_of_lt hs⟩
  rcases le_or_gt b t with hbt | htb
  · refine ⟨n, hn, le_rfl, ⟨fun _ => ?_, fun h => absurd h (lt_irrefl _)⟩, Or.inl ?_⟩
    · exact (hx.le_right (Nat.sub_le n 1)).trans hbt
    · have hlt : x (n - 1) < t := by
        refine lt_of_lt_of_le ?_ hbt
        rw [← hx.last]
        exact hx.lt (by omega) le_rfl
      refine mem_of_superset (Ioi_mem_nhds hlt) ?_
      exact fun s hs => ⟨fun _ => le_of_lt hs, fun h => absurd h (lt_irrefl _)⟩
  obtain ⟨i, hi1, hin, hti, hlt⟩ := hx.exists_mem_panel hn ⟨hat.le, htb.le⟩
  have hlt' : x (i - 1) < t := by
    rcases hlt with h | rfl
    · exact h
    · simpa [hx.first] using hat
  rcases lt_or_eq_of_le hti.2 with htx | htx
  · refine ⟨i, hi1, hin, Icc_subset_extPanel i hti, Or.inl ?_⟩
    exact mem_of_superset (Ioo_mem_nhds hlt' htx)
      fun s hs => ⟨fun _ => hs.1.le, fun _ => hs.2.le⟩
  · have hin' : i < n := by
      by_contra h
      have : i = n := by omega
      subst this
      exact absurd (htx ▸ htb) (hx.last ▸ lt_irrefl _)
    refine ⟨i, hi1, hin, Icc_subset_extPanel i hti, Or.inr ⟨htx, hin', ?_⟩⟩
    refine mem_of_superset (Ioo_mem_nhds hlt' (htx ▸ hx.step i hin')) fun s hs => ?_
    rcases le_or_gt s (x i) with hsx | hsx
    · exact Or.inl ⟨fun _ => hs.1.le, fun _ => hsx⟩
    · exact Or.inr ⟨fun _ => by simpa using hsx.le, fun _ => hs.2.le⟩

/-- **Differentiability of a glued function.** If the panel functions `Q i` have derivatives
`Q' i` on their extended panels, and both the `Q i` and the `Q' i` agree at the interior nodes,
then the glued function is differentiable everywhere with derivative the glued `Q'`. -/
theorem hasDerivAt_panelGlue (hx : IsPartition a b n x) (hn : 1 ≤ n) {Q Q' : ℕ → ℝ → ℝ}
    (hQ : ∀ i, 1 ≤ i → i < n → Q i (x i) = Q (i + 1) (x i))
    (hQ' : ∀ i, 1 ≤ i → i < n → Q' i (x i) = Q' (i + 1) (x i))
    (hd : ∀ i, 1 ≤ i → i ≤ n → ∀ t ∈ extPanel n x i, HasDerivAt (Q i) (Q' i t) t) (t : ℝ) :
    HasDerivAt (panelGlue n x Q) (panelGlue n x Q' t) t := by
  obtain ⟨i, hi1, hin, hti, hcase⟩ := hx.exists_extPanel_mem_nhds hn t
  have hloc : ∀ j, 1 ≤ j → j ≤ n → t ∈ extPanel n x j →
      HasDerivWithinAt (panelGlue n x Q) (Q' j t) (extPanel n x j) t := fun j hj1 hjn htj =>
    ((hd j hj1 hjn t htj).hasDerivWithinAt).congr
      (fun s hs => panelGlue_eq_of_mem hx hQ hj1 hjn hs) (panelGlue_eq_of_mem hx hQ hj1 hjn htj)
  rw [panelGlue_eq_of_mem hx hQ' hi1 hin hti]
  rcases hcase with hmem | ⟨rfl, hin', hmem⟩
  · exact (hloc i hi1 hin hti).hasDerivAt hmem
  · have h2 := hloc (i + 1) (by omega) hin' ⟨fun _ => by simp, fun _ => (hx.step i hin').le⟩
    rw [← hQ' i hi1 hin'] at h2
    exact ((hloc i hi1 hin hti).union h2).hasDerivAt hmem

/-- **Continuity of a glued function.** If the panel functions are continuous on their extended
panels and agree at the interior nodes, the glued function is continuous. -/
theorem continuous_panelGlue (hx : IsPartition a b n x) (hn : 1 ≤ n) {Q : ℕ → ℝ → ℝ}
    (hQ : ∀ i, 1 ≤ i → i < n → Q i (x i) = Q (i + 1) (x i))
    (hc : ∀ i, 1 ≤ i → i ≤ n → ContinuousOn (Q i) (extPanel n x i)) :
    Continuous (panelGlue n x Q) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  obtain ⟨i, hi1, hin, hti, hcase⟩ := hx.exists_extPanel_mem_nhds hn t
  have hloc : ∀ j, 1 ≤ j → j ≤ n → t ∈ extPanel n x j →
      ContinuousWithinAt (panelGlue n x Q) (extPanel n x j) t := fun j hj1 hjn htj =>
    (hc j hj1 hjn t htj).congr (fun s hs => panelGlue_eq_of_mem hx hQ hj1 hjn hs)
      (panelGlue_eq_of_mem hx hQ hj1 hjn htj)
  rcases hcase with hmem | ⟨rfl, hin', hmem⟩
  · exact (hloc i hi1 hin hti).continuousAt hmem
  · have h2 := hloc (i + 1) (by omega) hin' ⟨fun _ => by simp, fun _ => (hx.step i hin').le⟩
    exact ((hloc i hi1 hin hti).union h2).continuousAt hmem

/-- A function with a derivative `u₁` everywhere, where `u₁` has a continuous derivative `u₂`,
is `C²`. -/
theorem contDiff_two_of_hasDerivAt {u u₁ u₂ : ℝ → ℝ} (h₁ : ∀ t, HasDerivAt u (u₁ t) t)
    (h₂ : ∀ t, HasDerivAt u₁ (u₂ t) t) (h₃ : Continuous u₂) : ContDiff ℝ 2 u := by
  have hd₁ : deriv u = u₁ := funext fun t => (h₁ t).deriv
  have hd₂ : deriv u₁ = u₂ := funext fun t => (h₂ t).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun t => (h₁ t).differentiableAt, fun h => absurd h (by simp), ?_⟩
  rw [hd₁, contDiff_one_iff_deriv, hd₂]
  exact ⟨fun t => (h₂ t).differentiableAt, h₃⟩

/-! ### The panel cubics -/

/-- **The cubic on the panel `[x (i - 1), x i]`** with end values `f (i - 1), f i` and end second
derivatives `M (i - 1), M i` ([quarteroni2000numerical] (8.46) integrated twice, with
`h_i = x i - x (i - 1)`): `M_{i-1} (x_i - t)³/(6 h_i) + M_i (t - x_{i-1})³/(6 h_i)
+ C_{i-1} (t - x_{i-1}) + C̃_{i-1}`, `C̃_{i-1} = f_{i-1} - M_{i-1} h_i²/6`,
`C_{i-1} = (f_i - f_{i-1})/h_i - (h_i/6)(M_i - M_{i-1})`, as a polynomial. -/
noncomputable def panelCubicPoly (x : ℕ → ℝ) (f M : ℕ → ℝ) (i : ℕ) : ℝ[X] :=
  C (M (i - 1) / (6 * (x i - x (i - 1)))) * (C (x i) - X) ^ 3
    + C (M i / (6 * (x i - x (i - 1)))) * (X - C (x (i - 1))) ^ 3
    + C ((f i - f (i - 1)) / (x i - x (i - 1)) - (x i - x (i - 1)) / 6 * (M i - M (i - 1)))
      * (X - C (x (i - 1)))
    + C (f (i - 1) - M (i - 1) * (x i - x (i - 1)) ^ 2 / 6)

/-- The panel cubic as a function. -/
noncomputable def panelCubic (x : ℕ → ℝ) (f M : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  (panelCubicPoly x f M i).eval t

/-- The panel cubic has degree at most `3`. -/
theorem degree_panelCubicPoly_le (x f M : ℕ → ℝ) (i : ℕ) : (panelCubicPoly x f M i).degree ≤ 3 := by
  unfold panelCubicPoly
  refine (degree_add_le _ _).trans (max_le ((degree_add_le _ _).trans (max_le
    ((degree_add_le _ _).trans (max_le ?_ ?_)) ?_)) ?_)
  · refine (degree_mul_le _ _).trans ?_
    calc (C _).degree + ((C (x i) - X) ^ 3).degree ≤ 0 + 3 • (C (x i) - X).degree :=
          add_le_add degree_C_le (degree_pow_le _ _)
      _ ≤ 0 + 3 • 1 := by
          gcongr
          exact (degree_sub_le _ _).trans (max_le (degree_C_le.trans zero_le_one) degree_X_le)
      _ = 3 := by simp
  · refine (degree_mul_le _ _).trans ?_
    calc (C _).degree + ((X - C (x (i - 1))) ^ 3).degree ≤ 0 + 3 • (X - C (x (i - 1))).degree :=
          add_le_add degree_C_le (degree_pow_le _ _)
      _ ≤ 0 + 3 • 1 := by gcongr; exact degree_X_sub_C_le _
      _ = 3 := by simp
  · refine (degree_mul_le _ _).trans ?_
    calc (C _).degree + (X - C (x (i - 1))).degree ≤ 0 + 1 :=
          add_le_add degree_C_le (degree_X_sub_C_le _)
      _ ≤ 3 := by norm_num
  · exact degree_C_le.trans (by norm_num)

/-- The explicit form of the panel cubic. -/
theorem panelCubic_apply (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    panelCubic x f M i t = M (i - 1) * (x i - t) ^ 3 / (6 * (x i - x (i - 1)))
      + M i * (t - x (i - 1)) ^ 3 / (6 * (x i - x (i - 1)))
      + ((f i - f (i - 1)) / (x i - x (i - 1)) - (x i - x (i - 1)) / 6 * (M i - M (i - 1)))
        * (t - x (i - 1))
      + (f (i - 1) - M (i - 1) * (x i - x (i - 1)) ^ 2 / 6) := by
  simp only [panelCubic, panelCubicPoly, eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  ring

/-- The first derivative of the panel cubic, as a function. -/
noncomputable def panelCubicD1 (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  (derivative (panelCubicPoly x f M i)).eval t

/-- The second derivative of the panel cubic, as a function. -/
noncomputable def panelCubicD2 (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  (derivative (derivative (panelCubicPoly x f M i))).eval t

/-- The (constant) third derivative of the panel cubic. -/
noncomputable def panelCubicD3 (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) : ℝ :=
  (derivative (derivative (derivative (panelCubicPoly x f M i)))).eval t

/-- The panel cubic has derivative `panelCubicD1`. -/
theorem hasDerivAt_panelCubic (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    HasDerivAt (panelCubic x f M i) (panelCubicD1 x f M i t) t :=
  (panelCubicPoly x f M i).hasDerivAt t

/-- `panelCubicD1` has derivative `panelCubicD2`. -/
theorem hasDerivAt_panelCubicD1 (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    HasDerivAt (panelCubicD1 x f M i) (panelCubicD2 x f M i t) t :=
  (derivative (panelCubicPoly x f M i)).hasDerivAt t

/-- `panelCubicD2` has derivative `panelCubicD3`. -/
theorem hasDerivAt_panelCubicD2 (x f M : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    HasDerivAt (panelCubicD2 x f M i) (panelCubicD3 x f M i t) t :=
  (derivative (derivative (panelCubicPoly x f M i))).hasDerivAt t

/-- The explicit form of the first derivative of the panel cubic. -/
theorem panelCubicD1_apply (x f M : ℕ → ℝ) {i : ℕ} (hh : x (i - 1) < x i) (t : ℝ) :
    panelCubicD1 x f M i t = -(M (i - 1) * (x i - t) ^ 2) / (2 * (x i - x (i - 1)))
      + M i * (t - x (i - 1)) ^ 2 / (2 * (x i - x (i - 1)))
      + ((f i - f (i - 1)) / (x i - x (i - 1)) - (x i - x (i - 1)) / 6 * (M i - M (i - 1))) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  simp only [panelCubicD1, panelCubicPoly, derivative_add, derivative_mul, derivative_C,
    derivative_pow, derivative_sub, derivative_X, eval_add, eval_mul, eval_C, eval_pow, eval_sub,
    eval_X, eval_zero, eval_one]
  field_simp
  ring

/-- **The second derivative of the panel cubic is linear**, interpolating the moments
([quarteroni2000numerical] (8.46)): `M_{i-1} (x_i - t)/h_i + M_i (t - x_{i-1})/h_i`. -/
theorem panelCubicD2_apply (x f M : ℕ → ℝ) {i : ℕ} (hh : x (i - 1) < x i) (t : ℝ) :
    panelCubicD2 x f M i t = M (i - 1) * (x i - t) / (x i - x (i - 1))
      + M i * (t - x (i - 1)) / (x i - x (i - 1)) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  simp only [panelCubicD2, panelCubicPoly, derivative_add, derivative_mul, derivative_C,
    derivative_pow, derivative_sub, derivative_X, derivative_one, derivative_zero, eval_add,
    eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_zero, eval_one]
  field_simp
  ring

/-- The third derivative of the panel cubic is the constant `(M_i - M_{i-1})/h_i`. -/
theorem panelCubicD3_apply (x f M : ℕ → ℝ) {i : ℕ} (hh : x (i - 1) < x i) (t : ℝ) :
    panelCubicD3 x f M i t = (M i - M (i - 1)) / (x i - x (i - 1)) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  simp only [panelCubicD3, panelCubicPoly, derivative_add, derivative_mul, derivative_C,
    derivative_pow, derivative_sub, derivative_X, derivative_one, derivative_zero, eval_add,
    eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_zero, eval_one]
  field_simp
  ring

section PanelCubicValues

variable {f M : ℕ → ℝ} {i : ℕ}

/-- The panel cubic takes the value `f (i - 1)` at the left end of its panel. -/
theorem panelCubic_left (hh : x (i - 1) < x i) : panelCubic x f M i (x (i - 1)) = f (i - 1) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubic_apply]
  field_simp
  ring

/-- The panel cubic takes the value `f i` at the right end of its panel. -/
theorem panelCubic_right (hh : x (i - 1) < x i) : panelCubic x f M i (x i) = f i := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubic_apply]
  field_simp
  ring

/-- The panel cubic of the panel `[x i, x (i + 1)]` takes the value `f i` at `x i`. -/
theorem panelCubic_left_succ (hh : x i < x (i + 1)) : panelCubic x f M (i + 1) (x i) = f i := by
  have := panelCubic_left (x := x) (f := f) (M := M) (i := i + 1) (by simpa using hh)
  simpa using this

/-- The second derivative of the panel cubic is `M (i - 1)` at the left end. -/
theorem panelCubicD2_left (hh : x (i - 1) < x i) :
    panelCubicD2 x f M i (x (i - 1)) = M (i - 1) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubicD2_apply x f M hh]
  field_simp
  ring

/-- The second derivative of the panel cubic of `[x i, x (i + 1)]` is `M i` at `x i`. -/
theorem panelCubicD2_left_succ (hh : x i < x (i + 1)) : panelCubicD2 x f M (i + 1) (x i) = M i := by
  have := panelCubicD2_left (x := x) (f := f) (M := M) (i := i + 1) (by simpa using hh)
  simpa using this

/-- The second derivative of the panel cubic is `M i` at the right end. -/
theorem panelCubicD2_right (hh : x (i - 1) < x i) : panelCubicD2 x f M i (x i) = M i := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubicD2_apply x f M hh]
  field_simp
  ring

/-- **The slope from the left at the node `x i`** ([quarteroni2000numerical], the first displayed
line before (8.47)): `s'(x_i^-) = h_i M_{i-1}/6 + h_i M_i/3 + (f_i - f_{i-1})/h_i`. -/
theorem panelCubicD1_right (hh : x (i - 1) < x i) :
    panelCubicD1 x f M i (x i) = (x i - x (i - 1)) * M (i - 1) / 6 + (x i - x (i - 1)) * M i / 3
      + (f i - f (i - 1)) / (x i - x (i - 1)) := by
  have h0 : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubicD1_apply x f M hh]
  field_simp
  ring

/-- **The slope from the right at the node `x i`** ([quarteroni2000numerical], the second displayed
line before (8.47)): `s'(x_i^+) = -h_{i+1} M_i/3 - h_{i+1} M_{i+1}/6 + (f_{i+1} - f_i)/h_{i+1}`. -/
theorem panelCubicD1_left (hh : x i < x (i + 1)) :
    panelCubicD1 x f M (i + 1) (x i) = -((x (i + 1) - x i) * M i) / 3
      - (x (i + 1) - x i) * M (i + 1) / 6 + (f (i + 1) - f i) / (x (i + 1) - x i) := by
  have h0 : x (i + 1) - x i ≠ 0 := sub_ne_zero.mpr hh.ne'
  rw [panelCubicD1_apply x f M (by simpa using hh)]
  simp only [add_tsub_cancel_right]
  field_simp
  ring

/-- The one-sided slope from the left at the node `x i`, as the derivative of the panel cubic
([quarteroni2000numerical], the first displayed line before (8.47)). -/
theorem deriv_panelCubic_right (hh : x (i - 1) < x i) :
    deriv (panelCubic x f M i) (x i) = (x i - x (i - 1)) * M (i - 1) / 6
      + (x i - x (i - 1)) * M i / 3 + (f i - f (i - 1)) / (x i - x (i - 1)) := by
  rw [(hasDerivAt_panelCubic x f M i (x i)).deriv, panelCubicD1_right hh]

/-- The one-sided slope from the right at the node `x i`, as the derivative of the next panel cubic
([quarteroni2000numerical], the second displayed line before (8.47)). -/
theorem deriv_panelCubic_left (hh : x i < x (i + 1)) :
    deriv (panelCubic x f M (i + 1)) (x i) = -((x (i + 1) - x i) * M i) / 3
      - (x (i + 1) - x i) * M (i + 1) / 6 + (f (i + 1) - f i) / (x (i + 1) - x i) := by
  rw [(hasDerivAt_panelCubic x f M (i + 1) (x i)).deriv, panelCubicD1_left hh]

end PanelCubicValues

/-! ### The moment system

The moments `M_i = s''(x_i)` of a `C²` piecewise cubic satisfy, at every interior node, the row
`μ_i M_{i-1} + 2 M_i + λ_i M_{i+1} = d_i` of [quarteroni2000numerical] (8.47), with
`μ_i = h_i/(h_i + h_{i+1})`, `λ_i = h_{i+1}/(h_i + h_{i+1})` and `d_i` the second divided difference
of the data scaled by `6`; two closure rows `2 M_0 + λ_0 M_1 = d_0`, `μ_n M_{n-1} + 2 M_n = d_n`
complete the tridiagonal system (8.48). The panel lengths are a function `h : ℕ → ℝ`, `h i` being
the length of the `i`-th panel `[x (i - 1), x i]`. -/

/-- The superdiagonal coefficient `λ_i = h_{i+1}/(h_i + h_{i+1})` of the moment system, `λ_0` being
the closure parameter. -/
noncomputable def momentLam (h : ℕ → ℝ) (lam0 : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then lam0 else h (i + 1) / (h i + h (i + 1))

/-- The subdiagonal coefficient `μ_i = h_i/(h_i + h_{i+1})` of the moment system, `μ_n` being the
closure parameter. -/
noncomputable def momentMu (n : ℕ) (h : ℕ → ℝ) (mun : ℝ) (i : ℕ) : ℝ :=
  if i = n then mun else h i / (h i + h (i + 1))

/-- **The M-continuity matrix** ([quarteroni2000numerical] (8.48)): tridiagonal with diagonal `2`,
superdiagonal `λ_i` and subdiagonal `μ_i`. -/
noncomputable def momentMatrix (n : ℕ) (h : ℕ → ℝ) (lam0 mun : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if (j : ℕ) = i then 2
    else if (j : ℕ) = i + 1 then momentLam h lam0 i
    else if (i : ℕ) = j + 1 then momentMu n h mun i
    else 0

/-- **The right-hand side of the moment system** ([quarteroni2000numerical] (8.47)–(8.48)):
`d_i = (6/(h_i + h_{i+1})) ((f_{i+1} - f_i)/h_{i+1} - (f_i - f_{i-1})/h_i)` at the interior nodes,
and the closure values `d_0`, `d_n` at the ends. -/
noncomputable def momentRhs (n : ℕ) (h : ℕ → ℝ) (f : ℕ → ℝ) (d0 dn : ℝ) : Fin (n + 1) → ℝ :=
  fun i =>
    if (i : ℕ) = 0 then d0 else if (i : ℕ) = n then dn
    else 6 / (h i + h (i + 1)) * ((f (i + 1) - f i) / h (i + 1) - (f i - f (i - 1)) / h i)

/-- A sequence indexed by `Fin (n + 1)`, continued by `0` to `ℕ`. -/
noncomputable def extendFin {E : Type*} [Zero E] (v : Fin (n + 1) → E) : ℕ → E :=
  Function.extend Fin.val v 0

/-- The extension agrees with the sequence on `Fin (n + 1)`. -/
@[simp]
theorem extendFin_val {E : Type*} [Zero E] (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    extendFin v i = v i :=
  Fin.val_injective.extend_apply _ _ _

/-- The extension agrees with the sequence below `n + 1`. -/
theorem extendFin_of_lt {E : Type*} [Zero E] (v : Fin (n + 1) → E) {i : ℕ} (hi : i < n + 1) :
    extendFin v i = v ⟨i, hi⟩ :=
  extendFin_val v ⟨i, hi⟩

/-- The extension vanishes beyond `n`. -/
theorem extendFin_of_le {E : Type*} [Zero E] (v : Fin (n + 1) → E) {i : ℕ} (hi : n + 1 ≤ i) :
    extendFin v i = 0 := by
  rw [extendFin, Function.extend_apply']
  · rfl
  · rintro ⟨j, rfl⟩
    exact absurd j.2 (not_lt.mpr hi)

/-- The entries of the moment matrix, written as a sum of three indicator terms. -/
theorem momentMatrix_apply (n : ℕ) (h : ℕ → ℝ) (lam0 mun : ℝ) (i j : Fin (n + 1)) :
    momentMatrix n h lam0 mun i j = (if j = i then 2 else 0)
      + (if (j : ℕ) = i + 1 then momentLam h lam0 i else 0)
      + (if (i : ℕ) = j + 1 then momentMu n h mun i else 0) := by
  simp only [momentMatrix, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | omega | ring

/-- A sum over `Fin (n + 1)` of a term supported at the index `m`. -/
theorem sum_ite_val_eq_mul (c : ℝ) (v : Fin (n + 1) → ℝ) (m : ℕ) :
    ∑ j : Fin (n + 1), (if (j : ℕ) = m then c else 0) * v j = c * extendFin v m := by
  by_cases hm : m < n + 1
  · rw [Finset.sum_eq_single ⟨m, hm⟩ (fun j _ hj => by
      rw [ite_eq_right, zero_mul]; intro h; exact hj (Fin.ext h))
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl, extendFin_of_lt v hm]
  · rw [extendFin_of_le v (by omega), mul_zero]
    exact Finset.sum_eq_zero fun j _ => by
      rw [ite_eq_right, zero_mul]; intro h; exact hm (h ▸ j.2)

/-- **The moment matrix applied to a vector**: `(A v)_i = 2 v_i + λ_i v_{i+1} + μ_i v_{i-1}`, with
the missing neighbours read as `0`. -/
theorem momentMatrix_mulVec_apply (n : ℕ) (h : ℕ → ℝ) (lam0 mun : ℝ) (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    (momentMatrix n h lam0 mun).mulVec v i = 2 * v i + momentLam h lam0 i * extendFin v (i + 1)
      + momentMu n h mun i * (if (i : ℕ) = 0 then 0 else extendFin v (i - 1)) := by
  simp only [Matrix.mulVec, dotProduct, momentMatrix_apply, add_mul, Finset.sum_add_distrib]
  rw [sum_ite_val_eq_mul, Finset.sum_eq_single i (fun j _ hj => by
      rw [ite_eq_right, zero_mul]; exact fun h => hj h)
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]
  congr 1
  split_ifs with h0
  · rw [mul_zero]
    exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right, zero_mul]; omega
  · rw [← sum_ite_val_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ((i : ℕ) = j + 1) ↔ ((j : ℕ) = i - 1) := by omega
    simp only [this]

/-- The moment matrix is tridiagonal. -/
theorem isTridiagonal_momentMatrix (n : ℕ) (h : ℕ → ℝ) (lam0 mun : ℝ) :
    (momentMatrix n h lam0 mun).IsTridiagonal := by
  intro i j hij
  simp only [momentMatrix, Matrix.of_apply]
  split_ifs <;> first | rfl | (exfalso; omega)

section Dominance

open scoped Matrix.Norms.Operator

variable {h : ℕ → ℝ} {lam0 mun : ℝ}

/-- The off-diagonal row sum of the moment matrix is at most `|λ_i| + |μ_i|`, each term present
only when the corresponding neighbour exists. -/
theorem sum_norm_momentMatrix_le (i : Fin (n + 1)) :
    ∑ j ∈ Finset.univ.erase i, ‖momentMatrix n h lam0 mun i j‖ ≤
      (if (i : ℕ) < n then |momentLam h lam0 i| else 0)
        + (if 0 < (i : ℕ) then |momentMu n h mun i| else 0) := by
  have hrow : ∀ j ∈ Finset.univ.erase i, ‖momentMatrix n h lam0 mun i j‖ =
      (if (j : ℕ) = i + 1 then |momentLam h lam0 i| else 0)
        + (if (i : ℕ) = j + 1 then |momentMu n h mun i| else 0) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [momentMatrix_apply, ite_eq_right hji, zero_add, Real.norm_eq_abs]
    split_ifs <;> first | omega | simp
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
  gcongr
  · split_ifs with hi
    · rw [Finset.sum_eq_single_of_mem (⟨i + 1, by omega⟩ : Fin (n + 1))
        (Finset.mem_erase.mpr ⟨fun h => by simp [Fin.ext_iff] at h, Finset.mem_univ _⟩)
        (fun j _ hj => by rw [ite_eq_right]; intro h; exact hj (Fin.ext h))]
      simp
    · exact le_of_eq (Finset.sum_eq_zero fun j _ => by rw [ite_eq_right]; intro h; omega)
  · split_ifs with hi
    · rw [Finset.sum_eq_single_of_mem (⟨i - 1, by omega⟩ : Fin (n + 1))
        (Finset.mem_erase.mpr ⟨fun h => by simp [Fin.ext_iff] at h; omega, Finset.mem_univ _⟩)
        (fun j _ hj => by rw [ite_eq_right]; intro h; exact hj (Fin.ext (by simp; omega)))]
      rw [ite_eq_left (by simp; omega)]
    · exact le_of_eq (Finset.sum_eq_zero fun j _ => by rw [ite_eq_right]; intro h; omega)

/-- The off-diagonal coefficients of an interior row are nonnegative and sum to one. -/
theorem momentLam_add_momentMu (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i) {i : ℕ} (hi0 : i ≠ 0)
    (hin : i ≠ n) (hi : i ≤ n) :
    0 ≤ momentLam h lam0 i ∧ 0 ≤ momentMu n h mun i ∧
      momentLam h lam0 i + momentMu n h mun i = 1 := by
  have h1 : 0 < h i := hh i (by omega) hi
  have h2 : 0 < h (i + 1) := hh (i + 1) (by omega) (by omega)
  simp only [momentLam, momentMu, hi0, hin, ↓reduceIte]
  refine ⟨div_nonneg h2.le (by positivity), div_nonneg h1.le (by positivity), ?_⟩
  field_simp
  ring

/-- **Strict diagonal dominance of the moment matrix, for any closure with `|λ_0|, |μ_n| < 2`.**
Each interior row has off-diagonal sum `μ_i + λ_i = 1 < 2`, and the end rows have `|λ_0| < 2`,
`|μ_n| < 2`. -/
theorem isStrictDiagDominant_momentMatrix_of_abs_lt (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i)
    (hl : |lam0| < 2) (hm : |mun| < 2) : (momentMatrix n h lam0 mun).IsStrictDiagDominant := by
  intro i
  refine (sum_norm_momentMatrix_le i).trans_lt ?_
  have hii : ‖momentMatrix n h lam0 mun i i‖ = 2 := by simp [momentMatrix]
  rw [hii]
  by_cases hi0 : (i : ℕ) = 0
  · have hl0 : momentLam h lam0 i = lam0 := by simp [momentLam, hi0]
    rw [hl0, ite_eq_right (show ¬ 0 < (i : ℕ) by omega), add_zero]
    split_ifs
    · exact hl
    · norm_num
  · by_cases hin : (i : ℕ) = n
    · have : momentMu n h mun i = mun := by simp [momentMu, hin]
      rw [this, ite_eq_right (show ¬ (i : ℕ) < n by omega),
        ite_eq_left (show 0 < (i : ℕ) by omega), zero_add]
      exact hm
    · obtain ⟨h1, h2, h3⟩ := momentLam_add_momentMu (lam0 := lam0) (mun := mun) hh hi0 hin
        (Nat.lt_succ_iff.mp i.2)
      rw [ite_eq_left (show (i : ℕ) < n by omega), ite_eq_left (show 0 < (i : ℕ) by omega),
        abs_of_nonneg h1, abs_of_nonneg h2, h3]
      norm_num

/-- **The moment matrix is strictly diagonally dominant** for positive panel lengths and closure
parameters `0 ≤ λ_0, μ_n ≤ 1` ([quarteroni2000numerical] §8.6.1, after (8.48)). -/
theorem isStrictDiagDominant_momentMatrix (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i)
    (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1) :
    (momentMatrix n h lam0 mun).IsStrictDiagDominant :=
  isStrictDiagDominant_momentMatrix_of_abs_lt hh (by rw [abs_of_nonneg hl0]; linarith)
    (by rw [abs_of_nonneg hm0]; linarith)

/-- **The moment matrix is invertible** ([quarteroni2000numerical] §8.6.1): strict diagonal
dominance, `Matrix.IsStrictDiagDominant.isUnit`. -/
theorem isUnit_momentMatrix (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i)
    (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1) :
    IsUnit (momentMatrix n h lam0 mun) :=
  (isStrictDiagDominant_momentMatrix hh hl0 hl1 hm0 hm1).isUnit

/-- **The moment matrix does not shrink the sup norm**: `‖v‖_∞ ≤ ‖A v‖_∞`, i.e. `‖A⁻¹‖_∞ ≤ 1`. At an
index `i` where `|v_i|` is maximal, `|(A v)_i| ≥ 2 |v_i| - (λ_i + μ_i) |v_i| ≥ |v_i|`. -/
theorem norm_le_norm_momentMatrix_mulVec (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i)
    (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1) (v : Fin (n + 1) → ℝ) :
    ‖v‖ ≤ ‖(momentMatrix n h lam0 mun).mulVec v‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => |v j|) Finset.univ_nonempty
  have hnorm : ‖v‖ = |v i| := by
    refine le_antisymm (pi_norm_le_iff_of_nonneg (abs_nonneg _) |>.mpr fun j => ?_) ?_
    · rw [Real.norm_eq_abs]; exact hi j (Finset.mem_univ _)
    · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
  have hext : ∀ m, |extendFin v m| ≤ |v i| := by
    intro m
    rcases lt_or_ge m (n + 1) with hm | hm
    · rw [extendFin_of_lt v hm]; exact hi _ (Finset.mem_univ _)
    · rw [extendFin_of_le v hm, abs_zero]; exact abs_nonneg _
  rw [hnorm]
  refine le_trans ?_ (norm_le_pi_norm _ i)
  rw [Real.norm_eq_abs, momentMatrix_mulVec_apply]
  set R := momentLam h lam0 i * extendFin v (i + 1)
    + momentMu n h mun i * (if (i : ℕ) = 0 then 0 else extendFin v (i - 1)) with hR
  -- the off-diagonal contribution is at most `|v i|`
  have hRle : |R| ≤ |v i| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    by_cases hi0 : (i : ℕ) = 0
    · have hl : momentLam h lam0 i = lam0 := by simp [momentLam, hi0]
      rw [hl, ite_eq_left hi0, abs_zero, mul_zero, add_zero, abs_of_nonneg hl0]
      calc lam0 * |extendFin v (i + 1)| ≤ 1 * |v i| :=
            mul_le_mul hl1 (hext _) (abs_nonneg _) zero_le_one
        _ = |v i| := one_mul _
    · by_cases hin : (i : ℕ) = n
      · have : momentMu n h mun i = mun := by simp [momentMu, hin]
        rw [this, extendFin_of_le v (by omega), abs_zero, mul_zero, zero_add, ite_eq_right hi0,
          abs_of_nonneg hm0]
        calc mun * |extendFin v (i - 1)| ≤ 1 * |v i| :=
              mul_le_mul hm1 (hext _) (abs_nonneg _) zero_le_one
          _ = |v i| := one_mul _
      · obtain ⟨h1, h2, h3⟩ := momentLam_add_momentMu (lam0 := lam0) (mun := mun) hh hi0 hin
          (Nat.lt_succ_iff.mp i.2)
        rw [ite_eq_right hi0, abs_of_nonneg h1, abs_of_nonneg h2]
        calc _ ≤ momentLam h lam0 i * |v i| + momentMu n h mun i * |v i| :=
              add_le_add (mul_le_mul_of_nonneg_left (hext _) h1)
                (mul_le_mul_of_nonneg_left (hext _) h2)
          _ = |v i| := by rw [← add_mul, h3, one_mul]
  have h2 : |2 * v i| = 2 * |v i| := by rw [abs_mul, abs_two]
  have := abs_sub_abs_le_abs_sub (2 * v i) (-R)
  rw [abs_neg, sub_neg_eq_add, h2, hR, ← add_assoc] at this
  linarith

/-- **The inverse of the moment matrix has `‖·‖_∞`-operator norm at most one**: in the `L^∞`
operator norm (Mathlib's `Matrix.linfty_opNorm`, scoped in `Matrix.Norms.Operator`),
`‖(momentMatrix n h lam0 mun)⁻¹‖ ≤ 1`, by `norm_le_norm_momentMatrix_mulVec`. It is what the
error bounds for the interpolatory spline rest on. -/
theorem linfty_opNorm_inv_momentMatrix_le (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i)
    (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1) :
    ‖(momentMatrix n h lam0 mun)⁻¹‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_eq_opNorm]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  rw [one_mul]
  have hA := isUnit_momentMatrix hh hl0 hl1 hm0 hm1
  have hw : (momentMatrix n h lam0 mun).mulVec ((momentMatrix n h lam0 mun)⁻¹.mulVec w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
      Matrix.one_mulVec]
  change ‖(momentMatrix n h lam0 mun)⁻¹.mulVec w‖ ≤ ‖w‖
  calc ‖(momentMatrix n h lam0 mun)⁻¹.mulVec w‖
      ≤ ‖(momentMatrix n h lam0 mun).mulVec ((momentMatrix n h lam0 mun)⁻¹.mulVec w)‖ :=
        norm_le_norm_momentMatrix_mulVec hh hl0 hl1 hm0 hm1 _
    _ = ‖w‖ := by rw [hw]

end Dominance

/-! ### The glued cubic spline -/

/-- The length `h_i = x i - x (i - 1)` of the `i`-th panel. -/
def panelLength (x : ℕ → ℝ) (i : ℕ) : ℝ := x i - x (i - 1)

/-- The panel lengths of a partition are positive. -/
theorem IsPartition.panelLength_pos (hx : IsPartition a b n x) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    0 < panelLength x i :=
  sub_pos.mpr (hx.lt (by omega) hin)

/-- **The interior moment equation** at the node `x i` ([quarteroni2000numerical] (8.47)):
`μ_i M_{i-1} + 2 M_i + λ_i M_{i+1} = d_i` with `μ_i = h_i/(h_i + h_{i+1})`,
`λ_i = h_{i+1}/(h_i + h_{i+1})` and
`d_i = (6/(h_i + h_{i+1})) ((f_{i+1} - f_i)/h_{i+1} - (f_i - f_{i-1})/h_i)`. -/
def IsMomentEq (x f M : ℕ → ℝ) (i : ℕ) : Prop :=
  panelLength x i / (panelLength x i + panelLength x (i + 1)) * M (i - 1) + 2 * M i
    + panelLength x (i + 1) / (panelLength x i + panelLength x (i + 1)) * M (i + 1)
    = 6 / (panelLength x i + panelLength x (i + 1))
      * ((f (i + 1) - f i) / panelLength x (i + 1) - (f i - f (i - 1)) / panelLength x i)

/-- The interior moment equation is the equality of the one-sided slopes of the two panel cubics
meeting at `x i`. -/
theorem isMomentEq_iff {f M : ℕ → ℝ} {i : ℕ} (h1 : x (i - 1) < x i) (h2 : x i < x (i + 1)) :
    IsMomentEq x f M i ↔ panelCubicD1 x f M i (x i) = panelCubicD1 x f M (i + 1) (x i) := by
  rw [panelCubicD1_right h1, panelCubicD1_left h2, IsMomentEq, panelLength, panelLength,
    add_tsub_cancel_right]
  have ha : x i - x (i - 1) ≠ 0 := sub_ne_zero.mpr h1.ne'
  have hb : x (i + 1) - x i ≠ 0 := sub_ne_zero.mpr h2.ne'
  have hab : x i - x (i - 1) + (x (i + 1) - x i) ≠ 0 := by
    have := sub_pos.mpr h1; have := sub_pos.mpr h2; linarith
  have hc : 6 / (x i - x (i - 1) + (x (i + 1) - x i)) ≠ 0 := div_ne_zero (by norm_num) hab
  have key : (x i - x (i - 1)) / (x i - x (i - 1) + (x (i + 1) - x i)) * M (i - 1) + 2 * M i
      + (x (i + 1) - x i) / (x i - x (i - 1) + (x (i + 1) - x i)) * M (i + 1)
      - 6 / (x i - x (i - 1) + (x (i + 1) - x i))
        * ((f (i + 1) - f i) / (x (i + 1) - x i) - (f i - f (i - 1)) / (x i - x (i - 1)))
      = 6 / (x i - x (i - 1) + (x (i + 1) - x i)) * (((x i - x (i - 1)) * M (i - 1) / 6
        + (x i - x (i - 1)) * M i / 3 + (f i - f (i - 1)) / (x i - x (i - 1)))
        - (-((x (i + 1) - x i) * M i) / 3 - (x (i + 1) - x i) * M (i + 1) / 6
          + (f (i + 1) - f i) / (x (i + 1) - x i))) := by
    field_simp
    ring
  rw [← sub_eq_zero, key, mul_eq_zero, or_iff_right hc, sub_eq_zero]

/-- **The glued cubic spline**: the function equal to `panelCubic x f M i` on the panel
`[x (i - 1), x i]`, continued by the first and the last panel cubics outside `[x 0, x n]`. -/
noncomputable def cubicSplineFun (n : ℕ) (x f M : ℕ → ℝ) : ℝ → ℝ :=
  panelGlue n x (panelCubic x f M)

section CubicSplineFun

variable (hx : IsPartition a b n x) {f M : ℕ → ℝ}
include hx

/-- The panel cubics agree at the interior nodes. -/
theorem panelCubic_apply_node_succ {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    panelCubic x f M i (x i) = panelCubic x f M (i + 1) (x i) := by
  rw [panelCubic_right (hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin.le),
    panelCubic_left_succ (hx.step i hin)]

/-- The second derivatives of the panel cubics agree at the interior nodes. -/
theorem panelCubicD2_apply_node_succ {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    panelCubicD2 x f M i (x i) = panelCubicD2 x f M (i + 1) (x i) := by
  rw [panelCubicD2_right (hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin.le),
    panelCubicD2_left_succ (hx.step i hin)]

/-- On the `i`-th extended panel the glued cubic spline is the `i`-th panel cubic. -/
theorem cubicSplineFun_eq_of_mem {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) {t : ℝ}
    (ht : t ∈ extPanel n x i) : cubicSplineFun n x f M t = panelCubic x f M i t :=
  panelGlue_eq_of_mem hx (fun _ hi1 hin => panelCubic_apply_node_succ hx hi1 hin) hi1 hin ht

/-- On the `i`-th panel the glued cubic spline is the `i`-th panel cubic. -/
theorem cubicSplineFun_eqOn {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    EqOn (cubicSplineFun n x f M) (panelCubic x f M i) (Icc (x (i - 1)) (x i)) :=
  fun _ ht => cubicSplineFun_eq_of_mem hx hi1 hin (Icc_subset_extPanel i ht)

/-- **The glued cubic spline interpolates the data**: `s(x_i) = f_i` for `i ≤ n`. -/
theorem cubicSplineFun_apply_node (hn : 1 ≤ n) {i : ℕ} (hi : i ≤ n) :
    cubicSplineFun n x f M (x i) = f i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [cubicSplineFun_eq_of_mem hx le_rfl hn ⟨fun h => absurd h (lt_irrefl _),
      fun _ => (hx.step 0 hn).le⟩]
    exact panelCubic_left_succ (hx.step 0 hn)
  · rw [cubicSplineFun_eq_of_mem hx hi0 hi
      (Icc_subset_extPanel i ⟨(hx.mono (by omega) hi), le_rfl⟩)]
    exact panelCubic_right (hx.lt (by omega) hi)

variable (hn : 1 ≤ n) (hM : ∀ i, 1 ≤ i → i < n → IsMomentEq x f M i)
include hM

/-- The first derivatives of the panel cubics agree at the interior nodes when the moment
equations hold. -/
theorem panelCubicD1_apply_node_succ {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    panelCubicD1 x f M i (x i) = panelCubicD1 x f M (i + 1) (x i) :=
  (isMomentEq_iff (hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin.le) (hx.step i hin)).mp
    (hM i hi1 hin)

include hn

/-- **The glued cubic spline is differentiable**, with derivative the glued first derivatives of
the panel cubics, when the moment equations hold. -/
theorem hasDerivAt_cubicSplineFun (t : ℝ) :
    HasDerivAt (cubicSplineFun n x f M) (panelGlue n x (panelCubicD1 x f M) t) t :=
  hasDerivAt_panelGlue hx hn (fun _ hi1 hin => panelCubic_apply_node_succ hx hi1 hin)
    (fun _ hi1 hin => panelCubicD1_apply_node_succ hx hM hi1 hin)
    (fun i _ _ t _ => hasDerivAt_panelCubic x f M i t) t

/-- The glued first derivative is differentiable, with derivative the glued second derivatives. -/
theorem hasDerivAt_cubicSplineFun_deriv (t : ℝ) :
    HasDerivAt (panelGlue n x (panelCubicD1 x f M)) (panelGlue n x (panelCubicD2 x f M) t) t :=
  hasDerivAt_panelGlue hx hn (fun _ hi1 hin => panelCubicD1_apply_node_succ hx hM hi1 hin)
    (fun _ hi1 hin => panelCubicD2_apply_node_succ hx hi1 hin)
    (fun i _ _ t _ => hasDerivAt_panelCubicD1 x f M i t) t

omit hM in
/-- The glued second derivative is continuous. -/
theorem continuous_cubicSplineFun_deriv2 :
    Continuous (panelGlue n x (panelCubicD2 x f M)) :=
  continuous_panelGlue hx hn (fun _ hi1 hin => panelCubicD2_apply_node_succ hx hi1 hin)
    fun i _ _ => continuousOn_of_forall_continuousAt fun t _ =>
      (hasDerivAt_panelCubicD2 x f M i t).continuousAt

/-- **The M-continuity system is sufficient** ([quarteroni2000numerical] §8.6.1): when the
interior moment equations hold, the glued cubic spline is `C²` on all of `ℝ`. -/
theorem contDiff_cubicSplineFun : ContDiff ℝ 2 (cubicSplineFun n x f M) :=
  contDiff_two_of_hasDerivAt (hasDerivAt_cubicSplineFun hx hn hM)
    (hasDerivAt_cubicSplineFun_deriv hx hn hM) (continuous_cubicSplineFun_deriv2 hx hn)

/-- **The M-continuity system is sufficient**: the glued cubic spline is `C²` on `[a, b]`. -/
theorem contDiffOn_cubicSplineFun : ContDiffOn ℝ 2 (cubicSplineFun n x f M) (Icc a b) :=
  (contDiff_cubicSplineFun hx hn hM).contDiffOn

/-- The derivative of the glued cubic spline is the glued first derivative. -/
theorem deriv_cubicSplineFun :
    deriv (cubicSplineFun n x f M) = panelGlue n x (panelCubicD1 x f M) :=
  funext fun t => (hasDerivAt_cubicSplineFun hx hn hM t).deriv

/-- The second derivative of the glued cubic spline is the glued second derivative. -/
theorem iteratedDeriv_two_cubicSplineFun :
    iteratedDeriv 2 (cubicSplineFun n x f M) = panelGlue n x (panelCubicD2 x f M) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_cubicSplineFun hx hn hM]
  exact funext fun t => (hasDerivAt_cubicSplineFun_deriv hx hn hM t).deriv

/-- **The moments of the glued cubic spline are the `M i`**: `s''(x_i) = M_i` for `i ≤ n`. -/
theorem iteratedDeriv_two_cubicSplineFun_node {i : ℕ} (hi : i ≤ n) :
    iteratedDeriv 2 (cubicSplineFun n x f M) (x i) = M i := by
  rw [iteratedDeriv_two_cubicSplineFun hx hn hM]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [panelGlue_eq_of_mem hx (fun _ hi1 hin => panelCubicD2_apply_node_succ hx hi1 hin) le_rfl hn
      ⟨fun h => absurd h (lt_irrefl _), fun _ => (hx.step 0 hn).le⟩]
    exact panelCubicD2_left_succ (hx.step 0 hn)
  · rw [panelGlue_eq_of_mem hx (fun _ hi1 hin => panelCubicD2_apply_node_succ hx hi1 hin) hi0 hi
      (Icc_subset_extPanel i ⟨(hx.mono (by omega) hi), le_rfl⟩)]
    exact panelCubicD2_right (hx.lt (by omega) hi)

/-- The derivative of the glued cubic spline at the left endpoint, in terms of the moments:
`s'(a) = -h_1 M_0/3 - h_1 M_1/6 + (f_1 - f_0)/h_1`. -/
theorem deriv_cubicSplineFun_left :
    deriv (cubicSplineFun n x f M) a = -((x 1 - x 0) * M 0) / 3 - (x 1 - x 0) * M 1 / 6
      + (f 1 - f 0) / (x 1 - x 0) := by
  rw [deriv_cubicSplineFun hx hn hM, ← hx.first,
    panelGlue_eq_of_mem hx (fun _ hi1 hin => panelCubicD1_apply_node_succ hx hM hi1 hin) le_rfl hn
      ⟨fun h => absurd h (lt_irrefl _), fun _ => (hx.step 0 hn).le⟩]
  exact panelCubicD1_left (i := 0) (hx.step 0 hn)

/-- The derivative of the glued cubic spline at the right endpoint, in terms of the moments:
`s'(b) = h_n M_{n-1}/6 + h_n M_n/3 + (f_n - f_{n-1})/h_n`. -/
theorem deriv_cubicSplineFun_right :
    deriv (cubicSplineFun n x f M) b = (x n - x (n - 1)) * M (n - 1) / 6
      + (x n - x (n - 1)) * M n / 3 + (f n - f (n - 1)) / (x n - x (n - 1)) := by
  rw [deriv_cubicSplineFun hx hn hM, ← hx.last,
    panelGlue_eq_of_mem hx (fun _ hi1 hin => panelCubicD1_apply_node_succ hx hM hi1 hin) hn le_rfl
      ⟨fun _ => hx.mono (Nat.sub_le n 1) le_rfl, fun h => absurd h (lt_irrefl _)⟩]
  exact panelCubicD1_right (hx.lt (by omega) le_rfl)

/-- **The glued cubic spline is a cubic spline**: its restriction to `[a, b]` lies in
`splineSpace a b n x 3 2`. -/
theorem cubicSplineFun_mem_splineSpace :
    (ContinuousMap.mk _ (contDiff_cubicSplineFun hx hn hM).continuous).restrict (Icc a b) ∈
      splineSpace a b n x 3 2 := by
  refine ⟨cubicSplineFun n x f M, contDiffOn_cubicSplineFun hx hn hM, fun t => rfl,
    fun j hj => ⟨panelCubicPoly x f M (j + 1), degree_panelCubicPoly_le _ _ _ _, fun t ht => ?_⟩⟩
  exact cubicSplineFun_eq_of_mem hx (i := j + 1) (by omega) hj
    (Icc_subset_extPanel (j + 1) (by simpa using ht))

end CubicSplineFun

/-- Two derivatives within a nondegenerate closed interval at one of its points agree: the
uniqueness of derivatives within `Icc u v`. -/
theorem eq_of_hasDerivWithinAt_Icc {u v t d d' : ℝ} {g : ℝ → ℝ} (huv : u < v) (ht : t ∈ Icc u v)
    (h : HasDerivWithinAt g d (Icc u v) t) (h' : HasDerivWithinAt g d' (Icc u v) t) : d = d' :=
  (uniqueDiffOn_Icc huv t ht).eq_deriv _ h h'

/-- **The M-continuity system is necessary** ([quarteroni2000numerical] (8.47)): a `C²` function
on `[a, b]` which is the panel cubic `panelCubic x f M i` on every panel has moments satisfying the
interior moment equations, because its one-sided slopes at every interior node agree. -/
theorem moment_eq_of_contDiffOn (hx : IsPartition a b n x) {s : ℝ → ℝ}
    (hs : ContDiffOn ℝ 2 s (Icc a b)) {f M : ℕ → ℝ}
    (hpanel : ∀ i, 1 ≤ i → i ≤ n → EqOn s (panelCubic x f M i) (Icc (x (i - 1)) (x i)))
    {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) : IsMomentEq x f M i := by
  have h1 : x (i - 1) < x i := hx.lt (by omega) hin.le
  have h2 : x i < x (i + 1) := hx.step i hin
  have hmem : Icc a b ∈ 𝓝 (x i) :=
    Icc_mem_nhds (hx.first ▸ hx.lt (by omega) hin.le) (hx.last ▸ hx.lt hin le_rfl)
  have hd : HasDerivAt s (deriv s (x i)) (x i) :=
    (((hs.differentiableOn (by norm_num)) (x i) (mem_of_mem_nhds hmem)).differentiableAt
      hmem).hasDerivAt
  rw [isMomentEq_iff h1 h2]
  have hl : deriv s (x i) = panelCubicD1 x f M i (x i) :=
    eq_of_hasDerivWithinAt_Icc h1 ⟨h1.le, le_rfl⟩
      (hd.hasDerivWithinAt.congr (fun y hy => (hpanel i hi1 hin.le hy).symm)
        (hpanel i hi1 hin.le ⟨h1.le, le_rfl⟩).symm)
      (hasDerivAt_panelCubic x f M i (x i)).hasDerivWithinAt
  have hr : deriv s (x i) = panelCubicD1 x f M (i + 1) (x i) :=
    eq_of_hasDerivWithinAt_Icc (by simpa using h2) (by simp [h2.le])
      (hd.hasDerivWithinAt.congr (fun y hy => (hpanel (i + 1) (by omega) hin hy).symm)
        (hpanel (i + 1) (by omega) hin (by simp [h2.le])).symm)
      (hasDerivAt_panelCubic x f M (i + 1) (x i)).hasDerivWithinAt
  rw [← hl, ← hr]

/-! ### Cubic splines and their moments -/

/-- **A cubic spline on `[a, b]`**: a function of class `C²` on `Icc a b` agreeing with a
polynomial of degree at most `3` on every panel `[x (i - 1), x i]`, `1 ≤ i ≤ n`. -/
structure IsCubicSpline (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (s : ℝ → ℝ) : Prop where
  /-- The spline is `C²` on `[a, b]`. -/
  contDiffOn : ContDiffOn ℝ 2 s (Icc a b)
  /-- The spline is a cubic on every panel. -/
  piecewise : ∀ i, 1 ≤ i → i ≤ n → ∃ p : ℝ[X], p.degree ≤ 3 ∧ EqOn s p.eval (Icc (x (i - 1)) (x i))

/-- **An interpolatory cubic spline**: a cubic spline on `[a, b]` taking the values `f i` at the
nodes `x i`, `i ≤ n` ([quarteroni2000numerical] §8.6.1). -/
structure IsCubicInterp (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (f : ℕ → ℝ) (s : ℝ → ℝ) : Prop
    extends IsCubicSpline a b n x s where
  /-- The spline interpolates the data. -/
  interp : ∀ i ≤ n, s (x i) = f i

/-- **The moments** `M_i = s''(x_i)` of a function on `[a, b]`, as the second derivative within
`Icc a b`. -/
noncomputable def moment (a b : ℝ) (x : ℕ → ℝ) (s : ℝ → ℝ) (i : ℕ) : ℝ :=
  iteratedDerivWithin 2 s (Icc a b) (x i)

/-- For a function `C²` on all of `ℝ` the moments are the ordinary second derivatives. -/
theorem moment_eq_iteratedDeriv (hab : a < b) {s : ℝ → ℝ} (hs : ContDiff ℝ 2 s) {i : ℕ}
    (hi : x i ∈ Icc a b) : moment a b x s i = iteratedDeriv 2 s (x i) :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hs.contDiffAt hi

/-- **A derivative within `[a, b]` is read off a local polynomial description**: if `s` is
differentiable within `Icc a b` at `t` and agrees with `g` on a nondegenerate `Icc u v ∋ t`
inside `Icc a b`, then `derivWithin s (Icc a b) t = g' t`. -/
theorem derivWithin_eq_of_eqOn_Icc {s g : ℝ → ℝ} {u v t d : ℝ}
    (hs : DifferentiableWithinAt ℝ s (Icc a b) t) (huv : u < v) (hsub : Icc u v ⊆ Icc a b)
    (ht : t ∈ Icc u v) (heq : EqOn s g (Icc u v)) (hg : HasDerivAt g d t) :
    derivWithin s (Icc a b) t = d :=
  eq_of_hasDerivWithinAt_Icc huv ht
    ((hs.hasDerivWithinAt.mono hsub).congr (fun _ hy => (heq hy).symm) (heq ht).symm)
    hg.hasDerivWithinAt

/-- The first and second derivatives within `[a, b]` of a `C²` function agreeing with a polynomial
on a panel are the derivatives of the polynomial, on the closed panel. -/
theorem derivWithin_eq_of_eqOn_Icc_of_contDiffOn {s : ℝ → ℝ} (hs : ContDiffOn ℝ 2 s (Icc a b))
    {u v : ℝ} (huv : u < v) (hsub : Icc u v ⊆ Icc a b) {p : ℝ[X]} (heq : EqOn s p.eval (Icc u v))
    {t : ℝ} (ht : t ∈ Icc u v) :
    derivWithin s (Icc a b) t = (derivative p).eval t ∧
      iteratedDerivWithin 2 s (Icc a b) t = (derivative (derivative p)).eval t := by
  have hab : a < b := by
    have := (hsub ⟨le_rfl, huv.le⟩).1; have := (hsub ⟨huv.le, le_rfl⟩).2; linarith
  have hd1 : ∀ t ∈ Icc u v, derivWithin s (Icc a b) t = (derivative p).eval t := fun t ht =>
    derivWithin_eq_of_eqOn_Icc ((hs.differentiableOn (by norm_num)) t (hsub ht)) huv hsub ht heq
      (p.hasDerivAt t)
  refine ⟨hd1 t ht, ?_⟩
  have hs1 : ContDiffOn ℝ 1 (derivWithin s (Icc a b)) (Icc a b) := by
    have := hs
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)] at this
    exact this.2.2
  rw [iteratedDerivWithin_succ, iteratedDerivWithin_one]
  exact derivWithin_eq_of_eqOn_Icc ((hs1.differentiableOn (by norm_num)) t (hsub ht)) huv hsub ht
    (fun _ hy => hd1 _ hy) ((derivative p).hasDerivAt t)

/-- **A cubic is determined by its values and second derivatives at two distinct points.** -/
theorem eq_of_degree_le_three {p q : ℝ[X]} (hp : p.degree ≤ 3) (hq : q.degree ≤ 3) {u v : ℝ}
    (huv : u ≠ v) (h0 : p.eval u = q.eval u) (h1 : p.eval v = q.eval v)
    (h2 : (derivative (derivative p)).eval u = (derivative (derivative q)).eval u)
    (h3 : (derivative (derivative p)).eval v = (derivative (derivative q)).eval v) : p = q := by
  classical
  rw [← sub_eq_zero]
  set r := p - q with hr
  have hrdeg : r.natDegree ≤ 3 :=
    natDegree_le_of_degree_le ((degree_sub_le _ _).trans (max_le hp hq))
  have hcard : ({u, v} : Finset ℝ).card = 2 := Finset.card_pair huv
  -- the second derivative of `r` is affine with two zeros, hence zero
  have hr2 : derivative (derivative r) = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ {u, v} ?_ ?_
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · simp [hr, derivative_sub, eval_sub, h2]
      · simp [hr, derivative_sub, eval_sub, h3]
    · rw [hcard]
      have := natDegree_derivative_le (derivative r)
      have := natDegree_derivative_le r
      omega
  -- hence `r` is affine with two zeros, hence zero
  have hr1 : r.natDegree ≤ 1 := by
    have := derivative_eq_zero.mp hr2
    rw [natDegree_derivative] at this
    omega
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ {u, v} ?_ (by rw [hcard]; omega)
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · simp [hr, eval_sub, h0]
  · simp [hr, eval_sub, h1]

/-- The panel cubic depends only on the data and moments at the two ends of its panel. -/
theorem panelCubicPoly_congr {f g M N : ℕ → ℝ} {i : ℕ} (hf0 : f (i - 1) = g (i - 1))
    (hf1 : f i = g i) (hM0 : M (i - 1) = N (i - 1)) (hM1 : M i = N i) :
    panelCubicPoly x f M i = panelCubicPoly x g N i := by
  simp only [panelCubicPoly, hf0, hf1, hM0, hM1]

/-- **A cubic spline is the panel cubic of its values and moments on every panel**
([quarteroni2000numerical] (8.46) integrated): on `[x (i - 1), x i]` it agrees with
`panelCubic x (fun i => s (x i)) (moment a b x s) i`. -/
theorem IsCubicSpline.eqOn_panelCubic (hx : IsPartition a b n x) {s : ℝ → ℝ}
    (hs : IsCubicSpline a b n x s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    EqOn s (panelCubic x (fun i => s (x i)) (moment a b x s) i) (Icc (x (i - 1)) (x i)) := by
  obtain ⟨p, hpd, hpe⟩ := hs.piecewise i hi1 hin
  have hlt : x (i - 1) < x i := hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have hpq : p = panelCubicPoly x (fun i => s (x i)) (moment a b x s) i := by
    refine eq_of_degree_le_three hpd (degree_panelCubicPoly_le _ _ _ _) hlt.ne ?_ ?_ ?_ ?_
    · exact (hpe ⟨le_rfl, hlt.le⟩).symm.trans
        (panelCubic_left (f := fun i => s (x i)) (M := moment a b x s) hlt).symm
    · exact (hpe ⟨hlt.le, le_rfl⟩).symm.trans
        (panelCubic_right (f := fun i => s (x i)) (M := moment a b x s) hlt).symm
    · exact (derivWithin_eq_of_eqOn_Icc_of_contDiffOn hs.contDiffOn hlt hsub hpe
        ⟨le_rfl, hlt.le⟩).2.symm.trans
        (panelCubicD2_left (f := fun i => s (x i)) (M := moment a b x s) hlt).symm
    · exact (derivWithin_eq_of_eqOn_Icc_of_contDiffOn hs.contDiffOn hlt hsub hpe
        ⟨hlt.le, le_rfl⟩).2.symm.trans
        (panelCubicD2_right (f := fun i => s (x i)) (M := moment a b x s) hlt).symm
  intro t ht
  rw [hpe ht, hpq]
  rfl

/-- **An interpolatory cubic spline is the panel cubic of its data and moments on every panel.** -/
theorem IsCubicInterp.eqOn_panelCubic (hx : IsPartition a b n x) {f : ℕ → ℝ} {s : ℝ → ℝ}
    (hs : IsCubicInterp a b n x f s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    EqOn s (panelCubic x f (moment a b x s) i) (Icc (x (i - 1)) (x i)) := by
  refine (hs.toIsCubicSpline.eqOn_panelCubic hx hi1 hin).trans fun t _ => ?_
  simp only [panelCubic]
  rw [panelCubicPoly_congr (hs.interp _ (by omega)) (hs.interp _ hin) rfl rfl]

/-- **An interpolatory cubic spline is the glued cubic spline of its data and moments** on
`[a, b]`. -/
theorem IsCubicInterp.eqOn_cubicSplineFun (hx : IsPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ}
    {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s) :
    EqOn s (cubicSplineFun n x f (moment a b x s)) (Icc a b) := by
  intro t ht
  obtain ⟨i, hi1, hin, hti, -⟩ := hx.exists_mem_panel hn ht
  rw [hs.eqOn_panelCubic hx hi1 hin hti, cubicSplineFun_eqOn hx hi1 hin hti]

/-- **The moments of an interpolatory cubic spline satisfy the M-continuity system**
([quarteroni2000numerical] (8.47)) at every interior node. -/
theorem IsCubicInterp.isMomentEq (hx : IsPartition a b n x) {f : ℕ → ℝ} {s : ℝ → ℝ}
    (hs : IsCubicInterp a b n x f s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    IsMomentEq x f (moment a b x s) i :=
  moment_eq_of_contDiffOn hx hs.contDiffOn (fun _ hi1 hin => hs.eqOn_panelCubic hx hi1 hin) hi1 hin

/-- Two glued cubic splines with the same data and the same moments at the nodes agree on
`[a, b]`. -/
theorem cubicSplineFun_eqOn_of_moment_eq (hx : IsPartition a b n x) (hn : 1 ≤ n) {f M N : ℕ → ℝ}
    (hMN : ∀ i ≤ n, M i = N i) :
    EqOn (cubicSplineFun n x f M) (cubicSplineFun n x f N) (Icc a b) := by
  intro t ht
  obtain ⟨i, hi1, hin, hti, -⟩ := hx.exists_mem_panel hn ht
  rw [cubicSplineFun_eqOn hx hi1 hin hti, cubicSplineFun_eqOn hx hi1 hin hti]
  simp only [panelCubic]
  rw [panelCubicPoly_congr rfl rfl (hMN _ (by omega)) (hMN _ hin)]

/-! ### The interpolatory cubic spline with a closure of type (8.48) -/

/-- **A closure of type (8.48)** on the moments of `s`: `2 M_0 + λ_0 M_1 = d_0` and
`μ_n M_{n-1} + 2 M_n = d_n`. -/
def HasClosure (a b : ℝ) (n : ℕ) (x : ℕ → ℝ) (lam0 mun d0 dn : ℝ) (s : ℝ → ℝ) : Prop :=
  2 * moment a b x s 0 + lam0 * moment a b x s 1 = d0 ∧
    mun * moment a b x s (n - 1) + 2 * moment a b x s n = dn

section Closure

variable (hx : IsPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ} {lam0 mun d0 dn : ℝ}
include hx hn

/-- **The full moment system is the interior moment equations plus the closure rows**: for a
vector `M` of moments, `A M = d` with `A = momentMatrix n h lam0 mun` and `d = momentRhs …` holds
exactly when the interior equations (8.47) and the two closure equations hold. -/
theorem momentMatrix_mulVec_eq_iff (M : Fin (n + 1) → ℝ) :
    (momentMatrix n (panelLength x) lam0 mun).mulVec M = momentRhs n (panelLength x) f d0 dn ↔
      (∀ i, 1 ≤ i → i < n → IsMomentEq x f (extendFin M) i) ∧
        2 * extendFin M 0 + lam0 * extendFin M 1 = d0 ∧
        mun * extendFin M (n - 1) + 2 * extendFin M n = dn := by
  rw [funext_iff]
  simp only [momentMatrix_mulVec_apply, momentRhs]
  constructor
  · intro H
    refine ⟨fun i hi1 hin => ?_, ?_, ?_⟩
    · have := H ⟨i, by omega⟩
      simp only [ite_eq_right (show i ≠ 0 by omega), ite_eq_right (show i ≠ n by omega),
        momentLam, momentMu] at this
      rw [IsMomentEq, extendFin_of_lt M (i := i) (by omega)]
      linear_combination this
    · have := H ⟨0, by omega⟩
      simp only [↓reduceIte, momentLam, zero_add, mul_zero, add_zero] at this
      rw [extendFin_of_lt M (i := 0) (by omega)]
      exact this
    · have := H ⟨n, by omega⟩
      simp only [ite_eq_right (show n ≠ 0 by omega), ↓reduceIte, momentMu,
        extendFin_of_le M (le_refl (n + 1)), mul_zero, add_zero] at this
      rw [extendFin_of_lt M (i := n) (by omega)]
      linear_combination this
  · rintro ⟨hint, h0, hN⟩ ⟨i, hi⟩
    by_cases hi0 : i = 0
    · subst hi0
      simp only [↓reduceIte, momentLam, zero_add, mul_zero, add_zero]
      rw [extendFin_of_lt M (i := 0) (by omega)] at h0
      exact h0
    · by_cases hin : i = n
      · subst hin
        simp only [ite_eq_right hi0, ↓reduceIte, momentMu, extendFin_of_le M (le_refl (i + 1)),
          mul_zero, add_zero]
        rw [extendFin_of_lt M (i := i) (by omega)] at hN
        linear_combination hN
      · have := hint i (by omega) (by omega)
        rw [IsMomentEq, extendFin_of_lt M (i := i) (by omega)] at this
        simp only [ite_eq_right hi0, ite_eq_right hin, momentLam, momentMu]
        linear_combination this

/-- The glued cubic spline of the data and of moments solving the moment system is an
interpolatory cubic spline with the corresponding closure. -/
theorem isCubicInterp_cubicSplineFun_of_mulVec_eq {M : Fin (n + 1) → ℝ}
    (hM : (momentMatrix n (panelLength x) lam0 mun).mulVec M
      = momentRhs n (panelLength x) f d0 dn) :
    IsCubicInterp a b n x f (cubicSplineFun n x f (extendFin M)) ∧
      HasClosure a b n x lam0 mun d0 dn (cubicSplineFun n x f (extendFin M)) := by
  obtain ⟨hint, h0, hN⟩ := (momentMatrix_mulVec_eq_iff hx hn M).mp hM
  have hab : a < b := hx.lt_of_pos hn
  have hmom : ∀ i ≤ n, moment a b x (cubicSplineFun n x f (extendFin M)) i = extendFin M i :=
    fun i hi => by
      rw [moment_eq_iteratedDeriv hab (contDiff_cubicSplineFun hx hn hint)
        ⟨hx.left_le hi, hx.le_right hi⟩, iteratedDeriv_two_cubicSplineFun_node hx hn hint hi]
  refine ⟨⟨⟨contDiffOn_cubicSplineFun hx hn hint, fun i hi1 hin =>
    ⟨panelCubicPoly x f (extendFin M) i, degree_panelCubicPoly_le _ _ _ _,
      cubicSplineFun_eqOn hx hi1 hin⟩⟩, fun i hi => cubicSplineFun_apply_node hx hn hi⟩, ?_, ?_⟩
  · rw [hmom 0 (by omega), hmom 1 hn]
    exact h0
  · rw [hmom (n - 1) (by omega), hmom n le_rfl]
    exact hN

/-- The moments of an interpolatory cubic spline with a closure of type (8.48) solve the moment
system. -/
theorem IsCubicInterp.momentMatrix_mulVec_eq {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s)
    (hc : HasClosure a b n x lam0 mun d0 dn s) :
    (momentMatrix n (panelLength x) lam0 mun).mulVec
      (fun i : Fin (n + 1) => moment a b x s (i : ℕ)) = momentRhs n (panelLength x) f d0 dn := by
  refine (momentMatrix_mulVec_eq_iff hx hn _).mpr ⟨fun i hi1 hin => ?_, ?_, ?_⟩
  · have := hs.isMomentEq hx hi1 hin
    rwa [IsMomentEq, ← extendFin_of_lt (fun i : Fin (n + 1) => moment a b x s (i : ℕ)) (i := i - 1)
      (by omega), ← extendFin_of_lt (fun i : Fin (n + 1) => moment a b x s (i : ℕ)) (i := i)
      (by omega), ← extendFin_of_lt (fun i : Fin (n + 1) => moment a b x s (i : ℕ)) (i := i + 1)
      (by omega)] at this
  · rw [extendFin_of_lt _ (by omega), extendFin_of_lt _ (by omega)]
    exact hc.1
  · rw [extendFin_of_lt _ (by omega), extendFin_of_lt _ (by omega)]
    exact hc.2

variable (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1)
include hl0 hl1 hm0 hm1

/-- **Uniqueness of the interpolatory cubic spline with a closure of type (8.48)**: two
interpolatory cubic splines of the same data satisfying the same closure agree on `[a, b]`, their
moments solving the same nonsingular system. -/
theorem IsCubicInterp.eqOn_of_hasClosure {s₁ s₂ : ℝ → ℝ} (h₁ : IsCubicInterp a b n x f s₁)
    (hc₁ : HasClosure a b n x lam0 mun d0 dn s₁) (h₂ : IsCubicInterp a b n x f s₂)
    (hc₂ : HasClosure a b n x lam0 mun d0 dn s₂) : EqOn s₁ s₂ (Icc a b) := by
  have hA := isUnit_momentMatrix (h := panelLength x) (n := n)
    (fun i hi1 hin => hx.panelLength_pos hi1 hin) hl0 hl1 hm0 hm1
  have hM : (fun i : Fin (n + 1) => moment a b x s₁ (i : ℕ)) =
      fun i : Fin (n + 1) => moment a b x s₂ (i : ℕ) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hA
      ((h₁.momentMatrix_mulVec_eq hx hn hc₁).trans (h₂.momentMatrix_mulVec_eq hx hn hc₂).symm)
  refine (h₁.eqOn_cubicSplineFun hx hn).trans
    ((cubicSplineFun_eqOn_of_moment_eq hx hn fun i hi => ?_).trans
      (h₂.eqOn_cubicSplineFun hx hn).symm)
  exact congrFun hM (⟨i, by omega⟩ : Fin (n + 1))

/-- **Existence and uniqueness of the interpolatory cubic spline with a closure of type (8.48)**
([quarteroni2000numerical] §8.6.1): for `0 ≤ λ_0, μ_n ≤ 1` and any `d_0, d_n` there is an
interpolatory cubic spline of the data `f` with `2 M_0 + λ_0 M_1 = d_0`,
`μ_n M_{n-1} + 2 M_n = d_n`, and any two such agree on `[a, b]`. -/
theorem existsUnique_isCubicInterp_of_closure (f : ℕ → ℝ) (d0 dn : ℝ) :
    (∃ s, IsCubicInterp a b n x f s ∧ HasClosure a b n x lam0 mun d0 dn s) ∧
      ∀ s₁ s₂, IsCubicInterp a b n x f s₁ → HasClosure a b n x lam0 mun d0 dn s₁ →
        IsCubicInterp a b n x f s₂ → HasClosure a b n x lam0 mun d0 dn s₂ →
        EqOn s₁ s₂ (Icc a b) := by
  refine ⟨?_, fun s₁ s₂ h₁ hc₁ h₂ hc₂ => h₁.eqOn_of_hasClosure hx hn hl0 hl1 hm0 hm1 hc₁ h₂ hc₂⟩
  have hA := isUnit_momentMatrix (h := panelLength x) (n := n)
    (fun i hi1 hin => hx.panelLength_pos hi1 hin) hl0 hl1 hm0 hm1
  refine ⟨_, isCubicInterp_cubicSplineFun_of_mulVec_eq hx hn
    (M := (momentMatrix n (panelLength x) lam0 mun)⁻¹.mulVec (momentRhs n (panelLength x) f d0 dn))
    ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
    Matrix.one_mulVec]

end Closure

/-! ### The interpolatory cubic spline as an explicit function -/

/-- The moment vector of the interpolatory cubic spline with closure `(λ_0, μ_n, d_0, d_n)`, the
solution of the moment system (8.48). -/
noncomputable def momentVec (n : ℕ) (x f : ℕ → ℝ) (lam0 mun d0 dn : ℝ) : ℕ → ℝ :=
  extendFin ((momentMatrix n (panelLength x) lam0 mun)⁻¹.mulVec
    (momentRhs n (panelLength x) f d0 dn))

/-- **The interpolatory cubic spline with a closure of type (8.48)**, as an explicit function
`ℝ → ℝ`: the glued cubic spline of the data and of the moments solving (8.48). -/
noncomputable def cubicInterp (n : ℕ) (x f : ℕ → ℝ) (lam0 mun d0 dn : ℝ) : ℝ → ℝ :=
  cubicSplineFun n x f (momentVec n x f lam0 mun d0 dn)

/-- **The natural cubic spline** interpolating the data: the closure `s''(a) = s''(b) = 0`,
[quarteroni2000numerical] (8.45) with `k = 3`. -/
noncomputable def naturalInterp (n : ℕ) (x f : ℕ → ℝ) : ℝ → ℝ :=
  cubicInterp n x f 0 0 0 0

/-- **The clamped (constrained) cubic spline** interpolating the data with prescribed end slopes
`s'(a) = f'0`, `s'(b) = f'n` ([quarteroni2000numerical] Exercise 8.11): the closure
`λ_0 = μ_n = 1`, `d_0 = (6/h_1)((f_1 - f_0)/h_1 - f'_0)`,
`d_n = (6/h_n)(f'_n - (f_n - f_{n-1})/h_n)`. -/
noncomputable def clampedInterp (n : ℕ) (x f : ℕ → ℝ) (f'0 f'n : ℝ) : ℝ → ℝ :=
  cubicInterp n x f 1 1 (6 / (x 1 - x 0) * ((f 1 - f 0) / (x 1 - x 0) - f'0))
    (6 / (x n - x (n - 1)) * (f'n - (f n - f (n - 1)) / (x n - x (n - 1))))

section CubicInterp

variable (hx : IsPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ} {lam0 mun d0 dn : ℝ}
  (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun) (hm1 : mun ≤ 1)
include hx hl0 hl1 hm0 hm1

/-- The moment vector solves the moment system. -/
theorem momentMatrix_mulVec_momentVec (f : ℕ → ℝ) (d0 dn : ℝ) :
    (momentMatrix n (panelLength x) lam0 mun).mulVec
      ((momentMatrix n (panelLength x) lam0 mun)⁻¹.mulVec (momentRhs n (panelLength x) f d0 dn))
      = momentRhs n (panelLength x) f d0 dn := by
  have hA := isUnit_momentMatrix (h := panelLength x) (n := n)
    (fun i hi1 hin => hx.panelLength_pos hi1 hin) hl0 hl1 hm0 hm1
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
    Matrix.one_mulVec]

include hn

/-- **The interpolatory cubic spline is an interpolatory cubic spline with its closure.** -/
theorem isCubicInterp_cubicInterp :
    IsCubicInterp a b n x f (cubicInterp n x f lam0 mun d0 dn) ∧
      HasClosure a b n x lam0 mun d0 dn (cubicInterp n x f lam0 mun d0 dn) :=
  isCubicInterp_cubicSplineFun_of_mulVec_eq hx hn
    (momentMatrix_mulVec_momentVec hx hl0 hl1 hm0 hm1 f d0 dn)

/-- The moment vector satisfies the interior moment equations. -/
theorem isMomentEq_momentVec {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    IsMomentEq x f (momentVec n x f lam0 mun d0 dn) i :=
  ((momentMatrix_mulVec_eq_iff hx hn _).mp
    (momentMatrix_mulVec_momentVec hx hl0 hl1 hm0 hm1 f d0 dn)).1 i hi1 hin

/-- **The interpolatory cubic spline is `C²` on `ℝ`.** -/
theorem contDiff_cubicInterp : ContDiff ℝ 2 (cubicInterp n x f lam0 mun d0 dn) :=
  contDiff_cubicSplineFun hx hn fun _ hi1 hin => isMomentEq_momentVec hx hn hl0 hl1 hm0 hm1 hi1 hin

omit hl0 hl1 hm0 hm1 in
/-- **The interpolatory cubic spline interpolates the data.** -/
theorem cubicInterp_apply_node {i : ℕ} (hi : i ≤ n) :
    cubicInterp n x f lam0 mun d0 dn (x i) = f i :=
  cubicSplineFun_apply_node hx hn hi

/-- **The moments of the interpolatory cubic spline** are the solution of the moment system. -/
theorem iteratedDeriv_two_cubicInterp_node {i : ℕ} (hi : i ≤ n) :
    iteratedDeriv 2 (cubicInterp n x f lam0 mun d0 dn) (x i) = momentVec n x f lam0 mun d0 dn i :=
  iteratedDeriv_two_cubicSplineFun_node hx hn
    (fun _ hi1 hin => isMomentEq_momentVec hx hn hl0 hl1 hm0 hm1 hi1 hin) hi

/-- **Uniqueness**: an interpolatory cubic spline with the closure `(λ_0, μ_n, d_0, d_n)` is
`cubicInterp` on `[a, b]`. -/
theorem IsCubicInterp.eqOn_cubicInterp {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s)
    (hc : HasClosure a b n x lam0 mun d0 dn s) :
    EqOn s (cubicInterp n x f lam0 mun d0 dn) (Icc a b) :=
  hs.eqOn_of_hasClosure hx hn hl0 hl1 hm0 hm1 hc (isCubicInterp_cubicInterp hx hn hl0 hl1 hm0 hm1).1
    (isCubicInterp_cubicInterp hx hn hl0 hl1 hm0 hm1).2

end CubicInterp

section NaturalClamped

variable (hx : IsPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ}
include hx hn

/-- The natural spline is `C²` on `ℝ`. -/
theorem contDiff_naturalInterp : ContDiff ℝ 2 (naturalInterp n x f) :=
  contDiff_cubicInterp hx hn le_rfl zero_le_one le_rfl zero_le_one

/-- The clamped spline is `C²` on `ℝ`. -/
theorem contDiff_clampedInterp (f'0 f'n : ℝ) : ContDiff ℝ 2 (clampedInterp n x f f'0 f'n) :=
  contDiff_cubicInterp hx hn zero_le_one le_rfl zero_le_one le_rfl

/-- **The natural spline has vanishing second derivative at the endpoints.** -/
theorem iteratedDeriv_two_naturalInterp_endpoints :
    iteratedDeriv 2 (naturalInterp n x f) a = 0 ∧ iteratedDeriv 2 (naturalInterp n x f) b = 0 := by
  have h := (isCubicInterp_cubicInterp hx hn (f := f) (d0 := 0) (dn := 0) le_rfl zero_le_one le_rfl
    zero_le_one).2
  have hab := hx.lt_of_pos hn
  have hc := contDiff_cubicInterp hx hn (f := f) (d0 := 0) (dn := 0) le_rfl zero_le_one le_rfl
    zero_le_one
  simp only [HasClosure, moment_eq_iteratedDeriv hab hc ⟨hx.left_le (Nat.zero_le n),
    hx.le_right (Nat.zero_le n)⟩,
    moment_eq_iteratedDeriv hab hc ⟨hx.left_le (Nat.sub_le n 1), hx.le_right (Nat.sub_le n 1)⟩,
    moment_eq_iteratedDeriv hab hc ⟨hx.left_le le_rfl, hx.le_right le_rfl⟩, zero_mul, add_zero,
    zero_add, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, hx.first, hx.last] at h
  exact ⟨h.1, h.2⟩

/-- **The clamped spline has the prescribed slopes at the endpoints.** -/
theorem deriv_clampedInterp_endpoints (f'0 f'n : ℝ) :
    deriv (clampedInterp n x f f'0 f'n) a = f'0 ∧ deriv (clampedInterp n x f f'0 f'n) b = f'n := by
  suffices key : ∀ d0 dn : ℝ, d0 = 6 / (x 1 - x 0) * ((f 1 - f 0) / (x 1 - x 0) - f'0) →
      dn = 6 / (x n - x (n - 1)) * (f'n - (f n - f (n - 1)) / (x n - x (n - 1))) →
      deriv (cubicInterp n x f 1 1 d0 dn) a = f'0 ∧ deriv (cubicInterp n x f 1 1 d0 dn) b = f'n from
    key _ _ rfl rfl
  intro d0 dn hd0 hdn
  have hM : ∀ i, 1 ≤ i → i < n → IsMomentEq x f (momentVec n x f 1 1 d0 dn) i :=
    fun _ hi1 hin => isMomentEq_momentVec hx hn zero_le_one le_rfl zero_le_one le_rfl hi1 hin
  have h := (isCubicInterp_cubicInterp hx hn (f := f) (d0 := d0) (dn := dn) zero_le_one le_rfl
    zero_le_one le_rfl).2
  have hab := hx.lt_of_pos hn
  have hc := contDiff_cubicInterp hx hn (f := f) (d0 := d0) (dn := dn) zero_le_one le_rfl
    zero_le_one le_rfl
  simp only [HasClosure] at h
  rw [moment_eq_iteratedDeriv hab hc ⟨hx.left_le (Nat.zero_le n), hx.le_right (Nat.zero_le n)⟩,
    moment_eq_iteratedDeriv hab hc ⟨hx.left_le hn, hx.le_right hn⟩,
    moment_eq_iteratedDeriv hab hc ⟨hx.left_le (Nat.sub_le n 1), hx.le_right (Nat.sub_le n 1)⟩,
    moment_eq_iteratedDeriv hab hc ⟨hx.left_le le_rfl, hx.le_right le_rfl⟩,
    iteratedDeriv_two_cubicInterp_node hx hn zero_le_one le_rfl zero_le_one le_rfl (Nat.zero_le n),
    iteratedDeriv_two_cubicInterp_node hx hn zero_le_one le_rfl zero_le_one le_rfl hn,
    iteratedDeriv_two_cubicInterp_node hx hn zero_le_one le_rfl zero_le_one le_rfl (Nat.sub_le n 1),
    iteratedDeriv_two_cubicInterp_node hx hn zero_le_one le_rfl zero_le_one le_rfl le_rfl] at h
  obtain ⟨h0, hN⟩ := h
  have h1 : x 1 - x 0 ≠ 0 := sub_ne_zero.mpr (hx.step 0 hn).ne'
  have hn' : x n - x (n - 1) ≠ 0 :=
    sub_ne_zero.mpr (hx.lt (Nat.sub_one_lt_of_le hn le_rfl) le_rfl).ne'
  constructor
  · rw [cubicInterp, deriv_cubicSplineFun_left hx hn hM]
    calc -((x 1 - x 0) * momentVec n x f 1 1 d0 dn 0) / 3
          - (x 1 - x 0) * momentVec n x f 1 1 d0 dn 1 / 6 + (f 1 - f 0) / (x 1 - x 0)
        = -((x 1 - x 0) / 6) * (2 * momentVec n x f 1 1 d0 dn 0 + 1 * momentVec n x f 1 1 d0 dn 1)
          + (f 1 - f 0) / (x 1 - x 0) := by ring
      _ = -((x 1 - x 0) / 6) * (6 / (x 1 - x 0) * ((f 1 - f 0) / (x 1 - x 0) - f'0))
          + (f 1 - f 0) / (x 1 - x 0) := by rw [h0, hd0]
      _ = f'0 := by field_simp; ring
  · rw [cubicInterp, deriv_cubicSplineFun_right hx hn hM]
    calc (x n - x (n - 1)) * momentVec n x f 1 1 d0 dn (n - 1) / 6
          + (x n - x (n - 1)) * momentVec n x f 1 1 d0 dn n / 3
          + (f n - f (n - 1)) / (x n - x (n - 1))
        = (x n - x (n - 1)) / 6 * (1 * momentVec n x f 1 1 d0 dn (n - 1)
            + 2 * momentVec n x f 1 1 d0 dn n) + (f n - f (n - 1)) / (x n - x (n - 1)) := by ring
      _ = (x n - x (n - 1)) / 6 * (6 / (x n - x (n - 1))
            * (f'n - (f n - f (n - 1)) / (x n - x (n - 1))))
          + (f n - f (n - 1)) / (x n - x (n - 1)) := by rw [hN, hdn]
      _ = f'n := by field_simp; ring

end NaturalClamped

/-! ### Linearity of the interpolatory spline in the data, and the cardinal basis -/

section Linearity

variable {f g M N : ℕ → ℝ} {lam0 mun d0 dn e0 en c : ℝ}

/-- The panel index lies in `[1, n]` when `1 ≤ n`. -/
theorem panelIndex_mem (hn : 1 ≤ n) (t : ℝ) : 1 ≤ panelIndex n x t ∧ panelIndex n x t ≤ n := by
  refine ⟨Nat.le_add_right _ _, ?_⟩
  unfold panelIndex
  have := (Finset.card_filter_le (Finset.Ico 1 n) fun j => x j ≤ t).trans (Nat.card_Ico 1 n).le
  omega

/-- A glued function depends only on the panel functions of the panels `1, …, n`. -/
theorem panelGlue_congr {E : Type*} (hn : 1 ≤ n) {Q Q' : ℕ → ℝ → E}
    (hQ : ∀ i, 1 ≤ i → i ≤ n → Q i = Q' i) :
    panelGlue n x Q = panelGlue n x Q' :=
  funext fun t => by rw [panelGlue, panelGlue, hQ _ (panelIndex_mem hn t).1 (panelIndex_mem hn t).2]

/-- The panel cubic is additive in the data and the moments. -/
theorem panelCubic_add (i : ℕ) (t : ℝ) :
    panelCubic x (f + g) (M + N) i t = panelCubic x f M i t + panelCubic x g N i t := by
  simp only [panelCubic_apply, Pi.add_apply]
  ring

/-- The panel cubic is homogeneous in the data and the moments. -/
theorem panelCubic_smul (i : ℕ) (t : ℝ) :
    panelCubic x (c • f) (c • M) i t = c * panelCubic x f M i t := by
  simp only [panelCubic_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The glued cubic spline is additive in the data and the moments. -/
theorem cubicSplineFun_add :
    cubicSplineFun n x (f + g) (M + N) = cubicSplineFun n x f M + cubicSplineFun n x g N :=
  funext fun _ => panelCubic_add _ _

/-- The glued cubic spline is homogeneous in the data and the moments. -/
theorem cubicSplineFun_smul : cubicSplineFun n x (c • f) (c • M) = c • cubicSplineFun n x f M :=
  funext fun _ => panelCubic_smul _ _

/-- The right-hand side of the moment system is additive in the data. -/
theorem momentRhs_add (h : ℕ → ℝ) :
    momentRhs n h (f + g) (d0 + e0) (dn + en) = momentRhs n h f d0 dn + momentRhs n h g e0 en := by
  funext i
  simp only [momentRhs, Pi.add_apply]
  split_ifs <;> ring

/-- The right-hand side of the moment system is homogeneous in the data. -/
theorem momentRhs_smul (h : ℕ → ℝ) :
    momentRhs n h (c • f) (c * d0) (c * dn) = c • momentRhs n h f d0 dn := by
  funext i
  simp only [momentRhs, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The extension by zero is additive. -/
theorem extendFin_add (v w : Fin (n + 1) → ℝ) : extendFin (v + w) = extendFin v + extendFin w := by
  funext i
  rcases lt_or_ge i (n + 1) with hi | hi
  · simp [extendFin_of_lt _ hi]
  · simp [extendFin_of_le _ hi]

/-- The extension by zero is homogeneous. -/
theorem extendFin_smul (v : Fin (n + 1) → ℝ) : extendFin (c • v) = c • extendFin v := by
  funext i
  rcases lt_or_ge i (n + 1) with hi | hi
  · simp [extendFin_of_lt _ hi]
  · simp [extendFin_of_le _ hi]

/-- The moment vector is additive in the data. -/
theorem momentVec_add :
    momentVec n x (f + g) lam0 mun (d0 + e0) (dn + en)
      = momentVec n x f lam0 mun d0 dn + momentVec n x g lam0 mun e0 en := by
  rw [momentVec, momentVec, momentVec, momentRhs_add, Matrix.mulVec_add, extendFin_add]

/-- The moment vector is homogeneous in the data. -/
theorem momentVec_smul :
    momentVec n x (c • f) lam0 mun (c * d0) (c * dn) = c • momentVec n x f lam0 mun d0 dn := by
  rw [momentVec, momentVec, momentRhs_smul, Matrix.mulVec_smul, extendFin_smul]

/-- **The interpolatory cubic spline is additive in the data and the closure values.** -/
theorem cubicInterp_add :
    cubicInterp n x (f + g) lam0 mun (d0 + e0) (dn + en)
      = cubicInterp n x f lam0 mun d0 dn + cubicInterp n x g lam0 mun e0 en := by
  rw [cubicInterp, momentVec_add, cubicSplineFun_add]
  rfl

/-- **The interpolatory cubic spline is homogeneous in the data and the closure values.** -/
theorem cubicInterp_smul :
    cubicInterp n x (c • f) lam0 mun (c * d0) (c * dn) = c • cubicInterp n x f lam0 mun d0 dn := by
  rw [cubicInterp, momentVec_smul, cubicSplineFun_smul]
  rfl

/-- The interpolatory cubic spline of zero data with zero closure values is zero. -/
theorem cubicInterp_zero : cubicInterp n x 0 lam0 mun 0 0 = 0 := by
  have := cubicInterp_smul (n := n) (x := x) (f := 0) (lam0 := lam0) (mun := mun) (d0 := 0)
    (dn := 0) (c := 0)
  simpa using this

/-- The interpolatory cubic spline of a finite combination of data. -/
theorem cubicInterp_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → ℕ → ℝ) (D0 Dn : ι → ℝ) :
    cubicInterp n x (∑ i ∈ s, c i • F i) lam0 mun (∑ i ∈ s, c i * D0 i) (∑ i ∈ s, c i * Dn i)
      = ∑ i ∈ s, c i • cubicInterp n x (F i) lam0 mun (D0 i) (Dn i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cubicInterp_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj,
      cubicInterp_add, cubicInterp_smul, ih]

/-- The interpolatory cubic spline depends only on the data at the nodes `x 0, …, x n`. -/
theorem cubicInterp_congr (hn : 1 ≤ n) (hfg : ∀ i ≤ n, f i = g i) :
    cubicInterp n x f lam0 mun d0 dn = cubicInterp n x g lam0 mun d0 dn := by
  have hrhs : momentRhs n (panelLength x) f d0 dn = momentRhs n (panelLength x) g d0 dn := by
    funext i
    simp only [momentRhs]
    split_ifs with h0 hN
    · rfl
    · rfl
    · rw [hfg (i + 1) (by have := i.2; omega), hfg i (by omega), hfg (i - 1) (by omega)]
  rw [cubicInterp, cubicInterp, momentVec, momentVec, hrhs]
  refine panelGlue_congr hn fun i hi1 hin => funext fun t => ?_
  simp only [panelCubic]
  rw [panelCubicPoly_congr (hfg _ (by omega)) (hfg _ hin) rfl rfl]

end Linearity

/-! ### The cardinal basis -/

/-- **The cardinal spline basis** ([quarteroni2000numerical] §8.6.1): for `i ≤ n`, the clamped
spline `φ_i` with `φ_i(x_j) = δ_ij` and `φ_i'(a) = φ_i'(b) = 0`; `φ_{n+1}` vanishes at every node
with `φ_{n+1}'(a) = 1`, `φ_{n+1}'(b) = 0`, and `φ_{n+2}` with `φ_{n+2}'(a) = 0`, `φ_{n+2}'(b) = 1`.
-/
noncomputable def cardinalBasis (n : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℝ → ℝ :=
  if i ≤ n then clampedInterp n x (Pi.single i 1) 0 0
  else if i = n + 1 then clampedInterp n x 0 1 0 else clampedInterp n x 0 0 1

section Cardinal

variable (hx : IsPartition a b n x) (hn : 1 ≤ n)
include hx hn

/-- The cardinal functions at the nodes: `φ_i(x_j) = δ_ij` for `i, j ≤ n`, and `φ_{n+1}`, `φ_{n+2}`
vanish at the nodes. -/
theorem cardinalBasis_apply_node (i : ℕ) {j : ℕ} (hj : j ≤ n) :
    cardinalBasis n x i (x j) = if i = j then 1 else 0 := by
  by_cases hi : i ≤ n
  · rw [cardinalBasis, ite_eq_left hi, clampedInterp, cubicInterp_apply_node hx hn hj,
      Pi.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · rw [ite_eq_right (show i ≠ j by omega), cardinalBasis, ite_eq_right hi]
    split_ifs <;> rw [clampedInterp, cubicInterp_apply_node hx hn hj] <;> rfl

/-- The slopes of the cardinal functions at `a`: `φ_i'(a) = 0` for `i ≤ n`, `φ_{n+1}'(a) = 1`,
`φ_{n+2}'(a) = 0`. -/
theorem deriv_cardinalBasis_left (i : ℕ) :
    deriv (cardinalBasis n x i) a = if i = n + 1 then 1 else 0 := by
  unfold cardinalBasis
  by_cases hi : i ≤ n
  · rw [ite_eq_left hi, (deriv_clampedInterp_endpoints hx hn _ _).1, ite_eq_right (by omega)]
  · by_cases hi' : i = n + 1
    · rw [ite_eq_right hi, ite_eq_left hi', (deriv_clampedInterp_endpoints hx hn _ _).1,
        ite_eq_left hi']
    · rw [ite_eq_right hi, ite_eq_right hi', (deriv_clampedInterp_endpoints hx hn _ _).1,
        ite_eq_right hi']

/-- The slopes of the cardinal functions at `b`: `φ_i'(b) = 0` for `i ≤ n + 1`,
`φ_{n+2}'(b) = 1`. -/
theorem deriv_cardinalBasis_right {i : ℕ} (hi2 : i ≤ n + 2) :
    deriv (cardinalBasis n x i) b = if i = n + 2 then 1 else 0 := by
  unfold cardinalBasis
  by_cases hi : i ≤ n
  · rw [ite_eq_left hi, (deriv_clampedInterp_endpoints hx hn _ _).2, ite_eq_right (by omega)]
  · by_cases hi' : i = n + 1
    · rw [ite_eq_right hi, ite_eq_left hi', (deriv_clampedInterp_endpoints hx hn _ _).2,
        ite_eq_right (by omega)]
    · rw [ite_eq_right hi, ite_eq_right hi', (deriv_clampedInterp_endpoints hx hn _ _).2,
        ite_eq_left (by omega)]

omit hx hn in
/-- The sum `∑_{i ≤ n} f_i (δ_{i,k} - δ_{i,l})` for `k, l` at most `n`. -/
theorem sum_mul_single_sub_single {f : ℕ → ℝ} {k l : ℕ} (hk : k ≤ n) (hl : l ≤ n) :
    ∑ i ∈ Finset.range (n + 1), f i * ((Pi.single i 1 : ℕ → ℝ) k - (Pi.single i 1 : ℕ → ℝ) l)
      = f k - f l := by
  simp only [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_range]
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]

omit hx in
/-- **The clamped spline in the cardinal basis** ([quarteroni2000numerical] §8.6.1):
`s_3 = ∑_{i ≤ n} f_i φ_i + f'_0 φ_{n+1} + f'_n φ_{n+2}`. -/
theorem clampedInterp_eq_sum_cardinalBasis (f : ℕ → ℝ) (f'0 f'n : ℝ) :
    clampedInterp n x f f'0 f'n = ∑ i ∈ Finset.range (n + 1), f i • cardinalBasis n x i
      + f'0 • cardinalBasis n x (n + 1) + f'n • cardinalBasis n x (n + 2) := by
  classical
  -- the closure values are linear in the data
  set D0 : (ℕ → ℝ) → ℝ → ℝ := fun f f'0 => 6 / (x 1 - x 0) * ((f 1 - f 0) / (x 1 - x 0) - f'0)
    with hD0def
  set Dn : (ℕ → ℝ) → ℝ → ℝ :=
    fun f f'n => 6 / (x n - x (n - 1)) * (f'n - (f n - f (n - 1)) / (x n - x (n - 1))) with hDndef
  have hsum : ∑ i ∈ Finset.range (n + 1), f i • cardinalBasis n x i
      = cubicInterp n x (∑ i ∈ Finset.range (n + 1), f i • Pi.single i (1 : ℝ)) 1 1
        (∑ i ∈ Finset.range (n + 1), f i * D0 (Pi.single i 1) 0)
        (∑ i ∈ Finset.range (n + 1), f i * Dn (Pi.single i 1) 0) := by
    rw [cubicInterp_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [cardinalBasis, ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    rfl
  rw [hsum, show f'0 • cardinalBasis n x (n + 1) = cubicInterp n x (f'0 • (0 : ℕ → ℝ)) 1 1
      (f'0 * D0 0 1) (f'0 * Dn 0 0) by
        rw [cubicInterp_smul, cardinalBasis, ite_eq_right (by omega), ite_eq_left rfl]; rfl,
    show f'n • cardinalBasis n x (n + 2) = cubicInterp n x (f'n • (0 : ℕ → ℝ)) 1 1
      (f'n * D0 0 0) (f'n * Dn 0 1) by
        rw [cubicInterp_smul, cardinalBasis, ite_eq_right (by omega), ite_eq_right (by omega)]; rfl,
    ← cubicInterp_add, ← cubicInterp_add, clampedInterp]
  have hD0 : ∑ i ∈ Finset.range (n + 1), f i * D0 (Pi.single i 1) 0 + f'0 * D0 0 1 + f'n * D0 0 0
      = D0 f f'0 := by
    have : ∀ i, f i * D0 (Pi.single i 1) 0
        = 6 / (x 1 - x 0) / (x 1 - x 0)
          * (f i * ((Pi.single i 1 : ℕ → ℝ) 1 - (Pi.single i 1 : ℕ → ℝ) 0)) := by
      intro i; simp only [hD0def]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, sum_mul_single_sub_single hn (Nat.zero_le n)]
    simp only [hD0def, Pi.zero_apply]
    ring
  have hDn : ∑ i ∈ Finset.range (n + 1), f i * Dn (Pi.single i 1) 0 + f'0 * Dn 0 0 + f'n * Dn 0 1
      = Dn f f'n := by
    have : ∀ i, f i * Dn (Pi.single i 1) 0
        = -(6 / (x n - x (n - 1)) / (x n - x (n - 1)))
          * (f i * ((Pi.single i 1 : ℕ → ℝ) n - (Pi.single i 1 : ℕ → ℝ) (n - 1))) := by
      intro i; simp only [hDndef]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, sum_mul_single_sub_single le_rfl (Nat.sub_le n 1)]
    simp only [hDndef, Pi.zero_apply]
    ring
  rw [hD0, hDn]
  refine cubicInterp_congr hn fun i hi => ?_
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    Pi.zero_apply, mul_zero, add_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_range]
  rw [ite_eq_left (by omega)]

end Cardinal

/-! ### Calculus of `C²` functions on a compact interval

The derivatives of a function of class `C²` on `Icc a b` are the derivatives within `Icc a b`:
`f' = derivWithin f (Icc a b)` and `f'' = iteratedDerivWithin 2 f (Icc a b)`. At interior points
they are the ordinary derivatives, and both are continuous on `Icc a b`. -/

section C2

variable {f : ℝ → ℝ} (hab : a < b) (hf : ContDiffOn ℝ 2 f (Icc a b))
include hab hf

/-- The derivative within `[a, b]` of a `C²` function is `C¹` on `[a, b]`. -/
theorem contDiffOn_derivWithin_of_contDiffOn_two :
    ContDiffOn ℝ 1 (derivWithin f (Icc a b)) (Icc a b) := by
  have := hf
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl,
    contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)] at this
  exact this.2.2

/-- The derivative within `[a, b]` of a `C²` function is continuous on `[a, b]`. -/
theorem continuousOn_derivWithin_of_contDiffOn_two :
    ContinuousOn (derivWithin f (Icc a b)) (Icc a b) :=
  (contDiffOn_derivWithin_of_contDiffOn_two hab hf).continuousOn

/-- The second derivative within `[a, b]` of a `C²` function is continuous on `[a, b]`. -/
theorem continuousOn_iteratedDerivWithin_two :
    ContinuousOn (iteratedDerivWithin 2 f (Icc a b)) (Icc a b) :=
  hf.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hab)

omit hab in
/-- At an interior point a `C²` function has the derivative `derivWithin f (Icc a b)`. -/
theorem hasDerivAt_of_contDiffOn_two {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt f (derivWithin f (Icc a b) t) t :=
  ((hf.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- At an interior point the derivative within `[a, b]` of a `C²` function has the derivative
`iteratedDerivWithin 2 f (Icc a b)`. -/
theorem hasDerivAt_derivWithin_of_contDiffOn_two {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (derivWithin f (Icc a b)) (iteratedDerivWithin 2 f (Icc a b) t) t := by
  rw [iteratedDerivWithin_succ, iteratedDerivWithin_one]
  exact (((contDiffOn_derivWithin_of_contDiffOn_two hab hf).differentiableOn (by norm_num) t
    (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- At an interior point the ordinary second derivative of a `C²` function on `[a, b]` is the
second derivative within `[a, b]`. -/
theorem iteratedDeriv_two_eq_iteratedDerivWithin_of_contDiffOn {t : ℝ} (ht : t ∈ Ioo a b) :
    iteratedDeriv 2 f t = iteratedDerivWithin 2 f (Icc a b) t :=
  (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
    (hf.contDiffAt (Icc_mem_nhds ht.1 ht.2)) (Ioo_subset_Icc_self ht)).symm

end C2

/-- Two functions agreeing on the open interval have the same interval integral. -/
theorem intervalIntegral_congr_Ioo {g h : ℝ → ℝ} (hab : a ≤ b) (hgh : ∀ t ∈ Ioo a b, g t = h t) :
    ∫ t in a..b, g t = ∫ t in a..b, h t := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => hgh t ht

/-! ### Holladay's identity and the minimum-norm property -/

section Holladay

variable (hx : IsPartition a b n x) (hn : 1 ≤ n) {f s g : ℝ → ℝ}
  (hf : ContDiffOn ℝ 2 f (Icc a b)) (hs : IsCubicInterp a b n x (fun i => f (x i)) s)
  (hg : IsCubicSpline a b n x g)
include hx hn hf hs hg

/-- **Holladay's identity on one panel**: for `f` of class `C²`, an interpolatory cubic spline
`s` of its nodal values and a cubic spline `g`, on the panel `[x (i - 1), x i]`,
`∫ (f'' - s'') g'' = [(f' - s') g'']` at the ends of the panel — integration by parts, the term
`∫ (f' - s') g'''` vanishing because `g'''` is constant on the panel and `f - s` vanishes at its
ends. -/
theorem integral_sub_deriv2_mul_deriv2_panel {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    ∫ t in (x (i - 1))..(x i), (iteratedDerivWithin 2 f (Icc a b) t
      - iteratedDerivWithin 2 s (Icc a b) t) * iteratedDerivWithin 2 g (Icc a b) t
    = (derivWithin f (Icc a b) (x i) - derivWithin s (Icc a b) (x i))
        * iteratedDerivWithin 2 g (Icc a b) (x i)
      - (derivWithin f (Icc a b) (x (i - 1)) - derivWithin s (Icc a b) (x (i - 1)))
        * iteratedDerivWithin 2 g (Icc a b) (x (i - 1)) := by
  have hab := hx.lt_of_pos hn
  have huv : x (i - 1) < x i := hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have hsubo : Ioo (x (i - 1)) (x i) ⊆ Ioo a b :=
    Ioo_subset_Ioo (hx.left_le (by omega)) (hx.le_right hin)
  obtain ⟨p, hpd, hpe⟩ := hg.piecewise i hi1 hin
  -- the third derivative of the panel cubic is a constant `c`
  set c : ℝ := (derivative (derivative (derivative p))).coeff 0 with hc
  have hc' : ∀ t, (derivative (derivative (derivative p))).eval t = c := by
    intro t
    have hdeg : (derivative (derivative (derivative p))).natDegree = 0 := by
      have h0 : p.natDegree ≤ 3 := natDegree_le_of_degree_le hpd
      have h1 : (derivative p).natDegree ≤ 2 := (natDegree_derivative_le p).trans (by omega)
      have h2 : (derivative (derivative p)).natDegree ≤ 1 :=
        (natDegree_derivative_le _).trans (by omega)
      have h3 : (derivative (derivative (derivative p))).natDegree ≤ 0 :=
        (natDegree_derivative_le _).trans (by omega)
      omega
    rw [eq_C_of_natDegree_eq_zero hdeg, eval_C]
  -- the second derivative of `g` on the panel
  have hG2 : ∀ t ∈ Icc (x (i - 1)) (x i),
      iteratedDerivWithin 2 g (Icc a b) t = (derivative (derivative p)).eval t :=
    fun t ht => (derivWithin_eq_of_eqOn_Icc_of_contDiffOn hg.contDiffOn huv hsub hpe ht).2
  have hG2' : ∀ t ∈ Ioo (x (i - 1)) (x i), HasDerivAt (iteratedDerivWithin 2 g (Icc a b)) c t := by
    intro t ht
    have : iteratedDerivWithin 2 g (Icc a b) =ᶠ[𝓝 t]
        fun t => (derivative (derivative p)).eval t := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact hG2 u (Ioo_subset_Icc_self hu)
    rw [← hc' t]
    exact ((derivative (derivative p)).hasDerivAt t).congr_of_eventuallyEq this
  -- continuity of the pieces on the closed panel
  have hF1c := (continuousOn_derivWithin_of_contDiffOn_two hab hf).mono hsub
  have hF2c := (continuousOn_iteratedDerivWithin_two hab hf).mono hsub
  have hS1c := (continuousOn_derivWithin_of_contDiffOn_two hab hs.contDiffOn).mono hsub
  have hS2c := (continuousOn_iteratedDerivWithin_two hab hs.contDiffOn).mono hsub
  have hG2c := (continuousOn_iteratedDerivWithin_two hab hg.contDiffOn).mono hsub
  -- integration by parts
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := fun t => derivWithin f (Icc a b) t - derivWithin s (Icc a b) t)
    (v := iteratedDerivWithin 2 g (Icc a b))
    (u' := fun t => iteratedDerivWithin 2 f (Icc a b) t - iteratedDerivWithin 2 s (Icc a b) t)
    (v' := fun _ => c) (a := x (i - 1)) (b := x i)
    (by rw [uIcc_of_le huv.le]; exact hF1c.sub hS1c) (by rw [uIcc_of_le huv.le]; exact hG2c)
    (fun t ht => by
      rw [min_eq_left huv.le, max_eq_right huv.le] at ht
      exact ((hasDerivAt_derivWithin_of_contDiffOn_two hab hf (hsubo ht)).sub
        (hasDerivAt_derivWithin_of_contDiffOn_two hab hs.contDiffOn (hsubo ht))).hasDerivWithinAt)
    (fun t ht => by
      rw [min_eq_left huv.le, max_eq_right huv.le] at ht
      exact (hG2' t ht).hasDerivWithinAt)
    (by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le huv.le]; exact hF2c.sub hS2c)
    (continuous_const.intervalIntegrable _ _)
  -- the term `∫ (f' - s') c` vanishes
  have hz : ∫ t in (x (i - 1))..(x i), (derivWithin f (Icc a b) t - derivWithin s (Icc a b) t) * c
      = 0 := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le huv.le (f := fun t => f t - s t)
        ((hf.continuousOn.mono hsub).sub (hs.contDiffOn.continuousOn.mono hsub))
        (fun t ht => ((hasDerivAt_of_contDiffOn_two hf (hsubo ht)).sub
          (hasDerivAt_of_contDiffOn_two hs.contDiffOn (hsubo ht))).hasDerivWithinAt)
        (by
          refine ContinuousOn.intervalIntegrable ?_
          rw [uIcc_of_le huv.le]; exact hF1c.sub hS1c)]
    rw [hs.interp i hin, hs.interp (i - 1) (by omega)]
    ring
  rw [hz] at hibp
  linarith

/-- **Holladay's identity, summed over the panels**: for `f` of class `C²` on `[a, b]`, an
interpolatory cubic spline `s` of its nodal values and any cubic spline `g`,
`∫_a^b (f'' - s'') g'' = [(f' - s') g'']_a^b`. -/
theorem integral_sub_deriv2_mul_deriv2_eq :
    ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t - iteratedDerivWithin 2 s (Icc a b) t)
      * iteratedDerivWithin 2 g (Icc a b) t
    = (derivWithin f (Icc a b) b - derivWithin s (Icc a b) b) * iteratedDerivWithin 2 g (Icc a b) b
      - (derivWithin f (Icc a b) a - derivWithin s (Icc a b) a)
        * iteratedDerivWithin 2 g (Icc a b) a := by
  have hab := hx.lt_of_pos hn
  set G : ℝ → ℝ := fun t => (iteratedDerivWithin 2 f (Icc a b) t
    - iteratedDerivWithin 2 s (Icc a b) t) * iteratedDerivWithin 2 g (Icc a b) t with hG
  have hGc : ContinuousOn G (Icc a b) :=
    ((continuousOn_iteratedDerivWithin_two hab hf).sub
      (continuousOn_iteratedDerivWithin_two hab hs.contDiffOn)).mul
      (continuousOn_iteratedDerivWithin_two hab hg.contDiffOn)
  set B : ℕ → ℝ := fun i => (derivWithin f (Icc a b) (x i) - derivWithin s (Icc a b) (x i))
    * iteratedDerivWithin 2 g (Icc a b) (x i) with hB
  have hsplit : ∫ t in a..b, G t = ∑ k ∈ Finset.range n, ∫ t in (x k)..(x (k + 1)), G t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals, hx.first, hx.last]
    intro k hk
    exact (hGc.mono (hx.Icc_subset hk)).intervalIntegrable_of_Icc (hx.step k hk).le
  have hpanel : ∀ k ∈ Finset.range n, ∫ t in (x k)..(x (k + 1)), G t = B (k + 1) - B k := by
    intro k hk
    have := integral_sub_deriv2_mul_deriv2_panel hx hn hf hs hg (i := k + 1) (by omega)
      (Finset.mem_range.mp hk)
    simpa using this
  rw [hsplit, Finset.sum_congr rfl hpanel, Finset.sum_range_sub B n, hB]
  simp only [hx.first, hx.last]

omit hg in
/-- **Holladay's orthogonality identity** ([quarteroni2000numerical] Exercise 8.11): for `f` of
class `C²` on `[a, b]` and an interpolatory cubic spline `s` of its nodal values which is either
natural (`s''(a) = s''(b) = 0`) or clamped (`s'(a) = f'(a)`, `s'(b) = f'(b)`),
`∫_a^b (f'' - s'') s'' = 0`: the boundary terms `[(f' - s') s'']_a^b` vanish under either end
condition. -/
theorem integral_sub_deriv2_mul_deriv2_eq_zero
    (hend : (iteratedDerivWithin 2 s (Icc a b) a = 0 ∧ iteratedDerivWithin 2 s (Icc a b) b = 0) ∨
      (derivWithin s (Icc a b) a = derivWithin f (Icc a b) a ∧
        derivWithin s (Icc a b) b = derivWithin f (Icc a b) b)) :
    ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t - iteratedDerivWithin 2 s (Icc a b) t)
      * iteratedDerivWithin 2 s (Icc a b) t = 0 := by
  rw [integral_sub_deriv2_mul_deriv2_eq hx hn hf hs hs.toIsCubicSpline]
  rcases hend with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]; ring
  · rw [h0, h1]; ring

omit hg in
/-- **The minimum-norm property for a natural or clamped interpolatory spline**
([quarteroni2000numerical] Property 8.2, Holladay): `∫_a^b s''² ≤ ∫_a^b f''²`, from
`∫ f''² = ∫ s''² + ∫ (f'' - s'')² + 2 ∫ (f'' - s'') s''` and the orthogonality identity. -/
theorem integral_sq_deriv2_le_of_end
    (hend : (iteratedDerivWithin 2 s (Icc a b) a = 0 ∧ iteratedDerivWithin 2 s (Icc a b) b = 0) ∨
      (derivWithin s (Icc a b) a = derivWithin f (Icc a b) a ∧
        derivWithin s (Icc a b) b = derivWithin f (Icc a b) b)) :
    ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      ≤ ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2 := by
  have hab := hx.lt_of_pos hn
  have hF2c := continuousOn_iteratedDerivWithin_two hab hf
  have hS2c := continuousOn_iteratedDerivWithin_two hab hs.contDiffOn
  have horth := integral_sub_deriv2_mul_deriv2_eq_zero hx hn hf hs hend
  have hint : ∀ g : ℝ → ℝ, ContinuousOn g (Icc a b) →
      IntervalIntegrable g MeasureTheory.volume a b :=
    fun g hg => hg.intervalIntegrable_of_Icc hab.le
  have hexp : ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2
      = (∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
            - iteratedDerivWithin 2 s (Icc a b) t) ^ 2)
        + (∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2)
        + 2 * ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
            - iteratedDerivWithin 2 s (Icc a b) t) * iteratedDerivWithin 2 s (Icc a b) t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add,
      ← intervalIntegral.integral_add]
    · exact intervalIntegral.integral_congr fun t _ => by ring
    · exact hint _ (((hF2c.sub hS2c).pow 2).add (hS2c.pow 2))
    · exact hint _ (continuousOn_const.mul ((hF2c.sub hS2c).mul hS2c))
    · exact hint _ ((hF2c.sub hS2c).pow 2)
    · exact hint _ (hS2c.pow 2)
  rw [hexp, horth, mul_zero, add_zero]
  have : 0 ≤ ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
      - iteratedDerivWithin 2 s (Icc a b) t) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun t _ => sq_nonneg _
  linarith

omit hg in
/-- **Equality in the minimum-norm property forces `f = s`**: if `∫ s''² = ∫ f''²` for a natural or
clamped interpolatory spline `s` of `f`, then `f'' = s''` on `[a, b]`, so `f - s` is affine and
vanishes at the `n + 1 ≥ 2` nodes, hence `f = s` on `[a, b]`. -/
theorem eqOn_of_integral_sq_deriv2_eq
    (hend : (iteratedDerivWithin 2 s (Icc a b) a = 0 ∧ iteratedDerivWithin 2 s (Icc a b) b = 0) ∨
      (derivWithin s (Icc a b) a = derivWithin f (Icc a b) a ∧
        derivWithin s (Icc a b) b = derivWithin f (Icc a b) b))
    (heq : ∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2
      = ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2) : EqOn f s (Icc a b) := by
  have hab := hx.lt_of_pos hn
  have hF2c := continuousOn_iteratedDerivWithin_two hab hf
  have hS2c := continuousOn_iteratedDerivWithin_two hab hs.contDiffOn
  have horth := integral_sub_deriv2_mul_deriv2_eq_zero hx hn hf hs hend
  have hint : ∀ g : ℝ → ℝ, ContinuousOn g (Icc a b) →
      IntervalIntegrable g MeasureTheory.volume a b :=
    fun g hg => hg.intervalIntegrable_of_Icc hab.le
  -- the integral of `(f'' - s'')²` vanishes
  have hzero : ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
      - iteratedDerivWithin 2 s (Icc a b) t) ^ 2 = 0 := by
    have hexp : ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2
        = (∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
              - iteratedDerivWithin 2 s (Icc a b) t) ^ 2)
          + (∫ t in a..b, iteratedDerivWithin 2 s (Icc a b) t ^ 2)
          + 2 * ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
              - iteratedDerivWithin 2 s (Icc a b) t) * iteratedDerivWithin 2 s (Icc a b) t := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add,
        ← intervalIntegral.integral_add]
      · exact intervalIntegral.integral_congr fun t _ => by ring
      · exact hint _ (((hF2c.sub hS2c).pow 2).add (hS2c.pow 2))
      · exact hint _ (continuousOn_const.mul ((hF2c.sub hS2c).mul hS2c))
      · exact hint _ ((hF2c.sub hS2c).pow 2)
      · exact hint _ (hS2c.pow 2)
    rw [horth] at hexp
    linarith
  -- hence `f'' = s''` on `[a, b]`
  have hFS : EqOn (iteratedDerivWithin 2 f (Icc a b)) (iteratedDerivWithin 2 s (Icc a b))
      (Icc a b) := by
    have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le
      (Filter.Eventually.of_forall fun t => sq_nonneg _)
      (hint _ ((hF2c.sub hS2c).pow 2))).mp hzero
    have hsq : EqOn (fun t => (iteratedDerivWithin 2 f (Icc a b) t
        - iteratedDerivWithin 2 s (Icc a b) t) ^ 2) 0 (Ioc a b) :=
      MeasureTheory.Measure.eqOn_of_ae_eq hae (((hF2c.sub hS2c).pow 2).mono Ioc_subset_Icc_self)
        continuousOn_const (by rw [interior_Ioc, closure_Ioo hab.ne]; exact Ioc_subset_Icc_self)
    have hIoo : EqOn (iteratedDerivWithin 2 f (Icc a b)) (iteratedDerivWithin 2 s (Icc a b))
        (Ioo a b) := fun t ht => by
      have := hsq (Ioo_subset_Ioc_self ht)
      simp only [Pi.zero_apply, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        sub_eq_zero] at this
      exact this
    exact hIoo.of_subset_closure hF2c hS2c Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  -- `e = f - s` has `e'' = 0` inside, so `e'` is constant inside, and it vanishes somewhere
  set e : ℝ → ℝ := fun t => f t - s t with he
  set E1 : ℝ → ℝ := fun t => derivWithin f (Icc a b) t - derivWithin s (Icc a b) t with hE1
  have hec : ContinuousOn e (Icc a b) := hf.continuousOn.sub hs.contDiffOn.continuousOn
  have hed : ∀ t ∈ Ioo a b, HasDerivAt e (E1 t) t := fun t ht =>
    (hasDerivAt_of_contDiffOn_two hf ht).sub (hasDerivAt_of_contDiffOn_two hs.contDiffOn ht)
  have hE1d : ∀ t ∈ Ioo a b, HasDerivAt E1 0 t := fun t ht => by
    have := (hasDerivAt_derivWithin_of_contDiffOn_two hab hf ht).sub
      (hasDerivAt_derivWithin_of_contDiffOn_two hab hs.contDiffOn ht)
    rwa [hFS (Ioo_subset_Icc_self ht), sub_self] at this
  have hea : e a = 0 := by
    simp only [he, ← hx.first]
    rw [hs.interp 0 (Nat.zero_le n), sub_self]
  have heb : e b = 0 := by
    simp only [he, ← hx.last]
    rw [hs.interp n le_rfl, sub_self]
  obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hab hec (hea.trans heb.symm) hed
  have hE1const : ∀ t ∈ Ioo a b, E1 t = 0 := fun t ht => by
    rw [← hξ0]
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun u hu => (hE1d u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hE1d u hu).deriv) ht hξ
  -- so `e` is constant on `[a, b]`, equal to `e a = 0`
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact sub_eq_zero.mp hea
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope e hat (hec.mono (Icc_subset_Icc le_rfl ht.2))
    (fun u hu => (hed u ⟨hu.1, hu.2.trans_le ht.2⟩).differentiableAt.differentiableWithinAt)
  rw [(hed c ⟨hc.1, hc.2.trans_le ht.2⟩).deriv, hE1const c ⟨hc.1, hc.2.trans_le ht.2⟩, hea,
    sub_zero, eq_comm, div_eq_zero_iff] at hc'
  rcases hc' with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (sub_ne_zero.mpr hat.ne')

end Holladay

section HolladayNamed

variable (hx : IsPartition a b n x) (hn : 1 ≤ n) {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Icc a b))
include hx hn

/-- The natural interpolatory spline of `f` is an interpolatory cubic spline of its nodal values
whose second derivative within `[a, b]` vanishes at the endpoints. -/
theorem isCubicInterp_naturalInterp_and_end :
    IsCubicInterp a b n x (fun i => f (x i)) (naturalInterp n x fun i => f (x i)) ∧
      iteratedDerivWithin 2 (naturalInterp n x fun i => f (x i)) (Icc a b) a = 0 ∧
      iteratedDerivWithin 2 (naturalInterp n x fun i => f (x i)) (Icc a b) b = 0 := by
  have hab := hx.lt_of_pos hn
  have hc : ContDiff ℝ 2 (naturalInterp n x fun i => f (x i)) :=
    contDiff_cubicInterp hx hn (f := fun i => f (x i)) (d0 := 0) (dn := 0) le_rfl zero_le_one
      le_rfl zero_le_one
  obtain ⟨h0, h1⟩ := iteratedDeriv_two_naturalInterp_endpoints hx hn (f := fun i => f (x i))
  refine ⟨(isCubicInterp_cubicInterp hx hn le_rfl zero_le_one le_rfl zero_le_one).1, ?_, ?_⟩
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hc.contDiffAt
      (left_mem_Icc.mpr hab.le)]
    exact h0
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hc.contDiffAt
      (right_mem_Icc.mpr hab.le)]
    exact h1

/-- The clamped interpolatory spline of `f`, with the slopes of `f` prescribed at the ends, is an
interpolatory cubic spline of its nodal values whose derivative within `[a, b]` agrees with that
of `f` at the endpoints. -/
theorem isCubicInterp_clampedInterp_and_end :
    IsCubicInterp a b n x (fun i => f (x i)) (clampedInterp n x (fun i => f (x i))
        (derivWithin f (Icc a b) a) (derivWithin f (Icc a b) b)) ∧
      derivWithin (clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
        (derivWithin f (Icc a b) b)) (Icc a b) a = derivWithin f (Icc a b) a ∧
      derivWithin (clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
        (derivWithin f (Icc a b) b)) (Icc a b) b = derivWithin f (Icc a b) b := by
  have hab := hx.lt_of_pos hn
  have hc : ContDiff ℝ 2 (clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
      (derivWithin f (Icc a b) b)) :=
    contDiff_cubicInterp hx hn (f := fun i => f (x i))
      (d0 := 6 / (x 1 - x 0) * ((f (x 1) - f (x 0)) / (x 1 - x 0) - derivWithin f (Icc a b) a))
      (dn := 6 / (x n - x (n - 1)) * (derivWithin f (Icc a b) b
        - (f (x n) - f (x (n - 1))) / (x n - x (n - 1)))) zero_le_one le_rfl zero_le_one le_rfl
  obtain ⟨h0, h1⟩ := deriv_clampedInterp_endpoints hx hn (f := fun i => f (x i))
    (derivWithin f (Icc a b) a) (derivWithin f (Icc a b) b)
  refine ⟨(isCubicInterp_cubicInterp hx hn zero_le_one le_rfl zero_le_one le_rfl).1, ?_, ?_⟩
  · rw [(hc.differentiable (by norm_num) a).derivWithin
      (uniqueDiffOn_Icc hab a (left_mem_Icc.mpr hab.le))]
    exact h0
  · rw [(hc.differentiable (by norm_num) b).derivWithin
      (uniqueDiffOn_Icc hab b (right_mem_Icc.mpr hab.le))]
    exact h1

/-- For a function `C²` on all of `ℝ`, the integral of a function of its second derivative
within `[a, b]` is that of its ordinary second derivative. -/
theorem intervalIntegral_iteratedDerivWithin_two_eq {s : ℝ → ℝ} (hs : ContDiff ℝ 2 s)
    (Φ : ℝ → ℝ → ℝ) :
    ∫ t in a..b, Φ t (iteratedDerivWithin 2 s (Icc a b) t)
      = ∫ t in a..b, Φ t (iteratedDeriv 2 s t) := by
  have hab := hx.lt_of_pos hn
  refine intervalIntegral_congr_Ioo hab.le fun t ht => ?_
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hs.contDiffAt
    (Ioo_subset_Icc_self ht)]

include hf

/-- **The minimum-norm property** ([quarteroni2000numerical] Property 8.2, Holladay): for
`f ∈ C²[a, b]` and `s_3` the natural cubic spline interpolating `f` at the nodes,
`∫_a^b s_3''² ≤ ∫_a^b f''²`, with `f''` the second derivative within `[a, b]`. -/
theorem holladay :
    ∫ t in a..b, iteratedDeriv 2 (naturalInterp n x fun i => f (x i)) t ^ 2
      ≤ ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2 := by
  obtain ⟨hs, h0, h1⟩ := isCubicInterp_naturalInterp_and_end hx hn (f := f)
  rw [← intervalIntegral_iteratedDerivWithin_two_eq hx hn (contDiff_naturalInterp hx hn)
    fun _ y => y ^ 2]
  exact integral_sq_deriv2_le_of_end hx hn hf hs (Or.inl ⟨h0, h1⟩)

/-- **Equality in the minimum-norm property holds exactly when `f` is its natural spline**
([quarteroni2000numerical] Property 8.2): `∫_a^b s_3''² = ∫_a^b f''²` iff `f = s_3` on `[a, b]`. -/
theorem holladay_eq_iff :
    ∫ t in a..b, iteratedDeriv 2 (naturalInterp n x fun i => f (x i)) t ^ 2
      = ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2
    ↔ EqOn f (naturalInterp n x fun i => f (x i)) (Icc a b) := by
  have hab := hx.lt_of_pos hn
  obtain ⟨hs, h0, h1⟩ := isCubicInterp_naturalInterp_and_end hx hn (f := f)
  rw [← intervalIntegral_iteratedDerivWithin_two_eq hx hn (contDiff_naturalInterp hx hn)
    fun _ y => y ^ 2]
  constructor
  · exact eqOn_of_integral_sq_deriv2_eq hx hn hf hs (Or.inl ⟨h0, h1⟩)
  · intro heq
    refine intervalIntegral_congr_Ioo hab.le fun t ht => ?_
    rw [Filter.EventuallyEq.iteratedDerivWithin_eq (x := t) (s := Icc a b) (n := 2)
      (f := naturalInterp n x fun i => f (x i)) (g := f)
      (eventually_nhdsWithin_of_forall fun u hu => (heq hu).symm)
      (heq (Ioo_subset_Icc_self ht)).symm]

/-- **The minimum-norm property for the clamped spline** ([quarteroni2000numerical] Exercise
8.11): for `f ∈ C²[a, b]` and `s_f` the cubic spline interpolating `f` at the nodes with
`s_f'(a) = f'(a)`, `s_f'(b) = f'(b)`, `∫_a^b s_f''² ≤ ∫_a^b f''²`. -/
theorem holladay_clamped :
    ∫ t in a..b, iteratedDeriv 2 (clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
        (derivWithin f (Icc a b) b)) t ^ 2
      ≤ ∫ t in a..b, iteratedDerivWithin 2 f (Icc a b) t ^ 2 := by
  obtain ⟨hs, h0, h1⟩ := isCubicInterp_clampedInterp_and_end hx hn (f := f)
  rw [← intervalIntegral_iteratedDerivWithin_two_eq hx hn (contDiff_clampedInterp hx hn _ _)
    fun _ y => y ^ 2]
  exact integral_sq_deriv2_le_of_end hx hn hf hs (Or.inr ⟨h0, h1⟩)

/-- **The clamped spline is the best `L²` approximation of `f''` by second derivatives of cubic
splines** ([quarteroni2000numerical] §8.6.1, the display after Property 8.2): for `f ∈ C²[a, b]`,
`s_f` its clamped interpolatory spline and any cubic spline `g` on the partition,
`∫_a^b (f'' - s_f'')² ≤ ∫_a^b (f'' - g'')²`. The cross term `∫ (f'' - s_f'') (s_f'' - g'')`
vanishes by Holladay's identity, whose boundary terms are killed by the clamped end conditions. -/
theorem integral_sq_sub_deriv2_clampedInterp_le {g : ℝ → ℝ} (hg : IsCubicSpline a b n x g) :
    ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
        - iteratedDerivWithin 2 (clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
            (derivWithin f (Icc a b) b)) (Icc a b) t) ^ 2
      ≤ ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
          - iteratedDerivWithin 2 g (Icc a b) t) ^ 2 := by
  have hab := hx.lt_of_pos hn
  obtain ⟨hs, h0, h1⟩ := isCubicInterp_clampedInterp_and_end hx hn (f := f)
  set sf := clampedInterp n x (fun i => f (x i)) (derivWithin f (Icc a b) a)
    (derivWithin f (Icc a b) b) with hsf
  have hF2c := continuousOn_iteratedDerivWithin_two hab hf
  have hS2c := continuousOn_iteratedDerivWithin_two hab hs.contDiffOn
  have hG2c := continuousOn_iteratedDerivWithin_two hab hg.contDiffOn
  have hint : ∀ u : ℝ → ℝ, ContinuousOn u (Icc a b) →
      IntervalIntegrable u MeasureTheory.volume a b :=
    fun u hu => hu.intervalIntegrable_of_Icc hab.le
  -- the two orthogonality identities
  have ho1 := integral_sub_deriv2_mul_deriv2_eq hx hn hf hs hs.toIsCubicSpline
  have ho2 := integral_sub_deriv2_mul_deriv2_eq hx hn hf hs hg
  rw [h0, h1, sub_self, sub_self, zero_mul, zero_mul, sub_zero] at ho1 ho2
  have hcross : ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
      - iteratedDerivWithin 2 sf (Icc a b) t)
      * (iteratedDerivWithin 2 sf (Icc a b) t - iteratedDerivWithin 2 g (Icc a b) t) = 0 := by
    rw [← sub_eq_zero.mpr (ho1.trans ho2.symm), ← intervalIntegral.integral_sub]
    · exact intervalIntegral.integral_congr fun t _ => by ring
    · exact hint _ ((hF2c.sub hS2c).mul hS2c)
    · exact hint _ ((hF2c.sub hS2c).mul hG2c)
  have hexp : ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
        - iteratedDerivWithin 2 g (Icc a b) t) ^ 2
      = (∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
            - iteratedDerivWithin 2 sf (Icc a b) t) ^ 2)
        + (∫ t in a..b, (iteratedDerivWithin 2 sf (Icc a b) t
            - iteratedDerivWithin 2 g (Icc a b) t) ^ 2)
        + 2 * ∫ t in a..b, (iteratedDerivWithin 2 f (Icc a b) t
            - iteratedDerivWithin 2 sf (Icc a b) t)
            * (iteratedDerivWithin 2 sf (Icc a b) t - iteratedDerivWithin 2 g (Icc a b) t) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add,
      ← intervalIntegral.integral_add]
    · exact intervalIntegral.integral_congr fun t _ => by ring
    · exact hint _ (((hF2c.sub hS2c).pow 2).add ((hS2c.sub hG2c).pow 2))
    · exact hint _ (continuousOn_const.mul ((hF2c.sub hS2c).mul (hS2c.sub hG2c)))
    · exact hint _ ((hF2c.sub hS2c).pow 2)
    · exact hint _ ((hS2c.sub hG2c).pow 2)
  rw [hexp, hcross, mul_zero, add_zero]
  have : 0 ≤ ∫ t in a..b, (iteratedDerivWithin 2 sf (Icc a b) t
      - iteratedDerivWithin 2 g (Icc a b) t) ^ 2 :=
    intervalIntegral.integral_nonneg hab.le fun t _ => sq_nonneg _
  linarith

end HolladayNamed

/-! ### Vector-valued data and affine equivariance

The interpolatory cubic spline of data in a real vector space `E` is built by the same formulas,
with the moments `E`-valued and the moment matrix acting through its entries. It is what the
parametric splines of [quarteroni2000numerical] §8.7 are made of, and its affine equivariance
(`cubicInterpVec_affine`) is the geometric invariance of the cumulative-length spline. -/

section Vec

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The panel cubic with `E`-valued data `P` and moments `M`. -/
noncomputable def panelCubicVec (x : ℕ → ℝ) (P M : ℕ → E) (i : ℕ) (t : ℝ) : E :=
  ((x i - t) ^ 3 / (6 * (x i - x (i - 1)))) • M (i - 1)
    + ((t - x (i - 1)) ^ 3 / (6 * (x i - x (i - 1)))) • M i
    + ((t - x (i - 1)) / (x i - x (i - 1))) • (P i - P (i - 1))
    - ((x i - x (i - 1)) / 6 * (t - x (i - 1))) • (M i - M (i - 1))
    + P (i - 1) - ((x i - x (i - 1)) ^ 2 / 6) • M (i - 1)

/-- The right-hand side of the moment system for `E`-valued data. -/
noncomputable def momentRhsVec (n : ℕ) (h : ℕ → ℝ) (P : ℕ → E) (d0 dn : E) : Fin (n + 1) → E :=
  fun i =>
    if (i : ℕ) = 0 then d0 else if (i : ℕ) = n then dn
    else (6 / (h i + h (i + 1))) • ((1 / h (i + 1)) • (P (i + 1) - P i)
      - (1 / h i) • (P i - P (i - 1)))

/-- The `E`-valued moment vector: the inverse of the moment matrix applied entrywise. -/
noncomputable def momentVecVec (n : ℕ) (x : ℕ → ℝ) (P : ℕ → E) (lam0 mun : ℝ) (d0 dn : E) :
    ℕ → E :=
  extendFin fun i : Fin (n + 1) => ∑ j, (momentMatrix n (panelLength x) lam0 mun)⁻¹ i j •
    momentRhsVec n (panelLength x) P d0 dn j

/-- **The interpolatory cubic spline of `E`-valued data** with a closure of type (8.48). -/
noncomputable def cubicInterpVec (n : ℕ) (x : ℕ → ℝ) (P : ℕ → E) (lam0 mun : ℝ) (d0 dn : E) :
    ℝ → E :=
  panelGlue n x (panelCubicVec x P (momentVecVec n x P lam0 mun d0 dn))

/-- For real data the vector-valued spline is the real one. -/
theorem cubicInterpVec_real (n : ℕ) (x f : ℕ → ℝ) (lam0 mun d0 dn : ℝ) :
    cubicInterpVec n x f lam0 mun d0 dn = cubicInterp n x f lam0 mun d0 dn := by
  have hM : momentVecVec n x f lam0 mun d0 dn = momentVec n x f lam0 mun d0 dn := by
    unfold momentVecVec momentVec
    congr 1
    funext i
    simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp only [momentRhsVec, momentRhs, smul_eq_mul]
    split_ifs <;> ring
  funext t
  simp only [cubicInterpVec, cubicInterp, cubicSplineFun, panelGlue, hM, panelCubicVec,
    panelCubic_apply, smul_eq_mul]
  ring

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- The right-hand side of the moment system is affinely equivariant: shifting the data by a
constant leaves it unchanged, and a linear map acts on it entrywise. -/
theorem momentRhsVec_affine (n : ℕ) (h : ℕ → ℝ) (P : ℕ → E) (d0 dn : E) (L : E →ₗ[ℝ] F) (c : F) :
    momentRhsVec n h (fun i => L (P i) + c) (L d0) (L dn)
      = fun i => L (momentRhsVec n h P d0 dn i) := by
  funext i
  simp only [momentRhsVec]
  split_ifs
  · rfl
  · rfl
  · simp only [map_smul, map_sub, add_sub_add_right_eq_sub]

/-- The moment vector is affinely equivariant. -/
theorem momentVecVec_affine (n : ℕ) (x : ℕ → ℝ) (P : ℕ → E) (lam0 mun : ℝ) (d0 dn : E)
    (L : E →ₗ[ℝ] F) (c : F) :
    momentVecVec n x (fun i => L (P i) + c) lam0 mun (L d0) (L dn)
      = fun i => L (momentVecVec n x P lam0 mun d0 dn i) := by
  funext i
  unfold momentVecVec
  rw [momentRhsVec_affine]
  rcases lt_or_ge i (n + 1) with hi | hi
  · rw [extendFin_of_lt _ hi, extendFin_of_lt _ hi, map_sum]
    simp only [map_smul]
  · rw [extendFin_of_le _ hi, extendFin_of_le _ hi, map_zero]

/-- **Affine equivariance of cubic spline interpolation** ([quarteroni2000numerical] §8.7, the
geometric invariance of the cumulative-length parametric spline): for an affine map
`Q = L + c` of the data, with the closure values transformed by the linear part `L`, the
interpolatory spline of `Q ∘ P` is `Q` of the interpolatory spline of `P`. -/
theorem cubicInterpVec_affine (n : ℕ) (x : ℕ → ℝ) (P : ℕ → E) (lam0 mun : ℝ) (d0 dn : E)
    (L : E →ₗ[ℝ] F) (c : F) (t : ℝ) :
    cubicInterpVec n x (fun i => L (P i) + c) lam0 mun (L d0) (L dn) t
      = L (cubicInterpVec n x P lam0 mun d0 dn t) + c := by
  simp only [cubicInterpVec, panelGlue, momentVecVec_affine, panelCubicVec, map_add, map_sub,
    map_smul, add_sub_add_right_eq_sub]
  abel

/-- The interpolatory spline of constant data with zero closure values is constant. -/
theorem cubicInterpVec_const (n : ℕ) (x : ℕ → ℝ) (lam0 mun : ℝ) (c : E) (t : ℝ) :
    cubicInterpVec n x (fun _ => c) lam0 mun 0 0 t = c := by
  have := cubicInterpVec_affine n x (fun _ : ℕ => (0 : E)) lam0 mun 0 0 (LinearMap.id) c t
  simp only [LinearMap.id_apply, zero_add, map_zero] at this
  rw [this]
  have hz : cubicInterpVec n x (fun _ : ℕ => (0 : E)) lam0 mun 0 0 t = 0 := by
    have h0 := cubicInterpVec_affine n x (fun _ : ℕ => (0 : E)) lam0 mun 0 0 (0 : E →ₗ[ℝ] E) 0 t
    simp only [LinearMap.zero_apply, add_zero, map_zero] at h0
    exact h0
  rw [hz, zero_add]

end Vec

/-- **Affine equivariance of real cubic spline interpolation**: for `Q y = l * y + c`, the
interpolatory spline of `Q ∘ f` with closure values `l * d0`, `l * dn` is `Q` of the spline of
`f`. -/
theorem cubicInterp_affine (n : ℕ) (x f : ℕ → ℝ) (lam0 mun d0 dn l c : ℝ) (t : ℝ) :
    cubicInterp n x (fun i => l * f i + c) lam0 mun (l * d0) (l * dn) t
      = l * cubicInterp n x f lam0 mun d0 dn t + c := by
  rw [← cubicInterpVec_real, ← cubicInterpVec_real]
  have := cubicInterpVec_affine n x f lam0 mun d0 dn (LinearMap.lsmul ℝ ℝ l) c t
  simpa using this

/-! ### The not-a-knot spline -/

/-- **Two cubics agreeing to third order at a point are equal.** -/
theorem eq_of_degree_le_three_of_deriv {p q : ℝ[X]} (hp : p.degree ≤ 3) (hq : q.degree ≤ 3) {c : ℝ}
    (h0 : p.eval c = q.eval c) (h1 : (derivative p).eval c = (derivative q).eval c)
    (h2 : (derivative (derivative p)).eval c = (derivative (derivative q)).eval c)
    (h3 : (derivative (derivative (derivative p))).eval c
      = (derivative (derivative (derivative q))).eval c) : p = q := by
  rw [← sub_eq_zero]
  set r := p - q with hr
  have hrdeg : r.natDegree ≤ 3 :=
    natDegree_le_of_degree_le ((degree_sub_le _ _).trans (max_le hp hq))
  -- a polynomial of `natDegree 0` vanishing at `c` is zero
  have key : ∀ u : ℝ[X], u.natDegree = 0 → u.eval c = 0 → u = 0 := fun u hu hc => by
    rw [eq_C_of_natDegree_eq_zero hu] at hc ⊢
    rw [eval_C] at hc
    rw [hc, C_0]
  have e3 : derivative (derivative (derivative r)) = 0 := by
    refine key _ ?_ (by simp [hr, derivative_sub, eval_sub, h3])
    have h1' : (derivative r).natDegree ≤ 2 := (natDegree_derivative_le r).trans (by omega)
    have h2' : (derivative (derivative r)).natDegree ≤ 1 :=
      (natDegree_derivative_le _).trans (by omega)
    have h3' : (derivative (derivative (derivative r))).natDegree ≤ 0 :=
      (natDegree_derivative_le _).trans (by omega)
    omega
  have e2 : derivative (derivative r) = 0 :=
    key _ (derivative_eq_zero.mp e3) (by simp [hr, derivative_sub, eval_sub, h2])
  have e1 : derivative r = 0 := key _ (derivative_eq_zero.mp e2) (by simp [hr, eval_sub, h1])
  exact key _ (derivative_eq_zero.mp e1) (by simp [hr, eval_sub, h0])

/-- **A cubic spline is a single cubic across the node `x i` iff its third derivative has no jump
there**: `(M_i - M_{i-1})/h_i = (M_{i+1} - M_i)/h_{i+1}` in terms of the moments. -/
theorem IsCubicSpline.exists_eqOn_Icc_two_iff (hx : IsPartition a b n x) {s : ℝ → ℝ}
    (hs : IsCubicSpline a b n x s) {i : ℕ} (hi1 : 1 ≤ i) (hin : i < n) :
    (∃ p : ℝ[X], p.degree ≤ 3 ∧ EqOn s p.eval (Icc (x (i - 1)) (x (i + 1)))) ↔
      (moment a b x s i - moment a b x s (i - 1)) / panelLength x i
        = (moment a b x s (i + 1) - moment a b x s i) / panelLength x (i + 1) := by
  set F : ℕ → ℝ := fun j => s (x j) with hF
  set M : ℕ → ℝ := moment a b x s with hM
  have h1 : x (i - 1) < x i := hx.lt (Nat.sub_one_lt_of_le hi1 le_rfl) hin.le
  have h2 : x i < x (i + 1) := hx.step i hin
  have hp1 := hs.eqOn_panelCubic hx hi1 hin.le
  have hp2 := hs.eqOn_panelCubic hx (i := i + 1) (by omega) hin
  simp only [add_tsub_cancel_right] at hp2
  have hd3 : (derivative (derivative (derivative (panelCubicPoly x F M i)))).eval (x i)
      = (M i - M (i - 1)) / panelLength x i := panelCubicD3_apply x F M h1 (x i)
  have hd3' : (derivative (derivative (derivative (panelCubicPoly x F M (i + 1))))).eval (x i)
      = (M (i + 1) - M i) / panelLength x (i + 1) := by
    have := panelCubicD3_apply x F M (i := i + 1) (by simpa using h2) (x i)
    rw [show i + 1 - 1 = i by omega] at this
    exact this
  constructor
  · rintro ⟨p, -, hpe⟩
    have hq1 : p = panelCubicPoly x F M i := by
      refine Polynomial.eq_of_infinite_eval_eq _ _ ((Icc_infinite h1).mono fun t ht => ?_)
      exact (hpe (Icc_subset_Icc le_rfl h2.le ht)).symm.trans (hp1 ht)
    have hq2 : p = panelCubicPoly x F M (i + 1) := by
      refine Polynomial.eq_of_infinite_eval_eq _ _ ((Icc_infinite h2).mono fun t ht => ?_)
      exact (hpe (Icc_subset_Icc h1.le le_rfl ht)).symm.trans (hp2 ht)
    rw [← hd3, ← hd3', ← hq1, ← hq2]
  · intro heq
    have hmom : IsMomentEq x F M i :=
      moment_eq_of_contDiffOn hx hs.contDiffOn (fun j hj1 hjn => hs.eqOn_panelCubic hx hj1 hjn)
        hi1 hin
    have hq : panelCubicPoly x F M i = panelCubicPoly x F M (i + 1) := by
      refine eq_of_degree_le_three_of_deriv (degree_panelCubicPoly_le _ _ _ _)
        (degree_panelCubicPoly_le _ _ _ _) (c := x i) ?_ ?_ ?_ ?_
      · exact (panelCubic_right h1).trans (panelCubic_left_succ h2).symm
      · exact (isMomentEq_iff h1 h2).mp hmom
      · exact (panelCubicD2_right h1).trans (panelCubicD2_left_succ h2).symm
      · rw [hd3, hd3']; exact heq
    refine ⟨panelCubicPoly x F M i, degree_panelCubicPoly_le _ _ _ _, ?_⟩
    rw [← Icc_union_Icc_eq_Icc h1.le h2.le]
    intro t ht
    rcases ht with ht | ht
    · exact hp1 ht
    · rw [hp2 ht, hq]
      rfl

/-- **The not-a-knot closure**: the spline is a single cubic on `[x_0, x_2]` and on
`[x_{n-2}, x_n]`, i.e. its third derivative is continuous at `x_1` and at `x_{n-1}`
([quarteroni2000numerical] §8.6.1). -/
def IsNotAKnot (n : ℕ) (x : ℕ → ℝ) (s : ℝ → ℝ) : Prop :=
  (∃ p : ℝ[X], p.degree ≤ 3 ∧ EqOn s p.eval (Icc (x 0) (x 2))) ∧
    ∃ q : ℝ[X], q.degree ≤ 3 ∧ EqOn s q.eval (Icc (x (n - 2)) (x n))

section NotAKnot

variable (hx : IsPartition a b n x) (hn : 3 ≤ n) {f : ℕ → ℝ}
include hx hn

/-- The not-a-knot closure of an interpolatory cubic spline, in terms of its moments:
`M_0 = (1 + h_1/h_2) M_1 - (h_1/h_2) M_2` and `M_n = M_{n-1} + (h_n/h_{n-1})(M_{n-1} - M_{n-2})`. -/
theorem IsCubicInterp.isNotAKnot_iff {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s) :
    IsNotAKnot n x s ↔
      moment a b x s 0 = (1 + panelLength x 1 / panelLength x 2) * moment a b x s 1
        - panelLength x 1 / panelLength x 2 * moment a b x s 2 ∧
      moment a b x s n = moment a b x s (n - 1) + panelLength x n / panelLength x (n - 1)
        * (moment a b x s (n - 1) - moment a b x s (n - 2)) := by
  have h1 := hx.panelLength_pos le_rfl (by omega)
  have h2 := hx.panelLength_pos (i := 2) (by omega) (by omega)
  have hn1 := hx.panelLength_pos (i := n - 1) (by omega) (by omega)
  have hnn := hx.panelLength_pos (i := n) (by omega) le_rfl
  have hA := hs.toIsCubicSpline.exists_eqOn_Icc_two_iff hx (i := 1) le_rfl (by omega)
  have hB := hs.toIsCubicSpline.exists_eqOn_Icc_two_iff hx (i := n - 1) (by omega) (by omega)
  simp only [Nat.sub_self, show n - 1 + 1 = n by omega, show n - 1 - 1 = n - 2 by omega] at hA hB
  rw [IsNotAKnot, hA, hB]
  constructor
  · rintro ⟨hA', hB'⟩
    rw [div_eq_iff h1.ne'] at hA'
    rw [eq_comm, div_eq_iff hnn.ne'] at hB'
    constructor
    · have : moment a b x s 0 = moment a b x s 1
          - (moment a b x s 2 - moment a b x s 1) / panelLength x 2 * panelLength x 1 := by
        linarith
      rw [this]; ring
    · have : moment a b x s n = moment a b x s (n - 1)
          + (moment a b x s (n - 1) - moment a b x s (n - 2)) / panelLength x (n - 1)
            * panelLength x n := by
        linarith
      rw [this]; ring
  · rintro ⟨hA', hB'⟩
    constructor
    · rw [hA', div_eq_div_iff h1.ne' h2.ne']; field_simp; ring
    · rw [hB', div_eq_div_iff hn1.ne' hnn.ne']; field_simp; ring

end NotAKnot

section NotAKnotExistence

variable {m : ℕ} (hx : IsPartition a b (m + 2) x) (hm : 1 ≤ m) {f : ℕ → ℝ}
include hx hm

omit hx hm in
/-- The moment equation depends only on the moments at the node and its two neighbours. -/
theorem isMomentEq_congr {M N : ℕ → ℝ} {i : ℕ} (h0 : M (i - 1) = N (i - 1)) (h1 : M i = N i)
    (h2 : M (i + 1) = N (i + 1)) : IsMomentEq x f M i ↔ IsMomentEq x f N i := by
  simp only [IsMomentEq, h0, h1, h2]

omit hx hm in
/-- The interior moment equation of the sub-partition `x_1 < ⋯ < x_{n-1}` at its node `j` is the
moment equation of the partition at the node `j + 1`. -/
theorem isMomentEq_shift {M : ℕ → ℝ} {j : ℕ} (hj : 1 ≤ j) :
    IsMomentEq (fun i => x (i + 1)) (fun i => f (i + 1)) (fun i => M (i + 1)) j ↔
      IsMomentEq x f M (j + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [IsMomentEq, panelLength, add_tsub_cancel_right]

/-- **The reduced system of the not-a-knot spline.** Once `M_0` and `M_n` are eliminated through
the not-a-knot conditions, the interior moment equations at `x_1, …, x_{n-1}` are the moment
system of the sub-partition `x_1 < ⋯ < x_{n-1}` with the closure
`λ_0' = 2 (h_2 - h_1)/(2 h_2 + h_1)`, `μ_n' = 2 (h_{n-1} - h_n)/(2 h_{n-1} + h_n)`,
`d_0' = (2 h_2/(2 h_2 + h_1)) d_1`, `d_n' = (2 h_{n-1}/(2 h_{n-1} + h_n)) d_{n-1}`, which is
strictly diagonally dominant. -/
theorem notAKnot_reduced_iff (M : ℕ → ℝ)
    (hM0 : M 0 = (1 + panelLength x 1 / panelLength x 2) * M 1
      - panelLength x 1 / panelLength x 2 * M 2)
    (hMn : M (m + 2) = M (m + 1)
      + panelLength x (m + 2) / panelLength x (m + 1) * (M (m + 1) - M m)) :
    (momentMatrix m (panelLength fun i => x (i + 1))
        (2 * (panelLength x 2 - panelLength x 1) / (2 * panelLength x 2 + panelLength x 1))
        (2 * (panelLength x (m + 1) - panelLength x (m + 2))
          / (2 * panelLength x (m + 1) + panelLength x (m + 2)))).mulVec
      (fun j : Fin (m + 1) => M (j + 1))
    = momentRhs m (panelLength fun i => x (i + 1)) (fun i => f (i + 1))
        (2 * panelLength x 2 / (2 * panelLength x 2 + panelLength x 1)
          * (6 / (panelLength x 1 + panelLength x 2)
            * ((f 2 - f 1) / panelLength x 2 - (f 1 - f 0) / panelLength x 1)))
        (2 * panelLength x (m + 1) / (2 * panelLength x (m + 1) + panelLength x (m + 2))
          * (6 / (panelLength x (m + 1) + panelLength x (m + 2))
            * ((f (m + 2) - f (m + 1)) / panelLength x (m + 2)
              - (f (m + 1) - f m) / panelLength x (m + 1))))
    ↔ ∀ i, 1 ≤ i → i < m + 2 → IsMomentEq x f M i := by
  have hx' : IsPartition (x 1) (x (m + 1)) m fun i => x (i + 1) :=
    ⟨fun j hj => hx.step (j + 1) (by omega), rfl, rfl⟩
  have h1 := hx.panelLength_pos le_rfl (by omega)
  have h2 := hx.panelLength_pos (i := 2) (by omega) (by omega)
  have hn1 := hx.panelLength_pos (i := m + 1) (by omega) (by omega)
  have hnn := hx.panelLength_pos (i := m + 2) (by omega) le_rfl
  rw [momentMatrix_mulVec_eq_iff hx' hm]
  have hext : ∀ j ≤ m, extendFin (fun j : Fin (m + 1) => M (j + 1)) j = M (j + 1) := fun j hj =>
    extendFin_of_lt _ (by omega)
  -- the two modified rows
  have hrow0 : 2 * M 1 + 2 * (panelLength x 2 - panelLength x 1)
      / (2 * panelLength x 2 + panelLength x 1) * M 2
      = 2 * panelLength x 2 / (2 * panelLength x 2 + panelLength x 1)
        * (6 / (panelLength x 1 + panelLength x 2)
          * ((f 2 - f 1) / panelLength x 2 - (f 1 - f 0) / panelLength x 1))
      ↔ IsMomentEq x f M 1 := by
    have hc : 2 * panelLength x 2 / (2 * panelLength x 2 + panelLength x 1) ≠ 0 := by positivity
    simp only [IsMomentEq, Nat.sub_self, hM0]
    rw [← sub_eq_zero, ← sub_eq_zero (a := _ / _ * _ + _ + _)]
    have key : panelLength x 1 / (panelLength x 1 + panelLength x (1 + 1))
        * ((1 + panelLength x 1 / panelLength x 2) * M 1 - panelLength x 1 / panelLength x 2 * M 2)
        + 2 * M 1 + panelLength x (1 + 1) / (panelLength x 1 + panelLength x (1 + 1)) * M (1 + 1)
        - 6 / (panelLength x 1 + panelLength x (1 + 1))
          * ((f (1 + 1) - f 1) / panelLength x (1 + 1) - (f 1 - f (1 - 1)) / panelLength x 1)
        = ((2 * panelLength x 2 + panelLength x 1) / (2 * panelLength x 2))
          * (2 * M 1 + 2 * (panelLength x 2 - panelLength x 1)
              / (2 * panelLength x 2 + panelLength x 1) * M 2
            - 2 * panelLength x 2 / (2 * panelLength x 2 + panelLength x 1)
              * (6 / (panelLength x 1 + panelLength x 2)
                * ((f 2 - f 1) / panelLength x 2 - (f 1 - f 0) / panelLength x 1))) := by
      simp only [Nat.reduceAdd, Nat.sub_self]
      field_simp
      ring
    rw [key, mul_eq_zero, or_iff_right (by positivity)]
  have hrowm : 2 * (panelLength x (m + 1) - panelLength x (m + 2))
      / (2 * panelLength x (m + 1) + panelLength x (m + 2)) * M m + 2 * M (m + 1)
      = 2 * panelLength x (m + 1) / (2 * panelLength x (m + 1) + panelLength x (m + 2))
        * (6 / (panelLength x (m + 1) + panelLength x (m + 2))
          * ((f (m + 2) - f (m + 1)) / panelLength x (m + 2)
            - (f (m + 1) - f m) / panelLength x (m + 1)))
      ↔ IsMomentEq x f M (m + 1) := by
    simp only [IsMomentEq, add_tsub_cancel_right, hMn]
    rw [← sub_eq_zero, ← sub_eq_zero (a := _ / _ * _ + _ + _)]
    have key : panelLength x (m + 1) / (panelLength x (m + 1) + panelLength x (m + 1 + 1)) * M m
        + 2 * M (m + 1) + panelLength x (m + 1 + 1)
          / (panelLength x (m + 1) + panelLength x (m + 1 + 1))
          * (M (m + 1) + panelLength x (m + 2) / panelLength x (m + 1) * (M (m + 1) - M m))
        - 6 / (panelLength x (m + 1) + panelLength x (m + 1 + 1))
          * ((f (m + 1 + 1) - f (m + 1)) / panelLength x (m + 1 + 1)
            - (f (m + 1) - f m) / panelLength x (m + 1))
        = ((2 * panelLength x (m + 1) + panelLength x (m + 2)) / (2 * panelLength x (m + 1)))
          * (2 * (panelLength x (m + 1) - panelLength x (m + 2))
              / (2 * panelLength x (m + 1) + panelLength x (m + 2)) * M m + 2 * M (m + 1)
            - 2 * panelLength x (m + 1) / (2 * panelLength x (m + 1) + panelLength x (m + 2))
              * (6 / (panelLength x (m + 1) + panelLength x (m + 2))
                * ((f (m + 2) - f (m + 1)) / panelLength x (m + 2)
                  - (f (m + 1) - f m) / panelLength x (m + 1)))) := by
      simp only [show m + 1 + 1 = m + 2 by omega]
      field_simp
      ring
    rw [key, mul_eq_zero, or_iff_right (by positivity)]
  constructor
  · rintro ⟨hint, h0, hN⟩ i hi1 hin
    rcases Nat.lt_or_ge i 2 with hi | hi
    · obtain rfl : i = 1 := by omega
      rw [hext 0 (by omega), hext 1 hm] at h0
      exact hrow0.mp h0
    rcases Nat.lt_or_ge i (m + 1) with hi' | hi'
    · have := hint (i - 1) (by omega) (by omega)
      rw [isMomentEq_congr (N := fun j => M (j + 1)) (hext _ (by omega)) (hext _ (by omega))
        (hext _ (by omega)), isMomentEq_shift (by omega), show i - 1 + 1 = i by omega] at this
      exact this
    · obtain rfl : i = m + 1 := by omega
      rw [hext (m - 1) (by omega), hext m le_rfl, show m - 1 + 1 = m by omega] at hN
      exact hrowm.mp hN
  · intro hint
    refine ⟨fun j hj1 hjm => ?_, ?_, ?_⟩
    · rw [isMomentEq_congr (N := fun j => M (j + 1)) (hext _ (by omega)) (hext _ (by omega))
        (hext _ (by omega)), isMomentEq_shift hj1]
      exact hint (j + 1) (by omega) (by omega)
    · rw [hext 0 (by omega), hext 1 hm]
      exact hrow0.mpr (hint 1 le_rfl (by omega))
    · rw [hext (m - 1) (by omega), hext m le_rfl, show m - 1 + 1 = m by omega]
      exact hrowm.mpr (hint (m + 1) (by omega) (by omega))

/-- The reduced not-a-knot matrix is invertible: its closure parameters satisfy
`|λ_0'|, |μ_n'| < 2`. -/
theorem isUnit_notAKnot_reduced :
    IsUnit (momentMatrix m (panelLength fun i => x (i + 1))
      (2 * (panelLength x 2 - panelLength x 1) / (2 * panelLength x 2 + panelLength x 1))
      (2 * (panelLength x (m + 1) - panelLength x (m + 2))
        / (2 * panelLength x (m + 1) + panelLength x (m + 2)))) := by
  have h1 := hx.panelLength_pos le_rfl (by omega)
  have h2 := hx.panelLength_pos (i := 2) (by omega) (by omega)
  have hn1 := hx.panelLength_pos (i := m + 1) (by omega) (by omega)
  have hnn := hx.panelLength_pos (i := m + 2) (by omega) le_rfl
  refine (isStrictDiagDominant_momentMatrix_of_abs_lt (fun i hi1 him => ?_) ?_ ?_).isUnit
  · simp only [panelLength]
    rw [show i - 1 + 1 = i by omega]
    exact sub_pos.mpr (hx.step i (by omega))
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 * panelLength x 2 + panelLength x 1 by positivity),
      div_lt_iff₀ (by positivity), abs_mul, abs_two]
    have : |panelLength x 2 - panelLength x 1| < 2 * panelLength x 2 + panelLength x 1 :=
      abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    linarith
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 * panelLength x (m + 1) + panelLength x (m + 2) by
      positivity), div_lt_iff₀ (by positivity), abs_mul, abs_two]
    have : |panelLength x (m + 1) - panelLength x (m + 2)|
        < 2 * panelLength x (m + 1) + panelLength x (m + 2) :=
      abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    linarith

/-- Existence and uniqueness of the not-a-knot spline, for `n = m + 2` panels with `1 ≤ m`. -/
theorem existsUnique_isCubicInterp_notAKnot_aux (f : ℕ → ℝ) :
    (∃ s, IsCubicInterp a b (m + 2) x f s ∧ IsNotAKnot (m + 2) x s) ∧
      ∀ s₁ s₂, IsCubicInterp a b (m + 2) x f s₁ → IsNotAKnot (m + 2) x s₁ →
        IsCubicInterp a b (m + 2) x f s₂ → IsNotAKnot (m + 2) x s₂ → EqOn s₁ s₂ (Icc a b) := by
  have hn : 3 ≤ m + 2 := by omega
  have hn' : 1 ≤ m + 2 := by omega
  have hab := hx.lt_of_pos hn'
  have hA := isUnit_notAKnot_reduced hx hm
  set A := momentMatrix m (panelLength fun i => x (i + 1))
    (2 * (panelLength x 2 - panelLength x 1) / (2 * panelLength x 2 + panelLength x 1))
    (2 * (panelLength x (m + 1) - panelLength x (m + 2))
      / (2 * panelLength x (m + 1) + panelLength x (m + 2))) with hAdef
  set rhs := momentRhs m (panelLength fun i => x (i + 1)) (fun i => f (i + 1))
    (2 * panelLength x 2 / (2 * panelLength x 2 + panelLength x 1)
      * (6 / (panelLength x 1 + panelLength x 2)
        * ((f 2 - f 1) / panelLength x 2 - (f 1 - f 0) / panelLength x 1)))
    (2 * panelLength x (m + 1) / (2 * panelLength x (m + 1) + panelLength x (m + 2))
      * (6 / (panelLength x (m + 1) + panelLength x (m + 2))
        * ((f (m + 2) - f (m + 1)) / panelLength x (m + 2)
          - (f (m + 1) - f m) / panelLength x (m + 1)))) with hrhsdef
  -- the not-a-knot conditions in moment form, with `n - 1 = m + 1` and `n - 2 = m`
  have hnak : ∀ s, IsCubicInterp a b (m + 2) x f s → (IsNotAKnot (m + 2) x s ↔
      moment a b x s 0 = (1 + panelLength x 1 / panelLength x 2) * moment a b x s 1
        - panelLength x 1 / panelLength x 2 * moment a b x s 2 ∧
      moment a b x s (m + 2) = moment a b x s (m + 1)
        + panelLength x (m + 2) / panelLength x (m + 1)
          * (moment a b x s (m + 1) - moment a b x s m)) := fun s hs => by
    have := hs.isNotAKnot_iff hx hn
    rwa [show m + 2 - 1 = m + 1 from rfl, show m + 2 - 2 = m from rfl] at this
  constructor
  · -- existence
    set N : Fin (m + 1) → ℝ := A⁻¹.mulVec rhs with hNdef
    set M : ℕ → ℝ := fun i => if i = 0 then
        (1 + panelLength x 1 / panelLength x 2) * extendFin N 0
          - panelLength x 1 / panelLength x 2 * extendFin N 1
      else if i = m + 2 then
        extendFin N m + panelLength x (m + 2) / panelLength x (m + 1)
          * (extendFin N m - extendFin N (m - 1))
      else extendFin N (i - 1) with hMdef
    have hMi : ∀ i, 1 ≤ i → i ≤ m + 1 → M i = extendFin N (i - 1) := fun i hi1 hi2 => by
      simp only [hMdef, ite_eq_right (show i ≠ 0 by omega), ite_eq_right (show i ≠ m + 2 by omega)]
    have hM0 : M 0 = (1 + panelLength x 1 / panelLength x 2) * M 1
        - panelLength x 1 / panelLength x 2 * M 2 := by
      rw [hMi 1 le_rfl (by omega), hMi 2 (by omega) (by omega)]
      simp only [hMdef, ↓reduceIte]
    have hMn : M (m + 2) = M (m + 1)
        + panelLength x (m + 2) / panelLength x (m + 1) * (M (m + 1) - M m) := by
      rw [hMi (m + 1) (by omega) le_rfl, hMi m hm (by omega)]
      simp only [hMdef, ite_eq_right (show m + 2 ≠ 0 by omega), ↓reduceIte, add_tsub_cancel_right]
    have hN : (fun j : Fin (m + 1) => M (j + 1)) = N := funext fun j => by
      rw [hMi (j + 1) (by omega) (by have := j.2; omega), add_tsub_cancel_right, extendFin_val]
    have hsolve : A.mulVec N = rhs := by
      rw [hNdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hA), Matrix.one_mulVec]
    have hint : ∀ i, 1 ≤ i → i < m + 2 → IsMomentEq x f M i :=
      (notAKnot_reduced_iff hx hm M hM0 hMn).mp (by rw [hN]; exact hsolve)
    set s := cubicSplineFun (m + 2) x f M with hsdef
    have hs : IsCubicInterp a b (m + 2) x f s :=
      ⟨⟨contDiffOn_cubicSplineFun hx hn' hint, fun i hi1 hin =>
        ⟨panelCubicPoly x f M i, degree_panelCubicPoly_le _ _ _ _, cubicSplineFun_eqOn hx hi1 hin⟩⟩,
        fun i hi => cubicSplineFun_apply_node hx hn' hi⟩
    have hmom : ∀ i ≤ m + 2, moment a b x s i = M i := fun i hi => by
      rw [moment_eq_iteratedDeriv hab (contDiff_cubicSplineFun hx hn' hint)
        ⟨hx.left_le hi, hx.le_right hi⟩, iteratedDeriv_two_cubicSplineFun_node hx hn' hint hi]
    refine ⟨s, hs, (hnak s hs).mpr ⟨?_, ?_⟩⟩
    · rw [hmom 0 (by omega), hmom 1 (by omega), hmom 2 (by omega)]; exact hM0
    · rw [hmom (m + 2) le_rfl, hmom (m + 1) (by omega), hmom m (by omega)]; exact hMn
  · -- uniqueness
    intro s₁ s₂ h₁ hk₁ h₂ hk₂
    obtain ⟨hM0₁, hMn₁⟩ := (hnak s₁ h₁).mp hk₁
    obtain ⟨hM0₂, hMn₂⟩ := (hnak s₂ h₂).mp hk₂
    have e₁ := (notAKnot_reduced_iff hx hm (moment a b x s₁) hM0₁ hMn₁).mpr
      fun i hi1 hin => h₁.isMomentEq hx hi1 hin
    have e₂ := (notAKnot_reduced_iff hx hm (moment a b x s₂) hM0₂ hMn₂).mpr
      fun i hi1 hin => h₂.isMomentEq hx hi1 hin
    have hNeq : (fun j : Fin (m + 1) => moment a b x s₁ (j + 1))
        = fun j : Fin (m + 1) => moment a b x s₂ (j + 1) :=
      Matrix.mulVec_injective_iff_isUnit.mpr hA (e₁.trans e₂.symm)
    have hmid : ∀ i, 1 ≤ i → i ≤ m + 1 → moment a b x s₁ i = moment a b x s₂ i :=
        fun i hi1 hi2 => by
      have := congrFun hNeq (⟨i - 1, by omega⟩ : Fin (m + 1))
      simpa only [show i - 1 + 1 = i by omega] using this
    have hall : ∀ i ≤ m + 2, moment a b x s₁ i = moment a b x s₂ i := fun i hi => by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hM0₁, hM0₂, hmid 1 le_rfl (by omega), hmid 2 (by omega) (by omega)]
      rcases Nat.lt_or_ge i (m + 2) with hi' | hi'
      · exact hmid i hi0 (by omega)
      · obtain rfl : i = m + 2 := by omega
        rw [hMn₁, hMn₂, hmid (m + 1) (by omega) le_rfl, hmid m hm (by omega)]
    exact (h₁.eqOn_cubicSplineFun hx hn').trans
      ((cubicSplineFun_eqOn_of_moment_eq hx hn' hall).trans (h₂.eqOn_cubicSplineFun hx hn').symm)

end NotAKnotExistence

/-- **Existence and uniqueness of the not-a-knot cubic spline** ([quarteroni2000numerical] §8.6.1,
the closure "continuity of `s'''` at `x_1` and `x_{n-1}`"): for `n ≥ 3` panels there is exactly
one interpolatory cubic spline of the data whose cubic pieces coincide on the first two and on the
last two panels. Eliminating `M_0` and `M_n` through the not-a-knot conditions turns the moment
system into the strictly diagonally dominant reduced system `notAKnot_reduced_iff`. For `n = 2`
the two conditions coincide and the spline is not unique, which is why `3 ≤ n` is needed. -/
theorem existsUnique_isCubicInterp_notAKnot (hx : IsPartition a b n x) (hn : 3 ≤ n) (f : ℕ → ℝ) :
    (∃ s, IsCubicInterp a b n x f s ∧ IsNotAKnot n x s) ∧
      ∀ s₁ s₂, IsCubicInterp a b n x f s₁ → IsNotAKnot n x s₁ →
        IsCubicInterp a b n x f s₂ → IsNotAKnot n x s₂ → EqOn s₁ s₂ (Icc a b) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact existsUnique_isCubicInterp_notAKnot_aux hx (by omega) f

/-! ### The periodic spline

The periodic closure `s'(a) = s'(b)`, `s''(a) = s''(b)` identifies the moments `M_0 = M_n` and adds
the continuity of `s'` across `a = b` as an `n`-th equation; the system is cyclic, indices being
read modulo `n` with `h_0 := h_n`. -/

/-- The cyclic index: `cyc n i = i` for `i ≠ 0` and `cyc n 0 = n`, so that `h (cyc n i)` is the
length of the panel *before* the node `x i` on the circle. -/
def cyc (n i : ℕ) : ℕ := if i = 0 then n else i

/-- **The cyclic moment matrix** of the periodic spline: row `i` (`0 ≤ i < n`) has `2` on the
diagonal, `λ_i = h_{i+1}/(h_i + h_{i+1})` in the column `(i + 1) mod n` and
`μ_i = h_i/(h_i + h_{i+1})` in the column `i - 1` (`n - 1` for `i = 0`), with `h_0 := h_n`. When
`n = 2` the two off-diagonal entries land in the same column and add up. -/
noncomputable def periodicMomentMatrix (n : ℕ) (h : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    (if j = i then 2 else 0)
      + (if (j : ℕ) = (i + 1) % n then h (i + 1) / (h (cyc n i) + h (i + 1)) else 0)
      + (if (j : ℕ) = cyc n i - 1 then h (cyc n i) / (h (cyc n i) + h (i + 1)) else 0)

/-- **The right-hand side of the cyclic moment system**: `d_i` as in (8.47) for `1 ≤ i < n`, and
`d_0 = (6/(h_n + h_1)) ((f_1 - f_0)/h_1 - (f_n - f_{n-1})/h_n)`, the continuity of `s'` across
`a = b`. -/
noncomputable def periodicMomentRhs (n : ℕ) (h f : ℕ → ℝ) : Fin n → ℝ :=
  fun i => 6 / (h (cyc n i) + h (i + 1)) * ((f (i + 1) - f i) / h (i + 1)
    - (f (cyc n i) - f (cyc n i - 1)) / h (cyc n i))

/-- A sum over `Fin n` of a term supported at the index `k < n`. -/
theorem sum_ite_val_eq_mul' {n : ℕ} (c : ℝ) (v : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    ∑ j : Fin n, (if (j : ℕ) = k then c else 0) * v j = c * v ⟨k, hk⟩ := by
  rw [Finset.sum_eq_single ⟨k, hk⟩ (fun j _ hj => by
    rw [ite_eq_right, zero_mul]; intro h; exact hj (Fin.ext h))
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]

section Periodic

variable {h f : ℕ → ℝ}

/-- The cyclic index and its predecessor lie below `n` for `i < n`, `1 ≤ n`. -/
theorem cyc_sub_one_lt {i : ℕ} (hn : 1 ≤ n) (hi : i < n) : cyc n i - 1 < n := by
  unfold cyc; split_ifs <;> omega

/-- The cyclic moment matrix applied to a vector: `(A v)_i = 2 v_i + λ_i v_{i+1} + μ_i v_{i-1}`,
indices modulo `n`. -/
theorem periodicMomentMatrix_mulVec_apply (hn : 1 ≤ n) (v : Fin n → ℝ) (i : Fin n) :
    (periodicMomentMatrix n h).mulVec v i
      = 2 * v i + h (i + 1) / (h (cyc n i) + h (i + 1)) * v ⟨(i + 1) % n, Nat.mod_lt _ hn⟩
        + h (cyc n i) / (h (cyc n i) + h (i + 1)) * v ⟨cyc n i - 1, cyc_sub_one_lt hn i.2⟩ := by
  simp only [Matrix.mulVec, dotProduct, periodicMomentMatrix, Matrix.of_apply, add_mul,
    Finset.sum_add_distrib]
  rw [sum_ite_val_eq_mul' _ _ (Nat.mod_lt _ hn), sum_ite_val_eq_mul' _ _ (cyc_sub_one_lt hn i.2),
    Finset.sum_eq_single i (fun j _ hj => by rw [ite_eq_right hj, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]

/-- The cyclic moment matrix is strictly diagonally dominant for positive panel lengths: each
off-diagonal row sum is at most `λ_i + μ_i = 1`. -/
theorem isStrictDiagDominant_periodicMomentMatrix (hn2 : 2 ≤ n)
    (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i) : (periodicMomentMatrix n h).IsStrictDiagDominant := by
  have hn : 1 ≤ n := by omega
  intro i
  have hi := i.2
  have hc1 : 0 < h (cyc n i) := hh (cyc n i) (by unfold cyc; split_ifs <;> omega)
    (by unfold cyc; split_ifs <;> omega)
  have hc2 : 0 < h (i + 1) := hh (i + 1) (by omega) (by omega)
  have hlam : 0 ≤ h (i + 1) / (h (cyc n i) + h (i + 1)) := by positivity
  have hmu : 0 ≤ h (cyc n i) / (h (cyc n i) + h (i + 1)) := by positivity
  have hii : ‖periodicMomentMatrix n h i i‖ = 2 := by
    have h1 : ¬ ((i : ℕ) = (i + 1) % n) := by
      intro h
      rcases Nat.lt_or_ge ((i : ℕ) + 1) n with hi' | hi'
      · rw [Nat.mod_eq_of_lt hi'] at h; omega
      · have : (i : ℕ) + 1 = n := by omega
        rw [this, Nat.mod_self] at h; omega
    have h2 : ¬ ((i : ℕ) = cyc n i - 1) := by unfold cyc; split_ifs <;> omega
    simp [periodicMomentMatrix, h1, h2]
  rw [hii]
  calc ∑ j ∈ Finset.univ.erase i, ‖periodicMomentMatrix n h i j‖
      ≤ ∑ j ∈ Finset.univ.erase i, ((if (j : ℕ) = (i + 1) % n then
            h (i + 1) / (h (cyc n i) + h (i + 1)) else 0)
          + (if (j : ℕ) = cyc n i - 1 then h (cyc n i) / (h (cyc n i) + h (i + 1)) else 0)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        rw [periodicMomentMatrix, Matrix.of_apply, ite_eq_right hji, zero_add, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg (by split_ifs <;> simp [hlam]) (by split_ifs <;> simp [hmu]))]
    _ ≤ ∑ j : Fin n, ((if (j : ℕ) = (i + 1) % n then
            h (i + 1) / (h (cyc n i) + h (i + 1)) else 0)
          + (if (j : ℕ) = cyc n i - 1 then h (cyc n i) / (h (cyc n i) + h (i + 1)) else 0)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ =>
          add_nonneg (by split_ifs <;> simp [hlam]) (by split_ifs <;> simp [hmu])
    _ = h (i + 1) / (h (cyc n i) + h (i + 1)) + h (cyc n i) / (h (cyc n i) + h (i + 1)) := by
        rw [Finset.sum_add_distrib]
        have e1 := sum_ite_val_eq_mul' (h (i + 1) / (h (cyc n i) + h (i + 1))) (fun _ => (1 : ℝ))
          (Nat.mod_lt (i + 1) hn)
        have e2 := sum_ite_val_eq_mul' (h (cyc n i) / (h (cyc n i) + h (i + 1))) (fun _ => (1 : ℝ))
          (cyc_sub_one_lt hn i.2)
        simp only [mul_one] at e1 e2
        rw [e1, e2]
    _ = 1 := by rw [← add_div, add_comm, div_self (by positivity)]
    _ < 2 := by norm_num

/-- The cyclic moment matrix is invertible. -/
theorem isUnit_periodicMomentMatrix (hn2 : 2 ≤ n) (hh : ∀ i, 1 ≤ i → i ≤ n → 0 < h i) :
    IsUnit (periodicMomentMatrix n h) :=
  (isStrictDiagDominant_periodicMomentMatrix hn2 hh).isUnit

/-- The periodic extension of a vector on `Fin n` to `ℕ`, `i ↦ v (i mod n)`. -/
noncomputable def cycExtend (hn : 1 ≤ n) (v : Fin n → ℝ) (i : ℕ) : ℝ := v ⟨i % n, Nat.mod_lt _ hn⟩

/-- The periodic extension agrees with the vector below `n`. -/
theorem cycExtend_of_lt (hn : 1 ≤ n) (v : Fin n → ℝ) {i : ℕ} (hi : i < n) :
    cycExtend hn v i = v ⟨i, hi⟩ := by
  simp only [cycExtend, Nat.mod_eq_of_lt hi]

/-- The periodic extension is `n`-periodic at the ends: `v n = v 0`. -/
theorem cycExtend_self (hn : 1 ≤ n) (v : Fin n → ℝ) : cycExtend hn v n = cycExtend hn v 0 := by
  simp only [cycExtend, Nat.mod_self, Nat.zero_mod]

end Periodic

section PeriodicSpline

variable (hx : IsPartition a b n x) (hn : 2 ≤ n) {f : ℕ → ℝ}
include hx hn

/-- **The cyclic system is the interior moment equations plus the periodicity of `s'`**: for the
periodic extension `M` of a vector `v` on `Fin n` (so `M n = M 0`), `A v = d` holds exactly when
the interior moment equations hold at `x_1, …, x_{n-1}` and the slopes of the first and the last
panel cubics agree at `a` and `b`. -/
theorem periodicMomentMatrix_mulVec_eq_iff (v : Fin n → ℝ) :
    (periodicMomentMatrix n (panelLength x)).mulVec v = periodicMomentRhs n (panelLength x) f ↔
      (∀ i, 1 ≤ i → i < n → IsMomentEq x f (cycExtend (by omega) v) i) ∧
        panelCubicD1 x f (cycExtend (by omega) v) 1 (x 0)
          = panelCubicD1 x f (cycExtend (by omega) v) n (x n) := by
  have hn1 : 1 ≤ n := by omega
  have h1 := hx.panelLength_pos le_rfl hn1
  have hnn := hx.panelLength_pos hn1 le_rfl
  set M := cycExtend hn1 v with hM
  have hMv : ∀ i (hi : i < n), v ⟨i, hi⟩ = M i := fun i hi => (cycExtend_of_lt hn1 v hi).symm
  -- the slope condition is the `0`-th row
  have hrow0 : panelCubicD1 x f M 1 (x 0) = panelCubicD1 x f M n (x n) ↔
      2 * M 0 + panelLength x 1 / (panelLength x n + panelLength x 1) * M 1
        + panelLength x n / (panelLength x n + panelLength x 1) * M (n - 1)
      = 6 / (panelLength x n + panelLength x 1)
        * ((f 1 - f 0) / panelLength x 1 - (f n - f (n - 1)) / panelLength x n) := by
    rw [panelCubicD1_left (i := 0) (hx.step 0 hn1), panelCubicD1_right (hx.lt (by omega) le_rfl)]
    have hMn : M n = M 0 := cycExtend_self hn1 v
    simp only [panelLength, hMn] at *
    have hc : 6 / (x n - x (n - 1) + (x 1 - x 0)) ≠ 0 := div_ne_zero (by norm_num) (by linarith)
    have key : 2 * M 0 + (x 1 - x 0) / (x n - x (n - 1) + (x 1 - x 0)) * M 1
        + (x n - x (n - 1)) / (x n - x (n - 1) + (x 1 - x 0)) * M (n - 1)
        - 6 / (x n - x (n - 1) + (x 1 - x 0))
          * ((f 1 - f 0) / (x 1 - x 0) - (f n - f (n - 1)) / (x n - x (n - 1)))
        = 6 / (x n - x (n - 1) + (x 1 - x 0)) * (((x n - x (n - 1)) * M (n - 1) / 6
            + (x n - x (n - 1)) * M 0 / 3 + (f n - f (n - 1)) / (x n - x (n - 1)))
          - (-((x 1 - x 0) * M 0) / 3 - (x 1 - x 0) * M 1 / 6 + (f 1 - f 0) / (x 1 - x 0))) := by
      have : x n - x (n - 1) ≠ 0 := by linarith
      have : x 1 - x 0 ≠ 0 := by linarith
      field_simp
      ring
    rw [eq_comm, ← sub_eq_zero, ← sub_eq_zero (a := 2 * M 0 + _ + _), key, mul_eq_zero,
      or_iff_right hc]
  have hMmod : ∀ k, v ⟨k % n, Nat.mod_lt _ hn1⟩ = M k := fun _ => rfl
  rw [funext_iff]
  constructor
  · intro H
    refine ⟨fun i hi1 hin => ?_, ?_⟩
    · have := H ⟨i, hin⟩
      rw [periodicMomentMatrix_mulVec_apply hn1, periodicMomentRhs, hMmod, hMv, hMv] at this
      simp only [cyc, ite_eq_right (show i ≠ 0 by omega)] at this
      rw [IsMomentEq]
      linear_combination this
    · have := H ⟨0, by omega⟩
      rw [periodicMomentMatrix_mulVec_apply hn1, periodicMomentRhs, hMmod, hMv, hMv] at this
      simp only [cyc, ↓reduceIte, Nat.zero_add] at this
      rw [hrow0]
      linear_combination this
  · rintro ⟨hint, h0⟩ ⟨i, hi⟩
    rw [periodicMomentMatrix_mulVec_apply hn1, periodicMomentRhs, hMmod, hMv, hMv]
    by_cases hi0 : i = 0
    · subst hi0
      simp only [cyc, ↓reduceIte, Nat.zero_add]
      rw [hrow0] at h0
      linear_combination h0
    · have := hint i (by omega) hi
      simp only [cyc, ite_eq_right hi0]
      rw [IsMomentEq] at this
      linear_combination this

end PeriodicSpline

/-- **The periodic end conditions** ([quarteroni2000numerical] (8.44) with `k = 3`, the two
derivative conditions): `s'(a) = s'(b)` and `s''(a) = s''(b)`, as derivatives within `[a, b]`. -/
def IsPeriodicEnd (a b : ℝ) (s : ℝ → ℝ) : Prop :=
  derivWithin s (Icc a b) a = derivWithin s (Icc a b) b ∧
    iteratedDerivWithin 2 s (Icc a b) a = iteratedDerivWithin 2 s (Icc a b) b

/-- The derivative within `[a, b]` of an interpolatory cubic spline at `a` is the slope of its
first panel cubic. -/
theorem IsCubicInterp.derivWithin_left (hx : IsPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ}
    {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s) :
    derivWithin s (Icc a b) a = panelCubicD1 x f (moment a b x s) 1 (x 0) := by
  have := (derivWithin_eq_of_eqOn_Icc_of_contDiffOn hs.contDiffOn (u := x 0) (v := x 1)
    (hx.step 0 hn) (Icc_subset_Icc (hx.left_le (Nat.zero_le n)) (hx.le_right hn))
    (hs.eqOn_panelCubic hx le_rfl hn) (left_mem_Icc.mpr (hx.step 0 hn).le)).1
  calc derivWithin s (Icc a b) a = derivWithin s (Icc a b) (x 0) := by rw [hx.first]
    _ = _ := this

/-- The derivative within `[a, b]` of an interpolatory cubic spline at `b` is the slope of its
last panel cubic. -/
theorem IsCubicInterp.derivWithin_right (hx : IsPartition a b n x) (hn : 1 ≤ n) {f : ℕ → ℝ}
    {s : ℝ → ℝ} (hs : IsCubicInterp a b n x f s) :
    derivWithin s (Icc a b) b = panelCubicD1 x f (moment a b x s) n (x n) := by
  have hlt : x (n - 1) < x n := hx.lt (Nat.sub_one_lt_of_le hn le_rfl) le_rfl
  have := (derivWithin_eq_of_eqOn_Icc_of_contDiffOn hs.contDiffOn (u := x (n - 1)) (v := x n)
    hlt (Icc_subset_Icc (hx.left_le (Nat.sub_le n 1)) (hx.le_right le_rfl))
    (hs.eqOn_panelCubic hx hn le_rfl) (right_mem_Icc.mpr hlt.le)).1
  calc derivWithin s (Icc a b) b = derivWithin s (Icc a b) (x n) := by rw [hx.last]
    _ = _ := this

/-- **Existence and uniqueness of the periodic cubic spline** ([quarteroni2000numerical] (8.44)
with `k = 3`): for `n ≥ 2` panels there is exactly one interpolatory cubic spline of the data with
`s'(a) = s'(b)` and `s''(a) = s''(b)`. Its moments satisfy `M_0 = M_n` and the cyclic system
`periodicMomentMatrix`, which is strictly diagonally dominant. (The remaining condition of (8.44),
`s(a) = s(b)`, holds exactly when `f 0 = f n`.) -/
theorem existsUnique_isCubicInterp_periodic (hx : IsPartition a b n x) (hn : 2 ≤ n) (f : ℕ → ℝ) :
    (∃ s, IsCubicInterp a b n x f s ∧ IsPeriodicEnd a b s) ∧
      ∀ s₁ s₂, IsCubicInterp a b n x f s₁ → IsPeriodicEnd a b s₁ →
        IsCubicInterp a b n x f s₂ → IsPeriodicEnd a b s₂ → EqOn s₁ s₂ (Icc a b) := by
  have hn1 : 1 ≤ n := by omega
  have hab := hx.lt_of_pos hn1
  have hA := isUnit_periodicMomentMatrix (h := panelLength x) hn
    fun i hi1 hin => hx.panelLength_pos hi1 hin
  -- the moments of a periodic interpolatory spline solve the cyclic system
  have hsolve : ∀ s, IsCubicInterp a b n x f s → IsPeriodicEnd a b s →
      (periodicMomentMatrix n (panelLength x)).mulVec
        (fun j : Fin n => moment a b x s (j : ℕ)) = periodicMomentRhs n (panelLength x) f := by
    intro s hs hp
    set M := moment a b x s with hM
    have hMn : M n = M 0 := by
      change iteratedDerivWithin 2 s (Icc a b) (x n) = iteratedDerivWithin 2 s (Icc a b) (x 0)
      rw [hx.first, hx.last]; exact hp.2.symm
    set v : Fin n → ℝ := fun j => M (j : ℕ) with hv
    have hext : ∀ i ≤ n, cycExtend hn1 v i = M i := fun i hi => by
      rcases lt_or_eq_of_le hi with hi | rfl
      · rw [cycExtend_of_lt hn1 v hi]
      · rw [cycExtend_self, cycExtend_of_lt hn1 v (by omega), hMn]
    refine (periodicMomentMatrix_mulVec_eq_iff hx hn v).mpr ⟨fun i hi1 hin => ?_, ?_⟩
    · rw [isMomentEq_congr (N := M) (hext _ (by omega)) (hext _ (by omega)) (hext _ (by omega))]
      exact hs.isMomentEq hx hi1 hin
    · have h1 := hs.derivWithin_left hx hn1
      have h2 := hs.derivWithin_right hx hn1
      have : panelCubicD1 x f (cycExtend hn1 v) 1 (x 0) = panelCubicD1 x f M 1 (x 0) := by
        simp only [panelCubicD1]
        rw [panelCubicPoly_congr rfl rfl (hext 0 (by omega)) (hext 1 hn1)]
      have h' : panelCubicD1 x f (cycExtend hn1 v) n (x n) = panelCubicD1 x f M n (x n) := by
        simp only [panelCubicD1]
        rw [panelCubicPoly_congr rfl rfl (hext (n - 1) (by omega)) (hext n le_rfl)]
      rw [this, h', ← h1, ← h2]
      exact hp.1
  constructor
  · -- existence
    set v : Fin n → ℝ := (periodicMomentMatrix n (panelLength x))⁻¹.mulVec
      (periodicMomentRhs n (panelLength x) f) with hv
    set M := cycExtend hn1 v with hM
    have hAv : (periodicMomentMatrix n (panelLength x)).mulVec v
        = periodicMomentRhs n (panelLength x) f := by
      rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hA), Matrix.one_mulVec]
    obtain ⟨hint, hslope⟩ := (periodicMomentMatrix_mulVec_eq_iff hx hn v).mp hAv
    set s := cubicSplineFun n x f M with hs
    have hc := contDiff_cubicSplineFun hx hn1 hint
    have hsi : IsCubicInterp a b n x f s :=
      ⟨⟨contDiffOn_cubicSplineFun hx hn1 hint, fun i hi1 hin =>
        ⟨panelCubicPoly x f M i, degree_panelCubicPoly_le _ _ _ _, cubicSplineFun_eqOn hx hi1 hin⟩⟩,
        fun i hi => cubicSplineFun_apply_node hx hn1 hi⟩
    have hmom : ∀ i ≤ n, moment a b x s i = M i := fun i hi => by
      rw [moment_eq_iteratedDeriv hab hc ⟨hx.left_le hi, hx.le_right hi⟩,
        iteratedDeriv_two_cubicSplineFun_node hx hn1 hint hi]
    refine ⟨s, hsi, ?_, ?_⟩
    · rw [hsi.derivWithin_left hx hn1, hsi.derivWithin_right hx hn1]
      have e1 : panelCubicD1 x f (moment a b x s) 1 (x 0) = panelCubicD1 x f M 1 (x 0) := by
        simp only [panelCubicD1]
        rw [panelCubicPoly_congr rfl rfl (hmom 0 (by omega)) (hmom 1 hn1)]
      have e2 : panelCubicD1 x f (moment a b x s) n (x n) = panelCubicD1 x f M n (x n) := by
        simp only [panelCubicD1]
        rw [panelCubicPoly_congr rfl rfl (hmom (n - 1) (by omega)) (hmom n le_rfl)]
      rw [e1, e2]
      exact hslope
    · have e0 : iteratedDerivWithin 2 s (Icc a b) a = M 0 := by
        rw [← hmom 0 (Nat.zero_le n), moment, hx.first]
      have eb : iteratedDerivWithin 2 s (Icc a b) b = M n := by
        rw [← hmom n le_rfl, moment, hx.last]
      rw [e0, eb, hM, cycExtend_self]
  · -- uniqueness
    intro s₁ s₂ h₁ hp₁ h₂ hp₂
    have hveq : (fun j : Fin n => moment a b x s₁ (j : ℕ))
        = fun j : Fin n => moment a b x s₂ (j : ℕ) :=
      Matrix.mulVec_injective_iff_isUnit.mpr hA ((hsolve s₁ h₁ hp₁).trans (hsolve s₂ h₂ hp₂).symm)
    have hlt : ∀ i < n, moment a b x s₁ i = moment a b x s₂ i := fun i hi =>
      congrFun hveq (⟨i, hi⟩ : Fin n)
    have hall : ∀ i ≤ n, moment a b x s₁ i = moment a b x s₂ i := fun i hi => by
      rcases lt_or_eq_of_le hi with hi | rfl
      · exact hlt i hi
      · have e₁ : moment a b x s₁ 0 = moment a b x s₁ i := by
          simp only [moment, hx.first, hx.last]; exact hp₁.2
        have e₂ : moment a b x s₂ 0 = moment a b x s₂ i := by
          simp only [moment, hx.first, hx.last]; exact hp₂.2
        exact e₁.symm.trans ((hlt 0 (by omega)).trans e₂)
    exact (h₁.eqOn_cubicSplineFun hx hn1).trans
      ((cubicSplineFun_eqOn_of_moment_eq hx hn1 hall).trans (h₂.eqOn_cubicSplineFun hx hn1).symm)

/-! ### Error bounds for the clamped interpolatory spline

For `f` of class `C⁴` with `|f⁗| ≤ K` on `[a, b]` and a partition of mesh at most `h`, the clamped
interpolatory cubic spline `s` of `f` satisfies `|f'' - s''| ≤ (7/4) h² K`,
`|f' - s'| ≤ (7/4) h³ K` and `|f - s| ≤ (7/8) h⁴ K` on `[a, b]`.

The argument is the classical one (Stoer and Bulirsch, *Introduction to Numerical Analysis*,
Theorem 2.4.3.3): the vector of exact values `f''(x_i)` satisfies the moment system (8.48) up to a
residual which Taylor expansion bounds by `(3/4) h² K`, so the moments are within `(3/4) h² K` of
`f''` at the nodes because `‖A⁻¹‖_∞ ≤ 1` (`linfty_opNorm_inv_momentMatrix_le`); on a panel `s''` is
the linear interpolant of two moments, hence within `(3/4) h² K + h² K` of `f''`; and `f - s`
vanishes at the nodes, so two applications of the mean value theorem — with Rolle's theorem in
between — give the `h³` and `h⁴` bounds.

The constants are not sharp: the sharp `5/384, 1/24, 3/8` for the function, its slope and its
second derivative are the theorem of Hall and Meyer, *Optimal error bounds for cubic spline
interpolation* (J. Approx. Theory 16, 1976), which is not formalized here.

The function is assumed `C⁴` on all of `ℝ` rather than on `Icc a b`; this matches
`Numlib/Approximation/Interpolation`'s `norm_sub_piecewiseLinearInterpCLM_le` and avoids carrying
within-derivatives at the two endpoints through every Taylor expansion. -/

section ClampedError

/-- **Taylor's theorem with a uniform remainder bound on `[a, b]`**: if `g` is `C^{m+1}` and its
`(m+1)`-st derivative is bounded by `K` on `[a, b]`, then the `m`-th Taylor polynomial of `g` at
`c ∈ [a, b]` approximates `g` at `t ∈ [a, b]` to within `K |t - c|^{m+1}/(m+1)!`. -/
private theorem abs_sub_taylorSum_le {m : ℕ} {g : ℝ → ℝ} {K c t : ℝ}
    (hg : ContDiff ℝ (m + 1) g) (hc : c ∈ Icc a b) (ht : t ∈ Icc a b)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv (m + 1) g y| ≤ K) :
    |g t - ∑ k ∈ Finset.range (m + 1),
        (t - c) ^ k / (k.factorial : ℝ) * iteratedDeriv k g c|
      ≤ K * |t - c| ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  rcases eq_or_ne c t with rfl | hne
  · rw [Finset.sum_range_succ', sub_self]
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK c hc)
    simp
  have hsub : uIcc c t ⊆ Icc a b := uIcc_subset_Icc hc ht
  obtain ⟨ξ, hξ, hT⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hg.contDiffOn
  have hpoly : taylorWithinEval g m (uIcc c t) c t
      = ∑ k ∈ Finset.range (m + 1), (t - c) ^ k / (k.factorial : ℝ) * iteratedDeriv k g c := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      (hg.contDiffAt.of_le (by
        exact_mod_cast (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)).trans (Nat.le_succ m)))
      left_mem_uIcc, smul_eq_mul]
    ring
  rw [hpoly] at hT
  rw [show g t - ∑ k ∈ Finset.range (m + 1),
        (t - c) ^ k / (k.factorial : ℝ) * iteratedDeriv k g c
      = iteratedDeriv (m + 1) g ξ * (t - c) ^ (m + 1) / ((m + 1).factorial : ℝ) from hT]
  rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hK ξ (hsub (Ioo_subset_Icc_self hξ))

/-- The third-order Taylor bound of a `C⁴` function between two points of `[a, b]`. -/
private theorem abs_sub_taylor_three_le {g : ℝ → ℝ} {K c t : ℝ} (hg : ContDiff ℝ 4 g)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 g y| ≤ K) :
    |g t - (g c + (t - c) * deriv g c + (t - c) ^ 2 / 2 * iteratedDeriv 2 g c
        + (t - c) ^ 3 / 6 * iteratedDeriv 3 g c)| ≤ K * |t - c| ^ 4 / 24 := by
  have hg' : ContDiff ℝ ((3 : ℕ) + 1) g := by norm_num; exact hg
  have hK' : ∀ y ∈ Icc a b, |iteratedDeriv ((3 : ℕ) + 1) g y| ≤ K := by simpa using hK
  have h1 := abs_sub_taylorSum_le hg' hc ht hK'
  have hsum : ∑ k ∈ Finset.range ((3 : ℕ) + 1),
      (t - c) ^ k / (k.factorial : ℝ) * iteratedDeriv k g c
      = g c + (t - c) * deriv g c + (t - c) ^ 2 / 2 * iteratedDeriv 2 g c
        + (t - c) ^ 3 / 6 * iteratedDeriv 3 g c := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, iteratedDeriv_zero, iteratedDeriv_one]
    norm_num [Nat.factorial]
  rw [hsum] at h1
  calc |g t - (g c + (t - c) * deriv g c + (t - c) ^ 2 / 2 * iteratedDeriv 2 g c
        + (t - c) ^ 3 / 6 * iteratedDeriv 3 g c)|
      ≤ K * |t - c| ^ ((3 : ℕ) + 1) / (((3 : ℕ) + 1).factorial : ℝ) := h1
    _ = K * |t - c| ^ 4 / 24 := by norm_num [Nat.factorial]

/-- The first-order Taylor bound of a `C²` function between two points of `[a, b]`. -/
private theorem abs_sub_taylor_one_le {g : ℝ → ℝ} {K c t : ℝ} (hg : ContDiff ℝ 2 g)
    (hc : c ∈ Icc a b) (ht : t ∈ Icc a b)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 2 g y| ≤ K) :
    |g t - (g c + (t - c) * deriv g c)| ≤ K * |t - c| ^ 2 / 2 := by
  have hg' : ContDiff ℝ ((1 : ℕ) + 1) g := by norm_num; exact hg
  have hK' : ∀ y ∈ Icc a b, |iteratedDeriv ((1 : ℕ) + 1) g y| ≤ K := by simpa using hK
  have h1 := abs_sub_taylorSum_le hg' hc ht hK'
  have hsum : ∑ k ∈ Finset.range ((1 : ℕ) + 1),
      (t - c) ^ k / (k.factorial : ℝ) * iteratedDeriv k g c
      = g c + (t - c) * deriv g c := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, iteratedDeriv_zero, iteratedDeriv_one]
    norm_num [Nat.factorial]
  rw [hsum] at h1
  calc |g t - (g c + (t - c) * deriv g c)|
      ≤ K * |t - c| ^ ((1 : ℕ) + 1) / (((1 : ℕ) + 1).factorial : ℝ) := h1
    _ = K * |t - c| ^ 2 / 2 := by norm_num [Nat.factorial]

/-- The second derivative of a `C⁴` function is `C²`. -/
private theorem contDiff_iteratedDeriv_two {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) :
    ContDiff ℝ 2 (iteratedDeriv 2 f) := by
  have h2 : iteratedDeriv 2 f = deriv (deriv f) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  exact (hf.deriv' (n := 3)).deriv' (n := 2)

/-- Iterated derivatives of the second derivative are shifted iterated derivatives. -/
private theorem iteratedDeriv_iteratedDeriv_two (f : ℝ → ℝ) (j : ℕ) :
    iteratedDeriv j (iteratedDeriv 2 f) = iteratedDeriv (j + 2) f := by
  have h2 : iteratedDeriv 2 f = deriv (deriv f) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, show j + 2 = j + 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_succ']

/-- A `C²` function has its second iterated derivative as the derivative of its derivative. -/
private theorem hasDerivAt_deriv_of_contDiff_two {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (y : ℝ) :
    HasDerivAt (deriv g) (iteratedDeriv 2 g y) y := by
  have h : ContDiff ℝ 1 (deriv g) := hg.deriv' (n := 1)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact ((h.differentiable (by norm_num)) y).hasDerivAt

/-- The two Taylor remainders used in the residual estimates: of `f` to order three and of `f''` to
order one, both about `c` and evaluated at `c + w`. -/
private theorem abs_taylor_pair {f : ℝ → ℝ} {K c : ℝ} (hf : ContDiff ℝ 4 f)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
    {w : ℝ} (hc : c ∈ Icc a b) (hcw : c + w ∈ Icc a b) :
    |f (c + w) - (f c + w * deriv f c + w ^ 2 / 2 * iteratedDeriv 2 f c
        + w ^ 3 / 6 * iteratedDeriv 3 f c)| ≤ K * |w| ^ 4 / 24 ∧
    |iteratedDeriv 2 f (c + w) - (iteratedDeriv 2 f c + w * iteratedDeriv 3 f c)|
      ≤ K * |w| ^ 2 / 2 := by
  have hw : c + w - c = w := by ring
  refine ⟨?_, ?_⟩
  · have h := abs_sub_taylor_three_le hf hc hcw hK
    rwa [hw] at h
  · have hKg : ∀ y ∈ Icc a b, |iteratedDeriv 2 (iteratedDeriv 2 f) y| ≤ K := by
      intro y hy
      rw [iteratedDeriv_iteratedDeriv_two]
      exact hK y hy
    have h := abs_sub_taylor_one_le (contDiff_iteratedDeriv_two hf) hc hcw hKg
    rw [hw, ← iteratedDeriv_succ] at h
    exact h

/-- Two positive numbers below `h` satisfy `u² - uv + v² ≤ h²`. -/
private theorem sq_sub_mul_add_sq_le {u v hm : ℝ} (hu : 0 < u) (hv : 0 < v) (huh : u ≤ hm)
    (hvh : v ≤ hm) : u ^ 2 - u * v + v ^ 2 ≤ hm ^ 2 := by
  rcases le_total u v with h | h
  · nlinarith
  · nlinarith

section Residual

variable {f : ℝ → ℝ} {K c u v hm : ℝ}

/-- **The residual of an interior moment row** at the exact second derivatives of `f`: the row
`μ_i f''(x_{i-1}) + 2 f''(x_i) + λ_i f''(x_{i+1}) - d_i` of (8.47) is at most `(3/4) h² K` in
absolute value. -/
private theorem abs_interior_residual_le (hf : ContDiff ℝ 4 f)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
    (hu : 0 < u) (hv : 0 < v) (huh : u ≤ hm) (hvh : v ≤ hm)
    (hcv : c - v ∈ Icc a b) (hc : c ∈ Icc a b) (hcu : c + u ∈ Icc a b) :
    |v / (u + v) * iteratedDeriv 2 f (c - v) + 2 * iteratedDeriv 2 f c
        + u / (u + v) * iteratedDeriv 2 f (c + u)
        - 6 / (u + v) * ((f (c + u) - f c) / u - (f c - f (c - v)) / v)|
      ≤ 3 / 4 * hm ^ 2 * K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK c hc)
  have huv : (0 : ℝ) < u + v := by linarith
  obtain ⟨e1, E1⟩ := abs_taylor_pair hf hK (w := u) hc hcu
  obtain ⟨e2, E2⟩ := abs_taylor_pair hf hK (w := -v) hc (by rw [← sub_eq_add_neg]; exact hcv)
  rw [← sub_eq_add_neg] at e2 E2
  rw [abs_of_pos hu] at e1 E1
  rw [abs_neg, abs_of_pos hv] at e2 E2
  set F0 := f c
  set F1 := deriv f c
  set F2 := iteratedDeriv 2 f c
  set F3 := iteratedDeriv 3 f c
  set P := f (c + u)
  set N := f (c - v)
  set Gp := iteratedDeriv 2 f (c + u)
  set Gn := iteratedDeriv 2 f (c - v)
  set A := Gn - (F2 + -v * F3) with hA
  set B := Gp - (F2 + u * F3) with hB
  set p := P - (F0 + u * F1 + u ^ 2 / 2 * F2 + u ^ 3 / 6 * F3) with hp
  set q := N - (F0 + -v * F1 + (-v) ^ 2 / 2 * F2 + (-v) ^ 3 / 6 * F3) with hq
  have key : v / (u + v) * Gn + 2 * F2 + u / (u + v) * Gp
      - 6 / (u + v) * ((P - F0) / u - (F0 - N) / v)
      = v / (u + v) * A + u / (u + v) * B - 6 / (u + v) * (p / u + q / v) := by
    rw [hA, hB, hp, hq]
    field_simp
    ring
  rw [key]
  have t3 : |p / u + q / v| ≤ K * u ^ 4 / 24 / u + K * v ^ 4 / 24 / v := by
    calc |p / u + q / v| ≤ |p / u| + |q / v| := abs_add_le _ _
      _ = |p| / u + |q| / v := by rw [abs_div, abs_div, abs_of_pos hu, abs_of_pos hv]
      _ ≤ K * u ^ 4 / 24 / u + K * v ^ 4 / 24 / v := by gcongr
  have hfin : v / (u + v) * (K * v ^ 2 / 2) + u / (u + v) * (K * u ^ 2 / 2)
      + 6 / (u + v) * (K * u ^ 4 / 24 / u + K * v ^ 4 / 24 / v)
      = 3 / 4 * K * (u ^ 2 - u * v + v ^ 2) := by
    field_simp
    ring
  calc |v / (u + v) * A + u / (u + v) * B - 6 / (u + v) * (p / u + q / v)|
      ≤ |v / (u + v) * A| + |u / (u + v) * B| + |6 / (u + v) * (p / u + q / v)| := by
        rw [sub_eq_add_neg, ← abs_neg (6 / (u + v) * (p / u + q / v))]
        exact abs_add_three _ _ _
    _ = v / (u + v) * |A| + u / (u + v) * |B| + 6 / (u + v) * |p / u + q / v| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < v / (u + v)),
          abs_of_pos (by positivity : (0:ℝ) < u / (u + v)),
          abs_of_pos (by positivity : (0:ℝ) < 6 / (u + v))]
    _ ≤ v / (u + v) * (K * v ^ 2 / 2) + u / (u + v) * (K * u ^ 2 / 2)
        + 6 / (u + v) * (K * u ^ 4 / 24 / u + K * v ^ 4 / 24 / v) := by gcongr
    _ = 3 / 4 * K * (u ^ 2 - u * v + v ^ 2) := hfin
    _ ≤ 3 / 4 * hm ^ 2 * K := by
        have := sq_sub_mul_add_sq_le hu hv huh hvh
        nlinarith

/-- **The residual of the left clamped closure row** at the exact second derivatives of `f`. -/
private theorem abs_left_residual_le (hf : ContDiff ℝ 4 f)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
    (hu : 0 < u) (huh : u ≤ hm) (hc : c ∈ Icc a b) (hcu : c + u ∈ Icc a b) :
    |2 * iteratedDeriv 2 f c + iteratedDeriv 2 f (c + u)
        - 6 / u * ((f (c + u) - f c) / u - deriv f c)| ≤ 3 / 4 * hm ^ 2 * K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK c hc)
  obtain ⟨e1, E1⟩ := abs_taylor_pair hf hK (w := u) hc hcu
  rw [abs_of_pos hu] at e1 E1
  set F0 := f c
  set F1 := deriv f c
  set F2 := iteratedDeriv 2 f c
  set F3 := iteratedDeriv 3 f c
  set P := f (c + u)
  set Gp := iteratedDeriv 2 f (c + u)
  set B := Gp - (F2 + u * F3) with hB
  set p := P - (F0 + u * F1 + u ^ 2 / 2 * F2 + u ^ 3 / 6 * F3) with hp
  have key : 2 * F2 + Gp - 6 / u * ((P - F0) / u - F1) = B - 6 / u ^ 2 * p := by
    rw [hB, hp]; field_simp; ring
  rw [key]
  calc |B - 6 / u ^ 2 * p| ≤ |B| + |6 / u ^ 2 * p| := by
        rw [sub_eq_add_neg, ← abs_neg (6 / u ^ 2 * p)]; exact abs_add_le _ _
    _ = |B| + 6 / u ^ 2 * |p| := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 6 / u ^ 2)]
    _ ≤ K * u ^ 2 / 2 + 6 / u ^ 2 * (K * u ^ 4 / 24) := by gcongr
    _ = 3 / 4 * u ^ 2 * K := by field_simp; ring
    _ ≤ 3 / 4 * hm ^ 2 * K := by
        have h2 : u ^ 2 ≤ hm ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 huh) (by linarith : (0:ℝ) ≤ hm + u)]
        nlinarith [mul_nonneg (sub_nonneg.2 h2) hK0]

/-- **The residual of the right clamped closure row** at the exact second derivatives of `f`. -/
private theorem abs_right_residual_le (hf : ContDiff ℝ 4 f)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
    (hv : 0 < v) (hvh : v ≤ hm) (hcv : c - v ∈ Icc a b) (hc : c ∈ Icc a b) :
    |iteratedDeriv 2 f (c - v) + 2 * iteratedDeriv 2 f c
        - 6 / v * (deriv f c - (f c - f (c - v)) / v)| ≤ 3 / 4 * hm ^ 2 * K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK c hc)
  obtain ⟨e2, E2⟩ := abs_taylor_pair hf hK (w := -v) hc (by rw [← sub_eq_add_neg]; exact hcv)
  rw [← sub_eq_add_neg] at e2 E2
  rw [abs_neg, abs_of_pos hv] at e2 E2
  set F0 := f c
  set F1 := deriv f c
  set F2 := iteratedDeriv 2 f c
  set F3 := iteratedDeriv 3 f c
  set N := f (c - v)
  set Gn := iteratedDeriv 2 f (c - v)
  set A := Gn - (F2 + -v * F3) with hA
  set q := N - (F0 + -v * F1 + (-v) ^ 2 / 2 * F2 + (-v) ^ 3 / 6 * F3) with hq
  have key : Gn + 2 * F2 - 6 / v * (F1 - (F0 - N) / v) = A - 6 / v ^ 2 * q := by
    rw [hA, hq]; field_simp; ring
  rw [key]
  calc |A - 6 / v ^ 2 * q| ≤ |A| + |6 / v ^ 2 * q| := by
        rw [sub_eq_add_neg, ← abs_neg (6 / v ^ 2 * q)]; exact abs_add_le _ _
    _ = |A| + 6 / v ^ 2 * |q| := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 6 / v ^ 2)]
    _ ≤ K * v ^ 2 / 2 + 6 / v ^ 2 * (K * v ^ 4 / 24) := by gcongr
    _ = 3 / 4 * v ^ 2 * K := by field_simp; ring
    _ ≤ 3 / 4 * hm ^ 2 * K := by
        have h2 : v ^ 2 ≤ hm ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 hvh) (by linarith : (0:ℝ) ≤ hm + v)]
        nlinarith [mul_nonneg (sub_nonneg.2 h2) hK0]

/-- **A crude bound on the error of linear interpolation** between two points of `[a, b]`: the
affine function through `(p, g p)` and `(q, g q)` differs from `g` by at most `K (q - p)²`, where
`K` bounds `|g''|`. (The sharp constant is `K (q - p)²/8`; it is not needed here.) -/
private theorem abs_linearInterp_sub_le {g : ℝ → ℝ} {K p q t : ℝ} (hg : ContDiff ℝ 2 g)
    (hK : ∀ y ∈ Icc a b, |iteratedDeriv 2 g y| ≤ K) (hpq : p < q)
    (hsub : Icc p q ⊆ Icc a b) (ht : t ∈ Icc p q) :
    |g p * (q - t) / (q - p) + g q * (t - p) / (q - p) - g t| ≤ K * (q - p) ^ 2 := by
  have hp : p ∈ Icc a b := hsub ⟨le_rfl, hpq.le⟩
  have hq : q ∈ Icc a b := hsub ⟨hpq.le, le_rfl⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK p hp)
  have hd : (0 : ℝ) < q - p := sub_pos.mpr hpq
  have e1 := abs_sub_taylor_one_le hg hp hq hK
  have e2 := abs_sub_taylor_one_le hg hp (hsub ht) hK
  rw [abs_of_pos hd] at e1
  rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - p)] at e2
  set eq' := g q - (g p + (q - p) * deriv g p) with heq'
  set et := g t - (g p + (t - p) * deriv g p) with het
  have key : g p * (q - t) / (q - p) + g q * (t - p) / (q - p) - g t
      = (t - p) / (q - p) * eq' - et := by
    rw [heq', het]; field_simp; ring
  rw [key]
  have hθ : (t - p) / (q - p) ≤ 1 := (div_le_one hd).mpr (by linarith [ht.2])
  have hθ0 : (0 : ℝ) ≤ (t - p) / (q - p) := div_nonneg (by linarith [ht.1]) hd.le
  calc |(t - p) / (q - p) * eq' - et| ≤ |(t - p) / (q - p) * eq'| + |et| := by
        rw [sub_eq_add_neg, ← abs_neg et]; exact abs_add_le _ _
    _ = (t - p) / (q - p) * |eq'| + |et| := by rw [abs_mul, abs_of_nonneg hθ0]
    _ ≤ 1 * (K * (q - p) ^ 2 / 2) + K * (t - p) ^ 2 / 2 := by gcongr
    _ ≤ 1 * (K * (q - p) ^ 2 / 2) + K * (q - p) ^ 2 / 2 := by
        gcongr
        · linarith [ht.1]
        · linarith [ht.2]
    _ = K * (q - p) ^ 2 := by ring

end Residual

/-- **The second derivative of the interpolatory cubic spline is linear on every panel**, taking
the moments at the two ends ([quarteroni2000numerical] (8.46)). -/
theorem iteratedDeriv_two_cubicInterp_eq_of_mem (hx : IsPartition a b n x) (hn : 1 ≤ n)
    {f : ℕ → ℝ} {lam0 mun d0 dn : ℝ} (hl0 : 0 ≤ lam0) (hl1 : lam0 ≤ 1) (hm0 : 0 ≤ mun)
    (hm1 : mun ≤ 1) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) {t : ℝ}
    (ht : t ∈ Icc (x (i - 1)) (x i)) :
    iteratedDeriv 2 (cubicInterp n x f lam0 mun d0 dn) t
      = iteratedDeriv 2 (cubicInterp n x f lam0 mun d0 dn) (x (i - 1)) * (x i - t)
          / (x i - x (i - 1))
        + iteratedDeriv 2 (cubicInterp n x f lam0 mun d0 dn) (x i) * (t - x (i - 1))
          / (x i - x (i - 1)) := by
  have hM : ∀ j, 1 ≤ j → j < n → IsMomentEq x f (momentVec n x f lam0 mun d0 dn) j :=
    fun _ h1 h2 => isMomentEq_momentVec hx hn hl0 hl1 hm0 hm1 h1 h2
  rw [iteratedDeriv_two_cubicInterp_node hx hn hl0 hl1 hm0 hm1 (show i - 1 ≤ n by omega),
    iteratedDeriv_two_cubicInterp_node hx hn hl0 hl1 hm0 hm1 hin, cubicInterp,
    iteratedDeriv_two_cubicSplineFun hx hn hM,
    panelGlue_eq_of_mem hx (fun _ h1 h2 => panelCubicD2_apply_node_succ hx h1 h2) hi1 hin
      (Icc_subset_extPanel i ht),
    panelCubicD2_apply _ _ _ (hx.lt (by omega) hin)]

/-- The second derivative of the clamped spline is linear on every panel. -/
private theorem iteratedDeriv_two_clampedInterp_eq_of_mem (hx : IsPartition a b n x) (hn : 1 ≤ n)
    {f : ℕ → ℝ} (f'0 f'n : ℝ) {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) {t : ℝ}
    (ht : t ∈ Icc (x (i - 1)) (x i)) :
    iteratedDeriv 2 (clampedInterp n x f f'0 f'n) t
      = iteratedDeriv 2 (clampedInterp n x f f'0 f'n) (x (i - 1)) * (x i - t)
          / (x i - x (i - 1))
        + iteratedDeriv 2 (clampedInterp n x f f'0 f'n) (x i) * (t - x (i - 1))
          / (x i - x (i - 1)) :=
  iteratedDeriv_two_cubicInterp_eq_of_mem hx hn zero_le_one le_rfl zero_le_one le_rfl hi1 hin ht

section Bounds

open scoped Matrix.Norms.Operator

variable (hx : IsPartition a b n x) (hn : 1 ≤ n) {f : ℝ → ℝ} {K hm : ℝ} (hf : ContDiff ℝ 4 f)
  (hK : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ K)
  (hmesh : ∀ i, 1 ≤ i → i ≤ n → panelLength x i ≤ hm)
include hx hn hf hK hmesh

/-- **The moments of the clamped spline approximate `f''` to second order** (Stoer and Bulirsch,
*Introduction to Numerical Analysis*, Theorem 2.4.3.3): for `f` of class `C⁴` with `|f⁗| ≤ K` on
`[a, b]` and panel lengths at most `h`, the clamped interpolatory spline `s` of the nodal values of
`f` satisfies `|s''(x_i) - f''(x_i)| ≤ (3/4) h² K` at every node.

The vector of exact values `f''(x_i)` satisfies the moment system (8.48) up to a residual bounded
by `(3/4) h² K` — Taylor expansion of `f` and of `f''` about `x_i` for the interior rows, and the
two clamped closure rows separately — and `‖A⁻¹‖_∞ ≤ 1` by
`linfty_opNorm_inv_momentMatrix_le`. -/
theorem norm_deriv2_sub_clampedInterp_le {i : ℕ} (hi : i ≤ n) :
    |iteratedDeriv 2 (clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b)) (x i)
      - iteratedDeriv 2 f (x i)| ≤ 3 / 4 * hm ^ 2 * K := by
  classical
  rw [← hx.first, ← hx.last]
  suffices key : ∀ d0 dn : ℝ,
      d0 = 6 / (x 1 - x 0) * ((f (x 1) - f (x 0)) / (x 1 - x 0) - deriv f (x 0)) →
      dn = 6 / (x n - x (n - 1))
        * (deriv f (x n) - (f (x n) - f (x (n - 1))) / (x n - x (n - 1))) →
      |iteratedDeriv 2 (cubicInterp n x (fun j => f (x j)) 1 1 d0 dn) (x i)
        - iteratedDeriv 2 f (x i)| ≤ 3 / 4 * hm ^ 2 * K from key _ _ rfl rfl
  intro d0 dn hd0 hdn
  have hpos : ∀ j, 1 ≤ j → j ≤ n → 0 < panelLength x j := fun j h1 h2 => hx.panelLength_pos h1 h2
  have hmem : ∀ j, j ≤ n → x j ∈ Icc a b := fun j hj => ⟨hx.left_le hj, hx.le_right hj⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ⟨le_rfl, hx.le⟩)
  set fd : ℕ → ℝ := fun j => f (x j) with hfd
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := momentMatrix n (panelLength x) 1 1 with hA
  set d : Fin (n + 1) → ℝ := momentRhs n (panelLength x) fd d0 dn with hd
  set Mv : Fin (n + 1) → ℝ := A⁻¹.mulVec d with hMv
  set Fv : Fin (n + 1) → ℝ := fun j => iteratedDeriv 2 f (x j) with hFv
  have hmv : momentVec n x fd 1 1 d0 dn = extendFin Mv := rfl
  rw [iteratedDeriv_two_cubicInterp_node hx hn zero_le_one le_rfl zero_le_one le_rfl hi, hmv,
    extendFin_of_lt (i := i) _ (show i < n + 1 by omega),
    show iteratedDeriv 2 f (x i) = Fv ⟨i, by omega⟩ from rfl]
  have hrow : ∀ j : Fin (n + 1), |d j - (A.mulVec Fv) j| ≤ 3 / 4 * hm ^ 2 * K := by
    intro j
    rw [hA, momentMatrix_mulVec_apply]
    rcases eq_or_ne (j : ℕ) 0 with hj0 | hj0
    · -- the left closure row
      have h1n : (1 : ℕ) < n + 1 := by omega
      have hdj : d j = d0 := by simp only [hd, momentRhs, hj0, reduceIte]
      have hlam : momentLam (panelLength x) 1 (j : ℕ) = 1 := by
        simp only [momentLam, hj0, reduceIte]
      have hext : extendFin Fv ((j : ℕ) + 1) = iteratedDeriv 2 f (x 1) := by
        rw [hj0, extendFin_of_lt _ h1n]
      have hFvj : Fv j = iteratedDeriv 2 f (x 0) := by rw [hFv]; simp [hj0]
      have hmu : (if (j : ℕ) = 0 then (0 : ℝ) else extendFin Fv ((j : ℕ) - 1)) = 0 := by
        simp [hj0]
      rw [hdj, hlam, hext, hFvj, hmu, hd0]
      have hu : 0 < x 1 - x 0 := sub_pos.mpr (hx.step 0 (by omega))
      have hcu : x 0 + (x 1 - x 0) ∈ Icc a b := by
        rw [show x 0 + (x 1 - x 0) = x 1 from by ring]; exact hmem 1 hn
      have hres := abs_left_residual_le (a := a) (b := b) (hm := hm) hf hK hu
        (by simpa [panelLength] using hmesh 1 le_rfl hn) (hmem 0 (by omega)) hcu
      rw [show x 0 + (x 1 - x 0) = x 1 from by ring] at hres
      rw [show 6 / (x 1 - x 0) * ((f (x 1) - f (x 0)) / (x 1 - x 0) - deriv f (x 0))
          - (2 * iteratedDeriv 2 f (x 0) + 1 * iteratedDeriv 2 f (x 1) + _ * 0)
          = -(2 * iteratedDeriv 2 f (x 0) + iteratedDeriv 2 f (x 1)
              - 6 / (x 1 - x 0) * ((f (x 1) - f (x 0)) / (x 1 - x 0) - deriv f (x 0)))
        from by ring, abs_neg]
      exact hres
    · rcases eq_or_ne (j : ℕ) n with hjn | hjn
      · -- the right closure row
        have hdj : d j = dn := by
          simp only [hd, momentRhs]
          rw [ite_eq_right hj0, ite_eq_left hjn]
        have hext : extendFin Fv ((j : ℕ) + 1) = 0 := extendFin_of_le _ (by omega)
        have hmu : momentMu n (panelLength x) 1 (j : ℕ) = 1 := by
          simp only [momentMu, hjn, reduceIte]
        have hext2 : (if (j : ℕ) = 0 then (0 : ℝ) else extendFin Fv ((j : ℕ) - 1))
            = iteratedDeriv 2 f (x (n - 1)) := by
          rw [ite_eq_right hj0, hjn, extendFin_of_lt _ (show n - 1 < n + 1 by omega)]
        have hFvj : Fv j = iteratedDeriv 2 f (x n) := by rw [hFv]; simp [hjn]
        rw [hdj, hext, hmu, hext2, hFvj, hdn, mul_zero]
        have hv : 0 < x n - x (n - 1) := sub_pos.mpr (hx.lt (by omega) le_rfl)
        have hcv : x n - (x n - x (n - 1)) ∈ Icc a b := by
          rw [show x n - (x n - x (n - 1)) = x (n - 1) from by ring]; exact hmem _ (by omega)
        have hres := abs_right_residual_le (a := a) (b := b) (hm := hm) hf hK hv
          (by simpa [panelLength] using hmesh n hn le_rfl) hcv (hmem n le_rfl)
        rw [show x n - (x n - x (n - 1)) = x (n - 1) from by ring] at hres
        rw [show 6 / (x n - x (n - 1))
              * (deriv f (x n) - (f (x n) - f (x (n - 1))) / (x n - x (n - 1)))
            - (2 * iteratedDeriv 2 f (x n) + 0 + 1 * iteratedDeriv 2 f (x (n - 1)))
            = -(iteratedDeriv 2 f (x (n - 1)) + 2 * iteratedDeriv 2 f (x n)
                - 6 / (x n - x (n - 1))
                  * (deriv f (x n) - (f (x n) - f (x (n - 1))) / (x n - x (n - 1))))
          from by ring, abs_neg]
        exact hres
      · -- an interior row
        have hjn' : (j : ℕ) < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp j.2) hjn
        have hj1 : 1 ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr hj0
        have hdj : d j = 6 / (panelLength x (j : ℕ) + panelLength x ((j : ℕ) + 1))
            * ((f (x ((j : ℕ) + 1)) - f (x (j : ℕ))) / panelLength x ((j : ℕ) + 1)
              - (f (x (j : ℕ)) - f (x ((j : ℕ) - 1))) / panelLength x (j : ℕ)) := by
          simp only [hd, momentRhs, hfd]
          rw [ite_eq_right hj0, ite_eq_right hjn]
        have hlam : momentLam (panelLength x) 1 (j : ℕ)
            = panelLength x ((j : ℕ) + 1)
              / (panelLength x (j : ℕ) + panelLength x ((j : ℕ) + 1)) := by
          simp only [momentLam, ite_eq_right hj0]
        have hmu : momentMu n (panelLength x) 1 (j : ℕ)
            = panelLength x (j : ℕ)
              / (panelLength x (j : ℕ) + panelLength x ((j : ℕ) + 1)) := by
          simp only [momentMu, ite_eq_right hjn]
        have hext : extendFin Fv ((j : ℕ) + 1) = iteratedDeriv 2 f (x ((j : ℕ) + 1)) :=
          extendFin_of_lt _ (by omega)
        have hext2 : (if (j : ℕ) = 0 then (0 : ℝ) else extendFin Fv ((j : ℕ) - 1))
            = iteratedDeriv 2 f (x ((j : ℕ) - 1)) := by
          rw [ite_eq_right hj0, extendFin_of_lt _ (show (j : ℕ) - 1 < n + 1 by omega)]
        have hFvj : Fv j = iteratedDeriv 2 f (x (j : ℕ)) := rfl
        have hpl1 : panelLength x (j : ℕ) = x (j : ℕ) - x ((j : ℕ) - 1) := rfl
        have hpl2 : panelLength x ((j : ℕ) + 1) = x ((j : ℕ) + 1) - x (j : ℕ) := by
          simp [panelLength]
        rw [hdj, hlam, hmu, hext, hext2, hFvj, hpl1, hpl2]
        have hu : 0 < x ((j : ℕ) + 1) - x (j : ℕ) := sub_pos.mpr (hx.step _ hjn')
        have hv : 0 < x (j : ℕ) - x ((j : ℕ) - 1) := sub_pos.mpr (hx.lt (by omega) (by omega))
        have hcu : x (j : ℕ) + (x ((j : ℕ) + 1) - x (j : ℕ)) ∈ Icc a b := by
          rw [show x (j : ℕ) + (x ((j : ℕ) + 1) - x (j : ℕ)) = x ((j : ℕ) + 1) from by ring]
          exact hmem _ (by omega)
        have hcv : x (j : ℕ) - (x (j : ℕ) - x ((j : ℕ) - 1)) ∈ Icc a b := by
          rw [show x (j : ℕ) - (x (j : ℕ) - x ((j : ℕ) - 1)) = x ((j : ℕ) - 1) from by ring]
          exact hmem _ (by omega)
        have hres := abs_interior_residual_le (a := a) (b := b) (hm := hm) hf hK hu hv
          (by simpa [panelLength] using hmesh ((j : ℕ) + 1) (by omega) (by omega))
          (by simpa [panelLength] using hmesh (j : ℕ) hj1 (by omega))
          hcv (hmem _ (by omega)) hcu
        rw [show x (j : ℕ) + (x ((j : ℕ) + 1) - x (j : ℕ)) = x ((j : ℕ) + 1) from by ring,
          show x (j : ℕ) - (x (j : ℕ) - x ((j : ℕ) - 1)) = x ((j : ℕ) - 1) from by ring] at hres
        rw [show (6 / (x (j : ℕ) - x ((j : ℕ) - 1) + (x ((j : ℕ) + 1) - x (j : ℕ)))
              * ((f (x ((j : ℕ) + 1)) - f (x (j : ℕ))) / (x ((j : ℕ) + 1) - x (j : ℕ))
                - (f (x (j : ℕ)) - f (x ((j : ℕ) - 1))) / (x (j : ℕ) - x ((j : ℕ) - 1)))
            - (2 * iteratedDeriv 2 f (x (j : ℕ))
              + (x ((j : ℕ) + 1) - x (j : ℕ))
                / (x (j : ℕ) - x ((j : ℕ) - 1) + (x ((j : ℕ) + 1) - x (j : ℕ)))
                * iteratedDeriv 2 f (x ((j : ℕ) + 1))
              + (x (j : ℕ) - x ((j : ℕ) - 1))
                / (x (j : ℕ) - x ((j : ℕ) - 1) + (x ((j : ℕ) + 1) - x (j : ℕ)))
                * iteratedDeriv 2 f (x ((j : ℕ) - 1))))
            = -((x (j : ℕ) - x ((j : ℕ) - 1))
                  / ((x ((j : ℕ) + 1) - x (j : ℕ)) + (x (j : ℕ) - x ((j : ℕ) - 1)))
                  * iteratedDeriv 2 f (x ((j : ℕ) - 1))
                + 2 * iteratedDeriv 2 f (x (j : ℕ))
                + (x ((j : ℕ) + 1) - x (j : ℕ))
                  / ((x ((j : ℕ) + 1) - x (j : ℕ)) + (x (j : ℕ) - x ((j : ℕ) - 1)))
                  * iteratedDeriv 2 f (x ((j : ℕ) + 1))
                - 6 / ((x ((j : ℕ) + 1) - x (j : ℕ)) + (x (j : ℕ) - x ((j : ℕ) - 1)))
                  * ((f (x ((j : ℕ) + 1)) - f (x (j : ℕ))) / (x ((j : ℕ) + 1) - x (j : ℕ))
                    - (f (x (j : ℕ)) - f (x ((j : ℕ) - 1))) / (x (j : ℕ) - x ((j : ℕ) - 1))))
          from by ring, abs_neg]
        exact hres
  calc |Mv ⟨i, by omega⟩ - Fv ⟨i, by omega⟩| = ‖(Mv - Fv) ⟨i, by omega⟩‖ := by
        rw [Pi.sub_apply, Real.norm_eq_abs]
    _ ≤ ‖Mv - Fv‖ := norm_le_pi_norm _ _
    _ ≤ 3 / 4 * hm ^ 2 * K := by
        refine le_trans
          (norm_le_norm_momentMatrix_mulVec hpos zero_le_one le_rfl zero_le_one le_rfl _) ?_
        have hmul : A.mulVec (Mv - Fv) = d - A.mulVec Fv := by
          rw [Matrix.mulVec_sub, hMv, hA,
            momentMatrix_mulVec_momentVec hx zero_le_one le_rfl zero_le_one le_rfl fd d0 dn]
        rw [hmul]
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
        rw [Pi.sub_apply, Real.norm_eq_abs]
        exact hrow j

/-- **The clamped spline's second derivative approximates `f''` to second order on all of
`[a, b]`**: `|s''(t) - f''(t)| ≤ (7/4) h² K`. On a panel `s''` is the linear interpolant of its two
end moments, which are within `(3/4) h² K` of `f''` at the ends
(`norm_deriv2_sub_clampedInterp_le`), and the linear interpolant of `f''` is within `h² K` of
`f''`. -/
theorem norm_deriv2_sub_clampedInterp_le_of_mem {t : ℝ} (ht : t ∈ Icc a b) :
    |iteratedDeriv 2 (clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b)) t
      - iteratedDeriv 2 f t| ≤ 7 / 4 * hm ^ 2 * K := by
  obtain ⟨i, hi1, hin, hmem, -⟩ := hx.exists_mem_panel hn ht
  have hpq : x (i - 1) < x i := hx.lt (by omega) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ⟨le_rfl, hx.le⟩)
  have hd : (0 : ℝ) < x i - x (i - 1) := sub_pos.mpr hpq
  have hmesh' : x i - x (i - 1) ≤ hm := by simpa [panelLength] using hmesh i hi1 hin
  have hlin := iteratedDeriv_two_clampedInterp_eq_of_mem hx hn (f := fun j => f (x j))
    (deriv f a) (deriv f b) hi1 hin hmem
  set s := clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b) with hs
  set p := x (i - 1) with hp
  set q := x i with hq
  have hlin' : iteratedDeriv 2 s t
      = iteratedDeriv 2 s p * (q - t) / (q - p) + iteratedDeriv 2 s q * (t - p) / (q - p) := hlin
  have hα : (0 : ℝ) ≤ (q - t) / (q - p) := div_nonneg (by linarith [hmem.2]) hd.le
  have hβ : (0 : ℝ) ≤ (t - p) / (q - p) := div_nonneg (by linarith [hmem.1]) hd.le
  have hαβ : (q - t) / (q - p) + (t - p) / (q - p) = 1 := by field_simp; ring
  have h1 : |iteratedDeriv 2 s p - iteratedDeriv 2 f p| ≤ 3 / 4 * hm ^ 2 * K :=
    norm_deriv2_sub_clampedInterp_le hx hn hf hK hmesh (by omega)
  have h2 : |iteratedDeriv 2 s q - iteratedDeriv 2 f q| ≤ 3 / 4 * hm ^ 2 * K :=
    norm_deriv2_sub_clampedInterp_le hx hn hf hK hmesh hin
  have h3 : |iteratedDeriv 2 f p * (q - t) / (q - p) + iteratedDeriv 2 f q * (t - p) / (q - p)
      - iteratedDeriv 2 f t| ≤ K * (q - p) ^ 2 :=
    abs_linearInterp_sub_le (contDiff_iteratedDeriv_two hf)
      (fun y hy => by rw [iteratedDeriv_iteratedDeriv_two]; exact hK y hy) hpq hsub hmem
  calc |iteratedDeriv 2 s t - iteratedDeriv 2 f t|
      = |((iteratedDeriv 2 s p - iteratedDeriv 2 f p) * ((q - t) / (q - p))
            + (iteratedDeriv 2 s q - iteratedDeriv 2 f q) * ((t - p) / (q - p)))
          + (iteratedDeriv 2 f p * (q - t) / (q - p) + iteratedDeriv 2 f q * (t - p) / (q - p)
            - iteratedDeriv 2 f t)| := by
        congr 1
        rw [hlin']
        ring
    _ ≤ |(iteratedDeriv 2 s p - iteratedDeriv 2 f p) * ((q - t) / (q - p))
            + (iteratedDeriv 2 s q - iteratedDeriv 2 f q) * ((t - p) / (q - p))|
          + |iteratedDeriv 2 f p * (q - t) / (q - p) + iteratedDeriv 2 f q * (t - p) / (q - p)
            - iteratedDeriv 2 f t| := abs_add_le _ _
    _ ≤ (3 / 4 * hm ^ 2 * K * ((q - t) / (q - p)) + 3 / 4 * hm ^ 2 * K * ((t - p) / (q - p)))
          + K * (q - p) ^ 2 := by
        refine add_le_add ?_ h3
        calc |(iteratedDeriv 2 s p - iteratedDeriv 2 f p) * ((q - t) / (q - p))
              + (iteratedDeriv 2 s q - iteratedDeriv 2 f q) * ((t - p) / (q - p))|
            ≤ |(iteratedDeriv 2 s p - iteratedDeriv 2 f p) * ((q - t) / (q - p))|
              + |(iteratedDeriv 2 s q - iteratedDeriv 2 f q) * ((t - p) / (q - p))| :=
              abs_add_le _ _
          _ = |iteratedDeriv 2 s p - iteratedDeriv 2 f p| * ((q - t) / (q - p))
              + |iteratedDeriv 2 s q - iteratedDeriv 2 f q| * ((t - p) / (q - p)) := by
              rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
          _ ≤ 3 / 4 * hm ^ 2 * K * ((q - t) / (q - p))
              + 3 / 4 * hm ^ 2 * K * ((t - p) / (q - p)) := by gcongr
    _ = 3 / 4 * hm ^ 2 * K + K * (q - p) ^ 2 := by rw [← mul_add, hαβ, mul_one]
    _ ≤ 3 / 4 * hm ^ 2 * K + K * hm ^ 2 := by
        have : (q - p) ^ 2 ≤ hm ^ 2 := by nlinarith
        nlinarith
    _ = 7 / 4 * hm ^ 2 * K := by ring

/-- **The clamped spline's slope approximates `f'` to third order**: `|s'(t) - f'(t)| ≤ (7/4) h³ K`
on `[a, b]`. The error `f - s` vanishes at both ends of every panel, so by Rolle's theorem its
derivative vanishes somewhere inside; the mean value theorem against the second-derivative bound
`norm_deriv2_sub_clampedInterp_le_of_mem` then costs one factor `h`. -/
theorem norm_deriv_sub_clampedInterp_le {t : ℝ} (ht : t ∈ Icc a b) :
    |deriv (clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b)) t - deriv f t|
      ≤ 7 / 4 * hm ^ 3 * K := by
  obtain ⟨i, hi1, hin, hmem, -⟩ := hx.exists_mem_panel hn ht
  have hpq : x (i - 1) < x i := hx.lt (by omega) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ⟨le_rfl, hx.le⟩)
  have hmesh' : x i - x (i - 1) ≤ hm := by simpa [panelLength] using hmesh i hi1 hin
  have hm0 : (0 : ℝ) ≤ hm := le_trans (by linarith) hmesh'
  set s := clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b) with hs
  have hs2 : ContDiff ℝ 2 s := contDiff_clampedInterp hx hn _ _
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hde : ∀ y, HasDerivAt (fun z => s z - f z) (deriv s y - deriv f y) y := fun y =>
    ((hs2.differentiable (by norm_num)) y).hasDerivAt.sub
      ((hf.differentiable (by norm_num)) y).hasDerivAt
  have hdde : ∀ y, HasDerivAt (fun z => deriv s z - deriv f z)
      (iteratedDeriv 2 s y - iteratedDeriv 2 f y) y := fun y =>
    (hasDerivAt_deriv_of_contDiff_two hs2 y).sub (hasDerivAt_deriv_of_contDiff_two hf2 y)
  have hderiv_e : deriv (fun z => s z - f z) = fun y => deriv s y - deriv f y :=
    funext fun y => (hde y).deriv
  have hnode : ∀ j ≤ n, s (x j) - f (x j) = 0 := fun j hj => by
    rw [hs, sub_eq_zero]; exact cubicInterp_apply_node hx hn hj
  obtain ⟨ξ, hξ, hξ0⟩ := exists_deriv_eq_zero (f := fun z => s z - f z) hpq
    (fun y _ => ((hde y).continuousAt).continuousWithinAt)
    (by rw [hnode (i - 1) (by omega), hnode i hin])
  rw [hderiv_e] at hξ0
  have hξm : ξ ∈ Icc (x (i - 1)) (x i) := Ioo_subset_Icc_self hξ
  have hbound : ∀ y ∈ Icc (x (i - 1)) (x i),
      ‖iteratedDeriv 2 s y - iteratedDeriv 2 f y‖ ≤ 7 / 4 * hm ^ 2 * K := fun y hy => by
    rw [Real.norm_eq_abs]
    exact norm_deriv2_sub_clampedInterp_le_of_mem hx hn hf hK hmesh (hsub hy)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => deriv s z - deriv f z)
    (f' := fun z => iteratedDeriv 2 s z - iteratedDeriv 2 f z)
    (fun y _ => (hdde y).hasDerivWithinAt) hbound (convex_Icc _ _) hξm hmem
  simp only [hξ0, sub_zero, Real.norm_eq_abs] at hmvt
  calc |deriv s t - deriv f t| ≤ 7 / 4 * hm ^ 2 * K * |t - ξ| := hmvt
    _ ≤ 7 / 4 * hm ^ 2 * K * hm := by
        have habs : |t - ξ| ≤ hm := by
          rw [abs_sub_le_iff]
          constructor <;> [linarith [hmem.2, hξm.1]; linarith [hmem.1, hξm.2]]
        gcongr
    _ = 7 / 4 * hm ^ 3 * K := by ring

/-- **An `O(h⁴)` error bound for the clamped cubic spline with explicit constants**, behind
[quarteroni2000numerical] Property 8.3: for `f` of class `C⁴` with `|f⁗| ≤ K` on `[a, b]` and panel
lengths at most `h`, the clamped interpolatory spline `s` of the nodal values of `f` satisfies
`|s(t) - f(t)| ≤ (7/8) h⁴ K` on `[a, b]`.

The error vanishes at both ends of every panel, so the mean value theorem against
`norm_deriv_sub_clampedInterp_le` applied from either end gives `|s - f| ≤ (7/4) h³ K · h/2`.

The constants are those of Stoer and Bulirsch, *Introduction to Numerical Analysis*,
Theorem 2.4.3.3, not the sharp constants `5/384, 1/24, 3/8` of Hall and Meyer, *Optimal error
bounds for cubic spline interpolation* (J. Approx. Theory 16, 1976). -/
theorem norm_sub_clampedInterp_le {t : ℝ} (ht : t ∈ Icc a b) :
    |clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b) t - f t|
      ≤ 7 / 8 * hm ^ 4 * K := by
  obtain ⟨i, hi1, hin, hmem, -⟩ := hx.exists_mem_panel hn ht
  have hpq : x (i - 1) < x i := hx.lt (by omega) hin
  have hsub : Icc (x (i - 1)) (x i) ⊆ Icc a b :=
    Icc_subset_Icc (hx.left_le (by omega)) (hx.le_right hin)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ⟨le_rfl, hx.le⟩)
  have hmesh' : x i - x (i - 1) ≤ hm := by simpa [panelLength] using hmesh i hi1 hin
  have hm0 : (0 : ℝ) ≤ hm := le_trans (by linarith) hmesh'
  set s := clampedInterp n x (fun j => f (x j)) (deriv f a) (deriv f b) with hs
  have hs2 : ContDiff ℝ 2 s := contDiff_clampedInterp hx hn _ _
  have hde : ∀ y, HasDerivAt (fun z => s z - f z) (deriv s y - deriv f y) y := fun y =>
    ((hs2.differentiable (by norm_num)) y).hasDerivAt.sub
      ((hf.differentiable (by norm_num)) y).hasDerivAt
  have hnode : ∀ j ≤ n, s (x j) - f (x j) = 0 := fun j hj => by
    rw [hs, sub_eq_zero]; exact cubicInterp_apply_node hx hn hj
  have hbound : ∀ y ∈ Icc (x (i - 1)) (x i), ‖deriv s y - deriv f y‖ ≤ 7 / 4 * hm ^ 3 * K :=
    fun y hy => by
      rw [Real.norm_eq_abs]
      exact norm_deriv_sub_clampedInterp_le hx hn hf hK hmesh (hsub hy)
  have hmvt : ∀ y ∈ Icc (x (i - 1)) (x i), ∀ z ∈ Icc (x (i - 1)) (x i),
      ‖(s z - f z) - (s y - f y)‖ ≤ 7 / 4 * hm ^ 3 * K * ‖z - y‖ := fun y hy z hz =>
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun w => s w - f w)
      (f' := fun w => deriv s w - deriv f w) (fun w _ => (hde w).hasDerivWithinAt) hbound
      (convex_Icc _ _) hy hz
  have h1 := hmvt _ ⟨le_rfl, hpq.le⟩ t hmem
  have h2 := hmvt _ ⟨hpq.le, le_rfl⟩ t hmem
  rw [hnode (i - 1) (by omega), sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [hmem.1] : (0:ℝ) ≤ t - x (i - 1))] at h1
  rw [hnode i hin, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm t (x i),
    abs_of_nonneg (by linarith [hmem.2] : (0:ℝ) ≤ x i - t)] at h2
  have hC : (0 : ℝ) ≤ 7 / 4 * hm ^ 3 * K := by positivity
  nlinarith [h1, h2, mul_le_mul_of_nonneg_left hmesh' hC]

end Bounds

end ClampedError

end Spline
