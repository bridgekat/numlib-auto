import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Complex.ExponentialBounds
import Numlib.Approximation.DividedDifference
import Numlib.Approximation.NewtonForm

/-!
# Runge's phenomenon

Runge's counterexample ([quarteroni2000numerical] Example 8.1): the Lagrange interpolants of
`f(s) = 1/(1 + s²)` on `[-5, 5]` at the equispaced nodes `x_j = -5 + 10j/n`, `j = 0, …, n`, do
not converge to `f` at every point of the interval. The point exhibited is `t = 4.9`, along the
odd `n`, where the interpolation error is at least `1` for every odd `n ≥ 401`
(`Runge.one_le_abs_sub_interpolate`), so that `Π_n f(t) ↛ f(t)` (`Runge.not_tendsto_interpolate`).

## The route (real-variable, no contour integral)

* `Runge.newton_runge`: the divided difference of `f` at distinct real nodes is
  `Re (I / ∏_i (I - x_i))`, from the partial fraction `1/(1 + s²) = Re (I/(I - s))` and the
  Cauchy-kernel divided difference `DividedDifference.newtonOn_inv_sub` over `ℂ`.
* `Runge.exists_prod_I_sub_node_eq`: for `n` odd the symmetric node set makes `∏_j (I - x_j)`
  real, and `Runge.abs_sub_interpolate_eq` gives the **exact error**
  `|f(t) - Π_n f(t)| = ∏_j |t - x_j| / ((1 + t²) ∏_j ‖I - x_j‖)` at every non-node `t`, by
  `DividedDifference.sub_eval_interpolate_eq_newton`.
* The two products are `exp` of sums of logarithms, compared with integrals through Mathlib's
  monotone Riemann-sum lemmas (`AntitoneOn.integral_le_sum`, `MonotoneOn.integral_le_sum`,
  `MonotoneOn.sum_le_integral`) and `integral_log`: `Runge.sum_log_abs_sub_ge` bounds
  `∑_j log|t - x_j|` below by `(n/10)(9.9 log 9.9 - 10 - 0.1 log 10) - 2 log(10n)` (the two
  nodes nearest to `t` are handled by the separation `|t - x_j| ≥ 1/(10n)`, which is where the
  rational `t` and the odd `n` enter), and `Runge.sum_log_one_add_abs_le` bounds
  `∑_j log(1 + |x_j|) ≥ ∑_j log ‖I - x_j‖` above by `(n/10)(12 log 6 - 10) + 2 log 16`.
* `Runge.margin`: the difference exceeds `log(1 + t²)` for `n ≥ 400`, with certified bounds on
  `log 9.9`, `log 10`, `log 6`, `log 16`, `log 25.01` from `Real.exp_one_gt_d9`,
  `Real.exp_one_lt_d9`, `Real.log_two_lt_d9`, `Real.quadratic_le_exp_of_nonneg` and
  `Real.exp_bound'`.

The threshold `n ≥ 401` and the constants are far from sharp (the divergence holds for every
`|t| > 3.63…`, the book's figure), but the statement `¬ Tendsto` needs one point and a
subsequence only.
-/

open Finset Set Complex
open scoped Real

namespace Runge

/-! ### The Runge function and its divided differences -/

/-- **The Runge function** `f(s) = 1/(1 + s²)` of [quarteroni2000numerical] (8.12). -/
noncomputable def runge (s : ℝ) : ℝ := 1 / (1 + s ^ 2)

/-- The partial fraction `1/(1 + s²) = Re (I / (I - s))`. -/
theorem runge_eq_re (s : ℝ) : runge s = (I / (I - (s : ℂ))).re := by
  rw [runge, Complex.div_re]
  simp [Complex.normSq_apply]
  ring

/-- `I` is not a real number. -/
theorem I_ne_ofReal (s : ℝ) : (I : ℂ) ≠ (s : ℂ) := fun h => by
  have := congrArg Complex.im h
  simp at this

/-- **The divided difference of the Runge function** at distinct real nodes is the real part of
`I / ∏_i (I - x_i)`: the partial fraction `1/(1 + s²) = Re (I/(I - s))` and the Cauchy-kernel
divided difference `DividedDifference.newtonOn_inv_sub` over `ℂ`, the denominators of the
explicit sum `DividedDifference.newton` being real. -/
theorem newton_runge {m : ℕ} {v : Fin (m + 1) → ℝ} (hv : Function.Injective v) :
    DividedDifference.newton runge v = (I / ∏ i, (I - (v i : ℂ))).re := by
  classical
  have hinj : Set.InjOn (fun i => (v i : ℂ)) (univ : Finset (Fin (m + 1))) :=
    fun i _ j _ h => hv (Complex.ofReal_injective h)
  have h1 : I / ∏ i, (I - (v i : ℂ))
      = I * DividedDifference.newtonOn univ (fun i => (v i : ℂ)) (fun s => 1 / (I - s)) := by
    rw [DividedDifference.newtonOn_inv_sub hinj univ_nonempty fun i _ => I_ne_ofReal (v i)]
    ring
  rw [h1, DividedDifference.newtonOn, Finset.mul_sum, Complex.re_sum, DividedDifference.newton]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : (∏ j ∈ univ.erase i, ((v i : ℂ) - v j))
      = ((∏ j ∈ univ.erase i, (v i - v j) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hd, ← mul_div_assoc, Complex.div_ofReal_re, runge_eq_re]
  congr 1
  rw [mul_one_div]

/-! ### The equispaced nodes -/

/-- **The equispaced nodes** `x_j = -5 + 10 j/n`, `j = 0, …, n`, of Runge's example. -/
noncomputable def node (n : ℕ) (j : Fin (n + 1)) : ℝ := -5 + 10 * (j : ℝ) / n

/-- The `ℕ`-indexed node `x_j = -5 + 10 j/n`, for the sums over `Finset.range (n + 1)`. -/
noncomputable def xr (n j : ℕ) : ℝ := -5 + 10 * (j : ℝ) / n

/-- The two indexings agree. -/
theorem node_eq_xr (n : ℕ) (j : Fin (n + 1)) : node n j = xr n j := rfl

/-- The nodes are symmetric: `x_{n-j} = -x_j`. -/
theorem node_rev {n : ℕ} (hn : n ≠ 0) (j : Fin (n + 1)) : node n (Fin.rev j) = -node n j := by
  simp only [node, Fin.val_rev]
  have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.2
  rw [show n + 1 - (j + 1) = n - j by omega, Nat.cast_sub hj]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp
  ring

/-- The nodes are distinct. -/
theorem node_injective {n : ℕ} (hn : n ≠ 0) : Function.Injective (node n) := fun i j h => by
  simp only [node] at h
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have : (i : ℝ) = j := by
    have h' : 10 * (i : ℝ) / n = 10 * (j : ℝ) / n := by linarith
    rw [div_left_inj' hn'] at h'
    linarith
  exact Fin.ext (Nat.cast_injective this)

/-- **`∏_j (I - x_j)` is real** for the symmetric equispaced nodes with `n` odd (an even number of
nodes): its conjugate is `∏_j (-I - x_j) = ∏_j (-(I - x_{n-j}))`, which is the product itself
because `(-1)^{n+1} = 1`. -/
theorem exists_prod_I_sub_node_eq {n : ℕ} (hn : Odd n) :
    ∃ r : ℝ, ∏ j, (I - (node n j : ℂ)) = r := by
  rw [← Complex.conj_eq_iff_real, map_prod]
  simp only [map_sub, Complex.conj_I, Complex.conj_ofReal]
  calc ∏ j, (-I - (node n j : ℂ)) = ∏ j, (-I - (node n (Fin.revPerm j) : ℂ)) :=
        (Equiv.prod_comp Fin.revPerm fun j => -I - (node n j : ℂ)).symm
    _ = ∏ j, -(I - (node n j : ℂ)) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Fin.revPerm_apply, node_rev hn.pos.ne' j]
        push_cast
        ring
    _ = ∏ j, (I - (node n j : ℂ)) := by
        rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin, (hn.add_one).neg_one_pow, one_mul]

/-- **The interpolation error of the Runge function** at a point `t` which is not a node, for the
equispaced nodes with `n` odd:

  `|f(t) - Π_n f(t)| = ∏_j |t - x_j| / ((1 + t²) ∏_j ‖I - x_j‖)`.

By `DividedDifference.sub_eval_interpolate_eq_newton` the error is
`ω_{n+1}(t) f[x_0, …, x_n, t]`, and `newton_runge` with `exists_prod_I_sub_node_eq` evaluate the
divided difference as `Re (I / (r (I - t))) = 1/(r (1 + t²))` for the real number
`r = ∏_j (I - x_j)`. -/
theorem abs_sub_interpolate_eq {n : ℕ} (hn : Odd n) {t : ℝ} (ht : ∀ j, node n j ≠ t) :
    |runge t - (Lagrange.interpolate univ (node n) fun j => runge (node n j)).eval t|
      = (∏ j, |t - node n j|) / ((1 + t ^ 2) * ∏ j, ‖I - (node n j : ℂ)‖) := by
  have hn0 : n ≠ 0 := hn.pos.ne'
  rw [DividedDifference.sub_eval_interpolate_eq_newton runge (node_injective hn0) ht,
    newton_runge (Fin.snoc_injective_of_injective (node_injective hn0)
      fun ⟨j, hj⟩ => ht j hj)]
  rw [Fin.prod_univ_castSucc (n := n + 1)]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  obtain ⟨r, hr⟩ := exists_prod_I_sub_node_eq hn
  have hr0 : (r : ℂ) ≠ 0 := by
    rw [← hr]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (I_ne_ofReal _)
  have hIt : (I - (t : ℂ)) ≠ 0 := sub_ne_zero.mpr (I_ne_ofReal t)
  have hsplit : I / ((r : ℂ) * (I - t)) = ((r⁻¹ : ℝ) : ℂ) * (I / (I - t)) := by
    push_cast
    field_simp
  rw [hr, hsplit, Complex.re_ofReal_mul, ← runge_eq_re, runge, abs_mul, abs_mul, abs_inv,
    Finset.abs_prod, abs_div, abs_one, abs_of_pos (by positivity : (0 : ℝ) < 1 + t ^ 2)]
  have hnorm : |r| = ∏ j, ‖I - (node n j : ℂ)‖ := by
    rw [← norm_prod, hr, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  have hpos : 0 < ∏ j, ‖I - (node n j : ℂ)‖ := by
    rw [← hnorm]
    exact abs_pos.mpr (Complex.ofReal_ne_zero.mp hr0)
  field_simp

/-! ### The two Riemann sums -/

/-- The primitive `G(r) = r log r - r` of `log` is nonpositive on `(0, 1]`. -/
theorem primitive_log_nonpos {a : ℝ} (h0 : 0 < a) (h1 : a ≤ 1) : a * Real.log a - a ≤ 0 := by
  have : Real.log a ≤ 0 := Real.log_nonpos h0.le h1
  nlinarith

/-- **The sum `∑_j log(1 + |x_j|)` over the equispaced nodes, `n` odd**, is at most
`(n/10)(12 log 6 - 10) + 2 log 16` when `n ≥ 10`: by symmetry it is twice the sum over the
positive nodes `h(m + 1/2)`, `m < (n+1)/2`, which is a lower Riemann sum of `log(1 + s)` on
`[1 + h/2, 6 + h]` with step `h = 10/n`. -/
theorem sum_log_one_add_abs_le {n : ℕ} (hn : Odd n) (hn10 : 10 ≤ n) :
    ∑ j ∈ range (n + 1), Real.log (1 + |xr n j|)
      ≤ (n / 10) * (12 * Real.log 6 - 10) + 2 * Real.log 16 := by
  obtain ⟨N, hN⟩ : ∃ N, n + 1 = N + N := ⟨(n + 1) / 2, by obtain ⟨k, rfl⟩ := hn; omega⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set h : ℝ := 10 / n with hh
  have hpos : 0 < h := by positivity
  have hle1 : h ≤ 1 := by
    rw [hh, div_le_one hnpos]
    exact_mod_cast hn10
  have hNn : (N : ℝ) = ((n : ℝ) + 1) / 2 := by
    have : (n : ℝ) + 1 = N + N := by exact_mod_cast hN
    linarith
  -- the positive nodes: `x_{N+m} = h (m + 1/2)`
  have hxpos : ∀ m : ℕ, xr n (N + m) = h * (m + 1 / 2) := by
    intro m
    rw [xr, hh]
    push_cast
    rw [hNn]
    field_simp
    ring
  -- symmetry: `|x_{N-1-m}| = |x_{N+m}|`
  have hsymm : ∀ m ∈ range N, |xr n (N - 1 - m)| = |xr n (N + m)| := by
    intro m hm
    rw [Finset.mem_range] at hm
    have : xr n (N - 1 - m) = -xr n (N + m) := by
      rw [xr, xr]
      have e : ((N - 1 - m : ℕ) : ℝ) = (n : ℝ) - (N + m : ℕ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        push_cast
        have : (n : ℝ) + 1 = N + N := by exact_mod_cast hN
        linarith
      rw [e]
      push_cast
      field_simp
      ring
    rw [this, abs_neg]
  -- fold the sum onto the positive nodes
  have hfold : ∑ j ∈ range (n + 1), Real.log (1 + |xr n j|)
      = 2 * ∑ m ∈ range N, Real.log (1 + h * (m + 1 / 2)) := by
    rw [hN, Finset.sum_range_add, ← Finset.sum_range_reflect, two_mul]
    congr 1
    · exact Finset.sum_congr rfl fun m hm => by rw [hsymm m hm, hxpos, abs_of_pos (by positivity)]
    · exact Finset.sum_congr rfl fun m _ => by rw [hxpos, abs_of_pos (by positivity)]
  rw [hfold]
  -- the Riemann sum
  have hmono : MonotoneOn (fun u : ℝ => Real.log (1 + h * (u + 1 / 2))) (Icc 0 (0 + N)) := by
    intro u hu u' hu' huu'
    exact Real.log_le_log (by nlinarith [hu.1]) (by nlinarith)
  have hsum : ∑ m ∈ range N, Real.log (1 + h * (m + 1 / 2))
      ≤ ∫ u in (0 : ℝ)..0 + N, Real.log (1 + h * (u + 1 / 2)) := by
    have := hmono.sum_le_integral
    simpa using this
  -- the integral: substitute `r = 1 + h/2 + h u`
  have hint : ∫ u in (0 : ℝ)..0 + N, Real.log (1 + h * (u + 1 / 2))
      = h⁻¹ * ∫ r in (1 + h / 2)..(6 + h), Real.log r := by
    have e : (fun u : ℝ => Real.log (1 + h * (u + 1 / 2)))
        = fun u => Real.log (h * u + (1 + h / 2)) := by
      funext u; ring_nf
    rw [e, intervalIntegral.integral_comp_mul_add Real.log hpos.ne' (1 + h / 2), smul_eq_mul]
    congr 2
    · ring
    · rw [hNn, hh]; field_simp; ring
  -- bound the integral
  have hI : ∫ r in (1 + h / 2)..(6 + h), Real.log r ≤ 6 * Real.log 6 - 5 + h * Real.log 16 := by
    have h1 : (1 : ℝ) ≤ 1 + h / 2 := by linarith
    have h6h : (6 : ℝ) ≤ 6 + h := by linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 6)
      intervalIntegral.intervalIntegrable_log' intervalIntegral.intervalIntegrable_log',
      ← intervalIntegral.integral_add_adjacent_intervals (b := 1) (a := 1 + h / 2)
      intervalIntegral.intervalIntegrable_log' intervalIntegral.intervalIntegrable_log']
    have hA : ∫ r in (1 + h / 2)..1, Real.log r ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      refine neg_nonpos.mpr (intervalIntegral.integral_nonneg h1 fun r hr => ?_)
      exact Real.log_nonneg hr.1
    have hB : ∫ r in (1 : ℝ)..6, Real.log r = 6 * Real.log 6 - 5 := by
      rw [integral_log]
      simp
      ring
    have hC : ∫ r in (6 : ℝ)..6 + h, Real.log r ≤ h * Real.log 16 := by
      calc ∫ r in (6 : ℝ)..6 + h, Real.log r ≤ ∫ _r in (6 : ℝ)..6 + h, Real.log 16 :=
            intervalIntegral.integral_mono_on h6h intervalIntegral.intervalIntegrable_log'
              intervalIntegrable_const fun r hr =>
                Real.log_le_log (by linarith [hr.1]) (by linarith [hr.2])
        _ = h * Real.log 16 := by simp
    linarith
  have hfinal : ∑ m ∈ range N, Real.log (1 + h * (m + 1 / 2))
      ≤ h⁻¹ * (6 * Real.log 6 - 5 + h * Real.log 16) := by
    refine hsum.trans ?_
    rw [hint]
    exact mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hpos.le)
  calc 2 * ∑ m ∈ range N, Real.log (1 + h * (m + 1 / 2))
      ≤ 2 * (h⁻¹ * (6 * Real.log 6 - 5 + h * Real.log 16)) := by gcongr
    _ = (n / 10) * (12 * Real.log 6 - 10) + 2 * Real.log 16 := by
        rw [hh]
        field_simp
        ring

/-- **`t = 4.9` is separated from the equispaced nodes by `1/(10n)`** when `n` is odd:
`t - x_j = (99n - 100j)/(10n)` with a nonzero integer numerator. -/
theorem sep_le_abs_sub {n : ℕ} (hn : Odd n) (j : ℕ) : 1 / (10 * n) ≤ |49 / 10 - xr n j| := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hne : (99 * n : ℤ) - 100 * j ≠ 0 := by
    obtain ⟨k, rfl⟩ := hn
    omega
  have h1 : (1 : ℝ) ≤ |(((99 * n : ℤ) - 100 * j : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  have e : (49 / 10 : ℝ) - xr n j = ((99 * n : ℤ) - 100 * j : ℤ) / (10 * n) := by
    rw [xr]
    push_cast
    field_simp
    ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 10 * n)]
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- **The sum `∑_j log|t - x_j|` at `t = 4.9` over the equispaced nodes, `n` odd, `n ≥ 200`**,
is at least `(n/10)(9.9 log 9.9 - 10 - 0.1 log 10) - 2 log(10n)`: the nodes left of `t` other
than the nearest give an upper Riemann sum of `log(t - s)` on `[-5, x_{J-1}]`, those right of `t`
other than the nearest one of `log(s - t)` on `[x_J, 5]`, and the two nearest nodes are handled
by the separation `sep_le_abs_sub`. -/
theorem sum_log_abs_sub_ge {n : ℕ} (hn : Odd n) (hn200 : 200 ≤ n) :
    (n / 10) * ((99 / 10) * Real.log (99 / 10) - 10 - (1 / 10) * Real.log 10)
        - 2 * Real.log (10 * n)
      ≤ ∑ j ∈ range (n + 1), Real.log |49 / 10 - xr n j| := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.pos
  set h : ℝ := 10 / n with hh
  have hpos : 0 < h := by positivity
  have hle1 : h ≤ 1 := by
    rw [hh, div_le_one hnpos]
    exact_mod_cast (by omega : 10 ≤ n)
  have hxr : ∀ j : ℕ, xr n j = -5 + h * j := fun j => by rw [xr, hh]; ring
  -- the index `J` of the first node to the right of `t`
  set J : ℕ := 99 * n / 100 + 1 with hJ
  have hJ1 : 1 ≤ J := by omega
  have hJn : J + 1 ≤ n := by omega
  have hleft : ∀ j, j < J → xr n j < 49 / 10 := by
    intro j hj
    have : 100 * j ≤ 99 * n := by omega
    have hne : 100 * j ≠ 99 * n := by
      obtain ⟨k, rfl⟩ := hn
      omega
    have hlt : (100 * j : ℝ) < 99 * n := by exact_mod_cast lt_of_le_of_ne this hne
    rw [xr, ← sub_pos]
    have : (49 / 10 : ℝ) - (-5 + 10 * j / n) = (99 * n - 100 * j) / (10 * n) := by
      field_simp
      ring
    rw [this]
    positivity
  have hright : ∀ j, J ≤ j → 49 / 10 < xr n j := by
    intro j hj
    have : 99 * n < 100 * j := by omega
    have hlt : (99 * n : ℝ) < 100 * j := by exact_mod_cast this
    rw [xr, ← sub_pos]
    have : (-5 + 10 * (j : ℝ) / n) - 49 / 10 = (100 * j - 99 * n) / (10 * n) := by
      field_simp
      ring
    rw [this]
    positivity
  -- the two nearest nodes
  have hsep : ∀ j, -Real.log (10 * n) ≤ Real.log |49 / 10 - xr n j| := by
    intro j
    rw [← Real.log_inv, ← one_div]
    exact Real.log_le_log (by positivity) (sep_le_abs_sub hn j)
  -- split the sum
  have hsplit : ∑ j ∈ range (n + 1), Real.log |49 / 10 - xr n j|
      = ∑ j ∈ range (J - 1), Real.log |49 / 10 - xr n j|
        + Real.log |49 / 10 - xr n (J - 1)| + Real.log |49 / 10 - xr n J|
        + ∑ i ∈ range (n - J), Real.log |49 / 10 - xr n (J + 1 + i)| := by
    rw [show n + 1 = (J + 1) + (n - J) by omega, Finset.sum_range_add,
      show J + 1 = (J - 1) + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      show J - 1 + 1 = J by omega]
  rw [hsplit]
  -- the left Riemann sum
  have hL : (n / 10) * ((99 / 10) * Real.log (99 / 10) - 99 / 10)
      ≤ ∑ j ∈ range (J - 1), Real.log |49 / 10 - xr n j| := by
    have hanti : AntitoneOn (fun u : ℝ => Real.log (49 / 10 + 5 - h * u))
        (Icc 0 (0 + ((J - 1 : ℕ) : ℝ))) := by
      intro u hu u' hu' huu'
      have hJ' : h * ((J - 1 : ℕ) : ℝ) < 49 / 10 + 5 := by
        have := hleft (J - 1) (by omega)
        rw [hxr] at this
        linarith
      refine Real.log_le_log ?_ (by nlinarith)
      nlinarith [hu'.2]
    have hint := hanti.integral_le_sum
    have hval : ∀ i ∈ range (J - 1), Real.log |49 / 10 - xr n i|
        = Real.log (49 / 10 + 5 - h * (0 + (i : ℝ))) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [abs_of_pos (sub_pos.mpr (hleft i (by omega))), hxr]
      ring_nf
    rw [Finset.sum_congr rfl hval]
    refine le_trans ?_ hint
    -- the integral
    have e : (fun u : ℝ => Real.log (49 / 10 + 5 - h * u))
        = fun u => Real.log (-h * u + (49 / 10 + 5)) := by
      funext u; ring_nf
    rw [e, intervalIntegral.integral_comp_mul_add Real.log (neg_ne_zero.mpr hpos.ne') _,
      smul_eq_mul, integral_log]
    set a : ℝ := -h * (0 + ((J - 1 : ℕ) : ℝ)) + (49 / 10 + 5) with ha
    have ha0 : 0 < a := by
      have := hleft (J - 1) (by omega)
      rw [hxr] at this
      rw [ha]; linarith
    have ha1 : a ≤ 1 := by
      have := hright J le_rfl
      rw [hxr] at this
      rw [ha, Nat.cast_sub hJ1]; push_cast; linarith
    have hG := primitive_log_nonpos ha0 ha1
    have hmul : -h * 0 + (49 / 10 + 5) = 99 / 10 := by ring
    rw [hmul]
    have : (n : ℝ) / 10 = -(-h)⁻¹ := by rw [hh]; field_simp
    rw [this]
    have hneg : (-h)⁻¹ < 0 := inv_lt_zero.mpr (neg_neg_iff_pos.mpr hpos)
    nlinarith
  -- the right Riemann sum
  have hR : (n / 10) * ((1 / 10) * Real.log (1 / 10) - 1 / 10)
      ≤ ∑ i ∈ range (n - J), Real.log |49 / 10 - xr n (J + 1 + i)| := by
    set b : ℝ := xr n (J + 1) - 49 / 10 with hb
    have hb0 : h < b := by
      have := hright J le_rfl
      rw [hxr] at this
      rw [hb, hxr]; push_cast; linarith
    have hmono : MonotoneOn (fun u : ℝ => Real.log (b + h * u))
        (Icc (-1) (-1 + ((n - J : ℕ) : ℝ))) := by
      intro u hu u' hu' huu'
      refine Real.log_le_log ?_ (by nlinarith)
      nlinarith [hu.1]
    have hint := hmono.integral_le_sum
    have hval : ∀ i ∈ range (n - J), Real.log |49 / 10 - xr n (J + 1 + i)|
        = Real.log (b + h * (-1 + ((i + 1 : ℕ) : ℝ))) := by
      intro i _
      rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (hright _ (by omega))), hb, hxr, hxr]
      push_cast
      ring_nf
    rw [Finset.sum_congr rfl hval]
    refine le_trans ?_ hint
    have e : (fun u : ℝ => Real.log (b + h * u)) = fun u => Real.log (h * u + b) := by
      funext u; ring_nf
    rw [e, intervalIntegral.integral_comp_mul_add Real.log hpos.ne' _, smul_eq_mul, integral_log]
    have hc : h * (-1) + b = xr n J - 49 / 10 := by rw [hb, hxr, hxr]; push_cast; ring
    have hd : h * (-1 + ((n - J : ℕ) : ℝ)) + b = 1 / 10 := by
      rw [hb, hxr, hh, Nat.cast_sub (by omega : J ≤ n)]
      push_cast
      field_simp
      ring
    rw [hc, hd]
    have hc0 : 0 < xr n J - 49 / 10 := sub_pos.mpr (hright J le_rfl)
    have hc1 : xr n J - 49 / 10 ≤ 1 := by
      have := hleft (J - 1) (by omega)
      rw [hxr, Nat.cast_sub hJ1] at this
      push_cast at this
      rw [hxr]; linarith
    have hG := primitive_log_nonpos hc0 hc1
    have : (n : ℝ) / 10 = h⁻¹ := by rw [hh]; field_simp
    rw [this]
    have hinvpos : 0 < h⁻¹ := inv_pos.mpr hpos
    nlinarith
  have hlog10 : Real.log (1 / 10) = -Real.log 10 := by
    rw [one_div, Real.log_inv]
  have := hsep (J - 1)
  have := hsep J
  rw [hlog10] at hR
  linarith

/-! ### Certified numerical constants -/

/-- `log 10 ≤ 2.4`: `10 ≤ e² · e^{0.4}` with `e > 2.7182818283` and `e^{0.4} ≥ 1.48`. -/
theorem log_ten_le : Real.log 10 ≤ 12 / 5 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (12 / 5 : ℝ) = 1 + 1 + 2 / 5 by norm_num,
    Real.exp_add, Real.exp_add]
  have h1 := Real.exp_one_gt_d9
  have h2 : 1 + 2 / 5 + (2 / 5) ^ 2 / 2 ≤ Real.exp (2 / 5) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have he : (2.7182818283 : ℝ) * 2.7182818283 ≤ Real.exp 1 * Real.exp 1 :=
    mul_le_mul h1.le h1.le (by norm_num) (Real.exp_pos 1).le
  calc (10 : ℝ) ≤ 2.7182818283 * 2.7182818283 * (1 + 2 / 5 + (2 / 5) ^ 2 / 2) := by norm_num
    _ ≤ Real.exp 1 * Real.exp 1 * Real.exp (2 / 5) :=
        mul_le_mul he h2 (by norm_num) (by positivity)

/-- `log 3 ≤ 1.1`: `3 ≤ e · e^{0.1}` with `e^{0.1} ≥ 1.105`. -/
theorem log_three_le : Real.log 3 ≤ 11 / 10 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num,
    Real.exp_add]
  have h1 := Real.exp_one_gt_d9
  have h2 : 1 + 1 / 10 + (1 / 10) ^ 2 / 2 ≤ Real.exp (1 / 10) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  calc (3 : ℝ) ≤ 2.7182818283 * (1 + 1 / 10 + (1 / 10) ^ 2 / 2) := by norm_num
    _ ≤ Real.exp 1 * Real.exp (1 / 10) := mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le

/-- `log 6 ≤ 1.7932`, from `log 2 < 0.6931471808` and `log 3 ≤ 1.1`. -/
theorem log_six_le : Real.log 6 ≤ 17932 / 10000 := by
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul two_ne_zero three_ne_zero]
  linarith [Real.log_two_lt_d9, log_three_le]

/-- `log 16 = 4 log 2 ≤ 2.773`. -/
theorem log_sixteen_le : Real.log 16 ≤ 2773 / 1000 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  linarith [Real.log_two_lt_d9]

/-- `log 9.9 ≥ 2.29`: `e^{2.29} = e² e^{0.29} ≤ 2.7182818286² · 1.3364833 < 9.9`, the last factor
from the Taylor bound `Real.exp_bound'` at order `4`. -/
theorem le_log_nine_point_nine : 229 / 100 ≤ Real.log (99 / 10) := by
  rw [Real.le_log_iff_exp_le (by norm_num), show (229 / 100 : ℝ) = 1 + 1 + 29 / 100 by norm_num,
    Real.exp_add, Real.exp_add]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_bound' (x := 29 / 100) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  have he : Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 :=
    mul_le_mul h1.le h1.le (Real.exp_pos 1).le (by norm_num)
  calc Real.exp 1 * Real.exp 1 * Real.exp (29 / 100)
      ≤ 2.7182818286 * 2.7182818286 * (13364833 / 10000000) :=
        mul_le_mul he (by linarith) (Real.exp_pos _).le (by norm_num)
    _ ≤ 99 / 10 := by norm_num

/-- `log(1 + 4.9²) = log 25.01 ≤ 3.3`: `25.01 ≤ e³ e^{0.3}`. -/
theorem log_one_add_sq_le : Real.log (1 + (49 / 10) ^ 2) ≤ 33 / 10 := by
  rw [Real.log_le_iff_le_exp (by norm_num), show (33 / 10 : ℝ) = 1 + 1 + 1 + 3 / 10 by norm_num,
    Real.exp_add, Real.exp_add, Real.exp_add]
  have h1 := Real.exp_one_gt_d9
  have h2 : 1 + 3 / 10 + (3 / 10) ^ 2 / 2 ≤ Real.exp (3 / 10) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have he : (2.7182818283 : ℝ) * 2.7182818283 ≤ Real.exp 1 * Real.exp 1 :=
    mul_le_mul h1.le h1.le (by norm_num) (Real.exp_pos 1).le
  have he3 : (2.7182818283 : ℝ) * 2.7182818283 * 2.7182818283
      ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 :=
    mul_le_mul he h1.le (by norm_num) (by positivity)
  calc (1 + (49 / 10) ^ 2 : ℝ)
      ≤ 2.7182818283 * 2.7182818283 * 2.7182818283 * (1 + 3 / 10 + (3 / 10) ^ 2 / 2) := by
        norm_num
    _ ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (3 / 10) :=
        mul_le_mul he3 h2 (by norm_num) (by positivity)

/-- `log n ≤ n/100 + 2 log 10 - 1` for `n ≥ 1`, from `log x ≤ x - 1` at `x = n/100`. -/
theorem log_nat_le (n : ℕ) (hn : 1 ≤ n) : Real.log n ≤ n / 100 + 2 * Real.log 10 - 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < n / 100)
  rw [Real.log_div hnpos.ne' (by norm_num), show (100 : ℝ) = 10 ^ 2 by norm_num,
    Real.log_pow] at this
  push_cast at this
  linarith

/-- **The margin of Runge's example at `t = 4.9`**: for `n ≥ 400`,
`(n/10)(9.9 log 9.9 - 10 - 0.1 log 10) - 2 log(10n) - (n/10)(12 log 6 - 10) - 2 log 16`
exceeds `log(1 + 4.9²)`. The coefficient of `n/10` is at least `0.91`, and the remaining terms
are `O(1) + 2 log n ≤ O(1) + n/50`. -/
theorem margin (n : ℕ) (hn : 400 ≤ n) :
    Real.log (1 + (49 / 10) ^ 2)
      ≤ (n / 10) * ((99 / 10) * Real.log (99 / 10) - 10 - (1 / 10) * Real.log 10)
        - 2 * Real.log (10 * n) - ((n / 10) * (12 * Real.log 6 - 10) + 2 * Real.log 16) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn' : (400 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.log_mul (by norm_num) hnpos.ne']
  have h1 := le_log_nine_point_nine
  have h2 := log_ten_le
  have h3 := log_six_le
  have h4 := log_sixteen_le
  have h5 := log_one_add_sq_le
  have h6 := log_nat_le n (by omega)
  have hkey : (n / 10) * (91 / 100)
      ≤ (n / 10) * ((99 / 10) * Real.log (99 / 10) - 10 - (1 / 10) * Real.log 10)
        - (n / 10) * (12 * Real.log 6 - 10) := by
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  linarith

/-! ### Divergence at `t = 4.9` -/

/-- **The interpolation error at `t = 4.9` is at least `1` for every odd `n ≥ 401`**: the exact
error `abs_sub_interpolate_eq`, the products written as `exp` of the sums of logarithms,
`‖I - x_j‖ ≤ 1 + |x_j|`, the two Riemann-sum bounds and the numerical margin. -/
theorem one_le_abs_sub_interpolate {n : ℕ} (hn : Odd n) (hn400 : 400 ≤ n) :
    1 ≤ |runge (49 / 10)
      - (Lagrange.interpolate univ (node n) fun j => runge (node n j)).eval (49 / 10)| := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have hsep : ∀ j : Fin (n + 1), 0 < |49 / 10 - node n j| := fun j =>
    lt_of_lt_of_le (by positivity) (sep_le_abs_sub hn j)
  have ht : ∀ j, node n j ≠ 49 / 10 := fun j h =>
    (abs_pos.mp (hsep j)) (by rw [h, sub_self])
  rw [abs_sub_interpolate_eq hn ht]
  -- the two products as exponentials
  have hP1 : ∏ j, |49 / 10 - node n j|
      = Real.exp (∑ j ∈ range (n + 1), Real.log |49 / 10 - xr n j|) := by
    rw [Real.exp_sum, ← Fin.prod_univ_eq_prod_range]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_log (hsep j)).symm
  have hP2 : ∏ j, ‖I - (node n j : ℂ)‖
      ≤ Real.exp (∑ j ∈ range (n + 1), Real.log (1 + |xr n j|)) := by
    rw [Real.exp_sum, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
    rw [Real.exp_log (by positivity)]
    calc ‖I - (node n j : ℂ)‖ ≤ ‖I‖ + ‖(node n j : ℂ)‖ := norm_sub_le _ _
      _ = 1 + |xr n j| := by rw [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]; rfl
  have hS := sum_log_abs_sub_ge hn (by omega)
  have hT := sum_log_one_add_abs_le hn (by omega)
  have hM := margin n hn400
  have hpos2 : 0 < ∏ j, ‖I - (node n j : ℂ)‖ :=
    Finset.prod_pos fun j _ => norm_pos_iff.mpr (sub_ne_zero.mpr (I_ne_ofReal _))
  rw [hP1, le_div_iff₀ (by positivity), one_mul]
  calc (1 + (49 / 10) ^ 2) * ∏ j, ‖I - (node n j : ℂ)‖
      ≤ (1 + (49 / 10) ^ 2) * Real.exp (∑ j ∈ range (n + 1), Real.log (1 + |xr n j|)) := by
        gcongr
    _ = Real.exp (Real.log (1 + (49 / 10) ^ 2)
          + ∑ j ∈ range (n + 1), Real.log (1 + |xr n j|)) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ Real.exp (∑ j ∈ range (n + 1), Real.log |49 / 10 - xr n j|) :=
        Real.exp_le_exp.mpr (by linarith)

/-- **Runge's phenomenon** ([quarteroni2000numerical] Example 8.1): the Lagrange interpolants of
`f(s) = 1/(1 + s²)` at the equispaced nodes `x_j = -5 + 10j/n` do not converge to `f` at
`t = 4.9`: along the odd `n ≥ 401` the error is at least `1`
(`one_le_abs_sub_interpolate`). -/
theorem not_tendsto_interpolate :
    ¬ Filter.Tendsto
      (fun n => (Lagrange.interpolate univ (node n) fun j => runge (node n j)).eval (49 / 10))
      Filter.atTop (nhds (runge (49 / 10))) := by
  intro h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h 1 one_pos
  have hodd : Odd (2 * (N + 200) + 1) := odd_two_mul_add_one _
  have := hN (2 * (N + 200) + 1) (by omega)
  rw [Real.dist_eq, abs_sub_comm] at this
  exact absurd this (not_lt.mpr (one_le_abs_sub_interpolate hodd (by omega)))

end Runge
