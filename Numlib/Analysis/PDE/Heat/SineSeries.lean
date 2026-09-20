import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Numlib.Analysis.Calculus.Taylor
import Numlib.Analysis.Fourier.SineBasis
import Numlib.Analysis.Fourier.TrigonometricBasis
import Numlib.Analysis.PDE.Heat.Classical

/-!
# The sine-series solutions of the heat equation on `(0, π)`

The explicit solutions of `∂ₜ u = ν ∂ₓₓ u` on the strip `(0, π) × ℝ` with homogeneous Dirichlet
boundary values and a *finite* sine polynomial `∑_{j < n} b j sin ((j + 1) x)` as initial datum:

  `u (x, t) = ∑_{j < n} b j exp (-ν (j + 1)² t) sin ((j + 1) x)`   (`Heat.sineSeries ν n b`).

These are the solutions every textbook Taylor-expands when it analyzes a finite difference
scheme for the heat equation ([han2009theoretical] Examples 6.2.4, 6.2.8, 6.3.3, 6.3.4): they
are `C^∞` on all of `ℝ × ℝ`, every derivative is again a finite sum of the same shape, and so
every derivative is bounded on `ℝ × [0, ∞)` by an explicit constant.

## Main definitions

* `Heat.sineSeries ν n b : ℝ × ℝ → ℝ`, the series itself;
* `Heat.sineSeriesDerivX ν n b m`, its `m`-th spatial derivative
  `∑ b j exp (-ν (j+1)² t) (j+1)^m sin ((j+1) x + m π/2)`, and `Heat.sineSeriesDerivT ν n b m`,
  its `m`-th time derivative `∑ b j (-ν (j+1)²)^m exp (-ν (j+1)² t) sin ((j+1) x)` — the two
  *towers* of derivative functions that the Taylor bounds of `Numlib.Analysis.Calculus.Taylor`
  consume;
* `sinePolynomial n c : C(Icc 0 π, ℝ)` (root namespace, beside `sinMap` of
  `Numlib.Analysis.Fourier.SineBasis`), the sine polynomial `∑_{j < n} c j sin ((j + 1) x)` on
  `[0, π]` as a continuous map, the value at `t = 0` of the series.

## Main statements

* `Heat.hasDerivAt_sineSeriesDerivX`, `Heat.hasDerivAt_sineSeriesDerivT`: the towers are
  towers, and `Heat.abs_sineSeriesDerivX_le`, `Heat.abs_sineSeriesDerivT_le` bound them by
  `∑ |b j| (j+1)^m` and `∑ |b j| (ν (j+1)²)^m` for `t ≥ 0`.
* `Heat.sineSeries_isClassicalSolution`: the series is a classical solution of the heat equation
  on the cylinder `(0, π) × (0, T)` in the sense of `Heat.IsClassicalSolution`, for every `T`.
* `Heat.abs_sineSeries_le`: **the maximum principle** for it — for `ν > 0`, `T > 0` and
  `x ∈ [0, π]`, `t ∈ [0, T]`, `|u (x, t)| ≤ M` as soon as `|u (·, 0)| ≤ M` on `[0, π]`
  (`Heat.IsClassicalSolution.abs_le_of_eq_zero_frontier` at `E = ℝ`, `Ω = Ioo 0 π`).
* `Heat.sineSeries_neg_left`, `Heat.sineSeries_add_two_pi_left`: the series is odd and
  `2π`-periodic in `x`.
* `Heat.abs_sineSeries_sub_forward_time_le`, `Heat.abs_sineSeries_sub_backward_time_le`,
  `Heat.abs_sineSeries_centred_sub_le`: the Taylor bounds a finite difference scheme needs, on
  the whole line in `x` and for `t ≥ 0`, with the explicit constants above.

## The odd periodic extension and the density of the sine polynomials

The second half of the module is about the space `C₀[0, π]` of continuous functions on `[0, π]`
vanishing at both ends, in which the sine polynomials are a dense subspace: the natural phase
space of the Dirichlet problem in the uniform norm.

* `oddPeriodicExtend v : ℝ → ℝ`, for `v : C(Icc 0 π, ℝ)`, is the extension of `v` to the line
  that is odd and `2π`-periodic (`oddPeriodicExtend_neg`, `oddPeriodicExtend_periodic`),
  continuous when `v 0 = v π = 0` (`continuous_oddPeriodicExtend`), equal to `v` on `[0, π]`
  and bounded by `‖v‖`; `eq_of_odd_of_periodic_of_eqOn_Icc` says that an odd `2π`-periodic
  function is determined by its values on `[0, π]`, which identifies the extension of a sine
  polynomial with the sine polynomial itself.
* `linearIndependent_sinMap`: the sine system `sinMap k = sin ((k + 1) x)` is linearly
  independent in `C(Icc 0 π, ℝ)` (from its orthonormality in `L²(0, π)`,
  `Numlib.Analysis.Fourier.SineBasis`).
* `exists_mem_span_sinMap_norm_sub_lt`: **the sine polynomials are uniformly dense in
  `C₀[0, π]`**. The odd `2π`-periodic extension of `v` is a continuous function on the circle,
  uniformly approximable by real trigonometric polynomials
  (`exists_mem_span_trigFun_norm_sub_lt`, `Numlib.Analysis.Fourier.TrigonometricBasis`); the
  odd part of the approximant is a sine polynomial that is as close, since the target is odd.

## References

[han2009theoretical] §6.2, Example 6.2.4 and Exercise 6.2.1; [brezis2011functional] §10.1.
-/

open Filter Set Topology Finset InnerProductSpace Laplacian
open scoped Real

namespace Heat

/-! ### The finite sine series and its derivative towers -/

section SineSeries

variable (ν : ℝ) (n : ℕ) (b : ℕ → ℝ)

/-- **The finite sine series** `u (x, t) = ∑_{j < n} b j exp (-ν (j + 1)² t) sin ((j + 1) x)`,
the solution of the heat equation `∂ₜ u = ν ∂ₓₓ u` on `(0, π)` with Dirichlet boundary values
and initial datum `∑_{j < n} b j sin ((j + 1) x)`. -/
noncomputable def sineSeries (p : ℝ × ℝ) : ℝ :=
  ∑ j ∈ range n, b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) * Real.sin (((j : ℝ) + 1) * p.1)

/-- The `m`-th spatial derivative of the sine series, written with the phase shift
`sin^{(m)} y = sin (y + m π / 2)`:
`∑_{j < n} b j exp (-ν (j + 1)² t) (j + 1)^m sin ((j + 1) x + m π / 2)`. -/
noncomputable def sineSeriesDerivX (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ j ∈ range n, b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) * ((j : ℝ) + 1) ^ m *
    Real.sin (((j : ℝ) + 1) * p.1 + m * (π / 2))

/-- The `m`-th time derivative of the sine series:
`∑_{j < n} b j (-ν (j + 1)²)^m exp (-ν (j + 1)² t) sin ((j + 1) x)`. -/
noncomputable def sineSeriesDerivT (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ j ∈ range n, b j * (-ν * ((j : ℝ) + 1) ^ 2) ^ m * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) *
    Real.sin (((j : ℝ) + 1) * p.1)

variable {ν n b}

/-- The spatial tower starts at the series itself. -/
theorem sineSeriesDerivX_zero : sineSeriesDerivX ν n b 0 = sineSeries ν n b := by
  funext p
  simp only [sineSeriesDerivX, sineSeries, Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one]

/-- The time tower starts at the series itself. -/
theorem sineSeriesDerivT_zero : sineSeriesDerivT ν n b 0 = sineSeries ν n b := by
  funext p
  simp only [sineSeriesDerivT, sineSeries, pow_zero, mul_one]

/-- The second spatial derivative is `-∑ b j (j + 1)² exp (…) sin ((j + 1) x)`. -/
theorem sineSeriesDerivX_two (p : ℝ × ℝ) :
    sineSeriesDerivX ν n b 2 p = -∑ j ∈ range n,
      b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) * ((j : ℝ) + 1) ^ 2 *
        Real.sin (((j : ℝ) + 1) * p.1) := by
  simp only [sineSeriesDerivX, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((2 : ℕ) : ℝ) * (π / 2) = π by push_cast; ring, Real.sin_add_pi]
  ring

/-- The fourth spatial derivative is `∑ b j (j + 1)⁴ exp (…) sin ((j + 1) x)`. -/
theorem sineSeriesDerivX_four (p : ℝ × ℝ) :
    sineSeriesDerivX ν n b 4 p = ∑ j ∈ range n,
      b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) * ((j : ℝ) + 1) ^ 4 *
        Real.sin (((j : ℝ) + 1) * p.1) := by
  simp only [sineSeriesDerivX]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((4 : ℕ) : ℝ) * (π / 2) = (1 : ℕ) * (2 * π) by push_cast; ring,
    Real.sin_add_nat_mul_two_pi]

/-- The spatial tower: `sineSeriesDerivX m` has derivative `sineSeriesDerivX (m + 1)` in `x`. -/
theorem hasDerivAt_sineSeriesDerivX (m : ℕ) (x t : ℝ) :
    HasDerivAt (fun y => sineSeriesDerivX ν n b m (y, t)) (sineSeriesDerivX ν n b (m + 1) (x, t))
      x := by
  unfold sineSeriesDerivX
  refine HasDerivAt.fun_sum (A := fun j y => b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * t) *
    ((j : ℝ) + 1) ^ m * Real.sin (((j : ℝ) + 1) * y + m * (π / 2))) fun j _ => ?_
  have h1 : HasDerivAt (fun y : ℝ => ((j : ℝ) + 1) * y + m * (π / 2)) ((j : ℝ) + 1) x := by
    simpa using ((hasDerivAt_id x).const_mul ((j : ℝ) + 1)).add_const (m * (π / 2))
  have h2 := ((Real.hasDerivAt_sin _).comp x h1).const_mul
    (b j * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * t) * ((j : ℝ) + 1) ^ m)
  refine h2.congr_deriv ?_
  rw [← Real.sin_add_pi_div_two]
  push_cast
  rw [show ((j : ℝ) + 1) * x + (m + 1) * (π / 2) = (j + 1) * x + m * (π / 2) + π / 2 by ring]
  ring

/-- The time tower: `sineSeriesDerivT m` has derivative `sineSeriesDerivT (m + 1)` in `t`. -/
theorem hasDerivAt_sineSeriesDerivT (m : ℕ) (x t : ℝ) :
    HasDerivAt (fun s => sineSeriesDerivT ν n b m (x, s)) (sineSeriesDerivT ν n b (m + 1) (x, t))
      t := by
  unfold sineSeriesDerivT
  refine HasDerivAt.fun_sum (A := fun j s => b j * (-ν * ((j : ℝ) + 1) ^ 2) ^ m *
    Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * s) * Real.sin (((j : ℝ) + 1) * x)) fun j _ => ?_
  have h1 : HasDerivAt (fun s : ℝ => -ν * ((j : ℝ) + 1) ^ 2 * s) (-ν * ((j : ℝ) + 1) ^ 2) t :=
    (hasDerivAt_id t).const_mul (-ν * ((j : ℝ) + 1) ^ 2) |>.congr_deriv (mul_one _)
  have h2 := (((Real.hasDerivAt_exp _).comp t h1).const_mul
    (b j * (-ν * ((j : ℝ) + 1) ^ 2) ^ m)).mul_const (Real.sin (((j : ℝ) + 1) * x))
  refine h2.congr_deriv ?_
  simp only [pow_succ]
  ring

/-- The first time derivative is `ν` times the second spatial derivative: the heat equation. -/
theorem sineSeriesDerivT_one (p : ℝ × ℝ) :
    sineSeriesDerivT ν n b 1 p = ν * sineSeriesDerivX ν n b 2 p := by
  rw [sineSeriesDerivX_two, sineSeriesDerivT, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The bound `|∂ₓ^m u (x, t)| ≤ ∑ |b j| (j + 1)^m` for `t ≥ 0`. -/
theorem abs_sineSeriesDerivX_le (hν : 0 ≤ ν) (m : ℕ) {p : ℝ × ℝ} (hp : 0 ≤ p.2) :
    |sineSeriesDerivX ν n b m p| ≤ ∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ m := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ m)]
  have he : Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) ≤ 1 := by
    have : 0 ≤ ν * ((j : ℝ) + 1) ^ 2 * p.2 := by positivity
    exact Real.exp_le_one_iff.2 (by linarith)
  have hs := Real.abs_sin_le_one (((j : ℝ) + 1) * p.1 + m * (π / 2))
  have h0 : 0 ≤ |b j| * ((j : ℝ) + 1) ^ m := by positivity
  calc |b j| * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) * ((j : ℝ) + 1) ^ m *
        |Real.sin (((j : ℝ) + 1) * p.1 + m * (π / 2))|
      ≤ |b j| * 1 * ((j : ℝ) + 1) ^ m * 1 := by gcongr
    _ = |b j| * ((j : ℝ) + 1) ^ m := by ring

/-- The bound `|∂ₜ^m u (x, t)| ≤ ∑ |b j| (ν (j + 1)²)^m` for `t ≥ 0`. -/
theorem abs_sineSeriesDerivT_le (hν : 0 ≤ ν) (m : ℕ) {p : ℝ × ℝ} (hp : 0 ≤ p.2) :
    |sineSeriesDerivT ν n b m p| ≤ ∑ j ∈ range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ m := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le, abs_pow, abs_mul, abs_neg,
    abs_of_nonneg hν, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ 2)]
  have he : Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) ≤ 1 := by
    have : 0 ≤ ν * ((j : ℝ) + 1) ^ 2 * p.2 := by positivity
    exact Real.exp_le_one_iff.2 (by linarith)
  have hs := Real.abs_sin_le_one (((j : ℝ) + 1) * p.1)
  have h0 : 0 ≤ |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ m := by positivity
  calc |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ m * Real.exp (-ν * ((j : ℝ) + 1) ^ 2 * p.2) *
        |Real.sin (((j : ℝ) + 1) * p.1)|
      ≤ |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ m * 1 * 1 := by gcongr
    _ = |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ m := by ring

/-- The sine series is continuous on `ℝ × ℝ`. -/
theorem continuous_sineSeries : Continuous (sineSeries ν n b) := by
  unfold sineSeries
  fun_prop

/-- The spatial slices of the sine series are `C^∞`. -/
theorem contDiff_sineSeries_fst {k : WithTop ℕ∞} (t : ℝ) :
    ContDiff ℝ k fun y => sineSeries ν n b (y, t) := by
  unfold sineSeries
  fun_prop

/-- The sine series vanishes at `x = 0`. -/
theorem sineSeries_zero_left (t : ℝ) : sineSeries ν n b (0, t) = 0 := by
  simp [sineSeries]

/-- The sine series vanishes at `x = π`. -/
theorem sineSeries_pi_left (t : ℝ) : sineSeries ν n b (π, t) = 0 := by
  unfold sineSeries
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show ((j : ℝ) + 1) * π = ((j + 1 : ℕ) : ℝ) * π by push_cast; ring, Real.sin_nat_mul_pi,
    mul_zero]

/-- At `t = 0` the sine series is the sine polynomial `∑ b j sin ((j + 1) x)`. -/
theorem sineSeries_zero_right (x : ℝ) :
    sineSeries ν n b (x, 0) = ∑ j ∈ range n, b j * Real.sin (((j : ℝ) + 1) * x) := by
  simp [sineSeries]

/-- With `ν = 0` the sine series is the sine polynomial `∑ c j sin ((j + 1) x)` at every time:
the form in which the spatial calculus of the series applies to a sine polynomial alone. -/
theorem sineSeries_zero_nu_eq (n : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (fun y => sineSeries 0 n c (y, t))
      = fun y => ∑ j ∈ range n, c j * Real.sin (((j : ℝ) + 1) * y) := by
  funext y
  simp [sineSeries]

/-- The sine series is odd in `x`. -/
theorem sineSeries_neg_left (x t : ℝ) : sineSeries ν n b (-x, t) = -sineSeries ν n b (x, t) := by
  simp only [sineSeries, mul_neg, Real.sin_neg, ← Finset.sum_neg_distrib]

/-- The sine series is `2π`-periodic in `x`. -/
theorem sineSeries_add_two_pi_left (x t : ℝ) :
    sineSeries ν n b (x + 2 * π, t) = sineSeries ν n b (x, t) := by
  unfold sineSeries
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((j : ℝ) + 1) * (x + 2 * π) = ((j : ℝ) + 1) * x + ((j + 1 : ℕ) : ℝ) * (2 * π) by
    push_cast; ring, Real.sin_add_nat_mul_two_pi]

/-- The second spatial derivative of a slice is the Laplacian on `ℝ`, and it is
`sineSeriesDerivX 2`. -/
theorem laplacian_sineSeries_fst (x t : ℝ) :
    Δ (fun y => sineSeries ν n b (y, t)) x = sineSeriesDerivX ν n b 2 (x, t) := by
  rw [laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ, iteratedDeriv_one]
  have h0 : deriv (fun y => sineSeries ν n b (y, t))
      = fun y => sineSeriesDerivX ν n b 1 (y, t) := by
    funext y
    rw [← sineSeriesDerivX_zero]
    exact (hasDerivAt_sineSeriesDerivX 0 y t).deriv
  rw [h0]
  exact (hasDerivAt_sineSeriesDerivX 1 x t).deriv

/-- The time derivative of the sine series at a point is `sineSeriesDerivT 1`. -/
theorem deriv_sineSeries_snd (x t : ℝ) :
    deriv (fun s => sineSeries ν n b (x, s)) t = sineSeriesDerivT ν n b 1 (x, t) := by
  rw [← sineSeriesDerivT_zero]
  exact (hasDerivAt_sineSeriesDerivT 0 x t).deriv

/-- **The sine series is a classical solution of the heat equation** `∂ₜ u = ν ∂ₓₓ u` on the
cylinder `(0, π) × (0, T)`, for every horizon `T`. -/
theorem sineSeries_isClassicalSolution (T : ℝ) :
    IsClassicalSolution ν (Ioo 0 π) T (sineSeries ν n b) where
  continuousOn := continuous_sineSeries.continuousOn
  differentiableAt_snd x _ t _ := by
    rw [← sineSeriesDerivT_zero]
    exact (hasDerivAt_sineSeriesDerivT 0 x t).differentiableAt
  contDiffAt_fst x _ t _ := (contDiff_sineSeries_fst t).contDiffAt
  deriv_eq_laplacian x _ t _ := by
    rw [deriv_sineSeries_snd, laplacian_sineSeries_fst, sineSeriesDerivT_one]

/-- **The maximum principle for the sine series**: for `ν > 0` and `T > 0`, if
`|u (·, 0)| ≤ M` on `[0, π]` then `|u (x, t)| ≤ M` for all `x ∈ [0, π]` and `t ∈ [0, T]`. -/
theorem abs_sineSeries_le (hν : 0 < ν) {T : ℝ} (hT : 0 < T) {M : ℝ}
    (hM : ∀ y ∈ Icc (0 : ℝ) π, |sineSeries ν n b (y, 0)| ≤ M) :
    ∀ x ∈ Icc (0 : ℝ) π, ∀ t ∈ Icc 0 T, |sineSeries ν n b (x, t)| ≤ M := by
  have hcl : closure (Ioo (0 : ℝ) π) = Icc 0 π := closure_Ioo Real.pi_pos.ne
  have hfr : frontier (Ioo (0 : ℝ) π) = {0, π} := frontier_Ioo Real.pi_pos
  have := (sineSeries_isClassicalSolution (ν := ν) (n := n) (b := b) T).abs_le_of_eq_zero_frontier
    isOpen_Ioo (Metric.isBounded_Ioo 0 π) hν hT (fun x hx t _ => ?_) (M := M) ?_
  · intro x hx t ht
    exact this x (hcl ▸ hx) t ht
  · rw [hfr] at hx
    rcases hx with rfl | rfl
    · exact sineSeries_zero_left t
    · exact sineSeries_pi_left t
  · intro y hy
    exact hM y (hcl ▸ hy)

/-! ### Taylor bounds for the sine series

The two expansions a finite difference scheme for the heat equation needs, for the sine series on
the whole line in `x` and on `t ≥ 0`: the forward expansion in time to second order and the
centred second difference in space to fourth order, with the explicit constants
`∑ |b j| (ν (j + 1)²)²` and `∑ |b j| (j + 1)⁴`. -/

/-- `|u (x, t + k) - u (x, t) - k ∂ₜ u (x, t)| ≤ (∑ |b j| (ν (j + 1)²)²) k² / 2` for `t, k ≥ 0`. -/
theorem abs_sineSeries_sub_forward_time_le (hν : 0 ≤ ν) {x t k : ℝ} (ht : 0 ≤ t) (hk : 0 ≤ k) :
    |sineSeries ν n b (x, t + k) - sineSeries ν n b (x, t) - k * sineSeriesDerivT ν n b 1 (x, t)|
      ≤ (∑ j ∈ range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) * k ^ 2 / 2 := by
  have h := norm_sub_sub_smul_le_mul_sq_div_two (a := t) (b := t + k)
    (y := fun s => sineSeries ν n b (x, s)) (y' := fun s => sineSeriesDerivT ν n b 1 (x, s))
    (y'' := fun s => sineSeriesDerivT ν n b 2 (x, s))
    (M := ∑ j ∈ range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) (by linarith)
    (fun s _ => by
      rw [← sineSeriesDerivT_zero]
      exact (hasDerivAt_sineSeriesDerivT 0 x s).hasDerivWithinAt)
    (fun s _ => (hasDerivAt_sineSeriesDerivT 1 x s).hasDerivWithinAt)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact abs_sineSeriesDerivT_le hν 2 (p := (x, s)) (by linarith [hs.1]))
  rw [smul_eq_mul, Real.norm_eq_abs, add_sub_cancel_left] at h
  exact h

/-- `|u (x, t + k) - u (x, t) - k ∂ₜ u (x, t + k)| ≤ (∑ |b j| (ν (j + 1)²)²) k² / 2` for
`t, k ≥ 0`: the backward expansion in time. -/
theorem abs_sineSeries_sub_backward_time_le (hν : 0 ≤ ν) {x t k : ℝ} (ht : 0 ≤ t) (hk : 0 ≤ k) :
    |sineSeries ν n b (x, t + k) - sineSeries ν n b (x, t)
        - k * sineSeriesDerivT ν n b 1 (x, t + k)|
      ≤ (∑ j ∈ range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) * k ^ 2 / 2 := by
  have h := norm_sub_sub_smul_le_mul_sq_div_two' (a := t) (b := t + k)
    (y := fun s => sineSeries ν n b (x, s)) (y' := fun s => sineSeriesDerivT ν n b 1 (x, s))
    (y'' := fun s => sineSeriesDerivT ν n b 2 (x, s))
    (M := ∑ j ∈ range n, |b j| * (ν * ((j : ℝ) + 1) ^ 2) ^ 2) (by linarith)
    (fun s _ => by
      rw [← sineSeriesDerivT_zero]
      exact (hasDerivAt_sineSeriesDerivT 0 x s).hasDerivWithinAt)
    (fun s _ => (hasDerivAt_sineSeriesDerivT 1 x s).hasDerivWithinAt)
    (fun s hs => by
      rw [Real.norm_eq_abs]
      exact abs_sineSeriesDerivT_le hν 2 (p := (x, s)) (by linarith [hs.1]))
  rw [smul_eq_mul, Real.norm_eq_abs, add_sub_cancel_left] at h
  have e : sineSeries ν n b (x, t + k) - sineSeries ν n b (x, t)
        - k * sineSeriesDerivT ν n b 1 (x, t + k)
      = -(sineSeries ν n b (x, t) - sineSeries ν n b (x, t + k)
        - (t - (t + k)) * sineSeriesDerivT ν n b 1 (x, t + k)) := by ring
  rw [e, abs_neg]
  exact h

/-- `|u (x + h, t) - 2 u (x, t) + u (x - h, t) - h² ∂ₓₓ u (x, t)| ≤ (∑ |b j| (j + 1)⁴) h⁴ / 12`
for `t ≥ 0` and `h ≥ 0`, at every `x`. -/
theorem abs_sineSeries_centred_sub_le (hν : 0 ≤ ν) {x t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    |sineSeries ν n b (x + h, t) - 2 * sineSeries ν n b (x, t) + sineSeries ν n b (x - h, t)
        - h ^ 2 * sineSeriesDerivX ν n b 2 (x, t)|
      ≤ (∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ 4) * h ^ 4 / 12 := by
  have hy : ∀ m < 4, ∀ s ∈ Icc (x - h) (x + h),
      HasDerivWithinAt (fun y => sineSeriesDerivX ν n b m (y, t))
        (sineSeriesDerivX ν n b (m + 1) (s, t)) (Icc (x - h) (x + h)) s :=
    fun m _ s _ => (hasDerivAt_sineSeriesDerivX m s t).hasDerivWithinAt
  have hK : ∀ s ∈ Icc (x - h) (x + h),
      ‖sineSeriesDerivX ν n b 4 (s, t)‖ ≤ ∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ 4 := fun s _ => by
    rw [Real.norm_eq_abs]
    exact abs_sineSeriesDerivX_le hν 4 (p := (s, t)) ht
  have hx : x ∈ Icc (x - h) (x + h) := ⟨by linarith, by linarith⟩
  have hr := norm_sub_sum_smul_le (y := fun m y => sineSeriesDerivX ν n b m (y, t)) 4 hy hK hx
    (right_mem_Icc.2 (by linarith))
  have hl := norm_sub_sum_smul_le (y := fun m y => sineSeriesDerivX ν n b m (y, t)) 4 hy hK hx
    (left_mem_Icc.2 (by linarith))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, smul_eq_mul,
    Real.norm_eq_abs, sineSeriesDerivX_zero, add_sub_cancel_left, sub_sub_cancel_left, abs_neg,
    abs_of_nonneg hh] at hr hl
  push_cast at hr hl
  have e : sineSeries ν n b (x + h, t) - 2 * sineSeries ν n b (x, t) + sineSeries ν n b (x - h, t)
        - h ^ 2 * sineSeriesDerivX ν n b 2 (x, t)
      = (sineSeries ν n b (x + h, t) - (0 + h ^ 0 / 1 * sineSeries ν n b (x, t)
          + h ^ 1 / 1 * sineSeriesDerivX ν n b 1 (x, t)
          + h ^ 2 / 2 * sineSeriesDerivX ν n b 2 (x, t)
          + h ^ 3 / 6 * sineSeriesDerivX ν n b 3 (x, t)))
        + (sineSeries ν n b (x - h, t) - (0 + (-h) ^ 0 / 1 * sineSeries ν n b (x, t)
          + (-h) ^ 1 / 1 * sineSeriesDerivX ν n b 1 (x, t)
          + (-h) ^ 2 / 2 * sineSeriesDerivX ν n b 2 (x, t)
          + (-h) ^ 3 / 6 * sineSeriesDerivX ν n b 3 (x, t))) := by
    ring
  rw [e]
  calc _ ≤ (∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ 4) * h ^ 4 / 24
        + (∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ 4) * h ^ 4 / 24 :=
        (abs_add_le _ _).trans (add_le_add hr hl)
    _ = (∑ j ∈ range n, |b j| * ((j : ℝ) + 1) ^ 4) * h ^ 4 / 12 := by ring

end SineSeries

end Heat

/-! ### Sine polynomials on `[0, π]` -/

section SinePolynomial

open Submodule

/-- **The sine polynomial** `∑_{j < n} c j sin ((j + 1) x)` on `[0, π]`, as a continuous map:
the initial datum of the sine series `Heat.sineSeries ν n c`. -/
noncomputable def sinePolynomial (n : ℕ) (c : ℕ → ℝ) : C(Icc (0 : ℝ) π, ℝ) :=
  ∑ j ∈ range n, c j • sinMap j

/-- The value of a sine polynomial at a point of `[0, π]`. -/
theorem sinePolynomial_apply (n : ℕ) (c : ℕ → ℝ) (x : Icc (0 : ℝ) π) :
    sinePolynomial n c x = ∑ j ∈ range n, c j * Real.sin (((j : ℝ) + 1) * (x : ℝ)) := by
  simp [sinePolynomial, sinMap_apply]

/-- The sine series at `t = 0` is the sine polynomial of its coefficients. -/
theorem _root_.Heat.sineSeries_zero_right_eq (ν : ℝ) (n : ℕ) (c : ℕ → ℝ) (x : Icc (0 : ℝ) π) :
    Heat.sineSeries ν n c ((x : ℝ), 0) = sinePolynomial n c x := by
  rw [Heat.sineSeries_zero_right, sinePolynomial_apply]

/-- A sine polynomial lies in the span of the sine system. -/
theorem sinePolynomial_mem_span (n : ℕ) (c : ℕ → ℝ) :
    sinePolynomial n c ∈ span ℝ (range sinMap) :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)

/-- The span of the sine system consists exactly of the sine polynomials. -/
theorem mem_span_sinMap_iff {v : C(Icc (0 : ℝ) π, ℝ)} :
    v ∈ span ℝ (range sinMap) ↔ ∃ (n : ℕ) (c : ℕ → ℝ), v = sinePolynomial n c := by
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
    refine ⟨c.support.sup id + 1, c, ?_⟩
    rw [← hc, sinePolynomial]
    exact Finsupp.sum_of_support_subset c (s := range (c.support.sup id + 1))
      (fun i hi => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)))
      _ (fun i _ => zero_smul ℝ _)
  · rintro ⟨n, c, rfl⟩
    exact sinePolynomial_mem_span n c

/-- **The sine system is linearly independent** in `C(Icc 0 π, ℝ)`: its image in `L²(0, π)`
is orthonormal. -/
theorem linearIndependent_sinMap : LinearIndependent ℝ sinMap := by
  have h : LinearIndependent ℝ sinLp := orthonormal_sinLp.linearIndependent
  have e : sinLp = ⇑(√(2 / π) • (ContinuousMap.toLp (E := ℝ) 2 halfRangeMeasure ℝ :
      C(Icc (0 : ℝ) π, ℝ) →ₗ[ℝ] MeasureTheory.Lp ℝ 2 halfRangeMeasure)) ∘ sinMap := by
    funext k
    rw [Function.comp_apply, LinearMap.smul_apply, sinLp_eq_smul]
    rfl
  rw [e] at h
  exact LinearIndependent.of_comp _ h

end SinePolynomial

/-! ### The odd `2π`-periodic extension of a function on `[0, π]` -/

section OddPeriodicExtend

/-- The odd reflection of `v : C(Icc 0 π, ℝ)` about `0`: `v y` for `y ≥ 0` and `-v (-y)` for
`y < 0`, the argument clamped to `[0, π]`. Only its values on `[-π, π]` are used. -/
noncomputable def oddReflect (v : C(Icc (0 : ℝ) π, ℝ)) (y : ℝ) : ℝ :=
  if 0 ≤ y then v (projIcc 0 π Real.pi_pos.le y) else -v (projIcc 0 π Real.pi_pos.le (-y))

variable {v w : C(Icc (0 : ℝ) π, ℝ)}

/-- On `[0, π]` the odd reflection is `v` itself. -/
theorem oddReflect_of_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) π) : oddReflect v y = v ⟨y, hy⟩ := by
  rw [oddReflect, ite_eq_left hy.1, projIcc_of_mem]

/-- On `[-π, 0)` the odd reflection is `-v (-y)`. -/
theorem oddReflect_of_neg_mem {y : ℝ} (hy : -y ∈ Icc (0 : ℝ) π) (hy' : y < 0) :
    oddReflect v y = -v ⟨-y, hy⟩ := by
  rw [oddReflect, ite_eq_right (not_le.2 hy'), projIcc_of_mem]

/-- The odd reflection is odd, provided `v 0 = 0`. -/
theorem oddReflect_neg (h0 : v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0) (y : ℝ) :
    oddReflect v (-y) = -oddReflect v y := by
  unfold oddReflect
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · rw [ite_eq_left (neg_nonneg.2 hy.le), ite_eq_right (not_le.2 hy), neg_neg]
  · simp [h0]
  · rw [ite_eq_right (not_le.2 (neg_neg_iff_pos.2 hy)), ite_eq_left hy.le, neg_neg]

/-- The odd reflection is continuous, provided `v 0 = 0`. -/
theorem continuous_oddReflect (h0 : v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0) :
    Continuous (oddReflect v) := by
  unfold oddReflect
  refine continuous_if_le continuous_const continuous_id ?_ ?_ ?_
  · exact (v.continuous.comp continuous_projIcc).continuousOn
  · exact ((v.continuous.comp continuous_projIcc).comp continuous_neg).neg.continuousOn
  · intro y hy
    subst hy
    simp [h0]

/-- The odd reflection is bounded by `‖v‖`. -/
theorem abs_oddReflect_le (y : ℝ) : |oddReflect v y| ≤ ‖v‖ := by
  unfold oddReflect
  split_ifs
  · exact (Real.norm_eq_abs _).symm.trans_le (v.norm_coe_le_norm _)
  · rw [abs_neg]
    exact (Real.norm_eq_abs _).symm.trans_le (v.norm_coe_le_norm _)

/-- The odd reflection is additive in `v`. -/
theorem oddReflect_add (v w : C(Icc (0 : ℝ) π, ℝ)) (y : ℝ) :
    oddReflect (v + w) y = oddReflect v y + oddReflect w y := by
  unfold oddReflect
  split_ifs <;> simp only [ContinuousMap.add_apply]
  ring

/-- The odd reflection is homogeneous in `v`. -/
theorem oddReflect_smul (a : ℝ) (v : C(Icc (0 : ℝ) π, ℝ)) (y : ℝ) :
    oddReflect (a • v) y = a * oddReflect v y := by
  unfold oddReflect
  split_ifs <;> simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring

/-- **The odd `2π`-periodic extension** of `v : C(Icc 0 π, ℝ)` to the whole line: the
`2π`-periodic function that agrees with the odd reflection of `v` on `[-π, π)`. -/
noncomputable def oddPeriodicExtend (v : C(Icc (0 : ℝ) π, ℝ)) (x : ℝ) : ℝ :=
  AddCircle.liftIco (2 * π) (-π) (oddReflect v) (x : AddCircle (2 * π))

/-- The extension is `2π`-periodic. -/
theorem oddPeriodicExtend_periodic (v : C(Icc (0 : ℝ) π, ℝ)) :
    Function.Periodic (oddPeriodicExtend v) (2 * π) := by
  intro x
  simp only [oddPeriodicExtend, AddCircle.coe_add_period]

/-- On `[-π, π)` the extension is the odd reflection. -/
theorem oddPeriodicExtend_of_mem_Ico {x : ℝ} (hx : x ∈ Ico (-π) π) :
    oddPeriodicExtend v x = oddReflect v x :=
  AddCircle.liftIco_coe_apply (by rw [show -π + 2 * π = π by ring]; exact hx)

/-- The extension is the odd reflection evaluated at the representative in `[-π, π)`. -/
theorem oddPeriodicExtend_eq (v : C(Icc (0 : ℝ) π, ℝ)) (x : ℝ) :
    oddPeriodicExtend v x
      = oddReflect v (AddCircle.equivIco (2 * π) (-π) (x : AddCircle (2 * π)) : ℝ) := rfl

/-- The extension is additive in `v`. -/
theorem oddPeriodicExtend_add (v w : C(Icc (0 : ℝ) π, ℝ)) (x : ℝ) :
    oddPeriodicExtend (v + w) x = oddPeriodicExtend v x + oddPeriodicExtend w x := by
  simp only [oddPeriodicExtend_eq, oddReflect_add]

/-- The extension is homogeneous in `v`. -/
theorem oddPeriodicExtend_smul (a : ℝ) (v : C(Icc (0 : ℝ) π, ℝ)) (x : ℝ) :
    oddPeriodicExtend (a • v) x = a * oddPeriodicExtend v x := by
  simp only [oddPeriodicExtend_eq, oddReflect_smul]

/-- The extension is bounded by `‖v‖`. -/
theorem abs_oddPeriodicExtend_le (v : C(Icc (0 : ℝ) π, ℝ)) (x : ℝ) :
    |oddPeriodicExtend v x| ≤ ‖v‖ := by
  rw [oddPeriodicExtend_eq]
  exact abs_oddReflect_le _

/-- The odd reflection vanishes at `-π` when `v π = 0`. -/
theorem oddReflect_neg_pi (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) :
    oddReflect v (-π) = 0 := by
  rw [oddReflect_of_neg_mem (by rw [neg_neg]; exact right_mem_Icc.2 Real.pi_pos.le)
    (neg_neg_iff_pos.2 Real.pi_pos)]
  simp only [neg_neg, neg_eq_zero]
  convert hπ

/-- The extension vanishes at `π` when `v π = 0`. -/
theorem oddPeriodicExtend_pi (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) :
    oddPeriodicExtend v π = 0 := by
  rw [show π = -π + 2 * π by ring, oddPeriodicExtend_periodic,
    oddPeriodicExtend_of_mem_Ico ⟨le_rfl, by linarith [Real.pi_pos]⟩, oddReflect_neg_pi hπ]

/-- The extension agrees with `v` on `[0, π]`. -/
theorem oddPeriodicExtend_of_mem (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) π) : oddPeriodicExtend v x = v ⟨x, hx⟩ := by
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · rw [oddPeriodicExtend_pi hπ]
    exact hπ.symm
  · rw [oddPeriodicExtend_of_mem_Ico ⟨by linarith [hx.1, Real.pi_pos], hlt⟩, oddReflect_of_mem hx]

/-- The extension is continuous when `v` vanishes at both ends. -/
theorem continuous_oddPeriodicExtend (h0 : v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0)
    (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) : Continuous (oddPeriodicExtend v) := by
  refine (AddCircle.liftIco_continuous ?_ (continuous_oddReflect h0).continuousOn).comp
    (AddCircle.continuous_mk' _)
  rw [show -π + 2 * π = π by ring, oddReflect_neg_pi hπ, oddReflect_of_mem (right_mem_Icc.2
    Real.pi_pos.le), hπ]

/-- The extension is odd when `v` vanishes at both ends. -/
theorem oddPeriodicExtend_neg (h0 : v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0)
    (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) (x : ℝ) :
    oddPeriodicExtend v (-x) = -oddPeriodicExtend v x := by
  -- the sum `x ↦ u (-x) + u x` is periodic and vanishes on `[-π, π)`, hence everywhere
  set g : ℝ → ℝ := fun x => oddPeriodicExtend v (-x) + oddPeriodicExtend v x with hg
  have hgp : Function.Periodic g (2 * π) := by
    intro y
    simp only [hg, neg_add, oddPeriodicExtend_periodic v y]
    rw [show -y + -(2 * π) = -y - 2 * π by ring, (oddPeriodicExtend_periodic v).sub_eq]
  have hg0 : ∀ y ∈ Ico (-π) π, g y = 0 := by
    intro y hy
    simp only [hg]
    rcases eq_or_lt_of_le hy.1 with rfl | hlt
    · rw [neg_neg, oddPeriodicExtend_pi hπ, oddPeriodicExtend_of_mem_Ico hy, oddReflect_neg_pi hπ,
        add_zero]
    · rw [oddPeriodicExtend_of_mem_Ico hy, oddPeriodicExtend_of_mem_Ico
        ⟨by linarith [hy.2], by linarith⟩, oddReflect_neg h0, neg_add_cancel]
  obtain ⟨y, hy, hxy⟩ := hgp.exists_mem_Ico Real.two_pi_pos x (-π)
  rw [show -π + 2 * π = π by ring] at hy
  have : g x = 0 := hxy.trans (hg0 y hy)
  simp only [hg] at this
  linarith

/-- **An odd `2π`-periodic function is determined by its values on `[0, π]`.** -/
theorem eq_of_odd_of_periodic_of_eqOn_Icc {f g : ℝ → ℝ} (hfo : ∀ x, f (-x) = -f x)
    (hgo : ∀ x, g (-x) = -g x) (hfp : Function.Periodic f (2 * π))
    (hgp : Function.Periodic g (2 * π)) (h : ∀ x ∈ Icc (0 : ℝ) π, f x = g x) : f = g := by
  funext x
  obtain ⟨n, hn, -⟩ := existsUnique_add_zsmul_mem_Ico Real.two_pi_pos x (-π)
  rw [← hfp.zsmul n x, ← hgp.zsmul n x]
  set y := x + n • (2 * π)
  rcases le_or_gt 0 y with hy | hy
  · exact h y ⟨hy, by linarith [hn.2]⟩
  · rw [← neg_neg y, hfo, hgo, h (-y) ⟨by linarith, by linarith [hn.1]⟩]

/-- The sine polynomial vanishes at `0`. -/
theorem sinePolynomial_zero_apply (n : ℕ) (c : ℕ → ℝ) :
    sinePolynomial n c ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0 := by
  rw [← Heat.sineSeries_zero_right_eq 0]
  exact Heat.sineSeries_zero_left 0

/-- The sine polynomial vanishes at `π`. -/
theorem sinePolynomial_pi_apply (n : ℕ) (c : ℕ → ℝ) :
    sinePolynomial n c ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0 := by
  rw [← Heat.sineSeries_zero_right_eq 0]
  exact Heat.sineSeries_pi_left 0

/-- The odd periodic extension of a sine polynomial is the sine polynomial itself, on the
whole line. -/
theorem oddPeriodicExtend_sinePolynomial (n : ℕ) (c : ℕ → ℝ) :
    oddPeriodicExtend (sinePolynomial n c)
      = fun x => ∑ j ∈ range n, c j * Real.sin (((j : ℝ) + 1) * x) := by
  have h0 := sinePolynomial_zero_apply n c
  have hπ := sinePolynomial_pi_apply n c
  refine eq_of_odd_of_periodic_of_eqOn_Icc (oddPeriodicExtend_neg h0 hπ) (fun x => ?_)
    (oddPeriodicExtend_periodic _) (fun x => ?_) (fun x hx => ?_)
  · simp only [mul_neg, Real.sin_neg, ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((j : ℝ) + 1) * (x + 2 * π) = ((j : ℝ) + 1) * x + ((j + 1 : ℕ) : ℝ) * (2 * π) by
      push_cast; ring, Real.sin_add_nat_mul_two_pi]
  · rw [oddPeriodicExtend_of_mem hπ hx, sinePolynomial_apply]

end OddPeriodicExtend

/-! ### The density of the sine polynomials in `C₀[0, π]` -/

section Density

open Submodule

/-- The odd part of a continuous function on the circle of circumference `2π`, restricted to
`[0, π]`: `P ↦ (P x - P (-x)) / 2`. -/
private noncomputable def oddPartRestrict :
    C(AddCircle (2 * π), ℝ) →ₗ[ℝ] C(Icc (0 : ℝ) π, ℝ) where
  toFun P := ⟨fun x =>
    (P ((x : ℝ) : AddCircle (2 * π)) - P ((-(x : ℝ) : ℝ) : AddCircle (2 * π))) / 2, by fun_prop⟩
  map_add' P Q := by
    ext x
    simp only [ContinuousMap.add_apply, ContinuousMap.coe_mk]
    ring
  map_smul' a P := by
    ext x
    simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.coe_mk, RingHom.id_apply]
    ring

private theorem oddPartRestrict_apply (P : C(AddCircle (2 * π), ℝ)) (x : Icc (0 : ℝ) π) :
    oddPartRestrict P x
      = (P ((x : ℝ) : AddCircle (2 * π)) - P ((-(x : ℝ) : ℝ) : AddCircle (2 * π))) / 2 := rfl

/-- The odd part does not increase the uniform norm. -/
private theorem norm_oddPartRestrict_le (P : C(AddCircle (2 * π), ℝ)) :
    ‖oddPartRestrict P‖ ≤ ‖P‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
  rw [oddPartRestrict_apply, Real.norm_eq_abs, abs_div, abs_two, div_le_iff₀ two_pos]
  calc |P ((x : ℝ) : AddCircle (2 * π)) - P ((-(x : ℝ) : ℝ) : AddCircle (2 * π))|
      ≤ |P ((x : ℝ) : AddCircle (2 * π))| + |P ((-(x : ℝ) : ℝ) : AddCircle (2 * π))| :=
        abs_sub _ _
    _ ≤ ‖P‖ + ‖P‖ := add_le_add (P.norm_coe_le_norm _) (P.norm_coe_le_norm _)
    _ = ‖P‖ * 2 := by ring

/-- The odd part of a real trigonometric polynomial on the circle is a sine polynomial. -/
private theorem oddPartRestrict_trigFun_mem (m : ℤ) :
    oddPartRestrict (trigFun (2 * π) m) ∈ span ℝ (range sinMap) := by
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · have hmem : (√2 : ℝ) • sinMap (m.natAbs - 1) ∈ span ℝ (range sinMap) :=
      Submodule.smul_mem _ _ (subset_span ⟨_, rfl⟩)
    convert hmem using 1
    ext x
    rw [oddPartRestrict_apply, trigFun_coe_of_neg hm, trigFun_coe_of_neg hm,
      ContinuousMap.smul_apply, sinMap_apply, smul_eq_mul]
    have hcast : ((m.natAbs - 1 : ℕ) : ℝ) + 1 = -(m : ℝ) := by
      have h1 : 1 ≤ m.natAbs := Int.natAbs_pos.2 hm.ne
      rw [Nat.cast_sub h1, Nat.cast_one, sub_add_cancel, Nat.cast_natAbs, Int.cast_abs,
        abs_of_neg (by exact_mod_cast hm)]
    rw [hcast, mul_neg, Real.sin_neg]
    ring
  · have h0 : oddPartRestrict (trigFun (2 * π) 0) = 0 := by
      ext x
      rw [oddPartRestrict_apply, trigFun_zero]
      simp
    rw [h0]
    exact Submodule.zero_mem _
  · have h0 : oddPartRestrict (trigFun (2 * π) m) = 0 := by
      ext x
      rw [oddPartRestrict_apply, trigFun_coe_of_pos hm, trigFun_coe_of_pos hm]
      simp only [mul_neg, Real.cos_neg, sub_self, zero_div, ContinuousMap.zero_apply]
    rw [h0]
    exact Submodule.zero_mem _

/-- **The sine polynomials are uniformly dense in `C₀[0, π]`**: a continuous function on `[0, π]`
vanishing at both ends is uniformly within `ε` of a sine polynomial, for every `ε > 0`.
The odd `2π`-periodic extension is a continuous function on the circle, hence uniformly
approximable by a real trigonometric polynomial, whose odd part is a sine polynomial as close to
the (odd) target. This is [han2009theoretical] Exercise 6.2.1. -/
theorem exists_mem_span_sinMap_norm_sub_lt {v : C(Icc (0 : ℝ) π, ℝ)}
    (h0 : v ⟨0, left_mem_Icc.2 Real.pi_pos.le⟩ = 0)
    (hπ : v ⟨π, right_mem_Icc.2 Real.pi_pos.le⟩ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ span ℝ (range sinMap), ‖v - p‖ < ε := by
  set F : C(AddCircle (2 * π), ℝ) := ⟨AddCircle.liftIco (2 * π) (-π) (oddReflect v), by
    refine AddCircle.liftIco_continuous ?_ (continuous_oddReflect h0).continuousOn
    rw [show -π + 2 * π = π by ring, oddReflect_neg_pi hπ,
      oddReflect_of_mem (right_mem_Icc.2 Real.pi_pos.le), hπ]⟩ with hF
  have hFx : ∀ x : ℝ, F (x : AddCircle (2 * π)) = oddPeriodicExtend v x := fun x => rfl
  obtain ⟨P, hP, hPF⟩ := exists_mem_span_trigFun_norm_sub_lt F hε
  refine ⟨oddPartRestrict P, ?_, ?_⟩
  · have hle : span ℝ (range (trigFun (2 * π)))
        ≤ (span ℝ (range sinMap)).comap oddPartRestrict :=
      span_le.2 (range_subset_iff.2 fun m => oddPartRestrict_trigFun_mem m)
    exact hle hP
  · have hFv : oddPartRestrict F = v := by
      ext x
      rw [oddPartRestrict_apply, hFx, hFx, oddPeriodicExtend_neg h0 hπ,
        oddPeriodicExtend_of_mem hπ x.2]
      ring
    calc ‖v - oddPartRestrict P‖ = ‖oddPartRestrict (F - P)‖ := by rw [map_sub, hFv]
      _ ≤ ‖F - P‖ := norm_oddPartRestrict_le _
      _ < ε := by rwa [norm_sub_rev]

end Density
