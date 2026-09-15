import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Quarteroni–Sacco–Saleri §13.1: the heat equation

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §13.1.

The initial boundary value problem (13.1)–(13.4) — `u_t + L u = f` with `L u = -ν u_xx` on
`(0, 1)`, homogeneous Dirichlet conditions (13.2) and the initial datum (13.3) — is stated as a
*classical* solution predicate on the rectangle `[0, 1] × [0, T]`: the three partial derivatives
`u_t`, `u_x`, `u_xx` exist as one-sided derivatives within the rectangle's edges and are
continuous on it. That is exactly what the book's derivation of the energy estimate uses
("interchanged differentiation and integration", integration by parts in `x`); the weak
formulation (13.12) is §13.3's.

For `ν = 1`, `f = 0` and a datum that is a *finite* sine sum, (13.5) is verified outright: the
finite sum `∑ c_n e^{-(nπ)² t} sin(nπx)` is a classical solution
(`equation_13_5`), and its coefficients are the sine coefficients of the datum
(`equation_13_5_coeff`, from the orthogonality `∫₀¹ sin(mπx) sin(nπx) dx = δ_{mn}/2`). The book's
infinite series for a general datum is classical Fourier theory and is not claimed here.

The energy `E(t) = ∫₀¹ u(x, t)² dx` is `energy u t`, and the source energy `F(t) = ∫₀¹ f(x, t)² dx`
is `energy f t` — the same definition at the other function.

## Conventions

A function of space and time is `u : ℝ → ℝ → ℝ` written `u x t`, space first, as the book writes
`u(x, t)`. The derivative functions of a classical solution are carried explicitly by
`IsHeatSolutionWith` and existentially quantified in `IsHeatSolution`.
-/

open Set Filter Topology intervalIntegral
open scoped Real

namespace QuarteroniSaccoSaleri.Chapter13

/-! ### The classical Dirichlet problem (13.1)–(13.4) -/

/-- **A classical solution of the heat equation with its derivatives named**: `u` solves
(13.1)–(13.4) on `[0, 1] × [0, T]` with diffusivity `ν`, source `f`, initial datum `u₀` and the
three partial derivatives `ut = ∂u/∂t`, `ux = ∂u/∂x`, `uxx = ∂²u/∂x²`.  The derivatives are taken
*within* the rectangle's edges, one-sided at the boundary, and are required continuous on the
closed rectangle, which is what the energy computation of §13.1 uses. -/
def IsHeatSolutionWith (ν T : ℝ) (f : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) (u ut ux uxx : ℝ → ℝ → ℝ) : Prop :=
  (∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (u x) (ut x t) (Icc 0 T) t ∧
        HasDerivWithinAt (fun y => u y t) (ux x t) (Icc 0 1) x ∧
        HasDerivWithinAt (fun y => ux y t) (uxx x t) (Icc 0 1) x ∧
        ut x t - ν * uxx x t = f x t) ∧
    ContinuousOn (fun p : ℝ × ℝ => ut p.1 p.2) (Icc 0 1 ×ˢ Icc 0 T) ∧
    ContinuousOn (fun p : ℝ × ℝ => ux p.1 p.2) (Icc 0 1 ×ˢ Icc 0 T) ∧
    ContinuousOn (fun p : ℝ × ℝ => uxx p.1 p.2) (Icc 0 1 ×ˢ Icc 0 T) ∧
    (∀ t ∈ Icc (0 : ℝ) T, u 0 t = 0 ∧ u 1 t = 0) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, u x 0 = u₀ x)

/-- **The classical Dirichlet problem for the heat equation** ([quarteroni2000numerical]
(13.1)–(13.4)): `u` solves `u_t - ν u_xx = f` on `[0, 1] × [0, T]` with `u(0, t) = u(1, t) = 0`
and `u(x, 0) = u₀(x)`, in the classical sense of `IsHeatSolutionWith` for some choice of the
partial derivatives. -/
def IsHeatSolution (ν T : ℝ) (f : ℝ → ℝ → ℝ) (u₀ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ ut ux uxx, IsHeatSolutionWith ν T f u₀ u ut ux uxx

/-! ### The sine-series solution (13.5) -/

/-- The `N`-term sine sum `∑_{n < N} c_n sin(nπx)`, the initial datum of (13.5). -/
noncomputable def sineDatum (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, c k * Real.sin (k * π * x)

/-- The `N`-term separated solution `∑_{n < N} c_n e^{-(nπ)² t} sin(nπx)` of
[quarteroni2000numerical] (13.5). -/
noncomputable def sineSolution (N : ℕ) (c : ℕ → ℝ) (x t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, c k * Real.exp (-((k : ℝ) * π) ^ 2 * t) * Real.sin (k * π * x)

/-- **(13.5) for a finite sine datum** ([quarteroni2000numerical] (13.5)): with `ν = 1`, `f = 0`
and `u₀ = ∑_{n < N} c_n sin(nπx)`, the function `∑_{n < N} c_n e^{-(nπ)² t} sin(nπx)` is a
classical solution of (13.1)–(13.3) on `[0, 1] × [0, T]`, for every `T`.  The book's infinite
series for a general datum is classical Fourier theory and is not claimed. -/
theorem equation_13_5 (N : ℕ) (c : ℕ → ℝ) (T : ℝ) :
    IsHeatSolution 1 T (fun _ _ => 0) (sineDatum N c) (sineSolution N c) := by
  have hexp : ∀ a s : ℝ, HasDerivAt (fun r : ℝ => Real.exp (a * r)) (a * Real.exp (a * s)) s :=
    fun a s => by simpa [mul_comm] using ((hasDerivAt_id' (x := s)).const_mul a).exp
  have hsin : ∀ b y : ℝ, HasDerivAt (fun z : ℝ => Real.sin (b * z)) (b * Real.cos (b * y)) y :=
    fun b y => by simpa [mul_comm] using ((hasDerivAt_id' (x := y)).const_mul b).sin
  have hcos : ∀ b y : ℝ, HasDerivAt (fun z : ℝ => Real.cos (b * z)) (-(b * Real.sin (b * y))) y :=
    fun b y => by simpa [mul_comm] using ((hasDerivAt_id' (x := y)).const_mul b).cos
  refine ⟨fun x t => ∑ k ∈ Finset.range N,
      c k * (-((k : ℝ) * π) ^ 2 * Real.exp (-((k : ℝ) * π) ^ 2 * t)) * Real.sin (k * π * x),
    fun x t => ∑ k ∈ Finset.range N,
      c k * Real.exp (-((k : ℝ) * π) ^ 2 * t) * ((k : ℝ) * π * Real.cos (k * π * x)),
    fun x t => ∑ k ∈ Finset.range N,
      c k * Real.exp (-((k : ℝ) * π) ^ 2 * t) * ((k : ℝ) * π *
        -((k : ℝ) * π * Real.sin (k * π * x))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine fun x _ t _ => ⟨?_, ?_, ?_, ?_⟩
    · refine HasDerivAt.hasDerivWithinAt ?_
      exact HasDerivAt.fun_sum fun k _ =>
        (((hexp (-((k : ℝ) * π) ^ 2) t).const_mul (c k)).mul_const (Real.sin (k * π * x)))
    · refine HasDerivAt.hasDerivWithinAt ?_
      exact HasDerivAt.fun_sum fun k _ =>
        ((hsin ((k : ℝ) * π) x).const_mul (c k * Real.exp (-((k : ℝ) * π) ^ 2 * t)))
    · refine HasDerivAt.hasDerivWithinAt ?_
      exact HasDerivAt.fun_sum fun k _ =>
        (((hcos ((k : ℝ) * π) x).const_mul ((k : ℝ) * π)).const_mul
          (c k * Real.exp (-((k : ℝ) * π) ^ 2 * t)))
    · rw [one_mul, sub_eq_zero]
      exact Finset.sum_congr rfl fun k _ => by ring
  · fun_prop
  · fun_prop
  · fun_prop
  · exact fun t _ => ⟨by simp [sineSolution], by simp [sineSolution, Real.sin_nat_mul_pi]⟩
  · exact fun x _ => by simp [sineSolution, sineDatum]

/-- **Orthogonality of the sines on `(0, 1)`** ([quarteroni2000numerical] §13.1, the formula for
the coefficients `c_n` of (13.5)): `∫₀¹ sin(mπx) sin(nπx) dx = ½` if `m = n` and `0` otherwise,
for `n ≠ 0`.  The product is `(cos((m - n)πx) - cos((m + n)πx)) / 2` and `∫₀¹ cos(kπx) dx = 0`
for every nonzero integer `k`. -/
theorem integral_sin_mul_sin (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..1, Real.sin (m * π * x) * Real.sin (n * π * x))
      = if m = n then 1 / 2 else 0 := by
  have hsin : ∀ b y : ℝ, HasDerivAt (fun z : ℝ => Real.sin (b * z)) (b * Real.cos (b * y)) y :=
    fun b y => by simpa [mul_comm] using ((hasDerivAt_id' (x := y)).const_mul b).sin
  have hcont : ∀ c : ℝ, Continuous fun x : ℝ => Real.cos (c * x) :=
    fun c => Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hint : ∀ c : ℝ,
      IntervalIntegrable (fun x : ℝ => Real.cos (c * x)) MeasureTheory.volume 0 1 :=
    fun c => (hcont c).intervalIntegrable _ _
  have hcosint : ∀ c : ℝ, c ≠ 0 → (∫ x in (0 : ℝ)..1, Real.cos (c * x)) = Real.sin c / c := by
    intro c hc
    have hd : ∀ x ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => Real.sin (c * y) / c) (Real.cos (c * x)) x := by
      intro x _
      have h := (hsin c x).div_const c
      rwa [mul_div_cancel_left₀ _ hc] at h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hint c)]
    simp
  have hprod : ∀ x : ℝ, Real.sin (m * π * x) * Real.sin (n * π * x)
      = (Real.cos (((m : ℝ) - n) * π * x) - Real.cos (((m : ℝ) + n) * π * x)) / 2 := by
    intro x
    have h1 : ((m : ℝ) - n) * π * x = (m : ℝ) * π * x - (n : ℝ) * π * x := by ring
    have h2 : ((m : ℝ) + n) * π * x = (m : ℝ) * π * x + (n : ℝ) * π * x := by ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmnpos : (0 : ℝ) < (m : ℝ) + n := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hsum : (∫ x in (0 : ℝ)..1, Real.cos (((m : ℝ) + n) * π * x)) = 0 := by
    rw [hcosint _ (ne_of_gt (mul_pos hmnpos Real.pi_pos))]
    have hc : ((m : ℝ) + n) * π = ((m + n : ℕ) : ℝ) * π := by push_cast; ring
    rw [hc, Real.sin_nat_mul_pi, zero_div]
  rw [intervalIntegral.integral_congr (g := fun x =>
      (Real.cos (((m : ℝ) - n) * π * x) - Real.cos (((m : ℝ) + n) * π * x)) / 2)
      (fun x _ => hprod x),
    intervalIntegral.integral_div, intervalIntegral.integral_sub (hint _) (hint _), hsum]
  by_cases hmn : m = n
  · subst hmn
    simp
  · have hne : ((m : ℝ) - n) * π ≠ 0 := by
      have h0 : ((m : ℝ) - n) ≠ 0 := by
        simp only [sub_ne_zero]
        exact_mod_cast hmn
      exact mul_ne_zero h0 Real.pi_ne_zero
    rw [hcosint _ hne]
    have hcast : ((m : ℝ) - n) * π = (((m : ℤ) - n : ℤ) : ℝ) * π := by push_cast; ring
    rw [hcast, Real.sin_int_mul_pi, zero_div]
    simp [hmn]

/-- **The coefficients of (13.5)** ([quarteroni2000numerical] §13.1): for a finite sine datum
`u₀ = ∑_{k < N} c_k sin(kπx)` the coefficients are recovered by
`c_n = 2 ∫₀¹ u₀(x) sin(nπx) dx`, `1 ≤ n < N`, as the book states for a general datum. -/
theorem equation_13_5_coeff (N : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) (hnN : n < N) :
    c n = 2 * ∫ x in (0 : ℝ)..1, sineDatum N c x * Real.sin (n * π * x) := by
  have hint : ∀ k : ℕ, IntervalIntegrable
      (fun x : ℝ => c k * (Real.sin (k * π * x) * Real.sin (n * π * x)))
      MeasureTheory.volume 0 1 := fun k =>
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).const_mul
      (c k)).intervalIntegrable _ _
  have hcongr : ∀ x ∈ uIcc (0 : ℝ) 1, sineDatum N c x * Real.sin (n * π * x)
      = ∑ k ∈ Finset.range N, c k * (Real.sin (k * π * x) * Real.sin (n * π * x)) := by
    intro x _
    rw [sineDatum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hmem : n ∈ Finset.range N := Finset.mem_range.2 hnN
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_finsetSum fun k _ => hint k,
    Finset.sum_eq_single_of_mem n hmem fun k _ hkn => by
      rw [intervalIntegral.integral_const_mul, integral_sin_mul_sin k hn]
      simp [hkn],
    intervalIntegral.integral_const_mul]
  have hdiag : (∫ x in (0 : ℝ)..1, Real.sin (n * π * x) * Real.sin (n * π * x)) = 1 / 2 := by
    rw [integral_sin_mul_sin n hn]
    simp
  rw [hdiag]
  ring

/-! ### The energy and the a priori estimate (13.7) -/

/-- The energy `E(t) = ∫₀¹ u(x, t)² dx` of [quarteroni2000numerical] §13.1.  The source energy
`F(t) = ∫₀¹ f(x, t)² dx` of the same section is `energy f t`. -/
noncomputable def energy (u : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, u x t ^ 2

end QuarteroniSaccoSaleri.Chapter13
