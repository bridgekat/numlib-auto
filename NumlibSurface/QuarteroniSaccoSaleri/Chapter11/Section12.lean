import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section04
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section08

/-!
# Quarteroni–Sacco–Saleri §11.12: exercises

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §11.12 — the exercises the main text uses.

Exercise 1 (Heun's method has order 2, cited in §11.3), Exercise 2 (Crank–Nicolson has order 2,
(11.90)), Exercise 3 (a difference equation with a double root and a pair of complex conjugate
roots, cited in §11.4), Exercise 4 ((11.32) for simple roots), Exercise 5 (the matrix `R` of
(11.37) is nonsingular), and Exercise 12 with the modified Euler method (11.91), cited in §11.8.1.

Restatements of `Numlib/ODE/OneStep`, `Numlib/Algebra/LinearRecurrence`,
`Numlib/ODE/DifferenceEquation` and `Numlib/ODE/RungeKutta`, with the closed form of Exercise 3
verified here. Exercises 6–11 and 13–15 are not cited by the main text and are not formalized.

## Main results

* `exercise_11_1`, `exercise_11_2` — Heun and Crank–Nicolson have order two.
* `exercise_11_3` — the closed-form solution of the difference equation.
* `exercise_11_4`, `exercise_11_5` — simple roots: the form (11.32) and the nonsingular `R`.
* `equation_11_91`, `exercise_11_12` — the modified Euler method and the two-stage tableaux.

## Conventions

As in §11.3 and §11.8: solutions are `C³` on the closed horizon with derivatives
`derivWithin`/`iteratedDerivWithin`, and the Lipschitz constant `L ≥ 0` of `f` in `y` is uniform
on `[t₀, t₀ + T]`.
-/

open Set Filter Topology Asymptotics ODE ODE.OneStep
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h t y₀ : ℝ} {y : ℝ → ℝ} {n : ℕ}

/-! ### Exercises 1–2: Heun and Crank–Nicolson have order two -/

/-- **Exercise 11.1**: Heun's method (11.10) has order 2. Along a `C³` solution of a Cauchy
problem whose field is `L`-Lipschitz in `y`, with `|y''| ≤ M₂` and `|y'''| ≤ M₃` on the horizon,
`|τ_{n+1}(h)| ≤ (h²/12) M₃ + (h²/4) L M₂` for every step of every grid — the hint's splitting
`h τ_{n+1} = E₁ + E₂` with `E₁` the trapezoidal quadrature error and `E₂` the forward Euler error
inside `f` — hence (11.14) with `p = 2`; `ODE.OneStep.norm_lte_heun_le`,
`ODE.OneStep.hasOrderFor_heun`. -/
theorem exercise_11_1 (hT : 0 < T) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y) (hy3 : ContDiffOn ℝ 3 y (Icc t₀ (t₀ + T)))
    {M₂ M₃ : ℝ} (hM₂ : ∀ s ∈ Icc t₀ (t₀ + T), |iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s| ≤ M₂)
    (hM₃ : ∀ s ∈ Icc t₀ (t₀ + T), |iteratedDerivWithin 3 y (Icc t₀ (t₀ + T)) s| ≤ M₃) :
    (∀ h : ℝ, 0 < h → ∀ n, n < gridCount T h →
      |equation_11_12 (equation_11_10 f) h y t₀ n| ≤ h ^ 2 / 12 * M₃ + h ^ 2 / 4 * L * M₂) ∧
    equation_11_14 (equation_11_10 f) t₀ T y 2 := by
  obtain ⟨-, h2, h3⟩ := hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn_three (by linarith) hy3
  have h2' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s))
      (iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s) (Icc t₀ (t₀ + T)) s := fun s hs =>
    (h2 s hs).congr (fun s' hs' => (derivWithin_eq_of_cauchyProblem hT hy hs').symm)
      (derivWithin_eq_of_cauchyProblem hT hy hs).symm
  have hlip' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith ⟨L, hL⟩ (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq]
      exact hlip t ht y₁ y₂
  refine ⟨fun h hh n hn => ?_, hasOrderFor_heun hy.2 h2' h3 hM₂ hM₃ hlip'⟩
  exact norm_lte_heun_le hy.2 h2' h3 hM₂ hM₃ hlip' hh (node_mem_Icc_of_lt hh hn)
    (node_add_mem_Icc_of_lt hh hn)

/-- **Exercise 11.2**: Crank–Nicolson (11.9) has order 2. For a `C³` solution with `|y'''| ≤ M₃`
on the horizon, `|τ_{n+1}(h)| ≤ (h²/12) M₃` for every step of every grid — the norm form of
(11.90), `(y_{n+1} - y_n)/h = (f(t_n, y_n) + f(t_{n+1}, y_{n+1}))/2 - (h²/12) y'''(ξ_n)`, whose
remainder the book writes `f''(ξ_n, y(ξ_n))`, the second derivative of `s ↦ f(s, y(s)) = y'(s)`
— hence (11.14) with `p = 2`, so (11.9) agrees with (11.90) up to `O(h²)`;
`ODE.OneStep.norm_lte_crankNicolson_le`, `ODE.OneStep.hasOrderFor_crankNicolson`. The mean-value
form with the intermediate point `ξ_n` is not formalized. -/
theorem exercise_11_2 (hT : 0 < T) (hy : cauchyProblem f t₀ y₀ (Icc t₀ (t₀ + T)) y)
    (hy3 : ContDiffOn ℝ 3 y (Icc t₀ (t₀ + T))) {M₃ : ℝ}
    (hM₃ : ∀ s ∈ Icc t₀ (t₀ + T), |iteratedDerivWithin 3 y (Icc t₀ (t₀ + T)) s| ≤ M₃) :
    (∀ h : ℝ, 0 < h → ∀ n, n < gridCount T h →
      |equation_11_12 (equation_11_9 f) h y t₀ n| ≤ h ^ 2 / 12 * M₃) ∧
    equation_11_14 (equation_11_9 f) t₀ T y 2 := by
  obtain ⟨-, h2, h3⟩ := hasDerivWithinAt_iteratedDerivWithin_of_contDiffOn_three (by linarith) hy3
  have h2' : ∀ s ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (fun s => f s (y s))
      (iteratedDerivWithin 2 y (Icc t₀ (t₀ + T)) s) (Icc t₀ (t₀ + T)) s := fun s hs =>
    (h2 s hs).congr (fun s' hs' => (derivWithin_eq_of_cauchyProblem hT hy hs').symm)
      (derivWithin_eq_of_cauchyProblem hT hy hs).symm
  refine ⟨fun h hh n hn => ?_, hasOrderFor_crankNicolson hy.2 h2' h3 hM₃⟩
  exact norm_lte_crankNicolson_le hy.2 h2' h3 hM₃ hh (node_mem_Icc_of_lt hh hn)
    (node_add_mem_Icc_of_lt hh hn)

/-! ### Exercise 3: a difference equation with complex conjugate roots -/

/-- The closed form of Exercise 11.3: `u_n = 2^n (n/4 - 1) + 2^{(n-2)/2} sin(nπ/4) + n + 2`. -/
noncomputable def exercise_11_3_sol (n : ℕ) : ℝ :=
  2 ^ n * (n / 4 - 1) + (2 : ℝ) ^ (((n : ℝ) - 2) / 2) * Real.sin (n * Real.pi / 4) + n + 2

/-- The difference equation of Exercise 11.3,
`u_{n+4} - 6u_{n+3} + 14u_{n+2} - 16u_{n+1} + 8u_n = n`, as (11.28) with `α = (8, -16, 14, -6)`
and the source `φ_m = m - 4`. -/
theorem exercise_11_3_iff (u : ℕ → ℝ) :
    (equation_11_28 (![8, -16, 14, -6] : Fin 4 → ℝ)).IsSolutionWith (fun m => (m : ℝ) - 4) u ↔
      ∀ n, u (n + 4) - 6 * u (n + 3) + 14 * u (n + 2) - 16 * u (n + 1) + 8 * u n = n := by
  rw [equation_11_28_iff]
  refine forall_congr' fun n => ?_
  simp only [Fin.sum_univ_four, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero,
    Fin.val_one, Fin.val_two, add_zero]
  have e : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [e]
  push_cast
  constructor <;> intro H <;> linear_combination H

/-- `2^{(n-2)/2} = (√2)^n / 2`. -/
theorem exercise_11_3_rpow (n : ℕ) : (2 : ℝ) ^ (((n : ℝ) - 2) / 2) = Real.sqrt 2 ^ n / 2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    show ((n : ℝ) - 2) / 2 = 1 / 2 * n - 1 by ring, Real.rpow_sub (by norm_num), Real.rpow_one]

/-- `(1 + i)^n = (√2)^n e^{inπ/4}`: its imaginary part is `(√2)^n sin(nπ/4)`, the real solution
attached to the conjugate pair `1 ± i` of roots. -/
theorem exercise_11_3_im (n : ℕ) :
    ((1 + Complex.I) ^ n).im = Real.sqrt 2 ^ n * Real.sin (n * Real.pi / 4) := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have h1 : (1 + Complex.I) = (Real.sqrt 2 : ℂ) * Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    push_cast
    linear_combination (-(1 + Complex.I) / 2) * h2
  rw [h1, mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
    ← mul_assoc, ← Complex.ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
    mul_div_assoc]

/-- The sequence `2^{(n-2)/2} sin(nπ/4)` solves the homogeneous equation: it is `Im (1+i)^n / 2`,
and `1 + i` is a root of the characteristic polynomial `(r - 2)²(r² - 2r + 2)`. -/
theorem exercise_11_3_sin_rec (n : ℕ) :
    let w : ℕ → ℝ := fun n => (2 : ℝ) ^ (((n : ℝ) - 2) / 2) * Real.sin (n * Real.pi / 4)
    w (n + 4) - 6 * w (n + 3) + 14 * w (n + 2) - 16 * w (n + 1) + 8 * w n = 0 := by
  intro w
  have hw : ∀ m, w m = ((1 + Complex.I) ^ m).im / 2 := fun m => by
    simp only [w]
    rw [exercise_11_3_rpow, exercise_11_3_im]
    ring
  have hz : (1 + Complex.I) ^ (n + 4) - 6 * (1 + Complex.I) ^ (n + 3) +
      14 * (1 + Complex.I) ^ (n + 2) - 16 * (1 + Complex.I) ^ (n + 1) + 8 * (1 + Complex.I) ^ n
      = 0 := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (1 + Complex.I) ^ n * (Complex.I - 1) ^ 2 * hI
  have := congrArg Complex.im hz
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, add_zero, Complex.zero_im] at this
  simp only [hw]
  linarith

/-- **Exercise 11.3**: the solution of `u_{n+4} - 6u_{n+3} + 14u_{n+2} - 16u_{n+1} + 8u_n = n`
with `u₀ = 1`, `u₁ = 2`, `u₂ = 3`, `u₃ = 4` is
`u_n = 2^n (n/4 - 1) + 2^{(n-2)/2} sin(nπ/4) + n + 2`:
this sequence solves the equation with these starting values, and every solution with these
starting values is it. The characteristic polynomial is `(r - 2)²(r² - 2r + 2)`, with the double
root `2` (the solutions `2^n`, `n 2^n`) and the conjugate pair `1 ± i = √2 e^{±iπ/4}`, whose real
solution is `2^{n/2} sin(nπ/4)`; `n + 2` is a particular solution. The source prints
`sin(π/4)` for `sin(nπ/4)`. -/
theorem exercise_11_3 :
    (equation_11_28 (![8, -16, 14, -6] : Fin 4 → ℝ)).IsSolutionWith (fun m => (m : ℝ) - 4)
      exercise_11_3_sol ∧
    (exercise_11_3_sol 0 = 1 ∧ exercise_11_3_sol 1 = 2 ∧ exercise_11_3_sol 2 = 3 ∧
      exercise_11_3_sol 3 = 4) ∧
    ∀ u : ℕ → ℝ,
      (equation_11_28 (![8, -16, 14, -6] : Fin 4 → ℝ)).IsSolutionWith (fun m => (m : ℝ) - 4) u →
      u 0 = 1 → u 1 = 2 → u 2 = 3 → u 3 = 4 → ∀ n, u n = exercise_11_3_sol n := by
  have hrec : ∀ n, exercise_11_3_sol (n + 4) - 6 * exercise_11_3_sol (n + 3) +
      14 * exercise_11_3_sol (n + 2) - 16 * exercise_11_3_sol (n + 1) + 8 * exercise_11_3_sol n
      = n := by
    intro n
    have hs := exercise_11_3_sin_rec n
    simp only at hs
    simp only [exercise_11_3_sol]
    push_cast at hs ⊢
    linear_combination hs
  have hinit : exercise_11_3_sol 0 = 1 ∧ exercise_11_3_sol 1 = 2 ∧ exercise_11_3_sol 2 = 3 ∧
      exercise_11_3_sol 3 = 4 := by
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h3 : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.sin_pi_sub,
        Real.sin_pi_div_four]
    have h2 : Real.sin (2 * Real.pi / 4) = 1 := by
      rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring, Real.sin_pi_div_two]
    simp only [exercise_11_3_sol, exercise_11_3_rpow]
    refine ⟨?_, ?_, ?_, ?_⟩
    · norm_num
    · norm_num [Real.sin_pi_div_four]
      nlinarith [hsq]
    · norm_num [h2]
    · norm_num [h3]
      nlinarith [hsq]
  refine ⟨(exercise_11_3_iff _).2 hrec, hinit, fun u hu h0 h1 h2 h3 => ?_⟩
  rw [exercise_11_3_iff] at hu
  obtain ⟨g0, g1, g2, g3⟩ := hinit
  have key : ∀ n, u n = exercise_11_3_sol n ∧ u (n + 1) = exercise_11_3_sol (n + 1) ∧
      u (n + 2) = exercise_11_3_sol (n + 2) ∧ u (n + 3) = exercise_11_3_sol (n + 3) := by
    intro n
    induction n with
    | zero => exact ⟨by rw [h0, g0], by rw [h1, g1], by rw [h2, g2], by rw [h3, g3]⟩
    | succ n ih =>
      obtain ⟨e0, e1, e2, e3⟩ := ih
      refine ⟨e1, e2, e3, ?_⟩
      have hu' := hu n
      have hg' := hrec n
      rw [show n + 1 + 3 = n + 4 from rfl]
      linear_combination hu' - hg' + 6 * e3 - 14 * e2 + 16 * e1 - 8 * e0
  exact fun n => (key n).1

/-! ### Exercises 4–5: simple roots -/

/-- **Exercise 11.4**: if the characteristic polynomial (11.30) of the difference equation
(11.28) has `k` simple roots `r_1, …, r_k` (an injective enumeration of roots), every solution
`u` has the form (11.32), `u_n = ∑_i γ_i r_i^n`, for a unique `γ`, which is the solution of the
Vandermonde system `∑_i γ_i r_i^j = u_j`, `j = 0, …, k - 1`;
`LinearRecurrence.eq_sum_smul_pow_of_injective_roots`. -/
theorem exercise_11_4 {K : Type*} [Field K] {k : ℕ} (α : Fin k → K) {r : Fin k → K}
    (hr : Function.Injective r) (hroot : ∀ j, (equation_11_30 α).IsRoot (r j)) {u : ℕ → K}
    (hu : (equation_11_28 α).IsSolution u) :
    (∃! γ : Fin k → K, ∀ n, u n = ∑ j, γ j * r j ^ n) ∧
      ∀ γ : Fin k → K, (∀ n, u n = ∑ j, γ j * r j ^ n) →
        ∀ j : Fin k, ∑ i, γ i * r i ^ (j : ℕ) = u j := by
  have hroot' : ∀ j, (equation_11_28 α).charPoly.IsRoot (r j) := fun j => by
    rw [← equation_11_30_eq]
    exact hroot j
  refine ⟨?_, fun γ hγ j => (hγ j).symm⟩
  have := (equation_11_28 α).eq_sum_smul_pow_of_injective_roots hr hroot' hu
  simp only [smul_eq_mul] at this
  exact this

/-- **Exercise 11.5**: if the characteristic polynomial has simple roots `r_1, …, r_k`, the matrix
`R = (r_m^i)` of (11.37) is nonsingular: it is the transpose of the Vandermonde matrix of the
roots, whose determinant `∏_{i<j} (r_j - r_i)` is nonzero;
`LinearRecurrence.det_vandermonde_transpose_ne_zero`, `Matrix.det_vandermonde_ne_zero_iff`. -/
theorem exercise_11_5 {K : Type*} [Field K] {k : ℕ} {r : Fin k → K} (hr : Function.Injective r) :
    (equation_11_37_matrix r).det ≠ 0 := by
  rw [equation_11_37_matrix_eq]
  exact LinearRecurrence.det_vandermonde_transpose_ne_zero hr

/-! ### Exercise 12: the two-stage explicit methods -/

/-- **The modified Euler method (11.91)**, `u_{n+1} = u_n + h f(t_n + h/2, u_n + (h/2) f_n)`: the
increment of the tableau `ODE.ButcherTableau.modifiedEuler`. -/
noncomputable def equation_11_91 (f : ℝ → ℝ → ℝ) : OneStep.Increment ℝ :=
  ButcherTableau.modifiedEuler.explicitIncrement f

/-- (11.91), unfolded. -/
theorem equation_11_91_apply (f : ℝ → ℝ → ℝ) (t u v h : ℝ) :
    equation_11_91 f t u v h = f (t + h / 2) (u + h / 2 * f t u) := by
  rw [equation_11_91, ButcherTableau.explicitIncrement_modifiedEuler, smul_eq_mul]

/-- **Exercise 11.12**: Heun's method (11.10) is the explicit two-stage Runge–Kutta method with
Butcher array `c = (0, 1)`, `A = [[0, 0], [1, 0]]`, `b = (1/2, 1/2)`, and the modified Euler
method (11.91) is the one with `c = (0, 1/2)`, `A = [[0, 0], [1/2, 0]]`, `b = (0, 1)`;
`ODE.ButcherTableau.explicitIncrement_heun`, `ODE.ButcherTableau.explicitIncrement_modifiedEuler`.
-/
theorem exercise_11_12 :
    (ButcherTableau.heun.c = ![0, 1] ∧ ButcherTableau.heun.A = !![0, 0; 1, 0] ∧
      ButcherTableau.heun.b = ![1 / 2, 1 / 2] ∧ equation_11_71_explicit ButcherTableau.heun ∧
      equation_11_72 ButcherTableau.heun ∧
      equation_11_70_increment ButcherTableau.heun f = equation_11_10 f ∧
      ∀ u : ℕ → ℝ, equation_11_71 ButcherTableau.heun f h t₀ u ↔
        OneStep.IsOrbit (OneStep.ofIncrement (equation_11_10 f)) h t₀ u) ∧
    (ButcherTableau.modifiedEuler.c = ![0, 1 / 2] ∧
      ButcherTableau.modifiedEuler.A = !![0, 0; 1 / 2, 0] ∧
      ButcherTableau.modifiedEuler.b = ![0, 1] ∧
      equation_11_71_explicit ButcherTableau.modifiedEuler ∧
      equation_11_72 ButcherTableau.modifiedEuler ∧
      equation_11_70_increment ButcherTableau.modifiedEuler f = equation_11_91 f ∧
      ∀ u : ℕ → ℝ, equation_11_71 ButcherTableau.modifiedEuler f h t₀ u ↔
        OneStep.IsOrbit (OneStep.ofIncrement (equation_11_91 f)) h t₀ u) := by
  refine ⟨⟨rfl, rfl, rfl, ButcherTableau.heun_isExplicit, ButcherTableau.heun_isRowSum,
    ButcherTableau.explicitIncrement_heun f, fun u => ?_⟩,
    ⟨rfl, rfl, rfl, ButcherTableau.modifiedEuler_isExplicit, ButcherTableau.modifiedEuler_isRowSum,
      rfl, fun u => ?_⟩⟩
  · rw [equation_11_71, ButcherTableau.stepRel_eq_ofIncrement _ ButcherTableau.heun_isExplicit,
      ButcherTableau.explicitIncrement_heun]
    rfl
  · rw [equation_11_71,
      ButcherTableau.stepRel_eq_ofIncrement _ ButcherTableau.modifiedEuler_isExplicit]
    rfl

end QuarteroniSaccoSaleri.Chapter11
