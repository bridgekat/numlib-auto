import NumlibSurface.QuarteroniSaccoSaleri.Chapter08.Section02
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section01
import NumlibSurface.QuarteroniSaccoSaleri.Chapter09.Section02

/-!
# Quarteroni–Sacco–Saleri §9.3: Newton–Cotes formulae

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §9.3.

The Newton–Cotes formulae are the Lagrange quadrature formulae (9.2) at equally spaced nodes: the
*closed* ones with `x₀ = a`, `x_n = b`, `h = (b - a)/n` (`n ≥ 1`), and the *open* ones with
`x₀ = a + h`, `x_n = b - h`, `h = (b - a)/(n + 2)` (`n ≥ 0`). The section shows that their
weights `αᵢ = h wᵢ` depend only on `n` — `wᵢ = ∫₀ⁿ φᵢ` for the closed and `wᵢ = ∫₋₁ⁿ⁺¹ φᵢ` for
the open formulae, `φᵢ` the Lagrange basis at the integer nodes — that `wᵢ = w_{n-i}` (Table 9.2),
and proves Theorem 9.2, the error characterization (9.19)–(9.20) with its degrees of exactness,
through the divided-difference form of the error (9.21) and the derivative identity (9.22) of
Exercise 4; Table 9.6 shows the negative weight of the nine-node closed formula. Examples 9.2 and
9.3 and Tables 9.3–9.5 are numerical and are not formalized.

The backbone is `Numlib/Approximation/NewtonCotes`: the weights `Quadrature.newtonCotesWeight`,
`Quadrature.openNewtonCotesWeight`, the rules `Quadrature.closedNewtonCotes`,
`Quadrature.openNewtonCotes`, the constants `Quadrature.newtonCotesM`, `Quadrature.newtonCotesK`
(and their open versions), and the error theorem for the closed formulae with even `n`,
`Quadrature.exists_sub_closedNewtonCotes_eq_of_even`, which is the case the book proves. The
divided difference `f[x₀, …, x_n, x]` is chapter 8's `DividedDifference.newton f (Fin.snoc x t)`,
and (9.21) is the integrated form of chapter 8's (8.20).

## Main results

* `closedNewtonCotes_eq_lagrangeQuadrature`, `openNewtonCotes_eq_lagrangeQuadrature` — the
  Lagrange quadrature formula of §9.1 at the equispaced nodes is `h ∑ᵢ wᵢ f(xᵢ)`, with the
  interval-independent weights `wᵢ`; for `n = 0` the open formula is the midpoint rule.
* `newtonCotesWeight_symm`, `table_9_2`, `table_9_6` — the symmetry `wᵢ = w_{n-i}`, the first
  columns of Table 9.2, and the negative weight `w₂ < 0` of the closed formula with `n = 8`.
* `theorem_9_2_closed_even`, `theorem_9_2_M_closed` — (9.19) for the closed formulae with even
  `n`: `E_n(f) = M_n/(n + 2)! h^{n+3} f^{(n+2)}(ξ)`, `ξ ∈ (a, b)`, with
  `M_n = ∫₀ⁿ t π_{n+1}(t) dt < 0`.
* `theorem_9_2_degreeOfExactness_even`, `theorem_9_2_order_even` — the degree of exactness
  `n + 1` and the order of infinitesimal `n + 3` of the closed formulae with even `n`.
* `equation_9_21`, `exercise_9_4` — the error as `∫ f[x₀, …, x_n, x] ω_{n+1}(x) dx`, and the
  derivative identity `d/dx f[x₀, …, x_n, x] = f[x₀, …, x_n, x, x]`.

## Not yet stated

The clauses of Theorem 9.2 for odd `n` and for the open formulae ((9.20), and (9.19) with
`M_n > 0`), which the book states without proof, wait on the backbone's sign analysis of the
corresponding Peano kernels (`Quadrature.exists_sub_closedNewtonCotes_eq_of_odd` and its open
companions); their nodes are open in the plan.

## Conventions

As in §9.2: `f ∈ C^k([a, b])` is `ContDiffOn ℝ k f U` on an open `U ⊇ [a, b]` and `f^{(k)}` is
`iteratedDeriv k f`. The nodal polynomial `π_{n+1}(t) = ∏ᵢ₌₀ⁿ (t - i)` is the backbone's
`Quadrature.intNodal n`, whose evaluation is `Quadrature.intNodal_eval`.
-/

open Set intervalIntegral
open scoped Polynomial

namespace QuarteroniSaccoSaleri.Chapter09

variable {a b : ℝ} {f : ℝ → ℝ} {U : Set ℝ} {n : ℕ}

/-! ### The weights do not depend on the interval -/

/-- **§9.3, closed formulae.** For `n ≥ 1`, `h = (b - a)/n` and the nodes `xᵢ = a + i h`, the
Lagrange quadrature formula (9.2) of §9.1 has the weights `αᵢ = ∫_a^b lᵢ = h wᵢ` with
`wᵢ = ∫₀ⁿ φᵢ(t) dt` (`Quadrature.newtonCotesWeight n i`) independent of `[a, b]`, and reads
`I_n(f) = h ∑ᵢ wᵢ f(xᵢ)`, the backbone's `Quadrature.closedNewtonCotes n f a b`. -/
theorem closedNewtonCotes_eq_lagrangeQuadrature (hn : 1 ≤ n) (hab : a < b) :
    (∀ i, lagrangeWeights (fun k : Fin (n + 1) => a + k * ((b - a) / n)) a b i
        = (b - a) / n * Quadrature.newtonCotesWeight n i) ∧
      ∀ f : ℝ → ℝ, lagrangeQuadrature (fun k : Fin (n + 1) => a + k * ((b - a) / n)) a b f
        = Quadrature.closedNewtonCotes n f a b :=
  ⟨fun i => Quadrature.integral_basis_eq_mul_newtonCotesWeight hn hab i, fun f =>
    (Quadrature.closedNewtonCotes_eq_sum_integral_basis hn hab f).symm⟩

/-- **§9.3, open formulae.** For `n ≥ 0`, `h = (b - a)/(n + 2)` and the nodes `xᵢ = a + (i + 1) h`,
the Lagrange quadrature formula (9.2) has the weights `αᵢ = h wᵢ` with `wᵢ = ∫₋₁ⁿ⁺¹ φᵢ(t) dt`
(`Quadrature.openNewtonCotesWeight n i`) and reads `I_n(f) = h ∑ᵢ wᵢ f(xᵢ)`, the backbone's
`Quadrature.openNewtonCotes n f a b`; in the special case `n = 0`, `w₀ = 2` and the formula is the
midpoint rule (9.5). -/
theorem openNewtonCotes_eq_lagrangeQuadrature (hab : a < b) :
    (∀ i, lagrangeWeights (fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2))) a b i
        = (b - a) / (n + 2) * Quadrature.openNewtonCotesWeight n i) ∧
      (∀ f : ℝ → ℝ,
        lagrangeQuadrature (fun k : Fin (n + 1) => a + (k + 1) * ((b - a) / (n + 2))) a b f
          = Quadrature.openNewtonCotes n f a b) ∧
      Quadrature.openNewtonCotesWeight 0 0 = 2 ∧
      ∀ f : ℝ → ℝ, Quadrature.openNewtonCotes 0 f a b = (b - a) * f ((a + b) / 2) :=
  ⟨fun i => Quadrature.integral_basis_eq_mul_openNewtonCotesWeight hab i, fun f =>
    (Quadrature.openNewtonCotes_eq_sum_integral_basis hab f).symm,
    by rw [Quadrature.openNewtonCotesWeight_zero]; rfl,
    fun f => Quadrature.openNewtonCotes_zero f a b⟩

/-- **§9.3: "the weights `wᵢ` and `w_{n-i}` are equal"**, for the closed and for the open
formulae: the substitution `t ↦ n - t` carries `φᵢ` to `φ_{n-i}` and the reference interval to
itself. -/
theorem newtonCotesWeight_symm (n : ℕ) (i : Fin (n + 1)) :
    Quadrature.newtonCotesWeight n (Fin.rev i) = Quadrature.newtonCotesWeight n i ∧
      Quadrature.openNewtonCotesWeight n (Fin.rev i) = Quadrature.openNewtonCotesWeight n i :=
  ⟨Quadrature.newtonCotesWeight_symm i, Quadrature.openNewtonCotesWeight_symm i⟩

/-- **Table 9.2, the first columns.** Closed formulae: `n = 1`: `(1/2, 1/2)`; `n = 2`:
`(1/3, 4/3, 1/3)`; `n = 3`: `(3/8, 9/8, 9/8, 3/8)`. Open formulae: `n = 0`: `(2)`; `n = 2`:
`(8/3, -4/3, 8/3)` — "the presence of negative weights in open formulae for `n ≥ 2`". (The
remaining columns of the printed table are damaged in the source and are not stated.) -/
theorem table_9_2 :
    Quadrature.newtonCotesWeight 1 = ![1 / 2, 1 / 2] ∧
      Quadrature.newtonCotesWeight 2 = ![1 / 3, 4 / 3, 1 / 3] ∧
      Quadrature.newtonCotesWeight 3 = ![3 / 8, 9 / 8, 9 / 8, 3 / 8] ∧
      Quadrature.openNewtonCotesWeight 0 = ![2] ∧
      Quadrature.openNewtonCotesWeight 2 = ![8 / 3, -4 / 3, 8 / 3] :=
  ⟨Quadrature.newtonCotesWeight_one, Quadrature.newtonCotesWeight_two,
    Quadrature.newtonCotesWeight_three, Quadrature.openNewtonCotesWeight_zero,
    Quadrature.openNewtonCotesWeight_two⟩

/-! ### Theorem 9.2 -/

/-- **Theorem 9.2, closed formulae with even `n`, (9.19).** For even `n ≥ 2` and
`f ∈ C^{n+2}([a, b])`, the error of the closed Newton–Cotes formula is
`E_n(f) = M_n/(n + 2)! h^{n+3} f^{(n+2)}(ξ)` with `h = (b - a)/n`, `ξ ∈ (a, b)` and
`M_n = ∫₀ⁿ t π_{n+1}(t) dt` (`Quadrature.newtonCotesM n`; see `theorem_9_2_M_closed` for its
value and sign). The backbone's `Quadrature.exists_sub_closedNewtonCotes_eq_of_even`, proved
along the book's route: (9.21), integration by parts against `W(x) = ∫_a^x ω_{n+1}`, (9.22), the
positivity of `W` inside `(a, b)` and the mean value theorem. -/
theorem theorem_9_2_closed_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) :
    ∃ ξ ∈ Ioo a b, (∫ x in a..b, f x) - Quadrature.closedNewtonCotes n f a b
      = Quadrature.newtonCotesM n / (n + 2).factorial * ((b - a) / n) ^ (n + 3)
        * iteratedDeriv (n + 2) f ξ :=
  Quadrature.exists_sub_closedNewtonCotes_eq_of_even hn hn0 hab hU hUab hf

/-- **Theorem 9.2, the constant `M_n` of the closed formulae.** `M_n = ∫₀ⁿ t π_{n+1}(t) dt` with
`π_{n+1}(t) = ∏ᵢ₌₀ⁿ (t - i)`, and `M_n < 0` for even `n ≥ 2` (the sign the book quotes from
[IK66]). -/
theorem theorem_9_2_M_closed (hn : Even n) (hn0 : 0 < n) :
    Quadrature.newtonCotesM n = (∫ t in (0 : ℝ)..n, t * ∏ i : Fin (n + 1), (t - (i : ℕ))) ∧
      Quadrature.newtonCotesM n < 0 :=
  ⟨by simp only [Quadrature.newtonCotesM, Quadrature.intNodal_eval],
    Quadrature.newtonCotesM_neg hn hn0⟩

/-- **Theorem 9.2, the degree of exactness of the closed formulae with even `n`.** "From (9.19),
it turns out that the degree of exactness is equal to `n + 1`": the closed formula is exact on
`ℙ_{n+1}` and not on `x^{n+2}`. -/
theorem theorem_9_2_degreeOfExactness_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) :
    (∀ p : ℝ[X], p.degree ≤ n + 1 →
        (∫ x in a..b, p.eval x) = Quadrature.closedNewtonCotes n (fun x => p.eval x) a b) ∧
      (∫ x in a..b, x ^ (n + 2)) ≠ Quadrature.closedNewtonCotes n (fun x => x ^ (n + 2)) a b :=
  ⟨fun _ hp => Quadrature.integral_eq_closedNewtonCotes_of_even hn hn0 hab hp,
    Quadrature.not_integral_eq_closedNewtonCotes_of_even hn hn0 hab⟩

/-- **Theorem 9.2, the order of infinitesimal of the closed formulae with even `n`.** "The order
of infinitesimal is `n + 3`": for `f ∈ C^{n+2}([a, b])` with `|f^{(n+2)}| ≤ M` on `[a, b]`,
`|E_n(f)| ≤ |M_n|/(n + 2)! M h^{n+3}`, `h = (b - a)/n` — the error is `O(h^{n+3})`. -/
theorem theorem_9_2_order_even (hn : Even n) (hn0 : 0 < n) (hab : a < b) (hU : IsOpen U)
    (hUab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U) {M : ℝ}
    (hM : ∀ x ∈ Icc a b, |iteratedDeriv (n + 2) f x| ≤ M) :
    |(∫ x in a..b, f x) - Quadrature.closedNewtonCotes n f a b|
      ≤ |Quadrature.newtonCotesM n| / (n + 2).factorial * M * ((b - a) / n) ^ (n + 3) := by
  obtain ⟨ξ, hξ, h⟩ := theorem_9_2_closed_even hn hn0 hab hU hUab hf
  have hh : (0 : ℝ) ≤ ((b - a) / n) ^ (n + 3) := by
    have : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    positivity
  rw [h, abs_mul, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n + 2).factorial),
    abs_of_nonneg hh]
  calc |Quadrature.newtonCotesM n| / (n + 2).factorial * ((b - a) / n) ^ (n + 3)
        * |iteratedDeriv (n + 2) f ξ|
      ≤ |Quadrature.newtonCotesM n| / (n + 2).factorial * ((b - a) / n) ^ (n + 3) * M := by
        gcongr
        exact hM ξ (Ioo_subset_Icc_self hξ)
    _ = _ := by ring

/-! ### The divided-difference form of the error -/

/-- **(9.21).** For distinct nodes `x₀, …, x_n` and `f ∈ C⁰([a, b])`, the error of the Lagrange
quadrature formula is `E_n(f) = I(f) - I_n(f) = ∫_a^b f[x₀, …, x_n, x] ω_{n+1}(x) dx`, with
`f[x₀, …, x_n, x] = DividedDifference.newton f (Fin.snoc x t)` and `ω_{n+1}(x) = ∏ᵢ (x - xᵢ)`:
chapter 8's (8.20), `f - Π_n f = ω_{n+1} f[x₀, …, x_n, ·]` off the nodes, integrated over
`[a, b]` (the nodes are a null set). -/
theorem equation_9_21 (hab : a ≤ b) {x : Fin (n + 1) → ℝ} (hx : Function.Injective x)
    (hf : ContinuousOn f (Icc a b)) :
    (∫ t in a..b, f t) - lagrangeQuadrature x a b f
      = ∫ t in a..b, DividedDifference.newton f (Fin.snoc x t) * ∏ i, (t - x i) := by
  rw [lagrangeQuadrature_eq_integral_interpolate, ← integral_sub (hf.intervalIntegrable_of_Icc hab)
    ((Polynomial.continuous _).intervalIntegrable _ _)]
  refine integral_congr_ae ?_
  filter_upwards [(Set.finite_range x).countable.ae_notMem MeasureTheory.volume] with t ht _
  rw [Chapter08.equation_8_20 f hx fun i hi => ht ⟨i, hi⟩, mul_comm]

/-- **Exercise 4, (9.22).** For distinct nodes `x₀, …, x_n`, a point `x` off the nodes and `f`
differentiable at `x`, `d/dx f[x₀, …, x_n, x] = f[x₀, …, x_n, x, x]`: the derivative of the
divided difference in its last argument is the confluent divided difference with `x` doubled,
that is, the coefficient of `X^{n+2}` in the Hermite interpolant of `f` at the simple nodes
`x₀, …, x_n` and the double node `x` (`Hermite.interpolate (Fin.snoc x t) (Fin.snoc 0 1) f`).
The backbone's `DividedDifference.hasDerivAt_newton_snoc`. -/
theorem exercise_9_4 {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) {t : ℝ}
    (ht : t ∉ Set.range x) (hf : DifferentiableAt ℝ f t) :
    HasDerivAt (fun y => DividedDifference.newton f (Fin.snoc x y))
      ((Hermite.interpolate (Fin.snoc x t) (Fin.snoc (fun _ => 0) 1) f).coeff (n + 2)) t :=
  DividedDifference.hasDerivAt_newton_snoc hx ht hf

/-! ### Table 9.6 -/

/-- **Table 9.6: "the weights of the closed Newton–Cotes formula with `n = 8` do not have the
same sign."** The weight `w₂` of the nine-node closed formula is negative (its value is
`-928/28350`; the printed table lists the weights scaled by `4` with the signs lost). From the
moment equations `∑ᵢ wᵢ iᵏ = 8^{k+1}/(k + 1)`, `k = 0, …, 8`, which determine the weights. -/
theorem table_9_6 : Quadrature.newtonCotesWeight 8 2 < 0 := by
  set w := Quadrature.newtonCotesWeight 8 with hw
  have h : ∀ k : ℕ, k ≤ 8 → w 0 * 0 ^ k + w 1 * 1 ^ k + w 2 * 2 ^ k + w 3 * 3 ^ k + w 4 * 4 ^ k
      + w 5 * 5 ^ k + w 6 * 6 ^ k + w 7 * 7 ^ k + w 8 * 8 ^ k = (8 : ℝ) ^ (k + 1) / (k + 1) := by
    intro k hk
    have := Quadrature.sum_newtonCotesWeight_mul_pow (n := 8) (k := k) (by norm_num) hk
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Fin.isValue,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_zero] at this
    rw [← this]
    push_cast
    ring
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num)
  have h6 := h 6 (by norm_num)
  have h7 := h 7 (by norm_num)
  have h8 := h 8 (by norm_num)
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8
  linarith

end QuarteroniSaccoSaleri.Chapter09
