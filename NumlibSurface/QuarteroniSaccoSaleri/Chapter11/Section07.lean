import Numlib.Nonlinear.FixedPoint
import NumlibSurface.QuarteroniSaccoSaleri.Chapter11.Section06

/-!
# Quarteroni–Sacco–Saleri §11.7: predictor–corrector methods

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*,
Springer, 2000, §11.7.

The fixed-point iteration (11.67) for the implicit step of a multistep method and its convergence
condition (11.68); the predictor–corrector schemes `P(EC)^m` and `P(EC)^mE` (11.69); Heun's
method as a predictor–corrector pair and the Adams–Bashforth–Moulton pair of Example 11.8; the
order of a pair (Property 11.3); the characteristic polynomials of the ABM pairs (Example 11.10).

Everything is the scalar case `E = ℝ` of `Numlib/ODE/Multistep` (`ODE.PredictorCorrector`), with
`Numlib/Nonlinear/FixedPoint` for (11.68). Example 11.9 (a numerical experiment), the
characteristic polynomials `Π_{P(EC)^m}`, `Π_{P(EC)^mE}` and Milne's device are not formalized.

## Main definitions

* `equation_11_69 PC f h t₀ u fv`, `equation_11_69_pece PC f h t₀ u` — the `P(EC)^m` and
  `P(EC)^mE` orbits of a pair `PC : ODE.PredictorCorrector`.
* `example_11_8_abm_pair` — the pair (AB2, AM3) with one correction.
* `pecOrder PC f t₀ T y q` — order `q` of the `P(EC)^mE` scheme along a solution.

## Main results

* `equation_11_68` — the convergence of the fixed-point iteration (11.67).
* `example_11_8`, `example_11_8_abm` — Heun and the (AB2, AM3) pair.
* `property_11_3` — the order of a predictor–corrector pair.
* `example_11_10` — the characteristic polynomials of the ABM pairs.

## Conventions

A pair `PC : ODE.PredictorCorrector` stores the predictor `(ã, b̃)` (explicit), the corrector
`(a, b, b_{-1})` padded to the predictor's `p + 1` steps, and the number `m` of corrections;
`PC.toPredictor` and `PC.toCorrector` are the two methods. The `P(EC)^m` orbit carries the two
sequences `u = u^{(m)}` and `fv = f^{(m-1)}` of the book; the `P(EC)^mE` orbit only `u`, the
function values being recomputed from the corrected values.
-/

open Set Filter Topology Asymptotics ODE Polynomial
open Finset (range)

namespace QuarteroniSaccoSaleri.Chapter11

variable {f : ℝ → ℝ → ℝ} {t₀ T h t : ℝ} {y : ℝ → ℝ} {n : ℕ}

/-! ### (11.67)–(11.68): the fixed-point iteration for the implicit step -/

/-- **The convergence condition (11.68)** for the fixed-point iteration (11.67)
`u_{n+1}^{(k+1)} = Ψ(u_{n+1}^{(k)})`, `Ψ(v) = G + h b_{-1} f(t_{n+1}, v)`, of the implicit step
`u_{n+1} = G + h b_{-1} f(t_{n+1}, u_{n+1})`, `G = ∑_{j=0}^p a_j u_{n-j} + h ∑_{j=0}^p b_j f_{n-j}`:
if `f` is `L`-Lipschitz in `y` and `h |b_{-1}| L < 1` (the book's `h < 1/(|b_{-1}| L)`), then `Ψ`
is a contraction, the step has a unique solution, and the iterates converge to it from every
starting value; Mathlib's `ContractingWith.fixedPoint` and
`ContractingWith.tendsto_iterate_fixedPoint` (the book's Theorem 6.1). -/
theorem equation_11_68 (M : LinearMultistep) {L : ℝ} (hL : 0 ≤ L) (t : ℝ)
    (hf : ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|) (hh : 0 ≤ h)
    (hcond : h * |M.bm1| * L < 1) (G : ℝ) :
    ∃ v : ℝ, v = G + h * M.bm1 * f t v ∧ (∀ w : ℝ, w = G + h * M.bm1 * f t w → w = v) ∧
      ∀ v₀ : ℝ, Tendsto (fun k => (fun w => G + h * M.bm1 * f t w)^[k] v₀) atTop (𝓝 v) := by
  set Ψ : ℝ → ℝ := fun w => G + h * M.bm1 * f t w with hΨ
  set K : NNReal := ⟨h * |M.bm1| * L, by positivity⟩ with hKdef
  have hK1 : (K : ℝ) = h * |M.bm1| * L := rfl
  have hK : ContractingWith K Ψ := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun y₁ y₂ => ?_⟩
    · rw [← NNReal.coe_lt_coe, hK1, NNReal.coe_one]
      exact hcond
    · simp only [hΨ, Real.dist_eq, hK1]
      rw [show G + h * M.bm1 * f t y₁ - (G + h * M.bm1 * f t y₂) =
        h * M.bm1 * (f t y₁ - f t y₂) by ring, abs_mul, abs_mul, abs_of_nonneg hh, mul_assoc,
        mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf y₁ y₂) (abs_nonneg _)) hh
  refine ⟨ContractingWith.fixedPoint Ψ hK, hK.fixedPoint_isFixedPt.symm,
    fun w hw => ?_, fun v₀ => hK.tendsto_iterate_fixedPoint v₀⟩
  exact hK.fixedPoint_unique hw.symm

/-! ### (11.69): the `P(EC)^m` and `P(EC)^mE` schemes -/

/-- **The `P(EC)^m` scheme (11.69)**: at every step `n ≥ p`, the predictor `[P]`
`u^{(0)}_{n+1} = ∑ ã_j u^{(m)}_{n-j} + h ∑ b̃_j f^{(m-1)}_{n-j}`, then `m` times the evaluation
`[E]` `f^{(k)}_{n+1} = f(t_{n+1}, u^{(k)}_{n+1})` and the correction `[C]`
`u^{(k+1)}_{n+1} = ∑ a_j u^{(m)}_{n-j} + h ∑ b_j f^{(m-1)}_{n-j} + h b_{-1} f^{(k)}_{n+1}`; the
sequences are `u = u^{(m)}` and `fv = f^{(m-1)}`. `PEC` is the case `m = 1`;
`ODE.PredictorCorrector.IsOrbitPEC`. -/
def equation_11_69 (PC : PredictorCorrector) (f : ℝ → ℝ → ℝ) (h t₀ : ℝ) (u fv : ℕ → ℝ) : Prop :=
  PC.IsOrbitPEC f h t₀ u fv

/-- **The `P(EC)^mE` scheme (§11.7)**: as `P(EC)^m`, with a final evaluation
`f^{(m)}_{n+1} = f(t_{n+1}, u^{(m)}_{n+1})` so that the stored function values are those of the
corrected values; `ODE.PredictorCorrector.IsOrbitPECE`. -/
def equation_11_69_pece (PC : PredictorCorrector) (f : ℝ → ℝ → ℝ) (h t₀ : ℝ) (u : ℕ → ℝ) : Prop :=
  PC.IsOrbitPECE f h t₀ u

/-- (11.69), unfolded: for `n ≥ p`, with `Ψ_n(v) = ∑ a_j u_{n-j} + h ∑ b_j fv_{n-j} + h b_{-1}
f(t_{n+1}, v)` and the predicted value `u^{(0)}_{n+1} = ∑ ã_j u_{n-j} + h ∑ b̃_j fv_{n-j}`,
`u_{n+1} = Ψ_n^m(u^{(0)}_{n+1})` and `fv_{n+1} = f(t_{n+1}, Ψ_n^{m-1}(u^{(0)}_{n+1}))`. -/
theorem equation_11_69_iff (PC : PredictorCorrector) (u fv : ℕ → ℝ) :
    equation_11_69 PC f h t₀ u fv ↔ ∀ n, PC.p ≤ n →
      u (n + 1) = (fun v => (∑ j : Fin (PC.p + 1), PC.a j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.b j * fv (n - j)) +
            h * PC.bm1 * f (grid t₀ h (n + 1)) v)^[PC.m]
        (∑ j : Fin (PC.p + 1), PC.pa j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.pb j * fv (n - j)) ∧
      fv (n + 1) = f (grid t₀ h (n + 1)) ((fun v => (∑ j : Fin (PC.p + 1), PC.a j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.b j * fv (n - j)) +
            h * PC.bm1 * f (grid t₀ h (n + 1)) v)^[PC.m - 1]
        (∑ j : Fin (PC.p + 1), PC.pa j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.pb j * fv (n - j))) := by
  unfold equation_11_69 PredictorCorrector.IsOrbitPEC PredictorCorrector.pecStep
    PredictorCorrector.correct PredictorCorrector.historySum PredictorCorrector.predict
  simp only [smul_eq_mul, Prod.mk.injEq, ← node_succ, grid]
  constructor
  · intro H n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact H m
  · intro H n
    exact H (n + PC.p) (Nat.le_add_left _ _)

/-- The `P(EC)^mE` scheme, unfolded: as `equation_11_69_iff` with the stored function values
`f_{n-j} = f(t_{n-j}, u_{n-j})` of the corrected values. -/
theorem equation_11_69_pece_iff (PC : PredictorCorrector) (u : ℕ → ℝ) :
    equation_11_69_pece PC f h t₀ u ↔ ∀ n, PC.p ≤ n →
      u (n + 1) = (fun v => (∑ j : Fin (PC.p + 1), PC.a j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.b j * f (grid t₀ h (n - j)) (u (n - j))) +
            h * PC.bm1 * f (grid t₀ h (n + 1)) v)^[PC.m]
        (∑ j : Fin (PC.p + 1), PC.pa j * u (n - j) +
          h * ∑ j : Fin (PC.p + 1), PC.pb j * f (grid t₀ h (n - j)) (u (n - j))) := by
  have e : ∀ (m : ℕ) (j : Fin (PC.p + 1)),
      node t₀ h (m + PC.p) - j * h = node t₀ h (m + PC.p - j) :=
    fun m j => LinearMultistep.node_sub_mul (by have := j.is_lt; omega)
  unfold equation_11_69_pece PredictorCorrector.IsOrbitPECE PredictorCorrector.peceStep
    PredictorCorrector.correct PredictorCorrector.historySum PredictorCorrector.predict
  simp only [smul_eq_mul, ← node_succ, grid, e]
  constructor
  · intro H n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact H m
  · intro H n
    exact H (n + PC.p) (Nat.le_add_left _ _)

/-- **Example 11.8, Heun's method**: Heun's method (11.10) is the predictor–corrector method with
forward Euler as predictor and Crank–Nicolson as corrector and one correction — the `P(EC)E`
scheme, whose stored function values are those of the corrected values (with `P(EC)` they would
be those of the predicted values, and the scheme would not be Heun's);
`ODE.PredictorCorrector.heun_eq_pece`. -/
theorem example_11_8 (u : ℕ → ℝ) :
    equation_11_69_pece (PredictorCorrector.ofPair (LinearMultistep.ofOneStep 1 1 0)
      (LinearMultistep.ofOneStep 1 (1 / 2) (1 / 2)) le_rfl 1) f h t₀ u ↔
      OneStep.IsOrbit (OneStep.ofIncrement (equation_11_10 f)) h t₀ u :=
  PredictorCorrector.heun_eq_pece

/-- **Example 11.8, the second pair**: the two-step Adams–Bashforth predictor (11.50) with the
two-step Adams–Moulton corrector (11.51) of order 3 and one correction. -/
noncomputable def example_11_8_abm_pair : PredictorCorrector :=
  ⟨1, ![1, 0], ![3 / 2, -1 / 2], ![1, 0], ![8 / 12, -1 / 12], 5 / 12, 1⟩

/-- The pair `example_11_8_abm_pair` is `(adamsBashforth 1, adamsMoulton 2)`, and its `PEC`
recursion is the displayed one, for `n ≥ 1`:
`u^{(0)}_{n+1} = u^{(1)}_n + (h/2)(3 f^{(0)}_n - f^{(0)}_{n-1})`,
`f^{(0)}_{n+1} = f(t_{n+1}, u^{(0)}_{n+1})`,
`u^{(1)}_{n+1} = u^{(1)}_n + (h/12)(5 f^{(0)}_{n+1} + 8 f^{(0)}_n - f^{(0)}_{n-1})`, with
`u = u^{(1)}` and `fv = f^{(0)}`. -/
theorem example_11_8_abm (u fv : ℕ → ℝ) :
    example_11_8_abm_pair.toPredictor = LinearMultistep.adamsBashforth 1 ∧
    example_11_8_abm_pair.toCorrector = LinearMultistep.adamsMoulton 2 ∧
    (equation_11_69 example_11_8_abm_pair f h t₀ u fv ↔ ∀ n, 1 ≤ n →
      u (n + 1) = u n + h / 12 *
        (5 * f (grid t₀ h (n + 1)) (u n + h / 2 * (3 * fv n - fv (n - 1))) +
          8 * fv n - fv (n - 1)) ∧
      fv (n + 1) = f (grid t₀ h (n + 1)) (u n + h / 2 * (3 * fv n - fv (n - 1)))) := by
  refine ⟨LinearMultistep.adamsBashforth_one_eq.symm,
    LinearMultistep.adamsMoulton_two_eq.symm, ?_⟩
  rw [equation_11_69_iff]
  change (∀ n, 1 ≤ n → u (n + 1) = (fun v => (∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(8 / 12 : ℝ), -1 / 12] j * fv (n - j)) +
        h * (5 / 12) * f (grid t₀ h (n + 1)) v)^[1]
      (∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
        h * ∑ j : Fin 2, ![(3 / 2 : ℝ), -1 / 2] j * fv (n - j)) ∧
    fv (n + 1) = f (grid t₀ h (n + 1)) ((fun v => (∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(8 / 12 : ℝ), -1 / 12] j * fv (n - j)) +
        h * (5 / 12) * f (grid t₀ h (n + 1)) v)^[1 - 1]
      (∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
        h * ∑ j : Fin 2, ![(3 / 2 : ℝ), -1 / 2] j * fv (n - j)))) ↔ _
  have e1 : ∀ n, ∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(3 / 2 : ℝ), -1 / 2] j * fv (n - j) =
      u n + h / 2 * (3 * fv n - fv (n - 1)) := fun n => by
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.sub_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have e2 : ∀ n v, (∑ j : Fin 2, ![(1 : ℝ), 0] j * u (n - j) +
      h * ∑ j : Fin 2, ![(8 / 12 : ℝ), -1 / 12] j * fv (n - j)) +
        h * (5 / 12) * f (grid t₀ h (n + 1)) v =
      u n + h / 12 * (5 * f (grid t₀ h (n + 1)) v + 8 * fv n - fv (n - 1)) := fun n v => by
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.sub_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  simp only [e1, e2, Function.iterate_one, Nat.sub_self, Function.iterate_zero, id]

/-! ### Property 11.3: the order of a predictor–corrector pair -/

/-- **Order `q` of the `P(EC)^mE` scheme** along a solution `y` on `[t₀, t₀ + T]`: the global
truncation error of the scheme (the maximum over the steps of `‖y_{n+1} - P(EC)^mE(y_n, …)‖ / h`)
is `O(h^q)`; `ODE.PredictorCorrector.HasOrderFor`. -/
def pecOrder (PC : PredictorCorrector) (f : ℝ → ℝ → ℝ) (t₀ T : ℝ) (y : ℝ → ℝ) (q : ℕ) : Prop :=
  PC.HasOrderFor f t₀ T y q

/-- **Property 11.3 (the order of a predictor–corrector pair)**: let the predictor have order `q̃`
and the corrector order `q` along the solution `y` of a Cauchy problem whose field is Lipschitz in
`y` uniformly on `[t₀, t₀ + T]`. Then the `P(EC)^mE` scheme has order `min(q, q̃ + m)`: the order
`q` of the corrector if `q̃ ≥ q`, or if `q̃ < q` and `m ≥ q - q̃`; the order `q̃ + m` if `q̃ < q`
and `m ≤ q - q̃`; `ODE.PredictorCorrector.hasOrderFor_of`. The book states the property for
`P(EC)^m`
and adds that `P(EC)^mE` has the same order; the `P(EC)^m` scheme, whose truncation error is not
defined in the backbone, and the clauses on the principal local truncation error (the same PLTE
as the corrector when `m > q - q̃`, a different one when `m = q - q̃`) are not formalized. The
book quotes the property without proof ([Lam91]). -/
theorem property_11_3 (PC : PredictorCorrector) {L : ℝ}
    (hf : ∀ t ∈ Icc t₀ (t₀ + T), ∀ y₁ y₂ : ℝ, |f t y₁ - f t y₂| ≤ L * |y₁ - y₂|)
    (hy : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivAt y (f t (y t)) t) {qp q : ℕ}
    (hP : definition_11_9_order PC.toPredictor t₀ T y qp)
    (hC : definition_11_9_order PC.toCorrector t₀ T y q) :
    pecOrder PC f t₀ T y (min q (qp + PC.m)) ∧
      (q ≤ qp → pecOrder PC f t₀ T y q) ∧
      (qp < q → q - qp ≤ PC.m → pecOrder PC f t₀ T y q) ∧
      (qp < q → PC.m ≤ q - qp → pecOrder PC f t₀ T y (qp + PC.m)) := by
  have hf' : ∀ t ∈ Icc t₀ (t₀ + T), LipschitzWith (Real.toNNReal L) (f t) := fun t ht =>
    LipschitzWith.of_dist_le_mul fun y₁ y₂ => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
      exact (hf t ht y₁ y₂).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have key : pecOrder PC f t₀ T y (min q (qp + PC.m)) := PC.hasOrderFor_of hf' hy hP hC
  refine ⟨key, fun hq => ?_, fun _ hm => ?_, fun _ hm => ?_⟩
  · rwa [min_eq_left (by omega)] at key
  · rwa [min_eq_left (by omega)] at key
  · rwa [min_eq_right (by omega)] at key

/-! ### Example 11.10: the ABM characteristic polynomials -/

/-- **Example 11.10**: for the Adams–Bashforth–Moulton pair `ODE.PredictorCorrector.abm p m`
with `p ≥ 2` steps (the `p`-step Adams–Bashforth predictor with the `p - 1`-step Adams–Moulton
corrector, padded), the predictor and the padded corrector have the same first characteristic
polynomial `ρ̂(r) = ρ̃(r) = r (r^{p-1} - r^{p-2})`, and the padded corrector's second characteristic
polynomial is `σ̂(r) = r σ(r)`, `σ` that of the Adams–Moulton corrector;
`ODE.PredictorCorrector.abm_charPoly`. -/
theorem example_11_10 (p m : ℕ) (hp : 2 ≤ p) :
    (characteristicPolynomials (PredictorCorrector.abm p m).toCorrector).1 =
        X * (X ^ (p - 1) - X ^ (p - 2)) ∧
      (characteristicPolynomials (PredictorCorrector.abm p m).toPredictor).1 =
        X * (X ^ (p - 1) - X ^ (p - 2)) ∧
      (characteristicPolynomials (PredictorCorrector.abm p m).toCorrector).2 =
        X * (characteristicPolynomials (LinearMultistep.adamsMoulton (p - 1))).2 := by
  obtain ⟨h1, h2, h3⟩ := PredictorCorrector.abm_charPoly p m hp
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
  have e : X ^ (k + 2) - X ^ (k + 2 - 1) = (X : ℝ[X]) * (X ^ (k + 2 - 1) - X ^ (k + 2 - 2)) := by
    rw [show k + 2 - 1 = k + 1 from rfl, show k + 2 - 2 = k from rfl]
    ring
  exact ⟨by rw [characteristicPolynomials, h1, e], by rw [characteristicPolynomials, h2, e], h3⟩

end QuarteroniSaccoSaleri.Chapter11
