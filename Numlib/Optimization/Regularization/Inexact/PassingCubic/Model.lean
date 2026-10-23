import Numlib.Optimization.Regularization.Inexact.StepOne
import Numlib.Analysis.Calculus.TaylorModel.Scalar
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Actual passing cubic checks under large regularization

The actual computed quartic model is globally nonnegative. A selected reference would strictly
improve that model, so the complete ordered radius computation must instead finish with all
computed checks passing.
-/

namespace InexactRegularization.PassingCubic
open Polynomial InexactTrustRegion

/-- The actual cubic polynomial with zero linear term and a negative cubic derivative. -/
noncomputable def polynomial (B : ℝ) : ℝ[X] := C (B / 2) * X ^ 2 - C (1 / 6) * X ^ 3

/-- The genuine derivative jet of the computed cubic polynomial at zero. -/
noncomputable def jet (B : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  ftaylorSeries ℝ (polynomial B).eval 0

/-- The actual scalar jets of the computed cubic have their prescribed coefficients. -/
theorem polynomial_jets (B : ℝ) {j : ℕ} (hj : j ≤ 3) :
    iteratedDeriv j (polynomial B).eval 0 =
      if j = 0 then 0 else if j = 1 then 0 else if j = 2 then B else -1 := by
  rw [Polynomial.iteratedDeriv_eval]
  interval_cases j <;> norm_num [polynomial, Function.iterate_succ_apply',
    derivative_sub, derivative_C_mul, derivative_pow, derivative_X]


/-- Every computed Taylor degree through three has the exact scalar polynomial value. -/
theorem value (B : ℝ) {j : ℕ} (hj : j ≤ 3) (u : ℝ) :
    TaylorModel.ofJet (jet B) j u =
      if j ≤ 1 then 0 else B / 2 * u ^ 2 - if j = 2 then 0 else u ^ 3 / 6 := by
  change TaylorModel.eval (polynomial B).eval j 0 u = _
  rw [TaylorModel.eval_eq_sum_iteratedDeriv]
  have hh := fun i (hi : i ≤ 3) => polynomial_jets B hi
  interval_cases j <;>
    simp [Finset.sum_range_succ, hh, show (0 : ℕ) ≤ 3 by omega,
      show (1 : ℕ) ≤ 3 by omega, show (2 : ℕ) ≤ 3 by omega] <;> ring

/-- The genuine computed Taylor decrement has its exact quadratic and cubic terms. -/
theorem decrement (B : ℝ) {j : ℕ} (hj : j ≤ 3) (u : ℝ) :
    TaylorModel.jetDecrement (jet B) j u =
      if j ≤ 1 then 0 else -B / 2 * u ^ 2 + if j = 2 then 0 else u ^ 3 / 6 := by
  rw [TaylorModel.jetDecrement, value B hj, value B hj]
  split_ifs <;> ring

/-- The norm-regularized actual cubic jet is the displayed quartic polynomial. -/
theorem model_formula (B σ u : ℝ) : model (jet B) 3 σ u =
    B / 2 * u ^ 2 - u ^ 3 / 6 + σ / 24 * u ^ 4 := by
  simp only [model, ModelDecrease.penalized, value B (show 3 ≤ 3 by omega),
    Nat.not_ofNat_le_one, ↓reduceIte, Nat.succ_ne_self, Nat.factorial, Nat.succ_eq_add_one,
    Nat.reduceAdd, zero_add, mul_one, Nat.reduceMul, Nat.cast_ofNat, Real.norm_eq_abs,
    ← abs_pow, add_right_inj, mul_eq_mul_left_iff, abs_eq_self, div_eq_zero_iff,
    OfNat.ofNat_ne_zero, or_false]
  left
  positivity

/-- A sufficiently large regularization parameter makes the computed model globally
nonnegative. -/
theorem model_nonnegative {B σ : ℝ} (hσ : 0 < σ) (hB : 1 / 3 ≤ B * σ) (u : ℝ) :
    0 ≤ model (jet B) 3 σ u := by
  rw [model_formula]
  have h := sq_nonneg (σ * u - 2)
  have hquad : 0 ≤ B / 2 - u / 6 + σ / 24 * u ^ 2 := by
    have hh : 0 ≤ σ * (B / 2 - u / 6 + σ / 24 * u ^ 2) := by nlinarith
    exact nonneg_of_mul_nonneg_right hh hσ
  nlinarith [mul_nonneg (sq_nonneg u) hquad]
end InexactRegularization.PassingCubic
namespace InexactRegularization.PassingCubic
open InexactTrustRegion

/-- Every positive inherited radius admits a full actual Step1 computation that passes
every computed test. Its third-order output radius is bounded by the small quadratic
coefficient. -/
theorem exists_passing {B σ : ℝ} (hσ : 0 < σ) (hB : 1 / 3 ≤ B * σ)
    (initial : Fin 3 → ℝ) (hinit : ∀ a, 0 < initial a ∧ initial a ≤ 1) :
    ∃ (reduced : Fin 3 → ℝ) (reference : ℝ) (direction : Fin 3 → ℕ → ℝ)
      (count : Fin 3 → ℕ),
      StepOneComputation (jet B) 3 σ (1 / 2) (fun _ => 1 / 2)
        initial reduced reference direction count none ∧ reduced 2 ≤ 4 * B := by
  have hBpos : 0 < B := by nlinarith
  have hnorm : ∀ i, 2 ≤ i → i ≤ 3 → ‖jet B i‖ ≤ max B 1 := by
    intro i hi hip
    change ‖iteratedFDeriv ℝ i (polynomial B).eval 0‖ ≤ _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, polynomial_jets B hip]
    interval_cases i <;> norm_num [Real.norm_eq_abs, abs_of_pos hBpos]
  obtain ⟨reduced, reference, direction, count, selected, hone⟩ :=
    exists_stepOneComputation (ζ := (1 / 2 : ℝ)) (le_refl 3) (jet B)
      (lt_of_lt_of_le zero_lt_one (le_max_right B 1))
      hσ.le (by norm_num) (by norm_num) hnorm (fun _ => 1 / 2) initial
      (fun _ => by norm_num) hinit
  have hnone : selected = none := by
    cases hs : selected with
    | none => rfl
    | some a =>
      rw [hs] at hone
      have hi := hone.reference_improvement (by norm_num) (by norm_num) hinit
      have hn := model_nonnegative hσ hB reference
      have hz : model (jet B) 3 σ 0 = 0 := by rw [model_formula]; ring
      rw [hz] at hi
      linarith
  rw [hnone] at hone
  refine ⟨reduced, reference, direction, count, hone, ?_⟩
  have hδ := (hone.radius_bounds hinit 2).1
  have hl := TaylorModel.jetDecrement_le_jetCriticality (jet B) 3
    (δ := reduced 2) (s := reduced 2)
    (by simpa only [Real.norm_eq_abs, abs_of_pos hδ] using le_refl (reduced 2))
  have ha := hone.approximation 2 (count 2)
  rw [← hone.radius_eq 2] at ha
  have hp := hone.outcome 2
  have ho : modelOrder (2 : Fin 3) = 3 := rfl
  rw [ho] at ha hp
  rw [decrement B le_rfl] at hl
  norm_num at hl hp
  have hh := (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
    (ha.trans hp)
  have hδ2 : 0 < (reduced 2) ^ 2 := pow_pos hδ 2
  nlinarith
end InexactRegularization.PassingCubic
