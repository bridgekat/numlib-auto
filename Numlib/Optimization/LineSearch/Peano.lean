import Numlib.Optimization.LineSearch.DescentTrace
import Numlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Numlib.Analysis.Calculus.TaylorModel.Peano
import Numlib.Optimization.HighOrder.Criticality
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# A Peano obstruction to descent-direction linesearch

The polynomial `y² - 3x²y + 2x⁴` is strictly minimized at the origin along each
nonconstant straight line, yet decreases along `y = 3x²/2`. Its genuine fourth Taylor
polynomial equals the function, so the obstruction also violates approximate
fourth-order criticality, with a fixed positive tolerance at every radius at most one.

The coefficient choice `κ₁ = 1, κ₂ = 2` printed in the motivating example instead
has a global minimum at the origin. The saddle example uses `κ₁ = 3, κ₂ = 2`.
-/

open Filter Polynomial
namespace PeanoExample
/-- The real Euclidean plane of the Peano example. -/
abbrev E := EuclideanSpace ℝ (Fin 2)
/-- The Peano polynomial with its two coefficients displayed explicitly. -/
def objective (κ₁ κ₂ : ℝ) (x : E) : ℝ :=
  x 1 ^ 2 - κ₁ * x 0 ^ 2 * x 1 + κ₂ * x 0 ^ 4
/-- The corrected saddle example. -/
def saddle := objective 3 2
/-- The Peano polynomial is smooth to every order. -/
theorem smooth {n : WithTop ℕ∞} : ContDiff ℝ n saddle := by
  change ContDiff ℝ n (fun x : E => (EuclideanSpace.proj (1 : Fin 2) x) ^ 2 -
    3 * (EuclideanSpace.proj (0 : Fin 2) x) ^ 2 * EuclideanSpace.proj (1 : Fin 2) x +
    2 * (EuclideanSpace.proj (0 : Fin 2) x) ^ 4)
  fun_prop
/-- Every actual directional derivative at the origin vanishes. -/
theorem line_derivative (v : E) :
    iteratedDeriv 1 (fun t : ℝ => saddle (t • v)) 0 = 0 := by
  let P : ℝ[X] := C (v 1 ^ 2) * X ^ 2 - C (3 * v 0 ^ 2 * v 1) * X ^ 3 +
    C (2 * v 0 ^ 4) * X ^ 4
  have he : (fun t : ℝ => saddle (t • v)) = fun t => P.eval t := by
    funext t
    simp [saddle, objective, P]
    ring
  rw [he, Polynomial.iteratedDeriv_eval]
  simp [P]
/-- The actual fourth derivative along the descending parabola is negative. -/
theorem curve_fourth_derivative :
    iteratedDeriv 4 (fun t : ℝ => saddle (WithLp.toLp 2 ![t, 3 / 2 * t ^ 2])) 0 = -6 := by
  have he : (fun t : ℝ => saddle (WithLp.toLp 2 ![t, 3 / 2 * t ^ 2])) =
      fun t => (C (-(1 : ℝ) / 4) * X ^ 4).eval t := by
    funext t
    simp [saddle, objective]
    ring
  rw [he, Polynomial.iteratedDeriv_eval]
  norm_num [Function.iterate_succ_apply', Polynomial.derivative_mul,
    Polynomial.derivative_pow]
/-- Every nonconstant straight line has a strict local minimum at the origin. -/
theorem line_strict (v : E) (hv : v ≠ 0) :
    ∀ᶠ t : ℝ in nhds 0, t ≠ 0 → saddle 0 < saddle (t • v) := by
  by_cases hv1 : v 1 = 0
  · have hv0 : v 0 ≠ 0 := by
      intro h
      apply hv
      ext i
      fin_cases i <;> simp [h, hv1]
    filter_upwards [] with t ht
    have hp : 0 < 2 * (t * v 0) ^ 4 := by positivity
    simpa [saddle, objective, hv1] using hp
  · have hc : Continuous (fun t : ℝ => v 1 ^ 2 - 3 * v 0 ^ 2 * v 1 * t +
        2 * v 0 ^ 4 * t ^ 2) := by fun_prop
    have he : ∀ᶠ t in nhds 0, 0 < v 1 ^ 2 - 3 * v 0 ^ 2 * v 1 * t +
        2 * v 0 ^ 4 * t ^ 2 := by
      apply Filter.Tendsto.eventually_const_lt (by simpa using sq_pos_of_ne_zero hv1)
      simpa [ContinuousAt] using hc.continuousAt (x := 0)
    filter_upwards [he] with t ht htn
    have hp := mul_pos (sq_pos_of_ne_zero htn) ht
    have hh : saddle (t • v) =
        t ^ 2 * (v 1 ^ 2 - 3 * v 0 ^ 2 * v 1 * t + 2 * v 0 ^ 4 * t ^ 2) := by
      simp only [saddle, objective, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hh]
    simpa [saddle, objective] using hp

/-- The origin minimizes the Peano polynomial locally along every straight line. -/
theorem line_min (v : E) : IsLocalMin (fun t : ℝ => saddle (t • v)) 0 := by
  by_cases hv : v = 0
  · subst v
    filter_upwards [] with t
    simp
  · filter_upwards [line_strict v hv] with t ht
    by_cases h : t = 0
    · simp [h]
    · simpa only [zero_smul] using (ht h).le

/-- The genuine fourth-order Taylor polynomial at the origin is the objective itself. -/
theorem eval_four (s : E) : TaylorModel.eval saddle 4 0 s = saddle s := by
  let P : ℝ[X] := C (s 1 ^ 2) * X ^ 2 - C (3 * s 0 ^ 2 * s 1) * X ^ 3 +
    C (2 * s 0 ^ 4) * X ^ 4
  have he : (fun t : ℝ => saddle (0 + t • s)) = fun t => P.eval t := by
    funext t
    simp [saddle, objective, P]
    ring
  have hj (i : ℕ) (hi : i ≤ 4) :
      iteratedFDeriv ℝ i saddle 0 (fun _ => s) = (derivative^[i] P).eval 0 := by
    have h := TaylorModel.iteratedDeriv_affineLine (smooth (n := 4)) 0 s 0 hi
    rw [he, Polynomial.iteratedDeriv_eval] at h
    simpa using h.symm
  rw [TaylorModel.eval_eq_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hj 0 (by omega), hj 1 (by omega), hj 2 (by omega), hj 3 (by omega),
    hj 4 (by omega)]
  norm_num [P, Function.iterate_succ_apply', Polynomial.derivative_mul,
    Polynomial.derivative_pow, saddle, objective, smul_eq_mul]
  ring
/-- The objective decreases quartically along the descending parabola. -/
theorem curve_value (t : ℝ) : saddle (WithLp.toLp 2 ![t, 3 / 2 * t ^ 2]) = -(t ^ 4) / 4 := by
  change (3 / 2 * t ^ 2) ^ 2 - 3 * t ^ 2 * (3 / 2 * t ^ 2) + 2 * t ^ 4 = _
  ring

/-- A scaled point on the descending parabola belongs to the prescribed Euclidean ball. -/
theorem curve_norm {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ‖(WithLp.toLp 2 ![δ / 4, 3 / 2 * (δ / 4) ^ 2] : E)‖ ≤ δ := by
  apply (sq_le_sq₀ (norm_nonneg _) hδ).mp
  rw [EuclideanSpace.norm_sq_eq]
  rw [Fin.sum_univ_two]
  change ‖δ / 4‖ ^ 2 + ‖3 / 2 * (δ / 4) ^ 2‖ ^ 2 ≤ δ ^ 2
  simp only [Real.norm_eq_abs, sq_abs]
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  have hfour : δ ^ 4 ≤ δ ^ 2 := by nlinarith [sq_nonneg (δ ^ 2 - δ)]
  nlinarith

/-- Every neighborhood of the origin contains a point with smaller objective value. -/
theorem negative_near {r : ℝ} (hr : 0 < r) :
    ∃ s : E, ‖s‖ < r ∧ saddle s < saddle 0 := by
  let δ := min (r / 2) 1
  have hd : 0 < δ := lt_min (by positivity) (by norm_num)
  have hd1 : δ ≤ 1 := min_le_right _ _
  refine ⟨WithLp.toLp 2 ![δ / 4, 3 / 2 * (δ / 4) ^ 2], ?_, ?_⟩
  · exact (curve_norm hd.le hd1).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  · rw [curve_value]
    have hp : 0 < (δ / 4) ^ 4 := by positivity
    have hn : -(δ / 4) ^ 4 / 4 < 0 := by linarith
    simpa [saddle, objective] using hn

/-- The actual fourth-order Taylor criticality is bounded below at every small radius. -/
theorem criticality_four_lower {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    δ ^ 4 / 1024 ≤ TaylorModel.criticality saddle 4 0 δ := by
  have h := TaylorModel.decrement_le_criticality saddle 4 0 (curve_norm hδ hδ1)
  simp only [TaylorModel.decrement, eval_four] at h
  rw [curve_value] at h
  convert h using 1
  norm_num [saddle, objective]
  ring

/-- The origin fails fourth-order approximate criticality with tolerance one hundredth. -/
theorem not_four_approximate {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ¬ TaylorModel.criticality saddle 4 0 δ ≤ (1 / 100 : ℝ) * δ ^ 4 / 24 := by
  have h := criticality_four_lower hδ.le hδ1
  have hpow : 0 < δ ^ 4 := by positivity
  intro hc
  linarith

/-- Every order at least four fails its approximate criticality test at the origin. -/
theorem not_approximate_of_order {q : ℕ} (hq : 4 ≤ q) (δ : Fin q → ℝ)
    (hd : ∀ j, 0 < δ j ∧ δ j ≤ 1) :
    ¬ ∀ j : Fin q, TaylorModel.criticality saddle (j.val + 1) 0 (δ j) ≤
      (1 / 100 : ℝ) * δ j ^ (j.val + 1) / (j.val + 1).factorial := by
  intro h
  let j : Fin q := ⟨3, by omega⟩
  have hj := h j
  have hn := not_four_approximate (hd j).1 (hd j).2
  apply hn
  simpa [j, Nat.factorial] using hj

/-- The origin is not a local minimizer in the Euclidean plane. -/
theorem not_local_min : ¬ IsLocalMin saddle 0 := by
  intro h
  have he : ∀ᶠ s in nhds (0 : E), saddle 0 ≤ saddle s := h
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨s, hs, hn⟩ := negative_near hr
  exact (not_lt_of_ge (hb (by simpa [dist_eq_norm] using hs))) hn

/-- The coefficient choice one and two printed in the source has a global minimum at zero. -/
theorem printed_global_min (x : E) : objective 1 2 0 ≤ objective 1 2 x := by
  have he : objective 1 2 x = (x 1 - x 0 ^ 2 / 2) ^ 2 + 7 / 4 * x 0 ^ 4 := by
    unfold objective
    ring
  rw [he]
  have hp : 0 ≤ (x 1 - x 0 ^ 2 / 2) ^ 2 + 7 / 4 * x 0 ^ 4 := by positivity
  simpa [objective] using hp
end PeanoExample

namespace PeanoExample
/-- Every trace restricted to descent directions and initialized at the origin remains there. -/
theorem trace_stays {x : ℕ → E} (hx : LineSearch.DescentTrace saddle x)
    (hx0 : x 0 = 0) (k : ℕ) : x k = 0 := by
  rw [← hx0]
  apply hx.eq_initial
  intro v
  rw [hx0]
  simpa only [zero_add, iteratedDeriv_one] using line_derivative v
end PeanoExample
