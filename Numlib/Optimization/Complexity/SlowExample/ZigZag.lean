import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Numlib.Analysis.Calculus.Gradient
import Numlib.Analysis.Calculus.MeanValue
import Numlib.Approximation.HermiteSpline
import Numlib.Optimization.LineSearch.Backtracking

/-!
# A zig-zag example for steepest descent

The two-dimensional example of [cartis2022evaluation] Theorem 2.2.5 (Appendix B, Lemmas B.2.1–B.2.6,
adapted there from [cartis2012steepest]): a twice continuously differentiable function with bounded
Hessian, bounded below with constants independent of the tolerance `ε`, on which steepest descent
with the "first local minimizer" line search, started at the origin, takes exactly `k_ε = ε⁻²`
iterations to reach `‖∇f‖ ≤ ε`. With the corridor function used here, every step is also the first
*global* minimizer along the steepest-descent ray, so the example applies to the exact line search
(2.2.26) itself.

## Construction

Fix `ε > 0` with `k_ε ε² = 1` (`ZigZag.IsAdmissible ε k_ε`), let `ω_k = ε (k_ε - k)/k_ε` (B.2.4)
and `a_k = ε + ω_k` (`ZigZag.stepLen`). The iterates are `(x_0, y_0) = 0`,
`(x_{k+1}, y_{k+1}) = (x_k, y_k) + a_k (1, (-1)^k)` (`zigZagIterate`). The function is
(`zigZagFunction`, (B.2.24))
`f(x, y) = (f₁(x) + ψ(y - y_mid(x)))/√2`, where

* `f₁` (`ZigZag.f₁`) has slope `-a_k` and zero curvature at `x_k`, with the quintic pieces (B.2.7)
  on `[x_k, x_{k+1}]`, is linear (slope `-2ε`) on `(-∞, 0]` and levels off to a constant over
  `[x_{k_ε}, x_{k_ε} + 1]`;
* `y_mid` (`ZigZag.mid`) is the middle of the corridor (B.2.13)–(B.2.15): it moves by
  `(-1)^k (ω_k - ω_{k+1})/2` along the quintic smooth step `10t³ - 15t⁴ + 6t⁵` on
  `[x_k, x_{k+1}]` and is constant elsewhere;
* `ψ` (`ZigZag.capSq`) is a capped square: `u²` for `|u| ≤ 1`, with second derivative decreasing
  from `2` to `0` along the smooth step on `1 ≤ |u| ≤ 2`, and linear (slope `±3`) for `|u| ≥ 2`.

Both `f₁` and `y_mid` are written as finite sums of fixed profiles (`ZigZag.ramp`,
`ZigZag.smoothStep`) in the local variables `(x - x_j)/a_j`; on each `[x_k, x_{k+1}]` all but one
term is saturated (`ZigZag.sum_localVar_eq`), which gives the book's piecewise formulas and the
uniform bounds on derivatives.

## Main results

* `Optimization.zigZag_gradient` — (B.2.25): `∇f(x_k, y_k) = -(a_k/√2)(1, (-1)^k)`, so
  `‖∇f(x_k, y_k)‖ = ε + ω_k`, and `(x_{k+1}, y_{k+1}) = (x_k, y_k) - √2 ∇f(x_k, y_k)`.
* `Optimization.zigZag_bounds` — Lemmas B.2.4–B.2.5: `f` is `C¹`, `f ≥ -5` and `∇f` is
  `350`-Lipschitz, for every admissible `ε`.
* `Optimization.zigZag_hessian_bounds` — Lemma B.2.3 and the second-derivative form of B.2.5:
  `f` and the corridor function `f₂` are `C²` with second derivatives bounded independently of
  `ε`, `∇f₂` is bounded and `f₂` is bounded on the bands around the corridor.
* `Optimization.zigZag_isFirstLocalLineMin` — Lemma B.2.6 as proved in the book: the step `√2`
  is the first local minimizer along `-∇f(x_k, y_k)` (`LineSearch.IsFirstLocalLineMin`) for
  `k < k_ε` ((B.2.32)–(B.2.36), `ZigZag.slope_neg`).
* `Optimization.zigZag_isExactLineMin` — Lemma B.2.6 as needed for Theorem 2.2.5: the step `√2`
  is the first global minimizer along the ray (`LineSearch.IsExactLineMin`), because the slope is
  nonnegative beyond `(x_{k+1}, y_{k+1})` (`ZigZag.slope_nonneg`).

## Deviations from the book

* **The corridor function.** The book's `f₂` (B.2.19) equals `(y - y_mid(x))²` inside the corridor
  `y_low(x) ≤ y ≤ y_up(x)` and is continued by quintic Hermite transitions to the constant `8
  δ(x)²`. Here `f₂(x, y) = ψ(y - y_mid(x))` with the capped square `ψ`: the two agree on the
  corridor (whose half-width `δ(x)/2` is at most `1`), which is where the iteration path runs and
  where the book's argument evaluates `f₂`; outside, `ψ` keeps `f₂ ≥ 0`, `|∇f₂|` bounded and `0 ≤
  ψ'' ≤ 2`, so that `f` is `C²` with bounded Hessian as in the book. The growth of `ψ` away from the
  corridor is what makes the line searches exact: with the book's bounded `f₂`, `f₁` keeps
  decreasing along the ray after the corridor is left, and Lemma B.2.6 (whose proof only examines
  the segment `[x_k, x_{k+1}]`) shows only that `(x_{k+1}, y_{k+1})` is the first *local* minimizer
  along the ray.
* **Beyond the last iterate.** The book's data (B.2.5)–(B.2.6) are stated for all `k ≥ 0`, but
  `ε + ω_k` vanishes at `k = 2 k_ε`; here `y_mid` is constant after `x_{k_ε}` and `f₁` levels off
  over `[x_{k_ε}, x_{k_ε} + 1]`.
* The nonnegativity of the slope beyond `(x_{k+1}, y_{k+1})` (`ZigZag.slope_nonneg`) has no
  counterpart in the book; it uses that the middle of the corridor never moves past its value at
  `x_{k+1}` in the direction of the step (`ZigZag.neg_one_pow_mul_mid_sub_le`).
-/

open Set Finset
open scoped RealInnerProductSpace

namespace Optimization

namespace ZigZag

/-! ### The profiles -/

/-- The quintic smooth step `10 t³ - 15 t⁴ + 6 t⁵` of (B.2.13)–(B.2.14). -/
def stepPoly (t : ℝ) : ℝ := 10 * t ^ 3 - 15 * t ^ 4 + 6 * t ^ 5

/-- The derivative `30 t² (1 - t)²` of `stepPoly`. -/
def stepPoly' (t : ℝ) : ℝ := 30 * t ^ 2 - 60 * t ^ 3 + 30 * t ^ 4

/-- The second derivative of `stepPoly`. -/
def stepPoly'' (t : ℝ) : ℝ := 60 * t - 180 * t ^ 2 + 120 * t ^ 3

/-- The quintic `-4 t³ + 7 t⁴ - 3 t⁵` of (B.2.7). -/
def rampPoly (t : ℝ) : ℝ := -4 * t ^ 3 + 7 * t ^ 4 - 3 * t ^ 5

/-- The derivative `-12 t² + 28 t³ - 15 t⁴` of `rampPoly`. -/
def rampPoly' (t : ℝ) : ℝ := -12 * t ^ 2 + 28 * t ^ 3 - 15 * t ^ 4

/-- The second derivative `-24 t + 84 t² - 60 t³` of `rampPoly` (B.2.8). -/
def rampPoly'' (t : ℝ) : ℝ := -24 * t + 84 * t ^ 2 - 60 * t ^ 3

theorem hasDerivAt_stepPoly (t : ℝ) : HasDerivAt stepPoly (stepPoly' t) t := by
  have := (((hasDerivAt_pow 3 t).const_mul 10).sub ((hasDerivAt_pow 4 t).const_mul 15)).add
    ((hasDerivAt_pow 5 t).const_mul 6)
  exact this.congr_deriv (by simp only [stepPoly']; push_cast; ring)

theorem hasDerivAt_stepPoly' (t : ℝ) : HasDerivAt stepPoly' (stepPoly'' t) t := by
  have := (((hasDerivAt_pow 2 t).const_mul 30).sub ((hasDerivAt_pow 3 t).const_mul 60)).add
    ((hasDerivAt_pow 4 t).const_mul 30)
  exact this.congr_deriv (by simp only [stepPoly'']; push_cast; ring)

theorem hasDerivAt_rampPoly (t : ℝ) : HasDerivAt rampPoly (rampPoly' t) t := by
  have := (((hasDerivAt_pow 3 t).const_mul (-4)).add ((hasDerivAt_pow 4 t).const_mul 7)).sub
    ((hasDerivAt_pow 5 t).const_mul 3)
  exact this.congr_deriv (by simp only [rampPoly']; push_cast; ring)

theorem hasDerivAt_rampPoly' (t : ℝ) : HasDerivAt rampPoly' (rampPoly'' t) t := by
  have := (((hasDerivAt_pow 2 t).const_mul (-12)).add ((hasDerivAt_pow 3 t).const_mul 28)).sub
    ((hasDerivAt_pow 4 t).const_mul 15)
  exact this.congr_deriv (by simp only [rampPoly'']; push_cast; ring)

/-- The smooth step `S`: `0` on `(-∞, 0]`, `10 t³ - 15 t⁴ + 6 t⁵` on `[0, 1]`, `1` on `[1, ∞)`;
it is twice continuously differentiable. -/
noncomputable def smoothStep : ℝ → ℝ := Hermite.glue3 (fun _ => 0) stepPoly (fun _ => 1)

/-- The derivative of `smoothStep`. -/
noncomputable def smoothStep' : ℝ → ℝ := Hermite.glue3 (fun _ => 0) stepPoly' (fun _ => 0)

/-- The second derivative of `smoothStep`. -/
noncomputable def smoothStep'' : ℝ → ℝ := Hermite.glue3 (fun _ => 0) stepPoly'' (fun _ => 0)

/-- The ramp `F`: `0` on `(-∞, 0]`, `-4 t³ + 7 t⁴ - 3 t⁵` on `[0, 1]`, `t - 1` on `[1, ∞)`; its
derivative goes from `0` to `1`. -/
noncomputable def ramp : ℝ → ℝ := Hermite.glue3 (fun _ => 0) rampPoly (fun t => t - 1)

/-- The derivative of `ramp`. -/
noncomputable def ramp' : ℝ → ℝ := Hermite.glue3 (fun _ => 0) rampPoly' (fun _ => 1)

/-- The second derivative of `ramp`. -/
noncomputable def ramp'' : ℝ → ℝ := Hermite.glue3 (fun _ => 0) rampPoly'' (fun _ => 0)

theorem hasDerivAt_smoothStep (t : ℝ) : HasDerivAt smoothStep (smoothStep' t) t :=
  Hermite.hasDerivAt_glue3 (fun _ => hasDerivAt_const _ _) hasDerivAt_stepPoly
    (fun _ => hasDerivAt_const _ _) (by simp [stepPoly]) (by simp [stepPoly'])
    (by norm_num [stepPoly]) (by norm_num [stepPoly']) t

theorem hasDerivAt_smoothStep' (t : ℝ) : HasDerivAt smoothStep' (smoothStep'' t) t :=
  Hermite.hasDerivAt_glue3 (fun _ => hasDerivAt_const _ _) hasDerivAt_stepPoly'
    (fun _ => hasDerivAt_const _ _) (by simp [stepPoly']) (by simp [stepPoly''])
    (by norm_num [stepPoly']) (by norm_num [stepPoly'']) t

theorem hasDerivAt_ramp (t : ℝ) : HasDerivAt ramp (ramp' t) t :=
  Hermite.hasDerivAt_glue3 (fun _ => hasDerivAt_const _ _) hasDerivAt_rampPoly
    (fun t => (hasDerivAt_id t).sub_const 1) (by simp [rampPoly]) (by simp [rampPoly'])
    (by norm_num [rampPoly]) (by norm_num [rampPoly']) t

theorem hasDerivAt_ramp' (t : ℝ) : HasDerivAt ramp' (ramp'' t) t :=
  Hermite.hasDerivAt_glue3 (fun _ => hasDerivAt_const _ _) hasDerivAt_rampPoly'
    (fun _ => hasDerivAt_const _ _) (by simp [rampPoly']) (by simp [rampPoly''])
    (by norm_num [rampPoly']) (by norm_num [rampPoly'']) t

theorem smoothStep_of_nonpos {t : ℝ} (ht : t ≤ 0) : smoothStep t = 0 := Hermite.glue3_of_nonpos ht
theorem smoothStep_of_one_le {t : ℝ} (ht : 1 ≤ t) : smoothStep t = 1 :=
  Hermite.glue3_of_one_le (by norm_num [stepPoly]) ht
theorem smoothStep_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : smoothStep t = stepPoly t :=
  Hermite.glue3_of_mem_Icc (by simp [stepPoly]) ht
theorem smoothStep'_of_nonpos {t : ℝ} (ht : t ≤ 0) : smoothStep' t = 0 := Hermite.glue3_of_nonpos ht
theorem smoothStep'_of_one_le {t : ℝ} (ht : 1 ≤ t) : smoothStep' t = 0 :=
  Hermite.glue3_of_one_le (by norm_num [stepPoly']) ht
theorem smoothStep'_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : smoothStep' t = stepPoly' t :=
  Hermite.glue3_of_mem_Icc (by simp [stepPoly']) ht
theorem smoothStep''_of_nonpos {t : ℝ} (ht : t ≤ 0) : smoothStep'' t = 0 :=
  Hermite.glue3_of_nonpos ht
theorem smoothStep''_of_one_le {t : ℝ} (ht : 1 ≤ t) : smoothStep'' t = 0 :=
  Hermite.glue3_of_one_le (by norm_num [stepPoly'']) ht
theorem ramp_of_nonpos {t : ℝ} (ht : t ≤ 0) : ramp t = 0 := Hermite.glue3_of_nonpos ht
theorem ramp'_of_nonpos {t : ℝ} (ht : t ≤ 0) : ramp' t = 0 := Hermite.glue3_of_nonpos ht
theorem ramp'_of_one_le {t : ℝ} (ht : 1 ≤ t) : ramp' t = 1 :=
  Hermite.glue3_of_one_le (by norm_num [rampPoly']) ht
theorem ramp'_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ramp' t = rampPoly' t :=
  Hermite.glue3_of_mem_Icc (by simp [rampPoly']) ht
theorem ramp''_of_nonpos {t : ℝ} (ht : t ≤ 0) : ramp'' t = 0 := Hermite.glue3_of_nonpos ht
theorem ramp''_of_one_le {t : ℝ} (ht : 1 ≤ t) : ramp'' t = 0 :=
  Hermite.glue3_of_one_le (by norm_num [rampPoly'']) ht

/-! #### Polynomial inequalities on `[0, 1]` -/

theorem stepPoly'_nonneg {t : ℝ} : 0 ≤ stepPoly' t := by
  have : stepPoly' t = 30 * (t * (1 - t)) ^ 2 := by simp only [stepPoly']; ring
  rw [this]; positivity

theorem stepPoly'_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : stepPoly' t ≤ 15 / 8 := by
  have : stepPoly' t = 30 * (t * (1 - t)) ^ 2 := by simp only [stepPoly']; ring
  rw [this]
  have h0 : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
  have h1 : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  nlinarith

theorem abs_stepPoly''_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |stepPoly'' t| ≤ 60 := by
  have : stepPoly'' t = 60 * (t * ((1 - t) * (1 - 2 * t))) := by simp only [stepPoly'']; ring
  rw [this, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 60),
    abs_of_nonneg ht.1, abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1 - t)]
  have h2 : |1 - 2 * t| ≤ 1 := abs_le.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h1 : (1 - t) * |1 - 2 * t| ≤ 1 * 1 :=
    mul_le_mul (by linarith [ht.1]) h2 (abs_nonneg _) zero_le_one
  have h0 : t * ((1 - t) * |1 - 2 * t|) ≤ 1 * 1 :=
    mul_le_mul ht.2 (by linarith) (mul_nonneg (by linarith [ht.2]) (abs_nonneg _)) zero_le_one
  linarith

theorem stepPoly_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ stepPoly t := by
  have : stepPoly t = t ^ 3 * (10 - 15 * t + 6 * t ^ 2) := by simp only [stepPoly]; ring
  rw [this]
  exact mul_nonneg (pow_nonneg ht 3) (by nlinarith [sq_nonneg (t - 5 / 4)])

theorem stepPoly_le_two_mul {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : stepPoly t ≤ 2 * t := by
  have : 2 * t - stepPoly t = t * (2 - 10 * t ^ 2 + 15 * t ^ 3 - 6 * t ^ 4) := by
    simp only [stepPoly]; ring
  have h : 0 ≤ 2 - 10 * t ^ 2 + 15 * t ^ 3 - 6 * t ^ 4 := by
    nlinarith [mul_nonneg ht (sub_nonneg.2 ht1), mul_nonneg (mul_nonneg ht ht) (sub_nonneg.2 ht1),
      mul_nonneg (mul_nonneg ht (sub_nonneg.2 ht1)) (sub_nonneg.2 ht1), sq_nonneg (t - 1)]
  nlinarith [mul_nonneg ht h]

theorem rampPoly'_le_one (t : ℝ) : rampPoly' t ≤ 1 := by
  have : 1 - rampPoly' t = (1 - t) ^ 2 * (15 * t ^ 2 + 2 * t + 1) := by
    simp only [rampPoly']; ring
  have : 0 ≤ (1 - t) ^ 2 * (15 * t ^ 2 + 2 * t + 1) :=
    mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg (t + 1 / 15)])
  linarith

theorem neg_one_le_rampPoly' {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : -1 ≤ rampPoly' t := by
  simp only [rampPoly']
  nlinarith [mul_nonneg ht (sub_nonneg.2 ht1), mul_nonneg (mul_nonneg ht ht) (sub_nonneg.2 ht1),
    mul_nonneg (mul_nonneg (mul_nonneg ht ht) ht) (sub_nonneg.2 ht1), sq_nonneg (t - 1 / 2),
    sq_nonneg (t ^ 2 - t / 2)]

theorem abs_rampPoly''_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |rampPoly'' t| ≤ 168 := by
  have h1 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2
  have h2 : t ^ 3 ≤ 1 := pow_le_one₀ ht.1 ht.2
  have h1' : 0 ≤ t ^ 2 := sq_nonneg t
  have h2' : 0 ≤ t ^ 3 := pow_nonneg ht.1 3
  simp only [rampPoly'']
  rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]

/-- `F' - S = -6 t² (1 - t)² (t + 2)` (B.2.36). -/
theorem rampPoly'_sub_stepPoly (t : ℝ) :
    rampPoly' t - stepPoly t = -(6 * (t * (1 - t)) ^ 2 * (t + 2)) := by
  simp only [rampPoly', stepPoly]; ring

/-! ### Nodes of a sequence of steps -/

section Nodes

variable (a : ℕ → ℝ)

/-- The nodes `x_k = ∑_{j<k} a j` of a sequence of steps `a`. -/
def node (k : ℕ) : ℝ := ∑ j ∈ range k, a j

/-- The local variable `(x - x_j) / a_j`, which runs through `[0, 1]` on `[x_j, x_{j+1}]`. -/
noncomputable def localVar (j : ℕ) (x : ℝ) : ℝ := (x - node a j) / a j

@[simp] theorem node_zero : node a 0 = 0 := by simp [node]

theorem node_succ (k : ℕ) : node a (k + 1) = node a k + a k := sum_range_succ _ _

variable {a} {N : ℕ}

theorem hasDerivAt_localVar (j : ℕ) (x : ℝ) : HasDerivAt (localVar a j) (1 / a j) x := by
  have := ((hasDerivAt_id x).sub_const (node a j)).div_const (a j)
  exact this

/-- Chain rule for a profile in the local variable. -/
theorem hasDerivAt_comp_localVar {G G' : ℝ → ℝ} (hG : ∀ t, HasDerivAt G (G' t) t) (j : ℕ)
    (x : ℝ) : HasDerivAt (fun x => G (localVar a j x)) (G' (localVar a j x) / a j) x := by
  have := (hG (localVar a j x)).comp x (hasDerivAt_localVar j x)
  rwa [mul_one_div] at this

variable (ha : ∀ j < N, 0 < a j)
include ha

theorem node_le_node {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : node a i ≤ node a j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    rw [node_succ]
    linarith [ih (by omega), ha j (by omega)]

theorem node_nonneg {j : ℕ} (hj : j ≤ N) : 0 ≤ node a j := by
  simpa using node_le_node ha (Nat.zero_le j) hj

theorem one_le_localVar {j : ℕ} (hj : j < N) {x : ℝ} (hx : node a (j + 1) ≤ x) :
    1 ≤ localVar a j x := by
  rw [localVar, le_div_iff₀ (ha j hj), one_mul]
  rw [node_succ] at hx
  linarith

theorem localVar_nonpos {j : ℕ} (hj : j < N) {x : ℝ} (hx : x ≤ node a j) : localVar a j x ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (by linarith) (ha j hj).le

theorem localVar_mem_Icc {k : ℕ} (hk : k < N) {x : ℝ} (hx : x ∈ Icc (node a k) (node a (k + 1))) :
    localVar a k x ∈ Icc (0 : ℝ) 1 := by
  have hak := ha k hk
  rw [node_succ] at hx
  refine ⟨div_nonneg (by linarith [hx.1]) hak.le, ?_⟩
  rw [localVar, div_le_one hak]
  linarith [hx.2]

/-- **Localization.** On `[x_k, x_{k+1}]`, a sum of profiles that vanish on `(-∞, 0]` and equal
`g₁` on `[1, ∞)` reduces to the saturated terms `j < k` and the active term `j = k`. -/
theorem sum_localVar_eq {G : ℝ → ℝ} {g₁ : ℝ} (hG0 : ∀ t ≤ 0, G t = 0)
    (hG1 : ∀ t, 1 ≤ t → G t = g₁) (c : ℕ → ℝ) {k : ℕ} (hk : k < N) {x : ℝ}
    (hx : x ∈ Icc (node a k) (node a (k + 1))) :
    ∑ j ∈ range N, c j * G (localVar a j x) =
      (∑ j ∈ range k, c j) * g₁ + c k * G (localVar a k x) := by
  rw [← sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hk), sum_range_succ, sum_mul]
  have hhi : ∑ j ∈ Ico (k + 1) N, c j * G (localVar a j x) = 0 := by
    refine sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [hG0 _ (localVar_nonpos ha hj.2 (hx.2.trans (node_le_node ha hj.1 hj.2.le))), mul_zero]
  have hlo : ∑ j ∈ range k, c j * G (localVar a j x) = ∑ j ∈ range k, c j * g₁ := by
    refine sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [hG1 _ (one_le_localVar ha (hj.trans hk)
      ((node_le_node ha (Nat.succ_le_of_lt hj) hk.le).trans hx.1))]
  rw [hhi, hlo, add_zero]

/-- **Localization at a node.** At `x_k` (`k ≤ N`) a sum of profiles that vanish on `(-∞, 0]`
and equal `g₁` on `[1, ∞)` counts the terms `j < k`. -/
theorem sum_localVar_node {G : ℝ → ℝ} {g₁ : ℝ} (hG0 : ∀ t ≤ 0, G t = 0)
    (hG1 : ∀ t, 1 ≤ t → G t = g₁) (c : ℕ → ℝ) {k : ℕ} (hk : k ≤ N) :
    ∑ j ∈ range N, c j * G (localVar a j (node a k)) = (∑ j ∈ range k, c j) * g₁ := by
  rw [← sum_range_add_sum_Ico _ hk, sum_mul]
  have hhi : ∑ j ∈ Ico k N, c j * G (localVar a j (node a k)) = 0 := by
    refine sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [hG0 _ (localVar_nonpos ha hj.2 (node_le_node ha hj.1 hj.2.le)), mul_zero]
  rw [hhi, add_zero]
  refine sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [hG1 _ (one_le_localVar ha (hj.trans_le hk) (node_le_node ha (Nat.succ_le_of_lt hj) hk))]

omit ha in
/-- Every point of `[x_0, x_N)` lies in some `[x_k, x_{k+1})`, `k < N`. -/
theorem exists_mem_Ico_node {x : ℝ} (hx0 : 0 ≤ x) (hxN : x < node a N) :
    ∃ k < N, x ∈ Ico (node a k) (node a (k + 1)) := by
  suffices h : ∀ n ≤ N, x < node a n → ∃ k < n, x ∈ Ico (node a k) (node a (k + 1)) by
    obtain ⟨k, hk, hx⟩ := h N le_rfl hxN
    exact ⟨k, hk, hx⟩
  intro n
  induction n with
  | zero => intro _ h; simp at h; linarith
  | succ n ih =>
    intro hn hx
    by_cases h : x < node a n
    · obtain ⟨k, hk, hk'⟩ := ih (by omega) h
      exact ⟨k, by omega, hk'⟩
    · exact ⟨n, by omega, not_lt.1 h, hx⟩

/-- **Uniform bound** for a sum of profiles supported in `[0, 1]`: at each point at most one term
is active. -/
theorem abs_sum_localVar_le {G : ℝ → ℝ} (hG0 : ∀ t ≤ 0, G t = 0) (hG1 : ∀ t, 1 ≤ t → G t = 0)
    (c : ℕ → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j < N, ∀ t ∈ Icc (0 : ℝ) 1, |c j * G t| ≤ M)
    (x : ℝ) : |∑ j ∈ range N, c j * G (localVar a j x)| ≤ M := by
  rcases lt_or_ge x 0 with hx0 | hx0
  · rw [sum_eq_zero fun j hj => ?_, abs_zero]
    · exact hM0
    rw [Finset.mem_range] at hj
    rw [hG0 _ (localVar_nonpos ha hj (hx0.le.trans (node_nonneg ha hj.le))), mul_zero]
  rcases lt_or_ge x (node a N) with hxN | hxN
  · obtain ⟨k, hk, hx⟩ := exists_mem_Ico_node hx0 hxN
    rw [sum_localVar_eq ha hG0 hG1 c hk (Ico_subset_Icc_self hx), mul_zero, zero_add]
    exact hM k hk _ (localVar_mem_Icc ha hk (Ico_subset_Icc_self hx))
  · rw [sum_eq_zero fun j hj => ?_, abs_zero]
    · exact hM0
    rw [Finset.mem_range] at hj
    rw [hG1 _ (one_le_localVar ha hj ((node_le_node ha (Nat.succ_le_of_lt hj) le_rfl).trans hxN)),
      mul_zero]

end Nodes

/-! ### The data of the example -/

/-- **Admissible tolerance** for the example: `ε > 0` and `k_ε ε² = 1`, i.e. `k_ε = ε⁻²` is a
natural number (so that `ε ≤ 1`). -/
structure IsAdmissible (ε : ℝ) (K : ℕ) : Prop where
  pos : 0 < ε
  mul_sq : (K : ℝ) * ε ^ 2 = 1

/-- `ω_k = ε (k_ε - k) / k_ε` (B.2.4). -/
noncomputable def omega (ε : ℝ) (K k : ℕ) : ℝ := ε * ((K : ℝ) - k) / K

/-- The `k`-th step length `ε + ω_k` (B.2.5). -/
noncomputable def stepLen (ε : ℝ) (K k : ℕ) : ℝ := ε + omega ε K k

/-- `ω_{k_ε} = 0`. -/
@[simp] theorem omega_self (ε : ℝ) (K : ℕ) : omega ε K K = 0 := by
  simp [omega]

@[simp] theorem stepLen_self (ε : ℝ) (K : ℕ) : stepLen ε K K = ε := by
  simp [stepLen, omega]

theorem stepLen_succ (ε : ℝ) (K k : ℕ) : stepLen ε K (k + 1) = stepLen ε K k - ε / K := by
  simp only [stepLen, omega]
  push_cast
  ring

namespace IsAdmissible

variable {ε : ℝ} {K : ℕ} (h : IsAdmissible ε K)
include h

theorem K_pos : (0 : ℝ) < K := by
  rcases (Nat.cast_nonneg K : (0 : ℝ) ≤ K).lt_or_eq with hK | hK
  · exact hK
  · have := h.mul_sq
    rw [← hK, zero_mul] at this
    exact absurd this zero_ne_one

theorem one_le_K : (1 : ℝ) ≤ K := by
  have : 0 < K := by exact_mod_cast h.K_pos
  exact_mod_cast this

/-- An admissible tolerance is at most `1`. -/
theorem le_one : ε ≤ 1 := by
  have h1 := h.one_le_K
  have h2 := h.mul_sq
  have h3 := h.pos
  nlinarith

theorem div_K_eq : ε / K = ε ^ 3 := by
  rw [div_eq_iff h.K_pos.ne']
  linear_combination (-ε) * h.mul_sq

/-- `ε + ω_0 = 2 ε`. -/
theorem stepLen_zero : stepLen ε K 0 = 2 * ε := by
  have := h.K_pos.ne'
  simp only [stepLen, omega, Nat.cast_zero, sub_zero]
  field_simp
  ring

theorem le_stepLen {k : ℕ} (hk : k ≤ K) : ε ≤ stepLen ε K k := by
  have : 0 ≤ omega ε K k :=
    div_nonneg (mul_nonneg h.pos.le (sub_nonneg.2 (by exact_mod_cast hk))) h.K_pos.le
  simp only [stepLen]
  linarith

theorem stepLen_pos {k : ℕ} (hk : k ≤ K) : 0 < stepLen ε K k :=
  h.pos.trans_le (h.le_stepLen hk)

theorem stepLen_le (k : ℕ) : stepLen ε K k ≤ 2 * ε := by
  have : omega ε K k ≤ ε := by
    rw [omega, div_le_iff₀ h.K_pos]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [h.pos]
  simp only [stepLen]
  linarith

/-- `ε + ω_k` is nonincreasing in `k`. -/
theorem stepLen_le_stepLen {j m : ℕ} (hjm : j ≤ m) : stepLen ε K m ≤ stepLen ε K j := by
  have hjm' : (j : ℝ) ≤ m := by exact_mod_cast hjm
  simp only [stepLen, omega]
  have : ε * ((K : ℝ) - m) ≤ ε * ((K : ℝ) - j) :=
    mul_le_mul_of_nonneg_left (by linarith) h.pos.le
  linarith [div_le_div_of_nonneg_right this h.K_pos.le]

/-- If `k_ε ≥ 3`, then `2 ε ≤ 49/32`. -/
theorem two_mul_le_of_three_le (hK : 3 ≤ K) : 2 * ε ≤ 49 / 32 := by
  have hK3' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hε := h.pos
  have he2 : 3 * ε ^ 2 ≤ 1 := by
    nlinarith [h.mul_sq, mul_nonneg (by linarith : (0 : ℝ) ≤ K - 3) (sq_nonneg ε)]
  nlinarith

/-- If `k_ε ≥ 3`, then `4 ε/k_ε ≤ ε + ω_m` for `m < k_ε`. -/
theorem four_mul_div_K_le (hK : 3 ≤ K) {m : ℕ} (hm : m < K) : 4 * (ε / K) ≤ stepLen ε K m := by
  have hK3 : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hm' : (m : ℝ) + 1 ≤ K := by exact_mod_cast hm
  have hKp := h.K_pos
  have h1 : 3 * (ε / K) ≤ ε := by
    rw [← mul_div_assoc, div_le_iff₀ hKp]; nlinarith [h.pos]
  have h2 : ε / K ≤ omega ε K m := by
    rw [omega, div_le_div_iff_of_pos_right hKp]
    nlinarith [h.pos]
  simp only [stepLen]
  linarith

/-- For `k < k_ε`, `ε/k_ε ≤ (ε + ω_k)/2`: the ratio `(ω_k - ω_{k+1})/(ε + ω_k)` is at most `1/2`
(compare (B.2.9)). -/
theorem two_mul_div_K_le {k : ℕ} (hk : k < K) : 2 * (ε / K) ≤ stepLen ε K k := by
  have hK := h.K_pos
  have hk' : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
  have h1 : ε / K ≤ ε := div_le_self h.pos.le h.one_le_K
  have h2 : ε / K ≤ omega ε K k := by
    rw [omega, div_le_div_iff_of_pos_right hK]
    nlinarith [h.pos]
  simp only [stepLen]
  linarith

/-- `(ω_k - ω_{k+1})/(ε + ω_k)² ≤ ε` for `k ≤ k_ε`: this uses `k_ε = ε⁻²`. -/
theorem div_K_div_sq_le {k : ℕ} (hk : k ≤ K) : ε / K / stepLen ε K k ^ 2 ≤ ε := by
  have hε := h.pos
  have ha := h.le_stepLen hk
  rw [h.div_K_eq, div_le_iff₀ (pow_pos (h.stepLen_pos hk) 2)]
  have : ε ^ 2 ≤ stepLen ε K k ^ 2 := pow_le_pow_left₀ hε.le ha 2
  nlinarith

/-- `ω_k > 0` for `k < k_ε`, so that `‖∇f(x_k, y_k)‖ = ε + ω_k > ε` before termination. -/
theorem omega_pos {k : ℕ} (hk : k < K) : 0 < omega ε K k := by
  have : (k : ℝ) < K := by exact_mod_cast hk
  exact div_pos (mul_pos h.pos (by linarith)) h.K_pos

theorem stepLen_pos_of_lt : ∀ j < K, 0 < stepLen ε K j := fun _ hj => h.stepLen_pos hj.le

end IsAdmissible

/-! ### The functions of the construction -/

variable (ε : ℝ) (K : ℕ)

/-- The univariate function `f₁` of (B.2.6)–(B.2.7): it interpolates `f₁'(x_k) = -(ε + ω_k)`,
`f₁''(x_k) = 0` with the quintic pieces (B.2.7) on `[x_k, x_{k+1}]`, `k < k_ε`, is linear on
`(-∞, 0]` and, after `x_{k_ε}`, levels off to a constant on `[x_{k_ε} + 1, ∞)`. -/
noncomputable def f₁ (x : ℝ) : ℝ :=
  4 - stepLen ε K 0 * x +
    ∑ j ∈ range K, ε / K * stepLen ε K j * ramp (localVar (stepLen ε K) j x) +
    ε * ramp (x - node (stepLen ε K) K)

/-- The derivative of `f₁`. -/
noncomputable def f₁' (x : ℝ) : ℝ :=
  -stepLen ε K 0 + ∑ j ∈ range K, ε / K * ramp' (localVar (stepLen ε K) j x) +
    ε * ramp' (x - node (stepLen ε K) K)

/-- The second derivative of `f₁`. -/
noncomputable def f₁'' (x : ℝ) : ℝ :=
  ∑ j ∈ range K, ε / K / stepLen ε K j * ramp'' (localVar (stepLen ε K) j x) +
    ε * ramp'' (x - node (stepLen ε K) K)

/-- The middle `y_mid = (y_low + y_up)/2` of the corridor (B.2.13)–(B.2.15): it moves by
`(-1)^k (ω_k - ω_{k+1})/2` along the smooth step on `[x_k, x_{k+1}]` and is constant elsewhere. -/
noncomputable def mid (x : ℝ) : ℝ :=
  stepLen ε K 0 / 2 +
    ∑ j ∈ range K, ε / (2 * K) * (-1) ^ j * smoothStep (localVar (stepLen ε K) j x)

/-- The derivative of `mid`. -/
noncomputable def mid' (x : ℝ) : ℝ :=
  ∑ j ∈ range K, ε / (2 * K) * (-1) ^ j / stepLen ε K j *
    smoothStep' (localVar (stepLen ε K) j x)

/-- The second derivative of `mid`. -/
noncomputable def mid'' (x : ℝ) : ℝ :=
  ∑ j ∈ range K, ε / (2 * K) * (-1) ^ j / stepLen ε K j ^ 2 *
    smoothStep'' (localVar (stepLen ε K) j x)

variable {ε K}

theorem hasDerivAt_f₁ (h : IsAdmissible ε K) (x : ℝ) : HasDerivAt (f₁ ε K) (f₁' ε K x) x := by
  have h1 : HasDerivAt (fun x => 4 - stepLen ε K 0 * x) (-stepLen ε K 0) x := by
    simpa using ((hasDerivAt_id x).const_mul (stepLen ε K 0)).const_sub 4
  have h2 : HasDerivAt
      (fun x => ∑ j ∈ range K, ε / K * stepLen ε K j * ramp (localVar (stepLen ε K) j x))
      (∑ j ∈ range K, ε / K * ramp' (localVar (stepLen ε K) j x)) x := by
    refine HasDerivAt.fun_sum fun j hj => ?_
    have hj' := (h.stepLen_pos (Finset.mem_range.1 hj).le).ne'
    exact ((hasDerivAt_comp_localVar hasDerivAt_ramp j x).const_mul
      (ε / K * stepLen ε K j)).congr_deriv (by field_simp)
  have h3 : HasDerivAt (fun x => ε * ramp (x - node (stepLen ε K) K))
      (ε * ramp' (x - node (stepLen ε K) K)) x := by
    have := (hasDerivAt_ramp (x - node (stepLen ε K) K)).comp x ((hasDerivAt_id x).sub_const _)
    simpa using this.const_mul ε
  exact (h1.add h2).add h3

theorem hasDerivAt_f₁' (x : ℝ) : HasDerivAt (f₁' ε K) (f₁'' ε K x) x := by
  have h2 : HasDerivAt
      (fun x => ∑ j ∈ range K, ε / K * ramp' (localVar (stepLen ε K) j x))
      (∑ j ∈ range K, ε / K / stepLen ε K j * ramp'' (localVar (stepLen ε K) j x)) x := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact ((hasDerivAt_comp_localVar hasDerivAt_ramp' j x).const_mul (ε / K)).congr_deriv
      (by ring)
  have h3 : HasDerivAt (fun x => ε * ramp' (x - node (stepLen ε K) K))
      (ε * ramp'' (x - node (stepLen ε K) K)) x := by
    have := (hasDerivAt_ramp' (x - node (stepLen ε K) K)).comp x ((hasDerivAt_id x).sub_const _)
    simpa using this.const_mul ε
  have := ((hasDerivAt_const x (-stepLen ε K 0)).add h2).add h3
  rw [zero_add] at this
  exact this

theorem hasDerivAt_mid (x : ℝ) : HasDerivAt (mid ε K) (mid' ε K x) x := by
  have h2 : HasDerivAt
      (fun x => ∑ j ∈ range K, ε / (2 * K) * (-1) ^ j * smoothStep (localVar (stepLen ε K) j x))
      (mid' ε K x) x := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact ((hasDerivAt_comp_localVar hasDerivAt_smoothStep j x).const_mul
      (ε / (2 * K) * (-1) ^ j)).congr_deriv (by ring)
  have := (hasDerivAt_const x (stepLen ε K 0 / 2)).add h2
  rw [zero_add] at this
  exact this

theorem hasDerivAt_mid' (x : ℝ) : HasDerivAt (mid' ε K) (mid'' ε K x) x := by
  refine HasDerivAt.fun_sum fun j _ => ?_
  exact ((hasDerivAt_comp_localVar hasDerivAt_smoothStep' j x).const_mul
    (ε / (2 * K) * (-1) ^ j / stepLen ε K j)).congr_deriv (by ring)

/-! ### Uniform bounds on the derivatives -/

/-- `|f₁''| ≤ 252`, uniformly in `ε` (compare (B.2.10)). -/
theorem abs_f₁''_le (h : IsAdmissible ε K) (x : ℝ) : |f₁'' ε K x| ≤ 252 := by
  have hs := abs_sum_localVar_le h.stepLen_pos_of_lt (G := ramp'')
    (fun t ht => ramp''_of_nonpos ht)
    (fun t ht => ramp''_of_one_le ht) (fun j => ε / K / stepLen ε K j) (M := 84) (by norm_num)
    (fun j hj t ht => by
      rw [ramp'', Hermite.glue3_of_mem_Icc (by simp [rampPoly'']) ht, abs_mul,
        abs_of_nonneg (div_nonneg (div_nonneg h.pos.le h.K_pos.le) (h.stepLen_pos hj.le).le)]
      have h1 : ε / K / stepLen ε K j ≤ 1 / 2 := by
        rw [div_le_iff₀ (h.stepLen_pos hj.le)]
        linarith [h.two_mul_div_K_le hj]
      have h2 := abs_rampPoly''_le ht
      nlinarith [abs_nonneg (rampPoly'' t), div_nonneg (div_nonneg h.pos.le h.K_pos.le)
        (h.stepLen_pos hj.le).le]) x
  have hr : |ε * ramp'' (x - node (stepLen ε K) K)| ≤ 168 := by
    rw [abs_mul, abs_of_pos h.pos]
    have : |ramp'' (x - node (stepLen ε K) K)| ≤ 168 :=
      Hermite.abs_glue3_le (fun _ _ => by norm_num) (fun t ht => abs_rampPoly''_le ht)
        (fun _ _ => by norm_num) _
    nlinarith [h.le_one, h.pos, abs_nonneg (ramp'' (x - node (stepLen ε K) K))]
  rw [f₁'']
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 84 + 168 := add_le_add hs hr
    _ = 252 := by norm_num

/-- `|y_mid'| ≤ 1`, uniformly in `ε` (compare (B.2.26), (B.2.34)). -/
theorem abs_mid'_le (h : IsAdmissible ε K) (x : ℝ) : |mid' ε K x| ≤ 1 := by
  refine abs_sum_localVar_le h.stepLen_pos_of_lt (G := smoothStep')
    (fun t ht => smoothStep'_of_nonpos ht) (fun t ht => smoothStep'_of_one_le ht)
    (fun j => ε / (2 * K) * (-1) ^ j / stepLen ε K j) zero_le_one (fun j hj t ht => ?_) x
  have ha := h.stepLen_pos hj.le
  rw [smoothStep'_of_mem_Icc ht, abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    mul_one, abs_of_pos ha, abs_of_nonneg stepPoly'_nonneg,
    abs_of_nonneg (div_nonneg h.pos.le (by positivity))]
  have h1 : ε / (2 * K) / stepLen ε K j ≤ 1 / 4 := by
    rw [div_le_iff₀ ha]
    have := h.two_mul_div_K_le hj
    have e : ε / (2 * K) = ε / K / 2 := by ring
    rw [e]
    linarith
  have h2 := stepPoly'_le ht
  have h0 : 0 ≤ ε / (2 * K) / stepLen ε K j :=
    div_nonneg (div_nonneg h.pos.le (by positivity)) ha.le
  nlinarith [stepPoly'_nonneg (t := t)]

/-- `|y_mid''| ≤ 30`, uniformly in `ε` (compare (B.2.26)). -/
theorem abs_mid''_le (h : IsAdmissible ε K) (x : ℝ) : |mid'' ε K x| ≤ 30 := by
  refine abs_sum_localVar_le h.stepLen_pos_of_lt (G := smoothStep'')
    (fun t ht => smoothStep''_of_nonpos ht) (fun t ht => smoothStep''_of_one_le ht)
    (fun j => ε / (2 * K) * (-1) ^ j / stepLen ε K j ^ 2) (by norm_num) (fun j hj t ht => ?_) x
  have ha := h.stepLen_pos hj.le
  rw [smoothStep'', Hermite.glue3_of_mem_Icc (by simp [stepPoly'']) ht, abs_mul, abs_div, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_pow, abs_of_pos ha,
    abs_of_nonneg (div_nonneg h.pos.le (by positivity))]
  have h1 : ε / (2 * K) / stepLen ε K j ^ 2 ≤ 1 / 2 := by
    have := h.div_K_div_sq_le hj.le
    have e : ε / (2 * K) / stepLen ε K j ^ 2 = ε / K / stepLen ε K j ^ 2 / 2 := by ring
    rw [e]
    linarith [h.le_one]
  have h2 := abs_stepPoly''_le ht
  have h0 : 0 ≤ ε / (2 * K) / stepLen ε K j ^ 2 :=
    div_nonneg (div_nonneg h.pos.le (by positivity)) (by positivity)
  nlinarith [abs_nonneg (stepPoly'' t)]

/-! ### The capped square -/

/-- The antiderivative `5t⁴/2 - 3t⁵ + t⁶` of `stepPoly`. -/
noncomputable def stepIntPoly (t : ℝ) : ℝ := 5 / 2 * t ^ 4 - 3 * t ^ 5 + t ^ 6

/-- The antiderivative `t⁵/2 - t⁶/2 + t⁷/7` of `stepIntPoly`. -/
noncomputable def stepInt2Poly (t : ℝ) : ℝ := t ^ 5 / 2 - t ^ 6 / 2 + t ^ 7 / 7

theorem hasDerivAt_stepIntPoly (t : ℝ) : HasDerivAt stepIntPoly (stepPoly t) t := by
  have := (((hasDerivAt_pow 4 t).const_mul (5 / 2)).sub ((hasDerivAt_pow 5 t).const_mul 3)).add
    (hasDerivAt_pow 6 t)
  exact this.congr_deriv (by simp only [stepPoly]; push_cast; ring)

theorem hasDerivAt_stepInt2Poly (t : ℝ) : HasDerivAt stepInt2Poly (stepIntPoly t) t := by
  have := (((hasDerivAt_pow 5 t).div_const 2).sub ((hasDerivAt_pow 6 t).div_const 2)).add
    ((hasDerivAt_pow 7 t).div_const 7)
  exact this.congr_deriv (by simp only [stepIntPoly]; push_cast; ring)

/-- The antiderivative of `smoothStep` vanishing on `(-∞, 0]`. -/
noncomputable def stepInt : ℝ → ℝ := Hermite.glue3 (fun _ => 0) stepIntPoly (fun t => t - 1 / 2)

/-- The antiderivative of `stepInt` vanishing on `(-∞, 0]`. -/
noncomputable def stepInt2 : ℝ → ℝ :=
  Hermite.glue3 (fun _ => 0) stepInt2Poly (fun t => t ^ 2 / 2 - t / 2 + 1 / 7)

theorem hasDerivAt_stepInt (t : ℝ) : HasDerivAt stepInt (smoothStep t) t :=
  Hermite.hasDerivAt_glue3 (fun _ => hasDerivAt_const _ _) hasDerivAt_stepIntPoly
    (fun t => (hasDerivAt_id t).sub_const _) (by simp [stepIntPoly]) (by simp [stepPoly])
    (by norm_num [stepIntPoly]) (by norm_num [stepPoly]) t

theorem hasDerivAt_stepInt2 (t : ℝ) : HasDerivAt stepInt2 (stepInt t) t :=
  Hermite.hasDerivAt_glue3 (fun _ => hasDerivAt_const _ _) hasDerivAt_stepInt2Poly
    (fun t => by
      have := (((hasDerivAt_pow 2 t).div_const 2).sub ((hasDerivAt_id t).div_const 2)).add_const
        (1 / 7 : ℝ)
      exact this.congr_deriv (by simp))
    (by simp [stepInt2Poly]) (by simp [stepIntPoly]) (by norm_num [stepInt2Poly])
    (by norm_num [stepIntPoly]) t

theorem stepInt_of_nonpos {t : ℝ} (ht : t ≤ 0) : stepInt t = 0 := Hermite.glue3_of_nonpos ht
theorem stepInt2_of_nonpos {t : ℝ} (ht : t ≤ 0) : stepInt2 t = 0 := Hermite.glue3_of_nonpos ht
theorem stepInt_of_one_le {t : ℝ} (ht : 1 ≤ t) : stepInt t = t - 1 / 2 :=
  Hermite.glue3_of_one_le (by norm_num [stepIntPoly]) ht

theorem stepPoly_le_one {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : stepPoly t ≤ 1 := by
  have : 1 - stepPoly t = (1 - t) ^ 3 * (6 * t ^ 2 + 3 * t + 1) := by simp only [stepPoly]; ring
  have : 0 ≤ (1 - t) ^ 3 * (6 * t ^ 2 + 3 * t + 1) :=
    mul_nonneg (pow_nonneg (by linarith) 3) (by positivity)
  linarith

theorem smoothStep_mem_Icc (t : ℝ) : smoothStep t ∈ Icc (0 : ℝ) 1 := by
  rcases le_or_gt t 0 with h | h
  · rw [smoothStep_of_nonpos h]; norm_num
  rcases le_or_gt t 1 with h' | h'
  · rw [smoothStep_of_mem_Icc ⟨h.le, h'⟩]
    exact ⟨stepPoly_nonneg h.le, stepPoly_le_one h.le h'⟩
  · rw [smoothStep_of_one_le h'.le]; norm_num

theorem stepInt2_nonneg (t : ℝ) : 0 ≤ stepInt2 t := by
  rcases le_or_gt t 0 with h | h
  · rw [stepInt2_of_nonpos h]
  rcases le_or_gt t 1 with h' | h'
  · rw [stepInt2, Hermite.glue3_of_mem_Icc (by simp [stepInt2Poly]) ⟨h.le, h'⟩]
    have : stepInt2Poly t = t ^ 5 * ((1 - t) / 2 + t ^ 2 / 7) := by simp only [stepInt2Poly]; ring
    rw [this]
    exact mul_nonneg (by positivity) (by nlinarith)
  · rw [stepInt2, Hermite.glue3_of_one_le (by norm_num [stepInt2Poly]) h'.le]
    nlinarith

theorem stepInt2_le {t : ℝ} (ht : 0 ≤ t) : stepInt2 t ≤ t ^ 2 / 2 := by
  rcases le_or_gt t 1 with h' | h'
  · rw [stepInt2, Hermite.glue3_of_mem_Icc (by simp [stepInt2Poly]) ⟨ht, h'⟩]
    have e : t ^ 2 / 2 - stepInt2Poly t =
        t ^ 2 * (1 / 2 - t ^ 3 * (1 - t) / 2 - t ^ 5 / 7) := by simp only [stepInt2Poly]; ring
    have h3 : t ^ 3 ≤ 1 := pow_le_one₀ ht h'
    have h5 : t ^ 5 ≤ 1 := pow_le_one₀ ht h'
    have h3' : 0 ≤ t ^ 3 := by positivity
    have : 0 ≤ 1 / 2 - t ^ 3 * (1 - t) / 2 - t ^ 5 / 7 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg t) this]
  · rw [stepInt2, Hermite.glue3_of_one_le (by norm_num [stepInt2Poly]) h'.le]
    linarith

/-- The **capped square** `ψ`: `ψ(u) = u²` for `|u| ≤ 1`, with second derivative
`2 (1 - S(|u| - 1))` (`S` the smooth step) for `1 ≤ |u| ≤ 2`, and linear (slope `±3`) for
`|u| ≥ 2`. It is twice continuously differentiable with `0 ≤ ψ'' ≤ 2` and `|ψ'| ≤ 3`. It plays the
role of the corridor function of (B.2.19) as a function of the distance `y - y_mid(x)` to the
middle of the corridor. -/
noncomputable def capSq (u : ℝ) : ℝ := u ^ 2 - 2 * stepInt2 (u - 1) - 2 * stepInt2 (-u - 1)

/-- The derivative of `capSq`. -/
noncomputable def capSq' (u : ℝ) : ℝ := 2 * u - 2 * stepInt (u - 1) + 2 * stepInt (-u - 1)

/-- The second derivative of `capSq`. -/
noncomputable def capSq'' (u : ℝ) : ℝ := 2 - 2 * smoothStep (u - 1) - 2 * smoothStep (-u - 1)

theorem hasDerivAt_capSq (u : ℝ) : HasDerivAt capSq (capSq' u) u := by
  have h1 := (hasDerivAt_stepInt2 (u - 1)).comp u ((hasDerivAt_id u).sub_const 1)
  have h2 := (hasDerivAt_stepInt2 (-u - 1)).comp u ((hasDerivAt_id u).neg.sub_const 1)
  have := ((hasDerivAt_pow 2 u).sub (h1.const_mul 2)).sub (h2.const_mul 2)
  exact this.congr_deriv (by simp only [capSq']; push_cast; ring)

theorem hasDerivAt_capSq' (u : ℝ) : HasDerivAt capSq' (capSq'' u) u := by
  have h1 := (hasDerivAt_stepInt (u - 1)).comp u ((hasDerivAt_id u).sub_const 1)
  have h2 := (hasDerivAt_stepInt (-u - 1)).comp u ((hasDerivAt_id u).neg.sub_const 1)
  have := ((((hasDerivAt_id u).const_mul 2).sub (h1.const_mul 2)).add (h2.const_mul 2))
  exact this.congr_deriv (by simp only [capSq'']; ring)

/-- The capped square is the square on `[-1, 1]`. -/
theorem capSq_of_abs_le {u : ℝ} (hu : |u| ≤ 1) : capSq u = u ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.1 hu
  rw [capSq, stepInt2_of_nonpos (by linarith), stepInt2_of_nonpos (by linarith)]; ring

/-- The derivative of the capped square is `2u` on `[-1, 1]`. -/
theorem capSq'_of_abs_le {u : ℝ} (hu : |u| ≤ 1) : capSq' u = 2 * u := by
  obtain ⟨h1, h2⟩ := abs_le.1 hu
  rw [capSq', stepInt_of_nonpos (by linarith), stepInt_of_nonpos (by linarith)]; ring

theorem capSq_neg (u : ℝ) : capSq (-u) = capSq u := by
  simp only [capSq, neg_neg]; ring

theorem capSq'_neg (u : ℝ) : capSq' (-u) = -capSq' u := by
  simp only [capSq', neg_neg]; ring

theorem capSq''_nonneg (u : ℝ) : 0 ≤ capSq'' u := by
  rw [capSq'']
  have h1 := smoothStep_mem_Icc (u - 1)
  have h2 := smoothStep_mem_Icc (-u - 1)
  rcases le_total u 0 with hu | hu
  · rw [smoothStep_of_nonpos (by linarith : u - 1 ≤ 0)]; linarith [h2.2]
  · rw [smoothStep_of_nonpos (by linarith : -u - 1 ≤ 0)]; linarith [h1.2]

theorem capSq''_le_two (u : ℝ) : capSq'' u ≤ 2 := by
  rw [capSq'']
  linarith [(smoothStep_mem_Icc (u - 1)).1, (smoothStep_mem_Icc (-u - 1)).1]

theorem abs_capSq''_le (u : ℝ) : |capSq'' u| ≤ 2 :=
  abs_le.2 ⟨by linarith [capSq''_nonneg u], capSq''_le_two u⟩

theorem monotone_capSq' : Monotone capSq' :=
  monotone_of_deriv_nonneg (fun u => (hasDerivAt_capSq' u).differentiableAt)
    fun u => (hasDerivAt_capSq' u).deriv ▸ capSq''_nonneg u

/-- The derivative of the capped square is `2`-Lipschitz. -/
theorem abs_capSq'_sub_le (u v : ℝ) : |capSq' u - capSq' v| ≤ 2 * |u - v| :=
  abs_sub_le_of_hasDerivAt hasDerivAt_capSq' abs_capSq''_le u v

theorem capSq'_le_three (u : ℝ) : capSq' u ≤ 3 := by
  have h2 : capSq' 2 = 3 := by
    rw [capSq', stepInt_of_one_le (by norm_num), stepInt_of_nonpos (by norm_num)]; norm_num
  rcases le_total u 2 with hu | hu
  · exact h2 ▸ monotone_capSq' hu
  · rw [capSq', stepInt_of_one_le (by linarith), stepInt_of_nonpos (by linarith)]; linarith

theorem abs_capSq'_le (u : ℝ) : |capSq' u| ≤ 3 := by
  refine abs_le.2 ⟨?_, capSq'_le_three u⟩
  have := capSq'_le_three (-u)
  rw [capSq'_neg] at this
  linarith

/-- Lower bound for the derivative of the capped square: `2 min(v, 1) ≤ ψ'(w)` for `0 ≤ v ≤ w`. -/
theorem le_capSq' {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) : 2 * min v 1 ≤ capSq' w := by
  have hm : |min w 1| ≤ 1 :=
    abs_le.2 ⟨by linarith [le_min (hv.trans hvw) zero_le_one], min_le_right _ _⟩
  have := monotone_capSq' (min_le_left w 1)
  rw [capSq'_of_abs_le hm] at this
  have : min v 1 ≤ min w 1 := min_le_min_right 1 hvw
  linarith

theorem capSq_nonneg (u : ℝ) : 0 ≤ capSq u := by
  wlog hu : 0 ≤ u generalizing u
  · rw [← capSq_neg]; exact this (-u) (by linarith)
  rw [capSq, stepInt2_of_nonpos (by linarith : -u - 1 ≤ 0)]
  rcases le_total u 1 with h1 | h1
  · rw [stepInt2_of_nonpos (by linarith)]; nlinarith
  · nlinarith [stepInt2_le (by linarith : 0 ≤ u - 1)]

theorem capSq_le_sq (u : ℝ) : capSq u ≤ u ^ 2 := by
  rw [capSq]; linarith [stepInt2_nonneg (u - 1), stepInt2_nonneg (-u - 1)]

/-! ### The iterates -/

/-- The `y`-coordinates `y_k = ∑_{j<k} (-1)^j (ε + ω_j)` of the iterates. -/
noncomputable def height (ε : ℝ) (K k : ℕ) : ℝ := ∑ j ∈ range k, (-1) ^ j * stepLen ε K j

theorem height_succ (ε : ℝ) (K k : ℕ) :
    height ε K (k + 1) = height ε K k + (-1) ^ k * stepLen ε K k := sum_range_succ _ _

/-- The middle of the corridor at the nodes: `y_mid(x_k) = (ε + ω_0)/2 + (ε/(2k_ε)) ∑_{j<k} (-1)^j`
for `k ≤ k_ε`. -/
theorem mid_node (h : IsAdmissible ε K) {k : ℕ} (hk : k ≤ K) :
    mid ε K (node (stepLen ε K) k) =
      stepLen ε K 0 / 2 + ∑ j ∈ range k, ε / (2 * K) * (-1) ^ j := by
  rw [mid, sum_localVar_node h.stepLen_pos_of_lt (G := smoothStep) (g₁ := 1)
    (fun t ht => smoothStep_of_nonpos ht) (fun t ht => smoothStep_of_one_le ht) _ hk, mul_one]

/-- The iterates lie at distance `(ε + ω_k)/2` from the middle of the corridor, on alternating
sides: `y_k - y_mid(x_k) = -(-1)^k (ε + ω_k)/2`. -/
theorem height_sub_mid_node (h : IsAdmissible ε K) {k : ℕ} (hk : k ≤ K) :
    height ε K k - mid ε K (node (stepLen ε K) k) = -((-1) ^ k * stepLen ε K k / 2) := by
  induction k with
  | zero =>
    have := mid_node h (Nat.zero_le K)
    simp only [node_zero, range_zero, sum_empty, add_zero] at this
    simp [height, this]
  | succ k ih =>
    have ih := ih (by omega)
    rw [mid_node h hk, sum_range_succ, height_succ, stepLen_succ]
    rw [mid_node h (by omega)] at ih
    have e : ε / (2 * K) = ε / K / 2 := by ring
    rw [e] at ih ⊢
    rw [pow_succ]
    linarith

/-- `y_mid'(x_k) = 0` for `k ≤ k_ε` (used in (B.2.23)). -/
theorem mid'_node (h : IsAdmissible ε K) {k : ℕ} (hk : k ≤ K) :
    mid' ε K (node (stepLen ε K) k) = 0 := by
  rw [mid', sum_localVar_node h.stepLen_pos_of_lt (G := smoothStep') (g₁ := 0)
    (fun t ht => smoothStep'_of_nonpos ht) (fun t ht => smoothStep'_of_one_le ht) _ hk, mul_zero]

/-- `f₁'(x_k) = -(ε + ω_k)` for `k ≤ k_ε` (B.2.6). -/
theorem f₁'_node (h : IsAdmissible ε K) {k : ℕ} (hk : k ≤ K) :
    f₁' ε K (node (stepLen ε K) k) = -stepLen ε K k := by
  rw [f₁', sum_localVar_node h.stepLen_pos_of_lt (G := ramp') (g₁ := 1)
    (fun t ht => ramp'_of_nonpos ht) (fun t ht => ramp'_of_one_le ht) _ hk, mul_one,
    ramp'_of_nonpos (sub_nonpos.2 (node_le_node h.stepLen_pos_of_lt hk le_rfl)), mul_zero,
    add_zero, sum_const, card_range, nsmul_eq_mul]
  simp only [stepLen, omega]
  have := h.K_pos.ne'
  field_simp
  ring

end ZigZag

open ZigZag

/-- **The zig-zag function** of [cartis2022evaluation] (B.2.24), with `K = k_ε`:
`f(x, y) = (f₁(x) + f₂(x, y))/√2`, where `f₁ = ZigZag.f₁ ε K` interpolates the slopes
`-(ε + ω_k)` at the nodes `x_k` (B.2.6) (linearly continued for `x < 0`, levelling off after
`x_{k_ε}`) and `f₂(x, y) = capSq (y - y_mid(x))` is a capped square of the distance to the middle
`y_mid = ZigZag.mid ε K` of the corridor (B.2.13)–(B.2.15). -/
noncomputable def zigZagFunction (ε : ℝ) (K : ℕ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (f₁ ε K (z 0) + capSq (z 1 - mid ε K (z 0))) / √2

/-- **The iterates** `(x_k, y_k)` of the zig-zag example: `(x_0, y_0) = 0` and
`(x_{k+1}, y_{k+1}) = (x_k, y_k) + (ε + ω_k) (1, (-1)^k)`. -/
noncomputable def zigZagIterate (ε : ℝ) (K k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[node (stepLen ε K) k, height ε K k]

namespace ZigZag

variable {ε : ℝ} {K : ℕ}

/-- The gradient of the zig-zag function. -/
noncomputable def grad (ε : ℝ) (K : ℕ) (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  (√2)⁻¹ • !₂[f₁' ε K (z 0) - capSq' (z 1 - mid ε K (z 0)) * mid' ε K (z 0),
    capSq' (z 1 - mid ε K (z 0))]

/-- The corridor function `f₂(x, y) = ψ(y - y_mid(x))` (compare (B.2.19)), with `ψ = capSq`:
`zigZagFunction ε K z = (f₁(z₀) + f₂(z))/√2`. -/
noncomputable def f₂ (ε : ℝ) (K : ℕ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  capSq (z 1 - mid ε K (z 0))

/-- The gradient `(-ψ'(u) y_mid'(x), ψ'(u))` of the corridor function, `u = y - y_mid(x)`. -/
noncomputable def grad₂ (ε : ℝ) (K : ℕ) (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  !₂[-(capSq' (z 1 - mid ε K (z 0)) * mid' ε K (z 0)), capSq' (z 1 - mid ε K (z 0))]

theorem zigZagFunction_eq (z : EuclideanSpace ℝ (Fin 2)) :
    zigZagFunction ε K z = (f₁ ε K (z 0) + f₂ ε K z) / √2 := rfl

theorem grad_eq (z : EuclideanSpace ℝ (Fin 2)) :
    grad ε K z = (√2)⁻¹ • (!₂[f₁' ε K (z 0), 0] + grad₂ ε K z) := by
  ext i
  fin_cases i <;> simp [grad, grad₂]; ring

/-- The gradient of the corridor function. -/
theorem hasGradientAt_f₂ (z : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt (f₂ ε K) (grad₂ ε K z) z := by
  set p0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0
  set p1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1
  have hp0 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 0) p0 z := p0.hasFDerivAt
  have hp1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 1) p1 z := p1.hasFDerivAt
  have hm := (hasDerivAt_mid (ε := ε) (K := K) (z 0)).comp_hasFDerivAt z hp0
  have hh : HasFDerivAt (f₂ ε K) _ z :=
    (hasDerivAt_capSq (z 1 - mid ε K (z 0))).comp_hasFDerivAt z (hp1.sub hm)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hh.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [grad₂, p0, p1, PiLp.inner_apply, Fin.sum_univ_two, InnerProductSpace.toDual_apply_apply]
  ring

/-- The gradient of the zig-zag function is `ZigZag.grad`: `∇f(x, y) = (f₁'(x) - ψ'(u) y_mid'(x),
ψ'(u))/√2` with `u = y - y_mid(x)` and `ψ = capSq`. -/
theorem hasGradientAt_zigZagFunction (h : IsAdmissible ε K) (z : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt (zigZagFunction ε K) (grad ε K z) z := by
  set p0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0
  set p1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1
  have hp0 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 0) p0 z := p0.hasFDerivAt
  have hp1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => z 1) p1 z := p1.hasFDerivAt
  have hf1 := (hasDerivAt_f₁ h (z 0)).comp_hasFDerivAt z hp0
  have hm := (hasDerivAt_mid (ε := ε) (K := K) (z 0)).comp_hasFDerivAt z hp0
  have hh := (hasDerivAt_capSq (z 1 - mid ε K (z 0))).comp_hasFDerivAt z (hp1.sub hm)
  have hs : HasFDerivAt (zigZagFunction ε K) _ z :=
    ((hf1.add hh).const_mul (√2)⁻¹).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by
        simp only [zigZagFunction, Function.comp, Pi.add_apply, Pi.sub_apply]
        rw [div_eq_inv_mul])
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hs.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [grad, p0, p1, PiLp.inner_apply, Fin.sum_univ_two, InnerProductSpace.toDual_apply_apply]
  ring

/-- The gradient of the zig-zag function, as a function. -/
theorem gradient_zigZagFunction (h : IsAdmissible ε K) (z : EuclideanSpace ℝ (Fin 2)) :
    gradient (zigZagFunction ε K) z = grad ε K z :=
  (hasGradientAt_zigZagFunction h z).gradient

theorem differentiable_zigZagFunction (h : IsAdmissible ε K) :
    Differentiable ℝ (zigZagFunction ε K) :=
  fun z => (hasGradientAt_zigZagFunction h z).differentiableAt

/-! #### Lipschitz continuity of the gradient -/

theorem abs_mid_sub_le (h : IsAdmissible ε K) (x x' : ℝ) :
    |mid ε K x - mid ε K x'| ≤ |x - x'| := by
  simpa using abs_sub_le_of_hasDerivAt hasDerivAt_mid (abs_mid'_le h) x x'

/-- The gradient of the corridor function is `98`-Lipschitz, uniformly in `ε`. -/
theorem norm_grad₂_sub_le (h : IsAdmissible ε K) (z z' : EuclideanSpace ℝ (Fin 2)) :
    ‖grad₂ ε K z - grad₂ ε K z'‖ ≤ 98 * ‖z - z'‖ := by
  set x := z 0
  set x' := z' 0
  set u := z 1 - mid ε K x
  set u' := z' 1 - mid ε K x'
  have hx : |x - x'| ≤ ‖z - z'‖ := EuclideanSpace.abs_apply_sub_le z z' 0
  have hy : |z 1 - z' 1| ≤ ‖z - z'‖ := EuclideanSpace.abs_apply_sub_le z z' 1
  have hu : |u - u'| ≤ 2 * ‖z - z'‖ := by
    have e : u - u' = (z 1 - z' 1) - (mid ε K x - mid ε K x') := by simp only [u, u']; ring
    rw [e]
    have := abs_mid_sub_le h x x'
    have := abs_sub (z 1 - z' 1) (mid ε K x - mid ε K x')
    linarith
  have hd₂ : |capSq' u - capSq' u'| ≤ 4 * ‖z - z'‖ := by
    have := abs_capSq'_sub_le u u'
    linarith
  have hm : |mid' ε K x - mid' ε K x'| ≤ 30 * ‖z - z'‖ :=
    (abs_sub_le_of_hasDerivAt hasDerivAt_mid' (abs_mid''_le h) x x').trans
      (mul_le_mul_of_nonneg_left hx (by norm_num))
  have hd₁ : |-(capSq' u * mid' ε K x) - -(capSq' u' * mid' ε K x')| ≤ 94 * ‖z - z'‖ := by
    have e : -(capSq' u * mid' ε K x) - -(capSq' u' * mid' ε K x') =
        -(capSq' u * (mid' ε K x - mid' ε K x') + mid' ε K x' * (capSq' u - capSq' u')) := by
      ring
    rw [e, abs_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 := mul_le_mul (abs_capSq'_le u) hm (abs_nonneg _) (by norm_num)
    have h2 := mul_le_mul (abs_mid'_le h x') hd₂ (abs_nonneg _) zero_le_one
    linarith
  have e : grad₂ ε K z - grad₂ ε K z' =
      !₂[-(capSq' u * mid' ε K x) - -(capSq' u' * mid' ε K x'), capSq' u - capSq' u'] := by
    ext i
    fin_cases i <;> simp [grad₂, x, x', u, u']
  rw [e]
  calc _ ≤ _ := EuclideanSpace.norm_toLp_two_le _ _
    _ ≤ 94 * ‖z - z'‖ + 4 * ‖z - z'‖ := add_le_add hd₁ hd₂
    _ = 98 * ‖z - z'‖ := by ring

/-- The gradient is `350`-Lipschitz, uniformly in `ε` (Lemma B.2.5). -/
theorem norm_grad_sub_le (h : IsAdmissible ε K) (z z' : EuclideanSpace ℝ (Fin 2)) :
    ‖grad ε K z - grad ε K z'‖ ≤ 350 * ‖z - z'‖ := by
  have hx : |z 0 - z' 0| ≤ ‖z - z'‖ := EuclideanSpace.abs_apply_sub_le z z' 0
  have hf : |f₁' ε K (z 0) - f₁' ε K (z' 0)| ≤ 252 * ‖z - z'‖ :=
    (abs_sub_le_of_hasDerivAt hasDerivAt_f₁' (abs_f₁''_le h) _ _).trans
      (mul_le_mul_of_nonneg_left hx (by norm_num))
  have e : grad ε K z - grad ε K z' = (√2)⁻¹ •
      (!₂[f₁' ε K (z 0) - f₁' ε K (z' 0), 0] + (grad₂ ε K z - grad₂ ε K z')) := by
    rw [grad_eq, grad_eq, ← smul_sub]
    congr 1
    ext i
    fin_cases i <;> simp; ring
  rw [e, norm_smul]
  have hs : ‖(√2)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by rw [Real.le_sqrt zero_le_one] <;> norm_num)
  have h1 : ‖!₂[f₁' ε K (z 0) - f₁' ε K (z' 0), (0 : ℝ)]‖ ≤ 252 * ‖z - z'‖ := by
    refine (EuclideanSpace.norm_toLp_two_le _ _).trans ?_
    rw [abs_zero, add_zero]; exact hf
  calc _ ≤ 1 * ‖!₂[f₁' ε K (z 0) - f₁' ε K (z' 0), (0 : ℝ)] + (grad₂ ε K z - grad₂ ε K z')‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ ≤ 1 * (252 * ‖z - z'‖ + 98 * ‖z - z'‖) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1 (norm_grad₂_sub_le h z z'))
    _ = 350 * ‖z - z'‖ := by ring

/-! #### Second derivatives -/

theorem continuous_smoothStep'' : Continuous smoothStep'' :=
  Hermite.continuous_glue3 continuous_const (by unfold stepPoly''; fun_prop) continuous_const
    (by simp [stepPoly'']) (by norm_num [stepPoly''])

theorem continuous_ramp'' : Continuous ramp'' :=
  Hermite.continuous_glue3 continuous_const (by unfold rampPoly''; fun_prop) continuous_const
    (by simp [rampPoly'']) (by norm_num [rampPoly''])

theorem continuous_smoothStep : Continuous smoothStep :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_smoothStep t).continuousAt

theorem contDiff_capSq' : ContDiff ℝ 1 capSq' := by
  refine contDiff_one_of_hasDerivAt hasDerivAt_capSq' ?_
  unfold capSq''
  have := continuous_smoothStep
  fun_prop

theorem contDiff_mid' : ContDiff ℝ 1 (mid' ε K) := by
  refine contDiff_one_of_hasDerivAt hasDerivAt_mid' ?_
  unfold mid'' localVar
  have := continuous_smoothStep''
  fun_prop

theorem contDiff_f₁' : ContDiff ℝ 1 (f₁' ε K) := by
  refine contDiff_one_of_hasDerivAt hasDerivAt_f₁' ?_
  unfold f₁'' localVar
  have := continuous_ramp''
  fun_prop

theorem contDiff_mid : ContDiff ℝ 1 (mid ε K) :=
  contDiff_one_of_hasDerivAt hasDerivAt_mid contDiff_mid'.continuous

theorem contDiff_grad₂ : ContDiff ℝ 1 (grad₂ ε K) := by
  have hp0 : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 2) => z 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
  have hp1 : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 2) => z 1) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).contDiff
  have hu : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 2) => z 1 - mid ε K (z 0)) :=
    hp1.sub (contDiff_mid.comp hp0)
  refine (contDiff_piLp 2).2 fun i => ?_
  fin_cases i
  · simpa [grad₂, Function.comp_def] using
      ((contDiff_capSq'.comp hu).mul (contDiff_mid'.comp hp0)).neg
  · simpa [grad₂, Function.comp_def] using contDiff_capSq'.comp hu

theorem contDiff_grad : ContDiff ℝ 1 (grad ε K) := by
  have hp0 : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 2) => z 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).contDiff
  have h1 : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 2) =>
      (!₂[f₁' ε K (z 0), 0] : EuclideanSpace ℝ (Fin 2))) := by
    refine (contDiff_piLp 2).2 fun i => ?_
    fin_cases i
    · simpa [Function.comp_def] using contDiff_f₁'.comp hp0
    · simpa using contDiff_const
  rw [show grad ε K = fun z => (√2)⁻¹ • ((!₂[f₁' ε K (z 0), 0] : EuclideanSpace ℝ (Fin 2)) +
    grad₂ ε K z) from funext grad_eq]
  exact (h1.add contDiff_grad₂).const_smul _

/-- The zig-zag function is twice continuously differentiable. -/
theorem contDiff_zigZagFunction (h : IsAdmissible ε K) : ContDiff ℝ 2 (zigZagFunction ε K) :=
  contDiff_two_of_gradient (hasGradientAt_zigZagFunction h) contDiff_grad

/-- The corridor function is twice continuously differentiable. -/
theorem contDiff_f₂ : ContDiff ℝ 2 (f₂ ε K) :=
  contDiff_two_of_gradient hasGradientAt_f₂ contDiff_grad₂

/-- The Hessian of the zig-zag function is bounded by `350`, uniformly in `ε`. -/
theorem norm_iteratedFDeriv_two_zigZagFunction_le (h : IsAdmissible ε K)
    (z : EuclideanSpace ℝ (Fin 2)) : ‖iteratedFDeriv ℝ 2 (zigZagFunction ε K) z‖ ≤ 350 :=
  norm_iteratedFDeriv_two_le_of_gradient (by norm_num) (hasGradientAt_zigZagFunction h)
    (norm_grad_sub_le h) z

/-- The second derivative of the corridor function is bounded by `98`, uniformly in `ε`
(compare Lemma B.2.3 and (B.2.26)–(B.2.31)). -/
theorem norm_iteratedFDeriv_two_f₂_le (h : IsAdmissible ε K) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖iteratedFDeriv ℝ 2 (f₂ ε K) z‖ ≤ 98 :=
  norm_iteratedFDeriv_two_le_of_gradient (by norm_num) hasGradientAt_f₂ (norm_grad₂_sub_le h) z

/-- The first derivative of the corridor function is bounded by `6`, uniformly in `ε`. -/
theorem norm_fderiv_f₂_le (h : IsAdmissible ε K) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖fderiv ℝ (f₂ ε K) z‖ ≤ 6 := by
  rw [((hasGradientAt_iff_hasFDerivAt).1 (hasGradientAt_f₂ z)).fderiv,
    LinearIsometryEquiv.norm_map, grad₂]
  refine (EuclideanSpace.norm_toLp_two_le _ _).trans ?_
  rw [abs_neg, abs_mul]
  have h1 := abs_capSq'_le (z 1 - mid ε K (z 0))
  have h2 := mul_le_mul h1 (abs_mid'_le h (z 0)) (abs_nonneg _) (by norm_num)
  linarith

/-- On the bands `|y - y_mid(x)| ≤ 2` (which contain `[y_low - 1, y_up + 1]`, since the corridor
width is at most `2ε ≤ 2`), the corridor function is bounded by `4`. -/
theorem abs_f₂_le {z : EuclideanSpace ℝ (Fin 2)} (hz : |z 1 - mid ε K (z 0)| ≤ 2) :
    |f₂ ε K z| ≤ 4 := by
  rw [f₂, abs_of_nonneg (capSq_nonneg _)]
  refine (capSq_le_sq _).trans ?_
  nlinarith [abs_nonneg (z 1 - mid ε K (z 0)), sq_abs (z 1 - mid ε K (z 0))]

/-! #### The lower bound -/

theorem abs_ramp'_le (t : ℝ) : |ramp' t| ≤ 1 := by
  refine Hermite.abs_glue3_le (fun _ _ => by norm_num) (fun t ht => ?_) (fun _ _ => by norm_num) t
  exact abs_le.2 ⟨neg_one_le_rampPoly' ht.1 ht.2, rampPoly'_le_one t⟩

theorem node_K_le (h : IsAdmissible ε K) : node (stepLen ε K) K ≤ 2 * ε * K := by
  calc node (stepLen ε K) K ≤ ∑ _j ∈ range K, 2 * ε := sum_le_sum fun j _ => h.stepLen_le j
    _ = 2 * ε * K := by rw [sum_const, card_range, nsmul_eq_mul]; ring

theorem sum_ramp'_of_node_le (h : IsAdmissible ε K) {x : ℝ} (hxK : node (stepLen ε K) K ≤ x) :
    ∑ j ∈ range K, ε / K * ramp' (localVar (stepLen ε K) j x) = ε := by
  have hpos := h.stepLen_pos_of_lt
  have hK := h.K_pos.ne'
  rw [sum_congr rfl fun j hj => by
    rw [ramp'_of_one_le (one_le_localVar hpos (Finset.mem_range.1 hj)
      ((node_le_node hpos (Nat.succ_le_of_lt (Finset.mem_range.1 hj)) le_rfl).trans hxK)),
      mul_one], sum_const, card_range, nsmul_eq_mul]
  field_simp

/-- `|f₁'| ≤ 3 ε` on `[0, ∞)`. -/
theorem abs_f₁'_le (h : IsAdmissible ε K) {x : ℝ} (hx : 0 ≤ x) : |f₁' ε K x| ≤ 3 * ε := by
  have hε := h.pos
  have hK := h.K_pos.ne'
  have hpos := h.stepLen_pos_of_lt
  rcases lt_or_ge x (node (stepLen ε K) K) with hxK | hxK
  · obtain ⟨k, hk, hxk⟩ := exists_mem_Ico_node hx hxK
    rw [f₁', sum_localVar_eq hpos (G := ramp') (g₁ := 1) (fun t ht => ramp'_of_nonpos ht)
      (fun t ht => ramp'_of_one_le ht) _ hk (Ico_subset_Icc_self hxk),
      ramp'_of_nonpos (by linarith : x - node (stepLen ε K) K ≤ 0), mul_zero, add_zero,
      sum_const, card_range, nsmul_eq_mul, mul_one]
    have hr := abs_le.1 (abs_ramp'_le (localVar (stepLen ε K) k x))
    have hb : 0 ≤ ε / K := div_nonneg hε.le h.K_pos.le
    have hbe : ε / K ≤ ε := div_le_self hε.le h.one_le_K
    have hk' : (k : ℝ) * (ε / K) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ h.K_pos]
      have : (k : ℝ) ≤ K := by exact_mod_cast hk.le
      nlinarith
    rw [h.stepLen_zero, abs_le]
    constructor <;> nlinarith [mul_nonneg hb (by exact_mod_cast (Nat.zero_le k) : (0 : ℝ) ≤ k)]
  · rw [f₁', sum_ramp'_of_node_le h hxK, h.stepLen_zero]
    have hr := abs_le.1 (abs_ramp'_le (x - node (stepLen ε K) K))
    rw [abs_le]
    constructor <;> nlinarith

/-- `f₁` vanishes in slope after `x_{k_ε} + 1`. -/
theorem f₁'_eq_zero (h : IsAdmissible ε K) {x : ℝ} (hx : node (stepLen ε K) K + 1 ≤ x) :
    f₁' ε K x = 0 := by
  rw [f₁', sum_ramp'_of_node_le h (by linarith), h.stepLen_zero,
    ramp'_of_one_le (by linarith : 1 ≤ x - node (stepLen ε K) K)]
  ring

/-- `f₁` is linear on `(-∞, 0]`: `f₁(x) = f₁(0) + x f₁'(0) = 4 - 2 ε x` (B.2.24). -/
theorem f₁_of_nonpos (h : IsAdmissible ε K) {x : ℝ} (hx : x ≤ 0) : f₁ ε K x = 4 - 2 * ε * x := by
  have hpos := h.stepLen_pos_of_lt
  rw [f₁, sum_eq_zero fun j hj => by
    rw [ramp_of_nonpos (localVar_nonpos hpos (Finset.mem_range.1 hj)
      (hx.trans (node_nonneg hpos (Finset.mem_range.1 hj).le))), mul_zero],
    ramp_of_nonpos (by linarith [node_nonneg hpos (le_refl K)]), h.stepLen_zero]
  ring

/-- `f₁ ≥ -5`, uniformly in `ε` (compare (B.2.6): `f₁` decreases from `4` by at most
`∑_k (ε + ω_k)² ≤ 4`). -/
theorem neg_five_le_f₁ (h : IsAdmissible ε K) (x : ℝ) : -5 ≤ f₁ ε K x := by
  have hε := h.pos
  set c := node (stepLen ε K) K + 1 with hc
  have hc0 : 0 ≤ c := by linarith [node_nonneg h.stepLen_pos_of_lt (le_refl K)]
  have h0 : f₁ ε K 0 = 4 := by simpa using f₁_of_nonpos h le_rfl
  have hcb : 3 * ε * c ≤ 9 := by
    have h1 := node_K_le h
    have h2 := h.mul_sq
    have h3 := h.le_one
    have : 3 * ε * c ≤ 3 * ε * (2 * ε * K + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have key : ∀ y ∈ Icc 0 c, 4 - 3 * ε * c ≤ f₁ ε K y := by
    intro y hy
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f₁ ε K) (f' := f₁' ε K)
      (s := Icc 0 c) (fun x _ => (hasDerivAt_f₁ h x).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact abs_f₁'_le h hx.1) (convex_Icc 0 c)
      (left_mem_Icc.2 hc0) hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, h0, sub_zero, abs_of_nonneg hy.1] at this
    have := neg_abs_le (f₁ ε K y - 4)
    nlinarith [hy.2]
  rcases le_or_gt x 0 with hx | hx
  · rw [f₁_of_nonpos h hx]; nlinarith
  rcases le_or_gt x c with hxc | hxc
  · linarith [key x ⟨hx.le, hxc⟩]
  · have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f₁ ε K) (f' := f₁' ε K)
      (s := Ici c) (C := 0) (fun x _ => (hasDerivAt_f₁ h x).hasDerivWithinAt)
      (fun x hx => by rw [f₁'_eq_zero h hx, norm_zero]) (convex_Ici c) (mem_Ici.2 le_rfl)
      (mem_Ici.2 hxc.le)
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
    rw [this]
    linarith [key c ⟨hc0, le_rfl⟩]

/-! #### The gradient at the iterates -/

@[simp] theorem zigZagIterate_apply_zero (ε : ℝ) (K k : ℕ) :
    zigZagIterate ε K k 0 = node (stepLen ε K) k := by simp [zigZagIterate]

@[simp] theorem zigZagIterate_apply_one (ε : ℝ) (K k : ℕ) :
    zigZagIterate ε K k 1 = height ε K k := by simp [zigZagIterate]

/-- The zig-zag iterates start at the origin. -/
@[simp] theorem zigZagIterate_zero (ε : ℝ) (K : ℕ) : zigZagIterate ε K 0 = 0 := by
  ext i; fin_cases i <;> simp [zigZagIterate, height]

theorem abs_height_sub_mid_node_le (h : IsAdmissible ε K) {k : ℕ} (hk : k ≤ K) :
    |height ε K k - mid ε K (node (stepLen ε K) k)| ≤ 1 := by
  rw [height_sub_mid_node h hk, abs_neg, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_pos (h.stepLen_pos hk), abs_two]
  linarith [h.stepLen_le k, h.le_one]

/-- The gradient at the iterates (B.2.25): `∇f(x_k, y_k) = -((ε + ω_k)/√2) (1, (-1)^k)`. -/
theorem grad_zigZagIterate (h : IsAdmissible ε K) {k : ℕ} (hk : k ≤ K) :
    grad ε K (zigZagIterate ε K k) = -(stepLen ε K k / √2) • !₂[1, (-1) ^ k] := by
  rw [grad, zigZagIterate_apply_zero, zigZagIterate_apply_one,
    capSq'_of_abs_le (abs_height_sub_mid_node_le h hk), height_sub_mid_node h hk,
    mid'_node h hk, f₁'_node h hk]
  ext i
  fin_cases i <;> simp <;> ring

theorem norm_toLp_one_neg_one_pow (k : ℕ) : ‖!₂[(1 : ℝ), (-1) ^ k]‖ = √2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_one, norm_pow, norm_neg]
  norm_num

/-! #### The line search -/

section Local

variable (h : IsAdmissible ε K) {k : ℕ} (hk : k < K) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
include h hk ht

theorem mem_Icc_node_add :
    node (stepLen ε K) k + stepLen ε K k * t ∈
      Icc (node (stepLen ε K) k) (node (stepLen ε K) (k + 1)) := by
  have ha := h.stepLen_pos hk.le
  rw [node_succ]
  constructor <;> nlinarith [ht.1, ht.2]

omit ht in
theorem localVar_node_add :
    localVar (stepLen ε K) k (node (stepLen ε K) k + stepLen ε K k * t) = t := by
  have ha := (h.stepLen_pos hk.le).ne'
  rw [localVar]
  field_simp
  ring

theorem f₁'_node_add :
    f₁' ε K (node (stepLen ε K) k + stepLen ε K k * t) =
      -stepLen ε K k + ε / K * rampPoly' t := by
  have hpos := h.stepLen_pos_of_lt
  have hx := mem_Icc_node_add h hk ht
  have hxK : node (stepLen ε K) k + stepLen ε K k * t - node (stepLen ε K) K ≤ 0 := by
    linarith [hx.2, node_le_node hpos (Nat.succ_le_of_lt hk) le_rfl]
  rw [f₁', sum_localVar_eq hpos (G := ramp') (g₁ := 1) (fun t ht => ramp'_of_nonpos ht)
    (fun t ht => ramp'_of_one_le ht) _ hk hx, localVar_node_add h hk, ramp'_of_mem_Icc ht,
    ramp'_of_nonpos hxK, mul_zero, add_zero, sum_const, card_range, nsmul_eq_mul, mul_one,
    h.stepLen_zero]
  have := h.K_pos.ne'
  simp only [stepLen, omega]
  field_simp
  ring

theorem mid_node_add :
    mid ε K (node (stepLen ε K) k + stepLen ε K k * t) =
      mid ε K (node (stepLen ε K) k) + ε / (2 * K) * (-1) ^ k * stepPoly t := by
  have hpos := h.stepLen_pos_of_lt
  rw [mid, sum_localVar_eq hpos (G := smoothStep) (g₁ := 1) (fun t ht => smoothStep_of_nonpos ht)
    (fun t ht => smoothStep_of_one_le ht) _ hk (mem_Icc_node_add h hk ht),
    localVar_node_add h hk, smoothStep_of_mem_Icc ht, mid_node h hk.le, mul_one]
  ring

theorem mid'_node_add :
    mid' ε K (node (stepLen ε K) k + stepLen ε K k * t) =
      ε / (2 * K) * (-1) ^ k / stepLen ε K k * stepPoly' t := by
  have hpos := h.stepLen_pos_of_lt
  rw [mid', sum_localVar_eq hpos (G := smoothStep') (g₁ := 0)
    (fun t ht => smoothStep'_of_nonpos ht) (fun t ht => smoothStep'_of_one_le ht) _ hk
    (mem_Icc_node_add h hk ht), localVar_node_add h hk, smoothStep'_of_mem_Icc ht, mul_zero,
    zero_add]

end Local

/-- **The slope along the step is negative** (B.2.32)–(B.2.36): along the segment from
`(x_k, y_k)` in the direction `(1, (-1)^k)`, at the point with local variable `t ∈ [0, 1)`,
`f₁'(x) + ∂_y f₂ ((-1)^k - y_mid'(x)) < 0`. -/
theorem slope_neg (h : IsAdmissible ε K) {k : ℕ} (hk : k < K) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    f₁' ε K (node (stepLen ε K) k + stepLen ε K k * t) +
      capSq' (height ε K k + (-1) ^ k * stepLen ε K k * t -
        mid ε K (node (stepLen ε K) k + stepLen ε K k * t)) *
      ((-1) ^ k - mid' ε K (node (stepLen ε K) k + stepLen ε K k * t)) < 0 := by
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1.le⟩
  rw [f₁'_node_add h hk ht, mid_node_add h hk ht, mid'_node_add h hk ht]
  set a := stepLen ε K k with ha_def
  set b := ε / K with hb_def
  set s : ℝ := (-1) ^ k with hs_def
  have hs : s * s = 1 := by rw [hs_def, ← pow_add, ← two_mul, pow_mul]; norm_num
  have ha : 0 < a := h.stepLen_pos hk.le
  have hb : 0 < b := div_pos h.pos h.K_pos
  have hab : 2 * b ≤ a := h.two_mul_div_K_le hk
  have ha2 : a ≤ 2 := by linarith [h.stepLen_le k, h.le_one]
  have hS0 := stepPoly_nonneg ht0
  have hS2 := stepPoly_le_two_mul ht0 ht1.le
  have hS'0 := stepPoly'_nonneg (t := t)
  have hS'1 := stepPoly'_le ht
  have e2 : ε / (2 * K) = b / 2 := by rw [hb_def]; ring
  have hu := height_sub_mid_node h hk.le
  rw [← ha_def, ← hs_def] at hu
  set v := a * (t - 1 / 2) - b / 2 * stepPoly t with hv_def
  have huv : height ε K k + s * a * t - (mid ε K (node (stepLen ε K) k) +
      ε / (2 * K) * s * stepPoly t) = s * v := by
    rw [e2, hv_def]; linear_combination hu
  have hbS : b * stepPoly t ≤ a * t := by nlinarith
  have hv1 : v ≤ (a - b * stepPoly t) / 2 := by rw [hv_def]; nlinarith
  have hv2 : -v ≤ (a - b * stepPoly t) / 2 := by rw [hv_def]; nlinarith
  have hvabs : |s * v| ≤ 1 := by
    rw [abs_mul, hs_def, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_le]
    constructor <;> nlinarith
  rw [huv, capSq'_of_abs_le hvabs]
  set w := 1 - b / (2 * a) * stepPoly' t with hw_def
  have hw : s - ε / (2 * K) * s / a * stepPoly' t = s * w := by
    rw [e2, hw_def]; field_simp
  rw [hw]
  have hw0 : 0 ≤ w := by
    have : b / (2 * a) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
    have : b / (2 * a) * stepPoly' t ≤ 1 / 4 * (15 / 8) :=
      mul_le_mul this hS'1 hS'0 (by norm_num)
    rw [hw_def]; linarith
  have hw1 : w ≤ 1 := by
    have : 0 ≤ b / (2 * a) * stepPoly' t := mul_nonneg (by positivity) hS'0
    rw [hw_def]; linarith
  have e3 : -a + b * rampPoly' t + 2 * (s * v) * (s * w) = -a + b * rampPoly' t + 2 * (v * w) := by
    linear_combination (2 * v * w) * hs
  rw [e3]
  rcases ht0.lt_or_eq with htpos | htz
  · have hvw : v * w ≤ (a - b * stepPoly t) / 2 := by
      rcases le_or_gt 0 v with hv | hv
      · nlinarith
      · nlinarith
    have hP := rampPoly'_sub_stepPoly t
    have hpos : 0 < 6 * (t * (1 - t)) ^ 2 * (t + 2) := by
      have : 0 < t * (1 - t) := mul_pos htpos (by linarith)
      positivity
    nlinarith
  · subst htz
    simp [hv_def, hw_def, stepPoly, stepPoly', rampPoly']
    linarith

/-! #### Beyond the next iterate -/

theorem neg_two_mul_le_rampPoly' {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : -2 * t ≤ rampPoly' t := by
  have e : rampPoly' t + 2 * t = t * (2 - 12 * t + 28 * t ^ 2 - 15 * t ^ 3) := by
    simp only [rampPoly']; ring
  have h1 : 0 ≤ 1 - t := by linarith
  have hc : 0 ≤ 2 - 12 * t + 28 * t ^ 2 - 15 * t ^ 3 := by
    nlinarith [mul_nonneg ht h1, mul_nonneg (mul_nonneg ht h1) h1, mul_nonneg (mul_nonneg ht ht) h1,
      sq_nonneg (3 * t - 1), mul_nonneg ht (sq_nonneg (3 * t - 1)),
      mul_nonneg h1 (sq_nonneg (3 * t - 1)), mul_nonneg ht (sq_nonneg (t - 1 / 2)),
      mul_nonneg h1 (sq_nonneg (t - 1 / 2))]
  nlinarith [mul_nonneg ht hc]

/-- The alternating sum `(-1)^k ∑_{i=k+1}^{m-1} (-1)^i` is `-1` or `0` according to the parity of
`m + k`. -/
theorem neg_one_pow_mul_sum_Ico {k m : ℕ} (hm : k + 1 ≤ m) :
    (-1 : ℝ) ^ k * ∑ i ∈ Ico (k + 1) m, (-1 : ℝ) ^ i = -(1 + (-1) ^ (m + k)) / 2 := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [Ico_self, sum_empty, mul_zero, show k + 1 + k = 2 * k + 1 by ring, pow_succ, pow_mul]
    norm_num
  | succ m hm ih =>
    rw [sum_Ico_succ_top hm, mul_add, ih, show m + 1 + k = (m + k) + 1 by ring, pow_succ,
      ← pow_add, show k + m = m + k by ring]
    ring

/-- `mid` is constant after the last node. -/
theorem mid_of_node_le (h : IsAdmissible ε K) {x : ℝ} (hx : node (stepLen ε K) K ≤ x) :
    mid ε K x = mid ε K (node (stepLen ε K) K) := by
  have hpos := h.stepLen_pos_of_lt
  rw [mid_node h le_rfl, mid]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [smoothStep_of_one_le (one_le_localVar hpos (Finset.mem_range.1 hj)
    ((node_le_node hpos (Nat.succ_le_of_lt (Finset.mem_range.1 hj)) le_rfl).trans hx)), mul_one]

/-- `mid'` vanishes after the last node. -/
theorem mid'_of_node_le (h : IsAdmissible ε K) {x : ℝ} (hx : node (stepLen ε K) K ≤ x) :
    mid' ε K x = 0 := by
  have hpos := h.stepLen_pos_of_lt
  refine sum_eq_zero fun j hj => ?_
  rw [smoothStep'_of_one_le (one_le_localVar hpos (Finset.mem_range.1 hj)
    ((node_le_node hpos (Nat.succ_le_of_lt (Finset.mem_range.1 hj)) le_rfl).trans hx)), mul_zero]

/-- A point in terms of its local variable on `[x_m, x_{m+1}]`. -/
theorem eq_node_add_localVar (h : IsAdmissible ε K) {m : ℕ} (hm : m < K) (x : ℝ) :
    x = node (stepLen ε K) m + stepLen ε K m * localVar (stepLen ε K) m x := by
  have := (h.stepLen_pos hm.le).ne'
  rw [localVar]
  field_simp
  ring

/-- **The corridor stays on one side.** After `x_{k+1}`, the middle of the corridor never moves
beyond its value at `x_{k+1}` in the direction `(-1)^k` of the `k`-th step:
`(-1)^k (y_mid(x) - y_mid(x_{k+1})) ≤ 0`. -/
theorem neg_one_pow_mul_mid_sub_le (h : IsAdmissible ε K) {k : ℕ} (hk : k < K) {x : ℝ}
    (hx : node (stepLen ε K) (k + 1) ≤ x) :
    (-1) ^ k * (mid ε K x - mid ε K (node (stepLen ε K) (k + 1))) ≤ 0 := by
  have hpos := h.stepLen_pos_of_lt
  have hc : 0 ≤ ε / (2 * K) := div_nonneg h.pos.le (by positivity)
  have hnode : ∀ m, k + 1 ≤ m → m ≤ K →
      (-1) ^ k * (mid ε K (node (stepLen ε K) m) - mid ε K (node (stepLen ε K) (k + 1))) =
        ε / (2 * K) * (-(1 + (-1) ^ (m + k)) / 2) := by
    intro m hkm hmK
    rw [mid_node h hmK, mid_node h (Nat.succ_le_of_lt hk), ← neg_one_pow_mul_sum_Ico hkm,
      ← sum_range_add_sum_Ico _ hkm, ← Finset.mul_sum (Ico (k + 1) m)]
    ring
  rcases lt_or_ge x (node (stepLen ε K) K) with hxK | hxK
  · obtain ⟨m, hm, hxm⟩ := exists_mem_Ico_node
      ((node_nonneg hpos (Nat.succ_le_of_lt hk)).trans hx) hxK
    have hkm : k + 1 ≤ m := by
      by_contra hcon
      have := node_le_node hpos (by omega : m + 1 ≤ k + 1) (Nat.succ_le_of_lt hk)
      linarith [hxm.2]
    have ht := localVar_mem_Icc hpos hm (Ico_subset_Icc_self hxm)
    set τ := localVar (stepLen ε K) m x
    have hS0 := stepPoly_nonneg ht.1
    have hS1 := stepPoly_le_one ht.1 ht.2
    have e : (-1 : ℝ) ^ k * (ε / (2 * K) * (-1) ^ m * stepPoly τ) =
        ε / (2 * K) * ((-1) ^ (m + k)) * stepPoly τ := by rw [pow_add]; ring
    rw [eq_node_add_localVar h hm x, mid_node_add h hm ht, add_sub_right_comm, mul_add,
      hnode m hkm hm.le, e]
    rcases neg_one_pow_eq_or ℝ (m + k) with he | he <;> rw [he] <;> nlinarith
  · rw [mid_of_node_le h hxK, hnode K (Nat.succ_le_of_lt hk) le_rfl]
    rcases neg_one_pow_eq_or ℝ (K + k) with he | he <;> rw [he] <;> nlinarith

/-- **The slope is nonnegative beyond the next iterate.** Continuing the `k`-th step past
`(x_{k+1}, y_{k+1})` by `σ ≥ 0` in the direction `(1, (-1)^k)`, the slope
`f₁'(x) + ψ'(y - y_mid(x)) ((-1)^k - y_mid'(x))` is nonnegative. -/
theorem slope_nonneg (h : IsAdmissible ε K) {k : ℕ} (hk : k < K) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 ≤ f₁' ε K (node (stepLen ε K) (k + 1) + σ) +
      capSq' (height ε K (k + 1) + (-1) ^ k * σ - mid ε K (node (stepLen ε K) (k + 1) + σ)) *
      ((-1) ^ k - mid' ε K (node (stepLen ε K) (k + 1) + σ)) := by
  have hpos := h.stepLen_pos_of_lt
  have hε := h.pos
  have hε1 := h.le_one
  have hk1 : k + 1 ≤ K := Nat.succ_le_of_lt hk
  set x := node (stepLen ε K) (k + 1) + σ with hx_def
  have hx0 : 0 ≤ x := by linarith [node_nonneg hpos hk1]
  set s : ℝ := (-1) ^ k with hs_def
  have hs : s * s = 1 := by rw [hs_def, ← pow_add, ← two_mul, pow_mul]; norm_num
  set a := stepLen ε K (k + 1) with ha_def
  have ha : ε ≤ a := h.le_stepLen hk1
  have ha0' : 0 < a := hε.trans_le ha
  set b := ε / K with hb_def
  have hb : 0 < b := div_pos hε h.K_pos
  have hab : a + b ≤ 2 * ε := by rw [ha_def, stepLen_succ]; linarith [h.stepLen_le k]
  set u := height ε K (k + 1) + s * σ - mid ε K x with hu_def
  clear_value x s a b u
  have hu0 : height ε K (k + 1) - mid ε K (node (stepLen ε K) (k + 1)) = s * (a / 2) := by
    rw [height_sub_mid_node h hk1, pow_succ, ← hs_def, ← ha_def]; ring
  have hD := neg_one_pow_mul_mid_sub_le h hk (x := x) (by linarith)
  rw [← hs_def] at hD
  have hsu : a / 2 + σ ≤ s * u := by
    have e : s * u = s * s * (a / 2) + σ * (s * s) -
        s * (mid ε K x - mid ε K (node (stepLen ε K) (k + 1))) := by
      rw [hu_def]; linear_combination s * hu0
    rw [e, hs]; linarith
  have hhs : capSq' u * (s - mid' ε K x) = capSq' (s * u) * (1 - s * mid' ε K x) := by
    have e : capSq' (s * u) = s * capSq' u := by
      rcases neg_one_pow_eq_or ℝ k with he | he
      · rw [hs_def, he, one_mul, one_mul]
      · rw [hs_def, he, neg_one_mul, capSq'_neg, neg_one_mul]
    rw [e]
    linear_combination (capSq' u * mid' ε K x) * hs
  have hlow := le_capSq' (by linarith : 0 ≤ a / 2 + σ) hsu
  rw [hhs]
  have hmin0 : 0 ≤ min (a / 2 + σ) 1 := le_min (by linarith) zero_le_one
  suffices key : 0 ≤ f₁' ε K x + 2 * min (a / 2 + σ) 1 * (1 - s * mid' ε K x) ∧
      0 ≤ 1 - s * mid' ε K x by
    nlinarith [mul_le_mul_of_nonneg_right hlow key.2]
  rcases lt_or_ge x (node (stepLen ε K) K) with hxK | hxK
  · obtain ⟨m, hm, hxm⟩ := exists_mem_Ico_node hx0 hxK
    have hkm : k + 1 ≤ m := by
      by_contra hcon
      have := node_le_node hpos (by omega : m + 1 ≤ k + 1) hk1
      linarith [hxm.2]
    have ht := localVar_mem_Icc hpos hm (Ico_subset_Icc_self hxm)
    set t := localVar (stepLen ε K) m x with ht_def
    clear_value t
    have hxe := eq_node_add_localVar h hm x
    rw [← ht_def] at hxe
    have hf := f₁'_node_add h hm ht
    have hm' := mid'_node_add h hm ht
    rw [← hxe] at hf hm'
    rw [← hb_def] at hf
    have e2 : ε / (2 * (K : ℝ)) = b / 2 := by rw [hb_def]; ring
    rw [e2] at hm'
    have hP1 := neg_one_le_rampPoly' ht.1 ht.2
    have hP2 := neg_two_mul_le_rampPoly' ht.1 ht.2
    have hS'0 := stepPoly'_nonneg (t := t)
    have hS'1 := stepPoly'_le ht
    rcases hkm.eq_or_lt with hkm | hkm
    · subst hkm
      rw [← ha_def] at hxe hf hm'
      have hσe : σ = a * t := by linarith [hxe, hx_def]
      have ha0 : 0 < a := ha0'
      have hsm : s * mid' ε K x = -(b / (2 * a) * stepPoly' t) := by
        rw [hm', pow_succ, ← hs_def]
        linear_combination (-(b / (2 * a) * stepPoly' t)) * hs
      have hw : 0 ≤ b / (2 * a) * stepPoly' t := mul_nonneg (by positivity) hS'0
      have h2b : 2 * b ≤ a := by
        have := h.two_mul_div_K_le hm
        rwa [← ha_def, ← hb_def] at this
      rw [hf, hsm]
      refine ⟨?_, by linarith only [hw]⟩
      rcases le_or_gt (a / 2 + σ) 1 with hv | hv
      · rw [min_eq_left hv, hσe]
        linarith only [mul_nonneg (by linarith only [mul_nonneg ha0'.le ht.1, ha0'] :
            0 ≤ a + 2 * (a * t)) hw,
          mul_nonneg hb.le (by linarith only [hP2] : 0 ≤ rampPoly' t + 2 * t),
          mul_nonneg ht.1 (by linarith only [h2b, hb] : 0 ≤ a - b)]
      · rw [min_eq_right hv.le]
        linarith only [mul_nonneg hb.le (by linarith only [hP1] : 0 ≤ rampPoly' t + 1), hw, hab,
          hε1, hb]
    · have hK3 : 3 ≤ K := by omega
      have h4b := h.four_mul_div_K_le hK3 hm
      rw [← hb_def] at h4b
      have ham0 : 0 < stepLen ε K m := hpos m hm
      have ham : stepLen ε K m ≤ a := by
        rw [ha_def]; exact h.stepLen_le_stepLen (by omega : k + 1 ≤ m)
      have hσa : a ≤ σ := by
        have h1 := node_le_node hpos (by omega : k + 2 ≤ m) hm.le
        rw [node_succ] at h1
        linarith [hxm.1]
      have hq : b / (2 * stepLen ε K m) * stepPoly' t ≤ 15 / 64 := by
        have : b / (2 * stepLen ε K m) ≤ 1 / 8 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        have := mul_le_mul this hS'1 hS'0 (by norm_num)
        linarith
      have hq0 : 0 ≤ b / (2 * stepLen ε K m) * stepPoly' t :=
        mul_nonneg (div_nonneg hb.le (by linarith)) hS'0
      have hsm : -(15 / 64) ≤ s * mid' ε K x ∧ s * mid' ε K x ≤ 15 / 64 := by
        have e : s * mid' ε K x =
            (-1) ^ (m + k) * (b / (2 * stepLen ε K m) * stepPoly' t) := by
          rw [hm', hs_def, pow_add]; ring
        rw [e]
        rcases neg_one_pow_eq_or ℝ (m + k) with he | he <;> rw [he] <;> constructor <;>
          linarith only [hq, hq0]
      have hε3 : 2 * ε ≤ 49 / 32 := h.two_mul_le_of_three_le hK3
      rw [hf]
      refine ⟨?_, by linarith only [hsm.2]⟩
      have hfb : -a - b ≤ -stepLen ε K m + b * rampPoly' t := by
        linarith only [ham, mul_nonneg hb.le (by linarith only [hP1] : 0 ≤ rampPoly' t + 1)]
      rcases le_or_gt (a / 2 + σ) 1 with hv | hv
      · rw [min_eq_left hv]
        have hX := mul_le_mul (by linarith only [hσa] : 3 * a / 2 ≤ a / 2 + σ)
          (by linarith only [hsm.2] : 49 / 64 ≤ 1 - s * mid' ε K x) (by norm_num)
          (by linarith only [ha0', hσ])
        have e : 2 * (a / 2 + σ) * (1 - s * mid' ε K x) =
            2 * ((a / 2 + σ) * (1 - s * mid' ε K x)) := by ring
        rw [e]
        linarith only [hfb, hX, h4b, ham, ha0']
      · rw [min_eq_right hv.le]
        linarith only [hfb, hsm.2, hε3, hab]
  · have hm' := mid'_of_node_le h hxK
    have hf : f₁' ε K x = -ε + ε * ramp' (x - node (stepLen ε K) K) := by
      rw [f₁', sum_ramp'_of_node_le h hxK, h.stepLen_zero]; ring
    rw [hm', mul_zero, sub_zero, mul_one]
    refine ⟨?_, zero_le_one⟩
    rw [hf]
    have hr := abs_le.1 (abs_ramp'_le (x - node (stepLen ε K) K))
    rcases hk1.lt_or_eq with hk2 | hk2
    · have hσa : a ≤ σ := by
        have h1 := node_le_node hpos (by omega : k + 2 ≤ K) le_rfl
        rw [node_succ] at h1
        linarith
      have : ε ≤ min (a / 2 + σ) 1 := le_min (by linarith) hε1
      nlinarith
    · have haε : a = ε := by rw [ha_def, hk2, stepLen_self]
      have hσr : x - node (stepLen ε K) K = σ := by rw [hx_def, hk2]; ring
      rw [hσr]
      rcases le_or_gt 1 σ with hσ1 | hσ1
      · rw [ramp'_of_one_le hσ1]
        nlinarith
      · rw [ramp'_of_mem_Icc ⟨hσ, hσ1.le⟩]
        have hP1 := neg_one_le_rampPoly' hσ hσ1.le
        have hP2 := neg_two_mul_le_rampPoly' hσ hσ1.le
        rcases le_or_gt (a / 2 + σ) 1 with hv | hv
        · rw [min_eq_left hv, haε]
          nlinarith [mul_nonneg hε.le (by linarith : 0 ≤ rampPoly' σ + 2 * σ),
            mul_nonneg hσ (by linarith : 0 ≤ 1 - ε)]
        · rw [min_eq_right hv.le]
          nlinarith [mul_nonneg hε.le (by linarith : 0 ≤ rampPoly' σ + 1)]

end ZigZag

variable {ε : ℝ} {K : ℕ}

/-- **The gradient at the iterates** ([cartis2022evaluation] Lemma B.2.2, (B.2.21)–(B.2.25)). For
admissible `ε` (`k_ε = ε⁻²`) and `k ≤ k_ε`,
`∇f(x_k, y_k) = -((ε + ω_k)/√2) (1, (-1)^k)`, so `‖∇f(x_k, y_k)‖ = ε + ω_k`, and the next iterate
is the steepest-descent step with stepsize `√2`:
`(x_{k+1}, y_{k+1}) = (x_k, y_k) - √2 ∇f(x_k, y_k)`. -/
theorem zigZag_gradient (h : IsAdmissible ε K) {k : ℕ} (hk : k ≤ K) :
    gradient (zigZagFunction ε K) (zigZagIterate ε K k) =
        -((ε + omega ε K k) / √2) • !₂[1, (-1) ^ k] ∧
      ‖gradient (zigZagFunction ε K) (zigZagIterate ε K k)‖ = ε + omega ε K k ∧
      zigZagIterate ε K (k + 1) =
        zigZagIterate ε K k - √2 • gradient (zigZagFunction ε K) (zigZagIterate ε K k) := by
  have hg : gradient (zigZagFunction ε K) (zigZagIterate ε K k) =
      -((ε + omega ε K k) / √2) • !₂[1, (-1) ^ k] := by
    rw [gradient_zigZagFunction h, grad_zigZagIterate h hk, stepLen]
  have ha : 0 < ε + omega ε K k := h.stepLen_pos hk
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.2 two_pos
  refine ⟨hg, ?_, ?_⟩
  · rw [hg, norm_smul, norm_neg, norm_toLp_one_neg_one_pow, Real.norm_eq_abs,
      abs_of_pos (div_pos ha hs)]
    field_simp
  · rw [hg]
    ext i
    fin_cases i <;> simp [zigZagIterate, node_succ, height_succ, stepLen] <;> field_simp

/-- **Uniform bounds** ([cartis2022evaluation] Lemmas B.2.4–B.2.5). There are constants `M ≥ 0`,
`L ≥ 1` such that for every admissible `ε` (`k_ε = ε⁻²`) the zig-zag function is continuously
differentiable, bounded below by `-M`, and has an `L`-Lipschitz gradient on `ℝ²`. -/
theorem zigZag_bounds : ∃ M L : ℝ, 0 ≤ M ∧ 1 ≤ L ∧ ∀ (ε : ℝ) (K : ℕ), IsAdmissible ε K →
    ContDiff ℝ 1 (zigZagFunction ε K) ∧ (∀ z, -M ≤ zigZagFunction ε K z) ∧
      ∀ z z', ‖gradient (zigZagFunction ε K) z - gradient (zigZagFunction ε K) z'‖ ≤
        L * ‖z - z'‖ := by
  refine ⟨5, 350, by norm_num, by norm_num, fun ε K h =>
    ⟨(contDiff_zigZagFunction h).of_le (by norm_num), fun z => ?_, fun z z' => ?_⟩⟩
  · have hs : (1 : ℝ) ≤ √2 := by rw [Real.le_sqrt zero_le_one] <;> norm_num
    rw [zigZagFunction, le_div_iff₀ (by positivity)]
    nlinarith [neg_five_le_f₁ h (z 0), capSq_nonneg (z 1 - mid ε K (z 0))]
  · rw [gradient_zigZagFunction h, gradient_zigZagFunction h]
    exact norm_grad_sub_le h z z'

/-- **Second-order bounds** ([cartis2022evaluation] Lemmas B.2.3 and B.2.5, (B.2.10),
(B.2.26)–(B.2.31)). There is a constant `C` such that for every admissible `ε` the zig-zag
function and the corridor function `f₂ = ZigZag.f₂ ε K` are twice continuously differentiable
with second derivatives bounded by `C` on `ℝ²`, `‖∇f₂‖ ≤ C` on `ℝ²`, and `|f₂| ≤ C` on the bands
`|y - y_mid(x)| ≤ 2` (which contain `[y_low(x) - 1, y_up(x) + 1]`). -/
theorem zigZag_hessian_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (K : ℕ), IsAdmissible ε K →
    ContDiff ℝ 2 (zigZagFunction ε K) ∧ ContDiff ℝ 2 (ZigZag.f₂ ε K) ∧
      ∀ z, ‖iteratedFDeriv ℝ 2 (zigZagFunction ε K) z‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 2 (ZigZag.f₂ ε K) z‖ ≤ C ∧ ‖fderiv ℝ (ZigZag.f₂ ε K) z‖ ≤ C ∧
        (|z 1 - mid ε K (z 0)| ≤ 2 → |ZigZag.f₂ ε K z| ≤ C) :=
  ⟨350, by norm_num, fun _ _ h => ⟨contDiff_zigZagFunction h, contDiff_f₂, fun z =>
    ⟨norm_iteratedFDeriv_two_zigZagFunction_le h z,
      (norm_iteratedFDeriv_two_f₂_le h z).trans (by norm_num),
      (norm_fderiv_f₂_le h z).trans (by norm_num),
      fun hz => (abs_f₂_le hz).trans (by norm_num)⟩⟩⟩

/-- **The slope along the steepest-descent ray** from `(x_k, y_k)`, `k ≤ k_ε`: at the point
`(x_k, y_k) - τ ∇f(x_k, y_k) = (x, y)` with `x = x_k + (ε + ω_k) τ/√2`,
`⟪∇f(x, y), ∇f(x_k, y_k)⟫ = -((ε + ω_k)/2) (f₁'(x) + ψ'(y - y_mid(x)) ((-1)^k - y_mid'(x)))`
(compare (B.2.32)). -/
theorem zigZag_inner_gradient_ray (h : IsAdmissible ε K) {k : ℕ} (hk : k ≤ K) (τ : ℝ) :
    ⟪gradient (zigZagFunction ε K)
        (zigZagIterate ε K k - τ • gradient (zigZagFunction ε K) (zigZagIterate ε K k)),
      gradient (zigZagFunction ε K) (zigZagIterate ε K k)⟫ =
      -(stepLen ε K k / 2) *
        (f₁' ε K (node (stepLen ε K) k + stepLen ε K k * (τ / √2)) +
          capSq' (height ε K k + (-1) ^ k * stepLen ε K k * (τ / √2) -
            mid ε K (node (stepLen ε K) k + stepLen ε K k * (τ / √2))) *
          ((-1) ^ k - mid' ε K (node (stepLen ε K) k + stepLen ε K k * (τ / √2)))) := by
  have hg : gradient (zigZagFunction ε K) (zigZagIterate ε K k) =
      -(stepLen ε K k / √2) • !₂[1, (-1) ^ k] := (zigZag_gradient h hk).1
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.2 two_pos
  have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  have hpt : zigZagIterate ε K k - τ • gradient (zigZagFunction ε K) (zigZagIterate ε K k) =
      !₂[node (stepLen ε K) k + stepLen ε K k * (τ / √2),
        height ε K k + (-1) ^ k * stepLen ε K k * (τ / √2)] := by
    rw [hg]
    ext i
    fin_cases i <;> simp [zigZagIterate, stepLen] <;> ring
  rw [hpt, gradient_zigZagFunction h, hg, grad]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    neg_smul, inner_neg_right, inner_smul_right, inner_smul_left, map_inv₀, conj_trivial,
    PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, one_mul]
  have e : (stepLen ε K k / √2) * (√2)⁻¹ = stepLen ε K k / 2 := by
    field_simp
    rw [Real.sq_sqrt zero_le_two]
  linear_combination (-(f₁' ε K (node (stepLen ε K) k + stepLen ε K k * (τ / √2)) +
          capSq' (height ε K k + (-1) ^ k * stepLen ε K k * (τ / √2) -
            mid ε K (node (stepLen ε K) k + stepLen ε K k * (τ / √2))) *
          ((-1) ^ k - mid' ε K (node (stepLen ε K) k + stepLen ε K k * (τ / √2))))) * e

/-- **The line searches find the first local minimizer** ([cartis2022evaluation] Lemma B.2.6, as
proved there). For admissible `ε` and `k < k_ε`, the step `√2` from `(x_k, y_k)` along
`-∇f(x_k, y_k)` is the first local minimizer of `τ ↦ f((x_k, y_k) - τ ∇f(x_k, y_k))`: the slope is
negative on `[0, √2)` and zero at `√2`. -/
theorem zigZag_isFirstLocalLineMin (h : IsAdmissible ε K) {k : ℕ} (hk : k < K) :
    LineSearch.IsFirstLocalLineMin (zigZagFunction ε K) (zigZagIterate ε K k) √2 := by
  obtain ⟨hg, -, hstep⟩ := zigZag_gradient h hk.le
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.2 two_pos
  have ha : 0 < stepLen ε K k := h.stepLen_pos hk.le
  refine ⟨hs, ?_, fun τ hτ => ?_⟩
  · rw [← hstep, (zigZag_gradient h (Nat.succ_le_of_lt hk)).1, hg]
    simp only [Nat.succ_eq_add_one, pow_succ, mul_neg, mul_one, neg_smul, inner_neg_right,
      inner_smul_right, inner_neg_left, inner_smul_left, map_div₀, conj_trivial, PiLp.inner_apply,
      RCLike.inner_apply, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, neg_neg, mul_eq_zero, div_eq_zero_iff, Nat.ofNat_nonneg,
      Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, or_false]
    right; right
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  · have ht0 : 0 ≤ τ / √2 := div_nonneg hτ.1 hs.le
    have ht1 : τ / √2 < 1 := by rw [div_lt_one hs]; exact hτ.2
    rw [zigZag_inner_gradient_ray h hk.le]
    exact mul_pos_of_neg_of_neg (by linarith) (slope_neg h hk ht0 ht1)

/-- **The line searches are exact** ([cartis2022evaluation] Lemma B.2.6 and (2.2.26)). For
admissible `ε` and `k < k_ε`, the step `√2` is the first global minimizer of
`τ ↦ f((x_k, y_k) - τ ∇f(x_k, y_k))` on `[0, ∞)`: the function decreases strictly on `[0, √2]`
(the slope (B.2.32) is negative there) and is nondecreasing on `[√2, ∞)`, where the iterate leaves
the corridor and the capped square grows faster than `f₁` decreases. -/
theorem zigZag_isExactLineMin (h : IsAdmissible ε K) {k : ℕ} (hk : k < K) :
    LineSearch.IsExactLineMin (zigZagFunction ε K) (zigZagIterate ε K k) √2 := by
  have hfirst := zigZag_isFirstLocalLineMin h hk
  have hf := differentiable_zigZagFunction h
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.2 two_pos
  have ha : 0 < stepLen ε K k := h.stepLen_pos hk.le
  have hd := LineSearch.hasDerivAt_lineFun hf (zigZagIterate ε K k)
  set g := fun τ : ℝ => zigZagFunction ε K
    (zigZagIterate ε K k - τ • gradient (zigZagFunction ε K) (zigZagIterate ε K k)) with hg_def
  have hcont : Continuous g := continuous_iff_continuousAt.2 fun τ => (hd τ).continuousAt
  have hanti : StrictAntiOn g (Icc 0 √2) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 √2) hcont.continuousOn fun τ hτ => ?_
    rw [interior_Icc] at hτ
    rw [(hd τ).deriv]
    exact neg_neg_of_pos (hfirst.2.2 τ ⟨hτ.1.le, hτ.2⟩)
  have hmono : MonotoneOn g (Ici √2) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici √2) hcont.continuousOn
      (fun τ _ => (hd τ).differentiableAt.differentiableWithinAt) fun τ hτ => ?_
    rw [interior_Ici] at hτ
    rw [(hd τ).deriv, zigZag_inner_gradient_ray h hk.le]
    have hσ : 0 ≤ stepLen ε K k * (τ / √2 - 1) :=
      mul_nonneg ha.le (by rw [sub_nonneg, le_div_iff₀ hs, one_mul]; exact hτ.le)
    have hX : node (stepLen ε K) k + stepLen ε K k * (τ / √2) =
        node (stepLen ε K) (k + 1) + stepLen ε K k * (τ / √2 - 1) := by
      rw [node_succ]; ring
    have hY : height ε K k + (-1) ^ k * stepLen ε K k * (τ / √2) =
        height ε K (k + 1) + (-1) ^ k * (stepLen ε K k * (τ / √2 - 1)) := by
      rw [height_succ]; ring
    rw [hX, hY]
    have := slope_nonneg h hk hσ
    nlinarith
  refine ⟨⟨hs.le, fun τ hτ => ?_⟩, fun τ hτ => hanti ⟨hτ.1, hτ.2.le⟩ ⟨hs.le, le_rfl⟩ hτ.2⟩
  rcases le_total τ √2 with h1 | h1
  · exact hanti.antitoneOn ⟨hτ, h1⟩ ⟨hs.le, le_rfl⟩ h1
  · exact hmono (mem_Ici.2 le_rfl) (mem_Ici.2 h1) h1

end Optimization
