import Mathlib.NumberTheory.Real.GoldenRatio
import Numlib.Approximation.DividedDifference
import Numlib.Nonlinear.Bisection
import Numlib.Nonlinear.ScalarNewton

/-!
# The chord, secant, regula falsi and Muller methods

The derivative-free one-dimensional rootfinders that replace `f'(x_k)` in Newton's step by a slope
`q_k` ([quarteroni2000numerical] §6.2.2, §6.3.1, §6.4.3; [kress1998numerical] §6.2;
[isaacson1994analysis] §3.3): the chord method (`q_k = q` fixed; namespace `Chord`), the secant
method (`q_k` the difference quotient over the last two iterates; `Secant`), regula falsi (the
difference quotient over the last two iterates bracketing the root; `RegulaFalsi`) and Muller's
method (the zero of the quadratic interpolant through the last three iterates; `Muller`).

The secant and regula falsi iterations carry state (a pair of points), so they are `step` functions
on `ℝ × ℝ` with `iterate f x₋₁ x₀ k` reading off the `k`-th point, as `Numlib/Nonlinear/Bisection`
does with brackets. Lean's `a / 0 = 0` makes a secant step with `f x_k = f x_{k-1}` stall at `x_k`;
the theorems assume what excludes it.

## The secant error analysis

The whole analysis rests on the divided-difference identity
`x_{k+1} - α = (x_k - α)(x_{k-1} - α) f[x_{k-1}, x_k, α] / f[x_{k-1}, x_k]`
(`Secant.sub_root_eq_mul_newton`), an algebraic identity in the values of `f` with
`DividedDifference.newton` of `Numlib/Approximation/DividedDifference` — the interpolation-error
formula `DividedDifference.sub_eval_interpolate_eq_newton` of the secant line at the node `α`.
Near a simple root of a `C²` function the first divided difference is bounded away from `0` and
the second is bounded (`exists_ball_bounds`), both by the mean value inequality
(`exists_ball_abs_slope_sub_deriv_le`) — for the second one through the identity
`f[x, y, α] = g[x, y]` with `g = dslope f α`, which is `C¹` by Hadamard's lemma
(`Numlib/Analysis/Calculus/RootMultiplicity`). The two-sided bound
`c |e_k| |e_{k-1}| ≤ |e_{k+1}| ≤ C |e_k| |e_{k-1}|` then gives local convergence
(`exists_ball_tendsto_iterate`, through the Fibonacci decay `E_k ≤ θ^{F_{k+1}}`) and, when
`f''(α) ≠ 0`, the order `(1 + √5) / 2` (`exists_ball_convergesWithOrder_goldenRatio`,
[quarteroni2000numerical] Property 6.2): in logarithmic variables `s_k = log(|e_{k+1}| / |e_k|^φ)`
the two bounds combine into the linear recursion `s_{k+2} ≤ log A + θ s_k` with `θ = 1 - 1/φ < 1`,
whose solutions are bounded above ([isaacson1994analysis] pp. 99–101, in the bound form rather
than the limit form). The hypothesis `f'(α) ≠ 0`, missing from the book's Property 6.2, is needed:
at a multiple root the secant method is only linear.

Chord convergence is the scalar Ostrowski theorem (`Numlib/Nonlinear/FixedPoint`) applied to
`φ_chord = x - f x / q`; it is the `𝕜 = ℝ` case of `Newton.chordStep` (`Chord.step_eq_chordStep`).
Muller's method is a definition only, in real arithmetic; its order `p ≈ 1.84` is not formalized.

## Regula falsi

Regula falsi needs no differentiability at all: `RegulaFalsi.tendsto_iterate` derives convergence
from continuity on the starting interval, a bracketing pair and the *uniqueness* of the zero
there. The brackets are nested (`RegulaFalsi.state_mem_uIcc`), so their two ends converge to
`l ≤ r`; the secant points, written symmetrically as chord zeros (`RegulaFalsi.chord`,
`RegulaFalsi.chord_comm`), converge to the chord zero of `(l, f l)` and `(r, f r)`, which is a
convex combination of `l` and `r` and at the same time an end of the limiting bracket, hence `l`
or `r`, with the corresponding value of `f` vanishing. Its linear *order*
(`RegulaFalsi.convergesWithOrder_one_iterate`) needs `f` twice continuously differentiable at
the root with `f'(α) ≠ 0`, but no convexity and no identification of the endpoint that is
eventually frozen: the two divided differences of the secant error identity are bounded
*uniformly over the bracket*, from below by the minimum of `|dslope f α|` on it and from above
by splitting on whether the two points of the bracket are close together or far apart.
-/

open Filter Topology Set

namespace DividedDifference

-- TODO(orchestrator): the three explicit formulas below belong in
-- `Numlib/Approximation/DividedDifference`, beside `newton_pair`.

variable (f : ℝ → ℝ) {x y z : ℝ}

/-- The Newton divided difference at two nodes, explicitly: `f[x, y] = (f y - f x) / (y - x)`. -/
theorem newton_two_eq (hxy : x ≠ y) : newton f ![x, y] = (f y - f x) / (y - x) := by
  have hne : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  rw [newton, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (Finset.univ.erase (0 : Fin 2)) = {1} from rfl,
    show (Finset.univ.erase (1 : Fin 2)) = {0} from rfl]
  simp only [Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

/-- The Newton divided difference at three nodes, explicitly. -/
theorem newton_three_eq :
    newton f ![x, y, z] = f x / ((x - y) * (x - z)) + f y / ((y - x) * (y - z)) +
      f z / ((z - x) * (z - y)) := by
  rw [newton, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [show (Finset.univ.erase (0 : Fin 3)) = {1, 2} from rfl,
    show (Finset.univ.erase (1 : Fin 3)) = {0, 2} from rfl,
    show (Finset.univ.erase (2 : Fin 3)) = {0, 1} from rfl]
  simp

/-- **A divided difference through a node `a` is a divided difference of `dslope f a`**:
`f[x, y, a] = g[x, y]` with `g = dslope f a`, for distinct `x, y, a`. This is the recursive
definition of divided differences read with `a` as the first node. -/
theorem newton_three_eq_newton_two_dslope (a : ℝ) (hxy : x ≠ y) (hxa : x ≠ a) (hya : y ≠ a) :
    newton f ![x, y, a] = newton (dslope f a) ![x, y] := by
  rw [newton_three_eq, newton_two_eq _ hxy, dslope_of_ne f hxa, dslope_of_ne f hya,
    slope_def_field, slope_def_field]
  have h1 : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h2 : x - a ≠ 0 := sub_ne_zero.2 hxa
  have h3 : y - a ≠ 0 := sub_ne_zero.2 hya
  have h4 : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have h5 : a - x ≠ 0 := sub_ne_zero.2 hxa.symm
  have h6 : a - y ≠ 0 := sub_ne_zero.2 hya.symm
  field_simp
  ring

end DividedDifference

section MeanValue

-- TODO(orchestrator): a general fact about `C¹` functions; natural home `Numlib/Analysis/Calculus`.

/-- **Difference quotients of a `C¹` function are close to its derivative** near a point: for every
`ε > 0` there is a ball around `a` on which `|(h y - h x) / (y - x) - h'(a)| ≤ ε` for all `x ≠ y`.
The mean value inequality for `h - h'(a) · id`, whose derivative is small on the ball. -/
theorem exists_ball_abs_slope_sub_deriv_le {h : ℝ → ℝ} {a : ℝ} (hh : ContDiffAt ℝ 1 h a) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ x ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ, x ≠ y →
      |(h y - h x) / (y - x) - deriv h a| ≤ ε := by
  have hd := hh.eventually_hasDerivAt
  have hc := hh.continuousAt_deriv.eventually (Metric.closedBall_mem_nhds (deriv h a) hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hd.and hc)
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have hne : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have key : ‖(h y - deriv h a * y) - (h x - deriv h a * x)‖ ≤ ε * ‖y - x‖ := by
    refine (convex_ball a δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun z => h z - deriv h a * z) (f' := fun z => deriv h z - deriv h a)
      (fun z hz => ?_) (fun z hz => ?_) hx hy
    · exact ((hball (Metric.mem_ball.1 hz)).1.sub ((hasDerivAt_id z).const_mul _)).hasDerivWithinAt
        |>.congr_deriv (by ring)
    · have := (hball (Metric.mem_ball.1 hz)).2
      rwa [dist_eq_norm] at this
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at key
  rw [show (h y - h x) / (y - x) - deriv h a =
      ((h y - deriv h a * y) - (h x - deriv h a * x)) / (y - x) by field_simp; ring, abs_div,
    div_le_iff₀ (abs_pos.2 hne)]
  exact key

end MeanValue

namespace Chord

variable {f : ℝ → ℝ} {q : ℝ}

/-- One step of the **chord method** with fixed slope `q`, `x ↦ x - f x / q`
([quarteroni2000numerical] (6.12), where the book's slope is `q = (f b - f a) / (b - a)`). -/
noncomputable def step (f : ℝ → ℝ) (q : ℝ) (x : ℝ) : ℝ := x - f x / q

/-- The scalar chord method is the Banach-space chord method `Newton.chordStep` of
`Numlib/Nonlinear/Newton` with the frozen derivative `A : ℝ ≃L[ℝ] ℝ`, `A 1 = q` (multiplication by
`q`): `A.symm y = y / q`. Through this identity `Newton.tendsto_chordIterate` applies to the scalar
chord method. -/
theorem step_eq_chordStep (A : ℝ ≃L[ℝ] ℝ) (hA : A 1 = q) (x : ℝ) :
    step f q x = Newton.chordStep f A x := by
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hA
  have hAy : ∀ y : ℝ, A y = y * q := fun y => by
    conv_lhs => rw [← mul_one y, ← smul_eq_mul, A.map_smul, hA, smul_eq_mul]
  unfold step Newton.chordStep
  congr 1
  symm
  rw [A.symm_apply_eq, hAy, div_mul_cancel₀ _ hq]

/-- The derivative of the chord iteration function: `HasDerivAt f f' x` gives
`φ_chord'(x) = 1 - f' / q`; at a root `α`, `φ_chord'(α) = 1 - f'(α) / q`, which is `1` when
`f'(α) = 0` ([quarteroni2000numerical] §6.3.1). -/
theorem hasDerivAt_step {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (step f q) (1 - f' / q) x :=
  (hasDerivAt_id x).sub (hf.div_const q)

/-- The local convergence condition of the chord method in the book's form: `|1 - f' / q| < 1`
iff `0 < f' / q < 2`, i.e. `q` has the sign of `f'` and `|q| > |f'| / 2`
([quarteroni2000numerical] §6.3.1). -/
theorem abs_one_sub_div_lt_one_iff {f' q : ℝ} : |1 - f' / q| < 1 ↔ 0 < f' / q ∧ f' / q < 2 := by
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- **Local linear convergence of the chord method** ([quarteroni2000numerical] §6.3.1): if
`f α = 0`, `f` is differentiable at `α` and `0 < f'(α) / q < 2`, then every orbit of
`x ↦ x - f x / q` started close enough to `α` converges to `α`. Ostrowski's theorem
(`tendsto_iterate_of_abs_deriv_lt_one`) for `φ_chord`, whose derivative at `α` is
`1 - f'(α) / q`. -/
theorem tendsto_iterate {α f' : ℝ} (hα : f α = 0) (hf : HasDerivAt f f' α) (h0 : 0 < f' / q)
    (h2 : f' / q < 2) :
    ∃ δ > 0, ∀ x₀, |x₀ - α| < δ → Tendsto (fun k => (step f q)^[k] x₀) atTop (𝓝 α) :=
  tendsto_iterate_of_abs_deriv_lt_one (by simp [step, hα]) (hasDerivAt_step hf)
    (abs_one_sub_div_lt_one_iff.2 ⟨h0, h2⟩)

/-- **The error ratios of the chord method** tend to `1 - f'(α) / q` along a convergent orbit
avoiding `α` ((6.18) of [quarteroni2000numerical] Theorem 6.1 for `φ_chord`): linear convergence
with factor `|1 - f'(α) / q|`, and the "lucky case" `f'(α) = q` of superlinear convergence. -/
theorem tendsto_sub_div_sub {α f' : ℝ} (hα : f α = 0) (hf : HasDerivAt f f' α) {x : ℕ → ℝ}
    (hx : ∀ k, x (k + 1) = step f q (x k)) (hne : ∀ k, x k ≠ α) (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 (1 - f' / q)) :=
  tendsto_sub_div_sub_of_hasDerivAt (hasDerivAt_step hf) (by simp [step, hα]) hx hne hlim

end Chord

namespace Secant

variable {f : ℝ → ℝ} {α : ℝ}

/-- One secant step on the pair `(x_{k-1}, x_k)`: the new pair is `(x_k, x_{k+1})` with
`x_{k+1} = x_k - (x_k - x_{k-1}) / (f x_k - f x_{k-1}) * f x_k` ([quarteroni2000numerical] (6.14)).
When `f x_k = f x_{k-1}` Lean's `a / 0 = 0` makes the step stall at `x_k`. -/
noncomputable def step (f : ℝ → ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.2, s.2 - (s.2 - s.1) / (f s.2 - f s.1) * f s.2)

/-- The secant iterates: `iterate f xm1 x₀ k = x_k`, with `x_{-1} = xm1`, `x_0 = x₀` the two
initial values. -/
noncomputable def iterate (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) : ℝ :=
  ((step f)^[k] (xm1, x₀)).2

/-- The secant iterate of index `0` is the initial value `x₀`. -/
@[simp]
theorem iterate_zero (f : ℝ → ℝ) (xm1 x₀ : ℝ) : iterate f xm1 x₀ 0 = x₀ := rfl

/-- The first component of the `(k+1)`-st pair is the `k`-th iterate: the pairs are
`(x_{k-1}, x_k)`. -/
theorem fst_iterate_succ (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) :
    ((step f)^[k + 1] (xm1, x₀)).1 = iterate f xm1 x₀ k := by
  rw [Function.iterate_succ_apply']
  rfl

/-- **The secant recurrence** ([quarteroni2000numerical] (6.14)) in terms of the pair
`(x_{k-1}, x_k) = (step f)^[k] (xm1, x₀)`. -/
theorem iterate_succ (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) :
    iterate f xm1 x₀ (k + 1) = ((step f)^[k] (xm1, x₀)).2 -
      (((step f)^[k] (xm1, x₀)).2 - ((step f)^[k] (xm1, x₀)).1) /
        (f ((step f)^[k] (xm1, x₀)).2 - f ((step f)^[k] (xm1, x₀)).1) *
        f ((step f)^[k] (xm1, x₀)).2 := by
  simp [iterate, Function.iterate_succ_apply', step]

/-- The first secant iterate from the two initial values. -/
theorem iterate_one (f : ℝ → ℝ) (xm1 x₀ : ℝ) :
    iterate f xm1 x₀ 1 = x₀ - (x₀ - xm1) / (f x₀ - f xm1) * f x₀ :=
  iterate_succ f xm1 x₀ 0

/-- **The secant recurrence in terms of the iterates** ([quarteroni2000numerical] (6.14)):
`x_{k+2} = x_{k+1} - (x_{k+1} - x_k) / (f x_{k+1} - f x_k) * f x_{k+1}`. -/
theorem iterate_add_two (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) :
    iterate f xm1 x₀ (k + 2) = iterate f xm1 x₀ (k + 1) -
      (iterate f xm1 x₀ (k + 1) - iterate f xm1 x₀ k) /
        (f (iterate f xm1 x₀ (k + 1)) - f (iterate f xm1 x₀ k)) * f (iterate f xm1 x₀ (k + 1)) := by
  rw [iterate_succ f xm1 x₀ (k + 1), fst_iterate_succ]
  rfl

/-- **The secant error identity.** For a root `α` of `f` and distinct `x, y`, both different from
`α`, with `f x ≠ f y`, the new iterate `z = y - (y - x) / (f y - f x) * f y` satisfies
`z - α = (y - α) (x - α) f[x, y, α] / f[x, y]`. It is the divided-difference form of the error of
the secant line (the interpolant of `f` at `x, y`) at the node `α`, and needs no smoothness: an
algebraic identity in the values `f x, f y` and `f α = 0`. -/
theorem sub_root_eq_mul_newton (hα : f α = 0) {x y : ℝ} (hxy : x ≠ y) (hxα : x ≠ α)
    (hyα : y ≠ α) (hf : f x ≠ f y) :
    (y - (y - x) / (f y - f x) * f y) - α =
      (y - α) * (x - α) * DividedDifference.newton f ![x, y, α] /
        DividedDifference.newton f ![x, y] := by
  rw [DividedDifference.newton_three_eq, DividedDifference.newton_two_eq _ hxy, hα]
  have h1 : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h2 : x - α ≠ 0 := sub_ne_zero.2 hxα
  have h3 : y - α ≠ 0 := sub_ne_zero.2 hyα
  have h4 : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have h5 : f y - f x ≠ 0 := sub_ne_zero.2 hf.symm
  field_simp
  ring

/-- **The upper error bound of a secant step.** Under the hypotheses of `sub_root_eq_mul_newton`,
if `0 < m₁ ≤ |f[x, y]|` and `|f[x, y, α]| ≤ M₂`, then `|z - α| ≤ (M₂ / m₁) |y - α| |x - α|`. -/
theorem abs_sub_root_le (hα : f α = 0) {x y m₁ M₂ : ℝ} (hxy : x ≠ y) (hxα : x ≠ α) (hyα : y ≠ α)
    (hm : 0 < m₁) (h1 : m₁ ≤ |DividedDifference.newton f ![x, y]|)
    (h2 : |DividedDifference.newton f ![x, y, α]| ≤ M₂) :
    |(y - (y - x) / (f y - f x) * f y) - α| ≤ M₂ / m₁ * (|y - α| * |x - α|) := by
  have hf : f x ≠ f y := by
    intro h
    rw [DividedDifference.newton_two_eq _ hxy, h, sub_self, zero_div, abs_zero] at h1
    exact absurd h1 (not_le.2 hm)
  rw [sub_root_eq_mul_newton hα hxy hxα hyα hf, abs_div, abs_mul, abs_mul,
    div_le_iff₀ (lt_of_lt_of_le hm h1)]
  calc |y - α| * |x - α| * |DividedDifference.newton f ![x, y, α]|
      ≤ |y - α| * |x - α| * M₂ := by gcongr
    _ = M₂ / m₁ * (|y - α| * |x - α|) * m₁ := by field_simp
    _ ≤ M₂ / m₁ * (|y - α| * |x - α|) * |DividedDifference.newton f ![x, y]| := by
        gcongr
        have : 0 ≤ M₂ := le_trans (abs_nonneg _) h2
        positivity

/-- **The lower error bound of a secant step.** Under the hypotheses of `sub_root_eq_mul_newton`,
if `|f[x, y]| ≤ M₁` with `0 < M₁` and `m₂ ≤ |f[x, y, α]|`, then
`(m₂ / M₁) |y - α| |x - α| ≤ |z - α|`. With `0 < m₂` this makes `z ≠ α`. -/
theorem le_abs_sub_root (hα : f α = 0) {x y M₁ m₂ : ℝ} (hxy : x ≠ y) (hxα : x ≠ α) (hyα : y ≠ α)
    (hf : f x ≠ f y) (hM : 0 < M₁) (h1 : |DividedDifference.newton f ![x, y]| ≤ M₁)
    (h2 : m₂ ≤ |DividedDifference.newton f ![x, y, α]|) :
    m₂ / M₁ * (|y - α| * |x - α|) ≤ |(y - (y - x) / (f y - f x) * f y) - α| := by
  have hN : DividedDifference.newton f ![x, y] ≠ 0 := by
    rw [DividedDifference.newton_two_eq _ hxy]
    exact div_ne_zero (sub_ne_zero.2 hf.symm) (sub_ne_zero.2 hxy.symm)
  rw [sub_root_eq_mul_newton hα hxy hxα hyα hf, abs_div, abs_mul, abs_mul,
    le_div_iff₀ (abs_pos.2 hN)]
  rcases le_or_gt m₂ 0 with hm₂ | hm₂
  · calc m₂ / M₁ * (|y - α| * |x - α|) * |DividedDifference.newton f ![x, y]| ≤ 0 := by
          have : m₂ / M₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hm₂ hM.le
          have : 0 ≤ |y - α| * |x - α| * |DividedDifference.newton f ![x, y]| := by positivity
          nlinarith
      _ ≤ _ := by positivity
  · calc m₂ / M₁ * (|y - α| * |x - α|) * |DividedDifference.newton f ![x, y]|
        ≤ m₂ / M₁ * (|y - α| * |x - α|) * M₁ := by gcongr
      _ = |y - α| * |x - α| * m₂ := by field_simp
      _ ≤ |y - α| * |x - α| * |DividedDifference.newton f ![x, y, α]| := by gcongr

section Local

open DividedDifference

variable {ε m₁ M₁ m₂ M₂ : ℝ}

/-- **Local bounds on the divided differences near a simple root of a `C²` function.** If
`f'(α) ≠ 0` then, for every `η > 0`, on a ball around `α` the first divided difference at distinct
nodes satisfies `|f'(α)| / 2 ≤ |f[x, y]| ≤ 3 |f'(α)| / 2` and the second divided difference at
distinct nodes different from `α` satisfies `|f[x, y, α] - f''(α) / 2| ≤ η`. The first is
`exists_ball_abs_slope_sub_deriv_le` for `f`; the second is the same lemma for `g = dslope f α`,
which is `C¹` at `α` with `g'(α) = f''(α) / 2` by Hadamard's lemma, through
`f[x, y, α] = g[x, y]`. -/
theorem exists_ball_bounds (hf : ContDiffAt ℝ 2 f α) (hf' : deriv f α ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ Metric.ball α δ, ∀ y ∈ Metric.ball α δ, x ≠ y →
      (|deriv f α| / 2 ≤ |newton f ![x, y]| ∧ |newton f ![x, y]| ≤ 3 * |deriv f α| / 2) ∧
      (x ≠ α → y ≠ α → |newton f ![x, y, α] - iteratedDeriv 2 f α / 2| ≤ η) := by
  have hf1 : ContDiffAt ℝ 1 f α := hf.of_le (by norm_num)
  have hf2 : ContDiffAt ℝ (1 + 1 : ℕ) f α := by simpa using hf
  have hg : ContDiffAt ℝ 1 (dslope f α) α := ContDiffAt.dslope_same (n := 1) hf2
  have hg' : deriv (dslope f α) α = iteratedDeriv 2 f α / 2 := by
    rw [← iteratedDeriv_one, iteratedDeriv_dslope_same hf2,
      show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num]
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_ball_abs_slope_sub_deriv_le hf1 (half_pos (abs_pos.2 hf'))
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_ball_abs_slope_sub_deriv_le hg hη
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx y hy hxy => ⟨?_, fun hxα hyα => ?_⟩⟩
  · have hx' := Metric.ball_subset_ball (min_le_left δ₁ δ₂) hx
    have hy' := Metric.ball_subset_ball (min_le_left δ₁ δ₂) hy
    have := h₁ x hx' y hy' hxy
    rw [newton_two_eq _ hxy]
    have h1 := abs_sub_abs_le_abs_sub ((f y - f x) / (y - x)) (deriv f α)
    have h2 := abs_sub_abs_le_abs_sub (deriv f α) ((f y - f x) / (y - x))
    rw [abs_sub_comm] at h2
    constructor <;> linarith
  · have hx' := Metric.ball_subset_ball (min_le_right δ₁ δ₂) hx
    have hy' := Metric.ball_subset_ball (min_le_right δ₁ δ₂) hy
    have := h₂ x hx' y hy' hxy
    rwa [newton_three_eq_newton_two_dslope _ α hxy hxα hyα, newton_two_eq _ hxy, ← hg']

/-- **The local bounds driving the secant analysis** on `ball α ε`: the first divided difference at
distinct nodes lies in `[m₁, M₁]` in absolute value, and the second divided difference through
`α` at distinct nodes different from `α` lies in `[m₂, M₂]`. `exists_localBounds` produces them
near a simple root of a `C²` function. -/
structure LocalBounds (f : ℝ → ℝ) (α ε m₁ M₁ m₂ M₂ : ℝ) : Prop where
  /-- The two-sided bound on `|f[x, y]|`. -/
  two : ∀ x ∈ Metric.ball α ε, ∀ y ∈ Metric.ball α ε, x ≠ y →
    m₁ ≤ |newton f ![x, y]| ∧ |newton f ![x, y]| ≤ M₁
  /-- The two-sided bound on `|f[x, y, α]|`. -/
  three : ∀ x ∈ Metric.ball α ε, ∀ y ∈ Metric.ball α ε, x ≠ y → x ≠ α → y ≠ α →
    m₂ ≤ |newton f ![x, y, α]| ∧ |newton f ![x, y, α]| ≤ M₂

/-- Local bounds persist on a smaller ball. -/
theorem LocalBounds.mono (hb : LocalBounds f α ε m₁ M₁ m₂ M₂) {ε' : ℝ} (h : ε' ≤ ε) :
    LocalBounds f α ε' m₁ M₁ m₂ M₂ :=
  ⟨fun x hx y hy => hb.two x (Metric.ball_subset_ball h hx) y (Metric.ball_subset_ball h hy),
    fun x hx y hy => hb.three x (Metric.ball_subset_ball h hx) y (Metric.ball_subset_ball h hy)⟩

/-- Near a simple root of a `C²` function, for every `η > 0` there are local bounds with
`m₁ = |f'(α)| / 2`, `M₁ = 3 |f'(α)| / 2`, `m₂ = |f''(α)| / 2 - η` and `M₂ = |f''(α)| / 2 + η`;
`m₂ > 0` when `f''(α) ≠ 0` and `η < |f''(α)| / 2`. -/
theorem exists_localBounds (hf : ContDiffAt ℝ 2 f α) (hf' : deriv f α ≠ 0) {η : ℝ}
    (hη : 0 < η) :
    ∃ ε > 0, LocalBounds f α ε (|deriv f α| / 2) (3 * |deriv f α| / 2)
      (|iteratedDeriv 2 f α| / 2 - η) (|iteratedDeriv 2 f α| / 2 + η) := by
  obtain ⟨δ, hδ, h⟩ := exists_ball_bounds hf hf' hη
  refine ⟨δ, hδ, fun x hx y hy hxy => (h x hx y hy hxy).1, fun x hx y hy hxy hxα hyα => ?_⟩
  have := (h x hx y hy hxy).2 hxα hyα
  have h1 := abs_sub_abs_le_abs_sub (newton f ![x, y, α]) (iteratedDeriv 2 f α / 2)
  have h2 := abs_sub_abs_le_abs_sub (iteratedDeriv 2 f α / 2) (newton f ![x, y, α])
  rw [abs_sub_comm] at h2
  rw [abs_div, abs_two] at h1 h2
  constructor <;> linarith

/-- A pair `(x_{k-1}, x_k)` of consecutive secant iterates is **admissible** in `ball α ε` when
both points lie in the ball, are distinct, and differ from `α`: exactly what the error identity
`sub_root_eq_mul_newton` needs. A start equal to `α` stops the method at once, and two equal
starts make the step stall. -/
structure IsAdmissible (α ε : ℝ) (s : ℝ × ℝ) : Prop where
  /-- The older point is in the ball. -/
  fst_mem : s.1 ∈ Metric.ball α ε
  /-- The newer point is in the ball. -/
  snd_mem : s.2 ∈ Metric.ball α ε
  /-- The two points are distinct. -/
  ne : s.1 ≠ s.2
  /-- The older point is not the root. -/
  fst_ne : s.1 ≠ α
  /-- The newer point is not the root. -/
  snd_ne : s.2 ≠ α

/-- The last iterate of an admissible pair is not a root of `f` when `f` is injective on the ball
in the sense of the lower bound `0 < m₁ ≤ |f[x, y]|`. -/
theorem LocalBounds.apply_ne_zero (hα : f α = 0) (hb : LocalBounds f α ε m₁ M₁ m₂ M₂)
    (hε : 0 < ε) (hm₁ : 0 < m₁) {v : ℝ} (hv : v ∈ Metric.ball α ε) (hvα : v ≠ α) : f v ≠ 0 := by
  intro h0
  have := (hb.two α (Metric.mem_ball_self hε) v hv hvα.symm).1
  rw [newton_two_eq _ hvα.symm, h0, hα, sub_self, zero_div, abs_zero] at this
  exact absurd this (not_le.2 hm₁)

/-- **One secant step from an admissible pair.** Under local bounds with `0 < m₁`, `0 < M₁` and
`(M₂ / m₁) ε ≤ 1`, the new point `w = (step f s).2` satisfies the two-sided error bound
`(m₂ / M₁) |v - α| |u - α| ≤ |w - α| ≤ (M₂ / m₁) |v - α| |u - α|`, lies in the ball, and differs
from `v`. It differs from `α` too when `0 < m₂` (`LocalBounds.isAdmissible_step`). -/
theorem LocalBounds.step_bounds (hα : f α = 0) (hb : LocalBounds f α ε m₁ M₁ m₂ M₂) (hε : 0 < ε)
    (hm₁ : 0 < m₁) (hM₁ : 0 < M₁) (hCε : M₂ / m₁ * ε ≤ 1) {s : ℝ × ℝ}
    (hs : IsAdmissible α ε s) :
    m₂ / M₁ * (|s.2 - α| * |s.1 - α|) ≤ |(step f s).2 - α| ∧
      |(step f s).2 - α| ≤ M₂ / m₁ * (|s.2 - α| * |s.1 - α|) ∧
      (step f s).2 ∈ Metric.ball α ε ∧ (step f s).2 ≠ s.2 := by
  obtain ⟨hu, hv, huv, huα, hvα⟩ := hs
  obtain ⟨h1, h1'⟩ := hb.two _ hu _ hv huv
  obtain ⟨h2, h2'⟩ := hb.three _ hu _ hv huv huα hvα
  have hf : f s.1 ≠ f s.2 := by
    intro h
    rw [newton_two_eq _ huv, h, sub_self, zero_div, abs_zero] at h1
    exact absurd h1 (not_le.2 hm₁)
  have hupper := abs_sub_root_le hα huv huα hvα hm₁ h1 h2'
  have hlower := le_abs_sub_root hα huv huα hvα hf hM₁ h1' h2
  have hM₂ : 0 ≤ M₂ := (abs_nonneg _).trans h2'
  refine ⟨hlower, hupper, ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq]
    have hv' : |s.2 - α| ≤ ε := by rw [← Real.dist_eq]; exact (Metric.mem_ball.1 hv).le
    have hu' : |s.1 - α| < ε := by rw [← Real.dist_eq]; exact Metric.mem_ball.1 hu
    calc |(step f s).2 - α| ≤ M₂ / m₁ * (|s.2 - α| * |s.1 - α|) := hupper
      _ ≤ M₂ / m₁ * (ε * |s.1 - α|) := by gcongr
      _ = M₂ / m₁ * ε * |s.1 - α| := by ring
      _ ≤ 1 * |s.1 - α| := by gcongr
      _ < ε := by rw [one_mul]; exact hu'
  · have hfv : f s.2 ≠ 0 := hb.apply_ne_zero hα hε hm₁ hv hvα
    simp only [step]
    intro h
    rw [sub_eq_self, mul_eq_zero, div_eq_zero_iff, sub_eq_zero, sub_eq_zero] at h
    rcases h with (h | h) | h
    · exact huv h.symm
    · exact hf h.symm
    · exact hfv h

/-- After a secant step from an admissible pair, the new pair is admissible iff the new point is
not the root. -/
theorem LocalBounds.isAdmissible_step_iff (hα : f α = 0) (hb : LocalBounds f α ε m₁ M₁ m₂ M₂)
    (hε : 0 < ε) (hm₁ : 0 < m₁) (hM₁ : 0 < M₁) (hCε : M₂ / m₁ * ε ≤ 1) {s : ℝ × ℝ}
    (hs : IsAdmissible α ε s) : IsAdmissible α ε (step f s) ↔ (step f s).2 ≠ α := by
  obtain ⟨-, -, hmem, hne⟩ := hb.step_bounds hα hε hm₁ hM₁ hCε hs
  exact ⟨fun h => h.snd_ne, fun h => ⟨hs.snd_mem, hmem, hne.symm, hs.snd_ne, h⟩⟩

/-- With `0 < m₂` (the second divided difference bounded away from `0`, as near a root with
`f''(α) ≠ 0`), admissibility is preserved by the secant step. -/
theorem LocalBounds.isAdmissible_step (hα : f α = 0) (hb : LocalBounds f α ε m₁ M₁ m₂ M₂)
    (hε : 0 < ε) (hm₁ : 0 < m₁) (hM₁ : 0 < M₁) (hm₂ : 0 < m₂) (hCε : M₂ / m₁ * ε ≤ 1)
    {s : ℝ × ℝ} (hs : IsAdmissible α ε s) : IsAdmissible α ε (step f s) := by
  rw [hb.isAdmissible_step_iff hα hε hm₁ hM₁ hCε hs]
  obtain ⟨hlower, -, -, -⟩ := hb.step_bounds hα hε hm₁ hM₁ hCε hs
  intro h
  rw [h, sub_self, abs_zero] at hlower
  have : 0 < m₂ / M₁ * (|s.2 - α| * |s.1 - α|) := by
    have := abs_pos.2 (sub_ne_zero.2 hs.snd_ne)
    have := abs_pos.2 (sub_ne_zero.2 hs.fst_ne)
    positivity
  linarith

/-- Once an iterate is the root, all later ones are: `f α = 0` makes the step stall at `α`. -/
theorem snd_step_eq_of_snd_eq (hα : f α = 0) {s : ℝ × ℝ} (h : s.2 = α) : (step f s).2 = α := by
  simp [step, h, hα]

end Local

section Sequences

/-- **Fibonacci decay.** If `0 ≤ E k`, `E 0, E 1 ≤ θ < 1` and `E (k+2) ≤ E (k+1) E k`, then
`E k ≤ θ ^ fib (k+1)` and so `E k → 0`. This is how the upper bound
`|e_{k+1}| ≤ C |e_k| |e_{k-1}|` alone gives convergence of the secant method (an R-order, not yet
the order of Definition 6.1). -/
theorem tendsto_zero_of_le_mul {E : ℕ → ℝ} {θ : ℝ} (hE : ∀ k, 0 ≤ E k) (hθ : θ < 1)
    (h0 : E 0 ≤ θ) (h1 : E 1 ≤ θ) (hrec : ∀ k, E (k + 2) ≤ E (k + 1) * E k) :
    Tendsto E atTop (𝓝 0) := by
  have hθ0 : 0 ≤ θ := (hE 0).trans h0
  have hfib : ∀ k, E k ≤ θ ^ Nat.fib (k + 1) ∧ E (k + 1) ≤ θ ^ Nat.fib (k + 2) := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using h0, by simpa using h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      calc E (k + 1 + 1) ≤ E (k + 1) * E k := hrec k
        _ ≤ θ ^ Nat.fib (k + 2) * θ ^ Nat.fib (k + 1) :=
            mul_le_mul ih.2 ih.1 (hE k) (by positivity)
        _ = θ ^ Nat.fib (k + 1 + 2) := by
            rw [← pow_add, Nat.fib_add_two (n := k + 1), add_comm]
  have hlim : Tendsto (fun k => θ ^ Nat.fib (k + 1)) atTop (𝓝 0) := by
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ).comp ?_
    refine tendsto_atTop_atTop.2 fun b => ⟨b + 4, fun n hn => ?_⟩
    exact (by omega : b ≤ n + 1).trans (Nat.le_fib_self (by omega))
  exact squeeze_zero hE (fun k => (hfib k).1) hlim

/-- **The golden-ratio order from a two-sided product recursion.** If a positive sequence
satisfies `c e_{k+1} e_k ≤ e_{k+2} ≤ C e_{k+1} e_k` with `0 < c`, then
`e_{k+1} ≤ B e_k ^ φ` for all `k`, `φ = (1 + √5) / 2`. In the logarithmic variables
`u_k = log e_k` and `s_k = u_{k+1} - φ u_k`, the upper bound gives
`s_{k+2} ≤ log C + u_{k+1} - φ⁻¹ u_{k+2}` (since `1 - φ = -φ⁻¹`) and the lower bound turns this
into `s_{k+2} ≤ L + θ s_k` with `θ = 1 - φ⁻¹ ∈ (0, 1)` (since `φ θ = φ⁻¹`), a recursion whose
solutions stay below `max (L / (1 - θ)) (max s_0 s_1)`, `1 - θ = φ⁻¹`. [isaacson1994analysis]
pp. 99–101 give the limit form; this is the bound form the order of Definition 6.1 asks for. -/
theorem exists_le_mul_rpow_goldenRatio {e : ℕ → ℝ} {c C : ℝ} (hc : 0 < c) (hpos : ∀ k, 0 < e k)
    (hupper : ∀ k, e (k + 2) ≤ C * (e (k + 1) * e k))
    (hlower : ∀ k, c * (e (k + 1) * e k) ≤ e (k + 2)) :
    ∃ B > 0, ∀ k, e (k + 1) ≤ B * e k ^ Real.goldenRatio := by
  have hC : 0 < C := by
    by_contra hC
    push Not at hC
    have := mul_nonpos_of_nonpos_of_nonneg hC (mul_pos (hpos 1) (hpos 0)).le
    linarith [hupper 0, hpos 2]
  set φ := Real.goldenRatio with hφ
  have hφ1 : 1 < φ := Real.one_lt_goldenRatio
  have hφinv : φ⁻¹ = φ - 1 := by
    have h := Real.goldenRatio_sq
    field_simp
    nlinarith
  have hθ0 : 0 < 1 - φ⁻¹ := by rw [hφinv]; linarith [Real.goldenRatio_lt_two]
  have hθ1 : 1 - φ⁻¹ < 1 := by rw [hφinv]; linarith
  have hφθ : φ * (1 - φ⁻¹) = φ⁻¹ := by rw [hφinv]; nlinarith [Real.goldenRatio_sq]
  set u : ℕ → ℝ := fun k => Real.log (e k) with hu
  have hu_up : ∀ k, u (k + 2) ≤ Real.log C + (u (k + 1) + u k) := fun k => by
    have := Real.log_le_log (hpos _) (hupper k)
    rwa [Real.log_mul hC.ne' (mul_pos (hpos _) (hpos _)).ne',
      Real.log_mul (hpos _).ne' (hpos _).ne'] at this
  have hu_lo : ∀ k, Real.log c + (u (k + 1) + u k) ≤ u (k + 2) := fun k => by
    have := Real.log_le_log (mul_pos hc (mul_pos (hpos _) (hpos _))) (hlower k)
    rwa [Real.log_mul hc.ne' (mul_pos (hpos _) (hpos _)).ne',
      Real.log_mul (hpos _).ne' (hpos _).ne'] at this
  set s : ℕ → ℝ := fun k => u (k + 1) - φ * u k with hs
  set L : ℝ := Real.log C - φ⁻¹ * Real.log c with hL
  have hrec : ∀ k, s (k + 2) ≤ L + (1 - φ⁻¹) * s k := fun k => by
    have h1 := hu_up (k + 1)
    have h2 := mul_le_mul_of_nonneg_left (hu_lo k) (inv_pos.2 (zero_lt_one.trans hφ1)).le
    have h3 : φ * u (k + 2) = u (k + 2) + φ⁻¹ * u (k + 2) := by rw [hφinv]; ring
    have h4 : (1 - φ⁻¹) * (u (k + 1) - φ * u k) = u (k + 1) - φ⁻¹ * u (k + 1) - φ⁻¹ * u k := by
      rw [show (1 - φ⁻¹) * (u (k + 1) - φ * u k) = (1 - φ⁻¹) * u (k + 1) - φ * (1 - φ⁻¹) * u k
        by ring, hφθ]
      ring
    simp only [hs, hL]
    rw [h4]
    linarith
  set S : ℝ := max (L / φ⁻¹) (max (s 0) (s 1)) with hS
  have hbound : ∀ k, s k ≤ S ∧ s (k + 1) ≤ S := by
    intro k
    induction k with
    | zero => exact ⟨(le_max_left _ _).trans (le_max_right _ _),
        (le_max_right _ _).trans (le_max_right _ _)⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hLS : L ≤ φ⁻¹ * S := by
        have := le_max_left (L / φ⁻¹) (max (s 0) (s 1))
        rwa [div_le_iff₀ (inv_pos.2 (zero_lt_one.trans hφ1)), mul_comm] at this
      calc s (k + 1 + 1) ≤ L + (1 - φ⁻¹) * s k := hrec k
        _ ≤ L + (1 - φ⁻¹) * S := by gcongr; exact ih.1
        _ ≤ φ⁻¹ * S + (1 - φ⁻¹) * S := by gcongr
        _ = S := by ring
  refine ⟨Real.exp S, Real.exp_pos S, fun k => ?_⟩
  have hk : u (k + 1) ≤ S + φ * u k := by
    have := (hbound k).1
    simp only [hs] at this
    linarith
  calc e (k + 1) = Real.exp (u (k + 1)) := (Real.exp_log (hpos _)).symm
    _ ≤ Real.exp (S + φ * u k) := Real.exp_le_exp.2 hk
    _ = Real.exp S * e k ^ φ := by
        rw [Real.exp_add, Real.rpow_def_of_pos (hpos k), mul_comm (Real.log _)]

end Sequences

section Convergence

open DividedDifference

variable {ε m₁ M₁ m₂ M₂ xm1 x₀ : ℝ}

/-- The errors of the pair sequence: `E k = |((step f)^[k] (xm1, x₀)).1 - α|`, so that
`E 0 = |xm1 - α|` and `E (k + 1) = |iterate f xm1 x₀ k - α|`. -/
theorem abs_fst_iterate_succ_sub (f : ℝ → ℝ) (xm1 x₀ α : ℝ) (k : ℕ) :
    |((step f)^[k + 1] (xm1, x₀)).1 - α| = |iterate f xm1 x₀ k - α| := by
  rw [fst_iterate_succ]

/-- **Convergence from an admissible start under local bounds with `(M₂ / m₁) ε ≤ 1 / 2`.** Either
every pair stays admissible, and the Fibonacci decay of `E_k = (M₂ / m₁) |e_{k-1}|` gives
convergence, or some iterate is exactly the root and the method stays there. -/
theorem LocalBounds.tendsto_iterate (hα : f α = 0) (hb : LocalBounds f α ε m₁ M₁ m₂ M₂)
    (hε : 0 < ε) (hm₁ : 0 < m₁) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hCε : M₂ / m₁ * ε ≤ 1 / 2)
    (hs : IsAdmissible α ε (xm1, x₀)) :
    (∀ k, iterate f xm1 x₀ k ∈ Metric.ball α ε) ∧ Tendsto (iterate f xm1 x₀) atTop (𝓝 α) := by
  have hCε' : M₂ / m₁ * ε ≤ 1 := hCε.trans (by norm_num)
  have hC : 0 < M₂ / m₁ := div_pos hM₂ hm₁
  by_cases hall : ∀ k, IsAdmissible α ε ((step f)^[k] (xm1, x₀))
  · -- every pair admissible: Fibonacci decay
    set E : ℕ → ℝ := fun k => M₂ / m₁ * |((step f)^[k] (xm1, x₀)).1 - α| with hE
    have hE0 : ∀ k, 0 ≤ E k := fun k => by positivity
    have hEθ : ∀ k, E k ≤ 1 / 2 := fun k => by
      have hmem := (hall k).fst_mem
      rw [Metric.mem_ball, Real.dist_eq] at hmem
      calc E k ≤ M₂ / m₁ * ε := by simp only [hE]; gcongr
        _ ≤ 1 / 2 := hCε
    have hrec : ∀ k, E (k + 2) ≤ E (k + 1) * E k := fun k => by
      obtain ⟨-, hup, -, -⟩ := hb.step_bounds hα hε hm₁ hM₁ hCε' (hall k)
      simp only [hE, Function.iterate_succ_apply']
      calc M₂ / m₁ * |(step f (step f ((step f)^[k] (xm1, x₀)))).1 - α|
          = M₂ / m₁ * |(step f ((step f)^[k] (xm1, x₀))).2 - α| := rfl
        _ ≤ M₂ / m₁ * (M₂ / m₁ * (|((step f)^[k] (xm1, x₀)).2 - α| *
            |((step f)^[k] (xm1, x₀)).1 - α|)) := by gcongr
        _ = M₂ / m₁ * |(step f ((step f)^[k] (xm1, x₀))).1 - α| *
            (M₂ / m₁ * |((step f)^[k] (xm1, x₀)).1 - α|) := by
            simp only [step]; ring
    have hlim := tendsto_zero_of_le_mul hE0 (by norm_num) (hEθ 0) (hEθ 1) hrec
    refine ⟨fun k => (hall k).snd_mem, ?_⟩
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have := (hlim.comp (tendsto_add_atTop_nat 1)).const_mul (M₂ / m₁)⁻¹
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    simp only [Function.comp, hE, Real.norm_eq_abs, ← abs_fst_iterate_succ_sub f xm1 x₀ α k]
    field_simp
  · -- some pair is not admissible: the method has landed on the root
    classical
    push Not at hall
    have hk := Nat.find_spec hall
    have hmin : ∀ j < Nat.find hall, IsAdmissible α ε ((step f)^[j] (xm1, x₀)) := fun j hj =>
      not_not.1 (Nat.find_min hall hj)
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hall = j + 1 := by
      refine ⟨Nat.find hall - 1, (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 fun h => ?_)).symm⟩
      rw [h] at hk
      exact hk hs
    have hadm : IsAdmissible α ε ((step f)^[j] (xm1, x₀)) := hmin j (by omega)
    have hroot : ((step f)^[j + 1] (xm1, x₀)).2 = α := by
      rw [Function.iterate_succ_apply']
      by_contra h
      exact hk (by
        rw [hj, Function.iterate_succ_apply']
        exact (hb.isAdmissible_step_iff hα hε hm₁ hM₁ hCε' hadm).2 h)
    have hconst : ∀ i ≥ j + 1, iterate f xm1 x₀ i = α := by
      intro i hi
      obtain ⟨d, rfl⟩ : ∃ d, i = j + 1 + d := ⟨i - (j + 1), by omega⟩
      induction d with
      | zero => exact hroot
      | succ d ih =>
        rw [iterate, show j + 1 + (d + 1) = j + 1 + d + 1 by omega, Function.iterate_succ_apply']
        exact snd_step_eq_of_snd_eq hα (ih (by omega))
    refine ⟨fun i => ?_, tendsto_atTop_of_eventually_const hconst⟩
    rcases lt_or_ge i (j + 1) with hi | hi
    · exact (hmin i (by rw [hj]; omega)).snd_mem
    · rw [hconst i hi]
      exact Metric.mem_ball_self hε

/-- **Local convergence of the secant method** ([quarteroni2000numerical] §6.2.2): if `f α = 0`,
`f` is `C²` at `α` and `f'(α) ≠ 0`, then there is `ε > 0` such that from any two distinct
starting values in `(α - ε, α + ε)` different from `α` the secant iterates stay in the interval and
converge to `α`. The two "`≠ α`" hypotheses exclude the trivial case in which the method stops at
the root immediately; convergence holds there too, but the pair is not admissible. -/
theorem exists_ball_tendsto_iterate (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) :
    ∃ ε > 0, ∀ xm1 ∈ Metric.ball α ε, ∀ x₀ ∈ Metric.ball α ε, xm1 ≠ x₀ → xm1 ≠ α → x₀ ≠ α →
      (∀ k, iterate f xm1 x₀ k ∈ Metric.ball α ε) ∧ Tendsto (iterate f xm1 x₀) atTop (𝓝 α) := by
  obtain ⟨δ, hδ, hb⟩ := exists_localBounds hf hf' one_pos
  set m₁ := |deriv f α| / 2 with hm₁def
  set M₂ := |iteratedDeriv 2 f α| / 2 + 1 with hM₂def
  have hm₁ : 0 < m₁ := half_pos (abs_pos.2 hf')
  have hM₁ : 0 < 3 * |deriv f α| / 2 := by have := abs_pos.2 hf'; positivity
  have hM₂ : 0 < M₂ := by rw [hM₂def]; positivity
  have hC : 0 < M₂ / m₁ := by positivity
  set ε := min δ (1 / (2 * (M₂ / m₁))) with hεdef
  have hε : 0 < ε := lt_min hδ (by positivity)
  have hCε : M₂ / m₁ * ε ≤ 1 / 2 := by
    calc M₂ / m₁ * ε ≤ M₂ / m₁ * (1 / (2 * (M₂ / m₁))) := by gcongr; exact min_le_right _ _
      _ = 1 / 2 := by rw [mul_one_div, mul_comm 2, ← div_div, div_self hC.ne']
  refine ⟨ε, hε, fun xm1 hxm1 x₀ hx₀ hne h1 h2 => ?_⟩
  exact (hb.mono (min_le_left _ _)).tendsto_iterate hα hε hm₁ hM₁ hM₂ hCε
    ⟨hxm1, hx₀, hne, h1, h2⟩

/-- **Property 6.2 of [quarteroni2000numerical]: the secant method has order `(1 + √5) / 2`.** If
`f α = 0`, `f` is `C²` at `α`, `f'(α) ≠ 0` and `f''(α) ≠ 0`, then there is `ε > 0` such that from
any two distinct starting values in `(α - ε, α + ε)` different from `α` the secant iterates
converge to `α` with order the golden ratio in the sense of `ConvergesWithOrder`. The book cites
[isaacson1994analysis] pp. 99–101 without proof and omits `f'(α) ≠ 0`, which is needed: at a
multiple root the method is linear. With `f''(α) ≠ 0` every pair of iterates stays admissible
(`LocalBounds.isAdmissible_step`), the two-sided bound holds at every step, and
`exists_le_mul_rpow_goldenRatio` turns it into the order bound. -/
theorem exists_ball_convergesWithOrder_goldenRatio (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) (hf'' : iteratedDeriv 2 f α ≠ 0) :
    ∃ ε > 0, ∀ xm1 ∈ Metric.ball α ε, ∀ x₀ ∈ Metric.ball α ε, xm1 ≠ x₀ → xm1 ≠ α → x₀ ≠ α →
      ConvergesWithOrder (iterate f xm1 x₀) α Real.goldenRatio := by
  have hη : 0 < |iteratedDeriv 2 f α| / 4 := by have := abs_pos.2 hf''; positivity
  obtain ⟨δ, hδ, hb⟩ := exists_localBounds hf hf' hη
  set m₁ := |deriv f α| / 2 with hm₁def
  set M₁ := 3 * |deriv f α| / 2 with hM₁def
  set m₂ := |iteratedDeriv 2 f α| / 2 - |iteratedDeriv 2 f α| / 4 with hm₂def
  set M₂ := |iteratedDeriv 2 f α| / 2 + |iteratedDeriv 2 f α| / 4 with hM₂def
  have hm₁ : 0 < m₁ := half_pos (abs_pos.2 hf')
  have hM₁ : 0 < M₁ := by have := abs_pos.2 hf'; positivity
  have hm₂ : 0 < m₂ := by have := abs_pos.2 hf''; simp only [hm₂def]; linarith
  have hM₂ : 0 < M₂ := by rw [hM₂def]; positivity
  have hC : 0 < M₂ / m₁ := by positivity
  set ε := min δ (1 / (2 * (M₂ / m₁))) with hεdef
  have hε : 0 < ε := lt_min hδ (by positivity)
  have hCε : M₂ / m₁ * ε ≤ 1 / 2 := by
    calc M₂ / m₁ * ε ≤ M₂ / m₁ * (1 / (2 * (M₂ / m₁))) := by gcongr; exact min_le_right _ _
      _ = 1 / 2 := by rw [mul_one_div, mul_comm 2, ← div_div, div_self hC.ne']
  have hCε' : M₂ / m₁ * ε ≤ 1 := hCε.trans (by norm_num)
  have hb' : LocalBounds f α ε m₁ M₁ m₂ M₂ := hb.mono (min_le_left _ _)
  refine ⟨ε, hε, fun xm1 hxm1 x₀ hx₀ hne h1 h2 => ?_⟩
  have hs : IsAdmissible α ε (xm1, x₀) := ⟨hxm1, hx₀, hne, h1, h2⟩
  refine ⟨(hb'.tendsto_iterate hα hε hm₁ hM₁ hM₂ hCε hs).2, ?_⟩
  have hall : ∀ k, IsAdmissible α ε ((step f)^[k] (xm1, x₀)) := fun k => by
    induction k with
    | zero => exact hs
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hb'.isAdmissible_step hα hε hm₁ hM₁ hm₂ hCε' ih
  set e : ℕ → ℝ := fun k => |((step f)^[k] (xm1, x₀)).1 - α| with he
  have hpos : ∀ k, 0 < e k := fun k => abs_pos.2 (sub_ne_zero.2 (hall k).fst_ne)
  have hstep : ∀ k, m₂ / M₁ * (e (k + 1) * e k) ≤ e (k + 2) ∧
      e (k + 2) ≤ M₂ / m₁ * (e (k + 1) * e k) := fun k => by
    obtain ⟨hlo, hup, -, -⟩ := hb'.step_bounds hα hε hm₁ hM₁ hCε' (hall k)
    simp only [he, Function.iterate_succ_apply']
    exact ⟨hlo, hup⟩
  obtain ⟨B, hB, hbound⟩ := exists_le_mul_rpow_goldenRatio (by positivity) hpos
    (fun k => (hstep k).2) (fun k => (hstep k).1)
  refine ⟨B, hB, Eventually.of_forall fun k => ?_⟩
  have := hbound (k + 1)
  simp only [he, abs_fst_iterate_succ_sub] at this
  simpa [Real.norm_eq_abs] using this

end Convergence

end Secant

namespace RegulaFalsi

variable {f : ℝ → ℝ} {xm1 x₀ : ℝ}

/-- The secant point of a pair `(x, x')`: the zero `x - (x - x') / (f x - f x') * f x` of the
secant line through `(x, f x)` and `(x', f x')`. -/
noncomputable def secantPoint (f : ℝ → ℝ) (s : ℝ × ℝ) : ℝ :=
  s.1 - (s.1 - s.2) / (f s.1 - f s.2) * f s.1

/-- One **regula falsi** step on the state `(x_k, x_{k'})`, `x_{k'}` the latest earlier iterate
with `f x_{k'} f x_k < 0` ([quarteroni2000numerical] (6.15)): the new iterate is the secant
point `z`, and the bracket partner becomes `x_k` if `f z · f x_k < 0` and stays `x_{k'}`
otherwise — the book's "maximum index `k' < k + 1` with `f(x_{k'}) f(x_{k+1}) < 0`", since
`f z · f x_{k'} < 0` exactly when `f z · f x_k ≥ 0` and `f z ≠ 0`. -/
noncomputable def step (f : ℝ → ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  if f (secantPoint f s) * f s.1 < 0 then (secantPoint f s, s.1) else (secantPoint f s, s.2)

/-- The regula falsi iterates: `iterate f xm1 x₀ k = x_k` from the bracketing pair
`x_{-1} = xm1`, `x_0 = x₀`. -/
noncomputable def iterate (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) : ℝ :=
  ((step f)^[k] (x₀, xm1)).1

/-- The regula falsi iterate of index `0` is the initial value `x₀`. -/
@[simp]
theorem iterate_zero (f : ℝ → ℝ) (xm1 x₀ : ℝ) : iterate f xm1 x₀ 0 = x₀ := rfl

/-- The new iterate is the secant point, whichever partner is kept. -/
theorem fst_step (f : ℝ → ℝ) (s : ℝ × ℝ) : (step f s).1 = secantPoint f s := by
  unfold step
  split_ifs <;> rfl

/-- The recurrence: `x_{k+1}` is the secant point of the `k`-th state. -/
theorem iterate_succ (f : ℝ → ℝ) (xm1 x₀ : ℝ) (k : ℕ) :
    iterate f xm1 x₀ (k + 1) = secantPoint f ((step f)^[k] (x₀, xm1)) := by
  rw [iterate, Function.iterate_succ_apply', fst_step]

/-- **The secant point of a bracketing pair lies between its points**: for `f x · f x' < 0`,
`secantPoint f (x, x') ∈ [[x, x']]`. It is `x + t (x' - x)` with the weight
`t = f x / (f x - f x') ∈ [0, 1]`. -/
theorem secantPoint_mem_uIcc {s : ℝ × ℝ} (h : f s.1 * f s.2 < 0) :
    secantPoint f s ∈ uIcc s.1 s.2 := by
  have heq : secantPoint f s = s.1 + (f s.1 / (f s.1 - f s.2)) • (s.2 - s.1) := by
    simp only [secantPoint, smul_eq_mul]
    ring
  rw [heq]
  refine (convex_uIcc s.1 s.2).add_smul_sub_mem left_mem_uIcc right_mem_uIcc ⟨?_, ?_⟩
  · rcases mul_neg_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_nonneg h1.le (by linarith)
    · exact div_nonneg_of_nonpos h1.le (by linarith)
  · rcases mul_neg_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [div_le_one (by linarith)]; linarith
    · rw [div_le_one_of_neg (by linarith)]; linarith

/-- **Bracketing is preserved by one step** when the secant point is not an exact root: from
`f x · f x' < 0` and `f z ≠ 0`, the new state again has `f · f < 0`. -/
theorem mul_neg_step {s : ℝ × ℝ} (h : f s.1 * f s.2 < 0) (hz : f (secantPoint f s) ≠ 0) :
    f (step f s).1 * f (step f s).2 < 0 := by
  unfold step
  split_ifs with hlt
  · exact hlt
  · simp only
    have h1 : f s.1 ≠ 0 := fun h0 => by simp [h0] at h
    have hpos : 0 < f (secantPoint f s) * f s.1 :=
      lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm (mul_ne_zero hz h1))
    nlinarith [mul_pos hpos (neg_pos.2 h), sq_nonneg (f s.1)]

/-- **Bracketing is preserved** ([quarteroni2000numerical] §6.2.2): if `f x₀ · f x_{-1} < 0` and no
iterate is an exact root, every state `(x_k, x_{k'})` has `f x_k · f x_{k'} < 0`. -/
theorem mul_neg_iterate (h : f x₀ * f xm1 < 0) (hroot : ∀ k, f (iterate f xm1 x₀ k) ≠ 0) (k : ℕ) :
    f ((step f)^[k] (x₀, xm1)).1 * f ((step f)^[k] (x₀, xm1)).2 < 0 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hz := hroot (k + 1)
    rw [iterate_succ] at hz
    exact mul_neg_step ih hz

/-- **The zero of the chord** through `(u, f u)` and `(v, f v)`, the secant point written
symmetrically in its two points: `u - f(u) (v - u)/(f v - f u)`. -/
noncomputable def chord (f : ℝ → ℝ) (u v : ℝ) : ℝ := u - f u * ((v - u) / (f v - f u))

/-- The secant point of a state is the chord zero of its two points. -/
theorem secantPoint_eq_chord (f : ℝ → ℝ) (s : ℝ × ℝ) : secantPoint f s = chord f s.1 s.2 := by
  rw [secantPoint, chord, ← neg_sub (f s.2) (f s.1), ← neg_sub s.2 s.1, neg_div_neg_eq]
  ring

/-- **The chord zero is symmetric** in its two points, as long as the two values differ. -/
theorem chord_comm {u v : ℝ} (hne : f u ≠ f v) : chord f u v = chord f v u := by
  have h : f v - f u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h' : f u - f v ≠ 0 := sub_ne_zero.mpr hne
  rw [chord, chord]
  field_simp
  ring

/-- **A state whose iterate is an exact root is a fixed point of the step**: the iteration stalls
there. -/
theorem step_eq_self {s : ℝ × ℝ} (hz : f s.1 = 0) : step f s = s := by
  have hp : secantPoint f s = s.1 := by simp [secantPoint, hz]
  unfold step
  rw [hp, hz, zero_mul]
  simp

/-- The bracket partner of the next state is one of the two points of the present one. -/
theorem snd_step_eq (f : ℝ → ℝ) (s : ℝ × ℝ) : (step f s).2 = s.1 ∨ (step f s).2 = s.2 := by
  unfold step
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The whole state stays in the starting interval** ([quarteroni2000numerical] §6.2.2): for
`f x₀ · f x_{-1} < 0`, both points of every state lie in `[[x_{-1}, x_0]]`, and each state either
brackets the root or has an exact root as its iterate (in which case the method stays there). -/
theorem state_mem_uIcc (h : f x₀ * f xm1 < 0) (k : ℕ) :
    ((step f)^[k] (x₀, xm1)).1 ∈ uIcc xm1 x₀ ∧ ((step f)^[k] (x₀, xm1)).2 ∈ uIcc xm1 x₀ ∧
      (f ((step f)^[k] (x₀, xm1)).1 = 0 ∨
        f ((step f)^[k] (x₀, xm1)).1 * f ((step f)^[k] (x₀, xm1)).2 < 0) := by
  induction k with
  | zero => exact ⟨right_mem_uIcc, left_mem_uIcc, Or.inr h⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    set s := (step f)^[k] (x₀, xm1) with hs
    rcases h3 with h3 | h3
    · rw [step_eq_self h3]
      exact ⟨h1, h2, Or.inl h3⟩
    · have hz : secantPoint f s ∈ uIcc xm1 x₀ :=
        uIcc_subset_uIcc h1 h2 (secantPoint_mem_uIcc h3)
      refine ⟨by rw [fst_step]; exact hz, ?_, ?_⟩
      · unfold step
        split_ifs
        · exact h1
        · exact h2
      · by_cases hfz : f (secantPoint f s) = 0
        · exact Or.inl (by rw [fst_step]; exact hfz)
        · exact Or.inr (mul_neg_step h3 hfz)

/-- **The iterates stay in the starting interval** ([quarteroni2000numerical] §6.2.2, "unlike the
secant method, the iterates generated by (6.15) are all contained within the starting interval
`[x^{(-1)}, x^{(0)}]`"). -/
theorem iterate_mem_uIcc (h : f x₀ * f xm1 < 0) (k : ℕ) :
    iterate f xm1 x₀ k ∈ uIcc xm1 x₀ :=
  (state_mem_uIcc h k).1

/-- **Convergence of regula falsi** ([quarteroni2000numerical] §6.2.2): from a bracketing pair
`f x_0 · f x_{-1} < 0` of a function continuous on `[[x_{-1}, x_0]]` with a *unique* zero `α`
there, the iterates converge to `α`.

The two ends of the bracket are monotone and bounded, so they converge to `l ≤ r`, and the chord
zeros — the iterates — converge to the chord zero `z` of `(l, f l)` and `(r, f r)` as soon as
`f l ≠ f r`. Every chord zero becomes an end of the next bracket, hence lies outside `(l, r)`, so
`z` does too; being a convex combination of `l` and `r` it is then `l` or `r`, and in either case
the corresponding value of `f` vanishes, so `z = α` by uniqueness. If instead `f l = f r` then
`f l · f r ≤ 0` forces `f l = f r = 0` and `l = r = α`, and the iterates are squeezed.

An iterate that is an exact root is a fixed point of the step (`step_eq_self`), so that case is
separate and immediate. -/
theorem tendsto_iterate (hf : ContinuousOn f (uIcc xm1 x₀)) (h : f x₀ * f xm1 < 0) {α : ℝ}
    (huniq : ∀ y ∈ uIcc xm1 x₀, f y = 0 → y = α) :
    Tendsto (iterate f xm1 x₀) atTop (𝓝 α) := by
  by_cases hroot : ∃ k, f (iterate f xm1 x₀ k) = 0
  · -- an iterate is an exact root: the iteration stalls there
    obtain ⟨k, hk⟩ := hroot
    have hstall : ∀ j, k ≤ j → (step f)^[j] (x₀, xm1) = (step f)^[k] (x₀, xm1) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => rfl
      | succ j hj ih => rw [Function.iterate_succ_apply', ih, step_eq_self hk]
    have hαk : iterate f xm1 x₀ k = α := huniq _ (iterate_mem_uIcc h k) hk
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop k] with j hj
    rw [iterate, hstall j hj, ← iterate, hαk]
  · simp only [not_exists] at hroot
    obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ × ℝ, ∀ k, S k = (step f)^[k] (x₀, xm1) := ⟨_, fun _ => rfl⟩
    obtain ⟨L, hLdef⟩ : ∃ L : ℕ → ℝ, ∀ k, L k = min (S k).1 (S k).2 := ⟨_, fun _ => rfl⟩
    obtain ⟨R, hRdef⟩ : ∃ R : ℕ → ℝ, ∀ k, R k = max (S k).1 (S k).2 := ⟨_, fun _ => rfl⟩
    have hx : ∀ k, iterate f xm1 x₀ k = (S k).1 := fun k => by rw [hS]; rfl
    have hbr : ∀ k, f (S k).1 * f (S k).2 < 0 := fun k => by
      rw [hS]; exact mul_neg_iterate h hroot k
    have hfne : ∀ k, f (S k).1 ≠ f (S k).2 := fun k hEq => by
      have := hbr k; rw [hEq] at this; nlinarith [sq_nonneg (f (S k).2)]
    have hmem : ∀ k, (S k).1 ∈ uIcc xm1 x₀ ∧ (S k).2 ∈ uIcc xm1 x₀ := fun k => by
      rw [hS]; exact ⟨(state_mem_uIcc h k).1, (state_mem_uIcc h k).2.1⟩
    have hLmem : ∀ k, L k ∈ uIcc xm1 x₀ := fun k => by
      rw [hLdef]
      rcases le_total (S k).1 (S k).2 with hle | hle
      · rw [min_eq_left hle]; exact (hmem k).1
      · rw [min_eq_right hle]; exact (hmem k).2
    have hRmem : ∀ k, R k ∈ uIcc xm1 x₀ := fun k => by
      rw [hRdef]
      rcases le_total (S k).1 (S k).2 with hle | hle
      · rw [max_eq_right hle]; exact (hmem k).2
      · rw [max_eq_left hle]; exact (hmem k).1
    have hLR : ∀ k, L k ≤ R k := fun k => by rw [hLdef, hRdef]; exact min_le_max
    have hfLR : ∀ k, f (L k) * f (R k) < 0 := fun k => by
      rw [hLdef, hRdef]
      rcases le_total (S k).1 (S k).2 with hle | hle
      · rw [min_eq_left hle, max_eq_right hle]; exact hbr k
      · rw [min_eq_right hle, max_eq_left hle, mul_comm]; exact hbr k
    -- the brackets are nested
    have huI : ∀ k, uIcc (S k).1 (S k).2 = Icc (L k) (R k) := fun k => by
      rw [hLdef, hRdef]; rfl
    have hnext : ∀ k, (S (k + 1)).1 ∈ Icc (L k) (R k) ∧ (S (k + 1)).2 ∈ Icc (L k) (R k) := by
      intro k
      have hsucc : S (k + 1) = step f (S k) := by rw [hS, hS, Function.iterate_succ_apply']
      constructor
      · rw [hsucc, fst_step, ← huI k]
        exact secantPoint_mem_uIcc (hbr k)
      · rw [hsucc]
        rcases snd_step_eq f (S k) with he | he <;> rw [he, ← huI k]
        · exact left_mem_uIcc
        · exact right_mem_uIcc
    have hLmono : Monotone L := monotone_nat_of_le_succ fun k => by
      rw [hLdef (k + 1)]
      exact le_min (hnext k).1.1 (hnext k).2.1
    have hRanti : Antitone R := antitone_nat_of_succ_le fun k => by
      rw [hRdef (k + 1)]
      exact max_le (hnext k).1.2 (hnext k).2.2
    have hbddL : BddAbove (range L) :=
      ⟨R 0, by rintro _ ⟨k, rfl⟩; exact (hLR k).trans (hRanti (Nat.zero_le k))⟩
    have hbddR : BddBelow (range R) :=
      ⟨L 0, by rintro _ ⟨k, rfl⟩; exact (hLmono (Nat.zero_le k)).trans (hLR k)⟩
    obtain ⟨l, htL⟩ : ∃ l, Tendsto L atTop (𝓝 l) := ⟨_, tendsto_atTop_ciSup hLmono hbddL⟩
    obtain ⟨r, htR⟩ : ∃ r, Tendsto R atTop (𝓝 r) := ⟨_, tendsto_atTop_ciInf hRanti hbddR⟩
    have hLle : ∀ k, L k ≤ l := fun k => hLmono.ge_of_tendsto htL k
    have hRge : ∀ k, r ≤ R k := fun k => hRanti.le_of_tendsto htR k
    have hlr : l ≤ r := le_of_tendsto_of_tendsto' htL htR hLR
    have hclosed : IsClosed (uIcc xm1 x₀) := isClosed_Icc
    have hlmem : l ∈ uIcc xm1 x₀ := hclosed.mem_of_tendsto htL (Eventually.of_forall hLmem)
    have hrmem : r ∈ uIcc xm1 x₀ := hclosed.mem_of_tendsto htR (Eventually.of_forall hRmem)
    have hfL : Tendsto (fun k => f (L k)) atTop (𝓝 (f l)) :=
      (hf l hlmem).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within L htL
        (Eventually.of_forall hLmem))
    have hfR : Tendsto (fun k => f (R k)) atTop (𝓝 (f r)) :=
      (hf r hrmem).tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within R htR
        (Eventually.of_forall hRmem))
    have hflr : f l * f r ≤ 0 :=
      le_of_tendsto (hfL.mul hfR) (Eventually.of_forall fun k => (hfLR k).le)
    by_cases hne : f l = f r
    · -- the bracket collapses to the root
      have hfl0 : f l = 0 := by nlinarith [hflr, sq_nonneg (f l)]
      have hl : l = α := huniq l hlmem hfl0
      have hr : r = α := huniq r hrmem (by rw [← hne]; exact hfl0)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hl ▸ htL) (hr ▸ htR) (fun k => ?_)
        (fun k => ?_)
      · rw [hx, hLdef]; exact min_le_left _ _
      · rw [hx, hRdef]; exact le_max_left _ _
    · -- the chord zeros converge to an end of the limiting bracket
      have hden : f r - f l ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      have hchord : ∀ k, (S (k + 1)).1 = chord f (L k) (R k) := by
        intro k
        have hsucc : S (k + 1) = step f (S k) := by rw [hS, hS, Function.iterate_succ_apply']
        rw [hsucc, fst_step, secantPoint_eq_chord, hLdef, hRdef]
        rcases le_total (S k).1 (S k).2 with hle | hle
        · rw [min_eq_left hle, max_eq_right hle]
        · rw [min_eq_right hle, max_eq_left hle]
          exact chord_comm (hfne k)
      have htc : Tendsto (fun k => chord f (L k) (R k)) atTop (𝓝 (chord f l r)) := by
        simp only [chord]
        exact htL.sub (hfL.mul ((htR.sub htL).div (hfR.sub hfL) hden))
      have hout : ∀ k, chord f (L k) (R k) ∈ Iic l ∪ Ici r := by
        intro k
        rw [← hchord k]
        rcases le_total (S (k + 1)).1 (S (k + 1)).2 with hle | hle
        · refine Or.inl ?_
          have hh := hLle (k + 1)
          rw [hLdef (k + 1), min_eq_left hle] at hh
          exact hh
        · refine Or.inr ?_
          have hh := hRge (k + 1)
          rw [hRdef (k + 1), max_eq_left hle] at hh
          exact hh
      have hzmem : chord f l r ∈ Iic l ∪ Ici r :=
        (isClosed_Iic.union isClosed_Ici).mem_of_tendsto htc (Eventually.of_forall hout)
      -- the chord zero is a convex combination of the two ends
      have ht01 : 0 ≤ -f l / (f r - f l) ∧ -f l / (f r - f l) ≤ 1 := by
        rcases mul_nonpos_iff.1 hflr with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hd : f r - f l < 0 := by
            rcases lt_or_eq_of_le (by linarith : f r - f l ≤ 0) with hh | hh
            · exact hh
            · exact absurd (by linarith : f l = f r) hne
          exact ⟨div_nonneg_of_nonpos (by linarith) hd.le, by rw [div_le_one_of_neg hd]; linarith⟩
        · have hd : 0 < f r - f l := by
            rcases lt_or_eq_of_le (by linarith : (0 : ℝ) ≤ f r - f l) with hh | hh
            · exact hh
            · exact absurd (by linarith : f l = f r) hne
          exact ⟨div_nonneg (by linarith) hd.le, by rw [div_le_one hd]; linarith⟩
      have hzform : chord f l r = l + (-f l / (f r - f l)) * (r - l) := by
        rw [chord]; field_simp; ring
      have hzl : l ≤ chord f l r := by
        rw [hzform]; nlinarith [ht01.1, sub_nonneg.2 hlr]
      have hzr : chord f l r ≤ r := by
        rw [hzform]; nlinarith [ht01.2, sub_nonneg.2 hlr, ht01.1]
      have hz : chord f l r = l ∨ chord f l r = r := by
        rcases hzmem with h1 | h1
        · exact Or.inl (le_antisymm h1 hzl)
        · exact Or.inr (le_antisymm hzr h1)
      have hlt : l < r := lt_of_le_of_ne hlr fun heq => hne (by rw [heq])
      have hzα : chord f l r = α := by
        rcases hz with hz | hz
        · have hfl : f l = 0 := by
            rw [hzform] at hz
            have hrl : r - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlt.ne)
            have h0 : -f l / (f r - f l) * (r - l) = 0 := by linarith
            rcases mul_eq_zero.1 h0 with h1 | h1
            · rcases div_eq_zero_iff.1 h1 with h2 | h2
              · linarith
              · exact absurd h2 hden
            · exact absurd h1 hrl
          rw [hz]
          exact huniq l hlmem hfl
        · have hfr : f r = 0 := by
            rw [hzform] at hz
            have hrl : r - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlt.ne)
            have h0 : -f l / (f r - f l) * (r - l) = r - l := by linarith
            have h1 : (-f l / (f r - f l) - 1) * (r - l) = 0 := by
              have he : (-f l / (f r - f l) - 1) * (r - l)
                  = -f l / (f r - f l) * (r - l) - (r - l) := by ring
              rw [he, h0, sub_self]
            rcases mul_eq_zero.1 h1 with h2 | h2
            · have h3 : -f l / (f r - f l) = 1 := by linarith
              field_simp at h3
              linarith
            · exact absurd h2 hrl
          rw [hz]
          exact huniq r hrmem hfr
      rw [← tendsto_add_atTop_iff_nat 1]
      refine Tendsto.congr ?_ (hzα ▸ htc)
      intro k
      rw [hx, hchord k]

/-! #### The linear order of convergence

The order statement needs the divided-difference error identity of the secant method
(`Secant.abs_sub_root_le`) applied to the bracketing pair `(x_k, x_{k'})`:
`|e_{k+1}| ≤ (M₂ / m₁) |e_k| |e_{k'}|`, with `m₁` a lower bound for the first divided difference
`f[x_{k'}, x_k]` and `M₂` an upper bound for the second, `f[x_{k'}, x_k, α]`. Since `|e_{k'}|` is at
most the length of the starting interval, that is linear convergence. The two bounds are uniform
over the bracket rather than local, which is what removes the need to identify the endpoint that is
eventually frozen:

* **below**, `f[u, v] ≥ min_{[[x_{-1}, x_0]]} |g|` with `g = dslope f α`, because
  `f u = (u - α) g u` and `f v = (v - α) g v` with `(u - α)(v - α) < 0` (the root separates a
  bracketing pair) force `g u` and `g v` to have the same sign, so the numerator of
  `f[u, v] = ((v - α) g v - (u - α) g u) / (v - u)` is a sum of two terms of equal sign; and `g`,
  continuous and zero-free on the compact bracket (zero-free because `α` is the only root and
  `g α = f'(α) ≠ 0`), is bounded away from `0` there;
* **above**, `f[u, v, α] = g[u, v]`, bounded by `|g'(α)| + 1` when `u` and `v` are both in a small
  ball around `α` (the mean value inequality for the `C¹` function `g`,
  `exists_ball_abs_slope_sub_deriv_le`) and by `4 sup|g| / δ` when they are `δ / 2` apart. The
  iterates converge to `α`, so eventually `x_k` is in the small ball and one of the two cases
  applies.

No convexity and no hypothesis on `f''(α)` enter: `ContDiffAt ℝ 2 f α` is used only to make
`dslope f α` continuously differentiable at `α` (Hadamard's lemma). -/

/-- **The method stalls at an exact root**: if the `k`-th iterate is a zero of `f`, every later
state equals the `k`-th one. -/
theorem state_eq_of_apply_eq_zero {k : ℕ} (hk : f ((step f)^[k] (x₀, xm1)).1 = 0) {j : ℕ}
    (hj : k ≤ j) : (step f)^[j] (x₀, xm1) = (step f)^[k] (x₀, xm1) := by
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih => rw [Function.iterate_succ_apply', ih, step_eq_self hk]

/-- **The root separates a bracketing pair**: if `α` is the only zero of `f` in `[[x_{-1}, x_0]]`
and `u, v` in that interval satisfy `f u · f v < 0`, then `(u - α)(v - α) < 0`. The theorem of
zeros gives a zero strictly between `u` and `v`, and uniqueness identifies it with `α`. -/
theorem sub_mul_sub_neg_of_mul_neg (hf : ContinuousOn f (uIcc xm1 x₀)) {α u v : ℝ}
    (huniq : ∀ y ∈ uIcc xm1 x₀, f y = 0 → y = α) (hu : u ∈ uIcc xm1 x₀) (hv : v ∈ uIcc xm1 x₀)
    (hfuv : f u * f v < 0) : (u - α) * (v - α) < 0 := by
  have hsub : uIcc u v ⊆ uIcc xm1 x₀ := uIcc_subset_uIcc hu hv
  have hle : min u v ≤ max u v := min_le_max
  have hcont : ContinuousOn f (Icc (min u v) (max u v)) := hf.mono hsub
  have hmul : f (min u v) * f (max u v) < 0 := by
    rcases le_total u v with hle' | hle'
    · rwa [min_eq_left hle', max_eq_right hle']
    · rw [min_eq_right hle', max_eq_left hle', mul_comm]; exact hfuv
  obtain ⟨β, hβ, hfβ⟩ := exists_eq_zero_Ioo_of_mul_neg hle hcont hmul
  have hβα : β = α := huniq β (hsub (Ioo_subset_Icc_self hβ)) hfβ
  subst hβα
  rcases le_total u v with hle' | hle'
  · rw [min_eq_left hle', max_eq_right hle'] at hβ
    nlinarith [hβ.1, hβ.2]
  · rw [min_eq_right hle', max_eq_left hle'] at hβ
    nlinarith [hβ.1, hβ.2]

/-- **The first divided difference at a bracketing pair is at least `min |dslope f α|`.** With
`g = dslope f α` one has `f u = (u - α) g u` and `f v = (v - α) g v` (`sub_smul_dslope`), so
`f u · f v < 0` together with `(u - α)(v - α) < 0` forces `g u · g v > 0`; the numerator of
`f[u, v] = ((v - α) g v - (u - α) g u) / (v - u)` is then a sum of two terms of the same sign, and
`|f[u, v]|² ≥ m² |v - u|² / |v - u|²`. -/
theorem le_abs_newton_two_of_mul_neg {α m u v : ℝ} (hα : f α = 0) (huv : u ≠ v)
    (hsign : (u - α) * (v - α) < 0) (hfuv : f u * f v < 0) (hm : 0 < m)
    (hgu : m ≤ |dslope f α u|) (hgv : m ≤ |dslope f α v|) :
    m ≤ |DividedDifference.newton f ![u, v]| := by
  set gu := dslope f α u with hgudef
  set gv := dslope f α v with hgvdef
  have hfu : f u = (u - α) * gu := by
    have h := sub_smul_dslope f α u
    simp only [smul_eq_mul] at h
    rw [hα, sub_zero] at h
    exact h.symm
  have hfv : f v = (v - α) * gv := by
    have h := sub_smul_dslope f α v
    simp only [smul_eq_mul] at h
    rw [hα, sub_zero] at h
    exact h.symm
  have hkey : ((u - α) * (v - α)) * (gu * gv) < 0 := by
    rw [hfu, hfv] at hfuv; nlinarith [hfuv]
  have hprod : 0 < gu * gv := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hvu : v - u ≠ 0 := sub_ne_zero.2 (Ne.symm huv)
  have hsq1 : m ^ 2 ≤ gu ^ 2 := by nlinarith [abs_nonneg gu, sq_abs gu]
  have hsq2 : m ^ 2 ≤ gv ^ 2 := by nlinarith [abs_nonneg gv, sq_abs gv]
  have hsq3 : m ^ 2 ≤ gu * gv := by
    have h : m ^ 2 ≤ |gu| * |gv| := by nlinarith [abs_nonneg gu, abs_nonneg gv]
    rwa [← abs_mul, abs_of_pos hprod] at h
  rw [DividedDifference.newton_two_eq _ huv, hfu, hfv, abs_div, le_div_iff₀ (abs_pos.2 hvu)]
  have key : (m * |v - u|) ^ 2 ≤ ((v - α) * gv - (u - α) * gu) ^ 2 := by
    rw [mul_pow, sq_abs]
    nlinarith [mul_nonneg (sq_nonneg (v - α)) (sub_nonneg.2 hsq2),
      mul_nonneg (sq_nonneg (u - α)) (sub_nonneg.2 hsq1),
      mul_nonneg (neg_nonneg.2 hsign.le) (sub_nonneg.2 hsq3)]
  have h1 : 0 ≤ m * |v - u| := by positivity
  nlinarith [abs_nonneg ((v - α) * gv - (u - α) * gu), sq_abs ((v - α) * gv - (u - α) * gu)]

/-- **Regula falsi converges linearly** ([quarteroni2000numerical] §6.2.2, "the Regula Falsi method
has linear convergence order", quoted there from Ralston and Rabinowitz without proof): under the
hypotheses of `tendsto_iterate` together with `f` twice continuously differentiable at the root and
`f'(α) ≠ 0`, the iterates converge to `α` with order `1` in the sense of
[quarteroni2000numerical] Definition 6.1.

The constant produced is `M₂ |x_0 - x_{-1}| / m₁`, with `m₁` and `M₂` the uniform bounds on the two
divided differences described above; the book's hypothesis `f''(α) ≠ 0` is not needed, and neither
is any convexity assumption identifying the endpoint that is eventually frozen. -/
theorem convergesWithOrder_one_iterate (hf : ContinuousOn f (uIcc xm1 x₀)) (h : f x₀ * f xm1 < 0)
    {α : ℝ} (huniq : ∀ y ∈ uIcc xm1 x₀, f y = 0 → y = α) (hC : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) : ConvergesWithOrder (iterate f xm1 x₀) α 1 := by
  refine ⟨tendsto_iterate hf h huniq, ?_⟩
  -- the root, and its position strictly inside the bracket
  have hxne : xm1 ≠ x₀ := by
    intro heq
    rw [heq] at h
    nlinarith [sq_nonneg (f x₀)]
  have hle : min xm1 x₀ ≤ max xm1 x₀ := min_le_max
  have hmul : f (min xm1 x₀) * f (max xm1 x₀) < 0 := by
    rcases le_total xm1 x₀ with hle' | hle'
    · rw [min_eq_left hle', max_eq_right hle', mul_comm]; exact h
    · rwa [min_eq_right hle', max_eq_left hle']
  obtain ⟨β, hβ, hfβ⟩ := exists_eq_zero_Ioo_of_mul_neg hle hf hmul
  have hβα : β = α := huniq β (Ioo_subset_Icc_self hβ) hfβ
  subst hβα
  have hα : f β = 0 := hfβ
  have hαI : β ∈ uIcc xm1 x₀ := Ioo_subset_Icc_self hβ
  have hInhds : uIcc xm1 x₀ ∈ 𝓝 β :=
    Filter.mem_of_superset (Ioo_mem_nhds hβ.1 hβ.2) Ioo_subset_Icc_self
  -- the divided slope `g = dslope f β` is continuous and zero-free on the bracket
  have hdiff : DifferentiableAt ℝ f β := hC.differentiableAt (by norm_num)
  have hgc : ContinuousOn (dslope f β) (uIcc xm1 x₀) := (continuousOn_dslope hInhds).2 ⟨hf, hdiff⟩
  have hgne : ∀ x ∈ uIcc xm1 x₀, dslope f β x ≠ 0 := by
    intro x hx
    rcases eq_or_ne x β with rfl | hxa
    · rw [dslope_same]; exact hf'
    · rw [dslope_of_ne _ hxa, slope_def_field]
      refine div_ne_zero (sub_ne_zero.2 ?_) (sub_ne_zero.2 hxa)
      intro hfx
      exact hxa (huniq x hx (by rw [hfx, hα]))
  obtain ⟨m, hmpos, hmg⟩ : ∃ m, 0 < m ∧ ∀ x ∈ uIcc xm1 x₀, m ≤ |dslope f β x| := by
    obtain ⟨z, hzI, hz⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hgc.abs
    exact ⟨|dslope f β z|, abs_pos.2 (hgne z hzI), fun x hx => hz hx⟩
  obtain ⟨Mg, hMg⟩ := isCompact_uIcc.exists_bound_of_continuousOn hgc
  have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg β hαI)
  -- the `C¹` bound for `g` near the root
  have hC2 : ContDiffAt ℝ (1 + 1 : ℕ) f β := by simpa using hC
  have hgC1 : ContDiffAt ℝ 1 (dslope f β) β := ContDiffAt.dslope_same (n := 1) hC2
  obtain ⟨δ, hδ, hball⟩ := exists_ball_abs_slope_sub_deriv_le hgC1 one_pos
  set M₂ : ℝ := max (|deriv (dslope f β) β| + 1) (4 * Mg / δ) with hM₂def
  have hM₂pos : 0 < M₂ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hspan : max xm1 x₀ - min xm1 x₀ ≤ |xm1 - x₀| := by
    rcases le_total xm1 x₀ with hle' | hle'
    · rw [min_eq_left hle', max_eq_right hle', abs_sub_comm, abs_of_nonneg (by linarith)]
    · rw [min_eq_right hle', max_eq_left hle', abs_of_nonneg (by linarith)]
  have hdiam : ∀ a ∈ uIcc xm1 x₀, |a - β| ≤ |xm1 - x₀| := by
    intro a ha
    rw [abs_sub_le_iff]
    constructor <;> linarith [ha.1, ha.2, hαI.1, hαI.2]
  have hxpos : 0 < |xm1 - x₀| := abs_pos.2 (sub_ne_zero.2 hxne)
  refine ⟨M₂ / m * |xm1 - x₀|, by positivity, ?_⟩
  by_cases hroot : ∃ k, f (iterate f xm1 x₀ k) = 0
  · -- an iterate is an exact root: the method stalls there
    obtain ⟨k, hk⟩ := hroot
    have hstall : ∀ j, k ≤ j → iterate f xm1 x₀ j = β := by
      intro j hj
      have hj' := state_eq_of_apply_eq_zero (f := f) (x₀ := x₀) (xm1 := xm1) hk hj
      rw [iterate, hj', ← iterate]
      exact huniq _ (iterate_mem_uIcc h k) hk
    filter_upwards [eventually_ge_atTop k] with j hj
    rw [hstall j hj, hstall (j + 1) (by omega)]
    simp
  · simp only [not_exists] at hroot
    filter_upwards [(tendsto_iterate hf h huniq).eventually
      (Metric.ball_mem_nhds β (half_pos hδ))] with k hk
    have hbr : f ((step f)^[k] (x₀, xm1)).1 * f ((step f)^[k] (x₀, xm1)).2 < 0 :=
      mul_neg_iterate h hroot k
    set s := (step f)^[k] (x₀, xm1) with hsdef
    set v := s.1 with hvdef
    set u := s.2 with hudef
    have hvI : v ∈ uIcc xm1 x₀ := (state_mem_uIcc h k).1
    have huI : u ∈ uIcc xm1 x₀ := (state_mem_uIcc h k).2.1
    have hfv : f v ≠ 0 := fun h0 => by rw [h0, zero_mul] at hbr; exact lt_irrefl _ hbr
    have hfu : f u ≠ 0 := fun h0 => by rw [h0, mul_zero] at hbr; exact lt_irrefl _ hbr
    have hva : v ≠ β := fun h0 => hfv (by rw [h0, hα])
    have hua : u ≠ β := fun h0 => hfu (by rw [h0, hα])
    have huv : u ≠ v := by
      intro h0
      rw [h0] at hbr
      nlinarith [sq_nonneg (f v)]
    have hsign : (u - β) * (v - β) < 0 :=
      sub_mul_sub_neg_of_mul_neg hf huniq huI hvI (by rw [mul_comm]; exact hbr)
    have hden : m ≤ |DividedDifference.newton f ![u, v]| :=
      le_abs_newton_two_of_mul_neg hα huv hsign (by rw [mul_comm]; exact hbr) hmpos
        (hmg u huI) (hmg v hvI)
    have hvclose : |v - β| < δ / 2 := by
      have hveq : v = iterate f xm1 x₀ k := rfl
      rw [hveq, ← Real.dist_eq]
      exact hk
    -- the second divided difference is bounded, in both regimes
    have hnum : |DividedDifference.newton f ![u, v, β]| ≤ M₂ := by
      rw [DividedDifference.newton_three_eq_newton_two_dslope _ β huv hua hva,
        DividedDifference.newton_two_eq _ huv]
      rcases lt_or_ge (|u - β|) δ with hclose | hfar
      · have hu' : u ∈ Metric.ball β δ := by rw [Metric.mem_ball, Real.dist_eq]; exact hclose
        have hv' : v ∈ Metric.ball β δ := by
          rw [Metric.mem_ball, Real.dist_eq]
          linarith
        have hb := hball u hu' v hv' huv
        have hb2 := abs_le.1 hb
        refine le_trans (b := |deriv (dslope f β) β| + 1) ?_ (le_max_left _ _)
        rw [abs_le]
        constructor
        · linarith [neg_abs_le (deriv (dslope f β) β), hb2.1]
        · linarith [le_abs_self (deriv (dslope f β) β), hb2.2]
      · have hvu : δ / 2 ≤ |v - u| := by
          have habs : |u - β| - |v - β| ≤ |u - v| := by
            have h' := abs_sub_abs_le_abs_sub (u - β) (v - β)
            simpa using h'
          rw [abs_sub_comm v u]
          linarith
        have hbound : |dslope f β v - dslope f β u| ≤ 2 * Mg := by
          have h1 := hMg v hvI
          have h2 := hMg u huI
          rw [Real.norm_eq_abs] at h1 h2
          calc |dslope f β v - dslope f β u| ≤ |dslope f β v| + |dslope f β u| := abs_sub _ _
            _ ≤ 2 * Mg := by linarith
        have hvupos : (0 : ℝ) < |v - u| := lt_of_lt_of_le (by positivity) hvu
        rw [abs_div, div_le_iff₀ hvupos]
        refine le_trans hbound ?_
        have hmax : 4 * Mg / δ ≤ M₂ := le_max_right _ _
        have hkey : 4 * Mg / δ * (δ / 2) = 2 * Mg := by field_simp; ring
        nlinarith [hvu, hmax, hM₂pos, hMg0]
    -- the error recursion
    have hstep := Secant.abs_sub_root_le hα huv hua hva hmpos hden hnum
    rw [iterate_succ, secantPoint]
    calc |v - (v - u) / (f v - f u) * f v - β| ≤ M₂ / m * (|v - β| * |u - β|) := hstep
      _ ≤ M₂ / m * (|v - β| * |xm1 - x₀|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdiam u huI) (abs_nonneg _))
            (div_pos hM₂pos hmpos).le
      _ = M₂ / m * |xm1 - x₀| * |v - β| := by ring
      _ = M₂ / m * |xm1 - x₀| * ‖iterate f xm1 x₀ k - β‖ ^ (1 : ℝ) := by
          rw [Real.rpow_one, Real.norm_eq_abs]
          rfl

end RegulaFalsi

namespace Muller

/-- One **Muller step** ([quarteroni2000numerical] (6.30)) from the triple `(x_{k-2}, x_{k-1}, x_k)`
to `(x_{k-1}, x_k, x_{k+1})`: with `d = f[x_k, x_{k-1}, x_{k-2}]`,
`w = f[x_k, x_{k-1}] + (x_k - x_{k-1}) d` and the zero of the quadratic interpolant nearest to
`x_k`, `x_{k+1} = x_k - 2 f(x_k) / (w ± √(w² - 4 f(x_k) d))`, the sign maximizing the modulus of
the denominator. Real arithmetic only: the square root is `Real.sqrt`, junk `0` for a negative
radicand (a complex pair of zeros of the parabola), where the complex version that finds complex
roots of polynomials would continue with `Complex.cpow`. A definition only; the book states no
theorem about it beyond the cited order `p ≈ 1.84`. -/
noncomputable def step (f : ℝ → ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let d := DividedDifference.newton f ![s.2.2, s.2.1, s.1]
  let w := DividedDifference.newton f ![s.2.2, s.2.1] + (s.2.2 - s.2.1) * d
  let r := Real.sqrt (w ^ 2 - 4 * f s.2.2 * d)
  let den := if |w - r| ≤ |w + r| then w + r else w - r
  (s.2.1, s.2.2, s.2.2 - 2 * f s.2.2 / den)

end Muller
