import Mathlib.NumberTheory.Real.GoldenRatio
import Numlib.Analysis.SpecialFunctions.Tribonacci
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

The secant, regula falsi and Muller iterations carry state (a pair of points, a triple for
Muller), so they are `step` functions on `ℝ × ℝ` (on `ℝ × ℝ × ℝ`) with `iterate f x₋₁ x₀ k` reading
off the `k`-th point, as `Numlib/Nonlinear/Bisection` does with brackets. Lean's `a / 0 = 0` makes a
secant step with `f x_k = f x_{k-1}` stall at `x_k`; the theorems assume what excludes it.

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

## Muller's method

Muller's method replaces the secant line by the quadratic `Muller.interp` interpolating the last
*three* iterates and takes the zero of it nearest the last one, `Muller.next`
([quarteroni2000numerical] (6.30)). The library's theorem is about the **real** regime near a
simple real root, and that is a decision, not an oversight: there the radicand `w² - 4 f(x_k) d`
under the square root of (6.30) is automatically nonnegative
(`Muller.LocalData.nonneg_radicand`), so `Real.sqrt` is the right square root and `Muller.next` is
a genuine zero of the interpolant (`Muller.interp_next_eq_zero`). The complex regime the book
actually exploits — Muller's method started from real data finding complex roots of a polynomial —
is out of scope: a negative radicand is exactly a complex-conjugate pair of zeros of the parabola,
and pursuing it would mean running the whole iteration over `ℂ`.

The error analysis mirrors the secant one with one term more. Expanding the interpolant about the
new point, rather than naming the second zero of the parabola, gives Muller's error identity
(`Muller.sub_next_mul_eq`)
`e_{k+1} (w + d (α + x_{k+1} - 2 x_k)) = -f[x_{k-2}, x_{k-1}, x_k, α] e_{k-2} e_{k-1} e_k`,
whose left-hand factor tends to `f'(α) ≠ 0`. The sign rule of (6.30) is used exactly there, through
`|w| ≤ |den|` (`Muller.abs_linCoeff_le_abs_den`), to keep the step `x_{k+1} - x_k` short and so to
exclude the far zero of the parabola. Bounding the divided differences now needs second divided
differences at three *arbitrary* nodes, where no node can be singled out to play the role `α` plays
for the secant method; `exists_ball_abs_newton_three_sub_le` supplies them from the mean value form
`f[x, y, z] = f''(ξ)/2` (`DividedDifference.exists_newton_three_eq`: Rolle's theorem twice on `f`
minus its Newton interpolant). The resulting two-sided bound
`c |e_{k-2} e_{k-1} e_k| ≤ |e_{k+1}| ≤ C |e_{k-2} e_{k-1} e_k|` gives convergence and, when
`f⁽³⁾(α) ≠ 0`, the order `Real.tribonacci ≈ 1.8393` (`Muller.exists_ball_convergesWithOrder`,
[quarteroni2000numerical] §6.4.3, quoted there from Hildebrand without proof and printed as
`p ≃ 1.84`). The tribonacci constant is not in Mathlib; it is
`Numlib/Analysis/SpecialFunctions/Tribonacci`. In logarithmic variables the two bounds combine into
`s_{k+3} ≤ L + (2 - p) s_{k+1} + ((p - 1)/p) s_k`, whose two coefficients are positive and sum to
`1 - (p - 1)²/p < 1`, so the same monotone induction as for the golden ratio bounds the solutions
(`Muller.exists_le_mul_rpow_tribonacci`) — the companion matrix never has to be diagonalized.
-/

open Filter Topology Set

namespace DividedDifference

-- TODO(orchestrator): the three explicit formulas below belong in
-- `Numlib/Approximation/DividedDifference`, beside `newton_pair`.

section Explicit

variable (f : ℝ → ℝ) {w x y z : ℝ}

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

/-- The Newton divided difference at four nodes, explicitly. -/
theorem newton_four_eq {w : ℝ} :
    newton f ![w, x, y, z] =
      f w / ((w - x) * (w - y) * (w - z)) + f x / ((x - w) * (x - y) * (x - z)) +
        f y / ((y - w) * (y - x) * (y - z)) + f z / ((z - w) * (z - x) * (z - y)) := by
  rw [newton, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  rw [show (Finset.univ.erase (0 : Fin 4)) = {1, 2, 3} from rfl,
    show (Finset.univ.erase (1 : Fin 4)) = {0, 2, 3} from rfl,
    show (Finset.univ.erase (2 : Fin 4)) = {0, 1, 3} from rfl,
    show (Finset.univ.erase (3 : Fin 4)) = {0, 1, 2} from rfl]
  simp
  ring

/-- **A four-node divided difference through `a` is a three-node divided difference of
`dslope f a`**: `f[x, y, z, a] = g[x, y, z]` with `g = dslope f a`, for distinct `x, y, z, a`.
The four-node analogue of `DividedDifference.newton_three_eq_newton_two_dslope`, and what turns
the third divided difference of Muller's error identity into a *second* divided difference of a
function whose second derivative at the root is `f⁽³⁾(α) / 3`. -/
theorem newton_four_eq_newton_three_dslope (a : ℝ) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxa : x ≠ a) (hya : y ≠ a) (hza : z ≠ a) :
    newton f ![x, y, z, a] = newton (dslope f a) ![x, y, z] := by
  rw [newton_four_eq, newton_three_eq, dslope_of_ne f hxa, dslope_of_ne f hya,
    dslope_of_ne f hza, slope_def_field, slope_def_field, slope_def_field]
  have h1 : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h2 : x - z ≠ 0 := sub_ne_zero.2 hxz
  have h3 : y - z ≠ 0 := sub_ne_zero.2 hyz
  have h4 : x - a ≠ 0 := sub_ne_zero.2 hxa
  have h5 : y - a ≠ 0 := sub_ne_zero.2 hya
  have h6 : z - a ≠ 0 := sub_ne_zero.2 hza
  have h1' : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have h2' : z - x ≠ 0 := sub_ne_zero.2 hxz.symm
  have h3' : z - y ≠ 0 := sub_ne_zero.2 hyz.symm
  have h4' : a - x ≠ 0 := sub_ne_zero.2 hxa.symm
  have h5' : a - y ≠ 0 := sub_ne_zero.2 hya.symm
  have h6' : a - z ≠ 0 := sub_ne_zero.2 hza.symm
  field_simp
  ring

/-- Divided differences are symmetric in their nodes: swapping the first two. -/
theorem newton_three_swap₁ : newton f ![x, y, z] = newton f ![y, x, z] := by
  rw [newton_three_eq, newton_three_eq]; ring

/-- Divided differences are symmetric in their nodes: swapping the last two. -/
theorem newton_three_swap₂ : newton f ![x, y, z] = newton f ![x, z, y] := by
  rw [newton_three_eq, newton_three_eq]; ring

/-- **Newton's form of the quadratic interpolant**, read at the third node:
`f z = f x + (z - x) f[x, y] + (z - x)(z - y) f[x, y, z]` for distinct `x, y, z`. An algebraic
identity in the three values of `f`. -/
theorem newton_three_eq_of_newton_form (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    f z = f x + (z - x) * ((f y - f x) / (y - x)) + (z - x) * (z - y) * newton f ![x, y, z] := by
  rw [newton_three_eq]
  have h1 : x - y ≠ 0 := sub_ne_zero.2 hxy
  have h2 : x - z ≠ 0 := sub_ne_zero.2 hxz
  have h3 : y - z ≠ 0 := sub_ne_zero.2 hyz
  have h1' : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have h2' : z - x ≠ 0 := sub_ne_zero.2 hxz.symm
  have h3' : z - y ≠ 0 := sub_ne_zero.2 hyz.symm
  field_simp
  ring

end Explicit

section MeanValueForm

variable {f f₁ f₂ : ℝ → ℝ} {x y z : ℝ}

/-- **The mean value form of the second divided difference**, for sorted nodes: on a convex set
where `f` is twice differentiable with derivatives `f₁, f₂`, and `x < y < z` in it, there is `ξ`
in the set with `f[x, y, z] = f₂(ξ) / 2` ([han2009theoretical] §3.2). Rolle's theorem twice on
`f` minus its Newton interpolant `f(x) + (t - x) f[x, y] + (t - x)(t - y) f[x, y, z]`, whose
second derivative is `f₂ - 2 f[x, y, z]`.

Unlike the two-node case (`exists_ball_abs_slope_sub_deriv_le`, a mean value *inequality*), no
node is distinguished here, so `dslope` cannot be used to lower the order; that is why the file
carries a Rolle argument at all. -/
theorem exists_newton_three_eq_of_lt {s : Set ℝ} (hs : Convex ℝ s)
    (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z)
    (hf : ∀ u ∈ s, HasDerivAt f (f₁ u) u) (hf₁ : ∀ u ∈ s, HasDerivAt f₁ (f₂ u) u) :
    ∃ ξ ∈ s, newton f ![x, y, z] = f₂ ξ / 2 := by
  have hsub : Icc x z ⊆ s := hs.ordConnected.out hx hz
  set c : ℝ := newton f ![x, y, z] with hc
  set b : ℝ := (f y - f x) / (y - x) with hb
  set E : ℝ → ℝ := fun t => f t - (f x + (t - x) * b + (t - x) * (t - y) * c) with hE
  set E₁ : ℝ → ℝ := fun t => f₁ t - (b + ((t - x) + (t - y)) * c) with hE₁
  have hxz : x < z := hxy.trans hyz
  have hEd : ∀ u ∈ s, HasDerivAt E (E₁ u) u := fun u hu => by
    have hd1 : HasDerivAt (fun t : ℝ => (t - x) * b) b u := by
      simpa using ((hasDerivAt_id u).sub_const x).mul_const b
    have hd2 : HasDerivAt (fun t : ℝ => (t - x) * (t - y) * c) ((u - y + (u - x)) * c) u := by
      simpa using (((hasDerivAt_id u).sub_const x).mul
        ((hasDerivAt_id u).sub_const y)).mul_const c
    have h := (hf u hu).sub (((hasDerivAt_const u (f x)).add hd1).add hd2)
    simp only [hE, hE₁]
    exact h.congr_deriv (by ring)
  have hE₁d : ∀ u ∈ s, HasDerivAt E₁ (f₂ u - 2 * c) u := fun u hu => by
    have hd : HasDerivAt (fun t : ℝ => b + (t - x + (t - y)) * c) (2 * c) u := by
      have h0 := ((((hasDerivAt_id u).sub_const x).add
        ((hasDerivAt_id u).sub_const y)).mul_const c).const_add b
      exact h0.congr_deriv (by ring)
    simp only [hE₁]
    exact ((hf₁ u hu).sub hd).congr_deriv (by ring)
  have hEx : E x = 0 := by simp [hE]
  have hEy : E y = 0 := by
    have hyx : y - x ≠ 0 := sub_ne_zero.2 hxy.ne'
    simp only [hE, hb, sub_self, mul_zero, zero_mul, add_zero]
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hyx, mul_one]
    ring
  have hEz : E z = 0 := by
    have h := newton_three_eq_of_newton_form (f := f) hxy.ne hxz.ne hyz.ne
    simp only [hE, hb, hc]
    linarith
  have hsubxy : Icc x y ⊆ s := (Icc_subset_Icc le_rfl hyz.le).trans hsub
  have hsubyz : Icc y z ⊆ s := (Icc_subset_Icc hxy.le le_rfl).trans hsub
  have hcont : ∀ t : Set ℝ, t ⊆ s → ContinuousOn E t :=
    fun t ht u hu => (hEd u (ht hu)).continuousAt.continuousWithinAt
  obtain ⟨ξ₁, hξ₁, h1⟩ := exists_hasDerivAt_eq_zero hxy (hcont _ hsubxy) (hEx.trans hEy.symm)
    fun u hu => hEd u (hsubxy (Ioo_subset_Icc_self hu))
  obtain ⟨ξ₂, hξ₂, h2⟩ := exists_hasDerivAt_eq_zero hyz (hcont _ hsubyz) (hEy.trans hEz.symm)
    fun u hu => hEd u (hsubyz (Ioo_subset_Icc_self hu))
  have hξ₁₂ : ξ₁ < ξ₂ := hξ₁.2.trans hξ₂.1
  have hsub₁₂ : Icc ξ₁ ξ₂ ⊆ s := (Icc_subset_Icc hξ₁.1.le hξ₂.2.le).trans hsub
  have hcont₁ : ContinuousOn E₁ (Icc ξ₁ ξ₂) :=
    fun u hu => (hE₁d u (hsub₁₂ hu)).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, h3⟩ := exists_hasDerivAt_eq_zero hξ₁₂ hcont₁ (h1.trans h2.symm)
    fun u hu => hE₁d u (hsub₁₂ (Ioo_subset_Icc_self hu))
  exact ⟨ξ, hsub ⟨(hξ₁.1.trans hξ.1).le, (hξ.2.trans hξ₂.2).le⟩, by linarith⟩

/-- **The mean value form of the second divided difference** at three distinct nodes in a convex
set where `f` is twice differentiable: `f[x, y, z] = f₂(ξ) / 2` for some `ξ` in the set. The
sorted case `exists_newton_three_eq_of_lt` plus the symmetry of `newton` in its nodes. -/
theorem exists_newton_three_eq {s : Set ℝ} (hs : Convex ℝ s)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hf : ∀ u ∈ s, HasDerivAt f (f₁ u) u) (hf₁ : ∀ u ∈ s, HasDerivAt f₁ (f₂ u) u) :
    ∃ ξ ∈ s, newton f ![x, y, z] = f₂ ξ / 2 := by
  rcases hxy.lt_or_gt with h1 | h1
  · rcases hyz.lt_or_gt with h2 | h2
    · exact exists_newton_three_eq_of_lt hs hx hz h1 h2 hf hf₁
    · rcases hxz.lt_or_gt with h3 | h3
      · obtain ⟨ξ, hξ, hv⟩ := exists_newton_three_eq_of_lt hs hx hy h3 h2 hf hf₁
        exact ⟨ξ, hξ, by rw [newton_three_swap₂]; exact hv⟩
      · obtain ⟨ξ, hξ, hv⟩ := exists_newton_three_eq_of_lt hs hz hy h3 h1 hf hf₁
        exact ⟨ξ, hξ, by rw [newton_three_swap₂, newton_three_swap₁]; exact hv⟩
  · rcases hyz.lt_or_gt with h2 | h2
    · rcases hxz.lt_or_gt with h3 | h3
      · obtain ⟨ξ, hξ, hv⟩ := exists_newton_three_eq_of_lt hs hy hz h1 h3 hf hf₁
        exact ⟨ξ, hξ, by rw [newton_three_swap₁]; exact hv⟩
      · obtain ⟨ξ, hξ, hv⟩ := exists_newton_three_eq_of_lt hs hy hx h2 h3 hf hf₁
        exact ⟨ξ, hξ, by rw [newton_three_swap₁, newton_three_swap₂]; exact hv⟩
    · obtain ⟨ξ, hξ, hv⟩ := exists_newton_three_eq_of_lt hs hz hx h2 h1 hf hf₁
      exact ⟨ξ, hξ, by
        rw [newton_three_swap₂, newton_three_swap₁, newton_three_swap₂]; exact hv⟩

end MeanValueForm

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

-- TODO(orchestrator): a general fact about `C^N` functions; natural home
-- `Numlib/Analysis/Calculus/RootMultiplicity`, beside
-- `ContDiffOn.hasDerivAt_iteratedDeriv_of_isOpen`.

/-- **A `C^N` function is `N` times differentiable on a ball**: around a point where `f` is `C^N`
there is a ball on which each iterated derivative up to order `N - 1` has the next one as its
derivative, and the `N`-th is continuous. -/
theorem ContDiffAt.exists_ball_hasDerivAt_iteratedDeriv {f : ℝ → ℝ} {a : ℝ} {N : ℕ}
    (hf : ContDiffAt ℝ N f a) :
    ∃ δ > 0, (∀ j < N, ∀ x ∈ Metric.ball a δ,
        HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x) ∧
      ContinuousOn (iteratedDeriv N f) (Metric.ball a δ) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  exact ⟨r, hr, fun j hj x hx =>
    (hfu.mono hru).hasDerivAt_iteratedDeriv_of_isOpen Metric.isOpen_ball hj hx,
    (hfu.mono hru).continuousOn_iteratedDeriv_of_isOpen Metric.isOpen_ball le_rfl⟩

/-- **Second divided differences of a `C²` function are close to `f''(a)/2`** near a point: for
every `η > 0` there is a ball around `a` on which `|f[x, y, z] - f''(a)/2| ≤ η` for all pairwise
distinct `x, y, z` in it. The three-node analogue of `exists_ball_abs_slope_sub_deriv_le`, and —
unlike it — a genuine mean value *theorem* (`DividedDifference.exists_newton_three_eq`, Rolle
twice) rather than a mean value inequality, because no node can be singled out to lower the order
through `dslope`. -/
theorem exists_ball_abs_newton_three_sub_le {f : ℝ → ℝ} {a : ℝ} (hf : ContDiffAt ℝ 2 f a)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ, ∀ z ∈ Metric.ball a δ,
      x ≠ y → x ≠ z → y ≠ z →
      |DividedDifference.newton f ![x, y, z] - iteratedDeriv 2 f a / 2| ≤ η := by
  obtain ⟨r, hr, hd, hc⟩ :=
    ContDiffAt.exists_ball_hasDerivAt_iteratedDeriv (N := 2) (by exact_mod_cast hf)
  have hca : ContinuousAt (iteratedDeriv 2 f) a := hc.continuousAt (Metric.ball_mem_nhds a hr)
  obtain ⟨δ₁, hδ₁, hb⟩ := Metric.eventually_nhds_iff.1
    (hca.eventually (Metric.closedBall_mem_nhds (iteratedDeriv 2 f a) hη))
  refine ⟨min r δ₁, lt_min hr hδ₁, fun x hx y hy z hz hxy hxz hyz => ?_⟩
  have hsub : Metric.ball a (min r δ₁) ⊆ Metric.ball a r :=
    Metric.ball_subset_ball (min_le_left _ _)
  obtain ⟨ξ, hξ, hv⟩ := DividedDifference.exists_newton_three_eq
    (f₁ := iteratedDeriv 1 f) (f₂ := iteratedDeriv 2 f)
    (convex_ball a (min r δ₁)) hx hy hz hxy hxz hyz
    (fun u hu => by
      simpa only [iteratedDeriv_zero, zero_add] using hd 0 (by norm_num) u (hsub hu))
    (fun u hu => hd 1 (by norm_num) u (hsub hu))
  have hξ' : |iteratedDeriv 2 f ξ - iteratedDeriv 2 f a| ≤ η := by
    have h := hb (Metric.mem_ball.1 (Metric.ball_subset_ball (min_le_right r δ₁) hξ))
    rwa [Real.dist_eq] at h
  rw [hv, show iteratedDeriv 2 f ξ / 2 - iteratedDeriv 2 f a / 2
    = (iteratedDeriv 2 f ξ - iteratedDeriv 2 f a) / 2 by ring, abs_div, abs_two]
  linarith

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

open DividedDifference

/-! ### The quadratic interpolant -/

/-- The **leading coefficient of the Muller interpolant**, the second divided difference
`d = f[x_k, x_{k-1}, x_{k-2}]` of [quarteroni2000numerical] §6.4.3. -/
noncomputable def quadCoeff (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) : ℝ := newton f ![x₂, x₁, x₀]

/-- The **linear coefficient of the Muller interpolant** at `x_k`, the `w` of
[quarteroni2000numerical] §6.4.3: `w = f[x_k, x_{k-1}] + (x_k - x_{k-1}) f[x_k, x_{k-1}, x_{k-2}]`,
so that the interpolant reads `p₂(x) = f(x_k) + w (x - x_k) + d (x - x_k)²`. -/
noncomputable def linCoeff (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) : ℝ :=
  newton f ![x₂, x₁] + (x₂ - x₁) * quadCoeff f x₀ x₁ x₂

/-- The **radicand** `w² - 4 f(x_k) d` under the square root of (6.30). It is nonnegative near a
simple real root (`Muller.LocalData.nonneg_radicand`), where `w → f'(α) ≠ 0` and `f(x_k) → 0`, but
not in general: a negative radicand is exactly the case of a complex-conjugate pair of zeros of the
parabola, which is what makes the complex form of the method find complex roots. -/
noncomputable def radicand (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) : ℝ :=
  linCoeff f x₀ x₁ x₂ ^ 2 - 4 * f x₂ * quadCoeff f x₀ x₁ x₂

/-- The **denominator** of (6.30), `w ± √(w² - 4 f(x_k) d)` with the sign chosen to maximize its
modulus. The choice is what makes the step pick the zero of the parabola *nearest* to `x_k`, and it
enters the analysis through `Muller.abs_linCoeff_le_abs_den`. -/
noncomputable def den (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) : ℝ :=
  if |linCoeff f x₀ x₁ x₂ - Real.sqrt (radicand f x₀ x₁ x₂)|
      ≤ |linCoeff f x₀ x₁ x₂ + Real.sqrt (radicand f x₀ x₁ x₂)| then
    linCoeff f x₀ x₁ x₂ + Real.sqrt (radicand f x₀ x₁ x₂)
  else linCoeff f x₀ x₁ x₂ - Real.sqrt (radicand f x₀ x₁ x₂)

/-- The **new point of a Muller step**, `x_{k+1} = x_k - 2 f(x_k) / den`
([quarteroni2000numerical] (6.30), with the numerator rationalized). -/
noncomputable def next (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) : ℝ := x₂ - 2 * f x₂ / den f x₀ x₁ x₂

/-- The **quadratic interpolant** of `f` at `x_{k-2}, x_{k-1}, x_k` in Newton's form based at
`x_k`, `p₂(t) = f(x_k) + w (t - x_k) + d (t - x_k)²` ([quarteroni2000numerical] §6.4.3). It
interpolates (`Muller.interp_apply_node`) and `Muller.next` is one of its zeros
(`Muller.interp_next_eq_zero`). -/
noncomputable def interp (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) (t : ℝ) : ℝ :=
  f x₂ + linCoeff f x₀ x₁ x₂ * (t - x₂) + quadCoeff f x₀ x₁ x₂ * (t - x₂) ^ 2

variable {f : ℝ → ℝ} {α ε η x₀ x₁ x₂ : ℝ}

/-- One **Muller step** ([quarteroni2000numerical] (6.30)) from the triple
`(x_{k-2}, x_{k-1}, x_k)` to `(x_{k-1}, x_k, x_{k+1})`, where `x_{k+1} = Muller.next` is the zero
`x_k - 2 f(x_k) / (w ± √(w² - 4 f(x_k) d))` of the quadratic interpolant nearest to `x_k`, the sign
maximizing the modulus of the denominator. Real arithmetic only: the square root is `Real.sqrt`,
junk `0` for a negative radicand (a complex pair of zeros of the parabola), where the complex
version that finds complex roots of polynomials would continue with `Complex.cpow`. -/
noncomputable def step (f : ℝ → ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (s.2.1, s.2.2, next f s.1 s.2.1 s.2.2)

/-- **The Newton form interpolates**: `p₂` takes the value of `f` at each of the three nodes, for
distinct nodes. This is what makes `Muller.interp` *the* quadratic interpolant, and it is the piece
that ties `Muller.step` to [quarteroni2000numerical] §6.4.3. -/
theorem interp_apply_node (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂) :
    interp f x₀ x₁ x₂ x₀ = f x₀ ∧ interp f x₀ x₁ x₂ x₁ = f x₁ ∧
      interp f x₀ x₁ x₂ x₂ = f x₂ := by
  have a01 : x₀ - x₁ ≠ 0 := sub_ne_zero.2 h01
  have a02 : x₀ - x₂ ≠ 0 := sub_ne_zero.2 h02
  have a12 : x₁ - x₂ ≠ 0 := sub_ne_zero.2 h12
  have a10 : x₁ - x₀ ≠ 0 := sub_ne_zero.2 h01.symm
  have a20 : x₂ - x₀ ≠ 0 := sub_ne_zero.2 h02.symm
  have a21 : x₂ - x₁ ≠ 0 := sub_ne_zero.2 h12.symm
  refine ⟨?_, ?_, by simp [interp]⟩ <;>
    · rw [interp, linCoeff, quadCoeff, newton_three_eq, newton_two_eq _ h12.symm]
      field_simp
      ring

/-- **The sign rule makes the denominator at least as large as `w`**: `|w| ≤ |den|`, because
`2|w| = |(w + r) + (w - r)| ≤ |w + r| + |w - r|` and `den` is whichever of `w ± r` has the larger
modulus. This one inequality is the whole content of the sign rule for the error analysis: it is
what keeps `x_{k+1}` near `x_k` rather than at the far zero of the parabola. -/
theorem abs_linCoeff_le_abs_den (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) :
    |linCoeff f x₀ x₁ x₂| ≤ |den f x₀ x₁ x₂| := by
  rw [den]
  set w := linCoeff f x₀ x₁ x₂
  set r := Real.sqrt (radicand f x₀ x₁ x₂)
  have key : 2 * |w| ≤ |w + r| + |w - r| := by
    have h := abs_add_le (w + r) (w - r)
    rwa [show (w + r) + (w - r) = 2 * w by ring, abs_mul, abs_two] at h
  split_ifs with h
  · linarith
  · linarith [not_le.1 h]

/-- **The denominator solves `den² - 2 w den + 4 d f(x_k) = 0`** when the radicand is nonnegative,
since `den = w ± r` with `r² = w² - 4 f(x_k) d`. -/
theorem den_quadratic (hrad : 0 ≤ radicand f x₀ x₁ x₂) :
    den f x₀ x₁ x₂ ^ 2 - 2 * linCoeff f x₀ x₁ x₂ * den f x₀ x₁ x₂ +
      4 * quadCoeff f x₀ x₁ x₂ * f x₂ = 0 := by
  have hr : Real.sqrt (radicand f x₀ x₁ x₂) ^ 2
      = linCoeff f x₀ x₁ x₂ ^ 2 - 4 * f x₂ * quadCoeff f x₀ x₁ x₂ := by
    rw [Real.sq_sqrt hrad, radicand]
  rw [den]
  split_ifs <;> linear_combination hr

/-- **The Muller step lands on a zero of the quadratic interpolant** — this is the defining
property of the method, and it needs the radicand to be nonnegative (real arithmetic) and the
denominator to be nonzero. With `h = -2 f(x_k)/den`,
`p₂(x_k + h) = f(x_k) (den² - 2 w den + 4 d f(x_k)) / den²`, which vanishes by
`Muller.den_quadratic`. -/
theorem interp_next_eq_zero (hrad : 0 ≤ radicand f x₀ x₁ x₂) (hden : den f x₀ x₁ x₂ ≠ 0) :
    interp f x₀ x₁ x₂ (next f x₀ x₁ x₂) = 0 := by
  have hkey := den_quadratic (f := f) (x₀ := x₀) (x₁ := x₁) (x₂ := x₂) hrad
  rw [interp, next]
  field_simp
  linear_combination f x₂ * hkey

/-- **The value of the interpolant at the root** is the divided-difference form of the
interpolation error there: for `f α = 0` and distinct nodes different from `α`,
`p₂(α) = -f[x_{k-2}, x_{k-1}, x_k, α] (α - x_{k-2})(α - x_{k-1})(α - x_k)`. The four-node analogue
of `Secant.sub_root_eq_mul_newton`, and like it an algebraic identity in the values of `f`
([han2009theoretical] (3.2.5) written out). -/
theorem interp_root_eq (hα : f α = 0) (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂)
    (h0 : x₀ ≠ α) (h1 : x₁ ≠ α) (h2 : x₂ ≠ α) :
    interp f x₀ x₁ x₂ α =
      -(newton f ![x₀, x₁, x₂, α] * ((α - x₀) * (α - x₁) * (α - x₂))) := by
  rw [interp, linCoeff, quadCoeff, newton_three_eq, newton_two_eq _ h12.symm, newton_four_eq, hα]
  have a01 : x₀ - x₁ ≠ 0 := sub_ne_zero.2 h01
  have a02 : x₀ - x₂ ≠ 0 := sub_ne_zero.2 h02
  have a12 : x₁ - x₂ ≠ 0 := sub_ne_zero.2 h12
  have a10 : x₁ - x₀ ≠ 0 := sub_ne_zero.2 h01.symm
  have a20 : x₂ - x₀ ≠ 0 := sub_ne_zero.2 h02.symm
  have a21 : x₂ - x₁ ≠ 0 := sub_ne_zero.2 h12.symm
  have b0 : x₀ - α ≠ 0 := sub_ne_zero.2 h0
  have b1 : x₁ - α ≠ 0 := sub_ne_zero.2 h1
  have b2 : x₂ - α ≠ 0 := sub_ne_zero.2 h2
  have c0 : α - x₀ ≠ 0 := sub_ne_zero.2 h0.symm
  have c1 : α - x₁ ≠ 0 := sub_ne_zero.2 h1.symm
  have c2 : α - x₂ ≠ 0 := sub_ne_zero.2 h2.symm
  field_simp
  ring

/-- **Muller's error identity.** With `e_j = α - x_j` and `d, w` the coefficients of the
interpolant, the new error satisfies

`e_{k+1} (w + d (α + x_{k+1} - 2 x_k)) = -f[x_{k-2}, x_{k-1}, x_k, α] e_{k-2} e_{k-1} e_k`.

The factor on the left is `p₂'(x_{k+1}) + d e_{k+1}`, which tends to `f'(α) ≠ 0`; the second zero
of the parabola is eliminated not by naming it but by expanding `p₂` about `x_{k+1}`, where
`p₂(x_{k+1}) = 0` (`Muller.interp_next_eq_zero`) leaves `p₂(α) = e_{k+1} (p₂'(x_{k+1}) + d e_{k+1})`
exactly. Compare `Secant.sub_root_eq_mul_newton`, where the corresponding relation is linear in the
new error. -/
theorem sub_next_mul_eq (hα : f α = 0) (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂)
    (h0 : x₀ ≠ α) (h1 : x₁ ≠ α) (h2 : x₂ ≠ α)
    (hrad : 0 ≤ radicand f x₀ x₁ x₂) (hden : den f x₀ x₁ x₂ ≠ 0) :
    (α - next f x₀ x₁ x₂) * (linCoeff f x₀ x₁ x₂ +
        quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂)) =
      -(newton f ![x₀, x₁, x₂, α] * ((α - x₀) * (α - x₁) * (α - x₂))) := by
  have h := interp_next_eq_zero hrad hden
  rw [← interp_root_eq hα h01 h02 h12 h0 h1 h2, ← sub_zero (interp f x₀ x₁ x₂ α), ← h,
    interp, interp]
  ring

/-! ### Local bounds -/

/-- **The local bounds driving the Muller analysis** on `ball α ε`, all with the same tolerance
`η`: the first divided difference at distinct nodes is within `η` of `f'(α)`, the second at three
distinct nodes within `η` of `f''(α)/2`, the third through `α` within `η` of `f⁽³⁾(α)/6`, and
`dslope f α` within `η` of `f'(α)`. `Muller.exists_localData` produces them near a simple root of a
`C³` function. -/
structure LocalData (f : ℝ → ℝ) (α ε η : ℝ) : Prop where
  first : ∀ x ∈ Metric.ball α ε, ∀ y ∈ Metric.ball α ε, x ≠ y →
    |newton f ![x, y] - deriv f α| ≤ η
  second : ∀ x ∈ Metric.ball α ε, ∀ y ∈ Metric.ball α ε, ∀ z ∈ Metric.ball α ε,
    x ≠ y → x ≠ z → y ≠ z → |newton f ![x, y, z] - iteratedDeriv 2 f α / 2| ≤ η
  third : ∀ x ∈ Metric.ball α ε, ∀ y ∈ Metric.ball α ε, ∀ z ∈ Metric.ball α ε,
    x ≠ y → x ≠ z → y ≠ z → x ≠ α → y ≠ α → z ≠ α →
    |newton f ![x, y, z, α] - iteratedDeriv 3 f α / 6| ≤ η
  base : ∀ x ∈ Metric.ball α ε, |dslope f α x - deriv f α| ≤ η

/-- Local bounds persist on a smaller ball. -/
theorem LocalData.mono (h : LocalData f α ε η) {ε' : ℝ} (hle : ε' ≤ ε) : LocalData f α ε' η :=
  ⟨fun x hx y hy => h.first x (Metric.ball_subset_ball hle hx) y (Metric.ball_subset_ball hle hy),
   fun x hx y hy z hz => h.second x (Metric.ball_subset_ball hle hx) y
      (Metric.ball_subset_ball hle hy) z (Metric.ball_subset_ball hle hz),
   fun x hx y hy z hz => h.third x (Metric.ball_subset_ball hle hx) y
      (Metric.ball_subset_ball hle hy) z (Metric.ball_subset_ball hle hz),
   fun x hx => h.base x (Metric.ball_subset_ball hle hx)⟩

/-- **The smallness conditions** on the ball radius `ε` and the tolerance `η` that the Muller step
estimates need, all relative to `|f'(α)|` and the bound `|f''(α)|/2 + η` on the second divided
difference: `8 η ≤ |f'(α)|` keeps `w` within `|f'(α)|/4` of `f'(α)`, the second makes the
`(x_k - x_{k-1}) d` term of `w` small, and the third makes `4 f(x_k) d` small enough for the
radicand to stay nonnegative and the step `x_{k+1} - x_k` short. -/
structure Small (f : ℝ → ℝ) (α ε η : ℝ) : Prop where
  eps_pos : 0 < ε
  eta_pos : 0 < η
  deriv_ne : deriv f α ≠ 0
  eta_le : 8 * η ≤ |deriv f α|
  eps_le : 16 * (ε * (|iteratedDeriv 2 f α| / 2 + η)) ≤ |deriv f α|
  eps_le' : 32 * (ε * ((|deriv f α| + η) * (|iteratedDeriv 2 f α| / 2 + η))) ≤ |deriv f α| ^ 2

/-- A triple `(x_{k-2}, x_{k-1}, x_k)` of consecutive Muller iterates is **admissible** in
`ball α ε` when all three points lie in the ball, are pairwise distinct, and differ from `α`:
exactly what the error identity `Muller.sub_next_mul_eq` needs. -/
structure IsAdmissible (α ε x₀ x₁ x₂ : ℝ) : Prop where
  mem₀ : x₀ ∈ Metric.ball α ε
  mem₁ : x₁ ∈ Metric.ball α ε
  mem₂ : x₂ ∈ Metric.ball α ε
  ne₀₁ : x₀ ≠ x₁
  ne₀₂ : x₀ ≠ x₂
  ne₁₂ : x₁ ≠ x₂
  ne₀ : x₀ ≠ α
  ne₁ : x₁ ≠ α
  ne₂ : x₂ ≠ α

/-- The oldest point of an admissible triple is within `ε` of the root. -/
theorem IsAdmissible.abs_lt₀ (hs : IsAdmissible α ε x₀ x₁ x₂) : |x₀ - α| < ε := by
  rw [← Real.dist_eq]; exact Metric.mem_ball.1 hs.mem₀

/-- An admissible triple exists only in a ball of positive radius. -/
theorem IsAdmissible.eps_pos (hs : IsAdmissible α ε x₀ x₁ x₂) : 0 < ε :=
  lt_of_le_of_lt (abs_nonneg _) hs.abs_lt₀

/-- The middle point of an admissible triple is within `ε` of the root. -/
theorem IsAdmissible.abs_lt₁ (hs : IsAdmissible α ε x₀ x₁ x₂) : |x₁ - α| < ε := by
  rw [← Real.dist_eq]; exact Metric.mem_ball.1 hs.mem₁

/-- The newest point of an admissible triple is within `ε` of the root. -/
theorem IsAdmissible.abs_lt₂ (hs : IsAdmissible α ε x₀ x₁ x₂) : |x₂ - α| < ε := by
  rw [← Real.dist_eq]; exact Metric.mem_ball.1 hs.mem₂

/-- The leading coefficient of the interpolant is bounded by `|f''(α)|/2 + η`. -/
theorem LocalData.abs_quadCoeff_le (hdata : LocalData f α ε η)
    (hs : IsAdmissible α ε x₀ x₁ x₂) :
    |quadCoeff f x₀ x₁ x₂| ≤ |iteratedDeriv 2 f α| / 2 + η := by
  have h := hdata.second x₂ hs.mem₂ x₁ hs.mem₁ x₀ hs.mem₀ hs.ne₁₂.symm hs.ne₀₂.symm hs.ne₀₁.symm
  have h2 := abs_sub_abs_le_abs_sub (newton f ![x₂, x₁, x₀]) (iteratedDeriv 2 f α / 2)
  rw [abs_div, abs_two] at h2
  rw [quadCoeff]
  linarith

/-- `|f(x_k)| ≤ ε (|f'(α)| + η)` on the ball, from `f(x) = (x - α) · dslope f α x`. -/
theorem LocalData.abs_apply_le (hα : f α = 0) (hdata : LocalData f α ε η)
    (hs : IsAdmissible α ε x₀ x₁ x₂) : |f x₂| ≤ ε * (|deriv f α| + η) := by
  have hds : f x₂ = (x₂ - α) * dslope f α x₂ := by
    have h := sub_smul_dslope f α x₂
    rw [hα, sub_zero, smul_eq_mul] at h
    exact h.symm
  have hdsb : |dslope f α x₂| ≤ |deriv f α| + η := by
    have h := hdata.base x₂ hs.mem₂
    have h2 := abs_sub_abs_le_abs_sub (dslope f α x₂) (deriv f α)
    linarith
  rw [hds, abs_mul]
  exact mul_le_mul hs.abs_lt₂.le hdsb (abs_nonneg _) hs.eps_pos.le

/-- **The linear coefficient is close to `f'(α)`**: `|w - f'(α)| ≤ |f'(α)|/4`, since
`w = f[x_k, x_{k-1}] + (x_k - x_{k-1}) d` with the first term within `η` of `f'(α)` and
`|x_k - x_{k-1}| < 2ε`. -/
theorem LocalData.abs_linCoeff_sub_le (hdata : LocalData f α ε η) (hsm : Small f α ε η)
    (hs : IsAdmissible α ε x₀ x₁ x₂) :
    |linCoeff f x₀ x₁ x₂ - deriv f α| ≤ |deriv f α| / 4 := by
  have hd := hdata.abs_quadCoeff_le hs
  have hfirst := hdata.first x₂ hs.mem₂ x₁ hs.mem₁ hs.ne₁₂.symm
  have hx : |x₂ - x₁| ≤ 2 * ε := by
    calc |x₂ - x₁| ≤ |x₂ - α| + |α - x₁| := abs_sub_le _ _ _
      _ ≤ 2 * ε := by rw [abs_sub_comm α x₁]; linarith [hs.abs_lt₁, hs.abs_lt₂]
  have hmul : |(x₂ - x₁) * quadCoeff f x₀ x₁ x₂| ≤ 2 * ε * (|iteratedDeriv 2 f α| / 2 + η) := by
    rw [abs_mul]
    exact mul_le_mul hx hd (abs_nonneg _) (by linarith [hs.eps_pos])
  have htri : |linCoeff f x₀ x₁ x₂ - deriv f α|
      ≤ |newton f ![x₂, x₁] - deriv f α| + |(x₂ - x₁) * quadCoeff f x₀ x₁ x₂| := by
    rw [linCoeff, show newton f ![x₂, x₁] + (x₂ - x₁) * quadCoeff f x₀ x₁ x₂ - deriv f α
      = (newton f ![x₂, x₁] - deriv f α) + (x₂ - x₁) * quadCoeff f x₀ x₁ x₂ by ring]
    exact abs_add_le _ _
  linarith [hsm.eta_le, hsm.eps_le]

/-- `3 |f'(α)| / 4 ≤ |w|`. -/
theorem LocalData.le_abs_linCoeff (hdata : LocalData f α ε η) (hsm : Small f α ε η)
    (hs : IsAdmissible α ε x₀ x₁ x₂) : 3 * |deriv f α| / 4 ≤ |linCoeff f x₀ x₁ x₂| := by
  have h := hdata.abs_linCoeff_sub_le hsm hs
  have h2 := abs_sub_abs_le_abs_sub (deriv f α) (linCoeff f x₀ x₁ x₂)
  rw [abs_sub_comm] at h2
  linarith

/-- `|w| ≤ 5 |f'(α)| / 4`. -/
theorem LocalData.abs_linCoeff_le (hdata : LocalData f α ε η) (hsm : Small f α ε η)
    (hs : IsAdmissible α ε x₀ x₁ x₂) : |linCoeff f x₀ x₁ x₂| ≤ 5 * |deriv f α| / 4 := by
  have h := hdata.abs_linCoeff_sub_le hsm hs
  have h2 := abs_sub_abs_le_abs_sub (linCoeff f x₀ x₁ x₂) (deriv f α)
  linarith

/-- **The radicand is nonnegative near a simple real root**, so the real form of Muller's method
is the right one there: `w² ≥ 9 f'(α)²/16` while `|4 f(x_k) d| ≤ |f'(α)|²/8`. This is the
hypothesis of `Muller.interp_next_eq_zero` discharged. -/
theorem LocalData.nonneg_radicand (hα : f α = 0) (hdata : LocalData f α ε η)
    (hsm : Small f α ε η) (hs : IsAdmissible α ε x₀ x₁ x₂) : 0 ≤ radicand f x₀ x₁ x₂ := by
  have ha : 0 < |deriv f α| := abs_pos.2 hsm.deriv_ne
  have hwlo := hdata.le_abs_linCoeff hsm hs
  have hd := hdata.abs_quadCoeff_le hs
  have hfx := hdata.abs_apply_le hα hs
  have hlin2 : (3 * |deriv f α| / 4) ^ 2 ≤ linCoeff f x₀ x₁ x₂ ^ 2 := by
    rw [← sq_abs (linCoeff f x₀ x₁ x₂)]
    exact pow_le_pow_left₀ (by positivity) hwlo 2
  have hprod : |4 * f x₂ * quadCoeff f x₀ x₁ x₂|
      ≤ 4 * (ε * (|deriv f α| + η)) * (|iteratedDeriv 2 f α| / 2 + η) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    refine mul_le_mul (mul_le_mul_of_nonneg_left hfx (by norm_num)) hd (abs_nonneg _) ?_
    exact mul_nonneg (by norm_num) (mul_nonneg hs.eps_pos.le
      (by linarith [abs_nonneg (deriv f α), hsm.eta_pos]))
  rw [radicand]
  linarith [(abs_le.1 hprod).2, hsm.eps_le', sq_nonneg (deriv f α), sq_abs (deriv f α)]

/-- `3 |f'(α)| / 4 ≤ |den|`, by the sign rule (`Muller.abs_linCoeff_le_abs_den`). -/
theorem LocalData.le_abs_den (hdata : LocalData f α ε η) (hsm : Small f α ε η)
    (hs : IsAdmissible α ε x₀ x₁ x₂) : 3 * |deriv f α| / 4 ≤ |den f x₀ x₁ x₂| :=
  (hdata.le_abs_linCoeff hsm hs).trans (abs_linCoeff_le_abs_den f x₀ x₁ x₂)

/-- The denominator of a Muller step from an admissible triple is nonzero. -/
theorem LocalData.den_ne_zero (hdata : LocalData f α ε η) (hsm : Small f α ε η)
    (hs : IsAdmissible α ε x₀ x₁ x₂) : den f x₀ x₁ x₂ ≠ 0 := fun h => by
  have ha : 0 < |deriv f α| := abs_pos.2 hsm.deriv_ne
  have h2 := hdata.le_abs_den hsm hs
  rw [h, abs_zero] at h2
  linarith

/-- **The step is short**: `|d| |x_{k+1} - x_k| ≤ |f'(α)| / 12`, since
`|x_{k+1} - x_k| |den| = 2 |f(x_k)|` with `|f(x_k)|` of order `ε` and `|den|` bounded below. -/
theorem LocalData.abs_quadCoeff_mul_next_sub_le (hα : f α = 0) (hdata : LocalData f α ε η)
    (hsm : Small f α ε η) (hs : IsAdmissible α ε x₀ x₁ x₂) :
    |quadCoeff f x₀ x₁ x₂| * |next f x₀ x₁ x₂ - x₂| ≤ |deriv f α| / 12 := by
  have ha : 0 < |deriv f α| := abs_pos.2 hsm.deriv_ne
  have hd := hdata.abs_quadCoeff_le hs
  have hfx := hdata.abs_apply_le hα hs
  have hden0 := hdata.den_ne_zero hsm hs
  have hnx : |next f x₀ x₁ x₂ - x₂| * |den f x₀ x₁ x₂| = 2 * |f x₂| := by
    rw [next, show x₂ - 2 * f x₂ / den f x₀ x₁ x₂ - x₂ = -(2 * f x₂ / den f x₀ x₁ x₂) by ring,
      abs_neg, abs_div, div_mul_cancel₀ _ (abs_ne_zero.2 hden0), abs_mul]
    norm_num
  have hstep : |next f x₀ x₁ x₂ - x₂| * (3 * |deriv f α| / 4) ≤ 2 * (ε * (|deriv f α| + η)) := by
    have h1 : |next f x₀ x₁ x₂ - x₂| * (3 * |deriv f α| / 4)
        ≤ |next f x₀ x₁ x₂ - x₂| * |den f x₀ x₁ x₂| :=
      mul_le_mul_of_nonneg_left (hdata.le_abs_den hsm hs) (abs_nonneg _)
    rw [hnx] at h1
    linarith
  have e1 : |quadCoeff f x₀ x₁ x₂| * (|next f x₀ x₁ x₂ - x₂| * (3 * |deriv f α| / 4))
      ≤ (|iteratedDeriv 2 f α| / 2 + η) * (2 * (ε * (|deriv f α| + η))) :=
    mul_le_mul hd hstep (mul_nonneg (abs_nonneg _) (by positivity))
      (by linarith [abs_nonneg (iteratedDeriv 2 f α), hsm.eta_pos])
  refine le_of_mul_le_mul_right ?_ (show (0:ℝ) < 3 * |deriv f α| / 4 by positivity)
  linarith [e1, hsm.eps_le', sq_abs (deriv f α)]

/-- **The factor in Muller's error identity is close to `f'(α)`**:
`|f'(α)|/2 ≤ |w + d (α + x_{k+1} - 2 x_k)| ≤ 3 |f'(α)|/2`, because `α + x_{k+1} - 2 x_k` is
`(α - x_k) + (x_{k+1} - x_k)`, both short. This is where the sign rule of (6.30) is used: it is
what bounds `x_{k+1} - x_k`, and hence excludes the far zero of the parabola. -/
theorem LocalData.effSlope_bounds (hα : f α = 0) (hdata : LocalData f α ε η)
    (hsm : Small f α ε η) (hs : IsAdmissible α ε x₀ x₁ x₂) :
    |deriv f α| / 2 ≤ |linCoeff f x₀ x₁ x₂ +
        quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂)| ∧
      |linCoeff f x₀ x₁ x₂ + quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂)|
        ≤ 3 * |deriv f α| / 2 := by
  have ha : 0 < |deriv f α| := abs_pos.2 hsm.deriv_ne
  have hd := hdata.abs_quadCoeff_le hs
  have h3 := hdata.abs_quadCoeff_mul_next_sub_le hα hsm hs
  have h2 : |quadCoeff f x₀ x₁ x₂| * |x₂ - α| ≤ |deriv f α| / 16 := by
    have h : |quadCoeff f x₀ x₁ x₂| * |x₂ - α| ≤ (|iteratedDeriv 2 f α| / 2 + η) * ε :=
      mul_le_mul hd hs.abs_lt₂.le (abs_nonneg _)
        (by linarith [abs_nonneg (iteratedDeriv 2 f α), hsm.eta_pos])
    linarith [hsm.eps_le]
  have hsplit : |α + next f x₀ x₁ x₂ - 2 * x₂| ≤ |x₂ - α| + |next f x₀ x₁ x₂ - x₂| := by
    rw [show α + next f x₀ x₁ x₂ - 2 * x₂ = -(x₂ - α) + (next f x₀ x₁ x₂ - x₂) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
  have hsub : |quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂)|
      ≤ 7 * |deriv f α| / 48 := by
    rw [abs_mul]
    have h4 := mul_le_mul_of_nonneg_left hsplit (abs_nonneg (quadCoeff f x₀ x₁ x₂))
    linarith
  have hwlo := hdata.le_abs_linCoeff hsm hs
  have hwhi := hdata.abs_linCoeff_le hsm hs
  refine ⟨?_, ?_⟩
  · have h := abs_sub_abs_le_abs_sub (linCoeff f x₀ x₁ x₂)
      (linCoeff f x₀ x₁ x₂ + quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂))
    rw [show linCoeff f x₀ x₁ x₂ - (linCoeff f x₀ x₁ x₂ +
      quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂))
      = -(quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂)) by ring, abs_neg] at h
    linarith
  · have h := abs_add_le (linCoeff f x₀ x₁ x₂)
      (quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂))
    linarith

/-- **Local bounds near a simple root of a `C³` function.** For every `η > 0` there is a ball
around `α` carrying `Muller.LocalData`. The third divided difference is handled by
`DividedDifference.newton_four_eq_newton_three_dslope`, which turns `f[x, y, z, α]` into the second
divided difference of `g = dslope f α`, a `C²` function at `α` with
`g''(α)/2 = f⁽³⁾(α)/6` (Hadamard's lemma, `ContDiffAt.dslope_same` and
`iteratedDeriv_dslope_same`). -/
theorem exists_localData (hf : ContDiffAt ℝ 3 f α) (hη : 0 < η) :
    ∃ ε > 0, LocalData f α ε η := by
  have hf1 : ContDiffAt ℝ 1 f α := hf.of_le (by norm_num)
  have hf2 : ContDiffAt ℝ 2 f α := hf.of_le (by norm_num)
  have hf3 : ContDiffAt ℝ ((2 : ℕ) + 1 : ℕ) f α := by simpa using hf
  have hg : ContDiffAt ℝ ((2 : ℕ)) (dslope f α) α := ContDiffAt.dslope_same (n := 2) hf3
  have hgd : iteratedDeriv 2 (dslope f α) α / 2 = iteratedDeriv 3 f α / 6 := by
    rw [iteratedDeriv_dslope_same hf3]
    norm_num
    ring
  obtain ⟨δ₁, hδ₁, h₁⟩ := exists_ball_abs_slope_sub_deriv_le hf1 hη
  obtain ⟨δ₂, hδ₂, h₂⟩ := exists_ball_abs_newton_three_sub_le hf2 hη
  obtain ⟨δ₃, hδ₃, h₃⟩ := exists_ball_abs_newton_three_sub_le (by exact_mod_cast hg) hη
  obtain ⟨δ₄, hδ₄, h₄⟩ := Metric.eventually_nhds_iff.1
    (hg.continuousAt.eventually (Metric.closedBall_mem_nhds (dslope f α α) hη))
  have m₁ : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have m₂ : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have m₃ : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₃ := (min_le_right _ _).trans (min_le_left _ _)
  have m₄ : min (min δ₁ δ₂) (min δ₃ δ₄) ≤ δ₄ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min (min δ₁ δ₂) (min δ₃ δ₄), by positivity, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [newton_two_eq _ hxy]
    exact h₁ x (Metric.ball_subset_ball m₁ hx) y (Metric.ball_subset_ball m₁ hy) hxy
  · intro x hx y hy z hz hxy hxz hyz
    exact h₂ x (Metric.ball_subset_ball m₂ hx) y (Metric.ball_subset_ball m₂ hy) z
      (Metric.ball_subset_ball m₂ hz) hxy hxz hyz
  · intro x hx y hy z hz hxy hxz hyz hxα hyα hzα
    rw [newton_four_eq_newton_three_dslope f α hxy hxz hyz hxα hyα hzα, ← hgd]
    exact h₃ x (Metric.ball_subset_ball m₃ hx) y (Metric.ball_subset_ball m₃ hy) z
      (Metric.ball_subset_ball m₃ hz) hxy hxz hyz
  · intro x hx
    have h := h₄ (Metric.ball_subset_ball m₄ hx)
    rw [Real.dist_eq, dslope_same] at h
    exact h

/-! ### One step -/

/-- **One Muller step from an admissible triple.** Under the local bounds and the smallness
conditions, with `m` and `M` chosen so that `m (3|f'(α)|/2) ≤ |f⁽³⁾(α)|/6 - η` and
`|f⁽³⁾(α)|/6 + η ≤ M (|f'(α)|/2)` and `M ε² ≤ 1/2`, the new point obeys the two-sided error bound

`m |e_{k-2} e_{k-1} e_k| ≤ |e_{k+1}| ≤ M |e_{k-2} e_{k-1} e_k|`,

stays in the ball and differs from the two previous iterates. Muller's error identity
(`Muller.sub_next_mul_eq`) divided by the factor bounded in `Muller.LocalData.effSlope_bounds`. -/
theorem LocalData.step_bounds (hα : f α = 0) (hdata : LocalData f α ε η) (hsm : Small f α ε η)
    {m M : ℝ} (hm : m * (3 * |deriv f α| / 2) ≤ |iteratedDeriv 3 f α| / 6 - η)
    (hM : |iteratedDeriv 3 f α| / 6 + η ≤ M * (|deriv f α| / 2)) (hMε : M * ε ^ 2 ≤ 1 / 2)
    (hs : IsAdmissible α ε x₀ x₁ x₂) :
    m * (|x₀ - α| * |x₁ - α| * |x₂ - α|) ≤ |next f x₀ x₁ x₂ - α| ∧
      |next f x₀ x₁ x₂ - α| ≤ M * (|x₀ - α| * |x₁ - α| * |x₂ - α|) ∧
      next f x₀ x₁ x₂ ∈ Metric.ball α ε ∧
      next f x₀ x₁ x₂ ≠ x₁ ∧ next f x₀ x₁ x₂ ≠ x₂ := by
  have ha : 0 < |deriv f α| := abs_pos.2 hsm.deriv_ne
  have habs6 : |iteratedDeriv 3 f α / 6| = |iteratedDeriv 3 f α| / 6 := by
    rw [abs_div]; norm_num
  have hN := hdata.third x₀ hs.mem₀ x₁ hs.mem₁ x₂ hs.mem₂ hs.ne₀₁ hs.ne₀₂ hs.ne₁₂ hs.ne₀ hs.ne₁
    hs.ne₂
  have hNlo : |iteratedDeriv 3 f α| / 6 - η ≤ |newton f ![x₀, x₁, x₂, α]| := by
    have h := abs_sub_abs_le_abs_sub (iteratedDeriv 3 f α / 6) (newton f ![x₀, x₁, x₂, α])
    rw [abs_sub_comm, habs6] at h
    linarith
  have hNhi : |newton f ![x₀, x₁, x₂, α]| ≤ |iteratedDeriv 3 f α| / 6 + η := by
    have h := abs_sub_abs_le_abs_sub (newton f ![x₀, x₁, x₂, α]) (iteratedDeriv 3 f α / 6)
    rw [habs6] at h
    linarith
  obtain ⟨hLlo, hLhi⟩ := hdata.effSlope_bounds hα hsm hs
  have hident : |next f x₀ x₁ x₂ - α| *
      |linCoeff f x₀ x₁ x₂ + quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂)|
      = |newton f ![x₀, x₁, x₂, α]| * (|x₀ - α| * |x₁ - α| * |x₂ - α|) := by
    have h := sub_next_mul_eq hα hs.ne₀₁ hs.ne₀₂ hs.ne₁₂ hs.ne₀ hs.ne₁ hs.ne₂
      (hdata.nonneg_radicand hα hsm hs) (hdata.den_ne_zero hsm hs)
    have h' := congrArg abs h
    rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_mul, abs_sub_comm α x₀, abs_sub_comm α x₁,
      abs_sub_comm α x₂] at h'
    rw [abs_sub_comm (next f x₀ x₁ x₂) α, h']
  have hP : 0 ≤ |x₀ - α| * |x₁ - α| * |x₂ - α| := by positivity
  have hM0 : 0 < M := by
    have h : 0 < M * (|deriv f α| / 2) := by
      linarith [abs_nonneg (iteratedDeriv 3 f α), hsm.eta_pos]
    nlinarith [h, ha]
  have hupper : |next f x₀ x₁ x₂ - α| ≤ M * (|x₀ - α| * |x₁ - α| * |x₂ - α|) := by
    have h1 : |next f x₀ x₁ x₂ - α| * (|deriv f α| / 2)
        ≤ |next f x₀ x₁ x₂ - α| *
          |linCoeff f x₀ x₁ x₂ + quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂)| :=
      mul_le_mul_of_nonneg_left hLlo (abs_nonneg _)
    rw [hident] at h1
    have h2 : |newton f ![x₀, x₁, x₂, α]| * (|x₀ - α| * |x₁ - α| * |x₂ - α|)
        ≤ M * (|deriv f α| / 2) * (|x₀ - α| * |x₁ - α| * |x₂ - α|) :=
      mul_le_mul_of_nonneg_right (hNhi.trans hM) hP
    refine le_of_mul_le_mul_right ?_ (show (0:ℝ) < |deriv f α| / 2 by positivity)
    linarith
  have hlower : m * (|x₀ - α| * |x₁ - α| * |x₂ - α|) ≤ |next f x₀ x₁ x₂ - α| := by
    have h1 : |next f x₀ x₁ x₂ - α| *
        |linCoeff f x₀ x₁ x₂ + quadCoeff f x₀ x₁ x₂ * (α + next f x₀ x₁ x₂ - 2 * x₂)|
        ≤ |next f x₀ x₁ x₂ - α| * (3 * |deriv f α| / 2) :=
      mul_le_mul_of_nonneg_left hLhi (abs_nonneg _)
    rw [hident] at h1
    have h2 : m * (3 * |deriv f α| / 2) * (|x₀ - α| * |x₁ - α| * |x₂ - α|)
        ≤ |newton f ![x₀, x₁, x₂, α]| * (|x₀ - α| * |x₁ - α| * |x₂ - α|) :=
      mul_le_mul_of_nonneg_right (hm.trans hNlo) hP
    refine le_of_mul_le_mul_right ?_ (show (0:ℝ) < 3 * |deriv f α| / 2 by positivity)
    linarith
  have hεnn : (0:ℝ) ≤ ε := hs.eps_pos.le
  have hkey₁ : |x₀ - α| * |x₁ - α| * |x₂ - α| ≤ ε * |x₁ - α| * ε :=
    mul_le_mul (mul_le_mul_of_nonneg_right hs.abs_lt₀.le (abs_nonneg _)) hs.abs_lt₂.le
      (abs_nonneg _) (mul_nonneg hεnn (abs_nonneg _))
  have hkey₂ : |x₀ - α| * |x₁ - α| * |x₂ - α| ≤ ε * ε * |x₂ - α| :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul hs.abs_lt₀.le hs.abs_lt₁.le (abs_nonneg _) hεnn) (abs_nonneg _)
  have hsmall₁ : |next f x₀ x₁ x₂ - α| ≤ |x₁ - α| / 2 :=
    calc |next f x₀ x₁ x₂ - α| ≤ M * (|x₀ - α| * |x₁ - α| * |x₂ - α|) := hupper
      _ ≤ M * (ε * |x₁ - α| * ε) := by gcongr
      _ = M * ε ^ 2 * |x₁ - α| := by ring
      _ ≤ 1 / 2 * |x₁ - α| := by gcongr
      _ = |x₁ - α| / 2 := by ring
  have hsmall₂ : |next f x₀ x₁ x₂ - α| ≤ |x₂ - α| / 2 :=
    calc |next f x₀ x₁ x₂ - α| ≤ M * (|x₀ - α| * |x₁ - α| * |x₂ - α|) := hupper
      _ ≤ M * (ε * ε * |x₂ - α|) := by gcongr
      _ = M * ε ^ 2 * |x₂ - α| := by ring
      _ ≤ 1 / 2 * |x₂ - α| := by gcongr
      _ = |x₂ - α| / 2 := by ring
  refine ⟨hlower, hupper, ?_, fun h => ?_, fun h => ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq]
    linarith [hs.abs_lt₂, abs_nonneg (x₂ - α)]
  · rw [h] at hsmall₁
    linarith [abs_pos.2 (sub_ne_zero.2 hs.ne₁)]
  · rw [h] at hsmall₂
    linarith [abs_pos.2 (sub_ne_zero.2 hs.ne₂)]

/-- With `0 < m` (which needs `f⁽³⁾(α) ≠ 0` and `η < |f⁽³⁾(α)|/6`), admissibility is preserved by
a Muller step. -/
theorem LocalData.isAdmissible_step (hα : f α = 0) (hdata : LocalData f α ε η)
    (hsm : Small f α ε η) {m M : ℝ} (hm0 : 0 < m)
    (hm : m * (3 * |deriv f α| / 2) ≤ |iteratedDeriv 3 f α| / 6 - η)
    (hM : |iteratedDeriv 3 f α| / 6 + η ≤ M * (|deriv f α| / 2)) (hMε : M * ε ^ 2 ≤ 1 / 2)
    (hs : IsAdmissible α ε x₀ x₁ x₂) :
    IsAdmissible α ε x₁ x₂ (next f x₀ x₁ x₂) := by
  obtain ⟨hlo, hup, hmem, hne₁, hne₂⟩ := hdata.step_bounds hα hsm hm hM hMε hs
  have hne : next f x₀ x₁ x₂ ≠ α := by
    intro h
    rw [h, sub_self, abs_zero] at hlo
    have : 0 < m * (|x₀ - α| * |x₁ - α| * |x₂ - α|) := by
      have h0 := abs_pos.2 (sub_ne_zero.2 hs.ne₀)
      have h1 := abs_pos.2 (sub_ne_zero.2 hs.ne₁)
      have h2 := abs_pos.2 (sub_ne_zero.2 hs.ne₂)
      positivity
    linarith
  exact ⟨hs.mem₁, hs.mem₂, hmem, hs.ne₁₂, Ne.symm hne₁, Ne.symm hne₂, hs.ne₁, hs.ne₂, hne⟩

/-! ### The orbit -/

/-- The **Muller iteration** from three starting values: `iterate f x₀ x₁ x₂ k` is the book's
`x^{(k+2)}`, so that `iterate f x₀ x₁ x₂ 0 = x₂` and each further value is one application of
`Muller.step` ([quarteroni2000numerical] (6.30)). -/
noncomputable def iterate (f : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) (k : ℕ) : ℝ :=
  ((step f)^[k] (x₀, x₁, x₂)).2.2

/-- One more Muller step shifts the state and appends `Muller.next`. -/
theorem iterate_succ_state (f : ℝ → ℝ) (s : ℝ × ℝ × ℝ) (k : ℕ) :
    (step f)^[k + 1] s = (((step f)^[k] s).2.1, ((step f)^[k] s).2.2,
      next f ((step f)^[k] s).1 ((step f)^[k] s).2.1 ((step f)^[k] s).2.2) := by
  rw [Function.iterate_succ_apply']
  rfl

/-- **Decay in steps of three.** If `E k ≥ 0` and `E (k+3) ≤ E k / 2` then `E k → 0`: each residue
class mod `3` decays geometrically. This is how the upper bound
`|e_{k+1}| ≤ M |e_{k-2} e_{k-1} e_k| ≤ M ε² |e_{k-2}|` alone gives convergence of Muller's method,
the three-term analogue of `Secant.tendsto_zero_of_le_mul` (for which the sharper Fibonacci decay
was available, since there both factors could be taken small). -/
theorem tendsto_zero_of_le_half {E : ℕ → ℝ} (hE : ∀ k, 0 ≤ E k)
    (hrec : ∀ k, E (k + 3) ≤ E k / 2) : Tendsto E atTop (𝓝 0) := by
  set C := max (E 0) (max (E 1) (E 2)) with hC
  have hC0 : 0 ≤ C := (hE 0).trans (le_max_left _ _)
  have key : ∀ j i, i < 3 → E (3 * j + i) ≤ C / 2 ^ j := by
    intro j
    induction j with
    | zero =>
      intro i hi
      simp only [Nat.mul_zero, Nat.zero_add, pow_zero, div_one]
      rcases i with _ | _ | _ | i
      · exact le_max_left _ _
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
      · omega
    | succ j ih =>
      intro i hi
      have hidx : 3 * (j + 1) + i = 3 * j + i + 3 := by ring
      rw [hidx]
      calc E (3 * j + i + 3) ≤ E (3 * j + i) / 2 := hrec _
        _ ≤ C / 2 ^ j / 2 := by gcongr; exact ih i hi
        _ = C / 2 ^ (j + 1) := by rw [pow_succ]; ring
  have hbound : ∀ n, E n ≤ C / 2 ^ (n / 3) := by
    intro n
    have h := key (n / 3) (n % 3) (Nat.mod_lt _ (by norm_num))
    rwa [Nat.div_add_mod] at h
  refine squeeze_zero hE hbound ?_
  have h1 : Tendsto (fun j : ℕ => C / 2 ^ j) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (1:ℝ) / 2 < 1)).const_mul C
    rw [mul_zero] at h
    refine h.congr fun j => ?_
    rw [one_div, inv_pow, ← div_eq_mul_inv]
  refine h1.comp (tendsto_atTop_atTop.2 fun b => ⟨3 * b, fun n hn => by omega⟩)

/-- **The tribonacci order from a two-sided triple-product recursion.** If a positive sequence
satisfies `c e_k e_{k+1} e_{k+2} ≤ e_{k+3} ≤ C e_k e_{k+1} e_{k+2}` with `0 < c`, then
`e_{k+1} ≤ B e_k ^ T` for all `k`, `T = Real.tribonacci` the root of `T³ = T² + T + 1`.

In the logarithmic variables `u_k = log e_k` and `s_k = u_{k+1} - T u_k`, the upper bound gives
`s_{k+3} ≤ log C + (1 - T) u_{k+3} + u_{k+2} + u_{k+1}` and the lower bound — used with the
*negative* coefficient `1 - T` — turns this into

`s_{k+3} ≤ L + (2 - T) s_{k+1} + ((T - 1)/T) s_k`,

where the two identities `(2 - T)(T + 1) = (T - 1)/T` and `1 - (2 - T) - (T - 1)/T = (T - 1)²/T`
are the cubic read twice. Both coefficients are positive and sum to less than `1` — exactly because
`T ≠ 1` — so the same monotone induction as in the golden-ratio case
(`Secant.exists_le_mul_rpow_goldenRatio`) bounds `s` above by
`max (L / (1 - a - b)) (max (s 0) (max (s 1) (s 2)))`, and no spectral-radius argument for the
two-dimensional recursion is needed. [isaacson1994analysis] pp. 99-101 give the golden-ratio
analogue in limit form; this is the bound form the order of Definition 6.1 asks for. -/
theorem exists_le_mul_rpow_tribonacci {e : ℕ → ℝ} {c C : ℝ} (hc : 0 < c) (hpos : ∀ k, 0 < e k)
    (hupper : ∀ k, e (k + 3) ≤ C * (e (k + 2) * e (k + 1) * e k))
    (hlower : ∀ k, c * (e (k + 2) * e (k + 1) * e k) ≤ e (k + 3)) :
    ∃ B > 0, ∀ k, e (k + 1) ≤ B * e k ^ Real.tribonacci := by
  have hprod : ∀ k, 0 < e (k + 2) * e (k + 1) * e k := fun k =>
    mul_pos (mul_pos (hpos _) (hpos _)) (hpos _)
  have hC : 0 < C := by
    by_contra hC
    push Not at hC
    have := mul_nonpos_of_nonpos_of_nonneg hC (hprod 0).le
    linarith [hupper 0, hpos 3]
  set p := Real.tribonacci with hp
  have hcube : p ^ 3 = p ^ 2 + p + 1 := by rw [hp]; exact Real.tribonacci_pow_three
  have hp1 : 1 < p := Real.one_lt_tribonacci
  have hp2 : p < 2 := Real.tribonacci_lt_two
  have hp0 : 0 < p := lt_trans one_pos hp1
  have hA0 : 0 < 2 - p := by linarith
  have hB0 : 0 < (p - 1) / p := by positivity
  have hAB : (2 - p) + (p - 1) / p < 1 := by
    have h : (1 : ℝ) - (2 - p) - (p - 1) / p = (p - 1) ^ 2 / p := by field_simp; ring
    have h2 : 0 < (p - 1) ^ 2 / p := div_pos (by nlinarith) hp0
    linarith
  have hcoef : (p - 1) / p - (2 - p) * p = 2 - p := by
    field_simp
    nlinarith [hcube]
  have hbp : (p - 1) / p * p = p - 1 := div_mul_cancel₀ _ hp0.ne'
  set u : ℕ → ℝ := fun k => Real.log (e k) with hu
  have hu_up : ∀ k, u (k + 3) ≤ Real.log C + (u (k + 2) + u (k + 1) + u k) := fun k => by
    have h := Real.log_le_log (hpos _) (hupper k)
    rw [Real.log_mul hC.ne' (hprod k).ne', Real.log_mul (mul_pos (hpos _) (hpos _)).ne'
      (hpos _).ne', Real.log_mul (hpos _).ne' (hpos _).ne'] at h
    simp only [hu]
    linarith
  have hu_lo : ∀ k, Real.log c + (u (k + 2) + u (k + 1) + u k) ≤ u (k + 3) := fun k => by
    have h := Real.log_le_log (mul_pos hc (hprod k)) (hlower k)
    rw [Real.log_mul hc.ne' (hprod k).ne', Real.log_mul (mul_pos (hpos _) (hpos _)).ne'
      (hpos _).ne', Real.log_mul (hpos _).ne' (hpos _).ne'] at h
    simp only [hu]
    linarith
  set s : ℕ → ℝ := fun k => u (k + 1) - p * u k with hs
  set L : ℝ := Real.log C + (1 - p) * Real.log c with hL
  have hrec : ∀ k, s (k + 3) ≤ L + (2 - p) * s (k + 1) + (p - 1) / p * s k := fun k => by
    have h1 := hu_up (k + 1)
    have h2 := mul_le_mul_of_nonneg_left (hu_lo k) (by linarith : (0:ℝ) ≤ p - 1)
    have hrhs : L + (2 - p) * (u (k + 2) - p * u (k + 1)) + (p - 1) / p * (u (k + 1) - p * u k)
        = L + (2 - p) * u (k + 2) + ((p - 1) / p - (2 - p) * p) * u (k + 1)
          - ((p - 1) / p * p) * u k := by ring
    simp only [hs]
    rw [hrhs, hcoef, hbp, hL]
    have h3 : k + 1 + 3 = k + 4 := by omega
    rw [h3] at h1
    linarith
  set S : ℝ := max (L / (1 - (2 - p) - (p - 1) / p)) (max (s 0) (max (s 1) (s 2))) with hS
  have hSpos : (0 : ℝ) < 1 - (2 - p) - (p - 1) / p := by linarith
  have hLS : L ≤ (1 - (2 - p) - (p - 1) / p) * S := by
    have := le_max_left (L / (1 - (2 - p) - (p - 1) / p)) (max (s 0) (max (s 1) (s 2)))
    rwa [div_le_iff₀ hSpos, mul_comm] at this
  have hbound : ∀ k, s k ≤ S ∧ s (k + 1) ≤ S ∧ s (k + 2) ≤ S := by
    intro k
    induction k with
    | zero => exact ⟨(le_max_left _ _).trans (le_max_right _ _),
        (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
        (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
    | succ k ih =>
      refine ⟨ih.2.1, ih.2.2, ?_⟩
      calc s (k + 3) ≤ L + (2 - p) * s (k + 1) + (p - 1) / p * s k := hrec k
        _ ≤ (1 - (2 - p) - (p - 1) / p) * S + (2 - p) * S + (p - 1) / p * S := by
            gcongr
            · exact ih.2.1
            · exact ih.1
        _ = S := by ring
  refine ⟨Real.exp S, Real.exp_pos S, fun k => ?_⟩
  have hk : u (k + 1) ≤ S + p * u k := by
    have := (hbound k).1
    simp only [hs] at this
    linarith
  calc e (k + 1) = Real.exp (u (k + 1)) := (Real.exp_log (hpos _)).symm
    _ ≤ Real.exp (S + p * u k) := Real.exp_le_exp.2 hk
    _ = Real.exp S * e k ^ p := by
        rw [Real.exp_add, Real.rpow_def_of_pos (hpos k), mul_comm (Real.log _)]

/-! ### Local convergence with order the tribonacci constant -/

/-- **Muller's method has order the tribonacci constant `p ≈ 1.8393`**
([quarteroni2000numerical] §6.4.3, where it is printed as `p ≃ 1.84` and quoted from [Hil87]
without proof). If `f α = 0`, `f` is `C³` at `α`, `f'(α) ≠ 0` and `f⁽³⁾(α) ≠ 0`, then there is
`ε > 0` such that from any three distinct starting values in `(α - ε, α + ε)`, none of them `α`,
the Muller iterates converge to `α` with order `Real.tribonacci` in the sense of
`ConvergesWithOrder`.

The hypothesis `f⁽³⁾(α) ≠ 0` is what the *order* needs, exactly as `f''(α) ≠ 0` is needed for the
secant method's golden-ratio order (`Secant.exists_ball_convergesWithOrder_goldenRatio`): without a
lower bound on the error the two-sided recursion degenerates. The book states the sharper limit
form `|e^{(k+1)}| / |e^{(k)}|^p → |f⁽³⁾(α) / f'(α)| / 6`, which this bound form does not claim; the
constant is visible in `Muller.LocalData.step_bounds`, whose `m` and `M` both tend to
`|f⁽³⁾(α)/(6 f'(α))|` as `ε, η → 0`. -/
theorem exists_ball_convergesWithOrder (hα : f α = 0) (hf : ContDiffAt ℝ 3 f α)
    (hf' : deriv f α ≠ 0) (hf3 : iteratedDeriv 3 f α ≠ 0) :
    ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, ∀ x₁ ∈ Metric.ball α ε, ∀ x₂ ∈ Metric.ball α ε,
      x₀ ≠ x₁ → x₀ ≠ x₂ → x₁ ≠ x₂ → x₀ ≠ α → x₁ ≠ α → x₂ ≠ α →
      ConvergesWithOrder (iterate f x₀ x₁ x₂) α Real.tribonacci := by
  have hA : 0 < |deriv f α| := abs_pos.2 hf'
  have hT : 0 < |iteratedDeriv 3 f α| := abs_pos.2 hf3
  have hB : 0 ≤ |iteratedDeriv 2 f α| := abs_nonneg _
  set η : ℝ := min (|deriv f α| / 8) (|iteratedDeriv 3 f α| / 12) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηA : 8 * η ≤ |deriv f α| := by
    have := min_le_left (|deriv f α| / 8) (|iteratedDeriv 3 f α| / 12); rw [hηdef]; linarith
  have hηT : η ≤ |iteratedDeriv 3 f α| / 12 := min_le_right _ _
  set M : ℝ := 2 * (|iteratedDeriv 3 f α| / 6 + η) / |deriv f α| with hMdef
  set m : ℝ := 2 * (|iteratedDeriv 3 f α| / 6 - η) / (3 * |deriv f α|) with hmdef
  have hM0 : 0 < M := by rw [hMdef]; positivity
  have hm0 : 0 < m := by
    rw [hmdef]
    have : 0 < |iteratedDeriv 3 f α| / 6 - η := by linarith
    positivity
  have hMeq' : M * (|deriv f α| / 2) = |iteratedDeriv 3 f α| / 6 + η := by
    rw [hMdef]; field_simp
  have hmeq' : m * (3 * |deriv f α| / 2) = |iteratedDeriv 3 f α| / 6 - η := by
    rw [hmdef]; field_simp
  have hMeq : |iteratedDeriv 3 f α| / 6 + η ≤ M * (|deriv f α| / 2) := hMeq'.ge
  have hmeq : m * (3 * |deriv f α| / 2) ≤ |iteratedDeriv 3 f α| / 6 - η := hmeq'.le
  obtain ⟨δ, hδ, hdata⟩ := exists_localData hf hη
  have hBη : 0 < |iteratedDeriv 2 f α| / 2 + η := by positivity
  have hAη : 0 < |deriv f α| + η := by positivity
  set c₁ : ℝ := |deriv f α| / (16 * (|iteratedDeriv 2 f α| / 2 + η)) with hc₁
  set c₂ : ℝ := |deriv f α| ^ 2 / (32 * ((|deriv f α| + η) * (|iteratedDeriv 2 f α| / 2 + η)))
    with hc₂
  set c₃ : ℝ := 1 / (2 * M) with hc₃
  have hc₁0 : 0 < c₁ := by rw [hc₁]; positivity
  have hc₂0 : 0 < c₂ := by rw [hc₂]; positivity
  have hc₃0 : 0 < c₃ := by rw [hc₃]; positivity
  set ε : ℝ := min δ (min 1 (min c₁ (min c₂ c₃))) with hεdef
  have hε : 0 < ε := lt_min hδ (lt_min one_pos (lt_min hc₁0 (lt_min hc₂0 hc₃0)))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hεc₁ : ε ≤ c₁ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεc₂ : ε ≤ c₂ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεc₃ : ε ≤ c₃ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))
  have hsm : Small f α ε η := by
    refine ⟨hε, hη, hf', hηA, ?_, ?_⟩
    · have h := (le_div_iff₀ (by positivity : (0:ℝ) < 16 * (|iteratedDeriv 2 f α| / 2 + η))).1
        (hεc₁.trans_eq hc₁)
      linarith
    · have h := (le_div_iff₀ (by positivity :
        (0:ℝ) < 32 * ((|deriv f α| + η) * (|iteratedDeriv 2 f α| / 2 + η)))).1
        (hεc₂.trans_eq hc₂)
      linarith
  have hMε : M * ε ^ 2 ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * M)).1 (hεc₃.trans_eq hc₃)
    have hMe : 0 ≤ M * ε := mul_nonneg hM0.le hε.le
    calc M * ε ^ 2 = M * ε * ε := by ring
      _ ≤ M * ε * 1 := by gcongr
      _ = M * ε := by ring
      _ ≤ 1 / 2 := by linarith
  have hdata' : LocalData f α ε η := hdata.mono hεδ
  refine ⟨ε, hε, fun x₀ hx₀ x₁ hx₁ x₂ hx₂ h01 h02 h12 h0 h1 h2 => ?_⟩
  have hs : IsAdmissible α ε x₀ x₁ x₂ := ⟨hx₀, hx₁, hx₂, h01, h02, h12, h0, h1, h2⟩
  set s : ℝ × ℝ × ℝ := (x₀, x₁, x₂) with hsdef
  set X : ℕ → ℝ := fun k => ((step f)^[k] s).1 with hXdef
  have hX1 : ∀ k, X (k + 1) = ((step f)^[k] s).2.1 := fun k => by
    simp only [hXdef, iterate_succ_state]
  have hX2 : ∀ k, X (k + 2) = ((step f)^[k] s).2.2 := fun k => by
    simp only [hXdef, show k + 2 = k + 1 + 1 from rfl, iterate_succ_state]
  have hX3 : ∀ k, X (k + 3) = next f (X k) (X (k + 1)) (X (k + 2)) := fun k => by
    rw [hX1 k, hX2 k]
    simp only [hXdef, show k + 3 = k + 1 + 1 + 1 from rfl, iterate_succ_state]
  have hadm : ∀ k, IsAdmissible α ε (X k) (X (k + 1)) (X (k + 2)) := by
    intro k
    induction k with
    | zero => exact hs
    | succ k ih =>
      have h := hdata'.isAdmissible_step hα hsm hm0 hmeq hMeq hMε ih
      rwa [← hX3 k] at h
  set e : ℕ → ℝ := fun k => |X k - α| with hedef
  have hepos : ∀ k, 0 < e k := fun k => abs_pos.2 (sub_ne_zero.2 (hadm k).ne₀)
  have helt : ∀ k, e k < ε := fun k => (hadm k).abs_lt₀
  have hbounds : ∀ k, m * (e k * e (k + 1) * e (k + 2)) ≤ e (k + 3) ∧
      e (k + 3) ≤ M * (e k * e (k + 1) * e (k + 2)) := by
    intro k
    obtain ⟨hlo, hup, -, -, -⟩ := hdata'.step_bounds hα hsm hmeq hMeq hMε (hadm k)
    rw [hedef]
    simp only [hX3 k]
    exact ⟨hlo, hup⟩
  have hhalf : ∀ k, e (k + 3) ≤ e k / 2 := by
    intro k
    have hup := (hbounds k).2
    have hb : e (k + 1) * e (k + 2) ≤ ε * ε :=
      mul_le_mul (helt (k + 1)).le (helt (k + 2)).le (hepos (k + 2)).le hε.le
    have h1 : M * (e k * e (k + 1) * e (k + 2)) ≤ M * ε ^ 2 * e k :=
      calc M * (e k * e (k + 1) * e (k + 2)) = M * e k * (e (k + 1) * e (k + 2)) := by ring
        _ ≤ M * e k * (ε * ε) :=
            mul_le_mul_of_nonneg_left hb (mul_nonneg hM0.le (hepos k).le)
        _ = M * ε ^ 2 * e k := by ring
    have h2 : M * ε ^ 2 * e k ≤ 1 / 2 * e k :=
      mul_le_mul_of_nonneg_right hMε (hepos k).le
    linarith
  have htend0 : Tendsto e atTop (𝓝 0) :=
    tendsto_zero_of_le_half (fun k => abs_nonneg _) hhalf
  have htendX : Tendsto X atTop (𝓝 α) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact htend0.congr fun k => by rw [Real.dist_eq]
  have hiter : ∀ k, iterate f x₀ x₁ x₂ k = X (k + 2) := fun k => by rw [hX2 k, iterate]
  refine ⟨?_, ?_⟩
  · refine (htendX.comp (tendsto_add_atTop_nat 2)).congr fun k => ?_
    rw [hiter k]
    rfl
  obtain ⟨Bc, hBc, hbound⟩ := exists_le_mul_rpow_tribonacci (c := m) (C := M) hm0 hepos
    (fun k => by linarith [(hbounds k).2]) (fun k => by linarith [(hbounds k).1])
  refine ⟨Bc, hBc, Eventually.of_forall fun k => ?_⟩
  have h := hbound (k + 2)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hiter k, hiter (k + 1)]
  exact h

end Muller
