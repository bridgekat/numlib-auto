import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Taylor
import Numlib.Analysis.Calculus.RootMultiplicity
import Numlib.Nonlinear.FixedPoint

/-!
# Order of convergence, Aitken's Δ² extrapolation and Steffensen's method

The order of convergence of a sequence in a normed group and of a fixed-point iteration
([quarteroni2000numerical] Definition 6.1), the ratio lemmas behind the convergence-order theory of
one-step iterations, Aitken's Δ² extrapolation and Steffensen's method ([quarteroni2000numerical]
§6.6.1, Exercise 6.5; [isaacson1994analysis] §3.3), and the increment stopping criterion
([quarteroni2000numerical] §6.5).

`ConvergesWithOrder x α p` — `x → α` with `‖x (k+1) - α‖ ≤ C ‖x k - α‖ ^ p` eventually, `p : ℝ` a
real power so that non-integer orders such as the golden ratio are allowed — and
`HasIterationOrder φ α p` (every orbit of `φ` from a ball around `α` converges with order `p`) are
stated for a normed additive group, so that the `ℝⁿ` methods of [quarteroni2000numerical] chapter 7
reuse them. The derivative-based results are scalar. Every error-ratio limit carries the hypothesis
`x k ≠ α`: an orbit that hits the fixed point is constant from then on and the ratios are `0 / 0`.

## Design

* The order of a one-step scalar method is read off a **ratio limit**
  `(φ x - α) / (x - α) ^ n → c` as `x → α`, `x ≠ α`. Two generic lemmas turn such a limit (or the
  eventual bound `|φ x - α| ≤ C |x - α| ^ n` it implies) into `HasIterationOrder φ α n`:
  `hasIterationOrder_of_eventually_norm_sub_le` for `n ≥ 2`, where the bound alone gives local
  convergence, and `hasIterationOrder_one_of_tendsto_sub_div` for `n = 1` with `|c| < 1`, where
  Ostrowski's theorem does. Property 6.4, Aitken's method, Steffensen's method and Newton's method
  (`Numlib/Nonlinear/ScalarNewton`) are all instances.
* The ratio limits are computed with Mathlib's `dslope` (`φ x - α = (x - α) · dslope φ α x`, with
  `dslope φ α` continuous at `α` when `φ` is differentiable there and `C¹` when `φ` is `C²`, by
  Hadamard's lemma `ContDiffAt.dslope_same`) and, for higher orders, with the Taylor factorization
  `IsRootOfMultiplicity.exists_eq_pow_mul` of `Numlib/Analysis/Calculus/RootMultiplicity`.
* Aitken's iteration function `φ_Δ` is extended by `x` itself where its denominator vanishes, so
  that a fixed point of `φ` is a fixed point of `φ_Δ`; the identity
  `φ_Δ x - α = ((x - α) (φ (φ x) - α) - (φ x - α)²) / (φ (φ x) - 2 φ x + x)` reduces everything
  about it to the expansions of `φ x - α` and `φ (φ x) - α`.

## Errata

The remark after Definition 6.1 says a factor `C < 1` is *necessary* for convergence when `p = 1`;
it is sufficient (`tendsto_of_eventually_norm_sub_succ_le`). Property 6.4's range `0 ≤ i ≤ p` must
read `1 ≤ i ≤ p`. The last clause of Property 6.7 (Aitken at a multiple root converges linearly
with factor `1 - 1/m`) is false as printed — `φ_Δ'(α) = 0` for every `φ` with `φ'(α) ≠ 1` — and is
[isaacson1994analysis]'s statement about Steffensen's method, proved here as
`tendsto_steffensenStep_sub_div_of_isRootOfMultiplicity`.
-/

open Filter Topology Set
open scoped fwdDiff

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E]

/-- `x` converges to `α` with order `p` ([quarteroni2000numerical] Definition 6.1): `x → α` and,
for some `C > 0` and all large `k`, `‖x (k+1) - α‖ ≤ C ‖x k - α‖ ^ p`. The second conjunct is the
displayed inequality (6.2) of the definition, the first the word "converges" in it; the exponent is
the real power, so non-integer orders are allowed, and the definition does not force `p ≥ 1`. -/
def ConvergesWithOrder (x : ℕ → E) (α : E) (p : ℝ) : Prop :=
  Tendsto x atTop (𝓝 α) ∧ ∃ C > 0, ∀ᶠ k in atTop, ‖x (k + 1) - α‖ ≤ C * ‖x k - α‖ ^ p

/-- A fixed-point iteration `x ↦ φ x` has (local) order `p` at `α` if from every start close
enough to `α` the orbit converges to `α` with order `p`: the sense in which
[quarteroni2000numerical] says "a fixed-point method has order `p`" (the sentence before its
Property 6.4). -/
def HasIterationOrder (φ : E → E) (α : E) (p : ℝ) : Prop :=
  ∃ ε > 0, ∀ x₀ ∈ Metric.ball α ε, ConvergesWithOrder (fun k => φ^[k] x₀) α p

/-- A convergent sequence of order `p` converges. -/
theorem ConvergesWithOrder.tendsto {x : ℕ → E} {α : E} {p : ℝ} (h : ConvergesWithOrder x α p) :
    Tendsto x atTop (𝓝 α) :=
  h.1

/-- **A linear error bound with factor below one forces convergence**: if
`‖x (k+1) - α‖ ≤ C ‖x k - α‖` eventually with `C < 1`, then `x → α`. This is the sufficient
direction of the remark after [quarteroni2000numerical] Definition 6.1, whose word "necessary" is a
slip. -/
theorem tendsto_of_eventually_norm_sub_succ_le {x : ℕ → E} {α : E} {C : ℝ} (hC : C < 1)
    (h : ∀ᶠ k in atTop, ‖x (k + 1) - α‖ ≤ C * ‖x k - α‖) : Tendsto x atTop (𝓝 α) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  have hC'0 : 0 ≤ max C 0 := le_max_right _ _
  have hC'1 : max C 0 < 1 := max_lt hC one_pos
  have hbound : ∀ n, ‖x (n + N) - α‖ ≤ max C 0 ^ n * ‖x N - α‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc ‖x (n + 1 + N) - α‖ = ‖x (n + N + 1) - α‖ := by rw [Nat.add_right_comm]
        _ ≤ C * ‖x (n + N) - α‖ := hN _ (Nat.le_add_left N n)
        _ ≤ max C 0 * ‖x (n + N) - α‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max C 0 * (max C 0 ^ n * ‖x N - α‖) := by gcongr
        _ = max C 0 ^ (n + 1) * ‖x N - α‖ := by ring
  rw [← Filter.tendsto_add_atTop_iff_nat N]
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) hbound ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hC'0 hC'1).mul_const ‖x N - α‖

/-- **Linear convergence with factor `C`**: a bound `‖x (k+1) - α‖ ≤ C ‖x k - α‖` with
`0 < C < 1` is convergence of order `1` in the sense of Definition 6.1, `C` being the convergence
factor. -/
theorem convergesWithOrder_one_of_eventually_norm_sub_succ_le {x : ℕ → E} {α : E} {C : ℝ}
    (hC0 : 0 < C) (hC : C < 1) (h : ∀ᶠ k in atTop, ‖x (k + 1) - α‖ ≤ C * ‖x k - α‖) :
    ConvergesWithOrder x α 1 :=
  ⟨tendsto_of_eventually_norm_sub_succ_le hC h, C, hC0, h.mono fun k hk => by rwa [Real.rpow_one]⟩

/-- If the error ratio `‖x (k+1) - α‖ / ‖x k - α‖ ^ p` has a finite limit along a sequence that
eventually avoids `α`, then the order bound of Definition 6.1 holds (with `C = |c| + 1`). This is
how every ratio-limit theorem yields an order in the sense of `ConvergesWithOrder`. -/
theorem exists_eventually_norm_sub_succ_le_of_tendsto_ratio {x : ℕ → E} {α : E} {p c : ℝ}
    (hx : ∀ᶠ k in atTop, x k ≠ α)
    (h : Tendsto (fun k => ‖x (k + 1) - α‖ / ‖x k - α‖ ^ p) atTop (𝓝 c)) :
    ∃ C > 0, ∀ᶠ k in atTop, ‖x (k + 1) - α‖ ≤ C * ‖x k - α‖ ^ p := by
  refine ⟨|c| + 1, by positivity, ?_⟩
  filter_upwards [hx, h.eventually (gt_mem_nhds (lt_of_le_of_lt (le_abs_self c) (lt_add_one _)))]
    with k hk hlt
  have hpos : 0 < ‖x k - α‖ ^ p := Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hk)) _
  exact (div_le_iff₀ hpos).1 hlt.le

/-- Order `p` implies order `q` whenever `0 ≤ q ≤ p`: once the errors are below `1`,
`‖x k - α‖ ^ p ≤ ‖x k - α‖ ^ q`. This is why Definition 6.1 speaks of "order at least `p`" in
practice. -/
theorem ConvergesWithOrder.of_le {x : ℕ → E} {α : E} {p q : ℝ} (hq : 0 ≤ q) (hpq : q ≤ p)
    (h : ConvergesWithOrder x α p) : ConvergesWithOrder x α q := by
  obtain ⟨hlim, C, hC, hbound⟩ := h
  refine ⟨hlim, C, hC, ?_⟩
  have h1 : ∀ᶠ k in atTop, ‖x k - α‖ ≤ 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hlim).eventually (ge_mem_nhds one_pos)
  filter_upwards [hbound, h1] with k hk hk1
  exact hk.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hk1 hq hpq) hC.le)

/-- An eventual bound `‖φ x - α‖ ≤ C ‖x - α‖ ^ p` near `α` together with local convergence of the
orbits gives `HasIterationOrder φ α p`. -/
theorem hasIterationOrder_of_eventually_of_tendsto {φ : E → E} {α : E} {p C : ℝ} (hC : 0 < C)
    (hbound : ∀ᶠ x in 𝓝 α, ‖φ x - α‖ ≤ C * ‖x - α‖ ^ p)
    (hconv : ∃ δ > 0, ∀ x₀ ∈ Metric.ball α δ, Tendsto (fun k => φ^[k] x₀) atTop (𝓝 α)) :
    HasIterationOrder φ α p := by
  obtain ⟨δ, hδ, hconv⟩ := hconv
  refine ⟨δ, hδ, fun x₀ hx₀ => ⟨hconv x₀ hx₀, C, hC, ?_⟩⟩
  filter_upwards [(hconv x₀ hx₀).eventually hbound] with k hk
  rwa [Function.iterate_succ_apply']

/-- **Order `n ≥ 2` from the bound alone**: if `‖φ x - α‖ ≤ C ‖x - α‖ ^ n` near `α` with `n ≥ 2`,
then `φ` has iteration order `n` at `α`. The bound makes `φ` contract by the factor `1/2` on a
small enough ball, so orbits stay in it and converge; `φ α = α` is forced by the bound at
`x = α`. -/
theorem hasIterationOrder_of_eventually_norm_sub_le {φ : E → E} {α : E} {C : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (h : ∀ᶠ x in 𝓝 α, ‖φ x - α‖ ≤ C * ‖x - α‖ ^ n) : HasIterationOrder φ α n := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
  set C' : ℝ := max C 0 + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  have hCC' : C ≤ C' := (le_max_left _ _).trans (lt_add_one _).le
  -- a radius on which `C' ‖x - α‖ ^ (n - 1) ≤ 1 / 2`
  obtain ⟨δ', hδ'0, hδ'δ, hδ'half⟩ : ∃ δ' > 0, δ' ≤ δ ∧ C' * δ' ^ (n - 1) ≤ 1 / 2 := by
    refine ⟨min δ (min 1 (1 / (2 * C'))), by positivity, min_le_left _ _, ?_⟩
    have h1 : min δ (min 1 (1 / (2 * C'))) ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : min δ (min 1 (1 / (2 * C'))) ≤ 1 / (2 * C') :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h0 : 0 ≤ min δ (min 1 (1 / (2 * C'))) := by positivity
    calc C' * min δ (min 1 (1 / (2 * C'))) ^ (n - 1)
        ≤ C' * min δ (min 1 (1 / (2 * C'))) ^ 1 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 h1 (by omega)) hC'0.le
      _ ≤ C' * (1 / (2 * C')) := by rw [pow_one]; gcongr
      _ = 1 / 2 := by field_simp
  have hhalf : ∀ x ∈ Metric.ball α δ', ‖φ x - α‖ ≤ 1 / 2 * ‖x - α‖ := by
    intro x hx
    have hxδ : dist x α < δ := lt_of_lt_of_le (Metric.mem_ball.1 hx) hδ'δ
    have hxδ' : ‖x - α‖ ≤ δ' := by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hx).le
    calc ‖φ x - α‖ ≤ C * ‖x - α‖ ^ n := hball hxδ
      _ ≤ C' * ‖x - α‖ ^ n := mul_le_mul_of_nonneg_right hCC' (by positivity)
      _ = C' * ‖x - α‖ ^ (n - 1) * ‖x - α‖ := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
      _ ≤ C' * δ' ^ (n - 1) * ‖x - α‖ := by gcongr
      _ ≤ 1 / 2 * ‖x - α‖ := by gcongr
  refine hasIterationOrder_of_eventually_of_tendsto hC'0 ?_ ⟨δ', hδ'0, fun x₀ hx₀ => ?_⟩
  · filter_upwards [h] with x hx
    rw [Real.rpow_natCast]
    exact hx.trans (mul_le_mul_of_nonneg_right hCC' (by positivity))
  · refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
      (fun k => (norm_iterate_sub_le_pow_mul_of_ball (by norm_num) (by norm_num) hhalf hx₀ k).2)
      ?_)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).mul_const ‖x₀ - α‖

end NormedGroup

section Scalar

variable {φ : ℝ → ℝ} {α : ℝ}

/-- From a ratio limit `(φ x - α) / (x - α) ^ n → c` at `α` and `φ α = α`, the eventual bound
`|φ x - α| ≤ (|c| + 1) |x - α| ^ n` on a full neighbourhood of `α`. -/
theorem eventually_abs_sub_le_mul_abs_pow_of_tendsto (hα : φ α = α) {c : ℝ} {n : ℕ}
    (h : Tendsto (fun x => (φ x - α) / (x - α) ^ n) (𝓝[≠] α) (𝓝 c)) :
    ∀ᶠ x in 𝓝 α, |φ x - α| ≤ (|c| + 1) * |x - α| ^ n := by
  have h1 := h.eventually (gt_mem_nhds (lt_of_le_of_lt (le_abs_self c) (lt_add_one _)))
  have h2 := h.eventually (lt_mem_nhds (neg_lt_of_abs_lt (lt_add_one |c|)))
  rw [eventually_nhdsWithin_iff] at h1 h2
  filter_upwards [h1, h2] with x hx1 hx2
  by_cases hxα : x = α
  · simp only [hxα, hα, sub_self, abs_zero]
    positivity
  · have hpos : 0 < |(x - α) ^ n| := abs_pos.2 (pow_ne_zero _ (sub_ne_zero.2 hxα))
    rw [← abs_pow, ← div_le_iff₀ hpos, ← abs_div]
    exact abs_le.2 ⟨(hx2 hxα).le, (hx1 hxα).le⟩

/-- **Order `n ≥ 2` from a ratio limit**: if `(φ x - α) / (x - α) ^ n → c` as `x → α`, `x ≠ α`,
with `n ≥ 2` and `φ α = α`, then `φ` has iteration order `n` at `α`. -/
theorem hasIterationOrder_of_tendsto_sub_div_pow (hα : φ α = α) {c : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (h : Tendsto (fun x => (φ x - α) / (x - α) ^ n) (𝓝[≠] α) (𝓝 c)) :
    HasIterationOrder φ α n :=
  hasIterationOrder_of_eventually_norm_sub_le hn
    (by simpa [Real.norm_eq_abs] using eventually_abs_sub_le_mul_abs_pow_of_tendsto hα h)

/-- **Order `1` from a ratio limit below one**: if `(φ x - α) / (x - α) → c` as `x → α`, `x ≠ α`,
with `|c| < 1` and `φ α = α`, then `φ` has iteration order `1` at `α` (Ostrowski's theorem gives
the convergence; the limit is `φ'(α)`). -/
theorem hasIterationOrder_one_of_tendsto_sub_div (hα : φ α = α) {c : ℝ} (hc : |c| < 1)
    (h : Tendsto (fun x => (φ x - α) / (x - α)) (𝓝[≠] α) (𝓝 c)) : HasIterationOrder φ α 1 := by
  have hderiv : HasDerivAt φ c α := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine h.congr fun x => ?_
    rw [slope_def_field, hα]
  obtain ⟨q, hq, hq1⟩ := exists_between hc
  have hq0 : 0 < q := lt_of_le_of_lt (abs_nonneg _) hq
  refine hasIterationOrder_of_eventually_of_tendsto hq0 ?_ ?_
  · filter_upwards [eventually_abs_sub_le_mul_of_hasDerivAt hα hderiv hq] with x hx
    simpa [Real.norm_eq_abs] using hx
  · obtain ⟨δ, hδ, hconv⟩ := tendsto_iterate_of_abs_deriv_lt_one hα hderiv hc
    exact ⟨δ, hδ, fun x₀ hx₀ => hconv x₀ (by simpa [Metric.mem_ball, Real.dist_eq] using hx₀)⟩

/-- **(6.18) of [quarteroni2000numerical] Theorem 6.1, from differentiability at the fixed point
alone**: along a convergent orbit `x (k+1) = φ (x k)` that never hits `α`, the error ratios
`(x (k+1) - α) / (x k - α)` tend to `φ'(α)`. The book derives it with the mean value theorem under
`φ ∈ C¹[a, b]`; neither `C¹` nor the interval is needed. -/
theorem tendsto_sub_div_sub_of_hasDerivAt {φ' : ℝ} (hφ : HasDerivAt φ φ' α) (hα : φ α = α)
    {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 φ') := by
  have := (hasDerivAt_iff_tendsto_slope.1 hφ).comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
  refine this.congr fun k => ?_
  simp [slope, hx, hα, Function.comp, vsub_eq_sub, div_eq_inv_mul]

/-- **(6.18) from a derivative within a set**: along an orbit `x (k+1) = φ (x k)` converging to
`α = φ α` inside a set `s` on which `φ` has derivative `φ'` at `α`, and never equal to `α`, the
error ratios tend to `φ' α`. This is the form needed when `α` is an endpoint of `[a, b]`. -/
theorem tendsto_sub_div_sub_of_hasDerivWithinAt {s : Set ℝ} {φ'α : ℝ}
    (hφ : HasDerivWithinAt φ φ'α s α) (hα : φ α = α) {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k))
    (hs : ∀ k, x k ∈ s) (hne : ∀ k, x k ≠ α) (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 φ'α) := by
  have hmem : Tendsto x atTop (𝓝[s \ {α}] α) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => ⟨hs k, hne k⟩⟩
  have := (hasDerivWithinAt_iff_tendsto_slope.1 hφ).comp hmem
  refine this.congr fun k => ?_
  simp [slope, hx, hα, Function.comp, vsub_eq_sub, div_eq_inv_mul]

/-- Along a sequence avoiding `α` whose error ratios tend to `l ≠ 1`, the increments
`x (k+1) - x k` are eventually nonzero: `x (k+1) - x k = (x k - α) (r k - 1)` with `r k → l`. -/
theorem eventually_sub_succ_ne_zero_of_tendsto_ratio {x : ℕ → ℝ} {l : ℝ} (hne : ∀ k, x k ≠ α)
    (h : Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 l)) (hl : l ≠ 1) :
    ∀ᶠ k in atTop, x (k + 1) - x k ≠ 0 := by
  filter_upwards [h.eventually (isOpen_ne.mem_nhds hl)] with k hk
  have he : x k - α ≠ 0 := sub_ne_zero.2 (hne k)
  intro h0
  apply hk
  rw [show x (k + 1) - α = x k - α by linarith, div_self he]

/-- **The increment test, [quarteroni2000numerical] (6.31), from a ratio limit**: if the error
ratios tend to `l ≠ 1`, then `(α - x k) / (x (k+1) - x k) → 1 / (1 - l)`. The error `e_k = α - x_k`
(the book's sign convention, which makes the constant come out as printed) is asymptotically
`1 / (1 - l)` times the last increment. -/
theorem tendsto_sub_div_sub_succ_of_tendsto_ratio {x : ℕ → ℝ} {l : ℝ} (hne : ∀ k, x k ≠ α)
    (h : Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 l)) (hl : l ≠ 1) :
    Tendsto (fun k => (α - x k) / (x (k + 1) - x k)) atTop (𝓝 (1 / (1 - l))) := by
  refine (tendsto_const_nhds.div (tendsto_const_nhds.sub h) (sub_ne_zero.2 hl.symm)).congr
    fun k => ?_
  have he : x k - α ≠ 0 := sub_ne_zero.2 (hne k)
  simp only [Pi.div_apply]
  rw [show (1 : ℝ) - (x (k + 1) - α) / (x k - α) = (x k - α - (x (k + 1) - α)) / (x k - α) by
    field_simp, one_div_div]
  rw [show x k - α - (x (k + 1) - α) = -(x (k + 1) - x k) by ring, div_neg,
    show α - x k = -(x k - α) by ring, neg_div]

/-- **The increment test, [quarteroni2000numerical] (6.31)**: along a convergent orbit
`x (k+1) = φ (x k)` avoiding the fixed point `α`, with `φ'(α) ≠ 1`, the increments are eventually
nonzero and `(α - x k) / (x (k+1) - x k) → 1 / (1 - φ'(α))`. The test is reliable when `φ'(α)` is
far from `1`, and optimal for second-order methods, where `φ'(α) = 0`. -/
theorem tendsto_sub_div_sub_succ_of_hasDerivAt {φ' : ℝ} (hφ : HasDerivAt φ φ' α) (hα : φ α = α)
    (h1 : φ' ≠ 1) {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) :
    (∀ᶠ k in atTop, x (k + 1) - x k ≠ 0) ∧
      Tendsto (fun k => (α - x k) / (x (k + 1) - x k)) atTop (𝓝 (1 / (1 - φ'))) :=
  ⟨eventually_sub_succ_ne_zero_of_tendsto_ratio hne
      (tendsto_sub_div_sub_of_hasDerivAt hφ hα hx hne hlim) h1,
    tendsto_sub_div_sub_succ_of_tendsto_ratio hne
      (tendsto_sub_div_sub_of_hasDerivAt hφ hα hx hne hlim) h1⟩

end Scalar

section Taylor

variable {f : ℝ → ℝ} {α : ℝ}

/-- **Taylor's theorem with Peano remainder at a point**, with `iteratedDeriv`: if `f` is `C^n`
at `α` then `(f x - ∑_{i ≤ n} f^{(i)}(α)/i! (x - α)^i) / (x - α)^n → 0` as `x → α`. Mathlib's
`Real.taylor_tendsto` on a ball, with `iteratedDerivWithin` on the open ball replaced by
`iteratedDeriv`. -/
theorem tendsto_sub_taylor_div_pow {n : ℕ} (hf : ContDiffAt ℝ n f α) :
    Tendsto (fun x => (f x - ∑ i ∈ Finset.range (n + 1),
      iteratedDeriv i f α / i.factorial * (x - α) ^ i) / (x - α) ^ n) (𝓝 α) (𝓝 0) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
  have h := Real.taylor_tendsto (convex_ball α r) (Metric.mem_ball_self hr) (hfu.mono hru)
  rw [nhdsWithin_eq_nhds.2 (Metric.ball_mem_nhds α hr)] at h
  refine h.congr fun x => ?_
  rw [taylor_within_apply]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hr), smul_eq_mul]
  ring

/-- **[quarteroni2000numerical] Property 6.4, the limit (6.21), as a statement about `φ`**: if `φ`
is `C^{p+1}` at `α = φ α` and `φ^{(i)}(α) = 0` for `1 ≤ i ≤ p`, then
`(φ x - α) / (x - α)^{p+1} → φ^{(p+1)}(α) / (p+1)!` as `x → α`, `x ≠ α`. (The book's range
`0 ≤ i ≤ p` is a misprint: `i = 0` would say `φ α = 0`.) Taylor's theorem with all intermediate
terms vanishing. -/
theorem tendsto_sub_div_pow_nhdsNE_of_iteratedDeriv_eq_zero {φ : ℝ → ℝ} {p : ℕ}
    (hφ : ContDiffAt ℝ (p + 1 : ℕ) φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i ≤ p → iteratedDeriv i φ α = 0) :
    Tendsto (fun x => (φ x - α) / (x - α) ^ (p + 1)) (𝓝[≠] α)
      (𝓝 (iteratedDeriv (p + 1) φ α / (p + 1).factorial)) := by
  have hT : ∀ x, ∑ i ∈ Finset.range (p + 1 + 1),
      iteratedDeriv i φ α / i.factorial * (x - α) ^ i =
      α + iteratedDeriv (p + 1) φ α / (p + 1).factorial * (x - α) ^ (p + 1) := by
    intro x
    rw [Finset.sum_range_succ, Finset.sum_eq_single 0]
    · simp [hα]
    · intro i hi hi0
      rw [hzero i (by omega) (by simpa [Nat.lt_succ_iff] using hi), zero_div, zero_mul]
    · simp
  have h := (tendsto_sub_taylor_div_pow hφ).mono_left (nhdsWithin_le_nhds (s := {α}ᶜ))
  simp_rw [hT] at h
  have h' := h.add_const (iteratedDeriv (p + 1) φ α / (p + 1).factorial)
  rw [zero_add] at h'
  refine h'.congr' (eventually_mem_nhdsWithin.mono fun x hx => ?_)
  have hne : (x - α) ^ (p + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hx)
  field_simp
  ring

/-- **[quarteroni2000numerical] Property 6.4, the limit (6.21)** along an orbit: under the
hypotheses of `tendsto_sub_div_pow_nhdsNE_of_iteratedDeriv_eq_zero`, for every orbit
`x (k+1) = φ (x k)` converging to `α` with `x k ≠ α`,
`(x (k+1) - α) / (x k - α)^{p+1} → φ^{(p+1)}(α) / (p+1)!`. The hypothesis
`φ^{(p+1)}(α) ≠ 0` is not needed for the limit; it makes the order exactly `p + 1`. -/
theorem tendsto_sub_div_pow_of_iteratedDeriv_eq_zero {φ : ℝ → ℝ} {p : ℕ}
    (hφ : ContDiffAt ℝ (p + 1 : ℕ) φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i ≤ p → iteratedDeriv i φ α = 0)
    {x : ℕ → ℝ} (hx : ∀ k, x (k + 1) = φ (x k)) (hne : ∀ k, x k ≠ α)
    (hlim : Tendsto x atTop (𝓝 α)) :
    Tendsto (fun k => (x (k + 1) - α) / (x k - α) ^ (p + 1)) atTop
      (𝓝 (iteratedDeriv (p + 1) φ α / (p + 1).factorial)) := by
  have := (tendsto_sub_div_pow_nhdsNE_of_iteratedDeriv_eq_zero hφ hα hzero).comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hne⟩)
  refine this.congr fun k => ?_
  simp [Function.comp, hx]

/-- **[quarteroni2000numerical] Property 6.4, the order statement**: for `1 ≤ p`, `φ` `C^{p+1}` at
`α = φ α` with `φ^{(i)}(α) = 0` for `1 ≤ i ≤ p`, the iteration `x ↦ φ x` has order `p + 1` at `α`.
The case `p = 0` is excluded because the property presupposes convergence, which only `|φ'(α)| < 1`
would supply. -/
theorem hasIterationOrder_of_iteratedDeriv_eq_zero {φ : ℝ → ℝ} {p : ℕ} (hp : 1 ≤ p)
    (hφ : ContDiffAt ℝ (p + 1 : ℕ) φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i ≤ p → iteratedDeriv i φ α = 0) :
    HasIterationOrder φ α (p + 1) := by
  have := hasIterationOrder_of_tendsto_sub_div_pow hα (by omega)
    (tendsto_sub_div_pow_nhdsNE_of_iteratedDeriv_eq_zero hφ hα hzero)
  simpa using this

end Taylor

section Aitken

variable {φ : ℝ → ℝ} {α : ℝ}

/-- The ratio `λ^{(k+2)} = (x^{(k+2)} - x^{(k+1)}) / (x^{(k+1)} - x^{(k)})` of successive increments
([quarteroni2000numerical] (6.33), shifted to start at `k = 0`): what estimates the asymptotic
convergence factor from the iterates alone and, in §6.6.2, the multiplicity of a root. -/
noncomputable def aitkenRatio (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  (x (k + 2) - x (k + 1)) / (x (k + 1) - x k)

/-- **[quarteroni2000numerical] (6.34)**: if the error ratios of a sequence avoiding `α` tend to
`l ≠ 1`, so do the increment ratios: `aitkenRatio x k = r k (r (k+1) - 1) / (r k - 1)` with
`r k = (x (k+1) - α) / (x k - α)`. Combined with `tendsto_sub_div_sub_of_hasDerivAt` for a
fixed-point orbit, `λ^{(k)} → φ'(α)`. -/
theorem tendsto_aitkenRatio {x : ℕ → ℝ} {l : ℝ} (hne : ∀ k, x k ≠ α)
    (h : Tendsto (fun k => (x (k + 1) - α) / (x k - α)) atTop (𝓝 l)) (hl : l ≠ 1) :
    Tendsto (aitkenRatio x) atTop (𝓝 l) := by
  have h1 := (h.mul ((h.comp (tendsto_add_atTop_nat 1)).sub_const 1)).div (h.sub_const 1)
    (sub_ne_zero.2 hl)
  rw [mul_div_assoc, div_self (sub_ne_zero.2 hl), mul_one] at h1
  refine h1.congr fun k => ?_
  have e0 : x k - α ≠ 0 := sub_ne_zero.2 (hne k)
  have e1 : x (k + 1) - α ≠ 0 := sub_ne_zero.2 (hne (k + 1))
  simp only [Pi.div_apply, Function.comp]
  rw [aitkenRatio, ← div_div_div_cancel_right₀ e0 (x (k + 2) - x (k + 1)) (x (k + 1) - x k)]
  congr 1
  · field_simp
    ring
  · field_simp
    ring

/-- **Aitken's extrapolation formula** ([quarteroni2000numerical] (6.36)) producing `x̂^{(k+2)}`
from `x^{(k)}, x^{(k+1)}, x^{(k+2)}`; when the second difference vanishes Lean's `a / 0 = 0` returns
`x^{(k+2)}` itself. -/
noncomputable def aitkenExtrapolation (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  x (k + 2) - (x (k + 2) - x (k + 1)) ^ 2 / ((x (k + 2) - x (k + 1)) - (x (k + 1) - x k))

/-- **The Δ² form** ([quarteroni2000numerical] (6.37)) of Aitken's formula with Mathlib's forward
difference `Δ_[1]`: `x̂^{(k+2)} = x^{(k+2)} - (Δx^{(k+1)})² / Δ²x^{(k)}`. The book writes the same
identity with its backward-shifted convention `Δx^{(k)} = x^{(k)} - x^{(k-1)}`. -/
theorem aitkenExtrapolation_eq_sub_div_fwdDiff (x : ℕ → ℝ) (k : ℕ) :
    aitkenExtrapolation x k = x (k + 2) - (Δ_[1] x (k + 1)) ^ 2 / (Δ_[1]^[2] x k) := by
  simp only [aitkenExtrapolation, fwdDiff, Function.iterate_succ, Function.iterate_zero,
    Function.comp, id]

/-- **Aitken's iteration function** `φ_Δ` ([quarteroni2000numerical] (6.38)),
`φ_Δ x = (x φ(φ x) - φ(x)²) / (φ(φ x) - 2 φ x + x)`, extended by `x` itself where the denominator
vanishes, so that a fixed point of `φ` (where `0 / 0` occurs) is a fixed point of `φ_Δ`. One step of
the Aitken-accelerated method is Aitken's formula applied to `x, φ x, φ (φ x)`. -/
noncomputable def aitkenIterationFunction (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  if φ (φ x) - 2 * φ x + x = 0 then x
  else (x * φ (φ x) - φ x ^ 2) / (φ (φ x) - 2 * φ x + x)

/-- A fixed point of `φ` is a fixed point of `φ_Δ` (the guarded branch). -/
theorem aitkenIterationFunction_apply_self (hα : φ α = α) :
    aitkenIterationFunction φ α = α := by
  have : α - 2 * α + α = 0 := by ring
  simp [aitkenIterationFunction, hα, this]

/-- Where the denominator does not vanish, the fixed points of `φ_Δ` are those of `φ`:
`φ_Δ x - x = -(φ x - x)² / (φ (φ x) - 2 φ x + x)` ([quarteroni2000numerical] §6.6.1;
[isaacson1994analysis] pp. 104–106). -/
theorem aitkenIterationFunction_eq_self_iff {x : ℝ} (h : φ (φ x) - 2 * φ x + x ≠ 0) :
    aitkenIterationFunction φ x = x ↔ φ x = x := by
  simp only [aitkenIterationFunction, h, ↓reduceIte]
  rw [div_eq_iff h]
  constructor
  · intro hx
    have : (φ x - x) ^ 2 = 0 := by linarith
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · intro hx
    rw [hx]
    ring

/-- The error of Aitken's step in terms of the errors of `x`, `φ x`, `φ (φ x)`:
`φ_Δ x - α = ((x - α) (φ (φ x) - α) - (φ x - α)²) / (φ (φ x) - 2 φ x + x)`. -/
theorem aitkenIterationFunction_sub_eq {x : ℝ} (h : φ (φ x) - 2 * φ x + x ≠ 0) (α : ℝ) :
    aitkenIterationFunction φ x - α =
      ((x - α) * (φ (φ x) - α) - (φ x - α) ^ 2) / (φ (φ x) - 2 * φ x + x) := by
  simp only [aitkenIterationFunction, h, ↓reduceIte]
  rw [eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  ring

/-- **The `dslope` form of Aitken's error.** With `s₁ = dslope φ α`, `s₂ = dslope φ α ∘ φ` and
`Q = s₁ s₂ - 2 s₁ + 1`, for `x ≠ α` with `Q x ≠ 0` the denominator is `(x - α) Q x ≠ 0` and
`φ_Δ x - α = (x - α) s₁ x (s₂ x - s₁ x) / Q x`. Since `s₁, s₂ → φ'(α)` and `Q → (φ'(α) - 1)²`, this
is the whole local analysis of Aitken's method. -/
theorem aitkenIterationFunction_sub_eq_dslope (hα : φ α = α) {x : ℝ} (hx : x ≠ α)
    (hQ : dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1 ≠ 0) :
    φ (φ x) - 2 * φ x + x ≠ 0 ∧
      aitkenIterationFunction φ x - α =
        (x - α) * dslope φ α x * (dslope φ α (φ x) - dslope φ α x) /
          (dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1) := by
  have h1 : φ x - α = (x - α) * dslope φ α x := by
    have := sub_smul_dslope φ α x
    rw [hα, smul_eq_mul] at this
    exact this.symm
  have h2 : φ (φ x) - α = (φ x - α) * dslope φ α (φ x) := by
    have := sub_smul_dslope φ α (φ x)
    rw [hα, smul_eq_mul] at this
    exact this.symm
  have hD : φ (φ x) - 2 * φ x + x =
      (x - α) * (dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1) := by
    rw [show φ (φ x) - 2 * φ x + x = (φ (φ x) - α) - 2 * (φ x - α) + (x - α) by ring, h2, h1]
    ring
  have hD' : φ (φ x) - 2 * φ x + x ≠ 0 := hD ▸ mul_ne_zero (sub_ne_zero.2 hx) hQ
  refine ⟨hD', ?_⟩
  rw [aitkenIterationFunction_sub_eq hD' α, hD, h2, h1]
  field_simp

/-- The limits of `s₁ = dslope φ α`, of `s₂ = s₁ ∘ φ` and of `Q = s₁ s₂ - 2 s₁ + 1` at a fixed
point `α` where `φ` has derivative `φ'`: `φ'`, `φ'` and `(φ' - 1)²`. -/
theorem tendsto_dslope_aitken {φ' : ℝ} (hφ : HasDerivAt φ φ' α) (hα : φ α = α) :
    Tendsto (dslope φ α) (𝓝 α) (𝓝 φ') ∧ Tendsto (fun x => dslope φ α (φ x)) (𝓝 α) (𝓝 φ') ∧
      Tendsto (fun x => dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1) (𝓝 α)
        (𝓝 ((φ' - 1) ^ 2)) := by
  have hs₁ : Tendsto (dslope φ α) (𝓝 α) (𝓝 φ') := by
    have := (continuousAt_dslope_same.2 hφ.differentiableAt).tendsto
    rwa [dslope_same, hφ.deriv] at this
  have hφc : Tendsto φ (𝓝 α) (𝓝 α) := by simpa [hα] using hφ.continuousAt.tendsto
  have hs₂ : Tendsto (fun x => dslope φ α (φ x)) (𝓝 α) (𝓝 φ') := hs₁.comp hφc
  refine ⟨hs₁, hs₂, ?_⟩
  have := ((hs₁.mul hs₂).sub (hs₁.const_mul 2)).add_const 1
  convert this using 2
  ring

/-- Near a fixed point `α` with `φ'(α) ≠ 1`, the denominator of Aitken's iteration function does
not vanish away from `α`, so the guard of `aitkenIterationFunction` is never taken there. -/
theorem eventually_aitken_denom_ne_zero {φ' : ℝ} (hφ : HasDerivAt φ φ' α) (hα : φ α = α)
    (h1 : φ' ≠ 1) : ∀ᶠ x in 𝓝[≠] α, φ (φ x) - 2 * φ x + x ≠ 0 := by
  obtain ⟨-, -, hQ⟩ := tendsto_dslope_aitken hφ hα
  have hQne : (φ' - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 h1)
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hQ.eventually (isOpen_ne.mem_nhds hQne))] with x hx hQx
  exact (aitkenIterationFunction_sub_eq_dslope hα hx hQx).1

/-- **`φ_Δ` is differentiable at `α` with derivative `0`** as soon as `φ` is differentiable at `α`
with `φ'(α) ≠ 1`: Aitken's iteration is superlinear from mere differentiability, and in particular
`φ_Δ` is continuous at `α` (the book's "continuous extension at `α`" by L'Hôpital,
[quarteroni2000numerical] §6.6.1). From `aitkenIterationFunction_sub_eq_dslope`, the slope of `φ_Δ`
at `α` is `s₁ (s₂ - s₁) / Q → φ'(φ' - φ') / (φ' - 1)² = 0`. -/
theorem hasDerivAt_aitkenIterationFunction_zero {φ' : ℝ} (hφ : HasDerivAt φ φ' α) (hα : φ α = α)
    (h1 : φ' ≠ 1) : HasDerivAt (aitkenIterationFunction φ) 0 α := by
  obtain ⟨hs₁, hs₂, hQ⟩ := tendsto_dslope_aitken hφ hα
  have hQne : (φ' - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 h1)
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun x => dslope φ α x * (dslope φ α (φ x) - dslope φ α x) /
      (dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1)) (𝓝[≠] α)
      (𝓝 (φ' * (φ' - φ') / (φ' - 1) ^ 2)) :=
    ((hs₁.mul (hs₂.sub hs₁)).div hQ hQne).mono_left nhdsWithin_le_nhds
  rw [sub_self, mul_zero, zero_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hQ.eventually (isOpen_ne.mem_nhds hQne))] with x hx hQx
  obtain ⟨-, hformula⟩ := aitkenIterationFunction_sub_eq_dslope hα hx hQx
  rw [slope_def_field, aitkenIterationFunction_apply_self hα, hformula]
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  field_simp

/-- **[quarteroni2000numerical] Property 6.7 for `p = 1`, the sharp constant**: if `φ` is `C²` at
`α = φ α` with `φ'(α) ≠ 1`, then `(φ_Δ x - α) / (x - α)² → φ'(α) φ''(α) / (2 (φ'(α) - 1))` as
`x → α`, `x ≠ α`. Hence Aitken's method has order exactly `2` when `φ'(α) φ''(α) ≠ 0`, and it
converges locally *even when `|φ'(α)| > 1`*: the book's "convergent even if the fixed-point method
is not". The proof writes `s₂ - s₁ = (x - α) (s₁ · t ∘ φ - t)` with `t = dslope s₁ α`, which is
continuous at `α` with value `φ''(α) / 2` by Hadamard's lemma. -/
theorem tendsto_aitkenIterationFunction_sub_div_sq (hφ : ContDiffAt ℝ 2 φ α) (hα : φ α = α)
    (h1 : deriv φ α ≠ 1) :
    Tendsto (fun x => (aitkenIterationFunction φ x - α) / (x - α) ^ 2) (𝓝[≠] α)
      (𝓝 (deriv φ α * iteratedDeriv 2 φ α / (2 * (deriv φ α - 1)))) := by
  have hφ' : ContDiffAt ℝ (1 + 1 : ℕ) φ α := by simpa using hφ
  have hφd : HasDerivAt φ (deriv φ α) α := (hφ.differentiableAt (by norm_num)).hasDerivAt
  obtain ⟨hs₁, hs₂, hQ⟩ := tendsto_dslope_aitken hφd hα
  have hQne : (deriv φ α - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 h1)
  -- `t = dslope (dslope φ α) α` is continuous at `α` with value `φ''(α) / 2`
  have hs₁d : HasDerivAt (dslope φ α) (iteratedDeriv 2 φ α / 2) α := by
    have := ((ContDiffAt.dslope_same (n := 1) hφ').differentiableAt (by simp)).hasDerivAt
    rwa [← iteratedDeriv_one, iteratedDeriv_dslope_same hφ', show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num]
      at this
  have ht : Tendsto (dslope (dslope φ α) α) (𝓝 α) (𝓝 (iteratedDeriv 2 φ α / 2)) := by
    have := (continuousAt_dslope_same.2 hs₁d.differentiableAt).tendsto
    rwa [dslope_same, hs₁d.deriv] at this
  have hφc : Tendsto φ (𝓝 α) (𝓝 α) := by simpa [hα] using hφd.continuousAt.tendsto
  have htφ : Tendsto (fun x => dslope (dslope φ α) α (φ x)) (𝓝 α) (𝓝 (iteratedDeriv 2 φ α / 2)) :=
    ht.comp hφc
  have hlim : Tendsto (fun x => dslope φ α x *
      (dslope φ α x * dslope (dslope φ α) α (φ x) - dslope (dslope φ α) α x) /
      (dslope φ α x * dslope φ α (φ x) - 2 * dslope φ α x + 1)) (𝓝[≠] α)
      (𝓝 (deriv φ α * (deriv φ α * (iteratedDeriv 2 φ α / 2) - iteratedDeriv 2 φ α / 2) /
        (deriv φ α - 1) ^ 2)) :=
    ((hs₁.mul ((hs₁.mul htφ).sub ht)).div hQ hQne).mono_left nhdsWithin_le_nhds
  rw [show deriv φ α * (deriv φ α * (iteratedDeriv 2 φ α / 2) - iteratedDeriv 2 φ α / 2) /
      (deriv φ α - 1) ^ 2 = deriv φ α * iteratedDeriv 2 φ α / (2 * (deriv φ α - 1)) by
    field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hQ.eventually (isOpen_ne.mem_nhds hQne))] with x hx hQx
  obtain ⟨-, hformula⟩ := aitkenIterationFunction_sub_eq_dslope hα hx hQx
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  -- `s₂ x - s₁ x = (φ x - α) t (φ x) - (x - α) t x`, and `φ x - α = (x - α) s₁ x`
  have hu : φ x - α = (x - α) * dslope φ α x := by
    have := sub_smul_dslope φ α x
    rw [hα, smul_eq_mul] at this
    exact this.symm
  have hdiff : dslope φ α (φ x) - dslope φ α x =
      (x - α) * (dslope φ α x * dslope (dslope φ α) α (φ x) - dslope (dslope φ α) α x) := by
    have e1 := sub_smul_dslope (dslope φ α) α (φ x)
    have e2 := sub_smul_dslope (dslope φ α) α x
    rw [smul_eq_mul] at e1 e2
    rw [show dslope φ α (φ x) - dslope φ α x =
      (dslope φ α (φ x) - dslope φ α α) - (dslope φ α x - dslope φ α α) by ring, ← e1, ← e2, hu]
    ring
  rw [hformula, hdiff]
  field_simp

/-- **[quarteroni2000numerical] Property 6.7 for `p = 1`, as an order statement**: if `φ` is `C²`
at `α = φ α` with `φ'(α) ≠ 1`, then Aitken's method has iteration order `2` at `α`. -/
theorem hasIterationOrder_aitkenIterationFunction_two (hφ : ContDiffAt ℝ 2 φ α) (hα : φ α = α)
    (h1 : deriv φ α ≠ 1) : HasIterationOrder (aitkenIterationFunction φ) α 2 := by
  have := hasIterationOrder_of_tendsto_sub_div_pow (aitkenIterationFunction_apply_self hα) le_rfl
    (tendsto_aitkenIterationFunction_sub_div_sq hφ hα h1)
  simpa using this

/-- **[quarteroni2000numerical] Property 6.7 for `p ≥ 2`, the limit**: if the iteration `x ↦ φ x`
has order `p ≥ 2` at `α` in the sense of Property 6.4 (`φ^{(i)}(α) = 0` for `1 ≤ i < p`,
`φ^{(p)}(α) ≠ 0`, `φ` `C^p` at `α`), then `(φ_Δ x - α) / (x - α)^{2p-1} → -(φ^{(p)}(α) / p!)²` as
`x → α`, `x ≠ α`. With `φ x - α = e^p h x` (`h` continuous, `h α = c`), `φ (φ x) - α = O(e^{p²})`,
so the numerator of Aitken's error is `-c² e^{2p} + o(e^{2p})` and the denominator `e (1 + o(1))`.
-/
theorem tendsto_aitkenIterationFunction_sub_div_pow_of_iteratedDeriv_eq_zero {p : ℕ}
    (hp : 2 ≤ p) (hφ : ContDiffAt ℝ p φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i < p → iteratedDeriv i φ α = 0) (hp' : iteratedDeriv p φ α ≠ 0) :
    Tendsto (fun x => (aitkenIterationFunction φ x - α) / (x - α) ^ (2 * p - 1)) (𝓝[≠] α)
      (𝓝 (-(iteratedDeriv p φ α / p.factorial) ^ 2)) := by
  -- the factorization `φ x - α = (x - α) ^ p * h x`
  have hiter : ∀ i, 1 ≤ i → iteratedDeriv i (fun x => φ x - α) α = iteratedDeriv i φ α := by
    intro i hi
    rw [show (fun x => φ x - α) = fun x => -α + φ x from funext fun x => by ring,
      iteratedDeriv_const_add (by omega)]
  have hroot : IsRootOfMultiplicity (fun x => φ x - α) α p := by
    refine ⟨fun i hi => ?_, by rwa [hiter p (by omega)]⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [hα]
    · rw [hiter i hi0]
      exact hzero i hi0 hi
  obtain ⟨h, hh, hhα, hfh⟩ := hroot.exists_eq_pow_mul (n := 0)
    (by simpa using hφ.sub contDiffAt_const)
  rw [hiter p (by omega)] at hhα
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hq : 1 ≤ q := by omega
  have hc : Tendsto h (𝓝 α) (𝓝 (h α)) := hh.continuousAt.tendsto
  have hφc : Tendsto φ (𝓝 α) (𝓝 α) := by simpa [hα] using hφ.continuousAt.tendsto
  have hcφ : Tendsto (fun x => h (φ x)) (𝓝 α) (𝓝 (h α)) := hc.comp hφc
  have hpow : ∀ n, 1 ≤ n → Tendsto (fun x : ℝ => (x - α) ^ n) (𝓝 α) (𝓝 0) := by
    intro n hn
    have := ((continuous_id.sub (continuous_const (y := α))).tendsto α).pow n
    simpa [zero_pow (by omega : n ≠ 0)] using this
  -- `R x = 1 - 2 e^q h x + e^{q² + 2q} h x ^ (q+1) h (φ x) → 1`
  have hR : Tendsto (fun x => 1 - 2 * (x - α) ^ q * h x +
      (x - α) ^ (q * q + 2 * q) * h x ^ (q + 1) * h (φ x)) (𝓝 α) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (((hpow q hq).const_mul 2).mul hc)).add
      (((hpow (q * q + 2 * q) (by nlinarith)).mul (hc.pow (q + 1))).mul hcφ)
    simpa using this
  -- `M x = e^{q²} h x ^ (q+1) h (φ x) - h x ^ 2 → -(h α)²`
  have hM : Tendsto (fun x => (x - α) ^ (q * q) * h x ^ (q + 1) * h (φ x) - h x ^ 2) (𝓝 α)
      (𝓝 (-(h α) ^ 2)) := by
    have := (((hpow (q * q) (by nlinarith)).mul (hc.pow (q + 1))).mul hcφ).sub (hc.pow 2)
    simpa using this
  have hlim := ((hM.div hR one_ne_zero).mono_left (nhdsWithin_le_nhds (s := {α}ᶜ)))
  rw [div_one, hhα] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hR.eventually (isOpen_ne.mem_nhds one_ne_zero))] with x hx hRx
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  have hu : φ x - α = (x - α) ^ (q + 1) * h x := hfh x
  have hv : φ (φ x) - α = (φ x - α) ^ (q + 1) * h (φ x) := hfh (φ x)
  have hD : φ (φ x) - 2 * φ x + x = (x - α) * (1 - 2 * (x - α) ^ q * h x +
      (x - α) ^ (q * q + 2 * q) * h x ^ (q + 1) * h (φ x)) := by
    rw [show φ (φ x) - 2 * φ x + x = (φ (φ x) - α) - 2 * (φ x - α) + (x - α) by ring, hv, hu]
    generalize x - α = e
    ring
  have hD' : φ (φ x) - 2 * φ x + x ≠ 0 := hD ▸ mul_ne_zero he hRx
  simp only [Pi.div_apply]
  rw [aitkenIterationFunction_sub_eq hD' α, hD, hv, hu, show 2 * (q + 1) - 1 = 2 * q + 1 by omega]
  generalize x - α = e at he hRx ⊢
  field_simp
  ring

/-- **[quarteroni2000numerical] Property 6.7 for `p ≥ 2`**: if the iteration `x ↦ φ x` has order
`p ≥ 2` at `α` in the sense of Property 6.4, Aitken's method has iteration order `2p - 1` at `α`.
Stated without proof in the book ([isaacson1994analysis] pp. 104–108). -/
theorem hasIterationOrder_aitkenIterationFunction_of_iteratedDeriv_eq_zero {p : ℕ} (hp : 2 ≤ p)
    (hφ : ContDiffAt ℝ p φ α) (hα : φ α = α)
    (hzero : ∀ i, 1 ≤ i → i < p → iteratedDeriv i φ α = 0) (hp' : iteratedDeriv p φ α ≠ 0) :
    HasIterationOrder (aitkenIterationFunction φ) α (2 * p - 1) := by
  have := hasIterationOrder_of_tendsto_sub_div_pow (aitkenIterationFunction_apply_self hα)
    (by omega) (tendsto_aitkenIterationFunction_sub_div_pow_of_iteratedDeriv_eq_zero hp hφ hα
      hzero hp')
  rwa [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at this

end Aitken

section Steffensen

variable {f : ℝ → ℝ} {α : ℝ}

/-- **Steffensen's step** ([quarteroni2000numerical] Exercise 6.5),
`x - f x / ((f (x + f x) - f x) / f x)`: Newton's step with `f'(x)` replaced by the difference
quotient over the step `f x`. -/
noncomputable def steffensenStep (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x - f x / ((f (x + f x) - f x) / f x)

/-- A root of `f` is a fixed point of Steffensen's step. -/
theorem steffensenStep_apply_self (hα : f α = 0) : steffensenStep f α = α := by
  simp [steffensenStep, hα]

/-- **Steffensen is Aitken's Δ² applied to the iteration function `x ↦ x + f x`**, wherever
`f (x + f x) - f x ≠ 0`: the denominators agree, `φ (φ x) - 2 φ x + x = f (x + f x) - f x`, and so
do the numerators after clearing `f x`. -/
theorem steffensenStep_eq_aitkenIterationFunction (f : ℝ → ℝ) (x : ℝ)
    (h : f (x + f x) - f x ≠ 0) :
    steffensenStep f x = aitkenIterationFunction (fun y => y + f y) x := by
  have hden : x + f x + f (x + f x) - 2 * (x + f x) + x ≠ 0 := by
    convert h using 1
    ring
  simp only [steffensenStep, aitkenIterationFunction, hden, ↓reduceIte]
  rw [div_div_eq_mul_div, show x + f x + f (x + f x) - 2 * (x + f x) + x = f (x + f x) - f x by
    ring, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  ring

/-- **[quarteroni2000numerical] Exercise 6.5: Steffensen's method is of second order at a simple
root.** If `f α = 0`, `f` is `C²` at `α` and `f'(α) ≠ 0`, then `steffensenStep f` has iteration
order `2` at `α`. With `φ = id + f`, `φ'(α) = 1 + f'(α) ≠ 1`, so
`hasIterationOrder_aitkenIterationFunction_two` applies through
`steffensenStep_eq_aitkenIterationFunction`; the asymptotic constant is
`(1 + f'(α)) f''(α) / (2 f'(α))`. -/
theorem hasIterationOrder_steffensenStep_two (hα : f α = 0) (hf : ContDiffAt ℝ 2 f α)
    (hf' : deriv f α ≠ 0) : HasIterationOrder (steffensenStep f) α 2 := by
  set φ : ℝ → ℝ := fun y => y + f y with hφdef
  have hφα : φ α = α := by simp [hφdef, hα]
  have hφ : ContDiffAt ℝ 2 φ α := contDiffAt_id.add hf
  have hfd : HasDerivAt f (deriv f α) α := (hf.differentiableAt (by norm_num)).hasDerivAt
  have hφd : HasDerivAt φ (1 + deriv f α) α := (hasDerivAt_id α).add hfd
  have hφ1 : deriv φ α ≠ 1 := by
    rw [hφd.deriv]
    intro h
    exact hf' (by linarith)
  have hlim := tendsto_aitkenIterationFunction_sub_div_sq hφ hφα hφ1
  have heq : ∀ᶠ x in 𝓝[≠] α, (steffensenStep f x - α) / (x - α) ^ 2 =
      (aitkenIterationFunction φ x - α) / (x - α) ^ 2 := by
    filter_upwards [eventually_aitken_denom_ne_zero hφd hφα (by rwa [hφd.deriv] at hφ1)]
      with x hx
    rw [steffensenStep_eq_aitkenIterationFunction f x (by convert hx using 1; simp [hφdef]; ring)]
  have := hasIterationOrder_of_tendsto_sub_div_pow (steffensenStep_apply_self hα) le_rfl
    (hlim.congr' (heq.mono fun x hx => hx.symm))
  simpa using this

end Steffensen

section SteffensenMultiple

variable {f : ℝ → ℝ} {α : ℝ}

/-- The slope of `w ↦ (1 + w) ^ n` at `0` tends to `n`. -/
private theorem tendsto_one_add_pow_sub_one_div (n : ℕ) :
    Tendsto (fun w : ℝ => ((1 + w) ^ n - 1) / w) (𝓝[≠] 0) (𝓝 n) := by
  have hd : HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + 0) ^ (n - 1) * 1) 0 :=
    (hasDerivAt_pow n (1 + 0)).comp 0 ((hasDerivAt_id 0).const_add 1)
  have := hasDerivAt_iff_tendsto_slope.1 hd
  simp only [add_zero, one_pow, mul_one] at this
  refine this.congr fun w => ?_
  simp [slope_def_field]

/-- **[quarteroni2000numerical] Property 6.7, last clause, read correctly**: at a root of
multiplicity `m ≥ 2` of a `C^{m+1}` function, Steffensen's iteration converges only linearly,
with factor `1 - 1/m`: `(steffensenStep f x - α) / (x - α) → 1 - 1/m` as `x → α`, `x ≠ α`. This is
[isaacson1994analysis]'s statement that the book paraphrases; as printed ("the method `x ↦ φ x` is
first-order convergent") it cannot be right, since for any `φ` with `φ'(α) ≠ 1` Aitken's method is
superlinear by `hasDerivAt_aitkenIterationFunction_zero` — the degeneracy occurs precisely because
`φ = id + f` has `φ'(α) = 1` at a multiple root.

Proof: with `f x = e^m h x` (`h` `C¹`, hence Lipschitz near `α`, `h α = c ≠ 0`) and
`w = e^{m-1} h x`, one has `x + f x - α = e (1 + w)`, so
`f (x + f x) - f x = e^m [((1 + w)^m - 1) h(x + f x) + (h(x + f x) - h x)]`, where the bracket is
`e^{m-1} (m c² + o(1))` — the first term by the slope of `(1 + w)^m` at `0`, the second by the
Lipschitz bound `|h(x + f x) - h x| ≤ K |f x|`. Hence
`(steffensenStep f x - α)/e = 1 - h x² / (m c² + o(1)) → 1 - 1/m`. -/
theorem tendsto_steffensenStep_sub_div_of_isRootOfMultiplicity {m : ℕ} (hm : 2 ≤ m)
    (hf : ContDiffAt ℝ (m + 1 : ℕ) f α) (hα : IsRootOfMultiplicity f α m) :
    Tendsto (fun x => (steffensenStep f x - α) / (x - α)) (𝓝[≠] α) (𝓝 (1 - 1 / m)) := by
  obtain ⟨h, hh, hhα, hfh⟩ := hα.exists_eq_pow_mul (n := 1) hf
  have hc0 : h α ≠ 0 := hhα ▸ hα.iteratedDeriv_div_factorial_ne_zero
  obtain ⟨K, t, ht, hK⟩ := hh.exists_lipschitzOnWith
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  have hq : 1 ≤ q := by omega
  have hfα : f α = 0 := hα.eq_zero (by omega)
  have hc : Tendsto h (𝓝 α) (𝓝 (h α)) := hh.continuousAt.tendsto
  have hfc : Tendsto f (𝓝 α) (𝓝 0) := by simpa [hfα] using hf.continuousAt.tendsto
  have hy : Tendsto (fun x => x + f x) (𝓝 α) (𝓝 α) := by
    simpa using (continuous_id.tendsto α).add hfc
  have hcy : Tendsto (fun x => h (x + f x)) (𝓝 α) (𝓝 (h α)) := hc.comp hy
  have hpow : Tendsto (fun x : ℝ => (x - α) ^ q) (𝓝 α) (𝓝 0) := by
    have := ((continuous_id.sub (continuous_const (y := α))).tendsto α).pow q
    simpa [zero_pow (by omega : q ≠ 0)] using this
  -- `w x = (x - α) ^ q * h x → 0`, and `w x ≠ 0` away from `α`
  have hw : Tendsto (fun x => (x - α) ^ q * h x) (𝓝 α) (𝓝 0) := by simpa using hpow.mul hc
  have hh_ne : ∀ᶠ x in 𝓝 α, h x ≠ 0 := hc.eventually (isOpen_ne.mem_nhds hc0)
  have hw_ne : ∀ᶠ x in 𝓝[≠] α, (x - α) ^ q * h x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hh_ne] with x hx hhx
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hx)) hhx
  -- the first part of the bracket, divided by `e ^ q`: `→ (q + 1) c²`
  have h1 : Tendsto (fun x => ((1 + (x - α) ^ q * h x) ^ (q + 1) - 1) / ((x - α) ^ q * h x) *
      h x * h (x + f x)) (𝓝[≠] α) (𝓝 (((q + 1 : ℕ) : ℝ) * h α * h α)) :=
    (((tendsto_one_add_pow_sub_one_div (q + 1)).comp
      (tendsto_nhdsWithin_iff.2 ⟨hw.mono_left nhdsWithin_le_nhds, hw_ne⟩)).mul
      (hc.mono_left nhdsWithin_le_nhds)).mul (hcy.mono_left nhdsWithin_le_nhds)
  -- the second part, divided by `e ^ q`: `→ 0` by the Lipschitz bound
  have h2 : Tendsto (fun x => (h (x + f x) - h x) / (x - α) ^ q) (𝓝[≠] α) (𝓝 0) := by
    have hbound : ∀ᶠ x in 𝓝[≠] α,
        ‖(h (x + f x) - h x) / (x - α) ^ q‖ ≤ (K : ℝ) * |x - α| * |h x| := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds ht, nhdsWithin_le_nhds (hy ht)]
        with x hx hxt hyt
      have he : |x - α| ≠ 0 := abs_ne_zero.2 (sub_ne_zero.2 hx)
      have hK' := hK.dist_le_mul (x + f x) hyt x hxt
      rw [Real.dist_eq, Real.dist_eq, add_sub_cancel_left] at hK'
      rw [Real.norm_eq_abs, abs_div, abs_pow,
        div_le_iff₀ (pow_pos (abs_pos.2 (sub_ne_zero.2 hx)) q)]
      calc |h (x + f x) - h x| ≤ K * |f x| := hK'
        _ = K * (|x - α| ^ (q + 1) * |h x|) := by rw [hfh x, abs_mul, abs_pow]
        _ = K * |x - α| * |h x| * |x - α| ^ q := by ring
    refine squeeze_zero_norm' hbound ?_
    have := ((tendsto_const_nhds (x := (K : ℝ))).mul
      ((continuous_id.sub (continuous_const (y := α))).abs.tendsto α)).mul hc.abs
    simpa using this.mono_left nhdsWithin_le_nhds
  have hB := h1.add h2
  rw [add_zero] at hB
  have hBne : ((q + 1 : ℕ) : ℝ) * h α * h α ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by positivity) hc0) hc0
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (((hc.mono_left nhdsWithin_le_nhds).pow 2).div hB hBne)
  rw [show (1 : ℝ) - h α ^ 2 / (((q + 1 : ℕ) : ℝ) * h α * h α) = 1 - 1 / ((q + 1 : ℕ) : ℝ) by
    field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hh_ne] with x hx hhx
  have he : x - α ≠ 0 := sub_ne_zero.2 hx
  have hw' : (x - α) ^ q * h x ≠ 0 := mul_ne_zero (pow_ne_zero _ he) hhx
  -- the identity `f (x + f x) - f x = e ^ (q + 1) * (e ^ q * B x)`
  have hyα : x + f x - α = (x - α) * (1 + (x - α) ^ q * h x) := by rw [hfh x]; ring
  have hD : f (x + f x) - f x = (x - α) ^ (q + 1) * ((x - α) ^ q *
      (((1 + (x - α) ^ q * h x) ^ (q + 1) - 1) / ((x - α) ^ q * h x) * h x * h (x + f x) +
        (h (x + f x) - h x) / (x - α) ^ q)) := by
    rw [hfh (x + f x), hyα, hfh x, mul_pow]
    generalize x - α = e at he hw' ⊢
    field_simp
    ring
  have hS : (steffensenStep f x - α) / (x - α) =
      1 - f x * f x / (f (x + f x) - f x) / (x - α) := by
    rw [steffensenStep, div_div_eq_mul_div, sub_right_comm, sub_div, div_self he]
  simp only [Pi.div_apply]
  rw [hS, hD, hfh x]
  congr 1
  generalize x - α = e at he ⊢
  rw [div_div, ← mul_div_mul_left (h x ^ 2) _ (pow_ne_zero (2 * q + 2) he)]
  congr 1 <;> ring

end SteffensenMultiple
