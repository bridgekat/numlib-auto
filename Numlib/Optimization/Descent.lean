import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Dual
import Numlib.Analysis.Convex.Gateaux
import Numlib.Analysis.InnerProductSpace.Coercive

/-!
# Descent methods and optimality conditions for unconstrained minimization

Descent methods for the minimization of `f : E → ℝ` on a real normed space
([quarteroni2000numerical] §7.2, §7.2.2, §7.2.6 and Properties 7.9–7.10 of §7.3): descent
directions (`Descent.IsDescentDirection`, `f' x d < 0`), the descent iteration
`x_{k+1} = x_k + α_k d_k` as a relational specification `Descent.IsDescentSequence` on the three
sequences of iterates, directions and step sizes, the decrease of `f` along a descent direction for
every small enough positive step (`Descent.exists_forall_lt_of_isDescentDirection`), the two
standard descent directions on an inner product space — the negative gradient
(`Descent.isDescentDirection_neg_gradient`) and the Newton-like direction `-B⁻¹ ∇f` for a coercive
`B` (`Descent.isDescentDirection_neg_inverse_of_isCoercive`) — the exact-line-search orthogonality
`∇f(x_{k+1})ᵀ d_k = 0` (`Descent.fderiv_apply_eq_zero_of_isLocalMin_line`), the second-order
optimality conditions (`Descent.nonneg_apply_apply_of_isLocalMin`,
`Descent.isLocalMin_of_coercive_second`; the first-order one is Mathlib's
`IsLocalMin.hasFDerivAt_eq_zero`), the variational inequality `0 ≤ f' x* (y - x*)` at a local
minimizer on a convex set (`Descent.fderiv_apply_sub_nonneg_of_isLocalMinOn`, whose convex converse
is `isMinOn_iff_forall_lineDeriv_nonneg` in `Numlib/Analysis/Convex/Gateaux`), and the compactness
fact behind "every cluster point is critical ⇒ `∇f(x_k) → 0`"
(`Descent.tendsto_fderiv_zero_of_forall_clusterPt`).

## Design

Derivatives are data, `f' : E → E →L[ℝ] ℝ`, with `HasFDerivAt f (f' x) x` hypotheses where they
are needed, as in `Numlib/Analysis/Convex/Gateaux`; gradients enter only through the Riesz map,
as the hypothesis `f' x = innerSL ℝ (g x)` (`f' x v = ⟪g x, v⟫`), which unlike Mathlib's
`HasGradientAt` needs no completeness of `E`. Hessians are the
derivative of `f'`, `f'' : E → E →L[ℝ] E →L[ℝ] ℝ` with `HasFDerivAt f' (f'' x) x`, and "positive
definite" is coercivity `c ‖v‖² ≤ f'' x v v`, which in finite dimension is `Matrix.PosDef` of the
Hessian matrix (`Matrix.posDef_iff_isSymmetricCoercive`). No symmetry of `f''` is assumed
anywhere: the second-order conditions are proved along lines `t ↦ f (x + t v)`, where only the
diagonal values `f'' v v` enter.

The book's Property 7.4 (c) reads "if `H(x*)` is positive definite then `x*` is a local
minimizer", omitting the hypothesis `∇f(x*) = 0` without which it is false (`f x = x + x²` at `0`);
`Descent.isLocalMin_of_coercive_second` carries it and concludes with a *strict* local minimum.
-/

open Filter Topology Metric Set

namespace Descent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `d` is a **descent direction** for `f` at `x` when `f' x d < 0`
([quarteroni2000numerical] (7.26), the nondegenerate clause; the book's second clause, `d = 0`
when `∇f x = 0`, is the termination case and is not a direction). -/
def IsDescentDirection (f' : E → E →L[ℝ] ℝ) (x d : E) : Prop := f' x d < 0

/-- The **descent method** `x_{k+1} = x_k + α_k d_k` ([quarteroni2000numerical] (7.25)–(7.26)) as
a relational specification on the sequences of iterates `x`, directions `d` and step sizes `α`:
every step is positive and every direction is a descent direction. Any concrete method
(gradient, Newton, quasi-Newton, nonlinear conjugate gradient) satisfies it until it reaches a
critical point, which is why the convergence theorems quantify over it. -/
structure IsDescentSequence (f' : E → E →L[ℝ] ℝ) (x d : ℕ → E) (α : ℕ → ℝ) : Prop where
  /-- The update rule `x_{k+1} = x_k + α_k d_k`. -/
  step : ∀ k, x (k + 1) = x k + α k • d k
  /-- The step sizes are positive. -/
  pos : ∀ k, 0 < α k
  /-- Every direction is a descent direction at the current iterate. -/
  descent : ∀ k, IsDescentDirection f' (x k) (d k)

/-- If `g'(0) < c` then `g t < g 0 + c t` for every small enough `t > 0`: the one-sided form of
the derivative as a limit of difference quotients. This is the elementary fact behind the decrease
along a descent direction and the termination of backtracking line searches. -/
theorem eventually_lt_add_mul_of_hasDerivAt_lt {g : ℝ → ℝ} {g' c : ℝ} (hg : HasDerivAt g g' 0)
    (hc : g' < c) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g t < g 0 + c * t := by
  filter_upwards [hg.tendsto_slope_zero_right.eventually (gt_mem_nhds hc),
    eventually_mem_nhdsWithin] with t ht ht0
  rw [Set.mem_Ioi] at ht0
  simp only [zero_add, smul_eq_mul] at ht
  rw [inv_mul_lt_iff₀ ht0] at ht
  linarith

/-- **Decrease along a descent direction** ([quarteroni2000numerical] (7.27)–(7.28)): if `f` is
differentiable at `x` and `d` is a descent direction there, then `f (x + α d) < f x` for every
small enough positive step `α`. -/
theorem exists_forall_lt_of_isDescentDirection {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {x d : E}
    (hf : HasFDerivAt f (f' x) x) (hd : IsDescentDirection f' x d) :
    ∃ ε > 0, ∀ α ∈ Set.Ioo (0 : ℝ) ε, f (x + α • d) < f x := by
  have hg : HasDerivAt (fun t : ℝ => f (x + t • d)) (f' x d) 0 := hf.hasLineDerivAt d
  obtain ⟨ε, hε, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.1 (eventually_lt_add_mul_of_hasDerivAt_lt hg hd)
  refine ⟨ε, hε, fun α hα => ?_⟩
  simpa using hsub hα

/-- **Exact line search orthogonality** ([quarteroni2000numerical] Theorem 7.3): if `α` is a local
minimizer of `t ↦ f (x + t d)`, then the derivative of `f` at the new point `x + α d` vanishes in
the direction `d`; with `x_{k+1} = x_k + α_k d_k` this is `∇f(x_{k+1})ᵀ d_k = 0`. -/
theorem fderiv_apply_eq_zero_of_isLocalMin_line {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {x d : E}
    {α : ℝ} (hf : HasFDerivAt f (f' (x + α • d)) (x + α • d))
    (hα : IsLocalMin (fun t : ℝ => f (x + t • d)) α) : f' (x + α • d) d = 0 :=
  hα.hasDerivAt_eq_zero (hf.hasLineDerivAt d).hasDerivAt_line

/-- **Second-order necessary condition** ([quarteroni2000numerical] Property 7.4 (b)): at a local
minimizer `x` of `f`, if `f` is differentiable near `x` and `f'` is differentiable at `x` with
derivative `f''`, then `0 ≤ f'' v v` for every `v`. Only differentiability of `f'` *at* `x` is
needed, no continuity of `f''`: along the line `g t = f (x + t v)` one has `g'(0) = 0` and
`g'` has derivative `f'' v v` at `0`; if that were negative, `g' < 0` just to the right of `0` and
the mean value theorem would give `g t < g 0` there. -/
theorem nonneg_apply_apply_of_isLocalMin {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E →L[ℝ] E →L[ℝ] ℝ} {x : E} (hmin : IsLocalMin f x)
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hf'' : HasFDerivAt f' f'' x) (v : E) :
    0 ≤ f'' v v := by
  by_contra hneg
  rw [not_le] at hneg
  have hℓ : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have h : Continuous fun t : ℝ => x + t • v := by fun_prop
    simpa using h.tendsto 0
  -- the line `g t = f (x + t v)` is differentiable near `0` with derivative `g' t = f' (x + t v) v`
  have hgd : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s : ℝ => f (x + s • v)) (f' (x + t • v) v) t := by
    filter_upwards [hℓ.eventually hf] with t ht
    exact (ht.hasLineDerivAt v).hasDerivAt_line
  -- `g'` has derivative `f'' v v` at `0`
  have hg' : HasDerivAt (fun t : ℝ => f' (x + t • v) v) (f'' v v) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => f' (x + t • v)) (f'' v) 0 := hf''.hasLineDerivAt v
    simpa using h1.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hg'0 : f' (x + (0 : ℝ) • v) v = 0 := by
    rw [zero_smul, add_zero, hmin.hasFDerivAt_eq_zero hf.self_of_nhds]
    rfl
  -- `g' < 0` just to the right of `0`, while `g 0 ≤ g t` there
  have hneg' : ∀ᶠ t in 𝓝[>] (0 : ℝ), f' (x + t • v) v < 0 := by
    filter_upwards [eventually_lt_add_mul_of_hasDerivAt_lt hg' hneg] with t ht
    rw [hg'0] at ht
    linarith
  have hminℓ : ∀ᶠ t in 𝓝 (0 : ℝ), f x ≤ f (x + t • v) := hℓ.eventually hmin
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hneg'.and ((hgd.and hminℓ).filter_mono nhdsWithin_le_nhds))
  rw [Set.mem_Ioi] at hε
  -- the mean value theorem on `[0, ε / 2]`
  have hmem : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨by positivity, by linarith⟩
  have hfc : ContinuousOn (fun s : ℝ => f (x + s • v)) (Set.Icc 0 (ε / 2)) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h
      exact hgd.self_of_nhds.continuousAt.continuousWithinAt
    · exact (hsub ⟨h, hs.2.trans_lt hmem.2⟩).2.1.continuousAt.continuousWithinAt
  obtain ⟨θ, hθ, hθeq⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => f (x + s • v))
    (fun t => f' (x + t • v) v) hmem.1 hfc (fun s hs => (hsub ⟨hs.1, hs.2.trans hmem.2⟩).2.1)
  have h1 := (hsub ⟨hθ.1, hθ.2.trans hmem.2⟩).1
  have h2 := (hsub hmem).2.2
  rw [hθeq, zero_smul, add_zero, sub_zero] at h1
  have h3 : 0 ≤ (f (x + (ε / 2) • v) - f x) / (ε / 2) := div_nonneg (by linarith) (by positivity)
  linarith

/-- **Second-order sufficient condition** ([quarteroni2000numerical] Property 7.4 (c), with the
missing hypothesis `∇f(x*) = 0` restored and the conclusion made strict): if `f' x = 0`, `f` and
`f'` are differentiable on a ball around `x`, `f''` is continuous at `x`, and `f'' x` is coercive,
`c ‖v‖² ≤ f'' x v v` with `c > 0`, then `x` is a strict local minimizer of `f`.

The proof is along lines: with `w = y - x` and `g t = f (x + t w)` one has `g'(0) = 0` and
`g''(t) = f'' (x + t w) w w ≥ (c / 2) ‖w‖²` for `y` close to `x`, so `g'(t) ≥ (c / 2) ‖w‖² t` and
`f y - f x = g 1 - g 0 ≥ (c / 4) ‖w‖² > 0`, by two applications of
`Convex.mul_sub_le_image_sub_of_le_deriv`. No symmetry of `f''` is used. -/
theorem isLocalMin_of_coercive_second {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hf : ∀ y ∈ ball x r, HasFDerivAt f (f' y) y)
    (hf' : ∀ y ∈ ball x r, HasFDerivAt f' (f'' y) y) (hcont : ContinuousAt f'' x)
    (hcrit : f' x = 0) (hpos : ∀ v, c * ‖v‖ ^ 2 ≤ f'' x v v) :
    ∃ δ > 0, ∀ y ∈ ball x δ, y ≠ x → f x < f y := by
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.1 hcont (c / 2) (by positivity)
  refine ⟨min r δ₁, lt_min hr hδ₁, fun y hy hyx => ?_⟩
  set w : E := y - x with hw
  have hw0 : 0 < ‖w‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  have hwlt : ‖w‖ < min r δ₁ := by rw [hw, ← dist_eq_norm]; exact hy
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • w ∈ ball x (min r δ₁) := by
    intro t ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    calc t * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right ht.2 hw0.le
      _ < min r δ₁ := by rw [one_mul]; exact hwlt
  have hmemr : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • w ∈ ball x r := fun t ht =>
    ball_subset_ball (min_le_left _ _) (hmem t ht)
  -- derivatives along the line
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f (x + s • w)) (f' (x + t • w) w) t := fun t ht =>
    ((hf _ (hmemr t ht)).hasLineDerivAt w).hasDerivAt_line
  have hg' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => f' (x + s • w) w) (f'' (x + t • w) w w) t := fun t ht => by
    have h1 : HasDerivAt (fun s : ℝ => f' (x + s • w)) (f'' (x + t • w) w) t :=
      ((hf' _ (hmemr t ht)).hasLineDerivAt w).hasDerivAt_line
    simpa using h1.clm_apply (hasDerivAt_const t w)
  -- the second derivative along the line is bounded below by `m = (c / 2) ‖w‖²`
  set m : ℝ := c / 2 * ‖w‖ ^ 2 with hm
  have hm0 : 0 < m := by positivity
  have hlow : ∀ t ∈ Set.Icc (0 : ℝ) 1, m ≤ f'' (x + t • w) w w := by
    intro t ht
    have h1 : ‖f'' (x + t • w) - f'' x‖ < c / 2 := by
      rw [← dist_eq_norm]
      exact hδ₁' (ball_subset_ball (min_le_right _ _) (hmem t ht))
    have h2 : ‖(f'' (x + t • w) - f'' x) w w‖ ≤ ‖f'' (x + t • w) - f'' x‖ * ‖w‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    have h3 : (f'' (x + t • w) - f'' x) w w = f'' (x + t • w) w w - f'' x w w := by simp
    rw [h3, Real.norm_eq_abs] at h2
    have h4 := hpos w
    have h5 : ‖f'' (x + t • w) - f'' x‖ * ‖w‖ * ‖w‖ ≤ c / 2 * ‖w‖ ^ 2 := by
      rw [sq, ← mul_assoc]
      gcongr
    have h6 := (abs_le.1 (h2.trans h5)).1
    rw [hm]
    linarith
  -- step 1: `g'(t) ≥ m t`
  have step1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, m * t ≤ f' (x + t • w) w := by
    have hcont' : ContinuousOn (fun s : ℝ => f' (x + s • w) w) (Set.Icc 0 1) := fun t ht =>
      (hg' t ht).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun s : ℝ => f' (x + s • w) w) (interior (Set.Icc 0 1)) := by
      rw [interior_Icc]
      exact fun t ht => (hg' t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    have hderiv : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
        m ≤ deriv (fun s : ℝ => f' (x + s • w) w) t := by
      rw [interior_Icc]
      intro t ht
      rw [(hg' t (Ioo_subset_Icc_self ht)).deriv]
      exact hlow t (Ioo_subset_Icc_self ht)
    intro t ht
    have h := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv hcont' hdiff hderiv 0
      (left_mem_Icc.2 zero_le_one) t ht ht.1
    simp only [zero_smul, add_zero, hcrit, zero_apply, sub_zero] at h
    exact h
  -- step 2: `g(1) - g(0) ≥ m / 2`
  have step2 : (0 : ℝ) * (1 - 0) ≤ (f (x + (1 : ℝ) • w) - m * (1 : ℝ) ^ 2 / 2)
      - (f (x + (0 : ℝ) • w) - m * (0 : ℝ) ^ 2 / 2) := by
    have hG : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => f (x + s • w) - m * s ^ 2 / 2)
          (f' (x + t • w) w - m * (2 * t) / 2) t := fun t ht => by
      have h1 : HasDerivAt (fun s : ℝ => m * s ^ 2 / 2) (m * (2 * t) / 2) t := by
        simpa using ((hasDerivAt_pow 2 t).const_mul m).div_const 2
      exact (hg t ht).sub h1
    have hcont' : ContinuousOn (fun s : ℝ => f (x + s • w) - m * s ^ 2 / 2) (Set.Icc 0 1) :=
      fun t ht => (hG t ht).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (fun s : ℝ => f (x + s • w) - m * s ^ 2 / 2)
        (interior (Set.Icc 0 1)) := by
      rw [interior_Icc]
      exact fun t ht => (hG t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    have hderiv : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
        (0 : ℝ) ≤ deriv (fun s : ℝ => f (x + s • w) - m * s ^ 2 / 2) t := by
      rw [interior_Icc]
      intro t ht
      rw [(hG t (Ioo_subset_Icc_self ht)).deriv]
      have := step1 t (Ioo_subset_Icc_self ht)
      linarith
    exact (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv hcont' hdiff hderiv 0
      (left_mem_Icc.2 zero_le_one) 1 (right_mem_Icc.2 zero_le_one) zero_le_one
  simp only [one_smul, zero_smul, add_zero, one_pow, mul_one, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, mul_zero, zero_div, sub_zero] at step2
  rw [hw, add_sub_cancel] at step2
  linarith

/-- **First-order condition on a convex set** ([quarteroni2000numerical] Property 7.9 (1)): a local
minimizer `x` of `f` on a convex set `Ω`, at which `f` is differentiable, satisfies the variational
inequality `0 ≤ f' x (y - x)` for every `y ∈ Ω`. The convex converse, Property 7.9 (2), is
`isMinOn_iff_forall_lineDeriv_nonneg` in `Numlib/Analysis/Convex/Gateaux`. -/
theorem fderiv_apply_sub_nonneg_of_isLocalMinOn {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {Ω : Set E}
    (hΩ : Convex ℝ Ω) {x : E} (hx : x ∈ Ω) (hmin : IsLocalMinOn f Ω x)
    (hf : HasFDerivAt f (f' x) x) : ∀ y ∈ Ω, 0 ≤ f' x (y - x) := by
  intro y hy
  have hcone : y - x ∈ posTangentConeAt Ω x :=
    sub_mem_posTangentConeAt_of_segment_subset (hΩ.segment_subset hx hy)
  exact hmin.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hcone

/-- **Cluster points and the gradient** (the compactness statement behind
[quarteroni2000numerical] Property 7.8): in a proper space, if `f'` is continuous, the sequence
`x` is bounded and every cluster point of `x` is a critical point of `f`, then `f' (x k) → 0`.
Otherwise `f' (x k)` stays outside a neighbourhood `s` of `0` frequently; along that subsequence
`x` has a cluster point `y` (bounded sets in a proper space are relatively compact), which is
critical, so `f' (x k) ∈ s` frequently along the same subsequence — a contradiction. -/
theorem tendsto_fderiv_zero_of_forall_clusterPt [ProperSpace E] {f' : E → E →L[ℝ] ℝ}
    (hcont : Continuous f') {x : ℕ → E} (hb : Bornology.IsBounded (Set.range x))
    (hcl : ∀ y, MapClusterPt y atTop x → f' y = 0) :
    Tendsto (fun k => f' (x k)) atTop (𝓝 0) := by
  by_contra h
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 h
  set l : Filter ℕ := atTop ⊓ 𝓟 {k | f' (x k) ∉ s} with hl
  have : NeBot l := frequently_iff_neBot.1 hfreq
  obtain ⟨y, -, hy⟩ := hb.isCompact_closure.exists_mapClusterPt_of_frequently
    (l := l) (f := x) (Eventually.frequently (Eventually.of_forall fun k =>
      subset_closure (Set.mem_range_self k)))
  have hy0 : f' y = 0 := hcl y (hy.mono inf_le_left)
  have hmem : ∀ᶠ k in l, f' (x k) ∉ s := mem_inf_of_right (mem_principal_self _)
  have hfreq' : ∃ᶠ k in l, x k ∈ f' ⁻¹' s :=
    mapClusterPt_iff_frequently.1 hy _ (hcont.continuousAt.preimage_mem_nhds (by rwa [hy0]))
  obtain ⟨k, hk1, hk2⟩ := (hfreq'.and_eventually hmem).exists
  exact hk2 hk1

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The directional derivative along the negative gradient is `-‖∇f‖²`: if
`f' x = innerSL ℝ (g x)`, then `f' x (-g x) = -‖g x‖ ^ 2`. -/
theorem fderiv_apply_neg_gradient {f' : E → E →L[ℝ] ℝ} {g : E → E} {x : E}
    (hg : f' x = innerSL ℝ (g x)) : f' x (-g x) = -‖g x‖ ^ 2 := by
  rw [hg, map_neg, innerSL_apply_apply, real_inner_self_eq_norm_sq]

/-- **The steepest-descent direction is a descent direction** ([quarteroni2000numerical] §7.2.2):
on an inner product space, if `g x` is the gradient of `f` at `x` (`f' x = innerSL ℝ (g x)`, i.e.
`f' x v = ⟪g x, v⟫`; in a complete space this is `HasGradientAt f (g x) x`) and `g x ≠ 0`, then
`-g x` is a descent direction, since `f' x (-g x) = -‖g x‖² < 0`. -/
theorem isDescentDirection_neg_gradient {f' : E → E →L[ℝ] ℝ} {g : E → E} {x : E}
    (hg : f' x = innerSL ℝ (g x)) (hx : g x ≠ 0) :
    IsDescentDirection f' x (-g x) := by
  change f' x (-g x) < 0
  rw [fderiv_apply_neg_gradient hg]
  exact neg_neg_of_pos (pow_pos (norm_pos_iff.2 hx) 2)

/-- **Newton-like directions with a coercive operator are descent directions**
([quarteroni2000numerical] §7.2.2, §7.2.6): if `g x` is the gradient of `f` at `x`, `g x ≠ 0`, and
`B` is an invertible operator that is coercive (positive definite), then `-B⁻¹ (g x)` is a descent
direction, since `⟪g x, -B⁻¹ g x⟫ = -⟪B u, u⟫ < 0` for `u = B⁻¹ g x ≠ 0`. Newton's method with a
positive definite Hessian and the quasi-Newton directions are instances. -/
theorem isDescentDirection_neg_inverse_of_isCoercive {f' : E → E →L[ℝ] ℝ} {g : E → E} {x : E}
    (hg : f' x = innerSL ℝ (g x)) (hx : g x ≠ 0) (B : E ≃L[ℝ] E)
    (hB : (B : E →ₗ[ℝ] E).IsCoercive) : IsDescentDirection f' x (-(B.symm (g x))) := by
  change f' x (-(B.symm (g x))) < 0
  rw [hg, map_neg, innerSL_apply_apply, neg_lt_zero]
  obtain ⟨u, hu⟩ : ∃ u, u = B.symm (g x) := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by
    intro h0
    apply hx
    rw [← B.apply_symm_apply (g x), ← hu, h0, map_zero]
  have hgu : g x = B u := by rw [hu, B.apply_symm_apply]
  rw [← hu, hgu]
  simpa using hB.inner_self_pos hu0

end InnerProduct

end Descent
