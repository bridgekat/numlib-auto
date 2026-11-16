/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Nonlinear.ScalarNewton
import Numlib.Nonlinear.Secant

/-!
# Monotone convergence of Newton's method and the secant method for convex monotone functions

Let $\theta$ be convex and strictly decreasing on a convex set $S \subseteq \mathbb{R}$, with
derivative $\theta'$ within $S$, and let $r \in S$ be a root with $\theta'(r) \neq 0$. Start
Newton's method from a point $x_0 \in S$ with $\theta(x_0) > 0$, so that $x_0 < r$. Start the secant
method from points $x_0 < x_1$ of $S$ with $\theta(x_0) > 0$ and $\theta(x_1) > 0$. Then both
methods produce iterates that increase monotonically to $r$, with the global $Q$-linear bound
$$r - x_{k+1} \le \gamma (r - x_k), \qquad \gamma = 1 - \frac{\theta'(r)}{\theta'(x_0)} \in [0,
  1).$$
Both methods converge $Q$-superlinearly when $\theta'$ is continuous at $r$, and Newton's method
converges $Q$-quadratically when $\theta'$ is Lipschitz near $r$. This is Lemma B.8.1 of
[cartis2022evaluation] and Theorem 10.2.2 of [ortega2000iterative]. The concave strictly increasing
case is the image under $\theta \mapsto -\theta$, which leaves both iterations unchanged.

The condition $\theta'(r) \neq 0$ is necessary. The function $\theta(x) = (1 - x)^2$ on $[0, 1]$ is
convex, strictly decreasing and continuously differentiable, but Newton's method from $0$ converges
only linearly with factor $1/2$, and the factor $1 - \theta'(r)/\theta'(x_0)$ is $1$.

## Main definitions

* `Newton.IsConvexAntiRoot`: the standing hypotheses of the convex decreasing case.

## Main results

* `Newton.scalarStep_le_of_convexOn`: a Newton step on a convex function with negative slope never
  passes the root, from either side.
* `Newton.monotone_scalarStep_iterate_of_convexOn`: Lemma B.8.1(i) of [cartis2022evaluation], with
  its concave mirror `Newton.monotone_scalarStep_iterate_of_concaveOn`.
* `Newton.monotone_secant_iterate_of_convexOn`: Lemma B.8.1(ii) of [cartis2022evaluation], with its
  concave mirror `Newton.monotone_secant_iterate_of_concaveOn`.

## Proof outline

The convex case rests on the tangent inequality at the root, $\theta(x) \ge \theta'(r)(x - r)$ for
$x \in S$ with $x < r$. A step $y \mapsto y - \theta(y)/d$ with a negative slope $d$ then satisfies
$r - (y - \theta(y)/d) \le (1 - \theta'(r)/d)(r - y)$. Newton's method takes $d = \theta'(y)$, and
the secant method takes a secant slope.

## Implementation notes

* Superlinear convergence is `ConvergesSuperlinearly` and convergence of order $2$ is
  `ConvergesWithOrder` of `Numlib.Nonlinear.Order`.
* In the concave increasing case, the starting points must satisfy $\theta(x_0) < 0$ (and
  $\theta(x_1) < 0$ for the secant method).
* Iterates that reach the root stay there. So the iterates increase monotonically, but not
  necessarily strictly.
-/

open Filter Topology Set

namespace Newton

/-! ### Elementary inequalities -/

section Ratio

variable {d d₀ t : ℝ}

/-- If $d_0 \le d \le t < 0$, then $1 - t/d \le 1 - t/d_0$. -/
theorem one_sub_div_le_one_sub_div (hd₀ : d₀ ≤ d) (hdt : d ≤ t) (ht : t < 0) :
    1 - t / d ≤ 1 - t / d₀ := by
  have hd : d < 0 := hdt.trans_lt ht
  have hd₀' : d₀ < 0 := hd₀.trans_lt hd
  rw [sub_le_sub_iff_left]
  have := div_le_div_of_nonneg_left (neg_nonneg.2 ht.le) (neg_pos.2 hd) (neg_le_neg hd₀)
  simpa [neg_div_neg_eq] using this

/-- If $d \le t < 0$, then $1 - t/d \in [0, 1)$. -/
theorem one_sub_div_mem_Ico (hdt : d ≤ t) (ht : t < 0) : 1 - t / d ∈ Ico 0 1 := by
  have hd : d < 0 := hdt.trans_lt ht
  refine ⟨sub_nonneg.2 ((div_le_one_of_neg hd).2 hdt), sub_lt_self _ (div_pos_of_neg_of_neg ht hd)⟩

end Ratio

/-- **A Newton step on a convex function with negative slope does not pass a root.** Let
$\theta : \mathbb{R} \to \mathbb{R}$ be convex on $S$, let $r \in S$ with $\theta(r) = 0$, and
let $x \in S$, where $\theta$ has the derivative $\theta'(x) < 0$ within $S$. Then the Newton
step satisfies
$$x - \frac{\theta(x)}{\theta'(x)} \le r.$$

From the left of the root, this says that the tangent line lies below the graph. From the right
of the root, the Newton step overshoots the root, and it can leave $S$. Strict monotonicity of
$\theta$ is not necessary. -/
theorem scalarStep_le_of_convexOn {θ θ' : ℝ → ℝ} {S : Set ℝ} {r x : ℝ} (hc : ConvexOn ℝ S θ)
    (hr : r ∈ S) (hθr : θ r = 0) (hx : x ∈ S) (hd : HasDerivWithinAt θ (θ' x) S x)
    (hneg : θ' x < 0) : scalarStep θ θ' x ≤ r := by
  rw [scalarStep, sub_le_iff_le_add, ← sub_le_iff_le_add']
  rcases lt_trichotomy x r with hxr | rfl | hxr
  · -- `θ'(x) ≤ slope θ x r = -θ x / (r - x)`
    have h := hc.le_slope_of_hasDerivWithinAt hx hr hxr hd
    rw [slope_def_field, hθr, zero_sub, le_div_iff₀ (sub_pos.2 hxr)] at h
    rw [le_div_iff_of_neg hneg]
    linarith
  · rw [hθr, zero_div, sub_self]
  · -- `θ x / (x - r) = slope θ r x ≤ θ'(x)`
    have h := hc.slope_le_of_hasDerivWithinAt hr hx hxr hd
    rw [slope_def_field, hθr, sub_zero, div_le_iff₀ (sub_pos.2 hxr)] at h
    rw [le_div_iff_of_neg hneg]
    linarith

/-- The concave mirror of `Newton.scalarStep_le_of_convexOn`. Let $\theta$ be concave on $S$, let
$r \in S$ with $\theta(r) = 0$, and let $x \in S$, where $\theta$ has the derivative
$\theta'(x) > 0$ within $S$. Then $x - \theta(x)/\theta'(x) \le r$. -/
theorem scalarStep_le_of_concaveOn {θ θ' : ℝ → ℝ} {S : Set ℝ} {r x : ℝ} (hc : ConcaveOn ℝ S θ)
    (hr : r ∈ S) (hθr : θ r = 0) (hx : x ∈ S) (hd : HasDerivWithinAt θ (θ' x) S x)
    (hpos : 0 < θ' x) : scalarStep θ θ' x ≤ r := by
  have h := scalarStep_le_of_convexOn (θ' := fun y => -θ' y) hc.neg hr (by simp [hθr]) hx hd.neg
    (neg_neg_of_pos hpos)
  simpa [scalarStep, neg_div_neg_eq] using h

/-- If $\theta(x) \ge 0$ and $\theta'(x) < 0$, then $x \le x - \theta(x)/\theta'(x)$: the Newton
step does not decrease. -/
theorem le_scalarStep {θ θ' : ℝ → ℝ} {x : ℝ} (hθ : 0 ≤ θ x) (hneg : θ' x < 0) :
    x ≤ scalarStep θ θ' x := by
  rw [scalarStep]
  linarith [div_nonpos_of_nonneg_of_nonpos hθ hneg.le]

/-! ### Standing hypotheses -/

/-- The standing hypotheses of the convex decreasing case of Lemma B.8.1 of [cartis2022evaluation]:
$\theta$ is convex and strictly decreasing on $S$, has the derivative $\theta'(x)$ within $S$ at
every $x \in S$, and has a root $r \in S$ with $\theta'(r) \neq 0$.

Convexity of $\theta$ on $S$ in the sense of `ConvexOn` includes convexity of $S$. -/
structure IsConvexAntiRoot (θ θ' : ℝ → ℝ) (S : Set ℝ) (r : ℝ) : Prop where
  /-- The function $\theta$ is convex on $S$. -/
  convexOn : ConvexOn ℝ S θ
  /-- The function $\theta$ is strictly decreasing on $S$. -/
  strictAntiOn : StrictAntiOn θ S
  /-- The function $\theta$ has the derivative $\theta'(x)$ within $S$ at every $x \in S$. -/
  hasDerivWithinAt : ∀ x ∈ S, HasDerivWithinAt θ (θ' x) S x
  /-- The root $r$ lies in $S$. -/
  mem : r ∈ S
  /-- The point $r$ is a root: $\theta(r) = 0$. -/
  apply_eq_zero : θ r = 0
  /-- The derivative at the root is nonzero: $\theta'(r) \neq 0$. -/
  deriv_ne_zero : θ' r ≠ 0

namespace IsConvexAntiRoot

variable {θ θ' : ℝ → ℝ} {S : Set ℝ} {r : ℝ} (h : IsConvexAntiRoot θ θ' S r)
include h

/-- For $x \in S$, $\theta(x) > 0$ if and only if $x < r$. -/
theorem pos_iff {x : ℝ} (hx : x ∈ S) : 0 < θ x ↔ x < r := by
  rw [← h.apply_eq_zero]
  exact h.strictAntiOn.lt_iff_gt h.mem hx

/-- The derivative $\theta'$ is monotone on $S$, by convexity. -/
theorem monotoneOn_deriv : MonotoneOn θ' S := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  exact (h.convexOn.le_slope_of_hasDerivWithinAt hx hy hlt (h.hasDerivWithinAt x hx)).trans
    (h.convexOn.slope_le_of_hasDerivWithinAt hx hy hlt (h.hasDerivWithinAt y hy))

/-- If $x \in S$ and $x < r$, then $\theta'(x) < 0$. -/
theorem deriv_neg_of_lt {x : ℝ} (hx : x ∈ S) (hxr : x < r) : θ' x < 0 := by
  have hs := h.convexOn.le_slope_of_hasDerivWithinAt hx h.mem hxr (h.hasDerivWithinAt x hx)
  rw [slope_def_field, h.apply_eq_zero, zero_sub] at hs
  exact hs.trans_lt (div_neg_of_neg_of_pos (neg_neg_of_pos ((h.pos_iff hx).2 hxr))
    (sub_pos.2 hxr))

/-- If $S$ has a point $x < r$, then $\theta'(r) < 0$. -/
theorem deriv_root_neg {x : ℝ} (hx : x ∈ S) (hxr : x < r) : θ' r < 0 := by
  refine lt_of_le_of_ne ?_ h.deriv_ne_zero
  have hsub : Icc x r ⊆ S := h.convexOn.1.ordConnected.out hx h.mem
  have hacc : AccPt r (𝓟 (Icc x r)) := by
    rw [accPt_principal_iff_nhdsWithin, Icc_sdiff_right, nhdsWithin_Ico_eq_nhdsLT hxr]
    infer_instance
  exact ((h.hasDerivWithinAt r h.mem).mono hsub).nonpos_of_antitoneOn hacc
    (h.strictAntiOn.antitoneOn.mono hsub)

/-- **The tangent inequality at the root**, (B.8.3) of [cartis2022evaluation]: for $x \in S$ with
$x < r$, $\theta'(r)(x - r) \le \theta(x)$. -/
theorem deriv_root_mul_le {x : ℝ} (hx : x ∈ S) (hxr : x < r) : θ' r * (x - r) ≤ θ x := by
  have hs := h.convexOn.slope_le_of_hasDerivWithinAt hx h.mem hxr (h.hasDerivWithinAt r h.mem)
  rw [slope_def_field, h.apply_eq_zero, zero_sub, div_le_iff₀ (sub_pos.2 hxr)] at hs
  linarith

/-- The error after a step $y \mapsto y - \theta(y)/d$ from $y \in S$ with $y < r$, with any slope
$d < 0$:
$$r - \Bigl(y - \frac{\theta(y)}{d}\Bigr) \le \Bigl(1 - \frac{\theta'(r)}{d}\Bigr)(r - y).$$
Newton's method takes $d = \theta'(y)$, and the secant method takes a secant slope. -/
theorem sub_step_le {y d : ℝ} (hy : y ∈ S) (hyr : y < r) (hd : d < 0) :
    r - (y - θ y / d) ≤ (1 - θ' r / d) * (r - y) := by
  have ht := h.deriv_root_mul_le hy hyr
  have : θ y / d ≤ θ' r * (y - r) / d := div_le_div_of_nonpos_of_le hd.le ht
  have heq : (1 - θ' r / d) * (r - y) = r - y + θ' r * (y - r) / d := by
    field_simp
    ring
  rw [heq]
  linarith

/-! ### Newton's method -/

/-- **One Newton step.** Let $N(y) = y - \theta(y)/\theta'(y)$. For $y \in S$ with $y \le r$, the
step $N(y)$ lies in $[y, r]$ and
$$r - N(y) \le \Bigl(1 - \frac{\theta'(r)}{\theta'(y)}\Bigr)(r - y).$$
This is (B.8.4) of [cartis2022evaluation]. -/
theorem scalarStep_mem_Icc_and_sub_le {y : ℝ} (hy : y ∈ S) (hyr : y ≤ r) :
    scalarStep θ θ' y ∈ Icc y r ∧
      r - scalarStep θ θ' y ≤ (1 - θ' r / θ' y) * (r - y) := by
  rcases hyr.lt_or_eq with hyr | rfl
  · have hneg := h.deriv_neg_of_lt hy hyr
    refine ⟨⟨le_scalarStep ((h.pos_iff hy).2 hyr).le hneg,
      scalarStep_le_of_convexOn h.convexOn h.mem h.apply_eq_zero hy (h.hasDerivWithinAt y hy)
        hneg⟩, h.sub_step_le hy hyr hneg⟩
  · rw [scalarStep_apply_of_eq_zero _ _ h.apply_eq_zero]
    simp

end IsConvexAntiRoot

/-- Let $(x_k)$, $(g_k)$ and $(d_k)$ be real sequences, and let $r \in \mathbb{R}$ and $t \neq 0$.
Assume that $g_k \le d_k \le t$ for every $k$, that $g_k \to t$, and that
$$|x_{k+1} - r| \le \Bigl(1 - \frac{t}{d_k}\Bigr) |x_k - r|$$
for every $k$. Then $x_k$ converges $Q$-superlinearly to $r$. -/
theorem convergesSuperlinearly_of_le_one_sub_div {x g d : ℕ → ℝ} {r t : ℝ} (ht : t ≠ 0)
    (hg : Tendsto g atTop (𝓝 t)) (hgd : ∀ k, g k ≤ d k) (hdt : ∀ k, d k ≤ t)
    (hle : ∀ k, |x (k + 1) - r| ≤ (1 - t / d k) * |x k - r|) : ConvergesSuperlinearly x r := by
  have hd : Tendsto d atTop (𝓝 t) := tendsto_of_tendsto_of_tendsto_of_le_of_le hg
    tendsto_const_nhds hgd hdt
  refine ⟨fun k => 1 - t / d k, ?_, fun k => by simpa [Real.norm_eq_abs] using hle k⟩
  simpa [div_self ht] using (tendsto_const_nhds (x := t)).div hd ht |>.const_sub 1

variable {θ θ' : ℝ → ℝ} {S : Set ℝ} {r x₀ : ℝ}

namespace IsConvexAntiRoot

variable (h : IsConvexAntiRoot θ θ' S r)
include h

/-- The Newton iterates $x_k$ from $x_0 \in S$ with $\theta(x_0) \ge 0$ stay in $[x_0, r]$, and
$x_k \le x_{k+1}$ for every $k$. -/
theorem scalarStep_iterate_mem_Icc (hx₀ : x₀ ∈ S) (hθx₀ : 0 ≤ θ x₀) (k : ℕ) :
    (scalarStep θ θ')^[k] x₀ ∈ Icc x₀ r ∧
      (scalarStep θ θ')^[k] x₀ ≤ (scalarStep θ θ')^[k + 1] x₀ := by
  have hx₀r : x₀ ≤ r := by
    by_contra hlt
    have := (h.strictAntiOn h.mem hx₀ (lt_of_not_ge hlt))
    rw [h.apply_eq_zero] at this
    linarith
  have hsub : Icc x₀ r ⊆ S := h.convexOn.1.ordConnected.out hx₀ h.mem
  have hmem : ∀ k, (scalarStep θ θ')^[k] x₀ ∈ Icc x₀ r := by
    intro k
    induction k with
    | zero => exact ⟨le_rfl, hx₀r⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := (h.scalarStep_mem_Icc_and_sub_le (hsub ih) ih.2).1
      exact ⟨ih.1.trans this.1, this.2⟩
  refine ⟨hmem k, ?_⟩
  rw [Function.iterate_succ_apply']
  exact (h.scalarStep_mem_Icc_and_sub_le (hsub (hmem k)) (hmem k).2).1.1

/-- **Global $Q$-linear bound for Newton's method**, (B.8.4) of [cartis2022evaluation]. Let
$x_0 \in S$ with $\theta(x_0) > 0$. Then the Newton iterates $x_k$ satisfy, for every $k$,
$$r - x_{k+1} \le \Bigl(1 - \frac{\theta'(r)}{\theta'(x_k)}\Bigr)(r - x_k) \quad \text{and}
  \quad 1 - \frac{\theta'(r)}{\theta'(x_k)} \le 1 - \frac{\theta'(r)}{\theta'(x_0)}.$$
-/
theorem sub_scalarStep_iterate_succ_le (hx₀ : x₀ ∈ S) (hθx₀ : 0 < θ x₀) (k : ℕ) :
    r - (scalarStep θ θ')^[k + 1] x₀ ≤
        (1 - θ' r / θ' ((scalarStep θ θ')^[k] x₀)) * (r - (scalarStep θ θ')^[k] x₀) ∧
      (1 - θ' r / θ' ((scalarStep θ θ')^[k] x₀)) ≤ 1 - θ' r / θ' x₀ := by
  have hx₀r : x₀ < r := (h.pos_iff hx₀).1 hθx₀
  have hsub : Icc x₀ r ⊆ S := h.convexOn.1.ordConnected.out hx₀ h.mem
  have hm := (h.scalarStep_iterate_mem_Icc hx₀ hθx₀.le k).1
  have htr := h.deriv_root_neg hx₀ hx₀r
  refine ⟨?_, ?_⟩
  · rw [Function.iterate_succ_apply']
    exact (h.scalarStep_mem_Icc_and_sub_le (hsub hm) hm.2).2
  · exact one_sub_div_le_one_sub_div (h.monotoneOn_deriv hx₀ (hsub hm) hm.1)
      (h.monotoneOn_deriv (hsub hm) h.mem hm.2) htr

/-- The Newton iterates from $x_0 \in S$ with $\theta(x_0) > 0$ converge to the root $r$. -/
theorem tendsto_scalarStep_iterate (hx₀ : x₀ ∈ S) (hθx₀ : 0 < θ x₀) :
    Tendsto (fun k => (scalarStep θ θ')^[k] x₀) atTop (𝓝 r) := by
  have hx₀r : x₀ < r := (h.pos_iff hx₀).1 hθx₀
  have hγ := one_sub_div_mem_Ico (h.monotoneOn_deriv hx₀ h.mem hx₀r.le)
    (h.deriv_root_neg hx₀ hx₀r)
  refine tendsto_of_eventually_norm_sub_succ_le hγ.2 (Eventually.of_forall fun k => ?_)
  have hm := (h.scalarStep_iterate_mem_Icc hx₀ hθx₀.le k).1
  have hm' := (h.scalarStep_iterate_mem_Icc hx₀ hθx₀.le (k + 1)).1
  obtain ⟨h1, h2⟩ := h.sub_scalarStep_iterate_succ_le hx₀ hθx₀ k
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hm'.2),
    abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hm.2)]
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 hm.2))

/-- If $x_0 \in S$, $\theta(x_0) > 0$ and $\theta'$ is continuous at $r$ within $S$, then the Newton
iterates from $x_0$ converge $Q$-superlinearly to $r$. -/
theorem convergesSuperlinearly_scalarStep_iterate (hx₀ : x₀ ∈ S) (hθx₀ : 0 < θ x₀)
    (hcont : ContinuousWithinAt θ' S r) :
    ConvergesSuperlinearly (fun k => (scalarStep θ θ')^[k] x₀) r := by
  have hx₀r : x₀ < r := (h.pos_iff hx₀).1 hθx₀
  have hsub : Icc x₀ r ⊆ S := h.convexOn.1.ordConnected.out hx₀ h.mem
  set x := fun k => (scalarStep θ θ')^[k] x₀ with hx
  have hm : ∀ k, x k ∈ Icc x₀ r := fun k => (h.scalarStep_iterate_mem_Icc hx₀ hθx₀.le k).1
  have hlim : Tendsto x atTop (𝓝[S] r) :=
    tendsto_nhdsWithin_iff.2 ⟨h.tendsto_scalarStep_iterate hx₀ hθx₀,
      Eventually.of_forall fun k => hsub (hm k)⟩
  refine convergesSuperlinearly_of_le_one_sub_div h.deriv_ne_zero (hcont.tendsto.comp hlim)
    (g := fun k => θ' (x k)) (d := fun k => θ' (x k)) (fun _ => le_rfl)
    (fun k => h.monotoneOn_deriv (hsub (hm k)) h.mem (hm k).2) fun k => ?_
  have hm' := hm (k + 1)
  have h1 := (h.sub_scalarStep_iterate_succ_le hx₀ hθx₀ k).1
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hm'.2), abs_sub_comm,
    abs_of_nonneg (sub_nonneg.2 (hm k).2)]
  exact h1

/-- If $x_0 \in S$, $\theta(x_0) > 0$ and $\theta'$ is Lipschitz on a neighbourhood of $r$ within
$S$, then the Newton iterates from $x_0$ converge $Q$-quadratically to $r$. -/
theorem convergesWithOrder_two_scalarStep_iterate (hx₀ : x₀ ∈ S) (hθx₀ : 0 < θ x₀)
    (hL : ∃ K, ∃ U ∈ 𝓝[S] r, LipschitzOnWith K θ' U) :
    ConvergesWithOrder (fun k => (scalarStep θ θ')^[k] x₀) r 2 := by
  obtain ⟨K, U, hU, hK⟩ := hL
  have hx₀r : x₀ < r := (h.pos_iff hx₀).1 hθx₀
  have hsub : Icc x₀ r ⊆ S := h.convexOn.1.ordConnected.out hx₀ h.mem
  have htr := h.deriv_root_neg hx₀ hx₀r
  set x := fun k => (scalarStep θ θ')^[k] x₀ with hx
  have hm : ∀ k, x k ∈ Icc x₀ r := fun k => (h.scalarStep_iterate_mem_Icc hx₀ hθx₀.le k).1
  have hlim : Tendsto x atTop (𝓝[S] r) :=
    tendsto_nhdsWithin_iff.2 ⟨h.tendsto_scalarStep_iterate hx₀ hθx₀,
      Eventually.of_forall fun k => hsub (hm k)⟩
  have hrU : r ∈ U := mem_of_mem_nhdsWithin h.mem hU
  refine ⟨h.tendsto_scalarStep_iterate hx₀ hθx₀, K / (-θ' r) + 1,
    add_pos_of_nonneg_of_pos (div_nonneg K.2 (neg_nonneg.2 htr.le)) one_pos, ?_⟩
  filter_upwards [hlim.eventually hU] with k hk
  have hm' := hm (k + 1)
  have hxk := hm k
  have hdk : θ' (x k) ≤ θ' r := h.monotoneOn_deriv (hsub hxk) h.mem hxk.2
  have hdneg : θ' (x k) < 0 := hdk.trans_lt htr
  have hLip : θ' r - θ' (x k) ≤ K * (r - x k) := by
    have := hK.dist_le_mul r hrU (x k) hk
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hdk),
      abs_of_nonneg (sub_nonneg.2 hxk.2)] at this
    exact this
  have h1 := (h.sub_scalarStep_iterate_succ_le hx₀ hθx₀ k).1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hm'.2),
    abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hxk.2), Real.rpow_two]
  have hfac : 1 - θ' r / θ' (x k) ≤ K / (-θ' r) * (r - x k) :=
    calc 1 - θ' r / θ' (x k) = (θ' r - θ' (x k)) / (-θ' (x k)) := by
          have := hdneg.ne
          field_simp
          ring
      _ ≤ K * (r - x k) / (-θ' (x k)) := div_le_div_of_nonneg_right hLip (neg_nonneg.2 hdneg.le)
      _ ≤ K * (r - x k) / (-θ' r) := div_le_div_of_nonneg_left
          (mul_nonneg K.2 (sub_nonneg.2 hxk.2)) (neg_pos.2 htr) (neg_le_neg hdk)
      _ = K / (-θ' r) * (r - x k) := by ring
  calc r - x (k + 1) ≤ (1 - θ' r / θ' (x k)) * (r - x k) := h1
    _ ≤ K / (-θ' r) * (r - x k) * (r - x k) :=
        mul_le_mul_of_nonneg_right hfac (sub_nonneg.2 hxk.2)
    _ ≤ (K / (-θ' r) + 1) * (r - x k) ^ 2 := by
        have : 0 ≤ (r - x k) ^ 2 := sq_nonneg _
        nlinarith

end IsConvexAntiRoot

/-- **Lemma B.8.1(i)** of [cartis2022evaluation], convex decreasing case. Let $\theta$ be convex and
strictly decreasing on a convex set $S \subseteq \mathbb{R}$, with the derivative $\theta'(x)$
within $S$ at every $x \in S$, and let $r \in S$ be a root with $\theta'(r) \neq 0$. Let
$x_0 \in S$ with $\theta(x_0) > 0$, and let $x_k$ be the Newton iterates (B.8.1),
$x_{k+1} = x_k - \theta(x_k)/\theta'(x_k)$. Then:
* $x_k \in [x_0, r]$ for every $k$, and $(x_k)$ is monotonically increasing;
* $x_k \to r$;
* $\gamma = 1 - \theta'(r)/\theta'(x_0)$ lies in $[0, 1)$, and
  $r - x_{k+1} \le \gamma (r - x_k)$ for every $k$;
* if $\theta'$ is continuous at $r$ within $S$, the convergence is $Q$-superlinear;
* if $\theta'$ is Lipschitz on a neighbourhood of $r$ within $S$, the convergence is
  $Q$-quadratic.

The hypothesis $\theta'(r) \neq 0$ is necessary: for $\theta(x) = (1 - x)^2$ on $[0, 1]$,
Newton's method from $0$ converges only linearly with factor $1/2$, and $\gamma = 1$.

The Newton iterates are `(Newton.scalarStep θ θ')^[k] x₀`. The hypotheses on $\theta$ are
`Newton.IsConvexAntiRoot`. -/
theorem monotone_scalarStep_iterate_of_convexOn (h : IsConvexAntiRoot θ θ' S r) (hx₀ : x₀ ∈ S)
    (hθx₀ : 0 < θ x₀) :
    (∀ k, (scalarStep θ θ')^[k] x₀ ∈ Icc x₀ r) ∧ Monotone (fun k => (scalarStep θ θ')^[k] x₀) ∧
      Tendsto (fun k => (scalarStep θ θ')^[k] x₀) atTop (𝓝 r) ∧
      1 - θ' r / θ' x₀ ∈ Ico 0 1 ∧
      (∀ k, r - (scalarStep θ θ')^[k + 1] x₀ ≤
        (1 - θ' r / θ' x₀) * (r - (scalarStep θ θ')^[k] x₀)) ∧
      (ContinuousWithinAt θ' S r → ConvergesSuperlinearly (fun k => (scalarStep θ θ')^[k] x₀) r) ∧
      ((∃ K, ∃ U ∈ 𝓝[S] r, LipschitzOnWith K θ' U) →
        ConvergesWithOrder (fun k => (scalarStep θ θ')^[k] x₀) r 2) := by
  have hx₀r : x₀ < r := (h.pos_iff hx₀).1 hθx₀
  refine ⟨fun k => (h.scalarStep_iterate_mem_Icc hx₀ hθx₀.le k).1,
    monotone_nat_of_le_succ fun k => (h.scalarStep_iterate_mem_Icc hx₀ hθx₀.le k).2,
    h.tendsto_scalarStep_iterate hx₀ hθx₀,
    one_sub_div_mem_Ico (h.monotoneOn_deriv hx₀ h.mem hx₀r.le) (h.deriv_root_neg hx₀ hx₀r),
    fun k => ?_, h.convergesSuperlinearly_scalarStep_iterate hx₀ hθx₀,
    h.convergesWithOrder_two_scalarStep_iterate hx₀ hθx₀⟩
  obtain ⟨h1, h2⟩ := h.sub_scalarStep_iterate_succ_le hx₀ hθx₀ k
  exact h1.trans (mul_le_mul_of_nonneg_right h2
    (sub_nonneg.2 (h.scalarStep_iterate_mem_Icc hx₀ hθx₀.le k).1.2))

/-- Replacing $\theta$ and $\theta'$ by $-\theta$ and $-\theta'$ leaves the Newton step
$x \mapsto x - \theta(x)/\theta'(x)$ unchanged. -/
theorem scalarStep_neg (θ θ' : ℝ → ℝ) :
    scalarStep (fun x => -θ x) (fun x => -θ' x) = scalarStep θ θ' := by
  funext x
  simp [scalarStep, neg_div_neg_eq]

/-- If $\theta$ is concave and strictly increasing on $S$, with the derivative $\theta'(x)$ within
$S$ at every $x \in S$, and $r \in S$ is a root with $\theta'(r) \neq 0$, then $-\theta$ and
$-\theta'$ satisfy the standing hypotheses `Newton.IsConvexAntiRoot` of the convex decreasing
case. -/
theorem isConvexAntiRoot_neg (hc : ConcaveOn ℝ S θ) (hm : StrictMonoOn θ S)
    (hd : ∀ x ∈ S, HasDerivWithinAt θ (θ' x) S x) (hr : r ∈ S) (hθr : θ r = 0)
    (hθ'r : θ' r ≠ 0) : IsConvexAntiRoot (fun x => -θ x) (fun x => -θ' x) S r where
  convexOn := hc.neg
  strictAntiOn := fun _ hx _ hy hxy => neg_lt_neg (hm hx hy hxy)
  hasDerivWithinAt := fun x hx => (hd x hx).neg
  mem := hr
  apply_eq_zero := by simp [hθr]
  deriv_ne_zero := neg_ne_zero.2 hθ'r

/-- **Lemma B.8.1(i)** of [cartis2022evaluation], concave increasing case. Let $\theta$ be concave
and strictly increasing on $S$, with the derivative $\theta'(x)$ within $S$ at every $x \in S$,
and let $r \in S$ be a root with $\theta'(r) \neq 0$. Let $x_0 \in S$ with $\theta(x_0) < 0$.
Then the Newton iterates from $x_0$ have all the properties of
`Newton.monotone_scalarStep_iterate_of_convexOn`: they lie in $[x_0, r]$, increase
monotonically, converge to $r$ with $r - x_{k+1} \le \gamma (r - x_k)$ for $\gamma = 1 -
\theta'(r)/\theta'(x_0) \in [0, 1)$, converge $Q$-superlinearly if $\theta'$ is continuous at
$r$ within $S$, and converge $Q$-quadratically if $\theta'$ is Lipschitz on a neighbourhood of
$r$ within $S$.

The proof applies `Newton.monotone_scalarStep_iterate_of_convexOn` to $-\theta$. -/
theorem monotone_scalarStep_iterate_of_concaveOn (hc : ConcaveOn ℝ S θ) (hm : StrictMonoOn θ S)
    (hd : ∀ x ∈ S, HasDerivWithinAt θ (θ' x) S x) (hr : r ∈ S) (hθr : θ r = 0)
    (hθ'r : θ' r ≠ 0) (hx₀ : x₀ ∈ S) (hθx₀ : θ x₀ < 0) :
    (∀ k, (scalarStep θ θ')^[k] x₀ ∈ Icc x₀ r) ∧ Monotone (fun k => (scalarStep θ θ')^[k] x₀) ∧
      Tendsto (fun k => (scalarStep θ θ')^[k] x₀) atTop (𝓝 r) ∧
      1 - θ' r / θ' x₀ ∈ Ico 0 1 ∧
      (∀ k, r - (scalarStep θ θ')^[k + 1] x₀ ≤
        (1 - θ' r / θ' x₀) * (r - (scalarStep θ θ')^[k] x₀)) ∧
      (ContinuousWithinAt θ' S r → ConvergesSuperlinearly (fun k => (scalarStep θ θ')^[k] x₀) r) ∧
      ((∃ K, ∃ U ∈ 𝓝[S] r, LipschitzOnWith K θ' U) →
        ConvergesWithOrder (fun k => (scalarStep θ θ')^[k] x₀) r 2) := by
  have h := monotone_scalarStep_iterate_of_convexOn
    (isConvexAntiRoot_neg hc hm hd hr hθr hθ'r) hx₀ (neg_pos.2 hθx₀)
  simp only [scalarStep_neg, neg_div_neg_eq] at h
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun hcont => h.2.2.2.2.2.1 hcont.neg,
    fun ⟨K, U, hU, hK⟩ => h.2.2.2.2.2.2 ⟨K, U, hU, ?_⟩⟩
  intro x hx y hy
  simpa [edist_neg_neg] using hK hx hy

/-! ### The secant method -/

namespace IsConvexAntiRoot

variable (h : IsConvexAntiRoot θ θ' S r)
include h

/-- **One secant step**, (B.8.5)–(B.8.6) of [cartis2022evaluation]. Let $u, v \in S$ with
$u < v \le r$, and let
$$z = v - \frac{v - u}{\theta(v) - \theta(u)}\, \theta(v)$$
be the secant point. Then $z \in [v, r]$, either $v < z$ or $v = r$, and there is a slope $d$
with $\theta'(u) \le d \le \theta'(r)$ and
$$r - z \le \Bigl(1 - \frac{\theta'(r)}{d}\Bigr)(r - v).$$
-/
theorem secant_step {u v : ℝ} (hu : u ∈ S) (hv : v ∈ S) (huv : u < v) (hvr : v ≤ r) :
    (Secant.step θ (u, v)).2 ∈ Icc v r ∧ (v < (Secant.step θ (u, v)).2 ∨ v = r) ∧
      ∃ d, θ' u ≤ d ∧ d ≤ θ' r ∧ r - (Secant.step θ (u, v)).2 ≤ (1 - θ' r / d) * (r - v) := by
  have hdr := h.deriv_root_neg hu (huv.trans_le hvr)
  rcases hvr.lt_or_eq with hvr | rfl
  · -- the secant slope `s = slope θ u v` is negative and lies in `[θ'(u), θ'(v)]`
    set s := slope θ u v with hs
    have hs_lo : θ' u ≤ s :=
      h.convexOn.le_slope_of_hasDerivWithinAt hu hv huv (h.hasDerivWithinAt u hu)
    have hs_hi : s ≤ θ' v :=
      h.convexOn.slope_le_of_hasDerivWithinAt hu hv huv (h.hasDerivWithinAt v hv)
    have hs_neg : s < 0 := hs_hi.trans_lt (h.deriv_neg_of_lt hv hvr)
    have hstep : (Secant.step θ (u, v)).2 = v - θ v / s := by
      simp only [Secant.step, hs, slope_def_field]
      rw [div_div_eq_mul_div]
      ring
    have hθv := (h.pos_iff hv).2 hvr
    rw [hstep]
    refine ⟨⟨by linarith [div_neg_of_pos_of_neg hθv hs_neg], ?_⟩,
      Or.inl (by linarith [div_neg_of_pos_of_neg hθv hs_neg]), s, hs_lo,
      hs_hi.trans (h.monotoneOn_deriv hv h.mem hvr.le), h.sub_step_le hv hvr hs_neg⟩
    -- `z ≤ r`: `s = slope θ u v ≤ slope θ v r = -θ v / (r - v)`
    have hsl : s ≤ slope θ v r := by
      have := h.convexOn.slope_mono hv ⟨hu, huv.ne⟩ ⟨h.mem, hvr.ne'⟩ (huv.trans hvr).le
      rwa [slope_comm] at this
    rw [slope_def_field, h.apply_eq_zero, zero_sub, le_div_iff₀ (sub_pos.2 hvr)] at hsl
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff_of_neg hs_neg]
    linarith
  · have hz : (Secant.step θ (u, v)).2 = v := by
      simp [Secant.step, h.apply_eq_zero]
    rw [hz]
    exact ⟨⟨le_rfl, le_rfl⟩, Or.inr rfl, θ' v, h.monotoneOn_deriv hu h.mem huv.le, le_rfl,
      by simp⟩

/-- The pair invariant of the secant iteration. Let $x_0 < x_1$ be points of $S$ with
$\theta(x_1) \ge 0$. Then the $k$-th pair $(u, v)$ of the secant iteration from $(x_0, x_1)$
satisfies $x_0 \le u \le v \le r$, and either $u < v$ or $u = r$. -/
theorem secant_pair_invariant {x₁ : ℝ} (hx₀ : x₀ ∈ S) (hx₁ : x₁ ∈ S) (h01 : x₀ < x₁)
    (hθx₁ : 0 ≤ θ x₁) (k : ℕ) :
    x₀ ≤ ((Secant.step θ)^[k] (x₀, x₁)).1 ∧
      ((Secant.step θ)^[k] (x₀, x₁)).1 ≤ ((Secant.step θ)^[k] (x₀, x₁)).2 ∧
      ((Secant.step θ)^[k] (x₀, x₁)).2 ≤ r ∧
      (((Secant.step θ)^[k] (x₀, x₁)).1 < ((Secant.step θ)^[k] (x₀, x₁)).2 ∨
        ((Secant.step θ)^[k] (x₀, x₁)).1 = r) := by
  have hx₁r : x₁ ≤ r := by
    by_contra hlt
    have := h.strictAntiOn h.mem hx₁ (lt_of_not_ge hlt)
    rw [h.apply_eq_zero] at this
    linarith
  have hsub : Icc x₀ r ⊆ S := h.convexOn.1.ordConnected.out hx₀ h.mem
  induction k with
  | zero => exact ⟨le_rfl, h01.le, hx₁r, Or.inl h01⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    set p := (Secant.step θ)^[k] (x₀, x₁) with hp
    rw [Function.iterate_succ_apply', ← hp]
    have hpe : p = (p.1, p.2) := rfl
    rcases h4 with h4 | h4
    · have hstep := h.secant_step (hsub ⟨h1, h2.trans h3⟩) (hsub ⟨h1.trans h2, h3⟩) h4 h3
      rw [← hpe] at hstep
      refine ⟨h1.trans h2, hstep.1.1, hstep.1.2, ?_⟩
      simp only [Secant.step]
      rcases hstep.2.1 with h5 | h5
      · exact Or.inl h5
      · exact Or.inr h5
    · have hp2 : p.2 = r := le_antisymm h3 (h4 ▸ h2)
      have hz : (Secant.step θ p).2 = r := by
        simp [Secant.step, hp2, h.apply_eq_zero]
      refine ⟨h1.trans h2, ?_, hz.le, Or.inr hp2⟩
      rw [hz, show (Secant.step θ p).1 = p.2 from rfl, hp2]

end IsConvexAntiRoot

/-- **Lemma B.8.1(ii)** of [cartis2022evaluation], convex decreasing case. Let $\theta$, $\theta'$,
$S$ and $r$ satisfy the hypotheses of `Newton.monotone_scalarStep_iterate_of_convexOn`. Let
$x_0 < x_1$ be points of $S$ with $\theta(x_0) > 0$ and $\theta(x_1) > 0$, and let $x_{k+1}$,
$k \ge 0$, be the secant iterates (B.8.2). Then:
* $x_{k+1} \in [x_0, r]$ for every $k \ge 0$, and the sequence is monotonically increasing;
* $x_k \to r$;
* $\gamma = 1 - \theta'(r)/\theta'(x_0)$ lies in $[0, 1)$, and
  $r - x_{k+2} \le \gamma (r - x_{k+1})$ for every $k \ge 0$;
* if $\theta'$ is continuous at $r$ within $S$, the convergence is $Q$-superlinear.

The secant iterate $x_{k+1}$ is `Secant.iterate θ x₀ x₁ k`, so `Secant.iterate θ x₀ x₁ 0` is
$x_1$. -/
theorem monotone_secant_iterate_of_convexOn (h : IsConvexAntiRoot θ θ' S r) {x₁ : ℝ}
    (hx₀ : x₀ ∈ S) (hx₁ : x₁ ∈ S) (h01 : x₀ < x₁) (hθx₀ : 0 < θ x₀) (hθx₁ : 0 < θ x₁) :
    (∀ k, Secant.iterate θ x₀ x₁ k ∈ Icc x₀ r) ∧ Monotone (Secant.iterate θ x₀ x₁) ∧
      Tendsto (Secant.iterate θ x₀ x₁) atTop (𝓝 r) ∧
      1 - θ' r / θ' x₀ ∈ Ico 0 1 ∧
      (∀ k, r - Secant.iterate θ x₀ x₁ (k + 1) ≤
        (1 - θ' r / θ' x₀) * (r - Secant.iterate θ x₀ x₁ k)) ∧
      (ContinuousWithinAt θ' S r → ConvergesSuperlinearly (Secant.iterate θ x₀ x₁) r) := by
  have hx₀r : x₀ < r := (h.pos_iff hx₀).1 hθx₀
  have hsub : Icc x₀ r ⊆ S := h.convexOn.1.ordConnected.out hx₀ h.mem
  have htr := h.deriv_root_neg hx₀ hx₀r
  set x := Secant.iterate θ x₀ x₁ with hx
  set P := fun k => (Secant.step θ)^[k] (x₀, x₁) with hP
  have hinv := h.secant_pair_invariant hx₀ hx₁ h01 hθx₁.le
  have hxk : ∀ k, x k = (P k).2 := fun k => rfl
  have hxk1 : ∀ k, x (k + 1) = (Secant.step θ (P k)).2 := fun k => by
    simp only [hx, Secant.iterate, Function.iterate_succ_apply', hP]
  have hmem : ∀ k, x k ∈ Icc x₀ r := fun k =>
    ⟨(hinv k).1.trans (hinv k).2.1, (hinv k).2.2.1⟩
  -- one step: the slope estimate `d k ∈ [θ'((P k).1), θ'(r)]`
  have hstep : ∀ k, x k ≤ x (k + 1) ∧ ∃ d, θ' (P k).1 ≤ d ∧ d ≤ θ' r ∧
      r - x (k + 1) ≤ (1 - θ' r / d) * (r - x k) := by
    intro k
    obtain ⟨h1, h2, h3, h4⟩ := hinv k
    rcases h4 with h4 | h4
    · have hs := h.secant_step (hsub ⟨h1, h2.trans h3⟩) (hsub ⟨h1.trans h2, h3⟩) h4 h3
      rw [hxk1, hxk]
      exact ⟨hs.1.1, hs.2.2⟩
    · have hp2 : (P k).2 = r := le_antisymm h3 (h4 ▸ h2)
      have hz : (Secant.step θ (P k)).2 = r := by
        simp [Secant.step, hp2, h.apply_eq_zero]
      rw [hxk1, hxk, hz, hp2]
      exact ⟨le_rfl, θ' r, h4 ▸ le_rfl, le_rfl, by simp⟩
  choose hmono d hd_lo hd_hi hd_le using hstep
  have hP1 : ∀ k, (P k).1 ∈ Icc x₀ r := fun k =>
    ⟨(hinv k).1, (hinv k).2.1.trans (hinv k).2.2.1⟩
  have hlin : ∀ k, r - x (k + 1) ≤ (1 - θ' r / θ' x₀) * (r - x k) := fun k =>
    (hd_le k).trans (mul_le_mul_of_nonneg_right (one_sub_div_le_one_sub_div
      ((h.monotoneOn_deriv hx₀ (hsub (hP1 k)) (hP1 k).1).trans (hd_lo k)) (hd_hi k) htr)
      (sub_nonneg.2 (hmem k).2))
  have hγ := one_sub_div_mem_Ico (h.monotoneOn_deriv hx₀ h.mem hx₀r.le) htr
  have hlim : Tendsto x atTop (𝓝 r) := by
    refine tendsto_of_eventually_norm_sub_succ_le hγ.2 (Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg
      (sub_nonneg.2 (hmem (k + 1)).2), abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hmem k).2)]
    exact hlin k
  refine ⟨hmem, monotone_nat_of_le_succ hmono, hlim, hγ, hlin, fun hcont => ?_⟩
  -- the previous points `(P k).1` also converge to `r`: `(P (k+1)).1 = x k`
  have hP1lim : Tendsto (fun k => (P k).1) atTop (𝓝[S] r) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => hsub (hP1 k)⟩
    rw [← tendsto_add_atTop_iff_nat 1]
    refine hlim.congr fun k => ?_
    simp only [hP, Function.iterate_succ_apply']
    rfl
  refine convergesSuperlinearly_of_le_one_sub_div h.deriv_ne_zero
    (hcont.tendsto.comp hP1lim) hd_lo hd_hi fun k => ?_
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hmem (k + 1)).2), abs_sub_comm,
    abs_of_nonneg (sub_nonneg.2 (hmem k).2)]
  exact hd_le k

/-- Replacing $\theta$ by $-\theta$ leaves the secant step unchanged. -/
theorem secant_step_neg (θ : ℝ → ℝ) : Secant.step (fun x => -θ x) = Secant.step θ := by
  funext s
  simp only [Secant.step]
  congr 1
  rw [← neg_sub', div_neg, neg_mul_neg]

/-- **Lemma B.8.1(ii)** of [cartis2022evaluation], concave increasing case. Let $\theta$ be concave
and strictly increasing on $S$, with the derivative $\theta'(x)$ within $S$ at every $x \in S$,
and let $r \in S$ be a root with $\theta'(r) \neq 0$. Let $x_0 < x_1$ be points of $S$ with
$\theta(x_0) < 0$ and $\theta(x_1) < 0$. Then the secant iterates have all the properties of
`Newton.monotone_secant_iterate_of_convexOn`: they lie in $[x_0, r]$, increase monotonically,
converge to $r$ with the factor $\gamma = 1 - \theta'(r)/\theta'(x_0) \in [0, 1)$, and converge
$Q$-superlinearly if $\theta'$ is continuous at $r$ within $S$.

The proof applies `Newton.monotone_secant_iterate_of_convexOn` to $-\theta$. -/
theorem monotone_secant_iterate_of_concaveOn (hc : ConcaveOn ℝ S θ) (hm : StrictMonoOn θ S)
    (hd : ∀ x ∈ S, HasDerivWithinAt θ (θ' x) S x) (hr : r ∈ S) (hθr : θ r = 0)
    (hθ'r : θ' r ≠ 0) {x₁ : ℝ} (hx₀ : x₀ ∈ S) (hx₁ : x₁ ∈ S) (h01 : x₀ < x₁) (hθx₀ : θ x₀ < 0)
    (hθx₁ : θ x₁ < 0) :
    (∀ k, Secant.iterate θ x₀ x₁ k ∈ Icc x₀ r) ∧ Monotone (Secant.iterate θ x₀ x₁) ∧
      Tendsto (Secant.iterate θ x₀ x₁) atTop (𝓝 r) ∧
      1 - θ' r / θ' x₀ ∈ Ico 0 1 ∧
      (∀ k, r - Secant.iterate θ x₀ x₁ (k + 1) ≤
        (1 - θ' r / θ' x₀) * (r - Secant.iterate θ x₀ x₁ k)) ∧
      (ContinuousWithinAt θ' S r → ConvergesSuperlinearly (Secant.iterate θ x₀ x₁) r) := by
  have h := monotone_secant_iterate_of_convexOn (isConvexAntiRoot_neg hc hm hd hr hθr hθ'r) hx₀
    hx₁ h01 (neg_pos.2 hθx₀) (neg_pos.2 hθx₁)
  have hit : Secant.iterate (fun x => -θ x) x₀ x₁ = Secant.iterate θ x₀ x₁ := by
    funext k
    simp only [Secant.iterate, secant_step_neg]
  simp only [hit, neg_div_neg_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun hcont => h.2.2.2.2.2 hcont.neg⟩

end Newton
