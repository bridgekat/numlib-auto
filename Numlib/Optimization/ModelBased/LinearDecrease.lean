/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Optimization.ModelBased.ProjectedPath
import Numlib.Optimization.Optimality.ConstrainedMeasure
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Largest feasible linear decrease

Let $E$ be a real inner product space, $C \subseteq E$, $x \in C$, $v \in E$ and $r \ge 0$. This
file studies the **largest feasible linear decrease**
$$\chi(x, v, r) = \sup\{\langle v, d\rangle : \|d\| \le r,\ x + d \in C\},$$
the largest value of the linear decrement $d \mapsto \langle v, d\rangle$ over the feasible
displacements of length at most $r$. When $v$ is minus a gradient, $\langle v, d\rangle$ is the
decrease of the first-order model along $d$, and $\chi$ measures first-order criticality on $C$.

The value $\chi(x, v, r)$ is nonnegative and nondecreasing in $r$. For convex $C$, the quotient
$\chi(x, v, r)/r$ is nonincreasing in $r > 0$, the map $r \mapsto \chi(x, v, r)$ is
$\|v\|$-Lipschitz on $[0, \infty)$, $\chi(x, v, 1) = 0$ exactly when $v$ lies in the normal cone of
$C$ at $x$, and $\chi(x, g(x), 1)$ is continuous in $x \in C$ for continuous $g$. Finally, $\chi$ is
bounded through the projection of $v$ onto a tangent cone.

## Main definitions

* `Optimization.linearDecrease`: the largest feasible linear decrease $\chi(x, v, r)$.

## Main results

* `Optimization.linearDecrease_antitoneOn_ratio`: for convex $C$, $r \mapsto \chi(x, v, r)/r$ is
  nonincreasing on $(0, \infty)$.
* `Optimization.linearDecrease_lipschitzOnWith_radius`: for convex $C$, $r \mapsto \chi(x, v, r)$ is
  $\|v\|$-Lipschitz on $[0, \infty)$.
* `Optimization.linearDecrease_eq_zero_iff`: for convex $C$, $\chi(x, v, 1) = 0$ if and only if $v$
  is in the normal cone of $C$ at $x$.
* `Optimization.continuousOn_linearDecrease_one`: for convex $C$ and $g$ continuous on $C$,
  $x \mapsto \chi(x, g(x), 1)$ is continuous on $C$.
* `Optimization.linearDecrease_le_tangent`: $\chi(x, v, r) \le \langle v, d\rangle + (r +
  \|d\|)\|p\|$, where $p$ is the projection of $v$ onto the tangent cone of $C$ at $x + d$.

## Implementation notes

* `Optimization.linearDecrease C x v r` is `Optimization.decrementMeasure` for the decrement
  $d \mapsto \langle v, d\rangle$ over `Optimization.feasibleSteps C x`. It is the `sSup` of a set
  of reals. The results assume $x \in C$ and $r \ge 0$, which make the set nonempty; it is bounded
  above by $r\|v\|$.
* The normal cone `Optimization.normalDirections C x` is $\{w : \langle w, y - x\rangle \le 0 \text{
  for all } y \in C\}$, and the tangent cone `Optimization.tangentDirections C x` is its polar cone.
  The projection onto a set is `bestApprox`.
-/

open Metric Filter ConvexAnalysis
open scoped RealInnerProductSpace Topology

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} {x y v w d : E} {r s t : ℝ}

/-- The **largest feasible linear decrease** $\chi(x, v, r) = \sup\{\langle v, d\rangle : \|d\| \le
r,\ x + d \in C\}$, for $C \subseteq E$, $x, v \in E$ and $r \in \mathbb{R}$.

The supremum is `sSup` of a set of reals. If no $d$ with $\|d\| \le r$ has $x + d \in C$ (for
example if $r < 0$), the set is empty and the value is $0$. -/
noncomputable def linearDecrease (C : Set E) (x v : E) (r : ℝ) : ℝ :=
  decrementMeasure (fun d ↦ ⟪v, d⟫) r (feasibleSteps C x)

omit [InnerProductSpace ℝ E] in
private theorem admissible_nonempty (hx : x ∈ C) (hr : 0 ≤ r) :
    (closedBall (0 : E) r ∩ feasibleSteps C x).Nonempty :=
  ⟨0, mem_closedBall_self hr, zero_mem_feasibleSteps.mpr hx⟩

private theorem bddAbove_inner :
    BddAbove ((fun d ↦ ⟪v, d⟫) '' (closedBall 0 r ∩ feasibleSteps C x)) :=
  ⟨‖v‖ * r, by
    rintro _ ⟨d, hd, rfl⟩
    exact (real_inner_le_norm v d).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hd.1) (norm_nonneg v))⟩

/-- If $x + d \in C$ and $\|d\| \le r$, then $\langle v, d\rangle \le \chi(x, v, r)$. -/
theorem inner_le_linearDecrease (hd : x + d ∈ C) (hn : ‖d‖ ≤ r) :
    ⟪v, d⟫ ≤ linearDecrease C x v r :=
  le_decrementMeasure bddAbove_inner ⟨mem_closedBall_zero_iff.mpr hn, hd⟩

/-- Let $x \in C$ and $r \ge 0$. If $\langle v, d\rangle \le b$ for every $d$ with $x + d \in C$ and
$\|d\| \le r$, then $\chi(x, v, r) \le b$. -/
theorem linearDecrease_le (hx : x ∈ C) (hr : 0 ≤ r) {b : ℝ}
    (h : ∀ d, x + d ∈ C → ‖d‖ ≤ r → ⟪v, d⟫ ≤ b) :
    linearDecrease C x v r ≤ b :=
  decrementMeasure_le (admissible_nonempty hx hr) fun d hd ↦
    h d hd.2 (mem_closedBall_zero_iff.mp hd.1)

/-- For $x \in C$ and $r \ge 0$, $\chi(x, v, r) \ge 0$. -/
theorem linearDecrease_nonneg (hx : x ∈ C) (hr : 0 ≤ r) : 0 ≤ linearDecrease C x v r :=
  decrementMeasure_nonneg bddAbove_inner (zero_mem_feasibleSteps.mpr hx) hr (inner_zero_right _)

/-- For $x \in C$ and $0 \le s \le t$, $\chi(x, v, s) \le \chi(x, v, t)$. -/
theorem linearDecrease_mono_radius (hx : x ∈ C) (hs : 0 ≤ s) (hst : s ≤ t) :
    linearDecrease C x v s ≤ linearDecrease C x v t :=
  decrementMeasure_mono_radius (admissible_nonempty hx hs) bddAbove_inner hst

private theorem scale_linearDecrease_le (hc : Convex ℝ C) (hx : x ∈ C)
    (hs : 0 ≤ s) (ht : 0 < t) (hst : s ≤ t) :
    (s / t) * linearDecrease C x v t ≤ linearDecrease C x v s := by
  rw [linearDecrease, ← decrementMeasure_const_mul (div_nonneg hs ht.le)]
  apply decrementMeasure_le (admissible_nonempty hx ht.le)
  intro d hd
  have hsc := div_nonneg hs ht.le
  have hfeas := smul_mem_feasibleSteps hc hx hd.2 hsc ((div_le_one ht).mpr hst)
  have hnorm : ‖(s / t) • d‖ ≤ s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsc]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hd.1) hsc).trans_eq
      (div_mul_cancel₀ s ht.ne')
  simpa only [real_inner_smul_right] using inner_le_linearDecrease (v := v) hfeas hnorm

/-- Let $C \subseteq E$ be convex and $x \in C$. Then the map $r \mapsto \chi(x, v, r)/r$ is
nonincreasing on $(0, \infty)$.

The proof scales a feasible displacement of length at most $t$ by $s/t$, which by convexity
gives a feasible displacement of length at most $s$. -/
theorem linearDecrease_antitoneOn_ratio (hc : Convex ℝ C) (hx : x ∈ C) :
    AntitoneOn (fun r ↦ linearDecrease C x v r / r) (Set.Ioi 0) := by
  intro s hs t ht hst
  change 0 < s at hs
  change 0 < t at ht
  apply (div_le_div_iff₀ ht hs).2
  have hscale := scale_linearDecrease_le (v := v) hc hx hs.le ht hst
  have hscale' : linearDecrease C x v t * s / t ≤ linearDecrease C x v s := by
    convert hscale using 1
    ring
  exact (div_le_iff₀ ht).1 hscale'

private theorem linearDecrease_sub_le_radius (hc : Convex ℝ C) (hx : x ∈ C)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    linearDecrease C x v t - linearDecrease C x v s ≤ (t - s) * ‖v‖ := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have ht := hs.trans_lt hst
  have hscale := scale_linearDecrease_le (v := v) hc hx hs ht hst.le
  have hbound : linearDecrease C x v t ≤ t * ‖v‖ :=
    decrementMeasure_inner_le (admissible_nonempty hx ht.le)
  have hmul := mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr ((div_le_one ht).2 hst.le))
  have heq : (1 - s / t) * (t * ‖v‖) = (t - s) * ‖v‖ := by
    field_simp
  rw [heq] at hmul
  linarith

/-- Let $C \subseteq E$ be convex and $x \in C$. Then $r \mapsto \chi(x, v, r)$ is Lipschitz
continuous on $[0, \infty)$ with constant $\|v\|$:
$$|\chi(x, v, t) - \chi(x, v, s)| \le \|v\|\,|t - s| \quad \text{for } s, t \ge 0.$$
-/
theorem linearDecrease_lipschitzOnWith_radius (hc : Convex ℝ C) (hx : x ∈ C) :
    LipschitzOnWith ‖v‖₊ (linearDecrease C x v) (Set.Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  change 0 ≤ s at hs
  change 0 ≤ t at ht
  simp only [Real.dist_eq, coe_nnnorm]
  rcases le_total s t with h | h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (linearDecrease_mono_radius hx hs h)),
      abs_sub_comm s t, abs_of_nonneg (sub_nonneg.mpr h), mul_comm]
    exact linearDecrease_sub_le_radius hc hx hs h
  · rw [abs_of_nonneg (sub_nonneg.mpr (linearDecrease_mono_radius hx ht h)),
      abs_of_nonneg (sub_nonneg.mpr h), mul_comm]
    exact linearDecrease_sub_le_radius hc hx ht h

/-- Let $C \subseteq E$ be convex and $x \in C$. Then $\chi(x, v, 1) = 0$ if and only if $v$ lies in
the normal cone of $C$ at $x$, that is, $\langle v, y - x\rangle \le 0$ for every $y \in C$.

The normal cone is `Optimization.normalDirections C x`. -/
theorem linearDecrease_eq_zero_iff (hc : Convex ℝ C) (hx : x ∈ C) :
    linearDecrease C x v 1 = 0 ↔ v ∈ normalDirections C x := by
  rw [mem_normalDirections]
  constructor
  · intro h y hy
    let d := y - x
    let a := (1 + ‖d‖)⁻¹
    have hpos : 0 < a := by dsimp [a]; positivity
    have ha : a ≤ 1 := inv_le_one_of_one_le₀ (le_add_of_nonneg_right (norm_nonneg _))
    have hf : a • d ∈ feasibleSteps C x :=
      smul_mem_feasibleSteps hc hx (by simpa [d] using hy) hpos.le ha
    have hn : ‖a • d‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos.le]
      exact (inv_mul_le_one₀ (by positivity : 0 < 1 + ‖d‖)).2 (by linarith)
    have hle := inner_le_linearDecrease (v := v) hf hn
    rw [h, real_inner_smul_right] at hle
    exact nonpos_of_mul_nonpos_right hle hpos
  · intro h
    refine le_antisymm (linearDecrease_le hx zero_le_one fun d hd _ ↦ ?_)
      (linearDecrease_nonneg hx zero_le_one)
    simpa using h (x + d) hd

private theorem linearDecrease_le_of_basePoint (hc : Convex ℝ C) (hx : x ∈ C) (hy : y ∈ C) :
    linearDecrease C x v 1 ≤ linearDecrease C y v 1 + 2 * ‖v‖ * ‖x - y‖ := by
  let h := ‖x - y‖
  have hh : 0 ≤ h := norm_nonneg _
  have hrad : (1 : ℝ) ≤ 1 + h := by linarith
  have h₁ := linearDecrease_sub_le_radius (v := v) hc hy zero_le_one hrad
  apply linearDecrease_le hx zero_le_one
  intro d hd hnorm
  let e := x + d - y
  have he : y + e ∈ C := by
    rwa [show y + e = x + d by dsimp [e]; abel]
  have heq : e = d + (x - y) := by dsimp [e]; abel
  have hen : ‖e‖ ≤ 1 + h := by
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add_left hnorm _)
  have h₂ := inner_le_linearDecrease (v := v) he hen
  rw [heq, inner_add_right] at h₂
  have h₃ : -⟪v, x - y⟫ ≤ ‖v‖ * h :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  linarith

private theorem abs_linearDecrease_sub_le_basePoint (hc : Convex ℝ C)
    (hx : x ∈ C) (hy : y ∈ C) :
    |linearDecrease C x v 1 - linearDecrease C y v 1| ≤ 2 * ‖v‖ * ‖x - y‖ := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [linearDecrease_le_of_basePoint (v := v) hc hx hy]
  · have h := linearDecrease_le_of_basePoint (v := v) hc hy hx
    rw [norm_sub_rev y x] at h
    linarith

private theorem abs_linearDecrease_sub_le_direction (hx : x ∈ C) :
    |linearDecrease C x v 1 - linearDecrease C x w 1| ≤ ‖v - w‖ := by
  apply abs_decrementMeasure_sub_le (admissible_nonempty hx zero_le_one)
    bddAbove_inner bddAbove_inner
  intro d hd
  rw [← inner_sub_left]
  calc
    |⟪v - w, d⟫| ≤ ‖v - w‖ * ‖d‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v - w‖ := by simpa using
      mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hd.1) (norm_nonneg (v - w))

/-- Let $C \subseteq E$ be convex and let $g : E \to E$ be continuous on $C$. Then the map
$x \mapsto \chi(x, g(x), 1)$ is continuous on $C$.

The proof combines the bounds $|\chi(x, v, 1) - \chi(y, v, 1)| \le 2\|v\|\|x - y\|$ for
$x, y \in C$ and $|\chi(x, v, 1) - \chi(x, w, 1)| \le \|v - w\|$. -/
theorem continuousOn_linearDecrease_one (hc : Convex ℝ C) {g : E → E}
    (hg : ContinuousOn g C) : ContinuousOn (fun x ↦ linearDecrease C x (g x) 1) C := by
  intro x hx
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hgx : Tendsto (fun y ↦ ‖g y - g x‖) (𝓝[C] x) (𝓝 0) := by
    simpa only [dist_eq_norm] using tendsto_iff_dist_tendsto_zero.mp (hg x hx)
  have hyx : Tendsto (fun y ↦ ‖y - x‖) (𝓝[C] x) (𝓝 0) := by
    have h : Tendsto (fun y : E ↦ y) (𝓝[C] x) (𝓝 x) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [dist_eq_norm] using tendsto_iff_dist_tendsto_zero.mp h
  have hub : Tendsto (fun y ↦ ‖g y - g x‖ + 2 * ‖g x‖ * ‖y - x‖) (𝓝[C] x) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hgx.add (hyx.const_mul (2 * ‖g x‖))
  refine squeeze_zero' (.of_forall fun _ ↦ dist_nonneg) ?_ hub
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [Real.dist_eq]
  calc
    _ ≤ |linearDecrease C y (g y) 1 - linearDecrease C y (g x) 1| +
        |linearDecrease C y (g x) 1 - linearDecrease C x (g x) 1| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (abs_linearDecrease_sub_le_direction hy)
      (abs_linearDecrease_sub_le_basePoint hc hy hx)

section Tangent

variable [CompleteSpace E]

/-- Let $E$ be complete, $x \in C$, $r \ge 0$ and $d \in E$. Let $p$ be the projection of $v$ onto
the tangent cone of $C$ at $x + d$. Then
$$\chi(x, v, r) \le \langle v, d\rangle + (r + \|d\|)\,\|p\|.$$

The displacement $d$ need not be feasible, and $C$ need not be convex. The tangent cone is
`Optimization.tangentDirections C (x + d)`, the polar of the normal cone
`Optimization.normalDirections C (x + d)`, and $p$ is `bestApprox
(Optimization.tangentDirections C (x + d)) v`. The tangent cone is closed, convex and contains
$0$, so the projection exists because $E$ is complete. -/
theorem linearDecrease_le_tangent (hx : x ∈ C) (hr : 0 ≤ r) :
    linearDecrease C x v r ≤ ⟪v, d⟫ +
      (r + ‖d‖) * ‖bestApprox (tangentDirections C (x + d)) v‖ := by
  let K := tangentDirections C (x + d)
  let p := bestApprox K v
  have hz : (0 : E) ∈ K := zero_mem_polarCone _ _
  have hcl : IsClosed K := isClosed_polarCone
  have hconv : Convex ℝ K := convex_polarCone _ _
  have hp : p ∈ K := bestApprox_mem ⟨0, hz⟩ hcl hconv _
  apply linearDecrease_le hx hr
  intro w hw hnorm
  have he : w - d ∈ K := by
    apply mem_polarCone.mpr
    intro n hn
    have h := mem_normalDirections.mp hn (x + w) hw
    simpa only [innerₗ_apply_apply, add_sub_add_left_eq_sub] using h
  have hpe : p + (w - d) ∈ K := (polarPointedCone _ _).add_mem hp he
  have h := inner_sub_bestApprox_le_zero ⟨0, hz⟩ hcl hconv v _ hpe
  have hlin : ⟪v, w - d⟫ ≤ ⟪p, w - d⟫ := by
    change ⟪v - p, p + (w - d) - p⟫ ≤ 0 at h
    rwa [add_sub_cancel_left, inner_sub_left, sub_nonpos] at h
  have hlen : ‖w - d‖ ≤ r + ‖d‖ :=
    (norm_sub_le _ _).trans (add_le_add_left hnorm _)
  have hbound : ⟪v, w - d⟫ ≤ (r + ‖d‖) * ‖p‖ :=
    hlin.trans ((real_inner_le_norm p _).trans (by
      rw [mul_comm ‖p‖]
      exact mul_le_mul_of_nonneg_right hlen (norm_nonneg p)))
  rw [inner_sub_right] at hbound
  exact sub_le_iff_le_add'.mp hbound

end Tangent

end Optimization
