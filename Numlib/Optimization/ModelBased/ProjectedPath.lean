/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.ConvexProjection
import Numlib.Analysis.Convex.Subdifferential.Defs
import Numlib.Analysis.Convex.Duality.Polar
import Numlib.Analysis.Convex.Duality.InnerPairing
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

/-!
# Projected rays in a Hilbert space

Let $C$ be a nonempty closed convex subset of a real Hilbert space $E$, with metric projection
$P_C$. For a base point $x$ and a direction $d$, the **projected ray** is the path
$p(t) = P_C(x + t d)$. This file proves three facts about it. The path becomes constant from a
parameter $s$ on when $d$ is normal to $C$ at $p(s)$. The displacement $\|p(t) - x\|$ is
nondecreasing for $t \ge 0$. The projection of $d$ onto the tangent cone of $C$ at $p(t)$ has norm
at most $\|p(t) - x\| / t$.

## Main definitions

* `Optimization.projectedRay`: the path $t \mapsto P_C(x + t d)$.
* `Optimization.normalDirections`: the normal cone $N_C(x) = \{ v : \langle v, y - x \rangle \le 0
  \text{ for all } y \in C \}$.
* `Optimization.tangentDirections`: the tangent cone $T_C(x)$, the polar cone of $N_C(x)$.

## Main results

* `Optimization.projectedRay_eq_of_normal`: if $s \le t$ and $d \in N_C(p(s))$, then $p(t) = p(s)$.
* `Optimization.projectedRay_eq_self_iff`: for $x \in C$, $p(t) = x$ for all $t \ge 0$ if and only
  if $d \in N_C(x)$.
* `Optimization.norm_projectedRay_sub_le`: $\|p(s) - x\| \le \|p(t) - x\|$ for $0 \le s \le t$.
* `Optimization.norm_tangentProjection_projectedRay_le`: $\|P_{T_C(p(t))}(d)\| \le \|p(t) - x\| / t$
  for $t > 0$.

## Implementation notes

* The metric projection is `bestApprox`. The normal cone is `ConvexAnalysis.normalCone` and the
  polar cone is `ConvexAnalysis.polarCone`, both for the pairing `innerₗ E`.
* The normal cone is defined at every point, also at a point outside $C$.
-/

open scoped RealInnerProductSpace
open ConvexAnalysis

namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **projected ray** with base point $x$ and direction $d$: the path $t \mapsto P_C(x + t d)$,
where $P_C$ is the metric projection `bestApprox C` onto $C$. -/
noncomputable def projectedRay (C : Set E) (x d : E) (t : ℝ) : E :=
  bestApprox C (x + t • d)

/-- The **normal cone** of $C$ at $x$:
$$N_C(x) = \{ v \in E : \langle v, y - x \rangle \le 0 \text{ for all } y \in C \}.$$
It is `ConvexAnalysis.normalCone` for the real inner product pairing, and it is defined also for
$x \notin C$. -/
noncomputable abbrev normalDirections (C : Set E) (x : E) : Set E :=
  normalCone (innerₗ E) C x

/-- The **tangent cone** of $C$ at $x$: the polar cone of the normal cone,
$$T_C(x) = \{ w \in E : \langle v, w \rangle \le 0 \text{ for all } v \in N_C(x) \}.$$
-/
noncomputable abbrev tangentDirections (C : Set E) (x : E) : Set E :=
  polarCone (innerₗ E) (normalDirections C x)

/-- A vector $d$ is in the normal cone $N_C(x)$ if and only if $\langle d, y - x \rangle \le 0$ for
all $y \in C$. -/
theorem mem_normalDirections {C : Set E} {x d : E} :
    d ∈ normalDirections C x ↔ ∀ y ∈ C, ⟪d, y - x⟫ ≤ 0 := by
  simp only [normalDirections, mem_normalCone, innerₗ_apply_apply, real_inner_comm]

section Complete

variable [CompleteSpace E] {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
  (hconv : Convex ℝ C)
include hne hclosed hconv

/-- Let $C$ be a nonempty closed convex subset of a real Hilbert space. Every point $P_C(x + t d)$
of the projected ray is in $C$. -/
theorem projectedRay_mem (x d : E) (t : ℝ) : projectedRay C x d t ∈ C :=
  bestApprox_mem hne hclosed hconv _

/-- Let $C$ be a nonempty closed convex subset of a real Hilbert space, and let $p = P_C(x + t d)$.
The residual $x + t d - p$ is in the normal cone $N_C(p)$. -/
theorem projectedRay_residual_mem_normal (x d : E) (t : ℝ) :
    x + t • d - projectedRay C x d t ∈ normalDirections C (projectedRay C x d t) :=
  mem_normalDirections.mpr (inner_sub_bestApprox_le_zero hne hclosed hconv _)

/-- Let $C$ be a nonempty closed convex subset of a real Hilbert space $E$, let $x, d \in E$, and
let $p(t) = P_C(x + t d)$. If $s \le t$ and the direction $d$ is in the normal cone $N_C(p(s))$,
then
$$p(t) = p(s).$$
Thus the projected ray stops once its direction is normal to $C$ at the projected point. -/
theorem projectedRay_eq_of_normal {x d : E} {s t : ℝ} (hst : s ≤ t)
    (hd : d ∈ normalDirections C (projectedRay C x d s)) :
    projectedRay C x d t = projectedRay C x d s := by
  apply (bestApprox_eq_iff hne hclosed hconv).2
  refine ⟨projectedRay_mem hne hclosed hconv x d s, fun y hy ↦ ?_⟩
  have hr := mem_normalDirections.mp (projectedRay_residual_mem_normal hne hclosed hconv x d s) y hy
  rw [show x + t • d - projectedRay C x d s =
    (x + s • d - projectedRay C x d s) + (t - s) • d by module, inner_add_left,
    real_inner_smul_left]
  exact add_nonpos hr (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hst)
    (mem_normalDirections.mp hd y hy))

/-- Let $C$ be a nonempty closed convex subset of a real Hilbert space $E$, let $x \in C$ and
$d \in E$, and let $p(t) = P_C(x + t d)$. Then $p(t) = x$ for all $t \ge 0$ if and only if $d$
is in the normal cone $N_C(x)$. -/
theorem projectedRay_eq_self_iff {x d : E} (hx : x ∈ C) :
    (∀ t : ℝ, 0 ≤ t → projectedRay C x d t = x) ↔ d ∈ normalDirections C x := by
  constructor
  · intro h
    have hp := (bestApprox_eq_iff hne hclosed hconv).1 (h 1 zero_le_one)
    apply mem_normalDirections.mpr
    intro y hy
    simpa using hp.2 y hy
  · intro h t ht
    apply (bestApprox_eq_iff hne hclosed hconv).2
    refine ⟨hx, fun y hy ↦ ?_⟩
    rw [add_sub_cancel_left, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos ht (mem_normalDirections.mp h y hy)

/-- Let $C$ be a nonempty closed convex subset of a real Hilbert space $E$, let $x, d \in E$, and
let $p(t) = P_C(x + t d)$. The distance from the base point along the projected ray is
nondecreasing: if $0 \le s \le t$, then
$$\|p(s) - x\| \le \|p(t) - x\|.$$

The base point $x$ need not be in $C$. -/
theorem norm_projectedRay_sub_le {x d : E} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖projectedRay C x d s - x‖ ≤ ‖projectedRay C x d t - x‖ := by
  rcases hst.eq_or_lt with rfl | hst
  · exact le_rfl
  let p := projectedRay C x d s
  let q := projectedRay C x d t
  let u := p - x
  let v := q - x
  let z := q - p
  have hp := mem_normalDirections.mp (projectedRay_residual_mem_normal hne hclosed hconv x d s)
    q (projectedRay_mem hne hclosed hconv x d t)
  have hq := mem_normalDirections.mp (projectedRay_residual_mem_normal hne hclosed hconv x d t)
    p (projectedRay_mem hne hclosed hconv x d s)
  change ⟪x + s • d - p, z⟫ ≤ 0 at hp
  change ⟪x + t • d - q, p - q⟫ ≤ 0 at hq
  have hs' : s * ⟪d, z⟫ ≤ ⟪u, z⟫ := by
    rw [show x + s • d - p = s • d - u by dsimp [u]; abel, inner_sub_left,
      real_inner_smul_left, sub_nonpos] at hp
    exact hp
  have ht' : ⟪v, z⟫ ≤ t * ⟪d, z⟫ := by
    rw [show x + t • d - q = t • d - v by dsimp [v]; abel,
      show p - q = -z by dsimp [z]; abel, inner_neg_right, inner_sub_left,
      real_inner_smul_left, neg_nonpos, sub_nonneg] at hq
    exact hq
  have hz : v - u = z := by dsimp [u, v, z]; abel
  have hsq : ‖z‖ ^ 2 = ⟪v, z⟫ - ⟪u, z⟫ := by
    rw [← real_inner_self_eq_norm_sq, ← inner_sub_left, hz]
  have hprod : 0 ≤ (t - s) * ⟪d, z⟫ := by
    linarith [sq_nonneg ‖z‖]
  have hdz : 0 ≤ ⟪d, z⟫ := nonneg_of_mul_nonneg_right hprod (sub_pos.mpr hst)
  have huv : ‖u‖ ^ 2 ≤ ⟪u, v⟫ := by
    have hh := (mul_nonneg hs hdz).trans hs'
    rw [← hz, inner_sub_right, real_inner_self_eq_norm_sq, sub_nonneg] at hh
    exact hh
  change ‖u‖ ≤ ‖v‖
  by_cases hu : u = 0
  · simp [hu]
  · have hh := huv.trans (real_inner_le_norm u v)
    rw [pow_two] at hh
    exact le_of_mul_le_mul_left hh (norm_pos_iff.mpr hu)

/-- Let $C$ be a nonempty closed convex subset of a real Hilbert space $E$, let $x, d \in E$, let
$t > 0$, and let $p = P_C(x + t d)$. The projection of $d$ onto the tangent cone $T_C(p)$ is
bounded by the displacement divided by the parameter:
$$\|P_{T_C(p)}(d)\| \le \frac{\|p - x\|}{t}.$$

The projection onto the tangent cone is `bestApprox (Optimization.tangentDirections C p) d`. The
proof uses that $(x + t d - p)/t$ is in $N_C(p)$, that the projection of a normal vector onto
$T_C(p)$ is $0$, and that the projection onto a closed convex set is $1$-Lipschitz. -/
theorem norm_tangentProjection_projectedRay_le (x d : E) {t : ℝ} (ht : 0 < t) :
    ‖bestApprox (tangentDirections C (projectedRay C x d t)) d‖ ≤
      ‖projectedRay C x d t - x‖ / t := by
  let p := projectedRay C x d t
  let K := tangentDirections C p
  let n := t⁻¹ • (x + t • d - p)
  have hn : n ∈ normalDirections C p := by
    apply mem_normalDirections.mpr
    intro y hy
    rw [show n = t⁻¹ • (x + t • d - p) by rfl, real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le)
      (mem_normalDirections.mp (projectedRay_residual_mem_normal hne hclosed hconv x d t) y hy)
  have hzero : (0 : E) ∈ K := by simp [K, tangentDirections, mem_polarCone]
  have hcl : IsClosed K := by
    unfold K tangentDirections
    apply isClosed_polarCone
  have hco : Convex ℝ K := convex_polarCone _ _
  have hn' : bestApprox K n = 0 := by
    apply (bestApprox_eq_iff ⟨0, hzero⟩ hcl hco).2
    refine ⟨hzero, fun y hy ↦ ?_⟩
    simpa only [sub_zero, innerₗ_apply_apply] using (mem_polarCone.mp hy) n hn
  have h := norm_bestApprox_sub_bestApprox_le ⟨0, hzero⟩ hcl hco d n
  rw [hn', sub_zero] at h
  change ‖bestApprox K d‖ ≤ ‖p - x‖ / t
  convert h using 1
  have heq : d - n = t⁻¹ • (p - x) := by
    rw [show n = t⁻¹ • (t • d - (p - x)) by
      dsimp only [n]
      congr 1
      abel, smul_sub,
      smul_smul, inv_mul_cancel₀ ht.ne', one_smul, sub_sub_cancel]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr ht.le),
    div_eq_mul_inv, mul_comm]

end Complete
end Optimization
