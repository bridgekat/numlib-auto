/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Operator norms from the geometry of a ball and its image

This file bounds the operator norm of a continuous linear map $T : E \to F$ between real normed
spaces by the size of the sets that it relates, instead of by a pointwise inequality. If the image
of a closed ball of radius $r$ has norms at most $C$, then $\|T\| \le C / r$. If a closed ball of
radius $r$ lies in a set $S$ and the affine map $x \mapsto Tx + b$ sends $S$ into a bounded set $D$,
then $\|T\| \le \operatorname{diam} D / (2r)$. The file also writes the operator norm as the
supremum of the ratios $\|Tv\| / \|v\|$ over $v \neq 0$, and, for a real functional $f$, as the
supremum of the signed ratios $f(v) / \|v\|$.

The second estimate is the basis of the reference element technique of the finite element method.
For an affine map $F(\hat x) = T \hat x + b$ of a reference element $\hat K$ onto an element $K$, it
reads $\|T\| \le h_K / \hat\rho$, with $h_K$ the diameter of $K$ and $\hat\rho$ the diameter of a
ball inscribed in $\hat K$ ([han2009theoretical], Lemma 10.2.2). Nothing in the statement is
specific to a simplex or to a finite element: only the inscribed ball and the diameter of the image
enter.

## Main results

* `ContinuousLinearMap.opNorm_le_div_of_norm_le`: if $\|Tx\| \le C$ for all $\|x\| \le r$, then
  $\|T\| \le C / r$.
* `ContinuousLinearMap.opNorm_le_diam_div`: the affine scaling estimate
  $\|T\| \le \operatorname{diam} D / (2r)$.
* `ContinuousLinearMap.iSup_norm_apply_div_eq_opNorm`: $\sup_{v \neq 0} \|f v\| / \|v\| = \|f\|$.
* `ContinuousLinearMap.iSup_apply_div_eq_opNorm`: $\sup_{v \neq 0} f(v) / \|v\| = \|f\|$ for a real
  functional $f$.

## Implementation notes

* The first two results have real scalars, because the constants are sharp only when the norm of the
  scalar field takes all values in $[0, \infty)$. Over a general nontrivially normed field the same
  argument loses the factor $\|c\|$ of `ContinuousLinearMap.opNorm_le_of_shell`.
* A supremum over the nonzero vectors is an indexed supremum `⨆ v : {v // v ≠ 0}` of real numbers.
  When the space is $\{0\}$, this supremum is $0$, which is also the norm of the map.
-/

open Metric

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Let $T : E \to F$ be a continuous linear map between real normed spaces, and let $r > 0$ and
$C \ge 0$. If $\|Tx\| \le C$ for every $x$ with $\|x\| \le r$, then $$\|T\| \le C / r.$$

Unlike `ContinuousLinearMap.opNorm_le_of_ball`, whose hypothesis is already proportional to
$\|x\|$, the bound here is uniform on the ball. The proportional form follows by scaling $x$ to
the sphere of radius $r$. -/
theorem opNorm_le_div_of_norm_le (T : E →L[ℝ] F) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (h : ∀ x : E, ‖x‖ ≤ r → ‖T x‖ ≤ C) : ‖T‖ ≤ C / r := by
  refine T.opNorm_le_bound (by positivity) fun x => ?_
  rcases eq_or_lt_of_le (norm_nonneg x) with hx | hx
  · have : x = 0 := by simpa [eq_comm] using hx
    simp [this]
  · -- scale `x` to the sphere of radius `r` and use the uniform bound there
    have hscale : ‖(r / ‖x‖) • x‖ ≤ r := by
      rw [norm_smul, norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr,
        abs_of_pos hx, div_mul_cancel₀ _ hx.ne']
    have hT := h _ hscale
    rw [map_smul, norm_smul, norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr,
      abs_of_pos hx, div_mul_eq_mul_div, div_le_iff₀ hx] at hT
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    linarith

/-- **The affine scaling estimate.** Let $T : E \to F$ be a continuous linear map between real
normed spaces, let $b \in F$, let $S \subseteq E$, and let $D \subseteq F$ be bounded. Suppose
that $x \mapsto Tx + b$ maps $S$ into $D$, and that $S$ contains a closed ball $\bar B(c, r)$
with $r > 0$. Then $$\|T\| \le \frac{\operatorname{diam} D}{2r}.$$

This is [han2009theoretical], Lemma 10.2.2, with the inscribed ball of the reference element of
diameter $\hat\rho = 2r$ and the diameter $h_K = \operatorname{diam} D$ of the element. The
translation $b$ is arbitrary, and neither $S$ nor $D$ is assumed convex or closed. Two antipodal
points $c \pm z$ of the ball satisfy $\|T(c + z) - T(c - z)\| = 2\|Tz\|$, and the affine map
moves both into $D$, so $2\|Tz\| \le \operatorname{diam} D$ for every $\|z\| \le r$; then
`ContinuousLinearMap.opNorm_le_div_of_norm_le` applies. -/
theorem opNorm_le_diam_div (T : E →L[ℝ] F) {S : Set E} {D : Set F} {c : E} {b : F} {r : ℝ}
    (hr : 0 < r) (hD : Bornology.IsBounded D) (hball : closedBall c r ⊆ S)
    (hmaps : ∀ x ∈ S, T x + b ∈ D) : ‖T‖ ≤ diam D / (2 * r) := by
  have key : ∀ z : E, ‖z‖ ≤ r → ‖T z‖ ≤ diam D / 2 := by
    intro z hz
    have hmem₁ : c + z ∈ S := hball (by simpa [mem_closedBall, dist_eq_norm] using hz)
    have hmem₂ : c - z ∈ S := hball (by simpa [mem_closedBall, dist_eq_norm] using hz)
    have hd := dist_le_diam_of_mem hD (hmaps _ hmem₁) (hmaps _ hmem₂)
    have hval : dist (T (c + z) + b) (T (c - z) + b) = 2 * ‖T z‖ := by
      rw [dist_eq_norm]
      have hlin : T (c + z) - T (c - z) = (2 : ℝ) • T z := by
        rw [← map_sub, show c + z - (c - z) = (2 : ℝ) • z by rw [two_smul]; abel, map_smul]
      have : T (c + z) + b - (T (c - z) + b) = (2 : ℝ) • T z := by rw [← hlin]; abel
      rw [this, norm_smul]
      simp
    rw [hval] at hd
    linarith
  have := T.opNorm_le_div_of_norm_le hr (by positivity) key
  rwa [div_div] at this

/-! ### The operator norm as a supremum of ratios -/

section Supremum

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **The operator norm is the supremum of the ratios.** Let $E$ and $F$ be normed spaces over a
nontrivially normed field, and let $f : E \to F$ be a continuous linear map. Then $$\sup_{v \neq
0} \frac{\|f v\|}{\|v\|} = \|f\|.$$ When $E = \{0\}$, the supremum over the empty set is $0$,
and so is $\|f\|$. -/
theorem iSup_norm_apply_div_eq_opNorm (f : E →L[𝕜] F) :
    (⨆ v : {v : E // v ≠ 0}, ‖f v‖ / ‖(v : E)‖) = ‖f‖ := by
  refine le_antisymm (Real.iSup_le (fun v => f.ratio_le_opNorm v) (norm_nonneg _)) ?_
  refine f.opNorm_le_bound (Real.iSup_nonneg fun v => by positivity) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [← div_le_iff₀ (norm_pos_iff.mpr hv)]
    exact le_ciSup (f := fun v : {v : E // v ≠ 0} => ‖f v‖ / ‖(v : E)‖)
      ⟨‖f‖, Set.forall_mem_range.2 fun v => f.ratio_le_opNorm v⟩ ⟨v, hv⟩

/-- **The norm of a real functional is the supremum of the signed ratios.** Let $X$ be a real normed
space and let $f : X \to \mathbb{R}$ be a continuous linear functional. Then $$\sup_{v \neq 0}
\frac{f(v)}{\|v\|} = \|f\|.$$ When $X = \{0\}$, both sides are $0$.

No absolute value is needed, because $v \mapsto -v$ is a bijection of the nonzero vectors.
[han2009theoretical], (8.7.2), writes the inf–sup condition in this form. -/
theorem iSup_apply_div_eq_opNorm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →L[ℝ] ℝ) : (⨆ v : {v : X // v ≠ 0}, f v / ‖(v : X)‖) = ‖f‖ := by
  have hle : ∀ v : {v : X // v ≠ 0}, f v / ‖(v : X)‖ ≤ ‖f‖ := fun v =>
    (div_le_div_of_nonneg_right (le_abs_self _) (norm_nonneg _)).trans
      (by rw [← Real.norm_eq_abs]; exact f.ratio_le_opNorm v)
  have hbdd : BddAbove (Set.range fun v : {v : X // v ≠ 0} => f v / ‖(v : X)‖) :=
    ⟨‖f‖, Set.forall_mem_range.2 hle⟩
  refine le_antisymm (Real.iSup_le hle (norm_nonneg _)) ?_
  rw [← f.iSup_norm_apply_div_eq_opNorm]
  rcases isEmpty_or_nonempty {v : X // v ≠ 0} with hX | hX
  · simp only [Real.iSup_of_isEmpty, le_refl]
  refine ciSup_le fun v => ?_
  rcases abs_choice (f (v : X)) with h | h
  · rw [Real.norm_eq_abs, h]
    exact le_ciSup hbdd v
  · have := le_ciSup hbdd (⟨-(v : X), neg_ne_zero.mpr v.2⟩ : {w : X // w ≠ 0})
    rw [show ((⟨-(v : X), neg_ne_zero.mpr v.2⟩ : {w : X // w ≠ 0}) : X) = -(v : X) from rfl,
      map_neg, norm_neg] at this
    rwa [Real.norm_eq_abs, h]

end Supremum

end ContinuousLinearMap
