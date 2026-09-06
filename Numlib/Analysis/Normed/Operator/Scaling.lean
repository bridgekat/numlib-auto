import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Operator norms from the geometry of a ball and its image

Two estimates that bound the operator norm of a continuous linear map by the *size* of the sets it
relates, rather than by a pointwise inequality:

* if the image of a closed ball of radius `r` has norms at most `C`, then `‖T‖ ≤ C / r`;
* if a ball of radius `r` sits inside `S` and the affine map `x ↦ T x + b` sends `S` into a bounded
  set `D`, then `‖T‖ ≤ diam D / (2 r)`.

The second is the estimate behind the reference element technique of the finite element method: for
an affine map `F x̂ = T x̂ + b` of a reference element `K̂` onto an element `K`, it reads
`‖T‖ ≤ h_K / ρ̂` with `h_K` the diameter of `K` and `ρ̂` the diameter of a ball inscribed in `K̂`
([han2009theoretical], Lemma 10.2.2).  Nothing in the statement is specific to a simplex or to a
finite element: only the inscribed ball and the diameter of the image enter.

The scalars are real because the constants are sharp only when the norm of the scalar field is all
of `ℝ≥0`; over a general nontrivially normed field the same argument loses the factor `‖c‖` of
`ContinuousLinearMap.opNorm_le_of_shell`.
-/

open Metric

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A uniform bound on a closed ball bounds the operator norm by the ratio: if `‖T x‖ ≤ C` for every
`x` of norm at most `r > 0`, then `‖T‖ ≤ C / r`.

Unlike `ContinuousLinearMap.opNorm_le_of_ball`, whose hypothesis is already proportional to `‖x‖`,
the bound here is uniform on the ball; the proportional form is recovered by scaling `x` to the
sphere of radius `r`. -/
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

/-- **The affine scaling estimate.**  Let `T` be a continuous linear map, `b` a translation, and
suppose the affine map `x ↦ T x + b` sends a set `S` into a bounded set `D`.  If `S` contains a
closed ball of radius `r > 0`, then

  `‖T‖ ≤ diam D / (2 r)`.

Two antipodal points `c ± z` of the ball have `‖T (c + z) - T (c - z)‖ = 2 ‖T z‖`, and the affine
map moves that difference into `D`, so `2 ‖T z‖ ≤ diam D` for every `‖z‖ ≤ r`; the previous lemma
turns the uniform bound into a bound on the operator norm.

This is [han2009theoretical], Lemma 10.2.2, with the reference element's inscribed ball of diameter
`ρ̂ = 2 r` and the element's diameter `h_K = diam D`.  The translation `b` is unconstrained, and
neither set is assumed convex, closed or nonempty. -/
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

end ContinuousLinearMap
