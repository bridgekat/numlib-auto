import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Nemytskii operators on `C(X, ℝ)`

The *Nemytskii*, or *superposition*, operator of a continuous function `f : X × ℝ → ℝ` is
`u ↦ f(·, u ·)` on the Banach space `C(X, ℝ)` of continuous real functions on a compact space `X`.
It is the nonlinearity of a differential or integral equation read as an operator, and the basic
fact about it is that a continuous partial derivative in the second variable makes it Fréchet
differentiable, with derivative *multiplication* by that partial derivative along `u`.

## Main definitions

* `Nemytskii.op f u`: the Nemytskii operator, `x ↦ f (x, u x)`.

## Main results

* `Nemytskii.hasFDerivAt_op`: the Fréchet derivative of `Nemytskii.op f` at `u` is multiplication
  by `f_z(·, u ·)`.

## Implementation notes

Mathlib has no differentiation-under-a-parameter lemma in the supremum norm, so the estimate is
written out.  Its only analytic ingredient is that `f_z` is uniformly continuous on the compact
tube `X × [-(‖u‖ + 1), ‖u‖ + 1]` around the graph of `u`: given `ε > 0` this provides a `δ` such
that `‖v - u‖ < δ` forces `|f (x, v x) - f (x, u x) - f_z (x, u x) (v x - u x)| ≤ ε |v x - u x|`,
by the mean value inequality applied to `z ↦ f (x, z) - f_z (x, u x) z` on the segment from `u x` to
`v x`.  Taking the supremum over `x` is then the whole of the `o(‖v - u‖)` bound.

This is the same argument as the one for the Fréchet derivative of a Urysohn integral operator in
`Numlib.IntegralEquations.Basic`, with the integration in the second space variable removed.
-/

open Set

namespace Nemytskii

variable {X : Type*} [PseudoMetricSpace X]

/-- The **Nemytskii**, or superposition, operator of a continuous `f : X × ℝ → ℝ`, acting on the
continuous real functions on a compact space `X` by `u ↦ f(·, u ·)`. -/
def op (f : C(X × ℝ, ℝ)) (u : C(X, ℝ)) : C(X, ℝ) := ⟨fun x => f (x, u x), by fun_prop⟩

@[simp]
theorem op_apply (f : C(X × ℝ, ℝ)) (u : C(X, ℝ)) (x : X) : op f u x = f (x, u x) := rfl

variable [CompactSpace X]

/-- **The uniform linearization estimate in the second variable.**  If `f : X × ℝ → ℝ` has a
continuous partial derivative `fz` in its second argument, then for every `R` and `ε > 0` there is
`δ > 0` such that `|f (x, t) - f (x, s) - f_z (x, s) (t - s)| ≤ ε |t - s|` for all `x`, `|s| ≤ R`
and `|t - s| < δ`.  The proof is the uniform continuity of `f_z` on the compact tube
`X × [-(R + 1), R + 1]` and the mean value inequality for `z ↦ f (x, z) - f_z (x, s) z` on the
segment from `s` to `t`; it is the analytic content of `Nemytskii.hasFDerivAt_op` and of the
Fréchet derivative of a Urysohn integral operator. -/
theorem exists_abs_sub_sub_mul_le {f fz : C(X × ℝ, ℝ)}
    (hf : ∀ (x : X) (z : ℝ), HasDerivAt (fun t => f (x, t)) (fz (x, z)) z) (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ (x : X) (s t : ℝ), |s| ≤ R → |t - s| < δ →
      |f (x, t) - f (x, s) - fz (x, s) * (t - s)| ≤ ε * |t - s| := by
  set S : Set (X × ℝ) := univ ×ˢ Icc (-(R + 1)) (R + 1) with hS
  have hmemS : ∀ (x : X) (t : ℝ), |t| ≤ R + 1 → (x, t) ∈ S := by
    intro x t ht
    simp only [hS, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc]
    exact abs_le.1 ht
  have hScomp : IsCompact S := isCompact_univ.prod isCompact_Icc
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (hScomp.uniformContinuousOn_of_continuous fz.continuous.continuousOn) ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun x s t hs hts => ?_⟩
  have hsub : ∀ r ∈ uIcc s t, |r - s| ≤ |t - s| := fun r hr => abs_sub_left_of_mem_uIcc hr
  have hR : ∀ r ∈ uIcc s t, |r| ≤ R + 1 := by
    intro r hr
    have h1 := hsub r hr
    have h2 := abs_sub_abs_le_abs_sub r s
    have h3 : |t - s| ≤ 1 := (hts.trans_le (min_le_right _ _)).le
    linarith
  have hbnd : ∀ r ∈ uIcc s t, ‖fz (x, r) - fz (x, s)‖ ≤ ε := by
    intro r hr
    have hdist : dist ((x, r) : X × ℝ) (x, s) < δ₀ := by
      have hde : dist ((x, r) : X × ℝ) (x, s) = |r - s| := by
        simp [Prod.dist_eq, Real.dist_eq]
      rw [hde]
      exact lt_of_le_of_lt (hsub r hr) (hts.trans_le (min_le_left _ _))
    have h := hδ _ (hmemS x r (hR r hr)) _ (hmemS x s (by linarith)) hdist
    rw [Real.dist_eq] at h
    rw [Real.norm_eq_abs]
    exact h.le
  have hderiv : ∀ r ∈ uIcc s t,
      HasDerivWithinAt (fun z => f (x, z) - fz (x, s) * z)
        (fz (x, r) - fz (x, s)) (uIcc s t) r := by
    intro r _
    have h1 : HasDerivAt (fun z : ℝ => fz (x, s) * z) (fz (x, s)) r := by
      simpa using (hasDerivAt_id r).const_mul (fz (x, s))
    exact ((hf x r).sub h1).hasDerivWithinAt
  have hmv := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbnd Set.left_mem_uIcc Set.right_mem_uIcc
  have hmv2 : |f (x, t) - fz (x, s) * t - (f (x, s) - fz (x, s) * s)| ≤ ε * |t - s| := by
    simpa [Real.norm_eq_abs] using hmv
  calc |f (x, t) - f (x, s) - fz (x, s) * (t - s)|
      = |f (x, t) - fz (x, s) * t - (f (x, s) - fz (x, s) * s)| := by congr 1; ring
    _ ≤ ε * |t - s| := hmv2

/-- **The Fréchet derivative of a Nemytskii operator.**  If `f : X × ℝ → ℝ` is continuous and has a
continuous partial derivative `fz` in its second argument, then `u ↦ f(·, u ·)` is Fréchet
differentiable at every `u ∈ C(X, ℝ)`, with derivative the multiplication operator
`y ↦ f_z(·, u ·) · y`. -/
theorem hasFDerivAt_op {f fz : C(X × ℝ, ℝ)}
    (hf : ∀ (x : X) (z : ℝ), HasDerivAt (fun t => f (x, t)) (fz (x, z)) z) (u : C(X, ℝ)) :
    HasFDerivAt (op f) (ContinuousLinearMap.mul ℝ C(X, ℝ) (op fz u)) u := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hlin⟩ := exists_abs_sub_sub_mul_le hf ‖u‖ hε
  filter_upwards [Metric.ball_mem_nhds u hδ] with v hv
  have hvun : ‖v - u‖ < δ := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hv
  refine (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).2 fun x => ?_
  have hy1 : |v x - u x| ≤ ‖v - u‖ := by
    have h := (v - u).norm_coe_le_norm x
    rwa [ContinuousMap.sub_apply, Real.norm_eq_abs] at h
  have huy : |u x| ≤ ‖u‖ := by
    have h := u.norm_coe_le_norm x; rwa [Real.norm_eq_abs] at h
  have hgoal : |f (x, v x) - f (x, u x) - fz (x, u x) * (v x - u x)| ≤ ε * ‖v - u‖ :=
    (hlin x (u x) (v x) huy (hy1.trans_lt hvun)).trans (mul_le_mul_of_nonneg_left hy1 hε.le)
  simpa [Real.norm_eq_abs] using hgoal

end Nemytskii
