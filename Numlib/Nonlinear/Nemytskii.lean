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

/-- **The Fréchet derivative of a Nemytskii operator.**  If `f : X × ℝ → ℝ` is continuous and has a
continuous partial derivative `fz` in its second argument, then `u ↦ f(·, u ·)` is Fréchet
differentiable at every `u ∈ C(X, ℝ)`, with derivative the multiplication operator
`y ↦ f_z(·, u ·) · y`. -/
theorem hasFDerivAt_op {f fz : C(X × ℝ, ℝ)}
    (hf : ∀ (x : X) (z : ℝ), HasDerivAt (fun t => f (x, t)) (fz (x, z)) z) (u : C(X, ℝ)) :
    HasFDerivAt (op f) (ContinuousLinearMap.mul ℝ C(X, ℝ) (op fz u)) u := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  set S : Set (X × ℝ) := univ ×ˢ Icc (-(‖u‖ + 1)) (‖u‖ + 1) with hS
  have hmemS : ∀ (x : X) (t : ℝ), |t| ≤ ‖u‖ + 1 → (x, t) ∈ S := by
    intro x t ht
    simp only [hS, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Icc]
    exact abs_le.1 ht
  have hScomp : IsCompact S := isCompact_univ.prod isCompact_Icc
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (hScomp.uniformContinuousOn_of_continuous fz.continuous.continuousOn) ε hε
  filter_upwards [Metric.ball_mem_nhds u (lt_min hδ₀ one_pos)] with v hv
  have hvun : ‖v - u‖ < min δ₀ 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hv
  refine (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).2 fun x => ?_
  have hy1 : |v x - u x| ≤ ‖v - u‖ := by
    have h := (v - u).norm_coe_le_norm x
    rwa [ContinuousMap.sub_apply, Real.norm_eq_abs] at h
  have hy1' := abs_le.1 hy1
  have huy : |u x| ≤ ‖u‖ := by
    have h := u.norm_coe_le_norm x; rwa [Real.norm_eq_abs] at h
  have hvu1 : ‖v - u‖ ≤ 1 := (hvun.trans_le (min_le_right _ _)).le
  have hsub : ∀ t ∈ uIcc (u x) (v x), |t - u x| ≤ ‖v - u‖ := by
    intro t ht
    have h1 : uIcc (u x) (v x) ⊆ Icc (u x - ‖v - u‖) (u x + ‖v - u‖) :=
      Set.uIcc_subset_Icc ⟨by linarith [norm_nonneg (v - u)], by
        linarith [norm_nonneg (v - u)]⟩ ⟨by linarith [hy1'.1], by linarith [hy1'.2]⟩
    have h2 := Set.mem_Icc.1 (h1 ht)
    exact abs_le.2 ⟨by linarith [h2.1], by linarith [h2.2]⟩
  have hR : ∀ t ∈ uIcc (u x) (v x), |t| ≤ ‖u‖ + 1 := by
    intro t ht
    have h1 := hsub t ht
    have h2 := abs_sub_abs_le_abs_sub t (u x)
    linarith
  have hbnd : ∀ t ∈ uIcc (u x) (v x), ‖fz (x, t) - fz (x, u x)‖ ≤ ε := by
    intro t ht
    have hdist : dist ((x, t) : X × ℝ) (x, u x) < δ₀ := by
      have hde : dist ((x, t) : X × ℝ) (x, u x) = |t - u x| := by
        simp [Prod.dist_eq, Real.dist_eq]
      rw [hde]
      exact lt_of_le_of_lt (hsub t ht) (hvun.trans_le (min_le_left _ _))
    have h := hδ _ (hmemS x t (hR t ht)) _ (hmemS x (u x) (by linarith)) hdist
    rw [Real.dist_eq] at h
    rw [Real.norm_eq_abs]
    exact h.le
  have hderiv : ∀ t ∈ uIcc (u x) (v x),
      HasDerivWithinAt (fun z => f (x, z) - fz (x, u x) * z)
        (fz (x, t) - fz (x, u x)) (uIcc (u x) (v x)) t := by
    intro t _
    have h1 : HasDerivAt (fun z : ℝ => fz (x, u x) * z) (fz (x, u x)) t := by
      simpa using (hasDerivAt_id t).const_mul (fz (x, u x))
    exact ((hf x t).sub h1).hasDerivWithinAt
  have hmv := (convex_uIcc (u x) (v x)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbnd Set.left_mem_uIcc Set.right_mem_uIcc
  have hmv2 : |f (x, v x) - fz (x, u x) * v x - (f (x, u x) - fz (x, u x) * u x)|
      ≤ ε * |v x - u x| := by
    simpa [Real.norm_eq_abs] using hmv
  have hgoal : |f (x, v x) - f (x, u x) - fz (x, u x) * (v x - u x)| ≤ ε * ‖v - u‖ := by
    calc |f (x, v x) - f (x, u x) - fz (x, u x) * (v x - u x)|
        = |f (x, v x) - fz (x, u x) * v x - (f (x, u x) - fz (x, u x) * u x)| := by congr 1; ring
      _ ≤ ε * |v x - u x| := hmv2
      _ ≤ ε * ‖v - u‖ := mul_le_mul_of_nonneg_left hy1 hε.le
  simpa [Real.norm_eq_abs] using hgoal

end Nemytskii
