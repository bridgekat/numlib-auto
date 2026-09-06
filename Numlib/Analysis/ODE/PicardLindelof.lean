import Mathlib.Analysis.ODE.ExistUnique

/-!
# Picard–Lindelöf with the solution confined to the ball

Mathlib's `IsPicardLindelof f t₀ x₀ a r L K` bundles the hypotheses of the Picard–Lindelöf theorem:
the vector field is `K`-Lipschitz in the state and bounded by `L` on the closed ball of radius `a`
about `x₀`, continuous in time there, and the time interval is short enough that `L` times its
length fits inside `a - r`. Its existence theorem
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` produces an integral curve, but says
nothing about where that curve goes, while `ODE_solution_unique_of_mem_Icc` compares only solutions
that are known to stay inside a set on which the field is Lipschitz. The two therefore do not
compose into the textbook statement "the initial value problem has a *unique* solution on the short
interval".

This file closes that gap. `IsPicardLindelof.exists_mem_closedBall_hasDerivWithinAt` gives an
integral curve that stays in the closed ball of radius `a`, and
`IsPicardLindelof.exists_unique_mem_closedBall_hasDerivWithinAt` adds that it is the only such
curve.

The proof is the observation that every hypothesis of `IsPicardLindelof` constrains the field only
on the ball, so the field may be replaced by one that is *constant outside* it — here `f t u` is
replaced by `f t x₀` for `u` outside the ball. The replacement satisfies the same hypotheses, and it
is bounded by `L` at *every* state, so the mean value inequality bounds the displacement of any of
its integral curves by `L` times the elapsed time with no circularity. Note that the replacement
need not be continuous, let alone Lipschitz: a radial retraction, whose Lipschitz constant in a
general normed space is not in Mathlib, is not needed.
-/

open Metric Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- **Picard–Lindelöf**, differential form, with the solution confined to the ball on which the
hypotheses are stated: under `IsPicardLindelof f t₀ x₀ a r L K` and `‖x - x₀‖ ≤ r` there is an
integral curve `α` of `f` on `Icc tmin tmax` with `α t₀ = x` **and** `α t ∈ closedBall x₀ a`
throughout.

Mathlib's `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` gives everything but the
containment. To add it, replace `f` outside the ball by the constant field `f t x₀`: the hypotheses
of `IsPicardLindelof` only ever speak about the ball, so they survive the replacement, while the
bound `‖f t u‖ ≤ L` now holds at every state, and the mean value inequality then bounds
`‖α t - α t₀‖` by `L |t - t₀| ≤ a - r`. On the ball the two fields agree, so `α` solves the original
equation. -/
theorem IsPicardLindelof.exists_mem_closedBall_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧ (∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ a) ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := by
  classical
  obtain ⟨p, hpmem, hpeq⟩ : ∃ p : E → E, (∀ u, p u ∈ closedBall x₀ (a : ℝ)) ∧
      ∀ u ∈ closedBall x₀ (a : ℝ), p u = u := by
    refine ⟨fun u => if u ∈ closedBall x₀ (a : ℝ) then u else x₀, fun u => ?_, fun u hu => ?_⟩
    · dsimp only
      split_ifs with h
      · exact h
      · exact mem_closedBall_self a.2
    · dsimp only
      split_ifs
      rfl
  have hg : IsPicardLindelof (fun t u => f t (p u)) t₀ x₀ a r L K := by
    refine ⟨fun t ht u hu v hv => ?_, fun u hu => ?_, fun t ht u hu => ?_, hf.mul_max_le⟩
    · simp only [hpeq u hu, hpeq v hv]
      exact hf.lipschitzOnWith t ht hu hv
    · simp only [hpeq u hu]
      exact hf.continuousOn u hu
    · exact hf.norm_le t ht _ (hpmem u)
  obtain ⟨α, hα₀, hα⟩ := hg.exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  have hbound : ∀ t ∈ Icc tmin tmax, ‖f t (p (α t))‖ ≤ (L : ℝ) := fun t ht =>
    hf.norm_le t ht _ (hpmem _)
  have hmem : ∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ (a : ℝ) := by
    intro t ht
    have hle : ‖α t - α t₀‖ ≤ (L : ℝ) * ‖t - (t₀ : ℝ)‖ :=
      (convex_Icc tmin tmax).norm_image_sub_le_of_norm_hasDerivWithin_le hα hbound t₀.2 ht
    have habs : ‖t - (t₀ : ℝ)‖ ≤ max (tmax - t₀) ((t₀ : ℝ) - tmin) := by
      rw [Real.norm_eq_abs, abs_sub_le_iff]
      exact ⟨le_trans (by linarith [ht.2]) (le_max_left _ _),
        le_trans (by linarith [ht.1]) (le_max_right _ _)⟩
    have hxr : ‖α t₀ - x₀‖ ≤ (r : ℝ) := by
      rw [hα₀]
      exact mem_closedBall_iff_norm.mp hx
    rw [mem_closedBall, dist_eq_norm]
    calc ‖α t - x₀‖ ≤ ‖α t - α t₀‖ + ‖α t₀ - x₀‖ := norm_sub_le_norm_sub_add_norm_sub ..
      _ ≤ (L : ℝ) * max (tmax - t₀) ((t₀ : ℝ) - tmin) + r :=
        add_le_add (hle.trans (mul_le_mul_of_nonneg_left habs L.coe_nonneg)) hxr
      _ ≤ ((a : ℝ) - r) + r := by linarith [hf.mul_max_le]
      _ = a := sub_add_cancel _ _
  refine ⟨α, hα₀, hmem, fun t ht => ?_⟩
  simpa only [hpeq _ (hmem t ht)] using hα t ht

/-- **Picard–Lindelöf**, differential form, existence *and* uniqueness: under
`IsPicardLindelof f t₀ x₀ a r L K`, `‖x - x₀‖ ≤ r` and `tmin < t₀ < tmax`, the initial value
problem `α' t = f t (α t)`, `α t₀ = x` has exactly one solution on `Icc tmin tmax` among the curves
that stay in `closedBall x₀ a`.

Uniqueness is `ODE_solution_unique_of_mem_Icc` applied with that ball as the ambient set, which is
legitimate precisely because `IsPicardLindelof.exists_mem_closedBall_hasDerivWithinAt` puts the
solution it builds there. Restricting the comparison to ball-valued curves is not a weakening: `f`
is only assumed Lipschitz on the ball, and outside it the equation is unconstrained. -/
theorem IsPicardLindelof.exists_unique_mem_closedBall_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r)
    (ht₀ : (t₀ : ℝ) ∈ Ioo tmin tmax) :
    ∃ α : ℝ → E, α t₀ = x ∧ (∀ t ∈ Icc tmin tmax, α t ∈ closedBall x₀ a) ∧
      (∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t) ∧
      ∀ β : ℝ → E, β t₀ = x → (∀ t ∈ Icc tmin tmax, β t ∈ closedBall x₀ a) →
        (∀ t ∈ Icc tmin tmax, HasDerivWithinAt β (f t (β t)) (Icc tmin tmax) t) →
        EqOn α β (Icc tmin tmax) := by
  obtain ⟨α, hα₀, hαmem, hα⟩ := hf.exists_mem_closedBall_hasDerivWithinAt hx
  refine ⟨α, hα₀, hαmem, hα, fun β hβ₀ hβmem hβ => ?_⟩
  exact ODE_solution_unique_of_mem_Icc (K := K) (s := fun _ => closedBall x₀ a)
    (fun t ht => hf.lipschitzOnWith t (Ioo_subset_Icc_self ht)) ht₀
    (fun t ht => (hα t ht).continuousWithinAt)
    (fun t ht => (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => hαmem t (Ioo_subset_Icc_self ht))
    (fun t ht => (hβ t ht).continuousWithinAt)
    (fun t ht => (hβ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun t ht => hβmem t (Ioo_subset_Icc_self ht)) (hα₀.trans hβ₀.symm)
