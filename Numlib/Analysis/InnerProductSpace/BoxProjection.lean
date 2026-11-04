/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Analysis.InnerProductSpace.ConvexProjection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.Linarith

/-! # Projection onto a Euclidean box -/

open scoped RealInnerProductSpace

/-- A Euclidean box with possibly infinite coordinate bounds. -/
def euclideanBox {ι : Type*} [Fintype ι] (l u : ι → EReal) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, l i ≤ (x i : EReal) ∧ (x i : EReal) ≤ u i}

/-- Clip a real coordinate to an interval with extended real bounds. -/
noncomputable def clipCoordinate (l u : EReal) (x : ℝ) : ℝ :=
  if (x : EReal) < l then l.toReal else if u < (x : EReal) then u.toReal else x

private theorem clip_spec {l u : EReal} {w : ℝ}
    (hl : l ≤ (w : EReal)) (hu : (w : EReal) ≤ u) (x : ℝ) :
    let z := clipCoordinate l u x
    l ≤ (z : EReal) ∧ (z : EReal) ≤ u ∧ (x - z) * (w - z) ≤ 0 := by
  by_cases hx : (x : EReal) < l
  · have hlr : (l.toReal : EReal) = l :=
      EReal.coe_toReal (hl.trans_lt (EReal.coe_lt_top w)).ne
        ((EReal.bot_lt_coe x).trans hx).ne'
    have hx' := EReal.coe_le_coe_iff.mp (hx.le.trans_eq hlr.symm)
    have hw' := EReal.coe_le_coe_iff.mp (hlr.le.trans hl)
    simp only [clipCoordinate, ite_eq_left hx, hlr, le_refl, true_and]
    exact ⟨hl.trans hu, mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx') (sub_nonneg.mpr hw')⟩
  · by_cases hux : u < (x : EReal)
    · have hur : (u.toReal : EReal) = u :=
        EReal.coe_toReal (hux.trans (EReal.coe_lt_top x)).ne
          ((EReal.bot_lt_coe w).trans_le hu).ne'
      have hx' := EReal.coe_le_coe_iff.mp (hur.le.trans hux.le)
      have hw' := EReal.coe_le_coe_iff.mp (hu.trans_eq hur.symm)
      simp only [clipCoordinate, ite_eq_right hx, ite_eq_left hux, hur, le_refl, true_and]
      exact ⟨hl.trans hu, mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx') (sub_nonpos.mpr hw')⟩
    · simp [clipCoordinate, hx, hux, le_of_not_gt hx, le_of_not_gt hux]

private theorem convex_euclideanBox {ι : Type*} [Fintype ι] (l u : ι → EReal) :
    Convex ℝ (euclideanBox l u) := by
  intro x hx y hy a b ha hb hab i
  have hlo : min (x i) (y i) ≤ a * x i + b * y i := by
    have h₁ := mul_le_mul_of_nonneg_left (min_le_left (x i) (y i)) ha
    have h₂ := mul_le_mul_of_nonneg_left (min_le_right (x i) (y i)) hb
    linarith only [h₁, h₂, congrArg (fun v : ℝ ↦ v * min (x i) (y i)) hab]
  have hhi : a * x i + b * y i ≤ max (x i) (y i) := by
    have h₁ := mul_le_mul_of_nonneg_left (le_max_left (x i) (y i)) ha
    have h₂ := mul_le_mul_of_nonneg_left (le_max_right (x i) (y i)) hb
    linarith only [h₁, h₂, congrArg (fun v : ℝ ↦ v * max (x i) (y i)) hab]
  change l i ≤ ((a * x i + b * y i : ℝ) : EReal) ∧
    ((a * x i + b * y i : ℝ) : EReal) ≤ u i
  refine ⟨?_, ?_⟩
  · exact (show l i ≤ (min (x i) (y i) : ℝ) by
      rcases le_total (x i) (y i) with h | h
      · simpa [min_eq_left h] using (hx i).1
      · simpa [min_eq_right h] using (hy i).1).trans (EReal.coe_le_coe hlo)
  · exact (EReal.coe_le_coe hhi).trans (show (max (x i) (y i) : ℝ) ≤ u i by
      rcases le_total (x i) (y i) with h | h
      · simpa [max_eq_right h] using (hy i).2
      · simpa [max_eq_left h] using (hx i).2)

/-- The Euclidean projection onto a nonempty box is coordinatewise clipping. -/
theorem bestApprox_euclideanBox_apply {ι : Type*} [Fintype ι] {l u : ι → EReal}
    (hne : (euclideanBox l u).Nonempty) (x : EuclideanSpace ℝ ι) (i : ι) :
    bestApprox (euclideanBox l u) x i = clipCoordinate (l i) (u i) (x i) := by
  obtain ⟨w₀, hw₀⟩ := hne
  let z : EuclideanSpace ℝ ι := WithLp.toLp 2 fun j ↦ clipCoordinate (l j) (u j) (x j)
  have hz : z ∈ euclideanBox l u := by
    intro j
    exact ⟨(clip_spec (hw₀ j).1 (hw₀ j).2 (x j)).1,
      (clip_spec (hw₀ j).1 (hw₀ j).2 (x j)).2.1⟩
  have hconv := convex_euclideanBox l u
  have h : IsBestApprox (euclideanBox l u) x z := by
    apply (isBestApprox_iff_inner_le_zero hconv hz).2
    intro w hw
    rw [PiLp.inner_apply]
    exact Finset.sum_nonpos fun j _ ↦ by
      simpa [RCLike.inner_apply, mul_comm] using (clip_spec (hw j).1 (hw j).2 (x j)).2.2
  rw [h.bestApprox_eq hconv]
