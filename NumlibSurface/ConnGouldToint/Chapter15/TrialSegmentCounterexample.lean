/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import NumlibSurface.ConnGouldToint.Chapter15.Section04

/-! # A trial-segment counterexample for the composite SQP analysis

The constraint map is the zero map into the zero vector space. The normal
step is zero, the null-space basis is the identity, and the tangential model
is linear. Thus the iteration is the basic trust-region update.
-/

namespace ConnGouldToint.Chapter15

open Chapter06 Filter Topology
open scoped RealInnerProductSpace

private noncomputable def segmentObjective (x : ℝ) : ℝ :=
  if x < 0 then -x else 1

private noncomputable def segmentParams : BTRParams where
  η₁ := 1 / 4
  η₂ := 3 / 4
  γ₁ := 1 / 4
  γ₂ := 1 / 4
  eta₁_pos := by norm_num
  eta₁_le_eta₂ := by norm_num
  eta₂_lt_one := by norm_num
  gamma₁_pos := by norm_num
  gamma₁_le_gamma₂ := le_rfl
  gamma₂_lt_one := by norm_num

private noncomputable def segmentScale (j : ℕ) : ℝ :=
  (1 / 2) ^ j

private theorem segmentScale_pos (j : ℕ) : 0 < segmentScale j := by
  unfold segmentScale
  positivity

private theorem segmentScale_le_one (j : ℕ) : segmentScale j ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

private theorem segmentScale_succ (j : ℕ) : segmentScale (j + 1) = segmentScale j / 2 := by
  rw [segmentScale, pow_succ, segmentScale]
  ring

private noncomputable def segmentCenter (k : ℕ) : ℝ :=
  -segmentScale (k / 2)

private noncomputable def segmentRadius (k : ℕ) : ℝ :=
  if k % 2 = 0 then 2 * segmentScale (k / 2) else segmentScale (k / 2) / 2

private theorem segmentCenter_neg (k : ℕ) : segmentCenter k < 0 :=
  neg_neg_of_pos (segmentScale_pos _)

private theorem segmentRadius_pos (k : ℕ) : 0 < segmentRadius k := by
  unfold segmentRadius
  split <;> positivity [segmentScale_pos (k / 2)]

private theorem segment_parity (k : ℕ) : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by
  omega

private theorem segmentCenter_even (j : ℕ) : segmentCenter (2 * j) = -segmentScale j := by
  unfold segmentCenter
  rw [show (2 * j) / 2 = j by omega]

private theorem segmentCenter_odd (j : ℕ) : segmentCenter (2 * j + 1) = -segmentScale j := by
  unfold segmentCenter
  rw [show (2 * j + 1) / 2 = j by omega]

private theorem segmentRadius_even (j : ℕ) : segmentRadius (2 * j) = 2 * segmentScale j := by
  unfold segmentRadius
  rw [ite_eq_left (show (2 * j) % 2 = 0 by omega), show (2 * j) / 2 = j by omega]

private theorem segmentRadius_odd (j : ℕ) :
    segmentRadius (2 * j + 1) = segmentScale j / 2 := by
  unfold segmentRadius
  rw [ite_eq_right (show (2 * j + 1) % 2 ≠ 0 by omega), show (2 * j + 1) / 2 = j by omega]

private theorem segmentRatio_even (j : ℕ) :
    btrRatio segmentObjective (fun z : ℝ => -z) (segmentCenter (2 * j))
      (segmentRadius (2 * j)) ≤ 0 := by
  rw [segmentCenter_even, segmentRadius_even]
  unfold btrRatio Optimization.reductionRatio
  have hj := segmentScale_pos j
  have ht : -segmentScale j + 2 * segmentScale j = segmentScale j := by ring
  rw [ht, segmentObjective, ite_eq_left (neg_neg_of_pos hj),
    segmentObjective, ite_eq_right hj.not_gt, neg_neg]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact sub_nonpos.mpr (segmentScale_le_one j)
  · linarith

private theorem segmentRatio_odd (j : ℕ) :
    btrRatio segmentObjective (fun z : ℝ => -z) (segmentCenter (2 * j + 1))
      (segmentRadius (2 * j + 1)) = 1 := by
  rw [segmentCenter_odd, segmentRadius_odd]
  unfold btrRatio Optimization.reductionRatio
  have hj := segmentScale_pos j
  have ht : -segmentScale j + segmentScale j / 2 < 0 := by linarith
  rw [segmentObjective, ite_eq_left (neg_neg_of_pos hj), segmentObjective, ite_eq_left ht]
  exact div_self (by linarith)

private noncomputable def segmentRun :
    BTRRun segmentObjective segmentParams
      (fun _ m x s => HasSufficientModelDecrease m x s (-1 : ℝ) 1 ‖s‖ (1 / 2)) where
  x := segmentCenter
  s := segmentRadius
  Δ := segmentRadius
  p := fun _ => normSeminorm ℝ ℝ
  norm_separates := fun _ _ h => norm_eq_zero.mp h
  model := fun _ z => -z
  delta_initial_pos := segmentRadius_pos 0
  feasible := by
    intro k
    change ‖segmentCenter k + segmentRadius k - segmentCenter k‖ ≤ segmentRadius k
    rw [add_sub_cancel_left, Real.norm_eq_abs, abs_of_pos (segmentRadius_pos k)]
  sufficient_decrease := by
    intro k
    have hk := segmentRadius_pos k
    simp only [HasSufficientModelDecrease, Set.mem_Ioo, Real.norm_eq_abs, abs_neg, abs_one,
      div_one, mul_one, abs_of_pos hk]
    refine ⟨by norm_num, ?_⟩
    nlinarith only [min_le_right (1 : ℝ) (segmentRadius k), hk]
  predicted_pos := by
    intro k
    have hk := segmentRadius_pos k
    linarith
  iterate_update := by
    intro k
    rcases segment_parity k with he | ho
    · rw [he]
      have h := segmentRatio_even (k / 2)
      have hbad : btrRatio segmentObjective (fun z : ℝ => -z) (segmentCenter (2 * (k / 2)))
          (segmentRadius (2 * (k / 2))) < segmentParams.η₁ :=
        h.trans_lt segmentParams.eta₁_pos
      rw [Optimization.acceptStep_of_lt hbad]
      exact (segmentCenter_odd (k / 2)).trans (segmentCenter_even (k / 2)).symm
    · rw [ho]
      have hgood : segmentParams.η₁ ≤ btrRatio segmentObjective (fun z : ℝ => -z)
          (segmentCenter (2 * (k / 2) + 1)) (segmentRadius (2 * (k / 2) + 1)) := by
        rw [segmentRatio_odd]
        norm_num [segmentParams]
      rw [Optimization.acceptStep_of_le hgood,
        show 2 * (k / 2) + 1 + 1 = 2 * (k / 2 + 1) by omega,
        segmentCenter_even, segmentCenter_odd, segmentRadius_odd, segmentScale_succ]
      ring
  radius_update := by
    intro k
    rcases segment_parity k with he | ho
    · rw [he]
      have hbad := segmentRatio_even (k / 2)
      refine ⟨fun h => ?_, fun h _ => ?_, fun _ => ?_⟩
      · exact ((not_le_of_gt (segmentParams.eta₁_pos.trans_le segmentParams.eta₁_le_eta₂))
          (h.trans hbad)).elim
      · exact ((not_le_of_gt segmentParams.eta₁_pos) (h.trans hbad)).elim
      · rw [segmentRadius_even, segmentRadius_odd]
        norm_num [segmentParams]
        constructor <;> linarith
    · rw [ho, segmentRatio_odd]
      refine ⟨fun _ => ?_, fun _ h => ?_, fun h => ?_⟩
      · rw [show 2 * (k / 2) + 1 + 1 = 2 * (k / 2 + 1) by omega,
          segmentRadius_even, segmentRadius_odd, segmentScale_succ]
        linarith [segmentScale_pos (k / 2)]
      · norm_num [segmentParams] at h
      · norm_num [segmentParams] at h

/-- Lipschitz objective derivatives near all iterates do not control rejected
trial segments. A linear model produces accepted steps approaching the
boundary of the differentiability domain, alternating with rejected steps
that cross the boundary. The gradient norm stays one and the model error
does not have a uniform quadratic bound. -/
theorem sqp_trialSegment_counterexample :
    ∃ (f : ℝ → ℝ) (P : BTRParams) (run : BTRRun f P
      (fun _ m x s => HasSufficientModelDecrease m x s (-1 : ℝ) 1 ‖s‖ (1 / 2))),
      (∀ x, 0 ≤ f x) ∧ (∀ k, run.x k ∈ Set.Iio 0) ∧
      (∀ x ∈ Set.Iio 0, DifferentiableAt ℝ f x) ∧
      LipschitzOnWith 0 (fderiv ℝ f) (Set.Iio 0) ∧
      (∀ z ≠ 0, ‖gradient f z‖ ≤ 1) ∧
      (∀ k, run.Δ k = ‖run.s k‖ ∧ run.model k = (fun z => -z) ∧
        run.model k (run.x k) = f (run.x k) ∧
        fderiv ℝ (run.model k) (run.x k) = fderiv ℝ f (run.x k) ∧
        ‖gradient f (run.x k)‖ = 1) ∧
      ∀ C ≥ 0, ∃ k, C * (run.Δ k) ^ 2 <
        |f (run.x k + run.s k) - run.model k (run.x k + run.s k)| := by
  have hd (x : ℝ) (hx : x < 0) : HasFDerivAt segmentObjective
      (-(ContinuousLinearMap.id ℝ ℝ)) x := by
    refine (ContinuousLinearMap.hasFDerivAt (-(ContinuousLinearMap.id ℝ ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds hx] with z hz
    simp [segmentObjective, hz]
  refine ⟨segmentObjective, segmentParams, segmentRun, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold segmentObjective
    split_ifs <;> linarith
  · exact segmentCenter_neg
  · exact fun x hx => (hd x hx).differentiableAt
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [(hd x hx).fderiv, (hd y hy).fderiv, dist_self]
    simp
  · intro z hz
    rcases lt_or_gt_of_ne hz with hneg | hpos
    · rw [gradient, LinearIsometryEquiv.norm_map, (hd z hneg).fderiv, norm_neg,
        ContinuousLinearMap.norm_id]
    · have hconst : HasFDerivAt segmentObjective (0 : ℝ →L[ℝ] ℝ) z := by
        refine (hasFDerivAt_const (1 : ℝ) z).congr_of_eventuallyEq ?_
        filter_upwards [lt_mem_nhds hpos] with w hw
        simp [segmentObjective, hw.not_gt]
      rw [gradient, LinearIsometryEquiv.norm_map, hconst.fderiv, norm_zero]
      norm_num
  · intro k
    change segmentRadius k = ‖segmentRadius k‖ ∧ (fun z : ℝ => -z) = (fun z => -z) ∧
      -segmentCenter k = segmentObjective (segmentCenter k) ∧
      fderiv ℝ (fun z : ℝ => -z) (segmentCenter k) =
        fderiv ℝ segmentObjective (segmentCenter k) ∧
      ‖gradient segmentObjective (segmentCenter k)‖ = 1
    refine ⟨by rw [Real.norm_eq_abs, abs_of_pos (segmentRadius_pos k)], rfl, ?_, ?_, ?_⟩
    · simp [segmentObjective, segmentCenter_neg k]
    · rw [(hd _ (segmentCenter_neg k)).fderiv]
      exact (ContinuousLinearMap.hasFDerivAt (-(ContinuousLinearMap.id ℝ ℝ))).fderiv
    · rw [gradient, LinearIsometryEquiv.norm_map, (hd _ (segmentCenter_neg k)).fderiv, norm_neg]
      exact ContinuousLinearMap.norm_id
  · intro C hC
    have hlim : Tendsto (fun j => C * (2 * segmentScale j) ^ 2) atTop (nhds 0) := by
      have hbase : Tendsto segmentScale atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using ((hbase.const_mul 2).pow 2).const_mul C
    obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (by norm_num : 0 < (1 : ℝ)))).exists
    refine ⟨2 * j, ?_⟩
    change C * (segmentRadius (2 * j)) ^ 2 <
      |segmentObjective (segmentCenter (2 * j) + segmentRadius (2 * j)) -
        -(segmentCenter (2 * j) + segmentRadius (2 * j))|
    rw [segmentRadius_even, segmentCenter_even,
      show -segmentScale j + 2 * segmentScale j = segmentScale j by ring,
      segmentObjective, ite_eq_right (segmentScale_pos j).not_gt]
    exact hj.trans_le (by
      rw [abs_of_pos (by linarith [segmentScale_pos j])]
      linarith [segmentScale_pos j])

end ConnGouldToint.Chapter15
