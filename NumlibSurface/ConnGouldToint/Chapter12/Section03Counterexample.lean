/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumlibSurface.ConnGouldToint.Chapter12.Section03

/-! # Failure of Cauchy active-set identification at nonvanishing radii -/

open Filter Optimization
open scoped Topology RealInnerProductSpace

namespace ConnGouldToint.Chapter12

open Chapter06

private noncomputable def intervalObjective (x : ℝ) : ℝ := (x - 1 / 2) ^ 2 / 2

private noncomputable def intervalCenter (k : ℕ) : ℝ := 1 / 2 + (1 / 2 : ℝ) ^ (k / 2) / 8

private noncomputable def intervalRadius (k : ℕ) : ℝ := if k % 2 = 0 then 2 else 1

private noncomputable def intervalTrial (k : ℕ) : ℝ :=
  if k % 2 = 0 then 0 else intervalCenter k - (intervalCenter k - 1 / 2) / 2

private noncomputable def intervalModel (k : ℕ) (y : ℝ) : ℝ :=
  if k % 2 = 0 then intervalObjective (intervalCenter k) +
    (intervalCenter k - 1 / 2) * (y - intervalCenter k) else intervalObjective y

private noncomputable def intervalConstraint (i : Fin 2) (x : ℝ) : ℝ :=
  if i = 0 then x else 1 - x

private noncomputable def intervalCauchyParams : GeneralizedCauchyParams where
  upperSlope := 1 / 4
  lowerSlope := 7 / 8
  radiusFraction := 1 / 8
  endpointFactor := 1 / 4
  upper_pos := by norm_num
  slope_order := by norm_num
  lower_lt_one := by norm_num
  fraction_pos := by norm_num
  fraction_lt_one := by norm_num
  endpoint_pos := by norm_num
  endpoint_lt_half := by norm_num

private theorem intervalObjective_hasDerivAt (x : ℝ) :
    HasDerivAt intervalObjective (x - 1 / 2) x := by
  unfold intervalObjective
  convert (((hasDerivAt_id x).sub_const (1 / 2)).pow 2).div_const 2 using 1
  · rfl
  · norm_num [id]

private theorem intervalObjective_gradient (x : ℝ) : gradient intervalObjective x = x - 1 / 2 := by
  exact (intervalObjective_hasDerivAt x).hasGradientAt.gradient

private theorem intervalCenter_bounds (k : ℕ) : 1 / 2 < intervalCenter k ∧ intervalCenter k ≤ 5 / 8 := by
  have hp : 0 < (1 / 2 : ℝ) ^ (k / 2) := by positivity
  have hle : (1 / 2 : ℝ) ^ (k / 2) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold intervalCenter
  constructor <;> linarith

private theorem intervalTrial_mem (k : ℕ) : intervalTrial k ∈ Set.Icc (0 : ℝ) 1 := by
  have h := intervalCenter_bounds k
  unfold intervalTrial
  split
  · norm_num
  · constructor <;> linarith [h.1, h.2]

private theorem intervalCenter_mem (k : ℕ) : intervalCenter k ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith [(intervalCenter_bounds k).1], by linarith [(intervalCenter_bounds k).2]⟩

private theorem intervalTrial_cauchy (k : ℕ) :
    IsApproxGeneralizedCauchyPoint intervalCauchyParams (Set.Icc (0 : ℝ) 1)
      intervalObjective (intervalModel k) (intervalCenter k) (intervalRadius k) (intervalTrial k) := by
  let x := intervalCenter k
  let d := x - 1 / 2
  have hx₁ : 1 / 2 < x := (intervalCenter_bounds k).1
  have hx₂ : x ≤ 5 / 8 := (intervalCenter_bounds k).2
  have hd : 0 < d := sub_pos.mpr hx₁
  have hprojection (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
      bestApprox (Set.Icc (0 : ℝ) 1) v = v :=
    (bestApprox_eq_iff ⟨0, by norm_num⟩ isClosed_Icc (convex_Icc _ _)).mpr
      ⟨hv, by simp⟩
  have hpath (t v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) (he : x - t * d = v) :
      projectedGradientPath (Set.Icc (0 : ℝ) 1) intervalObjective x t = v := by
    unfold projectedGradientPath projectedRay
    rw [intervalObjective_gradient, smul_eq_mul]
    change bestApprox _ (x + t * (-d)) = v
    rw [show x + t * (-d) = v by linarith]
    exact hprojection v hv
  unfold IsApproxGeneralizedCauchyPoint
  by_cases hk : k % 2 = 0
  · simp only [intervalTrial, intervalRadius, intervalModel, hk, ite_true]
    refine ⟨x / d, div_pos (by linarith) hd, ?_, ?_, ?_, Or.inl ?_⟩
    · symm
      apply hpath _ _ (by norm_num)
      field_simp
      ring
    · change ‖(0 : ℝ) - x‖ ≤ 2
      simp only [zero_sub, norm_neg, Real.norm_eq_abs, abs_of_pos (show 0 < x by linarith)]
      linarith
    · simp only [intervalCauchyParams, intervalObjective_gradient, Real.inner_apply,
        sub_self, mul_zero, add_zero]
      change intervalObjective x + d * (0 - x) ≤ intervalObjective x + 1 / 4 * (d * (0 - x))
      nlinarith only [mul_nonneg hd.le (show 0 ≤ x by linarith)]
    · change (1 / 8 : ℝ) * 2 ≤ ‖(0 : ℝ) - x‖
      simp only [zero_sub, norm_neg, Real.norm_eq_abs,
        abs_of_pos (show 0 < x by linarith)]
      linarith
  · simp only [intervalTrial, intervalRadius, intervalModel, hk, ite_false]
    refine ⟨1 / 2, by norm_num, ?_, ?_, ?_, Or.inr (Or.inl ?_)⟩
    · symm
      apply hpath _ _ (by constructor <;> linarith [show d = x - 1 / 2 from rfl])
      ring
    · change ‖x - d / 2 - x‖ ≤ 1
      rw [show x - d / 2 - x = -(d / 2) by ring, norm_neg, Real.norm_eq_abs,
        abs_of_pos (half_pos hd)]
      dsimp [d]
      linarith
    · simp only [intervalCauchyParams, intervalObjective_gradient, Real.inner_apply]
      change intervalObjective (x - d / 2) ≤ intervalObjective x + 1 / 4 * (d * (x - d / 2 - x))
      unfold intervalObjective
      rw [show x - d / 2 - 1 / 2 = d - d / 2 by dsimp [d]; ring]
      rw [show x - 1 / 2 = d by rfl]
      nlinarith only [sq_nonneg d]
    · simp only [intervalCauchyParams, intervalObjective_gradient, Real.inner_apply]
      change intervalObjective x + 7 / 8 * (d * (x - d / 2 - x)) ≤ intervalObjective (x - d / 2)
      unfold intervalObjective
      rw [show x - d / 2 - 1 / 2 = d - d / 2 by dsimp [d]; ring]
      rw [show x - 1 / 2 = d by rfl]
      nlinarith only [sq_nonneg d]

private theorem intervalModel_center (k : ℕ) :
    intervalModel k (intervalCenter k) = intervalObjective (intervalCenter k) := by
  by_cases hk : k % 2 = 0 <;> simp [intervalModel, hk]

private theorem intervalPrediction_pos (k : ℕ) :
    0 < intervalModel k (intervalCenter k) - intervalModel k (intervalTrial k) := by
  have hx := (intervalCenter_bounds k).1
  have hd := sub_pos.mpr hx
  by_cases hk : k % 2 = 0
  · simp only [intervalModel, intervalTrial, hk, ite_true, sub_self, mul_zero, add_zero]
    nlinarith only [mul_pos hd (show 0 < intervalCenter k by linarith)]
  · simp only [intervalModel, intervalTrial, hk, ite_false, intervalObjective]
    nlinarith only [sq_pos_of_pos hd]

private theorem intervalStep_eq (k : ℕ) :
    intervalCenter k + (intervalTrial k - intervalCenter k) = intervalTrial k := by ring

private theorem intervalRatio_even (k : ℕ) (hk : k % 2 = 0) :
    btrRatio intervalObjective (intervalModel k) (intervalCenter k)
      (intervalTrial k - intervalCenter k) < defaultBTRParams.η₁ := by
  have hx := intervalCenter_bounds k
  have hlt : intervalObjective (intervalCenter k) < intervalObjective 0 := by
    unfold intervalObjective
    have hb : 0 < (1 / 2 : ℝ) - (intervalCenter k - 1 / 2) := by linarith [hx.2]
    have hc : 0 < (1 / 2 : ℝ) + (intervalCenter k - 1 / 2) := by linarith [hx.1]
    nlinarith only [mul_pos hb hc]
  have hpred := intervalPrediction_pos k
  unfold btrRatio reductionRatio
  rw [intervalStep_eq, show intervalTrial k = 0 by simp [intervalTrial, hk]]
  exact (div_neg_of_neg_of_pos (sub_neg.mpr hlt)
    (by simpa [intervalTrial, hk] using hpred)).trans defaultBTRParams.eta₁_pos

private theorem intervalRatio_odd (k : ℕ) (hk : k % 2 ≠ 0) :
    btrRatio intervalObjective (intervalModel k) (intervalCenter k)
      (intervalTrial k - intervalCenter k) = 1 := by
  have hp := intervalPrediction_pos k
  unfold btrRatio reductionRatio
  rw [intervalStep_eq]
  simpa only [intervalModel, hk, ite_false] using div_self (by
    simpa only [intervalModel, hk, ite_false] using hp.ne')

private theorem intervalCenter_succ_even (k : ℕ) (hk : k % 2 = 0) :
    intervalCenter (k + 1) = intervalCenter k := by
  unfold intervalCenter
  rw [show (k + 1) / 2 = k / 2 by omega]

private theorem intervalCenter_succ_odd (k : ℕ) (hk : k % 2 ≠ 0) :
    intervalCenter (k + 1) = intervalTrial k := by
  simp only [intervalTrial, hk, ite_false, intervalCenter]
  rw [show (k + 1) / 2 = k / 2 + 1 by omega, pow_succ]
  ring

private theorem intervalStep_bound (k : ℕ) : ‖intervalTrial k - intervalCenter k‖ ≤ intervalRadius k := by
  obtain ⟨_, _, _, h, _⟩ := intervalTrial_cauchy k
  exact h

private noncomputable def intervalRun :
    BTRRun intervalObjective defaultBTRParams (fun _ _ _ _ ↦ True) where
  x := intervalCenter
  s k := intervalTrial k - intervalCenter k
  Δ := intervalRadius
  p _ := normSeminorm ℝ ℝ
  norm_separates _ v h := norm_eq_zero.mp (show ‖v‖ = 0 from h)
  delta_initial_pos := by norm_num [intervalRadius]
  feasible k := by
    simpa [trustRegion, add_sub_add_left_eq_sub] using intervalStep_bound k
  model := intervalModel
  sufficient_decrease _ := trivial
  predicted_pos k := by simpa only [intervalStep_eq] using intervalPrediction_pos k
  iterate_update k := by
    by_cases hk : k % 2 = 0
    · rw [intervalCenter_succ_even k hk, acceptStep_of_lt (intervalRatio_even k hk)]
    · have h := (show defaultBTRParams.η₁ ≤ 1 by norm_num [defaultBTRParams])
      rw [← intervalRatio_odd k hk] at h
      rw [acceptStep_of_le h, intervalStep_eq, intervalCenter_succ_odd k hk]
  radius_update k := by
    by_cases hk : k % 2 = 0
    · have hk' : (k + 1) % 2 ≠ 0 := by omega
      have h := intervalRatio_even k hk
      refine ⟨?_, ?_, ?_⟩
      · intro hr
        exact (not_lt_of_ge (defaultBTRParams.eta₁_le_eta₂.trans hr) h).elim
      · intro hr _
        exact (not_lt_of_ge hr h).elim
      · intro _
        norm_num [intervalRadius, hk, hk', defaultBTRParams]
    · have hk' : (k + 1) % 2 = 0 := by omega
      rw [intervalRatio_odd k hk]
      refine ⟨?_, ?_, ?_⟩
      · intro _
        norm_num [intervalRadius, hk, hk']
      · intro _ h
        norm_num [defaultBTRParams] at h
      · intro h
        norm_num [defaultBTRParams] at h

private theorem intervalCenter_tendsto : Tendsto intervalCenter atTop (𝓝 (1 / 2 : ℝ)) := by
  have ht : Tendsto (fun k : ℕ ↦ k / 2) atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro n
    exact ⟨2 * n, fun k hk ↦ by omega⟩
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (by norm_num)).comp ht
  change Tendsto (fun k : ℕ ↦ 1 / 2 + (1 / 2 : ℝ) ^ (k / 2) / 8) atTop (𝓝 (1 / 2 : ℝ))
  simpa only [zero_div, add_zero, Function.comp_apply] using
    (hp.div_const (8 : ℝ)).const_add (1 / 2 : ℝ)

private theorem intervalModel_Taylor (k : ℕ) (y : ℝ) :
    intervalModel k y - (intervalModel k (intervalCenter k) +
      ⟪gradient intervalObjective (intervalCenter k), y - intervalCenter k⟫) ≤
        ‖y - intervalCenter k‖ ^ 2 / 2 := by
  rw [intervalModel_center, intervalObjective_gradient, Real.inner_apply, Real.norm_eq_abs, sq_abs]
  by_cases hk : k % 2 = 0
  · simp only [intervalModel, hk, ite_true, sub_self]
    positivity
  · simp only [intervalModel, hk, ite_false, intervalObjective]
    ring_nf
    rfl


/-- The printed Theorem 12.3.8 can fail at the generalized Cauchy points.
A scalar interval run alternates rejected affine-model trials at the
boundary and successful exact-model trials converging to the interior
minimizer. The selected step is the Cauchy step, so AA.5 holds with equality. -/
theorem theorem_12_3_8_nonvanishing_radius_counterexample :
    ∃ (f : ℝ → ℝ) (c : Fin 2 → ℝ → ℝ) (Q : GeneralizedCauchyParams) (κ : ℝ)
      (run : BTRRun f defaultBTRParams (fun _ _ _ _ ↦ True)),
      ContDiff ℝ 2 f ∧ BddBelow (Set.range f) ∧ (∀ y, deriv (deriv f) y = 1) ∧
      (∀ i, ContDiff ℝ 2 (c i)) ∧ Chapter03.AC7 (Set.Icc (0 : ℝ) 1) c ∧
      Tendsto run.x atTop (𝓝 (1 / 2 : ℝ)) ∧
      LinearIndependent ℝ (fun i : activeConstraintSet c (1 / 2) ↦ gradient (c i) (1 / 2)) ∧
      HasStrictActiveMultipliers c (fun i ↦ gradient (c i)) (gradient f) (1 / 2) ∧
      κ ∈ Set.Ioo 0 1 ∧
      (∀ k, run.x k ∈ Set.Icc (0 : ℝ) 1 ∧ run.x k + run.s k ∈ Set.Icc (0 : ℝ) 1 ∧
        1 ≤ run.Δ k ∧ ContDiff ℝ 2 (run.model k) ∧ run.model k (run.x k) = f (run.x k) ∧
        deriv (run.model k) (run.x k) = deriv f (run.x k) ∧
        (∀ y, |deriv (deriv (run.model k)) y| ≤ 1) ∧
        IsApproxGeneralizedCauchyPoint Q (Set.Icc (0 : ℝ) 1) f (run.model k)
          (run.x k) (run.Δ k) (run.x k + run.s k) ∧
        κ * cappedCriticality (Set.Icc (0 : ℝ) 1) f (run.x k) *
          min (cappedCriticality (Set.Icc (0 : ℝ) 1) f (run.x k)) (run.Δ k) ≤
            run.model k (run.x k) - run.model k (run.x k + run.s k)) ∧
      ∃ᶠ k in atTop, activeConstraintSet c (run.x k + run.s k) ≠
        activeConstraintSet c (1 / 2) := by
  let C := Set.Icc (0 : ℝ) 1
  let Q := intervalCauchyParams
  let κ := min (Q.upperSlope * Q.radiusFraction / 2) (2 * Q.upperSlope * (1 - Q.lowerSlope))
  have hκ : κ ∈ Set.Ioo (0 : ℝ) 1 := by norm_num [κ, Q, intervalCauchyParams]
  have hf : ContDiff ℝ 2 intervalObjective := by unfold intervalObjective; fun_prop
  have hder : deriv intervalObjective = fun y ↦ y - 1 / 2 :=
    funext fun y ↦ (intervalObjective_hasDerivAt y).deriv
  have hH (y : ℝ) : deriv (deriv intervalObjective) y = 1 := by
    rw [hder]
    exact ((hasDerivAt_id y).sub_const _).deriv
  have hc (i : Fin 2) : ContDiff ℝ 2 (intervalConstraint i) := by
    by_cases hi : i = 0
    · have h : intervalConstraint i = id := by funext y; simp [intervalConstraint, hi]
      rw [h]
      fun_prop
    · have h : intervalConstraint i = fun y ↦ 1 - y := by funext y; simp [intervalConstraint, hi]
      rw [h]
      fun_prop
  have hset : Chapter03.AC7 C intervalConstraint := by
    ext y
    change (0 ≤ y ∧ y ≤ 1) ↔ ∀ i : Fin 2, 0 ≤ intervalConstraint i y
    constructor
    · rintro ⟨h₁, h₂⟩ i
      fin_cases i
      · simpa [intervalConstraint] using h₁
      · simpa [intervalConstraint] using sub_nonneg.mpr h₂
    · intro h
      exact ⟨by simpa [intervalConstraint] using h 0,
        sub_nonneg.mp (by simpa [intervalConstraint] using h 1)⟩
  have hempty : activeConstraintSet intervalConstraint (1 / 2) = ∅ := by
    ext i
    fin_cases i <;> norm_num [activeConstraintSet, intervalConstraint]
  have hLI : LinearIndependent ℝ
      (fun i : activeConstraintSet intervalConstraint (1 / 2) ↦ gradient (intervalConstraint i) (1 / 2)) := by
    let : IsEmpty (activeConstraintSet intervalConstraint (1 / 2)) := by
      rw [hempty]
      infer_instance
    exact linearIndependent_empty_type
  have hstrict : HasStrictActiveMultipliers intervalConstraint
      (fun i ↦ gradient (intervalConstraint i)) (gradient intervalObjective) (1 / 2) := by
    refine ⟨fun _ ↦ 0, ?_, ?_, fun _ _ ↦ rfl⟩
    · simp [intervalObjective_gradient]
    · intro i hi
      rw [hempty] at hi
      exact (Set.notMem_empty i hi).elim
  refine ⟨intervalObjective, intervalConstraint, Q, κ, intervalRun,
    hf, ⟨0, fun z ⟨y, hy⟩ ↦ by rw [← hy]; unfold intervalObjective; positivity⟩,
    hH, hc, hset, intervalCenter_tendsto, hLI, hstrict, hκ, ?_, ?_⟩
  · intro k
    simp only [intervalRun, intervalStep_eq]
    have hm : ContDiff ℝ 2 (intervalModel k) := by
      by_cases hk : k % 2 = 0
      · have he : intervalModel k = fun y ↦ intervalObjective (intervalCenter k) +
            (intervalCenter k - 1 / 2) * (y - intervalCenter k) := by
          funext y
          simp [intervalModel, hk]
        rw [he]
        fun_prop
      · have he : intervalModel k = intervalObjective := by funext y; simp [intervalModel, hk]
        exact he.symm ▸ hf
    have hderModel : deriv (intervalModel k) = if k % 2 = 0 then
        (fun _ ↦ intervalCenter k - 1 / 2) else deriv intervalObjective := by
      by_cases hk : k % 2 = 0
      · have he : intervalModel k = fun y ↦ intervalObjective (intervalCenter k) +
            (intervalCenter k - 1 / 2) * (y - intervalCenter k) := by
          funext y
          simp [intervalModel, hk]
        rw [he, ite_eq_left hk]
        funext v
        simpa only [id_eq, mul_one] using ((((hasDerivAt_id v).sub_const
          (intervalCenter k)).const_mul (intervalCenter k - 1 / 2)).const_add
          (intervalObjective (intervalCenter k))).deriv
      · have he : intervalModel k = intervalObjective := by funext y; simp [intervalModel, hk]
        rw [he, ite_eq_right hk]
    have hmg : deriv (intervalModel k) (intervalCenter k) = deriv intervalObjective (intervalCenter k) := by
      rw [hderModel]
      split
      · exact (congrFun hder (intervalCenter k)).symm
      · rfl
    have hmH (y : ℝ) : |deriv (deriv (intervalModel k)) y| ≤ 1 := by
      rw [hderModel]
      split
      · rw [deriv_const]
        norm_num
      · rw [hH, abs_one]
    have hR : 1 ≤ intervalRadius k := by unfold intervalRadius; split <;> norm_num
    refine ⟨intervalCenter_mem k, intervalTrial_mem k, hR, hm, intervalModel_center k,
      hmg, hmH, intervalTrial_cauchy k, ?_⟩
    have h := theorem_12_2_2_of_taylor_bound Q isClosed_Icc (convex_Icc _ _)
      (intervalCenter_mem k) (lt_of_lt_of_le zero_lt_one hR) zero_lt_one
      (intervalTrial_cauchy k) (by simpa only [one_mul] using intervalModel_Taylor k (intervalTrial k))
    simpa only [div_one] using cappedCriticality_decrease (intervalCenter_mem k) hκ.1.le
      (le_refl (1 : ℝ)) (zero_le_one.trans hR) h.2.1
  · apply frequently_atTop.mpr
    intro N
    refine ⟨2 * N, by omega, ?_⟩
    change activeConstraintSet intervalConstraint (intervalCenter (2 * N) +
      (intervalTrial (2 * N) - intervalCenter (2 * N))) ≠ activeConstraintSet intervalConstraint (1 / 2)
    rw [intervalStep_eq, hempty, show intervalTrial (2 * N) = 0 by simp [intervalTrial]]
    intro h
    have hzero : (0 : Fin 2) ∈ activeConstraintSet intervalConstraint 0 := by
      simp [activeConstraintSet, intervalConstraint]
    exact (Set.notMem_empty _) (h ▸ hzero)

end ConnGouldToint.Chapter12
