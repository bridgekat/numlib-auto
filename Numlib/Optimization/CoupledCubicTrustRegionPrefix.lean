import Numlib.Optimization.ConstrainedTrustRegionConcatenation
import Numlib.Optimization.HigherOrderTrustRegion
import Numlib.Optimization.CoupledCubic
import Numlib.Optimization.CoupledCubicTrustRegionRates

/-!
# An actual coupled cubic trust-region history

Fixed controls and initial data precede the heterogeneous tolerance family. The finite
history contains an accepted curvature-setting step, a genuine rejection, dyadic accepted
first-order halvings, a separate first-coordinate reset, and a final second-order trial.
Every selected ratio uses the actual selected-order Taylor decrement. Compact full-ball
maximizers supply every unused order and endpoint witness, and all trials lift to the fixed
box-constrained algorithm. The final trial and its endpoint fail true feasible quality.
-/

noncomputable section
open scoped Nat
namespace Optimization.CoupledCubicTrustRegionPrefix
open HigherOrderTrustRegion TaylorCriticality RegularizedTaylorModel Metric Set

/-- Fixed trust-region controls, independent of the requested tolerances. -/
def fixedParameters : Parameters where
  eta1 := 1 / 4
  eta2 := 7 / 8
  gamma1 := 1 / 2
  gamma2 := 1 / 2
  gamma3 := 1
  fraction := 1 / 4
  theta := 1
  radiusMax := 2
  eta1_pos := by norm_num
  eta_le := by norm_num
  eta2_lt_one := by norm_num
  gamma1_pos := by norm_num
  gamma_le := le_rfl
  gamma2_lt_one := by norm_num
  one_le_gamma3 := le_rfl
  fraction_pos := by norm_num
  fraction_le_one := by norm_num
  theta_pos := by norm_num
  theta_le_one := le_rfl

section Maximizers
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- An actual compact full-ball maximizer, also supplying unused inspected orders. -/
def maximizingWitness (f : E → ℝ) (x : E) (δ : ℝ) (j : ℕ) : E :=
  Classical.choose (exists_eq_gapOn (isCompact_closedBall 0 (max δ 0))
    ⟨0, by simp⟩
    (continuous_taylorDecrement f j x).continuousOn)

/-- The chosen maximizing witness belongs to the full testing ball. -/
theorem maximizingWitness_norm (f : E → ℝ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) :
    ‖maximizingWitness f x δ j‖ ≤ δ := by
  have h := (Classical.choose_spec (exists_eq_gapOn
    (isCompact_closedBall (0 : E) (max δ 0))
    ⟨0, by simp⟩
    (continuous_taylorDecrement f j x).continuousOn)).1
  simpa [maximizingWitness, max_eq_left hδ] using h

/-- The chosen witness attains the true full-ball Taylor gap. -/
theorem maximizingWitness_decrement (f : E → ℝ) (x : E) {δ : ℝ}
    (hδ : 0 ≤ δ) (j : ℕ) :
    taylorDecrement f j x (maximizingWitness f x δ j) =
      gapOn (taylorDecrement f j x) (closedBall 0 δ) := by
  have h := (Classical.choose_spec (exists_eq_gapOn
    (isCompact_closedBall (0 : E) (max δ 0))
    ⟨0, by simp⟩
    (continuous_taylorDecrement f j x).continuousOn)).2
  simpa [maximizingWitness, max_eq_left hδ] using h

/-- Exact maximizing directions satisfy the fixed quarter-gap requirement. -/
theorem maximizingWitness_fraction (f : E → ℝ) (x : E) {δ : ℝ}
    (hδ : 0 ≤ δ) (j : ℕ) :
    fixedParameters.fraction * gapOn (taylorDecrement f j x) (closedBall 0 δ) ≤
      taylorDecrement f j x (maximizingWitness f x δ j) := by
  rw [maximizingWitness_decrement f x hδ]
  have hg := gapOn_nonneg (isCompact_closedBall (0 : E) δ)
    (continuous_taylorDecrement f j x).continuousOn
    (show (0 : E) ∈ closedBall 0 δ by simpa using hδ)
    (by simp [taylorDecrement])
  change 1 / 4 * _ ≤ _
  linarith
end Maximizers

open CoupledCubic

/-- The exact full first-order gap on the zero second-coordinate plane. -/
theorem first_gap {x z δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) :
    gapOn (taylorDecrement objective 1 (point x 0 z)) (closedBall 0 δ) = x * δ := by
  apply le_antisymm
  · apply gapOn_le ⟨0, by simpa using hδ⟩
    intro d hd
    have hd' : ‖d‖ ≤ δ := by simpa using hd
    have hc := (abs_le.mp ((abs_coordinate_le_norm d 0).trans hd')).1
    simp only [CoupledCubic.taylorDecrement_one, point_zero_coord, point_one_coord,
      point_two_coord, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_div,
      add_zero]
    nlinarith
  · have hm : point (-δ) 0 0 ∈ closedBall 0 δ := by simp [abs_of_nonneg hδ]
    have h := le_gapOn (isCompact_closedBall (0 : Space) δ)
      (continuous_taylorDecrement objective 1 (point x 0 z)).continuousOn hm
    simpa [CoupledCubic.fderiv_objective] using h

/-- At the reset point the full quadratic gap is attained in the second direction. -/
theorem second_gap {z δ : ℝ} (hz : 0 ≤ z) (hδ : 0 ≤ δ) :
    gapOn (taylorDecrement objective 2 (point 0 0 z)) (closedBall 0 δ) =
      z * δ ^ 2 / 2 := by
  apply le_antisymm
  · apply gapOn_le ⟨0, by simpa using hδ⟩
    intro d hd
    have hd' : ‖d‖ ≤ δ := by simpa using hd
    have hc : |d 1| ≤ δ := (abs_coordinate_le_norm d 1).trans hd'
    have hs : (d 1) ^ 2 ≤ δ ^ 2 := by
      simpa using (sq_le_sq₀ (abs_nonneg (d 1)) hδ).2 hc
    simp only [CoupledCubic.taylorDecrement_two, point_zero_coord, point_one_coord,
      point_two_coord, mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_div,
      add_zero]
    nlinarith [mul_nonneg hz (sub_nonneg.2 hs), sq_nonneg (d 0)]
  · have hm : point 0 δ 0 ∈ closedBall 0 δ := by simp [abs_of_nonneg hδ]
    have h := le_gapOn (isCompact_closedBall (0 : Space) δ)
      (continuous_taylorDecrement objective 2 (point 0 0 z)).continuousOn hm
    simpa [CoupledCubic.taylorDecrement_two] using h

/-- A full testing ball stays in the box whenever every center coordinate has the margin. -/
theorem testBall_feasible {x : Space} {δ : ℝ}
    (hx : ∀ i, |x i| + δ ≤ 2) {d : Space} (hd : ‖d‖ ≤ δ) : x + d ∈ box := by
  intro i
  calc
    |(x + d) i| = |x i + d i| := rfl
    _ ≤ |x i| + |d i| := abs_add_le _ _
    _ ≤ |x i| + δ := add_le_add_right ((abs_coordinate_le_norm d i).trans hd) _
    _ ≤ 2 := hx i

/-- The quarter linear witness attains exactly the required fraction of the true gap. -/
theorem first_witness_fraction {x z δ : ℝ} (hx : 0 ≤ x) (hδ : 0 ≤ δ) :
    fixedParameters.fraction * gapOn (taylorDecrement objective 1 (point x 0 z))
      (closedBall 0 δ) = taylorDecrement objective 1 (point x 0 z) (point (-δ / 4) 0 0) := by
  rw [first_gap hx hδ]
  simp [fixedParameters, CoupledCubic.fderiv_objective]
  ring

open CoupledCubicTrustRegionRates

/-- The actual final second-order trial, with honest endpoint and unused-order witnesses. -/
def finalTrace (N : ℕ) : Trace Space where
  point k := if k = 0 then point 0 0 (curvature N)
    else point 0 (scale N / 2) (curvature N)
  step _ := point 0 (scale N / 2) 0
  radius _ := scale N / 2
  witness k j := if k = 0 then if j = 1 then 0 else point 0 (scale N / 2) 0
    else maximizingWitness objective (point 0 (scale N / 2) (curvature N)) (scale N / 2) j
  order _ := 2

/-- The selected-order ratio of the final trial is exactly one. -/
theorem finalTrace_ratio (N : ℕ) : ratio objective (finalTrace N) 0 = 1 := by
  have hs := scale_pos N
  have hb := curvature_pos N
  simp [ratio, finalTrace, CoupledCubic.taylorDecrement_two, ne_of_gt hb, ne_of_gt hs]

/-- Its objective decrease is the small heterogeneous payment. -/
theorem finalTrace_decrease (N : ℕ) :
    objective ((finalTrace N).point 0) - objective ((finalTrace N).point 1) =
      curvature N * scale N ^ 2 / 8 := by
  simp [finalTrace]
  ring

/-- The full final trial, including all endpoint witnesses, satisfies every actual law. -/
theorem finalTrace_legal {N : ℕ} (hN : 1 ≤ N) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (finalTrace N) 1 := by
  have hs := scale_pos N
  have hb := curvature_pos N
  have hs' := scale_le_quarter hN
  have hr : 0 < scale N / 2 := by positivity
  have ht (k : ℕ) : testRadius fixedParameters (finalTrace N) k = scale N / 2 := by
    simp only [testRadius, finalTrace, fixedParameters]
    exact min_eq_left (by linarith)
  have hdec : taylorDecrement objective 2 (point 0 0 (curvature N))
      (point 0 (scale N / 2) 0) = curvature N * scale N ^ 2 / 8 := by
    rw [CoupledCubic.taylorDecrement_two]
    simp only [point_zero_coord, point_one_coord, point_two_coord]
    ring
  have hfail : fixedParameters.fraction * tolerance N 2 *
      (scale N / 2) ^ 2 / (2 ! : ℝ) < curvature N * scale N ^ 2 / 8 := by
    simp only [fixedParameters, tolerance_two]
    norm_num
    nlinarith [mul_pos hb (sq_pos_of_pos hs)]
  have hwf : ∀ k ≤ 1, ∀ j, 1 ≤ j → j ≤ 2 →
      fixedParameters.fraction * gapOn (taylorDecrement objective j ((finalTrace N).point k))
        (closedBall 0 (testRadius fixedParameters (finalTrace N) k)) ≤
      taylorDecrement objective j ((finalTrace N).point k) ((finalTrace N).witness k j) := by
    intro k hk j hj hj'
    rw [ht]
    by_cases hk0 : k = 0
    · subst k
      interval_cases j
      · simp only [finalTrace, ite_true]
        rw [first_gap (le_refl 0) hr.le]
        simp
      · simp only [finalTrace, ite_true, ite_eq_right (by decide : ¬(2 : ℕ) = 1)]
        rw [second_gap hb.le hr.le, hdec]
        change 1 / 4 * (curvature N * (scale N / 2) ^ 2 / 2) ≤ _
        nlinarith [mul_nonneg hb.le (sq_nonneg (scale N))]
    · simpa only [finalTrace, ite_eq_right hk0] using
        maximizingWitness_fraction objective (point 0 (scale N / 2) (curvature N)) hr.le j
  have hfailure : fixedParameters.fraction * tolerance N ((finalTrace N).order 0) *
      testRadius fixedParameters (finalTrace N) 0 ^ (finalTrace N).order 0 /
        (((finalTrace N).order 0)! : ℝ) <
      taylorDecrement objective ((finalTrace N).order 0) ((finalTrace N).point 0)
        ((finalTrace N).witness 0 ((finalTrace N).order 0)) := by
    rw [ht]
    simpa only [finalTrace, ite_true, ite_eq_right (by decide : ¬(2 : ℕ) = 1), hdec]
      using hfail
  refine ⟨hr, by change scale N / 2 ≤ 2; linarith, ?_, hwf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk j hj hj'
    rw [ht]
    by_cases hk0 : k = 0
    · subst k
      interval_cases j
      · simp [finalTrace, hr.le]
      · simp [finalTrace, abs_of_nonneg hr.le]
    · simpa only [finalTrace, ite_eq_right hk0] using
        maximizingWitness_norm objective (point 0 (scale N / 2) (curvature N)) hr.le j
  · intro k hk hstop
    have hk0 : k = 0 := by omega
    subst k
    exact (not_lt_of_ge (hstop 2 (by omega) (by omega))) hfailure
  · intro k hk; norm_num [finalTrace]
  · intro k hk; exact le_rfl
  · intro k hk j hj hj'
    have hk0 : k = 0 := by omega
    subst k
    have hj1 : j = 1 := by change j < 2 at hj'; omega
    subst j
    rw [ht]
    simp only [finalTrace, ite_true, tolerance_one, pow_one, Nat.factorial_one,
      Nat.cast_one, div_one, taylorDecrement_zero]
    change 0 ≤ 1 / 4 * (scale N / 2) * (scale N / 2)
    positivity
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact hfailure
  · intro k hk
    simp [finalTrace, abs_of_nonneg hr.le]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact le_rfl
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rw [finalTrace_ratio]
    norm_num [fixedParameters, finalTrace]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rw [finalTrace_ratio]
    norm_num [fixedParameters, finalTrace]
    linarith


/-- The actual first-order ratio for a trial on the zero second-coordinate plane. -/
def linearRatio (x dx : ℝ) : ℝ := (x ^ 2 / 2 - (x + dx) ^ 2 / 2) / (-x * dx)

/-- A single actual first-order trial, retaining the center when its ratio rejects it. -/
def linearTrace (x z dx dz r r' : ℝ) : Trace Space where
  point k := if k = 0 then point x 0 z else
    if fixedParameters.eta1 ≤ linearRatio x dx then point (x + dx) 0 (z + dz)
    else point x 0 z
  step _ := point dx 0 dz
  radius k := if k = 0 then r else r'
  witness k j := if k = 0 ∧ j = 1 then point (-min r 1 / 4) 0 0 else
    maximizingWitness objective
      (if k = 0 then point x 0 z else
        if fixedParameters.eta1 ≤ linearRatio x dx then point (x + dx) 0 (z + dz)
        else point x 0 z) (min (if k = 0 then r else r') 1) j
  order _ := 1

/-- The recorded scalar ratio uses precisely the actual selected-order denominator. -/
theorem linearTrace_ratio (x z dx dz r r' : ℝ) :
    ratio objective (linearTrace x z dx dz r r') 0 = linearRatio x dx := by
  simp [ratio, linearTrace, linearRatio, CoupledCubic.fderiv_objective]

set_option maxHeartbeats 1200000 in
-- The generic constructor checks all orders at both endpoints in a single structure proof.
/-- Operational input checks suffice for one actual first-order trial; all unused orders
and endpoint witnesses are supplied by compact full-ball maximization. -/
theorem linearTrace_legal {N : ℕ} {x z dx dz r r' : ℝ}
    (hx : tolerance N 1 < x) (hr : 0 < r) (hr' : 0 < r') (hcap : r ≤ 2)
    (hnorm : ‖point dx 0 dz‖ ≤ r)
    (hpred : -x * (-min r 1 / 4) ≤ -x * dx)
    (hupdate : if fixedParameters.eta2 ≤ linearRatio x dx
      then r' ∈ Icc r (min fixedParameters.radiusMax (fixedParameters.gamma3 * r))
      else if fixedParameters.eta1 ≤ linearRatio x dx
      then r' ∈ Icc (fixedParameters.gamma2 * r) r
      else r' ∈ Icc (fixedParameters.gamma1 * r) (fixedParameters.gamma2 * r)) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (linearTrace x z dx dz r r') 1 := by
  let t := linearTrace x z dx dz r r'
  have hx0 : 0 < x := (tolerance_pos N 1).trans hx
  have hδ : 0 < min r 1 := lt_min hr (by norm_num)
  have htest (k : ℕ) : testRadius fixedParameters t k = min (if k = 0 then r else r') 1 := rfl
  have htest0 : testRadius fixedParameters t 0 = min r 1 := rfl
  have htestpos (k : ℕ) : 0 < testRadius fixedParameters t k := by
    rw [htest]; split_ifs <;> exact lt_min (by assumption) (by norm_num)
  have hwf : ∀ k ≤ 1, ∀ j, 1 ≤ j → j ≤ 2 →
      fixedParameters.fraction * gapOn (taylorDecrement objective j (t.point k))
        (closedBall 0 (testRadius fixedParameters t k)) ≤
      taylorDecrement objective j (t.point k) (t.witness k j) := by
    intro k hk j hj hj'
    by_cases hkj : k = 0 ∧ j = 1
    · rcases hkj with ⟨rfl, rfl⟩
      exact (first_witness_fraction hx0.le hδ.le).le
    · change _ ≤ taylorDecrement objective j (t.point k)
        (if k = 0 ∧ j = 1 then _ else maximizingWitness objective (t.point k)
          (testRadius fixedParameters t k) j)
      rw [ite_eq_right hkj]
      exact maximizingWitness_fraction objective _ (htestpos k).le j
  have hfailure : fixedParameters.fraction * tolerance N 1 * min r 1 <
      taylorDecrement objective 1 (point x 0 z) (point (-min r 1 / 4) 0 0) := by
    rw [CoupledCubic.taylorDecrement_one]
    simp only [point_zero_coord, point_one_coord, point_two_coord]
    change 1 / 4 * tolerance N 1 * min r 1 < _
    nlinarith [mul_pos (sub_pos.2 hx) hδ]
  refine ⟨hr, hcap, ?_, hwf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk j hj hj'
    by_cases hkj : k = 0 ∧ j = 1
    · rcases hkj with ⟨rfl, rfl⟩
      change ‖point (-min r 1 / 4) 0 0‖ ≤ min r 1
      rw [norm_point_x, abs_of_nonpos (by linarith)]
      linarith
    · change ‖if k = 0 ∧ j = 1 then _ else maximizingWitness objective (t.point k)
          (testRadius fixedParameters t k) j‖ ≤ _
      rw [ite_eq_right hkj]
      exact maximizingWitness_norm objective _ (htestpos k).le j
  · intro k hk hstop
    have hk0 : k = 0 := by omega
    subst k
    have h := hstop 1 (by omega) (by omega)
    change taylorDecrement objective 1 (point x 0 z) (point (-min r 1 / 4) 0 0) ≤
      fixedParameters.fraction * tolerance N 1 * min r 1 ^ 1 / (1 ! : ℝ) at h
    norm_num only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
    exact (not_lt_of_ge h) hfailure
  · intro k hk; exact le_rfl
  · intro k hk; norm_num [t, linearTrace]
  · intro k hk j hj hj'; change j < 1 at hj'; omega
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    change fixedParameters.fraction * tolerance N 1 * min r 1 ^ 1 / (1 ! : ℝ) < _
    simpa [t, linearTrace, CoupledCubic.fderiv_objective] using hfailure
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact hnorm
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa [t, linearTrace, CoupledCubic.fderiv_objective] using hpred
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rw [show ratio objective t 0 = linearRatio x dx from linearTrace_ratio _ _ _ _ _ _]
    simp [linearTrace]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    rw [show ratio objective t 0 = linearRatio x dx from linearTrace_ratio _ _ _ _ _ _]
    exact hupdate


/-- Halving a positive first coordinate has ratio three quarters with the linear model. -/
theorem linearRatio_half {x : ℝ} (hx : 0 < x) : linearRatio x (-x / 2) = 3 / 4 := by
  unfold linearRatio
  field_simp [ne_of_gt hx]
  ring

/-- Resetting a positive first coordinate to zero has first-order ratio one half. -/
theorem linearRatio_reset {x : ℝ} (hx : 0 < x) : linearRatio x (-x) = 1 / 2 := by
  unfold linearRatio
  field_simp [ne_of_gt hx]
  ring

/-- The first accepted trial sets the curvature coordinate without changing the controls. -/
def initialTrace (N : ℕ) : Trace Space :=
  linearTrace 1 1 (-1 / 2) (curvature N - 1) 2 1

/-- A genuine rejected trial reuses its retained point and halves its radius. -/
def rejectedTrace (N : ℕ) : Trace Space :=
  linearTrace (1 / 2) (curvature N) (-1) 0 1 (1 / 2)

/-- One accepted dyadic first-coordinate halving. -/
def halfTrace (N m : ℕ) : Trace Space :=
  linearTrace (scale m) (curvature N) (-scale m / 2) 0 (scale m) (scale m / 2)

/-- The separate first-coordinate reset required before the second-order trial. -/
def resetTrace (N : ℕ) : Trace Space :=
  linearTrace (scale N) (curvature N) (-scale N) 0 (scale N) (scale N / 2)

/-- Every law of the first trial holds at the fixed initial point and radius. -/
theorem initialTrace_legal {N : ℕ} (hN : 1 ≤ N) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (initialTrace N) 1 := by
  have hb := curvature_pos N
  have hb' := curvature_le_half hN
  have ha := scale_le_quarter hN
  apply linearTrace_legal
  · rw [tolerance_one]; linarith
  · norm_num
  · norm_num
  · norm_num
  · apply (norm_point_le_iff _ _ _ (by norm_num : (0 : ℝ) ≤ 2)).2
    nlinarith
  · norm_num
  · norm_num [fixedParameters, linearRatio]

/-- The second trial is a legal rejection with ratio zero. -/
theorem rejectedTrace_legal {N : ℕ} (hN : 1 ≤ N) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (rejectedTrace N) 1 := by
  have ha := scale_le_quarter hN
  apply linearTrace_legal
  · rw [tolerance_one]; linarith
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [fixedParameters, linearRatio]

/-- Every halving before the final dyadic scale is an actual legal first-order trial. -/
theorem halfTrace_legal {N m : ℕ} (hm : m ≤ N) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (halfTrace N m) 1 := by
  have hx := scale_pos m
  have hx' := scale_le_half m
  have ha := scale_pos N
  have ham := scale_antitone hm
  have hmin : min (scale m) 1 = scale m := min_eq_left (by linarith)
  apply linearTrace_legal
  · rw [tolerance_one]; linarith
  · exact hx
  · positivity
  · linarith
  · simp only [norm_point_x, abs_of_nonpos (by linarith : -scale m / 2 ≤ 0)]
    linarith
  · rw [hmin]
    nlinarith [sq_nonneg (scale m)]
  · rw [linearRatio_half hx]
    norm_num [fixedParameters]
    constructor <;> linarith

/-- The separate reset is a legal ordinary successful contraction with ratio one half. -/
theorem resetTrace_legal (N : ℕ) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (resetTrace N) 1 := by
  have hx := scale_pos N
  have hx' := scale_le_half N
  have hmin : min (scale N) 1 = scale N := min_eq_left (by linarith)
  apply linearTrace_legal
  · rw [tolerance_one]; linarith
  · exact hx
  · positivity
  · linarith
  · simp [abs_of_nonneg hx.le]
  · rw [hmin]
    nlinarith [sq_nonneg (scale N)]
  · rw [linearRatio_reset hx]
    norm_num [fixedParameters]
    constructor <;> linarith


open ConstrainedTrustRegion

/-- The actual retained point after a dyadic halving. -/
theorem halfTrace_endpoint (N m : ℕ) :
    (halfTrace N m).point 1 = point (scale (m + 1)) 0 (curvature N) := by
  have hr := linearRatio_half (scale_pos m)
  norm_num [halfTrace, linearTrace, hr, fixedParameters, scale_succ]
  congr 1
  ring

/-- A finite sequence of actual first-order halvings with endpoint testing witnesses. -/
def halvesTrace (N k : ℕ) : Trace Space :=
  Nat.rec (halfTrace N 0) (fun m t => appendTrace t (halfTrace N m) m) k

/-- The dyadic halving sequence starts at the same retained point for every length. -/
theorem halvesTrace_initial (N k : ℕ) :
    (halvesTrace N k).point 0 = point (1 / 2) 0 (curvature N) ∧
    (halvesTrace N k).radius 0 = 1 / 2 := by
  induction k with
  | zero => simp [halvesTrace, halfTrace, linearTrace]
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      simp [halvesTrace, appendTrace, halfTrace, linearTrace]
    · simpa only [halvesTrace, appendTrace_point_before _ _ (by omega : 0 < k),
        appendTrace_radius_before _ _ (by omega : 0 < k)] using ih

/-- The final retained point and radius are the dyadic scale indexed by the sequence length. -/
theorem halvesTrace_endpoint (N k : ℕ) :
    (halvesTrace N k).point k = point (scale k) 0 (curvature N) ∧
    (halvesTrace N k).radius k = scale k := by
  cases k with
  | zero => simp [halvesTrace, halfTrace, linearTrace]
  | succ k =>
    rw [halvesTrace, appendTrace_point_after, appendTrace_radius_after]
    constructor
    · exact halfTrace_endpoint N k
    · simp [halfTrace, linearTrace, scale_succ]

/-- All dyadic halvings through the requested endpoint form an actual legal finite prefix. -/
theorem halvesTrace_legal {N k : ℕ} (hk : k ≤ N) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (halvesTrace N k) k := by
  induction k with
  | zero =>
    rw [halvesTrace]
    exact (halfTrace_legal (N := N) (m := 0) (by omega)).restrict (by omega : 0 ≤ 1)
  | succ k ih =>
    have h := ih (by omega)
    rw [halvesTrace]
    apply h.append (halfTrace_legal (N := N) (m := k) (by omega))
    · simpa only [halfTrace, linearTrace, ite_true] using
        (halvesTrace_endpoint N k).1.symm
    · simpa only [halfTrace, linearTrace, ite_true] using
        (halvesTrace_endpoint N k).2.symm

/-- The fixed initial accepted step and the following rejected trial. -/
def headTrace (N : ℕ) : Trace Space := appendTrace (initialTrace N) (rejectedTrace N) 1

/-- The fixed head obeys all actual trust-region rules. -/
theorem headTrace_legal {N : ℕ} (hN : 1 ≤ N) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (headTrace N) 2 := by
  apply (initialTrace_legal hN).append (rejectedTrace_legal hN)
  · norm_num [initialTrace, rejectedTrace, linearTrace, fixedParameters, linearRatio]
  · simp [initialTrace, rejectedTrace, linearTrace]

/-- The initial point and radius are fixed before the tolerance vector. -/
theorem headTrace_initial (N : ℕ) :
    (headTrace N).point 0 = point 1 0 1 ∧ (headTrace N).radius 0 = 2 := by
  simp [headTrace, appendTrace, initialTrace, linearTrace]

/-- Rejection leaves the half-coordinate point with half-unit radius. -/
theorem headTrace_endpoint (N : ℕ) :
    (headTrace N).point 2 = point (1 / 2) 0 (curvature N) ∧
    (headTrace N).radius 2 = 1 / 2 := by
  norm_num [headTrace, appendTrace, rejectedTrace, linearTrace, linearRatio, fixedParameters]

/-- The fixed head followed by every dyadic first-order halving. -/
def preResetTrace (N : ℕ) : Trace Space := appendTrace (headTrace N) (halvesTrace N N) 2

/-- The pre-reset history has exactly the declared dyadic endpoint. -/
theorem preResetTrace_endpoint (N : ℕ) :
    (preResetTrace N).point (N + 2) = point (scale N) 0 (curvature N) ∧
    (preResetTrace N).radius (N + 2) = scale N := by
  have h := halvesTrace_endpoint N N
  simpa only [preResetTrace, Nat.add_comm N 2, appendTrace_point_after,
    appendTrace_radius_after] using h

/-- All earlier dyadic trials satisfy the complete finite-prefix interface. -/
theorem preResetTrace_legal {N : ℕ} (hN : 1 ≤ N) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (preResetTrace N) (N + 2) := by
  have h := (headTrace_legal hN).append (halvesTrace_legal (N := N) (k := N) le_rfl)
    ((halvesTrace_initial N N).1.trans (headTrace_endpoint N).1.symm)
    ((halvesTrace_initial N N).2.trans (headTrace_endpoint N).2.symm)
  simpa only [preResetTrace, Nat.add_comm 2 N] using h

/-- The prehistory including the separate accepted reset to zero first coordinate. -/
def resetHistory (N : ℕ) : Trace Space := appendTrace (preResetTrace N) (resetTrace N) (N + 2)

/-- The reset reaches exactly the center required by the final second-order trial. -/
theorem resetHistory_endpoint (N : ℕ) :
    (resetHistory N).point (N + 3) = point 0 0 (curvature N) ∧
    (resetHistory N).radius (N + 3) = scale N / 2 := by
  have hr := linearRatio_reset (scale_pos N)
  have he : N + 3 = (N + 2) + 1 := by omega
  norm_num [resetHistory, he, resetTrace, linearTrace, hr, fixedParameters]

/-- The reset and every preceding trial form a complete legal finite prefix. -/
theorem resetHistory_legal {N : ℕ} (hN : 1 ≤ N) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (resetHistory N) (N + 3) := by
  apply (preResetTrace_legal hN).append (resetTrace_legal N)
  · simpa only [resetTrace, linearTrace, ite_true] using
      (preResetTrace_endpoint N).1.symm
  · simpa only [resetTrace, linearTrace, ite_true] using
      (preResetTrace_endpoint N).2.symm

/-- The full actual finite history through the small accepted second-order payment. -/
def fullTrace (N : ℕ) : Trace Space := appendTrace (resetHistory N) (finalTrace N) (N + 3)

/-- The full history satisfies every actual full-ball trust-region law, including unused
orders and endpoint witnesses. Its first selected second-order trial follows the reset. -/
theorem fullTrace_legal {N : ℕ} (hN : 1 ≤ N) :
    LegalPrefix fixedParameters 2 (tolerance N) objective (fullTrace N) (N + 4) := by
  apply (resetHistory_legal hN).append (finalTrace_legal hN)
  · simpa only [finalTrace, ite_true] using (resetHistory_endpoint N).1.symm
  · simpa only [finalTrace] using (resetHistory_endpoint N).2.symm


/-- Coordinate margins characterize containment of the whole testing ball in the box. -/
theorem point_margin (x y z δ : ℝ) :
    (∀ i : Fin 3, |point x y z i| + δ ≤ 2) ↔
      |x| + δ ≤ 2 ∧ |y| + δ ≤ 2 ∧ |z| + δ ≤ 2 := by
  simp [Fin.forall_fin_succ]

/-- A complete first-order trial lifts to the actual box-constrained interface when both
retained testing balls and the computed trial endpoint have their coordinate margins. -/
theorem linearTrace_box {N : ℕ} {x z dx dz r r' : ℝ}
    (h : HigherOrderTrustRegion.LegalPrefix fixedParameters 2 (tolerance N) objective
      (linearTrace x z dx dz r r') 1)
    (hc : ∀ i : Fin 3, |point x 0 z i| + min r 1 ≤ 2)
    (he : ∀ i : Fin 3, |(linearTrace x z dx dz r r').point 1 i| + min r' 1 ≤ 2)
    (hs : point (x + dx) 0 (z + dz) ∈ box) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (linearTrace x z dx dz r r') 1 := by
  apply of_unconstrained h
  · intro i
    have hd := h.testRadius_bounds (k := 0) (by omega)
    change 0 < min r 1 ∧ _ at hd
    change |point x 0 z i| ≤ 2
    linarith [hc i]
  · intro k hk d hd
    interval_cases k
    · apply testBall_feasible hc
      exact hd
    · apply testBall_feasible he
      exact hd
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa [linearTrace] using hs

/-- The initial testing balls and trial endpoint lie in the fixed feasible box. -/
theorem initialTrace_box {N : ℕ} (hN : 1 ≤ N) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (initialTrace N) 1 := by
  have hb := curvature_pos N
  have hb' := curvature_le_half hN
  apply linearTrace_box (initialTrace_legal hN)
  · norm_num [point_margin]
  · norm_num [initialTrace, linearTrace, linearRatio, fixedParameters, point_margin,
      abs_of_nonneg hb.le]
    linarith
  · rw [point_mem_box]
    norm_num [abs_of_nonneg hb.le]
    linarith

/-- The rejected trial endpoint is feasible, although it is not retained. -/
theorem rejectedTrace_box {N : ℕ} (hN : 1 ≤ N) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (rejectedTrace N) 1 := by
  have hb := curvature_pos N
  have hb' := curvature_le_half hN
  apply linearTrace_box (rejectedTrace_legal hN)
  · norm_num [point_margin, abs_of_nonneg hb.le]
    linarith
  · norm_num [rejectedTrace, linearTrace, linearRatio, fixedParameters, point_margin,
      abs_of_nonneg hb.le]
    linarith
  · rw [point_mem_box]
    norm_num [abs_of_nonneg hb.le]
    linarith

/-- Every halving uses complete feasible testing balls and a feasible actual trial. -/
theorem halfTrace_box {N m : ℕ} (hN : 1 ≤ N) (hm : m ≤ N) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (halfTrace N m) 1 := by
  have hx := scale_pos m
  have hx' := scale_le_half m
  have hb := curvature_pos N
  have hb' := curvature_le_half hN
  have hmin : min (scale m) 1 = scale m := min_eq_left (by linarith)
  have hmin' : min (scale m / 2) 1 = scale m / 2 := min_eq_left (by linarith)
  apply linearTrace_box (halfTrace_legal hm)
  · rw [hmin, point_margin]
    simp only [abs_zero, zero_add, abs_of_nonneg hx.le, abs_of_nonneg hb.le]
    exact ⟨by linarith, by linarith, by linarith⟩
  · change ∀ i : Fin 3, |(halfTrace N m).point 1 i| + min (scale m / 2) 1 ≤ 2
    rw [halfTrace_endpoint, hmin', point_margin, scale_succ]
    simp only [abs_zero, zero_add, abs_of_nonneg (by positivity : 0 ≤ scale m / 2),
      abs_of_nonneg hb.le]
    exact ⟨by linarith, by linarith, by linarith⟩
  · have he : scale m + -scale m / 2 = scale m / 2 := by ring
    rw [he]
    simp only [add_zero, point_mem_box, abs_zero,
      abs_of_nonneg (by positivity : 0 ≤ scale m / 2), abs_of_nonneg hb.le]
    exact ⟨by linarith, by norm_num, by linarith⟩

/-- The accepted reset is feasible and retains a whole feasible testing ball. -/
theorem resetTrace_box {N : ℕ} (hN : 1 ≤ N) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (resetTrace N) 1 := by
  have hx := scale_pos N
  have hx' := scale_le_half N
  have hb := curvature_pos N
  have hb' := curvature_le_half hN
  have hmin : min (scale N) 1 = scale N := min_eq_left (by linarith)
  have hmin' : min (scale N / 2) 1 = scale N / 2 := min_eq_left (by linarith)
  have hratio := linearRatio_reset hx
  apply linearTrace_box (resetTrace_legal N)
  · rw [hmin, point_margin]
    simp only [abs_zero, zero_add, abs_of_nonneg hx.le, abs_of_nonneg hb.le]
    exact ⟨by linarith, by linarith, by linarith⟩
  · norm_num [resetTrace, linearTrace, hratio, fixedParameters, hmin', point_margin,
      abs_of_nonneg hb.le]
    exact ⟨by linarith, by linarith⟩
  · simp only [add_neg_cancel, add_zero, point_mem_box, abs_zero, abs_of_nonneg hb.le]
    exact ⟨by norm_num, by norm_num, by linarith⟩

/-- Both endpoint testing balls and the final second-order trial lie in the fixed box. -/
theorem finalTrace_box {N : ℕ} (hN : 1 ≤ N) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (finalTrace N) 1 := by
  have hs := scale_pos N
  have hs' := scale_le_quarter hN
  have hb := curvature_pos N
  have hb' := curvature_le_half hN
  have hm0 : ∀ i : Fin 3, |point 0 0 (curvature N) i| + scale N / 2 ≤ 2 := by
    rw [point_margin]
    simp only [abs_zero, zero_add, abs_of_nonneg hb.le]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hm1 : ∀ i : Fin 3, |point 0 (scale N / 2) (curvature N) i| + scale N / 2 ≤ 2 := by
    rw [point_margin]
    simp only [abs_zero, zero_add, abs_of_nonneg hb.le,
      abs_of_nonneg (by positivity : 0 ≤ scale N / 2)]
    exact ⟨by linarith, by linarith, by linarith⟩
  have ht (k : ℕ) : testRadius fixedParameters (finalTrace N) k = scale N / 2 := by
    simp only [testRadius, finalTrace, fixedParameters]
    exact min_eq_left (by linarith)
  apply of_unconstrained (finalTrace_legal hN)
  · change point 0 0 (curvature N) ∈ box
    rw [point_mem_box]
    norm_num [abs_of_nonneg hb.le]
    linarith
  · intro k hk d hd
    rw [ht] at hd
    interval_cases k
    · exact testBall_feasible hm0 hd
    · exact testBall_feasible hm1 hd
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    change point 0 0 (curvature N) + point 0 (scale N / 2) 0 ∈ box
    rw [point_add, point_mem_box]
    norm_num [abs_of_nonneg hb.le,
      abs_of_nonneg (by positivity : 0 ≤ scale N / 2)]
    exact ⟨by linarith, by linarith⟩


/-- The complete dyadic phase is legal for the actual fixed box. -/
theorem halvesTrace_box {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ N) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (halvesTrace N k) k := by
  induction k with
  | zero =>
    rw [halvesTrace]
    exact (halfTrace_box hN (m := 0) (by omega)).restrict (by omega : 0 ≤ 1)
  | succ k ih =>
    rw [halvesTrace]
    apply (ih (by omega)).append (halfTrace_box hN (m := k) (by omega))
    · simpa only [halfTrace, linearTrace, ite_true] using
        (halvesTrace_endpoint N k).1.symm
    · simpa only [halfTrace, linearTrace, ite_true] using
        (halvesTrace_endpoint N k).2.symm

/-- The complete initial accepted/rejected pair is legal for the actual fixed box. -/
theorem headTrace_box {N : ℕ} (hN : 1 ≤ N) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (headTrace N) 2 := by
  apply (initialTrace_box hN).append (rejectedTrace_box hN)
  · norm_num [initialTrace, rejectedTrace, linearTrace, fixedParameters, linearRatio]
  · simp [initialTrace, rejectedTrace, linearTrace]

/-- The pre-reset history uses the actual constrained witness fractions. -/
theorem preResetTrace_box {N : ℕ} (hN : 1 ≤ N) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (preResetTrace N) (N + 2) := by
  have h := (headTrace_box hN).append (halvesTrace_box hN (k := N) le_rfl)
    ((halvesTrace_initial N N).1.trans (headTrace_endpoint N).1.symm)
    ((halvesTrace_initial N N).2.trans (headTrace_endpoint N).2.symm)
  simpa only [preResetTrace, Nat.add_comm 2 N] using h

/-- The full constrained prehistory includes the separate accepted reset. -/
theorem resetHistory_box {N : ℕ} (hN : 1 ≤ N) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (resetHistory N) (N + 3) := by
  apply (preResetTrace_box hN).append (resetTrace_box hN)
  · simpa only [resetTrace, linearTrace, ite_true] using
      (preResetTrace_endpoint N).1.symm
  · simpa only [resetTrace, linearTrace, ite_true] using
      (preResetTrace_endpoint N).2.symm

/-- The full actual finite history is legal with the fixed box constraints as well. -/
theorem fullTrace_box {N : ℕ} (hN : 1 ≤ N) :
    ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective
      (fullTrace N) (N + 4) := by
  apply (resetHistory_box hN).append (finalTrace_box hN)
  · simpa only [finalTrace, ite_true] using (resetHistory_endpoint N).1.symm
  · simpa only [finalTrace] using (resetHistory_endpoint N).2.symm

/-- The complete history begins at one fixed point and radius. -/
theorem fullTrace_initial (N : ℕ) :
    (fullTrace N).point 0 = point 1 0 1 ∧ (fullTrace N).radius 0 = 2 := by
  simp only [fullTrace, appendTrace_point_before _ _ (by omega : 0 < N + 3),
    appendTrace_radius_before _ _ (by omega : 0 < N + 3),
    resetHistory, appendTrace_point_before _ _ (by omega : 0 < N + 2),
    appendTrace_radius_before _ _ (by omega : 0 < N + 2),
    preResetTrace, appendTrace_point_before _ _ (by omega : 0 < 2),
    appendTrace_radius_before _ _ (by omega : 0 < 2)]
  exact headTrace_initial N

/-- The final retained center and radius are the starting data for a constrained continuation. -/
theorem fullTrace_endpoint (N : ℕ) :
    (fullTrace N).point (N + 4) = point 0 (scale N / 2) (curvature N) ∧
    (fullTrace N).radius (N + 4) = scale N / 2 := by
  have he : N + 4 = (N + 3) + 1 := by omega
  simp [fullTrace, he, finalTrace]

/-- The small final payment is accepted with selected-order ratio exactly one. -/
theorem fullTrace_final_ratio (N : ℕ) : ratio objective (fullTrace N) (N + 3) = 1 := by
  have h := ratio_appendTrace_after (resetHistory N) (finalTrace N) (N + 3) 0 objective
  simpa only [fullTrace, Nat.add_zero, finalTrace_ratio] using h

/-- The actual accepted decrease at the last executed trial equals the small scalar payment. -/
theorem fullTrace_final_decrease (N : ℕ) :
    objective ((fullTrace N).point (N + 3)) -
      objective ((fullTrace N).point (N + 4)) = curvature N * scale N ^ 2 / 8 := by
  have he : N + 4 = (N + 3) + 1 := by omega
  rw [fullTrace, he, appendTrace_point_after]
  rw [show N + 3 = (N + 3) + 0 by omega, appendTrace_point_after]
  exact finalTrace_decrease N


/-- The final trial and its endpoint both fail the true constrained second-order criterion.
This is a statement about the whole feasible Taylor gap, independently of the computed test. -/
theorem finalTrace_true_gap_failure {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ 1) :
    tolerance N 2 * testRadius fixedParameters (finalTrace N) k ^ 2 / 2 <
      gapOn (taylorDecrement objective 2 ((finalTrace N).point k))
        (testingSet box ((finalTrace N).point k)
          (testRadius fixedParameters (finalTrace N) k)) := by
  have hs := scale_pos N
  have hs' := scale_le_quarter hN
  have hb := curvature_pos N
  have hb' := curvature_le_half hN
  have hr : 0 < scale N / 2 := by positivity
  have ht : testRadius fixedParameters (finalTrace N) k = scale N / 2 := by
    simp only [testRadius, finalTrace, fixedParameters]
    exact min_eq_left (by linarith)
  let d := point 0 (scale N / 2) 0
  have hd : d ∈ testingSet box ((finalTrace N).point k)
      (testRadius fixedParameters (finalTrace N) k) := by
    rw [mem_testingSet, ht]
    constructor
    · interval_cases k
      · change point 0 0 (curvature N) + point 0 (scale N / 2) 0 ∈ box
        rw [point_add, point_mem_box]
        norm_num [abs_of_nonneg hb.le,
          abs_of_nonneg (by positivity : 0 ≤ scale N / 2)]
        exact ⟨by linarith, by linarith⟩
      · change point 0 (scale N / 2) (curvature N) + point 0 (scale N / 2) 0 ∈ box
        rw [point_add, point_mem_box]
        norm_num [abs_of_nonneg hb.le, abs_of_nonneg hs.le]
        exact ⟨by linarith, by linarith⟩
    · change ‖point 0 (scale N / 2) 0‖ ≤ scale N / 2
      simp [abs_of_nonneg hr.le]
  apply lt_of_lt_of_le _ (le_gapOn (isCompact_testingSet isClosed_box _ _)
    (continuous_taylorDecrement objective 2 ((finalTrace N).point k)).continuousOn hd)
  rw [ht, tolerance_two, CoupledCubic.taylorDecrement_two]
  interval_cases k <;> norm_num [finalTrace, d]
  · nlinarith [mul_pos hb (sq_pos_of_pos hs)]
  · nlinarith [mul_pos hb (sq_pos_of_pos hs)]

/-- At the final trial's center and its retained endpoint, actual feasible quality still fails. -/
theorem fullTrace_final_true_gap_failure {N k : ℕ} (hN : 1 ≤ N) (hk : k ≤ 1) :
    tolerance N 2 * testRadius fixedParameters (fullTrace N) (N + 3 + k) ^ 2 / 2 <
      gapOn (taylorDecrement objective 2 ((fullTrace N).point (N + 3 + k)))
        (testingSet box ((fullTrace N).point (N + 3 + k))
          (testRadius fixedParameters (fullTrace N) (N + 3 + k))) := by
  simpa only [fullTrace, testRadius, appendTrace_point_after, appendTrace_radius_after] using
    finalTrace_true_gap_failure hN hk

end Optimization.CoupledCubicTrustRegionPrefix
