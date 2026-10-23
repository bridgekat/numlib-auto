import Numlib.Optimization.Composite.RunConsequences
import Numlib.Optimization.Composite.ModelError
import Numlib.Optimization.Composite.StepPowers

/-!
# Actual composite execution step powers

Before the first true certificate, an accepted step transfers genuine model
criticality to genuine objective criticality. The two residual value errors are
retained. Fixed coefficients chosen before all accuracies then give the source
accuracy powers under the explicit radius policy.
-/

namespace Composite
open InexactTrustRegion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fixed composite radius coefficient at a uniform parameter bound. -/
noncomputable def radiusCoefficient {p q : ℕ} (P : Settings p q) (L S : ℝ) : ℝ :=
  P.zeta * P.theta / (8 * (3 * L + S))

/-- The source radius coefficient lies in `(0,1]` on the normalized range. -/
theorem radiusCoefficient_mem {p q : ℕ} (P : Settings p q) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 ≤ S) :
    0 < radiusCoefficient P L S ∧ radiusCoefficient P L S ≤ 1 := by
  have hnum := mul_pos P.zeta_pos P.theta_pos
  have hnum1 : P.zeta * P.theta ≤ 1 :=
    (mul_le_of_le_one_left P.theta_pos.le P.zeta_le_one).trans P.theta_lt_one.le
  unfold radiusCoefficient
  exact ⟨div_pos hnum (by linarith),
    (div_le_one (by linarith)).mpr (by linarith)⟩

/-- A common obstruction coefficient is chosen before the requested accuracies. -/
noncomputable def stepCoefficient {p q : ℕ} (P : Settings p q) (L S : ℝ) : ℝ :=
  min (CompositeStep.coefficient P.theta (L + S) (2 * L) q) (radiusCoefficient P L S)

/-- The fixed common step coefficient is positive and at most one. -/
theorem stepCoefficient_mem {p q : ℕ} (P : Settings p q) {L S : ℝ}
    (hL : 1 ≤ L) (hS : 0 ≤ S) :
    0 < stepCoefficient P L S ∧ stepCoefficient P L S ≤ 1 := by
  have hc := CompositeStep.coefficient_mem P.theta_pos P.theta_lt_one
    (by linarith : 1 ≤ L + S) (by linarith : 0 ≤ 2 * L) q
  have hr := radiusCoefficient_mem P hL hS
  exact ⟨lt_min hc.1 hr.1, (min_le_left _ _).trans hc.2⟩

namespace Run
variable {p q : ℕ} {f : E → ℝ} {c : E → F} {h : F → ℝ}
  {P : Settings p q} {ε : Fin q → ℝ} {D : ExecutionData E q} {N : ℕ}

/-- A short accepted trial before a true next-iterate certificate satisfies an
actual mixed-power obstruction, with both residual value errors included. -/
theorem short_step_obstruction (hr : Run f c h P ε D N)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc S : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hcap : D.parameter k ≤ S) (hs : ‖D.step k‖ < 1)
    (hn : ¬TargetAt f c h P ε D (k + 1)) :
    ∃ a : Fin q, (1 - P.theta) * ε a * D.solvedRadius k a ^ modelOrder a /
        (modelOrder a).factorial ≤
      (Lf + (K : ℝ) * Lc + S) *
        (∑ i ∈ Finset.range (modelOrder a),
          D.solvedRadius k a ^ (i + 1) * ‖D.step k‖ ^ (p - (i + 1) + 1) /
            (i + 1).factorial) +
      2 * (Lf + (K : ℝ) * Lc) * ‖D.step k‖ ^ (p + 1) := by
  have ho := hr.step_two k hk.le (hr.continues k hk)
  have hnot := hr.not_optimality_of_not_target (by omega) hn
  rw [hr.point_update k hk, hr.radius_update k hk] at hnot
  simp only [ite_eq_left haccepted] at hnot
  obtain ⟨a, ha⟩ := Composite.criticality_obstruction P.order_le f c hf hc hLf hLc
    (hr.modelTrace.updates.pos hk.le).le hcap P.theta_pos.le hh hlipf hlipc
    (D.point k) (D.step k) ε (D.solvedRadius k)
    (fun a => ⟨hr.accuracy_pos a, hr.accuracy_le_one a⟩) ho.radius_mem
    (fun _ a => ho.criticality_le P.zeta_pos hs a) hnot
  refine ⟨a, ha.trans ?_⟩
  apply add_le_add le_rfl
  have hfac : (1 : ℝ) ≤ (p + 1).factorial := by
    exact_mod_cast Nat.factorial_pos _
  calc
    _ ≤ 2 * (K : ℝ) * Lc * ‖D.step k‖ ^ (p + 1) :=
      div_le_self (by positivity) hfac
    _ ≤ _ := by
      have hprod := mul_nonneg (show 0 ≤ Lf from by linarith)
        (pow_nonneg (norm_nonneg (D.step k)) (p + 1))
      nlinarith only [hprod]

/-- An accepted trial before the next true certificate satisfies one of the
source accuracy powers with a single accuracy-independent positive coefficient. -/
theorem exists_power_lower (hr : Run f c h P ε D N)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc S : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hS : 0 ≤ S) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hcap : D.parameter k ≤ S)
    (hfloor : ‖D.step k‖ < 1 → ∀ a,
      radiusCoefficient P (Lf + (K : ℝ) * Lc) S * ε a ≤ D.solvedRadius k a)
    (hn : ¬TargetAt f c h P ε D (k + 1)) :
    ∃ a : Fin q, stepCoefficient P (Lf + (K : ℝ) * Lc) S ^ (q + 1) *
      ε a ^ (modelOrder a + 1) ≤ ‖D.step k‖ ^ (p + 1) := by
  let L := Lf + (K : ℝ) * Lc
  have hL : 1 ≤ L := by dsimp [L]; nlinarith [mul_nonneg K.coe_nonneg hLc]
  have hcoef := stepCoefficient_mem P hL hS
  by_cases hs : ‖D.step k‖ < 1
  · obtain ⟨a, ha⟩ := hr.short_step_obstruction hf hc hLf hLc hh hlipf hlipc
      hk haccepted hcap hs hn
    refine ⟨a, ?_⟩
    exact CompositeStep.uniform_power_lower_of_obstruction
      (by omega) (Nat.succ_le_of_lt a.isLt) P.order_le
      P.theta_pos P.theta_lt_one (by linarith) (by linarith)
      hcoef.1.le hcoef.2 (min_le_left _ _) (min_le_right _ _)
      (hr.accuracy_pos a).le (hr.accuracy_le_one a)
      ((hr.step_two k hk.le (hr.continues k hk)).radius_mem a).1
      (norm_nonneg _) (fun _ => hfloor hs a) ha
  · let a : Fin q := ⟨0, P.order_pos⟩
    refine ⟨a, ?_⟩
    have he : stepCoefficient P L S ^ (q + 1) * ε a ^ (modelOrder a + 1) ≤ 1 :=
      (mul_le_mul (pow_le_one₀ hcoef.1.le hcoef.2)
        (pow_le_one₀ (hr.accuracy_pos a).le (hr.accuracy_le_one a))
        (pow_nonneg (hr.accuracy_pos a).le _) zero_le_one).trans_eq (by ring)
    exact he.trans (one_le_pow₀ (not_lt.mp hs))

/-- Unit-radius first-order tests retain the sharper natural step power `p`.
Only the actual unit-radius policy is needed for this implication. -/
theorem exists_unit_power_lower (hr : Run f c h P ε D N) (hq : q = 1)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc S : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hS : 0 ≤ S) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    {k : ℕ} (hk : k < N) (haccepted : P.eta1 ≤ D.ratio k)
    (hcap : D.parameter k ≤ S) (hunit : ∀ a, D.solvedRadius k a = 1)
    (hn : ¬TargetAt f c h P ε D (k + 1)) :
    ∃ a : Fin q, CompositeStep.coefficient P.theta
      (Lf + (K : ℝ) * Lc + S) (2 * (Lf + (K : ℝ) * Lc)) 1 * ε a ≤
        ‖D.step k‖ ^ p := by
  let L := Lf + (K : ℝ) * Lc
  have hL : 1 ≤ L := by dsimp [L]; nlinarith [mul_nonneg K.coe_nonneg hLc]
  have hC : 1 ≤ L + S := by linarith
  have hB : 0 ≤ 2 * L := by linarith
  have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
  by_cases hs : ‖D.step k‖ < 1
  · obtain ⟨a, ha⟩ := hr.short_step_obstruction hf hc hLf hLc hh hlipf hlipc
      hk haccepted hcap hs hn
    have hj : modelOrder a = 1 := by unfold modelOrder; omega
    rw [hj, hunit a] at ha
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one,
      Finset.sum_range_one, zero_add, Nat.sub_add_cancel hp, one_mul, mul_one] at ha
    exact ⟨a, CompositeStep.power_lower_of_unit_obstruction P.theta_pos P.theta_lt_one
      hC hB (hr.accuracy_pos a).le (hr.accuracy_le_one a) (norm_nonneg _) ha⟩
  · let a : Fin q := ⟨0, P.order_pos⟩
    refine ⟨a, ?_⟩
    have hγ := CompositeStep.coefficient_mem P.theta_pos P.theta_lt_one hC hB 1
    exact ((mul_le_mul_of_nonneg_right hγ.2 (hr.accuracy_pos a).le).trans
      (by simpa only [one_mul] using hr.accuracy_le_one a)).trans
        (one_le_pow₀ (not_lt.mp hs))

end Run
end Composite
