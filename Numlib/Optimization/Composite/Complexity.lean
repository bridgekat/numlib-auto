import Numlib.Optimization.Composite.Termination
import Numlib.Optimization.Composite.ConvexRadius

/-!
# Composite regularization evaluation complexity

Positive constants are chosen before all accuracies and execution data. Actual
primitive executions produce true generalized optimality certificates, with the
unit-radius first-order rate for convex outer functions and the general
composite accuracy-power rate otherwise. Zero model returns are justified by
their genuine global-gap computation.
-/

namespace Composite
open InexactTrustRegion
open HighOrderRegularization
  (parameterCap parameterCap_pos trialCountFactor one_le_trialCountFactor trialCountOffset)
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For a single requested order, the finite unit-radius accuracy minimum is
the source's scalar accuracy power. -/
theorem unitAccuracyFactor_eq_of_order_one {p q : ℕ} (P : Settings p q)
    (hq : q = 1) (ε : Fin q → ℝ) (a : Fin q) :
    unitAccuracyFactor P ε = ε a ^ unitExponent p := by
  apply le_antisymm (unitAccuracyFactor_le P ε a)
  unfold unitAccuracyFactor minimumAccuracy
  apply Finset.le_inf'
  intro b _
  have he : b = a := Fin.ext (by omega)
  rw [he]

/-- Fixed positive constants, chosen before accuracies, bound actual composite
executions producing a genuine general-order approximate optimality certificate. -/
theorem complexity_general {p q : ℕ} (P : Settings p q)
    (f : E → ℝ) (c : E → F) {h : F → ℝ}
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc wlow : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a c u - iteratedFDeriv ℝ a c v‖ ≤ Lc * ‖u - v‖)
    (hlow : ∀ x, wlow ≤ f x + h (c x)) :
    ∃ κs κa κc : ℝ, 0 < κs ∧ 0 < κa ∧ 0 < κc ∧
      ∀ (ε : Fin q → ℝ) (D : ExecutionData E q),
        (∀ N, (∀ k < N, ¬TargetAt f c h P ε D k) → Run f c h P ε D N) →
        (∀ k, ‖D.step k‖ < 1 → ∀ a,
          radiusCoefficient P (Lf + (K : ℝ) * Lc)
            (parameterCap P (Lf + (K : ℝ) * Lc)) * ε a ≤ D.solvedRadius k a) →
        ∃ (k : ℕ) (δ : Fin q → ℝ), Run f c h P ε D k ∧
          OptimalityAt f c h ε (D.point k) δ ∧
          (functionEvaluations k : ℝ) ≤
            κa * (f (D.point 0) + h (c (D.point 0)) - wlow) /
              generalAccuracyFactor P ε + κc ∧
          (derivativeEvaluations D.ratio P.eta1 k : ℝ) ≤
            κs * (f (D.point 0) + h (c (D.point 0)) - wlow) /
              generalAccuracyFactor P ε + 2 := by
  let L := Lf + (K : ℝ) * Lc
  let S := parameterCap P L
  let β := generalDecreaseCoefficient P L S
  let κs := 1 / β
  let κa := κs * trialCountFactor P
  let κc := trialCountFactor P + trialCountOffset P L + 1
  have hL : 1 ≤ L := by dsimp [L]; nlinarith [mul_nonneg K.coe_nonneg hLc]
  have hβ : 0 < β := generalDecreaseCoefficient_pos P hL (parameterCap_pos P L).le
  have hκs : 0 < κs := div_pos zero_lt_one hβ
  have hfac : 0 < trialCountFactor P := zero_lt_one.trans_le (one_le_trialCountFactor P)
  have hσ0 : 0 < P.sigmaInitial := P.sigmaMin_pos.trans_le P.sigmaMin_le_initial
  have hratio : 1 ≤ parameterCap P L / P.sigmaInitial :=
    (le_div_iff₀ hσ0).mpr (by simpa only [one_mul, parameterCap] using
      (le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))))
  have hoff : 0 ≤ trialCountOffset P L :=
    div_nonneg (Real.log_nonneg hratio) (Real.log_pos P.one_lt_gamma2).le
  have hκc : 0 < κc := by dsimp [κc]; linarith
  refine ⟨κs, κa, κc, hκs, mul_pos hκs hfac, hκc, ?_⟩
  intro ε D hprefix hfloor
  have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
  obtain ⟨k, ht, hr, _, hfun, hder⟩ := exists_target_general hprefix hf hc hLf hLc hh
    (hlipf p hp le_rfl) (hlipc p hp le_rfl) hlow hfloor
  obtain ⟨δ, hδ⟩ := hr.target_optimality le_rfl ht hf.contDiffAt hc.contDiffAt
    (zero_le_one.trans hLf) hLc hh
    (fun a ha hap => norm_iteratedFDeriv_le_of_lipschitz_lower (zero_le_one.trans hLf)
      (fun i hi hip => hlipf i hi hip.le) ha hap (D.point k))
    (fun a ha hap => norm_iteratedFDeriv_le_of_lipschitz_lower hLc
      (fun i hi hip => hlipc i hi hip.le) ha hap (D.point k))
  have hrate := generalAccuracyFactor_pos P hr.accuracy_pos
  change (functionEvaluations k : ℝ) ≤
    (f (D.point 0) + h (c (D.point 0)) - wlow) /
      (β * generalAccuracyFactor P ε) * trialCountFactor P + κc at hfun
  change (derivativeEvaluations D.ratio P.eta1 k : ℝ) ≤
    (f (D.point 0) + h (c (D.point 0)) - wlow) /
      (β * generalAccuracyFactor P ε) + 2 at hder
  refine ⟨k, δ, hr, hδ, ?_, ?_⟩
  · convert hfun using 1
    dsimp only [κa, κs]
    field_simp [hβ.ne', hrate.ne']
  · convert hder using 1
    dsimp only [κs]
    field_simp [hβ.ne', hrate.ne']


/-- Fixed positive constants bound actual composite executions producing a
unit-radius first-order certificate when the outer function is convex. -/
theorem complexity_unit {p q : ℕ} (P : Settings p q) (hq : q = 1)
    (f : E → ℝ) (c : E → F) {h : F → ℝ}
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc wlow : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hconv : ConvexOn ℝ Set.univ h)
    (hlipf : ∀ a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ a, 1 ≤ a → a ≤ p → ∀ u v,
      ‖iteratedFDeriv ℝ a c u - iteratedFDeriv ℝ a c v‖ ≤ Lc * ‖u - v‖)
    (hlow : ∀ x, wlow ≤ f x + h (c x)) :
    ∃ κs κa κc : ℝ, 0 < κs ∧ 0 < κa ∧ 0 < κc ∧
      ∀ (ε : Fin q → ℝ) (D : ExecutionData E q),
        (∀ N, (∀ k < N, ¬TargetAt f c h P ε D k) → Run f c h P ε D N) →
        (∀ k a, D.solvedRadius k a = 1) →
        ∃ k, Run f c h P ε D k ∧
          (∀ a, criticality f c h 1 (D.point k) 1 ≤ ε a) ∧
          (functionEvaluations k : ℝ) ≤
            κa * (f (D.point 0) + h (c (D.point 0)) - wlow) /
              unitAccuracyFactor P ε + κc ∧
          (derivativeEvaluations D.ratio P.eta1 k : ℝ) ≤
            κs * (f (D.point 0) + h (c (D.point 0)) - wlow) /
              unitAccuracyFactor P ε + 2 := by
  let L := Lf + (K : ℝ) * Lc
  let S := parameterCap P L
  let β := unitDecreaseCoefficient P L S
  let κs := 1 / β
  let κa := κs * trialCountFactor P
  let κc := trialCountFactor P + trialCountOffset P L + 1
  have hL : 1 ≤ L := by dsimp [L]; nlinarith [mul_nonneg K.coe_nonneg hLc]
  have hβ : 0 < β := unitDecreaseCoefficient_pos P hL (parameterCap_pos P L).le
  have hκs : 0 < κs := div_pos zero_lt_one hβ
  have hfac : 0 < trialCountFactor P := zero_lt_one.trans_le (one_le_trialCountFactor P)
  have hσ0 : 0 < P.sigmaInitial := P.sigmaMin_pos.trans_le P.sigmaMin_le_initial
  have hratio : 1 ≤ parameterCap P L / P.sigmaInitial :=
    (le_div_iff₀ hσ0).mpr (by simpa only [one_mul, parameterCap] using
      (le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))))
  have hoff : 0 ≤ trialCountOffset P L :=
    div_nonneg (Real.log_nonneg hratio) (Real.log_pos P.one_lt_gamma2).le
  have hκc : 0 < κc := by dsimp [κc]; linarith
  refine ⟨κs, κa, κc, hκs, mul_pos hκs hfac, hκc, ?_⟩
  intro ε D hprefix hunit
  have hp : 1 ≤ p := P.order_pos.trans_le P.order_le
  obtain ⟨k, ht, hr, _, hfun, hder⟩ := exists_target_unit hq hprefix hf hc hLf hLc hh
    (hlipf p hp le_rfl) (hlipc p hp le_rfl) hlow hunit
  obtain ⟨δ, hδ⟩ := hr.target_optimality le_rfl ht hf.contDiffAt hc.contDiffAt
    (zero_le_one.trans hLf) hLc hh
    (fun a ha hap => norm_iteratedFDeriv_le_of_lipschitz_lower (zero_le_one.trans hLf)
      (fun i hi hip => hlipf i hi hip.le) ha hap (D.point k))
    (fun a ha hap => norm_iteratedFDeriv_le_of_lipschitz_lower hLc
      (fun i hi hip => hlipc i hi hip.le) ha hap (D.point k))
  have hrate := unitAccuracyFactor_pos P hr.accuracy_pos
  change (functionEvaluations k : ℝ) ≤
    (f (D.point 0) + h (c (D.point 0)) - wlow) /
      (β * unitAccuracyFactor P ε) * trialCountFactor P + κc at hfun
  change (derivativeEvaluations D.ratio P.eta1 k : ℝ) ≤
    (f (D.point 0) + h (c (D.point 0)) - wlow) /
      (β * unitAccuracyFactor P ε) + 2 at hder
  have hunitcrit (a : Fin q) : criticality f c h 1 (D.point k) 1 ≤ ε a := by
    have hj : modelOrder a = 1 := by unfold modelOrder; omega
    apply criticality_one_unit_le_of_radius f c hh.continuous hconv (D.point k)
      (hδ.1 a).1 (hδ.1 a).2
    simpa only [hj, pow_one, Nat.factorial_one, Nat.cast_one, div_one] using hδ.2 a
  refine ⟨k, hr, hunitcrit, ?_, ?_⟩
  · convert hfun using 1
    dsimp only [κa, κs]
    field_simp [hβ.ne', hrate.ne']
  · convert hder using 1
    dsimp only [κs]
    field_simp [hβ.ne', hrate.ne']

end Composite
