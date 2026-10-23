import Numlib.Optimization.Composite.RunBudget
import Numlib.Optimization.Regularization.HighOrder.CriticalityCounting

/-!
# Finite true-target attainment for composite regularization

Actual decrease and parameter-update budgets preclude indefinitely many trials
before a true certificate or the literal zero-decrease exit. The first such
index retains the initialized function and derivative evaluation bounds.
-/

namespace Composite
open HighOrderRegularization (parameterCap parameterCap_pos trialCountFactor trialCountOffset)
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every consistent actual composite execution with the general radius policy
attains a first true target within the initialized general-rate budgets. -/
theorem exists_target_general {p q : ℕ} {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {P : Settings p q} {ε : Fin q → ℝ} {D : ExecutionData E q}
    (hprefix : ∀ N, (∀ k < N, ¬TargetAt f c h P ε D k) → Run f c h P ε D N)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc wlow : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    (hlow : ∀ x, wlow ≤ f x + h (c x))
    (hfloor : ∀ k, ‖D.step k‖ < 1 → ∀ a,
      radiusCoefficient P (Lf + (K : ℝ) * Lc)
        (parameterCap P (Lf + (K : ℝ) * Lc)) * ε a ≤ D.solvedRadius k a) :
    let L := Lf + (K : ℝ) * Lc
    let S := parameterCap P L
    let d := generalDecreaseCoefficient P L S * generalAccuracyFactor P ε
    ∃ k, TargetAt f c h P ε D k ∧ Run f c h P ε D k ∧
      (∀ i < k, ¬TargetAt f c h P ε D i) ∧
      (functionEvaluations k : ℝ) ≤
        (f (D.point 0) + h (c (D.point 0)) - wlow) / d * trialCountFactor P +
          (trialCountFactor P + trialCountOffset P L + 1) ∧
      (derivativeEvaluations D.ratio P.eta1 k : ℝ) ≤
        (f (D.point 0) + h (c (D.point 0)) - wlow) / d + 2 := by
  classical
  let L := Lf + (K : ℝ) * Lc
  let S := parameterCap P L
  let d := generalDecreaseCoefficient P L S * generalAccuracyFactor P ε
  have h0 := hprefix 0 (by intro k hk; omega)
  have hL : 1 ≤ L := by dsimp [L]; nlinarith [mul_nonneg K.coe_nonneg hLc]
  have hd : 0 < d := mul_pos (generalDecreaseCoefficient_pos P hL
    (parameterCap_pos P L).le) (generalAccuracyFactor_pos P h0.accuracy_pos)
  have estimate (N : ℕ) (hr : Run f c h P ε D N)
      (hn : ∀ k < N, ¬TargetAt f c h P ε D k) :=
    hr.evaluation_bounds (S := S) hd hlow
      (fun k hk ha hnot => hr.function_decrease_general hf hc hLf hLc hh hlipf hlipc
        hk ha (hfloor k) hnot) hn
      (hr.parameter_le hf hc (zero_le_one.trans hLf) hLc hh hlipf hlipc le_rfl)
  have hex : ∃ k, TargetAt f c h P ε D k := by
    by_contra hn
    push Not at hn
    let B := (f (D.point 0) + h (c (D.point 0)) - wlow) / d * trialCountFactor P +
      (trialCountFactor P + trialCountOffset P L + 1)
    obtain ⟨N, hN⟩ := exists_nat_gt B
    have hb := (estimate N (hprefix N (fun k _ => hn k)) (fun k _ => hn k)).1
    simp only [functionEvaluations, Nat.cast_add, Nat.cast_one] at hb
    change (N : ℝ) + 1 ≤ B at hb
    linarith
  let k := Nat.find hex
  have hfirst : ∀ i < k, ¬TargetAt f c h P ε D i := fun i hi => Nat.find_min hex hi
  have hr := hprefix k hfirst
  exact ⟨k, Nat.find_spec hex, hr, hfirst, estimate k hr hfirst⟩

/-- Every consistent actual first-order unit-radius execution attains a first
true target within the sharper initialized first-order rate budgets. -/
theorem exists_target_unit {p q : ℕ} {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {P : Settings p q} {ε : Fin q → ℝ} {D : ExecutionData E q} (hq : q = 1)
    (hprefix : ∀ N, (∀ k < N, ¬TargetAt f c h P ε D k) → Run f c h P ε D N)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {Lf Lc wlow : ℝ} {K : NNReal}
    (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    (hlow : ∀ x, wlow ≤ f x + h (c x))
    (hunit : ∀ k a, D.solvedRadius k a = 1) :
    let L := Lf + (K : ℝ) * Lc
    let S := parameterCap P L
    let d := unitDecreaseCoefficient P L S * unitAccuracyFactor P ε
    ∃ k, TargetAt f c h P ε D k ∧ Run f c h P ε D k ∧
      (∀ i < k, ¬TargetAt f c h P ε D i) ∧
      (functionEvaluations k : ℝ) ≤
        (f (D.point 0) + h (c (D.point 0)) - wlow) / d * trialCountFactor P +
          (trialCountFactor P + trialCountOffset P L + 1) ∧
      (derivativeEvaluations D.ratio P.eta1 k : ℝ) ≤
        (f (D.point 0) + h (c (D.point 0)) - wlow) / d + 2 := by
  classical
  let L := Lf + (K : ℝ) * Lc
  let S := parameterCap P L
  let d := unitDecreaseCoefficient P L S * unitAccuracyFactor P ε
  have h0 := hprefix 0 (by intro k hk; omega)
  have hL : 1 ≤ L := by dsimp [L]; nlinarith [mul_nonneg K.coe_nonneg hLc]
  have hd : 0 < d := mul_pos (unitDecreaseCoefficient_pos P hL
    (parameterCap_pos P L).le) (unitAccuracyFactor_pos P h0.accuracy_pos)
  have estimate (N : ℕ) (hr : Run f c h P ε D N)
      (hn : ∀ k < N, ¬TargetAt f c h P ε D k) :=
    hr.evaluation_bounds (S := S) hd hlow
      (fun k hk ha hnot => hr.function_decrease_unit hq hf hc hLf hLc hh hlipf hlipc
        hk ha (hunit k) hnot) hn
      (hr.parameter_le hf hc (zero_le_one.trans hLf) hLc hh hlipf hlipc le_rfl)
  have hex : ∃ k, TargetAt f c h P ε D k := by
    by_contra hn
    push Not at hn
    let B := (f (D.point 0) + h (c (D.point 0)) - wlow) / d * trialCountFactor P +
      (trialCountFactor P + trialCountOffset P L + 1)
    obtain ⟨N, hN⟩ := exists_nat_gt B
    have hb := (estimate N (hprefix N (fun k _ => hn k)) (fun k _ => hn k)).1
    simp only [functionEvaluations, Nat.cast_add, Nat.cast_one] at hb
    change (N : ℝ) + 1 ≤ B at hb
    linarith
  let k := Nat.find hex
  have hfirst : ∀ i < k, ¬TargetAt f c h P ε D i := fun i hi => Nat.find_min hex hi
  have hr := hprefix k hfirst
  exact ⟨k, Nat.find_spec hex, hr, hfirst, estimate k hr hfirst⟩

end Composite
