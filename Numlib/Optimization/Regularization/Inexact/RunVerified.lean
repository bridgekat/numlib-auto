import Numlib.Optimization.Regularization.Inexact.SharpOutcomes

/-!
# True optimality after actual passing regularization checks

Actual Step1 directions and tests, the exact propagated radius floor, and the
primitive oracle requests certify the true Taylor measures. The zero-error
oracle needs no small-request condition. The parameter cap retains the literal
short-step guard through the corrected maximum accuracy coefficient.
-/

namespace InexactRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The derived parameter cap for the literal short-step guarded execution. -/
noncomputable def executionParameterCap {p q : ℕ} (P : Settings p q) (L : ℝ) : ℝ :=
  max P.sigmaInitial
    (P.gamma3 * parameterCoefficient P.toOracleSettings L / (1 - P.eta2))

namespace Run
variable {p q : ℕ} {f : E → ℝ} {P : Settings p q} {ε : Fin q → ℝ}
  {D : ExecutionData E q} {N : ℕ}

/-- An actual all-passing Step1 check certifies true normalized optimality
under the printed error budget and a genuine parameter cap. This also covers
an exact oracle with zero error bound, without restricting its requests. -/
theorem passing_optimality_of_cap (h : Run f P ε D N) {M S H : ℝ}
    (hM : 1 ≤ M) (hH : 0 ≤ H)
    (hparam : ∀ k ≤ N, D.parameter k ≤ S)
    (hjet : ∀ k ≤ N, ∀ i, 2 ≤ i → i ≤ p → ‖D.jet k i‖ ≤ M)
    {k : ℕ} (hk : k ≤ N) (hselected : D.selected k = none)
    (haccuracy : ∀ i, 1 ≤ i → i ≤ p → D.accuracy k i ≤ H)
    (hsmall : P.errorBound = 0 ∨ H ≤ verificationThreshold q P.zeta
      (stepRadiusCoefficient P.zeta P.theta M S) P.errorBound
      (minimumAccuracy P.order_pos ε)) :
    OptimalityAt f ε (D.point k) (D.checkedRadius k) := by
  have hκ := stepRadiusCoefficient_mem (σ := S) P.zeta_pos P.zeta_le_one
    P.theta_pos P.theta_lt_one.le hM
  have hfloor := (h.radius_floor_sharp hM hparam hjet).2.1 k hk
  have hone := h.step_one k hk
  have hpass := hone.outcome
  rw [hselected] at hpass
  have hcheck := vectorTerminationCheck_of_uniform_cap P.order_pos (D.jet k)
    (D.checkedRadius k) ε P.zeta (stepRadiusCoefficient P.zeta P.theta M S)
    P.errorBound H (fun a => D.checkDirection k a (D.checkCount k a)) (D.accuracy k)
    (fun a => (h.checkedRadius_mem hk a).1.le) (fun a => (h.checkedRadius_mem hk a).2)
    P.zeta_pos P.zeta_le_one hκ.1.le hκ.2 P.errorBound_nonneg
    h.accuracy_pos h.accuracy_le_one hH
    (fun a => (mul_le_mul_of_nonneg_left (minimumAccuracy_le P.order_pos ε a)
      hκ.1.le).trans (hfloor a)) hsmall
    (fun i hi hiq => haccuracy i hi (hiq.trans P.order_le))
    (fun a => by simpa only [← hone.radius_eq a] using
      hone.approximation a (D.checkCount k a)) hpass
  refine ⟨h.checkedRadius_mem hk, hcheck.true_optimality f (D.point k) ?_⟩
  intro i hi hiq
  have hip := hiq.trans P.order_le
  exact (h.oracle_all k hk i hi hip).trans
    (mul_le_mul_of_nonneg_right (P.errorCoefficient_le i hi hip)
      (h.accuracy_mem hk hi hip).1)

end Run
end InexactRegularization
