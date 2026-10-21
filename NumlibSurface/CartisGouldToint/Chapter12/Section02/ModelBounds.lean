import NumlibSurface.CartisGouldToint.Chapter12.Section02
import Numlib.Optimization.HigherOrderDerivativeFamilyBounds
import Numlib.Optimization.HigherOrderModelDecrease
import Numlib.Optimization.HigherOrderRegularizationModelBounds

/-!
# Objective and Taylor bounds for regularized models

The all-orders objective assumptions imply the coefficient and Taylor-polynomial bounds
used in Lemma 12.2.7. The remaining radial regularizer estimates are separate foundations.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter12.Section02

variable {n p j : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℕ → ℝ}

/-- The objective's derivatives of order at least two are bounded by the common constant. -/
theorem LipschitzDerivativeFamily.norm_iteratedFDeriv_le_constant
    (hf : LipschitzDerivativeFamily f p L) (hj : 2 ≤ j) (hjp : j ≤ p)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ derivativeFamilyConstant p L :=
  hf.toHigherOrderDerivativeFamily.norm_iteratedFDeriv_le_maxConstant hj hjp x

/-- The Taylor-polynomial term in (12.2.40) is at most three times the common constant. -/
theorem LipschitzDerivativeFamily.norm_iteratedFDeriv_taylorModel_le
    (hf : LipschitzDerivativeFamily f p L) (hj : 2 ≤ j) (hjp : j ≤ p)
    (x s : EuclideanSpace ℝ (Fin n)) (hs : ‖s‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (Optimization.RegularizedTaylorModel.taylorModel f p x) s‖ ≤
      3 * derivativeFamilyConstant p L :=
  hf.toHigherOrderDerivativeFamily.norm_iteratedFDeriv_taylorModel_le hj hjp x s hs

/-- Lemma 12.2.7: the actual regularized model is Cᵖ, has σ-Lipschitz pth derivative,
and its derivatives of orders two through p satisfy (12.2.38) on the unit ball. -/
theorem lemma_12_2_7 (hf : LipschitzDerivativeFamily f p L) (hp : 1 ≤ p)
    (x : EuclideanSpace ℝ (Fin n)) {σ : ℝ} (hσ : 0 ≤ σ) :
    ContDiff ℝ p (regularizedTaylorModel f p x σ) ∧
    (∀ s t, ‖iteratedFDeriv ℝ p (regularizedTaylorModel f p x σ) s -
      iteratedFDeriv ℝ p (regularizedTaylorModel f p x σ) t‖ ≤ σ * ‖s - t‖) ∧
    ∀ s, ‖s‖ ≤ 1 → ∀ ℓ, 2 ≤ ℓ → ℓ ≤ p →
      ‖iteratedFDeriv ℝ ℓ (regularizedTaylorModel f p x σ) s‖ ≤
        3 * derivativeFamilyConstant p L + σ := by
  have hm := Optimization.HigherOrderRegularization.diagonalLipschitz_model
    (x := x) hf.smooth.contDiffAt hσ
  simp only [regularizedTaylorModel_eq_model]
  exact ⟨hm.smooth, fun s t => hm.operator_bound hp s t,
    fun s hs ℓ hℓ hℓp =>
      hf.toHigherOrderDerivativeFamily.norm_iteratedFDeriv_model_le hℓ hℓp x s hσ hs⟩

/-- Lemma 12.2.8: within the prescribed small radius, a positive actual Taylor decrement
gives at least half that amount of actual regularized-model decrease. -/
theorem lemma_12_2_8 (hf : LipschitzDerivativeFamily f p L) (hp : 1 ≤ p)
    (x s : EuclideanSpace ℝ (Fin n)) {σ α δ : ℝ} (hσ : 0 ≤ σ) (hs : ‖s‖ ≤ 1)
    (_hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : δ ≤ α / (4 * (3 * derivativeFamilyConstant p L + σ)))
    (hj : 1 ≤ j) (hjp : j ≤ p) (d : EuclideanSpace ℝ (Fin n)) (hd : ‖d‖ ≤ δ)
    (hdec : α * δ ^ j / (j ! : ℝ) ≤
      Optimization.TaylorCriticality.taylorDecrement (regularizedTaylorModel f p x σ) j s d) :
    α * δ ^ j / (2 * (j ! : ℝ)) ≤
      regularizedTaylorModel f p x σ s - regularizedTaylorModel f p x σ (s + d) := by
  have hL : 0 ≤ derivativeFamilyConstant p L :=
    hf.toHigherOrderDerivativeFamily.maxConstant_nonneg
  have hM : 0 < 3 * derivativeFamilyConstant p L + σ := by
    linarith [hf.one_le_constant hp]
  have hm : Optimization.HigherOrderRegularization.DiagonalLipschitz
      (regularizedTaylorModel f p x σ) p σ := by
    simpa only [regularizedTaylorModel_eq_model] using
      Optimization.HigherOrderRegularization.diagonalLipschitz_model
        (x := x) hf.smooth.contDiffAt hσ
  apply hm.half_decrease_of_small_radius hp hjp hM.le (by linarith) ⟨hδ.le, hδ1⟩ s d hd
  · intro i hi
    exact (lemma_12_2_7 hf hp x hσ).2.2 s hs i
      (by have := (Finset.mem_Icc.mp hi).1; omega) (Finset.mem_Icc.mp hi).2
  · have h := (le_div_iff₀ (by positivity : 0 < 4 *
        (3 * derivativeFamilyConstant p L + σ))).mp hsmall
    nlinarith only [h]
  · exact hdec

end CartisGouldToint.Chapter12.Section02
