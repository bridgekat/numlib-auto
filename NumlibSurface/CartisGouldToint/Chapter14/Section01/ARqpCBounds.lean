import NumlibSurface.CartisGouldToint.Chapter14.Section01.ARqpC
import Numlib.Optimization.CompositeRegularizationBounds

/-!
# Chapter 14, Section 1: composite parameter bounds

The componentwise Euclidean derivative bounds imply the exact source remainder constant.
Actual generalized Taylor value errors then control every parameter in a finite execution.
-/

noncomputable section
open scoped Nat NNReal
namespace CartisGouldToint.Chapter14.Section01
open Optimization CompositeTaylorModels CompositeRegularization
open HigherOrderApproximateRegularization (Parameters)

/-- The composite highest-order remainder constant (14.1.27). -/
def CompositeProblem.highestRemainderConstant {n m p : ℕ} (C : CompositeProblem n m p) : ℝ :=
  C.Lf p + Real.sqrt m * C.h.constant * C.Lc p

/-- The source componentwise derivative assumptions imply the actual generalized value
remainder, with no differentiation of the retained nonsmooth composition. -/
theorem CompositeProblem.value_remainder {n m p : ℕ} (C : CompositeProblem n m p)
    (hp : 1 ≤ p) (x s : EuclideanSpace ℝ (Fin n)) :
    |CompositeRegularization.objective C.f C.c C.h (x + s) - model C.f C.c C.h p x s| ≤
      C.highestRemainderConstant * ‖s‖ ^ (p + 1) / (p + 1)! := by
  have hmem : p ∈ Finset.Icc 1 p := by simp [hp]
  have hf := HigherOrderRegularization.DiagonalLipschitz.of_operator C.f_contDiff
    (C.Lf p).coe_nonneg (fun a b => by
      simpa only [dist_eq_norm] using (C.f_deriv_lipschitz p hmem).dist_le_mul a b)
  have hcomp : ∀ i : Fin m,
      |C.c (x + s) i - RegularizedTaylorModel.taylorModel (fun y => C.c y i) p x s| ≤
        ((C.Lc p : ℝ) / (p + 1)!) * ‖s‖ ^ (p + 1) := by
    intro i
    let L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m => ℝ) i
    have hci : ContDiff ℝ p (fun y => C.c y i) := L.contDiff.comp C.c_contDiff
    have hc := HigherOrderRegularization.DiagonalLipschitz.of_operator hci
      (C.Lc p).coe_nonneg (fun a b => by
        simpa only [dist_eq_norm] using (C.c_deriv_lipschitz p hmem i).dist_le_mul a b)
    exact hc.value_remainder hp x s
  have herror := compositeTaylorModel_error_le C.h.lipschitz C.c_contDiff.contDiffAt
    (div_nonneg (C.Lc p).coe_nonneg (by positivity)) (hf.value_remainder hp x s) hcomp
  change |CompositeRegularization.objective C.f C.c C.h (x + s) -
    model C.f C.c C.h p x s| ≤ _ at herror
  refine herror.trans_eq ?_
  unfold CompositeProblem.highestRemainderConstant
  ring

/-- Lemma 14.1.6: the source sigma bound for every state of an actual ARqpC execution. -/
theorem lemma_14_1_6 {n m : ℕ} {P : Parameters} {C : CompositeProblem n m P.p}
    {x : EuclideanSpace ℝ (Fin n)} {σ : ℝ} {δ : ℕ → ℝ} {N : ℕ}
    (run : algorithm_14_1_1 P C x σ δ N) {k : ℕ} (hk : k ≤ N) :
    (run.state k).sigma ≤ max σ (P.gamma3 * C.highestRemainderConstant / (1 - P.eta2)) := by
  simpa only [mul_div_assoc] using
    run.sigma_upper (C.value_remainder (P.order_pos.trans P.order_le)) hk

end CartisGouldToint.Chapter14.Section01
