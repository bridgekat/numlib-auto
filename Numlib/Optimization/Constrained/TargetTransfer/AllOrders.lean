import Numlib.Optimization.Constrained.TargetTransfer
import Numlib.Optimization.TrustRegion.Inexact.Selection


/-!
# All-order target-merit certificate transfers

All-order target-merit output transfers retain the exact first-order multiplier conclusion and
common-kernel certificates through order three; full feasible higher-order bounds include actual
increment errors.
-/

namespace Constrained
open InexactTrustRegion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Actual feasible displacements annihilated by both the actual first objective and constraint
derivatives. -/
def commonCriticalDirections (f : E → ℝ) (c : E → F) (X : Set E) (x : E) : Set E :=
  {d | x + d ∈ X ∧ fderiv ℝ f x d = 0 ∧ fderiv ℝ c x d = 0}

omit [ProperSpace E] in
/-- Zero belongs to the common critical directions at every feasible base point. -/
theorem zero_mem_commonCriticalDirections {f : E → ℝ} {c : E → F} {X : Set E}
    {x : E} (hx : x ∈ X) : (0 : E) ∈ commonCriticalDirections f c X x := by
  simpa [commonCriticalDirections] using hx

/-- A positive-gap true normalized all-order merit certificate implies the exact first-order
Lagrangian certificate, all-order full feasible certificates with residual-increment Taylor
error retained, and unchanged common-critical-direction certificates through order three. -/
theorem lagrangian_bounds_of_merit_certificates
    {q : ℕ} (hq : 0 < q) {f : E → ℝ} {c : E → F} {x : E}
    (hf : ContDiffAt ℝ q f x) (hc : ContDiffAt ℝ q c x)
    {t : ℝ} (ht : 0 < f x - t) {X : Set E} (hX : IsClosed X) (hx : x ∈ X)
    (ε δ : Fin q → ℝ) (hδ : ∀ a, 0 ≤ δ a)
    (hcrit : ∀ a, TaylorModel.constrainedCriticality (targetMerit f c t)
      (modelOrder a) X x (δ a) ≤ ε a * Real.sqrt (‖c x‖ ^ 2 + (f x - t) ^ 2) *
        δ a ^ modelOrder a / (modelOrder a).factorial) :
    let y := targetMultiplier f c t x
    TaylorModel.constrainedCriticality (vectorLagrangian f c y) 1 X x (δ ⟨0, hq⟩) ≤
      ε ⟨0, hq⟩ * multiplierNorm y * δ ⟨0, hq⟩ ∧
    (∀ a, TaylorModel.constrainedCriticality (vectorLagrangian f c y)
      (modelOrder a) X x (δ a) ≤ ε a * multiplierNorm y * δ a ^ modelOrder a /
        (modelOrder a).factorial +
          targetTaylorBound (residualIncrementMerit f c x) (modelOrder a) x (δ a) /
            (f x - t)) ∧
    ∀ a, modelOrder a ≤ 3 → TaylorModel.restrictedCriticality (vectorLagrangian f c y)
      (modelOrder a) (commonCriticalDirections f c X x) x (δ a) ≤
        ε a * multiplierNorm y * δ a ^ modelOrder a / (modelOrder a).factorial := by
  have horder (a : Fin q) : modelOrder a ≤ q := a.isLt
  have hf1 : DifferentiableAt ℝ f x :=
    hf.differentiableAt (by exact_mod_cast hq.ne')
  have hc1 : DifferentiableAt ℝ c x :=
    hc.differentiableAt (by exact_mod_cast hq.ne')
  refine ⟨lagrangian_first_order_of_targetMerit hf1 hc1 ht hX hx (hδ ⟨0,hq⟩)
    (by simpa [modelOrder] using hcrit ⟨0,hq⟩), ?_, ?_⟩
  · intro a
    exact lagrangian_bound_of_merit_certificate_with_increment
      (hf.of_le (by exact_mod_cast horder a)) (hc.of_le (by exact_mod_cast horder a))
      ht hX hx (hδ a) (hcrit a)
  · intro a ha
    exact lagrangian_restricted_bound_of_merit_certificate ha
      (hf.of_le (by exact_mod_cast horder a)) (hc.of_le (by exact_mod_cast horder a))
      ht hX (zero_mem_commonCriticalDirections hx) (hδ a) (fun _ hd => hd) (hcrit a)
end Constrained
