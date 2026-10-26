import Numlib.Optimization.Constrained.TwoPhase.CompletedFullRun
import Numlib.Optimization.Constrained.TargetTransfer.AllOrders
import Numlib.Optimization.Constrained.TargetTransfer.ZeroGap


/-!
# Corrected complete two-phase output classification

Actual stopping runs yield either an infeasible Phase1 certificate, a zero-gap
violation certificate with its explicit higher-order objective-increment error,
or a positive-gap Lagrangian certificate with its residual-increment error.
First-order certificates and common-critical-direction bounds through order
three retain their exact form. No multiplier is formed at a zero gap.
-/

namespace Constrained.TwoPhase
open Set InexactTrustRegion
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Actual normalized all-order constraint-violation certificate at the given positive radii. -/
def ViolationCertificate {q : ℕ} (c : E → F) (X : Set E) (ε δ : Fin q → ℝ)
    (x : E) : Prop := ∀ a,
  TaylorModel.constrainedCriticality (LeastNorm.merit c) (modelOrder a) X x (δ a) ≤
    ε a * ‖c x‖ * δ a ^ modelOrder a / (modelOrder a).factorial

/-- Corrected zero-gap higher-order violation certificate retaining the squared objective-
increment Taylor error, together with the exact first-order certificate. -/
def ViolationIncrementCertificate {q : ℕ} (hq : 0 < q) (f : E → ℝ) (c : E → F)
    (X : Set E) (ε δ : Fin q → ℝ) (x : E) : Prop :=
  TaylorModel.constrainedCriticality (LeastNorm.merit c) 1 X x (δ ⟨0,hq⟩) ≤
    ε ⟨0,hq⟩ * ‖c x‖ * δ ⟨0,hq⟩ ∧ ∀ a,
  TaylorModel.constrainedCriticality (LeastNorm.merit c) (modelOrder a) X x (δ a) ≤
    ε a * ‖c x‖ * δ a ^ modelOrder a / (modelOrder a).factorial +
      targetTaylorBound (objectiveIncrementMerit f x) (modelOrder a) x (δ a)

/-- Positive-gap actual multiplier certificates: exact first-order bound, all-order full
feasible bounds retaining the residual-increment Taylor error, and unchanged common
critical-direction bounds through order three. -/
def LagrangianTaylorCertificate {q : ℕ} (hq : 0 < q) (f : E → ℝ) (c : E → F)
    (X : Set E) (ε δ : Fin q → ℝ) (x : E) : Prop := ∃ t : ℝ, 0 < f x - t ∧
  let y := targetMultiplier f c t x
  TaylorModel.constrainedCriticality (vectorLagrangian f c y) 1 X x (δ ⟨0,hq⟩) ≤
    ε ⟨0,hq⟩ * multiplierNorm y * δ ⟨0,hq⟩ ∧
  (∀ a, TaylorModel.constrainedCriticality (vectorLagrangian f c y)
    (modelOrder a) X x (δ a) ≤ ε a * multiplierNorm y * δ a ^ modelOrder a /
      (modelOrder a).factorial +
        targetTaylorBound (residualIncrementMerit f c x) (modelOrder a) x (δ a) /
          (f x - t)) ∧
  ∀ a, modelOrder a ≤ 3 → TaylorModel.restrictedCriticality (vectorLagrangian f c y)
    (modelOrder a) (commonCriticalDirections f c X x) x (δ a) ≤
      ε a * multiplierNorm y * δ a ^ modelOrder a / (modelOrder a).factorial

/-- The corrected full output alternative: legal feasible base point/radii and either the exact
infeasible Phase1 certificate, zero-gap infeasible certificate with explicit higher-order
error, or primal feasibility with the corrected multiplier certificates. -/
def CorrectedTwoPhaseOutput {q : ℕ} (hq : 0 < q) (f : E → ℝ) (c : E → F)
    (X : Set E) (θ ε₀ : ℝ) (ε δ : Fin q → ℝ) (x : E) : Prop :=
  x ∈ X ∧ (∀ a, 0 < δ a ∧ δ a ≤ 1) ∧
  ((θ * ε₀ < ‖c x‖ ∧ ViolationCertificate c X ε δ x) ∨
    (θ * ε₀ < ‖c x‖ ∧ ViolationIncrementCertificate hq f c X ε δ x) ∨
    (‖c x‖ ≤ ε₀ ∧ LagrangianTaylorCertificate hq f c X ε δ x))

namespace CompletedRun
variable {p q : ℕ} {f : E → ℝ} {c : E → F} {X : Set E}
  {P : ConstrainedRegularization.Settings p q} {β θ ε₀ L : ℝ} {ε : Fin q → ℝ}
  {D : CompletedData E q} {N : ℕ}

/-- Derive the corrected multiplier or zero-gap violation alternative from the actual completed-
inner Phase2 stopping return, using the genuine return certificate and actual finite
derivative transfers. -/
theorem corrected_return (h : CompletedRun f c X P β θ ε₀ L ε D N)
    (hX : IsClosed X) (hconv : Convex ℝ X) (hL : 1 ≤ L)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {flow fup : ℝ}
    (hfband : ∀ z ∈ X, ‖c z‖ ≤ 1 → flow ≤ f z ∧ f z ≤ fup)
    (hreg : ∀ t ∈ Icc (flow - 1) fup, ContDiff ℝ p (targetMerit f c t) ∧
      ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
        ‖iteratedFDeriv ℝ i (targetMerit f c t) y -
          iteratedFDeriv ℝ i (targetMerit f c t) z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k < N) (hs : CompletedStopAfter f c X P β θ ε₀ L ε D k) :
    let δ := completedRadius (targetMerit f c (D.target k)) X P
      (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k) L
    CorrectedTwoPhaseOutput P.order_pos f c X θ ε₀ ε δ (D.point (k + 1)) := by
  let δ := completedRadius (targetMerit f c (D.target k)) X P
    (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k) L
  obtain ⟨hx, hδ, hgap, hres, hcrit, hzero⟩ :=
    h.return_certificate hX hconv hL hfband hreg hk hs
  have hfs : ContDiffAt ℝ q f (D.point (k + 1)) :=
    (hf.of_le (by exact_mod_cast P.order_le)).contDiffAt
  have hcs : ContDiffAt ℝ q c (D.point (k + 1)) :=
    (hc.of_le (by exact_mod_cast P.order_le)).contDiffAt
  have horder (a : Fin q) : modelOrder a ≤ q := a.isLt
  refine ⟨hx, hδ, ?_⟩
  by_cases hp : 0 < f (D.point (k + 1)) - D.target (k + 1)
  · right; right
    refine ⟨(constraint_norm_le_residual f c _ _).trans hres,
      D.target (k + 1), hp, ?_⟩
    exact lagrangian_bounds_of_merit_certificates P.order_pos hfs hcs hp hX hx ε δ
      (fun a => (hδ a).1.le) (fun a => by
        simpa only [←residual_norm] using hcrit a)
  · have hz : f (D.point (k + 1)) - D.target (k + 1) = 0 := by linarith
    have ht : D.target (k + 1) = f (D.point (k + 1)) := by linarith
    have hnorm : ‖residual f c (D.target (k + 1)) (D.point (k + 1))‖ =
        ‖c (D.point (k + 1))‖ := by
      rw [residual_norm, hz];simp
    have hcrit' (a : Fin q) : TaylorModel.constrainedCriticality
        (targetMerit f c (f (D.point (k + 1)))) (modelOrder a) X (D.point (k + 1)) (δ a) ≤
      ε a * ‖c (D.point (k + 1))‖ * δ a ^ modelOrder a / (modelOrder a).factorial := by
      have hh := hcrit a
      rw [hnorm, ht] at hh
      exact hh
    right; left
    refine ⟨hzero hz, ?_, ?_⟩
    · exact violation_first_order_of_zero_gap_merit_certificate
        (hfs.of_le (by exact_mod_cast P.order_pos))
        (hcs.of_le (by exact_mod_cast P.order_pos)) hX hx (hδ ⟨0,P.order_pos⟩).1.le
        (by simpa [modelOrder] using hcrit' ⟨0,P.order_pos⟩)
    · intro a
      exact violation_bound_of_zero_gap_merit_certificate
        (hfs.of_le (by exact_mod_cast horder a)) (hcs.of_le (by exact_mod_cast horder a))
        hX hx (hδ a).1.le (hcrit' a)
end CompletedRun

namespace CompletedFullRun
variable {p q : ℕ} {f : E → ℝ} {c : E → F} {X : Set E}
  {P₁ P₂ : ConstrainedRegularization.Settings p q} {β θ ε₀ L : ℝ}
  {ε : Fin q → ℝ} {D : CompletedFullData E q}

/-- Every actual stopping full repaired two-phase execution returns its actual Phase1 or Phase2
point with the complete corrected output classification. Derive every criticality conclusion
from the actual primitive runs and guards. -/
theorem corrected_termination (h : CompletedFullRun f c X P₁ P₂ β θ ε₀ L ε D)
    (hX : IsClosed X) (hconv : Convex ℝ X) (hL : 1 ≤ L)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {flow fup : ℝ}
    (hfband : ∀ z ∈ X, ‖c z‖ ≤ 1 → flow ≤ f z ∧ f z ≤ fup)
    (hreg : ∀ t ∈ Icc (flow - 1) fup, ContDiff ℝ p (targetMerit f c t) ∧
      ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
        ‖iteratedFDeriv ℝ i (targetMerit f c t) y -
          iteratedFDeriv ℝ i (targetMerit f c t) z‖ ≤ L * ‖y - z‖)
    (hs : CompletedFullStop f c X P₂ β θ ε₀ L ε D) :
    (θ * ε₀ < ‖c (D.phaseOne.point D.phaseOneLength)‖ ∧
      ∃ δ, CorrectedTwoPhaseOutput P₂.order_pos f c X θ ε₀ ε δ
        (D.phaseOne.point D.phaseOneLength)) ∨
    (‖c (D.phaseOne.point D.phaseOneLength)‖ ≤ θ * ε₀ ∧ 0 < D.phaseTwoLength ∧
      ∃ δ, CorrectedTwoPhaseOutput P₂.order_pos f c X θ ε₀ ε δ
        (D.phaseTwo.point D.phaseTwoLength)) := by
  rcases hs with hi | ⟨hN, hs⟩
  · have hν : ContDiff ℝ p (LeastNorm.merit c) := (hc.norm_sq (𝕜 := ℝ)).div_const 2
    obtain ⟨δ, hx, hδ, hb⟩ := h.phaseOne_certificate hX hν hi
    exact Or.inl ⟨hi, δ, hx, hδ, Or.inl ⟨hi, hb⟩⟩
  · have hentry : ‖c (D.phaseOne.point D.phaseOneLength)‖ ≤ θ * ε₀ := by
      by_contra hn
      have he := h.phaseOne_exit (lt_of_not_ge hn)
      omega
    have hp := (h.phaseTwo_run hentry).corrected_return hX hconv hL hf hc hfband hreg
      (show D.phaseTwoLength - 1 < D.phaseTwoLength by omega) hs
    rw [show D.phaseTwoLength - 1 + 1 = D.phaseTwoLength by omega] at hp
    exact Or.inr ⟨hentry, hN, _, hp⟩
end CompletedFullRun
end Constrained.TwoPhase
