import Numlib.Optimization.CoupledCubicTrustRegionRun
import Numlib.Optimization.ConstrainedTrustRegionConcatenation

/-!
# Completing coupled cubic trust-region prefixes

A feasible finite prefix ending on the positive coupled-coordinate plane extends through a
finite first source stop. The continuation preserves every previously executed trial, its
selected-order acceptance ratio, and every retained point through the joining endpoint.
-/

noncomputable section
namespace Optimization.CoupledCubic
open HigherOrderTrustRegion ConstrainedTrustRegion

/-- Any actual feasible prefix ending at the admissible coupled state has a finite complete
source execution. All already executed trial fields and acceptance ratios are preserved. -/
theorem complete_trustRegion_prefix {p : Parameters} {epsilon : ℕ → ℝ}
    {R b : ℝ} {t : Trace Space} {N : ℕ}
    (ht : ConstrainedTrustRegion.LegalPrefix box p 2 epsilon objective t N)
    (hx : t.point N = point 0 R b) (hr : t.radius N = R)
    (hR : 0 < R) (hRb : R ≤ b) (hb : b ≤ 1 / 2)
    (hcap : R ≤ p.theta) (hmax : R ≤ p.radiusMax)
    (he : ∀ j, 1 ≤ j → j ≤ 2 → 0 < epsilon j) :
    ∃ u : Trace Space, ∃ K : ℕ,
      ConstrainedTrustRegion.IsRun box p 2 epsilon objective u ∧
      ConstrainedTrustRegion.LegalPrefix box p 2 epsilon objective u (N + K) ∧
      Stops p 2 epsilon objective u (N + K) ∧
      (∀ k ≤ N, u.point k = t.point k ∧ u.radius k = t.radius k) ∧
      (∀ k < N, u.step k = t.step k ∧ u.witness k = t.witness k ∧
        u.order k = t.order k ∧ ratio objective u k = ratio objective t k) ∧
      (∀ n, u.point (N + K + n) = u.point (N + K) ∧ u.step (N + K + n) = 0) := by
  obtain ⟨v, K, hvx, hvr, _, hvlegal, hvstop, _, hvfrozen⟩ :=
    Continuation.exists_finite_continuation p epsilon hR hRb hb hcap hmax he
  let u := appendTrace t v N
  have hjoinx : v.point 0 = t.point N := hvx.trans hx.symm
  have hjoinr : v.radius 0 = t.radius N := hvr.trans hr.symm
  have hu : ConstrainedTrustRegion.LegalPrefix box p 2 epsilon objective u (N + K) :=
    ht.append hvlegal hjoinx hjoinr
  have hs : Stops p 2 epsilon objective u (N + K) :=
    (stops_appendTrace_after t v N K p 2 epsilon objective).mpr hvstop
  refine ⟨u, K, hu.isRun_of_stops hs, hu, hs, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hk' : k < N
    · exact ⟨appendTrace_point_before t v hk', appendTrace_radius_before t v hk'⟩
    · have heq : k = N := by omega
      subst k
      constructor
      · simpa only [Nat.add_zero] using (appendTrace_point_after t v N 0).trans hjoinx
      · simpa only [Nat.add_zero] using (appendTrace_radius_after t v N 0).trans hjoinr
  · intro k hk
    refine ⟨appendTrace_step_before t v hk, ?_, appendTrace_order_before t v hk, ?_⟩
    · funext j
      exact appendTrace_witness_before t v hk
    · simp only [u, ratio, appendTrace_point_before t v hk, appendTrace_step_before t v hk,
        appendTrace_order_before t v hk]
  · intro n
    have hf := hvfrozen n
    simpa only [u, Nat.add_assoc, appendTrace_point_after, appendTrace_step_after] using
      And.intro hf.1 hf.2.1

end Optimization.CoupledCubic
