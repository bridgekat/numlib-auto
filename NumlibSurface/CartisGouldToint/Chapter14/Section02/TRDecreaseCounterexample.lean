import Numlib.Optimization.CoupledCubicTrustRegionPrefix
import Numlib.Optimization.CoupledCubicTrustRegionCompletion
import NumlibSurface.CartisGouldToint.Chapter14.Section02.TRDecreaseData

/-!
# Chapter 14, Section 2: the literal heterogeneous TR decrease row

The printed TR row in (14.2.12) uses order-specific exponents `j + 1`. A single fixed
polynomial, feasible box, initial point, radius, and parameter vector admit a fixed family
of complete terminating executions whose accepted decrease has no positive uniform
coefficient for that payment. The uniform `q + 1` row in the complexity table is separate.
-/

noncomputable section
namespace CartisGouldToint.Chapter14.Section02
open Optimization CoupledCubic CoupledCubicTrustRegionRates CoupledCubicTrustRegionPrefix
open HigherOrderTrustRegion ConstrainedTrustRegion TaylorCriticality Set Metric

/-- The literal TR decrease row has exponents two and three at the two requested orders. -/
theorem coupledCubic_literal_tr_exponents :
    simpleConstraintDecreaseExponent .tr 2 2 1 box (fun _ : Space => (0 : ℝ)) = 2 ∧
      simpleConstraintDecreaseExponent .tr 2 2 2 box (fun _ : Space => (0 : ℝ)) = 3 := by
  norm_num [simpleConstraintDecreaseExponent]

/-- The fixed-data bad prefix extends through a finite first source stop. Both the center
and retained endpoint of its small accepted trial still fail the true feasible gap test. -/
theorem coupledCubic_completed_trace (N : ℕ) (hN : 1 ≤ N) :
    ∃ t : Trace Space, ∃ K : ℕ,
      t.point 0 = point 1 0 1 ∧ t.radius 0 = 2 ∧
      ConstrainedTrustRegion.IsRun box fixedParameters 2 (tolerance N) objective t ∧
      ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance N) objective t K ∧
      Stops fixedParameters 2 (tolerance N) objective t K ∧
      (∀ k < K, ¬Stops fixedParameters 2 (tolerance N) objective t k) ∧
      N + 4 ≤ K ∧ ratio objective t (N + 3) = 1 ∧
      objective (t.point (N + 3)) - objective (t.point (N + 4)) =
        curvature N * scale N ^ 2 / 8 ∧
      (∀ k ≤ 1, tolerance N 2 * testRadius fixedParameters t (N + 3 + k) ^ 2 / 2 <
        gapOn (taylorDecrement objective 2 (t.point (N + 3 + k)))
          (testingSet box (t.point (N + 3 + k))
            (testRadius fixedParameters t (N + 3 + k)))) := by
  have hs := scale_pos N
  have hs' := scale_le_quarter hN
  have hb := curvature_pos N
  have hb' := curvature_le_half hN
  obtain ⟨t, K, hrun, hlegal, hstop, hpoints, hfields, _⟩ :=
    complete_trustRegion_prefix (fullTrace_box hN) (fullTrace_endpoint N).1
      (fullTrace_endpoint N).2 (by positivity : 0 < scale N / 2)
      (by linarith [scale_le_curvature N] : scale N / 2 ≤ curvature N) hb'
      (by norm_num [fixedParameters]; linarith : scale N / 2 ≤ fixedParameters.theta)
      (by norm_num [fixedParameters]; linarith : scale N / 2 ≤ fixedParameters.radiusMax)
      (fun j _ _ => tolerance_pos N j)
  refine ⟨t, (N + 4) + K, ?_, ?_, hrun, hlegal, hstop, hlegal.nonterminal,
    by omega, ?_, ?_, ?_⟩
  · exact (hpoints 0 (Nat.zero_le _)).1.trans (fullTrace_initial N).1
  · exact (hpoints 0 (Nat.zero_le _)).2.trans (fullTrace_initial N).2
  · exact (hfields (N + 3) (by omega)).2.2.2.trans (fullTrace_final_ratio N)
  · rw [(hpoints (N + 3) (by omega)).1, (hpoints (N + 4) le_rfl).1]
    exact fullTrace_final_decrease N
  · intro k hk
    have hp := (hpoints (N + 3 + k) (by omega)).1
    have hr := (hpoints (N + 3 + k) (by omega)).2
    simpa only [testRadius, hp, hr] using fullTrace_final_true_gap_failure hN hk

/-- The literal decrease claim (14.2.11) with the printed TR row `pi_j = j + 1` fails.
All source analytic data and one family of full executions are fixed before the positive
coefficient is quantified. This says nothing against the uniform `q + 1` complexity row. -/
theorem literal_tr_decrease_counterexample :
    IsClosed box ∧ box.Nonempty ∧ Convex ℝ box ∧
      (∀ x ∈ box, -4 ≤ objective x) ∧
      ∃ L B : ℕ → ℝ, (∀ j, 1 ≤ L j) ∧ (∀ j, 1 ≤ B j) ∧
        SmoothBoundedJetsOnLevelSet objective box (point 1 0 1) 2 false (ball 0 5) L B ∧
        ∃ run : {N : ℕ // 1 ≤ N} → Trace Space,
        ∃ stop : {N : ℕ // 1 ≤ N} → ℕ,
          (∀ i, (∀ j, 0 < tolerance i.val j ∧ tolerance i.val j ≤ 1) ∧
            (run i).point 0 = point 1 0 1 ∧ (run i).radius 0 = 2 ∧
            ConstrainedTrustRegion.IsRun box fixedParameters 2 (tolerance i.val) objective
              (run i) ∧
            ConstrainedTrustRegion.LegalPrefix box fixedParameters 2 (tolerance i.val)
              objective (run i) (stop i) ∧
            Stops fixedParameters 2 (tolerance i.val) objective (run i) (stop i) ∧
            (∀ k < stop i, ¬Stops fixedParameters 2 (tolerance i.val) objective (run i) k) ∧
            i.val + 4 ≤ stop i ∧ ratio objective (run i) (i.val + 3) = 1 ∧
            (∀ k ≤ 1, tolerance i.val 2 *
              testRadius fixedParameters (run i) (i.val + 3 + k) ^ 2 / 2 <
              gapOn (taylorDecrement objective 2 ((run i).point (i.val + 3 + k)))
                (testingSet box ((run i).point (i.val + 3 + k))
                  (testRadius fixedParameters (run i) (i.val + 3 + k))))) ∧
          ¬∃ κ : ℝ, 0 < κ ∧ ∀ i,
            κ * min (tolerance i.val 1 ^ 2) (tolerance i.val 2 ^ 3) ≤
              objective ((run i).point (i.val + 3)) -
                objective ((run i).point (i.val + 4)) := by
  obtain ⟨L, B, hL, hB, hjets⟩ := coupledCubic_smoothBoundedJets
  have hex (i : {N : ℕ // 1 ≤ N}) := coupledCubic_completed_trace i.val i.property
  choose run stop hx hr hrun hlegal hstop hfirst hafter hratio hdecrease hgap using hex
  refine ⟨isClosed_box, box_nonempty, convex_box, fun _ hx => objective_lower_bound hx,
    L, B, hL, hB, hjets, run, stop, ?_, ?_⟩
  · intro i
    exact ⟨fun j => tolerance_bounds i.property j, hx i, hr i, hrun i, hlegal i,
      hstop i, hfirst i, hafter i, hratio i, hgap i⟩
  · rintro ⟨κ, hκ, hbound⟩
    apply no_uniform_payment
    refine ⟨κ, hκ, ?_⟩
    intro N hN
    have h := hbound ⟨N, hN⟩
    rwa [hdecrease ⟨N, hN⟩] at h

end CartisGouldToint.Chapter14.Section02
