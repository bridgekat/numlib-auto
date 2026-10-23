import Numlib.Optimization.TrustRegion.Inexact.MinRate.Run


/-!
# A fixed-objective counterexample to a minimum inverse-tolerance rate

Actual fixed-cost degree-zero, first and second derivative oracle events have unbounded
cardinality as the second tolerance shrinks. The literal minimum of inverse tolerance
powers remains eight.
-/

namespace OracleSimulation.MinRateCounterexample
open Real InexactTrustRegion

/-- The literal minimum of the inverse third powers of the two requested accuracies in
equation (13.2.5). -/
noncomputable def printedRate (N : ℕ) : ℝ :=
  minimumAccuracy settings.order_pos (fun a => requested N a ^ (-(3 : ℝ)))

/-- The literal printed rate is exactly eight for every horizon in the fixed-objective
family. -/
theorem printedRate_eq_eight (N : ℕ) : printedRate N = 8 := by
  unfold printedRate
  apply le_antisymm
  · have hh := minimumAccuracy_le settings.order_pos
      (fun a => requested N a ^ (-(3 : ℝ))) 0
    have hfirst : requested N 0 ^ (-(3 : ℝ)) = 8 := by
      norm_num [requested, Real.rpow_neg, Real.rpow_natCast]
    rw [hfirst] at hh
    exact hh
  · apply Finset.le_inf'
    intro a ha
    have hhalf : requested N a ≤ 1 / 2 := by
      unfold requested
      split_ifs
      · exact le_rfl
      · exact (magnitude_lt_quarter N).le.trans (by norm_num)
    have hh := Real.rpow_le_rpow_of_nonpos (requested_pos N a) hhalf
      (by norm_num : -(3 : ℝ) ≤ 0)
    norm_num only [Real.rpow_neg, Real.rpow_natCast] at hh
    norm_num at hh
    change 8 ≤ requested N a ^ (-((3 : ℕ) : ℝ))
    rw [Real.rpow_neg_natCast]
    exact hh

/-- Actual exact-oracle batches use one oracle of the requested degree at every
initialized objective or derivative evaluation. -/
noncomputable def primitiveCalls (N : ℕ) : ℕ := OracleSimulation.calls
  (OracleSimulation.schedule 2 (functionEvaluations (trials N) N)
    (derivativeEvaluations (trials N) (fun _ => ratio) settings.eta1 N))
  (fun i _ => [i])

/-- The actual fixed-cost exact-oracle schedule makes three times the initialized point
count calls. -/
theorem primitiveCalls_eq (N : ℕ) : primitiveCalls N = 3 * (N + 1) := by
  rw [primitiveCalls, function_evaluations, derivative_evaluations]
  simp [OracleSimulation.calls, OracleSimulation.schedule]

/-- The genuine order-point oracle events at all fresh initialized and accepted points. -/
noncomputable def oracleEvents (N : ℕ) : Finset (Fin 3 × ℝ) := by
  classical
  exact Finset.univ ×ˢ ((Finset.range (N + 1)).image node)

/-- All actual initialized and accepted trial points are distinct and strictly increasing. -/
theorem node_strictMono : StrictMono node := by
  intro i j hij
  dsimp [node]
  exact_mod_cast (Nat.add_lt_add_right hij 3)

/-- Actual oracle events have three orders at each distinct initialized or accepted point. -/
theorem oracleEvents_card (N : ℕ) : (oracleEvents N).card = 3 * (N + 1) := by
  classical
  simp [oracleEvents, Finset.card_image_of_injective _ node_strictMono.injective]

/-- The primitive batch count equals the cardinality of the actual order-point evaluation
events. -/
theorem primitiveCalls_eq_event_card (N : ℕ) : primitiveCalls N = (oracleEvents N).card := by
  rw [primitiveCalls_eq, oracleEvents_card]

/-- At arbitrarily small second-order accuracy the actual exact-oracle work exceeds every
fixed multiple of the literal printed rate. -/
theorem arbitrarily_many_calls (κ bar : ℝ) (hbar : 0 < bar) :
    ∃ N : ℕ, requested N 1 < bar ∧
      κ * printedRate N < (primitiveCalls N : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (8 * κ) (π / bar))
  have hNκ : 8 * κ < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hNbar : π / bar < (N : ℝ) := (le_max_right _ _).trans_lt hN
  have hπbar : π < bar * (N : ℝ) := by
    have hh := (div_lt_iff₀ hbar).mp hNbar
    nlinarith
  have he : node N + 1 ≤ exp (node N) := Real.add_one_le_exp _
  have hn : (N : ℝ) < node N + 1 := by dsimp [node]; push_cast; linarith
  have hsmall : magnitude N < bar := by
    unfold magnitude
    rw [Real.exp_neg]
    apply (mul_inv_lt_iff₀ (Real.exp_pos _)).mpr
    have hmul : bar * (node N + 1) ≤ bar * exp (node N) :=
      mul_le_mul_of_nonneg_left he hbar.le
    have hlt : bar * (N : ℝ) < bar * (node N + 1) :=
      mul_lt_mul_of_pos_left hn hbar
    nlinarith
  refine ⟨N, by
    simpa only [requested, show ¬(1 : Fin 2) = 0 by decide, ite_false] using hsmall, ?_⟩
  rw [printedRate_eq_eight, primitiveCalls_eq]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith [show (0 : ℝ) ≤ (N : ℝ) by positivity]

/-- No tolerance-independent Big-O coefficient, even on an arbitrarily small second-order
tolerance interval, bounds the actual work by the literal printed minimum rate. -/
theorem no_printed_oracle_bound :
    ¬∃ κ > 0, ∃ bar > 0, ∀ N : ℕ, requested N 1 < bar →
      (primitiveCalls N : ℝ) ≤ κ * printedRate N := by
  rintro ⟨κ, hκ, bar, hbar, hbound⟩
  obtain ⟨N, hsmall, hlarge⟩ := arbitrarily_many_calls κ bar hbar
  exact (not_le_of_gt hlarge) (hbound N hsmall)

/-- No produced point through the horizon meets the true all-order target for any legal
vector of positive optimality radii. -/
theorem no_earlier_target (N : ℕ) {k : ℕ} (hk : k ≤ N) (δ : Fin 2 → ℝ)
    (hδ : ∀ a, 0 < δ a ∧ δ a ≤ 1) :
    ¬∀ a : Fin 2, TaylorModel.criticality objective (modelOrder a) (node k) (δ a) ≤
      requested N a * δ a ^ modelOrder a / (modelOrder a).factorial := by
  intro h
  have hh := h 1
  have ho : modelOrder (1 : Fin 2) = 2 := rfl
  rw [ho] at hh
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at hh
  exact (not_le_of_gt (true_second_failure hk (hδ 1).1)) hh

/-- One fixed globally bounded C2 objective with globally Lipschitz derivatives admits
actual exact-oracle TRqIDA executions with arbitrarily many calls at arbitrarily small
second-order tolerance, while the literal printed minimum rate is eight. Thus the trust-
region clause of Theorem13.2.1 is false with its literal minimum; the fixed-cost
corrected companions use the maximum. -/
theorem verified_counterexample : ∃ L B : ℝ, 1 ≤ L ∧ 0 < B ∧
    ContDiff ℝ 2 objective ∧ (∀ x, |objective x| ≤ B) ∧
    (∀ j, j ≤ 2 → ∀ x y,
      ‖iteratedFDeriv ℝ j objective x - iteratedFDeriv ℝ j objective y‖ ≤
        L * ‖x - y‖) ∧
    (∀ N a, 0 < requested N a ∧ requested N a < 1) ∧
    (∀ N, InexactTrustRegion.Run objective settings (requested N)
      exactJet (trials N) (fun _ => 1) node (fun _ => 1) (fun _ => 1)
        (fun _ => 1) (fun _ => ratio) (fun _ _ => 1 / 32) N) ∧
    (∀ N k, k ≤ N →
      TaylorModel.decrement objective 1 (node k) 1 ≤ 1 / 2 * requested N 0 ∧
      TaylorModel.decrement objective 2 (node k) 1 =
        TaylorModel.criticality objective 2 (node k) 1 ∧
      (1 / 2 : ℝ) * requested N 1 / 2 <
        TaylorModel.decrement objective 2 (node k) 1) ∧
    (∀ N k, k ≤ N → ∀ δ : Fin 2 → ℝ, (∀ a, 0 < δ a ∧ δ a ≤ 1) →
      ¬∀ a : Fin 2, TaylorModel.criticality objective (modelOrder a) (node k) (δ a) ≤
        requested N a * δ a ^ modelOrder a / (modelOrder a).factorial) ∧
    (∀ N, primitiveCalls N = (oracleEvents N).card ∧ primitiveCalls N = 3 * (N + 1)) ∧
    (∀ N, printedRate N = 8) ∧
    (∀ κ bar : ℝ, 0 < bar → ∃ N : ℕ, requested N 1 < bar ∧
      κ * printedRate N < (primitiveCalls N : ℝ)) := by
  obtain ⟨L, B, hL, hB, hf, hb, hLip, _⟩ := objective_spec
  exact ⟨L, B, hL, hB, hf, hb, hLip,
    fun N a => ⟨requested_pos N a, requested_lt_one N a⟩, run,
    fun N k hk => ⟨(ordered_checks N k).2.1, (ordered_checks N k).2.2,
      selected_second hk⟩,
    fun N k hk δ hδ => no_earlier_target N hk δ hδ,
    fun N => ⟨primitiveCalls_eq_event_card N, primitiveCalls_eq N⟩,
    printedRate_eq_eight, arbitrarily_many_calls⟩

end OracleSimulation.MinRateCounterexample
