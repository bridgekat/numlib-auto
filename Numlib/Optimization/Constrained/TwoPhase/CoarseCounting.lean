import Numlib.Optimization.Constrained.TwoPhase.CoarseCharges

/-!
# Actual event accounting for corrected two-phase calls

Every continuing call performs a terminal accepted trial. Its endpoint either
spends a good merit charge, resets, or spends a bad-reflection target charge.
All other successful trials precede the return and are good.
-/

namespace Constrained.TwoPhase
open Set TaylorModel EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] {p : ℕ} {f : E → ℝ} {c : E → F} {C : Set E}
  {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ β : ℝ} {D : Data E} {N : ℕ}

/-- Every accepted nonterminal endpoint is a genuine good charge. -/
theorem PhaseTwoRun.interior_good (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    (hβ : β ≤ 1) {k i : ℕ} (hk : k < N) (hi : i + 1 < D.length k)
    (hs : P.eta1 ≤ (D.inner k).ratio i) : i ∈ goodSuccesses P D f c C ε₀ ε₁ θ β k := by
  have hh := h.inner_nonterminal_failure hk hi
  have hε₁ := h.dual_pos
  have hθ := h.theta_pos
  have hε₀ := h.primal_pos
  have hfixed : β * (ε₁ * θ * ε₀) ≤ ε₁ * θ * ε₀ :=
    mul_le_of_le_one_left (by positivity) hβ
  have hmul := mul_lt_mul_of_pos_left hh.1 hε₁
  refine mem_goodSuccesses.mpr ⟨by omega, hs, ?_⟩
  nlinarith only [hfixed, hmul, hh.2]

/-- At most one actual accepted trial per call lies outside the good set. -/
theorem PhaseTwoRun.successful_card_le_good_add_one
    (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N) (hβ : β ≤ 1)
    {k : ℕ} (hk : k < N) :
    (successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card ≤
      (goodSuccesses P D f c C ε₀ ε₁ θ β k).card + 1 := by
  classical
  let bad : Finset ℕ := successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i ∧
    ¬β * (ε₁ * θ * ε₀) ≤ firstCriticality (targetMerit f c (D.target k)) C
      ((D.inner k).point (i + 1))} (D.length k)
  have hsub : bad ⊆ {D.length k - 1} := by
    intro i hi
    obtain ⟨hiN, hs, hg⟩ := mem_successfulIterations.mp hi
    have hlast : i + 1 = D.length k := by
      by_contra hn
      have hh := mem_goodSuccesses.mp (h.interior_good hβ hk (by omega) hs)
      exact hg hh.2.2
    simp only [Finset.mem_singleton]
    omega
  have hc : bad.card ≤ 1 := by simpa only [Finset.card_singleton] using Finset.card_le_card hsub
  have hpart := Finset.card_filter_add_card_filter_not
    (s := successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k))
    (fun i => β * (ε₁ * θ * ε₀) ≤ firstCriticality (targetMerit f c (D.target k)) C
      ((D.inner k).point (i + 1)))
  have he : (goodSuccesses P D f c C ε₀ ε₁ θ β k).card + bad.card =
      (successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card := by
    simpa only [goodSuccesses, bad, successfulIterations, Finset.filter_filter,
      Set.mem_ofPred_eq] using hpart
  omega

/-- Each continuing call has a terminal accepted event in one of the actual
charged sets: good successes, closed resets, or small-check reflections. -/
theorem PhaseTwoRun.continuing_call_charge
    (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N) {k : ℕ} (hk : k + 1 < N) :
    1 ≤ (goodSuccesses P D f c C ε₀ ε₁ θ β k).card +
      (if k ∈ resetIterations true f c ε₀ θ D N then 1 else 0) +
      (if k ∈ badReflections f c C ε₀ ε₁ θ β D N then 1 else 0) := by
  classical
  have hkN : k < N := by omega
  have hlen := h.continuing_length_pos hk
  have hs := h.terminal_accepted hkN hlen
  by_cases hg : β * (ε₁ * θ * ε₀) ≤
      firstCriticality (targetMerit f c (D.target k)) C (D.point (k + 1))
  · have hi : D.length k - 1 ∈ goodSuccesses P D f c C ε₀ ε₁ θ β k := by
      apply mem_goodSuccesses.mpr
      refine ⟨by omega, hs, ?_⟩
      simpa only [Nat.sub_add_cancel hlen, h.inner_end k hkN] using hg
    have hc := Finset.one_le_card.mpr ⟨_, hi⟩
    omega
  · by_cases hr : ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1))
    · have hkR : k ∈ resetIterations true f c ε₀ θ D N :=
        mem_resetIterations.mpr ⟨hkN, hr⟩
      simp only [hkR, ite_true]
      omega
    · have hover : f (D.point (k + 1)) < D.target k := by
        by_contra hn
        exact h.continues k hk (Or.inl ⟨hr, le_of_not_gt hn⟩)
      have hkB : k ∈ badReflections f c C ε₀ ε₁ θ β D N :=
        mem_badReflections.mpr ⟨hkN, hk, hr, hover, (lt_of_not_ge hg).le⟩
      simp only [hkB, ite_true]
      omega

/-- The actual number of calls is paid by good accepted endpoints, resets,
bad target reflections and at most one final return. -/
theorem PhaseTwoRun.calls_le_charges (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N) :
    N ≤ (∑ k ∈ Finset.range N, (goodSuccesses P D f c C ε₀ ε₁ θ β k).card) +
      (resetIterations true f c ε₀ θ D N).card +
      (badReflections f c C ε₀ ε₁ θ β D N).card + 1 := by
  classical
  let charge := fun k => (goodSuccesses P D f c C ε₀ ε₁ θ β k).card +
    (if k ∈ resetIterations true f c ε₀ θ D N then 1 else 0) +
    (if k ∈ badReflections f c C ε₀ ε₁ θ β D N then 1 else 0)
  have hsum : N - 1 ≤ ∑ k ∈ Finset.range N, charge k := by
    calc
      N - 1 = ∑ _k ∈ Finset.range (N - 1), 1 := by simp
      _ ≤ ∑ k ∈ Finset.range (N - 1), charge k := by
        exact Finset.sum_le_sum fun k hk => h.continuing_call_charge (by
          have := Finset.mem_range.mp hk
          omega)
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le _ _))
  have he : (∑ k ∈ Finset.range N, charge k) =
      (∑ k ∈ Finset.range N, (goodSuccesses P D f c C ε₀ ε₁ θ β k).card) +
        (resetIterations true f c ε₀ θ D N).card +
        (badReflections f c C ε₀ ε₁ θ β D N).card := by
    dsimp only [charge]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hR : resetIterations true f c ε₀ θ D N ⊆ Finset.range N := Finset.filter_subset _ _
    have hB : badReflections f c C ε₀ ε₁ θ β D N ⊆ Finset.range N :=
      Finset.filter_subset _ _
    have hr : (Finset.range N).filter (fun k => k ∈ resetIterations true f c ε₀ θ D N) =
        resetIterations true f c ε₀ θ D N := Finset.filter_mem_eq_inter.trans
          (Finset.inter_eq_right.mpr hR)
    have hb : (Finset.range N).filter (fun k => k ∈ badReflections f c C ε₀ ε₁ θ β D N) =
        badReflections f c C ε₀ ε₁ θ β D N := Finset.filter_mem_eq_inter.trans
          (Finset.inter_eq_right.mpr hB)
    simp only [Finset.sum_boole, hr, hb, Nat.cast_id]
  rw [he] at hsum
  omega

end Constrained.TwoPhase

namespace Constrained.TwoPhase
open Set TaylorModel EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] {p : ℕ} {f : E → ℝ} {c : E → F} {C S : Set E}
  {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ β L : ℝ} {D : Data E} {N : ℕ}

/-- Actual parameter updates pay for all trials of each interrupted call,
with no false endpoint criticality failure at its returned point. -/
theorem PhaseTwoRun.inner_trials_le_successes
    (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N) {k : ℕ} (hk : k < N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (targetMerit f c (D.target k)) S) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c (D.target k)) y -
        iteratedFDeriv ℝ p (targetMerit f c (D.target k)) z‖ ≤ L * ‖y - z‖) :
    (D.length k : ℝ) ≤
      (successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card *
        (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (ConvexRegularization.parameterCap P L / P.sigmaInitial) / Real.log P.gamma2 := by
  have hin := h.inner_run k hk
  have ht := iteration_bound_of_parameter_upper
    (S := {i | P.eta1 ≤ (D.inner k).ratio i})
    (fun _ hi => hin.modelTrace.updates.pos hi)
    P.gamma1_pos P.gamma1_lt_one P.one_lt_gamma2
    (hin.parameter_le hS hCS hC hf hL hlip le_rfl)
    (fun _ hi hs => hin.modelTrace.updates.successful_ge hi hs)
    (fun _ hi hs => hin.modelTrace.updates.unsuccessful_ge hi hs)
  rwa [hin.initial_parameter] at ht

end Constrained.TwoPhase
