import Numlib.Optimization.Constrained.TwoPhase.CompletedReturn
import Numlib.Optimization.Constrained.TwoPhase.CompletedReflection

/-!
# Target budgets for completed-inner executions

Actual completed old-target certificates separate failed updated tests. Every
continuing call therefore spends a positive explicit target decrease, and the
fixed target interval pays for all calls with one final-return allowance.
-/

namespace Constrained.TwoPhase
open Set InexactTrustRegion
open HighOrderRegularization (parameterCap parameterCap_pos)

/-- Fixed reset or completed-reflection accuracy decrease. -/
noncomputable def completedDropTerm {p q : ℕ} (P : ConstrainedRegularization.Settings p q)
    (L β θ B ε₀ : ℝ) (ε : Fin q → ℝ) : Option (Fin q) → ℝ
  | none => (1 - θ) * ε₀
  | some a => completedReflectionCoefficient (modelOrder a) β θ
      (ConstrainedRegularization.radiusCoefficient P L (parameterCap P L) * β * θ) B *
        (ε₀ * ε a) ^ modelOrder a

/-- Common finite target-decrease floor, preceding every execution array. -/
noncomputable def completedDropFloor {p q : ℕ} (P : ConstrainedRegularization.Settings p q)
    (L β θ B ε₀ : ℝ) (ε : Fin q → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (completedDropTerm P L β θ B ε₀ ε)

/-- Legal settings give a strictly positive finite target-decrease floor. -/
theorem completedDropFloor_pos {p q : ℕ} (P : ConstrainedRegularization.Settings p q)
    {L β θ B ε₀ : ℝ} {ε : Fin q → ℝ} (hL : 1 ≤ L) (hβ : 0 < β) (hβ1 : β < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hB : 0 < B) (hε₀ : 0 < ε₀)
    (hε : ∀ a, 0 < ε a) : 0 < completedDropFloor P L β θ B ε₀ ε := by
  have hκ := (ConstrainedRegularization.radiusCoefficient_mem P hL
    (parameterCap_pos P L).le).1
  apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
  intro a _
  cases a with
  | none => exact mul_pos (sub_pos.mpr hθ1) hε₀
  | some a =>
      exact mul_pos (completedReflectionCoefficient_pos (by unfold modelOrder; omega)
        hβ1 hθ (by positivity) hB) (pow_pos (mul_pos hε₀ (hε a)) _)

/-- The finite floor is bounded by each particular actual branch term. -/
theorem completedDropFloor_le {p q : ℕ} (P : ConstrainedRegularization.Settings p q)
    (L β θ B ε₀ : ℝ) (ε : Fin q → ℝ) (a : Option (Fin q)) :
    completedDropFloor P L β θ B ε₀ ε ≤ completedDropTerm P L β θ B ε₀ ε a :=
  Finset.inf'_le _ (Finset.mem_univ a)

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
/-- Uniform initialized complete-inner cost from the actual merit start bound. -/
noncomputable def completedInnerBudget {p q : ℕ}
    (P : ConstrainedRegularization.Settings p q) (L β θ ε₀ : ℝ) (ε : Fin q → ℝ) : ℝ :=
  HighOrderRegularization.trialCountFactor P *
    (ε₀ ^ 2 / (2 * ConstrainedRegularization.commonDecreaseCoefficient P L
      (parameterCap P L) * ConstrainedRegularization.accuracyFactor P
        (completedInnerAccuracy β θ ε₀ ε)) + 1) +
          |HighOrderRegularization.trialCountOffset P L| + 1

/-- Legal absolute accuracies make the explicit initialized inner budget positive. -/
theorem completedInnerBudget_pos {p q : ℕ} (P : ConstrainedRegularization.Settings p q)
    {L β θ ε₀ : ℝ} {ε : Fin q → ℝ} (hL : 1 ≤ L) (hβ : 0 < β) (hθ : 0 < θ)
    (hε₀ : 0 < ε₀) (hε : ∀ a, 0 < ε a) : 0 < completedInnerBudget P L β θ ε₀ ε := by
  have hc := ConstrainedRegularization.commonDecreaseCoefficient_pos P hL
    (parameterCap_pos P L).le
  have ha := ConstrainedRegularization.accuracyFactor_pos P
    (fun a => show 0 < completedInnerAccuracy β θ ε₀ ε a by
      dsimp [completedInnerAccuracy]; exact mul_pos (mul_pos (mul_pos hβ hθ) hε₀) (hε a))
  have ht := zero_lt_one.trans_le (HighOrderRegularization.one_le_trialCountFactor P)
  unfold completedInnerBudget
  positivity

/-- Actual initialized objective calls, including every new inner initialization. -/
def completedFunctionEvaluations {q : ℕ} (D : CompletedData E q) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N, (D.length k + 1)

/-- Actual initialized derivative calls for each positive Taylor order. -/
noncomputable def completedDerivativeEvaluations {p q : ℕ}
    (P : ConstrainedRegularization.Settings p q) (D : CompletedData E q) (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range N,
    ((EvaluationComplexity.successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i}
      (D.length k)).card + 1)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Every actual successful trial is in its true prefix, so every initialized
per-order derivative schedule is bounded by the initialized function schedule. -/
theorem completedDerivativeEvaluations_le_functions {p q : ℕ}
    (P : ConstrainedRegularization.Settings p q) (D : CompletedData E q) (N : ℕ) :
    completedDerivativeEvaluations P D N ≤ completedFunctionEvaluations D N := by
  unfold completedDerivativeEvaluations completedFunctionEvaluations
  apply Finset.sum_le_sum
  intro k _
  apply Nat.add_le_add_right
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-- Fixed stronger regularity assumptions for the complete-inner repair.
Uniform merit bounds concern only the fixed admissible target interval. -/
structure CompletedRegularity (f : E → ℝ) (c : E → F) (X : Set E) (p q : ℕ)
    (L B flow fup : ℝ) : Prop where
  closed : IsClosed X
  convex : Convex ℝ X
  smooth_objective : ContDiff ℝ p f
  smooth_constraint : ContDiff ℝ p c
  one_le_constant : 1 ≤ L
  derivative_bound_pos : 0 < B
  objective_band : ∀ z ∈ X, ‖c z‖ ≤ 1 → flow ≤ f z ∧ f z ≤ fup
  objective_jets : ∀ i, 1 ≤ i → i ≤ q → ∀ z ∈ X, ‖iteratedFDeriv ℝ i f z‖ ≤ B
  merit_regularity : ∀ t ∈ Icc (flow - 1) fup, ContDiff ℝ p (targetMerit f c t) ∧
    ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
      ‖iteratedFDeriv ℝ i (targetMerit f c t) y -
        iteratedFDeriv ℝ i (targetMerit f c t) z‖ ≤ L * ‖y - z‖

namespace CompletedRun
variable {p q : ℕ} {f : E → ℝ} {c : E → F} {X : Set E}
  {P : ConstrainedRegularization.Settings p q} {β θ ε₀ L : ℝ} {ε : Fin q → ℝ}
  {D : CompletedData E q} {N : ℕ}

/-- Every continuing actual outer call spends a reset or completed-reflection
target decrease, derived from actual certificates and model radii. -/
theorem continuing_drop (h : CompletedRun f c X P β θ ε₀ L ε D N)
    (hX : IsClosed X) (hconv : Convex ℝ X) (hL : 1 ≤ L)
    (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c) {B flow fup : ℝ} (hB : 0 < B)
    (hfband : ∀ z ∈ X, ‖c z‖ ≤ 1 → flow ≤ f z ∧ f z ≤ fup)
    (hjet : ∀ i, 1 ≤ i → i ≤ q → ∀ z ∈ X, ‖iteratedFDeriv ℝ i f z‖ ≤ B)
    (hreg : ∀ t ∈ Icc (flow - 1) fup, ContDiff ℝ p (targetMerit f c t) ∧
      ∀ i, 1 ≤ i → i ≤ p → ∀ y z,
        ‖iteratedFDeriv ℝ i (targetMerit f c t) y -
          iteratedFDeriv ℝ i (targetMerit f c t) z‖ ≤ L * ‖y - z‖)
    {k : ℕ} (hk : k + 1 < N) :
    completedDropFloor P L β θ B ε₀ ε ≤ D.target k - D.target (k + 1) := by
  have hβ := h.margin_pos
  have hθ := h.theta_pos
  have hkN : k < N := by omega
  have hnot := h.continues k hk
  by_cases hr : ResetGuard true f c ε₀ θ (D.target k) (D.point (k + 1))
  · apply (completedDropFloor_le P L β θ B ε₀ ε none).trans
    rw [h.target_update k hkN, nextTarget, ite_eq_left hr]
    exact reset_decrease h.primal_pos.le h.theta_pos.le h.theta_lt_one.le hr.le
  · have hover : f (D.point (k + 1)) < D.target k := by
      by_contra hn
      exact hnot (Or.inl ⟨hr, not_lt.mp hn⟩)
    have hfail : ¬CompletedMeritTarget f c X ε
        (reflectTarget f (D.target k) (D.point (k + 1))) (D.point (k + 1))
        (completedRadius (targetMerit f c (D.target k)) X P
          (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k) L) := by
      intro hh
      apply hnot
      apply Or.inr
      rwa [nextTarget, ite_eq_right hr, ite_eq_left hover]
    simp only [CompletedMeritTarget, not_forall, not_le] at hfail
    obtain ⟨a, ha⟩ := hfail
    let δ := completedRadius (targetMerit f c (D.target k)) X P
      (completedInnerAccuracy β θ ε₀ ε) (D.inner k) (D.length k) L
    obtain ⟨hopt, hfloor⟩ := h.inner_certificate hX hconv hL hfband hreg hkN
    have hlegal := hopt.2.1 a
    have hδ0 : 0 < δ a := hlegal.1
    have hres : θ * ε₀ ≤ ‖residual f c (D.target k) (D.point (k + 1))‖ := by
      have hh : ¬‖residual f c (D.target k) (D.point (k + 1))‖ ≤ θ * ε₀ := by
        simpa only [ResetGuard, ite_true] using hr
      exact (lt_of_not_ge hh).le
    have hold : TaylorModel.constrainedCriticality (targetMerit f c (D.target k))
        (modelOrder a) X (D.point (k + 1)) (δ a) ≤
        β * (ε a * ‖residual f c (D.target k) (D.point (k + 1))‖ *
          δ a ^ modelOrder a / (modelOrder a).factorial) := by
      apply (hopt.2.2 a).trans
      have hh := mul_le_mul_of_nonneg_left hres
        (show 0 ≤ β * ε a * δ a ^ modelOrder a / (modelOrder a).factorial by
          have := h.margin_pos; have := h.dual_pos a; positivity)
      simp only [completedInnerAccuracy]
      convert hh using 1 <;> ring
    have hκ := (ConstrainedRegularization.radiusCoefficient_mem P hL
      (parameterCap_pos P L).le).1
    have haj : modelOrder a ≤ p := by have := P.order_le; unfold modelOrder; omega
    have hb := completed_reflection_target_drop (by unfold modelOrder; omega)
      (hf.contDiffAt.of_le (by exact_mod_cast haj))
      (hc.contDiffAt.of_le (by exact_mod_cast haj)) hX (h.mem (by omega))
      h.margin_lt_one h.theta_pos (by positivity) hB h.primal_pos (h.dual_pos a)
      hlegal.1 hlegal.2
      (show (ConstrainedRegularization.radiusCoefficient P L (parameterCap P L) * β * θ) *
          (ε₀ * ε a) ≤ δ a by
        simp only [completedInnerAccuracy] at hfloor
        convert hfloor a using 1; ring)
      (fun i hi hij => hjet i hi (hij.trans (by unfold modelOrder; omega)) _ (h.mem (by omega)))
      hover hres hold ha
    have hh := (completedDropFloor_le P L β θ B ε₀ ε (some a)).trans hb.le
    rw [h.target_update k hkN, nextTarget, ite_eq_right hr, ite_eq_left hover]
    exact hh

/-- The bounded true target range pays for every actual call, with exactly one
allowance for its final possibly terminal return. -/
theorem outer_iterations_le (h : CompletedRun f c X P β θ ε₀ L ε D N)
    {B flow fup : ℝ} (A : CompletedRegularity f c X p q L B flow fup) :
    (N : ℝ) ≤ (fup - flow + 1) / completedDropFloor P L β θ B ε₀ ε + 1 := by
  have hd := completedDropFloor_pos P A.one_le_constant h.margin_pos h.margin_lt_one
    h.theta_pos h.theta_lt_one A.derivative_bound_pos h.primal_pos h.dual_pos
  have hzero := h.target_bounds A.objective_band (k := 0) (Nat.zero_le N)
  have hgap : 0 ≤ fup - flow + 1 := by linarith
  cases N with
  | zero =>
      simp only [Nat.cast_zero]
      have hh := div_nonneg hgap hd.le
      linarith
  | succ n =>
      have hsum : (n : ℝ) * completedDropFloor P L β θ B ε₀ ε ≤
          D.target 0 - D.target n := by
        calc
          _ = ∑ _k ∈ Finset.range n, completedDropFloor P L β θ B ε₀ ε := by simp
          _ ≤ ∑ k ∈ Finset.range n, (D.target k - D.target (k + 1)) := by
            apply Finset.sum_le_sum
            intro k hk
            exact h.continuing_drop A.closed A.convex A.one_le_constant
              A.smooth_objective A.smooth_constraint A.derivative_bound_pos A.objective_band
              A.objective_jets A.merit_regularity (by have := Finset.mem_range.mp hk; omega)
          _ = _ := Finset.sum_range_sub' D.target n
      have hn := h.target_bounds A.objective_band (k := n) (by omega)
      have hb : (n : ℝ) ≤ (fup - flow + 1) / completedDropFloor P L β θ B ε₀ ε := by
        apply (le_div_iff₀ hd).mpr
        linarith
      push_cast
      linarith

/-- Every genuine completed inner first-target execution has the fixed
initialized cost supplied by its actual merit and all-order run budget. -/
theorem inner_iterations_le (h : CompletedRun f c X P β θ ε₀ L ε D N)
    {B flow fup : ℝ} (A : CompletedRegularity f c X p q L B flow fup)
    {k : ℕ} (hk : k < N) :
    ((D.length k + 1 : ℕ) : ℝ) ≤ completedInnerBudget P L β θ ε₀ ε := by
  have hr := h.inner_run k hk
  obtain ⟨hsm, hlip⟩ := A.merit_regularity (D.target k) (h.target_bounds A.objective_band hk.le)
  have hlow : ∀ z ∈ X, (0 : ℝ) ≤ targetMerit f c (D.target k) z := by
    intro z _
    unfold targetMerit
    positivity
  have ht := hr.iterations_le A.closed hsm A.one_le_constant hlip hlow (h.inner_first k hk)
  rw [h.inner_start k hk, sub_zero] at ht
  have hres := (h.invariants hk.le).2
  have hmerit : targetMerit f c (D.target k) (D.point k) ≤ ε₀ ^ 2 / 2 := by
    rw [targetMerit_eq_residual]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hres 2) (by norm_num)
  have hc := ConstrainedRegularization.commonDecreaseCoefficient_pos P A.one_le_constant
    (parameterCap_pos P L).le
  have ha := ConstrainedRegularization.accuracyFactor_pos P hr.accuracy_pos
  have hden : 0 < ConstrainedRegularization.commonDecreaseCoefficient P L (parameterCap P L) *
      ConstrainedRegularization.accuracyFactor P (completedInnerAccuracy β θ ε₀ ε) :=
    mul_pos hc ha
  have hfrac := div_le_div_of_nonneg_right hmerit hden.le
  rw [div_div] at hfrac
  have hfac := HighOrderRegularization.one_le_trialCountFactor P
  unfold completedInnerBudget
  have hh := mul_le_mul_of_nonneg_left (add_le_add_right hfrac 1)
    (zero_le_one.trans hfac)
  push_cast
  have hoff := le_abs_self (HighOrderRegularization.trialCountOffset P L)
  simp only [mul_assoc] at ht hh ⊢
  nlinarith only [ht, hh, hoff]

/-- Summing actual initialized inner schedules gives the explicit outer times
inner product bound, including all terminal and per-call initialization costs. -/
theorem total_inner_evaluations_le (h : CompletedRun f c X P β θ ε₀ L ε D N)
    {B flow fup : ℝ} (A : CompletedRegularity f c X p q L B flow fup) :
    (completedFunctionEvaluations D N : ℝ) ≤
      ((fup - flow + 1) / completedDropFloor P L β θ B ε₀ ε + 1) *
        completedInnerBudget P L β θ ε₀ ε ∧
    (completedDerivativeEvaluations P D N : ℝ) ≤
      ((fup - flow + 1) / completedDropFloor P L β θ B ε₀ ε + 1) *
        completedInnerBudget P L β θ ε₀ ε := by
  have hsum : (completedFunctionEvaluations D N : ℝ) ≤
      (N : ℝ) * completedInnerBudget P L β θ ε₀ ε := by
    unfold completedFunctionEvaluations
    push_cast
    calc
      _ ≤ ∑ k ∈ Finset.range N, completedInnerBudget P L β θ ε₀ ε := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [Nat.cast_add, Nat.cast_one] using h.inner_iterations_le A
          (Finset.mem_range.mp hk)
      _ = _ := by simp
  have hpos := completedInnerBudget_pos P A.one_le_constant h.margin_pos h.theta_pos
    h.primal_pos h.dual_pos
  have hb := hsum.trans (mul_le_mul_of_nonneg_right (h.outer_iterations_le A) hpos.le)
  refine ⟨hb, ?_⟩
  have hd : (completedDerivativeEvaluations P D N : ℝ) ≤ completedFunctionEvaluations D N := by
    exact_mod_cast completedDerivativeEvaluations_le_functions P D N
  exact hd.trans hb

end CompletedRun

/-- Consistent genuine completed-inner prefixes reach their first actual
outer stopping return, with the explicit target-range budget. -/
theorem exists_completed_stop {p q : ℕ} {f : E → ℝ} {c : E → F} {X : Set E}
    {P : ConstrainedRegularization.Settings p q} {β θ ε₀ L B flow fup : ℝ}
    {ε : Fin q → ℝ} {D : CompletedData E q}
    (A : CompletedRegularity f c X p q L B flow fup)
    (hprefix : ∀ N, (∀ k, k + 1 < N → ¬CompletedStopAfter f c X P β θ ε₀ L ε D k) →
      CompletedRun f c X P β θ ε₀ L ε D N) :
    ∃ k, CompletedStopAfter f c X P β θ ε₀ L ε D k ∧
      (∀ i < k, ¬CompletedStopAfter f c X P β θ ε₀ L ε D i) ∧
      CompletedRun f c X P β θ ε₀ L ε D (k + 1) ∧
      ((k + 1 : ℕ) : ℝ) ≤ (fup - flow + 1) / completedDropFloor P L β θ B ε₀ ε + 1 := by
  classical
  have hex : ∃ k, CompletedStopAfter f c X P β θ ε₀ L ε D k := by
    by_contra hn
    push Not at hn
    obtain ⟨N, hN⟩ := exists_nat_gt
      ((fup - flow + 1) / completedDropFloor P L β θ B ε₀ ε + 1)
    have h := hprefix N (fun k _ => hn k)
    exact (not_le_of_gt hN) (h.outer_iterations_le A)
  let k := Nat.find hex
  have hfirst : ∀ i < k, ¬CompletedStopAfter f c X P β θ ε₀ L ε D i :=
    fun i hi => Nat.find_min hex hi
  have hrun := hprefix (k + 1) (fun i hi => hfirst i (by omega))
  exact ⟨k, Nat.find_spec hex, hfirst, hrun, hrun.outer_iterations_le A⟩

end Constrained.TwoPhase
