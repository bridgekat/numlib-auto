import Numlib.Optimization.Regularization.Convex.DerivativeBudget

/-!
# Full constrained third-order regularization complexity

Actual successful trials consume the common positive objective budget. Actual
parameter intervals then control rejected trials and force the first literal
stop. Fixed constants precede every accuracy and execution, and the derivative
schedules explicitly retain initialization and all enabled terminal tests.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization EvaluationComplexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual derivative sites include all enabled terminal tests; higher jets
are computed only at nonterminal sites where the next model requires them. -/
noncomputable def derivativeEvaluationNodesForOrder {p : ℕ} {q : Fin 3}
    (P : DerivativeSettings p q) (D : Data E) (N j : ℕ) : Finset ℕ := by
  classical
  exact if j ≤ q.val + 1 then derivativeEvaluationNodes P.toSettings D N
    else (derivativeEvaluationNodes P.toSettings D N).filter (fun i => i < N)

/-- The cardinality of the actual enabled-order derivative schedule. -/
noncomputable def derivativeEvaluationsForOrder {p : ℕ} {q : Fin 3}
    (P : DerivativeSettings p q) (D : Data E) (N j : ℕ) : ℕ :=
  (derivativeEvaluationNodesForOrder P D N j).card

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- All actual derivative schedules fit inside the initialized accepted-site schedule. -/
theorem derivativeEvaluationsForOrder_le {p : ℕ} {q : Fin 3}
    (P : DerivativeSettings p q) (D : Data E) (N j : ℕ) :
    derivativeEvaluationsForOrder P D N j ≤ derivativeEvaluations P.toSettings D N := by
  classical
  unfold derivativeEvaluationsForOrder derivativeEvaluationNodesForOrder derivativeEvaluations
  split_ifs
  · exact le_rfl
  · exact Finset.card_filter_le _ _

variable {p : ℕ} {f : E → ℝ} {C S : Set E} {P : DerivativeSettings p 2}
  {ε : Fin 3 → ℝ} {D : Data E} {N : ℕ} {L flow : ℝ}

/-- Actual constrained traces obey the uniform parameter cap on the source domain. -/
theorem DerivativeRun.parameter_le (h : DerivativeRun f C P ε D N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i ≤ N) : D.parameter i ≤ parameterCap P.toSettings L := by
  have hh := h.modelTrace.parameter_le_on hS hCS hC hf hL hlip
    (fun k hk => h.mem hk.le) h.feasible_trial hi
  simpa only [parameterCap,h.initial_parameter] using hh

/-- At most one terminal accepted endpoint escapes the nontermination budget. -/
theorem DerivativeRun.successful_card_le (h : DerivativeRun f C P ε D N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y ∈ C, flow ≤ f y) :
    ((successfulIterations {i | P.eta1 ≤ D.ratio i} N).card : ℝ) ≤
      (f (D.point 0) - flow) /
        (derivativeBudgetCoefficient P L * finiteAccuracyFactor p (ε 0) (ε 1) (ε 2)) + 1 := by
  have hgap : 0 ≤ f (D.point 0) - flow := sub_nonneg.mpr (hlow _ h.initial_mem)
  have hd : 0 < derivativeBudgetCoefficient P L * finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) :=
    mul_pos (derivativeBudgetCoefficient_pos P hL) h.accuracy_factor_pos
  cases N with
  | zero => simp only [successfulIterations,Finset.range_zero,Finset.filter_empty,
      Finset.card_empty,Nat.cast_zero]; positivity
  | succ k =>
    have hc := card_successful_le_gap_div
      (S := {i | P.eta1 ≤ D.ratio i}) (f := fun i => f (D.point i)) hd
      (hlow _ (h.mem (show k ≤ k + 1 by omega)))
      (fun i hi hs => h.nonterminal_decrease hS hCS hC hf hL hlip (by omega) hs)
      (fun i hi hs => by rw [h.rejected (by omega) hs])
    have hs : ((successfulIterations {i | P.eta1 ≤ D.ratio i} (k + 1)).card : ℝ) ≤
        (successfulIterations {i | P.eta1 ≤ D.ratio i} k).card + 1 := by
      exact_mod_cast card_successful_succ_le {i | P.eta1 ≤ D.ratio i} k
    exact hs.trans (add_le_add hc le_rfl)

/-- The actual parameter updates bound all trials by the genuine success budget. -/
theorem DerivativeRun.iterations_le (h : DerivativeRun f C P ε D N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S)
    (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y ∈ C, flow ≤ f y) :
    (N : ℝ) ≤ ((f (D.point 0) - flow) /
      (derivativeBudgetCoefficient P L * finiteAccuracyFactor p (ε 0) (ε 1) (ε 2)) + 1) *
        (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (parameterCap P.toSettings L / P.sigmaInitial) / Real.log P.gamma2 := by
  have ht := iteration_bound_of_parameter_upper
    (S := {i | P.eta1 ≤ D.ratio i}) (fun _ hi => h.modelTrace.updates.pos hi)
    P.gamma1_pos P.gamma1_lt_one P.one_lt_gamma2 (h.parameter_le hS hCS hC hf hL hlip
      le_rfl) (fun _ hi hs => h.modelTrace.updates.successful_ge hi hs)
    (fun _ hi hs => h.modelTrace.updates.unsuccessful_ge hi hs)
  rw [h.initial_parameter] at ht
  have hA : 0 ≤ 1 + |Real.log P.gamma1| / Real.log P.gamma2 := by
    have := Real.log_pos P.one_lt_gamma2
    positivity
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_right (h.successful_card_le hS hCS hC hf hL hlip hlow) hA) le_rfl)

/-- Consistent primitive prefixes reach the first literal constrained derivative stop. -/
theorem exists_derivative_termination (hS : IsOpen S) (hCS : C ⊆ S)
    (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y ∈ C, flow ≤ f y)
    (hprefix : ∀ N, (∀ i < N, ¬derivativeStop f C P ε (D.point i)) →
      DerivativeRun f C P ε D N) :
    ∃ K, derivativeStop f C P ε (D.point K) ∧ DerivativeRun f C P ε D K ∧
      ∀ i < K, ¬derivativeStop f C P ε (D.point i) := by
  classical
  have hex : ∃ K, derivativeStop f C P ε (D.point K) := by
    by_contra hn
    have hnon : ∀ i, ¬derivativeStop f C P ε (D.point i) := not_exists.mp hn
    let bound := ((f (D.point 0) - flow) /
      (derivativeBudgetCoefficient P L * finiteAccuracyFactor p (ε 0) (ε 1) (ε 2)) + 1) *
        (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (parameterCap P.toSettings L / P.sigmaInitial) / Real.log P.gamma2
    obtain ⟨N,hN⟩ := exists_nat_gt bound
    exact (not_le_of_gt hN)
      ((hprefix N (fun i _ => hnon i)).iterations_le hS hCS hC hf hL hlip hlow)
  have hnon : ∀ i < Nat.find hex, ¬derivativeStop f C P ε (D.point i) :=
    fun i hi => Nat.find_min hex hi
  exact ⟨Nat.find hex,Nat.find_spec hex,hprefix _ hnon,hnon⟩

/-- Fixed positive constants precede every accuracy request and actual
constrained execution. The first true third-order stop and all initialized
objective and per-order derivative counts have the source accuracy powers,
with an explicit two-site derivative overhead. -/
theorem exists_uniform_derivative_complexity {f : E → ℝ} {C S : Set E} {p : ℕ}
    (P : DerivativeSettings p 2) (hS : IsOpen S) (hCS : C ⊆ S)
    (hC : Convex ℝ C) (hf : ContDiffOn ℝ p f S) {L flow : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    (hlow : ∀ y ∈ C, flow ≤ f y) :
    ∃ κS > 0, ∃ κA > 0, ∃ κC > 0, ∀ (ε : Fin 3 → ℝ) (D : Data E),
      (∀ N, (∀ i < N, ¬derivativeStop f C P ε (D.point i)) →
        DerivativeRun f C P ε D N) →
      ∃ K, derivativeStop f C P ε (D.point K) ∧ DerivativeRun f C P ε D K ∧
        (∀ i < K, ¬derivativeStop f C P ε (D.point i)) ∧
        (functionEvaluations K : ℝ) ≤ κA * (f (D.point 0) - flow) /
          finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) + κC ∧
        (derivativeEvaluations P.toSettings D K : ℝ) ≤ κS * (f (D.point 0) - flow) /
          finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) + 2 ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ p →
          (derivativeEvaluationsForOrder P D K j : ℝ) ≤ κS * (f (D.point 0) - flow) /
            finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) + 2 := by
  let c := derivativeBudgetCoefficient P L
  let A := 1 + |Real.log P.gamma1| / Real.log P.gamma2
  let B := Real.log (parameterCap P.toSettings L / P.sigmaInitial) / Real.log P.gamma2
  have hc : 0 < c := derivativeBudgetCoefficient_pos P hL
  have hA : 0 < A := by have := Real.log_pos P.one_lt_gamma2; dsimp [A]; positivity
  have hratio : 1 ≤ parameterCap P.toSettings L / P.sigmaInitial := by
    apply (le_div_iff₀ (P.sigmaMin_pos.trans_le P.sigmaMin_le_initial)).mpr
    simpa only [one_mul,parameterCap] using
      le_max_left P.sigmaInitial (P.gamma3 * L / (1 - P.eta2))
  have hB : 0 ≤ B := div_nonneg (Real.log_nonneg hratio)
    (Real.log_pos P.one_lt_gamma2).le
  refine ⟨1 / c,by positivity,(1 / c) * A,by positivity,A + B + 1,by positivity,?_⟩
  intro ε D hprefix
  obtain ⟨K,hstop,hK,hfirst⟩ := exists_derivative_termination
    hS hCS hC hf hL hlip hlow hprefix
  have hF := hK.iterations_le hS hCS hC hf hL hlip hlow
  have hD := hK.successful_card_le hS hCS hC hf hL hlip hlow
  refine ⟨K,hstop,hK,hfirst,?_,?_,?_⟩
  · simp only [functionEvaluations,Nat.cast_add,Nat.cast_one]
    convert add_le_add hF (le_refl (1 : ℝ)) using 1
    dsimp [c,A,B]
    ring
  · rw [derivativeEvaluations_eq,Nat.cast_add,Nat.cast_one]
    convert add_le_add hD (le_refl (1 : ℝ)) using 1
    dsimp [c]
    ring
  · intro j hj hjp
    have hb : (derivativeEvaluations P.toSettings D K : ℝ) ≤
        (1 / c) * (f (D.point 0) - flow) / finiteAccuracyFactor p (ε 0) (ε 1) (ε 2) + 2 := by
      rw [derivativeEvaluations_eq,Nat.cast_add,Nat.cast_one]
      convert add_le_add hD (le_refl (1 : ℝ)) using 1
      dsimp [c]
      ring
    exact (Nat.cast_le.mpr (derivativeEvaluationsForOrder_le P D K j)).trans hb

end ConvexRegularization
