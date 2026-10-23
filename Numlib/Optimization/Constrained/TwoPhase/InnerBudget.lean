import Numlib.Optimization.Constrained.TwoPhase.Uniform
import Numlib.Optimization.Regularization.Convex.FixedStep

/-!
# Actual nonterminal inner decreases in the two-phase target method

The ordinary fixed-tolerance inner method gives a uniform decrease at every
accepted endpoint before its return. A terminal reflection return is kept
separate because its old-target criticality may already satisfy the inner test.
-/

namespace Constrained.TwoPhase
open Set TaylorModel HighOrderRegularization EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] {p : ℕ} {closedReset : Bool} {f : E → ℝ} {c : E → F}
  {C S : Set E} {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ L : ℝ}
  {D : Data E} {N k : ℕ}

omit [ProperSpace E] in
/-- Every actual inner endpoint strictly before the return has residual above
the reset threshold and normalized criticality above the requested tolerance. -/
theorem PhaseTwoRun.inner_nonterminal_failure
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) (hk : k < N)
    {i : ℕ} (hi : i < D.length k) :
    θ * ε₀ < ‖residual f c (D.target k) ((D.inner k).point i)‖ ∧
      ε₁ * ‖residual f c (D.target k) ((D.inner k).point i)‖ <
        firstCriticality (targetMerit f c (D.target k)) C ((D.inner k).point i) := by
  have hh := h.inner_first k hk i hi
  constructor
  · exact lt_of_not_ge (fun hn => hh (Or.inl hn))
  · exact lt_of_not_ge (fun hn => hh (Or.inr (Or.inr hn)))

/-- The true fixed-tolerance ARp-CC decrease applies at every accepted endpoint
strictly before its caller's return, with constants independent of targets. -/
theorem PhaseTwoRun.inner_nonterminal_decrease
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) (hk : k < N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (targetMerit f c (D.target k)) S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c (D.target k)) y -
        iteratedFDeriv ℝ p (targetMerit f c (D.target k)) z‖ ≤ L * ‖y - z‖)
    {i : ℕ} (hi : i + 1 < D.length k) (hs : P.eta1 ≤ (D.inner k).ratio i) :
    ConvexRegularization.fixedDecreaseCoefficient P L *
        (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p) ≤
      targetMerit f c (D.target k) ((D.inner k).point i) -
        targetMerit f c (D.target k) ((D.inner k).point (i + 1)) := by
  have hε₀ := h.primal_pos
  have hε₁ := h.dual_pos
  have hθ := h.theta_pos
  have hp : (0 : ℝ) < p := by exact_mod_cast P.order_pos
  have hfail := h.inner_nonterminal_failure hk hi
  have hmul := mul_lt_mul_of_pos_left hfail.1 h.dual_pos
  have hlarge : ε₁ * θ * ε₀ ≤ constrainedCriticality
      (targetMerit f c (D.target k)) 1 C ((D.inner k).point (i + 1)) 1 := by
    change ε₁ * θ * ε₀ ≤ firstCriticality _ _ _
    nlinarith [hfail.2]
  have hh := (h.inner_run k hk).relative_successful_decrease
    hclosed hS hCS hC hf hL hlip (by omega) hs hlarge
  apply (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hlarge (by positivity))
    (ConvexRegularization.fixedDecreaseCoefficient_pos P hL).le).trans hh

/-- The genuine successful trials whose endpoints precede the inner return. -/
noncomputable def interiorSuccesses (P : ConvexRegularization.Settings p) (D : Data E)
    (k : ℕ) : Finset ℕ :=
  successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k - 1)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- An interior success is an actual accepted trial with a nonterminal endpoint. -/
@[simp] theorem mem_interiorSuccesses {i : ℕ} :
    i ∈ interiorSuccesses P D k ↔ i + 1 < D.length k ∧
      P.eta1 ≤ (D.inner k).ratio i := by
  simp only [interiorSuccesses, mem_successfulIterations, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hi, hs⟩
    exact ⟨by omega, hs⟩
  · rintro ⟨hi, hs⟩
    exact ⟨by omega, hs⟩

/-- The exact sum of true nonterminal accepted decreases is bounded by the
actual merit drop across the entire call. The terminal trial is uncharged. -/
theorem PhaseTwoRun.inner_interior_budget
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) (hk : k < N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (targetMerit f c (D.target k)) S) (hL : 0 < L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c (D.target k)) y -
        iteratedFDeriv ℝ p (targetMerit f c (D.target k)) z‖ ≤ L * ‖y - z‖) :
    (interiorSuccesses P D k).card *
        (ConvexRegularization.fixedDecreaseCoefficient P L *
          (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p)) ≤
      targetMerit f c (D.target k) (D.point k) -
        targetMerit f c (D.target k) (D.point (k + 1)) := by
  classical
  let F := fun i => targetMerit f c (D.target k) ((D.inner k).point i)
  calc
    _ = ∑ _i ∈ interiorSuccesses P D k,
        ConvexRegularization.fixedDecreaseCoefficient P L *
          (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p) := by simp
    _ ≤ ∑ i ∈ interiorSuccesses P D k, (F i - F (i + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hi, hs⟩ := mem_interiorSuccesses.mp hi
      exact h.inner_nonterminal_decrease hk hclosed hS hCS hC hf hL hlip hi hs
    _ ≤ ∑ i ∈ Finset.range (D.length k), (F i - F (i + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        have hh := (mem_interiorSuccesses.mp hi).1
        exact Finset.mem_range.mpr (by omega)
      · intro i hi _
        exact sub_nonneg.mpr ((h.inner_run k hk).objective_succ_le
          (Finset.mem_range.mp hi))
    _ = F 0 - F (D.length k) := Finset.sum_range_sub' F (D.length k)
    _ = _ := by rw [show F 0 = targetMerit f c (D.target k) (D.point k) by
                      dsimp [F]; rw [h.inner_start k hk],
                    show F (D.length k) =
                      targetMerit f c (D.target k) (D.point (k + 1)) by
                      dsimp [F]; rw [h.inner_end k hk]]

omit [ProperSpace E] in
/-- Exact reflection preserves the actual merit at its returned point, without
assuming any old-target criticality failure at that return. -/
theorem PhaseTwoRun.reflection_merit
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) (hk : k < N)
    (hr : ¬ResetGuard closedReset f c ε₀ θ (D.target k) (D.point (k + 1)))
    (hover : f (D.point (k + 1)) < D.target k) :
    targetMerit f c (D.target k) (D.point (k + 1)) =
      targetMerit f c (D.target (k + 1)) (D.point (k + 1)) := by
  rw [targetMerit_eq_residual, targetMerit_eq_residual]
  rw [(h.reflection_residual hk hr hover).1]

/-- Genuine nonterminal inner successes telescope across a whole reflection
block. The returned endpoints remain separate, uncharged events. -/
theorem PhaseTwoRun.reflection_interior_budget
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ∀ j < N, ContDiffOn ℝ p (targetMerit f c (D.target j)) S) (hL : 0 < L)
    (hlip : ∀ j < N, ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c (D.target j)) y -
        iteratedFDeriv ℝ p (targetMerit f c (D.target j)) z‖ ≤ L * ‖y - z‖)
    {a m : ℕ} (ham : a + m ≤ N)
    (hreflect : ∀ j < m,
      ¬ResetGuard closedReset f c ε₀ θ (D.target (a + j)) (D.point (a + j + 1)) ∧
        f (D.point (a + j + 1)) < D.target (a + j)) :
    (∑ j ∈ Finset.range m, ((interiorSuccesses P D (a + j)).card : ℝ)) *
        (ConvexRegularization.fixedDecreaseCoefficient P L *
          (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p)) ≤
      (1 - θ) * ε₀ ^ 2 := by
  classical
  let F := fun j => targetMerit f c (D.target (a + j)) (D.point (a + j))
  have hb : (∑ j ∈ Finset.range m, ((interiorSuccesses P D (a + j)).card : ℝ)) *
      (ConvexRegularization.fixedDecreaseCoefficient P L *
        (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p)) ≤ F 0 - F m := by
    calc
      _ = ∑ j ∈ Finset.range m, ((interiorSuccesses P D (a + j)).card : ℝ) *
          (ConvexRegularization.fixedDecreaseCoefficient P L *
            (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p)) := Finset.sum_mul _ _ _
      _ ≤ ∑ j ∈ Finset.range m, (F j - F (j + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjm := Finset.mem_range.mp hj
        have hjN : a + j < N := by omega
        have hh := h.inner_interior_budget hjN hclosed hS hCS hC (hf _ hjN)
          hL (hlip _ hjN)
        rw [h.reflection_merit hjN (hreflect j hjm).1 (hreflect j hjm).2] at hh
        simpa only [F, Nat.add_assoc] using hh
      _ = F 0 - F m := Finset.sum_range_sub' F m
  cases m with
  | zero => simpa using mul_nonneg (sub_nonneg.mpr h.theta_lt_one.le) (sq_nonneg ε₀)
  | succ m =>
    have hlastN : a + m < N := by omega
    have hn : θ * ε₀ ≤ ‖residual f c (D.target (a + m + 1)) (D.point (a + m + 1))‖ := by
      have hr := (hreflect m (by omega)).1
      have hn : θ * ε₀ ≤ ‖residual f c (D.target (a + m)) (D.point (a + m + 1))‖ := by
        cases closedReset <;> simp only [ResetGuard, Bool.false_eq_true, ite_false, ite_true] at hr
        · exact not_lt.mp hr
        · exact (not_le.mp hr).le
      rw [(h.reflection_residual hlastN (hreflect m (by omega)).1
        (hreflect m (by omega)).2).1]
      exact hn
    have hstart := (h.invariants (show a ≤ N by omega)).2
    have hθ := h.theta_pos
    have hθ1 := h.theta_lt_one
    have hε₀ := h.primal_pos
    have hstart2 := pow_le_pow_left₀ (norm_nonneg _) hstart 2
    have hend2 := pow_le_pow_left₀ (mul_nonneg hθ.le hε₀.le) hn 2
    have htarget : F 0 - F (m + 1) ≤ (1 - θ) * ε₀ ^ 2 := by
      dsimp only [F]
      rw [targetMerit_eq_residual, targetMerit_eq_residual]
      simp only [Nat.add_zero, Nat.add_assoc] at *
      have hθsq := mul_nonneg (sq_nonneg ε₀) (sq_nonneg (1 - θ))
      nlinarith
    exact hb.trans htarget

/-- Exact conversion of a squared residual budget into the separated primal
and dual accuracy powers, with no relation assumed between the accuracies. -/
theorem squared_accuracy_budget_eq {c θ ε₀ ε₁ a b : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) (hab : a + b = 2) :
    (1 - θ) * ε₀ ^ 2 / (c * (ε₁ * θ * ε₀) ^ a) =
      (c * θ ^ a)⁻¹ * (1 - θ) * ε₀ ^ b * ε₁ ^ (-a) := by
  have h0 := (Real.rpow_pos_of_pos hε₀ a).ne'
  have h1 := (Real.rpow_pos_of_pos hε₁ a).ne'
  have hT := (Real.rpow_pos_of_pos hθ a).ne'
  have he : ε₀ ^ 2=ε₀ ^ a * ε₀ ^ b := by
    rw [←Real.rpow_add hε₀, hab]
    norm_num
  rw [he, Real.mul_rpow (mul_nonneg hε₁.le hθ.le) hε₀.le,
    Real.mul_rpow hε₁.le hθ.le, Real.rpow_neg hε₁.le]
  field_simp
/-- The successful interior endpoints of an actual reflection block obey the
source primal and dual powers. Terminal reflection returns are excluded. -/
theorem PhaseTwoRun.reflection_interior_card_le
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ∀ j < N, ContDiffOn ℝ p (targetMerit f c (D.target j)) S) (hL : 0 < L)
    (hlip : ∀ j < N, ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c (D.target j)) y -
        iteratedFDeriv ℝ p (targetMerit f c (D.target j)) z‖ ≤ L * ‖y - z‖)
    {a m : ℕ} (ham : a + m ≤ N)
    (hreflect : ∀ j < m,
      ¬ResetGuard closedReset f c ε₀ θ (D.target (a + j)) (D.point (a + j + 1)) ∧
        f (D.point (a + j + 1)) < D.target (a + j)) :
    (∑ j ∈ Finset.range m, ((interiorSuccesses P D (a + j)).card : ℝ)) ≤
      (ConvexRegularization.fixedDecreaseCoefficient P L *
          θ ^ (((p + 1 : ℕ) : ℝ) / p))⁻¹ * (1 - θ) *
        ε₀ ^ (((p : ℝ) - 1) / p) * ε₁ ^ (-(((p + 1 : ℕ) : ℝ) / p)) := by
  have hb := h.reflection_interior_budget hclosed hS hCS hC hf hL hlip ham hreflect
  have hc := ConvexRegularization.fixedDecreaseCoefficient_pos P hL
  have hε₀ := h.primal_pos
  have hε₁ := h.dual_pos
  have hθ := h.theta_pos
  have hp : (0 : ℝ) < p := by exact_mod_cast P.order_pos
  have hd : 0 < ConvexRegularization.fixedDecreaseCoefficient P L *
      (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p) := by positivity
  have hh := (le_div_iff₀ hd).mpr hb
  have hab : (((p + 1 : ℕ) : ℝ) / p) + (((p : ℝ) - 1) / p) = 2 := by
    push_cast
    field_simp
    ring
  rwa [squared_accuracy_budget_eq hc hθ hε₀ hε₁ hab] at hh

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- At most one genuine successful trial per call has a terminal endpoint. -/
theorem successful_card_le_interior_add_one (P : ConvexRegularization.Settings p)
    (D : Data E) (k : ℕ) :
    (successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card ≤
      (interiorSuccesses P D k).card + 1 := by
  generalize hn : D.length k=n
  cases n with
  | zero => simp only [successfulIterations, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty];omega
  | succ n =>
    have hh := card_successful_succ_le {i | P.eta1 ≤ (D.inner k).ratio i} n
    simpa only [interiorSuccesses, hn, Nat.add_sub_cancel] using hh

omit [ProperSpace E] in
/-- Actual parameter-update intervals bound all inner trials by the counted
nonterminal successes plus one explicit terminal-success charge per call. -/
theorem PhaseTwoRun.inner_trials_le_interior
    (h : PhaseTwoRun closedReset f c C P ε₀ ε₁ θ D N) (hk : k < N)
    (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p (targetMerit f c (D.target k)) S) (hL : 0 ≤ L)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c (D.target k)) y -
        iteratedFDeriv ℝ p (targetMerit f c (D.target k)) z‖ ≤ L * ‖y - z‖) :
    (D.length k : ℝ) ≤ ((interiorSuccesses P D k).card + 1) *
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
  rw [hin.initial_parameter] at ht
  have hA : 0 ≤ 1 + |Real.log P.gamma1| / Real.log P.gamma2 := by
    have := Real.log_pos P.one_lt_gamma2
    positivity
  have hc : ((successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i}
      (D.length k)).card : ℝ) ≤ (interiorSuccesses P D k).card + 1 := by
    exact_mod_cast successful_card_le_interior_add_one P D k
  exact ht.trans (add_le_add (mul_le_mul_of_nonneg_right hc hA) le_rfl)

end Constrained.TwoPhase
