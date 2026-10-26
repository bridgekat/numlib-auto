import Numlib.Optimization.Constrained.TwoPhase.CoarseCounting

/-!
# Complete coarser budgets for the closed-reset two-phase target method

Good accepted endpoints spend merit, resets spend primal target decrease,
and small-check reflections spend a dual/primal target decrease. Their explicit
budgets give finite outer termination and every initialized inner oracle count.
The extra reflection term is inverse-linear in both independent accuracies.
-/

namespace Constrained.TwoPhase
open Set TaylorModel EvaluationComplexity

/-- Exact algebraic reset, reflection, good-trial and initialized oracle budgets. -/
structure CoarseBudgets where
  resets : ℝ
  reflections : ℝ
  good : ℝ
  calls : ℝ
  functions : ℝ
  derivatives : ℝ

/-- Fixed settings and regularity constants give the corrected explicit
accuracy budgets. Resets cost `(1-theta)*epsilon0`, reflections cost
`(1-beta)*epsilon1*theta*epsilon0/B`, and good trials consume their true
fractional model-error decrease. -/
noncomputable def coarseBudgets {p : ℕ} (P : ConvexRegularization.Settings p)
    (L B β θ W ε₀ ε₁ : ℝ) : CoarseBudgets :=
  let R := W / ((1 - θ) * ε₀)
  let Q := W / ((1 - β) * ε₁ * θ * ε₀ / B)
  let d := ConvexRegularization.fractionalDecreaseCoefficient P L β *
    (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p)
  let G := ε₀ ^ 2 / 2 * (R + 1) / d
  let M := G + R + Q + 1
  let A := 1 + |Real.log P.gamma1| / Real.log P.gamma2
  let C := |Real.log (ConvexRegularization.parameterCap P L / P.sigmaInitial) /
    Real.log P.gamma2|
  ⟨R, Q, G, M, A * G + (A + C + 1) * M, G + 2 * M⟩

/-- The reset budget is the actual global target range divided by the reset drop. -/
@[simp]
theorem coarseBudgets_resets {p : ℕ} (P : ConvexRegularization.Settings p)
    (L B β θ W ε₀ ε₁ : ℝ) :
    (coarseBudgets P L B β θ W ε₀ ε₁).resets = W / ((1 - θ) * ε₀) := rfl

/-- The reflection budget divides by the proved small-check target drop. -/
@[simp]
theorem coarseBudgets_reflections {p : ℕ} (P : ConvexRegularization.Settings p)
    (L B β θ W ε₀ ε₁ : ℝ) :
    (coarseBudgets P L B β θ W ε₀ ε₁).reflections =
      W / ((1 - β) * ε₁ * θ * ε₀ / B) := rfl

/-- Initial merit and reset injections pay for all good accepted trials. -/
theorem coarseBudgets_good {p : ℕ} (P : ConvexRegularization.Settings p)
    (L B β θ W ε₀ ε₁ : ℝ) :
    let J := coarseBudgets P L B β θ W ε₀ ε₁
    J.good = ε₀ ^ 2 / 2 * (J.resets + 1) /
      (ConvexRegularization.fractionalDecreaseCoefficient P L β *
        (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p)) := rfl

/-- Calls are paid by good endpoints, resets, reflections and one final return. -/
theorem coarseBudgets_calls {p : ℕ} (P : ConvexRegularization.Settings p)
    (L B β θ W ε₀ ε₁ : ℝ) :
    let J := coarseBudgets P L B β θ W ε₀ ε₁
    J.calls = J.good + J.resets + J.reflections + 1 := rfl

/-- Function calls retain the actual update cost and every inner initialization. -/
theorem coarseBudgets_functions {p : ℕ} (P : ConvexRegularization.Settings p)
    (L B β θ W ε₀ ε₁ : ℝ) :
    let J := coarseBudgets P L B β θ W ε₀ ε₁
    let A := 1 + |Real.log P.gamma1| / Real.log P.gamma2
    J.functions = A * J.good +
      (A + |Real.log (ConvexRegularization.parameterCap P L / P.sigmaInitial) /
        Real.log P.gamma2| + 1) * J.calls := rfl

/-- Cached derivative schedules pay one extra accepted endpoint and one
initialization for each actual call. -/
theorem coarseBudgets_derivatives {p : ℕ} (P : ConvexRegularization.Settings p)
    (L B β θ W ε₀ ε₁ : ℝ) :
    let J := coarseBudgets P L B β θ W ε₀ ε₁
    J.derivatives = J.good + 2 * J.calls := rfl

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {p : ℕ} {f : E → ℝ} {c : E → F}
  {C S : Set E} {P : ConvexRegularization.Settings p} {ε₀ ε₁ θ β L : ℝ}
  {D : Data E} {N : ℕ}

/-- Actual finite corrected target-method prefixes obey all explicit call,
good-success and initialized function/derivative schedule budgets. No event
partition, reflection count or inner endpoint failure is assumed. -/
theorem PhaseTwoRun.coarse_budget (h : PhaseTwoRun true f c C P ε₀ ε₁ θ D N)
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hmu : ∀ k < N, ContDiffOn ℝ p (targetMerit f c (D.target k)) S) (hL : 0 < L)
    (hlip : ∀ k < N, ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c (D.target k)) y -
        iteratedFDeriv ℝ p (targetMerit f c (D.target k)) z‖ ≤ L * ‖y - z‖)
    (hβ : P.theta < β) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {B b flow fup : ℝ} (hB : 0 < B)
    (hf : ∀ x ∈ C, ContDiffAt ℝ 1 f x) (hc : ∀ x ∈ C, ContDiffAt ℝ 1 c x)
    (hDf : ∀ x ∈ C, ‖c x‖ ≤ 1 → ‖fderiv ℝ f x‖ ≤ B) (hb : ε₀ ≤ b)
    (hfb : ∀ x ∈ C, ‖c x‖ ≤ b → flow ≤ f x ∧ f x ≤ fup) :
    let J := coarseBudgets P L B β θ (fup - flow + 1) ε₀ ε₁
    (N : ℝ) ≤ J.calls ∧
      (∑ k ∈ Finset.range N,
        ((goodSuccesses P D f c C ε₀ ε₁ θ β k).card : ℝ)) ≤ J.good ∧
      (∑ k ∈ Finset.range N, ((D.length k + 1 : ℕ) : ℝ)) ≤ J.functions ∧
      (∑ k ∈ Finset.range N,
        (((successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card + 1 :
          ℕ) : ℝ)) ≤ J.derivatives := by
  let J := coarseBudgets P L B β θ (fup - flow + 1) ε₀ ε₁
  let G := ∑ k ∈ Finset.range N, ((goodSuccesses P D f c C ε₀ ε₁ θ β k).card : ℝ)
  let A := 1 + |Real.log P.gamma1| / Real.log P.gamma2
  let O := Real.log (ConvexRegularization.parameterCap P L / P.sigmaInitial) /
    Real.log P.gamma2
  have hA : 0 ≤ A := by
    have := Real.log_pos P.one_lt_gamma2
    dsimp [A]
    positivity
  have hCst : 0 ≤ A + |O| + 1 := by positivity
  have hd : 0 < ConvexRegularization.fractionalDecreaseCoefficient P L β *
      (ε₁ * θ * ε₀) ^ (((p + 1 : ℕ) : ℝ) / p) := by
    have := ConvexRegularization.fractionalDecreaseCoefficient_pos P hL hβ
    have := h.dual_pos
    have := h.theta_pos
    have := h.primal_pos
    positivity
  have hR : ((resetIterations true f c ε₀ θ D N).card : ℝ) ≤ J.resets := by
    have hh := h.card_resets_le hb hfb
    convert hh using 1; dsimp [J, coarseBudgets]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hQ : ((badReflections f c C ε₀ ε₁ θ β D N).card : ℝ) ≤ J.reflections :=
    h.bad_reflection_card_le hclosed hB hβ0 hβ1 hf hc hDf hb hfb
  have hG : G ≤ J.good := by
    apply (h.good_card_le hclosed hS hCS hC hmu hL hlip hβ).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hR le_rfl) (by positivity)) hd.le
  have hcall : (N : ℝ) ≤ J.calls := by
    have hh := h.calls_le_charges (β := β)
    have hh' : (N : ℝ) ≤ G + (resetIterations true f c ε₀ θ D N).card +
        (badReflections f c C ε₀ ε₁ θ β D N).card + 1 := by
      dsimp [G]
      exact_mod_cast hh
    change (N : ℝ) ≤ J.good + J.resets + J.reflections + 1
    linarith only [hh', hG, hR, hQ]
  have hsuccess : (∑ k ∈ Finset.range N,
      ((successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card : ℝ)) ≤
        G + N := by
    have hh : (∑ k ∈ Finset.range N,
        ((successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card : ℝ)) ≤
        ∑ k ∈ Finset.range N,
          (((goodSuccesses P D f c C ε₀ ε₁ θ β k).card : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      exact_mod_cast h.successful_card_le_good_add_one hβ1.le (Finset.mem_range.mp hk)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, G] using hh
  have hF : (∑ k ∈ Finset.range N, ((D.length k + 1 : ℕ) : ℝ)) ≤
      A * G + (A + |O| + 1) * N := by
    have ht : (∑ k ∈ Finset.range N, (D.length k : ℝ)) ≤
        (∑ k ∈ Finset.range N,
          ((successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card : ℝ)) *
            A + O * N := by
      calc
        _ ≤ ∑ k ∈ Finset.range N,
            (((successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card : ℝ) *
              A + O) := by
          apply Finset.sum_le_sum
          intro k hk
          exact h.inner_trials_le_successes (Finset.mem_range.mp hk) hS hCS hC
            (hmu k (Finset.mem_range.mp hk)) hL.le (hlip k (Finset.mem_range.mp hk))
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_mul]; simp; ring
    have hs := mul_le_mul_of_nonneg_right hsuccess hA
    have ho := mul_le_mul_of_nonneg_right (le_abs_self O) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    norm_num only [Nat.cast_add, Nat.cast_one] at *
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    nlinarith only [ht, hs, ho]
  have hD : (∑ k ∈ Finset.range N,
      (((successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card + 1 :
        ℕ) : ℝ)) ≤ G + 2 * N := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    linarith only [hsuccess]
  refine ⟨hcall, hG, ?_, ?_⟩
  · apply hF.trans
    change A * G + (A + |O| + 1) * N ≤ A * J.good + (A + |O| + 1) * J.calls
    exact add_le_add (mul_le_mul_of_nonneg_left hG hA)
      (mul_le_mul_of_nonneg_left hcall hCst)
  · apply hD.trans
    change G + 2 * N ≤ J.good + 2 * J.calls
    linarith only [hG, hcall]

end Constrained.TwoPhase

namespace Constrained.TwoPhase
open Set TaylorModel EvaluationComplexity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Consistent actual closed-reset target calls reach their first stopping
return within the full coarser oracle budgets and give the true infeasible or
Lagrangian alternative. Every inner call is the original interrupted execution. -/
theorem exists_phase_two_termination {p : ℕ} {f : E → ℝ} {c : E → F} {C S : Set E}
    (P : ConvexRegularization.Settings p) {ε₀ ε₁ θ β L B b flow fup : ℝ} {D : Data E}
    (hclosed : IsClosed C) (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hmu : ∀ t, ContDiffOn ℝ p (targetMerit f c t) S) (hL : 0 < L)
    (hlip : ∀ t ∈ Icc (flow - 1) fup, ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p (targetMerit f c t) y -
        iteratedFDeriv ℝ p (targetMerit f c t) z‖ ≤ L * ‖y - z‖)
    (hβ : P.theta < β) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hB : 0 < B)
    (hf : ∀ x ∈ C, ContDiffAt ℝ 1 f x) (hc : ∀ x ∈ C, ContDiffAt ℝ 1 c x)
    (hDf : ∀ x ∈ C, ‖c x‖ ≤ 1 → ‖fderiv ℝ f x‖ ≤ B) (hb : ε₀ ≤ b)
    (hfb : ∀ x ∈ C, ‖c x‖ ≤ b → flow ≤ f x ∧ f x ≤ fup)
    (hprefix : ∀ N, (∀ k < N,
        ¬StopAfter true f c C ε₀ ε₁ θ (D.target k) (D.point (k + 1))) →
      PhaseTwoRun true f c C P ε₀ ε₁ θ D (N + 1)) :
    let J := coarseBudgets P L B β θ (fup - flow + 1) ε₀ ε₁
    ∃ K, StopAfter true f c C ε₀ ε₁ θ (D.target K) (D.point (K + 1)) ∧
      PhaseTwoRun true f c C P ε₀ ε₁ θ D (K + 1) ∧
      (∀ k < K, ¬StopAfter true f c C ε₀ ε₁ θ (D.target k) (D.point (k + 1))) ∧
      ((K + 1 : ℕ) : ℝ) ≤ J.calls ∧
      (∑ k ∈ Finset.range (K + 1), ((D.length k + 1 : ℕ) : ℝ)) ≤ J.functions ∧
      (∑ k ∈ Finset.range (K + 1),
        (((successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card + 1 :
          ℕ) : ℝ)) ≤ J.derivatives ∧
      ((firstCriticality (fun x => ‖c x‖ ^ 2 / 2) C (D.point (K + 1)) ≤
          ε₁ * ‖c (D.point (K + 1))‖ ∧ θ * ε₀ < ‖c (D.point (K + 1))‖) ∨
        ∃ y : F, firstCriticality (vectorLagrangian f c y) C (D.point (K + 1)) ≤
          ε₁ * multiplierNorm y ∧ ‖c (D.point (K + 1))‖ ≤ ε₀) := by
  classical
  let J := coarseBudgets P L B β θ (fup - flow + 1) ε₀ ε₁
  have hbudget : ∀ N, PhaseTwoRun true f c C P ε₀ ε₁ θ D N →
      (N : ℝ) ≤ J.calls ∧
      (∑ k ∈ Finset.range N, ((D.length k + 1 : ℕ) : ℝ)) ≤ J.functions ∧
      (∑ k ∈ Finset.range N,
        (((successfulIterations {i | P.eta1 ≤ (D.inner k).ratio i} (D.length k)).card + 1 :
          ℕ) : ℝ)) ≤ J.derivatives := by
    intro N h
    have hh := h.coarse_budget hclosed hS hCS hC (fun k _ => hmu (D.target k)) hL
      (fun k hk => hlip (D.target k) (h.target_bounds hb hfb hk.le))
      hβ hβ0 hβ1 hB hf hc hDf hb hfb
    exact ⟨hh.1, hh.2.2.1, hh.2.2.2⟩
  have hex : ∃ K, StopAfter true f c C ε₀ ε₁ θ (D.target K) (D.point (K + 1)) := by
    by_contra hn
    push Not at hn
    obtain ⟨N, hN⟩ := exists_nat_gt J.calls
    have h := hprefix N (fun k _ => hn k)
    have hh := (hbudget (N + 1) h).1
    norm_num only [Nat.cast_add, Nat.cast_one] at hh
    linarith only [hh, hN]
  let K := Nat.find hex
  have hstop := Nat.find_spec hex
  have hfirst : ∀ k < K, ¬StopAfter true f c C ε₀ ε₁ θ (D.target k) (D.point (k + 1)) :=
    fun k hk => Nat.find_min hex hk
  have hr := hprefix K hfirst
  have hbnd := hbudget (K + 1) hr
  have hx := hr.mem (show K + 1 ≤ K + 1 by omega)
  have hout := CorrectedPhaseTwoRun.termination hr hclosed (show K < K + 1 by omega)
    ((hf _ hx).differentiableAt (by norm_num)) ((hc _ hx).differentiableAt (by norm_num)) hstop
  exact ⟨K, hstop, hr, hfirst, hbnd.1, hbnd.2.1, hbnd.2.2, hout⟩

end Constrained.TwoPhase
