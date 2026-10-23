import Numlib.Optimization.EvaluationComplexity.Density
import Numlib.Optimization.MeasureDomination.Regularization
import Numlib.Analysis.SpecialFunctions.Pow.GeometricBudget

/-!
# Uniform logarithmic complexity at equal domination exponents

An actual small gap yields a small measure after one further accepted step.
Explicit ceiling-log budgets and source density give all initialized counts,
with constants fixed before every positive accuracy.
-/

open Set Filter Topology
namespace MeasureDomination
variable {E : Type*} {f ψ : E → ℝ} {fstar μ κψ ν κν κR κA : ℝ}
  {x : ℕ → E} {S : Set ℕ}

/-- Any explicit comparison-orbit budget bounds the first actual gap target. -/
theorem ARRun.first_gap_budget (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) {ε : ℝ} (hε : 0 < ε) {M : ℕ}
    (hM : ImplicitGap.orbit (κν / κψ ^ (ν / μ)) (ν / μ) (gap f fstar (x 0)) M ≤ ε) :
    ∃ K : ℕ, gap f fstar (x K) ≤ ε ∧ (∀ k < K, ε < gap f fstar (x k)) ∧
      (EvaluationComplexity.successfulIterations S K).card ≤ M ∧
      (K : ℝ) ≤ κR * M + κA := by
  obtain ⟨K, hs, hmin, _, hc, hK, _, _⟩ := hr.first_gap_hitting hd hε
  have hT := ImplicitGap.hittingTime_le
    (div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _))
    (div_pos (zero_lt_one.trans_le hr.exponent_ge_one) (zero_lt_one.trans_le hd.level_ge_one))
    (hd.gap_nonneg (x 0)) hε hM
  refine ⟨K, hs, hmin, hc.trans hT, hK.trans ?_⟩
  have hTR : (ImplicitGap.hittingTime (κν / κψ ^ (ν / μ)) (ν / μ)
      (gap f fstar (x 0)) ε : ℝ) ≤ M := by exact_mod_cast hT
  exact add_le_add (mul_le_mul_of_nonneg_left hTR
    (zero_le_one.trans hr.density_factor)) le_rfl

/-- One further genuine accepted step turns a small gap into a small next-point measure. -/
theorem ARRun.first_measure_budget (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) {ε : ℝ} (hε : 0 < ε) {M : ℕ}
    (hM : ImplicitGap.orbit (κν / κψ ^ (ν / μ)) (ν / μ) (gap f fstar (x 0)) M ≤
      κν * ε ^ ν) :
    ∃ K : ℕ, ψ (x K) ≤ ε ∧ (∀ k < K, ε < ψ (x k)) ∧
      (EvaluationComplexity.successfulIterations S K).card ≤ M + 1 ∧
      (K : ℝ) ≤ κR * (M + 1) + κA := by
  classical
  let i := successIndex S M
  have hcount : (EvaluationComplexity.successfulIterations S i).card = M :=
    card_successIndex hr.infinite_success M
  have hgap : gap f fstar (x i) ≤ κν * ε ^ ν := by
    have hh := hr.gap_le_orbit hd i
    rw [hcount] at hh
    exact hh.trans hM
  have hdec := hr.decrease i (successIndex_mem hr.infinite_success M)
  have hlow := hd.gap_nonneg (x (i + 1))
  have hpow : ψ (x (i + 1)) ^ ν ≤ ε ^ ν := by
    apply (mul_le_mul_iff_right₀ hr.coefficient_pos).mp
    dsimp [gap] at hgap hlow
    nlinarith
  have htarget : ψ (x (i + 1)) ≤ ε := by
    by_contra hn
    have hh := Real.rpow_lt_rpow hε.le (lt_of_not_ge hn)
      (zero_lt_one.trans_le hr.exponent_ge_one)
    linarith
  have hc1 : (EvaluationComplexity.successfulIterations S (i + 1)).card = M + 1 := by
    rw [EvaluationComplexity.card_successful_succ, hcount,
      ite_eq_left (successIndex_mem hr.infinite_success M)]
  have hex : ∃ K : ℕ, ψ (x K) ≤ ε := ⟨i + 1, htarget⟩
  let K := Nat.find hex
  have hKi : K ≤ i + 1 := Nat.find_min' hex htarget
  have hcard : (EvaluationComplexity.successfulIterations S K).card ≤ M + 1 := by
    rw [← hc1]
    apply Finset.card_le_card
    intro j hj
    rw [EvaluationComplexity.mem_successfulIterations] at hj ⊢
    exact ⟨hj.1.trans_le hKi, hj.2⟩
  have hbound : (K : ℝ) ≤ κR * (M + 1) + κA := by
    have hh := hr.density (i + 1)
    rw [hc1] at hh
    push_cast at hh
    exact (show (K : ℝ) ≤ i + 1 by exact_mod_cast hKi).trans hh
  exact ⟨K, Nat.find_spec hex, fun j hj => lt_of_not_ge (Nat.find_min hex hj), hcard, hbound⟩

/-- Uniform logarithmic complexity with first actual target attainment and one initialized
function/derivative call. All four positive constants precede every positive accuracy. -/
def LogarithmicCost (target : ℕ → ℝ) (S : Set ℕ) : Prop :=
  ∃ B > 0, ∃ C > 0, ∃ D > 0, ∃ F > 0, ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, target K ≤ ε ∧ (∀ k < K, ε < target k) ∧
      ((K + 1 : ℕ) : ℝ) ≤ B * |Real.log ε| + C ∧
      ((EvaluationComplexity.successfulIterations S K).card + 1 : ℕ) ≤ D * |Real.log ε| + F

/-- At equal domination and decrease exponents the actual gap has logarithmic complexity. -/
theorem ARRun.gap_logarithmic (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (heq : ν = μ) :
    LogarithmicCost (fun k => gap f fstar (x k)) S := by
  let c := κν / κψ
  let R := max 1 (gap f fstar (x 0))
  let d := Real.log (1 + c)
  have hc : 0 < c := div_pos hr.coefficient_pos hd.coefficient_pos
  have hdpos : 0 < d := Real.log_pos (by linarith)
  have hR : 0 ≤ Real.log R := Real.log_nonneg (le_max_left _ _)
  have hκR : 0 < κR := zero_lt_one.trans_le hr.density_factor
  have hκA : 0 ≤ κA := hr.density_additive
  have ht : ν / μ = 1 := by rw [heq, div_self (zero_lt_one.trans_le hd.level_ge_one).ne']
  refine ⟨κR / d, div_pos hκR hdpos,
    κR * (Real.log R / d + 1) + κA + 1, by positivity,
    1 / d, by positivity, Real.log R / d + 2, by positivity, ?_⟩
  intro ε hε
  obtain ⟨M, htarget, hM⟩ := ImplicitGap.exists_linear_budget hc (hd.gap_nonneg (x 0)) hε
  have ho : ImplicitGap.orbit (κν / κψ ^ (ν / μ)) (ν / μ) (gap f fstar (x 0)) M ≤ ε := by
    simpa only [ht, Real.rpow_one] using htarget
  obtain ⟨K, hs, hfirst, hcard, hK⟩ := hr.first_gap_budget hd hε ho
  refine ⟨K, hs, hfirst, ?_, ?_⟩
  · push_cast
    calc (K : ℝ) + 1 ≤ κR * M + κA + 1 := by linarith
      _ ≤ κR * ((|Real.log ε| + Real.log R) / d + 1) + κA + 1 := by
        gcongr
      _ = _ := by ring
  · push_cast
    have hh : ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤ M :=
      by exact_mod_cast hcard
    calc _ ≤ (M : ℝ) + 1 := by linarith
      _ ≤ (|Real.log ε| + Real.log R) / d + 1 + 1 := by linarith
      _ = _ := by ring

/-- At equal exponents one further actual accepted step gives logarithmic measure complexity. -/
theorem ARRun.measure_logarithmic (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (heq : ν = μ) :
    LogarithmicCost (fun k => ψ (x k)) S := by
  let c := κν / κψ
  let R := max 1 (gap f fstar (x 0))
  let d := Real.log (1 + c)
  let A := |Real.log κν| + Real.log R
  have hc : 0 < c := div_pos hr.coefficient_pos hd.coefficient_pos
  have hdpos : 0 < d := Real.log_pos (by linarith)
  have hR : 0 ≤ Real.log R := Real.log_nonneg (le_max_left _ _)
  have hA : 0 ≤ A := by positivity
  have hκR : 0 < κR := zero_lt_one.trans_le hr.density_factor
  have hκA : 0 ≤ κA := hr.density_additive
  have hν : 0 < ν := zero_lt_one.trans_le hr.exponent_ge_one
  have ht : ν / μ = 1 := by rw [heq, div_self (zero_lt_one.trans_le hd.level_ge_one).ne']
  refine ⟨κR * ν / d, by positivity,
    κR * (A / d + 2) + κA + 1, by positivity,
    ν / d, by positivity, A / d + 3, by positivity, ?_⟩
  intro ε hε
  have hδ : 0 < κν * ε ^ ν := mul_pos hr.coefficient_pos (Real.rpow_pos_of_pos hε ν)
  obtain ⟨M, htarget, hM⟩ := ImplicitGap.exists_linear_budget hc (hd.gap_nonneg (x 0)) hδ
  have ho : ImplicitGap.orbit (κν / κψ ^ (ν / μ)) (ν / μ) (gap f fstar (x 0)) M ≤
      κν * ε ^ ν := by simpa only [ht, Real.rpow_one] using htarget
  obtain ⟨K, hs, hfirst, hcard, hK⟩ := hr.first_measure_budget hd hε ho
  have hlog : |Real.log (κν * ε ^ ν)| ≤ |Real.log κν| + ν * |Real.log ε| := by
    rw [Real.log_mul hr.coefficient_pos.ne' (Real.rpow_pos_of_pos hε ν).ne',
      Real.log_rpow hε]
    have hh := abs_add_le (Real.log κν) (ν * Real.log ε)
    simpa only [abs_mul, abs_of_pos hν] using hh
  have hMb : (M : ℝ) ≤ (ν * |Real.log ε| + A) / d + 1 := by
    apply hM.trans
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_right _ hdpos.le
    dsimp [A, R]
    linarith
  refine ⟨K, hs, hfirst, ?_, ?_⟩
  · push_cast
    calc (K : ℝ) + 1 ≤ κR * (M + 1) + κA + 1 := by linarith
      _ ≤ κR * (((ν * |Real.log ε| + A) / d + 1) + 1) + κA + 1 := by gcongr
      _ = _ := by ring
  · push_cast
    have hh : ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤ M + 1 :=
      by exact_mod_cast hcard
    calc _ ≤ (M : ℝ) + 2 := by linarith
      _ ≤ (ν * |Real.log ε| + A) / d + 1 + 2 := by linarith
      _ = _ := by ring
end MeasureDomination
