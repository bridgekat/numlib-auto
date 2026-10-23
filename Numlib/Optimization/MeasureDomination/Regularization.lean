import Numlib.Analysis.SpecialFunctions.Pow.ImplicitRecurrence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Nth
import Numlib.Optimization.EvaluationComplexity.AccuracyUpdates
import Mathlib.Tactic

/-!
# Adaptive regularization on measure-dominated objectives

The abstract source algorithm class specifies only its actual successful
next-point decrease, rejection rule and successful-prefix density. The additive
density constant absorbs the source inclusive-prefix index conversion. Domination
gives the exact implicit gap bound, successful-step rates and first hitting
counts. All evaluation bounds explicitly include initialization.
-/

open Set Filter Topology
namespace MeasureDomination
variable {E : Type*}

/-- A nonnegative optimality measure controls the gap above an attained global minimum. -/
structure Dominated (f ψ : E → ℝ) (fstar μ κ : ℝ) : Prop where
  minimum : IsLeast (Set.range f) fstar
  measure_nonneg : ∀ x, 0 ≤ ψ x
  level_ge_one : 1 ≤ μ
  coefficient_pos : 0 < κ
  domination : ∀ x, f x - fstar ≤ κ * ψ x ^ μ

/-- The abstract adaptive regularization class uses the next-point measure in its
actual successful decrease, unchanged points on rejection, and the source prefix density. -/
structure ARRun (f ψ : E → ℝ) (x : ℕ → E) (S : Set ℕ) (ν κ κR κA : ℝ) : Prop where
  exponent_ge_one : 1 ≤ ν
  coefficient_pos : 0 < κ
  infinite_success : S.Infinite
  rejected : ∀ k, k ∉ S → x (k + 1) = x k
  decrease : ∀ k ∈ S, κ * ψ (x (k + 1)) ^ ν ≤ f (x k) - f (x (k + 1))
  density_factor : 1 ≤ κR
  density_additive : 0 ≤ κA
  density : ∀ N : ℕ, (N : ℝ) ≤ κR *
    (EvaluationComplexity.successfulIterations S N).card + κA

/-- The actual objective gap above the specified minimum. -/
def gap (f : E → ℝ) (fstar : ℝ) (x : E) : ℝ := f x - fstar

/-- Successful iterations in their increasing natural order. -/
noncomputable def successIndex (S : Set ℕ) (n : ℕ) : ℕ := Nat.nth (fun k => k ∈ S) n

/-- The actual objective gaps at successive successful iterations. -/
noncomputable def successfulGap (f : E → ℝ) (fstar : ℝ) (x : ℕ → E) (S : Set ℕ)
  (n : ℕ) : ℝ :=
  gap f fstar (x (successIndex S n))

variable {f ψ : E → ℝ} {fstar μ κψ ν κν κR κA : ℝ} {x : ℕ → E} {S : Set ℕ}

/-- Every actual gap is nonnegative. -/
theorem Dominated.gap_nonneg (h : Dominated f ψ fstar μ κψ) (z : E) : 0 ≤ gap f fstar z :=
  sub_nonneg.mpr (h.minimum.2 (Set.mem_range_self z))

/-- Combining domination with a successful measure decrease gives the exact implicit power. -/
theorem Dominated.power_gap_le (h : Dominated f ψ fstar μ κψ) (hν : 0 < ν) (hκ : 0 < κν)
    (z : E) : κν / κψ ^ (ν / μ) * gap f fstar z ^ (ν / μ) ≤ κν * ψ z ^ ν := by
  have hμ : 0 < μ := zero_lt_one.trans_le h.level_ge_one
  have ht : 0 ≤ ν / μ := (div_pos hν hμ).le
  have hh := Real.rpow_le_rpow (h.gap_nonneg z) (h.domination z) ht
  rw [Real.mul_rpow h.coefficient_pos.le (Real.rpow_nonneg (h.measure_nonneg z) μ),
    ← Real.rpow_mul (h.measure_nonneg z), mul_div_cancel₀ ν hμ.ne'] at hh
  have hpow := Real.rpow_pos_of_pos h.coefficient_pos (ν / μ)
  apply (mul_le_mul_of_nonneg_left hh (div_nonneg hκ.le hpow.le)).trans
  have he : κν / κψ ^ (ν / μ) * (κψ ^ (ν / μ) * ψ z ^ ν) = κν * ψ z ^ ν := by
    field_simp
  exact he.le

/-- Actual objective gaps never increase, on accepted and rejected iterations. -/
theorem ARRun.gap_antitone (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) : Antitone (fun k => gap f fstar (x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  by_cases hk : k ∈ S
  · have hp := mul_nonneg hr.coefficient_pos.le
      (Real.rpow_nonneg (hd.measure_nonneg (x (k + 1))) ν)
    have hh := hr.decrease k hk
    dsimp [gap]
    linarith
  · rw [hr.rejected k hk]

/-- The exact accepted-step implicit gap inequality, before division by a gap. -/
theorem ARRun.implicit_decrease (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) {k : ℕ} (hk : k ∈ S) :
    gap f fstar (x (k + 1)) + κν / κψ ^ (ν / μ) *
      gap f fstar (x (k + 1)) ^ (ν / μ) ≤ gap f fstar (x k) := by
  have hh := hd.power_gap_le (zero_lt_one.trans_le hr.exponent_ge_one) hr.coefficient_pos
    (x (k + 1))
  have hm := hr.decrease k hk
  dsimp [gap] at *
  linarith

/-- The precise source one-step factor, including zero gaps without division by zero. -/
theorem ARRun.factor_decrease (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) {k : ℕ} (hk : k ∈ S) :
    gap f fstar (x (k + 1)) ≤ gap f fstar (x k) *
      (1 + κν / κψ ^ (ν / μ) * gap f fstar (x (k + 1)) ^ ((ν - μ) / μ))⁻¹ := by
  let b := gap f fstar (x (k + 1))
  let c := κν / κψ ^ (ν / μ)
  have hb : 0 ≤ b := hd.gap_nonneg _
  have hc : 0 < c := div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have he : b * b ^ ((ν - μ) / μ) = b ^ (ν / μ) := by
    rcases hb.eq_or_lt with hz | hp
    · rw [← hz, zero_mul, Real.zero_rpow (by
        have : 0 < μ := zero_lt_one.trans_le hd.level_ge_one
        exact (div_pos (zero_lt_one.trans_le hr.exponent_ge_one) this).ne')]
    · calc _ = b ^ (1 : ℝ) * b ^ ((ν - μ) / μ) := by rw [Real.rpow_one]
           _ = b ^ (1 + (ν - μ) / μ) := (Real.rpow_add hp _ _).symm
           _ = _ := by
             congr 1
             have hμ : μ ≠ 0 := (zero_lt_one.trans_le hd.level_ge_one).ne'
             field_simp
             ring
  have hp : 0 < 1 + c * b ^ ((ν - μ) / μ) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  have hh := hr.implicit_decrease hd hk
  change b + c * b ^ (ν / μ) ≤ _ at hh
  nlinarith [he]

/-- Successful indices really belong to the success set. -/
theorem successIndex_mem (hS : S.Infinite) (n : ℕ) : successIndex S n ∈ S :=
  Nat.nth_mem_of_infinite hS n

/-- The successful indices are strictly increasing. -/
theorem successIndex_strictMono (hS : S.Infinite) : StrictMono (successIndex S) :=
  Nat.nth_strictMono hS

/-- Passing to the actual successful iterates preserves the implicit power decrease. -/
theorem ARRun.successful_implicit_decrease (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (n : ℕ) :
    successfulGap f fstar x S (n + 1) + κν / κψ ^ (ν / μ) *
      successfulGap f fstar x S (n + 1) ^ (ν / μ) ≤ successfulGap f fstar x S n := by
  have hi : successIndex S n + 1 ≤ successIndex S (n + 1) :=
    Nat.succ_le_of_lt (successIndex_strictMono hr.infinite_success (Nat.lt_succ_self n))
  have hanti := hr.gap_antitone hd
  have hg := hanti hi
  have hpow := Real.rpow_le_rpow (hd.gap_nonneg _) hg
    (div_pos (zero_lt_one.trans_le hr.exponent_ge_one)
      (zero_lt_one.trans_le hd.level_ge_one)).le
  have hc : 0 < κν / κψ ^ (ν / μ) :=
    div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have hh := hr.implicit_decrease hd (successIndex_mem hr.infinite_success n)
  change successfulGap f fstar x S (n + 1) ≤ _ at hg
  change successfulGap f fstar x S (n + 1) ^ (ν / μ) ≤ _ at hpow
  change _ ≤ successfulGap f fstar x S n at hh
  nlinarith

/-- All successful gaps converge to zero, including after finite attainment. -/
theorem ARRun.successful_tendsto_zero (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) :
    Tendsto (successfulGap f fstar x S) atTop (𝓝 0) :=
  ImplicitGap.tendsto_zero
    (div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _))
    (div_pos (zero_lt_one.trans_le hr.exponent_ge_one) (zero_lt_one.trans_le hd.level_ge_one))
    (fun _ => hd.gap_nonneg _) (hr.successful_implicit_decrease hd)

/-- Below the domination level, actual successful gaps converge Q-superlinearly. -/
theorem ARRun.successful_superlinear (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν < μ) :
    Tendsto (fun n => successfulGap f fstar x S (n + 1) /
      successfulGap f fstar x S n) atTop (𝓝 0) :=
  ImplicitGap.superlinear
    (div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _))
    (div_pos (zero_lt_one.trans_le hr.exponent_ge_one) (zero_lt_one.trans_le hd.level_ge_one))
    ((div_lt_one (zero_lt_one.trans_le hd.level_ge_one)).mpr hνμ)
    (fun _ => hd.gap_nonneg _) (hr.successful_implicit_decrease hd)

/-- At the domination level, every successful step has the exact printed linear factor. -/
theorem ARRun.successful_linear (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν = μ) (n : ℕ) :
    successfulGap f fstar x S (n + 1) ≤ (1 + κν / κψ)⁻¹ * successfulGap f fstar x S n := by
  have hh := hr.successful_implicit_decrease hd
  have he : ν / μ = 1 := by rw [hνμ, div_self (zero_lt_one.trans_le hd.level_ge_one).ne']
  simp_rw [he, Real.rpow_one] at hh
  exact ImplicitGap.linear_step (div_pos hr.coefficient_pos hd.coefficient_pos) (fun k => by
    simpa only [Real.rpow_one] using hh k) n

/-- Above the domination level, the exact recurrence is a sublinear upper envelope;
actual algorithms may converge faster, including terminating in finitely many steps. -/
theorem ARRun.successful_sublinear_envelope (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ < ν) :
    (∀ n, successfulGap f fstar x S n = 0) ∨
      ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧
        (∀ n, successfulGap f fstar x S n ≤ t n) ∧ Tendsto t atTop (𝓝 0) ∧
        Tendsto (fun n => t (n + 1) / t n) atTop (𝓝 1) := by
  let b := successfulGap f fstar x S
  let c := κν / κψ ^ (ν / μ)
  let τ := ν / μ
  have hc : 0 < c := div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have ht : 0 < τ := div_pos (zero_lt_one.trans_le hr.exponent_ge_one)
    (zero_lt_one.trans_le hd.level_ge_one)
  have ht1 : 1 < τ := (one_lt_div (zero_lt_one.trans_le hd.level_ge_one)).mpr hμν
  have hb : ∀ n, 0 ≤ b n := fun _ => hd.gap_nonneg _
  have hdec : ∀ n, b (n + 1) + c * b (n + 1) ^ τ ≤ b n :=
    hr.successful_implicit_decrease hd
  rcases (hb 0).eq_or_lt with hz | hp
  · left
    have hanti : Antitone b := antitone_nat_of_succ_le fun n => by
      have hh := hdec n
      have hm := mul_nonneg hc.le (Real.rpow_nonneg (hb (n + 1)) τ)
      linarith
    intro n
    exact le_antisymm ((hanti (Nat.zero_le n)).trans_eq hz.symm) (hb n)
  · right
    exact ⟨ImplicitGap.orbit c τ (b 0), ImplicitGap.orbit_pos hc ht hp,
      ImplicitGap.le_orbit hc ht hb hdec, ImplicitGap.orbit_tendsto_zero hc ht hp.le,
      ImplicitGap.orbit_sublinear_ratio hc ht1 hp⟩

/-- The actual gap is bounded by the implicit recurrence at the exact number of accepted updates. -/
theorem ARRun.gap_le_orbit (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (N : ℕ) :
    gap f fstar (x N) ≤ ImplicitGap.orbit (κν / κψ ^ (ν / μ)) (ν / μ)
      (gap f fstar (x 0)) (EvaluationComplexity.successfulIterations S N).card := by
  classical
  have hc : 0 < κν / κψ ^ (ν / μ) :=
    div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have ht : 0 < ν / μ := div_pos (zero_lt_one.trans_le hr.exponent_ge_one)
    (zero_lt_one.trans_le hd.level_ge_one)
  induction N with
  | zero => simp [EvaluationComplexity.successfulIterations]
  | succ N ih =>
    rw [EvaluationComplexity.card_successful_succ]
    by_cases hk : N ∈ S
    · rw [ite_eq_left hk, ImplicitGap.orbit_succ]
      exact (ImplicitGap.le_step hc ht (hd.gap_nonneg _) (hd.gap_nonneg _)
        (hr.implicit_decrease hd hk)).trans
          (ImplicitGap.step_mono hc ht (hd.gap_nonneg _) ih)
    · rw [ite_eq_right hk, Nat.add_zero, hr.rejected N hk]
      exact ih

/-- The exact number of successes before the nth successful iteration is n. -/
theorem card_successIndex (hS : S.Infinite) (n : ℕ) :
    (EvaluationComplexity.successfulIterations S (successIndex S n)).card = n := by
  classical
  simpa only [Nat.count_eq_card_filter_range, successIndex,
    EvaluationComplexity.successfulIterations] using Nat.count_nth_of_infinite (p := fun k
      => k ∈ S) hS n

/-- The first actual gap target is reached within the exact implicit successful-step budget.
Trial and derivative counts include an additional initial evaluation explicitly. -/
theorem ARRun.first_gap_hitting (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) {ε : ℝ} (hε : 0 < ε) :
    let T := ImplicitGap.hittingTime (κν / κψ ^ (ν / μ)) (ν / μ) (gap f fstar (x 0)) ε
    ∃ K : ℕ, gap f fstar (x K) ≤ ε ∧
      (∀ k < K, ε < gap f fstar (x k)) ∧
      (gap f fstar (x 0) ≤ ε → K = 0) ∧
      (EvaluationComplexity.successfulIterations S K).card ≤ T ∧
      (K : ℝ) ≤ κR * T + κA ∧
      ((K + 1 : ℕ) : ℝ) ≤ κR * T + κA + 1 ∧
      (EvaluationComplexity.successfulIterations S K).card + 1 ≤ T + 1 := by
  classical
  let c := κν / κψ ^ (ν / μ)
  let τ := ν / μ
  let T := ImplicitGap.hittingTime c τ (gap f fstar (x 0)) ε
  have hc : 0 < c := div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have ht : 0 < τ := div_pos (zero_lt_one.trans_le hr.exponent_ge_one)
    (zero_lt_one.trans_le hd.level_ge_one)
  have htarget := (ImplicitGap.hittingTime_spec hc ht (hd.gap_nonneg (x 0)) hε).1
  let N := successIndex S T
  have hcount : (EvaluationComplexity.successfulIterations S N).card = T :=
    card_successIndex hr.infinite_success T
  have hgap : gap f fstar (x N) ≤ ε := by
    have hg := hr.gap_le_orbit hd N
    rw [hcount] at hg
    exact hg.trans htarget
  have hex : ∃ K : ℕ, gap f fstar (x K) ≤ ε := ⟨N, hgap⟩
  let K := Nat.find hex
  have hKN : K ≤ N := Nat.find_min' hex hgap
  have hcard : (EvaluationComplexity.successfulIterations S K).card ≤ T := by
    rw [← hcount]
    apply Finset.card_le_card
    intro k hk
    rw [EvaluationComplexity.mem_successfulIterations] at hk ⊢
    exact ⟨hk.1.trans_le hKN, hk.2⟩
  have htrials : (K : ℝ) ≤ κR * T + κA := by
    have hh := hr.density N
    rw [hcount] at hh
    exact (show (K : ℝ) ≤ N by exact_mod_cast hKN).trans hh
  refine ⟨K, Nat.find_spec hex, ?_, (Nat.find_eq_zero hex).mpr, hcard, htrials, ?_,
    Nat.add_le_add_right hcard 1⟩
  · intro k hk
    exact lt_of_not_ge (Nat.find_min hex hk)
  · push_cast
    linarith
end MeasureDomination
