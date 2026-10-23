import Numlib.Optimization.MeasureDomination.Linear
import Numlib.Analysis.SpecialFunctions.Pow.PolynomialBudget

/-!
# Genuine successful-step blocks and measure targets

Rejected trials preserve the endpoint between consecutive successes. Actual
accepted decreases then bound the next measure and force a target within a
finite block whenever its unsuccessful tests would exhaust the remaining gap.
-/

open Set Filter Topology
namespace MeasureDomination
variable {E : Type*} {f ψ : E → ℝ} {fstar μ κψ ν κν κR κA : ℝ}
  {x : ℕ → E} {S : Set ℕ}

/-- Rejected trials preserve the endpoint between consecutive actual successes. -/
theorem ARRun.next_success_point (hr : ARRun f ψ x S ν κν κR κA) (n : ℕ) :
    x (successIndex S (n + 1)) = x (successIndex S n + 1) := by
  have hstart : successIndex S n + 1 ≤ successIndex S (n + 1) :=
    Nat.succ_le_of_lt (successIndex_strictMono hr.infinite_success (Nat.lt_succ_self n))
  have hh : ∀ j, successIndex S n + 1 ≤ j → j ≤ successIndex S (n + 1) →
      x j = x (successIndex S n + 1) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; rfl
    | succ j hj ih =>
      intro hfinish
      have hn : j ∉ S := by
        intro hmem
        have hb := Nat.le_nth_of_lt_nth_succ
          (p := fun k => k ∈ S) (show j < successIndex S (n + 1) by omega) hmem
        change j ≤ successIndex S n at hb
        omega
      rw [hr.rejected j hn]
      exact ih (by omega)
  exact hh _ hstart le_rfl

/-- Actual consecutive successful iterates retain the genuine next-point measure decrease. -/
theorem ARRun.successful_measure_decrease (hr : ARRun f ψ x S ν κν κR κA) (n : ℕ) :
    κν * ψ (x (successIndex S (n + 1))) ^ ν ≤
      successfulGap f fstar x S n - successfulGap f fstar x S (n + 1) := by
  have hh := hr.decrease (successIndex S n) (successIndex_mem hr.infinite_success n)
  dsimp [successfulGap, gap]
  rw [hr.next_success_point n]
  linarith

/-- After the actual comparison gap is at most G, a finite block of failed measure tests
would consume more than G; therefore the target is reached within that block. -/
theorem ARRun.first_measure_block (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) {ε G : ℝ} (hε : 0 < ε) {M J : ℕ}
    (hM : ImplicitGap.orbit (κν / κψ ^ (ν / μ)) (ν / μ) (gap f fstar (x 0)) M ≤ G)
    (hJ : G < (J : ℝ) * (κν * ε ^ ν)) :
    ∃ K : ℕ, ψ (x K) ≤ ε ∧ (∀ k < K, ε < ψ (x k)) ∧
      (EvaluationComplexity.successfulIterations S K).card ≤ M + J ∧
      (K : ℝ) ≤ κR * (M + J) + κA := by
  classical
  let N := successIndex S (M + J)
  have hcount : (EvaluationComplexity.successfulIterations S N).card = M + J :=
    card_successIndex hr.infinite_success (M + J)
  have hgap : successfulGap f fstar x S M ≤ G := by
    have hh := hr.gap_le_orbit hd (successIndex S M)
    rw [card_successIndex hr.infinite_success M] at hh
    exact hh.trans hM
  have hbounded : ∃ K ≤ N, ψ (x K) ≤ ε := by
    by_contra hn
    push Not at hn
    have hstep (j : ℕ) (hj : j < J) : κν * ε ^ ν ≤
        successfulGap f fstar x S (M + j) - successfulGap f fstar x S (M + j + 1) := by
      have hi : successIndex S (M + j + 1) ≤ N :=
        (successIndex_strictMono hr.infinite_success).monotone (by omega)
      have hp := Real.rpow_le_rpow hε.le (hn _ hi).le
        (zero_lt_one.trans_le hr.exponent_ge_one).le
      exact (mul_le_mul_of_nonneg_left hp hr.coefficient_pos.le).trans
        (hr.successful_measure_decrease (fstar := fstar) (M + j))
    have htotal : ∀ j : ℕ, j ≤ J → (j : ℝ) * (κν * ε ^ ν) ≤
        successfulGap f fstar x S M - successfulGap f fstar x S (M + j) := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        have hh := hstep j (by omega)
        have hp := ih (by omega)
        simp only [Nat.add_assoc] at hh
        push_cast
        nlinarith
    have hsum := htotal J le_rfl
    have hlow := hd.gap_nonneg (x (successIndex S (M + J)))
    change 0 ≤ successfulGap f fstar x S (M + J) at hlow
    linarith
  obtain ⟨K₀, hK₀, htarget⟩ := hbounded
  have hex : ∃ K : ℕ, ψ (x K) ≤ ε := ⟨K₀, htarget⟩
  let K := Nat.find hex
  have hKN : K ≤ N := (Nat.find_min' hex htarget).trans hK₀
  have hcard : (EvaluationComplexity.successfulIterations S K).card ≤ M + J := by
    rw [← hcount]
    apply Finset.card_le_card
    intro j hj
    rw [EvaluationComplexity.mem_successfulIterations] at hj ⊢
    exact ⟨hj.1.trans_le hKN, hj.2⟩
  have hbound : (K : ℝ) ≤ κR * (M + J) + κA := by
    have hh := hr.density N
    rw [hcount] at hh
    push_cast at hh
    exact (show (K : ℝ) ≤ N by exact_mod_cast hKN).trans hh
  exact ⟨K, Nat.find_spec hex, fun j hj => lt_of_not_ge (Nat.find_min hex hj), hcard, hbound⟩

/-- A true accepted decrease bounds the next successful measure by a root of the current gap. -/
theorem ARRun.successful_measure_le (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (n : ℕ) :
    ψ (x (successIndex S (n + 1))) ≤
      (successfulGap f fstar x S n / κν) ^ (1 / ν) := by
  have hν : 0 < ν := zero_lt_one.trans_le hr.exponent_ge_one
  have hm := hr.successful_measure_decrease (fstar := fstar) n
  have hg := hd.gap_nonneg (x (successIndex S (n + 1)))
  change 0 ≤ successfulGap f fstar x S (n + 1) at hg
  have hpow : ψ (x (successIndex S (n + 1))) ^ ν ≤
      successfulGap f fstar x S n / κν := (le_div_iff₀ hr.coefficient_pos).mpr (by nlinarith)
  have hh := Real.rpow_le_rpow
    (Real.rpow_nonneg (hd.measure_nonneg _) ν) hpow (show 0 ≤ 1 / ν by positivity)
  rwa [← Real.rpow_mul (hd.measure_nonneg _), mul_one_div_cancel hν.ne', Real.rpow_one] at hh

/-- Actual successful optimality measures converge, without any monotonicity hypothesis on them. -/
theorem ARRun.successful_measure_tendsto_zero (hr : ARRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) :
    Tendsto (fun n => ψ (x (successIndex S n))) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hν : 0 < ν := zero_lt_one.trans_le hr.exponent_ge_one
  have ht := ((hr.successful_tendsto_zero hd).div_const κν).rpow_const
    (Or.inr (show 0 ≤ 1 / ν by positivity))
  have ht0 : Tendsto (fun n => (successfulGap f fstar x S n / κν) ^ (1 / ν))
      atTop (𝓝 0) := by simpa only [zero_div, Real.zero_rpow (by positivity : (1 / ν)
        ≠ 0)] using ht
  exact squeeze_zero (fun n => hd.measure_nonneg _) (hr.successful_measure_le hd) ht0
end MeasureDomination
