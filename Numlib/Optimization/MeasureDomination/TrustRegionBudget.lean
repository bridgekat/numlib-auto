import Numlib.Optimization.MeasureDomination.TrustRegionRates
import Numlib.Optimization.MeasureDomination.Polynomial

/-!
# First-target budgets for historical trust-region algorithms

The actual gap supplies a dominated proxy measure for accepted implicit
recurrences. A finite block of unsuccessful true-measure tests exhausts the
remaining objective gap, without identifying current and historical measures.
-/

namespace MeasureDomination
open Set Filter Topology
variable {E : Type*} {f ψ : E → ℝ} {fstar μ κψ ν κν κR κA : ℝ}
  {x : ℕ → E} {S : Set ℕ}

/-- The nonnegative objective gap is itself a level-one dominated measure. -/
theorem Dominated.gap_dominated (hd : Dominated f ψ fstar μ κψ) :
    Dominated f (gap f fstar) fstar 1 1 :=
  ⟨hd.minimum, hd.gap_nonneg, le_rfl, zero_lt_one, fun z => by
    simp only [gap, Real.rpow_one, one_mul, le_refl]⟩

/-- Above the domination level, actual historical decreases define an adaptive
regularization proxy execution whose measure is the true objective gap. -/
theorem TRRun.gap_run (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ ≤ ν) :
    ARRun f (gap f fstar) x S (ν / μ) (κν / κψ ^ (ν / μ)) κR κA := by
  have hμ : 0 < μ := zero_lt_one.trans_le hd.level_ge_one
  have ht : 0 < ν / μ := div_pos (zero_lt_one.trans_le hr.exponent_ge_one) hμ
  have hc : 0 < κν / κψ ^ (ν / μ) :=
    div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  refine ⟨(one_le_div hμ).mpr hμν, hc, hr.infinite_success, hr.rejected, ?_,
    hr.density_factor, hr.density_additive, hr.density⟩
  intro k hk
  have he := hr.explicit_decrease hd hk
  have hp := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hd.gap_nonneg _) (hr.gap_antitone hd (Nat.le_succ k)) ht.le) hc.le
  dsimp [gap] at he hp ⊢
  linarith

/-- Any exact comparison-orbit gap budget bounds first actual gap attainment. -/
theorem TRRun.first_gap_budget (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ ≤ ν) {ε : ℝ} (hε : 0 < ε) {M : ℕ}
    (hM : ImplicitGap.orbit (κν / κψ ^ (ν / μ)) (ν / μ) (gap f fstar (x 0)) M ≤ ε) :
    ∃ K : ℕ, gap f fstar (x K) ≤ ε ∧ (∀ k < K, ε < gap f fstar (x k)) ∧
      (EvaluationComplexity.successfulIterations S K).card ≤ M ∧
      (K : ℝ) ≤ κR * M + κA := by
  have ho : ImplicitGap.orbit
      ((κν / κψ ^ (ν / μ)) / (1 : ℝ) ^ ((ν / μ) / 1)) ((ν / μ) / 1)
      (gap f fstar (x 0)) M ≤ ε := by simpa only [div_one, Real.one_rpow] using hM
  exact (hr.gap_run hd hμν).first_gap_budget hd.gap_dominated hε ho

/-- The current successful gap is bounded by the exact implicit comparison orbit. -/
theorem TRRun.successful_gap_le_orbit (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ ≤ ν) (M : ℕ) :
    successfulGap f fstar x S M ≤
      ImplicitGap.orbit (κν / κψ ^ (ν / μ)) (ν / μ) (gap f fstar (x 0)) M := by
  have hh := (hr.gap_run hd hμν).gap_le_orbit hd.gap_dominated (successIndex S M)
  rw [card_successIndex hr.infinite_success M] at hh
  simpa only [div_one, Real.one_rpow, successfulGap] using hh

/-- At equal exponents, initialized first-gap costs are logarithmic. -/
theorem TRRun.gap_logarithmic (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (heq : ν = μ) :
    LogarithmicCost (fun k => gap f fstar (x k)) S := by
  have ht : ν / μ = 1 := by rw [heq, div_self (zero_lt_one.trans_le hd.level_ge_one).ne']
  exact (hr.gap_run hd heq.ge).gap_logarithmic hd.gap_dominated ht

/-- Above the domination level, initialized first-gap costs have the source power. -/
theorem TRRun.gap_power_cost (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ < ν) :
    PowerCost ((ν - μ) / μ) (fun k => gap f fstar (x k)) S := by
  have hμ : 0 < μ := zero_lt_one.trans_le hd.level_ge_one
  have hh := (hr.gap_run hd hμν.le).gap_power_cost hd.gap_dominated
    ((one_lt_div hμ).mpr hμν)
  have he : (ν / μ - 1) / 1 = (ν - μ) / μ := by field_simp
  simpa only [he] using hh

/-- After the actual comparison gap is at most G, a finite block of failed measure tests
would consume more than G; therefore the target is reached within that block. -/
theorem TRRun.first_measure_block (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ ≤ ν) {ε G : ℝ} (hε : 0 < ε) {M J : ℕ}
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
    exact (hr.successful_gap_le_orbit hd hμν M).trans hM
  have hbounded : ∃ K ≤ N, ψ (x K) ≤ ε := by
    by_contra hn
    push Not at hn
    have hstep (j : ℕ) (hj : j < J) : κν * ε ^ ν ≤
        successfulGap f fstar x S (M + j) - successfulGap f fstar x S (M + j + 1) := by
      let i := successIndex S (M + j)
      have hi : i ≤ N :=
        (successIndex_strictMono hr.infinite_success).monotone (by omega)
      have hm : ε ≤ pastMeasure ψ x i :=
        le_pastMeasure (fun k hk => (hn k (hk.trans hi)).le)
      have hp := Real.rpow_le_rpow hε.le hm
        (zero_lt_one.trans_le hr.exponent_ge_one).le
      have hdec := (mul_le_mul_of_nonneg_left hp hr.coefficient_pos.le).trans
        (hr.decrease i (successIndex_mem hr.infinite_success (M + j)))
      change κν * ε ^ ν ≤
        gap f fstar (x i) - gap f fstar (x (successIndex S (M + j + 1)))
      rw [hr.next_success_point (M + j)]
      dsimp [gap, i] at *
      linarith
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


/-- At equal exponents a finite actual accepted block gives logarithmic measure complexity. -/
theorem TRRun.measure_logarithmic (hr : TRRun f ψ x S ν κν κR κA)
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
    κR * (A / d + 3) + κA + 1, by positivity,
    ν / d, by positivity, A / d + 4, by positivity, ?_⟩
  intro ε hε
  have hδ : 0 < κν * ε ^ ν := mul_pos hr.coefficient_pos (Real.rpow_pos_of_pos hε ν)
  obtain ⟨M, htarget, hM⟩ := ImplicitGap.exists_linear_budget hc (hd.gap_nonneg (x 0)) hδ
  have ho : ImplicitGap.orbit (κν / κψ ^ (ν / μ)) (ν / μ) (gap f fstar (x 0)) M ≤
      κν * ε ^ ν := by simpa only [ht, Real.rpow_one] using htarget
  obtain ⟨K, hs, hfirst, hcard, hK⟩ := hr.first_measure_block hd heq.ge hε (J := 2) ho
    (by norm_num; nlinarith)
  norm_num at hK
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
    calc (K : ℝ) + 1 ≤ κR * (M + 2) + κA + 1 := by linarith
      _ ≤ κR * (((ν * |Real.log ε| + A) / d + 1) + 2) + κA + 1 := by gcongr
      _ = _ := by ring
  · push_cast
    have hh : ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤ M + 2 :=
      by exact_mod_cast hcard
    calc _ ≤ (M : ℝ) + 3 := by linarith
      _ ≤ (ν * |Real.log ε| + A) / d + 1 + 3 := by linarith
      _ = _ := by ring

/-- A finite block after a small true gap gives the sharper source measure power cost. -/
theorem TRRun.measure_power_cost (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ < ν) :
    PowerCost (ν - μ) (fun k => ψ (x k)) S := by
  let c := κν / κψ ^ (ν / μ)
  let τ := ν / μ
  let r := τ - 1
  let R := max 1 (gap f fstar (x 0))
  let δ := r * c / (1 + c * R ^ r) ^ τ
  let A := (1 / δ) * κψ ^ (-r) + κψ / κν
  have hμ : 0 < μ := zero_lt_one.trans_le hd.level_ge_one
  have hc : 0 < c := div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have ht : 1 < τ := (one_lt_div hμ).mpr hμν
  have hrpos : 0 < r := by dsimp [r]; linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hA : 0 < A := add_pos
    (mul_pos (one_div_pos.mpr hδ) (Real.rpow_pos_of_pos hd.coefficient_pos _))
    (div_pos hd.coefficient_pos hr.coefficient_pos)
  have hκR : 0 < κR := zero_lt_one.trans_le hr.density_factor
  have hκA : 0 ≤ κA := hr.density_additive
  have hν : 0 < ν := zero_lt_one.trans_le hr.exponent_ge_one
  have her : μ * r = ν - μ := by dsimp [r, τ]; field_simp
  refine ⟨κR * A, by positivity, 3 * κR + κA + 1, by positivity,
    A, hA, 4, by norm_num, ?_⟩
  intro ε hε
  let G := κψ * ε ^ μ
  let d := κν * ε ^ ν
  have hG : 0 < G := mul_pos hd.coefficient_pos (Real.rpow_pos_of_pos hε μ)
  have hdpos : 0 < d := mul_pos hr.coefficient_pos (Real.rpow_pos_of_pos hε ν)
  obtain ⟨M, htarg, hM⟩ := ImplicitGap.exists_polynomial_budget hc ht (hd.gap_nonneg (x 0)) hG
  change (M : ℝ) ≤ (1 / δ) * G ^ (-r) + 1 at hM
  let J : ℕ := ⌈G / d⌉₊ + 1
  have hJ : G < (J : ℝ) * d := by
    have hh : G ≤ (⌈G / d⌉₊ : ℝ) * d := (div_le_iff₀ hdpos).mp (Nat.le_ceil _)
    dsimp [J]
    push_cast
    nlinarith
  obtain ⟨K, hs, hfirst, hcard, hK⟩ := hr.first_measure_block hd hμν.le hε htarg hJ
  have hJb : (J : ℝ) ≤ G / d + 2 := by
    have hh := (Nat.ceil_lt_add_one (div_nonneg hG.le hdpos.le)).le
    dsimp [J]
    push_cast
    linarith
  have hGpow : G ^ (-r) = κψ ^ (-r) * ε ^ (-(ν - μ)) := by
    dsimp [G]
    rw [Real.mul_rpow hd.coefficient_pos.le (Real.rpow_nonneg hε.le μ),
      ← Real.rpow_mul hε.le]
    rw [show μ * (-r) = -(ν - μ) by nlinarith [her]]
  have hratio : G / d = (κψ / κν) * ε ^ (-(ν - μ)) := by
    dsimp [G, d]
    rw [show -(ν - μ) = μ - ν by ring, Real.rpow_sub hε]
    ring
  have hsum : (M : ℝ) + J ≤ A * ε ^ (-(ν - μ)) + 3 := by
    rw [hGpow] at hM
    rw [hratio] at hJb
    dsimp [A]
    nlinarith
  refine ⟨K, hs, hfirst, ?_, ?_⟩
  · push_cast at hK ⊢
    calc (K : ℝ) + 1 ≤ κR * (M + J) + κA + 1 := by linarith
      _ ≤ κR * (A * ε ^ (-(ν - μ)) + 3) + κA + 1 := by gcongr
      _ = _ := by ring
  · push_cast
    have hh : ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤ (M : ℝ) + J :=
      by exact_mod_cast hcard
    linarith


/-- The actual history converges to zero whenever every positive current-measure
first target is attained; current measures themselves need not converge. -/
theorem pastMeasure_tendsto_zero_of_targets
    (hm : ∀ z, 0 ≤ ψ z) (ht : ∀ ε : ℝ, 0 < ε → ∃ K, ψ (x K) ≤ ε) :
    Tendsto (pastMeasure ψ x) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K, hK⟩ := ht (ε / 2) (by positivity)
  refine ⟨K, fun n hn => ?_⟩
  have hlo : 0 ≤ pastMeasure ψ x n := le_pastMeasure (fun _ _ => hm _)
  have hhi := (pastMeasure_le ψ x hn).trans hK
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  linarith

/-- The linear regime either attains the minimum at the first accepted endpoint
or has the exact positive contraction factor from the source. -/
theorem TRRun.linear_alternative (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (heq : ν = μ) :
    gap f fstar (x (successIndex S 0 + 1)) = 0 ∨
      κν < κψ ∧ ∀ j, successfulGap f fstar x S (j + 1) ≤
        (1 - κν / κψ) * successfulGap f fstar x S j := by
  by_cases hz : gap f fstar (x (successIndex S 0 + 1)) = 0
  · exact Or.inl hz
  · right
    have hp : 0 < gap f fstar (x 0) := by
      have hh := hr.gap_antitone hd (Nat.zero_le (successIndex S 0 + 1))
      exact lt_of_lt_of_le (lt_of_le_of_ne (hd.gap_nonneg _) (Ne.symm hz)) hh
    have hc := hr.linear_coefficient_le hd heq hp
    have hne : κν ≠ κψ := fun he => hz (hr.first_zero_of_equal_linear hd heq he)
    refine ⟨lt_of_le_of_ne hc hne, ?_⟩
    intro j
    have hh := hr.linear_decrease hd heq (successIndex_mem hr.infinite_success j)
    simpa only [successfulGap, hr.next_success_point j] using hh

/-- Above the domination level the historical optimality measure converges,
even if actual successful current measures oscillate. -/
theorem TRRun.historical_measure_tendsto_zero (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ < ν) :
    Tendsto (pastMeasure ψ x) atTop (nhds 0) := by
  obtain ⟨B, _, C, _, D, _, F, _, hh⟩ := hr.measure_power_cost hd hμν
  apply pastMeasure_tendsto_zero_of_targets hd.measure_nonneg
  intro ε hε
  obtain ⟨K, hK, _⟩ := hh ε hε
  exact ⟨K, hK⟩

/-- The historical target has the same power bound at its own first attainment. -/
theorem TRRun.historical_measure_power_cost (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ < ν) :
    PowerCost (ν - μ) (pastMeasure ψ x) S :=
  (hr.measure_power_cost hd hμν).mono (fun _k => pastMeasure_le ψ x le_rfl)

end MeasureDomination
