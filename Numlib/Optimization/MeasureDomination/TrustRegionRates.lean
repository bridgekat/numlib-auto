import Numlib.Optimization.MeasureDomination.TrustRegion
import Numlib.Analysis.SpecialFunctions.Pow.ExplicitRecurrence
import Numlib.Optimization.EvaluationComplexity.Points

/-!
# Actual successful-gap rates for historical trust-region decrease

The explicit current-gap inequality survives successful subsequences. The source
threshold separates the nonunit exponent cases; exact gap attainment yields an
actual zero measure because the algorithm stops at such points.
-/

namespace MeasureDomination
open Set Filter Topology
variable {E : Type*} {f ψ : E → ℝ} {fstar μ κψ ν κν κR κA : ℝ}
  {x : ℕ → E} {S : Set ℕ}

/-- The source threshold expressed with its original domination parameters. -/
noncomputable def trGapThreshold (κψ κν μ ν : ℝ) : ℝ :=
  (κψ ^ (ν / μ) / κν) ^ (μ / (ν - μ))

/-- The source threshold is exactly the explicit-recurrence normalization. -/
theorem trGapThreshold_eq (hμ : μ ≠ 0) (hνμ : ν ≠ μ) :
    trGapThreshold κψ κν μ ν = ExplicitGap.threshold (κν / κψ ^ (ν / μ)) (ν / μ) := by
  have hdiff : ν - μ ≠ 0 := sub_ne_zero.mpr hνμ
  have hexp : 1 / (1 - ν / μ) = -(μ / (ν - μ)) := by field_simp; ring
  rw [ExplicitGap.threshold, hexp, Real.rpow_neg_eq_inv_rpow, inv_div]
  rfl

/-- Every actual point after a zero-measure stop is the same terminal point. -/
theorem TRRun.point_eq_after_zero (hr : TRRun f ψ x S ν κν κR κA)
    {i j : ℕ} (hz : ψ (x i) = 0) (hij : i ≤ j) : x j = x i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    rw [hr.stopped_point j (by rw [ih]; exact hz)]
    exact ih

/-- All points before the first actual successful iteration equal the initial point. -/
theorem TRRun.first_success_point (hr : TRRun f ψ x S ν κν κR κA) :
    x (successIndex S 0) = x 0 := by
  apply EvaluationComplexity.point_eq_of_no_success hr.rejected (Nat.zero_le _)
  intro i _ hi hmem
  have hleast : successIndex S 0 ≤ i := by
    simpa [successIndex, Nat.nth_zero] using Nat.sInf_le hmem
  omega

/-- Rejected trials preserve the actual endpoint between consecutive successes. -/
theorem TRRun.next_success_point (hr : TRRun f ψ x S ν κν κR κA) (n : ℕ) :
    x (successIndex S (n + 1)) = x (successIndex S n + 1) := by
  apply EvaluationComplexity.point_eq_of_no_success hr.rejected
    (Nat.succ_le_of_lt (successIndex_strictMono hr.infinite_success (Nat.lt_succ_self n)))
  intro i hi hij hmem
  have hb := Nat.le_nth_of_lt_nth_succ (p := fun k => k ∈ S) hij hmem
  change i ≤ successIndex S n at hb
  omega

/-- The actual successful subsequence retains explicit current-gap decrease. -/
theorem TRRun.successful_explicit_decrease (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (n : ℕ) :
    successfulGap f fstar x S (n + 1) + κν / κψ ^ (ν / μ) *
      successfulGap f fstar x S n ^ (ν / μ) ≤ successfulGap f fstar x S n := by
  have hi : successIndex S n + 1 ≤ successIndex S (n + 1) :=
    Nat.succ_le_of_lt (successIndex_strictMono hr.infinite_success (Nat.lt_succ_self n))
  have hg := (hr.gap_antitone hd) hi
  have hh := hr.explicit_decrease hd (successIndex_mem hr.infinite_success n)
  change successfulGap f fstar x S (n + 1) ≤ _ at hg
  change _ ≤ successfulGap f fstar x S n at hh
  change successfulGap f fstar x S (n + 1) + _ ≤ successfulGap f fstar x S n
  dsimp only [successfulGap] at *
  linarith

/-- The full printed current-point contraction factor holds at every actual
accepted iteration, with zero-gap cases included. -/
theorem TRRun.factor_decrease (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) {k : ℕ} (hk : k ∈ S) :
    gap f fstar (x (k + 1)) ≤ gap f fstar (x k) *
      (1 - κν / κψ ^ (ν / μ) * gap f fstar (x k) ^ ((ν - μ) / μ)) := by
  obtain ⟨n, _, hn⟩ := Nat.exists_lt_card_nth_eq hk
  change successIndex S n = k at hn
  have hh := ExplicitGap.factor_step
    (div_pos (zero_lt_one.trans_le hr.exponent_ge_one) (zero_lt_one.trans_le hd.level_ge_one))
    (fun n => hd.gap_nonneg (x (successIndex S n))) (hr.successful_explicit_decrease hd) n
  rw [hr.next_success_point n, hn] at hh
  have he : ν / μ - 1 = (ν - μ) / μ := by
    field_simp [(zero_lt_one.trans_le hd.level_ge_one).ne']
  simpa only [he] using hh

/-- Below the domination level every positive current successful gap is at
least the source's fixed threshold. -/
theorem TRRun.current_gap_ge_threshold (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν < μ) {k : ℕ} (hk : k ∈ S)
    (hgap : 0 < gap f fstar (x k)) : trGapThreshold κψ κν μ ν ≤ gap f fstar (x k) := by
  obtain ⟨n, _, hn⟩ := Nat.exists_lt_card_nth_eq hk
  change successIndex S n = k at hn
  rw [trGapThreshold_eq (zero_lt_one.trans_le hd.level_ge_one).ne' hνμ.ne]
  have hh := ExplicitGap.threshold_le_of_pos
    (div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos (ν / μ)))
    ((div_lt_one (zero_lt_one.trans_le hd.level_ge_one)).mpr hνμ)
    (fun n => hd.gap_nonneg (x (successIndex S n))) (hr.successful_explicit_decrease hd)
    (show 0 < successfulGap f fstar x S n by simpa only [successfulGap, hn] using hgap)
  simpa only [successfulGap, hn] using hh

/-- Actual successful gaps converge to zero for every positive exponent. -/
theorem TRRun.successful_tendsto_zero (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) :
    Tendsto (successfulGap f fstar x S) atTop (nhds 0) :=
  ExplicitGap.tendsto_zero
    (div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _))
    (div_pos (zero_lt_one.trans_le hr.exponent_ge_one) (zero_lt_one.trans_le hd.level_ge_one))
    (fun _ => hd.gap_nonneg _) (hr.successful_explicit_decrease hd)

/-- Subunit domination ratios give a superlinear gap upper rate, including exact
finite attainment and the zero-over-zero convention thereafter. -/
theorem TRRun.successful_superlinear (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν < μ) :
    Tendsto (fun n => successfulGap f fstar x S (n + 1) /
      successfulGap f fstar x S n) atTop (nhds 0) := by
  have hc := div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos (ν / μ))
  have hτ := div_pos (zero_lt_one.trans_le hr.exponent_ge_one)
    (zero_lt_one.trans_le hd.level_ge_one)
  exact ImplicitGap.superlinear hc hτ
    ((div_lt_one (zero_lt_one.trans_le hd.level_ge_one)).mpr hνμ)
    (fun _ => hd.gap_nonneg _)
    (ExplicitGap.implicit_decrease hc hτ (fun _ => hd.gap_nonneg _)
      (hr.successful_explicit_decrease hd))

/-- Below the domination level an actual finite iterate attains the global minimum. -/
theorem TRRun.exists_gap_zero (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν < μ) :
    ∃ K, gap f fstar (x K) = 0 := by
  obtain ⟨n, hn⟩ := ExplicitGap.exists_zero
    (b := successfulGap f fstar x S) (c := κν / κψ ^ (ν / μ)) (τ := ν / μ)
    (div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _))
    (div_pos (zero_lt_one.trans_le hr.exponent_ge_one) (zero_lt_one.trans_le hd.level_ge_one))
    ((div_lt_one (zero_lt_one.trans_le hd.level_ge_one)).mpr hνμ)
    (fun _ => hd.gap_nonneg _) (hr.successful_explicit_decrease hd)
  exact ⟨successIndex S n, hn⟩

/-- Exact global-gap attainment forces the actual measure to vanish. Otherwise
all earlier measures and the first future accepted historical minimum would be
positive, forcing a decrease below the attained global minimum. -/
theorem TRRun.measure_zero_of_gap_zero (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) {k : ℕ} (hk : gap f fstar (x k) = 0) :
    ψ (x k) = 0 := by
  classical
  by_contra hn
  have hp : 0 < ψ (x k) := lt_of_le_of_ne (hd.measure_nonneg _) (Ne.symm hn)
  have hex : ∃ j : ℕ, k ≤ j ∧ j ∈ S :=
    ⟨successIndex S k, (successIndex_strictMono hr.infinite_success).id_le k,
      successIndex_mem hr.infinite_success k⟩
  let j := Nat.find hex
  have hkj : k ≤ j := (Nat.find_spec hex).1
  have hj : j ∈ S := (Nat.find_spec hex).2
  have hno : ∀ i, k ≤ i → i < j → i ∉ S := by
    intro i hki hij hiS
    have hi := Nat.find_min' hex ⟨hki, hiS⟩
    omega
  have hprefix : ∀ i ≤ j, 0 < ψ (x i) := by
    intro i hij
    by_cases hik : i ≤ k
    · apply lt_of_le_of_ne (hd.measure_nonneg _)
      intro hz
      apply hn
      rw [hr.point_eq_after_zero hz.symm hik]
      exact hz.symm
    · have hki : k ≤ i := by omega
      have he := EvaluationComplexity.point_eq_of_no_success hr.rejected hki
        (fun a hka hai => hno a hka (hai.trans_le hij))
      rw [he]
      exact hp
  obtain ⟨i, hij, he⟩ := pastMeasure_attains ψ x j
  have hmin : 0 < pastMeasure ψ x j := by rw [he]; exact hprefix i hij
  have hdrop := hr.decrease j hj
  have hpos := mul_pos hr.coefficient_pos (Real.rpow_pos_of_pos hmin ν)
  have hg : gap f fstar (x j) = 0 :=
    le_antisymm ((hr.gap_antitone hd hkj).trans_eq hk) (hd.gap_nonneg _)
  have hlo := hd.gap_nonneg (x (j + 1))
  dsimp [gap] at hg hlo
  linarith

/-- The first exact minimum and zero measure have a uniform finite budget.
Only the initial gap, the fixed decrease threshold and source density appear. -/
theorem TRRun.first_zero_budget (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν < μ) :
    let θ := ExplicitGap.threshold (κν / κψ ^ (ν / μ)) (ν / μ)
    ∃ K : ℕ, gap f fstar (x K) = 0 ∧ ψ (x K) = 0 ∧
      (∀ i < K, 0 < gap f fstar (x i)) ∧ (∀ j, K ≤ j → x j = x K) ∧
      ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤
        gap f fstar (x 0) / θ ∧
      (K : ℝ) ≤ κR * (gap f fstar (x 0) / θ) + κA := by
  classical
  dsimp only
  let c := κν / κψ ^ (ν / μ)
  let τ := ν / μ
  let θ := ExplicitGap.threshold c τ
  have hc : 0 < c := div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have hτ : 0 < τ := div_pos (zero_lt_one.trans_le hr.exponent_ge_one)
    (zero_lt_one.trans_le hd.level_ge_one)
  have hτ1 : τ < 1 := (div_lt_one (zero_lt_one.trans_le hd.level_ge_one)).mpr hνμ
  obtain ⟨n, hn, _, hnb⟩ := ExplicitGap.exists_zero_le_budget hc hτ hτ1
    (fun n => hd.gap_nonneg (x (successIndex S n))) (hr.successful_explicit_decrease hd)
  have hinit : successfulGap f fstar x S 0 = gap f fstar (x 0) := by
    rw [successfulGap, hr.first_success_point]
  change (n : ℝ) ≤ successfulGap f fstar x S 0 / θ at hnb
  rw [hinit] at hnb
  have hex : ∃ K : ℕ, gap f fstar (x K) = 0 := ⟨successIndex S n, hn⟩
  let K := Nat.find hex
  have hzero : gap f fstar (x K) = 0 := Nat.find_spec hex
  have hKN : K ≤ successIndex S n := Nat.find_min' hex hn
  have hcard : (EvaluationComplexity.successfulIterations S K).card ≤ n := by
    rw [←card_successIndex hr.infinite_success n]
    apply Finset.card_le_card
    intro i hi
    rw [EvaluationComplexity.mem_successfulIterations] at hi ⊢
    exact ⟨hi.1.trans_le hKN, hi.2⟩
  have hreal : ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤
      gap f fstar (x 0) / θ :=
    (show ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤ n by
      exact_mod_cast hcard).trans hnb
  have hmeasure := hr.measure_zero_of_gap_zero hd hzero
  refine ⟨K, hzero, hmeasure, ?_, fun j hj => hr.point_eq_after_zero hmeasure hj, hreal, ?_⟩
  · intro i hi
    exact lt_of_le_of_ne (hd.gap_nonneg _) (Ne.symm (Nat.find_min hex hi))
  · exact (hr.density K).trans (add_le_add
      (mul_le_mul_of_nonneg_left hreal (zero_le_one.trans hr.density_factor)) le_rfl)

end MeasureDomination
