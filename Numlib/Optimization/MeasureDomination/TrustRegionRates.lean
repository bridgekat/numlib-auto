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

/-- The first successful gap is exactly the initial objective gap. -/
theorem TRRun.successful_initial_gap (hr : TRRun f ψ x S ν κν κR κA) (a : ℝ) :
    successfulGap f a x S 0 = gap f a (x 0) := by
  rw [successfulGap, hr.first_success_point]

/-- At equal exponents the actual accepted gap has the exact source linear factor. -/
theorem TRRun.linear_decrease (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (heq : ν = μ) {k : ℕ} (hk : k ∈ S) :
    gap f fstar (x (k + 1)) ≤ (1 - κν / κψ) * gap f fstar (x k) := by
  have ht : ν / μ = 1 := by rw [heq, div_self (zero_lt_one.trans_le hd.level_ge_one).ne']
  have hh := hr.explicit_decrease hd hk
  simp only [ht, Real.rpow_one] at hh
  linarith

/-- A positive initial gap bounds the equal-exponent decrease coefficient by
the domination coefficient, before the first actual accepted trial. -/
theorem TRRun.linear_coefficient_le (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (heq : ν = μ) (hinit : 0 < gap f fstar (x 0)) :
    κν ≤ κψ := by
  have ht : ν / μ = 1 := by rw [heq, div_self (zero_lt_one.trans_le hd.level_ge_one).ne']
  have hstep := hr.successful_explicit_decrease hd
  simp only [ht, Real.rpow_one] at hstep
  have hp : 0 < successfulGap f fstar x S 0 := by
    rw [hr.successful_initial_gap fstar]
    exact hinit
  have hh := ExplicitGap.linear_coefficient_le_one
    (b := successfulGap f fstar x S) (c := κν / κψ) (fun n => hd.gap_nonneg _)
    (fun n => by simpa only [Real.rpow_one] using hstep n) hp
  exact (div_le_one hd.coefficient_pos).mp hh

/-- Equality of the linear decrease and domination coefficients attains the
minimum immediately after the first successful trial. -/
theorem TRRun.first_zero_of_equal_linear (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (heq : ν = μ) (hκ : κν = κψ) :
    gap f fstar (x (successIndex S 0 + 1)) = 0 := by
  have hh := hr.linear_decrease hd heq (successIndex_mem hr.infinite_success 0)
  rw [hκ, div_self hd.coefficient_pos.ne', sub_self, zero_mul] at hh
  exact le_antisymm hh (hd.gap_nonneg _)

/-- Below the domination level a positive initial gap is above the source threshold. -/
theorem TRRun.initial_threshold_le (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν < μ) (hinit : 0 < gap f fstar (x 0)) :
    trGapThreshold κψ κν μ ν ≤ gap f fstar (x 0) := by
  rw [←hr.successful_initial_gap fstar] at hinit ⊢
  exact hr.current_gap_ge_threshold hd hνμ (successIndex_mem hr.infinite_success 0) hinit

/-- Above the domination level a positive initial gap is below the source threshold. -/
theorem TRRun.initial_le_threshold (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ < ν) (hinit : 0 < gap f fstar (x 0)) :
    gap f fstar (x 0) ≤ trGapThreshold κψ κν μ ν := by
  rw [trGapThreshold_eq (zero_lt_one.trans_le hd.level_ge_one).ne' hμν.ne']
  have hp : 0 < successfulGap f fstar x S 0 := by
    rw [hr.successful_initial_gap fstar]
    exact hinit
  have hh := ExplicitGap.le_threshold_of_pos (b := successfulGap f fstar x S)
    (div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos (ν / μ)))
    ((one_lt_div (zero_lt_one.trans_le hd.level_ge_one)).mpr hμν)
    (fun _ => hd.gap_nonneg _) (hr.successful_explicit_decrease hd) hp
  simpa only [hr.successful_initial_gap fstar] using hh

/-- In either nonunit regime an initial gap exactly at the threshold attains
the minimum at the first successful endpoint. -/
theorem TRRun.first_zero_of_initial_threshold (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν ≠ μ)
    (hinit : gap f fstar (x 0) = trGapThreshold κψ κν μ ν) :
    gap f fstar (x (successIndex S 0 + 1)) = 0 := by
  have hμ : μ ≠ 0 := (zero_lt_one.trans_le hd.level_ge_one).ne'
  have ht : ν / μ ≠ 1 := by
    intro he
    exact hνμ ((div_eq_one_iff_eq hμ).mp he)
  have hb : successfulGap f fstar x S 0 =
      ExplicitGap.threshold (κν / κψ ^ (ν / μ)) (ν / μ) :=
    (hr.successful_initial_gap fstar).trans (hinit.trans (trGapThreshold_eq hμ hνμ))
  have hh := ExplicitGap.next_zero_of_eq_threshold (b := successfulGap f fstar x S)
    (div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos (ν / μ))) ht
    (fun _ => hd.gap_nonneg _) (hr.successful_explicit_decrease hd) hb
  simpa only [successfulGap, hr.next_success_point 0] using hh

/-- The final positive accepted gap is above the actual source threshold;
thereafter the method is at its unchanged exact terminal point. -/
theorem TRRun.last_positive_gap (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hνμ : ν < μ) (hinit : 0 < gap f fstar (x 0)) :
    ∃ k ∈ S, trGapThreshold κψ κν μ ν ≤ gap f fstar (x k) ∧
      (∀ i ≤ k, 0 < gap f fstar (x i)) ∧ gap f fstar (x (k + 1)) = 0 ∧
      ψ (x (k + 1)) = 0 ∧ ∀ j, k + 1 ≤ j → x j = x (k + 1) := by
  obtain ⟨K, hk, hψ, hfirst, hstop, _, _⟩ := hr.first_zero_budget hd hνμ
  have hK : 0 < K := by
    by_contra hn
    have he : K = 0 := by omega
    rw [he] at hk
    exact hinit.ne' hk
  let k := K - 1
  have he : k + 1 = K := by omega
  have hkS : k ∈ S := by
    by_contra hn
    have hx := hr.rejected k hn
    rw [he] at hx
    have hz : gap f fstar (x k) = 0 := by rw [←hx]; exact hk
    exact (hfirst k (by omega)).ne' hz
  refine ⟨k, hkS, hr.current_gap_ge_threshold hd hνμ hkS (hfirst k (by omega)),
    fun i hi => hfirst i (by omega), ?_, ?_, ?_⟩
  · simpa only [he] using hk
  · simpa only [he] using hψ
  · simpa only [he] using hstop

/-- Above the domination level, a genuine positive sublinear recurrence bounds
all successful gaps, including when actual attainment is faster. -/
theorem TRRun.successful_sublinear_envelope (hr : TRRun f ψ x S ν κν κR κA)
    (hd : Dominated f ψ fstar μ κψ) (hμν : μ < ν) :
    (∀ n, successfulGap f fstar x S n = 0) ∨
      ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧
        (∀ n, successfulGap f fstar x S n ≤ t n) ∧ Tendsto t atTop (nhds 0) ∧
        Tendsto (fun n => t (n + 1) / t n) atTop (nhds 1) :=
  ExplicitGap.sublinear_envelope
    (div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _))
    ((one_lt_div (zero_lt_one.trans_le hd.level_ge_one)).mpr hμν)
    (fun _ => hd.gap_nonneg _) (hr.successful_explicit_decrease hd)

end MeasureDomination
