import Numlib.Optimization.MeasureDominationRates
import NumlibSurface.CartisGouldToint.Chapter04.Section01
import Mathlib.Topology.Order.IntermediateValue

/-!
# Section 5.3: Measure-dominated problems

Successful points are indexed separately from attempted iterations. The chronological trace
is recovered from the actual number of accepted attempts; rejected attempts therefore leave
its point unchanged. Density is an assumption on accepted attempts, not a complexity result.
All oracle counts below exclude the initial evaluation.
-/

namespace CartisGouldToint.Chapter05.Section03

open Optimization.MeasureDomination

variable {n : ℕ}

/-- Domination (5.3.1) on a specified domain, including an iterate-restricted domain. -/
abbrev measureDomination (D : Set (EuclideanSpace ℝ (Fin n)))
    (f ψ : EuclideanSpace ℝ (Fin n) → ℝ) (fstar κψ μ : ℝ) : Prop :=
  IsMeasureDominated D f ψ fstar κψ μ

/-- The actual number of successful attempts before attempted iteration `k`. -/
def successfulCount (accepted : ℕ → Bool) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun j => accepted j = true)).card

@[simp] theorem successfulCount_zero (accepted : ℕ → Bool) : successfulCount accepted 0 = 0 := by
  simp [successfulCount]

/-- A rejected attempted iteration does not change the successful count. -/
theorem successfulCount_rejected (accepted : ℕ → Bool) {k : ℕ} (hk : accepted k = false) :
    successfulCount accepted (k + 1) = successfulCount accepted k := by
  simp [successfulCount, Finset.range_add_one, Finset.filter_insert, hk]

/-- An accepted attempt increases the actual successful prefix count by exactly one. -/
theorem successfulCount_accepted (accepted : ℕ → Bool) {k : ℕ} (hk : accepted k = true) :
    successfulCount accepted (k + 1) = successfulCount accepted k + 1 := by
  simp [successfulCount, Finset.range_add_one, Finset.filter_insert, hk]

/-- The minimum measure over the successful prefix, including its initial point. -/
noncomputable def runningMeasure (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (points : ℕ → EuclideanSpace ℝ (Fin n)) : ℕ → ℝ
  | 0 => ψ (points 0)
  | j + 1 => min (runningMeasure ψ points j) (ψ (points (j + 1)))

/-- A finite running minimum is attained at an actual earlier successful point. -/
theorem runningMeasure_attained (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (points : ℕ → EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    ∃ i ≤ j, runningMeasure ψ points j = ψ (points i) := by
  induction j with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ j ih =>
    rcases le_total (runningMeasure ψ points j) (ψ (points (j + 1))) with h | h
    · obtain ⟨i, hi, he⟩ := ih
      exact ⟨i, by omega, by simpa [runningMeasure, min_eq_left h] using he⟩
    · exact ⟨j + 1, le_rfl, min_eq_right h⟩

/-- The running minimum is at most its last measure. -/
theorem runningMeasure_le_current (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (points : ℕ → EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    runningMeasure ψ points j ≤ ψ (points j) := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact min_le_right _ _

/-- The generic AR and TR method classes of Section 5.3. The Boolean parameter selects
successor-measure (AR) or running-minimum (TR) sufficient decrease. `visit j` is an actual
prefix containing exactly `j` accepted attempts. -/
structure measureDecreaseRuns (successor : Bool) (D : Set (EuclideanSpace ℝ (Fin n)))
    (f ψ : EuclideanSpace ℝ (Fin n) → ℝ) (κν ν κR κA : ℝ) where
  points : ℕ → EuclideanSpace ℝ (Fin n)
  accepted : ℕ → Bool
  visit : ℕ → ℕ
  count_visit : ∀ j, successfulCount accepted (visit j) = j
  points_mem : ∀ j, points j ∈ D
  decrease_const_pos : 0 < κν
  exponent_pos : 0 < ν
  density_factor : 1 ≤ κR
  density_offset : 0 ≤ κA
  density : ∀ k : ℕ, (k : ℝ) ≤ κR * (successfulCount accepted k : ℝ) + κA
  decrease : ∀ j, κν * (if successor then ψ (points (j + 1))
      else runningMeasure ψ points j) ^ ν ≤
    f (points j) - f (points (j + 1))

namespace measureDecreaseRuns

variable {b : Bool} {D : Set (EuclideanSpace ℝ (Fin n))}
  {f ψ : EuclideanSpace ℝ (Fin n) → ℝ} {κν ν κR κA : ℝ}

/-- The actual iterate after a chronological prefix of attempted iterations. -/
def iterate (r : measureDecreaseRuns b D f ψ κν ν κR κA) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) := r.points (successfulCount r.accepted k)

/-- Rejected attempts leave the actual iterate unchanged. -/
theorem rejected_unchanged (r : measureDecreaseRuns b D f ψ κν ν κR κA)
    {k : ℕ} (hk : r.accepted k = false) : r.iterate (k + 1) = r.iterate k := by
  simp [iterate, successfulCount_rejected r.accepted hk]

/-- At `visit j`, there have been exactly `j` derivative evaluations and `visit j` function
calls. Applying the assumed density gives the chronological cost of `j` successes. -/
theorem visit_cost (r : measureDecreaseRuns b D f ψ κν ν κR κA) (j : ℕ) :
    successfulCount r.accepted (r.visit j) = j ∧
      (r.visit j : ℝ) ≤ κR * (j : ℝ) + κA := by
  exact ⟨r.count_visit j, by simpa [r.count_visit j] using r.density (r.visit j)⟩

@[simp] theorem iterate_visit (r : measureDecreaseRuns b D f ψ κν ν κR κA) (j : ℕ) :
    r.iterate (r.visit j) = r.points j := by simp [iterate, r.count_visit]

/-- Rejected points only repeat previous measures, so the chronological running
minimum equals the running minimum on the compressed successful prefix. -/
theorem runningMeasure_iterate (r : measureDecreaseRuns b D f ψ κν ν κR κA) (k : ℕ) :
    runningMeasure ψ r.iterate k = runningMeasure ψ r.points (successfulCount r.accepted k) := by
  induction k with
  | zero => simp [runningMeasure, iterate]
  | succ k ih =>
    cases hk : r.accepted k
    · rw [runningMeasure, ih, r.rejected_unchanged hk, iterate,
        successfulCount_rejected r.accepted hk]
      exact min_eq_left (runningMeasure_le_current ψ r.points _)
    · rw [runningMeasure, ih, iterate, successfulCount_accepted r.accepted hk,
        runningMeasure]

/-- On accepted chronological attempts, the run satisfies exactly (5.3.5) or (5.3.28),
with the minimum taken over all previous chronological iterates in the TR case. -/
theorem chronological_decrease (r : measureDecreaseRuns b D f ψ κν ν κR κA)
    {k : ℕ} (hk : r.accepted k = true) :
    κν * (if b then ψ (r.iterate (k + 1)) else runningMeasure ψ r.iterate k) ^ ν ≤
      f (r.iterate k) - f (r.iterate (k + 1)) := by
  have hh := r.decrease (successfulCount r.accepted k)
  simpa [r.runningMeasure_iterate k, iterate, successfulCount_accepted r.accepted hk] using hh

end measureDecreaseRuns

variable {D : Set (EuclideanSpace ℝ (Fin n))}
  {f ψ : EuclideanSpace ℝ (Fin n) → ℝ} {fstar κψ μ κν ν κR κA : ℝ}

/-- Lemma 5.3.1, the implicit gap recurrence (5.3.11) on the successful iterates. -/
theorem implicit_gap_step (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) (j : ℕ) :
    f (r.points (j + 1)) - fstar + κν / κψ ^ (ν / μ) *
      (f (r.points (j + 1)) - fstar) ^ (ν / μ) ≤ f (r.points j) - fstar := by
  exact implicit_gap_decrease hd r.exponent_pos.le r.decrease_const_pos.le
    (r.points_mem (j + 1)) (by simpa using r.decrease j)

/-- The gap is nonincreasing for both classes of monotone methods. -/
theorem gaps_antitone (hd : measureDomination D f ψ fstar κψ μ)
    {b : Bool} (r : measureDecreaseRuns b D f ψ κν ν κR κA) :
    Antitone (fun j => f (r.points j) - fstar) := by
  apply antitone_nat_of_succ_le
  intro j
  have hmeasure : 0 ≤ (if b then ψ (r.points (j + 1)) else runningMeasure ψ r.points j) := by
    cases b
    · obtain ⟨i, -, hi⟩ := runningMeasure_attained ψ r.points j
      simpa [hi] using hd.measure_nonneg _ (r.points_mem i)
    · exact hd.measure_nonneg _ (r.points_mem (j + 1))
  have hp := mul_nonneg r.decrease_const_pos.le (Real.rpow_nonneg hmeasure ν)
  linarith [r.decrease j]

/-- The explicit gap recurrence follows from the running-minimum law (5.3.28),
using domination at its attaining earlier point and monotonicity of the gaps. -/
theorem explicit_gap_step (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν ν κR κA) (j : ℕ) :
    f (r.points (j + 1)) - fstar ≤ f (r.points j) - fstar -
      κν / κψ ^ (ν / μ) * (f (r.points j) - fstar) ^ (ν / μ) := by
  obtain ⟨i, hi, he⟩ := runningMeasure_attained ψ r.points j
  have hcoef : 0 ≤ κν / κψ ^ (ν / μ) := div_nonneg r.decrease_const_pos.le
    (Real.rpow_nonneg hd.const_pos.le _)
  have hp := Real.rpow_le_rpow (hd.gap_nonneg _ (r.points_mem j))
    (gaps_antitone hd r hi) (div_nonneg r.exponent_pos.le hd.exponent_pos.le)
  have hm := mul_le_mul_of_nonneg_left hp hcoef
  have hs := scaled_gap_rpow_le (hd.gap_nonneg _ (r.points_mem i))
    (hd.measure_nonneg _ (r.points_mem i)) hd.const_pos hd.exponent_pos
    r.exponent_pos.le r.decrease_const_pos.le (hd.gap_le _ (r.points_mem i))
  have hr := r.decrease j
  simp only [Bool.false_eq_true, ite_false, he] at hr
  linarith

/-- Sufficient successor-measure decrease controls the next measure from the old gap. -/
theorem measure_of_gap (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) {ε : ℝ}
    (hε : 0 ≤ ε) (j : ℕ) (hgap : f (r.points j) - fstar ≤ κν * ε ^ ν) :
    ψ (r.points (j + 1)) ≤ ε := by
  have hpow : ψ (r.points (j + 1)) ^ ν ≤ ε ^ ν := by
    apply (mul_le_mul_iff_right₀ r.decrease_const_pos).mp
    have hlo := hd.gap_nonneg (r.points (j + 1)) (r.points_mem (j + 1))
    have hr := r.decrease j
    simp only [ite_true] at hr
    linarith
  exact (Real.rpow_le_rpow_iff (hd.measure_nonneg _ (r.points_mem _)) hε
    r.exponent_pos).mp hpow

/-- The positive coefficient obtained by eliminating the domination measure. -/
theorem gap_coefficient_pos (hd : measureDomination D f ψ fstar κψ μ)
    {b : Bool} (r : measureDecreaseRuns b D f ψ κν ν κR κA) :
    0 < κν / κψ ^ (ν / μ) := div_pos r.decrease_const_pos
      (Real.rpow_pos_of_pos hd.const_pos _)

/-- After any prescribed successful point, pretermination measure decrease bounds the
first measure-tolerant point or running minimum. The successor-point and running-minimum laws
use their respective tests, as in the proofs in Appendix B. -/
theorem measure_tolerance_after_gap (hd : measureDomination D f ψ fstar κψ μ)
    {b : Bool} (r : measureDecreaseRuns b D f ψ κν ν κR κA) {ε t : ℝ}
    (hε : 0 < ε) (N : ℕ) (hgap : f (r.points N) - fstar ≤ t) :
    ∃ k ≤ ⌊t / (κν * ε ^ ν)⌋₊,
      (if b then ψ (r.points (N + k + 1)) else runningMeasure ψ r.points (N + k)) ≤ ε := by
  have hδ : 0 < κν * ε ^ ν := mul_pos r.decrease_const_pos
    (Real.rpow_pos_of_pos hε _)
  have hdec : ∀ j, (∀ i ≤ j, ¬ (if b then ψ (r.points (N + i + 1))
      else runningMeasure ψ r.points (N + i)) ≤ ε) →
      κν * ε ^ ν ≤ (f (r.points (N + j)) - fstar) -
        (f (r.points (N + (j + 1))) - fstar) := by
    intro j hj
    have hmeasure := lt_of_not_ge (hj j le_rfl)
    have hp := Real.rpow_le_rpow hε.le hmeasure.le r.exponent_pos.le
    have hh := mul_le_mul_of_nonneg_left hp r.decrease_const_pos.le
    have hdesc := r.decrease (N + j)
    cases b <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_assoc] at * <;>
      linarith
  obtain ⟨k, hk, htest, -⟩ := Optimization.EvaluationComplexity.exists_first_of_decrease
    hδ (fun j => hd.gap_nonneg _ (r.points_mem (N + j))) hdec
  refine ⟨k, hk.trans ?_, htest⟩
  exact Nat.floor_le_floor ((div_le_div_iff_of_pos_right hδ).2 (by simpa using hgap))

/-- A finite-prefix outcome records actual successful and chronological oracle counts,
together with both termination tests at the displayed successful point. -/
def attained (r : measureDecreaseRuns true D f ψ κν ν κR κA)
    (ε : ℝ) (B : ℕ) : Prop :=
  ∃ j ≤ B, f (r.points j) - fstar ≤ ε ∧ ψ (r.points j) ≤ ε ∧
    successfulCount r.accepted (r.visit j) = j ∧ (r.visit j : ℝ) ≤ κR * B + κA

/-- A gap bound followed by the pretermination decrease argument gives both AR tests. -/
theorem ar_attained (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) {ε t : ℝ}
    (hε : 0 < ε) (htε : t ≤ ε) (N : ℕ) (hgap : f (r.points N) - fstar ≤ t) :
    attained (fstar := fstar) r ε (N + ⌊t / (κν * ε ^ ν)⌋₊ + 1) := by
  obtain ⟨k, hk, htest⟩ := measure_tolerance_after_gap hd r hε N hgap
  have hm := implicit_recurrence_antitone (gap_coefficient_pos hd r).le
    (fun j => hd.gap_nonneg _ (r.points_mem j)) (implicit_gap_step hd r)
  let j := N + k + 1
  have hj : j ≤ N + ⌊t / (κν * ε ^ ν)⌋₊ + 1 := by omega
  refine ⟨j, hj, (hm (by omega : N ≤ j)).trans (hgap.trans htε), ?_, r.count_visit j, ?_⟩
  · simpa [j] using htest
  · have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj : (j : ℝ) ≤ _)
      (zero_le_one.trans r.density_factor)
    linarith [(r.visit_cost j).2]

/-- The TR finite-prefix outcome has separate gap and earlier measure witnesses. -/
def trAttained (r : measureDecreaseRuns false D f ψ κν ν κR κA)
    (ε : ℝ) (B : ℕ) : Prop :=
  ∃ j ≤ B, f (r.points j) - fstar ≤ ε ∧ (∃ i ≤ j, ψ (r.points i) ≤ ε ∧
      successfulCount r.accepted (r.visit i) = i ∧ (r.visit i : ℝ) ≤ κR * B + κA) ∧
    successfulCount r.accepted (r.visit j) = j ∧ (r.visit j : ℝ) ≤ κR * B + κA

/-- A gap bound followed by the running-minimum pretermination law gives both TR tests. -/
theorem tr_attained (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν ν κR κA) {ε t : ℝ}
    (hε : 0 < ε) (htε : t ≤ ε) (N : ℕ) (hgap : f (r.points N) - fstar ≤ t) :
    trAttained (fstar := fstar) r ε (N + ⌊t / (κν * ε ^ ν)⌋₊) := by
  obtain ⟨k, hk, htest⟩ := measure_tolerance_after_gap hd r hε N hgap
  have hm := explicit_recurrence_antitone (gap_coefficient_pos hd r).le
    (fun j => hd.gap_nonneg _ (r.points_mem j)) (explicit_gap_step hd r)
  let j := N + k
  have hj : j ≤ N + ⌊t / (κν * ε ^ ν)⌋₊ := by omega
  refine ⟨j, hj, (hm (by omega : N ≤ j)).trans (hgap.trans htε), ?_, r.count_visit j, ?_⟩
  · obtain ⟨i, hi, he⟩ := runningMeasure_attained ψ r.points j
    refine ⟨i, hi, ?_, r.count_visit i, ?_⟩
    · simpa [j, he] using htest
    · have hh := mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (hi.trans hj) : (i : ℝ) ≤ _)
        (zero_le_one.trans r.density_factor)
      linarith [(r.visit_cost i).2]
  · have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj : (j : ℝ) ≤ _)
      (zero_le_one.trans r.density_factor)
    linarith [(r.visit_cost j).2]

/-- The small gap target used to obtain gap and measure complexity simultaneously. -/
noncomputable def gapTarget (μ ε : ℝ) : ℝ := min ε (ε ^ μ)

/-- The gap target is positive for every positive tolerance. -/
theorem gapTarget_pos {μ ε : ℝ} (hε : 0 < ε) : 0 < gapTarget μ ε :=
  lt_min hε (Real.rpow_pos_of_pos hε _)

/-- Theorem 5.3.4: linear implicit descent gives logarithmic gap and measure complexity,
including integer rounding, actual successful counts, and chronological function calls. -/
theorem theorem_5_3_4_complexity (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν μ κR κA) {ε : ℝ} (hε : 0 < ε) :
    let N := geometricIterationCount (f (r.points 0) - fstar) (1 + κν / κψ)
      (gapTarget μ ε)
    attained (fstar := fstar) r ε (N + ⌊gapTarget μ ε / (κν * ε ^ μ)⌋₊ + 1) := by
  dsimp only
  apply ar_attained hd r hε (min_le_left _ _)
  change _ ≤ gapTarget μ ε
  apply implicit_recurrence_linear_tolerance
    (u := fun j => f (r.points j) - fstar) (div_pos r.decrease_const_pos hd.const_pos)
    (gapTarget_pos hε) _ le_rfl
  intro j
  simpa [div_self hd.exponent_pos.ne', Real.rpow_one] using implicit_gap_step hd r j

/-- Theorem 5.3.5: polynomial implicit descent gives both tolerance tests. At small
`ε≤1` and `μ≥1`, the two budget terms have order `ε ^ (-(ν-μ))`. -/
theorem theorem_5_3_5_complexity (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) (hμν : μ < ν)
    {ε : ℝ} (hε : 0 < ε) :
    let a := κν / κψ ^ (ν / μ)
    let N := polynomialIterationCount
      (implicitPolynomialConstant (f (r.points 0) - fstar) a (ν / μ)) (ν / μ) (gapTarget μ ε)
    attained (fstar := fstar) r ε (N + ⌊gapTarget μ ε / (κν * ε ^ ν)⌋₊ + 1) := by
  dsimp only
  apply ar_attained hd r hε (min_le_left _ _)
  apply implicit_recurrence_polynomial_tolerance (gap_coefficient_pos hd r)
    ((one_lt_div hd.exponent_pos).2 hμν) (gapTarget_pos hε)
    (fun j => hd.gap_nonneg _ (r.points_mem j)) (implicit_gap_step hd r)
  exact Or.inr le_rfl

/-- Theorem 5.3.8: running-minimum linear descent includes immediate termination
for the exceptional coefficient and logarithmic complexity otherwise. -/
theorem theorem_5_3_8_complexity (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν μ κR κA) {ε : ℝ} (hε : 0 < ε) :
    let N := explicitLinearIterationCount (f (r.points 0) - fstar) (κν / κψ)
      (gapTarget μ ε)
    trAttained (fstar := fstar) r ε (N + ⌊gapTarget μ ε / (κν * ε ^ μ)⌋₊) := by
  dsimp only
  apply tr_attained hd r hε (min_le_left _ _)
  change _ ≤ gapTarget μ ε
  apply explicit_recurrence_linear_tolerance
    (u := fun j => f (r.points j) - fstar) (div_pos r.decrease_const_pos hd.const_pos)
    (gapTarget_pos hε) (fun j => hd.gap_nonneg _ (r.points_mem j)) _ le_rfl
  intro j
  simpa [div_self hd.exponent_pos.ne', Real.rpow_one] using explicit_gap_step hd r j

/-- Theorem 5.3.9: polynomial running-minimum descent gives both gap and measure
tolerances, with power-law successful and chronological evaluation budgets. -/
theorem theorem_5_3_9_complexity (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν ν κR κA) (hμν : μ < ν)
    {ε : ℝ} (hε : 0 < ε) :
    let a := κν / κψ ^ (ν / μ)
    let N := polynomialIterationCount (a * (ν / μ - 1)) (ν / μ) (gapTarget μ ε)
    trAttained (fstar := fstar) r ε (N + ⌊gapTarget μ ε / (κν * ε ^ ν)⌋₊) := by
  dsimp only
  apply tr_attained hd r hε (min_le_left _ _)
  exact explicit_recurrence_polynomial_tolerance (gap_coefficient_pos hd r)
    ((one_lt_div hd.exponent_pos).2 hμν) (gapTarget_pos hε)
    (fun j => hd.gap_nonneg _ (r.points_mem j)) (explicit_gap_step hd r) le_rfl

/-- Theorem 5.3.3: after a tolerance-independent entry phase, subunit implicit descent
has a logarithm-of-logarithm gap and measure evaluation budget. -/
theorem theorem_5_3_3_complexity (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) (hνμ : ν < μ) :
    let a := κν / κψ ^ (ν / μ)
    let τ := ν / μ
    let B := a ^ (1 / (1 - τ))
    ∃ m ≤ ⌊(f (r.points 0) - fstar) / (a * (B / 2) ^ τ)⌋₊ + 1,
      ∀ ε > 0, attained (fstar := fstar) r ε
        (m + superlinearIterationCount B (1 / 2) (1 / τ) (gapTarget μ ε) +
          ⌊gapTarget μ ε / (κν * ε ^ ν)⌋₊ + 1) := by
  dsimp only
  obtain ⟨m, hm, -, htol⟩ := implicit_recurrence_superlinear_bound
    (gap_coefficient_pos hd r) (div_pos r.exponent_pos hd.exponent_pos)
    ((div_lt_one hd.exponent_pos).2 hνμ)
    (fun j => hd.gap_nonneg _ (r.points_mem j)) (implicit_gap_step hd r)
  refine ⟨m, hm, ?_⟩
  intro ε hε
  apply ar_attained hd r hε (min_le_left _ _)
  exact htol (gapTarget μ ε) (gapTarget_pos hε) _ le_rfl

/-- Theorem 5.3.7: subunit explicit descent reaches zero gap and zero measure within
a bound independent of the requested tolerance, including chronological function calls. -/
theorem theorem_5_3_7_complexity (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν ν κR κA) (hνμ : ν < μ) :
    let a := κν / κψ ^ (ν / μ)
    let N := ⌊(f (r.points 0) - fstar) / a ^ (1 / (1 - ν / μ))⌋₊ + 1
    f (r.points N) - fstar = 0 ∧
      (∃ i ≤ N, f (r.points i) - fstar = 0 ∧ ψ (r.points i) = 0 ∧
        successfulCount r.accepted (r.visit i) = i ∧ (r.visit i : ℝ) ≤ κR * N + κA) ∧
      successfulCount r.accepted (r.visit N) = N ∧
      (r.visit N : ℝ) ≤ κR * N + κA := by
  dsimp only
  let N := ⌊(f (r.points 0) - fstar) /
    (κν / κψ ^ (ν / μ)) ^ (1 / (1 - ν / μ))⌋₊ + 1
  have hgap : f (r.points N) - fstar = 0 :=
    explicit_recurrence_finite_termination (gap_coefficient_pos hd r)
      (div_pos r.exponent_pos hd.exponent_pos) ((div_lt_one hd.exponent_pos).2 hνμ)
      (fun j => hd.gap_nonneg _ (r.points_mem j)) (explicit_gap_step hd r) N le_rfl
  obtain ⟨i, hi, he⟩ := runningMeasure_attained ψ r.points N
  have hp : κν * ψ (r.points i) ^ ν ≤ 0 := by
    have hr := r.decrease N
    simp only [Bool.false_eq_true, ite_false, he] at hr
    linarith [hd.gap_nonneg _ (r.points_mem (N + 1))]
  have hz : ψ (r.points i) = 0 := by
    by_contra hne
    have hpos := lt_of_le_of_ne (hd.measure_nonneg _ (r.points_mem i)) (Ne.symm hne)
    have := mul_pos r.decrease_const_pos (Real.rpow_pos_of_pos hpos ν)
    linarith
  have hgi : f (r.points i) - fstar = 0 := by
    have hh := hd.gap_le _ (r.points_mem i)
    rw [hz, Real.zero_rpow hd.exponent_pos.ne', mul_zero] at hh
    exact le_antisymm hh (hd.gap_nonneg _ (r.points_mem i))
  have hicost : (r.visit i : ℝ) ≤ κR * N + κA := by
    have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hi : (i : ℝ) ≤ N)
      (zero_le_one.trans r.density_factor)
    linarith [(r.visit_cost i).2]
  exact ⟨hgap, ⟨i, hi, hgi, hz, r.count_visit i, hicost⟩, r.visit_cost N⟩

/-- The implicit scalar equation has exactly one nonnegative root. For positive right
hand side the root is positive; no root is assumed as input to the recurrence. -/
theorem implicit_root_exists_unique {a τ t : ℝ} (ha : 0 < a) (hτ : 0 < τ) (ht : 0 ≤ t) :
    ∃! w : ℝ, 0 ≤ w ∧ w + a * w ^ τ = t := by
  have hc : ContinuousOn (fun w : ℝ => w + a * w ^ τ) (Set.Icc 0 t) := by
    exact continuousOn_id.add (continuousOn_const.mul
      (ContinuousOn.rpow_const continuousOn_id (fun w hw => Or.inr hτ.le)))
  have hleft : (0 : ℝ) + a * (0 : ℝ) ^ τ ≤ t := by
    simpa [Real.zero_rpow hτ.ne'] using ht
  have hright : t ≤ t + a * t ^ τ := by
    have := mul_nonneg ha.le (Real.rpow_nonneg ht τ)
    linarith
  obtain ⟨w, hw, hwe⟩ := intermediate_value_Icc ht hc ⟨hleft, hright⟩
  refine ⟨w, ⟨hw.1, hwe⟩, ?_⟩
  intro z hz
  by_contra hne
  rcases lt_or_gt_of_ne hne with hzw | hwz
  · have hp := Real.rpow_le_rpow hz.1 hzw.le hτ.le
    nlinarith [hz.2]
  · have hp := Real.rpow_le_rpow hw.1 hwz.le hτ.le
    nlinarith [hz.2]

/-- The uniquely constructed nonnegative implicit scalar step. -/
noncomputable def implicitGapStep (a τ t : ℝ) : ℝ :=
  if h : 0 < a ∧ 0 < τ ∧ 0 ≤ t then
    (implicit_root_exists_unique h.1 h.2.1 h.2.2).choose else 0

/-- The defining equation and sign of the chosen implicit step. -/
theorem implicitGapStep_spec {a τ t : ℝ} (ha : 0 < a) (hτ : 0 < τ) (ht : 0 ≤ t) :
    0 ≤ implicitGapStep a τ t ∧
      implicitGapStep a τ t + a * implicitGapStep a τ t ^ τ = t := by
  rw [implicitGapStep, dite_eq_left ⟨ha, hτ, ht⟩]
  exact (implicit_root_exists_unique ha hτ ht).choose_spec.1

/-- The positive scalar comparison recurrence (5.3.12), extended to zero initial gaps. -/
noncomputable def implicitGapRecurrence (a τ t0 : ℝ) : ℕ → ℝ
  | 0 => t0
  | k + 1 => implicitGapStep a τ (implicitGapRecurrence a τ t0 k)

/-- Every comparison gap is nonnegative and satisfies the exact recurrence. -/
theorem implicitGapRecurrence_spec {a τ t0 : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (ht0 : 0 ≤ t0) :
    (∀ k, 0 ≤ implicitGapRecurrence a τ t0 k) ∧
    (∀ k, implicitGapRecurrence a τ t0 (k + 1) +
      a * implicitGapRecurrence a τ t0 (k + 1) ^ τ = implicitGapRecurrence a τ t0 k) := by
  have hn : ∀ k, 0 ≤ implicitGapRecurrence a τ t0 k := by
    intro k
    induction k with
    | zero => exact ht0
    | succ k ih => exact (implicitGapStep_spec ha hτ ih).1
  exact ⟨hn, fun k => (implicitGapStep_spec ha hτ (hn k)).2⟩

/-- A positive initial scalar gap gives positive comparison gaps at every finite index. -/
theorem implicitGapRecurrence_pos {a τ t0 : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (ht0 : 0 < t0) (k : ℕ) : 0 < implicitGapRecurrence a τ t0 k := by
  have hs := implicitGapRecurrence_spec ha hτ ht0.le
  induction k with
  | zero => exact ht0
  | succ k ih =>
    apply lt_of_le_of_ne (hs.1 (k + 1))
    intro he
    have hh := hs.2 k
    rw [← he, Real.zero_rpow hτ.ne', mul_zero, add_zero] at hh
    linarith

/-- The scalar comparison sequence reaches every positive tolerance. -/
theorem implicitGapRecurrence_hits {a τ t0 ε : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (ht0 : 0 ≤ t0) (hε : 0 < ε) : ∃ k, implicitGapRecurrence a τ t0 k ≤ ε := by
  have hs := implicitGapRecurrence_spec ha hτ ht0
  obtain ⟨m, -, hm⟩ := implicit_recurrence_entry ha hτ hε hs.1 (fun j => (hs.2 j).le)
  exact ⟨m, hm⟩

/-- The first scalar tolerance hitting count (5.3.13). -/
noncomputable def implicitHittingCount (a τ t0 ε : ℝ) : ℕ := by
  classical
  exact if h : ∃ k, implicitGapRecurrence a τ t0 k ≤ ε then Nat.find h else 0

/-- The constructed scalar hitting count is an actual first hitting count. -/
theorem implicitHittingCount_spec {a τ t0 ε : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (ht0 : 0 ≤ t0) (hε : 0 < ε) :
    implicitGapRecurrence a τ t0 (implicitHittingCount a τ t0 ε) ≤ ε ∧
      ∀ j < implicitHittingCount a τ t0 ε, ε < implicitGapRecurrence a τ t0 j := by
  classical
  have he := implicitGapRecurrence_hits ha hτ ht0 hε
  rw [implicitHittingCount, dite_eq_left he]
  exact ⟨Nat.find_spec he, fun j hj => lt_of_not_ge (Nat.find_min he hj)⟩

/-- Implicit recurrence inequalities are bounded above by the exact scalar solution. -/
theorem implicitGapRecurrence_comparison {u : ℕ → ℝ} {a τ : ℝ}
    (ha : 0 < a) (hτ : 0 < τ) (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) + a * u (k + 1) ^ τ ≤ u k) (k : ℕ) :
    u k ≤ implicitGapRecurrence a τ (u 0) k := by
  have hs := implicitGapRecurrence_spec ha hτ (hu 0)
  induction k with
  | zero => rfl
  | succ k ih =>
    by_contra hh
    have hlt := lt_of_not_ge hh
    have hp := Real.rpow_le_rpow (hs.1 (k + 1)) hlt.le hτ.le
    nlinarith [hstep k, hs.2 k]

/-- Theorem 5.3.2: the first scalar comparison hit bounds successful evaluations,
and the assumed density converts this to actual chronological function calls. -/
theorem theorem_5_3_2 (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) {ε : ℝ} (hε : 0 < ε) :
    let N := implicitHittingCount (κν / κψ ^ (ν / μ)) (ν / μ)
      (f (r.points 0) - fstar) ε
    f (r.iterate (r.visit N)) - fstar ≤ ε ∧
      successfulCount r.accepted (r.visit N) = N ∧ (r.visit N : ℝ) ≤ κR * N + κA := by
  dsimp only
  rw [r.iterate_visit]
  refine ⟨?_, r.visit_cost _⟩
  exact (implicitGapRecurrence_comparison (gap_coefficient_pos hd r)
    (div_pos r.exponent_pos hd.exponent_pos) (fun j => hd.gap_nonneg _ (r.points_mem j))
    (implicit_gap_step hd r) _).trans
    (implicitHittingCount_spec (gap_coefficient_pos hd r)
      (div_pos r.exponent_pos hd.exponent_pos) (hd.gap_nonneg _ (r.points_mem 0)) hε).1

/-- The gap-only evaluation conclusion, retaining its sharper tolerance exponent. -/
def gapAttained {b : Bool} (r : measureDecreaseRuns b D f ψ κν ν κR κA)
    (ε : ℝ) (N : ℕ) : Prop :=
  f (r.iterate (r.visit N)) - fstar ≤ ε ∧
    successfulCount r.accepted (r.visit N) = N ∧ (r.visit N : ℝ) ≤ κR * N + κA

/-- A successful-gap bound transfers to the actual chronological iterate and oracle counts. -/
theorem gap_attained {b : Bool} (r : measureDecreaseRuns b D f ψ κν ν κR κA)
    {ε : ℝ} {N : ℕ} (hgap : f (r.points N) - fstar ≤ ε) :
    gapAttained (fstar := fstar) r ε N := by
  exact ⟨by simpa using hgap, r.visit_cost N⟩

/-- The gap-only part of Theorem 5.3.4 has a logarithmic successful iteration count. -/
theorem theorem_5_3_4_gap (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν μ κR κA) {ε : ℝ} (hε : 0 < ε) :
    gapAttained (fstar := fstar) r ε
      (geometricIterationCount (f (r.points 0) - fstar) (1 + κν / κψ) ε) := by
  apply gap_attained
  apply implicit_recurrence_linear_tolerance (u := fun j => f (r.points j) - fstar)
    (div_pos r.decrease_const_pos hd.const_pos) hε _ le_rfl
  intro j
  simpa [div_self hd.exponent_pos.ne', Real.rpow_one] using implicit_gap_step hd r j

/-- The gap-only part of Theorem 5.3.5 has order `ε ^ (-(ν-μ)/μ)`,
while the measure conclusion of `theorem_5_3_5` has order `ε ^ (-(ν-μ))`. -/
theorem theorem_5_3_5_gap (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) (hμν : μ < ν)
    {ε : ℝ} (hε : 0 < ε) :
    gapAttained (fstar := fstar) r ε (polynomialIterationCount
      (implicitPolynomialConstant (f (r.points 0) - fstar)
        (κν / κψ ^ (ν / μ)) (ν / μ)) (ν / μ) ε) := by
  apply gap_attained
  exact implicit_recurrence_polynomial_tolerance (gap_coefficient_pos hd r)
    ((one_lt_div hd.exponent_pos).2 hμν) hε
    (fun j => hd.gap_nonneg _ (r.points_mem j)) (implicit_gap_step hd r) (Or.inr le_rfl)

/-- The gap-only part of Theorem 5.3.8 includes the exceptional one-step case. -/
theorem theorem_5_3_8_gap (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν μ κR κA) {ε : ℝ} (hε : 0 < ε) :
    gapAttained (fstar := fstar) r ε
      (explicitLinearIterationCount (f (r.points 0) - fstar) (κν / κψ) ε) := by
  apply gap_attained
  apply explicit_recurrence_linear_tolerance (u := fun j => f (r.points j) - fstar)
    (div_pos r.decrease_const_pos hd.const_pos) hε
    (fun j => hd.gap_nonneg _ (r.points_mem j)) _ le_rfl
  intro j
  simpa [div_self hd.exponent_pos.ne', Real.rpow_one] using explicit_gap_step hd r j

/-- The gap-only part of Theorem 5.3.9 retains the sharper gap exponent. -/
theorem theorem_5_3_9_gap (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν ν κR κA) (hμν : μ < ν)
    {ε : ℝ} (hε : 0 < ε) :
    gapAttained (fstar := fstar) r ε (polynomialIterationCount
      ((κν / κψ ^ (ν / μ)) * (ν / μ - 1)) (ν / μ) ε) := by
  apply gap_attained
  exact explicit_recurrence_polynomial_tolerance (gap_coefficient_pos hd r)
    ((one_lt_div hd.exponent_pos).2 hμν) hε
    (fun j => hd.gap_nonneg _ (r.points_mem j)) (explicit_gap_step hd r) le_rfl

/-- The gap-only part of Theorem 5.3.3 has the double-logarithmic tolerance budget. -/
theorem theorem_5_3_3_gap (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) (hνμ : ν < μ) :
    let a := κν / κψ ^ (ν / μ)
    let τ := ν / μ
    let B := a ^ (1 / (1 - τ))
    ∃ m ≤ ⌊(f (r.points 0) - fstar) / (a * (B / 2) ^ τ)⌋₊ + 1,
      ∀ ε > 0, gapAttained (fstar := fstar) r ε
        (m + superlinearIterationCount B (1 / 2) (1 / τ) ε) := by
  dsimp only
  obtain ⟨m, hm, -, htol⟩ := implicit_recurrence_superlinear_bound
    (gap_coefficient_pos hd r) (div_pos r.exponent_pos hd.exponent_pos)
    ((div_lt_one hd.exponent_pos).2 hνμ)
    (fun j => hd.gap_nonneg _ (r.points_mem j)) (implicit_gap_step hd r)
  exact ⟨m, hm, fun ε hε => gap_attained r (htol ε hε _ le_rfl)⟩

/-- Lemma 5.3.1: the implicit gap recurrence and all three upper-rate regimes.
The rate interface records a superlinear upper envelope, the exact linear contraction,
and polynomial upper decay; exact zeros and faster convergence remain possible. -/
theorem lemma_5_3_1 (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) :
    (∀ j, f (r.points (j + 1)) - fstar + κν / κψ ^ (ν / μ) *
      (f (r.points (j + 1)) - fstar) ^ (ν / μ) ≤ f (r.points j) - fstar) ∧
    ImplicitRateBounds (fun j => f (r.points j) - fstar)
      (κν / κψ ^ (ν / μ)) (ν / μ) :=
  ⟨implicit_gap_step hd r, implicit_recurrence_rate_bounds (gap_coefficient_pos hd r)
    (div_pos r.exponent_pos hd.exponent_pos) (fun j => hd.gap_nonneg _ (r.points_mem j))
    (implicit_gap_step hd r)⟩

/-- Lemma 5.3.6: the running-minimum law gives the explicit gap recurrence and
all three rate regimes. Its interface includes the positive-initial-gap feasibility bound,
the exceptional linear coefficient, threshold equality forcing the first successor to zero,
finite extinction below the unit exponent, and polynomial upper decay above it. The threshold
is normalized as `a ^ (1/(1-τ))`, with `a=κν/κψ^(ν/μ)` and `τ=ν/μ`. -/
theorem lemma_5_3_6 (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν ν κR κA) :
    (∀ j, f (r.points (j + 1)) - fstar ≤ f (r.points j) - fstar -
      κν / κψ ^ (ν / μ) * (f (r.points j) - fstar) ^ (ν / μ)) ∧
    ExplicitRateBounds (fun j => f (r.points j) - fstar)
      (κν / κψ ^ (ν / μ)) (ν / μ) :=
  ⟨explicit_gap_step hd r, explicit_recurrence_rate_bounds (gap_coefficient_pos hd r)
    (div_pos r.exponent_pos hd.exponent_pos) (fun j => hd.gap_nonneg _ (r.points_mem j))
    (explicit_gap_step hd r)⟩

/-- Complete rate and evaluation-budget conclusions of Theorem 5.3.3. -/
theorem theorem_5_3_3 (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) (hνμ : ν < μ) :
    ImplicitRateBounds (fun j => f (r.points j) - fstar)
      (κν / κψ ^ (ν / μ)) (ν / μ) ∧
    let a := κν / κψ ^ (ν / μ)
    let τ := ν / μ
    let B := a ^ (1 / (1 - τ))
    ∃ m ≤ ⌊(f (r.points 0) - fstar) / (a * (B / 2) ^ τ)⌋₊ + 1,
      ∀ ε > 0, attained (fstar := fstar) r ε
        (m + superlinearIterationCount B (1 / 2) (1 / τ) (gapTarget μ ε) +
          ⌊gapTarget μ ε / (κν * ε ^ ν)⌋₊ + 1) := by
  exact ⟨(lemma_5_3_1 hd r).2, theorem_5_3_3_complexity hd r hνμ⟩

/-- Complete rate and evaluation-budget conclusions of Theorem 5.3.4. -/
theorem theorem_5_3_4 (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν μ κR κA) {ε : ℝ} (hε : 0 < ε) :
    ImplicitRateBounds (fun j => f (r.points j) - fstar)
      (κν / κψ ^ (μ / μ)) (μ / μ) ∧
    let N := geometricIterationCount (f (r.points 0) - fstar) (1 + κν / κψ)
      (gapTarget μ ε)
    attained (fstar := fstar) r ε (N + ⌊gapTarget μ ε / (κν * ε ^ μ)⌋₊ + 1) := by
  exact ⟨(lemma_5_3_1 hd r).2, theorem_5_3_4_complexity hd r hε⟩

/-- Complete rate and evaluation-budget conclusions of Theorem 5.3.5. -/
theorem theorem_5_3_5 (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns true D f ψ κν ν κR κA) (hμν : μ < ν)
    {ε : ℝ} (hε : 0 < ε) :
    ImplicitRateBounds (fun j => f (r.points j) - fstar)
      (κν / κψ ^ (ν / μ)) (ν / μ) ∧
    let a := κν / κψ ^ (ν / μ)
    let N := polynomialIterationCount
      (implicitPolynomialConstant (f (r.points 0) - fstar) a (ν / μ)) (ν / μ) (gapTarget μ ε)
    attained (fstar := fstar) r ε (N + ⌊gapTarget μ ε / (κν * ε ^ ν)⌋₊ + 1) := by
  exact ⟨(lemma_5_3_1 hd r).2, theorem_5_3_5_complexity hd r hμν hε⟩

/-- Complete rate and evaluation-budget conclusions of Theorem 5.3.7. -/
theorem theorem_5_3_7 (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν ν κR κA) (hνμ : ν < μ) :
    ExplicitRateBounds (fun j => f (r.points j) - fstar)
      (κν / κψ ^ (ν / μ)) (ν / μ) ∧
    let a := κν / κψ ^ (ν / μ)
    let N := ⌊(f (r.points 0) - fstar) / a ^ (1 / (1 - ν / μ))⌋₊ + 1
    f (r.points N) - fstar = 0 ∧
      (∃ i ≤ N, f (r.points i) - fstar = 0 ∧ ψ (r.points i) = 0 ∧
        successfulCount r.accepted (r.visit i) = i ∧ (r.visit i : ℝ) ≤ κR * N + κA) ∧
      successfulCount r.accepted (r.visit N) = N ∧
      (r.visit N : ℝ) ≤ κR * N + κA := by
  exact ⟨(lemma_5_3_6 hd r).2, theorem_5_3_7_complexity hd r hνμ⟩

/-- Complete rate and evaluation-budget conclusions of Theorem 5.3.8. -/
theorem theorem_5_3_8 (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν μ κR κA) {ε : ℝ} (hε : 0 < ε) :
    ExplicitRateBounds (fun j => f (r.points j) - fstar)
      (κν / κψ ^ (μ / μ)) (μ / μ) ∧
    let N := explicitLinearIterationCount (f (r.points 0) - fstar) (κν / κψ)
      (gapTarget μ ε)
    trAttained (fstar := fstar) r ε (N + ⌊gapTarget μ ε / (κν * ε ^ μ)⌋₊) := by
  exact ⟨(lemma_5_3_6 hd r).2, theorem_5_3_8_complexity hd r hε⟩

/-- Complete rate and evaluation-budget conclusions of Theorem 5.3.9. -/
theorem theorem_5_3_9 (hd : measureDomination D f ψ fstar κψ μ)
    (r : measureDecreaseRuns false D f ψ κν ν κR κA) (hμν : μ < ν)
    {ε : ℝ} (hε : 0 < ε) :
    ExplicitRateBounds (fun j => f (r.points j) - fstar)
      (κν / κψ ^ (ν / μ)) (ν / μ) ∧
    let a := κν / κψ ^ (ν / μ)
    let N := polynomialIterationCount (a * (ν / μ - 1)) (ν / μ) (gapTarget μ ε)
    trAttained (fstar := fstar) r ε (N + ⌊gapTarget μ ε / (κν * ε ^ ν)⌋₊) := by
  exact ⟨(lemma_5_3_6 hd r).2, theorem_5_3_9_complexity hd r hμν hε⟩

end CartisGouldToint.Chapter05.Section03
