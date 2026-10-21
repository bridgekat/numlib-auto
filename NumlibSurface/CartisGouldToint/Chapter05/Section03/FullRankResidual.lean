import Numlib.Optimization.ResidualPowerRates
import NumlibSurface.CartisGouldToint.Chapter05.Section01
import NumlibSurface.CartisGouldToint.Chapter05.Section03

/-!
# Full-rank residual applications of Section 5.3

The residual objective is the earlier Section 5.1 definition. Full row rank means the
Jacobian transpose is uniformly bounded below. The run is the actual accepted/rejected
method class of Section 5.3, with the actual gradient norm as measure. Counts include the
initial residual/function and derivative evaluation, in addition to chronological trials
and cached derivatives at accepted iterates.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section03
open Optimization Optimization.MeasureDomination

variable {n m : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
  {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
  {σ ell κν ν κR κA : ℝ}

/-- A residual method uses the actual norm-power objective and its actual first derivative
measure, in either the successor-measure AR or running-minimum TR class. -/
abbrev residualDecreaseRun (successor : Bool) (D : Set (EuclideanSpace ℝ (Fin n)))
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ell κν ν κR κA : ℝ) :=
  measureDecreaseRuns successor D (Section01.residualPowerObjective r ell)
    (fun x => ‖gradient (Section01.residualPowerObjective r ell) x‖) κν ν κR κA

/-- Actual attainment of the residual tolerance with chronological function/residual calls
and accepted-iterate derivative queries, each including its initial query. -/
def residualAttained {b : Bool} (run : residualDecreaseRun b D r ell κν ν κR κA)
    (ε : ℝ) (N : ℕ) : Prop :=
  ‖r (run.iterate (run.visit N))‖ ≤ ε ∧
    successfulCount run.accepted (run.visit N) = N ∧
    (run.visit N : ℝ) + 1 ≤ κR * (N : ℝ) + κA + 1

/-- The residual attainment interface exposes the tolerance and the exact successful
count, with the chronological function-call bound including initialization. -/
@[simp] theorem residualAttained_iff {b : Bool}
    (run : residualDecreaseRun b D r ell κν ν κR κA) (ε : ℝ) (N : ℕ) :
    residualAttained run ε N ↔
      ‖r (run.iterate (run.visit N))‖ ≤ ε ∧
        successfulCount run.accepted (run.visit N) = N ∧
        (run.visit N : ℝ) + 1 ≤ κR * (N : ℝ) + κA + 1 := Iff.rfl

/-- An objective bound at a successful point is an actual residual attainment, with all
rejection and initialization costs retained. -/
theorem residual_attained {b : Bool} (run : residualDecreaseRun b D r ell κν ν κR κA)
    (hell : 0 < ell) {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ}
    (hgap : Section01.residualPowerObjective r ell (run.points N) ≤ ε ^ ell / ell) :
    residualAttained run ε N := by
  refine ⟨?_, run.count_visit N, ?_⟩
  · rw [run.iterate_visit]
    exact (residualPowerObjective_le_iff hell hε _).mp hgap
  · linarith [(run.visit_cost N).2]

/-- Theorem 5.3.10: the actual full-rank residual converges Q-superlinearly to zero,
with a zero-safe consecutive contraction coefficient tending to zero, a superlinear envelope
and uniform double-logarithmic evaluation budgets. The explicit small-tolerance range is
`0 < ε ≤ exp (-1)`. Constants are independent of the tolerance and initialization is counted. -/
theorem theorem_5_3_10 (ell p : ℕ) (hell : Even ell ∧ 2 ≤ ell ∧ ell ≤ p)
    (hr : HasUniformlyFullRankDerivative D r σ)
    (run : residualDecreaseRun true D r (ell : ℝ) κν (((p : ℝ) + 1) / p) κR κA) :
    let μ := (ell : ℝ) / ((ell : ℝ) - 1)
    let ν := ((p : ℝ) + 1) / p
    let a := κν / (residualDominationConstant ell σ) ^ (ν / μ)
    let τ := ν / μ
    let scale := a ^ (1 / (1 - τ))
    (Filter.Tendsto (fun j => ‖r (run.points j)‖) Filter.atTop (nhds 0) ∧
      ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ Filter.Tendsto c Filter.atTop (nhds 0) ∧
        ∀ j, ‖r (run.points (j + 1))‖ ≤ c j * ‖r (run.points j)‖) ∧
    (∃ M : ℕ, ∀ j : ℕ, ‖r (run.points (M + j))‖ ^ (ell : ℝ) ≤
      (ell : ℝ) * scale * (1 / 2 : ℝ) ^ ((1 / τ) ^ j)) ∧
    ∃ B > 0, ∃ C > 0, ∃ E > 0, ∃ F > 0, ∀ ε > 0, ε ≤ Real.exp (-1) →
      ∃ N : ℕ, residualAttained run ε N ∧
        (run.visit N : ℝ) + 1 ≤ B * Real.log |Real.log ε| + C ∧
        (N : ℝ) + 1 ≤ E * Real.log |Real.log ε| + F := by
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast hell.2.1
  have hep : (ell : ℝ) ≤ p := by exact_mod_cast hell.2.2
  have he0 : (0 : ℝ) < ell := by linarith
  have he1 : (1 : ℝ) < ell := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hd := hr.isMeasureDominated he1
  have hνμ : ((p : ℝ) + 1) / p < (ell : ℝ) / ((ell : ℝ) - 1) := by
    apply (div_lt_div_iff₀ hp0 (by linarith : 0 < (ell : ℝ) - 1)).mpr
    nlinarith
  have ha := gap_coefficient_pos hd run
  have hτ0 := div_pos run.exponent_pos hd.exponent_pos
  have hτ1 := (div_lt_one hd.exponent_pos).mpr hνμ
  let τ := (((p : ℝ) + 1) / p) / ((ell : ℝ) / ((ell : ℝ) - 1))
  let a := κν / (residualDominationConstant ell σ) ^ τ
  let scale := a ^ (1 / (1 - τ))
  have hscale : 0 < scale := Real.rpow_pos_of_pos ha _
  have hα : 1 < 1 / τ := (one_lt_div hτ0).mpr hτ1
  obtain ⟨M, -, henv, htol⟩ := implicit_recurrence_superlinear_bound ha hτ0 hτ1
    (fun j => hd.gap_nonneg _ (run.points_mem j)) (implicit_gap_step hd run)
  dsimp only
  refine ⟨?_, ⟨M, ?_⟩, ?_⟩
  · apply implicit_power_recurrence_q_superlinear (fun j => norm_nonneg (r (run.points j)))
      he0 ha hτ0 hτ1
    intro j
    simpa only [Section01.residualPowerObjective, residualPowerObjective, sub_zero] using
      implicit_gap_step hd run j
  · intro j
    have hh := mul_le_mul_of_nonneg_left (henv j) he0.le
    simp only [sub_zero] at hh
    simpa [Section01.residualPowerObjective, residualPowerObjective,
      mul_div_cancel₀ _ he0.ne', mul_assoc] using hh
  · let A := 1 / Real.log (1 / τ)
    let H := |Real.log scale| + (ell : ℝ) + |Real.log (ell : ℝ)|
    let C := |Real.log (H / (-Real.log (1 / 2 : ℝ)))| / Real.log (1 / τ) + 1
    let F := (M : ℝ) + C + 1
    have hlog := Real.log_pos hα
    have hA : 0 < A := one_div_pos.mpr hlog
    have hC : 0 < C := by dsimp [C]; positivity
    have hF : 0 < F := by dsimp [F]; positivity
    have hκR : 0 < κR := lt_of_lt_of_le zero_lt_one run.density_factor
    have hκA := run.density_offset
    refine ⟨κR * A, mul_pos hκR hA, κR * F + κA + 1, by positivity,
      A, hA, F, hF, ?_⟩
    intro ε hε hsmall
    let K := superlinearIterationCount scale (1 / 2) (1 / τ) (ε ^ (ell : ℝ) / ell)
    let N := M + K
    have hgap : Section01.residualPowerObjective r ell (run.points N) ≤ ε ^ (ell : ℝ) / ell := by
      have hh := htol (ε ^ (ell : ℝ) / ell)
        (div_pos (Real.rpow_pos_of_pos hε _) he0) K le_rfl
      simpa only [sub_zero] using hh
    have hk : (K : ℝ) ≤ A * Real.log |Real.log ε| + C := by
      have hh := residual_superlinear_count_le hscale hα he0 hε hsmall
      dsimp only [K, A, C, H]
      dsimp only at hh
      linarith
    have hn : (N : ℝ) + 1 ≤ A * Real.log |Real.log ε| + F := by
      simp only [N, Nat.cast_add]
      dsimp only [F]
      linarith
    refine ⟨N, residual_attained run he0 hε.le hgap, ?_, hn⟩
    have hv := (run.visit_cost N).2
    nlinarith

/-- Theorem 5.3.11: a full-rank residual map gives the polynomial residual rate and uniform
`ε ^ (-(ell-2))` function/derivative budgets for the actual TR method class. The constants
are chosen before the tolerance; the even integer premise matches the source. -/
theorem theorem_5_3_11 (ell : ℕ) (hell : Even ell ∧ 2 < ell)
    (hr : HasUniformlyFullRankDerivative D r σ)
    (run : residualDecreaseRun false D r (ell : ℝ) κν 2 κR κA) :
    let μ := (ell : ℝ) / ((ell : ℝ) - 1)
    let C := residualDominationConstant ell σ
    let a := κν / C ^ (2 / μ)
    let δ := a * (2 / μ - 1)
    (∀ j : ℕ, ‖r (run.points j)‖ ^ (ell : ℝ) ≤ (ell : ℝ) *
      ((Section01.residualPowerObjective r ell (run.points 0)) ^ (1 - 2 / μ) +
        (j : ℝ) * δ) ^ (-1 / (2 / μ - 1))) ∧
    ∃ B > 0, ∃ C' > 0, ∃ E > 0, ∃ F > 0, ∀ ε > 0,
      ∃ N : ℕ, residualAttained run ε N ∧
        (run.visit N : ℝ) + 1 ≤ B * ε ^ (-((ell : ℝ) - 2)) + C' ∧
        (N : ℝ) + 1 ≤ E * ε ^ (-((ell : ℝ) - 2)) + F := by
  have he : (2 : ℝ) < ell := by exact_mod_cast hell.2
  have he0 : (0 : ℝ) < ell := by linarith
  have he1 : (1 : ℝ) < ell := by linarith
  have hd := hr.isMeasureDominated he1
  have hμ : (ell : ℝ) / ((ell : ℝ) - 1) < 2 := by
    apply (div_lt_iff₀ (by linarith : 0 < (ell : ℝ) - 1)).mpr
    linarith
  have hτ : 1 < 2 / ((ell : ℝ) / ((ell : ℝ) - 1)) :=
    (one_lt_div hd.exponent_pos).mpr hμ
  have ha := gap_coefficient_pos hd run
  have hδ : 0 < κν / (residualDominationConstant ell σ) ^
      (2 / ((ell : ℝ) / ((ell : ℝ) - 1))) *
      (2 / ((ell : ℝ) / ((ell : ℝ) - 1)) - 1) := mul_pos ha (sub_pos.mpr hτ)
  dsimp only
  refine ⟨?_, ?_⟩
  · intro j
    have hp := ((lemma_5_3_6 hd run).2.polynomial hτ).2.2 j
    simp only [sub_zero] at hp
    have hh := (mul_le_mul_of_nonneg_left hp he0.le)
    simpa [Section01.residualPowerObjective, residualPowerObjective, mul_div_cancel₀ _ he0.ne']
      using hh
  · let A := (ell : ℝ) ^ (((ell : ℝ) - 2) / (ell : ℝ)) /
      (κν / (residualDominationConstant ell σ) ^ (2 / ((ell : ℝ) / ((ell : ℝ) - 1))) *
        (2 / ((ell : ℝ) / ((ell : ℝ) - 1)) - 1))
    have hA : 0 < A := div_pos (Real.rpow_pos_of_pos he0 _) hδ
    have hκR : 0 < κR := lt_of_lt_of_le zero_lt_one run.density_factor
    refine ⟨κR * A, mul_pos hκR hA, κR + κA + 1, by linarith [run.density_offset],
      A, hA, 2, by norm_num, ?_⟩
    intro ε hε
    let N := polynomialIterationCount
      (κν / (residualDominationConstant ell σ) ^ (2 / ((ell : ℝ) / ((ell : ℝ) - 1))) *
        (2 / ((ell : ℝ) / ((ell : ℝ) - 1)) - 1))
      (2 / ((ell : ℝ) / ((ell : ℝ) - 1))) (ε ^ (ell : ℝ) / ell)
    have hg := theorem_5_3_9_gap hd run hμ
      (div_pos (Real.rpow_pos_of_pos hε (ell : ℝ)) he0)
    have hn : (N : ℝ) ≤ A * ε ^ (-((ell : ℝ) - 2)) + 1 :=
      residual_polynomial_count_le he hδ hε
    refine ⟨N, residual_attained run he0 hε.le (by
      simpa only [sub_zero, run.iterate_visit] using hg.1), ?_, by linarith⟩
    have hc := (run.visit_cost N).2
    nlinarith

/-- Theorem 5.3.12: least squares has actual consecutive squared-residual contraction,
a geometric residual envelope, or exact zero after
one success, and uniform logarithmic residual/function and cached-derivative budgets.
Both counts include their initial evaluation. -/
theorem theorem_5_3_12 (hr : HasUniformlyFullRankDerivative D r σ)
    (run : residualDecreaseRun false D r 2 κν 2 κR κA) :
    let a := κν / residualDominationConstant 2 σ
    (1 ≤ a → r (run.points 1) = 0) ∧
    (∀ j : ℕ, ‖r (run.points (j + 1))‖ ^ (2 : ℝ) ≤
      (1 - a) * ‖r (run.points j)‖ ^ (2 : ℝ)) ∧
    (a < 1 → ∀ j : ℕ, ‖r (run.points j)‖ ^ (2 : ℝ) ≤
      ‖r (run.points 0)‖ ^ (2 : ℝ) * (1 - a) ^ j) ∧
    ∃ B > 0, ∃ C > 0, ∃ E > 0, ∃ F > 0, ∀ ε > 0,
      ∃ N : ℕ, residualAttained run ε N ∧
        (run.visit N : ℝ) + 1 ≤ B * |Real.log ε| + C ∧
        (N : ℝ) + 1 ≤ E * |Real.log ε| + F := by
  have hd := hr.isMeasureDominated (by norm_num : (1 : ℝ) < 2)
  have hμ : (2 : ℝ) / (2 - 1) = 2 := by norm_num
  simp only [hμ] at hd
  have ha : 0 < κν / residualDominationConstant 2 σ :=
    div_pos run.decrease_const_pos hd.const_pos
  have hs : ∀ j, Section01.residualPowerObjective r 2 (run.points (j + 1)) ≤
      Section01.residualPowerObjective r 2 (run.points j) -
        κν / residualDominationConstant 2 σ *
          Section01.residualPowerObjective r 2 (run.points j) := by
    intro j
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one, sub_zero] using
      explicit_gap_step hd run j
  have hn : ∀ j, 0 ≤ Section01.residualPowerObjective r 2 (run.points j) :=
    fun _ => residualPowerObjective_nonneg r (by norm_num) _
  dsimp only
  have hz : 1 ≤ κν / residualDominationConstant 2 σ → r (run.points 1) = 0 := by
    intro hlarge
    have hzero := explicit_recurrence_eq_zero_of_one_le hlarge hn hs 0
    have ht : ‖r (run.points 1)‖ ≤ (0 : ℝ) :=
      (residualPowerObjective_le_iff (by norm_num : (0 : ℝ) < 2) (by norm_num) _).mp
        (by simpa using hzero.le)
    exact norm_le_zero_iff.mp ht
  refine ⟨hz, ?_, ?_, ?_⟩
  · intro j
    have hh := hs j
    dsimp [Section01.residualPowerObjective, residualPowerObjective] at hh
    nlinarith
  · intro hlt j
    have hp := explicit_recurrence_linear_bound_of_lt_one
      (u := fun j => Section01.residualPowerObjective r 2 (run.points j)) hlt hs j
    dsimp [Section01.residualPowerObjective, residualPowerObjective] at hp
    linarith
  · have hκR : 0 < κR := lt_of_lt_of_le zero_lt_one run.density_factor
    by_cases hlt : κν / residualDominationConstant 2 σ < 1
    · let b := (1 - κν / residualDominationConstant 2 σ)⁻¹
      have hb : 1 < b := by
        dsimp [b]
        rw [inv_eq_one_div, lt_div_iff₀ (by linarith : 0 < 1 - κν / residualDominationConstant 2 σ)]
        linarith
      let A := 2 / Real.log b
      let C := |Real.log (Section01.residualPowerObjective r 2 (run.points 0) * 2)| /
        Real.log b + 2
      have hA : 0 < A := div_pos (by norm_num) (Real.log_pos hb)
      have hlb := Real.log_pos hb
      have hκA := run.density_offset
      have hC : 0 < C := by dsimp [C]; positivity
      refine ⟨κR * A, mul_pos hκR hA, κR * C + κA + 1, by
        positivity, A, hA, C, hC, ?_⟩
      intro ε hε
      let N := geometricIterationCount (Section01.residualPowerObjective r 2 (run.points 0))
        b (ε ^ (2 : ℝ) / 2)
      have hg : Section01.residualPowerObjective r 2 (run.points N) ≤ ε ^ (2 : ℝ) / 2 := by
        apply geometric_tolerance
          (u := fun j => Section01.residualPowerObjective r 2 (run.points j)) hb
          (show 0 < ε ^ (2 : ℝ) / 2 by positivity) _ (le_refl N)
        intro j
        have hp := explicit_recurrence_linear_bound_of_lt_one
          (u := fun j => Section01.residualPowerObjective r 2 (run.points j)) hlt hs j
        simpa only [b, inv_pow, div_eq_mul_inv, inv_inv] using hp
      have hc : (N : ℝ) + 1 ≤ A * |Real.log ε| + C := by
        have hh := residual_geometric_count_le (v := Section01.residualPowerObjective r 2
          (run.points 0)) hb (by norm_num : (0 : ℝ) < 2) hε
        dsimp [N, A, C] at *
        linarith
      refine ⟨N, residual_attained run (by norm_num) hε.le hg, ?_, hc⟩
      have hv := (run.visit_cost N).2
      nlinarith
    · refine ⟨1, by norm_num, κR + κA + 2, by linarith [run.density_offset],
        1, by norm_num, 2, by norm_num, ?_⟩
      intro ε hε
      refine ⟨1, ?_, ?_, ?_⟩
      · apply residual_attained run (by norm_num) hε.le
        simpa [Section01.residualPowerObjective, residualPowerObjective, hz (le_of_not_gt hlt)]
          using (show (0 : ℝ) ≤ ε ^ (2 : ℝ) / 2 by positivity)
      · have hv := (run.visit_cost 1).2
        norm_num at hv ⊢
        linarith [abs_nonneg (Real.log ε)]
      · norm_num

end CartisGouldToint.Chapter05.Section03
