import Numlib.Optimization.ExplicitRegularizationCounts
import Numlib.Optimization.ExplicitRegularizationToleranceParameters
import Numlib.Optimization.ExplicitRegularizationUniformAccuracy
import Numlib.Optimization.FiniteIncrementCounts

/-!
# Geometric refinement budgets before observable certification

Below a uniform polynomial request threshold, actual explicit-accuracy passes must be
trials: all-pass inspections certify and returned steps meet the short-step accuracy test.
Every remaining refinement therefore has a bounded geometric exponent. The resulting
logarithmic bound requires no true-quality failure or assumed stopping index.
-/

noncomputable section
namespace Optimization.ExplicitRegularization
open InexactRegularization
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every actual explicit-accuracy execution has an integer and real logarithmic refinement
budget. Parameter and historical-radius upper/lower bounds are derived from actual transitions;
only analytic objective regularity and supplied-tensor norms are inputs. The endpoint may be
certified or may be another nonterminal inspection. -/
theorem Execution.refinement_count_le {P : Parameters} {f : E → ℝ} {O : Oracle f P.p}
    {N : ℕ} (r : Execution P O N) {L M : ℝ} (hM : 1 ≤ M)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hA : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j) :
    let S := correctedSigmaBound P.toImplicitParameters
      (r.state 0).request (r.state 0).sigma L 1
    let c := refinementAccuracyCoefficient P.toImplicitParameters M S 1
    let D := refinementLogConstant P.toImplicitParameters (r.state 0).request c
    r.refinementCount N ≤ ⌈refinementLogSlope P.toImplicitParameters * |Real.log ε| + D⌉₊ + 1 ∧
      (r.refinementCount N : ℝ) ≤
        refinementLogSlope P.toImplicitParameters * |Real.log ε| + D + 2 := by
  let S := correctedSigmaBound P.toImplicitParameters
    (r.state 0).request (r.state 0).sigma L 1
  let c := refinementAccuracyCoefficient P.toImplicitParameters M S 1
  let U := requestEnvelope P.p (r.state 0).request
  let B := refinementLogSlope P.toImplicitParameters * |Real.log ε| +
    refinementLogConstant P.toImplicitParameters (r.state 0).request c
  have hc : 0 < c := refinementAccuracyCoefficient_pos P.toImplicitParameters hM
    (by norm_num : (0 : ℝ) ≤ 1)
  have hU : 0 < U := zero_lt_one.trans_le (one_le_requestEnvelope _ _)
  have hε1 : ε ≤ 1 := (hεj 1 le_rfl P.order_pos).trans
    (P.epsilon_lt_one 1 le_rfl P.order_pos).le
  have hforce (k : ℕ) (hk : k < N) (ht : r.trial k = false) :
      c * ε ^ (P.p * (P.q + 1)) < P.gammaAccuracy ^ r.refinementCount k * U := by
    by_contra hn
    have hb := le_of_not_gt hn
    have hh : ∀ i ∈ Finset.Icc 1 P.p, (r.state k).request i ≤
        refinementThreshold P.toImplicitParameters M S 1 ε := by
      intro i hi
      rw [r.request_eq hk.le i]
      exact (mul_le_mul_of_nonneg_left (request_le_envelope _ hi)
        (pow_pos P.gammaAccuracy_pos _).le).trans hb
    have ht' := Execution.trial_of_small_uniform_request (E := E) (f := f) (P := P)
      (O := O) (N := N) (r := r) (L := L) (M := M) (ε := ε) hM hf hA hε.le hεj hk hh
    simp only [ht, Bool.false_eq_true] at ht'
  have hzero : r.refinementCount 0 = 0 := by simp [Execution.refinementCount]
  have hstep : ∀ k < N, r.refinementCount (k + 1) ≤ r.refinementCount k + 1 := by
    intro k _
    rw [r.refinementCount_succ]
    split_ifs <;> omega
  have hgate : ∀ k < N, r.refinementCount k < r.refinementCount (k + 1) →
      (r.refinementCount k : ℝ) < B := by
    intro k hk hinc
    have htfalse : r.trial k = false := by
      cases ht : r.trial k with
      | false => rfl
      | true => simp [r.refinementCount_succ, ht] at hinc
    exact geometric_exponent_lt_log_bound P.gammaAccuracy_pos P.gammaAccuracy_lt_one hc
      hε hε1 hU (hforce k hk htfalse)
  have hB : 0 ≤ B := add_nonneg
    (mul_nonneg (refinementLogSlope_pos P.toImplicitParameters).le (abs_nonneg _))
    (refinementLogConstant_nonneg P.toImplicitParameters _ _)
  exact ⟨nat_count_le_ceil_of_increment_gate hzero hstep hgate,
    nat_count_le_real_of_increment_gate hzero hstep hgate hB⟩


/-- Fixed controls, initial requests and initial regularization give positive refinement
constants before every replacement tolerance vector. All actual finite prefixes satisfy
the bound; observable termination and any failure of true quality are not premises. -/
theorem refinement_bound_fixed_initialization {P : Parameters} {f : E → ℝ}
    (O : Oracle f P.p) {L M : ℝ} (hM : 1 ≤ M)
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L)
    (hA : ∀ (x : E) (h : ℕ → ℝ),
      (∀ i ∈ Finset.Icc 1 P.p, 0 < h i ∧ h i ≤ P.kappaInitial) →
      ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative x h i‖ ≤ M)
    (h0 : ℕ → ℝ) (sigma0 : ℝ) :
    let S := correctedSigmaBound P.toImplicitParameters h0 sigma0 L 1
    let c := refinementAccuracyCoefficient P.toImplicitParameters M S 1
    let G := refinementLogSlope P.toImplicitParameters
    let F := refinementLogConstant P.toImplicitParameters h0 c + 2
    0 < G ∧ 0 < F ∧
      ∀ (ε : ℕ → ℝ) (hpos : ∀ j, 1 ≤ j → j ≤ P.q → 0 < ε j)
        (hlt : ∀ j, 1 ≤ j → j ≤ P.q → ε j < 1) (e : ℝ), 0 < e →
        (∀ j, 1 ≤ j → j ≤ P.q → e ≤ ε j) →
        ∀ (N : ℕ) (r : Execution (P.withTolerances ε hpos hlt) O N),
          (r.state 0).request = h0 → (r.state 0).sigma = sigma0 →
          (r.refinementCount N : ℝ) ≤ G * |Real.log e| + F := by
  dsimp only
  refine ⟨refinementLogSlope_pos P.toImplicitParameters, add_pos_of_nonneg_of_pos
    (refinementLogConstant_nonneg P.toImplicitParameters h0 _) (by norm_num), ?_⟩
  intro ε hpos hlt e he hej N r hr hσ
  have hAr : ∀ k, k ≤ N → ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i‖ ≤ M := by
    intro k hk
    apply hA
    intro i hi
    exact ⟨(r.request_bounds hk hi).1,
      (r.request_bounds hk hi).2.trans (r.initial_request_le i hi)⟩
  have hb := r.refinement_count_le hM hf hAr he hej
  have hb' := hb.2
  rw [hr, hσ] at hb'
  convert hb' using 1
  rw [add_assoc]
  rfl

end Optimization.ExplicitRegularization
