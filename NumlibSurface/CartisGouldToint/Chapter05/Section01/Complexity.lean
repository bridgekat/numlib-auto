import NumlibSurface.CartisGouldToint.Chapter05.Section01
import Numlib.Optimization.ResidualRegularizationComplexity

/-!
# ARpLE residual-root complexity

Theorem 5.1.7 is stated on every sufficiently long actual legal finite prefix: within the
printed budget one reaches the normalized iterate quality, with the actual computed model
directions or the empty strict-curvature certificate. The separate availability corollary
uses only the algorithm's local trial laws while its genuine stopping test fails.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section01
open Optimization Optimization.ParameterUpdates Optimization.HigherOrderRegularization
open Optimization.ResidualRegularization
open Chapter01.Section03 Chapter02.Section04 Chapter04.Section01

variable {n m p : ℕ} {params : regularizationParameters} {theta epsilon : Fin 3 → ℝ}
    {epsilon0 ell beta L : ℝ} {i : ℕ}
    {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}

/-- Either of the two source third-order parameter choices gives all required nonnegative
residual descent exponents. Earlier orders are strictly positive in both branches. -/
theorem arple_third_order_exponents (hp : 1 ≤ p) (hell : 1 < ell)
    (hchoice : (3 ∣ p ∧ ell = (p : ℝ) / 3 ∧ Real.logb 2 ((p : ℝ) - 2) < i) ∨
      (∃ o h : ℕ, Odd o ∧ 0 < h ∧ i = 2 * h ∧ p - 2 = o * 2 ^ i ∧
        ell = 1 + (o : ℝ) * ∑ k ∈ Finset.range h, (2 : ℝ) ^ (2 * k))) :
    ∀ j : Fin 3, 0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1) := by
  have hc := lemma_5_1_6 (i := i) hp hell
  rcases hchoice with ⟨hdiv, hell, hi⟩ | hchoice
  · have hs := hc.2.2.2.2.1 hdiv hell hi
    intro j
    fin_cases j
    · convert hs.1.le using 1; norm_num [residualDescentExponent]
    · convert hs.2.1.le using 1; norm_num [residualDescentExponent]
    · convert hs.2.2.le using 1; norm_num [residualDescentExponent]
  · have hs := hc.2.2.2.2.2 hchoice
    intro j
    fin_cases j
    · convert hs.1.le using 1; norm_num [residualDescentExponent]
    · convert hs.2.1.le using 1; norm_num [residualDescentExponent]
    · convert (le_of_eq hs.2.2.1.symm) using 1; norm_num [residualDescentExponent]

/-- Theorem 5.1.7, finite-prefix form. Every sufficiently long actual ARpLE prefix already
contains its first quality iterate within the exact residual and tolerance power budget.
The model-direction certificate may be empty, as permitted by the printed conclusion.
No local solver availability or termination assertion is assumed here. -/
theorem theorem_5_1_7 [NeZero n] {N : ℕ}
    (h : arpLEPrefix params 3 p theta epsilon epsilon0 r ell x s sigma N)
    (hf : higherOrderLipschitz (residualPowerObjective r ell) p L)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hchoice : (3 ∣ p ∧ ell = (p : ℝ) / 3 ∧ Real.logb 2 ((p : ℝ) - 2) < i) ∨
      (∃ o h : ℕ, Odd o ∧ 0 < h ∧ i = 2 * h ∧ p - 2 = o * 2 ^ i ∧
        ell = 1 + (o : ℝ) * ∑ k ∈ Finset.range h, (2 : ℝ) ^ (2 * k)))
    (hlong :
      let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
      let Q := complexityConstant params 3 p i ell beta L S theta *
        (initialResidualFactor 3 p i ell ‖r (x 0)‖ / toleranceFactor 3 p i epsilon0 epsilon)
      let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
      let D := Real.log (S / sigma 0) / Real.log params.gamma2
      C * Q + C + D + 1 < N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := complexityConstant params 3 p i ell beta L S theta *
      (initialResidualFactor 3 p i ell ‖r (x 0)‖ / toleranceFactor 3 p i epsilon0 epsilon)
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    0 < complexityConstant params 3 p i ell beta L S theta ∧
    ∃ K ≤ N, arpLEPrefix params 3 p theta epsilon epsilon0 r ell x s sigma K ∧
      (‖r (x K)‖ ≤ epsilon0 ∨ ∃ measures,
        normalizedResidualMeasures r ell (x K) = some measures ∧
        ∃ M : Set (EuclideanSpace ℝ (Fin n)),
          M = (if epsilon 1 < measures.second then ∅ else
            directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell)
              x s sigma K) ∧
          measures.first ≤ epsilon 0 ∧ -epsilon 1 ≤ measures.second ∧
          (∀ d ∈ M, measures.cubic d ≤ epsilon 2) ∧
          M ⊆ residualFlatDirections r ell (epsilon 1) (x K)) ∧
      (∀ k < K, ¬Quality 3 epsilon0 epsilon r ell (x k)
        (directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell)
          x s sigma k)) ∧
      (residualFunctionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (residualDerivativeEvaluations params p r ell x s K : ℝ) ≤ Q + 2 := by
  dsimp only at hlong ⊢
  have hp : 1 ≤ p := by have := h.toARpPrefix.degree_ge_order; omega
  have hi := arple_third_order_exponents hp (by linarith [h.exponent_ge_two]) hchoice
  have hir : ∀ j : Fin 3, j.val < 3 →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1) := fun j _ => hi j
  have hid := root_budget_eq (params := params) (q := 3) (p := p) (i := i)
    (ell := ell) (beta := beta) (L := L)
    (S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))))
    (epsilon0 := epsilon0) (theta := theta) (epsilon := epsilon)
    (by decide) (norm_nonneg (r (x 0))) hir
  have hL := hf.toDiagonalLipschitz hp
  have hS : 0 ≤ max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) :=
    (h.toARpPrefix.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  refine ⟨complexityConstant_pos (by decide) hb0 hb1 hL.nonneg hS h.toARpPrefix.theta_pos, ?_⟩
  obtain ⟨K, hKN, hK, hfirst, hF, hD⟩ :=
    h.exists_first_quality_of_long_prefix hL hb0 hb1 hir (by simpa only [hid] using hlong)
  have hcert := hK.certificate h.residual_tolerance_pos.le
    (h.toARpPrefix.epsilon_pos 1 (by decide)).le
    (fun d hd => directionSequence_unit p (theta 1) (epsilon 1)
      (residualPowerObjective r ell) x s sigma K hd)
  exact ⟨K, hKN, h.restrict hKN, hcert, hfirst,
    by simpa only [hid] using hF, by simpa only [hid] using hD⟩

/-- On a provided full actual ARpLE execution, the first quality point occurs no later
than its actual stopping point, with the exact source evaluation budget. This statement
requires no trial availability beyond the provided execution. -/
theorem theorem_5_1_7_of_run [NeZero n] {N : ℕ}
    (hfull : algorithm_5_1_1 params 3 p theta epsilon epsilon0 r ell x s sigma N)
    (hf : higherOrderLipschitz (residualPowerObjective r ell) p L)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hchoice : (3 ∣ p ∧ ell = (p : ℝ) / 3 ∧ Real.logb 2 ((p : ℝ) - 2) < i) ∨
      (∃ o h : ℕ, Odd o ∧ 0 < h ∧ i = 2 * h ∧ p - 2 = o * 2 ^ i ∧
        ell = 1 + (o : ℝ) * ∑ k ∈ Finset.range h, (2 : ℝ) ^ (2 * k)))
    :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := complexityConstant params 3 p i ell beta L S theta *
      (initialResidualFactor 3 p i ell ‖r (x 0)‖ / toleranceFactor 3 p i epsilon0 epsilon)
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    0 < complexityConstant params 3 p i ell beta L S theta ∧
    ∃ K ≤ N, arpLEPrefix params 3 p theta epsilon epsilon0 r ell x s sigma K ∧
      (‖r (x K)‖ ≤ epsilon0 ∨ ∃ measures,
        normalizedResidualMeasures r ell (x K) = some measures ∧
        ∃ M : Set (EuclideanSpace ℝ (Fin n)),
          M = (if epsilon 1 < measures.second then ∅ else
            directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell)
              x s sigma K) ∧
          measures.first ≤ epsilon 0 ∧ -epsilon 1 ≤ measures.second ∧
          (∀ d ∈ M, measures.cubic d ≤ epsilon 2) ∧
          M ⊆ residualFlatDirections r ell (epsilon 1) (x K)) ∧
      (∀ k < K, ¬Quality 3 epsilon0 epsilon r ell (x k)
        (directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell)
          x s sigma k)) ∧
      (residualFunctionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (residualDerivativeEvaluations params p r ell x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  have h := hfull.toResidualPrefix
  have hp : 1 ≤ p := by have := h.toARpPrefix.degree_ge_order; omega
  have hi := arple_third_order_exponents hp (by linarith [h.exponent_ge_two]) hchoice
  have hir : ∀ j : Fin 3, j.val < 3 →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1) := fun j _ => hi j
  have hid := root_budget_eq (params := params) (q := 3) (p := p) (i := i)
    (ell := ell) (beta := beta) (L := L)
    (S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))))
    (epsilon0 := epsilon0) (theta := theta) (epsilon := epsilon)
    (by decide) (norm_nonneg (r (x 0))) hir
  have hL := hf.toDiagonalLipschitz hp
  have hS : 0 ≤ max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))) :=
    (h.toARpPrefix.toRegularizationPrefix.pos (Nat.zero_le N)).le.trans (le_max_left _ _)
  refine ⟨complexityConstant_pos (by decide) hb0 hb1 hL.nonneg hS h.toARpPrefix.theta_pos, ?_⟩
  obtain ⟨K, hKN, hK, hfirst, hF, hD⟩ :=
    h.exists_first_quality_of_attainment hL hb0 hb1 hir
      ⟨N, le_rfl, hfull.terminal.quality⟩
  have hcert := hK.certificate h.residual_tolerance_pos.le
    (h.toARpPrefix.epsilon_pos 1 (by decide)).le
    (fun d hd => directionSequence_unit p (theta 1) (epsilon 1)
      (residualPowerObjective r ell) x s sigma K hd)
  exact ⟨K, hKN, h.restrict hKN, hcert, hfirst,
    by simpa only [hid] using hF, by simpa only [hid] using hD⟩

/-- Availability corollary of Theorem 5.1.7. The premise supplies only the genuine
local algorithm laws while actual stopping fails. The conclusion is first iterate quality,
which permits empty model directions at third order. -/
theorem theorem_5_1_7_of_available_trials [NeZero n]
    (hf : higherOrderLipschitz (residualPowerObjective r ell) p L)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hchoice : (3 ∣ p ∧ ell = (p : ℝ) / 3 ∧ Real.logb 2 ((p : ℝ) - 2) < i) ∨
      (∃ o h : ℕ, Odd o ∧ 0 < h ∧ i = 2 * h ∧ p - 2 = o * 2 ^ i ∧
        ell = 1 + (o : ℝ) * ∑ k ∈ Finset.range h, (2 : ℝ) ^ (2 * k)))
    (hprefix : ∀ N, (∀ k < N, ¬ResidualRegularization.Stationary 3 epsilon0 epsilon r ell
      (x k) (directionSequence p (theta 1) (epsilon 1)
        (residualPowerObjective r ell) x s sigma k)) →
      arpLEPrefix params 3 p theta epsilon epsilon0 r ell x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := complexityConstant params 3 p i ell beta L S theta *
      (initialResidualFactor 3 p i ell ‖r (x 0)‖ / toleranceFactor 3 p i epsilon0 epsilon)
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K : ℕ, arpLEPrefix params 3 p theta epsilon epsilon0 r ell x s sigma K ∧
      Quality 3 epsilon0 epsilon r ell (x K)
        (directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell) x s sigma K) ∧
      (∀ k < K, ¬Quality 3 epsilon0 epsilon r ell (x k)
        (directionSequence p (theta 1) (epsilon 1)
          (residualPowerObjective r ell) x s sigma k)) ∧
      (residualFunctionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (residualDerivativeEvaluations params p r ell x s K : ℝ) ≤ Q + 2 := by
  dsimp only
  have h0 := hprefix 0 (by simp)
  have hp : 1 ≤ p := by have := h0.toARpPrefix.degree_ge_order; omega
  have hi := arple_third_order_exponents hp (by linarith [h0.exponent_ge_two]) hchoice
  have hir : ∀ j : Fin 3, j.val < 3 →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1) := fun j _ => hi j
  have hlegal : ∀ N, (∀ k < N, ¬Quality 3 epsilon0 epsilon r ell (x k)
      (directionSequence p (theta 1) (epsilon 1) (residualPowerObjective r ell) x s sigma k)) →
      arpLEPrefix params 3 p theta epsilon epsilon0 r ell x s sigma N := by
    intro N hn
    exact hprefix N (fun k hk hs => hn k hk hs.quality)
  obtain ⟨K, hK, hfirst, hF, hD⟩ :=
    exists_first_quality_with_cost (hf.toDiagonalLipschitz hp) hb0 hb1 hir hlegal
  have hid := root_budget_eq (params := params) (i := i)
    (ell := ell) (beta := beta) (L := L)
    (S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2))))
    (epsilon0 := epsilon0) (theta := theta) (epsilon := epsilon)
    (by decide) (norm_nonneg (r (x 0))) hir
  exact ⟨K, hlegal K hfirst, hK, hfirst,
    by simpa only [hid] using hF, by simpa only [hid] using hD⟩

/-- The first- and second-order clauses: any of the source's good exponent choices gives
actual first stopping with the corresponding enabled residual and derivative powers.
The availability premise states only the local algorithm laws before actual stopping. -/
theorem theorem_5_1_7_first_second_order [NeZero n] {q : ℕ} (hq : q ≤ 2)
    (hf : higherOrderLipschitz (residualPowerObjective r ell) p L)
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (hi : ∀ j : Fin 3, j.val < q →
      0 ≤ Optimization.residualDescentExponent p ell i (j.val + 1))
    (hprefix : ∀ N, (∀ k < N, ¬ResidualRegularization.Stationary q epsilon0 epsilon r ell
      (x k) (directionSequence p (theta 1) (epsilon 1)
        (residualPowerObjective r ell) x s sigma k)) →
      arpLEPrefix params q p theta epsilon epsilon0 r ell x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := complexityConstant params q p i ell beta L S theta *
      (initialResidualFactor q p i ell ‖r (x 0)‖ / toleranceFactor q p i epsilon0 epsilon)
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, algorithm_5_1_1 params q p theta epsilon epsilon0 r ell x s sigma K ∧
      (residualFunctionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (residualDerivativeEvaluations params p r ell x s K : ℝ) ≤ Q + 2 := by
  have h0 := hprefix 0 (by simp)
  have hp : 1 ≤ p := h0.toARpPrefix.order_pos.trans h0.toARpPrefix.degree_ge_order
  exact exists_first_stop_with_cost hq (hf.toDiagonalLipschitz hp) hb0 hb1 hi hprefix

end CartisGouldToint.Chapter05.Section01
