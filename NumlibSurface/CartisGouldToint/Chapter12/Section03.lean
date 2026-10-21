import Numlib.Optimization.RegularizationSufficientDecrease
import NumlibSurface.CartisGouldToint.Chapter12.Section02

/-!
# Chapter 12, Section 3: sufficient decrease without global minimization

This auxiliary interface uses a corrected full-`p` interpretation of (12.3.1): the tolerance
index is `j`, but the prediction is the degree-`p` Taylor decrement used in ARqp's actual
acceptance ratio. The supplied text prints a degree-`j` decrement. No comparison between
these two decrements, and no complexity implication from that literal printed condition,
is asserted here. The full-model choice is the one controlled by the cited long-step
lemma and by the proof of Theorem 12.2.14.

The step branch (12.3.2) explicitly pays `sigmaMin / (p + 1)!`; its coefficient need not be
the same as that of the direct prediction branch. Both branches give the common
minimum-tolerance exponent stated in this section. A fixed finite budget of exceptional
accepted steps is allowed. A true approximate-minimizer stop follows only when legal
prefixes with these properties are available until that stop. Failure to find a step by
itself has no optimality guarantee. There is no numbered theorem in this section.
-/

noncomputable section
open Optimization HigherOrderRegularization RegularizationSufficientDecrease
namespace CartisGouldToint.Chapter12.Section03

/-- The common worst-order exponent in Section 12.3, using the two earlier ARqp regimes. -/
def arqpDecreaseExponent (p q : ℕ) : ℝ := Section02.arqpComplexityExponent p q q

/-- The common exponent is positive for active orders no larger than the model degree. -/
theorem arqpDecreaseExponent_pos {p q : ℕ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    0 < arqpDecreaseExponent p q := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hppos : 0 < p := lt_of_lt_of_le hqpos hqp
  unfold arqpDecreaseExponent Section02.arqpComplexityExponent
  split_ifs
  · exact div_pos (by positivity) (by positivity)
  · exact div_pos (mul_pos (by exact_mod_cast hqpos) (by positivity))
      (by exact_mod_cast hppos)

/-- Corrected full-`p` sufficient decrease for the actual ARqp acceptance prediction.
The printed degree-`j` condition in (12.3.1) is not identified with this one. The alternative
powered step threshold is exactly the root threshold (12.3.2), and its prediction cost
includes the parameter-floor/factorial normalization. The positive coefficient is fixed
independently of iteration and tolerance in the complexity theorem below. -/
abbrev HasArqpSufficientDecrease {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p q : ℕ) (hq : 1 ≤ q) (epsilon : ℕ → ℝ) (kappa : ℝ)
    (x s : EuclideanSpace ℝ (Fin n)) : Prop :=
  HasTaylorDecrease f p q hq epsilon kappa (arqpDecreaseExponent p q) x s

/-- The source interface is characterized by a full-`p` prediction branch and a powered
step branch. This explicitly records the corrected interpretation of (12.3.1). -/
theorem hasArqpSufficientDecrease_iff {n p q : ℕ} {hq : 1 ≤ q}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {epsilon : ℕ → ℝ} {kappa : ℝ}
    {x s : EuclideanSpace ℝ (Fin n)} :
    HasArqpSufficientDecrease f p q hq epsilon kappa x s ↔
      (∃ j ∈ Finset.Icc 1 q, kappa * (epsilon j) ^ arqpDecreaseExponent p q ≤
        RegularizedTaylorModel.taylorModel f p x 0 -
          RegularizedTaylorModel.taylorModel f p x s) ∨
      kappa * (minimumTolerance q hq epsilon) ^ arqpDecreaseExponent p q ≤
        ‖s‖ ^ (p + 1) := hasTaylorDecrease_iff

/-- Conditional Section 12.3 evaluation complexity for the corrected full-`p` interface.
The initial point, initial regularization parameter, coefficient and exception budget are
fixed method data. The displayed factors outside the common tolerance power are therefore
independent of tolerance. No global model minimizer is required: legal actual Taylor-model
trials, actual acceptance/update laws and sufficient decrease outside the exceptional set
are the operational hypotheses. They must remain available until the first true
approximate-minimizer test. Counts are the actual objective queries and cached derivative
queries. This proves the common minimum-tolerance rate, not stronger mixed-order rates. -/
theorem arqp_complexity_of_sufficient_decrease {n p q : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {params : ParameterUpdates.RegularizationParameters}
    (hq : 1 ≤ q) (hqp : q ≤ p) {L low kappa : ℝ}
    (hf : DiagonalLipschitz f p L)
    (hlow : ∀ y, low ≤ f y) (hkappa : 0 < kappa)
    (xinit : EuclideanSpace ℝ (Fin n)) (sigmaInit : ℝ) (B : ℕ)
    {epsilon : ℕ → ℝ} (hepsilon : ∀ j ∈ Finset.Icc 1 q, 0 < epsilon j ∧ epsilon j ≤ 1)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ)
    (delta : ℕ → ℕ → ℝ) (hx : x 0 = xinit) (hsigma : sigma 0 = sigmaInit)
    (hprefix : ∀ N,
      (∀ k < N, ¬Section01.IsApproxOrderMinimizer f (x k) q epsilon (delta k)) →
        TrialPrefix params p f x s sigma N)
    (hgood : ∀ N,
      (∀ k < N, ¬Section01.IsApproxOrderMinimizer f (x k) q epsilon (delta k)) →
      ∃ bad : Finset ℕ, bad.card ≤ B ∧
        ∀ k < N, params.eta1 ≤ ratio f p (x k) (s k) → k ∉ bad →
          HasArqpSufficientDecrease f p q hq epsilon kappa (x k) (s k)) :
    let M := max sigmaInit (params.gamma3 * (L / (1 - params.eta2)))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (M / sigmaInit) / Real.log params.gamma2
    let Q := (f xinit - low) /
      (params.eta1 * decreaseFactor params p kappa *
        (minimumTolerance q hq epsilon) ^ arqpDecreaseExponent p q) + B
    ∃ K : ℕ, Section01.IsApproxOrderMinimizer f (x K) q epsilon (delta K) ∧
      (∀ k < K, ¬Section01.IsApproxOrderMinimizer f (x k) q epsilon (delta k)) ∧
      (functionEvaluations K : ℝ) ≤ C * Q + D + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 1 := by
  have hb := RegularizationSufficientDecrease.exists_first_with_evaluation_bounds
    (P := fun k => Section01.IsApproxOrderMinimizer f (x k) q epsilon (delta k))
    hf (hq.trans hqp) hkappa (arqpDecreaseExponent_pos hq hqp).le
    (fun j hj => (hepsilon j hj).1) hlow B hprefix hgood
  simpa only [hx, hsigma] using hb

end CartisGouldToint.Chapter12.Section03
