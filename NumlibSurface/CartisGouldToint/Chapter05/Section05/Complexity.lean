import NumlibSurface.CartisGouldToint.Chapter05.Section05.Decrease
import NumlibSurface.CartisGouldToint.Chapter02.Section01
import Numlib.Optimization.UniversalRegularizationComplexity

/-!
# Chapter 5, Section 5: uniform evaluation complexity

The constants are chosen before all accuracy tolerances and legal traces with fixed controls.
The actual schedule charges active derivatives at every rejected and terminal trial. The
explicit logarithmic budget is also bounded by a tolerance-independent coefficient divided
by the exact minimum complexity power, giving the asserted polynomial evaluation order.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section05
open Optimization.UniversalRegularization

/-- Availability of actual model steps and legal nonterminal prefixes, without a stopping
or complexity assumption. -/
abbrev universalAvailable {n q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x s : ℕ → EuclideanSpace ℝ (Fin n))
    (sigma : ℕ → ℝ) : Prop := Available a f x s sigma

/-- Equality of all nonaccuracy controls; tolerance choices may vary freely. -/
abbrev universalSameControls {q p : ℕ} {r : ℝ} (a b : universalParameters q p r) : Prop :=
  SameControls a b

/-- The exact minimum tolerance power in (5.5.44),(5.5.52), with curvature omitted when
inactive. Its reciprocal is the maximum of the inverse complexity powers. -/
abbrev universalTolerancePower {q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (t : ℝ) : ℝ := tolerancePower a t

/-- The complexity power is precisely the source's minimum for both active orders. -/
theorem universalTolerancePower_eq {q p : ℕ} {r t : ℝ} {a : universalParameters q p r}
    (ht : 0 ≤ t) : universalTolerancePower a t = if 2 ≤ q then
      min (a.epsilon 0 ^ (t / (t - 1))) (a.epsilon 1 ^ (t / (t - 2)))
    else a.epsilon 0 ^ (t / (t - 1)) := toleranceRadius_power ht

/-- The full explicit budget: a uniform inverse-power term, the activated logarithmic
accuracy terms, and an initial/terminal evaluation allowance. -/
abbrev universalEvaluationBudget {q p : ℕ} {r : ℝ} (c : ComplexityConstants)
    (a : universalParameters q p r) (t gap : ℝ) : ℝ := evaluationBudget c a t gap

/-- Theorem 5.5.7: fixed controls and positive initialization admit constants chosen before
all tolerances and legal traces. Actual first stopping is forced by legal prefix availability.
Order zero and activated derivatives obey the full logarithmic budget and a uniform
polynomial-rate bound. Higher derivatives are charged exactly on the cached success schedule.
The unused second logarithmic constant is omitted when `q=1`; all used constants are positive. -/
theorem theorem_5_5_7 {n q p : ℕ} [NeZero n] {r H beta initial : ℝ}
    (b : universalParameters q p r) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hbb : Chapter02.Section01.assumption_f_Bb f)
    (hf : holderDerivativeAssumption f p H beta) (hi : 0 < initial)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (htr : (p : ℝ) + beta ≤ r) :
    ∃ low : ℝ, ∃ c : ComplexityConstants, (∀ z, low ≤ f z) ∧
      0 < c.success ∧ 0 < c.all ∧ 0 < c.firstLog ∧
      (2 ≤ q → 0 < c.secondLog) ∧ 0 < c.offset ∧
      ∀ a : universalParameters q p r, universalSameControls a b →
      ∀ (x s : ℕ → EuclideanSpace ℝ (Fin n)) (sigma : ℕ → ℝ),
        sigma 0 = initial → universalAvailable a f x s sigma →
        ∃ N, algorithm_5_5_1 a f x s sigma N ∧
          Stationary a f (observation x s N) ∧
          (∀ i < N, ¬Stationary a f (observation x s i)) ∧
          (∀ j ≤ q, (universalEvaluations a f x s sigma N j : ℝ) ≤
            universalEvaluationBudget c a ((p : ℝ) + beta) (f (x 0) - low)) ∧
          (∀ j ≤ q, (universalEvaluations a f x s sigma N j : ℝ) ≤
            (c.all * (f (x 0) - low) + c.firstLog * (((p : ℝ) + beta - 1) / ((p : ℝ) + beta)) +
              (if 2 ≤ q then c.secondLog * (((p : ℝ) + beta - 2) / ((p : ℝ) + beta)) else 0) +
              c.offset) / universalTolerancePower a ((p : ℝ) + beta)) ∧
          (∀ j, q < j → j ≤ p → (universalEvaluations a f x s sigma N j : ℝ) ≤
            c.success * (f (x 0) - low) / universalTolerancePower a ((p : ℝ) + beta) + 1) := by
  obtain ⟨low, hlow⟩ := Chapter02.Section01.assumption_f_Bb_iff.mp hbb
  let t := (p : ℝ) + beta
  let c := positiveComplexityConstants b H t initial
  obtain ⟨hs, ha, hb, hb', hc⟩ := positiveComplexityConstants_signs (a := b) (H := H) hi hexp htr
  refine ⟨low, c, hlow, hs, ha, hb, hb', hc, ?_⟩
  intro a hcontrols x s sigma hinit havail
  have heq : positiveComplexityConstants a H t (sigma 0) = c := by
    rw [hinit]
    exact hcontrols.positiveComplexityConstants_eq
  have hsucc : (complexityConstants a H t (sigma 0)).success = c.success := by
    change (positiveComplexityConstants a H t (sigma 0)).success = c.success
    rw [heq]
  have hbudget : evaluationBudget (complexityConstants a H t (sigma 0)) a t (f (x 0) - low) ≤
      evaluationBudget c a t (f (x 0) - low) := by
    have hh := evaluationBudget_le_positive (a := a) (H := H)
      (t := t) (initial := sigma 0) (gap := f (x 0) - low)
    rwa [heq] at hh
  obtain ⟨N, hrun, _⟩ := havail.exists_first_run hf.toHolderDerivative hexp htr hlow
  obtain ⟨hactive, hhigh⟩ := hrun.evaluation_bounds hf.toHolderDerivative hexp htr hlow
  have hactive' : ∀ j ≤ q, (universalEvaluations a f x s sigma N j : ℝ) ≤
      universalEvaluationBudget c a t (f (x 0) - low) :=
    fun j hj => (hactive j hj).trans hbudget
  have hsecondnonneg : 0 ≤ c.secondLog := by
    by_cases hq : 2 ≤ q
    · exact (hb' hq).le
    · dsimp [c, positiveComplexityConstants]
      rw [ite_eq_right hq]
  have hinactive : ¬2 ≤ q → c.secondLog = 0 := by
    intro hq
    dsimp [c, positiveComplexityConstants]
    rw [ite_eq_right hq]
  have hpower := evaluationBudget_le_power (a := a) (c := c) (gap := f (x 0) - low)
    hexp hb.le hsecondnonneg hc.le hinactive
  refine ⟨N, hrun, hrun.terminal, fun _ hi => hrun.first hi, hactive', ?_, ?_⟩
  · exact fun j hj => (hactive' j hj).trans hpower
  · intro j hj hjp
    have hh := hhigh j hj hjp
    rwa [hsucc] at hh

end CartisGouldToint.Chapter05.Section05
