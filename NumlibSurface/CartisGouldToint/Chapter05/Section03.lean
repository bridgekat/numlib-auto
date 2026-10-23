import Numlib.Optimization.MeasureDomination.TrustRegionRates
import Numlib.Optimization.MeasureDomination.HistoricalEuclidean
import Numlib.Optimization.MeasureDomination.Superlinear
import Numlib.Optimization.MeasureDomination.Polynomial
import Numlib.Optimization.MeasureDomination.Linear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.MeasureDomination.Regularization

/-!
# Measure domination and gap complexity

Gaps are measured above an attained global minimum. The adaptive regularization
class uses the actual next-point measure in its successful decrease rule.

The sublinear conclusion is an upper rate: an allowed algorithm may converge
faster or reach its minimum in finitely many steps. A genuine exact recurrence
supplies the sublinear upper envelope. Source (5.3.14)'s corrupted subscript is
`κν / κψ^(ν/μ), ν/μ`. The printed iteration and accepted-step counts exclude
initialization; separate explicit evaluation bounds add the initial call.

The historical-measure TR class has a genuine smooth-objective, continuous-measure
counterexample to Theorem5.3.9's assertion that current successful measures
converge to zero. Its gap and historical-measure conclusions remain distinct.
-/

open Set Filter Topology
namespace CartisGouldToint

/-- Measure domination (5.3.1), with a nonnegative measure and attained global minimum. -/
abbrev measureDominated := @MeasureDomination.Dominated

/-- The source ARψ,ν class: next-point successful decrease, rejection, and prefix density. -/
abbrev arMeasureRun := @MeasureDomination.ARRun

/-- The source TRψ,ν class: actual historical-measure decrease, rejection, prefix
density and constant continuation after a zero-measure stop. -/
abbrev trMeasureRun := @MeasureDomination.TRRun

/-- The actual objective gap (5.3.4). -/
abbrev objectiveGap := @MeasureDomination.gap

/-- The increasing index of the nth genuine successful iteration. -/
noncomputable abbrev measureSuccessIndex := MeasureDomination.successIndex

/-- Actual objective gaps at the successive successful iterations. -/
noncomputable abbrev successfulObjectiveGap := @MeasureDomination.successfulGap

/-- The exact implicit recurrence (5.3.12), including zero initial gaps. -/
noncomputable abbrev implicitGapSequence := ImplicitGap.orbit

/-- The first finite target-hitting index of the exact implicit recurrence (5.3.13). -/
noncomputable abbrev implicitGapHittingTime := ImplicitGap.hittingTime

/-- One initial function evaluation and one evaluation for each trial. -/
def measureFunctionEvaluations (K : ℕ) : ℕ := K + 1

/-- One initial derivative evaluation and one evaluation at each accepted endpoint. -/
noncomputable def measureDerivativeEvaluations (S : Set ℕ) (K : ℕ) : ℕ :=
  (EvaluationComplexity.successfulIterations S K).card + 1

/-- **Lemma 5.3.1.** The exact factor bound and convergence of actual successful gaps,
with superlinear, linear and sublinear upper rates. Division by a zero gap has
value zero, so finite attainment is included. Above the domination level the
sublinear envelope is the genuine exact power recurrence, rather than an assertion
that every admissible algorithm converges at exactly that slow rate. -/
theorem lemma_5_3_1 {n : ℕ} {f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {fstar μ κψ ν κν κR κA : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {S : Set ℕ}
    (hd : measureDominated f ψ fstar μ κψ) (hr : arMeasureRun f ψ x S ν κν κR κA) :
    (∀ k ∈ S, objectiveGap f fstar (x (k + 1)) ≤ objectiveGap f fstar (x k) *
      (1 + κν / κψ ^ (ν / μ) * objectiveGap f fstar (x (k + 1)) ^ ((ν - μ) / μ))⁻¹) ∧
    Tendsto (successfulObjectiveGap f fstar x S) atTop (𝓝 0) ∧
    (ν < μ → Tendsto (fun j => successfulObjectiveGap f fstar x S (j + 1) /
      successfulObjectiveGap f fstar x S j) atTop (𝓝 0)) ∧
    (ν = μ → ∀ j, successfulObjectiveGap f fstar x S (j + 1) ≤
      (1 + κν / κψ)⁻¹ * successfulObjectiveGap f fstar x S j) ∧
    (μ < ν → (∀ j, successfulObjectiveGap f fstar x S j = 0) ∨
      ∃ t : ℕ → ℝ, (∀ j, 0 < t j) ∧
        (∀ j, successfulObjectiveGap f fstar x S j ≤ t j) ∧ Tendsto t atTop (𝓝 0) ∧
        Tendsto (fun j => t (j + 1) / t j) atTop (𝓝 1)) := by
  exact ⟨fun _ hk => hr.factor_decrease hd hk, hr.successful_tendsto_zero hd,
    hr.successful_superlinear hd, hr.successful_linear hd, hr.successful_sublinear_envelope hd⟩

/-- **Theorem 5.3.2.** The first actual target gap is reached with the exact
implicit-recurrence success budget and source density bound. Include the initially
zero gap and the initialized function and derivative counts explicitly. -/
theorem theorem_5_3_2 {n : ℕ} {f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {fstar μ κψ ν κν κR κA : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {S : Set ℕ}
    (hd : measureDominated f ψ fstar μ κψ) (hr : arMeasureRun f ψ x S ν κν κR κA)
    {ε : ℝ} (hε : 0 < ε) :
    let T := implicitGapHittingTime (κν / κψ ^ (ν / μ)) (ν / μ)
      (objectiveGap f fstar (x 0)) ε
    ∃ K : ℕ, objectiveGap f fstar (x K) ≤ ε ∧
      (∀ k < K, ε < objectiveGap f fstar (x k)) ∧
      (objectiveGap f fstar (x 0) ≤ ε → K = 0) ∧
      (EvaluationComplexity.successfulIterations S K).card ≤ T ∧
      (K : ℝ) ≤ κR * T + κA ∧
      (measureFunctionEvaluations K : ℝ) ≤ κR * T + κA + 1 ∧
      measureDerivativeEvaluations S K ≤ T + 1 := hr.first_gap_hitting hd hε

end CartisGouldToint

namespace CartisGouldToint

/-- Four positive constants before every accuracy bound initialized function and derivative
counts by affine functions of |log epsilon|, at the first actual target-reaching iterate. -/
def measureLogarithmicComplexity (target : ℕ → ℝ) (S : Set ℕ) : Prop :=
  MeasureDomination.LogarithmicCost target S

/-- **Theorem 5.3.4.** Equal exponents give the exact linear gap factor and both
uniform logarithmic complexity bounds (5.3.20)–(5.3.23). Each target has four
positive constants fixed before every accuracy, and both evaluation counts include
initialization. A small true gap yields a small next-point measure by the actual
accepted decrease; no measure convergence or cost is assumed in the algorithm. -/
theorem theorem_5_3_4 {n : ℕ} {f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {fstar μ κψ ν κν κR κA : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {S : Set ℕ}
    (hd : measureDominated f ψ fstar μ κψ) (hr : arMeasureRun f ψ x S ν κν κR κA)
    (heq : ν = μ) :
    Tendsto (successfulObjectiveGap f fstar x S) atTop (𝓝 0) ∧
      (∀ j, successfulObjectiveGap f fstar x S (j + 1) ≤
        (1 + κν / κψ)⁻¹ * successfulObjectiveGap f fstar x S j) ∧
      measureLogarithmicComplexity (fun k => objectiveGap f fstar (x k)) S ∧
      measureLogarithmicComplexity (fun k => ψ (x k)) S :=
  ⟨hr.successful_tendsto_zero hd, hr.successful_linear hd heq,
    hr.gap_logarithmic hd heq, hr.measure_logarithmic hd heq⟩

end CartisGouldToint

namespace CartisGouldToint

/-- Four positive constants before every accuracy bound the initialized function and derivative
counts by affine functions of epsilon^(-q), at the first actual target-reaching iterate. -/
def measurePolynomialComplexity (q : ℝ) (target : ℕ → ℝ) (S : Set ℕ) : Prop :=
  MeasureDomination.PowerCost q target S

/-- **Theorem 5.3.5.** Both actual successful gaps and measures converge with sublinear
upper envelopes, and their initialized evaluation costs have the exact exponents
(ν−μ)/μ and ν−μ from (5.3.24)–(5.3.27). A finite prefix does not affect the measure
upper rate, which is expressed from the second successful point onward. Faster
convergence and finite attainment are included. All constants precede every accuracy. -/
theorem theorem_5_3_5 {n : ℕ} {f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {fstar μ κψ ν κν κR κA : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {S : Set ℕ}
    (hd : measureDominated f ψ fstar μ κψ) (hr : arMeasureRun f ψ x S ν κν κR κA)
    (hμν : μ < ν) :
    Tendsto (successfulObjectiveGap f fstar x S) atTop (𝓝 0) ∧
      ((∀ j, successfulObjectiveGap f fstar x S j = 0) ∨
        ∃ t : ℕ → ℝ, (∀ j, 0 < t j) ∧
          (∀ j, successfulObjectiveGap f fstar x S j ≤ t j) ∧ Tendsto t atTop (𝓝 0) ∧
          Tendsto (fun j => t (j + 1) / t j) atTop (𝓝 1)) ∧
      Tendsto (fun j => ψ (x (measureSuccessIndex S j))) atTop (𝓝 0) ∧
      ((∀ j, ψ (x (measureSuccessIndex S (j + 1))) = 0) ∨
        ∃ t : ℕ → ℝ, (∀ j, 0 < t j) ∧
          (∀ j, ψ (x (measureSuccessIndex S (j + 1))) ≤ t j) ∧ Tendsto t atTop (𝓝 0) ∧
          Tendsto (fun j => t (j + 1) / t j) atTop (𝓝 1)) ∧
      measurePolynomialComplexity ((ν - μ) / μ) (fun k => objectiveGap f fstar (x k)) S ∧
      measurePolynomialComplexity (ν - μ) (fun k => ψ (x k)) S :=
  ⟨hr.successful_tendsto_zero hd, hr.successful_sublinear_envelope hd hμν,
    hr.successful_measure_tendsto_zero hd, hr.measure_sublinear_envelope hd hμν,
    hr.gap_power_cost hd hμν, hr.measure_power_cost hd hμν⟩

end CartisGouldToint

namespace CartisGouldToint

/-- Initialized first-attainment complexity in log|a+b log epsilon|, with positive constants
and a positive accuracy cutoff fixed before every requested accuracy. The cutoff is at
most exp(-1) and keeps the inner absolute logarithm at least one. -/
def measureDoubleLogarithmicComplexity (a b : ℝ) (target : ℕ → ℝ) (S : Set ℕ) : Prop :=
  MeasureDomination.DoubleLogarithmicCost a b target S

/-- **Theorem 5.3.3.** Actual successful gaps converge superlinearly, and both gap and
measure targets have the double-logarithmic initialized costs (5.3.16)–(5.3.19).
The measure bound retains its exact printed inner expression, as well as the proved
ordinary double-logarithmic order. Fixed positive small-accuracy thresholds make
the displayed logarithms valid, including finite attainment and initial zero gaps. -/
theorem theorem_5_3_3 {n : ℕ} {f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {fstar μ κψ ν κν κR κA : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {S : Set ℕ}
    (hd : measureDominated f ψ fstar μ κψ) (hr : arMeasureRun f ψ x S ν κν κR κA)
    (hνμ : ν < μ) :
    Tendsto (successfulObjectiveGap f fstar x S) atTop (𝓝 0) ∧
      Tendsto (fun j => successfulObjectiveGap f fstar x S (j + 1) /
        successfulObjectiveGap f fstar x S j) atTop (𝓝 0) ∧
      Tendsto (fun j => ψ (x (measureSuccessIndex S j))) atTop (𝓝 0) ∧
      measureDoubleLogarithmicComplexity 0 1 (fun k => objectiveGap f fstar (x k)) S ∧
      measureDoubleLogarithmicComplexity (Real.log κν) ν (fun k => ψ (x k)) S ∧
      measureDoubleLogarithmicComplexity 0 1 (fun k => ψ (x k)) S := by
  have hm := hr.measure_doublelog_cost hd hνμ
  exact ⟨hr.successful_tendsto_zero hd, hr.successful_superlinear hd hνμ,
    hr.successful_measure_tendsto_zero hd, hr.gap_doublelog_cost hd hνμ, hm,
    hm.to_plain (zero_lt_one.trans_le hr.exponent_ge_one)⟩

/-- A smooth, continuous-measure counterexample to the current-measure
convergence clause of **Theorem5.3.9**. All trials are accepted in a genuine
historical-decrease execution with `μ=2<4=ν`. Its gaps and historical measures
converge to zero, while current measures at successful iterations do not.
The measure vanishes exactly on the global minimizers. -/
theorem theorem_5_3_9_counterexample :
    ∃ (f ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
      (x : ℕ → EuclideanSpace ℝ (Fin 2)),
      ContDiff ℝ ⊤ f ∧ Continuous ψ ∧ (∀ z, ψ z = 0 ↔ f z = 0) ∧
      measureDominated f ψ 0 2 1 ∧ trMeasureRun f ψ x Set.univ 4 (1 / 64) 1 0 ∧
      MeasureDomination.gap f 0 (x 0) = 1 ∧ (∀ n, 0 < ψ (x n)) ∧
      Tendsto (fun n => MeasureDomination.gap f 0 (x n)) atTop (nhds 0) ∧
      Tendsto (MeasureDomination.pastMeasure ψ x) atTop (nhds 0) ∧
      ¬Tendsto (fun n => ψ (x (MeasureDomination.successIndex Set.univ n)))
        atTop (nhds 0) :=
  MeasureDomination.HistoricalCounterexample.euclidean_counterexample

/-- The source's positive boundary between the nonunit domination regimes,
`Γ_square = (κψ^(ν/μ)/κν)^(μ/(ν−μ))`, used when `ν ≠ μ`. -/
noncomputable abbrev trMeasureGapThreshold (κψ κν μ ν : ℝ) : ℝ :=
  MeasureDomination.trGapThreshold κψ κν μ ν

/-- **Theorem5.3.7.** Below the domination level the actual first exact minimum
and zero optimality measure have uniform constant evaluation bounds. The gaps
have a superlinear upper rate, and each positive accepted gap is at least the
fixed source threshold. Function and derivative counts include initialization. -/
theorem theorem_5_3_7 {n : ℕ} {f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {fstar μ κψ ν κν κR κA : ℝ} {x : ℕ → EuclideanSpace ℝ (Fin n)} {S : Set ℕ}
    (hd : measureDominated f ψ fstar μ κψ) (hr : trMeasureRun f ψ x S ν κν κR κA)
    (hνμ : ν < μ) :
    ∃ κC > 0, ∃ κF > 0,
      Tendsto (fun j => MeasureDomination.successfulGap f fstar x S (j + 1) /
        MeasureDomination.successfulGap f fstar x S j) atTop (nhds 0) ∧
      ∃ K : ℕ, objectiveGap f fstar (x K) = 0 ∧ ψ (x K) = 0 ∧
        (∀ i < K, 0 < objectiveGap f fstar (x i)) ∧
        (∀ j, K ≤ j → x j = x K) ∧
        (∀ i < K, i ∈ S →
          trMeasureGapThreshold κψ κν μ ν ≤ objectiveGap f fstar (x i)) ∧
        (K : ℝ) ≤ κC ∧ ((K + 1 : ℕ) : ℝ) ≤ κC ∧
        ((EvaluationComplexity.successfulIterations S K).card : ℝ) ≤ κF ∧
        (((EvaluationComplexity.successfulIterations S K).card + 1 : ℕ) : ℝ) ≤ κF := by
  let θ := ExplicitGap.threshold (κν / κψ ^ (ν / μ)) (ν / μ)
  let G := objectiveGap f fstar (x 0) / θ
  have hc : 0 < κν / κψ ^ (ν / μ) :=
    div_pos hr.coefficient_pos (Real.rpow_pos_of_pos hd.coefficient_pos _)
  have hθ : 0 < θ := ExplicitGap.threshold_pos hc _
  have hG : 0 ≤ G := div_nonneg (hd.gap_nonneg _) hθ.le
  have hR : 0 < κR := zero_lt_one.trans_le hr.density_factor
  have hA := hr.density_additive
  refine ⟨κR * G + κA + 1, by positivity, G + 1, by positivity,
    hr.successful_superlinear hd hνμ, ?_⟩
  obtain ⟨K, hk, hψ, hfirst, hstop, hcard, htrials⟩ := hr.first_zero_budget hd hνμ
  refine ⟨K, hk, hψ, hfirst, hstop,
    fun i hi hiS => hr.current_gap_ge_threshold hd hνμ hiS (hfirst i hi), ?_, ?_, ?_, ?_⟩
  · exact htrials.trans (le_add_of_nonneg_right zero_le_one)
  · push_cast
    linarith
  · exact hcard.trans (le_add_of_nonneg_right zero_le_one)
  · push_cast
    linarith

end CartisGouldToint
