import Numlib.Optimization.InexactTaylorModels
import NumlibSurface.CartisGouldToint.Chapter12.Section01
import NumlibSurface.CartisGouldToint.AppendixA.Section10

/-!
# Chapter 13, Section 1: implicit dynamic accuracy

The oracle supplies arbitrary approximate derivative tensors, with unknown fixed error
multipliers. Function values are exact in IDA. Actual finite polynomials, their decrements,
and their compact Euclidean gaps satisfy the perturbation estimates of Section 13.1.2.
The TRqIDA child module gives the actual trust-region execution and its first true-quality
evaluation bounds. The ARqpIDA child distinguishes the printed accuracy check through order
`q` from the all-order `p` variant suggested by the preceding accuracy formula. Its remaining
model-derivative and complexity obligations are explicit in the plans. A concrete literal
long-step execution refutes the all-iteration parameter bound in Lemma 13.1.14; it does not
refute a first-attainment result.
-/

noncomputable section
open scoped Nat
open Optimization
open InexactTaylorModels
namespace CartisGouldToint.Chapter13.Section01

variable {n : ℕ}

/-- Implicit dynamic accuracy (13.1.2): arbitrary requested positive accuracies return
approximate tensors. A single family of fixed error multipliers works at every point and
request, but is hidden existentially rather than furnished as algorithmic data. Function
values in this section are the exact values of `f`. -/
structure ImplicitAccuracyOracle (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℕ) where
  derivative : EuclideanSpace ℝ (Fin n) → (ℕ → ℝ) →
    ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin n)) ℝ
  accuracy : ∃ κ : ℕ → ℝ,
    (∀ i ∈ Finset.Icc 1 r, 0 ≤ κ i) ∧
    ∀ x h, (∀ i ∈ Finset.Icc 1 r, 0 < h i) →
      ∀ i ∈ Finset.Icc 1 r, ‖derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ κ i * h i

/-- The exact function evaluation used in IDA acceptance ratios. -/
def ImplicitAccuracyOracle.functionValue {f : EuclideanSpace ℝ (Fin n) → ℝ} {r : ℕ}
    (_O : ImplicitAccuracyOracle f r) (x : EuclideanSpace ℝ (Fin n)) : ℝ := f x

/-- Equation (13.1.1): an actual polynomial from supplied approximate tensors and a
separate scalar constant. IDA uses `c = f x`; the independent constant also exposes its
cancellation from the decrement. -/
abbrev inexactTaylorModel (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin n)) ℝ)
    (j : ℕ) (s : EuclideanSpace ℝ (Fin n)) : ℝ := polynomial c A j s

/-- The actual inexact Taylor decrement in Section 13.1.2. -/
abbrev inexactTaylorDecrement
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin n)) ℝ)
    (j : ℕ) (s : EuclideanSpace ℝ (Fin n)) : ℝ := decrement A j s

/-- Equation (13.1.5): the maximum of the actual inexact decrement on the radius ball. -/
def inexactTaylorCriticality
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin n)) ℝ)
    (j : ℕ) (δ : ℝ) : ℝ :=
  TaylorCriticality.gapOn (inexactTaylorDecrement A j) (Metric.closedBall 0 δ)

/-- The inexact criticality measure is attained on the actual Euclidean displacement ball. -/
theorem exists_eq_inexactTaylorCriticality
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin n)) ℝ)
    (j : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ d : EuclideanSpace ℝ (Fin n), ‖d‖ ≤ δ ∧
      inexactTaylorDecrement A j d = inexactTaylorCriticality A j δ := by
  obtain ⟨d, hd, heq⟩ := TaylorCriticality.exists_eq_gapOn
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) δ)
    (show (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ).Nonempty from
      ⟨0, by simpa using hδ⟩) (continuous_decrement A j).continuousOn
  exact ⟨d, by simpa using hd, heq⟩

/-- Assumption f.D0rL: `f` is `C^r`, and every derivative of order zero through `r` is
globally Lipschitz, with constants at least one. The zeroth derivative condition includes
Lipschitz continuity of `f` itself. -/
structure ImplicitSmoothness (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℕ) : Prop where
  contDiff : ContDiff ℝ r f
  lipschitz : ∀ i ≤ r, ∃ L : ℝ, 1 ≤ L ∧
    ∀ x y, ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ L * ‖x - y‖

/-- The disjoint iteration types underlying (13.1.19)–(13.1.21). Successful trials are
one of the two trial types; an accuracy refinement makes no trial. -/
inductive DynamicAccuracyIterationKind where
  | accuracyOnly
  | successfulTrial
  | unsuccessfulTrial
  deriving DecidableEq

/-- Membership in the trial set `T`. -/
def DynamicAccuracyIterationKind.isTrial (k : DynamicAccuracyIterationKind) : Prop :=
  k = .successfulTrial ∨ k = .unsuccessfulTrial

/-- Exact function calls per iteration: IDA evaluates the objective only at trial attempts. -/
def DynamicAccuracyIterationKind.functionCalls : DynamicAccuracyIterationKind → ℕ
  | .accuracyOnly => 0
  | .successfulTrial => 1
  | .unsuccessfulTrial => 1

/-- Derivative batches to prepare the next iteration: a success changes the point and an
accuracy refinement changes the requests; an unsuccessful trial retains cached tensors. -/
def DynamicAccuracyIterationKind.derivativeBatches : DynamicAccuracyIterationKind → ℕ
  | .accuracyOnly => 1
  | .successfulTrial => 1
  | .unsuccessfulTrial => 0

/-- Cached tensors retain both the evaluation point and requested accuracies. These data
are available independently of the as yet open legal algorithm transition relations. -/
structure DynamicAccuracyCache where
  point : EuclideanSpace ℝ (Fin n)
  request : ℕ → ℝ
  derivative : ∀ i : ℕ,
    ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin n)) ℝ
  functionCalls : ℕ
  derivativeBatches : ℕ

/-- Equations (13.1.3), (13.1.4), (13.1.6), (13.1.8), and (13.1.10)–(13.1.11),
including both bounds in (13.1.3). The maxima `K` and `H` may be any common upper bounds
on active multipliers and requests. The last clause uses the step-dependent accuracy
condition and includes zero steps and zero error constants. -/
theorem taylor_decrement_error
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin n)) ℝ)
    {r j : ℕ} (hjr : j ≤ r) (κ h : ℕ → ℝ) {K H : ℝ}
    (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hh : ∀ i ∈ Finset.Icc 1 r, 0 ≤ h i)
    (hκK : ∀ i ∈ Finset.Icc 1 r, κ i ≤ K)
    (hhH : ∀ i ∈ Finset.Icc 1 r, h i ≤ H)
    (hcoeff : ∀ i ∈ Finset.Icc 1 r, ‖A i - iteratedFDeriv ℝ i f x‖ ≤ κ i * h i) :
    (∀ s : EuclideanSpace ℝ (Fin n),
      |inexactTaylorDecrement A j s - Chapter12.Section01.taylorDecrement f j x s| ≤
      ∑ i ∈ Finset.Icc 1 j, ‖A i - iteratedFDeriv ℝ i f x‖ * ‖s‖ ^ i / (i ! : ℝ)) ∧
    (∀ s : EuclideanSpace ℝ (Fin n),
      (∑ i ∈ Finset.Icc 1 j, ‖A i - iteratedFDeriv ℝ i f x‖ * ‖s‖ ^ i / (i ! : ℝ)) ≤
      ∑ i ∈ Finset.Icc 1 j, κ i * h i * ‖s‖ ^ i / (i ! : ℝ)) ∧
    (∀ (c : ℝ) (s : EuclideanSpace ℝ (Fin n)),
      |inexactTaylorModel c A j s - RegularizedTaylorModel.taylorModel f j x s| ≤
      |c - f x| + ∑ i ∈ Finset.Icc 1 j, κ i * h i * ‖s‖ ^ i / (i ! : ℝ)) ∧
    (∀ δ ∈ Set.Icc (0 : ℝ) 1, Chapter12.Section01.taylorCriticality f j δ x ≤
      inexactTaylorCriticality A j δ + 2 * K * H) ∧
    (∀ s : EuclideanSpace ℝ (Fin n),
      |inexactTaylorModel (f x) A j s - RegularizedTaylorModel.taylorModel f j x s| =
      |inexactTaylorDecrement A j s - Chapter12.Section01.taylorDecrement f j x s|) ∧
    (∀ (s : EuclideanSpace ℝ (Fin n)) (κs : ℝ), 0 ≤ κs →
      (∀ i ∈ Finset.Icc 1 j, h i ≤ κs * ‖s‖ ^ (r - i + 1)) →
      |inexactTaylorDecrement A j s - Chapter12.Section01.taylorDecrement f j x s| ≤
        2 * K * κs * ‖s‖ ^ (r + 1)) := by
  have hmem (i : ℕ) (hi : i ∈ Finset.Icc 1 j) : i ∈ Finset.Icc 1 r :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hjr⟩
  have herr (s : EuclideanSpace ℝ (Fin n)) :
      |decrement A j s - TaylorCriticality.taylorDecrement f j x s| ≤
        ∑ i ∈ Finset.Icc 1 j, κ i * h i * ‖s‖ ^ i / (i ! : ℝ) := by
    rw [← decrement_iteratedFDeriv]
    exact decrement_error_le _ _ _ j s (fun i hi => hcoeff i (hmem i hi))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [Chapter12.Section01.taylorDecrement, ← decrement_iteratedFDeriv]
    exact decrement_error_le _ _ _ j s (fun _ _ => le_rfl)
  · intro s
    apply Finset.sum_le_sum
    intro i hi
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcoeff i (hmem i hi)) (pow_nonneg (norm_nonneg s) _))
      (by positivity)
  · intro c s
    exact (polynomial_error_le f x c A j s).trans (add_le_add le_rfl (herr s))
  · intro δ hδ
    have hgap := gap_error_le A (fun i => iteratedFDeriv ℝ i f x) (fun i => κ i * h i)
      (q := j) (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) δ)
      (show (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ).Nonempty from
        ⟨0, by simpa using hδ.1⟩) hδ.1 (Set.Subset.refl _)
      (fun i hi => hcoeff i (hmem i hi))
    have hsum := error_sum_le (q := j) hδ (mul_nonneg hK hH)
      (fun i hi => mul_le_mul (hκK i (hmem i hi)) (hhH i (hmem i hi))
        (hh i (hmem i hi)) hK)
    have heq : decrement (fun i => iteratedFDeriv ℝ i f x) j =
        TaylorCriticality.taylorDecrement f j x := funext (decrement_iteratedFDeriv f x j)
    rw [heq] at hgap
    have := (abs_le.mp hgap).1
    change TaylorCriticality.gapOn (TaylorCriticality.taylorDecrement f j x)
      (Metric.closedBall 0 δ) ≤ _
    dsimp [inexactTaylorCriticality, inexactTaylorDecrement]
    linarith
  · exact polynomial_error_eq f x A j
  · intro s κs hκs hstep
    rw [Chapter12.Section01.taylorDecrement, ← decrement_iteratedFDeriv]
    apply decrement_error_le_step_power _ _ s hjr hK hκs
    intro i hi
    exact (hcoeff i (hmem i hi)).trans
      (calc
        κ i * h i ≤ K * (κs * ‖s‖ ^ (r - i + 1)) :=
          mul_le_mul (hκK i (hmem i hi)) (hstep i hi) (hh i (hmem i hi)) hK
        _ = K * κs * ‖s‖ ^ (r - i + 1) := by ring)

/-- Equation (13.1.45): the actual regularized inexact polynomial. -/
abbrev inexactRegularizedModel (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin n)) ℝ)
    (p : ℕ) (σ : ℝ) (s : EuclideanSpace ℝ (Fin n)) : ℝ := regularizedPolynomial c A p σ s

/-- Lemma 13.1.10 under the genuine approximate-coefficient bound (13.1.63). The
polynomial tail and the radial regularizer are both bounded, yielding the full model
decrease (13.1.65) from the truncated decrement at any active order. -/
theorem lemma_13_1_10 (c : ℝ)
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin n)) ℝ)
    {j p : ℕ} (hjp : j ≤ p) {L σ δ α : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsmall : δ ≤ α / (4 * max L σ))
    (d : EuclideanSpace ℝ (Fin n)) (hd : ‖d‖ ≤ δ)
    (hA : ∀ i ∈ Finset.Icc (j + 1) p, ‖A i‖ ≤ L)
    (hdec : α * δ ^ j / (j ! : ℝ) ≤ inexactTaylorDecrement A j d) :
    α * δ ^ j / (2 * (j ! : ℝ)) ≤ c - inexactRegularizedModel c A p σ d := by
  apply half_decrease_of_small_radius c A hjp hL.le ⟨hδ.le, hδ1⟩ d hd hA ?_ hdec
  have hM : 0 < 4 * max L σ := mul_pos (by norm_num) (hL.trans_le (le_max_left _ _))
  have hh := (le_div_iff₀ hM).mp hsmall
  nlinarith only [hh]

/-- Lemma 13.1.13 under its actual Step 1 and Step 2 model premises: the positive Step 1
witness (13.1.54) is retained by (13.1.55). This proves all of (13.1.76), strict positivity
of the denominator in (13.1.58), and nonzeroness of the trial displacement. -/
theorem lemma_13_1_13 (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (A : ∀ i : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin i => EuclideanSpace ℝ (Fin n)) ℝ)
    (p j : ℕ) {σ varsigma ε δ : ℝ} (hσ : 0 ≤ σ)
    (hv : 0 < varsigma) (hε : 0 < ε) (hδ : 0 < δ)
    (d s : EuclideanSpace ℝ (Fin n))
    (hStep1 : varsigma * ε * δ ^ j / (4 * (j ! : ℝ)) ≤
      f x - inexactRegularizedModel (f x) A p σ d)
    (hStep2 : inexactRegularizedModel (f x) A p σ s ≤
      inexactRegularizedModel (f x) A p σ d) :
    σ * ‖s‖ ^ (p + 1) / ((p + 1)! : ℝ) ≤ inexactTaylorDecrement A p s ∧
      0 < inexactTaylorDecrement A p s ∧ s ≠ 0 := by
  apply decrement_pos_of_retained_model_decrease (f x) A p hσ ?_ hStep2
  have hpos : 0 < varsigma * ε * δ ^ j / (4 * (j ! : ℝ)) := by positivity
  linarith

end CartisGouldToint.Chapter13.Section01
