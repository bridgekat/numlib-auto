import NumlibSurface.CartisGouldToint.Chapter13.Section01
import Numlib.Optimization.InexactRegularizationAccuracy

/-!
# Chapter 13, Section 1: actual ARqpIDA inspections and executions

The legal algorithm uses the supplied approximate tensors, preserves every chosen witness,
and separates accuracy refinement from exact-objective trials. The first radius-search
analysis and trial logarithmic budget are complete. The later all-order jet/radius analysis
and true-quality complexity theorem remain in the parent plan.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter13.Section01
open Optimization InexactRegularization InexactTaylorModels

variable {n : ℕ}

/-- Initialization constants of Algorithm 13.1.2, including the independent initial request
bound, geometric accuracy factor and the regularization update constants. -/
abbrev ARqpIDAParameters := InexactRegularization.Parameters

/-- Algorithm 13.1.2: actual finite prefixes with approximate tensor queries, pre/post
inspection radii, returned Algorithm 12.2.3 executions, and exact-objective acceptance.
The two Step 5 branches restore the pre-inspection radii and keep σ fixed. The literal
Step 2 branch checks only derivative orders one through `q` on short steps, despite the
all-`p` requirement in (13.1.46). Its long-step exception is also retained. The initial
function value is counted separately; rejected trials retain the same point/request cache key. -/
abbrev algorithm_13_1_2 (P : ARqpIDAParameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (O : ImplicitAccuracyOracle f P.p) (N : ℕ) : Type :=
  InexactRegularization.Execution P P.q f O.derivative N

/-- The all-order variant of Algorithm 13.1.2 checks every derivative order through `p`
on short steps, as requested by the prose (13.1.46). It retains the printed long-step
exception. This is explicitly separate from the literal `q`-checked source algorithm. -/
abbrev arqpida_allp_algorithm (P : ARqpIDAParameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (O : ImplicitAccuracyOracle f P.p) (N : ℕ) : Type :=
  InexactRegularization.Execution P P.p f O.derivative N

/-- Lemma 13.1.9: the exact trial-count estimate on actual finite prefixes. Accuracy-only
iterations leave the parameter unchanged and make no logarithmic contribution. -/
theorem lemma_13_1_9 {P : ARqpIDAParameters} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {O : ImplicitAccuracyOracle f P.p} {N : ℕ} (r : algorithm_13_1_2 P f O N)
    {σmax : ℝ} (hmax : (r.state N).sigma ≤ σmax) :
    (r.trialCount : ℝ) ≤ (r.acceptedCount : ℝ) *
      (1 + |Real.log P.gamma1| / Real.log P.gamma2) +
      Real.log (σmax / (r.state 0).sigma) / Real.log P.gamma2 :=
  r.trial_count_le hmax

/-- Lemma 13.1.11: every legal halving prefix is uniformly finite, all its intermediate
radii satisfy (13.1.66), and every sequence of actual fraction-witness choices has a first
finished search. The genuine approximate-coefficient bound (13.1.63) is used directly. -/
theorem lemma_13_1_11 (c : ℝ)
    (A : Coefficients (EuclideanSpace ℝ (Fin n))) {p j : ℕ} (hjp : j ≤ p)
    {L σ δ v ε : ℝ} (hL : 0 < L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hv : 0 < v) (hε : 0 < ε)
    (hA : ∀ i ∈ Finset.Icc (j + 1) p, ‖A i‖ ≤ L) :
    (∀ N (_s : RadiusSearch c A p j σ δ v ε N),
      N ≤ HigherOrderApproximateRegularization.geometricCountdown
        (v * ε / (8 * max L σ)) δ ∧
      ∀ k, k ≤ N → δ ≥ halvedRadius δ k ∧ halvedRadius δ k ≥ halvedRadius δ N ∧
        min (v * ε / (16 * max L σ)) δ ≤ halvedRadius δ N) ∧
    (∀ (d : ℕ → EuclideanSpace ℝ (Fin n)),
      (∀ k, CoefficientWitness A j (halvedRadius δ k) v (d k)) →
      ∃ N : ℕ, N ≤ HigherOrderApproximateRegularization.geometricCountdown
        (v * ε / (8 * max L σ)) δ ∧
        ∃ s : RadiusSearch c A p j σ δ v ε N, s.direction = d ∧ s.Finished) := by
  constructor
  · intro N s
    exact ⟨s.length_le hjp hL hδ hv hε hA, fun _ hk =>
      s.radius_bounds hjp hL hδ hA hk⟩
  · exact fun d hd => exists_finished_search c A hjp hL hδ hv hε hA d hd

/-- The all-`p` variant permits a uniform σ bound with `max κ_s κ_h`.
The printed κ_s-only bound of Lemma 13.1.14 is kept open separately because κ_h and κ_s
are independent in (13.1.51). This result assumes actual oracle coefficient-error bounds
and applies only to the
all-`p` variant. No bound is claimed here for unchecked orders in the literal `q` variant. -/
theorem arqpida_allp_sigma_upper {P : ARqpIDAParameters}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ImplicitAccuracyOracle f P.p} {N : ℕ}
    (r : arqpida_allp_algorithm P f O N) {L K : ℝ}
    (hf : HigherOrderRegularization.DiagonalLipschitz f P.p L) (hK : 0 ≤ K)
    (hcoeff : ∀ k < N, ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state k).point (r.state k).request i -
        iteratedFDeriv ℝ i f (r.state k).point‖ ≤ K * (r.state k).request i)
    {k : ℕ} (hk : k ≤ N) :
    (r.state k).sigma ≤ max (r.state 0).sigma
      (P.gamma3 * ((2 * L + 4 * ((P.p + 1)! : ℝ) *
        max P.kappaStep P.kappaInitial * K) / (1 - P.eta2))) :=
  r.sigma_upper hf hK hcoeff hk

/-- The Step 1→5 branch attains true approximate optimality once its inspected radii have
the source floor and the independent uniform-error budget is sufficiently small. This is
a local certificate at the actual inspected radii; no claim about literal stopping is made. -/
theorem arqpida_true_quality_of_uniform_accuracy {P : ARqpIDAParameters}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ImplicitAccuracyOracle f P.p}
    {x : EuclideanSpace ℝ (Fin n)} {h δ : ℕ → ℝ} {σ : ℝ}
    (I : Inspection P (f x) (O.derivative x h) σ δ) (hall : I.order = P.q + 1)
    (hδ : HigherOrderApproximateRegularization.ValidRadii P.toParameters δ)
    {κ ε K H : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε)
    (hεj : ∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j)
    (hlower : ∀ j, 1 ≤ j → j ≤ P.q → κ * ε ≤ I.radii j)
    (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hcoeff : ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative x h i - iteratedFDeriv ℝ i f x‖ ≤ K * H)
    (hsmall : 4 * (P.q ! : ℝ) * K * H ≤ P.fraction * κ ^ P.q * ε ^ (P.q + 1)) :
    HigherOrderApproximateRegularization.SatisfiesCriteria P.toParameters f x I.radii :=
  I.true_quality_of_uniform_accuracy hall hδ hκ hε hεj hlower hK hH hcoeff hsmall

end CartisGouldToint.Chapter13.Section01
