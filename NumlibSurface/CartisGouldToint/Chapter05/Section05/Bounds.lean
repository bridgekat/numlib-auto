import NumlibSurface.CartisGouldToint.Chapter05.Section05
import Numlib.Optimization.UniversalRegularizationBounds

/-!
# Chapter 5, Section 5: sufficient universal-regularization success

The common coefficient is exactly (5.5.19). Both activated orders share the same threshold.
The final exponent in the transcribed curvature computation is corrected to `r - 2`;
the preceding powers and the length test (5.5.11) determine this exponent. In the sentence
following (5.5.38), the second-order tolerance is `epsilon 1` in zero-based notation,
that is the printed mathematical `epsilon₂`, correcting the transcribed `epsilon₁`.
-/

noncomputable section
namespace CartisGouldToint.Chapter05.Section05
open Optimization.UniversalRegularization

/-- The coefficient (5.5.19) common to both active criticality orders. -/
abbrev universalSuccessCoefficient (H t r eta : ℝ) : ℝ := successCoefficient H t r eta

/-- Lemma 5.5.3: the actual trial is very successful under (5.5.18), with the additional
second residual threshold (5.5.20) when second-order criticality is active. This includes
`r = p + beta` and a vanishing Hölder constant, without a positive parameter floor. -/
theorem lemma_5_5_3 {n q p : ℕ} [NeZero n] {r sigma H beta : ℝ}
    {a : universalParameters q p r} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : EuclideanSpace ℝ (Fin n)} (hf : holderDerivativeAssumption f p H beta)
    (htr : (p : ℝ) + beta ≤ r) (hsigma : 0 < sigma)
    (hs : universalComputedStep a f x sigma s)
    (htheta1 : a.theta 0 * realPowerFactorial (r - 1) ≤ sigma)
    (htheta2 : 2 ≤ q → a.theta 1 * realPowerFactorial (r - 2) ≤ sigma)
    (hlarge : universalSuccessCoefficient H ((p : ℝ) + beta) r a.eta2 *
      ‖s‖ ^ ((p : ℝ) + beta - r) ≤ sigma) : VerySuccessful a f x sigma s :=
  hs.verySuccessful_of_threshold hf.toHolderDerivative htr hsigma htheta1 htheta2 hlarge

/-- The coefficients (5.5.28) and (5.5.30), indexed by the active derivative order. -/
abbrev universalToleranceCoefficient (H t r eta j : ℝ) : ℝ :=
  toleranceCoefficient (universalSuccessCoefficient H t r eta)
    (realPowerFactorial (r - j)) t r j

/-- Lemma 5.5.4: before actual trial termination, the tolerance thresholds imply the
step-dependent threshold and hence very success. The two active orders use their own
positive derivative exponent; equality `r = p + beta` is included. -/
theorem lemma_5_5_4 {n q p : ℕ} [NeZero n] {r sigma H beta : ℝ}
    {a : universalParameters q p r} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : EuclideanSpace ℝ (Fin n)} (hf : holderDerivativeAssumption f p H beta)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (htr : (p : ℝ) + beta ≤ r)
    (hsigma : 0 < sigma) (hs : universalComputedStep a f x sigma s)
    (hnonterminal : ¬Stationary a f (x + s))
    (htheta1 : a.theta 0 * realPowerFactorial (r - 1) ≤ sigma)
    (htheta2 : 2 ≤ q → a.theta 1 * realPowerFactorial (r - 2) ≤ sigma)
    (htolerance1 : universalToleranceCoefficient H ((p : ℝ) + beta) r a.eta2 1 *
      a.epsilon 0 ^ (((p : ℝ) + beta - r) / ((p : ℝ) + beta - 1)) ≤ sigma)
    (htolerance2 : 2 ≤ q → universalToleranceCoefficient H ((p : ℝ) + beta) r a.eta2 2 *
      a.epsilon 1 ^ (((p : ℝ) + beta - r) / ((p : ℝ) + beta - 2)) ≤ sigma) :
    universalSuccessCoefficient H ((p : ℝ) + beta) r a.eta2 *
        ‖s‖ ^ ((p : ℝ) + beta - r) ≤ sigma ∧ VerySuccessful a f x sigma s := by
  have hh := hs.threshold_of_nonstationary hf.toHolderDerivative hexp htr hsigma
    hnonterminal htheta1 htheta2 htolerance1 htolerance2
  exact ⟨hh, lemma_5_5_3 hf htr hsigma hs htheta1 htheta2 hh⟩

/-- The maximum of the active model-residual and tolerance thresholds in (5.5.27),(5.5.29). -/
abbrev universalSuccessThreshold {q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (H t : ℝ) : ℝ := successThreshold a H t

/-- The tolerance-independent constant (5.5.42), with both criticality orders active. -/
abbrev universalUniformSigma {q p : ℕ} {r : ℝ} (a : universalParameters q p r)
    (H t initial : ℝ) : ℝ := uniformSigma a H t initial

/-- Lemma 5.5.5: the actual update intervals give (5.5.39),(5.5.40) at every legal
prefix endpoint. With second-order criticality active, this also gives (5.5.41) with the
uniform constant (5.5.42). The endpoint may be the last parameter before a terminal trial. -/
theorem lemma_5_5_5 {n q p N k : ℕ} [NeZero n] {r H beta : ℝ}
    {a : universalParameters q p r} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x s : ℕ → EuclideanSpace ℝ (Fin n)} {sigma : ℕ → ℝ}
    (h : universalPrefix a f x s sigma N) (hf : holderDerivativeAssumption f p H beta)
    (hexp : (q : ℝ) < (p : ℝ) + beta) (htr : (p : ℝ) + beta ≤ r) (hk : k ≤ N) :
    sigma k ≤ max (sigma 0) (a.gamma3 * universalSuccessThreshold a H ((p : ℝ) + beta)) ∧
      (2 ≤ q → sigma k ≤ universalUniformSigma a H ((p : ℝ) + beta) (sigma 0) *
        max (a.epsilon 0 ^ (((p : ℝ) + beta - r) / ((p : ℝ) + beta - 1)))
          (a.epsilon 1 ^ (((p : ℝ) + beta - r) / ((p : ℝ) + beta - 2)))) :=
  ⟨h.sigma_upper hf.toHolderDerivative hexp htr hk,
    fun hq => h.sigma_upper_uniform hf.toHolderDerivative hexp htr hq hk⟩

end CartisGouldToint.Chapter05.Section05
