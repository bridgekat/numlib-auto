import Numlib.Analysis.Calculus.FiniteDerivativeStencil
import NumlibSurface.CartisGouldToint.Chapter13.Section01.TRqIDA
import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDAComplexity
import Numlib.Optimization.InexactRegularizationQueries
import Numlib.Optimization.RegularizationToleranceMeasure

/-!
# Chapter 13, Section 2: finite low-degree derivative schemes

A finite scheme specifies actual linear stencils, their polynomial cancellation and
contracting sample geometry, and verified uniform error bounds. Its query costs may depend
on dimension and orders, but are fixed before requested accuracies. This interface does
not assert a general stencil existence theorem. The trust-region specialization below
expands the actual objective and tensor-batch logs into lower-degree oracle calls.

Both methods use literal expanded low-degree query schedules. The full Theorem 13.2.1
combines both branches, with fixed constants and pure inverse powers of the common minimum
tolerance. This repairs the transcription's minimum of inverse tolerance powers. The
adaptive-regularization branch follows the strict algorithm tolerance domain and the
corrected fixed-initialization constants documented in Theorem 13.1.19.
-/

noncomputable section
open Optimization InexactTrustRegion HigherOrderTrustRegion
namespace CartisGouldToint.Chapter13.Section02
variable {n o p q : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- A verified finite derivative-approximation scheme. Every higher-order tensor is a
fixed finite linear combination of actual oracle replies of degrees at most `o`; exact
Taylor-polynomial cancellation and contraction accompany its proved all-point accuracy
contract. Costs may depend on `n`, `o`, `p` and the chosen stencils, but not the requests.
The error proof is required when constructing a scheme; no arbitrary estimator or general
existence axiom is part of this definition. -/
abbrev FiniteDerivativeApproximationScheme
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (o p : ℕ) :=
  FiniteDerivativeStencil.VerifiedScheme f o p

/-- Verified finite reconstruction supplies the actual Section 13.1 oracle interface.
The available low orders are exact, and each higher mesh is clipped at one. -/
def FiniteDerivativeApproximationScheme.toImplicitAccuracyOracle
    (S : FiniteDerivativeApproximationScheme f o p) : Section01.ImplicitAccuracyOracle f p where
  derivative := S.oracle
  accuracy := ⟨S.errorMultiplier, fun _ hi => S.errorMultiplier_nonneg hi,
    fun x h hh _ hi => S.oracle_accuracy x h hi (hh _ hi)⟩

/-- The actual eager low-degree query schedule: exact objective calls and every sample of
every full stencil batch. Repeated points and degrees remain paid queries. -/
def lowDegreeQueries (S : FiniteDerivativeApproximationScheme f o q) (params : Parameters)
    (t : InexactTrustRegion.Trace (EuclideanSpace ℝ (Fin n))) (N : ℕ) :
    List (EuclideanSpace ℝ (Fin n) × Fin (o + 1)) :=
  S.expandedQueries (functionQueries t N)
    (derivativeQueries params (Section01.TRqIDA.oracle S.toImplicitAccuracyOracle) t N)

/-- Exact low-degree query expansion pays the fixed finite stencil cost per actual batch. -/
theorem lowDegreeQueries_length (S : FiniteDerivativeApproximationScheme f o q)
    (params : Parameters) (t : InexactTrustRegion.Trace (EuclideanSpace ℝ (Fin n))) (N : ℕ) :
    (lowDegreeQueries S params t N).length = (functionQueries t N).length + S.batchCost *
      (derivativeQueries params (Section01.TRqIDA.oracle S.toImplicitAccuracyOracle) t N).length :=
  S.expandedQueries_length _ _

/-- The trust-region part of Theorem 13.2.1, with the actual low-degree query schedule.
Fixed positive coefficients are chosen before every tolerance vector and legal run.
The rate is the inverse `(q+1)` power of the minimum tolerance, plus the explicit logarithmic
accuracy cost. The counted stop is first true approximate quality, rather than an
observable stopping certificate. The adaptive-regularization branch is supplied below.
This theorem assumes a verified scheme, not existence of one at arbitrary orders. -/
theorem trq_complexity_low_degree_oracles (params : Parameters) (a : AccuracyParameters)
    (S : FiniteDerivativeApproximationScheme f o q) (hf : Section01.ImplicitSmoothness f q)
    {initial kappaInitial low : ℝ} (hi : 0 < initial) (hlow : ∀ x, low ≤ f x) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧
      ∀ (epsilon : ℕ → ℝ) (t : InexactTrustRegion.Trace (EuclideanSpace ℝ (Fin n))),
        t.radius 0 = initial →
        Section01.algorithm_13_1_1 params a q epsilon kappaInitial S.toImplicitAccuracyOracle t →
        ∃ k : ℕ, Quality (q := q) params epsilon f t k ∧
          (∀ j < k, ¬Quality (q := q) params epsilon f t j) ∧
          (0 < testRadius params t k ∧ testRadius params t k ≤ 1) ∧
          ((lowDegreeQueries S params t k).length : ℝ) ≤
            A * (f (t.point 0) - low) /
              Chapter12.Section02.TRq.epsilonMinimum q epsilon ^ (q + 1) +
            B * |Real.log (Chapter12.Section02.TRq.epsilonMinimum q epsilon)| + C := by
  obtain ⟨A, B, C, D, F, G, hA, hB, hC, hD, hF, hG, hb⟩ :=
    Section01.theorem_13_1_8 params a q S.toImplicitAccuracyOracle hf hi hlow
  refine ⟨A + S.batchCost * D, B + S.batchCost * F, C + S.batchCost * G,
    by positivity, by positivity, by positivity, ?_⟩
  intro epsilon t hinit h
  obtain ⟨k, hk, hfirst, hrad, hvalues, hbatches⟩ := hb epsilon t hinit h
  refine ⟨k, hk, hfirst, hrad, ?_⟩
  have hc := S.expandedQueries_length_le (functionQueries t k)
    (derivativeQueries params (Section01.TRqIDA.oracle S.toImplicitAccuracyOracle) t k)
    hvalues hbatches
  change ((S.expandedQueries _ _).length : ℝ) ≤ _
  convert hc using 1
  ring


open InexactRegularization

/-- Expand the actual objective and fresh tensor-batch logs of a complete literal ARqpIDA
run into the fixed scheme's low-degree queries, paying repeated samples separately. -/
def arqpLowDegreeQueries (params : Section01.ARqpIDAParameters)
    (S : FiniteDerivativeApproximationScheme f o params.p)
    (r : InexactRegularization.Run params params.q f S.toImplicitAccuracyOracle.derivative)
    (N : ℕ) : List (EuclideanSpace ℝ (Fin n) × Fin (o + 1)) :=
  S.expandedQueries (r.functionQueries N) (r.derivativeQueries N)

/-- Exact stencil expansion pays initialization, actual objective trials, and the fixed
sample cost for every actual fresh tensor batch. -/
theorem arqpLowDegreeQueries_length (params : Section01.ARqpIDAParameters)
    (S : FiniteDerivativeApproximationScheme f o params.p)
    (r : InexactRegularization.Run params params.q f S.toImplicitAccuracyOracle.derivative)
    (N : ℕ) :
    (arqpLowDegreeQueries params S r N).length = (r.prefix N).functionCount +
      S.batchCost * (r.prefix N).derivativeBatches := by
  simp only [arqpLowDegreeQueries, S.expandedQueries_length,
    r.functionQueries_length, r.derivativeQueries_length]

/-- The adaptive-regularization part of Theorem 13.2.1. Constants are fixed before every
admissible tolerance vector and actual complete run, and the low-degree calls are the
literal finite-stencil expansion. The common minimum tolerance has exponent
`(p+1)/(p-q+1)` at q<=2 and `q*(p+1)/p` at q>2. The strict algorithm tolerance domain and
corrected fixed-initialization constants follow Theorem 13.1.19. -/
theorem arqp_complexity_low_degree_oracles (params : Section01.ARqpIDAParameters)
    (S : FiniteDerivativeApproximationScheme f o params.p)
    (hf : Section01.ImplicitSmoothness f params.p) (h0 : ℕ → ℝ) {sigma0 low : ℝ}
    (hsigma : params.sigmaMin ≤ sigma0) (hlow : ∀ x, low ≤ f x) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧
      ∀ (epsilon : ℕ → ℝ)
        (hpos : ∀ j, 1 ≤ j → j ≤ params.q → 0 < epsilon j)
        (hlt : ∀ j, 1 ≤ j → j ≤ params.q → epsilon j < 1)
        (r : InexactRegularization.Run (params.withTolerances epsilon hpos hlt) params.q f
          S.toImplicitAccuracyOracle.derivative),
        (r.state 0).request = h0 → (r.state 0).sigma = sigma0 →
        ∃ k : ℕ, PointQuality (params.withTolerances epsilon hpos hlt) f (r.state k).point ∧
          (∀ j < k, ¬PointQuality (params.withTolerances epsilon hpos hlt) f (r.state j).point) ∧
          ((arqpLowDegreeQueries (params.withTolerances epsilon hpos hlt) S r k).length : ℝ) ≤
            A * (f (r.state 0).point - low) /
                Chapter12.Section02.TRq.epsilonMinimum params.q epsilon ^
                  HigherOrderApproximateRegularization.complexityExponent
                    params.p params.q params.q +
              B * |Real.log (Chapter12.Section02.TRq.epsilonMinimum params.q epsilon)| + C := by
  obtain ⟨A, C, D, E, F, hA, hC, hD, hE, hF, hbounds⟩ :=
    Section01.theorem_13_1_19 params S.toImplicitAccuracyOracle hf h0 hsigma hlow
  let c : ℝ := S.batchCost
  have hc : 0 ≤ c := Nat.cast_nonneg _
  refine ⟨A + c * D, c * E + 1, C + c * F,
    add_pos_of_pos_of_nonneg hA (mul_nonneg hc hD.le),
    add_pos_of_nonneg_of_pos (mul_nonneg hc hE.le) one_pos,
    add_pos_of_pos_of_nonneg hC (mul_nonneg hc hF.le), ?_⟩
  intro epsilon hpos hlt r hrequest hsig
  obtain ⟨k, hquality, hfirst, hfunction, hderivative⟩ :=
    hbounds epsilon hpos hlt r hrequest hsig
  refine ⟨k, hquality, hfirst, ?_⟩
  have he := Chapter12.Section02.TRq.epsilonMinimum_pos params.order_pos hpos
  have helower : ∀ j, 1 ≤ j → j ≤ params.q →
      Chapter12.Section02.TRq.epsilonMinimum params.q epsilon ≤ epsilon j :=
    fun _ hj hjq => Chapter12.Section02.TRq.epsilonMinimum_le epsilon hj hjq
  have he1 : Chapter12.Section02.TRq.epsilonMinimum params.q epsilon ≤ 1 :=
    (helower 1 le_rfl params.order_pos).trans (hlt 1 le_rfl params.order_pos).le
  have hgap : 0 ≤ f (r.state 0).point - low := sub_nonneg.mpr (hlow _)
  have hv := HigherOrderApproximateRegularization.div_toleranceMeasure_le_common_rpow
    params.p params.q params.order_pos he he1 helower (mul_nonneg hA.le hgap)
  have hd := HigherOrderApproximateRegularization.div_toleranceMeasure_le_common_rpow
    params.p params.q params.order_pos he he1 helower (mul_nonneg hD.le hgap)
  have hvalues : ((r.functionQueries k).length : ℝ) ≤
      A * (f (r.state 0).point - low) /
          Chapter12.Section02.TRq.epsilonMinimum params.q epsilon ^
            HigherOrderApproximateRegularization.complexityExponent
              params.p params.q params.q + C := by
    rw [r.functionQueries_length]
    exact hfunction.trans (add_le_add hv le_rfl)
  have hbatches : ((r.derivativeQueries k).length : ℝ) ≤
      D * (f (r.state 0).point - low) /
          Chapter12.Section02.TRq.epsilonMinimum params.q epsilon ^
            HigherOrderApproximateRegularization.complexityExponent params.p params.q params.q +
        E * |Real.log (Chapter12.Section02.TRq.epsilonMinimum params.q epsilon)| + F := by
    rw [r.derivativeQueries_length]
    exact hderivative.trans (add_le_add (add_le_add hd le_rfl) le_rfl)
  have hexpanded := S.expandedQueries_length_le (r.functionQueries k) (r.derivativeQueries k)
    hvalues hbatches
  have hb :
      ((arqpLowDegreeQueries (params.withTolerances epsilon hpos hlt) S r k).length : ℝ) ≤
        (A + c * D) * (f (r.state 0).point - low) /
            Chapter12.Section02.TRq.epsilonMinimum params.q epsilon ^
              HigherOrderApproximateRegularization.complexityExponent params.p params.q params.q +
          (c * E) * |Real.log (Chapter12.Section02.TRq.epsilonMinimum params.q epsilon)| +
          (C + c * F) := by
    change ((S.expandedQueries _ _).length : ℝ) ≤ _
    convert hexpanded using 1 <;> first | rfl | ring
  have hlog := abs_nonneg
    (Real.log (Chapter12.Section02.TRq.epsilonMinimum params.q epsilon))
  exact hb.trans (by nlinarith only [hlog])


/-- Theorem 13.2.1 for one fixed verified finite low-degree scheme: BOTH the trust-region
and adaptive-regularization algorithms attain first true quality within a pure common
inverse-power low-degree oracle budget. All constants precede every tolerance vector/run,
and every repeated stencil sample is counted. The TRq scheme is the original scheme
restricted to q; the ARqp scheme retains p. No general stencil existence is asserted.
The ARqp tolerance domain follows Algorithm 13.1.2, as documented in Theorem 13.1.19. -/
theorem theorem_13_2_1 (params : Section01.ARqpIDAParameters)
    (trparams : HigherOrderTrustRegion.Parameters) (a : AccuracyParameters)
    (S : FiniteDerivativeApproximationScheme f o params.p) (hoq : o ≤ params.q)
    (hf : Section01.ImplicitSmoothness f params.p) (h0 : ℕ → ℝ)
    {initial kappaInitial sigma0 low : ℝ} (hi : 0 < initial)
    (hsigma : params.sigmaMin ≤ sigma0) (hlow : ∀ x, low ≤ f x) :
    let Sq := S.restrictOrder hoq params.order_le
    ∃ KT KA : ℝ, 0 < KT ∧ 0 < KA ∧
      (∀ (epsilon : ℕ → ℝ) (t : InexactTrustRegion.Trace (EuclideanSpace ℝ (Fin n))),
        t.radius 0 = initial →
        Section01.algorithm_13_1_1 trparams a params.q epsilon kappaInitial
          (FiniteDerivativeApproximationScheme.toImplicitAccuracyOracle Sq) t →
        ∃ k : ℕ, Quality (q := params.q) trparams epsilon f t k ∧
          (∀ j < k, ¬Quality (q := params.q) trparams epsilon f t j) ∧
          (0 < testRadius trparams t k ∧ testRadius trparams t k ≤ 1) ∧
          ((lowDegreeQueries Sq trparams t k).length : ℝ) ≤
            KT * (f (t.point 0) - low + 1) /
              Chapter12.Section02.TRq.epsilonMinimum params.q epsilon ^ (params.q + 1)) ∧
      (∀ (epsilon : ℕ → ℝ)
        (hpos : ∀ j, 1 ≤ j → j ≤ params.q → 0 < epsilon j)
        (hlt : ∀ j, 1 ≤ j → j ≤ params.q → epsilon j < 1)
        (r : InexactRegularization.Run (params.withTolerances epsilon hpos hlt) params.q f
          S.toImplicitAccuracyOracle.derivative),
        (r.state 0).request = h0 → (r.state 0).sigma = sigma0 →
        ∃ k : ℕ, PointQuality (params.withTolerances epsilon hpos hlt) f (r.state k).point ∧
          (∀ j < k, ¬PointQuality (params.withTolerances epsilon hpos hlt) f (r.state j).point) ∧
          ((arqpLowDegreeQueries (params.withTolerances epsilon hpos hlt) S r k).length : ℝ) ≤
            KA * (f (r.state 0).point - low + 1) /
              Chapter12.Section02.TRq.epsilonMinimum params.q epsilon ^
                HigherOrderApproximateRegularization.complexityExponent
                  params.p params.q params.q) := by
  dsimp only
  have hfq : Section01.ImplicitSmoothness f params.q := by
    refine ⟨hf.contDiff.of_le ?_, fun i hi => hf.lipschitz i (hi.trans params.order_le)⟩
    exact_mod_cast params.order_le
  obtain ⟨A, B, C, hA, hB, hC, htrq⟩ :=
    trq_complexity_low_degree_oracles trparams a (S.restrictOrder hoq params.order_le)
      hfq (kappaInitial := kappaInitial) hi hlow
  obtain ⟨D, E, F, hD, hE, hF, harqp⟩ :=
    arqp_complexity_low_degree_oracles params S hf h0 hsigma hlow
  let alpha := HigherOrderApproximateRegularization.complexityExponent
    params.p params.q params.q
  have halpha : 0 < alpha :=
    HigherOrderApproximateRegularization.complexityExponent_pos
      (params.order_pos.trans params.order_le) params.order_pos
  refine ⟨A + B / ((params.q + 1 : ℕ) : ℝ) + C, D + E / alpha + F,
    by positivity, by positivity, ?_, ?_⟩
  · intro epsilon t hinit hrun
    obtain ⟨k, hquality, hfirst, hrad, hcost⟩ := htrq epsilon t hinit hrun
    refine ⟨k, hquality, hfirst, hrad, ?_⟩
    obtain ⟨he, he1⟩ := Section01.TRqIDA.algorithm.minimum_bounds hrun
    have hb := HigherOrderApproximateRegularization.logarithmic_budget_le_common_rpow
      (alpha := ((params.q + 1 : ℕ) : ℝ)) he he1 (by positivity)
      hA.le hB.le hC.le (sub_nonneg.mpr (hlow (t.point 0)))
    exact hcost.trans (by simpa only [Real.rpow_natCast] using hb)
  · intro epsilon hpos hlt r hrequest hsig
    obtain ⟨k, hquality, hfirst, hcost⟩ := harqp epsilon hpos hlt r hrequest hsig
    refine ⟨k, hquality, hfirst, ?_⟩
    have he := Chapter12.Section02.TRq.epsilonMinimum_pos params.order_pos hpos
    have he1 : Chapter12.Section02.TRq.epsilonMinimum params.q epsilon ≤ 1 :=
      (Chapter12.Section02.TRq.epsilonMinimum_le epsilon le_rfl params.order_pos).trans
        (hlt 1 le_rfl params.order_pos).le
    exact hcost.trans (HigherOrderApproximateRegularization.logarithmic_budget_le_common_rpow
      he he1 halpha hD.le hE.le hF.le (sub_nonneg.mpr (hlow (r.state 0).point)))

end CartisGouldToint.Chapter13.Section02
