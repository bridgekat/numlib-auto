import NumlibSurface.CartisGouldToint.Chapter13.Section03.ARqpEDA
import Numlib.Optimization.ExplicitRegularizationUniformAccuracy

/-!
# Global analysis bounds for actual ARqpEDA executions

The source global smoothness assumption supplies one objective constant before parameters,
tolerances, initialization, or oracle requests are chosen. The known unit-error contract
then gives a global supplied-tensor bound and the corrected parameter bound for every
actual literal checked execution. This does not restore the refuted printed constants or
assert certified termination or its evaluation complexity.
-/

noncomputable section
namespace CartisGouldToint.Chapter13.Section03
open Optimization InexactRegularization ExplicitRegularization
variable {n : ℕ}

/-- Global objective smoothness gives fixed analytic constants for the actual explicit
algorithm. The supplied tensor norm bound is valid at every positive capped request, and
sigma is bounded along each literal execution without assuming a parameter certificate.
The explicit formula retains the fixed initialization vector and its request ratios. -/
theorem ARqpEDA.uniform_analysis_bounds {p : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Section01.ImplicitSmoothness f p) :
    ∃ L : ℝ, 1 ≤ L ∧
      (∀ j, 1 ≤ j → j ≤ p → HigherOrderRegularization.DiagonalLipschitz f j L) ∧
      ∀ (P : ARqpEDAParameters), P.p = p → ∀ (O : ExplicitAccuracyOracle f P.p),
        (∀ x h, (∀ i ∈ Finset.Icc 1 P.p, 0 < h i) →
          (∀ i ∈ Finset.Icc 1 P.p, h i ≤ P.kappaInitial) →
          ∀ i ∈ Finset.Icc 1 P.p, ‖O.derivative x h i‖ ≤ L + P.kappaInitial) ∧
        ∀ (h0 : ℕ → ℝ) (σ0 : ℝ) (N : ℕ) (r : algorithm_13_3_2 P O N),
          (r.state 0).request = h0 → (r.state 0).sigma = σ0 →
          ∀ k, k ≤ N → (r.state k).sigma ≤
            correctedSigmaBound P.toImplicitParameters h0 σ0 L 1 := by
  obtain ⟨L, hL, hfL, hnorm⟩ := Section01.TRqIDA.exists_uniform_smoothness hf
  refine ⟨L, hL, hfL, ?_⟩
  intro P hp O
  have htrue : ∀ x i, 1 ≤ i → i ≤ P.p → ‖iteratedFDeriv ℝ i f x‖ ≤ L := by
    simpa only [hp] using hnorm
  refine ⟨fun x h hpos hcap i hi => O.derivative_norm_le htrue x h hpos hcap hi, ?_⟩
  intro h0 σ0 N r hrequest hσ k hk
  have hf' : HigherOrderRegularization.DiagonalLipschitz f P.p L :=
    hfL P.p (P.order_pos.trans P.order_le) (by omega)
  simpa only [hrequest, hσ] using r.sigma_upper hf' hk

/-- Every tensor request in a source execution keeps its original ratio to the first
request, through both refinements, both trial outcomes, and all value-cache behavior. -/
theorem ARqpEDA.request_ratios {P : ARqpEDAParameters}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ExplicitAccuracyOracle f P.p} {N : ℕ}
    (r : algorithm_13_3_2 P O N) {k : ℕ} (hk : k ≤ N) (i : ℕ) :
    (r.state k).request i / (r.state k).request 1 =
      (r.state 0).request i / (r.state 0).request 1 :=
  r.request_ratio hk i

/-- The global source assumption gives a corrected polynomial request threshold preventing
both actual accuracy-only branches. Its constants use the known unit-error oracle and fixed
initialization data. Certification means the literal error check at actual inspected radii;
no true-quality, sigma, radius, or desired complexity certificate is supplied. -/
theorem ARqpEDA.uniform_request_forcing {p : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Section01.ImplicitSmoothness f p) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (P : ARqpEDAParameters), P.p = p →
      ∀ (O : ExplicitAccuracyOracle f P.p) (N : ℕ) (r : algorithm_13_3_2 P O N)
        (ε : ℝ), 0 ≤ ε →
        (∀ j, 1 ≤ j → j ≤ P.q → ε ≤ P.epsilon j) →
        ∀ k, k < N →
          (∀ i ∈ Finset.Icc 1 P.p, (r.state k).request i ≤
            refinementThreshold P.toImplicitParameters (L + P.kappaInitial)
              (correctedSigmaBound P.toImplicitParameters (r.state 0).request
                (r.state 0).sigma L 1) 1 ε) → r.trial k = true := by
  obtain ⟨L, hL, hfL, hbounds⟩ := ARqpEDA.uniform_analysis_bounds hf
  refine ⟨L, hL, ?_⟩
  intro P hp O N r ε hε hεj k hk hh
  have hM : 1 ≤ L + P.kappaInitial := hL.trans (le_add_of_nonneg_right P.kappaInitial_nonneg)
  have hf' := hfL P.p (P.order_pos.trans P.order_le) (by omega)
  apply r.trial_of_small_uniform_request hM hf' ?_ hε hεj hk hh
  intro l hl i hi
  exact (hbounds P hp O).1 _ _ (fun _ hj => (r.request_bounds hl hj).1)
    (fun j hj => (r.request_bounds hl hj).2.trans (r.initial_request_le j hj)) i hi

end CartisGouldToint.Chapter13.Section03
