import NumlibSurface.CartisGouldToint.Chapter13.Section01.ARqpIDARadii
import Numlib.Optimization.InexactRegularizationRequestRatios

/-!
# Uniform bounds for the literal ARqpIDA algorithm with fixed initial requests

The literal short-step test checks only orders through q. Nevertheless its first checked
request controls every order because all requests contract together. The corrected bound
therefore depends on the maximum fixed initial request ratio, as well as the independent
initialization cap needed for unchecked long steps. Global analytic constants are chosen
before tolerances, initialization vectors or executions. This does not restore the false
printed constants or prove the separate first-attainment complexity assertion.
-/

noncomputable section
open scoped Nat
namespace CartisGouldToint.Chapter13.Section01
open Optimization InexactRegularization InexactTaylorModels

variable {n : ℕ}

/-- A corrected uniform sigma bound for literal Algorithm 13.1.2 at every p>=q>=1.
The global objective and oracle constants are chosen before the tolerance vector or run.
The explicit bound depends on the fixed initial request ratios through effectiveAccuracy;
no bound uniform over all initialization vectors is asserted. No true-quality, model-quality,
parameter-bound or evaluation-count certificate is among the hypotheses. -/
theorem arqpida_uniform_sigma_bound {p : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (O : ImplicitAccuracyOracle f p) (hf : ImplicitSmoothness f p) :
    ∃ L K : ℝ, 1 ≤ L ∧ 0 ≤ K ∧
      ∀ (h0 : ℕ → ℝ) (σ0 : ℝ) (P : ARqpIDAParameters), P.p = p →
        ∀ (N : ℕ) (r : InexactRegularization.Execution P P.q f O.derivative N),
          (r.state 0).request = h0 → (r.state 0).sigma = σ0 →
          ∀ k, k ≤ N → (r.state k).sigma ≤ max σ0
            (P.gamma3 * ((2 * L + 4 * ((P.p + 1)! : ℝ) *
              effectiveAccuracy P h0 * K) / (1 - P.eta2))) := by
  obtain ⟨L, hL, hfL, _⟩ := TRqIDA.exists_uniform_smoothness hf
  obtain ⟨K, hK, hO⟩ := (TRqIDA.oracle O).exists_uniformAccuracy
  refine ⟨L, K, hL, hK, ?_⟩
  intro h0 σ0 P hp N r hrequest hσ k hk
  have hf' : HigherOrderRegularization.DiagonalLipschitz f P.p L := by
    rw [hp]
    exact hfL p (by rw [← hp]; exact P.order_pos.trans P.order_le) le_rfl
  have he : ∀ l < N, ∀ i ∈ Finset.Icc 1 P.p,
      ‖O.derivative (r.state l).point (r.state l).request i -
        iteratedFDeriv ℝ i f (r.state l).point‖ ≤ K * (r.state l).request i := by
    intro l hl i hi
    apply hO _ _ (fun j hj => (r.request_bounds hl.le (by simpa only [hp] using hj)).1) i
      (by simpa only [hp] using hi)
  simpa only [hrequest, hσ] using
    r.sigma_upper_of_initial_requests P.order_pos hf' hK he hk

/-- For a given source execution, all actual requests keep their initial normalized ratios.
This applies unchanged to rejected tensor caches and to both Step 5 refinement branches. -/
theorem arqpida_request_ratios {P : ARqpIDAParameters}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {O : ImplicitAccuracyOracle f P.p} {N : ℕ}
    (r : algorithm_13_1_2 P f O N) {k : ℕ} (hk : k ≤ N) (i : ℕ) :
    (r.state k).request i / (r.state k).request 1 =
      (r.state 0).request i / (r.state 0).request 1 :=
  r.request_ratio hk i

end CartisGouldToint.Chapter13.Section01
