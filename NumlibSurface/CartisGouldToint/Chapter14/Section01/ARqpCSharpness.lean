import NumlibSurface.CartisGouldToint.Chapter14.Section01.ARqpC
import NumlibSurface.CartisGouldToint.Chapter12.Section02.ARqpSharpness
import Numlib.Optimization.CompositeRegularizationEmbedding

/-!
# Chapter 14, Section 1: actual composite sharpness executions

The earlier smooth construction is embedded with a fixed nonzero norm composition and
constant zero inner map. Both have their original composite regularity. Actual outer
transitions preserve their first true stopping point and exact independent oracle costs.
-/

noncomputable section
open scoped Nat NNReal ContDiff
namespace CartisGouldToint.Chapter14.Section01
open Optimization CompositeTaylorModels CompositeRegularization TaylorCriticality
open HigherOrderApproximateRegularizationSharpness HigherOrderSharpness Metric Set

/-- Corollary 14.1.11: one-dimensional actual composite executions attain the first-order
sharp exponent with a nonzero convex nonsmooth composition. Uniform smoothness and lower
bound constants are chosen before the accuracy; all oracle costs belong to actual executions.
The scalar domain and codomain are the one-dimensional instance of the source spaces. -/
theorem corollary_14_1_11 (p : ℕ) (hp : 1 ≤ p) :
    ∃ (L : ℝ) (B : ℝ≥0), 1 ≤ L ∧
      ∀ ε : ℝ, (hε : 0 < ε) → (hεsmall : ε ≤ 1 / 2) →
      let P := parameters p 1 le_rfl hp ε (sigma p 1) hε (by linarith) (sigma_pos p 1)
      ∃ (f : ℝ → ℝ) (c : ℝ → ℝ) (h : LipschitzSubadditiveComposition ℝ)
        (N : ℕ) (step : ℝ) (run : OuterExecution P f c h 0 (sigma p 1) (fun _ => 1) N),
        HigherOrderDerivativeFamily f p (fun _ => L) ∧
        ContDiff ℝ (⊤ : ℕ∞ω) c ∧
        (∀ j, 1 ≤ j → LipschitzWith 0 (iteratedFDeriv ℝ j c)) ∧
        (∃ z, h z ≠ 0) ∧ ConvexOn ℝ univ h ∧
        (∀ x, -(B : ℝ) ≤ objective f c h x) ∧
        0 < step ∧ step ≤ 1 ∧ N = ⌈1 / ε ^ (((p + 1 : ℕ) : ℝ) / p)⌉₊ ∧
        run.state = state (sigma p 1) 1 step ∧
        run.last = .stopTest (run.state N) ∧
        (∀ k < N, ε < gapOn (decrement f c h 1 ((k : ℝ) * step)) (closedBall 0 1)) ∧
        gapOn (decrement f c h 1 ((N : ℝ) * step)) (closedBall 0 1) = 0 ∧
        run.functionCount = N + 1 ∧ run.derivativeCount = N * p + 1 ∧
        run.derivativeBatchCount = N + 1 ∧
        ⌊1 / ε ^ (((p + 1 : ℕ) : ℝ) / p)⌋₊ ≤ N ∧
        ⌊1 / ε ^ (((p + 1 : ℕ) : ℝ) / p)⌋₊ ≤ run.functionCount ∧
        ⌊1 / ε ^ (((p + 1 : ℕ) : ℝ) / p)⌋₊ ≤ run.derivativeCount ∧
        ⌊1 / ε ^ (((p + 1 : ℕ) : ℝ) / p)⌋₊ ≤ run.derivativeBatchCount := by
  obtain ⟨L, B, hL, hc⟩ :=
    CartisGouldToint.Chapter12.Section02.corollary_12_2_16 p 1 le_rfl (by norm_num) hp
  refine ⟨L, B, hL, ?_⟩
  intro ε hε hεsmall
  dsimp only
  obtain ⟨f, N, step, smoothRun, hf, hb, hlow, hf0, hstep, hstep1, hN, hgap, hend,
    hstate, hstop, hnot, hfun, hder, hfloor, hfloorfun, hfloorder⟩ := hc ε hε hεsmall
  let P := parameters p 1 le_rfl hp ε (sigma p 1) hε (by linarith) (sigma_pos p 1)
  let h : LipschitzSubadditiveComposition ℝ := normComposition ℝ
  have hfail : ∀ k, k < N → (smoothRun.state k).test = true →
      Nonempty (FailedTest P f (fun _ : ℝ => (0 : ℝ)) h
        (smoothRun.state k).point (smoothRun.state k).radii) := by
    intro k hk _
    apply failedTest_of_true_gap h.lipschitz (smoothRun.valid k hk.le).2.1
    refine ⟨1, le_rfl, le_rfl, ?_⟩
    rw [hstate]
    simpa [P, parameters, state] using hgap k hk
  let run := OuterExecution.ofSmooth h smoothRun hstop hfail
  have hexp : sharpExponent p 1 = ((p + 1 : ℕ) : ℝ) / p := by
    simp [sharpExponent, Nat.sub_add_cancel hp]
  refine ⟨f, (fun _ => 0), h, N, step, run, hf, contDiff_const, ?_, ?_,
    normComposition_convex, ?_, hstep, hstep1, ?_, hstate, rfl, ?_, ?_, hfun, hder,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [iteratedFDeriv_const_of_ne (by omega)]
    exact LipschitzWith.const 0
  · exact ⟨1, by norm_num [h]⟩
  · intro x
    simpa using hlow x
  · simpa only [hexp] using hN
  · intro k hk
    simpa using hgap k hk
  · simpa using hend 1 le_rfl le_rfl
  · apply run.derivativeBatchCount_eq_of_cache_zero
      (fun k hk => by change (smoothRun.state k).cachedOrder = 0; rw [hstate]; rfl) rfl
  · simpa only [hexp] using hfloor
  · change _ ≤ smoothRun.functionCount
    simpa only [hexp] using hfloorfun
  · change _ ≤ smoothRun.derivativeCount
    simpa only [hexp] using hfloorder
  · rw [run.derivativeBatchCount_eq_of_cache_zero
      (fun k hk => by change (smoothRun.state k).cachedOrder = 0; rw [hstate]; rfl) rfl]
    have hfl : ⌊1 / ε ^ (((p + 1 : ℕ) : ℝ) / p)⌋₊ ≤ N := by
      simpa only [hexp] using hfloor
    omega

end CartisGouldToint.Chapter14.Section01
