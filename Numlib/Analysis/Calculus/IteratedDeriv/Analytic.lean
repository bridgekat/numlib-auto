/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.Analysis.Calculus.IteratedDeriv.Analytic`.
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Power series of the iterated derivatives

`HasFPowerSeriesOnBall.exists_hasFPowerSeriesOnBall_iteratedDeriv`: if `f : 𝕜 → 𝕜` has the power
series `∑ cₙ (z - z₀)ⁿ` on a ball, its `j`-th derivative has a power series on the same ball,
with the differentiated coefficients `(n + j)(n + j - 1) ⋯ (n + 1) c_{n+j}`. It is the iterate of
Mathlib's `HasFPowerSeriesOnBall.fderiv`, with the coefficients made explicit.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- **The iterated derivatives of a function with a power series have power series on the same
ball**, with the differentiated coefficients: the `n`-th coefficient of `f⁽ʲ⁾` is
`(n + j)! / n! · c_{n+j}`. -/
theorem HasFPowerSeriesOnBall.exists_hasFPowerSeriesOnBall_iteratedDeriv {f : 𝕜 → 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 𝕜} {z₀ : 𝕜} {r : ENNReal}
    (hf : HasFPowerSeriesOnBall f p z₀ r) (j : ℕ) :
    ∃ q : FormalMultilinearSeries 𝕜 𝕜 𝕜,
      HasFPowerSeriesOnBall (iteratedDeriv j f) q z₀ r ∧
        ∀ n, q.coeff n = ((n + j).descFactorial j : 𝕜) * p.coeff (n + j) := by
  induction j with
  | zero => exact ⟨p, by simpa using hf, fun n => by simp⟩
  | succ j ih =>
    obtain ⟨q, hq, hcoeff⟩ := ih
    refine ⟨(ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries q.derivSeries,
      ?_, fun n => ?_⟩
    · rw [iteratedDeriv_succ]
      exact (ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).comp_hasFPowerSeriesOnBall hq.fderiv
    · have h1 : ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).compFormalMultilinearSeries
          q.derivSeries).coeff n = q.derivSeries.coeff n 1 := rfl
      rw [h1, FormalMultilinearSeries.derivSeries_coeff_one, hcoeff, nsmul_eq_mul,
        show n + 1 + j = n + (j + 1) by omega, Nat.descFactorial_succ,
        show n + (j + 1) - j = n + 1 by omega]
      push_cast
      ring
