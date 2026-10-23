/-
Upstreaming candidate: a direct converse to the mean value inequality for iterated derivatives.
Natural home: Mathlib.Analysis.Calculus.ContDiff, using the existing derivative-norm identity.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Lipschitz iterated derivatives and bounded next derivatives

On an open convex set, the `p`-th derivative of a `C^(p+1)` map is Lipschitz with constant `L`
exactly when the `(p+1)`-st derivative has operator norm at most `L` everywhere on that set.
The same constant occurs in both directions. The codomain may be any real normed space.
-/

open Set

/-- Lipschitz continuity of an iterated derivative on an open convex set is equivalent
to the same norm bound on the next derivative. -/
theorem lipschitzOnWith_iteratedFDeriv_iff_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} {p : ℕ} {L : NNReal} (hs : IsOpen s) (hc : Convex ℝ s)
    (hf : ContDiffOn ℝ (p + 1) f s) :
    LipschitzOnWith L (iteratedFDeriv ℝ p f) s ↔
      ∀ x ∈ s, ‖iteratedFDeriv ℝ (p + 1) f x‖ ≤ L := by
  constructor
  · intro h x hx
    rw [← norm_fderiv_iteratedFDeriv]
    exact norm_fderiv_le_of_lipschitzOn ℝ (hs.mem_nhds hx) h
  · intro h
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ hc
    · intro x hx
      exact (hf.contDiffAt (hs.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_self p)
    · intro x hx
      change ‖fderiv ℝ (iteratedFDeriv ℝ p f) x‖ ≤ (L : ℝ)
      rw [norm_fderiv_iteratedFDeriv]
      exact h x hx
