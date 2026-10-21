import NumlibSurface.CartisGouldToint.Chapter04.Section01.Complexity
import Numlib.Optimization.HigherOrderSharpness

/-!
# Sharp first- to third-order ARp evaluation complexity

The witnesses are univariate real objectives, as in the source construction after
Corollary 12.2.16. The scalar real line is a one-dimensional Euclidean domain; this theorem
uses the canonical actual ARp execution interface on that domain. Its third-order quality
condition tests all objective-defined nearly-flat directions, including the full set Zε
printed in Theorem 4.1.6. Uniform bounds precede the tolerances, and choosing the hardest
activated branch gives the maximum of the three printed powers.
-/

noncomputable section
open scoped NNReal
open Optimization Optimization.HigherOrderRegularization Optimization.HigherOrderSharpness
namespace CartisGouldToint.Chapter04.Section01

/-- Theorem 4.1.6: for every `p ≥ r`, `1 ≤ r ≤ 3`, the maximum of the activated sharp
powers is attained on uniformly bounded, uniformly highest-derivative-Lipschitz univariate
objectives. The actual ARp run first stops at `N`, computes `N+1` function values and cached
derivative batches, and first satisfies the full objective quality test at `N`.

The positive tolerance range depends only on `p` and the tested derivative order. The
uniform constants precede all tolerances. The witnesses obey the actual factorial-normalized
model, all activated residuals, accepted iterate and parameter updates, and a nonempty tested
model direction set. They do not use the empty-direction nontermination obstruction. -/
theorem theorem_4_1_6 (p r : ℕ) (hr : 1 ≤ r) (hr3 : r ≤ 3) (hrp : r ≤ p) :
    ∃ L B : ℝ≥0, 1 ≤ L ∧
      ∀ epsilon : Fin 3 → ℝ, (∀ i, 0 < epsilon i) →
        (∀ i : Fin r, epsilon ⟨i.val, by omega⟩ ≤ toleranceScale p (i.val + 1)) →
        ∃ (f : ℝ → ℝ) (N : ℕ) (h : ℝ),
          0 < h ∧ h ≤ 1 ∧ ContDiff ℝ p f ∧
          LipschitzWith L (iteratedFDeriv ℝ p f) ∧ DiagonalLipschitz f p L ∧
          (∀ x, -(B : ℝ) ≤ f x) ∧ f 0 = 0 ∧
          IsRun CubicRegularization.sharpParameters r p (fun _ => 1) epsilon f
            (fun k => (k : ℝ) * h) (fun _ => h) (fun _ => 1) N ∧
          (∀ k < N, ¬ObjectiveQuality r epsilon f ((k : ℝ) * h)) ∧
          ObjectiveQuality r epsilon f ((N : ℝ) * h) ∧
          functionEvaluations N = N + 1 ∧
          derivativeEvaluations CubicRegularization.sharpParameters p f
            (fun k => (k : ℝ) * h) (fun _ => h) N = N + 1 ∧
          evaluationLowerBound p r epsilon ≤ (N : ℝ) := by
  obtain ⟨L, B, hfamily⟩ := exists_max_hard_family p r hr hr3 hrp
  refine ⟨max L 1, B, le_max_right _ _, ?_⟩
  intro epsilon heps hsmall
  obtain ⟨f, N, h, hh, hh1, hf, hLip, hb, hf0, hrun, hnot, hterminal, hfe, hde, hN⟩ :=
    hfamily epsilon heps hsmall
  have hL : LipschitzWith (max L 1) (iteratedFDeriv ℝ p f) := hLip.weaken (le_max_left _ _)
  refine ⟨f, N, h, hh, hh1, hf, hL, ?_, ?_, hf0, hrun, hnot, hterminal, hfe, hde, hN⟩
  · apply DiagonalLipschitz.of_operator hf (by positivity)
    intro x y
    simpa only [dist_eq_norm] using hL.dist_le_mul x y
  · intro x
    exact (abs_le.mp (hb x)).1

end CartisGouldToint.Chapter04.Section01
