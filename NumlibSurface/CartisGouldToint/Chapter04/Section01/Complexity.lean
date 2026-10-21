import NumlibSurface.CartisGouldToint.Chapter04.Section01
import Numlib.Optimization.HigherOrderRegularizationComplexity

/-!
# ARp iterate-quality and stopping evaluation complexity

Cartis, Gould and Toint, Theorem 4.1.5, gives finite iterate-quality bounds on actual algorithm
prefixes, with the three natural real exponents and the additive two for derivative calls.
For first and second order this also forces the algorithm's first stop. For third order the
quality certificate permits an empty set of directions; the exact stopping test additionally
requires the current model directions to be nonempty outside its strict-curvature branch.
-/

noncomputable section
open Optimization.ParameterUpdates Optimization.HigherOrderRegularization
open CartisGouldToint.Chapter01.Section03
open CartisGouldToint.Chapter02.Section04
namespace CartisGouldToint.Chapter04.Section01

variable {n p : ℕ} {params : regularizationParameters} {theta epsilon : Fin 3 → ℝ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x s : ℕ → EuclideanSpace ℝ (Fin n)}
    {sigma : ℕ → ℝ} {L low : ℝ}

/-- The first-order clause of Theorem 4.1.5: actual legal prefixes force a first stop;
the objective and cached derivative budgets have the natural exponent `(p+1)/p`. -/
theorem theorem_4_1_5_first_order (hf : higherOrderLipschitz f p L)
    (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ N, (∀ k < N, ¬arpStationary 1 epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) →
      arpPrefix params 1 p theta epsilon f x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := firstOrderComplexityConstant params p L S (theta 0) *
      ((f (x 0) - low) / (epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, algorithm_4_1_1 params 1 p theta epsilon f x s sigma K ∧
      (functionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 := by
  have hp : 1 ≤ p := (hprefix 0 (by simp)).degree_ge_order
  exact exists_first_order_run_with_cost (hf.toDiagonalLipschitz hp) hlow hprefix

/-- The second-order clause of Theorem 4.1.5: simultaneous gradient and Hessian termination
has the minimum of the two natural tolerance powers and the source's derivative offset two. -/
theorem theorem_4_1_5_second_order [NeZero n] (hf : higherOrderLipschitz f p L)
    (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ N, (∀ k < N, ¬arpStationary 2 epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) →
      arpPrefix params 2 p theta epsilon f x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := secondOrderComplexityConstant params p L S (theta 0) (theta 1) *
      ((f (x 0) - low) / min ((epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
        ((epsilon 1) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ))))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K, algorithm_4_1_1 params 2 p theta epsilon f x s sigma K ∧
      (functionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 := by
  have hp : 1 ≤ p := by have := (hprefix 0 (by simp)).degree_ge_order; omega
  exact exists_second_order_run_with_cost (hf.toDiagonalLipschitz hp) hlow hprefix

/-- Theorem 4.1.5: within the three-power evaluation budget an actual ARp prefix produces
the stated gradient, curvature and restricted cubic quality certificate. The certified set
is empty at strict positive curvature and otherwise is the current model direction set.
This quality result allows empty directions and does not assert third-order termination. -/
theorem theorem_4_1_5 [NeZero n] (hf : higherOrderLipschitz f p L)
    (hlow : ∀ y, low ≤ f y)
    (hprefix : ∀ N, (∀ k < N, ¬arpStationary 3 epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) →
      arpPrefix params 3 p theta epsilon f x s sigma N) :
    let S := max (sigma 0) (params.gamma3 * (L / (1 - params.eta2)))
    let Q := thirdOrderComplexityConstant params p L S theta *
      ((f (x 0) - low) / min ((epsilon 0) ^ (((p + 1 : ℕ) : ℝ) / p))
        (min ((epsilon 1) ^ (((p + 1 : ℕ) : ℝ) / (p - 1 : ℕ)))
          ((epsilon 2) ^ (((p + 1 : ℕ) : ℝ) / (p - 2 : ℕ)))))
    let C := 1 + |Real.log params.gamma1| / Real.log params.gamma2
    let D := Real.log (S / sigma 0) / Real.log params.gamma2
    ∃ K : ℕ, ∃ M : Set (EuclideanSpace ℝ (Fin n)),
      arpPrefix params 3 p theta epsilon f x s sigma K ∧
      (∀ k < K, ¬arpStationary 3 epsilon f (x k)
        (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) ∧
      M = (if epsilon 1 < leastHessianEigenvalue f (x K) then ∅
        else directionSequence p (theta 1) (epsilon 1) f x s sigma K) ∧
      ‖gradient f (x K)‖ ≤ epsilon 0 ∧ -epsilon 1 ≤ leastHessianEigenvalue f (x K) ∧
      (∀ d ∈ M, |iteratedFDeriv ℝ 3 f (x K) (fun _ => d)| ≤ epsilon 2) ∧
      M ⊆ objectiveFlatDirections f (x K) (epsilon 1) ∧
      (functionEvaluations K : ℝ) ≤ C * Q + C + D + 1 ∧
      (derivativeEvaluations params p f x s K : ℝ) ≤ Q + 2 := by
  have hp : 1 ≤ p := by have := (hprefix 0 (by simp)).degree_ge_order; omega
  have hlegal : ∀ N, (∀ k < N, ¬ThirdOrderQualityTest epsilon f (x k)
      (directionSequence p (theta 1) (epsilon 1) f x s sigma k)) →
      arpPrefix params 3 p theta epsilon f x s sigma N := by
    intro N hfirst
    exact hprefix N (fun k hk hs => hfirst k hk hs.toThirdOrderQualityTest)
  obtain ⟨K, hK, hquality, hfirst, hF, hD⟩ :=
    exists_third_order_quality_with_cost (hf.toDiagonalLipschitz hp) hlow hlegal
  obtain ⟨M, hM, hg, hH, hthird, hsub⟩ := hquality.certificate
    (hK.epsilon_pos 1 (by decide)).le
    (fun d hd => directionSequence_unit p (theta 1) (epsilon 1) f x s sigma K hd)
  refine ⟨K, M, hK, (fun k hk hs => hfirst k hk hs.toThirdOrderQualityTest),
    hM, ?_, hH, hthird, hsub, hF, hD⟩
  rwa [EuclideanSpace.norm_gradient_eq]

end CartisGouldToint.Chapter04.Section01
