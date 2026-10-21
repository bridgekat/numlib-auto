import Numlib.Optimization.NewtonLowerBound
import Numlib.Optimization.CubicRegularization
import NumlibSurface.CartisGouldToint.Chapter01.Section03
import NumlibSurface.CartisGouldToint.Chapter02.Section01

/-!
# Newton's method and Lipschitz Hessians

The normalized assumption f.HL carries continuous second derivatives and a global Lipschitz
bound on the actual bilinear Hessian. A bounded smooth objective with uniformly Lipschitz
gradient and Hessian exhibits the inverse-square derivative-evaluation lower bound for
full-step Newton. Objective values are not queried by this algorithm.
-/
noncomputable section
namespace CartisGouldToint.Chapter03.Section01
open Chapter02.Section01
open scoped NNReal

/-- Assumption f.HL, with `L ≥ 1` as permitted by enlargement of the Lipschitz constant. -/
structure hessianLipschitz {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop extends
    Optimization.CubicRegularization.HessianLipschitz f L where
  one_le : 1 ≤ L

/-- A global tensor-Hessian Lipschitz bound gives the normalized textbook assumption. -/
theorem hessianLipschitz.of_lipschitzWith {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hf : ContDiff ℝ 2 f) (hL : LipschitzWith L (iteratedFDeriv ℝ 2 f)) :
    hessianLipschitz f (max 1 (L : ℝ)) := by
  refine ⟨⟨hf, (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _), ?_⟩,
    le_max_left _ _⟩
  intro u v
  exact (hL.norm_sub_le u v).trans (mul_le_mul_of_nonneg_right
    (le_max_right 1 (L : ℝ)) (norm_nonneg _))

/-- Enlarging the Hessian bound preserves the normalized textbook assumption. -/
theorem hessianLipschitz.mono {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {L M : ℝ} (h : hessianLipschitz f L) (hLM : L ≤ M) : hessianLipschitz f M := by
  refine ⟨⟨h.smooth, h.nonneg.trans hLM, ?_⟩, h.one_le.trans hLM⟩
  intro x y
  exact (h.bound x y).trans (mul_le_mul_of_nonneg_right hLM (norm_nonneg _))

/-- Algorithm 3.1.1: test the gradient, solve the actual Hessian linear system, and accept
the full step. This finite run records the first successful test, without asserting termination
for arbitrary objectives. It makes no objective-value oracle calls. -/
def algorithm_3_1_1 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (N : ℕ) : Prop :=
  Optimization.Newton.IsRun f ε x s N

/-- The derivative-evaluation part of Theorem 3.1.1: full-step Newton may need more than
`⌈ε⁻²⌉` gradient and Hessian evaluations. The separate objective-value oracle is never queried.
The example has positive definite iterate Hessians, strictly decreasing objective values,
and tolerance-independent global smoothness and objective bounds. -/
theorem theorem_3_1_1_derivative_evaluations :
    ∃ Lg LH B : ℝ, 1 ≤ Lg ∧ 1 ≤ LH ∧ 0 ≤ B ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ (f : EuclideanSpace ℝ (Fin 1) → ℝ)
          (x s : ℕ → EuclideanSpace ℝ (Fin 1)) (N : ℕ),
          assumption_f_Bb f ∧ assumption_f_gL f Lg ∧ hessianLipschitz f LH ∧
          (∀ u, |f u| ≤ B) ∧ x 0 = 0 ∧ algorithm_3_1_1 f ε x s N ∧
          (∀ k ≤ N, ∀ u ≠ 0, 0 < fderiv ℝ (fderiv ℝ f) (x k) u u) ∧
          (∀ k < N, f (x k) - f (x (k + 1)) = ε ^ 2) ∧
          Optimization.Newton.gradientEvaluations N = N + 1 ∧
          Optimization.Newton.hessianEvaluations N = N ∧
          Optimization.Newton.functionEvaluations N = 0 ∧
          ⌈(ε ^ 2)⁻¹⌉₊ < Optimization.Newton.gradientEvaluations N ∧
          ⌈(ε ^ 2)⁻¹⌉₊ < Optimization.Newton.hessianEvaluations N := by
  obtain ⟨Lg, LH, B, h⟩ := Optimization.NewtonLowerBound.exists_hard_run
  refine ⟨max 1 (Lg : ℝ), max 1 (LH : ℝ), B, le_max_left _ _, le_max_left _ _,
    B.coe_nonneg, ?_⟩
  intro ε hε hε1
  obtain ⟨f, x, s, N, hf, hg, hH, hb, hx, hr, hpos, hdec, hn⟩ := h ε hε hε1
  refine ⟨f, x, s, N, ?_, ?_, ?_, hb, hx, hr, hpos, hdec, rfl, rfl, rfl, ?_, hn⟩
  · apply assumption_f_Bb_iff.mpr
    exact ⟨-(B : ℝ), fun u => (abs_le.mp (hb u)).1⟩
  · refine ⟨hf.of_le (by norm_num), le_max_left _ _, ?_⟩
    intro u v
    exact (hg.norm_sub_le u v).trans (mul_le_mul_of_nonneg_right
      (le_max_right 1 (Lg : ℝ)) (norm_nonneg _))
  · exact hessianLipschitz.of_lipschitzWith hf hH
  · exact hn.trans (Nat.lt_succ_self N)

end CartisGouldToint.Chapter03.Section01
