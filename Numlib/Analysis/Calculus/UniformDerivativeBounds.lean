import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Derivative norm bounds and closed-interval jet comparison

These interfaces pull scalar derivative estimates through contractions, compare actual
jets on closed intervals, and convert a second derivative bound to a gradient Lipschitz
bound using the Riesz isometry.
-/

noncomputable section
open Set
open scoped NNReal

/-- Pulling back a scalar function along a contraction does not increase its derivative
norms. This includes the coordinate maps of a Euclidean space. -/
theorem norm_iteratedFDeriv_scalar_pullback {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] ℝ)
    (hL : ‖L‖ ≤ 1) {j : ℕ} (hj : j ≤ 2) (x : E) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ |iteratedDeriv j f (L x)| := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hj)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

/-- A uniform operator bound on the second derivative makes the actual gradient
Lipschitz, via the derivative map and the Riesz isometry. -/
theorem lipschitzWith_gradient_of_iteratedFDeriv_two_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {K : ℝ≥0}
    (hb : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ K) : LipschitzWith K (gradient f) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hLip : LipschitzWith K (fderiv ℝ f) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hfd.differentiable (by norm_num))
    intro x
    apply (show ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ (K : ℝ) from ?_)
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hb x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, gradient, gradient, ← map_sub, LinearIsometryEquiv.norm_map]
  simpa only [dist_eq_norm] using hLip.dist_le_mul x y

/-- Agreement of twice smooth real functions on a nondegenerate closed interval gives
agreement of their actual derivatives through order two, including at both endpoints. -/
theorem iteratedDeriv_eq_of_eqOn_unitInterval {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (heq : EqOn f g (Icc (0 : ℝ) 1))
    {j : ℕ} (hj : j ≤ 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    iteratedDeriv j f t = iteratedDeriv j g t := by
  rw [← iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one
    (hf.of_le (by exact_mod_cast hj)).contDiffAt ht,
    ← iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one
      (hg.of_le (by exact_mod_cast hj)).contDiffAt ht]
  exact congrArg (fun L => L (fun _ => (1 : ℝ))) (iteratedFDerivWithin_congr (𝕜 := ℝ) heq ht j)
