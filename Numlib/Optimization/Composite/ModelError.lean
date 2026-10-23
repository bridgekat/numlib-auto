import Numlib.Optimization.Composite.Perturbation
import Numlib.Optimization.Composite.ModelTaylor
import Numlib.Optimization.Regularization.Inexact.CriticalityError

/-!
# Actual composite criticality error after a regularized Taylor step

The sharp all-order Taylor remainder and the actual integer penalty derivative
bound control the smooth scalar and residual derivative errors. Comparing the
two retained outer-function increments contributes twice the residual value
error. The estimate makes no assumption about a model's minimizer or stationarity.
-/

namespace Composite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in
/-- The genuine residual polynomial's actual derivatives approximate those of
its underlying map with the sharp Taylor powers. -/
theorem norm_derivative_sub_residualModel_le {c : E → F} {p j : ℕ}
    (hc : ContDiff ℝ p c) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ L * ‖u - v‖)
    (hjp : j ≤ p) (x s : E) :
    ‖iteratedFDeriv ℝ j c (x + s) -
      iteratedFDeriv ℝ j (residualModel c p x) s‖ ≤ L * ‖s‖ ^ (p - j + 1) := by
  have he := TaylorModel.norm_iteratedFDeriv_sub_eval_le_lipschitz
    (C := Set.univ) (D := Set.univ) isOpen_univ (by simp) convex_univ hc.contDiffOn hL
    (fun u _ v _ => hlip u v) hjp (Set.mem_univ x) (Set.mem_univ (x + s))
  exact he.trans (div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos _))

/-- Actual objective generalized criticality at the trial point is bounded by
actual model criticality, derivative remainder powers, and both retained outer
residual value errors. -/
theorem criticality_le_model_add_error {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p j : ℕ} (hp : 0 < p) (hjp : j ≤ p) (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c)
    {Lf Lc σ δ : ℝ} {K : NNReal} (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hσ : 0 ≤ σ) (hδ : 0 ≤ δ) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    (x s : E) :
    criticality f c h j (x + s) δ ≤
      criticality (smoothModel f p x σ) (residualModel c p x) h j s δ +
        (Lf + (K : ℝ) * Lc + σ) *
          (∑ i ∈ Finset.range j, δ ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) /
            (i + 1).factorial) +
        2 * (K : ℝ) * Lc * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
  have he := criticality_le_add_tensor_errors f (smoothModel f p x σ) c
    (residualModel c p x) hh j (x + s) s hδ
  have hsum : (∑ i ∈ Finset.range j,
      (‖iteratedFDeriv ℝ (i + 1) f (x + s) -
          iteratedFDeriv ℝ (i + 1) (smoothModel f p x σ) s‖ +
        (K : ℝ) * ‖iteratedFDeriv ℝ (i + 1) c (x + s) -
          iteratedFDeriv ℝ (i + 1) (residualModel c p x) s‖) * δ ^ (i + 1) /
          (i + 1).factorial) ≤
      (Lf + (K : ℝ) * Lc + σ) *
        ∑ i ∈ Finset.range j, δ ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) /
          (i + 1).factorial := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hij : i + 1 ≤ p := (Nat.succ_le_of_lt (Finset.mem_range.mp hi)).trans hjp
    have hfe := InexactRegularization.norm_derivative_sub_model_le_power f hf
      (by omega : 1 ≤ i + 1) hij hLf (K := 0) le_rfl hσ hlipf
      (ftaylorSeries ℝ f x) x s (fun a _ _ => by simp [ftaylorSeries])
    simp only [mul_zero, add_zero] at hfe
    change ‖iteratedFDeriv ℝ (i + 1) f (x + s) -
      iteratedFDeriv ℝ (i + 1) (smoothModel f p x σ) s‖ ≤ _ at hfe
    have hce := norm_derivative_sub_residualModel_le hc hLc hlipc hij x s
    have hab := add_le_add hfe (mul_le_mul_of_nonneg_left hce K.coe_nonneg)
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hab (pow_nonneg hδ (i + 1)))
      (Nat.cast_nonneg (i + 1).factorial)
    convert hm using 1
    ring
  have hbase : ‖c (x + s) - residualModel c p x s‖ ≤
      Lc * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
    cases p with
    | zero => omega
    | succ p =>
      exact TaylorModel.norm_sub_eval_le_lipschitz isOpen_univ (Set.Subset.refl Set.univ)
        convex_univ hc.contDiffOn hLc (fun u _ v _ => hlipc u v)
        (Set.mem_univ x) (Set.mem_univ (x + s))
  have hb := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 2 * (K : ℝ) by positivity)
  have hb' : 2 * (K : ℝ) * ‖c (x + s) - residualModel c p x s‖ ≤
      2 * (K : ℝ) * Lc * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
    convert hb using 1
    ring
  linarith only [he, hsum, hb']
end Composite
