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

/-- Genuine failure of objective optimality after an actual model-tested trial
forces the weighted step-power obstruction, with both residual value-error terms. -/
theorem criticality_obstruction {p q : ℕ} (hqp : q ≤ p)
    (f : E → ℝ) (c : E → F) {h : F → ℝ} (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c)
    {Lf Lc σ S θ : ℝ} {K : NNReal} (hLf : 1 ≤ Lf) (hLc : 0 ≤ Lc)
    (hσ : 0 ≤ σ) (hS : σ ≤ S) (hθ : 0 ≤ θ) (hh : LipschitzWith K h)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    (x s : E) (ε δ : Fin q → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1)
    (hδ : ∀ a, 0 < δ a ∧ δ a ≤ 1)
    (htest : ‖s‖ ≤ 1 → ∀ a,
      criticality (smoothModel f p x σ) (residualModel c p x) h (a.val + 1) s (δ a) ≤
        θ * ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial)
    (hnot : ¬∀ a, criticality f c h (a.val + 1) (x + s) (δ a) ≤
      ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial) :
    ∃ a, (1 - θ) * ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial ≤
      (Lf + (K : ℝ) * Lc + S) *
        (∑ i ∈ Finset.range (a.val + 1),
          δ a ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) / (i + 1).factorial) +
      2 * (K : ℝ) * Lc * ‖s‖ ^ (p + 1) / (p + 1).factorial := by
  classical
  push Not at hnot
  obtain ⟨a, ha⟩ := hnot
  have hjp : a.val + 1 ≤ p := (Nat.succ_le_of_lt a.isLt).trans hqp
  have hδa := (hδ a).1.le
  have hεa := (hε a).1.le
  have hsum : 0 ≤ ∑ i ∈ Finset.range (a.val + 1),
      δ a ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) / (i + 1).factorial :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hb : 0 ≤ 2 * (K : ℝ) * Lc * ‖s‖ ^ (p + 1) / (p + 1).factorial := by positivity
  refine ⟨a, ?_⟩
  by_cases hs : ‖s‖ ≤ 1
  · have he := criticality_le_model_add_error (by omega : 0 < p) hjp hf hc
      (zero_le_one.trans hLf) hLc hσ (hδ a).1.le hh hlipf hlipc x s
    have hm := htest hs a
    have hcap := mul_le_mul_of_nonneg_right
      (add_le_add_left hS (Lf + (K : ℝ) * Lc)) hsum
    have hid : (1 - θ) * ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial =
        ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial -
          θ * ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial := by ring
    rw [hid]
    linarith
  · have hs1 : 1 ≤ ‖s‖ := (not_le.mp hs).le
    have hp : 1 ≤ p := by omega
    have hterm : δ a * ‖s‖ ^ p ≤ ∑ i ∈ Finset.range (a.val + 1),
        δ a ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) / (i + 1).factorial := by
      have ht := Finset.single_le_sum
        (s := Finset.range (a.val + 1)) (a := 0)
        (f := fun i => δ a ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) / (i + 1).factorial)
        (fun i _ => by positivity) (Finset.mem_range.mpr (by omega : 0 < a.val + 1))
      simpa only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one,
        Nat.sub_add_cancel hp] using ht
    have hpow : δ a ^ (a.val + 1) ≤ δ a := by
      simpa only [pow_one] using pow_le_pow_of_le_one hδa (hδ a).2
        (show 1 ≤ a.val + 1 by omega)
    have hfac : (1 : ℝ) ≤ (a.val + 1).factorial := by
      exact_mod_cast Nat.factorial_pos _
    have hleft : (1 - θ) * ε a * δ a ^ (a.val + 1) /
        (a.val + 1).factorial ≤ δ a := by
      calc _ ≤ ε a * δ a ^ (a.val + 1) / (a.val + 1).factorial :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_of_le_one_left hεa (by linarith : 1 - θ ≤ 1))
              (pow_nonneg hδa _)) (Nat.cast_nonneg _)
        _ ≤ ε a * δ a ^ (a.val + 1) := div_le_self (by positivity) hfac
        _ ≤ δ a := (mul_le_of_le_one_left (by positivity) (hε a).2).trans hpow
    have hC : 1 ≤ Lf + (K : ℝ) * Lc + S := by
      nlinarith [mul_nonneg K.coe_nonneg hLc]
    have hsp : 1 ≤ ‖s‖ ^ p := one_le_pow₀ hs1
    have hmain := (le_mul_of_one_le_right (hδ a).1.le hsp).trans
      (hterm.trans (le_mul_of_one_le_left hsum hC))
    exact hleft.trans (hmain.trans (le_add_of_nonneg_right hb))
end Composite
