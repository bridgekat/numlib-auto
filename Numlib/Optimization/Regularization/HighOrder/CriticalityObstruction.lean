import Numlib.Optimization.Regularization.Inexact.CriticalityError
import Numlib.Optimization.Regularization.HighOrder.Parameter
import Numlib.Optimization.TrustRegion.Inexact.Selection

/-!
# Actual criticality obstruction for exact high-order regularization

The accepted trial point is the actual sum of center and step. Exact tensor
jets remove all oracle perturbation terms. A failed true optimality test then
forces the weighted step-power inequality, including the large-step branch
where no model criticality test is required.
-/

namespace HighOrderRegularization
open InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Failure of true optimality after an actual model-tested regularization
step yields the weighted obstruction with the exact coefficient `L+S`.
The conditional model test is precisely the short-step operational rule;
large steps require no model criticality assumption. -/
theorem criticality_obstruction {p q : ℕ} (hqp : q ≤ p) (f : E → ℝ)
    (hf : ContDiff ℝ p f) {L σ S θ : ℝ} (hL : 1 ≤ L)
    (hσ : 0 ≤ σ) (hS : σ ≤ S) (hθ : 0 ≤ θ)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (x s : E) (ε δ : Fin q → ℝ) (hε : ∀ a, 0 < ε a ∧ ε a ≤ 1)
    (hδ : ∀ a, 0 < δ a ∧ δ a ≤ 1)
    (htest : ‖s‖ ≤ 1 → ∀ a,
      TaylorModel.criticality (model f p x σ) (modelOrder a) s (δ a) ≤
        θ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial)
    (hnot : ¬∀ a, TaylorModel.criticality f (modelOrder a) (x + s) (δ a) ≤
      ε a * δ a ^ modelOrder a / (modelOrder a).factorial) :
    ∃ a, (1 - θ) * ε a * δ a ^ modelOrder a / (modelOrder a).factorial ≤
      (L + S) * ∑ i ∈ Finset.range (modelOrder a),
        δ a ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) / (i + 1).factorial := by
  classical
  push Not at hnot
  obtain ⟨a, ha⟩ := hnot
  have hδa : 0 ≤ δ a := (hδ a).1.le
  have hεa : 0 ≤ ε a := (hε a).1.le
  have hj : 0 < modelOrder a := by unfold modelOrder; omega
  have hjp : modelOrder a ≤ p := by unfold modelOrder; omega
  have hsum : 0 ≤ ∑ i ∈ Finset.range (modelOrder a),
      δ a ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) / (i + 1).factorial :=
    Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨a, ?_⟩
  by_cases hs : ‖s‖ ≤ 1
  · have he := InexactRegularization.criticality_le_model_add_error f hf hjp
      (zero_le_one.trans hL) (K := 0) le_rfl hσ (hδ a).1.le hlip
      (ftaylorSeries ℝ f x) x s (fun i _ _ => by
        change ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f x‖ ≤ _
        simp)
    change TaylorModel.criticality f (modelOrder a) (x + s) (δ a) ≤
      TaylorModel.criticality (model f p x σ) (modelOrder a) s (δ a) + _ at he
    simp only [mul_zero, add_zero] at he
    have hm := htest hs a
    have hcap := mul_le_mul_of_nonneg_right (add_le_add_left hS L) hsum
    have hid : (1 - θ) * ε a * δ a ^ modelOrder a / (modelOrder a).factorial =
        ε a * δ a ^ modelOrder a / (modelOrder a).factorial -
          θ * ε a * δ a ^ modelOrder a / (modelOrder a).factorial := by ring
    rw [hid]
    linarith
  · have hs1 : 1 ≤ ‖s‖ := (not_le.mp hs).le
    have hp : 1 ≤ p := hj.trans_le hjp
    have hterm : δ a * ‖s‖ ^ p ≤ ∑ i ∈ Finset.range (modelOrder a),
        δ a ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) / (i + 1).factorial := by
      have hh := Finset.single_le_sum
        (s := Finset.range (modelOrder a)) (a := 0)
        (f := fun i => δ a ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) / (i + 1).factorial)
        (fun i _ => by positivity) (Finset.mem_range.mpr hj)
      simpa only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, div_one,
        Nat.sub_add_cancel hp] using hh
    have hpow : δ a ^ modelOrder a ≤ δ a :=
      (by simpa only [pow_one] using
        pow_le_pow_of_le_one hδa (hδ a).2 (show 1 ≤ modelOrder a from hj))
    have hfac : (1 : ℝ) ≤ (modelOrder a).factorial := by
      exact_mod_cast Nat.factorial_pos _
    have hleft : (1 - θ) * ε a * δ a ^ modelOrder a /
        (modelOrder a).factorial ≤ δ a := by
      calc _ ≤ ε a * δ a ^ modelOrder a / (modelOrder a).factorial := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_of_le_one_left hεa (by linarith : 1 - θ ≤ 1))
                (pow_nonneg hδa _)) (Nat.cast_nonneg _)
        _ ≤ ε a * δ a ^ modelOrder a := div_le_self (by positivity) hfac
        _ ≤ δ a := (mul_le_of_le_one_left (by positivity) (hε a).2).trans hpow
    have hC : 1 ≤ L + S := by linarith
    have hsp : 1 ≤ ‖s‖ ^ p := one_le_pow₀ hs1
    apply hleft.trans
    calc δ a ≤ δ a * ‖s‖ ^ p := le_mul_of_one_le_right (hδ a).1.le hsp
      _ ≤ _ := hterm.trans (le_mul_of_one_le_left hsum hC)

end HighOrderRegularization
