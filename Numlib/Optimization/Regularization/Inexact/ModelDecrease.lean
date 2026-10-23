import Numlib.Analysis.Calculus.TaylorModel.Truncation
import Numlib.Analysis.Calculus.ContDiff.Lipschitz
import Numlib.Optimization.HighOrder.ModelDecrease

/-!
# Small-radius decrease for inexact regularized models

Restoring higher Taylor terms and the norm-power penalty preserves half of a
positive truncated computed decrement on a sufficiently small ball.
-/

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- A sufficiently small ball preserves half of the truncated computed decrease
when the remaining tensor terms and the norm-power penalty are restored. -/
theorem penalized_decrement_ge_half (A : FormalMultilinearSeries ℝ E ℝ)
    {j p : ℕ} (hj : 0 < j) (hjp : j ≤ p) {B σ α δ : ℝ}
    (hB : 0 < B) (hσ : 0 ≤ σ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsmall : δ ≤ α / (4 * max B σ))
    (hA : ∀ a, j < a → a ≤ p → ‖A a‖ ≤ B) (d : E) (hd : ‖d‖ ≤ δ)
    (htest : α * δ ^ j / j.factorial ≤ jetDecrement A j d) :
    α / 2 * δ ^ j / j.factorial ≤
      ModelDecrease.penalized (ofJet A p) p σ 0 -
        ModelDecrease.penalized (ofJet A p) p σ d := by
  have hm : 0 < max B σ := hB.trans_le (le_max_left _ _)
  have hsnorm : ‖d‖ ≤ 1 := hd.trans hδ1
  have htail := norm_ofJet_sub_ofJet_le A hj hjp hB.le hA d hsnorm
  have htail' : ofJet A p d - ofJet A j d ≤ B * δ ^ (j + 1) / j.factorial := by
    apply (le_abs_self _).trans
    apply htail.trans
    gcongr
  have hfac : (0 : ℝ) < j.factorial := by positivity
  have hfact : (j.factorial : ℝ) ≤ (p + 1).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : j ≤ p + 1)
  have hpow : ‖d‖ ^ (p + 1) ≤ δ ^ (j + 1) :=
    (pow_le_pow_left₀ (norm_nonneg d) hd _).trans
      (pow_le_pow_of_le_one hδ.le hδ1 (by omega))
  have hpen : σ / ((p + 1).factorial : ℝ) * ‖d‖ ^ (p + 1) ≤
      σ * δ ^ (j + 1) / j.factorial := by
    calc _ = σ * ‖d‖ ^ (p + 1) / (p + 1).factorial := by ring
      _ ≤ σ * δ ^ (j + 1) / (p + 1).factorial :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hσ)
          (Nat.cast_nonneg _)
      _ ≤ σ * δ ^ (j + 1) / j.factorial :=
        div_le_div_of_nonneg_left (by positivity) hfac hfact
  have hsmall' : 4 * max B σ * δ ≤ α := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 4 * max B σ)).mp hsmall
  have hsum : (B + σ) * δ ≤ α / 2 := by
    have hh : B + σ ≤ 2 * max B σ := by
      linarith [le_max_left B σ, le_max_right B σ]
    have hmul := mul_le_mul_of_nonneg_right hh hδ.le
    linarith
  have herr : B * δ ^ (j + 1) / j.factorial + σ * δ ^ (j + 1) / j.factorial ≤
      α / 2 * δ ^ j / j.factorial := by
    calc _ = ((B + σ) * δ) * δ ^ j / j.factorial := by rw [pow_succ]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsum (pow_nonneg hδ.le _)) hfac.le
  simp only [jetDecrement, ofJet_zero] at htest
  simp only [ModelDecrease.penalized, ofJet_zero, norm_zero, zero_pow (by omega : p + 1 ≠ 0),
    mul_zero, add_zero]
  calc α / 2 * δ ^ j / j.factorial =
        α * δ ^ j / j.factorial - α / 2 * δ ^ j / j.factorial := by ring
    _ ≤ (A 0 (fun _ => 0) - ofJet A j d) -
        (B * δ ^ (j + 1) / j.factorial + σ * δ ^ (j + 1) / j.factorial) :=
      sub_le_sub htest herr
    _ ≤ _ := by linarith
end TaylorModel

namespace TaylorModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Lipschitz lower derivatives and primitive oracle error bounds give uniform
bounds on all positive-order tensors of an approximate jet. -/
theorem norm_jet_le_of_lipschitz_oracle {f : E → F} {p : ℕ} {L κmax κh : ℝ}
    (hL : 0 ≤ L) (hκh : 0 ≤ κh)
    (hlip : ∀ a, a < p → ∀ u v,
      ‖iteratedFDeriv ℝ a f u - iteratedFDeriv ℝ a f v‖ ≤ L * ‖u - v‖)
    (A : FormalMultilinearSeries ℝ E F) (x : E) (κ accuracy : ℕ → ℝ)
    (hκ : ∀ a, 1 ≤ a → a ≤ p → 0 ≤ κ a ∧ κ a ≤ κmax)
    (haccuracy : ∀ a, 1 ≤ a → a ≤ p → accuracy a ≤ κh)
    (horacle : ∀ a, 1 ≤ a → a ≤ p →
      ‖A a - iteratedFDeriv ℝ a f x‖ ≤ κ a * accuracy a)
    {a : ℕ} (ha : 1 ≤ a) (hap : a ≤ p) : ‖A a‖ ≤ L + κmax * κh := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  have htrue : ‖iteratedFDeriv ℝ (b + 1) f x‖ ≤ L := by
    rw [← norm_fderiv_iteratedFDeriv]
    exact norm_fderiv_le_of_lip' ℝ hL
      (Filter.Eventually.of_forall (fun u => hlip b (by omega) u x))
  have herr : ‖A (b + 1) - iteratedFDeriv ℝ (b + 1) f x‖ ≤ κmax * κh :=
    (horacle _ ha hap).trans
      ((mul_le_mul_of_nonneg_left (haccuracy _ ha hap) (hκ _ ha hap).1).trans
        (mul_le_mul_of_nonneg_right (hκ _ ha hap).2 hκh))
  calc ‖A (b + 1)‖ =
        ‖(A (b + 1) - iteratedFDeriv ℝ (b + 1) f x) + iteratedFDeriv ℝ (b + 1) f x‖ := by
          congr 1
          abel
    _ ≤ ‖A (b + 1) - iteratedFDeriv ℝ (b + 1) f x‖ +
        ‖iteratedFDeriv ℝ (b + 1) f x‖ := norm_add_le _ _
    _ ≤ _ := by linarith

end TaylorModel
