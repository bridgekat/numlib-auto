import Numlib.Analysis.Calculus.TaylorModel.Truncation
import Numlib.Optimization.Regularization.HighOrder.Parameter
import Mathlib.Tactic

/-!
# Actual function decrease from a truncated Taylor test

The sharp full Taylor value remainder and the finite higher-order tensor tail
show that a sufficiently small truncated-model decrement retains at least half
its value in the actual function. No function-decrease conclusion is assumed.
-/

namespace TaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a sufficiently small ball, a positive truncated Taylor decrement
implies half that normalized decrement in the actual objective function. -/
theorem value_decrement_ge_half_of_taylor_test {f : E → ℝ} {p j : ℕ}
    (hj : 0 < j) (hjp : j ≤ p) (hf : ContDiff ℝ p f)
    {L B α δ : ℝ} (hL : 0 ≤ L) (hB : 0 < B) (hLB : L ≤ B)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (x d : E) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : ‖d‖ ≤ δ)
    (hsmall : δ ≤ α / (4 * B))
    (hA : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ B)
    (htest : α * δ ^ j / j.factorial ≤ decrement f j x d) :
    α / 2 * δ ^ j / j.factorial ≤ f x - f (x + d) := by
  have htail := norm_ofJet_sub_ofJet_le (ftaylorSeries ℝ f x) hj hjp hB.le hA d (hd.trans hδ1)
  change |eval f p x d - eval f j x d| ≤ B * ‖d‖ ^ (j + 1) / j.factorial at htail
  have htail' : eval f p x d - eval f j x d ≤ B * δ ^ (j + 1) / j.factorial := by
    apply (le_abs_self _).trans
    apply htail.trans
    gcongr
  have herr := HighOrderRegularization.value_error_le (hj.trans_le hjp) hf hL hlip x d
  have hfact : (j.factorial : ℝ) ≤ (p + 1).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : j ≤ p + 1)
  have hpow : ‖d‖ ^ (p + 1) ≤ δ ^ (j + 1) :=
    (pow_le_pow_left₀ (norm_nonneg d) hd _).trans
      (pow_le_pow_of_le_one hδ.le hδ1 (by omega))
  have herr' : f (x + d) - eval f p x d ≤ B * δ ^ (j + 1) / j.factorial := by
    apply ((le_abs_self _).trans herr).trans
    calc _ ≤ L * δ ^ (j + 1) / (p + 1).factorial :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hL) (Nat.cast_nonneg _)
      _ ≤ L * δ ^ (j + 1) / j.factorial :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hfact
      _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLB (pow_nonneg hδ.le _)) (Nat.cast_nonneg _)
  have hsmall' : 4 * B * δ ≤ α := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 4 * B)).mp hsmall
  have herrTotal : B * δ ^ (j + 1) / j.factorial + B * δ ^ (j + 1) / j.factorial ≤
      α / 2 * δ ^ j / j.factorial := by
    calc _ = (2 * B * δ) * δ ^ j / j.factorial := by rw [pow_succ]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : 2 * B * δ ≤ α / 2)
          (pow_nonneg hδ.le _)) (Nat.cast_nonneg _)
  rw [decrement_eq] at htest
  calc α / 2 * δ ^ j / j.factorial =
        α * δ ^ j / j.factorial - α / 2 * δ ^ j / j.factorial := by ring
    _ ≤ (f x - eval f j x d) -
        (B * δ ^ (j + 1) / j.factorial + B * δ ^ (j + 1) / j.factorial) :=
      sub_le_sub htest herrTotal
    _ ≤ _ := by linarith

end TaylorModel
