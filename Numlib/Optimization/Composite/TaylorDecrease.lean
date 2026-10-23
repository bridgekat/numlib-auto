import Numlib.Optimization.Composite.Optimality
import Numlib.Optimization.HighOrder.TaylorDecrease
import Numlib.Analysis.Calculus.TaylorModel.Holder
import Mathlib.Tactic

/-!
# Decrease retained by generalized composite Taylor models

The outer Lipschitz function is retained exactly. Sharp Taylor remainders for the
smooth scalar and residual maps, together with a finite polynomial truncation,
give a decrease bound for sufficiently small normalized Taylor trials.
-/

namespace Composite
open TaylorModel Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual generalized Taylor decrement retains the entire outer function. -/
noncomputable def decrement (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (j : ℕ) (x d : E) : ℝ := taylorModel f c h j x 0 - taylorModel f c h j x d

/-- The generalized Taylor decrement compares the actual objective with its model. -/
theorem decrement_eq (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (j : ℕ) (x d : E) : decrement f c h j x d = f x + h (c x) - taylorModel f c h j x d := by
  rw [decrement, taylorModel_zero]

/-- A zero displacement has zero generalized Taylor decrement. -/
@[simp] theorem decrement_zero (f : E → ℝ) (c : E → F) (h : F → ℝ)
    (j : ℕ) (x : E) : decrement f c h j x 0 = 0 := sub_self _

/-- Sharp full-degree composite Taylor error for normed residual spaces. -/
theorem abs_sub_taylorModel_le_lipschitz {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p : ℕ} (hp : 0 < p) (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c)
    {Lf Lc : ℝ} {K : NNReal} (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    (hh : LipschitzWith K h) (x d : E) :
    |f (x + d) + h (c (x + d)) - taylorModel f c h p x d| ≤
      (Lf + (K : ℝ) * Lc) * ‖d‖ ^ (p + 1) / (p + 1).factorial := by
  have hferr := HighOrderRegularization.value_error_le hp hf hLf hlipf x d
  have hcerr : ‖c (x + d) - eval c p x d‖ ≤ Lc * ‖d‖ ^ (p + 1) / (p + 1).factorial := by
    cases p with
    | zero => omega
    | succ p =>
      exact norm_sub_eval_le_lipschitz isOpen_univ (Subset.refl univ) convex_univ hc.contDiffOn
        hLc (fun u _ v _ => hlipc u v) (mem_univ x) (mem_univ (x + d))
  have ho := hh.dist_le_mul (c (x + d)) (eval c p x d)
  rw [Real.dist_eq, dist_eq_norm] at ho
  have hs := (abs_add_le (f (x + d) - eval f p x d)
    (h (c (x + d)) - h (eval c p x d))).trans
      (add_le_add hferr (ho.trans (mul_le_mul_of_nonneg_left hcerr K.coe_nonneg)))
  convert hs using 1
  · congr 1
    unfold taylorModel
    ring
  · ring

/-- Higher actual derivative bounds control the generalized composite Taylor truncation
error; Lipschitz continuity of the outer function suffices. -/
theorem abs_taylorModel_sub_taylorModel_le (f : E → ℝ) (c : E → F) {h : F → ℝ}
    {p j : ℕ} (hj : 0 < j) (hjp : j ≤ p) {Bf Bc : ℝ} {K : NNReal}
    (hBf : 0 ≤ Bf) (hBc : 0 ≤ Bc) (hh : LipschitzWith K h)
    (x d : E) (hd : ‖d‖ ≤ 1)
    (hAf : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ Bf)
    (hAc : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a c x‖ ≤ Bc) :
    |taylorModel f c h p x d - taylorModel f c h j x d| ≤
      (Bf + (K : ℝ) * Bc) * ‖d‖ ^ (j + 1) / j.factorial := by
  have hft := norm_ofJet_sub_ofJet_le (ftaylorSeries ℝ f x) hj hjp hBf hAf d hd
  have hct := norm_ofJet_sub_ofJet_le (ftaylorSeries ℝ c x) hj hjp hBc hAc d hd
  have ho := hh.dist_le_mul (eval c p x d) (eval c j x d)
  rw [Real.dist_eq, dist_eq_norm] at ho
  have hs := (abs_add_le (eval f p x d - eval f j x d)
    (h (eval c p x d) - h (eval c j x d))).trans
      (add_le_add hft (ho.trans (mul_le_mul_of_nonneg_left hct K.coe_nonneg)))
  convert hs using 1
  · congr 1
    unfold taylorModel
    ring
  · ring

/-- A sufficiently small generalized Taylor test retains half its predicted normalized
value in the actual composite objective, without differentiating the outer function. -/
theorem value_decrement_ge_half_of_taylor_test {f : E → ℝ} {c : E → F} {h : F → ℝ}
    {p j : ℕ} (hj : 0 < j) (hjp : j ≤ p) (hf : ContDiff ℝ p f) (hc : ContDiff ℝ p c)
    {Lf Lc Bf Bc α δ : ℝ} {K : NNReal} (hLf : 0 ≤ Lf) (hLc : 0 ≤ Lc)
    (hBf : 0 ≤ Bf) (hBc : 0 ≤ Bc) (hB : 0 < Bf + (K : ℝ) * Bc)
    (hLB : Lf + (K : ℝ) * Lc ≤ Bf + (K : ℝ) * Bc)
    (hlipf : ∀ u v,
      ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ Lf * ‖u - v‖)
    (hlipc : ∀ u v,
      ‖iteratedFDeriv ℝ p c u - iteratedFDeriv ℝ p c v‖ ≤ Lc * ‖u - v‖)
    (hh : LipschitzWith K h) (x d : E) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : ‖d‖ ≤ δ)
    (hsmall : δ ≤ α / (4 * (Bf + (K : ℝ) * Bc)))
    (hAf : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a f x‖ ≤ Bf)
    (hAc : ∀ a, j < a → a ≤ p → ‖iteratedFDeriv ℝ a c x‖ ≤ Bc)
    (htest : α * δ ^ j / j.factorial ≤ decrement f c h j x d) :
    α / 2 * δ ^ j / j.factorial ≤ f x + h (c x) - (f (x + d) + h (c (x + d))) := by
  let B := Bf + (K : ℝ) * Bc
  have htail := abs_taylorModel_sub_taylorModel_le f c hj hjp hBf hBc hh x d
    (hd.trans hδ1) hAf hAc
  have htail' : taylorModel f c h p x d - taylorModel f c h j x d ≤
      B * δ ^ (j + 1) / j.factorial := by
    apply ((le_abs_self _).trans htail).trans
    gcongr
  have herr := abs_sub_taylorModel_le_lipschitz (hj.trans_le hjp) hf hc hLf hLc
    hlipf hlipc hh x d
  have hfact : (j.factorial : ℝ) ≤ (p + 1).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : j ≤ p + 1)
  have hpow : ‖d‖ ^ (p + 1) ≤ δ ^ (j + 1) :=
    (pow_le_pow_left₀ (norm_nonneg d) hd _).trans
      (pow_le_pow_of_le_one hδ.le hδ1 (by omega))
  have herr' : f (x + d) + h (c (x + d)) - taylorModel f c h p x d ≤
      B * δ ^ (j + 1) / j.factorial := by
    apply ((le_abs_self _).trans herr).trans
    calc _ ≤ (Lf + (K : ℝ) * Lc) * δ ^ (j + 1) / (p + 1).factorial := by
            gcongr
      _ ≤ (Lf + (K : ℝ) * Lc) * δ ^ (j + 1) / j.factorial :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hfact
      _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hLB (pow_nonneg hδ.le _)) (Nat.cast_nonneg _)
  have hsmall' : 4 * B * δ ≤ α := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 4 * B)).mp hsmall
  have heTotal : B * δ ^ (j + 1) / j.factorial + B * δ ^ (j + 1) / j.factorial ≤
      α / 2 * δ ^ j / j.factorial := by
    calc _ = (2 * B * δ) * δ ^ j / j.factorial := by rw [pow_succ]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : 2 * B * δ ≤ α / 2)
            (pow_nonneg hδ.le _)) (Nat.cast_nonneg _)
  rw [decrement_eq] at htest
  calc α / 2 * δ ^ j / j.factorial =
      α * δ ^ j / j.factorial - α / 2 * δ ^ j / j.factorial := by ring
    _ ≤ (f x + h (c x) - taylorModel f c h j x d) -
        (B * δ ^ (j + 1) / j.factorial + B * δ ^ (j + 1) / j.factorial) :=
      sub_le_sub htest heTotal
    _ ≤ _ := by linarith
end Composite
