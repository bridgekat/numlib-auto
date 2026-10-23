import Numlib.Optimization.Constrained.RestrictedCriticality
import Numlib.Optimization.Regularization.Convex.FixedStep
import Numlib.Analysis.InnerProductSpace.NormPow.Integer

/-!
# Sharp actual constrained model derivative errors at every enabled order

The true highest-derivative Lipschitz assumption is needed only on the convex
feasible domain. The actual Taylor tensor remainder and norm-power derivatives
give the same exact factorial coefficient for all enabled derivative orders.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The scalar factorial weight converts the exact falling factorial from the
norm-power tensor bound to the source derivative-error denominator. -/
theorem factorial_penalty_weight {p j : ℕ} (hj : j ≤ p) (σ : ℝ) :
    σ / (p + 1).factorial * ((p + 1).descFactorial j : ℝ) =
      σ / (p - j + 1).factorial := by
  have hfac : ((p - j + 1).factorial : ℝ) * (p + 1).descFactorial j =
      (p + 1).factorial := by
    rw [show p - j + 1 = p + 1 - j by omega]
    exact_mod_cast Nat.factorial_mul_descFactorial (show j ≤ p + 1 by omega)
  rw [div_mul_eq_mul_div]
  apply (div_eq_div_iff (by positivity : ((p + 1).factorial : ℝ) ≠ 0)
    (by positivity : ((p - j + 1).factorial : ℝ) ≠ 0)).mpr
  rw [←hfac]
  ring

/-- Every actual regularized Taylor-model derivative has the exact local
source tensor-error bound, including all first- to third-order enabled modes. -/
theorem norm_model_derivative_error_le_on {p j : ℕ} (hj : j ≤ p)
    {f : E → ℝ} {C S : Set E} (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) (hs : s ≠ 0) :
    ‖iteratedFDeriv ℝ j f (x+s) - iteratedFDeriv ℝ j (model f p x σ) s‖ ≤
      (L+σ) / (p-j+1).factorial * ‖s‖ ^ (p-j+1) := by
  have hT := norm_iteratedFDeriv_sub_eval_le_lipschitz hS hCS hC hf hL hlip hj hx hxs
  have hN := NormPower.norm_iteratedFDeriv_norm_pow_integer_le
    (m := p + 1) (show j ≤ p + 1 by omega) hs
  have hNp : ‖(σ / (p+1).factorial) •
      iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p+1)) s‖ ≤
      σ / (p-j+1).factorial * ‖s‖ ^ (p-j+1) := by
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hN
      (show 0 ≤ σ / (p+1).factorial by positivity)
    rw [←mul_assoc,factorial_penalty_weight hj,
      show p+1-j = p-j+1 by omega] at hm
    exact hm
  rw [iteratedFDeriv_model f p j x σ hs]
  have he : iteratedFDeriv ℝ j f (x+s) -
      (iteratedFDeriv ℝ j (eval f p x) s +
        (σ / (p+1).factorial) • iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p+1)) s) =
      (iteratedFDeriv ℝ j f (x+s) - iteratedFDeriv ℝ j (eval f p x) s) -
        (σ / (p+1).factorial) • iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p+1)) s := by abel
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hT hNp).trans_eq (by ring))

/-- Actual diagonal derivative errors retain the exact tensor coefficient on
unit directions, the domain needed by the criticality measures. -/
theorem abs_model_derivative_error_le_on {p j : ℕ} (hj : j ≤ p)
    {f : E → ℝ} {C S : Set E} (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) {L σ : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {x s d : E} (hx : x ∈ C) (hxs : x + s ∈ C) (hs : s ≠ 0) (hd : ‖d‖ ≤ 1) :
    |iteratedFDeriv ℝ j f (x+s) (fun _ => d) -
      iteratedFDeriv ℝ j (model f p x σ) s (fun _ => d)| ≤
        (L+σ) / (p-j+1).factorial * ‖s‖ ^ (p-j+1) := by
  have hh := (abs_diagonal_le_norm
    (iteratedFDeriv ℝ j f (x+s) - iteratedFDeriv ℝ j (model f p x σ) s) hd).trans
      (norm_model_derivative_error_le_on hj hS hCS hC hf hL hσ hlip hx hxs hs)
  simpa only [sub_apply] using hh

end ConvexRegularization
