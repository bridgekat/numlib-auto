import Numlib.Optimization.Regularization.Convex.DerivativeError

/-!
# Restricted derivative step bounds from actual model tests

The model test and the endpoint obstruction refer to the same actual direction
set. Their genuine tensor-error estimate gives the strict source step bound.
Small objective diagonals also bound model diagonals on unit directions.
-/

namespace ConvexRegularization
open Set TaylorModel HighOrderRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every enabled actual derivative test gives the strict factorial step bound
when its true restricted endpoint measure fails the requested threshold. -/
theorem derivative_step_lower_of_model_test {p j : ℕ} (hj : j ≤ p)
    {f : E → ℝ} {C S A : Set E} (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) {L σ σmax θ ε : ℝ} (hL : 0 ≤ L) (hσ : 0 < σ)
    (hσmax : σ ≤ σmax)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {x s : E} (hx : x ∈ C) (hxs : x + s ∈ C) (hs : s ≠ 0) (hA : (0 : E) ∈ A)
    (hmodel : tensorCriticality (iteratedFDeriv ℝ j (model f p x σ) s) A ≤ θ * ε)
    (hfail : ε < tensorCriticality (iteratedFDeriv ℝ j f (x + s)) A) :
    (p-j+1).factorial * (1-θ) / (L+σmax) * ε < ‖s‖ ^ (p-j+1) := by
  have he := tensorCriticality_le_of_error (iteratedFDeriv ℝ j f (x+s))
    (iteratedFDeriv ℝ j (model f p x σ) s) hA
    (norm_model_derivative_error_le_on hj hS hCS hC hf hL hσ.le hlip hx hxs hs)
  have hfac : (0 : ℝ) < (p-j+1).factorial := by positivity
  have hden : 0 < L+σmax := add_pos_of_nonneg_of_pos hL (hσ.trans_le hσmax)
  have hpow : 0 ≤ ‖s‖ ^ (p-j+1) := pow_nonneg (norm_nonneg _) _
  have hcoeff : (L+σ) / (p-j+1).factorial * ‖s‖ ^ (p-j+1) ≤
      (L+σmax) / (p-j+1).factorial * ‖s‖ ^ (p-j+1) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hfac.le) hpow
  have hh : (1-θ)*ε < (L+σmax) / (p-j+1).factorial * ‖s‖ ^ (p-j+1) := by linarith
  have hm := (lt_div_iff₀ hfac).mp (by
    simpa only [div_mul_eq_mul_div] using hh)
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hden).mpr
  nlinarith

/-- Small genuine objective derivatives bound the actual model derivative on
unit directions; no unrestricted direction-independent estimate is claimed. -/
theorem abs_model_diagonal_le_of_objective_bound {p j : ℕ} (hj : j ≤ p)
    {f : E → ℝ} {C S : Set E} (hS : IsOpen S) (hCS : C ⊆ S) (hC : Convex ℝ C)
    (hf : ContDiffOn ℝ p f S) {L σ σmax b : ℝ} (hL : 0 ≤ L) (hσ : 0 ≤ σ)
    (hσmax : σ ≤ σmax)
    (hlip : ∀ y ∈ C, ∀ z ∈ C,
      ‖iteratedFDeriv ℝ p f y - iteratedFDeriv ℝ p f z‖ ≤ L * ‖y - z‖)
    {x s d : E} (hx : x ∈ C) (hxs : x + s ∈ C) (hs : s ≠ 0) (hd : ‖d‖ ≤ 1)
    (hsmall : |iteratedFDeriv ℝ j f (x + s) (fun _ => d)| ≤ b) :
    |iteratedFDeriv ℝ j (model f p x σ) s (fun _ => d)| ≤
      (L+σmax) / (p-j+1).factorial * ‖s‖ ^ (p-j+1) + b := by
  have he := abs_model_derivative_error_le_on hj hS hCS hC hf hL hσ hlip hx hxs hs hd
  have hb : (L+σ) / (p-j+1).factorial * ‖s‖ ^ (p-j+1) ≤
      (L+σmax) / (p-j+1).factorial * ‖s‖ ^ (p-j+1) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) (by positivity))
      (pow_nonneg (norm_nonneg _) _)
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp he).1,(abs_le.mp he).2,
    (abs_le.mp hsmall).1,(abs_le.mp hsmall).2]

end ConvexRegularization
