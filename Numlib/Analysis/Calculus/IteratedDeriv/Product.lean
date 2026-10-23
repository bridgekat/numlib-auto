import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Iterated derivative bounds for linear maps and scalar-coordinate lifts

Linear maps have no nonzero derivatives above order one. Composing a univariate
map with a Cartesian coordinate projection cannot enlarge its derivative norms.
-/

open scoped ContDiff

/-- Positive-order derivatives of a continuous linear map have norm at most its
operator norm; all orders above one are identically zero. -/
theorem ContinuousLinearMap.norm_iteratedFDeriv_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {j : ℕ} (hj : 1 ≤ j) (x : E) :
    ‖iteratedFDeriv ℝ j L x‖ ≤ ‖L‖ := by
  cases j with
  | zero => omega
  | succ j =>
    cases j with
    | zero =>
      change ‖iteratedFDeriv ℝ 1 (fun y => L y) x‖ ≤ ‖L‖
      rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
    | succ j =>
      change ‖iteratedFDeriv ℝ ((j+1)+1) (fun y => L y) x‖ ≤ ‖L‖
      rw [← norm_iteratedFDeriv_fderiv]
      rw [show fderiv ℝ (fun y => L y) = (fun _ : E => L) from
        funext fun _ => L.fderiv]
      rw [iteratedFDeriv_succ_const]
      simpa only [Pi.zero_apply, norm_zero] using norm_nonneg L

/-- A scalar-coordinate lift has derivative norm at most the corresponding
univariate derivative norm, for every order with the stated actual smoothness. -/
theorem norm_iteratedFDeriv_comp_fst_le {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : WithTop ℕ∞} {f : ℝ → F} (hf : ContDiff ℝ n f)
    {j : ℕ} (hj : j ≤ n) (x : ℝ × G) :
    ‖iteratedFDeriv ℝ j (fun w : ℝ × G => f w.1) x‖ ≤ ‖iteratedDeriv j f x.1‖ := by
  have he : (fun w : ℝ × G => f w.1) = f ∘ ContinuousLinearMap.fst ℝ ℝ G := rfl
  rw [he, (ContinuousLinearMap.fst ℝ ℝ G).iteratedFDeriv_comp_right hf x hj]
  change ‖(iteratedFDeriv ℝ j f x.1).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.fst ℝ ℝ G)‖ ≤ ‖iteratedDeriv j f x.1‖
  have hb := (iteratedFDeriv ℝ j f x.1).norm_compContinuousLinearMap_le
    (fun _ => ContinuousLinearMap.fst ℝ ℝ G)
  simpa only [ContinuousLinearMap.norm_fst, Finset.prod_const_one, mul_one,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hb

/-- Composition with a linear contraction cannot enlarge any actual derivative
norm at an order covered by the map's finite smoothness. -/
theorem norm_iteratedFDeriv_comp_linearMap_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {n : WithTop ℕ∞} {f : E → F}
    (hf : ContDiff ℝ n f) (L : G →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    {j : ℕ} (hj : j ≤ n) (x : G) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x hj]
  have hb := (iteratedFDeriv ℝ j f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  have hp : ∏ _ : Fin j, ‖L‖ ≤ 1 :=
    by
      simpa only [Fin.prod_const] using (pow_le_one₀ (n := j) (norm_nonneg L) hL)
  exact hb.trans ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _))
