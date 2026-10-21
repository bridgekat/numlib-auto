import Numlib.Optimization.ExactRegularizationInnerReturns

/-!
# Exact-coefficient returns for prescribed short steps

Analytic inequalities for the genuine Taylor model transfer to the supplied-coefficient
model with any independent scalar constant. The detailed first-order inner execution and
its retained comparison are then constructed by the existing operational interface.
-/

noncomputable section
namespace Optimization.InexactRegularization
open InexactTaylorModels
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Genuine model inequalities construct a prescribed short exact-coefficient inner return.
The independent scalar constant cancels from every value comparison and derivative. -/
def exactShortFirstOrderInnerResult (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z s : E) (μ : ℝ)
    (hmin : ∀ t, HigherOrderRegularization.model f P.p x σ z ≤
      HigherOrderRegularization.model f P.p x σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hs : ‖s‖ < 1)
    (hfrac : μ * (HigherOrderRegularization.model f P.p x σ 0 -
      HigherOrderRegularization.model f P.p x σ z) ≤
      HigherOrderRegularization.model f P.p x σ 0 -
        HigherOrderRegularization.model f P.p x σ s)
    (hgrad : ‖fderiv ℝ (HigherOrderRegularization.model f P.p x σ) s‖ ≤
      P.theta * P.epsilon 1)
    (hretained : HigherOrderRegularization.model f P.p x σ s ≤
      HigherOrderRegularization.model f P.p x σ d) :
    InnerResult P c (fun i => iteratedFDeriv ℝ i f x) σ δ d := by
  let m := regularizedPolynomial c (fun i => iteratedFDeriv ℝ i f x) P.p σ
  have hm (t : E) : m t = HigherOrderRegularization.model f P.p x σ t + c - f x :=
    regularizedPolynomial_iteratedFDeriv f x c P.p σ t
  have hmfun : m = fun t => HigherOrderRegularization.model f P.p x σ t + c - f x := funext hm
  apply shortFirstOrderInnerResult P hq c _ σ δ d z s μ
    ((regularizedPolynomial_iteratedFDeriv_minimizer_iff f x c P.p σ z).mpr hmin)
    hμ hμ1 hs
  · change μ * (m 0 - m z) ≤ m 0 - m s
    rw [hm 0, hm z, hm s]
    convert hfrac using 1 <;> ring
  · change ‖fderiv ℝ m s‖ ≤ _
    rw [hmfun, fderiv_sub_const, fderiv_add_const]
    exact hgrad
  · change m s ≤ m d
    rw [hm s, hm d]
    linarith

/-- The exact-coefficient return selects the prescribed actual short step. -/
@[simp] theorem exactShortFirstOrderInnerResult_step (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z s : E) (μ : ℝ)
    (hmin : ∀ t, HigherOrderRegularization.model f P.p x σ z ≤
      HigherOrderRegularization.model f P.p x σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hs : ‖s‖ < 1)
    (hfrac : μ * (HigherOrderRegularization.model f P.p x σ 0 -
      HigherOrderRegularization.model f P.p x σ z) ≤
      HigherOrderRegularization.model f P.p x σ 0 -
        HigherOrderRegularization.model f P.p x σ s)
    (hgrad : ‖fderiv ℝ (HigherOrderRegularization.model f P.p x σ) s‖ ≤
      P.theta * P.epsilon 1)
    (hretained : HigherOrderRegularization.model f P.p x σ s ≤
      HigherOrderRegularization.model f P.p x σ d) :
    (exactShortFirstOrderInnerResult P hq f x c σ δ d z s μ
      hmin hμ hμ1 hs hfrac hgrad hretained).step = s := rfl

/-- The exact-coefficient return has the actual unit short-step radii. -/
@[simp] theorem exactShortFirstOrderInnerResult_radii (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d z s : E) (μ : ℝ)
    (hmin : ∀ t, HigherOrderRegularization.model f P.p x σ z ≤
      HigherOrderRegularization.model f P.p x σ t)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hs : ‖s‖ < 1)
    (hfrac : μ * (HigherOrderRegularization.model f P.p x σ 0 -
      HigherOrderRegularization.model f P.p x σ z) ≤
      HigherOrderRegularization.model f P.p x σ 0 -
        HigherOrderRegularization.model f P.p x σ s)
    (hgrad : ‖fderiv ℝ (HigherOrderRegularization.model f P.p x σ) s‖ ≤
      P.theta * P.epsilon 1)
    (hretained : HigherOrderRegularization.model f P.p x σ s ≤
      HigherOrderRegularization.model f P.p x σ d) :
    (exactShortFirstOrderInnerResult P hq f x c σ δ d z s μ
      hmin hμ hμ1 hs hfrac hgrad hretained).radii = (fun _ => 1) := by
  exact ite_eq_right (not_le_of_gt hs)

/-- The prescribed exact-coefficient return has the actual two-transition state sequence,
unit returned radii, and the specified initialization fraction. -/
theorem exists_exactShortFirstOrderInnerResult (P : Parameters) (hq : P.q = 1)
    (f : E → ℝ) (x : E) (c σ : ℝ) (δ : ℕ → ℝ) (d s : E) (μ : ℝ)
    (hσ : 0 < σ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hs : ‖s‖ < 1)
    (hfrac : ∀ z, (∀ t, HigherOrderRegularization.model f P.p x σ z ≤
      HigherOrderRegularization.model f P.p x σ t) →
      μ * (HigherOrderRegularization.model f P.p x σ 0 -
      HigherOrderRegularization.model f P.p x σ z) ≤
      HigherOrderRegularization.model f P.p x σ 0 -
        HigherOrderRegularization.model f P.p x σ s)
    (hgrad : ‖fderiv ℝ (HigherOrderRegularization.model f P.p x σ) s‖ ≤
      P.theta * P.epsilon 1)
    (hretained : HigherOrderRegularization.model f P.p x σ s ≤
      HigherOrderRegularization.model f P.p x σ d) :
    ∃ R : InnerResult P c (fun i => iteratedFDeriv ℝ i f x) σ δ d,
      R.step = s ∧ R.length = 2 ∧ R.radii = (fun _ => 1) ∧
      R.execution.state 0 = ⟨μ, fun _ => 1, 0, .minimize⟩ := by
  obtain ⟨z, hz⟩ := HigherOrderApproximateRegularization.exists_model_minimizer f P.p x hσ
  let R := exactShortFirstOrderInnerResult P hq f x c σ δ d z s μ hz
    hμ hμ1 hs (hfrac z hz) hgrad hretained
  refine ⟨R, rfl, rfl, ?_, rfl⟩
  exact ite_eq_right (not_le_of_gt hs)

end Optimization.InexactRegularization
