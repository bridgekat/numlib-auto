import Numlib.Analysis.Calculus.TaylorModel.PerturbedDerivative
import Numlib.Analysis.Calculus.TaylorModel.PolynomialDerivative
import Numlib.Optimization.Regularization.ModelSharp
import Numlib.Optimization.HighOrder.JetCriticality

/-!
# Actual derivative and criticality errors of inexact regularized models

Finite-order Taylor remainder, actual polynomial tensor perturbation and the
sharp norm-power penalty bound control the difference from the objective's
true derivatives. Genuine Taylor criticality then inherits the weighted error
sum, without any derivative identity or minimization conclusion as a premise.
-/

namespace InexactRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual model derivative differs from the true objective derivative
by the source trial-length power, with coefficient `L + sigma + 3*K`. -/
theorem norm_derivative_sub_model_le_power (f : E → ℝ) {p j : ℕ}
    (hf : ContDiff ℝ p f) (hj : 1 ≤ j) (hjp : j ≤ p)
    {L K σ : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) (hσ : 0 ≤ σ)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (A : FormalMultilinearSeries ℝ E ℝ) (x s : E)
    (herr : ∀ i, 1 ≤ i → i ≤ p →
      ‖A i - iteratedFDeriv ℝ i f x‖ ≤ K * ‖s‖ ^ (p - i + 1)) :
    ‖iteratedFDeriv ℝ j f (x + s) -
      iteratedFDeriv ℝ j (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) s‖ ≤
        (L + σ + 3 * K) * ‖s‖ ^ (p - j + 1) := by
  have hrem := TaylorModel.norm_iteratedFDeriv_sub_eval_le_lipschitz
    (C := Set.univ) (D := Set.univ) isOpen_univ (by simp) convex_univ hf.contDiffOn
    hL (fun u _ v _ => hlip u v) hjp (Set.mem_univ x) (Set.mem_univ (x + s))
  have hpoly := TaylorModel.norm_iteratedFDeriv_ofJet_sub_le_power A
    (ftaylorSeries ℝ f x) hj hjp hK s herr
  have hpen := ModelDecrease.norm_iteratedFDeriv_penalty_le hjp hσ s
  have hfac : (1 : ℝ) ≤ (p - j + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hrem' := hrem.trans (div_le_self (by positivity) hfac)
  have hpen' := hpen.trans (div_le_self (by positivity) (by
    simpa only [Nat.sub_add_comm hjp] using hfac))
  rw [ModelDecrease.iteratedFDeriv_penalized_ofJet_eq A p j hjp σ s]
  have he : iteratedFDeriv ℝ j f (x + s) -
      (iteratedFDeriv ℝ j (TaylorModel.ofJet A p) s +
        (σ / ((p + 1).factorial : ℝ)) •
          iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) s) =
      (iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (TaylorModel.eval f p x) s) +
      (iteratedFDeriv ℝ j (TaylorModel.eval f p x) s -
        iteratedFDeriv ℝ j (TaylorModel.ofJet A p) s) -
      (σ / ((p + 1).factorial : ℝ)) •
        iteratedFDeriv ℝ j (fun z : E => ‖z‖ ^ (p + 1)) s := by abel
  rw [he]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
  have hpoly' : ‖iteratedFDeriv ℝ j (TaylorModel.eval f p x) s -
      iteratedFDeriv ℝ j (TaylorModel.ofJet A p) s‖ ≤ 3 * K * ‖s‖ ^ (p - j + 1) := by
    change ‖iteratedFDeriv ℝ j (TaylorModel.ofJet (ftaylorSeries ℝ f x) p) s -
      iteratedFDeriv ℝ j (TaylorModel.ofJet A p) s‖ ≤ _
    rw [norm_sub_rev]
    exact hpoly
  have hexp : p + 1 - j = p - j + 1 := by omega
  rw [hexp] at hpen'
  nlinarith

/-- True Taylor criticality at the trial point is bounded by actual computed
model criticality plus the weighted all-order derivative-error sum. -/
theorem criticality_le_model_add_error (f : E → ℝ) {p j : ℕ}
    (hf : ContDiff ℝ p f) (hjp : j ≤ p)
    {L K σ δ : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    (hlip : ∀ u v, ‖iteratedFDeriv ℝ p f u - iteratedFDeriv ℝ p f v‖ ≤ L * ‖u - v‖)
    (A : FormalMultilinearSeries ℝ E ℝ) (x s : E)
    (herr : ∀ i, 1 ≤ i → i ≤ p →
      ‖A i - iteratedFDeriv ℝ i f x‖ ≤ K * ‖s‖ ^ (p - i + 1)) :
    TaylorModel.criticality f j (x + s) δ ≤
      TaylorModel.criticality (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) j s δ +
        (L + σ + 3 * K) *
          ∑ i ∈ Finset.range j, δ ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) /
            (i + 1).factorial := by
  have hh := TaylorModel.abs_jetCriticality_sub_le (ftaylorSeries ℝ f (x + s))
    (ftaylorSeries ℝ (ModelDecrease.penalized (TaylorModel.ofJet A p) p σ) s) j hδ
    (fun i => (L + σ + 3 * K) * ‖s‖ ^ (p - i + 1))
    (fun i hi hij => norm_derivative_sub_model_le_power f hf hi (hij.trans hjp)
      hL hK hσ hlip A x s herr)
  simp only [TaylorModel.jetCriticality_ftaylorSeries] at hh
  have he : (∑ i ∈ Finset.range j,
      (L + σ + 3 * K) * ‖s‖ ^ (p - (i + 1) + 1) * δ ^ (i + 1) /
        (i + 1).factorial) = (L + σ + 3 * K) *
      ∑ i ∈ Finset.range j, δ ^ (i + 1) * ‖s‖ ^ (p - (i + 1) + 1) /
        (i + 1).factorial := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hh
  have hu := (abs_le.mp hh).2
  linarith

end InexactRegularization
