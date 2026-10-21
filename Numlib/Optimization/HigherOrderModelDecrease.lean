import Numlib.Optimization.HigherOrderRegularization
import Numlib.Optimization.InexactTaylorModels

/-!
# Actual decrease from a lower-order Taylor decrement

A Lipschitz highest derivative controls the actual Taylor remainder. Together with local
bounds on the omitted derivative coefficients, a sufficiently small displacement transfers
a positive truncated Taylor decrement to half as much actual function decrease.
-/

noncomputable section
open scoped Nat
namespace Optimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local derivative bound and a small radius transfer a lower-order Taylor decrement
to actual decrease, with the exact factorial scaling. -/
theorem HigherOrderRegularization.DiagonalLipschitz.half_decrease_of_small_radius
    {f : E → ℝ} {p j : ℕ} {σ M δ α : ℝ} (hf : DiagonalLipschitz f p σ)
    (hp : 1 ≤ p) (hjp : j ≤ p) (hM : 0 ≤ M) (hσ : σ ≤ M)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (x d : E) (hd : ‖d‖ ≤ δ)
    (hb : ∀ i ∈ Finset.Icc (j + 1) p, ‖iteratedFDeriv ℝ i f x‖ ≤ M)
    (hsmall : 4 * M * δ ≤ α)
    (hdec : α * δ ^ j / (j ! : ℝ) ≤ TaylorCriticality.taylorDecrement f j x d) :
    α * δ ^ j / (2 * (j ! : ℝ)) ≤ f x - f (x + d) := by
  have he := InexactTaylorModels.half_decrease_of_small_radius (f x)
    (fun i => iteratedFDeriv ℝ i f x) hjp (σ := σ) hM hδ d hd hb
    (by simpa only [max_eq_left hσ] using hsmall)
    (by simpa only [InexactTaylorModels.decrement_iteratedFDeriv] using hdec)
  have hr := (abs_le.mp (hf.value_remainder hp x d)).2
  have hmajor : f (x + d) ≤ InexactTaylorModels.regularizedPolynomial (f x)
      (fun i => iteratedFDeriv ℝ i f x) p σ d := by
    rw [InexactTaylorModels.regularizedPolynomial,
      InexactTaylorModels.polynomial_iteratedFDeriv]
    calc
      _ ≤ σ / ((p + 1)! : ℝ) * ‖d‖ ^ (p + 1) +
          RegularizedTaylorModel.taylorModel f p x d := sub_le_iff_le_add.mp hr
      _ = _ := by ring
  exact he.trans (sub_le_sub_left hmajor (f x))

end Optimization
