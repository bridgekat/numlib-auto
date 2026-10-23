import Numlib.Optimization.HighOrder.JetCriticality
import Numlib.Optimization.TrustRegion.Inexact.Selection

/-!
# Certified optimality from computed Taylor measures

The terminal computed tests are verified against the finite known error budget.
The total budget at the largest tested order controls every smaller-order budget,
so every reported accuracy holds for the true derivative jet.
-/

open scoped BigOperators
namespace InexactTrustRegion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- The known finite error budget for Taylor decrements on a closed radius ball. -/
noncomputable def tensorErrorBudget (e : ℕ → ℝ) (q : ℕ) (δ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range q, e (i + 1) * δ ^ (i + 1) / (i + 1).factorial

/-- A passing all-order computed optimality loop together with the explicit
finite error-budget test used to certify termination. -/
structure TerminationCheck {q : ℕ} (A : FormalMultilinearSeries ℝ E ℝ)
    (δ ζ : ℝ) (ε : Fin q → ℝ) (d : Fin q → E) (e : ℕ → ℝ) : Prop where
  order_pos : 0 < q
  radius_nonneg : 0 ≤ δ
  radius_le_one : δ ≤ 1
  zeta_pos : 0 < ζ
  zeta_le_one : ζ ≤ 1
  accuracy_pos : ∀ a, 0 < ε a
  approximation : ∀ a, ζ * TaylorModel.jetCriticality A (modelOrder a) δ ≤
    TaylorModel.jetDecrement A (modelOrder a) (d a)
  computed_passes : ∀ a, TaylorModel.jetDecrement A (modelOrder a) (d a) ≤
    ζ / 2 * ε a * δ ^ modelOrder a / (modelOrder a).factorial
  verified : tensorErrorBudget e q δ ≤ ζ / 2 * minimumAccuracy order_pos ε * δ ^ q / q.factorial

/-- The explicitly verified error budget turns every passing computed test into
true Taylor criticality at the requested accuracy. -/
theorem TerminationCheck.true_optimality {q : ℕ} {A : FormalMultilinearSeries ℝ E ℝ}
    {δ ζ : ℝ} {ε : Fin q → ℝ} {d : Fin q → E} {e : ℕ → ℝ}
    (h : TerminationCheck A δ ζ ε d e) (f : E → ℝ) (x : E)
    (horacle : ∀ a, 1 ≤ a → a ≤ q →
      ‖A a - iteratedFDeriv ℝ a f x‖ ≤ e a) (a : Fin q) :
    TaylorModel.criticality f (modelOrder a) x δ ≤
      ε a * δ ^ modelOrder a / (modelOrder a).factorial := by
  have hja : modelOrder a ≤ q := a.isLt
  have hepos : ∀ b, 1 ≤ b → b ≤ q → 0 ≤ e b := by
    intro b hb hbq
    exact (norm_nonneg _).trans (horacle b hb hbq)
  have hpartial : tensorErrorBudget e (modelOrder a) δ ≤ tensorErrorBudget e q δ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hja)
    intro i hi _
    have hiq : i + 1 ≤ q := Finset.mem_range.mp hi
    exact div_nonneg (mul_nonneg (hepos _ (by omega) hiq)
      (pow_nonneg h.radius_nonneg _)) (Nat.cast_nonneg _)
  have hεmin := minimumAccuracy_pos h.order_pos h.accuracy_pos
  have hp : δ ^ q ≤ δ ^ modelOrder a :=
    pow_le_pow_of_le_one h.radius_nonneg h.radius_le_one hja
  have hfac : ((modelOrder a).factorial : ℝ) ≤ q.factorial := by
    exact_mod_cast Nat.factorial_le hja
  have hscaled : ζ / 2 * minimumAccuracy h.order_pos ε * δ ^ q / q.factorial ≤
      ε a / 2 * δ ^ modelOrder a / (modelOrder a).factorial := by
    have hnum : ζ / 2 * minimumAccuracy h.order_pos ε ≤ ε a / 2 := by
      have h1 := mul_le_mul_of_nonneg_right h.zeta_le_one hεmin.le
      have h2 := minimumAccuracy_le h.order_pos ε a
      nlinarith
    calc _ ≤ (ε a / 2) * δ ^ modelOrder a / q.factorial :=
          div_le_div_of_nonneg_right
            (mul_le_mul hnum hp (pow_nonneg h.radius_nonneg _)
              (div_nonneg (h.accuracy_pos a).le (by norm_num))) (Nat.cast_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left
        (mul_nonneg (div_nonneg (h.accuracy_pos a).le (by norm_num))
          (pow_nonneg h.radius_nonneg _)) (by positivity) hfac
  exact TaylorModel.criticality_le_of_verified_jet f A (modelOrder a) x (d a)
    h.radius_nonneg h.zeta_pos e
    (fun b hb hbj => horacle b hb (hbj.trans hja)) (h.approximation a) (h.computed_passes a)
    (hpartial.trans (h.verified.trans hscaled))

end InexactTrustRegion
