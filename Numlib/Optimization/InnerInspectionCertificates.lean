import Numlib.Optimization.HigherOrderApproximateRegularizationInner

/-!
# Certificates accumulated during an inner inspection epoch

Inspection histories are independent of how their test is computed. Passing stores a
certificate, and halving changes only the currently inspected radius. The same interface
therefore serves ordinary and generalized composite Taylor tests.
-/

namespace Optimization.HigherOrderApproximateRegularization.InnerCertificates

variable {E : Type*}

/-- All previously inspected orders have certificates at the current point and radii. -/
def PassedOrders (C : ℕ → E → ℝ → Prop) (a : InnerState E) (j : ℕ) : Prop :=
  ∀ i, 1 ≤ i → i < j → C i a.step (a.radii i)

/-- Inspection certificates are accumulated until all orders pass or a long step returns. -/
def EpochInvariant (q : ℕ) (C : ℕ → E → ℝ → Prop) (long : InnerState E → Prop)
    (a : InnerState E) : Prop :=
  match a.phase with
  | .minimize => True
  | .inspect j => PassedOrders C a j
  | .returned => long a ∨ PassedOrders C a (q + 1)

/-- Passing the current order extends the certificate prefix and returns at the final order. -/
theorem pass {q : ℕ} {C : ℕ → E → ℝ → Prop} {long : InnerState E → Prop}
    {a : InnerState E} {j : ℕ} (ha : PassedOrders C a j) (hc : C j a.step (a.radii j)) :
    EpochInvariant q C long
      ⟨a.mu, a.radii, a.step, if j = q then .returned else .inspect (j + 1)⟩ := by
  have hp : PassedOrders C a (j + 1) := by
    intro i hi hij
    by_cases hij' : i < j
    · exact ha i hi hij'
    · have he : i = j := by omega
      subst i
      exact hc
  by_cases hj : j = q
  · simp only [hj, ite_true, EpochInvariant]
    exact Or.inr (by simpa only [PassedOrders, hj] using hp)
  · simp only [ite_eq_right hj, EpochInvariant]
    exact hp

/-- Halving only the current radius preserves every earlier certificate. -/
theorem halve {C : ℕ → E → ℝ → Prop} {a : InnerState E} {j : ℕ}
    (ha : PassedOrders C a j) :
    PassedOrders C ⟨a.mu, Function.update a.radii j (a.radii j / 2), a.step, .inspect j⟩ j := by
  intro i hi hij
  simpa only [Function.update_of_ne (ne_of_lt hij)] using ha i hi hij

end Optimization.HigherOrderApproximateRegularization.InnerCertificates
