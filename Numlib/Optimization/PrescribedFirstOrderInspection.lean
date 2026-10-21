import Numlib.Optimization.FirstOrderRegularizationInspection

/-!
# Failed first-order inspections with prescribed directions

Strict computed failures at every positive dyadic radius force the completed inspection
to select order one. The public search-direction identity determines the actual direction
passed to model minimization, without unfolding the search construction.
-/

noncomputable section
namespace Optimization.InexactRegularization
open InexactTaylorModels

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Prescribed fractional witnesses which fail every computed test yield a completed
order-one inspection and preserve its entire dyadic direction sequence. -/
theorem exists_failed_firstOrderInspection (P : Parameters) (hq : P.q = 1)
    (c : ℝ) (A : Coefficients E) (σ : ℝ) (δ : ℕ → ℝ)
    (hδ : δ 1 ∈ Set.Ioc (0 : ℝ) 1) (d : ℕ → E)
    (hd : ∀ k, CoefficientWitness A 1 (halvedRadius (δ 1) k) P.fraction (d k))
    (hf : ∀ k, P.fraction * P.epsilon 1 * halvedRadius (δ 1) k / 2 <
      decrement A 1 (d k)) :
    ∃ I : Inspection P c A σ δ, I.order = 1 ∧
      (I.search 1 le_rfl (by omega) I.order_pos).direction = d := by
  obtain ⟨I, hi⟩ := exists_firstOrderInspection_with_directions P hq c A σ δ hδ d hd
  refine ⟨I, ?_, hi⟩
  have ho := I.order_pos
  have hb := I.order_le
  by_contra hn
  have hh : 1 < I.order := by omega
  have he := I.earlier 1 le_rfl (by omega) hh
  rw [hi] at he
  norm_num only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at he
  exact (not_lt_of_ge he) (hf (I.halvings 1))

/-- The selected direction of an order-one inspection is obtained by evaluating its
public whole-sequence identity at the actual terminal halving index. -/
theorem Inspection.direction_eq_of_order_one {P : Parameters} {c : ℝ}
    {A : Coefficients E} {σ : ℝ} {δ : ℕ → ℝ} (I : Inspection P c A σ δ)
    (ho : I.order = 1) (hq : I.order ≤ P.q) (d : ℕ → E)
    (hd : (I.search 1 le_rfl (by omega) I.order_pos).direction = d) :
    I.direction hq = d (I.halvings 1) := by
  rcases I with ⟨order, hpos, hle, halvings, search, earlier, failed, retained⟩
  dsimp only at ho
  subst order
  exact congrFun hd (halvings 1)

end Optimization.InexactRegularization
