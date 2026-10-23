import Numlib.Optimization.HighOrder.ConstrainedCriticality
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Section 14.2: high-order criticality with simple constraints

Constrained criticality uses actual Taylor decrements over feasible displacements in a
closed ball. No convexity or connectivity of the closed feasible set is required.
Theorem 14.2.1 retains the additive criticality allowance and the local Lipschitz
neighborhood. The unindexed radius in (14.2.6) is the optimality radius `δ_j` from its
hypothesis and from (14.2.7).
-/

namespace CartisGouldToint

/-- The high-order constrained Taylor criticality measure (14.2.2), using the exact
feasible-displacement condition (14.2.3). For a closed feasible set at a feasible point
and nonnegative radius, the supremum is an attained nonnegative maximum. -/
noncomputable def highOrderConstrainedCriticality {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (j : ℕ) (X : Set E) (x : E) (δ : ℝ) : ℝ :=
  TaylorModel.constrainedCriticality f j X x δ

/-- **Theorem 14.2.1 (stability of approximate constrained minimizers).**
Small constrained Taylor criticality gives the printed objective stability bounds with
additive allowance `η` on actual feasible displacements, in both Lipschitz-constant cases.
The highest derivative is Lipschitz only on an open ball of radius larger than `δ`.
The feasible set is closed and nonempty, with no convexity assumption. -/
theorem theorem_14_2_1 {n j : ℕ} (hj : 0 < j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : IsClosed X) (_hXne : X.Nonempty) (x : EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ j f) {δ ε η L R : ℝ}
    (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (hε : 0 < ε) (_hε1 : ε ≤ 1) (_hη : 0 ≤ η)
    (hL : 0 ≤ L) (hR : δ < R)
    (hlip : ∀ u ∈ Metric.ball x R, ∀ v ∈ Metric.ball x R,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ L * ‖u - v‖)
    (hcrit : highOrderConstrainedCriticality f j X x δ ≤ ε * δ ^ j / j.factorial + η) :
    (0 < L → ∀ d : EuclideanSpace ℝ (Fin n), x + d ∈ X →
      ‖d‖ ≤ min δ ((j + 1 : ℕ) * ε / L) →
      f x - 2 * ε * δ ^ j / j.factorial - η ≤ f (x + d)) ∧
    (L = 0 → ∀ d : EuclideanSpace ℝ (Fin n), x + d ∈ X → ‖d‖ ≤ δ →
      f x - ε * δ ^ j / j.factorial - η ≤ f (x + d)) := by
  have hball : Metric.closedBall x δ ⊆ Metric.ball x R := fun z hz =>
    (Metric.mem_closedBall.mp hz).trans_lt hR
  have hlip' : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ L * ‖u - v‖ :=
    fun u hu v hv => hlip u (hball hu) v (hball hv)
  constructor
  · intro hLpos d hfeas hd
    have hdδ := (le_min_iff.mp hd).1
    have hb := TaylorModel.value_ge_of_constrainedCriticality hj hX Metric.isOpen_ball
      hf.contDiffOn x hδ.le hball hL hlip' hcrit hfeas hdδ
    have hsmall : L * ‖d‖ ≤ (j + 1 : ℕ) * ε := by
      have hh := (le_div_iff₀ hLpos).mp (le_min_iff.mp hd).2
      nlinarith
    have herr := TaylorModel.lipschitz_error_le_tolerance j (norm_nonneg d) hε.le hdδ hsmall
    calc f x - 2 * ε * δ ^ j / j.factorial - η =
        f x - ε * δ ^ j / j.factorial - η - ε * δ ^ j / j.factorial := by ring
      _ ≤ f x - ε * δ ^ j / j.factorial - η -
          L * ‖d‖ ^ (j + 1) / (j + 1).factorial := by linarith
      _ ≤ f (x + d) := hb
  · intro hLzero d hfeas hd
    have hb := TaylorModel.value_ge_of_constrainedCriticality hj hX Metric.isOpen_ball
      hf.contDiffOn x hδ.le hball hL hlip' hcrit hfeas hd
    simpa only [hLzero, zero_mul, zero_div, sub_zero] using hb

end CartisGouldToint
