import Numlib.Optimization.HighOrder.Criticality
import Numlib.Optimization.HighOrder.CriticalityLocalMin
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Section 12.1: high-order criticality

The criticality measure (12.1.10) is the largest decrease of the genuine Taylor polynomial
on a closed ball. The supremum is attained for nonnegative radii in finite dimension,
as proved in the backbone. This formulation also permits radius zero.
-/

namespace CartisGouldToint

/-- The Taylor criticality measure `φ_{f,j}^δ(x)` of equation (12.1.10), the maximum of
`f(x)-T_{f,j}(x,s)` over `‖s‖ ≤ δ`. The polynomial uses the actual derivative tensors of `f`. -/
noncomputable def highOrderCriticality {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (j : ℕ) (x : E) (δ : ℝ) : ℝ :=
  TaylorModel.criticality f j x δ

/-- Zero Taylor criticality is equivalent to every feasible model decrement being nonpositive. -/
theorem highOrderCriticality_eq_zero_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (f : E → ℝ) (j : ℕ) (x : E) {δ : ℝ} (hδ : 0 ≤ δ) :
    highOrderCriticality f j x δ = 0 ↔
      ∀ s : E, ‖s‖ ≤ δ → TaylorModel.decrement f j x s ≤ 0 :=
  TaylorModel.criticality_eq_zero_iff f j x hδ

end CartisGouldToint

namespace CartisGouldToint
/-- **Theorem 12.1.7 (cascading approximate optimality).** An order-`j` Taylor criticality
bound implies the preceding-order bound when the radius satisfies the stated smallness
condition. The source radius restriction after (12.1.31) is included as
`2 * δ * ‖D^j f(x)‖ ≤ j * εj`, together with `δ ≤ 1`.

For a positive derivative norm this is equivalent to the printed quotient bound. When
the tensor vanishes it imposes no extra restriction, avoiding division by zero; Lean's
value for division by zero would otherwise turn the printed positive-radius condition
into an unintended impossible hypothesis. -/
theorem theorem_12_1_7 {n j : ℕ} (hj : 2 ≤ j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    {δ εj εprev : ℝ} (hε0 : 0 < εj) (_hε1 : εj ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hεprev : εj ≤ εprev)
    (hsmall : 2 * δ * ‖iteratedFDeriv ℝ j f x‖ ≤ (j : ℝ) * εj)
    (hcrit : highOrderCriticality f j x δ ≤ εj * δ ^ j / j.factorial) :
    highOrderCriticality f (j - 1) x δ ≤ εprev * δ ^ (j - 1) / (j - 1).factorial := by
  cases j with
  | zero => omega
  | succ p =>
    have hp : 1 ≤ p := by omega
    exact TaylorModel.criticality_cascade f p hp x hδ0.le hδ1 hε0.le hεprev hsmall hcrit
end CartisGouldToint
namespace CartisGouldToint
/-- The literal quotient-radius formulation of **Theorem 12.1.7** when the derivative
norm in the denominator is positive. The multiplied formulation also covers a zero tensor. -/
theorem theorem_12_1_7_of_radius_le {n j : ℕ} (hj : 2 ≤ j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    {δ εj εprev : ℝ} (hε0 : 0 < εj) (hε1 : εj ≤ 1) (hδ0 : 0 < δ)
    (hεprev : εj ≤ εprev) (hD : 0 < ‖iteratedFDeriv ℝ j f x‖)
    (hsmall : δ ≤ min 1 ((j : ℝ) * εj / (2 * ‖iteratedFDeriv ℝ j f x‖)))
    (hcrit : highOrderCriticality f j x δ ≤ εj * δ ^ j / j.factorial) :
    highOrderCriticality f (j - 1) x δ ≤ εprev * δ ^ (j - 1) / (j - 1).factorial := by
  apply theorem_12_1_7 hj f x hε0 hε1 hδ0 (le_min_iff.mp hsmall).1 hεprev _ hcrit
  have hmul := (le_div_iff₀ (show 0 < 2 * ‖iteratedFDeriv ℝ j f x‖ by positivity)).1
    (le_min_iff.mp hsmall).2
  nlinarith
end CartisGouldToint

namespace CartisGouldToint

/-- **Theorem 12.1.4 (the criticality measure and local minimizers).** First- and
second-order Taylor criticality vanish for all positive radii at a local minimum with
the respective regularity. At every positive order `j`, the ratio of criticality to
`δ^j` tends to zero as the positive radius `δ` tends to zero. -/
theorem theorem_12_1_4 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    (ContDiff ℝ 1 f → IsLocalMin f x →
      ∀ δ : ℝ, 0 < δ → highOrderCriticality f 1 x δ = 0) ∧
    (ContDiff ℝ 2 f → IsLocalMin f x →
      ∀ δ : ℝ, 0 < δ → highOrderCriticality f 2 x δ = 0) ∧
    (∀ j : ℕ, 1 ≤ j → ContDiff ℝ j f → IsLocalMin f x →
      Filter.Tendsto (fun δ : ℝ => highOrderCriticality f j x δ / δ ^ j)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) := by
  refine ⟨fun _ hmin δ hδ =>
    TaylorModel.criticality_one_eq_zero_of_isLocalMin hmin hδ.le, ?_, ?_⟩
  · exact fun hf hmin δ hδ => TaylorModel.criticality_two_eq_zero_of_isLocalMin hf hmin hδ.le
  · exact fun j hj hf hmin => TaylorModel.tendsto_criticality_div_pow (by omega) hf hmin

end CartisGouldToint
