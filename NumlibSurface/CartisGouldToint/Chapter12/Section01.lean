import Numlib.Optimization.HighOrder.Criticality
import Numlib.Optimization.HighOrder.CriticalityApproximate
import Numlib.Optimization.HighOrder.CriticalityStability
import Numlib.Optimization.HighOrder.CriticalityLocalMin
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cartis–Gould–Toint, Section 12.1: high-order criticality

The criticality measure (12.1.10) is the largest decrease of the genuine Taylor polynomial
on a closed ball. The supremum is attained for nonnegative radii in finite dimension,
as proved in the backbone. This formulation also permits radius zero.

For Theorem 12.1.6(ii), second-order smoothness and the tolerance range from the
approximate-minimizer definition are explicit; its first-order branch retains first-order
smoothness. The Hessian bound is given as a quadratic form with an eigenvalue bridge.
Theorem 12.1.8 retains the local Lipschitz neighborhood and uses the optimality radius
`δ_j` in both tolerances; the unindexed printed `δ` denotes that same radius.
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

namespace CartisGouldToint

/-- **Theorem 12.1.6 (comparing approximate optimality measures).**
First-order Taylor criticality bounds the gradient norm. Second-order Taylor criticality
bounds every Hessian quadratic form, every genuine Hessian eigenvalue, and the gradient
with the explicit Hessian-dependent constant `√(max 1 ‖D²f(x)‖)`.

The source's `C¹` assumption is sufficient for (i); (ii) requires `C²` to interpret the
classical Hessian. The range `0 ≤ ε₂ ≤ 1`, used in its proof and supplied by the preceding
approximate-minimizer definition, is explicit. The quadratic-form statement also covers
zero-dimensional spaces, where a smallest eigenvalue is undefined. -/
theorem theorem_12_1_6 {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (_hf1 : ContDiffAt ℝ 1 f x) :
    (∀ (δ₁ ε₁ : ℝ), 0 < δ₁ → highOrderCriticality f 1 x δ₁ ≤ ε₁ * δ₁ →
      ‖gradient f x‖ ≤ ε₁) ∧
    (ContDiffAt ℝ 2 f x → ∀ (δ ε₂ : ℝ), 0 < δ → 0 ≤ ε₂ → ε₂ ≤ 1 →
      highOrderCriticality f 2 x δ ≤ ε₂ * δ ^ 2 / 2 →
      (∀ v, -ε₂ * ‖v‖ ^ 2 ≤ iteratedFDeriv ℝ 2 f x (fun _ => v)) ∧
      ‖gradient f x‖ ≤ δ * Real.sqrt (max 1 ‖iteratedFDeriv ℝ 2 f x‖) * Real.sqrt ε₂ ∧
      (∀ (μ : ℝ) (v : EuclideanSpace ℝ (Fin n)), v ≠ 0 →
        TaylorModel.hessianOperator f x v = μ • v → -ε₂ ≤ μ)) := by
  constructor
  · intro δ₁ ε₁ hδ₁ hcrit
    change TaylorModel.criticality f 1 x δ₁ ≤ ε₁ * δ₁ at hcrit
    rw [TaylorModel.criticality_one f x hδ₁] at hcrit
    have hh : δ₁ * ‖gradient f x‖ ≤ δ₁ * ε₁ := by nlinarith
    exact (mul_le_mul_iff_of_pos_left hδ₁).mp hh
  · intro _hf2 δ ε₂ hδ hε0 hε1 hcrit
    exact ⟨TaylorModel.curvature_ge_neg_mul_sq f x hδ hcrit,
      TaylorModel.gradient_norm_le_of_criticality_two f x hδ hε0 hε1 hcrit,
      fun _ v hv he => TaylorModel.eigenvalue_ge_neg_of_criticality_two f x hδ hcrit v hv he⟩

end CartisGouldToint

namespace CartisGouldToint

/-- **Theorem 12.1.8 (stability of approximate unconstrained minimizers).**
A small order-`j` Taylor criticality bounds the true objective decrease nearby. For
positive highest-derivative Lipschitz constant the guaranteed radius is
`min δ ((j+1)ε/L)` and the tolerance doubles; for zero constant the original tolerance
holds on the full radius ball. The Lipschitz hypothesis is local to an open ball whose
radius exceeds `δ`. The unindexed `δ` in the printed tolerance (12.1.35) means its
optimality radius `δ_j`, as in (12.1.34), (12.1.36) and the proof. -/
theorem theorem_12_1_8 {n j : ℕ} (hj : 0 < j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hf : ContDiff ℝ j f) {δ ε L R : ℝ}
    (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (hε : 0 < ε) (_hε1 : ε ≤ 1)
    (hL : 0 ≤ L) (hR : δ < R)
    (hlip : ∀ u ∈ Metric.ball x R, ∀ v ∈ Metric.ball x R,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ L * ‖u - v‖)
    (hcrit : highOrderCriticality f j x δ ≤ ε * δ ^ j / j.factorial) :
    (0 < L → ∀ d : EuclideanSpace ℝ (Fin n),
      ‖d‖ ≤ min δ ((j + 1 : ℕ) * ε / L) →
      f x - 2 * ε * δ ^ j / j.factorial ≤ f (x + d)) ∧
    (L = 0 → ∀ d : EuclideanSpace ℝ (Fin n), ‖d‖ ≤ δ →
      f x - ε * δ ^ j / j.factorial ≤ f (x + d)) := by
  have hball : Metric.closedBall x δ ⊆ Metric.ball x R := fun z hz =>
    (Metric.mem_closedBall.mp hz).trans_lt hR
  have hlip' : ∀ u ∈ Metric.closedBall x δ, ∀ v ∈ Metric.closedBall x δ,
      ‖iteratedFDeriv ℝ j f u - iteratedFDeriv ℝ j f v‖ ≤ L * ‖u - v‖ :=
    fun u hu v hv => hlip u (hball hu) v (hball hv)
  constructor
  · intro hLpos d hd
    apply TaylorModel.value_ge_sub_two_tolerance_of_criticality hj Metric.isOpen_ball
      hf.contDiffOn x hδ.le hε.le hball hL hlip' hcrit (le_min_iff.mp hd).1
    have hmul := (le_div_iff₀ hLpos).mp (le_min_iff.mp hd).2
    nlinarith
  · intro hLzero d hd
    have hb := TaylorModel.value_ge_of_criticality hj Metric.isOpen_ball hf.contDiffOn x
      hδ.le hball hL hlip' hcrit hd
    simpa only [hLzero, zero_mul, zero_div, sub_zero] using hb

end CartisGouldToint
