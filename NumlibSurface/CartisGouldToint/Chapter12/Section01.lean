import Numlib.Optimization.HighOrder.CurveOptimality
import Numlib.Optimization.HighOrder.Criticality
import Numlib.Optimization.LineSearch.Peano
import Numlib.Optimization.HighOrder.CriticalityLowOrder
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

namespace CartisGouldToint

/-- **Theorem 12.1.3 (relating old and new criticality measures).**
First-order criticality is exactly the radius times the gradient norm. Zero quadratic
criticality implies zero gradient and positive semidefinite Hessian, with the bound for
every actual Hessian eigenvalue. The third derivative projected orthogonally onto the
common first/second-order kernel obeys (12.1.13), and the stated vanishing criticality
ratio gives all three orders of necessary optimality conditions.

The tensor norm is the diagonal definition in the first equality of (A.7), expressed
on the closed unit ball. The actual orthogonal projection is applied in every tensor
argument. Under the source positive semidefiniteness hypothesis, the linear common
kernel equals the homogeneous-kernel intersection (A.8), as included explicitly below.
The quadratic-form and ball formulations also cover dimension zero. -/
theorem theorem_12_1_3 {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (_hf1 : ContDiffAt ℝ 1 f x) :
    (∀ δ : ℝ, 0 < δ →
      ‖gradient f x‖ = highOrderCriticality f 1 x δ / δ ∧
      (highOrderCriticality f 1 x δ = 0 ↔ gradient f x = 0)) ∧
    (ContDiffAt ℝ 2 f x → ∀ δ : ℝ, 0 < δ →
      highOrderCriticality f 2 x δ = 0 → gradient f x = 0 ∧
      (∀ v, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => v)) ∧
      (∀ (μ : ℝ) (v : EuclideanSpace ℝ (Fin n)), v ≠ 0 →
        TaylorModel.hessianOperator f x v = μ • v → 0 ≤ μ)) ∧
    (ContDiffAt ℝ 3 f x → gradient f x = 0 →
      (∀ v, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => v)) →
      (∀ v, v ∈ TaylorModel.secondOrderKernel f x ↔
        iteratedFDeriv ℝ 1 f x (fun _ => v) = 0 ∧
        iteratedFDeriv ℝ 2 f x (fun _ => v) = 0) ∧
      (∀ δ : ℝ, 0 < δ →
        ContinuousMultilinearMap.diagonalNorm (TaylorModel.projectedThirdDerivative f x) ≤
          highOrderCriticality f 3 x δ / (δ ^ 3 / 6)) ∧
      (Filter.Tendsto (fun δ : ℝ => highOrderCriticality f 3 x δ / δ ^ 3)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
        gradient f x = 0 ∧ (∀ v, 0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => v)) ∧
        (∀ v, iteratedFDeriv ℝ 1 f x (fun _ => v) = 0 →
          iteratedFDeriv ℝ 2 f x (fun _ => v) = 0 →
          iteratedFDeriv ℝ 3 f x (fun _ => v) = 0))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro δ hδ
    change ‖gradient f x‖ = TaylorModel.criticality f 1 x δ / δ ∧
      (TaylorModel.criticality f 1 x δ = 0 ↔ gradient f x = 0)
    rw [TaylorModel.criticality_one f x hδ]
    constructor
    · field_simp
    · simp [hδ.ne']
  · intro _hf2 δ hδ hc
    exact TaylorModel.first_second_order_of_criticality_two_eq_zero f x hδ hc
  · intro hf3 hg hp
    have hf2 : ContDiffAt ℝ 2 f x := hf3.of_le (by norm_num)
    refine ⟨fun v => TaylorModel.mem_secondOrderKernel_iff_diagonal hf2 hp,
      fun δ hδ => TaylorModel.projectedThirdDerivative_diagonalNorm_le f x hδ, ?_⟩
    intro hlim
    refine ⟨hg, hp, ?_⟩
    intro v h1 h2
    exact TaylorModel.third_derivative_zero_on_kernel_of_tendsto f x hlim v
      ((TaylorModel.mem_secondOrderKernel_iff_diagonal hf2 hp).2 ⟨h1,h2⟩)

end CartisGouldToint

namespace CartisGouldToint

/-- Theorem 12.1.2, as a counterexample for linesearch traces whose moves use descent
directions. A smooth Euclidean polynomial has a strict minimum along every nonconstant
straight line through zero, but every such trace started at zero stays there and fails
approximate optimality of every order at least four. The actual directional derivatives
and Taylor criticality are used. The Peano coefficients are `κ₁ = 3, κ₂ = 2`; the printed
choice `κ₁ = 1, κ₂ = 2` instead has a global minimum at zero. -/
theorem theorem_12_1_2 :
    ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ ⊤ f ∧
      (∀ v, IsLocalMin (fun t : ℝ => f (t • v)) 0) ∧
      (∀ v ≠ 0, ∀ᶠ t : ℝ in nhds 0, t ≠ 0 → f 0 < f (t • v)) ∧
      ¬ IsLocalMin f 0 ∧ LineSearch.DescentTrace f (fun _ => 0) ∧
      (∀ x : ℕ → EuclideanSpace ℝ (Fin 2),
        LineSearch.DescentTrace f x → x 0 = 0 → ∀ k,
          x k = 0 ∧ ∀ (q : ℕ), 4 ≤ q → ∀ δ : Fin q → ℝ,
            (∀ j, 0 < δ j ∧ δ j ≤ 1) →
            ¬ ∀ j : Fin q, TaylorModel.criticality f (j.val + 1) (x k) (δ j) ≤
              (1 / 100 : ℝ) * δ j ^ (j.val + 1) / (j.val + 1).factorial) := by
  refine ⟨PeanoExample.saddle, PeanoExample.smooth, PeanoExample.line_min,
    PeanoExample.line_strict, PeanoExample.not_local_min,
    LineSearch.descentTrace_const _ _, ?_⟩
  intro x hx hx0 k
  have hk := PeanoExample.trace_stays hx hx0 k
  refine ⟨hk, ?_⟩
  intro q hq δ hd
  rw [hk]
  exact PeanoExample.not_approximate_of_order hq δ hd

end CartisGouldToint

namespace CartisGouldToint
open scoped BigOperators

/-- The ordered positive integer tuples `P(j,k)` of equation (12.1.5). -/
noncomputable abbrev orderedCompositions (j k : ℕ) : Finset (Fin k → ℕ) :=
  TaylorModel.orderedCompositions j k

/-- The tuples in (12.1.5) have positive entries at most j and total degree j. -/
theorem mem_orderedCompositions {j k : ℕ} {l : Fin k → ℕ} :
    l ∈ orderedCompositions j k ↔ (∀ i, 1 ≤ l i ∧ l i ≤ j) ∧ ∑ i, l i = j :=
  TaylorModel.mem_orderedCompositions

/-- Theorem12.1.1: at a local minimum, the order-j coefficient (12.1.6) is
nonnegative whenever every lower positive-order coefficient (12.1.7) vanishes.
The curve coefficients are vectors, correcting the scalar OCR transcription.
Zero coefficients are permitted: the necessary condition holds for all polynomial
curves. The actual finite derivative tensors are used, with only local C^q
regularity. Ordered compositions supply exactly the mixed tensor terms. -/
theorem theorem_12_1_1 {n q j : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ q f x) (hmin : IsLocalMin f x)
    (hj : 0 < j) (hjq : j ≤ q) (s : ℕ → EuclideanSpace ℝ (Fin n))
    (hzero : ∀ i, 0 < i → i < j →
      (∑ k ∈ Finset.Icc 1 i, ((k.factorial : ℝ)⁻¹) *
        ∑ l ∈ orderedCompositions i k,
          iteratedFDeriv ℝ k f x (fun a => s (l a))) = 0) :
    0 ≤ ∑ k ∈ Finset.Icc 1 j, ((k.factorial : ℝ)⁻¹) *
      ∑ l ∈ orderedCompositions j k, iteratedFDeriv ℝ k f x (fun a => s (l a)) := by
  rw [← TaylorModel.curveCoefficient_eq_sum_Icc hj]
  apply TaylorModel.curveCoefficient_nonneg_of_isLocalMin hj hjq hf hmin s
  intro i hi hij
  rw [TaylorModel.curveCoefficient_eq_sum_Icc hi]
  exact hzero i hi hij

end CartisGouldToint
