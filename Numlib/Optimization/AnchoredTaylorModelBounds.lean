import Numlib.Optimization.ConstrainedTaylorGaps
import Numlib.Optimization.HigherOrderRegularizationModelBounds
import Numlib.Optimization.HigherOrderRegularizationBounds
import Numlib.Optimization.InexactTaylorModels
import Numlib.Analysis.Calculus.NormPowerFactorialBounds

/-!
# Anchored derivative remainders and feasible model-gap transfer

Actual jets need bounds only at model centers and Lipschitz comparisons from those centers
into an open convex neighborhood. Symmetry supplies sharp operator estimates in finite
real inner product spaces. Every derivative remainder and every regularized model-gap
comparison below retains those local assumptions. The feasible set may be nonconvex.
-/

noncomputable section
open scoped Nat
open Set Metric
namespace Optimization.ConstrainedTaylorCriticality
open RegularizedTaylorModel TaylorCriticality

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {r : ℕ} {A U : Set E} {includeValue : Bool} {L B : ℕ → ℝ}

/-- At each point of the open neighborhood, every available derivative is ambient. -/
theorem HasAnchoredBoundedJets.contDiffAt
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) {x : E} (hx : x ∈ U) :
    ContDiffAt ℝ r f x := (hf.contDiffOn x hx).contDiffAt (hf.isOpen.mem_nhds hx)

end Normed

section Add
variable {E : Type*} [AddSemigroup E]

/-- Translating feasible displacements twice is the displacement set at the translated
point. This identity aligns objective and model gap domains exactly. -/
@[simp] theorem feasibleDisplacements_feasibleDisplacements (X : Set E) (x s : E) :
    feasibleDisplacements (feasibleDisplacements X x) s = feasibleDisplacements X (x + s) := by
  ext d
  simp only [mem_feasibleDisplacements, add_assoc]

end Add

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {r p j : ℕ} {A U : Set E}
  {includeValue : Bool} {L B : ℕ → ℝ}

/-- At a center, symmetry converts the diagonal jet bound into the operator-norm bound. -/
theorem HasAnchoredBoundedJets.operator_bound
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hj : 1 ≤ j) (hjr : j ≤ r)
    {x : E} (hx : x ∈ A) : ‖iteratedFDeriv ℝ j f x‖ ≤ B j := by
  have hfj : ContDiffAt ℝ j f x :=
    (hf.contDiffAt (hf.centers_subset hx)).of_le (by exact_mod_cast hjr)
  rw [← hfj.diagonalNorm_iteratedFDeriv_eq_norm (by omega : 0 < j)]
  exact hf.diagonalNorm_bound hj hjr hx

/-- Anchored comparisons control the whole symmetric derivative tensor, without any
pairwise Lipschitz assumption between two arbitrary neighborhood points. -/
theorem HasAnchoredBoundedJets.operator_lipschitz
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hj : 1 ≤ j) (hjr : j ≤ r)
    {x y : E} (hx : x ∈ A) (hy : y ∈ U) :
    ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x‖ ≤ L j * ‖y - x‖ := by
  rw [← diagonalNorm_iteratedFDeriv_sub_eq_norm
    ((hf.contDiffAt hy).of_le (by exact_mod_cast hjr))
    ((hf.contDiffAt (hf.centers_subset hx)).of_le (by exact_mod_cast hjr))
    (by omega : 0 < j)]
  exact hf.lipschitz_diagonalNorm hj hjr hx hy

/-- Every derivative of a Taylor model has the sharp factorial remainder from its actual
center. The trial endpoint lies in the neighborhood; it need not lie among the centers. -/
theorem HasAnchoredBoundedJets.derivative_remainder
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hp : 1 ≤ p) (hpr : p ≤ r)
    (hj : j ≤ p) {x s : E} (hx : x ∈ A) (hxs : x + s ∈ U) :
    ‖iteratedFDeriv ℝ j f (x + s) - iteratedFDeriv ℝ j (taylorModel f p x) s‖ ≤
      L p / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) := by
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • s ∈ U := by
    have hh := hf.convex (hf.centers_subset hx) hxs (sub_nonneg.mpr ht.2) ht.1 (by ring)
    convert hh using 1
    module
  have hh := norm_iteratedFDeriv_sub_taylorModel_le_holder
    (f := f) (p := p) (j := j) (x := x) (s := s) (H := L p) (β := 1)
    hj (by norm_num) (fun t ht => (hf.contDiffAt (hseg t ht)).of_le (by exact_mod_cast hpr))
    (fun t ht => by simpa only [add_sub_cancel_left, Real.rpow_one] using
      hf.operator_lipschitz hp hpr hx (hseg t ht))
  have hprod : ∀ k : ℕ, (∏ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) + 1)) =
      ((k + 1)! : ℝ) := by
    intro k
    have he := congrArg (fun n : ℕ => (n : ℝ)) (Nat.factorial_mul_ascFactorial 1 k)
    norm_num [Nat.ascFactorial_eq_prod_range, Nat.cast_prod, Nat.cast_add, Nat.cast_one,
      add_comm, add_left_comm, add_assoc] at he ⊢
    exact he
  rw [hprod, ← Nat.cast_add_one, Real.rpow_natCast] at hh
  exact hh

/-- All actual regularized-model derivatives differ from the objective derivatives by the
sharp remainder plus the radial contribution. No global regularity or convex feasible set
is required. -/
theorem HasAnchoredBoundedJets.regularized_derivative_difference
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hp : 1 ≤ p) (hpr : p ≤ r)
    (hj : j ≤ p) {x s : E} (hx : x ∈ A) (hxs : x + s ∈ U) (hs : s ≠ 0)
    {σ S : ℝ} (hσ : 0 ≤ σ) (hS : σ ≤ S) :
    ‖iteratedFDeriv ℝ j f (x + s) -
      iteratedFDeriv ℝ j (HigherOrderRegularization.model f p x σ) s‖ ≤
      (L p + S) / ((p - j + 1)! : ℝ) * ‖s‖ ^ (p - j + 1) :=
  HigherOrderRegularization.norm_derivative_sub_model_le hs hσ hS
    (hf.derivative_remainder hp hpr hj hx hxs)
    (norm_iteratedFDeriv_norm_pow_le_factorial hj s)

/-- The regularized Taylor model has a global top-jet Lipschitz constant equal to its
parameter even when the original objective has only anchored smoothness. -/
theorem HasAnchoredBoundedJets.diagonalLipschitz_model
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hpr : p ≤ r)
    {x : E} (hx : x ∈ A) {σ : ℝ} (hσ : 0 ≤ σ) :
    HigherOrderRegularization.DiagonalLipschitz
      (HigherOrderRegularization.model f p x σ) p σ :=
  HigherOrderRegularization.diagonalLipschitz_model
    ((hf.contDiffAt (hf.centers_subset hx)).of_le (by exact_mod_cast hpr)) hσ

/-- The full factorial-weighted decrement comparison follows from the actual anchored
objective jets. The testing displacement need not itself be feasible. -/
theorem HasAnchoredBoundedJets.regularized_decrement_difference
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hp : 1 ≤ p) (hpr : p ≤ r)
    (hj : j ≤ p) {x s : E} (hx : x ∈ A) (hxs : x + s ∈ U) (hs : s ≠ 0)
    {σ S δ : ℝ} (hσ : 0 ≤ σ) (hS : σ ≤ S) (d : E) (hd : ‖d‖ ≤ δ) :
    |taylorDecrement f j (x + s) d -
      taylorDecrement (HigherOrderRegularization.model f p x σ) j s d| ≤
      (L p + S) * ∑ i ∈ Finset.Icc 1 j,
        δ ^ i * ‖s‖ ^ (p - i + 1) / ((i ! : ℝ) * ((p - i + 1)! : ℝ)) := by
  have hC : 0 ≤ L p + S :=
    add_nonneg (hf.lipschitz_nonneg p (Or.inl hp) hpr) (hσ.trans hS)
  have hb := InexactTaylorModels.decrement_error_le
    (fun i => iteratedFDeriv ℝ i f (x + s))
    (fun i => iteratedFDeriv ℝ i (HigherOrderRegularization.model f p x σ) s)
    (fun i => (L p + S) / ((p - i + 1)! : ℝ) * ‖s‖ ^ (p - i + 1)) j d (by
      intro i hi
      exact hf.regularized_derivative_difference hp hpr
        ((Finset.mem_Icc.mp hi).2.trans hj) hx hxs hs hσ hS)
  simp only [InexactTaylorModels.decrement_iteratedFDeriv] at hb
  apply hb.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ((L p + S) / ((p - i + 1)! : ℝ) * ‖s‖ ^ (p - i + 1)) * δ ^ i /
        (i ! : ℝ) := by
      gcongr
    _ = _ := by ring

/-- Anchored jets control the difference between the true constrained gap at the endpoint
and the regularized-model gap on the actual translated constraint set. Both factorial
normalizations are retained, and neither convexity nor connectivity of the feasible set
is assumed. -/
theorem HasAnchoredBoundedJets.regularized_gap_difference
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hp : 1 ≤ p) (hpr : p ≤ r)
    (hj : j ≤ p) {X : Set E} (hX : IsClosed X) {x s : E}
    (hx : x ∈ A) (hxs : x + s ∈ X) (hXU : X ⊆ U) (hs : s ≠ 0)
    {σ S δ : ℝ} (hσ : 0 ≤ σ) (hS : σ ≤ S) (hδ : 0 ≤ δ) :
    |taylorGap f X j (x + s) δ -
      taylorGap (HigherOrderRegularization.model f p x σ)
        (feasibleDisplacements X x) j s δ| ≤
      (L p + S) * ∑ i ∈ Finset.Icc 1 j,
        δ ^ i * ‖s‖ ^ (p - i + 1) / ((i ! : ℝ) * ((p - i + 1)! : ℝ)) := by
  simp only [taylorGap, feasibleDisplacements_feasibleDisplacements]
  apply abs_gapOn_sub_le
    (isCompact_feasibleDisplacements_inter_closedBall hX (x + s) δ)
    ⟨0, zero_mem_feasibleBall hxs hδ⟩
    (continuous_taylorDecrement f j (x + s)).continuousOn
    (continuous_taylorDecrement (HigherOrderRegularization.model f p x σ) j s).continuousOn
  intro d hd
  exact hf.regularized_decrement_difference hp hpr hj hx (hXU hxs) hs hσ hS d
    (by simpa only [mem_closedBall_zero_iff] using hd.2)

/-- A true failed endpoint criterion and a successful model criterion give the positive
transfer margin with its exact feasible geometry. These are the actual two gap tests;
no step size, objective decrease, evaluation count, or convergence conclusion is assumed. -/
theorem HasAnchoredBoundedJets.transfer_of_gap_failure
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hp : 1 ≤ p) (hpr : p ≤ r)
    (hj : j ≤ p) {X : Set E} (hX : IsClosed X) {x s : E}
    (hx : x ∈ A) (hxs : x + s ∈ X) (hXU : X ⊆ U) (hs : s ≠ 0)
    {σ S δ ε θ : ℝ} (hσ : 0 ≤ σ) (hS : σ ≤ S) (hδ : 0 ≤ δ)
    (hfail : ε * δ ^ j / (j ! : ℝ) < taylorGap f X j (x + s) δ)
    (hmodel : taylorGap (HigherOrderRegularization.model f p x σ)
      (feasibleDisplacements X x) j s δ ≤ θ * ε * δ ^ j / (j ! : ℝ)) :
    (1 - θ) * ε * δ ^ j / (j ! : ℝ) <
      (L p + S) * ∑ i ∈ Finset.Icc 1 j,
        δ ^ i * ‖s‖ ^ (p - i + 1) / ((i ! : ℝ) * ((p - i + 1)! : ℝ)) := by
  have hb := (abs_le.mp (hf.regularized_gap_difference hp hpr hj hX hx hxs hXU
    hs hσ hS hδ)).2
  have he : (1 - θ) * ε * δ ^ j / (j ! : ℝ) =
      ε * δ ^ j / (j ! : ℝ) - θ * ε * δ ^ j / (j ! : ℝ) := by ring
  rw [he]
  linarith

end Optimization.ConstrainedTaylorCriticality
