import Numlib.Optimization.ConstrainedTaylorCriticality
import Numlib.Optimization.TaylorModelRemainder
import Numlib.Analysis.Normed.Multilinear.Diagonal

/-!
# Taylor gaps on closed feasible sets

Translated feasible sets provide genuine constrained Taylor gaps without convexity.
An anchored jet family records smoothness on a neighborhood, bounds at a specified
set of model centers, and Lipschitz comparisons from those centers to the neighborhood.
-/

noncomputable section
open Set Metric
open scoped Nat
namespace Optimization.ConstrainedTaylorCriticality
open TaylorCriticality RegularizedTaylorModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual Taylor decrement maximized over feasible displacements in a closed ball. -/
def taylorGap (f : E → ℝ) (X : Set E) (j : ℕ) (x : E) (δ : ℝ) : ℝ :=
  gapOn (taylorDecrement f j x) (feasibleDisplacements X x ∩ closedBall 0 δ)

omit [NormedSpace ℝ E] in
/-- At a feasible point every nonnegative-radius feasible ball contains zero. -/
theorem zero_mem_feasibleBall {X : Set E} {x : E} {δ : ℝ}
    (hx : x ∈ X) (hδ : 0 ≤ δ) :
    (0 : E) ∈ feasibleDisplacements X x ∩ closedBall 0 δ := by
  exact ⟨zero_mem_feasibleDisplacements.mpr hx, by simpa using hδ⟩

/-- The constrained gap is an attained maximum on closed feasible sets in proper spaces. -/
theorem exists_eq_taylorGap [ProperSpace E] (f : E → ℝ) {X : Set E}
    (hX : IsClosed X) (j : ℕ) {x : E} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ d, x + d ∈ X ∧ ‖d‖ ≤ δ ∧ taylorDecrement f j x d = taylorGap f X j x δ := by
  obtain ⟨d, hd, he⟩ := exists_eq_gapOn
    (isCompact_feasibleDisplacements_inter_closedBall hX x δ)
    ⟨0, zero_mem_feasibleBall hx hδ⟩ (continuous_taylorDecrement f j x).continuousOn
  exact ⟨d, hd.1, by simpa using hd.2, he⟩

/-- Bounding the constrained gap is equivalent to bounding every feasible decrement. -/
theorem taylorGap_le_iff [ProperSpace E] (f : E → ℝ) {X : Set E}
    (hX : IsClosed X) (j : ℕ) {x : E} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) (G : ℝ) :
    taylorGap f X j x δ ≤ G ↔
      ∀ d, x + d ∈ X → ‖d‖ ≤ δ → taylorDecrement f j x d ≤ G := by
  exact (gapOn_le_iff (isCompact_feasibleDisplacements_inter_closedBall hX x δ)
    ⟨0, zero_mem_feasibleBall hx hδ⟩ (continuous_taylorDecrement f j x).continuousOn).trans
    (by simp only [mem_inter_iff, mem_feasibleDisplacements, mem_closedBall_zero_iff,
      and_imp])

/-- Feasibility of zero makes every constrained Taylor gap nonnegative. -/
theorem taylorGap_nonneg [ProperSpace E] (f : E → ℝ) {X : Set E}
    (hX : IsClosed X) (j : ℕ) {x : E} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ taylorGap f X j x δ :=
  gapOn_nonneg (isCompact_feasibleDisplacements_inter_closedBall hX x δ)
    (continuous_taylorDecrement f j x).continuousOn
    (zero_mem_feasibleBall hx hδ) (taylorDecrement_zero f j x)

/-- The constrained gap equals the objective minus an attained actual Taylor model minimum. -/
theorem exists_taylorModel_minimum [ProperSpace E] (f : E → ℝ) {X : Set E}
    (hX : IsClosed X) (j : ℕ) {x : E} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ d, x + d ∈ X ∧ ‖d‖ ≤ δ ∧
      (∀ e, x + e ∈ X → ‖e‖ ≤ δ → taylorModel f j x d ≤ taylorModel f j x e) ∧
      taylorGap f X j x δ = f x - taylorModel f j x d := by
  obtain ⟨d, hd, hdn, he⟩ := exists_eq_taylorGap f hX j hx hδ
  refine ⟨d, hd, hdn, ?_, he.symm.trans (taylorDecrement_eq f j x d)⟩
  intro e heX hen
  have h := (taylorGap_le_iff f hX j hx hδ _).mp le_rfl e heX hen
  rw [← he, taylorDecrement_eq, taylorDecrement_eq] at h
  linarith

/-- A feasible initial sublevel set, used as the set of Taylor model centers. -/
def feasibleSublevelSet (f : E → ℝ) (X : Set E) (x₀ : E) : Set E :=
  {x ∈ X | f x ≤ f x₀}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Membership records both feasibility and the initial objective upper bound. -/
@[simp] theorem mem_feasibleSublevelSet {f : E → ℝ} {X : Set E} {x₀ x : E} :
    x ∈ feasibleSublevelSet f X x₀ ↔ x ∈ X ∧ f x ≤ f x₀ := Iff.rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A feasible initial point belongs to its own feasible sublevel set. -/
theorem self_mem_feasibleSublevelSet {f : E → ℝ} {X : Set E} {x₀ : E} (hx₀ : x₀ ∈ X) :
    x₀ ∈ feasibleSublevelSet f X x₀ := ⟨hx₀, le_rfl⟩

/-- Actual diagonal jets bounded at centers `A`, with Lipschitz comparisons to an open convex
neighborhood `U`. Positive orders are bounded; `includeValue` additionally requests order-zero
Lipschitz continuity, without imposing an unnecessary bound on objective values. Repeated-direction
bounds express the diagonal tensor norm and remain meaningful in zero-dimensional spaces. -/
structure HasAnchoredBoundedJets (f : E → ℝ) (r : ℕ) (A U : Set E)
    (includeValue : Bool) (L B : ℕ → ℝ) : Prop where
  isOpen : IsOpen U
  convex : Convex ℝ U
  centers_subset : A ⊆ U
  contDiffOn : ContDiffOn ℝ r f U
  lipschitz_nonneg : ∀ j, (1 ≤ j ∨ includeValue = true) → j ≤ r → 0 ≤ L j
  bound_nonneg : ∀ j, 1 ≤ j → j ≤ r → 0 ≤ B j
  bound : ∀ j, 1 ≤ j → j ≤ r → ∀ x ∈ A, ∀ d : E,
    ‖iteratedFDeriv ℝ j f x (fun _ => d)‖ ≤ B j * ‖d‖ ^ j
  lipschitz : ∀ j, (1 ≤ j ∨ includeValue = true) → j ≤ r →
    ∀ x ∈ A, ∀ y ∈ U, ∀ d : E,
      ‖(iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x) (fun _ => d)‖ ≤
        L j * ‖y - x‖ * ‖d‖ ^ j

/-- Positive-order directional jet bounds give exactly the diagonal tensor bound. -/
theorem HasAnchoredBoundedJets.diagonalNorm_bound {f : E → ℝ} {r j : ℕ} {A U : Set E}
    {includeValue : Bool} {L B : ℕ → ℝ}
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hj : 1 ≤ j) (hjr : j ≤ r)
    {x : E} (hx : x ∈ A) : (iteratedFDeriv ℝ j f x).diagonalNorm ≤ B j := by
  apply (ContinuousMultilinearMap.diagonalNorm_le_iff _ (by omega)
    (hf.bound_nonneg j hj hjr)).mpr
  exact hf.bound j hj hjr x hx

/-- Positive-order anchored comparisons give the diagonal tensor distance bound. -/
theorem HasAnchoredBoundedJets.lipschitz_diagonalNorm {f : E → ℝ} {r j : ℕ} {A U : Set E}
    {includeValue : Bool} {L B : ℕ → ℝ}
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hj : 1 ≤ j) (hjr : j ≤ r)
    {x y : E} (hx : x ∈ A) (hy : y ∈ U) :
    (iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f x).diagonalNorm ≤ L j * ‖y - x‖ := by
  apply (ContinuousMultilinearMap.diagonalNorm_le_iff _ (by omega)
    (mul_nonneg (hf.lipschitz_nonneg j (Or.inl hj) hjr) (norm_nonneg _))).mpr
  exact hf.lipschitz j (Or.inl hj) hjr x hx y hy

/-- Requesting order zero controls actual objective values, including in dimension zero. -/
theorem HasAnchoredBoundedJets.value_lipschitz {f : E → ℝ} {r : ℕ} {A U : Set E}
    {L B : ℕ → ℝ} (hf : HasAnchoredBoundedJets f r A U true L B)
    {x y : E} (hx : x ∈ A) (hy : y ∈ U) : |f y - f x| ≤ L 0 * ‖y - x‖ := by
  have h := hf.lipschitz 0 (Or.inr rfl) (Nat.zero_le r) x hx y hy 0
  simpa only [sub_apply, iteratedFDeriv_zero_apply,
    pow_zero, mul_one, Real.norm_eq_abs] using h

/-- The anchored family gives the sharp factorial Taylor remainder along segments inside its
neighborhood. The comparison uses only the selected model center, not pairwise control in `U`. -/
theorem HasAnchoredBoundedJets.remainder {f : E → ℝ} {r j : ℕ} {A U : Set E}
    {includeValue : Bool} {L B : ℕ → ℝ}
    (hf : HasAnchoredBoundedJets f r A U includeValue L B) (hj : 1 ≤ j) (hjr : j ≤ r)
    {x d : E} (hx : x ∈ A) (hxd : x + d ∈ U) :
    |f (x + d) - taylorModel f j x d| ≤
      L j / ((j + 1)! : ℝ) * ‖d‖ ^ (j + 1) := by
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • d ∈ U := by
    have := hf.convex (hf.centers_subset hx) hxd (sub_nonneg.mpr ht.2) ht.1 (by ring)
    convert this using 1; module
  apply norm_sub_taylorModel_le_of_lipschitz_diagonal hj
    (fun t ht => ((hf.contDiffOn.of_le (by exact_mod_cast hjr)) _ (hseg t ht)).contDiffAt
      (hf.isOpen.mem_nhds (hseg t ht)))
  intro t ht
  simpa only [add_sub_cancel_left] using hf.lipschitz j (Or.inl hj) hjr x hx
    (x + t • d) (hseg t ht) d

end Optimization.ConstrainedTaylorCriticality
