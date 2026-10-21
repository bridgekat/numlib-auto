import Numlib.Optimization.ConstrainedTaylorGaps
import Numlib.Optimization.SparseConstraints
import NumlibSurface.CartisGouldToint.Chapter12.Section01
import NumlibSurface.CartisGouldToint.Chapter14.Section01

/-!
# Chapter 14, Section 2: constrained Taylor gaps and local stability

Closed feasible sets need not be convex or connected. The actual translated feasible set
restricts each Taylor gap, and local derivative Lipschitz continuity gives objective stability
with the source's additive error and its sharper zero-constant branch. The foundational
interfaces also specify anchored level-set jets, the complexity exponent table, and sparsity.
The algorithm adaptations and their complexity bounds remain separate open obligations.
-/

noncomputable section
open Set Metric Optimization
open scoped Nat
namespace CartisGouldToint.Chapter14.Section02
variable {n m : ℕ}

/-- The feasible displacements (14.2.3), using the canonical actual translated constraint set. -/
abbrev feasibleDisplacements (X : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  ConstrainedTaylorCriticality.feasibleDisplacements X x

/-- A displacement is feasible exactly when its endpoint satisfies the constraints. -/
@[simp] theorem mem_feasibleDisplacements {X : Set (EuclideanSpace ℝ (Fin n))}
    {x d : EuclideanSpace ℝ (Fin n)} : d ∈ feasibleDisplacements X x ↔ x + d ∈ X := Iff.rfl

/-- Zero is feasible precisely at feasible points. -/
@[simp] theorem zero_mem_feasibleDisplacements {X : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} : 0 ∈ feasibleDisplacements X x ↔ x ∈ X :=
  ConstrainedTaylorCriticality.zero_mem_feasibleDisplacements

/-- The constrained Taylor gap (14.2.2), with the factorial-normalized Chapter 12 decrement. -/
abbrev constrainedTaylorGap (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) : ℝ :=
  ConstrainedTaylorCriticality.taylorGap f X j x δ

/-- A closed feasible set gives an attained constrained gap at every feasible point. -/
theorem exists_eq_constrainedTaylorGap (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsClosed X) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ d, x + d ∈ X ∧ ‖d‖ ≤ δ ∧
      Chapter12.Section01.taylorDecrement f j x d = constrainedTaylorGap f X j x δ :=
  ConstrainedTaylorCriticality.exists_eq_taylorGap f hX j hx hδ

/-- Every constrained gap bound is equivalent to its feasible decrement inequalities. -/
theorem constrainedTaylorGap_le_iff (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsClosed X) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) (G : ℝ) :
    constrainedTaylorGap f X j x δ ≤ G ↔ ∀ d, x + d ∈ X → ‖d‖ ≤ δ →
      Chapter12.Section01.taylorDecrement f j x d ≤ G :=
  ConstrainedTaylorCriticality.taylorGap_le_iff f hX j hx hδ G

/-- The constrained gap is nonnegative because zero is a feasible displacement. -/
theorem constrainedTaylorGap_nonneg (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsClosed X) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ constrainedTaylorGap f X j x δ :=
  ConstrainedTaylorCriticality.taylorGap_nonneg f hX j hx hδ

/-- Removing the constraints recovers exactly the earlier Chapter 12 gap. -/
@[simp] theorem constrainedTaylorGap_univ (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    constrainedTaylorGap f univ j x δ = Chapter12.Section01.taylorCriticality f j δ x := by
  simp [constrainedTaylorGap, ConstrainedTaylorCriticality.taylorGap,
    ConstrainedTaylorCriticality.feasibleDisplacements, Chapter12.Section01.taylorCriticality]

/-- The supremum gap is the source objective minus an attained actual Taylor model minimum. -/
theorem exists_constrainedTaylorModel_minimum (f : EuclideanSpace ℝ (Fin n) → ℝ)
    {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsClosed X) (j : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ X) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ d, x + d ∈ X ∧ ‖d‖ ≤ δ ∧
      (∀ e, x + e ∈ X → ‖e‖ ≤ δ →
        Chapter01.Section03.taylorModel f j x d ≤ Chapter01.Section03.taylorModel f j x e) ∧
      constrainedTaylorGap f X j x δ = f x - Chapter01.Section03.taylorModel f j x d :=
  ConstrainedTaylorCriticality.exists_taylorModel_minimum f hX j hx hδ

/-- The constrained approximate order conditions use every order through `q`, positive
accuracies and radii at most one, and actual feasible Taylor gaps. -/
structure IsConstrainedApproxOrderMinimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (q : ℕ) (ε δ : ℕ → ℝ) : Prop where
  feasible : x ∈ X
  order_pos : 1 ≤ q
  epsilon_pos : ∀ j ∈ Finset.Icc 1 q, 0 < ε j
  epsilon_le_one : ∀ j ∈ Finset.Icc 1 q, ε j ≤ 1
  radius_pos : ∀ j ∈ Finset.Icc 1 q, 0 < δ j
  radius_le_one : ∀ j ∈ Finset.Icc 1 q, δ j ≤ 1
  gap_le : ∀ j ∈ Finset.Icc 1 q,
    constrainedTaylorGap f X j x (δ j) ≤ ε j * δ j ^ j / (j ! : ℝ)

/-- The bundled criterion is precisely feasibility and all source order inequalities. -/
theorem isConstrainedApproxOrderMinimizer_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {X : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    {q : ℕ} {ε δ : ℕ → ℝ} :
    IsConstrainedApproxOrderMinimizer f X x q ε δ ↔ x ∈ X ∧ 1 ≤ q ∧
      ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ ε j ≤ 1 ∧ 0 < δ j ∧ δ j ≤ 1 ∧
        constrainedTaylorGap f X j x (δ j) ≤ ε j * δ j ^ j / (j ! : ℝ) := by
  constructor
  · intro h
    exact ⟨h.feasible, h.order_pos, fun j hj => ⟨h.epsilon_pos j hj,
      h.epsilon_le_one j hj, h.radius_pos j hj, h.radius_le_one j hj, h.gap_le j hj⟩⟩
  · rintro ⟨hx, hq, h⟩
    exact ⟨hx, hq, fun j hj => (h j hj).1, fun j hj => (h j hj).2.1,
      fun j hj => (h j hj).2.2.1, fun j hj => (h j hj).2.2.2.1,
      fun j hj => (h j hj).2.2.2.2⟩

/-- Closed feasible sets convert the source inequalities to the canonical compact-gap
certificate. -/
theorem IsConstrainedApproxOrderMinimizer.toIsApproxMinimizer
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} {q : ℕ} {ε δ : ℕ → ℝ}
    (h : IsConstrainedApproxOrderMinimizer f X x q ε δ) (hX : IsClosed X) :
    TaylorCriticality.IsApproxMinimizer f x q ε δ
      (fun j => feasibleDisplacements X x ∩ closedBall 0 (δ j)) where
  epsilon_pos j hj hjq := h.epsilon_pos j (Finset.mem_Icc.mpr ⟨hj, hjq⟩)
  radius_pos j hj hjq := h.radius_pos j (Finset.mem_Icc.mpr ⟨hj, hjq⟩)
  compact j _ _ := ConstrainedTaylorCriticality.isCompact_feasibleDisplacements_inter_closedBall
    hX x (δ j)
  zero_mem j hj hjq := ConstrainedTaylorCriticality.zero_mem_feasibleBall h.feasible
    (h.radius_pos j (Finset.mem_Icc.mpr ⟨hj, hjq⟩)).le
  norm_le _ _ _ _ hd := by simpa using hd.2
  gap_le j hj hjq := h.gap_le j (Finset.mem_Icc.mpr ⟨hj, hjq⟩)

/-- The composite variant uses the earlier generalized decrement: `h` remains unchanged
inside the Taylor model of `f` and `c`, even when `h` is nonsmooth. -/
def constrainedCompositeTaylorGap (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) : ℝ :=
  TaylorCriticality.gapOn (Section01.compositeTaylorDecrement f c h j x)
    (feasibleDisplacements X x ∩ closedBall 0 δ)

/-- The constrained generalized composite conditions retain the exact composition `h`.
Each active order has its own positive accuracy and radius, as in Section 14.1. -/
def IsConstrainedCompositeApproxOrderMinimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (q : ℕ) (ε δ : ℕ → ℝ) : Prop :=
  x ∈ X ∧ ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ 0 < δ j ∧ δ j ≤ 1 ∧
    constrainedCompositeTaylorGap f c h X j x (δ j) ≤ ε j * δ j ^ j / (j ! : ℝ)

/-- Feasibility and the active-order inequalities characterize the composite criterion. -/
theorem isConstrainedCompositeApproxOrderMinimizer_iff
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {h : EuclideanSpace ℝ (Fin m) → ℝ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} {q : ℕ} {ε δ : ℕ → ℝ} :
    IsConstrainedCompositeApproxOrderMinimizer f c h X x q ε δ ↔
      x ∈ X ∧ ∀ j ∈ Finset.Icc 1 q, 0 < ε j ∧ 0 < δ j ∧ δ j ≤ 1 ∧
        constrainedCompositeTaylorGap f c h X j x (δ j) ≤ ε j * δ j ^ j / (j ! : ℝ) := Iff.rfl

/-- The feasible initial sublevel set (14.2.8). -/
abbrev feasibleSublevelSet (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (x₀ : EuclideanSpace ℝ (Fin n)) :=
  ConstrainedTaylorCriticality.feasibleSublevelSet f X x₀

/-- Assumptions f.D1rLaB.X and f.D0rLaB.X. Actual jets are bounded on the feasible initial
sublevel set and compared to every point in an open convex neighborhood containing `X`.
`includeValue = true` adds only the order-zero Lipschitz requirement in (14.2.9).
All source constants are normalized to be at least one. -/
structure SmoothBoundedJetsOnLevelSet (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (x₀ : EuclideanSpace ℝ (Fin n))
    (r : ℕ) (includeValue : Bool) (U : Set (EuclideanSpace ℝ (Fin n))) (L B : ℕ → ℝ) : Prop
    extends ConstrainedTaylorCriticality.HasAnchoredBoundedJets f r
      (feasibleSublevelSet f X x₀) U includeValue L B where
  initial_feasible : x₀ ∈ X
  feasible_subset : X ⊆ U
  lipschitz_one_le : ∀ j, (1 ≤ j ∨ includeValue = true) → j ≤ r → 1 ≤ L j
  bound_one_le : ∀ j, 1 ≤ j → j ≤ r → 1 ≤ B j

/-- Anchored level-set jets give actual sharp Taylor remainders from every model center. -/
theorem SmoothBoundedJetsOnLevelSet.remainder
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {X U : Set (EuclideanSpace ℝ (Fin n))}
    {x₀ x d : EuclideanSpace ℝ (Fin n)} {r j : ℕ} {includeValue : Bool} {L B : ℕ → ℝ}
    (hf : SmoothBoundedJetsOnLevelSet f X x₀ r includeValue U L B)
    (hj : 1 ≤ j) (hjr : j ≤ r) (hx : x ∈ feasibleSublevelSet f X x₀) (hxd : x + d ∈ U) :
    |f (x + d) - Chapter01.Section03.taylorModel f j x d| ≤
      L j / ((j + 1)! : ℝ) * ‖d‖ ^ (j + 1) :=
  hf.toHasAnchoredBoundedJets.remainder hj hjr hx hxd

/-- The seven simply constrained algorithm variants listed in Section 14.2. -/
inductive SimpleConstraintMethod where
  | ar | arIDA | arEDA | compositeAR | tr | trIDA | trEDA
  deriving DecidableEq

/-- The uniform complexity exponents from the table in Theorem 14.2.4. The duplicated and
conflicting AR rows in (14.2.12) are resolved using that table. Geometry is tested on the actual
feasible set and outer function; no convergence property is part of this definition. -/
def simpleConstraintExponent (method : SimpleConstraintMethod) (p q j : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin m) → ℝ) : ℝ := by
  classical
  exact match method with
  | .tr | .trIDA | .trEDA => q + 1
  | .ar | .arIDA | .arEDA =>
    if (q = 1 ∧ Convex ℝ X) ∨ (q = 2 ∧ X = univ) then
      (p + 1 : ℝ) / (p - j + 1 : ℕ) else (j : ℝ) * (p + 1) / p
  | .compositeAR =>
    if q = 1 ∧ Convex ℝ X ∧ ConvexOn ℝ univ h then
      (p + 1 : ℝ) / p else (j : ℝ) + 1

/-- The separate per-order decrease convention in (14.2.12) uses `j + 1` for TR, whereas
the uniform worst-order complexity table uses `q + 1`. This definition asserts no decrease. -/
def simpleConstraintDecreaseExponent (method : SimpleConstraintMethod) (p q j : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin m) → ℝ) : ℝ :=
  match method with
  | .tr | .trIDA | .trEDA => j + 1
  | _ => simpleConstraintExponent method p q j X h

/-- The source sparsity constraint (14.2.14), with the actual number of nonzero coordinates.
The budget is natural; the source additionally restricts it to at most the dimension. -/
def SparseFeasibleSet (nnz : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (fun i => x i) ∈ SparseConstraints.sparseSet nnz}

/-- Sparse feasibility means precisely the coordinate support cardinality bound. -/
@[simp] theorem mem_SparseFeasibleSet {nnz : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ SparseFeasibleSet nnz ↔ (SparseConstraints.supportIndices (fun i => x i)).card ≤ nnz :=
  Iff.rfl

/-- The sparsity feasible set is closed without any convexity assumption. -/
theorem isClosed_SparseFeasibleSet (nnz : ℕ) : IsClosed (SparseFeasibleSet (n := n) nnz) :=
  (SparseConstraints.isClosed_sparseSet nnz).preimage (by fun_prop)

/-- Sparsity sets are nonempty, including zero budget and zero-dimensional spaces. -/
theorem SparseFeasibleSet_nonempty (nnz : ℕ) : (SparseFeasibleSet (n := n) nnz).Nonempty :=
  ⟨0, SparseConstraints.zero_mem_sparseSet nnz⟩

/-- The mandatory coordinate indices in (14.2.20), using a strict radius inequality. -/
abbrev mandatoryIndices (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) : Finset (Fin n) :=
  SparseConstraints.mandatoryIndices (fun i => x i) δ

/-- The finite optional support choices in (14.2.21). -/
abbrev optionalSupports (x : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (nnz : ℕ) :=
  SparseConstraints.optionalSupports (fun i => x i) δ nnz

/-- The objective weights of the finite binary maximization problem (14.2.21). -/
abbrev optionalWeight (x g : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (i : Fin n) : ℝ :=
  SparseConstraints.optionalWeight (fun i => x i) (fun i => g i) δ i

/-- Theorem 14.2.1: constrained gap stability with additive error `η`. Positive local
Lipschitz constants give the stated smaller radius and coefficient two; a zero constant gives
coefficient one throughout the original radius. Closedness supplies compact feasible balls,
while the earlier Chapter 12 local derivative assumption supplies the actual Taylor remainder. -/
theorem theorem_14_2_1 {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {X : Set (EuclideanSpace ℝ (Fin n))} {j : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    {ε δ R L η : ℝ} (hX : IsClosed X) (_hx : x ∈ X) (hj : 1 ≤ j)
    (hf : ContDiff ℝ j f) (hε : 0 < ε) (_hε₁ : ε ≤ 1) (hδ : 0 < δ) (_hδ₁ : δ ≤ 1)
    (hL : 0 ≤ L) (_hη : 0 ≤ η) (hR : δ < R)
    (hLip : Chapter12.Section01.derivativeLipschitzOnBall f j x R L)
    (hgap : constrainedTaylorGap f X j x δ ≤ ε * δ ^ j / (j ! : ℝ) + η) :
    (0 < L → ∀ d : EuclideanSpace ℝ (Fin n), x + d ∈ X →
      ‖d‖ ≤ min δ (((j + 1 : ℕ) : ℝ) * ε / L) →
        f x - 2 * ε * δ ^ j / (j ! : ℝ) - η ≤ f (x + d)) ∧
    (L = 0 → ∀ d : EuclideanSpace ℝ (Fin n), x + d ∈ X → ‖d‖ ≤ δ →
      f x - ε * δ ^ j / (j ! : ℝ) - η ≤ f (x + d)) := by
  have hc := ConstrainedTaylorCriticality.isCompact_feasibleDisplacements_inter_closedBall hX x δ
  constructor
  · intro hLp d hdX hdn
    have hdδ := (le_min_iff.mp hdn).1
    have hrem := hLip.remainder hj hf hL hR hδ.le hdδ
    have hs : L * ‖d‖ ≤ ((j + 1 : ℕ) : ℝ) * ε := by
      have := (le_div_iff₀ hLp).mp (le_min_iff.mp hdn).2
      nlinarith
    exact TaylorCriticality.value_lower_bound_of_gap_le hc
      ⟨hdX, by simpa using hdδ⟩ hε.le hdδ hgap hrem hs
  · intro hzero d hdX hdn
    have hrem := hLip.remainder hj hf hL hR hδ.le hdn
    rw [hzero, zero_div, zero_mul] at hrem
    have heq : f (x + d) = RegularizedTaylorModel.taylorModel f j x d :=
      sub_eq_zero.mp (abs_nonpos_iff.mp hrem)
    have h := TaylorCriticality.value_lower_bound_of_gap_le_of_zero_remainder hc
      ⟨hdX, by simpa using hdn⟩ hgap heq
    linarith

end CartisGouldToint.Chapter14.Section02
