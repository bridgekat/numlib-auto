import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Unconstrained.Optimality
import Numlib.Optimization.Constrained.Optimality

/-!
# Cartis–Gould–Toint, Section 1.1: optimality conditions

The Lagrangian uses the source convention `f(x) − ⟪y,c(x)⟫`. Its derivative conditions
are expressed using the actual Fréchet derivatives and Euclidean inner products.
The source's strict second-order conditions (1.1.15),(1.1.18) require nonzero directions.
The converse in Theorem 1.1.2 requires a tangent-cone correction for general convex sets;
its original form is recorded as incorrect in the plan.
-/

namespace CartisGouldToint

/-- The Lagrangian with the minus multiplier convention of equation (1.1.1). -/
def lagrangian {E F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → ℝ) (c : E → F) (x : E) (y : F) : ℝ := f x - inner ℝ y (c x)

/-- The Lagrangian agrees with the objective at a feasible point. -/
@[simp]
theorem lagrangian_of_feasible {E F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → ℝ} {c : E → F} {x : E} (y : F) (hx : c x = 0) :
    lagrangian f c x y = f x := by simp [lagrangian, hx]

/-- **Theorem 1.1.1 (unconstrained optimality conditions).** At a local minimum,
the first derivative vanishes; for a `C²` objective its Hessian is positive semidefinite;
for a `C³` objective its third derivative vanishes along the Hessian kernel. Conversely,
a stationary point with positive definite Hessian is a strict local minimum.
The Hessian is the actual second Fréchet derivative, viewed as a bilinear form. -/
theorem theorem_1_1_1 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    (ContDiff ℝ 1 f → IsLocalMin f x → fderiv ℝ f x = 0) ∧
    (ContDiff ℝ 2 f → IsLocalMin f x →
      ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ f) x v v) ∧
    (ContDiff ℝ 3 f → IsLocalMin f x →
      ∀ v, fderiv ℝ (fderiv ℝ f) x v = 0 →
        iteratedFDeriv ℝ 3 f x (fun _ => v) = 0) ∧
    (ContDiff ℝ 2 f → fderiv ℝ f x = 0 →
      (∀ v ≠ 0, 0 < fderiv ℝ (fderiv ℝ f) x v v) →
        ∃ δ > 0, ∀ y ∈ Metric.ball x δ, y ≠ x → f x < f y) := by
  refine ⟨fun _ hmin => hmin.fderiv_eq_zero, ?_, ?_, ?_⟩
  · exact fun hf hmin => Descent.hessian_nonneg_of_isLocalMin hmin hf
  · intro hf hmin v hv
    exact Descent.third_apply_eq_zero_of_isLocalMin hmin hf v (by simp [hv])
  · exact Descent.strict_local_min_of_pos_hessian

/-- The feasible displacements at `x`, equation (1.1.7). These are actual
finite displacements within `C`, rather than tangent-cone directions. -/
def feasibleDisplacements {E : Type*} [Add E] (C : Set E) (x : E) : Set E :=
  {d | x + d ∈ C}

@[simp]
theorem mem_feasibleDisplacements {E : Type*} [Add E] {C : Set E} {x d : E} :
    d ∈ feasibleDisplacements C x ↔ x + d ∈ C := Iff.rfl

@[simp]
theorem zero_mem_feasibleDisplacements {E : Type*} [AddZeroClass E]
    {C : Set E} {x : E} : 0 ∈ feasibleDisplacements C x ↔ x ∈ C := by
  simp [feasibleDisplacements]

/-- **Theorem 1.1.2 (necessary conditions).** At a local minimum within a closed
convex set, the first directional derivative is nonnegative in every feasible
displacement; the second is nonnegative where the first vanishes; the third is
nonnegative where both lower derivatives vanish. Each branch uses only the corresponding
regularity on the stated open set containing `C`.

The printed sufficient converse with actual displacements is false for general closed
convex sets and is separately recorded as incorrect in the plan. It is not included in
this necessary-condition declaration. -/
theorem theorem_1_1_2 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {C S : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (_hclosed : IsClosed C) (hC : Convex ℝ C) (hS : IsOpen S) (hCS : C ⊆ S)
    (hx : x ∈ C) (hmin : IsLocalMinOn f C x) :
    (ContDiffOn ℝ 1 f S → ∀ d ∈ feasibleDisplacements C x, 0 ≤ fderiv ℝ f x d) ∧
    (ContDiffOn ℝ 2 f S → ∀ d ∈ feasibleDisplacements C x,
      fderiv ℝ f x d = 0 → 0 ≤ fderiv ℝ (fderiv ℝ f) x d d) ∧
    (ContDiffOn ℝ 3 f S → ∀ d ∈ feasibleDisplacements C x,
      fderiv ℝ f x d = 0 → fderiv ℝ (fderiv ℝ f) x d d = 0 →
        0 ≤ iteratedFDeriv ℝ 3 f x (fun _ => d)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hf d hd
    exact Constrained.first_order_nonneg hC hx (mem_feasibleDisplacements.mp hd)
      hmin hS hCS hf
  · intro hf d hd hfirst
    exact Constrained.second_order_nonneg hC hx (mem_feasibleDisplacements.mp hd)
      hmin hS hCS hf hfirst
  · intro hf d hd hfirst hsecond
    exact Constrained.third_order_nonneg hC hx (mem_feasibleDisplacements.mp hd)
      hmin hS hCS hf hfirst hsecond

end CartisGouldToint
