import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Numlib.Optimization.Unconstrained.Optimality
import Numlib.Optimization.Constrained.Optimality
import Numlib.Optimization.Constrained.Equality

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

/-- Equality LICQ: the actual vector-valued constraint Jacobian is surjective.
In finite dimensions this is equivalent to linear independence of the constraint gradients. -/
def equalityLICQ {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : E → F) (x : E) : Prop :=
  Function.Surjective (fderiv ℝ c x)

/-- The range formulation of equality LICQ. -/
theorem equalityLICQ_iff_range_eq_top {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : E → F} {x : E} : equalityLICQ c x ↔ (fderiv ℝ c x).range = ⊤ :=
  LinearMap.range_eq_top.symm

/-- **Theorem 1.1.3 (equality-constrained optimality).** Under equality LICQ,
a constrained local minimum has a stationary Lagrangian; with `C²` data the same
multiplier gives a nonnegative Lagrangian Hessian on the Jacobian kernel. Conversely,
stationarity, feasibility and strict positivity on its nonzero kernel directions imply
a strict constrained local minimum.

The unspecified source constraint qualification is specialized explicitly to LICQ.
The nonzero-direction restriction omitted in equation (1.1.15) is restored. Both
branches retain smoothness only on the stated open neighborhood of the feasible set. -/
theorem theorem_1_1_3 {n m : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : IsOpen S) (hfeasS : {z | c z = 0} ⊆ S) :
    (ContDiffOn ℝ 1 f S → ContDiffOn ℝ 1 c S → c x = 0 →
      IsLocalMinOn f {z | c z = 0} x → equalityLICQ c x →
      ∃ y : EuclideanSpace ℝ (Fin m),
        fderiv ℝ (fun z => lagrangian f c z y) x = 0 ∧ c x = 0 ∧
        (ContDiffOn ℝ 2 f S → ContDiffOn ℝ 2 c S →
          ∀ d, fderiv ℝ c x d = 0 →
            0 ≤ fderiv ℝ (fderiv ℝ (fun z => lagrangian f c z y)) x d d)) ∧
    (∀ y : EuclideanSpace ℝ (Fin m),
      ContDiffOn ℝ 2 f S → ContDiffOn ℝ 2 c S → c x = 0 →
      fderiv ℝ (fun z => lagrangian f c z y) x = 0 →
      (∀ d ≠ 0, fderiv ℝ c x d = 0 →
        0 < fderiv ℝ (fderiv ℝ (fun z => lagrangian f c z y)) x d d) →
      ∃ δ > 0, ∀ z, c z = 0 → dist z x < δ → z ≠ x → f x < f z) := by
  constructor
  · intro hf hc hx hmin hreg
    have hxS : x ∈ S := hfeasS hx
    have hrange := equalityLICQ_iff_range_eq_top.mp hreg
    obtain ⟨y,hstat⟩ := Constrained.exists_vector_multiplier hx hmin
      ((hf.contDiffAt (hS.mem_nhds hxS)).hasStrictFDerivAt (by norm_num))
      ((hc.contDiffAt (hS.mem_nhds hxS)).hasStrictFDerivAt (by norm_num)) hrange
    refine ⟨y,hstat,hx,?_⟩
    intro hf2 hc2 d hd
    exact Constrained.vector_lagrangian_hessian_nonneg hS hxS hf2 hc2 hx hmin
      hrange hstat hd
  · intro y hf hc hx hstat hpos
    exact Constrained.strict_local_min_of_vector_lagrangian hS (hfeasS hx)
      hf hc hx hstat hpos

end CartisGouldToint
