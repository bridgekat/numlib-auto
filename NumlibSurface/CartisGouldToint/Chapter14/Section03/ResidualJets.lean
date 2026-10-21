import NumlibSurface.CartisGouldToint.Chapter14.Section03
import NumlibSurface.CartisGouldToint.Chapter07.Section02.Targets
import Numlib.Optimization.TargetResidualJets
import Numlib.Optimization.TwoPhaseTargets

/-!
# Chapter 14, Section 3: two-phase objectives and actual residual jets

The residual and target objective reuse the earlier Chapter 7 definitions. Assumptions
on positive jets hold throughout open convex neighbourhoods of the constraint set;
objective bounds on the near-feasible tube are a separate condition. Constraint smoothness
is componentwise as in the source, and finite intersections supply common neighbourhoods.
Lemma 14.3.6 uses the intended `μ` in (14.3.63), where the printed formula has `ν`.
-/

noncomputable section
open Set Optimization Optimization.ConstrainedTaylorCriticality
namespace CartisGouldToint.Chapter14.Section03
variable {n m p : ℕ}

/-- The feasibility objective `ν` and target objective `μ` of (14.3.30), using the actual
Euclidean squared residuals and the earlier Chapter 7 target objective. -/
def twoPhaseResidualObjectives (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    (EuclideanSpace ℝ (Fin n) → ℝ) × (ℝ → EuclideanSpace ℝ (Fin n) → ℝ) :=
  (squaredResidual c, Chapter07.Section02.targetObjective f c)

/-- Projection to the actual feasibility squared norm. -/
@[simp] theorem twoPhaseResidualObjectives_fst (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    (twoPhaseResidualObjectives f c).1 = squaredResidual c := rfl

/-- Projection to the earlier source target objective. -/
@[simp] theorem twoPhaseResidualObjectives_snd (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    (twoPhaseResidualObjectives f c).2 = Chapter07.Section02.targetObjective f c := rfl

/-- The augmented Euclidean residual is the earlier source residual, with the objective
component last; its norm is not the maximum product norm. -/
abbrev twoPhaseResidual := @Chapter07.Section02.targetResidual n m

/-- The two-phase Lagrangian preserves the earlier source minus-sign convention. -/
abbrev twoPhaseLagrangian := @Chapter07.Section01.lagrangian n m

/-- Reset indices `K_a` in (14.3.36), among the first `N` outer transitions. Membership
requires the small-residual branch and its actual target update (14.3.33). -/
def twoPhaseResetIndices (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (θ ε₀ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun k =>
    ‖twoPhaseResidual f c (t k) (x (k + 1))‖ < θ * ε₀ ∧
      t (k + 1) = TwoPhaseTargets.resetTarget f c ε₀ (x (k + 1))

/-- Reset membership exposes the executed index, branch test and square-root update. -/
@[simp] theorem mem_twoPhaseResetIndices {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {θ ε₀ : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {t : ℕ → ℝ} {N k : ℕ} :
    k ∈ twoPhaseResetIndices f c θ ε₀ x t N ↔ k < N ∧
      ‖twoPhaseResidual f c (t k) (x (k + 1))‖ < θ * ε₀ ∧
        t (k + 1) = TwoPhaseTargets.resetTarget f c ε₀ (x (k + 1)) := by
  classical
  simp [twoPhaseResetIndices]

/-- Reflection indices `K_b` in (14.3.36), including the actual reflected target (14.3.35).
The remaining large-residual branch terminates instead of updating a target. -/
def twoPhaseReflectionIndices (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (θ ε₀ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun k =>
    θ * ε₀ ≤ ‖twoPhaseResidual f c (t k) (x (k + 1))‖ ∧
      f (x (k + 1)) < t k ∧ t (k + 1) = TwoPhaseTargets.reflectTarget f (t k) (x (k + 1))

/-- Reflection membership exposes the branch test, target crossing and reflection. -/
@[simp] theorem mem_twoPhaseReflectionIndices {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)} {θ ε₀ : ℝ}
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {t : ℕ → ℝ} {N k : ℕ} :
    k ∈ twoPhaseReflectionIndices f c θ ε₀ x t N ↔ k < N ∧
      θ * ε₀ ≤ ‖twoPhaseResidual f c (t k) (x (k + 1))‖ ∧
        f (x (k + 1)) < t k ∧
          t (k + 1) = TwoPhaseTargets.reflectTarget f (t k) (x (k + 1)) := by
  classical
  simp [twoPhaseReflectionIndices]

/-- The two target-update index classes are disjoint. -/
theorem disjoint_twoPhase_update_indices (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (θ ε₀ : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ) (N : ℕ) :
    Disjoint (twoPhaseResetIndices f c θ ε₀ x t N)
      (twoPhaseReflectionIndices f c θ ε₀ x t N) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k ha hb
  exact (not_lt_of_ge (mem_twoPhaseReflectionIndices.mp hb).2.1)
    (mem_twoPhaseResetIndices.mp ha).2.1

/-- The actual `f.D1pLB.X` assumption: all positive jets are bounded and Lipschitz
on some open convex neighbourhood of `X`, with no bound imposed on function values. -/
abbrev BoundedLipschitzJetsNearFeasibleSet (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  HasBoundedLipschitzJetsNear f p X

/-- The source `c.D1pLB.X` assumption is imposed on each scalar constraint component.
Separate component neighbourhoods are allowed; their finite intersection suffices. -/
def ComponentwiseBoundedLipschitzJetsNearFeasibleSet
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (p : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ i, BoundedLipschitzJetsNearFeasibleSet (fun x => c x i) p X

/-- Componentwise smoothness exposes exactly the scalar positive-jet assumptions. -/
@[simp] theorem componentwiseBoundedLipschitzJetsNearFeasibleSet_iff
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {X : Set (EuclideanSpace ℝ (Fin n))} :
    ComponentwiseBoundedLipschitzJetsNearFeasibleSet c p X ↔
      ∀ i, BoundedLipschitzJetsNearFeasibleSet (fun x => c x i) p X := Iff.rfl

/-- The independent `f.B.Fb` assumption, with the source near-feasible tube from Chapter 7.
It requires both objective bounds and is vacuous when the tube is empty. -/
def TwoPhaseTubeObjectiveBounds (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (X : Set (EuclideanSpace ℝ (Fin n))) (β low up : ℝ) : Prop :=
  ∀ x ∈ Chapter07.Section02.nearFeasibleSet X c β, low ≤ f x ∧ f x ≤ up

/-- Tube bounds provide exactly the two scalar inequalities at each near-feasible point. -/
@[simp] theorem twoPhaseTubeObjectiveBounds_iff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {X : Set (EuclideanSpace ℝ (Fin n))} {β low up : ℝ} :
    TwoPhaseTubeObjectiveBounds f c X β low up ↔
      ∀ x ∈ X, ‖c x‖ ≤ β → low ≤ f x ∧ f x ≤ up := by
  simp only [TwoPhaseTubeObjectiveBounds, Chapter07.Section02.mem_nearFeasibleSet]
  exact ⟨fun h x hx hc => h x ⟨hx, hc⟩, fun h x hx => h x hx.1 hx.2⟩

/-- The scalar components of the augmented residual before translating the final target. -/
def twoPhaseScalarComponents (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (i : Fin (m + 1)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Fin.snoc (α := fun _ => ℝ) (fun k => c x k) (f x) i

/-- The constraint coordinates of the scalar component family. -/
@[simp] theorem twoPhaseScalarComponents_castSucc (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    twoPhaseScalarComponents f c i.castSucc = fun x => c x i := by
  funext x
  simp [twoPhaseScalarComponents]

/-- The last scalar component is the objective. -/
@[simp] theorem twoPhaseScalarComponents_last (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    twoPhaseScalarComponents f c (Fin.last m) = f := by
  funext x
  simp [twoPhaseScalarComponents]

/-- The target objective is exactly the finite scalar squared-residual sum. -/
theorem twoPhase_target_eq_sum (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    (twoPhaseResidualObjectives f c).2 t = fun x =>
      ∑ i : Fin (m + 1), squaredResidual
        (fun z => twoPhaseScalarComponents f c i z -
          Fin.snoc (α := fun _ => ℝ) (fun _ : Fin m => 0) t i) x := by
  funext x
  simp only [twoPhaseResidualObjectives_snd, Chapter07.Section02.targetObjective,
    TargetLeastSquares.objective, squaredResidual, Fin.sum_univ_castSucc,
    twoPhaseScalarComponents, Fin.snoc_castSucc, Fin.snoc_last, sub_zero,
    ← Finset.sum_div, EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs, sq_abs]

/-- Lemma 14.3.6(i): genuine smoothness and affine-in-initial-residual bounds for `ν`.
The constants are selected before the initial point; comparison points range over the
whole open convex neighbourhood, including points outside the initial level set. -/
theorem lemma_14_3_6_constraint
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (hc : ComponentwiseBoundedLipschitzJetsNearFeasibleSet c p X) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin n))) (LA LB BA BB : ℕ → ℝ),
      X ⊆ U ∧ IsOpen U ∧ Convex ℝ U ∧ ContDiffOn ℝ p (squaredResidual c) U ∧
      (∀ j, 1 ≤ LA j ∧ 1 ≤ LB j ∧ 1 ≤ BA j ∧ 1 ≤ BB j) ∧
      ∀ x₀ ∈ X, ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ X, ‖c x‖ ≤ ‖c x₀‖ →
        ‖iteratedFDeriv ℝ j (squaredResidual c) x‖ ≤ BA j + BB j * ‖c x₀‖ ∧
        ∀ y ∈ U, ‖iteratedFDeriv ℝ j (squaredResidual c) y -
          iteratedFDeriv ℝ j (squaredResidual c) x‖ ≤
            (LA j + LB j * ‖c x₀‖) * ‖y - x‖ := by
  obtain ⟨U, LA, LB, BA, BB, hX, ho, hv, hconst, h⟩ :=
    finite_squared_residual_jet_bounds_near hc
  have hs := h (fun _ => 0)
  simp only [sub_zero] at hs
  rw [← squaredResidual_euclidean_eq_sum] at hs
  refine ⟨U, LA, LB, BA, BB, hX, ho, hv, hs.1, hconst, ?_⟩
  intro x₀ _hx₀ j hj x hx hlevel
  exact hs.2 j hj ‖c x₀‖ (norm_nonneg _) x (hX hx)
    (fun i => (PiLp.norm_apply_le (c x) i).trans hlevel)

/-- Lemma 14.3.6(ii): all actual target-objective jets are uniformly controlled at
augmented residual norm at most one. Both coefficient families are chosen before `t`.
This uses the intended `μ` in the printed norm bound (14.3.63). -/
theorem lemma_14_3_6_target
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (hc : ComponentwiseBoundedLipschitzJetsNearFeasibleSet c p X)
    (hf : BoundedLipschitzJetsNearFeasibleSet f p X) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin n))) (L B : ℕ → ℝ),
      X ⊆ U ∧ IsOpen U ∧ Convex ℝ U ∧ (∀ j, 1 ≤ L j ∧ 1 ≤ B j) ∧
      ∀ t : ℝ, ContDiffOn ℝ p ((twoPhaseResidualObjectives f c).2 t) U ∧
        ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ X, ‖twoPhaseResidual f c t x‖ ≤ 1 →
          ‖iteratedFDeriv ℝ j ((twoPhaseResidualObjectives f c).2 t) x‖ ≤ B j ∧
          ∀ y ∈ U, ‖iteratedFDeriv ℝ j ((twoPhaseResidualObjectives f c).2 t) y -
            iteratedFDeriv ℝ j ((twoPhaseResidualObjectives f c).2 t) x‖ ≤ L j * ‖y - x‖ := by
  have hr : ∀ i : Fin (m + 1),
      HasBoundedLipschitzJetsNear (twoPhaseScalarComponents f c i) p X := by
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa only [twoPhaseScalarComponents_last] using hf
    · simpa only [twoPhaseScalarComponents_castSucc] using hc k
  obtain ⟨U, LA, LB, BA, BB, hX, ho, hv, hconst, h⟩ :=
    finite_squared_residual_jet_bounds_near hr
  refine ⟨U, fun j => LA j + LB j, fun j => BA j + BB j, hX, ho, hv, ?_, ?_⟩
  · intro j
    obtain ⟨hla, hlb, hba, hbb⟩ := hconst j
    constructor <;> linarith
  · intro t
    have hs := h (Fin.snoc (α := fun _ => ℝ) (fun _ : Fin m => 0) t)
    rw [← twoPhase_target_eq_sum f c t] at hs
    refine ⟨hs.1, ?_⟩
    intro j hj x hx hlevel
    have hcomponent (i : Fin (m + 1)) :
        ‖twoPhaseScalarComponents f c i x -
          Fin.snoc (α := fun _ => ℝ) (fun _ : Fin m => 0) t i‖ ≤ 1 := by
      have heq : twoPhaseScalarComponents f c i x -
          Fin.snoc (α := fun _ => ℝ) (fun _ : Fin m => 0) t i =
          twoPhaseResidual f c t x i := by
        refine Fin.lastCases ?_ (fun k => ?_) i <;>
          simp [twoPhaseScalarComponents, twoPhaseResidual]
      rw [heq]
      exact (PiLp.norm_apply_le (twoPhaseResidual f c t x) i).trans hlevel
    simpa only [mul_one] using hs.2 j hj 1 zero_le_one x (hX hx) hcomponent

/-- Lemma 14.3.6: actual smoothness of both two-phase objectives. Part (i) has
coefficients affine in the initial constraint norm; part (ii) has constants uniform in
every real target. The norm bound in (14.3.63) is explicitly read as `μ`, not printed `ν`. -/
theorem lemma_14_3_6
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (hc : ComponentwiseBoundedLipschitzJetsNearFeasibleSet c p X)
    (hf : BoundedLipschitzJetsNearFeasibleSet f p X) :
    (∃ (U : Set (EuclideanSpace ℝ (Fin n))) (LA LB BA BB : ℕ → ℝ),
      X ⊆ U ∧ IsOpen U ∧ Convex ℝ U ∧ ContDiffOn ℝ p (squaredResidual c) U ∧
      (∀ j, 1 ≤ LA j ∧ 1 ≤ LB j ∧ 1 ≤ BA j ∧ 1 ≤ BB j) ∧
      ∀ x₀ ∈ X, ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ X, ‖c x‖ ≤ ‖c x₀‖ →
        ‖iteratedFDeriv ℝ j (squaredResidual c) x‖ ≤ BA j + BB j * ‖c x₀‖ ∧
        ∀ y ∈ U, ‖iteratedFDeriv ℝ j (squaredResidual c) y -
          iteratedFDeriv ℝ j (squaredResidual c) x‖ ≤
            (LA j + LB j * ‖c x₀‖) * ‖y - x‖) ∧
    (∃ (U : Set (EuclideanSpace ℝ (Fin n))) (L B : ℕ → ℝ),
      X ⊆ U ∧ IsOpen U ∧ Convex ℝ U ∧ (∀ j, 1 ≤ L j ∧ 1 ≤ B j) ∧
      ∀ t : ℝ, ContDiffOn ℝ p ((twoPhaseResidualObjectives f c).2 t) U ∧
        ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ X, ‖twoPhaseResidual f c t x‖ ≤ 1 →
          ‖iteratedFDeriv ℝ j ((twoPhaseResidualObjectives f c).2 t) x‖ ≤ B j ∧
          ∀ y ∈ U, ‖iteratedFDeriv ℝ j ((twoPhaseResidualObjectives f c).2 t) y -
            iteratedFDeriv ℝ j ((twoPhaseResidualObjectives f c).2 t) x‖ ≤ L j * ‖y - x‖) :=
  ⟨lemma_14_3_6_constraint hc, lemma_14_3_6_target hc hf⟩

end CartisGouldToint.Chapter14.Section03
