import Numlib.Analysis.Calculus.SquaredNormJets
import Numlib.Optimization.TaylorOptimality
import Numlib.Optimization.Constrained
import Numlib.Optimization.MeasureDomination

/-!
# Feasible Taylor gaps and residual-scaled solver outputs

Feasible displacements retain the actual constraint set. Residual certificates use the
Taylor jets of the squared residual itself. Inner solver contracts describe a supplied finite
trace, legal steps, evaluation counts, and tolerances; they assert no existence of a solver.
The residual wrapper uses these output contracts to derive its finite logarithmic bound.
-/

noncomputable section
open Set Metric
open scoped InnerProductSpace
namespace Optimization.ConstrainedTaylorCriticality
open TaylorCriticality RegularizedTaylorModel

variable {E : Type*}

section Add
variable [Add E]

/-- Displacements that keep the translated point in the actual constraint set. -/
def feasibleDisplacements (X : Set E) (x : E) : Set E := {d | x + d ∈ X}

/-- Membership in the feasible displacement set is feasibility of the endpoint. -/
@[simp] theorem mem_feasibleDisplacements {X : Set E} {x d : E} :
    d ∈ feasibleDisplacements X x ↔ x + d ∈ X := Iff.rfl

end Add

section AddZero
variable [AddZeroClass E]

/-- Zero is a feasible displacement exactly at feasible points. -/
@[simp] theorem zero_mem_feasibleDisplacements {X : Set E} {x : E} :
    0 ∈ feasibleDisplacements X x ↔ x ∈ X := by simp [feasibleDisplacements]

end AddZero

section Topology
variable [TopologicalSpace E] [Add E] [ContinuousAdd E]

/-- Translating a closed feasible set gives a closed displacement set. -/
theorem isClosed_feasibleDisplacements {X : Set E} (hX : IsClosed X) (x : E) :
    IsClosed (feasibleDisplacements X x) := hX.preimage (continuous_const.add continuous_id)

end Topology

variable [NormedAddCommGroup E]

/-- A closed feasible displacement set intersected with a closed ball is compact in any
proper normed space, including finite-dimensional real spaces. -/
theorem isCompact_feasibleDisplacements_inter_closedBall [ProperSpace E]
    {X : Set E} (hX : IsClosed X) (x : E) (δ : ℝ) :
    IsCompact (feasibleDisplacements X x ∩ closedBall 0 δ) :=
  (isCompact_closedBall 0 δ).inter_left (isClosed_feasibleDisplacements hX x)

variable [NormedSpace ℝ E]

/-- The half squared norm objective associated with a residual map. -/
def squaredResidual {F : Type*} [NormedAddCommGroup F] (r : E → F) (x : E) : ℝ :=
  ‖r x‖ ^ 2 / 2

/-- A residual-scaled certificate either achieves the residual tolerance, or supplies
separately positive radii for all required actual squared-residual Taylor gaps. -/
def ResidualScaledCertificate {F : Type*} [NormedAddCommGroup F]
    (X : Set E) (r : E → F) (q : ℕ) (ε₀ : ℝ) (ε δ : ℕ → ℝ) (x : E) : Prop :=
  ‖r x‖ ≤ ε₀ ∨ ∀ j ∈ Finset.Icc 1 q, 0 < δ j ∧
    gapOn (taylorDecrement (squaredResidual r) j x)
      (feasibleDisplacements X x ∩ closedBall 0 (δ j)) ≤
        ε j * ‖r x‖ * δ j ^ j / (j.factorial : ℝ)

/-- The certificate's residual branch has no radius requirement and covers zero residuals. -/
theorem ResidualScaledCertificate.of_residual_le {F : Type*} [NormedAddCommGroup F]
    {X : Set E} {r : E → F} {q : ℕ} {ε₀ : ℝ} {ε δ : ℕ → ℝ} {x : E}
    (h : ‖r x‖ ≤ ε₀) : ResidualScaledCertificate X r q ε₀ ε δ x := Or.inl h

/-- Positive radii and the actual relative gap bounds introduce the nonzero-residual branch. -/
theorem ResidualScaledCertificate.of_gaps {F : Type*} [NormedAddCommGroup F]
    {X : Set E} {r : E → F} {q : ℕ} {ε₀ : ℝ} {ε δ : ℕ → ℝ} {x : E}
    (hδ : ∀ j ∈ Finset.Icc 1 q, 0 < δ j)
    (hgap : ∀ j ∈ Finset.Icc 1 q,
      gapOn (taylorDecrement (squaredResidual r) j x)
        (feasibleDisplacements X x ∩ closedBall 0 (δ j)) ≤
          ε j * ‖r x‖ * δ j ^ j / (j.factorial : ℝ)) :
    ResidualScaledCertificate X r q ε₀ ε δ x :=
  Or.inr (fun j hj => ⟨hδ j hj, hgap j hj⟩)

/-- Above the residual tolerance, a certificate gives every radius and every gap test. -/
theorem ResidualScaledCertificate.gap {F : Type*} [NormedAddCommGroup F]
    {X : Set E} {r : E → F} {q : ℕ} {ε₀ : ℝ} {ε δ : ℕ → ℝ} {x : E}
    (h : ResidualScaledCertificate X r q ε₀ ε δ x) (hr : ε₀ < ‖r x‖)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 q) : 0 < δ j ∧
      gapOn (taylorDecrement (squaredResidual r) j x)
        (feasibleDisplacements X x ∩ closedBall 0 (δ j)) ≤
          ε j * ‖r x‖ * δ j ^ j / (j.factorial : ℝ) :=
  h.resolve_left (not_le.mpr hr) j hj

/-- Output contract for a supplied finite inner-solver trace. `step` specifies its actual
legal transitions and `evaluations` records function and derivative evaluations. Every cost
keeps its own additive and decrease coefficients; the tolerance exponents are strictly above
one. No solver, trace, or output point is postulated to exist by this definition. -/
structure InnerSolverContract {F : Type*} [NormedAddCommGroup F]
    (X : Set E) (r : E → F) (q : ℕ) (τ δ π : ℕ → ℝ)
    (step : E → E → Prop) (trace : ℕ → E) (N : ℕ)
    (evaluations : Fin (q + 1) → ℕ) (additive coefficient : Fin (q + 1) → ℝ) : Prop where
  feasible : ∀ k ≤ N, trace k ∈ X
  legal : ∀ k < N, step (trace k) (trace (k + 1))
  residual_nonincrease : ‖r (trace N)‖ ≤ ‖r (trace 0)‖
  tolerance_pos : ∀ j ∈ Finset.Icc 1 q, 0 < τ j
  radius_pos : ∀ j ∈ Finset.Icc 1 q, 0 < δ j
  exponent_gt_one : ∀ j ∈ Finset.Icc 1 q, 1 < π j
  gap : ∀ j ∈ Finset.Icc 1 q,
    gapOn (taylorDecrement (squaredResidual r) j (trace N))
      (feasibleDisplacements X (trace N) ∩ closedBall 0 (δ j)) ≤
        τ j * δ j ^ j / (j.factorial : ℝ)
  additive_nonneg : ∀ i, 0 ≤ additive i
  coefficient_nonneg : ∀ i, 0 ≤ coefficient i
  cost : ∀ i, (evaluations i : ℝ) ≤ additive i + coefficient i *
    (squaredResidual r (trace 0) - squaredResidual r (trace N)) *
      ∑ j ∈ Finset.Icc 1 q, (τ j) ^ (-π j)

/-- The signed Lagrangian for a vector-valued constraint, with convention `f - ⟪y,c⟫`. -/
def residualLagrangian {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : E → ℝ) (c : E → F) (y : F) (x : E) : ℝ := f x - ⟪y, c x⟫_ℝ

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- For finite Euclidean constraints, the signed residual Lagrangian is the existing
coordinate Lagrangian with negated multipliers. -/
theorem residualLagrangian_eq_lagrangian {ι : Type*} [Fintype ι] (f : E → ℝ)
    (c : E → EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ ι) (x : E) :
    residualLagrangian f c y x =
      Constrained.lagrangian f (fun i z => c z i) x (fun i => -y i) := by
  simp [residualLagrangian, Constrained.lagrangian, PiLp.inner_apply, sub_eq_add_neg,
    Finset.sum_neg_distrib, mul_comm]

/-- A Lagrangian Taylor-gap bound transfers to the objective with the exact norm of the
constraint change. The Lagrangian remainder and its small-displacement condition are explicit. -/
theorem lagrangian_value_stability_exact {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : E → ℝ} {c : E → F} {y : F} {x d : E} {p : ℕ}
    {D : Set E} {L ε δ η : ℝ} (hD : IsCompact D) (hd : d ∈ D)
    (hε : 0 ≤ ε) (hdn : ‖d‖ ≤ δ)
    (hgap : gapOn (taylorDecrement (residualLagrangian f c y) p x) D ≤
      ε * δ ^ p / (p.factorial : ℝ) + η)
    (hrem : |residualLagrangian f c y (x + d) -
      taylorModel (residualLagrangian f c y) p x d| ≤
        L / ((p + 1).factorial : ℝ) * ‖d‖ ^ (p + 1))
    (hsmall : L * ‖d‖ ≤ ((p + 1 : ℕ) : ℝ) * ε) :
    f x - ‖y‖ * ‖c (x + d) - c x‖ - 2 * ε * δ ^ p / (p.factorial : ℝ) - η ≤
      f (x + d) := by
  have h := value_lower_bound_of_gap_le hD hd hε hdn hgap hrem hsmall
  have hi := (abs_le.mp (abs_real_inner_le_norm y (c (x + d) - c x))).1
  simp only [inner_sub_right, residualLagrangian] at h hi
  linarith

/-- Approximate feasibility at both endpoints bounds the constraint-change penalty by
`2 ε₀ ‖y‖`. The displacement set may be any compact subset of the feasible displacements. -/
theorem lagrangian_value_stability {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : E → ℝ} {c : E → F} {y : F} {x d : E} {p : ℕ}
    {D : Set E} {L ε ε₀ δ η : ℝ} (hD : IsCompact D) (hd : d ∈ D)
    (hε : 0 ≤ ε) (hdn : ‖d‖ ≤ δ) (hx : ‖c x‖ ≤ ε₀) (hxd : ‖c (x + d)‖ ≤ ε₀)
    (hgap : gapOn (taylorDecrement (residualLagrangian f c y) p x) D ≤
      ε * δ ^ p / (p.factorial : ℝ) + η)
    (hrem : |residualLagrangian f c y (x + d) -
      taylorModel (residualLagrangian f c y) p x d| ≤
        L / ((p + 1).factorial : ℝ) * ‖d‖ ^ (p + 1))
    (hsmall : L * ‖d‖ ≤ ((p + 1 : ℕ) : ℝ) * ε) :
    f x - 2 * ε₀ * ‖y‖ - 2 * ε * δ ^ p / (p.factorial : ℝ) - η ≤ f (x + d) := by
  have h := lagrangian_value_stability_exact hD hd hε hdn hgap hrem hsmall
  have hc : ‖c (x + d) - c x‖ ≤ 2 * ε₀ := by
    have := norm_sub_le (c (x + d)) (c x)
    linarith
  have hy := mul_le_mul_of_nonneg_left hc (norm_nonneg y)
  nlinarith only [h, hy]

/-- With the same constraint residual at the two endpoints, no multiplier penalty is needed. -/
theorem lagrangian_value_stability_of_same_residual {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : E → ℝ} {c : E → F} {y : F} {x d : E} {p : ℕ}
    {D : Set E} {L ε δ η : ℝ} (hD : IsCompact D) (hd : d ∈ D)
    (hε : 0 ≤ ε) (hdn : ‖d‖ ≤ δ) (hc : c (x + d) = c x)
    (hgap : gapOn (taylorDecrement (residualLagrangian f c y) p x) D ≤
      ε * δ ^ p / (p.factorial : ℝ) + η)
    (hrem : |residualLagrangian f c y (x + d) -
      taylorModel (residualLagrangian f c y) p x d| ≤
        L / ((p + 1).factorial : ℝ) * ‖d‖ ^ (p + 1))
    (hsmall : L * ‖d‖ ≤ ((p + 1 : ℕ) : ℝ) * ε) :
    f x - 2 * ε * δ ^ p / (p.factorial : ℝ) - η ≤ f (x + d) := by
  simpa only [hc, sub_self, norm_zero, mul_zero, sub_zero] using
    lagrangian_value_stability_exact hD hd hε hdn hgap hrem hsmall

/-- A solve with tolerances scaled by the previous residual either supplies the relative
certificate at its output, or strictly contracts the residual. This implication uses actual
Taylor gaps and their own positive radii. -/
theorem certificate_or_residual_contraction {F : Type*} [NormedAddCommGroup F]
    {X : Set E} {r : E → F} {q : ℕ} {ε₀ β : ℝ} {ε δ : ℕ → ℝ} {x z : E}
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j)
    (hδ : ∀ j ∈ Finset.Icc 1 q, 0 < δ j)
    (hgap : ∀ j ∈ Finset.Icc 1 q,
      gapOn (taylorDecrement (squaredResidual r) j z)
        (feasibleDisplacements X z ∩ closedBall 0 (δ j)) ≤
          (β * ‖r x‖ * ε j) * δ j ^ j / (j.factorial : ℝ)) :
    ResidualScaledCertificate X r q ε₀ ε δ z ∨ ‖r z‖ < β * ‖r x‖ := by
  by_cases hr : ‖r z‖ < β * ‖r x‖
  · exact Or.inr hr
  left
  refine Or.inr (fun j hj => ⟨hδ j hj, (hgap j hj).trans ?_⟩)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_right (le_of_not_gt hr) (hε j hj)
  have hh' := mul_le_mul_of_nonneg_right hh (pow_nonneg (hδ j hj).le j)
  nlinarith only [hh']

/-- A wrapper supplied with scaled-gap output guarantees reaches a residual certificate by
its logarithmic ceiling count. If the initial residual is small the count is zero. The
hypothesis is needed only while the current iterate has not already certified termination. -/
theorem residual_wrapper_terminates_of_scaled_gaps {F : Type*} [NormedAddCommGroup F]
    {X : Set E} {r : E → F} {q : ℕ} {ε₀ β : ℝ} {ε : ℕ → ℝ}
    {δ : ℕ → ℕ → ℝ} {z : ℕ → E} (hε₀ : 0 < ε₀) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j)
    (hsolve : ∀ k, ¬ResidualScaledCertificate X r q ε₀ ε (δ k) (z k) →
      (∀ j ∈ Finset.Icc 1 q, 0 < δ (k + 1) j) ∧
      (∀ j ∈ Finset.Icc 1 q,
        gapOn (taylorDecrement (squaredResidual r) j (z (k + 1)))
          (feasibleDisplacements X (z (k + 1)) ∩ closedBall 0 (δ (k + 1) j)) ≤
            (β * ‖r (z k)‖ * ε j) * δ (k + 1) j ^ j / (j.factorial : ℝ))) :
    ∃ k ≤ MeasureDomination.geometricIterationCount ‖r (z 0)‖ β⁻¹ ε₀,
      ResidualScaledCertificate X r q ε₀ ε (δ k) (z k) := by
  classical
  let N := MeasureDomination.geometricIterationCount ‖r (z 0)‖ β⁻¹ ε₀
  by_contra hnone
  have hn : ∀ k ≤ N, ¬ResidualScaledCertificate X r q ε₀ ε (δ k) (z k) := by
    simpa only [not_exists, not_and] using hnone
  have hbound : ∀ k ≤ N, ‖r (z k)‖ ≤ ‖r (z 0)‖ * β ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hkN : k ≤ N := by omega
      obtain ⟨hrad, hgap⟩ := hsolve k (hn k hkN)
      have hcont := certificate_or_residual_contraction (ε₀ := ε₀) hε hrad hgap
      have hr := hcont.resolve_left (hn (k + 1) hk)
      calc
        ‖r (z (k + 1))‖ ≤ β * ‖r (z k)‖ := hr.le
        _ ≤ β * (‖r (z 0)‖ * β ^ k) :=
          mul_le_mul_of_nonneg_left (ih hkN) hβ₀.le
        _ = ‖r (z 0)‖ * β ^ (k + 1) := by ring
  have hbase : 1 < β⁻¹ := (one_lt_inv₀ hβ₀).mpr hβ₁
  have ht : ‖r (z 0)‖ * β ^ N ≤ ε₀ := by
    apply MeasureDomination.geometric_tolerance
      (u := fun k => ‖r (z 0)‖ * β ^ k) (v := ‖r (z 0)‖) (k := N)
      hbase hε₀ (fun k => ?_) le_rfl
    simp only [inv_pow, div_eq_mul_inv, inv_inv, le_refl]
  exact hn N le_rfl (Or.inl ((hbound N le_rfl).trans ht))

/-- An actual collection of finite inner traces satisfying their explicit output and cost
contracts makes the residual wrapper terminate within the logarithmic ceiling. The traces'
initial and final points are tied to consecutive outer iterates. The theorem assumes these
real solver contracts while needed; it does not construct an unspecified solver. -/
theorem residual_wrapper_terminates {F : Type*} [NormedAddCommGroup F]
    {X : Set E} {r : E → F} {q : ℕ} {ε₀ β : ℝ} {ε π : ℕ → ℝ}
    {δ : ℕ → ℕ → ℝ} {z : ℕ → E} {step : E → E → Prop}
    {trace : ℕ → ℕ → E} {N : ℕ → ℕ} {evaluations : ℕ → Fin (q + 1) → ℕ}
    {additive coefficient : Fin (q + 1) → ℝ}
    (hε₀ : 0 < ε₀) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hε : ∀ j ∈ Finset.Icc 1 q, 0 ≤ ε j)
    (hstart : ∀ k, trace k 0 = z k) (hend : ∀ k, trace k (N k) = z (k + 1))
    (hsolve : ∀ k, ¬ResidualScaledCertificate X r q ε₀ ε (δ k) (z k) →
      InnerSolverContract X r q (fun j => β * ‖r (trace k 0)‖ * ε j) (δ (k + 1)) π
        step (trace k) (N k) (evaluations k) additive coefficient) :
    ∃ k ≤ MeasureDomination.geometricIterationCount ‖r (z 0)‖ β⁻¹ ε₀,
      ResidualScaledCertificate X r q ε₀ ε (δ k) (z k) := by
  apply residual_wrapper_terminates_of_scaled_gaps hε₀ hβ₀ hβ₁ hε
  intro k hk
  have hs := hsolve k hk
  refine ⟨hs.radius_pos, ?_⟩
  simpa only [hend, hstart] using hs.gap

/-- Bounded and Lipschitz actual positive-order residual jets on an open convex domain.
The common bounds can always be enlarged to dominate finitely many order-specific bounds. -/
structure HasBoundedLipschitzJets {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : E → F) (p : ℕ) (U : Set E) (M L : ℝ) : Prop where
  isOpen : IsOpen U
  convex : Convex ℝ U
  contDiffOn : ContDiffOn ℝ p r U
  bound_nonneg : 0 ≤ M
  lipschitz_nonneg : 0 ≤ L
  bound : ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ U, ‖iteratedFDeriv ℝ j r x‖ ≤ M
  lipschitz : ∀ j ∈ Finset.Icc 1 p, ∀ x ∈ U, ∀ y ∈ U,
    ‖iteratedFDeriv ℝ j r y - iteratedFDeriv ℝ j r x‖ ≤ L * ‖y - x‖

/-- Exact all-order expansion of the squared-residual derivative. Ordered finite partitions
group every derivative argument correctly, retaining the symmetrization of the product rule. -/
theorem squaredResidual_iteratedFDeriv_eq_sum {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {r : E → F} {x : E} {j : ℕ}
    (hr : ContDiffAt ℝ j r x) :
    iteratedFDeriv ℝ j (squaredResidual r) x =
      ∑ c : OrderedFinpartition j,
        FormalMultilinearSeries.compAlongOrderedFinpartition
          (ftaylorSeries ℝ (SquaredNormJets.halfNormSq : F → ℝ) (r x))
          (ftaylorSeries ℝ r x) c :=
  SquaredNormJets.iteratedFDeriv_comp_eq_sum hr

/-- On a residual level set, all actual positive squared-residual jets are bounded and
Lipschitz with explicit constants affine in the level bound `R`. The comparison point in the
Lipschitz estimate ranges over the whole open convex domain. These conclusions hold at every
order through `p`; no formula for the desired derivatives is an assumption. -/
theorem squared_residual_jet_bounds {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {r : E → F} {p : ℕ} {U : Set E} {M L R : ℝ}
    (hr : HasBoundedLipschitzJets r p U M L) :
    ContDiffOn ℝ p (squaredResidual r) U ∧
      ∀ j ∈ Finset.Icc 1 p,
        (∀ x ∈ U, ‖r x‖ ≤ R →
          ‖iteratedFDeriv ℝ j (squaredResidual r) x‖ ≤
            (1 / 2 : ℝ) * (2 : ℝ) ^ j * M ^ 2 +
              ((1 / 2 : ℝ) * (2 : ℝ) ^ j * M) * R) ∧
        (∀ x ∈ U, ‖r x‖ ≤ R → ∀ y ∈ U,
          ‖iteratedFDeriv ℝ j (squaredResidual r) y -
            iteratedFDeriv ℝ j (squaredResidual r) x‖ ≤
              ((2 : ℝ) ^ j * M * (M + L) + L * R) * ‖y - x‖) := by
  constructor
  · exact (SquaredNormJets.contDiff_halfNormSq p).comp_contDiffOn hr.contDiffOn
  intro j hj
  have hjp : j ≤ p := (Finset.mem_Icc.mp hj).2
  have hj₁ : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjets (i : ℕ) (hi : i ∈ Finset.Icc 1 j) : i ∈ Finset.Icc 1 p :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans hjp⟩
  have hrj : ContDiffOn ℝ j r U := hr.contDiffOn.of_le (by exact_mod_cast hjp)
  constructor
  · intro x hx hRx
    have h := SquaredNormJets.norm_iteratedFDeriv_comp_le hj₁
      ((hrj x hx).contDiffAt (hr.isOpen.mem_nhds hx)) hRx hr.bound_nonneg
      (fun i hi => hr.bound i (hjets i hi) x hx)
    convert h using 1
    all_goals first | rfl | ring
  · intro x hx hRx y hy
    have h := SquaredNormJets.norm_iteratedFDeriv_comp_sub_le hj₁ hr.isOpen hr.convex
      hrj hx hy hRx hr.bound_nonneg hr.lipschitz_nonneg
      (fun i hi => hr.bound i (hjets i hi))
      (fun i hi => hr.lipschitz i (hjets i hi))
    convert h using 1
    all_goals first | rfl | ring

end Optimization.ConstrainedTaylorCriticality
