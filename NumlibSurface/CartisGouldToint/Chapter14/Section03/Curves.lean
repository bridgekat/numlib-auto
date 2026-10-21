import Numlib.Optimization.FeasibleCurveJets
import NumlibSurface.CartisGouldToint.Chapter14.Section03

/-!
# Chapter 14, Section 3: actual feasible curves

The descriptor in (14.3.2–3) retains an actual simple-set feasible path, its little-o
remainder, and all vanishing constraint coefficients. The necessary condition uses the
universal path-realization qualification AS.0 of the cited primary source [104],
Cartis–Gould–Toint, *Optimality of orders one to three and beyond*, Journal of Complexity
53 (2019), printed page 72, Theorem 2.2:
https://www.numerical.rl.ac.uk/media/people/nick-gould/CartGoulToin18_jc.pdf .

This explicitly corrects the supplied OCR's X.CqQ wording: mere nonemptiness of descriptor
jets does not ensure that a given jet has an equality-feasible realizing path. The
qualification below requires such a path for every admissible jet, as in AS.0. The
Lagrangian convention is the textbook's `f - ⟪y,c⟫`.
-/

noncomputable section
open Set Filter CurveTaylor Optimization
open scoped Topology
namespace CartisGouldToint.Chapter14.Section03
variable {n m : ℕ}

/-- Descriptor jets (14.3.2–3): actual simple-set paths and vanishing vector-valued
constraint coefficients. Equality-feasible realization is the separate qualification below. -/
abbrev FeasibleCurveJet (X : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (j : ℕ) := FeasibleCurveJets.Jet X c x j

/-- The corrected X.CqQ qualification, using universal actual-path realization AS.0 in
the primary source [104]. The supplied OCR states only nonemptiness, which is weaker. -/
abbrev CurveQualification (X : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (q : ℕ) : Prop :=
  FeasibleCurveJets.Qualification X c x q

/-- The corrected qualification exposes actual equality-feasible paths with the same jet. -/
@[simp] theorem curveQualification_iff (X : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (q : ℕ) :
    CurveQualification X c x q ↔ ∀ j, 1 ≤ j → j ≤ q → (v : FeasibleCurveJet X c x j) →
      RealizableJet (FeasibleCurveJets.equalitySet X c) x j v.direction :=
  FeasibleCurveJets.qualification_iff X c x q

/-- Theorem 14.3.1 with the path-realization correction AS.0 from the cited primary
Theorem 2.2. At a feasible local minimum, every fixed multiplier and every admissible jet
satisfy the coefficient sign condition when all preceding Lagrangian coefficients vanish.
Smoothness is imposed on an open set containing the actual simple constraint set. -/
theorem theorem_14_3_1 {X U : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} {q : ℕ}
    (hU : IsOpen U) (hXU : X ⊆ U) (hf : ContDiffOn ℝ q f U) (hc : ContDiffOn ℝ q c U)
    (hx : x ∈ FeasibleCurveJets.equalitySet X c)
    (hmin : IsLocalMinOn f (FeasibleCurveJets.equalitySet X c) x)
    (hQ : CurveQualification X c x q) :
    c x = 0 ∧ ∀ (y : EuclideanSpace ℝ (Fin m)) (j : ℕ), 1 ≤ j → j ≤ q →
      (v : FeasibleCurveJet X c x j) →
      (∀ i, 1 ≤ i → i < j →
        coefficient (ConstrainedTaylorCriticality.residualLagrangian f c y) x i v.direction = 0) →
      0 ≤ coefficient (ConstrainedTaylorCriticality.residualLagrangian f c y) x j v.direction := by
  refine ⟨hx.2, fun y j hj hjq v hprev => ?_⟩
  exact FeasibleCurveJets.coefficient_nonneg hx.2 hmin hQ
    (hf.contDiffAt (hU.mem_nhds (hXU hx.1)))
    (hc.contDiffAt (hU.mem_nhds (hXU hx.1))) hj hjq v y hprev

end CartisGouldToint.Chapter14.Section03
