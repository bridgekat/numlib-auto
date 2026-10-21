import Numlib.Optimization.FeasibleCriticality
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Chapter 6, Section 1: convexly constrained optimality

The restricted sets in (6.1.8) and (6.1.10) contain no unit-ball restriction; the ball enters
only in the criticality minimizations. All measures use actual Fréchet derivatives. Orders are
indexed by `Fin 3`, with index `j` denoting derivative order `j.val + 1`.

The minus signs omitted by OCR in (6.1.5) and (6.1.9) are restored, consistently with
(6.2.3)–(6.2.5). Closed, convex, nonempty constraints alone do not imply existence of an
objective minimizer (take `f x = x` on the real line), so no such assertion is made here.
-/

noncomputable section
namespace CartisGouldToint.Chapter06.Section01
open Optimization.TaylorCriticality Optimization.FeasibleCriticality
variable {n : ℕ}

/-- Assumption C.CNe: the constraint set is closed, convex and nonempty. -/
structure ConvexConstraintAssumptions (C : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  isClosed : IsClosed C
  convex : Convex ℝ C
  nonempty : C.Nonempty

/-- The feasible steps `C(x)` of (6.1.2), without a bound on their lengths. -/
def feasibleSteps (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) := {d | x + d ∈ C}

@[simp] theorem mem_feasibleSteps {C : Set (EuclideanSpace ℝ (Fin n))}
    {x d : EuclideanSpace ℝ (Fin n)} : d ∈ feasibleSteps C x ↔ x + d ∈ C := Iff.rfl

@[simp] theorem zero_mem_feasibleSteps {C : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} : (0 : EuclideanSpace ℝ (Fin n)) ∈ feasibleSteps C x ↔
      x ∈ C := by simp [feasibleSteps]

/-- The ball `B` in (6.1.3) is the closed Euclidean unit ball. -/
def unitBall : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 1

@[simp] theorem mem_unitBall {d : EuclideanSpace ℝ (Fin n)} :
    d ∈ unitBall ↔ ‖d‖ ≤ 1 := by simp [unitBall]

/-- Bounded feasible steps agree with the reusable backbone domain. -/
theorem feasibleSteps_inter_unitBall (C : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    feasibleSteps C x ∩ unitBall = unitFeasibleSteps C x := by ext d; simp

/-- The actual `j+1`-st derivative evaluated repeatedly along a direction. -/
def directionalDerivative (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin 3) (d : EuclideanSpace ℝ (Fin n)) : ℝ :=
  iteratedFDeriv ℝ (j.val + 1) f x (fun _ => d)

/-- The first directional derivative is the continuous linear derivative. -/
@[simp] theorem directionalDerivative_first (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) :
    directionalDerivative f x 0 d = fderiv ℝ f x d := by
  simp [directionalDerivative, iteratedFDeriv_one_apply]

/-- Every positive-order derivative vanishes on the zero direction. -/
@[simp] theorem directionalDerivative_zero (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin 3) : directionalDerivative f x j 0 = 0 := by
  exact (iteratedFDeriv ℝ (j.val + 1) f x).toMultilinearMap.map_coord_zero 0 rfl

/-- Directional evaluation of each derivative tensor is continuous in the direction. -/
theorem continuous_directionalDerivative (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin 3) : Continuous (directionalDerivative f x j) :=
  (iteratedFDeriv ℝ (j.val + 1) f x).cont.comp (continuous_pi fun _ => continuous_id)

/-- The feasible sets for orders one, two and three: `C(x)`, `C¹(x,α₁)` and
`C²(x,α₁,α₂)` of (6.1.2), (6.1.8) and (6.1.10). The thresholds remain explicit. -/
def restrictedFeasibleSteps (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (tau alpha : Fin 2 → ℝ) (j : Fin 3) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | d ∈ feasibleSteps C x ∧
    (1 ≤ j.val → |directionalDerivative f x 0 d| ≤ tau 0 * alpha 0) ∧
    (2 ≤ j.val → |directionalDerivative f x 1 d| ≤ tau 1 * alpha 1)}

@[simp] theorem mem_restrictedFeasibleSteps (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (x d : EuclideanSpace ℝ (Fin n))
    (tau alpha : Fin 2 → ℝ) (j : Fin 3) :
    d ∈ restrictedFeasibleSteps f C x tau alpha j ↔ d ∈ feasibleSteps C x ∧
      (1 ≤ j.val → |directionalDerivative f x 0 d| ≤ tau 0 * alpha 0) ∧
      (2 ≤ j.val → |directionalDerivative f x 1 d| ≤ tau 1 * alpha 1) := Iff.rfl

/-- The first-order domain has no restrictions on directional derivatives. -/
@[simp] theorem restrictedFeasibleSteps_first (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (tau alpha : Fin 2 → ℝ) : restrictedFeasibleSteps f C x tau alpha 0 = feasibleSteps C x := by
  ext d; simp

/-- The first restricted domain is precisely (6.1.8). -/
@[simp] theorem mem_restrictedFeasibleSteps_second (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (x d : EuclideanSpace ℝ (Fin n))
    (tau alpha : Fin 2 → ℝ) :
    d ∈ restrictedFeasibleSteps f C x tau alpha 1 ↔
      x + d ∈ C ∧ |fderiv ℝ f x d| ≤ tau 0 * alpha 0 := by simp

/-- The second restricted domain is precisely (6.1.10). -/
@[simp] theorem mem_restrictedFeasibleSteps_third (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (x d : EuclideanSpace ℝ (Fin n))
    (tau alpha : Fin 2 → ℝ) :
    d ∈ restrictedFeasibleSteps f C x tau alpha 2 ↔ x + d ∈ C ∧
      |fderiv ℝ f x d| ≤ tau 0 * alpha 0 ∧
      |iteratedFDeriv ℝ 2 f x (fun _ => d)| ≤ tau 1 * alpha 1 := by
  simp [directionalDerivative, iteratedFDeriv_one_apply]

/-- The bounded restricted domains are compact for closed constraints. -/
theorem isCompact_restrictedFeasibleSteps_inter_unitBall
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsClosed C) (x : EuclideanSpace ℝ (Fin n)) (tau alpha : Fin 2 → ℝ) (j : Fin 3) :
    IsCompact (restrictedFeasibleSteps f C x tau alpha j ∩ unitBall) := by
  have hc : IsClosed (feasibleSteps C x) := hC.preimage (continuous_const.add continuous_id)
  have h1 := isClosed_le (continuous_directionalDerivative f x 0).abs
    (continuous_const (y := tau 0 * alpha 0))
  have h2 := isClosed_le (continuous_directionalDerivative f x 1).abs
    (continuous_const (y := tau 1 * alpha 1))
  have hr : IsClosed (restrictedFeasibleSteps f C x tau alpha j) := by
    by_cases hj1 : 1 ≤ j.val <;> by_cases hj2 : 2 ≤ j.val
    · convert hc.inter (h1.inter h2) using 1
      ext d
      simp [restrictedFeasibleSteps, feasibleSteps, hj1, hj2]
    · convert hc.inter h1 using 1
      ext d
      simp [restrictedFeasibleSteps, feasibleSteps, hj1, hj2]
    · convert hc.inter h2 using 1
      ext d
      simp [restrictedFeasibleSteps, feasibleSteps, hj1, hj2]
    · convert hc using 1
      ext d
      simp [restrictedFeasibleSteps, feasibleSteps, hj1, hj2]
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).inter_left hr

/-- Zero belongs to every restricted unit domain when the thresholds are nonnegative. -/
theorem zero_mem_restrictedFeasibleSteps_inter_unitBall
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C) (tau alpha : Fin 2 → ℝ) (j : Fin 3)
    (ht : ∀ i : Fin 2, i.val + 1 ≤ j.val → 0 ≤ tau i * alpha i) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ restrictedFeasibleSteps f C x tau alpha j ∩ unitBall := by
  simp only [Set.mem_inter_iff, mem_restrictedFeasibleSteps, zero_mem_feasibleSteps,
    directionalDerivative_zero, abs_zero, mem_unitBall, norm_zero]
  exact ⟨⟨hx, fun h => ht 0 h, fun h => ht 1 h⟩, zero_le_one⟩

/-- The three measures (6.1.5), (6.1.7), (6.1.9), as maximal negative derivative values.
The compactness and attainment theorems below identify them with negative minima. -/
def constrainedCriticality (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (tau alpha : Fin 2 → ℝ) (j : Fin 3) : ℝ :=
  gapOn (fun d => -directionalDerivative f x j d)
    (restrictedFeasibleSteps f C x tau alpha j ∩ unitBall)

/-- The first measure is the reusable linear feasible-step criticality. -/
@[simp] theorem constrainedCriticality_first (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (tau alpha : Fin 2 → ℝ) : constrainedCriticality f C x tau alpha 0 =
      feasibleCriticality C x (fderiv ℝ f x) := by
  simp [constrainedCriticality, feasibleCriticality, feasibleSteps_inter_unitBall]

/-- Every measure is nonnegative at a feasible point with nonnegative thresholds. -/
theorem constrainedCriticality_nonneg
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsClosed C) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C)
    (tau alpha : Fin 2 → ℝ) (j : Fin 3)
    (ht : ∀ i : Fin 2, i.val + 1 ≤ j.val → 0 ≤ tau i * alpha i) :
    0 ≤ constrainedCriticality f C x tau alpha j :=
  gapOn_nonneg (isCompact_restrictedFeasibleSteps_inter_unitBall f hC x tau alpha j)
    (continuous_directionalDerivative f x j).neg.continuousOn
    (zero_mem_restrictedFeasibleSteps_inter_unitBall f hx tau alpha j ht) (by simp)

/-- Each criticality measure is the negative of an attained minimum of its actual derivative. -/
theorem exists_minimizer_constrainedCriticality
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsClosed C) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C)
    (tau alpha : Fin 2 → ℝ) (j : Fin 3)
    (ht : ∀ i : Fin 2, i.val + 1 ≤ j.val → 0 ≤ tau i * alpha i) :
    ∃ d ∈ restrictedFeasibleSteps f C x tau alpha j ∩ unitBall,
      directionalDerivative f x j d = -constrainedCriticality f C x tau alpha j ∧
      IsLeast (directionalDerivative f x j ''
        (restrictedFeasibleSteps f C x tau alpha j ∩ unitBall))
        (directionalDerivative f x j d) := by
  have hc := isCompact_restrictedFeasibleSteps_inter_unitBall f hC x tau alpha j
  have h0 := zero_mem_restrictedFeasibleSteps_inter_unitBall f hx tau alpha j ht
  have hcont : ContinuousOn (fun d => -directionalDerivative f x j d)
      (restrictedFeasibleSteps f C x tau alpha j ∩ unitBall) :=
    (continuous_directionalDerivative f x j).neg.continuousOn
  obtain ⟨d, hd, heq⟩ := exists_eq_gapOn hc ⟨0, h0⟩ hcont
  change -directionalDerivative f x j d = constrainedCriticality f C x tau alpha j at heq
  refine ⟨d, hd, by linarith, Set.mem_image_of_mem _ hd, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have hb := le_gapOn hc hcont he
  change -directionalDerivative f x j e ≤ constrainedCriticality f C x tau alpha j at hb
  linarith

/-- Equivalence with the source's negative-minimum convention. -/
theorem constrainedCriticality_eq_neg_sInf
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsClosed C) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C)
    (tau alpha : Fin 2 → ℝ) (j : Fin 3)
    (ht : ∀ i : Fin 2, i.val + 1 ≤ j.val → 0 ≤ tau i * alpha i) :
    constrainedCriticality f C x tau alpha j =
      -sInf (directionalDerivative f x j ''
        (restrictedFeasibleSteps f C x tau alpha j ∩ unitBall)) := by
  obtain ⟨d, _, heq, hmin⟩ := exists_minimizer_constrainedCriticality f hC hx tau alpha j ht
  rw [hmin.csInf_eq]
  linarith

/-- A criticality tolerance bounds exactly all negative directional derivative values. -/
theorem constrainedCriticality_le_iff
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsClosed C) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C)
    (tau alpha : Fin 2 → ℝ) (j : Fin 3)
    (ht : ∀ i : Fin 2, i.val + 1 ≤ j.val → 0 ≤ tau i * alpha i) {c : ℝ} :
    constrainedCriticality f C x tau alpha j ≤ c ↔
      ∀ d ∈ restrictedFeasibleSteps f C x tau alpha j ∩ unitBall,
        -directionalDerivative f x j d ≤ c := by
  exact gapOn_le_iff (isCompact_restrictedFeasibleSteps_inter_unitBall f hC x tau alpha j)
    ⟨0, zero_mem_restrictedFeasibleSteps_inter_unitBall f hx tau alpha j ht⟩
    (continuous_directionalDerivative f x j).neg.continuousOn

/-- Zero criticality means all directional derivatives on the restricted domain are nonnegative. -/
theorem constrainedCriticality_eq_zero_iff
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsClosed C) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C)
    (tau alpha : Fin 2 → ℝ) (j : Fin 3)
    (ht : ∀ i : Fin 2, i.val + 1 ≤ j.val → 0 ≤ tau i * alpha i) :
    constrainedCriticality f C x tau alpha j = 0 ↔
      ∀ d ∈ restrictedFeasibleSteps f C x tau alpha j ∩ unitBall,
        0 ≤ directionalDerivative f x j d := by
  simpa only [constrainedCriticality, neg_nonpos] using
    (gapOn_eq_zero_iff (Δ := fun d => -directionalDerivative f x j d)
      (isCompact_restrictedFeasibleSteps_inter_unitBall f hC x tau alpha j)
      (continuous_directionalDerivative f x j).neg.continuousOn
      (zero_mem_restrictedFeasibleSteps_inter_unitBall f hx tau alpha j ht) (by simp))

/-- Source approximate first-, second-, and third-order minimizers. Index `q` denotes order
`q.val+1`; only indices `j ≤ q` are active. All active tolerances are finite positive real numbers,
and the source's fixed restriction factors belong to `(0,1)`. -/
def IsApproximateConstrainedMinimizer (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (tau : Fin 2 → ℝ) (epsilon : Fin 3 → ℝ) (q : Fin 3) : Prop :=
  x ∈ C ∧ (∀ i, tau i ∈ Set.Ioo 0 1) ∧ (∀ j ≤ q, 0 < epsilon j) ∧
    ∀ j ≤ q, constrainedCriticality f C x tau (fun i => epsilon i.castSucc) j ≤ epsilon j

/-- Introduction and elimination form for the approximate minimizer conditions. -/
theorem isApproximateConstrainedMinimizer_iff (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (tau : Fin 2 → ℝ) (epsilon : Fin 3 → ℝ) (q : Fin 3) :
    IsApproximateConstrainedMinimizer f C x tau epsilon q ↔
      x ∈ C ∧ (∀ i, tau i ∈ Set.Ioo 0 1) ∧ (∀ j ≤ q, 0 < epsilon j) ∧
        ∀ j ≤ q, constrainedCriticality f C x tau (fun i => epsilon i.castSucc) j ≤ epsilon j :=
  Iff.rfl

end CartisGouldToint.Chapter06.Section01
