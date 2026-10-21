import Numlib.Analysis.Calculus.CurveTaylorPaths
import Numlib.Optimization.ConstrainedTaylorCriticality

/-!
# Realizable equality-constraint jets and necessary curve conditions

A descriptor is realized by an actual asymptotic path in the simple constraint set. A
separate qualification lifts each descriptor with vanishing constraint coefficients to an
actual equality-feasible path with the same jet. This universal realization hypothesis is
stronger than nonemptiness of algebraic jets. Local minimality then constrains every
Lagrangian coefficient, with the multiplier held fixed.
-/

noncomputable section
open Set Filter CurveTaylor
open scoped Topology
namespace Optimization.FeasibleCurveJets
variable {E F : Type*}

/-- The actual feasible set includes both the simple constraint and all equalities. -/
def equalitySet [Zero F] (S : Set E) (c : E → F) : Set E := {x ∈ S | c x = 0}

/-- Feasibility retains both parts of the original constraints. -/
@[simp] theorem mem_equalitySet [Zero F] {S : Set E} {c : E → F} {x : E} :
    x ∈ equalitySet S c ↔ x ∈ S ∧ c x = 0 := Iff.rfl

section LocalMinimum
variable [TopologicalSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
open ConstrainedTaylorCriticality

/-- On the actual feasible set, objective minimality is also Lagrangian minimality for
any fixed multiplier, with the convention `f - ⟪y,c⟫`. -/
theorem isLocalMinOn_residualLagrangian {S : Set E} {c : E → F} {f : E → ℝ} {x : E}
    (hx : c x = 0) (hmin : IsLocalMinOn f (equalitySet S c) x) (y : F) :
    IsLocalMinOn (residualLagrangian f c y) (equalitySet S c) x := by
  filter_upwards [hmin, self_mem_nhdsWithin] with z hz hS
  simpa only [residualLagrangian, hx, hS.2, inner_zero_right, sub_zero] using hz

end LocalMinimum
section Jets
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An actual simple-set descriptor jet with vanishing equality-constraint coefficients. -/
structure Jet (S : Set E) (c : E → F) (x : E) (j : ℕ) where
  direction : ℕ → E
  realizable : RealizableJet S x j direction
  constraint_zero : ∀ i, 1 ≤ i → i ≤ j → vectorCoefficient c x i direction = 0

/-- An actual path and its coefficient tests introduce a descriptor jet. -/
def Jet.of_path {S : Set E} {c : E → F} {x : E} {j : ℕ} (s : ℕ → E)
    (gamma : ℝ → E) (hg : HasCurveJet x j s gamma)
    (hS : ∀ᶠ t in 𝓝[>] (0 : ℝ), gamma t ∈ S)
    (hc : ∀ i, 1 ≤ i → i ≤ j → vectorCoefficient c x i s = 0) : Jet S c x j :=
  ⟨s, ⟨gamma, hg, hS⟩, hc⟩

/-- Equality-constraint qualification realizes every admissible descriptor by an actual
fully feasible path. It asserts no sign, minimum, derivative bound, or complexity result. -/
structure Qualification (S : Set E) (c : E → F) (x : E) (q : ℕ) : Prop where
  realize : ∀ j, 1 ≤ j → j ≤ q → (v : Jet S c x j) →
    RealizableJet (equalitySet S c) x j v.direction

/-- Qualification exposes its universal actual-path realization statement. -/
@[simp] theorem qualification_iff (S : Set E) (c : E → F) (x : E) (q : ℕ) :
    Qualification S c x q ↔ ∀ j, 1 ≤ j → j ≤ q → (v : Jet S c x j) →
      RealizableJet (equalitySet S c) x j v.direction := ⟨fun h => h.realize, Qualification.mk⟩

/-- A qualification for higher orders also qualifies every smaller requested order. -/
theorem Qualification.mono {S : Set E} {c : E → F} {x : E} {q r : ℕ}
    (h : Qualification S c x q) (hr : r ≤ q) : Qualification S c x r :=
  ⟨fun j hj hjr v => h.realize j hj (hjr.trans hr) v⟩

end Jets
section Lagrangian
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
open ConstrainedTaylorCriticality

/-- Smooth objectives and constraints give the actual smooth fixed-multiplier Lagrangian. -/
theorem contDiffAt_residualLagrangian {c : E → F} {f : E → ℝ} {x : E} {q : ℕ}
    (hf : ContDiffAt ℝ q f x) (hc : ContDiffAt ℝ q c x) (y : F) :
    ContDiffAt ℝ q (residualLagrangian f c y) x :=
  hf.sub (contDiffAt_const.inner ℝ hc)

/-- At a qualified local constrained minimum the first potentially nonzero Lagrangian
coefficient is nonnegative along every actual simple-set descriptor with zero constraint jets. -/
theorem coefficient_nonneg {S : Set E} {c : E → F} {f : E → ℝ} {x : E} {q j : ℕ}
    (hx : c x = 0) (hmin : IsLocalMinOn f (equalitySet S c) x)
    (hQ : Qualification S c x q) (hf : ContDiffAt ℝ q f x) (hc : ContDiffAt ℝ q c x)
    (hj : 1 ≤ j) (hjq : j ≤ q) (v : Jet S c x j) (y : F)
    (hprev : ∀ i, 1 ≤ i → i < j → coefficient (residualLagrangian f c y) x i v.direction = 0) :
    0 ≤ coefficient (residualLagrangian f c y) x j v.direction := by
  apply (hQ.realize j hj hjq v).coefficient_nonneg hj
    ((contDiffAt_residualLagrangian hf hc y).of_le (by exact_mod_cast hjq))
    (isLocalMinOn_residualLagrangian hx hmin y) hprev

end Lagrangian
end Optimization.FeasibleCurveJets
