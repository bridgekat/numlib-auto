import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Function regularity requirements

Mnemonic regularity requirements denote concrete predicates, independently of any algorithm.
A region is explicit; a neighborhood requirement quantifies over an open superset of it.
-/

namespace FunctionRegularity

/-- The kinds of smoothness, derivative Lipschitz and lower-bound requirements. -/
inductive Requirement where
  /-- Continuous differentiability through the specified order, including order zero. -/
  | smooth (order : ℕ)
  /-- Lipschitz continuity of each actual derivative in the inclusive order interval. -/
  | derivativeLipschitz (first last : ℕ)
  /-- A genuine uniform lower bound on objective values. -/
  | boundedBelow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Interpret a mnemonic requirement on a specified region. Derivative requirements include
continuous differentiability through their last order; Lipschitz constants may differ by order. -/
def On (r : Requirement) (f : E → ℝ) (S : Set E) : Prop :=
  match r with
  | .smooth p => ContDiffOn ℝ p f S
  | .derivativeLipschitz q p => ContDiffOn ℝ p f S ∧
      ∀ j, q ≤ j → j ≤ p → ∃ L : NNReal, LipschitzOnWith L (iteratedFDeriv ℝ j f) S
  | .boundedBelow => BddBelow (f '' S)

/-- Interpret an unsuffixed requirement on the whole domain. -/
def Globally (r : Requirement) (f : E → ℝ) : Prop := On r f Set.univ

/-- Interpret a neighborhood suffix using an open region containing the named set. -/
def Near (r : Requirement) (f : E → ℝ) (S : Set E) : Prop :=
  ∃ U, IsOpen U ∧ S ⊆ U ∧ On r f U

/-- Smoothness requirements are precisely the standard `ContDiffOn` interface. -/
@[simp] theorem on_smooth_iff (f : E → ℝ) (S : Set E) (p : ℕ) :
    On (.smooth p) f S ↔ ContDiffOn ℝ p f S := Iff.rfl

/-- Derivative Lipschitz requirements quantify over the stated inclusive order interval. -/
@[simp] theorem on_derivativeLipschitz_iff (f : E → ℝ) (S : Set E) (q p : ℕ) :
    On (.derivativeLipschitz q p) f S ↔ ContDiffOn ℝ p f S ∧
      ∀ j, q ≤ j → j ≤ p → ∃ L : NNReal, LipschitzOnWith L (iteratedFDeriv ℝ j f) S := Iff.rfl

/-- The lower-bound requirement is an actual real lower bound on every value in the region. -/
@[simp] theorem on_boundedBelow_iff (f : E → ℝ) (S : Set E) :
    On .boundedBelow f S ↔ ∃ b : ℝ, ∀ x ∈ S, b ≤ f x := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, fun x hx => hb ⟨x, hx, rfl⟩⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hb x hx

/-- Unsuffixed continuous differentiability agrees with global smoothness. -/
@[simp] theorem globally_smooth_iff (f : E → ℝ) (p : ℕ) :
    Globally (.smooth p) f ↔ ContDiff ℝ p f := contDiffOn_univ

/-- A global requirement holds on a neighborhood of every set. -/
theorem Globally.near {r : Requirement} {f : E → ℝ} (h : Globally r f) (S : Set E) :
    Near r f S := ⟨Set.univ, isOpen_univ, Set.subset_univ S, h⟩

/-- A neighborhood requirement on the whole domain is equivalent to the global requirement. -/
@[simp] theorem near_univ_iff (r : Requirement) (f : E → ℝ) :
    Near r f Set.univ ↔ Globally r f := by
  constructor
  · rintro ⟨U, _, hU, h⟩
    have : U = Set.univ := Set.univ_subset_iff.mp hU
    simpa [this, Globally] using h
  · intro h
    exact h.near _

end FunctionRegularity
