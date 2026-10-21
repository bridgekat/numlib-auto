import Numlib.Eigen.ShiftedInverseBatches
import Mathlib.Data.ENat.Basic

/-!
# Adaptive shifted inverse iteration

A batch uses one fixed shift and its actual normalized inverse powers. The next shift is
formed from the new Rayleigh quotient and a damped real power. Parameters constrain only
operational choices; they contain no convergence or spectral-error conclusions. Singular
shifts use the existing total inverse convention. Unit-norm conclusions require regularity.
-/

noncomputable section
open scoped InnerProductSpace
namespace Optimization.AdaptiveInverseIteration

/-- Fixed damping, exponent, and inverse-batch limits. An infinite batch limit is allowed. -/
structure Parameters where
  dampingLower : ℝ
  dampingUpper : ℝ
  exponentLower : ℝ
  exponentMargin : ℝ
  batchUpper : ℕ∞
  damping_pos : 0 < dampingLower
  damping_le : dampingLower ≤ dampingUpper
  exponent_lt : 1 < exponentLower
  margin_pos : 0 < exponentMargin
  margin_le : exponentMargin ≤ 1
  exponent_le : exponentLower ≤ 2 - exponentMargin
  batch_pos : 1 ≤ batchUpper

/-- Choices made at one outer iteration. -/
structure Choice where
  count : ℕ
  damping : ℝ
  exponent : ℝ

/-- The admissible choices, including the dependence of the exponent on the batch length. -/
def Choice.Legal (p : Parameters) (c : Choice) : Prop :=
  1 ≤ c.count ∧ (c.count : ℕ∞) ≤ p.batchUpper ∧
    c.damping ∈ Set.Icc p.dampingLower p.dampingUpper ∧
    c.exponent ∈ Set.Icc p.exponentLower (2 * (c.count : ℝ) - p.exponentMargin)

/-- The admissible-choice predicate exposes precisely its four scalar tests. -/
@[simp] theorem Choice.legal_iff (p : Parameters) (c : Choice) :
    c.Legal p ↔ 1 ≤ c.count ∧ (c.count : ℕ∞) ≤ p.batchUpper ∧
      c.damping ∈ Set.Icc p.dampingLower p.dampingUpper ∧
      c.exponent ∈ Set.Icc p.exponentLower (2 * (c.count : ℝ) - p.exponentMargin) := Iff.rfl

/-- A shift and its current eigenvector estimate. -/
structure State (E : Type*) where
  shift : ℝ
  vector : E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One actual inverse/Rayleigh update. The shift remains fixed throughout the batch. -/
noncomputable def update (A : E →ₗ[ℝ] E) (s : State E) (c : Choice) : State E :=
  let z := Krylov.shiftedInverseBatch A s.shift s.vector c.count
  let rho := inner ℝ z (A z)
  ⟨-rho + c.damping * (s.shift + rho) ^ c.exponent, z⟩

/-- The vector component is exactly the requested batch of normalized inverse iterations. -/
@[simp] theorem update_vector (A : E →ₗ[ℝ] E) (s : State E) (c : Choice) :
    (update A s c).vector = Krylov.shiftedInverseBatch A s.shift s.vector c.count := rfl

/-- The shift component uses the actual Rayleigh quotient of the computed new vector. -/
theorem update_shift (A : E →ₗ[ℝ] E) (s : State E) (c : Choice) :
    (update A s c).shift =
      -inner ℝ (update A s c).vector (A (update A s c).vector) +
        c.damping * (s.shift + inner ℝ (update A s c).vector
          (A (update A s c).vector)) ^ c.exponent := rfl

/-- The actual recursively generated outer iteration, for any stream of choices. -/
noncomputable def iterate (A : E →ₗ[ℝ] E) (s : State E) (c : ℕ → Choice) : ℕ → State E
  | 0 => s
  | k + 1 => update A (iterate A s c k) (c k)

/-- The initial state is the given state. -/
@[simp] theorem iterate_zero (A : E →ₗ[ℝ] E) (s : State E) (c : ℕ → Choice) :
    iterate A s c 0 = s := rfl

/-- Each outer step computes the inverse batch before updating the shift. -/
@[simp] theorem iterate_succ (A : E →ₗ[ℝ] E) (s : State E) (c : ℕ → Choice) (k : ℕ) :
    iterate A s c (k + 1) = update A (iterate A s c k) (c k) := rfl

/-- Computed vectors remain unit vectors along every finite regular prefix. -/
theorem norm_iterate_vector (A : E →ₗ[ℝ] E) (s : State E) (c : ℕ → Choice)
    (h0 : ‖s.vector‖ = 1) (k : ℕ)
    (hreg : ∀ j < k, IsUnit (A + (iterate A s c j).shift • 1)) :
    ‖(iterate A s c k).vector‖ = 1 := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hn := ih (fun j hj => hreg j (Nat.lt_succ_of_lt hj))
    rw [iterate_succ, update_vector]
    apply Krylov.norm_shiftedInverseBatch (hreg k (Nat.lt_succ_self k))
    exact norm_ne_zero_iff.mp (by rw [hn]; norm_num)

/-- A one-step batch of length one is always a legal parameter choice at the lower limits. -/
theorem Parameters.lowerChoice_legal (p : Parameters) :
    (Choice.mk 1 p.dampingLower p.exponentLower).Legal p := by
  exact ⟨le_rfl, p.batch_pos, ⟨le_rfl, p.damping_le⟩,
    ⟨le_rfl, by simpa using p.exponent_le⟩⟩

/-- No nonzero spectral coordinate is lost along a regular finite outer prefix.
The assertion applies to every coordinate of a repeated eigenspace. -/
theorem repr_iterate_vector_ne_zero [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (s : State E) (c : ℕ → Choice)
    {i : Fin (Module.finrank ℝ E)} (hi : (hA.eigenvectorBasis rfl).repr s.vector i ≠ 0)
    (k : ℕ) (hreg : ∀ j < k, ∀ l,
      (iterate A s c j).shift + hA.eigenvalues rfl l ≠ 0) :
    (hA.eigenvectorBasis rfl).repr (iterate A s c k).vector i ≠ 0 := by
  induction k with
  | zero => exact hi
  | succ k ih =>
    rw [iterate_succ, update_vector]
    exact Krylov.repr_shiftedInverseBatch_ne_zero hA (hreg k (Nat.lt_succ_self k))
      (c k).count (ih (fun j hj => hreg j (Nat.lt_succ_of_lt hj)))

end Optimization.AdaptiveInverseIteration
