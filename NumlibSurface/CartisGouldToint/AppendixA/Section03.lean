import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Quotient convergence rates

Appendix A.3 defines rates for strictly positive scalar sequences tending to zero,
using an existing limit of successive quotients. This is stronger than an eventual
contraction bound. In particular, finite termination is outside this convention:
no ratio at a zero error is silently interpreted as a convergence rate.
-/

namespace CartisGouldToint.AppendixA.Section03

open Filter

/-- A strictly positive sequence tending to zero has quotient rate `ρ` when its
successive quotient tends to `ρ`, as in Appendix A.3. -/
structure QConvergenceRate (a : ℕ → ℝ) (ρ : ℝ) : Prop where
  /-- The source restricts to strictly positive errors. -/
  positive : ∀ k, 0 < a k
  /-- The sequence converges to zero. -/
  tendsto_zero : Tendsto a atTop (nhds 0)
  /-- The limit of successive quotients. -/
  tendsto_quotient : Tendsto (fun k => a (k + 1) / a k) atTop (nhds ρ)

/-- Introduction and elimination for the quotient-rate convention. -/
theorem qConvergenceRate_iff (a : ℕ → ℝ) (ρ : ℝ) :
    QConvergenceRate a ρ ↔ (∀ k, 0 < a k) ∧ Tendsto a atTop (nhds 0) ∧
      Tendsto (fun k => a (k + 1) / a k) atTop (nhds ρ) :=
  ⟨fun h => ⟨h.positive, h.tendsto_zero, h.tendsto_quotient⟩,
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- `Q`-superlinear convergence means quotient limit zero. -/
abbrev QSuperlinear (a : ℕ → ℝ) : Prop := QConvergenceRate a 0

/-- `Q`-linear convergence means a quotient limit strictly between zero and one. -/
def QLinear (a : ℕ → ℝ) : Prop :=
  ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ QConvergenceRate a ρ

/-- `Q`-sublinear convergence means quotient limit one. -/
abbrev QSublinear (a : ℕ → ℝ) : Prop := QConvergenceRate a 1

/-- The source's order condition: a positive zero-convergent sequence has a finite
limit of `a (k+1) / a k ^ q`, bounded by some positive constant. The real order is at least one.
This does not assert the source's informal converse that superlinearity forces `q > 1`. -/
def QOrder (a : ℕ → ℝ) (q : ℝ) : Prop :=
  1 ≤ q ∧ (∀ k, 0 < a k) ∧ Tendsto a atTop (nhds 0) ∧
    ∃ l o : ℝ, 0 < o ∧ l ≤ o ∧
      Tendsto (fun k => a (k + 1) / (a k) ^ q) atTop (nhds l)

/-- The quadratic convention is the order condition with order two. -/
abbrev QQuadratic (a : ℕ → ℝ) : Prop := QOrder a 2

/-- Global linear convergence is the source's one-step bound at every index. -/
def GloballyLinear (a : ℕ → ℝ) : Prop :=
  (∀ k, 0 < a k) ∧ Tendsto a atTop (nhds 0) ∧
    ∃ ρ : ℝ, ρ < 1 ∧ ∀ k, a (k + 1) ≤ ρ * a k

/-- Local quadratic convergence is the quadratic step bound at all sufficiently
large indices, in the region where the scaled error is less than one. -/
def LocallyQuadratic (a : ℕ → ℝ) : Prop :=
  (∀ k, 0 < a k) ∧ Tendsto a atTop (nhds 0) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ k in atTop, ρ * a k < 1 ∧ a (k + 1) ≤ ρ * a k ^ 2

/-- A quotient rate cannot hold when an error vanishes, including a zero tail. -/
theorem not_qConvergenceRate_of_eq_zero {a : ℕ → ℝ} {ρ : ℝ} {k : ℕ}
    (hk : a k = 0) : ¬ QConvergenceRate a ρ := by
  intro h
  have := h.positive k
  simp [hk] at this

/-- The scalar error of a vector sequence relative to a proposed limit. -/
def errorSequence {E : Type*} [SeminormedAddCommGroup E] (x : ℕ → E) (xstar : E) : ℕ → ℝ :=
  fun k => ‖x k - xstar‖

/-- Strictly positive vector errors mean that no iterate already equals the limit. -/
theorem errorSequence_pos_iff {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (xstar : E) (k : ℕ) : 0 < errorSequence x xstar k ↔ x k ≠ xstar := by
  simp [errorSequence, norm_pos_iff, sub_ne_zero]

end CartisGouldToint.AppendixA.Section03
