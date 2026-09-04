import Numlib.LinearSolve.Stationary.Basic
import Numlib.Matrix.Hessenberg
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.RCLike.Basic

/-!
# Splittings and the classical iterations

A splitting `a = m - n` with `m` a unit, in any ring (`Stationary.Splitting`, determined by `m`
alone: `n := m - a`), its iteration operator `G = m⁻¹ n = 1 - m⁻¹ a`, and the matrix
constructors for Jacobi, Gauss–Seidel, SOR, SSOR and Richardson (Saad §4.1, (4.5)–(4.27); Kress
§4.1–4.2; Atkinson–Han §5.2.2 — whose convention `A = N - M` swaps the roles of the letters;
Higham Ch. 17). Saad's `A = D - E - F` corresponds to `D = diagPart A`, `E = -strictLower A`,
`F = -strictUpper A`.
-/

namespace Stationary

variable {R : Type*} [Ring R]

/-- A splitting `a = m - n` of `a` with `m` a unit, determined by `m` (`n := m - a`). -/
@[ext]
structure Splitting (a : R) where
  /-- The invertible part `m` of the splitting `a = m - n`. -/
  m : R
  isUnit : IsUnit m

namespace Splitting

variable {a : R} (s : Splitting a)

/-- The complementary part `n = m - a`. -/
def n : R := s.m - a

theorem m_sub_n : s.m - s.n = a := by
  sorry

/-- The iteration operator `G = m⁻¹ n = 1 - m⁻¹ a` (Saad (4.28)/(4.30)). -/
noncomputable def iterationOperator : R := 1 - Ring.inverse s.m * a

theorem iterationOperator_eq : s.iterationOperator = Ring.inverse s.m * s.n := by
  sorry

theorem one_sub_iterationOperator : 1 - s.iterationOperator = Ring.inverse s.m * a := by
  sorry

/-- Consistency: `x = G x + m⁻¹ b ↔ a x = b` (ring form; for `R = E →L E` acting on `E` see
`Stationary.step`). -/
theorem eq_iterationOperator_mul_add_iff (x b : R) :
    x = s.iterationOperator * x + Ring.inverse s.m * b ↔ a * x = b := by
  sorry

/-- Richardson's splitting `m = α⁻¹ • 1`. -/
noncomputable def richardson {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 R] (a : R) {α : 𝕜} (hα : α ≠ 0) :
    Splitting a :=
  ⟨α⁻¹ • (1 : R), by sorry⟩

theorem richardson_iterationOperator {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 R] (a : R) {α : 𝕜}
    (hα : α ≠ 0) : (richardson a hα).iterationOperator = 1 - α • a := by
  sorry

end Splitting

end Stationary

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
variable {𝕜 : Type*} [Field 𝕜]

/-- Unit diagonal part. -/
theorem isUnit_diagPart_iff (A : Matrix n n 𝕜) : IsUnit (diagPart A) ↔ ∀ i, A i i ≠ 0 := by
  sorry

theorem isUnit_diagPart_add_strictLower {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart A + strictLower A) := by
  sorry

theorem isUnit_diagPart_add_strictUpper {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart A + strictUpper A) := by
  sorry

/-- Jacobi: `M = D`, `N = E + F` (Saad (4.5)). -/
noncomputable def jacobiSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) : Splitting A :=
  ⟨diagPart A, h⟩

theorem jacobiSplitting_n (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    (jacobiSplitting A h).n = -(strictLower A + strictUpper A) := by
  sorry

/-- The Jacobi iteration matrix `-D⁻¹ (E + F)` (Saad (4.7)). -/
theorem jacobiSplitting_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    (jacobiSplitting A h).iterationOperator =
      -(diagPart A)⁻¹ * (strictLower A + strictUpper A) := by
  sorry

/-- Gauss–Seidel: `M = D - E`, `N = F` (Saad (4.6)). -/
noncomputable def gaussSeidelSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    Splitting A :=
  ⟨diagPart A + strictLower A, isUnit_diagPart_add_strictLower h⟩

theorem gaussSeidelSplitting_n (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    (gaussSeidelSplitting A h).n = -strictUpper A := by
  sorry

/-- Backward Gauss–Seidel: `M = D - F`. -/
noncomputable def backwardGaussSeidelSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    Splitting A :=
  ⟨diagPart A + strictUpper A, isUnit_diagPart_add_strictUpper h⟩

/-- SOR: `M = ω⁻¹ (D - ω E)` (Saad (4.11)–(4.12)). -/
noncomputable def sorSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0) :
    Splitting A :=
  ⟨ω⁻¹ • diagPart A + strictLower A, by sorry⟩

/-- The SOR iteration matrix `(D - ωE)⁻¹ (ωF + (1 - ω) D)` (Saad (4.14)). -/
theorem sorSplitting_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) :
    (sorSplitting A h hω).iterationOperator =
      (diagPart A + ω • strictLower A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A) := by
  sorry

/-- SSOR (Saad (4.27)): `M = (1/(ω(2-ω))) (D - ωE) D⁻¹ (D - ωF)`. -/
noncomputable def ssorSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0)
    (hω2 : ω ≠ 2) : Splitting A :=
  ⟨(ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
      (diagPart A + ω • strictUpper A)), by sorry⟩

/-- Gauss–Seidel is SOR with `ω = 1`. -/
theorem sorSplitting_one (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    sorSplitting A h one_ne_zero = gaussSeidelSplitting A h := by
  sorry

end Matrix
