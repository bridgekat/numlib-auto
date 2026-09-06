import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.LinearSolve.Stationary.Basic

/-!
# Splittings and the classical iterations

A splitting `a = m - n` with `m` a unit, in any ring (`Stationary.Splitting`, determined by `m`
alone: `n := m - a`), its iteration operator `G = m⁻¹ n = 1 - m⁻¹ a`, and the matrix constructors
for Jacobi, Gauss–Seidel, SOR, SSOR and Richardson ([saad2003iterative] §4.1, (4.5)–(4.27);
[kress1998numerical] §4.1–4.2; [han2009theoretical] §5.2.2 — whose convention `A = N - M` swaps the
roles of the letters; [higham2002accuracy] Ch. 17). [saad2003iterative] writes the splitting as `A =
D - E - F` with `D` the diagonal and `-E`, `-F` the strictly lower and strictly upper triangular
parts, which corresponds to `D = diagPart A`, `E = -strictLower A`, `F = -strictUpper A`.
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

/-- The defining identity `a = m - n`.  Only `m` is stored and `n` is recovered as `m - a`, so this
is the statement that a `Splitting` really does split `a`. -/
theorem m_sub_n : s.m - s.n = a := sub_sub_cancel _ _

/-- The iteration operator `G = m⁻¹ n = 1 - m⁻¹ a` of the splitting `a = m - n`
([saad2003iterative], (4.28)/(4.30)). -/
noncomputable def iterationOperator : R := 1 - Ring.inverse s.m * a

/-- The two usual formulas for the iteration operator agree: `1 - m⁻¹ a` is `m⁻¹ n`.  The first is
the definition, the second is the form in which the classical iteration matrices are read off from
`Splitting.n`. -/
theorem iterationOperator_eq : s.iterationOperator = Ring.inverse s.m * s.n := by
  rw [iterationOperator, Splitting.n, mul_sub, Ring.inverse_mul_cancel _ s.isUnit]

/-- `1 - G = m⁻¹ a`, the preconditioned system operator.  Read with
`Stationary.Splitting.eq_iterationOperator_mul_add_iff`, this is the consistency of the iteration:
`m` preconditions `a`, and the fixed points are the solutions of `a x = b`. -/
theorem one_sub_iterationOperator : 1 - s.iterationOperator = Ring.inverse s.m * a := by
  rw [iterationOperator, sub_sub_cancel]

/-- Consistency: `x = G x + m⁻¹ b ↔ a x = b` (ring form; for `R = E →L E` acting on `E` see
`Stationary.step`). -/
theorem eq_iterationOperator_mul_add_iff (x b : R) :
    x = s.iterationOperator * x + Ring.inverse s.m * b ↔ a * x = b := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := a * x),
    show x - (s.iterationOperator * x + Ring.inverse s.m * b)
      = Ring.inverse s.m * (a * x - b) by rw [iterationOperator]; noncomm_ring,
    s.isUnit.ringInverse.mul_right_eq_zero]

/-- Richardson's splitting `m = α⁻¹ • 1`. -/
noncomputable def richardson {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 R] (a : R) {α : 𝕜} (hα : α ≠ 0) :
    Splitting a :=
  ⟨α⁻¹ • (1 : R), by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.mpr (inv_ne_zero hα)).map (algebraMap 𝕜 R)⟩

/-- Richardson's iteration operator is `1 - α a`, so the step is `x ↦ x + α (b - a x)`: a fixed step
length `α` along the residual, with no preconditioner beyond the scalar. -/
theorem richardson_iterationOperator {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 R] (a : R) {α : 𝕜}
    (hα : α ≠ 0) : (richardson a hα).iterationOperator = 1 - α • a := by
  let u : Rˣ :=
    { val := α⁻¹ • (1 : R)
      inv := α • (1 : R)
      val_inv := by rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hα, one_smul]
      inv_val := by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hα, one_smul] }
  have hm : (richardson a hα).m = (u : R) := rfl
  rw [iterationOperator, hm, Ring.inverse_unit]
  change 1 - (α • (1 : R)) * a = _
  rw [smul_mul_assoc, one_mul]

end Splitting

end Stationary

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
variable {𝕜 : Type*} [Field 𝕜]

omit [LinearOrder n] in
/-- The diagonal part of `A` is a unit exactly when every diagonal entry of `A` is nonzero.  This is
the hypothesis every splitting below is built on. -/
theorem isUnit_diagPart_iff (A : Matrix n n 𝕜) : IsUnit (diagPart A) ↔ ∀ i, A i i ≠ 0 := by
  rw [isUnit_iff_isUnit_det, diagPart, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp [Matrix.diag]

omit [LinearOrder n] in
/-- The inverse of the diagonal part is the diagonal matrix of the inverses.  Every entrywise
computation with a splitting goes through this, because `Matrix.inv_diagonal` inverts the diagonal
in the Pi ring and is therefore `0` when one entry vanishes. -/
theorem inv_diagPart {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    (diagPart A)⁻¹ = diagonal fun i => (A i i)⁻¹ := by
  have hd := (isUnit_diagPart_iff A).mp h
  refine inv_eq_left_inv ?_
  rw [diagPart, diagonal_mul_diagonal, ← diagonal_one]
  exact congrArg _ (funext fun i => inv_mul_cancel₀ (hd i))

/-- A triangular matrix whose diagonal entries are nonzero is a unit. -/
private theorem isUnit_of_isLowerTriangular {M : Matrix n n 𝕜} (hM : M.IsLowerTriangular)
    (hd : ∀ i, M i i ≠ 0) : IsUnit M := by
  rw [isUnit_iff_isUnit_det, det_of_isLowerTriangular M hM, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i

/-- An upper triangular matrix whose diagonal entries are nonzero is a unit. -/
private theorem isUnit_of_isUpperTriangular {M : Matrix n n 𝕜} (hM : M.IsUpperTriangular)
    (hd : ∀ i, M i i ≠ 0) : IsUnit M := by
  rw [isUnit_iff_isUnit_det, det_of_isUpperTriangular hM, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i

/-- The generic shape of every `M` below: a scaled diagonal plus a scaled strictly triangular part
is a unit as soon as the scaling of the diagonal and the diagonal of `A` are nonzero. -/
private theorem isUnit_smul_diagPart_add_smul_strictLower (A : Matrix n n 𝕜) {c d : 𝕜} (hc : c ≠ 0)
    (h : IsUnit (diagPart A)) : IsUnit (c • diagPart A + d • strictLower A) := by
  refine isUnit_of_isLowerTriangular (fun i j hij => ?_) fun i => ?_
  · have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [hij'.ne, asymm hij']
  · simpa using mul_ne_zero hc ((isUnit_diagPart_iff A).mp h i)

/-- The upper triangular counterpart of `Matrix.isUnit_smul_diagPart_add_smul_strictLower`, used for
the backward sweeps. -/
private theorem isUnit_smul_diagPart_add_smul_strictUpper (A : Matrix n n 𝕜) {c d : 𝕜} (hc : c ≠ 0)
    (h : IsUnit (diagPart A)) : IsUnit (c • diagPart A + d • strictUpper A) := by
  refine isUnit_of_isUpperTriangular (fun i j hij => ?_) fun i => ?_
  · have hij' : j < i := hij
    simp [hij'.ne', asymm hij']
  · simpa using mul_ne_zero hc ((isUnit_diagPart_iff A).mp h i)

omit [LinearOrder n] in
/-- A nonzero scalar multiple of a unit matrix is a unit. -/
private theorem isUnit_smul {c : 𝕜} (hc : c ≠ 0) {M : Matrix n n 𝕜} (hM : IsUnit M) :
    IsUnit (c • M) := by
  rw [isUnit_iff_isUnit_det, det_smul, isUnit_iff_ne_zero] at *
  exact mul_ne_zero (pow_ne_zero _ hc) hM

/-- `D + L`, [saad2003iterative] `D - E`, is invertible as soon as the diagonal of `A` is: it is
lower triangular with the diagonal of `A` on its diagonal.  This is what makes the Gauss–Seidel
splitting well defined. -/
theorem isUnit_diagPart_add_strictLower {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart A + strictLower A) := by
  simpa using isUnit_smul_diagPart_add_smul_strictLower (d := 1) A one_ne_zero h

/-- `D + U`, [saad2003iterative] `D - F`, is invertible as soon as the diagonal of `A` is.  This is
what makes the backward Gauss–Seidel splitting well defined. -/
theorem isUnit_diagPart_add_strictUpper {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart A + strictUpper A) := by
  simpa using isUnit_smul_diagPart_add_smul_strictUpper (d := 1) A one_ne_zero h

/-- Jacobi: `M = D`, `N = E + F`, in [saad2003iterative] letters `A = D - E - F` for the diagonal
and the negated strictly lower / strictly upper parts ([saad2003iterative], (4.5)). -/
noncomputable def jacobiSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) : Splitting A :=
  ⟨diagPart A, h⟩

/-- The complementary part of the Jacobi splitting is `-(strictLower A + strictUpper A)`, that is `N
= E + F` in [saad2003iterative] letters `A = D - E - F`. -/
theorem jacobiSplitting_n (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    (jacobiSplitting A h).n = -(strictLower A + strictUpper A) := by
  change diagPart A - A = -(strictLower A + strictUpper A)
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← add_assoc,
    diagPart_add_strictLower_add_strictUpper, sub_self]

/-- The Jacobi iteration matrix `-D⁻¹ (E + F)`, with `D` the diagonal part of `A` and `-E`, `-F` its
strictly lower and strictly upper parts ([saad2003iterative], (4.7)). -/
theorem jacobiSplitting_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    (jacobiSplitting A h).iterationOperator =
      -(diagPart A)⁻¹ * (strictLower A + strictUpper A) := by
  have hm : (jacobiSplitting A h).m = diagPart A := rfl
  rw [Splitting.iterationOperator_eq, jacobiSplitting_n, hm, nonsing_inv_eq_ringInverse, neg_mul,
    mul_neg]

/-- Gauss–Seidel: `M = D - E`, `N = F`, in [saad2003iterative] letters `A = D - E - F`
([saad2003iterative], (4.6)). -/
noncomputable def gaussSeidelSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    Splitting A :=
  ⟨diagPart A + strictLower A, isUnit_diagPart_add_strictLower h⟩

/-- The complementary part of the Gauss–Seidel splitting is `-strictUpper A`, that is `N = F` in
[saad2003iterative] letters `A = D - E - F`: the forward sweep absorbs the whole lower triangle,
leaving only the strictly upper part on the right-hand side. -/
theorem gaussSeidelSplitting_n (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    (gaussSeidelSplitting A h).n = -strictUpper A := by
  change diagPart A + strictLower A - A = -strictUpper A
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, diagPart_add_strictLower_add_strictUpper,
    sub_self]

/-- Backward Gauss–Seidel: `M = D - F`, the backward sweep, in [saad2003iterative] letters `A = D -
E - F` ([saad2003iterative], §4.1). -/
noncomputable def backwardGaussSeidelSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    Splitting A :=
  ⟨diagPart A + strictUpper A, isUnit_diagPart_add_strictUpper h⟩

/-- SOR (successive over-relaxation) with parameter `ω`: `M = ω⁻¹ (D - ω E)`, in [saad2003iterative]
letters `A = D - E - F` ([saad2003iterative], (4.11)–(4.12)). -/
noncomputable def sorSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0) :
    Splitting A :=
  ⟨ω⁻¹ • diagPart A + strictLower A, by
    simpa using isUnit_smul_diagPart_add_smul_strictLower (d := 1) A (inv_ne_zero hω) h⟩

/-- The SOR iteration matrix `(D - ωE)⁻¹ (ωF + (1 - ω) D)`, with `D` the diagonal part of `A` and
`-E`, `-F` its strictly lower and strictly upper parts ([saad2003iterative], (4.14)). -/
theorem sorSplitting_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) :
    (sorSplitting A h hω).iterationOperator =
      (diagPart A + ω • strictLower A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A) := by
  set M : Matrix n n 𝕜 := ω⁻¹ • diagPart A + strictLower A with hM
  have hMdet : IsUnit M.det := (isUnit_iff_isUnit_det _).mp (sorSplitting A h hω).isUnit
  have h1 : diagPart A + ω • strictLower A = ω • M := by
    rw [hM, smul_add, smul_smul, mul_inv_cancel₀ hω, one_smul]
  have key : ∀ x : 𝕜, (1 - ω) * x = ω * (ω⁻¹ * x - x) := fun x => by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hω, one_mul, sub_mul, one_mul]
  have h2 : (1 - ω) • diagPart A - ω • strictUpper A = ω • (M - A) := by
    ext i j
    rcases lt_trichotomy i j with hlt | rfl | hlt
    · simp [hM, hlt, hlt.ne, asymm hlt]
    · simpa [hM] using key (A i i)
    · simp [hM, hlt, hlt.ne', asymm hlt]
  have h3 : (ω • M)⁻¹ = ω⁻¹ • M⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hω, nonsing_inv_mul _ hMdet, one_smul]
  rw [Splitting.iterationOperator_eq, h1, h2, h3, smul_mul_smul_comm, inv_mul_cancel₀ hω,
    one_smul, nonsing_inv_eq_ringInverse]
  rfl

/-- SSOR (symmetric successive over-relaxation), one forward SOR sweep followed by a backward one:
`M = (1/(ω(2-ω))) (D - ωE) D⁻¹ (D - ωF)`, in [saad2003iterative] letters `A = D - E - F`
([saad2003iterative], (4.27)). -/
noncomputable def ssorSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0)
    (hω2 : ω ≠ 2) : Splitting A :=
  ⟨(ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
      (diagPart A + ω • strictUpper A)), by
    have hu1 : IsUnit (diagPart A + ω • strictLower A) := by
      simpa using isUnit_smul_diagPart_add_smul_strictLower A (c := 1) (d := ω) one_ne_zero h
    have hu2 : IsUnit ((diagPart A)⁻¹) := by
      rw [nonsing_inv_eq_ringInverse]; exact h.ringInverse
    have hu3 : IsUnit (diagPart A + ω • strictUpper A) := by
      simpa using isUnit_smul_diagPart_add_smul_strictUpper A (c := 1) (d := ω) one_ne_zero h
    exact isUnit_smul (inv_ne_zero (mul_ne_zero hω (sub_ne_zero_of_ne hω2.symm)))
      ((hu1.mul hu2).mul hu3)⟩

/-- Gauss–Seidel is SOR with `ω = 1`. -/
theorem sorSplitting_one (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    sorSplitting A h one_ne_zero = gaussSeidelSplitting A h := by
  ext : 1
  change (1 : 𝕜)⁻¹ • diagPart A + strictLower A = diagPart A + strictLower A
  rw [inv_one, one_smul]

end Matrix
