import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.Stationary.Basic

/-!
# Splittings and the classical iterations

A splitting `a = m - n` with `m` a unit, in any ring (`Stationary.Splitting`, determined by `m`
alone: `n := m - a`), its iteration operator `G = m⁻¹ n = 1 - m⁻¹ a`, and the matrix constructors
for Jacobi, Gauss–Seidel, SOR, SSOR and Richardson ([saad2003iterative] §4.1, (4.5)–(4.27);
[kress1998numerical] §4.1–4.2; [han2009theoretical] §5.2.2 — whose convention `A = N - M` swaps the
roles of the letters; [higham2002accuracy] Ch. 17). [saad2003iterative] writes the splitting as `A =
D - E - F` with `D` the diagonal and `-E`, `-F` the strictly lower and strictly upper triangular
parts, which corresponds to `D = diagPart A`, `E = -strictLower A`, `F = -strictUpper A`.

The Jacobi and Gauss–Seidel splittings of a real matrix commute with `Matrix.complexify`
(`Matrix.complexify_jacobi_iterationOperator`, `Matrix.complexify_gaussSeidel_iterationOperator`),
which is how their spectral radii — `Matrix.complexSpectralRadius`, defined through the
complexification — are read off the complex theory.

Two splittings `a = m₁ - n₁ = m₂ - n₂` applied one after the other are again the iteration of a
splitting, with `m = m₁ (m₁ + m₂ - a)⁻¹ m₂`
(`Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq`); the symmetric methods are the
instances: SSOR is a forward SOR sweep followed by a backward one
(`Matrix.ssorSplitting_iterationOperator_eq_mul`, [quarteroni2000numerical] §4.2.6), and its
preconditioner at `ω = 1` is the symmetric Gauss–Seidel one `(D - E) D⁻¹ (D - F)`
(`Matrix.ssorSplitting_one_m`, [quarteroni2000numerical] (4.21)).
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

/-- The expansion `m₂⁻¹ (m₁ + m₂ - a) m₁⁻¹ = m₂⁻¹ + m₁⁻¹ - m₂⁻¹ a m₁⁻¹` behind the composition of
two splittings. -/
private theorem inverse_mul_add_sub_mul_inverse (s₁ s₂ : Splitting a) :
    Ring.inverse s₂.m * (s₁.m + s₂.m - a) * Ring.inverse s₁.m
      = Ring.inverse s₂.m + Ring.inverse s₁.m - Ring.inverse s₂.m * a * Ring.inverse s₁.m := by
  rw [mul_sub, mul_add, sub_mul, add_mul, mul_assoc (Ring.inverse s₂.m) s₁.m,
    Ring.mul_inverse_cancel _ s₁.isUnit, mul_one, Ring.inverse_mul_cancel _ s₂.isUnit, one_mul]

/-- **Composing two splittings.**  One step of the splitting `m₁` followed by one step of the
splitting `m₂` is one step of a third splitting `t` whenever `t.m⁻¹ = m₂⁻¹ (m₁ + m₂ - a) m₁⁻¹`,
that is `t.m = m₁ (m₁ + m₂ - a)⁻¹ m₂` when `m₁ + m₂ - a` is a unit: the iteration operators
multiply, `G_t = G₂ G₁`.  Expanding, `t.m⁻¹ = m₂⁻¹ + m₁⁻¹ - m₂⁻¹ a m₁⁻¹`, and `1 - t.m⁻¹ a` is
`(1 - m₂⁻¹ a)(1 - m₁⁻¹ a)`.  This is the elimination of the half-step `x_{k+1/2}` behind every
symmetric method ([quarteroni2000numerical] §4.2.6; [saad2003iterative] (4.13)–(4.14), (4.27)). -/
theorem iterationOperator_eq_mul_of_inverse_m_eq (s₁ s₂ t : Splitting a)
    (ht : Ring.inverse t.m = Ring.inverse s₂.m * (s₁.m + s₂.m - a) * Ring.inverse s₁.m) :
    t.iterationOperator = s₂.iterationOperator * s₁.iterationOperator := by
  rw [iterationOperator, iterationOperator, iterationOperator, ht,
    inverse_mul_add_sub_mul_inverse s₁ s₂]
  noncomm_ring

/-- The constant term of a composite splitting: under the hypothesis of
`Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq`, `t.m⁻¹ = G₂ m₁⁻¹ + m₂⁻¹`, so that
the two consecutive steps `x ↦ G₂ (G₁ x + m₁⁻¹ b) + m₂⁻¹ b` are the single step `x ↦ G_t x + t.m⁻¹
b`. -/
theorem inverse_m_eq_iterationOperator_mul_inverse_add (s₁ s₂ t : Splitting a)
    (ht : Ring.inverse t.m = Ring.inverse s₂.m * (s₁.m + s₂.m - a) * Ring.inverse s₁.m) :
    Ring.inverse t.m = s₂.iterationOperator * Ring.inverse s₁.m + Ring.inverse s₂.m := by
  rw [ht, inverse_mul_add_sub_mul_inverse s₁ s₂, iterationOperator]
  noncomm_ring

section Map

variable {S F : Type*} [Ring S] [FunLike F R S] [RingHomClass F R S]

/-- A splitting transported along a ring homomorphism `f`: the splitting `f a = f m - f n` of the
image.  Complexification of a real matrix splitting and the passage from a matrix to the operator
it induces on `EuclideanSpace` are the two instances used. -/
def map (f : F) (s : Splitting a) : Splitting (f a) := ⟨f s.m, s.isUnit.map f⟩

/-- The `m` of a transported splitting is the image of `m`. -/
@[simp]
theorem map_m (f : F) (s : Splitting a) : (s.map f).m = f s.m := rfl

/-- The complementary part goes along with the transport. -/
theorem map_n (f : F) (s : Splitting a) : (s.map f).n = f s.n := by
  rw [Splitting.n, Splitting.n, map_m, map_sub]

/-- A ring homomorphism carries `Ring.inverse` of a unit to `Ring.inverse` of its image. -/
private theorem map_ringInverse (f : F) {m : R} (hm : IsUnit m) :
    f (Ring.inverse m) = Ring.inverse (f m) := by
  obtain ⟨u, rfl⟩ := hm
  rw [show f (u : R) = ((Units.map (f : R →* S) u : Sˣ) : S) from rfl, Ring.inverse_unit,
    Ring.inverse_unit, Units.coe_map_inv]
  rfl

/-- The iteration operator of a transported splitting is the image of the iteration operator. -/
theorem map_iterationOperator (f : F) (s : Splitting a) :
    (s.map f).iterationOperator = f s.iterationOperator := by
  rw [iterationOperator, iterationOperator, map_m, map_sub, map_one, map_mul,
    map_ringInverse f s.isUnit]

end Map

end Splitting

end Stationary

namespace Matrix

open Stationary

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
variable {𝕜 : Type*} [Field 𝕜]

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
theorem isUnit_smul_diagPart_add_smul_strictLower (A : Matrix n n 𝕜) {c d : 𝕜} (hc : c ≠ 0)
    (h : IsUnit (diagPart A)) : IsUnit (c • diagPart A + d • strictLower A) := by
  refine isUnit_of_isLowerTriangular (fun i j hij => ?_) fun i => ?_
  · have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [hij'.ne, asymm hij']
  · simpa using mul_ne_zero hc ((isUnit_diagPart_iff A).mp h i)

/-- The upper triangular counterpart of `Matrix.isUnit_smul_diagPart_add_smul_strictLower`, used for
the backward sweeps. -/
theorem isUnit_smul_diagPart_add_smul_strictUpper (A : Matrix n n 𝕜) {c d : 𝕜} (hc : c ≠ 0)
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

/-- `D + ω L`, [saad2003iterative] `D - ω E`, is invertible as soon as the diagonal of `A` is, for
every `ω`: it is lower triangular with the diagonal of `A` on its diagonal.  This is the matrix
the SOR sweep inverts. -/
theorem isUnit_diagPart_add_smul_strictLower {A : Matrix n n 𝕜} (h : IsUnit (diagPart A))
    (ω : 𝕜) : IsUnit (diagPart A + ω • strictLower A) := by
  simpa using isUnit_smul_diagPart_add_smul_strictLower (c := 1) (d := ω) A one_ne_zero h

/-- `D + ω U`, [saad2003iterative] `D - ω F`, is invertible as soon as the diagonal of `A` is, for
every `ω`.  This is the matrix the backward SOR sweep inverts. -/
theorem isUnit_diagPart_add_smul_strictUpper {A : Matrix n n 𝕜} (h : IsUnit (diagPart A))
    (ω : 𝕜) : IsUnit (diagPart A + ω • strictUpper A) := by
  simpa using isUnit_smul_diagPart_add_smul_strictUpper (c := 1) (d := ω) A one_ne_zero h

/-- `D + L`, [saad2003iterative] `D - E`, is invertible as soon as the diagonal of `A` is: it is
lower triangular with the diagonal of `A` on its diagonal.  This is what makes the Gauss–Seidel
splitting well defined. -/
theorem isUnit_diagPart_add_strictLower {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart A + strictLower A) := by
  simpa using isUnit_diagPart_add_smul_strictLower h 1

/-- `D + U`, [saad2003iterative] `D - F`, is invertible as soon as the diagonal of `A` is.  This is
what makes the backward Gauss–Seidel splitting well defined. -/
theorem isUnit_diagPart_add_strictUpper {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart A + strictUpper A) := by
  simpa using isUnit_diagPart_add_smul_strictUpper h 1

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

/-- Backward SOR with parameter `ω`: `M = ω⁻¹ (D - ω F)`, in [saad2003iterative] letters `A = D -
E - F`, the mirror image of `Matrix.sorSplitting` with the upper triangle absorbed into the sweep.
Its step is the backward SOR method `(D - ωF) x_{k+1} = [ωE + (1 - ω) D] x_k + ω b` of
[quarteroni2000numerical] §4.2.6; `Matrix.backwardGaussSeidelSplitting` is the case `ω = 1`. -/
noncomputable def backwardSorSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) : Splitting A :=
  ⟨ω⁻¹ • diagPart A + strictUpper A, by
    simpa using isUnit_smul_diagPart_add_smul_strictUpper (d := 1) A (inv_ne_zero hω) h⟩

/-- The backward SOR iteration matrix `(D - ωF)⁻¹ (ωE + (1 - ω) D)`, with `D` the diagonal part of
`A` and `-E`, `-F` its strictly lower and strictly upper parts: the mirror image of
`Matrix.sorSplitting_iterationOperator`. -/
theorem backwardSorSplitting_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    {ω : 𝕜} (hω : ω ≠ 0) :
    (backwardSorSplitting A h hω).iterationOperator =
      (diagPart A + ω • strictUpper A)⁻¹ * ((1 - ω) • diagPart A - ω • strictLower A) := by
  set M : Matrix n n 𝕜 := ω⁻¹ • diagPart A + strictUpper A with hM
  have hMdet : IsUnit M.det :=
    (isUnit_iff_isUnit_det _).mp (backwardSorSplitting A h hω).isUnit
  have h1 : diagPart A + ω • strictUpper A = ω • M := by
    rw [hM, smul_add, smul_smul, mul_inv_cancel₀ hω, one_smul]
  have key : ∀ x : 𝕜, (1 - ω) * x = ω * (ω⁻¹ * x - x) := fun x => by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hω, one_mul, sub_mul, one_mul]
  have h2 : (1 - ω) • diagPart A - ω • strictLower A = ω • (M - A) := by
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

/-- Backward Gauss–Seidel is backward SOR with `ω = 1`. -/
theorem backwardSorSplitting_one (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    backwardSorSplitting A h one_ne_zero = backwardGaussSeidelSplitting A h := by
  ext : 1
  change (1 : 𝕜)⁻¹ • diagPart A + strictUpper A = diagPart A + strictUpper A
  rw [inv_one, one_smul]

/-- The two SOR preconditioners add up to `(2/ω - 1) D` plus `A`: `M_f + M_b - A = (2 ω⁻¹ - 1) D`,
with `M_f = ω⁻¹ D + L` and `M_b = ω⁻¹ D + U`.  This is the "`m₁ + m₂ - a`" of
`Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq` for the symmetric methods. -/
theorem sorSplitting_m_add_backwardSorSplitting_m_sub (A : Matrix n n 𝕜)
    (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0) :
    (sorSplitting A h hω).m + (backwardSorSplitting A h hω).m - A
      = (2 * ω⁻¹ - 1) • diagPart A := by
  set D := diagPart A
  set L := strictLower A
  set U := strictUpper A
  have hA : A = D + L + U := (diagPart_add_strictLower_add_strictUpper A).symm
  change ω⁻¹ • D + L + (ω⁻¹ • D + U) - A = _
  rw [hA]
  module

/-- The SSOR preconditioner is the composite of the forward and the backward SOR preconditioners
in the sense of `Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq`:
`P_SSOR⁻¹ = M_b⁻¹ (M_f + M_b - A) M_f⁻¹` with `M_f = ω⁻¹ D + L`, `M_b = ω⁻¹ D + U`, because `M_f +
M_b - A = (2/ω - 1) D` (`Matrix.sorSplitting_m_add_backwardSorSplitting_m_sub`) and `P_SSOR = M_f
((2/ω - 1) D)⁻¹ M_b` ([quarteroni2000numerical] (4.22)). -/
theorem ringInverse_ssorSplitting_m (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    {ω : 𝕜} (hω : ω ≠ 0) (hω2 : ω ≠ 2) :
    Ring.inverse (ssorSplitting A h hω hω2).m =
      Ring.inverse (backwardSorSplitting A h hω).m *
        ((sorSplitting A h hω).m + (backwardSorSplitting A h hω).m - A) *
          Ring.inverse (sorSplitting A h hω).m := by
  rw [sorSplitting_m_add_backwardSorSplitting_m_sub A h hω, ← nonsing_inv_eq_ringInverse,
    ← nonsing_inv_eq_ringInverse, ← nonsing_inv_eq_ringInverse]
  set Mf : Matrix n n 𝕜 := (sorSplitting A h hω).m with hMf
  set Mb : Matrix n n 𝕜 := (backwardSorSplitting A h hω).m with hMb
  have hMfdet : IsUnit Mf.det := (isUnit_iff_isUnit_det _).mp (sorSplitting A h hω).isUnit
  have hMbdet : IsUnit Mb.det :=
    (isUnit_iff_isUnit_det _).mp (backwardSorSplitting A h hω).isUnit
  have hDdet : IsUnit (diagPart A).det := (isUnit_iff_isUnit_det _).mp h
  have hm : (ssorSplitting A h hω hω2).m
      = (ω * (2 - ω))⁻¹ • ((ω • Mf) * (diagPart A)⁻¹ * (ω • Mb)) := by
    have e1 : diagPart A + ω • strictLower A = ω • Mf := by
      rw [hMf]
      change _ = ω • (ω⁻¹ • diagPart A + strictLower A)
      rw [smul_add, smul_smul, mul_inv_cancel₀ hω, one_smul]
    have e2 : diagPart A + ω • strictUpper A = ω • Mb := by
      rw [hMb]
      change _ = ω • (ω⁻¹ • diagPart A + strictUpper A)
      rw [smul_add, smul_smul, mul_inv_cancel₀ hω, one_smul]
    change (ω * (2 - ω))⁻¹ • ((diagPart A + ω • strictLower A) * (diagPart A)⁻¹ *
      (diagPart A + ω • strictUpper A)) = _
    rw [e1, e2]
  refine inv_eq_right_inv ?_
  rw [hm]
  have hprod : Mf * (diagPart A)⁻¹ * Mb * (Mb⁻¹ * diagPart A * Mf⁻¹) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hMbdet, nonsing_inv_mul_cancel_left _ _ hDdet,
      mul_nonsing_inv _ hMfdet]
  have hscal : (ω * (2 - ω))⁻¹ * (ω * ω * (2 * ω⁻¹ - 1)) = 1 := by
    have h2 : (2 : 𝕜) - ω ≠ 0 := sub_ne_zero_of_ne hω2.symm
    field_simp
  have hone : ∀ k : 𝕜, k = 1 → k • (1 : Matrix n n 𝕜) = 1 := fun k hk => by rw [hk, one_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hprod]
  refine hone _ ?_
  linear_combination hscal

/-- **SSOR is a forward SOR sweep followed by a backward one**: the SSOR iteration matrix is the
product of the backward and the forward SOR iteration matrices,
`B_s(ω) = (D - ωF)⁻¹ (ωE + (1 - ω) D) (D - ωE)⁻¹ (ωF + (1 - ω) D)` ([quarteroni2000numerical]
§4.2.6, and `B_SGS` of (4.21) at `ω = 1`; [saad2003iterative] (4.13)).  It is
`Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq` for the identity
`Matrix.ringInverse_ssorSplitting_m`. -/
theorem ssorSplitting_iterationOperator_eq_mul (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    {ω : 𝕜} (hω : ω ≠ 0) (hω2 : ω ≠ 2) :
    (ssorSplitting A h hω hω2).iterationOperator =
      (backwardSorSplitting A h hω).iterationOperator *
        (sorSplitting A h hω).iterationOperator :=
  Splitting.iterationOperator_eq_mul_of_inverse_m_eq _ _ _ (ringInverse_ssorSplitting_m A h hω hω2)

/-- At `ω = 1` the SSOR preconditioner is the symmetric Gauss–Seidel one,
`P_SGS = (D - E) D⁻¹ (D - F)` ([quarteroni2000numerical], the display after (4.21)). -/
theorem ssorSplitting_one_m (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) (h12 : (1 : 𝕜) ≠ 2) :
    (ssorSplitting A h one_ne_zero h12).m
      = (diagPart A + strictLower A) * (diagPart A)⁻¹ * (diagPart A + strictUpper A) := by
  change ((1 : 𝕜) * (2 - 1))⁻¹ • ((diagPart A + (1 : 𝕜) • strictLower A) * (diagPart A)⁻¹ *
    (diagPart A + (1 : 𝕜) • strictUpper A)) = _
  rw [one_smul, one_smul, one_mul, show (2 : 𝕜) - 1 = 1 by norm_num, inv_one, one_smul]

/-- **Jacobi over-relaxation**: the splitting with `M = ω⁻¹ D` of a matrix with invertible diagonal.
Its iteration operator is the relaxation `(1 - ω) + ω B` of the Jacobi one
(`Matrix.jorSplitting_iterationOperator`), so `ω = 1` is Jacobi itself. -/
noncomputable def jorSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0) :
    Splitting A :=
  ⟨ω⁻¹ • diagPart A, by
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hω)).map (algebraMap 𝕜 (Matrix n n 𝕜))).mul h⟩

omit [LinearOrder n] in
/-- The inverse of a nonzero scalar multiple of a unit. -/
private theorem ringInverse_smul {c : 𝕜} (hc : c ≠ 0) {m : Matrix n n 𝕜} (hm : IsUnit m) :
    Ring.inverse (c • m) = c⁻¹ • Ring.inverse m := by
  have h1 : (c • m) * (c⁻¹ • Ring.inverse m) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, Ring.mul_inverse_cancel _ hm, one_smul]
  have h2 : (c⁻¹ • Ring.inverse m) * (c • m) = 1 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, Ring.inverse_mul_cancel _ hm, one_smul]
  exact Ring.inverse_unit ⟨c • m, c⁻¹ • Ring.inverse m, h1, h2⟩

omit [LinearOrder n] in
/-- The JOR iteration matrix `(1 - ω) 1 + ω B` is the relaxation of the Jacobi iteration matrix `B =
-D⁻¹ (E + F)` towards the identity ([quarteroni2000numerical] (4.12)). -/
theorem jorSplitting_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) :
    (jorSplitting A h hω).iterationOperator
      = (1 - ω) • 1 + ω • (jacobiSplitting A h).iterationOperator := by
  have hm : (jorSplitting A h hω).m = ω⁻¹ • diagPart A := rfl
  have hj : (jacobiSplitting A h).m = diagPart A := rfl
  rw [Splitting.iterationOperator, Splitting.iterationOperator, hm, hj,
    ringInverse_smul (inv_ne_zero hω) h, inv_inv, smul_mul_assoc]
  module

omit [LinearOrder n] in
/-- Jacobi is JOR with `ω = 1`. -/
theorem jorSplitting_one (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    jorSplitting A h one_ne_zero = jacobiSplitting A h := by
  ext : 1
  change (1 : 𝕜)⁻¹ • diagPart A = diagPart A
  rw [inv_one, one_smul]

omit [LinearOrder n] in
/-- The JOR iteration matrix is `1 - ω D⁻¹ A`: Richardson's `1 - α P⁻¹ A` with `P = D` and `α = ω`
([quarteroni2000numerical], the display after (4.12) and §4.3). -/
theorem jorSplitting_iterationOperator_eq_one_sub (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    {ω : 𝕜} (hω : ω ≠ 0) :
    (jorSplitting A h hω).iterationOperator = 1 - ω • ((diagPart A)⁻¹ * A) := by
  have hj : (jacobiSplitting A h).m = diagPart A := rfl
  have h1 : (jacobiSplitting A h).iterationOperator = 1 - (diagPart A)⁻¹ * A := by
    rw [Splitting.iterationOperator, hj, nonsing_inv_eq_ringInverse]
  rw [jorSplitting_iterationOperator, h1]
  module

section Complexify

omit [LinearOrder n] in
/-- **The complexification of a real splitting**: for `s : Splitting A` with `A : Matrix n n ℝ`,
the splitting of `complexify A` with `m = complexify s.m`.  Its iteration operator is the
complexification of `s.iterationOperator` (`Stationary.Splitting.complexify_iterationOperator`), so
`Matrix.complexSpectralRadius s.iterationOperator` is the spectral radius of `s.complexify`'s
iteration operator (`Stationary.Splitting.complexSpectralRadius_iterationOperator`): this is how a
real splitting reaches the complex convergence theory. -/
noncomputable def _root_.Stationary.Splitting.complexify {A : Matrix n n ℝ} (s : Splitting A) :
    Splitting (Matrix.complexify A) :=
  ⟨Matrix.complexify s.m, (isUnit_complexify_iff _).mpr s.isUnit⟩

omit [LinearOrder n] in
/-- The `m` of the complexified splitting is the complexification of `m`. -/
@[simp]
theorem _root_.Stationary.Splitting.complexify_m {A : Matrix n n ℝ} (s : Splitting A) :
    s.complexify.m = Matrix.complexify s.m := rfl

omit [LinearOrder n] in
/-- The iteration operator of the complexified splitting is the complexification of the iteration
operator. -/
theorem _root_.Stationary.Splitting.complexify_iterationOperator {A : Matrix n n ℝ}
    (s : Splitting A) : s.complexify.iterationOperator = Matrix.complexify s.iterationOperator := by
  rw [Splitting.iterationOperator, Splitting.iterationOperator, Splitting.complexify_m,
    complexify_one_sub_inverse_mul]

omit [LinearOrder n] in
/-- The complex spectral radius of the iteration matrix of a real splitting is the spectral radius
of the iteration matrix of its complexification. -/
theorem _root_.Stationary.Splitting.complexSpectralRadius_iterationOperator {A : Matrix n n ℝ}
    (s : Splitting A) :
    complexSpectralRadius s.iterationOperator =
      spectralRadius ℂ s.complexify.iterationOperator := by
  rw [complexSpectralRadius, Splitting.complexify_iterationOperator]

omit [LinearOrder n] in
/-- The Jacobi iteration matrix of `complexify A` is the complexification of that of `A`. -/
theorem complexify_jacobi_iterationOperator (A : Matrix n n ℝ) (h : IsUnit (diagPart A))
    (h' : IsUnit (diagPart (complexify A))) :
    complexify (jacobiSplitting A h).iterationOperator =
      (jacobiSplitting (complexify A) h').iterationOperator := by
  have e1 : (jacobiSplitting A h).iterationOperator = 1 - Ring.inverse (diagPart A) * A := rfl
  have e2 : (jacobiSplitting (complexify A) h').iterationOperator
      = 1 - Ring.inverse (diagPart (complexify A)) * complexify A := rfl
  rw [e1, e2, ← complexify_diagPart, complexify_one_sub_inverse_mul]

/-- The Gauss–Seidel iteration matrix of `complexify A` is the complexification of that of `A`. -/
theorem complexify_gaussSeidel_iterationOperator (A : Matrix n n ℝ) (h : IsUnit (diagPart A))
    (h' : IsUnit (diagPart (complexify A))) :
    complexify (gaussSeidelSplitting A h).iterationOperator =
      (gaussSeidelSplitting (complexify A) h').iterationOperator := by
  have e1 : (gaussSeidelSplitting A h).iterationOperator
      = 1 - Ring.inverse (diagPart A + strictLower A) * A := rfl
  have e2 : (gaussSeidelSplitting (complexify A) h').iterationOperator
      = 1 - Ring.inverse (diagPart (complexify A) + strictLower (complexify A)) * complexify A :=
    rfl
  rw [e1, e2, ← complexify_diagPart, ← complexify_strictLower, ← complexify_add,
    complexify_one_sub_inverse_mul]

/-- The SOR iteration matrix of `complexify A` is the complexification of that of `A`. -/
theorem complexify_sor_iterationOperator (A : Matrix n n ℝ) (h : IsUnit (diagPart A))
    (h' : IsUnit (diagPart (complexify A))) {ω : ℝ} (hω : ω ≠ 0) :
    complexify (sorSplitting A h hω).iterationOperator =
      (sorSplitting (complexify A) h' (Complex.ofReal_ne_zero.mpr hω)).iterationOperator := by
  have e1 : (sorSplitting A h hω).iterationOperator
      = 1 - Ring.inverse (ω⁻¹ • diagPart A + strictLower A) * A := rfl
  have e2 : (sorSplitting (complexify A) h' (Complex.ofReal_ne_zero.mpr hω)).iterationOperator
      = 1 - Ring.inverse ((ω : ℂ)⁻¹ • diagPart (complexify A) + strictLower (complexify A))
        * complexify A := rfl
  rw [e1, e2, ← complexify_diagPart, ← complexify_strictLower, ← Complex.ofReal_inv,
    ← complexify_smul, ← complexify_add, complexify_one_sub_inverse_mul]

end Complexify

end Matrix
