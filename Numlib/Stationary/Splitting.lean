/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg
import Numlib.Stationary.Basic

/-!
# Splittings and the classical iterations

Let $a$ be an element of a ring. A **splitting** of $a$ is a decomposition $a = m - n$ in which $m$
is a unit. The splitting determines the stationary iteration $x_{k+1} = m^{-1}(n x_k + b)$ for the
equation $a x = b$, whose **iteration operator** is $G = m^{-1} n = 1 - m^{-1} a$. This module
defines splittings in any ring and constructs the classical splittings of a square matrix
$A = D + L + U$, with $D$ the diagonal part, $L$ the strictly lower triangular part and $U$ the
strictly upper triangular part of $A$: Jacobi ($m = D$), Gauss–Seidel ($m = D + L$), SOR
($m = \omega^{-1} D + L$), the backward variants, SSOR, Jacobi over-relaxation (JOR,
$m = \omega^{-1} D$) and Richardson ($m = \alpha^{-1}$). The presentation follows
[saad2003iterative], §4.1, with material from [kress1998numerical], §4.1–4.2, [han2009theoretical],
§5.2.2, [higham2002accuracy], Chapter 17, and [quarteroni2000numerical], §4.2.

Two splittings $a = m_1 - n_1 = m_2 - n_2$ applied one after the other give again the iteration of a
splitting, with $m = m_1 (m_1 + m_2 - a)^{-1} m_2$. The symmetric methods are instances of this
composition: SSOR is a forward SOR sweep followed by a backward one, and its preconditioner at
$\omega = 1$ is the symmetric Gauss–Seidel preconditioner $(D + L) D^{-1} (D + U)$. The Jacobi,
Gauss–Seidel and SOR iteration matrices of a real matrix commute with complexification, so their
spectral radii can be computed by the complex theory.

## Main definitions

* `Stationary.Splitting`: a splitting $a = m - n$ with $m$ a unit, stored as $m$ alone.
* `Stationary.Splitting.iterationOperator`: the iteration operator $G = 1 - m^{-1} a$.
* `Stationary.Splitting.map`: the image of a splitting under a ring homomorphism.
* `Matrix.jacobiSplitting`, `Matrix.gaussSeidelSplitting`, `Matrix.sorSplitting`,
  `Matrix.backwardGaussSeidelSplitting`, `Matrix.backwardSorSplitting`, `Matrix.ssorSplitting`,
  `Matrix.jorSplitting`: the classical splittings of a matrix with invertible diagonal.
* `Stationary.Splitting.richardson`: Richardson's splitting $m = \alpha^{-1}$.
* `Stationary.Splitting.complexify`: the complexification of a splitting of a real matrix.

## Main results

* `Stationary.Splitting.eq_iterationOperator_mul_add_iff`: consistency, $x = G x + m^{-1} b$ if and
  only if $a x = b$.
* `Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq`: if three splittings satisfy
  $m_t^{-1} = m_2^{-1} (m_1 + m_2 - a) m_1^{-1}$, then $G_t = G_2 G_1$.
* `Matrix.jacobiSplitting_iterationOperator`, `Matrix.sorSplitting_iterationOperator`,
  `Matrix.backwardSorSplitting_iterationOperator`, `Matrix.jorSplitting_iterationOperator`: the
  classical iteration matrices.
* `Matrix.ssorSplitting_iterationOperator_eq_mul`: the SSOR iteration matrix is the product of the
  backward and the forward SOR iteration matrices.
* `Matrix.ssorSplitting_one_m`: at $\omega = 1$ the SSOR preconditioner is $(D + L) D^{-1} (D + U)$.
* `Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one`: if $\rho(G) < 1$, the
  iterates converge to $A^{-1} b$ from every starting vector.
* `Matrix.complexify_jacobi_iterationOperator`, `Matrix.complexify_gaussSeidel_iterationOperator`:
  the Jacobi and Gauss–Seidel iteration matrices commute with complexification.

## Implementation notes

* The parts $D$, $L$, $U$ of $A$ are `Matrix.diagPart A`, `Matrix.strictLower A` and
  `Matrix.strictUpper A`, and $I$ is the identity matrix.
* A splitting stores only $m$ and the proof that $m$ is a unit. The part $n$ is defined as $m - a$,
  and the inverse $m^{-1}$ is `Ring.inverse`.
* [saad2003iterative] writes $A = D - E - F$, with $-E$ and $-F$ the strictly lower and the strictly
  upper triangular parts. Thus $E = -L$ and $F = -U$, and for example the SOR matrix $D - \omega E$
  of the source is $D + \omega L$ here.
* [han2009theoretical] writes a splitting as $A = N - M$, which exchanges the roles of the letters
  $m$ and $n$.
* The spectral radius of a real matrix is `Matrix.complexSpectralRadius`, the spectral radius of its
  complexification.
-/

namespace Stationary

variable {R : Type*} [Ring R]

/-- A **splitting** of an element $a$ of a ring $R$ is a decomposition $a = m - n$ in which $m$ is a
unit. It consists of $m$ and the proof that $m$ is a unit; the part $n$ is then $m - a$
(`Stationary.Splitting.n`). -/
@[ext]
structure Splitting (a : R) where
  /-- The invertible part $m$ of the splitting $a = m - n$. -/
  m : R
  /-- The part $m$ is a unit of $R$. -/
  isUnit : IsUnit m

namespace Splitting

variable {a : R} (s : Splitting a)

/-- The complementary part $n = m - a$ of a splitting $a = m - n$. -/
def n : R := s.m - a

/-- For a splitting $a = m - n$, the identity $m - n = a$ holds.

Only $m$ is stored, and $n$ is defined as $m - a$, so this is the statement that a splitting of
$a$ indeed splits $a$. -/
theorem m_sub_n : s.m - s.n = a := sub_sub_cancel _ _

/-- The **iteration operator** of a splitting $a = m - n$ is
$$G = 1 - m^{-1} a,$$
which equals $m^{-1} n$ (`Stationary.Splitting.iterationOperator_eq`). This is the iteration
matrix of [saad2003iterative], (4.28) and (4.30).

The inverse $m^{-1}$ is `Ring.inverse`. -/
noncomputable def iterationOperator : R := 1 - Ring.inverse s.m * a

/-- For a splitting $a = m - n$, the two formulas for the iteration operator agree:
$$1 - m^{-1} a = m^{-1} n.$$

The first formula is the definition. The second is the form in which the classical iteration
matrices are read off from `Stationary.Splitting.n`. -/
theorem iterationOperator_eq : s.iterationOperator = Ring.inverse s.m * s.n := by
  rw [iterationOperator, Splitting.n, mul_sub, Ring.inverse_mul_cancel _ s.isUnit]

/-- For a splitting $a = m - n$ with iteration operator $G$,
$$1 - G = m^{-1} a.$$

Together with `Stationary.Splitting.eq_iterationOperator_mul_add_iff`, this says that $m$
preconditions $a$ and that the fixed points of the iteration are the solutions of $a x = b$. -/
theorem one_sub_iterationOperator : 1 - s.iterationOperator = Ring.inverse s.m * a := by
  rw [iterationOperator, sub_sub_cancel]

/-- **Consistency** of a splitting iteration. Let $a = m - n$ be a splitting with iteration operator
$G$, and let $x, b \in R$. Then
$$x = G x + m^{-1} b \iff a x = b.$$

This is the form in the ring $R$. For the action of an operator ring on a space, see
`Stationary.step`. -/
theorem eq_iterationOperator_mul_add_iff (x b : R) :
    x = s.iterationOperator * x + Ring.inverse s.m * b ↔ a * x = b := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := a * x),
    show x - (s.iterationOperator * x + Ring.inverse s.m * b)
      = Ring.inverse s.m * (a * x - b) by rw [iterationOperator]; noncomm_ring,
    s.isUnit.ringInverse.mul_right_eq_zero]

/-- **Richardson's splitting** of an element $a$ of a $\mathbb{K}$-algebra $R$, for a scalar
$\alpha \neq 0$ of a field $\mathbb{K}$: the splitting with $m = \alpha^{-1} \cdot 1$. -/
noncomputable def richardson {𝕜 : Type*} [Field 𝕜] [Algebra 𝕜 R] (a : R) {α : 𝕜} (hα : α ≠ 0) :
    Splitting a :=
  ⟨α⁻¹ • (1 : R), by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.mpr (inv_ne_zero hα)).map (algebraMap 𝕜 R)⟩

/-- The iteration operator of Richardson's splitting with parameter $\alpha \neq 0$ is
$$G = 1 - \alpha a.$$

The step is therefore $x \mapsto x + \alpha (b - a x)$: a fixed step length $\alpha$ along the
residual, with no preconditioner other than the scalar. -/
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

/-- For splittings with parts $m_1$ and $m_2$ of $a$, $m_2^{-1} (m_1 + m_2 - a) m_1^{-1} =
m_2^{-1} + m_1^{-1} - m_2^{-1} a m_1^{-1}$. -/
private theorem inverse_mul_add_sub_mul_inverse (s₁ s₂ : Splitting a) :
    Ring.inverse s₂.m * (s₁.m + s₂.m - a) * Ring.inverse s₁.m
      = Ring.inverse s₂.m + Ring.inverse s₁.m - Ring.inverse s₂.m * a * Ring.inverse s₁.m := by
  rw [mul_sub, mul_add, sub_mul, add_mul, mul_assoc (Ring.inverse s₂.m) s₁.m,
    Ring.mul_inverse_cancel _ s₁.isUnit, mul_one, Ring.inverse_mul_cancel _ s₂.isUnit, one_mul]

/-- **Composition of two splittings.** Let $a = m_1 - n_1$, $a = m_2 - n_2$ and $a = m_t - n_t$ be
three splittings of $a$, with iteration operators $G_1$, $G_2$ and $G_t$. If
$$m_t^{-1} = m_2^{-1} (m_1 + m_2 - a) m_1^{-1},$$
then
$$G_t = G_2 G_1.$$
Thus one step of the first splitting followed by one step of the second is one step of the
third. When $m_1 + m_2 - a$ is a unit, the hypothesis says $m_t = m_1 (m_1 + m_2 - a)^{-1} m_2$.

The proof expands the hypothesis to $m_t^{-1} = m_2^{-1} + m_1^{-1} - m_2^{-1} a m_1^{-1}$, so
that $1 - m_t^{-1} a = (1 - m_2^{-1} a)(1 - m_1^{-1} a)$. This identity eliminates the half-step
$x_{k+1/2}$ in every symmetric method ([quarteroni2000numerical], §4.2.6; [saad2003iterative],
(4.13)–(4.14) and (4.27)). -/
theorem iterationOperator_eq_mul_of_inverse_m_eq (s₁ s₂ t : Splitting a)
    (ht : Ring.inverse t.m = Ring.inverse s₂.m * (s₁.m + s₂.m - a) * Ring.inverse s₁.m) :
    t.iterationOperator = s₂.iterationOperator * s₁.iterationOperator := by
  rw [iterationOperator, iterationOperator, iterationOperator, ht,
    inverse_mul_add_sub_mul_inverse s₁ s₂]
  noncomm_ring

/-- The constant term of a composite splitting. Let $a = m_1 - n_1$, $a = m_2 - n_2$ and
$a = m_t - n_t$ be splittings of $a$, and let $G_2$ be the iteration operator of the second. If
$m_t^{-1} = m_2^{-1} (m_1 + m_2 - a) m_1^{-1}$, then
$$m_t^{-1} = G_2 m_1^{-1} + m_2^{-1}.$$

With `Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq`, this shows that the two
steps $x \mapsto G_2 (G_1 x + m_1^{-1} b) + m_2^{-1} b$ are the single step
$x \mapsto G_t x + m_t^{-1} b$. -/
theorem inverse_m_eq_iterationOperator_mul_inverse_add (s₁ s₂ t : Splitting a)
    (ht : Ring.inverse t.m = Ring.inverse s₂.m * (s₁.m + s₂.m - a) * Ring.inverse s₁.m) :
    Ring.inverse t.m = s₂.iterationOperator * Ring.inverse s₁.m + Ring.inverse s₂.m := by
  rw [ht, inverse_mul_add_sub_mul_inverse s₁ s₂, iterationOperator]
  noncomm_ring

section Map

variable {S F : Type*} [Ring S] [FunLike F R S] [RingHomClass F R S]

/-- The image of a splitting under a ring homomorphism $f : R \to S$: the splitting
$f(a) = f(m) - f(n)$ of $f(a)$, with part $f(m)$.

The two uses are the complexification of a splitting of a real matrix and the passage from a
matrix to the operator that it induces on `EuclideanSpace`. -/
def map (f : F) (s : Splitting a) : Splitting (f a) := ⟨f s.m, s.isUnit.map f⟩

/-- The part $m$ of the image of a splitting under $f$ is $f(m)$. -/
@[simp]
theorem map_m (f : F) (s : Splitting a) : (s.map f).m = f s.m := rfl

/-- The part $n$ of the image of a splitting under $f$ is $f(n)$. -/
theorem map_n (f : F) (s : Splitting a) : (s.map f).n = f s.n := by
  rw [Splitting.n, Splitting.n, map_m, map_sub]

/-- A ring homomorphism maps `Ring.inverse` of a unit $m$ to `Ring.inverse` of $f(m)$. -/
private theorem map_ringInverse (f : F) {m : R} (hm : IsUnit m) :
    f (Ring.inverse m) = Ring.inverse (f m) := by
  obtain ⟨u, rfl⟩ := hm
  rw [show f (u : R) = ((Units.map (f : R →* S) u : Sˣ) : S) from rfl, Ring.inverse_unit,
    Ring.inverse_unit, Units.coe_map_inv]
  rfl

/-- The iteration operator of the image of a splitting under a ring homomorphism $f$ is $f(G)$,
where $G$ is the iteration operator of the splitting. -/
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

/-- Let $A$ be a square matrix over a field whose diagonal part $D$ is invertible, let $L$ be its
strictly lower triangular part, and let $c, d$ be scalars with $c \neq 0$. Then $c D + d L$ is
invertible.

Every lower triangular part $m$ of the splittings below has this form: it is lower triangular
with diagonal $c D$. -/
theorem isUnit_smul_diagPart_add_smul_strictLower (A : Matrix n n 𝕜) {c d : 𝕜} (hc : c ≠ 0)
    (h : IsUnit (diagPart A)) : IsUnit (c • diagPart A + d • strictLower A) := by
  have hT : (c • diagPart A + d • strictLower A).IsLowerTriangular := fun i j hij => by
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp [hij'.ne, asymm hij']
  have hd : ∀ i, (c • diagPart A + d • strictLower A) i i ≠ 0 := fun i => by
    simpa using mul_ne_zero hc ((isUnit_diagPart_iff A).mp h i)
  convert (hT.isUnit_iff).2 hd

/-- Let $A$ be a square matrix over a field whose diagonal part $D$ is invertible, let $U$ be its
strictly upper triangular part, and let $c, d$ be scalars with $c \neq 0$. Then $c D + d U$ is
invertible.

This is the upper triangular counterpart of `Matrix.isUnit_smul_diagPart_add_smul_strictLower`,
used for the backward sweeps. -/
theorem isUnit_smul_diagPart_add_smul_strictUpper (A : Matrix n n 𝕜) {c d : 𝕜} (hc : c ≠ 0)
    (h : IsUnit (diagPart A)) : IsUnit (c • diagPart A + d • strictUpper A) := by
  have hT : (c • diagPart A + d • strictUpper A).IsUpperTriangular := fun i j hij => by
    have hij' : j < i := hij
    simp [hij'.ne', asymm hij']
  have hd : ∀ i, (c • diagPart A + d • strictUpper A) i i ≠ 0 := fun i => by
    simpa using mul_ne_zero hc ((isUnit_diagPart_iff A).mp h i)
  convert (hT.isUnit_iff).2 hd

/-- Let $A$ be a square matrix over a field whose diagonal part $D$ is invertible, and let $L$ be
its strictly lower triangular part. Then $D + \omega L$ is invertible for every scalar $\omega$.

The matrix $D + \omega L$ is $D - \omega E$ in the notation of [saad2003iterative]. It is lower
triangular with the diagonal of $A$, and it is the matrix that the SOR sweep inverts. -/
theorem isUnit_diagPart_add_smul_strictLower {A : Matrix n n 𝕜} (h : IsUnit (diagPart A))
    (ω : 𝕜) : IsUnit (diagPart A + ω • strictLower A) := by
  simpa using isUnit_smul_diagPart_add_smul_strictLower (c := 1) (d := ω) A one_ne_zero h

/-- Let $A$ be a square matrix over a field whose diagonal part $D$ is invertible, and let $U$ be
its strictly upper triangular part. Then $D + \omega U$ is invertible for every scalar $\omega$.

The matrix $D + \omega U$ is $D - \omega F$ in the notation of [saad2003iterative]. It is the
matrix that the backward SOR sweep inverts. -/
theorem isUnit_diagPart_add_smul_strictUpper {A : Matrix n n 𝕜} (h : IsUnit (diagPart A))
    (ω : 𝕜) : IsUnit (diagPart A + ω • strictUpper A) := by
  simpa using isUnit_smul_diagPart_add_smul_strictUpper (c := 1) (d := ω) A one_ne_zero h

/-- Let $A$ be a square matrix over a field whose diagonal part $D$ is invertible, and let $L$ be
its strictly lower triangular part. Then $D + L$ is invertible.

The matrix $D + L$ is $D - E$ in the notation of [saad2003iterative]. It is lower triangular
with the diagonal of $A$, and its invertibility makes the Gauss–Seidel splitting well defined. -/
theorem isUnit_diagPart_add_strictLower {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart A + strictLower A) := by
  simpa using isUnit_diagPart_add_smul_strictLower h 1

/-- Let $A$ be a square matrix over a field whose diagonal part $D$ is invertible, and let $U$ be
its strictly upper triangular part. Then $D + U$ is invertible.

The matrix $D + U$ is $D - F$ in the notation of [saad2003iterative]. Its invertibility makes
the backward Gauss–Seidel splitting well defined. -/
theorem isUnit_diagPart_add_strictUpper {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    IsUnit (diagPart A + strictUpper A) := by
  simpa using isUnit_diagPart_add_smul_strictUpper h 1

/-- The **Jacobi splitting** of a square matrix $A$ with invertible diagonal part $D$: the splitting
$A = m - n$ with $m = D$.

In the notation $A = D - E - F$ of [saad2003iterative], (4.5), this is $M = D$ and $N = E + F$. -/
noncomputable def jacobiSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) : Splitting A :=
  ⟨diagPart A, h⟩

/-- The part $n$ of the Jacobi splitting of $A$ is $-(L + U)$, where $L$ and $U$ are the strictly
lower and the strictly upper triangular parts of $A$. This is $N = E + F$ in the notation of
[saad2003iterative]. -/
theorem jacobiSplitting_n (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    (jacobiSplitting A h).n = -(strictLower A + strictUpper A) := by
  change diagPart A - A = -(strictLower A + strictUpper A)
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, ← add_assoc,
    diagPart_add_strictLower_add_strictUpper, sub_self]

/-- The iteration matrix of the Jacobi splitting of a square matrix $A$ with invertible diagonal
part $D$ is
$$G_J = -D^{-1} (L + U),$$
where $L$ and $U$ are the strictly lower and the strictly upper triangular parts of $A$.

This is $D^{-1}(E + F)$ in the notation of [saad2003iterative], (4.7). -/
theorem jacobiSplitting_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    (jacobiSplitting A h).iterationOperator =
      -(diagPart A)⁻¹ * (strictLower A + strictUpper A) := by
  have hm : (jacobiSplitting A h).m = diagPart A := rfl
  rw [Splitting.iterationOperator_eq, jacobiSplitting_n, hm, nonsing_inv_eq_ringInverse, neg_mul,
    mul_neg]

/-- The **Gauss–Seidel splitting** of a square matrix $A$ with invertible diagonal part $D$: the
splitting $A = m - n$ with $m = D + L$, where $L$ is the strictly lower triangular part of $A$.

In the notation $A = D - E - F$ of [saad2003iterative], (4.6), this is $M = D - E$ and $N = F$. -/
noncomputable def gaussSeidelSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    Splitting A :=
  ⟨diagPart A + strictLower A, isUnit_diagPart_add_strictLower h⟩

/-- The part $n$ of the Gauss–Seidel splitting of $A$ is $-U$, where $U$ is the strictly upper
triangular part of $A$.

This is $N = F$ in the notation of [saad2003iterative]. The forward sweep takes the whole lower
triangle, and only the strictly upper part remains on the right-hand side. -/
theorem gaussSeidelSplitting_n (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    (gaussSeidelSplitting A h).n = -strictUpper A := by
  change diagPart A + strictLower A - A = -strictUpper A
  rw [eq_neg_iff_add_eq_zero, sub_add_eq_add_sub, diagPart_add_strictLower_add_strictUpper,
    sub_self]

/-- The **backward Gauss–Seidel splitting** of a square matrix $A$ with invertible diagonal part
$D$: the splitting $A = m - n$ with $m = D + U$, where $U$ is the strictly upper triangular part
of $A$.

In the notation $A = D - E - F$ of [saad2003iterative], §4.1, this is $M = D - F$, the backward
sweep. -/
noncomputable def backwardGaussSeidelSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    Splitting A :=
  ⟨diagPart A + strictUpper A, isUnit_diagPart_add_strictUpper h⟩

/-- The **SOR splitting** (successive over-relaxation) of a square matrix $A$ with invertible
diagonal part $D$, with parameter $\omega \neq 0$: the splitting $A = m - n$ with
$$m = \omega^{-1} D + L,$$
where $L$ is the strictly lower triangular part of $A$.

In the notation $A = D - E - F$ of [saad2003iterative], (4.11)–(4.12), this is
$M = \omega^{-1}(D - \omega E)$. -/
noncomputable def sorSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0) :
    Splitting A :=
  ⟨ω⁻¹ • diagPart A + strictLower A, by
    simpa using isUnit_smul_diagPart_add_smul_strictLower (d := 1) A (inv_ne_zero hω) h⟩

omit [LinearOrder n] in
/-- Let $A = D + L + U$ with $D$ the diagonal part of $A$, and let $s$ be a splitting of $A$ with
$m = \omega^{-1} D + L$, $\omega \neq 0$. Then the iteration operator of $s$ is $(D + \omega
L)^{-1} ((1 - \omega) D - \omega U)$; this covers the forward and the backward SOR splittings. -/
private theorem iterationOperator_eq_of_m_eq_smul_diagPart_add {A L U : Matrix n n 𝕜}
    (s : Splitting A) {ω : 𝕜} (hω : ω ≠ 0) (hA : diagPart A + L + U = A)
    (hm : s.m = ω⁻¹ • diagPart A + L) :
    s.iterationOperator = (diagPart A + ω • L)⁻¹ * ((1 - ω) • diagPart A - ω • U) := by
  generalize diagPart A = D at hA hm ⊢
  subst hA
  have hMdet : IsUnit s.m.det := (isUnit_iff_isUnit_det _).mp s.isUnit
  have h1 : D + ω • L = ω • s.m := by
    rw [hm, smul_add, smul_smul, mul_inv_cancel₀ hω, one_smul]
  have h2 : (1 - ω) • D - ω • U = ω • s.n := by
    rw [Splitting.n, hm, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hω, one_smul]
    module
  have h3 : (ω • s.m)⁻¹ = ω⁻¹ • s.m⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hω, nonsing_inv_mul _ hMdet, one_smul]
  rw [Splitting.iterationOperator_eq, h1, h2, h3, smul_mul_smul_comm, inv_mul_cancel₀ hω,
    one_smul, nonsing_inv_eq_ringInverse]

/-- The iteration matrix of the SOR splitting of a square matrix $A$ with invertible diagonal part
$D$, with parameter $\omega \neq 0$, is
$$G_\omega = (D + \omega L)^{-1} \bigl((1 - \omega) D - \omega U\bigr),$$
where $L$ and $U$ are the strictly lower and the strictly upper triangular parts of $A$.

This is $(D - \omega E)^{-1} (\omega F + (1 - \omega) D)$ in the notation of
[saad2003iterative], (4.14). -/
theorem sorSplitting_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) :
    (sorSplitting A h hω).iterationOperator =
      (diagPart A + ω • strictLower A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A) :=
  iterationOperator_eq_of_m_eq_smul_diagPart_add _ hω (diagPart_add_strictLower_add_strictUpper A)
    rfl

/-- The **SSOR splitting** (symmetric successive over-relaxation) of a square matrix $A$ with
invertible diagonal part $D$, with parameter $\omega \notin \{0, 2\}$: the splitting $A = m - n$
with
$$m = \frac{1}{\omega (2 - \omega)} (D + \omega L) D^{-1} (D + \omega U),$$
where $L$ and $U$ are the strictly lower and the strictly upper triangular parts of $A$.

In the notation $A = D - E - F$ of [saad2003iterative], (4.27), this is $M = \frac{1}{\omega(2 -
\omega)} (D - \omega E) D^{-1} (D - \omega F)$. One step is a forward SOR sweep followed by a
backward one (`Matrix.ssorSplitting_iterationOperator_eq_mul`). -/
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
    exact (isUnit_smul_iff (Units.mk0 _
      (inv_ne_zero (mul_ne_zero hω (sub_ne_zero_of_ne hω2.symm)))) _).2 ((hu1.mul hu2).mul hu3)⟩

/-- The SOR splitting with $\omega = 1$ is the Gauss–Seidel splitting. -/
theorem sorSplitting_one (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    sorSplitting A h one_ne_zero = gaussSeidelSplitting A h := by
  ext : 1
  change (1 : 𝕜)⁻¹ • diagPart A + strictLower A = diagPart A + strictLower A
  rw [inv_one, one_smul]

/-- The **backward SOR splitting** of a square matrix $A$ with invertible diagonal part $D$, with
parameter $\omega \neq 0$: the splitting $A = m - n$ with
$$m = \omega^{-1} D + U,$$
where $U$ is the strictly upper triangular part of $A$.

In the notation $A = D - E - F$ this is $M = \omega^{-1}(D - \omega F)$, the mirror image of
`Matrix.sorSplitting`. Its step is the backward SOR method $(D - \omega F) x_{k+1} = [\omega E +
(1 - \omega) D] x_k + \omega b$ of [quarteroni2000numerical], §4.2.6. The case $\omega = 1$ is
`Matrix.backwardGaussSeidelSplitting`. -/
noncomputable def backwardSorSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) : Splitting A :=
  ⟨ω⁻¹ • diagPart A + strictUpper A, by
    simpa using isUnit_smul_diagPart_add_smul_strictUpper (d := 1) A (inv_ne_zero hω) h⟩

/-- The iteration matrix of the backward SOR splitting of a square matrix $A$ with invertible
diagonal part $D$, with parameter $\omega \neq 0$, is
$$(D + \omega U)^{-1} \bigl((1 - \omega) D - \omega L\bigr),$$
where $L$ and $U$ are the strictly lower and the strictly upper triangular parts of $A$.

This is $(D - \omega F)^{-1} (\omega E + (1 - \omega) D)$ in the notation $A = D - E - F$, the
mirror image of `Matrix.sorSplitting_iterationOperator`. -/
theorem backwardSorSplitting_iterationOperator (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    {ω : 𝕜} (hω : ω ≠ 0) :
    (backwardSorSplitting A h hω).iterationOperator =
      (diagPart A + ω • strictUpper A)⁻¹ * ((1 - ω) • diagPart A - ω • strictLower A) :=
  iterationOperator_eq_of_m_eq_smul_diagPart_add _ hω
    (by rw [add_right_comm]; exact diagPart_add_strictLower_add_strictUpper A) rfl

/-- The backward SOR splitting with $\omega = 1$ is the backward Gauss–Seidel splitting. -/
theorem backwardSorSplitting_one (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    backwardSorSplitting A h one_ne_zero = backwardGaussSeidelSplitting A h := by
  ext : 1
  change (1 : 𝕜)⁻¹ • diagPart A + strictUpper A = diagPart A + strictUpper A
  rw [inv_one, one_smul]

/-- Let $A$ be a square matrix with invertible diagonal part $D$, and let $\omega \neq 0$. Let
$M_f = \omega^{-1} D + L$ and $M_b = \omega^{-1} D + U$ be the parts $m$ of the SOR and the
backward SOR splittings. Then
$$M_f + M_b - A = (2 \omega^{-1} - 1) D.$$

This is the term $m_1 + m_2 - a$ of
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

/-- Let $A$ be a square matrix with invertible diagonal part $D$, and let $\omega \notin \{0, 2\}$.
Let $M_f = \omega^{-1} D + L$ and $M_b = \omega^{-1} D + U$ be the parts $m$ of the SOR and the
backward SOR splittings, and let $P$ be the part $m$ of the SSOR splitting. Then
$$P^{-1} = M_b^{-1} (M_f + M_b - A) M_f^{-1}.$$

So the SSOR splitting is the composite of the forward and the backward SOR splittings in the
sense of `Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq`. The reason is that
$M_f + M_b - A = (2/\omega - 1) D$ (`Matrix.sorSplitting_m_add_backwardSorSplitting_m_sub`) and
$P = M_f ((2/\omega - 1) D)^{-1} M_b$ ([quarteroni2000numerical], (4.22)). The inverses are
`Ring.inverse`. -/
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

/-- **SSOR is a forward SOR sweep followed by a backward one.** Let $A$ be a square matrix with
invertible diagonal part $D$, and let $\omega \notin \{0, 2\}$. Then the iteration matrix of the
SSOR splitting is the product of the iteration matrix of the backward SOR splitting and that of
the SOR splitting:
$$B_s(\omega) = (D + \omega U)^{-1} \bigl((1 - \omega) D - \omega L\bigr) (D + \omega L)^{-1}
  \bigl((1 - \omega) D - \omega U\bigr).$$

In the notation $A = D - E - F$ this is $(D - \omega F)^{-1} (\omega E + (1 - \omega) D) (D -
\omega E)^{-1} (\omega F + (1 - \omega) D)$ of [quarteroni2000numerical], §4.2.6; at
$\omega = 1$ it is the matrix $B_{SGS}$ of (4.21) there ([saad2003iterative], (4.13)). The proof
is `Stationary.Splitting.iterationOperator_eq_mul_of_inverse_m_eq` with the identity
`Matrix.ringInverse_ssorSplitting_m`. -/
theorem ssorSplitting_iterationOperator_eq_mul (A : Matrix n n 𝕜) (h : IsUnit (diagPart A))
    {ω : 𝕜} (hω : ω ≠ 0) (hω2 : ω ≠ 2) :
    (ssorSplitting A h hω hω2).iterationOperator =
      (backwardSorSplitting A h hω).iterationOperator *
        (sorSplitting A h hω).iterationOperator :=
  Splitting.iterationOperator_eq_mul_of_inverse_m_eq _ _ _ (ringInverse_ssorSplitting_m A h hω hω2)

/-- Let $A$ be a square matrix with invertible diagonal part $D$. At $\omega = 1$, the part $m$ of
the SSOR splitting is the **symmetric Gauss–Seidel preconditioner**
$$P_{SGS} = (D + L) D^{-1} (D + U),$$
where $L$ and $U$ are the strictly lower and the strictly upper triangular parts of $A$.

This is $(D - E) D^{-1} (D - F)$ in the display after (4.21) of [quarteroni2000numerical]. The
hypothesis $1 \neq 2$ holds in every field; it is the argument $\omega \neq 2$ of
`Matrix.ssorSplitting`. -/
theorem ssorSplitting_one_m (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) (h12 : (1 : 𝕜) ≠ 2) :
    (ssorSplitting A h one_ne_zero h12).m
      = (diagPart A + strictLower A) * (diagPart A)⁻¹ * (diagPart A + strictUpper A) := by
  change ((1 : 𝕜) * (2 - 1))⁻¹ • ((diagPart A + (1 : 𝕜) • strictLower A) * (diagPart A)⁻¹ *
    (diagPart A + (1 : 𝕜) • strictUpper A)) = _
  rw [one_smul, one_smul, one_mul, show (2 : 𝕜) - 1 = 1 by norm_num, inv_one, one_smul]

/-- The **Jacobi over-relaxation (JOR) splitting** of a square matrix $A$ with invertible diagonal
part $D$, with parameter $\omega \neq 0$: the splitting $A = m - n$ with $m = \omega^{-1} D$.

Its iteration matrix is $(1 - \omega) I + \omega G_J$, where $G_J$ is the Jacobi iteration
matrix (`Matrix.jorSplitting_iterationOperator`), so $\omega = 1$ gives the Jacobi splitting. -/
noncomputable def jorSplitting (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜} (hω : ω ≠ 0) :
    Splitting A :=
  ⟨ω⁻¹ • diagPart A, by
    rw [Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hω)).map (algebraMap 𝕜 (Matrix n n 𝕜))).mul h⟩

omit [LinearOrder n] in
/-- For a scalar $c \neq 0$ and an invertible square matrix $m$, $(c\, m)^{-1} = c^{-1} m^{-1}$,
with the inverse `Ring.inverse`. -/
theorem ringInverse_smul {c : 𝕜} (hc : c ≠ 0) {m : Matrix n n 𝕜} (hm : IsUnit m) :
    Ring.inverse (c • m) = c⁻¹ • Ring.inverse m := by
  have h1 : (c • m) * (c⁻¹ • Ring.inverse m) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, Ring.mul_inverse_cancel _ hm, one_smul]
  have h2 : (c⁻¹ • Ring.inverse m) * (c • m) = 1 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, Ring.inverse_mul_cancel _ hm, one_smul]
  exact Ring.inverse_unit ⟨c • m, c⁻¹ • Ring.inverse m, h1, h2⟩

omit [LinearOrder n] in
/-- The iteration matrix of the JOR splitting of a square matrix $A$ with invertible diagonal, with
parameter $\omega \neq 0$, is
$$(1 - \omega) I + \omega G_J,$$
where $G_J = -D^{-1}(L + U)$ is the Jacobi iteration matrix.

This is (4.12) of [quarteroni2000numerical]: the JOR matrix is the relaxation of the Jacobi
matrix towards the identity. -/
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
/-- The JOR splitting with $\omega = 1$ is the Jacobi splitting. -/
theorem jorSplitting_one (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    jorSplitting A h one_ne_zero = jacobiSplitting A h := by
  ext : 1
  change (1 : 𝕜)⁻¹ • diagPart A = diagPart A
  rw [inv_one, one_smul]

omit [LinearOrder n] in
/-- The iteration matrix of the JOR splitting of a square matrix $A$ with invertible diagonal part
$D$, with parameter $\omega \neq 0$, is
$$I - \omega D^{-1} A.$$

This is Richardson's iteration matrix $I - \alpha P^{-1} A$ with $P = D$ and $\alpha = \omega$
([quarteroni2000numerical], the display after (4.12), and §4.3). -/
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
/-- The **complexification of a splitting** of a real square matrix $A$: the splitting of the
complex matrix $A$ (`Matrix.complexify A`) whose part $m$ is the complex matrix $m$.

Its iteration operator is the complexification of the iteration operator of $s$
(`Stationary.Splitting.complexify_iterationOperator`). Therefore `Matrix.complexSpectralRadius`
of the real iteration matrix is the spectral radius of the complex one
(`Stationary.Splitting.complexSpectralRadius_iterationOperator`). This is how a real splitting
reaches the complex convergence theory. -/
noncomputable def _root_.Stationary.Splitting.complexify {A : Matrix n n ℝ} (s : Splitting A) :
    Splitting (Matrix.complexify A) :=
  ⟨Matrix.complexify s.m, (isUnit_complexify_iff _).mpr s.isUnit⟩

omit [LinearOrder n] in
/-- The part $m$ of the complexified splitting is the complexification of $m$. -/
@[simp]
theorem _root_.Stationary.Splitting.complexify_m {A : Matrix n n ℝ} (s : Splitting A) :
    s.complexify.m = Matrix.complexify s.m := rfl

omit [LinearOrder n] in
/-- The iteration operator of the complexification of a splitting of a real matrix is the
complexification of its iteration operator. -/
theorem _root_.Stationary.Splitting.complexify_iterationOperator {A : Matrix n n ℝ}
    (s : Splitting A) : s.complexify.iterationOperator = Matrix.complexify s.iterationOperator := by
  rw [Splitting.iterationOperator, Splitting.iterationOperator, Splitting.complexify_m,
    complexify_one_sub_inverse_mul]

omit [LinearOrder n] in
/-- For a splitting of a real square matrix with iteration matrix $G$, the spectral radius
$\rho(G)$, computed over $\mathbb{C}$ (`Matrix.complexSpectralRadius`), equals the spectral
radius of the iteration matrix of the complexified splitting. -/
theorem _root_.Stationary.Splitting.complexSpectralRadius_iterationOperator {A : Matrix n n ℝ}
    (s : Splitting A) :
    complexSpectralRadius s.iterationOperator =
      spectralRadius ℂ s.complexify.iterationOperator := by
  rw [complexSpectralRadius, Splitting.complexify_iterationOperator]

omit [LinearOrder n] in
/-- Let $A = m - n$ be a splitting of a real square matrix $A$ with iteration matrix $G$. If
$\rho(G) < 1$, then $A$ is invertible.

The reason is that $1 - G = m^{-1} A$ is invertible. -/
theorem _root_.Stationary.Splitting.isUnit_of_complexSpectralRadius_lt_one {A : Matrix n n ℝ}
    (s : Splitting A) (hs : complexSpectralRadius s.iterationOperator < 1) : IsUnit A := by
  have hu := isUnit_one_sub_of_complexSpectralRadius_lt_one hs
  rw [s.one_sub_iterationOperator] at hu
  exact isUnit_of_mul_isUnit_right hu

omit [LinearOrder n] in
/-- **Convergence of a splitting iteration with $\rho(G) < 1$.** Let $A = m - n$ be a splitting of a
real square matrix $A$ with iteration matrix $G = 1 - m^{-1} A$, and suppose that $\rho(G) < 1$.
Then for every $b$ and every starting vector $x_0$, the iterates of the map
$x \mapsto G x + m^{-1} b$ converge to $A^{-1} b$.

This is Theorem 4.1 of [saad2003iterative], §4.2, and Theorem 4.1 of [quarteroni2000numerical].
The error after $k$ steps is $G^k (x_0 - A^{-1} b)$, and $G^k \to 0$ by
`Matrix.tendsto_pow_iff_complexSpectralRadius_lt_one`. The spectral radius is
`Matrix.complexSpectralRadius`. -/
theorem _root_.Stationary.Splitting.tendsto_iterate_of_complexSpectralRadius_lt_one
    {A : Matrix n n ℝ} (s : Splitting A) (hs : complexSpectralRadius s.iterationOperator < 1)
    (b x₀ : n → ℝ) :
    Filter.Tendsto (fun k => (fun x => s.iterationOperator *ᵥ x + s.m⁻¹ *ᵥ b)^[k] x₀)
      Filter.atTop (nhds (A⁻¹ *ᵥ b)) := by
  set G := s.iterationOperator with hGdef
  set xs := A⁻¹ *ᵥ b with hxs
  have hA := s.isUnit_of_complexSpectralRadius_lt_one hs
  have hG : G = 1 - s.m⁻¹ * A := by
    rw [hGdef, Splitting.iterationOperator, nonsing_inv_eq_ringInverse]
  have hAx : A *ᵥ xs = b := by
    rw [hxs, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA), one_mulVec]
  have hfix : G *ᵥ xs + s.m⁻¹ *ᵥ b = xs := by
    rw [hG, sub_mulVec, one_mulVec, ← mulVec_mulVec, hAx, sub_add_cancel]
  have herr : ∀ k, (fun x => G *ᵥ x + s.m⁻¹ *ᵥ b)^[k] x₀ - xs = (G ^ k) *ᵥ (x₀ - xs) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ', ← mulVec_mulVec, ← ih, mulVec_sub]
      calc G *ᵥ (fun x => G *ᵥ x + s.m⁻¹ *ᵥ b)^[k] x₀ + s.m⁻¹ *ᵥ b - xs
          = G *ᵥ (fun x => G *ᵥ x + s.m⁻¹ *ᵥ b)^[k] x₀ + s.m⁻¹ *ᵥ b
              - (G *ᵥ xs + s.m⁻¹ *ᵥ b) := by rw [hfix]
        _ = _ := by abel
  have hpow := (tendsto_pow_iff_complexSpectralRadius_lt_one G).2 hs
  have hc : Continuous fun M : Matrix n n ℝ => M *ᵥ (x₀ - xs) :=
    continuous_id.matrix_mulVec continuous_const
  rw [← tendsto_sub_nhds_zero_iff]
  simpa only [herr, zero_mulVec, Function.comp_def] using (hc.tendsto 0).comp hpow

omit [LinearOrder n] in
/-- For a real square matrix $A$ with invertible diagonal, the complexification of the Jacobi
iteration matrix of $A$ is the Jacobi iteration matrix of the complex matrix $A$. -/
theorem complexify_jacobi_iterationOperator (A : Matrix n n ℝ) (h : IsUnit (diagPart A))
    (h' : IsUnit (diagPart (complexify A))) :
    complexify (jacobiSplitting A h).iterationOperator =
      (jacobiSplitting (complexify A) h').iterationOperator := by
  have e1 : (jacobiSplitting A h).iterationOperator = 1 - Ring.inverse (diagPart A) * A := rfl
  have e2 : (jacobiSplitting (complexify A) h').iterationOperator
      = 1 - Ring.inverse (diagPart (complexify A)) * complexify A := rfl
  rw [e1, e2, ← complexify_diagPart, complexify_one_sub_inverse_mul]

/-- For a real square matrix $A$ with invertible diagonal, the complexification of the Gauss–Seidel
iteration matrix of $A$ is the Gauss–Seidel iteration matrix of the complex matrix $A$. -/
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

/-- For a real square matrix $A$ with invertible diagonal and a real $\omega \neq 0$, the
complexification of the SOR iteration matrix of $A$ is the SOR iteration matrix of the complex
matrix $A$ with the same parameter $\omega$. -/
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
