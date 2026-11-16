/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Upstreaming candidate: general material with no numerical-analysis-specific content, written
to Mathlib conventions with a view to contributing it to Mathlib.
Natural home: `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly` (the polynomial lemmas) and
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse` (the commutation lemmas).
Keep it free of dependencies on the rest of `Numlib` other than other upstreaming candidates.
-/
import Mathlib.Data.Matrix.Block
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Polynomials evaluated at matrices

Let $p$ be a polynomial over a commutative semiring $R$. The evaluation $p(A)$ of $p$ at a square
matrix $A$ (`Polynomial.aeval`) commutes with the structural operations on matrices: it acts
blockwise on block diagonal matrices, it commutes with the transpose, and it commutes with an
entrywise ring homomorphism of the scalars. In particular, a matrix over a field and its transpose
have the same minimal polynomial. The module also proves that an element that commutes with a matrix
$B$ commutes with the inverse $B^{-1}$, and more generally with the ring inverse of an element of a
monoid with zero.

These facts are the algebraic inputs of the matrix forms of the primary functional calculus in
`Numlib.Analysis.Matrix.Function.Basic`.

## Main results

* `Commute.ringInverse_right`, `Commute.ringInverse_left`: if $c$ commutes with $b$ in a monoid with
  zero, then $c$ commutes with the ring inverse of $b$.
* `Matrix.aeval_blockDiagonal'`, `Matrix.aeval_fromBlocks_zero`: $p(\operatorname{diag}(M_1, \dots,
  M_k)) = \operatorname{diag}(p(M_1), \dots, p(M_k))$, and the same for two diagonal blocks.
* `Matrix.aeval_transpose`: $p(A^T) = p(A)^T$.
* `Matrix.map_aeval`: $\varphi(p(A)) = (\varphi p)(\varphi A)$ for a ring homomorphism $\varphi$
  applied entrywise.
* `Matrix.minpoly_transpose`: $A^T$ and $A$ have the same minimal polynomial.
* `Matrix.commute_nonsing_inv_right`, `Matrix.commute_nonsing_inv_left`: if $C$ commutes with $B$,
  then $C$ commutes with $B^{-1}$.

## Implementation notes

* The ring inverse `Ring.inverse b` is $b^{-1}$ if $b$ is a unit and $0$ otherwise. The matrix
  inverse $B^{-1}$ of Mathlib is likewise $0$ when $\det B$ is not a unit. The commutation results
  hold without any invertibility hypothesis because of these conventions.
* `Matrix.map_aeval` is Mathlib's `Polynomial.map_aeval_eq_aeval_map` for the entrywise ring
  homomorphism `RingHom.mapMatrix φ`.
-/

open Polynomial

section RingInverse

variable {M₀ : Type*} [MonoidWithZero M₀] {b c : M₀}

/-- Let $M_0$ be a monoid with zero, and let $b, c \in M_0$. If $c$ commutes with $b$, then $c$
commutes with the ring inverse `Ring.inverse b`, which is $b^{-1}$ if $b$ is a unit and $0$
otherwise.

Mathlib has the two-sided form `Commute.ringInverse_ringInverse`. -/
theorem Commute.ringInverse_right (h : Commute c b) : Commute c (Ring.inverse b) := by
  by_cases hb : IsUnit b
  · obtain ⟨u, rfl⟩ := hb
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hb]
    exact Commute.zero_right c

/-- Let $M_0$ be a monoid with zero, and let $b, c \in M_0$. If $b$ commutes with $c$, then the ring
inverse `Ring.inverse b` commutes with $c$. The ring inverse is $b^{-1}$ if $b$ is a unit and
$0$ otherwise. -/
theorem Commute.ringInverse_left (h : Commute b c) : Commute (Ring.inverse b) c :=
  h.symm.ringInverse_right.symm

end RingInverse

namespace Matrix

section CommSemiring

variable {R : Type*} [CommSemiring R] {n : Type*} [Fintype n] [DecidableEq n]

/-- Let $R$ be a commutative semiring, let $M_i$ be a square matrix over $R$ for each index $i$ of a
finite type, and let $p$ be a polynomial over $R$. Then the polynomial acts blockwise on the
block diagonal matrix:
$$p(\operatorname{diag}(M_i)_i) = \operatorname{diag}(p(M_i))_i.$$
The blocks can have different sizes; the block diagonal matrix is `Matrix.blockDiagonal'`. -/
theorem aeval_blockDiagonal' {o : Type*} [Fintype o] [DecidableEq o] {m : o → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (M : ∀ i, Matrix (m i) (m i) R) (p : R[X]) :
    aeval (blockDiagonal' M) p = blockDiagonal' fun i => aeval (M i) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, ← blockDiagonal'_add]
    congr 1
    funext i
    rw [Pi.add_apply, map_add]
  | monomial k c =>
    simp only [aeval_monomial, ← Algebra.smul_def, ← blockDiagonal'_pow, ← blockDiagonal'_smul]
    rfl

/-- Let $R$ be a commutative semiring, let $B$ and $C$ be square matrices over $R$, and let $p$ be a
polynomial over $R$. Then
$$p\begin{bmatrix} B & 0 \\ 0 & C \end{bmatrix} = \begin{bmatrix} p(B) & 0 \\ 0 & p(C)
  \end{bmatrix}.$$
-/
theorem aeval_fromBlocks_zero {l : Type*} [Fintype l] [DecidableEq l] (B : Matrix l l R)
    (C : Matrix n n R) (p : R[X]) :
    aeval (fromBlocks B 0 0 C) p = fromBlocks (aeval B p) 0 0 (aeval C p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, map_add, map_add, fromBlocks_add]
    simp only [add_zero]
  | monomial k c =>
    simp only [aeval_monomial, ← Algebra.smul_def, fromBlocks_diagonal_pow, fromBlocks_smul,
      smul_zero]

/-- Let $R$ be a commutative semiring, let $A$ be a square matrix over $R$, and let $p$ be a
polynomial over $R$. Then $p(A^T) = p(A)^T$. -/
theorem aeval_transpose (A : Matrix n n R) (p : R[X]) : aeval Aᵀ p = (aeval A p)ᵀ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, map_add, transpose_add]
  | monomial k c =>
    simp only [aeval_monomial, ← Algebra.smul_def, transpose_smul, transpose_pow]

/-- Let $\varphi \colon R \to S$ be a homomorphism of commutative semirings, let $A$ be a square
matrix over $R$, and let $p$ be a polynomial over $R$. Apply $\varphi$ entrywise to matrices and
coefficientwise to polynomials. Then $\varphi(p(A)) = (\varphi p)(\varphi A)$.

This is Mathlib's `Polynomial.map_aeval_eq_aeval_map` for `RingHom.mapMatrix φ`, which carries
the scalar matrices over $R$ to the scalar matrices over $S$. -/
theorem map_aeval {S : Type*} [CommSemiring S] (φ : R →+* S) (A : Matrix n n R) (p : R[X]) :
    (aeval A p).map φ = aeval (A.map φ) (p.map φ) :=
  map_aeval_eq_aeval_map (ψ := φ.mapMatrix) (RingHom.ext fun c => by
    ext i j
    by_cases h : i = j <;> simp [algebraMap_eq_diagonal, h]) p A

end CommSemiring

/-- Let $K$ be a field and let $A$ be a square matrix over $K$. Then $A^T$ and $A$ have the same
minimal polynomial. -/
theorem minpoly_transpose {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : minpoly K Aᵀ = minpoly K A := by
  have hA : IsIntegral K A := Algebra.IsIntegral.isIntegral _
  refine (minpoly.unique K Aᵀ (minpoly.monic hA) ?_ fun q hq h0 => ?_).symm
  · rw [aeval_transpose, minpoly.aeval, transpose_zero]
  · refine minpoly.min K A hq ?_
    rw [← transpose_transpose A, aeval_transpose, h0, transpose_zero]

section CommRing

variable {α : Type*} [CommRing α] {n : Type*} [Fintype n] [DecidableEq n]

/-- Let $\alpha$ be a commutative ring, and let $B$ and $C$ be square matrices over $\alpha$. If $C$
commutes with $B$, then $C$ commutes with the inverse $B^{-1}$.

Here $B^{-1}$ is the inverse of Mathlib, which is $0$ when $\det B$ is not a unit, so $B$ need
not be invertible. -/
theorem commute_nonsing_inv_right {B C : Matrix n n α} (h : Commute C B) : Commute C B⁻¹ := by
  rw [nonsing_inv_eq_ringInverse]
  exact h.ringInverse_right

/-- Let $\alpha$ be a commutative ring, and let $B$ and $C$ be square matrices over $\alpha$. If $B$
commutes with $C$, then the inverse $B^{-1}$ commutes with $C$. Here $B^{-1}$ is $0$ when
$\det B$ is not a unit. -/
theorem commute_nonsing_inv_left {B C : Matrix n n α} (h : Commute B C) : Commute B⁻¹ C :=
  (commute_nonsing_inv_right h.symm).symm

end CommRing

end Matrix
