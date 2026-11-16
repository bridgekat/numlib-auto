/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Numlib.Analysis.Matrix.Function.Basic
import Numlib.Eigen.Normal

/-!
# The primary and the continuous functional calculus of a matrix agree

A matrix has two functional calculi: the primary functional calculus `pfc`, which evaluates at the
matrix the Hermite interpolant of $f$ on the spectrum, and Mathlib's continuous functional calculus
`cfc`. This file shows that the two agree on the matrices where both are defined. For a normal
matrix $A \in \mathbb{C}^{n \times n}$ and every $f : \mathbb{C} \to \mathbb{C}$,
`cfc f A = pfc f A`. For a Hermitian matrix $A$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and
every $f : \mathbb{R} \to \mathbb{R}$, the continuous functional calculus of $A$ at $f$ is the
primary functional calculus at $z \mapsto f(\operatorname{Re} z)$. In particular, the positive
semidefinite square root of a positive semidefinite matrix is the primary square root.

No continuity or smoothness hypothesis on $f$ is needed: the spectrum is finite, and both calculi
use $f$ only at the eigenvalues.

## Main results

* `Matrix.IsHermitian.cfc_eq_pfc`: for a Hermitian matrix $A$ and $f : \mathbb{R} \to \mathbb{R}$,
  `cfc f A` is `pfc` of $z \mapsto f(\operatorname{Re} z)$ at $A$.
* `Matrix.IsStarNormal.cfc_eq_pfc`: for a normal complex matrix $A$ and
  $f : \mathbb{C} \to \mathbb{C}$, `cfc f A = pfc f A`.
* `Matrix.PosSemidef.cfcSqrt_eq_pfc`: for a positive semidefinite matrix $A$, `CFC.sqrt A` is `pfc`
  of $z \mapsto \sqrt{\operatorname{Re} z}$ at $A$.

## Proof outline

Both proofs diagonalize the matrix by a unitary similarity. The primary functional calculus commutes
with the similarity (`AlgEquiv.map_pfc`), and its value at a diagonal matrix is known
(`Matrix.pfc_diagonal`). The normal case reaches `cfc` through an interpolating polynomial
(`cfc_congr`, `cfc_polynomial`).

## Implementation notes

* For a normal matrix, `cfc` uses the C⋆-algebra structure of `Matrix n n ℂ` with the operator norm
  induced by the Euclidean norm, from `open scoped Matrix.Norms.L2Operator`. For a Hermitian matrix,
  `cfc` is Mathlib's Hermitian calculus, which needs no scoped instance.
-/

open Polynomial Hermite

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Hermitian matrices.** Let $A$ be a Hermitian matrix over $\mathbb{K} = \mathbb{R}$ or
$\mathbb{C}$, and let $f : \mathbb{R} \to \mathbb{R}$. Then the continuous functional calculus
of $A$ at $f$ is the primary functional calculus of $A$ at the function
$z \mapsto f(\operatorname{Re} z)$ on $\mathbb{K}$. -/
theorem IsHermitian.cfc_eq_pfc {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : cfc f A = pfc (fun z : 𝕜 => ((f (RCLike.re z) : ℝ) : 𝕜)) A := by
  set φ := Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) hA.eigenvectorUnitary
  rw [hA.cfc_eq, IsHermitian.cfc]
  conv_rhs => rw [hA.spectral_theorem]
  rw [← φ.coe_toAlgEquiv, ← AlgEquiv.map_pfc, pfc_diagonal]
  congr 2
  funext i
  simp

section Normal

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.instCStarAlgebra

/-- **Normal matrices.** Let $A \in \mathbb{C}^{n \times n}$ be normal and let
$f : \mathbb{C} \to \mathbb{C}$. Then the continuous functional calculus of $A$ at $f$ is the
primary functional calculus of $A$ at $f$.

The continuous functional calculus is that of the C⋆-algebra structure of `Matrix n n ℂ` with
the scoped operator norm `Matrix.Norms.L2Operator`. -/
theorem IsStarNormal.cfc_eq_pfc {A : Matrix n n ℂ} (hA : IsStarNormal A) (f : ℂ → ℂ) :
    cfc f A = pfc f A := by
  classical
  obtain ⟨U, hU, d, hd⟩ := Matrix.IsStarNormal.spectral_theorem.mp hA
  set u : unitary (Matrix n n ℂ) := ⟨U, hU⟩
  set φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u
  have hA' : A = φ (diagonal d) := by
    have h2 : U * star U = 1 := (Unitary.mem_iff.1 hU).2
    rw [Unitary.conjStarAlgAut_apply, ← hd, ← star_eq_conjTranspose]
    change A = U * (star U * A * U) * star U
    rw [← mul_assoc, ← mul_assoc, h2, one_mul, mul_assoc, h2, mul_one]
  set s := (Finset.univ.image d).val
  set p := interpolateJet s (taylorJet f)
  have hp : ∀ i, p.eval (d i) = f (d i) := fun i =>
    eval_interpolateJet_taylorJet (Finset.mem_image_of_mem d (Finset.mem_univ i))
  have hσ : spectrum ℂ A = Set.range d := by
    rw [hA', ← φ.coe_toAlgEquiv, AlgEquiv.spectrum_eq, spectrum_diagonal]
  have hpd : (fun z => p.eval z) ∘ d = f ∘ d := funext hp
  have hL : cfc f A = aeval A p := by
    rw [cfc_congr (g := fun z => p.eval z) ?_, cfc_polynomial p A hA]
    rw [hσ]
    rintro _ ⟨i, rfl⟩
    exact (hp i).symm
  rw [hL, hA', ← φ.coe_toAlgEquiv, ← AlgEquiv.map_pfc,
    ← pfc_polynomial (Algebra.IsIntegral.isIntegral _) (IsAlgClosed.splits _),
    ← AlgEquiv.map_pfc, pfc_diagonal, pfc_diagonal]
  rw [hpd]

end Normal

open scoped ComplexOrder MatrixOrder in
/-- **The positive semidefinite square root is the primary square root.** Let $A$ be a positive
semidefinite matrix over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$. Then the positive
semidefinite square root `CFC.sqrt A` is the primary functional calculus of $A$ at
$z \mapsto \sqrt{\operatorname{Re} z}$.

The polar factor $(A^H A)^{1/2}$ uses this result. -/
theorem PosSemidef.cfcSqrt_eq_pfc {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    CFC.sqrt A = pfc (fun z : 𝕜 => ((Real.sqrt (RCLike.re z) : ℝ) : 𝕜)) A := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A hA.nonneg, hA.isHermitian.cfc_eq_pfc]
  congr 1
  funext z
  rw [Real.sqrt]

end Matrix
