import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Numlib.Analysis.Matrix.Function.Basic
import Numlib.Eigen.Normal

/-!
# The primary and the continuous functional calculus of a matrix agree

On the matrices where both are defined, the primary functional calculus `pfc` (Hermite
interpolation on the spectrum) agrees with Mathlib's continuous functional calculus `cfc`:

* `Matrix.IsStarNormal.cfc_eq_pfc`: normal complex matrices, under the C⋆-algebra structure of
  `open scoped Matrix.Norms.L2Operator`, for any `f : ℂ → ℂ`;
* `Matrix.IsHermitian.cfc_eq_pfc`: Hermitian matrices over any `RCLike` field, with Mathlib's
  unscoped Hermitian calculus, for `f : ℝ → ℝ` read on `𝕜` as `z ↦ f (re z)`;
* `Matrix.PosSemidef.cfcSqrt_eq_pfc`: the positive semidefinite square root `CFC.sqrt` is the
  primary square root of `Real.sqrt`.

No continuity or smoothness hypothesis appears: the spectrum is finite and both calculi read `f`
only at the eigenvalues. Both proofs diagonalize by a unitary similarity, which `pfc` commutes
with (`AlgEquiv.map_pfc`), and compute `pfc` of a diagonal matrix (`Matrix.pfc_diagonal`); the
normal case reaches `cfc` through an interpolating polynomial (`cfc_congr`, `cfc_polynomial`).
-/

open Polynomial Hermite

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Hermitian matrices**: the continuous functional calculus of a Hermitian matrix at a real
function `f` is the primary functional calculus at `z ↦ f (re z)`. -/
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

/-- **Normal matrices**: under the C⋆-algebra structure of `Matrix n n ℂ` (the scoped `ℓ²`
operator norm), the continuous functional calculus of a normal matrix is the primary functional
calculus, for every `f : ℂ → ℂ`. -/
theorem IsStarNormal.cfc_eq_pfc {A : Matrix n n ℂ} (hA : IsStarNormal A) (f : ℂ → ℂ) :
    cfc f A = pfc f A := by
  classical
  obtain ⟨U, hU, d, hd⟩ := Matrix.IsStarNormal.spectral_theorem.mp hA
  set u : unitary (Matrix n n ℂ) := ⟨U, hU⟩
  set φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u
  have hA' : A = φ (diagonal d) := by
    have h1 : star U * U = 1 := (Unitary.mem_iff.1 hU).1
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
/-- **The positive semidefinite square root is the primary one**: `CFC.sqrt A` is `pfc` of
`z ↦ √(re z)`. Consumer: the polar factor `(AᴴA)^{1/2}`. -/
theorem PosSemidef.cfcSqrt_eq_pfc {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    CFC.sqrt A = pfc (fun z : 𝕜 => ((Real.sqrt (RCLike.re z) : ℝ) : 𝕜)) A := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A hA.nonneg, hA.isHermitian.cfc_eq_pfc]
  congr 1
  funext z
  rw [Real.sqrt]

end Matrix
