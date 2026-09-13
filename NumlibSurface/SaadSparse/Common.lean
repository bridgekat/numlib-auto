import Numlib.Analysis.InnerProductSpace.Coercive
import Numlib.Analysis.Matrix.ToEuclideanLin
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.Hessenberg

/-!
# Saad: conventions for the `SaadSparse` surface library

Shared notation and glue lemmas for the surface library of Yousef Saad, *Iterative Methods for
Sparse Linear Systems*, 2nd edition, SIAM, 2003.

Conventions used throughout the library:

* vectors of `ℝⁿ` (`ℂⁿ`) are `EuclideanSpace 𝕜 (Fin n)`, matrices are `Matrix (Fin n) (Fin n) 𝕜`,
  and the book's `A x` is `Matrix.toEuclideanLin A x`, written `A ⬝ x` with the scoped notation
  below;
* componentwise statements use the plain function type `Fin n → 𝕜` with `A *ᵥ x` and `x ⬝ᵥ y`,
  which are related to the Euclidean picture by `WithLp.toLp 2` / `WithLp.ofLp`
  (`Matrix.ofLp_toEuclideanLin`, `Matrix.toEuclideanLin_toLp` of
  `Numlib/Analysis/Matrix/ToEuclideanLin`);
* Saad's inner product `(x, y) = ∑ xᵢ ȳᵢ` is Mathlib's `inner 𝕜 y x` (Mathlib's inner product is
  conjugate-linear in the *first* slot, Saad's in the second); over `ℝ` the two agree;
* `λ_min(H)`, `λ_max(H)` of a Hermitian matrix are `lambdaMin`, `lambdaMax` below, the extreme
  values of `Matrix.IsHermitian.eigenvalues`;
* real matrices are viewed as complex ones through `Matrix.complexify`, and `ρ(A)` is
  `Matrix.complexSpectralRadius A`.

## Notation

`A ⬝ x` is `Matrix.toEuclideanLin A x`, the book's `A x` read on `EuclideanSpace 𝕜 (Fin n)`.  It
is the only notation this library introduces, it is scoped to the `SaadSparse` namespace, and a
file that wants it writes `open scoped SaadSparse`.  Do not confuse it with Mathlib's `x ⬝ᵥ y`
(`Matrix.dotProduct`) or `A *ᵥ x` (`Matrix.mulVec`), which act on the plain function type.
-/

namespace SaadSparse

open Matrix Finset

/-- The book's `A x`: the matrix `A` acting on a vector of `EuclideanSpace 𝕜 (Fin n)`. -/
scoped notation:75 A " ⬝ " x => Matrix.toEuclideanLin A x

section Glue

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- Saad's `(A u, u)` for real `A` is the `dotProduct` `(A *ᵥ u) ⬝ᵥ u`. -/
theorem real_inner_toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u (A ⬝ u) = (A *ᵥ WithLp.ofLp u) ⬝ᵥ WithLp.ofLp u := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Saad's `(A x, y)` for real `A` is the `dotProduct` `(A *ᵥ x) ⬝ᵥ y`. -/
theorem real_inner_toEuclideanLin' (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ y (A ⬝ x) = (A *ᵥ WithLp.ofLp x) ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Saad's `(A u, u)` for real `A`, in Mathlib's argument order `inner ℝ (A u) u`. -/
theorem real_inner_apply_self (A : Matrix (Fin n) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (A ⬝ u) u = (A *ᵥ WithLp.ofLp u) ⬝ᵥ WithLp.ofLp u := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp

/-- Saad's `(A x, y)` for real `A`, in Mathlib's argument order `inner ℝ (A x) y`. -/
theorem real_inner_apply (A : Matrix (Fin n) (Fin n) ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (A ⬝ x) y = WithLp.ofLp y ⬝ᵥ (A *ᵥ WithLp.ofLp x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

omit [RCLike 𝕜] in
/-- `WithLp.toLp 2` is injective, so vector identities transfer between the two pictures. -/
theorem toLp_injective : Function.Injective (WithLp.toLp 2 : (Fin n → 𝕜) → EuclideanSpace 𝕜 _) :=
  fun _ _ h => congrArg WithLp.ofLp h

/-- The squared Euclidean norm as a `dotProduct` (real case). -/
theorem real_norm_sq_eq_dotProduct (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

end Glue

section Eigenvalues

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- `λ_min(H)`: the smallest eigenvalue of a Hermitian matrix. -/
noncomputable def lambdaMin [NeZero n] {H : Matrix (Fin n) (Fin n) 𝕜} (hH : H.IsHermitian) : ℝ :=
  univ.inf' univ_nonempty hH.eigenvalues

/-- `λ_max(H)`: the largest eigenvalue of a Hermitian matrix. -/
noncomputable def lambdaMax [NeZero n] {H : Matrix (Fin n) (Fin n) 𝕜} (hH : H.IsHermitian) : ℝ :=
  univ.sup' univ_nonempty hH.eigenvalues

variable [NeZero n] {H : Matrix (Fin n) (Fin n) 𝕜} (hH : H.IsHermitian)

include hH in
/-- `λ_min(H)` is a lower bound for the spectrum: no eigenvalue of `H` falls below it. -/
theorem lambdaMin_le_eigenvalues (i : Fin n) : lambdaMin hH ≤ hH.eigenvalues i :=
  inf'_le _ (mem_univ i)

include hH in
/-- `λ_max(H)` is an upper bound for the spectrum: no eigenvalue of `H` rises above it. -/
theorem eigenvalues_le_lambdaMax (i : Fin n) : hH.eigenvalues i ≤ lambdaMax hH :=
  le_sup' _ (mem_univ i)

include hH in
/-- `λ_min(H) ≤ λ_max(H)`.  The interval `[λ_min, λ_max]` that carries the quadratic-form bounds
of §1.9.2 is therefore nonempty; this needs `n ≠ 0`, since there must be an eigenvalue between
the two. -/
theorem lambdaMin_le_lambdaMax : lambdaMin hH ≤ lambdaMax hH :=
  (lambdaMin_le_eigenvalues hH ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩).trans
    (eigenvalues_le_lambdaMax hH _)

include hH in
/-- The quadratic-form bounds `λ_min ‖x‖² ≤ (H x, x) ≤ λ_max ‖x‖²` of a Hermitian matrix.  The
two halves are the extremal characterizations (1.38) and (1.40) of Saad §1.9.2, cleared of the
denominator `(x, x)`. -/
theorem isSymmetricBoundedBy_toEuclideanLin :
    (toEuclideanLin H).IsSymmetricBoundedBy (lambdaMin hH) (lambdaMax hH) :=
  hH.isSymmetricBoundedBy_toEuclideanLin fun i =>
    ⟨lambdaMin_le_eigenvalues hH i, eigenvalues_le_lambdaMax hH i⟩

end Eigenvalues

section Complexify

variable {n : ℕ}

/-- The Euclidean norm of `A x` is unchanged by complexification of both. -/
theorem norm_complexify_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ‖(WithLp.toLp 2 (complexify A *ᵥ fun i => (x i : ℂ)) : EuclideanSpace ℂ (Fin n))‖ =
      ‖(WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ (Fin n))‖ := by
  have h : (complexify A *ᵥ fun i => (x i : ℂ)) = fun i => ((A *ᵥ x) i : ℂ) := by
    funext i
    simp [mulVec, dotProduct, complexify]
  rw [h, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp

end Complexify

section PositiveNegativePart

/-! ### Saad's positive and negative parts

Saad writes `(z)⁺ = (z + |z|)/2` and `(z)⁻ = (z - |z|)/2` for the positive and negative parts of a
real number, in the upwind schemes of §2.2.3 and again in the finite volume fluxes of §2.5.  Note
that Saad's negative part is *nonpositive*, unlike Mathlib's `negPart`, which is `max (-z) 0`. -/

/-- Saad's positive part `(z)⁺ = (z + |z|)/2` is `max z 0`. -/
theorem max_zero_eq_half (z : ℝ) : max z 0 = (z + |z|) / 2 := by
  rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> [rw [max_eq_left]; rw [max_eq_right]] <;>
    linarith

/-- Saad's negative part `(z)⁻ = (z - |z|)/2` is `min z 0`. -/
theorem min_zero_eq_half (z : ℝ) : min z 0 = (z - |z|) / 2 := by
  rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> [rw [min_eq_right]; rw [min_eq_left]] <;>
    linarith

end PositiveNegativePart

end SaadSparse
