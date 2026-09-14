import Mathlib.Analysis.Matrix.Order
import Numlib.Analysis.InnerProductSpace.Energy
import Numlib.LinearAlgebra.Matrix.Cholesky
import Numlib.LinearAlgebra.Matrix.Complexify
import Numlib.LinearAlgebra.Matrix.DiagDominant
import Numlib.LinearAlgebra.Matrix.MMatrix
import NumlibSurface.QuarteroniSaccoSaleri.Chapter01.Section10

/-!
# Quarteroni–Sacco–Saleri §1.12: positive definite, diagonally dominant and M-matrices

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §1.12. The book's positive definiteness (Definition 1.22) does not
assume symmetry, so it is a surface definition in two flavours: `IsPositiveDefinite` (in `ℂⁿ`,
"`(A x, x)` real and positive") and `IsPositiveDefiniteReal` (in `ℝⁿ`, "`(A x, x) > 0`"), with
their semidefinite companions. Property 1.17 identifies the complex one with Mathlib's
`Matrix.PosDef` (Hermitian with positive form), Definition 1.22's alignment identifies the real
one with the backbone's coercivity `LinearMap.IsCoercive` of the Euclidean operator
(`Numlib/Analysis/InnerProductSpace/Coercive`). Properties 1.15–1.18 and the remarks after them
come from Mathlib's `PosDef` API and `Numlib/LinearAlgebra/Matrix/Cholesky` (Sylvester's
criterion, the `Hᵀ H` factorization, the entry bounds); the energy norm (1.28) from
`Numlib/Analysis/InnerProductSpace/Energy` and Mathlib's `CFC.sqrt` on matrices; Definition 1.24
and the positive-definiteness criterion for dominant matrices from
`Numlib/LinearAlgebra/Matrix/DiagDominant`; Definition 1.25, the discrete maximum principle and
Properties 1.19–1.20 from `Numlib/LinearAlgebra/Matrix/MMatrix`.

## Contents

* `IsPositiveDefinite`, `IsPositiveSemidefinite`, `IsPositiveDefiniteReal`,
  `IsPositiveSemidefiniteReal`, `definition_1_22`, `example_1_8_matrix`, `example_1_8` —
  Definition 1.22 and the nonsymmetric example (1.27).
* `definition_1_23`, `property_1_15`, `property_1_16`, `property_1_17` — the symmetric and
  skew-symmetric parts, and the Hermitian characterization.
* `property_1_18_quadratic`, `property_1_18_eigenvalues`, `property_1_18_minors`,
  `property_1_18_factor`, `posDef_diag_pos`, `equation_1_28` — the four clauses of Property
  1.18 for symmetric real matrices, the diagonal remarks, the energy norm.
* `definition_1_24`, `posDef_of_isStrictDiagDominant` — diagonal dominance.
* `definition_1_25`, `discreteMaximumPrinciple`, `property_1_19`, `property_1_20` — M-matrices.

## Conventions

The book's `(A x, x)` is `xᴴ A x = star x ⬝ᵥ (A *ᵥ x)` on `ℂⁿ` and `x ⬝ᵥ (A *ᵥ x)` on `ℝⁿ` (the
scalar product being linear in its first argument, as fixed in §1.10). The Loewner order on
matrices needed for the square root `A^{1/2}` is Mathlib's scoped `MatrixOrder`, opened for
`equation_1_28` only. Inequalities between vectors are entrywise.
-/

open Finset Matrix
open scoped ComplexOrder

namespace QuarteroniSaccoSaleri.Chapter01

variable {n : ℕ}

/-! ### Definition 1.22 -/

/-- **Definition 1.22, in `ℂⁿ`.** `A ∈ ℂ^{n×n}` is *positive definite in `ℂⁿ`* when the number
`(A x, x) = xᴴ A x` is real and positive for every `x ≠ 0`. No symmetry is assumed; Property
1.17 derives it. -/
def IsPositiveDefinite (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x : Fin n → ℂ, x ≠ 0 → (star x ⬝ᵥ (A *ᵥ x)).im = 0 ∧ 0 < (star x ⬝ᵥ (A *ᵥ x)).re

/-- **Definition 1.22, semidefinite in `ℂⁿ`.** `A ∈ ℂ^{n×n}` is *positive semidefinite in `ℂⁿ`*
when `(A x, x)` is real and nonnegative for every `x ≠ 0`. -/
def IsPositiveSemidefinite (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x : Fin n → ℂ, x ≠ 0 → (star x ⬝ᵥ (A *ᵥ x)).im = 0 ∧ 0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re

/-- **Definition 1.22, in `ℝⁿ`.** `A ∈ ℝ^{n×n}` is *positive definite in `ℝⁿ`* when
`(A x, x) = xᵀ A x > 0` for every `x ∈ ℝⁿ`, `x ≠ 0`. -/
def IsPositiveDefiniteReal (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x)

/-- **Definition 1.22, semidefinite in `ℝⁿ`.** `A ∈ ℝ^{n×n}` is *positive semidefinite in `ℝⁿ`*
when `(A x, x) ≥ 0` for every `x ≠ 0`. -/
def IsPositiveSemidefiniteReal (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 ≤ x ⬝ᵥ (A *ᵥ x)

/-- **Definition 1.22, aligned with the backbone.** Positive definiteness in `ℝⁿ` is coercivity of
the Euclidean operator `x ↦ A x` (backbone `LinearMap.IsCoercive`, through
`LinearMap.isCoercive_iff_forall_pos` in finite dimension), which is where its consequences
live; positive definiteness of `A` in `ℂⁿ` is positivity of `xᴴ A x` in the order of `ℂ`
(`0 < z` meaning `z` real and positive, Mathlib's `ComplexOrder`); and a real matrix that is
positive definite in `ℂⁿ` is positive definite in `ℝⁿ` (restrict to real vectors) — the
converse fails, Example 1.8. -/
theorem definition_1_22 (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (IsPositiveDefiniteReal A ↔ (toEuclideanLin A).IsCoercive) ∧
      (IsPositiveDefinite B ↔ ∀ x : Fin n → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (B *ᵥ x)) ∧
      (IsPositiveDefinite (complexify A) → IsPositiveDefiniteReal A) := by
  refine ⟨?_, ?_, fun h x hx => ?_⟩
  · rw [LinearMap.isCoercive_iff_forall_pos]
    constructor
    · intro h x hx
      have := h (WithLp.ofLp x) (fun h0 => hx ((WithLp.ofLp_eq_zero 2).1 h0))
      rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin, star_trivial]
      simpa using this
    · intro h x hx
      have := h (WithLp.toLp 2 x) (fun h0 => hx ((WithLp.toLp_eq_zero 2).1 h0))
      rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin, star_trivial] at this
      simpa using this
  · refine forall_congr' fun x => imp_congr_right fun _ => ?_
    rw [Complex.lt_def]
    simp only [Complex.zero_re, Complex.zero_im]
    exact ⟨fun h => ⟨h.2, h.1.symm⟩, fun h => ⟨h.2.symm, h.1⟩⟩
  · have hz : (fun i => (x i : ℂ)) ≠ 0 := fun h0 =>
      hx (funext fun i => by simpa using congrFun h0 i)
    have := (h _ hz).2
    rw [re_star_dotProduct_complexify_mulVec] at this
    simpa using this

/-- The matrix `A = [[2, α], [-2 - α, 2]]` of Example 1.8, (1.27). -/
def example_1_8_matrix (α : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![2, α; -2 - α, 2]

/-- **Example 1.8, (1.27).** Matrices that are positive definite in `ℝⁿ` are not necessarily
symmetric: for every `α`, `A = [[2, α], [-2 - α, 2]]` has `(A x, x) = 2 (x₁² + x₂² - x₁ x₂) > 0`
for every nonnull `x ∈ ℝ²`, so it is positive definite in `ℝ²`; it is not symmetric when
`α ≠ -1`; and then it is not positive definite in `ℂ²`, since at `x = (1, i)` the number
`(A x, x) = 4 + (2α + 2) i` is not real. -/
theorem example_1_8 (α : ℝ) :
    (∀ x : Fin 2 → ℝ,
        x ⬝ᵥ (example_1_8_matrix α *ᵥ x) = 2 * (x 0 ^ 2 + x 1 ^ 2 - x 0 * x 1)) ∧
      IsPositiveDefiniteReal (example_1_8_matrix α) ∧
      (α ≠ -1 → ¬ (example_1_8_matrix α).IsSymm) ∧
      (star ![1, Complex.I] ⬝ᵥ (complexify (example_1_8_matrix α) *ᵥ ![1, Complex.I])).im =
        2 * α + 2 ∧
      (α ≠ -1 → ¬ IsPositiveDefinite (complexify (example_1_8_matrix α))) := by
  have hq : ∀ x : Fin 2 → ℝ,
      x ⬝ᵥ (example_1_8_matrix α *ᵥ x) = 2 * (x 0 ^ 2 + x 1 ^ 2 - x 0 * x 1) := fun x => by
    simp [example_1_8_matrix, dotProduct, mulVec, Fin.sum_univ_two]
    ring
  have him : (star ![1, Complex.I] ⬝ᵥ
      (complexify (example_1_8_matrix α) *ᵥ ![1, Complex.I])).im = 2 * α + 2 := by
    rw [im_star_dotProduct_complexify_mulVec]
    simp [example_1_8_matrix, dotProduct, mulVec, Fin.sum_univ_two]
    ring
  refine ⟨hq, fun x hx => ?_, fun hα hS => hα ?_, him, fun hα h => ?_⟩
  · rw [hq]
    have h0 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
    have : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      rcases h0 with h0 | h0 <;> positivity
    nlinarith [sq_nonneg (x 0 - x 1)]
  · have := hS.apply 0 1
    simp [example_1_8_matrix] at this
    linarith
  · have hne : ![(1 : ℂ), Complex.I] ≠ 0 := fun h0 => by
      have := congrFun h0 0
      simp at this
    have := (h _ hne).1
    rw [him] at this
    exact hα (by linarith)

/-! ### Definition 1.23 and Properties 1.15–1.17 -/

/-- **Definition 1.23.** The *symmetric part* `A_S = ½ (A + Aᵀ)` and the *skew-symmetric part*
`A_SS = ½ (A - Aᵀ)` of a real matrix are Mathlib's `selfAdjointPart ℝ A` and
`skewAdjointPart ℝ A` on the star module `ℝ^{n×n}` (where `star A = Aᵀ`); `A = A_S + A_SS`
(`StarModule.selfAdjointPart_add_skewAdjointPart`). For a complex matrix the same with `Aᴴ`,
`ℂ^{n×n}` being a star module over `ℝ`. -/
theorem definition_1_23 (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (selfAdjointPart ℝ A : Matrix (Fin n) (Fin n) ℝ) = (1 / 2 : ℝ) • (A + Aᵀ) ∧
      (skewAdjointPart ℝ A : Matrix (Fin n) (Fin n) ℝ) = (1 / 2 : ℝ) • (A - Aᵀ) ∧
      (selfAdjointPart ℝ A : Matrix (Fin n) (Fin n) ℝ) + skewAdjointPart ℝ A = A ∧
      (selfAdjointPart ℝ B : Matrix (Fin n) (Fin n) ℂ) = (1 / 2 : ℝ) • (B + Bᴴ) ∧
      (skewAdjointPart ℝ B : Matrix (Fin n) (Fin n) ℂ) = (1 / 2 : ℝ) • (B - Bᴴ) ∧
      (selfAdjointPart ℝ B : Matrix (Fin n) (Fin n) ℂ) + skewAdjointPart ℝ B = B := by
  refine ⟨?_, ?_, StarModule.selfAdjointPart_add_skewAdjointPart ℝ A, ?_, ?_,
    StarModule.selfAdjointPart_add_skewAdjointPart ℝ B⟩ <;>
    simp only [selfAdjointPart_apply_coe, skewAdjointPart_apply_coe, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, invOf_eq_inv, one_div]

/-- **Property 1.15.** A real matrix `A` of order `n` is positive definite (in `ℝⁿ`) iff its
symmetric part `A_S` is positive definite: since `xᵀ A_SS x = 0` for every `x` (the quadratic
form of a skew-symmetric matrix vanishes), `xᵀ A x = xᵀ A_S x`. The book's instance: the
symmetric part of the matrix (1.27) is `[[2, -1], [-1, 2]]` for every `α`. -/
theorem property_1_15 (A : Matrix (Fin n) (Fin n) ℝ) (α : ℝ) :
    (∀ x : Fin n → ℝ, x ⬝ᵥ (((1 / 2 : ℝ) • (A - Aᵀ)) *ᵥ x) = 0) ∧
      (∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (((1 / 2 : ℝ) • (A + Aᵀ)) *ᵥ x)) ∧
      (IsPositiveDefiniteReal A ↔ IsPositiveDefiniteReal ((1 / 2 : ℝ) • (A + Aᵀ))) ∧
      (1 / 2 : ℝ) • (example_1_8_matrix α + (example_1_8_matrix α)ᵀ) = !![2, -1; -1, 2] := by
  have hT : ∀ x : Fin n → ℝ, x ⬝ᵥ (Aᵀ *ᵥ x) = x ⬝ᵥ (A *ᵥ x) := fun x => by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hS : ∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (((1 / 2 : ℝ) • (A + Aᵀ)) *ᵥ x) := fun x => by
    rw [smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add, hT, smul_eq_mul]
    ring
  refine ⟨fun x => ?_, hS, ?_, ?_⟩
  · rw [smul_mulVec, dotProduct_smul, sub_mulVec, dotProduct_sub, hT, sub_self, smul_zero]
  · exact ⟨fun h x hx => (hS x).symm ▸ h x hx, fun h x hx => (hS x) ▸ h x hx⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [example_1_8_matrix] <;> ring

/-- **Property 1.16.** Let `A ∈ ℂ^{n×n}` (respectively `A ∈ ℝ^{n×n}`); if `(A x, x)` is real for
every `x ∈ ℂⁿ` then `A` is Hermitian (respectively symmetric). Mathlib's
`LinearMap.isSymmetric_iff_inner_map_self_real` for the Euclidean operator; the converse is
`Matrix.IsHermitian.im_star_dotProduct_mulVec_self`. -/
theorem property_1_16 (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℝ) :
    ((∀ x : Fin n → ℂ, (star x ⬝ᵥ (A *ᵥ x)).im = 0) ↔ A.IsHermitian) ∧
      ((∀ x : Fin n → ℂ, (star x ⬝ᵥ (complexify B *ᵥ x)).im = 0) → B.IsSymm) := by
  have key : ∀ (A : Matrix (Fin n) (Fin n) ℂ),
      (∀ x : Fin n → ℂ, (star x ⬝ᵥ (A *ᵥ x)).im = 0) → A.IsHermitian := fun A h => by
    rw [← isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real]
    intro v
    have hv : inner ℂ (toEuclideanLin A v) v =
        star (star (WithLp.ofLp v) ⬝ᵥ (A *ᵥ WithLp.ofLp v)) := by
      rw [← inner_conj_symm, EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin,
        dotProduct_comm]
      rfl
    rw [hv, Complex.star_def, Complex.conj_conj]
    exact (Complex.conj_eq_iff_im.2 (h _)).symm
  refine ⟨⟨key A, fun hA x => by simpa using hA.im_star_dotProduct_mulVec_self x⟩, fun h => ?_⟩
  exact isHermitian_iff_isSymm.1 ((isHermitian_complexify_iff _).1 (key _ h))

/-- **Property 1.17.** A square matrix `A` of order `n` is positive definite in `ℂⁿ` iff it is
Hermitian and has positive eigenvalues — Mathlib's `Matrix.PosDef`, "Hermitian with positive
form", is the same notion (`Matrix.posDef_iff_dotProduct_mulVec`, with Property 1.16 for the
Hermitian symmetry), and `Matrix.IsHermitian.posDef_iff_eigenvalues_pos` reads it on the
eigenvalues. Thus a positive definite matrix is nonsingular (`Matrix.PosDef.isUnit`). -/
theorem property_1_17 (A : Matrix (Fin n) (Fin n) ℂ) :
    (IsPositiveDefinite A ↔ A.PosDef) ∧
      (A.PosDef ↔ ∃ hA : A.IsHermitian, ∀ i, 0 < hA.eigenvalues i) ∧
      (IsPositiveDefinite A → IsUnit A) := by
  have h1 : IsPositiveDefinite A ↔ A.PosDef := by
    rw [posDef_iff_dotProduct_mulVec, (definition_1_22 0 A).2.1]
    constructor
    · intro h
      refine ⟨(property_1_16 A 0).1.1 fun x => ?_, fun x hx => h x hx⟩
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      · exact ((Complex.lt_def.1 (h x hx)).2).symm
    · exact fun h x hx => h.2 hx
  exact ⟨h1, ⟨fun h => ⟨h.1, h.eigenvalues_pos⟩, fun ⟨hA, h⟩ => hA.posDef_iff_eigenvalues_pos.2 h⟩,
    fun h => (h1.1 h).isUnit⟩

/-! ### Property 1.18 -/

/-- **Property 1.18 (1).** Let `A ∈ ℝ^{n×n}` be symmetric. Then `A` is positive definite (in the
sense of Mathlib's `Matrix.PosDef`, that is, in `ℂⁿ` by Property 1.17) iff `(A x, x) > 0` for
every nonnull `x ∈ ℝⁿ` — positivity of the real quadratic form suffices
(`Matrix.posDef_iff_dotProduct_mulVec` with `star = id` over `ℝ`). -/
theorem property_1_18_quadratic {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.PosDef ↔ IsPositiveDefiniteReal A := by
  rw [posDef_iff_dotProduct_mulVec, isHermitian_iff_isSymm]
  simp only [star_trivial]
  exact ⟨fun h x hx => h.2 hx, fun h => ⟨hA, fun x hx => h x hx⟩⟩

/-- **Property 1.18 (2).** A symmetric real matrix is positive definite iff the eigenvalues of
all its principal submatrices `A(s, s)`, `s ⊆ {1, …, n}`, are positive (backbone
`Matrix.posDef_iff_forall_principalSubmatrix_eigenvalues_pos`). -/
theorem property_1_18_eigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.PosDef ↔ ∀ (s : Finset (Fin n)) (i : s),
      0 < ((isHermitian_iff_isSymm.2 hA).submatrix (Subtype.val : s → Fin n)).eigenvalues i :=
  posDef_iff_forall_principalSubmatrix_eigenvalues_pos (isHermitian_iff_isSymm.2 hA)

/-- **Property 1.18 (3), Sylvester's criterion.** A symmetric real matrix is positive definite
iff its dominant principal minors `d_k = det A(1:k, 1:k)`, `k = 1, …, n`, are all positive
(backbone `Matrix.posDef_iff_forall_det_leadingPrincipalSubmatrix_pos`, the leading principal
submatrix of order `k + 1` being `A.leadingPrincipalSubmatrix k` for `k : Fin n`). -/
theorem property_1_18_minors {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.PosDef ↔ ∀ k : Fin n, 0 < (A.leadingPrincipalSubmatrix k).det :=
  posDef_iff_forall_det_leadingPrincipalSubmatrix_pos (isHermitian_iff_isSymm.2 hA)

/-- **Property 1.18 (4).** A real matrix is positive definite iff `A = Hᵀ H` for a nonsingular
`H` (backbone `Matrix.posDef_iff_exists_isUnit_conjTranspose_mul_self`; the book assumes `A`
symmetric, which neither direction needs: `Hᵀ H` is symmetric, and a positive definite matrix is
symmetric by definition). -/
theorem property_1_18_factor (A : Matrix (Fin n) (Fin n) ℝ) :
    A.PosDef ↔ ∃ H : Matrix (Fin n) (Fin n) ℝ, IsUnit H ∧ A = Hᵀ * H := by
  rw [posDef_iff_exists_isUnit_conjTranspose_mul_self]
  simp only [conjTranspose_eq_transpose_of_trivial, eq_comm]

/-- **§1.12, after Property 1.18.** All the diagonal entries of a positive definite matrix are
positive, `eᵢᵀ A eᵢ = aᵢᵢ > 0` (`Matrix.PosDef.diag_pos`); and the entry of largest modulus of a
symmetric positive definite matrix is a diagonal entry: `|aᵢⱼ| ≤ max(aᵢᵢ, aⱼⱼ)` for all `i, j`
(backbone `Matrix.PosDef.norm_apply_le_max_re_diag`). These are necessary conditions for positive
definiteness. -/
theorem posDef_diag_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    (∀ i, 0 < A i i) ∧ ∀ i j, |A i j| ≤ max (A i i) (A j j) :=
  ⟨fun _ => hA.diag_pos, fun i j => by simpa using hA.norm_apply_le_max_re_diag i j⟩

open scoped MatrixOrder in
/-- **(1.28), the energy norm.** If `A` is symmetric positive definite, `A^{1/2}` is the only
positive definite solution of the matrix equation `X² = A` (Mathlib's `CFC.sqrt A` in the
Loewner order, `CFC.sqrt_eq_iff`), and `‖x‖_A = ‖A^{1/2} x‖₂ = (A x, x)^{1/2}` — the backbone's
`energyNorm (toEuclideanLin A) x` — defines a vector norm, the *energy norm* of `x`: it is the
norm of the energy space `WithEnergy` of `Numlib/Analysis/InnerProductSpace/Energy`, through
`Matrix.posDef_iff_isSymmetricCoercive`. The *energy scalar product* `(x, y)_A = (A x, y)` is
`energyInner (toEuclideanLin A) x y`. -/
theorem equation_1_28 {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    (∀ X : Matrix (Fin n) (Fin n) ℝ, X.PosDef ∧ X ^ 2 = A ↔ X = CFC.sqrt A) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        energyNorm (toEuclideanLin A) x = ‖toEuclideanLin (CFC.sqrt A) x‖ ∧
          energyNorm (toEuclideanLin A) x = √(inner ℝ x (toEuclideanLin A x))) ∧
      (∀ x : EuclideanSpace ℝ (Fin n),
        ‖WithEnergy.equiv (toEuclideanLin A) ((posDef_iff_isSymmetricCoercive A).1 hA) x‖ =
          energyNorm (toEuclideanLin A) x) ∧
      ∀ x y : EuclideanSpace ℝ (Fin n),
        energyInner (toEuclideanLin A) x y = inner ℝ y (toEuclideanLin A x) := by
  have hA0 : 0 ≤ A := nonneg_iff_posSemidef.2 hA.posSemidef
  have hsq : CFC.sqrt A ^ 2 = A := CFC.sq_sqrt A hA0
  have hS : (CFC.sqrt A).PosSemidef := nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)
  refine ⟨fun X => ⟨fun ⟨hX, hX2⟩ => ?_, fun hX => ?_⟩, fun x => ⟨?_, ?_⟩,
    fun x => WithEnergy.norm_equiv _ _ x, fun x y => real_inner_comm _ _⟩
  · exact ((CFC.sqrt_eq_iff A X hA0 (nonneg_iff_posSemidef.2 hX.posSemidef)).2
      (by rw [← sq, hX2])).symm
  · subst hX
    refine ⟨hS.posDef_iff_isUnit.2 ?_, hsq⟩
    have : IsUnit (CFC.sqrt A ^ 2) := by rw [hsq]; exact hA.isUnit
    exact (isUnit_pow_iff two_ne_zero).1 this
  · rw [energyNorm, norm_eq_sqrt_real_inner, RCLike.re_to_real, ← hS.1.eq,
      toEuclideanLin_conjTranspose_inner_left, ← toEuclideanLin_mul_apply, hS.1.eq, ← sq, hsq,
      real_inner_comm]
  · rw [energyNorm, RCLike.re_to_real, real_inner_comm]

/-! ### Definition 1.24: diagonal dominance -/

/-- **Definition 1.24.** `A ∈ ℝ^{n×n}` is *diagonally dominant by rows* when
`|aᵢᵢ| ≥ ∑_{j ≠ i} |aᵢⱼ|` for every `i`, *by columns* when `|aᵢᵢ| ≥ ∑_{j ≠ i} |aⱼᵢ|`, and
*strictly* diagonally dominant (by rows or columns) when the inequalities are strict: the
backbone's `Matrix.IsDiagDominant`, `Matrix.IsColDiagDominant`, `Matrix.IsStrictDiagDominant`
and `Matrix.IsStrictColDiagDominant` of `Numlib/LinearAlgebra/Matrix/DiagDominant`. -/
theorem definition_1_24 (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.IsDiagDominant ↔ ∀ i, ∑ j ∈ univ.erase i, |A i j| ≤ |A i i|) ∧
      (A.IsColDiagDominant ↔ ∀ i, ∑ j ∈ univ.erase i, |A j i| ≤ |A i i|) ∧
      (A.IsStrictDiagDominant ↔ ∀ i, ∑ j ∈ univ.erase i, |A i j| < |A i i|) ∧
      (A.IsStrictColDiagDominant ↔ ∀ i, ∑ j ∈ univ.erase i, |A j i| < |A i i|) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- **§1.12, after Definition 1.24.** A strictly diagonally dominant matrix that is symmetric
with positive diagonal entries is positive definite (backbone
`Matrix.IsStrictDiagDominant.posDef`, by Gershgorin's theorem). -/
theorem posDef_of_isStrictDiagDominant {A : Matrix (Fin n) (Fin n) ℝ} (hS : A.IsSymm)
    (hd : A.IsStrictDiagDominant) (hpos : ∀ i, 0 < A i i) : A.PosDef :=
  hd.posDef (isHermitian_iff_isSymm.2 hS) fun i => by simpa using hpos i

/-! ### Definition 1.25: M-matrices -/

/-- **Definition 1.25.** A nonsingular `A ∈ ℝ^{n×n}` is an *M-matrix* when `aᵢⱼ ≤ 0` for `i ≠ j`
and all the entries of its inverse are nonnegative: the backbone's `Matrix.IsMMatrix`, whose
three fields are these conditions (`Matrix.EntrywiseNonneg` is entrywise nonnegativity). -/
theorem definition_1_25 (A : Matrix (Fin n) (Fin n) ℝ) :
    A.IsMMatrix ↔ IsUnit A ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧ ∀ i j, 0 ≤ A⁻¹ i j :=
  ⟨fun h => ⟨h.isUnit, h.offDiag_nonpos, fun i j => h.inv_entrywiseNonneg.apply i j⟩,
    fun ⟨hu, hoff, hinv⟩ => ⟨hoff, hu, entrywiseNonneg_iff.2 hinv⟩⟩

/-- **§1.12, the discrete maximum principle.** If `A` is an M-matrix and `A x ≤ 0`, then `x ≤ 0`,
the inequalities being meant componentwise (backbone `Matrix.IsMMatrix.nonpos_of_mulVec_nonpos`:
`x = A⁻¹ (A x)` and `A⁻¹ ≥ 0`). -/
theorem discreteMaximumPrinciple {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsMMatrix)
    {x : Fin n → ℝ} (hx : A *ᵥ x ≤ 0) : x ≤ 0 :=
  hA.nonpos_of_mulVec_nonpos hx

/-- **Property 1.19 (M-criterion).** Let `A` satisfy `aᵢⱼ ≤ 0` for `i ≠ j`. Then `A` is an
M-matrix iff there is a vector `w > 0` such that `A w > 0` (backbone
`Matrix.isMMatrix_iff_exists_pos_mulVec_pos`). -/
theorem property_1_19 {A : Matrix (Fin n) (Fin n) ℝ} (hoff : ∀ i j, i ≠ j → A i j ≤ 0) :
    A.IsMMatrix ↔ ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ ∀ i, 0 < (A *ᵥ w) i :=
  isMMatrix_iff_exists_pos_mulVec_pos hoff

/-- **Property 1.20.** A matrix `A ∈ ℝ^{n×n}` that is strictly diagonally dominant by rows and
whose entries satisfy `aᵢⱼ ≤ 0` for `i ≠ j` and `aᵢᵢ > 0` is an M-matrix (backbone
`Matrix.IsStrictDiagDominant.isMMatrix`: under these hypotheses every row sum is positive, so
this is Property 1.19 with `w = (1, …, 1)`). -/
theorem property_1_20 {A : Matrix (Fin n) (Fin n) ℝ} (hd : A.IsStrictDiagDominant)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (hpos : ∀ i, 0 < A i i) : A.IsMMatrix :=
  hd.isMMatrix hpos hoff

end QuarteroniSaccoSaleri.Chapter01
