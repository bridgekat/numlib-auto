import Numlib.Eigen.QRAlgorithm
import Numlib.LinearAlgebra.Matrix.RealSchur
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section03

/-!
# Quarteroni–Sacco–Saleri §5.4: the QR iteration

Surface file for Alfio Quarteroni, Riccardo Sacco and Fausto Saleri, *Numerical Mathematics*
[quarteroni2000numerical], §5.4, over the backbone `Numlib/Eigen/QRAlgorithm` (the QR iteration,
its accumulated unitary factor and the similarity of the iterates) and
`Numlib/LinearAlgebra/Matrix/RealSchur` (the real Schur form).

## Conventions

From this section on the book works with real matrices, `A ∈ ℝ^{n×n}`, which is
`Matrix (Fin n) (Fin n) ℝ`; "orthogonal" is membership in `Matrix.orthogonalGroup (Fin n) ℝ`, that
is `Q Qᵀ = 1`. The QR factorization of a step is the one with a positive diagonal, `Matrix.qrQ`,
`Matrix.qrR` of the backbone (Gram–Schmidt on the columns, which is what Program 28 does with
`mod_grams`); by the uniqueness of that factorization (`Matrix.qr_unique`) a Householder or
Givens factorization gives the same factors at a nonsingular iterate. The iteration (5.32) is
written as the book writes it, as the recursion `qrIterate` starting from `T⁽⁰⁾ = A` (the choice
`Q⁽⁰⁾ = I` of §5.5), and `qrIterate_eq` identifies it with `Matrix.qrIterate`; for a general
orthogonal `Q⁽⁰⁾` the book's iteration is `qrIterate (Q⁽⁰⁾ᵀ A Q⁽⁰⁾)`, which is how (5.33) is
stated.

## Contents

* `qrIterate`, `qrIterate_eq`, `equation_5_32` — the iteration (5.32) and its identification
  with the backbone.
* `equation_5_33` — every iterate is orthogonally similar to `A`, through the accumulated factor
  `Q⁽⁰⁾ Q⁽¹⁾ ⋯ Q⁽ᵏ⁾`.
* `property_5_8` — the real Schur form.

## Readings and errata

Property 5.8 runs two statements together: the existence of the real Schur form (5.34), which is
`property_5_8`, and the claim (5.35) that its orthogonal matrix is the limit of the accumulated
factors `Q⁽⁰⁾ Q⁽¹⁾ ⋯ Q⁽ᵏ⁾` of the *unshifted* iteration (5.32). The second is false as printed:
for the cyclic permutation matrix of Exercise 14 (`exercise_5_14`) every factor `Q⁽ᵏ⁾` is the
matrix itself, so the accumulated product is `Aᵏ`, which cycles with period `3`; and the book's own
Example 5.9 shows iterates that do not approach the real Schur form at all. It is the node
`property_5_8_limit` of the plan, marked wrong and not formalized. In (5.34) "a matrix of order 2
having complex conjugate eigenvalues" is read as "a `2 × 2` real block with no real eigenvalue":
the characteristic polynomial of such a block is a real quadratic without real roots, so its two
complex eigenvalues are conjugate and non-real, and conversely.
-/

open Filter Finset Matrix Topology

namespace QuarteroniSaccoSaleri.Chapter05

variable {N : ℕ}

/-! ### (5.32): the QR iteration -/

/-- **(5.32), the QR iteration** with `Q⁽⁰⁾ = I`, so that `T⁽⁰⁾ = A`. For `k = 1, 2, …`: determine
`Q⁽ᵏ⁾`, `R⁽ᵏ⁾` with `Q⁽ᵏ⁾ R⁽ᵏ⁾ = T⁽ᵏ⁻¹⁾` (the QR factorization, `Matrix.qrQ`, `Matrix.qrR`), then
let `T⁽ᵏ⁾ = R⁽ᵏ⁾ Q⁽ᵏ⁾`. For a general orthogonal `Q⁽⁰⁾` the book's iteration, starting from
`T⁽⁰⁾ = Q⁽⁰⁾ᵀ A Q⁽⁰⁾`, is `qrIterate (Q⁽⁰⁾ᵀ * A * Q⁽⁰⁾)`. -/
noncomputable def qrIterate (A : Matrix (Fin N) (Fin N) ℝ) : ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => A
  | k + 1 => qrR (qrIterate A k) * qrQ (qrIterate A k)

/-- **The book's iteration (5.32) is the backbone's QR algorithm**: `qrIterate A k =
Matrix.qrIterate A k` for every `k`. -/
theorem qrIterate_eq (A : Matrix (Fin N) (Fin N) ℝ) :
    ∀ k, qrIterate A k = Matrix.qrIterate A k
  | 0 => rfl
  | k + 1 => by rw [qrIterate, qrIterate_eq A k, Matrix.qrIterate_succ]

/-- **(5.32), the two phases of a step.** At every step `k` the matrix `T⁽ᵏ⁾` is factored as
`T⁽ᵏ⁾ = Q⁽ᵏ⁺¹⁾ R⁽ᵏ⁺¹⁾` with `Q⁽ᵏ⁺¹⁾ = qrQ (T⁽ᵏ⁾)` orthogonal and `R⁽ᵏ⁺¹⁾ = qrR (T⁽ᵏ⁾)` upper
triangular (`Matrix.qrQ_mul_qrR`, `Matrix.qrQ_mem_unitaryGroup`, `Matrix.isUpperTriangular_qrR`),
and the next iterate is the product in the reverse order, `T⁽ᵏ⁺¹⁾ = R⁽ᵏ⁺¹⁾ Q⁽ᵏ⁺¹⁾`. -/
theorem equation_5_32 (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    qrQ (qrIterate A k) * qrR (qrIterate A k) = qrIterate A k ∧
      qrQ (qrIterate A k) ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      (qrR (qrIterate A k)).IsUpperTriangular ∧
      qrIterate A (k + 1) = qrR (qrIterate A k) * qrQ (qrIterate A k) :=
  ⟨qrQ_mul_qrR _, qrQ_mem_unitaryGroup _, isUpperTriangular_qrR _, rfl⟩

/-! ### (5.33): the iterates are orthogonally similar to `A` -/

/-- **(5.33).** For an orthogonal `Q⁽⁰⁾` and `T⁽⁰⁾ = Q⁽⁰⁾ᵀ A Q⁽⁰⁾`, every iterate `T⁽ᵏ⁾` of (5.32)
is orthogonally similar to `A`: with `Q⁽¹⁾ ⋯ Q⁽ᵏ⁾ = Matrix.qrAccum (T⁽⁰⁾) k` the accumulated factor
of the iteration, the product `Q⁽⁰⁾ Q⁽¹⁾ ⋯ Q⁽ᵏ⁾` is orthogonal and
`T⁽ᵏ⁾ = (Q⁽⁰⁾ Q⁽¹⁾ ⋯ Q⁽ᵏ⁾)ᵀ A (Q⁽⁰⁾ Q⁽¹⁾ ⋯ Q⁽ᵏ⁾)` for every `k ≥ 0`. Backbone
`Matrix.qrIterate_eq_conj_qrAccum` and `Matrix.qrAccum_mem_unitaryGroup`. -/
theorem equation_5_33 (A : Matrix (Fin N) (Fin N) ℝ) {Q₀ : Matrix (Fin N) (Fin N) ℝ}
    (hQ₀ : Q₀ ∈ Matrix.orthogonalGroup (Fin N) ℝ) (k : ℕ) :
    Q₀ * qrAccum (Q₀ᵀ * A * Q₀) k ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      qrIterate (Q₀ᵀ * A * Q₀) k =
        (Q₀ * qrAccum (Q₀ᵀ * A * Q₀) k)ᵀ * A * (Q₀ * qrAccum (Q₀ᵀ * A * Q₀) k) := by
  refine ⟨mul_mem hQ₀ (qrAccum_mem_unitaryGroup _ k), ?_⟩
  rw [qrIterate_eq, qrIterate_eq_conj_qrAccum, conjTranspose_eq_transpose_of_trivial,
    transpose_mul]
  simp only [Matrix.mul_assoc]

/-! ### Property 5.8: the real Schur form -/

/-- **Property 5.8, the existence clause: the real Schur decomposition (5.34).** Given
`A ∈ ℝ^{n×n}`, there is an orthogonal `Q ∈ ℝ^{n×n}` such that `Qᵀ A Q` is block upper triangular
with diagonal blocks `R_ii` each of which is either a real number or a matrix of order `2` having
complex conjugate eigenvalues. The blocks are the fibres of a monotone block index `p : Fin n → ℕ`
with at most two indices each, `Qᵀ A Q` is `BlockTriangular p`, and a block with two indices,
`(Qᵀ A Q).toBlock (p · = k) (p · = k)`, has no real eigenvalue — its two eigenvalues are therefore
a non-real complex conjugate pair. Backbone
`Matrix.exists_orthogonal_conj_quasiUpperTriangular_of_irreducible_blocks`. The limit clause
(5.35) is false for the unshifted iteration and is not formalized (see the module doc). -/
theorem property_5_8 (A : Matrix (Fin N) (Fin N) ℝ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∃ p : Fin N → ℕ, Monotone p ∧
      (∀ k, #{i | p i = k} ≤ 2) ∧ (Qᵀ * A * Q).BlockTriangular p ∧
      ∀ k, #{i | p i = k} = 2 → ∀ μ : ℝ,
        μ ∉ spectrum ℝ ((Qᵀ * A * Q).toBlock (fun i => p i = k) (fun i => p i = k)) :=
  exists_orthogonal_conj_quasiUpperTriangular_of_irreducible_blocks A

end QuarteroniSaccoSaleri.Chapter05
