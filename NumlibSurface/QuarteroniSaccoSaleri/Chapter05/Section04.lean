import Numlib.Eigen.QRAlgorithm
import Numlib.LinearAlgebra.Matrix.QR
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
* `qrAccum_not_tendsto` — the accumulated factors of the unshifted iteration need not converge,
  the counterexample to (5.35).

## Readings and errata

Property 5.8 runs two statements together: the existence of the real Schur form (5.34), which is
`property_5_8`, and the claim (5.35) that its orthogonal matrix is `lim_k Q⁽⁰⁾ Q⁽¹⁾ ⋯ Q⁽ᵏ⁾`, the
accumulated factors of the *unshifted* iteration (5.32). **The second is false as printed**, and
nothing in the library replaces it, because the book offers no hypotheses under which it holds:
what it has in mind is the convergence of the *shifted* iteration of §5.7, whose general behaviour
it calls an open problem. The counterexample is the cyclic permutation matrix
`A = [0 0 1; 1 0 0; 0 1 0]` of Exercise 14 (`exercise_5_14`): its columns are orthonormal, so the
QR factorization with positive diagonal is `A = A · I`, every factor `Q⁽ᵏ⁾` is `A` itself, the
iteration never moves, and the accumulated product is `Aᵏ`, which cycles with period `3` and has no
limit — `qrAccum_not_tendsto`. A real Schur form of `A` exists all the same, by `property_5_8`, and
the iterate `A` is not even quasi-triangular. The book's own Example 5.9 is the second symptom:
there the iterates converge, but to a "cheating" quasi-triangular matrix that is not the real Schur
form of the starting matrix, as the text observes. Property 5.9 of §5.5 is where a convergence
statement with hypotheses lives.

In (5.34) "a matrix of order 2 having complex conjugate eigenvalues" is read as "a `2 × 2` real
block with no real eigenvalue": the characteristic polynomial of such a block is a real quadratic
without real roots, so its two complex eigenvalues are conjugate and non-real, and conversely.
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

/-! ### (5.35): the accumulated orthogonal factors need not converge -/

/-- **The limit clause (5.35) of Property 5.8 is false for the unshifted iteration (5.32).** For
the cyclic permutation matrix `A = [0 0 1; 1 0 0; 0 1 0]` of Exercise 14 the columns of `A` are
already orthonormal, so the QR factorization with a positive diagonal is `A = A · I`: every factor
is `Q⁽ᵏ⁾ = A` and `R⁽ᵏ⁾ = I`, the iteration never moves, and the accumulated factor is
`Q⁽⁰⁾ Q⁽¹⁾ ⋯ Q⁽ᵏ⁾ = Matrix.qrAccum A k = Aᵏ`. Since `A³ = I` and `A ≠ I` that sequence cycles with
period `3` and has no limit, so it converges to no orthogonal matrix at all, let alone to one
realizing a real Schur form of `A` — which exists nonetheless, by `property_5_8`.

Only the existence clause (5.34) is a theorem about the unshifted iteration. The convergence the
book has in mind is that of the shifted iteration of §5.7, which the book itself describes as not
settled in general; see the module doc (Quarteroni–Sacco–Saleri, *Numerical Mathematics*,
Property 5.8, (5.35)). -/
theorem qrAccum_not_tendsto :
    let A : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
    (∀ k, Matrix.qrAccum A k = A ^ k) ∧ ¬∃ Q, Tendsto (Matrix.qrAccum A) atTop (𝓝 Q) := by
  intro A
  have hAA : Aᴴ * A = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_three]
  have hdet : IsUnit A.det := by
    have h : A.det = 1 := by simp [A, Matrix.det_fin_three]
    rw [h]
    exact isUnit_one
  have hqr : qrQ A = A ∧ qrR A = 1 :=
    qr_unique (qrQ_mul_qrR A).symm (Matrix.mul_one A).symm (conjTranspose_qrQ_mul_self A) hAA
      (isUpperTriangular_qrR A) blockTriangular_one (qrR_diag_pos hdet) (fun j => by simp)
  have hfix : ∀ k, Matrix.qrIterate A k = A := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Matrix.qrIterate_succ, ih, hqr.1, hqr.2, Matrix.one_mul]
  have haccum : ∀ k, Matrix.qrAccum A k = A ^ k := by
    intro k
    induction k with
    | zero => rw [Matrix.qrAccum_zero, pow_zero]
    | succ k ih => rw [Matrix.qrAccum_succ, ih, hfix, hqr.1, pow_succ]
  refine ⟨haccum, ?_⟩
  rintro ⟨Q, hQ⟩
  have hA3 : A ^ 3 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  have h3 : Tendsto (fun k : ℕ => 3 * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k (by norm_num)) tendsto_id
  have h3' : Tendsto (fun k : ℕ => 3 * k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_succ _) h3
  have hcyc : Tendsto (fun k : ℕ => Matrix.qrAccum A (3 * k)) atTop (𝓝 Q) := hQ.comp h3
  have hcyc' : Tendsto (fun k : ℕ => Matrix.qrAccum A (3 * k + 1)) atTop (𝓝 Q) := hQ.comp h3'
  simp only [haccum, pow_mul, hA3, one_pow] at hcyc
  simp only [haccum, pow_succ, pow_mul, hA3, one_pow, Matrix.one_mul] at hcyc'
  have h1 : Q = 1 := tendsto_nhds_unique hcyc tendsto_const_nhds
  have h2 : Q = A := tendsto_nhds_unique hcyc' tendsto_const_nhds
  rw [h1] at h2
  have := congrFun (congrFun h2 0) 0
  simp [A] at this

end QuarteroniSaccoSaleri.Chapter05
