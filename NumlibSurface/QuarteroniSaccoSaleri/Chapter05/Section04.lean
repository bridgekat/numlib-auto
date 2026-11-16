/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Eigen.QRAlgorithm
import Numlib.LinearAlgebra.Matrix.QR
import Numlib.LinearAlgebra.Matrix.RealSchur
import NumlibSurface.QuarteroniSaccoSaleri.Chapter05.Section03

/-!
# Quarteroni, Sacco and Saleri, Section 5.4: The QR Iteration

This module formalizes Section 5.4 of [quarteroni2000numerical]. The QR iteration (5.32) starts from
$T^{(0)} = Q^{(0)T} A Q^{(0)}$ for a real matrix $A \in \mathbb{R}^{n \times n}$ and an orthogonal
$Q^{(0)}$. At step $k$ it factors $T^{(k-1)} = Q^{(k)} R^{(k)}$ with $Q^{(k)}$ orthogonal and
$R^{(k)}$ upper triangular, and it sets $T^{(k)} = R^{(k)} Q^{(k)}$. Every iterate is orthogonally
similar to $A$, $T^{(k)} = (Q^{(0)} \cdots Q^{(k)})^T A (Q^{(0)} \cdots Q^{(k)})$ (5.33). Property
5.8 states that $A$ has a real Schur form (5.34): an orthogonal $Q$ such that $Q^T A Q$ is block
upper triangular with diagonal blocks of order $1$ or $2$, where the blocks of order $2$ have
complex conjugate eigenvalues. Its further claim (5.35), that $Q$ is the limit of the accumulated
factors $Q^{(0)} Q^{(1)} \cdots Q^{(k)}$, is false as printed, and
`QuarteroniSaccoSaleri.Chapter05.qrAccum_not_tendsto` gives a counterexample.

The proofs specialize the backbone modules `Numlib.Eigen.QRAlgorithm` (the QR iteration, its
accumulated orthogonal factor and the similarity of the iterates) and
`Numlib.LinearAlgebra.Matrix.RealSchur` (the real Schur form).

## Main definitions

* Equation (5.32), `QuarteroniSaccoSaleri.Chapter05.qrIterate`: the QR iteration with $Q^{(0)} = I$.

## Main results

* Equation (5.32), `QuarteroniSaccoSaleri.Chapter05.qrIterate_eq`: the iteration of the book is the
  backbone's QR algorithm `Matrix.qrIterate`.
* Equation (5.32), `QuarteroniSaccoSaleri.Chapter05.equation_5_32`: the two phases of a step,
  $T^{(k)} = Q^{(k+1)} R^{(k+1)}$ and $T^{(k+1)} = R^{(k+1)} Q^{(k+1)}$.
* Equation (5.33), `QuarteroniSaccoSaleri.Chapter05.equation_5_33`: every iterate is orthogonally
  similar to $A$ through the accumulated factor $Q^{(0)} Q^{(1)} \cdots Q^{(k)}$.
* Property 5.8, `QuarteroniSaccoSaleri.Chapter05.property_5_8`: the real Schur form (5.34) exists.
* Property 5.8, `QuarteroniSaccoSaleri.Chapter05.qrAccum_not_tendsto`: the accumulated factors of
  the iteration need not converge, which refutes (5.35).

## Conventions

* From this section on, the book works with real matrices $A \in \mathbb{R}^{n \times n}$, which are
  `Matrix (Fin N) (Fin N) ℝ`. A matrix $Q$ is orthogonal if it is in
  `Matrix.orthogonalGroup (Fin N) ℝ`, that is, if $Q Q^T = I$.
* The QR factorization of a step is the one with a positive diagonal, `Matrix.qrQ` and `Matrix.qrR`
  of the backbone. It is computed by the Gram–Schmidt process on the columns, as Program 28 does
  with `mod_grams`. By the uniqueness of this factorization (`Matrix.IsThinQR.unique`), a
  Householder or Givens factorization gives the same factors at a nonsingular iterate.

## Implementation notes

* The iteration (5.32) is written as the book writes it, as the recursion
  `QuarteroniSaccoSaleri.Chapter05.qrIterate` from $T^{(0)} = A$. This is the choice $Q^{(0)} = I$
  of Section 5.5. For a general orthogonal $Q^{(0)}$, the iteration of the book is
  `qrIterate (Q₀ᵀ * A * Q₀)`, and (5.33) is stated in this form.

## Deviations from the source

* **Property 5.8, the limit (5.35)** (correction). The book claims that the orthogonal matrix of the
  real Schur form is $\lim_k Q^{(0)} Q^{(1)} \cdots Q^{(k)}$ for the iteration (5.32) without
  shifts. This is false: for the cyclic permutation matrix of Exercise 14, the accumulated factors
  cycle with period $3$. See `QuarteroniSaccoSaleri.Chapter05.qrAccum_not_tendsto`.
* **Property 5.8, the blocks of order 2** (reading). "A matrix of order $2$ having complex conjugate
  eigenvalues" is read as "a real $2 \times 2$ block with no real eigenvalue". See
  `QuarteroniSaccoSaleri.Chapter05.property_5_8`.

## Not formalized

* **Property 5.8, the limit (5.35).** It is false as printed, and the book gives no hypotheses under
  which it holds, so nothing replaces it. The convergence that the book has in mind is that of the
  iteration with shifts of Section 5.7, whose general behaviour the book calls an open problem.
  Property 5.9 of Section 5.5 is a convergence statement with hypotheses.
-/

open Filter Finset Matrix Topology

namespace QuarteroniSaccoSaleri.Chapter05

variable {N : ℕ}

/-! ### Equation (5.32): the QR iteration -/

/-- **Equation (5.32)** of [quarteroni2000numerical], the QR iteration with $Q^{(0)} = I$, so that
$T^{(0)} = A$. Let $A \in \mathbb{R}^{n \times n}$. For $k = 1, 2, \dots$, the iteration
determines $Q^{(k)}$ and $R^{(k)}$ with $Q^{(k)} R^{(k)} = T^{(k-1)}$ by the QR factorization,
and sets
$$T^{(k)} = R^{(k)} Q^{(k)}.$$

The factors are `Matrix.qrQ` and `Matrix.qrR`. For a general orthogonal $Q^{(0)}$, the iteration
of the book starts from $T^{(0)} = Q^{(0)T} A Q^{(0)}$ and is `qrIterate (Q₀ᵀ * A * Q₀)`. -/
noncomputable def qrIterate (A : Matrix (Fin N) (Fin N) ℝ) : ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => A
  | k + 1 => qrR (qrIterate A k) * qrQ (qrIterate A k)

/-- The iteration (5.32) of [quarteroni2000numerical] is the backbone's QR algorithm: for every $k$,
the iterate $T^{(k)}$ of `QuarteroniSaccoSaleri.Chapter05.qrIterate A` is
`Matrix.qrIterate A k`. -/
theorem qrIterate_eq (A : Matrix (Fin N) (Fin N) ℝ) :
    ∀ k, qrIterate A k = Matrix.qrIterate A k
  | 0 => rfl
  | k + 1 => by rw [qrIterate, qrIterate_eq A k, Matrix.qrIterate_succ]

/-- **Equation (5.32)** of [quarteroni2000numerical], the two phases of a step. Let
$A \in \mathbb{R}^{n \times n}$ and $k \in \mathbb{N}$. The iterate $T^{(k)}$ factors as
$T^{(k)} = Q^{(k+1)} R^{(k+1)}$, where $Q^{(k+1)}$ is orthogonal and $R^{(k+1)}$ is upper
triangular, and the next iterate is the product in the reverse order:
$$T^{(k+1)} = R^{(k+1)} Q^{(k+1)}.$$

The factor $Q^{(k+1)}$ is `qrQ (qrIterate A k)`, and the factor $R^{(k+1)}$ is
`qrR (qrIterate A k)`. The proof uses the backbone's `Matrix.qrQ_mul_qrR`,
`Matrix.qrQ_mem_unitaryGroup` and `Matrix.isUpperTriangular_qrR`. -/
theorem equation_5_32 (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    qrQ (qrIterate A k) * qrR (qrIterate A k) = qrIterate A k ∧
      qrQ (qrIterate A k) ∈ Matrix.orthogonalGroup (Fin N) ℝ ∧
      (qrR (qrIterate A k)).IsUpperTriangular ∧
      qrIterate A (k + 1) = qrR (qrIterate A k) * qrQ (qrIterate A k) :=
  ⟨qrQ_mul_qrR _, qrQ_mem_unitaryGroup _, isUpperTriangular_qrR _, rfl⟩

/-! ### Equation (5.33): the iterates are orthogonally similar to $A$ -/

/-- **Equation (5.33)** of [quarteroni2000numerical]. Let $A \in \mathbb{R}^{n \times n}$, let
$Q^{(0)}$ be orthogonal, and let $T^{(k)}$ be the iterates of (5.32) from
$T^{(0)} = Q^{(0)T} A Q^{(0)}$, with factors $Q^{(1)}, Q^{(2)}, \dots$. Then for every
$k \ge 0$, the product $Q^{(0)} Q^{(1)} \cdots Q^{(k)}$ is orthogonal and
$$T^{(k)} = (Q^{(0)} Q^{(1)} \cdots Q^{(k)})^T A \, (Q^{(0)} Q^{(1)} \cdots Q^{(k)}).$$

The accumulated factor $Q^{(1)} \cdots Q^{(k)}$ of the iteration is
`Matrix.qrAccum (Q₀ᵀ * A * Q₀) k`, which is the identity for $k = 0$. The proof specializes the
backbone's `Matrix.qrIterate_eq_conj_qrAccum` and `Matrix.qrAccum_mem_unitaryGroup`. -/
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

/-- **Property 5.8** of [quarteroni2000numerical], the real Schur decomposition (5.34). Let
$A \in \mathbb{R}^{n \times n}$. Then there is an orthogonal $Q \in \mathbb{R}^{n \times n}$
such that
$$Q^T A Q = \begin{bmatrix} R_{11} & R_{12} & \cdots & R_{1m} \\ 0 & R_{22} & \cdots & R_{2m} \\
  \vdots & & \ddots & \vdots \\ 0 & \cdots & 0 & R_{mm} \end{bmatrix},$$
where each diagonal block $R_{ii}$ is either a real number or a matrix of order $2$ with complex
conjugate eigenvalues.

**Reading.** "A matrix of order $2$ having complex conjugate eigenvalues" is read as "a real
$2 \times 2$ block with no real eigenvalue". The characteristic polynomial of such a block is a
real quadratic without real roots, so its two complex eigenvalues are conjugate and not real,
and conversely.

The blocks are the fibres of a monotone block index $p : \{1, \dots, n\} \to \mathbb{N}$ with at
most two indices in each fibre. The matrix $Q^T A Q$ is `Matrix.BlockTriangular p`, and a block
with two indices, `(Qᵀ * A * Q).toBlock (p · = k) (p · = k)`, has no real eigenvalue. The proof
specializes the backbone's
`Matrix.exists_orthogonal_conj_quasiUpperTriangular_of_irreducible_blocks`. The limit clause
(5.35) of Property 5.8 is false for the iteration without shifts and is not formalized
(`QuarteroniSaccoSaleri.Chapter05.qrAccum_not_tendsto`). -/
theorem property_5_8 (A : Matrix (Fin N) (Fin N) ℝ) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∃ p : Fin N → ℕ, Monotone p ∧
      (∀ k, #{i | p i = k} ≤ 2) ∧ (Qᵀ * A * Q).BlockTriangular p ∧
      ∀ k, #{i | p i = k} = 2 → ∀ μ : ℝ,
        μ ∉ spectrum ℝ ((Qᵀ * A * Q).toBlock (fun i => p i = k) (fun i => p i = k)) :=
  exists_orthogonal_conj_quasiUpperTriangular_of_irreducible_blocks A

/-! ### (5.35): the accumulated orthogonal factors need not converge -/

/-- **Property 5.8** of [quarteroni2000numerical], the limit (5.35) is false for the iteration
(5.32) without shifts. Let
$$A = \begin{bmatrix} 0 & 0 & 1 \\ 1 & 0 & 0 \\ 0 & 1 & 0 \end{bmatrix}$$
be the cyclic permutation matrix of Exercise 14. Then the accumulated factor of the QR iteration
from $T^{(0)} = A$ is $Q^{(1)} \cdots Q^{(k)} = A^k$ for every $k$, and this sequence has no
limit.

The columns of $A$ are orthonormal, so the QR factorization with a positive diagonal is
$A = A \cdot I$. Every factor is $Q^{(k)} = A$ with $R^{(k)} = I$, and the iteration does not
move. Since $A^3 = I$ and $A \neq I$, the products $A^k$ cycle with period $3$. So they converge
to no orthogonal matrix, and in particular not to one that gives a real Schur form of $A$. A
real Schur form of $A$ exists all the same (`QuarteroniSaccoSaleri.Chapter05.property_5_8`), and
the iterate $A$ is not quasi-triangular. Example 5.9 of the book shows a second symptom: there
the iterates converge, but to a quasi-triangular matrix that is not the real Schur form of the
starting matrix, as the text observes. Only the existence clause (5.34) of Property 5.8 is
formalized. The convergence that the book has in mind is that of the iteration with shifts of
Section 5.7, which the book describes as not settled in general. See also
`QuarteroniSaccoSaleri.Chapter05.exercise_5_14`. -/
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
    IsThinQR.unique ⟨qrQ_mul_qrR A, conjTranspose_qrQ_mul_self A, isUpperTriangular_qrR A⟩
      ⟨Matrix.mul_one A, hAA, blockTriangular_one⟩ (qrR_diag_pos hdet) (fun j => by simp)
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
