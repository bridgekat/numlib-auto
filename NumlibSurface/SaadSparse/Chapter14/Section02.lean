/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Numlib.LinearAlgebra.Matrix.NonsingularInverse
import Numlib.LinearAlgebra.Matrix.SchurComplement
import NumlibSurface.SaadSparse.Common

/-!
# Saad, Section 14.2: Block Gaussian elimination and the Schur complement

This module formalizes Sections 14.2.1, 14.2.2, 14.2.4 and 14.2.5 of [saad2003iterative]. The linear
system is partitioned as in (14.2), with the interior variables $x$ first and the interface
variables $y$ last:
$$\begin{pmatrix} B & E \\ F & C \end{pmatrix} \begin{pmatrix} x \\ y \end{pmatrix} =
  \begin{pmatrix} f \\ g \end{pmatrix}.$$
Elimination of $x$ gives the reduced system $Sy = g'$ with the Schur complement $S = C - F B^{-1} E$
(14.5) and the right-hand side $g' = g - F B^{-1} f$ (14.4). The module states block Gaussian
elimination (Algorithm 14.1) and proves that it solves the system, the block $LU$ factorization
(14.6), the block inverse (14.7), Proposition 14.1, and the additivity $S = \sum_i S_i$ of the Schur
complement over subdomains (14.16). The proofs specialize
`Numlib.LinearAlgebra.Matrix.SchurComplement`.

Section 14.2.5 computes the local Schur complement of the five-point Laplacean on a rectangle that
is split by a vertical line. It is the only place in the book where a Schur complement is found in
closed form. The diagonal blocks of the block $LU$ factorization of
$\operatorname{tridiag}(-I, B, -I)$ obey the recurrence (14.20), $T_1 = B$ and
$T_{k+1} = B - T_k^{-1}$, and $T_n$ is the local Schur complement $S_1$. The module states this
recurrence at one eigenvalue $\mu$ of $B$, where all of its content lies. There it is a scalar
recurrence $\lambda_1 = \mu$, $\lambda_{k+1} = \mu - 1/\lambda_k$, which a linear difference
equation solves in closed form. The matrix $B = \operatorname{tridiag}(-1, 4, -1)$ has the
eigenvalues $4 - 2 \cos \theta > 2$, so the hypothesis $\mu > 2$ is exactly what the model problem
supplies.

## Main definitions

* Equation (14.4), `SaadSparse.Chapter14.reducedRhs`: the right-hand side $g' = g - F B^{-1} f$ of
  the reduced system.
* Equation (14.5), `SaadSparse.Chapter14.schurComplement`: the Schur complement
  $S = C - F B^{-1} E$.
* Algorithm 14.1, `SaadSparse.Chapter14.blockGaussianElimination`: block Gaussian elimination.
* Proposition 14.1, `SaadSparse.Chapter14.interfaceRestrict`: the restriction $R_y$ of a vector to
  its interface block.
* Equation (14.20), `SaadSparse.Chapter14.modelSchurEigen`: the recurrence $\lambda_1 = \mu$,
  $\lambda_{k+1} = \mu - 1/\lambda_k$ at one eigenvalue $\mu$ of $B$.
* Section 14.2.5, `SaadSparse.Chapter14.modelRoot`: the larger root $\rho$ of $x^2 - \mu x + 1$.
* Section 14.2.5, `SaadSparse.Chapter14.modelSeq`: the sequence
  $\eta_k = \rho^{k+1} - \rho^{-(k+1)}$ that linearizes the recurrence.

## Main results

* Equation (14.6), `SaadSparse.Chapter14.equation_14_6`: the block $LU$ factorization of the
  partitioned matrix.
* Equation (14.7), `SaadSparse.Chapter14.equation_14_7`: the block inverse of the partitioned
  matrix, with $S^{-1}$ in its $(2,2)$ corner.
* Algorithm 14.1, `SaadSparse.Chapter14.blockGaussianElimination_eq`: the output of block Gaussian
  elimination solves the system.
* Proposition 14.1(1), `SaadSparse.Chapter14.proposition_14_1_1`: if $A$ and $B$ are nonsingular,
  then $S$ is nonsingular.
* Proposition 14.1(2), `SaadSparse.Chapter14.proposition_14_1_2`: if $A$ is symmetric positive
  definite, then so is $S$.
* Proposition 14.1(3), `SaadSparse.Chapter14.proposition_14_1_3`: $S^{-1} y = R_y A^{-1} (0, y)^T$.
* Equation (14.16), `SaadSparse.Chapter14.equation_14_16`: for a block diagonal interior block and
  $C = \sum_i C_i$, the Schur complement is the sum of the local Schur complements.
* Section 14.2.5, `SaadSparse.Chapter14.modelSeq_succ_succ`: $\eta_{k+1} = \mu \eta_k - \eta_{k-1}$.
* Section 14.2.5, `SaadSparse.Chapter14.modelSchurEigen_eq`: $\lambda_{k+1} = \eta_{k+1} / \eta_k$.
* Section 14.2.5, `SaadSparse.Chapter14.modelRoot_lt_modelSchurEigen`: every $\lambda_k$ exceeds
  $\rho > 1$, so the recurrence does not break down.

## Implementation notes

* The system matrix is `Matrix.fromBlocks B E F C` over the index type `Fin p ⊕ Fin q`, with the
  interior variables first and the interface variables last, as in (14.2). No reindexing equivalence
  appears.
* The vertex-based block structure (14.8)–(14.14) of Section 14.2.3 is built in
  `NumlibSurface.SaadSparse.Chapter14.Section03` as `SaadSparse.Chapter14.VertexPartitioning`, next
  to its only theorem, Theorem 14.2.
* Indices of the model recurrence are $0$-based: `SaadSparse.Chapter14.modelSchurEigen μ k` is the
  book's $\lambda_{k+1}$.

## Not formalized

* **The matrix form of Section 14.2.5.** To transport $\lambda_k$ back through the discrete sine
  basis to $T_k = f_k(B)$ needs the inverse of $T_k$ read on eigenvectors. To identify $T_n$ with
  the Schur complement needs the block $LU$ factorization of a block tridiagonal matrix, which the
  library does not have. The limit $S_1 \to \hat{S} = (B + \sqrt{B^2 - 4I})/2$ needs a matrix square
  root in addition. `Numlib.LinearAlgebra.Matrix.TridiagonalToeplitz` supplies the eigenpairs.
-/

open Matrix

namespace SaadSparse.Chapter14

variable {p q : ℕ} {B : Matrix (Fin p) (Fin p) ℝ} {E : Matrix (Fin p) (Fin q) ℝ}
variable {F : Matrix (Fin q) (Fin p) ℝ} {C : Matrix (Fin q) (Fin q) ℝ}

/-- **Equation (14.5)** of [saad2003iterative]. Let $B \in \mathbb{R}^{p \times p}$,
$E \in \mathbb{R}^{p \times q}$, $F \in \mathbb{R}^{q \times p}$ and
$C \in \mathbb{R}^{q \times q}$ be the blocks of the partitioned matrix (14.2). The **Schur
complement** associated with the interface variables is
$$S = C - F B^{-1} E.$$

The inverse is Mathlib's `Matrix.inv`, so for a singular $B$ the value is $C$ (since
$B^{-1} = 0$ in Lean). -/
noncomputable def schurComplement (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  C - F * B⁻¹ * E

/-- The Schur complement $S$ of Section 14.2 is $C - F B^{-1} E$. -/
theorem schurComplement_def (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) :
    schurComplement B E F C = C - F * B⁻¹ * E := rfl

/-- The Schur complement $S$ of Section 14.2 is the backbone Schur complement
`Matrix.schurComplement` of the block matrix $\begin{pmatrix} B & E \\ F & C \end{pmatrix}$. -/
theorem schurComplement_eq (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) :
    schurComplement B E F C = (fromBlocks B E F C).schurComplement := rfl

/-- **Equation (14.4)** of [saad2003iterative]. For blocks $B \in \mathbb{R}^{p \times p}$ and
$F \in \mathbb{R}^{q \times p}$ and right-hand sides $f \in \mathbb{R}^p$ and
$g \in \mathbb{R}^q$, the right-hand side of the reduced system $Sy = g'$ is
$$g' = g - F B^{-1} f.$$
-/
noncomputable def reducedRhs (B : Matrix (Fin p) (Fin p) ℝ) (F : Matrix (Fin q) (Fin p) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) : Fin q → ℝ :=
  g - F *ᵥ (B⁻¹ *ᵥ f)

/-- The reduced right-hand side $g'$ is $g - F B^{-1} f$. -/
theorem reducedRhs_def (B : Matrix (Fin p) (Fin p) ℝ) (F : Matrix (Fin q) (Fin p) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) : reducedRhs B F f g = g - F *ᵥ (B⁻¹ *ᵥ f) := rfl

/-- The restriction $R_y$ of the book: a vector $v = (x, y)$ indexed by the interior and interface
variables is mapped to its interface block $y$. -/
def interfaceRestrict (v : Fin p ⊕ Fin q → ℝ) : Fin q → ℝ := v ∘ Sum.inr

/-- The interface unknown $y = S^{-1} g'$ that Algorithm 14.1 computes. -/
noncomputable def interfaceSolution (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ) (f : Fin p → ℝ) (g : Fin q → ℝ) :
    Fin q → ℝ :=
  (schurComplement B E F C)⁻¹ *ᵥ reducedRhs B F f g

/-- **Algorithm 14.1** of [saad2003iterative] (block Gaussian elimination). For the partitioned
system (14.2) with right-hand side $(f, g)$, the algorithm solves $B E' = E$ and $B f' = f$,
forms $g' = g - F f'$ and $S = C - F E'$, solves $S y = g'$, and recovers $x = f' - E' y$. The
output is the vector $(x, y)$.

The algorithm is written as a function: $E' = B^{-1} E$, $f' = B^{-1} f$ and $y = S^{-1} g'$,
with Mathlib's matrix inverse. -/
noncomputable def blockGaussianElimination (B : Matrix (Fin p) (Fin p) ℝ)
    (E : Matrix (Fin p) (Fin q) ℝ) (F : Matrix (Fin q) (Fin p) ℝ) (C : Matrix (Fin q) (Fin q) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) : Fin p ⊕ Fin q → ℝ :=
  Sum.elim (B⁻¹ *ᵥ f - (B⁻¹ * E) *ᵥ interfaceSolution B E F C f g)
    (interfaceSolution B E F C f g)

/-- **Equation (14.6)** of [saad2003iterative]. Let $B$ be nonsingular. Then the partitioned matrix
has the block $LU$ factorization
$$\begin{pmatrix} B & E \\ F & C \end{pmatrix} = \begin{pmatrix} I & 0 \\ F B^{-1} & I
  \end{pmatrix} \begin{pmatrix} B & E \\ 0 & S \end{pmatrix},$$
where $S = C - F B^{-1} E$ is the Schur complement. -/
theorem equation_14_6 (hB : IsUnit B) :
    fromBlocks B E F C
      = fromBlocks 1 0 (F * B⁻¹) 1 * fromBlocks B E 0 (schurComplement B E F C) :=
  Matrix.fromBlocks_eq_mul_fromBlocks_schurComplement hB

/-- **Equation (14.7)** of [saad2003iterative]. Let $B$ and $A = \begin{pmatrix} B & E \\ F & C
\end{pmatrix}$ be nonsingular, and let $S = C - F B^{-1} E$. Then
$$A^{-1} = \begin{pmatrix} B^{-1} + B^{-1} E S^{-1} F B^{-1} & -B^{-1} E S^{-1} \\ -S^{-1} F
  B^{-1} & S^{-1} \end{pmatrix}.$$
-/
theorem equation_14_7 (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) :
    (fromBlocks B E F C)⁻¹
      = fromBlocks (B⁻¹ + B⁻¹ * E * (schurComplement B E F C)⁻¹ * F * B⁻¹)
          (-(B⁻¹ * E * (schurComplement B E F C)⁻¹))
          (-((schurComplement B E F C)⁻¹ * F * B⁻¹)) (schurComplement B E F C)⁻¹ :=
  Matrix.inv_fromBlocks_eq hB hA

/-- **Proposition 14.1(1)** of [saad2003iterative]. Let $B$ and $A = \begin{pmatrix} B & E \\ F & C
\end{pmatrix}$ be nonsingular. Then the Schur complement $S = C - F B^{-1} E$ is nonsingular. -/
theorem proposition_14_1_1 (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) :
    IsUnit (schurComplement B E F C) :=
  Matrix.isUnit_schurComplement (by simpa using hB) hA

/-- **Proposition 14.1(2)** of [saad2003iterative]. If $A = \begin{pmatrix} B & E \\ F & C
\end{pmatrix}$ is symmetric positive definite, then the Schur complement $S = C - F B^{-1} E$ is
symmetric positive definite.

Positive definiteness is Mathlib's `Matrix.PosDef`, which includes symmetry for a real matrix. -/
theorem proposition_14_1_2 (hA : (fromBlocks B E F C).PosDef) :
    (schurComplement B E F C).PosDef :=
  Matrix.PosDef.schurComplement hA

/-- **Proposition 14.1(3)** of [saad2003iterative]. Let $B$ and $A = \begin{pmatrix} B & E \\ F & C
\end{pmatrix}$ be nonsingular, and let $S = C - F B^{-1} E$. Then for every $y \in \mathbb{R}^q$
$$S^{-1} y = R_y A^{-1} \begin{pmatrix} 0 \\ y \end{pmatrix}.$$

So a solver for the whole system provides a solver for the reduced interface system. The
restriction $R_y$ is `SaadSparse.Chapter14.interfaceRestrict`. -/
theorem proposition_14_1_3 (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C)) (y : Fin q → ℝ) :
    (schurComplement B E F C)⁻¹ *ᵥ y
      = interfaceRestrict ((fromBlocks B E F C)⁻¹ *ᵥ Sum.elim 0 y) := by
  have h22 : ((fromBlocks B E F C)⁻¹).toBlocks₂₂ = (schurComplement B E F C)⁻¹ :=
    Matrix.toBlocks₂₂_inv_eq_inv_schurComplement (by simpa using hB) hA
  funext j
  rw [← h22]
  simp [interfaceRestrict, Matrix.mulVec_apply_eq_sum, Fintype.sum_sum_type, Matrix.toBlocks₂₂]

/-- **Algorithm 14.1** of [saad2003iterative], correctness. Let $B$ and $A = \begin{pmatrix} B & E
\\ F & C \end{pmatrix}$ be nonsingular. Then for all $f \in \mathbb{R}^p$ and
$g \in \mathbb{R}^q$, the vector $(x, y)$ that block Gaussian elimination returns satisfies
$$A \begin{pmatrix} x \\ y \end{pmatrix} = \begin{pmatrix} f \\ g \end{pmatrix}.$$
-/
theorem blockGaussianElimination_eq (hB : IsUnit B) (hA : IsUnit (fromBlocks B E F C))
    (f : Fin p → ℝ) (g : Fin q → ℝ) :
    fromBlocks B E F C *ᵥ blockGaussianElimination B E F C f g = Sum.elim f g := by
  have hy : schurComplement B E F C *ᵥ interfaceSolution B E F C f g = reducedRhs B F f g :=
    mulVec_nonsing_inv_mulVec (proposition_14_1_1 hB hA) _
  rw [blockGaussianElimination, Matrix.fromBlocks_mulVec]
  refine congrArg₂ Sum.elim ?_ ?_
  · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec,
      mulVec_nonsing_inv_mulVec hB]
    abel
  · simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc]
    have hsum : (F * B⁻¹) *ᵥ f - (F * B⁻¹ * E) *ᵥ interfaceSolution B E F C f g
          + C *ᵥ interfaceSolution B E F C f g
        = (F * B⁻¹) *ᵥ f + schurComplement B E F C *ᵥ interfaceSolution B E F C f g := by
      rw [schurComplement_def, Matrix.sub_mulVec]; abel
    rw [hsum, hy, reducedRhs_def, Matrix.mulVec_mulVec]
    abel

/-! ### Section 14.2.4: The Schur complement of a subdomain partitioning -/

/-- **Equation (14.16)** of [saad2003iterative]. Let the interior variables split into $s$
subdomains with no coupling between them, so that the interior block of (14.15) is block
diagonal, $B = \operatorname{diag}(B_1, \dots, B_s)$ with each $B_i$ nonsingular. Let $E$ and
$F$ be the interior–interface blocks, with $E_i$ and $F_i$ the parts that belong to subdomain
$i$, and let the interface block be a sum $C = \sum_i C_i$. Then the Schur complement of
$\begin{pmatrix} B & E \\ F & C \end{pmatrix}$ is the sum of the local Schur complements:
$$S = \sum_{i=1}^{s} S_i, \qquad S_i = C_i - F_i B_i^{-1} E_i.$$

The book derives the identity in Section 14.2.4, "Schur complement for finite-element
partitionings", where $C = \sum_i C_i$ comes from the splitting of the bilinear form over
subdomains with disjoint sets of elements. The identity itself is block algebra and needs no
finite elements. Therefore the hypothesis here is the decomposition of $C$, not the
discretization that produces it.

The block diagonal matrix is `Matrix.blockDiagonal' B` over the index type
`(i : Fin s) × Fin (d i)`, and $E_i$, $F_i$ are submatrices of $E$ and $F$. The proof
specializes `Matrix.schurComplement_fromBlocks_blockDiagonal'`. -/
theorem equation_14_16 {s : ℕ} {d : Fin s → ℕ} (B : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℝ)
    (E : Matrix ((i : Fin s) × Fin (d i)) (Fin q) ℝ)
    (F : Matrix (Fin q) ((i : Fin s) × Fin (d i)) ℝ) (C : Fin s → Matrix (Fin q) (Fin q) ℝ)
    (hB : ∀ i, IsUnit (B i)) :
    (fromBlocks (Matrix.blockDiagonal' B) E F (∑ i, C i)).schurComplement
      = ∑ i, (C i - F.submatrix id (Sigma.mk i) * (B i)⁻¹ * E.submatrix (Sigma.mk i) id) := by
  rw [Matrix.schurComplement_fromBlocks_blockDiagonal' B E F C hB]
  exact Finset.sum_congr rfl fun i _ => Matrix.schurComplement_fromBlocks _ _ _ _

/-! ### Section 14.2.5: The Schur complement of the model problem, at one eigenvalue -/

section ModelProblem

variable {μ : ℝ}

/-- **Equation (14.20)** of [saad2003iterative], read at one eigenvalue. In the two-domain model
problem of Section 14.2.5, the diagonal blocks obey $T_1 = B$ and $T_{k+1} = B - T_k^{-1}$, with
$B = \operatorname{tridiag}(-1, 4, -1)$. On the eigenvector of $B$ for the eigenvalue $\mu$, the
block $T_k$ acts as a number $\lambda_k$, and
$$\lambda_1 = \mu, \qquad \lambda_{k+1} = \mu - \frac{1}{\lambda_k}.$$

Indices are shifted: `SaadSparse.Chapter14.modelSchurEigen μ k` is the book's $\lambda_{k+1}$.
Division by $0$ is $0$ in Lean, so the recurrence is defined for every $\mu$. -/
noncomputable def modelSchurEigen (μ : ℝ) : ℕ → ℝ
  | 0 => μ
  | k + 1 => μ - 1 / modelSchurEigen μ k

/-- **Section 14.2.5** of [saad2003iterative]. The larger root
$$\rho = \frac{\mu + \sqrt{\mu^2 - 4}}{2}$$
of the characteristic equation $x^2 - \mu x + 1 = 0$ of the linearized recurrence. The other
root is $1/\rho$.

The square root is `Real.sqrt`, which is $0$ at a negative argument; the results use $\rho$ only
for $\mu > 2$. -/
noncomputable def modelRoot (μ : ℝ) : ℝ := (μ + √(μ ^ 2 - 4)) / 2

/-- **Section 14.2.5** of [saad2003iterative]. The auxiliary sequence of the linearization of
(14.20),
$$\eta_k = \rho^{k+1} - \rho^{-(k+1)},$$
whose ratios are the numbers $\lambda_k$. It satisfies the *linear* difference equation
$\eta_{k+1} = \mu \eta_k - \eta_{k-1}$.

The book includes the normalizing factor $1/(\rho - \rho^{-1})$. It is left out here, since only
the ratios are used. -/
noncomputable def modelSeq (μ : ℝ) (m : ℕ) : ℝ := modelRoot μ ^ (m + 1) - (modelRoot μ ^ (m + 1))⁻¹

/-- If $\mu > 2$, then the root $\rho$ of $x^2 - \mu x + 1$ satisfies $\rho > 1$. -/
theorem one_lt_modelRoot (hμ : 2 < μ) : 1 < modelRoot μ := by
  have h1 : (0 : ℝ) ≤ μ ^ 2 - 4 := by nlinarith
  have h2 : (0 : ℝ) ≤ √(μ ^ 2 - 4) := Real.sqrt_nonneg _
  rw [modelRoot]
  linarith

/-- If $\mu > 2$, then the root $\rho$ of $x^2 - \mu x + 1$ is positive. -/
theorem modelRoot_pos (hμ : 2 < μ) : 0 < modelRoot μ :=
  lt_trans zero_lt_one (one_lt_modelRoot hμ)

/-- **Section 14.2.5** of [saad2003iterative]. If $\mu > 2$, then $\rho$ is a root of
$x^2 - \mu x + 1$, in the form
$$\rho + \rho^{-1} = \mu.$$

This is why the two exponentials $\rho^k$ and $\rho^{-k}$ solve the linear difference equation. -/
theorem modelRoot_add_inv (hμ : 2 < μ) : modelRoot μ + (modelRoot μ)⁻¹ = μ := by
  have h1 : (0 : ℝ) ≤ μ ^ 2 - 4 := by nlinarith
  have hs : √(μ ^ 2 - 4) ^ 2 = μ ^ 2 - 4 := Real.sq_sqrt h1
  have hρ : modelRoot μ ≠ 0 := ne_of_gt (modelRoot_pos hμ)
  have hquad : modelRoot μ ^ 2 + 1 = μ * modelRoot μ := by
    rw [modelRoot]
    field_simp
    nlinarith [hs]
  field_simp
  linarith [hquad]

/-- If $\mu > 2$, then every term $\eta_k = \rho^{k+1} - \rho^{-(k+1)}$ of the linearizing sequence
is positive. -/
theorem modelSeq_pos (hμ : 2 < μ) (m : ℕ) : 0 < modelSeq μ m := by
  have hρ := one_lt_modelRoot hμ
  have h1 : 1 < modelRoot μ ^ (m + 1) := one_lt_pow₀ hρ (Nat.succ_ne_zero m)
  rw [modelSeq, sub_pos]
  calc (modelRoot μ ^ (m + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    _ < modelRoot μ ^ (m + 1) := h1

/-- For every nonzero real $\rho$ and every $m \in \mathbb{N}$, $\rho^{m+3} - \rho^{-(m+3)} =
(\rho + \rho^{-1})(\rho^{m+2} - \rho^{-(m+2)}) - (\rho^{m+1} - \rho^{-(m+1)})$. -/
private theorem exp_rec {ρ : ℝ} (hρ : ρ ≠ 0) (m : ℕ) :
    ρ ^ (m + 3) - (ρ ^ (m + 3))⁻¹
      = (ρ + ρ⁻¹) * (ρ ^ (m + 2) - (ρ ^ (m + 2))⁻¹) - (ρ ^ (m + 1) - (ρ ^ (m + 1))⁻¹) := by
  field_simp
  ring

private theorem exp_base {ρ : ℝ} (hρ : ρ ≠ 0) :
    ρ ^ (0 + 1 + 1) - (ρ ^ (0 + 1 + 1))⁻¹ = (ρ + ρ⁻¹) * (ρ ^ (0 + 1) - (ρ ^ (0 + 1))⁻¹) := by
  field_simp
  ring

private theorem exp_mul {ρ : ℝ} (hρ : ρ ≠ 0) (m : ℕ) :
    ρ * (ρ ^ (m + 1) - (ρ ^ (m + 1))⁻¹) = ρ ^ (m + 2) - (ρ ^ m)⁻¹ := by
  field_simp
  ring

/-- **Section 14.2.5** of [saad2003iterative], the linear difference equation. If $\mu > 2$, then
for every $k \ge 1$
$$\eta_{k+1} = \mu \eta_k - \eta_{k-1}.$$
-/
theorem modelSeq_succ_succ (hμ : 2 < μ) (m : ℕ) :
    modelSeq μ (m + 2) = μ * modelSeq μ (m + 1) - modelSeq μ m := by
  have h := exp_rec (ne_of_gt (modelRoot_pos hμ)) m
  rw [modelRoot_add_inv hμ] at h
  simpa [modelSeq] using h

/-- **Section 14.2.5** of [saad2003iterative], the closed form of the recurrence (14.20). If
$\mu > 2$, then for every $k \ge 0$ the number $\lambda_{k+1}$ is the ratio of two consecutive
terms of the linear sequence:
$$\lambda_{k+1} = \frac{\eta_{k+1}}{\eta_k}.$$

With $\eta_k = \rho^{k+1} - \rho^{-(k+1)}$, this is the book's $\lambda_k = \rho (1 -
\rho^{-2(k+1)}) / (1 - \rho^{-2k})$, after division of the numerator and the denominator by
$\rho^k$. -/
theorem modelSchurEigen_eq (hμ : 2 < μ) (m : ℕ) :
    modelSchurEigen μ m = modelSeq μ (m + 1) / modelSeq μ m := by
  induction m with
  | zero =>
      have h0 : modelSeq μ 0 ≠ 0 := ne_of_gt (modelSeq_pos hμ 0)
      have h := exp_base (ne_of_gt (modelRoot_pos hμ))
      rw [modelRoot_add_inv hμ] at h
      rw [modelSchurEigen, eq_div_iff h0]
      simpa [modelSeq] using h.symm
  | succ m ih =>
      have h1 : modelSeq μ (m + 1) ≠ 0 := ne_of_gt (modelSeq_pos hμ (m + 1))
      have h0 : modelSeq μ m ≠ 0 := ne_of_gt (modelSeq_pos hμ m)
      rw [modelSchurEigen, ih, one_div_div, eq_div_iff h1]
      have h := modelSeq_succ_succ hμ m
      field_simp
      linarith [h]

/-- **Section 14.2.5** of [saad2003iterative], the recurrence does not break down. If $\mu > 2$,
then every $\lambda_k$ satisfies
$$\lambda_k > \rho,$$
and $\rho > 1$ by `SaadSparse.Chapter14.one_lt_modelRoot`. Therefore $T_k$ is nonsingular at
every step, and $T_{k+1} = B - T_k^{-1}$ is defined.

The book says "it can easily be shown that the above recurrence does not break down" and gives
no proof. This theorem is that statement. -/
theorem modelRoot_lt_modelSchurEigen (hμ : 2 < μ) (m : ℕ) :
    modelRoot μ < modelSchurEigen μ m := by
  have hρ1 := one_lt_modelRoot hμ
  have hρ : (0 : ℝ) < modelRoot μ := modelRoot_pos hμ
  have h0 : (0 : ℝ) < modelSeq μ m := modelSeq_pos hμ m
  have hlt : (modelRoot μ ^ (m + 2))⁻¹ < (modelRoot μ ^ m)⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) (by positivity)]
    exact pow_lt_pow_right₀ hρ1 (by omega)
  have hkey : modelRoot μ * modelSeq μ m = modelRoot μ ^ (m + 2) - (modelRoot μ ^ m)⁻¹ := by
    rw [modelSeq]
    exact exp_mul (ne_of_gt hρ) m
  have hseq : modelSeq μ (m + 1) = modelRoot μ ^ (m + 2) - (modelRoot μ ^ (m + 2))⁻¹ := by
    rw [modelSeq]
  rw [modelSchurEigen_eq hμ, lt_div_iff₀ h0, hkey, hseq]
  linarith

/-- If $\mu > 2$, then every $\lambda_k$ is positive, and hence nonzero. This is the form of
`SaadSparse.Chapter14.modelRoot_lt_modelSchurEigen` that the recurrence itself needs. -/
theorem modelSchurEigen_pos (hμ : 2 < μ) (m : ℕ) : 0 < modelSchurEigen μ m :=
  lt_trans (modelRoot_pos hμ) (modelRoot_lt_modelSchurEigen hμ m)

end ModelProblem

end SaadSparse.Chapter14
