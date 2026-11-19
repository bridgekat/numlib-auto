/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.DomainDecomposition.Schur
import NumlibSurface.SaadSparse.Chapter14.Section02

/-!
# Saad, Section 14.5: Full matrix methods

This module formalizes Section 14.5 of [saad2003iterative]. A *full matrix method* iterates on the
unreduced system (14.2) with a block preconditioner, and the section shows that this is the same
computation as a Schur complement method on the reduced system $Sy = g'$. An approximate
factorization $S \approx L_S U_S$ of the Schur complement induces the block preconditioners
$$L_A = \begin{pmatrix} I & 0 \\ F B^{-1} & L_S \end{pmatrix}, \qquad U_A = \begin{pmatrix} B & E \\
  0 & U_S \end{pmatrix}$$
of (14.55), and $L_S = U_S = I$ gives the preconditioners (14.49). The module proves the
factorizations (14.52), (14.58), (14.59) and (14.60) of $A$ through these blocks, the form (14.51)
and (14.57) of the iterates, and Propositions 14.11 and 14.12: a Krylov method on the
split-preconditioned full system $L_A^{-1} A U_A^{-1}$, started from a consistent initial guess,
produces the iterates of the same method on the (preconditioned) reduced system. The proofs
specialize `Numlib.DomainDecomposition.Schur`.

## Main definitions

* Equation (14.55), `SaadSparse.Chapter14.blockPreconditioner`: the block preconditioner
  $M_A = L_A U_A$.

## Main results

* Equation (14.49), `SaadSparse.Chapter14.blockLower_one` and `SaadSparse.Chapter14.blockUpper_one`:
  the preconditioners $L_A$ and $U_A$ for $L_S = U_S = I$.
* Equation (14.50), `SaadSparse.Chapter14.consistentGuess_eq`: the consistent initial guess
  $x_0 = (B^{-1}(f - E y_0), y_0)$.
* Equation (14.51), `SaadSparse.Chapter14.equation_14_51`: $U_A^{-1} (f, y)^T$ is the consistent
  vector $(B^{-1}(f - Ey), y)^T$.
* Equation (14.52), `SaadSparse.Chapter14.equation_14_52`: $A = L_A \operatorname{diag}(I, S) U_A$.
* Proposition 14.11, `SaadSparse.Chapter14.proposition_14_11`: the minimal-residual iterates of the
  preconditioned full system correspond to those of $Sy = g'$.
* Proposition 14.11, `SaadSparse.Chapter14.proposition_14_11_form`: every minimal-residual iterate
  of the preconditioned full system has the form (14.51).
* Proposition 14.11, `SaadSparse.Chapter14.proposition_14_11_galerkin`: the same correspondence for
  Galerkin iterates.
* Equation (14.57), `SaadSparse.Chapter14.equation_14_57`: $U_A^{-1} (f, U_S y)^T$ is the consistent
  vector $(B^{-1}(f - Ey), y)^T$.
* Equation (14.58), `SaadSparse.Chapter14.equation_14_58`: $A = L_A \operatorname{diag}(I, L_S^{-1}
  S U_S^{-1}) U_A$.
* Proposition 14.12, `SaadSparse.Chapter14.proposition_14_12`: the minimal-residual iterates of the
  full system correspond to those of $L_S^{-1} S U_S^{-1}$.
* Proposition 14.12, `SaadSparse.Chapter14.proposition_14_12_form`: every such iterate has the form
  (14.57).
* Proposition 14.12, `SaadSparse.Chapter14.proposition_14_12_galerkin`: the same correspondence for
  Galerkin iterates.
* Equation (14.59), `SaadSparse.Chapter14.equation_14_59`: the factorization that preconditions $S$
  from the left by $M_S$.
* Equation (14.60), `SaadSparse.Chapter14.equation_14_60`: the factorization that preconditions $S$
  from the right by $M_S$.
* Section 14.5, `SaadSparse.Chapter14.blockPreconditioner_eq_fromBlocks`: if $L_S U_S = S$, then
  $M_A = A$.

## Implementation notes

* The block preconditioners are the backbone `DomainDecomposition.blockLower B F L_S` and
  `DomainDecomposition.blockUpper B E U_S`, the split-preconditioned matrix $L_A^{-1} A U_A^{-1}$ is
  `DomainDecomposition.precondMatrix`, and the consistent initial guess (14.50)/(14.56) is
  `DomainDecomposition.consistentGuess B E f y₀`.
* A Krylov method is given by its specification: `Krylov.IsMinResidualIterate` (GMRES, MINRES) says
  that the $k$-th iterate minimizes the residual norm over $x_0 + \mathcal{K}_k(A, r_0)$, and
  `Krylov.IsGalerkinIterate` (FOM, CG, the Lanczos method) says that the $k$-th iterate lies in
  $x_0 + \mathcal{K}_k(A, r_0)$ and has its residual orthogonal to $\mathcal{K}_k(A, r_0)$.
* Both sides of each correspondence are written in the variable on which the split-preconditioned
  method iterates: $u = U_A x$ on the full system, and $w = U_S y$ on the reduced system.
  `SaadSparse.Chapter14.equation_14_51` and `SaadSparse.Chapter14.equation_14_57` translate $u$ back
  into the book's $x_m$.

## Deviations from the source

* **(14.55) and Proposition 14.12** (domain). `SaadSparse.Chapter14.blockPreconditioner` defines
  the product using the total inverse of $B$. The correspondence theorems assume invertible
  $B,L_S,U_S$. They need no separate approximate factorization remainder because $L_SU_S-S$ is
  determined by those factors.
* **Propositions 14.11 and 14.12** (generalization). `SaadSparse.Chapter14.proposition_14_11`
  and `SaadSparse.Chapter14.proposition_14_12` also give the converse for a candidate in the
  consistent form. The source states the direction from full-system iterates to reduced-system
  iterates.
* **Propositions 14.11 and 14.12** (reading). The book speaks of "the same Krylov subspace method",
  which is not a formal object. The propositions are stated for the minimal-residual and the
  Galerkin specifications, in the variables $u = U_A x$ and $w = U_S y$. See
  `SaadSparse.Chapter14.proposition_14_11` and `SaadSparse.Chapter14.proposition_14_12`.
-/

open Matrix DomainDecomposition

namespace SaadSparse.Chapter14

variable {p q : ℕ} {B : Matrix (Fin p) (Fin p) ℝ} {E : Matrix (Fin p) (Fin q) ℝ}
variable {F : Matrix (Fin q) (Fin p) ℝ} {C : Matrix (Fin q) (Fin q) ℝ}
variable {LS US MS : Matrix (Fin q) (Fin q) ℝ}

/-! ### The block preconditioners (14.49) and (14.55) -/

/-- **Equation (14.49)** of [saad2003iterative]. For $L_S = I$, the left preconditioner is
$$L_A = \begin{pmatrix} I & 0 \\ F B^{-1} & I \end{pmatrix}.$$
-/
theorem blockLower_one : blockLower B F 1 = fromBlocks 1 0 (F * B⁻¹) 1 := rfl

/-- **Equation (14.49)** of [saad2003iterative]. For $U_S = I$, the right preconditioner is
$$U_A = \begin{pmatrix} B & E \\ 0 & I \end{pmatrix}.$$
-/
theorem blockUpper_one : blockUpper B E 1 = fromBlocks B E 0 1 := rfl

/-- **Equations (14.50) and (14.56)** of [saad2003iterative]. For $f \in \mathbb{R}^p$ and
$y \in \mathbb{R}^q$, the consistent vector with interface part $y$ is
$$\begin{pmatrix} B^{-1}(f - E y) \\ y \end{pmatrix}.$$
At $y = y_0$ it is the consistent initial guess $x_0$. -/
theorem consistentGuess_eq (f : Fin p → ℝ) (y : Fin q → ℝ) :
    consistentGuess B E f y = Sum.elim (B⁻¹ *ᵥ (f - E *ᵥ y)) y := rfl

/-- The reduced right-hand side $g' = g - F B^{-1} f$ of Section 14.2 is the backbone
`DomainDecomposition.reducedRhs`. -/
theorem reducedRhs_eq (B : Matrix (Fin p) (Fin p) ℝ) (F : Matrix (Fin q) (Fin p) ℝ)
    (f : Fin p → ℝ) (g : Fin q → ℝ) :
    reducedRhs B F f g = DomainDecomposition.reducedRhs B F f g := rfl

/-- For $L_S = U_S = I$, the preconditioned Schur complement $L_S^{-1} S U_S^{-1}$ is $S$ itself. -/
theorem precondSchurComplement_one_one :
    precondSchurComplement B E F C 1 1 = schurComplement B E F C := by
  rw [precondSchurComplement, inv_one, Matrix.one_mul, Matrix.mul_one]
  exact (schurComplement_eq B E F C).symm

/-- **Equation (14.55)** of [saad2003iterative]. Let $B \in \mathbb{R}^{p \times p}$,
$E \in \mathbb{R}^{p \times q}$, $F \in \mathbb{R}^{q \times p}$, and let
$L_S, U_S \in \mathbb{R}^{q \times q}$ be an approximate factorization $S \approx L_S U_S$ of
the Schur complement. The **block preconditioner** of the full matrix is
$$M_A = L_A U_A = \begin{pmatrix} I & 0 \\ F B^{-1} & L_S \end{pmatrix} \begin{pmatrix} B & E \\
  0 & U_S \end{pmatrix}.$$

For $L_S = U_S = I$ it is the preconditioner (14.49).

**Representation.** This defines the product of the two block factors for every input, using
the total inverse of $B$ in the lower factor. -/
noncomputable def blockPreconditioner (B : Matrix (Fin p) (Fin p) ℝ) (E : Matrix (Fin p) (Fin q) ℝ)
    (F : Matrix (Fin q) (Fin p) ℝ) (LS US : Matrix (Fin q) (Fin q) ℝ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  blockLower B F LS * blockUpper B E US

/-- **Equation (14.52)** of [saad2003iterative]. Let $B$ be nonsingular. Then
$$\begin{pmatrix} B & E \\ F & C \end{pmatrix} = \begin{pmatrix} I & 0 \\ F B^{-1} & I
  \end{pmatrix} \begin{pmatrix} I & 0 \\ 0 & S \end{pmatrix} \begin{pmatrix} B & E \\ 0 & I
  \end{pmatrix},$$
where $S = C - F B^{-1} E$. This is the factorization behind Proposition 14.11. -/
theorem equation_14_52 (hB : IsUnit B) :
    fromBlocks B E F C
      = blockLower B F 1 * fromBlocks 1 0 0 (schurComplement B E F C) * blockUpper B E 1 := by
  rw [← precondSchurComplement_one_one]
  exact fromBlocks_eq_blockLower_mul hB isUnit_one isUnit_one

/-- **Equation (14.58)** of [saad2003iterative]. Let $B$, $L_S$ and $U_S$ be nonsingular, and let
$L_A$, $U_A$ be the block preconditioners (14.55). Then
$$\begin{pmatrix} B & E \\ F & C \end{pmatrix} = L_A \begin{pmatrix} I & 0 \\ 0 & L_S^{-1} S
  U_S^{-1} \end{pmatrix} U_A.$$
This is the factorization behind Proposition 14.12. -/
theorem equation_14_58 (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) :
    fromBlocks B E F C
      = blockLower B F LS * fromBlocks 1 0 0 (LS⁻¹ * schurComplement B E F C * US⁻¹)
        * blockUpper B E US :=
  fromBlocks_eq_blockLower_mul hB hLS hUS

/-- **Equation (14.59)** of [saad2003iterative]. Let $B$ and $M_S$ be nonsingular. Then
$$\begin{pmatrix} B & E \\ F & C \end{pmatrix} = \begin{pmatrix} I & 0 \\ F B^{-1} & M_S
  \end{pmatrix} \begin{pmatrix} I & 0 \\ 0 & M_S^{-1} S \end{pmatrix} \begin{pmatrix} B & E \\ 0
  & I \end{pmatrix}.$$
This is the factorization that preconditions $S$ from the left by $M_S$. -/
theorem equation_14_59 (hB : IsUnit B) (hMS : IsUnit MS) :
    fromBlocks B E F C
      = blockLower B F MS * fromBlocks 1 0 0 (MS⁻¹ * schurComplement B E F C)
        * blockUpper B E 1 := by
  have h := fromBlocks_eq_blockLower_mul (E := E) (F := F) (C := C) hB hMS isUnit_one
  rwa [precondSchurComplement, inv_one, Matrix.mul_one] at h

/-- **Equation (14.60)** of [saad2003iterative]. Let $B$ and $M_S$ be nonsingular. Then
$$\begin{pmatrix} B & E \\ F & C \end{pmatrix} = \begin{pmatrix} I & 0 \\ F B^{-1} & I
  \end{pmatrix} \begin{pmatrix} I & 0 \\ 0 & S M_S^{-1} \end{pmatrix} \begin{pmatrix} B & E \\ 0
  & M_S \end{pmatrix}.$$
This is the factorization that preconditions $S$ from the right by $M_S$. -/
theorem equation_14_60 (hB : IsUnit B) (hMS : IsUnit MS) :
    fromBlocks B E F C
      = blockLower B F 1 * fromBlocks 1 0 0 (schurComplement B E F C * MS⁻¹)
        * blockUpper B E MS := by
  have h := fromBlocks_eq_blockLower_mul (E := E) (F := F) (C := C) hB isUnit_one hMS
  rwa [precondSchurComplement, inv_one, Matrix.one_mul] at h

/-- **Section 14.5** of [saad2003iterative], the closing remark. Let $B$ be nonsingular, and let
$L_S U_S = S$. Then the block preconditioner $M_A = L_A U_A$ of (14.55) is the matrix $A =
\begin{pmatrix} B & E \\ F & C \end{pmatrix}$ itself.

So an exact preconditioner of $S$ induces an exact block preconditioner of $A$. -/
theorem blockPreconditioner_eq_fromBlocks (hB : IsUnit B) (h : LS * US = schurComplement B E F C) :
    blockPreconditioner B E F LS US = fromBlocks B E F C := by
  have h1 : F * B⁻¹ * B = F := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul B
    ((Matrix.isUnit_iff_isUnit_det B).1 hB), Matrix.mul_one]
  rw [blockPreconditioner, blockLower, blockUpper, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [h1, h, schurComplement_def]
  congr 1
  abel

/-- **Equation (14.51)** of [saad2003iterative]. Let $B$ be nonsingular, and let $U_A$ be the right
preconditioner (14.49). Then for $f \in \mathbb{R}^p$ and $y \in \mathbb{R}^q$
$$U_A^{-1} \begin{pmatrix} f \\ y \end{pmatrix} = \begin{pmatrix} B^{-1}(f - E y) \\ y
  \end{pmatrix}.$$

An iterate of the preconditioned full system, read back in the original variable through
$x = U_A^{-1} u$, therefore has again the consistent form $x_m = (B^{-1}(f - E y_m), y_m)$. -/
theorem equation_14_51 (hB : IsUnit B) (f : Fin p → ℝ) (y : Fin q → ℝ) :
    (blockUpper B E 1)⁻¹ *ᵥ Sum.elim f y = Sum.elim (B⁻¹ *ᵥ (f - E *ᵥ y)) y := by
  have h := blockUpper_inv_mulVec (E := E) (US := 1) hB isUnit_one f y
  rwa [Matrix.one_mulVec] at h

/-- **Equation (14.57)** of [saad2003iterative]. Let $B$ and $U_S$ be nonsingular, and let $U_A$ be
the right preconditioner (14.55). Then for $f \in \mathbb{R}^p$ and $y \in \mathbb{R}^q$
$$U_A^{-1} \begin{pmatrix} f \\ U_S y \end{pmatrix} = \begin{pmatrix} B^{-1}(f - E y) \\ y
  \end{pmatrix}.$$
-/
theorem equation_14_57 (hB : IsUnit B) (hUS : IsUnit US) (f : Fin p → ℝ) (y : Fin q → ℝ) :
    (blockUpper B E US)⁻¹ *ᵥ Sum.elim f (US *ᵥ y) = Sum.elim (B⁻¹ *ᵥ (f - E *ᵥ y)) y :=
  blockUpper_inv_mulVec hB hUS f y

/-! ### Propositions 14.11 and 14.12 -/

/-- **Proposition 14.11** of [saad2003iterative]. Let $B$ be nonsingular, let $f \in \mathbb{R}^p$
and $g, y_0, y \in \mathbb{R}^q$, and let $k \in \mathbb{N}$. Let $L_A$ and $U_A$ be the
preconditioners (14.49), and for $z \in \mathbb{R}^q$ let $x(z) = (B^{-1}(f - E z), z)$ be the
consistent vector with interface part $z$. Consider a minimal-residual Krylov method on the full
system
$$L_A^{-1} A U_A^{-1} u = L_A^{-1} \begin{pmatrix} f \\ g \end{pmatrix}$$
from the initial guess $u_0 = U_A x(y_0)$. Then $U_A x(y)$ is its iterate at step $k$ if and
only if $y$ is the iterate at step $k$ of the same method on the reduced system $S y = g'$ from
$y_0$, without preconditioning.

**Reading.** The book states the proposition for "the same Krylov subspace method", which is not
a formal object. Here the method is given by its specification `Krylov.IsMinResidualIterate`,
which covers GMRES and MINRES; `SaadSparse.Chapter14.proposition_14_11_galerkin` is the Galerkin
version. Both sides are written in the variable on which the split-preconditioned method
iterates: $u = U_A x$ on the full system, and $y$ itself on the reduced system, since $U_S = I$
here. The book states one direction, that the iteration produces iterates of the form (14.51);
this is `SaadSparse.Chapter14.proposition_14_11_form`, and the equivalence here is stronger.

`SaadSparse.Chapter14.equation_14_51` turns the iterate $u$ back into the book's $x_m$. -/
theorem proposition_14_11 (hB : IsUnit B) (f : Fin p → ℝ) (g y₀ y : Fin q → ℝ) (k : ℕ) :
    Krylov.IsMinResidualIterate (toEuclideanLin (precondMatrix B E F C 1 1))
        (WithLp.toLp 2 ((blockLower B F 1)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsMinResidualIterate (toEuclideanLin (schurComplement B E F C))
        (WithLp.toLp 2 (reducedRhs B F f g)) (WithLp.toLp 2 y₀) k (WithLp.toLp 2 y) := by
  have h := isMinResidual_iff_isMinResidual_schurComplement (E := E) (F := F) (C := C) (LS := 1)
    (US := 1) hB isUnit_one isUnit_one f g y₀ y k
  rw [precondSchurComplement_one_one, ← reducedRhs_eq] at h
  simpa only [inv_one, Matrix.one_mulVec] using h

/-- **Proposition 14.11** of [saad2003iterative], in the direction that the book states. Let $B$ be
nonsingular, let $L_A$, $U_A$ be the preconditioners (14.49), and let $u$ be the iterate at step
$k$ of a minimal-residual Krylov method on the preconditioned full system
$L_A^{-1} A U_A^{-1} u = L_A^{-1} (f, g)^T$ from $u_0 = U_A x_0$, where
$x_0 = (B^{-1}(f - E y_0), y_0)$ is consistent. Then there is $y \in \mathbb{R}^q$ such that $y$
is the iterate at step $k$ of the same method on $S y = g'$ from $y_0$, and
$$u = U_A \begin{pmatrix} B^{-1}(f - E y) \\ y \end{pmatrix}.$$

So the preconditioned iteration *produces* iterates of the form (14.51).
`SaadSparse.Chapter14.equation_14_51` recovers $x$ from $u$.

**Reading.** Book's forward form for minimal-residual iterates, stated in transformed unknowns.
-/
theorem proposition_14_11_form (hB : IsUnit B) (f : Fin p → ℝ) (g y₀ : Fin q → ℝ) (k : ℕ)
    {u : EuclideanSpace ℝ (Fin p ⊕ Fin q)}
    (hu : Krylov.IsMinResidualIterate (toEuclideanLin (precondMatrix B E F C 1 1))
      (WithLp.toLp 2 ((blockLower B F 1)⁻¹ *ᵥ Sum.elim f g))
      (WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y₀)) k u) :
    ∃ y : Fin q → ℝ,
      Krylov.IsMinResidualIterate (toEuclideanLin (schurComplement B E F C))
          (WithLp.toLp 2 (reducedRhs B F f g)) (WithLp.toLp 2 y₀) k (WithLp.toLp 2 y)
        ∧ u = WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y) := by
  obtain ⟨y, hy, hyu⟩ := exists_isMinResidual_schurComplement (E := E) (F := F) (C := C) (LS := 1)
    (US := 1) hB isUnit_one isUnit_one f g y₀ k hu
  refine ⟨y, ?_, hyu⟩
  rw [precondSchurComplement_one_one, ← reducedRhs_eq] at hy
  simpa only [inv_one, Matrix.one_mulVec] using hy

/-- **Proposition 14.12** of [saad2003iterative], in the direction that the book states. Let $B$,
$L_S$ and $U_S$ be nonsingular, let $L_A$, $U_A$ be the block preconditioners (14.55), and let
$u$ be the iterate at step $k$ of a minimal-residual Krylov method on
$L_A^{-1} A U_A^{-1} u = L_A^{-1} (f, g)^T$ from $u_0 = U_A x_0$, where
$x_0 = (B^{-1}(f - E y_0), y_0)$ is consistent (14.56). Then there is $y \in \mathbb{R}^q$ such
that $U_S y$ is the iterate at step $k$ of the same method on
$$L_S^{-1} S U_S^{-1} w = L_S^{-1} g'$$
from $U_S y_0$, and $u = U_A (B^{-1}(f - E y), y)^T$.

So the iterates have the form (14.57), and their interface blocks are the iterates of the
split-preconditioned reduced method.

**Reading.** Forward form for minimal-residual iterates with invertible split factors and no
explicit remainder variable.
-/
theorem proposition_14_12_form (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) (f : Fin p → ℝ)
    (g y₀ : Fin q → ℝ) (k : ℕ) {u : EuclideanSpace ℝ (Fin p ⊕ Fin q)}
    (hu : Krylov.IsMinResidualIterate (toEuclideanLin (precondMatrix B E F C LS US))
      (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
      (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k u) :
    ∃ y : Fin q → ℝ,
      Krylov.IsMinResidualIterate (toEuclideanLin (LS⁻¹ * schurComplement B E F C * US⁻¹))
          (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
          (WithLp.toLp 2 (US *ᵥ y))
        ∧ u = WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y) :=
  exists_isMinResidual_schurComplement hB hLS hUS f g y₀ k hu

/-- **Proposition 14.11** of [saad2003iterative], Galerkin form. Let $B$ be nonsingular, and let
$L_A$, $U_A$ and the consistent vectors $x(z)$ be as in
`SaadSparse.Chapter14.proposition_14_11`. Then $U_A x(y)$ is the Galerkin iterate at step $k$ of
the preconditioned full system $L_A^{-1} A U_A^{-1} u = L_A^{-1} (f, g)^T$ from $U_A x(y_0)$ if
and only if $y$ is the Galerkin iterate at step $k$ of $S y = g'$ from $y_0$.

The Galerkin specification `Krylov.IsGalerkinIterate` covers FOM, CG and the Lanczos method.

**Reading.** Galerkin specification in transformed variables, stated as equivalence.
-/
theorem proposition_14_11_galerkin (hB : IsUnit B) (f : Fin p → ℝ) (g y₀ y : Fin q → ℝ) (k : ℕ) :
    Krylov.IsGalerkinIterate (toEuclideanLin (precondMatrix B E F C 1 1))
        (WithLp.toLp 2 ((blockLower B F 1)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E 1 *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsGalerkinIterate (toEuclideanLin (schurComplement B E F C))
        (WithLp.toLp 2 (reducedRhs B F f g)) (WithLp.toLp 2 y₀) k (WithLp.toLp 2 y) := by
  have h := isGalerkin_iff_isGalerkin_schurComplement (E := E) (F := F) (C := C) (LS := 1)
    (US := 1) hB isUnit_one isUnit_one f g y₀ y k
  rw [precondSchurComplement_one_one, ← reducedRhs_eq] at h
  simpa only [inv_one, Matrix.one_mulVec] using h

/-- **Proposition 14.12** of [saad2003iterative]. Let $B$, $L_S$ and $U_S$ be nonsingular, let
$f \in \mathbb{R}^p$ and $g, y_0, y \in \mathbb{R}^q$, and let $k \in \mathbb{N}$. Let $L_A$ and
$U_A$ be the block preconditioners (14.55), and let $x(z) = (B^{-1}(f - E z), z)$ be the
consistent vector with interface part $z$, as in (14.56). Then $U_A x(y)$ is the iterate at step
$k$ of a minimal-residual Krylov method on
$$L_A^{-1} A U_A^{-1} u = L_A^{-1} \begin{pmatrix} f \\ g \end{pmatrix}$$
from $U_A x(y_0)$ if and only if $U_S y$ is the iterate at step $k$ of the same method on the
reduced system preconditioned on the left by $L_S$ and on the right by $U_S$,
$$L_S^{-1} S U_S^{-1} w = L_S^{-1} g',$$
from $U_S y_0$.

**Reading.** As for `SaadSparse.Chapter14.proposition_14_11`, "the same Krylov subspace method"
is read as the specification `Krylov.IsMinResidualIterate`, and both sides are written in the
variables of the split-preconditioned methods, $u = U_A x$ and $w = U_S y$.
`SaadSparse.Chapter14.proposition_14_12_galerkin` is the Galerkin version, and
`SaadSparse.Chapter14.proposition_14_12_form` is the one-way form of the book. -/
theorem proposition_14_12 (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US) (f : Fin p → ℝ)
    (g y₀ y : Fin q → ℝ) (k : ℕ) :
    Krylov.IsMinResidualIterate (toEuclideanLin (precondMatrix B E F C LS US))
        (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsMinResidualIterate (toEuclideanLin (LS⁻¹ * schurComplement B E F C * US⁻¹))
        (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
        (WithLp.toLp 2 (US *ᵥ y)) :=
  isMinResidual_iff_isMinResidual_schurComplement hB hLS hUS f g y₀ y k

/-- **Proposition 14.12** of [saad2003iterative], Galerkin form. Let $B$, $L_S$ and $U_S$ be
nonsingular, and let $L_A$, $U_A$ and $x(z)$ be as in `SaadSparse.Chapter14.proposition_14_12`.
Then $U_A x(y)$ is the Galerkin iterate at step $k$ of
$L_A^{-1} A U_A^{-1} u = L_A^{-1} (f, g)^T$ from $U_A x(y_0)$ if and only if $U_S y$ is the
Galerkin iterate at step $k$ of $L_S^{-1} S U_S^{-1} w = L_S^{-1} g'$ from $U_S y_0$.

**Reading.** Galerkin specification and converse with invertible factors and no specified remainder.
-/
theorem proposition_14_12_galerkin (hB : IsUnit B) (hLS : IsUnit LS) (hUS : IsUnit US)
    (f : Fin p → ℝ) (g y₀ y : Fin q → ℝ) (k : ℕ) :
    Krylov.IsGalerkinIterate (toEuclideanLin (precondMatrix B E F C LS US))
        (WithLp.toLp 2 ((blockLower B F LS)⁻¹ *ᵥ Sum.elim f g))
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y₀)) k
        (WithLp.toLp 2 (blockUpper B E US *ᵥ consistentGuess B E f y))
      ↔ Krylov.IsGalerkinIterate (toEuclideanLin (LS⁻¹ * schurComplement B E F C * US⁻¹))
        (WithLp.toLp 2 (LS⁻¹ *ᵥ reducedRhs B F f g)) (WithLp.toLp 2 (US *ᵥ y₀)) k
        (WithLp.toLp 2 (US *ᵥ y)) :=
  isGalerkin_iff_isGalerkin_schurComplement hB hLS hUS f g y₀ y k

end SaadSparse.Chapter14
