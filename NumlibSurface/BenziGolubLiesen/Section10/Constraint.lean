/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Numlib.Preconditioner.Constraint

/-!
# Benzi, Golub and Liesen, Section 10.2: Constraint and indefinite preconditioning

This module formalizes Theorem 10.1 of [benzi2005numerical], which describes the spectrum of a
saddle-point matrix after constraint preconditioning. Let $A, G \in \mathbb{R}^{n \times n}$ and
$B \in \mathbb{R}^{m \times n}$ with $\operatorname{rank} B = m$, and let the columns of
$Z \in \mathbb{R}^{n \times (n - m)}$ form a basis of $\ker B$. The constraint preconditioner
$\mathcal{P}$ keeps the constraint blocks of $\mathcal{A}$ and replaces $A$ by $G$:
$$\mathcal{A} = \begin{bmatrix} A & B^T \\ B & 0 \end{bmatrix}, \qquad \mathcal{P} = \begin{bmatrix}
  G & B^T \\ B & 0 \end{bmatrix}.$$
The characteristic polynomial of $\mathcal{P}^{-1}\mathcal{A}$ is $(\lambda - 1)^{2m}$ times the
characteristic polynomial of the reduced matrix $(Z^TGZ)^{-1}Z^TAZ$, and the eigenvectors of
$\mathcal{P}^{-1}\mathcal{A}$ come from the kernel of $A - G$, the multiplier coordinates, and the
eigenvectors of the reduced pencil $(Z^TAZ, Z^TGZ)$. The proofs specialize results in
`Numlib.Preconditioner.Constraint`.

## Main results

* Theorem 10.1, `BenziGolubLiesen.theorem_10_1`: $Z^TGZ$ is nonsingular, $\det(\lambda I -
  \mathcal{P}^{-1}\mathcal{A}) = (\lambda - 1)^{2m} \det\big(\lambda I - (Z^TGZ)^{-1}Z^TAZ\big)$,
  and, if $Z^TGZ$ is positive definite, $\mathcal{P}^{-1}\mathcal{A}$ has an explicit family of
  linearly independent eigenvectors.
* Counterexample for Theorem 10.1, `BenziGolubLiesen.theorem_10_1_multiplicity_example`: for
  $A = \operatorname{diag}(2, 1)$, $G = I$ and $B = [1, 0]$, the eigenvalue $1$ has multiplicity
  $3 > 2m$.

## Implementation notes

* The dimensions are natural numbers, and the block matrices are indexed by `Fin n ⊕ Fin m`.
* The basis $Z$ of $\ker B$ is given by two hypotheses: $Z$ is injective, and the range of $Z$ is
  $\ker B$.

## Deviations from the source

* **Theorem 10.1** (correction). The eigenvalue $1$ of $\mathcal{P}^{-1}\mathcal{A}$ can have
  multiplicity greater than $2m$, because the reduced pencil can also have the eigenvalue $1$. See
  `BenziGolubLiesen.theorem_10_1` and `BenziGolubLiesen.theorem_10_1_multiplicity_example`.
* **Theorem 10.1** (reading). The source's nonsingularity condition is on the full saddle
  matrix $\mathcal A$. The formal statement retains this condition.
-/

open Matrix Polynomial

namespace BenziGolubLiesen

/-- **Theorem 10.1** of [benzi2005numerical]. Let $m < n$, let $A, G \in \mathbb{R}^{n \times n}$ be
symmetric with $G \neq A$, let $B \in \mathbb{R}^{m \times n}$ have rank $m$, and let
$Z \in \mathbb{R}^{n \times (n - m)}$ be injective with range $\ker B$. Assume that
$$\mathcal{A} = \begin{bmatrix} A & B^T \\ B & 0 \end{bmatrix} \quad \text{and} \quad
  \mathcal{P} = \begin{bmatrix} G & B^T \\ B & 0 \end{bmatrix}$$
are nonsingular, and let $M = \mathcal{P}^{-1}\mathcal{A}$. Then:

* $Z^TGZ$ is nonsingular;
* the characteristic polynomial of $M$ is $$\det(\lambda I - M) = (\lambda - 1)^{2m}
  \det\big(\lambda I - (Z^TGZ)^{-1}Z^TAZ\big);$$
* if $Z^TGZ$ is positive definite, let $p = \dim \ker(A - G)$. There are vectors
  $w_1, \dots, w_p \in \mathbb{R}^n$ with $Aw_i = Gw_i$, eigenpairs $(d_j, z_j)$,
  $j = 1, \dots, n - m$, of the reduced pencil (that is, $z_j \neq 0$ and
  $Z^TAZ z_j = d_j Z^TGZ z_j$) with $z_1, \dots, z_{n-m}$ linearly independent, and vectors
  $y_j \in \mathbb{R}^m$ for each $j$ with $d_j \neq 1$, such that the vectors $$\begin{bmatrix}
  0 \\ e_l \end{bmatrix} \ (l = 1, \dots, m), \qquad \begin{bmatrix} w_i \\ 0 \end{bmatrix} \
  (i = 1, \dots, p), \qquad \begin{bmatrix} Zz_j \\ y_j \end{bmatrix} \ (d_j \neq 1)$$ are
  linearly independent, each vector $v$ of the first two families satisfies $Mv = v$, and the
  vector $v_j = (Zz_j, y_j)$ of the third family satisfies $Mv_j = d_j v_j$.

**Correction.** The source gives the eigenvalue $1$ of $M$ the multiplicity $2m$. The factor
$(\lambda - 1)^{2m}$ is always present, but the reduced pencil can supply further roots at $1$.
For $A = \operatorname{diag}(2, 1)$, $G = I$ and $B = [1, 0]$, the characteristic polynomial is
$(\lambda - 1)^3$; see `BenziGolubLiesen.theorem_10_1_multiplicity_example`. The statement
therefore gives the factorization of the characteristic polynomial.

The source assumes nonsingularity of the full saddle matrix $\mathcal A$. The declaration
retains that assumption, although its proof does not use it.

In the original coordinates, the eigenvector lifted from a reduced eigenvector $z_j$ has primal
component $Zz_j$. The vectors $e_l$ are the coordinate vectors of $\mathbb{R}^m$, written
`Pi.single l 1`, and the pair $(x, y)$ is `Sum.elim x y`. The proof does not use the hypotheses
that $G$ is symmetric, that $G \neq A$, that $m < n$, and that $\mathcal{A}$ is nonsingular. It
specializes `Matrix.charpoly_constraintPreconditioned` and
`Matrix.exists_constraintPreconditioned_eigenvectors`. -/
theorem theorem_10_1 {n m : ℕ} {A G : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin m) (Fin n) ℝ}
    {Z : Matrix (Fin n) (Fin (n - m)) ℝ} (hA : A.IsSymm) (_hG : G.IsSymm) (_hGA : G ≠ A)
    (_hmn : m < n) (hB : B.rank = m)
    (_hAUnit : IsUnit (fromBlocks A Bᵀ B 0)) (hP : IsUnit (fromBlocks G Bᵀ B 0))
    (hZi : Function.Injective Z.mulVec)
    (hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin) :
    let M := (fromBlocks G Bᵀ B 0)⁻¹ * fromBlocks A Bᵀ B 0
    let Ared := Zᵀ * A * Z
    let Gred := Zᵀ * G * Z
    IsUnit Gred ∧ M.charpoly = (X - 1) ^ (2 * m) * (Gred⁻¹ * Ared).charpoly ∧
      (Gred.PosDef →
        ∃ (w : Fin (Module.finrank ℝ (LinearMap.ker (A - G).mulVecLin)) → Fin n → ℝ)
          (d : Fin (n - m) → ℝ) (z : Fin (n - m) → Fin (n - m) → ℝ)
          (y : {j // d j ≠ 1} → Fin m → ℝ),
          (∀ i, A *ᵥ w i = G *ᵥ w i) ∧
          (∀ j, HasPencilEigenvector Ared Gred (d j) (z j)) ∧
          LinearIndependent ℝ z ∧
          let u := Sum.elim (fun j : Fin m => Sum.elim (0 : Fin n → ℝ) (Pi.single j 1))
            (fun i => Sum.elim (w i) (0 : Fin m → ℝ))
          let v := fun j : {j // d j ≠ 1} => Sum.elim (Z *ᵥ z j) (y j)
          LinearIndependent ℝ (Sum.elim u v) ∧ (∀ i, M *ᵥ u i = u i) ∧
            (∀ j, M *ᵥ v j = d j • v j)) := by
  have hP' : IsUnit (saddleMatrix G Bᴴ 0) := by
    simpa [saddleMatrix, conjTranspose_eq_transpose_of_trivial] using hP
  have hBs : Function.Surjective B.mulVec :=
    mulVec_surjective_iff_rank_eq_card.mpr (by simpa using hB)
  refine ⟨?_, ?_, fun hGred => ?_⟩
  · simpa [conjTranspose_eq_transpose_of_trivial] using isUnit_nullspaceCompression hZi hZ hP'
  · simpa [constraintPreconditioned, saddleMatrix, conjTranspose_eq_transpose_of_trivial] using
      charpoly_constraintPreconditioned (A := A) hBs hZi hZ hP'
  · have hG' : (Zᴴ * G * Z).PosDef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hGred
    simpa [constraintPreconditioned, saddleMatrix, conjTranspose_eq_transpose_of_trivial] using
      exists_constraintPreconditioned_eigenvectors (isHermitian_iff_isSymm.mpr hA) hZi hZ hP' hG'

/-- A counterexample to the multiplicity $2m$ printed in Theorem 10.1 of [benzi2005numerical]. There
are symmetric $A, G \in \mathbb{R}^{2 \times 2}$ with $G \neq A$ and
$B \in \mathbb{R}^{1 \times 2}$ of rank $1$ such that $\mathcal{A} = \begin{bmatrix} A & B^T \\
B & 0 \end{bmatrix}$ and $\mathcal{P} = \begin{bmatrix} G & B^T \\ B & 0 \end{bmatrix}$ are
nonsingular and
$$\det(\lambda I - \mathcal{P}^{-1}\mathcal{A}) = (\lambda - 1)^3.$$
So the eigenvalue $1$ has multiplicity $3$, which exceeds $2m = 2$, even though both
saddle-point matrices are nonsingular and $A \neq G$.

The proof uses $A = \operatorname{diag}(2, 1)$, $G = I$ and $B = [1, 0]$. Here $\ker B$ is
spanned by $Z = [0, 1]^T$, and the reduced pencil $(Z^TAZ, Z^TGZ) = (1, 1)$ has the eigenvalue
$1$. -/
theorem theorem_10_1_multiplicity_example :
    ∃ (A G : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 1) (Fin 2) ℝ),
      A.IsSymm ∧ G.IsSymm ∧ G ≠ A ∧ B.rank = 1 ∧
      IsUnit (fromBlocks A Bᵀ B 0) ∧ IsUnit (fromBlocks G Bᵀ B 0) ∧
      ((fromBlocks G Bᵀ B 0)⁻¹ * fromBlocks A Bᵀ B 0).charpoly = (X - 1) ^ 3 := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![2, 1]
  let G : Matrix (Fin 2) (Fin 2) ℝ := 1
  let B : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
  let Z : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
  have hA : A.PosDef := posDef_diagonal_iff.mpr (by intro i; fin_cases i <;> norm_num)
  have hG : G.PosDef := PosDef.one
  have hGA : G ≠ A := by
    intro h
    have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [G, A] at h'
  have hB : ∀ x : Fin 2 → ℝ, B *ᵥ x = ![x 0] := by
    intro x
    funext i
    fin_cases i
    simp [B, mulVec, dotProduct, Fin.sum_univ_two]
  have hBT : Function.Injective Bᵀ.mulVec := by
    intro x y h
    funext i
    fin_cases i
    have h' := congrFun h (0 : Fin 2)
    simpa [B, mulVec, dotProduct, Fin.sum_univ_one] using h'
  have hBs : Function.Surjective B.mulVec := by
    intro y
    refine ⟨![y 0, 0], ?_⟩
    rw [hB]
    funext i
    fin_cases i
    rfl
  have hZcol : ∀ z : Fin 1 → ℝ, Z *ᵥ z = ![0, z 0] := by
    intro z
    funext i
    fin_cases i <;> simp [Z, mulVec, dotProduct]
  have hZi : Function.Injective Z.mulVec := by
    intro x y h
    simp only [hZcol] at h
    funext i
    fin_cases i
    simpa using congrFun h (1 : Fin 2)
  have hZ : LinearMap.range Z.mulVecLin = LinearMap.ker B.mulVecLin := by
    ext x
    change (∃ z, Z *ᵥ z = x) ↔ B *ᵥ x = 0
    simp only [hZcol, hB]
    constructor
    · rintro ⟨z, rfl⟩
      funext i
      fin_cases i
      rfl
    · intro hx
      refine ⟨![x 1], ?_⟩
      funext i
      fin_cases i
      · simpa using (congrFun hx (0 : Fin 1)).symm
      · rfl
  have hPA : IsUnit (fromBlocks A Bᵀ B 0) := by
    simpa [saddleMatrix, conjTranspose_eq_transpose_of_trivial] using
      (isUnit_saddleMatrix_zero hA hBT)
  have hPG : IsUnit (fromBlocks G Bᵀ B 0) := by
    simpa [saddleMatrix, conjTranspose_eq_transpose_of_trivial] using
      (isUnit_saddleMatrix_zero hG hBT)
  have hBr : B.rank = 1 := by simpa using mulVec_surjective_iff_rank_eq_card.mp hBs
  have hAr : Zᵀ * A * Z = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Z, A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  have hGr : Zᵀ * G * Z = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Z, G, Matrix.mul_apply, Fin.sum_univ_two]
  have hc := (theorem_10_1 hA.1.isSymm hG.1.isSymm hGA (by decide) hBr hPA hPG hZi hZ).2.1
  rw [hAr, hGr, inv_one, Matrix.one_mul, Matrix.charpoly_one] at hc
  refine ⟨A, G, B, hA.1.isSymm, hG.1.isSymm, hGA, hBr, hPA, hPG, ?_⟩
  rw [hc]
  simp
  ring

end BenziGolubLiesen
