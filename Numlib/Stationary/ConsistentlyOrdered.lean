/-
Copyright (c) 2026 Great Bay University. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Numlib.Stationary.Splitting

/-!
# Consistently ordered matrices and Young's theory of SOR

This module relates the eigenvalues of the Jacobi iteration matrix $B$ to those of the SOR iteration
matrix $G_\omega$ for a consistently ordered matrix ([saad2003iterative], §4.2.5;
[kress1998numerical], §4.2). Write $A = D - E - F$, where $D$ is the diagonal of $A$ and $-E$ and
$-F$ are its strictly lower and strictly upper triangular parts. Put $L = D^{-1} E$ and
$U = D^{-1} F$, so that $B = L + U$ and $G_\omega = (D - \omega E)^{-1} (\omega F + (1 - \omega)
D)$. Following [kress1998numerical], $A$ is **consistently ordered** if the matrix
$C(\alpha) = \alpha L + \alpha^{-1} U$ has the same spectrum for every $\alpha \neq 0$. The main
theorem says: for $\omega \neq 0$ and $\lambda \neq 0$ with $(\lambda + \omega - 1)^2 = \lambda
\omega^2 \mu^2$, the number $\mu$ is an eigenvalue of $B$ if and only if $\lambda$ is an eigenvalue
of $G_\omega$. At $\omega = 1$ the relation reads $\lambda = \mu^2$, so $\rho(G_1) = \rho(B)^2$:
Gauss–Seidel converges twice as fast as Jacobi.

If moreover the eigenvalues of $B$ are real, the relation gives Young's formula for the SOR spectral
radius. Let $t = \omega \rho(B) / 2$ and $d = t^2 - (\omega - 1)$. Then
$\rho(G_\omega) = (t + \sqrt d)^2$ if $d \ge 0$, and $\rho(G_\omega) = \omega - 1$ if $d < 0$. This
value is **Young's radius** $Y(\omega, \rho(B))$. If $\rho(B) < 1$, then the optimal relaxation
parameter $\omega_{\mathrm{opt}} = 2 / (1 + \sqrt{1 - \rho(B)^2})$, where the discriminant $d$
vanishes, minimizes $\rho(G_\omega)$ over $0 < \omega < 2$, and the minimum is
$\omega_{\mathrm{opt}} - 1$.

## Main definitions

* `Matrix.sorIterationMatrix`: the SOR iteration matrix $G_\omega$ as a function of $\omega$.
* `Matrix.IsConsistentlyOrdered`: the spectrum of $\alpha L + \alpha^{-1} U$ does not depend on
  $\alpha \neq 0$.
* `Matrix.youngRadius`: Young's radius $Y(\omega, r)$, the modulus of the dominant root of Young's
  quadratic.
* `Matrix.optimalRelaxation`: the optimal relaxation parameter $\omega_{\mathrm{opt}}(r) = 2 / (1 +
  \sqrt{1 - r^2})$.

## Main results

* `Matrix.isConsistentlyOrdered_of_labelling`: the combinatorial condition of [saad2003iterative]
  implies consistent ordering.
* `Matrix.IsTridiagonal.isConsistentlyOrdered`: a tridiagonal matrix with invertible diagonal is
  consistently ordered.
* `Matrix.neg_mem_spectrum_fromBlocks_zero_zero`: the spectrum of a block anti-diagonal matrix is
  symmetric about $0$.
* `Matrix.IsConsistentlyOrdered.mem_spectrum_jacobi_iff_sor`: Young's eigenvalue relation between
  $B$ and $G_\omega$.
* `Matrix.IsConsistentlyOrdered.spectralRadius_gaussSeidel_eq_sq`: $\rho(G_1) = \rho(B)^2$.
* `Matrix.IsConsistentlyOrdered.spectralRadius_sor_eq`: Young's formula
  $\rho(G_\omega) = Y(\omega, \rho(B))$ for real Jacobi eigenvalues and $\omega > 0$.
* `Matrix.IsConsistentlyOrdered.isMinOn_complexSpectralRadius_sor`: $\omega_{\mathrm{opt}}$
  minimizes $\rho(G_\omega)$ over $0 < \omega < 2$.
* `Matrix.IsConsistentlyOrdered.spectralRadius_sor_lt_one` and
  `Matrix.IsConsistentlyOrdered.spectralRadius_jacobi_lt_one_of_sor`: for $0 < \omega < 2$, SOR
  converges if and only if Jacobi converges.

## Proof outline

The eigenvalue relation comes from the identity
$$\lambda I - G_\omega = (D - \omega E)^{-1} D \bigl((\lambda + \omega - 1) I - \omega (\lambda L +
  U)\bigr)$$
together with $\lambda L + U = \alpha (\alpha L + \alpha^{-1} U)$ for a square root $\alpha$ of
$\lambda$. This turns the matrix on the right into a resolvent of $C(\alpha)$, whose spectrum is
that of $B$.

## Implementation notes

* All matrices are complex, where square roots exist. Real matrices enter through
  `Matrix.complexify`.
* The definition of consistent ordering is the spectral property of [kress1998numerical], which is
  the property that the proofs use. The combinatorial definition of [saad2003iterative], a labelling
  of the indices that changes by $1$ along every nonzero off-diagonal entry, implies it.
* Spectral radii are `spectralRadius ℂ`, extended nonnegative reals. Young's formula compares them
  with real numbers through `ENNReal.ofReal`.
* `Real.sqrt` of a negative number is $0$. So Young's radius is defined as the single formula
  $\max((t + \sqrt d)^2, \omega - 1)$, which covers both cases.
-/

namespace Matrix

open Stationary

open scoped NNReal ENNReal

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]

section Parts

variable {𝕜 : Type*} [Field 𝕜]

/-- For a square matrix $A = D - E - F$, where $D$ is the diagonal of $A$ and $-E$ and $-F$ are its
strictly lower and strictly upper triangular parts, the **strictly lower part of the Jacobi
iteration matrix** is $L = D^{-1} E$.

The inverse is Mathlib's matrix inverse, so $L = 0$ when $D$ is singular. -/
noncomputable def jacobiLower (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  -(diagPart A)⁻¹ * strictLower A

/-- For a square matrix $A = D - E - F$, where $D$ is the diagonal of $A$ and $-E$ and $-F$ are its
strictly lower and strictly upper triangular parts, the **strictly upper part of the Jacobi
iteration matrix** is $U = D^{-1} F$.

The inverse is Mathlib's matrix inverse, so $U = 0$ when $D$ is singular. -/
noncomputable def jacobiUpper (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  -(diagPart A)⁻¹ * strictUpper A

/-- If the diagonal $D$ of $A$ is invertible, the Jacobi iteration matrix is $B = L + U$. -/
theorem jacobiLower_add_jacobiUpper (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) :
    jacobiLower A + jacobiUpper A = (jacobiSplitting A h).iterationOperator := by
  rw [jacobiSplitting_iterationOperator, jacobiLower, jacobiUpper, ← mul_add]

/-- If the diagonal of $A$ is invertible, the entries of $L$ are $L_{ij} = -a_{ij} / a_{ii}$ for
$j < i$ and $L_{ij} = 0$ otherwise. -/
theorem jacobiLower_apply {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) (i j : n) :
    jacobiLower A i j = -((A i i)⁻¹ * strictLower A i j) := by
  rw [jacobiLower, inv_diagPart h, neg_mul, Matrix.neg_apply, diagonal_mul]

/-- If the diagonal of $A$ is invertible, the entries of $U$ are $U_{ij} = -a_{ij} / a_{ii}$ for
$i < j$ and $U_{ij} = 0$ otherwise. -/
theorem jacobiUpper_apply {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) (i j : n) :
    jacobiUpper A i j = -((A i i)⁻¹ * strictUpper A i j) := by
  rw [jacobiUpper, inv_diagPart h, neg_mul, Matrix.neg_apply, diagonal_mul]

/-- If the diagonal of $A$ is invertible, then $L_{ij} = 0$ unless $j < i$. -/
theorem jacobiLower_eq_zero {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) {i j : n}
    (hji : ¬ j < i) : jacobiLower A i j = 0 := by simp [jacobiLower_apply h, hji]

/-- If the diagonal of $A$ is invertible, then $U_{ij} = 0$ unless $i < j$. -/
theorem jacobiUpper_eq_zero {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) {i j : n}
    (hij : ¬ i < j) : jacobiUpper A i j = 0 := by simp [jacobiUpper_apply h, hij]

/-- If the diagonal $D$ of $A$ is invertible, then $DL = E$, the negative of the strictly lower
triangular part of $A$. -/
theorem diagPart_mul_jacobiLower {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    diagPart A * jacobiLower A = -strictLower A := by
  rw [jacobiLower, neg_mul, mul_neg, ← mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp h), one_mul]

/-- If the diagonal $D$ of $A$ is invertible, then $DU = F$, the negative of the strictly upper
triangular part of $A$. -/
theorem diagPart_mul_jacobiUpper {A : Matrix n n 𝕜} (h : IsUnit (diagPart A)) :
    diagPart A * jacobiUpper A = -strictUpper A := by
  rw [jacobiUpper, neg_mul, mul_neg, ← mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp h), one_mul]

/-- The **SOR iteration matrix** of a square matrix $A$ with relaxation parameter $\omega$ is
$$G_\omega = (D - \omega E)^{-1} \bigl(\omega F + (1 - \omega) D\bigr).$$
It is defined for every $\omega$, so that it can be compared across values of $\omega$.

For an invertible diagonal and $\omega \neq 0$, it is the iteration operator of
`Matrix.sorSplitting` (`Matrix.sorSplitting_iterationOperator_eq`). The SOR splitting is not
defined at $\omega = 0$. The inverse is Mathlib's matrix inverse, which is $0$ at a singular
matrix. -/
noncomputable def sorIterationMatrix (A : Matrix n n 𝕜) (ω : 𝕜) : Matrix n n 𝕜 :=
  (diagPart A + ω • strictLower A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A)

/-- If the diagonal of $A$ is invertible and $\omega \neq 0$, the iteration operator of the SOR
splitting of $A$ is the SOR iteration matrix $G_\omega$. -/
theorem sorSplitting_iterationOperator_eq (A : Matrix n n 𝕜) (h : IsUnit (diagPart A)) {ω : 𝕜}
    (hω : ω ≠ 0) : (sorSplitting A h hω).iterationOperator = sorIterationMatrix A ω :=
  sorSplitting_iterationOperator A h hω

/-- Let $A$ be a real square matrix and let $\omega \in \mathbb{R}$. Then the SOR iteration matrix
of the complexification of $A$ is the complexification of $G_\omega$. This holds for every
$\omega$; for $\omega \neq 0$ it is also `Matrix.complexify_sor_iterationOperator`. -/
theorem complexify_sorIterationMatrix (A : Matrix n n ℝ) (ω : ℝ) :
    complexify (sorIterationMatrix A ω) = sorIterationMatrix (complexify A) ω := by
  rw [sorIterationMatrix, sorIterationMatrix, complexify_mul, complexify_inv, complexify_add,
    complexify_smul, complexify_sub, complexify_smul, complexify_smul, complexify_diagPart,
    complexify_strictLower, complexify_strictUpper, Complex.ofReal_sub, Complex.ofReal_one]

end Parts

section Def

/-- A complex square matrix $A$ is **consistently ordered** if for every $\alpha \neq 0$ the matrix
$$C(\alpha) = \alpha L + \alpha^{-1} U$$
has the same spectrum as $C(1) = L + U$. Here $L$ and $U$ are the strictly lower and strictly
upper parts `Matrix.jacobiLower` and `Matrix.jacobiUpper` of the Jacobi iteration matrix
$B = L + U$. This is the definition of [kress1998numerical].

Young's theory uses this property. The combinatorial condition of [saad2003iterative] implies it
(`Matrix.isConsistentlyOrdered_of_labelling`), and so does tridiagonality
(`Matrix.IsTridiagonal.isConsistentlyOrdered`). -/
def IsConsistentlyOrdered (A : Matrix n n ℂ) : Prop :=
  ∀ α : ℂ, α ≠ 0 →
    spectrum ℂ (α • jacobiLower A + α⁻¹ • jacobiUpper A) =
      spectrum ℂ (jacobiLower A + jacobiUpper A)

/-- Let $A$ be a complex square matrix. If for every $\alpha \neq 0$ there is an invertible matrix
$S$ with $C(\alpha) = S \, C(1) \, S^{-1}$, then $A$ is consistently ordered. -/
theorem isConsistentlyOrdered_of_conj {A : Matrix n n ℂ}
    (h : ∀ α : ℂ, α ≠ 0 → ∃ u : (Matrix n n ℂ)ˣ,
      α • jacobiLower A + α⁻¹ • jacobiUpper A =
        (u : Matrix n n ℂ) * (jacobiLower A + jacobiUpper A) *
          ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)) :
    A.IsConsistentlyOrdered := fun α hα => by
  obtain ⟨u, hu⟩ := h α hα
  rw [hu, spectrum.units_conjugate]

/-- The diagonal matrix of a family of nonzero complex numbers, as an invertible matrix. -/
private noncomputable def diagonalUnits (d : n → ℂ) (hd : ∀ i, d i ≠ 0) : (Matrix n n ℂ)ˣ where
  val := diagonal d
  inv := diagonal fun i => (d i)⁻¹
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun i => mul_inv_cancel₀ (hd i))
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg _ (funext fun i => inv_mul_cancel₀ (hd i))

/-- Let $A$ be a complex square matrix with invertible diagonal, and let $c$ assign a natural number
$c_i$ to each index $i$. Assume that $c_i = c_j + 1$ whenever $j < i$ and $a_{ij} \neq 0$, and
that $c_j = c_i + 1$ whenever $i < j$ and $a_{ij} \neq 0$. Then $A$ is consistently ordered. So
the combinatorial definition of [saad2003iterative] implies the definition of
[kress1998numerical].

The similarity between $C(\alpha)$ and $C(1)$ is the diagonal matrix
$\operatorname{diag}(\alpha^{c_i})$. -/
theorem isConsistentlyOrdered_of_labelling {A : Matrix n n ℂ} (h : IsUnit (diagPart A))
    (c : n → ℕ) (hlow : ∀ i j, j < i → A i j ≠ 0 → c i = c j + 1)
    (hupp : ∀ i j, i < j → A i j ≠ 0 → c j = c i + 1) :
    A.IsConsistentlyOrdered := by
  refine isConsistentlyOrdered_of_conj fun α hα => ?_
  obtain ⟨u, hval, hinv⟩ : ∃ u : (Matrix n n ℂ)ˣ,
      (u : Matrix n n ℂ) = diagonal (fun i => α ^ c i) ∧
        ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = diagonal fun i => (α ^ c i)⁻¹ :=
    ⟨diagonalUnits _ fun i => pow_ne_zero (c i) hα, rfl, rfl⟩
  refine ⟨u, ?_⟩
  rw [hval, hinv, mul_assoc]
  ext i j
  rw [diagonal_mul, mul_diagonal, Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [jacobiLower_eq_zero h (asymm hij)]
    rcases eq_or_ne (A i j) 0 with hA | hA
    · rw [jacobiUpper_apply h, strictUpper_apply, ite_eq_left hij, hA]; ring
    · rw [hupp i j hij hA, pow_succ]
      have hpow : α ^ c i ≠ 0 := pow_ne_zero _ hα
      field_simp
      ring
  · rw [jacobiLower_eq_zero h (lt_irrefl i), jacobiUpper_eq_zero h (lt_irrefl i)]
    ring
  · rw [jacobiUpper_eq_zero h (asymm hij)]
    rcases eq_or_ne (A i j) 0 with hA | hA
    · rw [jacobiLower_apply h, strictLower_apply, ite_eq_left hij, hA]; ring
    · rw [hlow i j hij hA, pow_succ]
      have hpow : α ^ c j ≠ 0 := pow_ne_zero _ hα
      field_simp
      ring

omit [DecidableEq n] in
/-- The number of indices strictly below $i$. -/
private def indexRank (i : n) : ℕ := (Finset.univ.filter (· < i)).card

omit [DecidableEq n] in
/-- If $j < i$ and no index lies strictly between $j$ and $i$, then the number of indices below $i$
is one more than the number of indices below $j$. -/
private theorem indexRank_eq_succ {i j : n} (hji : j < i) (hcov : ¬ ∃ k, j < k ∧ k < i) :
    indexRank i = indexRank j + 1 := by
  have hset : Finset.univ.filter (· < i) = insert j (Finset.univ.filter (· < j)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      rcases lt_trichotomy k j with hlt | rfl | hgt
      · exact Or.inr hlt
      · exact Or.inl rfl
      · exact absurd ⟨k, hgt, hk⟩ hcov
    · rintro (rfl | hlt)
      · exact hji
      · exact hlt.trans hji
  rw [indexRank, indexRank, hset, Finset.card_insert_of_notMem (by simp)]

/-- A complex tridiagonal matrix with invertible diagonal is consistently ordered.

The number of indices below $i$ is a labelling as in
`Matrix.isConsistentlyOrdered_of_labelling`, because a nonzero off-diagonal entry of a
tridiagonal matrix joins two neighbouring indices. -/
theorem IsTridiagonal.isConsistentlyOrdered {A : Matrix n n ℂ} (h : IsUnit (diagPart A))
    (hA : A.IsTridiagonal) : A.IsConsistentlyOrdered := by
  refine isConsistentlyOrdered_of_labelling h indexRank (fun i j hji hA' => ?_)
    fun i j hij hA' => ?_
  · exact indexRank_eq_succ hji fun hk => hA' (hA i j (Or.inl hk))
  · exact indexRank_eq_succ hij fun hk => hA' (hA i j (Or.inr hk))

end Def

section Blocks

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

/-- The block sign matrix $\operatorname{diag}(I, -I)$, as an invertible matrix; conjugation by it
turns a block anti-diagonal matrix into its negative. -/
private def blockSignUnits : (Matrix (p ⊕ q) (p ⊕ q) ℂ)ˣ where
  val := fromBlocks 1 0 0 (-1)
  inv := fromBlocks 1 0 0 (-1)
  val_inv := by rw [fromBlocks_multiply]; simp [← fromBlocks_one]
  inv_val := by rw [fromBlocks_multiply]; simp [← fromBlocks_one]

/-- Let $B_{12} \in \mathbb{C}^{p \times q}$ and $B_{21} \in \mathbb{C}^{q \times p}$. If $\mu$ is
in the spectrum of the block anti-diagonal matrix
$$\begin{bmatrix} 0 & B_{12} \\ B_{21} & 0 \end{bmatrix},$$
then so is $-\mu$. This is Proposition 4.12 of [saad2003iterative]: the spectrum of a block
anti-diagonal matrix is symmetric about the origin.

Conjugation by $\operatorname{diag}(I, -I)$ turns the matrix into its negative. -/
theorem neg_mem_spectrum_fromBlocks_zero_zero (B₁₂ : Matrix p q ℂ) (B₂₁ : Matrix q p ℂ) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (fromBlocks 0 B₁₂ B₂₁ 0)) :
    -μ ∈ spectrum ℂ (fromBlocks 0 B₁₂ B₂₁ 0) := by
  obtain ⟨u, hval, hinv⟩ : ∃ u : (Matrix (p ⊕ q) (p ⊕ q) ℂ)ˣ,
      (u : Matrix (p ⊕ q) (p ⊕ q) ℂ) = fromBlocks 1 0 0 (-1) ∧
        ((u⁻¹ : (Matrix (p ⊕ q) (p ⊕ q) ℂ)ˣ) : Matrix (p ⊕ q) (p ⊕ q) ℂ) =
          fromBlocks 1 0 0 (-1) :=
    ⟨blockSignUnits, rfl, rfl⟩
  have hconj : (u : Matrix (p ⊕ q) (p ⊕ q) ℂ) * fromBlocks 0 B₁₂ B₂₁ 0 *
      ((u⁻¹ : (Matrix (p ⊕ q) (p ⊕ q) ℂ)ˣ) : Matrix (p ⊕ q) (p ⊕ q) ℂ) =
      -fromBlocks 0 B₁₂ B₂₁ 0 := by
    rw [hval, hinv, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg]
    simp
  have hspec : spectrum ℂ (-fromBlocks 0 B₁₂ B₂₁ (0 : Matrix q q ℂ)) =
      spectrum ℂ (fromBlocks 0 B₁₂ B₂₁ 0) := by
    rw [← hconj, spectrum.units_conjugate]
  rw [← Set.mem_neg, spectrum.neg_eq, hspec]
  exact hμ

end Blocks

section SOR

/-- Let $A$ be a complex square matrix with invertible diagonal $D$, let $\omega \neq 0$ and let
$\lambda \in \mathbb{C}$. Then the SOR iteration matrix $G_\omega$ satisfies
$$\lambda I - G_\omega = (D - \omega E)^{-1} D \bigl((\lambda + \omega - 1) I - \omega (\lambda
  L + U)\bigr).$$
In the matrix on the right, $\lambda$ multiplies only $L$. -/
theorem smul_one_sub_sor_iterationOperator (A : Matrix n n ℂ) (h : IsUnit (diagPart A)) {ω : ℂ}
    (hω : ω ≠ 0) (l : ℂ) :
    l • (1 : Matrix n n ℂ) - (sorSplitting A h hω).iterationOperator =
      (diagPart A + ω • strictLower A)⁻¹ * diagPart A *
        ((l + ω - 1) • (1 : Matrix n n ℂ) - ω • (l • jacobiLower A + jacobiUpper A)) := by
  have hM := isUnit_diagPart_add_smul_strictLower h ω
  have hMinv : (diagPart A + ω • strictLower A)⁻¹ * (diagPart A + ω • strictLower A) = 1 :=
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hM)
  have hinner : diagPart A *
      ((l + ω - 1) • (1 : Matrix n n ℂ) - ω • (l • jacobiLower A + jacobiUpper A)) =
      l • (diagPart A + ω • strictLower A) - ((1 - ω) • diagPart A - ω • strictUpper A) := by
    rw [mul_sub, mul_smul_comm, mul_one, mul_smul_comm, mul_add, mul_smul_comm,
      diagPart_mul_jacobiLower h, diagPart_mul_jacobiUpper h]
    module
  have hexpand : (diagPart A + ω • strictLower A)⁻¹ *
      (l • (diagPart A + ω • strictLower A) - ((1 - ω) • diagPart A - ω • strictUpper A)) =
      l • (1 : Matrix n n ℂ) -
        (diagPart A + ω • strictLower A)⁻¹ * ((1 - ω) • diagPart A - ω • strictUpper A) := by
    rw [mul_sub, mul_smul_comm, hMinv]
  rw [sorSplitting_iterationOperator, mul_assoc, hinner, hexpand]

/-- Let $A$ be a complex square matrix with invertible diagonal and let $\omega \neq 0$. Then
$\lambda$ is an eigenvalue of the SOR iteration matrix $G_\omega$ if and only if the matrix
$(\lambda + \omega - 1) I - \omega (\lambda L + U)$ is singular. -/
theorem mem_spectrum_sor_iff (A : Matrix n n ℂ) (h : IsUnit (diagPart A)) {ω : ℂ} (hω : ω ≠ 0)
    (l : ℂ) :
    l ∈ spectrum ℂ (sorSplitting A h hω).iterationOperator ↔
      ¬ IsUnit ((l + ω - 1) • (1 : Matrix n n ℂ) -
        ω • (l • jacobiLower A + jacobiUpper A)) := by
  have hM := isUnit_diagPart_add_smul_strictLower h ω
  have hMinv : IsUnit ((diagPart A + ω • strictLower A)⁻¹) := by
    rw [isUnit_iff_isUnit_det, det_nonsing_inv]
    exact ((isUnit_iff_isUnit_det _).mp hM).ringInverse
  have hu : IsUnit ((diagPart A + ω • strictLower A)⁻¹ * diagPart A) := hMinv.mul h
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one,
    smul_one_sub_sor_iterationOperator A h hω l, ← hu.unit_spec, Units.isUnit_units_mul]

/-- Let $A$ be a consistently ordered complex matrix with invertible diagonal. Then $-\mu$ is an
eigenvalue of the Jacobi iteration matrix $B$ if and only if $\mu$ is. This is the case
$\alpha = -1$ of consistent ordering. -/
theorem IsConsistentlyOrdered.neg_mem_spectrum_jacobi_iff {A : Matrix n n ℂ}
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A)) {μ : ℂ} :
    -μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator ↔
      μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator := by
  have hneg : ((-1 : ℂ) • jacobiLower A + (-1 : ℂ)⁻¹ • jacobiUpper A) =
      -(jacobiLower A + jacobiUpper A) := by
    rw [inv_neg, inv_one]; module
  have hspec := hA (-1) (by norm_num)
  rw [hneg] at hspec
  rw [← jacobiLower_add_jacobiUpper A h, ← Set.mem_neg, spectrum.neg_eq, hspec]

/-- **Young's eigenvalue relation.** Let $A$ be a consistently ordered complex matrix with
invertible diagonal, let $\omega \neq 0$, and let $\lambda, \mu \in \mathbb{C}$ with
$\lambda \neq 0$ and
$$(\lambda + \omega - 1)^2 = \lambda \omega^2 \mu^2.$$
Then $\mu$ is an eigenvalue of the Jacobi iteration matrix $B$ if and only if $\lambda$ is an
eigenvalue of the SOR iteration matrix $G_\omega$. This is Theorem 4.16 of [saad2003iterative]
and (4.8) of [kress1998numerical].

The proof combines `Matrix.smul_one_sub_sor_iterationOperator` with $\lambda L + U = \alpha
(\alpha L + \alpha^{-1} U)$ for a square root $\alpha$ of $\lambda$. The matrices $B$ and
$G_\omega$ are the iteration operators of `Matrix.jacobiSplitting` and `Matrix.sorSplitting`. -/
theorem IsConsistentlyOrdered.mem_spectrum_jacobi_iff_sor {A : Matrix n n ℂ}
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A)) {ω : ℂ} (hω : ω ≠ 0) {l μ : ℂ}
    (hl : l ≠ 0) (hrel : (l + ω - 1) ^ 2 = l * ω ^ 2 * μ ^ 2) :
    μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator ↔
      l ∈ spectrum ℂ (sorSplitting A h hω).iterationOperator := by
  obtain ⟨α, hα2⟩ := IsAlgClosed.exists_pow_nat_eq l (n := 2) (by norm_num)
  have hα : α ≠ 0 := by
    rintro rfl
    exact hl (by simpa using hα2.symm)
  have hωα : ω * α ≠ 0 := mul_ne_zero hω hα
  set ν : ℂ := (l + ω - 1) / (ω * α) with hν
  have e1 : ω * α * ν = l + ω - 1 := by rw [hν]; field_simp
  have e2 : ω * α * α = ω * l := by rw [mul_assoc, ← sq, hα2]
  have e3 : ω * α * α⁻¹ = ω := by field_simp
  have hmat : (l + ω - 1) • (1 : Matrix n n ℂ) - ω • (l • jacobiLower A + jacobiUpper A) =
      (ω * α) • (ν • (1 : Matrix n n ℂ) - (α • jacobiLower A + α⁻¹ • jacobiUpper A)) := by
    have hl' : (l + ω - 1) • (1 : Matrix n n ℂ) - ω • (l • jacobiLower A + jacobiUpper A) =
        (l + ω - 1) • (1 : Matrix n n ℂ) - (ω * l) • jacobiLower A - ω • jacobiUpper A := by
      module
    have hr' : (ω * α) • (ν • (1 : Matrix n n ℂ) - (α • jacobiLower A + α⁻¹ • jacobiUpper A)) =
        (ω * α * ν) • (1 : Matrix n n ℂ) - (ω * α * α) • jacobiLower A -
          (ω * α * α⁻¹) • jacobiUpper A := by
      module
    rw [hl', hr', e1, e2, e3]
  have hkey : l ∈ spectrum ℂ (sorSplitting A h hω).iterationOperator ↔
      ν ∈ spectrum ℂ (α • jacobiLower A + α⁻¹ • jacobiUpper A) := by
    rw [mem_spectrum_sor_iff A h hω l, hmat, ← Units.smul_mk0 hωα, isUnit_smul_iff,
      spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  rw [hkey, hA α hα, jacobiLower_add_jacobiUpper A h]
  have hν2 : ν ^ 2 = μ ^ 2 := by
    rw [hν, div_pow, mul_pow, hα2, hrel]
    field_simp
  have hsq : (ν - μ) * (ν + μ) = 0 := by linear_combination hν2
  rcases mul_eq_zero.mp hsq with hz | hz
  · rw [sub_eq_zero] at hz; rw [hz]
  · rw [eq_neg_of_add_eq_zero_left hz, hA.neg_mem_spectrum_jacobi_iff h]

/-- Let $A$ be a consistently ordered complex matrix with invertible diagonal. Then the spectral
radius of the Gauss–Seidel iteration matrix is the square of the spectral radius of the Jacobi
iteration matrix:
$$\rho(G_1) = \rho(B)^2.$$
So Gauss–Seidel converges twice as fast as Jacobi. This is Corollary 4.16 of
[kress1998numerical].

It is the case $\omega = 1$ of `Matrix.IsConsistentlyOrdered.mem_spectrum_jacobi_iff_sor`, where
the eigenvalue relation reads $\lambda = \mu^2$. -/
theorem IsConsistentlyOrdered.spectralRadius_gaussSeidel_eq_sq {A : Matrix n n ℂ}
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A)) :
    spectralRadius ℂ (gaussSeidelSplitting A h).iterationOperator =
      spectralRadius ℂ (jacobiSplitting A h).iterationOperator ^ 2 := by
  have hgs : gaussSeidelSplitting A h = sorSplitting A h (one_ne_zero (α := ℂ)) :=
    (sorSplitting_one A h).symm
  have hB2 : spectralRadius ℂ (jacobiSplitting A h).iterationOperator ^ 2 =
      ⨆ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, ((‖μ‖₊ : ℝ≥0∞) ^ 2) := by
    rw [spectralRadius_eq_of_unital]
    exact ENNReal.iSup₂_pow_of_ne_zero _ two_ne_zero
  rw [spectralRadius_eq_of_unital, hB2]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun l hl => ?_
    rcases eq_or_ne l 0 with rfl | hl0
    · simp
    · obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq l (n := 2) (by norm_num)
      have hmem : μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator := by
        rw [hA.mem_spectrum_jacobi_iff_sor h one_ne_zero hl0 (by rw [hμ]; ring), ← hgs]
        exact hl
      refine le_iSup₂_of_le μ hmem ?_
      rw [← hμ]
      simp
  · refine iSup₂_le fun μ hμ => ?_
    rcases eq_or_ne μ 0 with rfl | hμ0
    · simp
    · have hl0 : μ ^ 2 ≠ 0 := pow_ne_zero _ hμ0
      have hmem : μ ^ 2 ∈ spectrum ℂ (gaussSeidelSplitting A h).iterationOperator := by
        rw [hgs, ← hA.mem_spectrum_jacobi_iff_sor h one_ne_zero hl0 (by ring)]
        exact hμ
      refine le_iSup₂_of_le (μ ^ 2) hmem ?_
      simp

end SOR

section Young

/-- **Young's radius.** For real numbers $\omega$ and $r$, put $t = \omega r / 2$ and
$d = t^2 - (\omega - 1)$. Then Young's radius is
$$Y(\omega, r) = \max\bigl((t + \sqrt d)^2, \, \omega - 1\bigr),$$
where $\sqrt d = 0$ for $d < 0$. It is the modulus of the dominant root $\lambda$ of Young's
quadratic $(\lambda + \omega - 1)^2 = \lambda \omega^2 \mu^2$ for $|\mu| = r$.

If $d \ge 0$, the two roots are $(t \pm \sqrt d)^2$. If $d < 0$, they are a conjugate pair of
modulus $\omega - 1$. Because `Real.sqrt` of a negative number is $0$, the maximum is
$(t + \sqrt d)^2$ in the first case (for $\omega r \ge 0$) and $\omega - 1$ in the second case
(`Matrix.youngRadius_of_le`, `Matrix.youngRadius_of_lt`). -/
noncomputable def youngRadius (ω r : ℝ) : ℝ :=
  max ((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2) (ω - 1)

/-- If $\omega r \ge 0$ and $\omega - 1 \le (\omega r / 2)^2$, then
$$Y(\omega, r) = \Bigl(\frac{\omega r}{2} + \sqrt{(\omega r / 2)^2 - (\omega - 1)}\Bigr)^2.$$
In this case the roots of Young's quadratic are real, and this is the larger one. -/
theorem youngRadius_of_le {ω r : ℝ} (ht : 0 ≤ ω * r) (h : ω - 1 ≤ (ω * r / 2) ^ 2) :
    youngRadius ω r = (ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 := by
  refine max_eq_left ?_
  nlinarith [Real.sqrt_nonneg ((ω * r / 2) ^ 2 - (ω - 1)), ht]

/-- If $(\omega r / 2)^2 < \omega - 1$, then $Y(\omega, r) = \omega - 1$. In this case the two roots
of Young's quadratic are a conjugate pair of modulus $\omega - 1$. -/
theorem youngRadius_of_lt {ω r : ℝ} (h : (ω * r / 2) ^ 2 < ω - 1) : youngRadius ω r = ω - 1 := by
  rw [youngRadius, Real.sqrt_eq_zero_of_nonpos (by linarith), add_zero]
  exact max_eq_right h.le

/-- Young's radius is nonnegative: $Y(\omega, r) \ge 0$. -/
theorem youngRadius_nonneg {ω r : ℝ} : 0 ≤ youngRadius ω r :=
  le_max_of_le_left (sq_nonneg _)

/-- Let $\omega \ge 0$ and $0 \le r_1 \le r_2$. Then $Y(\omega, r_1) \le Y(\omega, r_2)$: a Jacobi
eigenvalue of larger modulus gives a larger SOR eigenvalue. -/
theorem youngRadius_mono {ω : ℝ} (hω : 0 ≤ ω) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (h : r₁ ≤ r₂) :
    youngRadius ω r₁ ≤ youngRadius ω r₂ := by
  refine max_le_max ?_ le_rfl
  have h1 : 0 ≤ ω * r₁ / 2 := by positivity
  have h2 : ω * r₁ / 2 ≤ ω * r₂ / 2 := by
    have := mul_le_mul_of_nonneg_left h hω
    linarith
  have hsq : (ω * r₁ / 2) ^ 2 - (ω - 1) ≤ (ω * r₂ / 2) ^ 2 - (ω - 1) := by nlinarith
  have hsqrt := Real.sqrt_le_sqrt hsq
  nlinarith [Real.sqrt_nonneg ((ω * r₁ / 2) ^ 2 - (ω - 1)),
    Real.sqrt_nonneg ((ω * r₂ / 2) ^ 2 - (ω - 1))]

/-- Let $0 < \omega < 2$ and $r \ge 1$. Then $Y(\omega, r) \ge 1$.

With $t = \omega r / 2 \ge \omega / 2$, the discriminant $t^2 - (\omega - 1)$ is at least
$(\omega/2 - 1)^2$, so $t + \sqrt{t^2 - (\omega - 1)} \ge \omega/2 + (1 - \omega/2) = 1$. This
makes Jacobi convergence necessary for SOR convergence on a consistently ordered matrix
(`Matrix.IsConsistentlyOrdered.spectralRadius_jacobi_lt_one_of_sor`). -/
theorem one_le_youngRadius {ω r : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) (hr : 1 ≤ r) :
    1 ≤ youngRadius ω r := by
  have ht : ω / 2 ≤ ω * r / 2 := by nlinarith
  have hd : (ω / 2 - 1) ^ 2 ≤ (ω * r / 2) ^ 2 - (ω - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 ht) (by positivity : (0 : ℝ) ≤ ω * r / 2 + ω / 2)]
  have hd0 : ω - 1 ≤ (ω * r / 2) ^ 2 := by nlinarith [sq_nonneg (ω / 2 - 1)]
  rw [youngRadius_of_le (by positivity) hd0]
  have hsqrt : 1 - ω / 2 ≤ Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1)) := by
    calc 1 - ω / 2 = |ω / 2 - 1| := by rw [abs_of_neg (by linarith)]; ring
      _ = Real.sqrt ((ω / 2 - 1) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt hd
  nlinarith [Real.sqrt_nonneg ((ω * r / 2) ^ 2 - (ω - 1))]

/-- If $t \ge 0$ and $(\lambda + \omega - 1)^2 = \lambda (2t)^2$, then $|\lambda| \le \max((t +
\sqrt{t^2 - (\omega - 1)})^2, \omega - 1)$. -/
private theorem norm_le_young_aux {ω t : ℝ} (ht : 0 ≤ t) {l : ℂ}
    (hrel : (l + (ω : ℂ) - 1) ^ 2 = l * (2 * (t : ℂ)) ^ 2) :
    ‖l‖ ≤ max ((t + Real.sqrt (t ^ 2 - (ω - 1))) ^ 2) (ω - 1) := by
  obtain ⟨z₀, hz₀⟩ := IsAlgClosed.exists_pow_nat_eq l (n := 2) (by norm_num)
  obtain ⟨z, hz2, hzrel⟩ : ∃ z : ℂ, z ^ 2 = l ∧ l + (ω : ℂ) - 1 = 2 * t * z := by
    have hfac : (l + (ω : ℂ) - 1 - 2 * t * z₀) * (l + (ω : ℂ) - 1 + 2 * t * z₀) = 0 := by
      linear_combination hrel - 4 * (t : ℂ) ^ 2 * hz₀
    rcases mul_eq_zero.mp hfac with hc | hc
    · exact ⟨z₀, hz₀, by linear_combination hc⟩
    · exact ⟨-z₀, by linear_combination hz₀, by linear_combination hc⟩
  have hw2 : (z - (t : ℂ)) ^ 2 = ((t ^ 2 - (ω - 1) : ℝ) : ℂ) := by
    push_cast
    linear_combination hz2 + hzrel
  have hwnorm : ‖z - (t : ℂ)‖ ^ 2 = |t ^ 2 - (ω - 1)| := by
    rw [← norm_pow, hw2, Complex.norm_real, Real.norm_eq_abs]
  have hwre : (z - (t : ℂ)).re ^ 2 - (z - (t : ℂ)).im ^ 2 = t ^ 2 - (ω - 1) := by
    have hre := congrArg Complex.re hw2
    simpa [pow_two, Complex.mul_re] using hre
  have hwim : (z - (t : ℂ)).re * (z - (t : ℂ)).im = 0 := by
    have him := congrArg Complex.im hw2
    simp only [pow_two, Complex.mul_im, Complex.ofReal_im] at him
    linarith
  have hsum : (z - (t : ℂ)).re ^ 2 + (z - (t : ℂ)).im ^ 2 = |t ^ 2 - (ω - 1)| := by
    rw [← hwnorm, Complex.sq_norm, Complex.normSq_apply]; ring
  have hznorm : ‖z‖ ^ 2 = t ^ 2 + 2 * t * (z - (t : ℂ)).re + |t ^ 2 - (ω - 1)| := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] at hsum ⊢
    nlinarith [hsum]
  have hlz : ‖l‖ = ‖z‖ ^ 2 := by rw [← hz2, norm_pow]
  rcases le_or_gt 0 (t ^ 2 - (ω - 1)) with hdpos | hdneg
  · refine le_trans (le_of_eq hlz) (le_max_of_le_left ?_)
    have habs : |t ^ 2 - (ω - 1)| = t ^ 2 - (ω - 1) := abs_of_nonneg hdpos
    have hsq := Real.sq_sqrt hdpos
    have hrele : (z - (t : ℂ)).re ≤ Real.sqrt (t ^ 2 - (ω - 1)) := by
      nlinarith [Real.sqrt_nonneg (t ^ 2 - (ω - 1)),
        sq_nonneg ((z - (t : ℂ)).re - Real.sqrt (t ^ 2 - (ω - 1))),
        sq_nonneg ((z - (t : ℂ)).re + Real.sqrt (t ^ 2 - (ω - 1)))]
    rw [hznorm, habs]
    nlinarith [Real.sqrt_nonneg (t ^ 2 - (ω - 1))]
  · refine le_trans (le_of_eq hlz) (le_max_of_le_right ?_)
    have hre0 : (z - (t : ℂ)).re = 0 := by
      rcases mul_eq_zero.mp hwim with hc | hc
      · exact hc
      · nlinarith [sq_nonneg (z - (t : ℂ)).re]
    rw [hznorm, hre0, abs_of_neg hdneg]
    linarith

/-- The square of a complex number with zero imaginary part is the square of its modulus. -/
private theorem sq_eq_sq_norm_of_im_eq_zero {μ : ℂ} (h : μ.im = 0) :
    μ ^ 2 = ((‖μ‖ : ℝ) : ℂ) ^ 2 := by
  have hre : μ = ((μ.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h]
  have hnorm : ‖μ‖ = |μ.re| := by
    conv_lhs => rw [hre]
    rw [Complex.norm_real, Real.norm_eq_abs]
  conv_lhs => rw [hre]
  rw [hnorm, ← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]

/-- Let $\omega \ge 0$, let $\mu$ be a complex number with zero imaginary part and $|\mu| \le r$,
and let $\lambda \in \mathbb{C}$ satisfy $(\lambda + \omega - 1)^2 = \lambda \omega^2 \mu^2$.
Then $|\lambda| \le Y(\omega, r)$. -/
theorem norm_le_youngRadius {ω r : ℝ} (hω : 0 ≤ ω) {l μ : ℂ} (hμim : μ.im = 0) (hμ : ‖μ‖ ≤ r)
    (hrel : (l + (ω : ℂ) - 1) ^ 2 = l * (ω : ℂ) ^ 2 * μ ^ 2) :
    ‖l‖ ≤ youngRadius ω r := by
  have hμsq : μ ^ 2 = ((‖μ‖ : ℝ) : ℂ) ^ 2 := sq_eq_sq_norm_of_im_eq_zero hμim
  have ht : 0 ≤ ω * ‖μ‖ / 2 := by positivity
  have hrel' : (l + (ω : ℂ) - 1) ^ 2 = l * (2 * ((ω * ‖μ‖ / 2 : ℝ) : ℂ)) ^ 2 := by
    rw [hrel, hμsq]
    push_cast
    ring
  refine le_trans (norm_le_young_aux ht hrel') ?_
  have hmono := youngRadius_mono hω (norm_nonneg μ) hμ
  rw [youngRadius] at hmono
  exact hmono

/-- **Young's radius is attained.** For all $\omega \ge 0$ and $r \ge 0$, there is a root
$\lambda \in \mathbb{C}$ of $(\lambda + \omega - 1)^2 = \lambda \omega^2 r^2$ with
$|\lambda| = Y(\omega, r)$. -/
theorem exists_norm_eq_youngRadius {ω r : ℝ} (hω : 0 ≤ ω) (hr : 0 ≤ r) :
    ∃ l : ℂ, (l + (ω : ℂ) - 1) ^ 2 = l * (ω : ℂ) ^ 2 * ((r : ℝ) : ℂ) ^ 2 ∧
      ‖l‖ = youngRadius ω r := by
  have ht : 0 ≤ ω * r := mul_nonneg hω hr
  rcases le_or_gt (ω - 1) ((ω * r / 2) ^ 2) with hcase | hcase
  · have hd : 0 ≤ (ω * r / 2) ^ 2 - (ω - 1) := by linarith
    have hs2 := Real.sq_sqrt hd
    have hE : (ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 + (ω - 1) =
        2 * (ω * r / 2) * (ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) := by
      linear_combination hs2
    have hreal : ((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 + (ω - 1)) ^ 2 =
        (ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 * ω ^ 2 * r ^ 2 := by
      rw [hE]
      ring
    refine ⟨(((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 : ℝ) : ℂ), ?_, ?_⟩
    · calc ((((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 : ℝ) : ℂ) + (ω : ℂ) - 1) ^ 2
          = ((((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 + (ω - 1)) ^ 2 : ℝ) : ℂ) :=
            by push_cast; ring
        _ = (((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 * ω ^ 2 * r ^ 2 : ℝ) : ℂ) :=
            by rw [hreal]
        _ = (((ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1))) ^ 2 : ℝ) : ℂ) * (ω : ℂ) ^ 2 *
              ((r : ℝ) : ℂ) ^ 2 := by push_cast; ring
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        youngRadius_of_le ht hcase]
  · have hd : 0 < (ω - 1) - (ω * r / 2) ^ 2 := by linarith
    have hs2 := Real.sq_sqrt hd.le
    have hsc : ((Real.sqrt ((ω - 1) - (ω * r / 2) ^ 2) : ℝ) : ℂ) ^ 2 =
        (ω : ℂ) - 1 - (((ω * r / 2 : ℝ)) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, hs2]
      push_cast
      ring
    refine ⟨(((ω * r / 2 : ℝ) : ℂ) +
      Complex.I * ((Real.sqrt ((ω - 1) - (ω * r / 2) ^ 2) : ℝ) : ℂ)) ^ 2, ?_, ?_⟩
    · have hE : ((((ω * r / 2 : ℝ)) : ℂ) +
          Complex.I * ((Real.sqrt ((ω - 1) - (ω * r / 2) ^ 2) : ℝ) : ℂ)) ^ 2 + (ω : ℂ) - 1 =
          2 * (((ω * r / 2 : ℝ)) : ℂ) * ((((ω * r / 2 : ℝ)) : ℂ) +
            Complex.I * ((Real.sqrt ((ω - 1) - (ω * r / 2) ^ 2) : ℝ) : ℂ)) := by
        linear_combination ((Real.sqrt ((ω - 1) - (ω * r / 2) ^ 2) : ℝ) : ℂ) ^ 2 * Complex.I_sq -
          hsc
      rw [hE]
      push_cast
      ring
    · rw [norm_pow, Complex.sq_norm, Complex.normSq_apply, youngRadius_of_lt hcase]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, mul_zero,
        zero_add, add_zero, sub_zero]
      linear_combination hs2

/-- For a complex number $z$, the coercion of $\|z\|$ from the nonnegative reals to the extended
nonnegative reals is `ENNReal.ofReal ‖z‖`. -/
private theorem coe_nnnorm_eq_ofReal (z : ℂ) : ((‖z‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

/-- Let $A$ be a consistently ordered complex matrix with invertible diagonal, let $\omega \neq 0$,
and let $\lambda \neq 0$ be an eigenvalue of the SOR iteration matrix $G_\omega$. Then there is
an eigenvalue $\mu$ of the Jacobi iteration matrix $B$ with $(\lambda + \omega - 1)^2 = \lambda
\omega^2 \mu^2$. -/
theorem IsConsistentlyOrdered.exists_mem_spectrum_jacobi {A : Matrix n n ℂ}
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A)) {ω : ℂ} (hω : ω ≠ 0) {l : ℂ}
    (hl : l ≠ 0) (hmem : l ∈ spectrum ℂ (sorSplitting A h hω).iterationOperator) :
    ∃ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator,
      (l + ω - 1) ^ 2 = l * ω ^ 2 * μ ^ 2 := by
  obtain ⟨α, hα2⟩ := IsAlgClosed.exists_pow_nat_eq l (n := 2) (by norm_num)
  have hα : α ≠ 0 := by
    rintro rfl
    exact hl (by simpa using hα2.symm)
  have hrel : (l + ω - 1) ^ 2 = l * ω ^ 2 * ((l + ω - 1) / (ω * α)) ^ 2 := by
    rw [div_pow, mul_pow, ← hα2]
    field_simp
  exact ⟨(l + ω - 1) / (ω * α),
    (hA.mem_spectrum_jacobi_iff_sor h hω hl hrel).mpr hmem, hrel⟩

/-- **Young's formula for the SOR spectral radius.** Let $A$ be a consistently ordered complex
matrix of order $n \ge 1$ with invertible diagonal, such that every eigenvalue of the Jacobi
iteration matrix $B$ is real, and let $\omega > 0$. Then
$$\rho(G_\omega) = Y(\omega, \rho(B)).$$
That is, with $d = (\omega \rho(B) / 2)^2 - (\omega - 1)$, the spectral radius is $\omega - 1$
if $d < 0$ and $(\omega \rho(B) / 2 + \sqrt d)^2$ if $d \ge 0$. This is Theorem 4.15 of
[kress1998numerical] and (4.47) of [saad2003iterative].

The matrix $G_\omega$ is `Matrix.sorIterationMatrix A ω`, and the equation is stated through
`ENNReal.ofReal`. The upper bound applies `Matrix.norm_le_youngRadius` to the Jacobi eigenvalue
that `Matrix.IsConsistentlyOrdered.exists_mem_spectrum_jacobi` attaches to each SOR eigenvalue,
with the monotonicity of Young's radius. The lower bound applies
`Matrix.exists_norm_eq_youngRadius` to a Jacobi eigenvalue of maximal modulus. -/
theorem IsConsistentlyOrdered.spectralRadius_sor_eq {A : Matrix n n ℂ} [Nonempty n]
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, μ.im = 0) {ω : ℝ}
    (hω : 0 < ω) :
    spectralRadius ℂ (sorIterationMatrix A (ω : ℂ)) =
      ENNReal.ofReal (youngRadius ω
        (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal) := by
  rw [← sorSplitting_iterationOperator_eq A h (Complex.ofReal_ne_zero.mpr hω.ne')]
  obtain ⟨μ₀, hμ₀, hρ, hmax⟩ :=
    exists_norm_eq_spectralRadius (jacobiSplitting A h).iterationOperator
      (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ _)
  have htoReal : (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal = ‖μ₀‖ := by
    rw [hρ, ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [htoReal, spectralRadius_eq_of_unital]
  refine le_antisymm (iSup₂_le fun l hl => ?_) ?_
  · rcases eq_or_ne l 0 with rfl | hl0
    · simp
    · obtain ⟨μ, hμmem, hrel⟩ :=
        hA.exists_mem_spectrum_jacobi h (Complex.ofReal_ne_zero.mpr hω.ne') hl0 hl
      rw [coe_nnnorm_eq_ofReal]
      exact ENNReal.ofReal_le_ofReal
        (norm_le_youngRadius hω.le (hreal μ hμmem) (hmax μ hμmem) hrel)
  · obtain ⟨l, hrelr, hnorm⟩ := exists_norm_eq_youngRadius hω.le (norm_nonneg μ₀)
    rcases eq_or_ne l 0 with rfl | hl0
    · rw [← hnorm]
      simp
    · have hrel : (l + (ω : ℂ) - 1) ^ 2 = l * (ω : ℂ) ^ 2 * μ₀ ^ 2 := by
        rw [hrelr, sq_eq_sq_norm_of_im_eq_zero (hreal μ₀ hμ₀)]
      have hmem : l ∈ spectrum ℂ
          (sorSplitting A h (Complex.ofReal_ne_zero.mpr hω.ne')).iterationOperator :=
        (hA.mem_spectrum_jacobi_iff_sor h (Complex.ofReal_ne_zero.mpr hω.ne') hl0 hrel).mp hμ₀
      refine le_iSup₂_of_le l hmem ?_
      rw [coe_nnnorm_eq_ofReal, hnorm]

/-- The **optimal relaxation parameter** for a Jacobi spectral radius $r$ is
$$\omega_{\mathrm{opt}}(r) = \frac{2}{1 + \sqrt{1 - r^2}}.$$
For $0 \le r < 1$, it is the value of $\omega$ at which the discriminant of Young's quadratic
vanishes (`Matrix.sq_optimalRelaxation`).

For $|r| > 1$, `Real.sqrt` of the negative number $1 - r^2$ is $0$, so the value is $2$. -/
noncomputable def optimalRelaxation (r : ℝ) : ℝ := 2 / (1 + Real.sqrt (1 - r ^ 2))

section Optimal

variable {r : ℝ}

/-- For $0 \le r < 1$: $(\sqrt{1 - r^2})^2 = 1 - r^2$, $\sqrt{1 - r^2} > 0$, and
$\sqrt{1 - r^2} \le 1$. -/
private theorem sqrt_one_sub_sq_facts (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 ∧ 0 < Real.sqrt (1 - r ^ 2) ∧
      Real.sqrt (1 - r ^ 2) ≤ 1 := by
  have hpos : 0 < 1 - r ^ 2 := by nlinarith
  have hsq := Real.sq_sqrt hpos.le
  refine ⟨hsq, ?_, ?_⟩
  · exact Real.sqrt_pos.mpr hpos
  · nlinarith [Real.sqrt_nonneg (1 - r ^ 2)]

/-- For $0 \le r < 1$, the optimal relaxation parameter satisfies $\omega_{\mathrm{opt}}(r) \ge 1$.
-/
theorem one_le_optimalRelaxation (hr0 : 0 ≤ r) (hr1 : r < 1) : 1 ≤ optimalRelaxation r := by
  obtain ⟨-, hq0, hq1⟩ := sqrt_one_sub_sq_facts hr0 hr1
  rw [optimalRelaxation, le_div_iff₀ (by linarith)]
  linarith

/-- For $0 \le r < 1$, the optimal relaxation parameter satisfies $\omega_{\mathrm{opt}}(r) < 2$, so
it lies in the interval $(0, 2)$ of Kahan's condition. -/
theorem optimalRelaxation_lt_two (hr0 : 0 ≤ r) (hr1 : r < 1) : optimalRelaxation r < 2 := by
  obtain ⟨-, hq0, -⟩ := sqrt_one_sub_sq_facts hr0 hr1
  rw [optimalRelaxation, div_lt_iff₀ (by linarith)]
  linarith

/-- For $0 \le r < 1$, the discriminant of Young's quadratic vanishes at the optimal parameter:
$$\left(\frac{\omega_{\mathrm{opt}}(r) \, r}{2}\right)^2 = \omega_{\mathrm{opt}}(r) - 1.$$
-/
theorem sq_optimalRelaxation (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (optimalRelaxation r * r / 2) ^ 2 = optimalRelaxation r - 1 := by
  obtain ⟨hq2, hq0, -⟩ := sqrt_one_sub_sq_facts hr0 hr1
  have h1q : (0 : ℝ) < 1 + Real.sqrt (1 - r ^ 2) := by linarith
  have hA : (optimalRelaxation r * r / 2) ^ 2 = r ^ 2 / (1 + Real.sqrt (1 - r ^ 2)) ^ 2 := by
    rw [optimalRelaxation]
    field_simp
  have hB : optimalRelaxation r - 1 =
      (1 - Real.sqrt (1 - r ^ 2)) / (1 + Real.sqrt (1 - r ^ 2)) := by
    rw [optimalRelaxation]
    field_simp
    ring
  rw [hA, hB, div_eq_div_iff (by positivity) h1q.ne']
  linear_combination (1 + Real.sqrt (1 - r ^ 2)) * hq2

/-- For $0 \le r < 1$, Young's radius at the optimal parameter is $Y(\omega_{\mathrm{opt}}(r), r) =
\omega_{\mathrm{opt}}(r) - 1$. -/
theorem youngRadius_optimalRelaxation (hr0 : 0 ≤ r) (hr1 : r < 1) :
    youngRadius (optimalRelaxation r) r = optimalRelaxation r - 1 := by
  have hc1 := one_le_optimalRelaxation hr0 hr1
  have hsq := sq_optimalRelaxation hr0 hr1
  have hnn : 0 ≤ optimalRelaxation r * r := mul_nonneg (by linarith) hr0
  have hzero : (optimalRelaxation r * r / 2) ^ 2 - (optimalRelaxation r - 1) = 0 := by
    rw [hsq]; ring
  rw [youngRadius_of_le hnn (by linarith), hzero, Real.sqrt_zero, add_zero, hsq]

/-- **The optimal relaxation parameter minimizes Young's radius.** For $0 \le r < 1$ and every
$\omega > 0$,
$$Y(\omega_{\mathrm{opt}}(r), r) \le Y(\omega, r).$$

For $\omega \ge \omega_{\mathrm{opt}}$ the radius is $\omega - 1$, which increases with
$\omega$. For $\omega \le \omega_{\mathrm{opt}}$ the discriminant $d$ is nonnegative, and the
dominant root $(\omega r / 2 + \sqrt d)^2$ is at least $(\omega_{\mathrm{opt}} r / 2)^2 =
\omega_{\mathrm{opt}} - 1$, because $\sqrt d \ge \omega_{\mathrm{opt}} r / 2 - \omega r / 2$
reduces to $(2 - \omega_{\mathrm{opt}})(\omega_{\mathrm{opt}} - \omega) \ge 0$. -/
theorem youngRadius_optimalRelaxation_le (hr0 : 0 ≤ r) (hr1 : r < 1) {ω : ℝ}
    (hω0 : 0 < ω) : youngRadius (optimalRelaxation r) r ≤ youngRadius ω r := by
  have hc1 := one_le_optimalRelaxation hr0 hr1
  have hc2 := optimalRelaxation_lt_two hr0 hr1
  have hsq := sq_optimalRelaxation hr0 hr1
  have hr2 : optimalRelaxation r ^ 2 * r ^ 2 = 4 * (optimalRelaxation r - 1) := by
    linear_combination 4 * hsq
  rw [youngRadius_optimalRelaxation hr0 hr1]
  rcases le_or_gt ω (optimalRelaxation r) with hle | hgt
  · -- `ω ≤ ω_opt`: the discriminant is nonnegative
    have hfac : 0 ≤ (optimalRelaxation r - ω) *
        (optimalRelaxation r - (optimalRelaxation r - 1) * ω) :=
      mul_nonneg (by linarith) (by nlinarith)
    have hd : 0 ≤ (ω * r / 2) ^ 2 - (ω - 1) := by nlinarith
    rw [youngRadius_of_le (by positivity) (by linarith)]
    -- the dominant root is at least `(ω_opt r / 2)²`
    have hkey : optimalRelaxation r * r / 2 ≤
        ω * r / 2 + Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1)) := by
      rcases le_or_gt (optimalRelaxation r * r / 2) (ω * r / 2) with h1 | h1
      · linarith [Real.sqrt_nonneg ((ω * r / 2) ^ 2 - (ω - 1))]
      · have hpos : 0 < optimalRelaxation r * r / 2 - ω * r / 2 := by linarith
        have hfac2 : 0 ≤ (2 - optimalRelaxation r) * (optimalRelaxation r - ω) :=
          mul_nonneg (by linarith) (by linarith)
        have hsqle : (optimalRelaxation r * r / 2 - ω * r / 2) ^ 2 ≤
            (ω * r / 2) ^ 2 - (ω - 1) := by nlinarith
        have hmono := Real.sqrt_le_sqrt hsqle
        rw [Real.sqrt_sq hpos.le] at hmono
        linarith
    have hnn : 0 ≤ optimalRelaxation r * r / 2 := by positivity
    nlinarith [hsq]
  · -- `ω ≥ ω_opt`: the radius is at least `ω - 1`
    exact le_trans (by linarith) (le_max_right _ _)

/-- For $0 \le r < 1$ and $0 < \omega < 2$, Young's radius satisfies $Y(\omega, r) < 1$. With
Young's formula, this says that SOR converges for every $0 < \omega < 2$ when the Jacobi
spectral radius is less than $1$. -/
theorem youngRadius_lt_one (hr0 : 0 ≤ r) (hr1 : r < 1) {ω : ℝ} (hω0 : 0 < ω) (hω2 : ω < 2) :
    youngRadius ω r < 1 := by
  rw [youngRadius, max_lt_iff]
  refine ⟨?_, by linarith⟩
  have ht0 : 0 ≤ ω * r / 2 := by positivity
  have ht : ω * r / 2 < 1 := by nlinarith
  have hdlt : (ω * r / 2) ^ 2 - (ω - 1) < (1 - ω * r / 2) ^ 2 := by nlinarith
  have hs : Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1)) < 1 - ω * r / 2 := by
    rcases le_or_gt ((ω * r / 2) ^ 2 - (ω - 1)) 0 with hle | hgt
    · rw [Real.sqrt_eq_zero_of_nonpos hle]; linarith
    · calc Real.sqrt ((ω * r / 2) ^ 2 - (ω - 1)) < Real.sqrt ((1 - ω * r / 2) ^ 2) :=
            Real.sqrt_lt_sqrt hgt.le hdlt
        _ = 1 - ω * r / 2 := Real.sqrt_sq (by linarith)
  nlinarith [Real.sqrt_nonneg ((ω * r / 2) ^ 2 - (ω - 1))]

end Optimal

section Matrices

variable {A : Matrix n n ℂ} [Nonempty n]

omit [LinearOrder n] [Nonempty n] [DecidableEq n] in
/-- A spectral radius less than $1$ is finite, so its real value is less than $1$. -/
private theorem toReal_spectralRadius_lt_one {M : Matrix n n ℂ}
    (hlt : spectralRadius ℂ M < 1) : (spectralRadius ℂ M).toReal < 1 := by
  have hne : spectralRadius ℂ M ≠ ⊤ := (hlt.trans_le le_top).ne
  rw [← ENNReal.toReal_one, ENNReal.toReal_lt_toReal hne ENNReal.one_ne_top]
  exact hlt

/-- **The optimal relaxation parameter.** Let $A$ be a consistently ordered complex matrix of order
$n \ge 1$ with invertible diagonal, such that every eigenvalue of the Jacobi iteration matrix
$B$ is real and $\rho(B) < 1$. Then the parameter
$$\omega_{\mathrm{opt}} = \frac{2}{1 + \sqrt{1 - \rho(B)^2}}$$
minimizes the SOR spectral radius $\rho(G_\omega)$ over $0 < \omega < 2$. This is (4.47) of
[saad2003iterative] and Theorem 4.15 of [kress1998numerical].

The minimum value is $\omega_{\mathrm{opt}} - 1$
(`Matrix.IsConsistentlyOrdered.spectralRadius_sor_optimalRelaxation`), and SOR converges for
every $0 < \omega < 2$ (`Matrix.IsConsistentlyOrdered.spectralRadius_sor_lt_one`). The statement
is `IsMinOn` on the open interval $(0, 2)$ for the map $\omega \mapsto \rho(G_\omega)$ with real
$\omega$. -/
theorem IsConsistentlyOrdered.isMinOn_complexSpectralRadius_sor
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, μ.im = 0)
    (hlt : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1) :
    IsMinOn (fun ω : ℝ => spectralRadius ℂ (sorIterationMatrix A (ω : ℂ))) (Set.Ioo 0 2)
      (optimalRelaxation
        (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal) := by
  set r := (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hr1 : r < 1 := toReal_spectralRadius_lt_one hlt
  have hc1 := one_le_optimalRelaxation hr0 hr1
  rw [isMinOn_iff]
  intro ω hω
  rw [hA.spectralRadius_sor_eq h hreal (by linarith : (0:ℝ) < optimalRelaxation r),
    hA.spectralRadius_sor_eq h hreal hω.1]
  exact ENNReal.ofReal_le_ofReal (youngRadius_optimalRelaxation_le hr0 hr1 hω.1)

/-- Let $A$ be a consistently ordered complex matrix of order $n \ge 1$ with invertible diagonal,
such that every eigenvalue of the Jacobi iteration matrix $B$ is real and $\rho(B) < 1$. Then at
the optimal parameter the SOR spectral radius is $\rho(G_{\omega_{\mathrm{opt}}}) =
\omega_{\mathrm{opt}} - 1$. -/
theorem IsConsistentlyOrdered.spectralRadius_sor_optimalRelaxation
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, μ.im = 0)
    (hlt : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1) :
    spectralRadius ℂ (sorIterationMatrix A
        ((optimalRelaxation
          (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal : ℝ) : ℂ)) =
      ENNReal.ofReal (optimalRelaxation
        (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal - 1) := by
  set r := (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hr1 : r < 1 := toReal_spectralRadius_lt_one hlt
  have hc1 := one_le_optimalRelaxation hr0 hr1
  rw [hA.spectralRadius_sor_eq h hreal (by linarith : (0:ℝ) < optimalRelaxation r),
    youngRadius_optimalRelaxation hr0 hr1]

/-- Let $A$ be a consistently ordered complex matrix of order $n \ge 1$ with invertible diagonal,
such that every eigenvalue of the Jacobi iteration matrix $B$ is real and $\rho(B) < 1$. Then
$\rho(G_\omega) < 1$ for every $0 < \omega < 2$: SOR converges. -/
theorem IsConsistentlyOrdered.spectralRadius_sor_lt_one
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, μ.im = 0)
    (hlt : spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1) {ω : ℝ} (hω0 : 0 < ω)
    (hω2 : ω < 2) : spectralRadius ℂ (sorIterationMatrix A (ω : ℂ)) < 1 := by
  set r := (spectralRadius ℂ (jacobiSplitting A h).iterationOperator).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hr1 : r < 1 := toReal_spectralRadius_lt_one hlt
  rw [hA.spectralRadius_sor_eq h hreal hω0]
  calc ENNReal.ofReal (youngRadius ω r) < ENNReal.ofReal 1 :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (youngRadius_lt_one hr0 hr1 hω0 hω2)
    _ = 1 := ENNReal.ofReal_one

/-- **SOR convergence forces Jacobi convergence.** Let $A$ be a consistently ordered complex matrix
of order $n \ge 1$ with invertible diagonal, such that every eigenvalue of the Jacobi iteration
matrix $B$ is real, and let $0 < \omega < 2$. If $\rho(G_\omega) < 1$, then $\rho(B) < 1$. This
is the "only if" part of Property 4.4 of [quarteroni2000numerical], and Theorem 4.15 of
[kress1998numerical].

Kahan's condition excludes the other values of $\omega$. By Young's formula
`Matrix.IsConsistentlyOrdered.spectralRadius_sor_eq`, $\rho(G_\omega) = Y(\omega, \rho(B))$, and
`Matrix.one_le_youngRadius` makes this at least $1$ when $\rho(B) \ge 1$. With
`Matrix.IsConsistentlyOrdered.spectralRadius_sor_lt_one`, this gives the equivalence: for
$0 < \omega < 2$, SOR converges if and only if $\rho(B) < 1$. -/
theorem IsConsistentlyOrdered.spectralRadius_jacobi_lt_one_of_sor
    (hA : A.IsConsistentlyOrdered) (h : IsUnit (diagPart A))
    (hreal : ∀ μ ∈ spectrum ℂ (jacobiSplitting A h).iterationOperator, μ.im = 0) {ω : ℝ}
    (hω0 : 0 < ω) (hω2 : ω < 2) (hsor : spectralRadius ℂ (sorIterationMatrix A (ω : ℂ)) < 1) :
    spectralRadius ℂ (jacobiSplitting A h).iterationOperator < 1 := by
  rw [hA.spectralRadius_sor_eq h hreal hω0, ENNReal.ofReal_lt_one] at hsor
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨μ₀, -, hρ, -⟩ := exists_norm_eq_spectralRadius
    (jacobiSplitting A h).iterationOperator
    (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ _)
  rw [hρ, ENNReal.one_le_ofReal] at hcon
  rw [hρ, ENNReal.toReal_ofReal (norm_nonneg _)] at hsor
  exact absurd hsor (not_lt.2 (one_le_youngRadius hω0 hω2 hcon))

end Matrices

end Young

end Matrix
